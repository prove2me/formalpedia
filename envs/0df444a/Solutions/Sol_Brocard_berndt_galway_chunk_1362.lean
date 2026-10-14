-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1362
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:34:47.220225+00:00
-- url     : https://prove2.me/submissions/f7f49d1b-bf18-44ef-a1d6-da49db90f846

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 244784172 ≤ n < 244964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 244785422 1250 244784172 244784179
    0xc0a1b0f0e0c030c0c010c1701091104030215041d040b060d120f0908070306050405010e0c012003120406140106021b010311070c0e07112407031e1a 65
    0x141040031888840101c0d50007110801c4407941d0355907074107620126000d070301e070044015842c050001106170740007001c8a44081545251680903aaa0a008400c5e2003d204500341c8a04003400100014207000d203803108415485803e0508140d140c41d1000001c003540141003003003103911000c0c04240a11441c040d03402c400c0c00c2d100308802030311716210140442c1380d5120403000c1041d08010f40510034416404540680829816104026034900300000544800e5030252002e52030140761941000000400d940030801c10b03191100c00c501a0300140c40c3e00c02401140c071404d800100a10005500c015141da4403a502c10800000d02c0c030400e039981e07178034110140c0144e81594007030564400b140307006810f801001602440c0c040380030040011b00150b14041c0f41d0380245201e40e0b001e004038080740325691862040001d0f40e10703840e00351502e060150341c8070070402c01c50080d03400c12100b80700c0154240315426030019440c2000b25220300c400307000450180380c1108903000c036039844503552400c01144c0e50910740b0f0301e4202d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 244786672 1250 244785422 244785449
    0xb190f03060303050414030a080406020f0105090f071203090b2a120318070e0405011416080a020a02030c1c0f050906040b0c0a05031215101d0102030c0a1b 68
    0x60358040e00c01d00c91801800001b004290f020708a5680c10400001ca490340040c16940310f55a0f410007a5035a10305401c0307080b103542440c1c000341c15964001454034112000c40001c003811480c0019003010412400b40c1a030410039020000700b1907008840040008004543ea42c03ca0b2421040003101d22409030710007006c580c0c020110030010b1084050175680c1100051008111011810030254030b0030749140c3c04582e03040703501c50030481840360643c001d0141c1d5459420075031b040e65032141041c064140c4040c00c0004a10650081804d000095001d0021902140120792501c01c6030000d072481e1055065045901c0040401c000d500d1980c48a09a00702c22050708002d07007480041c030005400c6024034010fa01444030040345000035020b041240020085d00300302901c0c2d0b0340c1c0c0100c40d85840c1000840d800030b100c4805450320295401c00340b01c4158522240c0d550755040d0102201070903032a0000f0010300d81188014000c81240180c184a400841803185956807400125407100c1c04c50146264403208892564 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 244787922 1250 244786672 244786679
    0x20105060d0321050f100611030f0703031404050d11190803100b04230d0206070209040222200703091208040905040302031b010501080c190b190f0306 66
    0x14049444201039140c103100c4000c3c409815802c580c06154001d40110034204424070205402d501c2c036050084902d031866010703260f02d0380800d0702c0360120407c8003401e41e8401c22041c43c80c054550090320342140b06e4034002c103115070048100814808240c1e0f0645583d0040b201503400c054101c90312014210b020703805810560b43c8040c8194000003405809441828000002100c1c0e450f40340c030890180034036440e60f58489458443d050390650744800941c1d007070100788014482524058600c100802c0e4014007103440c0880550074422407040c054012030304090001c0c0241042000102c071500400145207000803211502e0500446c0e090100c0d50342d40721000c0800c5404046035010300c160b410350300c45281d014803214845c40d00b000280b05d507505c01120946004144170030194040000c10145104240200e20ba00020325440e01300c45003841401ca503540103040904141c1080011000000e2864100c008003d41e1040c100700702e54006030690840b078901152600c089a0000c00d00070315402203182c104011400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 244789172 1250 244787922 244787929
    0x1221060f120c080a050d0323011202040b03010c0c17040b040b0f0d0603060b0306061e011d0d030c050d0c0c0603050603010b0a0f18020906040303260403020a030f02010506 75
    0x840d01a01e5101c40380e4001c14801d221a62844000a100303040444c1c00502ca00d04040352070708001b10742c0c0c000003410084088054804071020a641e40c03003c0304410016483d21140001c3c030410041c00b260010303107803179510160755028131a02489403200d0321141c18242e001d14108801c4524046940d14299090005008006011007501c096414401c1c42d5a0b035107144002c40400d50165070104d507003090512402104000c0341c3e8110b88018103060302101d005440d010200702250001c00003030385a003114060807150661003064562100c80e05504400a03c114040110761841c01e000d9050700070426103540a0f0070014200000c50155446207401036604c2003a40d190454810300c2c0c841d040030191180f000c500d06580a5014002c8003e0003800864120b51301ca8048100d513989209000005014140c52041c48405008854110340000d0060f0b140c2030555800f6034070164281c0303182c102001a1040d14011241c100380c0c031401640242c0041080e1649480d008004203400d1000008590410741804469207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 244790422 1250 244789172 244789199
    0x103080c01111e03100f151403060f1306091d070e070203070f1401091b05061206190b0409020c1014150402131403010b0f010504170a122106 62
    0x6403d03c201c030b0f82d2034480017180c0a1003456074106034044940c80354000740c010082c2e106800320100360389507400090001010a80c06000440d070603508100c281e521011149021140100c2c09582d1650000b443c9032500d58038011514940d0124640c071181d107420b840c00020420482e40284100c003088141e52912880081d164042c1010003003207070b01e44800c008100310000101a4003802d108000304050003075418039400c072000030400385c03e4240c6102c00110715814400d048458144144110540039150181808119408901005500c00c0010300200380c050201d00100f00821404002584a28030072240f9802d10409498a090192a180c807001d29420100302582c0c2c007401001941010f00841c0010801074455a001035050b004a0f2001150006030035a940c03044507010340c02000091011401e0102d503225951030384d400710f2018042041702130405101c610715038000c1020b452926040c0e031f55800d80c24002034000320200c0d0461880d41003810071071800c8100102e840c8002c0c880b1520380b5201c0302c0d6a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 244791672 1250 244790422 244790467
    0x50105060a170901091415010509010f0e100803130e07081306021e040801140f010602030313060f062607060509040b040e06131202030f04060c0f05060103080c0111 72
    0x202c070000000b400070300700f0352214140c15000340390200c4d007070600e10740d4985400e40408080c0d40811040300100701414800d92071816901400d921445080c10402010743c901c00040c40c10301440c150500110744000240098540c2603c06c0c0010211107083c026205290107005180c042001564020405220348500700070074807a03000b040069590000188883c1da11041400c2d01d14041000980080e0070780c01540800192642407500562544070361142611240085c4141801a8002d001188448105101d0b5004543c4034040002c0c2408850f04040280d41c902d900484d90030300e03d48400849a070540240c14a810a21405484150b0a202024106000b55a4050b000d83d54454454240f5100c5070701c03002d50384019004036141703803034003000081c880c4010660490b00c1c840d103024052406030001013559a450030f41808039081504208003216032030001001501e06502c0d425810340031410600849000c1c5020b040d00640d900f040031901801e540c0046d000c0441c0420030014030345011102c1c0000ca00740c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 244792922 1250 244791672 244791707
    0x10090504110d0b0a0e0f070501030b010203220504180507090b062b0b091311040906020a0305041101020a0512220b0a0e04090b0406090615090f050105060a 68
    0x85459a080200e07108801a8150b90032404145202c8180125201260320919580f0741c10f0018009040e6650780340c100342c020100155201000030302031980641c100641c0c4d00010b10403203040a0314404d03050b0551240b481e005003e021586020b0046007040e0080850054264440b503104110517629640d8039070052185044055441031151801e90340c00c0d04a0300e92060010302c0fa40c803400c03001024849600300d000d02a1419260580d10099414402903c40c891910145654440203807a111005442c0450041d02d52251342c0740d1800300001e2103031014202d5510320b560005003501d024900125124180106c090540d44100c102c40000f881c005401c0c81402001c04841c0e4031006817071000da00c140c4000c44d544a01d805943c40100700c461740b440141c4501602503031a80180c0a103203041c401154140040641075180705c800003801305845412040c00f240c424440000e80003409030340f20104980d590420602c46444031070030301da01d840c01d0180c80d0250104403016881c000c00d16101a040e0145908640f00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 244794172 1250 244792922 244792931
    0xa060504170f1902010b040908030a0b090615070303091a070f0203250203010e0f030d0b0a060c021c02090c041a0f1b16090902030f01050613090215070308041a1009 72
    0x40e07034070030340001001b950058010b00400e01e643c0362501d00c1da0001c55103034003894a0004045038510f4043c048a0007150007400115220280036a0756201e0f60020303500f6020b1507150003001000074484c0c8100b002c089130f4900740603644c0c00c1040008001c2c020b143c00c10b41c01c65005105c0441030403040c1000442a6001d0300700c00c0000041840802c0c054481d640368018940907840b4415285a0080001c01a08108032410050b01241e50208600119a8010480001ca125074048014240050580e5616003140083d10780c00701c09600045940400f150406c1c1100750205003000040301c4080d8003019001c00c0c0d1040c1e806c050000300c0c442160f00070404107991036454140d404010300070a000d4011484e00c08855008043c0c0c80301d100b003010b4030070380b502240a442152000c41c0303922818410382e4001c090041c44150402141c0d03103107030003510308641c06a81c01004000351a05802000c0000c10081d4440d48a444603403615007401044041c0302603070703280c17031030700c030f001040f050701c908048004c150fa021500016 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 244795422 1250 244794172 244794217
    0x2006031812030903090306010f06080726010f15020a0f0201081e0705090a05220b060c0f06090d08040809060703140c0109060c0207030809060d09050a060504170f 71
    0x10318008200d401e0061005001040c004000d401200505050000754101c4807140d907924200030140069104850002e40c018003c10728a920031481c0e1007160200000072030001c034102c1007190003030901782d00000301140c58101c104000c00100840c290101c0d0341e800500a01001078603460502003034501c0c000e040100110010388885003100c200a10b0555074a00002c0c10301e0440e1020300154440c200d10361188924a60001d030b64641381c076070020313804440c0398107516a80c8090381881c090b1100d006e043d60302440c00d110005407101c081064188040c01d41d401880b0700d04008110030304194080c0c1c400010030018100b0800443c0e001c00803241e008005681c0e1541d2142ca500f821628001c206018480500000400c440f90080541000e9100c0307014a02c10011001011401e9a40d21424800103104140074000c111541c58208080c014040940ea80810311000a9403041d05003040c0c400122229031741c3d4010f10086c4503e200c2da0308040c070b21085030140362010244401c3d2850103211110380e003001040e6000c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 244796672 1250 244795422 244795471
    0x106140412061508060403120c0e0103090c080d0314090703030504150306090903020c03060f0108070302061c0203010f08010506090f0414121c05060a0b0a0c0302150a09200603 77
    0xf540d8000c01040c8011038203803240303003442d00c4400030b40d001d45c0011340300c00d00808070074428070546c3c20046c030a0300c030007903109c28583c0154061b0402d48429282c0c0c4040903000240765809004000d81c11150b95030015005200f8103000811181c00352841c1e0003940600c00a000083d0031000f141c0a40350041c416000c11100060300710094041500082085410712160008240e000211908448030480503101d1982e10903100108100e42407090581c554403440d0700700007504046005001c141d040040b548281c0001040c401c041e0fa00aa00c02d040410b0040b004000d140d4003841103a03041003040311000c80300e00b03100e490300705d01c0d00d00074101800480c000000c011150b40208807445400450068254481036003010380c4045000d48040074803041c0c20040010010320f03191200205464602416505101c84064103d41c4103400c0c5008400b0b5200d480c80805510100000f050712030f6194a03c00300340405c40389005030030041406a5151340c2a0003280186507039a908050340d91220301c250450000d0540500c81 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 244797922 1250 244796672 244796681
    0x150c0f0c0f0b0702040b0103090201080121060c02070f060905030606040b04090525080f03030c0a090b03090307150203061e060904020c010f050606030c03011404060306020a02070e010614041206 85
    0x3070404000d00c104000380319000500502480c2d40201c504003c0e80f13403184d006401b0f5401c1c4601c000e0000318684014426840c2090382c0503040d1201031b05036074040c80c895568604507030020300040051303440000c0400940400e180810050b04103031802c441150700c8d1401180d0703034400182501c0d2041e9181c0c41413190036100e6521000b541e40d0042c0450700e5040d074540054140d2402d603006800d103504000c130b02048050f4009400c0900c000c0e02c400451943c1d0b5808074a1080390081c004003010859000380001c0c0061494003d9401100d818000d166078840d0303444d001c1c41440c03100c0346006206005004000095032101c0c40202c180000715003d0045034070b942e0000c5c03c82d205516065902038408202d41641d80c605500c44a98800c00c20780c10801521142c003004100c1c04110380415103d03078100b0050000c2c524400038280343d00f10150011402545965615059803c014840c0d40181c0c0301200810510580030403160041a05080c9440303401d00300720104410b0310850054003205410340b59031f80300300b20f5a031380b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 244799172 1250 244797922 244797929
    0x10807030b1308070f1a06040c050906030604090f03050c01290118090903090305060601080c0d090219030303141b04030215130b1902010c0504060c03020f06091501150c0f0c 76
    0x148801140c40a14052240700c5a01ba81054100d41502c0007540c142024031500c40c007411103850b1141080001020000c1c1e03a84020a101d40080d280ca60360000142e0030501000a944651102600c82003072039401ca00b16035680a20300c1880141d81794110000c12840440400d4800a07e0001002c1d28034041000400d90310ba403043e101c4600d44036480050543c448181020342c0d21400070354907103450303d000443d04080b00781c81611040b1410440c907071440301140d00205005101903c0414040006605112110910381c000e4010a480301107030000b40c1442041e2542c00941308508008102030031192441c0303400340b400028042c9100c10200070880c0f4803441600c05856080c2c1c240d02140341c4800c00200700e070b00504404000881c04050314040f550040c0a044018003507a5580ea0605246c101c049901d914001010f4055000d0340f03640e03103507448003030140a108800440003003034062156150b100c26540164080356013101c0030210703011081d074001111071541d5005290680c0302c1045003071103040c00b1001e0f0f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 244800422 1250 244799172 244799183
    0x1209050d0c050106091b18031a070e0405100603020c010b130b100e0105071212110a0f0203090a03170c1609051e01170f010f0b0306010807030b130807 66
    0x54030040c0032035208002085140c0b01d40002e111495940745620140c811988003090160a070280f10300f0a140b1450182c08010480340811081c02d030782c1d8036000425184510030413607442c1e0640400001a4220080c5c041d42841900e0407c11480c241c3d4144001c03042501500c2c041540004595441e60b609400c805a201d1300200740e207940410400c60382e801031503d0244140909075800801c140d49009181200c5440350607101d840c40c04410341d981e0a03488101030783c01da0070320800480240d107001d00e5102d221039000002c04250790f03d00c1e01420146c060b2110408010866104106e1a88252958501001105da10016110b00d034400e224070031b01280200040c4035850300c107000054031500b404031610011901c580d8410002c45d03c84089800d44c00407108102046400300d0801001059030a000c40b006c909940c1082d1408201d0b000011406c1d0303140c4080c03005807640c4800290601380380501100d801044900024250b1900e1581c641c040e038000103040c0442440fa440824040c890070404403458654042d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 244801672 1250 244800422 244800433
    0x20f0d061406100503010f0323010504030c06060510120509071a032208090d0204020f0715060b090a140f0604150210020906070b04020607050604050714011707120905 73
    0x5404100310072040314520f01c07551451401119840c0140f0403203040e0b41481030010081c90550f200c08021004401c4030b822900e0f904500d00418210a105c0d40b80554400c1d0389000d1500d00d9401c00100707440b0386400180c440d49000000c400015084042e0b0f4000000003070002c00c1d5555454085030414005602900b40f200c59814000981d4030408000e51250240040201d540f40c041b07801200402c1c0c0c140c400406061080010101920340758030381e0069148020800362a062204800d440903420000d400c49070078025200752140b4030a140030f000081e2200c0c104490401c4030050000b0034122440c414151511810421380940352545050768841200151000f81d80750350f68042000140000c1c02581c2c01800f44501143c2c6800c040d000325051404010a860300340000394590036016000a00100ea018000f0440e5400003102400b54038440c0b401140600202840c01da464100c48071030000b05c40c10820301da40c00c00c6c0704130741d0507943c1c40d045001858002c0e0308540c844501c20080c8100038010300140302d02c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 244802922 1250 244801672 244801691
    0x9050319020d05070801021216020703110105180a091e0908040b0708040b1b0c01090503070b09010203040906030302010516090e0a0207030309062906180907020a0c03050c040608030307020a020f0d06 87
    0x407423613030160303895000c46100022441401c90700c5084a000c010441d40050241c41d099601c244040c1c03d03246a21a4000c11905900000071a04031866011010041c0c90b4212500010b17682d505041d00030301c04072420311480b0a41e03a2540710500c140d00940d854180d0215440b0148040001650003515040184c1990341c0524600700c5642020b0003402d008c03921407203844414035445060040202d40001d0003c00017103040540098507078200400540c114481032100207030880003401814001e501a800014070350500803036100344400b0002b6600140f041c40c0d482045071b0031011400d542c3c005940d0100580b650b0380d501e4118007800c40300101821140c109204209210020859000440d0824810143c080d0750388091101d1746c06043c4850030601a040e00104480c141601c030241c0c40031284c170603030f02d080c04584c0d900384080030603810640303a070341c060007505001d803d0920a14006c0c00c0c498000314110301e0a680000d6450410072002401400c420000b20480d80f1900b0b05a543d140e40004140514002c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 244804172 1250 244802922 244802947
    0x907080c10110f0109060212180a061a0d150606090810050601052205090a0b030709090507080706210207081801140a03021801170c09010c06050c0304020109050319020d0507080102 79
    0x8070780d6841c2080e800102c0401c140d1080c8851160700003240c5806042c46801c03607100c10700181501d50500c084607551501008070783c1c0d1165410b237840351041404041041300105a1400c42d00260001814448a040140070303058000800258031800c4d207001040d139a8a07100100c1c0d2500031340e0704015680c411a0107203070040310359207031000c146c03030043e581c4d80400c0c2d9507010b950044d12190b401440e099007107400c0034005014030390401c0c10744030b004400321811f465a9040341850b04c082079010f0000500842000c207030b440d00009002d9440f1042e200190704140350741c1c6900002c4d01c83c3c5041c42c040e019445581540503405020500b06c583d07070240072980c480ca0b244a001d4083e502034142e00d0f40481d16030100080c03541c041d1101d25520007003420381c00c2d60360341c0384403601c5103a503c0501c2c2c0b0b034140091816100001001030003500e00c99081d9104550702ca0030140b00144c03140c400d0350841403081d041941e1140100b41d40544c034515403501110700c880740620604041e030512501f50070904095000054180b400761 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 244805422 1250 244804172 244804177
    0x3020c0a090c02331b070305070c05030303010e0a020a11010c020706030f0225030e0402040312080a050417130302060c01140109020c060705070203100507080907080c10110f01090602 80
    0x10300d15002d8581400303840303091a144445007050b403030840018141d00e5654444c00c8110a60042c80841030440070b042d907804400741340c0c001c44003c80004a00203160010081094004001000103400950441d410011030003020700c0001c0c0108a2140c4c0414000d05a502c580840c2c00a80f0359040200000042c50a00075140c444074002c84001c00d082440d05104203039580708a030405000d525005446003006444414102102042a802c00c441001d0401031fa5990b44014801540b10300820804c1c46800074028151501c02046001010b24003000c010208140c2e1004091301c0c41c8091059689055000618550a40b1501301079027044001c0707022245240154884421040c3c1840554010b0fa80c0d0140079051380701d00c1071000300c190011720210307052500440191141a00c01001d4605c0c1c1c0080c00300b000304039101122100c0c00a40070409002d5440f5041c802800505500c0c0090088001444080f4256142c08c030300000410000c00d44400c00b07501c041c410500000c0c070640090080080c00c0c14420083e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 244806672 1250 244805422 244805441
    0x40b0d020d150b06130303050a051b150702030c070509100f0e07020f0f0a0303230f04030807110703021c12020604050706090501120509100204170d0f12020703020c0a09 74
    0x580c41c1044014161601100780e500c10517081c0d151030940c0381507540440d0250411182e0006122003440120271894001000c540d00d14a40d0000380081c99600e40c0e5842c0d250000b80ca503c0c00d43d041040f52032150321000c00c401c010740f04252007989668599800b1b000308100e8961200380507030258403001c070302c440511401c140203003075582c202e540090300030406549407201d03d4100e00d03040d40150b80c8403000078000e400010350140e00024010030b11150884800c2072402c2102d84a51050728a01040101a0407140554010843e03241c02d2a059201d43c0b04a0b9940110740800b83c42100018000301320814440b00b03180c03460b503100c02d503912242011031001e951380b98181c0701250603000c0c50780085030765032003400c0103000c862050b035031700c211a0a0840c071400200400340c92006540952040141e0390a043d00041c0014120070811140365440030001904002c3c05010100c104242d01242c001069032280520b8140000b40c08016905e812030b00e410b91401c00c100d072115130846101400014104d01507407000080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 244807922 1250 244806672 244806713
    0x3010c02030403290103030807020a02060a26060f09090f0a05070602070501021507051308160603050f06031f0906051512060c19050c1501051207030201020c040b0d020d 74
    0x70300410f10701594105100c4c031120700030f0101c08001040400e01c2051000d802810038015030350b4001241e0040b85031030740208003c4020550101c0c0d00c11003030032980784071303c21642404411082420944000fa20780301c0d05540c0c1e40e108100a10208044402c2444808a003504032001c40b14005040d182c101d03100c00d500d01c51b03100540100c07440001c45500115140f05620100d180510040c0d4400c4820782c1c1980008209a28401541c3c0f0003240c0c1c003500300050940030508021800340c02d840c02d040181680c0b00200488140904141406000d44001130001200348106400489003c10903c0080003040d0020303001c1d00042c140414803148442c1003940038006042032300d09021b0700d1009140103549010035500740c2440c0b14100085000303230b400a01ca0070f07154880b902e409490441004184c074505002c15201301c03c44e160b02c0c00104040e25040107500455404500500500344ca1900042d440366400005c80d0b00807915440d609219555005d00315910a6004010240c10901802c2214024555860140e032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 244809172 1250 244807922 244807943
    0x50306010b07080301050d1a010303030b0a06140702061b07090507110a0308041712010b04170a0308130804080a110406080a020d02040f1404081e070305070f1103010c02030403 77
    0x54050350744046407022500b01880c2ca20356480d10050100c00500102c0c03d880410142c0388041c491340408911600850080c1d4000c15045821410401101d201d41d000a040c020710000100c1c0443d40303181507840140c3c04603401c64480c9100700180b49110b2211010062074010a0b001040f10750380740d408580941020380c0c40c4400900c1c040042955030780d010030050f0104040341d0004000855101002c81403800c03004095091150001d50208000c1d02a040b40800740b1000c20280117004440810303042003000380300181181c42880e20050140c40c0044d2076080308071003689034403041c02900d5003124000d04d0707034408640081800b801c10f074420540e141d0b060303441a405d002000400c0e81000810400e0141c00038010158641c41d60b08200c01004406202c404294030f6084500021000e25160341c0b0480c007948960b82d0f105c555034254011081c007564888061201807281e080860b81c03003030075121400d90004400c2c46070740090410035a201054140d1070350641c00c2c56802410564084090300460344540300c81ca0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 244810422 1250 244809172 244809179
    0x120d171f0609060207141305190c2001020a08071b080c01090201030b100e010302070510060b030403021005070507060207020d061d0c04020403120f090b070303061404050c0a03020913050103060605030601 89
    0x10781540186c001e00e9845410342240180580040c3d206a41021204911486403041c2d0302410b01903403550101500400c0650100d0030b680c18154a04d41409184040214540203070000301424111001e044082006414508094250308103000800c5c516008501c0c0c0340c075000c1c00c941d01806445030880072030003e8103100405401e41040e424440a4241d192101c45040c001840110001e42100c04c0996013480345401012070b2030a0f44c0f240402500d43c1c06001342eaa4502824081d01e0300041000041030580b610080007031140e0b210094550843d807005005d070b940d8170140002880d070420228003509462900d04000400b503259400c132440303407109109644100040f0750800c0101c0c06544405040030400d01c4800660390b2146040fa05400340030304045040d20384070001c440040d0440203045010956440b07051000140b03081030455426000c40341072016103804c50310440b482c000d0900c1001859004035044016a803100c80d140d0070183e240c1d00c204110340e13503820414058104d600c10540280503000010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 244811672 1250 244810422 244810439
    0x6051009030302060601050a05091003050702120408061302030109140610081203060402090a09020f0a0806040c1413050d0c09050105100c021e130b120d171f0609060207 74
    0x400c116609600500780340d0b036503040150b540c1e501020512040243c10000c11003070790307942400d114004030360b60b500160624040c840a46441208030401058502c00c0c0800c000391403000442691019000d032030101880e007a0b00c046405086000001445c030700c05140704a81c1641c0002e60103200c0c00707101e42200003084d50784c4102510b481e401d14451003201400c0000070031504040c2c008141a207009030074400015554014102242c2003149540d5000c4000140e600c030b15940036010030741005048401304000340c0420b901a00e01c054496051075041d401040340007508403c80c58120003051301501c44002e520a91030b143c580c14480e402006c0d42030786880c0000c940c6092420990323041210a0312051181700454003008012981601036070b41d20400c030300d008d00300394591512081c110313440242d001c85ca100b1513400300441035620f00310540b4540c0c040c82114101e0b9034403d040540603940703403000300e035140c03240d0340200b2403250201c402c0402140050380001d4034681c44a400c1c01200d109900380c401e425241c01c0007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 244812922 1250 244811672 244811687
    0xa140705010c0e2e050403050f03130905060603070f09050d140d02010606091701060312051305060f090d11030304060f11010b01090e1f0b07030206010b07050a03080702150109060510 80
    0x444526060441c070004041d070100a08010700c0d45030800c2c13406c2581d00e03076680c0d181a50454030000d09401c081100c049200d4850350394000f420070072005211525264020845501000740841c040062007100a05624000c001d48000f8140140020030720080f46d081502c0b074640c3c010800c100c10303c191003c4000080c4184a9041620240d980341d5130020728004104003031100f100d508075800c4d50b13250b1002000500e468841b1444c0340c0c081c0c42c0c080e11125807540c0300c140801568050350040b030003000503000204c0c001044481c40380c8111a1b80c3c01840060070884407041c8421040d03505884000f074081010381c2c105090f4055840701d59203d80c900c2600407c054203803104a0b080c070b804180200c03000e01810340074107030307850307100e0075244809200c510450202001052268403003043c80c2c030002010310925505110041c0505400d400f8a89400c00650761155146034040015003041070103004100300a100b8088116102100000110a940c4881c6d10f43e0047c00680305051040d0310300d91049030028040c140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 244814172 1250 244812922 244812949
    0x70507051501081e10050a090614040c0513020d06080a021309031e03020d0f021806030f040807080c0607030605040b030606090a02130302120c0910030f080a140705010c0e 75
    0x3078440b00c0d04240c0404c5001411200c5407519001d05040000000d14901c80c0c144282d00512012841c0300c072a0070b1000840d1300e800042201c0401c0c840030040400d00b20050901229019222243c0012182d1600340c02401071400d40248103040c0200000c0c6500001280b4048034001ca800e584103204401400c2d04803501d5403030083c04200c02801c0540c0306c1c0401100700004480900b000351810680402680c11286840040040a6400305588c0e4808000f2591410b40ba041665198518204440d0382041100000d100421030b500004025040205103010388902000180c22034826050402d00600513220500501d4011450043e1000722840c0010f80c0601420010b0480301283e11081c0c10b0502944c441c1b0660201c415030344000200507202c0112100000d50814013a0040741540c4041100d003401c0942516088400c0d40c41c240b010138469059010040d510600503540d0b456064002e8a541000074509510f08802040c90320600c041900041c6c01c46602c1e0341c1d0620b458609804019841e5078042c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 244815422 1250 244814172 244814189
    0x108010b031302011b05160f0f052107050603070302040806060103180b0a0b1207030501060603051e070201060b030118050a0507020a06180206071a01050f09040b15040203070507051501 81
    0x1034648002d5401188400b400541400c040780b002c002d951225850850007d503901e200c01030203101000141c94903640319001c2d20351903e0fa00002840d05000900c0146c40441e000a0550309120341000c601081203480c004000241903a0344030300e00214094002e400601c9644c074079028060000380365611034400c007a0526403910816503240000c1d112140406402011811041e5851400d1032440e51240c0700c6100b9070303500c2c01c010b1207000c0c11440c210742514503540c0321100f030504200622510340e10714142d101091003001c804140301e07540c0032422805414541d02440351210004000708031554a150032003404010000144082d0704d590010004440c022102040143c0028400e14005a4207030002d9142028160603103659401540010b40c850780003407070450300030114040855144101c400d2050044c8022a400343c2c0380c0e403400010074050703140140002c00da9140ca00c00162030000c5268011608400940215100e14051101030802da00c4082c054a03144554160080e1806d65218424165002403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 244816672 1250 244815422 244815451
    0x200304260307050c0f030408010213050406031a0709050a171507050301150201061a030f01060c03080117010f0c02032212020f15031f0605031005120c09090a020108010b03 75
    0xc42c040721181c100074080081340c01007030365944541404001903c0900600400144e039000d10b21025005014035900c1313140070b18140b00041001c212900062020144504c4010441d9601c02c40d0031a1120a00d41000c1d6101103461808a11040b40440c0e03620003401e12011101e6020f08003010f000742c43d400300c1d201000208104014002600c3c04074403c048170f502c600021500a0b22000180021000b4110345111103002108200e0301e611100e506900406403410144040491620003d100c82014040c10590034215500014880e500758819041030400480c20410402d40d6070000392203a000005850490100c18643d140840e0b4040400c01101d007144919004112203509100c01600d0340b88031994044018040030ba802135000c4029441440d02e001511000046140004400b010790340100e010041c0500c10020031208441c107004c01e036441125041452400ca520592600404d00310140d00418100107018000500084401055100342c0300d80000d80e03220102407142780811138075030b034402141 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 244817922 1250 244816672 244816681
    0x30e07090b030102070803010e06030c0d03020a0209101d0a050c04120f03030207150b031002090108040303110405040e010b03010e0f0a0303020703200615030606010e010e042003042603 81
    0x640e444400050710140c000350030601d2580f651805a0000d81c4425020600c0104004d4585018080500060012604a014501180c600940d0faa10030f2038001d0140058601003110310b241120308000502c520701c4500070414000d030244882c01400ea4040181e00d0415010031812a80f2005440550381d01c6802d10f03041889070b0b1501c044400408034182d0034540d00304040c40202c1c00c01c0501d0400a04001c0c00883d1124041e4181840c0c02600078008240c28170610100000c0d0303900003107464101e5018600454501c80754619060184140c1d4401a4070600d841c1d28400d14a00c1900721010780b030f104030000c0000d03065510303500d500c0301982c0b03510401e160004048800003900a03405020740f40e00038a000e40011785140071507900030040c1d085405d10740d80704404000001e580e03070b1121011906c003a000b408142c204600041d00800101d03298506000c2170701c0341d60708591030b81d5205940c0710002da03659030400300792503014096580c0300303031403d48041d0030340040d100c103034006e40703010013101001c0082951a5984 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 244819172 1250 244817922 244817939
    0x2a1418071b1106030907080c091b07030201062d050f030703080c010608070e01090c0315060c0303020906121806010b0301090e250617060d060902030a050604030c0c06030e07 76
    0x725003a045510300507481004009490318800385210310f003039000409a0500304881d082c904506041c05600c6004204204900c0c5001440040007001103103140c140c99160351b190580c0980900d4100d52001c000c09500d8481c0201c000f90802c01039035000d40070340141d0341c40340f00740300710070030301c03501c401d4040d03001560401c00605600000e152000e06003000282c01c981751a44581011001d0f03100d03e0101789103c2c01407102034441e1081d040d4030203039030030100120100c481e1400b2035584584504818441c8205410042c58080c1d01100c09504004221694945507410700380503000041e00e070f01c0103030003101074161a82240000c0c910b044c0c46610baa9581503030b191080c110b0140c024100d9560007030141010081ca28a550080c040b40d20170310142e8042d81ca0b0030003000070003050310b01040fa50013840c0300042c06803940b507a01c480d0484a0f00b251011030710002a0010030b1070640b60b1000140b007031268000300000c0c0b5501501c1d0908040c4101703400c040d01d07682e07800103c080c0c0300c425800803240c2e00402410001c1c4075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 244820422 1250 244819172 244819217
    0x1406120a080306060c19030c0b010834030f08070b01050d0f0204051b0c010b1005090607020d0f020310020919083f0310080303040507032a141807 64
    0x141c80000f261100c1b032022075801101d548481c8100c1c007290848030311100b08042500c40c5800350040b4402005000101001d040c4029440a070400c0d0b460140034420020380c54584a40d03000d15000980741c401550185048059035018070005e403002041200040b46510301818030480e03ca8003c100740304540c0c0c040e003c12000f0b140180c8016444102c1c1400c2240c1004090302400061007803000010303000320b1841c18014039009160740001001000c1096007040d685a10582d00b0680c0c040d03031024802d00d41850203201840340e941c80607606200318141007100d8025600105a59041954040319244000130304900c0c1c0b0205000c2d0b010b0b41d41103d1210405e25407507050101c0864001c00a0144207420703486141444040035460320384d80d40300003081202c196400d4694100400309040110303d585043d8807041e8640415000081c04c06141d084201540e074011409400926841e640a0036040e5075030000348450006200600c0c000ca020300c8400980030b1341c00041d1841400d09403070304002c01174060a03811400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 244821672 1250 244820422 244820437
    0x10507020d09030b060607020d05010b01030501051f120b0409080304060605011e080603120a030e1c0f14120c0a031a130903091e0e090102040609061409041406120a08030606 76
    0x18814031441f400b60f07450b8520042402e003d480002074404e03a420004060780c905030490380c091a00440c4541400440070440481e10031180b50245210602c45d40850207001c1c1e0364802640182403032520f00520003084002d5000354414541000340c5660b5000640310000139a403000301480c0030b0711882015074000e002c001d50289000302510301c41c801c0c01c850021503400032401040001d07034500700781600c940e0421240e1420076a01e014034540740d0b0b420030300070303c80100071103a04204406408070b24000c0e80b800040e5074007907810139894140c0d4a40700c0200314003500400c51207030002e8100728240300e90f07800241b0140381c80701000e0300e40102e210000070044098000c503a021410000407202c0000c20240305000194100c07692803802107901d20706591142c02c1c0f0b10141940c21140d204202c20040940c02c440d0b000100d50842c2815100b0030080e0b103a8400a0192280054210342004c804411016198560300e2040d0412260003000d60300303140c0c40c155100507403000100316203030400c0852810701e000d101900d01c1d0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 244822922 1250 244821672 244821679
    0x2030414010c020d2003010b03030417070306061512020702090a1503081204061103071d0103060803030906100801150306090f0203030a0e03070509060303033405040305010507020d09030b06 83
    0x140c0160f80c00300302080c44400c0c040c1d80c0d48080085012800c0c904c01007501c02900110000d00078042908006a224800d9100380d0140403100d00072612842d1050003410b0066070011001c0165655400b042d01901004162000000701c1039005001907401620941d820140c01401c1c002c0542e545110741342c020030001160b80114020b140c4c001000409000060940c0c0c83c4420b42e003161410f203868518240c4d80c0d2502c07200c610350340500820071807a034002c003040d02c24001201907030f032580c01c40d400683c0105140d8010b24243d01001003044540f100c0080d1442c060300d421a01d180944c2c3d60b800048e401c882070800f43c84111381080030f040003c234066070400c2c4000e40c01036602440101080d0f00180c61741c0d0207111011b01160300f0908000300c40c50140000d900500c070a80d4075400b2407030038000080d101c1c40010814245000c40e50b14110340b0a8220b640d02e0280f103402e0102e041c16a42c900c00c0030301140c006200403202903080c80f002074401d900c0030417a070240080a444100c0714030304580c0c030039807040001440e640d003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 244824172 1250 244822922 244822937
    0x807060e0c12010209031204030803070302070813121523180a031d0f06120403020a05070b04050411090f0d0503070b010b1207030c02030f071a0a02030f0906070203041401 75
    0x1e403540c81909148442e5290000160340b1013000c41490709001414048090245c028481000880c100f041265130100300313071030010303910000c61130b00503403500402842042c21104250f01054061070046050340c218014282d00350320034002c1d5a00350075144100d0442405a086100707007540c0c03151850045030040c01e11050072044400d040d00940c58040b22040c2900020440c0c8008480b02001c140f42d0140341100b580c29006020b043d0020440074800d100706c1c40081d110b140b0016061510030320981011586c07140a5500080d40c1e03611811003508070b8000c0d10b10551902c004400031200140840d0b1a5410103083c080021080b45c00b04050010035580540b4140410030000c0005a00c04080368040e10140c0c04030313a140c000791300174500d4180004054205151a110b00042d4290700041594192050381020aa55080c00e18103800035580c0780c0d4401c111140040c00784980d40c0388075000341d40f203041d09006c2003c040d41c4284547c2d940701002e036021170140e00100401c0c401040004222001c410040c1050103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 244825422 1250 244824172 244824193
    0x31f1e15051f05030106140702030a0b0603010f020c060705090307081005010303030e19080d0e0a060504031106040b1306180c0504060f050f0909070302100c02030c0108040807060e 79
    0x4080c0e90368031160140c004603003030091250340b50290400c00c0340d568142a00c5581025000b000c0c01610060144000b1f0140c8150b1032010314840070110750344d199001e02a1355105015244c000b40020013590392612a50804011440b080c1052003503851004c41e213002004c80391035500d0250ac10303a10407440c041c1c040c0107003130003c00c003c0010080e06034540c04544001991390700d5820020100c9071010240c56044d0818040f0048101c10055408210780d0005805c5544141003100301c0e006000d243c58195090090a15500070b00803a940400d110f01e020b0780390708440019514541c0d03102c8204035001404070342c114001c1b4025083d9406481d6000d84551000205160b100c244280411a0201c00700c0d0009000300d0280182d00300783c001d0400030001c0405081c500d41c00c1c9000141c2501a21502c00e00a1750828001000c001040005200841c2c020300025504c2c40c0402c401001106e900b8010790203403007011280300c055440b403c6201d100760380003180700782489602e030740c0d04001d0081c107050346d6010310507060b200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 244826672 1250 244825422 244825481
    0x510030902101d0a06081611010e01060911030402130903030204050a08030c010f0c020d0c02040603020411030a0b0a06050f0a03090b010f06080906090c0d08041206020406020c031f 79
    0x107640402c03441d1210210860083c812800380322a406800c4d0185151880422060380c10000080c2c0110304041600071600080208458294480300c600070390b5030802e165980808010741c0010141c400c010001d02c410b00da101c0c61414944001d44000307403c50080e00380101d4103203455101c0000b262191401510306a607500c000340d080115900454480e42002401c101003000074802d074030305d112054405004240402201944841c04100714a00303128403136090108542d626804400555030080c810043d00c0355162000c500e0341c200703c4004002a1814048070000c0c9007488002046034081ea4890b480c1c001e80498200031900f00d080c50030f080c103455440603000a10364200b480d029110158090003560701d011030041c60844094030810080c1c004001b032026100c0301044e448943d200c1912881442c6610f4075003140544265880080c21240d072503c142c040144540007841200e40c1079003220301e10108a0704058880000030400419032040103200b41c42401e164000c0110300500c2c0390719130171618022886 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 244827922 1250 244826672 244826689
    0xa020405030109080c010513030f110f0f010501031202070b070f0618080306040b15040519090203070c020f03060601120b0102120c0a0614011a0d06080a0c08011107020a0510030902 79
    0x200c0e82c0010210382c12110400c24403485e076206c01e0701074450f20000e140b40c49c080e2509480306072800c104401d400450140725420801103049113030030000c450400c510070003214002c0100307000c06c40c2d910751640c0b02541d0003480080c400c0162070701418180d1800c0200c0d0707038502c3e40800f80c203011240580c5840d103c40c140600c107003c4412940c0101602035a0b46455000c210071030350384c0d05401e403080251000c0c400884ca10002940c00791030b8142c0e280741c8140224003c614198820f41d004030a9a40000304000d0015030055521001c2031096070b61b50310600000d0304041d01c441003202e11900007401d0340c22031000d08600f070b004103101041c1030064850300c40c0d018408101e00ea11103045400c0ca9403041460108003c11380c480c5955011580720714070070b00d504160800902110385a1425240880440c884001c40b04680c0548000c040c1442116420314403441c0001b0710303000c648280e5480c2d52074000b50311001548241100d8000741e0051201c5109410700d410406249501c2c0152420140d0722a0301100507105c5202 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 244829172 1250 244827922 244827941
    0xa0f0c0b04111c050601050d0204020c1b0a0e0601051c110a09080d03111b0c06032401031109010507050102040911030405010608030a30060f0e01051f080a0204050301 73
    0x50b601c40006052041c0710301d2811040340401c00c05014180c140118002254160541e541180c039001c05910070700014010703010b607640e900001d000c1c124000f000d20a00c072075465001217040d600820303926500c10200784a100c08a980601041e41040781c0d1041864015006400700c4400000148008624201603540d070030440c2c1130307400f2921b080c201744405141004034410103540303450300f841070b02000610b076082ca0080d00e21201030f219400503940310180090169840000b400340840d601c03441e1581286e80307101d01300500444600713008111240154801c2c01111040c1c41c0312002946045204001106d180c4c1c0018001e0f14295070a120100c0c4c0300d810341c003d5210345140302405580300e0403d0300b001401c4640a901046007603000300000f4203d0f54001a001050740840c0006000806c0780c0803000400a0054a07000c54240c035003103011545100240311002540c07428074070000b20b60f03295424019101541c40300200e03501520a009165180f0030400c107a441010148054103050b40c2c0c4001c40e0035241c0011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 244830422 1250 244829172 244829183
    0x111030106030606021605060708031005030d05091f021c0306050306150a09050609131e0c09061703030c030709080102120105090a051504020a02011e141602030a0f0c0b04 75
    0x14001c124017641044202c482007a501c00000e9058501400a03c00d8400d034007004003c3d040100000e505400b40002c2a0000c21b0080d0a81d510507107158401020b0b40d0190015a20a940d017042c82c3c00d104070079800b0811181d40c240c008116981c032038003c3c5d003400710078003103000109a06d545000c03456803000c0c01803500601108988200c0345580d10304004008485030441c0d50101d2a2a0420100340d5036811010b412813440a141c0d001000740d41402c900b071180d884a449100c00715905071004210413418510100ca03070000082001c952500d5242c100d1113942d40c5c2d0440c0035401070021407511030300040110b800040a080218503aa5548882400d9800c0101040a81e4801e00010001408d080e4030955108440203010481e42c030701604c1c484d02d41c08ea8241e0300c81c0a2a80890140c9006000b580450000b044d56a46000800b48001500028100000c0b0000058103c1000309010180c54280130405141035000765040800d0200102d54480f10340740200c04004400e0307800000b059008041502581c00390 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 244831672 1250 244830422 244830431
    0xb060616050a14060c0307050a110a030909050603010e06220c06050d0b0f180606093109050717070308031f170703031202040302100207090507030203131202011103010603 75
    0x241480440c0003c40300c034182983d08003034100300b050600481181e5019446040094407008494000c50707c024400280315400c0c0b01c1c141030f003014150001c61420495214201c1800155034520506098684590784075140798010004501140816182071400903210100030350205e20710f803249040504c1c1c6a002e0804140c0001d0310070444c0071503000307211002c40e0603554001c1d003000c80008038943d64082c9812540c0300c0301c0380d40854095903606088038865030300181540400581060f041540c0e01c0000030102d0003007444641007030b084001d402031a0340d071a000307000781c00d54034503040168411284911825120380a035410202c0066440744c0514018480d035028180028000e85040d40c450280d0b07000002d1132010901151205800001c030202580d90500c1c0595040000342c036044003070700441c0c000962059048025048550380011948201c41c5954000c1c00b054490440076800c030b00c403e0740d1810480f03480c5452003001c1103c0e10040c0149100e14030000901a04640c1380100d5a0401e07008140040c2d10b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 244832922 1250 244831672 244831693
    0x8010b1e15160c06030507210e0318180f040f03020705060f040501030509072916050c131404060905150703060501120203010807091d010501080d080c09030a0b06061605 74
    0x203e4282c1c101400c01070804103d1400c180001400007000d8072640e030300c0c1044016036406504d9698010f106001108030480ba00d0343c00b080171554680c070011407024010580e412901c060500144401c60103042c40240c008019101e5440705070140c40f070454281c00394402d5180004064841100510040246485480d00c41c0c0c01d0a0005059840c003070040400c0b9400844103105c00344003140c0404600070501c5000000805101100300319000e510030a5807500d0816405c2400d000c004500c0404c002c4088452802401c461609102116a513003090305109140f4000a40000c0741503005c03040150061080301c1c551140e5840c02c84046000b25100000a61a21400c01c569600304000502e072032442d080030340c03d42d03050421480e07a440f203d10600015545070708c40c06401c2e03480e5141c0c40c0d1b01a680d20009010382d603100c00000b6541d61400c400318001030386003800150701c04e01c40000d82e007100c40000c01402c0016a50340300c02c41c078440060a002c5e808502042003414030094603000c5070046204030040d10290b802c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 244834172 1250 244832922 244832933
    0xb0a030503071b060f020d030203071103030c03010e18030a0e0a030609051f020903032703070f150507110118090204030b010315050714031308180a08010b1e1516 71
    0x3ca51003641030040c0368a001a41e20b40103e030502407a0100d14005031203548220040b900d6189002ea00d995a0100205002034030719000c004505868010b82ca6070f0030b5450300401c50080b82000c9401c410b450304148001c0d041213208e0405030316449401400207900641329125a01211413800c02185c460b40301d0551407540303d17031541078500480d00c8400c0842c1420f00303543c0842d48034840c00205051407000350b403440c00b0035140044419640b20010303084440701915440d698445021398026030002414945400900c07030722030411030300c880b03a01101944800c4040c0c00152804c484035140344294803031306031011412048620181008501440328015954958202a509400000c007c0d0559600b01010805502c0c2c20008205604003800c4100c0da0700c5d0340d040f28210301324171004401810f6200010304822588000350f40b2101150303084072a05040e56030340e91803600301c0300c500034000d8001c030a0042c119100c24480780300848006001d052804200c12044801c0401c0c0c2c0254980c3c00300c0c0103085180f400303010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 244835422 1250 244834172 244834223
    0x90102010c0504050a0e04050111030c030403020c030a030f080603071715060901030f03080c090907030504050606120c060d1404030f11030c060105101101090302030406021605090601030b0a03050307 87
    0x1281818a10300d0513081a020602c00301003070003804121400c00e00404c080000961204040d4000305041c0303a00c9003007044954846a20945040d00107208030314280761145400720740303500003e5041e1281400f1060000050307800764001400076030b05000707108000404085c9540c00c509240c1d0044042c050418a81c80326034500c080141886008040d9500103200060740342c010a4141901030070161000d0ba2401413040c0541700720b00100ba0050300603400d00000c41d800d6045540218481c1068a4903603480c8001d02114407914042c803008c82d4440c2e80aa551420300070010480c2100d000c0011a030701c804080035070034012007030320120006001c60000c03500f5140d1000709200c2015580000e945000e07911031496523285410700030180726103188010804940c0c002ca840000100b00079000344104c0000d400e010b03441e90803521540025020f044290018080350f05110030640300000d04407695615031070300440c010440c4418841d0030004651010001c150108098190301d40701d80c3e100154200803c4c0c003402e010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 244836672 1250 244835422 244835441
    0xf09010306060f1e030303200f0403030e0303070b0a05150405090d020c0a0b0409050604140702010b010e0301060812030402060f280804050a150f0c0815010819020a020106051509010201 81
    0xc0d11030400c40100d244c00082c840341103035003510300841c4981c0313828a500c00e410501c9400202c0c6900c0021400d00844445024104590007074991000c41e900240a1540300c0c81501e000500c40c151034000942c2c08032082c0c2c031003030300000c2d445036100789071a4610129044410a40344074106500c80031007100910750400540a504100341c03000000e0074540482e0100c3e500850044040958582c8005011500c403680301192400c590244020242481100030b802402c03c010384030b0009100301d204c002a818140540412101580024102020203a9000c482a040904100d911442c00c00001c0b10000d120000741c0f031444000060242c00703441c08005030007103502900320f5109105041040101148010a61141c0250428050481d9000c850078403002068028074800301c0703d2070301c041d0340c2959030b0002c00b89100c0e28940798980140c0a092006507100c400c2110111062440b90103034840001c0310b41c0152014440b24000840c100d034903100040d00244612040c00301c010303004a101e00701580d09000b00080e2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 244837922 1250 244836672 244836689
    0x30b060a03020607080a0323090105100f030b06460e0705030702100501150801080c1537030f0b13020f0c011401080601060f17060f09010306060f 64
    0x203092460780440c10710f004808001d0013904000c920120b0040c040c3d0032014408554802a218a01382d00d003440301c1402058078400784540c81d00e80028406e084100e015019034501144000c24035140d07075039400078104002d1585812062044ca042c240321105001190701d404001c20100c110340c0400300c1c0400b4141c1081080000001403501000646034208040360441c07040d01c1d04991300d070381d60034041c2d00d0210350900114580d81351600001d0500c0312070a00c0b070354401d45a5140381e200d90f0386c1c8441e01c3d550b162050b1026444821107803000140c5480300000c00d5285502d460307461403154400c0d159441c481450342d0f04500c40703418140400b07455a0520a070b0024140c0c5040412804819001040304025010034503507032654002000c0b4041e12031002a15200c104c00002444294440700707044283c84001e10036a82d03140328000001c5800e0703008070412207441880b95500216191f50070840c0340c288402a16a81d04040680f091400d26161460028083c600845001c91540e00d403001d00782044030198440d021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 244839172 1250 244837922 244837939
    0x41404050f060408070f03020c10090f08070e010b0a0c0f050606040e06040c05060307030908041401180608041e120201050f07090e1305250501140405180a110a0504030b06 75
    0x600e00c04c191406641c00501c15403201711640b80507440c140c414022550300455084942d1501399016888005a40000070b024240f40d41d9064845d5540d4940c0c0030311114290048018040c8402e19005004061031f10300e451003080c00552501c0c081004e07070714810f0314190170000400c0040d08040c001d0b0041020071600602e000e10382500d27011f0500e46540a403500c100400000b1a00b85072090700901e4125800071400c1d96070b20740e41c0e0820341d040446405000e01090050100380744031a9a0002001100c1503612101c40301d945681e541000d104440c014410321100703040d80000428140b0b1104081d420141d000018681018014041d103280b008245404010016405001591100161640102840301c19031081440e500e07045040049030075081c00c1e22045015480410f118945415044503000e886014400d9034181903076002d0f1089008040c4c2003d100d000017502e03000c040400c664004a0341c00002000d60849010b582c00350f01ca1204c1500040b40880c09000b0300088000035500701000311032405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 244840422 1250 244839172 244839181
    0x20306060a05180702030d141906030309061b06020a0201050709171b040207120507060c030b0906120c06030a15080f06041b05100c031d060d0c0509041404050f06 71
    0x1a9000e000542c0d0381c03c2c003044440850803070340c02041603e038007103464181889000318800c842100000c00710f4084582c1c40116030b05c06505400d601c42c000640b03405a4408000310b04051055a003c40140041c042d40c4000300c41d03900c082056480540740c45801d96001286504202c3c1380240b03a00042d8000652131310503110f510088107000203402e03075003181c81400094992494000a0020700960002401040440d14022038440d8010000c060b40ca1042e402003182078410034046003282d512034201900520320902254681c60704142400310190768104644521645e034001c2401900140c801c00b45540c1c49180ba050550501c51a02c0040c106000041040050702124030b9600c110190026140005524405d100300e40c401548002604002c0c0150b070910f42c0940000b4001c0c0c0111806400244841101401103601e400000546200080c501c5040c00800c401c103100500d080703011502813000800001e46182c40360f000320f04c0e100060307420305a5540f400d030030603500344056a003060030340750007250401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 244841672 1250 244840422 244840429
    0x5100219020606030d092105010f021c0506010c0201080c13061107060c05030a0809120307020321040209010b0c07050312090306131a0a061205010605030708030a142212020306060a05 80
    0x4080726540036050301088481100d4503008011218081c2249d402c1a0440d545a012a0002e1821a12a02e00c652011a510b02a030f800c450060ba18240041d16070012640598852510075801088c409c0200c0e00d040d4021800d000c2e403003042d6000c800451080c040c1c0c1c410019041c88242c000308401e00700003000c03007250742c0c5868403442108500b400780503a107404070342c1300f9508010b101e906075418a00c43c1d5880c14014000b035600e03040303120004001018012100000b128000d0300c0c2d030080d039010b042d14640341d09082c0110320540100d5901e101078402c0c2c42c2c0015607a5400c012400d041050300c2c540e166070300741003000d03d410050010945100c0a800303040e5400040e0343e107003400c00c4030040ba01801c0c45a803074010b40d075005080150f10982d001304441181405000c0198402401c8420440031035407c0c41c0d540d00d107140c690186070846070216142d4442c654051501c00014aa40c40e00c0c2030226601d00303010100c80d1413602203600000040c041241c0e0300c03402c40c01c0070000c00d80c0264048030070540040c6450000b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 244842922 1250 244841672 244841687
    0xc12050c031608090a0e0f06060c0d0f0210060303080a050903160303020a03090209010306050f15060f0c1903020a0309080111070303021813020c1506030606090405100219020606030d 80
    0x2a24030303844010b040c450521801c4003c0d0340e04524003c0582c28229034036001480900c90540d4101524017810011405a02c0d14508450700500418040c20307140b81c02d2001610400401c40129007940a141c0108107a20400d00c1a50007942c0709865803155418095904070440318010080409a402040211050210300031030031550796061801507030700c0c821218120301038849184001d40050340b01c0d0010040040c580c00491203040700603911049691503201c40047e10903414030468100d80e04101281084030b58200030411441c119003103d03600010018000c4d10b41c0c016900980060304010340340801c040e441655038009015400082c85031f00000ca5064046200e0b580009040c150f000a0610300381c4404d00d000c007840e400040c0700342c12103002511020043e520080340f43e1010302858019241c2e00460480e514001c0c0300c007a004041c960344a43c28805c1040b00500140d85900c0fa5a41c00806000c0b40c0c00101125802100b02d035000c0c003148040a403a0010250106110760000042440d80b50307444900b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 244844172 1250 244842922 244842937
    0xb123304170f2a0d0c021003020d1409031909030b0a090620130902040b07170c03030910061202100302090105040302122508060705091507030c12050c03 67
    0x402960b14800c0d121070b01d80c41c0c4200354601036200149100c0d181e8807200c84090200380f08003002914090a03a064007107808096140000350320108142e0443d55003486a805443c45600742c3d080090b40040400c0145502502211000c515600008d0171400c10440785884111200040c1012240142941d4035440000002031040090603a0780e0915010b009454001c0c1c8070490221007a000083c800c031000c850b05901c4903020101550880c0c1000507500054400c890882d10207015550070000c681c0d450004281207076010301250f080a12001c031464201b480110700441d0444020008070300008080000d0b1415544490940d00085e005e1001603210805800703010199440d00591380c441050050390b1600844e04003030740014140c000400c071100b0001e140020a03402d005800c0451030480540c64200240c0e00070b4804a81000001c075000c2c034011000b030059110028044c00b0201d162043e400c01c1d540144406a000401c00d550400a03c02c2501e580401c40b460351030f000e0328007010f00e4403603075a84c880c600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 244845422 1250 244844172 244844213
    0x105070e0d030e011214040f0b1501050304110604080709020403110907080601120e0703030201020403061805030d05280b040e3403020603010e0f010506120a0b123304 73
    0x307128903502d45c19405092004001e90352501503041c607040c0f00381600340f401411280115000c02084821824603401c10201c44140e407514a15559079540558040710350680d0364102405110100310350200344a8000980440e400c01a2218038500308600c80c41c0841c40d446028034401d9050240a580c0319100d664001ca080c240400c0040c542e00002c001011001d441543c2c41c015818080105607041d0020821a8001d0400f4050b58001c00c080c0c8600300c0040394002c00c107500400c611a5007075000d40001da8003072201c69000d20312003241d40014445903407600c2511074071a0743d100002e07031600d4144514949150410001d200c50341d80c40901c00f000c10382d8841e800303086541d001c0000100c00841e0080030051176000d80360640f40d594403141c25940c440280e980712103003524080013183c00d04081c01038942c03143c80640381460030b450b41c070050801400c00340760560b00201e580d140b54071009400c12450000311180908140b13404140f40c0604074030800c080c80c102900700c220b004c0c04085100612811450a10103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 244846672 1250 244845422 244845437
    0x21020f071e0818090a05130308100b31030213020d020d0e010914161401020a05011b140304120509060714150603060708010905100302120105070e0d030e01 68
    0x80207a420a1074007a00001c0c1081400207441050702d4546014078611501940e50080030340320783e001a4243c4034100c440212030a200b40760000401c2c858044150411102044966019215889006607030303c2014060b0b400c101041d6000f100100c0848040c044403180304800800f40d013180c2c000389081c9034140c40030f9691a00401d548988000fa50f0465904004002080000748049080a400b900d03501c10190f94100e00304e010710500b00c1c00882c10042030120b4849040b031041c00c2c40035a0300c54014556030a07045110300e412080010702c09101d004032a1891034900f0849418809004140c401100b410307240442050042c03000207800386c4103ea0113241300d802c020b51103110540100b02c25000b5118050000b144200104940344c0000c500010300000c90f101907c035654803141450340c0c0740401da400b01d00058500300104032100c0d84d0741c89260450400a015001d4a940e070700010280170221440c100f0710b075510001c0c00780c000d0f0024031110b00040c042d5010080e03001d01d500d000c2e002c41a85000a03041c030000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 244847922 1250 244846672 244846703
    0x9151611060c070f030c06080f070c14060403021b040903020c120a020604030803040b0106032f1b010f05010f06270302040203040f0302060604060807062001050721020f07 75
    0x7250103a403414405a0115a040c80e926160700c0700c018803030720003a540d013912440b021452610a005091083c0100c603114145030300c904000b03d50040c1c544100382d07401c0281030300b2590072501c24054240107a01942c01000305031544039800c40526440340030244103610f00bc0d40e02e000250041a440003058046600e80c1550a0b0f03104c0c0d1341d003848486000254800d00000b004000c0015420196008038011091510260307200c13803080d4121035401d001301c6e00f54030703400d40084000c1c0c41501e522641c5803e085d40460509090b60040c106c2d100d0401219020369440c0d00e0310005460301c0b84134150040c048101c55244551a0141c0503107882c00c0406d0b50000c0d07040c03800004440c0c8084082c88401145e010f40110340e80e240031f0804409100641e1070441c014040c0d1008140989030600680054500e880081c041c9580303424019201c1d24011103108100301c0c18082038640300c000070300c1002c0c0b0039a455154000300526448202e04040080080c8004480c0305018031024410001c0980d0022544000b582070840d42c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 244849172 1250 244847922 244847929
    0xb0907091e0503010c020a0515040807150b090c0403021509151b0304030308010612090b0106051e0d090213060b160203030d2c010501120b040c03051209151611 70
    0x1d03500000d40642c00e013258005d6069002a084900c1400784d019504c03841c00c4c0f00304040b4403401c20b48010380b4608003440504040f442030060881442c400b841e001078840c144030042000060110741300341513000f02007000c10079401c003c86800c4036080641142131500580b040010345583e200440074100741e401041c42c01880e005440700002c0c940b800011252110740d030f443c0061800500b40101000940403030000071861585000b00d80f143c0382d00c10844102a82000f0b070844141c2c001802c0c059164034184c40501003080b03108010007110030904c1000c5080507141c01442226100401c0c141c1d082071508100304410750240b4240c4040d41641110001d0046035800000d203503020710710011448902e070024100301a001e41d407008409402c400500510001802d28803401c0b01d40906c58140300c042c4d0000c400e0005000740040a0b0b00a20031154031714a44d80300d071500c3c0d10381018a0080040c14000207100c80712403405d40e180380404018941b00c14501007130711410040046038000014640301d21090448225034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 244850422 1250 244849172 244849229
    0x30306260616180b07060c050316050309011401090e0708060c030a231602100213031220070302010201050627040320010f0b040c0c030c0204200307030b090709 70
    0x3c143c0030080030520f4550484426940c070110342100c09501d00400050040d0041d41640d100b0004840440b51529200c40f0946066200034200305140d541c0d40c051003031014032080810302905184000042c0d002501034100e182080b135170000c1c101ca500040402c840507042108895020b00b90400c08505c0396941c3c50408843c11507180114001c040341c104110882e4240f11504510508950840d040d4130381c511908022885068800d0381e100103070280130b20200300144103042451401d842e0601e010000241542c0224030300034052030f069044018200305560f824002d01d500000304460859000d1192410114210048a2103103c800038030740028040c14001d40e0801c0303100e04121101e43d1310111800f03005e4003e11059411518180c07a0901140c128202442070840309032054a0b1a6440c01e4291000e0360380c20700c0712100301d0b40a0f03110301c007500c070020108003c4907500703083c21b1406032a401c1143e030140a442000c0c4940340194404010050a1030b40158079a0480d00d0b020039060761081ca9070100c501d41e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 244851672 1250 244850422 244850447
    0x305310f0303020901091e09110c120a180b0412030e1f090909030509010c084e1306060e010605120108030f09130e0109030306260616 59
    0xc950224018140c05800408140c3d1003680c802e041c403910780c9010040c02555001b20084085c4a0710180400103030350303010542030040d03420a175007400b02c10303040940381013500c001301200200042000d1842c40d4000b0382d280341e01a8003040141490742030250302c407402c3c05031f403080c8003903006249900e40c145405034402290b4400b0140c0340305020944904039000030071101070010002840051300180c1c21596100d0402202c3d4075075200c0c0e07d007504e108011144440040c0066950303840410154500b412044000061030441685800d0184000e03107528001440d443c0d94858941c5510640030f410911b005a010391104032070a00c800042ca160034080000d00c1150850007055011000115205810802609200c52010b10b419510380e01c2c1c486181c0c5034001d20300000f2a41d0010301c91034481c1d10b080b8035400115901510b000440740c8001d0240c0f801c1d1050280241d001c26030302c007820300400d85401d00d14900c021913800154200c207805481141d8030a001010003140c1d1101100d89401580301d0400503486 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 244852922 1250 244851672 244851683
    0xc010f0e011206080102040f120c050d1b140103110c060105061e03130215070309060545190306050c090a09021908010803070609060617010f0c030531 66
    0x41d10386070115135000b5070250189003400c1c5101e80d07001809018151541541da80c2c45504840041d00d0181405150307088603070205d541c1c41000d60400103400015001ea40146034031040c01c1d04088200d00058125a0055900c1c405140d003001030403007408d4006001411660240c414a603105030108082c4880c9510341c8078800c07014000803e21485481c2e8107a0188070034001c80b4520384013001400d0050980c4201702c03005002c515190010400503001c0d401901d0071300310760710740c5c19540384d0160031808144190524a1407202a0045c6041090702c1200c2000e00325681034400f11202980030b482005502440e1000802140e1200b000a00c00030b41003041e52580400504001071154403040740c10043e420ad100009a1603162030010001e091013160401d040b1103805024600d8602903489180141641c0f140540b80b41c4e403260310001d410b030a6241d510300e904140c40e00001d600040c0c83d01c0703481540d040b825020209802d0030709000d003031801e800d141462031940340791000e22803080107465920ba030f4800074083d08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 244854172 1250 244852922 244852931
    0x3030703080612190606170a080901021203130c2c0402060c06010e010e1501090902030406061a0909011401090623030a090204051018020711031009050f0c010f0e0112 73
    0xc0c0c902134003424051081030144442c64480395642002d00c3c1c0f16440800c031758021140b00003c50070410081041c0030061050328107815102c9058000d0340e01c2a180035242019103120401070251500700707440604641c5403003500759183c4642641d0030881c9001000119110f12000c10115610981100c0f1040e4411090300d559681da912800070036202403050320380024106000501d0281030300380d6000c40100503101c43c00300d18244015030000750001441240c0c00c90761244003113802d83d4281d180100a400d400c0009655000000910074818010307031140500500140035003003540e03000140c1a054401d10318140803d000b003440060401c0c1e00304506492058400402c2c81702e1644541c10203644903000340c43c280710540701d001100c540303100f41d449580e00c04012903039042c6500c1200d40040c910a0b001c0c5100c0f171a559180342c0000e0030003100e44990952240c2d651b1860003080300900403900000d41c0035000d40403520348900080c1c50807814111803070030400c10001c101c0d5560300561809542d106200710403c0f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 244855422 1250 244854172 244854193
    0x1c050d2f010b010207080111070803130b1501110f0a020f06210109180b0c0c030c01050f0406050106110c061b061311040b010c080d0e0d021b0d0203030703080612 71
    0x5000b08086030625005008943c408186050f05003d6240c0c41c81c00070700c041e4580429a1500f20030383d000900b2003c080b0310015a00404142c0d0705c220640103201940f002c1c810b8881860014200f50300a1032240b02d0b50300000d020300034000c804524a50566010381d0340c10001903401001400c00d10500d41c40740011820940c84204c2c070200c001c0d00c94162409601c04000c00b0400e54000945400040030003820600084001080903a80c4806070200c5c1040ca0b0480381452080c131612400d64808072082c0d0803510300542040180003640c0a00d9005010301d0400326201c0b140046000d44035100544054091a00018941d1100b4030300b080e0700c0c40d56880c0006581881c20014a404c0b03440310f614009844a003003440076a01c0c4c0b071900b032040080403d0141c544c005003c20715500c410381d0b0782100f00c601080c55603441c0074402c000c0091001c1111020a42d01801c10304c21408050008001e601c01c200d40601c84007070003800148c900008941d12550142090110f9645100020f81d4408152440043c0c81c001c518950 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 244856672 1250 244855422 244855517
    0xd050705131e0e060f040803070309020114040803130b0f03010b03040f0c121208131509060c1808010209010e010305130c080313151b0501020906181c050d 68
    0xd0055480802c00e80f54192174404071a14100815600907000304000c20103d103a040c000c2c3d201c842d140b441811301d8104090381c0e050398840c0e50490751060400350800601b4030070380180c0c0102d0342c1c054020402c0c440c1c1080d1130703030030420a1400140a4166414000000304083c48042a6607a000a41c000400c0d211903807a230071800c03a03a40605070102c0e101c01403030358940f45441c014a03905101c4c1403c00880021007442d6150103550f000003d0085043c1507990410b640410400e0140380c41032103150715043e07860001c0b4102d00c21a461144e0110420364414004c03802e5aa0344841d811000e05400d1074042201c1e02c9801c00c0a03101d1340072003001070031103030b010b9000a60300501001030b02070003201d91400b4051070365821320f60041c01087c185060024580a10300c1011030b004045c0c80280c2409000014200035914010402c5988007101900c28404000660715151400200f001da060004040700300b6a0300466842030340d900030786a0114203114004076240542e82500c0f44684080c2d81c004040707420a50945c200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 244857922 1250 244856672 244856681
    0x1c0309020907090e060406060e150c0111070c080303010506090d020f0406240306081c02070e04030924140309190804080c0d0f0318051806030c0d050705131e 69
    0x2189100714113000041c0d51803805200e018111000c503100c4030b009805a90030800f1500300c14040a4641d941032010704100f420074802d030510100b81c4500150381c2d2086050110b21005240d0045809620410040c00315032594000e48008580648001407203107070300e02c0024440303900d900215420502e40240020303000c03400c120a40d000c0b001094400c61300000f00300110160b446078065110680d2001c3c0d14010b4100384000c0820b20403c940c41592400c030b03241c20142182e0300701910180d0014102e00b40c00d00070b082890041d10400450225420003c80d0401405851000403048465042d0004000520810800e0049200303044031401c15041004162170810510740050080d010309105400b940003880c00c05540028190307030890612038503020159000c48400c0c3d19040c03030300d0115024140000e01c41d101c1103080b08285d0385040e141d155070301c0c1600a151410003152449485072a10300c546030089880861044155001900d200c205d444c80014580c005d0610000b40862140090f1060007103c0d14540c403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 244859172 1250 244857922 244857929
    0x40e01020d0609061502120a0201061203080105090a0e0c010c020310020a170901061a0d0b0603070807020d030c0509040e010204030206030f0103050607021f1a0303030a0204170f1c030902090709 85
    0xc0040381d89608507511600e00c0c408806015070700c204461040c81c041f84000d003000c000188004103411361901c81040c025070840d03600700c0119504c04014005481d000300c82c1d681c0103c124004010064100b00ca081d40c0c4c000e12503109040c80011100041991001c3c412512000320804040d90343c1da1801c0c038002d041c4080d00001104d0241c0c0e00b00850f0b80c03240306000307117030480f1802000840c903551041e144c1d540c00c1d8040440c00581507500c8040c02d043da252440a035103e801540c6940006142501c0040d06110003880404e08042c0703005011000c0680200985503a010250b9000507281c0a100d6030600902c296040658400c00102c20002044074250740541628418001e4841640710141c2c140e075681c030b07104141150804290f41c41c119403142503120800b000c41480940c60125142c6020a045d07034070a0380e00c4004c0315000603040c0306012482103103c2049501300c0081580510310654141c40b11895201d020505501840d1405603c2c80794000e1003203160010060340c02c40c1810074000c1c140103081d10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 244860422 1250 244859172 244859189
    0x90c1005130e09030d06050d03090501080c071203090506060f010516140106140307061d04050c070b0c090f0102030304050a03080c070804080a0b01050418080d0e060406050105010917070e0402040e01020d06 90
    0x3d007ca441c0c10a24405040f459040d02c030007840c0c50a110040d526007000401c00703180041c0c00e110b03c1010034021880312045600a80740003940c4040d40c00e00398105240104103034025003101c0044480ca90388401261083d80c2a981550b0303000102d494180d200400031100d180c0950b09115010450154021052410441c102d0444003800d81d0380030306840d0f00428500d01d18495020340c41e071007030a0800d0707002183c1c0400c41481e903502d000070550760100d81c000e090302d07059220320307012412000d035051280303000c0003100c0b090004505501d081e944083d078581e01200020f04010700303400400d01c3c148204c1e050b03071800d5500c01d40c4141c4580e10f400741c0300c3c2d03502201032066a000300350400000d00c2d13081a10608202c180d043c0e40110001c441500c84860a900900d111402c09656604c42c20b01c5400c1805801d01861245001081075450180010110101c0c1c2d0483c43c40c08020f03503494441d0003000104003044807080940c0f11420390b030702e0002034001d2040b165203400b00d500029001e00100001d1b4460b209030740262 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 244861672 1250 244860422 244860431
    0x6030f0b01050424180b19090b03010e061303020123071701080a031d0d062c06010627060e0907030209180402040e0307030c0506090c1005130e09030d 66
    0x142c2d5407448003078804c107081d511501a65040c0b09800c90f480c484050907070010fa0101e001c652800c00f0445180514100302c14008204005210706400d9018804043ca0110000c2c0503a04042151548a01c0f0107003240d41018804e20b20f0307200b050f000f074004401e80004401c0e164103500140703541c0000d200d0f0403666400002c2c1010b15400b0702c11a10b000190580d261031009290f10f140940d4103031101902034444802c520030790b0301140c11596882c8040c045e038921504000c0380d0041701d20804052620440500d2100e181a09941c1d040100300151050466019140c08044140040d441c007161451022070107006c2a003840340410740540160303804024200c1680c840e02140c0e00c0c040110220300030945070a521400360a0040c913250a1290110381160008000090240c84800203d24542c00140d040740481c401603447d01c148172052200c6036001c2034045c090548070055400042840001c500080300380180842c00e50351000324080850060f04c0240840c0c4007908020002c607540790420391101d40e1060a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 244862922 1250 244861672 244861691
    0x3080405150f0103021207090612020f0d170a090308131e03051b030c0307150206010e0c0403080a050904050f1519050603071407120e060909160306030f0b010504 71
    0x7115a914850b00700440c603060b550b400d5500700403d40c01180002c110921482e2400b15091084c0c4c800e00e0001d000103d0a0002c01a00c1d105004c815880b00100328484c02041c109480031403008048080990258032003180d41d114000001d03240d12070540c0024050110114079200103e0030811103000b03445480044100b210415948503070300c900b01d80001402908550b007400c9181c2030140400102e49401002c0c4d13101801c0d8103000c17034500101684045c203000b0384100d4100c00740c0d40600000e805000c40b0490200103140c0b20403c040d407403083e0f100041040e00b00041c101c1c1748510802c02c0e81c0401c00000d00c140640d0030302d00d81030a0400010303160484c00e021201140c405525052900d801101d42240c1c0c040c8145203007e08100d200e0700020449410700c80c04030008000112150020001d1038410500c3c3d118506200350000c1081c0014000c0501805080000b282e0b82d0307851041265104c0c851060020086034141800c501070009944024800480f420760303041000780b2109020f060b603000307942c1001100007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 244864172 1250 244862922 244862953
    0x1050402131208180f0f0603060a0527010608012313051f2102040c051c02190c030c1b0807060206060f010e0d03050702030313090b0f030c1302030604090f03080405 72
    0x95005d0983d902040d400c91000f10b60801001455100c5030040469600e60b984401064030009010042e6a50001c0b02e10081c4240d04ae0140d00f0740980310618203c0440c0d03040203030100c1c11030804000301840210300c84442516684500d150038102c50440c3c0148518140505880703031401001000076400607a81d200815169130040360500380304142d0211075411041034007480000c0507880d1444081100030090817200c8000714181d034421500365440142c2e07802c1c600740241c00d01550081810208580346414070007080e4030a1580c0c24590b003210344142c0c0101c1398501e0f5060201070b41d11400b141d0042c2c0000060994010038581c0c400d1300e0580f00c0b20082000d040c01101c2e2907030154509503100309080d100102003441040500b60301880a07048a03c0c0001c1d498010440d101d0980c0120f804c50345440402c030803403d1102544600d0242174006102040c00c2400040001e000e10156040c4c80d130380440002c1c11542c42c0e400c031903078040d0003500009441280d4240104005c0d0101c80c240d409100d0040a2003000d130 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 244865422 1250 244864172 244864189
    0x12180f0121090215071a0c070206030a1a0406061107140604120302010b0d0b01150201051510180b07170301060f031107140d0f1103030105040213120818 67
    0x400c084820000e54001c07500d800101076180080c0c0c1c000ca1546180010882020000c0017100c2c05a2150f054002002204511798907000b080d554860700207010000050b1646420b40741c200c0582c5401090079854042400c0d02c4804e0280e5456106050201c00200150401c001003030007403807a42030f00c070410380f20000c2071038910940b038016401ca1000c01040009172205881c1d1170000e40300f88000b20b20400740c0d200245e84181000c42c1518801400e2004000c5003055580321009945036000034000b40c90711048280040a03c03c018500a0710444200340e0500d206040070b801a4404201c3c4413000c6480c0c1e00100b14176040316404549e0070b60290100c0e01079031100d5090b41e048070400d07900d03d00f202d072075558110080c1941c4100c030901070805004800004015161500d01c45014100408001081c0c0200810040c1d41c0d1034003409110302e4a02d00100c0c0140030044074151201a2400b503a0303542c254058003010030655208803488184000c44002700480c200050811003624942014030000c64020802402e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 244866672 1250 244865422 244865447
    0x160306080703020f1309120e0102190b0907090f020d0605060f07080702011707030f0c0e010215090f0303090a0302010c030203010501050d0908040b0f031608010b1b12180f01 76
    0x1580701c45401c1005240040c0070510042c006004294041d410107036640139118150021240520341c00c01809040d507000054880c641170920091010500c1d903110902566a00324015100980d100000384407008100720290041950400400c400e620304078041000350030402d50700c2e00480c2450340009071031a1074425181c2c0780c010744031410f20740b05003a5039980e0142d200d1181241802441007100404441104280c5e00c50001d50f14080713040881000b03400b04a0350707011140f0050103207409086010b03990005003c0c1440920a003c09815110660306524099502010b81c103640300000400400720808150b5000306442034000f4002c403000b1100c1603060340400d018050006505110040100e5801c0c3c0121504a000f40c508070b180a03101d1000036425407082080c0010600b0010511040700410309030041e40300428a4800e05030f50602d00034803698840c000180c3c00700a041e08100c40c029406000784c110301102d0002c1e1a0762844580719294013100e89102e1544a10580c905c500180d5010f407500b030084 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 244867922 1250 244866672 244866689
    0x30f0307030504090b030106050a380d0b0402160c030c05063405070816050307050a0b0c0c1c0221060a0905031c06030b07050f0f0304051c0305160306 66
    0x4050504c09640b00400940031034a07815034a840c0c00041640310a05400b0151501d0801408000c881c03d199600101e202c68243d070039107005000750600d84001e101942d1140500300404240101c15a00040190286d41d52281c5e10115640b8060208020700b00850100c81c810103440322001d0b503d0017008464019198845c6a00c480b8400a203ea00421400340300c04041d034006114650342c1c2c1f502d40b01d18100e02c9410000e0340d41e206aa50302948241c0c03450140040108030300070080700382480e0108090369402c3c4288140b20102081d0140c283c0b2080c03050022010010f8181030340280a04031032072803e9902401a8042d590460b04000603100c00f5a0071030b54446140002d00454460f0324080e0b00626010501b41c485020a00002c41c402070a66803040c00700942e1b40021460504605000444000c00340000081c408100310b60748414051400740c41c4408041c5002584917a1181425802e0400600381c03c850451418101184540c0681c40303039014208174480d004440004d10400c0d400c84003540502c482 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 244869172 1250 244867922 244867927
    0x8010b01020d08040f0501060609260a080f0d0920180601120204080102030109020309120a08011206020d05091e0a230c03060702030d230411040e1b030f03070305 71
    0x380c0310f025445a64004d446007094081c0075100d52251800c441d85604010300003804800b0821070040d041d01d904000c1c0f00c15440c0f4058000c480c90b0789603a10700003003000030921040450781c0f0b0484100c1c4000e481041c8600f1400340560403051401103200b2041400000380d01710881030703180e0542001090a00c0300c0b4003908106c0f01a0700c40f007005403091141c0d05e040000c1e40e602080085a801001e0004d54024100c10b500540c40341031641d005804c19008082c01c6490107000c3c805400540d03031140303605044406560704404145287c2c20402e020340700b4181c809041a050605000029000007881c0000300003941010402c4001c0c01e80c2244c03103001c2c21402811441e9101d4008507011031207011076500207111004c4450060075000441e003407850031200003000d82c001244000741c00c40903005030245e02821582c00074808004101c2014004e030083d00282c01d501a40000c0002a281c90380019108610242103600005840d03016410030402241c26a00900420f05518900c0301c001040c0d642c4140c3c99140e560 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 244870422 1250 244869172 244869193
    0x90501140105060a0e03010b06040314060112150b060d060303200c0f010e030c040905340b0705010e121b010504023319030b010804020f1c0804090b0a08010b0102 71
    0x103e21280d5176410b15031656880d0b100380e20a580301e030018401148282e800400b0220702124490610005034000400c1d40044400e410001d45da40303032a0a83c4220780c0c440042c0595020010600d2030107500700300d80d000c071314110002c000e1503000849444c10700079220040410038159199291101c0c91510b07429001020076512010b5903016540c110000000501203540c110440c1d0001425540601010b507007030f40052034246900001c2c0c40c1c10011281c50036176410740b44196160400e000c4c019038826000b50010101d0340c0010000b0070341103019540c1a01048554407001c1e4441e0810550220303104c25031581041c025803901e135006005541c800c41d0000e0400025003440030585540003480388a8000e400144442d00c241070305050003030100b02c00c1c800414558004020000380440c0c00304040c0354103011010042100590341c0d007080c1a0005001e585400304401c00d426140104400540020144000403501180d08001030b40030f4a00a6800c0315100482551541001e08880543e0411801a0030020b010b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 244871672 1250 244870422 244870427
    0x3060903270e0a0b01030212040308070f17130f05101b03060b04060e03031201060c1e0b061201020d090602070302070f1a0f0d0c080103060510230f0a09090501140105060a 75
    0x10f100d513034107040140c503080311000a0411071008490480215a00405015041da40010340c108002003d00303211464020704154010a680c0042c03121003078940f44038124080003847c1918940150b480790844000030160402c00010b8030a00d840700c4030b4941d4030030800c41100c2c841e004100449152005281c60a030910004071046070180c0d144581500c410440d0244141e2100d501c2402800a907a034110080010314040d0303000052604280a000c022103421000700d21403010283d0043c00c1290041c5400c1108004180680200061460100e01d07201c03004040c803403160010702855109509031084581c4401100741c1808150081c0381c0100e8942003004503603041e900c01011560000301481c4c0c01c142c1c0b4100c1c0c0c00166680020f4540c00240034000401c108041e81c010350760002c00541000164034100010410030f03810411801c0007103a217110b45d018040c1c50f5a08020005030001c0c00c250540c40e21150003070050500c0d40130885183d80b030040300c0e14803078150b50030582c1078603001805240341c0303c14500c04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 244872922 1250 244871672 244871681
    0x60605091509060304151d030a080703180506100e0118020a12050a0902120304080c04021612021b0306060a050f03072102031209030706110703060903270e0a 69
    0x32002500420098244943d07030b03c60165100e184104018400c008a914550068811031203c026444102a01c4419050340100560b18650202c3c41c20029640c0e4180d8118041c207003041000080b1162a9204400c0c0a8081030180c480d40310a5003030400c0307030307aa4001710303a07211400d00c02d001030100c130321600140b507208030703001410101c11714a8018940051404290b0403101d080c0c03481112140d49696580031810704c2100c5a05410301d00001d581000e1419103c3c0351110749807000c440c410740d40055558240e0b4106083c0c00135094001a2030051040600f00181d95028000c06004003043c880c61038005900d4001032061148034080d081c0600c940c54142449000010459603503458090340e08082841c0c214039600740018810b017a03e0080d00d0701140185800c00c6e030308900d0740140881c100141c251340d0b100015824112401440c1c00c1d0004041246941c0c00c10175039420003020720b0300f4030f0012003d01d6809010000c0d8690030402003c2c081d07118805c003510408852240300c0007000400c001409008103a8407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 244874172 1250 244872922 244872949
    0xd0516020c210106090f1401080d230f0306011b050c1302191805010c0804050d031e02010f11030403020706051309111207090807032d050c090a06060509 67
    0x2034200840b110000d007609444540e004041559512081100c1403d40e600800700d0100c054224404c05505003103104c1d0b21006903503000014410103808070ba504580c05001e1540c54600286420f4445c1c40e61000082c50398000d51301c40d400120391804180d010105402209511a4050b009044c43c0d00c48905104040300128114075a00e5424006d13082a5855a410002503041039035824281c2c141c48001e540c2c403400e068200038104010307a008040080c0e040402c82d03040d140f045405505000c00da1404a07114440c450301d5134448501500c2802d01c8503015040300544042c070490034042d42c51000d61038010350108903009401030348510f90402107a40110000c0881c2044500c40400e001d0b00c9050310f8054603043d8203c1810303440c0018000481000c400285500a4402d2500d414030b036291010065854020b03000140c12001c19401603920403c00c621900548080b1445201401c0b07030380e0805030781328003408850a0040e040500080d151028601c903000a42d00d6a466140c01e00c40038409100f0b9102c100f01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 244875422 1250 244874172 244874209
    0x210201141902070608100b0414042705010515010f08040204151d06060f040b03070918050a050705091e03030d0e07180b0105030103020108060112110d0516020c 70
    0x6100803035a45284050141100c1c0d07001030807070914141c0000d014510040213413104240b4424207204c00c64105003150110741840c500d40071211241e000107001010f40ba01800244100c1d05503111491032821015440b80d40642c0081001707035185440221140d84040c10b0900040c68035100c5100741c1d0080120a0700203001410000390030700003440e0300c0c807200b0450300101054400090600100382c140300d091940480240c84060904201c9405548075004e6401038001c60540800011503003403041801d88020440c7d4600d110a030a00c4d0150b002c01014140c6080e0480790820000441c04c601072821508401c5014014542c40c44061044007c1c090031107507103d9044c0810401074020314503500034207000150010107020001d20301020030304101504ca127103004107418451036841c5030303801809890440f602803c01840e20760391100105d40302600ca80c1c000400c0c2d4a4540001051f42200001e448540144001000541c6640c010f00044140380d8000c0d40050b440581c030401141440e0b50b0001e0307801e840d00f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 244876672 1250 244875422 244875427
    0x50301050d06060e0106020a05010e0109051203070e04050406020c010b0301090209130f140606010206010e01060c03210f05100f05060a052a1c080702060601030518060f0402010921020114 82
    0x2099914210013003079105400503404005c1d00428000280701c0d070751003880c1e000000c01040d4241e0381c0300350300e82c0032400702c007840c020005c0300140c0101e001e004801c80301540148100203038685480e22000030740200540300d00545c0380061980315420140714244000c3e40007882099196650314207958a00ca206608840c01001d180b034090004d90905280142c051032007024244030328000d0002031401005070b2181d0b00c080f08800c010840140c01290154030070b505860047d140c1d070205201c2000311100154169070003468002035070803404144c2c1c0000d0203800000c2200c80d4403a0b03100d01d44840c0143d80d0046582c840c40030032178540800d0294004050480940507000312000c000110b41580081d00314801e00e0316009006903a0241d40c811580418100d01420040400c0c10101c100a41d608070062126040c90b60b904007007400e016100c44c1a15407641880101c48041c9000300c008901c94009441c2203011440c02500829840038805001211100e0707402c6d90360456469400459024840304660902e07940b08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 244877922 1250 244876672 244876679
    0x1b06060a150908010f0203010302100f050901030b011106040309060f05040f05060c070f2301051c05090f07060e030609010c051603090b0a0c051002030126010f0203070825050301050d0606 82
    0x780034071448805d040c940182ca030740c51030051100508800207800200000f00360007902c520340041c1601c403803100038640000e00b450f4840040e5402880ea10001010b885048104010140c0c0125144291041035072441c032807400c50300c0144c40c03d015a000f0170b0300c46004034800b407107a400c0c20741c007034445801103604948002d0740d2001612400c201580141802b85c100c14074403411500c0004030151002005e203009460241030302c005946100d9944407600d101a01c80001c640c800800b00644102404008207031003c00b5514800034098031209030846010f40550000204003080601c5241c030703000320640742d051074481c502c80e00d90540452a03030300310706105000d00007103403c904141c0517010b00405a00c41c007039440c0742410005d19040720b00310f400c00ca007801040140a01075294094040d070801880c5d440e000c7c103004004040c0507092811640403014030110400c11610b6202280601940c0c0c031203107554121502c001c0c1ca00080c1801078118000c5201000108550b0074981d03603170802c60b4000d003000110582c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 244879172 1250 244877922 244877939
    0x8150a020d0e030a0315050d0b06010903200103050c160b0a180b04150509101107050102030406060512030703142206020106060e090610050f16081b06060a1509 70
    0x4462004000c41c3d10204020903802d4052042d019010200a5070308286861300d0b0008441007110b60000340010040404101c2c1c0ea400703004a00080e540c8541e0a05401800e1503683c2c80c036050425130140040c1c2042e0100d840084960101e4103803094041c01c007121104282c48081c143d03480586140109030b52080c51110240311000b5420001d407083c0b920728440d0510b0b00341030b088040b5184841c440e01d0f15000500c00740000014140e44405c0d0080804075100303801401d001410b015840010780310754000010441000901d5122009854007180c1c0b4218036143c281c2000da50b400703a000f0007008500d21101c3c010000030540d000e03154000841c1c103404141030400e070703000450031041d51100340940e46031081400415085021012080e4054030614142e14059002443d103103080c904c44814400c00151074241d101c01c000444908071810810b092b42c4035030514240c01d555100d140300c0d25503d0034101466a0404000c20200c1c00342d1401010065000d042805d02c0b0340701e450307840008040c031864080c0000c110340d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 244880422 1250 244879172 244879181
    0xc060702030a0506010902030f0a152c010801020a23030a052502010c11010b0303031b0408030714100b030c22061e0608040203071701060b0c010509011508150a020d 72
    0x303549009601c908062104620146d000b0784112090340c104000d440d00d00038542f1030101150292060b0a15408010b00e15680d1580c00d6101101c00e407860f038002040b0528150020b110700c08142da20400405056a4081458220045100f980c00020404146119070741d27080729402a0200c0c81c0c0400d80e0084644050300440c01030034a001603510303508014003c64000d0188080c2030b107510024050845c080c40081e89030b02c0002d0091000410f014030320b00d4400901e10541e8041c0c0000e604607039031354a00b400e20f12800303d4050ba901c1014815444416a0007400d0300400100200140080c0401140c40b410000041c541c212101842411200c2c04c103e225102d0007468014040c0ae02c200d0051202c965003039080b1405d6402071014460004284070040e2070000301d0404440c50451290180300c0e20715481405403070b190344060340a08001c550541e10010641c0642e00508007d802003004103c0d0030510889590076210314400e07030300440c01040c503040700c41c0300d502c0d4001c5a1000041c94080d410400c9c00454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 244881672 1250 244880422 244880429
    0x303020f22140a03080c01180516050103140402040207020d020901090c020c0307060921170409150303020304060e0102010609050907030201170f01050103090609240606030605030c060702030a050601 87
    0x8548000742082041d901d5000001600c000c0e12415072050103000421121082840010000d000000703860000c004290701c1001c03c1c50a500342840a00400c2c1440c581d101015400000004800140083d0ba503000744110300412001d5140110300c0d0307907143c0802c0020f40140790240e8110004070405401641c48003e202c0c00782040c6000042c8039242028002d2130900804201c1d070280d4004001446080d400000d58800c0301c21000c810050400c64825256003464076100041c40344407040e0541d08148003520240084d20007201003080501c000d0103810804442d1480701a0140c0c00800c000d0050501c55119010a0401800089440c42e0f95004600445000b21100c0b0881c0d04402e41c148210340e48550031a80c9103a44580301c41140c10000800c400250041c4100c60515a492006a0800540c1d0f0082c4c4841030f04440100044201c0404040300c824120b50101059890301c2c0e4007191300d5000b442080141d620140082904641307506c00e2180d2030b07120359000ea9042c400c680c0c0b030f90006001085000d018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 244882922 1250 244881672 244881697
    0x7060e030a0311160b0408040b03071d03032704090803100302030c010801061e090b0c160518010504050604110301090b130b010522080a0f02181902070303020f 70
    0x40c1c003960140281202c0030000e01601c0d80d00100146050900c0294480103020340009010805841c0c80c9000c481d20310480e0700901e260b5101004000d00759400542c0d040741d048038141c0500c08150613074101900d0340300b1540102d518240d0440e40c1106944885c002e18180c04024000080c0ac4c0407075201c988a40d001141c900d1903550303501000340b003181018007020049010030300b481700c15541804800340c115400c00c1d28601c1880307101d08100516603c02c0050400a0910700c2e44e1580e138000d0004401d894072000b1200344003030020340b00001082d0502c00e0f000307031030100c1c40301001c1090b07402e10080002511001e0030042e031003a200c140d508140031100c002180203040c0480b00258031a8010144a14110b408aaa62845240008009141c0d0300306040ba585000c3c0b40c489500c031440064130189044540d5002900340e44a00c4804400304203850a1040081e402101c508540724100410300c0c0c0100c0c82254089480c01c1c503038400c603411030b030160044d000e010f1090401508004003a048404c05802117400d00d180c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 244884172 1250 244882922 244882927
    0xd0e03040f0803180a050a06030b06070804060206090d1412041406090d0e030631145a0a030504050405070806030303401a01080c04090807060e03 64
    0x1420a201d412502803901d0a1720540b580c980350000217a0020500e2045a090544a480044007640d40e2421107991690000440da100e60b294040296200000c40701d04d00781d84510001001a14002c11003507001e11000d4010350f00c0c01040041e151461030000e0000c03100b4080310080d4290540c8248010743c4110884401841c0803842014010709203904031601502039001002485216906400c580346181d00880d1102403840c0751801c500481020468003030324184031403441c014031100214108881c030541024559529160121011070f601c01545100ba01c810700701e61101d5081800d030102c07903d02d40b01c40d040009140c00b608407a400c081612404400040c4001000e0001e850a4452980c00c40000c1ca001e030202e00d0044042503503484040d05208511185e0ba038100c5c20342640503008003010350f02820304888040384141c040390882885000f1510f07a21640ba26400c100050a800381c122a1204001c100c02104c00003480010700b04d503101038605600800140000c13642d140500c0d030046111400555 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 244885422 1250 244884172 244884187
    0x20a02030a08010f03050a020405040f02040501230f0901170703050f06060114070308070e0303090a0e0702010513030203030708100b1305120307020a0306020d140906060a0f0b0d0e03040f0803 84
    0xb401e2020503040710120020415043c00400c400240088010703605580020f20354507070b402c00100e20102040001e50007800c2c640003150445401943c005030180a00138008084503000402c85000300f6000b2058104130f0b0705004015901107000755044501e681e40c20341d0b9113580c403611000c0c202040c965040000b51302440070b002e11540e1042d440c1c00e50518180d102800c00c0c43e1039400506014028114404100401c100700040755000c0c400c542c0210002440c407440542e907103e0b284c8014808a440d40c0155103008001240e19007091110034980c2d0707041d030195256607100142920003d03809045141d42c00603400012903090724074401000d40144101c881004985040104441482c2038000f10b4450340040c009040141c071040030000c152580b00c01c000d41c40c1c1c00c102c00d81d2002084d40041040c004815030040c810310301c0740400d029000f00000d440601c030a944840e41600c080141c0e10070170540c0181000509400400366000001c00301e601c0c0c0a41c2e19240d07498442900c80e151940001009400010701d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 244886672 1250 244885422 244885427
    0x30301080a0213020304050c0f01030605040c02011a03060415050703020d110309060108070503030711060d02070804180b01170709270b09060109031e0602040f050310111801050904020a02030a 84
    0xf901402c3d00b050540c0756113070a6a40c80e0b00d0b03407484081d2500400490031540402d80c00b0780c0100025100c040d204102e03280c2906c600078040c08c004480c201115024000f024110708010032110300c116044031030741600454140c000801440300802071000c141c2d090040e91a202c40c00d0181e0104070344902c414076204d05000000600b024010380c00305440d0b50242504100685002c03080e154619003201c02000e0605071407000c60100e1042c02500880188002403003010403844002500c02d4078038a00050540d0300488441e60300b00d450a4031803074040740c817000e40c08119034081c0e039140ba441015440c00c2c1e49460b5540c5a640316403058640d00c0040520003040460412507a4410b0001c0078404680c070000a040401c0041c2980d20140800b804150464a018a101c10490a0003500f00d070701000441d5500c0d900c610a0f2004606405094442d01400b116101280682d010703d01b04c10b442c041005242100707040c0743d84000744003001400e05000c01481100c0d4181e949201402001e14160003541c1d9555101e40700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 244887922 1250 244886672 244886689
    0x905040201021e07050d020301110307021c09050108060f06071202010c170c070f1a0c07030e03061009020d0605030102030f090c15030c0a030b1903020f010c0512030414030301080a02 80
    0x9032003182c07490fa03110040c544800604001156000d841070480ca0485002290240c0a0601c0860030340e0000001e021406a000508032280000c1500400d2010803101003201d0070249031045600144808010640d41c3c50000703614020400e00a1070146445081e40e180700b80b41c211030384000c000d0717591407041010951700300d070b040701e440c030700c1c1e8080b2646a24107400c45004078041c02c1009080d42038a4400741041280103004045e403516200c80504c2e2a140a400200290780b00480480028422070040801814001070441c01807100001030403085007800e882d08004e410115a00e038400342c4400000445850a100075402100c406811180340c0c642038175040d10b0041c040c07403810b010307460580d500031052443c0800d0380e070001e681038041541d40b100400c04a003d00b10030056142d005117210b40b86d42d900c942c25203030442202e2007039034044004c0c01c5000056031000990803000d05aa041041c08035050408480103540c442d203e00320503210100700035003403441c42e00241c1001d0b010ba84800049003d501d0814172 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 244889172 1250 244887922 244887943
    0x1060e0117070c201311040e1815070f030c020c1005040920030a0c03110c01050412050c0307030c050a06050f040b0a0b060a08130204050703020a11070e010308030a0204030c090504020102 82
    0x40040ba900e144d001141500c0303102c2000b00051540c8500400c0940c08070801c82d801000000d02218141c1407202c04990401041c0050341101c5c441d000c0741044926040c041c1c40c0c41603010b52107402c400a8114015000340c04c0c0c444540d01103024480310042260742d64110414000c180c0c3e61155266814080000215050300c0e20000c3d140d40000c42d00d0303007a2040c0c00100d0383e003e42c0981e004117050b0304001041d00075080c40644505a1140803812084030901540014850b6002c0d004040c25201e03000415151071040c2c0c0c803040102e030000c122120201c1d00a1403001c032801d104508441c0c0d40358a41e16460b0849600b9602442000e91b40001e1005200080381f0081c1c01200c00d203070030020030b00e08400281c2c2c688a803030307080c4007400340c51400140041860140c089940c0c1c0c0250050041e4a0408001070003580005000b80206d0414607042c0c0e040100000d642e07068030044041d9a100d40d085480d4040075400080c00354010b103400f04408000100042c00240c0100a8840041003d060600c000390400e4041c88 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 244890422 1250 244889172 244889213
    0x3030e030f030306130f020d050f100501020d0c0510050c0703170f0f0403030b0d06020d1a060703030506120d0507020405010e19020c01090203030712020d02060f01060e0117070c 78
    0x3005101d407400841100c0e0485000c9a400c170460b00361480800160207000d0384c6440051000c156030403040c1a5801052084200750300c1d06090b60b41c2c005081116000320700546006034800006100e10b00d000340300d0141d400e40601c0031a003448010050480c1920011a5480e041040100c0c0d41002c058008681015001540c1c41c40380c454640f010840000703a500404031414141101d000c01c1c00c5c5030007079200359420400540781c80c048581c1c030704100c130103940300d5001001000e10b007066080b1a0040c410a8000c10100240603a203003455941381203010f4030018209586c865189004038a404004002c4080000500e0302d500340c460f40075004000480c0d50580c461500c2d0805401040b4403100480c00030010f4503545c0c040140c4400289158a00401d500b58000790144800501c40d402d0103e41030820505607a40da08555071030981d9201281c40e10800c0e251a00c036000c0440060000a0140228948211061400c0011492000c0c100510350109460007004610509601805d00c200030701d811641c1245039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 244891672 1250 244890422 244890433
    0x3160c090c141804020d09060603020f04270309170f0d0903021f0306090f0b0a060c020306180c04061403010501050a0f0302060325051803060103170a120204060903030e03 75
    0x150140c0c61038070a501e0f145041051180d40c20380710ba6036503070641c3c01171580c4580070400401d031464058010010740c002070340300e94026180d00b141e030310b0540074552450000031990f0f650840c064408002c40d000401d000c03400d201e50072102140d141071050712403455814420007081b040c08101502418051030300d203207600b004440e0a0500140c0c40300020458040ea119181828003d4480340807402400355812400e0400d045c401c0d03546100807550092950004201c401c4e40403180d5920054460084200c00203415401c42c0780015030b8030541e001e201e24168014000d54410a504100090031619141c2000c0203441d0b03515442c3d580d0303060034464540074210075588103882e542804109261304c042c0d0700c40280b05250000014140c01c003041c0301100c1c014207040b01090301d01c82c4094040d00d15004203d01c008481c180a1503007007a46000603a0300c0c1202e0f00440c250070003490301d58000075554404401c502c02d2048050351101120010310003000180f03266614215060300318680101910615820144658400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 244892922 1250 244891672 244891697
    0xe09100e06060a170f12090307050301020313020904060605040c0507030807020606011220071113060513020307110703030e0109090207110603060310050a02210f150303160c090c 78
    0x50070660801d40b807402c007540340c2c0f000c98000d20601c0c0c000c02c045e8600680c080c4011240c00e991030708024040c2c0354030440c02d0398840f1713031108240749c200e0008990b42c60002c81410052405030415070343d51343c1c04c103005203c08607600383c48001003400e48a000e00c03a6000918006152400d055201c0b10346c64000800344054409810804002020758000c60b002440b07080c0d0781c10a88810380d41c40e80241c190340046000c0151501e4541c10031504841030b000c0701c5402411900010848129a07109000640300010041059003220a40e204000d410081c0520f050001c4400004a5868200f04800056202c0c2e900c0d0488036601a000524850040e8850003181d40140010400134400241c048440c03030003070f9241602c030740d00e80000905e083c0f94003004048440c68a800e1090a111a4005114586070010540551803142d01c070600200303411180e010714002e6030750200c0e400c0008186021741c0528014102ca0800c01d1409100f00b411902110480c3c480319840002c003c0c058490184851908141c240b40016180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 244894172 1250 244892922 244892929
    0x1e0903290c18090f04030f0915030506150309010c0f1704020f0a03080f03010f0605211008030d0204090c0203070b070c0206071203020706060801021e070206040e09100e0606 76
    0x98840c010411000c5114120360448910b9500940d07402030a154003820418695000100155000c1d40011a842c090003401809131280d01c4c11038441d01040401a802c0440450003030101820040d80080358040500621103602c02840c0078281140000480c000b2110780640010100040f0304c1c2801758103600071180e0702000040507841501500c54405203074140d00014800f00035034000509941e80410300440d01c2500c0009141641d0582407514151900c64006907494002e2003201030402084414400303100c40c0b10305160390042c003090a01d041c265140c0d4a000c0c10b6400c40180c4030091603010508000a43d183d00400c4000611400034500d400c5903600c500340000402429182031180c14020b01e0115180c0c0805c5882440d001408004543c0560400501950110806071034550501c0e5000c920803030107200301c0d600c650848452109001c100e04580350350340c000b010144c0c0d0101c0103000000d900c00040e00c1051141803020f000c0c20b030036400440174078112805d60305403010507071003c2e041196070345 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 244895422 1250 244894172 244894253
    0x201110d0911060a05030f09071503021b0106080f15220f0b0106030501081e030912010609020304031716021e01150305060618060f040c1e0903 63
    0x100c40d50100700c0e11464181400c1c44030105501e60303005003000840c240e0351540b2001035800f07150350020b03162240d00c544030956521141d0780201c002c00900c000c44103a225009030b0092001c84400c01c07076890405c00c24940142100c61aa000765403640240780c003d80c0c1048180505425102c1c1c00704802d0a604005c0c0f18602502d5081c0d02e0f00d185a0716100456060000315001c81a602da40940c0340040c941c0c4845d40140030b03000a00c540d820702e01c0b1f00c0ca0504901855030008000c05503c048c0191305212080040006055010003158455583d40c2c1c000315002080d40001c40c8103a020381c995420b1b504000388075641c0f01400402200d400d90042d038480f0900c0c3e03404101c000404000711500701d00051042920343c0100048a007039040c0c240100000410040e010aa2a100740000c440d0441041c02c4460303008010306044810b15071100004500824501e403650200840d04424900071a182d1a1002e4507803100b05007081c000c008c00d40c003e074200100041c00504026400c01306108000b11001d1880340356602 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 244896672 1250 244895422 244895437
    0x50319050705040e1608071b17040905040b01060807051326060702010e0c010207030b04081b0d08100b190e0f04110c070501030527030d0c03021801020111 68
    0x140c03035601003903074644038400755400303400440224111800e00c114041c00108588188101045030300c070001d85441e000381d03003440c114a800d464940d00c1300e0860781c80110040364600b20042d40381c4c05000110b0031040034420140f260b41308640c005e03a95414000080d240410080440e82041001c018501d00c21506020b078800300d80255102d084141c42c12118401d640407130b00000002403140008022030103030305400c802c01d914141426aa52182c000b801240c5421481c0805001102c4000204000510410007010706a095086109143c0d0300910981d04000328000c510f00020804024800e0031900007040d040186000d0303090518200071a80401a607000b0f8403504d2081c494100b140d45030a444030031078125a000e000f00700308441e004020321100a80c110340341d951268450b0220100d000d500902c0b90034000c1c0043d066101450000400b540300c080306521186049001c2840442d0540d0720703130301a1412101c807640740580c4804100c070000d204200306448d003a045a06240880381d20000c001c080b80d806 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 244897922 1250 244896672 244896721
    0x31b0f071a03060103180f20100804080d06030309060806032d100f0c0305090303010806040212031e070506250c020102070b070303050108070b0705061303020c090103030315060503 79
    0x10b0b955440300590003404000542a9103424440920041101c0ea40d01858030320b10941040c2d00001d030100307107604c504d80020300b01c0740c02c04200d50220000364000c848065110b0300c2000917901e8811080407640c252130340c1d46d0040f800700e600c94000b4840c054122003815840103080d0014410641c0b17000c03c0104c640000b91504514100701400c0c0744c064981031100200e00c2000d40b400f80b003051301c510446001014401e110b071000a242c100420709100000c400c9034121078141000f0800b0751603036020080c007840c4903030100c515440200684003100c0b083d80c0096410b0940e01440c541c80705450700f801070070300200510800d01c00841e42c00002d52250005600085442c240c03030000221421840142c0c0b908042c1d4000a40198001c11440101a8150049416228040285c900746075884d0f9004016000b690b0005025400500000d6810002001340b000340ca07000307104440c1c84400d0030f00403e90400003a001540004d403038003040000b298045031070034000c110616045155103070031150041e1198500e10b04040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 244899172 1250 244897922 244897927
    0x403080402120d0207080d140306090c160c030b06010323280204050f0a030503040302040b130e060f130323040512150c03150f0102010e031b0f071a 65
    0x6544504100b00c2010244a0846250310048200699101440d1155420504c5200010003846110311841320803580380000160454540001300980180000c1c940a260303c6c043c0030f940d01d0089248007040c0c0361790040a1400c03e660450400300e00d029001043e0724149810034030f07000381c095903501c5108840140300014402e50303111903014003400340759080400d031414410969171302c556800c0d50080080b18000c41e01c481402201c40c0c18466242c00c130f803001078925002408200094100760b0080c6d410500c1c0204104010b41107038024034110b488003071746524183d02c084104248817030000c408540044021100800a01440d50010419000ca00800d842400c02604c2400c3d20710983e4155009004010500c04002c40d41310041d03581c0d08541100d02003a8400000480c110310001421280140b8040e10601c00303501081040c0980c100340d285e1810b04640d40c401420304440018006050740a24540c041d44d4015070142c507003490001a10309044068009031020040c003d984003000d2071540d02c0c24100340c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 244900422 1250 244899172 244899181
    0xa020c0a06050402150408011a030106150809030405090f060a0e37050412020601090b010e040209150d09110616030c170a030207030809070302150f1c060824040308 72
    0x110018601580150038103401b013008101c1c0e42c01034226162801841c070b00b4203005c0594208140c26907400d44038881d00c85001e1288400a01e10401c51164040d032403070304481c5041d603544003007108828210b8009060001603001d2110341d1400065000003482545800342082c1080c41d0040004156482d010304c542d0a501e4050309410314400d1443c0d09001e9409040101c0c1c941428200204a24074004034010300401c00003044032401441040c4010b641030b0348000707914118a0502c8002c8d84a40d074420340c0081d95901102081040030002c2868542c1000081009946450300007005080c55089500c10b1006000301c08068441e081d205220036018980890240401d080c901040c5031851801502d11200098074104075405800400143c1d00c00c1e940d9603500d60725a58002e84404003808003d50002034642d00c50142c600c003030094102101e01c84241da140c0b000c1140c142c18a02c07408419802600d813208030410500e1414040c403204059460300c2600f4004540043c11800c100061005003407122460108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 244901672 1250 244900422 244900429
    0x1b081306090503040b0702210604082809060e011d190305030301060804210c170f22150507150e010216050c010e0607060b0607150209090a020c0a06050402 68
    0xa08150b0b004029207580da5181c0d4003000e02036000d61030907805802c12070782800c151034010020703102002290000d49040c2d110340c0e41d058126401a4a58541c851030f4014683d0180c0007090344a0b8883c0c101d46806030454508280641040006e01c3c5041c11700599000d401d640b5003542d00c02d5990504219840c0c80c0281c0003001340301b090314854002a00e14070011001050140c2c001209500481c010003400500400c09504c242d0740c400c2e0b60996100040034000792000141c4031101c11aa403000520410b405e00010410382030640d0010035620078540d02200c1d0041440100d0f298004c050008006507400c0080d0801c0d000e40359105044c0b0003008905414203960104481b503000082c135204810080d543e174030701c2d812200103010360640251380900400200024940c012a00c440b014a0f01514482c10151140ca030b03500103000040751035400c80c00800a1800096200200f018500c25445005844031581c0040c800a0f42000f8074900c0d02038410080a4004140080c445080951250001c5460f0340d40d880072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 244902922 1250 244901672 244901681
    0x1090302060901062328090506060c0c150d0c0903021806060a0e0d020406060c0204050703230901110412030905010905011202070203120408030702150a05030f040c08150603011b081306 81
    0x44041003042c20700300c50418680160b0340000c4031f4803070405010640711242008110b200c2e88a048005910021125205041026410031003468104616003082d0903202280b00346c0b182d0b0305908002a83c2140c05204510307044918054105030031000d80d655180c110003048451052641d604180051200d0909440d40c4072031102d02019800707803042c03003403c0e51440d01030003100c280d80d800c034461410b1400180c007040c480d228020880d101c529100c4480c4090121002e46820301a00074605552200048091390100030000c2c4004e0420701400305480c183c4e0704000b484e1141c0e90b00301604001c0a403108101070703a4086000640000d00482c0103030f44000130f1001070b1a02346815000c030803220001c00d00181040e4084098880710340203540300180b0b20344085d4500764621403480001c0106905101040511808020322030f44a486800d101c90341640300c1180030f16060012040b00b600c2205c42c810040c07a41401c2c012044014220700c022981d02548000150403004010b00c0c0d0304a0000c40800314060040c203401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 244904172 1250 244902922 244902949
    0x90c12060204180203070f02060c160c03081620360702011a0906180702030705010510030c05010c1a150604031103120c0706030906020903010c02010903020609010623 73
    0x41e69450f04009101c0c1401a40085a400011074000d040b00307a0702a0000c103032144261100802c203031401185c4030848440080a071415103e80d0504080440015001c20081001005a40030940d8600e25481c000d0103903c4044200002c0c0c0e88000760900c03d5849d0060030342018010500c9401e0359081c034000f4a5080b08a052100450203051414829440d8040d88420740b202d12010f0020030320010716090104811080e1642600807421034a20f4151200c131030001a0401c0161059920b0103000351500c07425600d0549800801d0056003500304104680b15a80c2070043c82c0c00e00f442200020300c0e44a1440c1e0300306880111203000449000243c11200441c0d101c2c0001c50000c140b16102c544038103141100300c403441c69031802407282d803030b1883c1c0042c03001003030b201000200c200410065080100c1140680201802151066000c2c0b1034010295400c1c040d000d010803241e8000142465a400c00030302e003060240450f07180b43d01d410170603c40d0380d482280c140508030401000f5241c200c0c0c03690114194481465 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 244905422 1250 244904172 244904189
    0x80c04050c07021009240e13230901200304111c05010e191e05010f06030f03080601030e0a030c0c050603090d09091503150b0303210a090c12060204 65
    0x3d8100490301c1e0020504002c1c0c40304001c1039062480b04240d1b135030121107000c8100d0f020078590241c00480c4d1404920045201c5403c40c0b0216540c007064046401201d441c08148880418003820403010b031809100da4040e08000306e00c0034090405080d140d01c25480060000b4000f809941d00f07850050300c80501400c0a101c101228117016007503410070038004c001c0304038040c00d14060011902513002e00d038a06004041d0708207009854400500c1e6100021a02c28482140c503035488070003036568001c803481000010350140c039100303804100901d0005d080342d000400d591305040c6460360f0500000d40000749044001d81c1360402e03280740d02080c18448a4901d03154080da0f404000013040040c80308000c00d4213a0f40c00079039102c0c1c0ca60035444481a074151412a010384810782460402000410f050408140040c00c008800140d9a01c87e803002c24119800f000003145190301d100764403104401c140c07622982c8220802e03400c010012450b034400014110f54400c603601900286440000c0c02070640c102da00038034946 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 244906672 1250 244905422 244905439
    0x210706090c140f0f0105040e091f060305101514030304030605160f08060907050d0b04090606080705011103030f06030f031201050a1e15030e0a080405040510080c04050c0702 76
    0x455048502c41407440000d40201c0300b49610442c0c0d42000c092130101310340e050311035508090800c45c0d04a11800b00411814040c0709450340c0c51007003804a4014400100c3d5007001284260070341c01c10034603001e0703c008048903030741ca803000b03091030002d00d03400743c5098803c003c000760078100380400081c0c5180180e0300050015481c040512026244120b00030703035080c0c0c50f80c40711102418004805c1d01c0baa942118500c5c0c0000b095000502068410700081c08800340518000801d1051803000c0b80481e03085440803a1820303a078400a20000307504016440c0140001d2038241603059a140703000785c5070b000c090101c084100203e0040744007070780c0511550700084200780c1180d4071040d82e0803083c68070303401c02c2c46402c0c042c01c8020004034a944412030344503007581c000c92440503414a0301c00030300301d4101100034000800da030b200c00002d0b02c01014065003e055028a41c40c58555043c030b0304000456070082d10a0f02d0280b4200307810030240703001080748100014210760025199035546a60091840703600402907000758130 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 244907922 1250 244906672 244906679
    0x61504020c0c03030429190804021c060f0b0301110706090503093312070f09170606040c110604170405100302030f0603210913060b0403060b03210706090c 68
    0x40d001110807110f024a8031100d45001c208001400348918401403d04038103084889104038000c230022500544060407045041d1180e041c00c0031a00122130003100c0203a1616054009041c0034020304444803402c800800140c400041c0c0c00000303104c1c1c0c020040900d503c40d4200028031100b8010b440702208023420441c00c000c20042505010041d071140c40082d06010814400682c2100055070042181e03a40102e000c0d450340e1070b081e80c241c0000c02c0c400e000c1009442c00801e9083c0001180c02c80d00d01203000401d180c0c1405410001074402d418880e00801c0390f45240c8505000c800200d5a4110f41c000340042d0329482c1c5003402604600c62a00301c2500200308203000080c0317503072507030045102e400d95610040a40e203c481c10141c031006100d0300140043c0001240361000741d5580014120514001d000d544c14400002c0f40310151030069120192822000c10300300280185801180440c8504401611003070081c0c0074010048110070004450480001c619041000307881d920140401d60040c5812a04030758 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 244909172 1250 244907922 244907939
    0x13060509100806010605030402010c0b0612300304020105190320071a0606040b0a0c0204050106030e0d030606121d07230406080316020a0f121202061504020c0c030304 73
    0x5491094820b83d110b020000074405104500380c900855059484203d600302c543c0790881000009071150f80d2001e0131610880c2c8240040141402010300e01f0380d000900c5006164a10704490704030b02e00450b0450400030840180c0c2d01004517421860f00302d079014400342810078200c00404810341d0b6449041000750800e104001a10054040c03075200d2034150862146242e04031901c2c11041d18140d820803414002400b620307010740b014000d1030b00303246490320100000783c001405844003a4051404295501400341d5064400e100075403001c01c0908007030120038a8890003c0109000d0740444c41100d680d20105d000a0007204208101403903007030120740042da110301d441e01e07480520740c2a0583c484004201010141014000c020454140c800998141814a07220300300d07042d0b0944049a03c52488400421401c044d862110003410a140d0f86550409032807034403101c180403419a8205540c80075003003061b00040c07010113404040c000e80d00561a2900031341d81914160410380c0b25a4940000b1174042400c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 244910422 1250 244909172 244909201
    0xd14150109051803090f060d02071e061112060d02010c140606101704020913020d050303060102010c030204050918030f0a05031906050303031b130b09010801140a0513060509 76
    0x1041d5403030244040c0f40d00088035075a104410041e60481d4003102c1080851801e81c0c068502e0b0b00c04e4640c050314001c442c2c0d50704641e0100740c01644208481c00c000c40c1086c400345102d080040c0719001c45a83c0740600b0360001f40c0d03000000402c1c0500c200c21510f001c004691080c18103000260740442075112201c0c650743d0741c94030792208540341c0b8018a401d5200c81034103840b8440c0c4407098003032403035403000d65241c030380a0080024000344002c0d40410b0300c416200040c0c0314801202c205a000e040655203a007042d100081c2551100010407040600500c402c0c081a84d4040402d50006035095003880c1c002100401c00c0d06501030b10380c0321304d03000901240c2c414109070800c008610913002043c140905c41c1c696116442151064002e00d0b805603c24000500400020b00b0503100c4e000b000c091070740c241800c00c0c0c2c01c80340740040b0380c001c200c00030b0012501d5052940c000458a000d08490021000d082079403202282ca0a1598490148900c404060300c4c9481c0c84154403280262002902140d840e1400614185011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 244911672 1250 244910422 244910431
    0x7081602060f1207091203270605030a0c08040b06121e070501090f1401110307020a06030603020f121f090f1211030a0503150f130b0406050904020d1415010905 70
    0x803c40070000680d001c3c070a440c0314058884101440c800c0710032940b000c03280010044d407000340d000c942d215100d50900b00e007080440181001c0e03695070307528a410b040040035510010904e809020300700e0140000255106507090380507100b038940c2040000c403c12079514083c101842600d0a0301ca039004c04221403404103800007038803001e88a039080240c0d5140c401000301c0503407041c20300700d62249105000541c440c4c5100640300941200b200c2c10012190000b41c014100781e400b14011980e036034020411400c1c24000000d140c071040321803c030040901890070352183c2100d40400e1011040d403495602c0c0c2c0300998848001140c111001c440d40e0b4441c0e00d01304490b44404000c1c1400305000b0007218805031030000440e203180c40117a81c0c840c15500c0390900030008030301c1040d05030b5009519a80145154803416004d81415180b4040441c01d040c8660078802102c07001d4108a0252410004001c090388801139800315666014000300c00401c501e40b912801c00c058910a201102600000040d42c0c2d00f41d9000113000d07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 244912922 1250 244911672 244911697
    0x3250c03080301172808040803030703060e0c0703080403030b0109081006060809070303091401091d1f2702041d07021606081807090e030403140606010507081602060f 73
    0x800c4d0b4481c0300c3da99030348203101c0d010701da46044076045081c1e2203884a50a103020710a28042d4201070f2100249030854000b01c5010000036038480d410040b000c0400700c419049000a03094034504239168170002c0ca0141300030000b40c149038940082c00700591045219100a01c00501a51020000c02c0f01c280007500b161700c141030010f120980803600850000c81c40a044070b9050b00c56003010351600d124160010070100c8518148601e015000504852800b170742d400450004110f50000c2c0740c50414400d080c08840380d9100000381c0396400b40402d00481a070b2034084030700404071389054101b00442001902c0f40760420f12401162401c010b10302102500340a01a030fa0a0f000c2e02e900802c8020004410130140c072541c8c1c0084c43e40b4001c03400740759880300c0d0481100150015200c545031150241340c1520311401424095500c0054100180054072855400800014024103514140740000034003a014607200034007842000129031643c082c11015504125602600c000e403625958100545240c1050303104450 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 244914172 1250 244912922 244912949
    0xe180c130b040f0b09060a0804060f02030108062502070506031302150703030f05040b070e0d0615060908060106080117031306091509032a05060f030702100b0303250c03080301 77
    0x38110a284207841710080041c09040c00c00e500000215038001c40075005444455403015030007408241030000b18003800c04280105014144008401641c14140700e02902c0d1651054a610159601160074421101c0480f02c85440341c9401c40f144947c0072030784c440250701000c280e400320707401e4000d2005045100e009450420900e0b44204102d420780d102124001c00380909180051940c500806901c1019903001d03001840c429841d40e0f503034046491094074440f241d07030000d4007008210350101820f8042c112030300103400035514026024107030201c18000d91002d030b0010a181019200c007081641c1c1692040180c0d21699542e5610140050009008111100501c9641540064001c0d05403900f00e03507200c0c00201e2084e404640c2003807085010140000e00c1e0007202c000045a5881c13001800c01405440c401c1c654900340890003078038046040815002c0c06051514460490760044103803811803500c1c02d4018a410b16801030002d240c6e8a82c0c1d0000c01141d082c2c6004000d006003400a0350507214060342c402c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 244915422 1250 244914172 244914179
    0xc01080c091309141605040e0102040e041112070e01240c0615030b040602090103050702120304030f12020a0c021905130e0f0d080702010b010e180c130b040f 69
    0x440500c1000348141e04408505948440c0d0081c42d807104070218040c0c55201e070740c4c2401e0100c03207081110741240c3e1602038445c5035061050b840e02e84122409000c2101c000c5280c0341c60171003075001817000180050300403050f805602d01962980d44a015031f03110301c4821b4407001910303003000e0010700200380180d000c01d44500d0145103800700d4141043c01d518050307465007861036400b5552440500780c11400718041c02034522000001604060701c060189100d820b0158407807034244001001c42c0d800130980e90456112218001000c40c2d001e040740e400640503e400000c11048040c10340f120809034480d0441d007880090b80f20506503022200480da9032088034081c1c003003a022080305802d07450600072079a0240410860040c0f81180354400c0ca641c140134000d69040e00c00520080b81003071001844840030038650300400c65030550a10507000454002d0070f20081882d400404246000a010010400d03000208007082d1000303130750019180340e800c40d18032842c0499180c101400240d082480746900d854100784020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 244916672 1250 244915422 244915441
    0x3050d0212121501050c10022503051c092a06090501091202040b030a0b101a091309120309050f07031e06061e05030c0d020a060f050903060103050c0108 67
    0x884450301c0030b11250740341d91280c98001490ba0018901d4906000c0300700800008290180003580311982c3d01000141c585907190404440c400900c900e84464004003101040083c0e0020255010200010401e02170916111481c0d001440f080c24050b01c014040032421b0132103000e00316082c10450249103085003090b82c0300c0003601c12040501406000c249560010700032030a40443c69080b084c0001c00c0401c2c50b640c160003080c2000c20b10b440554440034a0010000003d40101061008203004c4402e0740b420481c0c00c0001809010f200181407240382c1e00c0c299494030074034680003980c0c1d01e6000040568595034440d8098000c1295080c11a000d00945040346050880400d010046981003000400013204500b5441c1158110f130000b120082d5031002c2c0491485500c07480301e61010300c004404090b40b420701040514040180c05014405c00790644070900585510780706100b11201400c00088a8170030304e60036a6140034401289d41c042c4074520000044c0000000c405c48c1e00042078951011a8440e450030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 244917922 1250 244916672 244916677
    0xe19050d030510051201091a010f0b03010302030d0e03150f150102150406020309030f0d0204061d0f0603130f080a17010f0e0c040315050406050c070b1b0f0403050d0212 74
    0x150503d20307100d04400c1010707040c003d03c0304d20a003140c00000100010b84e030f501e000704441880140c24560159100510030120ba02c5050000340c810000c8640c2507600d103500081d40c5441d02d90071442040307019105039105840802240116980507070454003140351900840d400604201d030100c59114990b0300040c00d65001044030143e03c00040e18801c00c55440352140d5001c0c1d44082c01005951004001c2d101841500e103024202e9183d81d00000f50341d892400c0c0005003d200a0115840c4411503503003003c41d41d86e0381c1050991100b50980d04541c807030355408041c071100b00310500042c204000002c2c1e40d00820801200802480032152a0009412110805460056000d00603400001105c0300144034414510b801c4580c4421106442d078038081d22030b80c983c20385071500400c1d600c855071540180401c2001030700600b540311400c2c4441d18201099034039502d00303911002c0d190301c24070070345c8804010591500c9800c8500000c0b110005903502c50781d0b807901c1a81c82150250840060044040d00d1141c032096004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 244919172 1250 244917922 244917931
    0x1b12020609040e1509030712030e030304030e03210910020105010e221a090601091802120106030b190c0c020604090506011e170115020d120e19050d0305 67
    0x16503810a03001c00c0900c0020103d503644080c080c41040d032000d103414015504103215004440107141c9400381c503c0c0500028000076407010030315003820200d1258920000c00e41e030707120740c0600d4030a0196846102107410700500401d80100111400c022102d034841003c01031200f01000e95502d034449514200c00ca0881c5c00c00e004441b842103c1d04081441c8125034451100320b0f41400ba00110512100da5a5103c05441e01140084402a034000c10038196000d1040e5030040c1a0380030203200244514000d40d00c5d545804500030311424074403101000c100000d6020308082c690080c0b268240742000c03640b5558000003617000d500687c0c282122002118440d00c0713071302201c0340d01810080c281410b00c0d5142000c1d00000709442d040280c050608004085907101c04200e40c40c01ea1180e84042c1d00340701703184503001c3d0705802c0382000740120560414199030010750100003886615010a813601002400005810401c01000032842040d10800000d01440c0c03440c0710040c810007c5079110200a60180c003500d10498 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 244920422 1250 244919172 244919179
    0x5030607050322060b0f0a030309050103020d0e0d0c050715090504020304030201020c010504110315040c030311030408010603080a17151003110c06070905090c0429071b1202 76
    0x314500038022409550030241d8034000000300d00b10419410440e0a1014060754801d40318401c3c1d040e1410990f40f0044801c0c000d603008000350b070650703d0142038540584941c6040503400a000418405a680308038903074036544d8190344510b0035250b0700500c0c51007034aa003541c1a014001000548600604504800320566110032108514082c00c100003034200500950940d50208a00a003051382803107424461881400da2401d074004450502d80b904030300070350500403040104180800b040c040b56965003140c0c5e0514160700b1501d20b001089003580140e91010f0034543c20070034007104024005004e02101b008039a00c86c2ca003205082c40104d5140c0c025034800b440d0045008035003d1905201d56002d03503688442c04c005c180040d03091003010460707024142d981c440750040750a1001c402c1c2e121040f030303004000445035039990307080045c16110745114034030031422484001c01c0410301804001c80c801e10500c200a80894654545090980316020080304201414004000201e9400c5424411600740364024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 244921672 1250 244920422 244920433
    0x240e07020a150e06180d020c09060603040212120c0c010305060d1106130e0a0c050703020615010c06060303031e02041505070804090c05040e06040912081003140109020111070503 78
    0x1c0c1c4514102c07118098182d01c40c10b80741c12916202e54410480f690283d044600807007280f00003d170030b850500e1601031560086401503421440c00742e50b02c07500d09030088803c0701c24503929240c0d4400128800c802140d04006802085907911920380400085e00070440e9140645500c2851003004608907202220400e600a0844218074081a43c804000e0800c081c00380c69180303000c082c00c0720106000c0f10f40e48100e0094500404010300400b4902a0b4190508103040c40b905010403998013035111407000342101118491030500000980c0f15112900610790490802c118064403410010003510a40c83e15080c1c102c01d13a80d50500d44041407085904884a00106184a285000e4211042c2d440800c040d17a00710341c144400b00d6507000a1044030303e0300041d6126a42e1303452509035400b186100041400e07120b01e03e40b0f240200440d124107000011440d00d85000029640d50390f04c80844001c5640000d03101083c0100c40c040c0d01c00d8150b03c107c4088bc000d03241d0b01035100d4442c03400c60392042c42c6c0c05a41c2d01600030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 244922922 1250 244921672 244921693
    0xa0605011406070609031205010f080106050402070c0b07051c0801090e0601150f02010b060d06050117061003020d1b08090708060c04051002030f071212020903060115090504240e0702 80
    0x41c0e8811405c0c40c1c0b01c1c1c90100512041d1000b0369007601c1083e0040d0a9942c1c4410041210140c240710705001031a0a5400394288000e603181c01d80c0e4901e0a00ca5461a0600055036004110b42032000042c181c0380c110700882140050310009080100c240103078844130f4901004101d03100800200300b0704950182f0f2680c00401006c000884000e2002041402559250004414940c2d16000a0001c10707504003000039905143c4800145610a03c90454400e80300c04424030001e5254450145210043c2d814050390318208114601c00030404100b13010044002503007140e105036403105055003d0401e00c030880d01041d0b121807805840700d43c25038510303c1818080004012034107000c0310004030b10340d450054900300154000450f8481e40302d110304660000303080c1e1341c2c40082c0760001c807410b4a080c0000000c500300340c0f0200c04a81c2da6407040c018059040741000380e00e00c042e0f101c2c0d40c50202800c8098004d02c0b41d01d244440009000d40810040500c0b04141c4601240100803001c4a0f07100f0382a07a401030450303440303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 244924172 1250 244922922 244922933
    0x140601051801030c0c020d0f030e0d1a060a03021201050103030206160e0418082101060c03121a04020f030103060b010c020108130f0803010b0c0d0905030c1908060106020a060501140607 81
    0x84e40c3c441100b0700c981c220310030340540d0ba4400b4060b0882d02400b4100740c0c00441e0310740180718428621417588549901981400494074000103480c00040b10002c4c41920386512000403002102a44001e42c460144040100d1640043d040306040301c0c481c2c2c0844515846480030f10380c01c0c005000c3c600300001c58001c0000010704d42904090340361031504043c1d82e2503400c1e0f82c50b405480d620140e00003507407038240550b4044d452881c0e030b5201d00400061401c081c00092070380c0d008000c0d4040116102d03c8a8072031400c4200b03802108079030703011814001e20855950300f080111940c941c10912081c0c80315450300c042d07004194000c0d02c0c0c106150b68165555450707a40d802102c5062441807a42c10342750038084040074400158040c0045028002d8030b8401502e604848103158a0709418480240820034141d03000c214540b00014402c1145008444001419001030010001c2c4100c1c0c6e4010700b001d00c01c0380000551380e40c0100d44200c0c040e0080f00240704980c0c81d214215100130045641940110042051601203007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 244925422 1250 244924172 244924181
    0x1050607080706020705010c110d090f14010e0a1205010f14070c030e0310050f06030d020d0e060d0501030602030f0c07030801030b060f04050903040504060e01050a031202030f040914060105180103 86
    0x62040f00300606284107134890720308440c10812880c02107009050b5203000310104204c8075480b03c6180c50001c0c0e58034180030205028402c940301e40035070b01200c00c000311847e81c003882c80342c041102e0151180818554894840c0c4004c603c250098446520f08002103440001600510803a44024400100f4a840e80071080f105507208810660030401d001861078040d54040c400311114600943c00420141800c04020320601006802c0501c2076108040d800282e0340c010948103045000b83c01c214020760701500c00b1840511500d61041320319441c003000482000f00b04c2d030103140515032811149040c0c3d52408500c03042c50ac201c040180c04203011000400000e103105080d5030340400042c005505414080340460f00343c41c0142e4125415070008101801541450721908004050342520b1180d203504d4800414800501400003610100c00d003102c0c1c980f014003c00450705005006200b41c1c0c1e480343c2c0d0344020801801340c00c030700103000c40160021842c9076100360241c030078030740f9010010186035141740019070040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 244926672 1250 244925422 244925437
    0x30106110f120702271909031d0f060c010518070e0604180203010207052107110d02030312150a060305070503070309150c120605090405060a0c05120c0706140105060708 74
    0x10703120300b04040401c8117090ba2a07458001c2260340c03200c2c2c0d04104c914070714840301903881249060b1508040c00046903010754201c1c10303840c40d0f107030f803ea00580070004262085001000c0f2908142d002403440005441584428842c0c40a000c2640300d003210090702c207444139240e2080204005130100850b0081c5070a40c0801d0700c2d031040050040c2c80006560104e42a0b0f0094002a180380d00400c0e022586458810701e002e4000c40107070000d82c5000ca180c0c0c0d86070311106844e0707902070090149002510442d10b00700200c07403021144c8500710f03c1518107070b0540c901c2c480350f92a0440c0074040015000035618040d014090159540c0c0d1503090841d86c41074002c0f0002c3c8080b00042c0d031803003003121020b41040540d2041200d8036005542d01c1c40c40081080c41142075070102d901040c001d422401c2004007003403000c9000703600b00481180c0031a01c0c1c0d454103401c80d110302a800803440c89803125810b0052814001c1e0040142c80c0c0702e00001d005070204101d000942100c244641070b0031410070412000021500e60041018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 244927922 1250 244926672 244926679
    0x1200406031107021018050405010f09050928050d090b18151c0e19020603090703290f0606160f0803010906180c020a110103140c030106110f120702 65
    0x242560f54000608000303441683c000894208403c401d860061580c05001410702550240040c0d4075007000031038203010520516040c1c0c0d5885021404108051040d2140e1001448101044034003103400c105046404180440c1d031132003140800944c00740078061010480f40502840750074901c60300f0442182100c0407410703503400165030b00c15000a81014000c1d0904c0c809080b001034041303581d40726250481321380113400a0b0b6988869049940610000310350030916034161104c17a240d407141c2d2501441e050b201c2d00024004290070310881d03000301d0b06481e0b2941d400c101107107150780754440850441198800751034082e0858020003c0c00340e201e0030019929a01c40c40b41c03001280305001c0e074030340340260f810a8200000d8152210782c10801400704c8680101c003507200800802c960f40450001075551268400010402003240302e004881d0ba001c4d0b4414040030314105401c1d15503103480503e10b80b01e54005d000f0325001c1441c000448600034400140101c641c09202e0040c16408010700916000d0b404c021002c0381e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 244929172 1250 244927922 244927927
    0x1030e031603030c120b030706210f020a0e061204110a1d090106080d0e0d0807060504060c0908070602030409090602040f0f090b060918060f10050c012004060311 71
    0x2403036240c0a015034020b40240d41c0010002e80a14004140d4020200c03040812810080203110301d5501055201c210746250034521204440700484074801489100c00d40700d100d2800820b01c5c900300da25001890320080356590b11450a000ca02007001c240611ba00854400e01c0b400c0005000800400d080524440c0052a03140c0301d86d50740c51422a42582c582401d8012503040d018014610024021103025122001c05800030741c482a1006000c040302c1000c0e54032400c05100440240404001103d503c2c0b9000b4000748032500d81410003801501f0141c1c0d84ac80003449103c80014582400700d1044155038655000c0d501c0c0c280351000301000342c070a42c03105542c0f00da420080026458441140b1034020304180310814081460000d4490442d1901886c02d0302032913040228a0265a69080030808204890159580d80c0c03169804625100340c2040201c0d000300440003035440035500704002d001300a198800038408100c40740150704105260744903c844019040c4010b02c0f000c2d019400031401c1400c50350600c1d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 244930422 1250 244929172 244929187
    0xa0807020c04060602010b03151b090109050a0803031008030a090302090a0b04060f080f1c030213030b0c040e010b16120c05071d07020f0c060a050913140a1a01030e03 73
    0x40843d52035910450240c1c4d554070801c0910308040c8031030b506c407078044190004035242046490810140c00c2411160b40c5000060f070001603270250015031301502c006418101801d031a907101a03030340e502c191540d5181c03c052140005d03206c54000101c4403d0700c0c081d80c400b0812840d41c1d09200315401c01070710900f0500c0d15003502c001c254440d403046600900c0c45489080d44a45002e000e503040020283c0c1800f840d030001c2112a1100200561035148200d00e45001a91030301e680095001d070500a0b040107115030140400e00c440c800303c0d2806001542d0840616100d646d0381d07494110031512603444902401040c9074030380c1000c03440724019082400020b090403446418180d9545040418a4100d00b40042ca40003220088424080d4490f42c0000203000602410b9228200d1680e034214003c000c2c1c0c810309000402e00e841905c00c4054418032070002d80701000d91907c004240c00600121000301e80404a0075000850500250003514950130040b0340608040541400440280c8010030f90001c4a200800802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 244931672 1250 244930422 244930429
    0x30f051e030c040303181410031b0201021b030c070b2805032d06090a140c222d150206101203080f0702010e0f0c040c03050405030a0807020c 62
    0x210301c140c54100d1000c0da65419803038050512171548001d00261680d1b40410301100d41541d41000f0034032800c0f40c0844800c1e904401c110b0241a85c0300780307036034440c2070100701c840b103039805401600c841483c410091104010100d0070701e0340c80c02016010803042d0f200c43c0d0308124981c2114010030710f1400071f1601002c0303800b1500b285c98200c140620043d0000d41c000040007001c0c0007052011070b07103407421101110541c040c110030243c550009003025104403071510200d03035500b400380d000380c608110300e8006005602e811a961880f1742c00900c07420490081c15009010f030300039000c68200981e242070071030888890301545d10f40041d1401d81c0b140c5003400661000803d1800300f01c2401d03100d2020701d900800c400c2c50503400305440c4114a911001d4400000207008000036080194254883c4007103e00044666549404a004d40000d040500b000e000c2c00c0146806040d0114144000400603942803050344460001141162000c4902030010f030414030880d01c5c041d110b4582103801148501c102c4900040301c0001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 244932922 1250 244931672 244931677
    0x402010f1106130503091203040608130302030714010e010e0609010f0b241201091508030316230c1005060f010e0105070201030b090a0f0e0606060702010f050c0d0503060906030703030f051e 83
    0x241f240b103078408182040410b51201c5e2459000b8804030100b8826070456401a58078015000d0051803010b4502000011503400d502c010703040302707019009000f032820310310746d00d038640380d050303820510550030054a28604041401500412000a04416080c0c04090001c5c1e2200682c01c464080064040140420281202968901a043d2890300040c010002000040b1500c1268050012a0001e004005086041c11212460520607003410603010111001590300d50031603642003024000f0120701038011000004071181c030381106840800039a2618801c20074500c548040c2d840c0081d5461800003400c3d4401c1c00075121140c4181000b2405802c40000102410300484121003c1c903940d06422800904901588100c01034000150406003080c0001c034490340301e02d407000b0741404801102c0400c42c0340b26604442c101102c940a41e0850f03013102c40d00521540c419103e0610843c000030100320146070204080045a6040d11801420540d07554250385a421280e071050240c2c2c1900901c02d0900d038803400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 244934172 1250 244932922 244932949
    0x203060103021c390506090d0503070203060a0c12110406050a020c030607030b0f1525080c06010317030618130c0f0e070c0f26120402010f110613050309 67
    0x20700c000101c480345144e00300040d420300c241021180c3c0c840e00308010344500044030038400083d543e04510400c40d050041c41c41c8102c1d07034003c0d05445034038204800e506241e882a44a21451303a2030969005088544c030301992500e03c0d10f65030781300040104125160160004085400786401507a40c01e0f078a50000074242142140c0c1c0f9808607031550700518141c50b000003185894441142c00e60341c5940880da42c100540103181c04000d08460b001410810700c141c0c9c0d22105d601652000e4420740e5040e900b461180c80d802c2c280300c01c45000103401e403610905802c440580744550809415000711040c8140e00c42d0515201030041c001800d0010700040100d90f4110100000c1c00324603010858a40c600108828545001000d9804001e4825481c2c00003e070480014800c4a412103400000e41d84200795901c91907130a06810707860f801d000a40c0c00040c08040c9d00d0f081c13046000f601d46c0d0108a41c99a42914000400e000c01101500202c1c001072805140206c07580907107018408032801c0913070351408614403074038012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 244935422 1250 244934172 244934213
    0xc061d030a1109100e0103120c0507290f09101404080a050708010501030807030c051e010c020c010519110c060f18010e0d03052206030c020c0d0203060103021c 70
    0x2c4089640e400c0c107034a055041200341d101011302078600b103c041c91100c0103020042c10440c040b01c800c20201d1140e81403164107a08a4296141c07142ea8010300c03044181ea414203900344c1c45a00b10f00700a0041d045081e180d41d503900c048214503005480d01000301d61403419920718103100601501001180701e08001d030000e42011401040c1040702410400d192000640c0134808070380c10100188006640d06040c0c0f0320182d85401d0035900f03c1ca95140280c10b29200e0b8400702c4040c02003240e0b001d21000150800e00303142e135094007903401840080c001104c00e84540c507035108550503400318400344a84610b50014039005c806050310045880540000c10030b42c41030f041c00409001c0400c1c0320062180350b424206801009003403811540d080312010498a10b8034500c0031342407100100d240343d103020441c014984241c95000d0802030035501c500001c2d000b0b00100c0070190042c40343d80c03c1a040c50400700d1000c18990b4005004090030380c65582040f03805018060352680080700d001802c00020b141d060381550341e0802c107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 244936672 1250 244935422 244935443
    0x301060e1501030501090b06190e15040905090111030112080c0a05010b09130c09022208030d11090d1103030f070c0311030109150e070b0d021b0304030c061d030a 71
    0x4a0004050b2441a0000c26001d1f240051144169a4040850702c0d4030160784c4040401d8214100c054408480507002c0035004455260225541c0c0802d07c0100242c0d1042c0070100001e13114030b4070003070880c0d049096040d1034401c1000103000c040000d0040b00080345c07094926500c1c1659035601235042c07402101080354607039120126000c1c2c0c1d18101d400c203a40001ca004100d0f01112107501d0712964004103100d101d201c0d507070015081c4120460400da10068403107204c4101601035036211220382d00d6109106048541d0303e4003071031414803170301c510882c2d445043c010007102d001d40b01340e01e5281820350072108083d894481089003800c026250b1028008071400f403c0000e10f4948ac6043c03809020383c040e003005109900d4510604002100c581c05801440b24003100000c01030484142a45441a03c0d0000114110b02091181c600043d507001001051018031020800031a40e03e94a076a0780610b01004042c1081c0200600042d4800d200e402c5118418400010308041000c02190405042941c1600c0d01e0801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 244937922 1250 244936672 244936711
    0x30705100501050a0e07120c111f0c1103040504050a14090706120b090f101703180109030f08070303141302100503010620121303050c04021204110301060e 68
    0x851390300000c0039102d08200891070304090040c81c118100c809506d40ba03980385140002c443c442c000c410300344070b417100480d000010301a0081d150350124041207400c04c0c5c2007030044000d00f8420600d19641682820040d8106424007007000041c20000f0510341031156218a861100c02184c080140145d01d0b05000e004000d0400306d00078078801040130311610b42824100b0864082e1140220250b000700c54010a170b02c00e445558030020204030b04e501c103116482d000c2102000c0c10b007010004111413600d4403e00241418240015222545e291001030f20903031890707030317201d000c40d0090700204512446460000f6001100c0c40d0111402081500d5510f83c1348880d0704480118240b211641d41c00f14130301d0405605541c50302100030040c9690255100c2c2601c41d40c0340e04c070002ca600300001b00c1c036590410046a200e00c2107802c1c07003c20010512040e03401e40714940c6101c07d10308052007120100e24100040d0347c41a40c0c0c5448800c4159132142c1441d0b015962030600007507281011454a0041d07040c0802c20411700d59 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 244939172 1250 244937922 244937929
    0x5040516120c0506180d06060b03090d3c05070206071a0a051005120f0f0a0b010603060b0f09130606020105061914010c0f0c08070e180d1103070510050105 68
    0x320760803041c0140e81c20450b10150b17504011400c1c0c00030000300c07801c00d205490303458014003800c15988002903aa10100030f00c104550045006011a01d49565540054404220341110b01071080040d4291008884402d0101d207880120124400c1590810350f24201c241e1707020420a0f40728000507540c0000d00745401a03402e580401c29908060040024012414600e4005651a407a03103d200c2c459100c4100080a4034402e018102001d8032110550300000481441c51b03480e2404804110b404551220002c82c42d503000e403040406a480240c1c1c06800c20111041c41d0000750712208005a1180c1240007414a100c22402001d001e0500c1d41d002041a040c0f403000e100125150480116010354150010310800e804501c0e4114041400d1820090054050404d002c6480e800c281c06050600340b8603000c40c01490024040c02142c8000300c0d41c84907a61481201480c1c420200c02491468201034103801545115644a0300d00e207070303140d0030350b07141040300e42e20107189ca481e0702d10080f800b07034480d07004206528 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 244940422 1250 244939172 244939193
    0x3050c0910201c030b031c09030803010906050f03030c0304050d03120f15050406030b0a050402011b0506090c0d110d14030a0315060306060203040306091a0708040c050301110d0504051612 82
    0x7000d003001e00c030309150317a80029260005e404d40d00c0d660601c20000c0030700d51072242803010f0045801403100c56881d6150401400504080d010322401642c03540340e080303c00d080000c11200340c05080405103041904180408c0540b418020303044d010412420350031f17025a07502d482050030140e0b965000240000c92054a8248030b402580114452850a00200081158100f0f103030343c043c2d50804001b034a9690781c80180e80ba00080040c46004586043c00001000350000e15180941c0f0070504440d40c904016041000c04200070070000c084200c0c0084012890601c8141107040c41d21a462510884080b400107030b1035500109200c1e40000e44864040c9030b007114158044000d0300842c501840901c0c28018003941d284a5480f000f08003c0c2d54607101401d02c031480050300d107180200000d101c05414005001030818005a900360703a09400803000081a190512800510b816a141540d0a214802c0c080f20003c0c40c00401c15242c1e400b030b2042034280da0407140f1a0601a00110245454890107810042d42c0b18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 244941672 1250 244940422 244940473
    0x3302030402010206100503030d180f03020d020c0a0b0f18031b090105060403030206010b030a020409020301090501170109021005090a03060e0d020708010b0105030402130f1401090c03050c091020 85
    0x3005100003401552002300464a042940300300104030510300c00910101c2011134840a004051044034a02c1015404a800d96000820b035084549005110701000f015041f03d10030a483d08a041090042102000340036080e0368031481400e1100c1c00400002ca801d004503002050110078210f500d4160614017891014050582601c1d95030030b140c150f039006035803a0018001c80701400c2000c00001c1e101030b01e0380c0490300500740c80e200554030303941d4445034240603040038003501406212406259032402414841c0741c410319001006500d00c11070091003900c01d80e000c594101c2d00310f50364150120102c2ca0900481003145905401410344044c01c100c000d0801401c0c0d00880300ca0703418403500f9801d5a82c4032056a80184d011601945e201c1740110a10008000b50405002d00509003154040840f01c0072000c036040b03440804061001c008541d2044044402c00c58103c4080b00e0180310750304450901d60300b4009924014202400c20703c000f000144202e8020000d02c80440c0e0140207201c194940d828450141c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 244942922 1250 244941672 244941691
    0x15090c0307080a0b0f040503130902041a0a0915030b04020304050609010c09031101140d140118020a141303021c0302011508031b030d0c03091a010e043302030402010206 74
    0x725070301d543c03031a096482c00317401d00300c3c0d04d2040700c04541803000900469048051605940d4020756403a200040a0342040c0301d581c00c6040e0322401ca0708001c0746041180c20000f080d40d100341019040c116032543ca03078105c0b20210205036880c0c00c00e80c00340e265440118003490040004040f945814503c603070944480c24910360400c400b4610400000d103071038034110066502401c01100c8440f40400790107640c040c080700b02800d00c1c241074600495101800c0b10906840500480c10616400c5440c4401a4812462004001509030007503400040c000b901400055590042130f861007903903900000d28140700141d000c1c2c629076007180d03c44101902445190591002d500b040403803907183c016407075184d02038201036074800786e889600941e400030280300701c1d034281c108800308000300342d42110001e00500d21100122002065860150185181511514101c91541030070040c2e96039240e81303407588500460999480e0a1820048440b030540c0c8582c56200d407605c21100507224505400028600300019186010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 244944172 1250 244942922 244942933
    0x5070920030118090f0b040201090b03011404020d06080303040b0f0a0c0c02041d07060c031205251e030f1d0d050a0e030303101e0b0a030c0215090c030708 68
    0x80180c2010a4030304440100500f0b452140312038081c600030345501c0f44024000c8255203403000030040900309160085000780c1c0c406545507111100190107100a0080c20803e003100c5900c078506107490340040600c14080039000c1040355079074204a2840d04103580c04c5606030300c10f40400c0000100c28803041d41c440501003061000680c411400b808001101d00041c3c040c588502080c40b060703212403210142d00203110100c0e0003d030390380c080007003071100381c854114000f0758215100300848040d401090b01030031140f40510322821620850040c414080c02c250814011502e40c0d40c061102080e25815416080d0b48000c00c907464100310711006c44030b01103038041c0415005008103410303000000d04071646640a082c41544c03007140e500d003a2aa2141c0010711540b501c000030800081c03001001841c01160052100c0810b111b02c00c140b45550a0a94001c900c40404103008000d12030f0710980000c1400e00a40c010348504610100c3d0300e45114800301c501001c1c65101009880a605082203180014507546001d0503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 244945422 1250 244944172 244944221
    0x50a08070e0f090402040920040b06090a060e0d08121501020a030f030e0f010207050a0605010e0106080c0a03061502070e070203070b010513110d050402030111040605120a0e0307050709 81
    0x10500b58612401c41d00800c0d250740040c0c00c5440f181c1c4800030f080d41000b00280c828040308924280386a00840c2c9078002d5003410300001d802d082c0031007500d0300c90600404140103241400390899102800460060384059080700c1203002ca00c21304024149142c5501000c4400c0c900400110840302c0072080041c11035002191000121354400c064010a1140340744c00f25a101c40080847d01c0c2061115414609502c00201501081400580b106e0528460402401710faa41e541e042e0320b40b0700702403140b0004110f00c40005400089480b0003005c5040c1907080c0020000c4d01c8151070080180034000e000e01692001c80b0031322900004034446580600d981c40110b103030102a40d41c0c3c9128000600c203550044500c03104028140c24290441c192040ca0b000b215030f15030803000d040b24007070141950164003a5180c6140460310001c2c450496007901c0305600ca0900d030450610011060380d50040500700300c07559450b0030103140d030420f00003010701500034801040c0c01424009031800715030740a842d4140305255130038500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 244946672 1250 244945422 244945429
    0x30e0613080705121b0609100e0f0306040503041512061205100204050a0506070512030c040311010503040b190b300106060c0201080430170906060f030708010507050a08070e 76
    0x3013903103416103210f100501d03080d070000c079446c0c0c0100040030381e02a04004228169030360051310554050000c540101400551200340342e12840282c4024100e60070801050140c15401010400e401c10703d49040000e841d6509161011107489400c0000c030194886e0481040c02000c12001d0301e110070340710003107151030310b420000f40c4814501c0c03040030b0042c60003180081c00d001c02030242e0b02c00520300041050381ca15011460207181c0d401400100c6a841c4070400230892540300308142d0344250fa004030304810b240c07141403518041284c0c0c65140d804c5145c0b1812201015210b1080c00c1801044000d40c2c403004c4000c128090340032080660120741c041c2c0c5001d404101c4258480d002060081c0c082c249850103071100d04000c1c5c4070142d03505111068640045079256401100c180a14000c43c2d5603840c1c03080d140304d12502501400040d2516030807684044085500703403130404544203094000078122080c4a5403146a09d00b541d00440344803020034000700c3d01e010000c0d04802110ba101400d858588080143c48001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 244947922 1250 244946672 244946683
    0x90c040606091208130e0403021b0901090905010f0c0f020106050103110a141209070e06010309030909020d0207020310020301140d0b0a180503131401030e06060d030e061308070512 79
    0x443c18111800001042405585011590542e02d810441c3c1100340e15449000a203210a590840c01403041860705401c110b0400300d5100c0620004000340556441d101c4030710003070003600c4410307200c9558a0b843c18105048030f10401500c2c0c00e07184c490300c840e01d850a0700a801c40b41503078406818103042c1031460803010b203201c04441601f8200d00b0500c004c544c169a000b4960701841c2e003807400b00f680c014213000c03040000240c110100c0704140032454142c1d0328400110150b0711402401400304800c000e0522454009402030002c2100c40c440050034021380f41c00092030041140c0407100340c82d600000602880200c484240b140341c030103642e5100c94a80303560700c2000d0544018042c210069035100360070580340c0420710034000aa003000880b500c0d88000028480144124455a8001d1883d152050080e500070b0040030100501a806082c840c3c1d58602030000300700c00100100e00300201015903018542d10500035089040c850041605498103000d102e500c0c01c0081c0e08901d01c12801e000b44010380d407100044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 244949172 1250 244947922 244947929
    0x30a0206011505220317090904060e03130b0301050406080111030703020c01060e0103060e1005060d020919020f040e010b0702100f09030203011109011805100f1205070305090c04060609 81
    0x901c03101a07090140894040c0141804a9420340c000c036480444404907100440680e80109000d41141820385608101b504c610401e8582124070080040d01141c101d502000f5050074007400e803440d10009e641d1360118461030350003042c00c0080203c0144464142885148081c200030402002040c2c0d10307494101903030000a0540c82007640000d480c0030400d20a400c45001040c0030140d104c5196140c0c078200c0003400c40e005d80721035144101d510807100b80f4140e000d0a4002c50000c1c11450502c040c41d02440052040280980d900c10590700911101007103520061801700c0d40300f10b0303654403503051103448407411006900c41c01c15070070284101c1c80983d641b1062000b140f0007500741420200031a540545074084642c0c00a581035103040c240c0e50408001c600105a0402c090746c60300c1003618003508254020b00c1e58010b04d608041c181e0500844a801581420002c4d901800d040d16012501450b00301921012940b860000752110b0500007400000c2180c1103200104a505006c018144100103003104281d11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 244950422 1250 244949172 244949189
    0x25020303120a0b04290114040902070c0b2805071e02040906090b0105030c1207060509030f01020d0f230714160b04020a08030f0d0207030e06130e010503030a020601 72
    0x60110307114112540c0002c6552101400c2804407042c240344130b42644000c000200990b006031700c5900030562203524408102c184189000d810181000200d00007500040c80440b4100b01da241c010520b0b0f500700003d007034240041041c01d244806001da00700c2d000d01524800d002840028400b400c0080c0242c483d00c1d035901c6041c5c660100c2ca414500019010300b442d064060310952400d01b904060080e60102d01f0306070351050f001c0342c030074025a00c14000e0030303501c0c020640d881d40c1140205016482c4600000d00300ba5078000c040390004030f400b0b580242241d00041c2c4061000ba502d41c07905030589141c0c00f4a51003c024074080004528030316002c80140396000382920f0420091258948085101da02614610502c00800c2c1042e0005d900d400c02041070b0aa40c20b0340700c3c10350604006900c5000000300c942420010142508110a609188000c5c1d00030f018118203020450540c10391544845018121246801c1c0c45c3c0302c0d0181c43e088403d1900c82042c1c0050780603820400441000540014550381120b2411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 244951672 1250 244950422 244950457
    0x203070201180b030a0f05060609010215060117010f1d15012703141011070609020102030405060c0105070f02010b030a021e0604080706030507030501060c0b0a061a25020303 76
    0x500b030907500110300c3c0c00050310040c010050003542c04065002e910300780700800c010412502d40c801044204d028021107030b4010b038800300e0b00c4e00c81d00ba012401c494200f0010305040c865100c0c0d482ca0784010042c240c12134043d210412408008100410f803071080c41511041090300340341822155a1751901c0c00d0308902d0b060003140d501080c10071a02c0810b0717004041046404813030580d201e00e0003405a0800b181c03903100030700c5400780b802408021813095462002d05080b0451074034825a41d00b0b005001c1d081001d80c1580014040042c4a40f40d010040c00c501c00e04400005991820a40c040c04d00111460f9a200310781c5410201c40d440c1d01d0006d0211401c540444041c641440d1100a01c0354110b80110141c2d0054070209001800d200c0010f0014160317100743e1024040e9540e1a14210110740f0244608000988608404008103c10721039690300560003040104140f903c0b2051485858844100c214182c00000b4821280d03910801044d0304440d4000141402074040b0340019540c0e0207005250100521071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 244952922 1250 244951672 244951697
    0x403020c03010c0507051536010929060102120906040504060305010504020108070c0b06060d0213081c030e030a0f020709060308070c0b07020a0303030b0604030b01030503090109150203070201 84
    0xc0054500c0160010002d210456201070000c01d2500f082400703c03142e100e08080103020402441c5894494181e10242d030702800000c0300100907001c5c1045a41043c103e10305a06c0c05004000e0158076601400381d41d8a07601460500064100700420070700048455940d04e0501007039a03070115105000403000704566440d46003510000b107040c031070759000641c824500400041044070640005101e0341c002d807500441590b85900581344c051010000506203007000380010058a0a13401030071071080e400d54010b0500310600c0c441c65000c0c0d80340d080110701d9400111011080f141081c889000182103103400d003d9250032074116640c07800345000140500602101d220100da100b000300b180203101d07100f400d10545a4074140703440300d135202304800c2c5ca4a000840c030200b01202034004585021b94054008082e141c07940e10224001e005051041c0d501a201300000004601c0100e03000d4061400781c0c0103556200c040d0340014046401581c000c0c09031505118030300141c0c0d5004829198099020708107264010706 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 244954172 1250 244952922 244952927
    0x50a08240d0f05060106140909040309092903010c02060a0b011b111507020f010c06020408010903080603010c090f030b04020103060b0a080603120313080d0902210606090105090a02030403 82
    0x920361459a0000d00481012050101d80703445000c55602400c161161640c850000301c5000043c0b14428640345000c00c9203104078181040101c0c0d00c580603182910f050b40e01c4044020a884813088049130490845902d400075440c05072062805a2048008018284000134041d44602d00100901d0b150760340e8440001059004020b1255030040401d044800d40904e468901d59110141803482c0c0500d2405c03a000c1e243c140c50904481a00f50010306048458a10031300440300d10016881c12103000d60280030006072480c1c05d00484000c58829101c0306150700d05041418219100a001c01c005c0110003041000854520720894003580e030840e0080320f150b074840c00140d0117845540e01003248890001922000298098001030040c0c004070207941a610003500c403660a4001501c8000d03424420f203150b0000650032000400340f221348100013241b58515500000d04648003503240000110a041110441d2038082c008140d2125044440c2c4c800d6504086c0401c1c2c00c9440148600c2400313078000b002c10103060 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 244955422 1250 244954172 244954231
    0x100e040b060702100215010b07031e02010902030d02010903081509160e061303021002060108060a090c0f15091a070803090309041e0c020102030c09010e150a1e050a08 73
    0x290003421080442e40a00d0009641b01c509040d517152540d088800481e8143d40031049505950b05a40c68a0201c241c02003060038001c00588440d007550750752901c001c0140c809101401410041c0d4000040040c1581009085404000e01520103440e00c08480c101c00d5032580700c5260400009024100c054880360b40980b0341e0800d00300002ea114101155540b6801c41e98185082031b41c0c4223543c2c104030400c5020050b6034070b071000e01483c02203410660000e000344103503910841c0080c0c040e1519180ca2555903084502080094000d0061401e00c00507200c2d6968000d86410001e0540c0509030400d01122012442e483c0558131300200603c400001144161804109035000000014000c0003206074143c03902100c42c00d0000d0714000241000c59100c3c05d0b600610036644100c00200002d03103012105801100c076111f0425150b86d1103071b024440300398040f00c60000ba040c05030170f64480e02c0d0b80c06252040303a14039400c94130b444020082d04000660380340340c1c413140c5290426000e02c1030780c0a913102c80300c0207940700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 244956672 1250 244955422 244955437
    0xa03230312010e0a0b030615151c05180d021c090e091018051504081201080d03062403051b070501050f1e18030f03130c05100e040b06 59
    0x941200c00100b40700f050071600381d005200c40c0c442000307a8000c24050603142d140840300c40c040360131201100c1b005400c10040b0030045003103046089160140d11842c002082c0500702c2114200783da190204a00341c0400060904202104030041080c002c00d07040003551030300d03140e01c1001e43c00400806000142c1c0030740c0086024042030010161540741541215036a00503014200003141e040207400f0311350000c0403256084058001000d84003100fa507902d0580120340203081210303d170a08101a810244007000000e010300a404041c00d00790b107d0690042c1a40c0c07158104403008070282500305d480d4410141000011641c60401007880c1c2d82c2e4007240d00c2074613000d209a0a507514002000410018190301081c4141c5c00d450110200d41c0f0384401d807145004a03031040c0401c1d1166200468006850341c028032804184100c2181d02c2d1041d00110480550015a40401500c1c0702d80c0142d800c0100480d5048040c2500303171400e5501030009100107080c0503103460500d000c0c0d83d850700e840d17205480e043c0454455 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 244957922 1250 244956672 244956697
    0xf0b0901210e07090506030c0d020d020402030f2e091d07060507031103040501050f030405010e0d0816020105060a0b0901090803030f0612060106120518060a020301140a032303 77
    0x40250025001c000340107501c402d040035004140f000b068040b014844c0900940c409402411124086014803403030900c4032000b80da0207420041c070000140d5841c001148220078500d000f1480d400c050341c980305007145003076000022817083d0822014030311004000d13100b100c0703410380c021603a0340c81e00724001c00c80c036450381d10703e84540a6282d000c5212500000100440b0303120b55034a180503951000300a8482c0200d000c0c050000c1ca0401c0036001c003001c000040e5030054054800045c035400201aa50710f001d2900c946200415110030800c4540000c101f0003000c5a55a40000d00440c80e2100011f00342c03190a0080070b42245010442c08802c1e40300e075003104050f140d0b034070490355241414802c0350740c0f8420444101d4422141c401a03480342d001d002c99007504a5856407200922002d458682e50041c0c00024041b000d008100091180032001c100b2415000314608800180c1d65410444207006803081000c01e0f42c00748044400030400070710940026640c0790030f200d10465005c032400016504600c100b1218001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 244959172 1250 244957922 244957967
    0x10f0c03110d0306050a0b160204050c041706010512010e150910050a05060a06090609271404050c0301060821270906090402090a05040302070b0c0102030f0903040f0b0901 75
    0x2c419003607840300c0b050782c00440e25038443c503903030301d15462503882440700044860700d0150840700182441c1c0c0209130000c2c1407101341424561101078181010301101860404d0b540140f004014506140c0344a10040719075100a0088200c1e10b003140b40d98100320b030f00586450800c000052020b035004c1c004c486034182d0643c818041030400c100c55501800b002c0c0c4520b80308080c8034100043e801d01442010003102e10a8413400c3c2858902280712198171000166000a03401350100d64400311040e2149480544881840d007816007001c4c06c0c4185030000c0610b41c28040d0b03152036414003076074a0000744100c112861600c004a0640048aa892580a041400101802c404800c501e42c40840c1219001c0004246c41c041090703070b91201044888030060794080d4104001d000072501c002915003160740c1c0640280101c5004580d6a0264203040e44002e0010310312741d5000c000d000380d045074006915003021401c002942030a003054014202070009101c0d0301003410300014054407590050080f4071410702017242002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 244960422 1250 244959172 244959193
    0x31103070308090d0807140304170301081b060a140c0304030501060e07030c0320091807090e0a1a01050d09021302120a06150e040f0203040614090c010f0c0311 70
    0xe100210980d1107141038050010300c48000c4d44501004c40c07084046503507411080400c03a401c05003903400504180d135030745100341c50100d031000d4a80056008040100007405102341c0780000440310080801070783d100b001d0070044c0600d0654800078180000300b0180d4103039503400c00c4402d540d04d18483e5600003403295080210014004405c5865103100d84240d4a041c4404100306030700b1030403a090200102106090880c00010000030395000e417000702c0c3d0260070008114521400c45c400030004039512400076915030000e012000005a6554206100c000f041c0250400e49100140f550440a0002d0400c000032516906100c540d0b00a00c80341c0d0340140901d400606e61106144c080d6120100c041c488000800c00320700342d100603200d0013084aa603041000203c5440c11b00c1140d04400ba200403903405520341c08002c00905480c07004600940c807030f90b0300240d1116000b819001c001c90050040c2c1d85500700c501400c40b07a076001104101c040d54207160299072441149400d03138213400004056800c030700c0340c00440d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 244961672 1250 244960422 244960427
    0x1061a090a0e090607080a0501150e03160b0408010b0108010e0a05101206021207180510050f0d020703020d1407080f04081605030f0a0f120509130c0f0309020d030c0311030703 77
    0x205e005c0d042031303078901c00c081e43d071b128440e41520000c0c4141d07100c490044030b100c001a803040c0001528044001d0640381c1c404611045081c46409540203511011000034003041032010900c621040c4000a081914840d071420684200b0000000d0004208503100e1000480800c1b40b82c00c900c01618051001000352401810150300030741025069603c003c481c035000c90390f03281c041c07107200d103c240141270520b05c0582003405202d0503013005440b0400784641400900340380d66a58014001c0726403185c00c0143c40b00d6036800c000346050705114400d03080c008046250741c5078008040444d055540c00410140d9100344601c0f5140f210301c00d551001085003e02901303400c2d41070315602d1400481c0d00450848045112580700c05480305120f0764000d00d0000d401c1c00700000140003020780c40b080c440c103007002c5040c0050400850040c54a900c01b0107003243c0d58ac0803204001c1d804c03045019000c661483d003001052001d134046001e0041900e0081c0500580d21140000c05d84501b00385400d03014200d05480c2c40300b4540c40c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 244962922 1250 244961672 244961683
    0x6040e1207030e0405040209040f15110c0607182102091801140705180d08040806040317010f0506090d080c0d09120206030609130206030c190201061a090a0e09 70
    0x1100026042040241a80713028003030280290b0300280482040c1d162580c400e42c41c2c001d40364045501c040391400e501c0b5030b0390702c5103e100440c100303203465955101d081209407421310354014628000d001c5140401401038018400550540c0c9403801c0c02000b1004200c0321013428160f90f10025800000c44d0704000440d00c180004c000d40b0000b0400903c2281c11408140c0d10b00d440480c0d19900184086c4046000b507107003d0407609048002801c0e40340b90742e84944900c10030307500c141c002c5121913020b0b01c203000030540d01801801a1580c003a1741e00c80d480d410610064918042442401d101d80808a01e101c40d5507280c1c43d0300145164410240b42c2d0325446515150f45508178000c90310b0200c2c00350000090545100e4032503460240c5d00910007032540e5108400c000c1e02d080080e0501c001d030f001e020b51400040c1c80b80760080d030007003583c00005c580703442070310f5101d010091400803050110790600c4020054003603803028005c6403413000740c441074070389511001040c9000b0881e88407404100500c0184480000c1c0888c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 244964028 1106 244962922 244962937
    0x3090409110d1b060804030c02040c11060a06060e09060d060e0a14010b0405160804060507051e071101140a03020d021204051c030915020306040e12 65
    0x1c070b4060110340c001100c4800741110610040306035006100c00820a900e0108250f00d0144c1d0010011025044002e01403502e0f88031520310203020b1a80380c402003006500301d03030141c54407013074810191800d481240b0100b1481c2c07009a009041070705106105040c00f80c1210141c1402d81c0d2a60024000ca805030b0100f4000c030304100340081d41c80d00b41041c1c1c2030502c0c2c001203164620101003200319440039002c807180c0603851020002c560b420480c1c55505c01d0f0031010004042e80c0303600c01a11036105040007400c84180c2c080e00c1070080000b210143c10b856008080246c9200d41d82c1d0019035050a840b500001c9500091212041252280d00189644a5a10000f5040505440700c20449040c00d8400322201e41002081c035441300c2d0621411281c003426445d0600c81460b8545074140200d904104824186400000040307840d2a41d1b0403405581040c0300880741c0d018009003007007109070070504 = true := by decide +kernel

theorem cover : BRFrame.Cov 244784172 244964028 := by
  have h0 := BRFrame.cov_init 244784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 244784172 ≤ n) (h2 : n < 244964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
