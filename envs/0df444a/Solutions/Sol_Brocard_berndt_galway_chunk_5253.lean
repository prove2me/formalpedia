-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5253
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:15:15.258528+00:00
-- url     : https://prove2.me/submissions/e67bc1ce-35ff-4ce4-97fc-06d21dcd9efa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 944604316 ≤ n < 944784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 944605566 1250 944604316 944604329
    0x2a050d1d0f0f1302091003020a0305090a02240708030a0903140325031d061605040f151206060e0f04020a0f050904090b04050a030809070b0901080a1b11070906 70
    0x82c09100c01018403104800001c0d040204950038001e0342ea0b01d0312651510403441509a0340142d440c1d01d10b00c0050121803000d88802d0740343d44034002d8800180c4031035080300c20b2045080e00c00440014094176850740780c4901d0200500c13034039011051115400854001d991803602c43d032109451140001e00c0348417240421104c0d021445546541d10038034414240344110302640c0d0340b90100b203100540d5000000e40e1030011030040c56034070410070003c440040d2500b188003092286842860a0718002100d040c0e0901801041a151034040d040020f2078050303505c860712110421418031009681d054040c003202c0c0e0345460a0b002d003842c09100e2441d403400780700b02c0c1d090418544804440c2c4460700f108175000e40100c0030349034000c0d40d51005680402d10000303e4a10681c800e0005200114003894018842003001d030902e005944040b17428481051201c055a180b0700082c6031000c50b560f9641c660b10094070750800703070104071030401508ac0c40d01641320114008022205080701c51084c0c0d68041842140c14511544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 944606816 1250 944605566 944605579
    0xf07020a060b120303131101230a0302090a0b0307120b0105070605180a0c17012f040512030702040b1009120813180c0f2a050d1d0f 58
    0x500024200c1c0d07002e00d0806078003400c1c000d003000c080c242d014956482581c40e1007500d0400c0c800300040000908110320303940303002e10f4004548001c01c1c0035841408004508512101d07000308000c0ea90398407a80c16203d0b030050051240300103681e1072030000225403007903904c5400612840c82030000301e9410b02034204841410394604d4603010290b29808001c0001802c403900307601c070079080d00c06c100c40c0030000d0320902c6002c1d107403104181d450b1040001c190a02c4807010b094a034184018640200d28099840001740c80820325120440c0408076031f920140310b10303001715034818441c000004180714004040d016640c42980c041085541c0c1d00700300308401404000080c001003165100748021900c850216443c0341c880d001c202d00308401c604280529000036045162901080c80c0c0d0781044c8500d0733005400c080c0000b821300e07019034040080e00520049001d03040f41c40c01d0800c41406004080c4180d40c6404860b0848151058605610030091100303510013000d681c0d000400b03c803000c0ba840c144203800015400144003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 944608066 1250 944606816 944606833
    0x309080f0c0f06090706081003031403090a060603151503020f0d020f060a0f081e131e03120e0105130f020109150504030c0b0a020c01031a0303041d0f0702 68
    0x88442981c8a0606215640a00e448800215400300f01843c0034080c3c00029103201424440002c0003880000c00c003070107510700d0090420200c1e4000800c00c402216945419507aa0b940f60640e520b0301140d094000c1c1014075203000001408180b00303200c030401406c00800d000c4d01e1055800021000d00341d01000e58041c52818010143d841d107100700c0c50403903101401142c0c103103c095001030400c1d00300001c000c0c00310701445c174000a0f6613401900070b6481220412204262410f00d03003148034620004045500350700480c014a0240180010241140702c0b400e4541c0c11109841d1400810070032450501019860070101e00e9401c606c0c0c1805418454032003d0100c0704074070300700d89500345031450003a1b05905000d000d6902040011440038001072440c019200c041c1c2da5451841c00d01c2c140300084d030200503240014802c00c120716a002c2000f281140303003440c0c0451222000304800340034024031140681d043c03100103000034958202d00030380c409512242403060369543c1c0e5816400b4842c40304507048401600084c42 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 944609316 1250 944608066 944608087
    0x140a02011b1d0108101a0408010b0114090907050409020304051501050d0f060b04110d0b01020c0a061704050f031611120303070315050d111003271a040f060606030908 73
    0x440e17074890310b510304145c142c43d91100c041c249146048007055169900090600c0b41e92001d0183d2041141700786459401403c00e006041c2d1607020342403940c0e10032302142c40442c214500c07440580d4003406062104554a040602d030296aa1880107120f40512012900010b518905901e03116a459005028181c0b00106603440000900500f0710300765115945002d602180c28840c00500f5000d540c000f40062040c070079500280c6400416504030f446219448018040140c0c0401c9403845440d4200c003034049e80e119417504c182400f00c141c800310300e10700c40800d4840350140110683d06a050080f5078034840400c41e40c040c072801680540032449550720800116551600c03c0d0300460705c0c17981c00c096282c8199207500000d444070218080a980504202440040350710348044900c13000b40307090404100070001101440f0310300101c20004121101c14020481c28091a03039040001c03e07500ca10104401d103000d1405081e901c03504542640d680b4601400442d00c0340c000e03c200d90b04030744c10030780b81802c241c02e804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 944610566 1250 944609316 944609327
    0x41413051b060a05032a0c011a060f090d051009031403010b0406050706090204020f0406031d100f0e01231f050607030c0203071404230406020307140a02011b1d01 71
    0x10b02c6e014214800e01e00d03c0280c44400041803e11046c0310845c40d580342c517007011150079900510150a044026401001b2155a40c1422200c0311084641c0741a00d5540440028040b000d213514050094014480d4010541d9219406040400c0c420f8480310058102c422030400240024080d440041070204010321100340203001404115118140229400070254003040c103a80005c0e4110f5903840c0e01150907c0340c19058060f050108170040b004403028842a50025aa600041ca019a880c2d580c1d05c1b102c000801d642d0000b031500740f590301c028041c03107014913207030040440344543d411801840000415017580d40810101510034600900d80e50850815041003000e61014104505210000510b000161010b014070070043c0300c0d5121002000b128001070200b0b50780002500d020090b0104001500c035843c011281d40c005400590050b201c0d907036800c056504a8203000007800000c8040f94009c0115130541003001c1401841030b1100ca04440c2400940314207a1142c00110166200b8042032419441031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 944611816 1250 944610566 944610571
    0x8040602190f06151a0a080106110c010e01030213170610061d0105121810090314092403070207090c0e09190f02070c0b04030b0109050402041413051b060a0503 70
    0x706602240c2c4c07130707440841c0500c0b0f6001c8060503182e004045555404150490b149034014121400e040920601424074503403690400c50942d414011410a03401840e4483d40c10303110a0489140b89800990701c41c1000f2400801030303013507000148142c000080400340c2c50b0040700110740040c1c0304c3c5800750000504203000419220321035810030005000b1880e19042d410022400b81d0105404442c00030f6a41d50510f04242c2071030001c40309142071618000001c0c0c1e00181031601628100c9885888140c83c2d00020340301002481c18032400581c0280305155000120002c1d40207a4854003128940d559a03400035068410020407540460880c0208000f1404c01c0000d555011140b104030020140c1400c1c9010700f2a41040113061403254046000000c1003080009200504036a5102e20f0a0515644d143c0300e110005002e0035005a0306d58001c101103480740c1d0030440707007840032500c40402403910380f02c08520746181c007a00b91010301c01c444990039070300d09503e4059451000504641d1a0075145082640e559001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 944613066 1250 944611816 944611841
    0x3020309060a0c0b1605270a06170a0506150a031409070f0b0309060403050705030702030d0c05100b1e01020703080c0703030f050f041203050d060308040602190f06 72
    0xc1100808a80e50203000742050310b9280c969280c0b00d1054204080c50b418001c00c0030302040a10822019851307081001d0324058608003004800910100030500d030751805040700740f0f4201040c00340205520b9048100c0004030020b02c141000d0655503100118192030050340d070260001c400040e002c02c0d103404d00c00100032241e5039090200380080c00b00140100380508940c4881c1e80d03082200144030000f04004402d00611091900900b14200f002c140c584801020341300806010340081d6107001c210f03061040d43c0b14160020b044e00c501c003048940140c00055101c00c02c45a43c00362160115640d00c5a1258414236030015002e00c2c40c500352500300c03d00c1702110390f404605501c03400a002001681d03a60041100f103241c1c002405000d85146409440800346464900600405000050b42900c8103001d1b1402c480c40410300c800300300b50f44e080076102c91140000c0648154106600881070000c544d0090040b00c20503400c440041039407203801101d09803221001801d8001d01981080851180c0c0c004030030f20401c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 944614316 1250 944613066 944613073
    0x50f1b0f0d060b0a0602030406020d090812031305070b0d0b1008190b060f0901260c0d0222080f01020f0403020f1f0905031923070f0314100e0304060c0302 68
    0x3150b00000c0c810080d07540c00000180d100090274400300b90b0500507203964030f115003480507000f420641640d44502c01d0482d500c48911010000504541c10107000c06203094100c3c00707460030b00e61152400d035503030f83c80303000c1011744913041c40500c1c155801d01c8082c440c00b2818541c1c941d0826223441d6070551540e241481c00000b8543c886102000a999103030080800c0400083c0541e91900b041002420100310000b0307400c01034006642da00380c40d110302d03190154420104484540d0360841883c1010090080501c0498100c03024400a40005c481e651480b05850b440c800720350751101e40914240c00d078070443d01401c81100047c08200010f05000004400d9400000c00305090018814085159004d0412040d0005003140c001000075003003d0110f07400e84904000146400c0307420351202c40341c2002083c600c4000b1050301c210041c08038400d0007981c0c068200c6d80f80c86840d490342c0c0c1c1802800c4084525003680c56010380c07003140e032101005100300d0034100c50150145043c0752a019007520340502c52a810b409501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 944615566 1250 944614316 944614331
    0x70f1b0924081b120d1d0922050a060603050d200d0e0a09090f1e02090c0a0c050f030d1103040f1b1802280806120a050604050f1b0f0d06 60
    0x7009002000200441d90381d0501b0100da110503040c1c4d00408412014003441c540c0c014803c0500c1011a413440e00120440c0c2020610302516165151022104020309100c0c54200044200400411030841307400e4140d580605100c43c0b5402a00c0110580d00501d8003a440407202c00381d094000c0640880e951740c020880c425071507480314008291045440c0c119264519542c00c24100840da03030310001755020b8500784c44120101a07010a121420141808514000116004002c18460500c07039110540c40700c01d0f2190340000102a5580340c10086000352440c0c10503c220034207402d287c1c1524419500040c114081c0540b5444d4600c960f00260115803040c0c91304000400c0c0564000700c05070303640c0c0081e0030059460301e10b07400c040b10320700300c45041708c07404041d00b0a0303007900942c0800d865030090811140c200c000200010414070b840d4105a0060440c01800c04200074440040740d64041c004222040d155108400ea207a43c103d080900b000641c04030f9070303200c0c485050500d003000c2c02210340703d90000140107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 944616816 1250 944615566 944615599
    0x5150408010204080c1e0315040503090307061121040920180109050603100b0901091d060a05010c03020a03031e0905070801110f070f1b0924081b 64
    0x82c0c0c4030350804c1034103622084680b200d07400c4c2070003000c101c01c00c88646050b0b685691000a0707110700d04c540c10b482c1010924800300b0140320341881214a251001401c039003841e65124409080101c10502e4031050b03008030640c0141d518107184c00f02c541e65041002c100d02d0720303040003502c2009001308010021103c6c00d00c4072500b8051000001090403000b60b0080003a1843e1020005040050941009009035000c0c4140641824001200300680e4a6880c100b07440d06200780040751034581540c802503000e1700720402009640003226201e802200c0568030324074541d40300c4005540c044000d0000034016844944c42e04003080c4203511800318154802410809a858090940c055036001501613a10f50000c0400b00490b010911070070303507070381d0b403807000ca5080086200500700c06004588024006030f510541640c200401446003803001000d440c80b070449640c071a08007000504d89428881702044440046141000040707041004407084000100602014003882d084443c00c00c04c5c010341c20018a51858508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 944618066 1250 944616816 944616821
    0x90207080403080c1e1f020a0815120a0b100f0b030f070e100f03151d06040605062709040209040201031e050a021305100203071e060f06050f09100515040801 69
    0x41c0117404000300a0f8402c00400f0301064500580100c40701c40c810010741c80ca840e08450700503808071041004402941110001c00c5000e818a58042c0090155042d42c108011403986c0490040d50b20300f02010025494940f952415444c60013040308a040501c0000c2c0c441044079038203036202c0d100e4640400b0307108252000c120000b400e0b0200c0d034040350348426440f900329030521a0052410740e43c00d002c0e840702e1810005031108641840740c0d900c00f24921001860700d032100d8012000924016021640e41c203c03501401c0201710703030050700481b001168540d86d5850b10b058000c0c20301450300144090b405480b42d5005500400c003009071206070038214440f921043c825072140394802d0880a90241e82d4940020081078032803120342006225419607898071040395070020907070395040c0d030103201c000310800e0360f03921103407050f007640320042810341029080405201c441d000b51086800549480b9503400009041007a000030450302c02180001d0000100814030740000842c0310100003101991800f622048618203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 944619316 1250 944618066 944618113
    0x60509040b4014070f05060c0327090a050403092c0403020105180a0f23030705010c2c0112020904050a0e0c1012050c0412110a090207080403080c 64
    0x4a5820507a000000e100000d43d83c1041000403001401d00c880c20454882c4074441c40307010741c0740600000700b810301c2083e40810481c0c200e101da6200c0745040c04585460009452811080035015105541c0402c442c14000c1c000c080c080d0351b26444109085c0d00b03004468418a40301d80207005001c024003400c8195400362140580514007a500114a500d05004628601401e41c0202c022580c440c00d03110b404214021402e49046600440b10200c1d0500d22080d40e014400d2180200c500b4000000e84404100c0c1c15804100c964007103032141d0348146540c006140d0040404035041c902c0b0810404040313095071241c000c51207945100e500041c01c204031040402c0848400321200a0215600c4070048901d0304e04004510354940103d92019401c803070f2072001800c1126840058401d282c8480114907032203450710030ba5010300010400d605901e4200d0508510f04816031000074051500b009010810704243d0084490250f00816004c0c82d003442c40d45d5140c81603101e04041a101d00911000010064854a5414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 944620566 1250 944619316 944619421
    0x7060203041a15061c0605090907090c1b151e050910050903040608100308030c0307090812040e06040f2c06060a0e061504060f0201060509040b 63
    0xc00326100b80d0300d1044041c40074150520344041c404051810340e8800048a6804d0051307401082091502146007000d80b00641146600c0030702c0908101e0040000901d0f07204490380d4042c20302074030400000c151200c90300d11543c1c0900703802000b4080042086041c0c0c2c11b180b11085440002c040762154914034003c0824002e0706a126200c90900c0303420b480c2085001c50807000d00314100603508001c0c02d5255a0710a900c07a203410300c82200d0001d0f4540c134421082c0001141c00198a903175902e4030342041030f1a54021900c090202d8102440441d102c01c0004007d910003100865a42c07805082124182841400030700a951050701d4020340850407220340079078141c064140070f50fa22681420f001d80320500540126010040c0d01c40c1c401c01180740c0c0e4074034001e000c40d40580041c520301e4564030302041160702a15800340c1c00c1000003c2c0052001d03031002081202c06a030754000c00442d9211420031030050401e54024003003200100108069492020210854a2118040030120700469003003c900280070034007107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 944621816 1250 944620566 944620583
    0x17190203010801021c0203280902030303070507050d080c03010b0f0d1505030d03110a051c09230a171c05040818091303140405040e0d020d021c0e04020706020304 71
    0x8608840c0c1e0302c80c00745060100a85d043d400c5140c6181d10140c080a207603802801c511910f10040e140d40c031203038071460038190081d007035030b541c1e1030b000c2e0010302035500c905d804a0340c610448000c00949881005514014201200c4640c6184d2a0805003500354012012004062008024402c500d24083c07041c0e203102120a40704031110f0303241600309810841450381c0d00c41454180041a0b1701400c405003100c0d01c00302c003410465113880510740000490303079528071000ca2152903c000002800140e020100c0b00000c01c11398044a10701a54410303444441c642c4000f448001510082848441c4100180440d800707500c0d00c80c0d01c2c1585901da0340065403002d0b01c8c295403070712002813050103415441180640c0b1210a442d002010704042c8810007687c0c01c249000f90412101552018a03c00e0300e004132401040300610500039080980000d84c0c9a1110001440240c40307a140c00c3c07070130280042179429142c080c1c00c4407100f4000794040700340d504000001000b94020340c02c0004000142141c4013850055015603280c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 944623066 1250 944621816 944621827
    0xd060b1917060105060304120305040c260d021b0409141605091510210906020903160317090a230a080705030a020d020301060801020a02100b0a061719020301080102 72
    0x3a00b80b28068204900542c000c00c20000450b030754840e040d00000f20b13840c0005650b95182031014005c5001d0304003007000200310210820031031071080380502d01440281600c441424840c07081c0c1c0d0310307084400701014250148148454a1405034412000c44d80900d121882403040a8500703401c01002058034213190600c3d190074403841c100f03a8040c0350310401754102140524030b5800040d00307000d0005034070000c100c441220b102000042019603206d100303940d20103100d4000e80c0d05e059006900540c03d080e010b07215a44110042d010f0b00d0300600d0450760440d4210321502da41209045259002100568200f0300c5c82d8400030720041c0520410400311130b840404424103c80800b0424104803039031000000354032403030007480565008200c0c0e02046034102e65008040c0c0007031010038003601156000030366951011031075100c02e07600880c01032460070220300d04201c0b19210741d0800250000c14081c541c0042c520240e00c079030113003030301c0e94040d0840000e41000381d100340c2030314080050361300c241c01000440c0d4001c10b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 944624316 1250 944623066 944623109
    0xf120a110c010903062a050903011104050906090c0c06040c0e0609010f14010e03101401080303071205090c0d032705130917040e0f01080307020d060b19 67
    0x208120608010302034900c99400100003080c011180c0009483c1d19076404000c12110011140c0c000540e4241095000e11003c82002800c079400150701c0c50b009508003048600220159001c41d8192030005041c107455031a0303201403001c030807001041900094400c00103d1820b030f008100f92480340740f141541014840c1000a1000f07882400f80949005006101c01440700c44a10603140c0305540d1100840400841000c0040f5804140c4242d800e805000c0c00051040e814031796040350a07503081280503502142d99507407800d40e0f6031108171035140010754142d00400305060b550b000b02c0d801280800881d440340702e002001402c103520316039045011511100d8031881d4800016100140b04030b021044821181c60000418040e45402c0d909095195840c0310301d00c200512694844100455450380030744558449c549551048000d841c88424080010000640800b00108584200781d02401c3c500c8000319503070310480030300340c1c2220060f8052249114040c85172580301640c802007001300f05442941c0b0b27003500d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 944625566 1250 944624316 944624327
    0x40803060f040509070e0c0d0e010609051e060603100308120601120606090302190807090f0b040b300f0618120a0809031209100608071a09030f120a 65
    0x55000d03d0900c1c042000050001c9600350072651180003040300c4e0340d6400304281c0305e0b110314002504c2144c40e082c00307001581f5055200c2c6050321800b0004000b1174841015884203800017131171400a4408d0a4005011030401030003958000000c09482c9203d15100d903625070040d007042c07914a4403401543c0401c0295070303108080005075a0802c1041008030f00b48070000f41400214040a8000c003003014103003c0004000442d60024210759043c2e941160303c03028480050300d0790400d105030503030174201800410b1400d032003440c007240c030000c2c01c451210b0506078800300d903802c580b403001000041078540024920014010920345003040b9010b04007510b048203030415859244800c24400b94420030034091603040c01c01c1102e01e51012810414826a2420551861031040c40820915000c10100b844140c00001410202c0c411500348140010768032031140640d01c010340c0c030854030004051201941424485002022000e101805441203030b5180260756140c0030307680f078542585503000141d8400561b800b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 944626816 1250 944625566 944625589
    0x304020a061b02150c0601030b19060609060804020109090c050d051b04121b240f0e04020c011413050d0201020403020d06051f2d0b0d150b0304080306 66
    0x142800d1940042030785442040c80c401c060000c0c000c00900740218118104c0c503090704d440d0b50b60007089420035070b1a81341c036219885098411012040e03620064442072070725809080183d07542603452043d064902401120491000360003030f814040c1c1803202185100540c080d403551100759446141e592090360f0441d00c1100c4e0018000f41419900341c03d410698081401200d04a4002e07600c20740ca0416241051441c0300325407810700c0d40e260198807000950300500c64886418103076898009040e0081c4d40c8069405044000c0e80c2c000003055200310013198a80356004c2e04008000c0400011140c8060903281001b000c00c1d240e12800e0242d40f40d4100c1040030800c00d6100c0c0c9000f5100a42c20185036074042645218200001804a078480000800521300c80d011400351010040895810603661000030540f0038103503402c480c401001050356451080c000c60f01d10116008556400c1ca812511034001c801071051840c1c07222424980080010006007000145000300d010b210f559540e0700303000d410042c038400316 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 944628066 1250 944626816 944626829
    0x6051504021306051b0607020a060c020a020d17220f080a0507031514240a0605123c0a0b09040f0309050607030909050f13171e0304020a 60
    0x4020504082009110100c1100d0fa075042180d225003242000005c5080c0c1c44020400500c2454200301c54607500040315100140144402c00c1502424182280ca85c0404000603401c070303103903110300c40c00141201030783c882000d4031006850400030091110306c0d403010740010a516101e0f050320103200202144070200300801c240401025680601d0b85c5050300d5019a03c0054019050307881c2c5c103da03402c00c50700100c01c2e01120345641072042c940700da4004c00f440754004041d4901c510798030340c40071a4180081c0c2d400c140d820b80c1d15a241805024811505443c034018891110022018a036031601d0424410401c000b4560910b94400c1c260b6141c40003203201d0700200011009410724130300708020381312550309a81090700103c3da000e05500a041c16a1030315110340c00180c00290004082041c5544407500e181035442d006014801511012070f031503041c034002e41d99443c4500202d0140400a1981940d42121045c9082410b0a0010000703201d1459600d11183d5048030b0780c00003c01045281514140002d802c0b03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 944629316 1250 944628066 944628071
    0x50103090b13020102030909010815100b1b070302181f060c110f06030a090506090607020c060711060a0302071a100501030f0b19030c0803210403110a06051504 70
    0x1064445400c40180034001d00c030400d54000c0302c101036920038021100e20302c00c090444413403541d5a401250303564206070360070300030001c541010036101c6054030104400c807414490600e0030301c5503000102110029070f044442d0f140c41407407000001a207900e410103800d8903501428003c0c600d4201e81c1e0040c400c043c805003501985c6640340601c4107070b406c402e12181042c1c100041c4510070040002040b8012042e084580d40080e01108009064103290404030382240310b00252075058903411011a5035400544001015802444400e5054240320002e042e40f6401464810011504903021543c19404103602500081d0001081c006000030380c0720303035007801c081d0602d1847c035440c1c42c441d2801401d203d401040e0415440e200e0075008102c00e0b800240e40301e10010100c0c5a094840c1008500c9080540310403280f103c0f0100b40064040400f00c243c90b804001a4200f1204c0e4019051000e455600108220103010300c0340301000034503008120420650b4840c480028050500700c4082e03410383e00b0b05651911490 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 944630566 1250 944629316 944629331
    0xe0402120c0a0b090102160801020307090b031b07080d0203040305070c0e040c0e15120708060105011704230105040501090b1302180901020415051c0204030203030711060c010c020a0c050103 83
    0x101c55140300390403180c1c0300281c1130f16840c40c100101d0800c0d00c070341c1102c440350609074008103601c1c50660080d400745003161580e9684030380c4c990710310f811808119003203103c40e00e04414070088600b40000802106104800c030624201c104504141244c00070364094000980c049412810005280000d41c05070109010071491480c0c59507800e1203000990183d0510b440c0d202c00815010141c074000c8030380d2200014a4500502c0060b09840e540d00807030300c01d22aa80c89581c00004d11075021380b22800352400313010078078051a56681ca0395060002e00e005030b02106195030003203408440c82803181d02d0007588948000324042040d8101381031011006401301144c00e10050250005a90702e0920a05c1c8011141450200340e45104505009010750b621080c11401140c661001d00303948103001740f030048007281c44442c500d1400840041203004600009401d50710400c590004101480c0e01004410001808246000c84204d07899095034100340200e40540c1c0607180b440100021040b1100151000786000c2100c41f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 944631816 1250 944630566 944630569
    0x80c07081801020309041406090705090901090b0a0315150f0503031b07030503070b0103050114060a0b07060605190503010b04050702150c0c15161103030a1e05010e0402120c 76
    0x1441040c180c040041c05401000c0c507141d0003031040d02c4400000400801c00d401c0508017100400743c040b100369103d034003a08001489603018209460710b905000d00103802c143e0810008800408a5000c46503000c0c502d200c001001980440c1900300b60700041c0da011541c0701c2c0d48045034208107500e801040d50b9444511003803020740c9000056400518854001c2c2114030882c1510a0902100390030282050100003031140c10b001078410349a040780d100e600200300132032280c2d813001003c03a000e6a10760340c42010b120b010000c042c01000580340250240d07100150040e03503080081c4100107100d4181088541e1b0803400c20a0340380030310400700010415141400f051804040094665241013991a580c5040502140c40c003039031042039412101d14a01200c440241e1203046450084085401e0b4000c03c0d40d04210240c050702c00c5800c82d5240400200860454940c03a00c24405060a03004128603080d1b00c4a40c00002c00d114001c80b802401c40005c418580d0030240140b006d9544000c003007440560240b500c00320316 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 944633066 1250 944631816 944631833
    0x712060b18042018040207060e03031e010807030201030509100507020f1b150f1b030d06350a08070b040303060605131206110c0105070909090b060d03020a0b0f040201080c07 76
    0x200e8804c605031a14841100001002070083c8200581480d240100c040340d20b0034008020340c0144a131410174202071030940c80380c5904000900604005800c00c00003040154041c2d005650050401c03002e40b6190100054004201c1e0030484e05640140d108001c00c40c14078030148a40d180104205981400101300301c0c1c0451070b207052014400d11613200c009901c01e00718094000380c50800c494121821204fd07003e816050356600714804030358100340f40043c00034841000b0700c1c045600351040d0080d5040302c6110114007000398800180400c480c0515030340800014246001051494820005034042d402c06041c000c045800c0c5400000500c801081245c2d0f00c0140705104000300c41080506a2a910380303840c007807002d4034420384490b003000e4000c501c0750074100c41900800d201d985555900c240c51503550280780c083d0b9001c0300307010780301c9140d4002089441c01c04103411102c003402401183d00c0346c0c400703a49026443d801210004581400c0038248800c640c0d0020006130060402049282441c0360707510382468 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 944634316 1250 944633066 944633077
    0x7051e070201030b1c0b06010507240b150d050c090d12020a0206181201151a071202100506010302070c0b0304020a150203041d010305060712060b180420 67
    0x8020010402000310380c0301c1c0d0030aa68015001d080c011841c1841c4854040d80b070902c80b8200c0e200d00c0c52000098a95200304241c603051500900003140c08450203007181204a92526015441754850f020b88034541c0706c071440100308584584060b56180c5400d03104404540c0080d006020f217072000c1080e104950b40d07c0d200325034116001140d441608007808020b0b8908861800025001503000c1181050031004809840342c0031403d032200c0704202d401515484c220b07055801040f10403518854140300f1040c000f50a141211008140b45c0e240c411503440341601d90318200710305c80045c1d07c514035004d802503e0340901d6400190a0a0550070080c1a50380c5400007182c5001c2c40381c6805000c40010195030350060320200078080385075283c0300700d42080c600944940c080d014010700f0702d14031088109070044e0b40c1b20480c12a50040081c2c611615450800c407010740b51442c1d103e0354103441d02004100740d00c201c002445c40c0c1d221010010207451104040c082079908500c1c800c6842c0c5010169845000781050440c0c3c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 944635566 1250 944634316 944634367
    0x10b0a05030d0f020f060106050702010f020d0503130201050d02070b01050a08030910030218040608161406090103200307030b1005070b060112090c140f03030a210b090405150705 78
    0x890000c001e2022860700c402d50b017400e410380c85a0400061000d40010003404144d000782d8401075020010b10b401e99079980420a048000b40042000174840201055480300c030500c1403400901e40f541d80c00340b04050340c000080a80b454008040100802e203480d802c40c5000303225580c050b6080c41d0351600000e0140381c00044060606070000307a082d005151040344280c0044004108021f80385c0c41d42c25803a44d44030704102000e11100c0710440401d50904040c2459541000141003d2800041a00440150840a80030f14094913070054019403180000c1c0614800e459540e00018515200c4042040d900301010940c0d0600104202d408041041105000e0b817144080c2811408110b05910400c000c000d074007400340c1302034035480d00418095041d4019900445048a01054019000c8105038582c45908041d00c00303e4220702c1e1070608500c0b0040b00080c1400f804400207a940d01c3c1002084c0600c4044074211b0361900040e07030f5041d164800443d0907805c94080c0c40c09604240b506c2142d00c490695024141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 944636816 1250 944635566 944635577
    0xc110402030a0b130e06060f2101150b0a08060904020108060409020f0d0501020c012d1e020a020c090a0b0109030b10080316110f0d061d1e010b0a05030d 67
    0x1507003410883e0040d040408003e40300541c0b42c542e0f1600e80c80109800341d510800e5018800c0441e1081ca0a00b480b042c4d0090300901d107a55540b1190354a0002c181509074103080380d500d030700d0b803a0003090280059400070010103c2d2990b0341d2042090040c0301d084010416841080702030140310150b41e00c80c810030b511043c2920005031103285c50000400c80341072000c1640e400300344c14041f1010004190064202c0e1b43d030120092240c1c02c0c0500d811180c10f40c9040340000301400084940741079a580d41c000795001c0c004056102c442c500c030203410006a9201e2180480540d000d0321110040e400c18242c0c160b4040c1164204110b56042d00c1c00003403070a03200e40720282010010700040b80162008408101c020065902101c0da1102601c04a0304814208081601c80004001d540203039802c00720f090f09000c0c9001801c1d81c071400c0361641c03a03900400c07040e00003841c070916000340381d1082ca0007048040318041d2105d11b0103130f0a2030004040c60a40700518405070103a0394802d8200b00703a840019540c0101010b40c1001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 944638066 1250 944636816 944636821
    0x1214040605090a050f10050108030a0512130c090504032304120303110301080609060c03010f09050a0e070e0a1a10050f0d141806240102150103060f0c0c11040203 71
    0x141c0e03d03001002c800603103a802104a1120b039400001542d02018100f500c05010583e030740e641860322400ba200030000402c900300011140c82030104185581310810036107207613401e0610f03290009454080d40180c26403035540d406100a2541006c000b0220040c0214840818001d0f01800c00d914040ea1203104030f2996001040002c06010384c0001c810f00364072a44558496a45510580d6264415909403505000c1c800c086000c1c1c00c10401141c2c181e44414203843c1646240603035a1005220050a5403065030380c2d1a200c9001f1402440188010700f00e10001d11101e00380b0101c0380c402c03540c420241c02032880109580c101c4584070400e03c112607940071f00f0302648400300d4616011991040c050600381192504004091b80300510041c1c0d405031807a0541d03459070200b040754240e0b413840256034185c021106c0010701492050035500305444040b0608c1502c142608141c4003400c019021f0b0421150ba0f0340350b0482d10284c031a18420004000d1203890401c940c40c0c40da845080302540d010705014002c3c2d400000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 944639316 1250 944638066 944638081
    0x121e04030903260c061005060a0e100e09180d05120a0b0a0b03160816020a0f0309092f040e221a070201050f150909010f09030507031214040605 63
    0x80a1a071604011195039241e80c0b8400e005d40307550084503008035080c6180030101b4141448400e0b540d000d252502d80961700c0e00e07400c01300f0880c0c1280c6603c4404110350f0080c9401c094494900007801100d040c80da00d4000114061214102821034441c00c04000c002d02c840750310024400788054004000034000600000030001080b031010b03441e00031703800c1c1120000c00c0c80031483d0440c2441d4640b0780c181d40c607111981c5032069124680c480d020b0000340141d005c0e0001501140d1895911010b82d8440d0a0a41380c941d80d80c1c0c04182542d06c10352580c0041c0c07035612160f20348112001010b0480c43c1001034228507013030404c0c082000300030019251003250080249032855980f8040404490315402400d040040700108000c0143c184049803d80015420a0080303901a4109050240115140207121f80d219407641c09001c0070000040081da07080d0340f20105c1d0740ca0700c040da00c164000d082c000c3d07036100d5540603141000b0b480c01c000d40310140f2602e40b034480c180c60350f518046e0707211350050f90015000c0b80300e407607208 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 944640566 1250 944639316 944639363
    0xa1101141608061f02030304121403071110060801060302030c0a061e0c210e120601050d0615030c080d050a09050f280801060e040f1214121e04030903 66
    0x30b2613000c83c11082d1a0340241a00040139500c100d20411078203c102d0000b10301100c1500c9565413000c000941840822119070142908500c3c1102d51b0040b40d51110020300440155042d6600504c1c280e590f8020074000e508040c401c0b032480510689050981500c2c15070005d1030788007010b07508103483c07038410101003510380300341e00700e0959940005515801e031644010501014104e145100d012510080031451582003d52000f20201600c070064103d41e841c0100b8086100c1c60740c0412502a540d5500b1f60380702212a00f5040040e40c0681408246503052418161400405054000070b21200780807418045500c1407400040e900d05881c101c1d00c4000c0b00000c40d4080c1084044611141426184043c914036641001000c07140200028020aa51408038069191040e00c0c0036000220781080113000c00c00b51315104204031603034a0008800da01945101c0c0086c0c02c0000388200d07100096080c840c4580e40d048048005c071090b6140d0044600b8156800741c22100d103880020101d481c0c40d000004024200c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 944641816 1250 944640566 944640589
    0x30c0507050105011d06010e0112110f0412050f1902010c02010302040e0a0e0c040c05090f03150406020304020301051015121107060902040e0d052d0a110114160806 72
    0x303002440f40307507114040d185046152a146412640c040000500e0710343c030030f50304d181c2e504006844211080894000d10406810310b10b901c035103000d10800c084207030700b40c48900038002000ca244841001c4012850f02d54100b50001107c1c4405911060314009502a1868582201542420701502c0f004482c40107170064003450344440d03503035808e090070043d41c01c2c7c0c6038000080701c582e28010354040201090410003101e18041111001400c00e201d90206420580b540b4001c0e940020120381c2503041c5101000001481210221000382e004818007046003006d018403174018440034840d118641c1081010088001c0c0e1105250810203503002d02141016664800d008020240241e90f03919407250412102070015400201c0c0203d25060710445000e10102d901d080f1489155030b00e43c030b444000171500554042c44809002002e2400e12a0f041e40040e510043c4140f28a40d1115044582c1c044240307400c6664404140c11450ba55008101d011b441e8075141844101c05424190f4880d03c039640401d5081101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 944643066 1250 944641816 944641823
    0x1602011401060f090603051504150504092301090b0a090c0302030105180f2107140a150e0c09061c05060f191503030e030109061b020c01020616030c0507 67
    0x4140002c00d01603800854a030781005540c4a00b402150760300e03030840807114100c4e0050754404808080e5003441ca0650042550204480585241275407141c00090441d00c0b0002c080b00e048504850781034840b01400b0030801b00340c507440d0082296440c940c641c0c2c202d100e0000d01051115a845120b481008802c6070310380c01864000c1d00800c40341c5425030401c003008800001c0c00c2070707500c2004002c0882c503030001860b0380d96500484910704105488003007246240c2010400711b5850041d0902024900020405101700c179010f1a003280026262004040c02c03a00c02020104803900105206141d5440b440215038115200383c81034101d90001a45980c143d0350581001491402803109008509214107442c5009036036507106d6804803009400603900b00c9941c1008580f903400c50b0402000070038004c041e802c0100201900200d4040c0c66551000c04843c0c02d172540300386c0e554648008624a03507041060b001e14980c280010007a038100348462070b0448080c2ca0030b1008154035035009840651164054900d851792 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 944644316 1250 944643066 944643101
    0xf0e0a0905070305011d031603050c150907030614060901031403070c032111121309020a02010e070501030c080a05090703050313031b03080703030515030d0e03070e0f160201 76
    0x1204d00c0c04034040c3c405140f403c5d0360180b40080849813180044125001d03180b200d00603804400c20b80da82a180d0f41c11060848520303000d1110851366460800b44180d01c9078510b00f02030880039045140c001c1c101c0701d132088020b0f81030719400100800307922800502e5064a80142c15018001b190000340740c81c41c401d0480040101d000702c1c6001042140c0c44c5003058540101451050800651a1044a07413806201c0c54210507803000c40b1980710100701c0c500916a01c0440c0706264541a2290003401c241c0c0e029148240042c1c0d51008941500070b801c0c446100585030901c1c041c081141800c20040102101400050f00f89907108041b0304180c1c030402c00301c1d0045a02c40b050340e8454100c48040c2c0d1018169100a0780d181c2400480d5440c04c0980b07110b00f80960b0391041503641040c0c5651001ca0080c103008000c00ca61056582c0e0500280d03800b084005075a4003c1d0382c90780c81d80c1139158203040c2025420b83c0000c1044c1c50243c144010118903c002660040d442a10386a507450700c10720403800761103150134100c400e11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 944645566 1250 944644316 944644319
    0xd0c140f010605090c1e0c0102090a0b0d05151e0f1c06111e030a2d141b0a05090a03060603030f0c020a05010c03020c03061017070f0e0a090507 63
    0x3103064000b10b04071a400c891012980d071700e0301c4c50b84030180b080c07520900345400b90506914140b007041c00a071040511940c00141004880d00c0032850f4251a50043c90103034401080e099000d5644d800703050340c0220408040003881c01d400022544802c05005543e1002c141202030b07803016290000300d1880300c0c3c40244660500c4203403038a13140c5040c4c00700302d0a0b9111410000c039160703c4150b50040f280d688218061502108100141041e2503070030241644801d241c03692207007000760060f00d500c1c032401c140071100e482503068820550001ca13080031407401c1800801c07504219001e0007400010b0800c00d81c0509040c2c1e201104481140c203071080d5000b20790301019884000c000e002d031030b0344900d050300c0c46500c0f900d5020b101050192a1b4142d0701034001d6004220400502285d4861081d400300f2317500c00e00407100c61212860001c0e0504000b110f80506510088004010141c40c410035100c280c1010b0021349070f09802e14042c00d035880c0c0329004000101c00343c900818020080c40c0d02900a80d82c10400750b605d140d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 944646816 1250 944645566 944645593
    0x11b060f0c1812050a0b0603210c0705030f030313210c12020115150306090216050c09010602030d021827100f1203030e06090d0f0503090d0c14 63
    0x2e400c25488401c590445090120703246440d850901210f940020080407000380e103076a40d003000d0030002c07d416094002c40d460800c49810b400745481c001e0b29403290003902c07501d002d980b40385054144d62165100c3e51010343c07802030f144d0002c41226003142c003140300da40001c45281013850b00c141e6100d200039042001c51802640e41c55106e5500c900c0039106403640c0e4241c140d240001c81c20388086200e41c10140d08980020000f00010105407010913000d0b040c0800c8140e0344907001c1040b0b80080062480200c0c2e0402d29004200040c8807411801000310303811145941044002944c0b4050441e08000302503001410407540b81d5800809a039000e0000e00005c1d60350300c11400d010b00c04280b050940100185640072850f5031b0040700c045c900392109568400b00041c1341c003d20802c130000d504015001d15a0b9000d209104d08003c1c007a052054090300e008003440042d40200400741035234201755030208a42481800b2701b4150104050507884903600e40750440d22000e040c80300d18008200c0d0303141043d216240018070746 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 944648066 1250 944646816 944646827
    0x15040b0108160e16090b0f03010810050f04080a090f290c1906090b130506010501030902130e0f1c090807030b0105011d0301140a0f0902011b060f0c 65
    0x1a107900409a03100c001c48000c100035105628010260012010000203c1641c0b0355480502c0c01e1026160100c0b8180d41c03840c80c01080c1e8801034000131442000001171049a208004500043d000c802d001c11903031070480d0314454202000380008000c45400a52070481c0e070311031802c4102820700c0c4213510000550b41c1d16820442030145111403828100403e0680300348900c0e03002d44001003604009003007a18020044541c0f05801c00c4000c4401d1580d80c1d4911003c10110704229218002e6a0050907441e460740c1461440c3c0241680064101402c144040300140c681c141400103c5c2d66044c8041800d8074142034580c205410034003607818074401d03501300c049a0141c94607056080d091079141c018000d0345071542c10780c8504060002902c540000001040954403541507903240801041041045c0300c440000242580c0d03840d10040f400e0840130080c440c0c9004503106501c0c80340a0507038200040d0350301e540040c0100120f80580a1726500317000c9242c2c00d110194000d51503a000f14001089083ca07000c0003c0e20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 944649316 1250 944648066 944648069
    0xa020d140a060c260105060a0f03021b1e0a082502040c051b0715050c0a291321030f240506030912070c0b1201090b06040608060402070515040b01 64
    0x246101407044d1400c01202d0784500a0584802900c10b1785070042608040d1031200a8480358003c00d5420420300c140304140000d6584002c40b100302604c0200c1c100342001c205400318040c484201d0300500140e800041210003110360620150101020704d514500c1024011560a00c0180d0040e0402115902081d4450018111030076018159218102c261a10b160b0fa5565030080c0810002c0401032004d030107001d0f40c0540414003190303040768104262950303140030820b0120300708200301c41e0801c80c0d001b160104410260b405510200c490410040ca40c0f2022001e41d4003003003100319024500d00200b1402c1c820b801a030074512501c0c0050010003c4008a21070002d0315100e500002e921219010a9911b04038007168007406145005005c4d0494101c1180803550202c08200c0c0c000e40485030000c0c0441c00d800145c94a0508180380b40c01c5985001410002e5458030142c0c81e1084100b00014041c03681c001c00000d4003d071007940c005813640042d25040d841e0001052800c006410124100010010075611950 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 944650566 1250 944649316 944649347
    0x10050603061005030c13060312031b0e181023120f070e0c0d1d10020c1504290a0b010206070c03052115120a020d140a060c 54
    0x84003950b44818980c0e00d0303541405075a5140c0c116044120755072510340808010710102c450002140c0d656540c0b4412034103690010640807d0b100e81c2244419102020021070041d00d41c01c010805219203030005021009512228059400f410080fa20040302c0402140242143d075400c1c2c80c0312030559a60070352400d07140d5002403043c03140c60b40d4604000b20106000c5048849a001882d074681803180b9480302c00030040408030001c8050000380c003480641e005030001c00000340155100b1351203406080303040a040704c00d01551240100910b008401c400500b080702c1034140c0074820201d44451404068200c44815955030014140402e804c141c40d80300003080c003508015500f0080e410300003006a80383d00c3c040b200d400108010300600070220340904001d00d01d440e42880c5400e07110f400008480c0c401c12007610a50b003600c551543c026a070f0700384115540c0200042500a0140412540c0052545980b6400040c90245003521485070071100b08000480d555202c0760901c104e0610300002004070b00b4251080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 944651816 1250 944650566 944650573
    0x50717070522030c15030b1e013b0303070204021902071205031207050c100e0c0a080c0d08041805060103050c0c1213121208010e19090c0810050603 65
    0x240c4100460b0765110048a074451181c0132120714102c003034403030b402100c0c3c030050a150311030310070030841d44da05a4076032281d100c04152101000c01c10000109080c041011944101980c2581d1803140840f00084400c1000340c00200d1145841d1179000c6800e50103101d00094106001103401d000903095051103241d0905640d00301c41183d5a542841c4040c034003070340400f83c0950403c00204510214030007006601220500b4890702e04140240c800d80703015044070a04a9403603690b1254940d4401c00c0c4000e8555582c22550f101c1098140001d660300d8045455105e8172500011100200308150002518010072541c090110103940701081d06019040443d4a140002e14040028030307034a12030710513507090104401c018203d010ac070014410b40d1340c0c80000005100749201400003000c450741242c40e08014801c0219501c8695118000340c165031040e000030680751395107400c1088006503140d403004400501480801e40c8126410500c0d820607942c0c000364031a008041c6604260a880c0d081540142c4054048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 944653066 1250 944651816 944651857
    0xa0b12070e1609120201051b060f161d0a08030a021c050708030a09020402040503010905101112070e011e030504050d020c18221b06080106050a030507170705 69
    0x200c0c40b01d125828050300110390001c10500c103e050907130036255214818107105240011300c070140d40c0040d402c00c4d003401c01a40401c0800180b88504c0a420f034000e0200d000e0142e40000040c6d000d0270f00343c03000221482404142c0d00f00c80c09039448070000c10050042005681d80c03400c0000000313495045040100c4210704811555140d12480b590403550181e13042000315041d0385034049110050710641c142641d10580074032000c50305030b400388140c02d103191158009000a804116101c400da500c924a842c0d0350345418401074441e0003590302440d5100a103450b02d50071207104180144d41c000714002c0030648120706040d050500a0f0140c2c04030740151700810858401c900461000c03a51406a1140d16801180b60f000c03e61040d006501c0a40d0000c00000c058000412030985031203602c1e02a0009071100742121070003e482001c050040005440c01340b4280000b0b60418030003030164401d5048280c00c25a0b42c10004240701d00c07600a5201c1040485034030380850406001c000c01c65007000008880c2c40e106210b5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 944654316 1250 944653066 944653081
    0x4201207080601050703031a1302041a120c0d090f030f1209030e0f15070302010504020108181504061407050903070b03010e01120507080312010f0905071202030a0b12070e 75
    0x2050b200c0c0030140e48491030326004d950110060180c0200d6601124010300c1190240c0d40d803800c0c42c4000c90f0b5540401038580b0328043c4900428588001e260304030100c04c0009541030070581000d9070b03200c101d8008ae5503981700c42006080007441b000c0c0e4007a21070355441c07081d082015400071220003912919a40c2407078291040c03008604641d1803000040100d400120108070301c0c14441d040410014004280407161000c0203a000c45a0f40704010880c0140d40d1a4108411983c1085585070408083c001c0c900c090ba4640c0715096688440b1011003082d00c043c0340014007004525013028030b01c1340e04142c40c0a240e0900820180441d004281e4052190141c0e98010070641d1a0400f43c9040300c2e40420141d20a92038540b045e05941446070b015101c5004c1c00d14007140310a03080008012040b03048440404d95071505100c0da48002141c0c001120050501c4c0622180b6a8880e000516101d1131000041c0c1c1c0c3d4542c200d00600a00740c401004d80c004500c5400706003455001f2400384200ca884400b100c074203946889 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 944655566 1250 944654316 944654327
    0x30d39031b020a0303050c09030604080301050108011217090d12020109112d0604212f010e06090a1233020706060b04031101090803130b0904201207 65
    0x1041e180050380401d1580d00400d201c0d80080da00b20300d0b01c0310218a041c00603030119007030003030485056809000000040042d5680041070b076004101349c02d0895180c00c015564401001003040c2e0b0019004d1020030800c40d0b603a03810360440015a84120000340880810001a020f410202c2086d03030401c031030010001c01410800841c003c0c403160941400f5a29420242400c1c407038100d8401d1b160030800070320000c1001c960002003002d800300d110300b104204030800d01c0d2407040d02100d071a107010503180040c3c85044d0301010301400080a103090031b00c0518018400042aa01d00590030762a43c8a81070000000c1c592283c0310f0840d1142d801600442c100409100d1000c8840c2141000c4611009a405454480c00100d030302170018144900c90101700d40e42d4817a0040225001604295650210302e900e881030b540e04228104010007100002d10f0130403001d124010a224154032811092200020b41801203079903948c4040c000d1455519031142680816450200c1900000c2c0d41400d400c0d2500082428a030184 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 944656816 1250 944655566 944655611
    0xf2609070b09180901090f0b0103151e0b03011b03020d0e030405030c0108181516090e060d02010c12030608120921010e07060f020709020c030d3903 65
    0x3d0801201e0100c0ea02da00344a00304000c02e44400c2e035688100c0341000400c43c81081000340c1c0162040e07026541141820340400715a04c114207040c81c2350400010505840114003e56801e50400000f48a100000428050b226038682c5850b180d9920004000e581c1c0c060340a060aa01080703020400140c8458a080c4d0300d110b10301403240e0540c003101c090140c540c40b914034581e00c692100080c10740c3d100c115070010300d070071080100c00d0f545107014800c004485d0079041240450400c5071400c0c1ea10185004060041c605000d481503000b0307402e01d0031120959000708030040b900c6130300418064902040e00e000600401f1079001c6c10603140208408641c4881c000c0050b00d03442a8014010420f124801095080b4200341003001d5440307548400c0050503500003840f0b0395000b0004c94483d007060641c40a4000d003850100e0f00701002841c8107001c45218454004140c0e01d0754030f02c0140000305240104101c00ca403038041201c00258550400d90401801c041c03e90410017640d01d51000e11003440b00780100b10000c1d41a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 944658066 1250 944656816 944656819
    0x30804090209060d060603060510030902180705130b03010524040909060603021002060604151212030e06180d0c1a07033e04150f2609070b09 62
    0x1400180318205440d401401180d100030040f929110010711540d09441082c0d0142d40804d80d11201040141072107000d04035414000d2a04202081d5650300040c411809103611604d40b0803110000b5081b1402130084401d6444003c20b0441c0003070f0303645082c140e140c1c401d01a150007103492a000184190a8101c0307017507500802d000b000c1c1401c1c102915a0000c041c91001a00c1e12621114000050f27100c5400300c08407400e003540540481e10f4010700384030a681c415640c521034500794810030044c00c01007146900d0f00d15802807160118905001c021400340880c02c6600c0d4082c0502c6040c0441c0910803c4580314401050301600c0c1020b112220655010440300e02c042e281070b104031000320002d04888107040d403102460400103466905010094650700c00e500700040c40c40080d02c40c5c881e6000040c61000240c3c10b8240211b8030302400d00030030002c8010300200396424815801301c0b0482c0c140c0202d1420060105080a0f40b1107440c0d604060300007c80190b0703078005140541c2e240401d400c0d1f036207000c40344072100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 944659316 1250 944658066 944658083
    0xc060503040c090207020307091e1401050d080f09040608061803090a05010c0201030f150e150d030516051204030b0a0603051b060d1d0f0a0c090905250f060903 70
    0x240543d0880607501402040b640746c00760400c0420546124032407540280d1f81102c43d02d240c89401450502203880314400540c6c8880020300401482d41d030120b040704050b500c6400141c8072558510f01202501420301d2082c0e125041613800f00301e103800010014410885a18003403900c1051035030294580c80790900103034015071940c0c41070100b940541c1c84000d14920604d400590504048040004c480d44c00802c07401994281e0001c00c0f4801a044e001034100760640b450b18000b83c1d903840015001c201808004081c0b15000c501540441c5100c03c0342030a4036040302c00d0340c005050309004044d41d40e0240c0011691003001740045111007000b44101015254050002c04c03145448000d01295003c9404486a001908200080417036105009003851082c51120802c0d1480306580e0361070400b0200340202c1520303800b03443d5080118811465210880311084030024814415082140c10805c2004078881400d40c031700c17400c942c114001c480c028222603500013418030003074944504507614a01480041d060380c2c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 944660566 1250 944659316 944659319
    0x7030f031b0b0c0c0a121d180a09150f05040606060216090f1d0709061a0306090703090f05060108010c050702061801021e0c01080a140411011413030c060503040c 71
    0x1a0a9001003400380e08400c00c8501c0c5c2c5d840c0d41d45412118403075100f0500090905504503003091a4405007001404088030718010110300e00701c2005d140303040201110102c50b01e9507840d4050140301c00d8801c000007103111003444442c0b0654042800340c58140e808846c00d0f031403c40001180c40c03005c108409503207598002c0c1c3d0003071440c0c40018009019501c890700c0c0c580c0d40d56024265407900c244078070092003654102424170315180000300c4c003c68440368040c2c404640f554443c5242cdc0c3d40f15070304070380c0d000e8400c44405603035490302c00b8120010541b848009041c400d04181c524144140000d0f40e03412583c0040c000d206204034208201c030140104940290488030500102002e1528288071405000042c41103e004060320b1407402d40e0720048600082042e000301500c600a96070000840d5408208080300f400b218800744200701303d080e002007010301070414003000a00d40303a200c0c425214107240c2c1c03810b04c1c5032a001e40740000904070000d844101c42c84c0e060160005001405181900d00c142d802511a01d00030b0f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 944661816 1250 944660566 944660581
    0x110c0601060207180b092e0602151503030403142103060a081b0f0301110a0801030c050a050d06150506040f06081e0624040e1603090510020a09030507030f031b0b 71
    0x810441620019800c80d440351faa141050880920011b06450340244100718000c01c490040035005810000e040305101d00c1141ca68030000700310740c100c9134054041a052040c00b0041800c25090f85c1307a035003101c09510010242900e8081c05140600340c2110300030412a91a903c1d15560aaa65941c450312400d400340d00c0350b1850580c0011101d040054008542d0100d18203010030749034090b00d01c06003ca90380e10014003c0c0701c0000b408a01912040c2e80c0e414005050600140000740304000061005440c4d1126078510348421079848002c22004d00402d445503100c2080d80f4002c80d0a02400001035004030019000c041079010422920310104052901a11810203000c00c01c1002e50000038210129040c4403031490900340108002c01c40c0309000c4602c0d00b0060f1035100d000e80d01d80302c0c0c03108160030300f005140400d80c0032810303000e9119a141b00590302c2d0500e40d02529000c085038400f900328000c0c00d030b000081c40a0071002c000c20a1083c1d032480392204e948000e280803021010320150040d511940084d0300c9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 944663066 1250 944661816 944661841
    0x13052107120602040b0403060c0206090a05060f0a1b05040812090a1a1b0c0f010e0918010f060b030a06050901032111030d0b0102120a080a110c0601060207180b09 71
    0x40c01c0c01440054136041d00ea050030034103035105070700440b5041e40d542c40c80c540d941c0d07041c80001d81109450000d80402581600d40c1907031940080c000e9000c6240c1580403515103140d0350301c05e00b50303840819210b21602c0c2e0101c2e00503180e50442d116261080c003e10843c120310180500480b400b901c00141048912400e00c8640c10101d1107040f0b4802004c1000c00c019030001404006071402449240002d00a0244c034202740034841002c00c00d801e041c0700d01c40504610a690b070150a0781d0019a10b64010441f601410781c4038007511840104110f800d05d00040810a020b80800a5216118403071042c000706990b40706001c20620244005020b2249946e90410543c1c00b0f05e00801c8040a40c1c42c114400300c5a130089141141d01024041ca0510341d1002000200c5d40c06201001c01003202d07440242c10211741100241850000034052101d55070fa54141e44080f08450301624016003c5604a07030700c0d0740c0c49410295032205c190040028103002d04610400c410100e0051210a480103401400c01c8d45400c40b0f20741e00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 944664316 1250 944663066 944663099
    0xc060d0902060f1803010b01090b0a320301080601050105030105030a06020307091a1c02093d0518040218090601030e2a03030705060705030c04080313052107 69
    0x910082c10804080707034086240c080c01150184951112400307049104041c2121150090705041c00540c0b0300400150001b1016611910300d41d050011700b0000c400c48d5981d0b08090031820064840201101620040c010806141130729000d0701104c2050f40ca034401920303240002d00c2000d80c564809108500002c1458000d10307000901400e01e81404d60b2140448030308901010410000034001060031300000407083c042c4121402144001c51811003101c0c04178040d000b0781e015900d4807420f00300145003003201e000a5144000245005e030307000705904150052290740042d0500182e61034081003140c403071409100700c40c03031416001c3d03003940c045422005210204500900b0541415070301c076541c10755044280704d0364002c0151120040002074402c1003d040c3ca021449903903019a10038008800002e80001c0c245030007007000d09150782c0f40d07035810440000c0c3c0d10558000350100d000204030343c050701c050441c4100964604917141060300d40c85d00d00500d1902003a03558141c0ba139202200400c0700b84d01c0b02c080d045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 944665566 1250 944664316 944664319
    0x151005040e180d0306031104091a0a05040309450903210504050303040b061504120c171c0c02060408060117070f0308090a08010c1206080c060d0902 65
    0x282429940c1000c40d021040071100d0250b04801c20911520248042c00901c00c41040c0781000c00030181591100c0d90840c84401000d030041d99074070b0325407091210b60307881000056a000001c9040303191600d03000b0040c0109603001c40c04900c280d5800300d0710303141d262460395480d0341003c8081c54011b1201c002d42c884a40880201018140c41d0016200c074001030702a0460440c041c1c3c540030a400801000b20f101041341220610301103240c14244000244088110394025400c402c1c404180d80328180020030726145552140b007003c00c002400035413a850900041c403114054407401642555418004104075011903281074a9007103080181d44121803c956200845807500e0099460003503503010a00d036030711580008400d680008010440c40c04901400d580c010080405400d0b00c40c034064101d1110605400010001000801c2c2c0703038030949800e5a410002c2046100030b1004101c20100642800c0c0103d801070b5400d81084000b0524143c0040c0305010b40101514042c5460b41c0070041000801c1425400c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 944666816 1250 944665566 944665577
    0x11d0c0d05100b0f0d03110f010213090f141006020c010c0209071d030d051201060201090c06081905010b1b0d0f1b06020f0d1802060a0804061104080c0909061510 71
    0x8144d161603000030030440074880d45071014074800178000685002071182518404ea07004108a21017a0101215402182c103a81070109950301c00c03040c000c2c02b9164005034a00d01c4100e0000700b100461012801c0002c50b18940c00740d501d810201001103490100444019400266040c003007501d07288200c0b04415142040d103000c400e20301d01034000900f498180020980021404550382034041b42001d502d900600d5140020041003207075a4482610840364801c241c148144c8a0024141441e40310320725081c4c0c0c0100034100015a100e41c0044000d402100700040382c140a1032100524079400601812480c1007603d8441a0084d00a0704840d00c52446412118280140c2204000203980d400508a85c40d5100c02540d1a980700104000c22504207042c401c803a510109070030005030308c41c0f504541180c0b4107468941d045541e81c0c2060400741c0306031900c01410640005002921010104018902c02e0701180d8001e016110304c805995903290030380300707100b01000c010030102a5140134042e47c0300c2603c250a11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 944668066 1250 944666816 944666839
    0xf1b020120010b19121203091e1a0105061c0b06040311181e06031527010b060a0e0d0c0803040e010e07091a0408011d0c0d05100b 57
    0x15810000004000003669039140d120b00750007858042c0d102180fa040300c141c0720b4140d52901c0004000c064203000c0141186c01c01a405041e0a0300c0b80c1c2205000e0b03a04003104685d041d881e18440603c00d001c0c6601a01d24410004051000081100c40c0d00c0c12600001c1295042500348049050038a51404c2685030040d5240c04404464407000301130401107014103501d03008560400d0500196442c842c1300300307288909032800c0003684490301c00a2200c5080e2409070070310039610756010900d8090458289001010010108220007141480d229214084021520b00074165031000e0360a031007048555503409002881780c070039240e02c111a6003503100310040403d00408075540320b03140100c2c01070300108226000000c3c2408212441c03000d16004001320300e000345c0b040c64a0304c0e00810086040c06144220030000c11a0191a1501029140501403440081101ea0a4001400315620003000040381500503001030914a20349020000300443d0404050311084060440c074000501005804580c04011181ca = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 944669316 1250 944668066 944668097
    0xa0e060109090f0b010e0904030c030c1e0b070e03030c0a1b031a0411120c010e060c031803190510020903030d050118140c1204080c0102031f060f1b0201 67
    0x42550381c00c032010300003a1403912100014080c00c4c04081847c096003000c428000041d502242c4e880d00103400d8038080d484911540341c03a00b80800c0030466000c18180322440c0f5001d01c5031200e9480e0180502e503c0b40d141e4444004141a2240a1010b00740700c55000780d1014800f1600b00320100c5c0d4a8003140400b034685c661651744101c59115040404c50103644071008010400042c0c0f9545090f4003c1191254140e41c076416960760394040e400c40490401040303400741403003901c414003070f2041c034028002517030b07210140c0044200b603038404e480a45111744031700c5040b52010b075550080000e4950704030f809801407081c40a0b484020390f0010300501e030540b100b00242000e45205204035400303402e0500e44840c410700d00c0c958204c2030b21b5010401e41d0140c21144140131102c10300604580f001ea603211920b208030f55030390900302c06074014004204000d500000401c00c5401c0c1c5025030800c14074074a0058081e5544a2100701c40c07011213010054080392543c010302c480b66010b805000101b030b20524010031031010715039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 944670566 1250 944669316 944669321
    0x4140a091506080114060405131e240f12050304120b0708090c0108070e1207060e0307090612061109033306090c03130803072c0a0e06010909 62
    0x6003440c00e641e01c08007090105990040c0614010102015406401140907001030044e01c04c603c01c8911400c00116030360b01000302504990320202c943c040341844110451900d60141100400004000a003c101038420030280758083c0180c03205855504002d40c20503001012032b02451714160f0b486e04c8203001c0001c000d140104030b0000188074146900315404c007104040d024007006040c0b00b00c50382012a5142d00c0f640d0002800e039014806241004103550100041a0b80341c0105030a40c03a28080e904011038040d41000780040d21080035001c54942581d24000501102d00340c0c00340c5205000c03080044400310b1041d0304000c81954901c1d400c1c5141c0b40c20080002e1408030300081001e48030444945000a1241030a4042095080f8000010f5a0300d05180002c01700100104031020251022002c80d0725901c8090b01300070000e0780405550761b80c1c00d080b034003d000e005022844400c100c241c40f201480307414095255040600b0301400260f141130422445d03400f8220018106810041e40e04400030f040c0d100c0d030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 944671816 1250 944670566 944670581
    0x210050c06070e2b022407050d020607110c060912010c09180e03031b040b0c0a0b180d0c170706090b070c0b0103060f02091002011b090b04140a09 64
    0x5480380f0003440240000d02c0f4004000200d0741c1c0b218500e00c00400190344e210f0204c6804158101d07411401d50074082906142c16020000301d04400201286040c01c0100004150b8414040c5808803101640c84c0d8008582c0c400240380b000d94181c10140380e801c06802c0c41c0e405466441002043c0c04d85904900140a003100e084d244188001000440100324000c01c000310044503414030807040c0f02c3e0442032040d031036591101034540c51052998090f10000c42650304203845c06880c2020405549900c050034080d0754a40c410816195054814040b6a0030140c0003800110305102601802c5803280e6548251030040b40c407441034030090034203856500c0c05a515401000c46034860b1800152550203030404106011008220800388129020f4150105403444016411641e2020f070225064442001300c4001c6e008180d903041d00b29201080f50401542c040d004200c41804245001d81000740811301140d0282d61442210702028003080141300c0407848060b5514214805030000d0310309551400400101d45d0b12 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 944673066 1250 944671816 944671831
    0x910021e030f100509071d06070203070303091404021614070f080708120306030a0206281707020d1d150307051315021c030b04090507050a1e030210050c06 68
    0xa80421500098202440740544015200e603035881c40c00a901500c4800044000c7d204800e444d01340082560300d0400705d40c095603015041d212042d55914001c0c044c4500c50007a840754405c120040942c0703083c80d200340e841da034000d5599400300f69060b07240c10009102d40d80d64540d16009200010900003c00744483c0000c101c1c0d4002810140c1c503255182d4142401045c0a8030550401c00900036030383c1e030006641c805160122805541c074111021040d608031444000c0074012200030040b140d925400050b0300b1515089c41144101c1c0da076981d00201e072280c01004e501e00c0429107600a0981307509200c10045e880d108060040d4585403e6812014a980c100326032a20024100140b80e80700c01003020001c40042c21003640e068892070340501c02a442e880d01c200e141007600040d02c1007022061094110400d200d1014104003c000c6031030130026205c00c01d40c0141c3d130140d5400300c0002105440d00107001c0004140b414140c00039802c607820801030707002c0368840c0c608202c018891404d0178803040c402a4001c911 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 944674316 1250 944673066 944673091
    0x120c11060c0c010e070f0e0705040e07020d0e040e0a0b0a060906090b01021c09090c031b021b010c031202160503160210080103051b061312020906090910021e03 70
    0x70b078203251404d560b0045012640d0f50040042040428144036004081e40d2490742000000da4440c01d084840d80260340c06844051003620a000840c3c4d0040740110002d1080d40d074100441c1510002c0c00180e032180018003400342d00003054039020030b18610643e901b00303440d208041036441d030307034901c4000340c50300f94010f42c7d9516602d1a0703c011a40c1c04120314500f584080044803282d2102c044041d14883e05446040a00390325950050360a5102e07074030225003401000340c8900300100c0c1180c025a40c40042102a00d01924030701c02082075070041d1003040e100707a8595520100242d40001d0180a90810a01038003100310b191100e0300041c10910150a03500081040030303407031220714010000890400521b4005100707000d001403000c070f040030451414482c59000780308420702e006400f10700284959404a40c4008020f40003090443c45421503514882c022121025191100382c100208800c00351480380007136120b4101154000940e0b00030302440701c4070348a013103c1c4445154500e81550300888481c00c1000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 944675566 1250 944674316 944674327
    0xc0d030204051e030703032a0308060102010c0504080a08180402040e10090204180c1701090207030e0f01050909130b13050123071107030c0f2301120c11060c 69
    0x2400c0214811000e504080241e40e03c48100c046500c580b45404090104901402070f460031080f1003c1c1441c00002d0f141d0b009955003240e090040c0002c80039603104d4019401c0688174200c0c584a481078905580c4220068080c04c001940c6040c80365101c200344649040340c01d405901181d41c0ca10190008115000348070030301c0c1c906600c42c610003c01031f4002c036000c18818072050040c3c0e424405c0b4404c2c08940043d00085842e00d00c03000361040e0301140181d1862000c14000851410034540140000034442d4484c110a005200100f109100c4040030980c0050000d1112031181c3c40d080322a0354000407607a916419801840d1540d944503401201d51902841e0804040d40800c1001d00c01c034001014400004160521140002c1d03030300322400f9200004100016200600e41c000030b0000000440e40200d0000d12155501404591045907214218403050845001c0020407201d076240e0400d0740050751802c04031234003d588480281319001010041100341e01e250101d18204000300f40c081c4460b03800c17168481 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 944676816 1250 944675566 944675569
    0x106170a140601060e01050919080c12070e0609250c120c0f170c0f07090b060f0a0513150810050a12060507020a05030a171315050402060c0d03020405 66
    0x9038071201c400308072a4080c8004114040d4408011464184240380c015507d4144000092050111075100341c10003450070400950842c0000d00031071201c1e030594040401d400050b241544460843c03245000c0a0f2030000041c14501e008031407154403040701c240c1c1c1005200e02d400800c00c08540380e040b03040420480c2141c0001d0000d03130b82d40c0e004100401e1801014044640e030717805946810440b0004c15000c000704e6028800c04102c0b081c1d80302c409000084907a001411141150350320014440e020840f0311f855102c80090410000b200e40c1d05205c1001186442d19265044a03254409503c0e919002220030010914468050101d088459680c1e52220103040418090428880e80d074002d07031140308510000c1200402e140c0402a0b815000000080c5583c0c0301641607052140100b07009000f40000284407d8150b08540700b03014078050380103052040d035250202c41c40a00d102000160034110044181608407000e038005a0340700f131000d0400d5044c50003400710949840206203443e008280c0125081c40349 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 944678066 1250 944676816 944676833
    0x70f080301030b0c19030e010f11120a02040b03161b050607030c090f05010302132402070e13060c09050a08010b0f040b0d030507030306030807080d1416110106170a 72
    0x2083c031407080c0d103142c0040e48040c1071a00900d40c2003101411f4480341030300c007030000c00e40c0080c0c05107103117080522081503184560030480d408091114401202500440d040e400944280c07410703100130711074030b500d56101d0858a590000c2d9008041003081541c0e10403076008035800c5200c4180a00c944000c120b542402c07403020b4240e40c41c01d08950100400c403c13040241015a40c000c00c101e0343d0030f00700140d80e24028400c070041c042c41034109407801105c030f9128400c22481c00075040054685c40e0300351040c041e04e98500c40c02011046c0c079003902004400d04088082201c035031114446d0000f80c00c0c41c0d040c40396500040740001505600080407079648040280840c1402861104e030340004860402180c6480b4000402801804101800304000420074104040c0a54440006140c11284050704e4030f405245c00c1200f9440359181004e014209202c070308010503036041d03c1c1d000b0401c1410101c6d00c0b1500600482d001ca1f01524407695642d2582000a005024042c0380415030704d030400a00480310050802c5400d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 944679316 1250 944678066 944678071
    0xa0b03280e2509021831050f04060c021f050105040e0f06040b190e0c13180816020a290a02070e070302210709091107020f010203070f080301030b 64
    0x81c002d10707074424410b40140c80c0b2610140c030304001005889480600c031501803140410012600b000c100000000140d205d1591040d0b140c61001e000d03ea4204a220420103a8006031001c0e0780300c0c0003581c0481c00044c4a0b4118200030009031044950143c2c0c920803c00040701030414041601d555580144070070308060040040603c0d403d030040c00310b8182030413115036510300280054800c2c0740304008180901e00e0702018510341500d02000380400d0800071041c90701c1d02c069010591003554149125520607410340150810a8113240c080040c082c1152150015907102e9001850140c5004003c1001a0380741c0103240040c004025401d00040e801040405d2002811090900f0483d801e00c9000c0e80c1a03400140c5500741c0d401c500301d40c1119210410164064096230200c2c60702909a1075818a01d8a03110010a03c1000c580d1b0b280e5000c00e5540b0284011241801d0b50b83e051040d0030400e10000d403d00304030302c4141c1039062041301e00d49182601c40c06020206644200d842c008000010410702c003901c4000354 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 944680566 1250 944679316 944679343
    0x1410020703050d0203041e060606090e13060e121c0e011e0b0109090207140d05040602070e270d02010507090e04140a080c03090a0f050a0b03280e 64
    0x186800c1241d1405800c1d03008034a015401c250700000090308020b2802c4031841004440183d461203c1014035001001c0c02081c002c1500290b8240c00014002580240c10380c004d902c1c1059100152a04c0e45400c0081e02c00c1d1028410709100d6404c4140e032030361802d00105089001644036541c2c2000c054410411307616a0041503000e031303040c5541440b070394509000b5a4003000781002d0000c1d1324001080141c0398241c2c141e02a44440384041202000c1c05080706c00c580050480405880c000f00e8070180035903060090b805100010380c409407091198200441c00c3c5500030140054903848021003214a000c4900700d00d01004443d04401002d0380c010385c09006003500222a424444802ca0500850041d4079000a102810001d41c0d201103c01c0c0280500c4203041c80d43d00700f10070590301d8001c038442540e00e901580701385000f80f0386440d00103802040d45402c20262038000b00103840d150b00d40082c011154101400d6a2112040e041650354030a407000510441d4202c803510200b41c00f05144140c5027091000240603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 944681816 1250 944680566 944680571
    0xc030919030812341b12030c030e0706090e0a050112030e180a051005150904020f04090509010902040b101709190f051e03090f060909041410 62
    0x34400980500140c1c1c103904a04521200740ba0745040304d440211003502c0b0380080501d0300c0c8035100702008880d131044034103e10702d0f214111402c03007000c0d103100c0828140d04090480b251110003c80658400e030458904100c2c20301d00030452008170525503040003495441080480c00b00070042241c00c08049903142d000c1e48903002000070390700d012885201001900402020840d4170447c1c0c00c92652481406030740e0647c08442446d030351030040c02000c000e12040e01c3d5200200403800d400266441c002d000802021003502d1a01e09190a24040c00040c0d04050071380802c0f030500303200c04036003410070303200c0c180c45516090000714850f103040c01440111030002203854002d030000c00c58440ba090b004440802c48185844851201d6565030041a0030f10700c5001e0b80c08609542100c509c0c040c070051044400d0301c103005d0400c2e01c2c202c0807180660102030000d22047e14a54105002030398080c136110306034400c18407014280c01c0c0340c1110038000419a440803038040710507241da24203190070084100000c645020010204 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 944683066 1250 944681816 944681819
    0x703050705030d0f180b03090a020a080d0c06050c0712020601090f0e150a2c061509010b0703090e07050c0d09120611070b010e070e04091a1b0c030919 66
    0x810a004c40e9000e1424040c011201440e400c1c03440c0c094030020000d541c4102c0c0c0300e04041a40781d0711440f007100140d00c12500c1040101e4950004140c1c0d80520060391200c07803441d01c3d50b82c0d4110261070007e00c0c01168560502c290300104201c01d00d81609040c603036010b0041581462148802c40d1505140240c1403890021800702e174500005161100180c5025070481700d40d500000c00f000b400360318880901054001135030151101d0000d046491501504082c2d40b00341c4d544080c0e40c000c00c8090481c150340107080c200108080c1c010b03a4010200d5902a140603002c1c0d58880030083c4458105031891070000e80f0004601c020b42e00141700101160146160444045140150100c0320b40c0e03810202500643d0307504400144030700f000341201d50302d0364001040300c26076079182c00b0f01e4011603040310b84502003400140705142ea480c052080030469540145039020100301142d1441140b032000b80303856220340358044980400c0c4141005040c1443c80780004542e542290400c0c06045c490200b1a1110940e41040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 944684316 1250 944683066 944683093
    0x303071209301b09020d020703090918150b0303030f1f0303080c0c0a0c03050d14030402152a0606040e190201110a0f0809100c0506040303020306030c12070305070503 73
    0x200a6480e0f00541c1d070201100542664948000003076010404203840000d100d60401059005020000e01a440c1c015096a0720b0700440213603641c0c0c08441e9a410043c03984c0d140000c2c80020152800c2504050000d5054001c0740400d140da0f0080d182c0c1e0000c17100034070420454484868a4170aa8085c90090000e00c0c2c5ca1580c5c0680210009041044074541c0800c0d8104108170030040450f0700c0383c000305464440daa40303040c801c0d140e0121040d45070020394070121f01c18074604254101c0e805268041c2002c001081c400f940c0d0822a044a98039100800551034140d80e42041c1c2002c0707448150800000d419542021410070080380d007000090051074102c4071050180481c918140701c0201e4080c2805059008100e80360f330b00341003400744000c0059040846603c18044802c0c00780130010b00030f80b080c09100b1a8840d0035210000102001081c0340e02c08000140013078032980142d90882c00c0603040f01c1c07403d5083c0303000942a1000c01c1030392015600c0010304005203c020020280102419400b070712040c1048007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 944685566 1250 944684316 944684399
    0x4060902070507061b05032811100b0d08031e060f03060606070206041509180e2a040c0503150411040306020a021018030e0303030c04140303071209 65
    0x10400341440000c1c06401d82c62085c049245c0f440326480003d40750391710300488881088004414911002111002c103420030300e4000c20700c03c0448500c207801000e100500710650805480d10f211a82d400050b408070700400100c1d03200180d8000e8941c216825822444440f00900d0f01c00000d1000e80b241c109441d05c600b0341c2d10b001c10901e42001c2c081d0780282e81d4590a00108005218640c44101c03441c2d010055629aa40d20211582c15244c0548030009442805010300c815150022102980354008a40c00100c41c02403190f11559000c00c04009818184da5400240c104d68001102d02c001c10800800c0090040003d0050301c80706000b1241000794132000140c2c00200c0c040c90000030400d95001a4600555000b000316201d80b01844a050100400c40d011b4040585101d07001100817858602c00072005150100c160b9104412203840141024603008103401c000c800030300543c1e054041044a2004a8402032041700c1c0d0084685070010b605240c288606559010319605510034a04080240342444204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 944686816 1250 944685566 944685569
    0xb032a040b090d080705060907080307171308030f04030b0612070b0a09260624040b0d050d03050105100809120702040e0604060c0f020f030405040c1b0804030204060902070507 77
    0x5007a800d846002840205800412614000d0200304000c11007404105000602c02e1041c21500280d400c0640d44402180e540c1c06207080080c50030911000704c80c8003640c082c0c082c1600318200c151440705107503610b8289003140e100707401e04a104003000500340300340061408010b40101e0256140e03041c0c0140541907a03103600c0300f802440d0700c0c1c481c0054078681c058401c07848500500010600031045800c8180c5141c1058084100784c40c41d80070303107000070f4070036032140c00302001800c1c1341100d03d03409000600400004000200c6082d500c60324208214021502c1003080003c117a0450f2000582135050008001280c50120b5244080000354402c00c0b450480118454080301c0d210140300d612250720b440006c014001d001800400d520592040000303207c050b8005001c5014a51a40141e5114400701240c913501c00b1444070b03610394000c20041040c0e040941c408141035800c0c0c0341c441c903a1411a0700450785094406400e5800c50000315003401545070511440000b081840002c615000a958440d40c544405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 944688066 1250 944686816 944686829
    0x2601060e12100f0c0804020a0e06030f0115050307080607090902030c0903010207060f150302090402090703020915070c0b0306090a050408091003050103050606060f030c220b032a04 79
    0x42030802400d4561410742080148140103480340980d50400000040800400d10101c2030b0600c004461814007070b003661070103113401803d1416941d0030807808840480f4090052501072240c0c55200101180a200b8540c00880d07074a0018640c900d040704140c50a4140d030401052500074805101045070441020000c43d0a803c80240c0c50359503030405051540610080150554000141031003040f0b01948a0021041211000c01c05941010040000064203000080d0800012001b0401500e09042a11350003911340c6005403800c40c40101041955000b104003000c02200880c1c083e082100c4200303040c01802d40100d99509502d01140000d14032a0094000b02440e682c038030110381480f0b071000841e40c10040103803a5100039041544000c0081000740b0040e00c035802480045111841c0180c00c403050a0380d42c41d0002e09507220101c0c003825070740c004107101090340e085800c032009444495003a6001848001201c40d200e01d05469130814004000400305044280405100040f100d0007094034142c50a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 944689316 1250 944688066 944688077
    0x1b0f020f12060f0406060302092e140d0501021614011116020f0a030203061905090604030509060d0b100c03030b090103050d030c020a17070c080606090601030902061209030a260106 79
    0x4c80d4107044009002541010f908580800100011a06190307045444480b41c0400c006418048241d0070745078a0700340c02024411405117500900500e0700c1c8040000e0749004c1c000051038030360403004a400c2c076541501c00b12a841c00d04050404848001c0c441c8c0c400408010700b00c42d01d0040d00000070f1a55a80d1841d009200d001c0050383d06826460b100c8511003e0341d0b002d4129903541c104031007902020720320309080400060030403001410b00310001c9880c40c0150b83c152100d50501c9030030002c00c02c00e50031104004002654900d88a00d242e51200780d031461a05140d16460030906403802c004080e00d90f405d0105004824450040000440c0003489a03002e681d00d240000d00841d80481c102d0810020700c0004c1c05213a40d0041e10031500c07200c04001c0400f60b11032207140080d140d030780f050292203004c212450703580b0018841c000740305540281c2045000c2031000300050319198100010040c80941a1307201d1005610102d400c00395039801281c04848400c100c00186070702c10300c4440c4184180300500a0008011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 944690566 1250 944689316 944689321
    0x81608090a05010608011a01030207080f071509061a040b0d06050a06080105040809091b160809040f0905010c1b060b0102031e09010306060507050606101b0f020f12060f 74
    0x20010700c0000d552035400402400265901c41c003180c06040c030500484102c48040d0b488044560082c801c8a00c403d07840315445040441d260010603180e0441da5065440c10000783d080c009021540c03180301400c52184800280d24001c000d840300c034800495500300d006a180c100841543da848401207195264403120201e250b07940d610002000e0121540721125541c208000c0c4070420201070080c1c20001400c3d2070700001a5243c2861040c400002c0340385240d1181e08014000c05659680c2000802500407200985000e030748602040c12100c40446100010303940e03846010410100380145461061140341002d00302079070310502c02003001620f00007030507280d0750340c108480c80e4001e00649442004452016252007940c4588501710340c0504081030000c0e141ca00c0220380f07107007d41c00360380303515070040c00810303040d030700e90003441070060504040000b030101c070761103150316a40310307964030b8460a10a14041030302c64035510610404c840b00c03080c0b407807040225508090820f940064280d5100d41403941120a94 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 944691816 1250 944690566 944690581
    0x60304020f120f030409050f0609130f085403160f0602010c0f05070f11131424211b1320071b090516081608 48
    0xd05802e80c0101d49001da00102c41400d000130026001b143c0c0e0605003409180c1d10040e4010501508030b90350b560049020012840c0d0b103c035801060076040c400c05050004014cd500e44d444642c210f04041d804028021070841d440040900c1c480082c90385282c6161408a00350243c0310012090b9400c0c1c0c0310401102c8243c09403a81c0c10000e50609800620b41c0411160f100d08040c0c5011540307001d120003541c00c01013207040440c0300c0e00901c60098075176a5101e0803e8165a2221505207046405888400080810017501c1d07541a220600d56946040006502c400ca807107040e070300d81e000420790040d01c1c44156082242e02246100c60755040310032101da00812030700321541c0c03040c844054441c0d41c083c03052082800c600d010b810188406440d0458001c0510701a18020000fa05c040d00c146111100d00c042824141c05180d4003c0c0c04100d10a05424010008100c1545030b0003416070b100700ccd04181c0300c100b81301c2000c1002105840f40c1d1141e15003108540b822500c1c0d041c540c0b080040038005c201c0000d0004032803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 944693066 1250 944691816 944691829
    0x6010e070e0f100203030405071205060112061b020102041409100b0f04030f0b04060b0f01020a1202010e16060305100e04020d08090405070201060312020f100b0103060503120715050105060304020f 86
    0x850001003002c3c0c04026800c200941d039820842e001c4403144290030002c10840d00f00c00c0004840d95121005100a0f070030084200e1440c00c10003411140c054032031070481074100085641141d06220341d400161640d01c0c0559200c1100c40310039980d80920310340c40601803940661040f10040d00d114460543e6035654400310300c03105101d40d178001f61581c280c40380c200e0100300b820300d52140154041c0c10b0074030014441c40f0400040048909040d40503a100c2a03e480000d00d910f50783c486600180e00001540d00c0c1c81c0034469051420300c20320040e1411082700c0610246805114072604103030320b800184015030a050035009100c43c06000039108038403003504403080003084002c40b16081c0c00980f09100c2404c0440c0068003070903050100300c401c0780310001d01000d035502c00961381964444030402001c0e80c1e40311820307040003030100d145c01904264a6000200e80c0d520200b010108103003d1580147c0ea038200e40c20801400108403803080c4107070b82844c004000ea651041c00f5241c00c20740441c1c0c0b250785200081c001946 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 944694316 1250 944693066 944693089
    0xe0d0929180a0e06190b121f06050408150403050a03020304051e011a060a09031103100e1515010504150e0a090e060f0103050a0f15050a0c02010e06010e070e 69
    0x510022142c00031a403d191203036150b014880c1640c02e000b45107003629404400c041c250007054540d140c148100d0107078880f8440c0e11504501c1e903458800e52012400030f4106d0199481d08100007007a800a01000310b9030042056500d148001084104a0706207668010010320821180e10201a004404641403041c1801003644103004030048042c0094100b06150203444500c03004050b8269800c180300c07090038020100c54040d9001d039070b00900c0c2400c45c3d4032501310801400130207406200741d5074840d0480c0058031408008000c114024842240783c0c2040d4041950024509110728480e03207044103e59811401782e070103586822054a00031007040004a40600c840001c1541c00100c56a000031a01a190300c560415903c0c402610210f40d501c0c101a42211028800100950320105418022030f07402d00d9400049481038210750b44900220079480b040e01c0003540c07841070860383e0300e2042150b00d80901c00d90890400b1440a4000b07980350404108a5580080c204003e00090010a503000c0c1c0c1e80d180002d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 944695566 1250 944694316 944694319
    0x402070309060806030a111002120f130807060c140a0507030605060312031005040b060c100507090504090309050103020306060c0102030c0d0e030c07150e03010e0d092918 75
    0x645a925908005040600300d00c00c180115003104041402810017141003c001e5401550031320148101c00b042c0310070002c41034070768001c5001d104001c8081c1d500440c0140103030420718101075100c0c80702c41c0c2049600c603038507408000258054141085120f030440c404000035034011014504481c4041907160504c40352704030040150044450100030801d1903403000340500c005400702c1b0705020002c02c0e4200315110544000116205411040145182a070441e18a8400140526050004180b0f4403807500b001201c0000100d40c1791410002d080b030780222040010319044405002c1744c1400d44000c1c0c50342d04103008443c10182c0000020b120354460390101c3d42c040242500031507682c40c002d40c50190039003007825034007030303042c1400c2c031950211710000700382d07103c2242130000762101601c0c081281c0d084241c00020a424001100c000b070105640130b1040c50040000d074400b50608640d240c00061030308910b80c001031414407890341101060b81c94000008503101044ca5110b6403040c0c0c081403407036503400740301116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 944696816 1250 944695566 944695571
    0xd06110a030f050709051f0c02130c1706060306040911062a0703030915181202030d0206070e0108062110060605121519060f23030105090405030904 65
    0xc140c036505a009050030b1609001c10007540d10703044403c50b0001400e22820342e1080b242000b0080c070300705050400407841d0550424000340303949503021800314680c400c1d4034030503965102042d400141d0880140500f0b00450288030300300c3d18003a40091118000600110300450346c50a100e410003031080016208003900421103929204002d0000031803516400c4a00c0144100c68011a11100c00007580030a036076050303c8140c001d6090181031200380211901071401c20a058480601d0901044030141c00342c4400e10810141e04014014189440520703861b441c1190301c1003040000c103540c4000c007852000c03024680b0903417a444502c00078845103038410040550007003040849504070300005a81300c02940350b010510096560340300948050145c40a900c00c45040356002400d11007900181049440004100c01c00b6240b01e00c03240032585001f41c0042000c0303000407082c8860141c01c20388a040d412442c1c1c640d0b1181019010410040380810712445021300b13441c00114080150a00c140c40413020050f104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 944698066 1250 944696816 944696827
    0x90f020603090c19030b0403110304050a060e0415260a02190302090a1b082a030601090b0c0a060c170c03071d0f010509010203090402130f0605030f04020d0611 70
    0x107602c4000011043c0d200c4e14005840c1070340f8050100d034030301c11a50444540d414035074032610305030b41500058881030001d020401002c611562990304500103400c01c0e070303181e110340c40002c81404102d681c82c12001c50f403400012020001001650705c19542450001802c032000596903121601e810180349000354406d00380c2e4600006280001422003c0b68002c8070580655190a140c07041107420b180206101241016425185103004601d0240c0200084c41030102c03590300044542c201ca0b030105d85000b03085070000f05000c41c543c3c8c083c9204015141c02c031307103c0d03142c0301c6040680ba558120219000709030546031508017521601400c1c0200380c407851104840124a000a1240c141340e008548240201d07030008008450714a4100110701c035818040c008a42d400565801502c84c3d80025540504621082046100d180c8650028148150981f1100c0010a040c01d05651191146e60003403010003d060040102a007031143e001d5401c00d0f016150300e8222025070901d0000342c0b4601d051003002c02c000052 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 944699316 1250 944698066 944698081
    0xc02150c031213060b01050a05040e100504091101121103240303030901020705100b10200304270c0c080f040f030b09010501060f0905150d06120b0c03010f09090f020603 74
    0x329400540d00c01c020421010305d024005450900030341d040c40000810900080c0305148101c002d207500aa401294140101d0b510310029041d94101803040b1210070708607224600b036507040440c01003045000c0e00c0c140500d08210841302454080107054030801d620700a94007d004100680c4d0241605000c2c003680d617240741c06c8103024007035407004000311000c1c071a420008001b2100c0348549111614000c0161a07440d80d006011601c0d89000e4000c410070b0008501c100d0f40101c0c08200900003411a480c56000c10540b940238100040c2e03064040d00d40c128205009110f90541c0000200c0f20350350b21200d402c4d00c80350380310071011403806030703400180990307a4403603000c418441d01005840c1b261007050000d004a80e21098200e030f0140c52005680c0c08101482024850344c60881c004120400201d55504d0030001c0002e05c0b0300544103980e001c10220322604400e102800300200704c081c1d1190801f001d0078595490141c480d512010248280390280703035582040750410203c0e84400d03c1007500203120580307030704180c0e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 944700566 1250 944699316 944699341
    0x6072d030c150603081204060b03010219180602030a050705120d32150d020904030906090906050105030703020a170103140d09030803041103071a190c02150c0312 71
    0x1c1c0d081d1a8000c240041034400c1940740100e00c1030b00d502c1262242000080f01c1c080035995400ba0044898540340c00d51200e040c1c400f440640000030007008a85800c10168402400e4160190003003549400ca0540c11300801e9000000c507042543c04d8a02155101d00320b003811400c04440c3d2103541d000540008042c04000541d820050588440421620000f07a40741d0403290b910004003404443c80340168005104016140480c40788028003801210007030307a15900180c4144411501240400c2d0010740501003603501c80021005000c4c018000c000386801c000019000d400000d00c01004c02d90002a804031a0b84220b0003000b0f6004c4020007080c0380d50f10f03850140c208520151201e81d8510544404003c25403103090f501040300e0300482c0302c519540311921001e1602101f03140e616050f1150000018490240305420303010b1503415402a1f07228241101542032481e00000c10700c0402c52000c42c50f501581d106241803052040c012345642d580c040d4056aa400c0d40200103100c42031403604010070130300201c1c52 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 944701816 1250 944700566 944700587
    0xc1712090f031c0f1b0b060108070e0301090b07080f07080c07230d1b15021605060109140a0c020303191b030e010c020109030816140f0c0f0c06072d03 66
    0x1d803071741d60b440300f1490f01c010012500d8120140c4011191400315400d0b5018050071a007044039861f001e090f059800c0d0200c1c0c00c0d21040d03402124000460010443c0981d84441241d8102403030b14000600c03400c1500005152180c060202c1d4010080091031008006000304114030120401203030b1241882d41921035600c426804180001042e000c407804c160804038038036801142da03800110341d8000b003040c00001001b50001c00303130034400344c40e5201f007034001c607038100300c968000c015411004c28103201c10302800f2100341000d000c40c10441d0030001d0000e91183c0100640354041e81800c02807080145014215010303103240d84403403007c80740140c1c04450f0903038190003040e507260710350307000380490540c0103c22401c03505080d802800141042d00070603203041c1201004011400342d45071030b0011000024070240c81d588015200c640b117402c0080c2c1e03000006000d220541100c040700003d0490306e20060041999441688002481c1c0e01521541c2c0880d07440e4907030b0008e00700003807929a001152203890b019000218a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 944703066 1250 944701816 944701847
    0xc02090424020301080d140d02040f240905090a0b1527030a02061803070f0311040606051602030f0a030c050601230103020a05090d0c1712090f031c 65
    0x1c007100d100500507140212412100003070001d000740403100204940b40b01c0d0340c84c03260a60001c10000e80200c11214005040540080315141070114500126031000d64109000e815103108590b584003021030700010f002c0d04640065441c1c805941e100540100284506201d01340e20100321120200141c130b02e4000f03000a5074880d4142141400e8480800009505114074141d050f03201c81c85000044c240003018200700c5c8556820031561140520004e03041000e1074200c00102e000c059401c0041c000d9000b00e09407030110a981c100b02c0103040003002891807150341d0005400841c00c40310b001c1151410004038034070001501c1070ba54a540d007854001c01c03081b00d0040a6600340304201c00425030052201c4001c4607418035251b140d08118001d8019006500800c5041d4217000d02031000c5503503030301c1c1d0b030320003519052140d050f202101e400c1000e0440c0006050030000b9030360344104d0441d49d1084043c1c045440d8103030101d80000500c00d041000920380340380219a01e06003604d004054020030340040540460500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 944704316 1250 944703066 944703113
    0x120905060108061807050a050d020d1a1e070e01050903070e0a051e15190b03160f0504050a0b0d0209031c09120330060612110903060a0c0c020904 64
    0x820f0300c6130307555007060b4014150b0021a00d6400c0129161600181e601c8a10190542124030510b48854881c10f518070751018854000c1001c002490f003025070518406d000c1281401554280800024990828112000d050100014811202d42c2d404c00106008000f40c444041e9140703840c0d16024003400064901010b40b155544910340614150311105101e04101850400e454480c2d4007040b11008003140c003403d40d0b115000740410b818448500440c1b15044020308890b0710b0b401d00c40024034075640c2030302140c1003000a0105100d240c0d20720451030202c0c0d854000c82d58650102e442164001d10405100940c1880340e0344080d02c100744134141c04040c08074661104040b095441e10405100f866008008001440701d12401c4d444ca007500ba0a019000e40f082c0301c071202e084044091800700c1da883d40052000c6000c101e00a50003100c40d00505030306010009000b8100341c408004650f40300c0d00a8008030700310342c41d0440408914410551903440d1500200324072080d00309414070910290140c900c1150101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 944705566 1250 944704316 944704351
    0x2030c1c06140603150c0910020c0306010e0603070b21070c140d08060628180b04060e0108070c060603060209210330040302060601020d03150612090506010806 70
    0x1800c250840c401c0034040c4c050248043c52070b01040080c0001840781040d07010901011145031120b9207049403031901f83d0000d0100c951080105881d000f4142d200f0500c2580342c20400406440c0401c20500b11011010b810340c0700c07031780c0c5880410804020f009104510b81300b08104581c041e40080300704200c5014400c1c8003079216003640b10079101c075042111000403c84020116140d400c01c11700805c05004138240802441a90110f00c000c0c000d4402c00000c0014020818800c400e4101c412a50081c50845001841e26103813506c0504003284a00c0c4160600c00309400042240380500c0b012102194018000c1150548071700d0510025040710700c803180602110106600c84a00b9410904c1d10701214000a40c2810751650b6450ba0707100441501d070f990110344103000300480c0c906a5a09010390300c00c3c1c026080a2400320002481c1c0000c82c0000740c00c050500710314540301d41200d20b5070000d4810511b4450390880682d05020302800c0c4122008100740b0548000181000010458500408509240f9103032030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 944706816 1250 944705566 944705591
    0x13020d1a010f0e0d0b18120306040f0e0a080a090b040b07110d4d030c0303040f260d0903201c1b030507030210050a05120402030c1c06 59
    0x5a00d51030300d4541207000c000d00704e004100150307402c40d40a1001e104043c0071050300c0f400c0b0760030800d032000040c0c100032000c018400d8520380340c003e6900e030ba01c880900300000c400340700c0c0c00b0b039a17000d2049025082c0b010001d44100c0c80c910640080001d481c2d0030381480d989590314034080d2480e601c500030940c0d018440b41c0680e0154a080208068040d4100101d1404030007140d440c801504110f000503202030444d07502c90018005107180e16080b900070307049204200e0039000b040c58200001105a50b120f5042003000b03100c4d400c002c02c502801c0d10203d86049a07418480c54604900c1c0c041713540006800d118980c904c0c0d9100b50710560100c00d4038070900310101880340c1c1c051a82d4422111510081c0c0c804030248513840460080e240c0c595a00303000320180003140706400b003641140a091782013506c19400c900010f00c1541012101a111000c09207440740c0340c09559800100180030f505841603450100d6808201503540400482c41e28107402030a800300042c050301c81d06417401d01c90100300c030064280800075006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 944708066 1250 944706816 944706827
    0xa0204120c0602122a0f100509060601030626281a010506040e060a170f06150a030f021f050909060301060303050708070305070b010e06031501031113020d1a010f 71
    0x700d801c00e1040c0483d0140d001a1751452034582c03480c81020b204080c84a12440d40c10012804c1400400e5800540c17414060842c03410008020603180c1410705000b4100804809050070003d07141c848201610022004410182000c0103208400300012071200b600c0b10400a01001c00d030040e1046082545084000c0d020303410f084c1e002d100b1303079601c50300c248420091011a100e0040d8080c0005089803240381e120032815032421600c17a411482544190600c01042c81c0810001d07400c10301c8913012103041c1d0990800105619141d000c001e001d900703000207880c21512102d4842e03003900d60306092000441803140000300141c109104a41c03203000c0580109045007018418101540e400d40d449518011003511403a4090307000800c224104802044034001081c031040015028000355011031465080c58010589401b1400d100004512003290040002a02504000200100580e1100b412010b81044c00c0e0080c05401c0c0c200d03d090381000d82c0d21845140b0550b800540302c6098a640301c51304043c40013140d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 944709316 1250 944708066 944708077
    0x1602060703091104090503090306150a060c021c082107020c010504030b0403050c100e01050f06040515100509060c0109030216030804270f0606110a0215030a0204120c060212 76
    0x3c555a0011040ca65013429000076007003038040c0048030300d450040400302c1c0c9800342c01c40f82c0c3c944885141444044524082c0c40140c02000c4e00d240c1011180c405400040b491040940c009950640325200c2c8400c000c3c5440a6900d4414800d411140c0301003036008101e0a100d08403400030040c0100d030002d01c81507010b002900c050300d401080c0c01178a69a10703a0705440c143d00040d90380c1c00f1845101404030303041059014034005400e0400011a50b800c0c90104084030b20310152070300f40310354144000c002c0300b00b00514940c9505641291002104180d07640141e4051046105040c1c1001b8000f64010350b6142c15040381528621903801c0303400d6002c407003003900101c4210f4080144407401c100030800c0314115882103010720100c0c081404810854001a0b00200d0304000744205110b42c0700c3d2801c010035604443c8003c01c12102e03902038084004e0560004400d611200040010310300040007040f201042541541c019007401c641d0340e5040d080301e00f0001c0d100085ca10030b5000611540345020150f0203038030f00707a0b40f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 944710566 1250 944709316 944709323
    0x608160b09100c0f050d030510050117040804050a0b07020f010c080406030b03120301091a030325060f020f04090e1b0909010905060109020a0e040b0604030305070f0b160206070309 79
    0x9007054108400c216145469200d038004200c40d900030900403509001c1c40f01401441900100404030f40e1410240540303400030715100c0c1c0410b981e032040000d642c00000400204840440300c018a9030b441ca0728081c1e074002c2d6000b041d002020b40002140b4451000002c1c90601e008951182150009200444201c04100d50090100e001408100f00c014080d800c0001c40c0d200007001d460a40d44038900b0059290401da0200e8081521903115041e58030140c942c2c04d410500a802540c070340010104c0d843d42031f8500c14001c0403d00070700c91080c8203100703455010914145003e0415581e8500b6601c000040390060301542442d00d14014641304444030000b142c0301c44005e00d0070340d04911740040e010011500c50060000c0910b540300c001e19800180c003480303001c2c042c0007040030050311002925402000f07442100f8429000300c1c54004880c107982e03140e406030303001c5075414900181e503220145041142c3c402400b00041c81517100101340b04807a9001c242c84140c4440c281c0c01c0b1600e87d0754110049058502c00180075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 944711816 1250 944710566 944710589
    0x2011706010507171e04051c0221100903020d080703050405060601050a021c082205060a090309030609080406030e030703080105010f260406060e0c041412060a060816 73
    0x40001101c000642c45022504c203c0e940c00e0031040c24203008140064040e00c0c1081000103024001ea151181044240b4011800415203584455000c41d248540810361030303006142440d450079000c1c0701000360010b1001e0651060080c03030510710340603664186404154004c1802c0d800041c03800c0f0300c43e00c181d40c41545c0040003440d544d103800c001585d069001d403140c801140a240324645a125102c0042120783c901c03941e502e0705614012981094010242556541180d422100f44003c200e0014506802800c0440d00141284991605494000d030b60f03400140b00d00c1c00c0c41000d41c28408142c1c09402160019102440080b404001850700c9101d85a80240030641401c01407007154070503c0c1c0c2100400c6c107401c00d401402501000b0116502c840480c91030005813800412080007118000d08005120076402101d450400c0c01242e4443e0040740140404c1701c0700c144d0029038030390301c003819800300b90b8540741510100c0c100808141c01900c0325000d002464803031402d03641d80400f1380e104440b04031108030180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 944713066 1250 944711816 944711827
    0x606100f03020d020f031003021201020a0e0906010e03060403030b03070b040501121d0f061503060402030a0f02031608031e0310090f020405030d18240513090c0c020117060105 77
    0x281d00940100940181c4654280004501d50242400071809080024aa01c54052940c0704101d14a203d0400080e545e0340140310482559403c1503050341e103040c040301e5040e490342c1c030307800121240810002502d90501c07540c8140070925405a02c507001048058040d80c0e0b84685412040301d4a104074410240051032a8001c01d07140a26a84007040940c600286044900102100940742040041d141040d98218006000b464844950305128090341980901401d143c80e8000a840380e00e400c402402c00088074002004550b82030091070f90110325007140124158940c1291540c0790421025072210040310542d9a42c0c0103006019688212410b88050144c141270903034003c040c0144a01c2d0341e00613502072101081c540d0701070110f40d40880486d034401c000320031178507032090710a1170951141c4150280002c0748175003c4000c80110031012201d09010341ea4070076011408981001961144a0407403034004030380300e01c640c051100c008250017661245122071080c5843c2d502d0a505688050206904004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 944714316 1250 944713066 944713097
    0xa0b06160c0f05090115030914010e01060e060a0b03091518101103060d02030f07121509030912020316080616020309090a09050708062503051e091e0a05060610 70
    0x31086d01408143c5000b0a000c48142c0c1d403089103080d180e480d00c3c1d0b0b41e51903001200c0201b0702441210024103040ca180c84035400d01d0800301b00e0030700c070a0040b01e403040d06c0000056080c0108016040c00c0c00450410007c0c00e01d081015180c030000743e22142074080c002c4c4106480102d2981c007591009086040310142345840f14400c000040002e110f0403031b01030042c5100b00c4103030f110901005004240155070b40c00d00700f03440e1801c5c82a0401e540700158030645401040b002182d41326540340c048c1d03010b040c460750b4000074031b00002c1c1c0b611001d000d030850035170007000c2c000c0b8850a011070101c1c000c20741000040c0d18a400100180d8903401821801074004000200041c04945150080160325000314196034507a5150384000d8108a0200c81c4e0049420401c0c00035403003050b01170441c0c2c01124540c501040740c3c1c108441c1ca405c10300600c160b0b43c18502ca075140401c440c001c05000d00010214021000809030f2960305905440d60510f040c00c2c4c4079409074200081e1a400c0912580300420740d2a035846103840580103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 944715566 1250 944714316 944714339
    0x60e010903020705040e1f14060a18050604020405042a03021e030c0c1504110a0b0a0e040609021204050114040213150e0711010501080102160b0a0b06160c0f050901 72
    0x400d1018640321f018007480044107695042c240c01c004402006c2140303046075150000007100504424002d001100c030030040c0c0b041005034540d035801c002002091a03203c42000401a0207250405030f481031406004480c59020503012119800c854106410402840e903003d030220702860b1074000b0700000c2d2500c2d00240b090600002c545c00a107400b0310b5410101d0303a0b242e49d8600005c41c10a008184c1d0712406000c1880b04200c59104071450450b0900c0d409801c02201c2d02e00da004a1075450140010504906010307680c5400480142a0380b0a0464441c94940c140900304d502c180e03820348407940307030416000004940340c0c041840b6a802800f140541c2c0300c845080350003080c00c9031031003003840320b81076011650b100100241c901a45956503070701c2581c01a0040c246c219a4107900c001c04581c4100107000c1c0e0902c095420124031508940c400e00c1c00d507954452000170300b80780300f2032642c81000000d401035000d000484440015010b22414032039241c8a925080d1a203441b4051180c2c8801c200c1e004010f6000c1c000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 944716816 1250 944715566 944715581
    0x51f12050102120907031401020a050f030a09081c0e030703090501080901020c07060c030f090f060c0602090a0308031e0f24130203150906061602060421060e01090302070504 76
    0x1000014a0f1010514551100d0203098488440a0700004410010711a0101100701d03c2c481c41c90085103031020f01023014080b4880c642031140348407004000941c2003140d99002c044c54540015460340d45000f56110545c656a1803a11100034a1414521000c00c41e07000080d034840551603180c1c2c0d0b100c01d04000064600c520020305201d2150740030040c1c0c580003242406041b000700800c1d01c0c3c4102500741c030f1401600180e00d8144000420040e04d004210400803c040a4100c440038201480441c42c107082c003001902c00e0040e05034000480d40303000810410b04a00452086c03440f000e8103466825858200c000c00b03031066894610304c400345008600000c0c03c0b81c110260849401c820b40100c80c0c0b480c004a226002c4043d1142007141d404001c0000d26081c006000b003c8003c1210244028030701100002c10030300855443c0724241e5010f2a50000f15129801110050401e11030030f10069421003100020b25040b030041281c1090800322070a03d04101401a03004481e490b07000781492604201c1400003d0154 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 944718066 1250 944716816 944716823
    0x10c140c040c0e0f09060d08041203140a0206011a1b0708010b0901080c0103050a180308060406150206040b090f03030103050a02132a021e0304030501060e04054903051f12 75
    0x44410076000191444001c000401500712107000704262b0341000390001c40f002e40d0340350980b0700400c0030041c2141d0100d202815107100d405c96412480d11501418424000d02c03c0c200ca402c02000a1aa250107000910f0f104541c180c00081c886101140180060500300780305210640d800440c04c000c41d91700a4200c0c42d44490103410009500b11103490b011803440e00e011090300400c803113100b13124260501c1c0c0079400160540c952020b2154454000c0250340300710007840035044000707181c0412440703607003802140002c03080b80003120703209e50f1a401c1c0070b6210300e09020300b2485000782108400c0da908042c0101c0f0700c10501c6400f000740c0c0500078001c90030205105c000000460055036283c070b90614101110740081c0d103801001f107854a0941c0740040c21124150446019008a80e00b0040040c1c030005086014113401c1603e8410704803496010a000381e0840300000c01c202400681c0114500d00602140098806030380902c980d0711000d1582c000303154510700304541b010040405109240010401070800b511 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 944719316 1250 944718066 944718079
    0xa2304020d06020d0b28121a10061d0109060507050c0907032f2a0a03080702060a09170c03070803010902091e030c040b010c140c040c0e0f0906 63
    0x1240e50710301081383c2c0060f500341c0c0d010366180c4450f003482c104154a0b610400d0500d15040c0d0000e00400c1c59148401180704246500025141c2070702000780364550140d00742181d41e41400760b81404003510380d16400c140105c0700010490b401d0214404400d0440c1481008103840d507080315820160200c0c0d8a90140b07209039420700c1035038001051500d450751954421141950001104483c009030350001807601280c15441d075155161810000b80c0d0902100e501c0c0b443c008924240e4240040d5810305800c602e0301c500c0480c040d404150b0181500240143c0c4a01440d500790f5006036107a261100468107003031030140030140600844484904020700a100e0410703240101c0741024042c0e52102c030658007d070882a001034011440300000d04081c1c100c10b045080c0c01118141c10711403040413075074403031601c0c103414442c940315000d04015034000c0011080940e000180380d049880d105038001e5440b81c0300d01c00180140c0c41c01800d080c48070310070200280d5100e801001c45500e60102e0040140602001e0b10041e401203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 944720566 1250 944719316 944719339
    0x3060324020c0616121a0111330f100b13080703060b040c080f0f0601032a140a020a08030714041401090509011412030904020a170a230402 61
    0x16010000b05104101d113801107606001103120040801e400c0c010303401144c0741070802c4540c0302000340781012100c000a10f022207828580340d08141c0781454461b50b250790071100c0c02185044a210400307408101c41c8046405001e911445c21031440980201c0d491160140184014852400f007000181400103550280510958072005d0050400f200f40d8070031141990b0340e800e0701119050a0081400100c0c45007814045031400c10711500320044000c20400e005a41e020009010340c0c043d522015040b0842900062044801c2420644a00119507010049035680342195008100b0703404a07442c5541581c00340a0903c0d60350742d5403082c1d8002070040e00a00c039900700d000d006030a00101401c0244003400d080d101010320100050000980742d04100c0c0140041070050110310000b01c50035019076402d582a405103140f1102150441c0030719802c0540c410300014a16034101e078030824405106c409006c042d102c0b0b48a08041c0012540000c04040500c1d0300190180c00c0480031841e601d078828000703000f044000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 944721816 1250 944720566 944720587
    0x40b0915190905090906061e0d08031f0506090d0605040c030b0f0403170408042d080a051c1707050d29040e0615040e0d0206090d0306032402 62
    0x2210441c040700020802c0c40c041001d4908000d150ba0031150070000380030242003c07008101c441c1140300455000120a000d42a03007601da0071a50800302c0d07005985151a070801c3d45013910312510402601074845540840400d20386031100498416a070014041400188c031070b03176828041e0800400569940180c4940040442c0500300001c0c0f2070b00004034603107158501450007401c804009054203c5410022080200027180d5008542c1952030f003840b012a1129850003600800316400c0391404a20642c210001d10300c500000e10409042c4144240d804903401c402c0784120707d840b004080c10005074085401032220440070819034210f0200d245ca146005044070021094803a4683c001c00d46000884051110155204c0b40500c1c0640c00c8509210280c220f24047c0c1d95200041c0804188144152a07a0701076a00d0b644044000c0580c2d6064650085034024040d4580104031072400c20381c02407403031122089100f44a4001580e502841c04a2031030f50300d51520f4001158111074201d819403c00142011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 944723066 1250 944721816 944721847
    0x7030b031006060809060a09030806040908130f1a0f071b09090506061503040203071703040317030a0510180507050c15041203200c0c060304030320040b0915 69
    0x907203200d440c0c002a50070310300000c0b0b21b401c10040030000c605181c07a03468000258031514080d0000b000701e074080b82e69103003401e1084551041101c00c00e440518598006105040d42081c40b08840c146074410440560384a888540c0303115500d0710200e248010000080000c40c940560413111802d40a800403031a10340c1504422514032000170b44580d449a001c11400703150421281e40000c01200089046007820341c00709170b482c4a0f80c000d001c01c2410130501d075030760858100151401141c0110b030502407860b4258000119a106450003086203042100190100c104003000c1c0c81150b011501041c020300208500c0001800060800000c02c6010407540500303403000c000c0034110181c032400b05245414140742006040d10511480402d060030058503500e107014035202c01218850010071103603145d01401c0440d0401c4400003100d030740003402100340010301d9890380c00140480820106e0019070020000090841c0c0228440c111640342c040203101010308083c004101c3c003070b800c1d80c0c4031420000d010400300c18 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 944724316 1250 944723066 944723069
    0x1480b0c0309010b0a06080604051503032809080312060a1205010c02010b0910030308090a1a100506070b0a0b2e12090f1209090f09020f010206090607030b031006 71
    0x8040c2030110611010510a1142000307540c01168095100c3d40b90401c0582500350050550740b00310350740d900040002c045124244070000c0c004040e01d50360380c0c3d12900d408114106c03002501000c0c104803030b04100680980d03401d1040da42c900008505291080ca1030541420f0000c00789074100d03208280c0000d1001151010f644d20621031800810801040c0000030708407071402c605540300300d102c14140321268030400601d0003540c0d010303c0d00842680ea84079501d4600100000018590550800c8412080018001c15405000c421203045072040c0d1b150104100350149010152040d1202d0380458003400865000390340c40070f400790408c0800f55010a514224007407440140389076406c1d1078031008101d50b00c2451042464110041040003403042d4545040c680b202c0a402081036008445900030b00c1e004030064002003908400900c5504420141100a410010703c100d00400120080d01502d42c00440c0461043d41d00070b00510309a40c0301c034000c401038110201030350707018020081d00c005c401c1d18a00a100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 944725566 1250 944724316 944724331
    0x3171c0b0f090708010512010b090c130807030b0f1512010b0f0a08030f03280b0a080f120a050408030f1308060717180105041101480b 59
    0x421221580a0100c100340a0325294482c80749282041145500100261705540c002d0b0351002c40100f101d000e1174010801c9030f0f441940920010104401aa01c0b40c001340030158a0b040400041552105510703910380c0c050000400001510b4000b600a550310402280d00028031860051801d40e01008190081e100c2070076035034103035181c0035103032854184508640501c04d0199400a8454500001c080e01c0340120a854402e0280010100d01c03550f9441280214000d450800400d4010100b106580281030502115020340f0070640006042d90001c5603581d08040e0140c05007050150400071040107038490755080e01404024400414010000c10203440034841e0410030f10303501c4076042d820301041080b47d445006554040c90800c40b416030301910044030140d503594030960795102e07c7c400d01d12200c00c81d08581c607990320f014204018400d6040c11022040c1003038a80f00c000305040a69401100001c040b024101e40b403c01101c21060051444a081052030800b40041d41010390b6403000051030a54400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 944726816 1250 944725566 944725571
    0x40302150333091905061e100302091201050907090b09060d02031002040b04050a08030406021b060424032a05280203030103170a090522182102060103171c 68
    0x5140c0500705208054014001f02c80ca403d40d0b03100c8990180c0324000300c211443c040c1d003582c1130f64510280650192400402d0080c02a034002c0080302e0390300c2c02440d040701e0585aa118840d000152900a4030801c2451078018004e1003d45c0d407400244030100240420807a01842111840b145042962010780090000401d0843c1c4d10344ca130400704029402140c211081c00c0e0000c00082000c1038001070041d444004c90a19003c0f1402683c0004a440c012640080e044801c0c8030481158558502c25110125400c0e40b000c0044c0001012040c1b03549006c40c2c01c1c2a84840701c642800001c50250003c1d240040e81750110128107601080c42d441680c582c500540e001d60300200040c0108140309001420310018020b40d6424100480801051100f0a00c20180a80505203450308104003a0424222101e40203006000c40c80b00c0704901150066050000d9400411012015002e070b1082c02181c0e100c0d07611a40200026421500d0321403804400761034082d2482002c101501404c2c91092603d0100c45024200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 944728066 1250 944726816 944726851
    0x17130206030c1803070506030115030e2b0c050c220c0908150415240602160b0c070b1b1603120e0108010603021b0a0804030215033309 59
    0xc3d20415400c00b55076912a0300202e0080c044d98507a80c081d24110b441c4032000f52000710505100794020301c0101c0d0340e041c1900407603c0e500c06400c40202c60b01310010b0810b21408407080c56050442d514418500010003e410031032050100d89003002c903d43c0c9080b6258000421003589024110444400c00c80e140007180b01080f081040310302c00d0050707071940140400c055115181c103560701061207100c0306194050947d10f20825040181c03c500c805450300e4405035562180d611200081e41d60f4500c1d0303048140d82c050000e00410011414401d039003030503460000030b040303203410400c00c980303150041180c4a240002001c140000300404003c446030b4056698962045203085003041c0010414610826041c40a0005202440c0e640070901904440140c5401620340408110f1031043c90721a0710740b40c0c06482003181d0a002d2013240070051084910881d802d2100042c91b841c60303080d9000071907404c074851041324907031581c1025880420307442a803108401d03442c131084c1200041620030144d4400343c84003d10000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 944729316 1250 944728066 944728087
    0x20f1204120c1203090809060a030b0a05010f050313260405090c160b18030406020c030f012009040204030602070b181204052106010602032817130206030c 68
    0x514401d0715403460400703599405070710b0710241c480800d4140340c00c0640d0b03a640601407003500015140317030300d40041040c0d55442940e203005025004e007100c09842040c44000000e815802a24101034122550310b55a0030340e80c6000030030801040001c410741d01074245030281540f500c541c48902d0400c4184a0344103860f1400d000c2400840e100081241d01200c0080190910026044800b2030242e5481402c0c144981c0d681e08024a103045044800340e024440854049001900840c100342c1c04101901200e07044400c04240909983d0488080c034080e500004104948000d50002405180c6000e0405480c1a60703d595000403a44121420307510942c03004140084080e075017100d0307088500103400401503030f500c090350181188540c0c4151031045008080001031a00b00b04c002c5100b41c6216030a944072507a54200103512984004c0c580d210102500c0f105800444807440980030400309540c13800d4240c2592160303283c485034040d00d100040c1c401044420016584d0200841c40b03402c80701e043d181c441c44040b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 944730566 1250 944729316 944729333
    0xc0f09050c03040218090c12011d1b090a0b030703060b040e010902010509060919080307150e0a17090907050d0f09020612041b060c0c061803020105030a020f1204 71
    0x402424545400b0002d10000d0b070344210750010192030460020580e03448100203036140c00d0006c1032940e00001130a00c3c000481c44103510040f09038404c038080110700303560301851a0310740000320305400d102202d410355414a0300b0040300c0c869108012130b40003c0c0c800b41640c0028074008040c0e004442c0e00e61906d081c1c01c4242018042c0d481103006685c0240070003850740d40082c050b0b01818004900900010429078102d039280701e00c80082c1c0ca03038103000d043c0701600c5202007a01d981c0146000d4507140c28800c080300c95440e480c40b4020009030383c04080c0001105680e9598581ca820090307421340013100344039000f6075549202d9118084d2825840c0c850762003040501010549644c1510346c9051480d00a000015880700c008680c420a402150304505595034a040d407510150711882d042502c4c40c8000c00b0800036003001c0b403507200500640f201c618840d40c0e400203c54282d110640c1e00c141503000f0404000550140340a0341d001018500c2c0941005d0500c901440c083d040b01100036001c0c0f04c2da070309100c11300a00c00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 944731816 1250 944730566 944730571
    0x516060507121b0b04051c09080601120602071a010f050303070201170915071110110a030e1c030609050c1204080f1b1005090c0a0b090d0c0f0905 64
    0x50606078100074030340d11000361a0402c01020030074402e2507184800d000c01121a0410210f501101ca5011410603007025a507070301100121822241c4181c903c80e41e001c7c010000704080f240c6c0030006041e1070f0700340711070003074036002c400740c00c6944c0e81c3c0070b003c032030002000340464024002c90101100110b601d40f20700e201554801d94811402900100300d00301c0540d0780580044102c02c0ba058034646c0c2e548540354054500f1a2410b8290b8011694205000c4115401001e001c642c1c0148000c4070040d5050105070001ca030840150500c4101082040807101d600a401802501c007800041d154181e60744c10261035410003010910001a568442c107004c4043d0f82d101d81c0f6001045500c1950800c40c01c0b00c406c10401340c0c01b03080070700003035800300b0b04040c1070b0b414408807852465401000981c83c842146895943c096180c24000e000d07003400005801e0203070000b1190f20380b81000f4401c0c1c8225180c41c15044c50f9500c0106002e810040080c000700101c4e0701044914000c0501e00f2031014450324240b88242150b101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 944733066 1250 944731816 944731829
    0x14090f100e0d080603070e040b0f0f010b250204050c040317310906141003091e110a0e04120801030f11010e041b020d0203030f0a1d010203040516 64
    0x820410701c00c41c4600203a0010b5070003850800000c81c0d240c0703200203460140300d58003502c1141802c004220030008000c0000d8062069030304406072644851030142e410a90901405000503400d202d00bc0014109014050315840c681226030711200306500403c06403001140c8031030341260005010810040c0c4180c0b582d0105540030300d12820400b04080044400030040e41c041d100044407030800591102d034142490081850035400c02002e40d4805200091151103002180b2400745152520b2515020b4003030f9104481e03201445200405810f400300c42419505a003e90302c00507260020050750307d402466001400310b68034103100c980362500d4202090f0866a44400c00c008120004000081f101044d03074003126400800700000c00c083d030004841448070150b00702d5000d420b01181680d41d0f0800c0c1006641d064140d0300344c5140e016105d1090741e5910055400c442140e8000780002c55500155104e100240f03641c410007104140180c98450a80e0030a84080e24103801c0b0700310050a82149111903001041d0303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 944734316 1250 944733066 944733071
    0x1020c09060f0307180504030905040510050603090f030304050c0f010c0b06240327160909020423100e16030e0c030703030518010908060103110414090f10 68
    0x8808000c0394104002411950051500d1040850305590500008028107442d104003180340114000240103008251403d034041220420085001d05080c0125407240c4100c7e212113951514100c180207a03580000c15501881c05101c401c0c1c525440240010341c040e9001e00000d00390a0428010001040d00103500207051002c02c6d480c91000034500e0030099409241100d08010541c0801c1620071912076071013081e00340c078900004001d491b82403121013101c0701c201e1030240b0880c81c5450080700d580d0b01c80c03100d0b40f04441c402c1803810005914580c002c0300e141440a817010610901d018030072490388840d00141f00c0000361603030130029108495555800140300a44642c91107041c10105039801c41e240850740000c15450f984840944101000044c6050301c010b002c0b01d0901d5603e0400030810340000c5940032090201c4000f50400d98840d4104c081640c204001030b0405901c0c0d07541e00380c0747d4207100d51201c3c1c00a440d46103400340302c445854118070500000010381500003114051500b8540c035400c10601c1e00d407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 944735566 1250 944734316 944734333
    0x51e0702090a090501020904060e0708010603020a27030209010b0d0b01170c1e0a030f05010b13050d06060902160b0f0c0a0c03050f0a0203120a061206090305070209160e0102 76
    0x9950340e010381e4000c82e0000c070004282d011070904902a218004550345c200e82031250000c1c103140300341c0030380b0b2040049a4401c074080e620b0b8032044050b8410982c2c21030000311401d030542500001c010f11081940c008000c4005402ea07203602280e0b11910903480156400008074080b00d1050250262007104142440c2c034004000903150303214580311010b0191059080f011031890280c489500d210b4002405030b2081ca071b01c9410511008001e00440700c40b102406003005e0002481c03104410590f608102105007180d0128104014040481e400d0380c2d0a450306512040c001502040c184010040e10b2204031502c4101500da083c282295031025080d1860301200c0010881a0b0611000741c1d031402916180440d20500030303040446060040030712030000307002e0001d042e410480c0c00000030701e56060a1a1b50801b40c0d07403201041001c50703000c0d1040880202c0740010910003e00d0383ea04c5511100c0c4241060303030a000040d000710345c002c00204da05030880d01c0b20300f101c010540d400c0b94021881060901c0144000c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 944736816 1250 944735566 944735569
    0xf1b060608031b0a0f0809030c041a0307080c0a030b070203040b19110a0c030803061201020c100b0d0c031716060c0212090a0b031803210f070e150d02040303051e0702 73
    0x10724917850180128034082103100d0343c0da6051003c5075070620000c0c000d002c004030049101c0000c01410310303058840d22460100241c075140101d01e00252141c010800b206a0f491500c0f1041295001007881045000822000c01c0d6800c1d203101501c003900c400060b001000c003c00e0406003500c3c070300f842d05d90b40d9903028030f0100001403040004141941d5210160b00e841c0d84072034011a19a942000d00094a54004148200e5088002848a03884100603505200840d501d0003881800703a131075200913254a0b4840414000f02e06070382c00020200346200125031900c40c28982d60a045c010f8540200d50301501d400641c0c6483e0360410441002200e40e0400602c0c0800d9500040c4075040300c0e00c66440c98200210000740c0d10842284003c8d258400c8409807603841c5c0d0010581080b000c4212180c00e101c500d040041000c01c01c3d0f0b41d0040c1e10900058540035202c1c401d410070820901b094110144500000304005034281a2a0010f800154440d85540c0c0e201d54080c290028082d1598500c51040380c0c0038030125025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 944738066 1250 944736816 944736833
    0x171e0306061602011412100e090d03050619031a0702060c0a1223010306050708040f1e140c03010b0d17220f080613030f1b060608031b0a 60
    0x92440d15128207912440f0b20040c1c40031200e0010030000380b00d0128009404006d40014203200e60f0040d400701c090180c0380c1c04040d0f10324100344c0342c1c1642c035030082c0c07600303840c1d1030003130b40415007000300180410b008403414100d0398010519500b003200c40e1028203030f0782942500e011604a4102e03900d4009040d092604030f10041242c00340c1c0001e50308000003064a4010700380700d58890484c04001c00c0900319214070000907040244000e01c0304681c1c0c81c0c544400544154400d1205902540d40140c084280b401c45860b504000d42500c40040d406000f0010740c0000074890905170084d81407140090448050442c0805003141c8040214034002d920300160300c40010326101c02ea41d440c085404565481c0e4252040b03581e80003040e240b000000ba0b180701030104054481d403c00c0411a8541821601c15554a03040000c0c090000c000050204e414414050743c8036000c1d00106080c800021a1983c0060b801e841f101e0036035a007075004144507000020120f00d07140c4105040d0314a020700c80d0007049515050368401b00c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 944739316 1250 944738066 944738077
    0x30714040c030f09060207051b01170405100903020c120303061f091e03020907030b2b0213150803030403170612010219080603011e0902030109171e030606 68
    0x128598690741200d01030301036402000900c0700701c0020004c040c41440c1900081d0b102c44c02c1a034a61041c41c0440e81130365284030900180c0307241a5901284407040d900c51124a4034081c004582c1c40c00380c0720407a4440c66191240d10940341c001d13030080c4078075000d200c284402c00154408001a581003001082070302e4403200700390b00070f0101d116500700c42c08201a8085840d89000d4004041d042c0c01d030322480d00305009104074181a40d000329154402925544015021508007188542e040f0500031400504441111440da008601c0c0184a070403070925a1300044c401190407950711280340d65040480c2a403852910b003078016040120056207141816100030780b25040c2c29005141c9172001c1d000051094543c00b400000542c01080255250200c500c800380700c038020550000006004c010002d041413605014200240c5541d000313108254402407540800740c400c0000a0741c056407504442ea00180401c6111010094074904007910b91300741e0b600c00f10655030307240c2c0100c800c3c041c1842401441ea80d10700031102d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 944740566 1250 944739316 944739319
    0x6060824060307080c0f0f030a050a150911120c0402040e16020f100c140406030b100e011202130503030304080408010f061401050a090803040b09031005010b0f0d060306090303020d0b030714 83
    0x10701d008404000f0b07589001c0c7d81903058040c01801220000c01400244c0310145600c16401100341801c9a4200345c1103038501000904007505064184002d03050004c00941942c10b4030080d1840c0c1c4601602042c1603900130b44c0003847c1c002d01c0000700b0200b02d6106805d0904071041d8405482018045110711f80e0710446400340c00e400315915080c150070140101c000e6112900c4013289551190340d6108050024400746039040d00441221502ea4041846460703a03100307918058403080d5801c00d00d601c4100003500014140704001c0310b09075001c55159010806140700e14070480440c1c0c0c0d40c81c2803501207403d4412580010300ca25042c10000c3c01070b2102c202003031300c0c0c52100f032038121340702c0e140e108040317440f0400d581c000401400f00103400f140b0216504010403c1c144190100c0f0340d4000400c00f01c03412144244148403c0e442c0038814800300d840f61500030030904d18a000086400da4507900d031481240d88a000440100380e0015101d100d0354050301600500d0f042c01c5000c2c2c0915071401040e146055240c2961a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 944741816 1250 944740566 944740579
    0x60411090910120807050610050916020f0f01150911030403081e07030e0f0303040503090603061807020a06290105091305010b04050301150f030f06060824060307080c 73
    0x1c848070000c2542000800703c0c2000d0b446500000d09001044da40054030603030f002d006c1c200005d00124040050b1704100c92014107100c0042e541c141403040b820314102049421030080d824a0740c642c041c10070103060380151031303400002c40c14880c4003140655001d9600040c0301505002d00e4410390000c000542c2c1c0e0182d058203040721a943d5403500908214182203824860207203184c148051140d060344a00c00700f000030f000319600340300501ca140c1d5580c0002c4500416541c81003041c01c0e0780b070501c94051604440080e10040d54103031b51032802c140c4080d007100c0000069121400e00700034841140142079078060020011070011451400d0714103102c100102c5035040c00b100085101858803080601c4408003102002000f665840f490b03d112258058403800c0d11a40c01c18103591300160480101608880b1a80101960203140d03036902400b101103854180c440e0b65a42c0c50010b8059000c2c041e01c1c41e05c420001d88100c1d014111050203011080280509003e60701140c82449041000202080c0e4150210380a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 944743066 1250 944741816 944741821
    0xc03010e0708092a040207120201180819091d0a1b45081501120308100f08061b090120030706110322082d0f0903060604110909 56
    0xb004c1d00d81881540702030300700e4400030700303607081c004142c0100082c50490350007403040325080010b240c80380c3c001460242c103694041000392072000040c08000701c61507490178403110107540c403408855141070b83da109020f03030b403c03000c10051000c0c514880c0d06001c404900c011403050001e104000c0c107400000316680441c4421101708014070502d440000007540c8201c050b40040c1d0841903511a5070301a61180b0025403040c000185241503001ca051030680e41001200c0b9040c0b410b42d2002c849040d00507021480c00b00c040140032403460135100b0303c180603024000042480e402c1640902c3c1e00444c1c0d10380f4050b40850180410303502a1307840f13055102c044030b200c05060a0a044098920b08612030024001c081c1490040c00c852103517203010185d03214022604405210205860a03e038100450240040c12882c0c00c02618095000c0041e21824207284425a0b00c400d8540340741000741c540c403e4500a00310100402c090742d181c941001300c0355201406580a20040800c80c400b10f1040c040d00410a1190241400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 944744316 1250 944743066 944743123
    0x9090b03070f140d0210030614061908070e0a14030c01020d0504062d020a0b0a020f03010603020a0c0b010b0319060e0103111210061a03070c0201120e060c03010e070809 74
    0x703098280da4004000751b00b0441400301c05001016544112580e1425001443e200b910b4140e05440103130311848151010908640c408499071140100414280035404a000c40751f51590103001d8043c04808400010305186001018a0304140c400114112b600c00d0040c1c260b000e5200341550201c8131b00703041800b08403620085d000880a442148a0b015440b003601d02208940d0000780c0d40d9810f8061070f4000000e403590103510050f8803550140445070307030042004014444c484c0e80100b010101501d42460000129511400c4140d000e031b00000d0140c0b404000e0240c404104100c802401032600c00400c0340ca4906041009807400c1403001500b450303010300800f451621840030700b201500541042d00c62070380ca1061810001c111038010307103105981c200103441da800d5507002141e014003210381380d0740c040d9902940119050700c2040c03000392040741c8076240c0070100c25080240602895040030030b25200e6050020f090f0880343c006041900300b0007018248403500c030002c01d8208011140743e00b05861201d0101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 944745566 1250 944744316 944744329
    0x30a0b070e04020f0a0f17270d020c030d171b0c0f071503050408090915040204091d0601030f03111e010e0105102303100c09090b03070f14 61
    0x400e075401c14000101d591181c01214000e040c0d0012540b18582c1312400c600b07007212112604202c0c82c441c01c4240001c2010308003e40b418084d0806d05410021280005031010b80c1088841c01402025034480c078a00f00711440e040c003c0c0c4a48410a1070000022212881c4000c1c8900014003802000704259401c150380312490812121008110710407940b030740d10031007905c907598a00c510440d410a080e24a00f520840d110b03004482c09103400080003420b0040b00f03001c001101e10b02800b1400e0600c40945507840941f5140080d000400c007209c0d0004290310440b40c0326042041104520115400500045c00007070012801c004207a90117251076035400f00e16032919480c0010910801c000700074a01032815007200150050024010020300a2045d501e99026584042c3d002d8029035064425070040780d40100052880e0500c8240c1c01400c0f04c410400b80040307001101d1a1410b4200042d8404074140103c0400c0d004007910000284c001f0442035141c0841d40c12600c02a0088010f425445c0e0701e94240d90b96242e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 944746816 1250 944745566 944745587
    0x150e0c0f0d020f031c08010f060c200d020324010e0f01030b04080d090b0115030b01080a0e01141302100c08090105161515050303090312071a010b12010e06030a0b07 72
    0x11704419044980003a00985441401d01c0340144012484001250040c4a600300d4004030707900c401c0410f500d4203401c42e01e6035004400c041054000144800100c0560b40810000f074011880b5224121a22a82508101c1e0349070305030000b4806200c1c40c01446507000300d42a8403411284c020f4103015040d1a00e10b04407404c3d1051040c8002e0711420300c1e006405100030b20030514100d07130034580012a0741820031003e0b001c0c0e5092761420781c0440c0c2800d0004841c40402d81000d10780544070340000618012000020440070301c295010203402060406180446c00d00314400d80508105003401b1910600c036540d0b0580031b200714500e40d81000404110381907a402c1100041c41c41c16404000d1507058109600341d000101042503200c5c1030f0741ca03405000101c90034084112011004041d0140c5408148090390402130b5004c0c0004072a00300c00c1c54546011410b010384a42e020f031003a0210302c0e599040c851581101924180c219102c0c44512400740300207650b00042c21144142e001005590fa03503a00e0070b054503180300e82c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 944748066 1250 944746816 944746843
    0x380106050a050d020c030d0b04140402010503100801020d0509010b010512070e0a0909030f0e0103110405060705160906081c0c11010201020d15051008190b0d150e0c0f0d020f03 77
    0x3159000b80c40d2408409080c090814807c10844010010304000c02d94070041722065105503000c0204015510071001036a010940c3c0401403c4699280d02042c22a0b10811a074144980e8640600c14101428002c03a41b120f9024607105003824500d03840b100c82d02c10045e2880c1c090021080c081419502c4110b048401071001c40000c102403ca20700f0f0141c084400313902d04500141d01400c21000c25070282c420b000503103910b108090300305801e2401b031100560000c10103581500c20309480d07146a025039040070018040c4180c001c01d54500d044051032400d00b031005107a040800c8003550601e0300350b100b042e881c84507401040f00380640c0d0150b40141d0092190f440b800100c141071900d404081c03240380745160102c81c070a8810220031503106c07000300e40c1d200c826900a5480400d0315103415151100d900041000036008160b00440300c240d40d9411754040023004102d401c561541c0090081840c02c4c09880d080b00c42c1075590f01804003000c00028807a0320a190b00070f200d001c60b090142ca030781d01c0800c00c46080c03201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 944749316 1250 944748066 944748071
    0x180203012d030b0705121b09040504020a1520013303170c10051605030912070309140301050601091703070803040605010e090102090616021804380106050a050d 70
    0x9154100400c65840f60026075032246c5140040341c42c0301e00c5828441003503440042550308080010f02000041d04000d002640e0102d5140c0e008a1400050542c8080d5003180d6141c80e0500740d10800f50150005285c800700406915001088566600f03004400c3c00741819000703000e8140002c620300b500d20700c05941024110303110030308454920118000060100070011030454108002a544210a07100300320340c4045140760700ca8000f142c650041c00074540180000080d00e1201540c03142d2a8100e401031101600000d40b00e09007008509072060720070700240c000354002d0010b4944403001074100720f1030380b040c01141486660a007040040a10031fa80b404e585c080c40c403035528101820507801422003070040c0711036940a9004184040d805200322041c0e1900038111508143d0b0034921180381c998600e07000d03a0080c41c0c0c1c44c1e44e49009950a03086c140b10701e01c290000b19503801d00d00981d00f42e451210200b00c0400c8070030318032020a42d24089045045071618600103035284030282d804c491078011442c10f00005c60 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 944750566 1250 944749316 944749321
    0x20c010c050c10020c0c060702311802150d0609051807060c0c0e0a02090904061b0c050304290c0309040b0103050c0306010f02160f180203012d030b 65
    0x5501400401066510500f2102d4240070140700404910440d1001003850303121545402c6d071810950301501c1d840d8001480000800b00703550f0252003400c04d1800d80c43c611200e42d22450241800d61044070484618041003a801c1070099001c5080c0369000d2810b40c1c1100c00c04a07620742e0001060b00804058042600180a541040f02c0001d056482c00750140c0018012054003240c4d6511440c6004070241d0441008100c15141010101d081800a014800940d408004070206515003012441c0106d110720000101041c1000c080300695008404000070405032040890100301d00000361030580d000407845074010a1008041e4121483d004180c9a240c00c0208012950000204c042d00c41e07104243c4051003820741942c0110101c440890382045a2402030010540c10751180d051980820160b004079100a43ea85034401c100c00700c0b41d400900004075042c000c0c0018078010001c007010b544418030544c00c550608000d400d410503800041b2071500d07420341c03201c6641c41c02c040840b0010354020040754101e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 944751816 1250 944750566 944750591
    0x6050301090302061e070f052503231606050a06121b0e071b05210a030b18040b040c0f0308030108210a050d02040e01080706080f04020a03110103020c01 67
    0x1004d080310100c2401058450030401018481e801c0d922541c140d0b0b4a500071603690720400e50315a04400480150445446081842c2c120410341072001740d4081d031568109548000c615030b046440c22200d2a1266005100039649980c03111011107807176a010344003041556582c14108010b0286512001010007800742c80303028000d04684481104e1019a4440303001078941900c0400c8100954164000444841000ca010301007022a018032a118800740e560768480c0d03400e420f04161041002c4403429400081c10084180c05101d00030348034606a5400c1e07001d602038280e0b0300088000074005424481d00800140c2042141c0c01041d025103000459480039503102d05003429150400d0081118920030080034011652a1003a100d0004c0c1000d0003181c602084204201c1e03041d0081032039060116020f0101054501400c5000da01814080c001842850700e0500300628401000d0010055903002100b4000581c59001040c1c0079240c101c0500d41580c140600101c00900c100c0c001d40d0110b519111180245 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 944753066 1250 944751816 944751823
    0x804090b010f0e0d03141e180a030f020d05030c0a0606230312090415090b0f060c0607030507110a0f051c080a09110a090504022b0b04050106050301090302 68
    0xc60600b030740d844540d1030869100b40c8503510310085482c0d2040d440084400028030500c3e20b84c11428110b2042820b080c5000001c1c4d2031485919410b5140d061301044203095210411407134115560222086034003c1d00e56201c010701c019136040064022480424a6000d2100030412105940300d05d0040300d0070040f050401b031000f050709028000c424100c000a5441058402c000d00303d1404004020309804204411002c0f1aa44240113558000d91500c0100d028074140c12902002842d55030b60208150390030070108100149400e028920440d414808003146900001d491075000c61282800a074a0300c07030324810707158041443c805880034810196400304000004c18400d0382940304404543e02048240e60f02d42100b0255403110340041c8001001800041898102080b440e0064840d9110301c0d041d680403d10b0014581c00103902c894840b0284002c60038107400003548d6590800c0950461741c00381c1c00c08100e42c034800c030740500781c141944013141c1800000e40c4070710001d1100500030445402c040c60701945 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 944754316 1250 944753066 944753081
    0x102011116110109182a0201150b03010b0406030c0e04110a0f020d02030a180503011b020c0607021815040f1d0303071e02010204080d05030103020301150503030d0b0409080409 77
    0x1100041d0b01e41002e0341e035005100d41c60980b10040c8006400e45052200d5000070300706600c0c2c0e03014451001d80036a107500a00c00e5902d50481b501d50003c1109102c1c03090220500c68242d00c410f006110070401080040d0203a010345041c1e469614005c190422a81d004592103408000c2040d4018a060150486040004c004108005154481820329421400241c0c4c451105810240c0541c00820003d43c8440c0700d030701c0c1940440b1240d00103002c01a150804242100c5103c801030098a210070b02c051806501084803100c80401190400d1070001c0c20340c0404c603c401900306100030742c202d200200310740585030490310303282d02e20103042002400d1030b0150200c05030604240054000c00513003250b90b104507000c012244103d1060300c4d0000700040c06084154903200701c0300d581c01195424440819201da05000714107085481d95910354403941540109800c40d41c486611030081e2400d08010484d50302d0201c19581030b26907000d400121803003200041b80c054104202c00510102c0005000f258a0070f05500040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 944755566 1250 944754316 944754323
    0x11704050f010612060f09021c03020f0a03022a01020d0f030e0d1809022d0706090b061503040b011707080a0f1103031e070606030204090b04030f090e0606090102011116 74
    0x1182444501d011b208a030048000070350841c0e8408441c071301c65042a013600d003600d4031070b1040f902000c051050071030a200d02084100c005803c80d01070018400216226489505950f040501c000811a40041d507240e80368000704090181c11a14408210f01940c800c43d1500003090980d0044056044004c0148030001e01c04042041102d2010448008034800c1d9841038580d4011641307070001441c89101d0741072107450551040c0800b0801c0000084190003411021482024881071a007072001c1045400b02c0c8000c1e182882120520400c00800d034000c0b190303030441c0d07948a1850307007840b1510165401c2280da50015607032031280441c48801c00140051285642d4002c039980041038145004044c1c4030311450012500395080364002d640400c06040c0246451031043c0e400141e00c1d0740d2940442d0a442c03525806813001d2600c00108008e0641014074142160503a01d000360100b81004c8110310887e4020340030030300540c004941000140d0007548240c420031441e8801ea51a600d0510010080410300b61085 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 944756816 1250 944755566 944755571
    0x906040507061103120a02091e0a0605070f031107080f06090c0a051e010e09070201050f0c041215020f130305070803030c1b151603050114011704050f01061206 70
    0x50b030b10300c1a1528000b808004000e146040743c520031100b0349240140081c20016820411604d0690341d600380c0700c908090350009405510315044c02c01030b485010b64441c81c184401049060000b0740511040142e00313071300d4142140161031071400750346054151b810640380c5200d03003a0b18103817001c0b000810707601c5104040101d40c801d14030401446001d054921801f0b4100000a8040a414060528100c440f0744189080702404006e000010030002d0152090380160750f41c2c6050244040613142c0710742d0302200352203040340340600d0424020710b000300c0400302a0002910b694400203401c15078046030241007032810700380d840d82c0f034024464641d0342c882d2100300c0780c0303106146000500010110581c0d1281c80d580700c87ca420150811021035181410403091400c41c0a403030868841010b0382c0b08460f020308150f1142c5450003580000c090102c0e075044c1c200148120009240d09078a0f0f80c4a9401c11103600d4039085080241c40750701d805403600b4640c482410265081030004604600304100e400c031040c1c0195401d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 944758066 1250 944756816 944756819
    0xb040e0c0a052403190603081c1a1e030102040815010911090108180f01020405150f091009031e0605072c06040306050f010302031c120917030906040507 67
    0x1040100c420010002c840003d1115908100380d0343d070806140d11640303200d0101810310b0b291608900301c50300d03a00200c550703400203d0b00e12885a0900f0680b42d00d400180c00030880c9085c11580200e200c00003904641c03050030780c5108510482055119a550010090001d42d12a515146442e854403450b21000b404c0011400001071900b00c11b004000ca20b088070400c0500c2c0802c0640112141ea600a1000e0741d09a20300a00300e00d0080100b042030003a41f864000103031194100b104005041820445a80e02c4203018001c1aa034120380134100c0304800030031200c071340ca8441a0301041d210721200b0351024280040a8100350030050016490b400e1182c841c0400308840d80d40c4850648565500d110640050007945407007603209040310782c0c3c024115000400381420681d99669841c150307034003141c1100c40031702000010021401c0400c54004e4803102c15900c10720301c0102d20001460b1402031111a140c00d600c40b40541e0074004030400000c09405204001c0381d07a03241001c1d61135907520f800d5500312218400e02c1300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 944759316 1250 944758066 944758069
    0x302160605071b061a1914060405060d0e0111070512090a0e01060f021c0c0210111f0f09080706050a020706020d02070201020607021b061333020d050d0f0b040e0c0a05 73
    0x5082c51005246e41420304d00d800d02124460f480c0140055641115040001203500c4c0c0d100000703032048420300b41c00420004041c203a503600390b800d506460000c4030014010000000d80c040b407542200c211400540d902c40901800003191443c1c0c540c00301600c50b03001c800106066500909200c0c8001d000c2d02195564000003c07003200c1c40d040324105500290740300d45644010320f440c1300f1140c0c3c900151702d04203142c1464080b0490030240c0c4c4048007200d082000060190106440c0500700c205880c2c1d02d0100100710301c54950041500c00c0108c000c010035500e400040d60101d041d8151000b258004208548810602c40103c000303601c0301c00203a0140c03050310002013080d8400942411030b1644514400c544405080900c10f554028550482261050f41e8001c1079a2070024250745a020400d0b508000c8804118041c400080c1d03410020002c54000e440c0b8044032682003021503001944c0d01c180022008070044030000184003280c5099840303820140e41170340d0414006800c400100040f207002e4ac0d000d03650070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 944760566 1250 944759316 944759329
    0x309031109060a0b160204060f030212070b09100309150527031c060510180801021213020f1003020309010605040b0d081b061e06010302160605071b061a 67
    0x102c220b41d020305102c00c02e200d82c0540c0d0003e408241c0c02c4c050700092401003540001c3c10703180c00741c00003100242c40980401c03e40c0303022000c2c948014142000b40145504200444c00684600350f1445d000d100844011403009110354090742e2690303003102d03220a40c642e9141d04040030b00020354080e6240d001d41001e8500102c2180340c46c10040b0f81d6130740210301e001701d030031440318400e004000382c20038850b984d03400040c254075020400200e40342c041da1080c200100020300345070b90104070b030001603ca80c8144026803a502411010030b80140d5220b00d000a100d00c1480012800d510302d40540d41c001140084c50807419030103070003030b6000e1035084009014480d1940c050000311050036545039448691981c0c89008900c100000b05aa101c0c205001c40844a060f00d25502c2c00790203030303104003100e0321120801c0d80e44881078882a0704580b003442c003940303011100083c10200074040e0f8009401c0581e50f40200d0715035030184083c400f040c1d4031410350f6800d84a960800c0c0000b0902c0d84e0240b0319035440f00c45800012314001c5c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 944761816 1250 944760566 944760571
    0x3060f03030903060406052a040510050a02060415291c02030303011211030604080304021813030815041a03300c01090b0a02030612030f0f090a03020d0309031109 71
    0x90f0003070125a031551142405000c1c094a41006690840b00c8070041c074011224071044980006821a40e80c3d00d400288076500c0102d210000810105011030308ae19070b80400c443da00550020080c504181844000800401d00303a418110744c1058a40b00c0d0300440350550284a4096040b5410305002c0101c0d003505203409480d01c4000d50541003040140244d801101404000500030541010b80c06880e8010910b451020348040d29040408400c2100318038201c042002040e0481c0308501c3c060900759052803425001c0c900003400d10084600144843d085410815070f42e000c001d04c24010130b03042e031102c40c14a07031010b01c02c14020302444070b6560400c10084195885120300070824501080020014141a04080c51098665403601c242d03d003c0b4107052141c50207200303104030060352401c00200f081144000c5c6829100b0b15003050000d2291035440303205035400118121401036440c0e0503640040c02050701908000e5100c0341c21400d09050550112503481501c5c442c90103d14141c801808014418208 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 944763066 1250 944761816 944761819
    0xf0e030106061b0f0503221202011d03010f060b070611030c07081b1006172e0e0303040c0f0b0f040603020a050d06081b1912140d0503060f030309 64
    0x83c0340c840b01e2800494104503078180c050032507022000c00750f94903036081d5841240380b0305d840840c40700e16021102945a0000040c0100780c00000100100c1e400a04039004200d0f4941800d031109504040c103407000c3d0000480900140707410090340c0c2e1182d240c0c00094001c5842515401e150038010311146480d0000c982c00b03542c8590303455060406665514070154410000e800d001d003018046910b400c01d00700648800c0300c5083c0d1000c01c4050505000300ea22041c070105c456001c0d8800c03121000c480210208080340e170451500c8100320300904c5402c80e00505003c22514201c0e1100004000030300c4075407982041518031002600754400d65a070034994144c0a03450200b05641d204220409c00d240c081c0c1e000b400401c00c50f0400c0c40c01d144107102c43c5002c80d41d00b54851042c6400244070440010340f80b140c800100201110306c0e000140c05582c0390851a005d0b8040c94001805804001041c841683c0d141c08403110000100c2d40140d0034514010480d40065494034081c40581000001610340070040d03d510100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 944764316 1250 944763066 944763077
    0x607021f05090a1b0806010f09140f1b070b1302011e0e01050310050402160303050a201308060c07061103010803030a0c03180302071809020d0f021903030f0e03010606 73
    0x8658070f034070003d50980c52418084a0784113a000904103401d22045000300840c0c049403130101d25110b80072045e038600c00f1600152241403810443c901c1b00e288070482e0858480301b07012540510034880c6000301d2068030b01c0988101c00760300030002005a011010500c152003a030b901d00c0d20032031003595000449564410240814101c88681074a544104065540404044940c642c0a50380c2c1010904a034405141c1e10301c0e000c440f03d19a0245074150198907008080c54a082020f03411782c411144880002501d1030902910000d88698002120380402c1d0140078034205071245800c062040d4925030380082c1d4100c91427400c00c04040c0b4140d000c3c0041d41d048036400c202940c075580e00c908019000b0904440034800b8580d55094a00b9402c0d07941d580703002c42601c80d0b0010031919061502459021100d0100074400b581008610310058440a0051648540c0104c46200e80d41c0c0310310000c0e802c180700c2180141541e0080d900023060650102e08010036900e80d48541c00380015007800d050996200d4004d1402059 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 944765566 1250 944764316 944764333
    0xf1403070317061807020607180f06030f09081204060e011a190b0f0c0c040902060913140a06331808010509030c070f140f120607021f0509 61
    0x902c034800e56540414018004156140700c4040032000507800d8980c2801640000104107001e6041703840d131401c00c1c040c8204003821514059000028441e01c2c020041050748030015174000107502e42212801a43c003103c4035031034806450050070510f01c210b82c03d943c1c86080c021158201070042c42070f008c8841a06032080d00142d40d51040c4840542c1405240404900644002a0121101c80500803014130b00544607038038000da103a8135241c41c07078000072288100e1500542200590b120000c5402d0103006482c2809030b084000003c0c001400005e060b21100544d8001300458190194031a00540340303980d041080740e0043c0c407406407080c105c500c610184da52010201c11112030044a05480c2a8854007100c0400d58840131598251241550016040d91000c176000000e14028018003001d420005444402071340350001c00c04c1c1e50480072518070700480345461007400e151503203258094045030550440380d250400c5034009582d0811030004d005115003000907605151028052540031714241402006100d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 944766816 1250 944765566 944765597
    0x21060a12023007152a03080c0415020a060e0c0d150e030d050f010812040b09010e040c0804111806040c0c0507151b2604080102070f14030703 62
    0x850010302205490010b094960241c402c00c02212001d400c81d803941d10001074088001810b800750050385038a4100c18040c081c14880d107804110344480b40c06140071103103601c80702d024640c14400c85d004521307048160b03e1240040b64000403501c90b8244251000c0240c0c01e03c190074075840302200b0340940d501c00100c88481001c10740c144e1500243c50700c0700c0d40010303061300d803441c805103540e12601d501b03100c0d144c0311810002d0340c1c440e4100180c0108003107401340941c03080d03008204021b4030542c080c1101003031000c03a41c0c03120380c2d22602e2445038140016004104900f400700015002c0c1c142120110b0b014141003c2c403001c01e00b4005584135202d460034802142d02d0300d4450810020345209c4100d20304000301d022a0760081042040124010104462400c54043c40c802c0000d14030000d40b100e00300c03e1042010040000380c96034407080c0510030305200304000c04c2c880e101c00441078469984984215800801d0030030500806440b0400a14440c100760008841054066500c80c0198000900860b02928007540d21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 944768066 1250 944766816 944766859
    0xf06010605040b2b0f050612070b1204210201021309060602210706050c18040218100c0c0b090f0d0209010b0a0306031212051f14030321060a1202 64
    0x1000d810b11342d00c1e0720780340d49032040c402190890040200c03104e498805201340d40c284507880c0d0001c0404240a072030f0490030920104e60390b00c07401c00b0300b440b03807041c020000f803e00109400c41d03682c1c907040c086000c28081404100034041e40003075940c1d20760300045500002c0d4054a030f01c0740342c0c200c0b44250090f1040340c0040340240308031811864140b5103241e0401c10b90000407001d1181506c614614a5140e440386083c0314540d10110308000007600452040006012214400002c0c002200d0b048030049101000c090003180c51000032800105440c42c0408045803c500050161001130401e88143d200800c204041100d0800c0000c0042d4001056000502102006c58010040040f29003008646035940343d646124a01c0d10000400000d00158802d183c0001d903401041d070005402d004c140220803483d0007803131449100f441508e0302044d0b4030380e0190b000c0d02e0900965281c2070b100300340d004941c039154216414000045030250310520568502040006504401100701a00a00203030034822a03000716190 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 944769316 1250 944768066 944768107
    0x90f190c020c0607030f02070602071a0a0c020306101706010302090a0209211005010915050f3c010c050d030203151009031131090507080f06010605040b 67
    0x11402102c10301c0c0103689880004200e054402c0d55019038503811588020b08100380398110b082150040ba100300700491100c0c02200d0303020701e10202c04e5a12040344000f07455840042000035018094202082109035105c00300034101c0300b80d000000c604000900c40151030318002d0100a500500d00c0000c599001c0196019155000001d4258042d80e410001d6044120050b0800842d150307005582c0101028180d0040b18010a0860b2043c8080800c00c0007495100c010f900a99000304010b140700c410540d200c0048045050400c0074400d407602c14290500c49180803480c4d1016811118140d0203540d520406000143d143c000d0098103c50240e80d80407800b035440a0010544582d5070301e44200d01c1c0d03482181d1004182155210025040d21310328100c503c2020000c1d420384551410b40c0200306500038400860740314104170290400764580d540f5040000e01c0c98240141541c494180007085403200001c90900c85984442114000e0383e0b02c034022283c900c682c0c01102d64010707040c0441d10b17007054520f00440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 944770566 1250 944769316 944769341
    0xa29062502090c071203020c0a0609080f0d0605031209011b050a0c1401090b0a0e090a02070f0b0f0a06150e04060e13110f01020a0f1401050411090f19 66
    0x120200c40360780000b2640101602c43c84169400001c01c4820880c9154141c041c42c0c0a0303007030070350822404200d0140c13148950380000c3c0049407aa0240b80800132410200d07110007956041307054940700000d004000400540c01014060b00c2003083d00c0c210080d1100a85101c04016500d03c1c0305054800740d90390f800032200c00111280e100340407034140041c030b02e065020068003c038141c800060382c64a000500c0750589034400b21a20000304650714859034070000000304145c0684104c021601d58404180007440381c414003404c89010403010508002201d00e8050144481203c04212912650700c6101268400c0c442c0e0406070a00c410000102c500a4070003e900c400003c0002a0165071201c030b600d5100000c450340502880007000d04020066030800d08a401c0301d0948203a00607150b00c5c00041d585207100c12004e04100b02c0c4881880811041610480c000e04d40c060092110741400d00d40406503185010b040761180340c800000070704550440950b148110703e0280840ca80054819103d0018804107a045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 944771816 1250 944770566 944770627
    0x40b0403120c3905031209011e080601170c04141201090501061701090507050427080304150b100e27100f062f060a2906 53
    0x2c2d001c140641c65015805003030710a00c00e505040c481c014000015248880304201480349400d00164800184d85a0036201001070386d51b4030300c25240181c0b002144440e03074442d041030010b1119282036006130910300a140070b0300c4529051501c000e040c100404120b4408009410030311081028600c515102c0110321005818400851b45d8407507040d0039a002c003c410b4403940e4503800d00304052984c142070940e02c1100d4000800c01c1180c07558038070342c440002d40703d1148202c1d150001d440b103c0d1f0211514842c108004004900a10b03280d203060b00a5400480742580c054900c00300100300c113103440c0518044400010400d00307001070a1201070721004400202950007000601e5001c0d00444028080f40c3e0100c41500000c00c1c40c60400d41078920382100760000104c088881c0403c220a5030011041044994016180c48825402c1c502d600107003000464000a04c0c440c0300b00741302c040165940a020800c11888071a800940c1500b100008000f0103440507030000420040044c0840c01000041203d08040015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 944773066 1250 944771816 944771837
    0x20f121809090109030905032805030f120a0b01050412030804081303030c0203100b0a2d090e011d15090a0b092a0112020706060807080705031002040b040312 69
    0xc205551001c45200c202c581d51001c82105243d0000c028000a00040f40286940200d0030740c020400400600303848090305000903e002001400e2082d00d202c01a144103058840b448040c2d40c01100e07800750341e1010f24914104210005505ca0011981a114010030458900310942c1e0100d030030400c000e02c1034503400d90030701c12400810b0710340401c0c3d402107000781d0303038130100440c41d00401d4240340103102c1ca1200c0e2071400000c00305a40f90011310301d040b183d1400c0134400c1080039002e244d21600700040311748440a640316000c90305204690002c0c0030540f1800081100c0c0110380301d0302e003d440c604001d03407000d980002200c0100d556440c03c802d43c4107030018103440a003483c035511000076600c142e17480d104c00c1d002043c0031080146a0400b0154035032507a4884201c200000001815000d5190700031103c117a0006004003d00c00b841e04003000a007072010440b94240d031350305182a00c401ca00c0c05403e2282c0600c809090003507a6030300964045d24045d0303c08500c2d00c0c0c0395070f03204068880381622002c00d20068101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 944774316 1250 944773066 944773069
    0x807020604031d0f150705060604062103031b03090506100320010c0f06020901080f07120b06090307081c0e0303042705040c0306050603061e090106050a0b0d050106020f1218 76
    0x1002905c60500031006078643e1505d00d01741d401d00c04018601d0f4080c91600004014400103840c0490700c180050f5002e00100d02c460808401920003030000c035060720b25440d81c422203540c0c158021050a40290151540b40d21200b00d048a02e02080c03202409202e44002402080061aa0940e4048030141041804c2030a00c0d134500b0040c034a24a0280c03162540401e1152040d40c02000f860b6100d0f02c8481c010761186080e100240084040300c01910002d980c42040000c030341c4947c0200e800e2030900608070746941e940c50b1316050340e865164103d40e010b00102d030351801116004906a03080081c00402079402c1c0760a01880c2c0284d000c00f032154100104a495010461070224820310303009038054036090405c0e031304504100c0c09885016002c58000e9000c0401c10209407801c503035902407006042119200d41c3c4800801c1400751000b13400860744201c8ac090009541c00c840d070300a000c4c83d911210103024681e40c0b2001070f40c442000b0386070f0f552643c00c400c2c1201c0d000040180100313840c19000021400012841c0c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 944775566 1250 944774316 944774329
    0x90e1e06060c07080601080124031104020403062c0a0c03020613031a09010615020316020a05060408010b04140c030117120c150603030f0d150801110a0807020604031d0f 74
    0xa200c4100c6070000c4005000c1c41c7d800b80a47e003003c521245030060020800c41e80c9003a00900d0744000703030030070b02c1d100310080c1103698503011100259017101c820b0210800310441032a0802c03054140c55840624401d1180b800000030030040041a00014680c0480380343d0740034040705607c080c80c0d114880b41441c0b0007200140c0d003080c844c4001100c12a03a03001a01d040c0c00d48a007140c40070381028000405c1404d140d14582c1e40081140d200e25003280b04800c56801520210701c02048540080368050004100404d030508150310104401104613803d00040d800158030700c8000d003065552501001040005001044040e181100d1001d942c008450203000c0e0a00800e0650b00700c0c5805900d960400c1030764014040d050303002d02e508420110080c620300a141d51100020f4400c200481c580300b511f40d14401100e1300940e80303480042c80c80c4c038004d018981143c02c1c01007069010820040c0443c0000010030307503ca1000599620960349515003155451307c8210a072107800007040e0031035000b140c45e904094039032a0700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 944776816 1250 944775566 944775569
    0x271806050c1218061f05120a0b010b1201241b120c050f01060609060c0f02030105040b011a03060d15090c030303020408011a03030a051e03090c01090e1e06060c07 71
    0x100203080318142c90140d19070402e24045d02c510f051140040036900010103c83c8520708949003110524020b5032040600d41c1000200000513001c001074400000e684c4455030020192865038410781151680c80e1259501c8580e03c6c2c0c0c001801040b8969400301ca002d00071101c481002d0100c60000700820030582d1500541c440e11300c4d00d0f00c0002d480d80720101c01c201040001c04112440c080c028800310b41081c200502c0150386101b00010050f92440001c207001118007040e856170f80150003408940f41c641490b03d4840c03000c0c4607441000301913141a2010990010550f0300480b4003d1102d51707048420b8440b031032144c05100310f03112499658a440d0340010701c4829010002c1d80700b502c0250302e943c40d0000301400c48070641c04901c2040140d5001010b02d135000b000715081c1181505103161a80450020300c420401c202c40c01d00d100080000501c42d04400025102c84688002d03600ca620381307511400b801802d0b14041ea2003284002c2c0c5d0350381c280368002c070140020754482d402902c0385040c6200808e11600d0b240c0203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 944778066 1250 944776816 944776831
    0x150825030f0528021f090b0d05010f06020d05030a2007140609011107060903051c090204050601090b1c0216030c11090915090115271806050c12 63
    0x80f1610030780740e0512103141d41ca0007035203d0304000c030f03203105402042d0000000c00740212000100d50007480014001d88030040980020240f044d101c80c0e510b148070b00200400c0c01044c60b060000840000d2107480001e01024016160352658290349490316190050840c030b105c0e182042941207007400c00c0304e041c3c2c2c1c05848903070b00801c90b0030719003946000180e00701b06002c0c044004036410982c088045200740011903a0060748100c000800c507010741002c55507405180303920502000c1c090b409903040039644e0042861a070017100c00700306a48891006440ca20800c0c41001a411810302c240d04140c6442c007200e0b02c2d41000110007524190407034500007001400070404401003980d164101e002e003c51040440c040590680d1600c111707041040c0c880da925a544d40c41c076141a82424001951200203421045941010600030750549480d480c400031611170180c1d840c4040c10301010060840c10250042c01e410f04080b091401d91a4010384624010388402480d90601c030f03104001c0c04e1f1546000064603440b9110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 944779316 1250 944778066 944778073
    0x9080c0c0f240f040e1f090b0d0f150507030e06090c22060f0b0c0f0111091018150207080c01020601060f12060810150825030f05 57
    0xc04041180390075000040703038003550b1040c400d465910072810010400142503894a80c84544081d0111400e220707541103a401d400d982002d0005452030f1013501079a038503c0a01800d465030b2103080050449460004150b40309803070000720008030b902c4200c214590341c002d0b03024500c6000404404002e0f03d0003500e0f01d00002e660f69660515524043c080d0725008000c010181500540d9000028083c88000c14100e040e581d0080031048158071a900940c0207002d50a0802c400d0350f40c0754501019038200c0214140640207507440030302c100e41c040c80340b12a81c040c6011105e05110041d014031000c0e8007a81c8581e424000e90410011540202500380c40080074914400c0c2c072880b600034002814480703264490989603005081411091780c01185040c156089031a209094000c4c01c54110760b2090140c0c88070b800e10340b52040120b246100856603051041d140b4500b40184444480c210411000510410100d904958007a1110382005000760002d22030700c0d665003030000d4a907100c001403180e5442c07080300c1561 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 944780566 1250 944779316 944779333
    0x606130f110d06050f0d110a08010501060822030f2105012d0e01151b030f09062c120f06010303080a05150d06023109151809080c 57
    0x3860f01416002e4a41030f1340509000c10300c2c0c00800d04d641c03074041e0010300c0c07419107400f0810240c844503030080091500c3d070007c0c001543e55590150548006503040d03c005004000b40446062104445503500380d895540c1140001542008403160b00119009442408042e005207400200700d015041c007800e4503003407800b8128072241c0281211503300c420444011080300d01003001482c0e0806940c11152060074081e11840c100600b02d0b17102359a14944003034510041441018180d0007a0751103840071288d1543c0b2991516441d090701d03a84001b80070a0b102c180404071498004400c20b8890b00016400f52800400311140f00c0c806081c0705501c82c0640040c0d109400400505071301105250700281e40714806c009505041c9114805040e508901c980140c080715000b808114a50741107a04032000070351001d91801d4210325202c0751040c00034a10f10350060004021507582c5143c4140000008002e0300f00210701d01c0d260070402c007035070a035100210321b640d82c1c95014045072415004021205205002c0c00054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 944781816 1250 944780566 944780587
    0x90f0703020d0c09151b0f08040b030109090c08030306031009020f06040605070b1312030c020705060c07061409030a0308040507080601090209130605131107120e090906090606130f11 80
    0x80c0c1ca4070420806c445803198025128403003c5486855800210140100307080b4244070540e485550300c04e0b801036900000000b46900954008501d55200b81d41104001e50384000155582c0810b0325810781c0f68012610520368240960700c8090040c1c0702800c5a010700000c1c02c005000d94200703600c40c0000c10300000b0321104105180e030103039030303c8007104011540e82100c0d900d44000140d40251248240b6aa401c11132510500070080b09008000042100f03664404181510340c503006648114000300300c005982e000b10355620025180c9001001e0010709940004d030f00c0890328414003605c1502c15025012000c41c0d0140180007490107000c0d01d800150741d840c400c00c148003c4290b850400303d403d0b031a0040620090781c0e070410102d00c1a91440713021691000e00c0c3c80180e111f02c50b82100401d02d4041c0c6005a07003c0750400c41188411030115034071a41507850700c6085840c0c08048441440d6a005240043c0d039511344103018140c80007181e500060b10f900211001c90458404403140c0c15005c60106040248 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 944783066 1250 944781816 944781839
    0xc13060b04090c08160c0321060602070f0509010b0f07020105160b060901170d230c16060503040c0303050d090b091f02070c0e06010e13051e06090f0703020d0c09 71
    0x401159a901742034a031204400521240001c00010100f0241d003070308000405000c0c0a1820142c0052130411010307540f00006940c1d105584128145440720781000600c910348a102c09040700d0005409034903101da06407034400350340d0115070100e05111051160300c5403423060403507588a09100d1b000d0086142400b03401c0141c0c04805038030004d80a03540401c1c03017114071004280d5056200f60381c01c00c81001c007191806010f00c24100070102e10074003404240350300304100c00140c45000f40d0b10014190035940e01d61004654502c4201d501074880c400e5200c04000080c403840c001c1c8100b0901d04c1d030019080300155a03502d203000e000e40309003000350b00003204030a40e0129440508201140324000311300d402d21554601d010001a40b268100310214140041c01d1a4043c02685817549030040104001400350556900240b1080d80d100384ca4051a4138000c082c0e00358507039202d01404000f410202140e03201c9036024404400201300c80209a000d004840c1150002d0107048074200c0c040d101c0032946400c00391078261 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 944784172 1106 944783066 944783071
    0xa020f0a080d1d010503070c030e27090c060a0c11030f0d050a020105060418081b030a0203070611250f0c090605040f09050c13060b04090c08 62
    0x2441503100c000e0102038441c40f030302d921804040500445560000311401004646160302d5600428003036070307180c0703031110005014036981300c00e11592142e2840f50b1007480340b90384040300c20300c07032420740900038201c121400740c1b59a814010103d2004040d00000c0d400a0714000d10906100c0c80d64030184600d541d6580c110044420b84800303204000d180358010b2004000551811020400900d81401454101426042c8411010b11542c86505c42c550188400d11061341052003000c108240c00c1c00907100e0301015401443e101d0201d400c0250a40c0c00700821405000001c00c40c000044030300d86030440c10b0b10404c0e0681c0d80b0b0700c2c5462802d91440c0c025100f02500742e20b052007000429007a690400d50036107106a40601480c180811135100382c1d80c0c220002000c0f41c001016000c0c1d14180542c0c01c00d42074003050f43c04241c0703030385c0c900c0030020541c05a04056205620b81d00200d41d060b400071145034 = true := by decide +kernel

theorem cover : BRFrame.Cov 944604316 944784172 := by
  have h0 := BRFrame.cov_init 944604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 944604316 ≤ n) (h2 : n < 944784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
