-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:53:36.781098+00:00
-- url     : https://prove2.me/submissions/4a250d42-4725-4a70-95b3-05c799fec198

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 391187050 ≤ n < 391366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 391188300 1250 391187050 391187053
    0x13020301021b0a03020c0a0e0f1005030a050a0b0f07140307030f0218180705071502040918062703050304031e0c02010e190e070207050d110f040e0618 66
    0x884001c52007661512802e000c108000d400d840c0d02c03508019040c000d000e903031544a0f46414005002540350381c0d80b0706400c0742d90001407082075501d0400001c259421904656414400e01841d002041000100c40110504c1186c000e0070703a0b122414008400300d400c0d01d01001080008401031801c240107070107181c0c0f02410307150100d000481000c0c00b0301280d10008400004200d0040d080955042041e08441c108407c0e90890741303540f404d100020000e01808178020843e88200901c240000300d5501030303401a2203000da0030400d219481e89090b680e0ac14584045034154145040b414044181c104103c4000c0144030031904a0040350f50102c80b1a40020700850a00489210164113608601c4201b032040480c2d40f5010710350341250001510320000100f40f58410600a00140016160a4896000c90341c01c4e4941c5a1642c603144010307400d040c05504a20b4211800700000418840030f200f04122500d41501d203200c2c41c0f40d03004240310030303100103d4059007541c0c004d2000c640307a5981c000d146400c0921900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 391189550 1250 391188300 391188307
    0x60b0c0c0105131805180604020609040b18090102190206040c0b1606290d02060a2f06011a09010206040201180b04090c02010b011706010e0105041d04050c12061302030102 75
    0x1d09090b01340103907603004500c6035150104900d1401009440c4440e402c244000e11241c5096030008003588100e24649000d00d886101a44c00d0f034541c82000641203568450131030f1036140458486000350040c0383d041d2021300d0300030070180300a40085981401140c005c80c0c3c1c0711440d810700050b00da071030340700f00d02c54424018a01c0d9a000821890300c41c044c18000d5200600c0c6a07c00f07070104a040340030304000781c24456000500840c1c0140e03503100454403103010b44e041085141340346204241600070141286d40850600c110040b900705800f0a060b8140d075980e00c035030742e10410f006c1701c440180c0c00b03860313100c50150b03100a0200e0090341c0625500360300b4070f04006001c14840e071120b02044090700154003900d0783c5602e80c4da2455030f060702070003a041000001c0c03130428142c00d03034114418680000a0011030500806c00b0103203415900c03031002c480180488420801c14030a5205c00320744400000c5030103540c40d01400d0f41031002d601d0140d43e814000341104000f00182d84405e10b80d10171668100340100c1c0d1641d800c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 391190800 1250 391189550 391189559
    0x180924042f030a1104051f0e0403110a03030b040507141e040f060e031905030409020d020d02030f040b07030e030a0521010e0103060f050708070c0f0b010f09060b0c0c010513 76
    0x400000d000c030b61044c4040e0a80c08180010703c0203440c00608910400014040030444400007015400c080360203418030b030b800507115801c003a5030801e208504003025008440d4001e090641540100340b180030159001c1091341d613054802c4a003201180719190456400700034180410502a00103a0302070000034446142c113070b5840514001e908954032403400308500b100030b00401e107018040c03040b820001540c1c4100310b191994501c3c0c0c5900c1103010b081007c41d4003240405007031b44c1c2c0d50b043d0b50541c00703407043c210340d6400c2c8101401e114140c01c440c2100e40a5040000524841c0319025030342e40d0b80750a6004505280c1032200035211500701782c01c0c0a130205181102803030503480b4a84403d0080c80c5803182c0030384070350543c18000b060324044800780e00110b040c0382c24049043c2e80004c80c1c2d50f00404929004185000500e04003548040309000909101c1c0c100c0c0000c56a01c0d1070950f01d40440313000c035030704101e010761300c2d22410458020403001201a03008424800e07410b5020300000c107070200c07850b0b000410a5464 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 391192050 1250 391190800 391190803
    0x70c0606081f110c0d0516060216050d0f0206070f02030f04060816020f070303050706090b01060e011823180c090418150b180924042f03 60
    0x64481526540c0c2e551081d41c1c2c00c4070003d104860900140d40c050324540800b050000d035076415a154164100180020b03c404407042204200c02c04580c842e80655552a46d0449110028130704c0b2002d85490188003000d20001c3d009041c4120f401ca0b15801400c030303d507246242500c034401e4a04144041d030000b004035000d00000200104041c103002e8503841c1942c2083c2103a1a2401c406c01412010342d4442ea40c40b003200e1000161160480360701d80b60a0307a54000510b8100051715070180014400c51300b000000c2900740d00890f04044800c800c1c0d8a100402000c003d10800a82183c850f8442d40e5031143c40391401e50002c100180d06101f005860091560180d181141038a0400c13100c0c030403002e0001ca070030391040c40e143c041c40751f014940c2507a8000e5000541c070360901c0b40b8202030140310101d540304600d6450340c6a07800c072141d5008007107141d0412407400c0b0107041d4584000000c09065986540014002e551080a1300703405590803503444405c2c40c0f4080907e0b0480c5885807041e0700d00000c071800104551b80c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 391193300 1250 391192050 391192063
    0xd06020a021e0303090609070605030c2a1b150904110c100c09050a0b030f04031b0302060a200d0209040b15070201080a05130f02041103010609080607090e070c060608 73
    0x107050025942c0c0d00c0e15000050411b100600700740145e0b00040800c0011a520000307a0380c01441111032103555404400b01a074080d0075001c0559450101c4000c0306191060109480440001c01c4141c0c0e254005400c04012015204680741c1d20701003014407820805080c160712200c2000740c403480c1c81e0315143c03c002d000781c500038101c1c105403460386d2114032060f44564094801002800305407800d00b05981404001442808028007a02d0280515800201814800d8038900c2c0c200c40071a5041c225400141402900d0b40412558a2501401c0030b81120298081449018502012080482c10082e2095140001e5806050115806130f1a42e03080b6407169224900c510540c50300f06a00e95031034106200140070000004e00a2480030302d06400c01100e14403038199825101e900c4007410022007881c0c8000b4004120f801424041c00e440031001069098000640000341d07114141150300f103a4441d8030456101c1124082c1e0080c0e1916100454110340c05a40c007440054440c030004100f45072580707906468100b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 391194550 1250 391193300 391193353
    0xa0e060615031902160309080c0105180a050a08070501020c0a0608070f0504051f0f02062a0f0309010b0a0f0302010e010e0616080a110109020a0630020d060509060d06020a02 76
    0x9003d2003105c080607044281d41d0000d00f0144007034141c10303941c2c00018002e07020745455540c2d00d0002d0104110666181c00d8030002500000b04026201b903201c1e11421340d5008203015060151085200b201024940161a00c0803541c0700c0e41c48070521381d60407a0403204155182407101c103101c01404080f840b59220380c204602c1000d2401c601810782a11100103102d0b2401c2201e08042d900309034148450005c400c4003100848260104045045810100b0f150340751098262003d0626400710500520701410b41003070444102c02c031500b480890315048070711401c2d0810b01c0001e002c00c0803540c1002c080e5009104425201380c00070a405d0400c031185c28070600c040c80445040381c48000029040740c810307810070b20b00c40300f121107840200301840c1e40f540403c41442c0c0340c0c024031080c8100d00c924180280e0000048900fa940400c007010700b640d01c188800070180d000114884240d0b810b00001107010709250a18a1003200010003e1443c241c1d541c0312040294004100007003103000d180d000810032035000c00f80c400d014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 391195800 1250 391194550 391194577
    0x5102304080a0b1311010e01050705010212010f0b180f01050d0911040608030a1202181804061a01020c1201021e0c010e010207211b0302060a0e060615031902 69
    0xc5482c901407404140c02480c0b512840c42560310702d40030548202c2540304170f910030b08008001c80804401600c6074080c58200038100e60000882d01d200c0400c68884034104d5210a0441840980740c0e11503031038501505400c44000c080d03404401b0000d140c140da005600c10010b0400926021620803008161150781c942602c540081e40c046013080c0c2824441e2600078044035010b181001052480102250380086800c0000354000c54003d20b160ba942d4035022035142e0080203076401c80e4040700308a5582e642203905880705490b001410b88807a19409002800000583c041c0039854080020880350b94140c080c00b408941d424040e60201007450141c03480c80c101d059205a40340d10090b104035096508803400784410341d0062009000140350b070511500d07002e040140d6000900c0e1600d40450f00a180f10504400991122480d1400d1540205215000300c0140c20223211448482c03c1c6140d560344140c43c4a80c103e034496035002c40c0305035a030020f59000b54408045070a00110a40750f0001d076000001c80e0840d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 391197050 1250 391195800 391195813
    0x81311101e1d041e1b12020301030201080c0c012009030f03090a18090203060c1b0d1b0602040f0303113003061c0c0f050102070510230408 61
    0x440d55580652240c4010030300c0e00341000c2c5040c1528020100e40b011045026944988100c2c08070350035151100080201001d00b00f20081d429821011244140014240421007604807648500c0c424000c49041e00d8068541e01e586403104c2d0101c100300d501c541a00402c2e5542c8000d40201c10340038440c0c03141c020190034929921017006400301800e2504040b00801320707610402c4030440948810003040c04440603846691840440000d0000181c106040001c2d41405094108859982c051000d03080c002c81e4817803580540e060009510f44c1d140b2100c080c0101155140340003c9801110501921013684218070160520350380d0003490f02c1e908000e80049010644012030766446500811500344040e6402d407995105c4c45120494800d1690440c2003410f075503c000000034050f072030325403003441d24110b4500f01d9124404035040c03003070b5104140d0103860f441c103004030400141e0390b100007503080c151100281010f804034849841034031008107a90901160b80c248400301e101e040701ca80c01030002003034a80043d011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 391198300 1250 391197050 391197077
    0x81b071e051206010611030f0f0409060e04020117061215040308070f050f0a0504030b0f220206091c0f06091104060605190909020c1c0f08131110 64
    0x445840039084079000e0800c0c280455000340b00010010304445480c1072004c6040d000000e00340c114400e0000b11190b0520006401c40c915803074000070812188044c50030040c298840001111000042c3c0f0082e0005200075000c810404c4e03070b8401c0c030360403c1c0010448001900c01d01619420040500d551036003c520905c20041410b80084603251301010b5464503401c40f032005800600603006014050020081c0440d5400e4524058003c8502564028040c58803910b0060080e102d5503200b21030005c543c40418000308440c4840078080001c60394001c015504103004081404003a42c80040545a0f400d03003141c3da500400d00411081a0341402882c022820782c281b030910301040d1040d10503150050340351090400c06030354042d003a519603000458141c155202c1c0354108a580602d02d8105a210b01d100103880b00c00c5002c00600c0201c0c41039110f03640241c3d05003070001983c00300410b43c40a00498140c0c4002140d1001d141c10300d244543c8640268400009074101007030036803100039442d00209545051035803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 391199550 1250 391198300 391198349
    0xf0308030f0f040302190c180504050705061602190b1c06050f13050403021c0e0108090111120c04081c032d0b04091b030b0f13081b07 59
    0x980c0407010b100003084a040c59500250b41392400040c4400c49503111070150100200c200a00004049071004a05415411078440000301025501250f0ba8820842e0028071030070200152102c1000c00312441c441d8407150303024021050400e24204a0100c100f503408203856081e00054075584808548142c0442c1c95003034840111340300307908030174070403d481d03d1503644550b1201d181000154489001081030740341c52030140d18100000c4081c40c1d420f42550110030040354029070484001a0980e01e8460588484e20413a00b295100300b06640e00813010003910b42d01404030000329805c07081c983c030007074030f01640c3c1c08000e4100002130a413504001c1036900c0d0441a00d40c0b6020300003800350351014400d1000752181d0042c8604080c0c6009441158440e82a0303280c56135030354800d03080c09811024107101c3d210b602a043d120f41800c1c4c0000c84040c52075002003042d106007580380c640300fa4584569078011065039150190765801482018480410454a8940b001c90034813000b0300900d10110b1003001501c0c5202d40d00f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 391200800 1250 391199550 391199581
    0x903070c0e010b0f0d150602060a0f0501080307030e03030f04060302091219110103060308030a200304050c0603100b070f11040e03041a1902060f060a0303020606010f03060f030803 79
    0x450702010000501c0341030480c50441da00c0c00790014800ba519030400c41d082c1d005d0100b00224a4240350860300005100d42c0100e0003a2003105640410000078908100000c2252001c0c00f51440a0f802400980300190090b030002c440240014201d90609040308802c0340240d102d500180f0000c0e8010400745a1030500c09a80208020a003028001250031082d45103044054407001070311001030000c044c00b40c0c0e4082ea00c040040c5402581e581ea076441e1200a0401070218504210f129048404880c41500c0c20201604d00541d40035003c2c1c00e01001c0881003054a8102405245811304103603030002e0004503e4000344180c2c0d124074100c4118030681e0030140040b07100d07160110f02490078060051800f070400f00c215402d079036821607204407189001c0c2281e000c60007440e224000c0480500010072409400191007071103540078178995680743d41e807001408694034040c03200038050b0b070140c4042040c960140c3c50306400340031103150004440c0d98038402c00c080081c89a0040c0d40c0e0013000800e01c04200c420b03d511 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 391202050 1250 391200800 391200809
    0x20c1e0f04020c19030f05090319110d0305090a0609180509010209130b01030501090c0e04020f0c120706060b07211206060c0203061302060405120a06060303030e1e0c10020a0503030903070c 83
    0x1941231080c04c8012079100c0c81004c010081c0100d0b41c00715581081403c01c4107401d1000040c3c21070240040c9440c018269900480e80c5d1442000c00d0340d4000364092240340030406a8038006004001e2180b000301450103044081d000300e40c1550240540c10b500d8660f030340d100210b40c80300d020205d1441c0d800000901150f0b41a005459040d0510104091907500444c1b1003480001c1603c0040c0d03154001001c0c03003440c0c021505602007034002c40f5030400300f00341120040c01000340105820482250f46007401d20003440b465200801081100710141c0c600d00046201c1d07000c0a07100e0400c20410200c44941a040319060780240c000f041074400314100f941020007100d135012350040c00340040c8640940001b0054040e9204003441b40c540100740308000d40c07051000f94500d690042c0b003841a262680f80240103070001031240701c502c0c801c1c07080b20461464081c410801c803190b080050045198040c081c0207440c022b50101c0400e610420a85100080741000214882d050076006507480d07611500d440710181016502 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 391203300 1250 391202050 391202057
    0x30f06061b0309081002091008060906040b030a0507060909060501210b221d150a150506030430120902010c0b070807020c1e0f04020c19030f 62
    0x1030112603040750124024100e00350992a007285075280441d41d180c0103402045950040e41c4180c1030082c0150007070120102d04503543c0b211640d12603000c61710403d044550580c4000100c0105400307050541c82948408009030590364024030b00c0d12200d107443c0655019000041c40f000003004800c2c1c1c14840c9401600091801105000101c010021210407500500045640d54031091110b1f0f07807164855801c1800190a003400d00201a0710b460041400700071001860010030340c210459035011800b805100300c039121041480e00c030001c010b40148070120f04e81c11024115031021843e0341e01c840207036100b40d00c207050814081c1600315043d803482300741c0c14040da0320402c04d012402d5965005820132210341c14084c00025210a5400100c4a18094510280035900028240120968003a0000d442001c250702210300310840642480582c0300035801d801420850038841103a54503003c82d8014046400400c058100018040020304126500c2d41c0c4803080f4007110150340030140c00400c0600000301c00d05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 391204550 1250 391203300 391203311
    0x81909020310020a021c020f0c09040807060507021e070302040c080702060103080c01020f0438120a090221060601020105010b12070903050f0307031403090309010503040f0209040b0601030f 83
    0xa000c070741d48000780c1c0740e0b1840a640100700300304030320702c200100300009500350811180850555000f82d107883d020b80000d80c0f20301820710380b96080d092007036800c0d0145034002c290610f00707050b5440303110007002d01074001e40860160742200c0c09004842e105400f400b03144103000c1c19050746188100400c40f0242004042440458000c11650540200340750341100c0e044101c80340e80d4100351400c4e9009202c1c01030810303002c20000c40d000c00c141500756480d9500500f001c02c40c902c1202800740040041801c0a080c0030f000000b044444031310300c2c40d00c21880e04003808800202c1c0408490740050b50f0000b0042401104420703050f03000c90030320740c204007da41264003070000300095414000c11090384d00c102d00c00c11082c1c000c1e2102255030b0174481e408881c000c5810030103450b84400d441c03c4c0035440782d100d28000c0e070001c0c03240400600b150b2030500c200c07800740030030100941c5810b440400555082d00000e000744d925440640310b40300540c0702c0b0301119119a01c100301d80c2c0100e01e084000981122401c19140005620300f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 391205800 1250 391204550 391204553
    0xd121407080606030a0b13020c011802060a11100509011b08070c120c060606020304050112020906040608040f12051b0a0c03020f060d0e1b010521040f0f03081909 71
    0x4041c035008481070700c00c9a503980d0b0300e0103850060110030009035048280899401d40c20361003580601504450003000b80010020750520b024680b03101000654440310400007100664094442d408134600801c099403103c413155025502100c8040740d0ad018180d44451199a200c1400a515407102c469401d1819843c240408001e10540c0c1781d081c01403c80502001900c00a80118803090540c1e0340304805110054546d04000c0d100d4202d4031503240031484100d5036001240c0079009545682a0140041e403c06203008401c48035414050819150813204c0740b200004550080c40b01c80001c2699158590740740e0f004004104411640b50001c0300541049001c82c00040783c01500e90222a01220341462141405002542610816000f94404da18009094032101c001007404980e1030390548810503440103060065a05106201c1c02042d030301c61405003881080444040c198003d0b008803207080703200805035070314403001e2854641680030070500010000b2a040c50000018101c1b03912209201d800c1d440e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 391207050 1250 391205800 391205807
    0x60609060e100504030b1003050c0a050102060c03060a1805010f05061603030914010204061e0c0c091a09090a02040509160306091a07090602060108011104060513080d121407 76
    0x8031440d40d00c19250300c0800b0568603c201c0944001c0c581202d0048040d00b071244482c11810301908c001c58290043c0b10341c09a0901d0318082d00c404840060700600101e90351201150141c0d4401420380d907100810a00c0400c009504084c003e5040f1a5440005101e504000c4010107028007a03200520480b02000300e903070030796140c0c2540c95280d541810041102c5000d8540301c1c107400358200266130b041d840810700140389584050044008008002241e05810403801d01b25180c3d1142c2201904140140404001d032076041d074082c01c180000303034042c001c0540101d40003d1080700d0036110031856078800c0400c007056261520816801c035070241d0007440c50b101d500c081800b41174554400600030564036500340e0107204c01c041c03228410307481d401080041450320b50b0b40603020907540e00135031005110f00c0300045200101486101c10311180003403603030304081c40c081c402c69507030b400308038948088501c09800080b0000c0030403035a0b154070203c1c1c541d0b5400e42000d100d41c0c0700f00e03440013220003001881041407001d002e81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 391208300 1250 391207050 391207067
    0x10312050c010b090901020a08011203020703021216230d120e1c05010e0d0309110f01050c01060f23090411030a1e060b091b1b030c030403050106060906 67
    0x25041680d00c850300354001c580141100404a40c002622404110804006500600c51820191203a41c0f259072298001000d00c1816000100540d201080c24405854503542198251645c9001c90701c4c0308600e900609840e00c040d9005914002c0c155407178200c4054115000b911a000980f1040000041612030300103540c41c414102090050003840d10780552505031880203e4446518600111405480e00500070b0003184100c4c046405004505000c8521a01403a0a030319040201050320380d51420401c40101d0010407290306210080080c0000c4c14001c6c09560020100c1c400b11800051070440c161040340704000020352042da0201019440d55100000340c0d1700542c001904d800a00d50b0071002c1307803a2084640300039105203585020780c40303c40c01c0120501e040e640329682c03c1c004901460b080c4501d59409649a0101480a00c0750175441541d070030281030300c00c0005600c004e04400801e4041d081d9844007241c00180e401c00641441881003d00441700100654642030741d1491802100605036503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 391209550 1250 391208300 391208333
    0x1b0d120c050408071206050705180f06070203010c0804020a0503010e0316110904060b010311120f040302010f0e03040306050108030412030c03141204060c020303011802070507080607051c050103 85
    0x9650340403849040c1e11071070030756000d00142001c856805450304080c10404002c403a00f05e0b090780c10100003801e0a0701c200141c6503108000301c6017070148001c1000b0000d1098242c0070b4140c00000500025000d07a07001d0140c0f10841d2090380f512045400c0c41d006100b41c100c91a08400d0081e0f0604210301d00b01800001123441c01322507a141c401e0404042c2c40e14100741c42000c4609688052141d06000501215612111512100341c90800032001103548081b40340c082c890204501c4100200010410318a859100c0d610900c240300000c1c1040c849080c000450300c02450001285c0c0c0007150070300820400b4441e45005d06681030003503050503c0c05070310b43d0903401600b4001f4200075450b4403480806009000d2028030401c0060b4254031f803121252140ca0b120411581a2903a82c00c0c451441e403a580040102da050712000030340d61040000f01030168020f50700c441d0085070707a0303c00e0801c0003400744414407000340100001c1d510b0656400350b9508101c210000d602d00d06a640c0c1c81c081c01040010b6400c1e0710840d090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 391210800 1250 391209550 391209587
    0x204050c070507060906030f0c090b031915090b030606030a0f030903150c0314040305030c09030c0307060804050607030c0504060c03030b09070509031009020d060e0a05030c031b0d 79
    0x6a5900061041600407410010000e02c180e03c00850401d4010446409641c05590100056030400c1640802d5a1380100080c000c00c94544041c05000802002103601c01010001c040b4040d100032600011a0841040107010145481e010b01c4510700e18020380140150271402820756051180010f520307417009490080119041040080400d80501c080400864001c8218502041a000000c01178504030088000291400700d8078080c0310111016907000319050360f1024195540c0020250381035001341a180c0e85841864010880e55a01b0042c0c40050f0641e40d8403035400d42482d2801d2454841d001d07205d038040c94188000840781c50f50003000d40e4200e075424603041003600e519041c00d50080030440c04007900456603008006105410000621040c40c040d000c4501c0c007198400074400701c42110000039808180c03015524003040300341d004661004120810f948090403d9900e2514652092961203815080401d1040a140c00036040c41c4141c2440c5001e40210350381070100929090320650400c840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 391212050 1250 391210800 391210811
    0x8040e0403020a050106060e0906031b09130c1202040510060c150617061006090b09130b03060f010302040c0807020607031d0d02010615090f0b0304020118140405070e010203070204 79
    0x74144200300700410b43c1e8000e002040307140e40f20303c0010008000c5200031401101c20388003041160a0018076141003c107080400c41d0b00881940130408924000303843d14411755001e180c07103408944005001d00050046820000e00141c642c418002601d0380100300c0b02020300702c01c00404c0696084041045010b40c0b04015100011855041d00014041e54000100d43d4640c001200d130601c4000602c1802030241c81c0c13900310190b907142d900b1030300c10030a8000c002c2405018054020380c0d00340400c010340d10400d060030100e10303201c203100803920b000c0c2d049842c404034136246401081581094411407595051524004960f4504440b01079521003001d400d41040554076480c0e042e02c40e043e080901c45850200054640b070000c4400000d000c0c01090042101d4282003c06480039180502c815504a0302200f04510781030345040804001a00000e0080c6c1c1071000c2c000c003802c0d651500c01407840c0a050140240b00c3c1a5400c1820b01080b40d800a00714810300c0110664090303207a80000686000036411500400c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 391213300 1250 391212050 391212053
    0xd0b04021c02160c0305010911040b010c03110a051f1103060f0f130c030c03140103020307050d030212130329010b0715020c01050106170c07030806040b0a03052808040e04 75
    0x83e100031000001d40340484660001c000c014043d004808154050740c1e90504461052081108a90b035940c4203c2c0414000d4030a180001d0051101d001c2e81c40c443c03800e4905d51251900ca80d03080c007013041014080c1280a50369555480054411064a01080c004090031490714002160400c4060316401344138401c00d91000d850341d95004d14200b02011965814000460400301c0540900484500400800c4c105074103170742c0d42c00002e4041812030703400400038031106160609020f103091800d131040d02103010301d00020302c01c001080001c2c0340c070120b10024940541e2a50030452440305080086c907403c01a42007407555522001d0b10410306690344046010380c5e5038114901b51030492050704004080500101b0090310f080d1040d80b0107070482d907030303601c415290344181811044600c9040300c909582403c184080c9001c07a1003210119484400600001940034852001440110166000b01da080e841351149520424000180030280c9800e200c4101c00714000340e8030b081c3c07503028500604ad442da010400180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 391214550 1250 391213300 391213327
    0x5060304050c220b030c1521040804090e010c0f11030c01061202100c031205060406050303070b011a1c02090105040e09030a02120a0e0904150c050d0b04021c02 70
    0x8000d08802000925821034900541452a411480040f034032072420340212034038140866001e0180100800d030702e40400c10940a00c526400040d50100c03448084020400038928030080140a14080c107003032a02c55203049442415034030a10f80420f8140d061041d0160000e4206551500120090030a041e030343c046000110300d0340c081c860003490030350f0901c039000404207640821144014000d0b600e401c180407404009a805100840d801400587d081e00030031542c607100e621041d0410f01c02131020424507a81c10001c0c2c51600005000d480140040c0300402c102024140010a9107499213201c50034001f00040d0014441003c2c0303540002c0c0da800058882031603103d04205c402405105020050901307098100e00c2d07132500130025030380140c81260901040c0c42c4d0756605440b039000c0544c1e510001035030044c05000c22040090701c00c54410810743c6510b012030b0828041c0f0710301c1400960762951039002c40c0c481c60003503031003104100b4056841086154034014030280200744c007002c01c010240c2e45003207404142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 391215800 1250 391214550 391214563
    0x4120212030d06060c060f020c06150a0e0108010e1b061e1303050319020102120103080a0c0b070309231203070504030f14010506040501051e04090609060e1002070c0506030405 77
    0x10495251580100c2e104d5002802d1790442c0b80500420820350700d40d6004001244a0810300000036404800000c00d4441103400b01d1003042c00c044c0032a12400c5d55030501001c000820307000f440310340e511050050704240c420483ca00c000e5084040f50a5814800c03808940c0a20618680100c03000005000c205140360b41022609000307100780c40e03d078000d40c0c0c0c1c0c10080c0d01e0350811081006009880d07002841d250f032050083c1c0b200c030f40c82c0303855500640e427850361740301e08507448020600b080c00003801d245400305086815892081a803614045000764980c80e201454401070100741d1002c1d107883d403881d245520b001580c6141810340c01c4045980b07803034180b81621039000d01e0b400188160400041c4000700007880d40058002e5a40c0360090086031210b400308000e58000b4020703c1c0e00208480462105a0a00009800c1801d0098030000b08900d80c0c0e00c802c0c041c2c0d40c1001c01920081d85172280c2d8005100e0821188101115176502141064001d9503400034800b01d5104a17071244d50088045800e02c642031000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 391217050 1250 391215800 391215817
    0x3b0109090804050907050a091d2806061d120a12020a080d060918120e01050d051006110f42010609080a030806090a140a0e120412021203 60
    0x30700700c00d850171800040c400e81c045010b030b000107042c0c50f0f00000e8503004ca1a00e03030032411448a21040139502c001d4402c01020107642d903410200b00c00c1d43c100e604c222440c821007028003004e40d10404007104090788440040a0b180c8881d01070040603808586000022900c80907159110080e115000c2400008074076010b207103440900f0345100010200b080080c1540040102d8802e0700d0244204032208003403201e103481d0114090190041a0700380c42403030303120301c455214100d014101141010481403450003220030443d43c40309a40d20b00c82c0184017444c1c03c4040980c13501404001800404082500b0729111810a110020740480002c03600d10042d5850040d050b00702010120741d90b0308000e20030350341c40f0f0200a11441001c100303d5040480d0880001c180144040d03007640b1565280d444200522102d040d0042820825698444008107400e00704014103004010840780821090f07259400340d401c1812410080c00079090400c402c021300c1104602146200390111466170140c00c01029940c15331081c501d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 391218300 1250 391217050 391217059
    0x21303051e030327120c06160f0c03091502031305030d0516060b100e04060803030105030d120608190c35010f0e0a140a030503160309020a3b010909080405 68
    0x101c194101617028000c500703820812940e45444031480303030104205c581014070024404600011880f07008841541003940710b0b241c1044626a9911601c00d110100340c3c00c08016000001d01c1c075850002c1c118a00080e0100318041d200d400c2c402c40d80030740b06114440e640720658106054803414000e0550040c0c0c44190302800c0b8100c0350340c039500028201c0700b808034500e1003035107483d40200d024540001a80e041c1c40001c1c4c02003c0c8041684811303034109171601841055140c4900020480c0101400079070422000f4041342c240424040c5458100310100d60404556005001000b0500f8403282a1620341040268150b074440718001c4151809081e00d022500343c0c960402c02e5081c81010700140320714280c0e0084194150050b0182d5243c0e8403954141009800a2030510108501070300900c02c0b01c1011181d4100090b5108059020905003025544407800604c42c0c10005070101003458a13002e00ca62031200301c81c010781e5080c140b0340c41081040c02102c000c142c7d1401d41604000800c030885019020040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 391219550 1250 391218300 391218313
    0x319110a05071815140d2a0303020f0d0203040303050903101406040b060c100b0310050f100902071a1306020d05011d13020108040c0306021303051e030327 68
    0x5486101ea0448034502032a04d140201c4840030078808074441050f075030b070340340d020080642071420404814068401a00c184182d20004103006202503030070344044000750b81c0b1300d90492440c24040c0c00e02c60b4001c1000401d070000344c031410100d1b5011003280e042d00e80c14240381b41c44d1580700c030100e86440c481100c41c407500b40c6440c0601903c00c1800744958841c900880e002d0001545640520006004032151103065a000d03540c070701002034480e000b00c8207091010702201c81e00716098008900f0782d6020b03036540361140d400302d00340711141c1000f59901c0007410348450154640400c030b64809a42da1401d607144007045880001160703086650384400f8150302d400c2a0150b45a003003040c1204018442845441c1231038507201811000c0030950030303e8038890115004a0014418590015140800000c0044809201b08040400016418805810b14a01d00d07200103402c1815841c00503d04000d50020041c0210500e042c0145528004101d0358401d50040a04031150401450140d180d400e10002039414045c41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 391220800 1250 391219550 391219559
    0x1303030b101b0314210901020a090302090411060304030302120106091d0a0e0d0323220503120403020d08070302130b07020a0b0a05071e08041e05040c0c140319110a0507 74
    0x13942505d100341c0c200e5101443d036880740c0100500303c0c0318012540011601c0103004001601c1d0510220307078080d0240014031128510140003901d0365204803000c5012035030224540ea0b551070807201c0320740500303031500b81306616074140315809443c0d0781ba40904501041424001681c10802500080000403030401100c803120b030701c6032003d00078040d00009034900410320700100c140030820803104e502072450304001c60b5050180480804064008120139070383da02c4104001c02103100c0d42a034a80c45640603034013810801c26075582c01895010003030400c05c10503005001100c0d0542c441c1005208407600c0183c07041c0d0f42c01c0341d880881d24110013a4443d224140000ca1980021900540240355251041c0c045541480345030000700c540c1100d0a5001e006181c3c01c0c00280140301349000d00d20020070203500c001c0783c120390b41d070001015a500e0403419800500820b0311001081030f250100a00940580040c509200c0e00c1b6400111409521010f1400c110410051804d140010301001003681d03000016100b005848 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 391222050 1250 391220800 391220827
    0x20d1104110301120b061e010c11090c0a030c020a1101180f0b13060504030506060d020103090b071e030203010e0606030408071e1202010c0e040e030409051303030b101b0314 76
    0xa1840c00e80d005d01740c00b400266146405045040d42048418250654003201001110002c0c21080100e4408680c0620780b102c2e0340d20400307040e20802007060100d40c0c401650078002c0aa6050044060655001d9104180091582030300001c01010a207030801c0b080c1c0340706201c80031409881c1d00c2005444058480401c503020658014200310340300802005c0804e6940c0d80881c1c1e20301c1036120251883d0880d4000c240c0c0d901d02042103090b240d0052501240301c2c841503c6403584034006881d0b60002c559a554460140c0b8551008600b5520260404501b07540c5058001c0c01d803000c000300850321400c80080010100100c800a072002c0d15006013608002c23958484401040c0141c030700c003d98210b0000650100c656105005501000d0304560b25045101101400e01015250381800015207010502c070204601303895200341481500603c03c41d519501090401504882c083c0c01030034020703122000000c410720380291040c0c000030821103845084d64024201140e1904010741d41c451482c0b000106003440e4101c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 391223300 1250 391222050 391222079
    0x303060109141809010c022407030c120f06061409090114040e1e070e04054201090509060402010c030804060204030f1407090c0207090b0a090c08041509020d1104110301 74
    0x2403a001c2320071044410904290503d0b24642c0d94800c0b140b00304c000b1f5103107440f80e00440b40c50b903510b05103003148018a00101c0251081c00001601d2103584600400141758003802403030601c020310000510341418400403443c1003105029000390350600348a030f6107035030f2180d611100b8091898015180805d840000c81100c024140c00642403500c500000131a0070012040d186010310b9100b0014a119400d4400700424a108001d40202589600c21655007030054400394466076a00400d900b0042c0d81404844800c840c4082c4c46032090b5403041c03080100503600039182112003074050038a42c107251303075614202d0003a00c11604014103000d03c1da0036000030454280300035540030680d0300954000c943c0754554203044034200c1e0140c0b030050380440030420036110344d03500c02089844081c10b0042060344411030340003603440b1075001a0026103c40308110500c800380f080d07001c40385010302050016180ba5000103104070301090028010107050303549207085907203591050005590082455032607680d125604490140c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 391224550 1250 391223300 391223321
    0x70b130c08120301050d140f03040801060f1d042604030201080a27050f06010b090307081204060503180a0b0a1817030702070e0a020a0f02030306010914180901 70
    0xd140c15000310381200c0c042811403500550310096400e507840c0404120070042c45001c141d481c0300710380c1c544a0f4000b00a02c01616070a9024009540d118589400300703003100e400d90700401082d4a401c0050050303148441100804a80c46001c0703949d00d803220b0030203407001069042d03444641007140454040e07550f6500083e10849000340c960201550307602c82c1c048261900c4001c07445071a4030304075051800d940d5080220500754090805c071080c2c0c10f031100300289000707400c2c2c000700030300e50020410804519040005201901100014244141500000525502640c01520117120000c000960503e50014000040440c10030841d100d02409003085d03002a102621301c10443d41c01d0643d880c0b00f00f10440d01a0005a920004401101600c000340861b1f030b4001914190440c05850000108492200c11141c040c10140b0f00060361480d01c540d010b00f5103001c0203600c1c01590810b204003c1e07541e800c100317080c0407110007260709030415240710005040c800358200d400c0d442c5002c203400d02098840540c00081000f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 391225800 1250 391224550 391224563
    0x3032a0c05010f080f0703110f031519060f030207080706090b0f010b0a05040315090507080d02070f05061602040204080706030608010b03030306060d090f080415080106031b05030c070b13 82
    0x4000c80000f1501d0300000c6640f8080041100f0211b400070740300f83d12901175250086240ca09080d841e0124100d20380c01076034a0180348020701c0540d130031403074280345c502c5010310700000b05100d003803800340040c0c154100003c404050582c0841c5d000d0901c0316401c02c4440169000d2010003101049182800741841c066880800d8a0b1900c1c002280d20050081292044c40a940b02e1078105891507592420801d0042802d000283e1130303420103000a502044000c000d003090074054982070300c6508000f0f03d4100c0b65446010301d502094401c01030b588030002241e0041382c03c0c1d0107001303010190340003080180c426039020f030485204103400059006e03815401801610784c4a002881f40001d07031001c240ea40e000641c1c41d554048400c0095001c811a00d9103c03415040c418003003a1311401103901d800342150400d900ca80880d5001c1c0e640f030b05809902a4840c1d0241c691400c0802034450100d0510800400c030fa51f810060180000101d4160b0500800782c07005c40368070100d054171030310b000300c44406045001801140c0f00f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 391227050 1250 391225800 391225817
    0x90606010f090e0c0409050403260105010e0d02150a0504060905030d2708030a03050703050a0e030d0e0c04050405030a0216030330090809030708120403032a0c0501 72
    0xa600c81d01815800d07656039a5800300700e030300b04500c451a14601410b03840a0321401c0200260880160055038801c5002e6156941c40c620000810703858408241003400d00e00c2c902c08010b000680c0c0000142802c000141c40c40002c5400b144045a00034111880444001c0d00103d0300312541948000100306680903561001c54080d1707240e040c907070350f000a400b035000403c808907103c0e40800b6010030016200106400300c9403441d582d440c150340c1160300806001d00043d80321405c1000d8075405014041c0c200104940411540243c800700513207e014012a0090013030329050700d045055020804410a84030040c0f040050741400e00e4910b64980c046012000540a44206080010328505415044940644441e41c40b042c44420f10741801540b18018201c4041c0c803100c8607000b40440c8900700416106031103165031140300e40c04051500290340d00203003260380059105501c0c043c05d1000c1d40d080340e0741030070040c240e44103803200e90381d00040440e00100070003d0348e2194018000e00c10302c0c01e42240e10a0725160103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 391228300 1250 391227050 391227061
    0x71104050108071d0411060f120103110114030f040311011410080105090d02030a0e010912060e190206070803100e070201020406090509012d120f05010c050310170a0f08030906 77
    0x10814088801030003180d0400c003800e06e0b50030b04500611b0034284c4446445e140c5000075038807100001080c1c106445d4981210151720340303560050f0076200c0c45a40a000d090851608600390403080d84000d00c000c040100c840b802c20040b980035004025003108050100d129807503c01d0a406001d041ca1040700e003a90f00303010125002c04808140118074000175030246182298415081d42d401ca07240c8065410050b260350000355540780001800b240d0b52080e00302007103010300390350454030b07080c10050802040c0c0c0070014118010717581d40c4121000300d544071100c1c507241d550b5101e40403003584013075210005040c4d80300100003842d6419802841035881c02e464100300551224248070800d0024000c0f40c0e240b90620101c1a011991035400c120740320515030605000c981c0780c929120342818864001c50780c00e8402d291410400c0320030300818841e880c00e49425410341c500301480b14203803142441003c01e030050964011181440500881070701c150407180103c440003032440e02071400e80c411a000c505502a0700301064 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 391229550 1250 391228300 391228349
    0xb0d050a0506040e12092d0a1a270d050307210e012d0201060812070201080123030a11010f020c010909020a0e120703020a121707110405010807 63
    0x1071311021031070020086800c0c0e1001d4403041e1760000c4486a4060340c08029060580014400a403103030340c10206c9016101340000500440c014240c10460b00b0380c0d0603036401c0302c0c410b0002007519401c1d02d00f06139070001e50030701d040d1004070030503ca1411074000d244410384500340302c00040281125072140c20886240c44900c3c242c2000114a5403030705000905021408215602c5202880060317480e425100e901e24a10030000c01c212081142a280583d4407601f08105030074050241111203064802044e18010303280d400280391520500a1142e9034140c00c000075589090070b540410105c1e80036080324030381d02c8541009074003401507800d00c600085019400072800c03803020074100000c02040e150390301c02506107031101000c2d40040f281441000950400c40410b943e455110001101224001d0070f501c1d03080d0300501c01400556000081c1000202c081c40e800110701e554840390026034100c1041e1900500e10b0440002448049400ea0181c00d00c40045030915000c60524110749046400c541080351890150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 391230800 1250 391229550 391229561
    0x207050a230d05030f04060f06140a0807051003020a02160603050402040606021c0e0d020a090c02150c0702040207020a05040e06060103061e0905131b08010507141e040b0d050a050604 80
    0x1070000b030004e00228110202c5010125000341c46001c0215803012250400011500103511005440860f080c400010f402c10320060409004080081d01d03805042c0404a071205001b05504c904155000a503460818400e01c008540455448010400c2c1c0d5902e0300002c0103080195010303441240f0b00f502c000b6100e0f0001030b188c050411400c00c03a43d501092000207071180c1c401d060220740c00066580c44d200050350b405207507201030b081c0250001007010b4420402440c0501010400703805d4070400b400e00032203081d800f0613946000d50458016a4400680c40410038a0710039030f01446e0007900345643c00c420240c000ca0326600c1400c1c01c0c1d030100280c507902e000d407186085144000c0601d444c0156001d01c40c04003a5040303298041d507407543c2c1e00401078641d61960401d0112803102030070414001d10030322600000b8081e054010182e85410326a05000d140b10b24070500c6900c90040b000049000424541c80b0404e081d071703004220942041c0e40b5a00ba03520850040d0004030b400c9480c0500d0100061407624061141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 391232050 1250 391230800 391230823
    0x20307060804050c011112120405070e04050a150212090a1101030614130e0d050712020c06040e10030203011e0605090f0c0d140403030b030c0a0b16060207050a23 71
    0x50142280c0c0c0c0005645400c04503076003010b54000d0310200103101c1f41c52801419100032907400b066003403615003032003030418595030094011142c000d000d2001080002030010400d0350800150b03065050200900d40091040200c0b105c1c5051140d4200110300c0e0000c80d42ca0040d90080c0d0183c0c40880c2e03101e00440c01c4900718010040076500443c088142810154040108401c2c60940061a64440f04a07640b80840440c031220009400007154002c000581c62088a0a521400142050010040080c4503405a400703200c0a10310305200250403400c0b1403e0004c001d54001d4020881c05d12200190a464140c042c01d40c44d802d4200800010581040050b41e841462020aa40d200362039040325000f155210b82030280c1107548030300100101d07040c0106078a0049110340c40008031802d8500c01d050901504800c0e0a116902e0080c040000c0d82c01e1100b00c0c1d003144200307101d0b03482e40d0b903040c60a03000074018160040d1491060840060401c103d1840c0112840b40341d500e0718000a0b4003005546d5038054030710380c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 391233300 1250 391232050 391232053
    0x60503180d1209020a0e0a02090a06050c0303041514040305180d08070b0c0706020c070f120b010302040c1103040806220c051e040c0f030506030c010806090a021b070302030706080405 80
    0x4502d00707003000b5a2060308041c2c40284140f0b0310f282d88075441c1c981e221099800840e095030020b9021514a8108a940700600c0c850824034145005601025200d000040000c0d1400c1d03000507103900728039010fa008080343c041d0013000503082d0810b802e008105070002102d40c040c000704003d03401c01754540044260102e9600034000b51500d050313555840003e903c040d10815103484288004000a0000c2c005040c200342440010021245040e0245890102075400700004500411f808000314544081190541e90166008240d100700c6a00881e4481e09a5200e00100d000c0480c011030200d0011503104e000d10342090a01540130a1a81380000003506100028403240384040100400d05140404c100a00200c0200c1600c0200c0034010030b0941da0840507050025503100409046a03416105080e040b0310305800070040400341d0000a808140d014040e01c0c481c41e0400c00040c0307250b8007074045415191030400c204051132002040c1a6440080b800100e101e80180c6070701013040317881042081d204640020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 391234550 1250 391233300 391233317
    0x6050117041217011512050705070b0402240702120c0307170304091d0d0e0a0b03060f04020417190b070c05070f0b1b01060e0c0a021501060503180d 65
    0x162440304a80c014850801801240002d1503142c4180304601c600a041aa60b24600c0f540034282c02404983c020481b464102e00e070809006205920006031482c4550180480d1314a484900016241030845010380c3d80255600000f4004000d0030740140500910070344a9560441c002d2002d540c40302030303403045030ba0180d110880403c4104481ca8144c81c44000900c1620300d002d07201c00102c01660b0240358010068082004140000402000103c1c200c0205152101090b12210300040e941509803182d461001d6020000c41e0480d982e0035410246404020400c40d40d9503940c09a03000c40e01484070f1141c030380c1d0040401ca040d0419001d080c0009480e0701c180c0200050361403450a5500c03d03010601561580719014003c42d80d50060302288014080340e10b4101e48460010240d0071401800741200662641056003c106d0004810b800c0343d04500d0a041c0180c90b1450354408074a0410881c54202c01d072450600001a111340100c01140110f1140103001d0304813000401441d0f440e035002440d1400101b014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 391235800 1250 391234550 391234553
    0x207030e06130302091003120c0302070b0c0c0d0516081b010c050a02120102090f0a0506090402090d080307081b09090f070908031b0c09010803090d08070204020d0f0605011704 77
    0x3402402101d4480b20304080d0503840ea00402c0c00d05500315083c4408004d00352062040c0b01e46000c011004080d04d00d084442d01c1c9056800a413650b8407442100030000300130a00c01c8a4800038008600201006001080364031a40d060440e0340e005040c903181d070004484840403070421b002080207480101019003800303004404000440b5082d29105084c0c43c540a444405d0005941d00d219070401041c0b800009a190710754482004035680c18a10850b1261003026010449601c0380400e507031380c1102c00c0706c0c01601d500e20000862541189040c0007440345e84000708001e81c0d0350300009030501419800309405920402d541c006605071040e9807119601003250400101c85041d922041d950128884c50105a090f13901c01c0c9151540c1c2000307003030344503c0200c514103a07180764080090749103288085415200e0355240a001a0b2030b8070495540a00901d800e44280f400d00c4401d82c03c0300d20f16079000c1c2003196101c0c0900c200d040101034149000894504290340001d003503100d02044000d002d200c00303100a25032940e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 391237050 1250 391235800 391235809
    0x2090613033e0d0f050d080903070201091a07080c0102190e0303091011030c0a11090f0106030f0b0a0e0a060905090309040e160e010602011407090b0a0c0501061d0603010207030e 78
    0x24949107035404080f8103180ca0028101070901d1842501c0740d00141400c01501d2006000d03207c0080c1601e03601c2e0f00078000c82d00582e900c040ca50007203500044c8420b1000030402401c110304e00c40c024000d0414203000409501542c8158003d160001e030416805824802c0d61504881c80080395041c41d40c582e000f417110013500d2a190f035940d41421031078102180e104048411090a40c0c100d1500302d0b40d15003105003010203001614400815400f8200c51126251038042441c1c0e9802e8410300412080581d100c40650701060140d001c0074071141c0c000e1401e04055034915402c0700c01e200c100c651808042c204040040c500c280c5006141c09904480091030410307510600f880020300b1040144652441410628040f0110050305c07000545500340110b17000350f0600c2d002038295000a9014404500d1501c10454420b900005c144151042c0783d01456459000b00000c84641c002c00380c014113154600030f000903401401c01841d16401c0340301c0f40c1c0d0200642e01d5508060803405003140240214034540400802d5190 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 391238300 1250 391237050 391237163
    0x409060b0301150f090f09020a02070b092409030303150f040b03120706090b0c0405090709060905060903011d1006060203040f0918060504122d0f030209061303 70
    0x980350020701ca031b940300d0f08640c1044955105840b030b5540022400012541413040d0005030100d60151031415000502090804202c0460961001c1c030804a007410fa00c807010841d0381e90710b40141240c3d182c0c03e0207541800b585030f203580010b00c110300e509500302031810709000302101000010060620222107420a07107455000100890703106550303c4401c000a480c010702c1c58020b4030302072040c9450360304003800d0004030040901300409003d0081000c0007000d92010a002c1900c2d01030702c0c0300b1f480303008400c080707405003802e41203400071032070012840826200000740e914075a9070190030900803a643c50b40c4c00da03120712446c060f85801d45001d03e002d000c080003075000241510411405001002015111941142d100362012501c4860700e00c1c10284865000808002921a4000e4807950810399140c08203030309444102d12050280c0c12503400d01e090f010364140c89040034040e20b60750b0391300590206148001e0389800102c502c1e424030203004181ca09540e200c1140d4940302040c080b80d080c0b4501001e140303d0f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 391239550 1250 391238300 391238327
    0xd08040b13050a1202120c0a020607080d1409070f1404090c03120903020906060306010c170c0109050705040507020105010503030f13350102160609050106080a03050409060b030115 79
    0x20021480303900050000c002da881564051341e1494500c50b40b62400070b003440752184650914410600c02501c08000210f1000c882ca84d04840c51542c0301e806c2d1a0580f12801a003400307034421481c2c0082c01c0049041c2e43c803124410071038001981e400703944801d00e04040c9903c501550720b0301c50a45010a4160403e680a640d020303010f15a0f5080c42540c075529a441c1c0d86803011004002414503c08004509003000038a0b000a401c135810b43c11403130944002010130440001c041c003107048125140031a4403081c1c00f00c070606001c03039000f80491002400c040e0358614042c49010b010704d00c0c090002d81161701c18421035043e264003c001d1450001d40443d000e0b400c0e0030107900305502c501403440018810300107205420204c201d15252140e410340641c41e200d0038044030700384407000b42d00420010911182400d9144841940a43c00040f2110030b03040490040c03040307400c20380c95841010f90013410315070054007400c1245c00c11541807140303a0720354400012a00080c410112aa15141804c100441c014a50906c206 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 391240800 1250 391239550 391239571
    0x30303070c142b110304061b0309030b180c0301090b010303081b1206030c040605090601051e030f250503061203090411090406061b06050601120921020d08040b 70
    0xc100a0540146108034850030f0381509580e200400725698101e18070094103020607002d035003071920346440580031240d03401d80c0c0244d550034408154200742c004c501c0310000d503801000401c1c035460230417001c4501c200c240d408a6400c1c490100c800780e05203414003072000b24907440070800501d40d2175940c1c01d4443d068040c1811003940700d208c0820120600c1200a85041e080d204014400c0d420400c061605107070182c20024021400c00900340016210800f201303410440a2811542d01c07000303030b4030003440145003a031540c003050030000500c00360203002004030340528000c500180c0400e52082d0311b0940c0400d07840480700401d80c184001806d625010305911001c40419098a03d000140b60001c1c0482d400c4510303130304882401041080d03080c10280304042c06840141016000360f85000c01240346001e42c008000c1490b5162800903d241c0d1090488003101d442240e000d0094001c145008002c11014582c107001c24a2000f074141042e520001c2c444036a14410348a00e09a0340b515155025401c400400440d000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 391242050 1250 391240800 391240813
    0x501081b0319230601050918071505070512040302190806150409320c0303030604020a090807060809010b06040b0904330e100f0e04051509030c0705030303070c14 71
    0x5805260b400c1216400112000c1c08041d030601c000c2011f803020141c01a8480702c04c0b002043c0901030001080015031b0f80c00c7c0648260101c0641e81103030944030700d010050070f0f070055500524283e1281c0d40500b050307030310858125200340030722042c2440c3d4a038103210b0300b91035a0016000c503140306c070305448440012801030400310340715007183c56480702c04c0346107281c3c4044495886c09154102408078040340c108801c04002d401e001518000281d6039000c040c141c00d124a60000700760702c01c01d020700240b1000303001d14402c7d5020669a40c1d40644094802c07120f4000c0e9500b0101e03982c03914070f0560100c5003034803103049001c0d081990007400d12000b0904169541081c80c03c29404e8006000c1c0b030808c2c8000d07114010a4810303640e04040c00214070311b10290100010780404001405109024011401074801c15040c400e516511820001c1c40e01c3c0e030300500400321442c030b1000d2154900d0084000c1006c01e1644007101d050030b60720300030b0581c0da02c0100d9410000501c00035405001405058400496120b0f102c00c0700c92 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 391243300 1250 391242050 391242083
    0xd170d0606020609010f05061806041b0804111005070807060f02180a14090105090702010b040204030821010302150a0908010f020307090b03040f2a08010501081b0319 73
    0x1200d089070001c00141c1e20000812084403001d0050720001c20503070405000a081c10000b29160f080025027100c20314001800140b1143c4490303002072041c040c0600a4500e12105210181103034070150350547e01c000d03000c480042c0500302a598039196002c983e03200c9103455002d07203c0d4a205d4008900c201c48442e21036904400500c018009000d050701d8281901e65640d0180080001c2c03010a070f03105a86410085154400c0703079440044050440704282d0b406c0c0c40a55542c07000300e0051070000075196200388042004824010941e0282808074a8400c040e007900e01b0560348981405800d00c00203502034510b0035074885100a040c090440044141401010140c60710796040c00d43d103041b15003284003a4040300b00308040d5804070a420040c841c2849643c61070034103454441d00c0d1400c00c50084c1c101e80c220040c3c0456a8034450104100703410300ca6080c26100d4481d105540601400e10030500039104021201c81082012104100517120041c002d045580100e9411030380e1004483c025500c00c20072a80034103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 391244550 1250 391243300 391243327
    0xe010911160c060e0d15180c0e0a061d0c130e0a0203420a0510020f010f0605010c0623040f050d0e03100506060d020406020106080111090d17 62
    0x450503407080038281012410f2a900400c0c41d07000d034400c0e900c914010241100407624244840004100190010900310034003035079403011903925103004290300301c2d08000003208030f613500007280140c1e00b000c0280000d6559101007050003486088042c00c1c131040f100800c803007004140007420580190020141072950702c00b003440a0f07400c00c460290151f40c0001c00c02020005010300700756000040390401c132645181d034040c44805880310a444020304072240703d0460039916500f600c0300800380142030303600c2c40b10b01c000c0c025110f460b1442400c4556003000c400c181c5180503401220241c40c01070391020080003045d00c90354080c2c10044070029485103410600e40d150060000790a20a500440c40184545060700c6e010b403821a91f1201c031020010a030070840d0310b40e5004503c805c1c0c01a00740801181036100c18002498034404e051801c40c0b00c1d84002800940c0c55010742011046038401c1000300800400200c540c103c1380314502d4078030b9201c070b070202d8107000041c00000c0d08204000d030440725a050031100e20340072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 391245800 1250 391244550 391244587
    0x1d011e140a02060421090603091a04080a0201061a0f0d02040905041a0c1201090504020f0603100303140309070e0c0d020a050705011a0f0f011103190801060203040e010911 75
    0x1d40041e0400d508000030311031154500c8403c0fa001310b510a01d8481161402000c409080c0a84401c0646074a4520144070041c50401c3e15210800410320b46420140b8000260b03900441503507002d1350801c1000500c044080401000e060940d550152805410103941c0b54036a011010256a050b428040850307425614031600d44164412011070000d00e1441030750300c000c00340c0181800c40d8402c0800080e40801c0c500c040082c11541220000715864540f0b00c0000c00000e81c44000380d8008401204010004241400c4001260300a80b502080b906440744010260321044500d00c245a01400c41005845034066050783d201c110342c000c0504041c0d410403003034240ea01c00100340c40055008607003401030002c00c0c8101050208412030f1041030a8010700403880e11b0b042007001d0351044440004045550740248400c4805012100c2640d0b9181e0048226140c900b01610760b007000105444004107a01c0c3c00001228103964910002d01400d0380707050058800343c04011110141d440d070510060303101f0654003514 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 391247050 1250 391245800 391245817
    0xc050105070e03070b0c0304030f0302150c0421081605071212030507030b0f0613050402030c0309011103040503121b0c0d02061e0a020d0e060906071d011e14 69
    0x12100c16074400b408043c078140d501d41024041c2e4000704004030101c40000202d40403250f1002c4a071034140f40508040c4c0c14641c40042d90702c00c000c0600b08100c1c500c05000010015038040d9045035104011404244020260191000b4550601003003003003440a40e00c0c0d08110528490f6080325200c58403080010620078100208864080c000316040003040e4144c0180c41d881202894200f04058000c400103201d6911000c48500a220015080e0420b2001c03c84010141a001d0402c0d50349007403040421030ba940c802c55000c0c416503c0c00b1a0820050b000b001101c0c00350781c20000460a0000c001c59503906407002074803030035108245d2070703660207642d0105001d0702c0c01e642d4250180100c0070101c0d101a08101c401407074103c5c0c01c03041031001c3d506000740342c410350340260681800585401054030650000c0c400300a0010403441060b0070072400603000140c091180d5416590b14040f011440e00340c01c800501c52200303601148024244085060805a0f5a4100c09540c60321240c0100d10b010500c030158080c005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 391248300 1250 391247050 391247057
    0xa08030c0d1b020d06050a0f0603110405010506070c15050d0f39110a23010b0616020402030a091b03030216030305090105030721020711040605010207060f0c05010507 73
    0x41d269541c0d40218551280c40781d96414a030b0450603d03400501c2491800310001e14032a51607000c11440c4980783e02002a481203008100202d6440e41002c2100100350155644102c1c2407400114540c1400c00a880180e5031000c0160f42c001c0c20404154151507084080c403080000c24041c2454411003401481d16140c1e52a1002925005024804031107c94610104105480c4164410485000d000329849040824500b010071261007150041c144200c00c0c9010300030301c04c4c20a030554802458150b003061818643d00030040340c002c00c0c05010480c06000007960074142250174420150900782c000b194803495a0100140ca60780c07130755900c015403004c0c406001115008940500405404000c0300032020b41000c00d1502041c91680c0c000c105104101e4020304008003c000f0401c0c045c0251080b9814000b103040750b400003481d45108d8002900103030010381c1d0395400c40746d14040750b0070179108503020b40b032069010308851801c14000f078808001c685103000030020310300a07a0010440a1055a01a00307181d82c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 391249550 1250 391248300 391248313
    0x16050c1b0f0a0501021015050307080d0801060c0f060509031b030c150f0112080705010504060c030c05090102070e07110601030c050f1c030c290907090213090b0a08030c 74
    0x10301c0000c07884a4969406202ca02d4000d210fa6a00050000100c801c0d001d4045201c2c000703140d0040102c2502d501c2a80c15100d050350200384114045068000d2143c5941c51001503070f40e41ea811140b0030110304010b809009102d1401c80424110f40180381c0c003c0c00c20085030725180c0c500c005c44108044001c82081c140d000400c07400b84031402884624031100f100e24940c00f0b14100b4020380c1c0800b400c18482c0707800704028440000100801c0d8000d503007000d6003020003042a07283c5800c151004e400f00f0315681c00041d181103941c1151902840c1076841c81c0318182e00a103142d508200c80754414080c068115000c2c0102d180113000d02d0002001158040d62061106d844814500030901010803421214203100304104084174030303002c0540241e03030400b54052030410301d80d0510b0309007040e10400a190610f0b14008228903980030400e450080c074064860003049031003c65841213100103d00400c1c03428075040c0c040e03401c1042000d0003a0040070301410010304640d44541c1d101c40740d52855100c0381e60400301d81c0000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 391250800 1250 391249550 391249603
    0x207060801060e090606090d0f06060504150602061f052101050717040f020114030103030305070806121b0f03151b0a050405060d060306051009110901020616050c 71
    0x1102981c0184000e0500348820a0100f0018002d0b0030014036903409003002048502c043e07900c01d60030344091500500d0380884403400f41044405450701d8058607001d035041040510154200e403d50790300b00c17804e40e40980000d03140c101d00c4020343d100860303802d004041d0618000c581a030382d200c020318200444100440065516a00107801e548004000f80e06004640d940000d01a520a480b20351140d805032844091044c5440143c034480c0d00c002d44c216040340044004000c160f0940c0c05940a14915107603076803035648450400c08000302c483c072010140c0e04801c500a9200340d01c0f80f803948034407500410400b08400c088021a01e044500011070358004500300a120a50848090401c250078413410141e182c407440f900060300c18420ba100b020300503c80001d007940881e200d0b80c002e501540d405002400355040000c01956501c0c01400381c6c03804030b803400c100e03092850121030407a100c07100181c004c2c03c0542d850303170701030111501446140001d0000c00c01c109000f030b41041c400d945102255480003116500d14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 391252050 1250 391250800 391250807
    0x705060105040921020709020304110315251115071214060d080d09050105011401091508041b0e16050a1205090703291308030403050310080a03020706 66
    0x1a8030590049261035445404500c5041000507000800c484402002001c4203081b46000303440c2d400b124400e0b2011081c0001c21411161540c11010b0840403503c078607031200003610200e90117403102c80d0035a810030940c6822012b1501e00340e03206042402c201c0b80744801c61425a081030319150300321810040c03980800400d50740101a0a020140350710003003100d10030f9030b2030b0fa146101018214601c643c50a040d00020800ba4000701c4e15211140e26041c01040c5542c90034074040c01007030003040003060711a60b8103502544a0000c00f41100c080c000014030008800101383c404000252099546003039220805200b03c4810f10040010804240c500100b0b18211175055509088052820104039007084001034050340040103004a8100039000141c9480c0e9603d01c43c0350104c2680300400400c1c690108510541482c0301c1c4540c4283e040c1c035a4041692a0304000c100c5149059000344015800c1c000b28002c680304802031580a4804082078120719200e031030051070650300840850042c0e002c04028095a540f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 391253300 1250 391252050 391252063
    0xd020111070b040825050d230304020409080712020f1005070e0906120a0506040b01092a05070b090a02030f070b070f05010204030812090705010e0d08070501110f0705 73
    0x4202481070616038036541d1000d110744040c001401c0108040386103034044282d050242c441903221810191a010a840c14944804802035800d01280c0119010b2100b001c00c4081010201c1d80071080914541d1250700300001405188015500c1031400e011020002d40e04440d0030a400081e074008146040072403207042c0c500304003030388400c0665040c0800e001610760040f2841c400c400d811a01c8030115039410012030f100704800180b800366440b484961000744140441c980e8052030240036600e6081e81c035641c0031829590f06003120441580c001010b0101505401c200c0c0d00a103200780351840c0b804030b5940705c1d44030b070090642c0c904100340c0160310924214601007003da01002032407000b5110036480e001010905010ba148080c25a89000d116481040829811540955400059941c40395010b00030f418100314102e801d607515100300d440c041200d60141d6007102001c0300c000d0402070104240e5844105c15004a0360480303256403100282102100311101074284041490021500c5160030b0a00514008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 391254550 1250 391253300 391253321
    0xc03030c09050607080c0a0804032315011412060109060f080c10050711030a0602030f34020f1203011a0705030a120b040c0201020a020706030e0a0b1008010f02070c05181609030209090d0201 83
    0x501680018094103c401080381c1101c5030541c0101941040c1001b04fc034960b0300108400d401e0041e003001240caa00d01d40e02060a9030f100401c00300b03003d902c50a072190f6401e01080d030fa0354000540183e19000600c213000400015104460302c404181c01c0d0b0003c246080c044040403203120342c000c0200800d001e2280c0e03406d64440800d506409601e103034600740c0e03040c0c4411002c80c07000141c0d400346c00e0040c05000300400c56100c041e003011070383d030b143c5030941c9170406070002c1c0281d070280111640c4d243c040941c0c81054901858000014503e0a003400a041c2c40d41e42150072040001c90301c858200c000f50380c8512440610484c690005a510310030858003d081c401c0907000034003810f1400d11050072a0301c0c00503403900d0156000c407400c00917803070318170300503480d22040d91100702c517503003881070901c600e070390a8028104003403007443d00e00949501e410800c204840c420760780302006d86841d40010b0700504400f804542ca041681441d0420b50740342d80210383c40240481700c504040d404070402c962580e90901c0b5252206 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 391255800 1250 391254550 391254553
    0x703090e06010c0f02040209151206030609031c0b12060405210a0801090f090c152c040c231207050403120509031c0c03030c09050607080c0a08040323 66
    0x142100d81e1340041d40400140064001d950108000d03030340e07442c2c895a034000d44643c005003a403601d0016851440241040307031740740c2c042d004a002080040310b0001c10744003d031004824060320102c126200c0707001070800e045403540c032103080c100704120014240011070082e80180080d00009800d114032020700c009203d100c141c40c0004018181c0f18030f80c426940c03410b4030f442c4040400c0b04510292140301a10103000d01a144240d0f100380001c541d2085500c000c10800e81da143e01c00440d85066000244015400000360760603100314203060580f17003d51003000000300c1400d02c0d000b40e009403900c004407004c00d400c1101d21080000341d9001070050b107803082948803000f07292546c68103003103aa171107504100b4203896600340f040c0401d0400880d40c05100f04881c1c041401d00c00b0340300010000c0024090b901d04402540070900d002d0494a010b0310411900f402d0701c5000e010b451401403507940300c007001d5000c080603c91602444448a00080380f800003000214010001040c02030080503003011226604c5514807410f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 391257050 1250 391255800 391255817
    0xc0d051003201f0f0302030c0903160608090102030103030f08062d040f0504320d050307030b010c051c0306050301050901060609060c0b0f07020102091002030a0f09080a08030603070b0703090e0601 86
    0x4d0b801942641058010700d000f6032213840e0680c80510b0b03030080f0000d06078180900c801403405a1b802103081e80856a29a40b0029540c40f1311410324204d10082c00040c00007503e80d0f03601d07a00c07580608440d60300714002522103084082c83c400c0459030780cbc4c040c03a41311304450f52100304500c140c0f42a00603c00c14264421080005040594400c403440b1a05142d99900381700c807103544511040180c503035096540100e416075840505950000345250301c1203c83d100841d2a201200305a0351194036020941035101e4018008480d644124680039000b9111443c20961036020110f2251400c1c090203014003043d20000c81d1043c20060050420708441c0c000c60100700651400102003400300701c0c503a4001c100020301c4460350300c418204070b029206012109412850142640c4c0314158008002c08a0484c00e5a421580b540319050444d020151391094800580c480b626000100d40400b00070f5400ca40700404a520305641c411500696401200c1b040d408a061030300d041013090a41c00106038410801d180c20b1b402d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 391258300 1250 391257050 391257109
    0x90c09090d03050402060d02040303030b120d0c02041d1b01091502030f0702010e09041b060509060f1b1c020106090e030a0f031508060a140c0d05100320 67
    0x94400d44152030760109a10f0ba400314081d034417004111600c105da1880203550b034a8681c01d000d80a0070001394000e0007180e07048c1c1520803d4001084c00e00c01c144036552100e0621210742c0800c1f001d04818007140c1205108000e1803080e41108024000340d01e040020302520b20b00c60000050045a00c5034803100014250510680707141e40d021080300c41c0040312400c0c8a841c1c2d031075400121058100340035400d801906810134441480914001458001c112100c01440d080c0c4400e0200c0d0307240241e441c1d00760090030511540380d6403903102002d0032503042c0c034140b0f401c0300110041c0800e1501140d49617140305681a00100c1e012242d0a0140e480500a60f0b5001d101081d00c01d174905a480c03150140e41c038104181c6c420083c4000d44260822881220040c25008401c1d4032581082d4880301e055420304c00b00c80c5810510b000003240000081e01c030314500d0f00b185003802c1e0b15045190181030002d1903010900b2002c2c1c000310010310781652174141c05180418410b0191180d10030301c941c2c01c0c8403844c003d1441d2000e880704031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 391259550 1250 391258300 391258303
    0xd0c091805061f03110a18080d020d03020904110307051903060609090903030b060a0909181a040f060c1d0a030804140a03060606020c0316080c0d0f050604030305090c0909 75
    0x440700c03050301e48401007203080e20000700e0003040c011941440d0101700242c032060f01503110713203900e242081301d440240d4166038602e0f010b5035400d0b03246103150141c3c04c00070360303019050301aa001e440e12806c044c03c04543e11028050740c01c11507200302c94040104501041d5800740706485006000100311a041c01c0040c1401c004018003034043e07502c80c090305180c4400120003014070940007000d191501501550b10740d410000702500c00075550180c2e0b80c0b098038010140203480d078451305c440402500214603005910a000010824100040c0280da405a40d4014400052110310030381810201d02e907240014840810804001400511161481041c03050030500c0803907661001c5600700c40d450b0200000400b041c201003814540142d0016003007924002c0b000801c2034021545450252046080d1000310107101002c2c0c0c40f0154500030340020380d008c0c440402050034004401c0761541c0c02607211104000c41c0c0d940703140c074003402100c0c11000262a6400d100c581202002000c0545508580154080c03501c81c142a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 391260800 1250 391259550 391259569
    0x270b010312030905070b09011d0a0b0c0f060705180909060a0b01020109020303040902070b07230a141c0e0a03020307110f03030705071e0b0910050d0c09180506 70
    0x5801c200e410050054980d00991040038055400300c190317880f080d51900005240d800900005000c00d24065074424407504818602c1000c080c000c08404047c0c2c140508940749410040c1c81020034414072043e000d201c403040145a01c106c0540d9034455a03260303040e41220307400c0102540103006024071824080c0344140491611750058010300005000000040100d026049048001e50107010006010420301042c3d001000c43d00c1c02411501d50940b030300d140448030b00a0300e16081114560050f800d19010181030020100f9818a25040a9034134100010882076031080034500d81604214040d0601e101c3c8601800003858030290140c100782c90b894070083d4070fa01c10050014410186003d81c1a09030f5034080b03041c1a01800030b41120780721441c0d45840e0350764110502520f55500f0000707481e0009560081080402da0b840003101a0403c10a0300500c94403e041ca508501400350622502001035402e101d0900015a41c1d81c583c141d06203408040c08801140740d03441c440036420002004034607142c4207001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 391262050 1250 391260800 391260803
    0x31107080d09020a0f03050105160206040206030a020f090a080a05100c0e0405060303071e030815180907092306040b150c0f030403060b120f060114030c0a0306270b0103 74
    0x2c14644400e2000032280c20031398001043d0508034075004801c0c014154042071080c03210b450b50010791030b05240145d036035010456000794003000410010309034919680103081d240034103011a900b01035000c00003c0b00d00c50180c0008407190320407084001801001c11905000d840e61903401c0281e0924054000e00460b10b49401d03034040c0341c445002c5005510200203c50001e90007a2281841e0000003404040e009030420098000403648008102021840203196035410001440006104e0012014030480c9a00070102c0c1c0f290f010745100012808507500070400c1c0c8501d9481c14407102601032100c0320812a0142190703010724580010f50b81c40340c85444211800c40221692181c48201c0c480b1080e2030071000141544850101040c00410003c03e40c00c540b4021000329034000055681022a035541c4041007000100d81d80040b004105549d0000902d031183d24018003074410000b002e44c08580038504544c0122241e50359488901c800003a6a0a055000c1e4020016040d11b000652603403011542c06020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 391263300 1250 391262050 391262077
    0x90807062018152a1f0e150403090f0902070203070b03060d0c1d0a051e090c03032106030f0607030c031806050405010509150c070203071a0a03110708 66
    0x202212560b84800d4890307052a66154070f42d407880129050444c110910340c0003090b4441006140e421010003082c030301e035254100310380040b440c0408403500001d04052003106242d03004415440d40400042c015952185000b0780302c02030498900003102007580300c503900440c440e501c148031406c0169004a1020704881d40d05454907180c0c1c0324180007500d0080c40c2d000080413005548400075501e0b00084c816540c524014803d03400c02e5507403001c0c5606403142201c0a6440200d480750000100005d48801904003509104548081c501d44d00802c2c40c42d03200308010f120100540112651110690024660001c400d50141540091030103a0303d40e0351501030040b800b4145c0726414410340d248681c2c040700041c0d00c500d0414a8940003400d043c2c00400c41a1001d89031340d4202000107480c1c142c009040d4001600c0b4036541a41c1d0b40c0c17140c0100c01d236500003c0c01280d15020388000052644144000c88000010540b1203540e2039081c91b401800303ca890b620320040d9258103002c0140455000c20030348400940341c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 391264550 1250 391263300 391263337
    0x2180109061b02091803031305060c0906161727030a0b070f020309060f0c0601170c0108090f2e0920040f1503110f0906010f120908070620 61
    0x104408405c0d0040f00f6815620004c41000840d00452030f0114809000d04150b4541c1d0b2100e0031588618400c1c1000325410100421540c0c903600107944801c012513010304800d080001810140d16200d6006148018607814540c0e8015241c0003c115000180c600c04c6005240c50444c03a0340b03801089000400c44002c0c002d26001c240c041c1c2c1e000f40122842d003034008082035a645000c0c421405150094080000c00d0f1240304000b007a825100d0245500341c64040005096a032211401102d480303800400c500c2090040144001d5841010480344242c0080c0d6880803180c0c06800d60132380301c3c0e6400ea0f00e114040500389134000001c41c008504072006a84103d44249004442c0b00c00304010300032030601c000009180c0148840084c401100410031b40e803195281079280500341c020032070101d40c0c451500da800400c1c6408192258028030000d00e8100c1982000007003141d402c007c04040300c5441c501660001e5000603a00100100c91065015034408004075400082200707610000f02e0042c5549208045200d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 391265800 1250 391264550 391264561
    0xf040f050402090f06070606051807030509010e19030504030f0807211b0206090904081306020102040e0c090d06020c062205120906040305100f060e010b0a081902180109061b0209 78
    0x680290300900404ad124100c5c0c44050218010072034012113603000013910f40701c0031401c4060180586907902d031260005241801081c2100c00b400e00544400700e0a0000400c0004000b807030040c2c5030080140220a100c0c0c42d1081c41c105010150b90072048480800d003680e42003511039401c5000c0200745c800040120140042c3c51010800314030a403904941d10110721030410041180c043e0040c4a0840f1200c140300d007180d038034071040c0c0c284e010350b024003804a14108009170901441c8809010086070051a103490300c0450340f2041c089a02c05105441d0b5500a0700030070080c0c00c0d141c444440c040603503000403c90302c195900c40c1358442460480520b03000e040000e200f04c6550312042038401940c2c1200503100c1020703170315144000601808148141a90038010000780b050b03180903825040390b003004542c511700150348030304869015004048403010b03c0180b28540d041d00703043c800f8015014000a20742c51500091001615041c00c81c0d00610401c40c1c0c0c0e44c40705101134000c0c0406414264160390755007450b201d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 391267050 1250 391265800 391265813
    0x90e07090503060f0402030c0f030a150908191805090a09032c120d091a04030c120c0503030a1202031005360f010b0c120f040f050402090f0607 63
    0x540c40a035040c0308943c01e1001400c035010506015900c00c4045a2142c0564420302c50b01c60803a00030668182c100c2041ea001080031001c0c10090402800c1e400a0202d116690b00e0f07260b070b0002018070a0381c01c0891100c1d01d207140c00a6800100143c81c0d116030030b00074900030000b1303400040241503400c43c546440c00b440405004502107079041c40f000d4150140d0700007420215113a80f494021903841155108510740c82d8a201280d030491100042d903485c41c095061815410301413211a01319103410104110000200b0680d910000280c42840720744202040b0504041c25007520f25008180300b50010420050855086650310064405941001d6280c4d915541002c941c1d040c254444e54008210791114854007003030108480c040050f01140b030100c000c5070f01500d240150201d940c0c0e818044a400140700076202d50002d0001c60101c0d2003182c034000c1210140030304641080f5240821994042014400a680c0361000000f901c002c1c0c1d011820880d1140004551070080c820181c06000d0000710f540901c1403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 391268300 1250 391267050 391267067
    0x30201050711060f0901030612030f1b0209010b22080c0f01030906050c041806260129040b0d0b0f04050f010e0321040b040201030e100f06091b090e07 66
    0xf003040d0380b1140c0600a42140394450703010240043c3c94000c020031040c0c080304128041c150160b49100341180d0072001070301d135400c00c44030f070580c555002405480113030b030390044403030280000700707281505c5503607400d20300410244a240340c50746101c01c0c440500c0140e200042c40011480111100031582250400607001400646805000d2504140070024003010540c01001181e14030341c8098a83c444008500c41224154081c0a80007942d0b00310515444500c425990900c0034000c1c00060311845501081c2015101004001a501d4928885680a15103846240c604100540348822050101d07a41c031004240c000700b035114a044840085802c1c4003041049003c2101280c00800c0f155a81c480800ea598200c2549080f08030000910728400d0321611400902480d4064800d2025071180d0303006402502c4030b4091041c2500c100c664252000c1414000d109820005000018101d4213200c0c0132401d903424a11143d6503901c149100811b42640800310314212844403034400595114000101c2d017626 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 391269550 1250 391268300 391268333
    0x1409100c030209040f020406021213050906041b08090607090b04050d080910020106140a120b090c040c0c020909030f030a2703030b100305270109050303090609060c130302010507 78
    0x14603002c40c81707152200301d0340107105403080340e0200d8012401e18560008544034880e43d10b526500c0d13200f802c04c02ca041a10a454109800030030220710002400c00d40f020440b100c004002c0020810f41c08c0c01241501804003507004036940c5014020f207403c101c072a1046103d2031003507078003505481c2103200501c1100000d9070308038440101411402c101c5480001d010701f01a014060307954129584d40c100c10f203000d40e8150116003903c40301ca4024207164451054200b001003010949010b003d081c001c2ea40d41e075114000000c0065140c6031b5803030b80b0b18014441d840c03100402c0510954030412245040c1800402903ea20a204000c00314030030456626102c1c00c081c02040c0b04a00c0640c0008038030405401d03401156288000b515509001e420359882241640e400741c444030b00c0702e50004941303581d007403001ca5100302c8000c41200201e6400c01c595241481c40d44202c6103002e8a40080b814058046014413180c0c0e00000c51903c40c2d0b0038100401000440300502c1d10000341401400100381080003d040880d21069 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 391270800 1250 391269550 391269559
    0xa0b01060206010609060e090a2d060602010e0102031015110d030903020c01020d0813080f040311090f0403020705010302071a01032d0c1a0f030a020d1409100c030209 73
    0x25603550002a41d151001e000342c10110314030150120710148910385458201c00000e08054550f100d0b5602c0c0e60050002900304403246126408042d25040c12482078211984500b100090345458400002d08448007505414201d9004100384000c0c68007200d00325056518440340220060f0701000700b0349500c045280c3c0c80802d40a8900300d424980e416601c1440030a011b03809030307145001107400480e1200e2400644202043d60800420380818002c0e003080103051103546011310348071041070164a46c0d00690f10444800c0f0204120304a54104902c0d142d4010303211400b03011603400c207590069110700803030140a0400d070703000c540c1205010404600f903280c11241c00c210080d40d6100d00345400014160000400b4550103030562549001c40440b90381070740c0f6002450160201d003003103210007a007034000d0080c1d0b06501050248a81c9598900015405042944030044e924584460740c101540c02c20300d080041010710708104528500d010511070902881d80d0000212910f0004050b0020700541d440035410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 391272050 1250 391270800 391270823
    0x2d03091012060303170105063a09050105010512060903091905120a060516021209120607080108070e0601082a0c0f011d0307060b03010908030f040b06060a020d0c050a 73
    0x2030581046404030401030481c503c0990b41e1f221418402c003845010044480460500b000107615849005901030204900020003403141030310312114183c6888030000c4c2c4041c2d65640042001c5c0c54001481640c000d0a140070381240d01d0114903054880c01113065860043c4c030f40d841d1100c40036501e0f2601c0d80180000a003a01d10800e103640316155660003009003101c1c01498071000c20f91305080010780c411010743d10340c0100442118607180d1349a036000707520ba06803c45050100c0c4100d03007505009240c0300b070000e543c810400c1c1d85041c1c01507280c21a40ea01040151801c0303c04d2000c41d0764440e01541d480808400748400c0e040340140e100d000d0320030a0340003085505010036081450b41d0045042e50500f075940000341301112281200401e031081003644a4004d92040011000081c1d45800421900c1d000a000241c8109030351101e807200d40c804c89000d024008041c0400040101101c0b521b2f40248090701e0b581c1c101000c51102a641c1c0001181d11018408407102c0c05040110402c0304070b0a20b0740c4492000103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 391273300 1250 391272050 391272053
    0x209040f090f060e06010f14120715170709030b13050f0d0305060907050a081509070314070903080f070819020102030105030f2a010c0c082d030910120603 68
    0x22a0342c4200c1d400c642c0c0798181000c9001c644d600140e11410b840050101b484018544007544901003031842e01e41c1d8005020380f2180d200d842c0140505401030800c029910000d043c641d10007404860824641d004072156a01885039495105602c10140d03035104102c200d041d10b076a401c2c0110100384200c01040c0c0d01c9504a800c078000004a66540c0c00e10315a00d080c04540c45a50070080d90102c01ca40c882e0006406110a40c11148100c00b0740da0403009180b031845a10760140b02080700c0a07400c40318800460384030750751a10142400d019081d0301516a18003800c03001c0c1107980b02c84031442440498000c811010414809015003901240c0d00310307116100651a110032150068041d4009128031442805031000100001001264011400d007040c15a0801c80350b400101c158032055402201b810444181040300020300e00722030580160500e03000400c40e000d0307116180010321102043c1040c49502240d52a0b81550000080c6c0d0292807044821101002c3c0308034007103580603005c8080950403403c1410000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 391274550 1250 391273300 391273313
    0x70e04090201051b101a130b01090f290a200c060d15080a08191106041506060219061107020a03060501050a060e030d0e0f040f140709180209040f09 65
    0x389044980d84c1440842e0704800f41407200e01841642c4c541100e08801c041110071f141e0350200a0b003000506140c01499102c1408222140075900f10003d444210500344040354401c6a04024525180300707154a0004003007401000089030b00e268000841c1000040010080d0501c48016241e501508a5446800c102800f00244c442e018058403940541840441c07400c01c0803500e20511908640d440d444c00906541c1c506140003004c50340310800103142030131518040b00b0320100f40214001d80e50540c0000f01e02c1010811100315522100c00d562041040c8425020010341441c41c054020100080c840c2042d5550b070b06074801c2c08002903115514640120410007554070480c1600d4050702d58100d81c58031082c040c0da412200402c0340784d0580c45826465078184c41064a84820500a010a400030750040042802d880c4061904001072f03449041c095001c0c4a180700840d072010380340c900003460501c1d1075180300f1074216144d495140701d0380005d04021251540e82107514000813100c4100410724139805d294 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 391275800 1250 391274550 391274563
    0x180a1b0b0a0305010315060605070b0a0908070b0a050612070302060c0304050607050708010c0f05031303020f1207291f031502030105010f03090506010b22030506040302070e070e04090201051b 84
    0x303c2d0b001000c8450803140b203c0c05e02c107c0003540c0050306c0e810310b8030050791101d82200380700910107041c15446808001c0011407001c0900308003445441a0030680c2000134081043d1000246100e010300241520b1100f80c1c10000359400840341c064a009a99804030386072581980301d036070001c94018800090041c04c0040c001a007000b2620390700002c01419061030404c40e004003100b50f16000107203003440400c80500d000d0707411442043c0b00e8011242d0440700c0b11801410000c0980722250404000300d00c1b4428000011541501c940c4041011307442c03000303d11102c40000f2000b82061280c03050100001c0040410b903004d8102454115907100550001600300401030342c02402080d0025130074279090094140a4011400710641c00406003d042e0b080446100451300442c1000d031144503031140400341c950a08541101460280014159034038060501900d04480b6174882211040b20504100350241d000c6040c10b0f005408550220722501a030004849034007803480920040340c0d40c3e0005c40d0030510009103d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 391277050 1250 391275800 391275803
    0x1031803120c030e0a030e010906050337050a150506120a0e0a0506040813050301020a0e01030f02161109071d010315031b150c1709060f07060c0305180a1b0b0a03050103 74
    0x4000c20f040d1075000864bd2800142c03607d2009a000d03100f45001200c184144420360315041405a8505541c0d03002139003a500f007a26210032080d41c600d1044804d03540d0302000d0000d440c06560803841c10740020004103440000070010346002d5511200808041e40510400640b5500724040f01c595040908000c01541d01102c110710190001070400a036a0406000391056201c42ea201d003a42009000c0054010f0b1a6100c07000184603400c2000c88220070703024019948890042450800c95600042031000008001c0c0555080c00b0440d800c400c3d0381c0b5030400c007080f561074081ca4007007244443da03940703e81e4040c41d41e04010f0102d101d10f070210320419125113000e821520081c910442407241e400041e140310960743c4010700315241030b4030b05555017102c010007001440b801030503592400781103203040061038202e190101c6455072540500b20401d41e26018203600701d1440e0804440d2030141b00c1416aa40c0b0700020014043d8a4041034901c11030030f40c661840003007448a0304281c1e0343c103107102d00070000c0009010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 391278300 1250 391277050 391277057
    0x13081215030d080106050703030e0f031804140c030a020702360105100207032012070e010902040e1302040f06090c140f120c250201031803120c030e0a030e01 69
    0x4602c800c0034400c0b421641218001d840e664036004158401310003514000624240600c6108912810644108010004d1010b1442c078803040010004c01c010076100c0c800400414000e22600744280c00807010126504801580380043e950520b9101043d6006c803000c074140d408032803410390b11034501064081801451040710b0036000503030b2204100700000300200081801a0b110000510002d181d04108150030602003001822503000040024000c0b218104400d00035001a9000c000b050805050180580700005040d418181071039041f08202c0401481d14406c404610b00c17a00c01c0d9121607100f844014011201440b420342c5400030000545100c06840c0d0000e118401d0b000c1c02210f018080daa500e100c604c2d0081e1400f03500070b82c1989119006001c10b54001404c000c00a140420441c000c5013006030300c25052003824031800058200c40700313007120301060008024030704002a0301c0400a15000d02d800e034000b8850300d030040301b100107040c494184040c1d4812040b15030103040c2c12000c003080280090f42e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 391279550 1250 391278300 391278313
    0xc03090506070306060f0f020106030503040801140f060d060b1311031006030b030d0c1e0b190e0606091003050303040803090618060f28150803121308121503 69
    0x2e80840485001303201d07000019142400b0a9801071160403010408600d501c004104c05881c1d0f25041d0459001c1da003c0040c90b951440025405081d00904603405100403a101165150110104841c400c0703030a0010940e17907030780740c44082c29a0303000010001c1d000038030410042040b20244907012540180c40505500442c10b070001a650301c2405103100c0c151014000c1c0001d405020029100703030310300d0b4100310750203907619408038442091a4103000b92503008030b402140908294980c840f004104850b8000141e04154407104c0e0f19400141c0c1c182c00c81c0040d55202029603c040d030103202040b5942000380b50740400000d020a0140f25800365000f801440103580141c2c0314000f103038a5140c0c640803c1d4800d0f030000000141c0104810b01d00c2a4400010341e07404204401100c0c0c510004400c2d0441025020790322911143d07421205034600004d841c24000030340c64802e0901020030080b40003444800040420f81000041090040c26240740108207080c030421410900340c1128402c2c2181920390003446001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 391280800 1250 391279550 391279561
    0x9050a09020711040b040b031204150e01020d1d030a0305040f06170106052b091407140609040902040606020703060509010204060c080304020d0203071d090105060102030a1b060c03090506 82
    0x144210b4140c1680240042c8051816009000141c610603a03825400359444209070083d0710140070b088648c80080c0b191559450405140145500720740040302d040151003610110300740d0300002c0d210101c0340141007032501d40c5410024540d5510071603030b07029054000d034401b80040540060240080e00c0c00000040c5071030f0f0702c1c1c0c5011030340002500c8244140552507001042444d008000801d4102e03c2c41c15003c8403000c5c1240380b000ba4001c890254224655030308a03c8042c008580403450030800c11502401d00075142c045100700c11078101d04810f1146100080c007044030f903956440540d8440d4007400600c86103958039000b079100c100134071003a40c0c101c0c1001c1c000782200703a042c82207400b50341550f11040e072104583c1c0c4800c580e5820042040b81c10000c0e86280303d0141c1e0303080004074003c0c01074454002101e1000b141c81e84a440b0050700101b941e0313040c01c007400307a2a078011041c0e562076001480d001c10281c4102900c10103180c0c0403040a4140da05d810000004150316410101460303005030110b078150b8545 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 391282050 1250 391280800 391280819
    0x6152b240617072903010f06020d0e01050a0f11010603060501061107060c06020a230c010c02010614010804050a15020307141804050c0909010803070302070512060c2809050a 76
    0x491201540b83e070403408080c007034682400c80d07461038458985900da941c020188a0700210340e1003a000000d4024003031508104043d81002000e51003041454040340703407401b00c40041c0850240740051810700c1142090380d103c0c070f8482c0301c02015681c3e100000780b02146da00c0c00e100008200a001d8100092010041e09450b0803001908508607036007541c504481c40405e8680000a4000d48414010803481c001281e0240c07500c070008144805071140a80d81d0b4004c0b503100c50382102c00c441c44000030769040c1030003000084001004840c80c0329003070901c401c0c943d03101d1500e9030500042801c002c140c6411110565540556a80038511030001616003030904005000013030401d010722180544203540c102c0443d00d0b10f09007900b2190f0440c0c0030000c840d0419040a0000d40c0c044401d0300840f030b00e075001150960615504002c031600400c41500c4000041c4007040d41541c9440c0c0080505280440c00614001d0030b128640c3c1504045440092030101c207508200028040d94692041d00d109140056010400005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 391283300 1250 391282050 391282079
    0x30f090303080106030f180b090d030e07151403090c030c220c110106031a010902030108030403080a120903082e03031209021008040506152b2406 64
    0x10581c6a840301a880d090f02100940306d801c040d42c10143e01c510307041186000461400043c4c2d07126800000340743c07805920961400c000521351104050824030714080006010420405403001e101b98000d120140d0801a03a502500484043d04205e00200304848441c010404000303414084040d100d440c400801001743e13515400b110141e0140800b030b0329040c0b615895011062404803030038410202c1d031002c920582140c0b1103510568114030410032a031032840d0b180e52040d0140228880031402c550414612940e00d000b40d0000500c60b84000810a18540c05444c000d41682d0084006220075541490000e1002400341c0d0302014a5654001c02e52074101040165180c0340e1080529000503451514100c0b408900300005451403591070312110f025885d280340583c0900c58645440801313003485d26009242035001004043c00c01800203103a039166848440c903120342d034685c9a0300c03039100c2c050070413540c200b85034103c00614803040c103e0b03200740440381e1220b140307040340300c001d001c00c242503440000076400070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 391284550 1250 391283300 391283303
    0x90915100924120f02030609010b0a080102131a0c01020301060504050405060a0311190f06020c01090f06020d200604030305181c03020c071e140118030b0c070204050a09030f0903 78
    0xb440142d082c490b02603124010b141c0b20740541ca07241c2c038411094010034101074003540c460a059446205005103424079440040042007000b008500d821002c000150032000503004a600c0f0900e0218650101030510301929985d10545008541c0c9594800000c1e10503030141c42114080c50030300f0001040b0b0710304009900c08030394215030305402a0340c0c01010081c0d2061241c2c2d90303003001e1205c2100030840003e03980c0c101e00540090b400400401d90420300150488a113980681d0380b10550890520541d0340c04102c11510844505000355000d42d0000b06044022034900c006400b4850f0000300018164075422441c05014000300e8800d040c41442c2207251034082e00a01b00500c1c80511225004e01d603c02d030700a204040c03000c015588010b48610102e1096030001104d2503240080a0040c4840c12a920b2001c2c03c04000342410051030500907992004000c0f20700c009001c0201103c0010780b20600c440407200c03030960041040211b494450350796001002a0b250980000305440c81040170140a00410400d99 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 391285800 1250 391284550 391284611
    0x209060d021e060d0203041b080a080a0f120504050c040f06030b0c07020a0518040b160c060e0f030f070521121302330301140909151009 60
    0x35107800561440c450503540441d0414000c10000c00407404ca0301c00f42d07014a1285007030703030b01d440a62560300300c039080250010311954001c01e000781d0008120358211840411300d410240908400d820054480481002010380402d08000c104020401c5c04500d2044c14a41264200020002d18120303500300c1d9103601004000078040f102187d000080e51001d4404107100801041c4402d4441001c190b0b41c14407901180000320b07810092004021007450816407141d0344140d140c10000219030010300101c6881e1001e011560340e0034290524820501c1050384402410301100d5403038200c000c060360241d01041c400c3c0e8060062440c12005900e4241e054080300304041409810558611850200c080014000d404084c1e4100002030058a8001c40c2808030200c2078410040056003c080d0489401c1e81881f00c041c10781d04100520071102e24190720200300000740c0b182240c9586216216280800e031504d402e24804145017003204ea401c07080c03510302c16030300080002c1c031007034000034050007039401e00030f5540046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 391287050 1250 391285800 391285819
    0x406020d0302130504142d04020d2d03030608070e01180f1109030606010e030d0f170a0213090207030903060509031b030307140412030e0a08030a0c0209060d02 70
    0x5a4829000b512034550400011a03d4035600c9000800311418000c241d031004042c007040000f45080001600081c504100100c0c00640c0e181580310003614004100034450742d2203039180c006100e04070701441c81d138040645500080d0380c0341c00b0400038490104442140040e00f400350105200401142540480307410520410051b428030050184159803000640d0300d040c0c1e00d20400c0004142800340000c91001104440d0390752000300181810f042c00140542e05005e61409855901d40300021020201d41c494644450b9a00e03401c4e00071640580b0010808140c02c080c0c40503c64120625030050113103840306501c01802654034000c40040c1d01a010b405004200140710400c01300d14030750002c540c40007800c0c040d40e02d09288030300800301d28101c114003010380d41d001104100405800c003100d414442c21500300d00d4102803510303003406c4061640850090030030a510030301d0035481d226254500c0241c0040020359450740400c00008001d034002c00800e030b11640c0590080f940504014070364004158015054010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 391288300 1250 391287050 391287073
    0x150605102c06070804060905010e0909060c0c070e1009060e130f2909010f0603050309040b0a080601080a0b0601080103050d080411060409090606140604170a080a200102040602 77
    0x3002070880080ca800c03100030880800098990030052020748500d4079010348031390402d00010440342450a0050003050074405218080100007000c5502c40b652420050390344502004080c01d10744181d0082c90050050300034802d19080c004102016501031500800c0700d036617200200160064262940c1c0380b41042d107901c00300460342e01c100c001e0b01e05006459504412a103518444219014545a0301c6890f0860042c070034000c00a002c1d2800c807401c00803041c40610b045072140c544078451901103900c5156180b00240d400d41f00c03240601d004000c0785090345d04035a51503c90f252100c1c44054215800860340380001c10640c010b01d2014140c03034000c0018600c14480d42d800b034401e5000508169000304101000038003d80e1000020f0020300784500c40031840b440c0c2c5240840a903001c0380c20040544032514004421500c4400079a41103429002204e0280d0b10259007a601300b440790340c0007400f24180024901c5210340c20000989000070800b468860741607402c000b132401c0303000b24028100142c01043c80c1c0407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 391289550 1250 391288300 391288367
    0x607020118110a1d1510020c1309020a030f060b100e090a0f05070504050108090105040f0206030c04050d0602071209030b0a1e0c0c031407020607030c060915060510 72
    0x1908800d000c0c18031503d080d200c42c240720401654805284003240c05004001d441c3c40940c01c0e907280c60340260707814142111580c43c00b0b91a29198250640501400c610206480c991508000302c8250084d0807100d50a40381d0408a03007000c40168241c1d20070b030403c2c0700c12009060080e2008a04500342d9102450364103880c00b0170000c1e05000c1c3c08080202c0d00c0c2c882e1060f02c64054071419001b071a0b1a154941c2c1c03140307441c00140521a0003020452180d150104000c04a5a50f00030040c1803941160007550f81d68910715005010f010f03031b42005030012030340d005010812455034014100a4002d20440c041c072903400b1001c48004a440c0002010f4080150105004910a0b08181009a007800c00c0542e1502225880350444200740302900000780a45201d1007030503000004088030071910403200307240841c26004501607110340c01f0000c0810241080090601209074010812a6407017140c10403045105640c140103000140909031282050882d03515000c1d0007881c1035100b41021440342c0c10705891400c401d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 391290800 1250 391289550 391289573
    0x1401050703080414070611010e150c09120d030b040f0c0f0e0301200a11030c0a030e01051204111c0c052b08030a20070b04020105040807030507080607020118 69
    0x12189030000c1e59602d10380078414005e0502404890b07503002d207072800c003550b05400c2d40c8030344080d1503c0307030408488081d20311000241194802d1900d1500c076520554400880d10240c0031010709803590140034004034074150f05400034502d003403080314140401116074031214101c800e480035100200e04200c401a1042d03000e030003c1140c2c044020300019101039078030b4038030ba1062440c1681c00c1c1d420304c0010312070b41c11a800109440484c5c10080095041960481e5819912100345402409000c1007000484150384184210717442c00244021104403410180f034001804141c4904a034442c07410200002d80c1960204403402e90703142c00401801e40036140c8402c4c024240081c0c04008207202c0c04050108024204030300300d84045101d000b541c4e681e85800d510802c200c807070310135501c0c844071881c61072200d242c2c195805850800307030046e81c0103185440310b100584c0c0c41d10031540074210600911130004140103000c00c41c842150419010b1310305540d00c0040480c02c0301d80c2042d04c1400e8001c09142d00011841030301d280e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 391292050 1250 391290800 391290803
    0x609050709021810020a0503070f080f040b192610080312040506150a03060e16120308101505030711030d06170d08160e0d0c0f14010507030804 63
    0x80d1000e068403072140308141da1181d0395007084904290805045401c10a5000c59051010b10150940c000e5a64503d6200c0c0b15500024155982111004090005150890b0f24040180c3d4840d0707034640d99074440c0e8119801401100e05400c450316505001c1c02d0082c8080c2c08003500145940142074040360000120542c05441015a80d002c8040414683c104000400c209030400e4080025803900d40f4201c2e2800d50000c2035500c0500c880174841401b41c581038100c4003502d50091000c20303800c098030355452810020f40510060003c10b141c0006142e90b42040940a940c0607950756503203030391180c500e083c48098520850300d80c000460484201c443c4608d001c0c54000f80b8901d80030348001c0154204a01d15004040080c02256840508000c140307110030804407140c003054098000b0303018981d0090b0401e10024601441018810303400003826102d0200d400d8010350092500a54540d0782c00d0081098205000b04e0200401c2c01c034011861031200d00c0d102651003c16582d151420506a80458000801400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 391293300 1250 391292050 391292053
    0x140a030e0c091e0106021b0f010e090a0507020c0d0512070c030b1f080109050607030515150909010609080303070f0905030a0609120905090105060a0507170a031a0904060905 76
    0x81c21880303030742d60942c00340181d401e264801400807900310408035211040e80100d080d5809521f40c44101d10b2000d200c0c408608003111800141c071402001a01e0000156030707080c1d072105242017000000707400c1d03500060060425508540c10500580c060094002c581740000e00b540d801081c54041c2d901d8a0f000420420f0320907100307200c54990700d5541102d00c48041e50325100d440c80030044141203040e6084858020203051000740001c20690702d40d9510b420001d040e0001305604d84001a030950704031503a49498042c0030f411494030410b081c00b1a282e07500300c44802c0e807007100102c000250346032080b6012403d1350b0290001c0e515580380c001d401c1e40c000302c26802c0ca4040c040602d000140941e014890011054042c5602282c512140d14148040c0c1d40085e00700c1d400c2c04800da500b4400f5440b400e100b641524000c1d555180d8408485a0655080c01204c3d0010911502c00202800018942024000307240301c3d6103040c000d5442c94400400d08090f10703820a50080ca140d000a000b0a0950b04640c00c494066030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 391294550 1250 391293300 391293313
    0x50d0315290c0a0302030901020105060d02300313050907050301081c091701020702183c04050f0f120d0c0909020f071b0b160639140a030e 61
    0x70001c900f4046107690075405038002098810040d42c082c000c00358404000c031408c15440005a002600c14034186c1d004100041d030700f0502e2814800c424022000c020b090400b2640c60b0342c0704078425440c1050600580b4082c2c2001c401140010b40102c0c2a0b034180d48a401c0a410002c901c002d070034000c60005499007003000f4519000003007001c0c0a001d5210640c3d4106d0001d40e403580c070350040c00090b40c035070104130884400305000c01c8200445004418221491050f1070044c030260300802e8600c0d058005400c03d040c82405050204008002503140c0c0b000b24408141c95090500707542441d1070303500000100d81c40420401c9100940e129540c8021100c04003810b29900107500e4203418070481e0041c1401c0b2550480010759031081c00500407400311200191154442c41034103001c00e4610600482c0030a94104030301840c000300b000b4554200c824000ba4100c03100145140d000707600003000c0308440c5480086030400404a0101d0f03c1056a071f51003080290446160003402c01c400c0b4000c18100345800705602560 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 391295800 1250 391294550 391294567
    0xb1e04231317040603050a0b0a030201120b04090206120403021002090a0911130303230c0a0b0705040b03090a021002031306231c0c050a020712020406080a050d031529 73
    0x3440a800a0540740e6030010b520311f041540c034011120301440c41d5100e10098801000140c3c2d0180400e12118400400841d0120200c8041001b91088034802580003401090030b0503003401c00c41c3c0300380c8164001d40c202c90500081c000507100702d103e580d1070180c000c0e44021080c001111030b600410009083c100b50980341a1081a84d0000000d00d81c00403800030700c801d5680700302d250014203401120440d04103810b00d081440740040d80da940042d8001001040348000044d25a8001d10644000f4500c0000c075941d240741040415440c1d0440002c00c80c440d0661180c9041d100f440001aa088010042d8240303140600300b5600395480d102c466504a80001c2000d800303082d9800c51005000d00ca00e02030821100304220301d18070300c196400192610304000d000d000d060345c0d00c0d60008180b002c440100c1c0302e09481246038004079018141c50707002021184103e0f10032030200301c8009020025042596000c100c840b140040d294000340b403902c200100010400d0f010102ca10704100c6c400281500b40a0307540c60441e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 391297050 1250 391295800 391295843
    0x10e06100e01090b0a030803130b101d060402090a09060e10080c010e040b042a02010203040b0c03070c020a12020a0806010f05120f060c13090c081501030b1e042313 72
    0xc50b0310a12101079274084004000300080040d400c00000000b005280b41001040c035015140c16030411980302c0c0301c00c0401e0301da44a560407104ea111018049504050b01e5071a200060310390391141000e8003004000203200400803070002c009951700c031806441c0981074040116031407004400c40582c869034807071001c0950381e5244210b20494106070b402201040216070160f4440c044040550150f900420030040000d64110096500180e80c10320f460310798591103c1140d218440300402500300501340d8011408a41b8610358808480c0f080700e030100d000307468034000c0392500710a204200a0720344844050080d8a003200005c194095510100d80500340807040c0d0344c0c503203c0c00344d510700502040010720010464440d0f43e00710260011031001d211001c201d8100070700e8100d0003000443c0f10070155625400350b0384290021070310340c10003c20f2400e00c404240c14442c10460840b0300c00c1e01c618500300c0d07003880307042640504154481d018141c200607030355003c02440c120651890110745c0c01c40003220034880c01c0381 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 391298300 1250 391297050 391297057
    0x60e0d020d080d0b19080705090f2703030a0b090a0b010f12110d0b091303090303052b0506031603020d030c02150309010902010801090b030606120304080f010e06100e01090b0a0308 79
    0x10b4100c0171104601c0c0410301420310b50b0310f40025008020007010080a021808442900401b6070824014510045c002d1404103d44039409030000f03000020070f21441c100c641d009011114000c9038098400c1d110b145145040f15810300425010544084205015a018420304100c002444102088428441c452460307164000b0702d14030b0901d551106d649000f418145104c903404490440c2916181026440162400e90203100040410070001034884c40141d01141021002007004402c2c000d216106003010051301080390790038028401c4403429803402602c0c114486c11240c001d03001c11018252514101d800381300c010710a903045000c00303170f07501100c00002009610a9030f140d000040e00301440d100040142206a0100e0786031030520040716190358001c10b0464005004480c0c5600408076030401e242140140e40c0a84a40c2c003c1c80610804540e041d00b00d04403c080c40300a58103550707035640f03204030207880c140600d000c01072400d001404048400d91003c030392000e009002814981c2d59a552000550 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 391299550 1250 391298300 391298329
    0x42402210406140411041d0f06090d05121602070302060c010204030c091103160e030111040306060b030106231215040b0111030f070c0803070309060e0d020d080d0b 72
    0x28414420041400720b50301c20340160400b1501c4400c0345040548914000c0c071041480907100702d0b95120040400014441204009080d040a03101002c802c41c0d4015281e01048076404507500800c00710b240454456401c480c0c105900100f01c01050f1603122513a011000c10000741070070740c80f40031808009a55408042c0c008981d1500000d6580c81c210702e44100002c010307600003c0d04504003e4031401c40c081440c02c2d20b91180d9003049111030144255411280e0103140304e4505d806500c1c00001980c1c2e4036222009100b9a40201d41c140030b640daa501d0f40822510003403092800040c506000f101d481d6004200d49151b00e0300c40034131030313050910030802c01c42c0c5403200746d40820000c242c20440010900341800385000080e024206200e031007081065071600c900c603403c003004400c2e400145a50400c03005680d654081c140c42c200b102d0300c451580c5406070010036a8010344001c00c2c1d0728080080c0030b181000e03850440c07590280c070392034003003511f42d481c444aa0446904021440c1c0c89444002c80303500c0e80c80708080602d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 391300800 1250 391299550 391299607
    0x210c040f1e060201060303080a09111002010b09060a050f01080405160e012c1302031e01090506010f08120d0b090a06061128050f0102070f1406042402 66
    0x60074003024640341c11509911410669041410810200c0c0d0000007045d408050b0b0080130a90b9541c41c54450415a4194500c0d50300c010340c01d143c03640e15030703055000c10070450055030340c5161a2141c10400c01ca04000f44105580851020701a28865103e02d4034290841d218a00300c80c5d0600c0c000c2e60091024031160047c84500444038010000e0300c0c2d500c20858a407090100705000081f84c14034401c901c90f034006004844021100f48841e0071501e003080384132054071103140450944070313071903002c18040d206e510004d8849215120003c0756032403401300780d0300803902017000502c081440201c400403d50041400702541503907510320111140c842440c0c1c80e00c1081c40d0400028020b003000e10190000707190b488094110303401130124447d04060140c04100344018019098007440c0303145065440c0c52201c00c444c00c01c03940081140c0b810061019000e0348030f2403040c1c0006074041d0051042d5555488125005001d02c01e450700c1c10b07096101008900c40c25085248000b42c80c100c4018a010340320003000d034030f09858 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 391302050 1250 391300800 391300829
    0x70218040605040b010509160f050f0301090209150a090504090218092104060c02060c0109050307060f05070c0302060f2d040b15060f0309070509090f12210c040f 71
    0x20840c0c41013070b103809054201e85a40180c181241442419120388600c4403d01129a0710001803e000307100740c4841c8000c801d229956982c50f0082900607401c00c1c220f00340030700380d003441140040c070003c41515000416656144000b502e04810840a050003800c182d07040041c50040b00700720723400b81402d244a09014401040a200c001301140c0d1440140714849200510900c024000070307600462060b50150100c505a8491641e082a81d00400d0031190080c04e510000800c00200101c42e000741501601a00d001c21030b9540d01d44058811010b5081d000300182c022a000415011148640c1da411841c825086142070411072090710080100744d568414080050040004028515040303507400980d0322060303991043c0540101e142802001825800c0020200018120b11400c10020009201c02803002c041824107901c520345400d00c0c90034007201c0b4080c400c0805549420007046a400c0d030300c2d10700741c200c1c04440304503a0120038001800710140c4d04010880020001030f0f420020001d0100044520700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 391303300 1250 391302050 391302053
    0x71d1203031501080115050309100216060b1503180c030d02012403050c0d060f15090e06010b1e1603050910020c0117180d0e100c020607030507021804060504 69
    0x541080b4504281003042020040c000b2071111203c0800341082401c3c02a00c03030b2102c8080a0510004844080c0524404a49140d48041c0c00120481c1703240506000c0001070180000d2000080140c14031680060040001c01c0c808480d13014100083d04130103081e0b80c400d021a0000a042c04842092540181e4481950100e124005146944a0038019025005043c5150f4519480e00b08051032a48a082e030040340b4002e02c0202e8105203c20107181d1001c000c80c282d40b480040c3d69488901500c141c951501d01d20301c903110400640c1d2810390b51920300007828141c640e41c1c8841800c172a041d0500345da250500032104000240000c0c200b03654420380f611600c900211090020110b40b103120702e411584444d43c0003000d40d23001200215041c2d90304000030b5050362515400d11a04112440d02c04284c4103160603400c9150f800030204a01c0a804c690303060136020040d0040702d18804050380654810410455517000034050402400010b1001e06401d0269000315015030b0740c90412241a00d007680c58404010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 391304550 1250 391303300 391303321
    0x201150504020c060601032708070c0e061e030c0910031a0f040210090e0906070f02070b04140f06032a07050307170d02070302280b071d120303 63
    0x601804058400318140300c842d000035590351202411141c107160361003514540d0440200200241c880000181010841e1245000209c940c4030001c00c1c0c0d41022021b8010030310b07050031164940101c10042c0240e046504007001c002d810701100c16000c2d403521854503840f20075100c00421501c100d0000e00d40c003048500d503040c25901d202e40010b100004250a0080181c40c0840342101c0e50441e4060b071300b80c10f0308012580140d610317281c2500300f801500314603c2003180e50721000a41c1c0c3e101d05103680e68142c1505403d40c069036200c10340d019100b075601c8107000901000c030041c0c0881015030001412584103c400a02056169005803114089140c942c4001141c611248400c2e040c84802c504180c1c1c50f14025441c0c15440740140c10005000d04d44516600107c00b01c0c03c0c00b500d8000c4003a400c110f6a600c0146000780d07039015030401c07222243d480d911001504030801c80c0100380b019000103111556036038181c4201c4002da0701d02c6030307840c0c01c001030040c45440f900e544010542040302c2d0f200071981c9003004004038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 391305800 1250 391304550 391304591
    0x10e07050103090305070807020a030c150f02010510030b09070f0b0c1b01300509031b06131b030602040f1409090d110c03010c02150a02030c041206020d05070201 71
    0x107040c1403c0541d10000070350700c08101c0d00800e4220a25944070940c510010b1a4120300c0d81c800f816082d4015404901c00809840da0100000a52142d031b40400c1041800c0c1c0c00e0319070072908210031000700c13541040803503000a0326540c00760361801030340d0460b030321016880c0c2c401d02d203504401c40001d404202412441802c010b1032141c1040d80b0300e03100f40031700e540b40004c2c10a004200c024141c2e220413112075880c0d050700c401180242103200c0f03080c4a1403400e4014103580340c01204061898135884100700711a0076002c00c616006200d10351070500344104603221040300b0030820207500c0c80c501041c200040856224800b0308054940038403200313545072506c581603501c554403404040c032828015003400f003800e1000800580507011400c00c10700c18000e0101890a1898150300c1d2500f5500308458103480720340c0402d01c8c0320760b290801c0305c4000a480e0002d03100c0890000b150f44102d207402c01c2006012115039035442103101d910548002d40740c0144090043e00b603034415138200c0003503074680e403076200e5040700040da2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 391307050 1250 391305800 391305809
    0xa140303010e1303020a1208060307050103110304020d0c17030301030309060f09290f0309060916091d102c0a080304030e0a0b0d1406100f20010e07 65
    0x11400c55050102a60500034003503c8103c0742c0e000103c0c08420940244800700459410188000c107800908402529441e07088507807511030701886001248942c0640b003050400762001840303c1c03c694850307081c0000301421003426901a6444e003400285445402c08007100e4107140f5011b15100e51562401829810300e5402a000703002420a252040030390100c0721204030350006245414a500d404626080744010070802c1503c8040065035114001d00e00000f10302900360001210701c2c0c1e03610085d00355160010010344100340109000208038806c602e80100700700201840c488540301c481641128a0046804600e14205480b0104120780c1e05a503d030303407500400342c50a20f00008182024440e142d4628110080070101c003c00464145845100d0340201c825028060880302030320790851000d640c00045e00210b0039401e250380b0305106c0c104441c1d0140030787c03c060940c18803066010b006507102c1402c2d00300f200c00c01c0300310411190066001e501e01800c1210702000014401288001a4101001a040f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 391308300 1250 391307050 391307053
    0x7080402030303060d0809040e010204301101050d0504060c0206160f050c010608010c0507050d03060311010e030a02030102030a060503060a02041a0d06030602071208100e0a09030302090d050a14 85
    0x20000561404000c036a48940c2c11100e944010382c1600d0291864050140031a0300f007807400503101141c1005500620603114200b5040481d94800010701480141e40c0a14064085400c464100050409005808143c0c0141400c4d030074240da5101400c00c55404842c165241515102054081c41e01030114640200c050255071140220300200030782030032051301e182000c110300000c040c443d08800390b00040c050146500244103420f00d0303050050151304010b00075246405511150300520380684100000c0703951028120f41c07411012801034070310342200c220031074160184a45d02001650300380b00851140c2060507001820078204414140340080050108014900c10081488001c01c541c045564400d000d0000907500e0001ca012000030348110740c001480b02d80003107245010000b000410080301000351f6160303034443c0c0d18030581009050082c405c80c0640e0301c0101c00300386090041d401110085019040c05460700620b00e0214899200c481030698a0b13410089000302040b181c4070304003035156400c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 391309550 1250 391308300 391308317
    0xb04050f06060a11160815090a020a05010807030906050f220f020906011b03091401050a0c23030301170606060414010e0d0503131e08060109110705060702030702030607 74
    0x20003158040c8a42c2d03860f0801e1000c00850f50a0464040018482e4800002104400c00c0c0e81c40000c5a5540408098550100d48a400041c0002c000103284815107030001c140794500c0d49004019070381c54401400f18000c150300d805081e0040b55483c0610b03030240607184c2d99144c5611701800c0011004242844210800c1e8401e0500380c0070928105040741c2d05501181c0031070300794a039140140d9000c03a2101c0d0070110040c69841900905401c62205401c4a1a544804000a030300300300448861098524902c00b00e07a210614801007002c2c82070300391103024200d4aa420060808030070a203503170000d82c0b2605200820030526142d5460a1200540001050741c040e402d041c00e1246500005842e1780d0030a04000e00b2030341c00d014a946105c082c0c403c494100c03042c0c1e07644120001d5032115020081c00742c0c10b2003071104080021424140c031200000c540310900070300401c0e42401d10780e40184c61604440b072000803040c8450004607505100300c60261070b035600255640d042c5031041c1400c00c480204000140300200303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 391310800 1250 391309550 391309561
    0x70c020109030b07090e041401060b120a0e0c15040f05010504030b070c021305010e06010818030d090c0e091510060507021003140903040306050c0f0405060f040e0a0b04050f 76
    0x1e03040c5056a0707005088401c40c1c0e440107001c940c1d241c101e520070300d2a007108500340424800c1c08840c2c1d07002a003420000303008890304d0348110f0899101e00d506404034002c1ea100042c0e1508030307950122561a40c00029100c86524000000b0249002400318181a80300000d0400445a0903100200105020b080c0103040030b1441d140c80e14800e400400e88130903c60b464030040119a61805005000c0c0c007010000c0007156100d824102c10038004403501d078046110f980c04100c004403c0789402030b0b13240c2c056004500d8016400c0c0c030346002e0102008216040711200c1c801203010340340c00441d0340c0f24205100c02405d480d4144a140c1c0700d0320340083c040d8510011000024040d0541c010122120503806503400c0c04502c0d0700d003104070000d0484044844201f020101030040102010000300304490003007a040c4042c0d1640440a421441860300d12211250108420409814100d01906900d06c808400604050f44c88a11180340c4038101c400c0540c2c143e50b488454010310b000d02c12107400414030070005041c0c1c42c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 391312050 1250 391310800 391310807
    0x9040302031207020a0b040804150c0804050f06450105070204180c0906080d0801080d0804080f0d090611030f190f090809044b02180306070c0201 64
    0x15680051180901e900010f8820341c0204582c020955201c500003080d0f140c2400c1441403071f001401441410120002c2600038548544101c85503960803000607840c3c140307040100180504000441a000340041c4071400d0104515075041c1c00d21818014a6841ca41154010308050040801c9c20400c45c070709030158140b6039034070070203542e85554141c80000302d03c801036071000d0009a1051000b0179091821501080800c02900076204840b10581240c0110720381c5002907401000901810310958402203a01030501e2040300300c2508030b4050082d8a07c0d000c0e41c40d02c81d600590003045211005500c0d1050103080165a200360100710003140b44840c2142081c0d035000d940903401600c14242034180541e0f40e034880155920007a5030194822041144202c1850300d00e460b80c2010544070300c194901041130008074929405600e8510030104035992160120300440030a00111204860204444982d000c5200300740c801044045801c030744490742c0c1d8030345200301071404800500c02000c00011b81d82da040140d81 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 391313300 1250 391312050 391312057
    0x5040f06080a090f03020a0507090b1302030705070c060f0f1e030902060c01060618050a0503030703140d0c050d05151c06090f1b05060f0f03060f030d0201020406020c0904030203 78
    0x1214544a00c0c50380720800740101410066001800900d100c100b05403c0580008480310741f00d00c54010764424555846003442215800c4072215000441c1d5142c01d0140e051a500446d807000300c0d0f0070960300304141900d6000e902d01541e00f204011415031103400c0d400703d410041d444602a90f510304604c1c03004580d000c079100c20619020200906481d01345030021903450005a42c00310210390001c1021a958400082100305e5400800f8030703440c1c00e074101240904102c01a40295100079000750b181801c0350350126404800c082c0260300701a0103200321080c0710b89900030b1200007660340c0c0c0c402d074640303e6103041c4404880001d86600c902c810300000d084072070b031a0340c500010620184c607001241d01865080ca0782c0a0000070300b0090510300e07580603031000c220011290180391516a000142951313190400c0c04024881c0e03455060340140e080c86240100c0c03a516005641c40b20018013a40721618500001c207260052003c0d800002d40d4000c1018400d0039410000d59068500850700d22010b030408de00c001e9145d22 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 391314550 1250 391313300 391313309
    0x304050114041b0e27072c010902040e01051e19051206060102071203271814060402071406040b06040b0405061302130b030112140d0801170a02040e01091205040f 71
    0x4501c1442c041d902d80c1c0900c5114000c02e4070004100310075031f0b164416040b54550b9400031490381d00f800300100310140c3c0340c801d40d4252512400b40f0b03001c3e6428541042030300c6240c68040b0420b02c90700c5410083e907454044c1c40038000800c0d42a075041c041d04040400659141e100c01d84601a8010400c100f680e82e8001030b04403c840100c440c0342c0c8208000c1c201190301d042e80d80140601d03040c0c00c05505603402ca0102e17401d02110150340b114191800803100b4001514262641c90880d039404a022030020315280d801060075501c907141c5854490f01d5204400d080c007004503415503040080004001c40760500d40543d00801d007084404202c50315240b00040c10041081ea2030000c0c1e19030104648500780700014a0a02419010404a4070303580c1d55010300c8200c2d80d9450007141c1c0c010540703904003041140001c40040e801c0c50b40e1510130840c0c0c2840c0c2c040b9500b03003100d5031509442c444c0c0d48181e800740c1c0300c512401a2a510840021498070001c0c20301156038401340d5045820030100304810000720040d22001c00598 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 391315800 1250 391314550 391314601
    0xc0312011211060a11070f140108010f260f06011412061f051c030f050406020309012307030903290708151507120809120304050114041b0e 61
    0x400d41c911017103524031030088075034969104081000c150724144400810450704481c28940ea03030002032004407807100017849606a4070500100900402c00160f0704500d540b842c41481444101021014501d070402d540340740d080c1c540115005000911840507900003030b000a0301d40c0c0400101d141d10709682e0340401840615034455070000e144150904902c000001c0200500b00b5807005010f20004007070b65034000007140407440660381c03010054003502c103071011103000e0b2f0051401c08034a4001550303001046050034401001040c0e048081e001c41c1d01c0940082c9010743c1e5001029070840c41c26210a0040061105200c1c00ca201d0685503092401c00e0240d1101c100d19080302943c489500031005012020207032070f480b420a543c05040172484801402003640120100e20f11000607040654900f24280c50b0191250042246003401100b10307001950840d1003140005000ca5860104091820081c1c0301101d01034041d01c1c1d980d041c602580100302c080e10191000c103c0d00d051804a1030502c21b6502d6051840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 391317050 1250 391315800 391315807
    0x110106230402070206030c1801090e040f0213050712060902030c0a140712030b100804050c10090e010b040806091605040b0301021207051314130506060f0c031201121106 74
    0x1591070399019030f54000e50203864a82c0700c0c200b0f01319980980e0801c0f081c0c40c5007000d905052040561055124008841c0c03119a800324a031500e455030120300d00c3c051420303a0007098021201ca00004913120304e6120f040b042e9641c052010a98080c1c074291820341e446100440e0050080c4080c244001088a80c003148509060994180421074070443d0300500b4005002a05100c0150300c040c0d0b0507400180d28084101c075426800903078004151821001568094829800740080c3c0c2c003607040552200d03a070040035080c061040c503a0b4075624181054243c01049440401007010070060501f0400c2c50f400a04002c0230f00a030003420385807450710303600e2031144c94800c80c1c890307690b116651000e6040301d610034114038241000d440c8c00b000290141d4440c04420501e0501584000365080a41f101540f8032034004040701d220f0a080760542c0082c001c05040309500080402080301005050030040c44040150300113141c0f6105007880e08000503d0580c00640da007102040c0e5540001d80b8059040ea02a0040741c02c2a02c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 391318300 1250 391317050 391317119
    0x50307051807030e07030c060806040e0604030906050c0a0c172109210607080411030120130b03070c060f090206090904030201110c030723030301120f02040f020a110106 74
    0x80c080c171a031b02c050000c804c0500c01292441d03000d07005034802c1c5400e0310103129000e0718400196031500d00302ea0190000315480010b0106a2060004024030443d500c12242c0e03210441d1106c181e5041d00f540483d540c001c004d070800d801030505100039000280e801004005e8243e900301101e11034070079200228400e002000400690f4202c0070000080f800d40070085800360b20b843c142c0600700560640d0300351844001181e84c1c25461605014004082481ca40a20b03800400600110b0181d0810300c281d240c5c240240300045640c5040f8000366100780c0c159a60300390824000e003007240c221200b00308001402403c2000c0140580c44603c101ea08401060300c4000040c3e660b070604a0061840c9940104220710000302c1521000c0c000021f080c210703026108060780081584001c03d00154050311241d000d400500040000019002c1ea01d2000c0e0701403541061290110b60008080302c41c0415110398079913000c1014803000f03a0145e4080c1c010b164901c0200030b02c50410200802808090300000080940301c5480407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 391319550 1250 391318300 391318303
    0xc17030712020a030e010b0306060a06230a050a0306060f0504051e0405090a0201020111130b030405011416030510081b011e0801031509020d11030f070f050307051807030e 75
    0xd4401d0000c120031516080041401800740c041c0340c0c0100c0d4030750708120750b0310114540481c0c600d02071b05c0000c02c49500319103000741c2641c5600d03000c01c40450505941c201010302ca00703008020b00e030805242c0d5550b03030b417940d1540d4050112a0303540c005100b00300b0400b4035003442d55003080450302514000c945000a0702d951400d011000740e400d050898116040c20180465405c0001d1410581c1d4404d0b00240b20009e00c068a404a60052114142400c819160b041201000c80c400840e00540600c002007141400404031807241c030300c00da6185540030b040c03014400d170055041c030941d03410880020a000c0075601c0d050710b60b507803040a10301d98400720003031410585483c0e006a040d000b1114190642c0700f1042c0f00d41c40090082c0341d00744004d45085002d4400038084140784d208503034100d94010040c0c18001d846803200307464044804031454240c0719001401030322031030401c40c2d90000e0400820000c03000c0e007030105241c1014490303800349000d0084003c1c4000250940c80180340d00070f48521340040c0c0381c5040c82409 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 391320800 1250 391319550 391319567
    0x9010c060b151902060c0714030c0a0c05040b040e0c091302030a06090b0603070f030f06060302092809030c060c0203070f030e0103112503050910020c100c170307 71
    0x30703039001801d0340c04024400b0320300340580b08040c4588600c0414031044201030780c842400700c4242c0f0881108004010015440c1d08400da00c0b85000c1e0704403420304e2200c0403030030b01d00390540b0819500405c030104108070602c2c1c98081c4148040082d24140117032006445840d580361105555103104a200400044036100c0d140e5070110700c0e603001000c884024580e806c03c0c60044c00703030090542e0b0049004000440c41d00703000404100703c07203140e040445540e145803180040b80141040071151503403074010010140e65202540740c010604d80440e0b001c40317441a045004000746030005d14074280d00b049a90004240c2244804020541052001c142003c02e01401c82c210311903204c2c014184042d40004030181513001c20880301741502038a08000c211002c2c44803810500601460006800c40d20001d1142c0c2c000644040d210340703100303041041c1405583c0740025100001d5250440059102e040c18510500c0c001d080301240c4030072400c01505034032064032010f51980d08a03c0700442e100c0000301141c4401c1c440c0544 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 391322050 1250 391320800 391320821
    0x5030a050729042a0b030405060f06010203030109090305090603070f02010f0b012a020303071407061809020904090c1e170303130510090b0f0f190e0f2401170309010c06 74
    0x754002c070380c0c45c0d00142c207a50700250780580c0d891040382c00040200038012030250141d68144c00075030443e0b1074074440e40007414184804404012080c0409040368450300080c2d8060341194448c008116002d10000b400c5400d03110144515908108480801da40c1249099040e61201c0001c50b46410003002590456039898400940521001662000340480c403ca4426611810001c0c0c0e0f88465603840f045802c8100c1c20405012402500c0082060310b800d40d0080c52120009000030900340000c1c0c403a100000c125030b015400040401200c3c001301040e5098000203444083c10401c00f002c16548034903540c3c00001d20075542085444035680c1403140400034600718000c2c1180034044a4010302d03005c20a10401d682d076881000504020030390b0440e012440b14490f1031480c400d44800c0020081110103001206a280e01d00e000b00482c000340c0e12400d001003c0c80701003229510700059140880c1d40395411050340450880711800041c070018140210403a403040702c007482c100d140614a8101a002000ca0303184 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 391323300 1250 391322050 391322123
    0x703090e040305030f0705040305100222080d02010b09010f0621020c030a030b0907080604050c0d0504140c01020f030306042007050d0807020304031a070c05030a05072904 75
    0x1088109070f8008015403090140d10603140041c1c46001c000d89040c012800004d106800815030421221140d070f01421100121070b1000d6102081d07d01060b46028a0750482c51064100076809880150240142040b07001c0965031520741d9803402e00d00042c0d420090241c1020826191352611a107080001840c81c84202e1768011943d48103d840021b507682d12003071a41d00480d0800700c00345441e1500d01c4040344038401d5600d40c21000e5a40000f000300508005040b181d01c0c0d0300601c5111a411040d00c10284120310800025804901200c85a4034004071490054110f6000145000c00c2540100589404c008103a60204a01c6030780c8406040d09100541d150003540b501040580a000002400c1d02d10404261100f00194582402c200e890384242c2c0400340900f8110042045034240354030506e5404819441d28000d4220345541f26030659000d98806070009001180c10001c2c40868000b50310402c82405140304c0e1440310110000c21138100074406050300082102ca11121030000b000005002c04529 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 391324550 1250 391323300 391323329
    0x70b0c0f031005010e01050f07260d09170301121e120309201012150617010905070f0c0204091209030b0c0306031e030705190b1b0d02070309 62
    0x5a101c080742d120b00c030b401d0010700c1c980c0d2540070a5004104642d03010701d5030007146240486903152143e0031581e441e401c60101180030651070340c0c01a500040c5c400000d0300c40c8081040c08407030608000f12441000c9202c2c02d868200010009030741d414200b4803000c0c0d80010984040a8401803841c0a0586c503600030f450340c0883c445101a160303149e401080700903c07401c00711401f040c11201d090401d0001c801120781058800180740c41203030240a40002e5481c0024020418082c1622a88080c80c3c440d4405000300c1c0c520700108002803001d074241800740c01c070800c0800045c540042c0003480c64002415071030a103e901800718040d074449400120851743c20ac0c03144851410304100c020f001c10300c2071200303696012000011500d03151014040b24060080207004002600910100c080d801110408040143c401002002e00285040c40740c040c04c601c2110504091100714280b4551180000340a03005601c03501c04580001c03400081500d08643c00c2c1c81c4011327107550310f07807030281c51408164110402c2c000c0101c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 391325800 1250 391324550 391324561
    0x31902190e160f0806060406050f09040e0105060a06080412030522050609010609110a080601090806010602030304061b1e17012c04110105160816030807020a0206070b0c0f03 76
    0x51802c042d01001070382e904940808185400c0303822010944a090303000070108000c102e000d2181e805000d00e40200300801e0306c3c21000c0740000f411140c40082442c51070b51901d0130440390b07252004210b40180554180400702f4500784d42c03000e8041901c0c910010a146c2d441c8040f80b0b1002c91060011000c0e05c0d44c445440790000c65007001562813104031140381c1c0729802d141000c20109918090400d5512503c210f6900708041c50304c060700c1020703006003014100010410001025076080019074001c01664002d907580e400e0a003040000d48251200c5120061124843c000d003269020100030b882c0c9800345d100081d00c81c00c510048902c003032042074900c405c1120b000045503900c045203042c2c4a102c0010154080084c2c0707200e960030101821078014140300860382c04e024140d4015402031001e02c0c6462658801780c0c1c0d85603200d00c1e540d0400c029403c500301c2110392000415401910319500065103000400343c40c041a8001100e80c0b003241c1000b001c04a110022468803408401550f00c0c0d0380107400c1c8640c603440d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 391327050 1250 391325800 391325821
    0x10b0d11030a0b03010b011803121407060c08060a05130b011808060f060406180213123903030e0f0d1202010c030b10110a0b0c0c0c031902190e 63
    0x700343c80c4d100394601038505007150f000d8a580345132034410140c0180507d156484540380460300c1c100038800d000070709101c1d05044c1680401410001d01c02c07000083c41c24146180101050700080c10680500c1081409000030355807a50002c502a8500e00301041c055a5076004031501c3c83c602a83c120704100c0e401010620380c40c003140f0f07244180e0500d42c490803240d03242c0c01044243c450758170548000e80f900d440039119601c901d030014006019200c40c03100d20641d03a90100508010400c000b5680350201c41c13080c0c040c28101140004800300500d482300c4881464100001302e002031880010305006480f5880c1c0265156070340303051440d00c40100039001d101c0d800d00741a0084d00c0c00041c4040103518140031080394030301a1007041846940500315003481442c001054a103108080d4000c00c2034400c092040c070018014044987c80b80000240c2c407030f141c0349260b0703001d031900b843c6c883c106100c0e40208060201e01d81c20440c90b201841e030112010003c0141c03010182c03c038080640c00540c0c01d031041c0010400880302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 391328300 1250 391327050 391327061
    0x190b0412021509060a080403110601180509010c020309060a180b03071404030302060412020f0d020106140307030f0b190513021f0c060213050a0909060e060c03010b0d11030a 76
    0x80c1c84110060300e080d45070b05100e1181d0070000741e00c918180240200c4078461121a80c0c4240f2906001d000c104503000c043d89004400d030b1000c000985400b9602181848501805401541e1100240042c01801001039264040c075480700740180710100d8052035007442812583e540301c0b269203400004640341e180c9600c166004403141d80228950324107031110b20f4114803c8508898060380903003540e89495960074030700a02880b54400710b00c144040082000014040d404e00c016480d0000102140fa01289803d0a8248509a0306c80e40012004101142030241030302e090590200700300000343d0b101c040c0b00c040c44003611365681c1c1c1240f0305070400180c4152008004076450003191401d81a6000d203466142d40265120440006000110110700140c070f10340107040081c20521213240001d4440307010038501d40c0590310401d6415255001581072180034414200c61021038000342030340e454558a58502e41c8010302c500321101070001024842d40e40e00b40d200c200000b011036007a503528242650100081e04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 391329550 1250 391328300 391328303
    0x16080c0604121409220e010b030d09210501090c060e0a140f0405040c1a120901050603071403100603060e0601050604061706190b0414040605010509190b0412 69
    0x40d5610301c00314034a40070350b0a00d40c0100e8900d14491809001205104c03407030501da66107a000c04298011088200400e0061b0446404800000038021030308408040c03524412601c501d041c042d03100400d114040080f4168070900014220500c400680c8d45000c6005028002d00a01154050900840c4071680007241030072081c0b00300c416450454480f000020f000307104500d440d52100302c10040c01c030340382041d80000b42e000d070182010300e181d140da0f06034640c240f0102183c2c0303004440300000c4a43c06400102c1e49250441c00780d0000b08020b00e03001000ca5901c0c4014000c2016114485030b4100507503504100c2444075198203030091081550760b14020016203151405058240188400801c0c0390410006940442e1250744d0782c000030300000d1800c0d01c103080002c0c0c107090304903007007207011004500c980402000500f007580009a58524202500fa8500300c5402480d1081e808c0940400003a0f900032300f074032000042147e5528041c2a0901240e9041005502a01c0d0841003c580021075841140309c40c413415 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 391330800 1250 391329550 391329563
    0xc0306190507050a0c060b01111603150b0d0209091c050301060e121e0a0506041b0e040f0305180d081309020f070f15090c0312050c100216080c0604 65
    0x2c1d1203012058802e40591071201000a02172a8210049070359500500d1909a042c108141c1340300e80c00c1c080354101019040da111060510101c10000c1000199880c0c1e003004a00400b0080400240001039401c541d9281c003074410031030040401c1405c0810300009100d00c000b9184c9000350755508a01070020f402c00d120308400300e401c07441b425565040400e050381c00d2003540f81c09040c0c2c0000c58034201c0d900b0105413000c0701d800e201d00354078400050004c1101034091806001c4100070308104800e44040d2403a0b581101c0d07c0704100205020009501e840c0000d10306605003003030768650000452881e40c80b031a1101c407030b520a82100d01c400c10710903070500801003889001d040c16881e644801101040e442001030400200d001040f180000c10b0700224100c0c0414464880c01c842d0340000003009041d250166019070381340345504000c200300036200d914150340306140c0c1040d90070500d4189101d5222079004040b441f181da000030742208400d00040004036274581c044c1d10703240c94840d555026a52420b0489084402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 391332050 1250 391330800 391330811
    0x61b0703140f0c010809070302091e0c210735070302090a090e030705031b0114040b06092d04052503080703050d0906092001020318030c030619 63
    0x1040041140c0e611030400400603d403441d00f042c01110710403001090407825000c0c4003004801030350303072000742401611b00c40c00b036054144100911184456018090b400600c50410050a44c0c070502400c06031310340304241e0034a400e0798620900351071000c05c28501d420784440d03c4481a075105114060010714800d00d07924450940c2c2c80480c140d04074411095410f07406400d00303a042000f450160020444030310f001055a0a00c4456500c0d0f521310380003030345106403d50048021801240091103005800701e5140002d48041c20191560320500758041c043e40c0c080e00c040e02c0000c50841d2106d28030400001c08205064025491600540b1404001d65044440e40246403500703060703801c081c023075a2901248500c10014a491650741800c0c681c02010101e043c441e0031301030580750150521580301a580900d00110345042e661070305448014880301c2000707040d00f0100c1c0d04c0d401c2c0e9a00000f40c6045517551102d0b10010217488002078680020001e884d541031040c2d40404c40340c040b100180b200c0300301d03000209001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 391333300 1250 391332050 391332083
    0xf05070c0e010b0d05090d02121303122102120a05060301091e03021e07050904050c100302070203010f050f061e030303070201020406180e071209170c0d110604080306061b0703 77
    0x1c4980e0000600c1d001a42700743d5074102d24582d41d00042c0b00c80d9441c10100b03000680d9030740d2016840c1c1721210181c03010522031a130200304820300a03060300c40383e21510003c40c58180000740c005154131028040c038003007954900001e0300c0e070340f425400810013642184400700c0b0311409c82d0016140401c00c0c181100140640381980c501c0078000c0042c12407407000d002c041c1120a0505081c00000c00d4028000d803124801c0201d50907440e190a0050300501c0798550f00035035110b0340d50040c5404c0d281d090610081061811003049070a55981c4005a044403044822450200c4110304000c0029103201006d40d141c04004140500e4503015030040c81150704644503404280c1080f440780369174410034403400442c4640c2d00c000500081c4642c128035602d186403100010780700742c217440d020700241e00d81d1514064940000390246819400300003250300000c092903c2c076516080c0a144a48501002c2c0008010392000b0000c92030541d184019070380001c9400c20403c181c0c2c02074081c8d083d50355120b0b00c400d955052004241a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 391334550 1250 391333300 391333303
    0x50111090a0b0f1e160c061d13020d0204090501090501090507090b0a050a090e0702010e07080a02030c151b01060905220b0712060b0d18030f05070c0e010b0d0509 71
    0x543c4541210449810b01020410001c01a07200c01c5010000b12400c0020101420120703010600703660040042d0f1041e14140280a488400000f2088020700c0c0078004030201e560741d076060a00211100000541c03503101c501d04210103400f27160000300d05030b400c140021600c640241d0140d4104e5600060521035500c40708002c1e500034805006000e000e050800c582c05001d0301450091080400900c0c00c44950f542d40e02c1c0021005c1070a98801e00107075169503034590400d9040003088081c3c3740304005005018407a40c0001c0e030310380846807101c1c0621070301d41c00045803460401c2501c22504558070045401d0320240f4081b40240300c5401656081490480481c008507072014110707804e000301030300324001c1407201c1d162141d10780c000610b04002c0061400301c40040c20558000d1074014003900c42615181e83d2103400080a946088a61030004084020f4802c0865403044a03400340781c0c210b0811075550400d0b4102056080f0003500710006200c005400001c200c01940010000b803036000e582000703151607040c8400d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 391335800 1250 391334550 391334557
    0x10306030302120f090904060209180c2b05070c05150f0c03040c09110d05010b31051f0e1e010e120d0801030201020d08010315090f050111090a0b 64
    0x9030050f4003696021021070314840040c52804042d44455040088010010f41128001c94080768042d8021610500e5400c1c400c058070351008995814400c0c0385081c400c000480d0107410300002450f0b07580d50184200344015080f940c10b58400b072006211034a042000034003c8405403c3c1252030b441521b5070070591118040c800703400fa07007c00401c10040c0c0c071100180041034001800681d5842ca088000168a049502c0307030002c207a00a80d00360b9161254840350030100d81050340601c8441c00104005148000c9810b0018a14001054900c4001a0961501e100b0b004560003103904103031000c00c10825041c411041c0c204145032552549451150b4005004504c51258a14002410f66100000056005402c800c0030f03100c0107040c41240320303041075100b80b40a4030a41c0300d01c045001a0018001e41d6414003884003c40400d081401c84c0317524598400c1c40c60b0021f043c800c0c0c4a20350b600080400c00800504181d503258011000344444200074819a038168407500846209612032030700004d10080e210144c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 391337050 1250 391335800 391335803
    0x20307050304110f040f0501080c0d08030c130b071a060f010207050111010221011d0709091109030f0c091e0606130b0a020105060427030e0a09180203010b01030603 72
    0x34941151220b680700070b25040d1900340390b5840300e030701061402c01d0b40301c6101d2240e140c0c803c5240456070b5403521410324140b0700c1088401d40580b10850541c0b010888241c00c40f6007006021648a80e95403101174481d8480d101d5400c10a41c1000008023407061111000228180c1c1c0c0034100c2e054890345840c010029034030f460039603040c09600040c404001075805520310030310584074980090310340941340388001c84402e05405d0300444031030fa01005010550b1418a040c5669501524044540c102140c0107000c0d402c4c03910400140b242c07907004a45c19004050155000701c1e0001e021140c20000b0641425105c1700789014990041c0702c0b10001841103d09403c00d03c030154214400070000d9100d0105004941d4050039820824100c10710000442c640103100a01000c2c015070300004040c1004420401070700c10100e03a507600c0d200d07260200c03c1401d4115105803e500d9042c188900100c007007002080910649030f0008010798500100c4507845c1018801412002d4400c4000300720140754000190b003112200d010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 391338300 1250 391337050 391337057
    0x501030b0f0d03020c040c0c0507061b0f0206070b07020d1103030c07140c15042102060406121e0c0207080d020c060706020702041e0b040c0e190909080306010909020307 74
    0x2a088000c0c02e1150721291890b01030710584000010084c042002d80c0d944400c0c0310000b603401840300040c4507042c0310401c060900391401450030000703400305035000c424040303000e000c110017400c0b074000315035564040340c80107940405008030750700c2e0100000c1d40310340e030601600303010540749400411104c0c8003004503449070600034901070a1400e01c1d02e5051458400a003000e8041c8071b1092a8001a42d4039810400004080801a99900c1c14202442d40312a007803500c0f00b04a00815102000503a200b60660b01500c0891500c1c03007100417a00f078405c000d06064500705240c09800305010300c0400441d08500c4800010b078085840c030700e40d518070150365141700314030703050041c2c2003114506010324044000b000d58038082c4002506040703140d00020200d032510010070800c0000e2240d4803504441d0360290f80a01d81080750100318840c601d81010380f400702140b65461141240c0c0300211440e2208408000140c10720040030072481f4064035010300701e6442550243d01140391980d0004402c480740c002c6900c035202a55 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 391339550 1250 391338300 391338319
    0x2040e070e0328020307030b1902070302030d0b0117090102030a0c0c020a26070f0f0524031305060a0203070e060a1b0c031407140301020c0604170c0a06020c01060501030b 75
    0xc0425224070f10000c02c1c41d00d00f1481c0d940200c0560f90411a03100514000c00041e81142000034a415400146500c0c9103050750050083d280071070f40120a50b41200404035000c00c01c032030b801004941144001081d515802c1ba4070301400416030055010754401d107145c0308100203d14001c0c1050311500a02d620080d03014441075410b1106200e00d043c03440252101c0540c070100701d0215990030307044c03e00715001401c1400a00c0310030000b600111134034000828040d99810009020034103c81c03904266090541c801c403a0000c08160714800500341da05001e0f400c2000e958850500041140c0a0350096490100040600c07401d040715140040031616005050346520700c2a080048c3d10740070f01c0f0400013081d246803142d0100000858000564685030b0401a4042d020b514200081c03186a1500c01040c280240c0c4140001c0906810010311980c00070f4100b13810842c80070440d1100c8190303200b19659841140a8905103404014040d006401c0185101c4000d0000a0f100c0700110100c2e401c50322029804030801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 391340800 1250 391339550 391339573
    0x20a0e0a0b0f030c090319030203120c04060519020f07060e1810090e01020f042d0b0a030b040e121803010513030c06090c0b0c01150b040512010b090a02040e070e03 72
    0x2103009200420004d026220074080b080603810b00030103160815009600002284492105408980c0c0d03807114a540d11281401d080001c010500d000d25500074100480304240745434014004c120b400801e11a000407a5550342d101c8070300500d0100902c41680c0200e13580da600b410255480b1070550311038039160340c83c0ba03000c9240540c2600989011070750220a958201304440b03031901d8020042015054205461403010b001c24842e01d030480e02c06c0320201031000e17a030400748200003100e0200c424030005841c002c54402c000d8400580280700343e001040e664850075803e04940794030900a040400510b80d05c02d0f401070688000e05083e20011500788402099103e91308000074041c0c100c500300f072801414001182481c03a65050004607140e040940c50807804900032144070424060b66000480645400030840e16124910441c0d004074000c0c58840c1d040704401c0041c812095120889040008141002e6800c01810000c003d60146c0159801187d128002880c000e01601c940f00190501900824030654132 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 391342050 1250 391340800 391340821
    0x2120c091c0807080d06050108250c03020709050424022503030212070809010f0e0607112406040b0d051203180106031b0e0103170a12020a0e0a0b0f03 66
    0x202107084959007000d0211030b010521036400341055036600c2c0ca002841c2d0b410030002401c610401840180b0f04941c000c800c15680176510303100c0d03c02150a06002800c3c171414582a402d2004541100401c10300c1e0004100500c0301400c10b1424810105107209842554003002c282a44201c47c0510302e0364a00e070a080d448000001d034110f207114040d03d00141040400100304036500800c1c0c0c1c1100000f0414801c3c0040f6200c00c1c41006408020740c0000c02491312000e800d1030325100010b0114090180e140c03e80304c81d82c2024450000005002d0b00300c280000c0c00708024045041054400f01d024525028100100d03060565602d00d4950300720004080c641540404d0011560004261901800000440d100c2805090040001030362048031488181c030409040704840240c503512540d101c2c040100100040342000001f441c180000c0444180d440d41c11140035a078076201c0207025241c66100141a0341380607440807403403011110807500e40380c00c84d0380e0b45413501d001d02500080c201d01b80410804a040c1594 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 391343300 1250 391342050 391342099
    0x30f290d080f1303051507031107050613020d02031c020d09081005040c150804290703020d0204030b07020a06140105010e0d02191e060c0b0402041a060d02120c09 71
    0x6a25440006513181d55440303061540742d80307000c04608400414840a5505030040d841c01b81e40102465082100507128943d8441d0003800219810320580104002d5403100d40240c070134290058101c0704680c514400241d41114003281000040c029076102444061056144004560304480200201e103111840c100061201520445003050b83c80d4000a00208005036282c4004241d203c6408515050030320507581c42d50031a03100303100d02a00300b03a0b0ba14840c4000710280c00c60110719005032581e01c000b0300c801c02445290030250100303801d4010000310307580c00036102041602c1841c0074400981d0f00d4105003010842070040c1d0380460011911082c45040030b482c0c800110307000034010039038803170f29400100e00e04010350480c04e524940400b10410b100328948030200200014a890355441405803950030050801900007440785403140c0310f00b050240d0400394015900c5000300900c0c2e175032001c03800c00070081d800100b081d084489010000b9004107540300075a48468030140002907082d81241078442c4280 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 391344550 1250 391343300 391343317
    0x1b041d090a0b22120201020909131703070905130507030b030f0c060f1201060207170609060403141902010b010e0109350604050703020909061009020901030f290d080f 73
    0x180070f0501d103004a42018560f0444c05556000144d58481a60600c031a81d040141455941d01801040f0000111a25128000002c000b41c0198036078440840480b0315540d0390f4000f5910141521030106070b40040e510090041002e602d0421010340340d8824103031030b008041c1c0320030f1305908105010304080c18000c0041080c203891034011446d140010b2411101c070b00c020707082000185e00c0b60405200795250641007800c4100000010884c910788104266589c1000404c01010007094030710b00c58a02c1c2d6a8000c3e206201c05c0c80c40c03081c940206004009000303040c6000031034009090b0403242181540903082000030744000d2410400d0040707072601c0d91110560800d5450100e0121004e10000c070034000e0292a01541c8224003424019103140100807192201502d602100d400005c10f0100717926946403010200c501e500e20160301d80c090380300103a0080043d034014101e02030601141000403545d95054004c03030f0032403403464440c900c0c0002c144425494a0744008110746403c00504980041c03030400f404146 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 391345800 1250 391344550 391344601
    0x1050a020f06010f081207050601060c030c05010e15010b040308031305030c120405031212180313090b0301050a0507050a050315210f030310030303051b041d090a0b 72
    0x200c0c01c0020251500909a211441e18101c905041c440102d0030b000703c0b4044c0c440046070790304100140e00c8032034a41c08107114203030610090000600805005e4100c11406503040030003007049031100460540c0718900015080008464072001080c100c10080a440c141c2c0c1d0031240890841c1e0b00c415216584c81920842a030b560b05c814050390310203081c20000f10b00240768204603291580e1801c424507203460301a0064401c0b0b02070902140e10300e00d0308c4e4403c8035400419810040c1200481a203d40c0c154480c3d082ca25100310b008440110703e1240300e400191104505600130000d80ea140d0950b42e08444d001c4c2c4000c00003500c1041013045441c410005550014103143e0a4190388010a0000380ca0303d006641c3c02039034141841d100482d5040601ca081c2040065001462461030f1241c1d040301410b14a000060500d9601d8004c180720081c100036030314103e545c08903680e80c1d9981700c2452801c0000b594000c40c05100240707001403003038007002c01c0c920710b5a50b214459040b6501c0d480c1c11a81000c2090ba00603c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 391347050 1250 391345800 391345813
    0x708071e0e13021b01291c12030c021204030b060121092a0302010516081c0213090213050d0618080307030e0a0b040303020901122904090507030201050a02 68
    0x8034405880100000c01414000b040000f10300c1000354251101403c0c100114080340042d00702c42e0320965070b440c000340400c48000d1211f203110f51042e08600c0907540081c10200041400703403111900f650003d0040b0714070b9021602d000c2e105000c0d028a40c8114040144881814400f00305694041d088150f03984000500f00c9240f202460a540101d80300e003081910a14503680f10410010440a80841c000303d0002698400710309640001c1c080344201e005130460105020210030510410400740c41d481401c402844020292108502d0060342080725101c0c1c01104042c00004d0503502e130701c220340d450040c1e1524000007d03d0601080300841180f00300303a031501d44521800d40300c0301c2960254441c69109994107912030030046d1008040702c4920511030881c5c3d00ca0748070a004200c0d9668100e0b440b96061a0150b500c1c45d50301d0048074884010840703964058240608141c0c0400700100710f111068000070303800d1001016070200804c1c2c2c0c0702800084c203103812100c001d001552180c4014010180c203401203234103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 391348300 1250 391347050 391347079
    0x50c091207150305041703060a03021c020a0e01030308010f0e0604090305071506090b0111120c0c0901060c051b0d0b4303090b15010c060c0201050708071e0e 69
    0x44114050702d62030000795490042004000180c00890308102400890a007103240c18004178011802501001c1e105401d103c1010141040e003400d40031109501904c101c0d55169900321002c02d08000f0300080300829545800401c990715144995012104243d045030300603114036088c00300500801d001502000020030200c0041906445044801f410350b001c002143c0b450102e2601c1103500c0614140c2c1000f00c2d0b641e1801c010800056140039451510104c0c13640c99100310394080c0350207450f007481500000c41900004105410040450070742d4020826156208955800c0c10b07150796048100fa42d03c81d140d20b0104020035200008140c0c080c8110304000f00701405502a44004024403c021000030320420a040030321a000c9a1b51040708043e013418803e00b8100d0741c58640b8a0001001d508205549012100d403603803241d120429602d070415401c00c80003e1010000f806030204507045804500f41d0f401180307943e446040c50400c08015080c880c0e00c1d80100d404111034483c002216141d0010f888001e411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 391349550 1250 391348300 391348319
    0x20409080c0604060c05040503030406200106081006090603032708120a02010f06141017070c1202060c041a090604090b100305040804050d210905010909050c091207 72
    0x204205100241081c3c542482d180c02616503455902007004400c1c8401c2100d0380703000042e101982d01d42d0138604000180c5407044a0054a8154151890f60a005000500150119200400280e141010f100050312901100d080d41d42c0b40c80002c000a45602580069401202407400c1185c2c8400c4030501e071360340c5d030260341e45005070011070f8019000300003400707d80325602485004000d880c004011301031280b40c1040c1c2c0c03a6080c0300c0c2d0a103074018001071249002803881101c401251800c0b045910046017068600240750034511001181c00301203900301c0c03168080c0001440c61081801003400e03440d143c10b00b04405111015000d0881058405104103402d80e91b5000103400580103d845c0010148104001c000255944103440340074589000103000214002408035802d5520564100ca4007a03450300d05000c0701e8204c40a04100030b8803124050b500b050f03208100000310382c42640d40c0ba25264454a021084907c255501c82104904005000043c1040401c4408802090b01a60b0169a0301d03200d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 391350800 1250 391349550 391349557
    0xf090d061a0102160509040f020105040b030403210b210c06071202070b130303180518090c1531060906090b07081c061208040503010c11120702040908 66
    0x14801d000d1554500400d95038104811440d14140c512616580352401002c9000c044010b4000b030080d120000081c0c082d64019411140280300d2641015500d250904005048160824413401040700f00c110508844c1458041c00501c444014041149900d60200c00c4460302d2140d005000640074007034140d01c01d642d07450090210540541c2212201080713048001b400d01a482c6c008104c070f00310906c1140445980c2d8501c00042d84c5d0700d41400c405110183c051609502619031103240c0c412007070904102c88000300015140560010340444804d06505801c100040d01c03000704002e11444113003c03803a101c0400803040441001c615004068004d40e0300a11803801505801900104e60701e1982048010781c4421b11000601c80c41c4c0801c1e041074242d07550700c10903110b1100da030510340c9039144040c914060550700000c010944101c14980e035810038500390311107401c2840350601c80d502c0c11250030301041c041c000c40380d80c001001003d070107081c000400424564008800580c0c0041d61175071031000043e4100c008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 391352050 1250 391350800 391350821
    0xc030f15060f0c0115080a060e21090901050901120b040819090e0606190302030a0f1d0c090405030403020607140d0c1e080a030f020702040f0203100b09060f090d06 72
    0xb903660b15a9809412400c1d136000c2044000203140402e41004607500119800181ca540b0a1021864880300740345203181c410350280b01c0d0410075401e143c1d188086151401000c258009a605441e04d87e40d0340c0c2008000e600901c15a5882100429528009215242e401e94442c4c845d10b80282000c0c003104042d202000c1f10040d01c1d0108e13a000754180319140601f00e002e80e01010442e4007601e45400040c003200702d1000d1038694024540c003c404a04a07580d2a0480d0078054030980c000c2007003034502c01601d00d4010b06980901030328022104180359508010b10080c3c420740c0c220006500c4c10b0314660a0104a03071210700140d030215500d0540a103800810b02000b0000d0350f00d175840c45d01403c038a00386a401e0046050201c2007030003124004100188804003582c100340401d040020b120309090344210082e229081000703500901c5c20500307003a946d50319405103000b01d00e98880a113400d5100d042190403441000b0718942c4c42041400000b0140a80c94002d2940d0600582884210101036644900f40c4581461 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 391353300 1250 391352050 391352077
    0xd020408031620031b0f130f0b03030301150f0203040f0803070308010b070c03060e1e010c080705070c0311010309062d061a0c031c0c020c04050c030f1506 68
    0x56140034060107000c809000603c1c624403500b007007148000a0343d10b100501c01c07964400c403d1307021810b496581283e04129a000034000502e818400c00190004010282c55079100614240d006411418000300392410f0b5011000881280f0781d81035419252030b41104c2400e4210b1104000104450004c0501c2c0c1c4024002e0304010342e2600034610300030341440c405801001d07038100301b80a041d004c0744108120b0001c03030742c110000107110403103010f8080c10302680c00400000d01221380c0c2d43c4548014154041c0c0426207150756444401d49030701c83c1c1248c0707d100d0030401130240724001074140085543c040707048105030014100000c5c0e44100c0c2d55224152a0f0f072140e038000d1081e103440d1401495140640120021902e150104411303400c3c8014200c24242c2484084808035010600814214080044620020321400c0210000644801900207401c00402c1c000041c0034110700700c1d030700f070816000d502e00501c12086514215992140840100e1070018000c0d03c204a81d91011145038681034020012403000f43e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 391354550 1250 391353300 391353337
    0x803040c230102010f1a04050601030612030801051c030207030b0c0706110d050a060f2702070b39090f041814060601090302102706020d0f020c060d02040803 69
    0x7001900b11a1301e052826503031820300c0001c13403084102110541d8802c60880d400030780da40f02c81c00100c000300b00b140c001800b11405d20f00c035101031540100035181211000c460344501d440304c0b1a20548081c1c1d803014005c01581c002c0c0e10038800600714550580e8040c0414040a0a003007690b21181c041e075010081e4046003800000d5003040c00103003801066440942d120050110310701d008810003c8000380d00ca89600800f04074040030000030503141070003c4050304c400564072040d590400721503407981134410700c480401d500201c50745048140710091801000346191404e24440a482c0d080075840030036129440001d2031401c19140c4c1d598810101c514546a811182e586101d02c0d05501040300009070118550050080103403e030b9010306ca0905603581518a0b0ba500f01c0c5890054400c4039400083d80c0e06100c0480610502d94007840010044451b01d0b400c44d4250000b0302030680785003040c0d03100c140040c1c006200b032000c1820900020102100b80500040c60240d6550160b41140c101074480a003150145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 391355800 1250 391354550 391354619
    0x10050a031e051e101202030102090603041a070309020a1505090d12030c020a0f080f0708040605071a1005090619090b01090b03150f0d0510091209080a0803040c 70
    0x4982040341d49143c01c66001400c140113021341a040790301c0344009006100c5032140446d1020b406032103512101410700c644a042074508100f81401c903540c0410001d804100040d8618030070300900c1c50300c030b4014080302460360401c0307450800e0207410200b0b071050040802100455440720180000b44034013940390010311074045032004058450b03a91000741154008000070f804034502e03402c4010710707a0b0711491f51030b900c400ca001d0b101018001d000b00a0030b00d000210780014002e800c20300900c1810f1080648048000c9103210b10300c0f00c0e0800fa11000e07481d200c0c480e018400c504201140c03e0b04000f009090841c9040246030041c3c3d07840182c1c2062000e00e0301c60368074040303030350308080d1920140c13551211690541c80c000c0383c100c40c200380807034030a8441c07110146648010b442d09080000e4851f000415a40c00701348048a81c405050318100880d50200c01142c10460b10f440342c0401d5084e180190301810b046c40f2252a44800b503000a0800d48084c40111000610143c00300c210741560b44008425050000301ea = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 391357050 1250 391355800 391355821
    0x15030c0e063c01020d080f070c02030a0b0f0a061d0a020904022706030405100c0c0b0a091a06060405010c0c0e07020d020607140304031209021302070c1410050a031e05 73
    0x200b00c5228190760003200310503449604032068607446156135070741c0300303059441c0801162811000c01e0040d4060040d0b484217018000c04072203c5102c1d2003119207520141d00c1d82c1401c0e1040300c000b4401c00305021945441c1c0b04410000030341a0703400056002026041040420000702245e10412040d64603958680ea003c1868000d280e030416010012246241149443d880e901e44444068035030400140c0c2e030322a4449140c6c01070102001d91a080307035407190903240510b02c00f03009190202d800e803156880303040756000c80740c111040340303108100140c4514100391074107005540c0c101010700100d4000c0480040499121648403c56205070362a81c010b02043d021680301034180600075000504014a000c08040071485540843e900250705190131048103140c1a0010000d00e00780d040254000004461464071840fa5005440041d019140104130700740d03600c0303c10310030b005041c00054012030b003640c941905074012409010402002e007404114200b260300c40c0690701d201b41c1038000a441d9034000b8420300005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 391358300 1250 391357050 391357159
    0x1a0f1602280e06030607020c310506010305061005180a08010504030509012c010c14100501090f05100603020f0c01020f1903050402011403091203090a020415030c0e06 73
    0x50a80103048a8100b00b000207440f45084d480c0c45000e481e0403060203038110042d8004100440c0800c48510309a89e1134079460000d04010394009002a09004c0402c1d5079250440c400e0b5115007180e11250303e041c500307030300d403110303c0407014881030f4000b080a030001345002080c0100303803060784a40d0341c1c980d07107660303800c000350843c9007150412424400303940882141c01010380001542a0307003424510a04500d42c0b0b40842e840405140d201142d01490055450040c000d40195050381c800540c144119039540000c001164401c5030342400349190710504000c0c00b4069801020383c50300c10000700d0700e04038161843c50b0a9070700c80c001c80d055221f0001460214011005170248450200785000d03ca5420701e500000c001e00c03180085000460301c0000031488580c4104416156642081c0240303071245412010b8980b14520f001003a402582070032607008140744001420010f40e988001411600c2c1d003071500007420b00b03400510403a04004506003801e0b03103484854901601819034a40c25008a41c10801d50b02d1001e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 391359550 1250 391358300 391358311
    0x5030105100807030b0a020f1b060610050405060906040506070309090b0904032c0a061e09080a1104110d0506310504170c06011a0f1602280e 62
    0x3003001818480b4400220324801104d07040054140203840b1592184024802c4144e10b9140c5500000e11904070309041c1c44200d8614440420f581d925500d181c00d004884101030301160008000700014445490a03001600315130b54042d290ba801c0030303207680114403182d20003242600458000c01080116502c240100703006464161081c802508050394080d11840303910500300c000700001141c4500d2062107649180e00114024120324503a07507035240240a118920800014030b13070b50040f0008000340a04404000c440e2580010108100783e521860000003115080d107601585a080001f043d00c8000c015008a11002c2000101414840104107212042140000c00d00102c0f80401030651040301100c03940c81d211b10000b064568880c0341c5441c101001c03028402c00544085070000c60327240000f4600d81a91f43c0f0700b010f441c8800c2000c48084040c0140384200c0c0449100b013283d10180c40c076035241c8001407840500b5170100b0114940c100c0204a003003e880e420f0b0610041410041300000c01040c41c0c004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 391360800 1250 391359550 391359571
    0x201180b0301081e0c061c0b03010c03020d180b1611161e0803030a0e031309020a0f09150309050c100f0e01030b0609190b0c060114030303090607110313030c05030105 73
    0x1020030001c61b065025202c82c10300c58400b2007048140540701d940055400d000000d001b00036800c030000029000b90403035000704070702501d44501081c801d240b164100023020380188881440d41e4a41c01e802c16071060510110040007494040c59a40d0b02c001c00c00713a41c0c1c0d08402d8800304001c50400c80a8125a0207018a0f030344000310146081010100200c2200e806c900520000709140d1601c030b120b10318511550000260500205078002440100c9601905040384c9540c0c0e02390140e680340c0001c95240c2c00758040d444a04407000b070f9018602d0302a91100c49810700c01e001741c483c0b0b040300000040c4a03000c8403001e58041112511640001940815840381c080802d0a08000c01c250350f0003c100d050207188695401000d99054031000c2640c601807983c000e2a516050541e204d900d80303400350315101c0130700c504035502581036100c00b594a404000d0700d100c0c40002c1c0040003035503940c040c101d03281400156005d8003400204103810100312080c200710040e5004d001b200a460381750000381800c4510080103088030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 391362050 1250 391360800 391360813
    0x4020f010302130b0c030c070b09151e090406050904030e13020a020703021315030c0815060306072304030b09060601050c031c0617060a06060e06070201180b0301081e 73
    0x4400b400e0341640107603800145113907103450001202c1031075481010000c04051041070f00001e5240c0041c0000c000701034055590340b09403504401003191034002c1c041610411003c0c00b021040785242c2c02c000d0a1080310081010a01d0756030345002c500000300545d816030005d440000211054240030044002d00b00c0c4002d800c51518540d4a4001c0d20361000e408024480c0c20100c18010601c00342e9080300303d400d4242c007080e49400d540c91601e00000c0e0000e1080c10900d014000881d080e510070000110b00c100009009020700c0d40d41c0ca44112091032103519150311960b0001001c0e00004a144081c002440c8500010328241c1400c130b0f038251a01c10700130300c1e45041020411000720515000310a8034444003090390440740d42080340c40070401400c42c50f000006842c264130b501004400b4000350050003a024051b0401102d45c641d07002b200c0d0300919002c1c00c0c3d0800300801804006510030b144103042e0308520703020f5405503502c2d800040440c1e03100f03a01c00609940b03c080a01c0301f40134015054990552030340f000748070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 391363300 1250 391362050 391362067
    0xf02010c0e030a0b090a2a0806060a121a091e010b01020712030e0402030c1908010f1a210105030f16030b06041503120905061303141603030804020f010302 68
    0x1a10304820f50000c00b642c40840c0810340b801d004126910b540e96016003900c0d003a4042480050074000307408210074100c50140c4001800703142c00705030700c0d026481c0980396a01c080d09000080e80b03024482441140d00c0761103003c0c0d80080508440c0c007213008462002c080c0080c545e40302d044020001c00b0144035030069140c40d50058076682c000580c01c04544203d141c2a407201101d04041c1c50303840c4800f40d86a0403900000c104032503c07210714002e060200e040c101d080205004c818042303404030400d004074000384450800900006d070000440c070307220a14901000c3c0c5031680810740c14a40d40c42000a013420b012404006000d149000c0c020b00b004210210300030880414005078030154040c9601c009009205440c02052098680f0b070000d44000c200161442646607681c5016400701260740c50400c0090350b940c401140e01c0c86c1100440c1c00e00070880815080090031500c0d00c4001035644001c1280900c1055528034a00140703034195402113003c0d45030031030ba901d003900510003070f00c1d800d81941b0304051040282c0c10703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 391364550 1250 391363300 391363303
    0xd0905210c0613021c0b0406061512020d06080304090510050d0b0f100b030f01030506070e0d08030915040b01030b060405040506040f03050405060d060f080304150305070302190f02010c0e03 83
    0x56110b00c051040c80740c03611081c001328110126051082076040417000182c818450450004c034041c1d440354404001c480c1d075984841c807079034072070345044400104140c425a09184064001c2d11400741151800901181d9945031340d0b14603409681f00b0580b058070340c070404c070120000c00c40c114010041038400c0058800c060780d03040144107000b040c2141c0461648003041d25500700c1015403001d04180200140d5906000b040e04525080034070045031a40300710310016440510525100703060030b00141205085035801d41d41d03103d840d00700a10005180c40f411b000703140340d0301d403810505d401580220800c0d6442c1d410760500280b5410010040780c015400c04003070100040e000140c481e07015400c44000d003070b00d51940c682111148203d03030009501100100728040c0020469102c50122200e071468611170656400426481c5e00480c4641252003201050050845020b80c01c025031207030507890010700e85000f1451640030a1982210900090540e151490450360244104844503a16080c4030307046061450019 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 391365800 1250 391364550 391364563
    0x1060e1b12071d0a0308130501031a0103110904090807060513080f0c010b130c020601050a0e07080712061205060a060f060e0607120e18010b0f09060d0905210c 70
    0x402c00c102a002401610311038015003014204001040c5601e03581e664140307201540c02045042080c00c0c00d001d00000e1544c002c0c4a0407140c4e29090241040080b8944015030040112401c0310124440402c40c0d0390036540d50b48582c9008601c00d014443c1c65001e1402c10070201d0380020080020f20040c143c01401046410064a4840c0740c8110369a96442e800e6034240d01400200c00082c1c2c1003503820054646140e00c03600441c42014040d0300310741c190780e42d4034108004662588a045010440d400208601c54455140c455215000c3c1c00c1c10300000c0d000c401e0740d80485909500c4102c03100c1c820006070080082c1403140315000411b1190612201d03040c0050828034882600c01e1001740803c081c440c4007182c0320f071800d66008a810800d0201041ca40c000301034541c403118400c49214003180d5280360174401e4602101da0580d41926440c505180b01444c0c19112036100001e4594444001e2141d01d0941140307001d0810518441d0b4040d01e243c1c450034041c1e0031200168a00441c0117030062001103203072500080d18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 391366906 1106 391365800 391365811
    0x41e09140d030209060912190302030414040b1503060a03200a05030d0206150f2707021f020703030b0315010503190f0311030c01060e1b12 61
    0x12400c1340700303005003d9404141400301400c14181042c902140301401c40c12184401182000e00301880e200000840045e400028281f2031045511840b59161300d05940a201640780d02c0d0004003c0068201280d41035000403001400d10350398900c4080086030060104841000040d69179000614803002c1e290107120042c0c400070702c5080014a2078850300c02c65000e0040da80340c6608101109003540300310355201d928002496580e0b660440303003001901098841b20070700070042065020380380004210034299040031040c04110340501000a0310700381c1c08000180d40300301760701e02035008000310150f56815114a02c0a1881003210320505030580e00b04604458204400c08605606014800b1b4000c0107030350326035070f07110000f8050244a070020364060290b03400c040e0310829550071a0010b50051000014001c1840000c403810b8401c0403180f6190503191f4a415140c0c4503241c04c000020b0403 = true := by decide +kernel

theorem cover : BRFrame.Cov 391187050 391366906 := by
  have h0 := BRFrame.cov_init 391187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 391187050 ≤ n) (h2 : n < 391366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
