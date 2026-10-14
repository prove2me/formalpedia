-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3447
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:41:10.870455+00:00
-- url     : https://prove2.me/submissions/679f46d9-cfa8-433c-830c-87743d2b2ba9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 619784172 ≤ n < 619964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 619785422 1250 619784172 619784183
    0xe07090905031b010c11030913110d0e0a031202130b03060a08030a0c0203070f060203090d080d330602030a050d0213030503120901113004030207080c09040503030708090304030f 78
    0xa075035000031765110200c0581c105205c2c0c011814052210001110391421b29070b483c0c4050782e10044e1004903125403080e1480d0800e2404100003121010000303030b84038600e09108600041800d403a004590000784251600710768070780c0076140d6081c02c00310b10700581d610140400e03511480e94100002c0c01c041c200000c2080f81c1607035403100490306661042c0351902c0710942280812400940e82070101c03542c000305a400340d42040714800d601451760b0a0200041c0710342c8419110740c40c00c01e0259860744500541031120105406458600442c1c0d40c50400803d6106005690041e0000c100c1510a1440b88018101d407512000005180036a070385504c044440c2a940103c929070004680d180b2440580f04200b03500061800c024010340002d07070100c0380e16100710b90041140c0110002c81c2482500c1d40400c1113200010358030300505608013800c2c0a5503418061260310f03094481c0260b00351840c284900300601980d4000000c42c00c0d034aa445059170301e00001000300e0304610045c0400400300b942c000d46c0c42a244d0003613 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 619786672 1250 619785422 619785431
    0x30109061d062208040b0a02071a03070f030b2d18010b0304030311070503130f05060a051c09230d030207020d0f03030b0a03080408010509010e07090905031b01 70
    0x70302401407030260303411100365250044030401042c8002d0001264100c10012031107002440706203400b20240c00755410080b041103020038800e02d103030303000102c00c1c040d9400515407240903c480c00030b410103844101d440c4400250400301c416841c600a07040b030820058024040d0900307184103080742c101c08903c800413a014540c09046080e00e810005020072407000320300b031004055810000301c42400e00c806800102010342e11541508144810300680703141c3c643c0501075981c3ca044ca00c59141356031406000d00800c0204484d000a001c5c64020100d41210846864007814045111520406120045020241c194032a0000c1e00081c60202e0980d1400218082c050460110108901c2c5070151817402403050c50710400420001d40d490b000940e1595034000b000050248582ca800c602802c003a900050300030800481c040b0030800b07a4170140080d02c4c0304000030420740c0d5820510f18241d645051440f955900940c10502c481a065003060642c240101d08a07460425401d2601e103440140c1800822607075500c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 619787922 1250 619786672 619786691
    0x140d030f210c21060f061107180e121314130c1709060f0f040510050106020d1b0308040807030e03030a1d0a0b0d0c0903020d0b061305150402090f03010906 68
    0x100340c43d8980049190302c08212007418040e803c0f088412900581d0140001398800343d40d0b0601c10040c4101805080380c0006100310004c580c4805010544820007560045000e8401c2c0c1030103070300035a54034100350000400114a80415911960415003809400000d64008030003125480d01814030303002007941d03441110240158071403500820141150003181c000c1d4040c0030292122018031900059419642001034613903282c82464034603008103420009040034000680260003003080448400c80e6140c1c640d61300301c0c0e61344000d41d007600104020042807034080414041174840b8050702d5072601c41e08001c42d1180f4001c0002c2d19542040300f07440c0005a820400c034244102d11500f00c035003d4011780d0103010a5080002c4024240141842c200c401517440c0d044501c05071107089180d0095070050001c00340650182801d11201070304840150141c00c1c440368000050b2500d00c281c40c42800300d072041c080041642400c01010f54044880c0702e510010f0803404400d603580a102d4000890301c62000000c004a2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 619789172 1250 619787922 619787957
    0x50301020a080f16020a061a04060e06031e120715020708030103171206091f03120e030703150c2601060f020a020112090215070606140d030f210c 64
    0x80041c00130380f18100c82d19955120075000075a60045650005022551005540c800e5601c066048200c640c401e060030030000342007195403080c9006a00035401d64038809809200842c0030040175001444503400300c0d400b1680030003400c0103030200310300c5600040c0d071004d00410319000307a0700001403d60b00c030a4004010420443c50508401d0b00e020154007035070402660710050701052034010421070082420100003942c030746540111030910101454a00192078903418036800d1161456000c07400f0800441c111440b40c80c00140c00c000326948003100540c079414a000141c050000c004d240c50901c00b85051000301089503402c01141e9151107205240190b02d0010000d010b0200d900502c8159080a0f04010150344d02003255000c6180c1c83c2400b061000b01d902c046000310790700749025510b11201140308803c010031303a00403804649110300d0200c91080103901f0000d440b4220500100490200400d42c00990302600d2911400b940100444000c10002031142095605140320000005d0325036099050550 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 619790422 1250 619789172 619789201
    0x120907060e13090507230f0a0305340605130f050604140a03022115060a090b010c0813030c090605030717280201080f0c03010506090a050301020a08 65
    0x4020325016011400c11000710319048007145104440783d0711910400e052042c20031440c0b0041003400c61103800740c400b00d00c00030100d9400582c11441101090048243c03450070b00c200100390398009010f030008107a011b0009030342e1042203040752034881485801e03600807030601c0410001855a03407a401e558600411b4501450b1b5950380002c21050500d54084c032054541c40140c40a0311700d0703000d540d107195640c00c001440e030400a0780020b600071101e02c0d510f00c0b8020041140c045100104040310680c2150951070b50542001710741c0c00340c110a40d40d00401c041c4450350485400c451060600f101c0304002a1255102984600e85400c1504400e980400c2080340142402004100015082103150705004c0060b4035000c2c0c2e4451403218106c6020304501c2e21000b401144c1104100000f444c3ca0400020081c030301c6a424074000f607000c03034200c000280c003c0006c600c1082c42160a01d00840c9182e00b403204000c196000700510316003001c142c50001c41ea58500b440200b440070b0319a101c5155500c0d040030702041c1c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 619791672 1250 619790422 619790429
    0x2d0b030403122c0a0b0a0207200d0308151002070f091802010c1b0f050a090e0a1e060e0c0f0a0e010509130503121803093003120907 58
    0x40c0c1c6085021610542c900c1200d801900300f80380036020b1141ca0b21980303841c160410750b000e0482a01c60060260103900d650040c00500e100c0c0c0c1c002200950194000039182000d107204503003126101c8442800640310750102e6a20580c05042d001041003181c01084161400b2580e01c000f580c4200c0040c0303d07000032503900b00010036042c44180841e0000001c01c2003c10142c0000a0502c441060204104000100340510015620b148400d80c150b464030011640021032190314012a40c05030042010121801496540c800d01e00041c1541d400d1695403501461643e20380302458501d0503019800500c072401203a207511031900081c82c05c100f5517420070408801e80c1c440a880740254100c1002800c03503604050303045a03002c03aa5100c01356203403098039440544003080240a03000025410f540b005000284c24000e40004081c012402c028541031560391241038244e0707922010541e14004008494410780503020900f09a4030400356601901e00e2030750b000329024051402c0300904000e6032450030046103009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 619792922 1250 619791672 619791707
    0x40b0c071e020418210e0d06150515120405010b12060615030106120b030c0607050120090a0b090d020621060a15110c13020a1b0209012d0b030403 64
    0x50207141d40c2d4405264070b0319040d1740142e09072800c401c48140141c034680c2c04060f001d4416400d88459140400003814003080074014482218804075030b034101100c5a482c1d1500c009581890010b1110740e09113103c00090049400d592070b014140b800380c44220071a0f0100212000a161505243c010131008080800111204030824001080302c035074420030102c060700340c4031000a151003244d40840e08280c02a030f0416082500040c40c0b43c00c01ca070540c888807910aa00c0203402e611110099400120f1103642c0081c0e900025083c81440001e060100425014a0003021665403e031a0b60200790182c1115400104188003007a040c001e958680e244581d0101c0c0440c0c118030b00c1810140c4c510221141000c1c55001c03c10040b01c035600d00001000203c10341c500041c0350700001403040072413001a6120040a0000804820841240c0b00f164808410701340d0b40146052056824401c031491200c2d00448103402c07003011a820003880301e10414140c0050841690070542d00c0c40d01c0e003005000e81c07005401000a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 619794172 1250 619792922 619792961
    0x82b02090a12020f100c0c03030512060102010c1409010e12060f090c03060a0b06130f1502030c150709150903031103030610141c06082103040b0c071e0204 68
    0x60b50794068004c08200101c9929124110a020440e82c11462800c01040061540000f00515400601900b604912a0014403290b50b41e0b400481c240d60f810030102c030129020603054420345820002602c1d10400c1031500d0120440c3c1580021500011010303407542c0c580000052141109119110130351101c4100d0051050301c0d00300002c660344903002884516056550341c0c3e10b10069a4002c1202d406c00308520010300300c152144200b05c1c07180303624030800c1b42d0340100420000f045d80c008410390310f02c07542250140000c0741209080e1206103d004001c1e104005014a02007a02810440c50302848069a0b9400d1482811840c0240c10903101c0110b1980c04ea205208201140c0c2d115000010303561481e15200950455141e648101400b44040413009140354608100020446a021504035000401221030700820f024551401104080042140003000c1001501140d100d2800e20b0308121560940c6140540360380320380c00c03204c1e8031b260f210000744144800e4105614150184d0b480c851007a80c010711 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 619795422 1250 619794172 619794209
    0xa05090a1d070f05030a0207060204030206070b01060906090803070b1308040b03060a090603020310200a080609130309120206042c0108070b09010e2103070606080c0607082b02090a 79
    0x13000c0d400700400380c00c2c6407900010840d040203074580598006507405007003da100d490510381002514024010580000c007020000245548154102401c40709a900614600b200da51558000038000401501c42515020000d000094002c1c004100815807001c4058403030409000700003800d8401e07403100c41c0d81c0703041c16400d00261b5804265035010080c0c0400004003102c2c0a200e588a8564a0140061096000c03606c28000c9803c00e080600c11b08085483c0c074442e41d14050340d560398200880307020b0001240040e00380407043c1d040381c040110900041c0201d040543d101c09040120b0741092414000c1c60005130480c041051032a00706000d06040e0b005890034a04145c61100c223801070b180c1c414100440550030700340076102d803104020000a2810b00103001e4404401c0c04d41d0300d82c4801d604607022445c00c04006900000841c42212400b4002c04070b9290003403a40700c5041e0344d04041041c0e8681e40d4515195088020700c450b5035140340e02c54003000351f02c81c09a40d04100b143c2040368800d120010b001e81c40700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 619796672 1250 619795422 619795427
    0x3030c0e01092c19060806070906140403020303030109020a110a051b06090405040501060302271503031c0c030e0303150d051e03071103210a05090a1d070f 68
    0x41d1503201003c040a04092061000c48003030190700000c140c0c400d4020b000202c4403005001080c1c840540d4244960390340c0d0511310b561080c0c102d03105000038440314014000d480c03180309a240810340011b8800d0515440c2d8000904661088c1e014000b543d60020780005000e0700114044428000c0030042e00c005c06131500c4454950061980b91042000800c005c00d07403031359800701078031143c0300007500030042454a031034818024001400207078401c5d00c42c10240e13000030b18101c0d00b000c1350707132800b40b4151002d0321003070490b5001004101e0a190305000501c60000d00400300c2c5074525401c00d807898041602d41c40108040e084980c07079088030301c181e0010020070180142d800800709000741c003540d44080c0d00c49070b4103080381040b07169900d80300a101c40710021012800d000000d050b4560281c25600c00074018001055918174905055900c003a410445490f000d81806025000112030390810303c0c03a029401c000605104444d404c855101c0000003124103582c5c3d01384e0700c1e00713610000500f40f020100080c020302 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 619797922 1250 619796672 619796687
    0x120f030403080f1b160c080c010329010f0e0d1101120c050316200705090105040218040b1f08090d2a1a040f15021603080a06030203070b040303030c0e01 67
    0x320130142c00107401007540245051040e081e90031400380b2661a8030303003902c551120080255140020308164136003c0ca222045800f03602c915040403810060003c2e58011354240314058444014401c10100c8c2c40342d1626804040b2002ca840340341403041501c03501001608201d000070030303c095180f50a0342a1880c60300102102c1e0064815502400d08184110045468003030406041c0c2c14003060300710001d081e40000070302d6000d40b0021200e16880ba0f8942e41404201d000361020301048860740340883d1441d0030642d02c59000e14001400b900651200c41c2000c190740381100e070207000003400c180c040003216041404103404400079490450b440d10840349030140e1020740d14003400c0c3c800e05115031443c20030014021415021640c485500132528140c184200d5071495910203460400316000d09180d966410701c02c55110300c1c1e4040010307030411401d490444a5071002410701c8402540c4003008009a0b030100104002001161501d990310350851400400b5200300000803000e1041d50b4000c000275a8010b5003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 619799172 1250 619797922 619797961
    0x31081801140f0a1407050d02100509010b010531230315180a120503160806012001060509181c090303030504060b120106060f140306060903120f030403080f 68
    0x4040c1380300110304032052040c0c492030500030a184550302c0c003910084d4021039000c03989425079004001a80d140d0520750700761020f5404590010300d040150b107074100d4000c00d881d8075114100d0342c0702c4007400c0011700c17001252043d500039403100800ca890b4142088190b030500d00c416003082c0d01410f10100e00350050500810003a001542c91900c0d40030303580e0000002c00a2501c0c02c0d070000140754000c0c0c0e15450251040e8010341d801b1408003281e4030603040d16030040d1a810301800e010395448507002c2039400c01040c201301d03c00c440c4140303548441e800207081da02d007654180250800c0c25800c1026130020606860100f4140324154141c0c0031141a170885d0f600914420100da41600380403605968038032b0000d0042c4a030385400c60340641e500008000082056001d001a1009515202d0840b5030b171960540700080820710780e4a42d29000c1001500904010000e400351800240071a00c0e00c82499811080b5600304600100e0b2400c0080100002d06500224071900084c401a8004041c1810142c00510082401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 619800422 1250 619799172 619799177
    0x1b0102091e0a05061c2a050c0607122a031808040918242403080a05040b041805070804050a020d020f060a02061008010531081801140f0a 60
    0x170001e024500d08001ca039100d1400003001c110358005120300c220611304c84036111007001d44644e80124942c0c02a011503030040e003403000500c5940e8a900b82100d155030701a1003080c816890304100c0b010040403a5405800f88030109641d1003504056400404581e0544104070480b4803685d047c40100c0c060a086074191155500082150303411071181e504003500e41040104817107540300000b2030403080741244c403102a0080c041170190441c42d1500e0104003003110901c4070480c1da0034104000049452000304072240d680c3c1429410141e4400031b041c416000b941c09582c2c1c41800c0c4400e8003a500c074071311500e07500c03c40504042020f4105511600ea865021040003401040d29120003c20756480f42d00e06c01d10410300a010980d9241c60007002529031105850181c0491381d0858013148a840c18054584244c070002881844449e807407500b55076104100187c0d01071181205c0041d0003084c0d80303070001e103104181e1080301c00c042100c2c8170005003030350541450740500e040e00f4050b0300500070b8520110340c459070091 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 619801672 1250 619800422 619800427
    0xf05070c020d08031005092a0c070b1308060708090705040c0e0112060801050c07020f030c09130c050301050a230411130e150f130b0a050c1b0102091e0a0506 69
    0xf82c07800d1704074082e8001540c042d0094003046080f80c1c076807004002125030300720414040c0784081890711150095002d903003115040f0110900400d80c010307016150801c0390310001030074199034400c0d460034000c1c151040400248074804114207203408000d044010401074030100041ca2003203400800d882214144281045076008074010004070340d0b0003140280080310000c001904107450456260ba007e4a4100c1c02101049801d01c42498081000c140c1c0040141507a10280c2d20900c426640c0510014200d0300c02608207070201d5551801d1003618415103824800240c03200c2c0b0129031400007064048050000c3c0d40320003c020000b080d0844004401c20706659640501d0040d44208024084ca28241e0101c0d10443c05082d040d44c1501060f640650007462030080591500c2e10a4a0350a18018000c1c1403031803040301103401906294013180c1c0c405500c9000508248dc1440c040c0259040c40c4408ca003d82e4010820a210703242c46198000340c2d140340185504110744803c00326071000300c1e501c81c3c2441840d01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 619802922 1250 619801672 619801681
    0xf06071706060d1a120a080f090102030d060303020604061406030c0f0d1505040212030c0604081b0a050a1101030603021513030f201e120c0d060f05070c020d0803 71
    0x4040c01d90741c2406a402044c80351941088001218041c3d010030340c0e200c0c0e020400c01450500c400306041e04215000030b0000d26080c0c8400c920107a923480142294118131007003002010901c030780d10503813000d184694042d0480d828641000010303036400c680c104080e041c281c003c2c07020554001400c1c0e903149500742c030941c0170004c10700000b50031010f6500000d441420014900f0380d048500da4001c0e03103d18400c90310316180408030704400380c0c0c9000342131440c0c42507880200400c012840e51340c0a001000461000705446560102c50f550030614001c6003204d4943c01106480c0400028403c0e1080611007860100980380c5142c00140446940300b00b0b0f040f2403400016030006807411483c05502440d0402140b03000e120386403904e59198000d01c02c0d4188030903003840000546281c045024160107040481402e40361342e00100f08125007400e0840004940301d42c56154080e5147c18001003800303030244000091442b1012030354800c1d510028100c8080000c020240070050759103c900f440c0700d680000c0300c0b5880747c0d030703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 619804172 1250 619802922 619802929
    0x1050d020909340602060603070e0a11070f060c030e03040608100803270102030702130c03140709030507080f030712091805040201030b010c2d060218030f06071706 72
    0x200244040f072120700180d1141d500c883c880c0c009120103084880c0800f56918001207807228810b885141e810303008000c4c10004200c02c00c0d1800d0300008420341c002800110091400c01d542e200007400c0341c001045090403405d00199100b000e01d9084d8509050091000840c25a522131089004032820311642c0f5010490003460a4280c002800300b5008030707940e03074030b16010f03000b101d00d6401c241a501c0141304291010952002c000c1c0c4010300e60203000441042c10054807440903225018240080596030f082c13845506402c003003581e001d40e10b01d4450220040c00e41c03d0140c14281640c00038050b41c0d03c031400c1c10340000303000000c0702d041c00c6c1c0180b6005241d6460b1a0202d4001d1650ba00960082143c1070741c1103084c512a03403040b800749100b6241003265240c100010340c0c40d81d00055000c0c02c18681e03202c06000c00c0103441742034103444600d8281030000880c079540d00f500700d0300840c2c803400e0500c10200c401e4005080070044d50300f41b03c0d0341c040200107500d03022600070700d00c80c140750400d000e152511001c00c12544 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 619805422 1250 619804172 619804183
    0x9010605160b1024140d0b030a03031a01031e021605030705011d0105100b1e030103120e011e0c020604030f0b0613021303020f0607080301080105011a0301050d020909 73
    0xd40c01042c64255003080b06511000950038001d10500f40446403030440c1880c8082c1d00d0303820220b1240c603014403803040c0b40802c1d030842d044681d070900090340b0b50f0130714000c03a90144440000c2034441d0703e002822040300800c43c1c11503409100311301d060610f449a000c1784003400c05140c0c0506030b405071015035540008000720b00c4042d40014000d140b4030011075a40100030381900088500801041d92002003502015040d0a0355000c0d04c40d0b416641c881d000c140041d406040040040c001c65200700048501c010107403030381310b5000b64400e07505c100e4100841d540c1e03030764031038031030556070b0001d10b4000621a00441c000f151120326405100502c0909a84907085480d0300040d580115005805980302d074001c0c0c02c0c4002c071418100d0b0710500c9288810900c00050f0030a100307a401040307090700051000c90455083c020f41d1001006c040f0350040d01404036100080445008502a011460000c1499490120340b51101c0d5640c220854985e0020700040c002038840c00a00ca11282d0119640025619010442801c14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 619806672 1250 619805422 619805467
    0x3010908040b210402060a0305070201020c0a060b0f0117130510090b0601022b080a09080403140d170f190e010e06060a080d210c0c2009010605 63
    0x54404200020100e01c4440500300300300350340d03c0b44543c1c03080984900655000c03c41e4001c1d80500144200c40d440e038840e40c8803a80c0303e1014000145004049161180383c41a0340104071030081d110301640ba1795003007410b03a5010307122081c00c2010100d030f0f0b20b240350300c02001c000700f51414501ca03003103c43c000d016007003003040311001c1444420088c44501c0c1c1043c4c40c402d442196100d025122381c0414080c0c3c00c034031191110340e0fa0b522084030798009160340342c1104da07188007801d450f0317640c2c4d1224011404108070328024070045105413040364407181d0481000703007007030707801c2c45141c0038401582c1d80305030142c2d507032481243e212084841c40310302c558611078206951003503140712040040c5407030184072500c44158090000500100300711041a0740740010425480000d00909010360004101049441e000300960f000404209900100c0340441c144680102c80d0580b4140c0c1c00a480b2603120014800003010b0288502c00300c0c1140d80c400c2052102140101d003041c40b400c01000700024111025102d41c80100e0f088 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 619807922 1250 619806672 619806683
    0xa1e0f1101090204020a120b0a050102060604180b130c090207120e0d0c1502100509100b060f0d0f0606171f1a1206060301031110170a0e0d091202060702030109 70
    0x261001c804000b8807003084552075510341850812011102c3c40d009d10000102c0d00141c4c010041582c41400340301c05420080f5141e80c201c2079111418002a8010882c20301c10404c202440c0d20820250038105d0300348003d640600c1c1207510400c0450045201032604442d02425410250006009000031540d00d0340e440502410000c5850400b0442e100420981d0311843e00d0359080352100340e003260301c0c00304444050302c0342c0f0b10503404031800c0b068191558015007071484006041c1410710040b01d090710855031001402e1600c948c0d90708000c0d00808854441c110107041149004580481002440c03a138001000e0140390514107a00440c07001c2521000c8844040c00841e507682051009221070458281c1100760107124031021000007800c00e090800503030b4122500040c00d540c0c00c41320201481001a10f40642c401040940c0603d000c028a00d00c2106000308002500010303058040141c96050010010440e0100400c00c84100f105294844a084049030100c3d40941c1c1c0e0306a07440042c0c010084040300904 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 619809172 1250 619807922 619807927
    0xf080c030a0c020405070e060301030b070504170c0405070504081e1e0102030a051b04090c05070f051b03060c0405090a090203010603050a03090b0901140304050703170a1e0f110109020402 82
    0x8103a9803000030b480a103842502c0a010319120386100317407800b0429110058010741c0c1840104045400d1400303040c0c11201f00d0070518640b545074419003039510305110304080c160340660f0074401a814a40701e499031000c486c0c90f0803404c181c04c00350546e1f101e640384161001141e41c1803041c0320b44040e040c41000e4400c40e4064403e41840800c0c00424040e410480d0090201c51500d0002003440010540c81c0001c842860001031406080600f02c1d4000c00f803440200c0c0421109104041c0000c1c1b0648803012103900500003403a041d070040540c099048160300c40c081c025081042407140c144c01040564040c0c8a003150300811a540c3d6a034014001d04100ac0c020f5490b45c2441000801e010011a40c015038030b010790398a02443e40c8075400c003034080c426400010b000601d410806040c421400d8080e40e0414424400d40d03c40329581e8039685c4044d004002e04500002c800140d002000d50084980074102840800c81070400b40495009030140840340d20700b00c1806060300007080c03600820761103040c140d0b900520854 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 619810422 1250 619809172 619809187
    0x3120e130f0b0306013c1203170c03060f0d08030a0c1215150309030207051516050c1c020a050105031f0b09011d0d080c0a1502120f01120f080c03 64
    0x745000090341c03103a07041c8800c02c4084501d06d01341950400384060404079620245281c030602107405507042205808125510000c1d051102c824900c0902481c1d500f008261203007406c0080042c0c0d556004491031107010510a0000050a0102601d03480040213800040748c900080003a00c15029404043e12003a10f03001c054100503034158549426103111100f0784016400b000400c2d422035030f0602000e00540e0040d0010040c80c60301c2000003180c40280d202e40d90a04150200e00c2c15070309804c0c20304030350f16040028443d20324202800408149100c58940d030f81c0303030b145036004120b001c075450041c030b41003100000c0042d45103810410103000480c0f50906e0610780580e590400e81040e003102034454002000201c566800d4500c00140e50760244c0c00500700520100c0d02c1c0d95120b05980814000030050241c10f1500000c204960840150111069409642d07100982000c0091441c02841da21802105c84018004500c00740c0c0807100c00c030b43c00300176070780b03c8920b0b400d145c2d005004455052045110014005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 619811672 1250 619810422 619810439
    0x105040320072d08070305121c021b06100506030f0411100201050718031e140102040b07020a050a0803071713060e090901020322080408030f0403120e130f0b030601 72
    0x3c5051124000800c5081c075201d25889032034034400c2c48050315561040c0440090584010000c0c400301c0e81d5a64130940f003c0303500c803100090783c02c4140412600065006660465001030140c0e07644060104100700480d4105030018989001c068403201d8103202a0000504025814459a0410200800c445007040c100c04009002c0e020440380c0600080034a400741044074482540c00302034a40c050444105001341e400c0005421000070002c0d42c869041e13070041120b444081c0b0041000e00300c40f41820341d8600c19070042c050901e07696801580999104a000c000460307010007035450b1a90701c40703060f89418000190304101d0340a1014005094614031000045c441e8004200307200c0d41d6015100f0350850782d00c91715554200d00044652000c00031110040105031107820101b5031100c0d110360655814903071101035180c1b4580080f07800303444050f13000034180b09100300c688414200140034034001d00a0024003010400c4a003100000710302d05a2115041d42c9641c889800c00070f50f608008c1c0440b515582d484055 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 619812922 1250 619811672 619811729
    0x1018030f050618010b0901120f17040e01121a04210f1d0f0112150801021b060903070206031503010e010f0e070806060d03050f0406051308010504032007 67
    0x5003ea00b4541440c0014101018015010b85210040c80c81e20203a1904030024480868070404451405040990b1800281c42510f1030303581c683c0048803140c44605080fa00030a444068108410520045803040000b44e184050001c0c41e19000e0344182c0785840300e10b04107000f070b407000080000325121210390303110b995403140d1401c4c000b0442e03503601866003114145103c041e50084000c0f540103c0c0c0120240529402440e4040b0112007141000032800031212054240342ca25402840c0a6500080c40002000c100201011032007280805404036040c01b403090707a5244034800009000340c802000040800e4081a00b0440511010380280403240c92500503d00801000d42902d002900e840f00300c01030407500160310010784d51140000e1849440e414208515581002801c40412404024ac00d44070455071000e0801805585c40b000c0e1150444016001d13000d01075003103800140c0c5030508100c042035200191003054108800800e40c0b800d086c820483c1001131740c0c4c0240f130f4010a009801121045045039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 619814172 1250 619812922 619812931
    0x7030302030f0105040e0d030e1203010807060f080f0f1506122e0905090109020a06080702010f020f0712020705100509030105090303040512280201020a02010f0b1018030f0506 77
    0x400b1490ba22202000119002d084070640301e41e00071720000c410540642d0100c100b880c1808100c03045e001022016043d82c1d442604032507a180c00c0020704000207500880c03503d50030300e80c9091001c200d00e0a50b507000300f007910041c0410f0b1003064803000719048484680859020060140001d0303507880f05080c0720128042c090b182208040c0c80c1c81c83c050441030f03a0024965140b030318130160b40c2d02517203001c483e070000d09030203081c103e555581c500031070005030b43c1c1e0a1100000c180586a00fa02031420303960123400c40e54040d9041d07040724010002c00d001e00c0701400c00c5401c0d441d8400c0040203900403880d001ca02c2c7c0801500400d0700050904007001b449900400509000c0310308400a004c01e55424185039142e020a4034014055800482c2110f1881404400380604801e050600a44006c030306241c80c480022082c44000581d6000519000c060390a0241d5000035a0808042c4520f207602404140001c0c0d50041c103004004503921040c000c0325900520710004c41e0050261b540100150810644405c420399 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 619815422 1250 619814172 619814191
    0x40f1a060a0f061d06041d0103030f0813020d03230c010f02040503030912010b09190e0f06010b0d020903060903040e09160902090d051b1023130801020703030203 71
    0x400141280c1c945030002c25540156200009042d802043c98035000110310035a5000400340008102c3c0c0b00000c2954442c21404011722001d945075083c0607124444d91402041007000080c00c00c8136103c1c181d0a204c034116410764129010045508044444c00840c0e03110861902000c0f00a50314450030401070300082c04243c000708501c1d940360760f03410100e114500c50305406030800c0c04110401d00e840200044554126400400c044000800140c1d405004840805c1c80803560b20f049142c106a600c166280c002e9064010002c7c011034529141c1d6031700d0144602c003110786c8002041034000d00560140c4400043c05070480c1e645080801d60644c90b908203004214845030010009401c607031001410080240c4842d11503c1341c02e0900040382c01035400002c178181c0141c86103c44000161080041d22100851666041440611f1a04000c104500b505000c000c221801610500c403001c0d810201020400c814040303551680c003440e4102d011003c41e0301404c010351000c03a04505054264006610440030035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 619816672 1250 619815422 619815439
    0x60606030a090b1f0902120a020306060c190b06040504030e0f030309040504140d08150d0f050307110901060203040b18150a050d06170a0213061a0d0b011e0305040f1a06 74
    0x621045c0101e020310101180d103850700d50040b40510001c2d5008580040d0b014240514100107104a103181042d502c243c002481c204502c00b2041c80403035040310342c025508940a104ca4241030300c00501e43d0001098891188400c0c3d48840340c1644c00304102c03041d403100a0424005494182080802944403283c82a240d00a04010340c82d060f2181c1d89062040d00d0a00ca50545481c1000a003c40c548400e0000c41d0303680100c002090205030304101400c24544192005c81e000f841030014881c201c1340682c051800e661003800180080000790081d01c400341b1a980030100504001000602080301a20f07170fa90381003a00084240c6e03050740c808020600c0c00100390040c882d260fa155056072402840d296040d645400400400703006281194070142d44401034000400c04030f4854071131444c6035803011a01040240000383d000c2d0508028040c191120a090074207481c1d54410b50300c6031890b6024403244204050b52000001c0402001c40c1c81c044484d0f0f0001c01c0c1c5d0424602180400b0606507082d1070661284824 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 619817922 1250 619816672 619816679
    0x50c150f06121f0f020d0f0f020a021902040f020a18120f030818160305150606040b0a120213080606030f0d14093a0203060606030a090b1f 61
    0x1002c50071909091440082603e84000720001881c04440710442e001d540c0c503003483c030300103c03081d0000d0043c04641d20b100081011150103c2e00858602e2009004200d005114200c0b0307980e004242e0840841d041c041c0140000c140e44000340003001c80440452402c6c0c80031450500701c035804400700383c200380d408000c0d035002915040626490a03c0800040000d4103049540700000e00c200341c803603002405088245a12031000100904000c40e080028109900d030305410403c3c04010019000a001407032041c0916051403804941640b1581c001c0d4580d000d40041c43d02c040314418102030006a800503401c43d11a8108020034448442501c10f0105912410f40410401e1070301103064811907500038010010350b00e600350207072040224070b8480c91303010805020710b80554032240360100d090400c0b04644611240c0301250740b548000100400e08140c60b405400b10f0058800064490b0000422034030a0386075528802e4200140040b1040105030300140360074132408083c4118201101c00000e507804010702c1d20b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 619819172 1250 619817922 619817929
    0x507020a0e0c041701020c070b090307061b02010e0a030804030f060e01020a080403030c11030408060106110d0c0b0a0605040e0106080706031a090709170705150c0d0f050c150f06 78
    0x1542c04040c16a0704020802004603502041114a00da5a0000d42410305104405041c01401d50110900400006140d03032a0b190030312012019200c5070a007540f1319920504180c041804082c0001d041c00146910301070b90f40e41d800c1c0180000d5070301581c2e06940d40e85030300e8921003148040070200c030000d0504070303c00d0b01c014041c001e5580d03208007952183c40070341d030300d490443c040d10020004130306002d0008900680164148000c1014110b4440145899454500014404205014092803503000080036020299100c1c1c4450a00b0b0703004001c10260b80c80d03441d01c80c00208503980c40160302518004031901103c0040d00301204503010301040d40c0710300e595a142541603d503902c2c0280d44c14440601d0b109070f18940400300e19000a051716060349c8460315036407240807a110600c511078041d03000c4582000703e850706804602001c3d03503003012541004c40d40d440c9944d80c0c11011105c10180f202d180d03070f40b001131031040f0182e4491000103811100c810003c4100e070140c02e1000d940255100e2100c400084950a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 619820422 1250 619819172 619819199
    0xa02120c03270a0303110702090604050406020f27010e090a020d060e070c0203071e05041e0203040b0f130305030109180210050a030f0e06010b0309011506080603060702011a0d0807120507020a 84
    0x923000ba06030344050362188200001014014421160030381e0a000181242180303501a00045103104444082984907042e80002070f1013014042e030400a007010361340c0c1e6036142c040c00700c2d03000703180001d0141c0c588a0072404403018000907007040d4401800346040041c490f501992614105000b607081d2a4207946900c44600b11440c01e0700e0403080060802410000b07401c00e907100c3d408141001c1400c007002c48020303892500742d82c02610140d82d2100204c1c140140c00da10403080d40d42240080c25956281300c500c0d42c02400e1800140300b0318074a10b17a210501c240440045c60f561650540c01443d4000810044901801e01d42182e000710340081c0c5002c0165841400c0c40c8555003c00ca40b05008021a0b880c00000200c41e5000070014000340d502d0700100521481020f92010150001c0e850b49801450104141860610002c00d07030b03811a07050001749101c0700805000b0703004110007581d100340701c1c02003820b000c1070504c5040b00c010310b940e07122040001c14660000191840b64800c4544400466031003607024100d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 619821672 1250 619820422 619820437
    0xd06050d03210b100f05040521060106020a020108040624030c060311090d02060702030718020a08090a030c1205090613060207081209041802060c06040b0a02120c03270a030311 77
    0x41c160f0501e0810140502e244544021682ca1306c02e00e09915000820354140b5000400715250030303c0e407039014046e0750a00045001d00344910007404c0c540c10540000700f40d950040c2010302078a039a40b29031662411458412410010407001d4200040c0da6850310f00704c0780c5104c2c4501d2000a1a24150300d0721200070303100311244030742c0003854040c1095131a002c01030b243e486110700302e9040c4508900002d020342502141c91801c03d06d20320041e210340e41881d01610201e001460f90241e50016591400066001140002c0f581d030000d8a00004005211055809114540c456a44404003107490b00031102002103c40c1a90081c0e400e8a9000f030350b0b4030b81c0c596101050ba0041c40100828842a8524105540240030702405200c00c0017004000d0b4000c20140e41c0f0801c403803009500f26600300f0081c0302c052000030303801441903602185483c041c011305504040d0094400001d5507000800b140c051601c0e101d942c0301c540003d171080c00000c07540103000e0ba078880d0007c0085000c03d0070003660600d03494130301091710b81d40c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 619822922 1250 619821672 619821679
    0x1061203020a02040c170a2009011707140c06040507050109030201020604080307020c1f14090d02040f11131d19150b03090a0c050607020d080d06050d03210b 69
    0x612000c0c3c1c02c00c400703418a072128a04204010000c400c1c4d07900000308150040d49100d40001e1007039802d4801e903442003821b2000c00140b0030100300002e070b143d078800c206003011152501c410000307464104084641580c0358040c074124440100d0f80d40b40d40300700072400c107000302c0c4034204552680d9500c000540f12034100d0720020303000d80c100000207400708202400469200b41d20744150f0749030811900008a114503090581c040c2c400702d01a42c0b0b480e19030010070441d90700ca11340443c1c0d8185403110001071061200e144c070003401252281c040c20007020346500301c031300c140703103a01803094035a030f2a4403c20002145038031402a80d4110303071480c100c40845074288580150484c1204600711510f01503214040c00d110000001150104803000800c513040c1c0380550b0150740440041e010035112410b00c44601030464102c80d1081004101540042c2d907650704140520383d00c40c60450b00c450402d510007005080d640e0219030840c4c0c6a011f44410142d1000d03c00032416450344040000c4240740f030303002c0200c1d00924500c641 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 619824172 1250 619822922 619822933
    0x11030d03061e08120c0f060a0e010c0804050d14070c080109021c02010c030f0203070b0c1812030d0c09091404060507030e0c0f04150e0a0e0d050f09040902030a050f0106120302 77
    0x7030024808001d00302d201401013200c5800300036006c03203440e11800700c0f0603040c0d035580d031060301e03513001802c4c041e9181a030030504d02480c181c1016102d154541c43c03001481d00c01c0c802441104900c405682023034a84042c0c0044610b400300f50f079808014081c050900c0200c0c495044191703009203c403980c030398000d03041750103035128a8602403980d030a603090784200300711000b944014040d11001603417a081c410700c02e0504144150315122890f202480c0300d1030f80102c65100b40b0541e20707648151070b0f000044d00c0c3784403009640807e0b440c00c803840550b04030070b9a81006644604003881010b0f03440312000401e0145200d40c4042140740d070f85650440c1180d80241032a0440d401440c00c642803072603e030b5084060000c00420014000d04081c0b185c019028442d4007012030036049100704103001e015841500c0c1100c58400140c4120090003c00414a113750b50355080b4500001c66174010544039540001c6100d58003404645808103d4100a5610b01c1440c461100c2d42d8200344020408880c1002070020143d8150020705 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 619825422 1250 619824172 619824193
    0x10203240d080d110409020a020a021219110103060807030c0e0609040b04120311040f03020306010605031e10050402070602090a0b0a020c130e120714060105061611030d03061e08 78
    0x10064031500341e20313006a400a00c00441c0d01445031004000e02c1000b40c0050688803590710500111044240400149400c41030400c06a4427000012800d540c3d44015000030110392000180d00409050704940b4092040d1b240c044108103001818000341d4407a640448031a9407018100f2800140482c1c0041041c0d044030003080c0040d030320614240080e070840c10007043c5a20400407030f44158228dd1300603060307500360140804c151b04091080c47d02411b40343c07801f1407643c50440e07601c0104860310f441440c6040e4071080015000c00502d9614006800020010740d030320078803400c00034080e40002d0000d0303102e00c0c104a400292120300074220760b948521303600a44120f01903401007142d01e920010180c490340c3e4440400d87c03403486c0b0601c0191070380308070360306496120042800c0049518009036030940095100c0d030010b001076620f50b000c0d618020400550f0341d5121003140740c9013003008101c1900c150035103d0600745044941e0103400540c01e64410b072441904612003510700c4100c0700c030684180d500c2d40c0c02050b80c81 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 619826672 1250 619825422 619825447
    0x402060a05090f090a15050f09131403070b06030d0e0a06030906060902032e1d061809100b180c0f0c0d020d0305010e072708010203240d08 61
    0x409811100800e885040c9502802055104c4011a50390700c0b10741d81c610f04060341c200a07502c01c5014040a4400700340c0c01d070514001c40d1186030054040707400801200711180400071154a9245406802c0303064036240c910034907113080c803000b055800a100303005410103405414415031000c00400300007015418014a8004150000c117032850095a40a80b11100803072a41440e000441c0156450224450140c00c07002705c001c6076040b801d4015140f41c02801041150007400781e0200c05160f003207818144503454440004010311038000c2c0d100003a1046900f0000f2411000c00d10300d01d0044055018804691030350208900d00020051a07507501241402040d0b00c418500d02030700d520202454214034000444080c1480c019040000100682c84001121040b9900d80107250041150448910305404d0020001e0000d1541014010070060020861500c4103501c800031402031030003900031580d905102a0440e54107e942403115201c08020340c200c2c6940c01d081e44200381c0b154210740880e00700b0609481c10b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 619827922 1250 619826672 619826677
    0x5061207120e030f220e010b0307110d03050103051002040f0b03040f080c010605131118010504121103160602120a0e040c031b030515060d091b06080f0402060a05 71
    0xe039225540c0e00c0d8200000c0082c10002031801002410940f91074030008111108800c3c05541d080c80d0705256280c0030010300a00446050548503a0800c5580340d0343c50140464503e5030421510040b0700c1007079266082603800d540302b5070599002d142030f00c0024411403940410b0344101e01c200785075171800160800c003008000020f160818800c19400b90340440d142c482a26940100f44c00c6491039554400420292510010022504032008030030710400394030078420410380c0641040210a20341d45218082c13168030540880d0054013000f200e4036400382442c280481c0c0d003401005098003030301c640c80e6071320303049510740e1600c3d4104e820690040500000da03030f06402203070f04a03403035104c103000003011021a01e640714080c03084074111954001924440c80368a00c0c1027514580000000e051400c41448864500507036421110017091311810740e109076054035000100704011001d0561100c031000e0700c2c801414440880111651552020080c0d1508070105100041c2500e0013580000100549110203024030003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 619829172 1250 619827922 619827947
    0x3030706110f030f090c0f0d0b07090306020a0c020301140108060c0a020a0c0905070e040905031605100501060831020d0302010b03100b1c0b0105210a030e090105061207 74
    0x20341800e00c80700521644441e00b0903904000c0100d43c403000c2010840c02001308148039030301115840c51000c0a50082a6107150303808000c0e002700e14840002e54824007911140000715440481190b4031020580014054107032250224400c0d402c0490340009400465105816554200701038812902c800c05a00c03030640c010390110095001d0800b451010445107404000141503040c0301041c1403034100402080a104072074102d10071484d1040e5000410800400c1d60102c0b61143c0200000c1030150030f140b0f05d000b09000342c0207665410000041621640413a040f070240707080c00020440083c10940049a141c00c0700444140403138005010b20143c035001c240620130a01034000001e52000340c0c0082810903c805071009849500e54aa41c2014100070000b1038100f0041d05803402d0800032aa5959030421061103014801d494460070642d032324001e40810301c4c2c079050180880701500d0040c940030f007010200544261041450400016140c10013000719409241146141003442d13603203030b6080e80c80141900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 619830422 1250 619829172 619829201
    0x60e09010e091203040308070f051207080a060e19140c0904090602041d07110d05040b0c01111c0b010306081c09050d151803020703060b06070819080c0903030706 71
    0xe02007010006450041d8003a5000381c0c2c038030f001c072300e00180e02401c945070140310031040100800064525a4076100415003002c52071800481030340303611071303042e01178160368202104c4e03403551034144441d40d42500d40e046c180445071003007070003400400b00d0503075400481101c50200240080108800f14035099200f000780700d10034100141056150340300281c51030400351140708101c41382c0c41800030301600065510440c030341040081079454080c441c020110b000d50711950740c80c1a4080364915001c0700a400180e03a00307045105030380e100c6002c4d02905642a07100032819901c40d03c0c080340314085500c28000c00c4241d03191180100000ad440188040041e074101c0c51325401c01182d94000b1400344d85e0305545a954500413600c02040e03200003405c01040b51407103201c500d02c40300c49803d804006500428980201c070b03040540024030b211301401007095445000f2004010420000c0e4105074403250031810b00d0140415511482613584d490601d41c424410b40c62160381c56071042c08400300103400340e008212410b81c1d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 619831672 1250 619830422 619830433
    0x30601090f110304030c0b06040203060d021c060c051c05070503041b090501080a05161a0c1f090506160914180703060806100e04030509041b02070f060e09010e09 71
    0x48007442e8003500107580c01c90000d40b00304110710610000c1500c140e003200741100c08615604040001400c06c0c0c20001000380561640905501c07994442c541800712550031000c01e02403180e50700760041495000741242210102c0611090308015414890b0368030407059030300d0346459a200c40d00c4000d01c044041942c6d00d41022220000300c1c0c989064003501d4000c0080000030942640740c0e00e030035401d14102e070307480e0b0b5820404404200855000c80a00d82c1d4601c4070341500c1d607951507540c87e207035040c129400300b015030b07079202500360354202c00d0907900c0780c5509070140003030300c6060b1201c90006101040c400040c1001070780c5140706002902c1914900e4001d010010000760420080d541c0c8060705080c00c45202010036a501030405c0007032001d0000a0340301071520907140301942007002c0c035a242040640041c0c10070802241314030040d1030780c1e40030141a4492081300288000203500081d0395603041e00030b0641004c002c1100003241c0380a58404200c004000300301282582c20303e075031215003440081c001111407244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 619832922 1250 619831672 619831691
    0x90307080607170606030402010e030f12040f0815160c150b2704290a09030f0e0307090b190b0409110a0c0201271d0603030405030601090f 61
    0x104002802080c000001d000c05142042018016082400c0720702c00040d400400c00c0002e64540003283c3d401039090a0100030b40002c10046031816000ca00048818407410f8000711140f400f50002d4000c0380c1c400314a101400382c5a8501e40c1e11243e40000014000000102081c0062a01080140b005440780351100e0000940c2c0c0b14806865050801080410307612a00e503142400c14241c000e03403e90f1484042e410642e1880d43c200c0f081c0c48d00500c040c03c0640d4456064071019110081d181c94508034003124009410048003840083c00318a400310081490301110321a8240240200320b4a80002405002c0061070861020301a0080030207a0b40e01c45054242c002d480320b0301c0302054010341810521a0745072414560400b045495551886c01054410f102481c1c210380d1000c4808141542071030425180c5440801c400480060010040c4040581c0301c0081408208811001c0500090303000d0701400340c8410b02407540b44e2180740142a003680012006204010341a0400203101086002c0083c03401e25 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 619834172 1250 619832922 619832929
    0xc0f100c170a03020304170c060403030906020403060c050a02010e281104020a120b01080105090604180501020f0a020114061f110d090806060a230102031309090210081b0d0209 77
    0x1021050b2404268048144002d100301d01c8280716035101d00081003458030801840c492382c3e600009100070109034459210354200100b0782c06031001181d00c1941480302d0f0722503c034080c03e26044250302200541c03800680800300d810020704004001c440b00c1006c0c0542d100002d0022410382e84540131b44141e03400382e0300c2d084903442c2c0d40f00507c40302d140c1d0394800b008016213400000a0390b0b50b0603400c0e03041200c00360060001c0d03514480c40b160481e0003110b000802108a0704400c01505c400b45000c0c2c4103500c04148003008800b1440180401420396000300417102002d6a00040c2d05010b651554201c1d03e040c1302c280c40c20a0005a46051031000c1c200401c0903484075113040d00e00481400d4070350009041071350401c1490020049940c000408594005500d414a001c981404a643c04144d01204d003c43c2921030a900a00880d9110380d0881d4640e480e59440e4000c030005408040022401946020050313540503120380280b1380030301c94940f04240810044048010b0607000b50414104107982000051181d64 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 619835422 1250 619834172 619834177
    0xb092106010b0304030215061c0f122006040f110a150903060605030303130b060d0f0606150f05070201141204060f05060f0303070602030703090503031302030c0f100c17 74
    0x3240b240803654900e46450020b003002000300454441103808814411542c0d299880c0c001d021101c03001142070700c035550401f80070055031518050182a01c02d0720220310079600c40a01010012040d10f2040d5840307000050b031360384180491b0090005c04c2861154030029042401c807a80e2084018140c88110380c540c40f04008820f240d00e60180412055a020400c00c5690702501c0001c2c9801c5019509500c0c3c0301c48088590180381c00c0c0102901d681400154035580e40303245404210740c0154a80b0a010f1440c548400204540d0090391440b4407a0804444480d1049a903400800c01030396403a414000c0ea540195500c9448502c8020040c5041c040c40d00c2002c41490a14403650107402d001c140100c00c9901842114400390186000300741400d000441520004100e907401a800b000c010303500d070303245c0c6421002403110b2627006181d40000428040c021a0846100000c01d0007102680c00400e100c1d02046510b40c00800d172030350840949450854054014030149140b54001c042002014800404250155 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 619836672 1250 619835422 619835429
    0x60411060c10020d1a090a09050106080d021501050307120b04050319020a1101091514071b03060605040b1e040912020115050405040302030921070311040b0405010b09210601 76
    0x3580131621001155250007101d1814403017a0305544018054008034100040c010890203c05446290b44020010309500503030041c4a4941070751842416060300035103401800114510924000c40003003464500428280c0c04c44d10904604488604241c2d585c4076500e030000d0050f54180018040c801105040e40c60315500811150b0181035400e142e840d2100414005003500e504104650701c0501c500841c0205c0e400d201420b5013001d10740c0c2c02c2013611014191090b00f80c01006502160b641801100b2485400303000e40b0710410090246c551a10300780401c075549c40d002c455100c0320000342110b5855044118058420006d04040b4108010703451f0314070044803040c40320380142e42d00c040c04003039014001e2420b000703048201c4080c8201d05082d02d00130350700c0c000d441603e84500f002c49060341e070034149a00a03582c080c01400990304666070f642000c610100801c0d00c00c0d0f020310b090a403201654940f5104a90580d04000c28003030074450900d00b444400c2c284003005006140c114009000300b04400c1000e903008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 619837922 1250 619836672 619836703
    0x70311100207140f0601030201021b12030f0c07060e0d1410140612030c1b130501060518030313140f03010e01061a07120f050421031107030302060411060c 68
    0x9200460204500d0304d40c40000002d490b0f00182c00500040c1e0340441d240c108241d2000c0030440c031184140002d82c45290108404c8080d01c4006503a07440d40c15050050218010f4140c203840c40d560742c035a000e0f00c00d000b1801c035107640007001c040c07043c0000c2d400c00b0140311007840d0a000c9852501c9070600280031602c40942107813942400c0800c101541c60305400125855400b0000b56060026048140f5552403641605e0415145e0b40310042210391900e880c4e0040d24400050305011650303450030041c0403a80600d40300142c02600c20070f02115420000222807905254034000c8003164506610104c00810f1402c4140c2e12901d024412103156409000e400400507400000103255490650391a8007070b820101401101c2c213041c054440451215415148040a41d041c000d50381a20180105d69a01c65900000034040e01c4900c01441d176000440081c82041c80b9440790082d128510f02c085680301514400200140c0c0540c00081c005142444a00052000508401d050006200c0b54905040c0c6075541c0050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 619839172 1250 619837922 619837943
    0x1407090509060109030c031203140f0a0605010c02012f030a270e0c0c03130303020d0e121011160503030712050609071815020d0801090b0105070311100207 68
    0x1500d400241c5540184090038020f0f00a032455a400c80c0f064040d10028100c0d1a10480c40042280642c0101540c85190740701044ca9207480d40d4480e001540640d5186456480c14a0109495003d0f0079064001c903016114150506c080c070103070790814003041ca040115040401c110840003441000505245000341d00e8501e0a0a801d03952007610402c2c1c034400700005c8076240000c104001c1403054003500300d42c5030460190b884440d640e607203246d072150285200c044d0710030401c00000d055021503640070104940d1ba680d6998901c800402c03901500c044000145c0360401c240180042205922007507260580c06000c41c100002010b40c24885400c0c1c00099a0a400000410080c9079120000740d8800c41140320403c9503007800c50200c0c9000c03400510140c00d0007085504202c00c042d002070100001c0c840c001c001d040c12006001c0c025220b00b00b118401011480c0b0130004144c940075801a8008180180d66080c1030801c2078a0454a41d040f80c80b090742c49000d140300c0340c0c0a15103030380010078520f4004c845140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 619840422 1250 619839172 619839179
    0x120c0302011b140307020304030b0c07030e0121150510020102040807060903050606100c02130f0b09040b160504080f0318010e090c030c0c07170c1002031903140709 72
    0xd0964103103a450002440c2c48079520701495070002e15080c0034a0150034181d8881d9250f0750103a1440c0702d1a04050000c43d02541040080c001510040204038880c2d641d000030500000c0054680c03404a00038403010703280c1590403040701c162650040d01c038003640101c0c10905075520b10208480d991b103140f5410050b50001004d012036a402c100f108000e01203403a2550410b0318540745c2944075900642001e00c50960307103204092061080d08078400d9070380c000309141640a1a06840b1000301011100114a181040000c49051411080321446aa002010441e10b0f43d105c00a4a49184000091a06002e030600011503c814200102c0c0c3c0301d003400c54011540c982075901107802201e800500f090400c92120302c025020388a0819a54200d0310020046882e030700e9160160000e07000d96961082c05101d00400040c070030001035940d034880040344040d9110750100784103201d4101d50068031840584d00c104000c2c1c5900390f461030080020301461900184003074584a5852a047c802d448000c0041c1240703a090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 619841672 1250 619840422 619840427
    0x27031c020d05090307120503060a1508010806011d0c071712061903050c010e06090301020705030310080c060a08041505130312020903190c21050705041e050a09120c03 73
    0x603600301d43d0308002582800310a64401009010f804045c804005d4044045074064440c6510540640394900020140310b01c88540100003140900c6400c100c0d2140c03100004010203560741c030f02c0716280b801102e040c9598030351070340701031a90015504960f001e8801c441c0f02d080c0d1350000c0140410901210700078031305040c0541000041e40c0c0c9131f440795456500c5800c08000150001071540c01d8040c00382045190b011000001a059000d8618000c3e01540005043d00c02c005001c0000c1d442504001c0b00100400d0711241481c0c0c0d1619070007002508160104a036200d0f03503004520f6a54420722440700a0100510404503106559090320b1900b480c2c507030201c421b402c050304840f200d2172070300c4248000c40c1060441070000c1d0b0345140c40c05103070f0021141311a04009015141c0700d202e0140c851700421400d03601400f04419a0181040c0c0182e801d4004d40341d01246500d40380c01340f1b901d58401012580c405000c04915130004050103040c02e01c05c00d590342090000a07074442d040319141c3c802c945401c06008a0303410702 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 619842922 1250 619841672 619841681
    0x907060522080a140d09030209060d050d09080f0c10050318070314151012030c1b03051005011203051c110a030c0305040b010b21011401031427031c020d 67
    0x1040c1e010b4000040d1007407446e5104d806141100c1e0112030300402c984030b00e000b081c0d060002e00b40182c080e00030010041d001c0c5070003616803011500500704584806040e18819900c031141800c0d11395200042e41540d0707000e05d01c10b5001c1c54001039107140c00c05016008042031454140180d108482c170200c9410f602c1c0014000340420701121801c00300900c901d2504e22601b039102a864003c006184514031000c0050512a00b19444100c9d0b12030315005200d0340740c03030504cad01021407407100302d0300d51183e00030345c01300000340f03025080c12241d031540701b01800d60f22560103544940014200c1100b15480794030781c103412010340c0203040f0b01d4101a080c0720780d251000040141502c0701d18a05000740741c208428400000c03580601e85044070b1162540b50f440c0c0300da1f00d03210041360358400d5000c44140c809030004517050308403d5130301182c000262003c200e4114a00c1031005903040490714140f841000c10202e0b440d40d808845210900c0b80c4000a0300c2c5000e24480a1600c2c07401a55001c1c0d101d1507011035481901d5095108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 619844172 1250 619842922 619842953
    0xa08070f0507050d03110903061821030601030519090c0509010f06080a0e07080d080a0c030612123b01020a02090415060e010815010e0907060522080a 66
    0x205030389054443e40700c440d518060b1510b08030401d0307030390710b0384201c6103404c1c0c02500c00b151001000c0d2541420032500d1070050803012000d0302c1d500e02950400e141010003184042020524101007507095603143d000640080c00c005280c00304201d4082d5105220305800d21070704070fa4070700c00e41c00600b00c24108014420f00c80c00c1600000d200700d500070b0702130001a8200c04038a900c61500c043c0031406400c3d8030744a60600c900d03640204120b1180e110340b0b6074460740003150382c2d2041650074410480c4269800c0101d096925a2181001103200b140c40e52020a100040050001113607040010306c20641c0a500325075201c1d03000b11540c2501e00100d800542050240c01000c09000900c02070401241035000199070b010043c00080c1040c40708090b06182440310341058008000c0e2040021543da1740762003103034950520582d059040300c0303070074004070b000c007d10080c441c000c4c08481e0050a0707440c01e1040a4890390702c0600e42c104141000100c0704c6000340380030b0000025040d0303440070301059507040ca0441c489d07603103852 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 619845422 1250 619844172 619844177
    0xc090e0f0102040b040b030c07020604030c0905090a02010c0318080322050d1a100902030103081207030510170c060408010b0312070305251421130b030601140a08070f 73
    0x100403c62084c1d1030050703a0998110011701035a0b030300c8480c00301c035080c4600728009402071000304000040c030070309603998400c450480c5024001d035654540c0e0203440fa00000b000a0100c1c6030510050b001c6440344c421102141502e014104420b52108400c510b541c01c10f0240c2e0346280014081ca070b00e14250051714038001c0c0000da031401d215461a5407600000e062602138103400340b100000140b00c08910b0701c0458001e01600c001150b0303958403410145c0e540d43c8006205000250f426002c0b0f17042c01d01c280f298034420000140c1c4e4690440c10715034407070025103074501c0360803180c402c1c0034400140e80c0ea010003c00c01482d100000258840c4070006160070000d540041d02e007104418044400881d8000e01242e9004e0ba02c1c000030140d05a0003000b182ea0b5040382000900f4042d05056041e00b41d43d000a211141d0303080c82c1c19080110f01c44079039403c096200e4401c060210700c505100c100408a20800034680206050400404c040e200042d0340303403241c202a200c0e8001405800a00050603046020002d0450952 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 619846672 1250 619845422 619845427
    0xb010e04060b12090a1a1b18040203150301061502010c020f0705060a0314040609020307210618050a0803040309050405060d0b0403140f0c0f01021201031407030c090e0f0102 76
    0x40d0b07070403541e07010341010041c0e61142000003c42c3d00300240b224060b5260b0006829041c01d0744090b0304217005104481540d40b9003031141401c021040b85805a65250130b13480380c070294186480041c40301a400150130742105100070780d6000c130365940c2800b0300d07409004103040c0008605014000207094800d05181c0800707642143c0300301c0d104100d02003512010b652060720070f29514a100b190440080042505406140c003080c014402002040e41003240864000c0303048512076500e440c507007040c1d100540200c51450020f40c1841c000201300d03412101c0c0c850640400c501c144034590321901d00b0106801d400311000d650010412003091303001741e0100d0180c5410744082040d4500b09000c550b2100c01c0060242c1080a04000941018032404041440d418102201d81d12584c0c6074019810940000c038031301000d4020703a0f03120010154144269140300c120480c0c101126480c5803104a00d1034030020580d001e0380103092010000c20319400c00e4800608280c0710006892509011135414446124103004159004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 619847922 1250 619846672 619846679
    0x9070503060a15051c0c350408070f0302030307020f0a0f03120b0a0b130806040b1b0708030709140102060709060e01051c090507170703031407020901090b010e0406 72
    0x702506801030783c850070201c03110900ca1640943d05400b074514500c4a03d500f4802c42d01e0b41c2c48150304003401307010340e40d2030b48000503d0720301c032402c040310444151058081d020200c01503844102c00c0d90300e404c58003d5403043c1c500740003501c070400350580c03024060300541e10000030702498560400078044c41e40700300c0015000c20200e03039491100354405000c014040100a41c2445d10030303480703036020304c0c599000240818405582c83c800c0000d0340d08400e5015589103001c7c500011401c101040c0c291169a21540d21181c90b40d86a4038550000418080211212428032603440007c6040f001540108199154965141e1414401307002000300c210907581150801000d011606410041003426680c55062a0a4010254004035694095100341000b5003d11004c12a00307030060380d0290070740300c0c020317001c2c0e80b4030310f031513210041501801d40d02c0c40000e40d201c4a01000070078426280c100c81d050050081500c0c0070ba00b600040c0c15280280c21a494540c1e0381e1249002960304800628212001941e040c86114034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 619849172 1250 619847922 619847929
    0x8040e0a0c050f0f0d060303081b12060418060906050f0c0c0a11010c0b0103060207050606010c05030f0901030902040906270b0f070e120102091005160327060c020907050306 76
    0x18040000da4500d001240142c681390000d420f0341e40450b14032204100302503482c140140442002e68480d910450701604418003007a090003101d0280314100401710180d150002400020283d84142c3d5003c091540c9400002034201e00035401141d020340c0001c28a070600f2007095042c540f015110305884d4800301711071105c072900800e80b05181d40e0407011001c00055210016503c0c41c4071140000c0410040344004030401090768050260b5600130401c452084c4d0310303180150b41c1c0c001080f02c09011a070040c05003032440c1500e280140346811041c500800c0d41446540840c0907100301c8030040b42d03425140c8807114112180180c3c00c0c01d0442003594088032400c0191103001c211740014104103800e0075500b0001c0c04007401021020b01d80e15000c0d01011b1448a40340701c8500035082000031034440c2ca1307601c0071004210f20410568800b8003d55200e46291180355070280c1d503520f041e10920f1f044901e001850703880140305010741d1000305503a840b45554050039104000581400601c054140042401030085503103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 619850422 1250 619849172 619849177
    0x10021c0302031f050906041e24060906080c07050118052b090b03060301110307080a0e122205030d0909061e060c0302120301090905190308160c0c0308040e0a0c05 71
    0x6505940025080b50f07230342c0701c1c40340d2031001000507803200382004100045405440f240c0e50044141e51220084261212800c40c3c1c0301202e03204060000d003801c40807034203219602006010f0180729900010b034480d03200086090381e00071420103490f03d0708540c404200c5403600b8a0460103080d0041410f2880a07030610028221060a000740014040c0210014001352003d41c4543d552007655007c0da0349916007100000d0203040d04a484980407030034500710301149040043d4140c80c0c2e1708242c0b210ba0402035001c40341d480b200100401540c2c03000c03103030310b000545c2e850902102640c00e001d41d9450065604040000c01a075030384d80e12108020304d2041000601403030b5000c1e0780048d2031045c40e00340d181800c2400c00702c0c980300700e032034529072104000800043c000444e940f01a65052007981550600b0b0780304107000000111104019020410800000d00709000c001c6909030300c0005820001c100d807204d0345030310402c60680c1e0801c4075410400103080c08800c688201c001d034010040d00d018041d41c500320000a0150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 619851672 1250 619850422 619850431
    0x105040b130503070308070212031c23010b0d1d0d0302130308120703060b07030c1704091103010509010b0a02031804090203010e0706120b03060610021c0302031f0509 73
    0x111020503808000001c940380300300100303001002c0b43c0310395440b420701c525184d1203644128841e0401c8194100040004416603070f03041500c0c440a00007150002c40d80c406000c3c0c09803d105054080c182404031458005869400f81000340c1e900e6840e1440001400e04030341421600400d055440519850032681c000b64094250100746405a1210740094055100d0042034100800003100030461290641e0184000380c45844265014040c05a84800d890418499000c02500103000710041a0104001594880300c407821089601e141a0380d07401d0403800c036003207003204402805000004011529040e280340c0c0c0984682410245012101c030310281d580e00c03415210006450014015142c181c2e00c951200019a170050005e200e00e41c0c81240051b181c1d17a090003424003051802c070041c6610401413140c0421034102400070708454032050201f00300100c80324400130071440f412500204c5000703c04804c0c0c1e101c1d800390b00c015841e400c20014134100800c4c40780080083d282d010000b04003a42c3c3c0c4003000c0703400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 619852922 1250 619851672 619851689
    0x6050409020a03020d03180314010c080c0904110405030f06011418180c040c03050f100b0403060e0f0312070909050f1314010c090e060a120b09150f160806010504 71
    0x400300d41c5010b45411145401f04040500c52460000a20156581c059590b00109000700211a4111000d4620b90340656241c4100301c42402612510306041e03200b923a0304402007428a06144e42c640000340f401950201c040d049070095001006441b10459015840a50403180f05001c0c4c80200c0350300c4000100285109440c0401c07401d102c081307401c103001440602c1c9001c2d205110304007a5140190152a058440b2003030460200c00113045005000201c5090f1508003001c24686486c0d601c4600141c212000c800a160041c4041c0b080865030820081028030306209002034245030a14015080409035803002001f14280720401c42d10800041e03040340c0c0819602c2001c80d00c1405420240e09080303806086802d958070380082101f0f0301c0c2e00100b800c0d007150a41160001c062340c483e400e0103041c50880c403c004980d03d00c4c80c5484d000035100300420390700c580603008440010042c00b0030301920490a40744030404013000028481464684681420001c0080c04c2c05012070400f140000c00c9445503200d00c100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 619854172 1250 619852922 619852939
    0x3111507030c030c02060f0414220207060212041a0106020d120c050c1b0427060903110a080901030b06090312090102120c03090f09010807091109030102030403020d0306050409020a0302 81
    0x805000c0d5201300c1605401504a64440030740f56642c2c540341d40309009240c6003044940d0030303111a1038000400c142c0d051180d00140500f01410519101a400140d0201e58403502807191488070b00b03403604054401c60041031004051103c0c04800150700030181c100508640080000210f6035401c50505115a00d8540c00042c54560780d0b03a00300d03024000c0680c2e00945007d050254868007808140303101400d4806c5408000c00455989030301400c0c00442d1756181c2014403a8601c2010071040c2d40161049800b038100701101501d80c0364014107160f0802c01c1114000000300b02ca84c119603044c8154001041c0c2a200e0a203800c0300740300041c0e919145511012002900002e840445074401c0c0300d880c81c0f80c0000e400e0380c4d172200b80e204080740c4c40b50004c22507039002e995500c1421247e0310340402028120303850400a0600305003401e028030081c1444482c4115241000c12207040151024401075101700d00942c00341802540c5244000c080e51003030f5000d14459420b160801e40583d40382200041100c4d4122003049 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 619855422 1250 619854172 619854197
    0x40201030b03060f0f100302030a080309120a0f080a09080342100309034802040b2b0606030c030b0a05071e050d240311150703 56
    0x30040d0280c00c00c215054007601c024403100c00b903000c1070305000710342c000481c1c8401d58031403044210901d26840069031503840f0300e24210108007210019a0011001020b441c03290500d441220f0b9141d0000810000007506a2001d03840e881d4040f40e03090304081d4800051007201290740300c070f03039440c0005020810005881301c04840c108513980b001c21811480d0702c002880d0029041d11410f540d460f1000c1440c0901200b18404070709502ca071040d80b1074160b060711503604416a521008110003a9145404100c01c02d00001030081d50141c84004284c0e0b04103884e0043c661841c1c414042a00c0007000442d00a00105220168034000540c4040580940c1044006003880354205040540110340c0090941c510740300020040c0b00310741210512a01009806011075119a041144c201c10ba0b1700301907110106003400d407000544101d000302810302c03050f0004580600200c4c60710003248030b40d90442c403070703981007401c104104038416850b0007508030212040301c411b00108484407524810400300070b040141558044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 619856672 1250 619855422 619855427
    0x2010509030a0213020705010f1401060f05040f03080c01150308191e17090c0306180a12020115060c0506070318080301091505040c0e012a110f0108040b0609040201 72
    0xc84550343c004084084010105000300d0081d03100c1a070542e00c950a00080c0449030400e4010028024014012210142c1c0307065400c440010201c0c0035101084001c100000e00c109022001c00c02130b501440b03115540e5400d4841c00707400c5a40389a805420300c1c0145000b040401c41001c15a2112210403d40851030728081c0f00848950068802403803c1110700c00b8032208055100c02803c28001d82402602c0c10703500c07000e00841d40c2d01c40c0c0c1c801582d80341e804100011207000280114106514522003105c0390380c440da81d60105c01c0203220790700c600107030343d16140200c41e9a50410408010003182c140010803111548850fa02c80b1307402803400007070585600800e0821119210b00304e9820ba00683c0d080e0b141d584500c2d201c809008851402104c031442c0d1100030515103001d04c19540182026100c080c020445d040055070005000040403184c410b18010080c41113130942c00c0d80400703911400d0956070059090302004012451000c40d0340c1081140010000020710a1350740a400c10700c00c4541071200c2d91070340b004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 619857922 1250 619856672 619856683
    0x115060f08191d0f03030f07110a020d150f0b011b0519052a18010b070308071115010f0e0907060c020f040207080903011b020d18080a050307050105130309030201050903 74
    0xf40101c1e100f1101d07010103160b00840a540190611401e401090310f54000031580f000100344514102d411075035a0800618004070422103452203049030030091041a40c03408100c403185d1040a034069200d4030515055039001c0d190140d205281041b5071a035218686071b1554495030b11400c2a51307411348591032420301004225a800c40100750104180c10403d003042c000c80103c28000329405050030380d80c06424451244285410780b80c0e030295141c11300504e8ac40850f2154000340144081c00401a404080030200780032010307a03070038040c0c0800510352410710281c1107a4171a60014002c2d00081c0b0038841d801c800410300307004a07080ea15040720380010324000102c42002c40d00760030394044c0c40060000c041201a401800401504070000c0003548a012000c3d10f041c59080301400050308011203082240740250b040d130f070f80d0340f1000038100c1d20241c82d038200521704400f010055601e170f072002c110721041000034002d25030701068043d40e0143c3e0040558014100f40603500000b41484000b141180703443e2020450b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 619859172 1250 619857922 619857971
    0x6160309020d0b19060f03030e060306040605100e12010203090a02090912040905041209030c09200a031b020714060a0215010b0901020c0102120f07050f0115060f0819 73
    0x1404407041c113100c8041e04141c02004074075000c903030030440c0c00130384081c401e26158126038244d1210504144110100324856000a00842c2c0c40355640402003800d03240d5500b40300c040b458545800300da40304180300f00001e80c1700700141c82c070302680100b003003010a14001c9040300850380e0640d108111070710380311403050800100199400140700007040009a003061034000c2802240590300c4014030407064081200c0ca110349020240035804100002c01920a50703038000098a04000850706845006d13000b00c1c080c030340c0684150000240c4503035064046200300103003541072030954001403003810b00d0161103a42e407085000348944220702c0481d80d1002c4500a2100c081d83d400e850402500c507607160044a07001e60001a0326600500c01c21041380c03034550001070400000e20000782c00300d0401220408034101d0760700c4510110381c2c5001d011590b29610b03409020351161107000d5150007188a00b0400010000010350700e4801c00c01c581c2d0b07030a00042c0c5031044070040000100060104480540324001c556003d449403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 619860422 1250 619859172 619859183
    0x106090e07051e270f060114190e03011d03070b1303080112020a030609030f080c0a020a02040908090307060507062003071101180302010f0e0705060a0f0207181a0306160309020d 78
    0x4104250b00b00300f904500c41e82090305c0f6542155032302e2074414500d01030903000c148c00d150500e0040c080c40d0301800550f0300c007210040002c80e5000f142c1c92002000c0c50b030091b00d00710503030010640c00e00704224521403645c000074405d80140076103401e80300202000018410765040b038002d40d001c0002d5490f40400007001d50307005581806a040c040c03030020b005828010070440040c1207400400e8410a00804691011b1816802041040342d59001c200c000c1080070720403605000b003080092810b071424000240100380585882d9103412490421030103407482e080c07510700b0b6407001041d20f400703030310400007070341c0c1c2150491a0070707500805031004890062040194900c0704106200301c600c201941500044a12581ca41003841a00c2c404e00f00c00c1c1e6601100d0181641c0400c1c203022003404c2e5440303680c0540140c0218811224030640d81e40e441000300170300d160720030302c1203444030441c414010302d100003485502400c2c4c0081c130091411207406040190b03291840d204168680c40720348113540d595a4841906500078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 619861672 1250 619860422 619860499
    0x60c030c201f08060301020405010905060f041d01080d02010b06031f05040e1b0d0803131716030e010206060a0902070c080f070501020f0f0307030e120106090e07051e 73
    0x1d00b41d00702c0400c401d000390070010300d003e0006135003400c06009a0781240c04c10b1b1a454845800c000410025402c08520440300305801d20001030b200b00701596403440c2509440600031036504200956040103400c912040c06d681c1824004400c5032181e0341125070191b02e052180114140c0071060221403032080d840076a2003820107401c444841e0003c0f485440c2246074140c2c42e112410080244030544061f40c4002d0015001800025200340e514500e80c18101c0c455201c442d441203c448200b40160090000b4501d1128030340002c03410540c0003400c2540d5003100b40020840f6280800004200f80340602401410a4000ca00e40080150202e0600060102c9005840c2916054140c83c0c2c0c0d180224850180148125004090231000101d400c100843d106400b462625650391020340321a035002c03080c0b54100f240c08c0e015501501080c450078004d00714011003c0741135100181c01c1c52a01c1d4458000e00e1181c0b11034001a1816074000008003140003041da00101240100d2041c030180c0105c2135454481c05081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 619862922 1250 619861672 619861699
    0xc0a05010b0f04090503040614070c0602150c090901061209060203192012100806240102030a051c06050d0c05010912050c0108040c0906030b10060c030c20 68
    0x190080074a02200b55200c2078070700840300c108010313103904081c06441c40d08100000d0254034822103030044240c4101c3c016030f181440c150b442030002882c0340c0c0036a00680000400d0700c2c2514002c030744260084902d00035a8101008400043c161400612507041886800b4000c040c101c41140c0005661f260410301c01c648174500600c04031558000c4401101e0460b00c0c040810903040c0a080d000551103400c003a220b410158500711200c80004050540404030a55020000f24601d081060900c03401c00b0003401c000b50a9802c81c04e003000414070750310b1030542d003061046425083c0e01c00291020101c01d03002004800b068515004001d0810350030090f04180303141111001d11101254450846500303030b03180115156942d2007501d5000008400070400c1c3c03c600308400c07030f81d0300c118009a0000d00581250000b039039107640700402c41302250300844100d89035504102d03200c20506418801040309041680d01001c469400130100b1041040007098404511446010074520140803080319001402031682001d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 619864172 1250 619862922 619862933
    0xb0c18010c140d05090a05040510030803040503190e0306010509060f01031a0603070c140d0507080c011b110106170307080a02070f0605070210090b090f041b030915061d06010201020c0a 81
    0x1117454054041e050030705000943d400c0611030680300d002490b222106181c115901d01c82c0c6640003400a948500c014000c5020342c00324141104031203107154880641c02c0d04910241814081c1c141d000310b21964464040001603102d81121040000003460002446070400d04220308100b600000346800c0a8040b017002003003a00b100b405151140a00b145480311500c210400ba0345004602d40307200010401d01050b03001910b840094480c0d10042c600100340036841003142c115600000c0943c0c2c001810380c614200c1620000c2c0b04a078041c1103c1d6501c1c2d012400d4000450b540c82c0305e0500700410700400041c4071900ea038824480b4402174600c190344515465510f4000070000c1e04803500580c858a081034003908910b0040e05118100d501d1000140d0900c8090b408001c1c00f480300d29441e0f90402c2c1c98441c0c6012640950781c00c40c03984070b61034030001007407446818018104001e501880040500d41142130103588050b11007100340c0f05103416042410303038420700101c1c06402102c0c0700a94074401d01c01408100403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 619865422 1250 619864172 619864177
    0x1c11060a031808030912190507050a060510180b0607120207150207090605090421050d0e030703090e0f130221011d0c06120606070c09090b0c18010c140d05 68
    0x80c0041b90141d50046141d01513620441c16500d203400021028070000e0f50080000e403030300c03500600030788100d030190352105002d441d81200c0d24400140c60358001c1c4250a4016081d09503001880000c20008203c0004505144550140584905008410000079a10030030a00f000380c0150801010407510a44000c0e41e610002c0c06000052401c0c0603011401d0b0130020a494452034001190f5800c020309205021019415000c034402040320410180001e190342c0d020701e1011941d8070340203641e2601281402407131164150811090100b00c00d003403280c1d00a0380c415032504480c00c4c004031043c0e1280351001400c0510742000c2e0348840b2990319400b050344141036124040c070080282040d134103031240c10f00c0b0075151101840095444901403001c030383d0383d40e80c032514142d002030b016220b42e2600c0750341e0700d441c1c450031456030200464075120f40da40010059021441a00714500e45102c0e41040b0391540203699000b0855140c81c100f0545880810521000c0503884040d1400a0280c8107856400c0d6002001c65 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 619866672 1250 619865422 619865431
    0xd020a03050f0c0d0302060f0c130b04032a03120e15090301060f06090b13050409050303100b16020d030c0b24031203011a1c0b1c11060a03180803 64
    0x1d0061400100090414a40d0040d4a85d0300d40d000c0d0200d076032001d0490303828401c00352105a10500c103000c2581c1e01955041c90101501c46144c3d11503d96185103000248200b400a82e030312111651180110102c41c03c20581c3c6c181c0f82d0080003084200140042104c809007005040356125000d880b00c0e0400041c02c4005160703c03842500244250354852045a144100d607124800012300300071001c001078030784000507006000741418089582da58400000e010f40340458002d4a00e0742000061010702840e1424400c014424040c0f5141840005804140d14420307003100a0700038904010b03ca002c142c840e03007460020991100041c816402e010b0380c0c0b030724803010a0800003904a0f2805007407029150000748d08507051000540140782da1300707100094940040120640040d103070705115002000c1001d005185e002a14601d00040100440041100180c023402c0c040409440b81000c51011401104252a100c42e0648603941e468119240c1100100300701401c1d090030103018079107a810014020000e5004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 619867922 1250 619866672 619866703
    0x1e011b09090c0e01050316020f0a030801061106060a05060304030e131d0f300d2a12020a2003040611031303290a051b0702010e040b0d020a0305 63
    0x92400c08282583c015004030107040c041041800011a60245040c0e001641d58061055915400d82400c040c0c0c80d2086645048021550180041c005598040741e0400c50800a400500313160500302e000c1282510320b4020503015041c000006001d042c0986100c0061000c058083d1100c3c5039215442401003450302e94002316940800c1085404081c002103616514a07000045d04110b1258480d50480007100144441041220b0112640d110860710182c540c1039032504010510501d42d45842c150941002a448400c54101200c40d03042507106800c440d07072100c114001a40c035000354500b03070b950b860480402100d401c1592403001007000c0c0440507004644040c0ca0340c0c0413401400034403035100d00400a08403020b0360718890400c04100c5070302c500401c004c2c0e81e00842c40105039109400740d00120850303903c0d075125190401d101d102150408040005d00c1c0240106007081034540c0001d10103d844541580300300d03100c428042c4c50f559080d2805105681c010400340c00e0719541d252498441d0110000c820b035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 619869172 1250 619867922 619867931
    0x190e04140a03020a061803200c0d0506040c1205060417040801020c030706110304021005071505010e16030c05090904140d170a05131e0c080f06010f0501021e011b0909 73
    0x818400c0d40054000003a8561192900c4207010700c100d01d110740301000230748000c0c4603000c9100381c1905d80c0e040c50f040042c015000f0b484a441c007407d10728040d07100d5912800010b0325485401c0c01042c008200d41e5001507202c0c07211484d4414001010580e0300554001091030f520000340c010600500200401c005807203004207000c0345d0000d14201c001d40c0401c88019400044d00b10821078040e00c82d81c01014114420b0a5001480042c1844403040350000d03007000c0c0c80c0510b03000c14024030b03464a9410f038842003e13900d0240300881c01084000c10500680c88528021003040340440c08020802d21803090380c103680c2085031901e419005005040030968410302d89508a0f07580030900c031082600425101d242d100e0b0103d0590626030369040007050310390100080f910350500e549000140ca0b000c00c80020038540d0020480301441c0c0c54554104001a4040004009912010011640c022900307828140442400c0d11a607022241c03013034003401c110001c600582c071940204404054010401d00d0664a05040400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 619870422 1250 619869172 619869191
    0xe07091d010303020a0222020304062901020c1012020304080325050a0804020402130f1e1208030402190801022502092a070f03030b190e04140a03020a06 67
    0x465505003804050010303002034035808090300300050303900001c103401e8518407c8040d481c10480200d03042910203c400c2a19948444030b030954460f2801112600740641c108084000c0001070765481d880100c00b8080d05da03103002d4208840c01410a10500115688155900d1600d0315000420350f0080b0742c1a04192080345280c48000c007110245c5540716a00c0c0c40b441d107001c103208815036140d480200220792003502002010103034611580c84070020140c06104110190402d0141408000b424030007004c3d0039044981040720308404105c01d2910342d000138202c2d640342c49030b002080c1c510b10b42c80742d02103c0403450b16001803000341c154000c00c941c2c4000048a101c012815102c09520044c024000e07500c40e030303103101040d160403040005003003c074180c6030f01c65203440300b4100c2c40000c4e8011100907aa40c00141e0b007036005045d014014841e02007402c0303440809030381c040500501240c203280900c030312500d00b0070002010070445041480d6191241021a07807030161900d8000c3d9100c5007a10216807240c240307880304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 619871672 1250 619870422 619870469
    0x1030606080702150c072109050105090a0e13050303010f080d030c0f0e1c0c051507050a0b0405010f0e0307051606050d150f030f05011503031202090a0e0709 69
    0x81d40612043c0d8080c048000f801c54154460600150070707020020300c200302c0180000c51b0590803885001c000c1048020300d01d140600540fa10030303650701141c1405001c0010101ca551045070341e00555208083c05520703520340241240c0140c0108000400702d110020001c100003c1518080c01294026002c5031024524280c0403000d0711209400d03140030450440214500c0f40c018500d400f80c0220140003480c9151401c1454178800040340820b82c3d06514030b0b0010300450070300328084107034510043c045034a4020190b50342d0f076889044144c00390624101da0081001c0040a41100c0341e40c0aa0700c10602600d071194100540303d5111340c40032141d0348140034500c43c0001010100d6070454559032900d50600d41c00b4220040588071540e02400c0302070f20b2040119001113011280c4010b1401819031005803040d034a0302c182110704003001601c014204040130000254081040d0403c203002e03600241c0c5496101011618a900940144e0b042c064081c080003507050748000d802003103484504145a0b80184c00c401c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 619872922 1250 619871672 619871687
    0x1403070f020405060d080a110106081209100e0603160f0201060302152d0a1805060706021b010f05100501090b040306051b071a0609130b0c09130b01030606 68
    0x1409a21101111005880d0640c01a5031114001c1c1c50108170707441c50341d95081c0b0f40d4441c0c018100031403920035040f16140000d10030a0080e110410080c400b00794030581d043e4041c043c034143c03940b0418104c1e10070903c075031062404d0f4586042c040d04090b140e080c20403540c140c08100c2c05030400058000c038a0b014295105021f4030080766000b03001d15500a402c0d080c052641c0d40b1030070030780010b800750b400c0b821000007035000001c0400c242c00f982c0d1034440c0d040c1c80000700071004107100180508602d040910003035a400c404c03a54055440180144e64003103e403010860baa407030050041c1c6a5182400d100c00954480c2c02440c0704445250983d40415298001503402c0701c80d900a091204009000600c00220254000d5400030300c1020017045105007540b803524181e001c684100c8030503801503000c101b03110344408034030f4000d44110341152040c682481ca070039010010700c50141c524002e01004c03541c1851486c1c00c0317510019010b0600c00c80c008900204d00050500c520400e4000792801d0310000c0d40c20703c07917201e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 619874172 1250 619872922 619872937
    0x2030105270601051b06130b070807080f060a090c020c09060409030e060f2809090b130903122a09080a0b060f0a0e07020106090b011b05010f02040b03041403 69
    0x240903010380c842c00b004580c65003001c88001385030080c050720054064020007100f4030078a031142c0c00d040005045e142116031108081c00100c2030188890600c9902a001500c084d400503c5c20003040003a940c2da4001400101164000c0c140741e4034001c80001c1c42030b40840c07407240c808029200080c0740d440d4003052000700c490340d007400f0300004c107031f440c016085141110041080040703001605082c8411044071030b1301d8285500300e0514900c0c180300d40e0400d00741c008541500030b0910354010801d403c02c50010540d88111a480e006400341d94590038000c050043d003541c4500c03c0c40e02000c000002c1500b4045c01c03025187c00b10550031000d44071000007218801c40a407805c3d941c6c0c2c4805440702c0d01481d5114081420080d001551082080460080c203446015801d001851000b441e80c40c581480c0e800030b805c68059400c001c2625080258021450341c0000c0c40400d43d044103120841488000d0904600411030055200c2900d8000240021b140884001547c0220302400c00320310a56020088aa40d9208412 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 619875422 1250 619874172 619874239
    0x41205010b0f270604020c070b070506090715180b0417011b050418060503010c0c120c0c1a0d06030c0608160e06090f0d0305040830031003050f0102030105 68
    0x400840c0c0001e03c4059443d00810f01070f01c05810b00c81c4403200300f804c0880703039008000321000114040301880f000f0000d07507400140010142c6065070804413003004a181d90b9280c0018071008802d622100d1007100042e000500c0310f0981d50385c5541d11041c042040354010342411700c141d820180e20340041602c42d007045034042601e40395646040d181410040603548000441c0204990320880081c1545082c010406002035542d0381490044280ca032001c0022a40c0811008015910100c01c0000e8000a4414281e07140b0f8081094101c03000d02c5207402e5882600403501c507060906000200b04403900c0848403c2ea041601c45403841d5507411202064040203202c0540003448041a00560381000c50003004003d00190040c410b4507402c80220344103418091045001480003d000c005812080c01040c8404ca1403c040c00000900c43d0032522101c507200c4000091541c00201003a15600c1e958401001182e00ca400d0b2000c0340c000c809528002c2d0000d101d0740f805880007a02c1115454000f9450f020b811074030341c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 619876672 1250 619875422 619875469
    0x50c0310060f2105010908070b0a0905100203100515070210050f04050607060e0a0b151008040228092003070f03090837030b06040e0903041205010b0f 66
    0x14080c0002d441240d600f050015000c40a0022032000c1c05514582030140903030710313680c1c1d840b4505902c01c05402060074014518020102c8000b820104800c2000010850b0144c0c40792215400f017286800140e20071030f40308502081e80074110084c0009090000c5c000c132001180e102d0020b800307440320300c035145110854500c2000188100d150603c080c100040c01407900081000031000c03540c1c40c080410348165080303101c100030040425040486d602e6503400503100d11700780c3d441c1032401901ea8800680000c0c481c0c0701c9041c000c4005100358078610030301502c0400d82c03d2900d68541444004021b01401c0c010203410300304594a5284480d01228001c1285580c0d6007204074075500b04030001d00d0b07400c0e001c45000e041080440305280900b0a071070030346180d8101d51080c0200000c04840d843e0f82c102005414503040c103001c00e0740c46c2d45500543c0c04032010b022030140141d8a40010030b05602c1150880381507883d610448800740a01540910b510744000e8400c22241c100417008c02040804441d503086000d59407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 619877922 1250 619876672 619876679
    0xd02010f051c06081605030d02030904020304050a171801020a12080901140a0b010908010b01090b0310090227030601051f031107080c12030907030809011b050c0310060f 74
    0x940042c603000c192500d9110342c02e0a01c10304901030301c10340c0e4441e070003a0b4480c49482030740b038041c0c040c1440203003402c43c0188521a40b081e4003070345070300580341c0052281c0c2d40400000e0510400744482024150312885504660712800c41c0500603411002c0ca20703899111503608010701d54000107203803048170381125503041504d104a10444000b28000c3c15020195222801641124040726900303004456030f0300f001c1144030300c171000101900003d40c40381e003190303042c042100c0090741c10020990036602c2c2019801d980c0c0c0d6a0b42e1000c200d4400946c81840c00610000d01e09d2965906000c0845110104003856030004400d40c1c205541d03941e0038000c543e40702510317903aa6110118000c914004102181c200412a186034001400d00f0b40c00034482558001000500208500000c0c080244a81c50103510f2608609041003059643e51950000400c02000050819266030050440002d034003250900504d01c0032a600d06652907200c90281d032070081c410360b61080c080e04520700650003542c01e0f030a2a0b5004c0f134035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 619879172 1250 619877922 619877927
    0x3031b15050601031407081e0c03040f0f080301091b210209031608010c0201180305041203050f030a090618020f090705040e070302031501050c060411120a050601140d02010f 76
    0x18041d1030b90b4145a600c180242504410300d103280d104444070b48500b03a00f803820303025896500c44840580e80f00e40c60004108180b213100f0500356600103070851070a00d42c2110720700d00309080e1000040007604c03861000c000054a00c58039000000d800a05e403400b8030010b115000296000e0341d0041418954584100c0503243d485055400f914603500018100d0b08081c0640c4841c22a04520790400b1b90186d451303a45084545809005d003510038010301d1006480301c002510000c1c03003400340e8002c3c1c000380c1c01f600303241da8141440f0310181c034601c02e11945456641c1c00c1c0620514010320003444121426403c01c00459504030308035a0001d40d913030300130f4550001d4210700d004010307070480010100b10034420280300103c0c60850303004180d4850b4003540c41c0160303242400a07a000e400c007041c0410504000c410054031004a20100d8a0740d00140d0015110350020745880c000f5500e1010000c0140d8503110341d00e400f40034040d0004045048a044000c0c18034161007110030701c654800729403006404200c103d001d15803041d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 619880422 1250 619879172 619879181
    0x3020705100f0204090903050c15040f0f11040509010e06060913021c05061f0506040501320f070b0a0902031203070e0319120903120f021e0703031b15 66
    0x9905a4018545034940d40d8810855030000c01c2600010b1022441e6507420004100d1101102b60389101c031001482d096440c51050b880c401c10050040f03181c1d0548408101540c0d501c29044080100240b007285842030f907980c000c003110316540c1c9a51003150045400e81c01c1030320015015142d00a0010382081030340d000c0c82005031203958803200c03100c41c4880c1000898024000203010380e1400007a16040180d61800c0b001c1c2c050381d80c014601c105020401001260b81003400c480400d41c0788040303218080c0d142a141c0302702801e40d0300d100341c00300c50004a0004103107641c4005c100440c0300d060748407040c0d1a80d40c83c9808460440034025019842406004000e503140e20107554464481d1509048440c01c0c1b40209041440c40c10316021175204015031541003003d0f1405c4205503504601e00500014515112130241100d1140850140000103610100c46442130014505018484e6011204076000e40c030b91aa17a004184025000244691981c0350099000e070080c00200d0b4001c1044000008803203551350050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 619881672 1250 619880422 619880441
    0x2010e1504290c0f0702280b181c1a07030c02011112040f06060806060906030a02030a021509090c0901140a0c0602160515041b08070315020f0412050d0302070510 71
    0x100c000740030000c0142c1e683d650082d401c1503c800198187d00164040d07214404660300411800c18090168181e01d4008140c0001ea82000726003e45802e4401c014252814a614001419220340e056840c100e01c0840e1030f546000d904c2c0c950b0100031000882c071040742204c141280c0180040c0d4200b01304034070103002c030400e160014010580c0010680e1699141421105a0b511443c03050300310300108a140d00e040f42045500580580c054400c5140750303030000b40c48240c481402440b4115500c1c0c80c5080c800c0c0c100a44e42030800180c00103042d81042840c680207500900d00032800210a805440e80d02070b90034040e1001e140c81612044030f03d203102d94412001c0d40041d001400c03c1ca40c490805000325a0801800c2043d072a0311882038a0f60800341820500094111150031000340e52000410200c400054101f007201d4105181a2016600b0480e6401034441c8512003030b030740d807400316010498030440440c0b0302e6031130310078421100030f809028410340603800b40d2040900250044a1411a02e001c076410100d1134 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 619882922 1250 619881672 619881697
    0x4022803200c1204060c0507060914040e030c10050f13020a0b090310090f0c05010809031602030f0a030906170f01090f09171e03010807060f02010e1504290c 69
    0x70381e0000f03107641c8150055803003400000c0707108003100d081c804107100d40d9001d000c00e4078249805505160001c2a180c64015420f8002ca5480035030103543c4606105039580c0d11003a80594561004540c44070002d03220640d01d1490800168011070744038244d618882c02c507241d0140000c01400c2c540707584030500341c01c084404c0da05070250b0300b699038070b44109118181e40184580c010000d041a0b505000280c80d41c0c0f0f4000a052101c4141445581140003040c3d842d048124403041c2405106c07071001c641070200071904040e03075204003600c40e004c00d0b40180d10380c0e003034500a81d2500355900d440081c4a00000c0140d0b2a03681202c000d00041c4160000c80e0841e40d0742c0301030f00b030010400c82c2d502da40d50111034243d01060ba091943c0886ca150740801c9881000b07514005606034581103505180b54192250b4140c8240c0341403100000101880500079004050b52070640000e850100c440140550907038102103604480180035180040646a004006046000c03100d042c0e806103955030b02384000c00c552211104464 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 619884172 1250 619882922 619882933
    0x306090a1a151804150501230a0905101701020901090509060102190b150301110f1e0304060b150328060314070501030b090c0706021804022803200c 65
    0x1c00e40f180d41003080a03d650f0803502c80185481d0820100c0d1444035a10f1160307450400b401002502d00c031508816040c6545000c0c44c0c884240722001880040301640080015803d0900308608510002c6c0c0c00c0c0219100110b0b0f5103440c0e1100c400080c200c2c0f1400c801c880c0030a00858041c010742c18140d0340740d94084010b0048600101d43c0b2041c00000d078070174040031550482202c041003034984490820481c0c0000034bc000f0300c40012138550340b504900a808004403401404034116441c03a2900390380c2c40d1041c00132081d841d0b4038189824000050070072801d2441c061211800340d82d4103c0c0d5804126481580f0926028103840c4050041ca00070001c074614440f911a11400f0210224541d070350203403c1181c68400500310546000c0026098418080c0d5162240c150402000030205600040f07810042c0e00c5a0010303510603039080000c40c40305140302c0950300a4804188400b4402103010f00441568200c6409150543d80440880507208101e8511620510a00b9000300f450310040142503400741280c113403407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 619885422 1250 619884172 619884211
    0x4030f1112011406030d0f1d030c1207210f02010309020f04020d0905070b071515030c08010212090c0109090506060702041b0801080304062f07090b0306090a1a 70
    0x5096980b910480c3c05680901c00500c401440c0402c844885a40d040c01c00c00c07164030a00c072006d00041c4c86184c0d40318000d00f00382403642e100d65042c80b81030701001c0300038010303024006810f6240b69900e07528020b54040f155001c800c1c603040c00f412407440c21920b50052640011001650044001d012104422a00094001c0b030808155849001400408001c2007001584060740e01300710f85801e070340e0740c4030f005c0c41001008003001041d0064580301a40a00d04004a0700b40c2c52a4203030107001013a5440a0f040c403801c040701041e886010340040c42200049022001c0c0ba032070780c41141d611485080f4407039021440b10f00c2c0400c04a005500590741c030000052825042c03089540103d01680e2403c0c11001d0171644442030030540e00d4004c00c08a0241500d440214140340c140b01000c1c00001994070600800d45070842c11050f0260303c6036210000004c8002550310321652504c44401074075011350380d2486802440e000901a00f00003030860310b01074004000349181c1d00000c0c014901c400c00074003c5c10b000301944a100303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 619886672 1250 619885422 619885459
    0x160e13021f1808100b19031e0c0914090705030303160302040512010203163f1523181003140a060f0b0112020a0306271104030f11 57
    0x402c01400350030060510141200007a42c100d0304151181c5200f84081c2d012284103c00c65401c21301503d6024645600070300030540d410020045a41c40107203d0b80441030042440b10356500040508005010091160784078070001c03e0302c801e6036000303154140d841030001904004442c0ea081c01da0007000e00b00140b07807680307841c00306448a8428442003104e82d00041404912807807030068581010781c510385000301d07985510a501040ca0070a958041c41042a04c1d90031850214080f42c001a5083c2d1104201c008102900010140d14905c217220000b24441c83c150b400400a848a1400080050100c0012040343c01401c4a0100107803030210900c0e40410701000040402d01b0000300c0d503010f40001d0030104460301d040b50668038008c0e00c0e9072449040001507541a60807907841c0206242d08400562145002a02100200110342c0700302c64281c500d00940100291840107524212040d100a00c80555940c004010744c0c401d030b10005000c442404011004146001c0d005494030070001e140114900101454 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 619887922 1250 619886672 619886717
    0x21015080106081606110304060c02040b0d05150112081b030f03040501051f140906033a020105090303130303060302090a05100f060e12010e160e13021f 67
    0x12200942c0600c070040305441300c00845000038421841d0012004010078121900ea0007107100d80c13814030940034401307000c40daa2a04030361404000600301c1c5401e210750b82401a0358412101240380480202e000210f034280071040700381d070016008641c19141501e0031103442000385524820880c0ca0200f0710102002d040c01ca001036024500400001c1800e003040c4149042c00459600660501d1146180400c6544040e1503040f0107200102c038001001d648074808642040309999207006008008c0b00c0e0780d03c01c4442e03090403180d0051501c01c5050010003501044e4225081a21000547d80c002e100003411441e1010950f60454030038640800d40c0750b540c0e40480c840040640b2600c20160f00c0d00100032804c00c0308188274008040d1455804141484d01001130b0081e104c000001d0300944201c0349810500d1401d400404400c00020304840299844200b10507074152a80544501181c8201c086917001855165500c01243c0007080781c40100305400b2800c5140b803002c0c0041007400030f010540c40c3c01200c4600c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 619889172 1250 619887922 619887929
    0xd020301060513050a1a09130f0c03110a0c02090c07201f0f030b061c09020111010e06010e18010c0e03100203010f0306090c030f0804050907050a021015080106 70
    0x403000d4950b003c0038003d20003101d5a4225034040c0032688010010030320720700110b1845000b942680d03943c1c4c061380004102c407d82d0b8042c2515400781411426448401a54003c07403052096503020440c2d0340d0010381c0e410741c0340b15840b0401c000074503004100001d032400f41d540c503030019004a2071610f8512199640d558005900c040710003111500005840346050507440603600d420070200d0074103022010000600b18446003a1440101540ca5480303007161f8031102c04840d2041c01016884010b110300b0184400600204503080740043c80d00b08004880400500888410401440103410940e003021403054618100034402c001400c1d00203c008a0320740c00b0312800d0041c800c2c9540e075003000f0b000113080c5403900140c80c0d2440d80036403041004000b4070707411190f03090650307601c00004511034401c2d0405100c0282d10f5040075202d05c0c103282c050001c0007030b498014011103100350f644044a560f6003030141d030b01d40104881440960003a44105007040c20741c0c6d0060b5901000380240f1030703486860f0000c039421075481c2e40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 619890422 1250 619889172 619889177
    0x6150f020f01230c191202090306090a0c08070e1f090c0801060f0e1c06092015030411040b0103061203110709051314010221040201110102030c07170d02030106 70
    0x30b480d6050548800240d502a2000c1041864143e0020650100d02d000c4a5000204186d1840b00e4044081540444041d10002403c64040382008044141c6400303440d50300b21703200302d06e000c40010402c1020401c102200c15a040d41085c555420100c0c0b03c0f141e2101e0980c42210302c05440124403030700107114000014140e40d9488240c0d40c1040c2020308842c2030415110b05010004c0e4441406075504601066143e0030300e040e20000c540c8610308207020b86800b41004010040c0c074500c1448840b07600902d055405400c49040009213242141d40c1240e12066501400351f15000140030000d0078036800c00e00f460303541854002001c540da80003504e40c40441003021000031300c4e600101c03042c0060410003070001c1e0041c00010400e904020030400100f000f00c0d00010075030820341d0807001d180b031400c1d4150340213030998100740c8220941250300318101c00b10440d0120301007880d00d200700c052661305100381d030303c200240d0b0340303052074030b0401e48078040b070701804580e1030324000700800c8030310000c5040c0d0010f503001b04490b4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 619891672 1250 619890422 619890461
    0x4060e180c030a0f2d0e1203042901060c0f02040507030f050f06100c0512040605090414041e0f081b06070c0203070306020a030b030115050f0406150f020f01 69
    0x56954280c0d40c62100c120201c1d41003c00c4005a40e22913018404215024002c0c0d103017100c5144582d0f0702405080c0850750690044105e88841c3e464440000d40c0300754840c0d182024030303620b002100070410390740c00413841142244038018042c0300e0168042511150094100c050f00904550000b42598021545a000691904c8141c20f481029000b0683c00080e0350a01d6240c514040c404140600d00301c41074030b803c0109450800c0d00b030000c2441b01c503482014400ca80ea035110b0322240d02070559801100110300640c43c066202c004042039150a41c020780e8401d12403076040c0c1000d05103011124071403505540e95641c22034280d00007a00c050041c040280034903a002c030008007442140c0d007003960050450040c0603000280100590340412002c06580d40060300507204c034405038040f80101105d032085501980b8001c416a008a003159120040390021103400024060720003e0000382ca149210b020b5070400e980580c0d0042071301a004154001d4928412078191000c01c80c00c4c41d003500c0709601041d00e000f025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 619892922 1250 619891672 619891681
    0xf102c1609120203060c0304021f0503040c0905070e04020c010b1c050609030403050d03051e04031808070b0d09080f1201030309050913230115082104060e180c03 71
    0x14000500501110716070b188540d00d6500840d40b00c810040c84155451000400501103540e0801154103007144540400440b00c160007001d042da83c01940d007600c3d103030003000c800101d5081d1409070900c102015034422050203400e4040c00041e40016000c52055500c6001040503911307040504c2c0554070191010304100300803800c019050000141c8000d000b40c200700070510100e10700185801c0226070a1800041955503100c0d0364451000703e0a54000c0c990840052100341548100d0050800d0b03140740b408400e141d95500416610900c610410003c01c100344040504000c0da94043d81100d40602c060a00d8800410680e044507400119540d0200003060010b20a040c0d018550101400064030404401e00701215000450341200c2c2d0001d0401d81e0a0b0f030818035404007819041690407190000340b040b0096035030a4920b5222a0050000c07c0c485ea003603142031310700b0395861a010603605a800d0303880c007428403a00b11f9110003610790850b08044d8a403045a06201c041e21301521411410420035100d040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 619894172 1250 619892922 619892927
    0x1d041518140d02280f031107090b180901021e040f05010e0a0b07020406033806010f0f0e06070c0501020c0118290703030605090f102c16 60
    0x75034990104aa1115041500498002030f03800da800c100b00a0707a05200303080403050750780b07804208801007103a100541c1a00415801c80100b0b0408a000310a80301059200c1d9401d00c125607410400c0d950103005090b20030306c0e2166240718580c000d44d0410026203082c5400810302500c1419a0000303503d8803002408000c4244200c1010f00509800d03e081410301078410f0000b16007031000d00030f14036181e40018110085654070381c00080116880060003407068040d60080700c2d80009601031503441549000001e0856000315012486000140c4440c0480d08440800300e5040c0f6602c0c44840a0281c400b24400d044e64884001d0710b01c00c0d1144440c04011810b141c002400c0481840c043c605001e00101480c85003401d4240b03a0094504003102803150712800c800080464401c412120403500d80040d070202491350681110042c0c039402d5812621680b9100740309044400101d400c85c0b40064140c0c0c0521251101c0064503551050b40801c1100c2002580050000000183c807814040c00d24200100203154 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 619895422 1250 619894172 619894193
    0xe0c090907030203060d06021c1d01060603090b0403050a1701030f11040c1e0306031a06031e0a030f050405100f0305091501150c05070605180603011d041518 69
    0x1281c0307419404d40c01c108000c40c20403071303440e44000e0010b0f40201c0c0102440705005440c903150200741400344403280c01c0390700c501c00f03001030442c0220095090040128003076019020b0685080d40c00320300d800d03050b501c41c0c03002c4415410101080041268200f1541104202d000c4c21038081c40c00341320100c203044000e2030455030710240c2c49000790089040c0605085455040342010401c94a8580311028071002c10908400403c5141c1005000ca000c0311180110301c440e5075001845804164115a8440341400e011301c54501c41c04204503140e8400002100080d100e5000003c0c2c4148900f4020300340303510f03440054a1001e5404440001030201c060300c2c80c81e04e0b41801055000a01900a0301d02038441100c0b10740c60b104140180003004c0000c05880c0c0100f0321030510030084a0f0010190303030310306454500060030f6600c1a00c07000380c0880102820991454074504507812a9010003645142c0640c0039a002801038006109032480c03001d0b4041c5208100e4640508010350703079040c00260840d80703135180001452 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 619896672 1250 619895422 619895431
    0x8040306020903210d05070e2e02010b1c0201030b1509040b09060a03030e0a051906091d07030905011d070303170408120a230a050615090105130e0c0909 67
    0x814a10b501d031004c120001c04031001041c204030b0103d0a030f41e441105452490740301c2c41d038580103020f98041c03059000000e1410315210607000003080225280740000c9003a2100c000004d0361104444452200b00b14044040180711441810082007019200001582c0a4100200805c9040c030015501000385498810f41030a840201c821103214241070340814000c003010301008050007541c0c01c0c40d52131580ea00000030300405000b4444d00e0b210a802c0b4a10090802c82e00c03d0f44085203000002280d00c880c0e81480c001a00f01c0240c000c01e5aa8075103004070041d241600068034195629403190400001d6403050741031442c1c008000304112031039450001c0104102505004d4000b14400a1200160340403044552850158003070740b2840e201c1480840007060418104680007043c031502c030041c03e0303680020078496598450b08020643d5074006100e001f00400c80484601142040907540f507602600c0a00190800a80c0b01e5580d00d89640d401c0b40081d10644151601d094085a10741c180d01d404080b10350700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 619897922 1250 619896672 619896703
    0xb070507090f240311040f06080303070903030908010204060512070302220807060203030402130c27060e030a031e11030d051f0e060d03111905010b03010b0a14060708040306020903 79
    0x103c4e02e1501d0740203107184603044940c8141e8860341c5840e80400d1a4008202400d074040560303035a0309240e403015012076041c0c842100030800a0500240d104010b1098030211036141c1c80300c503d80250340c070b02d04607400300050041d02819406c0c801c2b65014028000581921500113403c01c1c00b0714145406c05240c501183d00c0441154810000c100068070707522030b42c6e045810700e034070040b034840c0c082c9100742c07140c0382d852100100a5088805030242000c84142400131180c045e1104c4261030b02c01c0e403c0c16154850390801134041076449038107002c10385c00b490542020003068503204c0d085815010003241554801c0515a01058945c4c06119603140134034000c05001d01e92221540d81a031400c003980c9030707039030b4020580b502c035040c3c03041e486003410b0103202c0d80c0c42c550740220252100001d803000c084c000e000781c907201035a80d0341c0b03440c81c280120704052044080b8810000c10f600d60880c5448180c0901c00e000e4060070381c100c034060281d400007941b0800a000518403132040962140076140516140500c0b28861000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 619899172 1250 619897922 619897991
    0x507080f0d0b012c0f0307122111030a2102040603140606091e0312030906040b0604050c0d090204020c06040c0e0c190c0201020a0203060702070609090c090b070507090f 74
    0x1240b051168905418000c00c1c1d83c00305c07100c5800e00019041c402558064281000c1c054a640100902101c244003031000b01e0120801079454100100d540445500c00c00084e03a108201c3c046180e0b0140f1008000c803e0401c070700740088680100c681050742c00580c081070200351281408a0115200e00c15590701c00820b58141d4102807071180052488844000c80b18160920f003581045551014418607212400c00701e0110f54904103485881d580b540110360517220a052440801d0f4140307801d024150160713403c4c2c0d082d5824103180540c0e10000303111204080f68010780c02c0100280800041c030035913226901540e10000103601e042400d0051180041104417240b804210310006007501c05503c08060740c040c9040c58000c2e05510060341780540c1c0a03030195051094400704484550b002aa07441070340c8850ba10021415556003214080d1207a40c440b090100d4a0880240285030405000e0015540200219902940d440c01e140048603000b2400e681c1182c1c441e0684001c02110070b10a49078031070100000301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 619900422 1250 619899172 619899227
    0x180212010b090303090909190807030314072a020904110a150c030e040b150d0e010504020d0321050c04150c050c061803030c01020a0305010509040f02010507080f0d0b01 74
    0x1d880b171040008070380c070a014075804541a22410080f007032400700b00880110004009080050b180d1304510800c4001909111120240e41c040702c5000340100a00c0d00d91912040c0c1009103021400c0a60020580303200c030034120840566605803d041c011805074012010b00c1c6524030034031105240c542c02964482c02591514240b0640c807118070001a80c05d0f250055555040c1340004018080d02011954442d03a00815002607075442001015009104c5000b045000d203601d030b0003420b0b0358088901941c010540101100440c2c0501c42100b802d051100752007101e1001c00c10f5600840b0380903183d01ca03200001240501600c1004070100c2282c0c0b001c0d0034480590031569542c2c5540c3c0494031070450051001140c650801c1103215041d420012000b41540d840f411416600e6000350484074950002a007841e00000b16814040500c601540e0041c05407048100e403500155502d910007071080390392083c10813044144820b04405848003150070040455465100300006000c446400303210050046080503c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 619901672 1250 619900422 619900429
    0x1501020f0a08030c0307090312030e100b0f06030406020c0610030203070e160f0e030a03050304060f060b0307113a02030313020f0f0a0b04031703010e0f10180212010b09 74
    0x100d500011300490181d490340c5408085500740c595038001040c00f1040044103100d05d030541c001d18200c00c040300442c0c0d100f256098100d000c1d1003440c2c85c4075030440003110179020b040c01c2c000011035005000b05401343c80c15601409040c40d110048800b0380d501d080300e00040c02145020b2100340014421013003800603505252100411140e4002d00a4003401090203c141c0411b00890440580391743c024140c60700766455050213041a44121421911985002d5050860309058401c150594039400503c5055030344001066401c2e03420224500c1d0070b4461004101c00f01e095102c0158882402c68010841010011000800034a0108801c2007590020310401c00480200d00c103466840340c045941320407422014020855810741c1100454015006510228030100640018000c49100d03d8a070845a01914000074440c0028000c5003129078082c030200e403411407204002034000300340c8035407100d0305a59618621003c036601448a64440d40102e01c80e0240c51300d056005004141c2c9500452602a980000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 619902922 1250 619901672 619901677
    0x120f0f011d010509150a0b0909010b1819050d0f02030609061b0f040f06090602070b0712030203061906021606030e07290a02031c020a0c11181501020f0a08 68
    0x183d502034a0b443c000600c00300070300002141010806010f0084498440141c0388503075220345462401418081c0000520109503402c4840351000f14600949210215080020b01001540b583c0a80008104007142e00d03a10803105000051242e0710090000c5c030710b407050605060000b82545002e80159080081d2001480c13200041a080c2200f41c542e52002d600940046000741e800c0101c2c0513099410104241f80c2100c056801e03034516800b1500c1071551f58400c6641c40c4a00c19000708810701101d81203044030f00940245410860003444249614483c080250100805a10802c0168000c48036007801a8181c00540040d090034a0305201c0d10000e480c44030b42c1c1d02d020784100d062403400c103040f4080050402d03980c0e98102c070140c0c55a603036542582400035980d80081e0403070401804410004415600c161081314400c2c0c00c1a150601004230311b86460b400d135240a00b0542c0c04c40104601c50081909070441e0611a1403407000c414000c900801c002440d02098003070452841c1c1c0008046030100340603200b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 619904172 1250 619902922 619902929
    0xe0a0b0601080f1603020c030d090308090a1a040804080f010b090108070806151c21050910031d0703030302070c05030705130f0b060c011a100c0305070602120f0f011d01 74
    0x40e1300082003e200350880013441545041034480c000401c01c0e9034501038941040302424000c6e52200d05a4907186801c41c2c07140e000480040100c1100c00800501c40600b100c0310354001e029280c0c241c01c1550b074580d0035040c091500c44000c01d07a5507031640c8006a144c5220058050f10f0187d000f40070f0141403030201c03651175030302500b5441812100c540708001c40c1e448089551180000b459081c1c0c02c0c42040c0707002e0220000700c00600300da501001d662200824440c0040d1501100010519600da0189200c20b034001d1006400290408005804034030085c60104509402944240d0700103985911a0071b0004c0342d0511600218829081074104021650390070303881c00c0b900609814001100005100e840c1c0c028401360310715a42101010414103607200b030643c80300c42c009007d640140036200760501084400344d400568807000c170b6654061040400d118401038038049104020040c40e1500d1400800a80b00c402c1328420140c400f40f0381045811030842c0c6000b0300401c0100700042201e0003030640d09294110500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 619905422 1250 619904172 619904191
    0xa090209130f0902060403140d050a0f0516141b0a0b07021e09070305090d0c12050a09050405010f060f05070209192a09050f1f020708010e0a0b0601080f 67
    0x4156042903849540043c00385a40108102e03039642c2e40345041400300c3c081a0925000f0b005001031706c41e01c14060300031151800d026030750781d5032541d07020182600e5030b030010303540c0080090040e00e0013070001d50032030341d00d013031189003140180180f00702c034400002d0000d0b501d40414010440307400100903d55022050b580322590454000c0880d000c01201d0b00700648140f0802d40c3e00290a009103c4010b0301644101e00400140e01580c1150812440503a440c0a5005008140000380c40700b40d80e06611981c050400c0134000d140c0700c06401c0c0d980000a00b611405e0b0484880150106070400801d81c0042102410380c503141020390906041703030001117010000601c0c02054040c1d0504070322800c42103a02424001504c038658001c4070340012070b8603011100c041405c4000c1421140f000c00c1c01d190003041c05002c0e410041c01d031070861102d08486040030541908000540c40791120108000304280503506010450b04020032009005003012010803070090302c0c903810700184134180102080d285480e00d03400b01289 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 619906672 1250 619905422 619905431
    0x1d07032001021c12050606032401090306060e010617090703230d030e0c150d0e240403030605041a090c0f180909151519080303060a09020913 62
    0x500142e0910722100000ca03015100c034500c1d080034030341000402101ca0b500c4e0400700320907501c0d003062000c2071000b80c881000740b884400128140c100c5035800440354200c10700d801d42d40c559880c0d0700d01040c2c0b6896040301070040c00d907030300500820f42e00107011000c1001d103a15080840c2441d001c4a038603500e044c00090036400c085d210b8041031004881d40c05000c0c4440004a511030a510354008004112412440460340034451400800d40f5003805003100300c0365200f01d00b615044c02c0869020080500e8100f0701458051402c0b11240c1c1410205070017600c00d00e000900b50a40342625000301142c07565080359124524000c1e212000d846900d600b080c211400b91200c07081c51f2a1103600c18105e00840508021100000442503007176240d121442c05141802c2d034941c501d6807104c40070390703440f90341002074403449112140004841c48000314180c810080068200740c2d034002c0c1000700b94641c403295004000c02b03500000501a00b030030203a424000403c00781c40c04600b802604030014180444042c129010545c44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 619907922 1250 619906672 619906733
    0xc320102031204080930070b0301050109140f12030304030f0201180b1008160e0a02041d040f0210030b01021902150a0203040b1210120809090408090409061d0703 71
    0x2c0304101d2800d07404006046c1440f0114040c91040d9030000501d400050040140000c0d0500c4d0710802e072410780708141c50718500c80b410000b8200400b01ea01c0307005980725058082c241030503200d481665071041503071805559a40b400e07080c0034100005204c640400c581c9841110807840c9020042c02c0300c070582c0154080100c1d00c41c500c00c40050102500040218041e9505c007480000c0040c0f8100215181c4110600c0036540d14000c0e44200d0099220740703940c1c0840004029071650030081007540c0144201105010904a90041443c0c83e0385450208040b0b565542d8010840d038040003218001102240040840316a40d40865490300036048654400040403840e468001d0091090390090001920340944401100c01242950f50080d11203d0480d5000c44002c95607079404802d8003107041c1c204d8855468031803504140315082d10028000d03503e40000340b00700c038004e0b5503c2c003078148541d000c1c40000c07891286001c0c0c290f0038071070901042c02041d80a40d000b04002050781c0e582c40c02c08000b50314130340400d000303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 619909172 1250 619907922 619907929
    0xc03060e0703090b010e0708040807150c0801050411091c02060f03041b091a0613031401150f03170f070f051b03010e150907050904030f390c3201020312040809 70
    0x461316220cca201d03080400c40c4894540c0200624121103042701e091200764448002c501061103a0f00840d500820b00110322540c0305980301c0303031001c00da2001d0601840c15140103800d107904d400c1560110303040020007802110a0184030440e43c09055801c03002c1022104000d00810f07621450641d2501032040480c210070039035410554080255089190104e5201d15420070a009140049a2151068075000081901c80f03098601c0340039650710040c0d010880314481040b4005410201c01e0b400c241c80100613200c0082c03110803072888018890401000c4c040c81e0a44641f00c10491420b0b118001da141c142d84189210000a0031424444460843c6a090711b03108645410003141d9000950000030000c148405c155115050742e0a24440350340303003191f80c0410104862000642245201050000b08110350381070381d08526001e81d02d00c03980041d80320955580d11499442c51102e402c0850070991000028170104201d01134255400074070240d8039040c400201c05850103000f60001c0e1100401041d005e0b4581c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 619910422 1250 619909172 619909193
    0x904080d020a020a1b150822080702030708010b130506040e0d0903050c06030f160917070603050c03011d04111305150a0e0a0c03060e0703090b010e0708040807 70
    0xd180340070742da590392400001c2e5580100c01011180071030001943c0c0f0390942d0451611003550061501901c0c803010085c01200d603494098058a9000e0100781c00e100d00c41c1c149280040d40d14820b9245030303140c84a500405050a40c2c03940040721690502101c650715581c0c28001080500344020006459240c3d800480c0090120100c009410f2060522107500b054202c4c10520807a031180085494a052000510155000036903070904508003900c0070400c11660079141d40c0d4490310914001e103800e691004200421803585150860541000d48240441075241c06040e034480c0705068400d01e1549403a0b41c0104a5410012103010540c030f000c0402c08010300380c00380c80d000754002040803c08940c0b92180400810341500c0d4110250340780f0001084505100c014401221407541d5001c0305955810030700005090707200e031144209540c0d1341001c22002459451140500c026941c0010200800e24001c0c84240060700240302180708003081100041d0300c501582d034060703030040b10981c0b2054680390000300d08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 619911672 1250 619910422 619910437
    0x601030e150109050117190f05010b181b07050d03050c1b1b0d15110904060b0c0d020f3003070210050a200a02030423010e0108070e090408 61
    0x85000030001400e00752640056041e2007014802103100009440c032150303100d40b907402e100780540208070705002042d86404402340e0301e80688008a951821b00300064940402c5d805002000710415007481403d200c12100329901042c0c0c5490189001c0c103607128255100b900300400001c041d124400145004940340c2a80c40800f0420f503824401c0c40c04420300e5454000da450040c0310720842960300b40ca58606400c4282d00c0035007040d188030624845c8098103010f002000c42800c03810f0410403403c500c0341c4032846048024107803003c007581c45280d034075100c504000f561a00c0c1c804640c1b0102010400c0000841c0e50042c1c0d00003000d8590f850105000461805d01d041211940790001c08820485002d80104d46080100500c0b503041015680e801404070884030f2005801c21042c43c60b2002c04800941080203040c040410f0045909107946c55028480e40c1280050320b91002c0e06072283c0707491307958000004010400b82400c09521500e0b01c800300500d410b070310180d00c2e8030445410010034280b011840454420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 619912922 1250 619911672 619911703
    0x1703070309051b0d080f130f14044d0306030607090806011e0f0801051b0f250f0f0b0601030504150b0415270b0901170102190c060e0c01080601030e 65
    0x301030b642c002d540501541131080c9c0000c0c11480e034480c3d0350b500d018170403501c1c0e010b50041c1200b814a45044d01004801e002e404141150746038803502e02000c002da0b004c4031120780441480341d640c2e28003a824582408800391550003803000c001030a0010003400702c0c407281034650b100d0b41c200f4500300010b07011400c40029030045002e008250804544c0301c074107410061058000044400c1c2c00d84003511a4610f5101d5840310401070703202807002e54134403851400702c100c8810107288100010482d9459860100c074414600310b0314a0400e207440e004100c413031b560706a484402402d0403c15031800f40c544034582404401e0300c1109070b50b43d6030048103d64a56010814800c90082e0190b245034507903504070040c1e8600e0720721f8070f054640751601980209690090500e030031405046540700c0c2e4a000c41c0d50040c0504044111060354007400070203015030307180c00700002001c900e5940d51101c00050a0150803501d96898070354440d000008043c22698020600c41d4208400f843c001403500340d4001c0081c02c0003825000800d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 619914172 1250 619912922 619912957
    0xe0108130f0f050c010f0914010306050909010903020d0f02070510120501030506070e0a0b0f1c02190f0203030403020c060c1014041101090f121703070309051b0d080f 73
    0xd201c0101d00640000d40b10f20700b11810600d51000540d6046070b4140d01400080510382c040c080e001541c1c12040707407104107040200b0a661144005040d6410480f0051600c0e9518080e070740a050381048410380a100504062441c04403008009407110814000e580c05003030040948501c02d44200c021b42c026403080c0b6000c00c01946c4902d041a120a400c0c0e609000194900051024a00e401a000021105141c42007490400d91403a2280b81e5003003008401c111000000c2e07007001c0102503000500700b01d001c0b40009a6401060b2201401c422002d400d08030031548140308220000b600000d141400034400c039412074403600109042490f00012241e0100b003903041c081c801041040500d1140e000d184141c003014240c803410303001110039505510850400c07111200d01088105d200c49112110300d0300520840c8404d4110f04004a1280c2c400e881110000390350701441c5017804418400d003450040c285940343c5410015200140020802c4c0002801e14070000036011207010052044542601d0702041089 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 619915422 1250 619914172 619914203
    0x10918090c0e040b0103020a0b0f07170f040905040c06080c0306123d0510120507030b070c0b090c061c0f0501060906080f01050904111207260c010e010813 68
    0x1034110030280301c220700691003804081000c035403004c191500ac414000000342046940c1d1602001c0307080c106005070314500200505156020107000802c041c000e810800b03d80c504103441c15458002259004038100903145003441070362856030040729000841101c0c5000002c40040c4407038280345070002c3e60804014510064001041c61900b480d06201c034001c0500a11504c44040c20103640003110344c04440403c458040c01000d06241c1360440d0b82c1e002d041100c2d40c8030303141d55848401100a41d205c801080a0300010020020480e420302d80c440d081c0b02c0640f21031540340d03000c00d056006402400c41201c3e00481c02011340365546e41308401c0141c038600c05004d1940d4515001d4503103000340c061000003c403a18000341001c40c8004600381241c0c0094502700f819503403a160b10580c0300c5482c0a9541c040c82030002d60340c0d2004204240c3c0b02074054064000c16407035454010380030354981c04101c45215001a070404403d40c0c1c01171401c0c03071a041d082c02c0000301942c1d85088101c0708048990010300740d02c8461a0381 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 619916672 1250 619915422 619915433
    0x9130f150518012304020910030506010902090f04060e070c030c0605010306022215050901031b0519090803030708061203160308010e090606210a05010b040605010918090c0e04 77
    0x142d480070440001c01c280b5140c4034200442e40c1d030030701c05a1100360201c8003050050030302c012011361100d000d8041146c500d4a80c4d45550a01c0c03000c0c0d20410745580c010034000c05504e0300b0b042d1180c0c0308030f04071740c2009414078104115480c404010076900a0140c5181d6000516020b405149041540404200002d43c3c69203056030094014000100062810400d41030301c1300e20f0030640d04180c40c142d008205458401070001c4600b540b1400c0828105611195001d0b01c480c003100201d40441c400f907c5a0791200d05801807450155401c1014008020050400300680f0034080b0807a0b800021603d030182d0303a0f9580b0700214a000000c62100c0c00d10384400101c1844034007480c210b0594580c030035078500d16280d03a0303444d80786aa80340990b6100e045420070340100d407240c58585480c0d9410011a260404240150700e00c0505040c0303104003e844594440f422010304e4a86407040d40041d04003420080d00c002e00742402190344034600c0c5940b00550780d480101000717104140040c440103144030760455440e441c5c246000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 619917922 1250 619916672 619916701
    0xd0503131a07030b090405152e0612111603020717060a060b09100f02010b040606270e180304090204030609050f1c0e0f0a031a0609130f1505 62
    0x2202c0010385030402442440c41d20f489480d0107260410010401c000b0b401442800381c0c18050216428501c40f0000741c018515080041c50b40d001c0c00203500c5c180c0034982040909080e5a50142113404c5141084c2102e01d0703081c01050702c8003200c18815105100c1c0080c9020391400550360881400762210381c0142c20030480c005407a920610044000340001d5990b4950300a150103000704440d4010901c4a002c0081c0d4890404a03211207510310002c2440500300001c10211442d9811200024003e2518001d9017007070190048502d40342d403c000b010292422002001440014282002d901e5000c07008800881c0100292406402070007030071556940d592520100074a032480c2e080b2024081d41041151214010400a00039058400c02c101c1c40d4000403021202c4801d0120a990b0001003980003007001e07140c43c0540c1c00a14800c50710032021044130214250300721030042042d0700c120301003020440646c40700319006407800c0d40700c2401612103909240c00f440e030314590b0340c50010003443d0104221000454081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 619919172 1250 619917922 619917931
    0x1e09080c1e012012040c030611070605060a1a07080708120103120f3516080907050d0201120b1201020a0f08040b011403071a0d110c0d0503131a 63
    0x2007100070100d50000e02c40f0078522041280c03050f0148010901d202d034883d420369020784200341c050007481d20395981008880958102030800d000101c0c4a1003000102d102d4146c001c501222402240d901d4600103015611340f000c521810300d080851030f0802c000f5400d00b40e03034001d684001099200c404014440407180340910066174a51402c0349907000d401d003d641402c00c20111681d4032441e040f02d5241c0d0215602c4442d541158014421000d00741140074860514007030707030048814910ba159005402089400c018000c20082d411280040106540b0485024000c943c2070070003600316401d0040c10760007801815001c030b411101e4080c02189000042d4010716612047ea2504154110301c1c150807104000b046900912011507440180101c1998181d48160504010222088103403034160005850a0311040d240070b180010900810b01c15950050045007222811500c0c104101d0500055580d000044c0020034450004080340390038818004003043e40750001c1c49108245d104010300c0d611000201c4c1e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 619920422 1250 619919172 619919233
    0x1a03010611031204122c120c04090f060615120b04140709060908010608070302190f0b070b1b2d0a0207090e0105040206120a3c1e09080c 60
    0x110982c1d00a04071034164101e0041c0e55018162001401060061005a8450a1099212300f440d2818560360b14002ea1028500ca00980c25040000d031030400199079160704061242211100e07240001c0d5030120200a41450042010410b514200003080080600e20041420741c07146508100840750000d200d88200c07030040c5c4c0c80010141d50750107801e00725140e50241094a40004070100054500390000994100a00c10f0f80718216988640001003590541c1c8a001c0942c0701007542002c0c0b040c6803a00e40e0780142d0030406900350f42c0d44594103050501c50704a9904101014000141c01404010711074240d911144000c144e5845210340080d41c3c4041d1072180c08809070a02400032102101030151a0060350301600c0d05040005141846640c81c8008120f40849a03840c3d00030000310803032944030320a40d50220341c1c090b100c00d00108c440603a0151142014600390401280703840040ea050f1b4444103e000380b10300005c03a088185401c1c1090f00c16103170445007078426000c0072422a0250007000c1b246442c000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 619921672 1250 619920422 619920437
    0xf05040f020102120310172d0709051603020c010902030102210603010b010c03050307050910050c0f0607120207021309060b180408030408090607050d090f1a0301061103120412 77
    0x2050144d0051004540090803002d901d64104242c054416207100e40039081e009075004148401c070702803010034480309400c2103c5c0c440030840ca81600240210000f4010f8104280000e180c5154401290042d00650804141c0d00081d1740d080c0803000c0d4800311075a540113009554038143d20846665000c0300b034407000704c8a0124000b02e030042c94140301c1c6400340c49068550500700481c9031020b803504d0300000c000509125007009540e03985d95a80c0c0d8152840b80c40c54450750f85850411000c1031405c0115000d03425554410f0081c0640c142d00060341541c544040c00c00566602c4481c03000c0b4220209081009007200e040404003400c0004903004074210110580d001d000000d1102e5414160703c6d0181e078043d040036401c002003008140307050018040307244040c0003a85001d100342e40f62031805c8074086442000a203000010300c0285442e100c4580109086904900c800d8500328065601d40700c18415041405016040b215600f1340600036140b850002030014201c034078150401004015240024800003a480c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 619922922 1250 619921672 619921693
    0x1e090c0a1404080606061b0a0308011a0c071512020301030c0305061003030e130902060c0a0b1315020a092412050c03040f050705040f14181207060f05040f020102 71
    0x1400680e021074440390000c1441c4c0d00e4920038440940d020442500803080301311200c0b0300121f420020307208201e1095507407148a600d003089681164084180424150703100f0007402c0502e4400081c014255104074a0314034484d414403000340e410005441c8110b264600200000081c0420010044126405175090301c01c180d992031440401c1384461b00004011807080c5003a141343d410805445122004a1040081c8854480e000252250000c1c0342c000403552010300303000d0800c03500d0800b036504601ca55040d540000300c150b898080c0600040f014099080d070202d1401081e40c800c014102c001e00003a5410300e080740b4944086040a41411a95008100c056103148580c0e10140702d0340d0f00c60349211800e1030854586654982c0c011100181c180c0d401e01c91b007000442d0176951482907880d45071946500140c008100c0a112060b06401011420450189a406031070741da0042644924088003860681e950940c0d80f5000e001030545009802006150004000400110180d100e01c0b16000340c0890750120003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 619924172 1250 619922922 619922957
    0x7080a150b18060a050d050c040f0b030402031605010f081b030705040e0105150d0c031b020703111827031204150e03090d02030a021207060f0801060e1e090c0a 70
    0xc2c8189040005a0030021031b0240c0802e07901264210842942d030030310b4561380b600e004c0400749654000ba164a0300000c1888114641009440100c0320042044c0141524001c0042c02c500c0301c4503042d00512402c50002810f40580e00343e103054082c00c0382d89058a81c1024900100305421038014150500d810800204052611148000096540030300142c0790050380003203c0050000d006803038003456210f00d0740005c0c00c95405121fa459100742c1d40209249441c5080c041030013180301001c07a00818103507100c40d00318807050340341d113900150401d0000d005000c40d11110701003400a601c14010b41c00013103100e20341004000300d054040d60180c81e40c0884031080d898840201c0c0c00b00c05990403268000c0002c03021900b001c08a204855000400f900d104003107640205400c800f120188510a0b00300c203100b880442c1d00304014060004032031400c00130541c100400907107100382c03811a2030b20500844040f9440112560124030b68020050401581c0341440d0400d83c0c00e0f80c101d0020180442c85544181d2090741 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 619925422 1250 619924172 619924177
    0x12010f05030703030e0f03070303050c010b04060e0a180503030406140109020a201519060602030f1e04170114070c0f08030a180c03052407080a150b1806 67
    0x42008014150092841da41a24149040381d0a06d401c400e20b00c03101e0f0700d940d40c103000e51740095010f52642a600c030521b0044508507800c40c0444c1d0303c52031400b0014082d07041000c4030b0315402000d51500203440010280421041d036120078006041d40b00000402042003072a8111442c2803461155296484c0d07229070400050b4003807075001400081e0401c050381003a00c0e1189180700c2d400c1181f4180c80c0807828115011000b80011030b4900420362000c48018084100d62091000400e2644091410500352038043c40383c9210305038100071034042140c090102c2051000031903008181364030040c0a103410b0383e413940e170103001170824401e99400850300280b545401307807100340318050f402050409002c1e00d6075106a019000a40f1301881d03665110443e14201500c040c034180700901800e182d508c480d146180c15482c0000c0052080d5000d588140807045811812403000e420800c103003803490540e86d59901010041050528100110450365400280505118000c0401c07a0070162021109070b8040244695072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 619926672 1250 619925422 619925429
    0x1507050304090b0a0f063f0b1203130e07031d01090303060f0b1e070204060609030c0501030204050603060d050a1b0501080c040b0912150f070e040509062701090812010f 74
    0x3a03065643c014045d0010200440f26951f6480b08110362034034071000d1540c0389044c0c0800c2105540c1c0348800101407030308410a003d1070000030021482c0c4200035414261800c030610502d840d00f82c0c103802003108140079400103510140c848001a0000200125541c043c1c21b04607029404245441804240c1c0c1002c84500415900d80e42c2c0071a10b006014000c40784a0441f041c910013181c207007802401c1c0140e440740200c5c0c0c020b041603030fa580901400c50a14014a000e01d0380a641071500c1048200030648a05068a81c03110007116004c0c0c0308429400d04030309003403500754020203003038034280503c0c612402320704401c056a9080c0d030340c2d181c1e03070756056800c401d144581d0240c070302182c80a11004a052400c0c8840e18030780c9000f00c060b101107045220380b0087c41641501c240020300c040004001105901141402800301c0482d4140402d04040c103000b603c900c40508540000c4c00035500d419021400c021040501048240081140307500b641040310041c0c22405c1c14884024030030000040580d40c1b40d4004058 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 619927922 1250 619926672 619926677
    0x130311030706082e080f071203020a110d020a090f0b041107260a120e010924091403090f091e31170406020c1507050304090b0a0f06 58
    0x91344031401d42d000b014003030b807915109119100400864500d00f141000000b4515003004052084500543c5403c00174076400c4002c50203850412603000c00d50005882c0801345d040b82504180c00402d50101d2095040440d0103074000088200000d80710030700d030b4807880c601c4640270400c01c1801c4071041000150381d0203042d0b10805440c00d000b410b02140c8100200082c01d4020b2000ca04503e4071071843d50310340d4200c0c101001c00702c1c51503588519158400c2c024461b449800c82d000f00585c4c0310755904c01114501c40400d480480c1c081c002e02c1c6030a4841782d400f860200707400c40000f030428640c3c480565039070340c45528164012508056180464207003121114050314403002c90141c403004051080301c1240700141407403400c10080340c08055400141c214101c92001c0c1e001c41191b2800c0c1070030041c2018142c001140203000301007004100240d4003264076149202d0485149a895481c0398440038a07004c0c1200142040c00300260002d01e5440759405032200480c240c4a00e0907866407840c90600c8020280b046001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 619929172 1250 619927922 619927937
    0x3020a0317070f1b0e0112060b0321040911032a0f0c06090f1b0d110402040b0a080901061a0c07170a0201031a0a0303050a14130311030706 61
    0x64000c0ca000540c11201020541803012680f9030000800d2000b509585511032543c016403400c0e1101030b2400a40051150040103514200120796004040600034040d0303582c0e9060040d0540c0c00388600c2c0c03000c03807861001140003042285201042c1d4014803441111601e00300e05010b8000c2d010003502c0c03080000c10200e000b101c22808050280140a0609072814403040000c81c0c550000c80380a08401d050300d034010034282c58645030700c5203040078842e00ba420a9100d1880105000201c5000203c174500680c0e031501e0060003403400e0b048035050440c80e036900a002150100e00000420041c103a50800740d60340c410710361071b6812401c1c01c0320002d000c2c103012440c0800300320712480710401c0244000c482520480c0d0390f4a988160b140e0f60040740d03483c086051380190500d5815907906000740c0382d80b209850802d801711004500024030a240074403001f01400404030391108481e0152000c1210110b0a1700e25a0b6214014110808000078a002c100d030b450140841c3e501d00c60400181c280f090307076040d441d0001d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 619930422 1250 619929172 619929179
    0x103080a0f0201201b0637021206101812111008091005060306220b0f0714071a1302030312062b080a0302090306100611010603020a 58
    0x2210781040003080d00642d900d80303080d146911102c200c8091110240810107441d0400704001140114103a01d00361069403001050101d00001c00300c00d0020380c01040c1020401c43c1803038844202181e885440032080d50710100303442d5400190142098480d04c4122140c0031008041103040e254070a151044d92660711080300180103d0600001d26145240901e8141c3d507098450400903a01d46507048610b00010281424455019010409500c081c426400144058506503011035600c8400038110070300c00c028400c001c620090704200700548180c018040c941c6603d401c0c00c1c50204000706594000c00a2070801035040444404015600d00d07507440002e03110100300d01244182d020704040c150a05d0703200c0b80448680140e4040006003140c4400404500d41454580f08001210b4140c122003001d020f01e0b10b5074404c01d0700d000c0c1460740c05642d0009000d0345a1003020002c40080c00341c2042c4a4252080e10309201d0381703d03d2203401408a0b61107507035400100100400d540c0c261240c83c070000b5000010400c050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 619931672 1250 619930422 619930427
    0x603050604020c010f0903031a061c0b0d1b06082e1517060d05060a0e07230a08030c0a03050d090609030507050d02010b0f040e010902060a03230103080a 67
    0x1034110800400250074190b03407400c05400c40320000c4181040b142c2c0c40d6640d40800d41c140c020200c0580041841c0001507620b075012030007500c00d40fa0440041e0494003e000c030210701691007030a00042c05841403441e81c0c00752a01501e8492924014402c106503d040025128445c00f9011f11501928400002d1140d1141030070901c0038103000c1e143c0c0045100007020607501100c1507180884862540c4081d6011010107030800b0002003d07118501a808400e03849012800004006402911602c00082e407044c072104c0c55420107015401c40c13540c000440c8150700c000c46081c07845401d5000e04550341c0034005d9460390056501d100c0c08109080c00d8215080c1c000210780201c0c050b000f0040d003010045801a695981c1c60211107a855040300072070380100700002070102c104514603020005000800400b07910070000f914690030409a10700c01e075101c11b86010405002e400040c006540074003155111604040041c000d801144031120400c810101c0905000c00003401044c100ca4210000c0e618040100c0800c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 619932922 1250 619931672 619931681
    0xc14060d0b0a05040e010f051f1a040e0f0105011b1205090d080c010e12040b031b070c06030b030d0c0b010605030c1201030f121809022508040305060705130603 70
    0x100c99001c00c460b44005034603200c50280b200040107541c000940c0e00140e0070124115100500000d01600a078484e1000104802c240101604c4600f10b04070b2140d00140582c48040c415030b003084490fa1550818029809861080a41130722426212603115900444140c02c002c0906030340980750030003403c800700c0000e001314000c09400c2d80c050074620300c3c510a5198080294030030a0047c0c0c89130354502009401c6c0030240140d06101500340b6805191900d484801d82c0345020103041c15081d4000c03600761007001c0340341500302c4440302c1e4480305002c081d076034070b942c01340c02007003030310701580c000d01038910070590041c400c240c11260907502c800d070303058140d0030540c0499940d003000f0510300b188001000040100d441c400b05481c000d510031004c210003a00245401241d4441c07400341203060150607940b1071032006904680d201900c80340d0b480140c0f83c4003192503070742ea0000c115840d9030b00040c8501c0b4810038041e10030010815a8001c004a40721502c850008a45510452415a0b110700ba4030000340300841c4070707401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 619934172 1250 619932922 619932941
    0x6090b0106210e030c032205061305060d14191a0901030b040620071a0c07020d020a05040c111b01120e0a08040b122505090303040915030c14060d 64
    0x8885c1404a40c3e198149958800103a00c5607403015070401ca02000c051603c007501406064503e5070901d6600b08000c0078183e40e5004040c494031010404225289459003d9080840e102d88000f0300c0e414001c0905810010070b03058459224101b0541110b800680e4200d9001e8000181500240c4c3e860350311601c0d220301c800fa01c1102d02d030341c1300c0002403a08070301d4810100500542c0710b892079071011280340c08a04401c09641a8018820710380420640e01c409000f610480b41d01603900086840b01c1d8800a21250010f420896110b46072180d0505000d174440ca108480142220444481d01070031940e0b58a8600300113091400100c074001e60f1826140507030040000401080d04841c0c6204055840c87e03a20341058004c50303041c5e2404119800c0b0804106040c580103003002141d46c3d510030700c0b554146c25221901006a041c071000145524603600c003001154000c00441404000d00758503046980b100032083d100c1601e680d580050b020903031081411099018480003400140b601c6151010388024008824 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 619935422 1250 619934172 619934201
    0x9040606080f03041706130816060f15050406141210020415020606090906060d0c050312270105181c0501200f030a02030c0409020706090b010621 64
    0x490001c1e035800300700801c035818403540d000b45440d00d0809174504140c06022180d070542d5072224050006040b8401b036040407264109802c0c41d078a60124501e402c0070035841c0e10061005141c82c603410221641507000240030541540f030003c0fa130742c0e1002080262000f60040106040010030032240a140210b540d103542440d500c02d9a1003045c2c045030010490300710350701c0145414901c004071070513640e062005075070124040350420902d00b0119005940d528005082c0c0d0b0281c1c10300b1040d1000e02c012540c0c0d074001000001c0440340071455484a400c9581c2040040c80135607003088004240d13a01e01500c0c01310140b001a17454a081c40c1000c6247c0340040c1036070b40c1d0513070008041ca02c0e884001030003c83c40715445e4040c0d400895080141800c03684120400241e40d0000390082c454001c41d81401c10440c0d800c58643d51000d0317203a454035101c1042c02d109035805416000d100103007140401080382c102140842c0034440d1445180c6c0d807420103a03490054903001040d00ea141050880d803003601c0d40d0106007045810b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 619936672 1250 619935422 619935431
    0x1050f03280f061814160902090a1a0a111506190914090c041416030605060703030c080109111b03090604080705040501080102090d14101433090406 65
    0xa450715002c94400104c51a2a4141c562410b0140545400d2405031902d1202c02130180f001091145c6101c02141e000b103101d41600000e0450b0135550703008212001c0c1c050600711201e020f010640303c0b038440c1d102c0c0344e03541d001c200540c07040340c098000031900188000180700c9514081d500d040801101c0110f150741c4a41c0045200b40100c0c0303c0003148030f0f10f5580c0e00c071754903880b890342440d111851074401ca10104902c079034103000850405220400740c0940000c22494a11446a0b4108058025000a810064000802280410a240d40b41c1c11444101e401d540750b6100c90f0362140c2d14101545d00c24880500f05e074004000f40004e500c0066100c43d07042664109490400131300000060180c1c0c842d86c4406070036800000d0600c001d1821703128840c01420014021460013000d01c012819098400c0e401a11545511401c01e4030300a0a02c25411000100346040164040f0f0b802400a9400243e0700718044100d0404010601c034002c00451130f44c9002e6500b55107100c0b9504007007041d0703008014004c49440d03072078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 619937922 1250 619936672 619936703
    0x21009080d050c010917091f020705040506030709231e0c072a170a0b0f150d150e07060504150504031202030a140f19030b030f0601050f0328 62
    0x241b07500d410404415007541551a21b450080000a8080c1c1000d0101411040d41c080461600044c101c0211001a500171500f0707038941000905103040360f80306030492070409200c54000c40c00d29010842c10403914035040610303101d08041c03504d00300d468140c03455038030b001034007082000840d0000362403103d101704514240740903810b0f49100c0307800c03d10050720144d01c680001404020710300e55100d9182e10400008221a4810b62a9004c0d13122014140c039009840d1b8801040102074628094080c21030080c202495800003440c0100403031040c0e1a004100e20718141c2691a250404201d1004a461542c3e4150401d402c0020480d4514002040c5400340301d8108000000641108010b0600e0710158001c0e6882d40484a4040c0c041c1041144071112280200040403042007840c050b00c0030180d003039003e141402c4020400394000c2c0195000d040d4035100e11410502c514500080c03185c160ad0040d079001080c64891018581e40741e881c04101c203500700c0181c851f460741d50905103aa000881c010301e40c14260f400f5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 619939172 1250 619937922 619937933
    0x20607020a17010c08090316020604152d02120c0a0b0901060e100b0703050f0d1b020c0402070312090201021c0f0206180c0d0204020f0f030103021009080d050c0109 72
    0x700c0303034030140e500c00892410001001080c460418414014103094015144c03480c569902d0f4810501070004e580341582c80c410a54a80310141c0d00549520482c05c5004650000064203100302c9800081c1a940803281c00e130800c0d4456208085000851340084c1200d42004070980c001d500410900281e5201e01100c00e030124036000d40660280c2d004500024000741081030213082c00300b00424260800e8110b510801c80b20080a04403030005405103012510790007400e200c04103920640d4518a034a07420201601d0b14924088111020110300c0d40131104a0859081400242c0c0141301c0c0140105001000c030041c0081140c1011a4651051064940c80728000c0032850440a42e1019030300094944807128201a4040243c1a0041c0903000c002461014409902e9031358907003140891f0049030350500722421501c554041d0360366800d850000648038008200e50b650030380c01c244000da1040079076040182e04140100d450500b43e0b075100c1c000d420a504840c1c42038030507903c81e0b5003c603e690360300c0c00c0c2d0801045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 619940422 1250 619939172 619939189
    0x20f01080a15030803040b01120210050703120614010e010905010507020d0203010603021008160509060a0e040b060a020c03012009100c080301060905010816091502010b13090201080a0e0309040902060702 89
    0x52283e0301142e05ca0400c1d041001c401c3c070050b00003682070400c000101300540d50b80513082c0c03a020810b141141d40d440c1607280446641038020301380d80c060b83c240702c008103c0442001080d14200e0003aa0740245000200004690103000c501c40c3c075000c50000c1080c400903041111003120564000303030000c94032650740d601080005100107105000102004203100c2217100b50200303c20100c1403403400a040490310400261144280c0c00700b0300600c40ca9001491803602e40340c020b10310900380180300325240c0c000e1000c069107680f0a00e500907c43e5103400f4034030781c0b01c20727401c0d02da411880928085241400811414809101200309a503001e01080702d0f01540050303400700c01180600f08503a03c040d020740c03910b4005440820007a050b203551150390744603041507075400840d0b1006c542c10140300710070351212500241d004003034a811864000d0740c40f440c981f044400c25080124038520030390301c483c4640d4504a220007255500079071542d00f5001040035201610701a04480c0181e400205150302c1c0c5615a03000500d5a07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 619941672 1250 619940422 619940429
    0x120206071704210b0628030501020a020f072306040e0c120f041a100f170f0304030506070e18090d0f030212040b040314030f06030106090207020f01080a15 68
    0x4072001030144891a009407125010180401c00010300703d0f032907507450541c03600c0244038901994421040d56500f540c0c0848101c0851a83c54000c816592a400c025001c1c0d40090f100700e001d440748442c00700e41c1d031000064030b00446a021403400c420301e0f90407858940e410b003140f000d6540302105000200d0100446200503000b121a525415034880b6400c8424611903001840410f00e0408402000302280c000583e40c0000c040b450000e040947d654803c0060717501d03c035009140c0032540f000e0b0100f018188204180302c0300b8880d40031614411300680303c0c241d50784030781d0000401c4c0c0d4100d00c02117241c3d603020f650310b02c000050003003d8200c4000c6d120b03040004070108941d0580254007240120410325000360020010500340c2c9015480e144800c0208080d106000c0c1c00104800708140c002030a1505c200c10450003100640f500070b58909210300755080c1c080c02922102c2c130952070b00c1070014503070f03150384212141c095000c0c003548584444480190341c02c100050206031a1034807625800d01c140407240521014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 619942922 1250 619941672 619941713
    0x6010f080c030411120d0201050a05130b04024c020d050904180302060402090c041a1c02040602060405120a0813050a021021020c030403140703050d0c200a12020607 72
    0x4401c151b002030a651014103c250741910349001c2c1302d0740302410824800403035002402012591614400308500840b10b8640112450101582c00c0f003e03514080304030001c003505403804492008030110b8407008620b604400740981d205c4516003280c940510080e0001805c0240000b49201359001d041c0d6440000040c00c8005800410402045241605810b034210361203d802a00b03150420701c0d038946d5012525900d58003854049906035144948000001d0a064952810740d1140e9a5000c040e6450105680403580b6000e0a074524207000040000d07151024a40c0e07941541c0f0340c4134422100c072070540503802500d1902804007010302688903540d03800341c410003076503030f1810b0007800c040106030035080070040700d20b5903004000c10401d056000064500362500095441d4a0300410b01c01ba500c5c05a0603030008102d801002c071400459a000010a00c806024a640d04c4441d482000344020840302548441e41c081240301d0180078880364844c20000c03041c0301030615407a208458032603480000c0003281c80d0f0103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 619944172 1250 619942922 619942933
    0x150a03060e0d0306052d0406030804030308150f01030506032a100315050f010c05010f020307140a0801062319030605010c0507030828031406010f080c03041112 70
    0x25001c41082002d003032000900c3c04001090801e0b002800200c10000800d001c40401c0d05140300610b1200d204000d5108014403c10003940e47e031501d0300c1c150b007092006801003900500026400c02c07030054a07804505c001050042101030640c019002424040c02541d054803501d590b450040e42400b01240420700d0703050360103030143d5241081056501041414030f00300b6007450282d03181a6540075a140640320201c490000c0f01c4940c000407a0134100d6004090029800d14001d00069138603075000310b0089a1564402e00b045400c20303111040303171150180381c500045000c001082000d200f4070018841040750200d2020f00090121f034010b140c3c00495820564250551080030b00d2505841081c00402d002e0800701049441511403e445114900c00544800000540b1140740707261300d803084c488448401c5c601802202e507403100900a0440d881034410b81c0c01e65001145156006903403900c0c0035012651038241e556952a141541c07500017030001c440300c0716204e10f80502c0d036407107585050000300204000e09 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 619945422 1250 619944172 619944191
    0x5031e04081c14090d0801090506030109021003020301060e0f130c110708070e0604050108060a09061b020102030a06090b030c01051303050a260405010c11030a06020301121104020f12150a0306 84
    0x20003084029114100301d5010701401c0d174601d1b80200c8114115000c1340d41c0043d0030343d21440443d014010b8600d000354854024200d1074103081d01036001cbd6041c0c510075035851600000c180207000e40c000713842900b59404201400840070316589500800d240d140e003403415107007000983c9020b620b000c401707030030404181e0000c240a00105030050382c050350140003141d050005514240a01c1d0316070401500262400d512200403030144425034000e06c0101d501d4040c9008038100000c0000d00070f400549084151038208040081c0d901a640660b121501c401005030602c00803003001940c05621021050440e16610000040490380501c032401c841070003050342d036403005400a40180f0701c2d03518000c00c00000000340024091031340d0200c100010541e0001107440b54011100c002482e1400320240103000314000130000c6100072540e69820f032003c1c80b40c420240b1031407000081100368022201d0000721180e0500818104230f0b08445c59a030050305540040e014450740101154640c1c00e00c2d0402c0e203e16441d0380108 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 619946672 1250 619945422 619945451
    0x50c0403060f02090d2a090b09090f0309011b0503310602122a0c0406140f220203041a24060307020709060f0602060705031e04081c 58
    0x40b8000e89001d821460701c908400011020313020007201400080d200d24620300c01c0214200c446d141000c034000e280b1803644d40c45148001030413940c8040b0740030744000c2c40811145040001c03010144108030014500f09070351034004440307030140140405050a0382050480c04120280000d0995800c04030030815900c4032840284200751041e11200c400c100805070411009602164500d0400820b84006503a8908018041040f401119640850f00b104c0c0d0700404219400003001030441c142590103200003561000801c40c0e21801f0003000d40c02000381680d540d628500482180c40980040b1720010388103600b00504d00480c2c0048a0803148501400c2541c1e04a10041c2d03d044d52040041c50720200f519a803508565000000442244c000d08020000c503000d2402403180300083e00100c41c0402c030940d50b03142d80880c0031a407172142e1400b6019035004120120f201c1c81c2200d108031128220085824024814902c01e80f0004000745c40e000d0060104050340c40001c0d08400c25200040008140b580e00381641d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 619947922 1250 619946672 619946681
    0x7050a0806043509040212090c0f04090c0512011103090604060b04050c0d0f200706050f06090426041728031803080703020a0b06040203010b120a060504050c040306 72
    0xc2d207110162410f140d040d050383e060b040030300096015050603140c40e03110012030081c1c007490989018403502d00d410018481c2000030034101d00d550458880407040004402e101c01c4400003030b40900600385014051005080000b05403001105080000808419688404806820503030b80041503401840902c000d12450f402450303c0f1003011503040086041555507620244901400030340300e103842d90810542d2040d43c1e80038000d00d2250540550081560310041e041e55800f000301102c2e02c0f483c0c58045055000b070302c40314511945014003500400d4407262034054000d03540b20f40c0c24075009102901c120388603407040081c000400c103051581803114091210306003090281d8404071070040090a41c448610060140440e8450301b5081208086124400c4030700500740541010f013801a000418104143e40003c000c0c4000d80104110b41c2e00740c45400c1000280d11080c41003100fa074100303121440341a100a894190810251140024625aa200410140c401c01c680c0c006543c07401150400501105c1c1c003a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 619949172 1250 619947922 619947953
    0x9010b01021f0c0e03010c0e01020f01020901020a14030415030915110f0d11040602060f070905030a29011403011a151309110d060605030402150a0207050a080604 71
    0x1510b80c598910818602074240030480d85101500c07007110b2003810b4001d072840704001802900900915012a901070300900b000c56002d80103100300c1c038a40a8200b8103200f07440d4441016805426500d407107840c4c1d00b404841082d5402000d001c1084006611000000c002e20342401c2501d011a40348100c0c1050140341809115142000c1d04210300050083d004c0030480e80e2030010910103684030071440d08082c0c001c0500d11885548001c0014006c2a03481c1c001034004c0c4614101c80900015544000c01154048079501c41c3c160103512100c7d5100000701e40500d510284006440c00003024040c00d0305041a001003030f480700011003010303a0344841c517090a000301c0322809094080640c00c0034103000455210301c0c1d0480100410b010102e14220700c1801040e900004101c00351083c4090b201c992140007480d40b00341d24038900030b0f2506400003400e0b40034809492065400070440e0454041d2402c448000d903000c21850300441c09803d4000ca603a56a00030000d01078525840100b00701c0c40d2515015403507850030807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 619950422 1250 619949172 619949177
    0x5120f100912081e100504051906080f03030403080c0c0a12030e01020c120702010e2101050a0605030312060319080309010c18090e0307060906020a080f150d0203030403120809010b01 80
    0xd0411802004000e4400541303c0700200650b959580c40f0700100d084281904503070b81c858107103800e00419000020340680b010b4070015007080780507640d10109941d400d802e01001501e81040c00002c002c00c0c0038002c4980e00411b50100d251070545c807407421901f000c001c44022a945d2070050300c0c001d03089078507102c0c140306610f00300021890f10901f0000075a4910411012101984000035085d0071039100710700403440854090840415070409000300c0d043c040d0344980c507041962130f100c0020030128060082404445001c0c0c043c5181031442030307440008200c000c140f107400d449000c1d21030300011090a0b11101103400b5140c0d0300e450b420045035160079035140b841410204104461703011700c007003d1b40c266441198041a0009803004082440b03c0c110700503c0c4025104071b160590b60014004250001c0030030790741c141e861080c2075a6065500000480a8542580104041090a0301d600f0013280480c1c105000030101e80c100f0784d030390352000b100c4000c10008074009610030040c0028031809004400a0b846e090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 619951672 1250 619950422 619950437
    0xc0403060c27082e020c0d1b0c2309010b0714010b101d0603010b0901020c040621030c1b050111120307050d02070204110310060309080405120f100912 66
    0x5400750b0751350383d04d11a81c000c003455858820300752078030610b0b80102414004a044d915000c62141c5603440350b50421045e80803841110100d5400c540c030b40034401800c0d5000080d40160307402c10f07542c0203180340c01140190800f46141c40780b04180c2d641c0d00b026402030010208a5980d0301c6503282c40e864004100340e80c190560b06000011949648040c9100000d51451900c99010681c500c0346e0401c00f005c10344807a03040a800400840c40e0440d102c01407140c40820380031610f09208190a002c01c5418500c509001c3d140a42c0c80d5a100720789410759182414024503044820054945800c070800b116900c601c102c21510311030401240d42c000c8051020004c0007809003030045005d0131004103901c0000c1c002420808009480100080c46071f05561080750064001c2118803070340d0450f0171040c0d00580c0c880001202c1210005055886409661360256200740d20b00c0c00c0903e0002407050034001a0420803550254150049202204004da580c0425a01002040e402d000c4d06113846400174000c041020041207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 619952922 1250 619951672 619951679
    0x3070912020a060c03050d1503121d100909050c0306120601080c0f040618060e130302031207025709100b070b091c0c03080c0403060c27 60
    0x29400000c00f20303402420a4614040c080c0380803a968800d442000b0400b03458100c140000d000d080c64039600ba03920600c01e580c0c43c0181c8507000c1ea407040b0103030111855241882c01c80342c40707410000315013081c5d005907084c03070342081e5140d903c114140c0701c0032241c01400620200800c80705181585440030002041c2c0090206941003007031a07a220030f0035000e00c1d8009c045a1485104039291a88820000c2101002c103c400b090120b01902c050505841081a40c0712642c011945011464152403000760f4590000c5150411f4000a9140c01400804540560103042d40d402410a86001c41c0444062003040c00840c200c030200c84400e400300c01da008080c000048000c83c2a000a20f1150402010001c0700d0301c42045d511038030204488140c4d500188020080441d69008200403001d9442c007c04c01c5409540794500121031450740c111030a100304001418805001c800b290080034400c1d0403541c44001145042d4881d1109e0f001e85181000c4100056100c180c3c40f0241550350b40c4510460f410840140a02447c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 619954172 1250 619952922 619952929
    0x9050706080f071d1c060606020613060e01110304080408150c0409021b1c1103070215030901110a051207080411060906190e190e2e08030307091202 65
    0x80204000e05000107200348400011510100b25941130000381a20300802d0344200d0300880c100d241e24101c41c691b06105020529500114070517101b052142c00c04c0342c503c441912030a003c2c00c0300e0013200c89503569502142e0718801311800114800c81c081d41c95140e607545000c03005e5113052280310703081030010340758024000e0041c0b00904071000c44034214009600c031380030f040c07062001181d442c000b4115032169000794002c00310300c995505030b110345984841600140c11003006880e40720b4500000d40c84001d100303c1031101754003a001f03160000c842c0c400014003550703e980a007403c0d0340480c80b0070000c1100400c120b2408107028202951110161038481807504156980c0c0c0303e280d10880c0700c0c91140320045030500d1551121405d80f0b4001030414466040e10007072000142081c144481070038000c000c18083d00082d0404105010704941d50500c0c0000c076a615010035407403d005040e030003045a050f0030789840451490f00d001202500f1400c0203140d03030703040024029012018903845a00040075101146025a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 619955422 1250 619954172 619954201
    0x614130608030327070e060301060806090a0305130f0e15030c011706040f06090903030608120a1b05030703090906060e030a02040b1815010f08040b07300905070608 72
    0xa162110380380c0e0700e440414221501d0f07040855108800e01c5440ea0008011b2140301943d4004c80d000da00801c5215101c221607034030f40c0412144129645d100d001603c0000380310f10001c040568018024451041d184c400c1c208600103198000b0481d03006890500c09090341608200058980440040c10a03011a50000e040c0c050420808140501d00000140080c0c0302c94100d508141c11855042050710744130b512810003401c481d942540000c0c684540892103190000300c2403107600800d88010306004a90408444051102c400380c07110f8081c90b503100740020700c1000034110540c40798507080c9a07607061042c58021602264000000c000200d80c800003242c40c0440c0120005805075404281c10070070002040c0c4900c44c281203401601c2c1c010003000f070700140d90340310000007070700981e10489140340c0c0705c108480b50740d81903d010b0704d02d104d51008626258002d00d60b0714000310b0500390b064040c02411444032a44001c004030380d289680c440c502502000000d00640d00a40300074200f170f25140c20414821010003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 619956672 1250 619955422 619955431
    0xb0402030c010c02100c080f1606060905010f030f111f23040618050d05030a0e040504080f18120c01180803040e10030602030709051801052409030106141306080303 72
    0x80030205e5140e00744001f04048400745150003140640d40c11883e0301000d485ea40f02001a1091450b040001c01c1e20041400345a04841150707904078500360450316120428152444100c0710742d070148519400030340b11038050115010f81b152150711661117444001e03001c4503500060302081a0305501d21070000b007060080d6415640b10b49000f461105c1100c000c1d6144050b190001984002803480700020003a00000526000300c007960f070503280f15009020300042d11010f480c0103080307460500210180c0b00300e59001c0c243d03d80f080001e240426410034041004840da0016101283d0040c8510b000d965801c960492204c00d04200c2d81f19615142c60b0101340c50707020b20b010304032100100001003802405074521140c007a40e00540304641d6818500809055010b19205007030003409000010402c020391072200300e04880002c0d000c0b1021520482d000b4550705201d02e41c4c2805a4802d00034142070fa2000d10400d00645141c6c1d82c160384148081c4d04029030052000ca1040543d4288201800040d001006030b0b03411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 619957922 1250 619956672 619956677
    0xb0111032a060c0a1709150702010f0504140d020f0a020405180f010c1d01020615010c050a0b1e04051209010908030a0801051c0804030f05190b0402030c010c0210 71
    0xc40241451207900050240603402244920014070028180c044002c0002604545500594104480703803a00c1c2a501112021042e4002441400d540d84920040603031080f0310380300001c0d407a0150031011080b038a0544090310388403103298074000d10000401410404d40d8581c0000c1c9810b103040700c80380c5c3d6a00400400240259120b50108540f544041102c016450001c0140c401456924100c60f0007810001445030000b0769040d10000b288801c0c10041d8003401041e03014224030b81d40d801022404400100c1240d041111000c003c4010030010b00686800b41d01c41d103081e8040c3e04000300310078406141d6442c00354464400720700780030000e500010034454400c1011481504e03a1341403401650521181c2d48614458000019240245540800051b042e1031046800014980300e607503117220b42055000f4010400b440c2000b0600104070b14894000c2954424007c41340002441495000d00070501e0304110307240b19000043c0001c520f81480002c0841c1301c207103840104e441003900055104150b82c0c2c0d00005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 619959172 1250 619957922 619957957
    0x3050d1d0f061b0105040b01060801030b0f090309060d020301050a061b030f1422060f05040b16080705060a0b0d030e010309030917030a03110306030309100c06050f06040b011103 78
    0xa92980415a115401140b800c000c10034000f10140740030b01000c8034203c4103400d500c0c00200b540343c090b20005050342d401c005a00800e07902d6a40100070108040d15180c2d07248020f00415a040d0344813001041110090440561694980300034400000c100c2e401400a2011503038200e00b4101d000f41100d0030240e0180380c860303d00c040e8010140c4580e004090098004680001d00e80e00c1880007a1601071201c51404109448a941e010100ca0a00300207029000080081208100305000b00010380160500a8600a498801a43c0c0c0c6034007640031403401c03a0139800101c00c000d80010280306800c0299411364a8181c00e21156400038010f070031440006e0f0500d40ea0b0300c640c0080c184900b4100000d000340348014000304c100488140c1e5284c000080c8000003900300142c030741048180358152802070754051700039400c100030710f020044002c00d48030340c203420000508070740c0d8082021409064000d03151025030000e1403c10405100c15100e1502d111414801c0f00d59080c5000507000085910300341c4007000c140d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 619960422 1250 619959172 619959199
    0x2060115051222080403051c08060f03032712010204030b040f0813030321060e22050d0f030e0309090403080c12010e06100c170a050c0604030903050d1d 67
    0x20414030703410381d80c49409894000f480b0402c01c0b4180100b06482c0180204c0c1ea450310326000488041a1030307001c180008000c803000c036000381002400d11800c0710008059906010551100d80d805a0b5070394901481180d00038428a42c5d401d004041d0130803508858000d42c50301c2d0964032952071500700a08005c09502d8000d50f4071081c4000101500c1001c81c0340340e02d44418560300d05005029000030009505000d0200b80e84140f0100f40b0300c2103408607920407060006581e1f0f120607940e0001201e10075445603078500d6410100040341400081c14070703c240c2e04c42c0031101d004000c004048448008601d41c05610401200103c0d40e03444c2c5032554020f0345460b09114031742e5034901800680c024030109007003424485d00042045545100c0b00c1c1d10584081d10b0749e03010001e20010844e0201610783d8050004c400c03e000601201120340000c043c55905810031614044081110b0307458000c0c200e81c01c0d40092041407090013004400c0c0800110140e49140c50880600100030715120b1089004076188990081160213 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 619961672 1250 619960422 619960441
    0x1b03080f03102310170c1e0a020706021e06180106090f02040306140c16110d03050d0e060712020d0e06040f0b220b061f0906020601150512 61
    0x380c003d4000920b40500c65810390800038116140c91420350321403118248000c41040c8984070813108603501c2c060300d00d455100c0000c0c400d060f030302c40e5001c10f44400c5020024050410340000900c1c2220b490f50082c0b07444c52030810002c0c2080101e40c00003900c00b14181d110b00d0081030000e80650010f040000d04091910000e956a00401c115030100c0744c00e034200000001000c0341c6031301a1003101d0080c5021f1004a0601c04a044014400c80c0c010904803028440213042d4900c1c400c0300c2108030b03c55400b80302d604000d2400580c411510340c404900103040040c402c41c1014250041a0120601000030710399400e220340b010f8034001c3d5800e10b42041c9076004c600d00d900d914143d0003109141c80d0a074107880180c1800e040540c11500100401d035003005010020855242c80fa54504201146a0242d42c030032401603580c1000c5c070100034155590180d0520701c450303c1000c0e00008402d100031a41c85d98100740e031800401a08110050740711400e5501c181045101040e0800100d440003010781c4560b0940d9a02d000b00c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 619962922 1250 619961672 619961701
    0xf010602150a2c0102040626010e10050d0b0603010f1505060a0c08040e07110f031b0a21030b0307051c1a04050a0204060801021305100201090503030408071b03080f03 73
    0x210041d03448000005201c00f041d03000340b082d120b4664900000f00d11000c1d00c170310040c600306560106941e40078010030090510a01d0707075820800361214400150381d5140014602160101d090f00d068002d4428000d061034244540c0344841e803c00014000c00f541c081c10844500840e1050703e02403000001e034028403071303c14143c042c581c42d8002c0d1103d07100c0303803185034046114504644060200b03004c2c0b40c40380010707040040e0450000c3d18100c02107141001d99500d4120401e06020008007510076600000c0005d00c402d0042c6054020711500601c0f0000791920090070303140580c620070300a1704060400d10181e00da81034641a01e000c0070509140603e51403030859013400001140700342008900040c0004c010340030810088150081381c05002503516143c002c0d00300d22410101c080d000042c0c6804101504000300c00d00241701c25400002000c0c03916442d400c4c2076900480f82140c00340400542c50301000810050460000050305000e4946401d42d903a02003180700b0054810b9541070f012000a0031403840030320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 619964028 1106 619962922 619962971
    0xa1a041416140a050306090a0b0105060406080c180a060507060f05010b07030e0102030c010c05041a040305060f040c1701021c02091c0203010209090f0f010602150a 72
    0x1900742181402202c00e0781003041d200c070010781c543d0184403151207809440c1c05412170715a54500003002d0386050300018400c041c140001e01c449a400700c0595403100040c0b03409a40d8070141154481c8003c5003500302540268510400b16403168844064030307035140304000034040310480d05003c00c2514400d020340c0025210511180001c2803152209001c2080b040c01036a01d03000985001c5c0b07095030310210ba80c6007c10b40014041140080304a44080c20448400c0214181420b50b920310741c076044013510040c0410541e102080c04c0c00002c48a10000341410b080227418040c5082010307000c0e4002c000c25034584003140d41216420070481c000c403a04420001c1c6101c900f81d503003142c400b50305d0101803021f036090365091092850b04d40704c20445034051a0020451174070351601907136041161805070041c0c801c640121042e40361245014003002e4008202000220301c440001480042c1c4a00000303 = true := by decide +kernel

theorem cover : BRFrame.Cov 619784172 619964028 := by
  have h0 := BRFrame.cov_init 619784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 619784172 ≤ n) (h2 : n < 619964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
