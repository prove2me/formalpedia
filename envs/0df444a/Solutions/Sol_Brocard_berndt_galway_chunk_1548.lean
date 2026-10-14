-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1548
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:31:21.617167+00:00
-- url     : https://prove2.me/submissions/9bb120ff-529a-45b6-90ed-0cc34ba948ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 278237410 ≤ n < 278417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 278238660 1250 278237410 278237437
    0x204090b04050a200604050f0a0506030403230c0303070c030e03031209060a02160807080d02041403070b0a02101a0d0305030709290304020a0915140406150f020a0512 73
    0xc20030788140101180340b1140d1402480c170340c209400d0006000508804010f06908003041e00b40100d142e0fa11040590b00c218402c0d80c031205400d80c000311030070400e0569014180740000030304c5441c528403c04000d880e400f00d8140b51103203900350300f400c00703c03003080310f8035800740e010b00001846280e0380000d06060303032048514404981c80c503110482e4840c101e119070000d20a0401c8038481100000d0384070002081d200e030240314410305044c40030000100300c0c1c2c040d601400d1040903240152503a42810b001c414005e01441002e6800c0803010000030b512900c1c06003500c00141d41d11300d540001c2421106c50341151b5180542801d0b01c0503518070303000d403090b401a60380780040340b000d00000801d40382e004d2034004d02410300c601800f004618403403081c0346900050402c0fa0710500c14200400c0c5642c16200d29803401b0000460000348a2402030203140c6a2076844403a40601e062000a002c0703401603000d15071070700450b0302c3d104200b000d024034100c0c180740d0b511400400c01d000e43d924014800c10b00038007600c100d020703991 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 278239910 1250 278238660 278238683
    0xc03020a0305010503150403110f190209100f090c05040b1626070602030601020a120201020901030b01050322050a080406021b10021b030f030408010501141207030f0204090b04050a 79
    0x10107689040515070011b42c10403a07000900002c2c42214140c54141c0e110b01150440118040180d041c540423a0018819200710924030040d858414003080d000300038202082c20142c10b000800c240004d103070280c5000140ca407403088101030320803800c65000349050f520b01500c51032610744a821402d0031a80640328058074803c010120781540320460080360b200703c80e0f50702e48280b42c3d55940194000410060550042030380203030215440f42a000b038007182c650f00041c1d840c01f944001404070b44031140c00e9030411070140100001d00000c140d40401402100c9466910ba007298034081c1c0ca05004000020701d24000403c002030310980008440f0307420b110381c51103100c40616041c1400100c4003500001c10040c0d00000c031868103060200c84000728104003506640203d44402d04e030501d554000e602c00d0050740e5643c0010083d10300402016450400100c0d00814091ba51a48003035940c2e10b180409400c1e13040314040300046569550141709041c5e03020042d8580c40c073301400c00300e0b1940c6191505076034165194 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 278241160 1250 278239910 278239919
    0x271406150c06150918030a0f03090b09011e0b0f09090307020d0b0405010c110d0305070504150e030705060a05030c0a091502010c080a020c12030901200a0f0206010f0504050405010f0c03020a030501 86
    0x540350a01c83c3c0c05c4000065043c0801100c00b228481d100b22400000d0680d00c0e151075000ca208820014480d074807000010074000b8000c10102a83c0e220780b0b02d4034940c280b400c03000901990b1020038084410710704482c13401598690754a00d03803c62084003002503004004204440800900301d51880c82903020318003c21080c800303e10191264091190300b200b154100a40e51a0064001d0340440e800404901d4154101030b11102c410310054080301c0e40401286511001c0152407804000080250000380c0361641040039104014000340405040d480d134500e0003082c801c03440c500c64008007008144100b095944440501400790080c1514441d001c00901504006003119200e8001c0712030013075a0900900d40000d1134102007030a5040944120815502c1c1c864881e40d450762843d580c1030482c00c58440c02d42d00c0d60b2039480501040078a06c200c40075500714000410146000d400340c10101c9509071170101e51550380349800b80c010079050300d580500d14905000030906a6059000d00312a00641d00d00300090390700c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 278242410 1250 278241160 278241181
    0xd090501020c060304020904030c1b0e10050604270c09051008010b040b0d0b12010509070e0f01180f06030809040e06040b070f051201271406150c061509 67
    0x1c0020b56a045401000071a0041c01c11000c0c240d48113005e86068a40001d00382e880340c8038142a5603420b0450206603200f40300030301c2c801000580142e42c0202c0d04507450329000200742603000754850b4400c1c2c485000f210706030796818500c00491a18001034100704480c400303100034045401034020316000b07000781009261070600480c14507040e10b03e00e0703c110341003d25140c080d0b8207c0d4000004044655110044070f6583e4460180019040e90144c002103814500180316a02e04400c0f44c1c04070500f003500d1428090795031002103605040d640800e0106a4414490074054050600300010a0f403951410b80d0000600c14614050304080303508640c248200394260035266550030080d00c001e01281030306408650389a020700e64014480400d0b08220307040541d43d20114aa00c00e007688210010050007801000c19a10800c00031050045500f003044803e003000c84c610900e00000300024091b00700c044200442e41030308816154010f8074242290034900d403269100d801d40c00a000350900490111020400c07070a031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 278243660 1250 278242410 278242423
    0x105040b0d0605101a0301030506160c02090c0906030f060103060b0a080f1b04030309050f0409200118091b02010501060203030f0a0b0405070c052109090c0c01020c0d09050102 77
    0x1c000740500310068030b0341001088058880d00c0200d1511000203400c0c0340d4401c0720751100c50081c100c1a00c9600d181441c90030074200a003d400c1038240440380d2140290044c020205580d016590441c1a940300401c0d50345520449082d0b540c80f000101c1004082c002e03001480340f09410070303030f001e22400342d941c00246e0060060014600100e004034000491482403e50b510782e000c5401048074400c074214206444050740144c2003907000803101700c0c3c1071001381845001d072500614291800c001c400002c0d250103100c0030301c011004071501801c40040315141e00c01c10541c030380ca40800c107409110a507038141c5070000303100c0d0000384502c03503e403082d01c031070580d0040c41594121162a0065469565100200c0c28070b1440240082046d030f41d504442c10880d2901d1140901c20241512a1203450450f4103005140c007441444c0e540b0304070658401e40020803802400c1e100e48803000c1d01c0d440840d403140d250700c01e100c1c050280319448540c404102c00e031440c41e00040301490065030f0384521400b01c1e00c13a001240c5401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 278244910 1250 278243660 278243681
    0xc0801051011070b072604030206030105130e071205190803010608101d010e0a0e0c010e0d170405090f060d0f21090504060e04120c050a050607030501030605010504 72
    0x100ca90501d01941800340400c64a4003a0100c103441d0040d490b82e4100c0044d412410003500d400c0c00b20010018000c0f008401031b0ba0b44d0f248602d80318101895540010641c0c40140902d6001d440007044c54046481c403900080c41007090b91040c2c40f000d6486005a107010390b4100000c3d6040d00c11030003000b2840f4103403130080c40703900c4d00403d940c0c1c07443c3c0c2018000d40b044040540904110f5103200c01c00940c0405840b00c606d81d20703a100d0021912940341c44020120260301810319980b031868840321207602507002500850900f02030812010001d006000a10365000d01c610240000100d4200041c00789002401081550b20071100d4100b03a480c5d00c030000c0e14401d0300725003540e003040031110500041010300c2c941540081c0700e480511103243c0e00310150a40041210010030124000d9001880246024010030010307080307184c6652424501600e401100068403800f010034403400100d541c06000051103a001e0a03a0405c00700c44103410305010080042000f44002e5a489180000200e02850709010310907180b07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 278246160 1250 278244910 278244919
    0x1815090a1a0307030b190b090a08191203180510110301060206150d080a0801050a061403040803090708030c0a060506100c060c030f181101020111041e0302061c0c080105 74
    0x643d0380c41404d40050406620007907011855032125015204d0b00c0b0a41005801c000e0001c07512829481d060203011180342e00a240c11b0b40069054002c612050f00d0350056540d00224032000b519034002068006040c00419018030245031141901480760005007940c08002c0b207801000b0032003461500090900081c040d07072005800a80c080b90030704107840000c6155074401031604021084d03d90f0782007640d6004400701800b0036641c400401c218503004001e04000c0c003407400c1952280281c08a002c01c9444000d000a1250300c000c404141203102c100301c0c032000391440740c044944d2183c80d21500f03542c0e022a070304126000e42c202000600c40e410104111661004161540c3d98040110f90310b1501525018072003004050b0b4508484503900d241d400b0300c2d1045030300320078030102d0f10005040c80d00c00c1c0303628030303101c2c41c19a0304040d2106400c62040080f20210307045944c12821030340c2100509100010f1940c006584a100810044030405260841e4000d4510102003040506140070301074644c01002d204140c0d02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 278247410 1250 278246160 278246167
    0x806031203040312060314060a151710140109050105060a0e060a023d0209210c210c0d0327050907020f0d030204080706051815090a1a 59
    0x8480c8000103142c2061190500c0d10f0140c0114128000b16200e40d072081c3d0f4030007046031500200b4070042c40280d0b04a01c01800c240040e20080344584070b002c2c00da04c29003404052601c090500744205100d1b0180c003004201c0144a0301000085986540c8400c0c060308081c0c40c40e101c00050720b40341c40317021a240c1500e20384490740c1e44903003842000103507000b090ba680103502071a1105c8414001484440c001124400088096035920380c0041c082d8110342041d02c80110710400c02ca01e040d550b00c021030000f450300c1460800b06540a030841c07909011007010850303041040300310311001c405491036480080e02c060764101c0f041070b43e0007020480040361000019001c0b0b006a1108001101c00c1c90b80f40600c0c0d104c0e034445070640b40d554400305240100849109006030800508003407440c505200981a2000c03c0c54258200350500f8601903d5160500c101414040e0004551490009100041c41690402044800310900d00750988145901801d081c0e4413030490300d200480d074820070304c0784030580c0c9002c051850704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 278248660 1250 278247410 278247433
    0x302090306070c08070507060206160c17070f06061412060f0106030f021c090506010608070219210f090605040e0103080d02070b0709030203120f030a051015020a050706080603 77
    0x21041d42e00f410942c0d00d82800c0000c0381c0420410041f02c001443c859000f07113010718010340500c41d54002d18a06104100c108180314010902c41280d1403200b04001d4499a0f94680c24039100c0c0c80318003407000c010003180c1070180005088101145810040400b61030b60400c09054008464951600f01c581e40b21060351a0f0040c449140301e6442001480044035005240c01c411b000f8030200110309803040a041c580b41c4070280100041840028010009410803050601301072001a4503040e07042220003204040c48088410701c4403047e0150106450710f074025071021200c0b50300401c01c40309040c3c004003145095500041d0076209a04940848001c108110032690950742c401d0001d91205404501e80b58082c0401e0020039070742a1914040c00003070311040d90082c41c0d031040c5410700024038000d4004210601203c665581034074203c070b501c420aa4400103880c2c1d20245034000b4030b2510f42007200c4550700091912001900002c10401080c000c1044403207160b50340301c08072500017048070419010b80100340c1424 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 278249910 1250 278248660 278248667
    0x305040b0a0b0f0d0c17070302030d0819140708010f0501020318030f01060f0810111801030e0d020718020304020f060d06091803030c0206150f1503090f0d030209030607 74
    0x510240e0052552103c0d200400c00074852402c003403070035100d01c4202c3e03408100200361802c2007540105c6101c05402124615000283c581d202001d0760b8050181d0392001030410804044010f06810b0ba40b00b00308044240f5404c1c106640c88111649008200780d040041080484400c1050895205038011031900e82e0410048440d504444d55554040c441c0f07498684848ca030a0140b00098845e40001e0305c003107840e0560704c0f45402d04081e548810380d403a000002c201b07404000e080701c440c05a80322006000c1980c1c2c1d00100d004140a030f055000c01d0080401c1005100d44c0844c80400701c0318000c440028029050300c90804a100641c1c0c029030004a24140301140d044c04809004800800b4500180f403d60b0f44e00c8080944821880f04501800d410a1001c01c142e054401d0030700050107440241981e24102c943d08030006004074074240300e41040680d1202540e42e030030501c00907840786124240c9138100721400300c0da110300d1511030401034062241380c0f030790252092082d00c00050004004040544681c58141d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 278251160 1250 278249910 278249921
    0x105090d0f1103030f27030f160c090f0c1107051512040606030b090309010815060705030d02300103110a050301140403030501060504030f02060a0c050d0e0f010305040b0a 75
    0x25014450481d00e41c402c00340c0c081c03000d18885c50613914900150320301049010701c65840314061203000c401008102111a50002c29900042500c20b125030340d0300041d4110104401400d9401484a041340001083c030b01c0e0503400041c80040500c80901a20401e08001d0310b14107142d00c009807107540711170340c00c11991400025200c1c0464003403200c145002c00d903000042c101c00c07044909803440c5844100800400140020283c0c0c0070501801031070030141d0640000304180310240480c0000d460703100040c10a44d03545c90442e805103034400101c0c2da680481d80c1081c0065005007035080d995010108021011160040140c0d580d442c0740c0300302d04103ea09590351030403c0c40404003110307008610408003054a031001d1040d0b041d0b031056002d03250303204c1c581451700500391501600101c08214051100f040000d45050440d2a035681c1111030b1901d5504400c0d0481c0c0d220700c02d400c042e0540c41051340004041d90461502c03842c81c00c060707a00c0030003a8a01c2c001501a07030b0b400e403001404148403000003000f0b4031695000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 278252410 1250 278251160 278251187
    0x60d060603020307080601030201200c12120a0e030d03021c0e0a080c1608210c12131403030909010e041505100608091203040f060209040f0c020c030105090d 69
    0x18032540301e8000c645000081c0e0000412030740884010300654ac1c0200000c08a10a82c4022281003641000c6081d01c400703041101a014592001d428039a618040c000061010042e20311541c80d442e851800078030317145503064518060302440c44034111a40c843e000321000508041c0103600e80390500d040c903500820382c2900c030b0b290307601a15810800062103032005050800001c0e0044c4a070707200b1a1002039103550385502044072607009040341c1d840807000c2e03460f406107030002c1441c00d80c0740d40104140604110b42403408002d60040040c030305c003a0780744e0303404400103584000906280c1062901c1c1071650700d1181c1501280d115030b1080c0108036049218411540c064840c90003807950b40218174540342502c10030350750224105440101031060700d80c00821154804940c0c001088490480010342555103c082d00162211382c0072040c0c0014840c050b01120300612018100700821041603104000400080c40c10400501415107458440c0c5414024240900000c03030141006c0507501c10f00381c8800180c03961 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 278253660 1250 278252410 278252423
    0x90304090501090c1b020102070923040f0c0801090804091e090803071d150f0403050f010504381807090c0206011d0c091824030106030803060d 63
    0x408610340d016402418020180800003107101041000080d00440c009910301c000040741051650261303030700040340421101004030004400f0342c084a80380443c00c40c0701c82c03a140e0f030103072130103010800074072803498808540280300c1c481d500703a10381c11214213813071000340b02911103a410300051107505d2b4184d10801c5107042c109004031311500c201080e1016124401d1041d5500340021081020940d08164881c200784440c0d12983c21080c0c61074002035054600840c284c0f0204400f081000452070b40c3d000b00c1b0050f6030010100c1381d882c4200041c030b0b8007a2004a41c112224000e19103900402000c8120480031314070300d03480b2000c1c204035000c41c4510039040240038111164400e0781d01003201d101440144090a2030040c0401c043c280890702901d003000c11703440f000e1540e10704118044080d03440303640250042501d1070f0050341e503d111000a010404075241e5800144004170038401e580d023a800d244240710807e40b1b5083d64a01b80c0800301401c880e12844050001074041001078100d103421a00a89914414030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 278254910 1250 278253660 278253667
    0x519051003140901020c03030c0a0908030c06070207060c020d0201080726010f0b03060d0f030905061b06010b16060506150301080a0b0c180d050a060c090617090d080903 74
    0x51028aa95040c040842c0e920a62100205540b80d2655444260080254909640000611b580303200042070356108000124a14624034813648002d0300424518007181c0d21307104507080907926950160f81031030161082090000f00d03607014440c00303948150018042070024100341c0040d10400710003001403082010100f800e1000d482e200b51151408800620008915810103002c1c1c20b500c20650004801c6990510810195969401c0c000c01d555500c00c84001560580e444e0540d030842c8a50000d660003800441c03044006140415446200c981038030850340c450740c0e01c44284a8900c40c0c00620712813031190b10248030218070a50001a000300010380002d096202500d03400045800a030000c40e80b0b500300003103900c1405036a090141c1c02c0007080c0391071881d2410804941310000299120240118124040c28081c01024044036107901e41108045c40003a04c03100d00245014030501880b40410490381038a141503000708522032040500d1030040180e2001c047c03003511341c601c0090034104240b0040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 278256160 1250 278254910 278254919
    0x105090a1103070507030311090d020d1a070c110904030503180c1002060601020d091d041a010e1603090825140114010902120f06060702150d0c05130519 67
    0x12000b140b140d0065603e2507101d00103803900400b590341000c06035541c2e91052042c009070765140640b001801e0f0381190b440c2c140141398600321001d0114401d01c1d82660001c10100f01c20560040031754294180316003c421101c0480c002005800c017410380d0058005001400040d9050f58841100d49504901404640c443d48417100090402d841007402800160821014040c80756010865007a449990741002c404843c104000c0012000402402d02c94801d0340d0300c007040a0200d110419503c1a00c140b00150b001d6031200c481e081c1c0c110042c1c031442c1c2e0704801c10581160f400d00c603104a0405541c04800c107481d1441d00569040780300b4098802d501c9030381c8005d06040c0090034220101c0024000503002150740084400c20b505000700580c00140c9550041001201d041841603c0e280c1c4141040e070b415600343c40c1c010105185000d00d1000070f40000c503201000c20140d209a015055692a502007801082c0b81010200c0b035034061601c08521540c0355440a000314036120310017000300c0d03d134281092000c031707601c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 278257410 1250 278256160 278256191
    0xe1614160c09060305010b09010b0a0c030e1207080c0d020604031b05100201060905070f0507020103050a0e190b0a0c091206020706050a02030a0b0405062b0605070225030201080105090a 81
    0x55804200b0142e5a40010000c0107028021188203a5044400000c558174001029040c1d2040d8840d040400c00103a05d00310030940500b564012401020b01030008200c1d503000003507a68030700340c002d40c44240b0404c1c48404803441c118082d41103865000c0c0249007024510781c3c0e0202048070900b2415001240c400d808a01c2e0b8840b581040a0f007029a03001195461400c5800421104003400003000c101c1d1200300d0101d1140c01074100e030011039081c03a00013080d603200f119607401803070402c451050340d001c2c01640c400b03101d080f80b0900c98030300c0c0035401401c20f075143c507210041200c020400c04000302d000c4c03203400c011129010181c0c1c101c070b501880c00540f508041d555030004071001103500590a40d400b000740100c0010f14406c000c1c1c44031040c3d400704001d081c030200041129403081900f83c010400c0001d00c000f0100428084c541e0f55074880350910140c01c1095010351281440c204803c10021810f03210080c0721581c42140d4200c03a01a1a1000d181c0d0800c2e0a01010043c01030086040c16204c108400d4444d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 278258660 1250 278257410 278257433
    0xa0b0403050307030c0e0603010b030a091b0501090f150f14070b040308061012020901020708070e011d010605070f02032103070f021501090c23040e161416 68
    0x440d50712250b4a01c1c12042c0501180c1d800c40034141040070344148610181c0310300c0100e0341500c850443c0c10740c881d50b50240748000b80c00035130781c01400c842c1c420400c4851400340e60350381c3c030588000b41c07100c0c9621134807143c0c020810315203449440744080714841000c004a01070f440e400e80b00544c0e89411094002940451400740c4e00407a0102c3d403040c44902000700303050748a805160403241c2141d021a00d00741201000704005070620001c1030040e8000b071040e401d68000c02c40d0b00014451a012384920654404204503070701c00c00d10602030301408050409408840401410707050300c1c040c0d103441d41460300c5070301c5da0038820000c084200d070184918440d03e01c0303c4401d2080c5080c8a003e460110742d4030310701721000900412141c0304600c03e5600c000b140c18203c555420390a4151040c14100050b0113624072000c4503854408100c8070420740a03440e4842900345184001c1040e2480d8580ca1344503078450507442d0034605010403141000136400703a0160240140e440040600344042c010031a14a01551034140e88180c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 278259910 1250 278258660 278258663
    0x1006030e16320a030308101208030907050628121814241b0a0f0e010503070c0f05031b0a110102070501020a080f13080a061a210a0b04 59
    0x30360400078460b0035001c028040c61460090312400c00c0c2e00e14004042090309816020003428040000009500a18040000300080034200000840004103080280840d8010b640d0402c441c09800c0011403141001003c8034041c11203085041da443e1912188512803013904050181080207800703803c1160380311409024050800c204451018089520301070006010b0040d40840035008049000607a20070a42c92034102400051210b00e96990300042d9038406180030140c41421030085242c620003030f4400050145001e46031a207000010305240152100d000891301c000010700e4100051001402143c0b82c0307480180703d202140c2c00e10300080d000f49208070410b031088209501940c90344091002100c071400c06500280040c003d0303c0d09200000752281c0004c6400b030301e0f0400c0050344030b01084a64089404003110751a041c408242c5441d000d0f516090100c00543d039180c1401284801c05a10403003c1e04202001017a003802c0d50000d81102d40301065004114085026451410700451030702c507411880355 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 278261160 1250 278259910 278259929
    0xb1203120123010c02041b08040c240e030a02150904200417150c0703020d09060f030f06031209081009080901030207021929031006030e16 61
    0x503012440804014001640068184942c0700880320070360030800007010303100600703103000396415400380080350180c5049249001c9441c00b0302c02c040c49995201c041c81b030040e4810400781e1105035803a01002000300d2414a01d84130541e00d107800300101ca0050b08000c0c0b25080150590b0100d0485400082040071903c50800304410001202c84140c5000d00c40c1841100001d00410b00c0f0034040c10012045000d540181c00c520040000e024013048801c20405445150001d240c1140e03180480d03115445402c002000c50240c4124403110003040e00030101c00c002d6034441c0d90354110341e04025a04401401004503500c00742030355108080081604076903002d403140c000da00c4120b0b0091501d105607107401e54801582180c540b030004014001000c0b40101d4064000918001d62102c849000003011072040344c0034030b0f49007007910b507000800d6040000f2020a05686100040801100c0740c51460303a8802115440f203001f0380307140280513241c0258000c0380d541c100c01e000c1380c0b1004040f0921003c255019000311506 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 278262410 1250 278261160 278261167
    0xa02090718050103060807060f09030b04050c0411030417090103060906330507330c02010f0c0e040f0e07031406070507020117060f0d0803100506040303090303120b1203 74
    0x41058a001d40241428601000a0741c502074103030303484942c01d004941c1080f48d00c51341c04076642d10410f69803014540100c011452410b01c5e14040e60780301403106809000d6414072143c1d10a20240500380c0780301d250030071031842407643c0c0403041c200254070800806052541d01d01000ca40f055143c89420003510744408545d03071448201a00c3c1e0500c01210208000030b81c11403030301220813503004050300c202a0740501007418894034560111482440c031104401c0c1c5102c104141c91044400d500000b40c010915002049400b141001c4030065501c000407420100d01d15006140709801c0c158000c03460b400200c14000785c102505c0f200a41003038500e500c241ca4858040b413092055a4007070024a40100941c18111316101640c0c1c000307095201c0d01c510302d411308c110303a40006980d910b4507640c03205100340050882241520a18000d0f045800540d51154a08655003000c42c290920b5011a410381e601900d0f0300c800189155011100090380c5480c42107103c1d1070304410385154603000d00940c100e5060380d01035a00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 278263660 1250 278262410 278262437
    0x1504020901090608100b060d0c020d11120a0c0c0504060b0a02060a152c190b030102030c30070818061501030c17010e01060801080c01020706030e0a020907 68
    0x40e010040c0c2040441c2843c000081012a100003014400c156421038045001405080003d0041c06004001100b060610072a0340d081c56000c1125203c021080c1c44444000c0f8224110b640c1e10031540b00d01954209041200c07003e440d004140c00c00815102d1203860403102c1e04c0f08003180980710b2540c0082613600c0c0205600754541e40620400c1d51040e2480020010f090000b044003020140c40c0c407501003000c620002c15101000d01018036900745115242000c0141400c0c20340c0c00c5980b001d09030700c07850a8640003400600f40303410b0003200c3c091101c1042050038004e1500c0d04900c69100f04196443d80120300380d1000070316500e0008a80710303080342e4580b1030301c81c81c0405a8184170b82c003200d0000d03600c1e085441040a41210000390305543e0b2002e10f00000c0c02d000d841e03410354295082c22000325001c01000000101c0b16214003015060301c10035a03c841c0e4a90f610b81e4290780e038001c0314205c140960050101408954860307403162030015080c50031501414495000314124090507108a00000d1204181c081c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 278264910 1250 278263660 278263669
    0x30a0b0405150717041a100501180513020313051209040c030c09091d0f0307030e01020a08070809060d0c02150115020604140307080d020a080109050f0f040311150402 73
    0x900340b80c241114440e4a00e46104014261110940100450b81c0d013400450280100c0d2400401803034801d0f01c1481080c2132440041c071070103600348561360001d117081039940c2c0b00504c0741400c2c608440d4003811100801809600500282d00010203121950442d000c5910100c0e004202c48000300550a1046030b1312000041440103440c0400140740525080842038084e25038400700c2901120081c00d030001e40210b000c2a0014000c0007101d00c2d00c0c1a11849001144021010000b480f21611948804100820b9803006a8840f1210500902290800e019500105881000800c030144c40117003ca45031002e022450011209441e01c141c00581c0301d00c5983e4002c00c2a08400ca000d01120441200441c2c140c140080d41c441d002080201000c201130309801c00014100195101c0c1c60b80820740c1502c030407006406000070740052441c00700180000300001480c1c1c8462203424092400b01c620240142e5402c6002000c54030058000c50420552a83d80d5022170414094004004000b24540c15242018010003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 278266160 1250 278264910 278264923
    0x90108010e04020d030e0325080d08060109090f0f0f15050103180201051608031303021507090909110901080106081209031903090801020f0d1a060d0209040b030a0b0405 74
    0x20300648124034280030150384e07242403d2141550500c1c02d0502d0440210100b0700f4118a80782101c100d440c1e81d104490b4040648030380d401501e800c80101c484010746a28120303400c0f013041d19154049041c50005000d0301c000b94000d10f901c200b29240c04600b41400000c05400c4036924440075110a564110344644a003000d81c21400074002481c091000c440c0100c0188641c2c094018000d06001c800940310080004604200e21565080309000740c40e441d00c001d01841103050100d00700c00502421200c40301c48840700510038001d41065407100501b90030092114007c1585c16019155100b20740c807408155a90041514041c1c2650400426080e180c02c003854586100307112002a60902844407890984002841d000380d141c01c140748034000e401d00d080503600642c243e00000300a50000403c1000440d6400c001c0000030407a62040000b001810307500d071000f000064085030b110104000003404940503401a1030711020013003000441c104044002490022014000c0300c44106201c01c2009200e07050198 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 278267410 1250 278266160 278266169
    0xc050c040903080c0705011d01051f030b01050909010e0a030201061503051b03061c031d01110703120e19030303140910020a030e010e060603070b0406080a020711060f09010801 77
    0x500060403980d401a0003503400078500c490f200d01c045505c60600000750059400c10045600c558094032003408014041c0c00101c5104200e44140103400e2020500301d05841c04490304241b00d131825034204400c00c0b030140700c00751095a10350740f24484820102424440c80014904c282c000058003460212417500c0c251440b1103043c141841d140810001d800b40d514109007850646003807540e00d40e034410000d525440ca20780c28000201c860741e411410103402c481014030b00c1445140c4a0941c000390001160101c0c2c400c00d100c0d0311508600d42c01c00009000c0541118002c056081402c00213a001c4046242114011580f14984c800460f00f081455011720030745032102c3c1501c550141514000460964550300901d03c091159030000c0d01c1032002d40300354040e00349205803078003e00c0b440084020382d540e07500b800d5031480d109001700c00000443c0700325142103c0448429480e44902580d40059200094101311411381780d401c01d00340d19140795502e180040400e4441926000d03104c3d24807100050196905030407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 278268660 1250 278267410 278267419
    0x90918050d0e01021b030304080604060504020f090112150b030307030206100f120305070609020a091b210b060702030f060114030a0201080c031005060301090204060806030106030c0303080c040b0a0c050c 89
    0x411080b0390740811041891a400719000c0c0000340761708040782c42d5125640c000c1c942c50003141c0500080040e1604414000d074000c0300c0c0c0c580103250075401c1106011080c0303d4114294810b43c02d0400280070200c0700c00306604640d10014040c5021000320303081d0b910440d0100d0040e004101004401410300d41c501c80904413100040350760303038101240380003524400c4202500380800400d50784100102504100c44030356020304107403102a51001000085c0c0500320103c02e50f450207030307008a5458410000347d8142051410550842100d07848800c0c01040146615500316100b04440700140e00d041001d0745070100f5007001480158905203000c0c1c2e94811032903070144a80c00130664040540e0344070041c150040c0610500c29525200c03a64524602400c0b60b005540101000c000041d05400031b60292045410a445000440e40da25082500300e85050000130000d02c2c40301e1003480464464074844d0342c804200d086907442e103a2603d51488441d000302c0104000502c2560420341041002c0c8000007000800380c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 278269910 1250 278268660 278268677
    0x3070909030c14010f1b0806030c1e040e060c030414030a020a03140702040c0801081e0d200a050106141009210206040e010303030501081b040b01090918050d 69
    0x76070040c203050b401c401c041c00d200c4803803040e805500000e5001c500d0f1303180301c40c03c01c006001c8104001d0066882807021600850b02e6480010500d050224000001d00c0c00100030060000c3d10260001d1040c4070180e115811942da036804c104142d404006039402010380901c0241caa10b41480c0030110010940f030043c0b1540c03c14000c200c1742c181c0000b483d281441d414103100000f212091a501f845005e0250069400341c03c2086d404800b582242a55060b0b0ba131327900a4800071000300060359400f0f8134482045071a81e001d09520800c141c0308481c1c2c0c0700c00c603115070380c101011505002c41d6440c01c0c826407002d4545940d100003c010546150103d0403111205442c004021078107000043c0c04000c0e648200e80c28006e4040302c001c403a181c00c0c410030641135401800302e619180c03035440c020580c1000f40411404a4a060000300790400c0c0040d00120501030a140090880c444505000183ca1280b500e1414071954110114135145140030301203400002031707441d181d4540d8500f8880c0c03900d80b00000141c14051103c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 278271160 1250 278269910 278269913
    0x30506070807170708040506070f140f070b10090f09150c0504080f10050903040305060112110604030809040b06250c090c0503011508010b0301050d1412070203070909 73
    0x104005500c11801d040521850b5181d910903100c001a411080e0041c030720100c2000308054100c08000d000700c6c0030744201c0c0e100c0c2d03a43d20310035500842c12801c44408a5010080ca0040e60942c000a140d945001c00116062040d031b5914007204110990310001d02c000801300600c2044160710940440c0e404020080c0aa261243c640d552589400d0ba015024262184103041c05039005404660040c0669002c07141248031080c91142c03a603c2c0d0419214420382418045501d18500000fa60260390300040a080701fa46085a012107410702184100c1e0350f441c1c1d401c004203040d918003002c3c000850240030303c01d07540d00401040204070741c1c2d4800c0851040c031041c804604064500300000d007141c0c0032a01100e0210100341424600b502d215402842140e06185010301c9450780200590f049030f01d000042c1090701c006200558144109001d010b04281c0180010012803420758812200740303014520001d41110384802c50341c00c0c4400080e02d40420301d800540c910443c1420081c1d5001451400810032a07480907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 278272410 1250 278271160 278271163
    0x40803010902090406031707020a0806010f0e18010603120305070903111219032307080a08070c1a0709080319140c011a01111f020f04091401031403040305 68
    0x6000350346019901040c80382c2c0c0f0f6155540072801458022462416409124a20782c0840c0d10140040340110101d02000070b24900001d10141039610308600f03145103609080441460080080c200c05c842c0b002800c582035030380f9083c4031701800381d80282c06104841c45180806030a5490151051080201070304080012540010313000d41036980454120b5901e400c482c07545480c0c282c0083c0c0f410003c4003002c506800300b68005075000301410345c1403402d0b002c0307045c0302e09803007424050034402404000381085056001407013013003032903131003102c5081c0502002c0080e01c2d41c005000300713202d8403042d403c03016051041d0903420028420081007220015481c0240100e030080c00e004003111840c05100141061200d0b1038039010941c0d03042d201050007040a440150781801600583c454018049000000e07001d1a00303101140645e400c40c03807a007198040084111400b4001e50190348203200c4c0300c07410b1201007004607041c0203484d620503034443c0c10b8109505605111090002d507a0010003107503c1000104000b520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 278273660 1250 278272410 278272417
    0x2030a1b1101030c020c090c07031403070516020d060539091e0312030423150604020d0e0f071d0a150e0112030e03070605120c04080d0c12080408 64
    0x90030f00c1c000c030711800c1d264016403078142c03440b1034654801c000c84100910300729003c000d412018040c2d600c06030040c4101503141d4082c44166000e0380041c108024040801342070a084c40301d183d00c09070481140303d0644e01c62400301d520941d1000c4603148003074803454611600c0c2d880c90048d0034161181100034504d80108a01900c14150594001c01d03c04a40c80407501d40c0a00012822401500707030303034140255000300851a8001c68084841442c4601d5032412040300e04001c01445080300000c0141d0840307480c0c0d46a40ea2030083c21254001d408014001d0385e05070b50b0103a60002c0d00310000030091381c05916030f02418180541c010034400030450590240508801c1800390300080d27078141c0092080307100d07211162440055001114288000d2000007480784000711b03e801030328040c1d0b95a0b201074420030109038507404648500300004805111524a800c4403000030742c0c204158004007480c050b580c946d417a0500607154007002c0400c980110b10f0042c000a5489629019540d182c001c14916155032519150f00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 278274910 1250 278273660 278273693
    0x10602031803031612230304020111010e1006080f0d08010b030a061505032d0606130518090d05030f0c0901030905060415060617060415030c0602030a1b 67
    0x114001e00d00d5450b03101030089540d400c0100c0e0205410b809181020142c07614002c40c800c00042c1d40403841341c486130101426411141a19680d10301d1038541e5001190499120503980c41c1555035215840f5002004005032049449022000f05d0703220305e0030b40c4090510010300801d03001500441001c0507060341c420080ca064448090809441b900c0c1e580509006150580000842001d4604400c6040340c000c0302441c0f08291000b416900e03208016046c2c08580c01c02c200c52500e4062210106d5504c0c03070910090704e00d4214400c84215040e6a42d400070740000e0f104110441404044010301010f0300742440364030a600140e051040c0746082c00c0041c50300404004044200340c040100c0d51124a80c440e80201d96040d400504440715800d150502e1100c41d450a034881c0041440c2403000902c0a004001c84640b01e0240003110b80c80c2c0c0c1d078150070702c030140c00094054000da640100012000a020401c510040c2800d0b60003980c44013101340d00504035511b0490703540307031014489004000081090032121241d6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 278276160 1250 278274910 278274937
    0x61e0e0f0f0417030109060509060414060f0409050601032001020304060e091b030937020409080f04080a0302060609010b0a0f1b030203070b10030c0b070807061a0405070801060203 79
    0xa50b1982041e07441028104884910000b000000040c0f2882c1c54005000f9503100700e64810301512040c00700b00c116005c41c51202c050100d2480010064074115000500080001e00003041c60609680c9082c00c001c17007608112113a60803110540d4200403030408442d50301d9820700065103800e050040c040d005014004d03c05104e6130f0a54009040210315000c11419041c2010365a0b07100c0c03d040741e02c20786a00c090421440036481444105236001303080c5801d0b0416840030032840c42452003a80a1001502c071038036007682d00c58420001c7c2c8a104891100034001862458043c0c008a22540b03002410158050140c1c1d00c07aa0500700140061440311301150207440c0359007054402124541030603a000303103d80490742a0508018000c000703254011005021040c880c4140c00d045581d981c81080f03030a210b40c000a04050049602880441161802003c0550003504002c0c2401d5040c0ea84d4025070b00d18001d01039810100d940728030030504003401401d0704842d69040c4901e96604004c0c0080d43d9004a10200401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 278277410 1250 278276160 278276191
    0x4030f06020f09060a02010911030115061d09010608040c080102070308130c0519051306080a020105070305040b030a06080f0106030503090409020f130227060a03090203030d061e0e0f 80
    0xe5290441c103d4018940c05041542c40c5c0071a042c01078020040945c080d50380d80d4118500c0b1401e49818480c82010401020386842520304000d000c40c1c1003c1e01511101194841c108861a140c0d02d4607003850081c0404d9076030280e81e1405141c0300d8210000c80d44012031a0b801400380c00d000941100384241d02c005601c50070b01400c1141d045c0072280386080c2d8030594011103030210414941c21403042c5402582c0080e504035189210354880070007100d116101d2401c40340c206426010041d840b0303070020030940d4041d1401d02c1c2810f480300b41000311b5a005841e8030f040666a580c0807c0070000070321a105403011004001c00032240b86803100d54032072046a151038881d40c0e48908000455035140010b007c40180a0008400e9900320364100e0025400500149501c80115961442c0500060040901c500b00a0101c034201580d050050b0701510054000701d905020512003002d06141a1007414010640c418003101c010343e6410905001040e950070884100b07800d002000003146550142d2900100c101078600c0a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 278278660 1250 278277410 278277427
    0x4080415211d030a0906051602090a0608161406030c120901020301060e010e0102100e0f060c0705061015030f1d071e03080301030f0602040506181507050624041e0606030204030f0602 80
    0x2000d11048d100250710200c0c0700240030003151554007150a440d030120441d40c0d03101211010854400340c0703118010524411841425090a2401c061a08140010b400c0f0b4102140345214101c0712500f180c4c1c2440c130380c1d03000c4010041c86501090035890410282400c60080c1d01c40740c0002d40318100c11742183d400c81e440c1e841820609104101000c070040b084415140355082c0900207254950120b102034070284500b02c0410300641001503204200c960901012020b041130311070640281104840480700c1c070384c2c3c411511340b10451003071a0480500c6040f015080540c245002403c18512900d082e00304918069030a0000400324411607064035000f0190030b09502003440e0000181c80b40b40c2000ea044070001c10254441b40c010510200f44183c2101e90280b0104044540301c08d81c050703048080c015030b00407000304824032a050001070310320140c0240601c40d2200388010038103907005980c41070844103c8059a4203803050b903100d0f0324050b050030301d0b09500e000e2543c0c40714001c24641c80c2d0003402c02540043c4006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 278279910 1250 278278660 278278687
    0x30433020f07051210110903070617010803090603010905090c0d030809061b09010c02030708120c150403050d0504020102011d0a0605010b0307021e010f0f0902090f04080415211d030a090605 83
    0x541f268001021103107419103400008000112104124041104c1680041070544011055a20303066000e49074608580c40c24810501400c80602485014040c4108a1900d501ca0740040208540a51183c400070708001c50381034a4000010000303000720382412080c2c0c2c0908100e0b411100612024a02043e40c2e8079140006805c106040d8400702c581d1140c1700301c0c1e24814080700c015002071600350054401441944000f0344041d0382c1190001c0008400f001120181c81940d4031040d006030040c4000642030b4010301040390302110031429941e1a92040074828104109805030a02510f0601107190030340c00d20b01e1010f0340d41d0032541c40f001c0d07955026081d0129154401d500001000518200900000b2901c1158400500d81100240d026502c4000000d0040155031030260207603600c42103043c9054604944050a401d000c040d003400c200510030440c80001a010b0703c040c00301d48848000818006425004451406000d1000c00c9030b0000c1c010f0880403a04090b9480403290182401580c1d8400041d00e00e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 278281160 1250 278279910 278279917
    0x130c0801020a110d030b06040504021605010504030315080a0c09021b01020310030204060602150c0a03090209040506060405010e10060e0103061d01060e040b03030433020f0705121011 80
    0x4800358404190b08803950750108022208414110580307000c0d9100300c000310700f5640c0c1c4002c0701da0807280402080100e820942c0c000c010034540c040b444c0e5010310803a91190b0075110152810740029403901056005c083c88008108000e14100c8020808022181c0c0d03041c500164610420f0766466021444000306807460790207a152811000003107640e031800e0702005004d08018041070b07002d103140c80008900c8500001d01c00012480114109145030307502e0081211503403140c0110f108160716442c0d144016200c660031940110f101d40050710305441c00c1c00030b00c000c4807070583c04640502e400d00103000380f41580d107034503006807001880e280c0305800700d4100681c05010640d03c0410035025007903403143c2980d8003442c0356050341c5031943d0300c0c421b100e004010041a9174036804c1d51079040c0c008000800030102a87c9030b000c804094114a0210241001c400c1c031000c1c5102c944581c0580c21510345c101380d2039410f01452018140031141403980c04440980684d8442c0c40e001e40050485d901e100f05203014000380d080d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 278282410 1250 278281160 278281169
    0x1d0d12090c050a03030f0906030c27090c0c020f09060105070f05120301180b030102210a09081209060a09031e02100c05091c020d0b07090b0d060e13020306130c 70
    0xc9008207903a171400905080322124494006201280003147c40c17440b0340030f42c0c00c1c0140741c0e0303a4083c143ca02000c000c440342c58554601d5520100d91070300010311554140550b5170f41307200b180c9900701e40720401d0042c41130150695502502c6840d03100100503032b903030b0004183c07018203400100d02c80810000b440c00d40d19084000820011521000c0700003c1d410040900c80c3c003614400300c8091048140c0a800c0c9400d034020090307039260110382010a00c1c1c031071084200e510f52003881c0b2040455001c4564503142e0650340301c41c00208510780c11904210b01080c0c01c0141d05e810100b00b1404020b032604580b80108883c2c40c3c04a4100c1c00a48840b000a40c68405c201c034108504640c00c0420000010001c09800303940410049809420b0112107401601b1440c00c08803034094003d010208032401036510345480140c02010300d0244100d00c10302059840e2280040e103120a41d0020009a650601041885015001b0050f90100352800b410070010f880c0400c4c4160800100040c2c0519003a09150504029550313411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 278283660 1250 278282410 278282419
    0x106032307050306041101031808040522020f090a060e150313150c0f050f030106050a0c0c0605270f0111030d0207110907020615060702040914011d0d12090c05 70
    0x50101b40407410078104011300098a0030000031400b141e40040348032000b2400340001400380000c1100b0f00744a041072411070100c4c201d000310307040500141000c0380c019000344e010005d0007044a841a05159503003c0c042d00c0780b030a00f108408211342c00500200c2c0c000300e040d101d006001c0080380418440a0608140691019044691030303408104440205411013020002928540b945045980124221407610b407580820380e20750ba00b020000d40b40d50f400728401504102c2240030131000700d007610748103101070007080ea5516900c035958101281402c46142c48409100d913120390751040f070761b034000c00d200b0b6801c001e0070003a64801030501c419080d8000c03140aa8242400040c0c2341c0100601201a030640348804c880880040d00c40d424103da48500403120107c640020050002d01441e003400645002c6100410100e9180020f5039482d170190100c51503440315a44803c10981c035401c0588544901034a20002010040d5100c94002d210401c0e1101030300b0000c2c1d5410303c0c0014880e0001961014010160 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 278284910 1250 278283660 278283673
    0xc030902130b03120403033501030b100f0b090d021909020304060f022a031603110709020f070201050d06080f0706080708100302130f05240301060323070503 69
    0x141c20400303010003140c018428054480c50401d0403001e6800d40c0c058a82594078185880000d214203d001401e4000c1c10403000703074a41d65001c0002c0101035a40c041c500c251000f254a0518181815000c1000d403c085414040b0340c030240101c0350350300c00f950300440088941602c204824008280101680400001c2160480c0d00220300d54005030011801240300e480b0410100340a03004a000b2070041072030105150960020340d54800107121162003801d049442524074284030300c0314060440d00d030244200d02040d00d28801420030402403106400074000c120083d4a841000c00001003d0710411100034140000400c00180b81d169940c05040646180c00c00c6802c08600500c1241d0307240003034414003000034011070000da02039224401082c01040480002030785981141c0c00c00c0401d0303502e0700346200c0c25a0307540d81c200080052401860300404054003e040041172000e00308001c0c0880090980c0640e041c0b41c070800026042c54660817414961500f8041c90080c00c04140d400c0004980c4074503418407904 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 278286160 1250 278284910 278284939
    0xf12081e160c0e010e040209070306120b06120a210c0c0305150a0b0d0215430503030c0901020f030304080414030a020a0b090f040e070e070809030301090c030902 71
    0x40210748107900070b109015900703a0300e600e885000202405048918400c2d40c2c0820011f08054a1894002210307080100d41d0761746414020035001d04200c4243c51080e2038400784010740c100444e00104015107a0090b1441c4d0080ea11082c10072629100c01d0b0302d6001d050040102c015210f8400301001c2644220559213040d0b5909241e0ba4410034441e1030040d1008000c0400e01c249000d119007104c8001c0680100c020301e01c0e64003044103655800e10b054660010030444207007a00c1a0039080c0103041d0030000124150210460440301070302080120030075031200440c5080104100000781d0703034403600b1450695640c2c007040e00102e00f4840e4070001c8401e6131102001b80400c006c41000070300240d40025000403907100c10041090f903600c4c0309050294114002500c00e000504e00394004110090006d0454440c020341d540204040300d60194542e20306130412041031118089602a02d07800014515140c511410708001440c0c40340700c1031103030001c016540c4034101111400b907007103d08056002480000b880428 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 278287410 1250 278286160 278286187
    0x130e1f061e0f050a03050c0405130602031006030b01050c03040e04030c021002100c0f0f14041d0103050f0309030706080912030106110c01080c0906030a0e031903060f12081e 76
    0xd4000d200b0854244240424682814000e51040700e80110040a41d29240381c03e0100401001d0508587c00c0700302d15102011032020300003140a016215804400030307280000080840321401c40300343c1008410070182c0300e541030000944064a072061000103a58607070780f80959443d078010320b00031b4201d445036090200240c0c011030000b001c0c4614070030503c918004490100c0f00707500d080003e0804191080c42020b00184211302150552079004682454541c950b14402c440c00780b220314040004001200501c1040700a0009200780400b68000f58284520382c40001d84990a5004130410031641c1c500107030091204020311b44090099a000c2030ba2540c44940007000242d072144400007512400d002c066255210320f280030310821003108054203201900003004501d074030142510030070907203a0070314410b4072209000070440e962441ca0742d00b0443c26800d0025054440c25400440c6c0110745850400665421500c51146154803562007030342c601140400b4079021800c1490541e800502155004d100f900c0f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 278288660 1250 278287410 278287469
    0x1513170c01110c1b10050a0c02041a0112140c250b060306070207080705041808030c09131104050103050c07141014060d081308031206130e1f06 63
    0x83c01419201451181c820fa440b50b00182d2001d540c00c4403500d0b5031070304550302c50381c050040b00a075468640a10b88458000900b030fa02d444992945060440340241115078100c09801e820040a1406010000400c8400ca131050f5004160070040c0300000b070f604030302070800b280609000c0064002c800d00180c50b41028140c2c9402124030320300074414034010a000e40d000084500446403604014892a424001440081c0024140044448000103070500005420b080518441c0f8003843e001510b4420a00820218140104071321104520b48242c20303440301840021a401e1f80c0d003e081c080f074141c4034844100c0040c465044003800b252949081610300d89004608105e440c082c807203051101201c40c9128010403001034a1956205012201c003000180b80345000c0d00c40c481507031700c902e4074550703489152a0a6601540c0c40c5426455401e040029902d000d60810340c410707450040c2000280841c0081c00c1d5038034000c0e69520b100c4902c84200c08061640c580010004d404c55a088580d242003490540b0b14050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 278289910 1250 278288660 278288677
    0x4080906070822030b060607320109080a1b15051801451707050f010e150601020a020f04021306020604050c040b0d08250f0201021513170c0111 63
    0x100d02c501251940c0741a80c15100055000249d00d40384500900d0034181d0001d415812030140ca48450b02600001803c0c415900305c2800381c1c2406a5541410200420400c20020310500380c0301622440f1000c0340841c440e0404004a0880016668a0f003a283d200c92640340041c0e03080d65800c3c141426048030741510302d10360001920142c000c030401344021400e0402004000f41654400c0ea804400102e40c1c0f00401c002d81c07480c2c9001c080c2c030700744c1e07207484850420729403400507861760b911280010ad510ad010440d181c0705251f150a000041d04101300000c0d00c0d2958607201a00c28120380e542c080d6039503120340c1168003940c1d81c1410300d030290780e407440c1c003035210401250251141c0c0030308401f84605082901443e48030100051014030403000f0f503aa01207554000401c0031307061044911941001c1e251010b10403031903e000c0c40d0b0a10414003207100091400181401c5035010318028000e204610300085d4a00b04030650040c0e5680181007d908015180e0080c2d0008092541c20091041c00070f82031200203144c2e02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 278291160 1250 278289910 278289923
    0x1b030d051b01061205010c0906230904110a0206040b0906041a1038040e0106110c03072607050a0636030c0b031b030702240106020d080408090607082203 67
    0x1a42d10700c01a80d0180b069800d007042c079100c0e0322b8102c154690900003400c5801000b840050000c038a00165003503038119600c40c2c0f015078051424001400418030059a05c103480000620b1203140aa440d006080890006103901d101c00b20007103510014a00782c02c40207812071120032400551031000c0003043c40048280346c3c001d03c402100f41c0c01d0f003844203001c680070350b00c260215a555900e804411034800030b018030300568600800702d071032040e17a0b02404000020030006083c0c50000e14a01c407107603c141064100d001503980407032001c000c0e54440c0c1c440301d01155907a0602d042042d00001404846400040301140030741030346152401551044101c44064078002e00341100c650303480b9001e480e418072040d1044c1415851217206200701c40c0d400402564003817170345c0c130544e0500b0500c4000c00c0880c0401c00032070351404040c0001031011990412080700383c400c1602e0203aa0328249602d60036001c1c860007002e1402a076000400a0920218030704560803021a0508644108070300c94401a52040a01048030380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 278292410 1250 278291160 278291177
    0xe03030709080106030b04020f1c03020c0906120a03080a090b0a0c031409030313020d021e100201060b091014070f0302010f050408120a0e030c1b030d051b01061205010c 74
    0x102c0414030903002a00c0d03020b2581001502e45808000310344034940e201070317480030b000302d0340c12401d80c7c0100e103a1184502c07980081100340d211208220654100601e01c0d4016019428440d1520000003003190700e942d0941040b03c00e68940c00b20729000342210321000b0340074005910034000448040c0c0d02001403421603035001c005011800c1c038030038004001928040d04030343c0b051010078240c6c0c00900f9240046840248030910712032003a40800c1440e6299424400c41720806030139401281440c04006480c2c40f0144020084141000d04e0fa00180c0100d0b200c0b14084e502c09400030b81040c0c060300900c00c0c40041d203084e00e42c5450542c03421900c000ca42c01c000b18015401c281c000100030712307030b405401d00843c0e00549081c03c1c007030a68505040020300030800030585844800200d42000144024030103c0c840c5005403610040c003000d03801000e4003071a0300c0c600030342c40076419040003035001054132040d80f40c4c10301c100d41d250000c08186000d001c171a00000c91a44441076a4001c02c40d056000b20750007081912080300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 278293660 1250 278292410 278292419
    0x906070c05030c01022e180602071a13030e0f09010f030611090105030c090a0515040905010506070b0c130e07090806070206010312030207020310020f040e011707090b130e03030709 79
    0x200c501101d04400d1110012035981d034a41c82001c07052508186c85068000303243c0c10081c44244000f0031402c0290340c000d03800502c000501c240c205203403004d03070000d00e82e6507454203110807500050000100e01804204203030483c0d09407a1b6032080e40c5690320b80020050419561500301500c01d159081c44211260340c5002c03d41004170103150241e60308500c058403841d05540e00d01c0305040540d48030290790382d4071416810001c80c0680c0c829002d05404044001502d03115030500c00074004481041e04034500c40c000512090700024514100b076a440051021081c1c1c0307458142c51501c000c2406604510300c0e5600c00003c01203659400403462007160461003c03a02c2d1341e02c0d008001d036100c11003800050070007020340508029081c080c0d001400214400350480c3c4404240c0c420313070000c0781c1120f2090441c0d401c00280c06c00c4800c209103200303030262290440e07000121442001c0c055881045116042000d074440074280915600d122143c14901c0c01548144a90f118000503940c4ac3d80c001c442c02c1c00840e164040124 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 278294910 1250 278293660 278293663
    0x30708010e2d090f0601090c030c02120301090207020a0306020d020a08160804030f05090904060605040605010206130f0312020a030b041a06030103170c0f06010603050a0509031606020906070c05030c0102 89
    0x2c003203180041000a0240200034940e46910042103851107104c0d02d494201c401070100032441c002e0040350400954080c0c1c40c200181950403243e00d4404540c42038103079008018840d02180c0c119103103500c0c0141d58103207500c040750320307a1b03003942c00a40054400728030003c2492558009200c0803503241c0d100360142c0d4074a07180c0f5484100e000e09920012b16010001070001c1d003d02c50108079100e840c10214200402040050303003094045404441c055240c20041009040038050503000d413509001130102840d060b030480c2c00c000c110074000f92004008024602c2490b01410919080180c000d0080d96140e2403410301402070850300a030103018510700000756031075001c109150441c038900141002d00e5a40b03180c07181000300d070041015000f5242c0c1003060707924803501008402d01c200c124501a001c00e61500c0b82c09800c955004100301682c40c03d040400170511408011140d1700f09502000540304200d80c00c0500084c0501600190441c0d80012100f06208107103800d1411241c088040b0b50a2000314001203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 278296160 1250 278294910 278294941
    0xa150203010f0b04081b060c070b0c0f0606011d01051201090506090601050a05070807060e060403090807060c0804030813030804080c0418080304020d0809090c03010503010e2b14030708010e 83
    0x40750016086d58010080c4010300440141000304801d0030303c64070b82a42070500400e94018094580d00044003200c0c00c1c01801803d20340104480942414541040042e041001c0800002c02d002c05c417040d0912168024401d60741900c861480348900740d0b07100e00700c15009110507112584103030800340010300c43d50300c1041200d41480c1141d0340c40703040010310703a5140e1003078210340ea013218a580c48100c400640380702086141e1007940281e841d04000c40ca482c1c007540c2820312581026082144407464a400f0906540c00c031030480f5400003903103a48a00420216040382c20b2a04010079640d8000f50021303003040f00090307aa80740007041307804106803204880104e2184e04250740042448005100040140c585880c1e4036526502806503140340115003000141210400c65032104190343c040014030482c1001d2003007246442d41c0400038001d80318030488003a200325600704c0f2641800c62042604e00c0061003500d4149401c084090115160700300400003812500003401042001d051070800188241e5100400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 278297410 1250 278296160 278296169
    0xb04060c02130e07120519060504020109090e0a0305180a150323010911070f05060406140f01030813051201020306040c051e071e050f06060a030c050d050a150203010f0b04 75
    0xc2265602d0081a0882040c005c141a9a07034084c459401a084200c1001064083d1282c00c1c0000d05184c5840050030b000781941100320324600e00400358010134400201c0c040c0003900341c20300302e0701c0390390b01d041c901c1c60300d610403e08980064038823400040d889030407541d02080950310b403400d0010950101600b03d10800031001d01c20900b213250010000302c003260380441e4041024410f664074204c561b840f56889245c4500c030031503850b0b00000c1044103108640c8243c955581103004070311402d040480707541401c0c410600000c0c050481c001480391060301e01c4150301000f020081c0c5030030b007900c5003c00414000c4d002181e0f4540268100907002803038500c2002120400441c0c071110b84206030b280391859009800422003210b94246840e010011002c10f208651501c0d0b1103040103003200307543ca81a0390b0500801030308150040380c3c80b203000e100142003d40240e0603500145c2c0c405c0e00641417800e00615103e200d21000d04041c8180925581c10350072900150305840901c0d803c010b10300c0c2d40300114082482240716 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 278298660 1250 278297410 278297413
    0xe0112020a02030415020304050303270a080a03030c020c1c060b090601050a05090112050a1a011b0209060a1a0c1b13021c0e010b09090616050a090b04060c02130e 71
    0x50140c600a50342c1c90b170204400303204907400c2c03d880b880400e14581c094a80c2c480405816a041034012002104100020742d0507621a000c0501e007402850ba5447c580c1c0700202419180d0342c3d1100c1e070620802540c3c1c0803200081c1180f00410b1001141c40900030101e40555010f810680c07541514102070503064080c050695a4a02e0690041c00031185070b042051000c0c10132031148112101e40c01c0c6406850b0040c070f00054005071401b054000c00c0321084072002d0700717070500a441c2c400000d18006540c40b1141141c0585602c0c0c0c0c5540c500e80080e502c00440d8100da1243c46111517452415400b8074090800b01c4031260440341e00e020209a5284051000c8100690248010006030203c0c8140d402501351844000481c0c03070703500207a80c20700c02954410b840504240e955410114440d10340140425004403070030012b003095050074020f00c0c008a03a14900791040c880c2c0065141e50380e07440344075030000401441e01e0b9a500e079500d40718003c0c41c0e80c99100c0d05030f204919000501c007580c0311310f10520401002910 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 278299910 1250 278298660 278298667
    0x9030e0a031a040809060a0e09090705092d0f0f09150c18030708031c11120403020a060203040b010501110d020619140a051f0f030b1302040c0e0112020a0203 69
    0x2420b00414030000b0011544400f00307025503003540c4c490b03074050f10810803a620f0350741c2242c944205214100c0303002003c402065000460400485e102c200d00c030b5802c0001301e004e25042000801041c1050601300c2a084641c526080820965107100f443d80f82c00361b048010414019110381030603568030042251a00c03000b000d00c4010410b80c0c1034000041580c02070002e42c0b4180407120100103400c0a4071503014044c641c000046904034415a410240141c540591080004221000e190801d50003203074806147c80100300003240178540200b01020550750301503419550392500c2d10305040c1c0140203104075408987c2c103030f11800305140c0210303503520740e20b6075a0300600715a507510341105020045140312505940e900c40240d40340741c8404100621030200f0603404550b1b82402e6000b01c00703030100034410ba0441c01101106200240105a07603508803604040325824030340b103400d14440203c1500400a40c8580340c10484611207800090814005809881c0c000c5890101400442a40300700c0301c00800603082003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 278301160 1250 278299910 278299943
    0x306020c120339070c210c09020901050906030a0f0609020a12050c130e01080c190603270308090c0301020901140304061d0604050721110f0901060309030e0a03 70
    0x1101003d640e103281c005609000c2c4035444003241150300141042e1080b00301140300380080700c440c0c4481204103020018030109250b940d1520f003c520368a014a219242c0c00040034040d5a11a9040c5d80040000a0800303660382481c6070848000c2041602109042e030401400203140030151081d1142c120454803854001c00320612004d00400780109003070076440f410320a05000c7c01c130f1301c0119000341a144c00e145c0c181e941090380385031038400001941071003000003000f01ea00109078003491000301c41a42c100440c490050326200e25100c8154060103100500b8800c54509160340038030250300601840090303d207080000b80038107080c0c0c0b05460666010800050f440c10185004400035a4014020403001607260041c0c08602200c0514017180c00003540440184000d201c01807001c58010300c00050300806c1c080300003190303003040071098a001c1c180c10000c0c6a41901070301d40e80da02d2050940d0040008a007503842e104060000c03d0b4140b404c1c0c001680701c47c4501007606040b1804001d40e074101c41c0381e81841104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 278302410 1250 278301160 278301211
    0x18050c0f09190305010c0306050111030306010f2d120513080a0e060d050103050c090a06034202181903021c0b2701020909070f02160306020c1203 64
    0xb450421082c000440001001c110b080c41100c00030b04403030390301250440c0b420b00018407071161a0000051a0406c105000180c6e80003902d840d00b125160801480c42c040058001d2050035003003240f0040c1d80f981c1e45480c0c0035554001c20030450f80c50201e44c10401500d50f00e800148481c15080b0090080d01c0c00c01c041c206d00c5008000304c4a000c4030041102e4503050070004044141d85080e4800c035000d902024804c0103a00d01110354030783c4921950ba0070000c8900d107131034040a50340840144408103e9080d000c04500c54821f0b050b00810b90040c4603035480c001c8612000f0002d62013890140600c804070322038130f0204d01d068040d4140e001e08039405c040381e40707081d038003040700181510b0303507011420000c4402480015a2540e801d071081c0450030102c0401301080b003c621400c4820050f11303515074410040f045031030340e0f0007a00726080429407500151251003c0416031811041044042142444c220000100140d6230020a4a04841000d450106842da540184103000c00d0380d5426480540d02c2e0081c501405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 278303660 1250 278302410 278302429
    0x1201060c03122c0304050906191223100608010c05070822030b04020108060a030b041103160905040c0b030403021f06090501062c01020705210718050c0f09 68
    0x650044070b44a0312003c110100345030300d5525550032550004a4100100d242030f10000b94881001d8903808480c903400c02c0380050200c0b0b00c0c000d00c1042150f80100700244441414002039400802041192091003154140d549071000d010900c80b82c0e0800d0400f06008506008805045099031206810305010b6a2000c2154002c168114400c03003060740f001d40d054000e0101030000398000d2003800713041d04060000414072800204294050f20300030070100001820285220b61150304450540900d822080010781401490850080700c4803042c00b001c80c10b41d0b403d0744984e01440c407514130069030030b0303588814107400c1c04200c03009009a0031884540c1e084d00b4408071202c4061004090006281e500c1c1c040c1e071000c4440a801050000c0c3d1000003640304100b5400034079081984505810721600281304c0002e40d41d170801d0007200d008180c5040d40400354424100022140c69005040d2000c0c1c1d516004041c145010002c17050404a040c04040b51181440c1000c40f091890050b07802890300c440070042c00100c3c113 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 278304910 1250 278303660 278303681
    0x3060209042409050106080105130506220606080105030a05120f07051504060b090408090609030f06070806031506100309020d20120102040e0a18080408031201060c0312 74
    0x6403910218504244400044003101d0742c92541d003500b280c00e040d50103003110b205070001c6060014000040c0311079642d00340142d480c500c00c0030000c941a42d4400c0824031480e084c8040d01c0f0302401032000031003550003a82002040d9000c0341d41e030070a242c0c0d9510425070f4981d030005000d400c41d0000514203008100d0007000300a1044100006880c044090780e0f1549050000d80d013420f40a48810184000c0003c030b8000c80b000104210348100c002d0501d40c40d800c0703c1d0f10401d04914400c0c0c00004406035251420b221590040310703140140d0b4a00d241c401005024001c04481440c42401641c9507040c3e02600d503071006010342805000000342c2e009a42c0154020300841c0802d0f40d0003110500e040d170004019418001d1504d13045100c22250360b241400b170265404000c51445203c0c2d006100900074036150f036142c241c0c000f18104010075241600003184140110155024000f607a0004010030a254008001e05144050400c2040c45a0366690211089100228010005000718900468480450f0800701d031a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 278306160 1250 278304910 278304919
    0x7020d0c12060c030c030c0e0f04060906030f030e0901080c0d083105030a170d0b13020711010906122d0e100c0903060e1e0c0306090f0703060209 64
    0x3640c48001d10848121409021107400e070b00c440b1189a03095150081e81c0c1c200d1071609051203404031859015101d8905019082d004203644902006143e5850300080d004100c1e11508000090f100d0504c41440580c0e50070580104002185012aa042c584181d034100c50034040038048982d90700e41086440b80a46400b40c1f030000e020f2000c002c0c10400300248204070032592401550b050014440c822480d281580f180b8480e8100c091024041035610340198500c0403d908000e641e00400d046410040c02e95955994010307090f46101851040341c6c2e801890054024228800b00c08002c0004440021450061000148134140326000911054020720100c084652540b031100011a0480c2407402050542000464550000303410001060101d500030b50131040090001218515001d040c000c1a807100800ea16691040e88048a0041c00310103500e07600c12203081c10107542c000d01039580d404030300341d01486406480045060424001040c01c034901040e8054881c0e98030315202e4400940042529a400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 278307410 1250 278306160 278306183
    0x6160204020702040e1b09011a031f030305031b1603050304050705040507051c1104030312060e010e091b030d0c030c0210030603121107050607060f0e0c121207020d 72
    0x16aa18021050344c10310b00c000400300711200e0021b14521034404008a80504c41031030050204201c8106105821110028001d0fa02e44416840c1d00f11800000721380201065118408803c0503485001103000b405d10354001e944103206d101000c8000c0c403030903403820041d803104900480000d000c2c330082c50344140580240d07203107140d40340085810780d481141c10400041000800d0140e178100e801128001c1ea03c03001040011440c200740719074851081d1301015040c040c12008aa4100d44140c000c1d1001d0b00700f40c0c815004a583d80c28110000910907121980580280c04d5045045c041c130300209044240000c000300704207440340d101034480001c0c1807815805c0000c2c900382140540c94841d2001c84481c4590340005000e499401c0c8541c2c106c0740ca280040401c4060000c0c60a04103000848205803001150403030340d1070490745011801030180907815110316041011021050381c1c0407a500e4003002e820380f2105142807409522a48070760000022a4407044103202c41d9015041c402a400b500764480c03183e9480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 278308660 1250 278307410 278307413
    0x20309011218140d0302040806070c020613120201121b1d030a1109061906080a0f090c060816090326030903071a090a1502091c060b0a0302061602040207 67
    0x30040c20b04810b64640c4400c2c0c0e80d01c500d28004211603113520303429240031401c1504000860780c40d07d002030030310740c00c101062100c1c0c0103540d585001c40d401010307018540c030450743d41d8a11070000c607804010240c0c04501e07134107520350300d844a900a50700e17100741e000440b0000064062090f20700300d100d90031544040954442c001d4054500b0012002840c1c010303903401c405605441d00700001028018800c0d4000c0080e55070007451090414076580660310f8604040b00036595003044500205010348555074020700346144a800d2066441c0c8036410744400341c1c0c540f2007680d0303a0351001041d01c1030114028001a620102003000c01c90600701c2e20702c550111600301c8503c054550314004203400c141c9001c0c026800000303661081000c2010344480000074108510307040e1810700380d060345880014402901c00aa040079104111031070f0350458040083c004d10120604811030720855940c11244022107000e45495074450841c5032110084003100d60091507980f034403503020701e0f4040b40302201400300c0c1c005409018a80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 278309910 1250 278308660 278308691
    0x7020f1605150715090302010f1103060913030503040809010e0a03151d10020f0c07061806030c08180703050f0304030b0f04050c011107090920090408090d0201110304060f0801150203090112 83
    0x8040c80c11042d0319070303101c0c0ce00404010f5050300241a00c00e03440311048050000030b8105013a0f1b81d10079000340d803240d1544552001622050380c00c101b500c2c0d004540c942d000c01045034080a000c0c0400e0b00c0b200030030298a44400412034003654400c0408142c0c030141045405007600d07001402c602c1d20f0301014904081255034607610f01400c031780024000c42c0070305039040314503c0240c3c60a002091a4541444200c01003075015102d6840030300141c0c036030004454200884042003003c1c0b00103540c00404c031180022001a8251030f600076010446010b4842c0c004103000980b03402e411030143d40c001018120b036420325001560305c89040a203d040c0c8d0f00900400150548141c420b40c0c03c1c84c1d0241d40000608009030b8001d14403903d8402c0c8003885004070b101072201045e1000c0c01e544000206899045105043d800180c0303c500804c040240300b8480060003040c43c60784804003201805440c0c440d6011640c03551a40b0290048901c81c040041c0d00901c10300c462588501d8034500c0c12003690500140d0200300d0000344 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 278311160 1250 278309910 278309921
    0xf0607050307060509060402010215070903020607020616030503190504170a02281406070806131404060204060e100206160c0f0501050702070504110304060507020f1605150715090302010f 82
    0x445e154010a0402003556010f002000c08000501030807811803512441c05407141c4040e000c0a400780308013280700d5007191a07034001c956a01b8580300000514291030301d0014156442104e07000501e00c0c10071904a5a5160781c05001e00450340b00850703003290440201c0302c06c0242c00c0b0801a50452068240310400002c40300340c45212001c2c0040011404812814050101030910a60811552280003004807983d408100c2d190003000860381d2480c0615910408270180c00c0d6812100d088218500920040004a90003030040780c0041d02c4140c0c0d100700040410484000c092052405a044180060103c0740c2c640c648a258413800c0c01c112000d258a5180c42020081c034400c110f0300c51b95a01c09110801e0340421900009040498041c000e02d031810041511600020b03100804050f00c5401082e00c0c24021300c102070b030b0000041e048995040c0c12090f00884450548a001d000d01c0035962682110200102110340098100142059010490314920000e000c0002c0a6085543e2001a4181d0035080e0184 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 278312410 1250 278311160 278311171
    0x9100302040f06170717060d08040b1305100203031905090a0b0103080d0605041104030f0206090d05150c071208040f0b010906060201050a02070c060c061e0603030318020f06070503070605 82
    0x404d000100800e06010205074090094001e02c015082d0320341310748043e20344690b4031600582c0e4038103083d102e500e0104943d02860300600440440801d04c118a0340b44903420408440089401c0301500c0c494040a030380340d11003540e03408105c1c0032081048452000302c0d008241c003d12a41d0442c0c4410060f03484001300c00c3c00a8004640040c00003400036088481c41c05404c01070102214104410313034200760401182d12582c8401000b0026052188043d0b595a20a40c0c0d81000701070860390009440d40340454450b081d01c1c800060510080c404185807802150a50712020380c070106d03403561242e030464155800b680c001c00c101c07501381c44501c82000044040034014002d041c96400401c0e154100400642540c0009002888080c411702010340890742c0140341604461070b50600070300907051814001c0160200b0146c501440800c2d903a00700960759664400001c0700d01075601003044d03034940140f40030803081c1c588003e540901e02d1900d6080a1600c00010704080d442001107030b1425480c1d98401041d20400c40304c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 278313660 1250 278312410 278312417
    0x1e05030a030e060604050f130809040203041202070603051e04260a030b0d02032d0706080402130207110411091806010f050a0813020d05010f060302010e120309100302040f06 76
    0x42c80b080716201004000c0e04900d0840d8144081d10301011b00484114004110320280c08c000003181d028001c404003110211b01010b0020342d5645080d007032180c54500320032070240061042c010000360700d40c8203110726800b92002180c01aa03024a01b80002614a4041d0095402029100005a140015880306407040001546181d2106400c02020b0100c40c64080f596000b0041d110345140140d4022944a80c100d5004841e03040b02c2240a0039001050000c5d07080305054031034080301044254102014900c1180300326504441d0000040301803050340110390008014400c92103540d4414070381900f00c10310000080c080345080c0f00101c0c001403642081c0d040348a2000103020107211540d64030803010000405182080c0b460b010502c1001030010b40001c00003130040040c12686011540c0e0441d8000c00c580e0024001c0c460018041c168070010106c0d03101c100d0203c2c92340e403c0c018060400390718410121401c50055800c100f454028000380c44070704078102082560030000420701d401e2030031003500500307025076 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 278314910 1250 278313660 278313671
    0xa03060e1305010515031507030b06040611060604020403020105120619030804150c0c0303080c0405040501271107081602060a050301090b0d0209070509030106091a0f0f030a1e05030a03 81
    0x2d00b1400c440d800790014205090528031003925407800a03024032141091a175510807965a0303042180280850002d00340c1c403c90006000401c0c0c1d50001d82c1298000b1068242c6500d503d480d0108801c0b0700c078510000340821000e01c411180411001c6035240d03c280d014041e540e2031950241c076400d041070300d80c0007112801008a4140044040c05040002c55142400d0084039421151a5000340c0340044c0f00c02800c100342c6100080340c80b00315000b0340300107020140007400b15507140c540f02c210389801034980c103495507802c1407035142003402405041c03a02c017140b40e1031921f000140d84a03445030364000c00192080c80d00941c00e90380140c40d8400100390711f0300b19a513640d40b2541442112419102003503240c1c1d100b0403500d41901d000d41e5a02d0302c807582103001c50070031a980f101010042809009180d0010303002e40c2c0b0300342c00380d4107104582c1c551b0a031030481142c995112040f50801c02c401a80d41900c800e40541c042420321303000600c0e03012204c0034054030302c5940d080c4e00420340c2c600746180d121b4103045000030b4959 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 278316160 1250 278314910 278314913
    0x100804061508150105030d0516050304030501020310062d0e031f02031b040302062502030a050d09061e03050403111b01030605090601140901090e010f150f0203070201050a03060e13 79
    0x1202c3d03403400b5001c1100034001c5a00c2c8410024002d0244c041c00c1c9204880011182e000c0190030800c85000f142d000d0003e41d2689410b0784a80b02490040c0301d07040118245034203c0d9174280213062245030141c0b000c468941d150204c440122180307800380a81c00d81610401c002c041803401d55504050402a1384c80016a50740780c105c5050b20082e031011044400407009000610050703890b1390507220700640545048100000102d01d036aa0070f03154213400ba405d40106150082804030100c1c52030744003840b03610f600702d425544100807644c0d00e2000e4101c08400012880100e44039220341c0050340c10500030724015010410101040f401d080703a03158101480a0f807060110410350f01070084000400040b00c07403038000e2610740c0001e449089240844c103a0072000040c11500f41e800349024002424034444410325a68480554141860041c00b802e030156600809120b007080c0b1030410244c5110b00c59010f07508060043c0d0043d01c0c641c000914000c281903e44102050302011081594807c031038113820b0700e0441c9001e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 278317410 1250 278316160 278316193
    0x60103092111101a031f02070c03020d050a0b060f0a1505131e140303120402040f060905091002090a1e1701020315010e0609010c050102040e0705030405070f05100804061508 76
    0x500000c1030280d049100010300090407100011004e8600b10b0001d07991b020289428161403089da08000d602420007500082480000a40303030540380d2154944c00c500d07480d10410002846941c02a042c0d024011490501400d0141040058456000e05000d4203080829040b4140d6a6581c1c00c501c1c0300e640710948008070550041d076040d00805490004003039401d003150100f41c49214489501c140b241c441c102090441d26249e2101c030b1000e01c0c3c464200f20054440b415100680420340d42003003240f0031080c1054004145100b00e480345c10006269940d5103142544d03054440c9080742e0342400c811240702002038201e0212540c042c854002400051342c0340741030507810158840341d00c2024100310307100008441a441d4081100d8140c80c3c00d0030000b00aa109243c0680a0310440e007108050f00e214601340701d0119041005140600e100d20107680c41607484001800c09603d0714410035600c0203803294ac01b51298096484142c205d4024100451024805411130321102a5640010044d0780a0803030a00c00042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 278318660 1250 278317410 278317451
    0x311090f0a33050304170901021e030c0111030f070f02010905010603030e031507090b1b1005010f0e1902031807030c2c010302060c0a0f0c090506010309211110 70
    0x2514240241142010b03246d400d1840100c2001950405000640c0c40140e8000c0080301c01182ea20281c6160f6206030000b001e0f103a82143d001c3c004250b003005141050a081c2c40180c80c03051215a410b950f4980d196542100c009401c024020159541d5101c100701241080c002d80c009107000f80c80704e24808800d002030502c1c01c0c00219408003925a482c050107840355012811904448049004e20b8550301d50240310b10f4035903191000f0400e184241103001201340c85c541c003d40d040702c02851005214940e9031340c0107441c80004a49032000f03000c072020120001d04a6502954009502111070582c14040c4034820f85050030540041d110802e04400401104080d03a4022080b01032600030340d00d00d0080903203d2103400006000c000d1003000c0100c0c0c000c0c1a008108621224150003011500101c0c4160902581c6121940190b2083c5810400041c9aa500070301034007236a158800f5565824040741000104211640c040a0080040d4280ca00100840c20094080c5400c0c2070390380060488d50745021416000e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 278319910 1250 278318660 278318759
    0xf16051b011d090c0c0a0b01060306150c03181502010e06061c0b180d0c0510060503030306011809240510080708040302070f06020a060501060311090f0a 67
    0x1400c08003000c03180c40c0040d004520b60009075001142900c40180103100c0c0c1c040c10790f20504030702c51120070505002103070125034100c139000c0d1810041c15440d100c101d001d1f0518190002d0204200d1811800068441d03440200e5000744511941c10382600c641840d003140819442c21401031313445601720078452300c00344070f101d40201d42110649011214404e41a48008030040c000c1d25103842c100026003113044242d0018401180001a1500c6552034400a02000b0300d0a200795400d00c600c04410824158500c01c0c2019274034010000c5003150b60b500011101405440101100959100c40005034050036018840c144450030340641252404412a088203607090350000b0b10400186036400c01242d0420f004a4121040d4600000613580f5800d00380e02d2324100754481c2481002c8a9400903520b030b40401d076905610b1017030509100e6039a1b1440102c0980d181d0001020101a0801980084d4a0a10945005003501030808800290754100e401c150039100241b00c90790030b44001d01594600f80306540130810300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 278321160 1250 278319910 278319917
    0x40e0606280b0903010f14180109030e0f1809071d040317070302130e0703050a060602030301061d0d06150f0303050f0904090210031a01030605060a03020f16051b01 72
    0x1205045800203503503114188031200c0000d8003c02c03940f005e40081d41c1760705e0f14681c2400070404072061203480020440c1c110603060350601c800915400c06026651581d41c041c1c0e10002c0144c51501007003d942d54038032100d41d000f000103c6840c043c450a07011644240c00b09800342583c1850300e460460070007240321b00f2143c0c840c0c0340d808100000350040761202c1d0f0521003100030701c01540c4125040e4001e214a40300342e070f0f142da250030001420508101d0324600c188200d6a0612880d01c889103400c0c00d0b207469001e9030300540c0080c030044c80440e201d4100705520108060010060504840100e2a0051447c4050b192192900b0203030314600d01c80010712000f0324203259107000091843d14001c22902502d4514246050b0001e12840715550300c5d0403551103160000d191442e01c0d8841c2201500400074041c03001000841d4100301486903000c1c0c8200340840e90050012403802c0e54860b000c41c000d5112040403000d06c2d00500c039407040c0403400940c910000d445640123007152004800c407100182c0c461030070b9030b040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 278322410 1250 278321160 278321209
    0x601060e011b0b191401030201141303030e0103060b030903071a040308010b3006040e0d170702030f0d020c0105010b07150506120a03090510050309061b0702040e0606 73
    0x94036044030540a03550005000d901d07a0300c4840071a080011000703402a18141810409036171405615a4107040380c3c800d8030791036040c2034486800140c1d40581d44041c0100c050400b810000700b40141d04034050060140740006040d5160303c0c061005070810342e0401c1d0160b00105031002002181e40c0b4020007c14400601040c82c9456540205400d005001d43c640c040d0707011990340c071620b4009561003d05550fa2003200203481d021801001078040807107859110300c1c01c041350a071003c2d20200e038440140990307030380300c1d50404005403405032101009802c4400b14031007000300005080c802d101402c00548410005a6280a803d20746801d40301c068001d841c80719400c0181c2d1001507983c100044002d81c201c480422140d507000c000030a402a14850003040d80215034410040682c05103188003540c0c402c0365010094215904100c820740000c5030030300e005500480119020316102c007002c400e800f61000100e071410017954042002ea0700c2c2c1000260341980b00700140203c0d807400070126030310412180483d10b44c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 278323660 1250 278322410 278322437
    0xa02010501031202031903022d0315090606071b0f0803120f0105010c2910030501050109020a0c150b0d0b040605070309020f01180e04290c07030e0d0b090601060e01 72
    0x200000c0103561b10306040c0c0c00103031001074100000070b0400380c000b00c01107050042010514414598022070f114000318460f14800b008034542100e03030710b0080070007030306523800c058080d5582c450080112603203190741918040000340110707040d60307020003070910303031000d15125449660805c2a5841c0a007501c06181c842a0062010740da10001206e146504600d8151240c0c0400c0c0f01c030116495031a00707000d8542041d10800600c5e0b40311001200031030340b10b0002001700340c0e07171040e504049010340b400150004200c940c101d000b0404101c4c0c0c45410080450002824100b00c0c0001b074000c25610070110f50541c0c01200b0007090103481d10882e03030f001a61703040c24056074425a000444040240c90303400d05020001034100705552041040740e002d441d002900304682d00349810b010070070340c1600c150303100c00d40c00800100c000190b14603080d41c05110f1103046c85013811480e40d402d0701c00c05000301145401040d010b901c0c10100d0303401c01025028003a81805070042e54100b41d8010b0441c099400d540f41401188102e0700c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 278324910 1250 278323660 278323687
    0x8070809120304080d06060f1404030503030f061203030a0902130c02061609080f10050709060905040b010e090a0608070f0501051b0a020d111306032f060a0201050103120203 76
    0xd01018a90a050742c9030394a01d071140c0c250090b900035584841c50041c0101c1c1450300044042d03010002902c41002c1040c088400d44220f210350701004103560420310125070190401c0d07101c19000f0380300a01c0707803006004440007186160811a0409000d94070b4800902c194101110400e40c902218101805090b0a180c0081e580b48005000440204c91f0302410144881c0308003032000148c110b1205484041d0300c040d0640c1d540711282e19455002500e4000480c49540c001c4070040210b0740070b0340305e080010f8a002c04010080c0a402221814000300100103a020365403110080d1080d50081000a10203040010080c9420941c0d0000c10882184140074004d587c0c1103401e5841ca0b20410340e45200b000101c0e041a814050343c100c0080d048003802050745c00f08075490b404880d840000f5a4014400c100a89158040d03c1356440301808643e050507000ca0f2a100c3d004030b41c110440c050740742001181c0f600010490b076600040c1c18000503592000180104800b080c00149866241d10055060441ca0000300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 278326160 1250 278324910 278324923
    0x20d051f14161b030c020a0902091005090a260d030204080307022e17150f130902060d02070c050607020603070c1509082a07050f06040f1508070809 65
    0x40040b400446a40a0078400e42001803140342c1c0f004000b5504074613240107403002605c203a040f403055243d6580030a403043c941c82501c2c06000d0013062001c06008408081e1400c1c0e101103921a00400c1d180030104465110f0080c01c0400c4548c003c000e44080000c005946c10140c0150a007010580100310030040b0110010039600402d030122804003603403104181d0010541304854404a40000c4081404401ca0300b0145502880c152403a888450707503140e800148881030303d6401c0d5a48883da4041c044060308200d0340c801c1109054400c00604c02d042c0f50002142e6411030011001c200c0e070001440801c10001e20381080040c00107580c0d107410007a81c0d034001103507800020700610410404065050520220021000d10503480f86410014010f507810403404a60081401c00c0c4640d012421510440321156103000881d4401c0002d07015560600007003044040030440890b5218030248004514141800c0c03080f0000c01c0c64070403004e01078058102c060300150005242100b0301c5081400c004003400d01084c3c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 278327410 1250 278326160 278326171
    0x10305070902090a0e011410111c200d030b03070b0909040512160c08030703120e030405040e071e12022b0b070813081204050109020d051f14 62
    0x2580f65420000854150f0195a1116000456640001600c040a002450342000c01922401070700084200241c3d032000b1815405e8107564409449000c0440d1a02c806e2603000380da07860081d001c10b91400c806078004080d18100c0c0b4140c0c0081009503a031641502c5500c0c0d0202d42500580740140c58080080e00502401e110940a40c0d5283c0018081150600c10084883d201d2820680c0300c8000134030171502d4864210084698070326241c4003003a0100e000080e00c000c140d05580c2c8a4400d4120610040075002141c0d41000601c010300000c26565940e0065411990a103c01880118948202d2010b401c0001102c2034010086610500120300c16451180e4601e80540356610180144002c4604c0c1055182c0d29101d100c40c105202c03401c00100c0031000b0b024481e5a96140c503151a08030810307184c0c445545000740b102d40c00300700706403111880c0404142d00601030000003807458038503004245902d40740c603002c642c203030400380e90300844004e10b0142d40c2c490b1503012000c02181c2401c80c0b030782d01d50781c2c0003515 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 278328660 1250 278327410 278327429
    0x503040204020903210403110f0f0f0a1805091c0903110102030d0f02070c060807021b060426010c030c1b140d02010c17070c03050c01091e020f01020601030507 70
    0x40030300007620100302005e10760b0100c03540c0c498180050b01c84e809454219010480b4481c00b04e051301da00303d1400c041c05103040c20f8010a0f040d66001100200408605000250790300b084002e440024155040c4400c40090032605001180750f2510708000340c280801404100c2420241c01e10903100c0d9039011000c08240c0b54011082250344e98264010303850b600403c000051098204119807581220507000340c002c00e449410800300f440e88480c0103540c403e1007200c041c80183d20080f4048082c500d100c00c0c00c1002540900141e24041d244d40c000d1180030318070345c034419441c180f01c80503400326002407160791b10b801c8080c07800304105045100020304c141c0d0b2100d070004241c4120380031304082c000100b030b0380400b0001400468a0f0814540c4000e4080c1070342228440200d01290701c844400c05c1d81c0811248a8103865031482641c02c0c035980c05031045c1e004052800c0300d0303643c0e5111000006c1c2d640000f44070700d44825007e04e0614640c81c410440c0d5a04411001411500200c0c010030000d84001240f00641e6440c64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 278329910 1250 278328660 278328667
    0x1030c060c080f030c09130b13020a030e0d0801080f03130902090303091905030706080105030a03050a02030d02030112210f030f2003100e040807170c010912030615050304020402 78
    0x781060719003c2d03512aa885120000306000301000e6540c000c1c070500c9070540340c2e082034048400b1040201d07098500d400c1e0300700461942403000300e211940185030700705090500151200b180c00c08580f41001014141011410f0f07100140110380c1304100c0303207041d8041503000354a0498042c0c0f0289400303805210304000d940c2c000c6100c0e44180c0d024019281840c10141030303492503150140c81350000d45480e100d035a009000e2030f10080791445c802c1e52101e05941000d001450340e60b90590b4120750a0b40050820310031400103020080c04103461380001d50082c031190502550ba1040f605286449216070211245803450583c03810020341e40202d50481908845c0c00e000800e2a041480305000d0b2000040c03003c2115503100040400400c0207002c1e50082a481420707004103900c9601d0f1701d4204105a0340641100720602c039000001d0720140800e8440340c10b209140303007098410001c460945c0e030a550300301c541848104c3d9000c00c20764184207050041440700d142064900d1007607000303081c030b200c082c0020340a6038000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 278331160 1250 278329910 278329913
    0x1503120e0103110a1d031204030b040c0302060d020405150901120c1101090507090f060605030a0908070c03050102180f0f06160b240f060a03090204110c03070c090501030c060c 77
    0x9a0043d203c0e00d140700e0f41281e4946002e240207002d4031101c40310b42c4030a0014261041d56081c00501c03946a0070142000034905400d54699080300d000040c02151500b0130303400040300503160072001d4980c1c600310000143e100da08200822000c0f08501da0103643c109424400008541c0e4448034121070580015030014200c564400c048800400d000038a940329820001c1c0101041300018900003115601070081104d6801c108225042c2c507118840c460000384280040340f10003138142d0208802511403a1110300d041920750312200c1d40e24a5600584150354042514035651283c070f010b5803032000b0304480c55a901091900000d0020b40008625400341c1400b040b0060440c0541c9030035150703181c101c035a41c0820301d070035240d16080c40940c400b848540319903203509025a0030100300341d50349204014011824108000021402880440420b03640107490355440e08018108000400b61002c0f40c0300a166254114108075140408540c000c4070303041e24040c01003000c1800d2640a030b0a6070789500e041707420110305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 278332410 1250 278331160 278331167
    0x3010b210a02030d050d0608030a200f0d0302041e0f120204090b1303020d18050f1c0602130509040503030106050a021c020303060a0e06030a06020c070b030a050a1503120e01 76
    0x44007002501440f42c0340071180380603042030140c25116031018041c00a00d8507100b410340c4a001d454514008101081070040086591907000c62181e180d0708110f40c8280419100e180c50b10000304d44800220b540000d050056840d00103130b07801628403485803a1034040c5040650300a583c0325102c0d5100e26901241074508541e00c0750889604d0355002225042c1500340120000760400c071400c021009407140032500c105490080e025074603400005913101c4219031820b02401921640c810803140d00501c07031b04401c400d40035441214a085405501d0058403510166900e42d00c40e551070300014486d003003180801c4000340c4000126415154a03150081d10351a0600c000d07840c009800000c546240901002e0307140700d50340000617503c00e86040f2010058603980740d0400c0c0004405843c05a05500242559404180c0a4008040d0400202c084841c015903076403898020340c000750341e07500301b664562003800b041c00d40c14010f005100980b00c84a00c1690700c1c641c0c8003c001172451400c04148200c0412005a03070f0701 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 278333660 1250 278332410 278332423
    0x308090c1819090c140111060103020108061203130806060604080a110607050d170f04020108040f05120f0c010b03060603070e040602120c070506010e07020d0c17190305010503010b21 80
    0xb107509040c403490707140745043c00700200c040c00f52403140040407030102e0866120701d4031502c40742c0c40c01c0090030441c1d003940c00440788581d00600d01134120090b800039108401003040189450459079005040450421411a040a401070402440380800703001c02c0c801c54402240b2400610f43c0103c0b6540c40f00507030008109980241100a4410701900034200c2d00e0f99000008508088d04103c215006070b901c04070420000d04041e0760290014445800040c00513540038000c408450088007100c50408407015401e085901a20094495100104214a47c03130005d000341098290100c000d0007281c60702001103651114944541304c1520005400b1405206203681100d40841e14541c82458518200115000651003180201d809228007000061800e0520b44c805000ea5a240d01500c465100ca200407603050a04000a861400e501c000541a0301d40d0f01c1d008281d421091441114817040c4120040c3c11944141d00040c080d90510000d42d902d5602c00c1900807000043c0f202c2c500e40c1d041d201d4045460b142 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 278334910 1250 278333660 278333701
    0x60307021506360a0504080909061f02010b1f0225030611030106110d0905191d04020a0b0c0c06070302010b0d06020913090803040201051b07120308090c18 68
    0x8504480500031550840c3d81d890402d0148000020b00b512101d903814100c5a0859024011070800d11030124585030034203201d500180001d040204416015900c07840f45050b040b03200026030f6542024038098109408108a80c0041071070064400d080301c0d2000e5241c2118020140c111000b13421101d40c0c1c040c9580300740d409143c10003020000c40314942c010f00c520ba4000e00030300c40440c8841c01c1c00e401d2040009403000c8080c1c403580d1010341c001d2401e4140401e41814008502e009094210007003461142000c48442012031180d183c0120f04140c01070041310201900701d80c8061004006000061358001000020582c0c00d07954a42d03103081504040f401407680315880b592100840e4091000d01220f070b00030b880d2541c0c003100e5101001d06041d4103102150018100103021041c04c6c00045d01560080b406018202e201700200b0701d008440c174502500300560750700302c0c44000300142103850505d5440710000354042603100c01050070901e5840003c00542d43c843c0200d0302041990001008801c61002e06411203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 278336160 1250 278334910 278334949
    0x18040210110a032c01140d24050108060a0303090e061216150f02250b07080309161202090705130f030b0f01062001020f0318010605060307021506 64
    0x1111501d0010914940c00030f009030407100a010708136071481285094564503d0503120ba501c00080010034200d9a00031301050343c03c150b07540f403004a43c6880070b0f0744090500c0d4034449956009081100250100601400450292000d080280002070b00f00038484c042d555410500d1074241c1c1d50a0002e040c10b2440059081680038102c03544c03003412500c00744c1d0030070741c0e201c40000152840c3c4910202c80d0180c00d002d031320b00107902c03014607103280c541900240304250441c96030304089541c0342c404011455208103811180c1020010410000d070405102c4c02543d150001e6010804524002c103200351100b01d140041e01c1a103500b4049041d8601500c12107200d00d100d030f8000b00b5025952103018408a549103c160384400f031080003d603440c62074031200c50690300642c55020045105140e000c3c40110104c00103d410765082000e420300c901c1c1da802031803080284410084108017240340843c01d49080350302c042e02401c42807003030140c1990080340312110030341c1001d0480e40c10340e2603800160407000e210400800e407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 278337410 1250 278336160 278336173
    0x718050402150906250b25081015050304030e03010b0a090b120601180f111c06030b01260609030a030903090e04060c081003020f0907030b0a080d09051804021011 71
    0x40c1005c0c0d40d40b00540e00c3c0505500c03000c5944a109107605009040301560120b030300d8090035040300b4000d403a907540003094401040b000c0c5884440c0b07e0b01d807241c100c10600200f034003c8108420164080d2849050b04000e0700240078400d034503c04141300310054087c82203040d40b55442e050540d1100044003c00d01b00d442d01300c503080e50750f50025901200c0c107243c00ca086681004038000f4494032501a002d182021895200d00c0c10040e45008d8414000050140d60102c3d00c505000000c6140084028080c0010b6414158109400304803d801c0a40c00d0f034040d04690002d030100544160048107440c4071100070b04001ca00d1031840d140c201c031484826000004c0c0e01072410188414095240c2c009590f010f015207610131140c5138455070303500c80d403140c1c40000d501080d040045c070034174280011801e4001c203140c1000f0132072a94070000140c1c08036003900003200d2940003025884c0010b501c1a4a10b0042c007040d078800f030003d1a4803164100309a40100702038000c4110030100e40d0f8080c49141411509034911081c4c411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 278338660 1250 278337410 278337457
    0x1202060405132c0c060915070c0e10170c0a030201050310090207080904060f1a1308010504060c0201060b07110d030c0b0405030c0705060c100507031d0718050402150906 74
    0xd1091094243d400f03a8424000d804485090400403249171603801054030310714200b00011182c156200d284200d40c40309400e21700180240c1010070b058060030442e019031042d141030112040a165a1000c50984c1e41d10444072034440380c841c00000c2099079028a03204e42d490703480c1d0707100c11503080550b44100d206610004850060082e85805800c102c4401c4a0601c4020b55812030210030b20200d000756044845109801c1e5001600b4400504010400c40c400c3c0d42c41590392100b540c21100d0480f81078035040e840b90341540b40141c2c284164805450042045802e28000c1d444107199a07121001c214061456441c001c001d00d40901d8a038400d11b50310828607031142c5058580f5985a812020400d507091190500114040c40c2c00c10644031802100740c001c1840c17460103070208001e810054220024142d448401c0034008500042d0708aa94075480c004000d003d00d80711140594000c254840b40c80c05203080140710040e030303450303c1015060103001c00203a06d8403480c80000781d45108590118054400382a030f07025 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 278339910 1250 278338660 278338721
    0x203010b1b0c030a030e0a0510020706030903030f0c080f0c0f16050a0f0804140a0b0d02070f02030f0f0609010603021c17030a06080f15061224060307120206040513 72
    0x900e4000a41e0ba803105248daa005000012090401030740142c0c115140c18810244240e2140e0b04d5640240384c0030494030b0003034600c44220b81490085100091b284010062021401b1401c5500480c001458600d8101030501e400024054840131555810119040c0b0381400800c1006a190a0b003122030442c2140451600980c554064403840045030000c1c0901c0102d842d11164031000c81d00d80d894901e01d00091219000000d5100740012540c1c0803907014000090b032801c0040708071902150000704020442c3c00100c1c1e03e41380000344881c02e02d0f811f0520601c0162503001da01c0c0182414030244400e0309500e481c1504101d003d2000201842a011041243c9900e058101e00212400c2100303a40400118444032a1207104034040c00a88030007030703404a1341341d08103800d056000350079101c01d8640402c02c8a05850140398000c00581c6508506c1c01403005900e41402030000400c40700944280c4110142d001c200c003402907100d07140c03240c803025140c0e40112009400c400100c0c030795909541c451024010801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 278341160 1250 278339910 278339927
    0x204080313292118070806060f01030914030f0d06060503060a030210020309040e01060e101508060609030a05010903260a050402010201020c07060806010e040203010b1b0c030a03 78
    0x6040c0035a42000016030603845400b4011502c0101042c0d00d5003aa0b84054050740303a0110807400b071000c1071142140c03107200d00c0840303580c020456484042d0042d0b81c02040d0920b4005650405c6001c3c0c0c00802c00d205059840d1403000101c8802802d012407000041c0c24041d1542984032015803180c00001a90450680003000422203481a050704000320381c0c841c0022501e41c04100d400130f4201040c03c0d018805803074442c1c1c0a020403001c910450345000251070110301a1403502007080041d070345600d8240910075a010a041d8004d031781807802c050140c5040103140c01b5100c82151242403180220120701c1580722042150b40103e40542101e00405141c50001d0003046419400d034000b450589004003005202c0c00000d00d0141401d282000c26291182060001e002c064001c0341503642c02c00180220304400c0c045007000b403240da11b03895140d2510310005401c400159134801d00c00c610400040c058000d108095605580ea10544100c140091401c00d038900380842240780c2d45442070300d2400080580c003102d403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 278342410 1250 278341160 278341177
    0x903040312081311030f0d080105130e0307060216020603070503070915021f06030b01080a06050a090206070f021210290f100509041b02010506010816050f070602040803 74
    0x11003411000079600311881d150070707601460032401042c0402c01060740c402c003181c0042c00c000e0a840c04441d03031041140c40e010102c2c40c0b0300003080240c13004002524108042c45c0c0c83c0d41c00f01c3c2040c0040b00c0401070700e40d101e10039800014403841d80811810340d0322504c44400d1003800e1317028111541c2d07802d040201915940080f5400b00000b0300d5654040f0b030b6400300ca6090072007501550020080c1c3d42039203042c481604c104803c2c00401d90368403040000800c8840ca440350003072441304040e1811104506102098410003018000c1003410700c1115801600c62808858500d5000340c174040782030350280b00182e6441d0503024020301070300c200f4103021040200c81d4045103440034014191a01242c800303440c1d0b03c13110100c23440301d5445490000c00200c5418030101d84c600341381076490102e2600d44a131000500300c41c040d0840e44003028104800310001030b0244942a000402400e01003282d00d00034808401c549854488103041100214500707000748a100160764500354003000c00e43d1625110250290b40c1e800c1551f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 278343660 1250 278342410 278342423
    0x60f0e04230c0a241409041a0303030103061b090e0a0b0f15030108010e150f0910020403030c02011202070c05060c0313090b10050c0d05090f040207060c0809031813021209030403 78
    0x1130b41200e060007100000e03240c1c030500030542c3c2800d852404000080410005416240071202c41d00030290340c0510046004c3d51003114000780001654400c40c001082411010050001ca8032003840f03900001c151180e8494500b12010810845c0b40020030304611f4448201500540744040600b50301c014480650f068400d414004c2005000d41804141d50300789074003074407000403000070109144000b40d0382102d91200c01c0e802164007050610442c002282c1c019441640040e400c404403504640e80030748500d18045a4040c03c1d130810300d07103445210f900503c600c18548195400079403148000020b1041e103510340002c7c2c450307958242d82c03983c56602800c42c5404162154201000c03070901203019038240e072116072100004015401e0541007d46a41d805004000d901c4050f2081f1100303280d4947c0002c000c5148540400728985440500c00f400c0d4680c060082046070f0010f00032402c115072094507100420070100d034540c02c10025038104600034890307018980000714424081001c600c070000020400c6078030581 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 278344910 1250 278343660 278343719
    0x90d030c1509020d0204020702042a03060b0a120e070f08030c010b120607181502100c020102041419090c0c0510060f031115030901060f0e04230c0a 65
    0x101d981007151982d0070001d50285518800402500f065030150205034405080004c0001c448920b07907180c101c01044002003804444041025a6818011903004042c04210681400c1054101900603510504811445941d9028005654808201420040011004003051252030b400b40139220350000105560943c05d2a600650504003140e000070a129290090407031501d1b5050103c134103070456948403c0b0004104000310b800910203600341140d008a800030a1500003404908041e182c2440d83da0f015a48103110401c604181c04103003400351102110348580f400100d9031000c0580d0760540207050030782e2904064020703583d00072466103045c0e80140c00300c40c400d10f4158404815200d1901564049000d41c05d010070000e03a03060001102d20364000e04021384a00c44124441c103a400450300120745a445480402007a02c104035000d001d005040310a0805240a032580b24142090040f280008142001d002c00ca110061141806030f01c4020200520180d0b100000c125408054100300c110f01c4405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 278346160 1250 278344910 278344943
    0x20406020c1005030402060a0309081314010f080117070b040806101a090d020402090d0506100b030f0c03091501060c23060f0c070f05030703030608030a080a0c05090d030c 75
    0x951880450550b80d030b03030702e46155a035600b40070311508204e001d03105068803000d0b002c0c0010320b0a4040d02d0000b41509405207c649014a13820701480f010079a141405001c0504000f583d50100c2c6c0300e030544a49500007071070054682030192502489900c002c0c0c4c5004003040229403858007140f10f03070044c090401d903002c0c8181c0311190882e00702c4046d90b481e003400008221104036410050202c58445000410040c00c108940b0003080d80a40010b0040310507402407401c20107070b60900c10315074002d80154036080e0b0461508070050350903808041e10f03000070050044002403601d9000c10480844180176050b403aa5940d4600c5e01405a40840c00100e440c1804035296440002807541c01c0f403100100c5600420070740c0c9950b205007403181c4000d808030180da1000c01c800c5001c20740d0728044034075041c86000150b41c0d0f0800c038200101122f4030b40c1c0107400d8540081010128865020100a4000000060010346020160700548041c858840d9040e00080071541d041c0c02c0c940c010600b500000d010381020540110741 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 278347410 1250 278346160 278346169
    0x130b061c030c1a0f0103030801090c1706030319020d08061206060f0f10020a05060a2901020a121e02030301060c1707020306250216050607051f020406020c 68
    0x9a001184610305140001004a84290b400940c042c0c020f080011050702403141010f10b40404954203485003102c00700400070158400042c5005042100302003140c05013020000709280075030315441d1742280300c260104102c2c3d5020701c00c039001c08a480e030344102006c0100d00301075220f200b48820341d4041110980011440e080080200d0700281e440310181c0000c2d561202000100c550000c0f0503608070860b00f004101548034a0120414245c00340c005000c10300701d43c900680b030050001d001c2d01d100c1d07082079407070399920646d8400f5006140e682655003e040c00000c00403441c018031800b001c2c1141c0c4019200f0840c00d60807411241000200d100000c8000e040f05000b40e13a64030083c070511000403802d090a4020410030300b999000c1a01c42203545d8a00211500002d181400a4500b40e000d00c4942302c00d450310320703010138441d10000c00d140080c140459410003180344496003445130170b01a0000045c050300308102401020004200d0040492080c1c1414904500075003260041d5005032203203403910110b40c41e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 278348660 1250 278347410 278347429
    0x10314031c0e071e0306051302033316080603121c02070605010801020a0813020102100905010e0d0e0109080318010f050705060103060209040f140c03150603130b06 72
    0x28502507500c0180c1d100c0d10140000c100c942c1c0c2802c680c3c001c3d941c2c00b24801c8404c1c8010b056050035030400c60421829401c0103003c45030040c0545c01c0007083e40e465000103843c04a110294241c14041919640f21042c000c008501505150307429056118410840130003402015011036400903034900a003540da0109250b61070b240010340501440003800151a6144e44000200e4601c87c140805414016031b96102c4054030000c3c3c02880807a5000f080c08040c560340407c181c0c1e40115900c100e8005210680c002035100c00e40c140751901ea40391119040428024250081e220491070142200d902300d8080c8070081050310040c2c6800d0002c0d105140010710224000291250044501c1c081c817802e40c0c403080191413011014681c3c10138444180700b55070200d402800098000e5015620143e82d85030400c0c100b0080b9250a036052181c00d10784443c1a12003240c41980c1c580c81040001d00d42c0d03a0f41c6403140c41c240e00c0140d1020081e0311103c000104640220b034800d813140103505c903152404071071b1558000c2050070103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 278349910 1250 278348660 278348677
    0x30203040203060f0c27102d030612110906040603020325030b0a09050d0c0f0308090727061a0f0d060909030e030f061b0904111201031403 61
    0x900000226130001c0700c860007180c01014201c406454202c05101d0820100200962052900703078110749201d990402075060f0948100747e2800300b002d00503034540505403124825024030391807010788001c01900e000790704c51006030218240d20501000b035458500c07902d410019549000d23081c1c405c040b43c4141841d019040507640d000303000d000c80002d42c25074011403c4050450810050600d040080803031014a2011300800007940082185012340c01c003a0314080038442181704101c1520f100303201054100040e600c4850381031401d54525120071102c5458505180c000c1201090a000001c40d09640550a0001400c80c0c460500013507641e41034011006400600c0322001000800507012148180c0c0300034017122140000c00143c1c035844100007421908121012400300e64004150509450700304480c401c9492484010720302442c014010045000c04140c1c050903100c03002c41c0106260b036542c0c1203454004807881400b51500d8188103140900c600070b10042c0d0b003603112264008120038001c4121031281 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 278351160 1250 278349910 278349913
    0x130909051b06070f020d0f0c031703040803060108041505070c020405010b0910080a0212070801170d09090903050708071b080c010813020102240a0b041505010e1c0503030115030203040203 82
    0x1c41c8a844e085841329007614100c3e88071100350f40d8039000414408a40d0391103400380e680d502545040d03142101c8075a580440895452409200b0003000a070107400b02d9501050a1031700303aa4a4030b49142c90103602e5019019151102c2c10181000030495210f80700601c40c500844080c00320344d9031101490a94492507074016040246015541c452601690755550001c04113000181b81c000e0b0b03035a01d4507103504d081d2094400904800010084000102e200540792110400640b00101c11103401920190484c0b1070011259196080713201814061003d03103d880ba008410140c2d505141c2c548200850b42501495007000000000481d01071000174401c4245807040e140c0c0380c0a0b4a8401c0c55000040f1408400c90445c0b04000b1601c502c21141c815420b0101600c0c03250700c905c1d04142c2003400c25a0800c4001e41c0c040d0303142c0324a21031038058860007101215000e0802260000800e00031500e10204203002400d0b00102400000030071000000842c12564450b648864201c03110600710241d102c141c8020307505 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 278352410 1250 278351160 278351167
    0x40c05090310110d110d0e06060a0501121515090e0403020c01180302120115060f020601330c0b0106030203010303050910050910090f08150103110303130909051b06 72
    0x24942580041d1003e0080e40140d4207281c2046540c4081c0c40709900c2d120751304103000c01c0e0b19581079010701640c4507000780f00303003e0181407418902103040390201c0d1060301e04205d2001c20608103400c60303070302a12103c0003030015585e03080c5c4c42c2c21010f5601501007a0312400a030f903d00c800944002030601850141e5850b038043c0c1461050343c801140e0654844e11042c00b01031035a0710020040c0e07180403000b100000014004580710f81140c20301d001d036907126409401400a50004009035982c046482815141400a06d0b00c1d810002d90508451207d11441841118841c00540c41c1c0d048c2c01a1b0f50318050b6100d8003400e54640c0c1c83d10f108074180c0c08207100050100c3c10a202031075035880c01003141d0320000710b540303807440c28032400d03000250384004414221070100e48090404c3c04844402115040a0002240288030540704001c5030b01c000001444050441041c143c5800a00c4c4d0f001d00898003189482e211000c461516210178400801a205c0304441d40d01c40d07441d103070022808110352800c1e8860024011401c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 278353660 1250 278352410 278352433
    0x1606090f0e0403120614040f0204060e061c05010b070b15130b150301120b10030201020c01050a0201060f030b09010f050411010e0103150f0501020f0109120f0e031b040c050903 77
    0x2001d903070150085003801108180b40203c80710310701c2480014105816000c10700c44a0009010407a8942c480006003140100302c01d02165420954504034203605484160b9501c64000c40c1048500c042c0e41101070040c2000000505991107202030601e15000b5440484c00b5101d40c074080445402204040380c005007030f01d524400c80b03403150344401c080110207855208054014150b6a1f11980242c012011a1503110010800c0c054100e817900d910001c0380c3c10f1030300c030981550000b030b541d01c8a05c00f880e81004400203107442128400e400c131100074420302c001910619200c2c9010702c4012402c0f600981d1542ca40790010100460b18000c00b40075503000f403c4034448c894160700464484042da01d2440c1495180e400380c0c104c074100600380a00806400e23040741c05c031307909020009040c07900144010304a07a05084141000c60b40c410801c440050040c24403003490b803455003050701c4c01006a407040d03903d4021406210b10882c079015000c0c078600390032102088110190407095415010300380b135054065000d081010b5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 278354910 1250 278353660 278353679
    0x7170103020d020d0c06030f0c0305060d081e0a1205070c030806060a18121109040809040f0e030310080d0f092907080901020606040921030e0a051606090f 68
    0x2c0e41d4900182000b1002c0a080c1c680c030343c00c02140e500030300c00a40c1d10180a01d011000740f280b48121003852034180801c2c20300200280d413818000d5809007460000050140c0b1010b4203a0000d005060010b00458440c01626400341c07010035540c1c4030070000c1d410f00703000420302442400c070130910302e0b410345079a060794440e00c0c10301ca05900600c00280a000842040103018844600610006e1100030040303088105980340415108010700c6015001d481d135035062100090110b015038890306c1081d07500041c5060607403891409000104a4007045000003c140300c46446c1d54407446c81684c401c20102c0d44c140391044001c440c41d0000001c01e10000318204803c0c829084904885e03071004030344040c1200103114252041c4815845080120780624000503a2140c95805011280c0d101200f03c80c108104299511150328044c041e80381001181c00000c00000901c3c06170b4450110b5001400840d16880a01d15200d80d4900c400ea980103011066140005100c03031041d0010303400d03911003600040c2240e241c1601d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 278356160 1250 278354910 278354929
    0xa1a0313110a030f15020405030a0611120a0e0f0601080312250804110102010207120c062004051519110705060d0c110d020613060920090717010302 65
    0x880301d20203292591a51655208610005140104040c0391140749500d06101080c048400e0050300300d0051000f04513903070340450403a6a06410440100e4002d001140030545841071080c00e500003040e41d014401038910300d0b44800c2e000d20598044500c001140c1a01c0d40eaa10b80c01d204080003917200700040d0310802484443c0d0760b000b01d1075401c2d0341300640609103a01107000000c10104000341040007004107000c4020340071000c8010a000861401d1f1203600d4511842001205034024441d203d5107450800030340c0d500071240320303840100b204a501201404444203a12500c55944174240741035900e2884018141151080e803107540c40c00900c5444500107a03501c80001440840d1405003542c00502c60b1600b400926050441d100c001504074152072018003401078a0b02070311072692015483ea07120a40014034103810601c00d4a456118010514004000c1d000101c1c0080180c10680481103900c0460005944080d0084070340c81400d6035a0364044600440030044120a000da2800400250802081c503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 278357410 1250 278356160 278356163
    0x1a180112080d02071b09050108060a111902011a090105060301030f02180709061b1208060d080c010203010602190c0918020306040f050c0103090b0606030a06030c140a1a0313 76
    0x3a241081020b54841040382c02a080c25a81c0011800c0ca20340c0d41e04c8200e200c0406031840c040100400c1d410031921650343c81c002845030880a90f81c0c1c81150340c441d1032400742d4000002c090500202200d8400c0024040d00c0c03001178415004000c6045402c4600d040600d25050b06c9029101508507031030341d20340010845a144007070740c1114910007414014501e0304220380c41040603031100c620b0a031070b0000082190344081c030781c4000101c1f508040c0000542d0b40e0031003806007206241106454452a00203080715108000041c01c06000150340382c10b1b18010b4010314101ca04580a5070b020f12106642140c051814803401801d036810801c0a0011012381d6200501105030540c2e01d035045d0703045601280c0341c00002c1e94151644054154400e040110420030740941160a180070b018540762541c0c0c19060180150a0a203d282c001c0001415040c1170307400400116040925001800c1d5905135034010301412141c0315010304402d0300d003c5120b522240c03200065210010001e1300d5555101030041c94058030303030030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 278358660 1250 278357410 278357423
    0x1021c0b0d02030a0b010513020403023f160512120d06180506040c1d010c0f06020f0301081902060906030a0f06260f0a020d03030e101a180112 63
    0x9141c0268034100504c001c0c452003200340c004036504003001c00840001038008461003600420003400113856803030074040d220008146145140f02021807820380d0b040c1c24003594406030f140200e82550381c4800144a5403503500b2082880c1d145460f401407207108014071030a0705956008040c600c01c51016200140400c1c106080b00003032a035203400300001e1060300d44426034401c9484034240450313482d00c0c2c40780b4a503c031000d0400d0000c0410f10042e002205212001030340c14000d42c03981c10301c00d03c00180742500781d1907844541150348044c99100c4440704d800030300903d0307498442e43c050794078660500451000c559800504d454101241c200401840b40c1c40200f40c0e90b4665100c2c010038001c2c2e006400f13440b024005000c402c2041d22411103210214000038170600f56107520241c84c0350240301001c9604081e8940640d41d008090b1800e003000d0f4003900444a05040da0310424005402301d030141e0f030080b0911b910070b0070a035462541410070040ca6006070501c040c1245840d1004100c840c0d9464000080b00c1d12030300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 278359910 1250 278358660 278358679
    0x1203090306040c05040e010524040f050708041b0602060a480503060a090203070519020a1101030504051b030109060e0102041d0403020606010c080c011d06070201021c0b 74
    0x10042414074509076022110040140d10900091038075004165a22000000810040c40d040c070458000008000542044804c1c1d840c00c048107854941014040c51410303002409541001c0400420801e030481d03064880c1c001c0100005080707075404d4500811582c0701d41c000c0c02241c9500010800400b4900c81004103a04240700a070944030200303600f4a56041d0f50300403150901071742004081c0c0741560305481410440100100200c0c1e41d590324107003080e250383ca000103031a0341c1c690300180c030240300706100010741070746036409090048d500040c4450303000d01c20070300300500102a070019004e9500580d0002c006130400c4007400c90074021648061100b0000800124403680305880d10000c850b51600301e0303109a50005014010000b000c842c04120351511007155855140544009480d5880a03105031704004141c10040c060040240950300c02d220000004c02c590010b01a0b410800400b201c2069014002c0c0f400080c0140d0062003510049021a9040000c000385207034030000500640a5484c0e12042c0d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 278361160 1250 278359910 278359927
    0x30510021b0d0f020c03010c0903060213051906020c09090d0c02130f02030612070b0a0302030c040b1204030e01050a020d0e0301090605070f1805330a0c0c0905040506061203 76
    0x100410358000c2200e40b54504040b5500e28000c0c146401402d106000e0303814205c08c491201d0303000829504032500840c00684520b0b4099120b072030881c16901050b4030510305d6160309441e00803c4520000c9071486e408540e541d81019084c0000b000c03044501c01607039000310701503141190140c084201d003103100420711006a40313203441c0d0b40308507004030340b04000882d400310800045051800c1c5813403204803410020110907150940090135842860f88490401d80c010000c50801103122040d64050f003c90103816480b4824908424030641c0200ca0a8001070b007244c1041c42c20f940220110b0f410044241e0181c002c132a45008290780001f6484070b240c2c1c1540d40d5205020210340d062051600071900360380c81c220600204a40102660b2040c200c070001036140b00e004114030b66480e50000782e08500385843d41c922003c0842d4400d440084805080c81d070300000100d2254090380709c55100210b9105e400256807194480b1080c504030b03503045900400c0c590048010031b105180070380d08009540407140440b4945943c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 278362410 1250 278361160 278361163
    0x804080a022b0806090408031f0302060a03050601170c0904021b010504030c0317070504351e030f04050d050a0f03080f0a020a0905190801060f170304030510021b 71
    0x2201c0c24030122400d021007602080d64002900f07900080308544417040303800c05440f040000d200140030f1194480807032603154020018924030070b0045800412030f640725412400c000e4080c00c01251241d000a102c1c5035004078811040030314501071280c0006140c240110321007848025401180d03503184203500540504000e0202340606403003140b00740d598072903108442c0f4002d0300c0c0c2c4005800064045d00700204120710150b000c41a58229900c112441c3c40e41c010044c01142c2d0500d80268a060112a07110107103041310000413585011001e00c00d02c601402c210403d815224010025800000b00041008000d2460300320703030b00e0003504d020782d045e51208915640c403600314640504003100444c15603010013070800b00d0f1a900952008619a0a610f880f0810f0001491001c050007450b00c40c01c00801060441204441a280601032440080122540b503110504243c1101d1050303410742985c04000c143c01e039100ac400c0c6c904480d440300041845101a104141c0a50051744140c8120b10300e0a2101488810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 278363660 1250 278362410 278362453
    0x40c0c080c010207110108040308130305090904050124030f0807030e030708060405010b01080622020d020f040f08070e07080c0d050114090601031a01080c090405161e0804080a02 78
    0x901c2000181d660b40603140c25010b041c0c101d10418140080c0100300804203820588642c0c0c803940c600700381e0385503a1161406a805005042e012900a00c03118200300400c041544260170100c07800810201c0c0040e070f0740601c1802821404020002c1712102100320000b51110050aa01e900c60300f0170030340404107800401c1c0f900191b540b0191603540030308244418002d0030300c11000e001c4800e02c0d000142d480c007440412000e100c50300c6c084800b0022110b00c00c0394904584d05440310301d03940c02811740d5611001d8001c3c2c0380c2500140694502910501c01c00584008000307486d404454014054020303d55402a0548850794018138030318100e4820000c001c00b0020620443c3c1c06808104601c0055070b03000800d20170301c00c8006000c507061502d03210007080b41c080c00d810303030002010003460315061540e1089843d001502940340c460780c005d41000e0911961490800014400d0b92541e51a015000084a4075024500c80c2142600c007203203118010802151420004140d07140740c1b40103c1c0d003403882282590750000f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 278364910 1250 278363660 278363677
    0x40f020703080f150d0b070e091005090915010501050706020c100c03360503040f0b07120e0604050609031c09080c030307080d180503030108031206030f070302040c0c08 74
    0x100c14100300504229008200d5411030040c0a190390886140300202d0003540d0b840380080c1405031b015001901051080d072540307031000c5000d001d6090314100004400540391003170142c2d0348201268130011b550790000050988903140c0c0441220b00503481e00c801034440b540720a03000e9910076000c00000101e100200b03c03c001c2100303180702c000351500148900030120f03410549002c0c50000404405c0d9a01580808180740c14007008078600403d250502d005443d6100e00da0180600d401c9008000611001c484094588180190140030045403440c1040380c0740c40c14080c1d1240c0c0500148410300082c02d044009c3d100164018045801502010040140c0900316909110000b100d0005c14011400107202021103407000783c00a605004941e6900354443c0611078408204075522000010415450f40d21000d02d00c2d0400c064980d01d5031541c1c98107859520403103032040108942c00104403942400100d85802d02294800740c038800c0c5c1503501700000f07401c2d400c0d10311082040d040c18400104a84500508454 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 278366160 1250 278364910 278364917
    0x50312041406040b19020c1c11011e0506010801060804150e1605030d030e031605010204050a1707050901060c26160c09050408070f08070b0a020c06010f0501120b040f020703 76
    0xc3c900f40481d29882e17111401c42154031401485842032010740080c001d0344000d10303d031607001c40b02c94040089902d5040c0c001c82400c55801c2522113135034900e401000b44103c030180e6030240103d0307444034010f5900600c00e1160b100007490030000680840c0034030300c0024481c010200301158000300c0e104500d14140c000403040d54480d5003081d08105610307040000008240b51410b0900c06100c020f80900c0d241e024022104c003028040602140802c4000c0d41205d000c0c0030000c000b00429910780b95010b100010540c200c145c140300e43d001c0450245803410350141268115074071034078800b22550394104082e0b6442210401e03a9503d92880300d140086d60054685400345803001400311240d81051040320408e9803011030218a0402030202240e100343c01c540075640c100441464000480c40c010300c980c412801d01404088480d800c0c840c0d40341c0990000c000c003124000c2100c1c00c598807001d20450703103800d6220b1140030030340700e021203448c04031a80c0001134440001400004d00c9550107000b8005da82c400c81088000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 278367410 1250 278366160 278366183
    0x3020f0d0e15010905091e0c0d1b080703061406060f070609231513021018170f0c0f100e0604290702130216170307091205031204140604 60
    0x801c1003001103c1003a150170302d04c45d50300c0132802a915228103101d4060b07800303027841030145020b1100182031808861000700c1c041210f0755450744a181c440d03169000444486050116500702c240d8829401402808024030403840e00f40041350080e00c40d4840f400455103a41c1b03414011000c1840120104200145000e40c038100b078807091126420440300783c07001074217900c030b0005122041c0d02980704140c0180e416a90305660444050041d05d44031540060740494140380c0e10013040c1520088040700c0700b070421904039110011000b14143d22007086101085d0003042d032001d034603000c4c503110711007280000e014148009103200b0380001c507503258065007003208184002e24644000c1c441c0c1200d0390000d4014890007908061a5078001101440000d0380340320502e0300801c50900b0f03a442c80000340283c80e403080c07444004540c13070780d00103600c0d42040301c150022801c010800500c280d03025803504545581312025501c0c062054842000908004d0300c256071001c0744501c018864001007010a016030b014014540d42d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 278368660 1250 278367410 278367421
    0xc11090403090815010f0501050705070810060f150f120209041a01080f0c030402010305040611070f02010e01090b030f04110d060e0c0a050d0b06040b0604030c03020901050103020f0d0e15010905 85
    0x10304100d600c007030750306481e013800108030041c1c8420b10035081d07400901c0d0941c2c0d03d0803103043c142d1405170705810105039802010b030032481c600706a138480c000301c407001001c441d101583d414080b250300d01c40d04440e8000c40c8d0204641303d2107a00c140090490a110307240d0043c201a000804202190900c505060724100c0a01ca40c610a40e0080540d6038042020b82d0b00c0c0ba618509401c900c0d8031400050b000906041d00c920104040024a420a0400c4032519515540f11000b5041c0040382400004003a800700c0d104050701c03111944a02040340540da81704074020300d0343c0c40d58003005000301c000400c1610b01c011032042010b9280d48640360300001a00401000c80d40b03c0d44248602d0130142110100c5100e0a403034a4100f00c151986aa8407802035045000e0401c15035800010401801c80c410440e544814002804010000c0c070650020540b4001d4400c017015a0702e4038015002c030301c19089100081002446241448456504143d10791840b0400341c0ea051804600e100020400a803ca4030903561504104034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 278369910 1250 278368660 278368663
    0x1b05090a0b0f12040503070b0f0a0e0105010803040b09040e0717010b030a02090703090302071505040f05030708031204030c020604030804050102150c0409090819210b09070c110904030908 82
    0xa000c1c04405045a10709108080008441c0c41800101080c030900c5000150602c074040c4269001070380c01c8001e2480600e07080b00104e018903001c4800e0b0441d40d15010440130312442c14481d05041e07070340b5a0000c51519040c2480c0c00703082e03041080003036800707621508215403000043c005030b401016002040700341032908524071820b441c0d103600c1113030007a403112401001690310704000fa60041921b0500041e081103508041742407100582052641c180305244e060880c550080082048400303048200790340319200c0040586410151250342d0550f481840301030f5903000e080051680280c802d013000245100740340e001c90f40c2c540050307109a4100c400803500b084a940c042c412202c0029421003581d400b4600740d814154036000e07078007820040983c1c8501d840c040110300b00454585109141030380e4241003118800921880e08002c04100080301503810070b440403042c0c001ca420b40400104440440d690354001151905517540d002e0b580b5217514050403545485004503140518000e0360b40c1c088040c00c0c8821207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 278371160 1250 278369910 278369929
    0x80a02030706170f060301090b071e0c0b010e07091e030b010b1c27050c12030c0304140406050d030c0501060b09090a0209040b0618010207050117070809011b0509 71
    0x71002d01080032003410707014820752001c030b0b401290382c4c90b45001d544507030020a00502d145000100721061076824071104c2a00300242e4203141018200004010104040c1165540e168500c004c0c4005811001400480d8082c87d115a1081d02840d150001c82d640b046225500b002101c0f8811421452150038800d00040e41078850141490901d00b0340340040b81d40b010190380060202070007149039506020700009080031003081400389011285084117411f828040d4441f47c40401d164824065801901300c47c91f00841134450781d030f02d4540614103081c41c0c685a09080b440c85040c25038001c0c1d0312840400c1d0381d61420344580d00c05000e0b03920004690024030300242154510740107040c20a00600100d0f80c0d0790b481c8800254000c0c901d01d405600c2c0d003c81307001702d40580340380b0034000d9000a0208101507411841301e848182c510090307089900d100da0303820040d15560415400c6110b90400e4a0015069600036000a0781004520000140030300001450462003130303154248200285000600e108140343c001401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 278372410 1250 278371160 278371169
    0x2d1502071e06110c0613060605030109080309010b0d02060f090321030f01050f030d0516081c0b06070c03020f010e03030c030d0f060806040b0c16061b02010b090c0708070606080a020307 81
    0x40500e0a0741c018400c4d5035a201c010300c0c29007000301010442c42081580d8102000804010300207101c000d420380790541c020b07001103a81c105258030308505034405117003103900c44080e00c0d0042e00c0c0c40c0c40c1103049071702900380307a00c090040e940611549504d41594a5030351107180600c0e440018841e20b0f4145030100305042f00c010f0384420b10908030010000000d560108a60310302c0040703800c0095440d45140081da111025519000d0b1040202180062041803c4201320b2400a4808000c02c40c07000c1030070401500d40614240035261004d80712007400142041101030200440504140007407203140c100003465a480300e003114032181c10104144903211143e0113540540c0e070501c482441100c0c2058041307682e51000900180032100708101103081c458a25044902c0320341c0100108440007071508004006e040d41c3c281c01c48050b9856a10603816510600c04d08181000040c02d03805207844d44810204103800c00c080559509408100c0032002844130711452004016983c06415407951a00403d820540950720 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 278373660 1250 278372410 278372441
    0x3181603031209031202040b0a090f1805040213090c06031505060a050f0715091e0c05040c050d0509060906090a1a0a02070b04050a2d1502071e06 64
    0x409000094000b100d500c1407510416001031190110b0130229404624a03c4010340c05200041c040341e1025480001c01c10b420858607000c0640e940c5420060401d0120720030100b000c0c020174800e40f855103031900240c1c1c02c60300080c010341000300c071051a00b0489081e10b10403035015010590030021590035002d008807040c06060f522030311034901404565a88141c203c00c1080010004029003e81c02e004161280203402c8203065000c1c2e00340d040c1a000a1400a600382e03180e90f842c3c41c0f00101c445405480f4540b1030b170701681821b0031519040501001d0311a0b51900e60038404240698101c0c0b4040d440341521413a042e4000344001e0804043d03840c00c244016000038401d030450000c0001107040e61460015813000c5000c1c6107841d68070402408024003030390400800c5c1d0301d803500500040c004d000500c461624040c1c804850041c00d80d03222042c945200c0203202500f2680703002c0340384c0850401038010f550700340d0240340549000399030740d03030f41160382c0c410701c01c1d0300002c0501100307241445030070311500b501c02c3c26216 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 278374910 1250 278373660 278373703
    0x903050918090f030f16020a17030c1c0203070b0a060b0c0c0913020d12090312030e0607180302010302030a022215020c0d0807060905010e01020c1c050304080d060305030318 76
    0x310217100c6100c1c8100a004940c920724914046464503024200200a1010303603071b0b18107400d0400280c403940300603006420382c030502c540c0c41808800001d14500840c2c0c0c603002149010318660716414803c078020100c040e01503031403400081c034013854030003482034141c1c10300500f02c07010080e42000340e140000741001990240383d90102d801a1584850003c0b6103400152128495594082c00c498881c5035400c010590541105088841901a00443d040141d0541500c00c3d03955010011542014070f4007409103090300ca4001040554080d9005542202101101625001101c0e2078009103008840722061260b0340c581c42040002440c821450001e4954800350039112a004d0018a4105010501401c0c5d04400240a0108000e82d44803a074410f5100009100000c19035200a000303400480e42c864650040e22a078949060807502c01014160682e1250360858075143c80e00045600100448000e5a95940d40440420380400195105800f88008001ea1010181c921f600f0712140180a01c0c0c03601605 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 278376160 1250 278374910 278374927
    0x324160504170309060d1b0c0302030d1802100908100204080a02040509010b030f010b0a080601030c1505070c0e19022b0f1103010303022107060903050918090f03 71
    0x4021201191000120710a00500d5030818504520900b401035a000c10006000d50300039410741c0002a0500c2d0600580505d0300e9502412346615607000d2006005130010003204241020304d9000544040c40710a0b990041141640800c180052140000700071400d0a43c08102030401041820410045540b003542024a0440e6031a52050701e12002442940c0300d40c00160740e54001d40c48140015802812900c601c00d0700c6040d94001e000b640a03d9014803c136810102d00d0b8540092201d041701ea000c0101d010091800070941c1d42c40f44441340960811004020060101e20075181a1000c0c0184d5071004c51b0504050140740072103411450039a000b6070042c8002903c00d030080e0f560310904035003030f448030070b40500022103c4014600b2081d403403d110b24040e01141c1f6503002d8006141a60b21940071161129034a02482c0c40412254031000c0c0b20210403c03d040018600303400200503d031090410b0346c00c0200c0c1c00000384041c80c51070000c020001d641810005084010403640d4a8201128051071901d54070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 278377410 1250 278376160 278376167
    0xd0e010e0f100902061213060e0c09010915030b09030901081506180109050a090f05071b170415020a030215161805210105100e0a0507020c032416 64
    0x50840c1e5400b0070740c1d00c880103419901c0b003031704688015006075005003240c41e100c80e203030318014085c18080c0c44691508a038604018400111004020002410241240c0c6010141d00141a40c0c1881c0711540c50101000800101840105030042948002a60700c0b000b0440c001014810014015a030402c003840303c2c1c02e420344230741c001c81d040039540d40c403911015015600182c1d100451548465041030062000207013080380c0740d01070740220b0b580d40720500080d00c4100d0211074480f04000320b003c0c1c0d000c0480e030a90006564621020041158110140c1402d42d80d440581204105012100250300940b12000426a060181401e06000300e19002c0b01e505000000c0140607895a40c440248110a130140b81c0e244c021803411002420004c0c000150442140d843d500700903c0c07020910a10f60070000460071800b8106c00c44010380b02040200501a6a007030030303070f80c00745c04040c000d001907008924207070b58181c4040c401c43c102c1d0300c8108000c03c0d0400848205a181a000a20224984d411000d4102074107032b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 278378660 1250 278377410 278377423
    0x9090c04120804300803090c030d090e130c06050c0c0d0b151005090f21030715050601020c040902040b0411031b1905070201090b042c09060c18060d0e010e0f 69
    0x400040982d02e1b5560b407c5403d01d4000001050b6500d44a03c00c60351040740d07848940d8a040d07400302d03402145684c655007917000040091a1005000e002020024801140305070090080c004a039003c0303440340160071021800b01401500c06540d0f051448040107140c807483e0040752080030b41513440303009040d810a80205030340140000640f203a100c0f10f800d5805559049501180242c0c229810403040104100583d5694000402215185440224481d06039501d1040503c0b803003068000e0101c44014000f080000d040503a012648150749640c140758588aa104404920030f1210300c0303580d60308201030690584c800f40c3c51031039500e2138108850382c082182c8000e0070b8a601401e0500d40d49a20311480140d0f40d803021030300704030b400d281c0115001070310a02c0500400d00c00c0e004031080e113082d113405030a8021506801c50706500f80e51301c01c0b001710f044000303410020011141000d00c0d501400c0041400a9410f82c05078201c44c02203602c4a4a40300d55a50038070590366617641140c01400c20040000b0307040d407600d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 278379910 1250 278378660 278378663
    0x9140306041e150b150f040927060605040e0c2b15020409150506070b060406320916030e1e010c180b09090c0412080430 53
    0xc0001840030b101c1c00c08524024140e800310b02c15500740e00140580d0014840c0c0c0c0030003480b4100c2d25008614a400c04c104079003000100b280110300d454204030110b4040c003101c0040000656034805840d507090f2503650740c120454401c007000b1988500d071600704070540c3c0c9040e00c510350036000043c440c0802d0b521800341d2542440300c40001d0400d070401c0719030300d1680486c2a070064016445450202080075040e03005000786c8100040030020058201d240b68800442400b601d500b0050810000e030109030780e5003880e070303110382c004001250541c0c40e030710040d66072154544000da000c10044485000c60790b4883c05103c0b0407006030740001c01494000c803000d80d960905213200050550780d000821400e502408010b51212030300180641251201d40102d00070b19814602d50f001407140f2100713a01c540c113054001d80c101d489082181e03052a8660f0100544074101030000341d2511001c200c00560102c40107000300205001300c2c1040d1311140340a500070307044101004d01075400342020000b250000f0040304041c8006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 278381160 1250 278379910 278379923
    0x10803040e090c030102120f1b0f070c08191a0405060f04030e0a030f02040e120901050f0706051e0a0207050d0c050f07090e010b03030f090907090e0906070914030604 73
    0x19102c590342c890410f0b880c41c8660741c040d400061001c51112030031840307a01a03040304000342da0691703513101240107032103010207030807501b03001080308021214030b060241c80400d0023004003440c41542d5122980c80d041d00c890b070300c264508002c1611070501039450714107964a11844c08580807072410360ba0356525500000d14a4440c0758180740030505141c86106100301c01000941003a0401e0b40b00e09054141305040e05c4224865402c5c60403449600a004c01c240c001c0c1d907807030820141021880c800544260f00648a000c00c410f00c1840f046011403030b0ba0085a000740304111159a00341c820003008281454020918040540100701250010717000140d124020001e528107195140071900c0c004d030078400545d26903e560303c22178030045000b00c0194442110307000305400801c000e201001c181078481c0113004081a5040040c0061229424000d501c564000c5180c64035489003922188144203055041d2400e803840c5e804a07040214050b0003201810281010b032031b9040401d40c0041c0042e54a14000313000600d907 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 278382410 1250 278381160 278381189
    0x10240e01141c0206030714070c2409060e01050706060b0c12270d0206180109050d03141b03030108030712030513060b030c030d02010f0606090602060f07121112010e01080304 76
    0x144c4150407405082500c110710541e036180c58102700000240c14014a090860b0804902e40720f100c56002510003900e50703446d410043d51a1410595080035801c80c21414002b00704004400140360344241405400521380260700c0f140c00b14542072404050381051211a60104103d00c541010001c0c00f6621032804000f03202138400ca100450103680e0201d20003500701402003080b0a0240840140c0b190304a0283e0715006503507951420840301c0600780340d0240100c1c2e80d80ca407000042951000404955181c4050b5801c0041d866000c00d141d540243d00c4658140c00120304107042004088049001245506c0c080c415400c01c104550440c41500e900100a00e54a40045200b5142449080010640282613480d2100007103000380c080c01441d00d0b66480c55280410126049000e00e881c101550043d0703000f481a0744c2c40b0b6080d00c9110744050810f00a0044460390300402d500d86015030420440c0c60f048094941410161008070348206070082201d209211005200c480400015a000c032000200c42d2030a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 278383660 1250 278382410 278382421
    0x3010209040c02010b090a0203061005030c07021c0506010b19030e0106051e0f040c0503070f0306030219031a010308090f13050103050f0d0c030210240e01141c020603 73
    0xa108200303110380c0150528103000c0310181c040d80040c0c0340b050309a6603200165550281c0c074049110444503154880f5401d0a00d0341041c0c0f01d81c014517800412013010601d0903085800180307040350307000d00171808100c802545000300801880343c2401403800c0c10126081003400701100d440007442c1c501200826965004104280400750002d10045c03c02811a58041044120610301041c2510388240100c203c1000b146182c2010320a00f090b00c0020391792682182c803079000488000700ca030b80900d420103031a13142c04809a0780340e00f540c1d1410000500b80080071881d40c40d103402c1c10107814000c9102108080700410104040c0000c860188604951140000a491000401030b01c19400c1d10004245440d00200c03c204001807001116a41e0108a8031011030f610011140b8815007400140141c003c000319081306c068540045040c40c1041031041210b5140031f403034548042540e4030401c020170014004109034918000110280602951171004040d60903202d44560384000230000d015090020000c0d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 278384910 1250 278383660 278383663
    0x50f190b04080c1e070f080f0304140d05031207030f0b15130f090603050c0d0804050402071109070c02011103070b15040b060c030a0801054c0306031101020303040c090b03 75
    0x42d9010b280c504264000d0502c0c04c042e52a081c500890884540002d130209505800148640b880d4458500071031800d82000c0e0600b985c4030400310896040741998802500042050014000c040c5894940010625207200c0043c140c40700862800039151400c1500c2c021030302c070104916000e180c4809200c0d91105070030010700c00d40205500c45a80482d0306070000c0341490f070030b070807602c1100d001d40c0c11201155030f280e00704203014100501c000c2010350104410045030810f60040e0048a000710180c00200d802d580110f000c00c0421603516000a0500e00703003500319138000b80000207100c5031500450505000c3c2e61a10350a40d4043c1640003041031314003099034981c0e226000b107c10040e000d0b00c116141e68070b0401c4242d480d0400384829000c45c194100104603828550540000050041d501e1400c0d90309903d08811a501c21260140114802001011710700a01e02c0003040c03801c04680d0002a40f5156040c8042001c00348500141150400c0043c04003103207101e0700780e0081e2004010009032050010380000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 278386160 1250 278384910 278384923
    0x50606071505040503160803040501060801060e0a0c0333091e02091c0803010312030504030905060309160f0602010b10090519120309050906040606090b0a0c060504050f190b04080c 79
    0x811091b079401c06101000070342009907004510079002441844d0b12281218280c69641c020005010f000c1030010b1280500c0317400203110720800e41000200310403544403190418111003018007000e8401090b050b8001d50221a10f4014001c03808200045c050075a2034190405220325032020032500032948402980d40c501c25200c4141c00c00c011030070100a20300e031501c031340d4000348000e852604a00d00850f001d40d020b0b008541c85980c1c1980c500700d0060074801003200540005e401d0300300500c00c426012041c4842e40011001800010540102031803030400003d085d1552080018040d220144032046030135044400035040d0798040b00e05040c08031200515954a5105501032035100740d00036255400c2c581c005d00c000040d20380a5444404a5503a041840240c903028820800001e00e030b51403c10058101c40080c00300c4c20341e06c1c500812891046d0315090103440b01914250383e01d400001b07100407001402c0046800d5805040301182c80300031103403101c0d410303004018800740003c01c001502c0180240d084c09032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 278387410 1250 278386160 278386177
    0x10e190b0d0b0918070906051c1a0705040f080a1104050601120903090609170d0e03120c011406010804050a030e010e09040b0105030c120304090f02040b0a03050406050606071505040503 81
    0x80740c00d0789002110350504c4030303400c59603001501980c0004200180b07a4041d0310305855003e010101d0400008004400f40c1c07410300300903104400e10407078891070789c1e81807144039006405503520540c640d410700400000d10401540480c05950006414900203080400030304003d0200700c80c00242c544d10b15006941c0008903982002a10703140861010800d9000b1000c4001d8a503107944000c0c0b01900c070481220102e41c6021149840d030300c405900e191461140d8404012040c1c080d00f44d683d950404a075004a50704803d000310711994544c41d041d951268103a5003e03a0001092030300114a0609842d2583ca0f00c80031840901008540790207502c1031790140c101d0340100c02000c1e0001030350b8545418511100f840a0280798802e009801810b01e444c60400e95180b480b02242c0055468103141c81510700003855020907603001640c080c030000803201e66002c040d0a0114194034040745c1c910b001d2804a007200d10050056102d0482846500080f402100184100712141c01c000107036034980381815455401030606 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 278388660 1250 278387410 278387419
    0x1093807051510090504020306040b100b07060e0d0c020a0b03041a040b0402090916091806051639060b030717010506060415201209010e190b0d0b 64
    0x204060501c851070001446031140080d00820f1a8807081a0015180c081d90060351542c444000300303000c1444141c0668014450802442c0015a9503a40c4441508444000d442c07881d0344111203210040d0900034034017451520310b40340002020b10744c00070720300c5140790090205210012000070200405949041c1c080301c00001c0b441e00b20f1030146046542000111800c0b8010400d00c004505609000111100c240940e51020300c0d000341028400c40082c555400161140d407800d04a000c0130400703034803406004000c100c6e002c000304025500007401140b850102c07000f102d035810b10041c098011141e0041203030b852a80d20000342a0302c03410480080c095011250341d2502540000041240c9410b41810409800c07200910079503880804118140c0524401d09000360124070546a04a119064844600f107031020010f5581441c44503252070020400340a0002400008481c0f85a40c0c004242c4180c0030412a11400e03700e00040c1c0c046030f004001d1190320454103021881014880258010b1001da40b8080c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 278389910 1250 278388660 278388673
    0x3030406050c0c06030a0f24170102071703040314040617070e0a0602030309010c080f0a230a09020112151e0914010302040e0703080306191509050109380705 69
    0x101c82c80c0082080075503a08102e071030048e00c001b82c6505072009410083c50305056550061402040050296003040e41713607919503007040b4420020b010b010071000388141c8080036580b00d282914018000c0034002101c082c1c88141030104004080c0e0144a1030b619400343d0040d40d045403105402628034030030a540481d80b20810080200c0c484d54004051441024410024000000044000d4420680c25214113503602d0340c0d1000503080180a07000059000340101d11040001a001480010700c481610000601c07a1500da080040d5a4010110410000004410014412584000244072600d071084000c150b0005075081426120602d0b0038004020806050040398807040c10304103a014240002c901c143d24244c4600705405002600700c042d40d901940103891510750f0020070812203450300d0301121400c610200400c0d2001d000c4c0f400701e520021078403150300c110b0500001400c0d54105412030844214080b03051140c4000a001e05140140e951184849801c508560b07120319108921000d010340c030076075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 278391160 1250 278389910 278389921
    0x20409081204060605040c1202161401020301090506120334081e090a09050a06051f1403100308070611190e22020306040b150901020106050f03030406050c0c0603 71
    0x3464424402ca209080400806464030204000c440307001014400041c901c0b01082c0c101e2200e5801002038181c15030703400b40888180d646060f40c103007c913610005242d4021004000030f0300036002d204d4100b40210351040c110010b900e401943c9000d03207940405404030042c0041090240305c151601090b1283c0301038504940503051111f041c2d4856259040040070b2000e00e602d0079040d00094854403a401441d0403038003031408003102c020f0207001d492100d05540d9001c0000703c51742d131a841e03800c9400c44003022090040c0a103802800008003000c200002510800400400e0001d52a056065a0340112001d03160b145508102009100300c10226180356000909021001e031030901030030080c2d003195640721b4000060f03c1030041000100002441d4024444c101051000c05500a10750020000e400001d6400399040011003d507a04070700081c0f8400700043e1041c00d941d081c01140083c007010303945080c000800e000406c0c1d9900c600e10035101045004544e0b080011814041000d40c01d1009043c00e07180d0a28 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 278392410 1250 278391160 278391187
    0x40c11160f120209010b22060c0b07031109060705150709051002010c171302150913020f0301030618060c02060a0c0206100501030c03060503031305030d09080c01050702040908 77
    0x440c0540c0050010107440060078103000705003142d600d070740644403400d943d203401400000340d04050a0b008400000488000c078112001000d00001c1a240d41ca82001e0030543c00c0c00e5402100280c60007080601b000090801005044221601e500701a00c2c515a0782c03185003880b038140080900c0c1e100c0100c2c241d4003406903844c0d1100c2c091050f80c40c03c56850816120095080c0c1c00c07a0a40c004000104041c8007045007000d001e000001e6015001c0b0f050362010035920781c00929207000000ba41454881e021070844ad9509240031b4042056051036411031829400010a00341404144001010540c95106510520603e52402d016165000344148035504c0a50f1000e500e544c0c0407039150301d090340303803498070080b46100040d168090281003050042c0d150034000110050702d0001199410f068546130b0001d8182c904000903c401d401d10810082071500b00003c050901c0c003080c6200c820404aa0b0041c41441000308103074280801c2401c0699071000241301240107054140c0c40540500b10109010510310003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 278393660 1250 278392410 278392453
    0x17100f0b040509010b0c07030f02060d02070c08010e2803050f030f09060c03160e0109080d020619020c0303011205070f030506070f1b1709090c070b01060507020d02040c11 75
    0x10b0880b1401c8035070b81c8a600c07091450060012158690b88510740c100086510420b50701007880c0080c0403146050300c603041243c143c0c2c1c45000d003210411803170f841c1041060801c1c480d1140655524010700902c0001c0d494100740341280e10b07444403541c44c9002505040501580c1116802400d0501150712843c10f030344045a130000442c0d07030080600845002030014840281203a11800100b184071072981c0340040111142e01c00041c000c1c3c140000110082503400342000b0741c4c6000c650300e5000708043d00d0300703c0d0310407c1c000d684850410781070b00510204450560100a90781521030364032200105403210b04215241a0540e071001120562400d404000e001d8081901886200e15480f141c1c89801c00030340446250452900300300101c0c00e40310b4540b00140510b202250810516400a8205580b074000505c0305801940d040303907104000240c11301080516241940140024200107081c00c1c099000b01d0800303082c84000a01c51a0380300c5111240c2d03406012101301803840c400c112a032000a4504090340c030341 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 278394910 1250 278393660 278393669
    0x11010b04090b011d010e070806030c1c15060f0b1315032307081501020c10180b030c0304030c0501021201090b031e0a0f02030a080715051617100f0b04 66
    0x110483c1c41c2c1c0d0180704c01c004070b03040343c2034507140c1241c2d03503100b0380708440310040900799a078140103c0c0900d02840d95079085030001229482002021550700b85044100e0380b20200c060503489d1300301441000382e48502d803030392401c40f001280000d90b00e00c1c03002a429003e251a80007804132a01f001180b248440c2d0550000c0b0003000750114260030382030202d50741659680c00703d4885001035500e100044800d1800503040b0120304040c011601446c507040c2c00240c070107905001d800c0010b10b003c075100e22024110b1081500401d510490549503041c0110101d0032480014800382c2801010b83c1c50b9030800000354110741c080e4034400340802c00d558440e013890b070251411048041c0b00340308041070241041c0c1c96011110b034a11120f80103100e01001a0b42d510300d03510402c04161f80c107000b800f10380d8020405080060449620a40910b124100340344105000c07100090000c1c0300c0b100c120710400d840e49070080d804035401207a215031243d156481d1104c80b045404140c01100d01e850f5486030010349070300240302400c144d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 278396160 1250 278394910 278394929
    0x120702161202091506040b0d050f07170403052a071e0e040b06030a0507030506071803080a080a0e120705060f0c040b160618020102010608070b0a11010b04090b01 71
    0xc1e601c4071400541c40c21868041e43c407600c808040b5401101981d182d1035006405050340e410b040d40e880038481c80341c100740303a1200455155410040304500d540d022a1744007000f8246207595000900304a09800750041000f42401000202c020b08851a17500c6015800d81481c180e00380613200011403602c0750300d00e2060100c021848440c8100b0701a00070980d20586880c0c0340c0c03055031a5107540312060080c0f03002d09100d0301401707050407107000700e20148041d101560084000b00414200344400500c040303005940010007001c1c000d41800040c802c20100d418010341858000c139036440b00c03400040289021012001548102c2d180c180010f607513031019204450158055460540d601e030f0182400701c00440b44c0010500c010407040c03090010540c05460b006024802e4100d080c0043e80d03070b4004481100c0701c101268030003940031404560303090040310040c02040b4050000203107487d8406015001e411000c40507c8209404800041025800801d04034401001841317181e400d41080f03c4d441200b8022083d14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 278397410 1250 278396160 278396203
    0x31806020f0d050a0e011b0506040803040b09010b01050d1a190e1f180f0c030906290609010323070813050a0f020d0213020306011d09011a120702 64
    0x2154010000c4c2d4407500803980700c041144403440c00440e905c20754034a03990032a00140c18400c001c640e080001600c641c3c420b402313443e43da041c50300b080f00b0702d004000c0100d10503a040101c88201c50f41d2103000d44d00b08285d000400700f00500c00d202d0102c17400c1203240c1f800b80c000c071242e2003500c0c91004512002d4111240d00c44541419101e0040c00720484510300c0c2c1c03012a0380c440b8a81080a00d00c030000d542c0790350f00300c8280001d0758010720300828141d50608501200083d00c03074101e80113020541c8a14031039140111940f503021100001c14902d08403140c10501d200e00b030082040741c41d6900a4200f1190258085003240d8800114a040b5840790700968042c0b0000d4180c500140d10b801074801410031280d00480100300703140c03146e07407070781d941e03408000c822604110080c010000503120315800e0320003500c6211001da140d25046000400c0c0c2c032407828030540352010301e040f4060b5589400360f010781914000c840782e8400c145001d8248036148514030305820042c007503d00304011507a021420045007038824109048 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 278398660 1250 278397410 278397433
    0x60315040f0204090e2b0c0501021315030506030c09090304181d070b0702060a03020c01152c18070b0304080301032018060a0807120b0604060f090207031806020f 71
    0x1a185d002e200e40d503001011b11a0401d0030040f00f658030b980141c01d5480c00c0b11807819542d4806081e6041407495040040803108140084e10b05100b1441c0503220500c0d081285190420020303a540c0d04414115001c2d06000c0302082c4001002d1040764043c0c580200d81040c02c640d5031503400001d1400c501c0c10b02c400620110412071100c000310340c04084400c4400154100407460f002c0080d0f6a112541c64800e03d5420043d0300070314402802040c0d0004d010304000380c400b5180441a402c2c02c017000400c00429012903118805200611010a400451440d404a0440c2540300c0310b918112043e000200003190100421080040345002907041c0e03032086071201501090261003a040042800d0110b6000c0343c0b1911040106841c1c0726026809800240240300c600e03a10a10241050030300d80100918901128946091140c0c0e038100c03d80018058800304150740c506104c50703152800c14090064076540000e140c4090501c680a0740b0046598070050069030b556450020b592103604085107083c0f8003c0418950 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 278399910 1250 278398660 278398663
    0x51803030307050708030c07060606050904110a020d0e0621041e0b07080403020a0b01060210110408031606020d020325020d020303150117180f010e0a02060315040f0204090e 76
    0x81c069a002c1e03d409007468069991003680e41c0000b08030700103074a800c3c86800301091040c094240207054540307a5580e500005014001507600d690b5000320703120410070170710071210b03030018642d04440c2d058030f010604554010000390207032180c10030088095111101410341c0b03000314400c0b50301840c450001c07030100b16028401c101e081064581c016041d100360000145005000c1e084117a0f210f4801d10658a11880a03603400100da0401c0e04410700591003c43c100a070400b492144103443c18414074072070b0405103480d4449a80384165031110500c0c51444907518100061601501c1d4680d010640954a81c50a25031507040c10007000000c8590842c11680c000700c0c2800451400c88544040d4051440d651741c60031410b50030000841c500303040043d10340150400100c06800540030300c83c0400707214003042d04102040e107003c000d8000320056900d001810042400006a1780400d65815200c070b644030394480c2c0003001100107010990380c00a040c030301070492140c601c0d8018010746055020401a8004510185 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 278401160 1250 278399910 278399917
    0x90b010f020c21030c06090c030c0301090209040204020a11120901120510030206210408070201090b04270b0415090f02040f090b0f12150604050c031308160305180303 73
    0x180e002030b071400b51078907001041039a403080f20300303503004aa00c1c00010031307003891510004a981013140e4201ca09400c3c01c5e86001c0c003141c0410f0104a000340101507058001030f140d0703000544003d21940d80068102c085078005d40c048640c032560801540c01280095450102c01e84c00b8120490000d020595000044861845880c0c050b956a05500044a0031507080c04255404441002c0c0c1001c000b900064180c1103401b90300c0c2c03086d8400e170000c1c2d80700d07019840050f20406954105648141080c007003400124a24407820699242004c03d0b48402e0410201ca40020115410080d41003801c04041c3c03404c0091018401041b186804030402c10011914280030807405903001d1248174180e0450104a550803d8100038803400e4001c01e0a007900390b002000408a543c0c0003101d007116002103038040039800c824061164403240941d0180818270708142e203444c05110040002c1c194542d2074140f00c05000e0300320203890000360901148100b00c007460401610907041002d452911140b001455215030a01000f83c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 278402410 1250 278401160 278401183
    0x509010e04210e21070b0408010c0c0209190b211203090a02010e03192f0907030905070801110d06090c02030301030b0703020f0a050a1206031707050708010501090b010f02 75
    0x3d44107561075040401164440c04020164504602c44811550762010b1021000030204000b9803641e0701c0c0f43c13041e07107030035500104142018410040075a80c051303200c202080d0ba1041007008801300c64440707890160000c020a492007a003000c0d820340b0410060388407004501d038401c118012601280f402d401078039100e00c4215408001c0d600020b01020055000320b503c00354626006064030032540d00440400d9450b54500b03416510792001c0201e107001148400f1221503407040012000c4584100e06011804800d4050306050070142d4803242d04052180030b00c500c10107048070384002e01a40280c2c4070740150940182005c80b00040c80c1010020340b1300850310071709000b0700d0290003035400c0d680b95441e0000b01e40e400a2111040c16003c0000101002e80400101060f912548032035441c1c022660f002040b050f80c140c0b81c42d450510300720b414400304400c4c4601c5074607030a006600c203980b180c4515015040c00f20b15071044800d03600b4040081401941d039000140030755000e0342c4000d48601504000c0369280900ea09 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 278403660 1250 278402410 278402417
    0x703021e1009050c030d023702151606020c01060f0302030d0305070908101e0515120313031a100b0306010c060207081201091802010203180a0509010e0421 68
    0x303420340200c9990b0407000403a4010402c3e680516800d1010071b0914808a0031440180c200004010052142861151403040c14440068200c10554205224040740c9031001c0d1052541d8210b070405410001c084074200028103490f00e401d40c5140c9400c10203900310110101483d400c01501085840d5040e441d0700403241c00034000e044600103003909078000c01c005030245c0c00f045104100815105000c0102c80c41c1401c8548002806a00f2418520060720010000c3c400943c244000c0c003d40f14440760107162202c00881d80c819903040180001440c61260842144180410560000c24800001400503101e01c1c5641c03090002c1d921038054242001c0c031401084200341341400410045c2d403003100ca007070300310b80306610040c40c108543d00e584125400405100a50141e058010700854142c1d0003003410710114458564039440c81640041e480b80140021070503040350b01840f0400f60313521580310348020000a420712403a561100040c2c015441c045030b00342d54a128682d070503020100c00040700c08202d041540d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 278404910 1250 278403660 278403673
    0xc0b090d080901031b050a082508100f140a120203060a09030903020603010e0604060609060e04020d1407120b030703020f060306010210062306130b070c0b0f0703021e 73
    0x15074101d100d07003040d1402410181e4030762882c103125000f0358411040c284140c071502d860351140c28009041c010700030042441803006201580882d07002c40c0d0021400100c0e403c0c0100c40340e4420f0880007841189500081c1040e104410001c0c12210444e004c100b5040156400d400c46c0343c6528080368040390010009405502c0035000030001c1601358031070000030780b203498079500d416603a030001100340d0000c0c2c01201c446038007402444081c1c0b0707103413040b074004020b0f40c18400006031600d030020f41800000030400d40182c3d0006210601700030558008940c0d00000c0380146c1c49030a05110081615011341104407055141c002101e81c185000100c031070803254001c0c5225410b0080009024003a040a00018150b02c034440c45100094000d0041c600a081030440082d5610400500c8407140100080d1090045c04100050650581c248070b82c00c0a031101071000315580c6286280a45482105902480e406030000c20001d21781c0b00084001c085441c0a03500b280c03040031954001c03a60081e00c6d1500840240e1200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 278406160 1250 278404910 278404913
    0x911030f04020d031101020a1e0e031f090203120715060f180e07030b0702120408060a0e10090510060e07080610030b092d240a080d03090c0b090d 64
    0x42c0700c1c443e058400e16140b1003004102144ea070030786e0800e4400780d000c540810085415540702d10031040317080d40340b031a041000c0d901400c00700c1c0d154801c0c0c1b441c111040c01d03040122480c10406400804803264050f08461004c1044800304005420510040b0386208280c162079001b40210301921040e5101c0c2020154001d00d040c0440c4840d150351060344000c1a04c030751007400faa19080c007400000390700500421185240216000f401d0090a01e0703401c40c5101c042c0000e01403000d00150342030744002a910001080c440c9410014035003260404180ca00390300303000100e0100003011a220001d112840c005008050300c1d1150305d682900300321000c1e0001549000010600d141c0940042c0f0940500e00b00003610b104000003244181d03600320ba20f01c451100026201c00c1c0b454803603915102c1d003016144145910300740340c40305200c4040010307076003000d12840ba009144641d0b10480f8a80052561008079880745140354005000340c640302c1d6040da8510704000000603009400c5044500b03200b802401003441081c1c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 278407410 1250 278406160 278406169
    0x30b1b0906030424060810110403060e0c120f010f0e0c01140906070317071806050c16060c02030f0c030c041a0d030206041203060e0c0318010c090911030f0402 70
    0x61040d1481e5202c1500e0743c03074442602e07100d45501000000003080c17460814181030b1510b0780d02178982c0f0340d891070500405e1503500c1880a0b981940d0303000c074001c41c0360780d81d400c110703840e2012080c5003682c00541c03d10b568031020000581e00c000c0d40d6101c0000d00841ca070000c0c0c60011a44240c08440b1150022905c1d1a00b80d8424141090084903031400b250824850702c000c40d030190810282200480c0281d2101500346e080c401d8010384c09a2685441480e00080342036118040c112440b841080c04004545d5840e131050034000c00c684d801e8002d0034601241d941e40802401200c00c14070a90280c014940b02100480022130701c0007003104090002d107000f00d8003206004c01448100b8600327070701a58440140c20540d0341c0e01d071494080b90003980140301070306280c1011002c3c070705600b036008103052900300100714404800181b1036000040120311601c0b81d54111a00e60340d0160310091031030035441e1018041a10b03401c16080701c02d9400d81c5204001c40804a07074810154801500d10102142082000130f005180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 278408660 1250 278407410 278407417
    0xc030103120c050d03060f0f14120a06090c0e100608070f17090105040c14090a0506041803050309120c0a0f1704141008070806040e01140a06030b1b0906 67
    0x1403a141c2076000400300c1d03e500c0e0418001141600000791941820444440d803d422003025201d110780038007005260001e0300300d01e0403174500918010000d111341c000f6110414010450b259070050414000e0440d60b161410030100c4d207000d0503c4101040d0045101112102e042078180d5a440c0c80d140d03074507107446d182501c6421074071580d03c0030060780d907440e10080a0325640b103034050200d0304004181410b0500d40707a240514960044036580d80c9051400d800c655400100c6500070380240320000d6181c403105e0115001e00400d901d52040340d882c0148a00415500c400110320801241c000d4400641181441c14468800ea0724a5001c9500103d941c1c0c0101e007403600703120241c41c0700b251060301e0100840070000154005034007000030980568289511800d03c50140020101c4070300c1c00c011035242c100e42c045c00e00c40d4080e200307a009907680d403a01007096000358070803561141c541a40000341c0c138207001c06001906c41400211000100d84010407410034403950210425018104240c0c00c1c05982c0043c083c1b42d81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 278409910 1250 278408660 278408693
    0x9231b03120708040510110304030f0204090605090d08070509180a0e07060e0315070f0804050325110901030b0703090812010b07060b0307260c060a0809070e0c030103 73
    0x186010030a10040c0348401004481d00c070300e80305915949070001b045100200807107070300c0c00e100402c0f030302c100003520100c2100c0581e075100280140d410020300120f0300604031f0b04c000420261804050120700480054401c1c0d41c1c070a41e984d81d05d8695079a00c0121594000c80450030b41100d121000402850b01d240c20490303015060404c00128081014102031410903103500039404039480340d1641805007000c0c003002c80450381c11030341ca00b400d052540000340101501d60010040043d011f010804002d410720032511000e04540b0481100e051603424003e60914201080f9541c84000b5001300c09030400b40321140c1280d41140c0b80d228181ea40320000d42c00742c070710603108035a141800c0110786c00340e601c0ca0103460f0103814801215a21004507181c00002c4640700100745110f507110754010031001c910031050101400e040c100c51445c03040f1039003100785041030343c1d11029804200419440381440e8026201e40c07141c0c0c0244c00b280c00d140d5807100320f182c801c40c003512004d403031203c00c10041c404200400410160751 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 278411160 1250 278409910 278409913
    0x3050a020d060609060e030601061b050a0c230d05030f0c07050a0308040512010614041a0402070308091903080f090a1208100f0b0415020703060203040609231b03 71
    0x20005001c003100c2d956048500403a8000c403062003000d0340111000303d00c40f81680201100e504000f000b074440c7c43c0c1e550019074402142040701c000c0020500007145925032080318030710081d490b01c260016000244001d501140c030307401c1e1640b026241903000c0f1500d2a030410080e514110083c040030042c3d6100c184110307458407420310f00140d20340329090703084000d43c042c101840d140c0b410b2004120b40d030b40103554908010383c1400340620440d52805542d0f800c2c50000c40340017400b0b1003007440d003048422039002c0845d4001c0c03003c00c40c082070541280e2414030890001c420759071006420341840468422241c8040c0001c4d1041000980060302c240241d80c0001c0d0083c210703074920000e50390b050b1416001c03c03440000204a1001d00000f03541041c1488040c1209180c803010250400c081c1402074016485910905101c005010072298002d00014020f5500f1007070030742d42c80c03a0904001c0c02800340301e00c04403514885541816283c2070030045645003002c80340041c0c0f036032896102c07200d0348841c031109010382c3c103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 278412410 1250 278411160 278411167
    0x41802310b030c0a08150f300d0207060203040f031e02030f15010602010e06040602030a0605090a060e01090b06120a110d051008190602032703030a0c09140103050a02 73
    0x500809030091445000103d4046039a09a500e00c02810402e014100494040350055040e03c19603441100240504054442208601e000d410102c001d100b55040540c4480f61100c000001c2100814050b6051549408031840305607a000120390b248a24400d003400d001050b081800081c0081c40c000e105040f10f03111580600e4560380002e400e122088946c001607500100ca89404005008411401881c55000800c41d010240f01141d445800080c40100003a07800000101d6800c0c0c150b0050300a40030103031003001240f50001d03100c2c009151a02402c0b1202030f10000001d0203144074050240c0c813690103443d8504000007140745132002100640121412500c9402c0001900400c1028141003a056007010540e801c1003a46402c0303c03d117941095281e0b0700101000340759840c3d12a40403001c150722100041c1d507591241c0041043c10019140403074031989488040c00340315800000b840c041d01d903615080112807078652081da540030452007009800f405180c00c031180741d07003c0e034803140c3e101001610141c83c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 278413660 1250 278412410 278412419
    0x31203050903070b070c110a0609032a080304080f03190c0309050301051302090105241b03120a0b041a060a03060f0b030f0c030601020a17071704180231 67
    0x20b00340805c5030300c90700090654002e0414071414101e80c96001c1c0c0c068460159003400c144000380003005034003010340140041c80c080d0700c602004aa00115035800c04807000ca50359196814680c480c1d0085c850078100d8401c0300800c1007040d0700407088816600b624180654188030102c0300381c5112a2111068081c84640e03440099162401e0003042d10882584a40c045403402e82d1040183d4840182c001500920318000c001158190126401b099400105101d0ba02c482c07a50020640310038241408000754000400e1200d03c039503484030424010210742d2014401080c1c094184021680d00c20708040c00000000640500ca0030070500800640c09945400b1404503150400000429071760707807214412071070020802c0b00d580d60041d40d031074101e800708000c50700e1806d01c000005d50300d440c40440a4072203800031540c4400500c01808507000781d58400740d000b20307460260318180087d4025104004c2000b0000603129600201c070710072104a580c0d02e00811200c101ca4a04c200115204019501c0d5072000c09100402c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 278414910 1250 278413660 278413673
    0x8060303220501020d050309120f0f0c100e010c0f0518060403051b0a0308030a180209070c11030d1d030c060c010c0207090e100519150510080103120305090307 70
    0xd50501c241c1030031800d070380e18000c0024074100d0104042410040c0c00d100b400b6070340c0030120f801c030820b0069104264803508501d99043c52442000f596020194001542c0c4030200c0340895010741448841130304200c03100e140201c40b42030341c00d1101641c0000740d00c10803c042507801480900b00c000003107c03800c000960302c400883c1c155801a0400d9a42d07501c08030030280c4090700c03c40b0075078544809480ca003201520310b55402c0030754000a042c5180e030544982010301140d658614840c2c41d240c000300300c0d0307109040c12a00603120032011601507400e0310084e0f66031721140c1000034006894414994598107400000e0b800c21800c04841014580e05001c0c40c58003410b02e58524002e000030014245c0005450707241c004000e49420251b900c64601ca5050078280c1113481d601003600c01e15004003010203e929521036403203114143d010814241c01c075181c030780c5641001440e501d048060310300940715801c840a00b900182d4204900344402060b0002d01c43c41052524440c0c0c1141d5001000300d41243c0c1480800d5440a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 278416160 1250 278414910 278414947
    0x51516080c0a110910050603160309081204140106050612041a0709090b0307180c030f11040e0912031308040b031e130c0902160606090209030f0607020d08060303 71
    0x588095542083c480301902c2c046080640010440c0303000c50442d850034002c00c446010044c071042c2d1000301080340c90050b600070b410108082e40e21004080d0354007000030f01c00382161020f45080d1842c0c3c152035884515610148245400d5440c000c0c20b03941001c40b1030496003494280104211ba00c07090500e14052110301600f01c00f80117500c192283d01b000ea04021220040b10a01c0d94141d2003548901b0b010420a60031140b4a00d41c421001c401003486600303c10290302900041c1c240003080c5150a20908441843c8405801680c0c2984083c401c1c03a2240c22001d41d860034152000001150304101107102c1400380300c58044224410010709050642e41c0300080c00340c1d002160140d0221403d144104100403100310b2841d0300401034080c5030701480d00c0340c507000c075001c0903800b0f505140d59002420006030291b4020343c0006030ba000c40180301d941d442e100160060341000100074040d106030700e00203d00c60004103015104150720750091183d5a50040d048034500006000035030903010400400824203a49980d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 278417266 1106 278416160 278416163
    0x1a0a021c09050111010b090a060906050a0f0b161712091524030703050a02030c06030c0d0504030c050f060711030f09040203041a040b01060306051516080c0a 69
    0x84c41c0100742138502191f02c07002c003008100400c0d0044e000700003565504281848026500c2080c801180828010140c880741c06403006d01441000d000a00581c01400781144d0600000703031a0012100c94544020184480000300904038000708c3c0411508041024010684c269130650200e010000180501c60708440702c40d1003106000e11003083d800e00c0c40c001400e03148141c0e43c901d0050781c0c07100c201000324001d0044102c1c0122130300c1c101b02a2881003507880549032424101e4401140107080c0140110144034041c01d1040c00b0400801c004840d09240e4401089941400352000d803461060345400c03051640104003649144203d94240c1da80f001040c0c2d000760b26074466240c140605012031a22190b49843c3c60f0411040c003400c01c1402c0c0c102c42c4a62010001c04c0c1d2074005125503045242c00d00303a001d0700204545e1039621619003002d0035940c05039000c1d600f004904900c507400c1a441410 = true := by decide +kernel

theorem cover : BRFrame.Cov 278237410 278417266 := by
  have h0 := BRFrame.cov_init 278237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 278237410 ≤ n) (h2 : n < 278417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
