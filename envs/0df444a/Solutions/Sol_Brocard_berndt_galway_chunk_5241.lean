-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5241
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:12:54.801551+00:00
-- url     : https://prove2.me/submissions/dd3c2986-f360-4f1a-ab7f-715174d84ba7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 942446043 ≤ n < 942625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 942447293 1250 942446043 942446077
    0x50613032304140301090210050a0509060c03090103050f090a030804140102121009060e04060f0603140703170408150601020102041d0406060609050a0303080901020702060703120c021917 82
    0x20001d600d1000400c11201c90003640f000581d285001c0c5400d8441e1590003a5103c0000c1400c29140b80c0140010000da10306c1c0e01d0124500940030000a40c0c0c1d402c050000f84007903001280c0c203a2256054442c558000c10702194000051400b080755664400c01500020b0400a26001107010000c02c14220a96508010020364841e0381802c20352403400b504a0f004c070f0141d1030f551030000d41140d480c4039910170740c2c2c124a141191542c5645585d0050400700300024100c0d03a50b200c0c00070105001c0e9240c1c0078540040d4018081c4946981440640c40184070242240342804210810005100090400e901c0d40000d00e07108040e07540700e00603030090149900c0302a0308080d4140700d403442070100708100d200e2071084804000c5c2c0ca4a410b012504024a801007a8111180500a101003030142e00481da12114042c00545030011690119010740c01c441e0048010405550250340402070074002c4c000100b00c02c0c0b0081c41181c840380105800004182d5000c0d007400e0502e01c0340e81c0c42684001c1100c0d01d800700105495 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 942448543 1250 942447293 942447347
    0x2030c1203070201020c0f06180f040908040f1a090423130c0f06020d050309010b1e0f15030a0c12060602030a02070b13230a2c0405061303 61
    0x80d1241c2c803115040340140034a0403080258a042040d0780403501002d003582e42010404210404c40103890104a94041c00944800205588500800300c8080c814006941c8944c50160098202d05180c1c014094401c800808000411649415101d402d07008580c046010000f01021003010f0011041e030740f5095100d10100142c100300c2f00c803d035007118420725503c80b00a50300c0c0340c4c2154861480c080c020050304860310b10203c0612036005950448081400000e20001480004d40e25501d000c02c180c40314440c01e03030070074081d25080018849060054400e01c40190314005881594800201114201c1d80d80310900820f440c4200c083c0e070002400b034003040000549403040a03541380c0040d285100140b003581c0020482403402e00a840b980261701c80d0544445041075450307a0380e41a03020f48820311a0510700d21403481d6442420032801081c2610650500401143c8203145065845035107011208070705040c0300001c0d0700011381c03e46c04401d1200580c00c66006140444d28145d01c0e051415a00140318602c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 942449793 1250 942448543 942448579
    0xd05071109040323041406030f0114120a0c091a0307060513030804030804030203060702071a0d020d0f1505060412021e06040303030e0c09061c230f01050108151302030c 74
    0x4001b40c8400c0c4164034400c0030000104800c03403104544030148006144010001c41042880504020000030540101100d82406c1c26107424002141a00c054040102c04c1140340280d01c281082c4000a10f540780010307805001096503074155229500420000013484a202c00280122901855028400300c2e592540da09264656030400c0c0003d038400e000e11004540c2c02c90000409504980c0000c1c64154108907420251403d60401c607080048113070200103640c176001c136510802c8074003100858005540b085529114503030341d450b0340010340910310400c07091040354001c01e01e035040750f0b07411540c4085108441d60740c0740480b1140252203402030f0012902104064040d0441c0201e99101d0302220f07000103011040110010003030380c450350082052901901001041414101258007407085008465480708140d0460310700600480e94507005002c0342c090300706081c09100d0041850400801c55456415000c102c1d202c0c0c060f01d03c18000e04c6204801b01103403000e0003551082803005000d5240620000c402c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 942451043 1250 942449793 942449797
    0x3121b020c03010f06030f0f020415330210090816031d040504081c09020a120204050f161d0a06080103110928060305030a0906020d05071109040323 65
    0x214030b12075402c114450300c0441c401d00c0341c0b40840e60424070360280c240d0350780c60303050001001c45002ea0b0425100e0b140d13120200241d0f00340034018499400c01e00e10084403010406081d83e070400c2a60300107103418441c0c01d0380e580c0c000307164418001ca030032000410314507034a46940f092081a0101204160941c0c55005264210807040700d038103040000410740c0c1c401c9008210842d90215001050008140032680c51549103421480103000700304800110441c00740c0004140e0012a888480040c013460300e09011410940910b9030096042100340030141407402140100e02000440001000801d91a50070004100c00101803c40005440f02000340d0f140d00005082030343c2400306480d03007407a08a2000443c1000030300d80e4802d0305c41c0ca40c4100702640300f4801008941140b120001103949520011012074401c1c001448485e01c962a46040c10b03107001c070060304084844a4030002e2003014400807000c98200303503200c403402004031000030362030f03540349000d40b0a0344401248522000d0304070360560001c154000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 942452293 1250 942451043 942451063
    0xd0201053a15080106030b040314090a0b0306040c02010b030c22060b19020316110d0510020a081008060103020118080607170109020414040f02070f06052502030703121b02 75
    0x14140c0403e84480505080e68440d2000814801e800400140440e1145c1c42560390000c0441190380b0f0029280c00248400501c0d41116803541e03800002c0c407903a480c01d8070070030a10707007440d000901151029100180c3c1350b8500460030350150791108001203242c203d5180c404d024660f280800c01405840d0000000030307401c01800502d50440c0000703d03010043c00002505c080010344812904403a60603030f0345c00140030416000a03088034244410200240341400000b125210034000180c40e40002d440046c0b80c43d40103014a018181114418061030340c000c540b0030b0540e034081c24004108c040300214040c18225981c00078015014580a110560b80c3c002402050040b41e49200345090740c9422201c0102d1140c1c1c42408000e0050b41c0c00984a400d02d508035500701041e4140040c107142450f01d03030400a8018520444005070b80300e04200c3d02c0c5040061002e50060700c15840c02d080b112407040a0b56911030189c010381403240d20300e084641c540c0aa009400d0100501c00030700084c980800c8081d5542900b12 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 942453543 1250 942452293 942452321
    0x203030a02012004081b1908101512080f04170d1713030c0c08060106050301090501090b130504051e0a1703091207060f061d060d0201053a 61
    0xc0b6040107120081030a4505171000035003c2c0c05203d042d00401e541c51410314402e00e4103d0840400b1000e0030035004040c80061a50002510041c911004481c0c115040ca8241c113016000d006000d00c80c0d828005c502c4540c06071300403103031555016081c50416080c0215481140c0c1030302081c4140c00c404101140540040ba459214802251400b44407407172504011074843c503c22078810641004a446074195100d0140202e0840070100e49541c0002c1c28007400340c0001000c034100000400100c54940704041c014162650f040102208000000342c459103d9105aa4003503220008107082c05003d0000340c55128501c01c00e00d150030400c3d0301860311503200c040281c0e58404030074074605a6440c1d800450388240b80c0080903100c001543c809400c404d4108060584103956150f44da0307907041c041071060b51701801100600c03513800461342d404600f05410042c641805200840031110050760410b05030f844030788000016202082c00754000c0c0c0305000309107502107101507403a40309411084580d0b10480a001450b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 942454793 1250 942453543 942453581
    0x14060a180b0a080906012102210f070b040e040f021c0501050604060602210309280b0c070f110f04141605030c07060c0e060a020601150e0a03021201090203030a0201 72
    0x5880040c2e110042407203165040c407008421f4007040505c0b0310034091024402030102d00206214103031511022010404070f052a0b10401034000682c02c00c010407030007441d89e0f1640624080c20205aa100d503000500000d009210710b20a25003159600e00c002440103a9034000c4801c00ca00e01c1c2012400713072000b9500903024a10341a00450f540380f01081c484010020740444d010941480b05c0a1161030348010715200450040101c0414070203c11000c4559030030740e180d87c03020600c0c40303420f000c0e1001102505441b4121420816000000d80392545c0400c07294005c44920648010040456505081c1c03003c0713141d01a1904400e00c1e20255400341c0f1900a45c0c10750f54840c0004204102078400348000e5034103c0808800388002e03800a01030381c1100307016500318a0300c800030ba61044041049900000103820141c0c20000050141b00f407000c650f2140c1c5240d51503c0b11248105038003241c14031065000190040c2c14501220003030307802c00d400c02c1585540c00f80880e82c0d50803c0c540020300a200c00720003d4084021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 942456043 1250 942454793 942454801
    0x109060f0e0102072d0c0e060405010b3105040c0801080606010503060607110312041d060105040510140f03010b121302090a0e070e180c040614060a180b0a08 69
    0x705100750750049a0000c0100c1280b24070003028101008402e800340b0401804e00704107000203100141c030f00c00501000550407003909050b0200f0060380c9058010313141252083c002040c4000100391382d030709001140c00703441405c5043c00c01350320000180d54020a401504191610030101d038008070041c12580322509039400c6441d00401121036100c00d41d00da6501500500c48440484d060071088149408010119094801a0030800b40141c0151b4081c410102201c42141402001090025440300092808602d03080c1820001000c50031980704180420000c0281a40402d8003201202c039035491400009840350303900c0344400c100d54404114402d1505400022400301820340e15140f00b200d5000705004882e0381da50501c0d07001489400c50103003d51148220026001d42e130b8403c03050241d403114205100d880c500e00c000e686018501c0348103601842c41c182c020846078900c400b202c00702800498413170740d6503880103804880b9a2070101070807500c038400400009103501180010030007450740343c0b90a030207651 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 942457293 1250 942456043 942456071
    0x90f06121b05030f220809100e0a12050102090d060e0706020d05030c090120010c1710031410060f060905010c0c15140304060b0a08030a0e040b060c0109060f 69
    0x180000c0312201251060010581084403130010a912003514030071619221080c84465841c81c61800064072039030800242a851800c011001c800f54401c182003041e660760b005400b041040b01a4800c144203140c00b2800c26003005001e404a61884000074600c04880f401424024010480380940d141c40c0d1260140014007540080303981c1004140301e4540c14110341e20348002003450780c00041210704020405200314801c0c43c600e069810b803000c4400002806000181000e8102000c403802004044810820041c2001d0601402001d40b5402508560010070b82c290300c031b140850710742c94004a50309058010440100541408040319003d5580078141507640c3c1c015201505500c038042c0c01945a92802d00400588503515140d100741440e001c1d0212002d0a080035094000b680c0885046481d507005200074505026034001a001c01c02c013840c81c0001404000d4188003004010300d000c1d6448150418156441c02c090b51502c4261b0f000902c550300c80e07403421000901c00c40c3ca401c00c4881c9800c40400340c42c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 942458543 1250 942457293 942457331
    0xb010e0a06061403010519031505010807080309063403030c080a060506072607050f07080f060f040c09110d0c0e0114091318120309030816090f0612 65
    0x100c050f5501d0300d9079086c03a041c07203e83c07000103160001c0c039282910000700050728401a04204030712114001081d504095030141407101703950120f0800d80c01402100f600e90745403412903c240400710b01410b00300c81c01c01007103072103404980e940700c98038041810700806054064102c815490207075515024107566031045031013201c505006440c0c108034103001000008904044000580c41c801a52083e490152140780f02582d008041c00c85164000d410f5a0042c01c10411095020b000f0b50005000c03001c14090303403283d48880040003181c1d003100d00008141401400c0340e542e40605515072080c0500c1c1142d030901c1905e075000030402032a007880d00b442048820310905080e420748105a440c00000c4071481c800051580095140e10b0307016070398a01c0c84210134001c3c407130040c141072074200c501c01ca03141a0074203440d44203039207244609050510b000d140001c0c0e44002c019a01110800b03030742241c80400c150444040715940c00c100c80c5044215030220310a60002140c05120302000014080031801451070003c003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 942459793 1250 942458543 942458567
    0x30a05090d0801052403130218040b0f0c1c0e0d08010303052703070f031e0f2904050715090803040501110f102703170a06030b010e0a0606 61
    0x140700e100060000340b074a010301d2417403081c240c0100144010048510040c075030080d2510300b0303a180040d01d08002c604050741100c1307282d0100c1c15000c0091410f0b0f101c00040b0080107081c4500c0c4a03055001828004000c400e503040e5404c00101d0200044541c488180241080580c0c1c0d880e030f118244080b200244504103050580f0750560314241004002420044201074161081c900c0000d656000700c0c0c183c90030402c410040c00d0044881206178a982080c00c00541008030040068604003242004107804c800d40130300c0d180e80909241c10341c5200524086c0c4615071b900c0c0d8850740c118100103102c01e020000585c0700c2660400138507071005401c0b614064810617070134031503040190014002008190b001321a01a07590759010182e8041c0c0d080700d02000c1c10001310300d0001400315551441400c50345401c041103001c4a00c0309040d9616a00140c4002c0d0200c0c00710800d41365980401e00c00108100c1c40ba400003c01103a1180b0044c290f561505030004481d101203404200586c1740040000c1d8540c030411416104c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 942461043 1250 942459793 942459797
    0x140301090233030f0717070c030e0a091b0210021312110a090204080d050c15070e03030d0e010c17011a040b1b0c0a1401030b0f1203030a05090d 63
    0x78000e003580440340039034400078007080c0301e407622030041a5032030b1490010740c8141d074a805504618541088094035059465020f000f4a02e821400c000100c0e8002c1c04102d401c607018200702043c407400200150048940c0e4002031103a80c00d00d0200c0800d10060380401454007d190241c0704d45074440c1c03c14000300d000b5074440d41000441410304014400348503101d03250003805810b9180098550401280e0103080e0350b8880119030b82d00090800040320b060140c070300340121614000e03103400c290980566684164150044103101c8101c0807400c51405919041303a40100507041d01e0725a00524200b0008210014009480c5c2d400c28114092492150324a030b40c548085603680702d0180d0030600c0720941a10102c10802a0381c400f0000450764800040103440f007a40450f45072240d09000e401740c10b04000781400d070035002d20420310040c892448900c4400c14800b00c2031030005801030482c0f0014080030160014281c20084818201c2801c000100c0254450030801e8014009500c50110032943d5060950b48000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 942462293 1250 942461043 942461059
    0x6010e1308090607050607080405010c0512040b0603100e031201140303160515010e07110607210f05100618050916120c08090d08010b340c1403010902 66
    0x600554050610b2000c040c1c003160a00800d99690b0303107411000c0e9080d00106580104210410000b40103aa468805a1900b80c0c21f005071612400c807002001b0b0001081c051040f00010700607107080001c5030030300d15034050031701840c1c81ea4138045841e1303404860044803942440c400821521103080800d401c104010f002185040748944203528540c850b084200c40074007480042480e4810034103140d5010b0001a00307105040d0a1082000e00000a100d00c040710780d40104041102c07890b0000410305295000d98084c03d029a10500c0e840014a65010440d80880c580f0090020344040000c4030429200142c0b1203601000407002400c0d50719650b41304031070744242c85000040b50350b030303901489805648080c04c09050600c1e01c55044401e84a41c8802c08d000a155282040410b4604104180d6111035078202050f065050000710b240903c90707440c581240049605040840d0200c101541c000d0508010301390800c0d0b90a40b0741030821001512406c1101c01010121120f18135040c4912690300340e006021036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 942463543 1250 942462293 942462331
    0x50f03030f030417130501090e06030a0308090a0506090607030506060726040b0d0507021905071a120108100f0c050306010c060f060611060a06080706051c060b0c06010e 74
    0x34009070b100800858450589048000c1203200070300181101a108441c900d030140e0510300010310101c0b4640c4030014041d0b0450a01c102c585011414060303d83e0580f421080580e12002e419103070800e5124000d003180710b030100f00841c0c1540880d22038040c00155405002540322001000001d020f1500003528181c860562031941500f0882c0340507023403c59944040c02c0a070b44003100d404c030341c0040da040081180c07903c0030426042e82c14007078481c0741198803400c2c0a101c00c058592a82d1030460f03001d0400280f425480e40c071194603000081d41c01841121095010070740c1c465180c2a150400c400b400003415051114203502001c3c0b0b800340e207aa410055480500790360303491004481107500c5420645559a0760740e41e0b144c03c120540507000c05070066031108003445d2011804140b6000d00184a000200d14250041c4045c4001046010880e40746103421519080380101c481d100c61003a01c440c0c0b904a10b0a4000540340200e00c0241c041c2d48000025102c3c1c1e07030ba8541203d05402c0341118500c80c40c80d1030030402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 942464793 1250 942463543 942463567
    0x109061205060d020d0f1b080309220c0f0801060224100806090109021801080312070504080616030e0f101a100c0b1506071e2a050f0303 60
    0x465000c80b0042071920f08101e150042159020229016034000b440c480c1c00030184816102001e440c9840c8001c81c0c0346413842e1080c459101e019003914144121181f00582d40d4420000c07203124082f9540f6101004079042d07040019184c40e2940c0c044801140661000003040c0b0b0000ca105140c0d021518044100581c01d000e40000045000700f0a400211f6244008204604200700c15442407a0740400001c640516004100701c2d891407851071540c440113407005010403500803041d25004025001120a692107441d8152024000d81d04001703210b00c1120100312099050680e101c1c5144401e880400014820100d80c5d9107a0642c103a245007030b54861000c0401401031765002c84591034104230048074204032403001400d10101e0f480f0950010b081b031303a0700c00f080c08071000b0040e411003a008070400c001d000fa800466900c0c0101c080140c4180400e0682055000e91458002c0140342e00501d003081e070030007040c282040c103e031131902e107600407407076a4001c151070500245800d5204002030007581009003072184 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 942466043 1250 942464793 942464801
    0x206160203190f09170304030209061206040c140906031f0608060f07140a090506070f050604050a0c080106060203030c130b07200d030806040c02030408150a0b01090612 74
    0x9045110030444910718502540503540564400d64030142c410401e07600c0184100c6041c3c00c00409011803409400d44084000115002c40754103a0700840141e4034080000c42e001c5819041034058040c001c108020090200360090554040c1070010001d41c2501042c00072403801116080d400d6400300c403005212025041440d07009220030356010030280e07142c80e9880d0401b5001e5540c0c100354880681800707080f0341c010640403d0486101c07401070800e8007208004044007080d21a45015a000180400500c0000490358426607082070444d00e007800c00d4907002c1e94072110303980140c49061301020040f50b54103040c06a002220f48660013581107848000c0750303004640c8201c20780340b0458090040003460303611250141009038055252441d011301c03184504000401c1c8441c0d89407107500d88581c03d40001c0d420190050300700b034095074006442d0040320360981c80c520664120030703000e2080001443ca918144103800b4403908403000240700355070b01d406c015104500710340241004602a04001c0e044103030340b548 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 942467293 1250 942466043 942466081
    0x111516030f0f0222051906030207390f050d060b041b0801090f0506100f211d01020f070f0c1809050c030a081c02040509010906051309030206 62
    0x7000980310303450a04582264030614071403090100d03031325480a11504c0450040000c10007600c078240c0c1b0b400c01000d80586031003e4050081455400b04645042c040c028000b02c00125060580030301d03540b04650180701c0301c003a01c518401900f0200c50040758a52086203800c0841d04007034820725088038a81c0d07880000e44031480c0141d8005565814104081485205c0c0a00e840318980fa00d402075418203400300252a20810007120702410401844290b80f65281150f242e05034a207015100c031500c141c0c1c2281d84000d15411080d44481d126005004000f40358010410b41c0407045000075038003c1c407041e050a0b07000f1030710030078403142e4280302c0c180c040b074000d00102c2c80c40c601c110103044500751226440305c4000c00580607001415034603290041001030410100c48880c4040b00140454041d5540d0b01400d4805d042d240e2031070511919070f03036241c941182c050b81c001d4800206480c03129a1140300c24001010725121b00761088040d019040c00c0030f600d07841031551035501130b809041c03c5e9a800c070f040c0c030700c4142c011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 942468543 1250 942467293 942467321
    0x605040b121c0e030106290306010c02010e132a0207150509150412110f0a060f090503010e030a0e0a0b121305100e0c01050903100b04060305070611151603 68
    0x4901d2411a03135003803007503030b0150801186e0a4800a078242c0314010407401c08101101c000b0041060002d1603800c0101445425824031388184010f25440101e240c5001d00051503d44c00d003440303414404400360294988009900c1d2104903d641c194020883e984c0c3c046100342800c0800801c650915148540300030500c100740078104002d490881070074000380354001d500c180c07029804c0c0701da100d0401031184404118114100c40c40d4400e411103000080188409208800500004c0d000340b12a03603004841207001040018003c110f095500042d141e10795000d4400c13940000ca0b9180687c00c603107440c02583c2d0941d0899070310507042040120000181e56000b0f080d914081c601440381c840004c0c41007207644c01c0045c070a08003040000240001070300e000203a0140300e0500200380009000303034400140e040800c0405c0b15000c22600d8520001c2030060909800251450050700c10228505d600b01c00842e00c441010300845442041001c4140b0b407058042d00c90b004034240206010704018809d07004520031022207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 942469793 1250 942468543 942468557
    0x250b0306060702060406080403031505132c03030105100f08040f03090b041410030606021f110f03010e1005100c17030a090317131b030b0106030605040b121c 69
    0x60f4000482e181c010398000c2e00001c4070582040100765050051802c403000c1c00088039145814980003504400c800c0d052600b22940e01c202030400c46030820407499011941d10701c0c298001c00804102510f0783d100b4096035000303201814a117452075204a0724016400b00c255101d403560303141d60796062100b0000500c00e0701080b00c012404580d141e0404010801440c0ca0740741c024813941144140f041020199880600741440d200040214540119040005580715000c0303a542460405040780100380420300d0301c00c40f49004c268200e00048000040d4181c03110321a0712607846d620b4140c03401e180f0440d4014a90040701c0d15421105841c024024180c503180305261031002d5610070a0045140e810455825a4081c0c0314440001410f401481c002004880c0c010003a4481c0741000e800000d0004040c4014103818201c0040c10485103490281030240d0f50004060030b95507510100203000d841213011b0141314500c1d00310382403000e140c4107400b81458a100c0703000c0c1c43d0703a10b415200a040b0b00348420806040c0090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 942471043 1250 942469793 942469807
    0xe1008041202010e03030a060602101a04020c160e10090605060a050309010b1207051914150f0705010506181605130803072d17030424050405250b030606 67
    0x814401b540c4500c01608000508501e48200280750492403032a050a491900c141c4a200a540cbe00c00c081d0b80079015140503a850350043c04140c903108203000c1a40c1c040039044000708208090440103401030865445d4205140d03110b040703500844501c2d1290950200301000810000c4d80600b02843d03102c0d41d0400001059880e40c40401c4140318002c2e04900144c000329800d200718a0310300c180f54480d860180d94280e010b170501d24030f40c07400350341a451a4071030b45518450f5180541d0340c000700e4107103003d0840b02a45076411890414080c1c03c0699070f140c410f88440c8041e540c0c4d00c4901c204580304800c4d46071048940d00c280311090b02c0c0341d8001c600d03554040e81d070300d88089800d5a0800090140320700c01c1204069803076411030085004810400041000460f030842c80003c54003140503d0300c020030100816940341c07102d10b4000034501000600c480307514040c40c540f8418046a5200f60310a50041d003d542e0942c0c1c19105103d944040d10000800c0442a080e041c800074225101466000402804451038010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 942472293 1250 942471043 942471071
    0x5100318030c05010f2c03211005010309030509010e030127110409030c06022a0a14010e03180a090e030a020708011b030c180609060e100804120201 65
    0x960000c00e801154540002c078003040424400c042c440d0405020801001d2401071441c0d01115004d20002072040c00d406081000d550184119035055001900c6200145148800c810180b40200e810b4001004a1203000505501074010f42c4803040c0c5c513030381c4c051909003d4001511880740b0440d2950b0150f5840c80188240b00019060320301180d86010b1094580c0b0061405114058820b08424000c5007000806070010340c1200421100544c07160004d40c1340c0c858030640350f02e1180000c0700d980b0522004107518060f6000419510f819078001c102c10f00204400340c003241c1c20389080102a086035881004641180c1c00c5450603490aa00010080d40f100e9030758004240a03181e403003200e4440c5400004a9124480e01040307014002e0141100a201f962401c908204080242ca0240000d150f2646241034403a84144035000e20388161461084145417030b00f10041445905010342c402045001401143d945410615000300c2e80d5203a8030101ca0380c1c1c0c0c41ea500400b95100d110080c040d507480d20b4100228070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 942473543 1250 942472293 942472331
    0x21602040e0a050616020a030c1b1427011401021e011401060e0d0b0702010b03011103010503100513030e0d0f050c0a0b070b010b0c160305010207020a0503030a09051003 74
    0x642490042c102c503002c0d81429410903001401c8017074400003090300440042c1d004070380b8650241c0c06040c010f105060a0500e41181e048010305c200802d080c44070013103994200003561112500c02580c106441300a8049040920342c0108803110f103029007000104001d501500484070307072501c18415166000f4101140f200f9040000040300c1e0382d039444190840001040c8840382d4010941c6e03140c81e1410050510200342c004180030760140c0042200700008100da4001d400500300003801030020040010041004403440c1c000380a5a4400d025100c1c20341d0000d0f016001d0b0a004810104090310241b02a90f001c5c0d1f03800c03800280198116504240c41c2c800b06641700c80d007401650084001e4810b00c90041c0402c0200340044e003118a07107010a010110114800036211810348000c00c4040d41d80d0311011001300d141408590030540540d50200c0b02204008064000e011003910a540000c0d81c0354498003090780700d00600f014240000c000c05820001c500d01207980c2d08400445080001c2c007180c0e9508001944 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 942474793 1250 942473543 942473561
    0x16060e030909010b0d1506053a060602010b04020a20070f03060203270c040c020c040e1b060a0206040b04080d0203040f050f031306080a0609020a120b041a0402160204 73
    0x2c000103e03843d03118403a06d0159564420b400419288818146980a852030040e240000d850302c5a0b604420700c1400e075004420b070080b45409204003030001e043c080300e018102c2401118015401c18160b0303c602c0c2050300a507042d80c00d1503160310070b9003136400c0301f09081600b0642440d0090f00c110b000011310010b0040030070015501032440544e072441c00920fa07410b4a0b10740da8410700b84000481030406100400f141205010004035000b20f0741920503e0100d107040303c446200ca03440780c90111100b100c000d00050801c020481c00030784030020940d1070200300040c09040740d0307000940c010b000010001444403030041d5009215074001420503034820740d180d049070002c0790102c0c0c19881c0703c034039001401400c0000e412210321800045190408441010185852900c52007003405421404204032840c60740265000d040d2600085484803211200200340c4107409545020080c50f268090145080c103004423422608225400c04445000d102444020340c44852000d0444510411040c016508c41c007035180d0f8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 942476043 1250 942474793 942474809
    0x6030a14130b060303090a090203062b030e03070b0f0a0201021603090617090c0d021210090314030c0a12021207050d060909020310050c19120507030216060e03090901 73
    0x240c000549000c2c40000000741945200754001d00c00d140607542c9644040080e11142230380580c80b13886100202d6000503186125448051000c20351049003800d89100c0070516000390341d190381100326007013810f480d18214020030500030000c105035410010203000400e1490324601c00185016801c1e60442d20781115000c2c00c50020b007420004207c4d0560048082d100003000381101072103801e0a0020700c0d9540303031524900d802083c2140009055548100000440380c00180c291001d003081300501c00000d0a010f00128003141c05e0a0710b1030001035448054070311401c1400c56072494025162000e45154220070303540c0c915103408112070f0500b14850040140a2031581d143c071911000c01d02001c3e02a6142c6402c1442c4141c07400f450240035031340020341c0c180e44500715070001a86032110a2203648621551744080341240d0040502e01d54194005820300d40183d01c424108072984880c2c00442c2a4804c01640350040c03080d00c0c2c1081c01107189c03588490748c0360b1103050482e86440c8040001c208500310980c040f0403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 942477293 1250 942476043 942476071
    0x30a0504230303150102010c0c060b0109091e11212509090c02030a140a05040e01030b060f09360f0c040b0103110711060702130509070f06090506030a14 67
    0x11401303401c0b0080b0016032509000034040c2d20085180204034107240a00503102a8540d6002c02d030313590040c0741c0704c0060485440d0501140c8500d000c1c40c10100030003160451101c1c1340052851014510b1002c2c0c400a286404241c1d80801c01442208080d08016205032080c00085014400800680010f60250000d90300c1d901e001c645041680411140360700c1d1a00159041000b49080d050381c85102101c00704c0f004d40059403035840700b407001c4446000d580c101c0c190203107502c1d001205002c0d288905c64030984040351110b08100c040300502007083c2c001d60b03940104140027500c100d5074800160107040d041815500d440c203211a508400da1074841488480c2d049a0040e02141c4000c1c1072500800034144d0082c20184000640c4091440480c0309404000d841031011015540c92543c442080326100398005244c0900c840e610130500380101303420b80d444c5e000e42c42084400151401c07440d8022044400513200c1314685850070083c0803003948014515154030390f81701351a00341c008221042501400300e0b561a45 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 942478543 1250 942477293 942477301
    0x6010804060f1103090f0d0908070303050c0304091d0c04060b0414010e061611060a0806120f0313090506100905060702060d0c020a140c090c09040905010f0b03120708030a0504230303 80
    0x6c0d0a002448410102300061024103115024000680000f101c0d0300d460403076582d1284034140340c250b000c0d03900045061400c010740c3c2d0441c510380c0080541072506400c10b48014a105600f044202c0b1041d2152222540052208001c650301101c1012803284040c101380400e81a013800082166010000ca45203410200800380148100a042c03003a001c482603c801d8945034141c0006040000018051440f9248065165a0402c010711100c1000e0840350708980d104d01d00c14000b0400720384c0b503000d1500100e05d05400207680745000c0200f0200850681c442d0b0313581034102024440b00342c0c8412802c1c0d03003114042101b6055074449128400e82c84076036034040c00100085d0b24049516405005001c03166500001040540350b039030078101a0045070808400d5602c05036000494003800401c0700c058142e511700340c14580b20b40141d801c0508400d100314203845450407c6c81c10b00066000c1c040c00642510001e1000034190b590a500c034a4219000303038509100441d40e441850507800800c0c15140007034002000340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 942479793 1250 942478543 942478573
    0xc1b1008222f09040f020d17031b0909010320060d02091c03080621030313150e0a0b0a021c020a0305070e030c041a0a06020f0c010806010804060f110309 67
    0x100381540d8660b15444420350703070300d0005258004090400717028802010903c2c0708540d02d0081c00030105034409440c4160021105100019400403110951401201c0380c0382c4078204114412180040c0340100702c030400d6400d6071140d81c4580b0714100501149200d5800c80d10440d650b66003d08a20704620b9005a0f680c0607800034010101d1803d400300404004600140b00000e03000b5482c10760180e025070300c0c604c010340300c01240814800f41085c03c00343c500001082c07018a00c4003141411102d8014804200c41702001040d00c002c070b504000004900e6004002142c00068401e8074840e006000c0728400f40c180300c1c090b4401e4440768001c0d1007840240d580040c03070102140d0107014813031b030199640c103040b04003106001c003203600c0d0071400d240b0620a03a03407100004040c402685107140e502c1d0b40584145003a6840d03071000795072000000400c4030240300e90b04122100e0f601c0703014903034854101a03484078a0b03900c0b9075440c203028000001e46c1002e8951204280a107403000b840c0510312030a145401440c801e01c1c2c6074a2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 942481043 1250 942479793 942479843
    0x3050105061c12050315100c020108011a1e070203070803031902070f030302090a1e060306090e0a150905010c2a08091c08030c0c1b100822 61
    0x450300b180d1415081500482d40150b02c0075000420b034104640c2da640d6003001542410500700f0350702d500858810860220651080000051b90320030380301e43c0f17031990701c4014404c03010111841c000d002c1001007208040000559014104106460702840d0602c017140c0c1c0002e00301006604003e589034004000c1011180c2d0310aa40d9448202a0b242146082095210082c20b82c04800000d0145600056a50850b84400b0207000c000d00c6002e0b580c2c20199a031a06002c002c00c1d4601c5020000307424144003082c000c40a2050b0840e002c5440010225140c450744c52040e42c00c140e40400200e2035455050fa408544280241180c0341074582d982c061a05040c01c400c000043c1c85032906e404020350322004c10001d04100100c90707007000116584416030b170411142c030a03603441d401001010b4800100501c195182408050003a0881c11000d03240c0c550041d541c1251000c0005126507400141c1451340a00b890040b0f424a80103019410b20b07410b41d40020f0f8080448082828080ba84102c50881c030107454469240 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 942482293 1250 942481043 942481069
    0xf060109020406050a03050c070b0a0524100806030f0303100906080316080f16110a0611030f0304060605030604110103112a07150207030b07090509180c03070305010506 74
    0x1208500b0241401402052401810424402d05a6400120b2502011001a07846095001c2100c100c80d14240c6d140002400c01a40d2420b84c00988011038411040c030302e480080040d801600700c130002c2d911410102c0d102c41c000b8200c541c16004203d40603002110910007907204019404800800070302d004820340880f2459030100c0c2d407039007041c8000f6403010401030143c041d45030080440c0c2d46448074003110196600c11070a004801d4007180d6101010403000c1840015020401c03118003110a40d40d000c10b80314490128042c80044e00300304201010741d00f010000d0350f0001d01550300050155201c40200c0c2c984541a5003e440220540909150310360f4180110202c880305050010308003200b107000e0b00040c203655001d1101c11200d00d9003140c40c90324200000001401c0c20f111640710303011071b000060b41729a064002520b41140c50070000e20854010f180d40c1c0100d440240c10118030340c2e80e0b0b4031100000031100003c0c03c028000c3e494000741d030b80d50410042d4040c0d07008070000038140c00d04004019074505110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 942483543 1250 942482293 942482309
    0x515010f05090c0307080603120d0b190503030304150b280b0c0a021c1b14010201060506030f04030e10050d0e0a05120f040e0f0a0506030f030406110a060507020f0601 73
    0x10b01080500c001d0079059070f401400714241054907071100c078000790910040c550000351000d03012840b451f6401d9150400e42c00d21006582803084005241940c95005080d03004542d0103610030000b2030001443d00c0405041360f0720090002600f04200780000d0104c0d401c1c0d403101060b0410804190b12a600114101801050302a000e07514043e428220702c1e80b2a5604000a07200d0005018085402c804e4030001d0b00301aa4406010fa040d00342c5941801c00c0000e20703002740b243d240c0380c0b210013a101e5401440340700141d81004250700e00f1541c841381031013005d5600501c11020030025080050082c2c82752600020528050b444640d00d42d58450000780c221030346100d500242e58048800680447e1000c954461140c180281c03155540354816103041841c89543d000503203c2d0b601004204044030412060740c0550025241804981c59460406a455003183d412046c03a4104020070080140282c403107080008014064a2a18400c1d0f1600c4048910445000001d40c200b41081030030303030f8402e11131f050240002d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 942484793 1250 942483543 942483559
    0xc060b010801360c0216150903021e030109050f010e0105190c110d0302070201030e030307090504053102120304030804090b040e1902090112020609060d090515010f05 73
    0x191032001c44058518000402e485140300040180128003401040b03845203810030300044d02d01201c0290f941c4a120f82001586c040780f000815a681c0c00624041c00b400b0b40d030f64400c0040d096808000100303c000d102d22000752524140083d550301c082c065880800d004038064400c00050204890a480e400410f1042daa45810300b00603140e68207428003030646039012400102300c1d11481c015580d00c8400c002c0d0420610a4412040d4050341c150010981c8078800c0c0d8041c040d6107041e0900d0340d03a038001910303010301090440078103014508260344021350000308000c00396030082c4e01c2104804503001c0100980621069103013a007066081404964074140054401940b80a186807100310140c040c1c1c2c0602d0030b81036143c0c203500401c0c8d0b8990300050700318804002030300c510314480062007801001c013034412401141c5000000408040c994010040250003910032031809140310704000399603000325002490b03d5a1042150f000c94030400c481c04252003d02c01d444507950510b601050304601c560f000b24412250 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 942486043 1250 942484793 942484799
    0x4050d030b0418080a030209150c011b05031b1e070501270b06040b060c0a0506070503010501090902130323070b0313120908010c09050a050604150c14010c0c060b010801 74
    0x3486600020f050b07006406651a14030224040b0040d00c500812254040140304465500b080500b004040d0307150000001c2042001c0c01a450382240c55012805011610a0001036110041c440c800051384c010700900b6890701010040c0e90b801031500c03200d5046180710101d00041005001d20a150480700145490705680c411142070a0f00202041c000401c4038a10001140307841c0c45640200a41c10030083c8050303160004024020f5803696030360310035900c0e0311560010800b202d00a00c2124180c03072041e50ba45c0c40c06824401c103840694005907120803414684000000425000001a075032000c280725401d05c800002e80850f40b903c4416000203000c0350b0100180011030444e103c0507140d080d805085042245c0d0030343d41c1500c1546c81d80e4003a40f40340d420507444a07800c2e03034046a84410344030200d134101500c0b40c0b40c806110f0540030394001c040e0084481c55006082c50f02808000e00c03514411040804010040b84c09142035801d40c180b9140807410b040110820041c05d40100141d00c6400e10f403a000640c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 942487293 1250 942486043 942486071
    0x3030301050111012007061409060703090c0e0405070e010803030c030135010b011709032d04030503090f18070f0c140a0b011203120c0306090504050d030b04 69
    0x220610409042c0403115100ea0b85400b001e4000040315803111620041d40c40c9002c5401c80b090344840000c4039240d150880701010003840302521405040f0510040074030b640d9003103080d00102120132003942c1c031420070600001c0d250002c0800304c0c07103144280c018203502031030445550aa800306800003485070300300b441004513601c5000e040c5c0b1304490380c200030084003c80702d18010f000101081c1d14414040301190340c0300c0d1701c004150000c40900744203a8524010644004012040041c04e0b180903556800802900c2a030340b46150185602c4003680f078401c8052041c0a1003100d40d5405507204507050381002c6003210305072400b019210501c1c00140c0304a158a035420f111f0a101c010020048000e01c804091701c500d0307040c0309078200c00360980e200c015100f48240300503116544030010001110038200440000c03c000e5070b40018402d0280d030641b140f410091700081030070050044240d05104140e500c25000503003021600400c1d006074010b0016209420141030300030b065944844000d03004504050744444408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 942488543 1250 942487293 942487297
    0xf0303080c042106020d290f010c0b04061418100603021011101a10020a030503010e070c061109131503030e1f080f100515130315020c0705040b0303 65
    0x3c0d00c4050940e2480424a011030080c01184500f40c0070505d01100b2007002c1a0300806801120307140020819075005813020480300480000d10070f03000801c401c0c0b01c040000c0040e000580c000b4401c0b103000c2014460100b55600304034007103a81560000034a80380540840080c00301e141c000080d41e10903c000e5080d50041240c600c90280480204403408032001c034500410701a01a652501c68030500001c80140c1000061000e41740c0014840c1d0881c40c444080d050000500b8640707140c0c5038841c6800c6a20741500c002501138002e028206201300100e04500040f1248115204086004007047c0c84008110910507607100c1c020781e100000746400300c90442010719144500c100c0b540f600d00064081c440c60040f40310314101c010307961000c00380744032680c0009820407100c921460380165011080d640e03403e04194880c0c5188030b0346801030000d10400112504540c001e0011404101e4000d4805c1c0c0d680c2d9440313880d154000185204154045003030404d00105000e01001050119400c2c0000300000c40002c2d128 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 942489793 1250 942488543 942488579
    0x102060112020d030e060c0c011106100b070302010b180a14040b0a0c0c0f050c030d050301050f060711100f09052d0a0b120402013510030c0f0303080c04 67
    0x2e43c00da444410109445000f402204040c090400c07a282c446414030755a440c04501006408280301461780132143c2381c00103032284500b0080c0b4030407502c5032410032020051340c00703a002a011552286446000d40c1c40b050515802c008084100c2c059a1a0150b426411200315070403284107000101c060202080300c03114002d80000707043c500010010040c99069941d40050b01000b004800d21400942c180032020600d0003160350241c081d1400f101800b4401c590340c0c4002d0044980c400310401502034141420005403a0742c612803031064071083c000700000340030358a011020400013000c080301401c0b82540b0001d0300004003015500c186a40c1d4048802817080c0140525040381060154003030303400c0e541d4801c0550010498282d50340e41c1c501801030b1a04031420221016404565050200030b220001c030010713402c40d154004030b081c07100300c1202070510084402034010a10301e113080601002103000158500000d1001c18100018a4a03500e806055070300e00404942d8503490603c801c1250b0701c00c1e403240c0642c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 942491043 1250 942489793 942489799
    0xb0105062b0e0f0d0f11030703080613290d0b041e081209060717041203060b210601030504051f0207081902010f020406210e011e0b010206011202 64
    0x900119038086500400310b1800200e0a4403a03002500d6508070081026186501e030b6540d010404441c40707109403008007102540c9000c6506c100820300200f032207226244c0c1c2200008107a0b540c0310006014031000e41c0d0302c20000d007402494070b64a460b005c0800b100c002d403c0d00d20984a543e0f50007042e1300c0c0c48805440050028203060420141048058060b0702c0e110b658690007a44141c4035100c11011002007a03044503120014800c81c40400c0340140600045181c003c04040c40040c1030b51140e0f5458903045182c0201c006040d11104041a00348003d000340c02c03091098040386907091400d0223441205000a8501814103141609010203d200400d042407030030b8040142c0c1c4145068013031355a00a10031058050710b40007000c40c0340641c00348810148007009c04141c0c024401205000648000c0384118494080421000314004103440b0500700c0030110304e01e02a4000518a03030015007542540c6010307030714600710607031500310015560340ca1045102c260001e20007400c06605003004007460502403603020348 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 942492293 1250 942491043 942491107
    0x11b05191406071d150c06070503010303031a0a06050d0b0310021e09030c010c0812010303031e110405010f0e040e0601051305010315092f03010c02030903070303030b060d0203040f0b010506 83
    0x85c81c40168012036420a4980c42102c883e490600d10040140d0030a003c100c0c0040c0c14200c41d80d0855207094000c1c0030307800d4000c00c00d003662454254240c03520380c002d1203c8201c0f551510030090340d030351701441308203a00743c440c0d040541d48010f80001c1c401d11010009459486c0c00c010b2015400c141c0380081c11104010007800d010381042c15500301a021f50092030204410121440f00200805070b00d50000f0040c003030310101c00000aa02e01c0c0c40001600c0ca240318011441809001c100305562081d0340d0000140360604244810031000e00108058405010454642c0d0748a04010880707800c11400d0780818890030341d410000d41d411a590780b00540c030f4505807555444d49800303019091142921800038812010303c521306500a4511100d0b4046008458040c803039480d2158024400c1d0010045616010b0000d0280101504594003980181007507003485030080317424000d90010340f80501c0118000c0340260700d01e10b50900103180c00102e03584160492802220140541c101100200203881520022014041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 942493543 1250 942492293 942492319
    0x414010302032a090109090b0d0204050c071a0f06060c03070615090e0d110a0302060609040f120302040504111213240e010e0606011b05191406071d 65
    0x10840e43c00501d6003c10071410303e4070345500741c00100070301c0c00281c884c041041d95946214041754220310711765402ca03800701c99041c018a80703503100301da03c680910183d600700f1a445c1c481075140c46000d000740c401c00e1078440501c5403c012400c411544020100c641c00d2900500880d116204d0180328401040d0303035255123190110a01700094800682400c0d0803c10583c043c010f28036030365861081e01103010421400c00040c906001258800645415030010a155100c00c1c1c28403000c010003d005a482041c109900000034220300c0b03138011072510365540580c640303042070200001c46030038101c0e5070a024010000c128a83d05209111580300f03407041000c400010702c0d801c04038843c3c1c00003090713005107601043d52100b840116602016450f0f0085000304600103180a419503590000d48009010840d0081c00c0c044d0f032100d130204907049503c62016582d0286a40082c00490501d207502260b18520419204884090410201c0e074020728503d4584030050180460b00d804403c01c00809002c0c0c90700381c00344c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 942494793 1250 942493543 942493561
    0xf0f03030a1d0418020103060f050607081e040303020607080105030a1101080a1d010614100203040b03090a0c03030917070506041e0b03010321020d02123a0e03041401030203 76
    0x5082c1d40342c40904284105502448500840e0304203044c03c90100c1e1800c000424030792110104602503c101a00840c90418151209062070f0070944101d440c0100b200ca13603104901680002c0d000451182e00200440d0524140c09820720005030844c5002e41d10001d505030218501e007014400c04071081c00c05d40040e440c1c50008074003400054000e400d07124038036900d103131800c10150301c010112a1f000c07507052000c5866400700303c4441a001c4680f00140e005000900040074440c0080d5048801c600866001c050640ea0b144420087d5034405c0d8045040c02ca01003220f5007500c20740e000b00007118005040c2e1107040c40001400c0d8091805210508510b00300301c0c91810f0055507041c8081c2c00c0c0000052385940e52841c15031514412200d41c86000000007000350821400020039403030228684c2c01514018030300c3e200d9544540c10910f075201c0800200200d110008202e001c245084c0e03583c0341c91102100d40146621000d682d02c070320812201e035004020800882181e03d00717400001030246009030b42e80c2c03a08010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 942496043 1250 942494793 942494837
    0x90907030507052206030b06071104020f040f060302030f090303132402191e0f1409060307021e0a020f090403030e030d060f061d0d0309230f0f03030a 66
    0x100c1910340d044000f4a000703500c2e05040c3d002112206c0d0307800d00050308840c1c14007010740074140c8000e240d124981d1090b1400d16150b0041d24803002c45552850400313640703040420a80c4559440304001c66070000c14015400480300e41c460740300e441400194614103002c03001a801088400c2c000d02601e00d03520750706072001c1d13040b04080c2152145074419920b4010b0440040100d401c0d84c0b120fa0040340458000c910408111102c44100110b40d0300c0e45640501008416119220f40843e1801144000c00c0f040315955207410155000d6407a580c028074800c5682e00310b800d41d81c08148110000ca45c014540e54006a90340d01070315010f0b2500392103c0c0f0a0380c985280a81c00340400e100521110300000c00c20003c0740120713620040888110300900659103580e4441617031550b100001048551a05100c5408a4123100c42c485060501c249003140403160385482880203503092000840c40b01f1904c1c107034a00075191103a088510b40724200e920480c400030b07240000f6600d2280070a400c040c801d0703074901201d81611500d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 942497293 1250 942496043 942496057
    0x504060e010c1e0201050906010b0d0b06040b090103050108072106140c030f010b0a0c0f03020703050303070306090b0307152d17071103090d02040f02041706070509090703050705 78
    0x240034107000c840c005004126034240c03a001072440140f100c911035205006843c0174582000141c03003130340d00304a01f80d21591b00c1001c01030601c80e180e100500c8140ca60800400003082014401e039195280c18000509590041e4040941c0d5440a0b00500c0148000c0c1d0003c0c610b409911081c91000390319280c14405800b140c6e51140342c0d5100a010403200805a1b00118072510035240c02c405941e0300d41c4070340744081c045e0801030b03c0019a00f14050001504c0e2101d5500154083e004172a009982c981d43d05140d64000c036140000251140343c00c1001c20068003440a05080840c094070400d824a08003000820601a2a0040292400a0345078440c0301e52126910000100d1000c15188524030001e4020480a411000b0350030400c40000c0546100d9480145401c0194001d10b140c902d0302020860030056003c4203a078040e5176002c1c0c5c1514651284000c00060100002c0200044509400c00c0d04107103004140000303001c0304204078089039681c0f1507143d512001e80c5c00d00182584401d030080322507001c2d034a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 942498543 1250 942497293 942497321
    0x607020d0b0f060102060a1401050105071b260c100e060c01050405150703090302060601030e1207050f060112080403170919050a0b0f03041101030e030f03060a0b0702030a0204050406 80
    0xa010705112100b0000788649003c0c0c00303d4000e61101084201107807051039940006800200c01804150b204800901d8028000e0030607000c0180445510103c5212560005a4030355000394108075910320702c1107049900d44840f0103460441922000304102c40501d0111008000c20465120f16554520080d41c44040034031000700242c1c80d042c41c10980e506506121507040490b00000529114400d020340180181d1650242c10b180d11118019070182841804600540c0642640d0031703021034a43e0f002c1c0075468064401024035007081d801031400c02c00c06800c101c603514013440c101d801250078941110100d03603005860384190044030801c00c090340213440d0141c0c2e1008003100c0503044080e00442130816100101c6202101c1e03035480c0300c81902031081280030000e0031411700c00030f4041500250309148c0050181808688221203001301800c5500c104070291802d500442440401d0070b0001c040300241070b01031324144c078108040c1c000940e5103c000740d00912540d11400020b08116058002c0310045090b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 942499793 1250 942498543 942498563
    0x9060f06151918181103071b0326040b010e07142104030e040e01020c0c131103070804030f090609090c02010b0a0f030308060312160f0c0605030a0b040c020c0607020d 73
    0x2000608032124001604c4901d050800301100a4400c0c010f040700c0c00b60700305803600041209829a091032600c0c00d00002d5040c07003a040b030014068200c081448121824035601003006203010700c0c20104448041e0098036820480d5801c00003178903000b201d061000c92216000c25107880802c121302000344408030310b5004140740a400d00003007542100d28641c0b038040484c1d00780140711544280500700d000c1c0b49082880d96009003c64081400d05041200c5440c0c0d02202c0451f42158030700c2a250300707030302c1690341d48000350602c2c0c02c10050650003006000b4250092820014052900400030b01c0202d5038003501100c140d035004071041d218000d40c4808100c420151282141c01d50b01c005070707040702030140300903004240c00301d001444a10b00468400510340d0810380803424000d62008001c20040c03071240482c0c40d030459901c0303500401c042507088070082005690349540d07031500250442c02d0350559260b4038015410050b01603072003074003c1003441d07241038107680c25503d0710814000504900b170140000383c403107581 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 942501043 1250 942499793 942499799
    0x50c031018091a060310050f0a09060608010501062109150221070221040e04060b0627041b0801031e02150a090b25020402070b09060f06151918 63
    0x30081c510b4400e0702c0c2101541e1b03442145549840580340101c0b150030300341800400007044c1071501d910400c401e5000e980009219500c601c1040c1c21240d00f80c12000c0801d80c050074100707150012106029100459100c00d00c000c044a6503201024803546004541a6401003110410804d503c5242c00c075000c4600b43c01c955030b0510100280d00d0f0b0746004400c030005220030184501e104038030012101196840305c01a1803555641e00c0d203000500240c0722440d8003480070030890301e0010b03107601800940c1e015240720000e21074050040208407061403a20318030300602e11503140f140d0340d000740c00141102e801035001d107004120f0a20121600300312000081d48610705c142d890900d03180b500c0207807540c1c042a4031810401c42c0c840c0c68a40050280c0d0b110490b04a0300c9852120401da55000342c201324a10160001d4202a2990340b841256082150383e820603900081c1004034942c030b258140380e003080c01070b141c8144403a840340c04810340380f060300070107650040000401d20003140b18210700f080c400ca0290442100341e071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 942502293 1250 942501043 942501083
    0xf0a050d180c030203060a020412021c0209010e1914070309021f05070b010b07020303041404091a090d08090717210d1a0f09040212071404050c03101809 67
    0xc1c83c041079000c0c0c40303810000b8810417070074400c54066a0100142c800e220903190708200104060103110284510241100c200689a505901f4064035400303800b28002c1c900041c401c0020400c0c0d000e00c9410a007008c943c080c40c0c2200310100c44d000641361230049505540d600202e0004102c1d070400040a50101018502044d4440d014161303840c41044401000c1c2d0740e43c1042d40d07041c0030b1881c01a51640081104201c0e01c001c07101039100240000e440410102d0a03034030303108015040c5004e8000e461410b401000021001800b91100704084c6040c41030305420319505a96907019035009000b2403081046240c80011410864800070025982c0044034540d08d040140195811040303070381f402c183c02c200301a0001d204144603401e2010010b80f0000000d01ca850400500b0340002d0801c0e42c0100075004107030b151043c24043c407400341100d10b01040890000c0d80c2800121800202b40110000c028400e00c0b5400080042d5041100c03c1085032188400310b84071035400804110500510307076810b030107c10841d09 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 942503543 1250 942502293 942502313
    0x50912010617162907110910050f010932060c012a050a0f1e080601020c0105090d030807120e0c1f200a15021209030f0a050d18 56
    0x101401c1d035000c0003a581d441c6200c11070001c07801050710889011440620641303012014001c1341e4080c0c58030501d881d20980104406400c19100c0303407083c240b0240b00f8000c42c100b5071203422a0100030f00c0d0290402d45032184940c501480d030701d404800303100400306000307040ea80d03e4013015245000600442d528441c0c0d08940c0d0080100051044d03d10390340c0c0c1d52140501640b01200741081c041500d0b020f01c0c203484000d0844035402d4030040310040c0b058100115101c220020015480550b06454201407401e00c90300291500760b03003555507030401a0400c02500e1039107071039644018540d41401e21203902d031104103003501c1c842d00c021291a220703172404189151040001a11804d0800c064500d02d4400121030310542507107400c11009804100039400d49801c45200b010780e049950060015580c000e640b9541d0350b0410080e400040407801d80204000007812128940c2e81d8100c03001600a510307105e8984500c542c00e0044407009414804080b54034034400720940c01402c800351441c008036984400c14034000c1141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 942504793 1250 942503543 942503563
    0x10e03061005030d262d040c050402090604090b0621010311010305060f0108100b070c0f0611060f0a060e040503070611091c021801230f01050912010617 67
    0x82c411100107000c1d00d401501d28185240784045d800784291010740e00d003420004082d0000b40e0031a102ca13005039003217108007202c0141201c5401b85907524206400c02c1062001d05411980c46941b0401c42c00e9011b50720360301210111440803170003041790080f110000d103031809030311902c215151044000040d20066101c1c1507042c1c0e0710480d11003000e0780000d0011070842e50204c07082030300103034403000ca10030640c01740c0c1651350301240148070303002d00d69103600e00f0740d403d500481012a034058444205120000c40c500070000504000e14000d05182e030f964a044e662100f018001d0840b00c070031100440d03807101d00d50f00700c01d000d80b469901442d000d003014a011690307513101d19030584400c0d107842e214010302107600048600c0800010119100307520074440b007543e101c1c544141242c1c4000d0328100e40d0520b05c0981d18540c02032543e5a800303031210740e200c280e0000a9154003403041c4242c29258501d005030fa0002c0c02d845040c6826074551608121a102c800d00401154100c40d04101c1140e01595154600140104803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 942506043 1250 942504793 942504799
    0x270f0a0e0a0f022a0102040e0408091f09031109040507060f0c1a01030302011a030304181805060106120204030302030d110c12030106200606090709150503010504050c09030606040b010e03061005 85
    0x4c001c9040040310700700d025a0041c0f415139000e4402240c00324032000042d10f2094401405240d2803e2a2190016030548012642020074688070f010400e0105800a0b0520380005a41c03201e12444c01d43d40c0c1c1e0303031214000c0c0903c03024050310342c1c0c580154030302c81d18850072a40c0d070085148144400340c040c503540e2190309100c00c400640c02c0400d108a4865584260324040c0302c0940158103041c28072031050710b940980c0c00345d8107013195030340c803580a401c0541035488001401040601015414110010440310300c0c0240c411401c0d004100400019034000b04507040b03952140e000080c6807100da803036041d040c440d500c1860f00d5446a51050001407440500130750480d040350711521680c40c1203507281001c07500014644021034200303000048040c140058660fa01045910703114060581b2004a44c2064811800480020300d010005005504062296541001004103890300349804180001c3c1d482d2002040280180c1e21894906201e074004c03d005018600f009058590515040e061250b002000e0301c501c40c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 942507293 1250 942506043 942506107
    0x60702070f0503030a0c0308060609270108061005040c090b0a0207090e01141306110a0206040201020c010c050c0d03020709020406031e11040b070206040b270f0a0e0a0f02 75
    0x90354500001102c244440e9034640718100d00b1287c13020f90301610010a03490304a01c080000101c0c0e40d848008014030072000c03103464a1b480c2080c000c801d00040c0142c01c1540d803680b11070705000714000310039000800c48600f1240459075502c4440e00b11220580c50b404184521008940110b540d40c012802209685803e901000141d501b000c00c1403d0b5003810014813035200e5141c02007250300c961a1500600540604400304916122800c003d0b00c2c0c4d07000700c02c0100180c100310244811036a0600c400c1d01d65120900c0e044140c1c2c0380ca500c84a48074000041072a1007013102e08108801c0500078010303400107003543d200c1151120340d01c9a0160141a1815202c3d000d000e02e200344421a015034070840d0300c13210709200ba0609260400d4488590b6503c0300e04280c4e880003040c080000c00020f1700d40288101080d440400540c41d152000e01280320000a80c42d92003580d5181200e146d5440d448490780440d1441e84002010781c5504205000405a01c100c1c2584039000113800c042c4144140c40c0780320741d4150200c40c19 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 942508543 1250 942507293 942507299
    0xc0f010b0f0d080f161212050c120a0902030706030e0709150b031b030a0f0e0a0b1902040e041101080109060b07060c020102090904061e020702092205060702070f 71
    0xc0540c000c14040c880c0e210054403684000b10f0010005010605050b07050300d032a01c0030609880c080003901c4a402c6600200582281880d940d00c100c1205080c420341b40c0501c400e061200001c2200e004607605a140b258030100083c02c080304541000071a683c0180c1a200c4464883d40c4c01400361400110740d40b694441c5101c001034052541c441c0c010100b8440603502ea00e242442034107480b0340e20150052134112000b10120f000550118019401859000b400065004200c03000e001a03070360b40c8a0ba400150840c05890b000704e00c140c2c1440740d000710980c903044440341501c400728000b030055401520b46442014204030401c0300000100000780c500340c8a03640799aa8604102e010754a842c0220b4405503402d0004900054103908110003c1c2c0c2030b4000036041071a0000820581a8110390a85866840e40e014620144568074203000500060000390b151a100390003140900401400e01204011000b10b0043c014444161001c1c50640c490155001c0741040b03080250760740c0ba180070b010405a0200000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 942509793 1250 942508543 942508549
    0x905061803071208090f10051b0a08010302042007080904140709030209060604031b05040f0902210703081b0105071d040c050412030c0b01050a1208030411060c0f010b 73
    0x140d240690300c0036a506070314490203011140c008005d01076070400c5c072030301505000c010350920012a080041c10400101403801121000e01825003c80c44010320400300540050103900014481c1075a406440108040c1c0c0c0031801c2d000b2807043d0b01145034a0720780105054003045688002000e10b15801c850510a00340906140260014251420f1003c105010b01c00c0005062034100b05501060041066080030380e40e032268902403201c0013501c00ca6000844041c0220f103030a205030800e002c9100b07010041c421660340841c0d0f0400b007002c80d000c4090a221451055460b041081c0c1000d90382c402d02c25601c450388070400143c8074006000750640c950800f4001070a89101d02d01100466101c181c07500444000300301400014403048030030f00e0030070104000100d01c2c80308070004805c04900c20381e9108030780b00f5603040050005030103801403440303005881010402c502003900c1541d080c0350480c0080380c0c0c076201d03407400861381a5007200c120b81084c4041040c00c119440490041c601101750741c020301c0884224030070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 942511043 1250 942509793 942509797
    0x3050309090f0f191b0216080304140112111c0501050f0f090402010c0b090a140115031509050a06090605161e091806060f03090302031b100905061803 66
    0x152a15040c0d01e600010210a0700b40075104020820b6800040c4240341e03645d840000c590ba0004000c0940d01012a80900c8a0280d01d100d0003405c4120113035041c20b0030300b0b0b00701000e008a0313050a070400442c8107a80d00d06a40543c000600039a44400d03482e614070034002c1d4400c00b000c1540300c40e26864500130000030642048116520041002060000e4600c00300c0308000f030aa001800a03410008251844030000704280c0605005a901200514042c10350740380c06008103002861308107003070341080c4251007091130304800d10003526407000441c4540301541100300010004418090154800c2c0013082003070140940c000c0d100e00307000f548107004590302d500154910349818500840090b4035081040300c00d066801d80b040a031880303031514401c400e590b01450454845055034007025159203140030050990014848014440c45081c03d201140e40368038042e441703006e0381e848000c5284600344003440e10700061040d04040c1d030011400b00500700b21030600c555112011640e2640808600803551100e0304c1c0041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 942512293 1250 942511043 942511051
    0x1020f03130e090d02120d0905010c08090d030605030616111209100f021209040b0a081014040b0f270703020a06020a020f04110c0a110307150f030506150403050309090f 74
    0x1460300391004039500e05280e2003100d030192062350f1007500100148013801a410302d5542682c804440303091681c4002d00b40200750328200c080c1464540c1c1013049880110300d4a41c03001e5004410f03080d180d2044020340325600030700310184050080a0503540704950320409400300d080151403000743c40c0c903e0803058420711410780e200c40140e4030007031031030303c80c400c80700024150303c10080d202249080c0303004040381440f100c603000b000f442d030880c000f01e58014105e0f1040d007411310040400300f1058245a1120908990060091091010f0060001c0c11210000e400120304a550b0346a042d0000142e00301c0302d40721441d0f070004034490110540001586072000400401180d0010005803600107400c1c20040100340082200c01006014014904407030750621400d40814000d032030000c8604070510415007400c0413a0014a88030b0340740548541c049601c07416a140c80811070030000780548645000034007102119525140a490020f404003c05c072020014011901080e950803200e911034074100000b64108803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 942513543 1250 942512293 942512297
    0x150503190b120312061905090f0703020712080a150b16050c040606050d0501060813020603040201170a09060b0f15030417040b1b0c091501020f03130e090d 68
    0x2014003068409a0340300d4891200000c00c6501d01c0c02010b042541503400200b00303030907883c90070340400c002402d0000c81c51486048024526810f1401c1c480001e00100c00680000d04102c00d040000364100c3c06030741240d51442c0c100300c0340b03941c084d81c5110060020390129045546242401030440c1080a4090140c0a4031400a001c9003031a861800406451521800139200c5101c1d04040c0d40590f21144144030103406280d883c1d07603803800c040c0c03003090035118183d100313408200c511020010001c04407c843d000180d41222296900d49503400101c458200145412205841c0c0130240b0914294940c4150007052042005005031412207007000101c2852a100f141c0015100c0e600000b61f107a648029a031180c468196005125040038040c506a00f06801000d0044000604a0302c1000d101c088080300d003604100070f1511640102c0414100034016107249411030444240041d103a00034012080e028a11100316a1a10201054520a02d01500c900300e020814100490202d003008100303d007020580d6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 942514793 1250 942513543 942513571
    0x30804090b040e120a03140a1506080408070303020c0114012301140712111b0a0e06131d01020316080c0a081b1c050f060f0901030f03020a0b070306150503 68
    0x41900d131085034025244801099642d1100d800e02c20701505110b409042c01c150300103041003908022240c0c0342001d4010200b07206031841003100040591049803903850345460702603110200b000b1240c0c00b40800e4501846603c52a80012680030740002e190340c014100f5039609c3c2e8000c0d2005d401525030340103854028005002c03c100850104401161800c4401c540d46043c894610300c03c0111410b04580b11f880d02148491006505500d00e000300f4018043d00513200f206400341099000190b055100c3c441d0f010505444404510004148403d001c8991400310025980ca1a02c042da1461118882c00c00c00007007070040021841340710000341901d1000781140c4414020b9150202808140b015a4015548044040143d1943d441e14050142d6540410f03903004540e03402e01c40040031090f48000d00c8075019482510483c03080e030380c842074410704403900f0001c001e1251055007412802c000301001c011b8006130f108807d210bd03540d45580950225044158112540701d669042168039110039031b00c2e59259041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 942516043 1250 942514793 942514813
    0x6140a0608061506041a07030f2f030c071d07080402060a05130528060201110a1b02060f1213020a0320041104050a0803041a0a0c020a030804090b040e 66
    0x40401c2c440c800400401c0d050030030396598a03d44906081c0c030320641c40421b020450008058200c0003545281070f050800c02e6400c60700d8200c4584290030700b55041c6c8000f226880000940206200700e800320000c45050300c95040d207902d030396035003444500c000c5180074080000090b0b216100f110010f01843d401410585170402a46048030607800890140300b41004220000440d07039604034916070703101c401d00411f032100c869a01083c60301d03c441d584810156414004003c1c10302d061031003103400240d61418403032120080c09080b1041202050402500003500080b02607061003608090a800c140381d1561a045030303120700b103e0512140281c0000e4020392180010310000e401201e00014190381c1c01c08040b101c6c40e9410024040c0c80c1101903829200900103400d000750300f00201e0400181110724011071600d49801049104000940405034403c0004211441d40c07074072a42a95400c01d40080203110035584034182260b4641c424841d00b0001450030254144032700301406010441000031000c1c142000c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 942517293 1250 942516043 942516061
    0x3040c0e0c0d060e06130e0c04150b210c04031509030e030105100618030b070f020a080703020d201002250605041e080a1b0204050406140a060806 64
    0x20050180c5450120901034240c241d0458407400f0024400000400943c0c108070b0140002c400b0041640c0340f4090801607150641d0b0800604440c3c0c3e5481035800141005148030300100f0a480d5030030885c40c41200150003010202c550344016002e200b0212100745030b031240d4998080314403440c800208115160081301d40c2284895000c000c03a03d009060680384a4118800a402c45004403802980d446514200f40301e02603114140040301215007004c03500351819a2203900d1140c10050200781000815850070300140d10038001c0040031688141d9907601c0b010301d0315000c0c0d16101002036501c0007806040e0000702d04851103282860401070b0b01e0141055150000f00f210295008421001d070254035603909010349400303100f2404e0382c00e0003580001081c0c242843c0880190862111070210582555100800314200038111003090741182041550b04003a49581074540d0480200694414680020030040c003203d41c200b00122443c01c100d00b6840d41d103140c0d20400300c03001801050010303400701e000a01064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 942518543 1250 942517293 942517319
    0x140613023f010e0a15050d0311190b04080d060b03190c1b032304080105041e031b330b01020f0c04050402040e1c030b0306070f0c0204060816050a0b03040c 68
    0x10039980c5c1040c0207940301c8012905038100c420044002480419521200e54024489003070840f5a42c5051042c00c5801d4651024400c40031380054680b0030001016005100c203980700b0740003072048000f4183c991130042c082015141421030310258850034002d400121500c03401e4404443c00c3d5004030081089401d8504880c401e002d41c0850703d402842c48a10100e0781d0001001d04000c1c81002c00100303840c41e00740751054862201020301d03218413114146850019410510301c400030f64140300a4000a0301070b042403407240784d510010b50242d5103003408400c900e0f01c2c034515134009911005020700071201c50f00012a41da4500d00d5441120b83c00c041c802700d6062074990001500903000402c082071004141194504000c503100c90341100250000d081000250107000c2c0240c5800201c2c0904106c2c60640005003151801540c00c50400500c400c2002c215580e60380450040d0402204580c44558128030780da00d1400203001d004d06c1b038102810300080f035003014000c8912649e4443e010440d92403801900c84162 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 942519793 1250 942518543 942518561
    0x306020c100e0d0809120328051303020c0a0303140a020106090c090303020c0a08030301060e0301060b04080f061302222318060c040b0a090b030405060a0f140613023f010e0a 76
    0x10001c0c881140312342d41c150080901540d4500c5c020303c0800304514010349400c4400319040c6c0117a0040100300301180e0800d222000d44000f0351034880e0b0364024940301324010141e40c1c20100c006071070300301c040466503400040113083e030f0300c69002c5690307040c9100200845269a485050020b41c82040103029042c400c80040c905000003500120301c80340c481800c1c0d00325411a8000f501da65101601c551400181002041e404c807107150a0b01002c0100c81d00407801160310b00308061414038a0407641d1034004d0851b40704144100e150344580c1c03041242c481c1a0709000382c064800f800784166556210030020710100d00e603801021240c0d01c192420385480d608818070307042502c5a00c18800c4d0010005800c1d480c14000350301c61481000541128a000d002c00011030f40d0042c0450750a615003120805500480c0d407401d904a1001c0314101002040c0c0442a000391091000c1c4410300010410b2080c0f0307039144421640528070500090110424a24102001c885000d00c030b603031214543c10004caa00c0001c0c41e0310407100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 942521043 1250 942519793 942519841
    0x30325030e150f0f090a060510030209150f060f0706050705090d110108010b120a09060b040c054b1317070902040f0306020c100e0d08091203 62
    0x4a51019076401e04007150502d00030150340c98a01041103880c103108110b41e2040342842d0140d03980c1059400039544408080000380915a9000840c5c4c104070300c1840c100c01140c1c01041c504081c80c00c94130512849d1888d20b030050062008102c0590780e03150550035a07680500d410074090a000c81d0f515144050700c0d016100506002041010018684404c2c0c8820140b44c083ca82450240ca40034000400190050303200e8119000f0500110310106074040c071091300006001d20200d81c440c9281440c6000b49038440b0020350003807070a1038240c001e41c0c020b4007910032a084420190310100e100d0200c030010f0b5141c0101c0312040c01c0100301000d00c241440007d8007141c860300c180703503082c60409003c1c1c40c840c0c0d2072908060310310300d0044c28400f140c400030401c00700900b01182003581843e01d1f0110198410903030380001003026401180b000d02d980341c100940501e041140005204c03940140c00e0040c1c4a1718101e000b040041c550760001484040c4c005945046400030240c058a0740da00e055900b800c1c01d261075901d0701d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 942522293 1250 942521043 942521051
    0x909071d041502070c0f0608070504180f06080a0302120301031a0912042d030b06060d110301060c150b01020309041a1e040f1b030c111204031403032503 67
    0x886200c481c401380c08000e1050049004090038000c424419075929440282006112402c01c603859602c44161411501280304c0c0c521000d41c500007500c054105070010035003c51805400044401001641d80304e03550098094440340e041c240740b418000e2109000244c00d0002e184d074040c10850100300821b41c8519007034150740024240041c1c0b150150711a9100d12001c0d40c3d03a40d000581c000e01c00210b40d01441c8009240c80c01980340d50303a440450800140743ca8814034010a00c03000d0b0318042e80003504038140c019142c0c3d81e00d41c2c5030000500011032962055803002c60445c0745131001180380c8511602080160010b41c14040a0400c20018002907284010103000301c5060480781e0301d600b0400958103028245007556a020b030414442210f80040710b04122505081ca82e03000d04112404401c400e850502d00428980c1e000390041c2c1303002c007001d400310100d4803400c00c2e42480c50740e1480240098034481c0d291541d6620202386c03829940e001c06d40d500a92015030704048518036a0a070710720b16181c40e40e414081 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 942523543 1250 942522293 942522323
    0xe090703060615080c130501030b130603080c19080d0b01030f0c0e010f18030b0717010e010f05010819050a0b0307092a0c03080702120a0e0909071d04 66
    0x10042e00e03402d52060000000f401c411030040c1e904007501c01e07808021000500e052584843c14659042118410f050615a9541c0d40c21110384030000c0c1c2c0460008150014841c00b6680d140c02810703a800178044c4d03100c5000d0403203003041d401c0c082d50000101c90f4010620343d0070020300311403482c01030000c0c81a1310306066503035015450662142c050103400584c03540b2804007100000c40050602e14060403100708000010301d00803902d0103060400803d4039048040d6160580d600c4500b903035000034920360001c6442e8004000a81c030001580c205050780c28101110011a50354001503030b03513100a1311002c1d0440156503a1880c9410240d01203980a8400c6a021800000090200c1d00340315603a0005040d00b5207402c03014040039140400c0c51428a481c1800c5580c1a401500040c014109440c0007400c11841c1780228a030680700304101001c111050b01c505e82d50311a01c800240100d00c0300c0e000c81e03000c0d03050040007135145140810070100300c44d017144602c0c458800d240301170b41c1c031024001d1048a040100c1a024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 942524793 1250 942523543 942523553
    0xa0c17010603020a0605070203070e131419140709020f1803010609151a09180a020c0d0804032c01050702060d091a01080c100302091c03080703060503070f0e090703 72
    0x310028405c607180d99580c0c00d83c81c0141414003000380c0207082000b106d034062100c0c4905100c101903c158004400350818a034035058142405440d000300480d075144012040140190861504410000759048490745651140308a090f070040d00110020844284041584070804940c0401d6820004000003030445c3c45034a0302c000c403105000e80d4071000541b11828000149070340c0b1519a0f50b041c02251a0800c60046c1c0095850f01c0701504809004c00f08902240c4e003a070030703501620a501c0100c401d4600c1804103840082c01994103c0d01038000904081c0c90110100c0031000719400b809132640d500403001c40c084010754060313014082c1240c010100f0415048400190b1144801c080d00ca072803901120b20702c000c4c001003c081e049e0403612841d00070031114411640c071141c521006403205d0030003580723f04900002440e0780d52000c2c00ca0b42c0107080949034108040d44103040034454103040e241000001d03114800d055a4480c24080c82191540200041c050000d15000031a807150807113007180c0c3c03020f40f00e650f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 942526043 1250 942524793 942524809
    0x7090c0f0e03100e060a0b030c06040b0f040b190e0f090601081918050c0a06020a1b17010c0306270e011b1706040b0f0909120a020c03010c020a0c1701060302 69
    0x500c0d50000c03c107000c14203400f409060003c0e10308030b00800d15051010001003171031250b8848c0b0333111440000384204d0802c0b102000d4038024188491845d44803600c6500503446240d40803061800901074185a4605140900c4640103100000d44081c1d910380d5400c00650343c00c44c016000c0034004226850360280c03000340d030140061108485c903c40d401c0c03a0261621a1400400f03400c4c2d1031190804450501840d6270014210989640020f90030040001c0d00c3e19081d0942e030180c00401148111282c030308807108054010128020190350200705203561084108581c0e072400d41c045c8001030040c01c0601320306040b80c0007800007584800000886000c0d950500c1c0320000c083c480c0c040030035455a02c030800c1c402207041e40ca90250050790140301c043e100a00280c04400028199803141480401084030b001c42003002c0721124488140e9283d035403003d003002940c0c485203c070740309200e50b0800c0c02700c58002d0f1000c2845c403001503110144102c154201100e0078440c041d0f0f04540b050b29946c0760030002c0580d0358120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 942527293 1250 942526043 942526061
    0x141206130f090c05030c0603010819081204062f07020603040c05100908120f03010303030e0a0506010f050a051c0803041109040c081507350c090307090c0f0e0310 71
    0x5000c10510304d0442410b0402903ea50114856038081c00100006040860b5103621842c06440d00610903000780351040c0107004100161141c9040b040400040064580c009440c2110722000b9440c020411000c00f43d03a10b071842450b00680c5020321450300103003024406141c1091080c4040000262101c02040c40f06903400441c1000076020341003040b11200502503445038500440c809450045010000c20103444180b100604150b80d50a17400784144c00cd014541002d540581600c040d035a407500c0088030501a4040e5074420000c2c1500065079103030200d0640710301c071621140401c1c04501900d54001c55000200207a81040410845030410baa44e14001c038400c0307200d840803950310340c02c00d40300c1392610140d50807150404002d03009005100c0d8109204290204603620410300039000208042080781007141d003c50780c2840700043c00914690311003e40719109050342100e1240390b030303800e0000561310b45400f4400403c400040c84403c40d40300d601d1a04003510041e003240d40140813240d03c0c0003140d40c019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 942528543 1250 942527293 942527303
    0x6271a0d1109011b020907050705150711011d0601090b15030103050a1401230a0204080303040f1403070305041802040e090a0c0b07020915040b0d080901141206130f09 73
    0x142d0103482c0d6070041d04109443d403040710f0314912240580d0100b955180e02078503c80500c403020032076400704441080302c100d240003203411010b1360741040c44c4043c18030000904524101e50030506c03d058241140800c01c440b041c0b83d01c0003000d660740b0b00141c5030011700100f4035041e0400740140082403c10b02180c002c0d40210b2103200140180a060308040700510200c84071000c059041c007640d103144170015854862a40014408242552a070b010818024411a448500c050002008001c01e01000f0078400c400c0a000d03e8401030340b0f80c615088a030b103e100702d12009020030420702c400c0c400e604100110b4000000078010051038151206202c0141160440b03101115520615554007044822204080206200380c400c5043c0001907000a00041000f00380c012000c4403142c8030060340d42d0340d03000400b005078040d0680b080004207046c00c505540c4141c404034007044801d504055002101c000f01c86141c0d4903409145041e841d0042005007102d050000101c12036200c800500e010f803160300c21a00c0c044d20030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 942529793 1250 942528543 942528547
    0x111905011119180b091e04090b040c060305010e0a0b0a120602071101110d18030b090a0506070923041d15060d02091324020406271a0d11 60
    0x9008024500755910034003c00d4410b812000b00070b515120001c0c0c0300031107801c5400d62009008030541e1150031003421811980641803002e09001e010701503541c24001c030b000e40c41d4030000d039072528003c6d0182d0380280703d00105060840c001030f0b181001603102c0241d4607001030050440590300ca00404008417491000c2d24a55800076040c005c00010740c030f4140c1400000e0074001c602d083e4801080d40ca49200c3c0300c040303042c80382038031400c040154052100405143d02c04003140311030500324a01642c03540300d190704444520a69002c1030b00300d4004e04940080f0b40801d030b1104001c818400030308070344120030f21035a900281c95100c1c0c58580030321401509600141c80c001040c12100c0032142110881380540542d0040240d4040980981c4135101030952103146000b11070420380d00c86c80c10500942c1020503c0c0104a801c608602090515030002d10481e0200d55400704262034100c070440080440700d243c04c075440d8140d4820044d1f00700c0b00e901c45403900c292404c490700741580314840d942601c42c0003010000c05200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 942531043 1250 942529793 942529837
    0x20d0c0e0a03020901090e03131d071103041a1207050c0c0d0206031b070605041104060503030a1d0103180b040209070c0515060d080d0603050d1119050111 68
    0x1200011540c001000c49040c4016480c54011500c600010300a41c4040c0d0380b68407030590112800c204031540701e0116110b4051407075480a4100781040c1580c001040c0c0d42400d808038078801c0c0b0420040c03041d2100f54020314501480c01c483d400890b5142c144d851002c1d1814480720b0340100380c80e203800c0d10401e16a1100340c1ea80301e01405003400c1540c26200203118026841c441400760300c0302000e030f0f035120742202c220050300c0c03090100b070310240d004083d4018480d5040504010400808601c0816800c100f03a0f0300b40501503c5408050710780c054030251000050560451000350b90807104109902103060600165104010446c09440300400106942e0b04200d031003440308601300081c00541c01012803074088601140c6544503038856080f11a01d0652100d580080354195440d0401c0c03001143e0b0000d50250707074102c0381c90380c00040c0c40303584020340d000c0c000e00d040c5102030307801000304e1403020103900094200109103c00c2411788146124054800790369801c0890749031402c2e0300003000300d0104ea041d440e01c0041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 942532293 1250 942531043 942531047
    0xb040e06011a0a0504030f06021606060f09020c0a020415210c0b0f0a030221040510140606120408040b0f1806071109041502030a0902091003050705150c01020d0c 71
    0x212003220641e00b4010440caa002036441001c0d034041d40d51011118041c0359072401c14001034080c042e1126054502c2000c00750400c44203038412400c582e07a0b411b100d18026503c0e4a031204034007409010b40243d4000d441800d0041c900303503100d031040304005252804421b4a41c0100721030241010100d1803101c0791002200103100001e000c01d0014506000310398517040c0d110b00c1a040c24050007154505250b00410908000b041400e1a4445075005000b2125a0315103414070960711120000e080408620b041c1200340481c0c11005070510440000c1e160382c2c81e0001e610b42c0e11000c40700051060719029400e02000c143c40060400800c801040d08030f0f02c50712541081e14494071010640b01041c0b003101d0400071100001c400c4146d04904550446041650380c4e55410000b80350242e50820240082c03001042001d41c07841d50744002c01c03580c002e4030f5250701541c40110301c1c5002c07449404060510303031144404101d14a40582c1c0f655411641110007814140e940061600f60f03005080007010454541c2c000c041c1040d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 942533543 1250 942532293 942532319
    0x703052e0c090302010507050705040f06051e09181c02060f010e01030c0b0306220606120b0a0902070503070b01230303120a05090c030a05060604061e060309060b040e0601 75
    0xd0580400c00080300c0e6658040d11500092000a040c46004545e54082c0f181c00e001080050801030400e004800790342c031003100201014041c19200b140603110004207144120f40b00681201c002d4107a5031750b034840c00700c540078107504030442c01d02c28800c18030031441a4000c2c01c03440307103180e03103a40080c8071509115190000c0100142c2210903041460001003002c07889c02c807030038011070311404142c982d0ba844000200c0d069044004a41c041e5411030004003d521005611843c21076a03990f80761a40341000d409554261044005d41c0c66001c00618014484075841e54014030315180325104172840e02c0680c2c0d807521013101d000d0703202400354004070505810324500e04840c03900e0501c0c02c5019619090541c102c009141c08043c0c640c09a2960341c0e00041c01e801d03020002d0b842c00480080880744269901c0c07402c50382d00c500407101e0a000318105400000e46001d00f940501300d0301410600c0058940c2000021401440050810398605840b852680c0c032035150382c407a840c480e40d00c94001d40740c90740c100742001e4005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 942534793 1250 942533543 942533623
    0x30a0b0906071106061c080309060a0e010c0e0402030a06170303060108070f021908040504090b0115031808160b012d230301021b0a0309050102060f0403030e070305 72
    0x40a0f01c0c0240c0004101e010880c5544243e003220b141c260101c21150641c070510f00d02c600104140b000105100c20724100064151107031020b50818484d030010346110303034261003081d8024404100020080b07402c03403905401840c1c1c400c40055002550316175500b41d249180f1054112100c2a400000c00c3c000c0d07070351f0311040302e581c042e955040c25404240d8038440250703103480400104546500344200c50f8108500f0004a40060030300406c00e0100001d103081030121600c1c288207060740c0c1440c1c100d00c0304400740680140202100303000c040d50603001c0030303071a0883c90354050902d28580318101f0700c04400081402d288d090182451303c22890030106086648a2368054101c42e0008415004804000c0030000400c1c0220092104c8113038081c00ba4480d001c64064060640c100b00a21a0124000c2d540040040c814101900070707a6980609550b40c401a80c840506469507086c2c0b003422000540840d019400640c00703d0302480849000170b0303698171210f0074070301452800700750420381e50405802104268108015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 942536043 1250 942534793 942534797
    0xb071a060609040b0d140102180a0305061f03050a06050a0c0e100509010e030d020a021f23090306041101091e060f12060b040e071806120b030a0b090607 67
    0x824141000050072034051101202e01c5503403038031121032040d101c800313a55103415844019419002c896006403800307508001b2808014040f901c5541c040e44c9481d012402c21aa0000c001d02010b4843c40081e03e80201c60410801301307010740c2ea20010000c2c40400c2852603042c02050001401e041a01c1588141c5411210f04400c2101c00c07610b1403100d550707859031a076020111f401c220390742d00800300050f6154805420030990601811090101454011484800b214821070346106100114030309005070742c56031000301c030008002011b070890700d0154248150042090303070911342c140403000d00043c0c5800f904486c2100c1e07103003100e158031b415560001424006001e02c04c000301b60360303038005000410714002803244c502008119969184114000e8880c030421341d82c02c400074051180c54040d42c08095111744204400c0200c29800507420901c940c1c1c80041c411000c0c0c111245181c80c00508036048900300c81880059a80c0c4c0d0480381d0780b65000c001200c2d0b06842070250000c2454681c09003820918001c1070301c01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 942537293 1250 942536043 942536093
    0x4060f0e01141c110702030106050d05150c0c010c090e07020a03020c06071403071101020d08130f140106080601030c08030a320406051b0c0d03031a06040b07 69
    0x5000d0381c124500700c002c2d01e490103546441e402e40840c100d201c418441c01200c00c01d0301d004207681e43c00c1d003040010302e1558004e070000e0040c25955030a00c500303481d405001a03c0c0d0381000c81025101501e04490a800070181070342c40b800c0550640c030542c2142c1c42c107607510000c1041d03010100422101c900480f584400c8500140282120341c0d1400307901d504d800c1c1c000c01c0c491540007e502e8200011040f400d5208010700c03048070340700c012514003d40b0030300c60448210f01510079043c00e55050f03441450020303c146c020000240c0417002035502c44440c80c5050700200d92542003003001c81603410007403261000038501c81e4000c0c0615495810300ea00d12284642100d40704d608100091000c407a00030842c0c3e9540d40d4184c07418001000c042c94451b0a00c400d80803002807d0304000f070000303911035020001d03150400034541c804040c0d1000c00c40c2c01e13589807000801035800034210340024004ca030003640044041d0842400b0076000751002c40004001c0d81c415006003440c00e201003019400e12040b400f904e180c000781102d04c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 942538543 1250 942537293 942537317
    0x21c120207061413090207080307171308160203030d1401050a06050a110f010c0903020f0907090b070f0c06170705030c032202040c0306080d0207050d02190e07020304060f 75
    0x248043d40205480e075038201e0004244c4840416910890b0040c40001403c6448201e0741c90300c00c000f54404c1e150741c40010a0105200700d0040303c241c089001d80f1001040f10842da00320340e5034207181d811518910719070301081600e0313101588043c00200740488a01b400015650154508003805d214180c120501840b8014003d0001b160003800b100c1c044506420b108081d01554a0502d01e842102100d40c001c550034801940c1030150006524025244203c60155102c10700c1020702c49200c2d000c40700980001d0007001c08001e40010000100102802020000c20309405500c8803003814099502041c0000c81c84816a030709008a8403003550000c0340b07480c0662540c200840351031303100d01000c1c2c0342d26803080c459000c0e54081c0700133581d10400c140d8094000d1041103210308014009001d544200e001e01d00905e060303803a00c4c07031001c00c075401a04c0700248142404182a002c2c001030701e0702c4000d0f00c56034502c0c0c24400f00d0509490399566220302001c0d802142d03154100301000301000c02c101080d005002c40c3c80e40340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 942539793 1250 942538543 942538547
    0x140a060311160c17010506010f020a0c0504150503060c180a0e06090612100e1212180102070203030c0309012003030f070216061d031906020d0603021c12020706 70
    0xc41070b0142d010507201220140707003050121500e450384540c0d10071526918050407150706400142c0704d06000d0f21100c00c0d6a2000b98281c0e02d611034164000c00e0344010310420b10040c542a07009024007111103081c2540340b034940b40807030b00d04034007501c8200507800003180a99000101c0d801d000700024050721401406403a1107090343d000640903003031030307c41e070f400c4800a502e5442d411514110100d00c801110075030b02c607902d02d0f000140700c802c9071702ca070601456600b5892449200c0881c0d0741c0d540317090700a007942c4d40c460000118151849100c20180d540030002d0a015a40400190620004e0b20000d1030303840e442000003504142848002c00000401a40101c06050000c0103a95010b8158906030350385544111040741041c541145460301c007808080007040203540301030550b508802c01c01030740c0080c4611b0800c0542c3d6100000c1e1001c1444501e10142000403c1d9401505101a10b00c002240306a00e80d07000944c241e101844401c4a103c01700c07100f400b0f010307070b0f85951121849e950014003070150030440c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 942541043 1250 942539793 942539797
    0x6050a0803030109020a0c0c0303030509060a1b0e15030708190504021305060d1b1a0309031b07120303020909060f0108060f0a030206161a15130213140a060311 70
    0x1480210b43c1e170129104196601601e2811151984200b1a00710540c6a00d17026000708015100e9000601c0342e0340000d0486a52446840340000c081207800c407801680101c101c412040c80b02c0e1076900401b040c0031030f240429460780a1401079459803142403641c0740c1442da07c840c00102964296541d800e1400384000761303d51151030303010070f54440404a100da98410102e01d802c401390700c006103080c0c142c5115121030554400c40d08140c401d850b4217420740c500008031024581c00191f0706141e0940041050f800c100032170500050160201034140c5050503550031404000300c121020580200e84c00113102d023028500b88503226408103080302c50385010101032000030001580288901d001d01e090541c1e520711039440c045620002c582c000c000e203664007410360b00901100111a0f0444c1e6414041e50203c4451841101d2140310b0034102d000e0400c9000220100700c0b050143d0300e9107102d0301d50300f001080421100400100064901e4441c0e55030313001e01220900a196400317602c800101898200007802d15031000c02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 942542293 1250 942541043 942541049
    0xa05220f030e01030207020d0c080f16290c01050403030c170105060d0902030a0501020d0608060f1603020c0307061a01050f0906090102070519090506010504080a031107120b060406050a08030301 85
    0x5450b401400c04400160000e10407040702940c030000c0300c10450100101c002c4068243e5074074105071000b045511480b1039560b070541300d481c038a80000d05018021207001106039030080212240da003212451520600703950368032142400a05035100e1041205140c1c042c058140005458545110900c03111034501c851030b20103006040c0308510000d03403001103100f1908030740b59094000301994000c1e0294a003440c000e60240d04803a20305414488001014480840c00310b1180c6003402070118651345504c1ea1540f4548240c4039042403690a00440040000070806040701074451800083c03800107154181030040e00c0c0b0018076040003400c1003405201030303112064801450341602c40f592205100d80040c3c0c24015140c025a410400f00002d0805141680c1100b03000c44000c03404c1040240c440c1717001119039110713074008e140c0300d58082c80982000070320031300d06004034400c242c094459454071200b4030010302000c08000d07901500000b041c0429883d00d0701c21100105000c9804403900c91030161255100c3c00148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 942543543 1250 942542293 942542297
    0x5090a090b032e0c02030c030f041a0c030a03050606042301030e0f0c2202030f040b060102030918070215070512060603040f080a02030f160605150915060906030a05220f03 75
    0x245000104e14020000e40d101c800010042c2d0352100017200030703900240c000740300b104200020000500c441e00c103c031301160140e12080010314603082201005801526015061030703040a0204000100d010402c01296540006003102c40010b035443c10005054078441800c1200390b4100d0f4003034400030800052030059211041da0000708007149007180e00c024142281e41c016025000001f04840c81b00c51640d114841c0c0e100b140d0b41401522392030012a500d00a825003690042c555040321422094450005940058a40f0440e61905085012140d003c2c0c01139a0902c0407800100b41d0040070414041c10700e0740b000e41510528198034060302c40046901e44203501034a5081c0000784250141d100b402107800c00c8101c10ba00750f659069024081c07103050302100302500d18a29140210301150040180d108002d00c00400700d104a40310206054290485240d80c503600c050104941c001e1611050042d6104807030f1194000740c5440c02207201503503aa0314400910f40d80c0031003800d520004811107038104074982c040c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 942544793 1250 942543543 942543551
    0x3050906060f0a0e0c0408101e05061309080310050321280203041a0304030905060f221a030405060c0a0306030501020706090302010605011404050d0305090a090b032e 73
    0x350085403c2501d5600604041464001080601d451440040080b180d128088802000d280405402100c1d14080c004920b00b1851540719103e100c0c0b900726a403c55030040100845111014201d0100c446111048640705008410410a010038500c418010401500604410244403a500440600d6603e004440f0a00410b525181c0c1c51900c080c070780c0030004041c41c901c0d00e510511001e5641e401510998180740e22580da880c0c4501c80400680307026540c50380305d0600150511007007000c1d82d045115070103c0c4070000d200c0c01c42040522400e4080440d0b95201c280032031030900c1c0c103541e00c507111141c0c082c403800c10400521002810001e4026400700d025040c40c0d80310021010100c002d42202c0d80050125030000c9460b10511041d544202000c42c0300f034008021070b56950300150340703001c2c1e5031065040d00702052200700118101541e0200d02203200349009403916001000041d4808041c1d00701e15912540c4504400d0f039428100b100c03546880d041c00d02810507a400f0781c001c2000540c080d0b0035004050326 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 942546043 1250 942544793 942544819
    0xf060b0406141819030b0a0b010e1e060703110f0f0a03050307020705090a020d14010510030506181e13081b0a140312060d0f120e10030212070305090606 67
    0x4a000e2000d14000e00502c044134103944013154840c090301003a140c41c007035140802d034503100d5841010f480683c1a11181c04009107101006a481d160944003208000d141041c2c0c1480c0d640d8000502101d88243c80b0a1203003203031600b4240c5803c82e405150304003548200d9122104100000f820000d4640c10b1800542d01c0d504c01741d080f030403c0c280341e1080d034000e1000c00500080c40001e40182050180c1001e01300100f5416560700e070400b100c284521500700b1851000c81c2d40c107620941000341d02100203404148500001c03a155100390340c0449080700c5060001000004000400c1d001c150000d80c0e850b460030110600d91940019803050284407500c03640c00b41d4090070000303801d000c540c2e00c41c0d400c01902440644140005500c03940102032440815800c2400100746262526104030707540d0b04010b04003085002a030b00c1d210321201214000f0144490303102c403050700d5601c059851451901c950781c0980c98a620b1a646c01c607414001e03060710b06043c100b40400041c10000107500354001c004481c510200d00c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 942547293 1250 942546043 942546067
    0x39051503040c08032b050103080a030c110a1b080a08090907110f0303011706010e1b0408010c0203070c060c0f0b0703020f0c070303080714030705070804180f060b040614 74
    0x4501d5020802071300020401c080c08220030f8125800d0040380081742c0390705d608203102d010b0451340240401042c0010501c1700303604062080d0700103580303050706003010700c000700b09103841900d04100004200c0d12204507129500a041586d0b283d200201050001007480400300d6480c14298000c03003c07100e005071800400548824030035401c0e40340c00c102c031a003620b03241d00000c20f80580300d038024003541e55421f51540c2c1c00f102c1e007500010058100c1e040e03001c18040d03903194940d40c055202240c04056400074414003011612141c20b2040c1500d0b0681c1f90002c40c1d64002501d403020b5000203030391142c018446050000b00126912141403280640e2024100c00e00b6034411405074028016024a026111030206070707042510000034100058900179142c04c1c84c83da54000088802040c030084070fa80f107d80c14000b16407004e0042024002c214451040340307040039280c85c9050b52600b0041c1c00c2641c850f031a03680d6184000b15500c940009003610301560340c505400c140c806031132030444890001590800185001c0406 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 942548543 1250 942547293 942547313
    0xe150403051606090c03051e100e01060f09020a0e0d020102250b07081c0c020706140f070b06190623071208071d0901120f3905150304 59
    0x2d0b9022604000b501c01509002d412401c1e5800704490303e1003a4890003d902c650302d01e66004e1000c80c000142108800e445c11040030b03120410031624559240d07400800c2520324100c501000e040e494100584030441031100900d600608200e1030b0040817400c070303044050307603010411484a0398092003000c007d032078590000d80c0e161000d5211020441d400700e0305100300440d00008005c032104444549405040c9040c080081f108207402d403d0250b400044208030450042d02010000c0c5000b50049060103403031700001c1001c2d0f00500048030640540f0040011f00d00d0051080c0340d038590503031040c0c01e02c10304229000c1c00707030721151143c10151800400400106000c82d41240c80d4260b021803042d0800c1540e21000d0f061003000d136011030200d1100c000c91000c4c0c502d40c0030b401c100703400000c00b80d420503460314000c055030b0000002d054410388003005002012800542114490010915494640e9031a03108a450410300d0480c481032090f0040f001040207941d80e0200760444021a48500e68a071600d02e0002181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 942549793 1250 942548543 942548587
    0xe0709090f110d11091b0a0906172e03050d090503010c020c010210181203021c0207020f0105090316030c080d051c02030705130f090f1e0203060d0501090b01090e15040305 75
    0x3010002486c47c907040c0c0d110003100111601c546071141c881c1846070390f01c41003920890305446801c00030911310700b840ca030411102554411102980d0611030316511202d090003d101c2115010902d89041000a400d0074801d80440d844180301a007459026000000e49507211b002000c054951100c0500f030243c0c00000a03498404d038844a20b405800840034098041c0d000483d94441030410034500c200031802500803205840d500034206200005441c0041d04c064000c0d2030459054072400720741414034101707041800091170040c002c0340c20381407401d040c480c60316540034000070800105010020008000c2c4070b20350f03a214550704000d81c60340d90308581200e0074002c00803010144040c1840014501c00c0c130143c08005e5803a0101c00b84100b00003422404281d940a40e40c099203500640184100d0721000c1d4040d64011030b008000700309004045e102d031801d45c2e40c940001e0710a024210010407408025100b1500356482e40c1c40a0099401810900c0341c10010081010f010700c407001a0644a8040120030030743c40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 942551043 1250 942549793 942549841
    0x1c2f07030806090901180f06060b0703140f04120b040c0b0903031918140915031b0411130509060102012702060d0c03021812030702040e0709090f110d1109 68
    0x180c04080c1403501f601190742005680c814549980032801c8503800382100e4595815481d2407210030b0202e800e05d0201d03132041129905580040c0400f041c00d03040320052042d280e01400351586941440c0c1007208040d910b580c0b05e01d458031001c001c003a001d80c4011041d1241c412020f128038003030b54030340d6a0956044620311203505194200b07201c0410042d10051941820903c00c2d40c4d1030026985046120005080300000f0300d5144e0f100c01081d14000d04070000c000d2424601600225694071642c107802400c0d0000c05035596110111f9506200c10304241c00c200d43e00a00902c028000030925040003100c2551150084540101c001c14030703025512010103c9191070b443c100d003000480c0c607101000f1300035008142e28440c030b041c2d580300c4042513190100b8a40803281044001d540391000b01d41c2080010a5150070516180c0030b00003000030038039550322440e1109130040d2400c00e8205c01d41d00d01409101328014a140c070071401c0c4091036000c600d400415a01d0081c081e507402056407640616071125010301a50440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 942552293 1250 942551043 942551081
    0x50f0c150c100207080301080f0d0c0615050a06031e05010e01120f020a0f0302190303021b010c0c0603051e040809040b030c0301050103030519030e0d051c2f07030806090901 76
    0x4100750171008504075440c4109071a00031062071030807038580403030100c0e010014000300096004a1425440114241c0041d0018800c280e90b440205254003100ea110380e000c41d43c1d5800c040540c40003c1640700203030351000000c0042d5818040074640c164411b028200d0f0b140c1e00080d80b0320800070b4266450003881d0700140240300080d9a25204c0311704002500003203014140c195a43e07a407800046212009607070b4180c01801800d0302003074002c5140765900104604201f00c1c84000c0c8045511260130341c0283c4030750b0750007143e6480c1562032012503400d80b42d10b02d074148051104001c0400c3d103200642d10b030048221004950b2001c69800a8505541c3c00d010a0b499481e2800010415820000414255000340151403031020b030168141c00f103500192051002e070300030416004480303114000a000050202440d8041e004640001a003150071440c0b1440c5000720307403e9400550340203c2001d00f803210200300002d1504070030f42d400411000f00502443c0c0902c5456010419039042034202071002d11048080c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 942553543 1250 942552293 942552307
    0x51b060903041a072a081603031b2f06190806150a0f020c04090c180e07150311030105130902150d0b19030b0103031d090a09050f0c150c1002 62
    0x410200c10011700a03440e1406480700003000c02003c50290401c0c016840c4c0001064610780701602c5607005c0845001021403c0c405050000304074244140f03003140e82d102c06001301d18940b03d0400344103131a954114400c01381801510400035243c00280440c51061508241c0ca86400c0007050041c004000c2d118a03e10700403c0003482a40d10045618902d480b0b82c1c00c80304a50314050900c000c4494004c0702174007050f03032420305100d40c8069080c080c09900f984400013504002000d42c15040c480345801041100803003411310f00900e82e05000b4144102121084141766500d00b8002030201d03000a0040245180c44a500340199512503410030f036407072500d0700c0040e9281a0200403500030507400040d01d1046000340744008240c00581420303003d807580804942520703421a04c2c281c801140f161100a032408007903880059680315055094020b810441011500b180340d4074009080442c1c00c013482c03031281d000352207007011aa54101d60111205c02000c41560364004900740343e05041000420025190001483c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 942554793 1250 942553543 942553583
    0x11240f040f0603051614070f0f02031c0f0801180b0f0a0902042423040807141e031002090f03030301030b010512060118020d090b07051b060903041a07 66
    0x80c401c07000244c4003000600000d0040d1b8002d5610200262000000e1000d00c0010342c660500641c2c0a004081c2d000348144e103907002902d00150194400d101c81c000031800c01c07103180c200800300c0e0303102d500c0e04040d500d40d810546520070105021000f114000d49454440d285525540c880c40341e4400c0141960350403903245e907510b8000c3e40c080c4c85084405040c0750342120f5442d540525031010040703203981c0c0c07114415001c06482020380b00750f01e91245c0c20764100300c00681403c081011030f004100c5808106079412031131081160300300f030982074640c0445000c442401c1d2039501040c1c41c4091400b040006071140f8480000c035151402c0926200e4041c03100200102c1400681c0b01d00d5412940101c401c00302c0c1240c00520613417103a00a00c56148403a4010113402421680743e00030f001c3c5820580b000085600440d100c40c40c071007000741d5546020030400206c00c240c6024180e185801c086c115002017040c1c0c100503400355641d20039880791103a0f04046500d401c002914038400c40d041180c00144401d07002d5640c581c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 942556043 1250 942554793 942554801
    0x70212070614040506090d1e050604060e03191404090e0f0d02070315021c0f0504030f090b040302042c3711060c01020708040311240f040f0603 63
    0x80310041422450040141c0c6404022101a50130140a881c1001406010710210708081e000c01c48562154038407941340040710781188184c8a00550080295040904000085901e0303c045100306800c1004500740000b08a03180801107001ca14042840034208800c40e5502d0055030040f03440c641c10a0040e050003a4001407007180c54240000341d8400d021500310070713030b500c03001440010301c6031403030582084a40c80c5550252a6001c81200c003002611030140e890011101039140d240c0041d95558203010906511040442c040495420005040750500765220598040c078030000703105944400b603001d042c05120702683c00c29198070509449114403c4141501d500c000720f803e00c00c541c4140b401d03006184041d45107a100701405c01c20103c3c603521a4540851a16424500d1500078000300240301100e00244020403160340120304040d241e81c02c62820800e0806071001035071181010a51024001c03120310308204c2090f4841e081503540e105c0103407101140d402103034024800d2100b411000660305402d600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 942557293 1250 942556043 942556049
    0x1b0f2109030c090903080f09010207210e0f0310020702030c21121303060906090203060a060302090105030616230301032306090d0309030302040e1302011103160f030507021207 77
    0x311404203519403d0781c008544d0b0981002c0c000454110101d41e075203a4030710700c03143c00071503800c000341c078015007a02c80c3c0d9110400c4060081482d03107003078200c1d0011036000341c52120029044542200800c4180002540c400b0b844040201c11036000a07a0b10440d03401b0442040d1594010f4005005084d00045c03119500307a200d83c443c50740340228200d4449424000044074902e030036803500810362600395200c900c0105070540045801681da0043c842c05030341e041209038440d0840d000049103007421441440a407440680c04180254000002c2c4010607101b80c00e50320303824250745000da44405102002034070010004e444c2011001d0000004030502c410701c00041c0072000745c2020301c5800115010810780d1041c044812400a412981020010390311a420040505000e850098102034441c1c140190180095501001b0a16111040303011942c03c540040c0601d01c0a10296082c840084446070380340c980604020001180030072814201400341c42074032030058002c0c02c40056206050f00b010b94400c5140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 942558543 1250 942557293 942557303
    0x6040306050709230d030c0501021e090301140903030f06130501060e09070c0f061d1906110406050313061404050a0b01080d140a020f0f1c1b0f210903 66
    0x42041074107829101010345960a005e0600071001031142c40031281540001d02c112081d5400b0000014034020100d0008000602d1a00a41c0d50b1624081010708680b50b1003070002148084204112003c82c0200c1500ea00008000d130050266a521000443d21a40d0f50180c5101520701800403840c298405034400c80c2c0002550359060340d4481e03440641c1d0f012801640100700050528850340003a030b56412201c89001e450140758112908140054149501c02c00349080c030620b02d014100030700c035490007040e14441d04081c42c1c07441c25043c80401046840010310803a140540d088141e0100101170340a40e2a0380e46596010010b4281841c2040c0c4408001a060740e200c6178082c0049454a004942064444001d85030b50089070802c000101150b042202c0100c250f0055403001d11140c9801d1040342c1e42c40d070392800544a005d58000c1d40d4450014422000c0d0100204205031902101c0010015070700d85421010703c5d1082c000620340038a0704400ba01c4443c06c400300032001000819004849070f41928070903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 942559793 1250 942558543 942558569
    0x3040c08070e0f1e0720120d1103010e0109090302120a080f0a05131415091c020303100e0613020f1305100c12020f031315140a0e06040306050709 64
    0x2a0f400b0f8198020452040e411213614400400c05482c05480c1002a5800306002d020b041c2400707081243c140307103094080e49170042e800107540000c07440900c00c00c40c800b21001d041900315410f100c5000040c48050242000b0f0075610340c00c81c402c3c103000b00401d1034400607000007160307640301004004211101c1580d8405050036000042855800749004007427041c0290040048080c1054417903000c00344a24200d107400c0d024400041e60600020180248140090230003045a500000b84d03c43d211041c9010580c119041801070150502d6441c20341400c480b01000722072020349a40000030944d480c40b43e94254031078030000780e108440c5082d40251003481c3c040100c40503003581e03c4051214003d0396410000c0007501d0f4041480001e03400c40108800c030b2000c5d104031040141284c0d402031455004030828180550008410804003012610411400c2aa403510011500030650840062b0084400a60a00000d13a64124260312441c1c01d440c02036803c0750041c07203103017409000a0108601030107013100c00640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 942561043 1250 942559793 942559801
    0xd021602040e0d1209080c07080d02100e070e070e040c090503010b040204181d06040305121e0109020c03090a030606030c06110307030c17030709060207080f0c040203040c08070e0f 79
    0x400300d510100764000d0345485035403444182825004040d0324000701c620708010310040c160f07c5000c1081d5000b40018000518880c1180c0b6000307031901142041100015081010b01101d00c1404186041140c6902040d0500740d15140410f0b26404034080600390454036140d0040300b840d500000420407650f0036402009541c848000b0320059200d54040d12112031030701817400c4414a030030752003c910b004260781020360305c540c420700c1d441c101482a5020360010785d0105101078201c105c441950303000f0613002c05120605d05009008991580144611002c12740c1c0070400750600d103428012180c103600010452030440741ca038a800c00040038140000e40c0c1d046140715000c116180101d10740d103d48468a001182410129501207501c030f1380040c0c1c01ca031801121714451850001d00e10103540a500141c807000619403c00000902d842c0580e4410032a95012408600c1d40840100f81040c0c560303820341d0b026a0303e5803282403520790380c070301503100020354816000005008901602d9050240040380c0406c00c503031700c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 942562293 1250 942561043 942561071
    0x5071806021605060c01020c07030309090f0b012c060a0323040206040e040c1d04060b060901121802120d0f020c011407032304050120060c0c030d02160204 68
    0x1001c01c038a00e082d1190b84100788841c2c034218000d428070006101c0098501081c10044c981880f669500881c04038441403824407208906004041200c1000c0d10200300140d50640024208900d41640048594803202042c41c01c032a00440b640028401400e9035540b040e130403000034000c0901e0002202e04030fa803083d40c40800e855080c03540d4010350f0014041d07810907082441c1280351540180c412901041c030410000380c0c08001c60200303c07d018113228400b920317240c0390411406a90440350700320303c5800c2c1088042a580e800103a03404a00d00003800009202c1440e000d40155822504e9020354003460100d00519400b00026010103100001d42d030741c00021389520016a07480b1103075030106020501016100156246400150001c14024a403551040f41c0200f042014951021981c5c101504006824080d958011410410340390815641d445201c807915101c4c0d0300c414004e04000a9a03200183c00714100404206661125120f814110b5a5203503610140d103c018040350100e00035400c0003c8442151 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 942563543 1250 942562293 942562303
    0x20405010806070903021009050306010b090f0f011b060e1b1801060801031106130605041a0f0304081605070e040b0a021222060e1b150906090d060507180602 69
    0x3c1e5515003469450459081203d9204500c01150408c00511070001d0540c2d82000128000c10343c0c0c6810a94135600e000910812700c8515006038000d1145810070722071030b64854042c12030345400800d8210014036524000021307150f56036040859108840d00e0180b18810100c0341603480104842169002804504505c4800303024458030000c42c904000410100d04100b442d0f0340d111038001c000d5032038007448216240040c900703a041240001d101240c14418800510319003c5084035420040d42030a008007042d4415100c0288004d103c180c01043c1040a0340449107a421516031100541300060b45551a590942200321401d45c0c68800c1917000c00c00300003072442103c41e8045110400c0780503035981e080b0038680090003c5043c3c1000d15405116000c110548510000880d013200070f40480354039112031a411a903c03a10313681c80f030310356503103090700501886003203543c8003205a40950b2a0303038003c4001890420b030500060140c1d8101400c11107401c1d4040c20091170a4008680405000d84450040b0b07038031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 942564793 1250 942563543 942563551
    0xc0f04032306010f03050d030b04091a07091a0d0e0a0c0816090e0d0c0312020d15170318150705150a0c0f050309010603080c06070e01050a0801260118020405010806 72
    0x25801c1f21348448201d40c42a080850114009000800c049410741c0e50140c034004090b0b10025000c0e8010240601c40b540f01380140010503a9030068008010861799100203482000420401559514110100c0f0141400401c1000707811008180302581d64559035600c074101c030503a00007000112040442c0612f10381c4242400149810024034a4084d12034064420b01d450303030010703400c0c4004240703910300c0101d580c0001c0c4405c10202c000801c14140950040c1148905604101000010202c0305061002c00005898040582100240103901c0040c08a81c031070030340c12403030b0491100c005041c070b0500100080c4080d404041c006209a198de6141d2120100c54040c110b61b80050031029040500d2845640034540201c09000000f82c04d907544c0da03800c50507910240700c0345d6054002c1820030020a421802075681c1b01400e007005d42c94607460b0f52008012036014058104500100e1018104442d002040001207035482c000801c1410704100410700703021020402240314a00346800490800000305485000f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 942566043 1250 942564793 942564803
    0xd060b040f150306030b0a0b030c10020a03270905040516031509020111070f05031e060f0405010e250504020708090f010512010e07090e0702060c0f04032306010f03 72
    0x54505244600d448581440c03842da04041c0c540d0302c0440410300c00c0c210703c0d004003118500090003a44002c149401c00c4200d50819102c1c0030842101e402035500440e00c915815414a000150881c20582000140001c0b184030142c408540001196003d02648203501583c05042150031400308003022114082d601c0c0001081c0d4045410502ca600c941a00800310140c4141860f00101180030040c500d080d085030301422040c00000400c00c4141428009041042c40100c1803c849265400300c2541d140806080071b04041208000601801420b602a62801d0310601c191038114440d02c841c102800f03101c0b12140400501c003c40015180380c40d108494603941d00024103408c10782e45004120820a1040150b414001e042025075a12110328400d14017829034402541c2280c10a2080209020403a4229030503039100701d0240441542c0018803207a00c242c840309070b2a502e0000500d03168003801198401400a102136403000d03000d905c80c02070840783d0071380d43d022a90580e03651074160341440994800508 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 942567293 1250 942566043 942566069
    0x11030306100e0607060f15060216030f0812090106090605180604050417040609060210050631020a090302030f1518150a1d060115080a06090507050d060b04 68
    0x1414050b1441c0124400b0040c01c29050880d56194001071703955410003040e906d60381d002020048403525003060302806103440100110800c0b10f110120068040c000a821035603840038203c2007004c024100c0d09620380e071440c031950380d00b401a1081e010f080e450140b80780705400c0034030104546c141092003d119412041c4003130036603141c0301c0510008102c042d100352000c403003541d80b1005018051000f0b0005000641e80e559410b45081c00080c1000e202c1c0503004c800c030b8241014415030303584074401f01201419040000024410103210311904500050032030008500128945890390b400045807803c80b402a400d0300c4000140c14071054070348d580c1601074100c1003500c00c0800c4199000000030101344d00d81c00201d81800c0d141d0780341c05940080c1250030201c241d0b11009038a001d581c9509902d0101e40031000108043c0d41880f689000000b6444d22483c00c000b010030010380090307407070340008004000c2078204028904106c80010610760010008011503814507000190b4507650b941110300b03d4004815950b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 942568543 1250 942567293 942567319
    0xa0f020d170c07020d0807030e040204030f02040b0111190314031012060204050411031f0509010504112107020708070510030c050d111306170c0304050703050f070611030306 76
    0x2507079440c0a000151500302c207111900060300d4511114190a0042c0440c41c4c842e0f6003032400422801074507401c0d40c0142d0042c4400c0001403100012960780c154110350100e5500141c43c0125400c03403c03040d440115100340c0c0107182c81d40c0b07442001c0510301400f9640301c3c2c010b5000b051135501c00384001e030707020000301c603048000f000a840d00342d02920a05d031040070b0152500f0394510014007500d62086644101c05800400c3c41044541c070039100c000d0f110a40c0081c84903610388000519840c00511542d0f024544030340b100304d03100c2076080840d502000c116091b681e043c0e0004101c24000182180e00030054803952034041400c41c400610842145c0004010112040078044101c01070700104880c482400070500101da6507000301c0c0a89080000c032013010300c2e01c0c3c580015800030a48540d500407424003080402001060700810340c03041c3d2140052241e84e039a40c40e170340380261400b9919440689075008103405d1b000211700100d5075a085802c0c03a42d41d440d40b03004138581192a40300541d031043c0d00000304a101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 942569793 1250 942568543 942568577
    0x901110316050709050915010501030506131404050c18190e01050910110a020a1403041208090a0609060219030e1e03010e07050108041707080d020a0f020d 68
    0x101065008120660703040c098010104000c1406a00c412142904000c105006500340c903c078507580002078000502c030145040001c000311840600603107041540f50ba001406907103c40e0340d1095115a5040c0810600044441f0010001800e0b2801ca0740c600450402090b10f181400002c103c200705000c20000b6511041444e50b1035183d03400e402e1141c0c40d155540640084801c1c86443d11540d80b02c07015248a56010010404982b58a404003021140c1480040c2c1c00f036900007941c0300010b40c0300340c00c46803d101e020b0b9000d145006907400821031401469070001048601d0006e42408e45e400c3d100c0d8402161030780c038251800402c0b80503140059004003803c40244102c1410503010354001e041c0713007040d10f0143c4042010000041102c04681050101e0300303a00e03060074891940802e500c280640019410440003c0040dc0050000790000300220920038000c18540100c85a455100310810340c3c40320400e5958019400045c00003010a4200c00b40e040c6075400440c8200c5030302c40981d10702c20440b0b013440030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 942571043 1250 942569793 942569807
    0x3271003290102161211010201110405011d0d080a0809120901050702040605120a29130611040f0302030120030c16050f010509100c0903060e0a020a0f090e060c0901 72
    0x252504510505401d601801091341300f00c8054141c00212a0507401d441c10a00060401c1681d010304581c50958440320525099003983c007921000d10b800b81d80000048080b0310740b060040c20b2581c0c000000c000d4501048000d0700100381600d080d4940700165a504c0d01180d442e010711280d60000c282c030401008400d584a040103090b018801800000c0311034941011501c00c08000d220304065a00401084042c8240540d03544800c0d4041c00e094140310300680c900b0390300c0840c0501440f290040140c1160704200c0c05e0b41003242c070000c4030014141c40702d50700e0b40640b03507822581c841a80254a0115481a005910340d2544402c8002c00b02c0340345180c40381d071352003116944514981d1018400c801c00302d0001801c240f09609582003000c0c00400c1e0303418040003580c14140240d46915170240f42c10f21102c6041d810158a8044a400440024406800b2524641000010300000f5070043e040b4a0100340b14070170b00d56020039134004100412001c5002048580d072031005544085580358184000c07010782d8070460b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 942572293 1250 942571043 942571121
    0xb0a140310090618051e0c0a0b071713090615140f07050a061b1707140d0e0a0b1608040f0321050106080606070b1803271003 55
    0x80d001844e006860f0b1075004900c2620400c90b030a4100443c601821000c072044118101700a101030080036002000007152441e00e48647c0e04c16420104800040c0603105000411965010071700581e43c0c0d011606504541e0b009000c2c900849280010104580c0d5024416800d9403555407146124502c0c0610b1404184d045107541149003a0100084400102c3c10f00080450600c07800e00850301c505c808090b400e440d400c11031801704011180c4a011f102200b50310001e5080051800c1c900a50300126108c05414401c110303c0c2c0d515070313052940e102d000000000318494128010080c0c0c41954651041d40315024407040100b000054800e03010501082c406d24190702010b1003814600190031500e100482280305e0444c40c498226030b108010010340f90050101c0783d00c407108650070303860710310383c1c1c0d071906100d550207404044d01d00701501240b032003070100308111350108560b0502001c146491b0071004a0010300003080300d0103114021014144c0a003c0d0041c12200301c541588020300d40705000007010034500c40c1b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 942573543 1250 942572293 942572303
    0xd080417071101031a0a1206140c0d0e070504140f1f03020f031903110d0207050616020a05120f0111041202010f020109170a08090a050303160905090108010b0a14031009 74
    0x4410030403940c480350444020651f511031441500d01509160080b60050810760351005400803c0200d0901d8020842c1c0a44640c0c500009428600c1102903180c00b00341c1e0400d0f6007007807420600c5880e10051039415440b81c51107289400042c1d5a940000d982880c200521960500345501d00740b00600d001c3c071890000782405411181d81422007180d224102d40b0705801a00400e140c400618041c18050010303980d040340c40c1c001848102e180a01088440c424025101c00741e2480b6155081107686840c040001483e0040c0981540d205510016444083d41d5240c44407035880c184481035060031078000d54040f2001d00d04c03210100c00c110f8006580c807607852040300b411035590b0010701c00000c0c6000050151456166071807a128641da00000d404d0070b00113040507105511041c410400110000708885c5c1c441e00307801a9403201f65440d00c0c01c0d106088150001d95005843d6000800e14000560040301e00d02d00c2240e0640146a95111440e980b0540101490f016041903000c482584040c1e00001c64840c030807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 942574793 1250 942573543 942573581
    0xb03012d0207051c1205010e010b0313230c0418030302070305120712060b2802012702090106110d0f050c030c0601090506300c030d08041707110103 65
    0x2607440750b00340b1a044c10b000071004030004110408650000440e2914090444c0800095040651021480805100f10a0004400000194290846208104d255600070300c0582c0e9100c1c4050f4024a80302100d0b4540a03900c1010b00740c0074a4982070040b0103e414814129500031080c0381c800b20040c0d070240b44164107101d42080301c1c45450956000c50b51180546641d1417000c07203254080d550076200340f5441340f421504140302c0020005420354000c0e9105100d9030b100c8034915041981030b80544420130b0030007412400320b1510040030176040344d95030201d44215000600791ba2100d50a50f8405040403a0103229031150050002ca03078015812110560203a0401a0806240000030741c0340d40c0c040103d480c0e013a0020001000810024083d1682110f0111500780458034548041c1310381042c41aa4003400c1c2c02d1100c2c00038500a4240282c641110000c1d055401c3c040145c8000740103030f107055400320340e0154039005040714600700006856050743d00c505501100301c000700044020703050700c03880580c09844c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 942576043 1250 942574793 942574807
    0x1201180e06070e032e0f0e1b0f01090303020312040303090b070c060c0e0d24050c04061e1d19080d020f0c091306020717030a0b03012d02 60
    0x1041114420012940c07180c000050000c1813608181044051616a5204c10301e842d034070320030345451020407081440001540c0c0d03020030900b002410000003507031800d0244061a104400442c3c46003c100c240540e00c64846000c860011034500c25244400780040e00240300d0344810f0074070387c800749802038002d103004104010715403680b582c400016506180410019601081000440e0184451803c06800c0c1201d6815100d008a1000c0d0881d00f001048031151126111820b017402841640203102407030108403514004c0309041590340b00c0e0241c000402d01d12546952001243e0080c080c480c0481e540f40c032441c010100890f0790718048080b0803540643c00c480f201601e403110280200081245100416070820403110290800c154045050f5403174010a10003a07030740e00c44112254003c1c41b00b681d004035a40340781c103040c0024000e60344d00a20580c070008048000303640e1040654080d07200440200080b00d600401c06089aa4100750700c03140c0b00c0240c00d80503e03c1004505598260f460000c05460011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 942577293 1250 942576043 942576071
    0x8011e0302131a01080103030e2223130c120203031e090a050a030218070c0501060b04050a090b100e19170c120304050d060b0301230c120118 62
    0x1c91816041c0c11030340d50305010182a14001e080b000c0700f04082c00d10381c030307030b9411500c004256046508105009038115018501c4000001e02035590380c0c5818a0100312a0b4259601c010204c04158400b0300410b041d0408184440e55415120300c00c20391084030458014a410005a0340080701c0070244d9050105000d02451105000701204104110708101d035518011075040010442143e008035000c0c0c89502d10172300c0141c981c19021000280b660301034007140c1da20680700316008105050f004019508001d4001551490035001c0d0060300c40403950701c3d25054071120944111481c035060168011b4204030382d103030207600608412050a5002d0030304600c0841c20994941d444606034051040156000e8104072041e000340104e190442e0102c135046049074006810307554900541c00786500c07642070307a01c0c0fa400b000402e90005e024002e01400a000110207140c0044080c10352858407845e4407407110001701da0100d144216052500000020505e41c3d017400b9816074590f8444ca0b140c48096920b80210249030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 942578543 1250 942577293 942577309
    0x2a0f0b0a0609050a06030506040209040519030c03030c05210405031b07090f021c1a180711010608070e0408040e010806070e0d0c140103090c08010903090b0a08011e0302 74
    0x400345404105586424082c100b1610000d011104061901740c080c4001403000c950543c0203901201c032071689888500701719046c540881e12050040c4068481c4100701a040100602840c1c002c0d02c08001c8903590f960151180d10a4a40c02c0c0400c028035244181041ca4100800340c01074081c104032810f0020000c14000068501054001c0507030203a80c0801375170600d0300030f00b03810301e0307074400d0660400030040d268881c500c3c282290002c2c01074440d10740031704442d10718001680d10f540c0184441c2800c0300381124101c2034001a516503002a050005000a82d041401500c0482d242c2d4802400c459103010041103880f04042e00445440c20308010000313580300e1036058103002e01202030180c442c9080c819409049182c4140d84280075038a041c025801007031031083c0c15001c6840c0c0401601ca14200381c00124000d08507000002c0284170842030105005005501c40d124481c400d031101d00d9001d44542a10350203015403c11500094120001400303148a1a10103c007512400c03028101010307280ea0000d141e81e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 942579793 1250 942578543 942578551
    0x804090e0106050402040b1e070b0f07021903030b010f0206240109030c0b0a1b0203030d090f2a0509010e0a0903020f0f03070317040213021b0f0d0f2a0f0b 68
    0x803401052340c0116000d021440110005403051503494500d1a40e1a0010050000c0c441152042c4002c0040d820034000e1082c00c6110b08585803180c0d01101910b0080c0041c24113000003400102d0307207030f2005101b43c0000350050140c941c88000801e440c240b88113091008904241c194100b041d900304c00000920030000d40405031994503000c6850f0342c041c180003003448c084c0d80402280021452449000b5840102c111b030408003060300c001c501c1e0261800d0000d64015266001407041b0141c44000400404a00c1504500702820521160942d510360030010404028000c0c5c0707400d81c00000215820070165400f03120301c1c5100340161803c0c82400c0384924203010300300c00c6600c0301da0000511344041652080541628031000110080c0e6410180c010480211210048070802b41d0b0018200840b20000405d1420902c503800855070580a590340881c0c4403100c10003244041291040b5281c1542d01840b45d00c03e081e12545003081a01d80043d41070000307070030100b10039546241d010720000042908420f00ca481 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 942581043 1250 942579793 942579809
    0x3071205132306061c0b060105041d0109050a0c02060109051e0a020c0c0a03050604111f030f05060409050a1104110d0207051b030d0311090402030108280804090e010605040204 77
    0x1c82d26030224039a0a0040c010441481075648519400340b0b400b103540c28000e10341d0000540a03d66a440300140c0b00c5120381d0f0000b10180c0d400c030a94810358800c0f19145e60684842004c107202a4035403003180c40c00e0364003000c084400b50704408018007850101e540f003a82d10107014101405444040743d00080c1411050f19504401da0300020300c1e1110700e03c100b01244580c50705841c1e81000a255032a12030321018090300c0240b2518a16200d04042c6c1c0d07505c02d504c101020b07400ca0050320010b42c610058001e1005200021a150824000501c60f1409118950750315400c140600030540300d0707595102c034016540709480ea0003940c40416101c94425040903082084104a0069545a0a04119282c419150021048a1404611650607880100b071080b000e0103503017004903c02c9203008800000740078600741c2540045c03012000003001c10002403000149489161100c2014220b40d1107041c400001e44030103001d01404020401400740d9035444403014900301c8000240c41915030300000c1c1a039000d0740c8000c070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 942582293 1250 942581043 942581093
    0x40f060b1303031701030804030b1b0a0c021509100f03090605040f140706020d0f0309021008010e010e0403021203071205040c0609083d1e060b0307120513 68
    0x30815801c99400e4401c10880c42c4ca480d070541c515601c0b10309500c91408018490741d003075008100c81500d80440082200400d0022540300c44004000070019003200c0426841490700c43e101032403017041d480c04c961103144064541d0303241c1e01e0601400d9813480ea99030f490a04042c1d880c5540d50110f9880e00c900d50103507101d4002c1000c8181c1c44d0401100a0b54a1844021607800905081025a40015112840380028113180a0456450303100303030000d040458001c0c4d04004403920004000703601c00030a40c10385294624403a026600d40101031f1028904840080260307000d030140103030081d00038002d13581c04059440c000190340b02c002204000d031001650101c88594283d00f040c044143c220601c6400f402003000102001c000c0d01a808130b03109401500c94801c0d5030b24206d20320360b003041d00104075000011010b0a0158640c00d4404246a002990500d495176143c0340e004112840320f102144d00580d99a6079006941490441c41c00041c10060700050010f000d41826400103150410001111100007a072a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 942583543 1250 942582293 942582299
    0x60315090e061608070c030323010b0a140c0a02090612010c030b010f0f1b0f0c060903030f050f0a270b030f01080a0209070c030212031510080114040f060b13 69
    0xc8104103c0d0400380701404941e000300007aa9074004808043c603501481d01240a2421207650703c000c001103881c0d15040d02c08036001045503080c8000400303507841165a540303030f0070364800310243c0e09004405095015811071308510015140612100e0341048000300b98440b41300500711b803a82180c00c0b0030400c0d40460b8807108006840d40e0004680d054070303100c07810100e10030841880c004022003166440004080704404000c07051015000e51200e02580c4048070b0014661180005014981244002c0340010300300b1080c610001c1c4504203031074032203961000060608027012004e4070500700e0f6401d04070880700200c003044205040101500002c1191940c1c05a0300d0500303002411508505800000080c0e124100007070058a0301805a90b0210282c507010341c40c0c421500c1c040b4145042c05920814412011051001a000340c402c0710301e042d10101d85c000d28640340e00c1da050b41c0c00c0e8400d120b04250103040401c880c28a0600ea08589070800301b0480000e509621441e8000700d541080120b000b80040b005414 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 942584793 1250 942583543 942583561
    0xa02090d03081501080112021201020903032a01060b040b090d1203020406080a0903020712151a03061e06040f060302090c03060a1202030c01050d180b0709050415060315090e06 77
    0x10400f41d641c00e191207841176041c1480c40701415040708000b0f003c0c103080c80112111000c03e5041e640c48880040983e6aa12a020001051201003c801c806500002105400380410500c40c80007201c4188203e282043e1500100303e10a40000c074056402c200f034407001900040c454400704580f1100d94078016115418030f90000c041c0324009142803200c6250035460004260000380003422108000c0c41c84034400c0551600e0400054140c14000c4000d040c401f4240f010200300e0003003417246406904481c403035175413803602c0426600e00e118006042500040400d010b0304041e00000094070803207401044040c1d0380c1d40414440902243e00c0b01824101005000c00c0341b170018100002002128110228035002c0d40010703403208a035800d058180031b4000b41c0303081c0c4950031390440701003080c640c0a121011380060030f10b254040f20071943c900024405038800301c3c0b0351034540710340804009c403814115007640c00c0c000150002c00c4248a20f04034008d25010000d0328240f203004500500071140043c04580c2000410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 942586043 1250 942584793 942584821
    0x220204110d0c21110c0609010504060f020a08010302090a090b0c07050d052113200112060806041b0b07050f060115050315120a0b0103110a0b040b030a02090d0308 71
    0x2148200011111840010f0f41c040302088000800c0c000c001445000303825184485204104400440303000b00c0d020012908030640c0018840c1e40901414003641d10000c0c20201284500303d881000f1842d010014005410b24208040d0b22903a1a00300159841458a904503001c0048a1b40a43c1400008440003088000c1c0300c003084007005030611500b0f092411200c0c000701200313030700c051502e00740362800200101e8581500582594007c440040c144040f40302c0080c1c3e0000318080316011589601000094000d40d00c6a1802c641182024041584440d0b407071402680d10140d09501a04c2e62030804210102d01c5070007001d000d0b10490003802c3e0751040051803810031314168000c02c007200300c4407042001d140c0c100d41240d03440306040740c04c1040c03074140301e00140c41c7c85c0081c641450544502d015070701c10006402c0300181a01e005448004070011080104541500755020b00c4440c900e0500041110b440d5806c0615003041e00800d0260a125100001c039091841c0c1e06401d600092038401130203a0003060f204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 942587293 1250 942586043 942586061
    0xc0d1d0d0305041203051b0301080c041406010215091c0801180b090105010c06060e190b0a0302031510031a01060e03280804030b04050a030807080f220204110d 70
    0x40a01580c0f0f01911a141c1d418803618120080c1134881c000141004038803da26040e08080000864032541c4907100c603540e8401c090102405a860064500712061003a95010b205501c16402400019071026109803201c402801c03030030031449810b4802c04100d5040700100070405090303803048180e42c904840040d0041e15451041074251030504500c0c041d4440c4060f00f03056580a0a01d228031040f21700d40078005000c1544801c1a80c0ca00c80705124130145020000c170400d40c0e04020501c984c84030710341008172941280c8002940b65201e2010042daa220022070a5845084c010840710000d540b03480348a9403104588030b41440020100c01400620740140315041c401c0010703401080e50009442c11404405229113100d54107010f9044454200300c081c3c0c0c116400386034070007031003a0390341014038110b0b50740c0102100880214195100040c10340b0301c19101207228201c5890840c0654503005851114001940714003100020301c10362280140e19180111031100c885510040d40d1000e0140c420401c81b00950 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 942588543 1250 942587293 942587297
    0xe090a050403020d0804080c070b090f030609060402040b1c050303040201030509191b05040f090605010e040c091d011505010e03070e0c09030a150e0607031806050c0d1d0d 75
    0x40601c00400c1c1c0c009400907141d803890030480d190391541d04000c221070180ea01b5000280c45100804250303503118001408144600381e90020309020400c4c01c160711400c00b00c4100c4c406500c28400140946483d801403500080054820042c2403001891003a90031181441540d076a88000103100855a140c45001da01000344009401828604283d6001014918002500045400034005a642040c01d0340306c0080800600800441044013070060140a401c0f0040e10f45900e001d00014060b843e40503c581f0960b80f01c12f5007800c03d4182580346004040081140d82402904145403010324000d208145003c1c1b4160f07501c603d02031030300c000140032484200340d40b40240c0000408200c40b00603402d50365004800c07520a2516013410201092422500910142150459071032040c180c5c081a809080c024034001c00340c400c00c5d95808425019220700c044018007400d141088030000c84c800e45d0000d9008410713682c69a20f41081c0900700401d8408820f402110101021281448820b0800070b41204000318 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 942589793 1250 942588543 942588551
    0x31a0606070305161104060815090304150f02070302040c030e1c0203070204091a0708040b01050f210106030b0c1305032b090506040f050103181e11040203070e090a 72
    0x96400621078042c0f88040c83c040706080600388208a5030445c92550400081c000300541030365071a00e00c0d5240300c00c0e0300111603440030101007800c1030000300c101c4059840d6041c4140012042d50030444440202004840c00c6000d890f82c0030005940b5030203040400001c5030340c0401c845800700095400d0403e00c09001030200c083d003410608107500030060310030041c1c0481cae0014410301f00e41441ca42403c0c1d20f8036600d0340490740c10100000c00d17402c0381c507803402140109039900540c0c0c4c0304c00c10320000400d010b01c01c5030300c2a0101050904c00e01040c1d00c024030800228004504150f41340c0d40c8000c640c20030b40b28100a504042001c11307200c4215020304005080803002000383c0d4854a103108038081d1079401d08200317000411204003009004203040401420098005540c0700d507543c5080307440c440301c1c5c02440d00081c102100c00e5031000f09102c0700e062581e004dc042024020251042c070640560624040303c80f602c2a040d80c00c52646e5504c0514030035200350300c9041422a9220400036480001041408000d04d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 942591043 1250 942589793 942589807
    0x30510060609090b03161e0e090303060d0305090a09020415170105120a0b0a14090d1d030a060e0d20030f0d0b0405100f0603020408120d020c030301031a0606 69
    0x2000b40c4803400c594020b0400501c558624010a04003190403040d800444220140000d184003400320511000380d003240c180c81940d48800700c04c00101402e5404034840c0e8414400301d030749840c0405a22203114070a0500c24640312101022801c5401070740c1c00b00f004a43c3c04030b410403181c60108030841c5406860724084078080d0320f03d040c9418080041c01050b0080e1481070961910040070440340030f6164020740c0454661820210043c05407100c1918615070350051408a540310a0025010268800790b880784031000d90845041c103400c5603240185580352282809803000b09800c1d0bc59480c0400e85200070780f80581d403004010704005030030307044603490110708860102800da0100a84174a070f0319501005581d83c81034110400030344503810341c0c0c6500c18503280030b1189024040107440120381c42040314040b003070358480040e0200c0c052885441c8690300820404010100d0910080022500c0103100604104a01080c00e1840c0c0007608100c5d4070301da01000036503000d01c10b407400d698042011240c42c1c0ca000f80d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 942592293 1250 942591043 942591047
    0xc0203060a0b15072603040501060501050f160219060203121005010906110c090c070c15090909021c0b09060109060303050d0221100311030102090d080706060e0703060305100606 78
    0x4a000040c1150f050104001e03041000005d10780303400784004100d151808160005680151b8001d4804449562034600c0001c0c0c5c40d4001c0c815100842e082e600c1682c282103c1001c1d1405482c110317079003242c0c000c0751038910502c00413075801c03000045e010f141e0042d511070300440d062404002c40501845503128100004001983e03001c0002c00659409140003800d0076545100700c1d2400c1800c0114a5228950104101000303140e0b0010300381113030048119a202c25079407840c582040382d08001c038070002070342c0403002d001041d450b4000350402440036040c1c04030303901c0350b504400c3d5440340c407207003226118055818000c0241041042d54050f00f49a0300c2049000c0c03440d60040c145200740e1a001004035000300b03d44400c4583c1a000605d030300c1c0c801503004c1040c9498204403441c0c0505000490f44245030810004903401c051080d110800d00203004111001c03e00e44501c1003980050740e0884200c0d072142408514003070b1000000d402254140c802155046c19898414203080340150352109191910100b04000b607 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 942593543 1250 942592293 942592309
    0x20c0114090606130e1207120801061d010e090405030405011806090303120e07080d14090a091e02070c0f050910090b01050c01050103110a05030d1d01050909070c0203060a0b 76
    0xc0c0490308130301000c07440d407040340241540c0c256000e0103003e11046103188031603040050040764450700140c10601000e40058070a103800380601c00c001030f503c1801c001038805030700503620204414103100c12050300c001c0010b8040c920842d4201c0c0c10741c03c0450100031a5801c0b01c02c80f504240b800d85851011410610000c1a00c00c8600c07011f0104040404401c1c4a43c0340b42d40300b00c202448003006d854445840b03684039555598460910000604002040e80031489045e0070381d04203002c000c1c0100406841c1c40000760180075004902c1242481d02c00c0018001445440204000340c03140400030b444030b01d0101940d11038000c642c0543c0c0203810300000c0282c08108418404181c034032540c000a404420040101c406010f403840d40f15080d80b8041c004024017607080b42500041d107088540c0040300b5100c0080c1900d50b0b03030001040000c1416034072110078440d000e040b444100c100600d80b1504012a2200140000c0030650b40c0700003007055108400c041d030500f809542ea1041e8140000d004102c1c03880046242c2e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 942594793 1250 942593543 942593551
    0x6040f02040510050612071107050a0e071416110405070e011119033930081b130311040e07151b020627030f01020c01140906 55
    0x40e50b81e50000034040343c06116058003421000d44150307203500440042940d2002c0960b554404650b90b0425103038100e000080c980241d800151403540000d00e4004000071441d0301030320311400e02c50b00d1040507040741d507804064005880e14900005540141d82414141c003442c000c50980900d0a04041040041c3c20458a490400007880e052a985002c11104c9080a41c1800c20704074104503440018141070380040d0328038001c44c1440900070143c40000b04204105002d1480c0301c0f01c01407404590740441d69490094240d640480003c4108404000000e8000803141040b0340200c2c9543c0107105c0038000c6007100c41441140ea01d129880c10300e06418000884046100081c10041800345904040e00d95411200c0d14024010450b8200c03611001442c08440b00e0501c03010000d840f58192004502911505504007600030780326a1505d0701014880000003c18140850005560340045005407030401c14a00104036600c00180c40d4070003410b060782034961a054a08170030140301d040c040b49030404103c00707800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 942596043 1250 942594793 942594799
    0x2091c0212030c0c15070201140a09050a0b040e1810021b010c020a021504061403060f0d0c18090b01090509070807031208010819030f020a0b011d0906040f02 69
    0x150000c0c03000072440c4001580301c046901000c511450340000000c1d851680400032240d9900c040b85c00a4104210b008080f030190021310440600b40e400618100200700d039a807140780c1030346d01070303103500220b1072954081d03010700000c0d880018100a02c0c5150862030b074001203607008601800c44080d13800d507590806610254180c0d0350010b00d0900b204801202c0404050f42070009000030884138078040c0d11500c0d60750041c1d00466034810b840c02c51240d12001ca80c290740d90f503115149440c107494001600d940004011070303004030290194400c0355983e99010f200c0e8506c078103801c258682c2400d00c59008400400040c0140c0d608200192000a80e00321290b41941c3c1e500300f00141039585c01d2852450400b06500c5058039002d1040080306104083e180c6020180e62508c0c1c00e0010307681e0341c1081d981c1e00c0300c00010741190b4544034261300010384180003a51411069204070384d48800251264580303080e0070b0748405203595060400744804000314140d06c0e0701c2404c400c00350101e841c10b0345400c510800030a000a00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 942597293 1250 942596043 942596089
    0xf230a020906010c1403090117390c06070e101d04020418050f060a031e05100f1b03153809031506060f07140307030f0f030209 56
    0xe0f640b09000c00485a0341101440c080508003061a6803280d102489541c001404201342070301d000c1c200c000c1140100d1610000c900c101c41072000c2c0c00300941d4100286080e03a0000e060655841201e00040c00d110701c101c6014261034144550007900440c00020740c0ba0040c0c034107040340400d81e80c05c000080f040e10340400c0400c92007130304040001c0082c41660410f442901200c649069001c03803a511041c03003403d5a40300c5070303010b03101e5400300800041c191000815504542c0c06c084811458403508000d0740b0302c660225200241d4412081003500c5690240c107885541d550071422070090240900060f02c4840c3c14100103071090341c40c807264046030728015050194094454010140f40200030fa001c0c4043c00145402d404442d844c400340c0e582d01c0901c03600c0c443e10503581c0540170003a44960450040c2802003503680341498414400c4a00e4200c0001540c8040080420400f8840b0510043c044103119641d41032444541d508040c041803240700a8000301481842078042c0c64a0380b48600169000b401c43c084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 942598543 1250 942597293 942597301
    0x10c02120a1107030606150813080a120b1309020108160503070f050d06090902240a1404030b010e1b09011202070203100f050a0e030327070807030f230a0209 69
    0x64074140b0558001000d03607207006c43c000b41e40644020b9148880c50309644507605503d034030686c1ca03140d000910014001c0c4000300401d403c80390007400300301c02078290a600421a107944600041315079502c41d00c644074035038403401c14908640c0d101e01020390004219008070500121943c000b0810b000003020707a028496140c160144e0180600107a031000060004184401d40c0c440b0a80c601600c040c0320100e00908603110070700c0c208583d080e050340500d000c03031000c1402c0820800e000c03500c1203aa07a16003001c25900300f1020000c1103102454038041d0402080d58203103030410a10014150382a941019422441808601d860745c5c1e00a564030b0b00103401070300140e105d07101400003d0030503448020388a2258901601c1d02c0b07141c1d4454214a1003840c008034104450114450004d80742c1c0300444006807104030507550b940340862442840c46c0030058610032550565100e074240c81c0b51807450b030820f6a46a52061050341082003c12100d681134100c0e01a140e0400341d0400002d42d03400d000c0d44020312a4039110002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 942599793 1250 942598543 942598577
    0x302010e01110609030405360705070b010e0403080705190807110105070c050708010e030d020f040f03061b0c030c06050c31140105071202010209180702010c02120a 72
    0x2044444902c442919850b050081d0220f5a0f07500501c11540a0030341d8110020220340d106504061410500300e940d03541d501c48441031754982c0401403041c0c0910105101c080c001c80d0308a070142c2e01800d2160414011030a02d801e025007451001031801040000070007040090f601c048100010628190606140a448400080e07a09501140008442e580b9200130000840d0f030000c00c040c240f0340140299480c441d2a2290682610182900d02c8440d61081102d80c4c020341c4281c3c01003040030b45044a06040944810000d210440e40f5413040e5099900c0300f0301a080c942d500810040c1402040c1408090100d032594054a042c080042c007401069030b0790001101e0100c10b2003107901000d4142c80c040315101070010350b8080d003042c41c0440b200424140c0c00c08034200210340404d00043d08140c6038607013071032901c0d504c0d42c440d880b407940c1100071950207004a0fa0191581c49407103810306605401c081c42842c04e0704000f030031200c800050038115400306444002080801c0111a200002850580c418036150051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 942601043 1250 942599793 942599807
    0x30803040320060709090515060904020d020403032003041508040302160b22060813050f0a2009011a1b032d030403051204061e0b0111010e070302010e01 67
    0x288030b010000d14046078014800120f44207110701ca40ba124501a243c840001104071081150f0b0188400c04550392403215250800143c4501c000c014000361402291340300540c1a60030030f13071088000c60041c080c1d51542211050105c00c440141200850419150400035001e04213030140300c01c1030106c2c04001c902418801d01a00e1190b80c500340754852002d40d10300d0301d402e15030b105105070381e060483c4800702c148001394404003000301c0d110f550b1842c0c000e40b260701c54001d056070542400c88080c0b007081c0504901e9407052103008070003401002880d07610580c00440c001ca2042000f0720318800d1501d580103000001d6181c7c1508100500703454039684840180f0480c030f02c01c1c900c64041010610020501c0c49404c0b003450b440c0c3e1150810000300403d80800c40b010006240000d40c1c0040100d002400b60442e82010100d801c3d138028003410011840c0c0144c5c1401038440c0400740f00e118000c9481b0101c040c0030303503041640c4e05c040e100c00f03030020800f150407410f40b02e4039000f4a02000f4100700e00c1d003440314203d03807003400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 942602293 1250 942601043 942601067
    0xd0e040b010c0c03050c030c0406080d0f120501180c030e0a0b06040204030606030b09010c020d0e0907050f0304050714010207030201050f0d2c01060e06030a12030f090b06090f060a0308030403 84
    0xa0300510f203441c3d081c19507650004201d0305220744540c0e80004840d040a002c0c0700101c1d6204802041e000d901d03400280c80788018080e82d10100718846800180103203107030040b58020700c07440d105200c4004558000205a130030480d1402c00b41400c0240b0b0681d03c4200042d618007154001500e01d10545907800020045e10031a800a00b005040400100500c1132035844c842c000c40d005002000802c51580c420b070b848156a504581c0421750301021800c0a04240d10315503800308040c640a454205c1070900c0c1841e03500152820b4942e58400042444601e600d0703090703961480424001041110300d140d00003007844c4503030807411400c0b040c0460400d1010200d81c00c04a0a070412542100d03210940c42c0550f610703403400301c2d0050040d40c00c0045c002804a10140c5a500841c0702401408001c003503030f210a40c1c00b05412458104060303498800640100d10fa101d807101031031003034230200c00720304000081041900c005040c4009429002080c400303160744009501045a600c0003160781c0300e98403800c2c2a02d2001a0364 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 942603543 1250 942602293 942602303
    0xf01030c06032a1b05061009060f09020c0c090403051902030316030213050a061101050a18020904050f03130e10050a12170706090317241302040816080d0e040b010c 72
    0x40884e0041140100f9001c1c0704442e01024a00010750f90304000058074505e20404841808242080c441e0885940007020102d0754a02200c0c8914101804249003404c1118287d002601c0031560781440d5141c0c1c12003811821251004508508122100b205c19050544001040c141e0009803041d410210008880c002d080c004c0a04c581303c1c0e034401c0b0150045000c03d00e01c0d00c141d413a060004080c11707000e100d00b41421214030000e141d107650507030030b01580884c003a00903030b130f140320301c0540481c0c004080009003c1c910750305464400d21440c0801c07001d140c00c40544417044034240c170f00d82800161903a81d00d40c070032617804480c128161160b60070941100724110540700090b00c800207515081c4180c40d00224016482035031540000001c0c1203090440042c02e0386c41010440760240d00790f04141c015004240c1d00a002040c0301b00c2002030a0014040342d02c154000c880e190403c2000782540b18004280a0003081c6110207400900c1c91f1040050404000c160030500c01d41c0d0b00c80000101d40d1244060709a02c590007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 942604793 1250 942603543 942603587
    0x4090228030813050a0b12010501051c06150f1103030a0207031704030e01120c0e040f0f09120206090d08040303050c1b060604150e0112020303120f01030c06032a 71
    0x80314100450054501444d40503030b80d054400501c2c4608070048450300302c2207400501d174513400c3c03000440e0550b100800d1110308020080c40301e006408281315903001459480208000c91201103400360482d00078428620a10404c40c2101c0d1144001004036580441503140050380da080516068510445120031403072198044020002010f070070141003a080312003621561031a08414286c0d10503034241422a600054001051109604046d0410300300a0081100420100025217103202150b0000100b075844031941c07801d0704001a01407122540103141c01c0e003c2c00308084000301c042d182da100034100404042e83c882c0003400c030705100402e4455140303208950b842c1e03010104140ca030f40c8a0041c0c0d0614481d0b8981182c440c0b0410001c400081200c0e504568041c447c0c0c60f003440356a0301201c1c59800e0381c142c08200856061150340960103445490700c00c100e04180e505504040100b0310706a08003209161509585e10407599030050200c05100700246040c000040c690001c0382d02c40d0412207208246440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 942606043 1250 942604793 942604807
    0x180709030203060f0c0d0e010f2901020609151e07120c020f0c0112021204080a1d091609080f0d021c080609070c120518040902280308 59
    0x121124010459008a0460b03510743c980c0c5010b21000042501e01107000f00007002226400c1449401202a5881401c00010040201d6400405440c1d0708199081742c0860546906401c92250740c203607503280b400784000d00952801da04c1096030b0744403055504050140841c0003480103113042c000207035a82e00c6422020302500703140b038010307000b4143d245004407600d00700405501c00c0c070320000f000445100c002004000c0032411500645095114550005c601e07a001c1200c4000c484c81e0040440c001c0d4071800c081070323507510541801050783c40640000b803655504150006100da6600e0070140c0c005015802c0c0704880030b8851001d0b941e0070226401140d240c0154601c1400d11034012070308034003124494003580d8904884041d2082c40c0580060b0100100d1011808940a0b0a1513910641d1103074050501400813071041d158158404600c1825200050f00000d1295004e079540411003009002a1414086101d15500007406059403002c030010030751074503e005980c1404a4203480c000c40d04080708644d9245 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 942607293 1250 942606043 942606047
    0x3010302120705032a01021204180b270702010b2202090d1b0f050904080a0c0c08070f090203040b070806010e191e031a0408040e07020a29151807 64
    0x5a185c031100c082d2040300710113000c55400460058882c0008080c0d0f5454513003070035502c8290380201c080d140242c982e6494041c405440f03003944804800c211840c4824105414079550085a000402080c11a41462603031000c640f60642062240e40001c403820110035051000b178402800f41d100441d80c49101c8400c01c0b02801000400560b51800000058098075250115003401415500c592074001002000040201d0750001c0505800c2440d403420b85031080b4191691500c0346c80b175411a08080c0c0003160300b002400ca854150000415a084080d8210300c0c15890380940103200030070807414090b000000507480e070b01c589524140103200401d841d0520000000564640240d0b01600c194060b1125000c41c18400d186011130403254443d050010501e840c4409170600030700076008498a00d0144008110081221801441801540d005112882003424440310740103101500382043d42d009003480050440740c62040d81c1c01641a104820100c072182c0100329880f004406580c10b94140e40c0500803043d0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 942608543 1250 942607293 942607333
    0xf030a0e010501050d051002070f080a021f061202130b120307020a0509040c030f1106040e07021002090105042705040b010e1e0f0402010c0507270606050301030212070503 75
    0x400404000c006684c2c980b8103000000c0e0540380d01070003d40c0036010040806c840c85c0c000300600f500c15940d43d0003842659840e0001500204000c01c00b40e000301e40300e0b20031003904400c02d11240403408002d0100ba0710b4a075113050100350ba10030180c040d05d0f80091862924031160080c58035500080c107403140e2070185500705916500304000480c4030340d40d8410300180714600f1400ba00d000d203810404002c140d07440d566038020220400350707045421035500504a0559900c100251000300b40098409400346043c1a00034100542000b02da041035105114010242c0d074020300f99003e85260310381d8203903018540020234001071010411080c0e81400c0108001c1085141504141203400e54882c001850b2120480c9034541002c00b0340141c80d141c20710002641c8203120400e07003074000d80181084002c4603140e883e040e0501c1c20f650408103606031a140f1212600c0040120700c28103034000101040701707504020004141e44810b210180c0300e088024010300b40350005200880050900404440040810280d000d000c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 942609793 1250 942608543 942608561
    0x503030a1106101406030403110d051809010b032202030f0d0f090b0a0c0f050d0e030c0108090309060304080f1602090c090904080c01020706060b2a10110f030a 70
    0xe4002c8001142e4580140c00904080e9500701110b12241c0095000740112038000900640400c0400c1a42c840345500034451720078501601e90f122983c500102e0703400300b00c4072150100d03180503070780540041200d0110384003a240c100c814126445503180200090795070b0607040c0c040180d0f2600030490410602140003481c200c0e403c1e4107444984280800c040305031991b842901c1101e1008400300011001c0c144115031440e4031912456501414107440d444c2c1038a0465100300c100046045e09405440c0da1070304204155203140b0034a0540c1701840d00c2a5066203a016100c0618055400400882e00300b00004094590007424040515141c010387c15285441d41c800031800c2e4020a00580426012120717501243c00c40c030360140000321a81c6596407440c51640c0950380c23051282d50f00f4441f010019100303001c2d00000700b03c1c01d070b0300d81c7c0c0364019002c07030050481140c0c000803004405000003000c2d000300410303034811024482e9000100d42e110481c1001c9948145441c3e041e400da400010445000407640c0b0001d21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 942611043 1250 942609793 942609827
    0x200f040f0501110309040b130f0515040216020d1a07051207050f030609040318090b0301050a051b03040f141b03030a020a08030402030f032106010e0f04020a090503030a 74
    0x110340e940015200b010f48411010341e29001040207000702d0030f040d0002c21f00044013400c800c45541d0b030f03a0b0b00c4900700c41c01c0441d40f2018a44032030074084006915001020b011f14101d608514203011815251114011078500a00a010341c0800c1000e0004250700d8100d42c441c003507a034140d0391501d000002c003143e1045554850700c1d41d006e000700e1031152140e4241d62403c90017050692460311180c0c1041803d845c003c00131020860701d418140c200000c2a58414000c0c000854003041d00103a4008040c250355005000c140d420b4600010800c001481200b650422a80303003034102e40d01c1d200c03400e0103001c800c41c0c1200a0062001100061941b00000650040c01007003c0c0381c0e541c070f4200304401c05482c4d1103040c15030341c0103038084001e030070225403148000c2d074002c0d10040c122004523942c0c0c00030500b160000c20488403000703c44e05010100c040009a11548240246481e01019091000040c40c0140c0d0542e4203006950104000410b2030182c010f00010740001021070f52501e40c101c070300501351544401c0c1807107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 942612293 1250 942611043 942611069
    0x5012307050115030b2a1821060c0c07270c09060206100f05120c12060709140a09020702040e06160216051f021009082106090406200f04 60
    0x11401808101a403030302d042c6c0c1c0241c662a52484d1314241c0032504501e20180c2044c0346ca6101e01d045694140050f4022601200e0f6407071182c21340c00200341800402030103107501c2c2000f040381c10905080843c43d1001c1e244642c01568a0008402c1d00a03d1f2150440d1011050380c44c01c4180000950007420a0044030110340c225611640e8072032a10700e00014920592a2041400c4401d000905e4042c150003030070400c4008990078a10034600107020380d001310200080700e41210050203107580c0e024105601901c5403140030609051024080750801c0390b05e2241c84840d0b40e010951501715540c075001740d07c00c1e404203421522581030a0780e03440c100c176419128500c0944546000b035054895100e42400c00c4880052520940b01803401120715019100031450045004600c030500f9642c1d070520400038254015002c154980d001c210342c4003d5180100d00d0340f031a00c1e403210104803440d43d07101d481c1c80d40b042d0720210200350030f1075104c041c0c0c0111582615500b40302102042428070248150042d000301d849051b1041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 942613543 1250 942612293 942612301
    0xf08070605071805091902040e070e030d0905040f09020405330a0b070203031e07020301060b25020f0d0302030904150612051b030403030b010e0a05012307050115030b 73
    0x6240c200f076080c0c3c1015060390000003000103103480b18080b64404402030b12900124803003480c501c100e038055000820001803074024001029800600d800b44600107030014144a849020060080001031045070b1250ba11800d1510040343c003038204130385956000d0030911140c1042c1051410b02c080d105148845012891848200c6244d08042095a80f03000742a0200f00d50400440210781d80c8440c806a8040c1305c00c108140d001a175600c1000340c00c40d0604007203030702d0b0059403041500391003040c0d1044051580620001108400c0860b002c01c10003015143e400158040b0301c00300c1e03058400a120a0f0f0300c1156400621f01b0b15401100400c1030880440702041200704500c024169101c003030081c14009230003124135180e0340300a41d025680002c10070500c81c000080600c10800c20750710450341100001d44802c1400c8070b5581200480c04250403c5420890769414000020000c0c1004040f54049000c181c5405180050800486900942210080c458007400e10304802c3ea4080da444100d850000000000b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 942614793 1250 942613543 942613547
    0x303240a030308190626010209270a110906070303150f2123030409050705070302061e1b090316030b070809120a1b0308070e01110d0810030f0807060507 67
    0x180c01591b4015113040709003109100c251155010308890003040c0d40d820007a400c8c8a646003680788480740e07241d1507840703e40450000d40c0d411016018264038800340c206111404080000020395000b1102920410380f00c1c3d101d41001c401510304d018451081304420b010210703090150600000540b110407054514990949065507491841d2003005008041d44031926019090300d54248419100e0920849040546417448030040310801d41e0520080b542c0000c40f40101501030150303541c4920140c6454803d0b0708079400001c54580001c00103058822081420b06889144509036454002d014040f10000010310800d6410700b00e43d40000c1c0c964205500005404900c6403041501c15201d007406407038840c503104045001600030045001c284507400d10018011001c001030741048a00479660007100c0e042410300680450081d000760780c100021018045081000002c1101ea02c455070325001000350742e118000e13aa4850681c00013080c00c0c182c141038109100000780034180c032030b0081c1d0b0f017000706032168001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 942616043 1250 942614793 942614801
    0x131a06070b0105060319023915060109030501050a0605030c0a08030a0302090f030d0f0809160e041b12030f0c02010813060e03131403030c0303240a03030819 69
    0x8010a0741d1000c4005010b90f0400720051034021196144034400c80c022203034000c003641c219030140a45103503450008550113580b1124070003a50b40c1c4d0448ea448030185800c4507501c49211490302104a0300340008034420340d22400d1004011a0010000c00550501900c01c501410541c07044500c24407500030b1202442c0307003c080001c21240004000d510308119908107a000c1d410000c4419403048956411594545043c44005101a00b0303036110322400d42c141c2c0d409090414040d142184a40c0200142100004121500001d56280c483c0c0300121750351754a8104036041c01ca9100701e00114444800080c3c82d2040403104030064030a0b184e02a0440400304100c5845041d00070281c006400c11000c00c4810201c482c10f0103c02e40902408111200f441d507010740b95a10be4a901003840800b503408200c42c00c414801c0c2c28400b034003240514504080500125a00d00000c0d1100c29004903d5079205c9054040d60700780f9106800203020b01c440c040d5030b803c018258000441e9a25482d8203007045203560395846200d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 942617293 1250 942616043 942616057
    0x110c01030c1e09031a04021509030a1403040f060804050114100b0703020120250f02090907030c090903030c020109080a0525240b012c131a06 62
    0x3a0345070009842500c002c0300c1c455195034a006120503180040040740d605021000e0b41007215945c550b080c20f10b031040c0705015088041a10406009008030303200c40c4d034003140c0c0c01c04061b000011707010031a003550b90945c02c5100320380c07040caa480e03440c200c0021081d0700318a50600c214018002007201032158000c10b2058041160910410881c41e1028440038101c2c001610046001e40b00010b0302d00001b49111586000b030711550410b0300000b08001100315002851503e0102031a0710a40c209090f5541e6600780e4a20808000e100d00d21000005518050821950300116002030f041c03210b0701d669020400051041010542c0003a0411082e0f5a134213005000312540c40342e101011515110001004440e65000042502d0300d800c094042c0c0d038400355070103211000040c000c11007017045010300350300305440741c0202c0400c0f510755042441c07414807682c000c0c90840506a44400b4045880041c0701d01150b14039038100b2050780303c605400103a00d0301ca0680c0c0300e011411284582106c02444d40d00c00c0040900440e5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 942618543 1250 942617293 942617297
    0x8271c2f0d110705010c0f060e030414030708100902060708033103020a031d0a2309070c110103020403051603030807020a0b0a0b0f030a290618061203040303110c01030c 74
    0x7400801a6521800384290100c0c080c1b41e940c42e1008090340c230302c0300b038880d070090b075005542c40864103005520b800003007641c1001d000c400400481e46003505480c0c48840f0003143c081000c3c0e907000140c096445090494103a00c3c1d002d880d0300d0b900d04d4a01c2d1100400c000d80d09a011024480c402d510032021461003034040c449416400602d010503051384d04880300c41e614074050414680e900c49425043d01c5560204d0054a110038540c5840100c050110181d5028000e01500c104400e6050190164000b801c030020546c010304106030303ca56071401a0081d12680c0d00003042e03480303a200c08150074124500840141ca11943d1441d03040d840b11281242e86150711640900301042c84008180040020342c0101c0049a02402c5940b801400c0f01c0043d0801c4290042a01d4101d07039039002094110140303003c48003817180d1641000040c1025008985000b0f0740880704140700030f0140c08116540c0e074440c0315000803c0c2850440756a99202e140042032020040000744051094001c000050b6002e8092040409095 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 942619793 1250 942618543 942618553
    0x1d07030f05131704090908070210020102090123070f0303021b0714040e01060317032a090d02040b1207080f0f0309090411040c08271c2f0d11 62
    0x7644840400010100100e800f0710300803c0300041c0c2c0e130028000c00f404140510180e684a502c14014040700d070100746070b16030469104100001e40d607070304891052099507612249822100340c40c0e4545003940314032070f4007501c54101d8200c00401c0590640040100c0d250001000c0d5003a00300c0c050950342ca00f4207010702d210b008400100301040d400c040d84006144812800003140caa5a2074540450000080301c211403103200000030030881c40c00ca00b0f0300303004014144400c040541500100c40030540104803440c1e200392864a1410103659454000c030a11b4a0300901b031441c1c607801130400310b07070715401031180e0465030007400700d0031114040c0400c944807445010400356107400e00386010001d4a28005200300d81d001240740320005203485910a151000c41e2075250b10070b0078201404c01d00c07a06000701d140031002e06a1419031003507480c0089120703d03c4504032442c0d10042c0030660030035544400304000035078002040207107191111503046d0240c00200c241405544480c1070706802141c1e4910043c03920041507000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 942621043 1250 942619793 942619831
    0x110910030b0a14101508072312150109061103030a020309101109031b0d11011403070507021503040312020c0a0204090c03060506060f0301030f060b100306060e04020a02251d07030f05 80
    0x41c0050750360501c01e00307907034032032409c0c800a515580289056480c00c7d50f40e40c14500c2c046e280e58001703190b1000340c6640d0620f01c0c04541e080c0ba250340e8034440245210080c070380110101d11001420081c0d1204191403120a03c160000d8210300c000c280c1100700c81078031a104111000400303803907a11190102c150050034100b1150344030303180c00030b046000c08070070340c1000300176110b2444907100d000c040d5025440703961764190745000c280100300000c030580e18264503040040084c48002904150300f1344050100c0313503000d80c0f0340094003141070401180c150041c0d0480d081021034020000300101c0300d42524841c400400282e02d80006110345030056a00b180c5000c0c10400050020498403d61007900d5072083e8400301d81503001c1c40210700b1405161104401003600c4960510600303401c04043c03041490207032404c40c00c00c10b1180000390b0700c11010310682091104603608000d400004a00c202c081c1644162104090f0845001400580e0302240c40100203461305050610080080c0503260103051002801300d00c81c15 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 942622293 1250 942621043 942621077
    0xa090b03190c0e0c030603070b0301140132070b1302180a0609020712033b1213080105070c08070b100305010513110910030b0a1410150807 61
    0x1030040940b640c1e441d20303600040100351049400e100701d1540702500d03120306090045c1817501806411000c2c040b5002c0c0014401405680b80400202c002480c113003801010810500300c0d00c2022034130350480c4182680380f02140782021030051414a01c2404410455610340081481d00e00101c10004c2d4041c0180158100c42d070700b10f21425800080d070060015499640d40b071618100d0344541011500a0b4030341480280240c0c051051580e218031207038841c0813502c004042c00c114254009180041a19000e2031900f201c0c01c10440183c681c410520980c0c0d50f05541c20044138030000318411100a50b00780300005594034811841340342010b62001807981045070039511100301101c000d0500010004507600000441c000740281d90095070b012001c886402510f08028480508030340c161401a0504810310030011041e440b0442200d4111171482c0c610b0307c1d15070000011300100c51039031105106840038003905038602c0c0c4c1e800c0f00b1100c1780e014203081842a0041034074100c00c121012000b040c04200000001c3c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 942623543 1250 942622293 942622333
    0x70c2d0c081c050c0f01050411040e01090c0b13031502040305070f03030206010303030e2a10031103040f051048050f0405060c060f0108070f050f0a0e0f04020a090b03 73
    0x20f5040170356680c01091107056085403003c48041c5d0b070700e5005024100d0350b400c00d0300c94100080303070307510080c044d071039050700c40108141c181c0c803401e2101c1000140c4405805c0f10204031070007540e84403541c955001100c0101038040e40042c041500c0c207010b00c00000a5609105055104481e45034001d013100d0380c030b1505c0c140e0080c22620200d08a07401100702800f89500c61003140310120724402e440900544c4280203002ca100180a42e450605113420030044001c61001c0c01e032540075900000440c41207881e031808a050008400440200c5402c140c941d9a0301b544503840010780301d0584080d400142d241e0404000441800009a80c0d0240f84000010360f261041008295005000c0782d46840d0a5450022944c41c0e4402c400d9542c0c540c204030107000450051201a43c0108030941c0209041400c1200702c8000ca00c9500c80c0301d1085e0031641c9594525151032081c1c900404c03c00d10001c205143c109031320003000c041103404a10a0b0719602e008244444603204803d07000102400030074035100350140100c07001b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 942624793 1250 942623543 942623557
    0x313020409031b03031d0304060c0b0714041202042007060e030f13090f0b060a230301080d27060516050f0d031103010608070c2d0c081c05 61
    0x300003420101c00c02c60101640014140c405d660018820318003000405010300e00f042c10203d00e4204000400446901c07078220b121315a00001e01002e1611810020b94445058031091900c441c800718002442039411140c000d030700c90080e1418000303410b81c0490402c4032500038a410005070400d000c1d44000c0750075035114a40d0340c0300c000d0403286054802820391040d5007107442c05440840d60800103001c2002c0d91301403002141c030441001e1200341d20500018016008800c019000c00001c0341091403c41103075500301c0640e2014814079580d80d611034aa00d034075000384940a0f00420615640004120304003c826880008503031b20400200e8203150b01210154861209001740c860134101c07880c040b550601c01294036002000041c014061180d10180030740d42d0b400300c80c4401980030f00c0100700320760f0849000e43e4003500f2403070a1051401e003890007040c0b006450290090800030140407000791000b041a1a820318060810780d0040b603520081960782d141c041070100654842045a95000d50141e0701030804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 942625899 1106 942624793 942624797
    0x30c0702040e0a0f170702190302041d030405010f030e03130305150415020a051b2113050111070e0f070305160804030f0201061a180303031302040903 66
    0x11000c4c1c8450207000382c0410049841154413035012150104d40c02880302d00110503041c0107030407c0c2241c2c00b0882c0141d1415803080b0024120615281900010400442ca81400c4c100110b603100015104181070503142c140c038485081d01400500080c03078031255070310400c0346035082880c41d04c01032403504040b8604541c2800042484041e402440440054025946980d042411900740c441c1038140951168010a480300204010408062040c590012414104103d100901442c840d001400c00c1c003a00c038000c1008154015050038580c0854042950b003450b5982441c00d802e080c3c2180c00340b01c440000ea08100c11181c03d0702c20359400120040000c521101916800791090102900140c144001c507078400080c0c6100350801005086a580302404455a041400704280c00c61411342c00e40300c1c11440c0b80185030070004152072295046000b21005880c25800b4080244030304041501 = true := by decide +kernel

theorem cover : BRFrame.Cov 942446043 942625899 := by
  have h0 := BRFrame.cov_init 942446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 942446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 942446043 ≤ n) (h2 : n < 942625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
