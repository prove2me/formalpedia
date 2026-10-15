-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5519
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:07:49.50385+00:00
-- url     : https://prove2.me/submissions/6bd09daa-30a0-450c-9280-817979c8b5d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 992446043 ≤ n < 992625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 992447293 1250 992446043 992446087
    0x15030303061c2405011a0307020705010f18080609010501170a0221060a05060910240c020319030e010815010e0111010606031a040605090103080306030703060903050d1d03 75
    0x42030740780040308420389501030602c1d90901410741e030303c2005000c80501c00b1040d607811b00b1240021800c43c5480b480080d40c4000034000c890400c000407a141c9060f900461061481d140d2207811103540c00d4840d00c0d80c40d42c55204444442e80b1358206000051400c5000d00d070496100743e80f0001e003001c52b00c50f809005551b03050034900c1c0114044a003200e4501002404468003803031840202085d40e04000c0c3c100456020003600c0c2c1d15030f103403005404100c03030744032100c0f2412010070481d400010411303000c0d410340d82903240c10b070040d416000b46640340e15040785c04010300340c1207846519041e80d0040c0c041c0046580300000c82d030311000c4101c84010f544c5198081c90703e002d601c0c0f1052502c1105c015442e0150ba00751405030340300c2e4000c00d4031422a0514010004c007418140c003c01c1e101001b26916000000e1030b06172061001a00302000040411300c0c82e1003d0083d14013464200b9001c3c8020785aa1400400d1680035003818100c0c6403500c100c1c21020201805462009031030f100054ac28042001951060304204035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 992448543 1250 992447293 992447303
    0xa03080f07050309060705160b0901020312101a040906230d0f050708160806070e1c020301020711090a060e06040b030a020d081b060105060a1103090a0e15030303061c 73
    0xb200c104000d075117105c010300c5101d2180d0094900e00c20f880e04420404032040d08005000e020510031408c1a981c00800ea0348000621003203551540c4400002c0e40c100121504480d40341600003030143d0303c61030305400070000c4848a0304201310341990786040d44c2c41c090f09a1540d07410981404030000051402c400d84030465030060324602c015420f0381d99460300d844502d031311401c055000b280700500c1d51440400c07110700030660440904218039150b840207240e00c2e40050414801d0140284920f0108102041801d1803030f400b034004c43d5100107a040c001910000c4084141c0f182034280c0000e80001d0300c2e40180c904503803d40c2405541911050708010241511108980d010301c0ba0903000340259072240740e40c45a00e40248001c680e68170750307400710040c0d080e15900c0384141940030f50010003440c1c84000464010050510301030740c4d075011000d04c55045100310391141d40e112000000100d150000e4520440c01001000011285d148060381855200e010413207075035600140e03002c0050121039008895020640c410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 992449793 1250 992448543 992448547
    0x207050603220b0105130b030c01141e130501030c0f08060f0a120506060109140d0204090b09010516030903050f090a05060304030e04050f13020d060f0c050d06050a03080f070503 78
    0x10400007034440706003019204255080f0040040303040a00050b00342c03a4000c03000744a0070740000c010941e40c1218003525810450302c13004500c52b20589005851a420b4a2084030700d00903071454505441b81c1040007861001d04140340006415800b9205c0c11004c1c0440703071100324030f19040c1c080981352180e000301140d0300311140c0c040f11842a070f0740e941d0b41400b418400001803800c3d070680c2402c51402100500050500c95121018056150060300c0000c41000c1101c51608a621a20200d0003404810000a107098030301000d01c07a9940043d00038611409402c542045e8803071010a01720280c4480450140c049101001085003050104005120103074000e4542c2c00349658944c08200194000c803019030001c0c205140a05691809000380c90b003000040c00c5090311303070410027520108000b07002d000074482d000032980c035020402e1540007054500a0303480c0400c01039020a4000d40301f5803000e0482c18034a49008000300c0c00b40f92008451040e02d0f0802d5070941000120703d1205000d500c029004ea65078402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 992451043 1250 992449793 992449831
    0x8151f0504180e01051f0b030601030f0203040f02090603070612020d150b0d180b070309050f2d12071401020d0903031a0a060525050a080319020301060207050603 71
    0x2d141c2000b42c5094032114009040c0c12000d001d203085942c0680345203480a403420b100d5482580d80141c000c1901c5003040075603070700e44074200182c00038840000c1a10205001104000500000505240505000f030740d40742295940c2a04042c0c0311022401610301017079009a100e07284000c03940c0a8031180401d07210014070448a940000d0355000150b100b61110070300094641d80140480c050a1442c0c00c0c18030311850740001c2d80c0d80728011808010501000c0603034484151090000c100b01001000c903036030054642035070341007540490708007001e0260000d110640c18005024040007034181d0840000a04803410a406a079440107085984da03c03082c00780d902071058504a50b000e219000d07070309102c0e40340011204900e203644814200381c0c51740c01d4420355003000c1c20404203411004542c07060b402d89482085181078840c1c0f451810304014409403040c450302d00d10204100346500210f00654012451541000661710329400360b200c01d0040100680240c0010042c40c1844c1c000f654101240b95804880480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 992452293 1250 992451043 992451059
    0x360c2b0c12080a090b070302031c0f050709080f0c090f04080d020f0301050406060e0901090b060403050613060b031227030316020f06180d0606150c0308151f0504 71
    0x800400103890200b00066078100b015040221072004020144810341010706644001e5200e018021400303402d500b0b1982042c5003070038558040407401515140401050409030002410a210b60290f122144240c4000780a40c040005080d0040340004080c644580c1c1e0f00740729401103c8000d0011541d500d01803010b50241102d42c009495414074910166403298074007810401500c03c00d901500500082440c801c0041d103c1c800c1441c103440300c020003c50490304070000b18209100d59070024100c3d004507414040c0340d05c0751840c11200d190140c0c2c005e01070004100b0806843c0e110440d0904140f007010420390902c2d000484e072100e032040351401902e4090405501080c00e540c41649174500c10109161a88111f191115103040c2014090700c2840c1060200c42426007120648800d0510178071801d52000700b0445190407650140105800000020b00d0642000d4444141602d084011070320503400580c10081c2410386403018240140307040c401e00e5452050880c410800720400c420400200004280c0c00c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 992453543 1250 992452293 992452319
    0xb01050d140f0616030903020d03110409150302120118030e0d0c080309030708060106020304090b0a0f180b0402030c0901120b091009060b030106020a030503360c2b0c 73
    0x10010380241038549031090180620266134101c0100307040c0b80441c0c090100c1d9000407941b09610007420001511418090320840d10702465200300100c07401c0c40c4402c0c1030f11014001d00b0003224401c1d10080e08410003460b90509a0703401745101c000c040100c5c8070300740c0424420013100c03210f21b80150184520055a880c2e0301c2c05081950049113043d032001940c404541000c020810051900b0000f82c1015410140000d48900c1144104507809484102d0381013196a0360f81030100808135208040c590a5035114803880007032600010324400361400c0401341031401c240c000c40303200d204c020210390300e0228040b0054524252003c41c9501d1180e4400303071080a500c07250a02c1e8091000e10b110380744114548401a826141217802c00f41443d2400e10040203201e80000c2c0c14145950305085c0191280d80e44820714080100c820900c404a041c10000c51340804205285801251041016100c20148000510220340d08510b48420800a507500e01901d207003606112004d000e204481401c001b6558810b007000742 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 992454793 1250 992453543 992453563
    0x70f02011209201e090c0706140f100e060d0201200a0b0910180825060b0907020a0c140303090405040b061c0305070b07090b0d091e0b01050d14 63
    0x59801e03c2900c0c001e0300d0306000780340c4c08488910050300c060500d2408a03000e50800341c000e4030384103004a0150100003407500070248401403031031049440d00d0490003c020504003610003220148003050041443d03820740040d58401c180103044828101050b60044821003910340c400894607036160302c900031105091150481c003501444000c2c4060134407078181428035030b002c0c407070b910700903d4000d211400b0b51005851841c070a0304008801d4484c0c00087c54401401308011482e0100d11150000504021141c0d1045c102110261442800c0d0390701c1e5001a86e650012220241200ca0304e0502005070343c06400c1a1850b01402030b09807800e201c240c0000c00e003034510039102162400712400070041c00d800c20624520b0141004291502c0301e801b1524040c0c110f02c141d80300685044103a20000307030028029004900100022040b1035034403c044200c010003080010001c0352140c20309100006034900e2490031201413a005094244164079050030442c01c1c01c40400e0440b00015011414145d14505001038021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 992456043 1250 992454793 992454833
    0x140a03050316060e010c090306020708070515240f0409140d050304150209010f0c0c030206030108030a081005031905070506030903040303021225020d06050a0f0e0102070f02011209 79
    0x91680b0600e807800036641990840d0a03903a240c08001903080354851014012650800c00c0181c2e14141c1e401c00e05041c2c800d031600502603101e85240d100085441c54001d074803881007004c012141d07a071043c006400011802c1840c5501002c807520811052800340d00001c50584527901c0307034103032242014191b41045403141000d808074001204001c00c0c011a011851071080884800718603010f16200041d003041c980000a400b0822446150b400b0810907200d50b0000d140c000340050380f44c0d0394404040d6603a62000f00000005514140410b9816910301c1100f0306a8000801601003207034400e0032441c0c07031154958191a24411b402c00050551144002140203002c00806141c2d1241523040280c075002b1500c0101100007010002c51035a00e4074040c015480240202555450060a0001601071080c1ca24081c0200d03281805200900708542d010b1250141c68590501824411507009400c0303005150002c0d00144401003c0e80c0158410000328100d20180079000400016a86416a00100415407200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 992457293 1250 992456043 992456077
    0x604090611070201091d0c1b12090319030905011110050403030b0907140f0d0219020d0e0102060937030c0213021e0d09050604060501151701140a030503 67
    0x20f650f4007070a000044c08850541e104c6030000b000c90348180e050018912a8095400304001e102c2c01414901d0b69141c0034620308559060001c0320480c5001d40c00303c6007551207841284909265041c2e080c4080500c0d6425490700c0d002549000015150074070140e0003000507014191a48000c0b06c828803509000318001d550014903144000140500e81c0f1000d0203050501c61180306002c4101004030854842e48901d680c45501e407410398001030b01034018489000c441286034000310886a50008101800900655400003c51610ba0069841d15019114a040d5401400d00b00700c200d49403412407081100380c401030455442200302c40c0603081e040440f04900103102000040c0a61500c5a0038081c4030b5441c0c80c0440c5003038000c0c5449010504600f900201104001ca04402050500d0344420201d5801005480e25450185000e2008241c00d000700000f02007101c40c0340610703502c510400300c0d1940f585081c0030f11503400c0c003070003900101c01503c11643c4a8204400480020001d0024041c007402101c032500d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 992458543 1250 992457293 992457307
    0xf1e01060f11330c04090b060c0a03180b090d0813080610030b0609130605060105090a090f110712110c0d03050315010e2211040609060206061c0201080604090611 71
    0x112494440320204810407071a1041c81104204d6004440c11640c480c02c0028400f89008003017a05401010105007440c09810fa8201c00e041d04000507001c001360710420090010349851134940c1901401303288a0300282000080c4001440c1c1c040102071000707149101d50052540c80d20b0b1646080d02c208c0344259000c01031f0380c040080182405065401034000c964448061414070308080200500c1d03100075007400d441724046031040e406001205c50615010340007000440e280c0c000780f170103010601ccd0a142901d01e03014003145844080c83c169007030281d0120f01e180d004a9003141c02c4500c0800716a082c03100d40541d6040c00b05a607506c8031268016032281d1a119280d2a01421128601d128078803058184001e07202c071403400d82c1e40c40f290f042481d410898440301c0c1000c80c940450043c026040c3c1a90070950004d4003144068120201000721503055003181c68903941c60090090648c000c0966508180b03090400d00019805584c0075503011801a1001429441d152281800e03104403516030416000005461 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 992459793 1250 992458543 992458603
    0x12210c0c0f0d0219020f060a1e0509090c040e0f0c040902071211060f07050c07050303040f0302032103041101120f05011703070b061903050111030f1e01060f11 70
    0x6511400424100089000132a40100308242d220700c80b014071410001411140b0a4007543c003c4100c0e900811026009503841039010b40543d2041c416180301e850343d41c000491880f01c0000721400c2d46c9214407880070a4440300300c85856240c0c05040c581c0741d1042480081100701c1684060580c1c3c50003608482c000b040ca0002c06041041c4410603c0c900f50410010889100d00e0802d075150810211315110f42e441d00300964103401d040d4075411a684c1400001000503d1010150888066074000c82c00d4541d05842202200200804c2402741d0420f102d05000080102c0e2003190752007001d85043c142550301044807280481114801c400c644a865500d50061026070b0031018140648021180210700e000e0241c0c9501c02c0c070b030303000408091148032014a41344110b0281d806000c0290b82c0003009000355128400290a607030030446251144076010030000300100b046103d0b507500c0ca8001203100c0510703420f00c50225440c404400c2880f080c064880050302c0340407010021a88105110306988400c00b440c6142 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 992461043 1250 992459793 992459803
    0x1905030f0a2901020f0a0f121e030506060d0e01051803090604090e0a0206040e0714040b071211030d0b0f0103151e0b1b12210c0c0f0d02 60
    0x30541c03a0a2805002c0e0441d0b5500c24400b102c00381d1041c010030004094940100d1078202003401d42d00e000d0040c0f1401030100040e951444030254411b0101c0e00444e0210103003140c440f0030491140c1101c44205c10b442404900035802581c0000000d4031940c5410400b0f4041c005542540a840130306030340d2101040320005c070100303103100500c80480156190103110000038000d03014900492101d070f583c4040e48411200200b150b0326080d68041e2261b9210740c2d444845400c1c000c0c0440380d020124000b48100d4428a612070126016034105001040c2004400d4643c032900030f004850390024440c40c1d00b920346654400b040503142150303003000c01040705d59003101032251046d02a032030b075410b1504080e409541c000900d2013900030b55800702d40f002211100d03040240d0841782d16510075050b0720300c0003030803500700d01000d0071b8211990259011229104484030039900f02d803203031031075141c145600700c00c01010160710270313440c0c6802494551030b45c3d0400220031080ca08107810000140107a0340010107801c03140380c05000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 992462293 1250 992461043 992461051
    0x70308100b07021504080105091c210f291305090721020a0f05010e0306160c020312030a09020a0806041709031009082113020607081905030f 62
    0xc8848900d894210076440710b0081e040c000340301c4c070301d88245036800441c2d04060310014080400280500d0038000074107034481c592a03a6842003102138141c1c0c507411500903d0701c180007000e180c0c1000302201c10300c04001e0081c074200d82007980c2e0b44d40b0b41e402000142000104488101a1003119500340140801041042040f2402c00c088841c1800c007080910317480850118102d40fa001d56034005030b80041940c1c0100b440300341c0b000754000701280010442e8950580c1003800c2d07980030b8031425840700c80c8004041d0b886500315010002182940c029000741803041c49040d000d0b504c00f600722142c0300924070360120741d9002110410b42d580e075292104810761604071a040b0080c24684c0180815007440e45541501b981c404018501c00d020001e2251200d850820400c90801240c1c60b04100504503841c145010303902a403440c101103030411425811200740c0425450080407003404c113201c4540d09600748010790b000044203a0307501e0001d000b04600003880071404283c0d80050ba0700c996a03490b108203412044003010b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 992463543 1250 992462293 992462311
    0x6050909070314030d140601090e0f010512100e0606010801061b06150504020c011b0504050108011503060e090a0210030603021c08041827020a2702040b070308 70
    0x402409035010001c03a085040d2500300c407861200c3d0094104452a5108800c11440090f00d4064041030b68600e215009010b024260b030b90514030f0303956000d00b130601c070020340340070240c45034060040116103041d007450b03071000b440d0005175414a10081c42080c2202d5920407524030030f42040d410045907680c80003059003d0150344c1410411b0070b040c851450822a4144402800550788850801b40c0f00036840140c0c00600c0c0040c4107542e00c0580c108551b01a04004011440c0ae13041c800e0341600c07183c00790382039600761001a580c1d8083c5078a001d0f82d0541a8030121910070501d5540e071008540940070940b0648204801c00051030f01c4419403060110b001c03803c824610401d8640682840140d13100c1c140c2e10000e03110004201d4000e180e0b81408145845254003560142050586214020a5513001600c2c0c8100710492078210b0340c042540d00720903502d000002948010350401c2802800741810b2801ca40d000c01c07078108400c2c2000c1d00041d00880e0f0181c0c02003d16603001051500405902c1220315501076101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 992464793 1250 992463543 992463559
    0x30b1002070e0711160315051b0f0906070218042f092809030806090606041206090b0103140f0f03040504020a03020708070303051905132a17010605 65
    0x42540380b29240b02400c0c000400c260603d0140489408128442c16000c003c90140780541ea40d207442d808801080c050b450030141810700050301410070413440a20384194025a900d400c2c1b403541d03680500d80c03040000d0b95000105024040142e20b4907800c1440143c0144000c8096007030505108880451840c40c1c1e0000e454081200c0c20559000d80705080201c4040e0380c003280310b07250310140e620035880441c00c5a10130641e402503400c14035030a401c09240280130303455901c0b00e621403400384460118101e4450750004030030030042220740c2c46050300c0c088040c00740e00002034403802d680c2ca0401d070030005e034000d5515102c035060368405c103c0107005a042039410304008107422415542c2264482c0214810f4a11443d4040780582c03985000703070101d80b02c81e64031850895031410350346409002810207803040004a4a0318061240c500d100b4461a40200c01c805076a40c0c1d4144c8581e42c0c082c40c40e08595030251709854160040c0f803481601aa900090a022000d00c901c111041901500f110b18943c40944500c420f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 992466043 1250 992464793 992464799
    0x90c0308040f09020322050f010f0f1a032d10050a0b0607050c090711011d0c0109061d0f180402015d09050d050f0d050a1b030b100207 59
    0x909940c08500c1d1b80240e48280c90100d040c10300904103d00400640c04a50900b02c0902061141c0ea010060040711b200007045440c100003e6824141a4a050300c0c1d05544151348040001c8062401c1446000001c51001e0660610507902810403000042c5500d503541c80d182032220030881c1740182c040c920001c0e10854140b4615489685e980d92004900f94000c805030404101d0444c804d418441c2c1d07505082000b44441003a100d142012501c1c81e2180070114000ea80031680c0320b40c81107030b1010441d68140c3e86c00400d2540080c1802840381d00b0751886a0114200700d60b02c000740c96003e200c4038564011340528070b0030f14081c00007410302d520701e100d140c0205030000d2240d14035000e441d80c140c4d41145540c007503d060301000d550020500c40c10254400700c900304000d0030480788000c0d400940c00e00d441a01a55003420112505503242e024141d83c1d154054400c0c0141c100b14a03465209540c004411040031039843c00404100e0082c0350541d49100000c0d131203244200490602003001c03d6086118030080c160949 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 992467293 1250 992466043 992466061
    0x80d05311509080a0c02011206060c020306060d0c06030c0c0204060612050a0e1e010f1e060603060b040b162a0b19050c070506030f180a050c040e01090c0308040f090203 74
    0xb240d52130340802d01c01480381e99000d41e4444d94100c5a40c0c410088104045920340c60f02401c0d140c00508100e1291240000060442c24584195205a07503c20010131075203040c01801d5000c0c5c41024412030130054142c1e4400c1c00f40ea9a4041c2d0030050520b91141528202e140c100b010a503000103011111550400001100010b030000721001c3c41424072180750105410404001d000d007862994100c003a0b8102800b00ca62084c51b0321403040a503243c0c000401c4601c1d607800d402c2e420340e00107101e582e98001d0284010040a4000002003001602070000903c00c0305141e6605100030794400301c1c020a0340b1094540086642c049001100a044d072000000d082004410000e8090003540040c101042804915010340310420003910020b810000c2401e41c8918000158001042044034a138400d1a4495140341d50644041482554140c002c0c000d8004403440c54184800391001c1c1c58812135a42d42c80c0c0301c000214120a6110010b1480b0341603040d1b032203182c412861010703203550300304c1c152041c410070502c03032600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 992468543 1250 992467293 992467297
    0xf0705010509270403020705011106060d241505031b0a09110705190b0112030c1419060c1106010e01090b040209060d0c08090307080d0531150908 64
    0x7802c21103032101040724041c8000c00c01d160030201d00304070000600900c000c1580204045080d0380003a40c68286184880908903a15501680d1850f003249007049541c01203070354003010800300b08c0d1645604c00e1102c4515040d400302d690a44141050403008201032005140501c001445003925094540f42c100c0d412000420503515449902d82081d600d0300f0300b44081010fa0705560b003031900301e41a139200035458610754442c20000e11084404210700d6001040c100c01d401d86002400da0181d986082d1981d5980e1004424254100300803078074442c039140d1040700d03411015040c0e00c00e403080070040744000c0c40709000f0b840c01c00031120898450304400010701254070342c0c440c090304503000c0030400300e1040750301030100e0000e10030103081d290414000107550001000d0b2b900000c089036415510159103650f84170f0071507200d01031110002d111000c1004403031040400b03030b0400f076000600d41c0c1c00c0c07003441207006186ea01030130514031200c1b00803904441b000003030007003444100b44103159401051004e0811035440d04414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 992469793 1250 992468543 992468557
    0x50f0a061b0302070e0a0c080f0f06010c0204020d0618060f05093c16050309031b011b02160801020a0f03020310030209011d090f0a0b090a050607030204080f07050105 73
    0x12140e4007a03a80207040c420070002c4002d084c5042613111070b081141c0d5090182c11f0b00340186c400700c3c5030040450b801e08940c8007520300c42e01154a40c42c03200d86407140111000d48100b03506aa20540034030406038000102d115600007030042c00e8a5050541c6026205419103806030720100c1d10b28003400003040503440b200001a4007603502c0408041081600c0301d150845003401e07008114200390807900e00410030004d080b15014100303052000011840c101000c0341c03148011200e050701d0390800d1240070044200e2141440f6900c18410000c50302c94000d95211501c017000c1c1c0c640400680c0b01403110074034960880b1648018002010080d071401700012000f0f0081d900c50403060b4101a170000015002140c0c1c280140081d42e801002c4240c035581d14814190302c0c00c002c5c804001c14010300380100751230700030000e412550300500782c0182c03000f015562030341d0000043c02000075444d400795088560000c1c0007800800c0c4618940d0328016151410f04290300d00d040029840b4200d954408070003031041d42c0c0c01c03c09950070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 992471043 1250 992469793 992469827
    0x90109050705061c020406030b1c030e1e040203130b01140102070501080c090d0809030f07050d020913080a170108030918100504090507092004050d170304030207050f0a06 75
    0x25983d00b21075030316011300150005640d00c0303201103000700304954076401c001c4141c4021288048545035000540c4241c64005400401264801d110f80741c482c1812030f00314030185804082c101840842e08040f90603680203e51800d040c149001141d03040190032070310f0130b014007240d0034bc801d01b804842e40080c0d95030b981c5015450500c805000001e01c41201501203404841e80909000d00c51015450700348016000740c4da00500c40c0c040d000720907100480c00143e820454900500d643c07450301954007844600032010b031102c403c80b580141c800c404603091100810489c003c1d0340e00da05440060758601c001c00b00040e005a52990020068420f00f595060010341144c280c200281185031030f00780440042c410540d10003500079040c1745c40c03e41405408070300d80048440c0c8a00600c0001d42c0d100c403480c0312842c00c9060701c0030074605000a0015003090710300b41e11554451809000158400c0101081e107030000c982c00c8006038001e080601090410801840e4152000e84a041d1060305082c0040c0c03460641c0700c50044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 992472293 1250 992471043 992471047
    0xf0b0c03090f0d0f0b2509090905010e070b03040c060503131112070602010e010e012a0201110d0506040f0c02030a0c020f120706230a0c1109090307060509010905070506 74
    0x64954406040c0780d00700e940318000c4c00c070040145c80c04a20003001211110901010782d400100e5020751244045510061907541c1d8462505190205006002c0c0341c07800c2d0348a669801c100007014204000c00005480c07483c29554483c076144c60011602c10541c0c010000700320701401400360303010494089020140d0311140007000042001e01003030040714504a88881441082c500080c03040d0194402c4582541c0e2800a00200001007101c134281d03004203d0110354a001e00f100e4500b0404c51800b04142c4d80c1c402e100106203403d00f49044019500039141c1138108541e5501031161a01d010311a4560300340c8031a109022809007524040e40700c0c020400004203010030751799070b03004542c1d40c040540c041400c001c0000000e502a24425030390380c040c41c010300000c03680310311012910100c030b1001e542c61b00404114441c42c02101c410119800b141c2c40e08c0484c0c2090025000c00071558a0b8001148100b002e24011030b01c0e1b02541c03c08074103584018000e84140d0b4500304d0104041403000c100c85040d143c09840c40c41d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 992473543 1250 992472293 992472319
    0x60f0d0905031c06360b130b040e0d1b0305220e0f06031b030f100c0f0302040b1801020a0503030108010606092c0603010b06070b010f0b0c0309 63
    0x80040c0c0049400182240070004030041d00303150300100c00c858000b10510030007402d034440300041c0121039480e14448400007101e208580000b100303110030f501d0384010040810143c10302c00c0820300004010000f00700f02a1128000941d604042c41916102c1030003130010a000000107001400b82c17030740c044c403c12101162603a400309041c0a001114075154154080d580300550f043c43e00480caa651707004402c44204c0441c040780e400c0ca09001e0f000d00a81004020f0410305104c0c3d41d180601044600440b50580984075a041c8218030611140c800410304501c0410346004d90340f80101041c2c100c20000302410700c144410b200e2820440185c2e070002114030f203181041c10510340141e2520b107031108010014480040041000f02d419006102142c440d922000809902d55601e00c07141c1c41c01c04115a069646103a100b0303211b40001d80c040d40c102c240074000007400003018000c950240e01c1050150f070044419801009204000000c2070002d2407004481c41c104007801450507104c0c4500d8401e0751203004030300031107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 992474793 1250 992473543 992473567
    0x3021206010e0a0f12020a0b0c1c03180b180d21060f17122502120a06020909090a1a06040b13050402040c050a0e091003050f0307060c0905060f 63
    0xc28007130b10800d070070444681da0307a41c3c030f001141140441c101d000c0c4844440018078403090340141c50700c2d4010303003000c0d040c1e0b0790034101c203580000d50110f1040d041648605406c01035034640e407243d200860003150b0725500741ca041d0b600d058410004140d07202c110b80c081818503aa05a1103c03c0c0507040c2e814407024640c08c11100a100050026900300c540c0524a0560014100541d6090b00c2e840810350381c1070311001c0314a05080003181c01150000c00220301c1c48003450768041c03106889112460700c002c220348034841c0c2d0b9820451626030300da80100c071076a074009030111441c03070110441c42d0702c0f9007060000d00341380c1d6882e071710b036000c15105402e40c908e01340e005000f149071942c1d96001001007100203407000f905612407982c458023404054800703900441c0b414401c40441489003040300d05c3c0442c1900c541c40917036819828000c07850001801045c00701c03139101c400b00000c0e10600520700e1810000300115200c8034130b802c1481c110b800030031941060021020b010091394542d81d003030b80e42105040070481d4480c0c8030b680031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 992476043 1250 992474793 992474809
    0xe010b040329090d090b031012050109080a090608010b090d2d030302071a040b130812070201050f1014040c18231801030609021804110103050703021206010e 69
    0xc1c50b41c40d000c0c4202000006107002400c0f0380c50000c16515544030030765522050b100fa21054400d801c1d22401c0b42410312202e00c034007420b07074000d0348a6000090100555110740140741c10070f450141c0040d235010000c205050344621038a01501040300414503002e00380001030305504807c04002c184000e20300f6806c0000480b20340d43c1034200c40205a01c54004483d1400230000e5000c410308883c65241c1410080b030185030101c0e554451030340080c040919403520315140c80c003101034050844280004100c05040307060180c900c0c1d4040c0045030004111402e04170748070b0b466080300614022445040301e03c200015040d81e80f04000c0d111003614002040108140c048540086056800c0c207118201d500c00103094203480944042d03246501c0e8800030103094081013054506010000c80c0e03050040c80300600c0031989561000c010103100520000c400c0000403010305e00740b61b080358140d9040c051130400d0075647d42c1600074141d1000c4103250445c82d01d0310612070480c08800c060441410014540004186602d540d02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 992477293 1250 992476043 992476103
    0x90c070b101e032121090212060103020a0b071110200d230906090f1306030506100e070e060c010e0a1b080615031002030901020c01060e010b0403 64
    0x4039a04400761901c40641c6200d12a00c4200e42c1210142080c1c011365030484404009400f960b07035104030803c10410120465603000090180b0160b8034a45035006030764180d100c1004200e4030024182661660040081a00c099840f2074012201002000c0009442140034a15000211407030402e684580d80e046a14801d500f060070b902501d1000c000d96200c2c000a500800c003107155035805001140781c43d5501446200040d40b00020340248100d6601e8600000684490070001e000c1e180221a502c0c0003c65850048103100d0215503554428400d102c0c1c01d0080302d42c0544410044405140352840303408600e0401000d03101040003400481c0f41079035440003241d030121040341c000d122440c0903404250300c070b0072a030f00704441441d0504100100c0360134168440c0100c0700d440000d407080781d403043c094110400d840d4280c103a050041c0c1c42c58034000d02d003910146028100e80c400041c0ca99000c03010311800c41d400d64010340200759019004011400c411000c035420342e40e02a9900c82d508000c450480350f80c103a824 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 992478543 1250 992477293 992477309
    0x31605070f0302030c161203081f0b0a0206100513201305011101050103080a0c0611030109061e1503090503070c0e190b0a050607050c04050a020c0705090c070b10 71
    0x705110040c10b80c000050b2940c000040280c408100c00c10505c684e40101c24428110780503c403c4600021038010050203a0040030382184128140404c4a0b1481254641d003101155440118081c12110741c104551036000c1c0906c5c102400c1e01d0304000011b07034140c1c0d050004108594403240010340b00c00100c0c405c0740e00c506000b51010740b0303042240300e000055005801080d0000b4986c03c400601070700c0c14014507040760b8020040500c0e00091040480d007104802e07205a5140d40c0310109001144500002180284400080014034034146031007c2403002c100c0c8503402c54024451000d20050700e000e144032041410300d003000500742000b880c00d642103016026000c4d0048540b001c002800000160109101e0741100c2001e0600320800c1d07007001c0c01c4607112841c581d0070100c1d82c2c80a008605041d402002113500400881c0c400c44544070003c1d0036240c0882c1c0c0003032540e07000700e001e80c0740420070004103002d410200d034080ca886c6050171800e009400341c00e5000d00801c441c2e2020440e03940c04448030802400b910 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 992479793 1250 992478543 992478563
    0x14031303060b040e2b02030f0304060c030e01020a1413030204021303060b030706020a17040b03090f0c0d0b06090430021009081c0b1e030118030503160507 68
    0x81c10410300520304882c0071030049040040040c8003203c0415948400b8a001440c04081e11a948200c0c0c000310f1982206429480200005111800264044d500c100d218030804201100552001000d031000750440896070f0b801805024200d036000300d1144003004909640507100c14606100191b2400742d5800a504036200183d421041d850300010030084d203004070030900640b01244103040d902c4080e4810307080140c0000355500001240c03940d5041802e079026070198141034075183c220180743e10580b8034403003030f921145005c0d40040040c440001c01c45403c8030144240c0803e615000c08480340109280d118000c00300c006000c229080e0141314503245005804a500083c12146a18074100140540050302c50566908081b8140b8000e84814590101f5034600348441e0115040c1c03e44c0e03080d41014400c0340c9501100307032030b0f0300e404100d0803201c4104512000e071781082d40140f60031901981c00300f884400d15904170b9000300c0d4106086130b4214517a40c100407480207074040d088881f8055540c00418003203030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 992481043 1250 992479793 992479799
    0x18011206060203071a0907140d0b07110d021b120a0503040b0706060b0a051b0a05011a120309030c010c0c0b2116081f0e04030512010602061003140313 66
    0x8000083c2540e130b80300c1d1900070700c080f01c50310994005040860b0344c481c00d940400010f129402292500000810015090813440c5c00143d561700c2d440c035002c40303400b0000f4400020340340e81d0b428104441070010300140041d21140a403240301740106448a070503240103207080c03840c400f8035006c20070910042d5500907007500e407100d48500001500d0360014200713544c0c0600380355012600004220840701404202c0d102c1d186492014035406d03018034058041c8020383c0c000d801c45440800d10a02400501c92403103054560b02c0d100140400c00914218412248540c3c0180074500e055100050907100404090a0029100d4246d140c0048000c0142c1c00140c1010004500384c814130352801d0441440381c00c2d15903118000d0341c0743c00c0000214040c0f9410800018030000200360114101400145904c4880c0d001c03c2c103103603c60f00e0103031000000344c60441c00074900283d0130500c0070100e90750f540540305510140400d402e04015201e2310350174500001d440d401c1d0f590302c4049800740c00c00440e00c180c218003825026982d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 992482293 1250 992481043 992481047
    0x180f090501050a0801020f0d180b090d20060103021c060c030c03181214041220032b03020903011a24070b06010203041205060a0c141801120606 63
    0x5402e01c9107902031203d20308003041d504018025110075041e0075401e11f0920102030f10035405071480c03007005600c40365042555800702e0a94401c080c85841100000c1030301546443d00240741d0f06205160307180f000303003002c1072005900c804204a811a03404444802a030203041070121000c00c40c114004003414601451300f1413452301034005940010700d80d00d003000040000ca03400c0d0211000304100070300d8040050030300c2e004103004010708000d01000c046600d003010748540c01006c1b06000e49200b540d0140241041c1e201500400e0240040f03120183c02030b001c0350482100c0213004000748650340400c40e64002e603000c8058030a606469441034014024481c41914a2008a000d486030b10294043c40c1c00b02c1e01c1150a48062040807042c4406d2400c00e85400c040e910341c03d5032400007810b1503045000c00c1000050a501a080c5142c440b8029000f030812424164814022030328004040c10500207660f8490099244c8030094840890704441c0080c1952011001201d24a046101c0b0101040c500b00780410710035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 992483543 1250 992482293 992482301
    0x12010e0a03080417070b28021614070b07060f0b0a24050307020307080f09032d2a010e03060112030206010f21081e071e030f180f09 58
    0x3d0b000d00c0140f090342c4c1105041c440c29200b4001c3c09000541c03007402007160300c881500907e0202c0103400b51525610725001001090b0b03445065500b0800c1d0075061070206104100124014904500c001401036a18010341c03206640285c007005040030b40e5801003112100c605030043c00d0401c80c0200660049a104e012000390a641e001117100701444148040b009103001c0d0040b00e01441c0765070000c5080000d1079640c920158410900305510b50014013400e446134404000e840c0c00c001d00d01440c00950341c0c44614107082010000f0f400754140d4031102e45610046d141d0120895a0526164040c4420240e82d00603120070125059458040c480e45000243e445d034410000a9540e02c2903007980c810341d0341c0f1510860029200d003d14020f00324004c0304016040c1100e0303800c0b140d8921580441d0b00300700d1140c06034010000b113502c1048a46070b0024018080040c0640790074500d0401d075003990303110002c0c7d4500400c0380c15481200740c03d02851078422601006040000401070a650110303650407502c0e40c0c0c006001d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 992484793 1250 992483543 992483551
    0x80307050d0914010f0501030320010f020a230a080f0a0915051e0105130507090b0316090608190506120109080d0b01092907140d14130512010e0a0308 66
    0x3d03501c3c0c42800200d01e003841c05140d0480b5056074171502107000d1f0110031503420481510008440d075039140e00d00507022050002c0c1508504a8864001c8040d8818891081603601045a110b048e0100102c82403107400000780794106541900450595440303215100060558500103005c504100505521005440e00076034428403120021543e41078214900f881c09910a00034039a01c1044440b055120340d02d00e900a5074030503020304e0544422540c403800c414241d842910305805091043e90001842d6401c501a08010070103440e14040d0340c98280604403400c0041140c1d810b2041d291404260030399203440004082441e070038001c00c074440c21742c500108075501464455516600705020340205602401110003140c000c84500540850b814038a0003100c0105091010551707002e2210300040742c0800803080d848602e450003440e40b07620705807018040001c40180ca5090180030001001c101000c0c503942d204684c801da600f0403000c40400396140c050060002a00703081e00c41d00c01c080c41450351101c0c0b51402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 992486043 1250 992484793 992484833
    0x203062d040f021c18020a0b0904061a09040924050405010b0108271c110f19020103020c0111070f030816050412050f16091512080307050d09 62
    0x100550602c0075030140d01600c09468024081c0f00b545144600640e04020094008084026521100e030780c0001d0462015800c680354403c0081402171013070400b03200f82d0000e0708003614150311400c100b2440440500ca11280c541c01103450301840400c02102034101ca010f03450502249091501c110701103001808120390690f010341c20045060010f501842e0701d6401608215440347d40090b504400f2000c1103445800001c01d40b00d000d20000d0201805151150700365101d540c0c010300c0c1c1410701b24441c175003816492080d803660031405400300304400000c800444254282009600c0d001c10502c02401021020043c0440640c005511010030408000601c000d503c43d4440c8440c6803a400394149582d401400301e040801c00820040c068610b469040e02040b03442241102c0c00c0780c0211070002d007007080e80b0903035084031b8a09001c20f001c1000940280410804e918100e85002031401e0003000401000e14400f80c82c0c09170000c08508407034413071804c550070048140000d000e41ca4881c034000d80301c500300001c5011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 992487293 1250 992486043 992486051
    0x102070f120302251a16030507060f1401060c170456070f11030c1f2a03120c0e0f01140c1603020907090e01090203062d04 54
    0x200d00d02d00c540c00700c07050304c07115240c0011142c104808081d102609103240e03284031a00b13000c1c625500c540030b18190003061003035542546481080c90800d054401e5205ea601003079040c55400b031511803911140c0ba04642c594684500003000908101e41001203540a004280c14001400b00d800c0411601c1d0b120182c40e24000c070811035844005030706880382c01300801d4404c1071010404c040041c3d0324024510a0318010611140761910135501c05100030001c03881220124a49031100b0b6003490144111040c42509517455031a2980038010170181850325860725050128072500758480b1001c4e07540041e0140044401c1107005c007050706024014500048440c0003140c200503c0c1e8000c03030300c00c032214440740d00003070540c0351041014401501c4408034540140061481032060880c00c51003040100c2c1d489050001e4200d4890441c01400070010000740300d03506109100b40c0401104c0204002d5904441c01040c0060301e81e110340c4001210702c41c2c00c1c820316a4110070444005a0031007043c060070050001220200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 992488543 1250 992487293 992487313
    0x4020417073008090a05030a21110619090503030405030720060702090c0d14010914040503030f070e041a040531060e01090b010e0906040c03110102070f120302 70
    0x42c915020030030303a01d4440a0300c102c5074005040d00014180c03520000b0300081d102c98071100442d01e0b01141c01c1081c0e581c044400c25043c087c2c1e441d8496640b0201e814038200e03000100528000790f60300c2018018461188204048504000c0d036544400765266114054a070350341440d08145a89810540b001e4135888086038520304003460058180060780030140480d0f0410352590200422010010005441248100601d428030707403451003442d905003441d1a4186003541000300000451384020000e47d0703203008040034400881c00000c00e9950004c081804100c807990f030b1120803140704c41d444e1041034000341048200040201c0d09444840025425070b0b040100c0da6480b83d920614070b031019042c01c1050350b880b5a462800d40e0583e107400308540944408607442c10b5407021a402c40c0c9441740144c0303161456400500c003160812560f2034112219038010010b03414152241d05d1019291f00c80108034882201e200e03145079009000210042c002c0c409409011750307455005524034a100c080c1200180901003c503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 992489793 1250 992488543 992488589
    0x1215030305210f04020d240e07050315010b0f09060d050a0507080c0f090604150507051002120f060f0a0320121c05040305100c1d1e0402041707 63
    0x2d0b91040c1102c1c80424810f4031a07400f8441c4c240300c5880c050b9607401c0380c031801700380d9071072a6000021400c0d040b4800084211840d40e40a00300039590f000f03503210f500328900280403c042c0e6640607041d504005541c0e1740c1c4840c082e0b2400c1103031240c00c2d060f903000000450400c0700c080307550744407500c142c103052002d10040e510300d003040b0752a041c01c403550440c040051000f2600d008108006d01000f090140c40d541c5080d880795008100385d200501420001900041c005007040004d0041d8100d55105042c15070500641160b03034500c201000b0560f079805140503002842c2c0d640d9100000002d0a4050702c103406998907420f000d040d40b4261105884001d54100000e40d031400e25030810140b009808005d0007051140320070f003e03001581d20f400c090410500340008000f0610078003803a01100011680001c20510841000d80911000710305c0074640310003856038144035101d40500c00080300d00c002401c1d449030f0b16400040e000340076a8002d00b00c4080802c0f900344001000240d002c007520345220700ea170310760000d40b009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 992491043 1250 992489793 992489857
    0x151005010318060f090b0a09120516060b0105040e0f01030507080a020f040908070213020a02100605060304060507090b04080c030f0d0c1401061802130e01050102030a1215030305 78
    0x501840c841c00c03000000c0200d800c544c00101408290013010400c542c4d50f445007020540c09407030420381c107542c0305014000c0010740c0340741c40e01841c1e203400e00380d0400324008102100c0c1d01c1034001c05043c094841c8c1707546140343e1099040f100644107030768410303a45081c14188044009000d0004644621460f000070841034030000341c0e082104d500a0404d040005500e0610018007501401120120740a100e1000140c1e80c80d00c0d99040920765510058440d003411400901d094250030192000e10318180d02030050303450b110100e0f0713481030b081000410540c4480900301d411550941c0520007140000c140841c9514000c180f000a031041102140c13803803400303000407584070b82d900340a440218144650850005140c000c0b0542503048400c0001000c540e600c0042d800c040d00303e00306500860380028103025003060884c0100c0030300b00e004001c1c05d4544c100b10000c1e589100e01e80195090001540620384c109005421822a100e152071040803016560f103000391441d00884140030b080e4807070b035007500214884840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 992492293 1250 992491043 992491061
    0x1021b0c0a2313090b1905070f080c1b010c05040602150f060d0f02030d0809061e13020d020307060305060114090a12050f063309071107081510050103 66
    0x503010340c1c590500803c000040016001030120503072070702c081e00017154001070072500c0b07400d55900d01c041c0810f003180100c040310f90090280c1c042c0300703c8a64a07080c1a80c80360190390b0008801c501c5030760310010908e50300b22070707480d50f40210b00c0c5608100c1d02480c1d03164070038003801c11980c1940880346104038405c507421613140115114440404000300007081071804100c08405030b402a11252600c18240c0c0101e81440c1085400c031340460400b038107120405100f002036507400020510080d0310841c80144560f000300010309500201100c00300894159a50007082c0c4890650003030803a142c2036602c2d00040d014200841345940070038007a84503440c4a158030400c549016400510b1003079500e090544803100c101c0e1204c001e80311845600f1180c01224803c20015000741c00d00d40d022503603950050841c03240c00208402400c1c0d034031142d40c12000e82d40c5070404003580120160a101d030340b02c0a2000b541c0d02d44400766000d98464800c80740000c05c0070020300030481c001c0b0700e0b0402070441d41d9110001941078441c901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 992493543 1250 992492293 992492339
    0x40f08010902060a0c0c18090b1e06240c070512030f07030c030509040f0b105405010f05090d03320315220e01021b0c0a 53
    0x2404e28040e1041000300c1d1940e11442a94501a80301c0c90441968124140354184007983c0b40240c0c0244402a14420351000e20302c1000d0056140980b80701c061401c010308040c1c0641e48403020070307110802c18400980b00c0c00700307000400d441d1203075940c0180c0d40d00104c0c07168501500c000107a00554400110413034203000d072103085040c5040c0c4190340c11213000342d00391000e4007002818451407000d55503d020754031168410b1880490740820307010802c5801d0030041c4000781441400341a00d00501d50b08142030043c842c20a4602c1c14882801020183c00c0e00c01c446007400c401c0c01d4444031120034031410550825944281e98100c03a00f1f600c20f034151070751310402c00c1d4281d2203901c05046c540000d200c0e0308041c40512206c0500c586448008891002ca207880720140004c0d642e002c002c1006140403c101712418245c102d500c002e2504800c45010740c210002c0800d50011519050808403480094040794040280c8204050000a1052045840b80440f1014610904aa010029521044200c00c1a44030640 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 992494793 1250 992493543 992493547
    0x130b12060610090302061801050d060801020717091003090807062a0c0804050405070309080a09060e030309060f030c070b01030f020108070305061e2b150e060c0c0f0a030302040f0801090206 83
    0x340c0602c40b0035100412402d0304103c810045030b03074424468066840104600400503840c0e0196180001430805116560481d0701d2003800714001640d15640c80030901c0320103060000d070030461420301c17506034072038140b014140600b4007115203498a05500c0310200400164500003140c80503110481d84a44201005400002c040c48203105514107548103e4004440b42800140f104555465100700d420039803452010a10b8003500b000345640043c614195084101c000d1403070450b000002030414040e4600c0100c030780c4004070008189810203400c6410300c1c0c2d00207244980d075603500d241c0625003e452078030480c001080360001c101064001e0164034000c800081400b10b804045a00341e00340e081c2e4542400c0d911404907400d1540000a006065105c0d00c045043d4420001240c20259480003c000035001058a8030383c01a18003e130110b88a50040380055455940da0069030300b03140b41140b205002069401041c68170002c040d00356000348212061503d00000d5169208441803c90350780c041d01a4000d001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 992496043 1250 992494793 992494807
    0x30a090b1c0b13090309050307090b0d0803040c0f0e1501051306110a08030f010503010c0c030c41060a1802040c1b05011a0409020f130b1206061009030206 68
    0x4030350803003907800790302401c60640f001140344000d00755000018203901045513420240102d040070711200024210f4001c05010552013040424402c004090014110020120200e010840b8009803000140703049880304442a0300c070740110852a0b41501c1e0400c484400000e03049655024205031101030748480ba6645143c2d10b0321105a4402d8801003043d001030059144480004809001440c010f017900040002c1d00e6040c50309044c21030305a51626000c0c0040446500c002079407002c2c40003202980040c040d124103c4140c08000428140741200c42c90840402080f04c13101c458503da602d021b04401d089800076100c81403c0400c44440b08c144004207410b001461000d410182c00c1300c00007101520f0310584044002d80301903500841d0041c01c42d401e03511a20b04001e00c400404070000c0c40b50044600300300380d1140e80e000403469001924902c0c0600d078032164402641410b1703030214100080c0034010048035503000d19040c0e2503100403580240300d9100a03201d48200c61185c42d0f01c0301074030350240c040d80c60700c50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 992497293 1250 992496043 992496097
    0x304020409020102100207030816081006051c180c05060313170c01050f180304060903020f040f15210b0f151f020d02010e1902130905030a090b 63
    0x200d01c5050303056200e001c83d241035292440c030040030340c50700a540d258910304000ca00d044600c0c652089242c104183c1d0001c0c49110014181c10320103d507110b043c41c41e600c084083c00300192000000f07200d4003031440c001000344684034032810701c503440d1b00c5071410b60f03201030701c6400300141c50000b80c504560350300c039a43c0c40b41e000450700c3d030400400403243d076199170074407040e11040c900307550007160448403401c0d0140510000c1c8507a50541da50194151000c0c42c14142481801052840144000382c810380710f004d0084290303102c0760f000c617140c41e0030144240248103481c1100e6184485900c44c8060381040c0481081c021221010041c200300e0f401400e002c95622503003040002002d025100c0703100307880446182c0300a50b403290005180e0040d00c0102e42441e220700704000e400c29200d00030103001d41e41841041c1c00101c1c1e000c9112000c1500d202c0c0200055415400800d0303020f14421078103801a858038444405104000002d0210346005a5030b00c152141c9481045150780201d1240d100748410b1000c6040d41d02c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 992498543 1250 992497293 992497301
    0xc020309040207080d060b070515011a090409200f01050705030301090e07270f0b0a0510021e011b18050d0828090f050a141215010501091a03040204 65
    0x40d000e041c03040d0900003000600000c41d0300d547d100c5000d20400103070300303020000c0900034414407516080c001407082d0300d4041800b001e1190fa007108188002c0000f40d2001c03d41d21035002188a82c0c108005014401c0340d2444540b0005041020b240b20341c0c40b0110602d640c2d88030304201e44100e64014040d6080d6403070055654045c0a1180360415140942500405c01444208294500d00b0880880b0a030900b0040c06e00c2d01200c0760402a0001c2c00d08191074410300d07032030b1500301c0c00407a00300380c400d40385030707000c8a208a0130040481207012038400740701244000b00301305402038201c007150240200d15105018000313a0340081d6580900c031426851910401c41440c3c101c854540e5640030742c40c8a81b03040740d6040c04071b09881c01d0448161110340b0035040d441d00c00d135018607400060845c858586d01d0141c10480050105451481900b482040342d0b0031040a580310009800032100b00315086446410000070317052140002401118001350b00c181c00051408001501880c41e00e01004403a0310359240c0c1c0d02804040c2c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 992499793 1250 992498543 992498557
    0x50703050f2e110a0305010513020405030c0111030412141b10050c0a150e1b210f0d0807081f030f021912150c05090d14010501091e0c0203090402 64
    0x395490720309030a0883c0380030060920000f81d03940011258100810449140c1e03036004680e6500b44140010300c900d0b100020480c0d06038000342801d5140b6a0342e502c00500e1403083e500000210071200301c001040041440b10002801c4400064400100302a83c0a605400c075403c51a42d10030481d6001d41851b0740504000c0c065100300105071000380780d440c2c6410076801c10800d001c4010681c1c401142e691407005100500d6613200d2482140c01c441d091400195140c0020307020f04c10f400c42206070141d4040d40400c0707200d078528848416610385a6040101502c1c00b5001c07640c85e00801c4104000600d2628071100e40d08444400d454500c40042c11a211424100c801c0401242c204160380c1d82c41c003041d0001e00c448001002c124000d01c0181c40c1354504075056900300c1d80510a014200074018613410b8124090740d4985d5000d80360140384002d20b003040300c440c03140581c580380c65529140c0003180482c01504040d500100e2096144101c86003181d03040d040b102c80401241c01a003052221a0035450260000d00074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 992501043 1250 992499793 992499883
    0xb13020a08070807030e0d0908011a01020c19030203010c17090a03090b031504060807140d1104020f071a01061106070c0b0603011118151206010822050703050f 70
    0x1120006d40105207452120700d02c0c4804200701060410035400240101000c451001c0048030000d00f510002075030311582aa14140318040c4a1654202c0582d01c0c00240e0003103070014024003688404104c0030f4a50501d814a01074a01010000503c0301000005d00c1d40070305038503696100007907150460b4410507802c083c20a0b100001d0304003560f030302070345c840c050603000d024000c0140015a24112142c080d00f6110b800c024081c065420061000c10f0310407d010401e4101620f0141e650045030145111078401e40c00000c0451042032220301d5901480040e02e81a10819101c104002c0c01e54041140d440f14212111400204800128400111040c0100f0740000016001060060a428001d15a9005400068900340b22920899258a00303c41c8001402c5d003c0b400c45450141070703021611a191008104605106007100030454000c2003a0011b61401941803600d04900c41c980f6046454031100e1000b0f035102c2c41001c2c00840101001b1a03c05034442040d5081000711400352020180c5041a440b2120 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 992502293 1250 992501043 992501051
    0x12110d03030f090506061002010c0e060c120f1206060405103002180907092d121a150d0c08010212010e10050906091f08010b13020a0807080703 63
    0x95420280901d03e11103201d040500141e140441c00e002d19606e0f044581c90443e81007504030081185c0041a049a80030145c0d901607036031103214005484c0901049242e5101000020800342c6c03d40742002405007038151140d16561511100c0c1000800e002d94050141e01170303018042e605485005042680b6900c10082059078200f02d151130000d424070980c01103000c00da4000800308601c0340c420b00704013008681111217015508122030010b1900450f4082d034114480350201014045200b034010b032611956440c410308410342c42d195502c52181c1a0101103c0d40302038000c1d03030345c2480c91111400c0e02c00c41001c0302086141c1b0300b01d000c000b824000100c051794446082e41c0080f070801403c0c001400180442680341c829545010908410030600802499902540c05014010703030b41d404055030b8018034129082c40c01900c4084103202103a080401d004001c400c00c001c001000c40c4103410014180f40708480000842c641d5003517030b1041c0e1040d80540000680e0020000f0310141c0116a481d42080031854005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 992503543 1250 992502293 992502311
    0x3090e040212010c11161203081902070f05010e011e0c030f020f070308090604030507120315062705060304060e1911090903070b0117010b0904060b0a12110d0303 71
    0xa42118504c2d200100051070b05100f12807480000c002200303289244d0700f40016400d240c5188498195180c1c2002400c014001e0b01080c101c400d0f140040300c40020191b421591400c5524003440c0791000c3e44c10448155080c9a400c0c1c0851780c040c030491620b802c9000110380200f82002041300101078030b420482c1030540d03880c1d413100e501e4490310184c54414003050400350350b0845800c003e072180100404002c0306070b20440030031001030340c04025a5240c581c07180c1e0002da80e4603000000c0e00a45103c00c0700c1100074443d1600000c010380d21040e082005060000440f02e042c8114103001d00c40b101d50f0103943c0e0051000c001107000207102d640900c601c000340301c09883c8800d00c0d2034605510712412850035500020095040740d8645000095280c024084c40c006503d030034010b507149041e582d01446515417026209d10004201d50013074203c0710514000800d283d546141c14a007110050007041a041d0140d00c2000740840c03203140e500d0152064030b41200020090340c140300200304032401c007a40210105078541e1048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 992504793 1250 992503543 992503579
    0x11103070506011412030f0703050313021807030501080a050a1101030204030f0623090c2e031b0908150a02120f041703060f0f1915030c02070303090e0402 68
    0x19000e0300b040c94020404044c01c8003007000301c81c60004c4c030b034a440c0c0082000411100300c1c001200c040300e6044c1051916030741c40780190f1101019240c00650415500403c49816002e0408401d205011716103040146d43d0322082816591244260000c100f9804029000c02045003d803614410600503d009490103869542d021440001c1c070380c0444401d03868441101190442121041001080030710454461410410340daa484090096160082032607441c03012000091001864030b80445160907c1c02c501c092000070020141010030701c02c084038022071901031a104802e881b040361a0b9400411503d0a0310f0040f61859402030a4821944d608003c050303c071000300d035529881380ba400102c003140344ca040d0408800050311041c0b403c0c000d403010420040c0d155142d02d00801828401e540880200d1318030000305500400c40c0380101540c08030700200080000d440e074103840504460399010f01400c031000780103907035a500d2030100802066130a402070090700d04c80e121040d8000e00007000600141d05513020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 992506043 1250 992504793 992504803
    0x10503150a0b0d0b010206221a150a0807080d05030c0403051504030f030b030d0e030102120112030f020f0606010e060909010902031008060c03010509060102150717091b0111030705 79
    0x51a0801003c2603405070407a0511036490800c001b0300107401d0603e840c03080c0480c09440e0360100521281244569400c1c048903038940703690141580043d00c1c1c641018030700c0e084601000c83c140d0744520415030700810131007800300d805411107510500400009030421410b8803140c1008100700c1c0404e00034800000410020408a0700c6548941c181d04e07404d003040d080041c01c45280041c10028035040412124184e100040c0e1282001e100c0d24102c0c10042c1c0d1400007030b0280c400c4040300c00c03140000c0f800210350f4082459034a90618130a44034030401f001510010398840c0181407140c00d203600300500198440d4000c0115100b00e50004000e9031400b0024000245544001c0e0004a080c40c1d010041098564880007060040c03d080c0006150a150445500026200500480d8003681850000c201c440c2d0003004400c201c02603070301c1c0011440c64130480061201c1100d000c0400d1507229040480c0c0075550105004102041c40006110804003c1c001910028011803d824480c07100304032038404030b0030a0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 992507293 1250 992506043 992506049
    0xc0714043b121603090b18011d150c0f0d020309190e04050d08010b0708030a0c140c0d080a060806060d0507080f100b0402191407060c020c12011a010503150a 69
    0x2501c0b0044903d400c00030440f040940110345003020030003043d884100351541c0c6080909003441c0980c01940680000006c1c14070005030380703402c4899035820b100b1050040024040c99030508089554032002e101c5c003030b50b442c000f6540300c00258004000038001810a050b0303081080022600350091590340c0c54440440c601e04450980d015003100300c1100005520120345401004112800f07030401c896a03c441c810f03031101401e80985240d50306c981024142c0621a41c114032002071080545078a500321059031074041103400303180064140301c00140105194410401a5080c200040800344d840c1d00a0100d060340c032120950b090f108102e40060204010840c96001300313805406400c03900e0031104a41e00796041415140d00c0380d070062107a00a4900040704e04100700324980342038580c00000e2141c8200314401c580001c1d255030305103050601d42540014092000341e07010740c2c010070039041201d41140ac03120207910100403601421008500b641c82440035540100880940000341044500004c0030400554 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 992508543 1250 992507293 992507317
    0x406150b07120f080903040b03150301020406020d090b031b03060409120207050f060315090406090804030f0218101503020d1401080609060f0604020a03020c0714043b12 74
    0x42c2c0035241d503651049404070420500d0601071030900745080020b45a0145003e03c1e4000d0001100007000742c401c0c140c041011060180003155507a03210f25001303483e00803081588001c600700c1d4a00203242038110701140d00c90340b0540403030340621801007854196540003920300d0390b2250b2540c40000104510350725000003000f0940042c20900c1c5400280030014060f880d610384034841c10300401c02d000c000c0844d2042c0340c40003240c100503a07aa6a1a2440040180708805030407490301060200400010399032060340c5a008075606503c000c2c1c00c00d801c03d01d80904a6408100076041001040441c07403681e4840d642e17181900b00982804810400d16040b01c00703140d2100b2000c030003072004200b8a401486029003240040c0003901e01c518100e895159455030203443c01c3e000d107034002140c4c03050324071982c15212289070900940380e00c9a0b9030610301c10031141564a1500c61803811001000806440c910742031400c3d069030208900d80514000c4128007418405211018001c4526650081104800034101d00c40340d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 992509793 1250 992508543 992508563
    0x12f06010f3f0506010308180f0d11040f020c0601031a0114090714130303090f06020c1504031406041104050403021c0306090606030617010507080406150b07 69
    0x482400d1084240380d101040c20016010280064452072401614004020b203055008641c45060404100c500810180c0706018590005c000c03c4084002410744404c0c4c0740e070032507035404214200442e2240344503810307900044e800340c8600000e00201c1e246c0f005907070091000440e901d5844900c0c05903800400d60650a41000d00103200308000704080c08a00424603c140c0c0040d810400b85031481041e020301203204144007400151440e1240c042a50f014124061854a41c0300000c0003144080c014001280132407204032001ca01840010080012216030342e000b405280c07604002e21500c00d0340c905422440707840c204004000714060204045002a50030010702c950319107070401c0300140361320050041c421170400c001d000100c1d500080c1000f484820410503601c8020705541a0002c1417650311040c1038504040001440c69059030090044810b8001c1d9001c00303003600c0c50b4680c200c0c0d000b12200808a0518804200800d5407a40103200703900f901c1c0c0c1088101034803100342c076080340c101440031601e650f90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 992511043 1250 992509793 992509799
    0x1611070e0901050c19052206020a150c020706030e071703031503010603020922021512010b090603011a0706020708030916030519061d03270f012f0601 66
    0x109228071640100e00c2d200160504025820010075101600c600303e080201c0800c02003405c1f80902c2c0b0103186104c000700c40d40481079440602030340b00c40c07000400380d8805000040120800c14940941040490554080c1c210740c4d041840076002007400e842e110103d03120307807580490b01c502c4130352030000000010340045032241740000d401001c0c5201520315070701a0341851000c000689034900925001500c407444c40142048154100d501c000300b0b8076010f903000c50300c41480310b282243d2400512002603c2c1e65041c201d0f80c3c842c0c1980b41d5920814900c0b5030440c50410042010a04104c9120301c2040c0c0240494a008603070349a160983c3c0041e002036aa004000080c4080420100004100c41d49101d0400082ca403540c0c6407640c03207030940b0003c220f07150034400d000070401078194454662044491010f48911b50044000fa60700d030040308a860b15000010750a410303805c004c2403184014031004204201e20700d90300004642c4041c0803a000c000c03031441d80c1e4040c20480140040b83c51564100e100400b56585 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 992512293 1250 992511043 992511061
    0x5070e010816051c020d0b070e190305210408010606021f0e151314010506030d0c0b0a0c090929011b06091109070801030201090e010e1611070e 63
    0x200180b106480b54445910400c040c0d21603808004e65001c0300c81c05481c000a540c000b0400c0e426036150028410036041d01041456034001950f00d5030b00805452a845104c80000440300700c5200c0c1c0070180643d0b2011482010402040140c01d00c0b042d2201c1802e401c15907100807240c2950710503040000940c00c020640010212840600d01c1000106a028405607005028250701c62101c1d840c0c4021080881e0000340307890340407107407a050880d40700030002504840303c1801402490140c40051090140150910000707100d07418031908103412210f41d041d951982a0300c4001000c443c505102400340005e030000d4203010521982c1da803003800c0036180650218010f0808e81e4985030355046414000c6442c6034018902001ea24030005c154014000980410f4909000084541011000743c0c0040e400c410051041da003c07440c181260700c00e884017083c03a0b0325015018500182400790041035540d1800084100601e03803001d0140030303402c3c144803041c2a0610009418003015422940c1130084000502c2018031f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 992513543 1250 992512293 992512303
    0x71209050f01030908030609070201110f120a062d03140c09090f0c150c010c120b0a0501140307030e0d0f140708070f0602162d0b07031805070e0108 65
    0x82803d103000c2101c1c038400c0d5030300c038030600015111034041e81d9000c000030308503170003580903114640301c81711a01e8444682c1c0804a50a0740880da40500d08104200480d81c886d90a0042c0c80540e40401c407015210750b841c2c66010100003101800210380007a4500000101701d2607000500d04100000242410054650034007503c0d0402804154455000d16814021100003140001440d00200c2c0d0403011402c54020888243c010301c0306000b215440e000c03070f101c0d40356080300d400802c0c2100c0341c00c00c0c040418171104001e4900b2107845158007040c05140700c00d001c800000c000f9503200d000d84c140040c003120b18402017072030710395140380103404110f0b0f60380c200740b109030004400c0e458441500412407602c2d030a42e4444d181801401030003450601d4202c42c00b420400d60f030301070340c1043d01122480556504142480681108480c9440d00307a030030f0303480441d03010306680303d140082160882807203510740d221031000701c0050a811001081d840c600114030000500140407550080c5010f041c250440d5040844443c184 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 992514793 1250 992513543 992513569
    0xf02030a0c0206150a17010e10270b0a111303030f02100515010c03050408010c021e01020306010c020f180405030c0c030d0903060b010c1406101208070f03020307120905 74
    0x10010a0381d034820540c0e1045c982c0802d6450f182895203481c026650080d0144c080d41803400301034003400f4801b41b4910841d60050000381405800000803100810520181705040c402c05059148100300080700d6410f55040070740000d079216229403525543d000390128840350b076042140000c0d01410b48540003541040541c104501d951020069401c0c1000c601180e131700c80c40c56090501c5040c000c90000d050241003910020100d00000f40070091074140b00070b4440181c4544807240004081c9040502841442030f40c0c425141a1079010010029408004002103070f034403c6030317002c114200410800c2c41d0007004030703000d507200781c0c02540c8038a41e180085050a0340c0842c1140a60f1001c0b0f1a090031a901400d40001c40381c011034000343c00325440c0300407500b002c00f18502504650980c06034030b188000000e1014440d803051644a1201520f85007140c02c0490a19070240072100140258000b18000010b62101d00780310780102d0307142c4445035890100d203415948aa030041262800b00b0020350518051800030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 992516043 1250 992514793 992514811
    0xc05030a0b0f06060a020a0f0501060e0132220b040207080405181306090c1a0a0e010207050102150916031203050a0c0c06090c180b01030f0b010f080a0f02030a0c0206 73
    0x802c644604003e50750f801d6031030040c10455001112344c09004081d0320080181503806000f4410f5a10b5841301c0e4052410b016043c000340c100d00410032143c5009039001c400341d4000400d141003130040911049a600b20030070003450420f0f0340b0103541c030706591039100400d082072082031600c0d01c4601d400d04100c00c80d0340400b03881c0680c0d036962003007124190040c0151802aa8031160005500f101402d0500809503030781c1104040d02d10403081c10502d1210341025281540482d070b50002680c2d800001281c640d601807040501683c4045030745458502d0505030f50350301980f4041120701e03606d0305048002c44440a5481130310100d2001030346505855160180a83c000c42c240070601c010010624000d100303981c0249c0240c012903841c3c6019040106102520004140700c4030040b9483c1011038404000b0008010120b0102e450400000240d01d124080c0d0000000142c40702800c011a1020985410030f0091500c0b0180d0354500b07110440c00503d01c045c40c001c0c40d8010340000d15a0004202030b20b00031001d008505c1d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 992517293 1250 992516043 992516047
    0x190f0c090918020621180d14041503021306030e06090c0d02120a0f1514040818061902240f06120307060e06100e0f0f040c05030a0b0f0606 61
    0x82161000746003581d03d90540b10f040d80e628070b005140d090700c1d0215542c0d0540988000521411441290381c00d06103030141e0081c2c41c0c0010800005076401d40c407840505140311800d10040000e1404080e1a482107044c1e0304001d41b9080141038070011030380482d000b900c08281d0b201034401555404000181c1e100120400030303c091842040000d03e43c03000400c0091281d20031140c0c1610700c0d0b8081c0880004030b075111690031640700e050320f0100703c0089103a21b1400c03064039044d121452041c4412180d07004541001200d45001d00c041c00c1d92005001d10b146440e0415010002c03004150900c00450000000343d6000d010340382c11740300c603e6035030260600d0b812408035060014020404113490a65401660449022007848411041c482c19801a84c401510f81c4c5d290804030b020300d1001050141c03080d90040e00c1c4200d8a03464240e54100208203503070a0800c0c501000004803034005250285812a0044408001440c0c0d100c0000c6d15154140d10b0840b400260f9806204030b511480a000e60051000c94a2034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 992518543 1250 992517293 992517311
    0x1a040303021606120b0f10030f0e0a02010c080306010e150715050c090112060504020705030408010b06130312020c091905101206020310051215090313060503190f0c0909 74
    0x142540f40d207108610700165180c0c44a812031ba54200c2c0e210780c03c0000b800411006c0403a21f40903000f840442c1e02c0714203450410040c07000200c00417440e0b00d50240d0503151603114950700c0c0c035568166000109400c0c1440f0602c109014145d6601e01c010040451f80301d203250380c1da00145407003c0660480b0900b00300d05420300c001d0140100319081911a48542840e0a21448440c0000d00c03000e0030041d030020b40c015100160107414400c000c0010800d13940354600a02036194494188000c1e03100d9008124602898041e00b84001121241c5408104405104131501034100100103005540e06032070003402420b0030007236040c41100600589030310503403518400714001d280c03904000e100458004000c001680c004001a42d001110303421501070600508525060030480c0105a5100c0c55120240001d01d180000185003c0002080760f5680d0800400c21040500e4900306580541014048401a0003111506100d031589407203411301c85c0d04180030207c5c10492030301c009800300140f504510303c0743c1d040078090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 992519793 1250 992518543 992518547
    0x70306110d0e0a11060a090b0c010f0b0a03032f01020a110c090105010801142e02060a02070804060e222f0a05161b06120902031506010302041a040303021606 69
    0x1000090707509441c01a82c40030080e4085910b47c26541041c5216030010542c40083c07401544800c43c022040c2c2400c000c550020001c105081f040d900c0014000b07011084084d401c0c0c0c8450810544409120801d494690022a41c0c02c0c01da8100050741400100c040c6a020f1070000700b080030820b010425100c8032482e50410000a02d14141401101d40051180c1150025a242d01d28800e40114550b102d015100f000c41000f851070028120420006210341400310b070203400d061013201c4001d940110010b00c2d091521030709440c4a4009581303580c1c0040c06c01e8460209e00e18000d04a44001c91100000a01e0801c000303042c40d43d41c22511040740c050a000c00c8046407070f100b600c21954500d9480c00c0c519120b5450004040b88100d0040c0d0040c052a81308403160700544130000305005640c030030307205c1c2100301c220902e00d0400c480c0c10280180d41503200c40410b20032084030441c031940000c010b240140c1703401d84547c4003000901c189201c01e0b910303072000a010010325070705000c08141d1103845030310752045600e05880 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 992521043 1250 992519793 992519813
    0xa0207051c18090203010e010e0c0a14070812010306180203100921050309011107120f0e04090305180307050a211211010b01051317070306110d0e0a 65
    0x180c0c41c544800d1206144424080d86040d104050700340007090002c0d4607545108003035003081c400e640e820300a11001180340300110540511860b001e901480c180040c1940840700070b450381503c250b030007004126030001310b50007000074003040c3c000c56011007041d451032a1500071169408262901e80c2c6085403020016940070849600b01070381c80c0e40114100324035042c10b00504042d401c80200340074800c2c490344034040c0c010300594891207415000b0040752298401e4000360303100700d20005181b092982d403900740060083e01c2224ac0200c0914002450008442c0840c08070795203400c1c258089039000c680e00703200c0140c00b2108800e9810981c0503011440c60400483e0318100c99004580d1802496210032a4640c1d001400701c40c2c0d1a00f050207011141e00501014001c20b044a5030020a5420400c0c00c48031940a90112540c409414a600d00724619041d014980c41c12507006142032402006400000300e4424090703030079440401804140d540ba5003005100c111010401c0d00c0e126034000c0a5000701240081007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 992522293 1250 992521043 992521063
    0x31f031a09061014040b090f04140a03270503030a0e04110405220209040203010608010303080604090305040504091b031a012103050a05070605010609090c0813020d020a0b1606050a020705 82
    0x240000c0c0340c4d146800003402604d030021200341c00845031070402c11040302c5400040c0c0250702071000c030711740c0444554425440e41c01092028020070104550346101c0b4040005c2c1e03005031140303400992070294841c2c0003e0300315800000c0e42d00000e1400c00300840c00b850f141c4a032074030582240180c2480c2c1032501012550300030034409180c103008070b454101b654030012901101d05d07004008000310755960b181d900c00f030701000003030000742c000034004000900c090a2610441c1d164a8041e20b076607040a1411080201a22200c0c404a510203115500d50740c10014560611000e1071058208084413030b540e600a110700306059004085405024107690741301040d00c4401581c4a40502d080b03a564035655209079540d00c102c284c000c00d9945004000101164000e00ca8400e8408000c8180103007c2c904804403001c42044c0c03268000084902c0b01800185010003008644508c00b500a81615940c0d01051049422902070401c601e03078403000c0c40c403c01c850761040c960302c9001d8000450400c001922060350741e0301400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 992523543 1250 992522293 992522309
    0x60702100501081005100909080304060c03090f06050c0706061401081b040b0d02040512010e010e010207050c0904030c05030c030901090608011215020f21151302031f031a090610 78
    0x41c0c0420b00040c440f001c50b20247c40521070a114420940c603118016500840d8240d41780d45c9004400890507200c0e0142c462450340211002042103050b464a50040c00041e2807a99825400c018050010b2a50700a9000402c45161031040c00c0d03107442c2c005005140300421041c040400102003000c40c07460441030b40e0598140c0c081c42502d91842031401c4009115907041190f20208803110340340c94800540224005e00320000080c0880014005201e00340d003d81c100040640c3c100c4803101101e8100100d90384c0e80315009140c10f0a06a00c039485007803c641c8a07030412800d54100260704001941c100740b100c0000d00070b80c900040198900b0b484031440c6a000c81005141180c521202c840c000a10f80580300917603504550300d503131007968140d200d070b528081401240742c6201030000240080742c980d081802c240300160820740310348442440c16000394001880c25051114041040e003440400c1280d0b0b80107148500c1900300d01e01108d500d401381070b0304010105002c03507002030b0404c514101c1d2141503204031a0b00b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 992524793 1250 992523543 992523551
    0x30311030904090501050423030d0509030f120103030906090e0705090301060306060f030606051507141c080a0f0e1903121424060f0a0c02120607021005010810 70
    0x12010450a520a036401c440d401414111040b00f4080190300242c007070f62254081e401036000715106845001c50f5807461b00d820b900148005803e5403850341180764000c0141056034034000021036907800e83d8001424441c19000c2040044c0205034104040310003a1544c1e0422540c4685094111405544001c28040402034003140c1d00010740c600350030100c0034551140d02842030035100c200c0d0042581c4a48001d1300e0039401d100d4001901d051080e807000e5895600c50350107107441e28544441c150440309190209140c81298014651800200e8509012004c1c540c0c0d0742c1c9140c1000603825095882c81c40c041602e07549002e503100007041001884076010a440d025400c588881402c056440002c144203900d4000d052210401e10090044491481140114203850715040e203560200c20000b0710469540e0800003c010b090000700502c03018005c280d40c44c0c60f10038280701a81c0e0100710606900d00a19025910140034440640e406108250007101d02001c104400e601d0004030307030740d12480030b010740385d8881da9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 992526043 1250 992524793 992524817
    0x10209090106110304210f05010f0605060712030b13020f04140102031813110f0903121623011e062702071e0302070509013309050d0302012007020a0303 67
    0x1210480d0385034a41c01c0790451f03c40d05011f007000c501034202482d0b01200c2c941303406004255803920505580c43c2980040d264807088442e41420340040001a05680d480441c41040c1490000a40010000039200311103080d181d6180c4004201a4200304002d14150741081c0100714021007034140011265004031418090268040d001100401c14502e4130001150006001090b410045005001e04a019400c9501c0c040c00d0041d0b800302e40c01b50b481e00f402090b00ba180c0180101c0c0610080421190700400c0d10014141240282c1d403c41c1c1e52900f480180840707058801c02a641d8500c642c0e00140702102100310360600c4498480c0011404c8080b0f244ca8503404210201444080c5004071141e214a80c03140007039080c1428081d54908551262920840440c400820101a101c06204865010341d40c10502c50081c13880c800044801c4151300d03c10883d000900103840c0d6600c4021284090107500001420646500880340711060200c1801410504014070001a01c442c1602011290035141c05070300004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 992527293 1250 992526043 992526089
    0x60e0f16050c01020d0618060b0d09030318031d0f061e040806091e0714040e2112090d02060f10050d142509020d0914010209090106110304 61
    0x2600d010741c02d6a610204106a00304465400784007a51a003926020310700c600a450340f003d0354141d010b540104030041c00481501071071504000c0c0203600c0b83c10042100820720b0400c1041d19442601680000c2201c51007452113001d11803030200900342500c0040900310600b000c2003103071045d0320040c0c01102e80d085514654202c100f00fa00c010308a0b41c01a40c04a003402c203a4a40c0e550105010b6070001c440c40d1181e0401501c00080b03420803540e04800700b034101041d803020070004000ca6005600c1c1e600810405000080007881c1020070015014410303601c40c1c1d115220000c40e14801041e40c58240d003d600ea0152040d00000c009030300400c5848100407560750700e5442c03030200c500c544c4855005060800076000300f0103610b001c0031008051104650501c50888000001c0d090540d010b81410301c0030003014000c22079203800402141c4921800401c951215640d0601290002e081142c2d1603540400c09084c01d01d01000501d004000a01c1c00045c8220380e003c0380c41d01ca2085115250040c0400101d4001c051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 992528543 1250 992527293 992527297
    0x190303052502040f05040302060c070b07081e180c0301020f07062d320412020f061807060807050d05190c0915020307051b040603050a03030902010201060e0f1605 71
    0x395000e8014041381c0000c00341c1d0400344c401510124094040c20380040c080da1218015074602c60f401065001d031a4482e00b00603282000054100e0f45007500240c1c0160051542488040c0aa918041c41405811400d5152424600c3c07403005144242d004010303508010080505071440f4542010f400620a8007d0a2400500c00144183d1101e40d40d01040100440c00c00c0d8042c0401c4000e100d583c68901100c65041410b207444e03141445460301c01003000c500825a000f2140f105c001085c01103400400d0500025441c01a007158100141e41814036110340710813040c804040200751600f441c140301d0801083c0500300b0300842c40001200c95a41d4009070242115090340070b480302440004001111440000403e844420300400c0b0301031400c00500400140f001085446241c1c000d006000c11041003030180e0400f028405507243d00613201c50001c008218280494a00f03c0e03c03a8800241c2d5440324800a400d46107142e0100c1050315610b4100071102e035401e24811313404103801c960844c82c0e00c21010140c2d614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 992529793 1250 992528543 992528617
    0xb0406090501051501142d0903070b1206150712260402030d14030c07030c0606060302180102071208130e01080f010e0d17062418030d0c0b09240619030305 68
    0x940b01e10000000d402c0140002002d40f0f000c002142c425940cdc03600b06008255400c103d480589807410040d080c08a400c1c0c4007010b680b441c81345050300c40308204440354000e60084903400706440381480240802c51408008525041d009404e01c0d03690406005000c01c55808020411420300703c0001e00681014810030484260302e500031010841540c0300e50000b4001d40000c01d000ca10084c3e0300724002160741c000079411003101c0c014030481c80c240980e036840d03180d0307504880e055074030b0034041500200700007181c840c6071170180002400074150414214405030039030301e9000351910b154000c04240d85e0115440b00c40802070302003a0710034070031a07129480403e61090030000c0c01c15030b801981c9140901210b0a5001b031256a201c80c0081c03823801100304c100350f150580107110740c000c5402044d4040004007a8020258030a01500c00e560f04d031084614044041d0310154804003000100750104141c62400e01d01800c000720344405a2100f1f1829540c014001d84201c0d490680101141c41001c400c0001d00a13001e142 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 992531043 1250 992529793 992529799
    0x21c090902040e0a0e0604110f2209021008040503090904030509030714120c1c032006220c03140132011d040b0406090501051501142d09 60
    0x286660f90142240d41e40c105480c0b119801e400c0c0500d1040080d40000d505000719000140c2c080040501010041141a820700d550341004e070386405009800301d00e0040c1d94035400c08030004180020b180c41003004a1040b400c4103400e0061034014080415000010307916402c03015280c030074103500c03941000d5610b07008a18000d1f50601c10910007182d03010080c4010b2490b0441540c0009040040f454841c2e200c407134083c40c65400001c00b0710702515a0f84a40400c40301d050090610740c054210b00d2210102041407070900d80318541c0070300103002c52601300c0e8403403541e0780d80c50950340b2510107000d41c0d804881001c6444040c000d90340c540c02000c80e0b0102980001800d1011344410701400d4512101c0c0c98981c14047c5007900d030181501c000040a1407011415180c4103030840f0b0326640383c6d0b60b03507985ea03508240240054a11903980c45001000075024407405028803040c4009d0314a5031001c000052100d6803091014207003607010312001d87c0418408009110500c200005210041030b807440784c01090180e4105154 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 992532293 1250 992531043 992531047
    0x3050a030615020a2618120a1a06100c1424041b0303140c1603050309090106030b130b030a0203160f0b0a090b0a11010c030b01081303021c090902 64
    0x841c0b9400040b10601c41c1c1c071a80b070503804200d41c00304000d50a06402006030204108001885074a2584e8040c1d00120717000802001940000348001ca140030303c2842d08940f650506603110f441c130300000b40d800303a202e4400c5441c0340d442c54220a00814000c2020402046a10117440008000c00b0912150710710040e8041f40aa0321024954100c482c08010343e01910015000612181029010f181010030b40350180c803102203100d000c4152070b00c5548522003108181c040c003c024150080840400c80045015000440d00c0c4d0440000700318102c0d8060307003d0340034140761584148281c1ca4810328500c45240803140052010616004681003004012000303602d400340f54105030000a40c2106541600c00b6014001c9410ba101e03031018086100f20f51040c400709140050030015501d88a001303051b8003210740303412000d82c084032040314250380f01002a080441c1d1509000050795900401c2c40d54041c52034405029080e0494a0194a0f5401e1440724007040ea114001c21100c1401246140e0003400c030014115 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 992533543 1250 992532293 992532329
    0x100c170a081e060a2114030702120105161409100e03060f01061b020d14010c11030a0801150201090213060810020702211203010e071704122312040308091903050a0306 73
    0xf52650305c5203204a2080110780e0b4485d0001c1c005100341440b4406370307a6407180c01140040d0954960106d07106ca48a18442080451800d482c0c4110884001201e6144e2801301c0c50010201810840010074816a070707200000100b1001c0e41c80030100c03c040442506e82c02010506001042e030740c2502c4600505040200805442c01c810b05502a0004801907512804422128400b03182c0b80d110f2502e8000c00945080c006204041d19804032288140d15400001681030040d404201d900310984400c0d8052aa6070380304200d1030405204816810401080c210310b04000ca5001840404000c0300f144001d55203040440300101003009131030300041e09022225260f43e910000d0b640913903070032944140014449a203c003071044010308124000d030307881003044100e80541d0390300316a030b81d02c4610484006100803440d029100310480c0284800700c040c210042c0107141c1410040c29200001e002e108050b0b101018142900c069180b0104403a58186000c0755510b90100c41100941419040b24031070306440800c032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 992534793 1250 992533543 992533583
    0x320030103082a0604150b0d121b170a0306030b040f02040b09040b0601030c0504050d030e0306090307200604051507030f0509100c170a081e060a21 65
    0x3602c40c3e0500d0a074452005403689500d03015914908a1800c0103610400210700000c42003103101c0c0e4100480e49000480e0300800f070004051500303003070099a4415455507071074204c03070f4811070b0001c0c01c2c00643c3c0c5e5003201900f00c2d82c44ca41d080554901c85400c41d030001c112982c0c164483d4010500954010306c6803a254201824002c15441a6920481c4100d02d01080c490b03140c140604858402d0b40c12002000541e50782c80015030161212820100401c0300802c1b010440380ea88000d010406402a0b035801c62000080c03090601d001d1019100b0605944180a80c034001400d8000c00e500e0348000001c001c6e02280c030100401c1003130180740c100c0c46d4084000081954030035070380c0d0040c1520745e00943d21415406a2000305486030b02c10b400c1904c2d0801413007040c003c1e03014040c00000101521403941c0286120f000d0804aa203500982c401d000010f1030388051000d000e200851007100200f02d11211402c42c00c0440018030031503210b10411001803484140111641c01c92400041c4803600002c241000070342c45089 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 992536043 1250 992534793 992534797
    0xd030c05100504031d0f06030412030608241b0322020a151205040528080d090b01060203040b120915040602031f050303071106160305090406091803032003010308 71
    0x11260660704d01860034402486c2140e00c928400d080900918a542c66a4031031f11100c5520907000010b140d1200c03800078101c2c01c01c21000400f42800981618001c0c801c0481054038003001d44a00c549840c000c0410b00c01c00741d410101c81e0400300341c000141c1d090b40122940d1b40228134903c000386d4804010000011030301008554038800000070303030b54070003c1c0c581101e0400c212070095a000d00301e5070140b000b401414014041c080805000400501c541112540d0b0310196030b40021641c220b4103865441070b008024000081364007405050003c0c504050401c0003568850054440c44d010172402032022905400c0288102c4007900607001d0240d11501d02800c0100c0a50b0094440700c4014007403480000400300251000c0d401e503000100514608103d544540982014000c4010b1344840104081c030011508068202c0006200b038035403c0d118410300341004102e8080d80c2c00002c2441c100032002510041c984001d8200316894280092106000300580c01582640c1c80c02c1129090300200200c280144000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 992537293 1250 992536043 992536067
    0xe0a021f09030c0e1509070c0b060a03060e1506011403070c03050c0a140d0e01090e0c0408030301080d0e010f020607080a0609060905220f060504050c060f03040c0806060d030c0510050403 82
    0x5c00c2c440a0150301040c00301c410002c0b0380c4c0070009100c0002240010310070380c01e4140c00240007001000f030a5101c0c2c85140444c1c4191064407000ea00c218ad2040c0c641d08044925070b44104242000482e00c0e501d9543c210382d52100070446020007601403580010140210155080c2d030ba034a004032411000285881105070092903004e440c1440b56600031100d60b8030951005001e4407040e034407130309200c1c83d00d00b041a02600107006112030b60f82c18040812000402c01c00382d8002c14a90004100400c41d100d0060145075220081904000c044450080c40341d400140c1680c05c80150b02c2c020341150b0300e0702c83c14001405603820064415042080002e800d6074030341c1020f8020b9014410000d12814241c0c00c4035400c0b40c106000400703404c42ca4800d140400c00e29845140d116015405039405030000c0000a4020341c8011899601c4040100910003031100301203801e801f41c5420b40c01442c0300c4c20f24000240124031907030001401c100c0104407000410800f40710054650700503070340501160400346005040001805 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 992538543 1250 992537293 992537311
    0xc030917180f0307060315051807080c030f1503010912031401080102040602070b030c0403060510180c02061b12070905120d08190b09010e0a0e0a021f09030c0e 70
    0x12012107514a400b0000c1c01e20900010700512800c1e142180c20b030003405443c5402007841104e0b041c00503140e120400710090030345010348640e400749040503000c0d00d40c403000f51000c013803040180200960613501c8a200c5030041c4200ca5100031101d02070000034050060180c005115110250080d4400342d01608524011314019009212076a21950320740c1c00c0340a40d10035030b00140d100704070400509030050b005581041c1010380c1c2e1880d20746c60361204c00954005607030314007050a0345041003090842d02903c40f40e003400050420700412001610096a0310390142c242c0c903048106055204104102000f00c2d1b403816105980c0051031310300450003500113581489424001d15880c0c2d410b2030f00c40d0f40032a0050100505885500288c1c60f103555950b050a03089451020b160b989000d04003050780e510034482e00030a5110488001e03460059404000d690804600200c150f200c503041800503541c1c041c40c000000800400b04062241060307003205c8044490744080c0035461000004118205480d000c648118088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 992539793 1250 992538543 992538577
    0x121e080d090c1401020c0a0312050d0204081e0a02010806091008010f05042d0b072c01120b0105090d0501111b0105012124110c060f0103020105030103060c030917 71
    0x4401640c68a1b5a201019448004040103200103030362034103041701d6180b251801605250300940900101d80c85900700c039003544c0c02600c8002009420800440c0b500301d19402500c9c0c0e07100b607980040d08030100904898414407047c0d0005244098000882d0002c0080400910503520015001c500501e01038400760b0740d041c19a100d0020342009203075030585020340c1059444c0c3c421500c2d10f980840e40fa02a1941003003118030004500600c000c86850082d99001c140b446542481c1e60b0009014002900107001a05041400f010740350f03030704001070710b030940c00a503130403c80391b0102d2038024010460b580808075814800301700301d0f06002c0d0b0400030782c002016200003006103980b80c00c804000d042604c00b501c4101a095102100017800188070070780c08c032441a084000601d1203150401c01c2e21090036200e05c0709040840d01d081c11003000c010381030700911100c09403400380d410b54000070070500c01400080c0c045174076410500e8a03035211f039104c00c1c8015004401c070b20349850f10466135a046d6002c0c00c201a816040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 992541043 1250 992539793 992539829
    0x4031505060108090d0e04090804061706120c12070504091a0a09020a0605070302010914030a02060f09030a110304080d030504152901030e060f010e01121e080d090c 72
    0xa00b03465405851280001c000e40d40241781c044401c0702c4814103841d00301d5224080c1c42c0000780104042c0000d0451030f1a204410404005082070080b0001c1106100c1d00b42c1c45a50301c0090750104180c1c902030310585003070003441e04001c03040345010215404150007a00d00404502440440c034044d902e9285009241540c41e00d032550341209581d4000406948408450303404c000b007900800051800511900010030b420780241c40b04280d010124040c1d0b01d19400018001c03130526030511140e40c2c46410742202940c1c0341001c07402c0a90f81d00a6056010500c8078400050000350420000d440040ca4250101ca001540080c4001d024104c240c07401c0390070004002c4c0043e0301840c2c1740150030fa11226106181d405480c584a07103010014250b03c0c6506040d40c401d042440507201303100302e52007076502c01d1082942c0d514050020a070400164440c90300040c80d020700b100002c10110802402c1130f000000b11142c442c1a00b40380700324ac483c80a41007402e03441d0040d14810000e0110f40681124000c440002c0c8002c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 992542293 1250 992541043 992541047
    0x203090901060311040905061305010803220e04030c08192d020a1e02031207021801080309060a0915030603050106090212010b0a09170c0f0d12081b040315050601 71
    0x301c90888541c001c24442800030200c2a1f0105a1200004000c0c4800e000c10410a80c00c40304281c0151030b80e904000f0362960543c206030848129403402041c115070780c51030110302c0241e002c0045e10050400c903400c2c0c1c0d42020b001c80001038407421086800100c000760111900641040090300007030b400080000d100c40203c1d40040d8002c0080800760700503103501c1500341d40e6110008040705045c02e2000f009900e81c0e026071010442002c00101040d4001d903942494010003125a120b041c0d008044e4601100501c0540004400d40343c0840c416140350340c5a03c01202c094036400b82c960002018004103550001300f555054110204070f0b40290020002c40d510b8060702c0d000c0c1d2080b0022031101d003041200401403601618010507803400c540c40d01e00c00841c3c4038018074100c0b0941c04807040d0342d603101400e0710b049860085000c4c410150200c030030005524159235030070307048c801e14800c500910003c42d0003e035210100f48005d0f2a189040340b401ca1740d494917440e01c00c191001c0780b100a89000d00d003e00055040d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 992543543 1250 992542293 992542301
    0x2040b2706011e0f03060f090203040c050607050a0809180702030901030e010c050f07061b210203071d2110150b0403150207020a0e0103110102010908030601110304030f0302030909010603 82
    0x70316003641c000f40c0000032900559104006890001c20150380b418009445004d43c0914000342441c0440540c1d64202410031721040305481e0041c0d48134001c10002c4c05c6c00681e00041d00c6081c2e5600c1014561144441c000086400c10300325484010101d076075041004081d4007200401c8100b100762800c100744052004034900b25a0301d00302e0900458403c012018085e11440060b015403481389801140754441d148000c0e90075a41c40580a000c19140c00a8680d1000e4400c400c0040341d2031f0280c00c500f5868040300c0104a55843d00640401e200d100340f5810407510f420800142c49000b04806402c0d281004143d10303910f0600300389120005290244a101c0460741c0c0c039040040b01c02170003059007024116200c2080440746070050300f0301e20350708212403001600c408041c0c03001002d64102e0200c0c55031442c00c103008035090050200c0c0c116454851000005403a6006584e044034003881d08400709a64082800d1075881141c0000d000032006100c00742c201580000200350840d001d46102c3d4060760b85d28810340c103503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 992544793 1250 992543543 992543567
    0x118150e1608241504080105010515090d02210f1e070b07060507051603031505031501090f2019090f0306020307031113060e01050f0409050402040b270601 68
    0x1a100c01050741061648251402c3d00f400801031001098071280c40c05104141c1c041e03407010110740d454500400403803400b610325410340072448141030b240c510200d0002c1d02d09044500020310a80c1a20031102c031038a40308205504d0042c00d4412214000c0d0001e502c1a030320642c501d914800302038a09900c400d10308020178103034115100c44120b40d05040859452030040d0070f00402d0882002428090500400c1010540e0411240251800951040b03803805040d0441c031284c0055001c0d50091050720066005020054111034480d80e000440070358002d040030180510a5040d020302048074098240b95034043c1c018400c0d02d491500c036118540480c0003c0d64820741600c02d412112a401e8400c00115a141c1c004640c022440e15002440a03840c0b150040710760804920108600d5010005100468205804840041003400c065090105640c6980c142d031041e030081a480300e842c1c8000c601191210740150200d20801030066806280302115072031140f081c0b4030010581616600840c003a940149000b03221 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 992546043 1250 992544793 992544811
    0x10b0403030905090c120403050406020d0807051e1c02090f1008131a01030303051812090d02040605060415020d3b12030c1e060118150e1608 62
    0x340e0b5140204001000b01c0082c04d000012074204020000e024546c10098801e0f03110b529020740320742c184040285420b080b56582030a11240d10705000312640c100003901c200c0030405450300c0500c2c1481001007428006d1203524000012a40482c040b501e08a030050080d41c0c00c03d42d480c0402d0301140e010806040d00c0311900310049a0481c012404400c98071110f000824001e801015502d0140c90400c03001c41005d91007640001e90b9041804603a004014014a8440c2054002c1881e80e8814035440d2951160440c96481030f82c1e200410400c648454114078018a001040103454640d15076022140000c40c4407480300502481c105084000c0c040c40508080319045c40d0407200d4180903185108103061100510840110094004070340e6503250b40c4442c1c102e40c1074030040c548400703800910902c4c0c00140101100b24190410116000a0740003034000cac1184e249086c003070b0342d0450740c00c0c218000f0b080c2c0d0203403000d11040d90800400d0a20900a41c1d07400b1b100840c000c440c40d558084422a483c11041d591080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 992547293 1250 992546043 992546057
    0x10209011b0503040305030403150515030d03020a0e0307090902120a0b0105060306060d0e070519030b0c09010c1a0103020a06111e030d05090109050f0604030e220e070e010b040303 79
    0x2101d400c51008650301284500304881c0b4140d140d455607459038000e0b601c203e030300089602a84002602c1c5018a6030010004029010302000c400c3c0020344a001c02103440040540c04242c220056205415818103000064107071030381c09448544102c06420502000c3e40501e00903403803004542e000040c2c4080c0c1c0381d0000c060440c680d081004210079584040e210075030259041c4081c55600e0640d1258038034144d900c0c00140452031800040c801c140d45000ca501c642044050001c00125024504460303000c06c13104042c03031f40c801100d0300684529912541c003901900f10056001030b500d42400c42d81d8143c9000b1101011016900d4030116800c1448403207481d003a030403075181501d940c941c5901141c0c680c0301040c01c0d0380c00c1c0b1880e2403410342220000c4400c4040e6a460b40d41d47c10900c0340500071649450440c5001d0082071420380c801030f219010207841d060242c40d0041150503100e080b6034000103040078800050042201c8090266a115154041d84020003d048000104010b07414201c03000c07170740d05071241d003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 992548543 1250 992547293 992547317
    0x627031c090803100e0108030703050313020a03080304200f100e0121150e040807030806130c080a0b0105041802070204110a0914090f01150c05060106030e0f01020901 73
    0x1040d00400a4000c100c2651a60320550000c1d042c9030103144a50401c01030409000e203415091300707010324181d000c0401ca0f0010000500445e501500710b9521000b000c151301c00c58040d17803010403998203a81d8000303001144084203200c2004100c4084003150208100c0c0808003000020030440d0301103400303550980c044a010390003108580643c0114030f2a0405040c206582c0c01025190125480302500400e85640e840044012150076002040003038054a20400040d01d004d0380d80203a18480c5100c0039080c400d080f000a56a550340b11100d040700a2400420312540e0180003000d0030014050320b0300303100142000c08a10442d48036400765022a0781445001c1c105568112440e0001d41c405901a40c12580301c905030b00300826554014480300c81180d48034254070341717005103409500c0e8072201c500d48a030480380b00340440f00013010002ca0550351414440030054448a10a4a0f02103d61030020321900980000091290b011f921032020050f044055450442e8106049402c03842150b030b12601140c80300030342e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 992549793 1250 992548543 992548567
    0xf020c010927050106030609061202090f0a0e1006081b090a0c0c02060f03061903020d14031b010b0a06030608121b010f0b0a080c030a020907120e062703 67
    0x1000e20b80c6000b212002c496202c0321901d0040c1c0310260480c03400f09840d11340c00c000d80c682c01d2290310001d0000705a0b00461110301c6d40020311001014001c14a000a5580454800c050b5503102e401c281010000715813070342c44059a510b01070891403141440c20701947c900b1424192596030b0030300b18880010040705040e07032221043c5008002003000f04c420400d00d841c0d20300c0161500001051044402c0616a4491416008200080114081220f0000703510241040140c864021800c0e1859100403000740b19206000304c07030f155000301c141c0d403d80d40802c4c2119020290781136101c0b0900c040156004003085841d0030017a400c0d16411b105a444a0b44510341d04210000b05a01800e103841031440010707561410008000d0a403140810300304000b99032191184110b01d002264403000306007810150440c1d04a8800181c0c6541c12014042c2c05039000d003000400d02440b88140e0b41482085410070003014641c1c00105503564411036800320b5511805408040310000d00704d20082c002d019100540c500f41010b242 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 992551043 1250 992549793 992549819
    0x180e060a0c0201060519030c080a2001050913090204050112020f09040309082a0f0f041109030d0c02030606180c070804180c0e040501080a020f0607051c0f020c0109 72
    0x401c41107550380c400c041080c1e40c40c80050260015451101c60b40103080d814100d82200f0260f121030003c1c1e201210302c00014400044900b124482e080700c8030010f09803400165110f01c0703814106940000303442d60606041a0300d41c480c000c41402540c0402c0030380e07240c00c0541018000e034400030b90320203510014142c1d507182484003158014401d00d089242d02d9a240902403030314007140d081c2100503e56081c03003a04114034001501103010b00710382c00402c1641400200e1b90020140c1ca0070790086459441d43c0c7c440d626400101e404105002d0304030391070483c031154020302c6140100c408070700c06d015000c045062487c003145400310050f44060080c40944a040c4445003580c001c0780119280b0360144400a084892003411034801515410045100402042c0c01040e61020304880c1c0d10843c90000113100415000903480ca03055410b60303045a601050a000801c0e81c0100c05000f0854411f00d0842d03200002214010b85038040ea03a2640081e14104100030303030f00d49140d181c1c00c3e400114442810000682c00b0b00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 992552293 1250 992551043 992551061
    0x4020702150f04031101090e16092418080d05030a1113291903151e0905060f041a030a1b0f120f020325180e060a 50
    0x35402400c0300c0c0310006206402c04080341d008600045020810701a07001c1c880110410246071441170142003880d00320329040003410040303204407204203000125004442c3d18002d422164841c0224558807241a490144034140c0807001613258041115010b4508500c0740070741e60500d001e0300504108a00442e01ca41008000f03c84007903c900c0600c04a401c01c5008000450610a6402565080c0182681459078000082413001c20601914034141045025a010311281c0c0c140d100d1040590001140605003041c650182903101c0e140c001289050f14140e020388075818082418030654440c00c0f0380489001312043ca40003009060301d00118903080e4065030203004040d03c2403030082000720100f46000010442226500d1400c0c400ca60300300348140707801d001800c03112080fa4189040c4202060114494140103100e0034010398442c0071950240505040608140f01c031210452201107580c0071544544104207030101c00311004030b400003403401944684503094000384074613220a0030340c10040c030b007000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 992553543 1250 992552293 992552299
    0x20030706020c150405010b090c030402030a060b150409020c0c0d030206040308070306031e1e030c0f0f0b0c0301032006120a0f06060e1201090201080106050c0106050604031a0709120204020702 84
    0x110760602140d4402440f2400380d8002d100002d480903d1038180001d0f66006080011528000d008010040e540080e461010346d41c4074901241d00400c1c01c0201c0c201035212009000189400f040c0440d45401c0c3d580030745078030840c110841d01c05062910a01c051810303960703801340058000f4000140407a000d04180354100c9000d140000700c850362038860a0b10410240070800e90985900c0c102e0b0700b40403400c145c0568400b2042d149054403405941c001e400303182c0700030b0b000b01855242c4107040300307000c0e51900058685802c50903d480c00d24103a8106110b1750f20900040310355441001d4441c05d408050000d6420180015046501d05012400c11000140d002400b0a060710b46544185c40784003064001c4030003d0146031541070a4009941c00c204070a03c4407807134180f83d03078500032221001d0303a80301849034111a445c1c2030070703036440c00711900f514091320742a08580d030824030000c2c0c000104038404e4030b4100c0303449034641a082d1035103c00004a074883c1c110711500c104609006a0b0f00054035241e401480c0d128402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 992554793 1250 992553543 992553553
    0x5100e01140c1e03190204060f02011104053610030311030f03070e0a0906091d0a080702011d030106140108070e030705220501090b180403050d0b010c0f050d20030706020c 75
    0x30b845c00c0c0c0142d900c183c11007800204040ca80002260302402841c407042d0301c09400714109803d010203d0080000544407c1031410584a503901c40031030380ea0703a0b0001c1ca8041907070100c1444e00c0c0c0e40b401c0e00041c01e4402100010007020010034400000320a565042c0300b0090510710f9a101c3d1401102c14040001034651300481d40e600014030f20220b0301c54a00145924130004c5001d50100c61011907140324a08030714070b40c0c0c00c14210400000c20400490f50000d43c2424000a0004002d03031504000c00690070080c1c05620b00a4040380c000000301d18000000c509a843d0a80d541d0345100880c0d03440d0311844420782642c0300140c02e01240c5000d008a407244410b8802140c144204245040d050b40c4003079000c82d091030703510074060403035060042d0b801031883c40e50201049542031594000f44140701d19010308544503910741c513528444e8441c44142d46403a40110b0024100c4100d030034101c0e183c4600000300c40c0401c41102c61251085085449042c0401844000d54205103050700c840c0040d5104403140c1046010f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 992556043 1250 992554793 992554831
    0x12031b0f03070f1a07020c0411041802160f050604150c090e2d0901060b030103120e06210a050604060503070b070809030607020708070b18040905100e01140c1e03 71
    0x899244c5440391800f40e0041200140c460144421070340c0c40d4118000c1504100b00600206562a510354107280411a005a803010315004a00d90919a104001d019401202a04003070000c0040d42c18003d5028125070300012450702d52950031211401030383c5000c42c41e072810030482c2403125a40705074002d00c0210060b0000c43c0000740520409065811303c542c094032030303040c08030810091184074041c0002c40011803955045441d64004011200040300c00c101c481c61040c0e00544036002660182c2d560104100700c0d1908140003840c00c0e00b4100c44900034a07203404001521882c10f8001c0307400700c078000b0b0058241c0504010303c014059012903010b9601200400181165803400c1243c1b620511341e0394007600340b550400703208904003502903125481140c002d0043c10080305401004071b00040040700d0001d104a1285891801c00c1c004c4c4540394a0503152040c0c01400c82010340018840b405001c1103eaa6139a896050000c00d00414010507080c5014078950560405140c0003560020840060041c540710 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 992557293 1250 992556043 992556083
    0xb03010e0709060e07020a0519050c09040501020307030506150403080702030a0215030406060605040510030e151005030c030a0803060105163c151104030212031b0f03070f 75
    0x440e900c40841140c2d14401000351078643c0c4c4120750007a4540c80500a40b008a40b5200e54403c2d2164004030100a40d401380304c20418108204614110701600b00305141c901802c0881c000d400854016002c41d0a01001500506d445001119240704110100f41010709580b00c1c2e6034150881d03002240c06224290002003d6982c02c5101c0b80509490b45049649107040c2c81e01f070054400039840403050101c248418440355568440e00b6011080382d10300040c0030011b001d001c51500000754881c50740c5181140030f100042c0e40500c41082075500c141d044480c00d171001c1041c1a07030307444588805011044140046a40f542c0318000403d080712504415400c40011500c480c00c604039105141c030b07803a000c2c0e280d004044000e44460000341000103803180311140519101c0b0801400040d00c041c182c01c0c0c0d908400b0400011200903180a983c001e040700019624000901f50340e81e0255041070440e810b0420011407a0f03000144c5a403185404901441c145101556480c000380c1102104690600e003034107010a1a103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 992558543 1250 992557293 992557303
    0x30e0c031c090312170a0b0a12140a0b0910200f0706060b18150d02130e0906070f030c080a05090f01021b060c04030f0b040812070e12031315050c100204060e06070b04060b03010e 78
    0x1330161000d14072504219001c1c510f0301409240b00701c00d450400c020200445003210219110f4030200115503902d42c1a1364212400344220100145400d1a002c404954040c1c5a030180c5591401c11030030300701311a90b99042086407840c0c05000c6420300b004000650700266aa0041d00c801d50254050703480141d103992810310304901c12034501125500200800040c1a1300609176480d400040c2400c0002103008400200620310003001c4c60303030198481e0041201900200140441d414111001b151102845801540d041c120040c6240161040001241120301c0040031541282c0c0e000c8094071810707405694410030200001c20649000300103015500805825504651003080569200d07180d06009008028091121010b881380981c002e2001c40e11002090440d001540d0b469080b034258000110011034881c42141040714203801500c420114004040e0050b105480c0c640c0c0303400380d1109145040c00224016140003038001c2561101040c0800c00c00d52100004040140010521082c000d01c414a00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 992559793 1250 992558543 992558563
    0x160503030a05010b0405030a0b1005031e0f0f0a1502090a1202100320030411060c0304091a0d03030e120408070303030e0c031c090312170a0b0a1214 65
    0x16420000820070400e50318422036001d00f0394411880d042504240100b5500c0314811030052448402c003000c62080600d40035400000c0c13000508460105140c060f01d82541500586a64120720803400c1c0000c1c0c0d00804541410180b104000800b03100c045038840581c04032080c61000a000e83c00c03c0008095120380341c820000c0d0095400301a20300343d00d0700c148482a054034101104051404403100340e60350354000d00e2150b14440070031181d01c940703803030034026848001c0413482940301d5030004010070015000700c0648210b41000000300004118000600c1040c004003420039842940180d1210001e80240e2044241601403030448946005490380008160f00c240c1011100e42d200d00340800130541c5c140100b61600c040000038020081200b1302007941d43c1224020294030150301241c5030b100502c10415a0020f40d00840c0100130040c6054019101c01c1004200111a80c2d01c0d00029803041ca1038042c0740380c08940500f0a1410a161071206008031000c40c400310780c0c0f1810b4100f8400703540c1d4104107038000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 992561043 1250 992559793 992559803
    0x17060d1e1a0405191e020a050a0e040b010f180e15070905031002040e13020612040609060b010f0801030b0601020a05030d15061404090507111605211f0216 68
    0x40782010f0030110b240c41021405920080d20080544000950f13114084000e04103200c026800003074280300241160041d9003089404c102140400522062a0b140c0140114020540002e4507600d4003580f5054101a00950001400c940d0103000800d56039032109521a010394140c0c0c0003800c002c01c2144909005941c0b2000285044000f84034500c1d0a0019020510450104502e0301d1303c0c202c070b0b00d841428020400210340c1e9240c1c0c0c80c241551100030032244040121008000701d468240741c408018010302001307072000e500c1d1a2101d0030035405562080810a65030300c480409a02c0c42c0d440c452001e03001450181103000700f00c82030b80014820406020b0003084108007044550384104001e585825035070001c8100a401d4601c075181e4030b680710445081c0c9a101001090a41d00c0e075106440000c08144460900e11444620300d03200c140c14168001500c004541121011401c241c007203d08a500109c00c01e025003064a51900020041030300440848016130701608000d00003854402450540c0d0003650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 992562293 1250 992561043 992561093
    0x12030e1f020f0c0901030204090206090d0303021c05130b090c1c0b0901050c0706051e0114011409061b160b030f06041b0509040b1005070317060d1e 65
    0x96014404608810b07400001000012a10710000b10144c006100107809956111000415512a84c04075040580b001c0d221f40031041461030010020361101e20302d6031845070180c0d80300344100014002d0b03130300400000515540d906455100e03003420707290103462445184241c406000c100d448540c03007400303071200c8d4503ca104640e030181084600d640703004296940c0d5900d03110400c901408181d041d43d4800d5000300002405a5503440d403201c61460300400913042c45104400010720206101d0300c00b503258400e81e0350300000c1c00800c101c09041c0c0038102c0342c20703030144c4240b100c034051030b0b51182d020500743c1d50740d022180c80c00401c100519010020f03800403203080e41300004001c0481078503c149900108140c4040001a03080d001c14480d5075041c0c0c88410403c00d001806058581e220341040c0104c6c80700501280d0b6080c4941005030840c0d008202c101e0104e25020b00c00700e2441803050600c1c1c498100030301040c0c11800c283d43d400302c0154401400c46400d40001aa013000300c0d50710381d4030652030011703480384607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 992563543 1250 992562293 992562349
    0x509150a091a181807051e010f0c1e0c090c0206040201080c030609010312200d12090c0b0a1e0f0801080303071e05040503060a0204050a051912030e 65
    0x501040b209018580c0a005103000c04103005510150140d48144181d820f06441005245038900f0001d980d4041903106030464920815a5008030301c0c80e100c480262181c181800240b82c058810520200d80649050304c0d283e03d00c0270390b01858070603165a61107900104102500c5003d080c04032a10134034034100691002003004219600070104903000280502e44909519002000450320581400018008606900c0b11724142e0700a550aa00c0ca40300c20809040e43c03183c105100381c0d104412000c01d000100e000c014144070300751500c51050003035000f80b44191043e080c80c891000c164000500d030020070091021051410060b0042d085428903a0f50358508401c07403a80d4002c22001e03041e00168042e400c00c0050105068100fa0172890f03440304945e003101c1e18502500113940740d0003168030441c1c05004a004004d8803151070b900401c1501c1003284c2001c06e003510b980c20310550800c10030002c1103040c00e07103c00703003c07000c49446007803480f03482458200303480c203a041c012071302042c040c842c0180103160b801c09803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 992564793 1250 992563543 992563571
    0xf040b0607061d210904090f1203050604200703090b0c0f07061103030708070e030717011b0906050306040b1503150f10110304170307050d0306030c0509150a09 70
    0x1064507002c4000420401303889000400d0781c6001d1250318040c5101c0020000810307140d6070400c0f090607400901c070030507045880c10100c00d145800301341b460009241c000007840502d0300380300d0760150f11084c6502c002920045a0411349642c0076039130540a00c5680140001c0300720050008007000c3c00e008018016400110441904c1c10503160018400d006900d81e00255610b000010799501c410343e8641001540c84a52007651881e409814668241c0a18200403031050481e0400305041c200410080200503554098065110300301c1c00c070640025402c3e4010400c1034441c00141d40c000300001c00000d07169128a0000b205071001c5808054450000710802010350800d948420218406803113582146820100160900c030080001d50f090041030b21403007c0601080003501c0142c030386030152100510780302e50216a260465202107500784a005e940110440c8a4040c1c0002c60342d100c905608a242402c00f00050300c40c0003802e460740c509104142e100ca40d5a40d01151004205a10340050084070082c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 992566043 1250 992564793 992564831
    0x8070f260103212c0d080a020f06150d03140f0a0804020f090412030e0c061303020907090e0c2803050618060d0602030618040c09060e07020c0f040b060706 68
    0x1401442104d0555503a80b850703800b00100403407080340001c0030034080f810006018250b01070016200440200b4040031154000452801583c507141c02c071061035980d5080980062056456941c220005801c0d040009000b050503131002245610100e00b01450490841c01c0391f00000b51400010320000184010b40c241740e42d6104030703202c4c1500c5d0708125143c11384520003185011885102015641d8070041e604c58010311404908a00040959558203040002c043c0800258001607125008240100345154020b004800032114924109010b030303580e85084003600d0700101c10110741c00201410703928964448039184002d10607103031000542c1c2c0c103200c003c0c0040f03000413400307501150781840c0600ca400d81d0307030b80f0500740150b501103030145e641c0d603480e4003283d2500180180c140300c0185aa01380001c004890f4480403d450960354100a9164cd07102004000002542c0f00300c0982c100c09051008d41c200845610030710341c805040401d404140c2c00125034075611140e019101d2581e41c0740c62000e003800c4005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 992567293 1250 992566043 992566103
    0x2130b1909171203060f1305040506010b12060d1a04050d0207080f191b240503071704020406081506030717060109271505060108070f260103 62
    0x4840541500402e020766124421183c900e012080400001d40541d0f4003106050b014034041d1000901c420041c2c006030290170103440441da20300490002083c0c0d10718810a0766039001040320044c08a84505050100c60120700c3d106449240300741092089242c0034080300743c0601e200704000c00d060000028024208640f50f00f2451031a0011000031100881c0000e5202000603070800a2000102a20741020034003c2c9045c2c810342c04401445c0014101692140e03162400500e2802d00700d51700d00301c0406c48042c4401c482200c0031456502e0341e49980e000b045646684988050000228a6110310a5500d06442140e03d001113094800c04c208050a080c00003000500d29072031640d00f40c040d03520280380c88100500401241030b40c0c3c5d6400c50412050741e104040c020b88490080d10713869071039041c14510203617844680a070441c204008518030b54400c1501c148100510b07038400d000c034083c617403040b0385600140300d46944a021a020301d100e030f900b85100307450080d0b00c28403200c02100074080d03a00030b415080c45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 992568543 1250 992567293 992567309
    0x18070c02220e03210903190f09060509090c0d0b0a0801090510021201061b120504051c0c0504020a110601060e090a02040509010315021e041a180402130b1909 69
    0x80030100e14010302c4c12021200c000d805416400564550078401d00e140181105184031045031460b24184035080a078900d80c0050303542e90380c0b4040341c131440140d03894490840500e40043c0311f01c0000d0805480c0e80081c02c02100c800c2400b02d01446070300300042050700380742c000e400281d40d200c07415000c024081000d07044040400000707504085a1444252501c28140301e10350900105086507164400000140c13500a03a2080c2c50141110082d00001c0407074015000300d60140c207200031541c060300348009101301080d901203007090031182031105110203500128500b00c1401030044c003410395850140b000501a117040d035104800040078000304080c4150181001d01e20030b1040006001e1030b140d1012090660341c0000c92500c8414510101f640240318000064200c21541102e1829a408805c000c0041b10000c3d806081d0b0a0008981c00e8860700c0b90303030300090184094814003503180c20582c000e04500c000183d00b410142c1e9450000c02465070200c00b40807808510000180c0220b80c01c0001d100c0607000a03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 992569793 1250 992568543 992568547
    0x1b0604050307020f06070f0803010e010605070b16050906040b03042a1401050c030d0b01030b030705060d05090109020619080f130308100b04060e09060f18070c02220e03 74
    0x6458650712807041d408007900036240756000b40c0341910b9030300c211100c5c1c950220201001d02e806082c0321307406800c203004500c018500c1000001f0294804c7c2c054401d400d030441007044c030b5034440078244410302c0103d40302035060023018005d40100d40d850501600080c810511556039070326082c40d000341500c07500c03c0003400b2090b1070082e583c102280d4000003015607020205226000c024140165014065402084031610000075074296801c2d50b600301082468003a01e0500003020302404042d162803090155640040c81842802c00c03a19603500700d1508501c0c40070001a1030440d94021420962028a030400e02c00c2c008903068095076404502942c4c0f103192000d00780c4690801c3c2503050200100e5500103800c03c001074002c601501c000003c0c440080400a1076590303185d0313071550050700d81c141c401c010501c10303950000000d006003489440010040c400070080e640390300c6a020361071100c03000985183d0030082007032040030060b10781c200140c0407903103a220a080b6002010440034242d80c100c1c82c0c9820507800c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 992571043 1250 992569793 992569801
    0x614060c100f0212090c09010e0c18060403020303070302060f01092a090f140103050c12190e0105040822230111070605031f03050c0112020d060b1b06 66
    0x404220501c44003402070011401c2403500c1500710290080401d000264640383e81070140b80280000c0283c01031005458240300e51b0b130380301504c0003840001c40d01c1d130103900c408000c030200d0341f0510b4039a01c0440304001d241c3c5041546075008645981c10a0170203c0140c2e0080302845500520380071031500410f54a4000e0040c250200b0341190110307110035101d1131030b121201100c0321141c0100c04d4100030304146013550051030740c0c032050308034101c0e15582e2540c0400d1902020aa941040804590b0b00d050181d800c9162074682c040581002100f0360b0b4144003960780d80c1084121140280500c2c0c1c0a60b000c1e403403003512540001300740420304618245081458401200c10460030500fa03904c803120700840040c00c8007a503119030050f104a2303c012a141128051100301140c1143c00c0b03400b031402000b0700161041401d00c070303180b0301c420b2101d9070002410a501c42a04411b0562013000b032492010105000507082901000b918001c0e180b0355045040e11174400f29000d102004904141d0740c000d646040100500e0038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 992572293 1250 992571043 992571067
    0x812240109060302070317040803190501080705062b0605041409070506030a0e010e0d18060c02060d0b06190e010201091e050a05100603021809060f1009020c01061406 73
    0xc07440c81104141600443c4074403d044c003d50b420250003901405801c0103151030b183c0440594004c84070b4030b01380001e59019090449007841102d0596407000018440e1500300340800405810100000c0c01014080c07103401104040300810417415622008045102414101008241c0c0e004100840c40c4517190010441070328000100d1004841003903135950b944e900e602c091000a003508a481000c0c03503080017011129600700088d00110041c46594681141ca2001c0703c00425492522482001a561100b0203015181c0000140039001c1c1010300029200c0d100f1001c02e079a41c01c03508042c24002c801c0040100d0444d00010440c0484000344020840700c550f030781d03606100424400d4420848000800e0790b05c05c0003c1044441034164015048070241c65112144030003410080c003040780190308844008103007601010616002c2c0101502505150752010713503080b140c642c001c00d010030142c00c031040051840400e00c0140712400640d0b00104140d41030081c0311402002c80401d0f14041d0200f00700f020502d40c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 992573543 1250 992572293 992572307
    0xf0d05011509091a0901110a0c0c0e01030512093f0c100c06111201030c081b0d05070e130b060604151214130302010b03120a0f02030708122401 63
    0x3804c000140b25070b6485958001d40182103140c11240c41c804001010b40701543c20020701011107100f100d0050300b841e01c82960012a840a2000904540c0098404606214540090822018081c041000705003240000c40014607000d000ca8092070f81400d04034004c00c190b0103106002d4800503000700400e00020001c0380341e100758660741fa020402d55034100000c00400343c10401c40c0c8520114907603107406010458044a150030320040300e141e1810b4400180c40c40000c81c00740500700807401441d1083c0360740c00602900308103d0001325014040e4010100302498500401401109100f12018120099160009060901800291141c4001d103c00c03c40d400325071a85140042da14070340385039110460700d441009407031014441c02d20307090180104001c280100b214400064080d6000340030700001c00c0309041d125100807011000c8a5420000c1a03840b502844500380c00a855204aa1610360562a9904180c000c0d849000160b0800e80c2400b0201e100c041a8140602481c0c40c290032003a40364001800074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 992574793 1250 992573543 992573573
    0x20315090d26100f0812070201030209131410060309050c060a18080a06051e0a02090102191118010f030b06040605131509060f140f0d0501150909 64
    0x419034204030309112201000e8055004008031400c8860300b098544103d190707000c1d01a09044002d181ca00069064000801a4182c465004060319240702c580045010354070100c07580e80c22441c840c4a020349114070303210714811005400455021410704075428201c440540d80020304141c05e1900080110360003040a41c2c164604803186661210080c00546186c0c4240d00e02c03c0c8441c580100c0040c4060001c41c80140c4d491107040c0800c03280e500d009000070f84601084260036108100800907171b065816034014070507010705004a5101300034010308190000c0c00414221440c002401c1440014100340074a02404506890500308542c1406010741e00c034001e52001401c01d11800d404107100d03403134030342c04000505405003140112910a240f07000191011110039448030080340b1001503c02d000d4400c1c0340517206290281c2111900d8140f03e140c40c01d451440341944440ea07010881419074480f01d9400d2010301c40c000104506480381030402d4400c0d40c0c1da21103e0784030b0402191000262800d508403240d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 992576043 1250 992574793 992574797
    0x2040b0f0a0318030f020106061d0f0307090204060e030706020307030c08090a0b0c01050709060203090f010302090f09160305011215051503010c0e0f06160f11030703060603020315090d 81
    0x115080300208901928100f40e52824074070790220440240740d0300c403c104803001d1142e0002d0000702e985010031a07024405241d102e05984503070790800c0640c03401480e0034016080080441b085a0344a41100040368425407000f03001c80c407076082c02c4c400350030300b0b008080c02003130540041c40c18110a600c1c003501000800000074810040003032350090903a200c540600103802801d03071568445258000950080100755207000105159a03800a80701c2e100000310307409440060a06e45013003d01d01d00660194220f814482d80c82040a242c24030540ca0344011144504883e07070090400f1000710300c01a0032128103800c56071a495000d5100400318004180040c21a04207440c0001c2c103582e0b04601f050304001c84400c0a5165081c9818240c0040e030008140c20210400c80d6201380313601d10942000301078030501807201d030725502d00600301c40400e08444070300400c503000300e134140c81c50420316001904003030454008469159496000340290b05041050b00c46c0b00e43c020101c618a0305150f0225540c8001501051003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 992577293 1250 992576043 992576047
    0x2011e020a1b0b0f1b0a2c0f0409051e0c01090602121e070f05070510050309120a090f120b0601030902090a0c020f0331230d050d0c030e0402040b0f 65
    0xc0d62080c031940c042d0881000c9a01340381c407800c074006d0007050541d07200e803500e886401c071000d5000341400c110024140c0a400404030309039004058240005010240402d8426010f00c8050405d451480b443c1c01c2d640b581004090500049410b0015124003c15000082154407900c510031100c280c2e81c0486480c400750300340c0c00382003500c01c0121304120b1141c507400420b5140ca45180c0d508000e4002030003426102c0c1101c01805000144000b21054002116418801d6200620351100030704c01d64001e2006002c14070b032000d8204d44481000c04255070030750040140352030402c010400d0140c1601c2c165000b400c2440c1c01e21007442540c00140c4482000b8011082199132010104591802000303001100000752003581d03110104809901c0c1e0940e560240f410309000440782d40368081100c4582001502c0c5a901c0c41d0300d040b403080b202c00c54900101408141c014a80011000201c0d00070030241410a0456035400300100b40c034900203014541c00d203600f030300590043c003003407001c40e003000c00f5501c5034040c80c0c60701e40d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 992578543 1250 992577293 992577301
    0x30c0d1407050109060b09131a060f100c060605040c17070324080705030123040f0206040305012a050901080c09150d1a0904021002011e020a1b0b0f 65
    0xe600d21912600900c20340c40d2221100801c41075801103c00b2101c12241d00b665030b0b40d040380f91441e0a000303030030007044840c4150708402c0003032403050392980080000e018a1494440031010403d00180e202495021a07119003020040140d03d004020103800c0640d01805208805000541250395007800083e83ea103142c40002c501c20700ca9844155041c2e41000a0244140403203511140c0c0c1d041c0d0b0040c0e00407030140e0300b80400d07141414010f03070340c003991001c400b103114070031507529064081c0c00a001140c90300400c0e0b00940142e0f5500000c1e01c00341d4080d10001400c00704840280113181e8090489120b0050350094103110950040199440403000b030030f02120b2595000b4252001c1e1051500156000d01e074071003502c91064616000d001e200d0b00c00c0e503041214204808085d0703441c2000121807680100340130001001814a045c0340503024041b40004100b02103402e00385c80d40c505481c1580800a540850055010f0313901c4000900010289643c1808200850303c44000c40700e0300510041488030090041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 992579793 1250 992578543 992578577
    0x206120a05061f0f230408010f0507080f0903070206120610180b0a050f0a090e0a0209100c15140714040e0a11130b03060405061e10030b040603050d11030c0d 69
    0x302d50700100c040c0c0c10345010094914405c080c2c1007402840e55130740c0b0b002c0780c03114600d403039200d564055600d68548407a42d42c0ca8540c01c00f1041300003050500d00340018800000180c44500290110300f4035003010707840906e40102407040100d04a8401c0c400c005c000f05650410000c00100c000668044e2980030340d40311030407001601c1c4d51041d12040f0914000004c1c2202c402e5030f108030f0030341c103440c8454102c2e411038540c0c0d28204182e014401e07440d03034402c403070090541c0c82074002c1055003011441140640c02c0c004020443c0c904a0303080b201c401074560140350420418642c05182850208a103c071107030304050621458107208680103195281c41030b078910071008109201c0c0203a403001d0168010024011380ca811b420107054005070713a0140203a04004c003162461416a10324403806000105407241c86030410100b0440405420320382c000e1503682c5686015948880c02214040c50081c0b008100007210054014081480d9549030725040d0400d02c000c0c01c0500740403803103180604883c900707508085005100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 992581043 1250 992579793 992579807
    0x90d140c1501080a0311032104060b091305071703041a04050306090d02161809031209050102120c030403022517010e1203060a050d06090206120a05061f0f 68
    0x2030544680c9501c8000281d0060000d102411603201c0d5441a5503c4111612295603020b02c130310100140e258901421402c1c03181410f941e5029004031008070780340400002240c000c00e0291100880310580006820078000c00700034032402000800e440568100c004400d01d620f80c00356000300020401213a044d0b140d41c040402c10780707002c0c20004080d5030107418910301c026942e80040b000900540140c0030f544184201d030805000458403001d17071407440c603109120010010701c11031b44100d09102406089011000c2070703110342d842c41071003040010b075505940007003c012100e00400c5100b20312020001c010000b5070200d4488604045002c1d0102422000820904526040c3e00544145c000240140a0a101c1500600c2000c07500c0d0098440c54018100360300c403148801c6814a0704203a151504200606220b200040c3d081d00078080007904480c00e90000d420340d0b115107518504010108107100310750b03c4600c1486c1c5c008408603003041001c00c011259040d4141c4124a100c18031000700788400000380241c107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 992582293 1250 992581043 992581063
    0x20f0c13020f07061d0f070b0d0b01120608030703142511040207111309080306010e03030d06030809180106021c030b090f09070b090307120206070c090b0405090d140c 73
    0x5024005a4541c50f84642c000c82c04180b91104d43c82143c007001c072030006c00300e68101520421510700703181400611107100607000b0705225a041042a02ca07100a00c440c610440000c0e101040165594062a00340103050b62414000c400705880b08010000031015030301d001349043c4203c01100c0450350391504000103041e500c08175058000e400050031320100001d40003143e03869481120340c4600c0d4040707030100030100d8a4915004214a500b04086841ca40c09441e110b4008900101100d241c0402d4900d884240e4005a004031000c142c0410030300403524001c840309142075541035002c0320540c54040001c0d5134085100c9c42140c84112007101c06045403203034100300141040900510541c1c1012941c00003403110840b00051300e07004414010940c40021021038800000040050000038140700c506500b1420b5070b10101da205404011941c002070704403914100801c1c1a100c0001c103400e03c0c0c81800283d8400134504070580d0402d850b61102581c200d00d0b001c00c3c1502d6800413030b458510100035945032a180384 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 992583543 1250 992582293 992582303
    0xf0201020703173007031d120c0c12070e070c1209090b0301091709030f0d030e0c01050720040e01090f020a120506070c03031e0903020f0c13020f07 65
    0x250545001c180c0560040040c40f024003407126a5110040890400a0104c070100003c2c0c000000864081c500c641c00059010320300440300f500041401d072060340303440c2240340801081d800100b07156a4005c0d050001110000e01a07812003000481d01e002c80b5140c940b40c2c028105076424000c04100101d2160f006a440c070742e44052000100000d2002c058103800d824401d9002c0103003815134516031800d040c0100751b8078030350159011141c1040300e0f02c5c06040e46c20260701c01e0f4041c412480d040801c080104602c203058482070720002200d180c21160709040141d00741d46e05060180405c0904002221101d02c03040c58042c14220382d668a00046c00a8090000031080d07120a40c00e0074407000134000700b180035031552403007201e102445070b039203a040d044850304100c4c02a00310b80014000540d4140a036011010580c861f1030300090181c1e40e10310303141d1041010b18107a40915640e072a1001055010081e076011844640300030211642030381d002030750a07500c102c0411541600802c0d2444040110310990f0200d0b0303880 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 992584793 1250 992583543 992583563
    0x102190203190306140105030604090623070801210f0804061d090108150403050c070e1603060513150506210c0306010c030e1f0206070e0109120f0201020703 69
    0x180095070303600074110340d45020319401190344100c1e00a2040030f04840d0320740380301e01100c1550401500c1c0d58000402e140d4100da22420184001030741d0b40f050715480342510354070404035822120128000c400090a85003807090300d000500400100c2e8a03107040c8514001c003100000030342854103450340800f03510010022100481c020076000d4001119407207202d4840303640200302150750100040b0190230300c02d00d41030b604015a600c40040582c007400c3d91003402401c00307038501805280c1080c88c05074941c0c0002d0415400c103080c0116144a925120307075901440c901400244d0900000603030b0b4800c404001c1c200e20781d4811005d545c80c198015910000c0c03800038003294440800d41d0942440941302d8203041503a10501d4000342c4080c1286054070b001c0e40b81070f580d1407000101c5990070f58041180c10701e40740e40706000d406088612a00d0001c400382c42d452680c00380c0580e00306074001800700c070070018034039061201d4450144201e804802d400705156800803920b65081d400d600050742813840b5034001a100205d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 992586043 1250 992584793 992584837
    0x1704060501051c080a200a0501020d0b01113c06041406041101230d0b0915030a1221020a020c0a0311150f070c030227180102 55
    0x1640300303a04980054884400c0c4034408042e1901031200d001d40200f103004d090043c070603a40d119031415aa5140000030b0a92180701d0a0b030010314250b814801210180e4000800091500e41400341208041d030a0801104401c400c400c21610b801c03000c40201003000368402c4045241c004244450000081d4070411a01074681c83c48580c0c80351411a400c0c3d4a0030b00b00c1c921f14040440c00640079100c1c0c0d07000703003410324510484401100c225480304d040d201c1c00c0c030b40700310791340d6210311048000c140000354070030000707040038420080c03000c1100300031700c010362845071201c040301c40d07440100342c5c0c6628a601510141c0c510110107015903140d440107400400c1415410b42d1074800a800c2d0340105031505141d000c403949a030280d010080400340c41d010044c10480c140c4d403080c5c22b504161202003612603c50110905000d1900c10a04140e008081c0c15108100c040c0c400700b040d03040003000d03418140514543c10201d882e200a400310360742070161048508554441c41010001e80039070550754103402d910000510024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 992587293 1250 992586043 992586053
    0xd06092405040b060108010e1513180308060a14132c010e01021c09020d1e021c051e010908041706060301061a0d0612050a0b0108030306010c060902011704 68
    0x4811070302100d0190480c3c002c00c03503d41c020801c0c03d0413200300310140002c40c0d41b40345480d00510a0140c0a2ba04400f80008020000116000301c14100080d500d5010100d840781c18000c3c4010000341800d405040f040780248240c0c0c0c203103841107041070000d48901e000d02c0520355016004043d0500c010048281003200e9a104005464801d21006041e0000348201400c110600c2c3c00c07480b0b080a10b88203a4050720250003052502d802282e00240010849114001c20b0389400310b125072140c485a051490303004030f100841c542032007005c40c14503080c0311082c03802c682c41c2c0d201c0340d03220101c81d803114014041d8980c240d10848250025901a5808040c0b107032148d65801e0509070894145048980c80d010f504000398035030405200380c00456031405042241c403410301c58041c100b0350250348020b51041d03d42c5004503901c092101140005407055005164100090038030b071007400d906070001e640540003003042c400c079a0b03440f1622100b100e4004400045010507480141c4901c0d4111a060304030303140e2201040700b07100f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 992588543 1250 992587293 992587301
    0x81f060f260a062423120901151706060f132a02060601020606040c0e06031005180f0109020319090c030201021c0512070905060f0a0f0306050d060924 66
    0x15000d0320401e064a8015150b0198612403400344800a2449840c0c41c0d1a50240f0006500521045c11018a0f180c0a01040d84100008480c4c86405a440e06894800300140319405c100610302c1c807000d00440d0140807283d54607410090f00281c41480214500741c90340d503408140d040b80720b00161041191825500040110400018640340e45001e0300344c1c1d01c11200c3c0081205403007141d05034041e02c6213a8569041100802e030742c8250301c2c10000100e2864507e42c984000460255034412000c585580c645020402c0b129581d006000f20904c000c0709200080d1954603415055900c03000b00981c803555501603041080c01140c00880c11a03042c481036000340003c0011640035a070003a420f681381c0d44214001000f0080c1c000c05e2500002d0010000280c11522007019650010002d1401c1020030f95200c002030f8082c0c000f04640455004000340021515422000440d1a03000e1401c00b400b03064034040000d03542000342c1001824442c1c036180030004100d05824400101c040d540400542000c214580c10020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 992589793 1250 992588543 992588549
    0x90c09100e09151008150a06091e1203050d0b060403150c090803121e0106050c010b0d020d0615170c030105090102070507030219030b0106081f060f260a06 68
    0x781160a000c00c1d00358003c02420480d0103c094006000d00225400032140040300800010f040384000b0750503045c9545e184803d00c014034403030303940c140400c1c01d0481c2e0148003e01c5d00100401070301a10b004214103205024840c05294040c1000c236141d240b032081e90300c041c0001c008036541c080b400103004410040040d00c2d41c81c2642100c04108040755400c401554040c009000d00f4880c0e0f4414003d00000c00b030100300041c1d00c41c00b81d5003a01140448a298000030007001c2e044900802d10109084402080074410440060001ca0300ac3e510710100d80c0100704401e01958000d400c43e6106c452545c950b4100300d86400080ca5480380042e089583c1d13040751512a04000780891082d401c282c0814802c010500030303140e000e504a07000d0700c02070389103600f0095800180039032451062040c41001010412241c0c0b8030b0300806054540c0c001d01d162407041c103072100011078403186c034600051105110a13030b030001481e2004421410608401c00f254850b041d41d4001121242604c04034100070072851420f281c1041c021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 992591043 1250 992589793 992589799
    0xb0403140c16090b12060a0f0204080f030a0f02011109100e03120406171005040c0c060f090204050106050a09180e0709091719051e12090d0201060b09090c09100e 71
    0x91403840402c100c4140b003c0512840354024401f2591100c840d030b220501d10030070030a0051505039210031403030901c5c80400b1094556000405c242d611b1942014880340381c00910b2000f001100356000c00510a4080c070540c903809500c0310520681e10500520041996060060459503241c588a50b03200895004d030103000005845000030004a03c0381211a501580d418007501f07200b03074202028000184129130f004000c00080d2004403010409501c508070700d061390400042144076440c01407005850069204008000040120308226540440c02d9419602020302990b60b01c088508030b980640182c03003d000d41d03800790080014100c0d00c0c513441b4800c1c26200f080c128140c0c010704074802803a4094400e03699002900031111205081c4070b20018502c40d00c500c0c0c100c0c4400b44044441000a0b000445044510b280200910807a036004100c041d80508052000380440e90511400d003569029260751180074482c610003082c0b4a0100901340c40074043c02400314140110340b02d800a0040c0401844240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 992592293 1250 992591043 992591051
    0x5070b040b16110a120504150909060506040b03070309051c091d010308040b0705120c060402010207090507170c160b071b2118230d0b0403140c1609 65
    0x25070075000307481568100f541d150103844865044d4079800400c6080400480c00c10008110100d9241c041000c04005122a569003042c5a414441e94004a6509070442c03403203002c050204012192080341180e6100050b0f00e00400c82c0030329031400d0303417600f80c520191514213441e0404609017a44d00000e0f003030442e10400c415104032556400340c1d1000480c20b001c042d02d804000c10040c00203102e020010258180b290048030302d9407520041021213500061000c8030550404410b22040d0742e0b04002d0785000d0180c0d84400c200030b0615a40181030201c0c544a05000c0402848c0081c60300343d00c0c6c0d429540d440300c07100549694100070385840720340224101c2d40d000201344800640011a1f40d440c105101e800e5010b4003500480032160000081113a01aa45404101d000399000e00a282c0d0701e080780b801071107010500b0700ac98076a841c03607010005100b0312290240441040032004202440d210a0700107405046c40c0015503080e00740c0304074621500080c84030603c68003189211010a0308480e01c100d8400090400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 992593543 1250 992592293 992592331
    0x60d1e0507030923070e07020c19050301230105040b0f040234080304110301020706060b030a060506120106080402031509150a1a061602120c0913050703030305060105070b040b 77
    0x44c400195040586100750f04c103200c01d00200300c0c0c2150458000c030040c0100d0305100202d00c00145812103000c40c0c0c00303010610010030803840c1403d0140740d8044120004031004200481c91541c207141c01449090710544c3c40e2207800c20346032100030280140c0f0303602400075580ca15501111200f05009080b8500050001c000503401a4114800d004201540484614915106c41d21803640311200441c400303030325560030800c0034000f038030324401c81000380131081410752039241000130002280c0141e80202d024a400308810243c294510a0b003506561040c10000000c3d102e500100380703040329400b0602c840309291000d101c901c1a0000c0d10151000380580300101c00e80e41c030181001a581d1001484c1281000050201303900e103040703005008007030610050f00419041079000600101d4039040c0039500d0350089040c40803182802c0c0c0c095648100456206820001d25a1700c1390b660700c0b1a88070150825a46801081c1180e2044c012a901d00760011401c200600f06401c040d00c040c0030070380d094206080b140101e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 992594793 1250 992593543 992593583
    0x20071a070c080d0903032703120c020c10020717031206060a021b061603030b030705150a080408070f06140a05060120161203031a060d1e05070309 64
    0x1d000c5540d804aa0181454011081180600f6101c2411418191244864010700ca21462032603125142c00081c83c06400540c18060f11501c1505c0b8203a49031814580f603404210f80009042900795015504021a070a80c03c60403820a241504034000007000038005200510f4000058010083c031694070455940340c0d0f904010b800d1203400b1168016800030410682200003410300104d003a040684002e00c2c01d856000b034101c0e81488194214007180d5244082c03c06404c0406c207400242c5000e03512032001c0320718002c11089030f004030396102e0100301403400020304200c2540166502103030b20808100039a040340c50300700090118481d0203050b491281c000269142c84501503103001e01d0341070319001070000f0361081c1e1980d84d04d00100d81c02024851000d403401c50140c50060240103107120841d440365801d840c030f80201650301544466206100041c05805180d841204946806180410000d00c4003285008a03181e0300102d82a44074052910040100d41c940540042d032800f03115148508181c1002188 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 992596043 1250 992594793 992594807
    0x3010609090c0912141c03060303080f070203040b0a03020408190b06010905090a090f0812060102070b1206060a0309120e0411030415022d070309230420071a07 70
    0x10390104c0040a0130b0000101d03c41c8140a48410700d01015900701141c031007103009a41c1d40c2c90b5401000070b5551001001803640c01240e039074120114855014a9003000c800003540c1340114003941c0e4041000044d82c40d040f5000740d040341c00030052030007504d6000300c0795000c0e000c80ba0303848030040e1081148800068215803003448110156500184040400c1e00e50707004a40080c6100d60040340e0900c24040858045201c520117031044440381c810081d001c1c07501034002130a290181c2e0010160010500403400d103040e040c00c0c00c1d0f0f4402d00503103030241c030f071304940328210302401c0c0c28a000350000421014455410b50300102c1d4a001d01016030f81400300415841d24000e10b480100c0d0082d00302d4848100818540965800400740703080054014a10180c4400018008000c2e104000c085200c2c00642e4008050308017070484020001e0044008030b03030880c102c000c0a01903000403224801c6a40c0c0101142061000150050250754540e1060700e0384660b18280c0f260300150301e25102c03106c040380c0001c2c01c0c3c2d03486015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 992597293 1250 992596043 992596049
    0xa05250c03061d120a020106030b150a051e042c06060109170a0f0609020604080606040506090114090c0d1802030c03011e05060a1205031209160b0f040b03010609090c09 74
    0xa000b00d02d000307110018035070000117209085540350712001010595004c0700500900907095000400e620041c2002810413103540310b507006580c4c2da018a103c02c00e1a10740b1604086043d50003054100031040e00483c5114a41c1c250510700d80781c2a0ba60004802c0010000c0c4181030a8071400c060640720b41c98840084800e03c680199580860000c10010740000001030328603100700008620340a003907000544580280c1c120407c04e030b100b0301c2002181d14103401581e42045007510040c01950400c030000742501d40c00c4049030f010314a2a40416a821044001c0b01d50000a5580420034a0312071155280012080ca006038424491a82c2404151506102d080d054101c528400c90b5004d04a40c2040d015000c020861540005c0e04180040d02c0c8840300300c40c072a00352090700610b9a400c0c4290b003d22141d036015006200690003003120340c80c1f5250241040c0280c0d040350016a44441c64030034516102d1040d60007950040d1000b000010759640c124444005690340a002404802c0c96028115105080c500c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 992598543 1250 992597293 992597351
    0x415050a090e010906060b07110d110607030c0c12170a08011512150e150a05040b040603020d08041d0609060d03050c0a030909110f0a05250c0306 64
    0x88001c1000c0311195005250a00220300003180b41c0019484900480b03a6581c025401d220000800d442080100d01c0004050034007124112003103101c0ba03e821707000e07110b036a11f0305005034000560b2400385400b607200468117660003d407070641da81d1200c0a4507020003410304102d03040d03080c8480461440d2016000d94240704643d9842c51160717807915445190190100c485036092090a8003401001075540c0174294900012040c02400030740350100c1c4850000008204558050b40c900038850580d60f20840f1381c0840d9411640403c440340ca0000040041019600c0250f002e50140040410044128084d00c1200c2c0380d40440c0e0341c81520311611100e5802c0071107959070b0103c50f010014013145072244920007002c0c02850407a0420203500d8009140c8000f000095000c2052640100413035086401900040c500102c00030342032012942c0200410701400d81c1c4501400808205640500000308810b510000e0185009848200c0d601f05031150b4031450100340c6a03036040c010022080c40328804000d20700c003802 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 992599793 1250 992598543 992598559
    0x60b24070201080423060f1e040b07030e01020408060f0718050d030311360a0902030405030f120603070f030b070f090f090b0307080d05250f0f02041505 67
    0x81d0300460346540000e20031144004041c8100c07202540c11308032021401201c1004104605280c0c50b02152104001d0040702c81c6500c1c03104441c0b40d203001420454010b0b0b4001d1262810b51507040d03055014040c1607000442561020400043d2004001180303401500700d59010f6101e40c4030402d04a40d500c494411aa240415100042186042401c00b07070030b01e903009281c00101e1100741c10602a00381e001340070300a004030403120003400700038617006224198001103803d40c90240005001c200b000300244685596582e01100083c00d2100c248101da018801c800091565a40c1c50030036280100000c1d901e4074001e105801300481d5918990800300103803030b081a04508643c3e5082c1007204d40c10840140c07030080004010001503c004c2002c00440039103030030311011884001704818141f400004c1e07400520107902c05100746000c2c6412400710b503188960118600040c080d810444194043d0554000707080b440d110b0603001c2444691855121141e10032a010310810407404540b1101000c103015195100c140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 992601043 1250 992599793 992599807
    0x50408160312030b1e0402070209040b0f0f071d0a3804050a031103070e011401021203010509040f0501140c04330c050a1203061503060b190219060b24 66
    0x860040c000178200000c001602d04529507000c01c080100075202118081581c0d010b10590350303a9104115030029188254803880c0c50101401060348001d030810201d4104802c0955440380c4075000004c004c1c2105060741e009946148261080c00c03003041d946e03414440014000080f00000b100d04032001c441000b8400545a801c649a214000040d105050380c14801c2c014006501c2c00314102d00fa000704032400c01e40c801440442c00182c00c20320703a501c0c1034900000c20801405241da0f22680710740c010f9040b80b103034000031080d0b1812900500d1980d98160340759014804002011107248004c00030b071010811012082041c0c9562400c501000164a0f510b0015909404445605c00d4110121042c012001c86121442c540c0718045002117011450700042d80382e20003846000700320500001481010308d03041022916011181442d4040c0ea02c4100800380d04607074000c4428400c04c520750035000b0769200740d64001c030140740070070040030781e540c02e1400b49000300c10010007510740340741c2d070354101d030446e0202490b245c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 992602293 1250 992601043 992601079
    0x80108030901140a170a020c010f050136020325110a020420180901080d051615020d0606120b060912070803031306060e06030a060c050408160312030b 66
    0x4400080410040b49560170841024180c81c0c0c14051844c403a0016640e100200303040307096641d000c203000c50580c100310040002d0a0818101c0e801602180400042104029500c2c10150228050010401c1c00030042c8040745481d200200503007406400d6004e070b00b03172519009071404102d4061148058000400600c094141900542e1030315644402c0d070240380100392040c0d1945d030007400121440d050908242e25040c00c24414150141501200030f052a0486050041c42403050600100c1003501c0d411a14040082d55801d00c011080075003007d544400c82c007200c03100100f05038894a0006014003820012226081c0301e420800780d0064942c52421030300500380480001a05d242500300e1003603030b80c0040d16100903c00780d0300441e00414403000f0521a030801c101500c0d05c0c0d8114900c4c440c9203005000d640e03900010008450380c0e004101042d6070700320303d900341c41070300803070313000c9555405051204520314001c16503d0090324425030350f00003101c400c410218200c4c0c20840c101c40c1c018558400c40c501c030310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 992603543 1250 992602293 992602297
    0xf07030504030e190f090b1e090a180c03030503070906030e0d0516050a1407050a05010806010e0301060803210c03070522120b0f090111091c0c1508010803090114 71
    0x203403d11051004a569a4000d034010041d540500c0400d80d1f142da072150203140c4282d43d00a900c05c11900c00c40c607040da4900103444048080c02c0040c50658034048605c0c10204103118032000d5400150441c419a500d05000e030090380107c071048001540c00f000440c40c280244284146021541d0091150201c01e50040e185e5501c0f8016030502290b4014443c8002841002401105889015642c40d0060344100304c2d441c0c100d5070781000b4400d010b175100038400c2e668018030040d4049401d01c1c4c6080d001c0c130000d000c60300424442d0000f500324080014101c2c0c801800c100081e00d036007100b009555885e42d501145403c0e0340425103015000405c100000b155004242c429030941c9070103a5030b043c20701030755500c28594549041d1300850301048038408205c58684603a0b442a40542c0d030000034060012000080481481100c0c44148030301e04038100894040c00ca03403c000070302c0c1c0d030211844401c551280d888a8800341c0c0700740000b001034801c20001c1940b00001c01a50283306041c2c440e0504069110040c0000e6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 992604793 1250 992603543 992603569
    0x405010210090c060c08190c0c0b0405030a060f022a10151e122603060d121704050f070b040e0408180d0308060f061201030b04030201020f120f07030504030e 69
    0x1300240f200b41f6403140301c030307240c10000c03449a2182d040200d028908652801d04661014001c0d075400e102c1081107032000f00e00c0003207031a801000007075001034140c5c1c00b034002d0003a140804041400051141c002a6400401c00c40d18410081114440003041042000b5031b40d84a0a52524020348901000ba0f0707a95100f180e24051100000000519102e071590880c10220b10401d40c0d45d07101c0f02441c0c0304200c112004544c618200f40149500d145032800200d40c0d225407900e4000c1c4000c03048800c180030140b041c0f4600034000442011080582428102199280405140402d1038007800e81d00041d0814080101c608a072888000c4c0780c1e40341e0301c0ea02e0300d444903004610000802844000e4945855603840055409076119490f4040b50341044014401074501c942c1c5420f024201c02c11a0480400310b0038001811a81c0c02042112995114030b0220701a01500c1c0c0c1800f40742d0804603c184012488807648c0b03104050141001d4455910584200d0075198180c9001d00810500485003486040045034903000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 992606043 1250 992604793 992604803
    0x20105040b090d0f08120a0b0607021905031b040605121005150a030b071106130605090a0c0b04090c080610180b0a02070e2d0712110405010210090c060c 67
    0x402c00710b85405911800407131044607441800111140b6079a000140740b900000090f408001c00060031000c0344070f42c850000068031138150300c0c081c0460180007901c50b10142101030143d070b007500072034101c8444400304500c94900c11400c0480c00b00d0141000320301056008080c4000b001c251b203002c542c0344024480940841c42d2801c8407580e18032240c540f605103200452041441906034035111a0061601145501072415508080c00340320f01d8414104005031155006400080c082d110345d41c1107032514015210040030702801000c0080c0e0300e0055406070040700e901c00414004902c0e040d600300c3d030b0720101300d940c00d40c40f07001c90b84c004c9100e82c0309403a2604c0440034181c02c95019070b183c03e404002034010901110040c0c3c0054000d20070040d282d5116900b100601440c0c560148004002c90222040c035a00390300404080745c001851030380304141c4500c18100d100070412004150000341c5403980e1140c02240d02500c1403500110081d80948074180d65640c000100340f0109080004c1198040309441701500e07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 992607293 1250 992606043 992606059
    0x10e0616120c150501030c231005090306130f060b0f04050a02030a061403071e030f0b01031a04050604030806180906012108031f2c0c07020105040b09 66
    0x5844803007003100c0e004642d115194004242d1802c81c00d840148445680d0342030a0000410000303c545035218143c6150303150200944540a0481400000c03280805174041d21000700303400d400d0b0704030006100c001e00c184c0c281c600d6a920003030362089034411620010840c2c040c00c40e40401080141e8011a40c584005000ca000c5040f440002015901c080d03d0f01c1c2143c0f0ba001042c003030204614030484005264220903811a240d075a000a41c035400300e0320407103041541100c40c540c14211007a04010182d544004103055540090501e41d0440d2401d000c11a5180103800705095554040c0421620403580040240403595650380d04031241140540020341141024011070051044400298481c980c094000c20315503240564034a0958101c202078030450f040d492a083c085244002204d90040501c0041c9a2101c00000d41d202e01d0059039021000c0b0000c4032298006002c0704410101c003400d00d00d0041000c9803502e840e00d594a110720b8000070b01003001007000b0401d032100000a8a80c040d00201610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 992608543 1250 992607293 992607337
    0x1f230a03060906050a0b030712140c030d050a08060114191814030d03150e1515030601091703041e0803072f22110a02010f0e010209010e06 61
    0x1070903a940310794100e4046840e282040304845081c802e070b04401034120f00030700300c0031303c1c3c4045001072204401024161512401c00d4000c40b030740801c104c0e0b1203544040d0490b0b10301e1500c0300c0d00414540000c903203000003940110214000d580b01300b20740c13500403100800207403600781c1815101d850000110307242d10520804c1c1c0346e801074414000f4038202c000c200c042c854221009540003014141b40744022004d0038145000200243c0c0d0300d000c2464000c0d0f81a220303401c0c41e2929420803860083c041100c069034001c120104500130180114007840c0904d4003030701c1d4400e2241e21045d8134002400b07000c0200343d1a50007400108034140344c40f20626030080d400344540d041541c58a080303505580c096038054918610b1358442020340080c410200000f01e4000c6840c888002c01540081d8070304030b82144044030b10070b0b111040e000a2031554004016000e080f40d2113a038071061320f8806406003c40180440c1d4040c0f030080d05c22025403040c001c40e603207118160344030170103024440e04015582c2c00114103510003155404902d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 992609793 1250 992608543 992608553
    0x30503060d2301060f090212161403070f030e1f1505030a0507050114071e03050904141911030c0307051201030602030f130b0103110d0506010e1f230a03 67
    0xb02401d821010004614107041540c4100104220b51000c180180304101c1814852003046000390401d440501c40141c0e40308020741240c00640086410b02c5482d000024000800d4101400c800d20300c1d4251018401c0e4000c15143c1070b1202000c3c00040e904452150824461040c0c81c0e01069804452111103910151194042440c090045034101d13070660001009001d0356800c00401910086a0001286001a5591840c10688241440b009002c4040022900301801001a9002900050000c000c441c40908641070822000c1c0d840d02800e65500101a03070006060040350700c00c1030b807030314890714546030040422000c2e44010824020007100b8444000c82d4280280c40364002c500604e0050303120704102e00c0322450b8140c0a01130315088c0e0385080d0360000280d01c08c1d49042c11290000d0a01c0c4012a0000c049031240900c020020420301802c1c002254800b14121414010031808e11502a81d080560b00c806040706103010342c21044d80c283c130b04042c45c0d088110444500903805424203080d2647d90f914 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 992611043 1250 992609793 992609843
    0x503041502301b040f03020d02131505090601031404020d020f0a080f12190e0f1203041a09180712140717010b04030807230610060804030503060d 64
    0x34004020b0380c80d005100c14144055900d800400c03040c800a860107280c030441d016007817400d1200a01400c8420a10b80641d035908034001c0c4210b18460080c0070b4100c0c4644100e004002070301429108205000c0480d00651103482140c000e1180070b019843c45440381d03001c001250b40d5240c0101d920010394070b41d44c1480e8035603402040041003d80e008001244000c030030281490808181034841103803c0c400440781c188011428131191400d810a003000c14004804503402da00c4455005804c09038802840306c104400000600440341080c1c004059841d00c0d0341c00952a201d480c9110350312508a02000348203081200e001c1d600a100381c20303c3c0c0c14a2062843c0b82041d00c0c603070006c1d40b0b42e055001040048482e00417021800760045011301c2c1d034035503052000c0a0310750301843c04060242500400d0a108105101c039400713070150a0080d0030100d482c0080003095861800b21952401031280c44000102940140107580c0981c0d41034943c542541d503010103004c950000c0500a47d04000c0b643c10100301100c51480f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 992612293 1250 992611043 992611117
    0xd05030c01110a02061308070b060d0203030f070c0b0c0601030b181e0c0a0608070302090109120b1902030705120402040906150828060207050f03030c07120503041502 73
    0x11440e0b02d03801801c0f4060704002000781b00c0c1400e1101d203201c01002412813401c03a60400d5008544044984038070707012601440e09240000d415201c00604480c1c2d80d1500c60140405a01c911180810240c2740d110b04c400b43c1c020618214032542c850720060000440b210240d590151a800410900307126154404c1e1900c0c05e9401407101200b003100c07408000352003d005064424506a075005601458100c0050103140001d20002c20542e0106804007140c1c41074a001c3c00900700d141800d51118081c1c207080c3c118420a480f42655254032440381902c600e42402a24402c1c465511000d04015079441110034001005100300d0b4801c3c0c0d00c0219200194bc0ca1098220a4580505001c2214241140540740607880b210304400034402c001d200044984400301001c071207a001c4c50258a46a2a20300b0074a0305149882400d8103000100422907001069005884150f010303c5146030b00481c45035054807284400e440140c41c04a0036000100d1100040e0001c0824500c480e20710040060111800d1072442c0000c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 992613543 1250 992612293 992612321
    0xe03030f030406140a020306091f03020d05010204080607110a02060a0e090f190b030619020f0a031b0503040305031b0c070612060501030b0117091009050d121a0d05030c01 75
    0x403070904c001c41c11020582c1c440d0041c1d504618504090b000101d40e17180c0148140300c2c070b40c260322040700199203031a074420003560b000e40b15007941c00071031800c140030b90420301070782c0014410100042e01003482524441000000703100507100a08042c1c0038008103a0002e20804284440c030350350828143c8812a000b0710409510006031040c0c00c2c0502d01d910461403803040400c1c01c1b070510415000c1690041043c81d0004209080d950300e40514180c024064000c807440320440160200d00b00c10141c1c1c0540112940040003038003e00e1499811800382d42d680019103002d00010410320006100007101c2c000352034050884030a8900700740310801c4552070324000c1d4200000144000d50081805061405a4405064242024488020400c00003001114800b4007000102d060401180740301d0310a00c1000790072051f030003040c0040350440c2881e60783e503030403c9140d03030000b942d1441c40d60354054030f44070f03003507544800008203480c0c41450010025180501d841c192641e000800152041803003d20500003404000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 992614793 1250 992613543 992613551
    0xa0519050a020d05030618061804240507080609060307090e0a030809070602030f130e0c091201110a0302070204110706090210020f030304020105160507030318080c100e03030f030406 80
    0x644070003030034190f1030040242800380038814807149607141168621400c0d40c40c11050080d94130080019100215a5105611400f0500501c03061202003a0b0100e8080d00f44050509032049608482c02160401ca031200d00154a07400482d000e460003a0006030881e034020121540c1640b1822400100c41031041c400340d260748078808181c20160004009640480b07102c0c05014031a2602c60087c2d00c900c59400b200c2440306000980c3c0042c94900f1402c1e602520403074040200030f2906170801441a440901d03000c3c41400c5030300c148582c040050085035940d400150805086c4640c140c4190045e40111104a038007945a5400d0703031100d5643c001a242850044001040300700c0e150050000010350500e4190854006101072002c5c28000400c40c3c0d000340c3d080c6449940d424400014001d07004600304000c14600480c0000014143e005080c032020300301e00c20070140307620742d46c01c0201e07a204090002a90804244030034642c0590150100d0038041c400901a28a007045810445c00c60364803c035000c64010340e503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 992616043 1250 992614793 992614807
    0x203060a1409040305090d0602030709060e0613050f2b03030b0d0804030b18010c030e071508010306090318290720010203091e0f0303030403090306020a051905 70
    0x915150007000400341c255414495030020885160703000300050140040020410313507031307210107984103150740d0810b80454a90800200c020684e0200d4820000007502c0c3c1000b104c00e501d0201c045412110140c40869005072425090110f203248440340c0310b610002e5800030300c2444024030204a0300f60500401400840a0340c13030050f040310030740c0c0c1e011401a142292418000fa0ba2907044609898204034445060b036100301c01841c1c10000c51001403641d500f054058801d0540540180d804424a50305552403507448246451202e445440d01c100090114401040803a403694032901640d4000e141800c0144e2080204021040a945c07140511541040304441c036070030800b1102c1d10001c400d131000d034a084503e8031511003603c644040601c0c6001c1440440b4000e81c000c00841d07d5161010b44101d5159503e00d002883d00c401002c1d403075010745542c1d4224200b5103004812240301d42d9040c0c880c0c3d00840d05680720f200013500404c0e400000c0c40810003013070b04404680b05011035070400b140d5a040d03071540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 992617293 1250 992616043 992616049
    0xb07031508010914160b0903100216020406050405060105070f02040f1d010c081003150b04061e120203330a0606020f060601020715030b27090607021e1e01020306 71
    0x2595032200200c40c0c2100c542180d100c403101303070388808441006d41c00e181c484400b1000207003402d03180c81407004654400604d2180d011801446d04841a0084034200000340d1348100344000e8071001c07101d05000520801400d0300044064030141007450010f04001109507155040d001212101c07620080008200400413001031408d0007144150300c81071909101900707041c4890a56040540401031001441e40200f00d03000300725501c03070307100c071000180280a029940c0f44c07005040110000032090403a0540c2d03000c22030b00d0001014660341d950240040482d04032140a407402d4003107000b02c0500413865507016800c43c50941c0c8141d030244c2801603002034058a0200068a4049003404004070744c7c01c110104406680c021440004032402d500c0004818803107a03804800030074058801907800301e0245c0c0c0390071040034404040c1d20220303000d4241d16030b0f17a15042174150369560b007110030b000140c3c054a14003251411120b168800300000000300d035107904042d0204034200390900d450404a030741c04070030000c1501d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 992618543 1250 992617293 992617313
    0x30c1803030723010c17040302031c050105151905030c130e190b0109180608010e0106082503020f060c0d020a051908070605060d141023040b070315080109 68
    0x559001c005c20101340841750150200c0c102d0041070218100c6000080c0515000340300311a46020034036032171624040013420b900e0042000707008507409400302d80d0000060345100341c1152070701c001c01008902c9841c95540102c40d10303400141040346100051101d92074940040000ba0007400041c0c4000b003241c5818203100d8444055003c2042c101401c00318120902d9030444215000c1e01c846030b00040500c1e28003001c400c09000341d6030007502d0a40ca01005100e000701c0c10351000c000d4804030801c1c1ca12410014412603807030124400e8254000200f03400c1000189400000c1c1d071407103880503111a040c03d0040c01c0c071f0f608010300c600c071030005604200258400c011003807001d8180035503060a180100101d6403a03c180c0c500840000525181d51a80482d00a40e5400350007282c065000d0320182c0c05018014219071180924560892801d0a1440001d060420b00d070011071900d1007907111f04007680d21074a0b02a6280c8026050324140341e654040406541c148200d118003a2002100206402d007140c03500d454030f8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 992619793 1250 992618543 992618603
    0x15080615030609060f01022103040b070203091e27150405070c020405060406051005070302010c0503011208070c0306020310030507080c060429040f14010c02010203030c18030307 78
    0x851007001004126503a03040603d0b04004207698128984a01030f006030314214030412801801829200010542d0101c50021803081d407160300110000d403200201039a07240a611855070f4040e0801c00402d10002d816543d4128681000701911109030341d4442040d184c1d2951406900c0c0956020100004500e5485c014529210151410042450030030002846289030340002442161640d0210301030303a6841e00304402518000302103583d0540c901d1000390203070303120503801c8016500303082641c035055011b00152412615101155200400d141d82d0f500c2c80c0c0e901400c8101c1300c0105070080800801d05d184041d51103400b00701e020903445802c50130301910b0202c0551110503580d0108030501c00c01d4880f032042d501251044d02c00340640385d103520b4581c103160030703202c0d4401d0406801280000d0080c0301420500c084032100c0701001d41c0451000011124490b021401a0250b44200049070f15600340100400f01c481000b006c168540be000c10009046a1085500307030340280da44c0701c01e12941c1c000654402c1c0c5e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 992621043 1250 992619793 992619829
    0xf06060903053c0307081b060703050f06090403021501140310110712090e0a06090c0f02150603010906060810180c1a0f03040506011401020102250c150806 68
    0x12400d4420030841c116202c080341c00f9040c5040708a446255082065510850340603420035160041c0e0384441902c5038a00010b01010700c00d160200d02c01c41e000e4424607000b0b500d40071b1b9402e515600e00c4140881644003401c03ca08510a01c401e00c0e11100003000564080d000214601c40c0e0048050100b42c07a01403d010100501031401c00510b051020440840d49002e070302c80c030031110800c4000707002d545030340c1c140d0b00004004044001700b003100d032a194088410784004000400c1300c5881e5a5007201e440b55162321034030150340b100c0c0324510211150b03003400341c0c04200240007060b111000d54a507400c3d14a05e40c800c0f2450340c401951712032800c0442c010b40006040000214184c41516141d07290500c005218048403001110b0005194070141d000715030481c001c0f807040d60f03680d05141c40c149585000920403180800740f0f400f25030a903907206000715506d014091041a60020080c921201400c4440008841f016400140000d400a442d60000c0104507552100101c1307281100910800b20501030f08886 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 992622293 1250 992621043 992621083
    0x40c12050601180c0815030a0519060609050103020d0308150d0309080f030304020102120711040905101406060403020103050903070203010915061d010306020a0c150207030e0d12120f0606090305 85
    0x25131304e510405450f0b002016800c07648004c125400401c0c1400384860707005e007050103099000b240000340740004c0c00c49988136000800403a540c4d032100ca4100d49007808029444902000c850000ca4072606000ea0401c0035101c0580d01c82c0c1d640800145500000502140426882c203006c0010038800e100d284a00460000998a03518003640000d40f1490148030171140028085406404d00c450080700b038400d440050030810514125017407280e951868812041640d9040c000b107c4130079800000a203002c4d0310090007440c202421a4010f40280500622209142c4000e0281c600981d030b0034024100b980c0c0c004c1c02c5034030521130001b140c41c003920170300d4001c05800b01c80d0044a02c40082d00000da00c0c116a000382e0016114806003004075101c901080300501010120004203440c80101c1d801494003602c251980c41324203020b0350600801c2d510031000500403d041004001c401c81c09a4070302d03210103100c00c80025002c241c1b640051304440548c1c01c001c000038140035081c420010204580708251401050001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 992623543 1250 992622293 992622311
    0xa020a0e04050c060a020c030d12232805162601150c14010f0b0f0603070c0201110d080414010515210a080904061517040c1205060118 59
    0x19030b0722100f4056441c014540091180e0070603101f88100b5441140040035038280c1042d801c07004006440903003c070301502d07140078008800f841006452800030742c10070181020310787d034101c2a002408003c51002040c6a51040348150328403281c410203100e01243d0b030141d189240b44000003403101d6003200400a03802d2490340712036151760500500d54111000d0100c038a00c2d01850f82401c98081048000050011034508004840c0007010341280e010b01600100400045604608204281c000001c83c942c014008001240d082481548465690750040c1011006508000e05103031901c00c0441d0300030006003000d4207000801c5042c0c802d5403800c02c4000c000340074a05013074000d51a10b106100740248280d0074540c008182082c49003001000041000681d000303414030b4105005580d115543c4544581e1820030007040005148589641c00c850341e60b00c2d0f00051944840020728004007610035070f450303020004001040859001844d90051041001d001254545050000501c1c07080d0f65490540d400c0920300703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 992624793 1250 992623543 992623553
    0xb0c030f06011d2b050604050c0103020711040b04060f0e190b101d0a0e0a06210b0a020f040602010b0111010c020c19030512031609030201052a0f0a020a0e04 69
    0x3001028400700d40c0c54210400c41380440380310340b140540070050590710045800034400c003c41c80b288034034003810036034003001c120b90011400ca21900700c005003211040d0406d02d5031801d19034000c40c4e04410203080000d0301c2e912540c0034000d00143da40700f000002203142c100019501c41010210400c182030b2000d0050110200c0007074404d1244903550b0f07080101210034000d0501122005490340f0b10007900002c2c0c3c2c55290000380c0e24419080399030209550900100154540106100c1030401c0740841c4004503200c400d80d02c501403118058503003460503400344030303540815039900007d01c02041c0c0c0350000501d82c00325000150502c0c010020200c16645400c20240c1580d030089102090702e1000c072185510003c40200c942d0305c50f079898002409a2043d8400c213240003024030010341c0101c20024098210009600080b80c041905000090000e0000d0102004a01103440364000b61401240c031a00144081030055240082c04d0380c4081c4c0c1d41d4000e84400045d03041c41c00b10040504a54070b64a601d43c0f0b0207460f6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 992625899 1106 992624793 992624837
    0xf06030c090a0e120f1b0a02040c0c0201030b040e07050d02040e01020d0c18030309050621240405060a050d0212010e03030f01080d020d030c05070b0c030f0601 70
    0x910007940c0141000e0321252502d44030040d10781b00414450303200800e140c1504510620a030b54241c00169924041c0d20316403100b5542c0d07020440c03641d00005003580d4042010714000e518081342c03078003689800b060b03003010350301c0607144110004140e10108000345000d01007070000d0f5102107000030003000d082e080480000c0c00c03580c0307034404420807402801e40207006100c002d01007002040b00300101e041910203001c0d020321400d9011103031200444a02d600400032a440c18a0980703480c0d050314000500603805401070f400340d074100414980440458105080c0e4092184903414101c2c03801c00710355a80c00e1390542009128024020034160b210550b68a40040e103441c07028042c6d2100114170400f00040281c0b05014560042589481c55070302a002041f4010082e02008020800c0ca00481c000010a83c007464005464555a25021070300c8151741c54041c1480b41004003020610b4a10200d0802d = true := by decide +kernel

theorem cover : BRFrame.Cov 992446043 992625899 := by
  have h0 := BRFrame.cov_init 992446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 992446043 ≤ n) (h2 : n < 992625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
