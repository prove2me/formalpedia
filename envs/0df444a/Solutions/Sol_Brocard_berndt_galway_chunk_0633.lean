-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0633
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:50:22.427207+00:00
-- url     : https://prove2.me/submissions/15a17719-df93-4ac0-9d7a-065279f76d89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 113669064 ≤ n < 113848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 113670314 1250 113669064 113669111
    0x1c0f0f080d0c05091504080d0c08253311091e0102070b0a0503040611040b070609021017040605180a15050a051306090203010213031a0709151101 64
    0x209a002510304418102019030500d05858031706034508141c5000ba941d600e4002d00f098070402c2002d407420712810003000d0425508415507126412410703c1021008803c407003e070800a0320f1006009454040352002e0300c902c079800c0e200600400460a81e1041c0c50340141122504040400340705202502054540104496158001340c00218013603403124000381c20311105405c0100c03400000c20134268900d8000f8100c94105500001c00114140d00080071281d5006503001460308440026241d01401200d0300001b121038022a105041402d406034141c82c40420810b41c1007400c4401030004004c82c41560106512070040340c04411440c40604006041080c6810201c6010780c0058101c0c0d070080c010320410b070303118400c2032041000b800c00002c90300c04075407c542d00900050700c071070303036a000c41d1029010344903041581207a5440b85ca4480c5010f0304500c46d94141c4841ca94001000070381c0a0303100300c444c4000c4aa04901940d202032040c142140c4c420f90300c00362004150740300d625810042050080205a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 113671564 1250 113670314 113670317
    0xc0d140c1212010608011505090406050904110f011b062004081e1f0504150e030a030e0606060304020d03091e150e030d0c0c0b13051c0f0f080d0c 64
    0x41d034880b40c0c00d4a860944068002104115400b8014420175094081054444446040582d122031203280060040c0c00c09030025500030001409002c10800d60701000a0140d904803030303032807615004100460305d001030080095110000110200c000c6032071030b41f09140c0100d800c1002c24541405801180d115846544801c8032035110b03054004840d02102d1340040c07580c100c0000350200349030319221083c1401c15407003141001c40d0f4403c041020010840c600821a080b43c0c1030900010850342c03c45622500314a00c4040441c0c03d021024002070703004503a2038400c40e00200700c1d50071a1240d409001c51504800c3e82141880a5030f1004a10300060900484a440c20704c00c0d0304800780d007410190810b1030046566113041c0154020b00381038540d004600010402202c1c40c046201501a0400e00b240e142d00d68060200c0503000a600d590444001403050141c038800d41c0c0c0c1c0350070748102500501366240601000340180300701003000d0300020710150310780e50380601514a0b42d081c00e40c0f0341010421900180e04510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 113672814 1250 113671564 113671567
    0x8030307090f05060301030201080a0e06010f080705030a0f060b0114072012070303052a010203010905010f0b030103020d020d060216110d03080606030a0615020c04060b0c0d140c12 79
    0xe00150700030203401c09010400381101c0002d1521010850034081800000e05204c0c0a9000459040b002d07802011581c0c010401c40341c1c203594650302c0526800103170241c613506002c2c426020440d41030005540c10075076413103400c2c88400c42040d2950360043c08448100c50400910041c42c1000c0c4900e54087e040e007500850508016031b5a080c001840364a21031103050203803100c00796003500040b01203110800c03a074160800e1581c03003000c035072114003600f00c0c0c80b8240044d408503400c0d02c01c44801540514140c400e095010003003a41c80310620400f090051048500942003040148014108400510011440541042c1510b09956160383c00e0341c0200c0e05005042c1c3e0b13035030602c00c10f11110032900d00c40382c1c1c4145c526043c001e4441d00c1c0100002001022a07000c0c031000408501003801301d41c891401002100030b4814070340c1e07030a000251500c5402d00e41d244107a00b00b00000c80c10304101002c81d000101044001d25840c4a070810646d0000c802c440042400b050a00401141d000305000d1207402040c0304082d20f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 113674064 1250 113672814 113672821
    0x2070b1806060d030206070305070e060a1805040e0d0507050c0405090105151f030b06070803090336040504020f0411090301180b0f0c0415030b0f040b130f06090501080303 75
    0x224075040004105511954500c1082d0010903008a000b98010596141c0440c2541d58000241c802940f20311016401c1080042c00440090b800010030500ea0300e80900142816070b503100700310507640f10180b0705006030401d0381d0a080041c068002000710502c9041681c00c4000d40d04002012914129180c501d681d448030104601c05883d0700c003648101004503007080880e00000c0c00c110070742504901c0c2000385a911041030040c6d41c0d0381000d0301d224030f070300031034441c0c6d00d140c0240307615102d4106820714600c101c04000b041c030700480c007214540c0784039500100b0130301002d10010421001c0e010240040c1d0b040141b905400425807038602074004648088980b45548000010502d03007154004581e06502428001481e00040c031503440c440e41100e40085403201944030050811050f1107076911084190106000308501a609500040480c0303008a8060380518203003024007042e01c08103c0706551021010110351842000355010941840d0341000015480e80c83d41c7c10350044520a80001e600c0d40e00c04000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 113675314 1250 113674064 113674111
    0x210e010b03010c1b030c020607050d0f0801180c0309050f0607260105060a1110090b06040218150d05090303040c050a03050c040203060616030e0306010b090114070602070b 75
    0x451034400320940c02001515020540140a40c2d81c41d02c200309005030080000c428940701e0b48a803810103400800403a07954100d49486503480b440f180d030b080041030f50710510042c5980038400740c0d4100d070900c80f2040c2c000100c50402d14002c000e0504403d060660301c0e440c10340410020008412004c5100c40145140d0500303031030151078400c85404142d104605e1080240180e02d40005140c1188d8054405640701c2540c101c1c1a41c1039488560188240d2103005e15035045004aa0000c10140c0c1c050280ca04403615034105100a82c86010000b00c4001602020b69145007001005603110714403041c0002e0400c15504009429188103803084915070340007005000510240c262a000100740c01c41d61103101d40d01d56603649488040c0082d19134400c50f03020001400303e849003070407160b400f040188030303803808c04040c90042c2600345441c0704d8a00910400c400131503420b025104564000c1c105844101080d01d402070805503540c0516012a0510b03000c0c01300c003001500f040d08150042d1446400550503807a01040f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 113676564 1250 113675314 113675321
    0xa0f030305090307020a1a07020d060609061a03040b09120703020106050906010306051003051f060309050c01030614060c210301080115060804020d020a05030304060e03070f0b0910210e01 82
    0x5440c3d0001c100751001a5600e0400008503644680c41004424030700b203220a007801a0f03203020750010300342c100070000c21100ba805441a613207284003c110964403104d11216000056204410380c80b400c202180108298141056011003000201c51040440641003c007540000408802513916100280000d1030314411a6510801c00c5c03808000b45441c21001070f400f55120101c1e2014140d0b21004901c0e8216180c131000030b4041c030b80903543c807e00c4e507540e4000c006101c0e898040d078190161281d9584258428080c40d0111411444800d49201c1030b801040320681c8150300d070b50301d9445205200402120361684d079100d6104004501c03905c030340c50703c4d0b01388c0e080d13a5101403854100e4480107018000c59400201040c0c0098041d10b001400407000d03c08102c80d1500e13a004140d041c480481c00007141603004044080d4040c05a0070340b0910707951030241134441c800c0760250118880007402086407a05140386200e074101554a41021190754124895007210b216840045c5926116400000504001d02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 113677814 1250 113676564 113676571
    0x60a020309030708150c1803030412030e09040c1419030303050601080c0a0210050a0e010f0204050f0a0302030d0f0516080307260403031a0618030c010906050a0318050a0f030305 78
    0x42d100345203610511002500340103182076039446d400324840e1403800d001728141740c1c01c00c4060b040ba5996620703078a49034203009480c40c04a001921001021965040007d4010300565001050044813070401c11108000e20000c03191580055404d19042c2c40080002062401107000381c40005050400400051102c0700c020b00040f070300382c2d080041d69003040d400034185035060f60700070000a1940f16606408064080380228407450740c00d040603844d4a504503801001154004c0325008400101c1c1804c1c802d031440d2510000c0d44c03580004010710300c0c01d806038a520680d80c1c26403820920f4000382c00d800c034800c80001002601c128602008110708a5009050900d85150104015003507040c8020b00c004000c2000f000181059224040f0040b03401c0324041e4400d060318002c0529440320b1108244040c0d07083c1c0a03141d18840d1260021700c20595008085600546a49503611850079a8620090313018000045211403203144030394100c400709005101545025100e00c031030b82c03511402c0d4240101600c0014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 113679064 1250 113677814 113677829
    0x10c030807020114010e042a1401120e0115080c090a020a0e030d08090c0103050103020319020103020d1103101203080a0b0f040f1401050108090705090901060b070f060c0302030f1311060a0203090307 87
    0x52310610446044035490800302d40c001c0c100c060f116803005004a84004d034820344521114200507001d2030000d4190003111428600201100500d41d940d080d40d691002e00313244580d0000c0303603003010640d0300b1100c0d001000c491159080c800e070009500008a40b07440c8072612444006a01d007800e01040720001d00088081903400d00e0180101e505540004c5c0e2200c5844003c032a1400f050302d1021b0469000b0b8058405680301d0080030012100f034079212618550040700d40b2041c0f0416240b01080020900390400031482c0c143c0c3d28043c4959400180f6401842c052500d29405500c0c1d6056600a58541c0038400320b92109500114180c448840d190840000681080d414070555904110f500840060903000f2210301b26103499483c0c0382d0403100390050600d504400e000303420004440f4184410040c201e03000300d01c18402044051a9228100c04130300003503603140444c11049011592000c0301140502010740901014003a0348803450004107254818400c1001503000464000050320b0700b442500000e080c403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 113680314 1250 113679064 113679113
    0xf030a06050105071205160b07020f0f0a05060708090109020a06090e060f060d020a1701031b080105090307020f01020c0a0314010c0804080a030c1403040b0f07020c010c030807020114010e04 83
    0x142ea170700031080c124001000700f000700206040401c20703886050310001e9500140c0c01034080c00d14440003902c0c1e21010769141864070075142c0c000c054038800180c0501c555003003405010300d80c48290040740c011202900c0c8007030542d00c81e81c0c81400350351521960300c0105070688810004070b00e80020034040030401001e59101d89140030001009444280c11203c0e10501d50000682c1e4001884065407082d9500c6804c3c01000c0941001104000d580c0055211622620341c1c0c0628181e03130303503e0032426500d048919101c2900148803240050400e032002d2240040140107540c1040b407004041144100760750b0056403403040b0f00ca0300004c094420301c6890a0084036180c80c1b00d0034541074803403510911a5010381c00805548014004065105980445502e000d9000c419940d080c21700705130700300d000d081d9040b6120f0450940820304003030001a0940d03506006841b0780c00003038803581301680c803284000d02c910203654a86000404051b41560101d029020744039003c0820700b09810035aa43c09070306021217072903101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 113681564 1250 113680314 113680327
    0x70e010305090a0f0206090111030304050c01270b03040f05060a0b040e010e03120603010b0a060314010608040f03030c02070b04120b070e09040f050307060e0c09090303010b04090b030c060f030a06050105 89
    0x22002841404c1c0d01940d85036951381000c001219104030000c440307c0076000c044180070030003c000c02c90404440b0300341ea8420f24011810f4842c0381071580d081c0d81a0003e0724100d800c000101899024662180c0202c901c903541100765114141010001ca034803210003a0359900d4010700c3d14007840b5460710034140d0070003001000d0750068926a00d219168001d011020382c0c0000904594013500050000d40002d070110f0300c05552048040c01504116480180c41066440086142407150101c0d52085402120403849416142c505800411101000c0c03011405008400300b210048000180010035401c01c250000c0540b50414106e40f0201400345020401c0301100c002c2075030b4a41e10b000707411942010480034916250b10b046031462282010003041d19040a064031755048002c5180313407020505444280b250b82e2070904140e2288000d00a03c00d12207404d020500071880d4640c0000505c901c00b60495903019020340020b006504184c404181c0700b0800810401c60707170018000e480062034282045401d214 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 113682814 1250 113681564 113681573
    0x5160b0c0705060702040e031207120903050f0304020d1410060803030105090606130306090c14042a03060e0109240303051e12180114090601090b0303040806070e010305090a 76
    0x2442c4503081c89a800490342c50300f035540d070380d009125084002080380e0b520710840001a040000844540c030200302444501d00f00d0034050302811600c0e0364140d07552460440321294849450300060700aa030060050360100300018003481c40c00030603183c0f42d03000344000306042160348156080c641202c0c03119001840100034a81b03440d07007840c0d046002140c81c00d8550321403164900c1c0c0301d01580d20140c10a8145085441030141ca01102410313100316105610440d1540303000e1000350345a600c040364072101c694010484000c0c0c604a0203140c02060f242c00f194031640c8811155501c002038100c0c05101c0e03a41c03524813005010134600c0c00c2202c40f4980b1007182e0709244d61806040ba0040380a01c910700140d07400c000154060000403146c91860f440c445c80554141b031080c800c01c0128101001580f0341c41e000c0120340079001d15400c00c1c407803004000107281c181e0078005640302034404100b515426100c02d01c004114800c0c2800641d10034200c0340d403a8426144010001000d03a07001818800a941110100e1008034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 113684064 1250 113682814 113682823
    0xc030114040803040213060603020301060905010f140c16080114100609061404091a0f0102011505100507050a05010b01020c0d080703110c150301141207061b0b0405160b0c 75
    0x94014002d107483e903903140049191415404010080a45021404140150582d0166042e500c50ba50307480201ca84880040d1000403100744003d0100f461102214103e10104000300b4142040c181510107600c03145554003401c8100f504020003594442c09603440b41203401d0300c0700754022000314040c04070340d03c3c100d00075003102c18500031082000075003003a070720f034020314174007210000c06408201300640c0701c60100a66085940040d040c0c0300d210a11480b160541c814040d1807011400c1030000080c40d0b1800b410071400000800e070000c2400001c1c40203101044092000030211400b440002c100c01e811103000a00f44881001058400e80025804501040051043d520240d906086c4000f0b80300014000ca0f107052203200d400e1303a0100b650140c01104201100243d8100c2c0c014210f00c0c1891030100e001c10502030102000340303859501c081410050309205409440004d40c6182c0c0d40b0031580040e0720781d10200d010446040d02c49620500701030f1814486000120300030040340e04110308003880c07580840d864 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 113685314 1250 113684064 113684071
    0x3061707030b0a09020a0509040b07120204050f040f2706050108061b0a090b030702010603140a03050901081009090f02011e02030a0c0201120212060108010b040e04060903030e06180c030114 83
    0x42544e51605041191a80003510700074000c0180280c01500d006d181262000c0021203a54000a202c5c05205029100e00c0c001e84003668002080040402c402109000040c910000c3d452010307526040703042a0540a1a4281c40d074125400050303c00c0d055509080d03081e070b841a03000c1030680e4803200420906401d520240c08490340000f980f20b40d10f14030280101d0b130360301d20394000c0700f44a0000010701460540541c481000c0f46e21407401076580c007007500c01c00b030b413a0000c818014020850401280480d5032140060075846040c110b1401d114a44132600300003200c0042c4011902140004442401d40d0f0300801d9140b0500b800d084201c540c502c244000039224002e240c0c2402c01c0c030091080500031a07028843e1180302d038294040440d140c48028055548079001074850a000c101420008100c5010380340c1105c0541c0c0e1203003285072881c0c5450f5076105c02446840e2085c0d04156a03612020f02180c81804483d0041540080f40000506168200b505207548034171175a101c2ea14103031541d1072940c41c2100d980d60 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 113686564 1250 113685314 113685331
    0x1050d230c15030c030c160b01061806170c13080706050a031404021305150303030c0d140c0a081005100c05010510050310022505012f030a1e0c03061707030b 69
    0xc64000300840c216084a10b00307c0103001381200b074000f01e00306602c050a50f1140451040211103680ea80005407809441c40510b09808141ca0000449040c078207001000881d40090800c0089aa1007201e14180a419007100001410028551039885e40c58040c4a642c0c03420710020350004d041c541d00040000708001941030040c0e88820000e1a201107050350701510701c0c400f9007640c2d928506030544540c1a030111031143c80d000d207010043c0c04d05918100c0c05510900f03100340022301d08a030b050001e0341c0700302005113070910a16000c2c40218041e1107041c0400c012510039114045c1c94100ba01c0c1c80c0d0709440c0014809000d098055000300100e80c0c00003200304184180304070041c1c4da0241c5411002d80700e11000001d00c100d0300512105010040b055004030164903601000486102c0e9022017220b04d4040d02500301c18514050021403e1030001d41c1c0b201510406440318103610480ea140c158040e24201c00050012a5403200d0801600380c07801449451100302138050b04580b419507480c0001484042c15010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 113687814 1250 113686564 113686567
    0x306060e0904032102120f0a11030c0310150503090d080c07020f0604051c050c06070201172a120105030a0201020a12090f0b09130506010801050d230c15030c030c 71
    0x91a203502400d0340c60110a000310956503030411a1004a40303840071f680380c5000098820014080084030300c56900900e0108915030b203103803a0128940d5640e000502030ba07400211282000501d00002c603040c0c000c090203501d41c99240e14042103c0340c10508070380340400c11710600004014070130381d81200300d4803c290304071042a41d0b61a9000890081d00403600603507001a1016100300702403101d1a002442c6500c540e08403040701008806101c824014900f000380440c52840c111011405803e84c2c40380d109820003415801402c0c1c44000c6420081c0c01d40c00300524400c001a220241c004282070580940000e03001055585490b500007136640e4108800a001c44041525400089100d42c0b50716005141c101c00e009103141e20745074904d80c40e51042c28054400c485084e0074001c81c071041d0080710310410050b180d40403e6881c1405200b00809400800c40c0c1019038100d4000e20360309000038a210f904003240090204103600410b1142c03c0c0e03501c90000242580c248204007001901c0c00407a03902609200019 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 113689064 1250 113687814 113687837
    0x6040b0a02011b2a02010e090408090310050105011106010b03040b06030a0c0801060e012103030c020c1305010e010605030f07051b0d0804020a0902130b090a051f0306060e090403 78
    0x100d0050244851034800b000041c00b1a1810692140f00c002000745054540d107002c0c0b15204d0518890300840d44000c0c00700382c51030f440b0006490300b201026440b034040c400c1d082ca417850302c8001030700f41000b150054030841c2c0d0f9000180855603000407050010743c0c400c8020161035050030b0b60351025020082000b40040d00300800100562024030803041600c0c0c0c8006621005a1902410350103044a0301581c10300041c49000000c0c5d0130421002103049203844548e100d401d0000342c81c102d02078031384070b694030040d0701c0707102d03126107050322140300d82d512920300c0160009141d4140944401603a00603840038080260520522080000d81455180c1001c02420856942c80300081f221000210f0140030803168003985d10500700c29900100c0c1e051040e80300b103c5403640d5030f4881c040390040f0b01075010f00c800414000042030241920403030003450000c0c4000e129652803590f076000650f0050a901003030020030803402d400750300070303816000d41e1004d4940c0342010040b20101171301041c180f2800805c040c0030800014842d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 113690314 1250 113689064 113689067
    0xb0403090305030f0301090b0103020a1b0201050f040b0c0708030702010207120f06060303030b01080a020c07032409050d2d0f090e0106090f090204052d030601090506040c09030206040b0a 82
    0x554011035102083d42e44902943e400c0b04044e030401d00c1354406031410312100050b950301c44c0c0b0882e06580301580b5400d200c244c503082d880c03281c0c480320702040381441410407401d1160000000580010300f56007440654480c450a1041c5c142000fa5010603001e41c42030016000603a000310701c031010f41b4001c2501c05a00c1c13400381000034280400703401c042c00d81440e1110100c02d040c0d0580000c0305e0003000b130325421880c4c3c0b501d0410704128825442452000d030006841800004d021240140544281c0410b40d0007505d58401d6107000c9501c03082044506a0242c501d1034110f980000c3d402c04020750101c40707503003094010781c0301148900f20140035808000c001100140014060141c00e40500a402c502e100c50350317180c0e000030f84281498010082d150554250014070301410b8021138090b944040d1506413a01c82e5010012002c860004084010681d094001d1100c0d450030450140200304200f0041381c80e040075810b020840e01c8904e000820813080307540134005a04e589080f1801c880c8003122056440070320040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 113691564 1250 113690314 113690327
    0x708040909060209031504020a14040213060305011a030408030105060c0a06240f08070b0304020a0e07080103060e06090705060c0a231e0a030302090d06140f091203040b0403 76
    0xc5491100c0c5462400070a01485901414103040b054046610440d581c1c0341c81c0f03040060480b03001754001400441070180c1001d28002c1d542d41e0703034064405814801100007030822854903800100c00a5520401003100b12400598107820314681401d00d4650b0802c0d462781581031005008040c043d04d000505100155010030948040741e801100410000d10000101640044101e501074188008042c020565261100c0740ca011903a648004201007031030400c18a07500d40005100f03a1740421148000659000600c03041445102c80395910b6103d98158a0701c40101c440d600070a13055503109008103d4580300000d41e04050315400c0307a400d600c0b82410301049141005541000f0001c00940070340041160820030000c801b00200000d0b28003071a0300d61a000303442c8014965607006030340481c0503000840d005c2e50040941030b0025080c9164005141c0341c03d0159800b42030101c0f0014201d00810034000c4250814a8109a22001610042901e0b420716055808040c0010f0804200c0320041004c00d0301840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 113692814 1250 113691564 113691569
    0x31202071a1303080601030b03061f08030c01020c010c03020702100309020402090d05010207060c0809070312020a1403130905090d120b090f0405060a1103041415010f08010b061608070804 82
    0x1d41c07961841c90034000e0003016841d106400ca01096000b00481d60300c0d0b00900600b1501400600142040e41e50083d000c0380c80d41702d6031250801d98010110105500005100400c4040c610b4000940e44548542d0760b07608643d41c501004040501c1404070200580c0c80041c1e030024040c0c0c606c1e001c110604103000250013845100b0720668841c0c200c0d9402010000103402805681d0b000c4c80d01007040c20f1081d14290361000f8222070410454200c20303000d00000707140128030380751032503181304481c00c1e072a00369a40d108040d4900d81c5520554070100b6001ea4020180040001034410103400307000501b071040403241c0e150303541c501100500400150800103140154030842d0400c400420608243c20400110008100152402d542c0c0c1e018403000585607149a000d190481c4a81d040560314541da952521f00c0c404551580c900f00c02e0042d110480010049552424007812150514031301c40c80c41d1500403400c469018034164080c0c203041c054041c0c0503041d40010190721390041285941d13000e4501d000e41e118031454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 113694064 1250 113692814 113692853
    0x180703020c100c0c0308060a05060307050304031e08061906020303190e0a0602120f06060403080a1206060e0102250306150b03010905061002150c0a02010603050708030a0f050703120207 81
    0x11100300411031388008402031444c001d4581c03001580300c0c441840605e030341500601c0e4001c0000c2001c102400e10030001190310a001c2d00e40314400520b41c003980b220f001d098030903040016090f4828040d1910341102e4440407400d4490728554454a41702d006922030100404a80301a218239403108802251500524015651038007035402c101e5540c50000025044440f95400004c08000020403da03010156940517220007041c10341442d245a032010500d901c021050307070810085c031016541041941c091000030740201c1c0c4840c012402041d00082c9132108003032994244040b000d0210803015800712080042d00e4004030081012104022611301c400c0c00365000000d840390000c000100005240c1c081809410222042d6400500c0000202d96503500e82c559155119001c101180a15441c02c0007800f1215030f42c0008160b542da43d440c2c0c2c500301380070307540b01c650984c20008000c0150380e8071a42e11808080c49080250500111b42c034004c00480040c40440c09a50340040da02c401d0080080e00884c02e00c005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 113695314 1250 113694064 113694071
    0x11a0d05070312020307051e0607180b0d020d05091c050403030806120a0812091c081f1203080f1e01171005090c040b0102030f0d050604020405040207030518180703020c10 75
    0x29000003840c00802840c000308c15000380f0380800c01603449902600001c100b00789120b04024100702c2008030b994401010300240740d900f000108034440c550b0103900d2085400e000a401102038482040400004080d020750801c2806c003c01d00c000303908241c00d2600040c040c0e50744c62142118100c40c5190844495007e0003001c0049031104103049003035003582c812850502170b50130300c1e200e141200c0401880ca0b06030700046a0b0700d00c0003811b1400f41c0076075001041007600c43d84094170360344e40c2d8200702c0b002c0101d41a40080ca1150800504c0c82d941031403143c100304c40e0a0b4400984511242d074203505c2c00180115075100c0a5070050b000d14000130404c00000e201e0700d503010801c508004d111142d03110702d4041c0d075034040c07414008074101560020040c1c2c1d03500a110080340d480c001154180c180144001480582d110742c0c00d00011900da141c0380302030000540300783c4940b0754604150700d00d40581c06415113050f00c10000c644081040c0b00804c40303015007103a41420050384400324658202d0400040030711a0301941d14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 113696564 1250 113695314 113695333
    0x804170310061106071b230106030c050306160c030201021312060c02060609071211030c25020d06090303090f03020d1101110717040314011a0d0507031202030705 71
    0x90100751401c0740d04a4459043c0441ca61640d1512114100c0300300020860a00c540c103a08411201d02c008018031420710321050489040b48007000d80b030b061402e150701740c0d910340c024020001000d40c50f902900045000305910320706416000c11010b0314005003010044801840c0341018001d4041d180c3c4c0c030071496140103981d900d03641080015244070748103036446820b040c210743d421400860014060f60000d400001c03595203000040d2801c0b01d4401c146500c0350368070388001d941460380d84043c0d030060400803230044e581c143c400111312400e03030844808600c24401e03c42c95001a560345001c00ea4013503020070040746011560030140c1c0180301c039240c06403100a200b03000340101a03000c984803504519a03210100500e01c42103505080343d80e03140c500700f10202c0c20001000444c000c2951200c405280d07000c3c0501c0c21703413680c1d198025603500402418583c4c1d140c141e200c110050251f804202c0010980303003811544510f45481e0341c0d031165440090f0001c0c1c110381e020028944240200c0d080c0a0f007080c12651040c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 113697814 1250 113696564 113696581
    0x406150b0705030304110d030c110a08030c07060221040e0c04030605090a020910060917070b0f04050102061302090f040309050d03080a050601050702060304060f021c090521040608041703 82
    0x24801c96084489080d0117030746c4c4c0d01c2031801002011400b50550f03956a103001c65039a45000700c00f540c03462680d00244040000a000400308001c0140301421800b502015145c1007010b481d140e00e044564500401060070484800550010781341115141c00403500070383c07600c004e00c1500e407055401c042e00352401c0c5410025141d0300026605c089520035a82035450343d9404580041094107401814000340084004010032010f8054502c03500554200b5074a641c2da407404244c001c6e9016641c04010b50358007207410407256130140429940402c2d1540d5016242e0070399800104d1032900104001c0c940441340004c201414800d10b09407005c0d00000d081711000c1190b134240a01070b410100c40e1000b01c030341031200040255209400f622071003540a0f105c6030443d03c40e96a200080c0c8040808080c0d0b0795804c0c000f001c04a400b460103a1410030a010300050250042d080c02d82c14031202041e0500c603c1004070350314000881c08422141180d2191410324456103035803030518611880c0311041000c805020003442142d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 113699064 1250 113697814 113697817
    0x18070206070e03030306010c03140d090b010810021327050703060305120a020a020105070302011401061d03061005040b0d0f050304050306010909050601090911130218040905060406150b070503 84
    0x4484545403805425080b104044d600d101c12502c00d800180e004514800080c002e11644c203540d0540100d090508083c082141d04a9011080c113490250ba1040104001481230002c01113400200d01d0951508210964040450055105181000c112200304c03862502c04100d40200c101070030349041c070450402000040c00b50030725000640780d5014034440c040251550900700e8202a5483c1c01400703e0100325001902c2a0f0010030040e810765407030304160700036a0319050841d4060a02a00ca406601d541c0c3d05580a000030041d0b40c2a029911020a102081030344450b440d0490380120350210310045040041200c05140c0742000704800d0905c202c000030802d0200142082e140143c0444a0582e42c1d114504166440c848018105800140040c041c180035034004541903801600c200ea02025604081600c1031588410743e20a6580850035101c8100d5140b00a01411300803a414800441e054403004e40700c1e040980001c1c400c66503040da695049460a0038200203201c68849940c8030101801c0242e1607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 113700314 1250 113699064 113699071
    0x30604020d02190b09040c0207080d1b0b0f07030c0c02090c0c0309040f0219090b07060f060e0702060114121c031803050301050924280609150906050d0203040218070206 74
    0x2c030f047c04880d105861002806800f1100c1e500c0080c0460000c0200596260b85120b5170002c03642c1e866200e080c08207980825160003094120b030000d01d186004000242145c2406c1c03071013001c0140c21542000581c0d203108003560802c800c2c0e401c2c55502d50014003072620f184501c8021070340190801000b20742c0c2d21a80da019103d038580e01075820000f24403200045a10091a0181150003e0305008000c0414450350040300e09100785800081c120b5240c0030501e543e0f444c1201c01d440140c0c01f0710014081c030a1000300c080e15502055594010540c000740b291030302d0700d901c040c2400b600042200e0034404035209070030405249101e268a642030300c1e41ca003001040b640c000d009440c0948041d1010840c8c600111210018a01c50141c0b890600c9540b032003044580310b13007280381181907106044070000c2c0200c5c2c21050b1000303100b9a01c446200da8900140c8484c40302201103440d0900c080f0700e10800c8840c1d00a412680c000095000c010b030349584d18030001d100481c1003a600280030040c0e00800c0074807034001407010300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 113701564 1250 113700314 113700319
    0x30d0e04050c09030a0f08070b010e2a070809150f03071d10080411090129070804030b040f061b08090703050d0c11030a050d120605030604020d02190b09 67
    0x81c95a42c1e030144a041d01c181e404181d05076101d8901d907004a0342d22108a0a5580b140c0406450b00c200c07900ca0501ea40d800780c03c0034440c07520f410240004608483c060a01c100c0c50203402058003200707180d12a0b1980204440030340041c400180d006141d80c0d804405240d480d400315100c0f901c0304842560700340240c00c22140c140c04516104031440140c5856002010540402050710859105e060421242c036840078204903808540b004c5106c07000c1c0da41d1000c19019021003520400c00050070030300c0011120725071a1107083c1000400035200401c2c081c00031201941d400c2040d0103a582c540b40340c00c803610204c16a000e44950302c0c00e00c40b8422240203880c0194035903070b0b964031110140c0712841e103291a8100d41c0720007030240c0c1c85503074640701c914040d82545d4110350180c007002514414410100b42484001d420454054024038074060229811001505200050110401c181424000031070754504c00a480039114090041ca4041195a0a81e4041c10240c15200321400c10303907642020206504944d07102807 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 113702814 1250 113701564 113701571
    0xd030f060302030d020a030f140412110d060e07141e01050408061015080709090b01030209040e07060306120b0408090f13090302060a0c050301090b06070f050a031808030307031505030d0e04 83
    0x294814460541d410000350300009c1107103481e1600414000024585104980060010310803002d0f0395900c0c042c81c11104e01800c0c0214420540c680b100e820101d554100040203040b01c003100c00962200e4104020b030316860a0200d034080c80c0c400050b655070181e9485202d0512410003080368142100104600300da50b003101d000703000601d544090301c000404035034400005942040c20031001c0035a0b0054032400c030b0181801403801c80140082020350700030b00c494102940c070480d800c00c403259040c480c4200604041c1c0e5000280c29a655a5591454000d40080c1c21488040380c01c3d400359a40903c0c42c4498a80200113000d41600c0c8168a8094069500e00340d015005900000e00f54036400c0c00744001c4907000340e0f5030718a1030b800c0a42080040084000080d040841800904001510145040c0c41140180e0043c0403a1082d464014201880c004208044403000d070f000300141c800020a42c1e03006005418040b9850800c1809051103c030507910103a490300c18640301481d0141c0191144103005c00030b42d000e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 113704064 1250 113702814 113702837
    0x3081605120c060f060906090a060503030c03030103050c090424060b0304050a0c0510020316080d020408031902010606050406030b010c0501020d09170c0a020d141204140a03050d030f060302030d020a03 88
    0x40301c141100c440340c102440f40c0007d5142c0c43d143c140b25502c4290f01d9800102e990f00c64020a107140c0291300d178049190300c0000113000b80042042082004030040b110030031390785016138403040802c46610440f614501d21380e0841c0c40c0706245410007000307400f20501154603440c040c100150f6409990800391030f07050b003c14020501d03082c651482700301000c6a400071443c0a09085241317a2032024000161400743d4284410200c1a00703d0000344011b0a0faa0300554661480b040c5426424840d2402d200c19685000e80070010590450242c408580c100d050026001009500503207084104030340080a0b544001003600c4080d246a020030101402a000c0410703905e04100250410f2280180c0c2aa29a101110a00040c0740019861000f11301c1864424110794903900340702d1501c581801e02c1c0a191230b01080a2010308900b800003010b00300f08640401c08a0f1454071201e0b19a0210700080003050307107549034440e092400b60031410080d0790140c12610750001c130a000940f920710a0760700300d00040c00403045 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 113705314 1250 113704064 113704081
    0x306050d06090213061a0a170f040b1821070204060b0c0c040902090a0203092503120305040309050105180303130f0e01080c09070e04151503060e0103081605120c06 72
    0x9041c103490071032020701c400c0c1d10810541106d6401c42140c5104002021480014400c0210b50003030080e8403040180c00d40c3c0c1090b180045003d20018054100682c1006141d0500c81c0c000540c0740201e0844030388a8114441c0106031100391044800c041e4015003066000110340c03c6140c000c013050282041a15200074289040200341d030b1380002c01950081018010504a9150307600031a00103017103404a5030105143d21203000c0002401250421107403500008201303100c100b0296040101c4146820802403a01da60301420880355070041604204002c50406400c884050804400c5e990040460307485145502144003111118029003404040c00b09000669000210b030490580704a14041e0468035006020f200c000240181500204450040b4a046030388583c460080c0041c1400106040c280c20300e00c1c4c0981300030564030744c4d00403d07150a5042002d5103c0311101410340303a03c616070382d1751030b01c281c100325120f004101c03005804c0c1d0281d8134103ca8049413230310007451aa0f403035034195481640d41951 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 113706564 1250 113705314 113705321
    0x1c0201060918060e160b09030d050a3e0f0d0216090504030c02101d01052505070b030112061415060702030f070602010e010e0d0c120306050d06090213 66
    0x354114041005510002842d140c0086200b420741380304a44000300d850054084244044d4003c502500740020264560704041c070140c510504503040141c589441140010104c8600703911100150b14030301092002155405a005000443c80d840c00d2122140748a0341c0e44c40b503070350440481e81c03071103041000100e107400465035004003501c0980c414091843c160387e800c01b51100030812800c011642c428000169201c8100080b59415691071070f13100d000c9107100501b15a02c01c240141071100911020b5030418002070740030000001c0f074103000148009868490300d0031000307030059032003400003000108038503600300044000c4c540155800d210041c0c071603141c40d000b100c0940703000c0c2100394030f243d00603003070704100c0c00a01140e8030281c1200c0c0c045000c03d0005040c0452900082c00513515050308211039402400307624071003803004000e4515001d5000003d007403203403032010051608803440300c40c40c00f09010350711007001000007500140e0f1900a07460420010032103034208078840c0b403c050300c1e050701440c41d11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 113707814 1250 113706564 113706581
    0x1140106020319091212180806010b0714010c02010509070b19031d0f1f140a09020a09060f232103071a1518040204050a0b031c02010609 60
    0x1000b0b18a00181d8102c50240d05103102000000d010b031801d0000340300c6505006452805000d01d5600c401e80c02046001001d080381b1525900280000002c1407040b91004242141101c603c0e109c1550b49003058a0b00e26241d4511080d00c121552a11010300130b03058064101522560301c005c2541c04540d21810603800e9401000e001403804041a071044d0074050003030340404050382100040710110841c200200703140074584210200c40d5041200f1006c80d14404885012102c920107400703110105c0484510050814020b01400c200c5844071075503030540d180c00082d80e0151000f401c0034000c02d922000ca40010b0b188612840362090306180f000e110034616111300c20141c00e8010030765030110b403840d221460740ca40d06c000c907049140410414000040d01d040607403c50803052102c68489440c1c1409044410101400814003401115402c0015a118010700d9079001d503044034000740c980c1301c0d03080107001002d036000c841d40c00d4400d0408507100941c0485807140c110711554020b01c0400d4035440d20700d0960700c108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 113709064 1250 113707814 113707817
    0x9070f0510080105010f090312030c02060a09080f03151002060412260901240305010f1e0f1d010915060503030a050c030c0d050d05060108040b06060307020a05100b0301140106 77
    0x1a00521143d88100d41c1c04240070b41ba403400841c411b440f40c4900c0c0f00406a65415408650756030400e013075003a014040943d0010318202d0412408151782c450020300d12555540c00f5031102c00200050703600e2800007110420300b43c060403407034440300c40d070030007941c0d8217000d580990306d0841c2d140b0009061441400c0b409004504028401c500c85015240032200f050094000c43c0d155482d02c0320440051081880405000840d140000107503285040c41403c4401801c5201e14090030240c41c007100c0a00d2051200385c040380020000b48443ca0620024005c001c540c500c880210580c00d000081d450f01500128540c0340981c40e0000481c130030745200f40444100d40b04241e015002030060710f824a010307401410054015030162440c0a02d10180da90a002405041368086040410f5011824406108056020b4400e0030105818107203520380034070f2100010f2203544030710800800034540c03510902c0301010042d48071040b105410607d40d80350b030243c00510907941c0250b1034850389081800c44d660710307603048402a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 113710314 1250 113709064 113709077
    0x20d09050604180c02010905100c1709061602030c010c030f0506030f0d03020c0703050f0f0f0c1f0302090a03260f090108040215030a0903110a050d08060102120309070f0510 76
    0xf09000b5405401120025429550381c1d00c00807020880c14000d01d0914070b03e01100050101c0b46e100050506c8002100e5616100d25500030005220800070303150f80c003c0064a01d61100c8501039900301e20710702c90300c001c01009500300840c4600c06038064218400c1c820319004240526a07a49040c140d585001100c2c10515500501c000e161443c0a54003c0401c4043d11007138440750ba449488051400c050202c4110940d4003410310103442010a0200301580c500a0300548488800702c0d00190b044058449807000301c0c020078000d050f22034002d504807100c400014000700e10b40ca540b03092903414170480c1c00780c0c204603140795441c00c840b1720070742021640203030040c211060400c1b90103401190050070040040383c1140300e0140010103a98164003561060070302c0c01010540070b803585001420941c040b10400c1c015400041080001100810100503550761483c180c2c0b0075548100040b03142503450112002c00c00350000c284044003001254400c15944080c2d0d69880f040d550302d0a1040102d543e60000002940 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 113711564 1250 113710314 113710349
    0x21e07050d0e0402070f210206090703080d060806090a02010e03010b03071206020705120d060f0501050a1206120f02151204080c0703150b01030c0801082104090c020d09050604 77
    0xb880700c002154801034001410201d080e40c0f0044101c01030321040d9091809642e101c03081c6000c4130714101c4164602e1002c0c065a080c556140369891059003c01071a4000c040b9414640000542c0210020b01c04c1408481c503230304040c410952196601c400036400126000012142401c1c14010024500c40c080c00401810b0304c3c004200d0745072506443d045401e60780030003140003c640308104001102402e010159600d03011000740c2000c0b40c0442e8000c15204a241c002040300342e03002816980e0105850501101c000030303551140b402420150030628031a008002078406114040007251540c3d071080d1460000240003101c0c450075402114800340e0a02101c100080000d60b00c00e001d0518102044202c420040d140e07619a214031703c440c0c0380c94010341d5849080d82465a0306005e4a010341d807142c106604154103200c881e503105d070640981641ca0112208800042610300411240106080075041068080d0941d00a454a00c0c428110340014060040411586044c0040320201d03055424488040003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 113712814 1250 113711564 113711567
    0x8160302030a0f05011e0f030c0303050702030703020307060509010809072603070215030a05070c2a05090c0408070f12060b040f0509010c09090b0d0204051308040603021e07050d 78
    0x41c0020300d4102800c0d00c55071107004015503805218040c0524680c018030382c02c030800b12900000d00307582c004104880c600d80c0800108a101407214196070b018500580c0d0303541c150000c02c0c50310382d081c0d02c000d401d0f10407070f01c001501952020180c07150320b03000d80c1c407410503448504503140e440620380103035003510340e190300e0f150410a00c1c041e84070082c0c840003081d01e00b49200b5400040460000d120b958020100010811901d4a000e12070140d200c071042c10810394404441c1c49455204410381e07090801c800d02e003943c07900d0240c42542c00340001c040c014044822890411021460b03a0080e1090400b144502407020809001625202040c0c500445400c4003003000c0c0d85540c006041510f4031075030401e60390705040d8001003030360240c2d52290076214004500c0100345200104150016445071080a1800c0f804610340d5603200000d54081e50121408609515a6644100d0480710664024440c3d440000d0000700c40b41c042d00070b0010080707504520b80f40c00d0001000340d0807034852500010b00b50b40001c400c03585501d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 113714064 1250 113712814 113712817
    0x3020f060c100c0906030c03020c0604061505040e0309010801081f02070606080109120806010302090d06020703050408060703150b0901080a110903071403010518031206061303030c0b060108160302 86
    0x140031071007190b00030a0107800c10802c80d1880e450b2240060840d62040c40724a8141c01008108080382c80d007140f911440403803040d102d080117400100142c0e194940f20011030105035104000d844002c004004484d2040a402e40d0303680088021400701311000000240428041550340c49100b031300d40c010340d02082c95a503050081d407080d281103d10710307928032001c100038800744510b403140d5104201d001c00840305040083c001a4000b4116410140104402120740c1c44400000c89401d600c141c0150302d400c01c9181c2030710540500d4009400c80e01c40d02c0c00f00202182e06800503980070510801d1030546a0710703850042d40740d120f140034581c0880c50000100e200c0000310351100d50300300c900030195030500c180e50703000a081c600341c2da1000328255503086c040cc519140c01c0c810503400c1801407660300da12808a06010b41c0301c0c006e40c0803c2c09440d84440000e002625184100c0c2c400d101c40490741e042e11a280d1402030003155203840c003522400421000690f05500071200b090040b0500d80200074038000c07092084019 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 113715314 1250 113714064 113714077
    0x3090306020c03130821090f190306090b0109110304021c020d020a06051e1303120c08030a0f0b010305040c120807080f03061203040e0f130c03060f140103020f06 71
    0x75100c00c0050b10300c0c0c4001041c2d904c01801c07610f400f41100c01104100c04601d40c01c0c80ca01628540ca040200c8001c1d5500c2e9200c02c114030405880060300e502d00e450a080810340d00381d101038107850078140c03c0030420001e07414689c16100c030402d04010104441444c145540412580207410006440c9441d071001303008031302004001d10003007a1507a000041e5010560000c15a0303c0003000c00c01c0400d02015101d4080344503020710701d030105802c0c00c04101040303928405010707101c040c00025128500000742441070110002d065041908a17a0300e003003030344141000344070100da4440118500318005545601c82c1c043d5070301598104101c6840c440c140820480008216202229180c400300082400100e1505c041c01504121f9500c5603280c0c03408606102000c164280d0401e26134004101c01c0c0400c0038003503040c41d00440003101090715030b035407000d040703460301d00b035540c083c000b828568000401c011254102110040601000b80030b60103e291105215100a0000a40c400c0c1e081404440c182040302c0945075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 113716564 1250 113715314 113715337
    0x40207020f0307060e03070e040c0339090b0402030f040210031d07060207080307050d030b01091806050102010c030923010902090f060108100b19120e0303220309030602 74
    0x455000c450009183c00300342c1d441080030a01e00c2e00011a640350a2102200610f2252051019880e15a441c030a102d1154000200500d60704040b0781da00c203540d44101c140000b0403462045030309030078403122064581c851050000840c148103203203495040500907a4051903070071105c00e48940312136003080501d41c1252041c200f01640c031458041f000025607100c0035403440c2840606012410f01d0802814a09150424039250348100081d00005000203070242e02140c49180000e80a5409001210040b51a07400056036001100407000c4c6034140b50f100000701c034001d8000b0001071018440607401c0d00c41426002e08400400c02003a00051140c42404100700e20301c0e000082c024415600103044400296030443d0325074800d40c204032165820055560f0004401010344c00c02c18903003822000c20384a2041d4203a10170344900c05c003d000c0e500500c1042594440c90009214070301c0c103c1ca8039680e0743c10881d6001e0212000070708010944034842018914182c25542d8078640d103003581c641d500039602510043c107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 113717814 1250 113716564 113716579
    0x30b012f0307150e0c130911060d05090609010e0c04050408040e0f0a0e030708031503070305030301140a090b01022d1c0314060906010c0c0315020705070602010e070504020702 77
    0x20901003050006003850307840b0b004090188045814100212030710803005000e15030204d90683c502c0c6d9107150005807450300515000c40c0d2403405143c1110310000780d140c02e503084800441c1030049109141c1000b8071401043c000c80e199580d94a406a0982d844003010300b400350040500350040e0b0070141c100c564081c1c02030b10a10703d031503666842c04800c084202c504d504608040d0090201002145c06070300500110036008600f080300c6070702c0e100d5030b610000d040c907643d404044c049144103490601c1500e00543c1c021060343d40b02e681d68000d00390a9100c0c280401c2c840ca40240c00800c1d005020301c105048004107a00407c0320141381da0007040940e00f1185007100d214070241c8502102d0070b00b040044a040d81401c02c200710308002942c00350a80d09000c681c104815034600c00c11404d07440f1100c28a0b80b082d003d103024640410903007004010649560405080b6006030602d60b1071204854001b409030521840031103000b01e40e60b4008900b01c81142600e800c0b1500075600030040c903e482e40240c041e0500081c40d99 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 113719064 1250 113717814 113717897
    0xa0b191503080703090617010b0a0e030d03150e13081b0a050c1c020306040809130504050d1106010806010b0307051c0b010e0a06021e010213030305070c06030b01 71
    0x300c25402040e4021039018600242c24810151701c1000c18000300340c2e6080030381e100d85402004500c071070014050b201d0603000200704030b9480752003840d00310b451110150641310101c2496030000c001d0b0940d95400c0c0d4088002cbe0030005940c81003885858030604c419201a02080600d540e103e06591007088120313040d165a00d854000c1d42414000e0030000c502ca14000c002551004092010080d1940000f00c541040b4206010160b200460b80981c80340d0300c07612581e95050104002a91038010b003504c07180c504d2400301040204040001d8110410031951107807100d02e80480d00715036841909000b054407035000f01c001004030800400103180c003c1d40310b00b0000c0c14940d403001940007010b456030a020f1000c1d00c5501c1c000c0c56503006904a42c0341c1c1829980201d206003001c0010f0340d2400132404001540703101801082c10f0003429410350b560607843e46040c046469403070800030402c0e086940c094692070b16034903000915501038866104401810307160398504281c0420003c0e80740080a082c503a0341c00f60611030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 113720314 1250 113719064 113719091
    0x10c02100306060f0306060f030509011d0708010b0d020a03060b0d020603150111190b0c090a0605030906070302070b0402090403020715120e0c0604030b1e0115110a0b19 74
    0x3411030604266500041c1185045001810a00104a2201414a0244144900d990200303190300000d0130341c100440e15455005070f076070050240d5040c501c40030042941740120b0000219042c0304131054040240101801c4d40c0411149141f144002940a103039500c04000240c4980c200600690006206450303200716038010404903401240e002020001900c9455500c1d80c110400142d0080b40030020f1064001e5020428548810344101030301011818000800c0f03c503c61044074000c180c003503c0c00c07520725034a903005043c0740c106071512013080c0508400181d11034824402d40704c40a8008502141d0340d2596002e0100c15003020300240e08501170380001060442060341190f143c5030341940c4140621000030b988038104d032075101030340203190005004031a06948038016101600d40084e690388094035410908580030385c01410b028014020300c00001100004030503c0180d0410984400c51104a145150368071106840c200500c0345c010710010030804036503a8070610079545c14003400208483c03d84034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 113721564 1250 113720314 113720329
    0x1051f030b0d1a1510030b060f0c0c130b09040204020706020702040e070810112505010e03072a03030302090a120f02100908060109020d0b06030a09020301050106020f0c040b010c02 79
    0x1079500c1070826007070b4011070f401c91441c01c0d4800b204a404c0d040c5102c2d101d00040703030404030705d0000c02019182c000280080d030b00c1600310381640c40741060b10341e0703544000310169072a6803691841034481c2c01c2c1000c022814a80d240503070703004220300070141c0035140e4695007000001c0d04546010746865a00340206030044c0c849210b880021071080b0004c02c1c18524012441e850301d140d104100f5003007400d04012000600202050350940c0c0303060941503110b913145100b80503101c11415400f0b003080d803d01c940001c00b5900031009103a070070f0051503100c4019a403220103001103403540c44940e0703408600c00010404a8070070382c0904200b40b00204400e050640d120900355201d61001d1003510751200700c00a01c0e00b149801007804214282c0ca050041c1c031603142002040d1216130501c1480320350780e0001841c0c0038408096008004400000b0702c010744134141420030310000d0611140c01c80c00b0703600e00703000400c0781c6000003a80c0100c1d201c41001808608011010300c800741c01c0380320640f8140a011503844006954250f03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 113722814 1250 113721564 113721589
    0xa051606180b09070b0c10052203080105100e061606020d02130806060108010f031e060609151410120902060f0705160303081303120203090c010905040501051f030b 72
    0x44003030381c0c9400c2c82c070f02031400c1081c164841d064800d01000780450305070002c65a20302049130118002003550300c1070142c4802030ba020640c124002c41141c0c4041c10140c00050a9058690548005800c503400d108140c48412010148580c40700c8284000c080300d50304580800d901c1449500f015040c81660100d100903a00321b0a42d40681b422401c20500c4584010400c26038031040900c0d00c0e51055241c00409050f6060360302003d843d0016800b001a8481c401151607020309900c00c500b082500d40e00c10345800107005064000c5905044101c0010f0100480b43c04501d12582c001c1603a400117031541003e4410f40043c6100050381925240b8400160b80c40b034014100c60408e100020345d550ac3d241c640a81001c0310507504600e2032500308010300c00300e80c5c0451400d40c0510358607101b194003c0141800d54000046068140e581c500000c00c01c5070602000c01c441c0250302c801e0300d401060326142d41c1000262a002d00406400521050340c00403589040505c1d8101e6901a0800042d42088403001c19485001403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 113724064 1250 113722814 113722823
    0x10e0d02070303020606041b0807030e03160b060a03080a0e030106051003051f030c06050306010c12020309040e0714060f040b1305090702010516033209010c050a05160618 75
    0x1001c10024540c060005030740c0910b007107078200103600d50a150005260100409401045000f000040c09107000e64004040040b462007205e4071012810b910401070300c4600c101719a030840803004030f81c2c14140440c942e0241c030350213144242031910580089507591194040c5503070642d22050005040d889081540d0340c03069603683c2c0400c50340340c120180711030040318002d45400c000d070b122010400f04850708401ca094030003a00c1c117966139480c0c002c0100c99009083d0303005000c00c0280204014082d0b0000b00078004260161800d1103106010000d03940c0320300701d52180c1c3c46100042200f1100300d01d042d900030140c54003902c0c261810241c542c8180545500214001c4101039100c8030140210300e00020307040d5100d0f0003031000780001c0c1b40030880841602205c030904c000741915441000802110b0150000d11088005000e44818000c2071300704000f004103030340f504d07129482c0c0b2200c00c0941d44584215002c000c540e440b89440c0c1044004040c80b5044030a4080d907219907607e0555403000f0541000d0a28903010303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 113725314 1250 113724064 113724073
    0xa0b221a0702190302060105010c030306050603090c030c0f03120703020102041d07090b03070f0e03010e010e1f1b140f0c0307020906030102361012050105100804080c010e0d02 77
    0x601e0191500301209100780f0b1000d850801c5a00107507001460a040d038030701303190064081d03180c0d02e001d402a0a140d00401e0340402d01008205180d900003035510000c1c3c0c1e0440840758440c10840c02c2c409000d5501f140107805800200300006818402001048428800d2000602c2c0c185d403010003207040b0210303010030306000b0781c298240110b55602040c0c402c080c20498410358a98200303d080a05035540d03002842090112441240200d81d400794440410f0070700c081d00a010401c0c0350748419860f00d000c9441480000480741e041140a041c5128041140349401d0b100c030084200c112041c0c5910010031544e84103100e0410040a82224200c007a000e0b429041e0000c54946420348100001140024842402a8414000061aa04482c1c80c02c40ca420100c520440c103e10f4669030612103030742c0e083c0002d411421200003527620a03405200c4c3c0d400018242d000f0000b50362250700f00500c082001005100042c42080400c010170074102c000c00c24110ba800000820840e4103213200c1c1401950a07013100542c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 113726564 1250 113725314 113725321
    0xb030a0506070c171201050906040906060f0f140a03150f140105010f020c03060604110708181e090705090102150c0c010f2c120f07060c020a0b221a 65
    0x403181d48084d0055209480b5040c80c0f803070509041c8a50b81441444e01c40c1d0028404600240c41ea507102003800d58100c40140807158442d881072184120503c01e0903c031000c008000500e20310b68031100d841d490342c02000c12520515548606184c443c14049000315180c0d5001340b001e80320320a2090360790040c2c2c102041e00c2c1c2585003c0c00034006c4030b0b4414004003990414105482a5600032a03401c1c0d015408440000d02e804407600c113240b036805042001080501c2c001000729440e08a01c203464052042140e422004c100e0058412115040140704150022001408101054010380203011101c01c103104450000d43c0d200d08100084405440c030254003000019864102c001c02c3c010041120010582880303251040000c01501c10014045e08445840c011481200c0e0141070103200030030445007000c40d4a41120f11200066a8000001110048d140403210401d007030000c100380701ca182e086500c02d0400e03a188040c00464292050888a03c81707411401c800007c1c00404450a21040c240c0c2c10b03030918903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 113727814 1250 113726564 113726573
    0x30519021b030c1f0302070b0901060f0b120c030c0c03070b0f070c020607140106080708101406090f04030e04110403140a0b04031d06070809040606050c100b030a0506070c 75
    0x8074280e00d814081c0c3c1040c09428429122004107071070600c00c5079414105802604001c07002400754584c02400d0601110501c0030072803054120350281c41420607245000d07550b540c0121440d226026101189228100014554144000c05103500008901c0564074280c00403000c51b04660012900f210071450324010303c4240c4416500c2e00c5e92080503424031403103d0045d9000a8424058150300038203151240c0c1003485803d1003908440b00034000501102d08441d00da0b958a0b41340c94003041c14030304c00c1d071610a00d242d103800300c26240d5000f60720140c00d0084030380341c007104d0340c02200703000b0b00075828840303600401005900e4610800317000e5082c4040c1c10b5180c80c2545444103100d60341c12a010710b0380c5d00004d070201c08118031840321038206a0501b031045030640001078096890448840e010f03030040e00424014144030a4000034800b000303040301c00b001800c2c1c07240f0047d907841c0101c0000886a50280042c25a420b01a070311032030441c000141260780f01b80c0700781e0f47d1078503155003100c4500001b6038042c0744d5410003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 113729064 1250 113727814 113727853
    0x406060803090105090409060b030a0b0405010c230705160611071205061914040804030b0702070803091203070209130308010b0910140702090703060501020705010905061603051902 79
    0x10301942000c0d51800401e03000080443c001c10002d144203d540707407480001c2040e654060280d407a009415220f000904e418500241e50080343c0030f039907035401c4c05000403400e8401c6501d68120b41d80f0013410030388030003050140c030190b8200355803c0320140304032405041210710668991004149555464040d8040d44007820b04021080d444580030200c034040a200244c4049072190384440892007180305038442c2506807020f08400820b403100c10406000303100c00c0c01044002001901d0003102445410388a808040742d07280242d204411142d08244040740445c905920300304603101e40310007142c0c100b00070381e00040e0100c1c405590032501070703005580328403c054100000b1030040002d0030382d80b420700001d00d022500c060f40d046501002c000103400d82c41c4869005c502a90011500a024240c0c14503114601600900d6103010316405882010340c006403070761240b2050340c1500c10150800e030400d9420504e0f240104200e036800c0b0305210050040ea00130f40d080512140601401c0d0b4010542c41c858a540ba0545 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 113730314 1250 113729064 113729069
    0x14070b0306210a0204021c06061706090601020a02060f041a070303240306150306020a090302120a0201020318120307030c1a0906040201140f0a030501080d080f151314040606 76
    0x602c914031401c6008200300a650b50180c80160b501d0003c020312070b01c12043c10160310b01c0c0300d1400c0b00218019a02c900c8035260806400210032841d00c86204000c181e000841e00140184e0060f16020010b080840142c000046400c44040c14a500c3d01100b4004510f070020740031010201042c41c00034548e15000704030b0320075200b0318400c0d1410071107802480c003c1c03000e01019141a45400e07011017025034501910b0000d54105908640f40d6a080ea0001d102c5985880117906c0f400381e09008100c2c1e5100481d0760a11581c0c140c0046140c0104c2300b4013107030b10061311540ba5501071407540c82034450750010f2000f08041c1c0d00c40e5440d000804036a00d0070950800041c00c0f0495405414420000030324070014800e0340083c1c09013801c01c2d00c140c034004004050711620300000030070075002c42c0200ba001e400da00300c035050311a0001501e855441d2520300b2038081c4411648401c1041c03c2030041000c3c240c0130340c1940301c94000585100d0002601408200c140c80d14408101198100042000700740644ca1042002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 113731564 1250 113730314 113730349
    0x308100603020c1c020a0b011701050c030702030a110c100206010918020a05040e010f02041203021b010c0308040c08120910020f0d0e0d020301090809090a0209150714070b0306 77
    0x2445120f4016070b9480d114811684c140c3c110100c0303100c480c18020440d0ba640107901040310b090540e1a41100c980d001d640d01400c102c190f081c46c0100b00f1702c043c0d0340240c1c0d02c01c400e15030081d81004d009441c11100881c071050300c07220380e0240c455241c489868860304410003901640040215500d01902401107910382148110307201c041496140050380e401505104442c800c640c08200f02655480c524014046040c88818035031001900241041c9484190817025000b90241c3d4003c00401c0c410a02c1c019a80034402c0c0015001d0011000007400392407404c0e040740c0964071491106450318103140c80d010000480c120f0316000400d802e0701518107c0d00900040d400c0f8405000c420040341c1425942d224884448018403031503460b441c0d0345444a8004000c2150000c0092101c0b11003400c0c003051680c40861240c0c02004641c000078004102070007100c10401d0003421140d201150100030301c42c19081a07508542c1c021410710048450242004444023400319601c2c500d0b604d0900104102c4094072500c0b1350b62 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 113732814 1250 113731564 113731567
    0x5090d0801030804181b0f020c030a0b040209180105091b01050a08010e1305070e06041512080f091201052a0412030207080319030b04140406090305090409030810060302 74
    0x800a00d9103400d0344c00303d42c40d56001d005c2407403180451001400e05c108100c41440071410104111507031041c6041c1040070582c00381c840c213050364001d141d1649510000542100200000b007401410504e400c25030040001e513983d4683c501c0c0c1d170b22803401c1d50004e50314a000390340505510900c0100741e080e0031038541d01c00d007469480c000307541030f001d8854001441042090020080010144803000d001240c1059000084c2e980c0103407200c03641114100705845150003a49404d00d0310a800103500c1c3caa41c03e0b0760701b0144c1c80c4486c1001d40e4a080003a4803665030003250705002d02600c5c89603100e500c5ca40150b41c046c90300100f840d10700070840340d003031982280072103100800d840d041d00f50003259001141c0681c0c00020b02007002103506d0034141d141604c2c41d07014012501c00041c22410090580d86556484030140c1d8082c05100024020081980c50074072007040c03203001400c080360000d030300361f8090540c03075105c0d04081d41004400030003c2c0c02c82d250301c00140c010171002010090081508410003011f40483d06085 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 113734064 1250 113732814 113732819
    0x3030501090b04050f04020d05070810050103050730020105161a0f13020d0c0f0f0e010b120a0510030c06020a140105040b010b0313080310031b03020603061302040503010c0305090d0801 81
    0x3000c0b11790f0054000390103503608030070300000d2200c14014031029140b03400c21903800308000100c0d44001e20003440142c0707050042a00124084c041140819090030b0001250070205084491610034581e01c0031040f030500c1810030400a15081e800c0c503600e01640038550341034414010113101404031034014600c3c9194881841003002040394001c0e9a045946c0580300b113817610b500c92800005880d45030b00441e02d021185600018101e0740f0091003005d560402c403055666903641c400c00181c41c042d41d0342c2201404600c000081c1404040d5110551000202240c00e00a680e00d0301e48101024070764001d0070060b008115900140115890480c1108442d000200f01c035142644035021401c0060207480000da00000101d48031240203499032000d030760041901c954030f013400340f00741d80243e99600c001ca407041402161720051107900c48100d006c0300c0d00035100610355a2450100441260340070884414a0b1b030a000104240d2024860080b0245440c0c800103000c0c10480303141450301d00126041010400b009005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 113735314 1250 113734064 113734081
    0x61e0c08190203070f050c1203030f01060e040b0406060201020a0f08010503120703050c0312060a0518011e0e0a0c031107030c02060904020c0a030905120304050d12020a0f03030501090b0405 83
    0x200c501881c598442880d0405400c1c100700e06501c2034010203082404017482c0401803100c0400c00d20a2040c0c2181d501e440c040200e501d00341c60b030008881c424003a201c540c00402896014035240d00c4c2d040720043c400210b4030369070b500203400c90701c490700004010b0b940401e440107031a802055101d0441c14900303081e155507240c403002a036140302080100c5681c3c080420343d6000c15000b8002c0e04c00340644142031320340310a81070f00140c0507140c0450b107481c0b240c5000200000c25040c09003031414058419102a2150303802c0c207241038503c005080410030030411011000503880100a441340c0240314121000c0380602007400000c01303a4580395801000181e041140368006038203c1039640c84298103071035668661901d82c00080080c01484000c0784c081c05a102d01ca02050390028411043e02c2d402c6600844481d840c64619503a0b00550080540024190425a000c180e1a0f0f60031101a15640b045034a1940182d40c1c8002d12054411f040380400d4550005000c41c4183c6d00605020000c140c80402051601094 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 113736564 1250 113735314 113735317
    0x40c0b07081b0a0f080a020d050c0307240c020c0f12072d06020a050d0203131a04030c0602060108100504080d0207022b0309050405010f180204050a061e0c08 69
    0x181d542d00c034001a1140e00150082c484141da20381c00c2081201d5030303103450800c50b05035400550100010f0141c124000e184074040d0003550b08080352040203500b4646590765030120305c1760009092680c070103424044541e88019014100784505941c2c041c0c0810400309090000082070000a9407045c034409124031103e282c00103600e0301301d03038046298421a280020003886a4400780b070000c03005810704240070494540001e26102d015115504892011015400403030b281d00176032207040504240ea860810038840030404101e4202c0040120528090b40c0707550b00040f041c610b40c066005600300c0701c01040030741c0742804100d6120b080d0726001c2c0524035147e40c1e071010a05c144804c0c142e06590106042c1c0c155210002161440602221481301c1c800c00d1000d11044c032024040102d001510300d04012429040c540900760403141107840d900c0209040030399040d00190781a10400011b0341c05e04c0f00040f1640c2d080d1350000204550b0b1aa10000340c00c0a20413900140d41c40c0250041c482c03180c0a400c00600c60700c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 113737814 1250 113736564 113736577
    0x9060e0306060102120a0c06020a050309101407050d0b0a0807060f020f0c010c1e0b01091a060d02210c030105010801060f02060a0e0102040f0b2805070308060f030a0b040c0b0708 78
    0x101a66117046d50001605e0b01c3c0102d003070241681e440400e00e03d46c0b59402c0001540900291000c880c81c0505000150055887c02d1607034090140403080402c9015014034040d01622807411404034104600320b021134058a201c0c1e0140580c1c1e48060000c1100942060340f00301d2503247c81c406095054840302c04a5034a20440308042e04019400080c4410f10a80303060044170380c00c0c00f06203413080c444142800ca810070b8080c0910150140f502607103840340320486100710480c0c0c1e4040e00c0d5030700340388500c0b100c40e0003900407030160403001910701749400c80041100102c0d03110301c040d8075103652a541401d000408040b0140c00c24814403480d803100c0e5180e6500000ca03180d200c0c62400001c1480c8400f506098007a004660001526004000002c610b06202c14080e0002840000100b005a060104041c0b885002c207010600482c50411008000c280700366461640900c016103810000201b081c0464546501d007603042d02c01c14404ca085c0f1080005010590004118601200303080650382c1d200d061144c81290f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 113739064 1250 113737814 113737843
    0x3051e0411130c02010f051003030e0f01090302030f03030106021509060f0a2d0c08061305060316080d02010c0f0905040207060f09140c03010204030f240c09060e0306060102 76
    0x11190704609a45000c0480515240320b1000c1c06050449071001e80a0800300415255181c103040000d41e403031142000c2c0c0300489416560b4810f020030124140719044803d186501d040110340f10001c00541c4080002840d0304107a00d00440c1e40f9890900003e080105080000017001418024030001c4003000130300580141e6400340d403080c180c03139882d1808000c0500c198401d01d40b107090220307600c4134888c103880030640700701a04040c004d00c540210304841440c0c04450386a400194640051610f48048e0702480d8001c03400303811242499020864841d101005500001c0d40383c2c40b14103082e252541c20300801e09454001c1c10900ca140c48140301c041c007010f00700c2c02890300480c1c0c0440c503081031014642103001281c5004a040143d400c1d6401e2903152210b999150190a1061013407020003410140300300c5017125005490420121034a50307980303450780190a0490701141030200180300c29582449143d1160a031515400f80180c900b48003e0f042a4005204034841e400c0381d400c000403a40c02081200ca81c4149 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 113740314 1250 113739064 113739083
    0xa0308010906031208132901050a060207060f020102040f26070e061215010b1308060f13080d150f05010203070506060105030403021c1706100c030503060f1c0303051e04 74
    0x1b400900b40f030b808820a0041c01800010405204d2520481c60320300005444912a508983e200c40601908000c1b900c9400010b9000d900c040042600c1032813414841e07132052001600d403076a03c44000750004529041000c038185102c003004080700d40782c0c0315000d40200071000351000900e05035100308881c000034200c034001c0a08040c85076187e8000d111442d409048950f204005503194030b41480b164001c0343c101d06410150f101c02003103401c0c00151551080c0003000903201180d07500001800d041d50311007011501c1d420240303e0700a400c400c9020f02d01041080b49540d00d60140340125800c02600342d0b610960664004000300c038046140811050b034005400c0c208203940351210b1400301d141128443c1503184056507079100200665100300a9041070b03400e1203c01c1e900307480d4041045018000d00001300c1c00300c1d0900d0340500c0040c1c000c0002e90b40c0300500600c000c030094811004182140928048029241b42c0444144200354040c401c01d900110701c900007844900c4411111007030300002401c007a000450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 113741564 1250 113740314 113740321
    0xe01030209130212010503010507020609060105100507080a0804030914060304020d0f210905120606101818050c030709140301060b0c030a1d010504170307080c0a0308010906031208 79
    0x7600840c0708000c0c00b000004543c0c5404480e1301c00c50656080c05158865400d0001041c0c2c954400540b560040000c20080c0030a40d20781300c10070200c8842d8823002c0013404818411480401c01039006400541071a45031219a8586450000d101c074210b6007003100d103810f07006941e980030341f121030a1b0f90b480b6070705031808400c006103400e001c40310002901c0000c1682c07030b1140001c031100b841784000c50b014404036216007040340c2d10b501c1008000303002680304015641c060070001e0020320306000c0284848295050410075441400050040c0c0280c541160f01100e42000c19800900118464a030340140c4230109141581040381c4c001303001c481d40707100e82020800300d01c02c171a159650a41c8070500030071100b2401c554a00110605640705e0300140e10b504007244204074080c1c44040c0c3c4500c0c01011000594a00d490142400803580e40d400b541e420180032480207000c45800075003100014444002030701d0041030042d0b4180390003480d94030160464485141043c9040000420300c000d030f182c00f15118200201d81d0755 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 113742814 1250 113741564 113741569
    0x150a02040503030f0d0605030613030302130515130f0605031306060e07080609090601080c0d0f0f08122d0702150411040c080402130902010c05060103030801050109050f010e01030209 80
    0x901e030815649800001440307021040c0000080c40b42150f1aa414041265100f0400d80c13501400c4490550400d441140340e40020b10907801007130402c00c40005440e145858201141c807a00400d179003d180b8410004480ac41007131840f400d44010401407a07422000c90414000070a1030002a215104144078010010100411038111802070192040d1603003542c03070b003110000c10045003034030804e000e1800350700407481115001ca02c85040e9003001c4010610014884e0610050b1200c112090301e16407650340040300050646000c10a03201e0013200300b507072244980f40b038079818928060a1101e035a1484044801d4400114120b0380c50072a441002105a59032100280e00f0401d1005106103c943c019042104010500c400925860b205490802580c5500c0106032030b8001d040d40c010354444910308140013103000503080128003030310615000014140c0b0756929031500d68281c204401180407080140302950703006a40c00c0050400702e0304405036080342c1c400600031038040c4c0707945030406400003441d00e4180c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 113744064 1250 113742814 113742817
    0x1b030c0a080a170a02090109060809070b030901091e050c0108160c111021090804030f061806050a0b0a032609120105041505010312080403120615020609030c150a02 72
    0x2c3c0e442c04042400380340a080c440021341c00002d4181c00700380c40140204149214086035449203c41384010500b042c00c1c410320300c005420040240401d59250304500000420031049100454511030340d030b00c0b0304945490010706119058180c2810400c10404200b1240c8042c8ac12440c3d0b2146800c00003850000b82c1042821090710404158101c03101c0160021b005034010501c000c415120280b0300811a150100c01c4e0039510b8005010b041540188424400f00c1c0245544400703091080e180056140c802c05000c0d04c0c0194002816213410303035901d0400c85003000e07501624011300c8044940200c5c05007075a45050010340a0403081c99410420a42503500c10315030000c5030b0f0b401800803da1400040c80a0a4502a0208039011111064054600c0308040803078001c2d64146c2e9030201e00e014a00300b41c001c1c00c40325840000c0c0709804014910303180a0340561144114805030440b004107003401e24801602905d001406000c0940c59402081040950394001c1b400005a1241240d460102d4444001d100b019 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 113745314 1250 113744064 113744087
    0x70b060a03021c050f060c0d0f0e0a0b0108061e070e010215090a05010e0601140607030302071e12021527100b1201020408030301030b04020d06050406021b030c0a080a 73
    0x40541501c044070100c1110229400f00781c441c0c0100d51400c00b00845644d00c40c0000d4481c1c2020310814050b400040c61590800d804519540038001001b910002da81460003004440541e80303072030440014020100284655948058000c43c0000c02000900c008000703050010040010844c03407101c2040e041e882440a1800e07446600e0781c910310b904140c1d04098981d120510105c3d010342c80d0031401d010801000c6900b504a941208226442d4142c10050100a40c00f100e0114105582001003000064011600360210884410483c61014003441e004445800c03140d0080250f620003401c07200d0080c04540910f501484ad01816050700c001c1c140185108102c0d201102550f005100a0610203403803503014103441e003011070b41030f4002c0078014005800c03403090b40505001c6030401c00050000c42c1110710310740d80180c030180c41d0300c294075010303210310301165019038040b030f802d940005052040900522116124503210b07005549000c0900c41c105580d1070a071a4000d141313a074085030480d0800d0142c44101311 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 113746564 1250 113745314 113745319
    0x203070206190906050c0d200f070302120f040303140909011e03140303070801060c0c09051009020d0902030706090e150f0d05070302011e0210090c05030d0305061c02010203070b060a0302 82
    0x20171b0070700210901c0c654014810403122246030440740c043c81c0041c80d500a03010b0300041440c51415058490005440d400341c0d1302a01136200d502400070510302d000000344901c1c1c0880044984a9046d4030f030040c0500c0389418001c2450a003800708501035500c40120364111251080d031442040088510b00d110304510b5400540107a0f00600c06805d00076012004500c2003105940e540106da0f01c0754415152008008400b5045a0410b2014803490710654001900240d4480010781d10560703482001d000c1c2d9000b10f00001034075845282000450400301300305405000942840c20b00b8500b0102a0440742d0001400c200074140b410301f0301140c81d00c959a00c810000350160511510901c1c4c0e090080e42c0e03103a81d100407400144c1a1a003200d02c40001e540c40d40d02c4043d154064a8110390340c2d40f544e0080d11415074150380f00118554000340c1c95a04021204845045840210b01440d0020400407651460401a025401281c002381c0050fa4040200e401240d4802420850394a0f84070109080030004e8200a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 113747814 1250 113746564 113746571
    0x5310902030c10090f06021203070305060a030b13050c03010c0e1509040905070305100b011215090614040e0102070b01060f030e07030b0405160e011214031207120203070206190906 79
    0x10010ba502190351019100b0006403170240da5901e13001265183d40e01c602c017000081d403e0000c18140d41c401d0304002c0c0c0220b401030408442541b262603045840b80c0030385203201c441070006281c1b0204a81032002c24a03000080b4020040c6421004024004011081402c1d208415404884100b03600c0b107019502c0110000d00104040b80c0b42d4502581c0ea4078803400150744600c5081c03021041d00c111405114001e0707006940700000804654828070203000d10021445131a003190b20301040142151041c10001c2095015060201d0802d00c01d02c812503030403031040000c5900420001c0701149410484c0c030304407101071a105840c0403041c50102c00401d0040c00c00c1d42e9a002d10f020000c18000a0bc0e034550085000300181d82c600024120001040c9006118120400d0842c0d001040410318046800e034a1a0040a01043d8070010108260855211052501d00d4042c90740901c501c1c90362100312407404a010031002c6155062401000c0e55980e401800d5006003560b400040c0d545204680002c036440754810400d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 113749064 1250 113747814 113747839
    0xf0f031116110310110904020903150c0904060b070218060a0f240503060a05040506060c070f0f0e221103010216060e030a05070215070f08030105310902030c 69
    0x1101c9845400030754400c2c45034064400e5200c1c024440c0c0101014000c1c5c0343c62812500d0010f21005c0d4020030f601c554140034070909800c1d0500b4040e000e501c140b07c10b010941d038807040a42000110b48041e00481e280c1c940500c42e110046c0c9400d0300c1e4000518101c00700059680c0e50b10002030880c4010782000d00d100800b400f0009061003071401300411150300c1c2c80922285115070900301c2e810300003151a558480e10044c410409801c06074000c50b00000054042440c0250041655290180a601480301034495410420024004a0740f0001034450103070700d00543c1c02c04d060205040f80d000d00454890800c891042810040a1100030100300340280095498440342a4007042508403017a09407807aa007001d0035543e41e1940803044468003034040e120242020015028005400301c00364403440340a00400040020036508030a80345800c0c400c1b005542d40e58104030900c101510b9410006c007000321030342900c281c01140482d40706442c0020500005600c002400080c0ca424404000e4642019111185 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 113750314 1250 113749064 113749073
    0x15080f100f0b0a120b012304050d0b0906060d0f031409181503030f040902070206071a01031b0f03241a0a0509090a030c080d0f0b010206070f0f031116 66
    0x180060400720344460130200c501000712400d6607040d090440c006111612000b420000c1c13108800c4000c000700b20050300309a2180c0100d201504003503810380c0c0c1400303440704000034124200515640940c0c03c0c3c86507001d0244950341c00c0124643d005004051121003203868640c0c4515000b81c034080b8900904010041d24007008141300190103492159200d903060001d94041d042c00030450342c1041905981c149800e00d8185014001d400030f0304103d90092040000700041085100b403000c48c403031088050380c40d951552500001e202210500e41000002a020800914500034003510440760004100f03081e420b10000d1031103507490045610b00c1c0b43c0b440c200c1840b6100d09210741c006203040c42502c3c1e5a80c0261503000300160a0340485000890fa0710402d58400028411000400b9041c070075113549061020724140c1900f0b41d0300d2002c8414103d0303540c0e40c600c00d040d13a041040340d0b004684c80c00c0051510070080310040001e22144a5034080c103072034441c4241d80e041e50704111621080c0100710a950b0000c1480c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 113751564 1250 113750314 113750317
    0xc1306060e010f080711100e0106210f03050307050706050405011d0703120309050a06051e0606090d080307020309040e070503010e12160c030b070305060a15080f100f0b 74
    0x2400c0008080d5841e1240950045081032064071064440b040303565502d640032070b401c0014150f6800c0d240149034012204020314000e001286011400110381c07a8201915074020100f010032a1b48613840761440000450010000c2e2518150117291041c0e803a0345100c2c1c10744007031090510003410145444100b20500c14103500201d00440d86a090713038032007122424102d682e4103440c04042e115031100902801c185019901c0410310510660546038451050348549007142c0d000c941d004a509030340c43d00c240c108510004481c0c3e001004039201c900f880c5040001c50108140603200600d100300c000041079050340200182d0702c6411005205100e0b100b01d542440b9112040c0b841810300075030901c0100b09043e24041400c0d031441e424801038508010310381000c015001e07946c050a6440d04203021010000c41e220382d420314030a107d05d8601103038600b010403d02030004504c1c1e2100d050300143d61000343c0c1407075104d8249500070f0100d03000e405207611182c0c441c1e6803545165000c810704e00c2c014600024040c42010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 113752814 1250 113751564 113751569
    0x90302070503030f0334020601080d05180d0602130303050d0b01050304021e0118080303071701060c061d0304080a0506010e060607020111010609020c03120901060303050f0307020c1306 81
    0x2400d90340318075681c400b4076035a03008400300d11000d000103000051070310010f00c00e036050140c1c9180060348104000c000c500c0021883e0004034005801070700040c00304110400c54040c1c0141d051600038541594800440917042410002c01d00c00c0e04901105424095130342c040d02c4602407413240d4001c0300c80e0380b480c0103801d51f84030f81300540d6124102841040c231903019600b83c1e8800c0d90003a240341d0301d0240440301d40309480700718507515050200380c40e074180031300303410310103036405001590002e540d03e08005e40082c007180310070750342e1511141540005000d2560702110380600241d0101c00851094200f4200500c0c1c0420300c00700a0f483d00c0041400940b5441c006140300c8082c0c01201582c0143c0d0b2600201c9441d94401c85140b500428100450760040d44101101d40491050400000d03d040c0c507401180c00741d0703200d41d0700c6a03810b03400400d10108007007403010515045200000204602861540e000d420f03801030360444202680c0100005a10f00e000388208041888000c0c00f03000204042c41c05400203203d43d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 113754064 1250 113752814 113752817
    0x11100b040f05040209040209070c0c0e06011106040309120804080307050601061106010e070c29011706060a0902070201090b0a090e0a0b030a02040515090c07030311041d040816060903 80
    0x125038078445007403885428042e03500a0640840d541d125000c2c425070304400391142080084103058400070a07268070040000d409200c0c15980241020000101500b01c0c082c101d5000c0d400480c04d100009811226a400f140c140400034003003100745042c0300f072003401a80d02c00592030000003400f40410602041c0d0354141c50407a190505580f0342d501d4010340e0703007009004003040c00141401068076035025a540a03000351084000410701c80d0448a00815400002460720040742c0e00e40052040071414480302d440e170203013000241158035090300028052451445004031440e400103502e01035901c10b18201d03014040410300d8643d10440134030014480220b0b403241e107000700d03042c0d001308035001e41501901319100c1000700101804034003030f001c000080c40040d1140702c1228202c003e00d4515118105018420524045501e0721038000e4140a400c1c0e0300106c95004646104000c2400f80c590051058440a0460911440d0030307a40c070324000180703125456513483c1c0400700d13030442e804101c4160010581180b0a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 113755314 1250 113754064 113754071
    0x803040b0309060702070b09010318050a051b040c0806091e0705030403020d050a02030702012007090e0f010b060f1e07062a1209020a091b0f0e0105040b030711100b04 73
    0x1c2140882c6c991400d4010048101c4042204070102c0d84a5000389020401090705400405920b45d070302440c0c515039030811a001e0300000b11480200c00c1c2090800d00c404426902440a2000e4074801000b141000740058481c2d01041d01040c00d00c1e031030803c030180341c140f860581c000c1c6041021000d005038101319000c400511415004848a52040080c1d44d180c800390b40003581042c031140d00644800805000e421070030009010f81c003400c5c09080000500078045001700180010500040c18102030b60962a404268100304008859440301422103492802d806041078484c040110078901c00f910302d0f080c4d0388411501080c6002401000e034445074001d14500f45031792807550001490581031003c025150003089142855201140640c3c000306121031009010031021501c1308025002c40360324075100056243e03440c0440c84a5504901c00c1000030400f4108008120b40e0200000d28a2107513014007444c0c0c900200218032294001c0800f0800c0108650940d0f2001c11540d4001c4018aa2020300c18401d508 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 113756564 1250 113755314 113755321
    0x309120f0606150d1a04050127053102100819141801020405030a1b0b040302030c0f010e1018050108091207020612040501060504050915010e0c040803040b030906 71
    0x1020346444a036110955000c5040100c18003c4000405640c10010b10303207000b15500260540c0c1e18170910340600242c86111041c0046809c807084090360080384610003a02d03082c28001c913803041c141c1c05258a0080041080207211149524050f600010802900014680d075a0314050380c0000650303101344c1d00c0b00d845602c60404548600261101010a0228100c030880424401b29000c004440909100f00015150a541d400840d00c2c000da910320607039080c003448054030000807440003010018200c080c206810f00e402d640000391912401e0001901c18501c442c1140e2040c1d01448c43d45179030f403c0c001c02d1000100780c181009413500c0546100b0120b201810503010403503601440200e07010360407034801050380c1460054240990340c4201d1f000ea0388010140321121000241000c00c0e403090348101c0000c40c1c100d107082e0901044d01c2c400340020ba62600200300c2030142000e1000302604480701c003100f0300e42c5616650b110034440e1017a0340200e41e1502001901060300d0f586600110301805100088540a56 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 113757814 1250 113756564 113756569
    0x31814010f0f0906110a050304080a050111030106051606180f060615020c0402030c04271103040b0f060103020904020c07140d050303073c020601230409050309120f0606 74
    0x42c4280d0756240441c0e65000d06102c0e041c824081d000d002e0a9840468205102030703103510b4a1a0402d41c003840c9250b100885130020440c003801400c240c6103e00007614110f504014001e44140180c1c9400485800c080f5030342c005100301a04440911050b4242810107540c07181001d0140303040000050702c0b96400d101e00090b00c1d01800780c0d5801030844541c003030310109514401f040003030761004d0034440c40300000f0300c4040741ca03034060f0703100103540141c2508555080d400007207400182c607840c4480c041400c20600420020400030001940e000007001c107241d50654415005038000d0080560704c9400c0391011640b100d20040c0010345d07000b5503c41c589001d200c7c51310003040011441c008000107085401c1803000c20b0b411401501241c5100c0840360782015100c113241e0508070482c1e02c00c410b0040c42181c400c1d82c3d07030403c0d40500005014001510009150b180c420300320904000305842c0d8240916511340c486018014184269500900000c0240450601312a00541d07215040300704601280101e4000c1850313403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 113759064 1250 113757814 113757827
    0x1240215090d14041208030414120d050702030412020402090a030b1005040e06010b0f1e03040f150c02070611030d020f0306030609240702030c010e0f070603060e0402040207031814010f 81
    0x102c84c0340b64000b01c5c103901695080e00c980c1001d4411034050360584802c059034075090200044007500c00c86a1340c0c0750400416140203454014003040f095410410040c0001700c030a160204016806540240e40d0341c540c5000304010410341c0d440903127140c1d40c1c00c040c01015907a80d8507100482c2c804403410f0002c40d80f5510b81c15180e0700c081c0b0558000303100810001a1a03400c00010380514100300702020034550305283d00b408241c1c01158115400101c8a03508001c22001c11401d4900642498040021074000b24000e55640a40d000300c500b80460142085200d040c10001c803024000c80910642d11110004604e61980d00207584a43c802d00480000a000780b00c00228010b8100b03d40000f10744000c29600036004c48072003c1c0900c01180020811540100400d02030300b81d034142480c0c0100340e10201185150f090071001e0304060201410a5010441142c42400013500719804860040e0b4a020a00d400e40e410082000d110303818070498500003540801d03944c88904035940a0725610388081654800f2201c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 113760314 1250 113759064 113759069
    0x3020301120201080415020a18090504150e0712060605010e030325021f0c03030e1f0b0103090c0b3411120307050c0a0e01240215090d1404 61
    0x120407404800303000d5845a603642c0c0d001070290100d0502c80030b0600c8000141d87c000e03000d190120b06008600b01080402c02010340082140540420807030409a41b151743c800d02040c0682c2016444450040a0000600101000308103500041c400588240390a8010340319a20406010030706210340c159203820701008a80d04860790a0072040c1003548251504c400a2682c40240e800040c90a038a59511021084003020074000da181d0100c3d00c1c001d07240c000c096880d086050366403600140300580c2c00aa2540c00303040c42c100329a0b000b142c00c8900c500120700504141101410f4107180202c0000e1112507030000b0000a6001410203400610080c40c40c2d4401c500200e024071a03001118020022078035226149a9240380289003120606083c0111461600b1190007038483d9081380800c00c5552908503c00c0009100e4003a80340d00661500d5023402414080503410800c001d01c1d200c2110b62a4400c1c802e82c51480031901203a2810700702000302070f035541c00920131328010890381000e0b035101c641040159800c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 113761564 1250 113760314 113760329
    0x6010905010b0304030f14030403110601060e010e060d18141b0607060203100306020c010c0908010903020606150d1a10210902010504030602040801090201080f060d030e030a06290103020301 83
    0x10355103941e54102d42100022280301b007009000c12060703090300d140c40300850207217000365211801012440341c031504044d0117034000c406002070703400c0910f5584d030452800140110103e603100c1d203607481c0d41040d801800e0400c070001c4c00c407886007220b6820001301c02c55030089070454408584c01c8140c15074001004041c0e2412080d4000340074864200010f84980040d94840400c540501c0d001e6603c7d61680305a8100c031145220a9460b1200c804a0591042540c002400000024000c000c0da5440103901c90348090402401848581c42c400380c0c0b081c042d011218200c0160a0801c2034510300403200900c03201010390a407240b54400002c4814900c6010a6a6440b00f8074080000c140da00c0070566000303103502c7c141241440401d00002001c11903e20140004011403400440d5050300c0b803000412044c001001c180389000e00009100c0c090700c0343d070182e010580e45410204d80036040c03000003a141c0a90503074001e24860601405001d00d4848548030645080107a4842c880d4013050320040d41640400d010748034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 113762814 1250 113761564 113761567
    0x101515020a0204050411090103060204061403060904020907110f0106050a120b071812080a030b1903060915150503070510021f06181401050405041a151e0306010905010b 74
    0x2805032500b9442990000e1086450851841c17420002c41d002c41c900341c0c4290ac1c900c0d40403030100422604a43c000007401c00e5040306030310b9850007800064100d03d0140020340902c80010001c0c144600803941010550150340840b190401c031a5510b034080c10060041c68040c1d11041000180c2c8109038100002c015405483c401c1641e680500858402c05c0007048180310759500b45000920081240740c2100c624092200c003561040340d00009001c2c2e80c0b040c140d940c0034454074030303210000c0900caa034448192540320b04080362050301800c1411114500c4280141442c2c68010000710340e51001e04408201e420a4041d240ca407a036480030070440028824081002d600800701011003050028905006104c10440014030980c6442d035902143e020079450400b400d548031204034403a0500003820b40140000c6406102900c1d00e0350f107070350800c0002c044140300200320f0004182c0195460f1459201c001c0f004d013054801c00603c404140c40014600841d900a00a071000170a860a95001d16410b84001c9160079 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 113764064 1250 113762814 113762833
    0x501030c06090602031920030304063e07080c0606012307030e0d0c06090608061005121503030a0905043b0f011404140a03020709110c10151502 63
    0x2003600c1801b011680303081000401c1460354140c0f0781e2240240c0c1251004c000d5482c2d02d854507181c403c50315400790002003030100c00500c118440c0795516030340381c0c4075001e011480410712182c0124618016418010b03c035100114103040b540000041541c8501d07002d03070700c1803049420340041d02503124080c86a5242c90004002c00c3d0046130054040c11100702000e8940d80c80802961685212504960002000126003500411605500034580ea800050444886080000a11006e801803050070100000404000001400840200900700b000322000c0c081d2650303040d0550f4010142d090501810b8030031032a003031103c1440d0029030503007885500183c6c1034030050b03c0301d00070a0f13841c00e002d050700190a204402c0035000760701003809200f0300c5010007041c0d00750034241407a26500007130b60a021015280d00c24000d05001c82e0380020500c04484030220009020a540701c0081500d01c213a41c3c0d40710301803113000d07540221703c3c45030760004004044814401045680346c0070f41e200398220b62600388005a020340000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 113765314 1250 113764064 113764087
    0x110118050d020619020303161403071d030a080c0709090c0e130606120b0c030f0a0b010509041103040227060919090309060207060918090302150a0501030c0609060203 73
    0x4901070140014910b50900340140c04288041c1d080c0348400005030004828401440c48901400e90000c0707003400d140002d030104c483d80a01ca400020040010400041c80c0401e080204860300f03012010050281c0c1d808002c1818590740c00c0d403012030713070190324400c801c8005039070b503118030400c910347e41d01003420ba1105160251041c81101c02425011003205410917040003c0c0c0c084c81000001c1109255441c085881400d0541074902e004102d403c0d400010410040740485400704a580201040000131f0302454110040301d042c010140582d800a2420310989050750743c80303010b184a28400c0f50910014119020080c82000c001884c03c111109603102180345490101c1d500d507800200b140c410b04001520580301e00581d60030030000d40204031290014080140c0c10f20000014005900705600c000f4035000c40d40001080902240244550f01c03000368013003500c00d12a4070541100031003100f81504041c280c60005000a2004031914228140001446402030a101c411983c2c1071b0041e5080c884800c60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 113766564 1250 113765314 113765329
    0x40318090c05070f11060d0507020607050a1205091908090f04060303120b0105070210080f060105040f060e13050106090617011805040c0504020a030f0b040b03030304032a080711011805 81
    0xb05c1d0100030050f40c1c070780b15448410240091072070030080455942806500681841d2000c0c0c0301fa0100700040180c28401500503003c0384203d049070100159070b54404e4049404d0030409101ca114005c1c20244510601900c05c000d4041010219a4402d14001c064200400c0b580244401008604c1880c1c2c140c3c080c07035103030780070060240040c14007501e4111b03160b0000e4046211010780d4008191603c007806031620035905101c0c3e10400a0a141d03141c0340c1484004c03802c0360140d12800f0308000c06500e940b4401c0e00ca800042030003251454080c0001d50311200090040301c3c1c03600652000440c0800280d40f410140e0f03104a040790182c040c8820b404030004840800307000001c0042d10440710b200b00000340754490b84000c02e90851070766000592403101090440544510b501c4140c403840c1006201c510b00d07900481103a40003581400c010311164030500b008240d80045000069100c02c882e0600411f00080d030740108040c504c41c1d4441c00c0e109645100554011010351081140746d240d41c0014003040c03d0600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 113767814 1250 113766564 113766593
    0x3050a08030703091b060e0904020603062e090312020a030503010e0703021e1815040e1905040f1a07021b0307030503041205010b010f0509090a0e06040318090c0507 72
    0x60081030500700c3e03803500285c8005d1805000c401000c14241041000c1d4013014102c09003038101c0e0960311509007500001d1803408060100752180c0840c80000180b00586d0280c0c039074203071807101c0d0305001a21004002d03003515101d01c0140c42c0503101c400c0c146206880840c510524680c0354480301c0c11039003820300600c48588000e11107030074103600b0010362508501182e0020a00102c00e8501a40d41660401c149041c10b9160410f5000c2c00320000608440a81d1900303440503521424041091a5107040b8540c1c00700c03074032045919409280000748006d00544010340e10500c0d01403031030318005903400e202c080928078044030100f006802403e084018011a1a038000138410020b04540071310381c0380c1c0c840034110b9204da070010b4050040e0b4000b00702008400c8c020006000803d00301b01c0051f180051002c0c0544c428030140901c01d01509001407c569140e45c016108071f1b6000341103407030354546880c01604055241c500b4502c0044c0d0303000e000031040d01c64000d6568121250391254240911a544d1124039604031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 113769064 1250 113767814 113767817
    0x813050615060d05041112150c070305040f03080706050c030f060f061b01150803120c0904110304060b03010609060501090302150903060942040303090219050103051003050a080307 79
    0xc106140f0001a02d008240c040c9000f4807010706480640c000700f0887d01954071416015070084000400700e804914142a801040c40d1541680c9688520b0201c0c0c0610498000300000c00313903010301205002100c0e0180000c40e00c16032081101d9191f1300b084079140d0008440c030800c9082e070f000009a060500030951010b03000040d04180c00d12040d100e0059607101840017030300e60ba84d556003070000440d565103107600080900300040c40c0340207444005c00352100e00041c03e180f500300f03001a03c0007154603030381d0000d003038000368400e110b4480c181440e0a10141203107900d01882582403007000f054100c1284a041c0480320305844007920f0926540c00e1041220b052241e080c0482c00501030301d151a00c0c140540e0340700d103000d0006080b002120100c1b07001000d450050321a8550141070906101c00b0b8404500450190042d102c4045541c642c0b074120083d0020780c400a4100c0c0aa80b000c4210514488140c41911826202402555210b00024045002520018059912006080f404900342030700558000416 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 113770314 1250 113769064 113769067
    0x2304030210020a080417070f03051908091017090c031e012003060109091b110a050a03050d0b2b02031e0303010e0702060403020d0302130e0a050403081305061506 71
    0x36600d03000e12a8105e81d0041580d030315024036114408030309000700320151905200420505046840342540c85101310300380118a131400042c0018420800c00391029070303d00a2525010001140c801404403000240996004170000042485200041140c3c40001c10240051000c22030044282c0f03041c042441d071500070b6542e02c0c1e58410715840c0078400c40d1a881d460b90001503a90400c5000182042e0959000d821068580500c00c600314100f040d50485101e201d01e0201e104007844020b040c200085404000d101d4455061004101504900645984028000200045240541484042410b2031030041500140b41c401110703400d442465081790f1b50003e81100c0c0c0c03100001c0200c030396084040e07070052400d03030010004104140090840301d0f4054024400b400042c201503901035903900d8a1828802855000329180f40019040050017000f41031a2044034841d061070b4001c50b0051409490580009007500c002408412000c440d07141c0d038543c00002002544e492000c401c014002c0301c901c3c0c6520010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 113771564 1250 113770314 113770333
    0x9070315170c1516020105030703062d090e0a080f0f0c01141302060a11030c030d06030b090601120b06031203090c100e0d110a081c230403021002 64
    0x1030001c048442100340c0070082c044a05a1402c001510992203500c0c0028a810054040c894004612540f45168203080003078490311a08400e03030151074150090000800316548074a541100944483c406410f5150070401c5283c98517001d100b031781c19100e00204140c0c4034256810000706400010501c2c0100b41c24514100382405405849c41c0c1d2150424401583d107424203411070300c800005a47d08141030044524013418241c1c0450703454020901d0582c01d02001c90407402c02900c0c18021640c2c3c00e20003030b0540e0f41c2d506400045c000104041c1c041aa000c000080006818160000303c0c14165981040760881581c55030b0f4036070700784000c0209840c0d003600a07001064503540c0c07a80d02945c02000c0390740c090481c00d4412414025a043d034a541c41e01000111601e01c11192a0030f403288801d15002880400311882050100700c01a005503c068014803842c401c100d4283e4100d00000102582a030301c078600d03a45a25415a80d815000d4a651281c2c002004100b0043c40c1400e0b035001c0041050040c0c903c0d0f0305 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 113772814 1250 113771564 113771579
    0x50405190e01030f060b030102210601030912050c0616020c0607050102040302040f090b0a050c0313030c02090a1b020a05030a050c0c0a150306060c1109060a080d090f120209070315 79
    0x40c080e8401c0761241d40880c9403800300400790041c08000c54064000b1800d1170480f0401c811258404012b501c1d0000c1540b02007082c40e4442c1d0004100b00b030300860680b401c00803881000b00158061044049540201c030003040c0e0144509800d004109915070041101b80c0e410381c200010b95002c04000c9031300b50350820000005032528000c82060344080080082c407200c1a0501400d802002400c0d94080c0e0b1810041225000c0d01c94241e039000f21008082003104c0c80c00746002d41d00e000c00c0110103580401c90400b00400050a03401041e86000c074030515140303100890318141da461a031401c0081140c0c000340101c0c00c00900c540c001d804ca040c0c4400454481c822403001181303e158681d004180701c00030302028005145c0d00750081030000c1c02949400e03a48920f46489601c0c05040642d0a5441022a100450500d907034000c5803078060700140c003d80e00c0208441c00043c0c00c0111500c940d8409a220350400211210b8007400d0100d40354000c0d1403d042d0340e5603c031040f4001c01d04a03400385080d40210700d0102d243c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 113774064 1250 113772814 113772839
    0x6010908070806010609171f02070b01150f0908030403030c0822030203060c0901091404020906190206130213050c0c010c2109050703030323150111010c05040519 71
    0x8018180c0a48019411710400500840f01c2da0408540c1d0910344101d81c203600e000260791080702c03d421302d10702201122482004040c0c03044034006842068004008148110b421050b04082007098549207070403409801c0544580c255882100002d80042c40304001203809400310031010742c8500c004a25250700c0784280081002da030f12620403894460101841141000c07c070721900b00000030302d0242000d41020000b000841c5c2070081c5c1d420203500c6445100340d501d507a0160340b40c00000900d02920340b1100e840310385840c140c0320151001880b030740c008a00f0308100c10742e0301700c0000d4001c4c01601070341014840c59806008090004000c07804200b01100404d5030a20400c41307182d40c40da82d19210540b152264076010000d0700203001d00c0a02e00f00110002070f000103815400c0b00d038035040c08652040909000901421048110f01c40300fa070360f00412031800651070404002d44800d89804444a603a0030b012400c032104101c40c00081201040180500d103804a0f822040000c02b120303085c680340d25071030f046011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 113775314 1250 113774064 113774069
    0x406150e030114062101180311060f04030c2307080102040f050a0506091507020411040801140c04060c170c010501053c0103020c010507050405010e03030306180601090807 75
    0x140d60300c1600d200e24942800b94800c44050008a2690781c02c0c4000001d41c600800c45504d5121040503001c5141c4520030340040b0000f100c031810b120b481c4002414064540e6954244d910300b035018074000038064041040e459400740d1f8040d07480703160441c1113503126400460104030a02c035110910701a000351042c00c00c050300c09007240000158072540b42c42c1c0c415021700d45030382280d4801e00c95407205005070349880042e580309003c1183c40d50810381d5042100c0c00e0070b01c2080700203908582000c42d03550001036000300401c21100303108002c00582c0410302001c0b11606e41a501c6c4aa000301c2048108201480b96070343c0402c20f400f41c4001c1000d51040402d2849a501c40305440113165100c000400951800c0003400000c4007640070200071071401d215070208a06c884c1c074090712201c00c9400e4007105030f9219506a6092440c3c13007008000381e0802003006001d83d001031090a00296200d40100b134141004420f41e4000c1c9005081c60025400110f00d1001b02c40f030042841d410441c907240006245241041101c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 113776564 1250 113775314 113775317
    0x1030309140f0d0627080a23030406020901080703020a21021b06010501080601020d02060a0203072109050712200409020306070f0915020c0d03091d060f04060605040311040615 77
    0x211080101d0302007120701d100c071105c1e180c0320103030802100203d04410300b00c1e0b03000007103480e0030360b61000e485c100740030203184001e000c041c0401c011040000b0041b81c1e50060030f00a500341c0305c107002c03580e072144110b06912400d412080010000800f0000104078107840c054011034020000d81480c01e00b1986e41c00d62020b2041c00865980084010031035560040040c42d0008001e201502c0981c400160195940d003003c0e114000841d40080010310711889052564204002149910b1000400400760b502610071100e09482900807810001541c6008400701e500e19035000c018464098042043c0940c59510014031540094468184000690b414130030140304480c551920540d00303140d410024034415a40c0c0200b80d070f0070040c0044608964001504c03280001c42241c0782a040202881d040b25100c80903803001c08922a202c82d503d18072003880c1c8072184280c50641d50701030700d0542c41040000f558858400d102c04a1000c00c0b082c0085a815010510115405040440c0d0b8a640340d0303031706002008024401c0d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 113777814 1250 113776564 113776571
    0x5030d03020d05010605030f1305070f170c030303060a0b18090c0307080105041e15050603090124030f0305160215280e060705011d0d110601030309140f0d06 69
    0x42da8400341e20400380900301c240750590a41c60f0007440d551a0070005020000610b20101e90141000410040130001c4c24051100c0424a40e442e0510390103215680d6080203107014610001c10b1504000017078034840c07603008010124251820200c800b940d8002008920168491400c17070409441d401d9070700d405501c07007a6090b6500d10b040c400081070917106810451080f41003099128a14076186120355800400020000e0040254080003010550640c0070340c1d006440070041003a4800190310101c800d09490440d40d04c682d00000245400900d2404000d18110900c0b2408005c03070b00c60406081e40032428042c444800584c2d40024030034529081225280c180c0c005481140d6240d11200c4000722115482e40140010a942018003581e881d0480140100c43c04510f0006100c07013508541d01d2100592008034044440303c69654460403030b0102080403d0401e0850001000000b60580c100c03901a07940e42c0c1c1080c101f40b0124201103c512500e50f102d1159181c1c40301507a19200c510490622800000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 113779064 1250 113777814 113777827
    0x60c0c040216030212040308090402030a0e06040510060f05060301170709060803180108130b07020a021309031b1e140d18050a030c090914120a0201060e091c02030405030d0302 77
    0x3480d20384d001100c03c172108418002000059884c100350742101c94102c6000d0303281d9a40b0750b14803008100c030300191070141c4200818030040c45404600c07403042c21643e007420b004045d25080400705802a130b01c02d181c0c2145040004002004814110544000e401425101403d40d905914001c0d41d0700c07a00810000e800010356115a011102c04540000c0c60a0130708190602e004000c0c100d01d45030342c28010700140507210004407464424055100005c1d402808180c0345841000100010006008201e000c5032000b181c8070307500d2441802d240d620940c00040008615410000302648140b00300049440c80708848120102e20004d21030f04104c054141d0780e0303540301c10007054103940a001c0c0d40d2207507020b0908404e05001007001406040145c81c0b005402103101360349860f02c100c0c050034006004a650003264142c10700400c200e40103240713807240c9900034071816450b64003800b00c21071300f03403802c0550307a000078211400300100e1138060f4030007202c07401600d0034281d0310404a8180000d44041200095001034007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 113780314 1250 113779064 113779067
    0x150315060f060f17150a0e0406050601030b03031b0a08040303030f200906031008010c020f0c01020601050d0f0303110f0915040e01061103131409160e060c0c04021603 73
    0x444004003000e150403c0c80411400e00a000704009240c1c60103004000e1000804a43c1c07030351640603009070003401201402da511015094100c400380d030111412410a400704400b50700c00d02074082c4815000340650315106500701c11110b540e00884480000d40200b03054000496001b4000e000110702940307000c21004501c41c2c20008807411130390000c0d520300e40051815510400301054072401d4905898aa940c0d4036520110308102c1142d50000800b5030a01d4501da40720341e1b0101d5135440c4d1003017607400c881e21400424016038a641c000d01820b0381080c00d00a19102080c10f241c9025603d9009090000300204483c50000c00c5a11000b6402410940040c008403142043c65000554501402240e81404e0404d40b000a02d414180b140c1420450450300710071040c01c05200308c0d411143c1c10703004a060241d6400600c0c25001c50030b01c6051050100800080304142c911815040c9100b0f1580c071141040f01010402c142908243c6007281c2900c1081d040c1c005a44841c8000c0440074801e00150000c0b9106290 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 113781564 1250 113780314 113780339
    0x70504030b0f0c1c0e07120203060f1308090d0f1407061e0e01050d052a09150d020c0a0b0907080d0c060b010c02040c0801170705010e0415031506 64
    0x40160180d200904000d5690f003d4800d07202c030110100010085104080002800b80050004180660144e94000540d040c40c82039440019482034041d58203503511808944090300044400c074201c2410020110f0001d14110000c3c00c00d8080184810361100310354036900b00081005004841b5101c1c1c0615004c010340c2e040004400a044915001400c1c03a40c0740c400e220010408030780c0c24107200c1985a8282e4580c0070340245c54480ca40707a2020801450040e030760400311602d42900c40040240203417034158030140e034422154040009024140c130700744032000c4205c05038070507659002040d81c24400442c004400384881c51045004111140d102d00700a59090300700b850503400022154040408248001e81207030348051029003100d00025003002c00d800680d100301441c840250302c2860203104c01001c54000380001c1c10780b0b10f01103000c46c0303403002920b049a550f0080d010b12404070f080303581c4500d4035152540211030342c01c2140d02c0340d242c0f0703940e240e0310b0310300800210029907083e5485000c18009200940d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 113782814 1250 113781564 113781571
    0xf0a180c0306080a0503040312090305060c18060412110111030706060305100204060807211407020d0302180d080c01020c0d08060f09040305071109010902040303030506030c06040e09070b03070504030b 88
    0x2020b840c031310707403036a842039500c0c4a540710061074a40c89240648000c1d006566140007560841c00fa20b01a103007031182840c581c0d1141820380c00440c03803102c2c4801c4a051070f1060b1015070300c0120707040c079607441c10381c4800c3d2020b015a40503d0400107807070a19880c1e180148050840d80d0b106140100e203960a501d401030601c041300f10412400e520510007040794076403040f0419040707019420146164250401d0b09800e0309102c0c3c40c418012810800c0d030314182e001195220744200c00f507500350b030703068120050304a043e441883d0071032076501c4181c01040a603140c9402603014242c410b03100c1c07514142000013481c1c01d81e00301141c3e11065800048040c2c840c81e400c8103016500410131035803008401005000111595006000034040060101300b0608100d0017286001112500511201c220342e9540603d0010b503102d408210000780c140408a11103040014004020750b10040409050605089500ba403134080180280160f00c1030729000a4101c20860041d40100f1440e61869a61410350070480c00288014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 113784064 1250 113782814 113782829
    0x1107020a050f090105010804030c0f03080103050c0103110307050a05120c04050117070804030309110a030c090f0e03090613030804121e0f060509010b0603091507080103050a020f0a180c0306 83
    0x1905042c20aa440148081c1555000d080c5054161201c4c1401c0399403001c0100700a2082d40042041c1040c19003004d1414100d178070600403524540300c3d0b0703801102640c80f45519621000428004070715100c0c020406001e1031050b0303103440783c2003280f900c03c450a03840060729400751030701c00002d052056580c8441002c41a03852801c84001a0078403c200400540000348041e00305030707444812400300320070703c4621005e003000201403483c20340d228200204040d81c18810705040a00e05410382500c007241c1d0141180100082000e1030404501d04180015903010000c0119450084203000c000218000c0140c0b016011111030341004031003510340301e1071160110321141020f101104074100010101100d05110590000010581e511290b40d418054560314440300c3d8001404000c000c9080000100550344400000060030b071901c5400c01550305110030301024200da0408104107015051008542d40d8200010b46051000c035610a404c5e07402250844500000580750066640701d154940070300b00190194 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 113785314 1250 113784064 113784079
    0xa0c0801170316110d03090603050901090512030703060b0409020c010b18340e09060103090201090909080412030f020607030c210b060a0909051501080f0603010b041107020a05 77
    0x590580c0c1c0d49001d80d0f00c2410340e84602d1010b0008024080c0d101c40c1005030068000c801e2001103180292444025018010000346041c00181c90300e80c0500403111020b40190140c02c51501c55075100300700b40c0c8014154003e058441c0303000a40c4030b003c24028001800203120068444081e50241802c4d960015121882400481d207500388184030520800d0f0010030807152660324000c1644680c100d81d150908481c440014000b203540095001001340f500349508480c21125a074800d4010b60442e203800754082d00268540d130081c44540d249500c0f80718420f00034000e440c00d1030355a800d0010302008440003100014505506980c0d0b080c1c0400801c0e40000c0281001d100130300c10350f400141a0845a00702c50014810010502c4000c21030b0740c01410045009048541d84011012001d000b42d81d0078407540011925000c00101003400f6204100c0880105a440ca00c003a10b0300c900226084602521840d4503541e50740342070b5507a50b140e2085d10800000c0072511600c80c00d55004020160901c3e610990140742e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 113786564 1250 113785314 113785349
    0x5030a021b01030c090b0702040b03030a210203010b0403030c050a0b04030e03100606021c090f090209030f0102070b060603180a1b0b0c25030b0901050f150d110114030a0c0801 77
    0x80080b172507000e89503c102c10320b0721141e2600006010349501602580c06020000d040d0000c158022038052058100c58a02c2420481e084441002c80c4801d202d41242c2c010144024400a8807542c03020000d01d00030130440c0c21442c0c0300d40f16080805c505460403004940b038401352009a0034240408410a0091441000400e10b07180b0702030340b214603500380c01101318080c844650b0140d0060001d0400350000301440c28229495075180340c003c2d40030428280c0f1074400c840c0702c802c1c0c2a1050085a480c0c035404148042c258039a0400e006881d0400740101e0440c62680142c0140c0711010070591380c0b4503008411b003001110000e401c462841e0995001011503280801039019040d8001a07210107400b100c00c100c00d1260010340002c1c054003135640006201c0c1030480240101440150451400341c080c020307590f0010346640c07000b906250041c4400310b8011140070740d55008125041d0710301e11404410304261a410344c6d42403420030154011940032541e950740c0c1004800180d030120030035015124003100d2100641 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 113787814 1250 113786564 113786567
    0x40509060609040803180105010f030606050307121106071401090605070906020a02090403050903070801091505070e0f0f04090b040506150d081e04030302061519060302090d05030a021b01030c 84
    0x242c003c2004c0c0084500001203a00760383c000c0380074104200366000808c0603584a40c00c4036401c1040d48415a010750070a01d0100d00d500e4042221011200403003110207210203140d8032200740c0290710f00c1d00f5610241c244500004100111840c0010b90341c41c900008031103503a072901d101180c070003070000d10400c0781554051200715000075a9008480e0101c038031500607691131a00300c50f40c0c400c2d101515050b02400b503002030b00c1c0d00150030800c0742511591004520710401c4843e0343c1200d4044130340030009440da103148111420a40410349a515001d49098484444030002c076080c1c5180000483d0850031000402090010501c4102d40098070403500044214030000042d8040d440e400c40584451400110700e510344007062a02c9807500340400d80551901c0e505d0030043e46881049403641c41114200d0601c400c24645a04010b224400200c14101c407542400740c220001d4010103003ca812005000c42440440c60800140440c1d00147c0e00510400444107110080311080074417280c149030602c0329082446 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 113789064 1250 113787814 113787829
    0x2031c090605040510290d0206040f12030807051305040b03072c010902030606030711070807091e050603031b1513151103070c050c0d03090501030c050c0c101107060503060405090606 80
    0xc00d0102d41c08407c601040c000103909100d03079401805103100454000441d00e17014000c0310030142c007a0302d42901d5556000300070783c1d4078400c0b0700400c035050340700c1901484149066803109a00000203400c850006d84c45003400001f066510020400441c165a414404142c14884003405841103200960031820004040745060101619410601071710030b100302e46100c0104034001c0105802411a0303200743d910b0001e0701c01444c0c0c1030040c0300d20b01140359003c0350400c0c00f40600d600a420103401145400c4003241080d004180070340402000c0e0184091101140400410103801010301c01c0d000040c84c001464814440818070422600282c10140828141c03c24042038a0340502c41e802e2541040c03d40d45442404c0c01d030f80001c101e612588102030f8105040d4401c10440945800b03072070030400b443d51170f4415600b0340210400394901ea40081070004503401d10000084881d022401c1c01906a19901903060605060760849000220084200074051030540503094110040d0b401030002424050003040e042c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 113790314 1250 113789064 113789141
    0xd05060408091207060c0204060909020f040c020c0303070c090e0d211b20030408120a050906041e0b03040203030a0f020c0a06170604050702031c090605040510 70
    0x41c0001140c0e800c0780e40c039100203425480c101c0d50700f44d40c80103440303020182400d1000441139009910b4030001050441f41807090403155034008000c2e4218440c01c50412020706403541c0300c1c0c1d08501500c1c411003115141033003d0450b040c03195126031100d50030300f551034003118440b03441030f000c95006481030b8264903000030312100785178041c40c0c04903407c00c0a540000090901c00e003611001e11000034600d0030b03084d440410f0b01d512444a000c054006107422120741d60787e0041d80070b40929074000900e040c0420551500400b60000181880e5040070b40200000f269a0840c0d0b00200c55801d1403040d0901000d084020400507040442e01d40d030550a064010035a01d014a0b61314009104075824035504050003000030500c0d045000b80030030000e5844d4000180f00701c00c50402c03458041d00314800b00e4280d16060090780d214400c154000d6040841c5800c01482603279180480811460fa80c07590b40c800b0809601540d449503001d10010308441c00c100074030b982102c140103610010500705013114503d00114400c0c41c0762 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 113791564 1250 113790314 113790323
    0x804050634030605090406150608160507050c0a0b07110301060b1804060f12170a0c1205070510021b070308040b0d0f02070302011b020d0c08031e240d050604 69
    0x1e20401c034005078000c0c401504500e0b400f056140800082020b5a04540350200251081c0c0d8034a0742d5418090701c10f0401542c8215059030141090540c1d14841c0e40500f02150080b03080302c510a1070800801c2e408040c6820600d00e1040c001004018041c0b140d24241082c0c101790000c07c855458100340c100035000b285156a104041c046c40a03182c1d40d42c5810900151421807400201d150741e401070040d5800381c0c03200c101c6102003000054020144414255540d1081c1780c2c58107844d8142556070945140000e40842e424400c0621100e808240100008142d400d004500140d456070500c403c144aa000b03020f0380c0005500110090002800c4c01c42620101c400402c1c82c65200e1170f10300c031140701134400c03090b841d64890700c0403900704189030b17054100d2006080602c1030300781c1c0204808412030b101d089034581100440c00c2c0d84032083c00112040f0003980d11100601d4800b01660b050440007ca83d14107036481000d803091640d41003a81e8458182c040381858048460301e0026205e0341e0703841e4489034010400b50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 113792814 1250 113791564 113791651
    0xb0703020703210c030b0307050a0b0f070501050a0203041119030303050907030f05070302041103150d1727042f040b0c06100e0603060a0b0a08010c08040506 69
    0x5007054003c120805882001d0342d0490000b20307140c0d803500024030f407518072040000e0034107005003601c2c00c000c5440c4003910b8003e0080000c0c1d030300305901c4101c5540300f01e6040003608810421000496000c0c840c5900400200c240580d403410a410110b094401061a5030300c0fa02c0c15034102c0c5081c0e668076040780c7c120f942c141408038030b5690703821a02e814140140c2c0054540c18202911600b0040d000c6000004d480c802c0b80c0421403121a0381e1008001e000803100c08048210b08401c103201884c00620b070300002031103400c01d10344208544540701d1050b0044a2070541c10520800c821200002c07841100803074040607101040385c881e2200c20200d244d255220320002460442e0318000c1c02500703c40403503024040070320100d80d55203030440b6031580e41d401c2100c4c02c00342c1c4142c2e4000485d010043d026514010400100184103988a004a2100811440118540c01482d442d400250440e0070b0143e20f003148003d44502c0b80900d0103080180c00c0c000010440140d13084080328810321920b02c80814001000013414a5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 113794064 1250 113792814 113792827
    0x7030809010623090a0e03070812010806060a0b0306040b0d1104200a080603030912030309010f02090906130f0f0c110d020a0807030306180605010f020c0307060c060b060c03030619030b070302 84
    0x1540101b000c1341080c0103030700002070710b8001d0040d840000c09410500e1174034030045a90b5140070a84504040d0381d406c0c1e11001d80c8400b003041c911140003642e00079800402c00650446031100040440c900f903403046400080600e90007009117171911458050950500305040308020401042c2e41c00d2045004000a112016010444a8408105540000d08041e1152501c0080c20304059503e40048a20760300c15070034180c001860f0240c600036250320480280100714980c03540c03410000c0600e0144406c00c0c00e00d5440a58200ca800e16000d1720141e040b0010000405d1000480c00900042071a00040040d500040b2440449940040c10094058202014503100c568515088010f0b103001c3e402182e081c2011f440040d00804158011422200d00742c9035884d40d11038140050361100303049041c031549900320080c100f0046010b0f0650608881c451880051080e00d0180099203030f07040700481380219030000c42081a9820003501c09002c4084010700002c4d01e901e0f5030b884078a1030400038886010150041180e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 113795314 1250 113794064 113794081
    0x110a0f0f080f01050618090403170c040303020a0809030f0a031d0a03050705010320030a0c110607081803040f030501061d0f13032015070f020721080703080901062309 73
    0x103091b9840d000034010007181c00c0904000305102e001e589840c0c6050300075000714110403482421070341100c3d45034010302040840b54840402c0c41e003096517a02c2e014041c48040c02a410024880084014403d2310780c803440301c180064035410044004001c1d400303689039017424408180001044001c0340c00920700443c41d500c24401001400b140b201281c450300c1c60210038440380c10000c1d04290044400c5545400880070010a100d65449003650004c01040c1c0840200e031151006180e540d00d100c140c50200c9103043d5941403850400c054a500c103480c07a0b59500300030301801070404840851100b02c1c000a43c400c0c00c0c80c00461075079840c00742001d054031002108220406000e84080c070017080210078130714000c1075401040c58940351aa1134006c0300032000400240c00d40c3c018840510140500c0d0300030400c00d424024049207654a04002051420460b0940000240a030b0010f04503103200eaa100040d42c10451410340c20354607241c10581c004003950300080c00500915407032001e00801210000d0041d10380080703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 113796564 1250 113795314 113795347
    0x51207030b0604081f0c0c0609170f1c1514040902040f020a0f03020c07051c0506070c030201110403020d02040902040905010203070c0227070c06110a0f0f080f010506 73
    0x10100c1c2c104902090002d00c80c100421203004080c0a241c139001c084600c210300070115000a094100469200c00b004004211968005080d0912440d40c6040b006042c03244a1003d07089640c41781c0351051700180134801c030740c00c00c0c030102c012100070442400030990915820784590502d0007908100003004002181c155a9a003080103e2074018100b00400e2903804014006503004001c1003002c10864842e401700d07140309100325840960080060b0080c94100340400c40080d507801c0101c042d2012807884600070901c10301c130103070041005840f840003005035440e0290079680380320034010107441c082c0f0041016032140302c5459003155045034002400d22041c8006001040c0445002d400713984044108803200d500080041003a0740212061022000400c9101c0307604032055090b0b204250810700811034481c0070b040d000000510400b0041030071040845d0b004600d404c0b582e11500007500c44942174400075044500d070b80e203504c00c62400c151a031070104c00030400d07030720180305180c00760000040d400e00300840e0b000b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 113797814 1250 113796564 113796581
    0x304030c0818100e0405100b190216080105191407270e0109061202030304090506010c1b06090806150f0112140a15060e0402091807020a05010e0c0105120703 69
    0x3400e2a001c1511010b00804200c40881c4c0d450066240101040054100c41c0c4010100c4595010042c50440f048904d58030000d8081c41520940c424440413090101e84000042d01602c20840001800e02c2c06038141556082d0f41c03902c3c800740900d0590440c03141109111019800301542c03e01c2043c000027841c1e181040950400c0141c05a48119000715070340168258130390490f183c004007405116150340900450403003d010085d03242c0c0c4104000c1041d074405820440d4056014140b068000b459510f078080848014a4030720300e41c103001d08003030103130307a400107208005889040000c201d28580f04d2206d1445110310885c1c1e81c45140f05845800740360b80704071201078098a84160600940701240c420020b080c005951507034019040a8014900d150708009030405c42d05150340b01d4a08500c18408d002c0254130841d10300b5080710b0000f03c510300408592000c1c034050165503000b40303000880d0f0b040103400c4810350501c2d5512500007001030707000d6a034840261a444d10900c0d03100b42035512111000d074010319555 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 113799064 1250 113797814 113797819
    0x4030b0a06060305280513020a0605040812030108150604020d020d0207051e19060f0504050a0209010e150118090c020f010c020102130b0a020a05120a0e060304030c0818 74
    0x104000303030050349410610071124551402d01180c1c40b822012800b624080c0105550288001c3e0841c103a440c00e07803c6160020071201f14401c4406441e0041110700c0c0d0940c101c1d6000c03400000d020070032981c0401403102e48890b41c2840d03038199410290380ca40c488120f80e411510042c961004140c3e20354840c1d04407103140075011000c542d90b0700754181d000c01a402c201c400f51140d01585805071a2410304601c0d600441007034002070300200101100e0110b81b031002d0b41040d5011a0f9070500d154143c003503071007500d004600410003040c010907039204000035000140c010010b00c0c08200240b00d880300f1000441c8980d01401d080407190250050014201d0001542c4040032481c00c1c52243ca10464000c21b8060581803810001d02c001e4810040a03403d038890000b4402f9101314009040000b928400050300c04c3d0012441907407140c11041c0c88070792a141a07042d103007508600006440292a4000c0d0030082c00352001e980160852406403805410801e007400c02038880a40000c401c901c40d5040c502204551800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 113800314 1250 113799064 113799083
    0xa0909060e1b010905120c130f1103041e0503031803070507030803010f080106150509031f1a01090308030a0e12130612020c07140d0209011e1502100507050403 70
    0x8405241c459640841580c046880d040c004500c50410a0026403400c0c1d80324007c0007850001400c2c869000b8000031654a0581d54000040d07080159000340404559046180ca032a420241095501080982044401e550081e00114002a00401903981c0708007044600b50081d07111040d040c1c210701c0307500c1d070041081c05040804000c00403484080e5042c2c1e5000c00c1282c05007615103c04a00700d032a140074000380e41600ac00c2010500707210304001c18011300040c05850039940044e8408031122070889800c40300b07980b540400d4030350001c01c000c001c9800d030007444d1000c511455521040300911010704401c14041d16046078031056802080200f007480f400e50728850f982d544514034031285e03440c1c03405100c002a040c440402c010610b28001e484840540d000031300403003460706451244842c4100000d9070421050500b010142e0780e6255168001d05508800c000034600d001c400000d0124160821031203459030b183c9802c2c00e10380c00160040003403010b260004a80e124080161281c1c0115480204035a88 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 113801564 1250 113800314 113800333
    0x1151706120a0503030403140301080703020f04110a0903050d0f0c1502040b1209100603021c03030e0a050a050607050a051207120e1608030a0c0308060f1203030f0601030b0a0909060e 80
    0x1030000c001c5d84514000d42d01d100300090f0031300c0c40c111030b413000703200d404c80c0780d8011201400035140482d28405c05e000d008100080c40e880040c13092200c2c0e00071461344800b04e219000d081091002c24030881d0410102445d0102450403a10000340c0740a4060002070301052007402e40b80903401d42581150040d1540012558590b1001c80070540e10b010b049a0747c102c540a0540c15031140200c0740984c40c140e0350700909944031740d421005903498148520605800b0940c40b030301c0c01540320f030003400405d0809000c1c0c80a00400c08c0b143c28418034002c2d0103055071040200070080e401c81c02c2d03444401ea03180070940c0c40c1194060f840340c2000f107445141c03403207400012a1900030400752a0b100041c9008910580300440000e1076503806080d0b4490140028081c0071030980d000040000348651a01a4009002000c1c115800e00d94000720701000b6070300141c410250301c0041808105200d0081483d0302010918040c000304064201042d41000741d80f0511460030b844155080c100203194000859840c81101280d50b14007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 113802814 1250 113801564 113801573
    0xe070503060c0a03230109020306011e020c01091415070606080d050304110f0319020406120c0303020f0313181e060614032413060e07030501151706120a 67
    0x6010034400700109140c004801c002c1c0d58036010742c0001c440b2051503440540e07e0081484042c0d80010602810032010104540f210450308812000422072a4000c043d01060301001400010310750300100400d60525000d600c1c6aa05e2440b42c6000315004190755441e404c081c07901030060403140c0c11102240c003524099513502503200f405103106da400f61204404142c200d1003804010403000c400c036078040c0c10140d0703040301000d400b52030303c48a644042c00c0040e05940c1d03440500d40102e00d8010441e41c621581c4020814958108100d00701c0c0d5109a029615040c4042201c00e1900b0301c0d032045440038401c140102c100c0041907800b107140c03082c00040304403802c0030305103107107004061501904010586078681d000084017032400340c91003001142400c800c50100041c40c0c00d9074030b1100c480140c0c088442015082010400e00441c0300410806581c4441c80c100b0900180076030300140c108040300b051101d0300d0100715501040c41c000d078052000c0d06190a403140c0010444250704080d02c080d032845041c41c44020030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 113804064 1250 113802814 113802817
    0x2120a0f030c0509010804061a031c23030a09150509070303020106060207030f02060c0a08070804030618050616090f0f14010305010506070308060324040b0601020106080304090e070503060c 83
    0x342580c040203801c210031800c0c1c41030300a604820b07002811500000300000e0b80350303016800c03042005281444031101072000925001d14a4100c120000c00c80e100b01c0c40154002c0d17074001c00e00c1d0008144142c0261071051444179400001c0000150a072507078010400d010300d02c000c03215031035a5010240b085140c9803806030b40c0d80320b1070b10040f0300540c0703040c0001407018808505401500e605c000d020065540f030303408009042c1c00181c3d4060281c00b07869403810005d446080203000d046e105100150f00c071450b50800004031002d04421031b00c480141d001040025101052103940110119040c010f505d8424034111240d2030503400a001d20030a100c00803402c54a1000468121280c51054100b194600c20045041d41c07800c3c82000e4000701c0600c4020300190244c041c203a4801c101030210303074241c02900d103c0c204041305503001d03075001c20000040c8403e0264030328020790f002e0000e000900200746800c8100d55240700344d1090816295850004a11942050040350000c2100908468003401d02e01c0d207681e0b06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 113805314 1250 113804064 113804087
    0xb01051b060915090709110405040603030c0b0c0405060d090606180204080115030c0b03090a06050c0c0f0604020f1e030706080906010f081f02121005041107020306011502120a 77
    0x901c1841100f102482007011103512038007062001d40000d81c07810300da4030b0103040c800f0400d000c6000203000220302d07030f1541d01c9008010360080c2d440c40e08038413944c24a00c0c1551400307003c03030041020821041c41152119011100c0c5007521a000050310012801d01c10020408c40e0801ca04c07280c1c0072201c2100500c11a005881039840700700081000141400d030104000a95120007081e460b080f02080010a408102071a403000c00e20341501c030001555a030740c0045910440c3d9142c00481e0218150b004d8004c2008254501e003000c074000e01d110b0805400264079000400900c500c201c00c10041e2070b080d940700c4410a00c0030203010701203500042d100d480c064070081d421110310f0b12610403200002204803050a50740200e403903110141491258100000c15090191b50041c11242e808008180c081c0050b404c40c0c900c030740c80c0300525402003420502000305030780860350340d0741101c0400d0098501580e00411070398110780101903e1006110206c01c140e00707045040800d281c1881c0003041034190683c1042d03c1c000b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 113806564 1250 113805314 113805331
    0x4060c03061415070510020c01020406030f02030f01090b030f03120702010c14031f0b1315110705090717070305060a0605030f07030c050d0e01060f05040912030b01051b06 75
    0x400e40715014002100c00345811558041407240c010403d18400b080104292401101603c0022080d100d07041c042c0e80c82050305009a070b60003c0c00f0016958144110040d9900422040d445c5080c6845c2c0340c0c20440041c041c03890344a1703441c00d403000199010080a0011401141035039110b5075900c0020fa0f6646003203a4840165007070500d019220b901c40e1080320000141c00c0551403d503250244400c000d101c070709809803030761907200f140841c050b10901c001c2c10b0442040701c06610454200300c100d0707101c038486440e01420311450000a50030b0200c045040c1007945ca041d100c141e40b80e50740690460380031003140446d4031120b8420301030080302c5500d43c005034816042565454034507a0344a00032210303031104850715070880c0124004250303914401d80001c1c1d42001c0910f006424030b4000d21043c4101d032000710390903015a6460004001e40460302c4400070061404940c1001800556154900303d0f05541116108260b91071144009030b80c000c40564041d04030703801100620303d40401b4207a9a40800391803402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 113807814 1250 113806564 113806571
    0x302040f060909110705030a0f09050a08030c070504060503030f030606040b030103050a0614070e0904030905041a030609010c0c020108070302070b160806030105040c1502030d050903070c060c020102030307120e0604060c03 97
    0x204a1a0304e0700840303c00c17a81c4040150310b0580840b0003103498010301e4414004000040c100000d0654520144001030312510015659504158440f1440d01e0a02e5010601842c10a8410025076070003109407420178a5501d28665240c0d00c000000710a48031b50780011401031404000032040c402c00003402020544210f0f810000c0302c40c000590504040100d0304440003500301003034010141060a02d280d046031080c100010426115000503040d2200703e0340400800041403c0410240f5041007800c1d04849014002c00251807000c4009101c2c607c2034030041e06204105000c035807a144254100c8034180d41100c5828402e06250301940043c1110600c0c40e4000340c40000400c006150600c107250003594400c0c41c0812140c500300e0b5000d0205240000ea030154042400500b2000720380f802031912800d0240051541c403159840d22a5400703c46801c2801001035440c0c5810043c0d030000200c94008002e420840742122460305144041c0c01b41080110240c0155404e000803c0035981004c441c01c009502e050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 113809064 1250 113807814 113807831
    0x10303030c0216050f0f01120e0d020106170706050901051b0109030f0e0901030209092803090f03030203180409050f011e0b0303071104180302070302090a02030105010c120302040f060909 82
    0x1a4001e50203010313143e40000580040e0801d46041c2410003896141230415003154840140301c0070441c2d500110400c00354000d8400c0701402075080c41075102801314450748903402d00400f807149a0300c40d0035000f0035060040014903100d4130780c021381c142d5007050203150740324401d69521392981e40a41031402048020451104250003001e015040d0740700075800203400640b0681c07030b40d000c220900e80d01505034200d40c001c0e41c158403a00314000300c2103154800c60b4900050448040d01c1c00070002c0c41c050f8468208401e60907003d1000039404800c5502e034590961078440310566181c0002c0080800c400002c00e58440d018a00c103c181064000d99034070880c0c04d000401080e00141d4042c05d41d40301005096054100f0042e0000103002c1455181d00981c0c06400055580c41d1042c403441c2d81104882c003900540c4c8240b01c1041103150007180564001201c80b000d5003554075210010701328280c11000105600000780840310310381e110358180c0300100380091120052640e1000c02401c100707014010003c402e03050403041c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 113810314 1250 113809064 113809093
    0xe06090a1503140703090f0b0c160809031207150504020a0f06020d0908010c0903080f090d0b01090b062104021206070c2a0b07051218031c0905060a0512010303030c02 73
    0x1405206c43d0031a0310004044c5c510380d11307034036508001030840c1d070060320034020940d961000d01c00002c0e10502c07a8134030942d00c0c066801010700c1c04203425403241c00c03020700b001007500041240c850304061400108010a03251078a2000a140c03003020b80103880344605035100040e4442e80000c5400c0e080390143c07a03040d9119100c1441f103080c2c1740c052004001103080550300b0030000368107400520303c600011802c1800c0c0008a00010028501c500b13081d149040400300500c240b003150301c03c890b070812003201c45500d0448603004524000d060040c81c01200c01141c40050295100c1d40800f041401140701074800038945002d01401d40403c0582c250703040d540c500494591055282b90700c442c8009406034442c3c5003460601c4d03c00140d8420041182d0754010309001d41c0c201900f20010f4490132400040024002c400c00081c107142074407290844200e0031000284500d0150407003080002c1e102c00351003203a80d915136280183c80510442c40008001e02c54034000205041d4181e108464818056003510711041c60b1140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 113811564 1250 113810314 113810321
    0x40302040b100815040b04090302030c060106180501080402010c0605040b101707150c0507030c05121605090c09180103050708070b0d0b120109060506040e010c0e06090a1503140703 79
    0x41c00c0012440b18070104e280303c580b90030801c9245800400102e0100826804542694102c071000c601503480801c40380042001403100710b01500003403410703031070303420341c84541c0090421140703e110305104400021801f0359219201c04200c0361380012007444281402d00d045135a10078116900101c0100034040071071605c000d01e06802c8560181001442c1040c03c00d0140300302d83c603500b01e03070781c06010781d14407107000050f02405050300440c0183d40403d2200c2c500b105000040010714000b080704d0700800a200407441d0348884c003500307842060b140c05105a4544460540e144505078085501c0503101d20354100040142c041e0300e050348d100d601071f101490341d1901c04c00d68a034050300403040c1001c2e09000650102d086da90001c1e081c15001084214400b80c00c0c98200c1c2182e020a400b41d5406440344200206400e2034000c00c005440340000070082c24004110041049502911a0744901c9001440c02078641d19205018060240b880c5142c46c6c101222001138000d11134040d002a2031010740c400106407500a10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 113812814 1250 113811564 113811589
    0xa12020102060115020c131a0f0915040e010608030301140409050a2a081c05091011030d05010b13090603080a080703060f0801090302060609011d0a020c0d05040302040b 74
    0x200140056400e128040004c10701c4c42c0000800c5101d40400700b43c286c1c0d81d1441520580140c2d07070000610701025218148400c1c11020079502902030303074a2410854071030840d00740d40642c1003034014048106ca140006c0181011154000c801d6007450000710380603001100850496044d080d600403040c00c003200344000d03540b0300c04000e4010f400c046000300101c1c2229140a050102c0000c1c07030500c41d550031603001c01909854000450541c050200080801c0c001e8030b552180014605080d42441030b1a800503901801910303818040080f8200e2981c042a400c1040d154148840c540c00c0c420341d0b85904a5007099040008000c0c80c03010b00440c005401354140c42840d09494220030403528114070364000307441900c400f404c40001c02d9561400090310b51040e4208030003900b032007c00412100b03641c0c10004d182000150040348500350080041080d0382d4600d040b085080d100c0044201981d8a5107100c4000b80101031451956004944130f041010382d1107002801680c2c800c480c100405440c2c5014418483d1090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 113814064 1250 113812814 113812817
    0x406080f01030c051c0c1d0609010311040b010302120f040b010902041211030307021203041806050d141c1206060c03021513051e0706080705220e0f060a120201 70
    0x101e014040307420041031100d0840401c5045c0461181d059950300c00e003070700c143e102442d4803119251a04c07070f00031002e08481d001101142e8001081d41543c5070b800d00509401c10017441607955854610059000f501034500b02d10034a10520160300e8034019091102c0c41c11581210900800000854103295034420340d41903032000010075894080c0381da07841490211954000e1361501c4140040d0005a540e00c50180a00c0488405140c880e454000881c01c140c44000421049900b481000e200507242c662802c500c058121100f4110714143e004050704040071000b90007400b80c0d070800760788078503074007c841c0f42e0403814035120030000c070355654400704e50801c02c3e0301c0c0050040c0c001c0002242d4020208001c10b4100c4070500c0c004250b0b858646c0c40c40d10f003003004580442c002014089a100480080c80181b0080604d8100b055641c98101e0f001445c5100700381c2034410f40c03d030809079441280c5a13182d0700c202428004611300d00c00c0c04c014102aa4a00c02100c0c00e9228074420580411000d40b101c50540c1c01a40c10b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 113815314 1250 113814064 113814083
    0x2181002060c07020d05030a02070e070509010e10110708010b030d0815010c290a060e010803120406020d020d09060608010b0f040207050a080703050c070e04020607082d0406080f0103 80
    0x902440c101d0b80e50003620700380d074040c0c20240d0038008600140001c2400c0940c0b17400400c41d40e8909080403114200c014040d109020b014400c242c1d050340c00490001c000b101c1282e410121030100791090b41e00a070340012180c4684221080030511440c154881c89030184220103c50b481100802c04480d807410803105413005070090583c540c40ca50152882c1c0390b440744038010700500710340101800c003040c20300c03124005a011402c4091242c01c3c0c06a1040320050030341044040c59660514803c00e81e02c0c420038040f15100200840010203000d090760554120454606e4103540d1101c41d0385007500508219001034070f6080c50300800045a030014880c4002204020f88604000c8010108100094100305426540d80c0540071000c00003400c03000051120714030985a0580310401c0f03105043c60040d1036040700c00f00c1000c103014880580d4644e41a0380e406a4005041c1c0e6072002c142001c104400d413103591180c00c00041c000e01d80214141f03540604151076050341c0310942035a541064581200080c8006444031030b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 113816564 1250 113815314 113815321
    0x30303040c05060a090b030a060e0105031504030c14070f03050f07060807110f01090813080d0806100e0a0602061b0304020a1205070b030f040209090a0320070f090218100206 76
    0x10214050482c0e50518140302401c20386e180c00c15801d562080740c0304080603039140014494040e2000107240549000e0f030042140907011210528044000360000e02032040c518049802c11500d0182e40016045440a40350655603a800c00d107641080ca00049915000e4884403056000d0001000401c94800e51b80341c4500752a800c0c015034447c418164070121a001e001d01044107800d007402580003052103840265a0340001c01d00d04420000d06401000c0560064850110040d50101045030480d008a40c042c28003140c41800796041c41001c00e1654002100050015802c2e0b00441c010703104901596000402c2c5000500441c8144000c60b80250302213821030043c000f01086011603542548680100c40d98251034922005058100301c500d071007902e0107003042004504001001c41c0d0041007680081500080640e0050310140c414540001100340b900d03003021400908019000040104445c400605601e800d22034000c4d5202d00901d08910054903c012518104800d0281800b4195409072007640c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 113817814 1250 113816564 113816569
    0x10206070806180c071e080301060e060702040516020c031203010315020412120207090902130c030f0906020d05090d05040b0d1e1b030b060a050304080c010504030c11030303040c05 79
    0x2002e00341641040c024140d10000c1031031003540c1409041901040c83c2c0b69451441c0420500300700c444408403030b0f00140e1000c0d0004502d041561305540a5041c4404401c0f40040410094012900003960190500c824440007002d20381821020300180c0d802c0e200300d03605640503d596140c0b03818540300060700800041000c1065650707a50b01c1c03001d01e0100545000d94030f1100440010115034140c0780c0c4085414446001c1c1d0701045580300078400400c0178040040580c001441c01e500d881c00c400d45558440c00c02d402c08a22a500c940c42c8501c402c4020050200e41d42400300081d00420f55141d071140c17130907021804580002594103c0f640700e03a61540c0c549410400d2810740c40d00720014060b5202d40303615660551641c003441d11500e802c03c944001030042c0210040304404401d0125150030f1500d800c81e4801c4640741e504c21117112030400e0410396030305d4590345000c0c0707490b1141c00c4818005510b48400c1c0400c00d64003000e40c01159016420742c0850b111808105510385c8400c0d500106a8480d5074810021130 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 113819064 1250 113817814 113817827
    0x302010503060303130e07081501090504020c341202030a02010507170d0507030f110f0a14070b09070605090108161b03020609010606110309190f0806011404090201020607 75
    0x1406000c4c1c0b41042c00b03d00c0e403103810a20a42008589005030f00070414681c0d84241c2a9620041690580681840410020340105160300545028580016890280d2602004001000c9114402d1425081604004103000c01b00964501c1403000510360700090313060102f4603d000244c0c004001d0100f03080035500640e01940300c40d50860310602460810b45512190b0800b07422000103405000c552440c1195000f0304907824000c00700c0040e0b10780524802c03598880d03415212241620a403d503540e40940006070f44061003401540122030000071000100001d1031085401029040102c0701c1c00f980750241030300d882c060040c203680010305000000c0c5c1041010300d0342c08100055420a0b00a2050a040315200070310288000e4002d47d000030184000c1a03000d1081e42d0040109180403490072004611898903480340c100c08901c145507900380d09510650002d0b100c001840c918180729680d40d0f0316071441e61035807000d02c250600509090798030312040c10f0601640c091141e0580c0580242d5840507000e4942 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 113820314 1250 113819064 113819071
    0x31407031805010c050a080106030504030e10030b090c0a1e0c0206030a1b0206100b1c0b04020417010506040f05040b2410020105041205040605040608040501020d05070e09010f06090302010503 84
    0xa1070319801c0100851400c1c41008040d000660721070b955410021405821810107034003074002c240c501020400441d40c4059402425503040f5801c88403240710000c100d016120b00069660700a0140301409540342500303000b00840000c9807180501585a008405509000842004081408075440e003006140c0800119030081050704005041540108003803101482c40361043c0160788100c0030300040003c070803d81001402c13007400c10341c07810341c80c44402d04180c0700400307207107517540c0d121510003100d03640380c0e0142d80c00392201701e21851101c01c900c20700ea8060082520424016880c00d005000c1440d940e00a1174412904107494101e10303100d48840302120f03489201940c482002b200b600c0070240e9035194102c2001006940082541d09140c14a42035900c0940f041d03000340310042000308075450704082550221203080c2401c7c0c5440d43c4600f0a607000e40310301d00005100724a00002c10800340d40104507800c0c0960203a0700000f290381c13284000d881a442c1c0b4001e14000c9841808100300640c40341c3c1c0196070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 113821564 1250 113820314 113820341
    0x2060117120a0c0501050c0c1009050c030a08030f07080402010c03050d0908031003140c0a03020d1119090c020109020604180e060103080a080a02041d0405150906100603140703 77
    0x20340e14601d504005464009030740010008446042d22018840240034a50301306400710100b914010482da1015951000d001004460715120380340380c01805001d000e4086d0419000e410760b9254003d524084a079030b07004030341108d90941390b00c0203d043c2c83c0c400c80b03a0901c41d60b03040e140c0401d40303542ea44080d10543c2006220080031620341c003142001900b1a000386000720014150408014107515020000d03d01d40340d1409070341d5020084c070070015a901a03010742241d8050b10f601c0203c560a0804d0b000300c60340c0b031500c0f079001402e0803006040748445404260465442040c100300344542d000080b404d94002ca05c000e0340c401d0f8248028001d00307241405c0107021350610500000c0e40780003003130500e080500076842994020004501c1070304254008140ca98480500c001c114503103414124200c070302c0580080c0143c284015800010100001040f50f4100c407001c3c401c8c2440f00b403a02c624180d50300d49045401d01006c400c02ca1000074014024016200410010302c17020020f5a43c0d0001103000782840301070f044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 113822814 1250 113821564 113821573
    0x9030311010209040905160803090904020f0a0b0705060402010e01020c1818010f0f140f040b0601030207060912120e06010512010b10050909010b030403020a12110d080a0f050702060117 81
    0x40d43d5603d600c10302103070b2449600500000c070300f0640400e103203d800394041a5240c20070058500103994811540b5031007541140e140a00c1e02652000c00c00100d010380000500580c0041e03e88180709001520912480c400d076903481c070380c0c680300004985030717540f283c0c5443e0041902c03040c1ea0b2080720b171840407641c03100c0302c0034400c0908400d0103512400d5489854900308250360340e201d2800c01040034003c18074040301e1240300300301c24200304200e402546002031000c2c0180d48000c01040060b803003901114a02030300301c5000c0c803100f022b906042d104000c0010503900801c02d1040c01400120b064014024800100c0300908020b81c030309000d20505040c41c14844025560714003050300155143d80020100d09040d82d1950b0303c540d0751400b8003510400603000029844010700420000035800a9100c80c4a513004540ca0750070780618000340c80d4102042130b610018040c41c1e00d4003079216071004a1038420445a00300b0320041d036410346031104a440590303c203030060f008000180009241300a14000b084407480440c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 113824064 1250 113822814 113822827
    0x12030e030406080a0b0d0503190e0a031101090608090a0b19050106051801210b0d02060a020c0405060d0b0f1015050301051915030e071212020d0305010501090303110102 74
    0x40c0c219070180c0c0000010030509010300032122201c1c480d03e00e00000c2a51013180b098503a84480356640a0185c0307020031440c1013020018200d00c5107603014000e45002d42401806620707464514101120201c4160000d0340e8860000344582c0700d18030090160301c0301000340000b0100c9031108510060028200e040c000030342c40240c003010f080303032244c1d034000d03d80c0f6a521901e503481c0b2044017240c144004092410010f00150242070500910401e5410300c0010000044c107058020104199000080c00079501c1000070503141d82c2190082804496400c00300c82c01c00c0a5504c5408000b6032078440300b400361681085000061480070071404854209045126005c07125a0701c40700d00200c04030039150000001d40c044010407482c10000c00c4008118550007840c5600790034080d8000215501e0400c02c01003507201c141ca00f240910610103540507242c61114500c00c2c24681c100b910044000d49014001440384034100c42c180d0b0302c01d100302410307140305941d01d040903440c0d0307101110240000055000c441d5400c0062 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 113825314 1250 113824064 113824091
    0xb060d0b04061d01080f03070c2304060e07090f0305060601030209120601140a0503011b030b01050403170a090f060f0c1a090606150405030c0402070809220b18041203 73
    0x83c452502802c2051181643c104040c42e030a2804035445204550300034012034000501c00503207802a114203602c07101c902c10380503901c4c6000700b9148018a4100c3e10346800810f403030440c0c00d504c51044501e03440f4a0040c580e10340d00c07060a0303192440090b00c0d9402140115646610980091014010081400840c0c1400f0402c05040c05003c3e40070101107400c8900c0c4000d039051181c0302800401c1c088000300407030580748406601450a6071000b02c1010781d1042c0440c2c00c5c0c3c2c020001c5c0c40285070000c5130080c8403081d00c448031030340343c3c052600c480110708401d200081011074040364030290744007a42c80c9403810420716400e440105030300700102c9001800103201c2c0d034001040c803160b034405c040380c2005061a0500d202402548003100400e601102c1c1d0411050240741c80014001071610403d480c0141d5840444c1131222040c001d00714051760040c855515001d01100c042561a510f07010008100020040f186c20031404400d20302e1300d542d100843c80300080100381080b4003041c1455190901203401c0c1502c401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 113826564 1250 113825314 113825339
    0x203040e0403090512010902030d050c100b130c0302040e1003030210020307051b0606010f090807051201020f0c1006060509010c1b030b01090e070e01030201020a230102160311010b060d0b0406 84
    0x80c980286d03035541c02c05078290318041081c0c0117007051904100e841c0010f42888151900318441c4420103c54844107003034140d481c1e104080d80b03c40008041041409250700e0300402a5000f0300c990315041c00741c2000b0130810741085a140302102d070705070014600308610702c01440c082d400c021301c60000d001c0d091007090141002c1a07004003034113007202c000c0d209a1a141c2d0002d440d006c0c0c05a094010003128020501003040000342400c20741c0c0d03045800200e44440c4240c4075000e0701c034450103c040c803000481e000c10100d0f030004504a011114400c24840b06448075800c440b54005c0b006140d00141c0306074007040c0890042814440700a149803040c4e1061912912090300c00320080e4420407203140c1e5124220340d035480501c04030000d4104100f040c60503500d1078000070b42d5125100380140600419800d0702c09001004580b05049450200c0259203480d00710b002161102000d81c0250081012604032110a00040c429029100001048941481102280500140703100981260440d51720703c0c000c60b0070102c0d0103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 113827814 1250 113826564 113826589
    0x406141c0207020301140c16050109050d0306150221033313020f1207020f010507021c0f0c060b04090b040c1d070c020405060f1008250203040e04030905 67
    0xc0150351410248103060851386036810056039660014180010007a440c3e04a42d0310240d0080d1030310385440f1320300b4414010440641c0c011300c0745c4100726180000c1c6d50036800c410121040e050750810802000070040c5c0c1c9540045903100d01c21103010303c0c844440c10040d40a940c100c1da1480015901c80145050040c119481c028000140499182c0c000c0c501e242100900a00e010007080540c203210402b5400341c030381e000342401c1c00841d00c010400924000c1c400c108806124801c08024812420030010280d11400b1800250000c401800c0001d0005405080030401042880c2c1e10f00107002000c5e11040001e0081230300c0315600c00d86441040380402d40c6668400e01031401a8103800100e49003d0f03131000f260441e10020804880e03800c0811070415001183c0901c2142c0584001c500c07581c0711b50000d80d03500903d0038040c0c0d1080d00070402d09011940481d003e846811400100018080040049030000c01020041030040e84200f0050054420700c00078107810511038204050313500d803900b00180d8100e0069 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 113829064 1250 113827814 113827867
    0x20705011b03020406050405060d0207020d0605010306111908090102190513050306010317070f0c080607090e060607140c030f0a0501050c040605120603150c090123040614 75
    0xa9404401d007404a0521407038014141c1800c5103454034015000d010381c00b5501c075041c498a00410b81851480f4290101c4000983c004e00701840740d040ca02c0d080e001018207010030303154503143c070500d1840101044c00b114900c0252b0070040c03145200b00c4d0703011204904028034084065400b03111055618000124410210906842e410b0f1030b60440342c0e48855590140d0310040c46030340007100402c041742841e8641503107807118240842e6aa11241060240c2100c4201c3c020030040207984e00280d58072000c10214095a01c80d07888004450303031901c00100c2c8441c261115a4030031b808220f0300b8002500c42d060702c0158102c10095404842c01c00000170f0802c50014a404420b4114840043c00c0003820301c955927210415489041c1801e09002c8010914040c141002c1c004001c100c0c0411800e07941044000804219170440706041c0c0380040120005802c10100c560201d64407c1e0103200304480758103104441410740c150701c0c2c10640390101c101c4111162030f140e020307519420005010350302c0d079490403c240c00380103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 113830314 1250 113829064 113829071
    0x1e0903050c09010b091504030c351f0f0e0c0a06110604080d0e1b0310050415150b03040302150a09020a0b0c03120a1b0c050a0209071202070501 63
    0x1503081580c10000c0c01112244a072104a0060014000560690300c1d50102503c2140351b043c00044206154482e680003d1310f1074101000000f85988402c000301100c400c031400c5189282803121555503003070020100080b080d0811303042e400c84500283d01c00c43e0700001c500c0e000304140d002032614038115602d0a0400304603400c00000759016080c42240c4030b008224034508000050081c941c60740e11004007034002011b44400141ca00f8152116030018504d0301c01c0c2d2010707145042c800e00d0b4178010b20381442c0c1702c0501901602111980f889403511582d481a074014001007003149001003c0310051231061400004e04040c0fa60100d208000c00d4081d5100c1c5100350010514981d861010f4140d41d0402030040205030700300407082e0300588402c420041294050741d4002d45518051889038114080c010101d4841b0500c0f2007006400b102540140045c400e030106503010042182400301c418a480c25006000307035001421401c01800c0440030298010624a000540d4030303a00c002c018240da11044c41918160b44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 113831564 1250 113830314 113830319
    0x8030c0c01140f070807030908130501020705010f09030803100b0403050f3a0e03010906060314060606040b07030210020705010507020106050f1503060301091a040303060b03010e06040c1e09 83
    0x9126140c80c20300c02c1e900c4844607243c40740c0b04103c0414010000d8040002e414040703002d040c002d4204580855210000ea6204c0e03036500e1629881034801c0c440c0e280184640c3d41d00003102e5028401020b00380915a41e00b080d503a08544600959510181042080d0000301c41c0000b1880480030240002d94444c0c4041c01c405090410518a4401080d040300d072a02100c503009105000e61174030b02101030720103010310242c0d060b00f95419110109003840707942c0c165003071241d00820015203078080806d89200305510321045568520050387d4138411103026420810400c0107001042c4140c0180038018448c0c0304640400c1c41d903107940400c1e60002c40049401d0303034617001408411034081c010000030b0803040c0d60314990300b00c4400018044400c6080c400d138120780c000000c241e0310380303003904801030064000f4035185d41c00c1c59580049004110850302a40040d02e0220302045800244084074101e032154205080710303450b540c042000a02169280005104081044100c10010300080e070b400310300c090710380d002840d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 113832814 1250 113831564 113831587
    0xc0c010912120221180601080c0a08060705030112060209031207140c030d05070c0b0a09031b0302030c1309020406080601060e0306040210180807150e040209030a0605100308030c 78
    0x80c6000c94003842c142c010300603c400310291602410b800011201c0c000166202c0380c4104040010320304c00d5105501540c8000300d810031000400181c4003100385e611380e80e0355681d440c500e034860070309494000c00a00304000410103100144964102c00340184401460030361150300180c905034a40303900303800c048008142d540c2400f070384004d0001c05040303000141000084803800240ca940600f1200c000348034012940e1414811403440e201f0246c49c140c02040d90392104080c02611030b680a00c02100d40c0f0800b40300c0b050902d1003c401c503c1c02c0700d901400074680c9070203c2d0204201041c4400c0350a00d402e95030120300001da51103005040040c1509c10181038554140030380102400d032259081c1740a540031009100042c4c451080c1c03548280268035000a40d5910707074441d2050112258400d0000380304071803000c55640303080c3c44080c6075030700b1603118410004201001d000c2a4094082016490b400c000f201501080964110a6001482100d46000c03c3c0d165680c001c80d0b038009469456200d02c000c0303030650007131 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 113834064 1250 113832814 113832827
    0xd021906080118090b0103080c0c0607080c0607020d080c0703121a0306060402040e0c0c242401021b0103020c01022b090203031608070206040e061906020d0302030c0c010912 76
    0x14000f030f8109101c44145034454410a620600c17004010f03030000108484030039000e01020411200041c0381590320056400d01034056005640c030b041d01d0380680800700d00b20600000d420030004075203403600c85580d03680300ca03400c00c0d0f03401068041e4144140f6461980501000f849000032032003021242002c0c0d64401c00070b26103800e800511a50051780304000903c641c004c81200703076602ca4000f1040903599241c40001c0b50601d034581500c0d2031212680c01c40c000d911500030712200c1c414014148003070250707019503244e4000b01e100392220f00d0141e080b101c01700740380040d845000d40c28031206050140c5042d065a400d40d003260301940460b45006076005038400e503140d61007220030100c446144140108115074002a4a906c142e44503a02020a1400e0f02c2d01000307180c2d01540c2e02240c0041006417070319070b10400519000403c0301e00c03901c02e85000b003000030986103041c000c01c11349250b82d00070002d41d408444158002d40c4003520b02000c50343c09111400d100c000c240161440c0e244070b00c3c0080c490354500400a40030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 113835314 1250 113834064 113834099
    0x5012d0608191502040b0a05071a1605030a06050a1206050609062b0b04060615020f0705010f0908030706020903071a180f04050901021e090904020d0219060801 70
    0x2941207041d07401000c800820040c601607800001c10381c00607410f000500000d2080d44d11980000e040810f0061085422001500b009805640c1240d26402000d4800d1740e03034001101c0b809081109110f4181c4480d1140c0040c603400941518000b89030b41e1500001120003c440d485a1036407104c403054482004141d0003020342200054820010608010000500c0b80030825001420300402901d181c100c000050010820f003030b040110003009081030305021300941080c1c000c900c210409500d810b5402840010b0900a50040c40c0142084a090400441c0c85801c160b0b00802000801e1201141c003143c244010030029105040050f075491034035040c107017014a140e00c820074007034003414113140b09240c0a007110300c0c3c40010320710701c18141d00e4000000c0c0d40029850701c6980040c039050410010b510154000c00d41c3e00800071740f1202000700c0f4401c007000c902c01d901407640c000b2408400704006003040c0d080740061a100070300700303c40412601884800e881c1254040000500d00c2d9004000781e2103890762500b130 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 113836564 1250 113835314 113835329
    0x120b0d0c09020c01060f050a050d030203040e1f060203071703060406180b0306010608011d0c0705030d090c12050712140d0e10050403080307080408130801140a0b0d0f05012d06 77
    0x291b032440d180002c0d00028051123110b004010032144c2804251089c01100d0252007924040021810005001d9070217126a000000ba2070709402c001280c4940000242c0c4c00c416403014003408220800f00386101c4503000607000b1900161207200228185210078001004014032010001e0580344210803d45001410307402881802480b0700140034007044900105281149826000c0341600e903031070314908620940d400a0454003020608a55807542d0307803c500e0455006080000c0b4103500c1c0c3c85c4000b194060b9800c02425944203a10030001d210403805103c8000d401040200e490185d42d018260600005480c0c1c42c0006007004242600e51403c40c1140b1000702c0c030f80c60481c1c1424150741d0b0303c40d014032010704040180040600020200044d003400c0303d406050640000c103807103640f03501e01400ba00024150769140440700300003035440055489030700c039206001001010300d42059101d001b8403502001b007c0d14655258a502d411110303044400c0d05040e5070000b40c4c480d40c000c07002584030803280640c20551 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 113837814 1250 113836564 113836589
    0xf09100e09040807050a0804060302030405280f02060403061401030312090b060d0507091506021b03150c0f030411010305130309140604090609060305071203120b0d0c09020c0106 78
    0x5000e5166580115030040d80000b030595204824104503191807080c000080c000b6400003000704425a0640155000b5407040c0122a0741441a1000c02e003101c2c03000d131800107072141444241c070225030000c840c0407500b40080d1000e490292240c440c04103441c40502d25910104d240b10041081607442880c4e041d05c0701c0030040801658180390703240e4010000162006126010003001d40c0300388001032003d60021311711020108001d00310f00c000d80380112035601c140b401500a290b544d0759900d50090310702e0111a070060107002419244080600341e070302d0180943d401d4a0b024000302c00c4c4680f0140041d4040d40c0299524618108100300060503a44010203e00c01301010880a60000c8d42100e40036060340c04041d6551440e0b810300000c0340d907502441c6e0011000d542450380c0000c0c801000d41c808d0069078028000d42d440f190711044940412044100c1c0200002d0ba03107603008030a01010390054030210360040000d04003202d04d0311910588480c0342c0059030b1041d400104481070074001d03c141c0009040200a41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 113839064 1250 113837814 113837837
    0x102040315150b21101401020f030a14040b120103060605061c0b04091e02270c18060304050601060801090b061b011515020d030e030d0e01020f0f0910 66
    0x31070140c0c04a00c91043c416001051310030f40a0700e072076180141410304110000251800f5145014a1202c80c49152043d8158000700e0b2482d520110b0101000000c01008520744003204600f09c0381c0400401110f80f440c18144008a00d282a103402044004c810145808140d41142020300441d039540d801130303104803010400c1301ea101c01b01e03003031001003001e0f03043c800111410000d001c240139110f072001c001d000c0103100c0c10704503803060040e01d8452800e00943d2443c1010401000c0350030840070982801501c0c00d000b000003030780b02c14910010000b0810708481e13038240c0e6414002150994200340c8040350260068001442800e40c44100e00e80103010340d00d000c0c45042800404030b030b81c0d8890b81c0c0c00d910005603900030240885400750024501403035617200c249191940c1e184446c00070200b22514500500130900c840d440e4500c240030b00010012004051440c2c040020a404001c2c51101591a2195024022000001c5103030b0b0150074082d45040343d0580d2a40000304114102444442000601108840c035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 113840314 1250 113839064 113839091
    0x20c0c010e011706030106180e0106140109030611070609030305180d1b32010c030213050904030c1202030d0b03011a010804060b091603050a0627020c0f0102040315 72
    0x31483d184048480e40b1929110900441d024242d250031801e100320740083c485543c00e6103a07004618096900000300140c40e02c1c1d8500c03003450748495001da80020f0b5200b00c1480802c0b10340e40542203904448a4861901425581e024156071a4040583c0400c0d61581006204030001040302030303405418010749100e803403200c0301a05928100c4100810000100ba00000700050302c1c80d10418000c007000d40c46040e508000c2c1d282d81d070003402c10f4104041e500300140340043d80d020380203440c0300d88850400e10103038070300344000d01589100050081c2d0800039900c00c000c01080c0015a4104942402ea01647c0d80307018040b8070406403070424451a0082e03140841e023040c01500c030045803181d01c6d0700f444c103050103445604107070b006170818001080d440000c01042c070150380350204801500030710076141800303d581c549507000125401071040c0041c5000e0003c020004911843c40c10b262003880703050044c2084400e0031900d01e003c02404180100703070741c0081c05000b03108a0464801030203900b058240040341d4080f46 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 113841564 1250 113840314 113840327
    0x70603021803070b0a1413030212030d0c0e0f0d0b0a0207140d0c0b130507030308091513020405101a130315050a0b030321090718020c0c010e01 63
    0x105020158089525800c00001d44403540c03404400400720340d8070750780311011040141d000f15000c5000c1005250004050711340c01c02580d085030714003266074580c1844c5400f40400c03110250407000050004019442030402140318025884101c3e0f40c5564a41440e035007440700700c0e07400601c45031041003c1c004180c001800c2084540d0301a202c0340c0e0141c0c44010b1032030400080307100d07a204a21a405035043c000c50300340d4443c0e01c1100d50340c080c0322030501545690030100380242e10f090b00609550003003d030a03c00f081c000c01748582c004d05550211460380310b0440304903101290a40d01c240b90005084041419440c09025090f00800d441c11507a07000c61a1130035544013004a8200ba280b428ac1c003040c8555036801d14039a4000441d0006142c92410198017903000041a007100d098550728035081c0c1d51802401d00000b69203085500071011030700c000d02c0480820718017a00600020a0713206207a40840d90f228280c6540c0c0b03410f0641c02000d6143d10180c0d1249040403484000541007010104000509030307440807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 113842814 1250 113841564 113841569
    0x1d100e150a09050a020a0305010510050109030206071b05191d090a0b06010909050a0b03010c0503240409120507031124101e0801050105062d0409050c04030308060a030507 75
    0x4400242c40030191900b94140301580d50007a500010060001050000c1134001e03602c14804090030000c401d8541005680014440c0006504440e051060710009443e00c20031070605a00201940385040d0b46000186480e10300c044112005a200c1d4410403a103922842c03003c41403980f04d602d0007882d140c1098900d540c1c0750720400c0944941c034038501040c0c290f402541040082d0001070010702842c6800840c0001504c050345465001e58a0400c0b404c841d20b104805482c00381110003580c0c8810800201c2c00d5210090384508191b0041c2d03164000d0340054014402c085420441d916015124201401c0152801100321000885034100e407850b16003a5403051905204440031034842080d50712034800001c20618240c02028090507811060076183d081d40d000b07c0100c8500e90002e1165a07210340500405000300d2240348100140c030703401c0d03841c07030006841004500181031340790905244c0d80e400d03020141c4c0c0080e940580742201c00a41801416405808154071a5044d248082d10310f10390343c3c40d55541d02c072a2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 113844064 1250 113842814 113842831
    0x50a0e031e07050601060801030201080609040b060d03110303070c0b0a020708040303031107063e0304080702220504021002010c0c1101030b09010806090c0102070303021f1d100e15 79
    0x860030711490401c00d070a403114103402008070381c0b2035a1160005400c08000b8002a80412044000140c00746040071030f49118903400840810181c48070000c0c092200e8a008089060000780721710321940107010009503101c0c0945964016098515041284c4409005000c05900900402089004c03503100c0084a084950615002038043d18407070388000e1038040d0781c400410141c1010401e41c1842d80d1520300740d0620004600d01c0e61080c08004170000002c07052114403900f09001e000290105050300040d18510380082c06103070240d4048018046000111001040da0550700c2d010701003941032141811038951260300082110012160001e0540105104020f10582441004000e680d10175044401b0500020780302203240e50b101c0c040f41741c891400b1a0f000145105507116542030307602c002820001c4a40540107414640498100d002c600102c0c5103880000f0f94403000c4000c01031980146485100700c01c00c010b0320f01e5903441400201680c80350080c1410680c00b0404180080090303940050300402e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 113845314 1250 113844064 113844097
    0xc06010501200303013f06050a0e1b12030f071a040201020c0f03010f090803060906040b10050a05131202010306050103060f090e0a050607020a120f120f0f11070501050a0e03 76
    0x70b246501406d040000030400c00d1000d00303d17003404815070003035440007030600c1641c00340000c0d52800e101804031420701200480750b0f0b2100001104550760061640d6000c10090b0006c0b0003c440c01c025185190700821054940c0b0030000340900078480030f40c0c055074075900c2d01c00d5681824102900001d40e40c40001141034032a800c01c20800c9210340c3d00b503124404d00030041c2018000c0c8541400e051106030001c948050043d40201c000403041e2070248100e0f81c03a10001459100340b4503076041c044542d5044a9040700c24004208082240041000d80040050619440b081010000c0317200040580701d1a9000034140360400e80140400c0c07910380d000c0b40981e503964200145114081001d2407030b0101c940c1010303000b4020032003440720300c560210718815840d001e150401480103c0200403106550b102c1c1d20b41c1e00080700d002d405140044581c06c624508414443c0c041b07281050080e01000700c0c4c0b410102e01005440004400007003100078040c4e10b5000d454000b04000004054a8207030303ca1151b0703000168a03860 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 113846564 1250 113845314 113845349
    0xc0904050711011e0e0c09071805030613022409010309020604090203131403032412120c01060e060f12030f0403060c03051602100c02120c0601050120030301 69
    0x481c00c2401c0030114280300130310840708800e164546483c1c511440410850611034100c024200001c1c10000f052009080440b003551680f200b140c0114000760310404110301c03601300180300c2d80d00300481c5024180c3c0141203516400d5030f2040100369500710344d0300d6040c00740100750b00292000b02e00941d4580c00c000e090120340388455200050880c071583c0c005c1c0b20028808400d02c55402410303030341001d1043c03003640f005408542c0601613075500e001c01c44449090b8001080000d100c50020340c4100c2150001510100c40c010640e803500e030078003078008882c0d8400d040c08075201160310004d0180070002c143e20400b5080070305100012402d600c01107003c650040040c60003251700d03c8010021920401300c090103094403a0707140d24241000e00a0b60302a280043d04090100f1460001c50040d003c005c10070f90014200304080d404e589020302003030f003900000d600414a006590b146c1c05001040403644100160147d503060500150100740f08103139070202e481052030030390400c0030000201d0b8107441c0c00000c402199034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 113847814 1250 113846564 113846567
    0xc0806152b0b0a030f0809060d0509060702100c0c0206030408040b0703020109020307090c05120405011e0e060f0403090303050c01060b04060e0312030603191518050c0102060c09040507 81
    0x12a4031a011440d2000107440c545440d102040c0d11070341d8515070700a01c0b202c80c0750b000300409540540000382c1050200d02c500d0340003410000080c000800041d02c101c1c1862074003c0540c044441c111950ba42c0c3d600040d0411020507814000c0000c03000b00308100f0008491790050041c80084030710002401424000b000c0303024020804265802410001445a910303000352400a01900000204a000b80b10f5007801051301040c030f00848040f0505075480030308100e040181043c90000240040c0c2e01e655840c4a070301801901100c00854010000340046500a030031a0319510341031004000b100f03412a03080078080040d505c103000c0000c498042c40d200c0d03141c90803d98003d0040c201c50b80500c8000c00c00050001c1c00035000404115525012400c0d160840c01b4215a07500c144001c4504031707415004141c44400602c80c00b60718008c41750141070803071682000b907503d0408560300801d50011101040c2d055000304403040045e0300d04250700388058102402d15a00ca00880c1c007445480f98480d90703ea40001e80002d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 113848920 1106 113847814 113847817
    0x903120305220f05190215040302010e010c050f060103140606010810050409061113170c0a03030c0206160c060207090e3406030b010e01030c080615 65
    0x281c03088140d200400405900403101c04060f0724860001c1441045034100d003540f0140401540d500741e0040119134280410704201402c0204000e00050341c0c01100b581720403400b8200300300b03003540b14605a4200303000c2d140070500034401e8900000178811121120728008001405452841e2100001103c003007108841c02000603501c0181007050381095441000a207000d00380000d400740c0902180307402c0342d2150f0600290440c03180c40500038400700d10560440b0805d00070003018103086d00c0c00407403042d407010b00c80034060000c0ca402840541d00d910044810050318804488007028003403421a04982c0c1c54000c0400501c5801d502080140081c4204020030380400010501c00000600300c902480d444040300c0540741a08501c0328101e0040860107000e4955506e01145400410b0001485103c95141150402d8100600c4458694204007401d0b0450310950b100a040b400200300c02140c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 113669064 113848920 := by
  have h0 := BRFrame.cov_init 113669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 113669064 ≤ n) (h2 : n < 113848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
