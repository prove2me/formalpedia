-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4423
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:34:25.657487+00:00
-- url     : https://prove2.me/submissions/e3ff530a-060f-4f4e-8b27-018c18ad1983

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 795323741 ≤ n < 795503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 795324991 1250 795323741 795323747
    0x30b090a02070305030a0b01110307060614190b0903100e100f180b0405030d050f160903021804140d230a0206010e1e07120f1b050d0e070b0306030607 66
    0x380b40c85402d03640e881c0c5559100c1382000c000e0110748994904005511200c0e00c0e09240c02d0005d0990544a0b4601041087c9003880a5000d2020007035000e2240202d1403807461603c12510b905000c07264240380305500c0e0049500043e0501d0403010500300f0083c20280e00c2180490041485500c1c41310754201000a45e5042c81c2c050200c501401d0708a006008124006e80402c55016005e68010301c80c00440b441e0141d019400307030503039400f51031100d1602000800e02481b5000c40c031404032040380700e241291200f0300d50740008825003018040c4481800000700403406102c5400c0c0c10030800c01d405c40841d12218a400300042510b40d00c0720714100740780151842d00800d605190221060000c2d0703640200344c02d900f000030304524140f0103001913048804841641d01c0d81d6140c5c0070920700c11a0a41c0b140c054040d9000e0004040e111001e080042c06454025900c4617210040c40020641e407503031425944a01c5c1d40100d8100a00440d400321141d8468110300041c05601c000089d84514015015512141c5071103c0036 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 795326241 1250 795324991 795324997
    0x8061302130524120a030c0203060115051207032a0e0a0f0504053d0801051b1602040608010b1203130b070816030c06051e0103110f0907030b090a02 65
    0xd0200d240356800300d10107003003c00040f502240300c020010320000f01e050f07003440d141022680341207010038001d40d80c01055103014003c050050400221048034a800f29100030071b244038000b00d03115480c6c854404110403a104c3e50010b108100442d17481c1d50072040c5020400f00c982007448402c00024041d03030641e129410000c0f400c1c1d0860702c040600c003d041d400c15040002a2600030a0407151680ac40061900c01c92044100040c100c0f0740c1c2c902c160046070702c00c0b8012001913a0f8010300c046a0420b8240a10784080310058080c400d12280b025858940c032044444c202c21016070082c0d0300038184403000c1402c0e40306511041012504883c410031310840000d505407030b8040c1d01c1505040e411202e00030000c1c01c1d0048010401c4921500e501031030110341001101e1004011300e0240c00145400e036001e41084414403035190072a035026421142d00e03200d12040c0010f240e05010013404500c00018601a0751503180c440101000000c014203880d1410640080041041e02c0170701e44503414200100c0d510145502c22 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 795327491 1250 795326241 795326251
    0xc050406031511090612190507080402091005180123060f0f0d02031303020105060a051018091d24040b04020a08030d23130b10080613021305 62
    0x700c0100d6000d611600b8000d00c415106282110350070003040ca0541e5070140100802d40780303400c604000742022000350b07035440b05054421021a11300000c4c4008913401480d00d59200d40e0450b80e04a642d0f442c180c0e880080111544090341001c0000069a2204074000400741a10390714001c08929641900014221142100010340c0050f410003441c80c800001c070005100b1603881c0c900b00d510785002d403209082282d10480e035504104481a02140c00c0650a0045070b80010f0211030b100822428407000601008981100b40c081c04480d400007100840d40700c480c0030080c0441c5904110790340100300f529404c80c2d800fa0910006000350b03515100c90300010b440302900040c4040c000340b4181c0d119a87e1030318180c006001030342c0c0007245010000362050700300010300612082c588041201000d0b00c0e4040e040761705071949424032100348010000c050030f10f90441c504180c2c1280b0003034031a84841e0011102645141c0003088980100020810784480c40d80701c20030401d2090700c49c8402174074504180c108072603007526 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 795328741 1250 795327491 795327503
    0x1c02030115030c0b0c031611101d1011030c01060501110601060f11030c0604050c0406050a0312350f070f08043e0f01020304031e230601030c05040603 66
    0x3c00f80480d080300d201518640b0f0f20581103d1521904066401800904800803100410902c400e00700394240000c611481c20401d0404c51013040d2420070741020681d02000450140304000b5034400810712501c00d031008105184240d03941d03034400d0b1b40082d0183c01113000707080c045890410007103541d45002510713034120f64043d6103a5440000342103048418001d00324032070711140320500018100c9241401000d010310f20850051400716401d10030711060712290b41c81030b48030301c40c050710403c00b05908441110400701039180c1804802c08515540400760382d072004840005004240c01d0544261402441d40107241007141552141c2c0c0700031084444000d9000750034002120f642c041000612140e1600030b00284c03074901b800308034881e0201200388841c02500018981260b0318004010f05201c0c0144084100a10140d464981180c84442440d400300c52403540e134072a50b00102052100c0f848648d28245100103000d03402c42c0d0011020343c0c0d550300078003058a0103481d0440028040c0f80c50310600f42100e6101c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 795329991 1250 795328741 795328763
    0x3010b0711031f0c050405031c020f0a021e1903060c2d0807050c03160c0806060904290c0909012106050408130303120509060112020d030c021c0203011503 68
    0x421000044d2004511a5080c80000e0102050a1350207002e4041c84c1c1c026811322130185007500c4402803174290179480c41102c07038000307254150158940d03151a91480c11000080a40c5502e1440814170f1036200541c29001c1080c0d0b110041f0030081c0c02c2d00036001d440302c2551900700c1c02c98038442c07166850309180c9495943c0d180f9002541da14500035404250300c49094103100742002000d50b24142180d0105101041d00011002d0032020046004080800b40c21640020003003407034448042071181c003002d00064210030100361503510a040045540d001d804000300100150b0518044007540c0380c003d00c00e03251140c24418000f20320180c040a400d11000054028480d180a064490800801018001b03980d031160070021804809041c0b03d41c3c00c0294420740c0c1d8810b001448900700341c120345015041640540081c4010441c5046a22640500c280c04440e030311a1200036203019528080403040c02900298801d03a0414081c01c0e03070b030900381c40600a07002800008080300d84240005114040100050644 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 795331241 1250 795329991 795330043
    0xa06050d0b06130e06120105270a170d06050301060e010302041b051c1805030301060801060905030615030c03010f060f0501020102160308100b0706061a09150d020d0203010b071103 79
    0x620380c1c00c4c5c20400190100c41c0d9a0b40007902c040c2501d100f1030f01100204005200d03c0c8004404020305400c80403190003034510449290b64840c06186219440120300d4000315003001c50b070b18554000e03001044000c00070459180d4811081540072024442a4030903483c06200428000d44100b140482000f1070b9100c03442c2030348911020741c110303e078241301d18966a039581c089200c52040c407500780c03a868000c10007503450790300d010002000140c05810280070404c00d01001c001d540c0700024040c3d0814501c24a203203003100072101191501101c000003d50660a05008070803c070340070390007401650101030703c0180043e01ca800581c240c0c807038454900d60465100d0160300110744544049034100b0303035524000314055500c41c0e01c08030513001903400f904c2ea1940d44000300103500300003062600d2030390050f403841e0038010350b040012054000421403180c60403001a001903010015030407914a000200003c540f2541c440800a6840d000454100e50800000f4400d180305e180c0010920009444600b0500c40401a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 795332491 1250 795331241 795331259
    0x140c0a0b0609220314040e040f0209070504150509130c0e031006030c140d0512120f0c030a0f180302010f0f050f0a0902011718070609060c08180a06050d0b0613 70
    0x45101c41700c0f15001380000b0815188010301e8600440c090084400c0500c950b00410250a202030192400e008080100704101c50110318a0040d2034000c0c240603848452281c041080d66072568081000070386000f6643c5400c0d60011000c052a00e4140c040700c0c5501e40c181c0d030071021501a800082c1007500080820005040c1c0e0764404104c40b0f0025008683e1402e0070b9803100d103401c05c02140e19a0901c2d010071080e51001500880c16408120000c0c810694142039081c0320040c400130341801c414680b6a446a449564141c0100501d1425031816604542c0300d0b040007802080c02c81c0c21080994102010219a04000c0c000c10740221900744d01c1050725250000d05400a20b529a0200d0600c807284500c1c078581100f012295210340e034802e4100c03100b2060320f8009810600b4036080344040c08038000c01400340c0d640c4001910328055000d030b6000d070361710801c0785a070400d04c04900c407066200259140100309240e021000d08400401e4040a200e08402a801c00c01d244c020000796807440e8141a5080216002d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 795333741 1250 795332491 795332507
    0x90f36060906071829070f0303110301050a121416090e0105070f180b070303091e1101031a1201090b07110a120302070f06021c1b140c0a0b06092203 65
    0x48070103003070703002d40d500340141405800483d400e45090003c10182c10625404d40200032b5070001c0107600314613640c100720000385007a07840c0c0100020f60100110180c10444031800c03460742009a40c1c201d60105a5001c0ca20014030080d0048000719030a00244080d0f400050040134016029600e642e0f200e50b0400c18111903003a100e080d54482d000d1910800264446410000c09200c1d0080e41c012603101002d06003541003602d0800f1182c040307000040518040b030811360442c182210f09190100b03203401d02c00010b008007080c0301341c01d9a01000072079803010289415444840301500c12a80d01650780da846034140c800075401a02203500c0c0d00b00c150b609000403a0f01d88068000c01b050300380141840600d494008007505084011500301c6d5001800e0401c81b290800702940e41c0000c0101845018441a9540140c0ca04416104148414000660300e01740e142001d85102103212001c464a807591810701c6548038909986a038040c108132400b082031a8910754205081c840c100e1005c40a4ed09203581c1211011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 795334991 1250 795333741 795333779
    0x1302010e13050708250e04020f0c1203090c03070e0105010c061d1b0406140909190609120c0308071202220f05090f360609060718 57
    0x80c12820340303880010a9100d40342c083c101e0303a900c4007040d02c0c1506080b24140f2400035920710300c4560a0220880560101c03e050b002d0744c00340ca0160303e130303a0164603401c40e502400480e0321050190111055011090b8006940314800c40da0131104504503010515407074030f03254050404550042801800154021070700c0c50003003032049500095220341140e40e0f20000800c001c60304a56080304030b01d000c8980c82404000d070081801c503001c006442c9007804001650042d052074500842620b000114504410302c80d81c001a001c28800003004078052401c20010a800030b8126044001140b9680045220754034000b08590b164858641136190804152085800c6036043d26840e03808100140b429419410604c1e01c010000400c4600c09080050039540a01c882e0001c0c0d00407206041000007045000c6100e54014180d511400c00d00c8070840c00400096582c001d90140c0b04604040d071801a00d8005805803044d501e03641a11444d8460107011034680d91400c00c007120b01d0f00c50007030500c081219440e00b178942c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 795336241 1250 795334991 795334999
    0x100509030c041803080a050c0405040e0c0301090308220b0c180a06050c010b03031e0c032a0f06060f01030e0a1502040806070c0803010308070201030212010803030117061302010e 78
    0x301003600006043d100c40c40030311a500ca42d80080c4004054005240c1030300040d68890034045807501c0a55000240100e100c1c05120b0342e110560a030300d1300b42c14040c1c41c00c8040007500a0201521504001d041d400040e95152141981d0024100c41c016003901c85480d426485803242850f0307280c01020000355044840c1408184036001c1407058a0f9035109243c1e00200f04a460740c030f8541110706551401c45140c4108540250800c00c501b0380074101c007007000b6000131700e9415910f031220702d20300c40c484ca0f43c090210700b00c0362584c4417a50a0b080c0258902c030400c0d203444250465403d0891550340b59200e003820380d441c0c0d0308a0b80030540c0c9945507000350080220418040115a8103130640e03281c00a13104802c444051010368005000e0280d83d00a1200c140d20041d81d09040803407040c0c03551280740c513200500c806848007501140e103c0440e0312030b4044401692400c0c3c1c4075442541c496814a8070fa61080c420310a8101440540701c4103e803010540600c2030308074210810138010720b0340054868060b1320207500e900c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 795337491 1250 795336241 795336253
    0x180609100e0c1f020c0406080a1713030f0b010902120a050a0228091205060109021e121006210903051204050a03172728021c0210050903 60
    0x80c540b81c04282c040c9103007400342101c5801c943c0c1c41c0040d04080001d54034500031401d00000348800d900c001080c19086901042080c110710003034a418032140245001d03000107001e140000001d114002c118020340314081c094070840c4e070340c1e240c05000482c442d1f0380c07070840400041400a40544070542c0802d5000b0001040503140442c40c0c40c9011200303000008484808500e0010311080d503603c102408003030300d29203440b400340c1449902c5a654a480500c02c2c804050340000f21100c0c0c00c4c21000c81d00304e0704800e4000958503034024120001e4058011111509240b140c407000007107551085031212080707240703540040c03500481c3c00c0e41345002d040c2d140c2055050200030031903441203417101c1c3c0005100b98010320260520725403510b00100303c455a60720b8114010600ea061051030b0910448416410b080c0c15544207484034102e040c581000b0f0000460341600b414102c14000500740c031010304900c2c1740308481325101604034040d05041c0c14113610b4060741009640d05044e14443c0103c0041c082e41c24020101d0312 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 795338741 1250 795337491 795337513
    0x50d140c0604090e0d0504032a1505030901200d0f0605061c0b0f1003050405100204140906030706052203200906010807020d0c02060c1203180609100e 66
    0x21540c0035501083d0819030700c5080c0c0003600c1d0b09100f8207100386042d2400a15051468550030142800d80c00b184200b180755802c14100d041c0741c00d951030000c0c000304010140030030038620040c1c2160800c45005e1419402c190b00101000c0030440e00b6250b0400700740600e801c3c00c0440030140010101c400040015650b540800715140e034407400540602505000c090740941c008160405c01e03101460040c601584220802c500302e44d64100ea4032021040600d4005095900c40c203000b403070000440e0201c6a0944002004580d1a10320420b4060342401900c680005498460a25036194424401e200c000f510900201003d40f03461041c2100d1483c845007032010040d01d94403082c03190541900100e0301c443d124041c02e03005051100304e9560205090070240107074a0030650103522070301e51401500420010002e01d404541d91031080c0c92605070b040048078819001c042d00d6925503401510003520b44540b600140d000d0000004800c0d10500c2c0903009010f0b0141e501007520702500407099800c50340d020b5031401e10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 795339991 1250 795338741 795338749
    0x1509190503160615150905090405010216030504080111120c0c100c0206070f030e0c060904020d020c0105010f0b0403080901120225020f0406030206070b13020306040f0b0c04050d140c 80
    0xa45958010f40c40040d0800030300f070201342c44014962124042c0f404002c415450b85400c040140222042a82c0c00d400c155610b14059009101d8500030980d0a50800c5c000c3c0c1c02d2540c02000f400c156403004008001110642200c20150f0203041302695014a2020001c0c2e07295803010084c205001320a0111641c6c00c48581c10740c070a8854086510005a005604211340f40740e0100c0c0c0001030003c1400c003040705644074019203440311010981c003401048000b6660401d91181c1d07040360108024444111b40f42e0304011000e5018001c00e100700d140744a00114086040c054110441d0701303e03680403805500e05050400159000c030703081c0044500b00b48d4240f001c024803883c0c04003800c0c841d905c1c045007402000c90a20420400c0001c404149000e103161031400d0005864030003c460704113401000780a01d90741c03000003807220005900030082d054001c41092004021140c4091490750341b007145a120140d03192000304203a0f010760300c2150360264110741c002002c5a00001c01044040a6905982d2003110410200d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 795341241 1250 795339991 795340027
    0x10261c2f0c121507140f120a0e100903090e0103080a0201060906081015050d050a0303050702010b010e0105070218070c14010606020304170c0d11031509190503 70
    0x142515044418240c4030a4000307008044110000300d45aa548500e85051a03035208526140b5040d1003212070007046035036000d010200c40c2c1c860300008880e80c541d00803100c50459005600c0b44e40b003243c071f0a07001c80c1494031603000340880781d40840b00810203600703010b400368003030119120300b5414020f00f0a40411606130648043c0c0c082c5002d480410303035a07010150020700311503140d885002c1d06894080140094800402c80360b8082900d01c50104548807010604481e062240d40f0080d881000004501c3c100700001c552880102c0c0a92406c00941e500c1780803d80c261034206064a0006d085954000c44030341c0904040c040795800a00303114401003103100c2c04403030428141c50003404030f0075000a2200b001000c1c444c41001030074040081c024a85428400b83d0b40f40140d010301109016960300c0280c45003001c00c42c0307139462500145901d000c060746090902c072038500a48003e0081c0940c00c05014044c031310030151809026401c00070310445200c03120740c0750112074140d0211590300040291b072010303c050400b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 795342491 1250 795341241 795341297
    0xe030105040f020f0910140a09020c0c03070f030c0b07050a06060314101a0d1401020409020a030f0c0e1203040503060f070f0908060a020a0c0b10261c 66
    0x80c082d501d2210b03004002c0c0e900c02160b910380c8144980410000000000a01c032011100c98416070f811880d200400a075581c9600e80003a092588080382d0030791039000c00100702a0001058041d5514552203400d6644446001d007c084c0490590744000c1040510120040101500410a0721012640d660340d4100317450183d84240c0710000240582c0c90100c1052240084588440400f00080020090030800d44448e05503400d02c20a02c413031405061090030198610542c05180086554030b441d0840c003002500300d2051200068035200208500405a00c14034209075011740301d14140701090010440c07001c03074412010546000a2200160584041003641c3c092001c1d43c00030100740c039003e4001404c06007000c04101c200801c4140c104103121000c40c0450300100c03034800140c0d854141e454255210040b45400800510040b0304001e80c040c2d00750403110694120f10342c08075103149030000300002ca9929940a910980111750f800c580745200d420228401601410700c0b000440055000c520a8001190 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 795343741 1250 795342491 795342503
    0x80720010501090501060e091803191205060d03080f070e1201020306040c081006140715021b0708030d050603010f23100f03140f0624030601030807120e03010504 71
    0x10040c07003600c0603070044502620951802c1b500303c1f603400700080c078407010103031000c9030b00000d401e14107401900500c00c44004615811541c4441401400d00400110ba04204a41194900b00214041e8600b00c0082c0421030780585c0c4240264a42c61070001c1d9100c00a07120409004404a0550f11031301d4551220b000050040d000588a15010041c04240d42c0d199038907400f005548400c200c0e81c001150301c080c050b2580c40c503242d00c0240004000d030510b4403503c40041c0601038284610111304030180c004004a00110031442440007110130801e640e24100e0180020355001880041058212644101d9010348024008242c1c4600b00b09941c007182d44072004d28100c0c1e941c0586868200509041c201c1d00f18980303042c0740c110189800381d80c02450342c0d40e01000304501c0d150300c40c0e1040c5000400c4031804001a400644031a8141a0700310034020280d580c4806000c0d1014060115601c0c02040050480380c00000c0b6510341992942c0d240b00c06902e40d451281444140124560140c50900c00c2d1481240314038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 795344991 1250 795343741 795343751
    0x303060510050720130b0a0b040f150c06021204030f0201060305030405011202090907030b0a0e01050d02010e03251502070f0306200301030303200304032c0910030b0f0907030308072001 81
    0x24087c1d02c3d002600301c000070710401c00080000745000d03150b07041100d000105a070741903140402c0480d140040144041c020324008202c280094440d02041070040b48291a4080007200ca444140d086c0c40c41448080c04903041400200815400741c21750408500c00b500005103003040040c00540740302d03000e8580c6030000e6900d403014141410141280d102400b00e080d1000482c1d80f42c05d001941281256a0090401010108800054504009080311280b0040034000340010101e0248124602e610900e41380f15249901c5000a0340081408000c0d240c10aa2040c00542140c681300080d024201040c111001c0701c109440000130381c4005103010b50301c02d82e80411044a2841c1c404900a40030007a0b03200c0020800910000a80000c282072054030025a50201c4406070210b406a41c0101f01e038041e00314180d44104082c81d84028041ca090743e1003406e20239000c0d25480e0b030650040304200da480b240c56024850a01c0406e02604441358042d0392460103441500e81c00b01c01640c0d038030300c0c1e410440b07171a0344070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 795346241 1250 795344991 795345011
    0x100f051905370e01120503030c0a09150206060306070306030201020604080c0a12210506010c020d110d0305120a05060102060a1a0a0303031a062a010e010c02060103030306051005072013 81
    0x16014a0040c44101000180241179407903040c0c403440082d00e01c0f90504070004413203010038000c40742000106281d40c0501080080c03508042c0d1950821a04180720740506000508018000e1040130103681d0107a0003440c0c80e07690703580c2d0081da660100704c800c0328610400300103d0001d8062130005585603400c0e61400f540168404484010b011101701d400740c000d0402c8100002c59a001050390212501100c4540440840781401074804d9010100a904a90038a004c0d42c185500f00004205450f1000c40e10f800b1590b8001d4540110390060b9505401a04101c010504152254000b0b8510b5114640000c1c84031080500041c084103081e80110301103a21030804000d52510082d0114110105403041c07890050580e81c180d00c81009444503070800b2980c5121941c01d1202540250040c203021002007204040325440031b50340b29403d206c01c030002820103401044605140401e09001d1034640c440c9401c00d100d503070b075800741984680c2d150180300301444a400038036690601407450b6212440b200280017050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 795347491 1250 795346241 795346259
    0x60c050f06040317070306171509030a0c0206181801030203102d0e0d08090618060408090d05060403050406030b090c2b05100f05190537 60
    0x40c04a40990070a00800000ca5007021118080010180305402183d0302e0040a600510b0107421030040c483d1480c0c2c20714a122000110450440d0360104074903802d584030102c0f513542c0d200ba0b8011100003103c2c0c00c10301c0018200540a000581007492800703d006007032002003107080e20355203410058041c1d0f010040003035050074003200e03c0d80f00d0301c1c030000d0203d198004034003054030031030030f422240d1160ba01c281400c103101e1a50003844041a8402a10b600804000c00100b200c40e042d0303140700480c0141000b1176903500302c001a50503040c03410303c0602801d0b07860792070300445030700505100c0340c10040411600c40018814071086205510984889880e1030070311800404880a40c6903143c0114040018416079942c11004c0d5111448004200c4603c119100c1c503c400f5440711180080c01181840280a4896500c1005009407100031160349c007040d56540800030454400c50302e1814507031010a040c0114108041086504006903491101c00c2c607820032402c0f0034012288158500c6100003409101100b2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 795348741 1250 795347491 795347503
    0x81207120507051203070309140a060606051608130b0a0819142403160501020c010305040b061011030c0c0f011103040b0d09021201050f1b07140313060c05 68
    0xc510300d85076040c40116612140e64880010b42102d00d401d002c8000362406109402245d151640030140004820103046019903850100c141101c03854101039021400344d01c500f0985005a003a014a207041212941702d00c2d4060780600003c9034041030203100829038410360030090145070015a1060380038a8a03441d030000500c54031411122190800743c07c02c078420310424600f03410901400c292030408400c50405044629481c40d840d03018094900c010301c81d810341070104411a02c0a07000d075240703080030a00450468504590003086034101d40c010641c14140300780c10444094443c00c01c00350043c0800841c920b0750700041001c0e4000d500c091201e440e1403d00002c500000781c0c0030b003051269807007007401803901c90186000ba005540b03800b10702d100c04011150060100c458002c0c0440b42ca6400c1d20204a029150458401c05054484004039269500c0c1c80a01c6400c507803400803150410846a4807000e611900d0b078401c91540c401404000c52100c070084801c0000c048548841d00300411614000c0d007800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 795349991 1250 795348741 795348773
    0x71712061203071b09110c1b010f030207022202041d0f04030503150d03030c11060103110f0a05090114030f0303070504030f03230309120c150709081207 67
    0x40720741c0040d07031081002080c0d42945502c550b0308090f42d491480200d840e5100c580c000c0200505040070303108a502c001c0003d00320038010500350f03001891404121181071032010810350000700704111340d907862440799000c2d2440d01e20090106407191080c40c01e2060345098000c3c2c42c0c2d01c990340050100000700c54842200304802580c1d02c60040d0307290032180002a50350080c400340c184400000000c04040d09401c48209000b002130400c41180181d04008009140800444010440c0003062031a0484005041c0e03041782d80c00003c00c0c2076002d1000500c003a40003c0c0104c1900441c43c0340e804105a600c1e843c00314040c088401042030300c100740c0f07410140380800c0305544000940040050010782540030044800f6240c101c0f4030019540d1181c501110030030064100108071010900b00000e84207507490044d40513142180c121008804074a41640491040020740f03500da030301c500c1c83d981083e261060001e80c00422414007150342c3d03a0317404a06007440c001d40700c5000390090000c0c0f050100543c1800d180c0c111 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 795351241 1250 795349991 795349999
    0xa12030b120a121416061a0102061302060c030405060c0d0f05070b0f04140d02060a05010b09010504090f06051201060906090219030902030c0d0b01150f0207120807171206 75
    0x7202c154a5800b00702807050320a02c10007000f0880d40f1640c6a0316411240c0700c030318402c0595410a45401e003000186040c0c0301c03441000c0115500c04030307190b100240180c00307500d00030801c4c000350307400360700b0170a60794001c40c1c104c08640000c2c08005120f42d20880540305082d008800b805034851000e42c020f0010b2503039040c803c107010081c82400003050314030310500e500800400300040f042e160381c1407840841c40040359040091084015014000f030780420824000c40300b501c0d084c4400d98880c48843c0040c001c01582c0e03800501d0511081020610540140c0b0803c00410000240151500b001c075519409041c80960710b82e4456174104400c290301e00c110300041070388110031401c114001c035180380480c6010340d0540401d07803a9a940d41c01e40d034061100101c114001441030b00d0300c0d80c640c0341035184d80b0000d10a01d6050b00c2c1508400c000780e40128552500300486030301a00110782445882c00708502080700035030f94031000380325800010310065070b018a0741c80030140c842d4a03156181c5c0c2841d05110000c00d00f0b802 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 795352491 1250 795351241 795351253
    0x70e16020616141e092b0303090c030c03080403031205060d120e060c0a031d0a030b0c0702032a0103090b0601211814010e1b01020a12030b12 62
    0x10b40010301040c2c1c50301003051501100c02c43c00824007103024065103160040e40c80d1010560902d9407503070402004481e5040c2d5075440749a40300507500500c40b07148640e402004a18414180c00603202390f02080e0050301c0381d0b602d00c0c1880e403240c4451800c0102c2d0382044078403030030004060044c981c0000c0420243c9140c0d01061000d45001404903001c401301401c0108a42610344a50741d003603024403040106210050403094888080f8401255200361402054020640a1040c80e100c996010407410001c135010b4620404146947c2c0c4000d02c1d07010080070198054014024000142d4041c0310011440c01440030000d0419030000200801d85d079583c000e03505040c6410545000104a01c189a0b17000c50242004440c0d940e002102d020361a104800198100d40b4151425290400c0034000d041c4050142310303071100c0c1819141e40b8a0880300c101100c21005d40c041d416244003c25104600c0b403802c10184155050103042c2d81c2c91407880d01c0384a44000c0440d842d90750144039810400f00c2c07000003034422001029 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 795353741 1250 795352491 795352501
    0xc030c0b03061c02210c0d03051804060302061207020304121101320c030405030109141905120a0e06030403030c08090115050d230c01081506030f0414070e160206 71
    0x1d00c0124043c1c0c07140280b109880315200b1017205010b003002444010f40f03540326241d424034000304254813446c1100c05800c0428813110403170919119810a60f5030181c4000d1402d03410050381151000001c10702c01c2107100c2040701150078800d410600400d036100f040303603106200a000000d41071044074040107001c1c240003403c8484c210340800741d41c41e0810010089a03076600c0186000b0f802d6109035040340da019800c000030b2404200c41c40e510010180003101c19180c07807480c100b400d9070b02d4064032100a003e47e4816030740d0740c101100002c0100b40d02580c0e41001181f0b5005c40000c1a425001110260301107540ca41428100c2c5400c09001a80f2988010003040508542c002d4001085c032a03002d014001c0f02000841c00410a00004580c07417001c1e12510000c84000380c46085130341d5444c1e0800302d40003403020b20105140c51008441150354a000400860440c3d40d09500c00c0322640006105403080105003d2000703003410300380301c0c0c0c60103420214151046c0e49002c0b400b200300300081c803085204640c001000c00c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 795354991 1250 795353741 795353749
    0xf1c0605010816030b1c140c030c060d0f06030b1f14060703111203160306061e03020d090209100306050f060a050616060c080403020c0301090506010b070c030c0b03061c02 75
    0x641016010700b8000340241c10000803a03528401e800142e07441c01b29011002d0103200049030b42045500460084034905800328040c035499410081c55150070143c01c6c0440502d6060680104200c040d031094001481a600c1c1c0f03a09810788000c0c1c407a48940608003032a10182e840380e0f010f01c0d001d011683c091008081d10500803800c1482a070b8806002c10408011202408805002c42003640580104e49500c90429800c001d00c60041c0c5514500801c9c03420740001401801010110050495102814003402405074290041d5100c2543c0e40b0100e941d840040c3c0060340d4000515001d00a10000c03903520f0b905510702941103820280040354019100001c0111541d01e80c1c3c0020140c8406440c006d44800302c0184004d4042801d00c030040100e0301f00307012203001e194444480c174462802036003180d20f81ca504030141422100d200c040a042034110340010300a80c800c1d01c00601045100b80c01c802c2d80c2a550780c5628280303810541003001010300c00014000c0925025441d90030b10071000006c503070003190f42d900203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 795356241 1250 795354991 795355021
    0x190e06090609040207022806020a0c0603050a09061104090b061603260108010c170f01210501061509081203060108040f12020c190b030103170f1c06050108 68
    0x8030744200c20009500900e0345854042d01c800643c040d10ba1410669000d17901c3c3d1105c0e4901c80c1e1418603d20302040060000d100085002503203401c094000c5915061640c11800f41c0b00c01803101c400c05807210030100c00075485204451f258160f0f240003a40b10fa050030040300948029501d040e10502003885020b82203031001c1820400c0a91604000041c204c000068001d212074402c05058591182030000030b040506402c0980c1500c90303543c5401c686078000500205101e01034500c1c08200e0035400040c84680184485c0c84c0b040b07580144d10740c04803a1940d9505095502c6908100018506028112001d6800040460180070300102408000800c511050802d000c014952810040e1040225040c820307240001d058880d00040159019100010301135607070350400319614003400f080d481c200d01c43c940317190700d01d0285d41c1030b640503c4c60340e40b9640b070704820384100a68810f01910100441440512000d005080c03842940ea0460380039500743c40140d0840e60035510090601407000d080003240c00c070140c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 795357491 1250 795356241 795356257
    0x1a09010608030d050907031403031914061504090603050106050906061c0c03091a062d130e150a0609150501050c070305010e161a040e22030302190e06 66
    0x200154070307545d5a41e094035204c42640042c1c413100600340d0400742c03100f0200082d0b1050401d101a4040c1045003034088086864807502c9422030075080000c22894075003d902500e0801c0000200d03418541c03526440c000b150460380c4210741d5a95610420001ca0407c0c3c00700584c0000101c940c1402c010140089000c42d540490028070752503998108940781502030380c01032680940014070448010441000c0c20280c5a054910505c070348001c1e4908504072050307103054441304101c4a200c5040728032440a100c3c0807000d8642080001d620340d5404c3d846072008102c101003050404080c62458200200b0240460390326403c0714000741d0600d500d4400d13140003800e0200c112442032800507500c3e031322038003610f050003d683c00050695081c0150098840c000040d50b0308102c00c070030300c0d12180d1171f5a0302d0048074148880101c3d00380c10809100030421849407515003988181e03001c001318079034400905034a10070100d0f41021404079902007500e031180180307161115620121400d0040d110070200c4002200e601910b20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 795358741 1250 795357491 795357517
    0x3021804171c110a020c09010b0a0f02030903030309010c120c0e100c02090a05071407020f1011010501060203041d09070902090411040b0d0506030601240309020d1a0901060803 77
    0x10700d50b61070018106500342d407400d048800c1101241440e1210030325031003010700d03400512941000f0745d61441d007401c62a04a5081041c40c0f4540302d000003040d58049804003141c41076000c240444031060710113000030340c440c521301000011034440d4218058a04214103003407801c0749184c04000501103403c03448003480300200b01e0740b000b1400782a1908681d0280d4011000350889210414488800b08130b8200301c1c0a06519240c154401008014800103030060920280d442074aa0301850002d0800340c0d4411000c25461a144d02180d0303007101e84030300303680c1c00380e21520060b8400035003040050072543d00040600c0a43c90b9403001c60030a0100e0654502d518001c10841550004d901034903580c865100880a902c03151f0700e5900c03290748101502450b08200c030a513800e5414500061018500800c0b1076040e03510030301681c0c0d1041840614600d06510b0040800c0c10306503204140000b40c2d850845508289100707100851955110707101c0d00b00c1e40100a00903003500d07818080c1c248050344000c0203540722411400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 795359991 1250 795358741 795358747
    0x100507050307020108280b150f070204110c16050415030b06090a1d06090708010c02030a03150905091c08070507031409101d101e0215100302180417 65
    0x400c102500140c40c00d5089641b84070100350010040341c60300854003801045403640107208412a00900f41c0c854802408840751080019000610302030380a144114401c1c00e00c68142840303900110324040f9545c21030202102d52420400043c03505001c0c1c1d000c4411710301c201c140d59628680c2d940d0000315001e040e55100ba12048c00181100c2196403010801d0604a000705048a40c0b016145880700000c1e00c9a580c1d0f40902c0c4000300e00344005006d18418011981d004510348110b090301140101030041403c1d015140c0250009003540050242c1ca001d03060b070cc40a80400c110169828401e4046420b0940912042d44d0400c50b01d50b40200c143c820f070135058142040c00301d0007403016113458411071504641c06068410040841070307000305c1d03c4c01e4045500d5904540c180141040100345607041c001d46002500c443d521000200f0786001c11805221640102c0d1061000503180880d200b004481c2d0003d500903a82d400c2003949094821109070203200c1c0040e10b82c504182d00c500d48503034840032200407080000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 795361241 1250 795359991 795360001
    0x70504060f03030f0e041b120c1b21090513060513020705010f14010602061b03160315140f18040201110f07120c1502070611010902060f09100507050307020108 70
    0x103885c90a40b4050080040022114041507981c50001c02d50000c030004500c0c0300d02c00c221002c1803040e2844206962a0a003000301d0040e20403103401d1003c002107400b083c040c8088042012003580042c50b030415904d5044d2a9401c290501c8100c403494109d0b0403595050590030072642d210341c1000700a80011640c0540e880c1c2c031034203080b03002d441c640140840591501b0b402081c1060701501d224161140c96080c0c0d99140ca034480c4001445103c1482042c84080800200f54041c07a0240f203075925001c982400310302510b02d164800c080c2c83c041d41c089480310304452807190007850030659041c0039103011030f011600914008003142003a080140000c0c1400031440d0041e00d0203000300148021001288211030119031a03614000356809655002c6441c03071084200032812100f07951400e281c1c5d40c010703802001141d00c0c0c224200d542c0385086060032019541c0742d8400d00541c0301c1d040104100305d03d040015035140c82080c140440d8500c1c500c010380400105004050000b000401114103241d0246090756032601c40c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 795362491 1250 795361241 795361247
    0x406030e0c09240d0b010602010c090807050f010309051e10020a0903060f020c0316020109050d051903050f0a09080c040501030201270504050403030506030c0f180c0d020a020708070504060f03030f 86
    0x151144081d407000400c2c80804c10011810030850594665900038800010210340031799030301440e40218a182d030820401404141040140d0040d210740514010440c03140949589060401c035000c0701c00006014055258105020010a004800d070f0200444c600700d03411748001c040f1142c9010081c441500d4000488449015806541c204800f080c00e6a0b80c0e0441e1030819500b9016a4604901241454000180c180717020800c012150303410401030300c903061014040c00758005480f6821414040148601901355013050080e28503040c26485007804d903828500428506003a030110940708500348001480140da00c0305554558422a250546080584600d01c2d2421481900001e8010303207001c0c10070040c5541904a80d008480540c281c1e5904000300c2d00380000078120345011078005011a0061152030000083d00c0c1c2d1080f4404c000354107180100103500280c0e484018003000503071107100c0521140c00140103500062004039802c10081c1c0c03425408545078001031101406110360000000090340c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 795363741 1250 795362491 795362551
    0x609050405090a12080f0a11090603130c080d022a1e1005091c030e062101030803040b16021b04022115040911040902060409020408030406030e0c09 65
    0x940324070610f100180718080144045c404541c00b4500c5041403002c2510700b5107030720890501c03481d4007860750314250b0440f00b131022550003d441030005460071030302c400100341741181003000303031003610041d0021300b507000c80080c5801100c0c5400d0301d0001816031020ac040a558884a10310002074071040485c500350315000b111a81310b0509990040c1c031103824091019403101c020441c01c4401c0740d030f601a5514048801042c03007030031900180403c05031b80b551031042c80d03c3e4000d080d095484403032040d12800000703a44080360500381c2c401c540e181c10103c140810880101031466103c215003000c18002100c6d80300095646640b60071100e207402c030f02c0c90102190f89998044840f6017035141e262030f41074800c5446580701901d084070710802c200c0000800c000140b420b8000c51129980048200028014440400000b409045c004a901003000c0100040f1000140040d0009091000c0a59111407806002400390343d82c04009076004d801c8002d1954503503a980705d07a07513006414040c6101510402c800d503415086 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 795364991 1250 795363741 795363743
    0x60103032d020105010513020a0e12030c030c0303040c060f050904020310151106070f08010302060c070e04050304031704081f150816050415060c08090a03050123010609050405090a 79
    0x1004600e550b038054002d981292801e031080d800002c0b00c00c0b00c03070040f8042e4240910020b40b40c114941002c1c50f10781c998074404c107640c5042e0303860141018400380c40e40d800f007918150260000b004000900c03141c45050700080200b404d0140d400005100001c00c103120b12001c0b64032031030b80800850800036032214800301400c040c3e003400041d1a80208003402c05000c08141c42e003640308071000144140d00c50841246102081c0c0c072409101c0e4215420004203420400c00c078446807040b050700047d0010f420788694021800344000e1582d0b181181069011040290301d400c1294004001c01c1094900004010111421529265800201422418014100440c0c40326080401b0030404207850801080080c00400f00c2c1c1100c1822a03590800e202c280c80111001105099400c181040501e000e0102205224802c4010307500d40041540040c0300109190410745003607545c0c40e40300c2180c0c3e02c038514226201c02503042004d8950700d03084e402040b50b00c0034050603021319141c1c008110600020401d1065403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 795366241 1250 795364991 795365057
    0x2040b0919090c17030c120412021c050114090c010305040f0b0601270e06030105060117040303060b070f291f090207081210140d03200d0e030f06010303 67
    0x20702001503840340d03030f50030900862a403401110341f00701d8104038980444040321030440102d088840260204287ca2003900d0f840c00d00e1401201000c000641c0a200d0568480c400401000d007604223000c0040c54400040f0030641414501001c0c032010032021500300490300d0f800040003449035104401210114911014020240e2b502100d025100464441030320030b541d40c0081c800e94995134101003600b6035074143d0745103010524400488030403500c5400307043d83c0075001c0c3c24040340259035011002216800410103554482821030781c102000079070514030301203902d000c820320554054201604411a40600085145001a0307200303501454030000520003080720200c219202c080038104041b142c1d100c0b00504441e42070f00c200203100592480040b4068650485415180300011014490095000c110590611408050000242c4070803010202c1d440c00c500060012404403a00c050408900c0b443c0182c0700e07400c2000e800805210028040e81100d40500d13250101c050307208068038040101b00961445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 795367491 1250 795366241 795366269
    0x2030c13080102091305060d060e0715030c0809012a020c090f161b080310080a03110c0f2b0b040302070317071104051504020409060302040b0919090c 66
    0x103107a0190702900c40a80c0503104056150b1712039800c8030854100300e43d00c0d40c1c0000010f07034500c04280140d1004e8036210840d400c845246454556040c88080840705110000341c850841075881507210f001075400805c0c2c90001e0007130040d210110070600b01c91f1340c0c08038501110860715041c2603200700034005d01400040c3c5404100c0c01c0c03145003100300c064200c0c2c1484c40500b402180b08080e41c419013444402e88649200c401c54002030341e80703400b0b03640c0c0702038044a8800402c1201150f480130500c402801148a9141e104404800c220303a28102400f0381c1103540301d48a00140442a6201c050190f2040c020484501075018140302400d81e40c0b40913070001411a043d48400c000805400046540903240074600c45242e1386000d2525000910545000601652030300c0d4042c800c0e400c06801c19900654240464544543c01001050032600203078840c1420700c0c3c0315201041903040c18400d0711001c1c6420307508400300b860704101e9642e03040c81032100a031186640c0c00081d4148804050074601500940d00e030020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 795368741 1250 795367491 795367499
    0x30803060901050303120f071707050304141605040905010906140103050c0405070504030f0203100f0b0909010c0c0f0f02041a040c0c030818030c120a02070608010b090402030c13 78
    0x1125041259228040c150741e00021840346030001c1590804565200300038801d0380c1d00c0d9110181c0c0c440141110b010700600789981c0c980b19560308240c0d4400c19540e50341c15101d117000c7c18103501100754005600915048071100c0d0760704545076000351040d2075096502107131045441c6031540c01030905000180041d880e06450b40c0c92601040f051034104c5c0c0c05401200c46000b960742c10801220340c01c4d41c582c800f20300c081000304000360014160f04200740c00207042e540b2110700e07001160306440000b180013220560f103520103800e0340f03055525150407101c1d000080010b078415103005000c00c1e80303818000d071503100c4980c020000c00010902c1081d0301d50740503000f40020340008122140002105404034421030414104000b518843c1c0303111109030f17416607584c2e50f940e211110519900900e800c0e080314240801c100c40186a04c3c04c12009900f802220700c240d50360000c1d240001e04044040d0040030070014040010090410034034183c5007020011240182d5944500d000700d0342520407202c2481040308030000002d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 795369991 1250 795368741 795368753
    0x61521040c0e0108010b090411041d030c0f03040e1f0305011a010f050c06070e191401020c0303040b04060e040212100f080307020d0803040305130b030115143103 71
    0x72046800740e01d42c5400c144d80368840d650990741e000e042e850304080c5450001340488c1800c548203100183c042c0000542c56001e85122040100115440c1d200b40d000084400c40d41ca001c01200e2403080c524000342d070401d0b0400b00d0040307442c080540750420103461143c0c0c1c3c1e00032484038800d14000f507074004020490302060032012051840c4854829000c00c94200030200c03690300036001c41d40c1c4980894040c180c140d031b40b05000d07525003000c03d0055400899400451140416030f00c807034000f4108104803142c3c61040c3e80002448c0c4072421681038020740092108201c8641c190040e41d05440e0603080404103d03d028010800034040d02c0d0f1050303000060481880b05d6052100300030401c3d1403c029014482c203803500d040c5581d0b40b00750000203410180c0700366840d005c1401030018542040c401c1c900707149071007012014000d022109410803489444004010000c4641c4034482c110308140a08292654080070085045c0c140900000c2e00404810640401004000521145041d010010320001225102d003000703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 795371241 1250 795369991 795370013
    0x90949030507083403020421021e010c11150703080601032f0d06081c1d01091401140c0d180f060c061b05030f070806152104 55
    0x5400403905a1002c1640264183c030510400c1194245103513420301c2010b40c0c9542128440740c0a400c040c0d00b8080850b00151903290b4020121804078111036008190040000303204000c0e0f10203a40c003000050680342640c1101090a613140c02165110b1040c2d140c10103d00303032500c0407041032840d810004e00c0d1000c06400c01000b0f070203000c003030b03070200f004109119008590810340f040741210310f440c042204505184420003851410a0f003100400e96960b6a00800e03d0308401c0201c5011154500011920307403580099009101a555101c0300c07201e114040000c1c100d04000d0141c1d14815070203601c009450390140d8200d4521b00044086555100c00080c0940c0e250401480b032240003c189410f2000400c814003108402d07a40c60111700c60001345000700985404000000450710240c40308060f4040180d0000f0b020801891034542590324a055443c048409038010285800e00c0048410300c6540c1e110250150004601e11650760b5a600a10740030002d43e449032204101807805103801c00042003441030807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 795372491 1250 795371241 795371251
    0x507030b0d081903020d0f09030f1b0605150a08071815060e01020f070f030b0a020309071a07050a05030d050702030c0619060e150909490305 62
    0x10096922014204240510403000c090300c00c2c9000d000c661441c1c0540d41003910f03a250b41d800d005241c031800816a8040c0c030300c1402c4850a283c0c0d0ba0041400341038200300103241c213020910344076003110704104000d05419003503880a040e0035984d10000e150092504035002c0981c40c01060495081d0782c1c0c0b074000d50340d59114018445141c0d84070881d840365030b41a01605262111481e507016241c0e041c900d0490f080c1c01403c00c141d0451246001480082605000071000b504800c1414401e0b181181000211440060107003082c0760310410401c5500034010843d10309482e441901c2a03014a20011101e1203806100400740050048076144402c02a00100403c9441503174802403044da6a50627040e03031a8004c4000c402c0c9203803c054009541d03c000c40440304800c80d0144d030001511070700c4664007190584c040310420008000d00d4058000c91801210301c41e0310510110050170032540f1a804210360252034260100312a141e03001c0a1441246c3d4003100c000780400c003482e08045026044000d01415095070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 795373741 1250 795372491 795372497
    0x2120705040f020a0c0204090c030c0e071404030201020a1b08070603021209031303030e010314070804200a090f0e0d0f030f05070f111e0c0301051f0b0705010902040c030507 76
    0x4118940050b0500a0b80c034241038940b41c0c41040c6115409004c090030100b941143d40c80803080d008000504d100e0f4509004d086a2020300881d03290441c00a82681c950f00c4140b01e6004041c0410001070781c1c0000c482140d142d000300c43c0c41c1003015115420700c0c6900d064010400030701504034003027095603140c5c1c058800c2070005441e05080740c585540c032948a11070309100d00b0a18588100600100780540d02080700c580c0103160004407009207550702d00e921242503507500000f501090034030050000d14101c0c00e420154442e00103100385405000181d40304854451150b03241d4640c4110fa00c81d41459028900340b20a10301503c5860104080003884050a4140c07640030910701011180201c41506c2107501c47d403807686030101c0801c0186400e0b21040e060458441d114404c254551811302d24030901280340c14200740050030400024400c143c2540c40052a080c1284603043e0090071500001149800312a81c64202c1541d461700390801c18090f00c6620b00103500641401080000554158040da205450300d82d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 795374991 1250 795373741 795373751
    0x2a01021206040b03031b10062301020106061d0111030705070e0c1309020c0f070e16031a191505030618040f060c03090c080708010e07180f02070212070504 68
    0x6410803040324082001c2d550194401d1007081b00c0445007017010199620081c0460303489107070490100098444903003000d041c038090082d1740302c41940c0303925040340845000d000038020182000e00042010400c601801ca002d54139a04070300590b40942c04244800408000b41e990703411030303800c006039244501d2003107611009680001500801550090b90301a184914052081c0d51401455001075004409034610901400f11148040c0c0c03c100031038002062504000300e410726102001041050500100d030b070a041c01c01d99440c01c150448403022840030000c840000988a02101400000d034464110708140021966148081358000e00a94030404007119a0241c8245e00014082051025a4000c08506400000000260594000515014091900060321440f42e1180e4500882561100425400541c07003030100310001c0c0605020100603100400f502c9145c050540ea40a004903609102d0503a201e0201f04d8072566501180d03121f5400524150b84100310201c215110191480f0f1a4480c80c544 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 795376241 1250 795374991 795375001
    0x303030916150207090218040f0903030509030a0903170c06010602210405090f1510030f0e0a0b0a0504060f02221505090402031e040b040303050906040b0106052a010212 74
    0x650ba64400d00b0384558064040c00d40740c505010040c1d003240b281c101180300070507259602c03503d40e442100b404458040d00441e00c40781d982006011180040c4c140945900f0401c042070090341c100c1c03082d004984c0d201100030612111501d1002890081c6012804180503101c000115140d00141003181c211171200d924a40c0c80d03e8114078000ba10551060940007603260740040c422000461846604c1217151580034a900c89900000d8110035042d02400d001c40ea43d03003920b01c404141d03441b0307030700d0983c483d00014840c11200f42c0340c0c8003a07400010000701505881d00c0004041080c01e07041b0768481d041005e000c0d5100c80c240132000c441c02c180d03c0703101d040c0700c4002080001d18014060340e0040c001626111903190001030800c1c41b019600003408401c107402d45514104007041418006031107940100b4603050b146c01e0070714004054403000b40180d44161b01a10500c07000c00c410349003c40c1141d14500b08155201c072050315051040d160001c4040303410781e429403900381296044d001002c0526121502c590750381d5034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 795377491 1250 795376241 795376259
    0x305010f2913170a031b03110d0c110d05030910020705030a1109070807050306060d091e15020705190201020a1a0106020d020325051e4206010e0303030916 68
    0x142403002d80080e41840f2404100b212481d009003895000e890314008c581aa103030014a000d05015070138000980c540000d100b800310942080040d140104e80a180401c0281c8800c1c1d581d001d40c100051041d9090941030540e907000300060001001d0103000c0d921859581d040ca45003070850165014021540800001d60340c03482000e80070b100b81c6107030b29034a04603140d03442446820b0b080702c0e210b0144a1355419900001c074442c5030300300001101e200d0785411108954581400020100e209458290740148012800650f0100f0018200311003100060140c504a0004178070b4079100e4040030300320500c1e0b03504801812074a441c03c07505031076494080780c81e108002c01049030703648104206070318000c41820350141400183ca01c4001024000c00840d0b05034094003803c00715080300342c00b0780d01c9194424007002c15901e0b080d9841c20031101c0c19042c040e02c4003d80080d980ca0600d0002d5100a590303100a00045031603003ea000c0700c20140c2e01070300f12074403458001140d40d920030b0702e842022444030170b5803000140c03012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 795378741 1250 795377491 795377503
    0xf0e0d0c0314030717040305190b04020103050a0603060207050604020a060e0102070b030a1407020c0306010e010b030604050705040b07140105010b0720030a12030f0c0305010f291317 80
    0xa4050320300c03940c00d80380d034803031911080d00c5014a20702c0c0d020400c5030f503010460700c01550031000b2548802d10b560380d21b0742c0781c081c1c0b910310b141d00401c0c0c100d02c10120381004234044281c41e80c0e10a40a08006c0741c0b6030741c0d004c890f03c0140010b030402000b06101052034000d0080c00202148130301d20a442e005c0e20940c0700c000030307a01203040c1c0c00c204d030042e48000c205003c0c000c5424043d50b000003d111005c62608800d41c481c0301090004c407141e2006a012416114403071804000413401880ca01b125450194106100000140320041c00036000b00d8035040401c5903c0d204004450003082e041861545440b001e00c0c2048200c0d2240385041207130343c281000030030070721130344c604543c105079010f110b440a00c0350803a00c8910807641400c1842d4540140401074010410884402602070400da81c001101140541880304841c840b400c0c69080600e00001809841c20600701e0714140c4540da00381150503201500740c04000d0030182101c0404580201e0005d00c05941e0381d401d102030b50001d00718042281614083c19941d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 795379991 1250 795378741 795378743
    0x115090209120303063f21030c040302010c14030f1815160c1a12070c150e010b0d0605251d01020c2215080d0f1209030f0e0d 55
    0x45411110006984200000d800c001b205500c40b0300070100290900d11800c4c04210044903941049407030041000340c6012420032425000061815070030000051140c0d4043d80c00002d0501c03c124401e0020f0141c140b20b10400740c0e2444040300d40da4000c145444c04550801302080d10070090507070a0210614210003900400d0039030750421130808200144861303401d1042c0b01c1c2070b10510403c1d01c011a8084402c0030302e02d03034110b01d0540d1558803012210074641c11040140480d00300054005107000040042c2910351541c0e26440c408643c1958941310140186640600142e1104403204406c1c100b11041d08002d00c00d1340c1601428606a41d6542c040c0c44e0000c600e95074074001498440400200d40c5a021000800ca80610442d90108101d401241e510081000c603461032410080848900c2810703070103090f6002080c44080c40d1940d1a02070501d80c1c800380985418103100080100c1c510700361150829a1005110080a00140d0326908020b01440d0740c612001c400640039905009080c144984444680703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 795381241 1250 795379991 795379999
    0xf0c050a1709120c0d0f021c03020a20090c221202090708010b0d0518010207051e1f02090d020a0b030f060114030f060f042318060106030203040203011509020912030306 74
    0x2441d031b41e42c503648401c01d20003c03640002940c01102c80309094200152146200f500100040341083c1000c0c50b04040b0482905103181c1000e10f0014603031075103150316420141c440d12550b12509845540f060340502d07041c00d803101c1d940c02840050030722041c40d8040d00240c000c1c0c0304800d1030f803201e26040758200401d00840172001400c00400d44140e596a000c10390022050450700008680480341c40d0980c1d000c0380302640c00b6804a40304a9401046000c50310700c40219100034544542000b441800b5401450000703c4040d41c040ba9100c11500d890f00c0c0b84000550042200840c1a181c04d56140302c1c0e0415540e1880111a120004d580355004402c107061803c51030705007900b10b6981105003507503000000c0c070550300040003068842e41501e03240554641003d00c2a1045000283c000100a89080041154514625640300b082c0c5c240e0300402d80d6410760710785150240c2c0e40d641d00d0012034090310140c1c5500c00d0300400c500c070008040e45164050b0020003000c6801071480268400c1140d0f03a40800c0d50b03180c1d84 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 795382491 1250 795381241 795381259
    0xa0e0f070611030d14150603011802030a0b06160302010b0f061927030b090c0105070b131506080105060409020a050f0d0b15030d020601060f0c050a1709120c 69
    0x1407140981144000b0b8010b4000b26131820301c08080b10b8080d60754010800b128060b10400340302c514103083c88800030021054451b80c0c00d40d0325211200007084040c0d501c16028940c000301160310034555400000d0f19100207440e4a540309104e40800d0f0050140d0407040d00154a0900c2a181c00c0c40c04400b001030304070005100d1803d1000b15583c8620f25003060700c10700c040c0f1203105082200c0284d040071995410011a006c41000d501d10f090240c8107410052580415030809001840e8a03030300b01c01501c0d10b46412481406640c1d4400002c01600040b10078042c10100718888a04200040b5410040a80d106500244259119070b800d1105580d000c81c4000c0d444000880c0c00d10280c00e20856000c1501d1005100a0413031071140c0360021400026600b0700c030303003003128441202e40e418100000007503070f0168801084c079581360540041103200b504445070200b05c418401c840500008001360042980c000c1c4400c080c011110a65004079408003050601038203c80e0072682c82c07424082012030340c014024086101c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 795383741 1250 795382491 795382499
    0x20907140a030c110a0302010b030f06010b0409150b0c010605040c0e031e0102280e060c071a090303030906060316081e03190801140d020f1905030111030a0e0f07 71
    0x809003400701c0080c010442d500c0c03132442d0000d4080280d4142d05000b5000000d0100c410f509150030046034040e010915840440104095040b001c1118200c4034805800102c84002d140d8103001e408886d406900310460104a40c0c06071003040d40101d045a100b1203042000c04110b010170340d0701244800849601d0f0b0801201c100e1900c03242e044c0302580d070868000051411032400701050a0104030400a013003103000440c1d4880c050341081a00040310780448070306040203c51030302c1a58407075050040b2962441c80c0012260150346600940305840c20050550b6200c2c60204961940d40104030390030b0744a4802d0421000d100c05916032000700380c41c9604058103556001c60b908812200b1641d00a0103c0d100030002d41403109842c24500c400c0503080da594030103070b500d132801c40c202c1644841d00a03845500c3e41016500103980b10184034440103021b1b21161180c1c11300c03041d03071040c060603a8030007900b550038170380303050002d00388900214861a201c02c0c0030007510000002e43c0b03545103041454111551702c0004280 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 795384991 1250 795383741 795383747
    0x809060601080417071407080705030709090c091a10030218091905181c050d0b0103151401080c030402240d110c010c0f230d09050a020907140a 63
    0x43e0701901600040350355130710b96403211409a03c030b07030317816649941010704000035600184031010040035030341c00400000d810702c0c000a0b241d40d0588a035104407560b810068080050310821100100701e003050030030540002d003410319030800e207290025103e4000c0301c06000c80103010340f0030380704180500200c03900702503001020310240c400c01800110209016441c0c05144e220580512441403000884000f000c0c01e458110301e243c01c1c00b200380b0b00c0071104030110044405034800196810720100349800b00c1c0518200f80140c00401ca2500740c01d4400101c1400031912460150358480705140a80e118581a500c0415802e01800b050b81c0096015441010400d143c401500e2240300064414249d50310b880d08600091003119079010070403504210200b10109800c0f002c0c4145401c4400ca810445044002c208004046281001d402480180e44e1694006a1f4032814269944c0000d61032041103840d541382040e5035110880c80302244110540740c0007840c000c1c401e900c00401401100e00c42c03420301c0d00640b029 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 795386241 1250 795384991 795385007
    0x150f1e10030b0301021b06071b03140c070e151206010b0304240b0a05240a1403040b010e010510020304060e01122f0f0403060c05040806070306150809060601 69
    0x1800401d9110b0034030200b02d41e003c0c8010300c00d00310b5891428260b1900c0c2e00c989801e24000800740c20510030418100880203078292103085040b540342c42c0800142c2008100b0400b0f038061181e0f2114070384500301001c521200411034441c054120600200e450081358420085411082c5038035807560340082c0010007a00c0c0b201b101079504184240d211052940c000b01c0c070b80c85c1108000c0c0d40d0008040c0ca5031712505160400b03680b64006030805494112401c0440c2d122102240d50850010707010300400140d03001307094414184500300d0b01b03824040c15a281014141001c07410403e0054603110b40e05c0070b00004407880c0c031684000c1c1101050300a1802c0c40d02c0c240c002d039030413180856034505100c01c03451500941040740c828091960703104154030000c1d410388042002c0f40c0d0305458021900d140e0410101c1e04942506040d9030840c0d502000101d91419101400c07601d50203641c1c000303c0d00344200c80c1400b0100760503802060503211100c40d008561200c0a204a5008006071944c8569800034070114003194460840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 795387491 1250 795386241 795386269
    0x91209231318080d05010e1302101107170705030c031507050d090c0303030e060a0209030c12010e01060f0603110702010507020603040c0b160506130308060105071505150f1e 76
    0xb212184601c2e540ba0451039510800c1ca443c1400e0395100140400490803010b10340140003038401d41d031140344641c0890f803000e41d89400c0340e052044805001d1117000c0204000c0c0042c10044403001000d207020302c001d42d40c0380c01c40d0090b140300e07008108404815081c0020a14407034103645413811840d45a4440654050388907010b0030600341e840e40007040120b00c01c040241c000318030960b0001448044851200c0c00c00c88060a82012107004014800f61940c00240688001000312501d66480911103186401000340d8841c0c0c00d059401c0c5440002d560740402c0004c800c886103038400b4000304e10310451a8615100313140000380894010321035100582004000f4542c0144540e858001c1c45403130324030249a54100310000c01000d203610b0b2504080060521407503810040804401e11103000c5e6a40241c101c42000b04030300c0c10414041400400c4c40f8099620f20402402c03100c0c200301509010400400c105442c000c001d0051918400c5540345040c9503201e080241d0b40d60719503102044c1131804201224090000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 795388741 1250 795387491 795387521
    0x1506031c05070609210c0b0105210d08040c0b1c110c01050c030106110303040b1f0e040503090a0e07080402220203010b04030c05030f030313060912092313 68
    0xb180b0800206030344940710315940181c1e01c011102d01208031456804114442c10020030981042010028030001c509506480048440501603081d14160400400052000340014070030030790000d510a8104048034011760250042d004100d40b140b6207120b451191856190108495140e4a003290305103034400f000540501c1c112030b203042c2d190b620b860b0a480d0140c0f440000c40500000401015800c07464400c3c182450303e000c0d505504c4d142d110081c2c5924028180c1c0210391411400c4403110208070840f0b80a80510b4903101e40320300b41030400540da6000300c01c0e0b643c064000b24001054800d007000c0040d22030b00e0305541d090082d545590a0281c2003014903002e12a00c503003202c41e61500c540d84e00180d8040d00003020f10300c0c0c4407461401c2079004504a9400b45000390041c0c902800760780800700c00c070fa50000118001c51050242c0b880c045005002049014008080d24000c50034465805880e000c04c03070760100c00035a406610a1415074911a04d500c541d94010142e0000e03156004982c4c10108074801200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 795389991 1250 795388741 795388747
    0xc0c14060705010e06010501080a060506071101030b191805012411070e060301140610080408040b0c0102030f01090c090302150f04030503040f1e0521030f0c1506031c05 74
    0x2554950071349550300501241e540081e070051100396480300503203920100001d800e0103c03600e000045004e5101d207803009000c1098a824a0300103034000d030002a0459400b41010340c51202d0321499180704001d0b8003421142c80480c3c0324130444942d05001d101c0c10b80780d40c02c03081d40c1d06c00c0c1c2d807601c01b08248c1c1c2d403102040300703220000010003c1584c0c140000c000904921803c0340042c5022402c0600710b0b0040402d55091038000014400d00b52513600302c1c10301d42c03000c178100178034103445500b042049030203075a2222803140d01c0041d140c0140d140c190051405010f016000194503600c5200d003601351600180440c1c00101076050070030152800030318684a07980318903005403512403140d40b803488950080e0410b58443c1d10002c0c01b0028110440c00d2800208100c040484102155540150000f1000e00c121449081034409009101c0c202c901906681c01d010b02c2226a942d81c142c13050f039802d40054007524401c0c001c018030320b9580340030000341600c03400000780a000d06840000c02c0d03c00b0510000e001208010f018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 795391241 1250 795389991 795389993
    0x12100504090b1519060f09080109120c0c1509031a0405030f0d0902090403020f060c040503030d020901300c02120322050a061508010b010c12020c0607120f0c0c140607 73
    0x1c0d036078500103001c05d9910f24030900b030342c04400341024405038455101c507071402e20b815000c1010910032180409d85d17854440040025414005020011394101180046000b032403d40015008024401101e108030021403171803440840c6031002e030100316409443d84d0002c0003041045d0007404010600340c034038814002000d000d2600801ea41c01821070301280560312072400015601410080954026041d560151130982030a011075240e0150000000807650040750f4111280c2c002c24950700c0440480d001d016180c007000c21400c80980035520044c43d414a4080c0034509584041506415072108a0841d80307580c54410380d41c45030f420b02d003034094040350b4001c0348000060018401228040d00a20000c140d071081455259614102988402c1c0d460789014903801940c0d030002811404035030802e90744584000c903c1c1c820381c100756200c64483c0d4480c40020b425010050500b0302240f00c6991981d48003010058150191100d400c5801d0141401e411200108030313038000c50818140702c00006d003804d410000e107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 795392491 1250 795391241 795391279
    0x30612010614180112030509130507031e090b130204060302030a0f021801031104110915280512040503041d0601030b010912031404080312100504090b15 67
    0x80341c0c200c2c6803800d51607a4102c8003031911001c5082a4145030900d00c050b545040c1541078099140e400040a0100119881c011541c48907081c0e4400a4003550500c440c1c0f411480c0200142010a08001855040c07064405901c985100748103401d580b01d10180e100345c4410b01c91034102c09101d0004c990042e100c6c0c4010005031405e204908a051040a0841c0f160314144100003110403001ca803507031003510140c010030100e41090813030400c0b001c09a40005401c00d280c400191184552401603410004050f050f02468543c40010032400c3c0c200700740c000e840d500c02c194a000311524614840300180d014000d000b9132225580007150024800d100b00c914080e95406030a11680782d5031410000000400d041005650300350240c01c8003001c09203030644d071460800820003c035009548014040004501c0f0400b00c0300404003c0340c000c0c01c07240d412030b0f49441e81d2038446030a000080780c0c42a005401c5007400952410039005594070180c0c012840c441d070b90356401e490042d800088410b40c0d80606d2000e030780782003481 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 795393741 1250 795392491 795392501
    0x1b09230a020c0f212505150c0903070906060c140c040f060806100803030705180a080d11010b0d060203040f0606030b0601020d020309030c040b15030a0b0a06031e0203061201 76
    0xf01070000340006807240704000100401d40c01043e0000d402c200000089a0000201500b5100e00104185205125820410f00c4c01c0e01441d0502d000090302014002c0e03094030340024001c00d0000310110340304281c4580c01c0701d043d111a40720341c4010032407507000000010580944035040380007820172602c28010030f10004082d501004070103503540d9902c1c5403c0c07120020900c2907582c0040d01e011104222840c102da090740d42d10000701072004005011548184005034a10f14603641a0010403031210141c90b4000e0340e8903441e000c500003000c40c401440d05004444180a05440590018015141000151140d20196100074411900710000c0f1a100c0d001803c80e00c81c80000e113009001142c90340c6080000613140041c14642c45003554000e102c41100c580d0000381c01484143c05a40220b14410f201c804558140e1020100c940204004001c20030810480c3e4040002440d0440ea00d81c50303e0750359842a07040350340004110703006070071100c490142015150011904984041c0002140c0c0070800c00301802c43d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 795394991 1250 795393741 795393763
    0x17010e01021222080f070c05011e11070509091510030c0608040c0801290618150421060b011b060e2505040b060324060d0204031b09230a020c 62
    0x1600462200103000d800c2078481e000c1c8c0030070300709140c04100c0610080b01900d166100c0030204122075882181c0f1001c213226010003460b01404440c11814804461512002482121000d900c0500001050168513151840c01c41c0d17040011481818100a01110018001041983c000021010004084800744140030b1000c80230200910305050341c00341c0b51351060445180e2072090070140204209001c89a1505151940454128206004081d80c0841d1405554050800f41c03150f0009294002d0111207030030816407082808001c401e459200545a4800c0b41040c0d424045015074402d0004d440d5900c45814080b120049442a03942d440d107030b030154400410103100c4144052000c0002e07042c00d004203240d00108a501c030382189801c40c1b284604100d120145034079000d6a4040340101c0d04e5600492b00782c03c240b8481595600e44a0030203070300201c00504640180202c031000010428410310840d8034030a0850100000c66548400d51001c1c00d4000c0c0001101c3c035800c1003d400e10708001c00c0302e80d00e25 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 795396241 1250 795394991 795395017
    0x50a020319170106020d0e0402160c0f0801050604020a0e040504060b0306010f0620150403170f0402030d1107120201090b0a0306051e030606040f0f0617010e0102122208 74
    0x840506032903042c40807040e8448000d5502c000c1c0a1814a40c00c80034221015100b0303240143c454645d43c42910315801c0b81d49000d0912400e400012400c030038a0440307041940c0785900280250b84400042c0422841034802460000f004400b600c4031901e042d0304065002401031601241b04002c080010717050060030380c060100400e01c00c40400010f500a00041c00c075180f45643d9020400c085540c10b42c90ba21401203046c04007020400080415010303055006202928249440b80c07840e040b941c00324000c6007507401b0381c03092041d219a107400300c5c480c50b4401c43c85a88100540031152801041041d020464042207041c00340c201404541c0180303210103003055180584d40031071040d2408083c0070600d03001020302450605001c200307060075200050060f030490003e03100011481140070385032004004018000c0045800e01000040810050b50554003001d07441000300142c2400c44c10180c201e01c24a0f0520705815441c1000800d080f0401c0e442e40d070a02518400c2241581c0d055a80c03601940c0421103907964 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 795397491 1250 795396241 795396257
    0x60c010f02030703151a0a020f070906030201090b090f1003140a020318160b0d02090d0c0501080a090c03110d140f0606040207150f061203030f0b030309060703050a020319 75
    0x1006a05004484d48612902c54407145103040c0714601e074020030007510701030110300c0000c7da418829108102d803009541d0503d003580e08180c1c5400c1e503440903000030b1005900086a2000105010f059142191000c05005140003d80c601001c14050440285400d0109040d5140646401544c0d0800303054464011032a00503641e00c0c0c21000281000c500151082141c0d00c1a40c1c0e000c04100c00000c09016581c03414100703138480c40c03176000400280c829a500c2d50340200c00e004142d07042107003402c11041654001d881d90032241d81c40b00700041c101d80c84c641d409441c032461140e0410109403404101040410702030460941d04210b07480708801c8140c0079014170202d03888010811242c5005004554001100320360544c40c1c8540394450004141d920b084400901c0c2e640c030b80320300304e0441580c0514000c02d0541c403940d100c081d181c10054020b05c4550713003050550b0f05240004a561802100312088000700402d61400c00105403802c80b01034201c0000101584010407011003203483c10b002c081803009160b612806 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 795398741 1250 795397491 795397501
    0xe0a0e061009060e040f1b0e150301060203030411240703140306130b031002030c0d0c080c070b060d1203020c0601090b030601060f05040b0301030f05010b0a0e010b07320d08040302100b060c010f0203 87
    0x8a002c800525041e08502b48010b1207900c0d80801100e81040d000900180d99146180001d0240010340180d125038500c4100c2440744030007c0c00141c00c43d240243c80340d110458100780f112580b480122485540034426003d000722103c8660700c602058280541158610b81600c0340b42c070101c0c0e1043d07a811034498804507005581c0f400501032841c1c500c03500e00d40120f907402d20901c41041405208001021400d003400014201d4940d1485c10040c0c54000c00064801034009402900075844041041414000c1e9000800c0d81d500350300411900c4100640205180e03881d00381c04882e0001c2d4103001c40f040110811000501c25847d40156020354001c82c1034082c0c13840c6619002e030844101150320303400b0f5981c0103420090352344071103001811070383c01001c1d40340c0e00c05941c504105880300b00c3c80d003881c2c0c8000d40c1070001ea4032a4a00402035840c07c000f02115040401c40005491401d400c41e030080c0182c0c007500711801851810782000c000c0c01030180030b003403d00c0d03075a414071402d5900003000075440c1c80e40442082 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 795399991 1250 795398741 795398749
    0x6050a06052d091c0f0606140d08120c0f040902090a090b090604240905010e07020601150e0d1202060f0a0c020a080a0e0a0e061009060e040f1b0e 64
    0x1008071500b540c9034000398500c18056115004030007030ba511030300821501445404080d4000c0d40700070340c8145901c0489007540b410000402e407038014291812044e281c0c424950412002e01500300e90401f40341d900b4000c170310100b102050001000d00140407001d020310080310701007002400c05000200d00168680076900240b160740350b41070380030501850030190091000d0b150080810b8009409076804214140d100314030304150030b118000750050314168500046c0320342065200c507045c3c5040109481c01c9464501c0d00f241e6690003805840480043d2002d0741903038901560705002d81c048080e02e5000905415201d592003001145460300142e04104200803001c1540140b00b980310751410410020307009041700083d9912040b14005090300342c00103106000300e004000220082c040209024056030f00c820085200c0c0d0003e541c80c9002e40000b55280c0c000f06e019141060950b1619540e440000c840741007000081c0c200340e014580c90a58400e4074440c03e00070004890140d249a031070303034461102d0f0709040c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 795401241 1250 795399991 795400027
    0x813080604030206010e0c0f0a030f0b15070210050a050a0f0e040203190606020f0d26090a0b060a0e063f070807060c080c030c0106061e02060103150f06050a0605 71
    0x600252003009454007851908090301c00303841c0d035407a0010304007444c0bc1c1c0c020300415074801044da00c2482e45641c0300d208031941e801040703047d200f0f0307485000024a10710305a900f4082e40c40440080b80017030010315103d9201c1e0f18100003002140c549613100e41031610100702264000d54085e106402d501007000d49402072400303190020006031004001c5000e10000c1d00e0303144c103810012032041026003404009049274440d10919040c034030400000d054206507010075900c4030120801c03511070000400160715803408000c604200c892401a5403044da80340c2c4100070700a550300700003168000c16028030180411940c00417043c3c425401c101020120384688806180444039402144180d1040c40d003446050b900007a200051a031051001e921078a85074061406c602410580f20396030340c41c0040010ba410761100e50405204031251800821002c4140201c2c2c0351103003400081c19464224148c40500e501560205507100501000080da01e038403240050b51905203076200d13000003103012481c3c0540040d01031035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 795402491 1250 795401241 795401251
    0x1a030417030a02191e181d01061205060f0d0203100f0b01140c120c03071b060e0603070914030106120503120f01080601030611043c080a0813080604030206010e 70
    0x2080b401d03c51081107001524085445c00d004000000000744801c5540d00764401c00340400d808100008070303c0c007030381070390750802441200300284100100d180c0301640c6200d418082e05005d00151440040b0009000a0400f0031008036010300ca2802d26101e80c1c0300500c204840c0c0803204101068608170b08000500c40008429401c654240c2001039800c40c000029000e40b001c3c00d5850510340350180c040d00942580541040600f56541d00700200b04003810700104902a41d056868088080301c4100034403426001c1220b602d00840c40b1907000303010910f404103411102040080002c03c5a07034480d09526100ea51903041143d05030700102c5c10401020b4800c41c0b83d0740c000c101d21000a080c0d0b140c90700712540c907007041c8000b1301030b140d89031a50740c0c2c19040402120007512000465140c14246078a2020040a4809890440e0441c414910103121100c0e4010000ca8101c000100803041e03407502c03880c1d12640076060945550207140c20001c3d1204050010354444d6029030041e007034661404072180951100109 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 795403741 1250 795402491 795402497
    0xd06140705090105040e090a0b0a2f030411060c07091e0c0c080c0307061d070e0c071407050d080d05070810060f020114091b0a1a030417030a0219 64
    0x402c40500366440402e440403120700c00381502003512400c0c0c81c1414400708040203030020742800e08001d02c120250b0441240713148094074518102c0c1d10b4481070400040c180c0e0b02c80405c80340400205012480071643c14600300401042e6515000201e000c1d0352034841140e103e44044c41c0c440d54444054841c20050040c5040d4400c8180205180050000d0992018401c001e0003100042111503901c1010001e44136110f07072180c0d0810601c3c560803181c0c0604129001c04101c2c900c1030304004103020349228000d47c02281d2000845040081c0307942d4040ea58540714180700c1851250882c0054550750b401d9089250306c1c050382d0410360714401d0302c1800c1b042d243c000303016209100f811401c3c0001078800d12008003ca40c414039040e000c0300308a89040b4054641d1200301c0d5800a81e120912104000104800140d521520a1300038041c580b902440300441a5100d0640e119500304103052043c513105004543c058454a291825401841d942050542080c0d1303038215602d42c0450704140640700202025407401a43c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 795404991 1250 795403741 795403747
    0x3090c0e0610081519080607110304154805191a0106110708150103060c0c0b0403091d060d0201030b0a030c17011803021005060d020d06140705 63
    0x150110360b642400840c0102005100c100107a1060011104588800700c02001591200601c00c5150200d50050082c04028001c03c1c010441150040d9040d04480101c5000755090520302060345d0391480510042d0070500109800300e8900901d40544001c0b0070501965480150340d00b0809400801440c4540701100c542c4000980040380300041d80c24414000c6008c0d003440660540740400344c0c0c00c200d24400c1800140c0200100b076071138101000d841c1d041030020480e150140d0700c3c0e40150f955000d020458a0203045140107101094207900118003640c12400c11040e220300d240c1e1440c0102a044905500240d150101030201030801040c240c070303051860806181e01e082203000512501d414541c002d0615648111281c00d507258002c084000307507006101442015503a0341e43c1074800401101f03000965181035209050100d411000c2c0c0308450b0150300408050181204d04002040c0c0031304042c0d4041e00c010500d000517515510003880c1d2034031a85000c64440f403280f04031402c80c040903142e201480018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 795406241 1250 795404991 795405001
    0x912091a0306220203070309020f040911240f18040606200705040905060604050a05010e011a0d0c0c030305070201061d0c070203120a021203010e01061d1003090c0e 72
    0x84050741e820800403950711859002c3c0d80d070400c00191035182e00d08400c074004410425503a4056100c001d0460085d10142c501c02c4031102080111564000d00900100c9541c4c58105682444030000e02c0540c0b00c101450010820740e21840071941050381841d0075640006103281101110010a241c01142510144091400c00310042c1c414095070100c9030882242d407120112045040000310010139011b8410411030600307042c21a01c921048502d140541c1c01e01c400706149560910805041b90a8034903280000d03400c0c0040e001a44c810341c040b00121380c00900c08158810801c0c8107100400c2d03150381710407030f403448907140c080c007030b10380013401c83c0c0a59241110410101c0038012141685070035401c104e00c80c651340d0118400440c0140315020b5014403d807000c0044140101005000c003030950740841d0b01c4290504001c0340d4500c8240210b0000125020041000034001e54445094030f43c451036000b400d00303010010981060030000f41ca030029803598600300900011950b0382c07014001c000d803a52a14030f09 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 795407491 1250 795406241 795406289
    0xf070b071202180d0c03120c02041d06071202070605010e040213141501020f0610051903021809460503091203041a03160e0306061210091209 62
    0xc81c102c40c0a1180700d1404c0040018404118019691017040702c40000e18480d8010102071103c10124041c030700d0b107100742d842204204400c03441c0950300401400d1658500c0b00c1115841000c50342d000155800384500c40c0000c0450003420b01800c10190301c07040900c0c140c0101f202c014410580303110742c58035089800000300c06183c0b9036540030382c003110002c071600e4078500100d02d88495201c1d501d2080c0a80307020b00c403d44111460368002c640c0d0850340281111b4400990203241c54251000079401069483da030826201d1464035030b5440403c25050b2042c4140790441400103159000d1071036810445281d01c135001c0024038514841007104185c48010340c0c0300075604d00e41c1e24480c407600c03948252000448400800d004100301c50142102580c1e110207880b01420b9000107404c00e4a882c20410201c0e900300e6080c0d03110f10406145180001c00404507030b155907050000750650b40030340324110b000b040c054000d805000d00034412a11300c5130018894005a140d8000d1100244c0e070056251030019440d8400c00c242 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 795408741 1250 795407491 795407527
    0x220c0302061b030301090902010f020f190f0b0f0402031b01050405120f030d0c08060105250204060b210c0c0a03030f09020a031212110708030901020f070b071202 71
    0x340c1520385a58038512000030b02c0082c000c080703000002c1e100000000c108100260043c070040c40c400e0300d0340240291a00010b0327854801d800390300709065120003e1300c00031034046ca40710384140340980055043c200450b21214401e0303400300c42c41481c1d140c182c0240030450608200460901035810750400702400c000000034940d11662092910810b411071920610000c2408402010080070b811079682d042c0703584801b0081d000d8200810041750410000a42550245c000c8502c65986008155903001410b102c4071224403001070181c1c1c0083d0f6502001c00c51150b1500284414203102d02020b441c00f081030f000e115503400c002c00b0480e954509000b070b5901c403c0d00190211601d641401c01092800c902e007000381c018420010041e500400d643c100100f1310030307402031900310010303a680c440b100d0581d02d401c0301091b2006115801500b140402c6400e01145101010350740100000001525001c0701c0301440714990008403060740d09940034018000d015800c21030101c80c40e901d808065003413001181c00c07030300c04007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 795409991 1250 795408741 795408743
    0xe0a0501030c050a180317121006141c05010305211206040f0f0c031e020a0e010f0c0507060c061404030212091306080114010e0603030316050c061f060c0b07030b0616050105220c03 79
    0x1e0b40101b2500c03c400ccc40c00b540785d0314012038003008000542c0d480c1800ca03030300d103201c4000321154020180f01c4135034a0740d0f030030441c0d010f0480c9060340e04240c2c41b01e4050100400c45081000005543c5420980203041c060044005031003055601140d0030f41b0744001785480702030001c00600f14030320410100107035581000900051020908024041c0c5115403400e03144207107036040080680c000c01e1000b085040d00070343d24031107550091a0400c0b15041d011390032120900c0c2a200680943e104d107180d852400300110007440524005000c9442ca00c0c43c07804800155003540e0050446a5106d08584c13403a240c155284500400c2d43d9980f121660400001003a2644409441580380080390001c00d02c2d464020800c60340004140401c8031494503003035980452242c81504004401c10b04920005030451017070104003040e580014290249072a0b5000075030040012038276458010b0018446184c0405900389005a000c2c0500004240c518004a201481000410350071040b07ca00c0200304000c1100d1440250540b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 795411241 1250 795409991 795410027
    0xf0e070e041a060a09020403030f0f1701030b0903040f180c05070807111f02060912120a0c02120d02040f0f03050c040506040b030d0e0a0501030c050a180317121006 72
    0x1d4403450f0208920701c0007608842d00140c0005400400c0540c00305001d0307607204181d59018001764460904403504803100c00714019181c2294014804a2025407a0350f8010006c00103c80c030742983d400310311205202d19400a0100c4100c2c000910a01815002d1013420b00e582d031400f1464104180d803110624003500c1400b400000e009410821350b600d400c0c00d50300f213801c500e030549010000d80060003503803500122038585403406405170b044203102c0c010054520964445964403582c1d540c1502c1640144641c0102204511030740d10540ca04906081c02003102c01124400541d85c2da04040f18030103820035582c000124851480010800b0400114660040349001c640108894880b140014082c14040361810703410b02841559003001504440001034000c416101400c1c0c0a030b55400540072211445c01c402c01260040103044055841445180a06030411247c0300055813031707448140324440201000108910001110b200c80f114507246035074880012841d622655050684c001c168001803011000c40b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 795412491 1250 795411241 795411293
    0xf11160806090d021c1d1c060e030328200a0212040f090b0414010f030c050607030806210304030b0a05130203070b0a03020903101b0206130807030c060f0e070e04 71
    0x710ba03044024500b2840c070001c1003400c2001c0d59a01c1f031510500b100340d0031542d8034601010000d1100003c02680e101d02c64100181c2c5801d08070844101d4040401c80390702000c690340f505040d4034810088100c1019000381d10510740c640c00c42c4040a403400c0c0e00c3c1c400c0004610000c3c03004206280c4510000000d6413500080816030341c40d503401083c0503050054035143c8440d00c28002048508400001008890082c408420100d40c0c0b00140700c140d1213025000340005442c04001043da040200c0c1c54034021101c142c0d02d15550881010700d41c250741207904100d1301c03030b1400e509101c0400040c1c06500d400810669003101d60450507030009540da58a4822009080300104081c541d2a000ba4107445000201406035081d504885d01d0341d50080a101400c50310503440c404103c80c40603c00903a1078842c800420071500401d01d1a2a03180b01900404001c6082212074030300314001980c1030045681214444002103903002401c0080d41c10041e05403c0400c10758900420800407500340c0c0c170310048460b8040d0030600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 795413741 1250 795412491 795412517
    0x160806060415110a210801050f0603040c08060a020a0905010807080f1506070501060503071a0d02071e0506040309090c02120f04030803040b010315020405010f11160806090d021c 78
    0x2240c2203903022100d00d13800740a0203481403140d0a841c4a03900c9161246a00a880081806036030440081c0102d47e040b0700c1141000c440307824248010350304203009030054034103640d5800c5c00914080e0308580c0c12107590303004103a40f100c4a8010000101401007400c0c100150302e000d060040c5020710041a441d0f0260000003c20390b444801104003495410103402d0719541d0129040c00c074082e214a1082134064418024001a001c0202d0b51081003000008219841e01c600c41440350081c4d04140d80c252402000242220003103003440d209407503058410320140185140a00340a8840d030b5131644141c10950802521203c0c0c15408140786402e41c00c201c40e4551120381c502034007001c600031500001c02910000041c0414400e1314030060741220311403030b00c240e40201c15403400700c243d0080e44516804031700b5040c03c0c0c024080c0940100003000d000301e400c8800103003101d211a80c05d08210b50145144e03801820500c07481d21000d0080700c00200807400180103848030103400810301036800004104101086403d82 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 795414991 1250 795413741 795413747
    0xf0612050c090a11040602010e070506040b0a080c0d060e07110610030f15050c0414060703051c14070c050f0102040e04150f02032e0819020a030c0e160806060415 71
    0x750254088505003505d40e0389590000e402010241010b003500d1080d0f050006a501d07000085806840460446a08142400c81c1c00e545540d0081c210720351441e014845a01c2c604001e12901c401440b0f0f0903081c46290a00c00d034044c22000d40350701c481600741c00120811604800501001e001c41e40d0285c0321043c40708640c1801401103180040101e801030620041c00308885041c0e010380300383d036060200c0d048140a90340803c0114460b8402c01400b003101070003903469030850310704809164080b081c00420540c49440300398100c50411507800001c00e900303200010602900b0031641c862008200d00031071801d4140740024100510040c8000c5c0026900000c48070280c4550b040000044401d1100f951a400c00c20008200e16180541992304883c0c03803c40600100c5050604c0d5049624043c09130a0b008801515668041000c11060f0b81000c10150004000784036980d01d40014500980365425504014002d00e0303070000399540d400100b1030317294140540341d0390790340444080b14134450300e407103400788000000c0e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 795416241 1250 795414991 795415001
    0x60f1003020c100c021203010302011706121204150e0609090403020f0a20040c08070503130f0f03110312060904030e19090e0708120a051c0f0612050c090a 68
    0x140c6031a01960100f4041400c00303420280c21001c007a000ea541c405a46800310405000900c03001c1c0c00201d0b03a40d44104000611804c203074006c1405040008480b80071001c0c28906280542e41001d10314000800704208883c01d007205030415032a1400303180700444400000d0b03585c020061070320300ca081901d0105d802c1500030050400f0009110069450305002070400b00314500c005210030301003441c200f00414892030541300e075a80313007491030301c40015503240c07000101c0b42500700420507082038860400e1003003c1451090700140b0305110344890402c0081a00e070003404002500c05401080e4814441c041c102d142d0319460540c0a4800c0d40e9161136075542d420116809000358040903080302d080301c04030700c001e02441c52240c00d0fa12200d03010b100a03118205c54a44d500224400c2410b2500800d4a1030ba40d0440740005044a400500d4404e00b0035006103c40140d4210745135061038002e03070780d03a40603203000312901903a00100741d070303069880400c48651149034480313040e918140d12403000f04d800a140e80070261300c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 795417491 1250 795416241 795416257
    0x911040b0303071a04050d030507081609090207050f0f030a2c090a0e0d0f0207050904020402070c0b0703020d0206060109260633031f0e0a1208070305060f100302 71
    0x1a5046040c800c51019480540964051b81c26004011280d60001c0c0207024041c0107181950781c0501660714043d5407402014803400c01c0d020401c00b543c000031509a50700180c04024018005803460280c60321480d40341c40f904210404580e00240000d21500740c0040005200881540351f5540700000070b103400c002c0c9580e119027150300203404401c4c001c102c1c2142d4171858427400c1d17034000c0762074007141c180c000c2e2400314101d00e00d00010781c0101001c0c066030403e01100ca810901c06403000d03007011619681e605002055421800344058007007440c40501d9410400d41000c00418000340069007404d100086c40c42c495070060382c3c0354090202201c0b40003d644c1d94604c80c4c40c2020710035038096040007555903000b07a02040b4444a01c4c40c3c00803500342e900c2e4a28071400ea12410040040c101201801114400e0746000e1010540345584c0720403c01841a007408000308161213030000103011800210082c1c03074050b000d000e040070985003008109541e25940d06009890004440c1030701042182d4008030042e02c0350b161 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 795418741 1250 795417491 795417503
    0xa0509061605061e07051e0c06040c0e040b0f060f0a080c0a090204082d01090507031a070f0e030a0609080405030105130818010306081c0f030911040b030307 69
    0x19080e07424100c80d088451041c0c8954141c3e40c040d11030044044441c0c84401100f0007060880d40030600c41c6018000401c4032801841c80e00390792a00c80307660051660030a8408050383d4010030108000c20036007805140280c408030b018a0345a043c42e032075403016400c2c001c1c80718068544500104d1604c0d62a04111006d480c401401941203c1d16a1a0140c0380d05415000900a0312440b0b40400d08071118001d5400344ca41c15001800702e0b01003001e040c992201640c228118107100718010030350b500c0c000c0c0180081e46006000900c50320b17203945082817035840c05800540c038030049001400b030394641c000003c2d011000a0324103212070b1110400040e00300510208000c03d802d1420084208000784040a013080f81c4044000f00020f035a18100111200b10b403010082c02020204281c40c0004c01001c141c07420100b040c0340000d580c4c1e44800e442440e000080280d0401300400020040d02950b00074020004c4503014a018454101e450741ca0910384c01c0d00d40e0704207220350307100c1c898500b5686040054030748050b00b0134 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 795419991 1250 795418741 795418747
    0xf05030c0a080c0f2803060e040f021503090102041809050c090c2704200a0302030901020d0507020f100e100f020f04031a06010c031b020117070e0306060909120a050906 74
    0x5e004410440d00a01d82e054105016001000741a40a442101d0807140c1d101405059980c44d640d0740c003400108103600300e034810307141d103101040d0034080e0303000d14441e00c580000140e4460030070203030181c0d190904c6070301075400c1d040c24194000140080b40021b2404400e80b0203001d151aa407091000f140100300b1040c1200101c1103d803503210641c02045402c505054900308611000714080c07004115100c40c660041c04010000415200c1c400e600850303200b00188001403c299081d0b40c501c003500c200795558001a40300035150b81c207140050021920745084000100720031005414141d0319944044c084a554039907900b081d90203940c0390340460b4035203055140202e545d10303120301d07051084030540c2c0a1035464104000010761154021900909419096150812212110200c409840c040ca80d01241003102011030015030201c441444d034005c0e0241e441d10000300c5107000c00d0510300f1500505080c4a40001400d0002c41d12020828644034481d1600080d600d40300c148080d100c1d0f01c101d4182c0d5070888800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 795421241 1250 795419991 795420007
    0x6050319050703061706040804120302030d1e1d1902180c0307080a140c070f0203060c030a1104050612130b090a061a010f080907050d05030403030f05030c0a080c0f 72
    0x3d0b0748150152000c8000d020b00003940a881d09580d50002c560084c03c40d501040180318a6250346000c44400e40f1a1044a184c040000411401d03940510100c030101c0843c180344c0d06141c4118098107a00a5040008009040400c0c3c40259540034040c0d20340c41d5100c144c80c152040d5200c8003e1070070fa02c40000960401814030001c0084181d0045400c100002d544070045036140155000341c01c404004a0344c7c05006444a035907850750380d072180800304c40a244070045000140c5092007824456045581c047d078032072514180c0c05080e10701003031094440d54400c00050000750b8481d41680c0e0060342d90411081580d60310b10040b031150001d204044e0800a000c410008440c500241c03020465120301420f0240d02c1c0c40160000b00780300703000c10050124606005070303916544500501f81d03001c1100f4040380c06071991280401c81d54807180400fa2440c0e01700090074424581c004000c85e181d81d1061070320310b28518004445164a0280319044d8080185400125150080c400c1c10380300031081b0591400d50b80c0d510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 795422491 1250 795421241 795421247
    0x1060308040e0f0108070302010e130c030f1b020a0b04141b031b0f1917030d060b0a090e070504030210020d020f24060d06021207020c0a050a060503190507 68
    0x305200324600358a03080e0004071102c0083d4241c03412142500c1c02010590b055500540d4040031050065821070526080d240e0320b01c0d981d00605d0301e07040d504d0f100001c141340b014024034140c821b58182c2411200040706690300140d800903400c60b050b90810581443c50303c0e01d06d000e60158441540601843c458080031501104004041040c10720003141159540920080e41c50882c00450940c56406650444034524608045e0006d102c01c035070112107452050780b15182c804000220b001c41c0d00103548081100e900c480001d116a5014000c0c1000703c80c140380b040c80d0000c2201d0350380c0c064003040415160200f4611802502a83d01540c1d00404130f0070b120f5203030f880095452442c0020900144203079a448901b011000c5440180c11921141d030010714001c04d604d20400c0c60015004980022007164560080303a03291000d008402c41101942825040040c402454001781c100741a11481c1c03610410807181da109180001141d102c0e040c4140c4039960340002040070003102c0c41d0b02221a080c5010810107071780c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 795423741 1250 795422491 795422497
    0x528030507060306050f0105090103090c081204030c090e071203031104241e030c0e1002011e0203090703140a0c08300d1d0f1c0201020a0801051003090501060308 71
    0x211030f50308110050b5101d0400c4640310b41c41241901040040014000c2940300c1c0d04040081030043c44801a410b03074405a03240b034000d040100c841c5000b4042800d004108800520030024480d148092000d08801d02c80c0940f0b0700414811020221440011802058001e80180920200d400d40058445075125541e01000c50748145055000403042d000c8c10f08103010300002c600d0807030f00070b421302d04103189a4000d400408980c4080014440c0c940400c960560f20030001d01042d038107a600214040603100c0c501792120700b1821200c10024018001c0014005000440d102125009480c030802030b000000c0c607505060015102600010f5006008a00507000160744010304044c0d5009101120701c88000110381900e1509580f0b0302d40c420803400351000d441e80c018002d01a4040000900c2440d884021403030540d0450002c9000e030046101d1035221041e44015031600c034140e000a615040080304000e103075150500640f4483c44042c50841a2503100340d000c0d40b04c069001008000050312400c110030290 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 795424991 1250 795423741 795423749
    0x1611120f03250903020934090f0e040305130503160509070504030201120b0604050d05010b01080c030708161206080313120b040f08070803150a080d090528030507 71
    0x81d8200c0d44540500150500400704071003c0d41c40c40c1d0864119400c11007401005040046036030416001020070041415005034503440074461181110342011000d4264202c07640002200701c0c440c0c000f000702c0700b4089800c0781e11551502c0c04c01e0341d4002d07a01131601c1070800c43e009940c1510070030200320984410303417409405484048400e01001c4c0e80d0507008444030700c907a01000740040d0140400c40d100001c25004400ca0480050140782410384a20101d40a100107560556060391140c0c1924401d5030081e07034107900021120080743c0707076191000000c0c01601020304000c0a0039511003030b070000107100309580c201d80c0140c001c0034000c096a4002d515501c1c0c100404130984403041c00000181d40c40410080d00095500c07041544081d911502c548001010007002501c00c8502000484e0008003980c00451141c00082203242c040d02d03100b414402084800c0e0401010b5506c03580c07030140980d40124618080303420445000111071540303a00e000c00d400304003100d02207040101c0c00210422601080c110255 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 795426241 1250 795424991 795425011
    0x220507181502010e010e030d09020301231e01050618030f0f0706080c0c070e040510230a1e091407170f01020f0406140c0604030e04141611120f03 64
    0x20000044c101c1c0c0c200d40d00480b518050b50301c00c00182150389025045010b01a00050000940c182d141e80540340001031403440d0410791701c5201c100b0981c1c0010001e002d9216107404c0c0d2007001503040801040d9035202d0109120690301001c500c1c6038003564200001c941040411044e2a51107003100c0b000c42e03491110380141d502007130b01c00e000506c02d1031504040e00c1d61303d1240b400a003511403070001e0b0066007400141c42034802c0d0103198886c540c11038840c00b400f10894824100303103058204c038211406500b100070300301d40d201701e0030305c034074101480c0035004c0e074042010100300c0009908000c1d1031b000d140025014500d207280c0c01034440018440f04506070307000219242d0300540301018090f0340e41c1404c074860441c50f40000b80d0240000e00090f48150000340c0e40c000a9030009252050341c45110b8507000d011601103001456415030101c01e03003064001c02002c102c20f00d0503110a401c1510340902100d02c200026800c0080300d824400103120b0802c282003440c40c040c0031155442a4498280c4100d0380100e6161810b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 795427491 1250 795426241 795426251
    0x308072415240c051e0d0f0206070e1003091a0609160519030603061d3f1204030c02090601081e040309080d05070b0622050718150201 59
    0x4240c1e14000a100c5071200d1140400d20641400c1910b8880b280c031002d85017440b44c03180c60321245d80515404450200200c3c02800c400c40b40d803200422200da90000081150072020a210145402404880e80c8803400c6131a915054501c002c101c0c01000803900180c1b1780d01d0302088050b548003206290501400c0182daa82c0e81660b1b8204d0105502c0030704444ca81d001500802c5110055446284261139190581c40c0c0421142c0d070702c1c0c5608056842c0440c01032400040c84074070030b248180400c018061030007916101e12529a00b8100c4000c0790070400111000904262194580308005d40b0444482d03040c1604409202d04050500403d1564882d0080703025503002804161558001d9080b0b80c412103072403180c500c0c070f1052140c690100400190080301802000d83e00420f440106100101e07624a0030b0343c525440d0307916400c0c02c0c1c3c2d5602001c0d082d1030003024024285951248080f0103589030004540001c9950b407a540c208941507180d2091714a46009086008642e0b840741d4100000401030341d40c001d00c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 795428741 1250 795427491 795427499
    0x6060509120601030807031101090215030a05070201060b0f03220f050601090b09150a050604271401030201080c0d0c09080d3f02030f07110303060a0308072415 70
    0x2642e40c0b400e000103480d5081c00e00114001900c02d60051460a400383d001050b595074030741c0480c900c0702c140000c0901c00c96003c03080100102c0310317205403540100284020310001c0e10b080d80b001854880d002e502ea081e5071000000400441300c284d0003500924883d5051001c4041c2401e03c07141c106401e110407200c900400000142064080c0034407100d000004113041e01c2070301c07060040450050108102e6400480040e00012a59030b540b015100903c0031a542c07080003040710f0309100300142c0140c180301c0720381d140c441c05020404400c00c1e0141907a80c2030030a807500b6282c01c0c1a0080c0c501507c020070b0012070802440501c1b1540c08401c1c0b00480d0161400c031924104103140540d501240701c6582500101110b004050351750100e014160050f804886140e0b0140025174518141d82c000c40d01d07651007010400500880b01d0b805610b0407900b01655014605504200300051000b03c1140f001604d031500200c1c0c000140003d0900d103041048a2006000e074031190706c0c181d20090042103000001003162080002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 795429991 1250 795428741 795428743
    0x1030903091806290d02031e0708011a0c06040b070c0f08120a02090f040b040b030a060c17090d0e01120f050a0b030a031e020705030d08010305120a0e01140d0606050912 74
    0x13840ca0300700c0341d4045081585c800d2100000790030003400d6031368401c036844540b4000100801d0450182ca50381e5038007160b5606003e00c0c003010805021035500c130094100310100900070040b0340e160304075901038030b03002058607446000c583c52000203102902d44008820a0000c0002c020014003240d41c12010340d011603942c15944800301e00852020035002000b0103000241c91600b40e201c42070f034040081001644403080030200c5e00c0d018140c032007222030550303d0900114040d00507244456041000e074036001d0310b01d020000c0c1074549071821031700000c0c00500844c1070a140c0c014045c4442e0b10802150030080300035080e0509001e0b100035514100301c90328001d0141124200465242e00d5690035807184102003050781e50f040c060040d00e4101c50114017800902003031a0b80c0500c80b4050910142e600c865665045080442c2860304040700c1000c03581082286440540d00604100381c0c4103400d00b445107902500c031004030954407a4000c0e8400840c58400b01117080c540140140100c00750584102e00c02d090089419 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 795431241 1250 795429991 795430049
    0x40e070e0109050f280e04170307050a08040c05150d1a01171008030c060421140d0905010e1b0a14090a0603020d083601030903091806 59
    0x1c590402100d1103504d01070301301741856400c5014100f801152900040000e00300391941900664000140001408203100404480018611840710880e20714181403001401c41e124074551b840600003030000113000c4c01b508810b850700404000d001c040303540c0040e0007a01c2403030344072201c60090b00c0e2400f4004980d259243c00d4590100d4410f0f19104010b6103007038030640b40c03030300000d00400030011100008100018180050650304580f41c004040c0c9041519001c46d40348500d40943d4640010b1500c00d940d2154024100c0070722080b810358260355249440030700405418680c001074255803e0001a9240550003d1040ca40c180e0101448503c15840010411b07000d0492062200d0555500b401900d03921b0074200345500080034900004540d58dda0707000c50503080343d4107000d6829400100e40d8400c00e10080d080003000300c1d10200110304102c40c4050980003200041c080504040d40c0b184075504041c040c030002c0e0b01400d2140014840f00d0098041d00c0e01900050060b9040403042e64000000c81c14003580c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 795432491 1250 795431241 795431249
    0x1a2107091a040303020d23090d050d0c03080c0717070812070f12090507060513030506090313092f12040803041a0f01060309062c0717120705070308040e070e0109 71
    0x124401c147c7c6010154003564019004541d0701c0340a80e1003410020b4003c200c501c10010050312011100b51480c00c02900c0007030003d2007040c1d061410461000090020010019800200c2840350349400b000c0c02e02045a00840040c5802524a10148071021380c21003e41802501c0f55a29008901c06a101c5e900655410210003132903503000d50300c280b05207801030000e0000700c00184201d0007119130383d0725510300d030042c1592100c549800019440d07029040003e10320000d403680b20000c0c8424240822022a4007202c0040c290b420700c0604400800e80d401002242c0210384122200b8400c0d040034144001c02c0d41c42a84c0490b00103188012010641701110800c0c1d00c030303c00c040c10300d900c0780c0e10b029015406003003000e4080b07400a0b621425240201c0d2105c00031070780341906402000c02d00940140692405102c4d801c05240b0440031070364410000d0f000501c42e8224a24901003a4440c0d2080c42c2c8145410f8158000038560701d00840c0200d9040c0d046140703288600402d41d030341107005105000548841400340a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 795433741 1250 795432491 795432527
    0x30c0303012904090c031a03060f040c080706121b1704081c0c030e010b060924030c0a0f17010504051509101a2107091a040303020d 58
    0x20040101000e064010034a01c0c15400c00c220b6000c080a950700481e074081e4100c80c07407160ba21801c0021460b0700d441034070416614048442c40c460344a40001f659164001c140b10007107601440050200303c00480e4440c0107000031412600d80d10740b01d18014024100e480405201145008003c09090312151100e0002d0460750300c80e0f03400d65100c0c10b543d00e0b01c450018415141c0d46420001c420301c450400c40e1402c0022407200002813000780201004080e0382c40350304900c030300e681443d140c0c110a640b103404407048204c04542e00d01050317040e0004802d9540c62416405c08000001c070400108070f18940c01400c0314644c558070380c010340c152200141c51004d01020704071240d60b080d40c01030099007080e03803200e40c0103185254100c040da84034000103403000c00203d8903210603040230082004a80c0366001404200d030307402c81c0f4003414007103049240415070b00003546c00e441c00241c40d004140c030b240c01100e11401814095000074010102e10507080c0385580a8030088005100740c051141e5018415a0041ca1a880c100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 795434991 1250 795433741 795433747
    0x31005040b010303110c030a140c0102010c1202090a0312090501110a080306060304060b040912110319030207020a09050c1c0519020c010b2101060608040804060c0804090509061503030c03 82
    0x52021121000c042d0514011071141b200402c95540e0308000452040c0d01c10701004030601c0102e0700c098203001c5400d400c04d041d681045800f142d0660456a020590444510b00603120f004800014034550141c0d0f0002d0030580c0e000704800da085074465108815220203803100610100c081d85200d1b52b0799518040500026420701c040b072064a4200011038200e0b010300c03804201e03505c08200050440b202c00604840030716000005072501900300d4042079842c0d400d54003560400e0441203658180c40d4100c12560101070303002032844110b513640303000e81d009440034400030011490843e5038480c003507001840e01c050b11180d45803030203120343c1e80b03000d05031081d1008502105250316601441019401c0200440c0e01552541840d24207619206e10401e40500da41401d00c01000d04183c0e600e0841e011600081c1c00c001c0351800b0400410031600840342103d034a0304d00100320303a0703160030942c009000e0341e0088030101d82014248038501c007001a0f82c0d40074140c04803d400d12220b006003015503074420311860350b10b550824 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 795436241 1250 795434991 795434993
    0x515090c070c0306020d060302060c01050402030d0309050601030f020303040e160e0a0605090904080f07050610080a030512070912030203070b060f0f04050907050402030702030c06010e0c2209020d0b031005040b0103 94
    0x2500940080d4180106c0404c03825120743c005621a000449080d00d269035a20400095180130000300c6021802c9003810864030600b92502c1d52100780c1400041c004190513403111085480030001c98004005a4040003484d04000c20000407807800281840c000800302506414203103800c49255080302c1c1e4640b00d0901d0411003000784200303a03400038000c2e95418414002c02c46a070070001e0041071401d01c100d010b0003891401102c40a0500445d800108031540b002c2010703c006504542110a0441c1208882d0b00960399940110707000075840d0844030240c15449480010142c0000141990347d1095208460710360f60001030203c9251249681a440451507003404001c0c14a980310300e41082c0d800d0180c508803070b10390010405980c0250703084001a8000200c0000e242800d0241d20302410b4464041d07221030401d580c0b03640490059581050039490340302c040040002c50541000001c1c1101036080d0b4865a09003420402018010885800790140c01c1086a10070950b00c280340c0b05a0748007c2d951004d03429 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 795437491 1250 795436241 795436253
    0x501020622060e010c090303031a090c130504090c03150b030303070513121406011415090f0d140706030204030f0b060303160501020d0b0118060e03030d0515090c070c03 74
    0x70140240c40301591034003800c012110a004905416000303842e000c0c805850b43c82e00404036029012500f0302c2202000401c490ba40c0c509603050703040098410039a881d2b0100c621091580c540307a50001c0d620a00d8641100e0400000c080f0350001c4a0140d000b860000302d0280e83d0405032004400d0b05030749a0800c200161846009a014000d80540210300304006034403441103c2c2c105901f02e0701070b5801060095112132412040211074058a0b188400103010500c040104808401c00c61040910010214080406071a8842da001c00c002c0d0082076003440388120304094650400c0c100e180f190354082c209003c64403e000b8001c40301200d5002c94100641902074a031612000001f4113400c4e4180801c0005073f100c00404c4444040081c0031b9000140d8418561000e44102d95183c8042c0e41481591500c08071110080fa4100d000c54015080c0841ca05124000090540c46510b1200e031000340f5040c2484460703002046582080141a20448801e80f51150030028a0080c010018101c0c04115014070001d90 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 795438741 1250 795437491 795437551
    0x51b07050705100c0c0e18030c07030201080a0e03071a070207030203030405040c030605030a110118180e120c1b0904080711131a040c03061a09060712110705010206 72
    0x260f81d2515125540c0165a43c030815001a071000250010007403d21849039000864a0007403883d84000350310b032052100c502922007040c1d12000c2d061105c000e000401010140d0000c8600c0708444060307aa031001146009804000c66024001d080d62071040041c113802c0c00050400c060baa00203000310305151405007003001604403051b09008040c0c07110340000c2e054404000d890002d0340304000c0d83c0f9040ea0624001820740010282021005192443c20030001d1103142c049070750700740d4000d4081007e2015110380d5180620100402002180008800312884408039a07a9600c01108171040a041421401c020704402c00f5140a40742d40b50030414940000d5801c1d01c06428102c000d0150b107410380b058a030700801c99000c400c003c00320007040c0b818414540340c241302d14450f9011904040180b46c1c100403034940c1c0307168034040781c4241b1480050244115540c14059454041e8403900c3d08070781c5041c0084c0184820b40061500c5000d105e20301c0c000c51f1940c008a04603100c2c2c2c0d81c2c8003010041c481d64403005031401e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 795439991 1250 795438741 795438769
    0xb03040818060c1209210a140705091602010b191404060b0a18051507030e09160c050705090a0c0f0f020604020411121006020c041116080d0c03051b07050705 69
    0x1d00070b0b1011400940f40c00d02c2030040d031140300003407c04c540c4030b410007954001c2000e100c07060b55009458280090f81d580c1c080d039a0020882a214480c0b0b1100d00320603801803503843d8840e90321400e41030303614814811011942c426038076119112440c00c5026001c0c40191815401030f0314400c14207128041030280710300a0274002c102d10304c10034013500e80e071400400e1402580c026402044100004c155003850380000359400e50010540b01d40340c051030031601c0c003141118840707082810004a440d0b08018002c00300240c001178040240070390140e00386140c080b401061826401404503900c00481d5907468051010312031402000c2d0007411596886500b0040100802440040340d10002d2012907494400070350107602c244445801885024201000a840e103040000e000344038500b40594170004101c0d59003a611074200f9403110414038605481c0803011401140b1500301c0042c50840c42c42d0040741d040e0000f40c01401d11a56001c440040340c202600148120000504960701550040100d82810014180c001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 795441241 1250 795439991 795439999
    0x2404050a050d380703050708060f09010501230d021918050402090a0e130314041a0a0306080a200f1f0e03070303081501230a03060b03040818060c1209 66
    0xf15a0420384109410a8aa001c006a50703102089480381d00201032640102c0100d5401c0d0282205070000b400d420014090795040100c120f4074108000c452a08510284400c5201c058980c04172000c860300a401c480401c81030117148910140b240c50090042e281c95400080386000258144824400a54000400305800601011000890305010040b05010310707482d044040300390031103040c010220340300c1000543c68900100f004008030070a0501d889105000f000e64075850b415224420b4004203a154072020890041c2d8051004124a0b00c85000100c00040040b45000f02203905202001c8000e80a99801c82889222050003036400d405e05182d1195a1410030140c811882c02700b810b008080e80100c003c82d40c01000d0206104005204070483c000c00c0c82c02c9081515a04800194103001c01c2e0300d1070b03e102001401e034140d20301c039411690180044541d1241e607030419150040c1142d11060285c13040300c1e6170350301011a51924200301c40003425070600030300310002440f1014803181c1c44485200c1c2e00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 795442491 1250 795441241 795441323
    0x50c180c250b010914240f0315011e0602030313030c05210903101422050106030c090e0703080405130e150609070f08152404050a050d 59
    0x1807036160b00c0601a20541c80045101c91000201c4032180b480a0002400322110f080680001400020515100300c0101c132040103140014010904104800300c2c0c9080c0c10180c440081002c040d01c0e80d0004c8031820100c5880c00c0960fa17240200d850703010640304070711032501c405900c40109200302403500c2d206014a00740d800120392054182220519100c1e070b4a0305040214843c0924a0144040f00b403c4d80d1207002804401c40d003206070112054010211459030620049400b907034299041c1006000307500100030400b554903405e020030380e15075030722820f109981002070203c5111030204202c0122980014214101402c2408004080204804854889580e00d6840507080400c000309900c2002c95012061503046ca0010b002444c0801051002448003a131b000f0300d4030300d85c0711032005e506c10f80c402003004901410304001444040700440004124451140c0f80e42c4a015076001030085070307421141180080ea0710014071030440704405000c2c207850079001c2c02403040701c0d0740842c000c0c2c0c642c642c01144c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 795443741 1250 795442491 795442493
    0x7030507020c091f06090f0605070b010918050a1104111201090c030b03070e090123040611091305010e090a1a2206050604050105060403120f1803050c180c25 69
    0x4c00c0c00312a80030400280d20341404000725041400f4842c081c00d114a00649010b9054965818190040c4038004901e46c0c0d4503118a1103211080358600304d180d00c130099415200d11405d1030703d0010703c4079103810320039403a014503078911f4138245003150000540c11001101c160700e400c0382c0348003d04800c9004e1040c50f454082c1000c0d10f81d0180f010038080c00103164202100d040294050b42100d21a407412441d900c40081140100c2d982c810000780d006a1004010846464180d01200c06010342d4145a41210396680c0c2c8072200b0b9425001030741a50401c10550143e607450a114035524004076402a140d890740d01c040b82518000d418040340d0103410702c0c10f00d504d005000b100040302000f9070003095507640d681d5418080d8074a050b00a050050204031542d9042034103544130003010042d0b0f200b4420505c1440c10a5145040c0200320f030b00c440509040c10442e4840c2e032401c03c0c0e9150700303814444074403550200c0415000030500c10000c500407550001100c2c1041e1036070801c20401101c8030501001032540c41c40b250 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 795444991 1250 795443741 795443791
    0x20a0f02010e2805090910020f040308360d0605040206160c1701090804050d11030d022b0c0807030504080607030617010b03060a110f04150807030507020c09 69
    0x61004204880e1046180d040780d0703003d190381c903e60b0f00312a1080c4036550030b0003a42d00001441174101c0880072001641d4085204a00d6968400c81c0d100600c01000800c4049400c2d04050301a00c2c00001940e060442280c02e030030070040c150010468a0780b01e880108a4408140c4581c81a5440742c4051300303030f070724108801403c041444140a0704450f40c002c10901480b200103001801d5910300094130090040058035982d0440714002d90041a000d180030a010780203014008000e601442000760945000480c9442c000351607040c0e1044400c3d20b4000c0d00c10705560380410b1454007410308072603a01c020702d019065540030200c1d03001e8001501000f40611001c650b414003403251902500491b01d00140480c50030f18100142c0e0304414200895034903040d10301000c2c3d10041034840e4843c0000e0f000041c001c1201240c05da050143c61400e901c40305000c0380200716035108200a4003006010346030b0400665540d40700f142941d104444038401038000c200d42d0032103820700071002c6421102c80340300e2442a202e00c07174940c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 795446241 1250 795444991 795445009
    0x1d0303090102030414120a1b02041e06140d080a120213050a06050711120709020705060f0c04272d11092d1008061302040501020a0f02010e 61
    0x2400c8a650700006000402c03050102c1a2801000d140240c050804442c0c20b014444c041c1d1040c0c01c040c450410140c400e14a00710720104403055004208115100714040c441c400441da89007407120740c9180803008142d0084038505074240d44002030001840901d2507a941500790088040d42041c8003000c90180380360301c8107001a1501d85043c1001c4103056140008000281c0c1050303000d001480002c000b11404600e00c0c00c12442d5100060310503008aa44560a051510400b5400b00710014400308204042040c041841030103091248058030f116101e144081069214500c20b107948600c0040c001110b0240312002110906640b90000032a81c0303482d2146014803031795081c2000d04401e0552040300d40e513414031500407024528a003445c10088000c01080520440005e401d82041420400e4420341d4840a04030308031900c0074040c803c285c01e10100103001c0c072100792000c5204414450415640c0c528610075a0210b683c142d000300503032a03850700c03080c0d000d03502c40505031f0402c030211140350020745580c452 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 795447491 1250 795446241 795446251
    0x70623010e0901050f091005040c0902040801020423030a030c020d0804060f0810060c030507020301020706060b0408071e051c0606230409050d1d0a0f0806100b0d1d0303 74
    0x3040451074074040b243d084030340080c0800403681082c2c0500c0030b02c17a00040d4414000c1088000001c0c1c540340c03820665585603050344520102400054041210901074000c2c00032100c2c0e02440300e0008448918000b00c220b40c2c40c159640640c4040340c2c2c003001c00d12410300400c0c83da0000d08009400e9500c0d490302c0040d984a07400940205111216080d0081d82c403902450f8007820449103d4a40e81c24440e0040c20b00d0701e0903d0140c1000070100320001075540030740c12a0b403642e6105004228440e5104031a4506070040c4c41000218011800f0020302e2150032110007200c000b14482c5841c540b0300300000c21a9145a81c03141845a0301d141f0089070002d1410312410010346804d251143c014150100309004c8600404031881c01241000c500340d00042e00040d11541e01d030010708000200e0b05095244c000d244640c1c07440a03031700240382c0e1000250036031602036010603680000203948050742c0f0005a45040403040c410f011803a8820028044a40030710f612001095500f54403403d01124145105c80c0f958000fa20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 795448741 1250 795447491 795447509
    0xa0c0203010204060806130908030a200705010902091303091a0c011e0e0c0a0e092b080c0306031018050a080441010c08071209081207062301 62
    0x5c1401750354501300383c5c0c000000e00c01c40f005100d0041c06031f407404482d0002400d10400710ba03c0d50024892131f0204110600a0000e400d00c0603100e0b4000d041c29400b030300d08254280d000710706007004030f0340c090542a1159481c40d0103481f00e071029403404011480000300f0041510001009000300f8407408000c0c0a048214905980401d00c4143c0d87c146080c111880300c50f048903581e2082c1002c10050321480300f0102160a5400050095560f040902c0d04025544280c100c08000700705c501160310140c085142c21020840d9100c49143c0e55400c403000081c0700555280341e05620110000803003400d16088030380005000e04080c1c9501040e80d540c503140424206c0200c1c0c8014000c902408208000e81007001c0800c0d98a2007025940b201c202e104010703103404144000d9103002030729241c00c42d0740194a42d40107141d000350205e40d6003030a42403c803080303000116183c0c00202036200000e01c200000404003ca40c180c4510a40350403800d51300c4c9002841034070340f1400b0310090410801d070b4480b2450740703580c02005181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 795449991 1250 795448741 795448757
    0xc0908010501060c03091503020c1204030317060906121e06090c0405060a0308070501290a0905010501051b0f0d0c1716080a11031306030b0d03140a0c020301020406 72
    0x410850030340e10141c200700100004148141c012a41c0802c1c130008440d4000001221502c01c00e0303003203010b031050300708004062041c10781481c0d10441110050040b03038001e0b6141d069420100240204d20320054602a0f442120403000c60800d26209825481062540017212800a00d104140c0d103d007440a4200c609500042c0411241c2142840984c0c0b0301d440c1180c04019503d069400191054201c4c0000b511010011401104111095005011011112895200b207505071141c00990308442441c44c0e001e05140000000d0300c2c02140a00c81c181d52058551070309200e0300070301c000c09061a80c00344544500c1100c10a030340f50312040c810b00e01410410764400d01001070074100340100180c0c2116100003040d040050304102c00c15030401010140c0d0081c845950b860510100300c1d0303817500b041280b00080c0800250084c041e00c80901c05000c56102e80c17003d201001450041280f4a0004d071005030110700c10703070000550490030f00020084603189084c85d5125030340320340100f42247c1141d0810340c0070070520 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 795451241 1250 795449991 795449999
    0x15010e0319021305041e111302030403201e0712030903020306010b0a090308090d05010507030506040f02040b0706020c0a17180d0c0317090d0b06040b011d220c09 71
    0x6040039075140030000c0c00504c041c4c24550b460410034080c10800c0c02032000e4240420003081503070460010304020041000010700201d0844000075802074804401050302d52421400c9006240720320320300c1c2c9001001401080f41c1c140414120f44420704c11506286c0102140412180350403150440c0340c6010707507070b03254520f41148141441c00b82c041e000848005800d1002c1c92a0070f80c800c00f018107032580700e10741da511002407602045d07440740c4c2104010800c4d400c050400000a5150307201c01d205032400ca80a024032400a4400012031040b80038000c1d03001c5c400c01102011820b95002000d403003078440c08580c0054540d0700c0e90030416030514100d485030300c1e00040c0d894440c000d401d4906007800c0304803210300506109503143e030006242c40c8002401841c02007500c0468842000c155030406001803d24411a0410b142041e818001100d41c00d205515081c0b20080c9544141070290300c6064407111000c02c40100303404c214000c00c01440400b40c02441c1c01841d1140c1246010340d6603405959204c1007070321820 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 795452491 1250 795451241 795451249
    0xc01060512070f05102d02070522020304080906070f0c170c1504171018020d0b0405120703020105070e0306090a030318050d020a060501060e0915010e031902 69
    0x442922100c1a8000344040c80002888000001124005ca40403820610403180a484038110740100044101c00d1105070310300c030180c1d0402da41a4a900360309070b406864131002003060341c1000a80d03c152041c87d54084c18480001a80216080b600400b0620304040c0c40c0400a8a5503000e00d104803031002e0341c80000b2040003d05101c1d00040c3c114082c084200242c4d01c045559204101d4211510074483e0034507054420702d80300e04076006002a002c0e032166032800d159402c1e03951503059941102c460310340580c410100035900521608141d0042081c003d03018140ca44411a140142040d10b50f8099140d000d2030394100403000b055886d22940002c41c1c14503141c10050322107003142c840c850180d00081d003080507a00300482c170701444560500740083d1206a0400301c0c510440c1015006140b0b20030130321401d5139142c0005582c5100b070b10a0346c00f03021907a00c03150100c990030303000510281c00ca007510300485c1010544c25408600305030189890302e40300e004280068a0141c058200100c41c80c0c01a00b01015410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 795453741 1250 795452491 795452509
    0xa0c1506080a11220203060d0204060f0519060c1407082a0102010e03191107120c0f0501050f0901051309050105030f060f0f070c05010516030501080a0f0b060105040b0c010605 77
    0x2200300c40c042c100780500d124011004e000020311012080c0d0010000d41d080d03540c010719410311a0003070400c00c01300740c90700b6660f21401000d009103403242194049041d0002c800c080d83c101910705d0360340c030070b03082d20701c01daa030700d02d1103004100d801106005501c40440d039280b08010365403211284842102d00c103c10340d2084170741d82005008030b83c11641401d8003440303940d00000480e0900240160418501494020111280c000356401c0302c3d007902400303100181d544515408070b10b009010f2500448215914980c1c0a104040c51060034080358050107940203002e04d078006400d40103811304100c0d203094002899005281500c2e049420616518401482103007000c010b8010b5019091008040c1402c01c1e4002c0035200900610031401141e50000150750f0510414080b184581d10a0090007a401c100413800d40700c8801c09401400249010000600c11200060301007049400124034940c0c903046442d80c4034055401080380e4148681000300042608d203403401810b201c1b621100003e41d06041c0420030142c86 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 795454991 1250 795453741 795453773
    0x807051b0d0f0302190509030f10050a050906100302130605090a2403031b110603043f030c05090a0b0304020a141c02010c02060a020c03060c0f0a0c1506080a 69
    0x240c0b0602c80010b42d2100400102101708103410629241c0040100091800c0c1004e040c000d4180100405003282c025103070001c900481ca5050148026501d0840d4240d952604031001c16080c464a2170030405400d014030381d080412548140890016162804154071304001d40c0c02d1b61405640c0c10b5102e001e00d0ba9025580942616036089141c81403840d01e000f495000111803c00c002e00626881400f040ba070f00c0f40c1e0300030201010b8103150322403034142400d6aa5029468281440b5000f40c0710652210844611304a5041c08003180c03143c0c25070040300c0480040c0300108031041032207010410510380d41d94004040700284024000f4556900c4c01d403040c00407520580c2d000c0c0075001004071015156a6645020782c81450449103007000081840c0012549240f00003c040d410002c0040ca802c9120303070102d81da410b0f10100f9800c8400039116000d83e01854455441d04103080c000034400030403900c0c8100c400c03c110b01d0050440b1818111500d03000c00c1210211b51005106500040d0b424041100ca244244900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 795456241 1250 795454991 795454997
    0x30a0507140403021302040e101404020403030f0c051501080a0c08010b030a0212150a1b0804150e07050916080c04030c0501030902120f0f0c0409050d0807051b0d0f 72
    0x40300d81c00340c450703107140100c1c04024441e50841501c20083c007081d505460041c4425540c000e414101002e03101d4450f42c4c01c1c000d482c8622a14251074803241414021181200c4e0705680b210741000c1c1c01c08040303681d6402000115603d01034420104222a044c40241d40070382a103002401d2080110f1802b10130007845580010b0745a41805144a16580e020441c3e00e4a10340544100c900b00904498003402c01025214202c1e0319841c10702488101d120a6000b100d955107160300c0b4195581381080140c0781080204c8004106070032240710f031010264140c10095070000f030007040710306442d1078100043c52040101d50303800b40421050103001003142e02950315034006c00000381c19441c26080d5151056107803030b18041d4506140c1c40301c08071000c54a418000e803224611780010b842c91411000d080d00d446804003030b042c1c125889501540c5110f40f4141c40744107002a030010060a240700f024809448000c03000341540b007804018403c004410100141c4032000051030320184ca075400340300c0c90282c00d01d20311f130980c8410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 795457491 1250 795456241 795456257
    0x6031515030f02190f120605330604090207060e01061e1412010e0d0e010314150d0b01061e050c030d0e0304080a08121602030a080a090f08030a0507 65
    0x2c03441d94440052000d405850303040344140040c44005402e10346038041075611080440000c1c00c81d01d055541002188038440c140100d4403000d0322950640c0d0450241022860340705503010804c00c20b11909036285d0030261105080c19526200b40f4100d8004400075103081b03450304000103d03043e00f8403c41340a410070001800d041c0030605c001000030344050180c00c0d51001000802041580c40c18003c001e449280701c0280480e903140b104664540e591350a0350390110f082d03010035031059030003809500fa07000100c3e0349a1003582d071a040740c881e240340039002094025425031807207404030301a41c0c8154060045600c80780b85007160700f00044001004154817204018092240c1035408a01004481a11554110128190b4404100141580304a90141240303100b10b009803010481000090510701034080349402c030564a40c43c03140c402c142d0060700700e001038000b00700b0704850a01a03101180c02c5a60701000250300c030b41c183d80b0003100e0140d421081e074035100040304002903425140900ca07803006c154904804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 795458741 1250 795457491 795457493
    0x609060b0909030706020903070b0c151006021b06040e340503010302310c020f011104050105070614040b0a05131112030d0c0809100b09060405040204020d0603151503 73
    0x14076401025001481d454000031f41c01190381e02008140c010f403811025442c1e0f13030b0841c40080703a070f52410003014105009003080080d0f2900342d5450580e04841c0e5a4025040c0303500d540030002d039071100d008640c5510803800e100114441d5100101e0501ca50044030040d102128135104c0c07200904040424840c0b81c0312641c5020050561041c1600e0440358142c83c00d40c10a00e2101e041800e940800f00c2d1000404651842c0c5491042c580c0c0211030982c640350283c45014001c03410700ca090b680c840042d41c2103101e0802c402c1009520801c01010003034010640018076209000003443c070402d0503102911200ca004c0d0030721040c000148282c0f0f80080c3c0c0020210610105540d824003030000840c042440303215000703648521010240211104a5014071040000d1a0f0300074002d080024262510000c500c02d41003070b04e01e40800c520031084442001404421680d48800801018000040c000c98002c2e4003031001f881065503e00528002d5486141075241201c0141d1400f01211300c1550995130008589000704 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 795459991 1250 795458741 795458743
    0x30301050a0e04050a0212030a030c020304030804030b1f0305011505010c050d03050703090b010f1502060103080d0f020d050a09110f0108041103070f081c1d0d0201030e03070609060b0909 82
    0x1d0126094503088100d81d50360b5091031814200b000c140690002c0501c44800a11000400140442845a01c04000301c0201c03c204a070789014602005003584800c001c140045110f5413213055200001c40e16070000368102158000803466240c0c01140c1d00d82d15032540c074030740b64070710607070040030f85800c1c0f0b80080f000030780b07803903155031a18004804414103030b07120045000d036807103078018110300e5820074a02e920f2540c0d22a0a0803400c10544a0140910090040c0580952001c80e01038101d80e00800d40b5820044041c100c81d006101145181d40381c698204665140788084d4003c15224400300c00300000c0f10810760402603e105800c3d10700d148142c0d405d00800032582c2e001800ca0750440c2d0006052040f910115000c02c0c54100c1a40100c1003040001c07400140380c6400240b8540303100200240d80d8070031803500c0d0064461141c01c41c181600140d80d60b105040c1d50402041c44084d4500500d0080795403254200001d065a008130001d4a07801c0d1541004002e11030315000b49a900a029a40b140140c6002c506013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 795461241 1250 795459991 795460009
    0x4180611091e0f040903021c1b05011a06090d0609020a0306090b01060f032c1e03130812041e0801050a05090c0f1309050f030a051b03030105 62
    0x2010103a64022a03460300c568402a140d44500c090095101210a4018000210000070803148a90038450041003107050a020307030006240d0640080c009410410a0402d00c0074441650340c0810406441034030100100c50120b1403481e0241c0c0001030340100728140501d12001110300d450180710301b04050840c139180d020014070007035080b110000c0c1c028810b02c0000e03205280c540c0040c04450501d1010804c0c003c010004604031035254480700000e501d44002607068460000c1590740304621030b131401100100030544400c1402024080e10004480c00d0103800b03c003250368118074055403002c0394500d41d6001e49007a80b00070b0a088401001e411014003c82c4d0b84902c40d5004500304146a2020702c4e0071040414545005440d103107000b4005860007002c5080140350440d41001c452084a030b002c166428104040290100080c003d00c440d0b04009403080003920014204403040c0c452600c800d03040306010300c05441d03118220340d40d1681e60b908144001c541d00c0d0241e2240c000302d4004000401856641c1d80364 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 795462491 1250 795461241 795461243
    0x30a02011e02030903122d0307030b040b0a09201c0b01022404020f09040f110111150402030d0203160f0201120c080f1501020c1c1a01060305060418 65
    0x5858807440304484101e08501031203a45540510131140218000b07544440540801c40070958030102d40c507100880f0308069601c1c41c615024102042001c2010240300c1e820201003a03d0251020074004ca4880c0854004102e40c0d01640480d5a80c0150300600611080f031044640e08007940342e4203142910000d0a4140b240c1c142d411042030703440700d80f180140d00a010010f00750440c0103001d98074002614100c43c00d25400c40e800c81c031079200b900509a0f90303d06240400d000d00e4110000781c503001040d903078019040045040c0141030092611000c0d000d0602001a11250161841440f48a0406d48107140c504031580910a041d900140202180c1b01c800040e0001e81c960087d038a8408951107000607101c0b9000d0002c400d8415080c8007152002c2c0703030000803513800742421981c0d0540707070303951200320380b62a400d90010b05006800551070700c1410710340180c003205100c0001e000c1d0580c1c0407442d55640c90030f042908501d0420b0070b07a1070040040f1501881910361200c3c0035a0b0030710040c250f000c0306100c41b50303840c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 795463741 1250 795462491 795462527
    0x10504090c120302150702030a09091a0907090812070501050f040b040f0c030614060a0501020c0310020c01110c061e01060509060307030f15030204051501051b1029030a0201 76
    0x1c030380c0b4181403080009005400000345540e1303007400c0040b0000c1d02c07584104034403030100700380050008a030107462160344400301c50500480c1c224a00501080308031032010f802c80080182000d800304041c0070500642c610341143d151082c0d0355040d43d10f451402d40310f004144144039002d89040002140b040c3d1112580590700483c0176a0350412031505001d40c00142e007010708524507240d2140c81003a4000b0100b8020042281c1c41620581d0303032001280d03221990400395816400961240070500542d4024104078500000007003000e06581064203071540000c074a0420640c000f0300ae0140d5107942500b8510780840c1c000300e03410503604218000e0218070480650500480c40000000c000701d120340d110340c40f42143c500061106550710b1100c0074001106000c20383c070451a00011907401c2803100300008402e070041e182c0a060030f5950710080c034907401c00030502c40640141c1c10700503480190351203488081c1e80c0c1d14600c007421404026524a618480c501a6030081d40480c8170500980e801c40641d03080504820 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 795464991 1250 795463741 795463769
    0x10f14010507140105161b0c06050d0906020a020607110f0d0815120c01200d0347041a0f04060b04090207110102060c0f160803090106030506010504090c 67
    0xf01d00411018166100310b041c0d035203000c080c03042080d91407040d0162602c440c1c0c1c81c03480790303000503c6000c12481c0400009004410340c0c0b508100303690003003014080401e0341801c0056400e019480f0b44080c1e0f07000e01000c10041e00035004102240390058035020740504108000c01c0590301d003541c11035a0b0906041d8010900c4080d10000709a08210300c0248500000940510150814001c0b055501c40c0070103080d5000c07462150001e08400074041d00020000d6200d0002c1c001c2c0340e1a40300590080c13804583d034000394244e03140c6680c070301240c0280341400d01b880544414001c058411155241050340c00c91ba41c03047d41032602c1c2080b210080b09119003a00c0003210039072606034003030380000e005000641c00003402050100300060340c0c42596020f4012240200280e06000f1108401241c8481c2c044502940b800b0042c040021240c545401403c400d25460440c20340d00900703a11207a2154200319154a541da440710014000c00509200090062109072818496606039a4990500d0392040c0103120f46030441c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 795466241 1250 795464991 795464993
    0x516060f02070504090807210e03151302041d0309030c1203030f1008010e100c080709030f031418030708010524060706090305180a0510030203191803020105010f14010507 75
    0x504442c1f00301d038030449129894100300c1d24846182c070a0750244020412403200742030f4908021420384840f1741c00800e00c588550314446600d030f200d0011b241c2070742c0061396410818008a40345012441e00c4018400454070b8a441380704051030300c0b04092600b0b000e001a502459691640001600d030070040c95038011140e551f0303100c1d9101c5584da880e400540f041d030a04103080c41026011a031814800324015041c0050f125840007500c1c07910342581d20302e0000309140020000708001e00101a40c062081c07401041c9849941c0707407004076070000c805c0d4180c401016045041c40c0e00c0c0800c004001071076024002d0207075103041c45070200400401c8030401c141e070340100e448503440d0340c548d01240c4046503c0a81049116510308005240c1e0300926a2401009090003484119281089941040742e0005041c5072090f03c201c6ca003180a904003800b03a0144100c09162111000094002e0302d507a00c0100034003182d0003815040003400d4680603400500d55405001083c0880c20845001d00c82d0030b442801d101b0f54400031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 795467491 1250 795466241 795466253
    0x905071103040609030b0109142205061501030c090501020606120709060902130b040b03061c05061f05091504020a0c0b04120f0e09070815030106030516060f0207050409 74
    0x298a8000541c1c0400940842c2e003540140004094900440700c150081ea00c440004080381ca02c50300382c24040d005040085e90314183c09052020b6138022414080320942283d0720b103842c4c001c0644410f548402003804526495a040c4600c0c41401c9991502c0d0848519100000c2c2d1261009802d540c0184118212408140820000000140300c4600200301040d55041410000e400000106d100c8aa00000c001041008601504d00350342d240c0089902e50b0700c030002041903068900c0180401d608110262401045050205512642401903240d600d68090480094012107a81089104030301102c01c0c450f94800401b00d1b40c1c00c10707034290b07001a80c51b882e281095881d04115113005041c144420100b10400000c0c0542204010441e00c80d090302d41024602501d130b020007200442e80000891000420b250712640d0500e81208d04a016071314034641000100c0c0c00e5072001d800c1070320581e0106640990031400000346400800c80c1e8581055105061030009441c2e50040c422984610b40f590890700a110b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 795468741 1250 795467491 795467507
    0xf0f1b0306150316090806010e0606030402041e09140a03080117011503050a110a0b180a0503150103120804020901090e030405061912060f0e09010e0a24060609090507 73
    0x10841d20b02036200c0c50b003020300903030401c0d1220381c4400050700404006810300e00043c10341e05a503401d440003c4140d0303540061008039040200203a912580f00c6801d00041c5180d0400c10b90500d0401c0d40202c0c0000160402d84c04c0c9080b404900d1865034403601a050110703500c074501e40d06440c0410343c20b14a01c28000300340d501405200f000c01e01904042140003040000004400c80000d00c201016503000200004126020b9800d10401140204c200002c0480a888504d00843d002008024818090b00c840204c0d107850031494054086100002c0140240b12000004064070902440c020781c40e4501640480c140d4601889a04503440e00c80345215941c2c0303014815035024020191442d80c5402040c0404049240c0c0c0e803210a002c10705001420301210400c2c012002a200146111008507192580c42a000c800c01044d07540c0b29541c0e40350200e81100c0902180382110300400500f0025000d81d40f88100300b1045070006029549400400c0100c4c43e000300f5684129003400c500011180d5601c641034a44217 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 795469991 1250 795468741 795468769
    0x603020405100e070e060a050d091712060d0201020a02090403140d0f0e01380402071b0603151214060a060f1403030d1d150f0f1b0306 59
    0x281c01c0804000c0480c41c1c0c1504802120258201403486840c0c0c1c202c1030b54050b17010b82d40c95400102c10401e080c4100d008100802110740e03003113000114800b83ea2203010740060040c45d000040040010000c10801d02c2290f16600f1500403214a0854112940043c0d952004168003d001e00c004000003030515000d4485c401c0303110b80d0760484e00d80c0c0f2115104100b00034050070614400071071070b0810031452104144078000008030f5642c248080701056035031810000008488120721160f00316207035892604e031030024000c000e04c030b00c10748040305595030003416040c48da580110302014600080c928010788176107051401c854240e9000c00000c10b40e4244040704190301e210f00002c9100300828000d00481940c00082259440400f90b201c541c0c91f242940107603179118940300c0d807640c001d101c0718920030402d40c00318498030700b00960b10070b80072030031030010f82002c01d610001d18241a252041000b000b120042c0700354440d008a107903070b032240303401404c5c0d500800b002662601d5840d0080300003030403600c1d1416020402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 795471241 1250 795469991 795469999
    0xa0510031203090c0e16180b0c0f0c09130f030302070803040c050a0b091f110a11030c04020c1009020f0a090e1501030c0e07030b0a060e0a080708030d020706060302 72
    0x50007200000e0003820702888220303201c0d00c0c5900300040034000c4903d240d005094a0030020f1802205600486034802c60000707140c140300d0500000502186410010070b00c0c030706148041c1c092036000f40b030400e003810f41c404140ca016102840402680510707401d04428015404481724072685040d05044000b4000c3e100700078050000082800140021030b0044401c881c0d08442881303a40c1d0300d0300c45240c080e00039504c20a40248044001d413003091407003508030040c1c2a1510344607141c0025951310b5850201c4e060429240d061131121007455900741406801d82c400c00556083d4606561a00f9459840100308080c41280d5034850030340007150380700f04103522080001003040740455201c0c4040d9004221039240c181181c0b043c0c3d9101040709a0403810300341221703003040c1706500300f41c0340422000d005c80005202c00101580d130710055480b99036182c04403000e030080d9030395804a41001020300c42140c05907000f0361916400000708001e030100000445038500444407004d616a121894048083c0116410083d80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 795472491 1250 795471241 795471263
    0x15030b13050910202d030405120405010e0f030a0206040f170a2f04060b0408010b1f0c03050d1404200109030b09151f090b0303030a051003 61
    0x400300d058214900a080342800d4401c40e2001080400450f900003c4e00302c0440c00c400c500b2114075400d840901803003240100005002c0005055603820a20b03040f40c040c0118101000f0320080c810104600a44508514505440c15082000107000b0041c4088594441c01030040c02d9034250314284000c26810743d001e0041c80d180c0c2c0d144c003240500850f041c02445030f01000c0745901c1c1d07400d4500041c0803d40c1c6804c86054148003a5445404964480040a02c408800360000011050700c8a200300001080c0700350015407100e0804004030700b5210400c0a02d48202820f180d4402e0207490010482061030300d0f03041c21540c612981c902545c46000340a00e41c0701e62443c0c010f00d500c2c8461364400452180b4403c0b101400480c00701c413080564041c10340403035030004100000500028803241c1086810222000c00c84141841028208800c40b0f070407284240b400110381d46c0181508108440e0323038060142c800c0103205e40d10210340403036501e0100400c40340c686030f2618089042d039056031031303040050741d0031003190301c1c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 795473741 1250 795472491 795472519
    0x60a020118030509040b011b1e1a160c240603060f1a09041a070c1e03022e0903030e0d1701090209010507110a050d0f0203060c0307080115030b 63
    0x403501300d528014020350034070303940014662283c4148002440c3c1e0584032500184940c4500e80c1036010213050031100c814452036140420562000404000303003d02540405151080701c3c83e401380079403001c15042c050301c0c1507201c00040840210350900c45400c00c03042e9802440c44500e0003d0f04440d44040c041e01e203409404046906541c102540c9404d80413140d0800d40168800d001e212441120054031298013016604484801a0312480d0041c03041e2600201c46c0302e2540b40e119006198032584504000310208203001c0540521036015103080c0d440c00f1080f0414807040c20344000f0621071030030000719500c151220400d0700a42c4110f012810b4070013101c01c5458100d102808207040c0c498140e2001d4002000060481c0c40d900854201d1501a91003d060111560300c2032610092407103140e42c84100b03034001041360384440074500ca10031700960030340c004031945005240c00c0982c082d10a4561100801c00c01c0b08643c1c1002d00c140c115111003a201b021114221402c0300144070100420364131182081c1c03052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 795474991 1250 795473741 795473747
    0x51b01180302011407020703030c1502070c12050d020d09050111071d15061806090a05130f050c0403170c0f03030a050402030f28020a0e04120f030b010905060a02011803 74
    0x21044440818681645c1c4800d1404d90351400180f01c01000078140c1101c2c240007030340031114604078410300b80700541000f540d5510a21919031541200248500c518000400d01c10f0400510600e001d40e400500441300e15090020022401409458144058072400c0102c3da00200a4030b001031010008480d03492850a0007222029019202e0710034800f103146410b9600c0c5001340c1142c00d514012410305800000842c01d214258200d941d4080c0e1081000000103071540318004a0700540c0114031000441c1580b80c0341c400129070015210f4804000c0601c800c1c000103010400c2c2042180801c00714542700c03012039100e285850300f064130b2400b071030001000703100c42c0d0b00b07071a0011030040e44210107070307260f41c60880c011581c1c032014400e1007101008240307075903200360304141e00020740ca0313001901c1800d20365203803d405000d250042d242124241ca40b5a41070000f10b42c048124402e080c07191805000702d5201400003000b14409000c0d0394030441000400d200054000d61040c103440140d00012001c00142d41406 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 795476241 1250 795474991 795475001
    0xe10050315030c121c02030f0301031e0512090a060815090c0d022a03070b061c0203010908030a06080604030905060f09031f0c090803190207180608010c0f051b0118030201 75
    0x5c003041a007408101c107201e0001c0103807020802100d4405055038619118001c03680e070850509000c8144c1d80602001040d410304c0b00403c540030040200e540d0f03a0013002801303003c003842e41c8180304012000c018000b0a01d41001041040e0701d08569400ca01c0d114a01281000d10504180490143c400500303076160320300c0f1a040d10300f0421005503541c102c04640703e03101d03201e1003500002044128171000140180c41d20154244000c151008030142440b626408a0f0850f810b101c4280d41c0c1040100c10407801410502a5601905a030340127005241099540904140024000c443c0700380c00200f00d1a03103500a030030503141e4040000341241c1c1444a1000009000380c824980d80f107415084c00940603070301d40134081800c1200c502200031071404d1550a94828105160030090085006c0d4120026119044019031442c50491250009a4503d07054565003128100c0742000e00f801858907220005a82000076124074a0410501541c1d141e21a107070b250061090b2030741512a021240c58243c2030640c15840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 795477491 1250 795476241 795476263
    0x605030705120c010c150c0801050f0a081203060f0a090c0e0301020a0f050c12030c130905070503012c09011508010b061c0e01050103060b010e10050315030c12 70
    0xe46528640320710501c900022194880052a80a002e10600a5102d203c62a44240c015260385204114050001003550020401000010017100041c065403502c03106032111102e044403001c85240c80e1800700e40c0c40301e909203686440c0000100001c1c0740c946a80d0004402000020f0049940c02c0d00d40360607200600d03207444548001000a903880289040510031a180602d20740c41d01d00c002504400111100c0c1d201c1e00806080d80281c4100c0321301c0d590703100041c5000d0000e07440384946420aa0030f100a660700e0907030080070341c24140b5050000e289d401c070382124195820303251410044048601c1d150b1207103052550200000080c07401700425082c3c10342c0014054804902c003807243c81e581e03405480c00d0380e05881d041940302c0c404018002801140007803440000041e004041408898a031501e82100d400764402e03500c50b6200e00d4090140d40e0310204800b52480200e4144044880741580104035001c02031030030340c40301d0101d84121903076907040004458025000701200e02400070f2504254545403110740d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 795478741 1250 795477491 795477493
    0x18020304050105150f04020c0c04090b01060807090308040e0903130b040f05120613050f0105040305130e09060103030e0a03061d070b040303170604140711060901060503070506030403140d060503 85
    0x301280c00c13940c10110305a1158002021604c26640c1001004003d500200540003140f00c1c500c940101034490f409004485030017898429690b614211001d040600018161070820001e00c2c01480002c0d6614291401e503000c0940381d05095895140c0c0c1031031445902454824460b141c04002078030740b4030400400c20b41704212289208281e9842c1400506641144000c2d00d0382c008000040e110301b100c14a22031144e01820465030603044881e0400c2c2126009e40f82940041d0001602401808004901600501000b00846528940001400d48030003040c00010204034a040d0404455601c2401200165800820070094035036240c005203182d407121507038007059000b441c10000b8000d00080a45080b260107490f03c960f010100b482b802d005a40041c102e40e489903803010241410122207140500c9081d09071102d15000a1548220b842d1200040c85e20015030304114091041e1344000c610b50701110380c2500e002d92a915246426902c3c041e41c420050000d90000c120005e41000c150449800c8503c198 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 795479991 1250 795478741 795478751
    0xa120c020d061a01182904050603130308060d0b18120d1b08130822030524130305071127060f06071e170a110601151404180203040501 59
    0x207044030702d0304e05c0d2088040351b4403142150540d2120038040b0080c4c03200382c04103140c685525000044e0098000381c42c0b1511000040109400b0550402c50050700501c080700c44507413400f42c581e42c0e400e2144004003140031780300e046400519110b80c1044018402400151750301c0d15420280201e10050004104d199004901603902e845001d01619003103009000300340550020b01e40585803c03650b80d014048020f50350705090302e00100b080851007024040c0d40b181c0094403240003210a811030182524510040391590030052100200005480d801c040d94181801503c50301c0c00e0804903101210403a9507508042380d810241880303401c8050002c0c800d05c1c9503011442c00d0b2144400d0006c0440305c1c0741ba103608008204220030200f681602210103140c0c0402050326010440d9403801001540e1080e19800d6070030100b1186c005c6504140289a15040f04005244661600004900912003810b840d03040c40301c49504140d110180300300303c901030040c000c400081c00c46010741d1000298003c58054520703501c3c2ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 795481241 1250 795479991 795480017
    0x1031e0c060c0b012c22200f01093311061503030906070f0203070306050a1a0906010e030a14102d050702030702040e0114090a120c020d061a01 63
    0x2003007401445c0900925500703000701d40002e50303400b00ca43c042c101381c2c204403113195806c0401e0f100750914004203220702c14290a411440420191240e80081051b1007004000702881d00e40e41c1c054002011134040c2d00c82140c014110942182c0114400309400400504009050526540000c9403054121142c0d04488003580c070610410315102c0444043c540c103410401a141462621001030030006008a4003105e0f241d2481d80001d2a01102c4d500841c0d116840d0410483c00849030f205034004010402030105001e01c02100007480b08500400050510003541410041c0307840c00c0148180e81303a840000b0800c0c115200b019240e540344494094800c103410401494980c5444070305009a03030403100c1001540d4100040280003900b8001d0001e0704600c014440f650251741d82e03004921003c81103100020348070782454090148128000c00c0003400d0f502109030700700056080d504c00100c601d01807030081e502c1c4400e840024500760291001811080c14804820f5000c0c107840800c1380e415100b600e65213051500c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 795482491 1250 795481241 795481259
    0x8010902101b150516091d040c0918061a0306010e0a060515090406060e2119081810080f092a0a060f09030b060a080a030807080a0207020901031e0c060c0b01 69
    0x3146c00f41c50f0600020451f800f10403030369810305540152242d00309500c8075440d011400122041c0039140820760780717014034510501c00544201685010110401041044c00c0170200799106070611680360380751036541c00191121499807101d0094600186080030410f410a40403819400c1004044d00c200d103000c0f000160240100812401484050f10078100c081d40881541c4140b400d01096201c1703402500351665402820000c0340c00903602c21003416449009118401d6010180490101c0c01540b01d46515041e0139040080654055400502c4c059560399240000342817103001c8056913414542121403c14407401c103010300180c40c1c82a41c1010781c503591000c1c2100c092440030011400b04801e940f060001c21707184d00065600c460080c00b11510031303503111142c40c075090072000140c000904490a0001441e07010310a2900085a031400394101011a000281034180c103100041002040000480801e0182c90410680740d8001d80050302c81c035030303644000d0b0043d2103030300713084a84002c13100000c529004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 795483741 1250 795482491 795482507
    0x40612060e010611010b0a0810060b0406140c030c06010608010510031415010c0219030b0112080f0309010b0d080d060e040b0106081b03091608010902101b150516 71
    0x740c0702001200c2c0e4070348001030312642c2e1000c094000300c0d500d460b4040100c0c0c0703070000d0000050950b10000d100321011443c121023245c40a40021310010010002005505c1e030101c442800c040700a210a41d90b0f1080a105518521990061030f14601031103000103074840d01300700c1040c12114242c8442d0814012a44114101d9805103c2d0b00c00803411034010076410381c1141119000c3d900103041030900c00e04590000303280024124401d802080c00e000f070900401c20f09070740d020f00601c081001401c0c46c1405a5031203071280240d40d900c0d2a42140400050341c1000250440901d11002800302c800800b0942020051544400455a5518104200060144642c201d0310344110b4009803050540e03428010212159000034010400101083d0f0100c509200403500442c01510903c0c02040d003201007804d052006150740e80610707010b9145c6800800944c032030340d00049600115240c91340c280a003654102030552260b01000d44090b40c0104006048a6940e03c9036004506985600c06030f00700e24401103035480c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 795484991 1250 795483741 795483749
    0x105010e10090c0914130608010504050d110a060c0302040909030c030f1403060607050f0f2109031b13090b1005090103150c021212042f010e0d12020304061206 70
    0x198100341c108001d517192109525048401070089504666400a000c1510415000042c4e1655130324284001c1107001c115070850101355080408861440495403030711a032040c4005000c10351680b14180c00d4500c01d6040314007400c0794410820003032285007030082c50321403220000c0f00410f505904001030240a00092410503214841d054915541d5000340403451304560390446652007117569065418a0a002400c00b03c1c1d054802400d030710542c0c074462100311b0694805007102c00410009404a40c41c04280542d900340040b00c0001c0004500d00410f0001c800805c60882040c03800e45c0383c00410950581d018050100b01802503041c90300d40c01000480e90081c400101070801c1c0c039040c40040d00160704000c2e00300c407050041e2002144494244541640510050085d04080d8030030001041003147c402c101444441207031040e0120183e8074035101815800d0107505224a01400e120b056480c6445000b542b039022010b400c1c129101c100107540c2b0f801600980f000300c4c05081d01c0c0c80c160401d51094a0480d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 795486241 1250 795484991 795484997
    0xf2003040b1f18060305010207030503040c060f08040b340206180d080a1104030b040506070f0207170a0606090b0907111005070c12081e0112170c0105010e10090c 71
    0x624038280343d1220206080f403c4410803901d030f68000010900038405080c680380030741c40d2156285031510301028040d25680010302805000d0f008100503603408031206902641c40080c1d5902c50300c9a680400c1007500d85001c4405008a041c112003000d51180d0441c426031089400722036094483c0400f600c50801c0d01c20f036481d9a50710002014902c60721070200c044d000309501000050540101c41410380e5a480390f04240c0781c200680c400e00080000c01c10020707910048501c1d0500c0401e42c26000251543c0e40c51103994035140741200e041442c4c01c001e202148456502c00d104000d030f6a0354001000141400b245a14401c17101100001c0d00035000c1c41d85403408824041c042c07c04601131000000003064040c1c180010085104100400203030844600d10320300c400e039218035030a441c04905001c10004c2c69040400701c801c510740100628200d048040c1d004c1c13644480c6408854107459440712540c002c0200541d450343c2064000100404e0624041d0300640403a62404a42e036151813124040d14650f0030b0403800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 795487491 1250 795486241 795486301
    0x203030d1e0e073b04060b2704060f020903160312211104120507050a060c0f0b0406180605060a060f0e220218180115030f2003040b 58
    0x707501422000c4400c0104c2e01c004041e02c07481103450030f46001c8801c0300e04903030351617942107202c02a26240f11030301c01d0b03e205000d915900c400000c4030035507041c0010740010324654903081050018003064040d901110300181c200d034059a04d001407240c107105144410350310402c1c010030f0301c0b64540c0304001290f2040c0d10140d020711054111140c4100603c156504408040024880402e60990302d40340e10703100c1c9010390b00801e4041e051200f048804000c0794803007001d0040040c08040026840c03213420f002c69410a10000460340c0b81c1c1028409400d8207849009550211004201084403a510050082c0c0007a9405000c0c55284c3c841541c650710001d501d14040781e9510b40349051450b00700c440010f1400b0780c4c4100c18421580302540702c107a81005950842da5464a94246040e09021030142c0e1424170711158028107514101a002c2e510340c55851020403d84c983c9014140403c0e280c0046240013052101121201c0c29811000055002518129134880f42100425100d8030380d0300c1c0210f000c1e10880034001c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 795488741 1250 795487491 795487529
    0x10050f0a0f03090f0302010c110105010f03020d020d020406080d020c0402070c090510081f1503020117070e09010b12130b0612070b0d0603031407030210090203030d1e0e07 75
    0x20700344140d01c0303a541015281c0070f20100064044404031003440c4a6000843c01c0c0f00145009010740c0c09184010f0340756890507004000c00300c0c40340200e0086980644401007054078074004169607036860400a500281440c2000840460010701e2407010803c07507080e0340c2c802703c07068104001e034481c003030000d00342c0ba41c0c101090002881c070707601c210b400400b0006800c1c9001d9590320100c0c280800300340c1407010f102040040d0a13030f04180d070089650582e11149400092400e5900282c00001c0120051402111103800566840d0194400c9417000340000c10800032980d4030406071000d03600260b406031900b040710012600c01c9140c03805010384d40b584400741e44501e6480d0000d001e1000e00040784242c0901c140540040c03401c03042001004803141c12000031503100d05508010f421502c480402841d4140200000c5001c41d5001c24560398865003002c012960000c2400002c0c9540124122055424a003041e4513044400310703420f100d00044642801c0c0090030204061a4603003e091103005900100303600300c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 795489991 1250 795488741 795488747
    0x30406080c1602100503100e011d060102030c16030c05180604020f07150b1c1703040f020907120b030a0c17031201030b011d071209060e12070210050f0a 67
    0x1035034814a011203070146080d0f07000194029958600000421400001c3c00034051582c50300038042c0902c41002c0313960b9494900441c01c0c0c070305040d142c100e680b01d4000c0800d520380c0c030a0003243c0148501c04202c0e02c804e003ca80400504c41c04502c8211a480241c440000d0b072810a0700350580000018045e040c06175980000307002c0a503008401d01030140004000c1c00b00018800c046684020780c03040700c0047d0b6030000805002c205c0301d00913241c800201009517200001401c411094510030040410b40307840b511a8076041002480040000f5440203281042190300350340100f0b0008864901d0303000748881a6901d046c15158984078002400e0311400c0507060003e820100c0c0070f80c0003a602d241c21031f450040c415420411492080c0c00403250491400010006161034480f4000048094100c2c1c1a0747c1c01d200c000a00041c4468900130304803500c5410710020711805501c6401084051342c04d940c202807100071058855842000704a10400e000c2814400c8584075405a40071460403c40c180e01c0c01404a20035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 795491241 1250 795489991 795489997
    0x310050a0e400507210b0109110706090f0206030c0307031d0a0b0c0f0304050f0d0f2106080d02010b0102010f0b030a02190b0f1b0a0302030a051c060b1b030406080c 72
    0x50390244102000043c1c407580429580c000940040e52142da04411450040206e0074180c3c002d000c95810400542e55880c10300703049802107540700c40001946030741454042c004c91540c2d40040d5100c0c10100030480c1480c4440000e5114803000d64040040191003000d140344000091171421496028286500028000410b0280c00109000c0076504004404800329241d50003101c01312915041014810701c144002c200f201900006420702c42400e04000d640104020310000a002e0100604804591001c0c50b41d8000409048000c00356404484090b10203800303010041d4503c4e0042d07203018000350f11503980f4810700e0501000100503180c0703038450f50204540f01402c0414410f03c10214100001d0883c406801006c0e40a100b0f504251100076042c00d140b01382c50010044910768000d0a038640c0040d60201c1155402d01c000c2c1000d82d1078500004000c003400c0502c4a25114451600001203841801d12024105003844102c0d0400034080d0b007030382207880e80658850400441c41c01804100c0c103114103009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 795492491 1250 795491241 795491243
    0xf1611010204050d05030910030b0913030c0209070f0f03140606030402030f030a0c02011403040228080f030c01060602070f2603220f05090c0310050a0e40 68
    0x581800d44540c0092030507143c04c24112a945e00001c4e40c03042c1424a00d8079510210300d61300301000068040000315480300070040002c500600103040900c201402445000b02d03058001e090800703280f814900c042c140d0040031209902256806900901c00ba02c03a0190b200310f912550084180b64542506009540e04064000ca034036002d0010140300e084400c0019183c0c0d0301d01a40c0e2602d100b2080d00025080c0c1c07007240c007040c0320b80600300b04002c00b43c1c4401c01242001865240249404942001c011505334a250854040b60103045490200c0d0b210000142100e0310181008100c0d9940d10b80044c1da0f40c0103a8481d81001e08508102085102e54603e0700c640d800b2040c100101e040c40c1ea5184035411a804090060707620001c2c2c1403001200e1040e200d0010185c17010761040b85010741071000046078602d00401d082c0d400c070030010001d001c0000b400c1204000f040050040d04d403c5850f0500b408604400310703a2446042c10300c2003010811801c50440001003080b101550204003003840780842586440a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 795493741 1250 795492491 795492493
    0x2190b070c0e0a0b1f140708090103060510170406021905040509061009030308040f1208090f07080709050907050301060303020307050613080313060b0619140f22030b1006080f1611 79
    0x3d86c2c0c40003085c1d2004140d0503200d0900c0b5592088240300240031213a4a80100c1d014185425012100c02c1c0c000003c1078840d9904042070041e640c1b6450a00013910807140c016020b03101d851b241d40407864108015106403102290b030a00c86544007024810b40c0c2000d030710701000203085040c04201003802000a140c0050051313a120f140344910380c0341d00c02c050a810601000003141c0c04208006030310140030384040341c003940d400740030346a18094105503541d0742030040020b100c1e96440480d0b000c100c100300321002458080c0c02413003115902c1c00c0c0039440c3d4109040030386450061400185e030045002000070003159010300d00c50304586401045640720b80b014002202c12a82c0d881200006a462102402d011252641c4130b10160107011002000700a800f03c00010100b002d0140e402c40760285c00948603505000b40c5a0b00880f214000300d41031090300e60f400030304a41010018001c2d49480004648142c4440d074807217450607250001550030b01d9001b03c2c0c142144801c458002e0f0180f5200d2140c4904c1412400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 795494991 1250 795493741 795493757
    0xf050c0a0f0c08180f01020d0f0509030f1006030b090102130e07022407180503120c0a081612020309011d030708150403140a090302190b070c0e0a0b1f 66
    0x1548040080d800504c07404c42e20000a044401c951410782a901a8032100384007511350700911120180c0300300b40006050b41400000b0410a089403010080c00c0341e40d841d03006c103c4201c4212120510300074041400251500034921000400f8044140200d60703000e40c0701c03416400a01c1c40d001701e0301d0301580054241d20450007511810340f4016043e001740301c81c003255100d5102d400c2c00c3c44079011304000050101c0508054020508004682e404210880c1603514056041da8411501645500f00031000b04010300d84000422245c8a44e8000b0407000613181c801c014204105064081c160394a0080c042864001100d04070020310715a12403d000b560301070050121100540c0310a204c506001cbc00c4a009000c907a0000200011702d41d00004000e031200e543e82d01145018200c91009010446500020707001e007030b40c140182000745a2141d03142c020881e01071040c0d03d900d001e00e000070b40502c80344111600c004800d0302041c0701090f244520520900010201d83d1060800020301a1a4260703c44150901c1421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 795496241 1250 795494991 795494993
    0x1c0e010504030809162312070807210510090203011e0b030610060503040b19050703091506120204110702060a05040305070b1218070306020a11010f050c0a0f0c 70
    0x24000d00780954441c0e140c1e40c1403031400701c80075403418289180032051189950002c00c150b0060b03c880300c0c00c031880700c03401100502c045000300300c0714454200d50300190b2040a40028410b00045520001c0e20112001903019064590701952141d918002c054080d40003480070a051503000d0303000040543c80540041900841070303210300321204041d003e00c88595201c2e2041c819525051205640c08100e10542000032400c00c800142617003c000c00050080c0b94540c0810b200c19051050803500c1180150240280d07e8203010080142c1203002d4120350b8510403061420350b10456000d804141c8944103100782c11a80241c007000007511805607904030324801042904050b1319040001c0c001d040d42500c40c42d548500c0c2d490020f1500e181c5030311003441c1003414000402c00c581d03403c4e0390380d401c1189141e110704880040f50300b060030158580d2006100a10001d4264030342038000c000302402e15051002004030314050310054054400072104205012070401040000e50302800c80424420503e151104000d242 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 795497491 1250 795496241 795496243
    0x8130c08071413021603110114040c08060907350106031b1401080c09040e0a14010b0d0804031212060b03220b0402120a0c03080a0e0105040b1c0e 64
    0x103411101003050006030002890603c078009401a60301e100302140380c0034000100304114044048000c0410007524660921004250443c14a40009050f14100e600301031514410400301c0340300748071140c0140000100d5500c4041046e50403907005600c1c3c40c0c039441122200c0c4600c8228150344000c3c1c6148802a11310040013449004080c5218110742008480801c5041c218520107500821000d03c1d2040c20490990b4850140713070700200d100c000c483c0c030703008110002000303072003c070319400028071910480b8010710082c41c418a066002c44402004498051014420340800d20800035180007410031041000035140c6c400500602d0b49803800d10a015040c8c040711087d11040d601071707440603201100303101070513501c51a016010140300041130001c00b000e80d40c680551400078406031180d80001d40003802c106007404803024440d40014510401d43d140d00d00100213800c02d51140307000841d007000030181c0d035009004648c20754101d10302035030030211a000084c07982800c5084502ea9241c9440704440c10b450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 795498741 1250 795497491 795497503
    0xb0712090501050c0705010e0601060f0513240305060d08030c0d0b0603070903060605060a0c020904150c05070501150503070b030601021011190816030b19080d0e1008130c08 76
    0xc0c0070b03400b0917554403d9041440c01d68071203814041d0aa00500300400c00503410801307072040c0004500b070040d12401c84420404a80045501064100502c0d4034410804250442410b0758000c82c0d4904000c00e4440100744500010301e000d0040940c1010404038441c071640b000502050540c0441c0402c11220000109410b500141c0340278010504036201070040041500514000d003009568181c24082c04120040c540200d58601234080d960070302c0400c05002d007520310030308102e81400090003002c10512008005500c40c44065809500c0d01b0b00d400c9030441c82001450495000030010100c5609159048805074805040b60381503101d48000301e1134602290081000c00506202c41d26106c1980700310400d40e10304000070748030030810b1400400c40d104241040c651002521450005080b00000010a032003d0003449441c20101002100040701c400000e104650440203682d800d0070050658148501c104100740303090b000c1404200055141104080c40b030200d9405889014409659201c001d41481 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 795499991 1250 795498741 795498751
    0x1a0d0f0c05120d1d0d0305090d0b01060c0212010c17180d080a0c0e03031606020f030f091b03070311010e10030f0b030708031602010c0b10090c08040b071209050105 72
    0x50482216440942c1d0001c0301158801c414425025200404c5030004030300410ba08401018040c000c1022180c5450f0348001502440d0b0207401d034040c9503141c0740302800c5694440002c0b8460807082c2c41c8080c0001040c01204c101c000c031601d40d40441c1e0a0585800f20b001030040035071030540300c8031080c0780c0302c2c2a08218100c18150b01e61a080306c9401d103104c0310000c0d5014214408180054030010103502d4800108030b400311051071300501c40300e680d24540f20700a0b04c80e01c0b406514400b4080180500c0c0c5401e00c50280c001c480d05011101d03030302a01102c00d140b212038510b42a074190040d4904001060403c5c3c145001c0c1401407625155800703110001905000b403581c514000240c0c0c44c824078a03500d006101d05c48101d501200244191803038103002569074403d1095001e110601c2c0c080e03176821640a00440c3c0c40403540305442041c1840c24150205220002d807040019103803c00e1107441c0d21501408980e4011500201100600d59030b4000030358400310054003100507555507100c460041a001c0c0b00c0c2d14022 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 795501241 1250 795499991 795499993
    0x3180304030b07080702060403080406020309070b3420040b1c030801080c03070b280f031103060627030f0f1204081005040f0605011203031a0d0f0c0512 67
    0x50300780b140f401049000000d03c10025980030710188004a0707000000654019070041025a80380d84daa6281070500e05568802c6440002c0840c405001c1402d5882400e083e0880035081905150341440c0c0107030454469002800042c03040704000e10240f1105042811200081c10100340c05004d2030100b0400110706004043c00981886130100301a8003c050074014801840244000440c0000280e00c0e015680f107001840c040004680d509040c2c00c1c41c040d00d00d0005480441120351144001624000504941000091900c220800074601c85070659000b0600501154209444600d0039401034403480784400b94200300c0003917000165010414500401d0840d4003500300c00e102e81d6a01417800c0d00d80600c0300c5450340c00b44014065804002407080071101c4102c00403070161200d0130450403c011030341d0058100e50a02c3c0000c034000b80981071007045d841c4641d808008003180910014401d8150f90211980051800704090105034407000903481c95028030361000f202c0340c1c0c410020318408110900c0c9405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 795502491 1250 795501241 795501263
    0x3f030e040e03030702190c0e0c03090c0a0b0a08040c09052a09090402010c140303100806070e100f03063804050a0e04061b0207140406050306010b0318030403 69
    0x4581050701440076003a44500066040d400c0c115000780d164a40c4803c102621540196000180040000300d50024580f01c2c07900745550074085a640a01d81c0210340b001d8440c030800c0003000c2d1904102400c48101c46103006c0650030042c000104179841500036100b074800045040d008902808580320701d0b8061542440b00c0491900002d0080043d05000712159011002c00d110b4280c4d00d80701d003800650b0180d42441c05044143c00c40c5802c01001502411200640c4400300030004103031030200300002600c0c1d0300402c4520039943c1540840d0030044400406802c203a072000c0c84e0302d2060213080000d400311018100841c03c41e441d610041e40240d84030340c2400308c120f0359407043d844107107040c2c80e50728a8a20300a0414686170030324021402e50310b402e10039a020255140001400d01482c2c0d403141c1d0ba4000101954059400c22007802036403a800360003001d42080710000c040c1c3d194134142c0714400c03c89038050054150380c2e00e4040040740b25040100b41c150509800e203001c2c0c2204005000920103144504e1034255 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 795503597 1106 795502491 795502517
    0x5241813290402041b2a0f0501060302010f0c0b0105060304111c0b1006140306220609060b030708040b06040b0301092103063f03 57
    0x903020088030070414000580e030980340c09280212001e03c654858850300311400344541d01440040b651020b4101c0740403418a0440d002c40009140034022500c46454584540100590032501c40c1d5658000380700315070300324146c510304050614001c4d01460240d5034605040006010306486640084000760030000f25034110700d5454005480c282e02800700c080c201820100c0c210084401402c0c030300016490000c085551030450781140c0d9000c0081e1444c0030082032907032000c0c2c6060342000d1003200c0050344d1070140c481d08124800250001070b00e10b140200ca80d04803021900903000d203000420078003421980c000001a002608030300140c02036180c00340020f0040800301000e075090350070940140284074010440208452214002d01c0708000031200443c11200e06004406801441d02c0c5855104405c00080002280c8c481e03141c9014000c820094445d0454641c0341100003071101c00c0c41013 = true := by decide +kernel

theorem cover : BRFrame.Cov 795323741 795503597 := by
  have h0 := BRFrame.cov_init 795323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 795323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 795323741 ≤ n) (h2 : n < 795503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
