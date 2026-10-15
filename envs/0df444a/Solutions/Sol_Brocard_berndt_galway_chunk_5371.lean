-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5371
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:39:13.823384+00:00
-- url     : https://prove2.me/submissions/1f7a6e61-9567-4dd2-981f-cb740e802278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 965827338 ≤ n < 966007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 965828588 1250 965827338 965827349
    0x604021306140d030908160510080402061b031b030d05070f020a0602090303130e070e040627090609051b09150928060611030a0e090411030a0b0f0709 66
    0xc03121414850b500b829000480da9500900f00f41c40500d65404125040c259603002da20510004450706120b18586941000f52004040c0b402c10094607056011956512440d0051644c64404100084d1720010400441300c84221100024070305a82409601d6642d4000c01440c030b03007041c280400074034582d100e01002100e0191640c003c0a445045172100f030b00951110f40c40c160140820000781c440b40c0307050703030585004251600103a54507140c00780c401408904480e0855109904290302008070b40c035251500c1c1040b414451081c10002d103901089002414480b00060242e0300f40034414003400360105040c01d4100200c1c20400c140408142040400740d0111850700c41c4207540c44401c03d035414440501c2c1da2040c100071030001030034420080c04400f106074604a444542e203a070420b01c1403940c0810600d0040080342c00440c200541c0c0300c0040c01d6030709841c03071103400352000c50002414413510720010003031101d000c0c0c150340000d4550b0908100040c3e08030b6000080f8803070003012882c440d1007000f10b4802c90340c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 965829838 1250 965828588 965828609
    0xe0a050301140f04030903080f2802072102180f01060e031504140a110406060504140103091505010f060e1206011a1e0c01180b060f1507050604021306 66
    0x540b0344070f4245400078054015002c201900794040300044640d0002c0000b40c03401041a5203801440c6080e0950300c04100e00c9003d1b0410b050354204210740c0004421094569007520350006181c0101890b061b1141241c020f5801304c034a990300c0c030415016044860003811150851000e03030780c807000155008051901c110380c05911800550a00034120140b80340c10a100ba1842ca4480e210580c9081c5021075505c0f050f183c58a110501004914180c803d0300000c0440d410b1a43c2040d180c80702d50210314000e03050090615498031002c5081100b50540d000c025088590100544e584540d150b218800c058002c000200c0c021180540403481c00c0488600541c0e41000104101e80c01c066030081092141240000d51410910030b025601030300c8500c0900b6031458408403515600961540d07400d40b024904170700101c0c0541c80500780070031003039100c66034080c50030b50300424180b4003180441d06000c041076948101407130101c0d00b11f0411002080d4240514000c480d0142c1c00164007201000701c0f04c50b4400e203138100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 965831088 1250 965829838 965829841
    0x270a03030507360812030610090302040f050a0b0a030f080901090f0e040302120c0309130e0d08161112071502070f020a082a0609100918110a030911060a0e0a05030114 73
    0x1880e0008c001c01c408400c928146200d16500c2c0d0116040c0c400c86461200c031151210200039441541d846000303006002243d0403291285592240280111058009000c8010000da039481e141d000300804402022280340301004560780341c1c440e11400314180da044005001715049003100007105001d8454048509014500d400c41e144104001d00d100c1156041c1c040361660840c032140001480480d486c2a42a240c1d0707001c2e4549a0001c07041034414005020520568031140c40d0312050000741400040103004c207050361a200c42c100f808106c680000380345030580c000280c007020083c40746d601e042a1b91081d02d071451090b454291690300c03807103110300300800b6154184010440c18860301e001001000d000d0b001d5440c250b4148042940d004001d5902c50104a00c403104005003502420144220055210304121b200031258498030b242c40b0301c980300402c00d81c98030856010302840e48070007010340100811195461126132006002c14090790305d058480d941201c4001900c0c203042c02131909030044080d400407031303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 965832338 1250 965831088 965831101
    0x2030307081024230c070504050403020309100c061d01181e060b100809100204051f1e03270f03050c070b03070206270a0303050736081203 61
    0x82d508034025500800401c4203810b2880844003d44141c220f0002040958170076030340d4000b0785880c0159000d86d018500c2c28081001080d030110a640140a04540220015415850032941405100c00203014189081010b04025682e13001d04aa85000200240440000c4201146a29529081c09004001d00514103007031104000030b103100152088a002488117a00b401048045010311240c0d0040341e4506c080c040079203402c2080380c0500c404444190b103010306060108001c520fa904604450300c401e41452000030307008a217030405c0c0101051000d050740c4031a00e00200a000048074002030201d08008001d42c18280300d402e41c445c1031b04100318600c400c9056904a44d55031009200717a407640114540440d882e018940118006d4445900030065400c2002c6d0003146905c030600101c0008952800c13034100d40e900491080c0300d898040c03c0008190391008000d0380d01143c004400c401204001001003036101070b080c3d1101c0f0400790400c1c2c000c00c140d181c140d00b503035440944543d65042001400060741 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 965833588 1250 965832338 965832389
    0x3060102070e0a090501090602071b0b0906070809090a1b0207061e05070b0106030606080a02180d05031312050706080c042702030708040b060619051b060106020303070810 75
    0x108851500f100181e0107006494603802c603540b1040880d0410340000f9607d050050b0b500b800d20035800041000c2109038600240c0c03211522603c0882350181c038000c1103801c00d020400c8207a62402402038440300071890110001d0000b00b401c41000c2d05909040750040b05494400035102c2c09075401d40d1100d040c04810b55081c025070002d1035840074200107042100c0c1c0300007040c3c403000c0e034000c100300e0301c01051480c10402c019000040080a01102c2403040c08030003190140480721107000c5c4d1094454507034840b01c0307040050640c46640641d03e4100721000b40090402e200d440074900c0c0e20b018030142c2d5047c82c0c9030035044400c80c02c10b03151002c5a100620003482000c07500b20108000d07145c8c2941c402285c2d0081000c01c0c2c1603070070072600100404d84d40c20801040c002205000c41e40490100d6015242164040c807182d6200010b40300d01040005c0403500540c1c00403030501c5c01e8100304100c0103ca50a40e9241c8000f0740d0b1303074411038810700040e04003000700ba41000512a140700351105042c051b036680410f249080c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 965834838 1250 965833588 965833591
    0x1109040513060905060702060a020708031603060801111215010e06030c07060f0504061d030f0f0903070e0414010e060403030e010b120c0a120b04081c0e0a12020303060102070e 77
    0x58400001c86150000481d10300c1820301d0144107a0103401ea514088102a061260082c08403030407600401000e40012111802c0b80d43c0711200c4903442c108514200c0007103000301501d030000900b5610700f006440010340e9100c0030380100f80c0d0303064107420070395104929004844c5996002134081895207c20302031515100001d55408800b0365240b0b07003040c0507a103807281942d110301a054091a0b590080c03005020351400380081800303090301c4e01141c0c004100c8401b42ea9200d5400050250711020581c0010f409101080310410440141100c035041e1321031100c11a04a001da50445500c104181070001b42d11041c06042c071b030000b5440103080d60b03643e140c17400d4014241c91501c25906546c2c3c0c2ca48074a5a0343c0707846070b85804a2205008041e4008520113210718543c00d40c000c0802114540c6800c00000d0026030041c1d8082ea01040e100d40700c0c1c8002d0311004110102200b034105150410095844441000804a485a0040b81c2c0030360340e2a1848410fa85a02c0b007521140d0043e000510240120007d030030506 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 965836088 1250 965834838 965834851
    0x30306101b030804300e0402120105130b06040308040e06100e011b1a07030c020106121b0509040305030f0c0a020604060e1c1805092401091d040605070311090405 71
    0x1810a58288100008030601030103c40c08001d1341c2118031417440760b02103071a440a5005440c218507081c1400480c80308481e052084034401c403011644038a104000b50807580c6800d502400f2a9100d903204e2800c4062900140156040c0c10600000260305203000000d400700c43c40691038407e00c140d0a2801110404101c8150b2240001d003d150400007842401c01c50700e0388140510500a242880c200c0101075a140c025041e04581c14844107110090400850001d40356100c0360011002424248040011041d68491913212011808000031301d80c00900440c80340d13013100e18802103941e69141504940c0100c001050040e071103000003a0006d10b1907404035107010061001c54508440d1302d4801d82c25808840c0c209000035003a885100da540ca1250005405000100e030100d40750b2400700703040504e0401c405041d460390380c601c0022011903402800d80001410740c0100c4003410007103603000c0105060040c3d400f00c916504c0e0a0016039514468850410307840200c00146260000d00e02c1040081d2001a100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 965837338 1250 965836088 965836103
    0x20901050a0c081306172d100801023121260a1124041703010323210a020304050907090617060a0e0a1d030306101b030804 54
    0x960142040440119009100c11b6441e014403d00a42c040c21030288054042103202800000c1001c50000d0584c15002d040c20a03402c00a9650307030543c0c0380b104044641e0029445520000d09401c480500f100c04048a4408040403500b81910004400056800d40708845d01d000010b0100424691401e5680c4601c5000e1405030b2460450b61001e0055441e1900804c2c05a5200091100100342c0288103440c0b80c9507000040c1401080d50b0b040008094960a2611600420540014104964500e102d081c000d045068662a9078480c5002024141c0202d1051222161b03040c103078a80c0040010f0103440c0341e04594a000c802098002d440019030004003051055000c00d01002c51261100244503110344010b41c2c03240c08251806802800029540880c213200300c1200b0100140b5454111424045072032480403009180c2e50784003c40000e1008c45800c0a40603800c01c001519000000041c1d400742c40200c40030f6504c030403804001c3d01c1d140901c0001c07030321020070b00b04c0e0000442e0013007207056030150042c1c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 965838588 1250 965837338 965837347
    0x9071a0c030c16140915090c071b061202190f0e090a090b010e010b070f0204180308090c010c02130203070314091516021027150b04020901050a0c08 65
    0x5908200c1d0307140388400680307240704040140c0c3d00c4210122101d628180e03550f50391420301c01035100d1b110b135201c20418050b01d15000401c1c944240300302101e202c1d40e003159442d6400303112038400101d04c50080c407500c0d0000d0000031820a1003103040c070032981c280d560f10908001e4401e00d83c6064500d0001c0303c241c002409140c5550a45984500780c40501c22070b107014001031483c0741c80c9424800148180c000009000d250b2005024614048081761582c0350407000ca01c0075802a840050060300f81c4002c160034000c00e5045440030140c01400d02c40c044e0144006407804038840b03d004440042080402942c8803140080c061070325180b582c011074000303869250214034281c041c0e015000d004010794040c0d01c0e942c40214505694140700c407016400c690404544101c80c40800f81c000e6540c820301030a0300301d0950316030380c40d640e07007008140c00404c4c40001c0341070340e15080c918200f42c00c417040d100c1601c110441c2012150b50742468203108980c2564030584550f0b08044400e101107806080300b40c400c4682c0c400820 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 965839838 1250 965838588 965838607
    0x140a0f080c161103210c0d0903170d09140c090f1501180f23030a0f0b0618070c1407050a030b100306150503010c0903080f0901180f060809071a0c03 65
    0x15603505860355885e41007680c984100ca4100e141440740800f8504001d580c110510000b480d000300d002a05188030f50507a11041c616142c0b400071b200c000c9000b4900c1d60602e100d4130000c0000310300120303517038001c0340c00084036a911039000c21720050813280e504a550003482e600c00c0543c01070a02007070300103070144000c242c1500d551110554108680000515031005804446100c0443d100203074103034800e4001c0c082c03010907a55010446003103450001c4c01e111554001400503191000d0440307804ca2180340144071400e003000007034075a580d0b110b0705460100181039030500c59000010700340b00722038000c0d085200d4145103490b8141500b002614050b030310006403100001069a43c090b2200040b90210f549000c1c030311305020142141d0807030004100340103406201f0004242190180d50780a8030320400d461b600d2019074012542014140c44031600210f0583c008604100e80a00031001e49000e501c0c1e016103174482c0704032555205154810007a4070106100c0043e1142d42003000b0b0150034009104507810701d140d10303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 965841088 1250 965839838 965839873
    0x150525050a02012009090a180611220801060503060105030307020d050f102306100305070507020607060207020108070216120c0b0d0e06130206030a0903140a0f080c161103 75
    0x48601104e40013007290170613403402140094002d61070351001c2240f00101c0c8120100507100290191166030340e00c2d030f1681482a040704130341110030b20b01103002d1b01402880e424001c0550764081e2060644c43c103c0c0100b134034180000c0450590f0402401981001e07529401c100030b040701e100341211540103510401c240340204101624a8920307080001c1116041c1d204060860240d8240500d081c541c81c3c0103012041d04c905046c500071446925021590f0b07907440c0301c1552a0322800c0c0000b504180c0000c1c58005110f0150b001d0918180f00340d0f549001921440800c90380c401d003001e890300c981c4040f030ba4100314956140d403002d840d452181c840c42c0c51141d0f0305c091030b5030380e0b400401d007511906481d400024004032081c00880c1d032150003c2c511ba0b0035100c5640201d490b50100402004035280d6a103000c1d014140210b0400201c1182444103542e1211700f0307072000b400e00c4104000038003c200c0c0d9001240501c071208041d50b550031044404103203628026142c200d6000360914600c0d4060044000e51032242000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 965842338 1250 965841088 965841131
    0x90a0e0a08070b07031b0309050c030706030b04240902090a0e150103050708101404060308040810060b040e060f1503280207030e060a021603150525050a0201 69
    0x1501c40291034200a041c40d41d00858020184010986003000804102d060034846042c43c0d101c9160000d81c180c11403a11070324001c03001941da42d0612403200300180c0194581c112000b9001c05071401d01c036802072800f4004c40000400581203083e81f0445051060a03501e0b805400b106d04003c1200001e150341700140342d41d0000665030072800150000800302256018012140c000d00700c3d00c1c22401074600500107025042181c0503215550032040615941c59030785802c04005150481840d580e1280c3d20200d05580e01326071080d5400780c5040000005001f2035800c15207003118a400c82c2358403a50360390800c2040000490300302e283d200141030051280840700c1d601452007890100c04054082c03030085021081c0714102102488170383d00400284001a5010040c500c0090342641e000ea1a1410010140d05122044180c13480c90720040400106112808140c2c1d000c210000c0000c0049803110040079050700c06c012000350300481c0c00d104e0000000d1198008150040e002c0c4000100b8400049500009112 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 965843588 1250 965842338 965842343
    0x9010513030b0a09021011030a1112030108010501081603021008190f060602150c07140f0109030f0906050a020c0f010504030b040f05060c03040c0b07020604090c02160504060e06090a0e0a 82
    0x1aa13440c5541103003031260003002401e0031410806103140f407246110b55a441664520010440d4500d442211b00500300401c01c0080110303e6415102c1da101c80116000700402d100300c001074400ca48248480580c0c2658041c10340ea00544941c42d070403100b0b2015a10204040c0c5215500040a0400d18464846210340b0507008c420705004200145424002450700314600d1841e0004451101402201c0003010304480540d50b0007091030358010a016040c078140b000b10b0701c0c40185035080401c0b503030415070f0001d00c0805d84070361903d5170840b140d1907540844140c003a0004d148007580c00320810050500d420b400c100500c040500d401450207482c0d60700e01503000010b8400b101c840e60f204aa8000f0001c0070700c51742e40d00000c440301560a626044c2c650404814541c81030013180c00001036101c0070354603600110703406014041e5091004100407140299640c0328082000c100340012440810103203028003500c02166040c846c1c41505444820401c0b10480300500000e070020740e68005d240100c01c4c14080451182d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 965844838 1250 965843588 965843591
    0x51e04150e090a210c1e020d080d140106050304030311091002030c0c09090a0b06131b0206090105010812090301091e0605010915060804231f05090309010513030b0a 72
    0x40645880050135140444400c2250300b2100100e550990001d210300030b07181c000c0c040c5000c81c540c0c1c0c20340001a03850200040d4201c0165000807042c40303883d6008240b03c0c01f2402c010400b00d401081c0601440b8428000c0b03500150b8100301080119119400c06990030390040181032515148200092058030001381c50005a0800300b444404001d050140e85034094081d10018014600004210307101d030032181c40100500c0744440420b03450388401106400c1640341040405ca8a600350300112007500e1441850700042c81104009180540103024003412606480000c015049880e0155403041d0804000c282c0c00d0340d600c400900120701e4a401390340030030a0001c21100f42443d282428000e68005811500b5900e0500c4070000008580810110444507d80382010498032140f6207407100445242d5030705820440b00c40c09a814a4010030781495200c108404a1802160203192005650301248c03000481e41042c840602954022030080188650800c201c900032900c2e903498005002c0142c0f204071009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 965846088 1250 965844838 965844853
    0x240804031d220b030307020f01050a02070b0304060911030a0803060f150f03090d110a080306180f01061101060f05091305070816140a21051213051e04150e09 69
    0x1c076858412000c03040300990185282c010a9008142c002030000c100ca810800001412f40303610b4402c3c030507031001d0040e04500c2036480c2480d091000150602d00002d41d400301e20203a11348144c1c6000150396503d02c0c1d201e08036031f045503110401c11421350840e45030281c0020894502480005242c00101556100d1007400c0c0d8603400d08140c503e05d40710034010083e083c86440205030110300f0000407681e0800d43d000403495501e0307841001007400b8140800600d441c50070f8441c184655000b20f030b5840d605a40081d0b5400f200312b0424072007a420707507000d4440e520002050030310074800703030803d06c0c101c0b42d000d214020b105844004554132035223050001c1e4805078944c6c01000040c4048410942950b000f05505509108014035007000102c401440e8411511140d50007540c0ca407020001043e190200360b048001c2d540540c0054a40e11443d43c82000101800c00c2c03130103400b040c6407030001e50010075020742d24606440c8a00e0502480014000c44048a50710a005c1d04006544e00d0404c80051181310454042e0184 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 965847338 1250 965846088 965846149
    0x9061c14030c15011d09060f0c0f07032c0f092e0e0123010c060f092303041a0a0203130b0c06251409040c0801240804031d 54
    0x1c44c0e005d0000e041c129003040c240480c07808005000c40c0c000c4541c4100000e5901ca41c05103041500c00c0b00c0408050300008662117040c150810785410203400c0303099000c0005105441d12207a03071180080c1040c1d1040e1011030100300781c20290001c0b40d10000120000c0500c0005050581901c40380050341610a1840712007401200c0369044107a0040c0b445418524580110100c86400d10809013609410845181c1c44035080c0800e6400500d641c100000042001018a04140400f007043c404240303000c00040210075400300000040ba401c40f1400c1c1030102030a0190b58100401d0341c0455401021480148038080941c03010b501d0304001041c0f03103c9021359501407404101d04081008001203144a61100d4000d1940c00b02c902c0720308100c41074508150400c0d60401070420b40c1c000c1c880010b82162a0103000c45e02d40d500b04c2c40690603100e16100701000d008000b118140018407400c1140000784400c1c02040019001c2c031030304510034400c12000404180c009012500c4c2052001220302d00300c0005410144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 965848588 1250 965847338 965847359
    0x3070f2c010810140c0405100c1b210f15091718040b030c060c030403081306090b0f0414120d2a0507031403040b041409061c14030c1501 60
    0x344005013200502031340c901840c4400d11409641304140c02281c000909018051041090f041503079840342180b04c04c02c1ca072541070a44a205400f40303082041c8105803144005404a003810102c3c2c1e03020852001294807952035040b0102c10540b00d0f44196100c84c5640c0005105502d0714025404540e40c207a05c6085406510000c0ca607003000184c0103500c0c3c401124030700e803000316030701406250075143c090341c0c1d030842603907945103110b56440945280b0003c220610900301c0f040a000484245595a104894031401c0d00e6541d8452180e00b0120400204400c0003220351030002099034003801080090414040702c00c1c181072941b400007003800580b13040d03103078000e0241c040001c107800c2d00312030b003420400e401517a1400d40e1242240400317008003401c41038043c0d0700901002294054608010700c42c1d1102d559080001e02e034034500d14060301c50129140050350301e0030620781e031960031840c440320070303119458035140c10b01300827042c140e4641c03940810040360804240810241c44c1070440e41412005a602d0400702a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 965849838 1250 965848588 965848601
    0x60303030b04140609070305150406030f020a15020c15071506060818030313020a0f0b0903120f033921010b12060a030b01060c03080603070f2c010810 66
    0x440c200c000000c0c09104d0300c0300c2419983c00080c6e420000b48a80702d018036115140c0a8001d09a401030500802200b04001011060020382c0f081d1822015275480d2000c07d00986503011400340164403070312811900303141c220b41c004074419400000515000090b29440c3c5401401030361141d501d5201c0d5020080d0503031060803998401822400454410989203031240c882c4000780c01c00101041200c40c4205540e200c0500600a1215550001016503110701e00d11903600650b607854130a000c7c1031f200c0801c080b401400c0f42e03130034001c485030689141c0d601d00d2510034030084020400310214891654130003084049502e007001c42d000350541a16400a41d607032000c4442c03140260555044010300401203041024190f40c0c011651440a03105aa40e800100d04c502aa50b07002414204610000107082900100c03102c06440c06680d5224166940c8800c0c140d441c4050b00c141007581045000400c60f1a404648060031400e58501d103800360042889140c2d031141080c1c00070611904407040314440e040451181c2ca = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 965851088 1250 965849838 965849861
    0x1020c0f1c050315100f1d011b05012c0715090308070519230f06010902070311030d0e0f0706201e030a0219050706051309060303030b04 60
    0x801001140728010001c08018041c6081409070200104290301100c00340b4500800010340008000081c05034010400600c101844000c2080c034903064204030002036030000c80b198181c45a4980b0351004411800086a854060380c03503550300c031556100c00402c51400e078061911300c0b54868522084440a5007407804c02d034810582e00c0c1040700a9004190000f41c4081182c1d00425995107455860804a05003401c0320f00b45000e50803100100c00400460502d6a0648000d030081101c10800c0603500c59540c050020846805502c81d2004116401c6550004c00b006840b81c545020310000d15000949150880d5060031341c4d590303c4e0445034141d07003403c01903141030f0804100280603071850184050044044403580d0b0341078035118420852803e034100450108208400b00c20003408600401d070a480c1d400c00001c0c640140164003100c03000354101e51881c84500d030014040d101013440e020040d6820f82c0409101225115603c0000607107034014070980c0700545c080d40380440d01d8000705007008121307501103044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 965852338 1250 965851088 965851093
    0xe0c030102040315150b04060306061106071e02010b090f0405010e06150f012c040f1a19050916020d09060c12140f0408061819110a0801020c0f 63
    0x40000c68601928140d1061801800103200003105e25203c2c2c03807481c00d070003100c102040000d0001c4c3d19a4154041012111140c0e107000e81c0420f0a403425807503c4080c4c0311500000c82041410385450b0664189260141c02400000365054140f004214110004c0b24182002d81250041201b8424203020348031607510440054143c52406007120b6039000c100543c028050b229080c0d13078000c580d0251290000a12a4041500030b00a9061300c2c085100900c8000c00d01035414a09030b100c0203030040c010540443c142c00d6442840ca40880207010a20344c14030703018642500c858400041648030400c8540c003481e88444004010340c4940c4d0003901e480555620305041003d010010040e10383e01c0503c000040d6030285030307000f4070801a1002c403602c108a000000b00b001c030004490004e5040340c40248112090700d01a5000350359041480c10342800e1201d041d034480d4121810741e00201130b85007085c1e1460b51140800300c100388194800f150a01c001e80d000b40d181a0340c0013810000c0321a0030030110702c80d650010f00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 965853588 1250 965852338 965852347
    0xc0d0509040c09120f08041a0c1605060d0510092a09140105130f0f080f0111120901090501020a0e0916051905160506100b07050d052505010e0c030102 66
    0x41c000c41c1c1c030315a00000e458a61114808010031406d402218000c19800d5900c00c560301c4051a280800d030300006d03141500b07100d4000e074032100300041c2d814881120001000d2506060a54503080090040200021030641c13920001103440300d410700c110b012199065071070140350348800701c001e540e40c1c03012035105051144848003080141c44c1407070380c00f000b5a803c0ca0078a4581b1450510658410025040003211001a05000c2164150843c0c070a0071100354804881000c18292845802c035143d0108540040e1420000c2d64100d08080041035040259a0000122082c8685480b0b0880e000072101200046401d4610841480d010742865000740301e000d83e5041d034510a10019020b8820000c44802c4040b17260070a0400034015429641d01d0030301c040070030402812900c1c02a4807038404840300d4980c5000c0343d0011801075194010340722441c1c0c2c003100400d11800c0034030058420381c000508092240c1d00301c4d034219510014690030034550521078000401c0180c04407106505100031108410301a80c414030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 965854838 1250 965853588 965853599
    0x90a05010308191b05240c04090b120703030905040f0506130e01060f0e0109140106091a0904020705010b0306060f010801050409080c12090102190213050601050c0d0509040c09 77
    0x408482d18540c4400c606215003402003c107554402c072021a00c1089580a00800140b050110b44411000c1000100c044082c6510440c43d920020650b541a6540d006000512a4208aa1001c510303000c1c010a559081c0e080320b40c8062600c4510741045001690071a020403803070410340a50482070002c503406029900e045d01c04151035540ca4031018958940700c03800c0e0450098298854806018034a00c0d9041c855211140c1c141402420b100711031100d442c2112904840d088111914107030b40e529520083d2040c508407100b04048041c040c140c16102e010485648242e640e44000c003401c81c410710020480d41c151004145c107000d40100b8641c001d4519004601e40e0740e034015100d0703041d00c1044400094420305410303c03c19074054940e00504920a0320245041100320801412406009038211904014200519110700451410080d00610324605d4040190700542045034004010300d0134504100360100200d00c0c1411880327444000c200006820b031480d003800e000d070000361456418200226407405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 965856088 1250 965854838 965854853
    0x1c050406033617040e0603070501020106030503191403011701200d02030a09060509100c0c03051b0a0203070f140906060912010e0105010f060e191e05030604060209090a050103 77
    0xc0e85154141c403018889041000c0600300000022245070700a0b125520365000f4145c0641c00c0d103070f8078441c0c8158000055150310500031201620f604c40003445c2002103440c050f0b11040841c1c9c03c11010710902e1201d80380d140c0b50b4480603500074400700707043c081d081c4030011807242103e00c1c110b841c003400540c020400d000100e03803030205d421003c040f03540141d8903550901c0e000f004001c1c2c181d0041415050006102940c0710000350241070106d1840700f0424020300d40d20690380d900c0300311401004110180982142141840100700080110300150307542c014169002900b04100d03500103071140e0010711800c0c0910f0481d0100e070a10300c82c00351004c3c0ca49040100c0060128050001a113100304001d821150060700b080d0040c1600d61401c80c002e006658582e441902c01480310b014010004030340a842c0b146c90310b4594441161440c086c1c0700040c05c40e04141050303088890f00001c03103040d0419414000744503101006040d1045014040068445071a2010002848800790101c240c2905003401440030804d04c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 965857338 1250 965856088 965856161
    0x11d09070f0207030c060503040b090303010e0703021b1002041424031909060b090a090c06031121071e0806060a0314040302010911010c0c171c05040603 67
    0xa0414942100c0070410803440c0080da034000900041c1030b5680028001d0b00200514095403056084c440c04d50344401c0200c0d40c0e40000d10644c45600417105c0421041d90103580240108030000b00070a25140740f00b03098a02d08540361886940782940003604000c44490132101074031025003146d004c5681000008231404491000c400c403140340400101080754101005042d20144d06804070a02c58180d8504208008060340020706009a030f1200004d60ba40607603200c3c00c150150700040031100e0600340203046000b450310340d0004036a0141040040b110854448410034555811203c0d50040c2c0341c0305400601c116095400840001e410801c41022581c1020a045c3d000100391400c5443e20380002007123010705203030380d25045491001d00a0005155064000300340d000e001d9802c4008001c2d01800440b0312908003400a0003d958812040c81000e40c510020070181403603000700d80b0700700849091040c0b0760b0341c0038442e4004108001070410286406015038141d0800310000c0c41ea2012070500d4a8540c1d005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 965858588 1250 965857338 965857351
    0x90d03050a0c080f0c2802070e01030f11030c04020f0c0d02060702070e13020d030e01022e0b040b040204120b09031c0f06150c060e030a020d050d0207170702011d09 72
    0xd400010244007401c410b0386d1410b205840c503c254030300f42114884a81c08900440001030168001c08544091b41074041c0341220340c03005080034848055182c1a9a0380c10109005a03d801000041032041c2d0b0350303001070400001041081036644d094101114500348801e904030b0306541020040180d05a008a104011070348030005228059a65039248080c41c03801da032009501c50700c1c0034140740600d80d00c052080150345003a021a1082000001c0e090001c128204242c83c1c0c281c0c00b1161039036102c500750400c001c2d04070003030400700d120f08030040000c05a130040e81001d048819409426800c0c4806d03c062640c001e0b04c5031002d0b610709400c01c1d0041c5284031010088100441e224107040340801800d88c0030038000c10169912800409080c44024103100c1030503c00d441541c14480440a092804800c0701d00002103034004020000e1011010354060b00030484010391254241300180211700c0c0701940c031038036425006030a0b5403002103100251100c03620b013203241903400b03141c0001400d0340c441824864102a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 965859838 1250 965858588 965858611
    0x327110915090f0a05070305100510030b0d0501090312110414062101290306270c070215090d0212010906020d090c0623160506090d03050a0c08 63
    0x41e01c030029155011510a2607580201407401000303c40000b00007014010700b1207803014041916101012000d440c800d50b501c1d5000380844100300701c6032401d81e02d400c0ca500445d007400315490b0113800009076147d12003401a5060313511003c00804250f403028804082c00c107145400c01c00d8401c45550442d05010f01d00591070040aa012054071039a105011b0b0b8540b005003010320351207000402031101c0074600c00c1c494000a00c2e042005510450261904207a800d0b80b004203e070704540e265010045c6810042d0301c00443d08208423448000c4c5418511640d00c00c100206025035601080c2c414420400648100300c141690f05002c0e400480d6521748011580a404442000d105411121000d00520032004003c1c60b203440050740745400c0c41036402500a2600441c6c609484036a110425500d00c1c034000c40000c504d000003580e0708a4900c0990140c81c4d00d504030300c224103a4810715600c40b031420b801074504050952188650400407545402042c0e801009032800384620010b100003d00002c0c0060608010035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 965861088 1250 965859838 965859841
    0x609060607050303090703050f0703081c021308030711041b0804030e030703050c100306030308130f02061c05100b1b0321040312050f07030216080a03271109 69
    0xe503552000d85010325000001d8960b2800e00019035503480d0304900c002c8485000729010010b200b2408a2070904994000071480c0c40c0c4480021015070306a4411000c0755229428460713003016050b036183c10307400703040154002c40d910005c50330a8808403141441480c4101d040103c100e01c400700050000d0302c101344c50b041004594443d45000d4a070413500c815450380512910000100344540091030301880c00c0309540c80100607002110843c26180e59010190100d15600c01040b58107003041081002d0502070440c41c8001d0b0003d5000850f190312100c6190040201c00070440e000c003440f8854690030510310286c140d0b40d14070307100419025010300e03201d041030b44210350940e840c2c4050a0045034210340000101240000150fa254410b850302030703c09800040c0405456845020ba502c107090107024003920246465581000850281d0300401d0340340021000804518005040d0101a00760744280d0785007c03c0c8042c41e400035a4441600350200b110000c60f46600c5c501041010003000b4180c18280e840302d095 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 965862338 1250 965861088 965861101
    0x70c2d0b031b13031506030b1b03222306060307150f110604051c2c01051215120c06030601030b12060c090112091a10081c0f020303010e0609 62
    0xc041c03c1e131000d42240c0171401914881c6089902020aa034483d1000549985504016000f50618520b81c40c030161402c1002c07031064201907001c010500c08055050302140610340c1c407040f0084950b00c2291118801c034540700d0bc200800e201c40c3d54801c40903070045c005545840602150300c040841d00c44140700003540040b56030380c0b08402142e01014042c04460060400d071810030b90380c0c107421002500104600051049151044442c0b4584034102e0351007481e0101c6000c05545040340c00c910441c14000100000d0052050485130144103125940300d0104290400040c8858200744506624039a044005066956a00c4800b643d4005500b0320b030000e0741c1180400860220f852003c9400c02c9841124104158100700d00c0040044a07400e03620b6000322140a801001581d44d5103030000d080c6282c00144007108403032a8052640308a00c0055580010b558111032804c0c00c200b204001100d00500920201c3c1076000001d000c40b0303152901c01149103601d045100101c202c40502102d1003000e00c1c0004c40d03030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 965863588 1250 965862338 965862367
    0x110d030c0e0d050f0d08010e010b030601051204030f0f090b040e0406090c08010507090509061833042d09062702041d12070c2d0b031b 59
    0x14407100140030100001d100d801e007581d0f02c000194910040344a15071504044038400c6c030b141381c101c40b480c42040310341d80d0808442c0005601700134a4641000020300c003100c81807800c0b40c47c0d940140d0080d242e5494280401d2002009620941e5589041c0607614008010f20308985044504940c4000f1003903100d07032114a0450054014603d014204480d40c01d00811000704c1980198007944140c0c0307420060ba951401800384421003242d906500c0740502c1d051141c0c10108034011540515840e00c0050b1070080031030750055100c081440c5210541d121072400f4507508003449051495264a42c110004403508055800c0d4211000c18101000c0c2d140c0c500f900800c65590007800c00ac0402400c691082021034103420a4400118030580c821414040c4580b01c4120b44032148114002540c05000c07983d03d04a084a410f51103c0f208071f504411009000860300a501500d29010081a84903090156010101003802c042e0750420303e1018405c04c1031010701d0410001d00300601d0003d80d041034481801119115 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 965864838 1250 965863588 965863607
    0x305090312011502010c0c0f3c061505090c1e190e0a0e0a020c070305071412070b1b0c0d0302010b1203070b0f1306020a02061501110d030c 61
    0x8803000100001203030031407200d081c0b941000f44582c02000440301e800003c943e0000c418030090004140d001c542808602c2600100c007039644409411101c1d84c010402040d041080024582e5086650401110070865640505841665000d0082e8881420100001c0444c0d4000d0030810203081e00062000c807003e801340c5c0c140d010484141d091901c6002c0f0181600407070880d400841c00049021035503040318502207124038152821907074542100e59a00882c0300003540900501c2800703110f14600040020030822419000d0003142a00c4030545210a040c08420602c2408900300d607004180c007401001c00580503038451107100000c00b209074040d035080310700742000758a006402420800d0144145078054010101010b410365050301c4403008400002c2e12402048402050103521038081703901c502c0303c00242500030795107035080c44588010740e690b442240c0c0004002c08c0075820807401c206903219041c1d10035885140a003080b507522845000b8050b11484042021300c00c2c19500c1e80350715038081c414400c50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 965866088 1250 965864838 965864857
    0xa0521010e1902070c0504110405030319090b07080d0903050c0105040c03030801080f0c0f03030f220609180f0b180a1803090e04050102270a060f050a03050903 70
    0x24401540c4806044608410071140600079120300c8012615a507420b200315905113400c48890b440702070410003080003a01e11007160a035040c0b814080401d0564090004203903008050304022054000c444d0050950f80b4117a10a084545007440340a0100d44043c088030030108101a0000300352800d450305603020f00601071800f0147d03180c48100020880c0c10303c42081138030300036110a50140c1e2b903641c02503516103840b6441d813591b4002e81c840e15250304020410a511020080550b424516a81c8001e4825041141c489040040bd00d13848100c503813030b825030140580628940050294207080000035180c8491452070741060b030b203404420712803501e9403000d90312640c0103054040d641c05182000600782000d0b00c80701480340c50700f0101030084c09031121140102d80d05840c2c801600340b414201c01030b22a8010001e90f01c554082040e0260384144d9030080e6226207039140c0141410700800300f4030685407140d8218a00b84102d120305e02d9607850b00541a10f01c144010302c0c001c1030301e5480c00a0385c4d086004941e1319 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 965867338 1250 965866088 965866147
    0xb03070b22090504140606030c010804061128030b0a030807050109061109042703081b07030c0b090615060714030a03061a040f060f0507120807090504020705030a05 72
    0xb161a8030740ba005580074034003a0820b00011085c3e02405501c4441c1a140b40e903050b408000004c6a6500074014107610900440c80000c0180c4101007041e0151307c142c100c100c00345442050901c115aa02010807640d2000d494100403561049000c108034030024000a0000704001c2201401c02900350858225107500c600305101c6200c41c200011034a41021103454440c42c1040c507002076403040c40345541032030081403400d03860210450b101540c0c3e40740e0191a001c201c60f0002c413120442c9000a00404103144a6980c0e40541c0e00181000c24074558007600c000c40e1f41d0020360500c0400e0703070510204a003a110480e5003a503031b030049242402010001408480c0c00e40004035980420300d0701a4040422203001c007080355500705900c0c15141c4948151b004a02442d01d101609001a42c030450081c3d441e02441d0605600c4c101c503640b921079484e0f83d10740080001861100800400540c4030710114014502036809505265603a5900c98480c0207142c45102080702c08960060041c0706007070110340106400ea036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 965868588 1250 965867338 965867407
    0x5010c1b0f06030e011a0d0302150903030a24030201050a0203091512090706081f05120d02120a020a0b060613030803010311010804020d0219090618050a0b03070b 71
    0x158076404420910588021900d0511090343d00f10041c0506000000060040c50504d49014100480c882e901003059045216142c8404010180d249205020781e2104006503101d1403d000c109081d2003085070041070410003480c1301851103072202c0ca014150782c0d0908001d5100c08031420b0483c034501458058540c8078034000b554885070303d0240c004116070042800c1c0e00703100d95111403820f99155260720400001961200000d000b00f800240100140c4a4140001d030a0300e0350780b170014140d546c5016151400e50800c41c64142d400d6010020008801d4110f04000c0c2070940e4170f04041d45812200300e01500c050791820001e035070ba60711030007210300510404024840c404d4881c100204140c0007400304484648011100c10203540c001d41c5014860380d8010450020b1075070a900780602202500034032400340e001282d020130f1040c1203000f02e4000c0c000600c11103d040e0288030000c8260f800c041c0905410a2400030303404c1440c1c03004103280c8260341c100d4520565924007105404101c0c6246503084020201805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 965869838 1250 965868588 965868599
    0x91603030206063a1703130b0a020f030c0918060a03170c0610090c140301050d03030f0f0b011412010b0307050d0f020a08060a05060301170f03030a15080102030408030105010c1b 78
    0xa10143e040e074082c06000507500045045c42003903100c180c2e0f4055020105800d02400225203507980390303200e61201409070404144d5a804d54240e002035900c030589460204201e020360904000c2c503400204040b460191a05120011a480100c10b010242185a60301c0d402086503040c6800c84019040c1841201d10320304d0324901d00c015841403400f0f0f0303140950900940c5040c5c01c2c4212800e84190308401d1100d86182d10b814100440703058000c40860a058580740f8040c2e41481a10500d070690710701c881e010482140c00d00004020004841258a80d00820b02084060501d03400d41c40e41512010341e131440c0d603501c400d64240c03100c1c0500301c007100e801c81c00d0903030156030451203401501408400b901d500340036454580400450f540280a8142c21040030720040008625800250400925a00a8510703148901e540315046500450360008520b031524034400e6600c21030401e00c4000c02ea007030021411401c26a4036074801c0c1c441032150a04011070802580300303001e10344141000d26070304094002200c03991203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 965871088 1250 965869838 965869939
    0xf0d0803010f08010204052101140a1b140d050402150f070c090513080d1826120114010909050718080a0b16050714030309160303020606 60
    0x90040708a8803441080c0014494814000d41d026540000d150915001004c00d8510b00d01c2c8d454148a1807540d00c981828288100e900a1140100c814607804145852140900c1d030700042d0042c101410040c030000a00800110398043c0c1d142500080f40200e42078556000081802c040c0c140c0001c0c5050000906814451154005100da00d02c01d21040c0c00050f50380300342c0e82c100c523000c641e001f02070281201202c001403030040c000d1050080d00c0170f000900701408410302d1580e07442084100c820030340c00440d030a0600b1021035288010541d408001d0324001d483c150341d0400501c18451070010f002030341e091045682c020000b41018041c1c0b5001006945005000100820f6110741c003004141070349040071032040004289034078100d0300296007810300d4895000c00c0026456119811003000018021203000501003104101525024801540c82c1d0502d0251030382080c1c00c105288002200c50310040000a8020541b10352044007140c1e404000c0301c460741c040001c00b09040c0341c00603096610b0106086503002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 965872338 1250 965871088 965871091
    0xc0302061603230a2d09090b0d15051e0f15010906020d08090c030708150a053706060c053c0a0605010f030308130305180f0d0803 57
    0xc3d943c0c0840c641052810300c901594100f0f0302c0100c0c00010041c074060300b4050f000c0c400464049540da0f542e960200148601c031240c800b201403000032aa0481000807001a0082d4204480121848400b012840e520400d00c505e04000865406854400052007510f04000314000d05807550311151b5580b51809440b40e00c2d8004072401c0132882030610450381254803518409041d6041a001805820b2018400b41c070110002445414288614410154a0340f03040c00f20500030280c003401825034681c45d41200040708030007840c10114500c3c000401c42040c000862041960242da0900314041c1198101c40700b40740740c05001c064550f410403200059599200002c00089030181003910b0341341e160900b541c1ca60701e4540c810684903110b000e10754a504400f200030700011040324000c444840e070700355071800d0540300709070301c000e03a1a0342d0b0300c0081080c10341101e400d40d400600b02e601e40115920300da0b030180c00c50280c0c003290402c91045584502e8030351500040f401e100200100301c0d641d4040b075468105080d600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 965873588 1250 965872338 965872343
    0x102040b09130e03030a0e011d060108060c0a05090402030a090f12110613110607060e011b03140f150613050114070b06090406090605100f060e03060a0203040c03020616 74
    0x300b90081440e440120f01c00c1c000c1e9407036072001640c510348401d80440b0107000404500c0391195030700c0d500d502c1342920181c01c200c40c0b0302204016009940c9025401403c03e00024039140700420100801c0c07808a61020869072041c4003243d0040c0c07607481c1c114001008100f4040c0041c03840030b038000382c80140160321210190b0000c6070f55804c000d4031031003050a5102c00c02520008011184c03100c0745000541c400c1c5c1c246143c020064031150a050054941e0310645602c90050195a551001440d0040f01c0500742d400001c2c8441c1403c1c0411644000f8296009a004105c490005050404240104043c0c200800985070082c079407074568031400108004507060384200c901081c28140d5800d01c58442d0b000342c40805400400c0c00b041e0307903140018091030140040080b15615660305200f8000344842c8210303409642d43c030140c0481036060055548101e4800e400800502c000101c143c1210340d40010308690151039103d01507200e0b01d561602007a0707442c1e113130002584448082420f41004c03900c058070030803150 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 965874838 1250 965873588 965873599
    0x90909050c030c0f0a1701090803040b0403030c09050303070b0c160b06090708010302090c07050a0b0a0510062a0c030f03081906050d02060a2f01050a0203070504260102040b09 77
    0x448001080703140c3e013104404035000006841d040100d0a10210200807082d56200040303148200355480301103541c0100ca04036401d440202c00d1205160385842170b01c545050350b05007029081d06000c0040d5503401a00001000c0d048000001043ca070001340580c0c0540749900c1616603150050b243c1607818900484595005240e0800000d001621800b1514100c0ba0040c00d240036649904161848561201000341d480c1c3c805d0702e0340d0b100011050100f0700d20134407143c10000b44c5d500781030310f020803801e196030720200400039040b0907070a0078a01c02c0243d403d90f0030018150b4410b07084620384602003400c00d40c405455001011180d8042c140c11030541c0f4070542c1c0c11855680310602c11503988003281c600740245074110503a000c3c0100141010401040140f685041520410b0301210402d1000e49802c0c811440100103130392808042442400b41d0b0790040d004600c02e606510b40350034010328034020b9200740121000102c2d0b140000e40980d003000300708000f101d0001e664560311420700420590042039001c1c0942c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 965876088 1250 965874838 965874853
    0x903070f0b2229040e010f03050f0a0c060e030c040204060e0901090e030d020306221b020319080403050f0a0201051803030f0103150605061b0705030f0606010807090909050c03 77
    0x4103425190720240c4880032001d10281d10070003800c0101030a1080280540f56081001103815074030f07040203500070911190012401c90951a101b4217045402c82e5541055101c1231101c00024818221003090307404924000c0348000c1020000383c5881c0381002c805030441d1000402061065010382c5440410106071101c44503a40c2e00c4e04c005c030495104d40041e0a83d44c00a21001d81801c007542c0003507420201c01401d25001e5030070402405a116800c1034501c7c00540d850300340f4803880301c80c416055000540340c000303181031079240d4520310305460750082c2a20810140c4c2c03001608041c01981038840710a1040301494585000c4003000c0c3c0207200955521800140c0204890b0810f000042128840c1c40e40d400007041c944d20f10340d02d5140620000c8030544280f031301c8030741c0416a0303243c0c036004d03110a244e21101a60b801c485084034504158040d0041c500039004030601c181c01c0c080000390070b40c216400b8644010940d4035900c08464040107038010100d41410b200221050090001d0050010b2034200c0685028 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 965877338 1250 965876088 965876137
    0xb0d0f060b1801090c031e0b0102102003040302120c07050a0b031509041113020403060b0a0509071409040c0f0305010608060a180e030f070b01060503010e04080903070f0b 75
    0x5403078101ca0002c03003420301d4038014011481140c1080901d0360300c03401d0102e84403078044201802003416032103102c4540c0d60354451000780c2d0b0f81007142d0074011203100c40c01c1120101c28100d0760440141102c01900320070b03000001c102094401c01c20b804481400024068945007050a015101c140ba80b08851003810f0780380c0d021418000750b00490f4054460500300c469401107542c01c0c4007c1400c018026204076030800345403601c0e510750045038004c200c08041c0040c1d540c2c0c11032511904a9006012480c004c2650140034009602d800048079000001e81c102029404400e003042b40d8070340705810b42c0135002400c1a00041903c2d820040c02122200591024400d43e82c0742d1000311000002214410340c40915440208a08040c035076001c032010000c0000450302c100881c0301c1c0c9256910211540205100000d445000c0c07010f02050711707000d01b42c035181191565242c00e10000341c0e800060000380c87c2070000150b0404c582e4007048444000c104100ca0140001e5603420380401035085188041c110400b0395120028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 965878588 1250 965877338 965877349
    0x9150603060e0709091e0606050d0e0f06280f0902030118120e0a03170408100504030c032601060518240a111f06080a11060d0b0d0f060b 60
    0x21030700041d611350f50410f2400307001d64050900f080e00320710001c89003030420b1392a44581c06000040d15860310340e203a948010900510032111840b940400a0f0442074117200e4241001c941c0e42d40019a280003d10644503208117120284141c0301412207003842c020ba04164600785070401950305000701c00030021400c0781c490b00400c4030103810000386589154a401710707c06002d401c6c1d560000c0307800340c8050300958680d507842410762407c584810100401123010840840c0802c418505507280c41402d00c054101035030060840091401c00405110560495000e81c081000c26403412400b5000c0f014415652105c5c080d0540d444040e201c98940121602329040703003424060300b10304160101315402c0300011800540700c0d541040c0c840104100346d0158032000f40c03d0030003c04d41e82408407981c8034102008075003c4401c841c55079001c01800d41120f0000d00c0494020007d00368002000e80d4078595035010700340060010311b41c2403240c070780c80058420000f041c000f14007902540940f14100c01c00048005004011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 965879838 1250 965878588 965878591
    0x914040c03121b0c0305120a02150606120f010509060f0108011802090a410409050309040c030e070602070e0406020904110729010b0d05090709150603060e 68
    0x421a80c111101000000d10b0b05400003003800e103d180c500b10500d1150902941d4085240c1d059900c1c8107100010301c2844400d2260303c52410f4401c100354a0071003e00c001039116050907800309042105440000c00e00d80300c4800700c840c2d54542070300010701c6140800700700c0c50401c0207001d40d0f8068507080001991605000050b400707030150585421990341e20744420038140e14582c00d03513400566024071006c42d4540351040c00340080c109600782d20750102ca4907000805081c0780591a140614031140c40b04c03038110080061404c100005640c08240c105807170401915503c0307600e04c1942c0043ca40020010420303419400708101e0310000b4165884965108412a91000a4041d160206070444082000101103900420510901510200c1c004030001810140b640200d001a54580c0c0c10034050840076802c00489403034000c1e0803e601411b5410116001038500408e80d29801640d0f4480c0462170600d001c210003c010411a501444650000048442c10317220034452600070034204500425664071090805 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 965881088 1250 965879838 965879843
    0x90106023012180102071415010f0e040c0807060f030b030a0305030f090c10080f0702070e06010c0501020f040f03031b110f01030b0306070809071d07080907090e0601091404 76
    0x16003030510105038160b0514019224803c2c00e05081d4112030325400038001381118a00400170041d040f0350018030a0b080c00c051050035142040e0341c0006018405814012400743c03400000070060740d5440e454000a1280b043c0c000807c1880f4510000814648c44113440308003250540e02401042c44083c18550f540207404402400b19006000145810f00000520f80d8841c555608980c51181c00101140788014a4080c4000060347d44040020440c2e60180541e04010103200410061b0301d040c0c9845c8020401034007060401045107016001d0100035010f4421070394440900c1d681e1035607910401d81149007548421804105901c500740030a03180d00c00820911500103803480c0071502c0000c100b10003c144e00c1070150505d552103071980c0d11a141041514490f0380c075600c4084050600426061515a40ba8048440a50615000e40e07a541c045030141e5008220703070074800e074aa2514607109003030203520340080300446e25046812411034800650380d4121102c4080400c00a0116001e120a81c101202c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 965882338 1250 965881088 965881183
    0x30323060a1212030e1006031b0506120c0a0903061b080c030c0d2d09050705220f18030203041d010602190201030f0f0209040b060901021902060909010602 68
    0x10f0920b035400307500f12038001a07007103081e5082400020444000c4a070103800646d00b0391a4465003480c052810441000908401c461103400c15070500880b5103021402448e40040b80070201c0d10000003030040700e548004c0c6500400c248041400503d9142e080b081c140502d9000070308400200d45000c194208a80c040c6000081c1549000081c001000c094080d1003958800b800c0705410540031000e50b03118041410030021804642c0d4202c41c1401403034000b09410081c0f05452010151350005c02d08000f1a000035012180494810800d03c9010f000f005030900c104a0070b004440000101070307001c00100203491000240345641d140c00d0002c074101d00824021040076034000c030020b03004d04403000710441529105144c04140300f4501d180c000103541e00003450111450300440c400303440d480c0c18060008134003c10394500781454a1400002e6440603000900100040c00f0130b0b05c0341c20740d01c40108071201c01a0203408070300d00b940d4402000b50b50318203070302411a085111340704a100300154800090100c0080252 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 965883588 1250 965882338 965882363
    0x60b0d02030a1b15020616110a020d02040b210601060f0801030609171303021206070e0907090b0307080106080f0c0d0e071e080601060c0c0b07030323060a12 69
    0x29400490200e00c07020350380c103c2c0c2d046000550500c00303070808500c18099a000d0314050500f8144a101005907006c06014032028401000540c600041c203084080d8040740d10700312500450010800500082c0d4030590000007820f41c0c001442c4442015a040006c40812520703507030380e10344040314105c0c0c0010490000600aa00400200e142078000c204c206010b8041c8210344541041c01015a500c212540454504182000c0040d80341083c4480180040c10018080c1c920300406c0040c06d40c440011407501c1031001102113120b0ba0300c20300b046006051350a2045581c4c3c200b503580502030743c000b44101d0303000403051400255a4802c41010302d0090041c0407000782002f80c0549024050843d0b4414a00f940c440c03500000307903405030180c4080e80e04003034000c1990a242444032260074860160414010b2101e050500380c00500446861030880350114861038a83c0414607003203000d048920b80011008106d03041b9140d0b6103080728451402900b00b00c031528100b680d9000c1804e1400d4690001522502e155a03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 965884838 1250 965883588 965883593
    0x40807060203040813270605090115120c0c140102090f1e0d06020c010b1f030f020706021b1c0e0d0305090d0605190e0d0e040e1207060b0d02030a 64
    0x40240d50014400c0e81494240790142c545240703001459401580c8000860007160010b440705040c103099446d103601e0900c103280c2040003080701190184a601c400d480403208668400784103042c68040c03400354900601040c0307210703203004000c2d00f501c45c816142000396186402c4001c10520846601c540d019005620034140601002411880b0b542c00d0a000340c01c9142e0002c460395140c00901c4a1442102c3c01030325054440d240c00d01312903c0003048d80c0a085001c4000404075040f80041c0742c11a020b240204d2003c1000b0502c00c003a00460f00002c02107400802c00341000c00e4030072030008580c15200c00f103410780036099100707181a00d03056000c000415140e030840b89143c00d110805040c100d010b800e0407880c09840c2c50200d03562000c0c034038080d5807540d921401c0c044181c420000201c0f00040300b036400e01c520110403c00341d480e07042d00c0140500703004070340c1701001d02ca4079560401e01540c030b03000c82941c0c1038203103200803140d5a40c07104104948503072510900d103c941c42c051001074242e0f50080e000300079600056 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 965886088 1250 965884838 965884841
    0x11112040b180304090207050606030a0b04140c060403080702040f110405092a0316021f0b0a380c0c01080702100603030309120207140103090606030b2d04080706 71
    0x240001c01080103082c180680b84008200070b000400f00440b00594130051410818101000034001d24444c0d048030700e41700041009491040d0b00184c0041c45580c02c240300d9a035043c58003600b1600d450300240c004c540003003482601d50140924500a840510078285071030303489030860f00c130b201d8080c543e05030501c001c2c003050400c02201d65000344006808030810a40d59001c3c2da10001d280203060b05480008200010722108400c8016000348a000900011165804410400d00b50b070903a14042580d0b400400d50a40d100c50a020007801c400c1e540000140030050f891460044808011803a4200b00440110001012084030100c2d030042c006032080d42c2c0070b1001160742d424090a520f08500ca242c0408031000560311a49006610940380003400300c0403850441c01200702200800c0a64201200030000880f80007101d0103441c2d001d20703000a83c202580b800400410b803641025003504500000c000100c202c138000d4004a0025800035850800300303080000010783c00b2070340185084070900920780040d500303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 965887338 1250 965886088 965886091
    0x60f0c070305060c0322030e01030506041404050609010b03030310050f010207090f1a10020a030e03030f0c0607140724060b1c0b01020a110f0301020f04140102011112040b 75
    0x44005440003580d90307460300e529080e0240c4002600810010a0000e0b9549429115100089000c2d0b4450304101c0750314013a040802624019042c0f41d11240010810381c1d0b594441d00c18246805a08840303802c00d401c020355290340c104d0725003499600c0c001d840071542c40c2c00802c0c0c0744201000c00602600a00305000d10694440c0c2d4541780741580306a440109800721280664540e05241600c0000c0d90010b0504401500f40d44441c41750007910444050200316501081501a0721341508050f11184c01440c007181c80c1d0310443c00c807410785441c04030b8a01c003500c0d004a4124000c154a941d01134402050042131540d5200d400c1004000801c5550351448150108194011020014400007080ca80d00c1780c5040700e55120b4582c000301d1442c00b924082c19191072344100f0315903003028401440304003216500d044089803036400440c816110011910444c2c0d800350101c0e500c2d120034000a035115540c564586075000b0210034180e0165080c18100049003502205644480e007801000a510381c8464a604118160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 965888588 1250 965887338 965887357
    0x7050f0f120c060c0312060a05010e09071b03180b040b1c0f0e03030a0f1109040f020f04080703031211090915040c0c1e080906031801062c06060f 64
    0xb912840324103503640c500140c5500015800036566649600c051441d1901d00101030302e01c15208080180b0643e40d201550410004040d034001c111910764410558080c0040e05040240900d080e4006003016404107401c1840f81c0c8040ea480441c0e6100c20b91915680501d0260300e120b0041030082150041c044600501c18084d0b40d0300005200280100840540d1880e5190005a0f4000014020131000c144540061034966010402c001e48041580120758400c54050342d1255031914041c41c48460954100c60320403007207120b12030f6601d6a0359100c680b01c00c042e200030b03001f20300c038000400c001403024018620005800440341e45040414410000d4241001d0075980300b03000d140015400c107449921812941c41c1c82d64581099000d810f00d0b10b81107440c1414101000035858003e410009410401515070b0600210b880310780300d555411b00301c0b042c2150406001559800c100c40015205139034085018805503592200303000030240c01082c00c10110542d0541c1d0401003c00000390510a1000a01f40040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 965889838 1250 965888588 965888593
    0xd0f090503060708090c0d02010e150d0510080601120b0103200a08071e291314010305160c0314040905100807120302120306121e07050f0f12 62
    0x544440c0420b00d0014100c42c10000b050180084c440d01990400100d14024821503d0940605032503000902185003510020301425148400020b50f24400040d50300c01c00c1801c0c01007169141c1048042c082c40507a105106450080200220f440d40005c4443c46085420800d44a096461580d92803c201d201c1000b03040c400d4141c43c0d02d01016030b9124003400040080100038106103080031081e03a0781684180c440701851103c0d01003004a0500f041d280008012000d04050500011311000e1065204030f00d0a102041d0480001046030402402d810150481c280c0e81049140d80e120031603003202e04104401408221070000d1080040d2080c3c6801e2017070303808d1100003030603d962261848141ca0040d24a0201003106d0b4138148409602000500010995200c80381c601c24031544010751134022a0302410300c071500c0080080c4207900d5007410072812200c02e02c2180c1e002c4000104500d01c0c0141e031454410140150f25001800e860659404403c000008001c402c62200c01001c00c29500e410803180640c50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 965891088 1250 965889838 965889857
    0x313150206011a09040605030f060a0b030c0a03060b0a210b010e220201140c070335070201030603020607081b01050108120d09050a0c0e0a15150207091d0c0f030d0f 72
    0xd071814422700461880303500080ca1a400c002e2200c10a4030101241c3c9402540104000c82c2c481e550107403440102d0340c00c6100092a0301a6002049058480d0317001f004400c07a82c5110304000b0007010340200348440c011a104801030340c0750849251614410b81d840c1d0294a2442c50800080c280d90f45680d4045105044c0508028149560804c4540148856105d550007002c41042884040c40b0903152103607480554407591130000d01c044404041200000d030422801090400459009510000240d80c001340f010b0740382e922034917000030103070b100c460801e101792881803144c0341501d014000c42d41a00d8045000e00a01c00b0142107180168103c0c200001c24039403a80600008903409003c166251030140c4801d5165900340140f015100a015002c400300504d024a4403c07641040190107060b1110900c1040074140c4c0003d0803803a00790181c211075826840e200b0051840b2240c0070040001c000f4a6003522003844603441088035806811901c55010780143e0007012449104030519844940d4900f40800c22 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 965892338 1250 965891088 965891099
    0x50714030702400c021e03030123210c0103110906070c0e041416060219030c05060a021309050603070e130f0f02011215050603090309030313150206011a090406 70
    0x1407070f44510850403180c1d01e941c030a0aa035414441c0800000090305410034041d90480d580303071359200c148104602e500c0310b00c41030303081c0e402d02000c41401d00d8001040480306010300d8048048201d80c00c412009148102012034801c1e501a0092400303840180548a01301000d04092003c242d00c84401103070045104000811000401c45000f4000c82c050041c02611604503599945001031001b4900c6003c0141e505c00c1010540c00035070014485281200c82d8513840c2546410307210040c007c400203025024001c01c0102400c540d60142c48115500d03054100d903540c2d206a2041101c109407149600340e040b80f62b0a0005400120402c0d030402c8803240b2003164100d65450780700300709400c0c8104071a400000c0d00c0c90419582d005660b840c000c42c8600040044a5401d15405c1c610000e030b105480c011300e0080001014000c080c400d46450750406020380ba5607030300345008114481a18040d90500310388a4684101091000448034144e07044000040e60030514041a0b1205070860700500350701649484000c1407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 965893588 1250 965892338 965892439
    0x90d1d0d0c03020a17102d0b03060c04030309090e031605100f180609030e031b0a0e010f03030e0630070201180b09010b0d03050714030702 61
    0x4124001d2185441807415071041003580621a880a129420b480500c0751103210082141c80c031340c5010310400501022030410301845600c640790016071046c0110890400c40c141c0343c01031300013100102c090740c2c040c0d90340c402408001d000e01d000150008100c142d05000300b61681c0d1041005801250441b8142441101d80d40e02d100300c0b000040702d40e600f2044c1500300c0a20b143c0655103c8915841051120302504e0b1101c1d00d10144040300940029240c031600d03001d25016022141d10110b0241c2600c2c10010048409680040722243d600c2c051030980800092041031902e403103041e140204502c041c52807568908036140107040c0081076020004010300880507405141c00d01069002d0801140f0840000800300f02000000382240c080d641004125100d0100300540c6101e00359000380c0758001d58980d00f1240380101042c2848540203407000c2c24070024107800c10003804003d44900800e80302000000700a070384a0044090094010004041c0e40c0f1388048140c54074a01403103168403403410861100071662 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 965894838 1250 965893588 965893609
    0xa110a060c1d01030903120504020d080301300209010314010e07060816080103030e010c1a0c070b07091206021b011a150301180b1c0312050609090d1d 66
    0x8504808410706a80c042000c50082d81d060900701040030365900d4078003400702c00e284d0b040008100e82c0c440016003190790320300d10010483c0d0040902500e030740e1105080c3d213080311590b000e031220a46600c0c001864080c001c1d6240081c583c003800d89402da1f440c5d680d42c1c022900300a21440015503c1c2c0c072603896850003c010b5040104150b0341d810046040c40048500000c2042c00200108210300c1e0042c030200360812104e40c0d0300c080c01c0c600161039805505002a16140605c0c040c8940b100120034031030080300010180200e540140e0000200c0d1300c41c1c603025503a038001c900c01c0301d55444480c0116000300d141940548051651184504450720213090010308554181d076140c80c1500d8102c0c1303541401e00300500004014071b5030301d00481c9554101201d10180d40c40c1050321108080e100c004c003009a484591801d103600c80e425101034075464052030050960342002ca64000c0c0c1c0c620b40000242a4039241e1241c0d40900c05001c0544180194103004480302024075941400d68540c0841507003090711401c5044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 965896088 1250 965894838 965894861
    0x1f020106030309080f061b0d0509030414030f0604110f030a0506091c05072904032106050105030415060f0b0705011103220c050901090506040b150a110a06 68
    0x5116030440c40e02814480b941c2d0004d4989a010700810074015200240864104031131b07459418020345039024100c00d1b407142da074440d41542e0500302882076000b0004003030410703141520009a103a40383c0c002803564580001040300c3c919401000410041000441008465800a00704404e03241069010034a40500070344111030702e5004004001e59800c09206c84070421108907408910440102001423240c010140040e00050340e400081500b10f04142c40e1a50100040403184e26500d02405d002c1c3c44800415030320005042c2e0075190716840c00a502c030b10000c1c0c4205031216801c6494540701c1e01c00c1350340d88040320f1b440c5035910440440c0000440307001031f0090080d00641607840c0d69034585039003500c04200d801e886410702441406001000c0c9000d28240d02c80f1071001442d031000c81e041c080d20498840d403081d6040440782001090000c03840d080188909005d580900c800b01c1d694040c40f41c01c0d601c120104000b20401c0c805c251110f841a0f100e03800802c200001c0b5900f03e1001c0c5c4644084406074a03c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 965897338 1250 965896088 965896091
    0x100c0e0612100f121103160b0c070e0127020702010c0339050c032808090d11010e030a030813061b08060a080706120507020a1205030118020304050c0f1f0201 69
    0x2070104001a045c2041482c403000d50207403403054000104240040341c0742c00342d03550b42200411043c000c603004200c248001e21b26890601380319652212000e103941d140d001424000c00511208071209469070003160949541030b074030400c4100341c80e14100d5030800c000b0407513260610511000c0701d5040410b07001d0f103040324104007010b0b0b020529103012440c00060103100c81c082e0300512030203849500e82d0580050744c86c0c0318042c040b02602e69881e00040c203100d00c00c8030303076840b902e5802030380180002040b840080b404280c1320b06924106c40401c02d541c80f140307280c0040018010100041000d506e80384640c0300c1901c180d002140e0740b80403201007c2905010300800002500e00350801c4000c0c40d10f40c21b620000c0003560080c0558509181005200a105112240045890300c000c00c07200f502c02c1125409040e00002c07503040d520409000205150700030700c5207820701012805800d11101c000d10890340140c0d0b011008101060111081c07200f00b440044c1250750250400b042c0765101c21006602e0040c1e508560700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 965898588 1250 965897338 965897369
    0x1e07050c0f030322170307021606050d0c02032811060a022d030c181f03290411041a0309060708060607030c0212030a02100c0e0612100f 60
    0x40220200e001c00300d13940d042c210003580b40c901140044181c25040c1c1d04c0f501c0850380d00d40c4c90550980c075182241c444407954019001000510950200181c20845070411050020785043c00c0f08036643d00416034841e107502101c61444030381f689038007a0450303604080d08120900062208900d1308210003250260701003500040c040c4502a078a024886100440306440100840250040d0255010003007040c540010002042c44e000c00b40c0c1c818003600e03070320010400c6050034600101001c0200480358054042400c00c0c254800102c0d66828007031842a5070403000f44403007003000801026000c900e0405d640d1010401001c0b40030507520800d104008003000c00c0d60342d01c3c00d00804180c0b030319030001c00c10010403c9100c18090aa90f4602c2182c81c0560540303402c8602c0c4080307000083c0c2608441d090341100c2d200004e2024820f40d00818001c0c0007211040b4100a0b00d940518240c0310142c007030500a0b0310035010014020720604200c02ea41d00002201110300c00103803100d035124910b101c0d41d0860011103110b2003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 965899838 1250 965898588 965898601
    0x6090501080c030f1f0902060a050d0f0c0f180b0c0f150c030423060702070305070f050a0b0d2405190e13030210050a050415051e07050c0f0303 63
    0x110710b80400c0c0640081c9103041c110b4280640b640c92242c40700301c4080304180c44016aa40c1754005c2070344560014516903681a0b00b11010781540c4c0503560144130682041070740070260038030b032088812180030b5440303984143c031468204442258025081100c81940c050340801c4101e8044040d044445141c0020a910505614054a064400728001da40102514100000f00c402001640c1d081390f8050010003842000d9000041c80201c00014101144514800c1002c0f841d400100320341200d02910980d000580c031004a0f01c0c880950b40a0550000b2800c0001c2007200c21040041c000e0b4000101c2c0000ca000740140130b210480301030b404420302c0956245043c4010301d0100d070314510412601044140182c500300e4020a040e00040100b5003001c0070000382d00c10306009100428494000c1d0000b008549002012100105000c0c2d50580f00d40982070010a8116014401d1a00440c10130040c007500ca40b81a603410f0301684000c061404002d0140480c1480c6001080885081c4070400051522464040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 965901088 1250 965899838 965899843
    0x6050919050a060e01110a0c0f0602010203130f0516030303020a1e2016030b1b07030c02040513050f15060303071707060912020106090c0c1e0309090609050108 70
    0x6000303194841500080070041582c9008944049543c0b40c2000028004a000162500c03040d2102c03a40d858007401058108110030350003444251040d10080c1084580c555404078201d000c01c455003031540143c60f041c01d012401400e00100690702c103404903402e42005241c0000c01100651046011a4001c240c60000640ac440d1801c20012112084c184018050000812940e03404c3c00c1150b1000e01c481c0c41d60040b40c0180f1414a00200c2e06006e07003c0950b5a00d00501c040b14200d0f0044200e058a641840700c02c600c0070b00300c503c043d81665506411440540070400100b00c00b5140854480f00c0001850000d43c0074030030030350400c80c1503010b00000311a00b200000c4010740103013810710a070000c01100e000145000c41c90f00300e0203071002c01242c58601524080c2c000302060b890203041212144107400c0e580b541504020140c41d4a480180140d000c0f510040c2c031141d5180c10003c0088030012007850801c00001182110a0300030314100c02199540e4080100f10349131500154a81a250313801846508003c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 965902338 1250 965901088 965901109
    0x30106260c09071b080f0f1305060403032007090e060f1821040b0708070c05060f040924080127120f030e120702090a06030c050f041401060509 63
    0x5a0300c2c0c0c1c1c00707450052030090900c1c0d4900410000d10010804840030b0242d840180c2e0000301010415694582c0418a05852034011030114940308456280208207414444259000c480c2d25403250503c04040341029407609501d0300c0c3c0030801384109600003c50f007025010700105481148080c000e11f04041118181c1141c0c0240195280d00c44280e24041ca0f8200080c0310440c4d140d011510039001c0ca9400c6403100305d208a60002000e0007000c40e1400500030b13000000d00301a44210861b04843c0c3d40e03101404100d01800c5140203018106202c00c21800c0302a40101180c040b43e144c0300c2c91320544020714038040d204260026403681c0c2d510350210341e000601c1443d9021101190744401c0034090035607160981520100860402c0101220094901c94000c1d0046240f030740e00c0310140e44070003071040c05d41211900149000c0e48a040c440e07000c66100d24035441020192600803d910703400600f04014411900d51172010190030581d00c0f0041c2d200c845500d03600740e000c0e103d02d61380d01d50ba0740e603c2000c20080760003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 965903588 1250 965902338 965902363
    0x20d02090f0420090d050706030507080f060a030f06090f120e0f030705284205090112020309060f0610092918040c052703010626 57
    0x25109500d00903c40038041250004a9804241da4550003000412000c005083c0b000b461031084040c007281c042d4040c1c1002d03103e00160f987c1d414a541d26250001c0b02c135000ae80ba00394105400f00b1050011610180510001900401c0f012420100700c0d038481e007840c03d00d40c0c8259403c00c0b80011054035154442010300001d00c0803a980c80720f0070403203000261034642c1413140c036106170250300c4010440348005c140c002c0b919991462101e10340b584c80080303120078013405803a031450700e25091151900300000ca024500800d08400c6180f00c0d0380643c03200740c1d060341c014078919041c0a42c0c4001c500002403a40015445103070b49402400503810822044c1403a00700142c100e511a100c118007035402294004420012103e0341030046212000d200e50010b48215110070220a184000924000407680d101d242c4d4400700095600b0003c1c0860490200d980b400f40101d12240f00410300309206021521306003921a90a00800004546903540303040303003001c07052118603580f400d028107501c1500c0f070080c0000c829610 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 965904838 1250 965903588 965903591
    0x120c0501020f03040e061e10021605090c0a0f02030c0a0302010f0c0c051f02090627030102040f090207050c030105130c05090402090c03090a14030d0f18020607030c0204020d02090f04 80
    0x6040c003c00340b100610040906d0302450b6101e44c0380004800e8000c2c1c0100c201c1001d4080340158145c001d0080d142e9544501060410000000008541c1400c400442c400c1030540040c82c18204411800c0320044251030712507003144002d110054404105211050b55144a40c00000348a502c075011030013036030043d0008030207204281c81c1c00f0f004a900403555901820b440c00c10b030b01448410301c01c80d071b0003400b03441c4581c0c4e0800d4010030b410804071602900343c5405408080200030142d02c81c2d041500741d208500a04c00d00200944040004000301d80260480b18811403e0b10300b140704800c0401c2c02c4450444008202c0c9508210080030f10001004030382c00340c2010342d885004e41c5800e801107034803100d000d000d01c0c01d9024000009584402c062002107041d030742c000d1030104480c103550340c0c0b80d60304d030810b0008620740c902e40154100001c0701481a17084031001340c04a4a01a0001e800704010b40d04081c0c819824080081031403030050340c840c0300401f009504003000584558200050207030008074211410b0056 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 965906088 1250 965904838 965904847
    0xe0c0702030d08090718050a0f0506010930060b150702010207061b1202060115031b0c05070306050a05071d0f06090604240e010c0b040201080a0204120c0501020f03 72
    0x1070710040303120b00d80225070b03040c5000107803034400100c1d1070410281e006068003001100c0b002c1c007a808581205010340c494a03814407150b0380070800a821101c0c2556103501041e094401005403990201c22440900c02d4140e15244111058001c013034013a08030801280d146a45080d111180d103001c01c040041c943c0e04202050030000d103980084e54500b80c9008243c00d1000c81d00e004c411308030710184940c4603940c0c08900e80d0b501d00d00c0010040d40d502ca00380a001100340c2110711001d0b007503119214950700111613900e0a10305011041c4103a070903090ba844203030b455000b502004000304010740540740c0141e90450b000202868140401050b6181c10741025858650b17440016000e580c85001c2d202c204181280c82650f20b003030440004410b03100ba82c4c000b5034844018100002c5138040e43c83da00e03600c00c0540d25001041c0c82e0040044540355902c40006003400c44105c041005544202909940014504401031516468130141103102c15100002c507034054507054140b0140d40c0c10311003078040f1a500801103080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 965907338 1250 965906088 965906093
    0x109050f04030f05030a0209030d020604030905060c07091113080a02130e2e390503010e09010f0513122109020a2c0c0702010c0308040f020303030106090e0c07 70
    0x54240f0302800c2400c020001c00070070490b9580b40c1c100c40721400018101c07203003445a504003035114081110181c0100d5800c200000303941c142802100c00170180c10300503001c2a420083c0e41402024149003500042c0c006218008414a041800c2c1014041d920010a001107044c030400c64601e05031041c040325079040c0b070420b00e0b21300c50000d000400840314900b8501c0803020700301d89520310107860319202c1e546030030000002000352005502040c2c2c1084d0b15011211130703010f00843d10010111070811000548200010440d8180242880c1d0700030200e140007040070f250004c1b0302810364034192080c4240d201100700800030088181c0d1000c0c0b480b41c080c204440b4542c0c0060200b030038212148081c2c03e00903110144a011555680000d101074000c00400c1c0800f1103d001c440c105000d0003c01d010501515413002c100401110740c2a100d059505940f011800c2890b86d6084820410145c01129a1000c036007401c80140d8041c0082d5001c1d200e00d40d94008114900f0358000c0c400703107001d00554800340c5e0030050741c1c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 965908588 1250 965907338 965907347
    0xb1003060b181303110313050a051c020915090a0e060603161701060b04120203070602120702060904021303060e0d0903080a080408040f060509091f14030f01140109050f0403 76
    0xa219201c40000200c075505804d003924180090344820300c29000c0080c801c0301c2c03e958104401d0580d0000e6401291164032401484040781981300c45a00003400c0d042e000c3d0040c039154a280d94020f441d80385103814040303518007043c2e80d144151042e040c025141c03410300104460401c00d0310f50082044000b0045003000c000c90051070601c0e4012181c0300a010b0208240303d1409401500c0241503030820980d071560f503045100b00e0340038000c2040f071180c06420000140c0c01d01c00103903c1c1000114000c0e00d85803000f941d0030072030907500006040e030b00640c090241c03001c0702604084000085004840c08107841600a0410341022444143e200c1800413101e42417011071840020340310407441900b00070440b03031a0b600740136103240590380c014101d00d20812004103090b680200688453302007a03910036101d0300c0e500d410143d00d80440f510703000041d03010b07002002400061148103210a1000d800e54551405200d00c20b03007510303503007444010b403003804e1030040100d15480e02c1560f0340a4034948240711a07081c196002403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 965909838 1250 965908588 965908591
    0x30f0a14061e130b090c030907050f0a030209040b070810180207020a080601080a260a0c062c0601080c011407020a0f03050d0801080d050405060706090b1003060b18 72
    0x10300078101000008041003040d0b180c1801d803500180340300300040c0310b0081e50010b030400300c22007405101c0c1080402c080300fa007a4256805004d2403000b40400c04e00b054140620381059405240e030182c0302c2840080583c440389032560081e402144810b510740380480c07010701310704405015040d1803004424104402c91702c00c012103210050542c40980e440d00d0500000b0014115604011010701a600001507401c0700001c00540e2a0312651100c040700592005001100d08114140400f00208001014049100c1c07015200c5552003100c0004100010030300d880a841d02c1d507160640241d910012050f0f1780241040818014031070b42006007141ea0003140001c0c5451104075084441c45004105101159211504000503120303042c403820000b40d423410300941c0c2e05a200d81d01000718076044d0003c2a00d80e8003145601d4491650f448440c1741601d040c083c0946944150f200b520295590751000001465a40d03041d4007842c58040002426402c6041c8041100c01171840b291080c800385000c039904881c50180d26 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 965911088 1250 965909838 965909851
    0x70e0a060e0607020a08060403030b0405010f0303080703060306020a030b0a090608030f160f0f02040516080105060c0c0a0807060207060e010c060b0303310e010e0f0c1905030f0a14 79
    0x19501e503100102058580c040e020009600c0b1014074004030f0300303a10018040744981e0180ea0107104c0b0706c00403400e000803140b00f8003135450740c000010414000b007406001d1250704000c051a00084640c0d036921210b0407600200c600000180c0c64455400603490201304a03c042d0a079168100409440c254580d690781c4500030b603403d40c1c0407000c600e54004680c80482012080d80088030041c005510703240000d10200c558070100e103d0f038039040c00319088045983c40c480c014201c070f8450030b00a034245810031019401000e003007940c80c4114103600c3d0b41e0f07445804030f03040180b80c400b00810049080a0000e4100300081d0410350801c03003001c0c1d00701d201e0380c0d001818190098202038001000b45841011a040d44034540c05c8040c0d43c0603e04000c0341051111a440c0c2e03a0220612190303c202d0b88410b00c0c800c1500085c0b00f40200c0003440004a071900040f6503a15400c088070b1800c2c0c2c0d2a041580c81e644035001c07020071807000400d0b008020055010b084500351544400c4419003080f6152401500c2d14046002611a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 965912338 1250 965911088 965911097
    0x5060c030a0323010b040303110606090601080c04212d0611040918020301060b1e160213051b0712080709050612011d1003061505100305090105070e0a06 67
    0x540390000600d1803260000c00043c078010845603110070078411254814401280021505038034800c00f580045120341c001c1c180104040003c1d12004011110080302038441103028108100005196900c8110710b032044840d150b29443c032285600b0400c00900b10580d2048869004059002e40c10103200c0c540b1551681c0400c0004c3c161100c40c1e81c1d281d00d0b008a4024100345890240158002c464501590307041504c210001e021039501c03007500001c03a024504da40b8190282790100107007100038200117003e0440416810380440401c03a00001c050000c40114010015034032028000c501c40da00205481050f00d490003989452a65521400c00d01e407081c03e060108a5000042940580b2070508000200b0000b821a03885210764982091300303850a00c03030f0482c020510507081180840c00111244191040745a600d441c61464844501400d0110b592a181e030482460218107a5116200641101c4440e603000845240c02c50a00e402c482c009007030107052104080c01c0d644256030b624054020744420380b80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 965913588 1250 965912338 965912351
    0xa0e040e01090614060904023105091f0c0e040218040519060801060302010509060c0f071401021506060906070c1d0103021002120318070506070515070302070521130f050a05060c030a03 81
    0x42706004001c50341010100380e081a00307000c00c0f00300014413010b040c00e01407200d110121403007850700111500f03040c42a0204017481d100800526040d03014000040300130390f180c001414890300180883c0c00885104c5240c40c20155072a040300540e100303410142a01e02c000f040018207540020300b81c2d00480e003405224540c0080c48404440041c001e92070f59044110403205c0c1030781c0b280c003410351001030304203094010701c070b44011403121050b96514540152005884e081c9400c0c005028801140d0040d03009540c004a001c800140ba1401c444c058000c5038140031303004444cd4110f05c1080941c07800c50703c04404660140c11641d10340c00e03101003100e0f003003140c2013190807602000030101d50034640b050380082da002d900420303035009220021070040300014880902e0395485e503e40340198100e004801c3c4c0070b00305034040c4c4180341e011181541c142d488030411020882c18030540c158a190140203540100c22145410242007041e81044c42e814005084100e0b030309402c0c0030f4514170030369403401014000b004040e20ac1c003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 965914838 1250 965913588 965913649
    0x130b07021c0c0515190c0212060f100504020703080a0c0216030b0901111e1c18020907050a051e040317040816030302030a0e040e0109061406090402 65
    0x3007482110702550440030080d071a06081c1210804464450319000f440f181da0b5002202c40d44608a40012805641c990840346901c0d4045501e10101c0d8412078202c03080b10442c52960f48100915440f0340385002d82000b03a0314240d94414800d400560000d40aa0b0052201c400000d0308a8446548400405000241487c0c0e0350070480c50440101500f4800d51042a03010092000059449228a8600d0000e020700d48840f10907009900c2800410000030585510b2007140f10705500042600c18110540350540c21440c6510f40704580303178050362100b14405070440000714103000c5400c5500c203030142000c0b401d01d215020081d04512540200b680030b82c1e403014110003210036240a4801950304501d401e211080c0500a032792199219000340615032040c030800001104402d800341e01900e90541c091402c1110080d03094500704080048160301c10746810040000c10002d208155000d03018020120350b0a444c40021166404003501d010b00070301d144402c00c009070b120f080d0140c0c840c94240940c204602c4010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 965916088 1250 965914838 965914849
    0x310231302130e0f0708090d2f0319020115030213020d02211003080d0b01020f0d02210c030f030c120106030e1c020d0f051204060203010f0b130b0702 66
    0x44980e003032401c020020100d044149a030000b441030392610f4021380c542d02c500605842d01e401c02c44840d400c90b0300c4184400b00c0548203590a410412243c0054100604070704042e00702c40c01140c442c0352156002040c180103503212852010f199440c640003c2081c50104c1500640c100d45034000680110742c4410014440c400310b6045510400c4030250841d2241c03009040015032505d00b1040005402c080030103e504400c40c3d0a00307a044990003c0030b42d1420116046110143c070b101901a419800b440a135000300000510002154003240c2e07010300941044104103824a00401008000c0780ea0b00b4890841a180300000b2240915114a0208c0e101e40d01c200e0026254880c05016a40d805600c800019000d90903801c0501c030180b185d400c1d2450f000e83c2d4000284c0c820b03242d03500c0600503408162103440180c002e481c0000c060f0841e1822514003116403805180c40c1d042560202c0789251b00100411000c02049494400345c400016014039005000300312034102c0d01a40107280d404200001c3c22021555030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 965917338 1250 965916088 965916097
    0x71a06041a0918070e0f18010605010f1b020a061e0306050a090203130f0809130903020601260a14010608191211010e0d030e0f071a0408060c0310231302 67
    0x16545c680d005150100c44941002d1054590040803044c070541c03a080c00070b060140c50b05590040e076480d0780d0486c141c00d0440c0c0c0c1e1501400e914580401010312000541c482410703020107001941c4030f00802c0c0d031444201d403c0c0340401641400c20107203007110602040d550005140100c0d500100d02503240c0d110740c82c000f000280c400c840288615014441c030341c2000f003018050280c01c0421104000e5000303103000c8690a89010304d400030010f810803c0140031400030001d83c2d040c410356030743c80b4480c80c854011010385060703000c04e0180c4402101d1000300700070341e400740220800380c55440060308903840c0c05c0f403076008030f80a4060300402c04c5504002c0c901300b05104060078103261001d81c000b480307403120200009445044121401c40003e05000044449010004500890f00b00c03540051850030316050b2080b5107928540c40861040c40200b00004007942d0070066103000300d8207107064503606d05200ea01003803418400d0388800a83c000307502040d0003100f000424001c0c402070584407520358044106201000348035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 965918588 1250 965917338 965917349
    0x909070e1608010b07032c060a031a0613090c030b130c14130603020714011401060806030a0305180a0509161202090a050114071a06041a091807 63
    0x1200800c8240d281107445007040daa0319481d155001d03600d5840a084902c2841005408105503d01c482050038142d0054031085d0340c401500c0d0142146000080d100303078001601d0304002074484110560040341800705024181040354283d26080d4407460550410003180700326503a055a526000076014004c2d0000043e004008040d0089908142c0c0c0d020001c02451407203c0c00a10800035804040c0f50349411141c01d10240d12000c0c0450707140c028100c01035484071070203d901c07100a08031180d00c20401d00030342c20642c0c00788400c05100d6040000040500500a0a0b20311170740c050f00c1950f02003a0403508440d0721401c02041e1030001203649010400c410b0b03540d4400b50300903244504015500441401e03161138190340703540f40c211002001d840c48059024007c941e40e88080380050800c071030740c050003030a007214805030f05007410314072036441d0b55131120444500320340b000c1d080ea07003084039501d824800c8802803240394550744400d407000303400304103074000042490156001c0441071084800701048078000070f20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 965919838 1250 965918588 965918609
    0x50406080d1b051c0c140706051e12090105010512030a050901110309030d031b0201140619030f050d030b0303030f011e0e0a02070501112104020406080a050c0907031406090907 77
    0x1013035100002c1c10105003c030b003540d509070a0790503801c0d800f03401b1070000110b519580d076050170b003882e03c00c1907040d122000030340f401078000030000004510301d0004158408d55805000060343d6150a00b0b100c2402541c040c402c1203900104001c26031180c200041e9a9540c00a00c2c00740c442410402d00a0b1851241a8445515200750728000f10802c0d40f58010403001d0680400d2601c0c8142005403da081c3c0e284046c0c1c1c042d1203407010380061381a0514090501c10180b1000c01062580d90726114903a0016405900751550741020184002e40c0d50580503500e030070b1009500a51552030840f505954904060048107e03a400340c1b0050320030080d100002c0d0b405801d4440641c4910f0600380c90b030304029440000c0460741e6500746901c02082505040030340c1d01400c141610130240b403150f40200e04800800130801c99006503942004111345104012907090355116400800c0d034540507200300b05030383d80021310070410981048411914001c214004541020055a511245d0f40300c83d001039003440d107980c11114800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 965921088 1250 965919838 965919883
    0x10b0d380a0903030b1c0602090301110f2502030c01030506040f1d061305060a050405191a1501050906032205031309140408091513050406080d1b05 65
    0x4501c0d82d02450b4114400d8034200014051030042c01000300140400c41e090302d41044070756003c01ca40d50020700085000400020f103071b03800e96036820004e810410030640100e0000c01d42000f81181185a03850202d030b9418445214100d0b50f000035a283c030002020380c1010744036004940c40344c50b1a00210500c21080c1014018120b0703c500ca0150201e80c071400c0d9940703200d0b09022905003114581400300054002e0b01420312552008110750107050060030803507030f40c0700d0b83e450443c298101d5000c40416600c50289441030204c0205c01140c50800035011100e134030301000c0c02e040580e82010854030134000c2500c4041d00c075540e1900750003065040b03003000700000c2e054042e50800c0050100040c20b01502d0100010122512841400219241c18241c0c003120408500402c001c00c0c841d030050044104000c004a400360f282d030f52501819040200511040e0841c50000d004c1d502e80741c00780c0c10180c031703a22000b09981d240c0380200919011411a4940f00b201160205000380301003405030484911100005030003e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 965922338 1250 965921088 965921101
    0x5120421170417060f0403021c020a0515010503010c09180b0f0a060203040501080f07020a03111609020a0207051503070c02120f0607080708040507170309120102040503010b0d38 78
    0x40000d000355851103802a8400110f441c5c554071203150090360154001c0994402e1500c1b01c0301411b1050341c942c4198442c14680c0e1000483c2009126205c1e20f800d02c2c020f2a035450081494255180035540000b888601071050225000e50701c81034542d080074400109103150300320082800d80000c50000c98000000a0700030400e01d40000042080318000e07030f50000c01e507545085404001004bc2e4400005801101c81440030078422481c01c074030151040148c0d0001481000c1070281c1d40b0319a07120740280354000c1059141c598062101c00000c10080d10700c1540582d041e6414110b602c0024940c400707200f02079a01c0b60541d1544100707480a83c0c2c602e411a0340c0c1c3c0080d8408990383e040100c910100141c000e90000d1051446940542d0060b540280203003045818046808132a8003120b90600942c4000e20200c00d035542e5200680d80030101c9900010303a518207040174142036503400c1c1e0a6a001c0e101e2502001c001841000c01403403401d880800308098041d000600020b1144154103001d425103021050159 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 965923588 1250 965922338 965922359
    0xc020409140c090c0a1d190e060103090302060c0304060b1320040b09010f0302130e040501060e010b03130218070824060a0c02041b0c051204211704 65
    0x80c1050340000c0b00c0511100308100490054210b03102c60390640d080c0400c5001d9801081c03c01c450090064000c2418012940031540e9030406991280d520130045004200e00003c03032030402e82100c1c080c40d05010180068601a5542c1c00c054092203204000000182c113010f0254800c028030700000b4900300900440d5403006000e001040c51554001d49052030a20a00141c2402c41c0e0131265809907507802c0c03400040054a400f0304000640c414943c00304a81e8016485e0440f014000e0040c1d0f420001803402c0a040240c00c54500350414010310750000010f01021410b030701900c0d806031101100710031100480c0702040d0881503030401103200c000d2405c10710900c2601f103010303144548060b06141c81903410b1104e00108015003d42c0c02500000100200403d9038865810719112034000b500200b4040d201400019283c0350340e0840c840007601a000700303400c11100780100c241031844807000e542401e0910141501280d130b01000801010200040d03581040607180c00003411690000c0200e444a41e55a850305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 965924838 1250 965923588 965923613
    0x6011d063a060606030e01050a060e040b090f030d0624050d02070602070209010305031213020307090c2123252102090909030705120a0c020409 63
    0x119010a06000800c1410050a1407401d006048001c0000d8004101025410141070503111140301c090015480841c1160141c68020086503a002a021444030200f03402c459020742036080e507508240741001100101d2500700e4200e03401200782e45080d1100060b4525103640044041d040f4040450805c0d01c581c480e52020f030454006482c0c3d0600380c4070140e88500c5122008000d078000c90018401d48480c0b2000b580540b94280c0f01c2c40700189401c65980008d0300d5000240e01c00c450a920020f0b484d80800e00300e26120360030100702c48036000341c409283d000039143d001758003400d0b0b140c0350780783e513a003840350700c035529000e9180d1620303802e5078603100d981d07031110058250b1266100901000802c07001101091080c42885400700307034078501000c558080391030300718a6102e0364001000111009200c2050060741d8150203950040001640c50031000f0501098500040c4250a80d810030300c980c0c408600301080c1c1e039596180b05070443d40c1e1840c50080c1560740c0c1440315000394101c3c1c82d166152042082541e81d11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 965926088 1250 965924838 965924879
    0x40b091f150b1c05090a0503190e09040309050402090f0414060301050903090607060207080f130317071101110f030409050906100303140c0a0f0b0708090313050906120601 75
    0x110003240c2c980c10450744512885010310015a04111030b0304002c002ca50202e03400100500503102c406095455052454004400407001101c902454256040e0007615920707101070103984202c4285451344000d0012006841a14001c81e000a40e4104940c7c407940700a94011000f001004403118076641c8048204088039598065131a14011941d02d80d0008141c41e6401001041186440b41980d034400282d004440300301d523000d509121000303401c4203c1001d40941205c86e5010380203e1b1450514111301c5000d0007200000311420050080412030542246801e8102030a01003402c071154260325180060410710660f071400042404200c00d5244c4d04501d000e41e03074000c00c03241251200401c025481d9041d1000401052081c40c0c807035201452000a4400300c01007801751480704e1202e4540d0403440322102c0c0125808030000d000c010419810501b0282c00c80c200c90b0007142040d684900180c000002d0740101c510a15032107001801c02c1e0740707094900e0004484401680c469580d01c00050041030104980c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 965927338 1250 965926088 965926121
    0x130e070e0a0308210915070e1c140d1e05030708180f030307020a1a36121c050f010b30090d0c0503040e0727061202040e040b091f 57
    0x8600980e10519040010500049c29942100300c440d00486c001e05122104a0b05990069280306c3c0d40c24090016807070b05510b54440400406010b80b8120a000f00074203071005101c2c090050005490307000c04115401000825400d061209644540d0720b04000c45140b8200d503c00041004021035003c030300b41c5450341c80341c28420031030010b0b150020180f0780f00701ca4000e805000700d0324144c0100c41c003150181c444007a2420111054488107403440c01c0c81c46c59805055000b20000e000003403407403424100c01ea07485c4035003030401040c10040320180030110184110081560049404041d40c400008c080c95001c01c506004041e5480c0c020b4003c00c4200111001303500c600a03c815044546d0140c00789642182e4460051441e00342421000f448040000c1c0400e01000a040d010f441912606005031950004940020000f645013000042c817543c28404100b1a503401400b0805c00110701121058000c9c2e4000a5a091541d40d60301d800c1c6425240307540103081d43c004c044451004686a1301a1200d40040c220 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 965928588 1250 965927338 965927341
    0x5120a030e07180506180f01030b070302120604110f1605011104080604021003061502010905060a0c051c20070605130f0b04110303130e070e0a0308210915 68
    0x192614058460200762412807510f81c1c80b9400c40c1c4c0d00065100d10018200401c0b170b001d0404c8268a41d4044a8907403c00f000301c40140b040c03140344070801d0703800800c3d89001e625205841c084034038000d00113000c1c1400303552526440d82d40203000d44140d48200c9040a00b054442007000b040e00550490080c05440d00e510309982070000050950440b030658144000400880c0c071103a0038450141c282e1a00e602c100b659605020642c0c03075009035040781922031075001041e459141e003801424108040c00020020b4a04405612642c7c2c0140c15200c0410548002401c1413030080c207808085c1c851146104400601e0140d5800c03540010b0024181c01c85c00340d5010000e640d01d1141410340ca82e00d10f44003401c80700344000d0500000d251030016640c000d1050304c01d1180d0840906c00301c4c0c99900442e081c995007070140c15041c0f03c400701c09c1c415180d0101c1c80389002003103d4480c10210b4552000303404050401e0000240e140d8a074002e8501c40001150b035000030b52014540081e00e40c0e03c504004042e042510070000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 965929838 1250 965928588 965928611
    0x1020d0b0a080106050a061101180311011a010f05030a0b0603040f0302010608010c0503160903020411040608060a05101128030e0a031203020703140316140a0509120a05120a03 77
    0x801c100982d50041c0071b1011103403d081094035000f4410f840086559240c400005142c0080d804404603a482912040362503446070304010b081d200c200c035401d50b42e014420000e40f5281c0e440304c500d2511459034100a59030b6254610801e0142940c112003607004140042440100001010704504160080c0e0080086513107440c0c10382d0a1303620903c8480300090050010441c961642d807099102d0000340c0c14544c200d240e8a50100d001d44203804446800d00e40041400c00c50140c0200380960f0115003141c1c85651a4188000100144100249041004040000b0080c050400c0110107110600d511800501074148003520f0300a01340c02c030f001c0300050001d000703000345800c04038522020303039901044400e10701d40d8444085000350040d5405600b0051200c81c20100e00b011180198050300c031110204444040080c000740c40c0003c0c4103040841c0100c10003003885490340c02800d6415400c0c00700c8110320000300c2c041c1820701d00601004050003901502402c1c10f40c59049000800480c0c4407510203100080400303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 965931088 1250 965929838 965929841
    0x6080d0f0203090d0312090506010e271b12060907150e01090e0a021318110c1510240f0504061209080705030f071506150c020a0801020d0b0a0801 64
    0x1081c884c0c214940c02c400400290048100d805454002040050781c0724881e190145851001e030b0014120303410200610440010b00d05c104e20603044032150018080c2c01044110b9641c0321a18100380d01d5408041040b511590780e01e0300d20070f50025900440b10036050042c00e191720b0300c8152184030b0001c0304c2403140c0002c071406010b007445a502d0586440d00c4007480c11701c481405040080c507913090a6030070402a95101c0100100001a10400340307407143c410b20400498044410311000b02010a00a1014280c50750300042c4528000741500110741080c2c4454441c0009242580c20050a02c4841100f64885054044850302010300e02e41e64490402194001a00d01c0d1169016500004240c0c0824442400c6160055071225102e003101c44d1803d07405894a50079600200010346540400041580920840c0c0c40018440700c503030401040103e10f09031000e1212901c903000d80e030a00613007250050655841210030001022071600955542c40a4540c05000b0140c00c40312170300c81c1070302d9040441d101070705 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 965932338 1250 965931088 965931097
    0x6022706030402010305100f0603020409060602030f16150f0516091802180604030f050d05040e070e12060a0b090a0c02121e0706061404050603030418060906080d0f0203 74
    0x580101e25544a5400440160000910380108880903070000950107034041c08420041205035001612503041041140a5400a50003070046507c14460803408541401c211100041c81c903002d80f62500c0c0340d1030a106c2029500588030301a0707160510740300308091160000c600c45e000e200310a8980c0740009909903150045805540300302102d100d040390602d0000da0050644812240d00c0000483c60b400000b2480d03842500119090343c0390801c040300b040810418400d001c0c5003810700c5810141450b400000b200002000881003103103500007807125848254960022062081c2685da107440c00711944800f500b582a18640038240e0740c4009041000c0f1403041c01e58256455000e00901100c01c4603011080d04161240180e800079918074a4140b2600c1c401030015611a041c0401c3e114500340b0650440c000940c0f021740124102401c1003029034012040310305442c01e0903c03030610740e803040c0e800f0402812030707402c125030644c5407120100e090f0030001880341102e003043d0785202c40311249110490303c9004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 965933588 1250 965932338 965932417
    0x1b0f090513080a120b0303070303060303020709051e0606070b0916061106070e12100b09070c0309031e1a062803030c0204020f0d091e030c021302090a030602 69
    0x41840081e65040c400c4441d500c0b103204907500440c281c5c2100d40042e0031070340054012000300341e031400308104040c0c06114501c0100f010030b4003082180380841e8080038180381007041c030003400e5603080068599615402622031a03a0406c40d000d050f0700c0d10003601aa95010318000326046021400700081480c850043c10b854400380720b000c3c4c0302c19180d84405a524005d01c03004a0b500c820a841e0300e46845e1010002c410f015030140c40003141ba40f000780140120fa0101401c48010400ca10500300003003900700c0040c0003200d51050042010078155211400d500005010061500f002000d002c0001107000c414940601d1040f40d00e5804000d10030724021745c8180c4084e9407480b90001100c00c001103402401c00910f80da001030409450540117281c0b01c51187e0020385049101a95064030340c3c1841b40b2000c103403164080700f00204020001075100a441100100300003446250816141501000c20b81c068504d40d000141c500e5100135100e00d4050044c1d04400c0880c0c0524640d004010b84181040045001081 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 965934838 1250 965933588 965933603
    0x405030702060f25210c02210a03031b0c02091821130f030506010e25031b0f093317060405040210050912190c141005071b0f090513 58
    0x8846d9402e20803250302c091212120030081e2280642c25603000c1c060405594032076640015440c1b0200c05040314a00e030302000ca820416075101010041c0c8035580c0303907504900c00300c0c0580d540d0007480403454903102d003103503442901440e44070740030440d40c0d1070f071025203004c5d00712400710200340d130300c460080d804e0341018880948207600680041002c403600203402a008030903003115003580c0401520f8201e480d9903540003600007903600c0d03465007400386400101c00d4042000d0b241c03070b00409021082c0184200040c0c05881c440031407824a1002801d40700101c502e400ca40384002c20320042221102a00555188144c04240014080000c50f507241900c174151203a640180708030b0f00340004820480c1c3d941c0100380b03483d810200381c502d840e01203801000140e80207842490103240d681c00a01c0e0500485200f58406040020803c1c804211945c414206030101140c51519981705d000d1406e1440b01503540c2c1c0f000d03014640101602080b030071007000004040d50120041842107854650036400c6411481d1406400078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 965936088 1250 965934838 965934857
    0x2406060e090423100203010b030f0a0c0f030c02031b3412030e120f1216110d0b07030c0e010215010614040308030c030f0105090405030702060f2521 65
    0x480f540408800e02c84030000403036032441032600a00c412a4000e0300000d5081801004200b0101400400250f001424810920050205100c0540140f2251410009060312081c8501841e03100704152085500d518040d5503000b04801046612012600307604681a02440c07c46042c410300f21110710700e901c03e011241d0175440e18241c17030014940000e039000ca04002640d403100e400d03a500c074a03800081103c1d610103050340261008a01e840d02c8528500720a45a8090104d6852072412043c0d0582c40e94020794105035074210700e00060403d40c0d0071180140408120001c0c41182a41035000301c0c04070440703460760b00450614400590351640740e00500b5500001c0c4400501400d403045411f042c2a02810404504082c3c40340c0c0d4214954000304c03403200d401d07040030007044480803042d008240140400c0e0741c1d110700c500342500e541c0d84074030980b0390282c000e41000031820b103004081000c40e00e0300414209040c00d0001540003422032120300090550342030340e604040311440020480c0c01450704102e5114820f84 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 965937338 1250 965936088 965936123
    0x3010303030f0e0f0706020c0d02060909090a0b0411090c0315040b0102030c010227040506010f08130c03030e0109060315030f0212010501030c09050a1b05072406060e0904 75
    0x2030032441c160b10a20545601c405010910100120b102c01e01c4254090400d032814080c00074900001c1140c081c2c8261160510704d40036031a0403049031202c00341958481c0c0c551341d031115002c1c0303403035242e14000303008030344803405c0005011001070044450305017100c0511882e12070842000040c08262185184480382603000007481c0703081d070310074903550300d040c0141d034103211602105500f20b0304034090108280742000c1d140001b8020b20080d81070828411101000f03d42401000201450b074039501c01028026130b000413445140b00810005c80ca5a4031511440c0c0d81601c07407400a00a030f10250840d40403d1000d480030a409000e40074504145812003000240a403458031030b02c1c5010540780082c0d030043c00d104e8001c16046001e0044601842c003480406e105c8524202c179903c00ca07000200440c0709685400e80c1154503880c200300c0090103c6044c030b000b035221900d83c10250591141d0300c24664040c001d034556010200030680000c011a003640c2c13561085030500d0740601800c51001c0760700401285002030852031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 965938588 1250 965937338 965937341
    0x6010e04120809161d100e0408070809030d0905031c0806100c060c0c030908030702011403060f031c1101150b0c1203040f0b0604140c091c060f060e0106050301030303 73
    0x52009070743c401c486580300c01c14180948091560020300e544900d03a006004064040000150000908000003024600d8543e10a800100140005094001c0002d040d410b108020081d0765003540d00500380d90500c1c00340000586255094400d40f8028041c0070007040c1040601340b02d6800e480c0590321202e2442c1d86032000c1011148058070601d040c40a201500e4000c500588620407071244561914803524800d410302411051541d403201e10799034410001b0000503644180e9182c04011900007841c0c03030342c446138002480c0d00e1610185540521500c682d00140c031031403110449004181e9210100d03103014618455081c0d4101c5030001c41c052100400400984600300700800c0700d02e0348041501c1e60046940210004d82d03200303a030241d0700c003446020704005205441c10180e402203400c490400c0400e400503455501400014039882e28401c000c81c1103ca1521401c1114100039840e54035040c2c410041c0ca0a140180500442000c1c0b05161240c01701b02013220298650690701142c80321420b40e8a50351b411030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 965939838 1250 965938588 965938591
    0xa0501030b101116030f0c08060403230f0d0504020a0f060e0f03010219080402131806110904090309030b06090417070204060b0f03090c06040f05190b0c06070206010e041208 76
    0x110544104030b00b010441081d5201340c40a1031040014080078105030038030308042c00c2030b90481e00c85504030809010000341c00000881b000d28200c10380c00224138085080a45030f01400c060b0f111466400205e2010407101c036400a88640d02c05c0720790f60040c2d51900303041007401c0d20901a040201c0e07012007950b08540340207402c404500d4401800985800f590703500c102c0c1c006800340100e41c041181282400b04626040d42c0204011000900422094660000d0000d03045a03420018120565881800d11000c0304501160b0311840094814020004940383c0240059480e00c0152400380900c00441c019161400c409402180c0000c48900c281d800c2100f41c0c442036004100480c0e10999904000a01c142c113080a8105081a081c00e60344a1800d404050308288444000c5807040300e04010a06c01e2103407500a460584130203560b84041c802c40b40054851032032407078000f026080404541e00030000740004041e88520350300d500f91900381e681e41105061803074003540c6c002e00c0f21204904d03441c8103e12859946 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 965941088 1250 965939838 965939867
    0xc0901050f071b0305060f091603110301060f080321070c1e0501092003070b030a110f0c1e010b090a020a030221061507080d0b01020f010213050a0501030b10 69
    0x140040d0740500c07041003e000e10340e8800c8541d80c20585c01c0099018210000307542c02052007000d880c0083e440e8258902d92490741c04028030790701c0700da58240003a40f8250b00c14805090000b03400310343c0588440c1156580c1c0c00c01021015484000c20f40c00c00c2c1201c150b03506034003500240e00c8184100340c80e50703200411844480b00d010000d410850341d280104100f4003071521a07034001c0e08103113400c1000090300004d1045412145000781d0001108028100081c1c1c212544011201000580110214807868062154409a1b218181c000c03912560901c1c000c21244401d80b4a130308800c0101c51468061401c0c0c403100b10000da8001ca06100048007450300c0c2d001031108040034a401450719003601c409140c5050342c800000c3c1c000c034003641040902c1c14258604084a49041007a5051515a82e50108940310b07441c00c44030003684500c1c2202e100c3c2d008004200740c0210600c000d5488101c10241315004d2038240c400d1520800b15460001801c0d40a4461440c00312006030200011800d4844141c1c1d0940400346113 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 965942338 1250 965941088 965941103
    0x1d10150e1902070b010608150109090e010f06030819080c0d0209011b0303060807080a08180f1002060a0c0f050933130602030f04171204080f060c0901050f07 69
    0x3001c4007280701e20090200e9031240550300030b1941031181c010305560008280c600141d4904a070315131207030703000655481100c2d2181404101400325440c6c0502400240c010140e0040c14200b020040100980143c5180c41c40c103004240540040442242c0500080d1f409980c00c2504020074412a0030380d030024008140103041420a000710550912030f4018030079010380019076506024051030360140030000041c0b4001000b401280d02c5525000c00c20f1245c1004820388035008440a0042d44581017040c0e030350070700140f141240c0c02040b40007944409044400208040c40c04641414840c050035000300c0841c01c2c0c0e07640b10b003810351403010b2041c8042040800001d0514128aa2014612028415a05c00c1c1040a1981c80b28907506a207203440d800c2d9045201950000e100e2912074802090940d403c582da04c4604034610880404203a00305a204186120312000c002404034003010001070030000c04503600119440c503603840c2c280c6102030083d0104140041c40801007103941d4003a28002d08085802290b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 965943588 1250 965942338 965942371
    0x60e030a170304050106050907120b3c010207030c0e04140102030a0f14010608160918020307021e1c210606140c061b0d1d10150e 57
    0x220305030101c0c82a11854034041c8004100000c0000a00030f040052a082d5890f41d014108108003414118498580c1c03000035503101011003503a07a070660603140040d1070a440620781c120140b070740403280c000d0580d00c0f2048c9210b40c6030200c0c1c40d440055103004a80e0000342031407400b800e0000940300c10728003400c1a583c0c64006149003e8001007840110b008200c008000078160002102400680301c099070b0748429020408010451550007050301e82e40900324028542c50081c0f019015980c00f40d568000c3c40448440596405203844140c1c005c50240c44690201c0301a0710210b11203040100390340e14210016004810341200940d04800c19581e03001180c1090510307808110044210381030074520107500c035501c07108100b1515400070408018a1105a043c43c80c041c2c07811401740d83c030680541010a0003240f14248010005100d0070358800d1140600300380541c1c2e0b110000b139000d000f0540801d0b00c0030702400c00046009100c0d803246414400d4111440b6540ca0b01d0007404110201c0d0061041e6010015443c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 965944838 1250 965943588 965943593
    0x30203040f0b090303091b0306041106040f23120c011d06121506071a0406180b01140105091c020a0b04090c081b030a09061811100c0c060e030a 63
    0x11220b61003a02c0500003103445e440c12182462800c40700c01016075140d4a0f868000e076640c0c03004a820380c1e0150300f1203508040043d084000c2645072003141c3c0700c1248008104008074403070042e150714020401c04007070081a0035400e01c003002103e011556002e5444e40c8240100002035004590349914070160201c000c50a8078400003058140e07100b41c0c0030720041c841c503000704004c9102c01c004641941c3c400b0fa60642c14442666280340050701031800aa905001400010b41000025003040d644103489185000e8004402c0c40c00a14a840038059102c2c1d80f0009503114040f54414001d5465142001700080540b070b50760940d43d0503035030030100f09a0700400030100201c0c00e414850010300040001c840000307400060000b0050003800050b1001e0080b141c07043c0b084080800007400e807504403408040c00a8080079515141e40100351703003004465801c1c006080311091001450b50304828000540d225001280d080030100c1c1d514218a00040c6140800141485036510986070540c1c0544080c0c00c4409481c4681c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 965946088 1250 965944838 965944853
    0xc23160305090a090902060f0f190c03110c0a03150f0c02100c0c0317190c050903100203061f030f0504110f102a02090f1b040b03010501030203040f 65
    0x20881680451000500700440d401c001440c0e00c020040c2000030004020300d5400912144680c1d043c0c415594400f1071029003d224900440340c0c60070a91903840c4441c4246440900b01c052440819804503100c50b10404620303801003984c2090040041400b4102820b5565822541c44c0c200c0f00103082664030b01f04001c011040d4450314095098a40040a8032840c0326504400c0e202140020310401090300108000a50012040381079602c0b0a40001013941e10004200302080c090f00003000c4490505111202807a0814020112090f0980648a0150030f2110036020fa1100b900c000350483d410745066903101d00d080520041103d458600400d10b43c1500b10000165801980c0955008044076402ea026140001c2e4001280400741c444001b001c200642c06400c0d15034010104000001c03c10810703141c0345410405102d41640106003494505002080c02040d05c01100c0d83c10000450900b42009c600000d005c2e2802c4505c0c0d1070b50075195a00346001100030303400c0034000711540718030701f8500300000303508 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 965947338 1250 965946088 965946127
    0x20303070c1a0a050901030f0e100f0b190627030819110a06181a150d0b0105212e0e15042a180c23 44
    0x21501240c0160401600c9101c001c1c0503030022000310010040c1c0c1c4825500302e0181c5815004c07d080001d00c0c01c4c00c1c40401000341c161512924841d018010450400302c685920010280d40d12400800000070003805200707441400408240412005103010401e10f441901b0500142900410000e00882d0710310160b00c021000d40c104840102d408510b400310314032041080c640b156410b1410180d541020f0016a8907882c1844021f4091134813104900c050800c038480c44650b03e1391005410301d0010590f02080d0100d141034030340b402c1c20040d20066801b02d14040102c0b10010f0381160040146034680303810000a804581c04003204180200c4121450200500071250820303103009213521200704480201c0c041031058a00c0085045c541f07050119614000203010094544107204034449480c1c50a22048450031915100c101c400b1103030705210a07202105d00c074001c40e01012a41c0c01241c0c0c0111191054610350304003280007070901107200d41d800c040e2a000c00c9001c1c204101c240e24012184101d450200310 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 965948588 1250 965947338 965947343
    0x31e130801090210091d2203050d0b0d080f0d3207092105011d1606090e06040b0406180c0801090e0d0809070509010314010e0606060409020a05040302030307 69
    0x65404281080d8104002001d031620501c3c03070408002402c0010001c0140b800346c030883c0c0340c040d6590000d6070502d041c0030300c1d40141e909100d840520f10340d145001003896002d698201d01c42800c1c04d4200405013041d0090030951603004149a00b4904242c424542c80d40102400c225900e4440c00b4070801080c201c12024003c00000038406101e000000008180440182814040040d056020800b641081d010714004810468659189850908240c0d000d84000515072200c21080010381c1c2a408000030402c2d400e20f0030781c4400301002d1f83d40784180d0b07400e00c0354840d81040b952102c0000d1018901640024035000340144006019521102c50070381001d500321b840013109541d1f1b039504a10b1a0050765131401083c40350020b120159240d01610f0311b4038505080c50040c81044008565200800d0003550003802e000380085800f2342e903905042c5444880c901085001c2c0d403800d04041c3e90707100c0c0400e100c2d00c01c00d40607106034038003490545c080d4000e51280c040f4408112041c800840180c0d41400101403050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 965949838 1250 965948588 965948591
    0x60602031b21070b1b040b130f08010912050f030601260a0b12190308060607140a1104022701090905093a0507140f0114090a0302031e130801 62
    0x201c0c103140c0300c00400400782000c2e01e0700020600071400341010748106d0b401c2d00c3c0000b124a45850601501041c6241d20780c0001d1842ea107201404200b1490540c064465035006415003003000c542c084094486214240f440151500c017000040c070f9550090300302030703e80501012034410031801c031f4014160f8008151699a00961104040d031150b180040a074040746610201400e0040c0218020b12040b668002c0e0003400d100d280c4000a10a40c0d8600035a00001d400110107000c00e82500c0109442c1d8941c40001c0742c8003040c403032420903507007002e02c01d50f8000442c00c1003071440d55909915000349904058103603810010806404192000140140e078003405888004044440c2d02c0c05078a080c0b100700c08904079a03030403000700a0003c14251608014849070505040d943d4500c503050210341e13414252000340503481020284841c01105500900e01b58021820b05845500d402c08100d44030120402d000d00180d20603c0180780784049000c80300e050b070765504021403401408081800b00300c0e146602c01c01207039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 965951088 1250 965949838 965949847
    0x2301140d060e07091a220213030f05100e03120a0e0a0c0e010e041505060315070521070c02040506030c03071509151b03020708010f0b1201060602031b21 67
    0x30340a80070b18422a83d5240300103d20020200101d0a6001c105084040c44080302205004e81072151741260300f54a00c82300c841802c80d8a0342403507648922000011103161045006058421140e84554484011450040d6240c060b604501640162014001c080c00640c4c03844c0051015901b04140ca01c0203214a182c0c149492401050380040d46059000c1500001c002c0208000139410400501e03200b00000c5002641e529110040303898810251400340040c440001440310090300304028081603801c0441c005455070611131600d4a203441601d291020030240043c10307006141c10f030440b80d400000a42184c41c81600040082d250000aa10003000f00750f40940d10f1038602d0344074800f9000b5248074010b0075031150200b00b000b403184506445900c1c01071842c3c0950800c051080c80900001c207000c0c0001d00c4a11050316a00b002090780e101014807480d14503051550504042c0620400c490306034016505020b006400100380e201c40000144290040f4022119102c000d2644503070002021015241c40f03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 965952338 1250 965951088 965951099
    0x170c0a12020135070c0c0306050117011104060f030902180711010b0306040803040f0b0c04290307050715020c1c03090c03061505060c010f2301140d060e07 68
    0x2d54603005031281c941c5440f00c1c0c0b030614201c034071004008454100800e0955035443c001100e83c60103c41d8000e000501c41034000040c8009074115a042c1c403030f2036a2520942402044031800c0f01d1070001041c1000105100c00c010040c0117100c0459042583d06010603140c10300e41c0003e025003c1c41101c05003207403851050103417250340b115100003c8002d0800070842121382800095440e07000174401000d10b800000098101700c0e6003410762a441c1e900c000e103029542085107003040e50380c01c18005c02040f05280441c000b96860701c03205400c110350001000314595101c94130212180c0d48102c006482d64007440d2805044031103a8402000b807010300f440076014403000b4180c040c45101c0e9500f030860401d410300342e0242c04100740c01d84180071203600200020741c0c1906c9a41144002c00a58003455010f034000c59a40c60100d03041d004941401c083d07a0040055410050090891610310200c030002120b0480061103940d01e040b5070051003405c020f010003640b8001d9582c000540d0304201440040d5040403400308078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 965953588 1250 965952338 965952347
    0x6070b07030c0c0807060216050a030201060305060c04030c0e04022706040515010807080709091d0f0d0c110105130b090a060809031c09140304080708010204050604170c0a120201 78
    0x24441c886142c55146180f03242c0303d00391a402000d4016144980c00601c2d0140d004101d04a207802c290300006543c0700c60080d0a020340240301c1c600c002d96150040c01c0004101c1d0382c0d080125404da9502510070b0300024105120030004410080040b41c002c01a21012a103412580201200a020010802006141c08030520040d201d01500114002d004040710742210381e04201e4540d40445145088a020b64407000200e8581000758001c1511038682050036a040002100c2c440c5004410b00803120b911105000c860780c1c490f286209a000141044a88800100b580780305a0640700149000ca0610a001c0c00c0d00c0d0f25003015038881f144507540044ca010a034200846200020102401d09400618103039083ca903c07442101d4011150b04000d684023004452568803408085802201074183d4020b407600c4036560740d10030701904c0c8051007804000584100140225410764501a0800c2d0034140350039a07120740701200b00d1328614a80203200710040e40b41c0b14042d203040208119801586d1a81080c0000361 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 965954838 1250 965953588 965953601
    0x61d01052517040809040603140109051b0a030f1a13030215040b15301501050f010f1e0504050a0e01120b0403050708070c23150a0201060506070b0703 66
    0x40034420301450a0480c0e51400e0b02e402d9015400031042c43c2d40b00900c00c0002c00810310760f0070040c401e58150030720b00d40400c5d056018101c010300c50710458400a06072154051540c001a9046600c120001c0080c400100e41d440400705491145000d441031804001702c0340301c0070300111a440ca40035110583e48090583c1007045990380c80d07602e40100010b0825844201c4001d10041202045201c00d003903005090301c2e0100d5880314024001210f5581200081c1c41d00509038880c2e81d911218440d462401c40e0085a260229040742c0e4014105c01400c44c1403001500e0011420a0f288140031088071020710616420602001014980d615180d9490800d42000b0003002503812001c44441c110380107209000c0c503da211440580c1103400b207220b13903032285421920341c810400007d041d40c03c04582c100400002500f0482502c10301e4018607480701c011018031300ca40c01e450a03d140d10506244206506100140003001c05420520003c0f035070f59200d40218170f05c0e40c840d00301142e42000390030401107001e83c14070554 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 965956088 1250 965954838 965954911
    0x140a0804140a0e1501050913050c03060414010e04021509041a1009060206220507030804050a0b09030a0320070f1806060207180f0f0903020c01081003061d0105 70
    0x41e0301810301e003441c84c241080c03d40100e8144038001425503595590203a90303001030800e2a0f0141b2151620480501841d0005d40d8194011402d101e03454009881001c00c26050314400080c60b4030740d80d6140c00704600014404071604011000700640109a140c40c094814449400541e6401c0c0004a0b0281700c04030040d0120f0100300150414280403030b42e03010821a4205081c002400d10349540c015102084001107180144240314583c800000c1061440180048030700856050180307903074800500c590b1b445180c00c0700e81d03d6040000a0000a40101003080c40300c50b11022915113100d902e00030320b1500415400a0b05260144001040891043c00d00c0852213072902c4001d020051401c034002c1d5656005014003841a94842d00426082d81e140d8000d010320003e00c3c80600c200450441d108000f040c070444103800502400c400c4135441c1d400340c0e911a000da00d88006410100e40340da00ca6078001c108116421002812482c16803406c0d400c01d008840c000d40811000e01e106014158880d60301007d034500c4c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 965957338 1250 965956088 965956109
    0x40b090309010912080d0219020c04060b0d020732160312080c1314011e12151503020c06180d110f010608032104020d140a0804140a 58
    0x3288580c1e60700c01000310807950364042013000a140c600d04215180a441c2181c002e8901c080f44107001884c640d40e00080401058081e600484e58201c2448156080c0b0701030b0342d00080c0100320703402170b2a5141c1e0041c1046401000c2d03001d041c00078404000c0348240511229a804c400c07040f200c0c8d804900900540c146070400003070307840c1c4c010715540d03030100c0101c4060008130a00c111100000d48110402080380c4c200e05048180d807441d20b89400b5000800740400c2a0540011003020080ca010b00032228240148070b190b4030f40c002e441040c028540064110002000c00c0056003d40004e40240d14814045190310b0036100035844081842503540f40c442d00401c2a1003074005080036241c0208003040340c845011103464545c05d10703469420001c1c034101001c00302c02019840c1c41c1e000959040080003400740c000c080c040a2610b0103485840d00710700031090b14040e60051002014000003052240003504009048d415907608400e25241c1016a4110ba84500350030740d941d061001251a00108040141074034070b61 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 965958588 1250 965957338 965957347
    0x501050307050f010903060c08011d090a060f020c01020706020d150e0703181a07030e0a08220506040905040b0c0c1b0a09060801060503190222090204090b040b0903 72
    0x641e5400c141e100303080c080d41d078064401007644d2240582402442d08082d060150803810300b0020007550382489154a0b0081c1c49401c0013410000302d1010b40100102c07402000342c44c00c1038886030014015000c2035a40b00360700f0440030aa1100a00250038203e018100c010f07140c0104001034019a16044607003607883d040214107000028411036102e410031290301c0c000950300d60349100f080c41035294a402901130a40d0f41c15600c41c086100c1d003550300c16603884d902403101510b004040c1383d56200c0c03044010a8001c0900031401e0041005200070003990404030490032007903a450204d0115481034014944c4103031101c0400c03041c0000c41454a812452100c9141d1401c0030350341c0c80c1c68031a014801b0600030214211444119070341c0b9044500050051104200300660395200b40314001c10162160500a00034000400c80d0350321007401113404941c024200c8825504d00344d289c01019170719019402d00d0340f41c2d2500341001589861240001c0c0e944504c090017400d0404d0b090550701140024460305940d0320810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 965959838 1250 965958588 965958599
    0xf0c080907050f10081b121f0803121e040f05060601050a120f091e03020c03030c1c05070503120a150311040903140d150623072910090501 61
    0x36a035030340712805840c00a90039110341c1c00200c401244003458040c0d0541c0410004000c885a052050140040440390b0300d4001078908c5902c440d0140707114020040d0000d0090429241d05c840a80d50b10402e0640710901d50103039035220380f01c0c5031400c3e60f003640c4544421980300c04000c81004000d030082c4090a0560074840d1030b440003800c09005005104540e51110000015503240da040b4225141c0d02410a0813a112038000c00b00c220030b019030095006100f007000c0e00e80385084c04022a0071202c5000040e1410000013061400c0c00307880302c43c3c00d03001c100042014a012603000c3c0041c26183c01404c01091050400800c22001d0301c00a083e018050708410320208001400440c403ca05400e068034080f81000a41c2000d0398009414284050078240014883d004d44540f58003201081c0d10880382c5811068507141d013240e611480403408540a01581d040781e407140c1500010b0510b0303074030032040750b101001048070741c1c4a0450704048034400074070144240881100340383c3e4154064501e01f64104032561410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 965961088 1250 965959838 965959849
    0x31207050f0325020402090a031118240a0f0303080f160e15090901030f020414040302060a050411040c020d0807020c010816030623030c04061412010f0c080907050f 72
    0x3202c0303c10402002642d1402107494035016699410030052000031710700c1e902c1c2005030148003200440d41c416622008011081c1e0303200241d503130280440b40e03101c401580310440c45503942c850611038244d201021a5000559885413601c0e03202030752081d65208910304100149641d28000500805440400e01c02007100840d480900c000880900b12110784039080d0795003140d6020301c030303056400c2d422402000001c410300000b06100c01d48a8420b4804201c90700d10091f10140c400000e540060058100c100880c1214406400950f002070003250001002141000000c0498407c000c02c440076800004014a065411030340d0b072a8005e82c1e90000c3d11211581400080004200400400240c540315000400da54460780c0600d000c3d0407103604903245040c60041c520000319135401d21768401e104014904900d403d080c0582c004843c2da03611500403500080040014040811030013a041e036580b050191006007290080804207840d5840e4528a42060152241040d071103401031030192000341c0503045603460b130 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 965962338 1250 965961088 965961127
    0x6030206030a1d100608071202090a0902010203040b0a03051503072d05030703030203040317091509032d070506071e031107060504260d05090f031207050f03 69
    0x400c600000c0d000300c1c6202c0e11400c00f02c4404030f28564880c941002d0900d42c2070303500c440c0c140c82030101200d0403103599041e40107540385290310094004841c04003143c2c1082d00c54108480461050045c0d905164440d1050701c0290411248807002039103d00500c90010a003029030410580d0640203880c0460400c400381c900210144a603071a011601c81ca2407110604808030380300036080050588182a03030342d0400950b6500503000a40390703c008844075804401c070800031075403070980c0900f4981580341d00c0040c240702600030f81c0c0e405401d8061150901078068086030150903800390740d2078421010302d03552041c41c03600007a50440f41c0a02c5040286d00d0100c1c1450f0790114441e03002c04180c40310b0054900c2c0480711000421100d030000d10951401048590b0804098020f46181e402c0c0504450711818009001404c00118044140c01106807800b003580b1503001803002c144060004407410f0241c0001c85d203452044100035400c03043c00b08030f003000c005062000d140440988001107042a41e8a400e0204030903c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 965963588 1250 965962338 965962351
    0x60d061a21090d110a0507030602030915070e010e0616150f020f091017040602250b0109051b0309010b03010c0503070807080403031b0903030e010311030a09020d1403120601030603020603 82
    0x2031044e440280c0f55002c106110a09038040255642e0990307a1078001c001e9041600c0940381c9000301e403107016611000881c01072080c0d1640c1d481b0211040300c013005560400c078003410141c0068040218032542d49030244904219840384001241640585504400b00d4004180c2201824010000d6440411118041e503420701011a801e01c030002083c8c40c2921441804050725544a03204406c010502c0398690160003451141505070b80c0701880000340c02c10f10300820000403c1041a40c0050104080d2a8480c45d400071111418400d903100120040310180c00480740081030303a440b134481d41c2d194142805460074520450030164210b0601d0000038010460003010f000c03c0020700000141414426000b000c0d03400320041c0364449050280700c0c024a040680d000c00c0d008105092030342c142a520034440c1a14140c000c810786801e54640305009005050024001c0c1e911170500301c5014003003201046000e00c140c103038000071a0f445000a0031f02c40415401401e06050506e800303c1000540c5035442280c0d44000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 965964838 1250 965963588 965963597
    0x815010e0603070512180c09090a030809010e010911031002070c14010201151e0806150d1a09031206040209060403020d0c0905011e080c030309060d061a21090d 70
    0xd031507140403107041c000d5100c0e54090080d4202031000413503980031640b680c1b000410075600b4828042d014840050070580c0d414540740d10060038100842d1183c140c00303802074150030010980c0e4071020445404d454903e041512901c031740450305025450b04000d604035101c0c40e2903055060210548410710080840e104000f500100d8912811007a8404e601c1000c3c0c0c0c41c40c024100c030089803038205400104d18820302d42541d010032550085000800090314521075174903040d003040c0100c8a001400b240310b44010003220001c0c0340c8444084420386c40c48145110706401001540c03280000740c0140c042030406407105008070f2040095201301d4a0b220f0860b0192074061714841c01415041c500014000d5903644490300030303440c0c0400481c5005141c3c861300500031111f4241407900c0d0311445030070b40b44e1590149035641640300300004082810818040c0c866007510b030070b0003c2ca840d960708501c0c18002c0e81c2d031580e140202d0000760045103c041c00903000640200c40480d0b401c00d2030700c80495030fa40c0084c22121811700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 965966088 1250 965964838 965964841
    0x80f0a110112060b0d0501050405090606100e0d0204050702060702070b0c07231201060611010b0a260709020a2d110307020a0e0402120d02370f02010815010e0603 71
    0x40d96642090b001841c0d80314906660300030098000d03008050a0288d01c1c40789041c0008103e01c210001307011030044600808450700b100120f00281c2e051258030003001c0d04400342c11001000340c3e8076846614801c034a25006011b840c90507070700c02801c1446503044081628405d1280b1000a10005400f5003518007003a461100b1907035119030b80b4101d244512019a0181070003600086034a019080039003214000d17200c0948141a118446083c1c6003204505d50300312440d110104210200c00e03800010018031000140c404100e0501054140f840e59044041c141d40c00184850b409170740565140700140303216000c0720000104c0e02c0c0c2030741c00b80e811018030410001d03a13041e941045c100c10b004882101e03900a05070071700ca0b030b0f860847c2c0309803490445060f882a6041e482c50308002c3e10204441c1c80d9070540c0c0c3d004d8041d40d40c10700c1288070001d41c069030079442494903100d000700c461240c50843d490540145030b081c801007080e20004011410003800e101c184052552840e03c540d0b0801743d172480b41c2d10101d842d10744a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 965967338 1250 965966088 965966117
    0x61513090209060415030905100e030304020907050906040906080c090408030601080709080d0909110f030103030807120c020c0a09060501020307060b04090507030c080f07140402070303110f04080f0a1101 89
    0x3d406590080c480f008000072290710541c1e015441280040c1c03003030041c1c030f1040301c140c075050040302c0840c1146411500100000f5005180c16840280c1c809900d091541c1040e10b600089462034120f50000204141d442c20203000502e010032a510551404840030b94661034265a1407440b800041d00c183d0500c00302c100807900d02c03401140e0a03805000c5500440c1c12851885000500303200c258495848035514246c0c6000000b40b00340700701c640242259164500d544d18555040300c0348030000303041104014114580382c91420042c02801a800c560fa070003800c214102c6805c200f01142c2d2a4400c174841840d0410800030307030360080203176203c00d5000000050800b16940229018060100c002800b40c01424008000c1054000c90320098820f21422540195080003500740c0d1303000c1c940141503428000e586000b00354034154000749803c1d4442c0c07902096042d100c0700e440c410390304940001c0e1039005003c40e040c090801d04100c0340ca01040d800f0300526448030310780c680310b00c00e42050340c03541c1c1080100e00d4903002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 965968588 1250 965967338 965967349
    0xf01141f0806220b1e010507030c03030b060f0a1d10050a140f04030c080105010e0123040f02300406091a040c050103050f040308010530010203061513090209 69
    0x62420401d4064468245494070810003007202004c498468010301c80522030240038800383e8030701020103846183c07805481c4e4400fa90800b0200208604041e203503d035240040e03c0340d10141c60304c81041c4070000d032501c044c80e81c00740c5030344009c00280d40d150080727072200d040c00d59800340856580da449040c81ca5480364003410072a64104030740b145200d80303000011070702c061201e818010070440740111400321810f91a080352a01fa90000c1c880c88202e000b400006010b81030b0800040040b00105081c001664080d0b0720206050310b648161a08141c0c1e0702142c6041020101003002c4c0540e011001c00708101c92900075081c00e030040c003520290003d036590420108000ba00541309a1341040b0a14008071842c0a18084c00c1d82c0b04540111400070341004e001c103030000d4070503034154040d903410380b1031010a0b03083c00c050000c1940c1507001110218040078068801d80c1c124081548005840f0f030000d40e07646040ca0074015203101c03801c1260529001003082002143c042c2840000f960740c000005a555080b4900140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 965969838 1250 965968588 965968609
    0x939091d180f07030b0103020f0303030903030c0d060801050901050601080c070209040f030306031b0f0b0307020a033207060506060906121312110c04060b0d0f140f01141f0806 77
    0x8203120f80c1d20080700b84505d01d0a1503040300d20850300c0c0e411511003030080c183c990000742d80d691410fa00a1000c903506208142c06040407080e5020005a0300d83e5500c0d285096a0303042c0c2e0080e03100d954810500165580c40000d465002020501c0360780b40c5881d43d80420345100300200040c1003881035400c4401003511940049004541101001059002e00c0380512049062480342c6180140a2440000c040c441041900e101701c0198000e003d003514141c50030340d0600711256400901120314000000f0321940241d55040e0165051106a2a6007042c50414121000500b40b0703845070005000c07000c86a0703502c00c100c4407124001d0000802d80d1f02e0329800074560b0104070000a061000d0500c508450a5001a018842c01c040300304940e030710582d01050100b154254040d5910121003001150162840758121000e015415000081c01c0315801c01004041001601d951090360178100040140000c2c007011b40c8040d49084441c0c551001c0c5a052804440c5c031148000401d1004d000000303800c540da41070340c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 965971088 1250 965969838 965969863
    0x1302180910091b030c020712080c070f0602030a02070503070515070519080c010b0a0503070909140618071a030f07020a0233130939091d18 61
    0x2d000e41d0454140f4544081000503140000924200c005450f4900c0018101c00b10740404800b618181810749403440c0700d138010041c801030f40c86080c0000540d0018580d80324000d0650382e000d1501c598810b10001d043c1081782c0e100340c0c46680814014001035070743c01080e55140d01c45540c15540c565580c94030b00d0408500c0020300e09070400c0e0b0400081400011401404041e90701c0e002042003034030310070401c007100007a8051990950311084043c0b2000d10258044402c1c140100c0e8243c0b4220450811149402c008032020100b2407049200c0c1d9400304010032800029001d0511200c40e0181c048084c96000d01000f01550080f10a44002c10030790b80c005c1c000302a43d140c0183c5114480c0c442d2130b40010a142d0101202e14056100c40241c001500760035043c0c4960390420980944a10724182614019140030141e61000915103110a10b58420b02c600f00e0000b080d103899603040403044c0c060050000800784d4004458070458000c4000c00e00c0c2c000c0550b0307030b210748890220041c00184a00d011b14280811004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 965972338 1250 965971088 965971091
    0x181209051f0e151201031509150234120203030108031c020405060a08160e031c18170c060a0507021909060b0304020405070311120603030d0515130218091009 69
    0x10303840a5130f0450098162030150380600c40440b450490581180e20030103001d01030313040351101a20454141e40050004040e001c00c0c50380c10f21142c03080c0c0343d44502c149145401b65040c0d0150881040040e200151082c0d0300d90010318159850315920507128403440804001500c105221805552426810746000d0b000240019840780b091000c0030300702c000250f40c000c030b244501002d00c1d85490b1003100094034006026002c2d141e80100d54410803103080010201c1d0060110112001034405008880e10300140110348141c00302c3c0c6408042c107414a0703640d1210718040c1c10104041c540c0540c10030304484201c1e40c161040750a0040418102c0140301d0250030482139a418a44002210480f84018600441c02144c0400c19522903200903011991036000c0340700311400600030100040710b0b04010942c4494042d007500e24054480c84008100c9a04442c210f680040300090310180e07080c0412501d400400b4034000f1841c00310622100340004c1400e0b956244203032103910005006480741170311403000b071003c2e810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 965973588 1250 965972338 965972347
    0x19030f1212061403010f0e03040e0a0204030803070f0306081b0d030314130201030f0603031e11060a0f05060a03200111010e070317030f01090e01181209051f0e15 71
    0x10842c43c0c0f620440d1414442d600306100482c266070306204071101040d10000440c6010310380540c0d0145010010504103a296092000001154003c0025131040d40c061391201000000720b54040c0884515400a2542c0d520150740c0e100486c0141c4075228984008072040140b219a03840e040300904503000341450600c4480080c000700e0084d820b0f0a50155100362014002c2007020f0406d8011aa614800a0005000b0284010000480442c00c0c0981949841c18101c0c2c592101046454030205903010b6076203980d80d40c400d0b4802007403031180940001d07007150007862480c85d64540000d2030840100310340c01e0380c40100c1c907503102da03000760f800c20b5030341c2c8007900240803401c4030103080c544401e039912054417040d40d01c510f2a50061070700d000b101d202d0b00107d000b60075540d0807c0b4000d402030440d44002d0516641c3c9203ca1441d240844502c3c0c03001510030b2250021100700010002d000000d5a40518000c5000c04c2c0203003030f0303100d5201766032107107078800d142c04414284040700161401c0810101219034020004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 965974838 1250 965973588 965973599
    0x71b051606050c0111090a031425030b0a020a0e1002190812011a07171b0c1003020c06151f050406090609060c0f0c0513020919030f121206 61
    0x3009070400d40320900080010017815002c880040c81980c8115501416000341440014801d61403081d00d0140207003100c1c0940c0c998501190b0010000041c8441120030f03180800c10004080140e60f4040409001581402c6412201810b0b0007400011a840342c3d1420340c500190900c200f046415080e042c482e070360fa4003075250814001c1a801281d5071109140110004120090f08440500880c19145159850402c1c607131a40040d82c6101340c030131074100000f00b08000841480040c1c010900500b5070251410151ba0f004214540032000a21404d141c018061108088404580c1a51061410f001a850a030b11a0002511340c88044a8607801c4207138400c0740c2e10000d07408000f40040d2030140c2c40d2200015150031059543d00c050b8071940f0002803030b48002900188502c1d080018081c411a0200941a1900b0000300061004100381807d15808640300142b40707445c0c02c00700d5100c0850a4904801429038640000d14044400b0190403070440ca80100c0d00c2620030601c00c101c2101d070901c01c1190719283d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 965976088 1250 965974838 965974847
    0x90c100c0203010c02070f0e091509010b03060603120d090501090204021914041a2212060510050a27153327060f1106071b051606 57
    0xc24242c0c0250b02c0c084904440c9800019400c1c151345a0881d11410145402e400700d040c01070003404003a160103941c2d0001c1c1b880007c060702c14015103480c2c0c00481ca141d01142414a028802052035109602115202c901c4001d000704860160000500c0480c6501c202c2c14503a024202402c0025003040c40002c00b42140b02c03071502c810b2403c5850341c1d07800446a60340d5a2a00d070f1070059000c1c900750399110104d000d88021a0000600c0240107800905c10492502c0e288007000c02c099500c150072080410200d101004910b1140552010300007801c1c402c1d480c1400082001881c0900498401d070a410360440040082914003000f0651003c20600c00e050203014614202d040d80c0c407841146984500e011802480701100c036889441c40c507080a003040820020844080001c03160a44024244140c0040f541b100820302602a11581c0c5810011b00300c4124004c0641180d00312901464000700140110b140d031010740c200345101810070485030a601c03414070710309113a01d8a1000419040d003441c00541d20360030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 965977338 1250 965976088 965976107
    0x60103061b03021e0a1b080301061803051203040318080c0a0504021215130603080a0e0d0f0201050d1b0309061506020a021203120c0d060605040e0f090c10 68
    0x2907082070400075464181c00740d000f02c0f03d850010120002c00c102d40c52240708003410001c4001d01e4000c811106401c03032190000120701060314800340c000014400b25410601c1d48448486412004103141d03c0c0d82c840c6511005034814404000030000080760074944074210b01c20414002480f031106160341c3e00841d03075540300c12000003405140820310014040c9860300c01e032208518980010455035441c0d00b4219045641445246d130712402c2c140c0d10600e2105030384a80d601640c86001015940ca13503203e4003030100c0f003a111080348074450400c0d01c013001501220300c00401581c2820200d840d580c2000e00800a40107500c0c008901c0d195900070940781315456003043c60100d01490082080d01019494541c0303c981c180900000340e80005491401030800e05d40d00486142042c0640341400004041c3c1d43c072402c002c0d81c000400c4034011415861040e22072240300014559428040d24041c584120300280090051003a91641041800519048014407400d880c0c4540203002d0604a540c010015002048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 965978588 1250 965977338 965977361
    0x605030d0909140112020d0c120305040504110310030b19020a03050f0a0b0a060e0d0f031e08250c02090c040e0109060b0412080d110c0105091605060904060806010306 73
    0x41a0840c14160300c01039046050b00c0c1007102c00310170b403e2642c00740001ea07180318070100c90021110000080c40915159601041032081e80d449a49514140810040e41c000307107252203042d0320400a1000903640074803034034100c03a8001e41c2c1c20280e41c3d83d8160b90032004902032681c5002400041c0c104c940075410f03071065108900201102101e0340320444030400300d8100d441d0091300107050704414405140620b03659054081b00402d111403140560b640c5a50206180300124042003c0350420fa04030442a08c2c000610303203003458040b0044c0342c401034094113903454415500e00c0400101d00e00381d00e18800c0718680c0525801801c0b481c8523081900f0640c0c50346e0300510900c036443c50070303c0020803228800d00401041358551451241401e06001080100204500084505200400641c881d0b0b91160182003052700712082c0141d203400040d511036084d284004c0074142c00d43c0040398000c1441000070b4210341507030703000c1e1140b03612000c0e610046401052550011051482803000000030801d0a8003c43c04100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 965979838 1250 965978588 965978591
    0x313051518010c020c0303160606090f1b0311120402031c0e03070506090f040b010507060912030b0d030f080712050901060305160305152502010509010b10120e010605030d0909 77
    0x6080742c2080381c035403442c0303201742da45608108000d02841a1040d480303001301c0d0156a0002c1c0140d40c82d0741542c2140d1b45c1c00700d2000f80d80c0c1c880030030807004011942413201808030350409204c040140041403010b80700d5408006030306141c1c2d201040542d00c04121010007621560540380a240060401602000c1c241031000d10071b11800c2d4011a860030150241c030500c1e0406000700c00028103070010080a08024101141080010700c0f2002c0840c040f4064880000e0080c51201a41058080000c084e2442c554609024052070680100003075800b01d4000c00000b034900d0098056158044220b820401c2c0418554119040c030090106100043d442441141d11940c101d4540c0800c00080c002c840380144805000c90300002c55207071010030800c1d201e42c2e1007850340842818004100001c140301c070303441c04400b10050390348134100050300c0001d11800e10b940e07008840c441012826541c00030b0814560359004402280c1311002010304510075040340c8003501000b0182e503500301c1103075070003012000c003071003200001e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 965981088 1250 965979838 965979851
    0x5040207141209061218070303030b01090603050c031b09040e1e01140f0405151e0c03012913120c0e0c070201050a020c060406030207060b15031305151801 68
    0xb404010403202c0c0784801401d400c0c200f090001c2e00c0c115440f0300a1010320060880d01076400d000b081403150308003651003614001000f180030000140405980e41041d0181450306041c002414600015039500c00046005002d91300c0c4294074202a40c0510310b10b0580003818092030082902c80400c0d40030001c039130300403081480c040303024001e030903034070702c0302541c1d03504040c91012801051142201c1c0354050302840c1207400403030039014084c0720b414003203418440300f80b180344492658610b811100c0703801c03041071840035085506081c800b4051028141c20004811007150441840030440030681e800d1114160041400640d142c8201d44060380088044a1050900c41c02280720001000e09a0213070041e800c10f40e040c20010313801500c05500c80410303e02540704660015920741c0d00d0f14001d0000d414682e40140c0c80704d1841c80c00300d059030502ca00b640d00c035502e18403140300da03c9804001e69500c0303060f5405640f05c010b05801c0041c14400070b0040503200e0b01071034041000c0020718044e01171a40d84880c0082000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 965982338 1250 965981088 965981113
    0x8071703070201091719060b01121e02071a1303020f01050702070b2a07060e0d0b060f150f0a0906030c080615040504050405012a050f030a060504020714 67
    0x280d1285140090208680e014241311002e2000c01615400c15820100c900d50061248042c011b06020300b42100c10384c0d02c3d1080b28449503482800c0a0300f40403413502c284014a42d81c0e1408500030b0442c844510501d030b01082190030b0050a9090420604503200341491a041c6214074414803001400c0c01c0c2c000d8420b036001400f0320705052080600c00c1c4490f6014014250038403606054950280c070a000449500b4000c0c4010003103007400c06070308040254001c04806e842c10201500c04210b15500510400300e2290314400308840d03410140c3d200c4003c880701800c0030054000600080c0d05125404999078011408006007040d8200815800e0030325203e072019160f40c0d00e022010303122042c214000182e01e10700820b040d41003070800905d40c02c1a0309080d60130181c482000c01c0841e00c0443c2d0030350f035070ba440c1e02c9540c401c2034503041200317540c81c2d981d0480441884161000783c06481029100c0403218000070004120070115400700b00036100051056644a800c0d0400122211002000d5a03850289040c100310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 965983588 1250 965982338 965982343
    0x20d09030b071202221415040e07050c07030c0e0f01051c0309120b0f010602191403090405040308060f06041202130b090c03160801061e020a0c080717 66
    0x11a035000c0420505503942482c00c0343c4403030401e0101041d07150203004a4110034030303810b034503a00b1980884038145240e00d000c400e51616840100194000d200100010b407014030f01904a900f9a06803011440040e01d1300141141d00c5d2041100740325250041c0a004003c2004405800e4100c0b0051b008031595508c6411801c0d01d81a401e1042640c8202e14041c150103072040303610003c9030a4001c0c1009406165154800d14103000e40304411a204402a01081ba181d2520b000c100d015050078401051481100445a040480074003009006101401e8110600510400c1129011500944240b0903402c152801030070b1031006940081c811014904041020b090400c250340c00c442ca01c003106003591110f9005d1041601e41c1c0c1040149103031310b540020350316417510151580154964030881e0b680345010b01052802103071007104002004142001040782076402001000da1a1150007041090b601048050b440e20650480c000e081884a080005100300e011440004a0301d507141d960202070300b003c00703094 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 965984838 1250 965983588 965983607
    0x91c0507061d060f0d0510081e100905060718031203020c0d030c21090602070b10120b010501111e030406020c04141617090a03090509040506071107051f020d 69
    0x1140c4c404188810340d0101c449030820380e0000f002e00203004842c1e440364031490501a48421502100c80d4940c10300c048080e0801c411290f00107081e20030080080d171561841d450b500b02a00d12401c203c01103a07200706106180580c0c1e0010340d030094580d50314554964006d80650886041c1c0003503030080300195540d0b00d00a000c2d214138003902d03035100c0c60040e200040004c2208800c482103440c042d541d1415500044d910300c000c00e04079001d0401c8102503d02081951004100c0f5009009a500c00713810b00030014a11450407030554409080c20991018010b1201c0d03c2e0540011228000d17213640c2601e0224002c0c080014030650300194292042c850b800000d02c0b069900680e044840c3d61950b1000991080d0f0301c944000110169281c0f810051005d03045000c081001a5400c004a0b0000400c220170150040b0003100100415907a024407171615480f61901e8050003003500307042c800352880050301c034441800038502414004041c0400741c1c1c080300c6a203050406d07000c00b08000d4400c1201c600c0700d0074028401003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 965986088 1250 965984838 965984857
    0x15060804051e12031f0b13061407050a11040501080f330717060906010c020132070c080304051509010c0c17060a11091c0507061d06 58
    0x103010340b41c1c07502c0c0d40344804045009a48040e000302c620b010f08002003a0004c40c024091301182005000c0303407401d05807401ca42c1e0b900114131884200329040805001c6d0320080200c5100381080c1c10191015100d0720346c02d21601c1d00091840c056140071504201607150307046203030403040c1e404100580e2502c0c0030b159148101c0e407401041d1703031001c1c0b20021415040d02034500e0300c030702c011031038034072052081d0244100d900d05455240c045003040003800b88154048401c0796100808039407608150030040c0010f42910303007210000e0b040182141800c28440800003141e000540800c01030342c0ca014803140c10ba4000d4016030411038071301a41e1440095011070004c00d440c203849005010801d1000d01101c0105c9591050701507078184000c058900340421149c1640d42c000f800051250580780021101003410140c2c0281040d840910b0400410030042c10f0109546820704141c603d07904da44950300c100421085d42001c0107140344580c0700045010b681c81440000c00412269140d00300103840010007510f8020741448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 965987338 1250 965986088 965986093
    0x3020951030106080316050118030c060b0a05120a0302010506030a050606130b040501091b08010e1305010612051525030507030f290f210f01020a031506080405 70
    0x40400ca0120350300556a0010000100da03070359154401d056030405545444100015400c11041c0b05080c0144035481500780000c22440c41a03a40103400300000c00c50281403144d40d030f20748032255101d0260610181000601c404031490080f1100c0d9a51210403404600650a1501240345400d0000d106d0710041d0f884000307014160780b0a0140302c1b26804407000c00001e240c44000c01c030b40b1a103840c41054081d02e44003a01007000007070700401c2d20310002039007417400c10042c05070010030402c1800216540c019002c0702c2c0000c005036260030410301414450b0448081181d43c4215079041110000e41540891408190341e0025510781003440e480d07242c803503417141546000340780700401c01d4840c0d071001e64001002d0800040c60340d00002044102c03000d20000080e240c070125540110b9030b2082c080050080c80c1190008821000300010958040c02c0c0340c510000781c0c40340c26400303030121000d0281d0300180450800031500d65001c0b801c001c02920f512094505140e50b01c038004030f40c0e14071814610b0303c6903070030800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 965988588 1250 965987338 965987461
    0x6170c0406080907120c09241403030d1e18111011030316080901290a0e0a020406170421020c0406140f010504230a030209 54
    0x40035030b0300b8200104002154001d4800100b9921a001c20702060140a0315801c98a14148030038541282d113015100d900b000f80b114402944c0b51a405041e006481c0404440c5064003005000b0a1540c01001044c0040c2400c2c2407918210700741e51003514020b4a001c40041c40002d01042c03000410704800900038207d2044602c00410508106802080304c107000c1c9801c0e0704458140c8040d90440d00180c40580340d0035100301844441d158010351003030700440154000c0248806154580c6282c001c00e01041004904426100d01d00b40c0d141c600d140300500c0343c0600c0401d03d01c0e01d030030204020b51050007041c0100c0e4030405200c10701541002c45070b1080358808a031204409036207041030010302681401c1c4003144200041003005031241e005100c0145200030103071088106d002c08011612440c0c03d04107040150a12040011208041040002c1d40000c0704412140c0e04004c0852210340c065000650812031400a0040241e15402a21a0429505101041d818210300350320720b191170345c04070482c3d81d544400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 965989838 1250 965988588 965988599
    0x1d09010b120d031e020c010507110708100906020c0115030519080708070c0302041e110a02030304121b081914031b091003050412140f0d0e07030c06170c04 68
    0x2c0c0240c202c10307115130800c40c00c1142004a07100340ea00c0340d008029980d440ba0140200300c0c0d001041c0c1c1c0403503818500075004c05414154070607a00e231030300c030420400c01c0d40b00d8910400744441d90341118500e00ba424000e00c80942140c00f200e880064500c803c0358144510111401025940381640a030544d1241c13075180791012903288c800719a044000180c442036034001001005982e07c1c070440361402c07011141d000d003d8240e4846070045035507810401c5040c5808000b0302c6103659000c03044a40c4164841030088000c107041504552504008002009000048e400c10042c07002d0740025142c0702416156203c1c05402d420812260002c020401e0a440081400403800000702c0200002201200041c2c43c0e05008200c00007500410b451040c040110307940c1c00500043c40f01d000318001c1d1800d00c40c1480300319041c044000c4100d41c451000c042c3d601090100e031800700780031503400140108110104803000e440e2a030900c0314144201d44542c1d404144821162041060f5403e2564810349401251508141ca0709 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 965991088 1250 965989838 965989841
    0x1701060e042003010618180b0406020a0908100213060302092d041104030c0b120f040f0803090c041b08010e070c08040602010b03060a1a01110102041d09010b120d03 72
    0x14440b8050030305010301030003151400d01c1039200038508030b0f080c00c4415040d40484400c07101042e410250ba8540c0007014400700d0313003501f00d2503001580440d006a5902c0340c800121215032441c2c00040c03050040f030a80000c1c3c0c8032190003a00752600041c5151400566941040d800ca00c181281243c003e8604011040070301c80f8400748446110368418618408404080090704440d800e6801c981c034584042824001c1c002040314920103040084182442e201c550085900d15920003030221000c040c0c202d00140c10860004078142d0794603800f0310311079220309201c60f0098545419801c8280520b25041d48080c00f513250380084080070791682c41d18507250f420204080041c4200030034550030700c0765101c9801e00080740200100000d0840e0b42c00010f204070b80030101420040050310540105d4113200794a01002c0c0700c010100c0709001c0034244a1a5403050340d1545000e40034a9208000301c5a00e40c121001e01030007141424855082c0c84020090a80103000f00003206a441c000c802c1580c3c0b003210031041481c042d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 965992338 1250 965991088 965991113
    0x100c0c0213020d0c020a1109040804150201380118090b150c061006081e06030114070f18060813060902060307050711090103030f050f0409060e011701060e04 69
    0x700380c003500d07142082d8076842c250b0715405242d1005900c00c42007030041c440c50040c0e81d0383d05d55040701c0740300060425855029450080c3d00031803510500111030300503040c0c001d51100890002c07000c180d420044414034500f0b0b45c11001c40c0c50090300b0b5802d05414080c0d610034840d61800c28400e0ee240303418681020745000c02040310901e1260010186501202c3c03006920700688201d1000000030710a03442d1121100341c1649180d84408148401c4400780710003480c01e4003a010800b044816520b0040da074442c0004e001d002044140c090b5403000c42c0c00c8c4440e0b258031056000115015807110740d0501441007035030000b0900ca2050780005402e00700402c1c010003007025003103032007030041a0225028015030001003540d4020b030707030810114000240c801c0401c510120501c42e0100d048540504941c0341d5100901122601440354080140026010800220748404c0c3c074041c6c01c280008212540d241e0750200303c510402e00542e5504040c43c03c0c100700d802c00c14081c1100786c440c102040d01c07258550303690f1030800441 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 965993588 1250 965992338 965992369
    0x5100c02091305030f071103070909140a0503040e06040f060f080d0e1804020105070503030903040e060301020715051003050a06090218040c030f1410060302100c0206040b0d02120406020c100c0c02 86
    0x244120062050350701007154074040c0c5060b45e00003031251128607142d0820305433002000410f41000e020b020200f030001c0305407802c60340c220383d61342481da0350790000800400e50351440150b01842c1c0b0070041100a410f007203a005441d8203c08807004111079050607140020301080f1144d1289000841005810303c0103082508944103042850030b02005070340703135030450700110307581c44040e84003103001c0200d0000b0030b04498114006034021490b21185440e548054020f01c0083d00c499912000410700080b00904104025500b00050340c1a040f5039142c080003900c1591016031051009001c04886140e5194241d8040d5034000c0640201c1443c542e500480c030029a90b00351200d051440f01c4190700baa003840030f0044842d0300e150004005045104100000340d000c04140104480e092030350700140c0f02c1104490585800e45222a143e8a0700362503038020344a200200c4800c001110284010040282c02500c0701c030400c02c09454030407101a11450843d80c426034100000745c030102074a800b60030400020324a401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 965994838 1250 965993588 965993603
    0x3070f0915030f03020c0307050f090406150b0c06011d0c18061b15092409010204032a080604120507021810090e061b1305100c02091305030f07 63
    0x1681c0f40c544203c0040c1c030035402d0b009030708251010301c003510741071280c040680422030361809d040e84140040f034a15180104001d09481d510403041d025040454100d000800d5040b120958410b00742c0f0043c1d454400a10400c240004c1000a0312401000b49648902c10383c06021103c2c144501015501c02409642c0792590701303c8801c011034240c2020100360500251030719401084000100da1403d050707104018a140c0180d00300340710b801c004101400c00300c520004201d039403030656202d051402c1d0081c415948014899080d070200840b401451110304000160f6114887c0101551104625210751045500819074160b03008860103250042014240741400a0600303c48240c20000d080c403485c0d401d41c0c150f02d80c07003141d84ac02c000c120140d0082100200b50103020b05240e0610824800807410b107100380380c68521001c10f080b10183c8000802034010800144911070480011202401c003034100c440980c080ca03007030030001d440c29a410924224451307004000703610341071300000c412203140c0140d0320858521 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 965996088 1250 965994838 965994881
    0x3051303080304060905060702152806170712051f0b1203030a0c26040f05100f0606020105040c0e06030a0623070f050403020409030905030105090a060b03070f09 71
    0xc0d03041c000340d88074a00ca02400034821a80e82003041c60034a00800400455004c180100950101c100f42103412040400c0821130194105507000052540c5501d0303860541c0c41e050001070a42e81c4041034448110b04041a07500007900c070300307244c0381010400001801079840b4030107030b03119884111f40c1c0c1800c0380c1ea02900083c00e05003240009041e61040f110040013644084248042c43c007541c0b041c2c81c0f1400c180c0c2420700741d103501030b41c2c0d51030610140e405165003a420107000805201040c042020f49039804001c1e150452001910070006007404411b003000b403450305001084103401403240034003860708155581e428501c1c012012000c204014107013601f5000c1c0f0301ca0f40340015504d0080820031103100e910303208060100e00d100d004014004000e44100300315501c1e036620650704181110243e94064074003180740a0142801e40c1c0610450313010035050340c60700042003010f80340410340c0c03c03901d8810322040c005023210504051740d40000c0d000d101c03800070010200304000c402d1035119a545105248060258 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 965997338 1250 965996088 965996093
    0x50703200a030306050108070c0c030204090615030b250519050912012a0c0602030c0702091f0b0405130e0f011e0f05070f0e0315090a060b04021603051303 68
    0x20101d500d40200c01094a40c2420b05c240c1d0b800408042d4801050728040704032041c0c0751509442e100b2144800b034021780d59003c524050000c1c982200380c01c03040c07403845803a0340760742e911700380e81c50300e10031a1007800e030014400000c1c1c00840d81200000100096942c2c207404e00000b04600d0585418014880302401400c200080b10740d101c5c0b401400750711016100000300148505074031000b50188015010100380742b98460349980f40c10402d0030400d943c1041006840c0d54500c1040c0d83d1900c11050043c1d800140907080120035150506104000d40c08200d4405045988002c1c60900b40664080c40e0782c090041d400000700500b10b0b0780b01014042e181001c8640c100b0100000c0d40c21510403001410f14060001100d0b400c0f4942b034001c0803250345001c0400c000074640040001c02c850074020700b540070081101341940761a82d0801500000000e0760060086034102050115940d5140744801c89a240c14840034003013601d0305200343c1d50000e0000d803031004a142d282e5011a65580010042240d940d00a0000b001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 965998588 1250 965997338 965997343
    0x31e060f100216050f1507030c170304020f03060103170a0210022a0606010206010311040912081e010e0708040302031b0a0309350f0f0a0b070f05070320 67
    0x1a80c41e5401600ca543c80d4090b441011084035001503010709400703590740c0d60700c1d100c00b9520050480903014481c4c5075806450100c40c1544c16610180c5580e803011040b000c4803400703900541c0105c1c421900e48050b150380c00103058803040709200203007130f40700048040c10380440d0490080000132014810780c0d4005410200c11422130b00000129180c401804200d21005c004e01c80c1c2c850881c8200da0300500c50741ca04140000d544031014000100000c0103550b410215489541104090342c0d4021a1603541030314901000b40815001c17105888603105440d800a0520a000001816070750b120300d24030150765680d8001e4803d68801303071003207086202c2004005000c2188100d003075240c1803003070080c0842140d5400c004010028503040851201e01604042c01d24080302d0381804c2030000c40d25181c614011501361000e083c032341c01400001c0d48c0e02414a42d001711090100b500d000700ca200b540c042e0001e450340c2c58210b42160500d0841c00100e00d0030040b000209000d490b10000070880100c08541d00c00710b01e16041d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 965999838 1250 965998588 965998609
    0xf2012030c0c06101e15180e070c0605010b0c030f090d0b0c04150e01020d0e010e04020a03050415020c03030a09170403140609030a0c03210e03031b031e060f 69
    0x10804030a00d014010100068001d45105041005c030805007428101c50a41002c0d03813655140500070f440444080f8400c8200900000309607003180e500880c40c1180d0050080040140222119880c00001198203403282c400d40b440c1c03003448030045042444000203c0150760002c3c0c40faa80c0b2007028811039000030fa40040c502d104248410710152a030f4a000c81c046e82c40400602c8103010304c52070000441c00350b41e000440702c5026501d494140401484400180c4000c12403d240c40c1e0010b000080c4c50b40d1a0303825400c00380c0a103200307800410605080e40101d201302d006209211000390020004904002c00c503401180020340038804210183c042c0030701500c1250320941c021900c4c41d0305a4000c110b482010701c00d4076400321891018628144110340010300010003804c0c01000e1000352402031501c0c50b07160071032584001d00790b0350401c2000c0c81c00702216070f2a0411076006511007407002c100e1390307008050020713640a0320419454800e8a807220030410503000c001000d15800c406040384844141e500c6c5203051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 966001088 1250 965999838 965999851
    0x7031404170a1101030c140307090806130c150f111501090b100201060803090d0c08010204121e0b060d03050705011104171606230a0f2012030c0c06 65
    0x801c072500306440e0031052042c03e40c041c036050526040f089006c0130781195200345500b250000c03075a541e0340c4d16172065401c00019042000c1d40c0c411441000010540f0311048a2618018100c040805076900742c551066006071004000180f213844100c107507a80902c3e484502c1c41c501c1419209400e0180c401140402c800b41d00034104282c49401e040100c0c1032903011007841b5030f131a00c0280203043c200840540c4d02d20454903914003c400e015100c03414440809003030805008960001c4d0340d5a80e80f003411100144400e030f010303a80d001000680341c807144600603221028036031040c0744484550b22502003104850022506600b400310421106001039000c0c80b50702c031001b28103240980c5403800c2525803601034440c12409600d80c2e014010f55243c0482d01203a0000321002880d12240103504018503034007043c0b1441aa4005c01d0000c10ba0110054001a03d00140f0881d569202181c08852a01c4500340c078501e402c1c0c40b52604003034000d9985800c0c0c4001541d000521030456441c0c1a01d50150518003079084980 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 966002338 1250 966001088 966001093
    0x4051513021318150f1103070224060105130302030d180f030308040803070e13090b0c041404241707150503280e100c140703140417 58
    0x203400314585000020720721201d03080b0400c44100c00000c494408070320004054a00e411605030f4040c2c2c1110368014038400c07110130405001c21110001d107194150010b41d040000350003102e05040e01c2210b4240000d101c0c100e500503800036511600d00640e031a0b4444c210904111500031404400760320100310100b00700740340384d540056040c5000281c160f84240c49d00703d000865410b40d810400303e0351084440c0d401580100d0340b07554980b11000e0a43c0c400848041ca60b400c840d8070005c2040c3c040b9154440b03d0041e0007980c0300c0e14103680e452403102c190300c07880c029604401d840710071240090825030300a11070311041c4804c0307964480309007505040068095100e290541d580038040b0058000c2408800d00801000c9501044404000b0019045000c02000400881d0400301c1e8800c10368404107404c007100340c4a2504102055105030701075110204031440b400140e0801d180000103920400440e20007007040c5284a0074a119031380d0490f088030000704010b40e01d10341400040ba00c1151b10391021000a5141e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 966003588 1250 966002338 966002371
    0x313080307030e1504060e0303120903030a0b01031b081005060309010f0e01110403240f050919150b06090415081b0d03030902040e010f0507090f0305070608040515 72
    0x4005007076040d00700030310b030144c95a19045904038840070140d0b81039403454113080e000300c00900046031a500640018404c01140c038001d004c50604044000c50088900500500c1101c002c0d100550030744240350301c80c07181c000403402c1601d8021310554100c1e402060481d080d0504643d0f90740059260f800c01c1d18030104a03559240300c0314003d02584039400210759000002d00a140c210036001c0110301441c80003800181602c250561341c0710101b8007503240c80d40b600c00c00700048207107207029000411044a10803054864900142e0100420b000e4031130305503074000380300e41c1c160204c5418000034004518619400075014481c3c0c0030660780314022030456a2803d0301c0001c070945001c02d181d1404003480704214400741c2d03481054020342c903122010080284c2500300440c44010074400310703008012074a800c0c00d043d440d11290355030046650304464000d40707190385e481030600e4481c0ba01942000561200810b1030b4483c40703080044501951015a02c03c1c06182a2048010105000302c22103030100d5100048442812 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 966004838 1250 966003588 966003593
    0x1030e0109350a03110d050c1b2a0301060f120b16020c31050402010e010216031b17010209041104082122051201091e050313080307 58
    0x82a1159594540441c0102c00c140c0c00000c20900c2800d030003c08054460011085441d41e25049a450034400f00d000c024515109401185540210741d40782c0da91400704500c00c0c0712000004c1d06002e004403903114044101d81c0c5040c0d21202c9103801504030b80554950800150220b50100945d00420300341e090303152407000e203103070100702c021001b441c1d24071200c01c00820311641c1d40c0c00a18110080030a0710a6002031450304800070b0032100c40181b0310402880418a80c9203616070350045805a07101b0b03290f808a40005c0001a6140d41100808d42070301810084100041061b108a0580d044820100803165070788408100004008000e50800325030340009508586091900c00e00309010107206015003440d08180203e610f0716a80c40d5030307680440005202c003642039000740c11038441020414882407a000c59008501007424503105051003001e240f15401c42c04007040c02440b040b10703480061810f5002450078003040b00803c1440136903c0744810f0140c500d00e02c050307030450806030003917400540e151111071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 966006088 1250 966004838 966004883
    0x2030f0a0912080a0b10230906180619080405150709060f020f1b09010e060f130b1c1202072102060705010501090203011e05011d01030e0109 62
    0x900003a40c141d262400c00c07008101d11410a140c620024a40080c00340c03105203070f04e0068141c10035007039440498414110003c54000700c92030a84842d03500c102c080541e001c52060300394055000280c1c0c201004200342995080320036007804800600a0405041c03510046051482c0d64540f01c21102040c3c80c0c50510040c0041000303940140a400072000303000b4034100b03600501c001c2c2d05200b48420300c01e03c5009240c900c2c1c002d0281c8000c100c4104100c8002d034a1289103101194940300c00703240030301c070101d001242c03107202d041c110b130b203d00300282c140811602c0c60024001491900d43c02e00d580340c1d9403100e0ba601d541d80c40c0041040c141c1c03116140e07050b954110382022244500704000c1803003550b20105040040d2641d04418543c1000110301c101020103090001c1565407040d040004c005500e480000705206030b1550195040c1c85040d14200c003070b00c00307a1100149c140c10301d015031400318031503001480551040c1090580800e5041c0f502047c202c03911001d05003035900704a01200c140d00d8201d1000343d0301611 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 966007194 1106 966006088 966006091
    0x8070b0702120c3a0f020906130f02030f091b011d120105010906080706080109020d0f090b040308100e060909010603120809010f020304020f1908030d02030f 69
    0x980d0040d0405113004070103210300000908100c1e0504900b40484000c80b41d106249521010481c5c0030040010340c000d1101d544039030043c46003008074031103008000d92603500c0700003d6124107000da0701080c800c40040c07071050780e50320154401d814074200e20310aa0491030282419401c0d9242c0018240c8504042603440d5040303029421b105030001ca0540c4101d040318603858081104136200c40000d0b45071109482803400248480005102042290b4024038561000d5400066032114030312450090f01d10302c0205440c40210602040309040c1c01c4608240d01c00c00e242051010b01d401c02882c020804070103003445020f81c100b200020010b44007544004082c6801000c0803500d0448100f000702000e0003198804000d5003042c040c11042c0c6a40d0080d00c0c041c5a008100c0d80c0d43d03a5458092041d03011007503401d010030140c01304000600c04003e00040c00800c521074805a580d14000884050500c0e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 965827338 966007194 := by
  have h0 := BRFrame.cov_init 965827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 965827338 ≤ n) (h2 : n < 966007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
