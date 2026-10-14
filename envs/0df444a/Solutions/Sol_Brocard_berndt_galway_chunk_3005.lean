-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:49.077643+00:00
-- url     : https://prove2.me/submissions/366ec597-e673-484c-8590-e33e6c087f09

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 540287769 ≤ n < 540467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 540289019 1250 540287769 540287771
    0x151d1509030c0706080411060708250201090909050c0411040512150712021c0603060f051b0a140403081201151205130221010f0b0f090402060d06030303021c 69
    0x4640c900b000403070358004403200c03030915004556480c00d10110a10304482c0055221b400011244104071004025166040c410581501c407010304400301d1800385000c241c046c2c0810105d074810040308006400c000c011521032000d503818190000049000e9541a682001e414803010031b041c4000c2c140321080c18541200b0743c00401c6095591980014000c030064031040c10050701d500780940c00e0603250112040c9552648800c042103404010007002844a4002225421b0416450a4078856180109402002112594085003090101904807544440c4a0b8414001c00071006d41c2c0c03030601030300948000c41c040c0b44c4a69031507500c1c801c921100707130050300800360030420f0018850200350b2043c11091503154441001480f5190402d40f030002e03003134150300298000301c1041c205040130807030301c1c0140c0c00b452414001d200d005400707890f010903034083d406c4181e0401d60007107400401d482e090400b66007003400a0407483c6030080a0925805441e41d40e0410b80c08250000b81c450411900100c07c40031a41140748 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 540290269 1250 540289019 540289027
    0x206011505032502030c0607020a0201030e0c0f0f13140a06050901080606041e02030a0c120c12090c0803070609021903150f02130f090609020306030604151d150903 72
    0x6910100f11409005801e440d248081070700c0050082046600111000044841e01c0c602484e00039034031359001078101d00003800c00721203000f841d60001b42c000ea6800024120b525800c11101070098110410841c03607130080402802140101103842400901085107507021058501051b54106903955907002d540507010074001000300101c0441d00941060084801040510b1070480e40414200034181140240d440001401011040c540c0809911801c9882d001e500c3c40c40b9080000031142c038024024086158980d4684c1090741c5d40e8400c1d4000c40c0304a12114495445100319403954110400845116030394402035015031412041a441e51038900d4070050186003103580c1d00c40d0701e41e01c00e50754007011510b406078082c903406240c06039001407994100d5017415aa41307141c0f130444200e007486001c0e131880c54104086910102402140c2c45001c02500a040c43e41f1155a550807220303845400d01c514030747c1c0325040c0c6015500c45118010b404a29030042c5028180e0b0310040f806c0d180045c00700101c0381d000308 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 540291519 1250 540290269 540290281
    0x8031e0f01030f050a0c06050706050c04120212030d050717060a03030509210d03200906220b031e0a0504021f14070506160903030203041203030b090106020601150503 73
    0x144200c0d041d40e030f00c050704825003902e41c070704203103400a003500050a19200c48004600305500c0320240c400d070b50040209012030340350182000f000d0b1045000d0009103414981c0300901506202c0c00b80c1c1d2615640c0070403a464281d01c610340c0d400711401607a241d00050401105130741040b80b4800e60940118048490a400b03610319600a0038911030040854002c44000c00c0210080c3d420241d125070421029080d04e403054151180100180309104030051a01a002e00d604412075100080d521140c01c080c2020389010142d0b9101e0b0a0040c907800d02da10780c010451800b14a41e85140d000c1d5021b0840301e85010340c0c62001020041c11350f10003c154618151a00d81000b000d40c0e45c4166010f0f069102849000c00c41070661030440d54044121500081940300044c2101000400101d0522419025000142c0c00750900d00440b00c580f4144805070050b8010710003440890072805400c031445100e4200004c0301100900802d19484c001d0b4040310160300720000403c49404508440c0725600b00615095265240034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 540292769 1250 540291519 540291541
    0x3042607060807120b0f0a03060b041a0d23030d06060809030a09091505060708070b0702030a02060408300406050604022505010e0a0605061005180906030304090908031e 74
    0x2000381d4074101e45941a09260f40c44246d1000102e0b8000340543d844d80b5141d05246000d0b0a11a4540780914506204a0320740c0720710702d002c0111000002c1541d0040c03c0d0036202d48186208460100030581d00386c2420010204003013008018181c480000030076131b02c4c80e025020342604030007003800311260020004040125800340f1480144c0d1060b003c00248040c52420000c2d9481072900042e40000300014a1010b010284000c1c090035440342049030b041c0e0f5070781e034004c0740c485c0500ca0294003d40d124101241c00248150041c0c030406241541012201c0044071411800104600c107500c2500c2103070b000d0000707000b0349008071940148103460551030006030351303220f40003e06a0500c080f003896403c018041005820341003000b50504030022070325450348504000300100802e58040e4890b05403c01502d00c014000c0040e90b0b403201040f5002c0d408100940140a05080014040d5038180010400070400300039900c80e1411480c0100481c0d40c0324035004442d455021a01c60040e41c545d80c25000b00100440780c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 540294019 1250 540292769 540292787
    0x1120302160605160c210c120302060f090c0607240501050d081305060f0307120504020a171204230a030b01210f06050703050703050105031e03042607060807 69
    0x40c08071030f8011802942060b50740020150442480c03401a040800c0440348071029000e0410b010b40b0307803014040d88c0c0b86a111040c8240e510002c0140c1c110800003801c04021200c02030780101340006071124441c240001680f035030300000c4100d5035500da0102c00c100d003085041004031400c0800350100425410500054100390441c200180351200004a95410655220081006200207001180c4230400d50a04e50000d401c2101d5560000f022680d20303002c010101d0040a00840e009042445014206950000c803185949e000038000d02c2024992000b54601d800100010720305044080c000d009058101e04459039801a0a0f100c1c041c3c1c004184045140c48645d141101c03582100607803402c19611240e034009071080b601a10600801200c1c0b814041c950300f041e031007410942e404000581c2e800c502a0221031084c000c082e00340d0300400ca92440b90b050a040088682040300480c0d040c05c1e0703a00308c0ca60000001400c2070350f103812007901000b8640c4013003080030058145818442c005240400000309001c0b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 540295269 1250 540294019 540294037
    0x316030f080a38030a0f02130903080a050a140703050912070525030602180a090e0606100302090402040807031703010803090f040902124909080601120302160605 71
    0xc1c10f00c083c403000c070940300202200b000c0501502e040b03a042d4200450541c06141c03059000744940000c82d1404150b92044c400c1542d0f041e210f150b450345803050f0f41d0000b80380c0140880c0c1d005540300603c6500000c00000984522002da801156500d00040c41c903003441c1e902190080060003d120074400100003068100b501030482c120407000d00c40d000e10b2400c165041d41d0005d030220313100240120410346854446003a408041d02c04940d010758680c2c408040700c01401c1c629000b500540b000c0f8038180b03080e02c688460004245400340c10691010002401c0341d03c030740d105208a0b401400104100b1044460041d4038500c01d404d010305640c501890991244038040c110340c800e600890200c03100e90b4450740b2050340719030060001e01100040307041140d034031081c03400e0307480600c1100d040c1c40c490f510103c4036014a40c000e8443c901d80103946c00d5400304125500e15001c00038010000d0000c00c05040402c01280200340c04541641145960300700641081c03d05c0701046440e4180713075070501c0070a4129044a00c004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 540296519 1250 540295269 540295331
    0x60f0103020f06090607081810030905070510211e0b1c030206160903060603081b011b0c1a0f1501080103321b120a0f03110316030f080a 60
    0x148428007020100480e03508649c1d00080382d007415911079600d80d1000c42c43e20f2040c001c50310304940350301c1040840f0040d45940e500142039034044000c036034019070b815158640b45800116229500b4800c2c001400c08225129407580e0f942d0420304485e01c2c0c00083c400f480102c4034450160b584490700c00a44a8500030301c21006549c080c0040d80d001d62080c9031340300c002d64100504000341603c03464055620b602c80c9941440d400403815007154440810b119504054034084403d8041240d004419070f00700c0031054050b500141d140c0c040c089090340c1c0902e0148101d000900c0b0390176910b440505600d00043c840411410000b41a0042c070010310301c3e0710b1400800141d07a2501c03910200c1060100300e119002c18100009020300f400c02c00100c42c010841c800d50352400c96145031640c03207201c442a954171011304090a1321544110600c00f1170301480101c01c034a90000242c030300e4040f03c890f4280d80c200103100200d00168035850324200300707940504519048104144140581c08040013120900742c0c254448042e08 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 540297769 1250 540296519 540296527
    0x10f0e1b0a03080c0f1905010b010e010207140a0314010219031e020d090c060216050102280507030804030503030a18030206040215040e0c0703030e1c20060f0103020f0609060708 78
    0x281041a01c905e8424642126072001d1004000b2031030240030fa000329200d60a144c04003000d0340c050b50000d00b02030300603401026158501146d20503041382c0302d6055a00303c04007110100214002501c129803268580002584d01c010401845c0d2108110340c000300201450451600700c0c10040004d0781c288821074510258454005c5210310008000c0608000c10103c0c13581d03030005202e500800c00c03500c01d2980070348292529945100582e01c40c1311081600400482d94181c140280c01d10744c0f06416118052012a18100c1d141e07500e0521541c401c2e041500d29a0002c0304000c02e15801e8007a504580e02203410145003900c0541d80070f580c81d1000303003000340728406031403107070700398206c5001690014810b000c00e000c3d0600f008140c00b0040d41c494981500040d0404101c80c828400c0001c190001140740380540c3c00c80781640c1c2003105c140712040400415500041503281001200b0044240141c90b000040201540741d81f0401c028101e00d48ca00a000f584140821421592001e094170150b94010305a0b940d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 540299019 1250 540297769 540297787
    0x702010f05040b070b1b180d1a15031902010203120a0f060b071203060323070308030c1801080c1b01060b070311010b15030105011d03010f0e1b0a0308 66
    0x510b02035500500f914030700214808080c07140e0003c0443c040d040d09603490142e12601c0c1040c03900c521822030f02c00b000d015000402d001d2801c1c0030a00c407425a0113101c00003442540013620704c000203c1555040c04044138100940c51901e407c4c001c810610540404404603181c4550002c4d46902441441c003070414130030070005089040c43e03000090b00c0180040204105074031162110100d0308151029100c1040c46500d02503424040d00c00c410650b9000310301806000c000d442c81e601d400005141c0e4001c40c1c01410000800a5030b80c0010394015060385d4101520b60821009101d40c4c00f881403021410440710304144181c4030000c604541702008a50081035481401100e040c0c0908101d611450945000003094020b15500810b4403800b01c503044000e00c0308440e81340030030880950241c1103100365002040104800e60041004000c1007150600443c2505140000642110201c1c25007100f400d880d044a026013000074421280e00c50f4000d100d201d811075808020410b40708041c0030007002c003200000e00e112 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 540300269 1250 540299019 540299027
    0x2090a050a0b0301111c020306151819060206090129010c0c1409010803030606040b0702010c020415180615050702180a06030215030f0609070e0d0b1806010b0702010f 73
    0x29440384040c0c0284007417010108103e03400d0788070528011001c000c05101d2110880c5074022039004040c01442031440010100303001c1d5590348509140c00603080078041b548542e8a03000100003c0c40c64010410740a50724120000c0d00b03001009101001e2649080204600c005e5801358008150750b00041c0104d40101d40d02c0162840b51030044083d1550003c5200080d042d807400c8580d002c1c040c015282c80c11181d07a0b07800329907944d000c00d0703503010fa118000780b10038028942c8000161040c00d005250070302c400c407129008181203802c11116032503a60710340c03002800341d81041480c00c08203e2520b0810801c80745080701c40d07041e8148041982042000004401d0b040d5641c41210003480078604204e41c04504203042d60f080140503521089006079851403040c0c605c0b20140741500d03c2090303090704110b019070352081041010000241010180183e1044810a07511a403030f040900611a04a181003402c1c0301a0300403400300801030100140d40b004d801130182016000a45007041ea080c20803a048494040c1c00b99 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 540301519 1250 540300269 540300281
    0x2090108070e120f070807170606010810091805060c07020117180d05030601030b0a140103110f0412060509010e0a060908120c1201210807051507050a0906080402090a050a 75
    0x1080710321130380c0300d0700064807004510380c0111021071007141c0c16242d0b1500d10303c889051540b024840c0360032400001d0107550107400744542c854441030141e4070340d03a1614007510072100c9100c1c00049542a030000d5904002042041c85d403c0b5042043d0305040c9000343d400245204000c2640c1c108854031007000c250340d03800080301d00144034060341c1a00e102c83c50303484004000390411101240001e0510000c07208c5420850005001c0e11103806003001748503800001940642024401c0d020041e4041002d00300c0540c00c00040c0002e01403860115254110b142050029aa80981040c1584c1d1410080d0401078100050550030f655000b04040b039001c0d41424081207d000e05a03194a40c1801407080000080d0664004d0111552025010909903210312100c00c004050482d04440c0102c034610231004144154040c10f940d5105804968440c5030041c200c000c104400d9908a02040c00403d02440070f0380c0100704100901024605001c0030b03e05900003448101021b440c4015599a96011a0307000c4041d4101c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 540302769 1250 540301519 540301549
    0x303050d1409061012030e120a02040606020d110f06040b090304050d0c080f1c030e16030605011a0a081603090506010e0106090f0b0403060e0a15091502090108070e 72
    0x601482d1991910b0303101c2000b00e6003c50f00b450b2146020501e500c81031000511070760140d5070020303030300d851100b8400500307052110b4003280e100711000f1b40300503075442c0075450144c869540031740410515008064045d01d00c021100541350000790b000c0c12600e80c00a00b1a9215800c03401920103034503440145401d620407504880d41042000c2a0481880307000d8200d9004c6440d1300742140d0302901c4c0040c0c03040e154207044c051040f054821409800310144070b9000143c004030041c0c00e81d5812412910b011820140740d9104503456600c410041141c0c04074501806c0d01c2c90380706100c8500c0d103071061000a0880d48002d1061440078000c3c100d590740305102c0d40c801640282e0150884206503183c015020361072800740b041c84001303034040c20041000c3c52801140011541c20f078480d2400c0906556510780070301301c1c0d040d003040c01d03210300e001e0780300070a00a0407400350704082440300140070905070900c2e01c0f042040d80440003009004000f00394071030364080026a4003940510703002c101840e19070002100001541c1072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 540304019 1250 540302769 540302801
    0xf12010608030703080702030702031e0106210302071a070f0c2c0601030b0603042003071526060d0201140706020d0c0807051c1119080c130303050d 65
    0xc56440741c000300030442903010f600c50322a682d80b00310040741c0c1c0b03120b403220081d09074000e42c409107401d04070408148080e04038030f0b00102e58240c03191f00303100d0700d03248800d00c2d0844a00304160780014560180b03d40805000300310740d0102c00c01d541001c1d401c01c601c182c8900510740c2265059003c00c0c841101c1d480d4010344039140c41400d50703540d02440da4008000b5840c1c001780003102900469955806840b6007884203030050b10036811513071540c40e40503114034a0344146905038411103074500c103642d05010310381c00743c011854284801c420342c0c18014000e1036514100710004034144c000700011440c2d0411640d00c4213003100c03070140e081ea45200403124407250884802c08404041044030800c495500604132603001c01d41c04000d05060080d04545440050b9140c02c0400c1c4108590b10805450401449001d035421601141c0e0700c0d10103908035990790100c110f040d0005004441d2503c120341c40f181468020070503084071410149124401404810b03244001402e20800191a01c20184560401086240d000c0d0ba = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 540305269 1250 540304019 540304031
    0x40905040b060f04061a030a150303080a0609061406090d02150c100603170304140703031d0a03030207170c090f0702061605090d0f0b0405100e0712020f1201 69
    0x3801e026401c009542a5100e940910030001a90415200d041c0403030700307440d5105d10000b08142c1001038642c00640050400d0b6126400c0003056000c44c544480258480d9589807024a08400d1960031030340150030810807070341403910030054242a01c608029007a030403201581d4601280c070000390222803140000b501704194205071060000d040000d001411000c07415180441c048900c0c003c229091400010004140c10245030002c0710004043e603440341c402c40540c2e40ea0b0080140e0546400d10715802200011070514000218600d08a64103d030600d050324412106415650080d403a600d1034014882032103c0000035040c0c0e9003040003030350100d12024103541c8560800741021070f0010000c07600e641c094410f190208080c2d20b18600290960419a900c8505180d800e81c10002d540418400548503080800400d0303011580c2114028000c82c45003006200e4161002034401c1900d50700300400032690403c3c2400c00c0a1041c1107160302100f603040702c02100c01084000083c40e81d8901c404070a40c190300e000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 540306519 1250 540305269 540305273
    0x1e140d0e031e1b06220614070c0b160b0a150909150c09050402040306062405070602031005130c030c020726011803050304020a051c2d1a010509070f0c050304090504 72
    0x4588040d94815503950482580e405a020404c0c4941d20f00180b07030001c027100800000b0440d4010b0018500c00000c001d00b6060151a0350061300307400d40341034519035a2011801107940b5603001c42001400160400e0201a415460724084a401c40f40c0984003180c0764a00e01c04501d12400c000400740500078030841d110760302c90a0140050545006a2407a003031f06442070780108441540021030230301d075a61000d2034555541c1d00c0102a410251549448107800c034804141580e0351282d5a200645c64480095030804050300103058980682001c010364114003c1407082500c45116025001c05902c0c1c0105443d01e403100003401812042e5145207402e580c0f130504010968030200440c003a6008803180d0910310744580402c04401800551444000100045440021100213001000c0b54107010703400e0300a0350b018000181d00c44000e100321000015491195000100b2103880e9000d0401619080c0d2036142501014004100e400c8041c403d120028900d0740c2005001c00440e80501486a014002802c040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 540307769 1250 540306519 540306577
    0x20102030c0a0819090b1909090c030222080c040b030c030d0c0605010902040f05040c030f02030a0603020405010b0f0412050a0507030b090c01020a1e140d0e031e1b06 73
    0x8030013402200c01121449a40e01ca11031440d1600b030b909400c07009440c0400007900a880b0407a0000c0030030038420b803c2c0c800501e4060714070808484002c43c0c1c90160340da43c6000c0a0190514480c4c0b0b18400c00d800c00030003440074450000741903200200c00e8600040219440c03001900e0800d030080c4203a407500c991650302100c0c2d948030350188607051107036206001a176202c4a00800fa4000d1740240c2030405550b038410442841c198100e0200c00c00d190600084403004000e0720300690740b0803110f03080901e8a52104004508042c80f135540100b0000f250542048030f1000740c03048900c50740c415210402000740b000c0050203010300110000036400300803030302c109a4901d449007060000301c990a22600035a14600060b500214480602540c40100c004c40e50324440c005410f50320220324159140500100c880b58458010081048005007944a044a0503a41c070200744c5081c01c2c00d80c004802c58000b4400079540f0200180b11404440e0100c101c010b03400605012410500484141001d03030b00c9402007110f900119 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 540309019 1250 540307769 540307777
    0x5060c010f0c050a09062d1101290405040f120516050721020307031202010e1b0a050114030f040f0f12110102210705041e051921020102030c0a08 64
    0x11302c2e26511041a034034003040d11883c1841c0c18030340c10ba030b4a40f052a07045603807c0c0c80d400c80c07140b001d08195188a40c5007440c0350840b0340d4400340c9a2495001c09101400100280c02104000c0c02101e00780004e1400e42e40e040028180f40900030440c2d80d5002e6510030031030007042910f103455089800328180765040c1c01d00640e1054980f181e81001000e0802c05280d9030080024860700310b0f00a401428607074a140c3c0c03081160342d001c004210442d541c0341c0c00130650040a10820a500c800d2000b90404480d0110404c2549007042d07200a040c00701c1c5a44402d010914801a01d5000c0030403110712000f43e0303d41c1012003600e80700400040030603090000d800c081044165001401d28025641d44a03013080b00c0544900300d10565099050020226000313201e0000d00c80e80d038540c00361903480d2480c1000d5451410f40b58503049096044004200303158144250b0500a8079000585080d14822000c1442c0541da13024641c441440c00c003024101600f003400750b900800464400141440031074400c11843d040282050700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 540310269 1250 540309019 540309037
    0x1303080702062205152a07120b090105090c03100c0507080313061a0f0906120a05030a140a090b09120d020109030315050f060d090b0c0c1e03030105060c010f0c05 71
    0x401100c841c0d41d0415800b0541d488400c039001e51032942186c21a490000743d03080030f80307242544075900d80401c507042c014024020f030b180300b80344070402410040d0805003034880c002c1030051a540110f1440c982ca550000709a10480710000c800903001410250032283c5210f420009440600d0000902200007029810100003e0007800100610f00721071900e0b007445010030b500310740e01c02ca0100090660740340149516400803c01003500381090010841c0e1800c05c54000020394840c1c0021510380200c030b800c00080c251007400940000e1610300141c001034241003090140c0c0024203400b041e00c00b0a621514100e0300c0080b074820171160700ca1171090000b406851889000c40009050841d01400864400c0100040d558000d2207841c000d840c0c00c2c00e0240ba500905c00258201c5d0300c54400c10042a075030b414242c0900c0d850024540e030749805048a620f0182c034440c05201542c3c450320b80f183c0d080e02c0401904c1c15070f40c04440140e90703400092290750261200c8000307048500e10380b2885c0030300d40da0010002e201c494 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 540311519 1250 540310269 540310279
    0x43801060f0e010e2220090108090601030b0703110c011515030e1504080f070b0708060d050c0603100515070201030509070b0f03041a19060b1303080702062205 70
    0xa0000c011500f000701402e0b000c1d00b090407817900d503000380450041c0702c4e070200e014000011594012802200b4040050b003000c0040c0b00c6c00070344e4118550744403826640c80b44040004003442d52441d40c454421700b100405490815550b80b000042481a260884021406450003402542408902c006c441d100500c0707221511034010300b1000c0024068014407501025003800761030360300b0399148055000304004100301c0703003c83c2c10000388000d0800e04020b00039080c0560000b81240ca001d00c0c01912081e0003030a414030038407451414800280c000101134040d1002910603035120344409031100c4041c6007030b420081d4040f69800d680640d01034100040c0040c14000d0343d0500043d01c0c2c464410791118120702a4204191040102620744000500210342040c80781240d0302c9036103540d00e030804058009403020398500f42c500c549400b00d6546405002d010b0102448014504400491494180c01092000030000c0f880071440300255034a800559200ca113040042d0008504405401e895450450081074824 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 540312769 1250 540311519 540311537
    0x9050703200a170103142406010e03030c0a060b0f040903050a0e0a0e0a0c02010e0303060307030b0a0e012d0c0801050d0c05120a0c0e043801060f 64
    0x100d20074020440203400c0e0034031488050480c00c0081c10305a00102e114003d00c01c1112034191143c002c1002c00340203500511448a51203030200955007410782d82c1004554154a1050b0304542d81d0726441d540390004002d00b44034500410b05000b103802c0d0701809860b0300c00c1c0c5c00b5240801050003145d8012083e080c4044951308152600300b820001160340c0726501900003207060140b9102c903405402c624810700e40003014901c00707d0b075504101c81100310032100703940d41c40c5d155042a0041c640900904820003040d03c065800c43c50a00c002c00c1ea9015180310160008141d00301203416485a031b4400e0000b00c000750000d000881c00011410301c05807588040c10b600c5070054500005202161044d441115901d5886110992030300e42048414103841c0020b85042649400015031a0365492030914401c2070507000c0c01c0c3d90001e9042c4540c0e40006a401004400000c00030440003903110b1140000b401c81c0150541d16102215010181e4401d1401c01c0040714110013001240c02c030341042e10038042005a540744194 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 540314019 1250 540312769 540312781
    0x20321360c031c120902030109060e060708041203110c15090f061005010503190e01150509010308040e10090c022b1e020f010609020306040b010c030c080313080a08010905 75
    0x240c0d10402540303041a41c426600441c80c81d11881c20346500854055005ca005486900000e013190003100086071442c0e0f136042c540000d41024020940c1c40310315410000078501e42074452040113040325400604142d40c548000150704c09220a90b5031035880d0b03800303d6030f141500750ba0462400406403200c10301c1e8401e040402e14418800120b05224480400e10391080364644801074466800c00b4002d4090341e0484c02c4032514018040c8070b00010b01808100104004014080140c844991608007d0180000000500100d41108211011250021045103d40d51820364001025115400445000f0306140e428180143d001400c060450b191400d180c000050220803105401c1001004401142048101e000544d030078821840003640140113462007100700300040c2e405c540d0b040d0413107040c5039804010721249080620030b0400003070f020301704000d0308407198a014083e100100f030001d1968400100054448140b40901c0c01c80300d51001c901c5803103036003c90020b44000424001c8004461130f120004078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 540315269 1250 540314019 540314023
    0xa0b04120515070e10270509060102030a02120a090e2e0e0402103b0306040201051b030906030c07120801210501060b160b010501020321360c03 63
    0x4020b90300c0d40c46540c03407020080181704610b4840200d10051000400b507481d10100a0038030034081200c0d10b04120380203400c10b000c100b003120000e00058119801030080101290b000115400d02c050f4107114251958101d81c4100d4200300503410011211119400f400680314104000189080c050510381e00d2403a4514050104a4528031801d070845004201060141c00c008200070f50380021840c0c541303111702101c8000c15111145841100c0389c034491840300d0a01c030040c01848580d0341001c50142c50740307050030b800082c441d0169215280c940c0040800d4900c00400406c00c071528114003030304103512803234052036489103a0040d850035943c101d001c9148204191042244038140d65900030210100c20004c81c1d01011100d01050442c0c1e10340d0b9508021400d011400060301701e205000c00d2807070001e0070900c0e28036111b21040c4c1c0503c0c1035500612030007101100061007040541c00c0d0b00720580560f6124404420107040c15800d10408114408941090004d10360035805040d40d0a000c840d000504030060503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 540316519 1250 540315269 540315271
    0xc0d120b1507020d02040f020315031c020c0907090905040308010612060501050a0507050a0605010308030103021f0203090f06070b1f0b0f160f080c0303150603040c0b03060a0b04120515 81
    0x210000d80d08001c42c000500d010305099515500141000034a0f50080c1c9070b4104a900070764407508220240c2c4000c040030301d01000508400080440415402050310350069036442030122a42d105242041c0021602c0f48281d50b000c0c000c0406410900060a0605014050704020300a0781d002440c40c5004030a9000e5600600c8200c0b1300c180d41d5545803419034442125182c0002d141204d19014810f02c5401081d228066680614000d00e0241d540b03524510420140440c198071031205004521091402c860b000f1003070340c1140205644e0801c01800c044002400c47c0b041100081c162902c030030a004030304144aa29580300940030541d4020192504040d50050154921415000f241000030007103606d0f43c2072441ca5024403a0701701e070030000389650b25080b4681011200c0b80c0b03680e01c08070400c28550703d8031a00542a5009030750241c95800e045d1140e9101460328003400c000d1308000400704941d40c4580c10f81c50002c108100701c40d521141c4650041001c004101402d5a051107051544030703400018682071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 540317769 1250 540316519 540316549
    0x40609151418030307111f0e060319050a06181a0d06270201080f1504050424020c0f1501140411161202070f060e03030c0d120b 56
    0x10000c0d01100d4222880654840c0e1498151241c0402e004001034030100040c010042c800c440203070401420b0b40510810300c40850000d25050f030242001c101403900125200c0b401282910056641e03a600c031200c034006001a50150600d41c40e040030070074034810590100e4103944916895050200e1260360141c291112350901d9002154103151442a0303240c006180f018052041c140030440b508003481c507440d0040203225448086420480c510115a44a0325099003c0302400e2104001c0c2016007020b010a00e01c025403a000d5640e5402240030f10002c2d8100e8000d201100b100c080c0320780e01146140000c1c1d00440c046031883e103e40161700102d0100813600555114105202c18101e80c60607010009010448060f81e41142d950703080b290aa2408070020224105090a610b106036842e2038480300c2007911405100c00c54120100904c40074168140b010129041c51800c01244031140c0c0010f4114403450f4006059846006400c5044a401504400e501c050b16001004003003681e009000f1880c00003100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 540319019 1250 540317769 540317777
    0x15011418150415030803010806041412030609070216060905030609011404030536120f031917010914090a030c03030507020c1818010b06030412021c030204060915 71
    0x28001e203504241d403144208010154181007083e0307894a50b101c1c00c1d40300303801000249d0464400c000034070100100034001980c0840007072a4200720104150403601001e0031007445005c40502040266208004545007543c0800700061801e0365994041c1c0050707201d1088070f0090203541c0c0042d50300394040c81001191400b0700e0309201c0540d56130740e0803100baa200600580200c200200c03200ca00604400c048034426010b0401b620340d400c0048201b00c1c0c2c0b48401008840316910520100040c41e02c04016030719081e42d40d5080b800301c09240390081e00c94084203200d60701c41c076440c24000640c0d000980c00c10300140d40748003000d00061b2503020047c2d840389055100507010801c0301c580300d00082d02c65800725a100c03403144180c501440086000038560303c41964060307000c105000500a950010002d81c100503101c0d4802000044059004a8035502000300f025200207060b82c900340c50035000b4404280304030310549400f8459090702070090025046401400001806c480c000300391940b006143c15104015612 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 540320269 1250 540319019 540319051
    0x8010b0418020108060a09060f1d060d0201030b03011416081f06050f0412050a05190209130204021b010905070f080307061d0a141908160515011418 65
    0x64851604c042c100035001010540d0014007c0c902d41f00303250144c480180c035a086a86070441d030042540e0403540e84901c9503620000e0140d00c0d69110300c844c00c1160f0a08000c034042d428003000034014031030440c12007030020f507400400443d00c2010122140b030031800c0d00c440744151500381203600c4003040740c146907882c4504548184111760061010384400c1d01c08120b9a850142c0301d113440741f041c0f400d4290440c0e0aa002072054010010103000b40d164001002c0062909454103400041c01910040c0201d0f1022503801a42400c1d9202d80d012103110494030504e86400303003012020309000300708249040c0d80e84e0041100201d84403482448201c122841a401103080c8882a1102402001c0100414440400d2066201460301e428444108514000c41040c030340c81568034040790a041c1d17070b0f40c1c1125060900c012513400040030300c0180c07160200c610600d234140c1945441c2403464002d078000e07202c442c101e550000290700d102c006804581d5200541e429034004c0130781946006d10000a0b1522151103040403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 540321519 1250 540320269 540320273
    0x3090604090504020409060c050a080a1b05070501090b010f0806090303150f030c101107090203070c080703030209090103060203040302010c0c0201081503190305030708090714040f0b0a0f08010b0418 87
    0x24110b143c02c1030004000050641b666602e580494450080c00d070302140d0045554107486400555a07913001046036002d0001448002007040c040001c22810f00034000c0109100d414040254000030310700c1c1e8480490106961104c558051444040c07103200d1292150100140c0e042c0408000d49001380407085c5540d00d038010400c200300d007548000100720b40500c21402c200e034850351030b42c0004801d14256141d00c0c5052400200c101d09202480e040100340500400901c4000341d031203040c440d20142c110300942c2e2071f421185070440103031258000490b4007408440011090194643c0114000c070b01c642c00800040010342015520b43c081500d01901085416000038080e035070041e03005e15881d6000f4152400f4000c4081e984920090f404015800204e02004011407590010141604041c4000041c03c036686440e20032804c21101c02c0109025540768a600d964400e6950050208070383d00420702a4226151b51016086003021f1040110541c2450a6404141424801d43c055109030710303510f0303080000c19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 540322769 1250 540321519 540321521
    0x30303040201111c050c0d030605030309150d060311041b1e0e120c21101a041b0e010e0303071106070206030915011703180f040e0304170309060409 65
    0x6104101d103e4012a0341125001201c0c1c801c1464030b000d2a221580c8403044444810310f440f0f800c1e0860740525152800c180444d0342e00000742d403040d00c81180c2d540702d01040e5081c0f900d024090045260203c6040500c084100a50440441240c940694003008501403900380b04601d0540360200d20045846605c501c1079071180281000f00407070302418800c1e400d0784c1e040003141400c800c003201d02d9043c2c0c0281c01041070790700d00080c0b28404417a800e601e0462403451503440c291200500140c3c03003201561000e28541031314807107540c40d0058500401c10008100e600524540d40c03124042e0300360005112445441e0a580034800f05d111100b0083d0042d41002e903541c0e00c21201c1000f1480e0070b607020905010f8480140c2d01c00c40218829611f010281541c4d09800155100802040c1c10000900c1402c580e01540d0f00300010a450040c88861f00f880011480c3c0f80204203a40741800c2066086800c10040c011604c3e00040244101c41a10144071420044110016280c0c0030b03441582d9801441000100320302e25503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 540324019 1250 540322769 540322787
    0x60b070f020f033007080a051614150609011202010804020a050a08030705060108011b081b0f120105030106060f1425061a010f05070807080310180b030303040201 71
    0xc0540b0020324144600000703071801c0c2c2c1c00b4135801c0c41d0800f00030050002c00e2084414800c1c01c61100b10b0700341452001d94581c4200d0041910a004004000c82e184002c403108500c068151034018121000f02400305110035110004002c548005200080c08a400c0c2d0600141d50340c1201c1004614070b000502d240c1c011500740002802c2660f10a500d00780205440c1d4954003004c004203036480040d591307403150340303851414458140d010b03101c0c0e40d14020b51401c0081e501c2c0214042811075150442059640203440300d008003a4a0040d1102500804d9444d005040b160040c109560203484000040c1c1c1d8800415081c0c4429000e04d100054400c1041e0407181d000302c000c82000d04181d41c6580c20000c0044c109c0c040c0614900f0540d40b011003a007900c01c2403001a03c1380c1c01e43e035095030018960b400041c030000b81c004076114035940c04000d00028a5401e00525506450310140d11071941581c07410001400c110040f014000c800c00022210030050605606210307500030014040c0c091402c0d40e84075001540d440403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 540325269 1250 540324019 540324023
    0x2031e070905070c0c060207260f01110405030f0610030308060303070813050901051207031e0203070330020706031a040c02070905090316170c06011710060b070f 71
    0x21035180041000c1140d0302a1620072102d643c2c64640380340260400707002840c1d050340000195008840c0034024102c03100044511178084a201c4034503440f1304136005242410b0f55803c10344a51030903400c0c18000862000500840e10102c00310389190f4000b0700455220030042e10750214010f021007041002078010641d0f1580184002c041e03a080103110b40350140e40ea4002401240c1006042400f40b100b0700c1d11103151405010305550941d411541010102e95507002400043c1120110481703020441500d000c280d00010b5000d000c0d1800544c0c0c9251040c40501140d005138540c17401d40921800288640c02003203051481940181042490031006600406020058000008440701d0003907041d02c403401900f2481c00a54000c0100501d0b00004a085a0005e060012103410810076a9840302c006808001803c6c0c0200c1c000c40b560320107030408040e030710807002d109116006450001a1010209152151700400101030300c42c48134060400c0412502d00e170281803a00542440000301081801408464640c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 540326519 1250 540325269 540325273
    0xf0b0d050a1404030809013209011104270b011224180c0306050102120f04170a0302010c020309100e0307030507090b0f0406080703140705100804120c02031e 69
    0x4402e10005500d080750484003940885c000b24144000d4100900c5502d08223084459181003034503403807401c450b000207507044804100380010082040c0701000c1d4805841c81c00084034440d40c072680d80071130001480d0841e210003040450f0a07880440540310f40640b5100b80016503030a120000010840c030001e00b0f0758102c071481d00d0007803184010300c45881200c6d8400340200030b80f00c03803e1909011000d829510388000c804201410400c042009980001e01d0103640701c0101e0640383c407001c082c101c802e454012940001c1e0301558a90100c504c03507001055145805000754024000c01c00c41c10000da94900c03450f00c00d02d40000004a043e031407244600f4078154920801002d6503c284d6503904c803a03281c0040b981000d4580e542c0c44185440914100031460b0350410b05035002d0251074540580c2c40e84514040c407020b440c3c0c642c801360400d4071000501c040fa0103040020111305905038a508014143d10084030129104007100f09003d038000d0040100b1640c20764000c0007000c0200d42d000c10b0500c40c401c803130641e42041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 540327769 1250 540326519 540326531
    0xb041a0d020909270a020109060f020a050a0c0812180103110705160501020c120d030e0a060903050702011b0b0117151e0f01081b0d02030618070f0b0d050a 68
    0x140c0d02c2e001298040d80c1c210b00d503c40c034005544070f10040400481442002603100310303e034030f0040c8d0304481c1600c01c03070b4018108007402c01c001c403005038148041004018814010131408808110750002d041d0306588114003141c0b00011018111540361280354456441c902c00d51907921841d40c42034100070700000c1d2100649062084d00d0780d035035181c85604800c07441504074040c011310055a04000c0c42800842c1240c0005404041100c0d04e0307101c7e040ca40f101810113440d081003041e481800c0051003c1d0691055041010403040d090080c400d0300242c0c4100c0c0000c45810708600f070007121344040f81c05c00750000b04459140e440e08400ba00e201500040d0740446000303502c402c100c444000d00781d90340704d456a0364080ca12200901d1208010030300041ca101d0358000c1940051110310000105010060348040061000d40c10000010f001c1c40d80580f0000d615100303800c10004031000d202203642c00341002100b102c200c0c1c1c0e100c00901c007284019001f1a00c00c003030140f080d070b070400e50180c000c150011804d000002e0301d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 540329019 1250 540327769 540327787
    0x3030b030f0c060904111b01050604091a0705040509040b01051005121302120d051804060e011e150c0201110607020c0d080403060c0f020d0c020a060305040302120c01060905010b041a0d02 82
    0x3160024000c101c08202e1200041344000021b01540754054006c40d801c21039400207941380c481080346c370030300c0d031800c1100d41c0c0018640c0c600410864010b003800a210400a18040c60807160112090055600881c0351041c90f101807170140b8143c0f040d545c2008a8030015036500344420340507641103c0d00340da1100c4000c82488500c00144140e8030800c5c01c50743c1d0140c0d1060b95030386d01c0004c0200360714814007070f030b01e07000041094145485006041d142001044c1c21203101403040d8a00d02840394020802a076117034400d9180319600305d00500c80261003170700c2d071000b200c0402c000c15454260880e06203000d6044980c0740c000d5403900c44442c68483e881046c5250810f80c403911088200d4061417442d6021a03a040b20620105404001c91620319116140c884180880b40d801b280840c40c45104007020305844402160405000703206042c4c0840081c0852070720783d8190700c1c20502a007801d201e00040030749023000205016003440100c9054030460030102c00307a4441007111024035402030300ba05142036400e210070a5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 540330269 1250 540329019 540329051
    0x120c0204060906050306010e0c040b03070509130c1b11010c020102160312090b090634030e1905030c27040305030a050105040903020606040c0201091e03030b030f0c060904 75
    0xc00b80c050030800141460501c01030518054040e00040d209111103003c00c0080c403043c008a8041c0e1b40f401c25001d03266290b1344010340d00c9010f2031801c2944807a0000b01100c020a056220540030280c1e59a03c01e86a005a03151010005405902501c40240180402c1055000d050351001242c4188120f800c00c0c0c8403032080241032106504103c0c0c0400300c0200440e41e840c1d101284002403da00c100592510840400040041c41145025449000c0c04208207034202c500d207040308a802d124000181061040346401054400c40c1941d5a100d154281c000080301035841c04008140c410140040c07010035660030410940341465809680c01d104038a182c8104804600b4007039016901c00d4684a4403030a01031035500c10b81c3c005810a5004078641681200441d40c006000ca0304640c064170700040f0700004030b008078058a041031000d801030b110031403104c9002d4002d49402e250b050003030764104400c014034002c040d2648009814003045601220705001d01d0b1070080000c000c1001e005000103094420192080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 540331519 1250 540330269 540330281
    0x403151a06030736153f1b030e0f010c090509061906020c1008090307030c210e040e07050d061e11090a150c060b04060306090530030103120c0204 64
    0x107180c41170a90072141c0303a50440024101500a1080c8a98001c050035580d20701002d00c1490003441c608001e149151401315501250300041c42d10450940d0030b0700280c0107400380486420040703051141c2540c1c2c0c03800032010320aa000003601e40e503c2c403024920b4041004000c00001d0850313603110907452200e080b92000500a00e0007400c06402510b04400c000c1c081142c200d40780e518210038404d911f0101b0240d1400030049880303655260030450b0b10b01c070083c201141c0f00020700d00120340e0181504100840c06070041d03214101e541c011a020720460800d03140c0f040c1c54032428402d8a0304143d01c141d00b14001180341d08040074648605410b41112a10320f407100068034040b0360f15100e401070026801482e030410070703405000b40036030100e0b002d0111a41000200f01c051540d40182c91039917200e4100d05142e880360403a00045030480e80c213100e07001c2982060f40c0c90b00d42124800080040d0840760b058481581850440e070134004442107030031070386913888a40340446020005410040c4c600c0c1c3c044010380d81c0703120380 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 540332769 1250 540331519 540331529
    0x21804270f12020303010e0a020a0207090507120608070509070f11010c0509031b0a050103150801020424140d02030402040b0d21050c0c010e060403151a06030736 71
    0x1140c1a440c28281202c0c032038852100401150010001406000a030210254011aa0710b0340180d44028a100890800840382c21203c1c01500f08018800119848505a226500c090404110655a0780142951280d1610560ba0090302c8800046c041d07500808000c0204100c90900810302168101c0c0942100d000b5000c500120380080313290907581c107040180d038040e000200304d0302100601c41c80000e446205075204280c1055107883c1840022049c540c00722008003a50b000941d19039440307110700c1100505004550340c01c1143c0d009641c12181c400c49400c0d0f40c0504800c051880c0041c01e4102001940c402030050b030300306880e440d000005440f079210b40c403241c501034290070f2f581c90724000301d504448002d070f1484410003a0520131500c0101700411002c041d01c0d0b003401c186880441c00e001184490050350300141180c03400008528540c45160010141141c02d522960504076071401048203078001130703034210002100c48005a000d11145030303020300020340c000e14140b1001d0035100941240c003074603000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 540334019 1250 540332769 540332783
    0x5031c180305033103080a050403020c060912030d0203151e01030515090a0c020d030e1c0e090a0218011b0b0408040801090f110604030201140a030b0d081c02180427 72
    0x26101c01c0c1640000306c2d60b00302100810900c40b43c241510025511003100300d0051150308000b54101007640c48000a003030506109042d01d8403006040b55040c003e400c102e4070380004924400b10880f4600c0c4c968401d030313054581c2c800d101142450b510011401031a006120b0134070484c4100354044983d13654941240300350030042005c100800300d103500038140303901d2030900003c0c103003052030b848120130300812402d40b41c1c0400c803010f14030016000c000b00d1740540034100c07498000c80e20405000f45d4038410f400402170305541031401342100c2008401116140c144000000f41c1555448440c1e00250a203001c468009005031b901034107141e16101c550f0300311522800210707a00f401104160082280c280c410781545841100c1d03840c1080c0c61500080d14503030042540311960200080d5405440c0d000764800e0600560150507400300d8000e6140c030241e590b00a4054803106a65001d10041802e454000c4a0f000c1e480041d210344049040c00600001e047e1b0000e0020400244010b0040503882c03108420304840d009000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 540335269 1250 540334019 540334111
    0x206190908010b03031803011503052a010c020d03110d18080c0d080307020106031205220612150306141905040807020d1a0405031c18030503 62
    0x54003a00c6400981d00109259040005010990340c011003038404941c0444038020b211417440700024010407200684c8442c50f41000408018080000381c1c0019888458000d00b0321490309a9a07140416145c0c1003490004030280d17a14001410421406203030306109081800e8000b910080d40b9043c80c504200302000152148420121400400030600050040c0c0d80906902c51200380400d0b103040c000000600501800004542524800d5021000958204a400d0010340030101d00505c2940658042e681054003081c185480015500f00c640444401c1d4440400100e0a41c030305030f01074256498682c0e0441c410520002c0070661500482403800d101521510746031034144407058820004c0108001c00a1525040200044c901821102120340489403803a62645514004031400c901581c40c0c00b41c0281d480900c420018000085d0400c5070300301c98080402d000c0b01241b1000c50300c050000300380c4400d0f028070b43c20100b80210019500129411400325611088a000d82040b40d5525096080c480c0d03145 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 540336519 1250 540335269 540335317
    0x90102070e0417070c080f0c0103050601020c0d15060b0f0408150c03220503070c030303060503160e22050f070b040b270d06090203060105010309050303070315030206 73
    0x20103058054920840310319250309064840d2581d55030102010400d441001031000d05000305000c42000800010301151080e090803204191034800c1d010002d8082814080428610340c004120720248036000f0745080b0f082c0405480b004504d00244100100840d501c0b0070200300041c1c004000d1454440410b041560350345404e0801e841d02844802d5095074500b40c1c4103000382243c0c90780860350070880890b80d158081000e8160111801040d1000a11a100016203801000040244102200d0083e20308116031503440c801c0c10744030854214201c032038030510718062002041034400981c20103050f00340c0040e070740c00c00c8040045e451040b51050305d883d80b01852280301c40d0030400820b006000001e0219091600d00380b8008030034011a903072111900680c490005441500604111907c800146548428403c03424400c2c01040d942009a0190180c840082150b50003130040c40c1c081e82c1c0c0715000f540b031030351620800c80c01083d0b1030400e4400d00184c04000400750382c419010b070402c4890346100740f80c158460 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 540337769 1250 540336519 540336523
    0x30b07050c030316091d100e0610231b0709110706090203010f110a030e0f070512101e05071107050d080d050406020304030f02162117090102 62
    0x410240810a0401441d40d41d04000b00030f603a000041091141d07094500720b101074920340300681200000350310b281c11117003e810000811501400b240700e0154166504c5d0811103255410484030380c0e0b0007035510000644c03118402c8509489690400141d810b0400c58601d0810b1264041c0c40e8016502c13048001003003043c1024082c520007003e140400300202d40c0d5501e0008624003c580c006420350745c0e80c40d0441c09540f4290070508041441100c00c0002c0c030f0f280101a262f64001203d603000003031a054007160390000c00240c1e114003844c48002400001e107490100580543c000e40500c6040c021040201004560341c080c081e481c00c4041c0301d40e140056000c50003812148020103403001c209400160107020000410018241c0318140c03913040024440b820b00a9042c880c0d6217100280c41d1406041105000003503000d140554465580d41840340c3d0100f00c100c1c0d1707414400821100d440103c20040140b500c1888502800d42c490994a64040c0c0c0d4649039901c20380c0843c0100c05e10301c080012003904540c2c0c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 540339019 1250 540337769 540337771
    0xc0601091b0809120c190309090c0302090d080f040801020f0315030a031d01021e060105031203010b03070e040e0307061b051c11040807060921050a0303110904060b04030b 75
    0x64a021a8980f50420140740c0c0c8000845a125260800090010316600c050000000351806050f0781040400300c1e190042040c040c5200c2c020416281c00e1902c643c05120307001315040401d00030b100e20130034040c503200c40003203521640c4603c206805c00c001c009401042800031b00414811140f006407645455010350929006844405100e500070300b00d100d0000750032910380d07806242c500b01000f0618400000603407405007000b810315800d102c4041940320304000003400c641070300c7c403d606031105c1e200380c803a2110850100303001c1e40508210030300c0001c45080c840c0b071440800520003040810f0400001c51400e095034414041510217540b140e0015042d24520f0303060030000d40141c54500d103440360030070043c2030303849041303801c3d8148613140ca581d00048207141095601500c030351401d480e68649d40306406407c1c40158862950b4410f011b0300420190340012002565103070304140035040078000d5981c110700605803000c551898170014481020551a00d01c188806044020692030341c450941c245802c000d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 540340269 1250 540339019 540339071
    0x80a05210603010614060a081b070819050a05121308032401020c06041a07020301060608180a030f0c061e06080f0307020d0b04050708061501030f0621080c060109 71
    0x803480c85c0c01016241c0c0d0701207a1043c0c0d814641182192120800990300010003140001c011a02090807001d1000c400020403180074000d50100d0895286001943d507806088241da02103001402000b48407043e8034500e41c4d10030b4094001d040c002d89250b44040c4190015151031030803040b4860010301403045120881c403a07420900092000c6c1d554100006e007a132107280291901c021100602c00303854002c0318203842500354010024071541d512884010702ca21000c40f030321199031040c81903c4030340e61300c0400c207a00c0c90354240d03071031100341c515056040e078484460702e000700c4045a50b024020450211300c0444800200d0741c00c4042001454050954a00710202400310f41c150002c0000b00c00582d034a02d43e428041c0d51240702d50b40313240d0300e0f070600785d080c07550701c1c0d022204c1801888104080c1c1b8903800c0e41d010101100740c81c1000300020f0544803000b1210980a01203a101050078003090341c1e01200c00200310103202c0c0c40040d1a0103076826589003014800e03400801e810b83c41c0c003000001c0314080149414501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 540341519 1250 540340269 540340289
    0x60b0403060f140a020c011b0f021b0604030303020a11070b0405011d060403020d0203030d06030b0f07080717090304030c0906170f0a0b10030b09060405010f1503080a052106030106 79
    0xc0f140386070780340d001406080c821030b0550014017064210700c00c0d0050b0740a00d408106607002c10b400c0310750150404000c2c1d2201e80050061800410300780901c039030a141c420310060000307400c045c250350b419002540b212259400b0f00a03104016242c121041040c407000d0911a008951075500e0b1030005007402d84d134515031088603900030800f28460b8552600f42c81c03c49404440c00c0c3c4600d0040d002003800d5108440203480c2c400d05048001c018001c000000a002d0041c0404c184450b9031000d40071151100300341c4100b80040ca80c0c0b202c19150001a4044e86c2d000b1f085601600e1a0070355035514118032090342e9002c000500d48440003004440c854991603100003a1a80c0a443c1c0b110000700c0042c1c03180d480c0c082c002c01310400030000c80c0002c80d22000400256600501014150410a046640e02c0400f141c048580790300b01042000700301841d00410700030200700510307140c02c2d038115a1b4041a580100302408200b240c280600b400841c80e403a034a07000c040c0710143c1c0c030406042c418145401d40b1482e4010107954 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 540342769 1250 540341519 540341531
    0x604050106080c01301e0b0a09090302030d0c09050d0b010f051c0b0a0b09071e09051008060409080316110d050a050d0617100e120427060b0403060f 65
    0x702c402c80d080340002000c900c100e4555172124000020003071840300410144880781c903148000a61607a0f10520360103100b240d4451130165a01c5c20002650440a0010010380090103840309074070355904520307100305d03142c00c141c105542c6070404140100100d010070340b010203401c0010481c0e074100440c040040c202c00c0c2d0301f00c161300e012144a540036a1207488020714011318840083d60021041e0f1080001d002c1c005c1104955007483e010007055401410400900301c51102c0520340344074050850001110800f4050001c0c0014429050715403000040c00c603a00540c6a0558100140c03d040042d0f2280c1c0030187e150300c0103046808020000102414071541c03d91002c10002d20f125000b605a0324012118902243e0b03d0b042003020f10060400c540c0881001c0b00381c0d0035511104200031130316040c840c3e100241003200908000300d180e0340701c1641583e6982c1c41c50400040c002d914034030303030404611001980310510f41c10102159a080b05c205900c40c0d44194001303e028010801c4500401c101d50032011818404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 540344019 1250 540342769 540342797
    0x260102030702100509030705032505030f180d0506180c0301090b07080c0301060e0904020f09042d0b04080c0304030b070f090e06010905041806020f090a050612160905030604050106080c01 82
    0x3d05d0ac10141540c0d000010f1110118210342501140e18546074002d00344c0317032101104421003005401100303115043c0890000a5079040c00d1041c0d00346090398201e0020030075912840c14140f1041c81403c1181079a020303041800182e030710300740a256001c500c074100000151821582c010102e201c05040344881c48070810040004d01d44c407101c071084800040764035a0f85500d4074070000394030030f800303180d26504a03e82104000030700505038000c010f04491140c0b403d65241d0308a00c10425400003d100820036981d030781c0850003141c0c0320405400340c20403180c01c0324603040d10303521134454244044518000056400780d505024940c0300715440001c2038101c0203260503040c200000381901040d400350300d0066030f0341c4040d81204c0148403031503081e0f030b41c0240045549a2210303c030a01030791301480c0418060b0b200b0044c006683c3c00c044007120380c845032050b012415074645070380d01047c0d10341c0680c500080000b03243c4045600d950034130419000c0c0d40701d0400090010314042e01c450604408498490600c1800200c4000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 540345269 1250 540344019 540344023
    0x3060506070b1b300a0b0901030b0a0b0a030c060f03020414090702030f0f22180b180a0b03060a0b0a1e0905010305070e0f060604260102030702100509030705 69
    0x40c00440307900c80c500b040a0441030200c000d005580381203501d0140000400201c20131480b070001415a100104001c0c1d5a03840342c10303002e9034260500d150300009610010030105002d88001604600f0f040404604d0300704040000b801c441c200d41040c2c07031056082008100c160781001c3c20030798440d00c03400d0035400c2914041c60380e80443c240b2028640103e0304030000412943c400e008030b910300208040703c29100d100031230101001d504039410306400e08841019080041c0b14843c0503004aa00d040101c103c0e5003c1011000003403e9440700b00303500059155125900b0b05903842805201d02c031540f40002c0d081c1c030020100340ca4410064000031540340382c100c5061113074481c61040e03c259489881c480440c10341c41800f1700d41301c080f10360005942915010010040250102c1e4200c111030092143e5240382d2111641c01312404010384955602031002c0004000070024000384e00304480c080c0040700d09503120222038909903441103070000016005104c0049800041c1e101e00d61300449600c0045080c03540c5580c90326 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 540346519 1250 540345269 540345271
    0x7060c0215100b0f1e0301060f111501060f02010221041115090103110d150302130b0307121406180d0203090306060402160804080706030b061306030f0b06071203060506070b 76
    0x743c074000c4c0015450f000f100703070401c560f0003a9081442c07a0ba600c1d0380d6401c00806071010010b205001076905425012076100004203040c00c1411015411140e9291100580341c807080350400b0000d55400340506120031000802003000d0403010141400f80d85000c2c03030410788080700345482600c00d0b40514a0f05011104010030303110520020300340080c00f2154600f49186c1405541c90f00c1d40075a00b400d44000c3d0507041500080d084a209996460742d0103503580c00381c0b017907aa00300e04650301588000b504205001c0a464242800c40c080c0d500300c0c0e0440c01021005081800c225012120203607922000074804604100d03038600303403406101450801015070b00203500e5601c068149841a600403440aa071010364902d01c5517240d078820245d60351642e841400c1a10343d08144149c90100380b40404036421410044121101094148a5540018180942900105811040c0e884069a520200c0b007140e290b83c402000d81d14019122441400ea10100007810b880c0aa00890702030380382445030000082e941040c071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 540347769 1250 540346519 540346537
    0x1c0506060118030609050a030806030a1e0303020f0c010506010e06210a0b120f06010509070c03141e070b06030c09041e1203020a0206010506130e06040207060c0215100b 74
    0xa12000424550940071800c10f03810180c2000d00c1c1110324410046e0020704005003920a8540100c1aa6a038042644070013450101801682855584807415a545c0a121544038802d040060602c4041040d002258210b040464550782d500c0d403e0140303a40c1c100d035541842c04001c48260b490403100c1a54580610280300d8005c2da0021103102150451485d03030004c81c001400504000d100c13410b03801c485a44c82034150901491b84c0298000810f0350f05001d60600d110300c0c0241c481c0c40c02412984d404681e049403621041003147d5050180c0c1080060001c0c074400003044c00c0c0781d4140c8488a5080580d03008402506180c4a80e001084018003911485040d60b0b225410488a144255509081ca0441205214000c0480058800b100c000b076426038041c00859800d5401c03141213a072140b06001c5a48141642a1000480d00000304000d08606a04036030000000d0005410000c8540c3c0d084242e0304084041c00158200102116030340c0256007050b6400900c8192b0004900c2c5007250200041c4140d01d25 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 540349019 1250 540347769 540347777
    0x140f100912020409050109050d09120c050d0c21170412030507050c060307030e1b0105181507060504031215050d08120103110a121211070b03151c05060601 68
    0x2801c01036695a50000c410315421200038040303007150b0b103089601e03594030b85290750104d6995400880c01c445441003200f080b80d070241c600c141c11414101000079406001000700c8600b82004400f041e500800350101540c0300200c0b021103215901032810008202e951802c0e1507600c2005c0c8400c00500e101c00c441d040e8880d40509103150b0318401c500784142003400300b08001c1d4001c480003080c000c40e194154003074528850824261004506891564038900782c01000050000e070051050b02c00c06030b503948101c40680703401804014199030908800e600c5410822040d2242c66540040106154122008115944090408010300c0303618001940480e0190b004d0305001d424800000010000031004498440c180c141109000303603034a00d020041404081c451038000d81200714000f5192150f9001400e0305640540d001401e0300190f80c00701e030054060500901688180c00000565896290046001d540784403005000c82c0381d68010321a6880c0e0034400ba441d55864040544045040803800c96003203102460 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 540350269 1250 540349019 540349049
    0x114070c0302070801020a0e04060b03040f0305090d0606080c030d1701060807091e300206070611070c05040b100f030b0103060b1b0706090302090c0903030d06140f1009 74
    0x1c040b442c2000303940101106610004031064490382100703c4500301441190705100964550f48a800a40400d0310000c10340718900d0080d00c0041c0c012000b07000c0c0305001030281000f0303900640350700064940aa00600c10354000100d201c1c654207046c040c0710780801d058109144030010400c0d800392003d10510624003001004004110700600c0740e850f82e00100100003010000842045144400c600741e4850010840101201d000440e22245002d01c86003048043c0e02d5414501c4c0d80030b00425a100590440341c0954030703d24440b0b103031b6800c400307030500c540911041c1c0041401c00e81400100c5a41064079441214000720003600c1301d500002e07000c080032940c580070501001c2400180c002e41455084080042c50215a0380c1009180c1000c941c05041c400086400042c0c2d900700c155061805400042e41101070480010440c1c0c0d41c8400804098101030122881c02c0c3c00300000000315051500480390030b28080240c6c0381545001c410030001c0b504100d4148428103541c080c05426100075204068442c10544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 540351519 1250 540350269 540350273
    0x220c030b04080405100203191b0321090305070c0801110d0f090819031b050a0c08160807050d1706010c02010c15061502010c050901350a0e0114070c 65
    0x4810f8030b000348001750103104000304000c80a906c035000352000980e400c4200801807a01e91149680b0940e00d030070b0303011400c03032031040b51812070302c0102c00c00e824140092000c00c500907070b00107441202c6200c0e0003580c4054480d21940b03003a0504802940c8081b41c0c1d42e05182101d4540c104520440d810700c421500c0c0090036402c0c9091240103482e440201911030140800c42c0c5002e00c00160001140b03100031380e82000646419440900140c0349a6145400128140804400f15000348140f03201d1600940c070181c1444c2040d41d0781440142c20110898101d4004105001009410800d0a00c800340c1030600e1980510141514040010000e040c603041000c00c0303c02006690203031004c2110b140d0013241c4004480c007071001e2040506024812803c0509959540f407001c0c1d4410311a01c503541d200380d540c0c40e140c84c0145004545190002015064114503220345202245c4c00c0f0b07120f510713800c10100201c04103117030070014802141c4181d480c03030354507074102217400c80c1002ca091107456000c0035504004005900134 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 540352769 1250 540351519 540351533
    0x60602250509040501091505090c15040306020c1015090e0d1e05090d05060f0f0412180b0c0d081e010b0a17040c051311030a09050c130203220c030b04 66
    0xa00e0000c0c0a4003411195003038843d482d6000227100ba9020022a00c0150905090040741c0362812015100e140062000740000317a02500101449a0000c040751a4050480800b4088072050242000101a0818104540c01c40c40c003c230b2070910070500103088807107032010015048038002c00c4000044110041d802c20f84502801c04c1d00d0b84500c028107000180e0a0b10300c4d0199403450192095003010550304002105403440320109841242d004021100c0c2c21206402520040110311300e00460703040384640402c41d04820005008120740841c01007040072180d040180a0b4400601b80600045141100103200010800344504503400d0004090303841d146070a0888032a80115644e45021711400203000900c03100600100950b2003c48024090304a100c9502044030a10340051009840901c00600c0108460748441c9216000300261880703002d08800050000e04041c1d00e00203000c0e400300030f00000440c0c3c10078440088801c02c149085110340c98941180c614920322004100e6001c0c0300c0010100000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 540354019 1250 540352769 540352781
    0x405060711040609020d060e15061605070b0319050f100509060612010b180f010804110a030209070207061d0102060126030708310510020708030d060602250509040501 73
    0x70355503017191142401182603000d01140d20818401032190703408140070000014501c040c841000f040b00e80341c10011030401c1c1c042c0310f044405455034000c00c080042d107203102c10000e501c20550f17869841840c03030340750250f0800c80b800985a100081d80e4801045140d041042c1c0c9030080e50f401720f07842417495407240c000819512626082a8454840d100001050722000c03001d400c0600b41418001040d4500c6800d000007001d000d002c55000507508808540030030000b4040c02c1961001400c020100782d00c030740101d495068103a0728800160701c0050200b110580c044a806001c600c200d9004845502d0100006e40e9408103000b02000703810b814502c502c155440441c594000d1645005894480c43d242c20b003051140c01114428071400c0110081c04c4003246a50061403082401200541f002400c000610800300d054a014405600c6410000314040c40b0400141c2040380da076400c046581d605084000742403071000c80c0305e400301c6415002020340c8100756094800544409880d0941c180e500d9040090151079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 540355269 1250 540354019 540354029
    0x1060608270307060204150503040819110d08070f0203030c0301061818050a06090203040203060a0b0103110d0b0a080a150207030309020402070309050f1527181b04050607110406 78
    0x840003e08904001c100d401074000c6651140d00702502900d000e00907a030510045030020b10203802000550010011603c02c519074010b9407920046440c003070249d161070000c05822440100384103c0812040550242c9070b40400c00c1544099810340c02c0c80903d6800c40c0c04180140000e1208141010f210305a0100341d0500404407803101741406403030348100000a05c026160910414144100458410014001c4900956000d4002c0c003040da140e01000f0002d0900d032007024101615601d03019034202681000c2c0100f02c40c2000001118250a0100001e10302140e1003114290000706200020900084800d9543c0b110035001503998a0980341c00c50040072541c0000b94854808250101411f45c01040c000aa54007550210f95012600d420080c881c03e04d0b003030149822030104060b8140c0c0d40c1444612119042c3c040b07500d48a00f56060000b42241d1840110004c40700040c001c001c0d05403114051201d80c85503030b8407114030300303807c1a01281252050f408081c4c00085c80c503040080b40c0d26180c0c00800282 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 540356519 1250 540355269 540355273
    0x2120f03150d060f14040201020d0f05091810120206070f080708070809040c11030d0b0d0501050c030a15030201140313150f0b1c02270c0a020f0106060827 68
    0x1030790034544070000b080307402e405151180c5400c054540e17482c0b681d80c05500a0350160014405a60803034800c96040c680c505481040040621400c0c0c1c4913103a8405c19410703070740c0048207910145003840403001c46051071707403040f20031081c240c610034056210304003120711440d00716260a407502943d04100c1d0301c40c4209480204404400204081031000e0440036012601040b40c0a100c02d02c100201101d01c082d03c11540000c0b90400c015410314000c842e80003001c07280000d011807810303028544500d821101c0031036a00122920020821450142d50710580030b400c1c107008096160541103400003044084110440c0700400c1c40000410310601d82c8188a0844a500c040c00c1c8004048442c624005460010091000d503414150005038900d8404030035010f1800c21003540f11003140503020004030300c0c0a10080820740c0c2c1800d200c07150b00c00c00003416902ca4802c4c000410f50311503650200030f140c442d00205440190745012818819158041d8406070064012130341e0140003940501e2071081d80c0100030445400d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 540357769 1250 540356519 540356539
    0x916110610030b0f01050109150915020a26070b04060b0409050d120203010e06010f0c06020304050304030c0e071409062107020105011e15031b0804110102120f0315 72
    0x1421005055100341d078415542c250068130b42d8800c00660000030300032203021902011080c0300c098203105100002c81110315020450030758030b46800450b2080f020007140180c001001c02d03000d0000906001c1c05540006903540002070803140780301544d02075880000d020380c2c01d5001050511200d50040c10080c44010710800120800d89001c0390b540042c91191004580210016240c1c401d680c42964101d481c0b6800c1050f0642c1d461004561459880811a0902c5641120a0040788040c400380d4410352050004681d030714110b0034290000c030425132215000804034030402c954164031422034814030100c0c24041380c072410220006141409400c140700d079114140302c7e00882c940d188180160003141d5a0f002000b0070b90701c40c241070f5500c050184101d15500f0030f0300c80420100705c0c8422402d41900141c40c00207035408900a03280d401c1401d034a0302c8000039050006203c18403400044441940303e00b40010500030000b100000340e24080c9029403251101c020001548040c5024940c0103c000e00920884070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 540359019 1250 540357769 540357781
    0xf0b060402270a080d0203071e05030304030201021c0e0309010e0a090c0201050f07030516050d060f14010908060106090e0c2512020a03050f0a090e191a09161106 71
    0x2485149825901c030f034200d800c0005201d60081150080b00f607283e805076103091005e0b1a602d03900c08020f640c003040c958820454801040041c0301170740c0541c0c865400942d0b142d0845240d448056510350f0900300c1545442c070390403d40f810000c11920080800e00707001c0004a000f0300011040410f40e80201030312070406440d007011a606610080c403840ea210320f0b21081c0d0311112400c8080380c008030343c4c010741d01d0440c060341120180200043c118001400383c0c00b0417450f0325a1601c015821039540a00921038685418107410360b000040c07400548603800082400e58540480101104083d1107840000700c1d00c0004160704040000468219000700005040c007211142c41e25509800680e1007a100e00e4131080130811960301c08540000801e400d42d0b2102d041c02c10300c00340184c29a01854900050000e054400210a40ca551742030788283d4ac1f02450b625116a150f0303000041da0006d0400709102a00c840c00045580d07124540c194119070512201803042c030445006965000050a02e0039507440b0f42401c06c84 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 540360269 1250 540359019 540359077
    0x1090e101a01081311150910082d01050d0f1407031b030c0501030e030d2d1e0b030a0b040b180a0b0f1003080403120e0307030f0b060402 60
    0x30751007a80c506540d59a0704500745100100a6401050010140c41c0b1030468038002d0009440200c3c00002c0c1e0f850034194100040d805d102604184001c40c1002c02004528a880f41c0b411f00700c0401d00518030038445210102c56a000c0d014000e42c1e1199643c1c1e00c844044c490356203803808038a41d00c10410603507884040d00240c0e841110380b10888003000302c240e01450900b588048841140d6110045a020310706100042d0098080078181e54094401032181c07880030300d214018000601006030a0fa4181c586503886140b51304004000101c0290801404001294103d203800394034460300c3c400080c0407102d1100080c200340c90701801030211000c02c01800240508079281c42d0007080318450311404894428441074561500c80030282401101c040091403014052043e254000f445c20024000c0b551203940c0c8210740e0300b01d900291441c071414042d070750340c2c550050605148003100720014048145190345400b5001601c42c0c00404100034000450201e46854040e11207640c00c80d0306101e0003800d0000c02c0a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 540361519 1250 540360269 540360311
    0x50601080c030d05160b1915031203090309050d0f0507060207362d050906061909020706020f0a0f030b06210c1224031501090e10 57
    0x251081c041c0c460503c080724015412140130058140d0300c0160f02d561a110505008030050035402242c520030b241c0c000b9040e491240f20b07030800d101110450240d0440c141041d0002100307110714241807400c42000301182c0c10601050855a00322a401c030b44c222030707103080c40209040d400c00408074070030300c54089a5160007040c0407064422210000403032a601001810551610100004020350400103541f1003401c15000f0710801c101010441c3c0380004038074110449001204800b807905561107050003c400018451550010411110840ea01e804000301500003016840380c5444958005018020040c040e0150750702a03000820b0a901c96680700c1010f005a090b0101f0301c00000d2400104c130217545004e90545540c040c3d4400010b983c0300c40a0100070304171102070110f0007000b4003848408485003004038100e1040d2040303800c0d040c440200c6a0705441c450446020076129411401034a0303600b0410f07101290469941000201d02501e01e48035030350800e102039801030b40b281d04000d060040b90b05400810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 540362769 1250 540361519 540361543
    0x510050f092e0602060603150a0506210102070209010909050c100e0a121a15060c0708030a1e08011a0306041b020d0e06040302240f13090605010f0f110a05060108 71
    0x51007455079080201900d9502302d00390f007034040030032501007468a0440e41c040f6500040c00707024a030205244408454010030441e802040507900062035004500b0450042030050042607010321000e6884d0b540d5685400703907101554021000b00445000c800e204040c3c1c0c811050b0040c02c600d000741d883e00c0d4900303003c015680d400d0740c204461009092603203500050403841190014160614144007000f009150f41c40f02400030340911038024045100272050000b0b2909541c15150744030f140c503803115009130740b020b101603040034025050010014903030318005245490898520f00d0340d07680d450100142c028400cd4012012511651241041098001440688001032a08c8180f000100711007001020b208a020081d00641d04601c40f200e40c1c80c0308000c050510000c0704610f81000c1510340076003015001030000100d00c2d0170301103082080140310322401e00503100070310b499160410044009130800640c903420000300503034008140c03c104414407607842550361190554010356551600c50355142c100c5545 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 540364019 1250 540362769 540362773
    0x60a031506031707020108011502031c15080307051506310612030c021002030906071a06060a05090f0f060c030706050601020613060e19030804060510050f092e0602 72
    0x2415038000c40d0f4020b991001e80c1c1656491711980c240351210030a2907094050340d042d44024085a000020071051003420022480400100040f120f200707800c40d11800ea00c040801c5d0005c200316004200c2c00b00d500f0356a81d006003410031f8180c4030100895505011540c40200703505001480c884540b41920940401c0741e81c91718184100c580710038403100403c00302c52004000c5031801e0070325001410b0558034814288514010340b410600e0f42c10100e02d00d944002e03022102c0c0443c10700c00c4102d00030540400c0c1d030012010344ac501e0409800d880702406510400600a100e01c660b0b205110095540202c02140b003880541450b844410008040740d0717903080086d0454106040c080007803095440040c1c0f00d031240703104100c42445190951664001011464404000e50040030740b91600c1d1301c0c21505114405209603102d280768549820034500f100c8000c2c0140c3d511080445040040c1d50328410b0248400c14101e461b035005803074464000c031710720a84031500084a41146214844c000c6080018402caa04c3e94003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 540365269 1250 540364019 540364043
    0x406050714040501050d0e01091707050106140d1b050301151a0304030c300c03120b0307090b0105040e0406020714030c0604060e190804060e0303090306070305060a03150603 76
    0x101824441c00b4a02070399001078001c0c071031152101c4070b0780c01c28204114108000100101646c580f20000b0902d5032203034188000000310001004424803030500205580c030100300180503003000042046a100901400d0006e4100e0f00d410f103040c0540b001e034002d00c4010000c000c030504070b100180910707042d881040844134031001e504666180d01d0085a21903945a520700b041207107140d4409240140c8407100303070213032031601c05441001035010208503000c0325142c941414100c5103150083c4008255004010b92908041644003280c40009280d0141ca26820000c14616010801200c003401a94018500142a20140024030166500809103a80510300100341d041c0302c129040e80d00d20030111001702e01e900907000540410074030303444038902851a205035000c1d260310301200d030314010012609443c0d221000030b08101c1c1a8024450048000c81a0003850802100c1c2c0b0000703494010052031802456214000240140c1d02c040401002d5039108103044003100c4407260410007000316000803030380714603418 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 540366519 1250 540365269 540365297
    0x210105241003090507030f050c1c030f23070c050f150904021c0203070206091b0d110102010b100f02161410030f1802030c040203071b0312020304060507 67
    0xd810085200d0240c086a0306601401080300248107041c403e544602603460040002400c141c0700a003d140120000d2980c600070004200b03000000c2c00448500d54041001300300000c0c0c002403600c1110105080c881085101d070003601091180e46d000b44500184001501420860000d0000c800c0e40d03c15544903140c50300075024061960034441c000e4125900500982e9003914298008004c03202020321101644211040104180c2c1c1090320540c0241c1c004a040142c4d028041208070100c0e24000e440a0011005c0070201e11409440c01f805020024a00303590801a4004d4025011040000d00120b16110b12142c00910280e251051900140640340c020600d201c6112a5003042d51901c02c1e01098606104003001500074051803070b01e0034180c490070340418160380740c892041214003101d1a0725500c0702c1d0780304050614002d910700a2040344184180020654000c1090380002403042070307808082c20604058621054400d007182404d80000200000c102094000c2800750000d911a44003030800e10b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 540367769 1250 540366519 540366571
    0x1112090d0516020301020403020a0603140c0a05070b0a0e16060809010603120e190906091103130b040f05070f05190510030c030b03030708040e0906040506070509210105 74
    0xc20401000a042800080580c482e4101c0b104007803440100010716003a9a41d01207101c448855200e800400d13519502503c481e0f004e83c1c40c0c0c5031b1203c2410716183c645492a400502180150b0074007824101c403034000900d9a44150744113400140300141142d507a1500e05e12584115640e0340541800910810003041c180302d41400303201e023602c1d802541d61201e00c0c80c0840480d00c0c0c61000c0402c0f0360210400c00c074092002103090b512005480b0800c0041401070410742c1e00025120001840c0c166810104200040010b21426145115911050240c81070311203080c000344e45100c0b0100a041c50190303610005040a02c0c0d1000340807558107856560b0b10040c40566030f07030b01c2c0c113a03442569000101c180c005061f9521036407002c2e906c092282000183c0c1c00113030012915580140c001241c1d0083c001a0921207425108102940200c0440c0200050301e0656070302500e618020f000303841402000700c0d02d090160f580d4241c10081000c0000000e00010400959501810060350032400c10102c0c1c2c955803e9954003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 540369019 1250 540367769 540367783
    0xe01170d02010b01020705101b0302071a030105090a020f0d050c0304060501080a051b060408160e132001030e030a0305010e0603011116030c0f0503030a053301090801111209 76
    0x105170060281c140c42e00c401d2002c3c80702100c03804000c101c00c1c00b81580c1e80c09440540f00d40b002e03000354010302c061403d0044100b80140744403420340c90046c06100421490b0340d11302c6d440b80d000300d03058030250f01d8040c4008040514040c1c4502030727202508240c100854598844040c0d48541c2c0900c1e014071041e680c0c1d9014589540340240043d00d6900104070190100074175808208441502070b044600c1c1c2559001c5290414001503000c030170180c0c45420400c0303040e4483d808260811a0708103140caa070441c1d41e45543c40178808400034000a64850b41d0b400c00d0368000c0e4010780c0c6507881101a00c0e40d80d402004028004c0c082402a00e0b104040e40001c11480d08051180180b00d0810344241c0e03184c114540400f035030010508508030304000b0300030f2440000600a104500150703125000440c0c0b81d04082c0703001000e48000030440089181c1040651010b682c200740e02c440010000203c21610541c3c0c840100c0d0000c9580d000300b0000c1d802e0080c80d40114030110700038a9480201c000004403521111005910f41c65 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 540370269 1250 540369019 540369041
    0xd0b1906020c011d030709230603070314070905040506070201050a02090f150d09140d0f0c020402070f0602031911030106090302120708010515100c200a0e01170d0201 73
    0x312440550034903501131a9144107007140241070048041800340000d02d40503140d08204170f090344440300c088038410300381c83c03086124218034500300903840c0080c0442d40d0381e8540d210241c000f44255810025002c2d0600c0040301524030384505005500c4c180c28070320354550781900c1c1000150300c0c107000606c80524074400e40d000e230070005008114048071001000918060029030480c0c1c2c2c40100400e014030324481c4100c10846219a419088a80c0c0d4441c40504007981460010180700f0b180c0300c1580b05035801040300001ca0350490700141c50b488241441d000310340418000520540c0300109212070f10950304c0d02a00072140000b0240501e80d000745203906540420b201e0100030511000e4244010710b026000d00c100c1c183e2800c2100c2d000c0380c2e0740440600750780c42034918071003c20180444d100107007890a1a0060040d550902e01580f600e240c2e50807090503140682403000350802c00000306156928003103200200310140c004000d5586503160788101001107000c100451084948200065006010b040d05c80d01d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 540371519 1250 540370269 540370273
    0x30e0310021908220512070c030b01080c010903081b0708100f1b0f020a050303070c15020712110c0a080303101e180e1501031b05330d0b190602 63
    0x2200130003136812505601c5000c0f0342c2c50103800464a045030940020b410914000c4845940641c594100700d01142d00c184c120344290380280720b440060b41d8200f40b24004407a4420103055540145004000c15691007024845080c01209000120045e000a00316081203d040302000508041c04144080f101c0900c0800501d828944543c40c040d405003038500340132003a40c0103903034034956182e03115800c55008481c50004038240b0341000042c000401580170705c100b400d0200f1440d2002e262a40500102032070010010081c2d00034184020303234002c0c00408003421001e080c1d41c1406841d1508181c81c2e4104541c0f485040c079102000141c94804008a03a1042407055450504039050440350310703844504031042601217845e14401c02c000d04c82080010880b43c00000c44e142c2a50562400103101e15a00e19810b00321400000c092250780d0310680c0c84412036021803441443d003804c51040b0000c100c4403070402e0241c007801203a51081c8016a40040032007500480342d03024490003050404a54030440d001e40c030016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 540372769 1250 540371519 540371551
    0x6170d0207050f03150a09060b04050f0f07050c070305010e210a1d0a030b04030f021c080a0609060b040315050c0d0f09080f0a030605120c0d030e0310021908 69
    0x1410400b8000f1076140026094504040c803100d0030102c0c2c282c0c241c6540701810b584082d44c106004e01481900101002100d050196090180043d01c0c0c095020380188140580100442c128501a10469110030f00240c20783d44690394030305045008200c041c416500314000c1008031a541000c6c0c908111230412181c0d04a41400090301c000c45200010141c10001c40415000c191310903a1004001c0300114820141000e6038509841d006252203009900d900940d480b1544101c024449041007400a81180c544000e095640d00da0074400f81c00c3c0c0381d024040040c81d009002c680010140000c009a0740183d41c10704814001c00c11110440307130200c600406179141400080444600398214030031a6030b4402000ca409185519200d10a50119000003c0000c0000c0c0038401142c241c01000000c1c94100e03542c600ca08400a20395072640741c00c0c10041d11400342e010410013050700502031000044d6010b8112006901c14601440080d40040d1a5031840c1485d191004411840340345502c0c0709445805561041c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 540374019 1250 540372769 540372779
    0x60d03050a050c03040e0108010b010c120309150e24010311010305060d021306050a0801020f031807030f0c050a0e240a0317041a0301030b0c09120d020106170d0207 72
    0x125410008401c41004410040180306040410140001d00103070062022154074000300755003191b900e4543e6070b0602111401c45c201061020442088812460070042001c0c0f08a180c9a528411080200311940b031401030b101500c400001041107400c40344250814031180c0e100400702c03602409100092403101c41360304000955200ea002141c10900280103a81e880300c0070360004081550640e00040c50700d540f101c0401c090700d40302c0b40b90002481c425000b14509484040381e0107440c4002001ca1201d8a80c07200554903100301000032000840d00260000524031807840c1c11546d00c00c3d28454588a482262408148074100761581406900440000444c40070300084031010541100d04003540004030081c000049496907a5140c0c5840e41340d11100e641d103003000552461016140f4400e0f440100030300c010710014054802164211072180009521480040005581c49d0b030b10007454403c0c5c0c003d03010500303081601500b1410070703102c1c21005508500c0342000256a9561058000001a0300154040103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 540375269 1250 540374019 540374027
    0xb0c0a020d0815011b0b0a0e06130803060904021203070c050906060a0f0c050304210c0b07050d120b10030c021c050702090a02091002030a08010b03070c0809030109060515090609060d03 81
    0x101000310040320100034141e68075114412541147d16070303a0b89480300d070704407074140c81409003030f52100d200910010328a449858822960000500d41406000d106002c2025235454000c1d25902500d4401240d40c0d801180c81e05405070040392150500030703829440410700070300d400c006031881007038150b5410712210100202241c01210103103098503140000c2001203418407031a80c018000303100f0550500700000d0145441324011040b41d0049a000700d040c40640c000440110318100101c25920786850b024048450b010002e0229070710080c2d0021440d982190050f40503048640d60310708507000c1d40c1d55014410519900403603102c10900000d941001010018a81101c15580107100800d0040c2070140b10f101203801581580f803007902591000c100e510295030b002c20980d0142c88072131205070942c28000005040d03080b0b109002000d0081c04200480c0c203031030941c0110740840c1c01480a01982c103094031b0680100011041c0e80f8082c42003c000100641041154180282006404050f204100e80c030211 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 540376519 1250 540375269 540375287
    0x90f040609020f21102a020c040f090201032009041a150301030c060f0806060a120501030b01050436020a12060c0e040b010e060a020a0b0c0a020d081501 67
    0x243d0000c2850318100490301d400b1441e80c0c0c8251808059103004201c01c840500e00b4000c01e48507a12142000c1100307040c11a401641107100103c510f80d900e80d4500c0c0c02c0140d0800045102940e000780c5005143c3c1d0403002240c0001218038002e0f00c00f0001e0b4000c003145040608415010300303564800c00c010000050a0a51202e1404006034804100341c000110009880380003500e1000d869000c0800140140424aa0060018602800e000c0003258003414080c080540082205200d80c0b000301d4181c0d0b8460182d02942405011128104819070b12840c1c400780002d03083c0285405039290000c441281003d8400d01039040141009070b0400d5600d0007001086400c80400481e001440f1103800a800a04080ea60307451520550011841c1444044010080400313042640e104500307003001325005907004401e10940c503500f5613207142e03604507089080c1e1030120002001840c05a9000400c0300710300024020701030649003a402d40e8141034800c402140c1418054030341d5844061669488000c0e0b41c0544240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 540377769 1250 540376519 540376523
    0x10e010b010e010e1f0e060f04030302010e060403140a0903050331140d050712030206060f04060506121f03050309041107080f0309011e02030717070f081b0a120b090f040609 76
    0x1c0c6c0d801c200c001c0406c90b603410250400d00318a402281c180b0800d0740a01a140700e9180003801058a49030a84004140d03500700c000b6419180c90000d103919460b031156148801840c0c115080740e50303641c1c0c0401480109041c2150090b00301c0d0717101c4042c1010105800d41001195440110301a280255a040200800c40c81c1070888040c441c2084c001031503200310050a80d160f000e0307006089140340403024440344132181d4801134030a62070120280003580e101402d541001c00340c410201d2490b5a104c501034031980010000344d0707a140d6144400420000f0000041c8032144080d0b40034000c2030783c000e14050040c042e00000401e00c00302404034121200101010390b0344050403a00100e40c04c4049420841a1803042c1556401280c00008001c09107421440341c0480300c0509245c0300c002d1510150042034820089812001c00901501040e01e0310741c84030f40d007248900e0b420201590780814180c0070701300b9040100013200a80c14244000120718024450900c200d00d0645002081e5032203a980c04010300d443c0c070342 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 540379019 1250 540377769 540377777
    0x11060108032703010606050a1202040506040e04050a1e02030f03030c0306120a150603061b0f0507110a06020f07060302130b07080d060b03090c040e030a030c11010e010b010e010e1f 79
    0x6080b580d640034014000200407544a580e41e90b0030020000b46181e4038220300325a2103004010411490b25218219011901d01e46e034241015115450641d040841d402409042550b01100e60015800c00e41400c2d81c0c1c0074400c0381210340030f1030394000064030fa000840791054500c4060000800d80d080054080d0401c2007c3d0042d80c9400390a44d0b1a00c1404450308400c070030703046d60740344140100544c3e0b205024000383d2030f54904034031181a0000070000011034298004000c1c003c11107108008440c895035844e24402416078050036110a0020355074820010400c010381314006c030000e0014001d02c21241c44118501c403048000781044151030301da80c40b00c0360480328a2010003144000c00c0d04e521034613010300390f12407001d0303580d0506c00041440c1100800c00248a80d00d4128140d10100c4004101e5486031904d040201da00a401202602c046907e50140d00540d400e10b841c01100790b03010340c0301d80d0208001340c03a4102e42424020044540d06400421143c00402c81c40015a0346150003c803510050241e00d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 540380269 1250 540379019 540379087
    0xd110f011103040e0a11120105040b1c06020c0d0c050a020618090a0f050604140f06041d0d03060609030320010b03370b070302092e1106010803 63
    0x507103a2441c1d00551100071160840b00510006507850b01402c100c10219a002606140d0080c607a0710301d07001c043c840c1c207201e6991040303108903d8039196441c0c0c49160890f0380d51403407181c1508203c1b0107035000c0d11217080c203030088084a4084034042c18480c0b420310340080042000451607400e125499002c1c0c14105c4440003e41380151040c1e42c3c40603103d1203101000c3d030100e04110081c080300c040c3e81010304040c1c42582072900f80d400f81c1465202c01640048030308804099074403004e01140043c81070008a000385110060003035021303400041c4102002c000ca607001c11070a5921101120b010480c0c1c00020000303004006086070000f10800c0036546d000311341700000b44d040b00341c07800280b4065410008051441c170082c2407501c0d001255080500301c415411406a01c031004d66501c0500580c000c110000381070b07011881501c60744501ca01c002e03600c00704002c0074142d12043d010409001001c8607007032001902481508885000102c2c1481c102d034842d074011400d1241c182411104408940b403c1d5a4401240b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 540381519 1250 540380269 540380297
    0x140f0405090408090109080d022805010c17011211042c15090106030f080a0c060908312709080a0801090c09141c05070501020c0d110f01 60
    0x446594042e0748201c140f42d565000010002d400c00369182e000111513089841d10040e26600440c040e00c903684400c0501401c0d0600c0d50040107803112202c4098215031820910611230b6406c448804480c0c0b043e00301c42015681d803854103503090690fa0600a0040311140d04080c501d0a26411040315201030b02030884441c0d01d0810440103500540f0220742d5103920032102642d18100d0100c99503044580d0300c0c024000703141140c481401303500114078000c001b500c00003210701040f4403d1507001314455000300300b40f0000155041031180d80d0888041910500407000c40c40404101841204000203a8800d080b100c0501d040c80150015842c5d46510001c0301812051741d0b40c0030302c0c40c0f103000540c2d8401c290094603503007418001010f106058000c80192803820301c0c11103806402a01040440d584a0100480e440d400c50100e0301209001c403260140803200f5001204000d00403500e04203460003a400c481107881d02c10104041c1e040f903c80060110b044a900500d902e00780300c12500301a00d03040c101180c0d04541c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 540382769 1250 540381519 540381529
    0x91e0a030f1d0315071101060b1b07090e070906050103052401090905041202010507020a0506150a03050a1a1f03110f100804030813150b0a0f0e1015140f0405 69
    0xc00003130f0f118012a000700205a03400c44d500c1c07100307290310303030000c11180d42841c0800240f0300c10940300c0c4c450f0b200e07010000003056208000d582c02824069070103101841c00c46a0107640d50b405400341c142d145040c00400700340c0f5407281c03160034452485100071080803204141c520400c03401c440c0a850401c0010300c0c010911300b451b801194040c03031180b10140c4103419095002400c4900c0a0190350464025000e042d000c1a000100c42d40c0140b980d0107602c1c0204000c500041101c4450341c0010b200d40200300c21002404528004a516041c443d010500c6c5542e0340e000d682c0385a1280564074580140c005401d2022644400790030301c0042c0c000d018242a1847c500000d49008000c07040c0c20001800311003040201a84510a0351f04048150b8071403008201c0c640d509410341490486030203e01c0c0c1d540b406480c15503503c80900e4010107503d100c0321085a1141c841c00a0503030b0031038a0f00d8800c0f68a403000190009190301e510341c140000d980741c0c0044901d55050114076401000100c1110328140300200d82e990f25 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 540384019 1250 540382769 540382783
    0x30c080403030b040e07030321060b0a180302090f04060b0105040609060507020303040e0c0d0f02031e1e07020d0905150702060d061e080c09060307060c1a091e0a030f1d03 75
    0x207a20303145400c9002e01c40200c1061030010142761441d0511104200d003409410a482c08041d45080c40501141c280d020707240d60310116030020f54881d0645c4103020308050003c800d40c1c00389000b88002d000b4104070400645044c0319038460440000e40e51841000314511510107443d0451004050303074505030340e0b001d0f400c240c03940036aa0074024036000944d100180d90380b4400c01c1c007001404102903046142c8a402c0308036200d0360030354156560215000192007101103a108001c1031018144041003418a40f200a645004c0d61090304013240041a000c1580d2911001c2d41c140318000d1403d503031030507840c0e41c07e2008580100618007c800d84036540800c00030000110178101c4038071240c0081c08140f81810003480c0000011009000c0c074000c40600c00242c6010640d02c060b1019420722a50044452502074a0209071042c13055414000701c00b80900d400e80030801420042d840d0801046040d100443d5a42301c900000004020078598642415082e0107117061411080d1002d40340814017040380086410000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 540385269 1250 540384019 540384023
    0x17090c190e042d030504030602030901020d05040813050d171e0a030b0a0905040b0103021e031501140102030309061b070b04230714151e0301090507030c080403030b040e0703 76
    0x25035103043c4815100e204812122400140c9071515103449514007a01d24461030101034400c40d00080000c2581c40f094044940d14903040341c0820540c503207400c0103801c80c1c2150803d44000b82c0d01c800001aa4a4035460401111b0741001c01b45202d507a23909180180f5910400c0304060780c18101c0d80901540c921100500a02c00317854034045440b1204108000e8448020342041c60000d24140c24003010075550f030714040c150fa5040e030310300e03011f403030a0f02a88100c1d07500480c1c3c0341c2c1d15200f41d01040d6540010f00c40e209040301c046041d0340c41c01a4000c4010380c0ca038007003110802140d40c4204000f07010f05600c1440c2a0800e40c2140d03615180c08411b40b01c004495604450556121001c1c0400460040380ea892410032486007401500c40a8101082822510000720188e0b1140e003060300511340f210901d10460ba000c00c0310801c9504000144c50b401e21642d0005d10560043c030340350500007034885009026040010707000c0e5844440aa46554059004012040c500d0741c0141c1e032441920140c500c03c10104020354 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 540386519 1250 540385269 540385283
    0x302160b0c07050406150c03020c0a0f030c080307033f020c061f03030e040b0612040308100312080a0e03030720030c0304060503040602070506010e0717090c190e04 72
    0x20a5950700145007203255400305028614001c010030982100e055000d003466202c0c9000c0042c04c081c3d08013280b034042d54451b2290f0002c441d5600190451040481c0300440c0c0c403481000304855500e0051540707a000d0b520000e00402c01540b01051940d403000702c1d0702c500540184005e41c200c500c0200e10200e0b2500040c407a0704003070b4000f8010781c9209003007042c00d074815045084d1022081e8000b507240d000e602c8030f22006027400010380150b801641d980d000010020700240c401c0f500c8001c0013020700243d1f0010b48060b00810b094101207828481140851000d03250031180007001c0e040800b00407602c500c001820700007400c2d5110400c00000d00148000c501801d00c0f030341d50030101c840501e0402817040003001c405416600410900241e1600482600c0455415062460300c03940c1c1da0400001a1007030740c4000340f09016000021074400c1e1040f1005026102030740c0c49458409900164002040301550b5214480e48940c404440d12f142800700000b05441900000d01c40a9860501d006180400d5a00312142 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 540387769 1250 540386519 540386527
    0xf010e0426030103031b051f1b17070305060904030e031009030207210b0621010606020d0801140904110f040501120308070906050706020d060b07030816050f03060d0302160b 76
    0x8194894400410302e2444001d10441d240d481d50b1750b44c0d990480c2d02000c423050340391034110420f846496100189144075041c44a0341800b5120f001000c2c440c0040050a4140c00000851070140c402d2182502c03030100903001d0106074856840076643d00000c1c0b00013940c18441c0707481c6200381c1c4456005d0110381920940040505900301610500200800807402228051429203030000c00d44c2c0002050b08403000b5100c7c0c80c0c000302003a608203803000d0600c01c040310641c20120b0002e4045d82c00201c078807030340e0160365445501c0e0b600c1c1c16205d6003000002d0003003544007032158041004034002114612410700001c01c0850302d062500085004c3d43e609900110040c5292141e503c140340d00045800c1d8406c61900d8408400d60402c440a41140100c03500a03041c2c8c0d601040240d242d0a15a200c03030040c3c50240f00032620342c192483c0003800b52204030351000c007560459140d01c0515008000f07a601c80ca401c0109d190640d0717202014072000804c444810390031441503408030405410900b444902130301c0d0f0b0903403040daa = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 540389019 1250 540387769 540387773
    0x6030f06170d09150206130302070f030c06080a020415030515100905040b09070801060503091f0b0a0b0901050901180f03050307120804030804032007080c0103050f0f010e0426030103 80
    0x110b030f036403030380f00d048411048903043c40a039a010801c0e0768404125101072264460900781240303442055000300d114404210004424000c0f0103078482c0c11aa01903849210179958200100306a000324481d1407640c0991516031f1000a00940009030720ac0c00d00c1c5890000311000e000028601414440790502280c0d4000b428890b42c28503004804202c0c20560b01d6000c1c50a1124009101440510401b01080b2000c00840d007400e40070700121704c1c03001d0310704c0c200860660420b0900c00149a9200424401c107210a8005254608042510300d03201c8161120b07801d00140b42c00540c0c078030200c00071284040c500701c1d03404508284d000c0b40410181d40200c0003180c50750110310705600e40304d004000d5441440101e90030040029400044250301030303418035052203a00b4441406480e001d0344d0403c102030754046c020020840c1400000c60441c1c0d41001d0b6402c0c40780c1e48480216510801094500101e03400f40400180228894000c0058001d4452072800e00980c0004010904c461059030001c141c0d100d000004000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 540390269 1250 540389019 540389027
    0x708150c0a03112d0c0616020c0301050103200a0825050d121101021e0705100507270503030403060b03101e0b0306090a02041d0f070317040f06030f06170d 68
    0x8004152822005d1400c2031002403a03588071001002c40120700c901501910060b8424429003030104005402403245507102d28280d0b12040343c1824006214440460f8950117260800c00d10048400403006440c2c40350b24000c484013804400030458201058840000440c3d80b200c82004003541d02451099400b0905680028400d038018582d100c0c0503070042c0183c400045200d00d042c0078070407e65210300e6452039580350441c00d00300711611104000d8600010040c00c1034104200c04c5441d040444c444500d020981e15440b801d18840c0109a00f60f40280000d10002d806940141814200102215030740001e1101c9003056480300700d24024803018007031599010450500404002001c02c40c0074054914001410580c0c07504c0b5554042d201d070380c80710b40c006034540b00340f03c914a01d05105400d440c0785440003041c10755030300024402210f500c032488440045c6c2007185019502903480411000049500e0401c04401501c0c6c42c0003100d075445e942d040e00040104203c10308882c0e0316210b01c041e110f2807282d014090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 540391519 1250 540390269 540390337
    0x1c0b03031b1b22051302040c2003070b0c1b120c1e0604030c080f0c0a0c090504020d030305100b07050c0901060e06120a06091103090708150c0a0311 65
    0x38051000f40e2403035029080724088a641d080c091243c0041c440c0c0d200c3c0c0c54209141940d40002e9080385ca0031403050003c2d81d0000d0401ca0003003000222a90383c20001000c00d45d030b4803c10760050010390301480403501c08140c1324018004854290444240700c0c40c040441c5040c00c4000c4400c20300c0080004865180000500c43c042103402610060111042c40719429510341600610040403c04402c4461003003000f501c061b42c4086100783c6085c3c2e150484421b101d6a60220754100b43c541091850b030000710348946010352803203150301030510504400180e4044d005000e0103407915900380e01006000c03518075100340207801014000c000a00350940ca0304140704100406030040740801801040b04c0c801a00d81d10300f19500c03407541d8a01d107402561405100c500810564000d40d40d440c1c06c0446003148401d65001450040c0031420070f03560401e503100c140d5541c9280c22101c40103107840d900e00280340c5010440140240c92490f0501007a00c5801c9041140b10743d020540d40710150030240341000c8004c60301580c070703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 540392769 1250 540391519 540391573
    0x61d01080102030f010b090415090b0405010503060402010f0c0c0812090405090706050a050c07080a060504140a0515060f03100507110316080c160b1801051c0b03031b 73
    0x2c51841c107007500040300c8008140112081081d00242d02011a102c99010b00030303820a19110202c01034407100d210002e400800816442141000000b140ea8a4046000b9004039816140d00010350107516040d0341c04440e04205454001e4200e80001e02060203000c0b00700803038003101c851942c699503a01048200d440142c00c0c0c50030790b80684424008180c10208550b09800c850030080d46401c15442c1c485e141c54216000501d403401204039000400540d50000c50181e0322a401d603a44518074060b02e6541c5001c003070006805541700c0f161000721107540c01c90b000e41288000d03101a85200710180481e2070000c034032003000c0b10f06542d0020846c1d8164031203184911001ca0401640c540002c0c1c0c600c0d000c0b0300b01e201c0e4001c1d2400c80c0000b020a102d4400300550100c1c2c00d002100c3c1d414866444510b0f4400740c01020303220b0303048861141c207003080c2d620510407203400411000076104071808a400c490b004048006540b50144010000ca400700000c04600c651850269001082170f80d01c9500720020600769200a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 540394019 1250 540392769 540392771
    0x7150902010c020f04091b1d0c040905100909150c0f02150a14011202041a0603130213021b0d080709091104170c0102150112060e010b0301061d010801 66
    0x14000142c0c1e100d11240001d50701210604805000100054001e001252000700040b032403005442e00b581c1d06a02e00b90880340206c00c01e844040550300030000c80c0d10119040c54080d04204014030059000d60b00580c0c0042c0b0071004000301c2c94995200d807007299500705044c0d59004882e0154004080300d8021005c00b8801490b100d203030f80700c0d400406950760480f00000c952b001101c04c0050b144003600e07403000340d0a80d010b8000900650b590480d80c0b051100a050603400745007890042c262500d08581c040182041c05080e10b86140d5a0700c0e203d000903e2a10001c0380d2200408030760b501c82100c030b40051314030840004004e11000351940c1e41710740f0703081036098a5400e101c4054100401c0642001e00401103d9440401086400c9201d1032000d0034807441d0011070704450101c1e60710340d029500080301292030310282c0803104050a03c03180002208400d104009140a40e60300420002d651074018050700480030740003040c071581803000a07080d98416004028000c04210110540804210515005002643c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 540395269 1250 540394019 540394031
    0x3070b0a0e03070803041509140d030b0f040906090c0f0512010902091f12031e03050c0a120902090c0c19122703060605030d0504300503030405030715 66
    0x1801c40e48070300400402820709000400040e003400001000340c0030b01400038504211301c4810b40b9160584410031852034589100320740b4800d500368020301c0355884d8450002c0800c40c0c40d0550804020140c101c1da0402c0710143c1c1c032820a800020341000207400070708001807080c04250309140c01c0c07001410a20340c014095a050880000160712890502900210300e07a4078142041e1100704034401c1e640103948080c1d0f01e5010340a001081c5940514010703044410070400c66500e2030046412015230323000792a0480314000400280d100e090141442022080d0f803840041981c090300d40000d03030701500403554050760610011300b4055601051201e600780210640035030b054400341d0b844007071001c4100c401010600104250300c60401a4005c03001028444500c801084952207180940103070040b4442c15000303110786600e00d200785004400b65000d548401410142c40080b07031042110181014104400000e4a5200f01c0c02103071050009500c1580501d00035903452041d45010300d6050040d030514005603103441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 540396519 1250 540395269 540395291
    0x6021b090403050309072102090603150115031104081605060a0509060708071e03080c04080a06051f090e07061115181e06161704030302040b0a0203070b0a 68
    0x114005800c00c2d014900180c42c1ea881000c150b20f0700541d5044060380810983c81d6460980c1c0b0290000343c064400e48545882d5102d607030030700d603603400940c06070916a43c5002c0140700c103580d400c400e810440c1d140e282c080b032065140480394440ba4443c1d0081c00044d00403105440d40880c1204204009100a50b50b1602d0100e8a26000380742d8080d14240741d100e200009049400e0022801c1542c12a51300104040c42580351b06052000d9801d81c9002180804c040c0d80004488440c40000e1750221901400600303920145580c69000400004001d014080d0411481046000c1c059000001620218030005145418088045e203001a9a03100300100800000d80001c401401705a0720012180300c00d00041d10345070781c100040d071404204d407107513000c1c425410100442083c80540507081c1844500703441c040e484a080008040e04001150700115503403205e039100c0c0340ea0880c601c6d64020f004c2c0c500107050580300c1e0401951640641812001a803010841909000081c50201d8100300104020001313807820b5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 540397769 1250 540396519 540396529
    0x3050c0907050a0203040b0c0109151a0114070605060406171f021306030e0a06020f0424020607140706091218080c06180316180b09040f02031507030606021b 69
    0x150281ca5105440070602303110b0380d0070940081404541c0503903014403014820f0405401403580d9a10407075041145400c0e01d03003039400b030440b41c11080400403009207040038948a95000e000040c00081e00305035600d000141c100350a13106c030b02c407080c0003202070824140c0f8a100e25040420856010160380d2040240c412551441d001c4001201c48500b4082012440d4000349030920f11181c0d0044c044900004407601c0c81641e1400420940300f030428508200342500040503c1c00b081020100090b90122011600c03071401041c00440c501144008245010300d540d0350307941540c40c400c00c12140b412181138128038180c0c000d844020144141c80d003900d101c4e40340c40e40c419a01d84c0e02c001c8003400784000050404810802c04500d81806c03401070100c401c840c01c0d005052034050964850703214010b00d00d0103008140c800d6400340c6003202c040104220079a44980d03c507075030209241001241d01d0f10407154010340d409400c600d02445010691000103007146486006810090444413030b0841400300a002d03034440e50f41d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 540399019 1250 540397769 540397777
    0x30a020a030633120624061101180b09030c150f0606120106030e070f08071511100f090b0a06030b013003030e1b0a0e01080a0b06010e040603050c0907050a0203 70
    0x628804804d60f20b40d080000c02000c400b0b0384075585d4800202c403001180c40c81307800300301107030401d95032400300c0604003074050308030780c5002c0c011800c210181403040d021550101003e500000780710b0a9918000e58540b20519082e82c1c01d049038a51240786040007141500c0c3c1b030383c07a94040010b4800e40c2c03401500c02003208400c0c40c1400340f00281640c480c50502c050504100c0080904030710510052001d403501552565210f540c0306000586c00801c03c6a075080d0303c111801c054039442c450050118a0901e8101d002408030004152030280e0340702c1b81c95020505071140a4050b41014a00041301d0b411810003e8400005800c80c02035000da226600c00d031003003402d4000401101c1c80044082c11001c61504070080d00c882c81c185151886904001c0303680510804a0380340344c0d0400c841034060a81d071442c10603da140e00b403064944039041047d40c44040355200c0707103250740240145003420040783e42c2c1e400201240c109030010385080c0d10021307042da01c0c1d05100b00c01c0b54210002c7d0030118107100780360340020b41e41c2c82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 540400269 1250 540399019 540399029
    0x60c0421290406050a180609110a0314011b0909051f0e150d03080703090309050a1401020111070f1202030d060902030702160e0106030b030a020a030633 67
    0x80100d040148949100ca0750120210300000400207901c5462019150a0544060b80e88900e0704010a4165a030b85c0b00301c1d00ca1005e9501101c5032002c41da11020b004012200003075403400e40340b140b245801e07901c651494024602c643c031122806640344507690b085079000203040340c40303400341c00d50400d91641111425040314000440807030203540d080641104002175081082d540c40204c80f002c00e00742d4000084910074840c005070340290210140411410801c0c144010f03004ca07410001090f0300500c44e0300017007009802401d000000544d11400701d00703003c00c150f00010304060a010b00b803603190303828020040b0308202c0360a000d003822502c1e01d4007038003014912802408100c140305000c0c8035900a10984000e00c0300401d041001c1c0395100c40038030180d401161076000600521b41340f02148804401003c054800c000c08402d0030f80e0030410250010310841100580c076103d40413407040165107481d11040076512488000c1030041a2003038540340d1a20701034209010785501410a42819203502e100c40c1114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 540401519 1250 540400269 540400319
    0xf0e1e2415040b0a090e0705040501021b01210e0f01050901061a0d0506010c0503030709050a1d0a110f0c0c040524010507060b042a050a050d0c02120409050108060c04 73
    0x80f45008003500c17241420f51020114114140402181c144c0100140c41203440c2038080e203124000e1481c0c0307141401610707a0060f011400b50244140e80f5a2040611a4040920b18001070080c00180040e894451100b04c950f40c169102c0e0100029000d0038001d040081c0a0200460383c28454408240f00500454520212207956a03000070b8090784100d81300000c05400005496403820401002450000c0c980a4203010340410078001130f001d4080040f94014110032083c1c6002a25100d1010307001d030044c0c402c0035a420000303010001002c45844010203191012000401c82d2204150510042d100010301c0110400368030182c8001c00c0d0010460144164401d29010f40c1d14161031400b8001808607112090308a881d00a0300404c105240c101c03101b074010079411601408201420031a034501c2121882000103000384a4500015090b42042d03042611900540e417106080403a01302c8070741c00c1544103500950715000108090070081c000c50ba0400081400d0516003414008503030111304400c42281d50507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 540402769 1250 540401519 540401527
    0x1090302090703150305030301031a041112030c030c01020408100903050703142b0510060c03050903120c03030a060906030305091215240a0f0e1e2415040b 68
    0x1c0d512a034055401c4c00900920041c1150722420042d0f500c0d0000d0004a88040c0355800d040001642d60610798825540041c030b030302c00108450184881241059100d40151200b0701516503c100148094800c0020080005840b83e00c3d00c00207500d868104945a00040c2c646640d0501180d03001007259111a01410702125400400610f0402441407000d96240194040c080720742d007c0c154403004a28046601d8140101e4a0700724002412080601c24100441d0107904064000b03030080c000b5003007041b0014241c0703013403400718000d0b4100350f400344410042681000080041c807100f07503c41c490180c101c41a0030030149065030740151582c4a0400c4032403050080007011700000000700041548003103011407007451410103501c403641202101182442210b0184c625850504000042c007003114400300e041807140d4604411500c00a0000d070040900e14030704902c45481584e03061586000c2c1018110340040510f11b52901c1100c0070700d05094038401c5400b06220100c0b4902c04080c0e07010f8616a00300141d403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 540404019 1250 540402769 540402781
    0x20306070f050d0c090603050a0b0a120f02090414060907030b070507020418030210140c070602160b0108150f1b1605010f0603021207060203160218040624050109030209 74
    0x420b010b9443d03907002083c10300100d9620b195002c0100d40071603003e030f18180301c19100c000401c0d00740d503002880503810a4007410f0401030703000003a201d44035090140030080801c1005802013000302c00304941c00d0f14451a140c0c42340305c1c490020030525034014080300203803001c2402c65441c02c80702c80e00a003042c420044085000c2c0305644d40d9034414074440b09000414044013841d4900030352103440c41004440341619100f0350b006134251042ca60742c400c5495510300b40c82c24010760f41e014020f4102c1c540d4600c01401d0404071000107100f01d001c00c3c0c06040c980d0000d00d888030001c51041c900c1c0c0f10080107920000d48041c1070008503408041030840b4a1101e0240a8503a1201340460700b0300c0f201c41380060090340c00c1c10410852a02d2036030044054078021341d541c030252441002d500e03030786d5511807040c500141d01c20095103100c409a49040341c47c8901c010031121240190544401c28100203071815a0000c2e0349070300b084600c5114a4a41658091808400400078a172100191854046100c0a40280724881c0040c00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 540405269 1250 540404019 540404027
    0x1f03110712020f1645060605040317070602040f030b0a11160b0a110a1d03070602060a05100905240f060d0911030106032006030c0708073318020306070f 67
    0x2259192000e03a4040c1c9036208a00d13104003040340c0300c170408668940b890108000307101d01c0448060f650001c1c2a0109070354650311020443c0d00c600401d40704c0c168240004500181c0c4401d140000358065000c081d40da003040d0224000b01c0701c003150b4240c1c03c2e840800251480900c140a9a4011b64100328000596680d1040d107602034072407104003100b01c090014010001a8110b0380148100303004080110400300f0003402d00d030ba0740d2418060140940d03c42000203000000701e41020b5800461207507003040c103c2d41d0307203070702c00540f041950407003070f030380146003a07500c20011403042440c81c203030b080b680e550644844001165052180150b05001d86440d0601c1c02c0510640640b4100b06010143c001c0040d6a07603400e020320070b21000046016104010b940039201494078405a9001c0d8506403580c42c0781000aa0341c40346940e01c0144226030740b40d81307103000c0120000052011440d51403540594452007102e05d60450484104070754000000f00241c0754035015031000251198410924100b190740403d2400c0265 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 540406519 1250 540405269 540405329
    0x8030f061c23010e0706090e280f02070b0411040c05040b071118010e0a0e071719060506030d080f070e0315100e0105010e1f03110712020f16 62
    0x40301c0d0300303204c94101500070020303880c0120317016a44c400032044d07180c00d4000780504003070300c2c6020200d2801d1403600e40e01c0c54103150605107402c502ca0014410604048920036030b000204261002c044000400051018060800045480c119401c0100080e2148054034600450081e0b407410301c0c01040a4003001204c40100c500c500c00100a141c9111010a2116040340240114031a2421100116016100034000c100340902c119018040d900d00b0030040342002043e000460265100b491017621031104c4030780c0c440ca1301c2750040030301088601d00784c03050516003040030582000f00030068081161510000d111071350410058607114252440e800c000074580100051400100c06540050180440000300140c0c201c0d055840c001c0c4083c1c0e031310401920348580151205401070f04002c07a24500159108501e2000c04440c10001120226650007c1e01c940100e6005c550340e079500e00e00311200a404010400d44075640034001c1c00d0520442140c03594400142c42046005d00c44c4001068014903880c0ca44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 540407769 1250 540406519 540406583
    0x19080a031401081b100f0c060603061803030c0e0105120604291305040f031101020c0a0c030b0c03010b120a09020607050604020a0b031e0a090f08030f061c 68
    0x100800c1d503114014544c8800808544900400b240001400310382000901000401210385500108800b030344e10641c4c1036082984c08039186a520440400010558400d20240d941c54000741c828401035460090203d50104810405105079040801c9440e0780c4a0111449100b048145000c25202c0c100490f000e040704400d0307140c5040070181c2c01d071010418070f000d0285c0e182084528207050f14601000004035041580c000d4041c141e40b07000c1c00086030152100c80c02c1100e010000515204011031260308100c0c1c260812603580b42e080c13008105005410642d281c00807900d0081c6451945003540003031107449000d4191818a01c02c0000a6a88d682640f00c002c02d1500a40303025940c00e07203441c009880e03c03c100ca0032031092141f41804590400c2c1a0140c0f40725074039100b0480c43c003e10200c0100c0100710b0050003888060385800945000441103000078202601c10601140c5a0070710091a80c61440008c064601030341000d40030800d2000f02200f420745007500240985200d10000741048140b004441c0d003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 540409019 1250 540407769 540407801
    0x150306020a0819051e07201f050907060c080f04060806040507030c081302030c030708010504050709020702030a0204022203050c0114030405070e0c04030b0708160219080a03 76
    0x42016400055681c403070503807901d401c5464140f000070a07044880c1600d0381150030034840c60340c0c8094a80008015004006400c1504070301c54140082103142c071018520120540090125950a9003904403070818249080000d004078540031070001d0781c4032883e10a903810444009000414032150104950235081c0100d0088d60342c85e111140909909002d81d551801245003800141100703100748240c2007800309540d6813000584880780e0496028210040599050045d01a480b51583d400c011050003410300f080041020700e8a41403050820416510901d845401004000010382c1c010560080b1a41c0c1240c0c010f0b1201b055205107070502da007145160820700306446011060100001d485000580241d84000175090020642a01c3c0e00007034070f0003000356125a00c1071198050010800768006142d1701d404c0d04095a83e12041c034201c40a07a80200414454000c0c8466000110500141481507000921020103080a1000e90700d41828010345091070200310300010900c40d030801000070b149590 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 540410269 1250 540409019 540409027
    0x100305160507031e05130519050603280e070f030f030f0e221b080a09030c02030d050a0e0a12031404090f0203090c040e0601030305070501140f040203071a0d15030602 73
    0x1c400380c43c1da88040040400c2e80c8104400045a20304000002e06128101c128012340914007402d000868001428101441c1c103403e01c0c2c40000800000100b031030f1400d001b804a040740c4801c1401d030410100f03070014143c1b0b1181c3d06060000c00c01506c41404403a9140c03074003141400448000b1660501d001c1c84407030744600442000088501d519106c2031700e080f0f144074200455111420380041d20404a0820703000b088001c400113068000d15070254030464040d06003c0c1d1042d106a0009080400309215880810f0010a90f0310b602503007c0310301d06030040150b40200070305003007490345089070500342c01c004c08000740c07080000c00502000c000da4000f45085d100500c0072182110005019400842d000f1006120350801a541d030314043c040c03045842440c401410341a42540ca08035241d030310800040e1410340d211500e06a00b0402c40c2a10b41c81540f000c1207030416800c0500c10107042c08000d5001d0070355424080102d0815403a0742080f074550411f22803000505007070711708054240d440c0651019101d640301007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 540411519 1250 540410269 540410327
    0x9061812050d140301121104060302030303010f1a031b09030f0607020f0c0d11010c0501020717180d02131812231606050a0e060a0b10030516050703 65
    0xd00e40721841026210000480c200c4001985240401d00c04c05048000c885a8040860747c000010600d111000c1d0005c1181034498000c00d01d1035200382e100301a40c18140208200c009202e00004000c2c241640e0401d2960901519920501c00ca480b000e00f891140090303004050303a0101701500d0205007000035501c0d0303460000d0010751030302c02900001d0194042c068548103e07141c82400002d07002e0b03021507d040c640c040940115441d0110b617004030ad01d99070801c03900011448128846590300d814060055803291f2214110100c406145541c0307008210f52002c480042e6515644510340c3d00d00c030f0700f0004618410321240d450503800b880e005441040b000d03000600007680020502c002160650f424611440405aa5250380c8103080803079012003520354265000172110b80107070340c1081c081000400c1d9031a1255880d401d026050f2034110081360f442c0d400780c9403820310140390b60320000789060400881c03801d0881010282001018802004000a209020140600318003105c014000d2840c1c661000c1c50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 540412769 1250 540411519 540411523
    0x203181306081e0a170c0709050411011e0c06051302041e1d071a04501003152d23040b040f0203010504060503010c0906181205 56
    0x83c040e41c0b100008180d1115154034006030200c801984203d0038803070305440c003050034003035080300002207100e006656002500288034007070309002e01d00540701569641410300c005448103200c4030043d090183e000d1a00c041a54101c0a003207003040d0010008180f40d91408030961800300c503070703500a40c8107123030486aa1102140d00c0540210030b05041c020002e0040d024031f100c1c14861204905044c640c8580c1b801c1c45804240440d50741895a0b50305144d007040e0702c0b81020200d03070038241010025049103d0740d420703640950714a1a0350340300848122391808809900e140c2108568110b086000700d046000400305284660b00525120704c1c0c12040200480d150540700c094643c804159100001d0103180394240c0b0320180c200c1808807181180351041c0412285001050203454460542d4480d655203405001c0fa00c030341c0a1110ba1a240e11001607807903040c07104000488005800c400e01aa14240a4031551500140b07140b041d0b86843c20130940615101c8a004001c184541200c481300e108411604100240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 540414019 1250 540412769 540412783
    0x2d18060909050106050933190215160309110402070f03141c1a06030702030d061e03150b1302070b060108040c17032514060403020318130608 62
    0xc08105100c1c2c0e90341d582048400b4083c40110039805114814002070a030b4984812000341001d00c00c05900950071241c00e100345402031110f95060a600582c007101180e4184803220010182030114a41400c080c0501030006501c4c040c03a07c2811307a5140c051050255040000414541c01041075540e10110b00e40f90440c1842044c0880c049900380c10101c04000c1c15005503004014140c0d00d104000d440c04900e20043c01161068a10084500914040c1c54076074100551140e0b000d0707002035969144a200c0042182d0311030b48820564896034042401c014015083c04045940280403011280b060403ea4401002d00c0e81b01c240d4441c0c00c001401c040c01905401a141c05400341894030b056903201d20064441c4401240d00501c00b10000c40d0a10816210120240c440050340b82241d04100b10ba04500111803014a640110b503400d06400c201000003e000140c3c0d4170803810b024140a040c65034002c0d6680c0244116030200000c012046146915540c1b0040f40c07400c552901440b00c1a40c0d0b05101c0c0c1c940d08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 540415269 1250 540414019 540414029
    0xb03030304080c19380709050a060809030328060f140405040b010504020a0215090114010506070c060309080904020d141003050303180a0f0809040c2d180609 69
    0x3a400c039000a80c261404080c1000750410001d02e14442058000601220074004c00304607405c3d28030403028003060102c107461042d2640e446582c0401e09210810a510549901402c2009400341c104202c117800802034035004881c10070183d14906042d00c034003030101c604c0d49003607072400c0c03a004001134018441c000703101c00c8901d048ad901e034071000c8003014401512001c89003c0c144114503001044281403079402088048200c1c0306880d6211401c410400c00c84c1c00070380700d19049a4440780a80f500e0301215900a0040030112007007881c0c16515681d0f4aa0340c44140b050b001415034502018003401500030407a01c2806000788119501d0300c5198040d4000e1001c02c11a45c085900c0c00d0015081c5804040c42400b501d030048002c41c1190f0381c1134481440064403440f184034070300910003120300040b03400a2210586205104450300d4405950a00c42103852080a610030829642c42c034241090704c41e10105803200019401064032940c0784000d88842400c03005510052900c80300018a041c0d001c01d000060714 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 540416519 1250 540415269 540415273
    0xa120e0910031703040f0b0606040b1605060a0b09041118071706040c020309040b0a09150e0a0204061409041d0706020f01060506161e030e0316030308060d060b03030304080c 76
    0x90800c3d040c541281c00200c038020012001d146540d00440c8248901c240d210a0007400315103800d03220707401110b42c0d4105d041d0303c03c803186c0d0b5140c48508100702403000980c0403400700020130040d0f0214000032181c1d10081d10152401c09003031305c40c02d0340d911141000d41074846140c0a14045040c41c101c0180000d0003010001c1d0f10341003110109907146440e00520421120355030045003804151001c0100a20a0b50f038400c0d8081f0001d000018900514001c09008440405410041c54606000a0120400105450b6095104000601508c1d411840d050040c42c814500644c41300c0e0440040f4000b05003c45007000d1102d54000c080082110010b103100a5035650303030a03680700c3e01940e5007040c0ad95025018103a40070906201d1214420300341e00e42402d1080c0076203e8030114084050581c4002c9514034800d0380010001408440320b400c0400411041c00e965106600c1480d1a51310000c22301040601a2449040840142d00510115401c6902242c1c801802e0342c0c0e607410300d40b034048459400640031245034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 540417769 1250 540416519 540416543
    0x803070c05060f060108011e030507090509060f0610030504080702181b130b07051002030703050406180302060f0c0d0608030a0207150905040b012f07050a03050a120e091003 76
    0xa900220894013561043e112130b0016420403e40a510302112160504402d40c0841d000002c80d5080154000400a10300d0015543c10b0000005051680042150022030512018485103440e0340103540b0700030040d45000141605c9501c3e0028030740c810303004060f500c61442031401c0542602c032002c443c003c80580c1c0b034410404c220003140201d58001d40c001c540216203401000c000100c006030051100a100c0d030b041d80c0b07602ca410824407003260000e884070030009565008210401501d44a01040d1202041207180013243c0c682d402581e60300c0046c2100454040340f03011428a41c11502500c180030102901401103548511915a490700900c200ca070052040b0400011905004508428854041d0f40c1e203610321800c1c04184400b80c103052144030304100000700f84021050203a0240b01d8114540d2841d1034030540d5150356580340c45140d8000900c04d0b44040000c00000e800080c950300502e6001000402d4101b00f50016141017050000d595042028842040b08a00d02400c488066900c03589012002c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 540419019 1250 540417769 540417781
    0x5010f0501090b0306012606010e190231270b06040812030402060d140402010306091a0d02030312010806070207081507120f0c0504030c2c10030803070c0506 69
    0x1d641190031100e405070041c90050094407000316548500f24180020003401c0401f1102c10383c03416000f40e10204c1002c283d4030038403092030b20840310451013104501c0c0a6040c0101090200d00f0b074104c812100b0048103041d002c5408031101100c03414001d0a10600e0240c0007102e009a40c0c01c615500d1078210b1441d0b1404c01d41b0207007880c1c500300361025501004024150203011030a0b1100c03603400608140c0c0d0240e8240070030a0114150f00440d10843c0c0e1401c1c110f14107040610025054030925004941c0c284e04000c1c04a151100a50040b802a6401c640b00071543d00c050011900310301c90322202107080c101c0f800002c40d51510015249021707002a50071503000540d103054842e100c914108920121400110204004c0703882985088103401c070364980014183e07844003000c0d08a441d0006030001103140401c04005104610704503c0080c41014114554801e180008007102c42000345403600d8000940c01180e200408a80c444024641c001c0e1095a42d09010380b000c1c004400d0441d08075510300c01d00c000516 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 540420269 1250 540419019 540419021
    0x304080706031d07030807031206140310110d020d02070602030a020304020111010b0a05103f060f171009110a090b0f06160c1d0f100605071a0405010f050109 69
    0x14112031030f4030151582d6030540d038500442d6848180e0650400909440114218100e445420014201d03d40d521040c0203251041c581030004201c1b424203c90320303248580c1100808142100d0b002c1d00d40510069465128280e068000c0c05291000360007980f02004200500b8030325130086000ba4000d0f00ca182c803900521072243e0aa13a01000d03801d4000280c02d104010600700102e40d000020031909058000d1111011050350010400d032041c10081800c41800e4103040400d80c00742204c0c18454010701c0b2060600c06025520b1030184603843d54441c4214050080403800c1c02440308414200394103002031011030614017401c00744024428850074082e05c0020b5440170340c0c42034814a41018001c1c2c103800e1602400c00c20550080c2c0703000104401d503203400390005110035040c84003030500b00305258201e0f03440384044101ea140c0241680c416200032410700560804650b50802200c000f40303040c03130f52400686010340c0d6800300ea030280c240c2e0084101c00e100802c0010740107000f015100b02c1b8200100d0303030707101c003604 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 540421519 1250 540420269 540420311
    0x81207080a1b0609060c1806090b0702011416020102010606080403083907110405061c0503041205030912031c020d11030438070807020c03030408070603 67
    0x40920108200000c01036000e50020070080d01c1d0281840d408240b81c3e02c401c000c2c1c0304615000c032070aa98516000c0320403034200c41030800c080c084003482400700b0b0a0020291056880b40140041038001240f032a003168420140a401e01c4c414220031034a03524a61814002c0c145d5214080307015500303004002c82d5080c42504868441d80d01551204e0003910b805482d0f400d07484a0302071480040c05038102500810015034040d9066004040d0aa540d810090a24001c41a1010610b0388a9420002030011035038550052941c0300b0a051805246010785290052451196030710005d10801009000400e00801001401c102a015070303020303d5080310140340e035849103d90080c003551103200020071a41c546241d0701070900c5480b013000018221202c00b0081216400444003150141c04484104510304003c50204010002031005a990300a28860680e21204000e08580c100200400001c040f14030801c080e2001c294082c05485d6940e403100043c40d02c50400d4021324020034100f15201c40c006080304240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 540422769 1250 540421519 540421523
    0xa0203012f03160f1119140a08040506160b131505010b0f07110402040f0503120c19020f090a1a0f06041401090902040e0f130b0f0603030c0303040804081207 69
    0x22111000c40000190341315070300400401c040245042c60402c1210080040348082d0100c0d07500070361840e0307041c0340c80d10322003a440005084541016401c003001800704816202070712011a0050384628828000185501d034444020b01440c0c0a04280300c941100c0c1d4604080c0c060113842c00d205160251803041d0244c1d1400c0c41003003290401040b524100000314000b0741070440c8a410001c036034020b160001400e036007041d04544002209000304000b0740c5000c000c454100c10310b0080c4079040244410b07100c2c1d2100c038401d0741c0030141184000e04104660710070740031a00803800140750340c3c220304003100c0c070034000c088a002c0081e0162015100e00814500f00c10000014000181400d1510707040040a00e0884c4486110b80c0c18407419030804601180c0c83e002410180c192014058070b82d01c2c001403513108908003c0c182e60540391200302071031301050a051007554407024005440388141c8801012078030b94400e08500101c0380c00080284030400031250000d004a464804c1154920342e42c0c405040140d229420b00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 540424019 1250 540422769 540422791
    0x402090a1a0105030a1d2409030a03050c04180902010e03010902210114040516090b090402092505070b0f09030a080a020d06030609020a140609040902030a0203012f03 73
    0x500070558400c000565022440034004583c04610002050030b01c1e10345602d104080d042510504000240111140070481000700d00b0881d50a0a5040c20303107030b103e0f1110200030151654000740032090f541c8100d4004080d04030054407d4408404520018042000e080f4009640302d0018059460705000380c0c0422600200f100140c02d102450004040b8284140c0d03054554a40206c1785110b09807034117080c0308500070030140c4480d059800180c84001042c0e005403241c40c3c0b6002000e0655151181e105901581c107564204440e10307260460603500c0310a0550500745c204180400b1625a130020140805a2042d042420306448201d052030800408440b083c0c00ca0380240710611020b403042c400d01c1c0d040b40319041c0c01807400c03491400143c1558039581094903126100d0300703d00d085050480c40300c1c008094408040440280d9100082d00c00d10400f1509441141c50b03d800209555084c030145c01d219a004000300301401c20700d42e5506000382c0c1301d001c068505982805007400c021250003124842e12850300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 540425269 1250 540424019 540424061
    0x110306100501030b040b030a08190315090c02010e01020301060e0307050f0607150605031501060806040902130c05040e101505090a150e03010501030305180303070c0b0f120f0402090a 80
    0x100440003882d041d00905d61003038680c5130810040c0c60030b01221020f1402a014987d80c4c100715422281c140b404d425450302090729150941c01e80c0320441e40200c040d12140032011070031090808040b801360162640040165100000000e03034550801c2a0f00d00602d0f058094640e6950b9502c1080100180c4102143d04031030208001c00c00100c0013032051080c800310f800000f42d010748487c00701e490180311082c10070900140400511145821071540395129808603018442540d00b540805c0b5461411078500043c00e4444403403141003400b94040d6009081d07902500c0c8280e19055420a000140502c1860842011982d0a0808921640403112030b440c010f00281e15440c84c1510907807010181e1b20000c400c004014074903e80e41e5900f80500c0d4020740c007950700c40c1d4581c1c00c4407081d1288101e42c184400e00ca0f5104220f4400020309015000084072100b050494a62101926680c490320800ca80b60000c1c0941800304040b040d01540c0f11805180240d5102805d5550220020b0482e0780d1815040003c02d8640703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 540426519 1250 540425269 540425279
    0x30303040602160507090c1d0114133305040605040506090a090e0a050706090602120a0c02030f0a050d0306030206120c0c010204080615092e0f0e0411030610 69
    0x1030010321110120f22615000c00d0301541310b02d810003000c0d40143c2d15a83d124056101c410f40e00100d480c1d80e00480c9880300550384100300000e821103003401680c1c1c0c4036082c0810700711050b81400340d0400003041c049d8800511421200c000701b0305030840055403404d0628140c90309003003601c1001524242c0f16280c50307a525180c20201002540d1300301da01d0050b030000d0b40c86000318a03501e00c1c0c012941215043c000130030f46940032f850820b05000040d00600e0400416103010002180d00062120720207402801413551003501490071070381600200406501445070340d4001c00601d400050300c0c02400e00407001d44054581e40c0200f141902c2ca64800a58840c1060020607420030045c080d99801c42d20034240c0030310306a15580203a00ba038029900040300d03a0004010410202080c45080c0841c10046800c0091071621410700b40c8015200d607001c00c210503001c00007280308841c038800300303001d03114144800c65a0740d5a800280700320082110201d90f000082000100b440c00c00064140c001d280903021454010700f00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 540427769 1250 540426519 540426521
    0x15032502100f02090a170705060f0a0c020a030f080c120301031a09280b0a0506030d14090613180b0a0531060510020c010207060f021c020105090d030b0303030406 71
    0xd01d00a003660b9a00b041110501e0b0f55072040f81c1c0003000d029064428681500d0a0303075041085541c0705a02a2a003049032032109030500c0700f10384030780070300d410b14505140803400855101411908004c0c6100e00c140702e14001d0101070f43c064043c1d400328504881000450450400c003601081c031006100d40c0501c0c0c22909100014000036900001d000110b44c08002c03000107140c4500034021340100300c3c85010454405000c440070310107520292241081c0150b080950200c0d581d10800b03030740e100c2088000e8150200e0041401c0480e0400e440040909481c2d50000d04d03507840446052040c2040c000000094100c411254001c06007030000080c00420118600024007d8200f0500b090240100408007540540c0b0601480200c0d00600184002141801c20b81400010341c01c00c010101994800240c0c00103076a40000e00b402940ea0a02d0401c607400e00000d000d924203007845105580c09004503d1410b103940d4154000d5120b03000180858006c41c0050030150100c4100804090709904104000ba001c2145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 540429019 1250 540427769 540427781
    0x8090a1e030201050a170c0c0d1403060d0c150306052806030c02032209050c030c070807020f06160309090c020c040905070509010303170c0a17151503250210 69
    0x1175040481d4404210104041480380459444092078000303c1c541003d1001044542d40000903424210180c0410f100c001f0414000144014481c921201004080042800b207903070090043e007078559214000ba40b0302801a280901895000c0c01d840b848924040c18002000032003140f40350360703d001c40c07070620008502501d1007000c16010f5120070001441c2e4183c3c80801175070f00d0007600082d5400e0310708200780d003402d42d18050a455070404041c42481108010a01194152603001003559a074896603c04107031007203140b50f080b55001501148040b4010620680c19418174131a036a80504245c680503c541111050498107005a1010300e601c1c1d2681050350041c81c0c860b01078003c840d803003580c8200280220000360022800a034103190a2844060107040181c0c00c60f4070850030b40c2c05d10b00e00700301c000c1c003210703510041429950081c2e011032010f0381c0c4411103048084001d000059525440d0ba854038071b59009032292030710381d41026803c0c6141651121314454041d0654090943c0e5070030428803c0c09852 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 540430269 1250 540429019 540429037
    0x82401030615030203090d0906140a12090602031006050a17060d0501050412021b06030a1d0118050f0d1b0602040e070e010314010b090618040908090a1e03020105 71
    0x5524800854a050034680c254050b04090380c01507500e01c4c04c04c600f40d0030204815440c100b44a4103440a0000e183c2000c84000c4c00484510700640b0380030404400c0300c0700380a46418810a9191415550070300c0020707001180b041d110b402e20300c00080d5441604441610030044034400180820088a041055001c400c642004009100460f481c496131150303401c491060f00c08030f926214202c014413200c0c0c0c060003844a55070300340d01c02110800c0c2c03010202e01c1030b100c020000110140da0f04044061800d0500c200c6038010f01a2000300411814584c1d01440d14429079801e503114441c240105400c100c00103000140d5110960740c43d0a0300c102004401800d040442c021a005c07a0203020100b0300030700303001d0218481d212039a03c07042c0c51349440002508917500440503442c0c00f620000144465104001100c01340300702640c1240d0780c3c1d00103038150310f910b00028a0403940903081005403020701614001030301c0d014104941e4646070366130310966052401c4001108844c1034104500c100003641c010005000313024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 540431519 1250 540430269 540430271
    0x40b091c1e140d05070209070c0c0b0c0a05070306060f27180501090302070312020327010c0c030f03081303090302011b0210020f1b210a0804060314060108240103 71
    0x315040382e114240511074200c0e0000610103c1c0f08000d600d0844071080d08a4050f08050b00c0e103aa198070b48811f04030050103421700480c030000d14018105401c12800c24010b80020941d5202c070748a00c1c2080281049100e455158078a00d000407174040350100020040400a8080c14000403c03039082c04080d04000411200481074402994003103842030007070881301c40c4641d001d015018110314021426800440b0b03020219031080c0321400c0040002070905d141d2014803082c202d441d40e00e5400403644c2038140c0c8001018100030100000811400c0d20011444a101c0c1d150714140b41d644009442100348010b202800107801403108202550065100444203040c0120f06d0040d00d000f6004100f42100346410840164000c5080c0e80c01c00405102205441e9124100c0460342c40b500300008030346202140746001c402c460142000c0341d00030104818040f0641c04104640c40315510400031b4010214903c1c130403040f0200000007400d42d8890540248107102021200c14418a000040d04c040b82140355032034145 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 540432769 1250 540431519 540431543
    0x60614130902030a020a18050c0a08130206042d0b0f03010e060f060f0a17010807050f03030c06090d020706050910050304060902030f0129010906110c06040b091c1e 72
    0x541c81d405e0001014001d40302e20340030166007c180000440704014007021228070244914031119900690a50f0800190448016180c440b400012040d01c200e078060000c010501007850010500c85030700200708a05010b07040241940c5a0120742d0380d101d80000c0c1d07000d003d410401440500300b403610558102c00050501150f07810030f40c3c0400c11a502c100e2030183c0300500801d480703400d1540040501c3c42c01d151420211590b5142804c0f007655000c1c24001c1e9803080a441c00e10b00060344040042d203010700f101c3c00444d030031420814401a102c04c050701e0b6000041c0222000490114020401c4640c0448040c0900110b035680f06400c8a0541010340100d074071503114000f010140c0c0d000c0040d890030402d200e0001910800300c07510501d003401c00410000304490700419050b201e0380c201d080001140c800741403200c84109105982c07810041d0161407980e21840201d07000c10b6180000001d045614025940101040080c0d04c4241c40e812420800410300306543c4040b0481084905072140035512a82406100d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 540434019 1250 540432769 540432773
    0x2060f1b04030605011e0807140409060507091a030702100b040902031501090e07080303060f120d020d09090209030c0609012102130b12060427030c060614130902030a 73
    0x650341c015441691030342e40311030061040314000e40385420350142c000d13111020145829003282c0c48081501c03900780c500c80c4d09401206151600d0704040e0310941d00010420961400b444090510360041c00380300c0758102c002d46407845014040c0200c80c05076095070014946200158804005400b609200c1501b06440c0c290640040c0c5080041d03001c0c0544003110000d0560600d0300a800b201ca203845100101d0303001d80020010003a005c800c40750445001d40e094030001407a800801c1000c55840740d03403282c902c904500d51840310b502050040701c407007032581ea90704c0d01582c0d020075000b80e01415650f03a40c9030300070080b01c461074908a80106011101030501c8050f0420125500a0805d810b0b2800381000d42c0026040100c40d8100c0d6021000d031240b4115242402c5403030f1800c51204d00000c02c01c901896a60410100702c000903482405c031592408c1e0110701e50700d65403600526140e056001291291304101c80415000001e46003040072260207000005078800113203518002c1c00c10914280e0309030141080c0700340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 540435269 1250 540434019 540434071
    0xb0606072d0218011707180b15070807110a06020d0c15020c0304090e060c1b0304051e090105010305090c010804140d110f0c090c07150509070306110a02060f 69
    0x86007804400c0e902c410b036151030b002c5404803080d580c0000498008440c14809040c40c11044030107a0251707403002518008e5200400c1c04108043d104102513600440e0901c1041204401054034501c917880c04010314464209000c452901070054001581041b031030105818403800d00598854001c4880c084038089010040c000c03030707002d43c3d2803030065000083e00780b091121500030406d480c20038200808040c03400720304c0c80500b4080e0849110100c60000d0004841c03a6041081d01d020300780c010f266141c0728003900c10f18100c11110703a030064000c0011000002c2c40c0c1d8003a10402e8450811800a881f034000c900d8011108080010070455203c2105449400b01a0f030402c40c032200c02c40d0075201c0d40060b414200c00c880c5041c2401807004141c2c0e0000c1c0840c14907031110f034501340d0001c101c003c0c069114030075460440040090f039034903101000e00c0d000402c03034005400600041100e0060000b00402c2450080010091281106440c0540d01c170001181c40c034007109688680c40102118800005801113100710 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 540436519 1250 540435269 540435289
    0x403020a0b01170606090c030c0f0904050f011701050f1306020408070e0103031713060f0e0a0b180c06030c07051203041b08010b0a060315050a0e040b0606072d02 71
    0x2083d003802c1400801d030490f040000c2900100d080f80e843c010740ca80000c04000502c030042500074121804554a0525a004826103810700d100400a020500d01803030490520b18092041152064682c0340401d109a13061260600864044a0500c1566118100244041c0b000c000449841d9800c020003d50002c050020b6070240400d0b0806101e15403441c2030041080e00400c0701010681a03403002d118204620004000d20396034012004038580c000b00900702e009000000382004030740680003032101007004807118148107810301d02010728606e4005440d42c4d0754205182505401550410102c0c044000c83c1c00a00f400706c4c0318604683c0030300401218042c1c41c0d0400e840454000e464402d03050007040203040e03024080c05142c0000c1003406c8070100001e2180602d881441c09240e81d4050301d42c041c01d0940a03e5000d00400340103c0d14041e0b4801c2d0081004100315070658180081d5008204103240800c1181d0510780c001c481c82c0e5440550380328007041c0c403201150041d001c042065491006882e080081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 540437769 1250 540436519 540436529
    0x11d09090109230705150715060f060c0203060f040f050a0305090a05011706041d0d050909010e040803012c07050702011d01020a23120a020709090210080403020a0b01 73
    0x3081d0400c00e8642010203400c80d8580f22508403810103148942200001d0400858808440300701c02c001c4042c8100f0083c1c401c0c450301811141c125207107200418101d4006004a450320202a042c05a0b2100211010521480001d6243c3c1010001c50107583d85a10100e4000740901c213041207600c80313691610300c0c225071403200300c2c0030442c00708a41c0b0b1540743c0489420700924007828001102c00c0040c003503840750140100f01500c47c45e900c1c103541481c0080c4c0200041c400c03540c48211004a80c1c040340107413098211609a500c00d5652100208004c1000b03650280201c2e03000e0809415a401d00c00c4051103802d0034200465000d441c2442c0d1850030b03412500d0135014984039101e4640d41d02c014000100b00888104c03042d4000707400400300c00481e0740e0004560403226048101c2c565500c24481c101481d00c1c007048800355444c800d00701d580d1a405520700c01040e002031950211607010755545d201800342d81700030780041e500100503070301e00e118113015404059000d80309205aa07008001d541d1504a9680c0c00c0e002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 540439019 1250 540437769 540437771
    0x120f030203430c1505040b220c1206050c0901020307020111160e01150e100c050a08032805011d0702011805060a1d0a0314040f18050c090f011d090901 66
    0x104a0034003140100002060161340c0050000e40ba264540346142940a440f0310305001e07042d10300d0a9808103410103802c00030b6000380c0302000d582c1e40310803d0a2102c0507030400e0766014585404a903000882d2000c0711040f00040c3c0203117007000602c0c0c005580c0d0039107a140b075192030b00072a400c80c5540d110f1448264040d040f160020100d035418401540b00142014001ea17042c0645040a403907540d450884954041c03045151000d454039091810300d0030303c072050b0001005210003006204690b080c110b840403c1e504100111400800c4e03031540582a26800e12510300651030010450130030614402c0b0f06a407181d0b050001244840b2001c1d901d503518537003248269140d8000d80c0c02d01041e2a40307030103042502c031f1040d0403082e014082aa42e207030301d440e10804014280003011824007a03501040b41524010700f01200c071480110340c1c940e0701d00c52200150ba404010300d403408000520001015059035000751018000000e171007030074001074407261407150001800074011845e280d1103a6460003000c3c411640500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 540440269 1250 540439019 540439037
    0x70c0803030a06050609010e150903060f0a05220f0317091f0c0504140111060f07031506050a0e0a090c120f02091f050d0504120f03020343 61
    0x14a82201c089400161040d101005603a503183e90001e08c14903128000c8944441c070b080e801c14111002c2c419489000e0f01801844208800c1482d0814018030540c849941488565502403a0500c0200c0c1800c0d4100c100d080c400c00000820fa00401200b0020300c2810f000e00314032019558001c08050854800015a20401542c190b11070380d644178540204050005024820404401a11a01850203081c0034481d00c42000c600e00c0e84540f20a85290b036108055400d1801d114480f030459500c1241c000b4042030030482c1050303500703412014075421500140c1d12107040003000b580456403108010000342e40a4244400800c05444170310403954861783d5038a5030030820030200707a12030690345980a80440b0340d20500002c079903901c0354a00c00708103050301401c13081c2d5110422030a99031400342c010800701031840c01c8104403c0184490320b200725114280c985002c5c801c241d00c01202648412294030300c1d90195505042d8400c003910602103240c90285841803006130b2041c0c40e0140c910b440c46000c0c400603110617 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 540441519 1250 540440269 540440281
    0x30c090109091d1c0203070602070206040b04030308041b0b030c030603010603210e0901080307031107030b10181e0c110f0c0901080a0c03080a0e090103031d03070e0c030408070c080303 81
    0xc6184c07440007006801070000365103400040e49a004900d0054411900000c0c030070708542e0360008490240c101c1c0442c50740c840c0d0316814000c180100c2154100c4060381c0c03041c401410000034080c000100d8106006840c03650365400315080e4140c2010705020303015034aa40000c00040c0e03002640c600c038005214403400b6611b0301c0741c00040c00f02007207901d22802009031000620010301c011040710440761b01405d00c03050b00e10400102c50b2403c0700c00d51000d0464000b901c00c0c80f52480002ca50b178400c9401440240304403920590310716048502004102261050f12649040c00403403d41260000082a08041d440c40203c0c0c9982d504004801003000c03000d8000d10100c0500d454562035460150601c5002000301d90701341d550b604880e41c058003000d04031680124080d20414454803010090071005403400c62656941d01c2d02910000056903130180800032100c036800181400035806045440d182c3e140c00b80384c0c4650111960a50000e441690700b036008014180202c3c44420050740241080401143d40349860 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 540442769 1250 540441519 540441523
    0xf0703120e150406050307050c1603030906210509010b03010212010302120d020a0b0a0f0f050603010b190302090402010302090607030c170a05091e0a030c0513090305030c090109091d 80
    0x3900025229101c80c40c0c400b1028100345060b64107403101401d00b56503079114440c0c00c0d034003070050010702401841140c2c04510090000040c54003101e21036290065140d4447c44d080c1c82445480c0e5a000c15001359103400e20402001c0d4101d107411a002c0000042e0064090340070a080e6405000448070030706428004004601704058210398a003040740240c04032614044000b52244030428000d4035a0607040081a8201c50301e5020008035071042c2401c1008440c60760726080902021076800c1e102e540703060303012440383c240035843c0520120800219004941141d00304407000d0350140003a410954240161070030340d1242001032071a10f000e502d8115241c0c48501c0d001c07100320f5003540c00b0034109100b404800100e6800c83c1c10b42e05607407411521609040506100d070b481c80c908410002f07901000a101c00424080e204482c00701ba55030640d03051041300701d142c0c19501514050721006000403070800005a40680c0da401526110805140981109540740e1006040d10f2186c9805124812040307a02d0300389100c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 540444019 1250 540442769 540442787
    0xe1516020c03120703030b06030103060504060c0e01020c090c1b0a060e0309011218061a01080604020915160c09020406080f07020d0c020a0306020a020d020d0905090103030c02030f070312 82
    0x11403008010810107000030980342c0222002c10820341e980814000308160080d00426540c8030094006902c035a52410100050b160548080d1015483e200001024500c100c0c90840c0034103041e0024440700d0310045c04d100c0e40d040010886683c0440c00d01c07004580e80f0501d03800344154000700340102076070907003030410408036000219210343c50b80c400c01540510b070360031400d100380c0840000300010710140c2c2c40b14034030001e02c82924010305c22460101c00ea00742644900d05031841c04006c0e80c41901655038602030104a200d01d00c036042c3d01c0080b004100811115250040804000d000048409aa610f6840030a1800140c100940c060b80200d424840194000c4080e603000e0112045100503003080f00b00607403201d040400b424100640059000b00f5922800070b444015a40b150003103560b1005040000c0d02c8407401c00c0c4000042c01b44036141d8100e10700c200f06c40b205a400080402580f42d20b180c1e416184444c42e202c00b20780500a10b03503035160b407810600240000398040c401441d00b003007081e9001451001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 540445269 1250 540444019 540444061
    0xb010215010f09091110050406020c0a0e040b090304030c0e0601030b0d11041d10050702070609140405071103070c03020a050402040f150221042c16030e15 68
    0x11000d8010041c00c580b202039502100d08280d03001075110f4031428070305400c0c10001101074000317101c4104600e4031544000203008480707096096491028000342084104020f40c4100c1c0c20022035040400c02062181176441c0c1c01603000f4040780d150941d01c2d541e50310303001c0309617010000c000b01c80000c110444d42c041c040c142503042c00301ca8a250b0f941660fa82c000f100203107511040d008903913551588507200c1800c0d0001040049010443c0d203c0c003155540e4030060001210b0810050185410004070b4500807450002076404480c400221348000c43c040c003004185c0100100e04014004951000d81c1f0b20900003030003e40d026001201480d41580180b2500100e90f60180340191700c104010000710550f4240c1c04d060384d8180e0207150480035118400c9143c615900050040c40034482155601b901d0076a004208a44681000b4042c01c401c2701802c2c0b0810420302d40344451b04281c4000220100341c1d02c08640012499424006414191850301d2460046d0b1218200c41242000b0240301c110b00c1502d0090030000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 540446519 1250 540445269 540445303
    0x3060c1e19030908090a0906090605120a06050601050708030a0b0306010519140411033d0b030603010f0c020106030201110309010e010c141005040b1b1c06090207060b0102 75
    0x114890100c219180003071520010150b0b600304031020044042e0403150400c200800203a40750b521070030301c000206003078403865840f6842e00c1800123950415842c4841c42901d1a400f8000384d002d10744034000034040041400d410041c2c2000f104002030100e001441c0500c0c1c8540001a0030780d003031000c3c5032030014180c101d54410400044186600e19070019071006130f0303000c50b40e81807080100030085006880e0141c0711210156011040142f8500c5125454004403065981d070388080c01c40010882100c1a845a80e0325002e581840c1404100f02d020f00441e080400038000281200c1d207032038014101d030075031582100143d444a104009543c0e100c0344035555072a0100183d0b18002c1c0318030018014460b50b04c06c044c1032100d2192a0401e101d4102c41c40309480700c011040d81c101400800421004010882e4111200342450000c10b00c6a5400c20040a050701c00d581004c3c80c150700d400008009201c00d568a0780303100d440343c10100b0b11500c01d00107025498401c80700031030744e02110000a414038500790102a005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 540447769 1250 540446519 540446527
    0xc02060c030106110115030807020a0605070b06060912070608060a0603060b090103230403050403140a05210d060807240503070e043201090b01020606041a03060c1e 72
    0x340c4060449044a02d42e0510703600802c0d01c924440e0142c21501904548020344070800401d00500a005000e01807080701c3e0381311016210841aa03241c0a5079101a000b103034900000349807802c10500811120388001c01050304681e0760b07070489242041d150049800111980d040c01039500b40701440070081c0449003024040c6c2410112036401c5c0b4040d880c3e2a80c1019240c08130011080360800218244045140413a0118905800c01030140e034800d11003103d8603000659500b0b030b03c0f0f03808034080107031580c403001038181d040003940700b1300c020b45a9011f03010041d4802c21009824000304c1c8500d00060107034a000d4400103142403e86500c0d0101e407090000e05070f070301c6001c0b240483d034040101c130340c0b145041c00c00b03918030601c44003c43c0c001c040c0f6217290604c0c0c11040d001a4a20700700c08400c011603170200403d800c07a6a8850125030142e070324007807440d800340e4410400708045107415009200d504400d0012089082e52900000303140100170748800c0c3c0c002e2000141c9850000b041d0680f202d0380c2e1241c1042c1858 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 540449019 1250 540447769 540447781
    0x21090f05010c300b010c080c060906180312040c050d050106090f05040c0e1b040902090a060e01052b020712080a06050108190b061b0c0906010e090403090504050f0105040c0206 77
    0x2020b450000001034195490038080c0381a802559100001134201c07044585234624010b065607240b505565501c1c0030720a0314005951070344002d039000508000e05000c4c6040c03004010007580e00c0c14001d0300403240c8808041010445482d030800344a0750a000d81c00100b40503141c9030440e000c40b403810180c140c180d4100f0b0b0820000c2070100c0c40b5001151100c08200310a5600c0301d00c056032081074020001801c00e0005000504650160007a2030351100444640d00c100b42d4074402503614003403d418039408240203000042001040c038220904a80004a440007418000c418000882c2d00440080f105440500171303c034080d03580081d50303079400a000f000400c0341070b040c103001a1110070020040040c101ca0200e9031011030015401402800e100038110940320010200309205180c001440386c42c4030301c90382509801e00d03d8400309490080300c060315040307840100001400440600140188c050142c900000180d540342c0c0c0c03240c0e07440317078403006130400055041c00308020a030340c3c403000b40703004540c451414401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 540450269 1250 540449019 540449087
    0x9150f0905151c09020405130b091c0509010c080706230606120705091206060111030f030403030e12030415110913150b04030503040603061521090f05010c 68
    0x10810300b412441c0c0810600c083c64103005031007403c1000b90070034101020701280c0f100d1030003444080c500c1403481909075900c047c0015602c1d40c045a0001c80c1d000e101c010307400b402c1e014100820b0840c8061401074400587d540303484800c0e81c04a82c04882c1d0700d0740c0c1d2400041e03040018113212802682081d42110314100310300095810f00603c1c80c4604140c05500220705201c0c082d00854004c60310240c813812071061042085500d80800302d40d01804501d000c0121000b4003000300c104d0b80c0780c1c000c1c01121b80c11070303c80345c83c220001c1030264035440441c8510304c00303610981d0b141c2020303610071ba101f090b00b0f642e81d80903150000d09640c001051003030000f07810b10802c0c0942d078542131100030b6070703581c0fa0340050300c4060b414025081d04801c1c4c0c0102580312000a0210a201011000700300f0f403956500c0621401d40e13600c144001841e01d030f0f450310380000c0049038a5400b54400300f650b200c0380e000741d41300032516103e9621502982103a120088480f40c1d5510710041c040f0303404c01e03100304c180f51410010183d040104480c1304 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 540451519 1250 540450269 540450277
    0x1e01150b0406051312050616091d0405070305030c030a02070506091e06040504020a02030712020c100807020309220b0102070528031a010306050105030a02150a09150f090515 76
    0x1405103d00803420054080340c212110f00240359203420100302da80e090511948520041e1160081140c0c5a000e22901c1ca000c0e041c010112440840c0c050035161801640a1051501030012215402826800000724104001404d10b403000c45010b99900e00380c0900181ca800724983c0039601880b000e0040c0895a40c404047d00c090b0344001115003016a011800030f00d640c49681c0201e40d0062008c24180b80c8641e001020b070141911912561500410440341603035150100040e06900042c0c61640d010124070401d1000e41207815801180d09001000740010807001e174140c00c1c4c0400d036104c0c0c100040010180d02441043c42d60a002400340c0c24100760102321000c03912802c00c054030090490a0b483e1108603a040384c01542c001140d01886001e52a488802440070711060b1249801c1000116040c03a0200e20520010340c003c0012145124046180c102d0b03402c072807550414441d42200014140b0014103a86540d00a69600c000d001785600380c01a00400003a0050b37805000d0001d0803601e038403429811a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 540452769 1250 540451519 540451529
    0xf0c07060905010c2024091207030c05060a0c17070515070206011202010e03010603030924050a031a1002011b0c02060a0305100b0d0b13090f02041802031e01150b04 72
    0x4880760a030700d000840e502602c58403000c107003160071424640c1b4021401d000350201c9001110b040854010b80241c4175903803c0640070180c244034043c0010052442d2040c001c0146007018248100c480240b92941c10510003a01501d01c42c2910004203982080018050390080000d503032095120b40c1040840255240c10500030f102071320440040e0304040da80146140844104028001d01c12181c882c9002002d00a0302d12403540020316000c0c14200341c0c03440805500144540f0b07900d050400481c2e25088001d0130821018101034038130340c20750010741c0e00d400c41350110140b281d40012645020741ba240c0e541503a50071140e03104006c0d22028220041e59203001b1604140079903c5c0108041d103a43e81144035a031070650024104e01c00000e0b000c01802555040140081021150303800c004203425003420954440800003001c0c09541c102d040b0040c40d05602440103c1e00444203501e450420383d020a2508000104814000c1394182d905880000240109500c81d158110781d00a15841d000b048000d0340a14052 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 540454019 1250 540452769 540452813
    0xa020702102c0301060810150e04260909091b0301090503120a0216050d0206070e011710080d120e0f0a0b0a0906090f0506181b04020f0c07060905010c 66
    0x880b0099609400030809041da207025100c0142d19102d116004200b455080c0c2c044074000c16000440407600f028091140b508454158230381515020f00411304400c1044188ca800010720825525441c0c000c130301c80c42082d03101d00500c1414100404101b2072011120524840d0303040452440c0060030220035220030701c0c84420411201c0d22090b90b804083d01031644518020000080340c101401030004902e4501c00311a02a1343c1c1940f21201d0443d043e0000001c000c0c0840c1e0015808035030055a00d03070b80b907030022011144462958071016001d04160000182d5400900840c00b40d18844241d0300c14405590f0036140105484038021640341d441c3d0f0940e0b00081c10034841c000c0090000c60007500710161965210004006c1c845c294600552900300c0c840381035030700b803040b000080c9810140e50003649070b4140c00c80040030104c00400c0f809001c12b24081681d900186c081c8409240140c5c00406050000000e6000d01406030900f100100712002c26480f890400c40b2074a84040440e075085884c108001280da6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 540455269 1250 540454019 540454097
    0x5030f0f0712150302100c1a07080103080706060b0f04050a0e041a07030905070303030f050609010b19032301080f0111090915090f10061412040f06050a02070210 71
    0x44580c040e0001e0381d0005e500410f548101a44403680b001318259030520903006015480014a036858040e1002c441060100c0e003440e005202081640300940401441901d0100780c070307a00e60800501030341105c03c040e1511030021605100d03514143c40c80340040d18254032041214546503c60f000c11044510041d2880e0034070070082903c5500ca43c0040e08140c1e00b005c1110001e680c1d924008008101c2c0e07002c0c50050340e1601b40803542d98038007820040e040354094a442418074440c0a40310008400d05066201810350b07035140e2402108108407401d411200b98a44aa0035600d02015641082400e0300e2400761a49000300341400300a0040540e240001c00755640442d692350300401e0030305100758448056009400100300f010290012030030f148119044c06900d0941960754400703880c0403180007210707001d80105000300c0e985101150030303081c1e0103405940c806021003010b07104c1c00100c402c244c80c1e5802ca03a40000d00c2c0010340c10142c0c0c0b070001c924411310b0180500707800a8900d101800a00f9046054004600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 540456519 1250 540455269 540455291
    0x60e041415090c041d1e10260601080c03010e06040312020d0b040f05070f0f091e031b0323030a03091502041202030c040e03030a180b0705030f0f0712 66
    0x280989000d84a020b407030341e031501020117642041c07000891b40300c040401c0840800c5840350083e10014007464030300884000407800c105044009001d1658204000c04100d000392041420412409009025590142080319508410f045c2500d030110a590b80c0c55201405210011b0342c01310801c1408400d02c200180c070b41c0100c1e00b01301d02500a44044070f0f44075042c0f0b61445080907469000e64013610054544021440c640c9500b9500d00915004c400d01203542e8a80070803040019112800c0f0f121031a821800b503281e101e5654011943d00d840d00c00707801c0038004406000300102d69901814030202c609010021882c0030a0030f941c1c911501008204042d2036904040400c4003010480c07454401000e425911507413607140c49c916481d42c0303c0701a44284107105034000181418894141c960303c80c00040c524564440e082d0354050b00e0507101d1030074151400700d00076011414001001e8050748055841c0ca96a04100d24140c1c4108802b40ca025094404c4005000700710b90822036011113190600c3c1d02258044040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 540457769 1250 540456519 540456541
    0x90b04150b0d03113c0601052d0a0803030a0b0604120303150306020c010902031b0307050d030905060a1215080d0e04061d0106081501230d06060e04141509 68
    0x240500039840e1009401d01080e03085480c1a1004580c03004501c404d8003101c1704800742d914003080c45482c0c0c00c02031030000111401038002c60100b082c03150180c01c6000c02c404d103021407455142980400d040350004010300c031806030766014003d0030050031a00541080c1c1415011200e913804000000c0a040e940c0301703400300402d140c0c00780358015034000c5c0085454181e007003e0180641042202240b083c021004455016240080300000525014000b003001c603090006008004809076420390034000c60000000d0311355103840090460150717565810b15180c00038911502a115600d40d84941d45400b41c4041c40880b40025100703c0c00b44040c40d02c43e0410714203070003040080500b5041200c3c99200d0907140700f0f220080202c268102c481541c0c6112040e901d0100d4041e50310040b40c50140000c0c40420903070300818031000040c8095094101203451721903d0303000d4008850155004401040d400c07800b4800c6450311307100744840c206000c60a02c0e500e242002c110440c6140c400a00ba00c568142001301d01c2a00f40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 540459019 1250 540457769 540457783
    0xc0309100f0e15040b010509070c0503030c0403020925030c030612210507050a020904060b03031218010c05030c03100b03010b0d0b15120403030f090b04150b0d0311 72
    0x400e81004518101d900304405000d00c010b604039a84946021014001c00c080c0025101d190005010a034076400c20702000311011000d030400c2c0401c96080b4040c00819070600042d0b01442000c100c1c2ca65813407451040c00b40340b00700140003071061509000031401011844c080100d021840b0b240005610304a03180c160010001d5401403451128900c02c0300c020045200980144032810580384a00c07582c2d00c490032507061042540041154110080303020043c1403044045030854030610010801d00c48880c0800d01c0c41e00644070440c03800692405006400b5032500c1030794042c00042c0f00034030a01000c507202408900c400380518401440c00000203102c0d04c3c00040d510080c06001140e941c0d02d5030354203410350064010303108881d01c940c502625098140b0741040c08442c0c0b900310f00c05c024101040c518420728a0b10700100182e0030700d40c41c1d1840000c804402d20464990b1442404045054242420308800340303801d07211618012417600c8140c1820740d41c0c0c400000180340e0700d81391072018241100e281f1410092 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 540460269 1250 540459019 540459043
    0x30c0203120a18050619050d0605130b12030c1908130e011e0f030303020304020406090e0a050c04021201120c08100e010b10050f1809010603021902070803030c0309 72
    0x400d04010b041d9008801000c0710f0311080049040d90380b00c1041007414800c801032500d0100365280a40e01e0380380039502030203090035405000111555104c0204181000104c0202c1080e075403111003c81c2845c0c43c01c5020100d1200070010f49c141084031014580e03032821280d0041205680e0340000e000c000c0e42004646a0314124060001401d035184005200300f00e0a010700e09285803450410810040f01d040d0800c100e0700e0007034220070390503d103440c240c0003940041c2090381c000361629808504002070340640c4c10110005c20040c201c054a90500905040f216454503224a004201945c082d045900025042d5181690344088405c12881e02c0c00024007640c1c40b80c80d041c01182c480c1407040350b403035000030106000740009024103c42e5400700511181d1949130100414010307c40101101001009819040717210540d940c030740c410790400501d1004007680908002600098440c6c0341100c4029541903249030790000b07040a500701000c0d1600c0e804010101031140c400032002070020b0070200130980b9140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 540461519 1250 540460269 540460303
    0x9010b0706022802061b070809040f060b09040606050c060a02090d411506130e07031b080a02132c0615010206130203010b0901060c050d0507080304030c0203 69
    0xd00d0f40754180400000c0504100c0540540da00094800025080345401059102e80c0313640741608a07039514409400050f844c90b040395032124035050310303d494451040034113074450407651174041440401c8250303852074105104004080c009211040000240f41e034110b110400b01507101c040b10030200310309050011010f00303612200d444041840094412194003100040b500ca105403410303640440070044e0b16484c002556121f69442940902c40b61881703900520002c0c920000c14400000003c2643c990300ac0e00341503504024800c004200c0c00e00d01d10464030040c203100381000da1800d241039844086040010f8007031026001011207401e4250302501859400d4400c40128603130160780c0030388080c80d9a038000301c5031280d100070400740301d200c101074004000305038010400317955040c2c180d500311001603030b08981540d21504014110361342d4120b00d40c0070b44525903034122030006605103145010803410002003800001c21906020038600c0d070440b54020f4042c2000d10410381d1500c0881c0c580303100140c031102c1078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 540462769 1250 540461519 540461557
    0x7030e1e090f01090b0d02061b070f1e0501030b0a030618150902090f01140607060f050705031e070503130512160c080c0a0521030a0c030216030209010b070602 70
    0x14030b002030103034140d49032a5000c22443c00c112044c09030801540101952090342440a1200c01070680e41c0903582d81442c8007a00c0f0543e40da400302c0313054220580c00030480300e006020083c81580d81c500100c00100024a028080c1603000d0000c180c0228450001605051301c0d2001000300c8001d106030000c0f800d80c4201060b8041c0c803040d840d04002d10707001c0f0089101c0c1c014030300418510045002d41905031749840380203800f8274000c04200440c641c090001100c00640315000189040caa43c80303a079116142984684d81d80b450040e4806021071806490380d0062381e4501c2c14071045d99401745c1500d03403212004001b0020600c0900340f45261200c40190044520000518500301080142c00030040d644101c3c001154251100c0607181c40c3c00c4460009a00010202020403491902d00d00049003801d5400c442000074010b000c4031030850340060280408076440320240700401d5810401f00c1e9041c2180b1007201000b900316400142150410b1041c181d0b4480c011804000b07020856048075440d81c0110b41c40210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 540464019 1250 540462769 540462781
    0x31903050403120e07150e060703090512070b0a0f02010209091009060503031927061808030306010e060a03060815090f03041802031302030a1a06040207030e1e09 71
    0x180004450850006103c11031030628010b0b640038a602d60340c500e402800310681406003240b00200102c01510420044115100c010f403510001459070f18041d9844000140c142018442410034250740324807554000081017140c804d2020544a00e010310703180803540c812800c07400700d0180c05844401a0700829207400e00c0a801c0100c00030303070101c608142080c040175954500300350716406a5100c60480c5a5840703200c00c075441c400c1000f00e140e980d84441c69000e07401c9a94118100050355004a03010030749c9150030401b00c4030460070010041074044015495032800c0300001348103004040380e507401800c000c200c030024180070703811801c041c184100413160144ea82c035080e80f40c1180182e41c00b510b00e0041122070030b240c6102000715801d9441071051030f503180c0b90402c882d1000394002090203107220650320400c2c0c01643c1c184201c1c0421030280d400c1c519000b060703510081100002800030791003240304100e003c2c0041e42100000100c00030484028071000040d03041184100c07235843c0003070b0340082c1003010411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 540465269 1250 540464019 540464021
    0x302150c060f18121614030a0206010303020c060a0c0f020103271a010f12050309040c050309010b030106080d140f0f041e0308040b03042604081219050c031903 70
    0x100c80d605250f81c0b20b5441c48080e1502c0d4607140b1010040c4e814040c02c000c0301621406500280820318810200c0d07030381c0e280300e10350107608641050070b90000581060004000b816410420481684002c603115132818401081c06400014400c2d0002c0464018074490825a8000c2e8000c40702e00c0d900d4018040e180d02d07807888075092015140801c81ea0700011781000c102e2010902003460585041c100014007103400c0c490590351011425800701c5d144e100c10010121a510344d03000d41403030b007159529103a840c0d040c07100105081d01c01d81c0740780600a0789003410411142800046c120b0240110341407003014203e100001c20110311030f50610068201000418034824851100240f00f110036540303000644020f003852400003444d0a1201400061040c4814031900103088010f58100d4840c0501900b40e02c6a00c406c01222120340c514141249000f1404003e01c080901c03ca032500708883d008607141a90a60801c0940038a0800303000810130046008080840104111015005510840c40940010b448010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 540466519 1250 540465269 540465271
    0x120c1306050102060903030408090d0507090c030203250e1009120b040b011d06010e040e060117190807060b0d0507090501092406051608040e1e07090302150c060f 71
    0x14018840e10001400305d2034080180ca000701e502c5415a4603180030a0200f154410404a05071490b000d00800003030781482c24400c00701e012185403030140e2a4a001c42400c1a1b03100d01856541041c0903024140c4040c1c1d901c801031004000c0c0c111202814010003071000c803600d805903000003941000900c0e04800344940780c00aa4440c034895900c00c1c10684c2c0700c2c041401000004400b416003001d504012414641c0260b0794401e000748081c000184a40c820700129140410070b038030403200301004001e220700c0301c1c07018454991219080c02100c9003d81995032440254468000302400d601d686090901c0586e403102480c1340c4d0f40703421a0890344601e48611090340200002e1042440c52880c091411000c00a040480b0070195500c3d114810302e0b5141150a440740e07803010f0010108503011420500c00580700002a01c00303024510382d03015191400160320030111210010100e00600c0c0350041150003580961004c05a1b5030540d140524441c44550842c0726005114a821660003110304101c52007086c40219 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 540467625 1106 540466519 540466529
    0x307021f020d0c032607110a08031506090904140d0903111210020403050705030606090105090103080d0f090311120a0f0e031c05040e012102120c1306 66
    0x5a078100d0901104e1781c080080040c042140d9109084c06100b8400200070300d51515242c50380150b40c00300070002c0703585404520140009484d01e00c180d8050050141c45030072507042518000380600458000c0841d0740c80303080e0300c0710304961103411010100d80c0c20150b540c5140012100b072000c2040c1d548007410582c0704070311401c1c14442061000380011801807000c4c09a090600040504242c00504014840c1c260f1100501c07846c2d0f9001e403d43d045070782c4501602c0d60707070700240c000c9000b5042403041c1c010030300c1c5004291803d144d00030358255000c076070710f405a840c6000000c40070310090140d440d54000160000150700e007018010440022000300080c11504000c006541e0865070092225417200001c2010500f00002540f4010301030140030b11041402803188800100d60f0300c0c0c241c66001034401c594503003010040d103005020007411910040c1002c4600521070368411301401c41c9100d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 540287769 540467625 := by
  have h0 := BRFrame.cov_init 540287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 540287769 ≤ n) (h2 : n < 540467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
