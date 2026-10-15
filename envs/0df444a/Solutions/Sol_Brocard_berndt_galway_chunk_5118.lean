-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:48:11.708345+00:00
-- url     : https://prove2.me/submissions/d86e062f-be6f-4bf7-9420-bb368c1d0530

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 920323741 ≤ n < 920503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 920324991 1250 920323741 920323763
    0xf0504030f120b030c010f11030a11070e01050d060902040b0d050601091d060f060a081219031b0503070e03070801050403090f06052a0114180102130e071b0807 70
    0x940e6041220740d00d0003084c2e00350348014151051507010301c0741100c10001611f0450024a010300700070341540c00540403000465602c1506060001c02440000701400c9040c410708415172526001900d0072083c0080170f0081e581e107014050654581d03410a000503c8050301224840840745810f136075560092107402500c6142000307a2070780d440c80c070040303a40c07006030807009118644600661190300391000d0040d5506c142103039030004480a0602421a4442e6507505840c4c544040310365200b0400003c000710020945003000e00c2c0300072092040c4c800311545092401944030340c0e070b1082c103681301020781180301d03854440c1c4040000c51100540006200342d1290b90b80b1500c0d607a80d8070700707c44044200c1c0150004250706100ca000e0140151052105140d450100c5290360418203140c03500b1111050041102910b4a0080004d14403503030400b4001c3e020f880008501c0d0405404002c0c88040e03550250043c14624038000c124142d1154070524079810256660011003502854a41c2c840e03408a03100f194088070340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 920326241 1250 920324991 920325017
    0x305060106020c0105340605070318030f0c05100f05040519230a020907030506240405010806150c150c0315010c03021608010b130b030304060c060f0504030f 69
    0x441d41003d18081038480909000141c5c01c00e144007501080c0316020210050480c0ca1003e042c19800304606000d030f90001070034200180c00906a4150440411540c1c840d0002c03040001e60009000c214090f46180008082070b19151160602e242c1148060b601d82c242807503180304400c0d0313034080340c050392194040f9000044404680304041c40d903540b0180010004010505c44d0400525840660b41d41c07110544421204907800038070343d050240d0b61040081d030381e030080210508009264016440a5941180b9042c440000c805c2051140d401018108200341c40400d40b00c2d00e407001c280483c01709501e40d10303465400248540366105815544905034002c1000411809000c4c8004c880c0a100305000c0a130012080d03c00544117164400411801c61080040030109100190300340009801820000301c1c8448004c01081076494402a14004d03031313480c0c200081483c1c1d400100700c9003140d1603410149004011801c1000c0201100d1900d4000c01d8288002c110070140d1002c400000d0450035250702d44080d00e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 920327491 1250 920326241 920326243
    0x151f03241140051005210a0c0819020c0a020d0602190302270d021f020c06040f0905040512120703240618120c0f08120d020904090516030506010602 65
    0x1e9030080c4900c1070b10805120505200031080b81c070702a10b003001071501d00b07948090788103114000000c1843c445400c0900c260320150340241002c403062443c01c1c1115007445503402200c000388580ea0441207500103020652048103124500390b0380e8000701504030750300741418002c1c0a54001062507440040448080701c17894002c1c426583c00c4800c1d04600804031901c40c9840404820002c41c03258441924020000103955240008900c40100d00ba40258000c1400d800b9280c407002d94407851152206010a20040030350740d291104407032100360085466100c6051450038403000c04403412107801c00050b140011401140b60600810156070204004c007200b03e11152842c8059034404405a10410200080e920030b40c0500503130403080c00c5041c0000da580a001b100c18800d400c00f140c41c034020b40801c00881c2000d00c1c2d040d004022a0003c1d010b029601a800103043c80f407401c01000e40760380410100c00686440e484091415408403c48045040341c1c442801c10001c2480126514800c0030004102d03584 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 920328741 1250 920327491 920327587
    0xa1407090b06070804271d070503031216180603050906060d08190e030a0506220b04080c010204270609110702130905151f032411 57
    0x78008502900b040d041800000708095000c809810300602885c00c080070910f14450307044950b0188405007c4040390000b02da0030441c0c980d00980c42600306002c51124210b26018040c0c1c8202001c080c44440c0c032504805607004107809c003114205600035013012030340b260503902440c02913001004842c02d9039906070400000c02810100200b01a105000c0c0b9104d242146420303c505074042e0030100d80d05007090003c6840c0100b900d400f036030b00e64490414056a403802d980c000340c402c01148200d8804c0651a25086d11440024000521000000030b418040203029410340b800b0713140c0044090854260003042000c2e60041e001c04002c203500c0c04070b000642d00380d14031882042c075102070080344c00c0c44065000c00810700000c40d072031805070f500c1d100d0500020b1028400403024041001d5451000e04060031426110001c114000b03400808102d42840440c0d00402c21100c80c014048c7e840b000034110301d070780101030420861401c01c5150080f58a061b00803040540035150545244480101740c00d10303040c40c034044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 920329991 1250 920328741 920328743
    0x180f0b010b04121b031407030605180304030213020904050403030606020c030601080d12020408100606110a0c050906030f06161d100302090111160e010b0a080a050601020a1407090b0607 81
    0x150f00c4410320005000c14540b900c86550045441032510b03541d0b11a100c0d200301c0001c0001140d00a02c10a008002e800d20072180c0018110321899071210400640540e00e11850101038800c1c1d980581204003000c1e507404851600c94007902c28805030901d0b2401502800c0c1902841015002c2d402041269040025105040380e46460017002d07a40034100c4182c0d000916000400307020707034081002180700c01080240603081c0c02c2d0004c4c0001c565282c5100140207a400340031074041c0360400c002e0746004c209a12244000d683e03045078007140f5500c03040d0000c0d15104240000c00c1c298003031142085000000d080c21141250031a072601c114050350344180802003c6865207140e03000c032039401204c1009129901400c00b885060500c1040281414202441e250340d00210501407045200203000740e81c240900e003401410091002400d000a6210240000d000141070401c126611400a040307070303208010030440140c0001c0800911140d040307003542c60340d005020b480440e40c01c004240002c0d080403404c41d0300c55 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 920331241 1250 920329991 920330009
    0x20604030903120c0209040b090c120c04050a060918050c060720010507170d060f03020609012f030c06010e0103080706050a1d0c041a06071104180f0b010b04 69
    0x5402c50340c4941c00d07803407440e6409040040d140c15040040e02d60b840011f00460060b100c00d5084d143c04041b803072400d05041c021a00440d0b05180e0b45a1540700014100c0c2142d500300c4000c18150b603110b030707090010300360744e40109580c90030070020020000303481c01516a101c0c0501c0c2030b140d80030b840b0403d01c4a13601c2903820043c40d44102c2e5941212500e03100070f074004d40420501d4454501500d139103841c840920800070407104907000007003a1740080c0c0b941c81104001c00d40340e02c010510620b1a0001003081c040c9032085810f0107034100c0c580b10000380725190900c1300d40084990310600711070350001643e40d4101141d94819445030a00100d420080280c0150403039034000c000768074013450703035543d0800741c9005004001c031a80c941c03540304c21003c041940e00340c14282c1c1c0e6000308201014035081005503200e810307441c40d40510900340080640c40705c00440c0ea040350407041c07446d00710184001240051480c10310102d17040300781c182c400301001000c003009120720b401014205503907601da035010b01d032a100c3e9101c4e15000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 920332491 1250 920331241 920331257
    0x40f05060f13031a07170a1a090106030204140a03051f0204150f27050402071403040b07020a0905330d080406090f0807060503040507180b090702060403 67
    0x10618000009216070761030444107505141c1c5400c03456281e1103040d08102e603107001c01116031503920244002160300464601e40503662800880e5414208400a03000e02c42c0507448440c01c03000745000c000c0203c081600581039240540e0f42e4607008000350024002c0301c0300a80c1e22184080c1e1868400b245105585e000307030150200300c07060241e046880c2c00c1e0718016a103c45c1c003400002a060340704c15801c03410341c080780c443c45851503c08000901c101e959481101490000300041c0c2e0313145d00044a0309043d188103030740045e40e50780641401c00103a0002903103800c0d9031000160214480c0017204c082c03e88030f80f0035a08024100e031580c035011f0645404462101e10038070103003540c46e040440355980b0501080040e000c0c1c141101800c0205041d10314007c400c2e50100b100060800400d5400005030700182007440c5003031003080c1070007402c6480c2c1c01c10b480380302c08014002c030108080c880240b040030014000b0812008482040c0f0840d07030003070511000303294854540d00f00029001800403800c14401c1da07041da12009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 920333741 1250 920332491 920332499
    0x603101104050f0d08130311061e0f07140115080f060604091a04030305040309140102070306230a0903080c04061b060e011a1507030503180309101d06040f 68
    0x20030503143e800c12980054000414808100008020400840360030a1655414114207080d001201034180850154500300882d0700c5600b000c8400d5440d0901031030b00343e030365404200038048840c028048040e001c1c14044010000340001507210003203c81102e0000a0061341c0c59000945035840c020b0075144079005500000c05030f24096100b44040751149003004858084294414608403044600b1000300343c0d12020301c0240b5030001c1d030400080056505240108402c080001d484030010f110003840c85403200500440301a00d00144c00c884800d0040d02c02c0d41303281a070600c9018002c40a800c2d40403859100110742c03203120400c21201590840c0e1919520700b03070b00300040707107240140d800140c50150307452560300f20549082c082c81c00b0704842a168109010940420071854140454448180c80c6080103542c00194221003982d42c0005420030b48000307402c00101c0c1908510540151b42c1c0c4c080c00740c03100c0e02e04c05074102c241d014036040404040003028101d4010306c0501c1c45207005120f20041e654078104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 920334991 1250 920333741 920333749
    0x7060806041103070e04060509070504031104090b0903040609060905010801120f020a0b0c1002040e0402061803070902030a14270102090406240f080708070e1206060310110405 77
    0x1641105010340700151000b60700200010036041581c2050019141100507038440c03401d8040c05c1c001d800105c0d0a01d11358103064401030310a104900c00104601d002c071813448101e42d07840e40818050b035003000d00044036240074590140c980d4064050480442c1202c0c070041545407080c80e94000b41c0e20b040e165040c00303900f41400c02c0640d200388031040f80d1403240c9100c810010b03240c03074050f4001091f10381841510b40e0f184010840c00d180314002d20041d0740348180020041c01e5100414150232a8041c2e81c0282c1c1c0701c021010001c0f084480744003040c1c03d4401d0010029203003080c0c1e40103610a1814810401152800d40c0401052040541c3d815a1280103640a80555a01c06c3c10310001011030500040c43c001804000c9010703140640d02c80400a0b40d800d10b225003d589400c243c00014649140c18100307020250005485003a024146008000000c800034003203500403407420b80d800c207000f880c0400400030002101c0c2d8462089408c40c0c040d01440440d129250580c0c064129075100c45c540450409041a00780 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 920336241 1250 920334991 920335007
    0x111070f1202060c0727110403020409140604050303060405070c12180e04050c040e0d09031704080114041b0503070b03071e0c0c0b0f1b01150e010f06050304050706 72
    0x5983c4201c08009000b1088001c000c1d92004042c00d4020610941d0601b8046544110700701c00c01e100c040c20001700c1800a28090111002e4950417180003500a8407030915507002202c4002040c141d10541d0288024004000f0241d4454003044401b80116964280111660445800001d0100c0c43c00349084903400d02504820800d00300070b0b40d102c40d01075510603490350001419182691141c200003026006814079024a92103c82e5140c0240504481100020445810b070702c0090500111610140840081401100c0c01804503800a00001c0f0030040780d01e86601b0241c03411107600448024202881d5038103a417500032942e0040140180b036140c03010010a551004020b00100100740c112415103000d250288100040240da6035100031009140150302c101d02a006640c0e102e1061003111405031542c000c40d482d10180031100600d9000d07c04845000d02140c000d04800080d5075200821622036240d6514100c0d21407030407820000d0790703075a01524144410750700500103402491301481042d0207030000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 920337491 1250 920336241 920336243
    0x1b0d0c152a02010b03010c11060f060d1118040809030705040506220b0303070309030b010e1506210c0a030501170c1513060905010815030c0f0d0203010f050103020111070f12 76
    0x8504074200c1000242120504201c42c0041042004546808c1c1420811144e0019180445400c1411300300005603842c0b000c2c8000402088070070b07030101d080c0c0d120003d0743c881403207080c01007802e40e040914104500e50440c0362301c98000e11480d040026949000c1c052a4090030000e4500a20b00c5c3e01c418512003000c81543d400f95099868610350702058608100401445010307a4074005410b05602e03000c081e400040c2d20121403074040d001804520040420071012801e0102c80300d41e5502004c80c4803000c0c82c02c118a030710820280e80c104000c965030314140101946002507408001580e00c40020440c0240ad0b00b000c100301d80d01c4540010300703078100904503803100c0042c2a200c6041407000403451003c01416080741e400104610300402503540c12101c2941c0200b50001c01c6c0c1e092925500200b6503411b11b501515100d000321101620941e01d410030391001c0c281c1c004e402031001d11503c41820303000d04403c1c0700890003c0c0c0051440c0c1c40d0b00202044e05420354002c10045040e4070b1422003c1c00301031100c900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 920338741 1250 920337491 920337493
    0x5041e02150a0302120708060f130e0d0e27060d0804030602031303030b031c03020a140417070609030b040b06150304050a020a05030a03050f1b0d0c152a02 68
    0x50720301442000c980241c810100e407a5009a5242d100681d11042a840504003c050050305014030078150394048880400c0c00c0c06480411001c0240384d030709805031081e00b60041550185c801814009035101513050001002901c00c151280344d048028014603249290744404007203482e021503050318000d498917021600508010b410140c5a0700c494040f039200340c1d0328201460851150701c042540600540e030000c1790880161085002d203042144415510480702410140d0009500c41c4c010300412070184900d04040d00262980e40f120807140341c004c08501104041d1003190b0002402e903124100c0c0005036684450a24496200c50303464451805010300259440b0550003080d00c00360700b142011303501ca140141c000381104071290040c03241c4044990051030083e0031062201c1d0102b13400a08841f46042543d1500e42d84580c1541110722034150400c0c103448501038101c1059195601c0801a8542c1c0c0c0074800c070300515584203034290110f90641000540085116400a00601f481c90f0651031050040c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 920339991 1250 920338741 920338759
    0x1e07231204171207080402180705031603110a02010509100c090303050306010207090e0d12112b06060f1202070c140a09020c0d0210270602130f03051005041e02 70
    0xc0c0c3c500010030002c403410000901400b00b00800d500e0000300600256102c02c15049283c01d084800a0642c40024222802c2503c601a0311510324030039408080b141c504000030340d072600410a4000e010f040d0070b590070211441001d17440807424495204450000702032344c403507a46051440d94260b40b19040181958158000d1040000b00c00342c050264400841e03a4001170411512011000340409a92000c2400b5440c030701403402e4000c1e40a10112214107049212217550702c0e03001e040d8400f561540b40000007545051610001d00182c01c4048000c40c01d0568035031025a21034108940202e005e4683c029010070700020040200024030b06003e031a04402a01d03c400594440d413030f0710241e80c0070100d01780e01503114070b101900d62366062005d1070f8a111100000d00c0410b40101040c201510011118021a040650386900300040c640c1100d40f03c2e02d1084221001d0b079901e16905506400d540300c20380e80d60290a46218141c0001c0c407815104a80c003840b0b1005000354403200c545070300c1d41040e0407600500c0d54 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 920341241 1250 920339991 920340007
    0x270f010e04031d03010c11010c090b04090b04060b0a0305100b030c0d0e0a0c0b0406021203011211060c0a1b050102030a120b0f0306040f02191206051e0723120417 71
    0x38041d8a0407290706d503c481c100c00c441e07103420705e00311450003105104120100c2c9080c01705d510a08101d9003102e1302c805000c101048144001002401c1907070181080740c0000800060103078144e08450710445031030418815440e501e8150310003d11044884d0103040d50104040c26000d8025880186003140c0c0038112120410940d44d41c460098850300100c4d05c081c3d001c00d082240e65410440c601821110740100c5045514040d0541c1ca041501d0200801d00760f03207904010030b90b4a800060341c3c1c1c004103500c04c4418450a50411034184028843c0c101c2c01404a5103002c52a5400081107440000d5613568000081510081c010004c00c4155442603100d460250359034050340d070400000c3e009600075490a0302403010f0744100b18024003c013880b81c02e5155800001c004d800c420360a40c120b4280c02190200e01a620440c12411030b4044401d212454a1400c041c40540b5921507a00d91005852002c1102400d9045614100902945113120303050080c0c100041c00040030b021051007034410300d62106040840c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 920342491 1250 920341241 920341243
    0xa09030f05060f06060708090d051609060f06171311040212090609010e1b040f020d020c0d031a0639010f090f0204051302270f010e04031d03 62
    0x8484000c0d1810382c405020302040c1d42d25a83c1c626041881120400c0c40d21406a40303c500310f001e146541403007150340068072804e10034180281c4501031003880c100c0b000e480e01e50140380d00402c0140200070710945008808501e450185410f01c40074001e91843c0441d982d194004200c0c3c40c00c000310100c64489290348003c040361118005003140114801244043d4070300b400d074042c42d10800400920310343c1c1c14402c02d800f03882c3d40070035100303150350003082c5d4841d00488820100d00581181000f0010381880022040c001011a40c050b07c134015950054135400241c404040b8159441181a10150461082012010b14203103004005141c0025030380034800e00044201c825144002c82684660340001c0001c0344070380c1081c41703020503002c060750701000920320a48440100d10b402e142c0080c021030b503400114440804512503810038a0b401403030b41c848054a01da0351208641c81c2400d1100703400b01000800c00145070901458140e50300311800b000f590f61640c80c100c41d0713401800101c2e01007503901d00f240c0c6000e0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 920343741 1250 920342491 920342513
    0x304021302031e070c140703020a23030a0b010305060a140a020a110109030f08070f0806040203070e03070621090209040803061c0507230a051201020f03240315060103020a0903 77
    0x1503a0b1311074004111860034038051030ba240441004547c1c200702002c0c0010b82c1c9030b58a070720544003140310030b240611204610440e5030002c9081c2e5945445029058010050940000d40c1a40c2c825016607425840e04800a000e80e1119000c01c80c0b03580100d4006110100640c5c00780680401c0b9150440441c06010507080c2103400500c0280c0c0015110194610003e4120f060150060300c50310308804100c2086100802c0c419024001c54410350b000000700340024420030b158081081c00a094850055845201800409041e00784044200c40100c055601c1e04451096100300758000c1c0c00524583c1c1c443d1b40d21181c0d98802230580b0380c4000341e40c20383c2c0d184100c064a0303185008d00c248002c02c40c070340c10102030701400007041c52800c0c440b840e918040b1079a600d0b6407103502c049500a4811700a52230030b00300424007a000349409410740382008400c00c40b4000c3c02c04c5600380020040444001020100001d05403621100d0700341c54110140700780415000d501c01d41c000e10200142d45000b2001030f03107075030310006005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 920344991 1250 920343741 920343751
    0xe150f030106030b06030403020703061104090219030b010e0303030105090a02071202071805091e21091504060212070c05090103030206040b0a0c021905010b0d03180b0304021302031e 80
    0x29004401031004641612609160160480e0700340e0551400780e038003c3d40e48005010082c070560300c2d2150320281216000c1031300d010708428801903454044a47d400b4408190407a060b07400242014041d18075940658101182404060059850745c5c2c20300c4240040000c003d408864041d6013040f24001040c4001c2d80c2c00c003014241d034058840f003880c108120a241940c8004801110314010134000c1c507030000603503050701510761340710156120055100c40b414003888040c80030324800032600b0303a19200420700c010206104115203071105a4031009402d0254003030740c05400701607400f9200842d43c20380302e0f4003c0c1c8030300c40c0318690131161a80c4910205003200d100381d0044016a104109000400510408407036000300803440401041500850003595500340c424140da486868000754814400290810124104060611034001c0034a24004003005d134a03003644c0c4c62036035500b04046403620380b5004403070056800078005014000303041c80602c02580081c0001c2c54003500101403155070710324000c03003c0c825 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 920346241 1250 920344991 920345017
    0x3090703080c0d08010e16030c0c02060a0c170f030c03040507150e040e010509070618031a0627061e030109060515030f1203100806041529010e15 64
    0x1d582c070443c00360034480306810000403130400c8000c004150015030303022040b0111528012407884c02c24036054500074849000039401560003c2c4640402e03422038585408e07140300304508190032019070140c0b00b01d4028001c40c06403103501080802c0500a01ca00a0340d00580140140c854031550313140c440e04680d5021400c0408204c51018401e403070f28151040c481c0305030180000780720500d40004e441c2d481d12810700801c014466002c0020001d680c18540d004c0241d40d1020130840060f410190361181010201d554510909065075441148100c03805460a200c2c00c90784030040584a0a0800602d810003034050030421041c00c0d00074015940900980c0d43c107030700070b910018080c1440c054420020340104800ea010b584617024009000000040c00c0808003800c44001b9142d89400025502c101c5035a440b43c52180300d1309061005010180c1803103010740a01000400201ca408210a2000f0400c0c00e04440c030f0143d01c1c40c0349522540243c0802e10400741c02080510a0701001c146080c0f980c200a0b4122a9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 920347491 1250 920346241 920346253
    0xa0f030b06040c021b151309050f0c12040f080706050f011a09010c020f1c030e01030609050906130503091507120201090f0f11090a0209191a03090703080c 68
    0x724149807051074012500343c80035242c1c2d103803004040e80c5171802d00c03940f00340513219212401c00004408425240c003034800300d03003484410b0356448901014281c00e0307821000454881e4003090707284c0180802c4a00740403a158416242d59280e40700d403c1c03080a108001d0390084020000c44d00050b4051280c144544400d035a041c599505050042041c100c520141400342913080254500e83c2e03030002f00100f134076641103030000300828101000c146280c5c11512051504c40d184c40c0e0300d07410180c02a5a401c2c1c101400e9900300072150b03403450641d080e03c6050320304400581201001c100f20b03079540020304103594068400c80349405141004205402c0380810179110b12480881c1010400528080d04040e0001c107200034040710007903455600c2c0600348490000c0030003412410880401c0300c140100c64492000509070340440c0f8052078040060340c0a8410148219240c14140c4c48034035441d00e84000b030314454600030784150105807000b8003d9001030a8503601c0d22502d580000003607840350081c003c5103030410180c22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 920348741 1250 920347491 920347501
    0x141b060f0703050919020d0501020c0d031104210302150718090506011b1707060603060e0105010b16020102120f071a06011704110d11030f010b030303040b060a0f030b 73
    0x394900c0040e041104050038502400800c20002948194019580140142c009031a100181906040000c003c1c000d50005c130f90555013440105c3d0b41070003108a40c030240850380305802c003807103207201d240500d02c40420048031410f620340216404050142c03283c0101c40d0781045d0620090f1090a04903001700c00652034100f456813220304549500c0c02000541018080c50a01c80c00180c0011058610b05500e0b017a14a42e9000b444461082e1400c1055940221640d0358010708050f0040d22490006071280d904110b5101484541403240904983c0303200c5000742413409607220041c06801541d8280c2c1140300d40105000c2031401900181030b2032490304a0180c0d94007051905801030f40104411034060380b20130b001c00bd0f2503600300c48038070082c40c0280307080b800907130329460b200140b100d17104091900441064010b40401242030f03d039a40c42c00c4105c003281c000c801905c007002d0983e028580e0f00c0da0160000c1c80402c0000d0f1113090101d0b00300b8070080201c0c0784a502d4948840c200c032084d9005440341085003080c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 920349991 1250 920348741 920348761
    0xb09010e0105120a05061f03060f050105180402010f0e060702120609060601080405100207060f0903020f330a0e03072609060319110c03041401110607141b06 69
    0x202d00302403805400030303680b0343c0c1394161035510003091f00e1041e04032a404001c03040302c0704038080e016641c0305a040200c1340c81d00d003104000b040c00b401203078010350a00c25200300d5200c0c1522954403480e4140d43d00e02040d100d000d02101d0500b00405102e8005805008490050741c43c1c041d030392008000400144802d20388010394503d403200140c6080d05005080c2c0510000c100b02003103454403900e0903000175a90399076a1908074020203040e14405000d40c41c3c801603004040d4003142c1c1140a4415104489081c40d04500c120201800b0903004404c0034000d030001c4a42060303071003500e50300c1060361b440001c1d9000f26403080c500715070202004540d048104001503207101c050020b0865100c2c1490001803d12030480041122444007400d04110f5a01d840c90604080c1c0d495044880115640b40d1450748812144050998940250160151445049401c000c007948510600e00140304060001d0145803a04001541d00416117800b44c1203a050400800103100d0f10728201c01e0702c0c1d0300000c000f04140c0ca030200b211 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 920351241 1250 920349991 920350009
    0x90204270602030903042103021606020c0420030c1306050a21091e060f0b0139120e0d050304051c15060510020109240b09010e0105 58
    0x392542444288180c089404500c09003496000c04010ba82e610380e43d10051035800381c0d6024000e445c1c285000070910010710710505d00024420707003c944031a9a45c03900003074030301440e0040000580c0b105c07410070160b2070300d0380110799000136440345690758583e58000610a5441145d500402c2400002d00404081c1480d0750503009203542d2902c02d007030944060000300440419046041c2180d4191181c01401502d0360006a01c654007001a00d00ca103468904180b4880d40400240c806520302201211100854003452580b001d050703441944801601c5049050078480d400f00410310f402083e4203125104076450103400c410f00a232520a40d00c0e203407980082040c8521201d00c0e003c2c00655007000001030000043e075042c0d541c00c40d605401203d0710390211340802820030001d00f2a00305072a828201c02d01a40c008020355106440d06400c02044281c16800d80d090800f00401a000d608070700d400c4070310a043c8078040421508004548089028005a940c0c0e0003038000440c404c20701e100401940c80c0503c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 920352491 1250 920351241 920351261
    0x5040501021006051309050f060103030f031409030304030c080d020d02070c120b01050f0103020d0f06080d1701033306080607030603050705060c0c0303180306060a211410090204 78
    0xb043c802e0504041c0400d100c1c54001d818401c600d519046070b0020000288640c0300b03400c1c801800c8800940e92418010142c680c0700f00031070f0200786060340309040000d803104c609210312034620045245803540d5904490f81c1080c04d80035038400388240001492000140010035400d01014009a01d42216080c40d41c85618250310004800c60b85100310340003d01c0c81041a411210200e407030340b03992000c280c0140d01034480c482d000183d16103001c80364841e8992640c00001a64409401c842810b0243c05c01910800790740100f01041c0c0b40302500400000b03110000210b0340019041c0c00410401e0850414600842001c151070302e01e03a119203050010100802001c0c0c0e0203d92450180500d9146880d031580b144410300820f406500001a6055045020031900f1741c03503400601180c2eaa18510b5401f42c0e0790b120038400451080c0a1341020a40340c1c80c1880901d420341d0311aa00301580d80d801864a00c0c01e0482109040703c03420b9401c503c41c10f00c0c11051042040f501910718020607000d0301441000211858014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 920353741 1250 920352491 920352523
    0xa0f0b060d02210d0e0d14010612060501090c05070b0f130b09031207090b070303050a2c0714060a0804020310110405010201060f0b1c0612030f021b030615150a0504050102 75
    0x1781d40410703510501c8000d10319401041000070f00510052950140c000d503000a071814444255510030800d060b80402c0c100c0c0e200500c10030106650100481d2913114480014010b50070b580c011889104001d400070380c004003001c040c40b4100703a01d5943c42e01440d8085900d4080c541002c24004842c000c109492980410759241070751400f0304000403810756010700c10001e030406980d040080c1200c1d909a01c0300e400c249034421000034445201d42c0c4000c2100a9090701c4540780900321000801d01900c103100b2540810040089013032510f038503011115510001c006076450b2081413180e000b07100184c40307060340082c051006c09640300c1c2004006804c2d0380031030340014116a03840314208031054021054612840c503403804118034041100030320010301915040000c0f650064205401015040614a581320202d0340949035140030700c3c490450201508482641c0503003050000031341c8641540c403131394500400149120000700c4070b0341e80424035400a083d00d502213100080c0038442503804120740e01800110722 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 920354991 1250 920353741 920353757
    0x927070603021209010618111b011b050304080d0506040f0906061401140a0f050c0d08070e0108101502030714010603020909120f0703120903080a0e0a0f0b060d02210d 73
    0x400c800d080821a04040c0c42d1176580d40198800401300044410303032102c449c003030303461021451f2000d40204030784501c0c02d040744e00a80940010f0b074003440a42e842942c000d2102400c000c10f80c050240900402030189600c82c0da5060311901041e11445030246003800341c1e0300003401038140380c500c6040c0c0450f08800c605100c51162010503270304003c41111441c034124a0554164003111b070080c1c0355030181030061000c90281100d072416195000d1482c5201e107503165116514801d0343c00040d100000c040d1103212200030a00001d012004103030280e802e01307207007903c100c80c50800c89480b500c41082075480c4052007030751940010410b5280c8690300c2c81d085070440c4c0c0607100100ca030512811f070a101e0310707065009070800800c1c0c4000781400754000800c044c0f520082813100340311354600242a80c008a03035110300545890b6550400d4940011070004250b03101c2048295042c1c91707222511046002003465038403034900002e0100507265000040000c0c989030071800981051a030480e820551107002140410040b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 920356241 1250 920354991 920354999
    0xc3b100c0219030b13020a0e07020a0618020609040e0c0604080307050d2613081c1a0d02010c14030f030106030f1a09070c12020a05070902040509270706030212090106 73
    0x144e07a4284c000750368414203010499540f001c00c80d808102d03030200811519080c00c110401c0d4010400000151041e0340401c030031480c25440d0a080312154401070342240d0103005031407582c2030039800700843c14840403c5503111076122000508a0388281c0054066810101c1c802d400c00608108081d21002c103410702001941ca100180204550200312514030103000c1808115040d0180300e1409101d40c2080505503600c4d5102042d9441a81d560b0101c450141751401c2e40300030a0341c2400c0e032a881ca4005204196003902074004465565003000141e441c8103001c048200405001c0000f0b01c41e175200e00000c603860750300d08240981101c0342d5442d0b403102c407070400c000e01810314000359201020038000c1b242840540c81e04801190415005840104021181986034107495000910801542d11400171548000d48401002c026400303130780301d0140c1001400001c01c415500d00e28821038041051145511041032100e40300345011026484800800e03800509412400303402108982e12484480007400042d140c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 920357491 1250 920356241 920356253
    0x11040621020a0c021915050c0c0d050d031515021c2105071b0b060a05041515020f120702040501230f040b0301090b01090c3b100c021903 60
    0x990024811382045c10f00c240210449071100020309031018003038580c56284074000d0040d50000c44a80d40c10711544800100c21328141c1c03541c403103a40c2e122002d000642154a4281c010b401c80d0008486d440102d440c0110348840802d00320f8000c060158000c004002e200712168809a107603100c11f07820001039aa45501c42c1c1d491b004100c400d01e8201c1c0c000142a85c2d038503403c4a20346100001c917244190081003200500c02c00360200ca028150440307580ca040c0790744108200440c1c0b030510101c101001072100030406060110040009100c1c24019107082d50781c003005a0b400c150210742e818807100e10214006055060521a030b90151181040c00070014101240d2141e5070026142a10311541035684204410b80b03e5800c180e051a202074000c5c401c130380380e600d44180e5105090050000007403070840d1548606204030a010700d90203600000204003510021951581d6680200c040503000c0c0710b1101e030006423210314014514502030799070540403818038810001002040a00d0701e4900c20070703000500203c1c407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 920358741 1250 920357491 920357507
    0x5190608010b03040c1517100302011103160b040302070509010602070e0112050a060b0406150503041a011211061b01052509061209080408161e03120311040621020a 72
    0x42000c0c441b03d40c007106200d0490b00c940b041c214103880c411186092280343d510800c400320940e4800d03254100707190500c0707418907900e0107846244103089904180d8040440e070003080e040d4100380244140c0d01404d489030045a001e0100381e000c1001070f0301803c0100010680100c056002d0440384040c801c8c030b1022074682a9548800c00409418141d80d42004c070515581c2c1d510500060807460103240c00e80c4d41140000e8500d4208403030036a00f1415412034000c07454130354000a4184c0d900c40e01002d49c000040d44820b00c024001d600d101e0313003040d020048a031121950314540311032180b60100101d1949070020301d000b034030304080106213602ca0855440041c001d40040381903043d5205442d0510070541d90551800203402c05d510003a0000600080100ea00040840c1d440490b04001c01c241d500960f950560003810813030341085040003480c1074002c2c00012810420000c1c203580a180c00300303103c11036008500e040d0307100743e009801060310040c5010210340d64141c6820172140800d070841c10011a520043c045103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 920359991 1250 920358741 920358749
    0x90326060907050a110f0f01180804121a01120212070b0f0d06051806270705070302030c07080606040e070506040303051c052d04030e040506030705190608010b03040c 73
    0x7010415103070700e0348a11025000d003401041146d403802c0510904584407c0711035281050340d401c015480500c000b1041d41000344070b0780641054038081c9400004003d951045200f21100d24100d00740f03228030101c2c0c40800d8040c010404203004019018410400d8401740c100031310840340c20034181005910510400d0b140c00c00b1220100d01e83c1c400321850384800400350340d004180e00c44010300c101c0064590b622429886501c0980b2820155002c5181a00c0d801040300740545000361101c0024400b144a0000741102c2440703070040b2414400200d0301d49040210341d0300155226030040b0b0811040d840c02e070160b8080062148044e110140c100004585248110701002d0103000c0000b61555208400000b00800c0000c4000e0801c035504003840034280c01910700030351401208031039038529128a83c02080d80e0260f46c0c141c0700e401d080748201e001d000142000030a080c0c3d06008140c0c00181c43c0d2942c45010b510701d6440001e00d00342d2820220044d00a00043c1c102c514881e400b402000002004044101c082d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 920361241 1250 920359991 920359997
    0x303010e0f070e100504030c0f06030b030f0606040b18041401150e0c090303041a0d1508060f060301020c070b031e040314030a06180b151c110409090326060907 70
    0x48898074019605c41c0705a52000302044120030380020503005444080301640c1440e61306012402402041607554051a502c10840740c02000c04541d452400750302c841c03220000500150920f43c10a840c08004480454094503520700c07440500b03000440a106036280083c0c00c0c0c2c04c91100c1c0c3d052206422a0781c1c00201405200708000130380ca10155000c005940060200c41404200340c0c040020581950300005500540942007820422409049009500c00d980d050801020143da4410000110010203840681c02d550308211118510740103002c100060064a510f09540c0d05107000041c402c1071008281c500c095040105000000358480030075a0540c0705584a1512521351020141c014011584070b803088086804088004400c41c2d00042c00c80f90084541c004d0b203003200c5161901600c901c0007032600c0c00041c0803200340c512a0a50210207548280081642425280c40e0b10104a134841c407015400700c2c00172040c00c601701c01500c15080000e88d000c0c03c92150707030501c14046149010094440d0040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 920362491 1250 920361241 920361259
    0xb0606040f0e0912070c06020d08041e03030603080d0c0e040c08070804080909100302042a0c08070803070903020a21020f040b0d0605091603120806030a0605090303010e0f070e 77
    0x250f00310410104030300043d100041c690b070301030a242842174103c40c0d10402004d070191104244140313004002c000d1150760018211150103512108510f01142c4c0314604a09240e56003c0210100c0c0c00760000c2c05004445841c00034200740e03400f0024020032a4003020300e01c02c5040c0302d030180b0030a070701450407a0401d00e103060415040d1a0703032900c401540610380070719411058020400140c21003004203c001c4038008e0301c0410550040780304502580120b8071031710ba031100c040b110710382d04030f0722800c400b0050328002c8540c01c1c1400c079203a90351282a8800ea411800207900110144150314054403c03100404490710b454640740034408008003000c28030a000b03071050f4180f0000c0034547c0c80e1500451341d005030003440c0350030001d0b1528001004010580f01402184646800000d12601180d00078040c0d03500b00c0c002146030540041c0440e00307020020034040c2c25000b402003820000d6410702500d805451000701440c1c5940c180140b220780300000410b0300d004109005c3c180000103400000c0107915160035501c5c015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 920363741 1250 920362491 920362501
    0x90b0303070f080705010218040e01020909060910090501080307060608030408190809120607020c040c120c050c031803060709120f02060f0c0a0b1510030b01030f020a0201090b0606040f0e 82
    0x81d40e0240901c00362940d4000a4400381c43d0303001220231070111108030780401c01c14071300402c254203e01440082070303040652503000c50150701e000719055078014449880704040c20f48072201c0c48181d0b042039006070301d16400401c601081192600401c3c01510b500c8004600701407030450590b070ba40405142045044008003407000034401ca94003202c201c003201034041100c40402440542d500c0701c0880b42080113005644d42ea901d1407425000c1c9080384001917440c00802c4251004020040c009a080103050050810079106000414405880e803180c480c0c0b49450805821014142041c9008008508020342c102d0140000c2101c0e451100c516604915841c14a0441e0f2021548034490298040111000424826000400042c122046501c205802c0c1e51a07106c1c03200d4184c06410455040d82c3c003c000320907032840d41d8400e42c402008002e05250100350488a04520012a8006a15840142d440382d1094080c0030300405481c0d0452000d44e502e6103024079002a8600110f1940030b0b01d0046141c607000705d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 920364991 1250 920363741 920363753
    0x20a1e0f12021804050c0706050c030c090f04180b01060305010e10030807020307050307091a0d12080a09020603180f0c1f020a1506050306160504032d050105010906090b0303070f 78
    0x104010013800400c400d0400d044000b10a401c8040d0480b0400e04260010b000d24075100c1c190b900400c14011550308103283d0b42c080004130b40c0a0121982c20580e9800390442416050b1410030000f802021075101b82d50601c0d00040944105800c00e140301e40303803502403100b440403140da94812207411146c89a2525485c1c40000c2c1403009907070040d42d0501c50840b0115407a05640c0c4011882488100c0001c5240c40f40824406142e048603400340032000c800c200e1910f62809102101e600c80c62000000540c031049500286041d0401d40760340802042d05c84164440c10000c00060501da0020002810706c45466000541c001580b668400350707212003182c5820100d402001651b004640c0004507810000f410409000103107060310034207202e4420700c000700300c042d910f4070b000b40c2403501a507503224585811501c1e158260003400260442c8801007442600110b0b0900e100c0c611803900c104000704084d45045c2d03171001030b034445402006000d8035140c84107010380e800008076814140c3c070011031b01003039440742000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 920366241 1250 920364991 920365027
    0x5030717030c0d05130504090809040e070914071205100303050a032d050c03070c0602130e040c05030d02150f09070b040b03010e0f0405100b030c04020a1e0f1202 71
    0x205030501c25040900d01e03003070f0410082c051000e0040c1417261103565940400040d911292800362042904100d01d48460804d504501310200700d00003102c0d40c0030350743c15844041b41c280d010840b14501c862414003002d107500207503410321041c0840081c000c0b0b080c42c484985039551280b100609005000079403200b810b000340c0000c648201c030b4540313154140c440552204500c0c2003030b002001c5c2480c6014005150b6122500581b0302a1180749d0b150442d500c11a507a80c0300070750000c48900c101c00403150b0001b032150b020340c640910803403003440d80c0e208140c80e20061500e00100d2071207400540d0000080c650b80c460840025541c04100a40c07a010349813a110b0007242480c015811052151f20006804078410300c12000442c120340b65140c61400950741d0040c0c6455200003580e0003060b80d0810a42e0000c00030090f008180340700c80003415075408080c4180000c040764815240900407444607041f050520141e500c03103410500890619441b5a1025a0001d0072240c10080e14100294003088118003018410b0407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 920367491 1250 920366241 920366257
    0x90603070807170d050a08010b0702010c0b3328030203060906040c0602010c0c020603100b220b0304050d0807110139080c1806191205010503071703 65
    0x64480203502c40d0040c2d840700140c0040f2040070321074950b4510030b0030311035000c0314400d05042d07032451680d90805100091345c0d071100c2400c3e0304100d1403003840c4000c1541c44c40c050703020740c160401c0383d0f000c0403800355030380324a000610400308c1e0085007a00c091410b4644c180440d2902440142d02503e206103000400751a94680d04080e416100703080c01c01c44004400154240182c3c05100d0260314280da5040c204c2c00e8800500780000000d400c0c124950040c101000030f160408034699a21007115220581e0038080e401200282141c0c0052000c2e04a02140100140740a40501c0030600d25500d49911600e969090b00100c40c0d0402c409100090381c075034030039170320060390a41c81c200911480040e01c10395002c0700701c850400b10341800d25034840700b0301d208103481c0c2510000498403010b81968541e40881d8060300240b620700004c40302800030404556a140040c41e00c840b542d1a40030b10901c400e0801010201c0104050303090038a48401030140c0d41d00000c9203011030700f40c0d240c0a2001403c60300458218010844 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 920368741 1250 920367491 920367493
    0xf040b030d11070806041a0f010302180403050d0e01020a2705060c0f1b100c0f0816020406120b06060f0301090911040906050124050f1e0310181a0906030708 69
    0x28081006241400c90140d400c0308402403a00e9111239804024142007032000940c0b002c3c010942d004542c000d039100c5c0c2c2e4010b009040c401e08200c2005854001d4070103174010711b80d403030f58000b40d052006500880151100908544644041d2495180c601c3d28160a8041c1901c10400841c4001100300100840d0940094802c01d4a00199450045021429030403104512403a05980b07407542c0c1c2031146d1414400560480a4049508400c2d212440b680c1d000300f4a0482100440f007020000d80c41c1c50003600020060320035500e01c009440c3c107044120340800b6000038810707081003188811021651060701d040d92004400000c0e0300200c2d04e0510f520140501c2001d80140c03c00c0c00c0b1900b480440c2c0d202a049540745840c40020700c040515641d5607a200d20740d210081001880740c00c1d200b95210b80503140030000002c0e50045600c514840c8003481c0c0003140c8241a50b44180801e100350382c50048220002480c0307810610035000c42d00c1d900040a801c00da60280182451000920142e904000400003044504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 920369991 1250 920368741 920368753
    0x1021f020922050109091101120e0304060203071104020705030417010204090e2a0a0306110408060c13060534150905010b03060f160c080a0c020f040b030d110708 71
    0x40500b114540a021902c41000c0c64100000b4840900d40030342c1380d0040d8001c1c00022048102001580c00314002d50754601d006030380d03160003690604100700810113002d158000b142c0350a51890310784012800607064500581c01840f503440043e0001050364290346600038060890030031954520300a004581c00300c00214240400080c644030041240e61140b001c0c680340d5050101420101080320581040381c1c2e4000350f1603c8100042815544051202c1242502c41071905944804551070308600340e400c3c0312031280002d640800148080000030040009082090828220ba40200b11500c0703044661021003074803001808603900c030703408080740e600d074004100640100c80b440c20383e00900c400b038021106580384c4004a4824600042c185103c0c070f1841e070348031100780d507803503014251400c400c01100c0600030300007200c030001000c00c005000c8a060303941e10701407094110300400529505c0340f00014003680c5071002074419524082142081c0212a00381201d958404034855480e02615500c2008540201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 920371241 1250 920369991 920370019
    0xb19020d0f140a05010e131e05060f130206040b0d02070203010c2f0304061b08181305041a1e0a05011e080c130f050f0108010c0e01021f0209 62
    0xb54400d0185140742292082150380b801006801c0300c10070b02455011190744400102c0002450314468212840344070410204001c00c9045440c043d005d05044402d5080481005210626981001e9110300ca402e0805440401500407c0141c8503074011062241c50003d18454000b02d1501121480c940c0a002009101c0842c180104000803c403c01c068000c01b61210b400107141520804d4686190507005d14685440c0080035038414a00c40391504000c1e07035403452074002c10500000303485040000851030400c001404c042180d00c041c40000f58455030b140c0400d00c400301707080f4404080501d440107054545910382d6031101c81c44041001802d450f0050840400c01800040c0d0052412900c0100d42140c000390071f2282c804c0d1003071450054070009d90220102521919049400303003440654000001040c1980301c03560815030740c0440302c182c89904040010811b03100c00f4410f40d10110010720b080c2e0110100000002e4482d0b45a001c4503100c0a80503038007214809a0342d0403034090100017070142c5039010750 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 920372491 1250 920371241 920371271
    0x50313060801080c0a05120118110306060d030210050408220f0902090d0f02040b06040b071101110a02060f0421060e0a1106130e1305010b0406030b19020d 68
    0x4038050800040c1c0c01c6400007030140c0300060003072003480740100030b440e120781090140100d1408a00d080e940035900c9001050421741504804107096000d0301041c20162000f505241c508440a0b000d05e0203084604290340100c0e6000ca24a40d00c0754030716501042a4480d402d10781020302501201c501c502c84200c0740314006284800c04c0358100c48021001005003542e0b0b00c1500d04a0003420110303070304214186034160010b81001c4000c0c100610050000440071030361008260030350450f811464000200090120074480c4066045443c08024a0403000c09242030450b1900c0d5940c400c4003d01820002c01c944403908105e4041e200074081003a9032038418410ba6034140c6442d07450316400c0d02c100c0d103450a08011108080740900305603030051580351100c604841840b0303160f400b401c981e914010312140041020320744006d82c0b81c01400e414801c2007405901342041707402c40d049004070303078429487d2034802c1000440d4040700680c005032803408002c80881e000b00d140045c1c401d082601c0b54045c900304080e460721007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 920373741 1250 920372491 920372527
    0x20c030d090504060b03310606030b0a0f050103170c01110d05100e0403080708090a050d0f030e07120807050708010905030a1e1e020304120f02120d050306060d090503 73
    0x700881c0d0501203550f83d1800101144002d641c0c150b4003c1403502100d000040c00401261f40c0f00e52034041c0002030302580c55600c215803c1e60412254020a0001d000c4e903041e403030241e401c1c00c05032400e0400c0136514603a0303441005403c0d8444132074941404120602d20034400c0d440140c1d4400341c601380c03540c3c400d41185c001006107400c8400641059510201058022a0341c856034810365068560784d80741d1700d619505a416450003040304206126510003000001c5081c800c40c040039460391280342e500442e000b4003905448403801000f4040d408448100b00d2030140035014021290048070480c0c0e81c0303590b803c11a05185e4241c1080c1103d6081007020010410000000d0002001c15030ba4250003104400c0e040b2981808031528030b000440c02030a00d404034208030601c2998802a00480e880c0ca42d1359172201e41c42c1e10408005952f0064909440025400c02d0f10200f00c29076002c0c000b0700040c443d0424007a140d40009080d060007103078085040c07028070001c0d0f80320a0406802c0720450340c40e692101d003042100c0c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 920374991 1250 920373741 920373749
    0xe01030f020109170706200d030b010e030f15041a0103030203040e070c0506041b08070801050138090a050406090509010617150a061215140705030115020c030d09 71
    0x54031800c0009500104584c0e06000800300202400c00a464220104d801002008041c0ca501c02002002c401c48181000715054036009900d000c15904c0700300c0c0024280a00100495002e07802c10201b0803050b02010404400620141076805055203460400c2d0510102c4000b1200f516502040003109164001002d00215011030595012590f14040304545104041070000c159501000c00324001070000d801c81e15071114254401001241e8842d960382c54010a40d10218030ba95607240140040306007408081301d18981c0749071000309a85010010169070288440c00e1100d1071010400844513542c6044500007088010400d120050b100c074070102c000d00d02984c000d0b0182d0b00c3c24000040d868210443c1c008c50441d440042c003c48104c0c00a883d1811038010064030f1003130b80e903500c0850703e0715684403208400342c0511540c008250980d1502400c980764801049520ba424004014240b5444011030b81910200002d5000a40f0b448070245d2503c4d6211130310130307454000c0c660090700d43c1d60310124150032a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 920376241 1250 920374991 920374997
    0x305180d09091812050306030c06030a0b09090a051c03060803070c142d0d0203010507110708160504020d0e1002090f18150d0c09020a08070201151e0e01030f0201 71
    0x4469066010041480401131020641c80f015880090099000c1c41d48184d02500380c0d000b81c0c0110001400720745c011107c0061640d80c445100c152800d20400d0f00350b00100c51002042d05c41c050ba1111650b80152100001c01c1582c2c004000c00d80d54800d07080703940241a00e00882e903c64059113445c01207a0014054130300103240031216440f10b480c20307031580041d140e9a611000c050f682d0756960480d200448450b0603800c80c14000910006840c24820306214140aa45042010444074451803c0c01501d0303003d8507842e440021030801980c080c0074400119403040358016610071254a40b4805000000360808135805040701401078002d05030001c01d02850101ca68a01049114003003040c20810700c51a440b0b20a1420009401f00181030007007010140c1c0246420224411560341030403800e21504215100c50300403510a1580d80c024102c20f80009050009103d41e0500703101d03442003d500c510640c407070a0031100222011140c9155210081c210b40d42c000d0855607168106400742a00c1c03642c080b400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 920377491 1250 920376241 920376251
    0x106090c033821010b03031810030608060a0b0a0512071809080f071a07390c0e010501050306180405011e0b010f0810060305180d0909 59
    0x100d030340300c0e204206120900e070106104619400c84034000e05040c5200300e485821222903240d02a980f02a034040449207010005220040d4085080b801d40d0500c0c0050b40c065402070100b0781c3e005041d42010b1005082c140c6520b4420100705000300c0140410380e0000300ba601a001c03e0180c520385681021201310340a8402c404c3c802d03541c2040c040b80c0404400741c02c1c582c0d0003012080c48000c48281c0c103251110303400b24000c03890030076a0315010480c3d8806004401e181c440021107034208100c04047c03c40200c0f20030b544000915181a000d881000d080440c480d9401c051004440c048240a8480208404528000c00c94100600c0c100700510300d1401914070743c0e0100e600000f0a036200e04122407040d20f0203401320305060040c48440480440140007203415540341d0400003150302007824001807a8451160202d80754840000140180100c0960002081907900400c680c0100b0b01541c803044071110718000580790f94a03866120b00c208a003001031018066107020b1b5444030b42c00590002951680401000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 920378741 1250 920377491 920377511
    0xd0b0403031d060c1e09090c1e0a050403020108071707410a0507080a030203010e100515220605040602060c042115051807060804050a1106040e09010609 67
    0x2d0358078021654803c00d034004204601702451401c2c448034510001e10345c001d00701a19640059200c05040f04e80e240d410102184e8000544040703d0360300c00244032148001c1c54a103003104000c01d84d02c07517404040e0500c0074500110f9a40c0788a08280c120301c1c00c00340b1100f005ca06095500500c001d04010107000b443d0310044100d013401d082001c10050301e501803504180c0d83c406510400309240c000b403c81d172041c8034081c02040301207060071000703212910040c0d50050381c96041c100e0406005401a14a0402101258041c0b144c1d4880000803440d400030b0f10311305903c42c1d181100c0290342902240d04c1d4101e8001503400007544907082405041520000d0b02510001c2e50340041c541c00da0b005510485210084440907602a070040030040b401d00313402946114030300da850740c2850b030a0781c10655520008060500d8085046441407041c00c01074042d034900f000042c2003a46a50390f44119203a000380105100c0207900da0940c3c1c5080844c0d004040300e0184c20303614501440c1003030007804148900900107040c024006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 920379991 1250 920378741 920378743
    0x302101a090103030c03050f0a2303060a090f0f020f0307171312091205150610080a020327010506010e1005030406050702010e03070b010f0914040b060d0b0403031d 72
    0x100c00e404081c25000e9183e10b903440c119846603000c10305805000040004a403041a05402003d5504954480c5090751030210100242a0307183c01d0034103d20a0103002b8070040d0340c1c500e04e074401140c00802010845280301c4e07240c0e20050065400050190788001544244645608041d500c1002113460f814280c2081c490f001c401303410211404901c1201003079000d8000313100d403041c0c0c1205030090f1901071a4070b07403125948070300318024403002d85255122869102c0030403012036070203074068803c0d50400c504090315a00980031800241400c0e2034541c01000141d803040071076000704d2003035001070030103011490325455042c000d041c2600c44a0001e4180710008440b418800300594200038140d54503480c0d0303551501c81c9001000d001d0b044400f10f548400c0c6009040b070003000607081007405840c1d20341b07045d451710300010b00c0980c0340c1d80902c0401c0d0524880030103d021300c1c800c0903405a040420010b0316590140007506c540100d1000a01740364040081c0018954180d104556064402d11040b21101100c00e0075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 920381241 1250 920379991 920380031
    0x6140906011a0703050d090b090d18090f180b091005071b03020a0b010f14121c0207051909050708060307050d0804050d060b01180f090b120109030210 66
    0x400d42d0120303001600d102000ea404020702c000c40c000d107059414150300d01c1000d810b03030303140380310680c1d81c00e00703040501400540070f00224481003c2d0b400c0c13111034402e2090304006540340e24460800180e940d400c061001d040b80b508445c0080300c4003502d07042a4002c0385042d00d10041c0075690908144610001c25019609500c03d89004180f651905001c0b84400c4d9258000c000c0b406504a00b1406440049000580f090341964060000030709540c40041c1021007002880300725a000340d1040f0510300c1d59016004000c01c06200c2c41d61591460080c544059800340c1c0b5100d03090340220313080195800b00c5442c850307156556200391002d0b9242842283ca4402c41241d0000c000c0e1038899040c0c10000b02005685001c4d894058502e120710005d0741402da49100007100c4509041c4162021503c1d01e00300c1c1030b40e40c4d01a065240c214440f010741541e180c204540012818002d00a406805540d442c2c0c20300135a58148000b00900884402403003d1042c038075001391100300901c088040541001c0c4161140c5003c0440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 920382491 1250 920381241 920381249
    0x5010f090e07090e03093a0f0f05031b0c01030501051e0402030a060b07050309011e08010311040b130e0601140d061116111008010605180316030614090601 68
    0x40c0185402d01e8007000c010712480105104d0f81c882001004103d0300c64007281064011081424858040e24104844128001d40281034420b0521001ca00c006202c148007007101d039400401c44c034003221840c541285940718808402103408400034a4441d00c0800007280d203211b580a0340e00780701a99944060000050324452281007000001012400c182003075800386a20541d0850041142940e0340c1504446910a00c0251500d07080056159419600700d02590348000c140b04802040e9407110748010600b031018003005203000c500035001070323040e600c5d40c2260820f00b6004150b1840c41039101d10081c001c000003d40c4130b0780d901403080000343da01c01305004030650020240c07040810b0710311642c402d4000d03c121a545045008284998554214541c01010075580710380e500781d540c0f040ca0010040175a44812404040140007001441074980c07200070350300c5a0042c551a030307180e8a080c10000c1c2c104407640801c590041441d8800000388010b682080c000b80003076212014240d19140c060545450003401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 920383741 1250 920382491 920382493
    0xc03120c0d0503090c1012060f0e1005060d0207050a0803090f07050102120a030b0d06060b0304060f09201807050406091707030305160609060608060609060a0522020d05010f090e 78
    0x2051710900303042000300320110961600c101031480689042c011a00707071f900f001d07a10f01e030841c1082c80400e0740c035850f02e608402c07140401460301c1d01e480d001601a2103040c061000342c42d00818000204101040051405a84511850f4903072600ca246180d59405450a40800340300340440001e070703540040340740010000307000e060324601743d00c144081d4041c4c107920780380d50f400000901b00320300812404d10443c80a809074000d46a40c90910b410074400303441084946442a40c5455600000260f0404601d80345410446281900e6044c18000900700340300d85100f0250242c00004204038158403800030001c2e1005900e6280b015905c030702200034411003680200e05558005002407000ca4080c07c060404950b112407409210318003aa02c21064584c030400496210303860300d009000f81c80e005c0c810203505c81d206072800d07801d034903001002460b120940d2040c2e5000b10406000e0109094170301083c00d9042130052815580d490340021100028a001d114501068003074080125100ca018014001b60043e204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 920384991 1250 920383741 920383753
    0x804060f0f110c1009080102030a0b0a0b09010c020d020402120c0405040606020303040c0b03101508100e13030302090303070c0f1e030302060c0a090302040507081005030307020306180c03120c0d050309 88
    0x4040c4030810000e402e840040c803c0302c08001501e184240009d6101d040090000b0030300c4002c0605000d030032041da8000e1000008148031046940c0d90201840c00c0c800e8040f52000000185400803500a20400048207000050181000f86000302c0500410481c0c200341c400300b104075a204000c0340c890100751001080380f00500e408008466810001c0c43c0c000b0325041501c114642d07036003c217440f20210001400c01040c6c802d4100880032241300301080040001c208551038901e04074800e40340c000b40001d00282415404140b040c1507480c10403e0b20146944040c070a1011034485000000084681c424410300700c00049809031100080c003045001c8a40c50340040542d601c4000021000390456a00032040004842c0c000001d03a90354041c0038000c075140d8603080850305140b20700c00090803560b084907000b503004002c410010b07140010f41980c440c0d81640d841c000070034808021800c1c502c07802c4080b5407500c5400d40d8520341110000c01004030350f01010446415198180096590340412140050103400030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 920386241 1250 920384991 920385013
    0x81504021c05100b0a02152214031611040f0e0a0308060f0a0303110d09120303021b0706080106020c010305010e041209030b010906140a0e07110a0804060f0f11 70
    0x5504069000701e4040c0400d0f9907591070b940010000d8002a00e0980143c2c000002c0c04150350010b00e0b4160401c1c89420400540d10b4115286503d01041c80002000d1060010707a40c043e521050055030781001c402ca4003c0100c4000c2e0610f4120442c0310410303a4421460400e458600c1c030000d100d9095404540030242c80e494084d918140c500c4140101220340180840c5014284c5548400060000e0342c801e031a54009a80307101b64191600199840110078010314940c10300c14030300d42e010842461681450701507510440520440c0d011002e081c05000c652068180c045030054100a989060341c4281d8201c49100e2040750044080da0001c1c80392000c4c0c1251240818007150a590350201800032a0500c0700507583d03607589201140400b60f000c445940e0396800144098601842d4080c12640d0440756080200e040282c590032121014004d14144407403205c200c840b10100744816200203801c50210342e1101d0780d6800240c5030300944020400000c0e6200d04074903c6600071814020041d00000081c5050442 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 920387491 1250 920386241 920386297
    0xf1508010b180903090312041e23030313030609290703050924010501140c03250506040606030309080d0c020405070201020c0a080702010305091f020d020708030708150402 75
    0x1c040c03c03200352030104102e0000903440170810703600e40d0f06000b122995070740d2a002840c140d004120000840030080c0040801000013030311010b00000803155400702498501d41c00091451054042e0300e091450452000030501c0644e61168030403a0040d0f8480441000078004400b64942c4070341d120f61505022800310394480c0c07003030703229030740c45034800080f01d49162212009400c0150001c0c12299292400c0e8014042541d1055a01c4c3c0e005c51146130f102d0600d00401c403c04c0c1c5038015240c0080c405c003000c00b0f0700744410740078140588003aa0400141c2e060f41c03d044c1414000341c6020300041e00810b584440c0060064800100250026007980d104030001c40280e0810014250142c200c40856400f8003052012000510600c0c032654440c4c07003080d0ba200550300c009012b80740001d040002d07982000c070500030b0391404400c850f000e41000110041e51410000030010085c0580c0f0b00c0a010390602008000003130ba00a80550b0051800603d60078109414004000591040c03284004605013503240980600c69 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 920388741 1250 920387491 920387539
    0xa0510030c03031823030d0c030c023001140c09031902130c0302030105120325081e030a0b1e0f0a1a0a09080a0b06010507150f1508010b 60
    0x1541040c40c800700d59540980100480c0b003441c20100c60308910717030246003502c1c0401c8060501009410450348010003500c014103a04504000a409820b0b00c203440d11100f000c0601d10020b0554046650703050b503602000030b83c001c2c444640445400c44079080031450301c042c17600503640c02420027002030209100c490402c2d45400d10f401c0040784c00141005e0f1a88012006006451100741c0aaa00680725850802048811005808002d1040d00300f00078250500c1011614208401c955450301c0081d44da452504110b5445402d60ba070413007001e0107a01402c0b41c1145c02c01107001d0440300000b840390b010380400300300081069803844070f0070126600c00d403803290500e04819844071f80020301001242da030b2060440e00301e28400e44520241680040c5a4030300d9034000d981000a46000c03402084d04001c140d8554000360f1000d020f55040c030101103000420081b4481c0e200e03031581828101070002001501d04100644410002441803542c508000b1584040500c182980030310700814210011600009401c42d00c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 920389991 1250 920388741 920388767
    0x150a1812030e030a120513051804230313050306090601060905041107020907090501080a0b0a030803040f0204090308090d11030301052205040f0c090b090a230c030a0510030c0303 78
    0x2000302c2c0c94440200c1d00d40192482c040005031a07141c1e488555402c0d58640c7c0342250080380c0314a022003400d0200d101803000042c1c1c419031014401c02001e40c24805040400425102c8103e2403000190ba804541c0088011000305d03441a000c580e0292152800c2c1034465109002d8980000c0416000308405c1c54603410103101d909403040c100345441c8854011420b60142100c0030408565614401c00c25540c1c0004990b070f000c0394200b001c00007a0340b00000619144070030300c0090b10700e039400710204052203c50480d00032101d600400420080c4420701c1c010307010350b104603100201030040202105d030213801503d10071000c1c07100d50051495a802c040030001340715002d94030030311000716003000e40020b03a045e403007128022401075000c0b030010240351800410b21310b1584c21204010381000394041d11030b21001d107020380144007a0404240c1400c88540e100c3e03185404c00e007240c603905070f040034403880341b0f014001503000b02811a0140819034480ca20125042c081d448020710a040440d0f0410200344101200c43c035203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 920391241 1250 920389991 920389993
    0x7021e01090503100c0e100e01080705090301020a0306080c042c0106030512092106072a15051302060301030807261801020c060702090405010b150a1812030e03 70
    0x5a912079001c0b82c07a04803c407452441e2142e4641100c00700301c0c0c0208070410f00a004690070342c01d080e68800010400508030548c0d078144030904010a0445026405681e8980300160003151182d03005507009002d00303400d1146041b1402202400ca046007018022001004007400303045180449102c869845c0c0c2104034401506550395650220004074140100300459031090056034135003070210304000240e8540d0112401d450080b1105000d140340104200780e0050070b40c01c0040c1c00c6e0102020314504428a00c14480c01c211590000204010015200040c809400314081202c0c2d43d032052900c0b8250340c101806903114000344010400030710444003c1c40c40714803c410408402c81c0c0e0941c20340041d031161000404501002c80c0070314440e1501650a622041c00340300601c0402d0000001c0b0b47c1c0d900c1840c00181c01002c2140005091101c2500a0042c1d0700b40913288403514041c411140c00b29401c24800040002e002d4181130380324003461500d050650707600d002041401d003040d41e000e40703407120000c85440d01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 920392491 1250 920391241 920391257
    0x1208071b0b09060705100c170106080106120509070b2b0b06190c0204060303081906060e0f0a0e130c0b03040837090807060503090a030f140304050109060507020307021e01 75
    0x1021b100c034003070b400f8040000d031901c640b14555090000d480d410140c000c0c0041044003001080082d5024141c0b020100000070005003648500801905242e05900b000d42628400540442190608086c0c007410842148402c0f05220010980005503801e210b0750907400101070051710300d014881000d0650403991400d040b038900c01c41d0340c04901520655403098000c00c10603020030540380000a58000e500180242c104021410440c000d048103022042590103151108801903da40b500706108014040f000b0001480b071401c50300a01d1000381c025000c96840305221030020748001000c05403409550b1214800b81441d407003060707880d40c91212820b950691600e4074408050304126030150840380009541e03c414050405201c54a015110b81c014030804c0810802c11103139480100302a152030b6070616051304210000c0004407001100c10040b80c0d41f480d000018401000300540c003480d145031040100388169a41c00c0c07020307038a0740120310020350070a0300b071020342d012038030724a0390715040180506242d41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 920393741 1250 920392491 920392513
    0x61a040b1b0105010f1d040512031915140306010308070609021c06090b070f020c0405041a010b0c150c0d0e012705010506150706020906041208071b0b09060705 70
    0x30070f6480130307031000c4e0072450445018000944034285441ea90891000501100e04196481c141d4882c2c8074404803448003c04408a0748d11401b0111031842d44803502c0041c406034104002c10034038210540700e000c8000c5640b41c0410340c1420b000c91101d040f40d40000c0c1c0c2500700751141c0c58072005000340b03000403030740035403110110000d0554444415502c2802110001103c1c0304034a071142c840700001d45100e0070b0103040341e54055403d41c0029214210740d001e4401142e1921140b514044620700c1c12542c80c00039036083d00201f02c1040a40c094030300e42c844182204d164000400401c90f05010030349413915842400c02903205810490f4010240214064000044240e54040540c09040c40c18150135451080304076100c041c094240a01a00b02c001114070624915103201c005216102d5800c0050032a500031810780705a03501d442c1034400501c807480c00a48021b200b45000070f080e500c4603204560a985690304545842800c00100003a184110049450554036900300000d42e001102c08032164820800428 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 920394991 1250 920393741 920393743
    0x61005180f04061508090f0d030e0309041d2107020d052e060b030c070308070306030b04150c090503070b0d061706060112090506071d0406031104061a040b1b 69
    0x401041410b2010303241307aa519100401c0c58802030015802030317000c0c1402010f01c1d240407038012480c0140d8100001d09040a03002542140a0204140d500ca0301d0580c480f0141c0600b900c4036184031081d0310503100c00c0414018601d045085030820449500400c0c07007007a005041c0403540500c0507000d42c1c01c949000c94400c0b4003154030003039881145580b50b0381c80360400d40c0e807000380030740405400600401402c514090711254454029034030041c003044910300c080f40005001c1d60140c0080d50304011021102e10b003608084080080041040e04614680303104646520b10a000700810388034000e000d000d2043c40c000510001c3d4018042100540c0c0d0399241c00180c02080c3c103051080b00080002911031803510030009400da1200300c0015203c40d0419100000141010403216031120b80c50511ba01e45482c0c0c0300c103202621400848494216180400110034420591100000c41c0802c4400f40b140b00c1e01c4074003192184600c01805003404a052105002c00f600030b01c09030040e0400c186444480c804100001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 920396241 1250 920394991 920395001
    0x2001030f110c0d0c1a04081603021506100e0111010e01231e0610030906020304060b0910080a08090402130e071d03060a0504150c080906061005180f04 66
    0x8407200e8034000380d28007640400748940340c85802c1034182519420180d842d0814100715284200264111a0000800704180c0400380d98040032003e07000390801d40c9500d4041d54401410180d0340e0700300c030f84c0c50002d0700c00e141010082408401590f9504109024140159515444800e1501455483d41d081040d0303a00c09209000580710345442100c4145101100f04182c400083d19580903110b0090701c4242000b45a0661500030714250f4072505c10180040c0203c00904070010000d0804d40000144410b024240c3c0002c8101042200c1c8d12a55440700071415041c201d107441440310a4001368000c2c00071454200107450316040180c00945013074030b0714100c1440240310b0341001e2038542d03201092000999010041e9a18046901d058000ea2010200001c2e620400102880c01d02038540e0002000c101d031490074050320b562000c606000a10000030301620380d00302245d01c0e20062098000050151070000c0074102c103008a0384840d072a107411402c6290921061107031545e0004030031b0720700c5030369502c540c86a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 920397491 1250 920396241 920396261
    0x114010e011107150e040e010204151103040b030c0c0c060a1d0301090f0302060712021e0c07170102120a02070809010f0219080a0206060a0803160c1e051c2001030f 72
    0x2605e460b41c0c1c1000100030846016601004180e071041c0800c0c0040020050780a2281d1014206524025015403042d45148a83d400454400e940031040c009460b00b050082d0418209480c151080c04400d18203200c0d15000c1d445040c800503000c2d0a040e9196810000d00c020130400c05000403030a2156a1100d1400c10813845046005a004174104511107500100600c8400802c0c1019486e0800c09000c1041401e1080d14500d482c400c00611403d00302e204008850040000c4c500314500a120400d015000f50007240a0409900d96040020310244040c0308031010241d011740d04508081c1c072034004441c1e040b0815400d20075031049040c00100e0380703c010006231780544152821550362031000320081c20410090009405820b20150030302c103402c00802500c020003c0403454001d688680d06100000812660100c04986400847d03a00420080d03a9254162801983e20907500805104a43c00300e441c584809442c2042c0710310101c070302d074000307074540c03a42c14a05240120302800c10750b220404496010344 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 920398741 1250 920397491 920397497
    0x15091b0c011b050912010608030901121d0705010906030506150a0203040e090304031e051b0a090e010b09060109030f030518091e010501090e0117010e0a0c0e0114010e01110715 77
    0x210f500051408a4285c0d075054101c100038020030307184c14401c030303504e000c0d080200e4188805e50a9003a410540ea601094105c1e0204464910200c10168110f403240c44134010940082d44c250800708000e406030048a0003503c02030308480d0b0039584810035140395007144444c0e004501042000007900a18101403a015a8a440c080c41d40e0700d156150445010707442200a2008000c1c1d904000c01188000c25481c403180c108501c2c003c24003101e03c1c0000c0d034032a00e941040d94030a1801100c14041601540240303007011094178001225102d5100565610390940700c0281748168201903440024800c002900c40780781001c5a0311050801100014038040d1b040311744030329841c071100c03a00c02020f4844124500506007800d00304217940c108007204c00702003814002c020384c0d0340c00121b00500500c0250300043e1182c0c2d04000b910742200a40c40c20401d00038980c49003100080203e00082000c20340b029001c920b90304140c507208501110500152100c0500312400341203030080d0640003500000300c1d58411180b00d000d035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 920399991 1250 920398741 920398747
    0x604090e0a120e1c080307030c1e030501080607020109120c1506120b0c0306030c09091002032701020a05040e0403031413020301050f044715091b0c011b05 68
    0x70305200004c500d1a07076600104140318100000f05454608880c1c114249142c049580070040406680c1d1043e141040082c0700d5039104849680c41d410b41c041c0c0c1c1a20280d0096500c0d544032048103d00780d1708500809410345001407001e0b8000c6004a80820b41070b803192000408840e680306414003141c10f640c0c0a02025074400702ca0904201142e030045a0021445c040641075040160200b56511503961000740142c01d5400400c3c2c00ea8410003150350b401c80304840655a91038a203414102c010751543d0020003800c070a05010340032540600070344034200c440b40e5404d41010701e00108103c080344098819001d0584d6100c442c0c00000d02c21039004d118a0900302c4c1030507003000503c14036003102c10080c6000d024480400c180000140e15564508014000380714404603244e103055891008640d28402402c0304421111450550400107183ea2003908012100e6140e085040280500766008840700302e514400b00640489100d200c0f0090b00754119240c000182200ca40070401080045001e02c41011074004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 920401241 1250 920399991 920400017
    0x70e031614180c0f0c06040606080d0906050a3209010e0f090402010309080c0307050615040903090e0c1e220e0f0c07020907080417090604090e0a12 65
    0x19100e0900e000100b9a00324000810300862030035445809090040250000241c1800c0c2120708070556800c01e441c881a100542001d03e0308900402d0036202d1202c640c060040c5042c0a41d000341c00d0401150071a4554074034103c400c1b0422200301c0c41110800e00101d444028513007403403565100f20030040390190301d03181c0d0700e850100c0050403412048036514850180702f961280291034100909403c42ea0a0030081901035080c40c00350b50307074010079450605c18070010070810f007804000280ca50040000d880c0d2050217803961014401510a1a14040d01040d0758042c20400c40803048a910340c041240380710541820358003055003c064172040d64441441c2400700c0c000b0303014820700010b42c038000f02821054140c1ca10340304000402a00007000b00304034034401d00000f480c080d00c4404848207280c1c02044642145440400940808000e9600352075000c50101c0c03109110100800300c50002400500c0d45042a140603c003c3c00f400002170090744c2030240300240800100141424494040c2e2902c48201030412 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 920402491 1250 920401241 920401259
    0x402040f18150e0d0203040b1806130306050106050903031b030409020d0b120a0b04112b0303050603010c02150c3702060c040e06030c1c030810050303040e070e0316 72
    0x8a803c80c0600c0d030001c00501a016400000310380c121409405020745030710040303ca5004032a000041c1ea40c111400041c41c2800c03030340f03001c01ca40c160303031082d441000b441e6240c6504450781d0255107121a01540b0411000c6403207105030b41d2407400035003840120317403410b5150130764902684c10061303a585e809621400c2c0400c030341c03030a45249446c07000a10700800341c03c141c60300e030ba40b035a190181001c0d10f80c1e6030202102074107843e91801c0810301c1300e0302c84d00030803030f40c18004000281e00c011010640000346010003080071441c040c003c202486500754010451a004103030301c00103034000039141034407009007040814402804103d00381c0d42031305440400d190b10391000e204088405211192941150840d030308101402c003070041500c0903154401c0030300c21103076200404a881d0000c0c820a141d44056402c140f05a26010f0254400c0c22512903510000c0580b1412013901c030840c0d545c040c0701e42c950820f100500c50b000e606011070b50701641e01d00d005584000b040c804070f03081c810311412552042c07005010501110172 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 920403741 1250 920402491 920402501
    0xc0c1f03050f0618150d08122415070c09060503060117060f040302030d0906052a0307050310030c0b03160513061206052205060603040503030402040f1815 68
    0x7155030000030526003c40041c2002591203450860401d200001c130f03d440700d9248070524810360280c082210400f02c1e0401900c07d801c1004080b503141107000000c4d4120030003806081454501d480c43c0c1d140d030034068003003010245192a070000c03200014000c20000c1aa06041900105000c100c0010000c1c1030030203160410205801806228036044403201c202400000c1c0c0b07503400840d2201640d680d403201d1400f24210f114046906200608001161007070000707980c02280925002c040d0001404c0c00040d1414103400c1d0a046a2000c00062000400542c0640002c1d9031050903100b00303150090301e95030f0b503542c0442c030364001d17030b604400200800c10304048040843c20203103803a0602c03c0c1006590740191800e0b00040c003d04082268040761030a5880b520b812001c042d1400074014201c0360311918002c403d05207410002c4801d1400c2402145590603e4001c1b1f038055504000a903165030b649809000c040c003202c07004450303016514003e6490080c1c42c480781e031440310721940101920403410752584080d62 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 920404991 1250 920403741 920403751
    0x40906030228060807090b030412080a0b030604060207020d1a0613022a07090c03050a0b190311150d0c02100c3c0f02070b0a080c0c0c1f0305 62
    0x12121100050b078603031566030035000c5854a00d800a040e80d14010220390780c1d0140e600000900ca004800d000030418242808544c030b100b29568410705960b16090351044d02d641019940d0580c0100e004980410195001801e1160000e0041110518540da6180c648038400900e400c11405580c01d00c5040c0c9440c00c4000300e032a10021055041c443c0800762740c00d80c4500e00540108120007190000d904400511814001b0122078000b080030f14200307407001e00941000c44100443e81d02d8502c440380d2600d010f88030054011806040303103840c2400c40e0f54400d09105901d1040d940242e26580f070f07400d800b092400511000c010000301280018001001a20f884103200702c0b50000741c20003200b00c0580761700c203024900c00714403880c903080400f4030f03080116180301350016034021980822211158041c0c014240803042c000541c01c0790880d035512111070003030780540c1080e0000986041c01080c89000000046c00580c1142019940008402c1c400250405021814000c1501c90f16940c0b000a642500c24103501c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 920406241 1250 920404991 920405029
    0x10b040b0a0b0307030b10030b0a1211060d020409050c04090b0406030302030f0f0c070b03061203031302060c0f0d120b030f0a021014030c0d0b121005090307080409060302 75
    0x426000350000ea207007062406200100c02c0c0200000d0b030014402c0d04590884440900040b06000758200700901030320392405464014028020f000910017840c941000b8000e802020b501304500c4060204086c82d4050704088034159000c0c0404240f080843c86440c2c0190b1202c42000e540e1440d29a1070003c0ea03240c00407480c45980380440070804280c000c4201c440d2031001c202c07201d41e640d80c0d5805030140da010700034118040c4d100c1d0442c0840d00c408118011406400304445034105810b40d28a055560b20003100e4500c941c486041011005050600c003909a403039980c815944100c216000161030250301090301000a80c00050089055405200740c0100040c1174003d803c10f000c820018907995191117100a0040f03960328210329901d4802c070b4020002c51061215141d4030704020f000110181c00a081400d045440c15080410174503109000c00500f410706405010f1150304010948002c02e0300800b10040d0340810060301d070000d02541d0080c0301030300b000140010a60b0560040c485903140c022001851 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 920407491 1250 920406241 920406251
    0x3050f100c02190204020a180906050108060604060f18091a01120b010804080d18050a021c0b060405040507080d02340e0601050904020a081e010f0b0c0a0203120705010b04 75
    0x7500f40c00c2d0340981c02901903402595a50039124100d411032901d00144610840e1403c002c075408211350072001c110340f002d0381c0f0120a81c0300c260400c6058403e80c4a0a40803032140d0b840c004003140901c4c4034101d0f81e03038281104c080300e95440d4011401e680000350060710f41244542003044560300302d00d926403442c40d001001c00c818034071030300003804913040900007030001100480c00100c4440190424000d00d4582290344406400600d06550b49840b00c2c01c08a22903088000c01940c080055a1a414801c1d080320ba10310f66516120184030061001400640340e5000d08000820f4000301000721034640300e410390080049150700c481045001d21100c0ca40413140d00d4117000d819020034910400e0381614050741d20450503841e2080180c445100c1c440038240c0150000c00c0711299107030040289403141c9022000160141401c12230252005002d014140c0c9640e04040e003440841881005080d0040800c07007114406200f580000b031a00740550296102a100007408004000302809881d2810710180e5051107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 920408741 1250 920407491 920407513
    0x4050d030e0304170709020a09030c090c090e250e18151e0a060c05010e070b0d090507080f060414160302060d1409010606092102041503050f100c02 65
    0x10b1280300714820322264045007819682d044406010a0f00140840101150b44e0300ea9280080c08401240c07000b90354010000380000b480b011035001e40f4480000c540d80700c298060030b112024490a4001c0c11821030b0081882c1d94a42c94440e56609892800303042d01d40c4032640000404011041d10100349104c000d4258406000f030704030162107140c07182081200c00340100040101846010340016140e198042c0010f42c0c0025000c0d08950441500360180000b4002c00081410700c960b2003000380314810311503400308083d10007400c4540c48080000c0c4100241d03000c003603491041e189811503003800300d26240c110005100411003001c05030115641c00c400540b07952412200c10754540b12513440080d001d4103002455842c010351035800b00c80300341d606106260031400e000c900345000f400140114004212103980206030040c0030000700c80e920702200c01c0c1a60242d07080c0c1c240400350000e00c804010010082c000400003440a2200c846c0c084501300c0140f840001c240d0747c0506880100c0e441070300755006900056 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 920409991 1250 920408741 920408743
    0x240e2802150702010c0c15090801291804060506030723010f09090c0c0209100e0a0903050c060f1501080423030f0c061006141c0f020c010504050d030e 66
    0xc4200c105001d03809445084078001a581064903890041c440c585108010614040d03602e040c1d40f00b014165500c0d50300d00d403511440c03800c0f118a610300c220030500308440740b0786806000d5512002c0c0c040103003110340c004801d444ca85c031200310117407805c44141e604c900c1009507a0804001000060500008000c511803e511403101d200030b03964500c0d810001071540d8401400d00590540008101042c010030002c3e1641500a24603607103a40105d1084004501041c040203001c042c0720706403a0703071880184183d210016000c0c0144039402c1d040307051150510281e00212014010340b4850700f411403900d840c52824000980b01840340790600c03418840c1c1401844086140c0c0160714228405580c6c052141074112102d42c1e1a6000d0150070b00d42030800003400c081642000b08215020f00700312520000400d88076003090b10540040110030040c0d00e01400048140a543d600c2402200b1081e080010b11f05110207200c0c0907603011524401c90390f0b4690061004203d0104487c0f0403807001840c0c100481c65402c00c080b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 920411241 1250 920409991 920410009
    0x110a050d0506030c0a060203070201090e0c0a1b0f0c0314060c030a09111003091b03030e09070512040803040b07020d080a480306050d240e2802 63
    0xc5100a55200700203102a00c081050300540000100804c0b44103644000095a940c080c09003280060039601002400d4494000c0e10b80c09801425142424104040000c0b40c118101c0d241081da08561403003a41c01007102e01d00d884800f1402071382c240c100c0d5070131824000b0848110b148400c405a005108011000c1c00c2101902d810010003c1c1c007080381001030034400340305285851040d92000c02c0c041100c4c40580c05a01400c0041c0c4118131021400741c40d841c03034070200c0b445807002501244114116000d94540031203c0c0ba13114415003003a0f03041110030f07203820031446012641183c0b00c034800000d0005020407440070703541c06852403000300405242da43c0003c002c50300140c4030000841e00da180c2030810403401220038101150440e092181604032040140031400745801e0a00c0301074070305186c818810301c44d0251405580c009030901080c542d481d6030700325035441e10000f98a140d6025801c044482e0040b801040c00c85c404100050045c02005059104110081040c119004910441010043c0c8611007a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 920412491 1250 920411241 920411257
    0x5070f0b16060b040f0f060504060302030607080916290a0903080a020f150f060d0803070e1201090c05030d0507050c060a051201090504051501080c04091e05060a110a05 74
    0x480300c1c800c00c1440c001020300564520941c1c403a00303214403401000090f901040580c890040e05000c21550340702440100d91441c0001794240d00020300083c0b1144c001c01c10385401c480700c40225419810b1802e05d08910440d00e0b04012030805c041a490001d020900c0615000d05170302d114100d1802a1801000c0c1c6025014800202140b00118803d00d42a00a0140c0345520480c03200f520400e0180c8202d50031024421075550110781e004101041c054102119947c48036a4421955461511089002d580d0900484640d95004901c0350740301d034600c0801e018140a4601c1503009084080c245002c0604080321040c0c4502040300500002000c5000050144030180701036610036a5580415003c490074492002c0441003a049000006400314055100c02d12880c01141a56641081c9480080b08044d0a03c25910541c0c007d104c440b10a2402e0f40c84129a503204031032000303540920b1104200e1401281400381d4054000d40104102c0107061b01910407503107660300b8860314111100c00098114094460 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 920413741 1250 920412491 920412517
    0x604030c0501020c0114100603090f03051602120d081b40150e0f10020f06100602120f0304120309051f1a0109140301110a02030705070f0b 61
    0x302a001e0103000c2d81295145a0000020f101c008208115418081019101800c40d4480704000085292280c42102182e591118803100783d416682c030111090b420030700007441810951001e190060b620b2007028005c0c50009400340003180040c03000503000320f20043c880000c20781c81c9190075500361040c03402c541e089142c00e000c284928501c1070000d0360003c540f030041020740c038010384a28607103590041c0240445043c0000b1000310822800112082c0341607c803010303013102418102c0d12507440c1c4040c51031140c800d02c0c030441c0c501071700d44e1044910b4813100381c4039054000704848080c03003400d40c1840188000ca1000c1041c0c0c3c41e285024100300d40702d20004202800403100c00d41d5007841d40e8400d030882c4020641180840d50944981c0b0b6281c0d0f003407030103e02c09245803440c040a42a42c82d21800c0041c15040c030586902c42030516101180d555688041031156240d50fa440009a50b00c0906c405003000501c640d004503200c04881c0b0b00b480c42c00004c1d0b0000c02d00e80701030100070004508254100d0b80741410300700c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 920414991 1250 920413741 920413757
    0x12061b1d0d03110102071a2a0702121b04110304050703060b12010606030f0b010809060106110a0b040615120b0c1614010c0905040c02060c0f19090302100503010602060403 75
    0x10a044880c01103910f01c100241d4000a844402e00140b194501030f000425041c00700180c0300c05007051986400f040301868048202140030b0f11240340c00025103481800900304142101107400c0342814421802580c0e115102d040740300324900d05080c424001e140081c20341541c611b050648a0b00c1d42d9022511000b00341580391420703691641c8840f107900900c210031000a1000c15191680a00070b46402100208039615003180721156620589080c0e004240b100d014102503400c150040302c01c490300c08400c00c1640b1a0111b82000243c038000030a2042d4000c440021b56410705071210300982c50107030300c0a500c2c21015a0700d100416102c080c17494001140d5030303525680d50304032120b03621000c01050740907024100d0b800700b0940d86907064004441101c501d9403280e80030758030b8004001c1115450400b100040c2d00c4040002c000311030b040003d082800d19030085030b0520382c0c0084074144044410b80c5e54000038090007420000c40c10b00c071103201405649824135a0456050000080d40c0315001031015003080400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 920416241 1250 920414991 920414993
    0xb090408090a0803030c0d0510150e0a12050604050124060315050409140d05210a0204080f0d030e03030717070c0b0c090a08070f0509090712061b1d0d 66
    0xd40b00d1004003910801e8030346a28206074440303503a41003c0381c0500c80034117080001d0b0000310308030500e8081e5006001500c1a000d500c02c3d044074206041c255068000e19141000b060104009640c5d09a06200340001d05d203505d800d20b0101d01351140d02c002c001c80c0411243e1102038000006034004190f03a003a203400180503a142001e2003a6503055132015801c58684030030760080c800903407001d4080840b07a00c1151541c0000a00071a034900c1400c03100e40c03440715588120070018080d05c1c0015004a8507550140c2010749440b02c80e0b0900003406404951a4440e09d030034110716405010b464115400700c8040c40c210b10b0b0513007001c0c180c1d104180020510007481c0d00000e00c900c0c060341403d42030a030000048146031615482c000190741c0b0100035140300341c941280009140a0014404e400d41c0e860035a51022170b8a00018400d500340d0151203d18140920040480c04035030f005618ad2100f4022880882d8086124114400c2c140702c144401c001c0180000b02403080d80e0101541e5904a482900c0c546803081d41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 920417491 1250 920416241 920416249
    0x10090308030a1b09031a0103151a04230708060906010f17040b07170c0909040f05010905070303030609050f0f0907030516030b090607020a120c081c0c030b09040809 72
    0x488440c3c0c10035910034070040c00c0355903100d07054a06682c42400c001c01e41010800c02d0030040c92092000520002c100360428001d50501d81040d401c68100d0102000c00c0c4640c1c0c1300003425504403074011844e01c0a50300c2603442000c40c1c0790320340b500001c86040282807810b203800482c00e1208020b02c0e1b5070502000194400035580b0915007506200c1c440c1040403958100b61922442c4610256440000141e80b07040c0000d101008100050080340002d003614907211440e018084a8400180f0903182c079002d40d204140400c10a004142d0f1a920031800b46c01101c1c2180740107411651982c0140329014900020041c481410034050360304100c2e002004003081d920914080c0c91b2081d0380c0c00003042c501428404103581103010380b6880c25680f01b03e644d242c041e0b40b0144071039610b0900f01c402a006030f01003240440403d184440c00c0d40051003602d0806a201a55104c7c2c065540c4007818118035071240324408800b1048030300c9800c00c4038141d8507051180200c140d00007090070b1800340004c3c1410f4400a05a2010360b5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 920418741 1250 920417491 920417501
    0x230a030e15070c030201020c06090d1e1703060a0f05090f220305030402040b18160909060b1b0d05070602031510050d150303140d0621020f10090308030a 67
    0x4100c000c030350b5691001c0d180041c0d03195040d2104a02511030f609000d40c1e01d00d014410b6958405000c0c040401c4403406071151031182c80c4002100c032225a4000c0c080c0b02040d4018442c00c1c10441c00b0780641d9072414010203200360403c01d44c0c004460401a18018440340e80d80165580d08924414440d080d107441c0e28071030342d41540802520f074030400d08000320907007007540000c055071266000f01e401301320214520081c0580156800c0f90320a18045840c005104441c0121000390022500e2900c0d20040d03032a10708041c1160b8450300300d003071240c101255910051860301c480e0159420010080d119489070510040c3c03481c0a2420300414082e008800100402c8440e8070124007520300910205410480c118040d12b01c2c0d1144c1d0081c1102403d0040750071005010116240481c0d6069036120100c0f6011001c03924150000c0d10610a5540c0f202800100e00b80c00c080031030340301c00040070301c0c2c25040107034810044c520f0f002c0042140550030150281d20321075000f0003110100c1c0d8016207401c0d525030b03c146107400102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 920419991 1250 920418741 920418769
    0x73507110f070f09052205011e0e2415060702090403030b1203040b04180f060f080f120d09030c1a04060b031b10030902090f04230a030e 60
    0xc401c00e1510020301c1c800003901012610391981c40c1010035210101c04003602c0702241c888040100710700c45014240f41d81d480c0c20301140e00450001130080010803014140c0300c55403001030700312921600e0b05004c259040c480d6001d007030340281204150b141c885c00341a1030110000d000c98429018044c0a001a444a20844214981c0141040c2d42c62600f45000340c0100034261381c0303d000e1502c0c00c500700d424000020484d0181c880d40b001c114103040c41c142d0203513500e45030b002e8072041c40c40d100d80300c0c0c0300690624024480501034003c20280207a09081110b07141c888400c88407809a40711007951464104d41c282110100c40464101043d4400300e41400d8a0011a0031401084d21008064504450946444050140d403196405011186100c0d0070556901032498880c004281c200540e400103141c201040000e01d40b40d81800f0400301c0311a000110003150031228028191162001c000800098000d0504140802c14400707082e20021082c10b0390742c59103c41c0050034015103008020840c0d4030310460007407007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 920421241 1250 920419991 920419993
    0x60b0a09020d0e0d1701050904021c150f060608010311120d03020306041401081510170303100501020f0303011206060b0c3d090f1a07350711 62
    0x40c0c4045502c1d40014800040d242540d8040d040c8055200c40c07280880107032842c0541c621119070b909000030082106405031040340d105000103903d080074120031982c2042d0764080c841345c0d800d082140b04100103070344005442c8805503183c11420b014040d005101c403810b6a811013a0045c0310040100880c1c090502c00c408182035200c1c041040280c150715400842c403508081c0d4080c00814900303d40c44800030403c0c003c0b003030241c1011219100c003154142031b46920210313000c07119031002d0b6500780c005814000c0104c0c64109800010030070002c50f003920a410001c22081c801040d000300d4041c02a40c0b40e010601a408488210009060a020103604164041e20146002e15901d595900d6425914040482c4c81d403018210101040306025407001c4a00314450704c442044000140c141c03040c2c0050541450031503581c14621500b07000f00d29403141c00103011800005501850800c0100a41508002d80c110324030700b0800f42c140360103690f840d442c42d01c0d428800c3c10040c0041c0c0758041c040d205005420096a00b07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 920422491 1250 920421241 920421247
    0x51c031215030c1a04150507060b19030b0c0309060f0414010c050a030f0507120e0307060c09050a08060705180d0b07030221040f02090c0d0e0a021c03080103060b0a0902 74
    0xa200c0c980d510f103400c44518100100003070b2404c1c54410807601070f900c58658551080030003251041e005000401156226800029901c040c00d00050a21041401070300301d42c0000820070b20801140203a60f50b042a120030040d03045280c034200d20b5588800062615030034000d000041810001003420803054820003600a10840c120a00d0040154001d01544c00000c1d0401050b2401c2e88110300c82e043c00340c000d60b99510882c942d0417000101a040e81000c5070f01511040080c100800c15520544100e006140d9603051103e10b42420800e100c0302075008102240c10500500800c583c01000b22001014040301000c6000d4026000400b85807030180e01803c510b407140c040100e8680d05500500b2100140600b11b1420005130078041854101120000c006030215410880580b9019107590340c84114642e02a29110011205000351504c0080070540ca9005440c1881107160082c0a0040c000000c5404084503241d030714001c112030410320006e0582640c80420588a0f2254100c14010303250011007995 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 920423741 1250 920422491 920422493
    0x7080c011404031e020d05130806190c0f1b06090501050a0504120c020f0d08041203020307110103090807170c010e07030506010b030603030a2a1506051c03121503 71
    0x303150007110b00700d00051144001c0b400e00300000c90401d0720180141c1c000c141400914005560560144580d4020070072000c8002441c000d0410020b81b042c0c00d000e109914401409282909803624400d2020070322030f100f202d42210342d9119130455405441d40502329821229402c00800400310f4150181c2a5405d15003005030640180d00701a0107144a122820660400f41d0800c64031b81030a0900250301070300050320b0302420711b42030b003101d01703101c2c0030360216440c0c9981e60200b6911401c41d443d0840150700040781020030700c50b440148a100c502d007030809016544181d82c940240d4410100028154401050a03451508035001916070340c4e10741000030812101880c3c1c1c21941c43c00c541c0b00c01c850318401e480010500514000540b40110b10240041d42002010354064410b0b000401c036120820394241085400300440b805041c80703860103125000381c1e510500c582902030310020340005001750030084d4500c0c900c0c0c02f880c95841105d50103150010b4115880c1041c8405407043c550030300d0208a507054080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 920424991 1250 920423741 920423771
    0x80c062104170c0c130b3a12090f05060a0f1707230f0304150b03030d050711011a010c02010e13020a08090a0b0f06011205010f060e0301060305030306040207080c01 72
    0x140801d0704c1114805c6a6031052000b20083c6e0303041200051300001031035514500d00c04200e428005080361040110b0039207601c07400d1a00111030018041d034070100e801056003e4980c00c0030805000d000940d500741400c5007041c02151203171248007086810012500c09140c00303a03110b4413400c0e01a0388550411405820201130087c0a14680200000e0040d0382218030324110711044203c0d110051001c0b9090b0955a442d00d40301d04101e810300a004803143c96140e406100c1d601440141548415098002007a082031203004055051020700d00d00302d1381c5040000085134041c400c1d07642012100346040410b580c880e10041701d43e40311011415410100303514a43c1d900f032559402600901503030b030396009103590f503408245942d64072440c2e020b0f00e07460440c004039583c2d00f1200c10551b880300303060401c500c8503282086024100c40b0264800300d401014840300340103041d8450702a064425040f0020307c942421604e810351284005002d461145900048510400440c481074032085030080d4001c104114103079081e2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 920426241 1250 920424991 920425003
    0x150f0507050f0d0905040207050604030c14070b1305031b09091005090a0302240105060d0902060304030215090703020a090513020303040f061701080a030305150316080c062104170c 79
    0x8074001c42c1d44c0601c00f0415041a20a45815941240040045403a141c0341540c460800201c03e0b254080c60100781919400e041100f08000c240c0e9440503540c3d005a0064818000742c5900040c3c0310b500080b01c0c80001d00c2880d0031000200368129000403154403540c103454a44481e00c0640746140f8140350402c008540701281070149103021360242c402c041c0340004150403596091340c4032042c90440000612007403c0c404041c04010080003400030300303608a0307000204a07070401c42e021001030b8803800424003c07003800000b4a800103412030003802c9031030440c0c0c0002d20301d1130207001c0d030750f0402c5d55500000d410803040341c201c3d4071707003500507040c0d999070342e00c0320455252441240981030110317260f605110014410381303080314102d03030010029085800080e90110301402014204001c80490064103510507078042c041125a040130094000000e4508a5450b06140e9481860361060a080c00107071000900c81150b600341c0c0907610b0250a5650751442d280048640b0741c002c0d00071140d408104403c404000140c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 920427491 1250 920426241 920426263
    0x42403030504080f06060112020705160e1017100203150a080d03050903090640031a070f200102030403050d0513020307050f010c1e1a01150f0507050f 66
    0x1504d904c0e011000d6440d0b945d07182a03c001b400900000c103039000c007a10550280c0342c1c0c00e00c070b84261046a22400349010345035280f030700101d0f50480170000b0b004001c001c00010200400b410910071441c46141c2007066100d00354050060541c980010002c0c142402071404042c4a490080000e11129180c0268994038940d154031b90ac040303440d00e00401c2002c0d10020a803400c0c24801030490346014843c0c10100300700e0008002102c10210720b058401301c003800901d03020010b29410354001100ea859810013110180c0c0080811303600c04050024001104e0340481040105404c80c03e0912260001035481154500014112030003548088103100070154040010721421140a0701444a0b4445000603c4100085c4900a6040d0b0054000300118100b031500e600d0418414100212800301c1616528040c0900b00e0380d40b41207040c51440001045001155050b1440204064202d558140f5405d08161650030b44200140400c15041c2e07081a4441c0b41102e14841e0f119054400e6081c45c40310140e62018a440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 920428741 1250 920427491 920427493
    0x507020d02060f091905031e09030d0507020a03110d120e0918100b0406030501141b0f0d0b060904020d06180911130e0718050615070204240303050408 66
    0x2c0030450360360341115114040d60546000d080404141560110010107030340c401c80d1203000500ca2107450b81041d80c4c05621000300d421505a8030079210f8101802c01a00e125076400340301013030013110096220b0209035011340b13500c02c807650511158803000481e0800c034110300800d1286681c2a02c90b13515484201484414015200c1d14019210940d440d400c1c0b001ca10340900e40b980c4600221078034242c160f00314030072a140c054000110103850f5220582940c202031707800b07801c0031110700502130240c00d00b2101d541c01507100c9404034104002010800b5162140ca02e0204c095a01c400341c0362044e60f2480c00712010312000074400c541d40c030300109820340a841c3d03520400d907076042c0d00410045041e0300c40c080d809140780d20507850008100e8500802070b15072003003c2d07030344007841e81d641e86005520030400502015011001031a17205580d50702c820400d441004208074001d004600c11081c51964039003e8604c05a0304440c00b0a2100d007909071183d08032820602c00613043e212003800400c0c590064014025621820 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 920429991 1250 920428741 920428753
    0x207180f050f0c070f1b0335190e040603060506040e300c030a11010506011e0f0e09010902270a030f0609120801080d0f14070f0203010507020d02 64
    0xd182c800328040032070307078000461010081c0c0380014a84000ca03a0300184141c0051707140300304503600750105903225081264814091510420044280004811640341c1082c507401952060000706800c0e004d01903052030012003400055a00303600808007042e0740a00680200915a80ca041c4007010740380c15103045008501c0c0c0350411b50000c0001c100d07031450141c60390300310040c03081162203c59049180c0c03d00c596007910034044030004200138402008041225650388400300c1d100c0c0d11307503403c540c00a00450306220b05c03a20940b00c0d07010f04034400c0c4051403003403c00c2c51035511521030507140840c50010041d8400b80010000c29000c15507405401e031806048454002c4110880010700d0114241c0110f41e07101c0e2040c442080040c5222142c00e10980c03081d080821419107681c0c0700c40c418241103c0341d0f03000c1580c0c040180f03d80707c1c00300641c080380d055a140c0021950100d0b40098402c0301c070504220350b50700d030010302441440f4210305e0050380c0d268060001c0129290800000352600d18111001d001800781e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 920431241 1250 920429991 920430001
    0x818131e09200a080d03050603070b091f0201020d1415040612060905031b1b180a1a090a050f0115020c0d140a14010f0e10020702010207180f05 63
    0x28460824196406103004038000c0d0910444642d0042a034111603004034022800708400e40b0510010b403034500142c9001c925800c00c0001c140c01c2800f9900300c0b5080e08028000121a0395410014441150340341e0010b011000c01c0c0b0a04902910030b1440501a5908006481c00c10750114450184240359004c40ca46202c4008070400c000d031a81846a840620101000940407942c2d03a40708041441c070520440b490300103072600b04a501d0a2480300c1c44a66006076201c001c9041800c0b5104140031422036410381c1064403008070700c4103c0303c05400340e88041d03650030159070307420401c407035982d02c60400600644161070201c81e0302001d8101200c001100011400c000204100440a2860041c080c0c0d0050140290807000b80014800e02c1c403803e841840c038a44401c010250b00f404041c03102c60286005211110f02c44500c5030030350f00002020213a8625001c070014150303c012803a295200400000541ea40140d400100e103800d100fa0006084259400d18280031b11203681c1c02011100000b14040c0002d030340f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 920432491 1250 920431241 920431301
    0x5101d0c40060c0515150a080d020c060306030d030504080f340302030a0311120708071e1d12010e0a0c0b0f031f03050106080c040e07050607081813 65
    0x604403000300b00c0d5001c01900404080b001003580d9200c0380e01d003110121103a043e000130310380790040d238051040c90300691200c01d002070b07060100382d0000c10f041e109103145083c40d4011035524112001280300b00355603400030a0400407042d0498460440c90035440c0d8640403502c00d007010061205017000310b02c40c0c1162140d441240000c0f038107200c09070590044d40c100202c800094002d48000c040c4484503100400025041301c500002c1075005604c103641c1c18032285003c0d01e010705010710280b80010215800606992015030102c0d003010759017502d2903450586c51001e000300303000c0c2000d0b00c0008501d50030300d010a803c1d0080000d413441c03007500407000b00400d01e0752203242507411300ca00d451205202c60204002814840c41900f02c2c05c40c10000c548400529a90f9200c039421607a40d42c01c0071103582c22100f400342161815018000110406c1d00182540c5848d01d00010300a224200008000c001c010410400e42c0302c280010302d445540c050400310041c2e03941d110b1030b030081284070700d100380c0000305042d2640310101c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 920433741 1250 920432491 920432507
    0xe09010e160c020d111009050a09020c1204090e190c120302031c3317030c070b0417030c0c041a060d05101d0c4006 51
    0x140c00300308141c88000a84840046040840050104407a10080183c440d03283d030600c8140641c00c442003025040c410002c02c001d604a00c48104612030a0500c02507941421000071110b0425006950f1a883c076a094107200c82100010621500403c0025010446422481c2111000c5d0240c4907904421000d212212210740005024051140002e020b01840c4401d6a810305000f401100c3c14200714103000c850108555840029080c1c9580c58884503074901c2003500c0901c075100442c80604007040e44000c4c590b0006203d100c4520035a010304040c100e07424421540d05004810540b01031a4441c44044410751041c0b040040c0c1c0d1218885801c1d8a1101100f035650581e4903001030518051140100000f500d100c20f0316100c0b200b100140742d00c0c01e503240b6004108940030402d011400d86040c107041452154254071404c0001d940001d41482032001d42d00700c660200f0524103103a100c07000d40c501c59a0348a2010b1100945204102200302d01d090a451032204821028407201040d54554008030362b104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 920434991 1250 920433741 920433749
    0x6090821101203120c0e0108060105120415060b0d0902130203040b0f1801060602100b06070201050715110c1507030e0705041a060a1706030c06070605040507180b010e0901 75
    0x10000038070041c42c1c2c001900d60200c1c041e140c000c807221880e40344041260201d40c507510210b500740d810311180d560801d18846d4031003424200f182c186558803032130798101c4000401c01045a000744dc14000b07120021b030712581c06001c0c04c00c059030710341e040c2c9524540105210f00781a40b24481c60b4541d0300d02c00341c450085078400c950003480b04419840d1103004265620024000da09510380b82201916600400d00c60354006050550040c0701803c9d400344083c0440d041c510000340281d108000d1140540d07000821100050760007840180c0014144c1c00050003081c48030070281c2c2c084000100c9150115000a600c024102080c000800944503a030b802e07822100d0341c203980b035060342100e50204140d00c2c05900004d03101d2182a051051035108100040c1c031f41d4040e24100001c14004100a508a0310340c12803549c5c0010250018003400c903c8000080c414003035414000e00140e00c0b000001c081110620034500200116481003403184080d50302003028010032040c040c0000c0342c042d201d0303d480c81d014000c54100c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 920436241 1250 920434991 920435011
    0x50603100509133207060203191209080414100207050402250b07080901020a020a02130f05010e061002150705090d0b011805011e090b0a0306090821 65
    0x8680340034180007030070200408a49104001d08091008950719004c00d00e000a81141403112140c2824a0320310590750b2200350200c5544090028001503400004907004400206a074140c0b0070000c29084480d07810108036080d0240c1003411202c2004550400341c0145d070b51040d180301e0700750740790350900200c0010801c4880c01680404410000350502d1f45c028035801c0c2c3c2903035003042285c0142c10803448800090701d040300ca26204000b000506c560105d0317003030740020f0764000035860081400d200070766036000540e01911580c4414406030441d070466110400200040d4003e0145680d40c10690701c0c00f9030112009030203083c0344a91004018400b18600700844483e0481c40002c1c1c030780171422195a0400b15003160440d01b24442c07400804c425000c41402004406004052203861181d035101340c44c1e06920001440c01000f161051a521a50f002c0080d90f221f0323240040d419030008002440da00c17081e030001c1e11492900160b81c0500c4a810000c0040d9441140c0c0307810302d034149004580c0f1000e03046a940c1e42c0713 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 920437491 1250 920436241 920436271
    0xd0b2707300f08133c0e0601030b040203090a02041d1c030f0f06060e0a1d13020604030b19140601030e070b07060b0406050607030504030b0603011415010e0109060210020d1515020106050603 83
    0x101b656071041c070703039004581807400107000c0b4081030202e0100c1c3d1040d1040e01c2d407503003d01c010394218906402510f08000010f051001d11103811094a6034038442d54030302400104840c24400c0400d4841da000d00c59104a95900b4005104231842440c0202018022100090341084201c0003038180812010300315540c51001409440d0202c0d1105800000900340340f0384641d007415000702595655000d400614000c074450740c0039003015600d200900c40c01c000c001c0011401c000d02d001403800040364803684030500b82008100041e0a01940e41014030503080b803e01c2d69004640c6078240009580f1180c00000d007500d08000c6c264803601004401c3c090b01c40004c0024808104c203000082c2d0b036400f0710340c10100103400460802c1c00c040d122190b101c3d00712210369a00c0c4070074582c020f83d50792008114891a400703082c000c59040c10424002e440380c80c080d0170030400903000030300080b400328190300c840280e070802c0141007144c0303448240e01540c0a031403981a600540c00d20401007424034084044030700844503d02c0d0154 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 920438741 1250 920437491 920437499
    0x14060a0e07051b33010e0f160309060507050a110f071a19030905010f090b06010f112d0601050d0b2707300f08133c 51
    0x80c15030150385041050340111408aa890001d00301c1080a00000600284c01c0158070400e90000c520142c1c00120b41c6e80c01365041c01180085140207a4205e03540103540304204001010a40150442180007070106d0b1030a000c02020f1540b007006040480e0413540c402112a10315070b140c036924041d8200d00885900225070400c8400c90001800010300c211100b024100329840704480c500d02c80700030504000c20388a011240800c03d081c4140c035940c1c03008003402c20803490503440d81d241c01d100c01449541407082007020024001e00034000c8488a030f080000711603120b0700f50001c078001e9014041c03000c1c0895903078000100b0b000b030700404c54a0580b040540714608228840c3c68909004401900b80440f92030584010b8a107080f014000360f65a045000081c00c505280c203400450b00801e8445000c0341d00401e0a004a00d041750340d9103403406682041c400304807448035080c0a007452154052908110b0044000010713403400c0c1171440240380410b080250700035000400c04442c44555a610503a0380144507400340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 920439991 1250 920438741 920438767
    0x610080f0601030b16141317011a12030d0e03090f1503040821040f1214030105130605060706050a051302100f02190809030601122102010f14060a0e0705 67
    0x4480d00d0070b1494010703480011b0003c0e180031580078003a04010000c40200c140f01340c1c2c1c10000c8070340401c42050020428064103005903501040d14503082c1c1c0c8a50071610709150518420001d48101d00d4218a003001500b0106c1c40e42592030b0b005401e554000c40ca83d40580f030151a0140c0748039045c42100c4445442d590700d5070b0340c00d100b0b5803120b0449014503072045201c02c242c41800401a1183d40f2800002c1006003c03414000300e0846503030320240c1001000c9283c00c51a041c40004d030f904648040d104c031400d40400441c0900904050f4000b290800c10200d030790781c02e00c4040c0d08881c0c06042c1d5030f0010880e40d114440412080304c05031034040d4200c0b4811141c0203645104690719020340006106494607804086115044640c003408280e85021001c0f410f078040f40f03000d0228500414224400c00340506460350f840b0300c014408131034808096061510411502d000390012416944038440c01c02080e1200410102001ca0584000703010b44060900840c510383c4c4000c040b4010092500d03040d041850346007007a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 920441241 1250 920439991 920440021
    0x2040509180304210309081204050f0f06030709031101170402060a030e0f0d02060a02030601090b0a091220010c151e0c090608091b10030e0610080f0601030b 69
    0x4541d00707100070800010745540d10380fa800b004526a41802d034102c645401c00404541440e00005041d4006111680b14440100125030484e24280d4041c034505120740d000600003041304081d03541000c0b0005c100b020665124a00b0000d4a124050044821000000448100300b248440045d0f40c075401000c02c015181400c0600700e0880103240200d04814410701041c20528010802c00082d48a00c0820030100d4061110591008040741d08500b1460250f00003010352559200e001d00c000030020385583c009200343c000c0701c0030705481c039070181031180a4601044164078201c00a055980440e8444e2003662052680307010180d00b044400d2080003e141540703009012401104040c0c02c0c507a1104c400c14005400b800e90784008946540a0491910801610984009110980c1354010074507d00c001c021030303040f00c405070400b030340c0c41d420b10703400f44c0c50a030000d04048600001c14400c0800f009201c00c1d01a090030b040e0f54211054070400b001e00780040d9901c041c01c0c00002c100044c000c4c001a01a00c0031090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 920442491 1250 920441241 920441281
    0x150405010e0f0102250203030304020103150b030705040626061306090e100e240703180f050d0c0816060b09010e01030b06010801080c0907030e0723030102040509 71
    0x1d007000700d500d00900d0500e040349107018507500820111940c600c00640c4078891500380981441108040c1d000940b03a00c001480281030590f00e100380302d00c0c105000081c00107880c40751906030792402c1055001e0600c0c0c20600c2100d000494025070350010717800c2c1c0440303130851150100c22042c194590904012020031043c1030404c4044c1c0e1000300003061031082c011a0040a01e08002d03001403014825000705442c081e802034081c561006000c0c420400e2100030040b8024cc109641e20035540740d1486c11009407650120b150b01400d144920755050100701d05001c0c400603c11400c41d8883c12482005aa00e00400903001c2c00061051080e4000c50020f00744c5014090f10814000030020020000504000d4003a04070300085c003204401841000180c8002e4ad03002002420041103542c0b42803001d40e910f04c002c124880c0540306400208014034021780200e11006250416a41400c3d140e9181444400304245007040300507030f01807101c50908042c801c0303c0c180e81d00a0070031800d60380d81c0302a50591314883c80c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 920443741 1250 920442491 920442493
    0xc0b010b0d1d0a0f020616080903070b0702090406020a0311030f09011b0c020d08070f0c09050c251a090d020c04140705070c0509010e0405100b01020601060e040914030a0f0e03150405 80
    0x98001087c618064540d40360701c501140d5445078880401d00d031030861346410038500f0000c108006400350f0f46580342264029840341e03025aa5805040d401c030040c0c1064007151820039004428040c0c0c40d07007400e080ca40706280d804000c2000c04104000501c1c4e1000340350700840401e40c0443d0b01405070a12458811405009120781c0d1707d842030300e07074071550a81d01162050707801d0f022020050080303001c04c0c0144c90704041b240c0042400c244885900203062410900041c0342041c0e9905010300308030400c48500041c0048440002451400400054450b911801c8560041c001e1005903030451a10b0302c60486244409025024156500c940a4800d41d101040913204501002c0c40003507a03603107000340035003c0c1251071044155401c10b498424a000c1281e0600040d2034102141d03181c503640d0004800c0e0440754240f40000b0f51105080104008115080c0080e0800001d52034000380c1620010050580b5822035075040040380900000300c0300040d00035807036503264010f1654030b0a41c2c400a10342580181c0548 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 920444991 1250 920443741 920443747
    0x1801020c1c2609011e050f0a030902100201320f2a12011d040206090616060b0a08030c060a0b010905031c030f0b01050409020a0c0b010b0d1d0a0f0206 66
    0x3941c00750001414009a5070002c01c006041c6019592142a081608035040400c031640c0188040191942c06000541100c1c41004103d0708070fa28883d80080700a2074024000300d544008100f4002e0103031a48005400840c14240312000c0e0074a03081311803034034841c04d07030b601000309845110105140d410042c01188038000c0ea80c1e02001104068440c1070001c007281d68250307540d00481d801020340510142d00500041642c0190074492005000341e0b10b030b206504403030321a980e8400500148643c042c40405000100d10701c058802048103961001030840703011100e4440c25550b910610f42c0e01c0c86030015040454002c000030540d1a0483d400241035914141414003c0ea41c880c800300c3d18100700342c001107921440f500c01c0300e100582c0521440e099503107002c0302440420264030000c1c11600c41d61042860b041d5000a100140707a00c104d4a111030b20f5030000d03d42d109961b54100d0311030160420041c1c5003105103061310400510903445141c40400142344090400307600f41c0e445107070f008c1c566254182d030011010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 920446241 1250 920444991 920445023
    0x1106190c110a081513052401061e12061806030501182a030204090317010b1801051c140a0e0c0a0e060109081606170903040513020c010606051801020c1c 67
    0x1c1c0f0687d100741c0380d41811710001b5101c0041003020340006a0100041c043c1d1001030800f2125840b40d00d0152952a060a0131850f0940384280d0003860b46a101942d4000e1205203402840744903001030301128000c1c0b00034480e4035100c10501035414040030b4000d2181094204402000340040540000c3e40c40b82403250000603900d401141c01d032103140208a0004c0c070f00e450001d41001c40707d1413a5003d4195080000d0404000c028110820000f1071540e505222022542545004072226500d282c20960002440282c22012078001026003d031050300d8982c2c140040b00c0404c000009403a1554000245240c2c001d6140007145409000c0250502c2d0400540001c049000441000110380c440b041c04c02c0d0704100ba1030003400604190200c08100c200548080610041c4440041640c0170f40d4000ca421501d183c6008030190000d00c10b03065070b41e403a5400d0810001e940354103d006400d003006400d000c4104000782400480e2100c1c081d010307007980f1041c4032040ca500440e4010030144151300c1a0701d0f4283e00700340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 920447491 1250 920446241 920446243
    0x20d03090503030f03180604050d051e21011403190213060e190504080d11040f091505030d090b1b06010f03021504060503041106190c110a08151305 65
    0x4080004a13000000107000200303d8404208450418000107011141090b5071069140c0c002401d00004125011032510b03100c2c0b02003240745000d203182ca0f51081c1d42c1c2800100041c2c070203584801442034000c0503c00010140d10445501d005000c0050103400d0300340040c06010b888185d10380f0142d0304414a0440001c00e00351510a00010340210042d2054a2420000402503421540009c13404070f401c00c2c00307200020b01480c0c01e449114101e004049810601038030304290901943d40013005503039990700c00007200001c60340044003080240764107271540303900d64061643c0c030001c840807000082d074000b408000200c6140054440307001d450103240c02c0201280401c618020013070b00f0400001094500800441c540729480f14510328040e07079024209444c024002c1d009010051010f0032a501402c4215119540c13407044440712818030100c0e03100c2da11004402004003049240840d55040b120102d150b0f203140800010701104d600e007009107242c0030b0941d00340401344030103800c00d10420b034204c0c00d02c0c0008030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 920448741 1250 920447491 920447497
    0x409020a03290f011403151c2006070503031b090312030f060306041a04051c080402040f0608030a0c110301051828060c020c03100c0305090c060403020d0309050303 72
    0x10307070441c2d400505040400c00c248601c5159625051000e83c1d5042c05d43d90003000c055a91002d0554540d507400640303800030410303000003000c584450844d51042081040010904090071211907a9158071590306401030103541e2203818009880d59005000041d258000c4416009402c00151020b9080107086d10201c1e19240000d04001c41c160800300c2000400005122155800342e421001030050f8141a02e412080e50415840c00c601c1c094100001400c0c007004100c05060756581c4400d0b50509403240390001e0440e41e0555089110b00c3c288a40c0c144a51a6406010309884848018515120304d150080c0ea900407011030895031054014030202040c1c0d800e100300d83c400e840003145200820b480f5121a402d013140524501080106072145410700c2c100142c01c030254591028002482c8131b080c0384103070319100a0310103441d458410b001d10406200c0040d003014a20b07850b652400e11140d1035000c043c3c0d031543d50704100141c01680a200c02c01c0545000a4000d10b800d020381002c1103031a0b205c202090542d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 920449991 1250 920448741 920448791
    0xc09090f151e0405130206030c0c0a3008070203090f180703060317070510180209040c05040c080603060402010e01142d070510020a0e0a03050109031709030409020a03 73
    0xa0b035071194070340d107007400d01515a0280594030701d0603c07034000c2d42c0090b00c6401301078a03510b01c07030502240340180740f0303000c006c04144070b908200d41c050345d4a44d84051003e03050719042d40003041c95095540d58241801013501c14051000c1d40c01450405e9918001e00c010704d103400f0012640301e20001071082d0340c1c100250b9031501076000c0c1d6502090300e500750705120a00318000d41318141c0e240020400000407580c0440c4d04042d2401603e000706805001c00c807200c8608840e0076001e9032200280043c0000c01052004007400c652060b80d0900071070314203007800d0300c00140c03c0310141d030190818000500190700c580071079a45031005050202d030903580558225100d070400b855084c02004180160b142c10703a903090701e0060745800f100b005450410150744040c0c44e956080b0002013030030b40110f05190003500414003492201d0000c3d1484244e0340c1d69082040c0a44459101540411601c143d011005400b6882c180c0c880e000b1000113524003490318019500a5006009210406588941000c6d00e071380c0401443d0410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 920451241 1250 920449991 920450029
    0xb01090506120708070c03080705031504180302010c020a03091214030a03150e040302192105120610091502101b030e01022d0405100203120c09090f15 66
    0xb81c40c001c0406000c0c040302900a0040c06641d80c01c02c40025403080a20390302031242d103000d070b489803070751100c40803080d10100241d40e101d82070036240300034a9810b8a000340040e0090f4001d2103038000402c400d98544514110180c000340d810282330002d84101c20316803c42521400100e11001890180705080d904540c070000c0c006620b844040204c0c40009440c4030140c210b820301040523007415580a542d51100380704c180341c0c2c0014407403040706005400201c1c48924134015a0803603030b42543c000041c05075100700000495612000b010640c1401c11440309025034140d501c0d460302c8030313051401225403902072003e0b40003144119900c2c0c90300801d1902803207080300c5007915000604a0300e002e000d420b0340c41c000c0b030644a0341c1c410703c0611042c481c0107030111100703000b541e2044100c202035160700406200b03c0e00590f40180e01d0440308039502d40e0001c010010501d600c0d0058941d5203c5c401584154442c03400d6081e0300c070642c01c02180c0c82d1449071054640040d0b17140d20201c2404002e40224204003600340750301d021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 920452491 1250 920451241 920451277
    0x5041206021b07061d3a02042301120506040803040c030204090b01030308070819090224040f0e070507060e012a11062202150c0a03140a02100b01090506 67
    0x140c0748206642d0f07845004121242c0c0c1b4501b05c07030882c200c079110510480c00028000740091210060843e090b9440c0c6c190042d10600807203103004d18001c4042000f04040c1407010352400000b40c0020700320803000300c0f036600c240075241380d0319203407900d08141c0c0000e801590740400307240d000001030f0745503c00c1000c501d1244500c4180c542c90b50801600154005042e003051010f50010030800a41c1c404018220411081c0009181001400071444a1a00000c884e41c0c0303000381e020510b240c41e030005c06001115800d540340e035115516086200c0c0f078000c00361040800700c0e0041c404400003d00320f40110403045070040001030340030000440d043d0341c103000040b5041c110400344080d0454607803001100703112220404c01001a4103181030b000c1c1c00031191100c9980311200c1e0810000455071042080d04a00d00e441a02948030001e005900c3d8540050348000c031f01242d0b0380300c0d00208149003c03065401000054001c3c1070769105009000700a02000c4510a0400c1101c02010920b0780e01d032806801201c8641500d50b01c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 920453741 1250 920452491 920452517
    0x309090c090617040b01051c0c090b10051c05060607060c112e05040c050d0c0815040201050d0f0e0a05031e0408060403050c0c1005090109050105041206021b0706 71
    0x45100742c038031883e034042810038081102041c0054102c0b4111182030390011140c0c580410400c80c15611590014031801c0010710000e400f8007030b604a10036400301181c41001c2e200070f40d6819103c80c4168010f4040001c0d0310001c101c920a910b500140d400403000c2d03d0340303140ca0701e2980c458045a20800d05030300456001203006e00c0151b010003a01c20030b560861001e011034008402c0c04c080d00001c94a0341740c50b0300d84070710005d400c104500070414001d240c0a4980a080b010a1509103000c1c803035401000740c9407007440b882c540070f0609102d10a006035010b840350fa285c240f24135446030142c01c1300b40c003da02150303d8460748003600504001301c200c0c850041c2e024546400d01c01c141d010880c030703080c00c100c2c0844070107010900c403540700460b10302d4020303905080903907031000c0f160f03505c9042000d5015030b50340c0301d2170100100da40540c011006004034030090340c450010396140d40c01910140141e0040301c01c0612200208000201d4950050017074114421a03110301455468240d403400c4d0140d0003080018010342140e039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 920454991 1250 920453741 920453747
    0xd1b0c12060e0c0627030601080f0615060913110d0b04060e0621120a05030106080603061504020a1b060b0109210209070c05070e06010f020f0312040309090c0906 71
    0x382c6a4190060032590482d10006851170040003807201465070701e2207503145400040c003c0c001c1a0714003d020713108107603582c6807500c2e10341c6c1c01d010025880d40a110b00050450004654601280a0060241303041c5500d43c41484041c64484c000c1231851650351035042502039500d4082d195858003100e000c50401010f83c2030200703a4a5035031141c01134119a000340481503480c59120b090f0104401d140700000003440b2507241c03070300c00c120000381500c030000240c0340300041c2d2080055068560702e445a0b100e5460715400d05039503107000c50302c01d00e2100300003015440034035154000b01740f1202c01e464440c4104001d8910190098080c007011108690344041c0c00e0300702d5801c45a60001030410945441043d140d13074039a8142c40080b00c000034843c144603000110914010851440916013020884810342c2e00d910016100901c1568480c0c0403610000e080855248005400340c01105e41001942c100031441010412030440604110140801c400c40894007901034403d40380390803115030391100c1d414a000710213 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 920456241 1250 920454991 920455001
    0x91406090c030105040218280933020f0c030f04060207050a060c0f02150c0604060b1909180219031e02030604170913090b0a0e0d1b0c1206 61
    0x19402641840704000261ba203e40490551520038403c40d2060381c0c0d101c0711400f05401d0514110782c230b030301c4034071064900a08603801150614820302000740c1030903006036640c82d1000224400c0c10307140b50711003041d68074000580180c107025084d90003403030034020f0b02c2c9d907600e0568004c00350750f4200840104041010550402284c00201816520b011000f820600c0040440010510141034034007c1040001151110781501070f5075208900b40c1c80d00d84101c00b45550b1504810303a0144c45050a207510712005141c58420301000c82040a010740b8154688000c1034041c06c1702a41500c41c50b1503407030700c05001d6150040071b0140b51f041c080b1000141425072800482240d0810007540ba000d00102082c001030720000307003845e0031580002c011000c034103408294a85030b104410070150000035400c140103003456150000c02203030b481000c0780c180b40e0b0b580007da0f030215401100348102c980d0000c240c0c5841230303000340d443c04020840b6501040a11085844411100103650700c80d00705000c10040141c1400880c0c858 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 920457491 1250 920456241 920456263
    0x121115190e040606110a060b13060e0a0c020111070201180b070503130b0f070b130c12020a1a040314150f061009050109061b0b0c0c0d020d0815010309140609 69
    0x18005d0043c400110581d103098403940104140c7e41d603ca0100c169980e40d1288942c205443c4082c04995100c0c0505458035006448018030305040c840300c2c141351801070060440000740300c522241816440c2d0011524010300b151400c07005c0300c60b807401103a030700303034583c000c041c164021b90083d540d80e4441c03064005e5001099006140800040c810b2800440c98801100d5026402c82d01d2031060b03860703621082028004680c00106201044032002400d4966130f807510305024001c80b0344a290542c3c0c2d10034484011004440f185a9003000c100900005410b401d40c144007980c0002101c2000740414400703007554000382c8031044010700c030104100803460111141c6240d0170a07031501c80d0102d0700c0c040010300282050300400c1f0521000c1c00c0c002110807289003d0b020b1700c0b6045034211f1920301b4140456101a44040180d04160184500d0750102c640001a200101c2405948502c1d1598404030743c402d10000d078011140c100f42c0c5601010011407801120b04c0804c0c00d180c4060701180c103000c10042d00d0302c0c4074014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 920458741 1250 920457491 920457497
    0x10f120207170a090611060a05150409060617032d071202010603020f06070b0c0c210a080c0708070201030506040e16061e1b06020f040b03060a121115190e040606 71
    0x300d0306c0ca0180021500c503801c02078800c00824180c59002184240c2c00c54401a0780d0428501a410400d0101c07940040c0116a45500080000e4509100c03041e00c0b0302c20b6400025524a010010b2440117150029543c6040400541541010b013683c1e42c2c060703040408182e43d00181c2d1149014025458017410b03060071410216003d6140c4601903556a0020748010600c0c441c0e0341002c10f070203400300410310600c01280800083c03032250f0200070282d041141c1100e0441800a400c0c0740010311807003550740c00c075403000340c000f0b00003070a0a02e15030044000d82002081c207a040380c3c80340680c909845003000082c0c00c40c429500c040c0c40b52401c00f100142071544245044d03008501c0d019046825641002c4590802c0c2050400f01601001e1410080064420b44102e110200340000780019810010000b03180160012520031440d1a5201194582c1446542c0d0103880501c507442c02001c0b902d400d28070980520b0003da503407410405001c43d00320180260b8010130011415283c84505907140c98842e21000d8aa282 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 920459991 1250 920458741 920458757
    0x10507030203011d10050a0305010213120c0b0d060e0c071403031501080c040509070f08070201020703170406200403060f0207030806060c0106030501050c0a0f0905010f120207170a0906 81
    0x2944050611043e48115400081380d0000c80c0030680c002d08102c01418024103001c4605070740e854454000c2d07100c400e4a0301c441481c210041451060099a80540c80e0050040c02000781000816045580300000403546550b44040020318100010312a07807042554003034242c1c0b110300c1400c0071810441601482c2071960010000c000d050280da803030213031307043c8020b00c1c0c11081070355500942c8000b849681c00c151b030320580040401203042d41c0800b02080c4510305a0710124192555003040c2c0c242d0040d4000140402d50320740b6800f84103406c080c4100d074464000e070004a5841c01c1c6900b0500380a4480242490f403500c002020f00612409015110301002050b0b0218682260b540f4000c00305000500344a11481d40003c400c1d20201094000902039070700711000b08468240007019110350b41c0444108030110301503070102100607002e00d000720129081a140c2c1d1600480403001103809111003068100311650070b100d99808500c000c5115141c013400e4040850f036030a0046400b1b070144801e94482802c1083c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 920461241 1250 920459991 920459999
    0x15190c021215370207030207060203190509190308031605181212160308070f1d030a0c030b040c05100504030f0c17102f07110a0308030901050703020301 67
    0x40b002194403140000080045808590280c00c01050081c3c21072160000038150003060340d400d0b4028942d070392083d001c07142030990314201a600c03030140c01003000c412541e95000c2c2c0320080c042c07001401c0511000303080300c00c1c451000101c041c0046858200751101c01c804410848400c2159907004504c0c841c9040003400d02d92405071f120b47d41d41c029202a03014801d1015031f29410501003185000410040107240d031681d803880707074442442c80b4a40e4103800060f030000104075070358000e054603503581240d991101803590500c0e15011100e10388110040d014402c031700c4008045030b0300302c509001842c03203440718000e43c0c00c05040c20385058a40d90840340c8190116400c001d99590060121411290b02802c00700c180e03403c40c2040204140c03a58454840300d0b28050b14151590700101e803004040d903428400304104400f803c1241e000044401240b559688079605082c0301c1d900c04001342c100303e4070034803c0d0045010b05c00c0206036002c0e50740e402100c0618011080c007102050a014890b44030b038079483c0850640d0702d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 920462491 1250 920461241 920461273
    0x5010c020a051f0b090903090a090e3f0c0f010b1305060103021306030b09090d020d08040606030611070c12110904020411181c0f0215190c0212 63
    0x742e52041c40440c208040f8041d950081d000b070881000c000744610700500d454a00303903403654000141584511620130020428809a21450103001c200c100200b00303403104040e261000420788610a22020b80c0040307114500301032040d0143d003c1801113060b82d2105503241035280f0703005c20503144a00603410100c10721125120b421030841d007080e80b07040c0460ba0b43c4903600141c0c020704c20a41181c0c03544241c00b4001c115a80c2580180070309030704c181c5207000c00d592900c0f20b15866804000700c40005800c00c03001603a0b1680b0491203103402c81d016080c001841503882e42c50404490020f001c14032200c4d4041b581c4c1d02070100268541e070003000701400242c00540296100d00c80795120300800c61150038000045010740d00c0e80e42c004640c014420350306540d6880b8441044e0304000501c0c0089118442c9041b0b02e07200001c003c08034076081e503400f0001003840781d91350b420000341100300e0180e0ba40610301800008001e464801c0705051980f000d448503190903800d801030080381d42035404150219880842d440c034200034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 920463741 1250 920462491 920462503
    0x1080403050d0209031002040501024e0a030905070b0a050313150608160f05090a05070c05070b031e0f041e020627030615040209040e1905010c020a05 66
    0x545454015542d5002108000c000c0c05141c81e5250544200d80380a11403003401c3e070091042e600c09808a540420412264045030010a51480c4030100300c070340e0008005802c20600c410440d181d249007000c4010f0501c40a19a400c120320f01c500103900c83c034a01041c004213002101c0501b1100780e01910f00501c0c01005001c610001d0106841564402280c00503c010402050203541c80345d5024866607a5032480c45030344501c5003040d50340082006200040c0182d101410904490018200c2451556441e40348002400c0c010181c0c000d1020400800001076070500c2000060004a800652242080d0300d84400000c03400030442c88100c12282400078840c20114090760140d4400c004514086030700741c00c0b171082401808020341000003c0351051158000600d020003038a0001e283c01041a9418101941c519003a80d9040240702040c0d9010b034181000c2d0001c004503040079001003a00300901000c580b80c60264000c1d030303112030030b80320420040010a000746000301d8081d200900d20280684c440d161181 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 920464991 1250 920463741 920463743
    0x406090b090f0a2907020c010e2d0d0f03030207170412110a08011107060c050f030c0c031c0e0c010306060e09101a040608010618171002030903091806010804 69
    0x2003056030039040541c598800444200101111341a80d41040d001c06580d500f144480540440c5107031800300c001d8100150007541c413071200040c00d0700ca0781c1c0f520309084442c039009010a0b0002c161010301400b00b000b222400c480c80c0d00c20b42e40180d541a56007840c5080290078214100e024800300301c10015200c02c0d890301d10800c0e070482c0c88035110780581c40015202940320b900c01201075003484251111840c507000a0700d0441d000300c00172301071039240c0181140d152041c03900d0b5041c0c9903014404a401445010041d1515038142ca00f1646041c050030020900d0f03100e654041481c1c00d031901c42d1201000021b00c11b00c140f280d400c0c2401d015203814014003030a090303643d040040c00740005100007014074503e00889030003403940e01c054045007140300160a17015405400f0b143e012418480001035406d10035200c101c0c000724800001140c850500176808031103920180024444d00c142039184031151050301c001c0d170107520388400960781c5045850500c205090101e05042882c02460108483c03641c110703411591103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 920466241 1250 920464991 920465003
    0xc37060f09140109050609070b0a0c060908030c3007270303020d08010b040e0c07050123060f09040213020901090e010303080106030e0c0a0504020f040b030406090b090f0a 75
    0x41520109014010000c044018042c0c007203601c03450410100640c000c1d900f9501442c25039506d83e440d903441030758804071482809165802002109000d0f849021480c6400b4070030300c008280100140c80700324040e0010349103403400140008034126050300c204042d41d41c014903443d00035420300090100180ca104010450b10038803910f00c042042004e0019903d500820310f106140d12010b80700d08000750380701a203040d80404510380d2400410302d45428003d68007111151110401c0a40d541e000c142c5154000b554102c4140d901da1141c000900100070000180c00d203140d1038003003d407900c1c0f01001400004201c0e072034010b06a280a020140c0c50303c08040d4031048201d4800f41c0c0d6803280c40c00403134000c0e025a00100714030052000210800d940104030f2170484510781d400344090058004407a441d01c40d014860399002c05441000c00280c1001d0300a080c4200040c1d04042c00d0564030301e05e980304c0e9030040b035080340d00c03554403403100382040442118190410304403002840c4003004111083d91b80c81141d50040d1030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 920467491 1250 920466241 920466251
    0x1203040f140102011a13021b07260d050f04030b09010b0109120507210b0f04200607020d110d0c030c060302040e010b0310120305090301050708270a05030c3706 70
    0x146c80c14540403500340d00072802c1810b00c0c0510011056465030014041c420011440b51213a03110071012180c1144038824a0380545641d0420381d80650b01d680c0302600c841e0180b4000d010000104505c040c01e90310900307403c0300209041440d88001005200d207038002000d0b04034a1800140030440001e0700c401603030280c0c0490307603da4040002071211407082d40e10051a500b80401001007401c590407103940246e108045a03004a0004085031510110404549801400034020840946055a80030880502030440031040c0c2c00c1410100b4084400c0450a80b0114128002001040741c94000e090040103d4a001c6041500b8920401110fa4040c450140c80380408004148000e858480c05001400d0f41c46241c0b0404040307140c0545030b0740081042c02d100e546840300062402c2d005990341c0c1d1091210544070341c03c3c0c1201c1c000b1038180c003090750b0403200140701e03039800310b070000d00c0400013480c00251400003043c001401f290301c00402071040344483c80c408240c140407000d203808065370072407480d409403010803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 920468741 1250 920467491 920467519
    0xf0406050c0c12150105090411060318070f030302061605090d080d0914060a1e090c0312090e0a090f0321051602010e120a030b1203040f140102011a 65
    0x102e059440c21032554040c09101002c02d8800b80011000c10820800c0e420142507a600d10400c08241ca04a401a210143c1d20346852102e00d454402141c0c04ac5581421121000c8400d196602e8549150421b40864440c1c4009106051701000866405049030303200f8609440c0e0340c88000e110340100c03c20107000700d1400603590300308001c4005841075882800340400251019051802d181104c0c0c15181d8402e028610100d00511034901403078491032045a00001a4a182880d8100904e540c43c8281c1d445c065000d0048005501202c5251280119540391030515081c121407410102002e801e1584c1d49180484820008483ca84414031203500341c185260b46100178007520241c3e2602500400c1101d290000700941a264aa81c00c05001d00320380c000c0050710622003500795108611400b86600210500820b88014071941008244403409400c814031085180c51040c40c41d0480d400150142000304c80501031043e000410000f0100248003c0c4142d5480daa41074040c0c100c400903250041404420f041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 920469991 1250 920468741 920468743
    0xf010c14010e07170f0c060906041a0a020f0d020a030f1101020d0e16050f0f0a150c03080c03250504080712060b0d0503040b0d090b070819020f0406050c 67
    0x480020310800003031000c11a40300040742c58aa0314041c40700c0400001da41486101d2001071901c8011203a0300040c49880d14034020031020341c100180c3d880e8030100402001c2001204d42c4c082d416180d80240741640c990303c990501a09040144c040703030000b54001c444880032075600151203010542c0604000c1144812110304641040c50032600210135800010181f41c00341c06940280800c0c4c141c01c0c19035414000c2c1f00d070060224280ca10500d070b8410aa00c10840003468410000700f590b810040403d0243e40d038441005021008500519000c180324000641c189604030403400d44c4149001c18645c03851030030303240289008002030140c28910401505050205000e6002c803006040e0101c1110b0030590741c0d0a0b4440c0d045600c50040f41d140c0d06003030f26614070381031040000d140c0f10f9001000c1c43c2400c0c10058542043d400103c0280901c039202d101000200b00c01003038280c02203100341d4600b1140d1900c078802410420a170310700c800040303204001040f442210003040d5425940d00c2d15001da99840100b03050b03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 920471241 1250 920469991 920470013
    0x31104030605150907020705031b030f0d050705010b0103050c03271002130b0301030f2004020f090f0d0201081b0c060a020a110703021c1406070203041805060f010c 72
    0x2070078945000203001040d005054102c1c02c0c0f0360100c8000066a4171103e0890312610507108250305507114584c01d1058540c0f05440340d210700e078013a0403116000d84614082c1d2404011104c0741c2c010841c00240b80041c01028010001d02103000c2c2003c2c030085c1852402d030201031200402210908900107108901740a03940c0c0f0200c2100001070480d40240c00381e00840c4025400302014100f40300c40b4203000260344820303400340d80c104c0303400c902405400d00407138607800002e404001000e100c009074010724983c1c80e03580344040c0000b0401e008050340c07645210720074001d0401e0b02c40703901403094203c0141000140c3e4400e00f6075600034101c2c4c1210104d10500d090140c605d001c0c1017098403050048008000014450758041d094155a590751021810514030410343c80c0c0c0c0380d03804041c0d0041100c090308803c10785400045c40045200310800c5060318140c420a07420302c13100b5030708800141c10009040081454116041d000360f01000b504200d5820300d1307030024641010303007001b05040c800c0107040d0790b050111000301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 920472491 1250 920471241 920471243
    0x9030e040203040503071703060415180905030c01060f0504180c090b0f0d0b04060b10050a0e0d0f030c06051b0405040908091c031b15050a0f06080328020d03110403 72
    0x1002c0f8076000e004580c103d546c0c00440c1e0090103545000c2d01450700710f500011180445010401c2d2103c3c80a4cd405840041c05200b041900d00e440100a09204500b01344100c2005000420820380e0280c103000401c000e0b95024490318060818501407000414030f200508007c0315043e044c0000c00701483d102285402080014059018a40744c84803005c1c48908100309110742d02c110820000380d4180d00820444002c00341105e00028028001c0411071402843d9100c00300320700070320090001d10207a903034100350302c103100c030840000f00c100c064801000024018942c1015104189002e8520031030340509044c0150707ca42c42c030a54031202c0c45130500c41560104d59035800d0103408205a07003403004062500215901c2d00701d00140c422100c00d2252041c0d54500f0150030b40c0020181c0701722000310f20751009010040c001c105500e6131510100401d2285101c2d560080407544050758481620000054400c074048000280d00c1d00c61020200c0c1c00c2c0d5000c40c922410318220306001490003441030358520b5501603604 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 920473741 1250 920472491 920472503
    0x6121505041d0609070b0304110d0c1d0603060c0a03020f040e090601080c031b010e0a05033909010e07050708031008010e0106060206012105031201051309030e04020304050307 77
    0x860205540d4001002d49001000034040310300f00d444542e5840e60712001031040d00340600041c8081400945a181e158001510040900c204400e0540710206144800d62086802180100702a801300d07440500480c4d001720102c026143e9450b0001421207141306460380e00c801c0590000d40c05080003154000d85018200110b0020483d02d420203105a0f5410b003070041e44450302c1a840540c07910f04e000034150040d221a10059020300e14480f0065454090440041d6070201c1d58ae00e0203e22070320100110040d808000b804a860045041c9031004480f4505c0d08542c2d0070300b03458001981d50b0f107803a0325142c11500c0c1e40c0e404442d03990314400102c485000c0c3c00c0008125541c00010700c4039402640c0c00c000c1c203980000c0b00821068025408103401c8070880e100b143c0140c2c110343e004005421590f91030701050b0307480b1030b10203400c8259603580904580c82500c452400010b00001480389007011090b4452464048004010b4a0403940303002e005c40e5500041c407031160f500000082c0801034140165101c1c01d03407200d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 920474991 1250 920473741 920473751
    0xa0e1e01150b0702090c13052b0302010b010e01110a031103070f050a020901090207050a021003090206040f0f080321040f05030a020d0806030a1703270706180612150504 74
    0x844070a0b020350043c08240c1c4100c607900f000c1140b03944caa0342101c00d6244643e5444103045d1420f002c2c000703800038200aa801482016030300030a00e415039001105d080f0f100340c0c00003e440c868417001502c0c11445030411410441c0071241d03c3d41c1c2d6000051503045403a0542040d400142c00a03c0030f80c80c40c801e1030381c01443c0002c1320300b100d8100f0000203201150f10b8402c44040755035a80701c80941c2c04074003c4080c083c0c0070794451441e41015050900003032000307541c40e2034080f07041d8900d0340109601e0380c8903a0201007507002002c000c00815520590000141c44e071030028501e09201105281000a0040181c0041c0b07000b10707010604102ca4000100c01041d485000c0d41d4854100c0e00000c2e4540a58050a2011138101e03000205c15107000f01e0305002456005030700f00984403108c0000c80a940008040c030b52900031404500c02103001c03000c0b4010007149660001d120442c1070039801044030558080d045039070a260441071010507082001100555244d01000942420b01000114004115407000e03410610b08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 920476241 1250 920474991 920474999
    0x40b0a03050f0d0f0c15150b090901060503090304140102070e07080702061008101a0607051b0414010302010503250c06230c0304081c140a0e1e0115 65
    0x42003002d09034001106503045802100c806413258600d800860b000034203103025100002d10a1911072007072500300c1400241c0c41d14603000862502c101508a090b10070800700d40c4c5003039071410f5a460b0b809419145099411404c00080c51503490085001d40c0c07001c001e00c1003200c00300c0c1e4803c020311001458040c920340305a0402c0180900307450400d481200044c000c130030009221a244038904011154400000c1c404a403101d034010006064811800d804040781d8040f64030b10743d440c80050007189000760040c1511403080c0c13080c50040814140d2450155044c00c15540d00131142c6161181100e40a090007666983c1d4540f1101e80c1d0841d01c00c28031403000201e468018225403140e00d40d42040d1040074104050080c0164010142904c0e10003100700c03019180000f011050800040e540062240120710b0600c0c2d54080911006480d003440070042c682d0351408404099210f5000300d030010502c3c203007000300100c034006440d190b40d6200186480c074910780c515450310203030950110805001380340c0329650040d16 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 920477491 1250 920476241 920476243
    0x30309151718210f0a0315030302070618031e030c0c2c0f070311040306020f1e0306100305070e0316080d08090616031803090305071a1602040b0a0305 66
    0x4085201d10491040c00858040011403901c5400030520f512182810910b9040201200707034031105408007050f480b49980002e200c6550030401c040d621980203410200e00b4800014440e0300094040d1400700c1c0380301c83c00c10128840329002c1b12882150079809040c60110304040d965502038000040400d50702c0100003410020000a46d42102c64801807030142a119440a01c6a41001d90341952014217820100b04494044d501138000c20000c20b005600b815030300d45945080342c0020708006004070001580c801c003510a92108414842a01f4400d402e50a0030008103a4201c840c0001d001030558030004180c519004020305041c0542c01011036144110000c0d0402c2c94002c10300c00c4038014400c4e075076400d005034014580e491181040000034591641c0346420b04007514850390309d91007407540d21401103079411132100030aa4010300a0f11240c804e0f5103186443e6244c40001d901440c0c1c070031014805808088051805c884200610790301c200c8060809000040042441003901a0300095100b800001c2140c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 920478741 1250 920477491 920477521
    0x190c0f1e0209060102011116020a0f06030c09060f02150c0c071d1003021f050403080406080603070e060a030209181f14010b0931020702040509070303091517 69
    0x31003650b500c0303a903881c0ea40069003640c00d00391280c0c02c104000d000d00881100c060038603c1c0c0c0680010b000c551017642d6071000b0b00500340b90380c02c0100000d07103480149a0305500100c3e00030040401b4074150845c8894403c00075260000102d09500c40e90451001c501d51166201c02d46a4011400c0e0075681c0d4990342e4010b1a4405010a000061110800001481d1b18804024002c212500940b440c078420820215400d502c03039602110400788002488044049580d0b0006000034140f81d4440082c0750408100b0985415281da001c00c040210303440400c545600d0341eaa20b030007100c0c1e05841e0a10305841d17074501100c0305108504081b420340714411405608111441000000d00c00514003007092512740d078500d0350003003824001e00c04102010403a400389414421880b0381e01d400343c2542004080310300c2c40014070440c6082e02c015200f90300400c00c0000c1d403410b4400d0756005402600106a1280b075560b001d4000c0c20103100d14500c81041d1404084010300034140066144609804402d892074901c080a80e482 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 920479991 1250 920478741 920478743
    0x9020d021c02030f071425020906040903021b0406150302041d0402030a2d080a030e0313051002100906020310090c1218150c14190c0f1e 60
    0x4154146801114400c0d8801c403802280d00c28003448041d0b40f45d0005569400111348001c050000411000c07440c40707200005003195510068400385014850b004000a0300800f91810340301d645401c1d81c9600181d00054030780c3c03030303505c3c03e42901e4088106c0400090003054291300c03201480e01e2100070085026490760041c0252900e19802c0d109880c0c0f41c15039112082011600203406502c0400404d021901340540c0000c41c0c0c1200304000d0030b21b55071051048045c207900308100da0315100482c2009802da0903000b05116481d8002c01141482e40c1200b0300c0031855500c0c40b0310703400784020005100c1624801e0000a140c024000d0f0b06000a414030301d05000254812078190b4401c40311000701040f844814083c074421800f6035996a10024076000c400340040c60741074144154111316070603107400a00c05080c2c2c0c616032a5803e0000a180080032006408074408800754291080300f040340d40d074085500c1078209580d0b400f40c503004244880034505220180c146401c050004a0045100c01c20a003080f28070482107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 920481241 1250 920479991 920480017
    0x50406090b2706040b04020c0f010603140f061b0c1c0f0521060a050301140610030c0219030311041e0b0913050a060504090803071d150901030609020d02 67
    0x260520b040d1122004071103502c8102e03031a4501141d01c52a0a4100780d40b90300c401000146001940300d031284c80c041040440000c541d44480040051280803900c1d0042c500086001c1c001c203d180d4501940c5a0700c0c0108004106c5a100c606901204003070320070f8074802c5c07187d0b00413983c80200d42c11516081d14518110b2000040f0034424039080b40b07105100b90b84103200490400c002804404035241c1d0203a100600c82c1c1e4000500c024001001e54090044044417510211521917904108d0b083c00744d003070180a0300205040c244000301500f59130002c0c45902c02c0100a1500c41e100d0418903088010700040d02080c10610004500811030030000c9000c1741c080307042060f1007240d403591400c44034828024100c8160b40b05002c00c1100b80c90001030340010b688002e00400000314561a040044c046803d09102543c42e60740c0071080240352500000500c00f62944c0310884d00c0215944000901d5840615802e80d0032000c0120307124072681d000b60040700203403c0f4a0025521614880000c5000390400c04c443d0490b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 920482491 1250 920481241 920481259
    0xc0c0b0105222f0a08060f150706021303082a072601051806100e060d030201090c031b171e07032405091b19050406090b 53
    0x450b1400d82c14182c08140180d05444000d0400070050b401480311021240c00d81100c01c20201280110400c1e115030354001d0180640c440c1010040106529401031501c0c0c010701048407181480d0b40c40403210f910240c03046400310356030000c41c80c268010b8054100da6002d0042c0040010042100c081c0107829500a01d5200407100885602d08020f2610040c2025400e904203400c20b020062101120215058416000c019502d0f0682c5210b1708640341114034555a0407452140700d0070b05000c6c40038540104180440ea8082820551040308843d400340030f9a10509408400404140c000c1d0082d140450b0003108d40207000b903a90501021505041d282d90140c45c3c076100c0080352404412002c0d03031140b03018000905d00700c880000340216941c0c407a00000442d12400c000080003425031000f02c45405800c40030707082450666000788069903c0903221854580023480c4c1842c1c28210700300c599003482400c80700d0b071012002510490a09051903080303190082d0038a2030105801c4501e820400526a0a40304405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 920483741 1250 920482491 920482499
    0x809090a0b0a06140c07080a0606080d020d030f06050907030c09081b04020708040509011701062c070302090d0609050c0904020109060806061605010b0315130609060f0c0c0b01 77
    0x1044030421909650b00810548090042610604520484111810080385440d2049080924101c5036902051169104400080800203103000d038100a005102c01000e8040d450075001c0c1d160000041c0d80020580d980070790034091340d026000100240b03c0a02044070f0790424080060103801100400c0c03020441b1107000003070001c400240d030034244a0810200a0080c4170008100c041c2d0710214040d40c40d180305120100705552441003c40c000c104200c3c40d80d600840709003a00e801d450596003c079940e09010300c036052840d00c1580320f1401410b0390044000c1680e035000c03800d400074042e68959541100b405c056081c02c220156000d14040c1d4011011030350f504002c035007082075480c41100d000f070019802801c00c10401c0d005403003080d040400101403d0421707070102444a100d8001c14403d840a030b44440c502071460400380641541c0810ba107801423400c0c45d103c00b080b40c0310080310100900300c0f0340c2c8940b01ca0500c2150744c03100449841501062000700784188d00100100ba04940564040c2c1401000003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 920484991 1250 920483741 920483761
    0x1110c0607110c180613052a0306091302130c0e040605061905030403110d09030618031d06040302150307090602010506011d030a0b0109060603060506160f02120307080909 75
    0x501084021304680080414041040b411100500340703036040184102e48000621180c024107114200b2140c4140c608562291944040c42d05110501c038021010000d09c0b8a5854048641c2e60108a07204001d09440d5188049058074004c2d034190f03080145080e00780c003403540e03010003e04105141185c2c28410f281d1500c040140511901c0701800d10f0900310550402d1980c000c80145034807034000c0c01c14007038202c242c00381a81031203c411104d81c009040148103208010041c4201c130880b05450303220114508080d5400b90103581a10062484c2e200401e05020455840710304a8024550151941318201c020791900911904262917950100d500f4405c0403480031310510503203100e40d078140e50300129684a0703003614200840d2070544079010301860781ca0b0008258543e0603d8000c140300c1c040061242d252140013004c503001c54100718800c980410452880c040042e044810141d0007164444034102248001046030003584048040c41c000802c05406000020b40541002001a141c1000d265520010385e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 920486241 1250 920484991 920485003
    0x50601030f06050a0501110304030f05030304030f02011506031d010e0f060f041113020702040213140117011806180e060106030605100f020c120c0319050d080901110c060711 76
    0x1054000c0c13440c0d1800c0240e50300c0303000400b0310800d803841a03c1c6840d440ba1103100c080c80140c081515141d00001c140b20405902410010b0070140b075200170040c804403040a11031b0403c40744141d03802c040c2c503030708102050074800c0790841a107032004000f00621109481141c0d03c039029448421400d01412001074000c0b40040c2245208a40c8401001d0300000e000742005081d00d1888051070049609101e140c005845601c014645034080d0000303400400e1400740ca11001240604102e41041900902601441e15401f031a5041d1914400000d14442d071008000e4020034640c0e0100b80c0140403c60798440f00c0140d60b2054200310007400076181a6a00ea03031007501030b10720704c2c443c10b43c00075440c0000395021072059089511440e03142c1b0564401980d800b000a2009003684024842600000202170743c03480c08102e803501ca00c4030f0003d404010416a15650f484422060440050142010000d00700700307002c0d030101840c03000c0001041c0d215591035081d65583d440071240440480c200c2100d5000501c000204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 920487491 1250 920486241 920486249
    0x102011d0f15100911040504090b0402040c03060b0904051305071508010503011b0f0c0c08010c03060503190209131208071d060d0207021804050a1703090712080c10050601030f06 78
    0x43d0b01928903008842d002070500700031040405e1400d010102d100d9480d03004a031122130040b0442d03503090405004100403228107540300c006151600204000710b00745001941c0e071601c0221400185550b80b00c0d8010120562800002c2050140a5001c80c0e0002a9151101850800d40d9648000d030303200c0c02414225650301c903141044410204244a4a030b1041c51845682051407404a0109069684140c2c03502d04940203007a150b5140c2504074401c2e54140301e22001006c08030003d03d03c210b200d034511403044440b444007078001d8240900103580750b009440c1702050036500103640c2c407060302e40e02c100805400d82a00c3c0100003a54041c202d1942c1e0850744040d503a2403d009142c00d1502480c42d029074001d51210901f281c2050343c0d6140350b030030000e030b105205103d140560060000c81c0d40c10b01d03048410f440f1002901a88001c24400c0c400c00400c00a2240141c4503400045a42c094050525080c140201c03403480540b445292004203928035a0b41140d401035100380c80900c42c102000414000340c50303007809 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 920488741 1250 920487491 920487511
    0x7020303060d03020c0904053004030b091c0c030f050901080c1b10020901030c110c4c0f0212090a05031006180b0d110102011d0f15 58
    0x8081140c1e85049186404002d2290044031146840c44000c204c21036401c440994060b0401001302c01c03552406510702c403412600b0031240204140015454880b4055804094461881580018203000c401c000e2a1003110740134000f030029000f1350100501d507002e00201200000c102403800c000c150f000e01c0585000c640161100055a95600c00d03080da42c0c1c205207080480ca00000914000d200001d024401401d2001c00d0050ba844c4401d80003d0291207286544600700254440e59403c0c0c0c03000441c03800743c0e0030300840c0d8038010301002c0018030040401d110441d0041c02400a2511181040411300d9010340c50b88080c1c1140084450b06c040d5400c0f01200740c410056007160007124011081040100f0211070f004207038602c0d560701c600100c0e291a000c101c0c18540d25603505024052068101282400301500d840148054007404021407804420000000e1040c214042c1021260307000790003152082440e90801e0144488401d105580c1c2d45014140300241d00528110f48842c2e4220072906101e121085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 920489991 1250 920488741 920488747
    0x60f080a03030905011b080411030703150902010c02060f0a030b010206070905330c1b180a060e091b0d0c0611120a08011409010e22061121070203 64
    0x601c041d0042c01c0d028208540c207540c2d0b510782d0301401e200d410210707050440aa684020b20314040ca04010200080300d0464403d03130000c0800c00010700079111444070401c0300080801d44071898401a07540d00000d440c002e50041c00401c00040e00550307000075000c03032003403640c0c10f01000c00c8100040ea01c1390380948401300055128441840f807800c1c88070340c3e140c2524400d1500702c0744250100001170160740c0d201090400f1000003d4400c11043c0402111210001189c0e020180038550000242d09021500301c03c201d00002c0c2e00000c003000210390114004241d0012041c882c0d18202c0541c607241c1c80c00e1000b0015440010f0921412402e04c100800442e650041d480b042c441e051140565521000c10044001072040981c9801c102c0b10100142041010645600d2095410028a202c00c40e280800c0315000d6040c60004000c01140c240c2d134a030b0414584030011000e103072079220b070b0303424502c10b8a40688940c0c2002e501c0b0b08034101c0d050061021484c0b802c40f41c3e403a40442910f10341a00c8044c0c91003801a030040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 920491241 1250 920489991 920489993
    0x6080316200a09090212061006080106090f1401020c030a060c020d09030b0a2a1706031c05030a0603020303130e0c0304050d08070c0b07080105041b14070c0b1309060f080a 75
    0x168082c130f00c600e000600c0c101d400c8411418084ca48139003220708110188151104120f405c2e0844200740c05055242411070700c4504104000d4001c011600c9001048040355800000c10b9000b4070a080c04002c01406a440510090a10402400d0785211000052103001540e41c00e00f8454541d11080e29030128101c461f644691422401901250004c2c0f088420b1425881403d424030708800c024503041900c402e40b078600f020b5044008100d00805082c080c2c3c02400040604001507241c8241600040c101039441b9222000031500409040d08000c0d01403000107041c108581000d10a03904031400605040120340d0f44880524450009850040c03199001403104140c4902405110340e100303c0c0d80c64400130115543d150140f540409603005404190740a00610180c1840e0062118001030f21080340c03c0aa940d10000303140c0c10010104550701c01c0b001c2445020084005406402841d03c102c09a4560418141c00c200580c21885444945444e0480000f01001c044c00d0704d10448110f82c000e0720008940f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 920492491 1250 920491241 920491259
    0x6060d0203070b070204290a0509190e0717100f0903080403080622090b0708060a1a070b071d0d0803130501110301060507060b1e06070606080316200a 66
    0x104d40b60803a03105031182c100d003800031500d0403071800041d0000840200800700e0390030321a100304250081401032006104101e51600e261000c0a4011001c2400043c02444d01600780d050150700d8010011780907842241103140c0e040040c088221050000382044018800c407002003c50349014401004a42450000f82c0401c1c01030043c036910a00281c05030f2100040025030111030300e11801101d0119a4a010400c28440b21070342103507102409003042550341c249003000400f4144d4521a0040711104144012450011070080d1b807919580010712018a04080f24050800c42008408020201250700820b1103072810f40640d41d99982c2018445140d80c03210122a0454030000d04207950541d2905081107150b24088020b500070010343e03407a00d4854a00d40751400a03203c851100c10300c220099412030351004010308444081000c00c0b9400c83d6510002d24148014207080d5000803201d000c0428a000700c02c021684c042c000a10545a00080241c2c8000c00000c00b10024a641c0d08001c40c443c0a000c0c0d021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 920493741 1250 920492491 920492497
    0xc030315082a060406030504050105070822030e09040515280c031b020c041508060c0702030a06061203031407020705060f04091a03010e030a020606100912060c0206060d0203070b 78
    0x30b0003912009000070802c2940503501030030000c1d5880041205000080c07107429040307030a41c9020740583c20142c00308103843c4080450703422031000c440300400416003e0414440491000303842104030340f8043c2802c43e120400120420350300d40d00b80e00003c0c0d40c204d101c1410308409000401c0b01081c00340180303079980141030a1511101b032668415001c1075046140000c40000c1c1215401071030b801c00e00c0c0060106442c031001070001d0030b400c001c100b0701c2003c0300400e0f05644440300c0311072291556039500001e403501c05024805080036107030040208420000700c0203040c40324000e032000c2c020050f400e003020109102c201c43c1540160071111081c003117490018010304600401c0000c40f42029190320222088440084121550380600b000a07030041c24203020f80440d00308150050360403c4800c18011f03458080042c01540300c0d1003003400b1200347e68010840340020b00050100e0851044c5540341c41001498021128400352290780b0001d41103190502c420407841e036000d40030341100c0e0714040c94031080e50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 920494991 1250 920493741 920493793
    0x510170d02150c0903011e180305070f0f0c090504121b030e2206151e03050406270312050601020a06050a1103070909050a050c040e1b0a0c03031508 65
    0x6841041104c145139400d003d0811a002c135080c0008030307400c210040d08201c60010714104407441c0e030b00e40d201340813941000a031854981c000e0b191300c81103403284c54142840030124000800b46900220003185000103175100342c0c841e910643d8100b96101c940d0f14261443d00c05445822601c1c0d17000340c0300b20300107032260b01c1c4410000000f408018069903101228400340105658840c11180d0780c0718100081c080c00e48400c0060451824101a1074821041003001d08080d84400c105140c1c541c1c01080802003030398820300347c0c1e85a926502211621003e00300740d854080324426000113186c050b031250341401d18450240500d5050f0010b060a414a9031001d016120013464011015a40c0c0c004a00321640400103510400c0681d44e0344540078105103920045031005800e01c002c60f0320740b000f00017660340742d101113806846c502e07008900d50360388007840c1800c549000900c0098034400802e20320f0940350040d08503002140b00b41c4051000d000260398604e00c07200383d0b00c281003e66001d8071a60255440b010900ca00320303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 920496241 1250 920494991 920495011
    0x30c0a0309080c241b070807020402030a02070b060f0105031302060d0911031e0a11120d03020d060801050f06060a09080a080406030f090c09110d0510170d0215 70
    0x101c0841c0c85403212a0040542074800741c200e007284402c0c207001d18003804c510f0328a64040880906001d50540301d01031081000c0b20b241c00d40003a4280900030320038203943c102d41d8010401c0d9600d2030300c0102a40a5000003a044400b81c02e01008180c540c07401c405401c1c85d058043e910107013540d49400800d41c3c0b40d40401e8050341c01580800c5141c000501034020000f01da8014500c9030038920007075050601d0140c41c2005c0c40343c1c0080c0e150880c0340340c482c0070802003102c50b00300b45480841801030000070240e007012009036a462140a01d01d13485603805801429812524000400c0803554500006003640c008a950489101140c400a1000d140c060003408403004c0741d142900c051510341503e070b0729103100960166071174440490100810303035160103480c120350550369081c4401d00e4982d82d19400403016008000c680d54403403e1400340840300106403201c1c81088581030020f41801c3d00e030b500f042012800360f250395411300c074503005009000182246066000e50300030803000350755980505401101408039001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 920497491 1250 920496241 920496251
    0x50a0804020112141e160c30030b01022a09090a29060a0315050702100204090905070e07170907030f12350a09060905060405070515030c0a03 62
    0x86501040303400d200e4105c000c801c01c13000c249103003407107010304000707080c01c1104060450740c48801d039005013002c0c00b15500505011400c40e0800c80610a40b09000203c0c07207003541c07400022002540368200009140080c3c003134032007484201113040b2151420440c030320a892800e0030302c080d260821081c031580c84225181a0381e040d80641e81d071344400c1c5501104030300503480c500b12003142d0020303594201c0384c0251301225410043c500c0e6aa88848c3e0002c038610f0310a0340c6a4400000e01028001c1c41003846400540004568403515400a40024002c86070107594600c07a06402088003580e01900d14003c14907520392084040c00e1102039428601d0050402e07195004036100000000d8886030b039000039a03c5448014001c800e84200140480300021100181d9440500030b410420004071090010001342c40482a05070b0362a8029405004022030060485250400000c284000172074424000d0b07105109903101256504100402c0580c0284240d47c0c2c4030040010a101035103c60041040701d17558140822 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 920498741 1250 920497491 920497511
    0xc011e0509061e210f070c0303050a0b090c1b03040e06150f0f04140301060e060d03030603081909060903230a2a0501080c03070804080f0a180501050a0804020112 71
    0x3050b9003010590131501c0c401d01c1c545802102040381d4190f4418070300c00c0c17029220300d000c44e001030a082d4000c0000d0189030340c5102061480000390071a010301c2d400a041c184c058181085008100d0780100c104450081b18074410b15549480401100c2c21510043c06c0a107841e2110010020384074210765146010320400c01c0040084003044014010b45803a0280403a215481c00c0c10420704400710301e504501c05e91514400b481000210124944c1100043c1c655404100d0649010380c0180301540014008042c00300c0c0e00d00c0c0c0c15840f42c60708850322219549512a640d40d4070010755a0440314007004101a103040c3c0c25901901c031f0305c09005910a212401c80d5140314098450401c10003001010030401da010540e4882d8007030700803500c10024142860141201d1074200c01c030050030701015000d40c4c1080810001315003400400da00342c802e11034010f10320030740c0c850007803c01a204151100000089620740b2500046541c055400e840c900083c54503514050313616580110b80d40c081039035000d410b0780c0c4c1d03d0060700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 920499991 1250 920498741 920498797
    0x50103051b240403030906020a020a06050c070b030a054309180f20040308030703020c030c0606030d080c1c200c1204030804090506040912020c011e050906 68
    0x842c428151040150f03540c0d00b1401c00070110812600510195400321f41c20784010380302c0140c035004442d02481c11302d40b00c40d40a00300700c1c200450382c2d1294080c054040b082c4003616461b60701544c02074004d040300c07804004c22282c0080d010001c10030302c545500140320304003100980d50001d00c04140c03814a010103500745c661003040b80c96060390440303070000c503601c0741a0311000750540318030703141da400c04c00c130740051040405031400b02032146000c014100380c030100218540c1c500035010f840d0404005020380c1c0e10307261941d0f19941c2c0d400040302c2c500d04c244500d5145254607406251001d000719204007080d03190008548084148960741070040308081d036150304005801070403081d000d1595078440396541c0e0340d0815000040c9803c0d05000010b50404041008000103100c80c1c080314102c8071105c0380442d4079070720a0f0009004000c90b050103807a2400b80003000945980c0800c00c442609026220902a40340c02250480d0a102440c000e6003c00d03c1082004201d1803c00064801c0c03429000061451194a05441c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 920501241 1250 920499991 920500039
    0x605010f110a0c08101d0a02060906040b04060507051b010c06021b120a021203090a0326181903120b13110909090102120a0c0e0a0b1c050103051b 64
    0x4042da001461041d03400d175400e000c0d451000d401c0d101c500b54044021000581c071120602c0c0000d200f0240000c0031340703840d1980b07001daa0080c209080c0c01a141d80e80c0e680080d055034010002101c0ca030291140e0034900121580d101000c0340360603902c1c012482010303915a0005c1d40243d0382e96039108103280c1d00080c01241003181582881360322690716251f0500c900080d1415500318411482c940003401000b008980000b9480d020036050b243c040c19448554605141e200d41d22a003201e00b600d00030003000300030b1440307a4030040400f12403000c44207041c500b0442200c41c8180311500900050030f00085a843e100310350850101040010b011807100420300f00c81c1001c441c04020700f02144440491010079502d0030a01082d88481004000d5291403881400509840e0008051110490b03481c1c120001252042c0300c1b8102982001d0301c0e0484281e1622041d1000c1e801007a050fa404103820035040003018406d0064a0480394040c00070000030502e10100d8041c9040c44121717540010802081506654800d944 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 920502491 1250 920501241 920501249
    0x150b03060a020a092403051b07050a02010e0607020d1506051e0f0a080303160e060a020105191e0c02010b09040b060f010c05060f0406020f0f0d0f0605010f110a0c 71
    0x69030f8480072040545004201d03400f1607405070000003500060764103000b81e403411901d50716000880360f54035a1848082c00d40520b82c2c400c12000032541c0e0041100c001a1464224001d072181420407200208000c014400c3c00342c02074104041c800d9800014034480b119083d03000d03140201042064603007010030210314828500c00d4041c024000030360b00604207941900e08006040d10007050030307030a02d54510303601d100241101c40d0f5907040070070f40d5102d144904481c801c0588000e18841d031f10400341078001d000e0320041d80c06a40a20b20407400d85003060252190740ca04078800001c0005c08401c1d549034400030a4910030f070340195500c1c4c080d00b103959036900100300c0c0314134030602e02d2003964180310041c8003e1024070f03200a41440b40c42c7c00941c021a10014400750300101c900071030100c07582c0c0c6280040c040d0050900300340030035402140e800300c401344442c0078100e03c40588004103c00700f40b07010050252a080c0c4030300c502044070b000003080403910036551076102d604600c0440746a000281d80c1c408090501e03900c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 920503597 1106 920502491 920502511
    0xc0d0e120d08132907030b03030a09031b091119020a0201080103110109030b0a0f0f060302061c230613050114061e030a020306030f0303070c150b0306 66
    0x303040215100c0f01180201c82e444e00105820f20718205888450203e4100340958a460600006980040089a803030082ca0782c59074541c12502c0d614417405014901e5900c20100d0142198094407659a140002c03107070340c9060340010303003a02c50705400c89103045420443c030000150780d002091905494018816090151a210050b610508030f0340c1700801c100140c07410032849014a42c022401c540440714280104405852841c0c119100e50000175404402840b0188c590340d0f614a03802681010360100249010100039241203081030a03042c6050038048008010460610007181000a241c07182c0502495050a050f640c002d440480b00f64041e0001090450751100b02c10620409081603c001c9980c038102001c4000c060740c42100c1c00c0740039110b0308610504402000045034030800c400d65416800000c1582c40c160b650a021050300246a1502181c2229a505000303160088401d28 = true := by decide +kernel

theorem cover : BRFrame.Cov 920323741 920503597 := by
  have h0 := BRFrame.cov_init 920323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 920323741 ≤ n) (h2 : n < 920503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
