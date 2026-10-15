-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4401
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:29:58.811005+00:00
-- url     : https://prove2.me/submissions/8554ac2c-cf4c-49f1-9522-2a8f1f34f404

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 791366906 ≤ n < 791546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 791368156 1250 791366906 791366909
    0x180e010e0c130c140d060305060114010801090903081306060902040f0f05040c0c1707151b051603050913020a050403051b060f0901030b030d0201150503030c0d140706020a030902040f06 81
    0x22071341800c0c41254a480c00d801822041c0400c0c500083c2072512521290720b091003d03800841c0c4160725494010540d43d01000aa0041002403801e11600300140d80c080c002c100002c0180058a600c0444001030266641001d070007014828401c5548984a041d40341140a0b94000c45101e419a84000a900e081a11076141092075940d5859036a11095807403801c0f03000108c1060542c003400340301c0100403800b80102215821a500c1000440d0480c101d03001070011141990340d81441740501880d60b00d413001d0f00205000f643c0c1450280d560f2402d90b00010034441d425a0110074052010a46d107020302e0300900180140e90081040303448175802d0300c100003980e504980329079030070407418031154580e00702e10700c041c11010f00c0505020965410180109103410104214000142e440791000440c10764a200b145003d44010307400766150016000d910303942c0d0b00f00284580e08104c1d4070507060481914440079204099031203d815952140395030001005841444000da00c036520f06046010b400325030340b103400b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 791369406 1250 791368156 791368181
    0x2010501150e0111030f03010f03050d030911010c05010e0706090e0109050105030706050a0201021204050106060f0503250207080f010f0501050f01020c060f04090912180f180e010e0c13 81
    0x488690b1810044520040303030044038250b84024006812a00071040145000e0b080318560200010324505003103141180c0304941d50140f620f09403e95011405d440c4c040f82d5212400e00300070b200c800300e071300d4050b0042100c007107000705034026020302082d003a80c04600e140031540d00f51000f044c40d9880e0040d41c3c040b2002072090342d40c15803006804000d040d004030050603403512103000043c20a00d40181583c028081207c00b110b05940d110700920507503811036205d5560144602c3c1090841c030340640040c0403d0795500540c560381d08040078280361203100300014009490300005407101e06a464500310f01910241220306009400c1900120b141d050045000c034000805a004110184058092001a0380448030075201404100000f140252141c00b42043d120b00c140801445022400300c0109407000e001841c405080301e4000400203040301c15000d500755542c81c00340d004a001d03890a42c000034450044414025401e00d000e0810020003c907421621502c282c5009182010b41c98a01c0e0840d001c036103082 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 791370656 1250 791369406 791369417
    0x7031802030601140f030f19140d03090c080c060f03180a05032106010f23070f0501060e06060a0809010b100215090102030705040b07110306130303180c050402161b03030201050115 79
    0x42c40e8112303d40010218050207881421800c541c10250400c3c140031500c038082500c6990400411800c003580c440184450700144c0040c207040740000d03d0622803884070520000340800440c02c0a0140300c9201a0103101500311262405540751080d2641c000c06078005107000c0c000c50303040c072062904242d0303441500169100d0a1001c180b00c0180d90810008006400c05d45030400350203d00c0780303031200810100c0d00800011801c50034500c0d0880c2903c0160300201c88c60869001484a5030302c64006a5600d44801c0c103048195940301a00e1500400140c80c41c03e0780004500303081b00e40d01ea0040740700980791000132407502c00c681d03406030354034241e10060b0b0701000040c038100f201b0000e0b660008007811145100b881030309011010040080e1505800f80c841d4050a01c80f050170804060305486002c0d458081401011103a05282d01c07040950886e6208a50249400141b012411400780c1d01c080071a5a110080e030141c0324030403003ca1142c0300180001c401640c40e20300003299a07000100008801d020b5556a17 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 791371906 1250 791370656 791370673
    0x100f03020906041508071d01124b0b07030e0706030c0504030506070315090b06030a0c120f02030601020c01030b030d0e150c21030f07031802030601140f030f 69
    0x501c4010806050884c0710460142e4000c2140541030081c90002c0168501c0d03141c0600092400d40c840280c10792003a001e4480030f05914001400341504560612100c501d0760854524204e8601d440c0391454500f40d003010100d0154941d0b84050a50658030b01b401040450580e54a10100307400310707a41d92041480310b501c521010000c40b88260080714a980752403030410b003016036a0b03423a103280803030075610000425152108013919038003200258008104900081c40040d0402005c80c031f07035110151a42425a0311090b0764102c29003c1d28101c513581e81031a808108000c1450a000020340040d01c0c0f05006005086507000151b1190042040c010001400741141c1d000304182540c8085084010f9900708000e483c840d000c0c402004050020141004040c04644654032007103051010088035401004e0740910504c1602681e200e122648598103040000b89020303a11085c129000d6103500080d0b051084000201c2d1406031074480f01614071040d80c0001d0985140e40406480f040c11460200903940203651 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 791373156 1250 791371906 791371909
    0x4090b01031103070b0309060a0b1504060f030222080d030e0304091a03070e090c181f1a130b0a020307152a0909050601050d0b1302070b100f03020906 66
    0x103040c2064103004003114501070f9900001d40d0260407c1302c00200a810250420241c4402d50080142d02a4210707001d06160740f03062a101c4030b502903406040100305031010719190460081d81240c0e404d01002c40d1206140500780c1ca03002d1300701c0c1c02e40244d986900940341c81c264003030b000f80030305049080860051400d00303082c40c584400805940c444040008661209030903079032018072203503018250000302c0200030f02c0c18040a601e070040c030411450003507101001c81c0201c2d4998510040c0c000b0351010b100118a41d450060f03500e102c049401180200c00d100010220b0f400100e0020525450b0003030060610554400080c82e141c003070f07181d2010160304200030440004d08c0400852030200403820300001d2031035650700098401110154141e070b10b000c03c054602c0003944c01c0503e100051490a40500240c904140020458001c10b160450b00f1921000743d00101d0307495a420741c074925143c840842d00c6000034103101d41001c506a40c408104014131101042c00e00c0f0384040402500d4015002da04262030300c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 791374406 1250 791373156 791373173
    0x140a0903060e0712140d0806060403140c03031908010b041401080c0c0105131407051c03030219091802090a0303050304061e0c2c1002030d060906090b04090b0103 71
    0x50450b03400380500d200200720440610f40222602c0c1c0513140c01e48054001089840c40d10464040e00001d01c100041001a103560303000440b01625400700c0e103041030b101641021860310042d03044050b0706000110304200202803824413000300c070080e642c0d64402640e076003140d0005071085004110403904011056440f03940503a000300e8218080b64812445c0600d540070355400c40c0c00c00c0d40c1c0140c01d440420000b109000040c0e1200e40011058000340401c0352400340050400c0c4040580d1804080985004500b454000d5042d96000c1d100010340200203151240000c0c00b440d8580075010310780070a0386552a00412620075101d40d0403010700150074480c19503c041d10107820046c400c54205442d02800e44901c216040e00421080c0c044501007001610280c002d002030285007020403000d511140a1400220790324a000305042d402e0720b4007491036007241c80481c03c1d1301c90300e14214642ea040050002d0184c0b410f034005011a0120002001710342062000c000588001d01d0014040b14400740051000c9148075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 791375656 1250 791374406 791374421
    0x2120f010912500a080a45021809070f060206130c1215050a0207020109030f02010908120301240e1002010e01091a0c0913050709030c15140a090306 65
    0x1a001c698100c09001060f12469101038100400200c041c0c00740008460603002e40d0840150301000640307092a40030720780804d1002a020081c41e481000500c0f40c805585e00c601d80416900506150f40c000400c218221103041c00b61400b0b103d41c8030f040c070002075005c00c0c10074030b40941c3c82690240c120343c1c0712003009110040b03031001c5c1510030022140002515101544503616258072907443e003070030f00b0300940300760003111070040c4a41d140760300401c02c040c010303a0b2004560042d690301a00c030040c00811800103c952020503000303040c0c1803040761191001d42d20244080d604171040c01801500c0310212114041c04001144582c20101c1c04541d02070480d40b07030a42c04130b0f1000c0e4452000184007502e03865000d0a6898030501501e201c0300780d00d151740d1405500011503910800003000c82d440d0809600104160078010707003c00329038640e00c0b00450b181c144101c0e4044015900100d001c0d04458507026401b01098035881d07250042a0042c0ba2410000c00710801e90f10814402d481d8800310380d01d192500e10240c5180c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 791376906 1250 791375656 791375777
    0x3130303110d051503010c030209010c15060902030906240d080c01090c1419050d02010c0606091d0d08090616090806042102030405090402120f010912 66
    0x144040b0a00038401c1c402c4610901444038515243d0480d0000d060031030342598103c108044c0108840291641c105198509482c1d0000082070140c01c103054280052030301d034001d1402035000009000302510001140b500441c3c0e0541e01d90840000d40c4a220808a5000d03080781e0001c2414940d500410140005071280d40998800482d1510351945c3d0030f05280c04a40040040360011548140d4900700460201c1c1d01040c00302801e80340074240400196a1301841d1f10003410005402400810095107070040002011110400d010702801f055015010f1400c0c045031000511806d40f00140706845440b10310f010b00d210101803e21502c40607490583c43d1840c82c1c151081c880c101034002980e442c20031aa61261340605030000200c8100e941100c0700c8200036008030b0131944180004d1244c1e030f072441100f0350002c0d811103401c0f00c0014807111060078121541d10394510b6501c2c2c100f0700418080050451842218203545031091400c02400c0714281c4060325100d0702d4540e548030310301c8000d65074120b10084403142 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 791378156 1250 791376906 791376941
    0x7031103030c0d1d0301060f090c170103060b0f03060601090527010b07060507050309071e0510030e0706170c03040512220f0b12060f0d0803040c080303130303 70
    0x2800d0311180b80c4200c2d658843d001807070034203460800d1203c04100500502044000348081c91070b0a00ca40710b000424026505610340da0404170704c106000b10982119041515904d006640c2d603424118020106030b00400d015081c071244055451a01142403441400143c403a0950380d41850144642a00707604060b60040c03000902c0c010480d00c0e201340d032900074580804900d5441d451860440d0a83e41c0141c14041481024414044548804a40c1d0801d032540d04401c50011842c00b5402c0000d081154440c5e0f0300039031440c04044100c1e0b8180c20504298080100312141e0741e40e900b40885a1050342c0c0488011a104000804c0d88080014000d64106001c0c00c100e420001840341c4980311903001551505842520100b1141c600c800e888400c0c008040c1007000b20481c0b40b500702014130910804d115400c40b10480c10002c0d005980d5000d64102e4150040d1211000146070326060f03d142d4010b0f01e003070b28a617050384000654400000122842040c0840c468661107885a80030341c0944102004040c4010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 791379406 1250 791378156 791378167
    0x30801030605180d2f0628290604060206010b0706020415030b030c010509011b110306010b0a0f02010c0509040f1d030a030e030901050f070f12170f06100e030102040b220b030402030703110303 84
    0x40c0a001c8ca6100e1050310710000b0004141d20344514500444600ba00c1c02501c0502c410450340e034020541504540c0d0b10001241d8496141c5090303070080c412900100c8081410031001c01e05598150301000c04c1705e100303604480e1580801d0340156010b0007035450890018480b084154910250b040c0380b4020316200d00c0391800c0c000514800a410200240c010314032500b00803615511690340501c054010340ca503030000f000000c1e0840d00080c158800c0c991900d02540d1101d01805020103554811002841c088524000aa0400c2c030700540329840b5511103030001e0701705104030711200000f208503142100e058494070b2a0140814210010b900480030550b0b1034002001300c0408511000c0040800f041c0d80d136175144601e0019250311180c44800b070f105085000c1ca0301c003080303030341e1301c03048070b01c1a48500c076092210ba44e207002000240a4070990b040380e9411400420b912280e52012004986a01040a00529101c2d1203201301c003a58001102d000c0c1d8107031302a034420004145005120070343d0743c0300642540d00c0d04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 791380656 1250 791379406 791379481
    0x203102706200a180303051e09040c0e01121437090204050a140402040b04060819050606090403140307050405180603060a0207030801030605180d2f06 66
    0x252102c0304803400d040c00003040c03003500b40c0c0b04212011024000890040081c25520020814015142d00c503511a2610b4000501c48071400140c0700100c1c0001c10510000800140c0184006c00b6816011301007503022040365802e9689000700408882030810301c220540e904541c1261b0f01c5041013a1141311800b030352481800c0ba02000d102d9407040760b05003021404984520502040326001885030720618900301050401c207012002140d04039404450205450030300030000f5000744441d900071740051145030b5651940888990b00c415901e0300800c00d84a0b141c0d2518140100b1600841d401800590003285041280030000d000c1c2d42c0041e16480d0031818641c41d000850248041200745150015108082140c903190401425910200901c4190708190a681c1c002e0014034041c04001c02072a12640021603104900c0d00700645c1d03800329402c031003002c001c1c141c02a00607130090b80342d00c01980030025028094060344080707200c0c0c15078100003404e05a03540300b40780146051014024007032030246030b9241c2d0316 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 791381906 1250 791380656 791380691
    0xc1b230312061c0503221203110f010b031c05040b04060e0306150d0f02040216080408010c08011d18120c0115080a0308220c030203102706 61
    0x40d0740a203050002414a803007005030307540d0b00940002e01a000c84204070f000540100035564078100441800780c110103081002e108140d0141c0140340d4111406d80a00e003031641c841500650407075a13a0640381081c50040c45a4243d4107504c00041c1c0641c0b0901c0181009810240601040e06451400300d00301078585246400c00c1e405a0300000014900c40c0030040e00385004c0c030410341c0042252550b0180d81c1003076804940c00c00311401c00038100c5e003500c16031741040d900c03190101d070ba01c403119086c0902590070750320b42110740d80c115005640e030b5507181c0040480740030302074110b8a05890481c104505010000c1005050810b002040d50b40c00404103010182d11003002c01c1250483c008401c0101d07160440314131840d003190064006880744c00c405840401c240e81e404224008d1080d094980b50899a45103128041c1c01c1c0203800051007104550070b41407041c003c105084009407403081b4191480285240491010b54050020342500213500d900302c0644002c403c4203581c02144504408602d04009020f001003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 791383156 1250 791381906 791381917
    0x5040f0605040501120c0912030c0605010306090b0a0207020108040803180a0503180f13231608131a090c0604030506061908030301120204060302060c0706030c1b2303 73
    0x8101c02003800d2041d583c10607404200d800203001c0c00c01040304044070041c68600316101c0c48009402650f110014580314009503019690085024006569649044402008802c0e425180c402100000c600403003041c0c000c8030744142e0142c2d80ca4015440d20344440f11160301c080c106506403001d4007504204a00c0501103007040d5070203080a951255100082102e5819101158a11900d018100e884850356a00d1490000c15110f105c0000e6804034a01c01c12400e0310410620794080ca050020051509418844030b54203103e503944444050f140d43d100384020000c0c110000705040d00c0c84003081c400242195030103510600e6031040b1403e42805c04041009a0710640080c2c40360b401242c00c0110f1800c02c4941215408440020060341c0361505410139101e01040c001e2102124242041d00c06564454000d00040c58006201a41d9480e158810a0b030740c64492040802107814642c60381941d40c00f4031442e00708640d4146070b040c104203241e43c0b2000040d22900712120f000258050300704845108001401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 791384406 1250 791383156 791383169
    0x723180703050703150e1324230c0706090503042c0709030f080f0904140a0507030e120c010225050f0106031709011106090102220b03010501050a05040f 67
    0x25030b0b801c0c0448001e0a80f0191914540e07540c5141504002c100c10751750303110303520140002c0d000d50004480e2034401204035414080e44102c5c0a6401d0709081c0c1300c401d90010304e03403203400c01d1070403007404405a43c2410440b04448030499a40240210f102083d0143c00540d1010310030410340f0301e4030351910390841080c0000c081c09001d0074004a0180021000000d10341d8018100e802c02002e481d10310360303d02e84a2940e48000400390400404c1c240040c2200b541643d8031000000c2003800068286500d0152000302140c0710000d050804003c541850b00900c20119440c001074050104c41c2d23441c00440d0b015a0100c810402d443d03500b008081c00180309041500000c1080044c10450300a29051640c9400400c0c402200140d240172000c0000501e500d0f0035030300e01e008168095854800c0c80d001a07621158090400560340252420010250010740c002c15030501c5506440f050326030403960554400403140541c07024040c0c10001030040750300450160541c1c00d524500300d803a150f101c044220909407280d2080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 791385656 1250 791384406 791384411
    0x14030709140303042426090c012309010c020405090309031002120114030a0b042f03070b090613150e0619080a0e01060806010311030723180703 63
    0xa001c1004490600380039650210011410107003008090315007005045c0c40d6503585a207028500707840c0c0d0700642c001c000c64007030541000c401304914000c000344820122001c0400d4010111015115801a20304076201400e94181801c800e514240601c141d0f80062403c50620036441150401030352540540b0744a40f620360060760300c480b541c40c14189880a100a0440058014822030b4144980d6100c403030f04540306041c090780c45d840f80d00007090070840408005040002003600b0402800700864408040ca50b01606c440708213900c060300c92025001c417007000e41d40741d08a01e0080110800743c1c40604484000101114a0b00c02062200080c5000c0c0c1d9100c514214071008040440580040002c3c03100344065500c40d14203500d800750514070f0504070307218000340940304000c20f800d00c405501c01600a0b0801008002c0d003916002e0056803000c09110445003c911082162007a04001c40c030482140c1c002c0d240080d05140002024100d4800b424242d900044915001c0040c061b0040c6094052146078900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 791386906 1250 791385656 791385659
    0x80a0e1f05010b04030816030908010e0106051e451509060f0d1104090b16020d1b110d03170108074407060809060613090314030709 58
    0x800c0980310140d1100026101c103100800105440e40211201042924019140d85c200c5180580d17500d11150071241c0290b280c81880c0d080040154048000d4a60407035010310040d10141346c2ca903410b480c0540e401d070404c4003010380307203000d10025407030006004130440d9403040f11024503031091450701600241c285485500091100071400084103148011042d1001005494084003042c3c0300100c1d60201030107a205085501c09101d400900c92000f004010820310640015052540541c00c1c166240303084228515642200c940c000160714400801a440d9490005a40f0744c1c412180483c001d002e440d0406210550380d01030f0741310529491034034807a483d240c3c20400000f440103d0100140c01c403000c954041c0005211495280340c0b99500f904454029441d401c0520461342c8200700071403429054406203074545a005203012035071905486a036a9503a10780e03a102c0038a90380d0741409440f5145c2008250007040c00d03c03107080d009040c1c00750203400c00c059159904d07905012240d00486142e4005500001d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 791388156 1250 791386906 791386963
    0x913110c030a0e060a0c030e030a0b10061103070b061c3002010c09090c0e03061005010216030c061b0c080c0a12050304141210091a09060403080a0e 65
    0x18010003003e059030b04d103007005410140907100c1040b101c800780910110b12241c0455550800c0144507a5910079003411260070000d09400042c40d041c022040481d000c2c01c10b81e0850074002082e02c00113900910004869200c032030600503801e800c004601c4d1020140c8400030041881143e1038491550705001c0c00003004080c800c01a02518080001c50869041c03088080c180380d4000032040a50700304210009140076507071000d07030340320780741e102d2403501070040e20b0400292030405a031603000c8417400e80980e10412a06140d4800d00c8040e07000c01400036000500c203000440c0305a020108884c62400000842a880d480340d6203154851382c0146895400f40c036002041c0c0c103240c640d600c0181000c0300c02c007000c030f100341d03581c80d45034080d0713028038404a04070303d1400310745d9520b03001043c401d81e5601041d40c1425108800100240c400110284d80140d100c80c0254442e03080000350511550400c0d01401e02c40d11181d40032105508050440c440303803615061041500c40040c4216005000500d034503155440d0b0050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 791389406 1250 791388156 791388167
    0x7030905011704060b03010603020414040b010b0408061b070203011406032a04020c01020417070614030717100f0815071b17070804030308060a050301110913110c030a 73
    0x304858104485000d000b208007002d06070290700305030301020204055102c400440d00400b020780c000b0303620508100e00840100388280d400c80c01103000f1398402c9011307a210f0690000707500c00e0340b14168403903100c1400204165648410b0341c10a200e03201c1c1d00ca1070700244d500040d0940705480c4155075845003000901141d4601003107481c0c81801e62006030203900094240c502d003a04c0340704542c1c601490b000250100e1454083d4100c40c058002d18080314401090702c10820707039a115500658004c291065000f40c000c0c440d410a82e0302c0394049903596075025446070b01802c6040c4000c0c0500d00080300038038000c54101e0980d4106c1c4045d069507401002c0c3e002041200350304519014048078148415030314400c191046ca8245c2d0f00201d03421010001008035811289945481100c0b030150200802180102c1050340c45058a4059601140c0d0208456240d02c109402c0f075243c00c401c0c0188000402a103a01402c00410b044040d120801000550b546003c18003040d642c04034084890513080001c00c02c0004d82c104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 791390656 1250 791389406 791389409
    0xd1e02091e0303041a0d0903020f010501090209090601050a140c010b01021005061020010f0b0f030f03032a07030302070218060907080901020915041809020d0807080f0f070309 77
    0x78107940541400000100b5201d00c1a4001c1c500030303142600c0140043c0400c50101e84528003104410440b00415040081d00c5d204040102000d55082100026103100306009a81442c1d10080224907035484600043d034081e031000136054103100c041b081501c945192400500752683c3d5240020400c1c0583d00300090030b000041c011040341606d00310501142d0b48503500c00c0c02440c0164146580500340b045501030301c0840001c091032141d070804001c1c25480046400074903c0100584110031290f082004141e2519500d80344540079600510000300290510410000d114000d101100e000046031042c42e070250344000c20950210b034000900c00214180103c02081c0c0340f441185440e0181401030002e41522409401030f02000751850100702c0900080d8111420b004004080c1035042d00400241480e5400078865042152416440413200d0301d014041c01d251164020300480c402d80d050358400d01103401a040588019a044c450090700002d40c500500c200110a200e090302c44080f4030b8010701c21001c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 791391906 1250 791390656 791390689
    0x12901090b040308040509281512150b0f060706090c0b070f0b1801140106080c1227301602010c02041b21020a02030f0d1e0209 56
    0x20070080002c0b5080c44161400e4490840b481c81c40ca49410343c40d103400072001c11541044140c101040200f498003513001009141c041c2001003804c1caea8405204c040440c05041c050030341e00118801560a2070142d0143c1c0600a00502e4640b2601c0e244000c40c0c40d5030040304046174078580e0307528850148500d15206100030700e80544501d2412007655584000b2440c1640014007140e80e403004102ca000311122000a0404804001c00200c1109003401040c01c000b886898041401800440c0c41c0c0700402e030884500b440348001184950301c40d48404412241d0001d03103403079074124031402d2908284041c000918851407001000819401c0d4450f40c106c1c1c0d00245070302c03490504040002d103c490542c003510181503a02401e040144c808580080340103001c0008008203a40c00740300c0406940c540010800c8510206400c510b00050440d80070700089208240e05540580d00c00d00440e011514014018004071507040c80201720140d01150010807054a8085247c0051b0007007074469050a0406921404020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 791393156 1250 791391906 791391929
    0x3120b030307030c03051806030405010b0f04020a020a0305130807150f090302011d0a090516090f031e03030e030706020405010f030501050109090e070509070804020a0b09010207061101290109 84
    0x300c0d94013404002d9011001000e111001c41c0c1140c4001c0001d034040d24022000d80f803580d4030b00e86850101d009107483c40100703105684002003a016400e2034425a920001d0540007040760402940b400d50f4160003c1c0e00341801e0031001c0101182101040c0083d0b0000c200c1d0700b030416012105030314081c041e800c07181c80750b40c00c0041e21803040016070ba0081c07404a428002e9104060351030081808203082c81c46540000310b0f414100381c1030028003011903d21695010007552048055038603002c2c01468461184405484d50f50340c0250820004d803408046090980709050014480c0b8503031404606507040450107440c51940030804010558024044904130700c0309103020055503041c0381c0040c01078109402400c000300da0380c200070080c10600304516006400003d01608645c40e01d04001400312004803422802030300018400100c4680f0b503015100800416006800310a04007401100c4514046201e51143d40d01c0d4000003145141c14030000403503816080d2010710111032080054581159980184076400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 791394406 1250 791393156 791393167
    0x6070816090b0a1808070f05030a12031d01050c0d23010612020c060a02091008041e03030902060309010c02010e0c0a0513020403080f030412170615040b0703120b0303 73
    0x160312400c00015195108659500c40c190345404441d00e5821386400220b10700c0c102d001142c0020001181401c0b121070040d00c5440320f40350010306480e03203003111001b441208500d10542259000e504882c214404251059041603174403e075907800c0d50800e940381c0c0070a54000522240f10400d5006140750750102d9510542055803075400c803402c10304144901c1c003c000e04007609049060b0140c040781e481442071401c81d601c9080038400754000b0743c80303048403034403d150b0100c00c034544c68040c1000701e1149400c2004070031a80342c000100354228507038140450405d40d50f6602400181d641070082c45c028003131100000b0700c040c4080303406401c407074100e8156045644880914034040d511b5a4400e01580c80644a03890341c0304545c281040030b40204d0b000141440000300307c0300540d490305006148036a0258000b4040c480010310203840e100402040d04180c00200c0c2c00240c000e0421282d0803000104400a0300d2405586900c4101c1b01d0300301c2d0100310300062003540b605061800c1c81c0500007441c0d03c100c000e5480d19 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 791395656 1250 791394406 791394451
    0xb0a18060e1002121801020c032a070302011704110411090102010b1906032412170f03010509040f14010b04060b2d071704032f040b1908060708 63
    0x1050020014840103040c9034118621700c10a4040d1001c06c0411002c49445074a100b69488804401201450614550402052054100042000c110794040c0c43d0f0360700f20005141c61805140c00104150795070144140b907040981c03544d20601c14400102d022250700c40e40c07494002401c0d1404680014807a40a85484451200c40e81255030101c8009090000d65070b004000403503000700d5500c10000c1c60940a44002814502355000708060b140704500340d04c01040009815985405002c00d071040420040c001440f15040111185803c41d0240144240544403540c42002c81d40031000307503d0b01a51070700020046810302e80607102c0500b04501906040c860614200412484d1001462414403441c1030352030814070740c850494010f65000040d040c0c80f442c600122801c10b03070240c80104c92036003a40d050f07004444d414a10071101c41d181050b0085248440208003c0a0085800301d075030321072546500c48100d4980c1940c0c0200800c0c052004d00040d1800100c00307400040003c0641417841c814101c1c80411 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 791396906 1250 791395656 791395687
    0x1090504020a0c05060117060a1118010509040504060609060605070b2a0310030c05010305070906030509120c0a02010201060e0412210207031d04020906070b0a18060e1002 75
    0x255141510016180c194460782220020b070550f202a1060051038004503c508444030f41c0b1000d00d800b00116034032a2a02c0c014031041380c000d4420303200303204014000100203030001ca66808900304145016030415180301c0005044503002d07201200d034250380f035030204114404e03805640001c08080c20903a003040e4064868030490b10b0300604525155140b81c0380c2c40c02c103070100c0c040d44280048003c0025100d01c0c2510407040e550010707001c282d82c00d1100c800c002440c2e42c46400b400d4868120742c2d031a8030016103051000c1c0c01620002e405289075000e0013116022064a1034050110407149000804000703989000283c215403207500030384a00c1c2d0b030307000070000421742c1350080c020190100d180403605065103040181c403c00c00c001160300c50600010350102817680c03120310103042414043c440c800e1042d114081200724418040242e4014606000301c10120b948165029449100404041009140e80c484a00b0b0200300e0101281d01d96a213144184000c0b43c1040741c140329284641d8114076050580a40c07014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 791398156 1250 791396906 791396909
    0x3020a050402090a1206091b0302030a0303270c050f1c12050405150904050c0c1002030a0609230a0908120916141206041e0c0510031d0601050109 64
    0x7468000502404030b0b00d07901044002071407807070000340c0011111318000002e00504030041c0c0352029001c13a4400c90510484844040340d50003801880c80030000c0d5020740140030705685a00386965070f601c02000913154043e10b100014460510040c030301d424041081640251801181d015006412226031240c0340160072009d01d94121105032022100d4003400c444510554010380e801c407001140e8004005d00440140c1841502150140a16924007440b81c50702c1c000d1000000702580030640c240140e01d060b60003503804c400d105802081c9140c84620001c10f48a00c1038541042c80f1035031031600c00099021840680045c500c46007440311141ca5140d0714064081c0b4460511500140700c0841c1c0c0207182040500307040c40801c01100c0889a43d5081001100100d03003005004000e89400e00c00d081d10301245040c460740d4028030492103030b00903051140314041700344230485000142d1076000c64203036100303071400201d05129039002c00e4860448850080c01c0b40080c0d40e08160385d02010044c0311582c1c1102580c2d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 791399406 1250 791398156 791398159
    0x60f010501022d032a06070e060c0f03040608072d030203071211040f170a03030c020f0318010905041a09070e040905010e0f03041d04021201140105030f030403020a05 73
    0x100708583d181c0020300c50000008445144000a6520030107680070101044000c10405000a5a44480e00903a142c0c00202e44400010300450b030700076660700c2c200b400b4056054401040f00d01d2210b450034030514550054000c0c06c0032509000801804c1c0d030303000b817034400c08034000f40b032194245c1c52000310040009030400700f400900d6000702c001071903c1c6c850b51a40da041905001c0a0200361115189034009074014056400c0c95201d022010552001003003072012110305480003061a01190f071011401400c00079480002c50045801b10340c90048100003400c2520b00d4204002409001c0303400141c012216a8031490041b403c000c01040d1a034202e0356101c2e402801601c1c118070b0360b03659081c202e80348007000e4001580145060001d0742404415031000504001982c112403035078030f4800410b5176900440c0700ba40c50300e10a00c4020b0310b0408422030390b02d8001c2e102400b01c2e05c040f1004e451803803c0d202c40035242e02c9020860b0004204614007000351298500d50304000c0e6141a085801049004496001b03d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 791400656 1250 791399406 791399443
    0x911121207030509060a0f0306050d02092d04030815010801081e010b15071101030608120c031306021524040b060c0d02060f0108070e0a0903020106091508060f01050102 74
    0x10140b40c0220b086480d010001005165a1141000061325440c41340e010000003030315091022503d404c0c290340d5001c032150010102c1c0c14a0f0b07110b00506542e001c0d40d04800007006c48440c40c000781000c0e00141180114883c0d00c4450f4549080061080c07450f14010340c0ca81003000c82d000400c041c1001207100e02412403c0880106002e24510f000e5024048000640c0d0308860450640502c0504075400707040c00b144110050400c8620741d40044043e2281805000e0300c0d508103550b42c0140904010042034452417410642e07060030302d80d03140355030741440990240025070014000604100484151180d0100c00644d28841468449102141c061404400300e406184d413914040c02e00c2d42ea040590300c003020b501c0200c1d441c2000c80c1100039100d01041d181c0014503540c070b400104c0c0648002ca651410340354801c0980d0119a10f4038102005003c10450580c00c1d0356071500d01281d485014011980c0d0b2954580c0103103619841d0203442c07440d0030300080c500c20a50390004014000d81e0703404960144c8020307200180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 791401906 1250 791400656 791400667
    0xc141516050c030d03060611060c0a0507050a02061603030b010c0803010512070b030a060f1406030403050307170736120203030c06010906090c030b0f011809020c0109111212 76
    0x80d490410b10072040c981c0f5124452803150142c1d41034024800b5510036983d020950b0b100d007680c141d40e0b00f6013551440d1481c6000d02c08043c00900c1200940901c9000d103045400c081d0003a0085103459022a40401c0100740b00c02804081c0b607054024450181001c5c078200100580c07d85505481e404103000341031142c0c4441c2d035111101341e0304000100c0540512a0355664a0514a43c1030008046a10500c4000a200d100c0000c0089090303140e08407905001c1c05080c03450703849942c11101503100404840500c140c40c1c0103410600c010440040c8640120303124000d41c0403140d204078400c0c210030f085031a400d82408041101c41e20f41811130070102c0e0600c5c0817440942c00c0a20000b0300718000d1040109180c07041d0400040c801001d50030217000c5a0ba828000c00000c200907400b2016581400c289a410242d40e5407215102d5200340e0510321442c0c1007841c00440d44d6118803001c4141e91000700c030080a60b44400174103045c40544841c60b01445421200409580385000b040d035243d0640044d54480310901203074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 791403156 1250 791401906 791401913
    0x2031609050d0c1403101109030f030c030a050f070f0303052a070b070203120a14011203050a08060103020d0e03091905090112050c1c050610050a03020609040b04090c141516 76
    0x5101b8581a4080b418841500034030b0b1001d1454115010540c402e118040c886002c0b000007000b01e9a401512001451030030304400415911a07100d44400880d0400800c000300100d240103002c915418030980d40400c041c00e01d000c825000c0c2c10084800020040500c00d04ca096407881c400b110f898070b5010b080c108299586010627819170007084049041d8868100800c0000031340e0741e02c040d002c0030320b6170b01652036030341c854075041c03080344100c18003c010600810130041024010070429511601c14900903141100074a82e41c0e094070b00c402e0034184180e20218442c241c1e8540400305003035403580c031140047e120b13141c400000c2e54801c040c0303e0806100381804084052140602c2419214100a02048001c1140070342180410803140810740301409800003040c08000d401c40f019040702d50003064a12103505607000c024a84c0c5c403007400942c1c050703620380303609405856074010211600e0080c000107145510b041c401c6000061200d180b18803c140c0c3d030902904040300e285c103541d0b100050194444c070074451031a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 791404406 1250 791403156 791403163
    0x20108060a0504050f0702011103070905090421030621020a05012102030c1207020601141203211605030709090e03070b010e0a0b01091206091502031609050d0c1403 72
    0x2c1000d50450b003000700f003200004080d62428001e026640c0200540d11500080034842e0105a6520002400c107100800192400b101241d421038011920f02100c0c40040b40c80b52034603140a4265000f1035169a4200580c050b811a5240302c5004804100504106580050300040107801b51905000140400b081c40b80212a441600209580801c66884c1012501d080c103640060340944144200480015000c03403012070320742c0c102c442000c0041a10000d42041202405003462002001d11060050040b90114941c40140018000c41d5240c210f0410818105400400e40641020b0010820500c00d000303601510881c100c03500000001807141c0044281810740c82420b46c0a4505201c1500224103c181a5003040c02000c01c0c007420048108079400640e0301c001c55100d13901e01e00380d510002c10b020500c00d03009816020f101d0741084096040b0310100000700d030000e071181065800030001174546642c0005011740a04821140506c3c90030684d51583c08005da02d00a2a034246032480f403502d03182d103080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 791405656 1250 791404406 791404409
    0xf030109031d0a05210f0f06010f0519090c02101d0c0307030506060f0d08030702010f05060d03020616020102190c05100e031c0e0a030e1003050403050d0509071701020c0622020108060a 81
    0x30346c251000c00821001159581c0d00a0040043d84508103000007001d162000e0481c1c91030b0321028014054034034101e00403004041da01307011811b500400e80c0c4030040308840e1007038000e6100100a011203042a01444600e04204030700101e0203507200e22000e1000c6140003038941d41c08101210110000c96030300000c6010f444448500414400c00441400003c1f50190080b40108482c210200080c0e5281820864110305a94028015030005008500001241d450070a84506039000141c030b07140e5803441105120f01c042444400050702c3d00c03405c0c01040000e2010a50300c040040307042c84505001c0580f95100d2144584580b110400d410207030048202c00c1c0c200d1742141100d0f03000d8038441c9059050241c6800d8a10060786c1c400c4901e6000040c440303000c0d11400d8081d540543d2221b041c80c20317407030112005190160114081d4458a00c0004600603041e101c41180001900050b0b20303000c00070f94a41ca04a4090021005a07021400b074502101815200320092602407030b001d002515031002003000013406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 791406906 1250 791405656 791405683
    0x2030c12130f05060604050709050f04051b0c070806070315060f02010603050607021f20030a02090a0b1b010c050901120e0714090f10140f030109031d0a0521 69
    0x20b81c8010a00c00b0205056110741003c0e0f40038080b6944121040351120824050180d20449075562280241003e40c421584541010b1a106c035500640041360300d15001340c0c44000c210351020806101610003806026000441c0f420180850400c000c0e580791000080c3c001d5034108850300d815140014400d40021000756002070544849051000000f51210480100000100f40d202144103020b942032207074030601c1032840840c856001010741002401d9102400d40000981c00307000b00c0b01c0c255078040000c030040c0403203c0141d544000610000c24240c00b4140d007032815924042c3e48c8242c481c0c000007201d08484003482d0070b0f0b1702a43c2d030403004001081c0c03c485d040400d101e0f068011500841400c24000d8407030b8211110049952000c7c2040703004d0030211102a164100c00200b0007064540c101c8851510f48003d003250154640c0d00c0110b421210020801e8002031079040d201054290340302d61900000b0000e81e4101c01c0907041902040700311685040100303d89888917502c1d55209000d128070b80c3d00c000c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 791408156 1250 791406906 791406923
    0x20405040308010f0f08151003051b0f090424020c011a01023007061103070c140d0c08070302073206070510200f030103050c01020102030c1213 63
    0x90905000b05034103402d018841c451140040045040800c2c0e46140003152400310080c5403604a04041c0020000003819940d011003048801200242c818010742410308140c480240e03922107540b081181c401c040d001214007801815060101143d016094164130540d1507a8124010406200b0756000f0f205900c4100025480c1405e03070307005003c802d003031000c2e001d2090b03007160007640041406c5001030718501c11118804440b41d904c039903c0c101c020050915140110ac0c0001c3e00c41b407400c2515505c1e8000c0f9512000101041005c10800c40801926920080a80c008240105d4001c0c00502a4610440d000d08090700206013001090310030814180a81080f6100b40c200001e0b208080b03020080d60032407070291814442004589050005c190756010380c0210080c020041e07000b111000414080340c0a0102c080e5005001003c508400010154003002e950340c50b5580d0701d5402c0c22414110413050480c11a401001072022070035064003540d040801d500600c01e00360311662507103641c25401080091a864 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 791409406 1250 791408156 791408161
    0x3080402220b030606181503031b0d021006060905090408160b090c0405041203021305090106090509060406050d15140f091b100f02030c030409050912040e0c090d020405 74
    0x40c8650040400d48000f0b03400c441c1980c58500c200105040e50000203c0361842e0100040e902c5148801542d05214000c0d041d07034640541c1c02a0401044015500e03c040303a481403151a045950410a0b00700c80100b500042204c241481c0c001050a2140c0c4541882000c0550215050254201c00c55207a9040341e03201c145078190034540500e44100481c0c46021500a2807060001410319020340c40c8101c1e4020b6003503400e01d0010005070002d42000b851203030000c1c031820010501d52280303124540070300241d44800100303920780350800c410a00018901400350782004401c000f5034481c644082816940041c05407400d0f05041d034800c0c0245402070004105505180902c00c81d00300340940340303028240a40c2a1055a4065445d443c21882c0c0c06081d82d030404040c00e448030032248100a000c03440c0350184103807440c0c07207481140345141d6003040d08483c40a50392041840f469803010006240d00c81c00310240241032516280403803120401c000c1000d07030341c003200195800c015900c41c058070703490580c000c10400c502d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 791410656 1250 791409406 791409469
    0x8040f081e0307051509011d0606040c030612080a0c06060b18031c1116080d030605010206070504090b01140d0605120a0c03021002070806070302030a180f03080402 72
    0x28480c030508404492500d000789450340c80084102c640f020782100c01085140c0035102e03a4080e91900900b040c40e955070700c2070001c06c1900554025144400808024105810400c04010450306d401e400d20b414945050420410f503030705d0340044454650007440864480c0c22070141030b203010007114801480c2d0703881c04038081000e845001c050700c5840030004d460f51351003100e42b0616030344d10b40022055039018260320800e8601031041c2062852002c0d4103069602030514610030080045540d000301043e60480c84000035142d46c9482070400407c001d100a00141c10004400703045442640180d211551712600030145c41c1e40901100e80901d0840c5014583d114424800f64000341540c0c000c1034400e00c03120320121480280000c81101c565000356a441070545581d003000665a40843c0050550158120015149070140142c6116501c551009a50307807500d968404c04a400c6610b904041e1921600a00c0204158600b1841c5213949410700d8402601c031400002e403590041d8608610401c2202440c6214 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 791411906 1250 791410656 791410663
    0x60705160f0306060b030126030906040602030c011b1403070e0a03060c08090705010923120303040303060e04150e010b030102040b1c022803141017070e060d08040f08 73
    0x202c1e4010801040050340b13800b4443d50070b1001384501000a0300a505c40005c500d00c048030003520355242001caa142c07480d20004501d40750416480381d030140c1c0000c44e082509030000e029040c2070407181d0701092011401d0b80c402521019030000e070845d10780340120001d8142c50041000c824880e0f4000d2110350307801d5881c640a006000440711306800505442d0115041010000d9071500703450b0140c4614043d14142007001d000c240800e00f03d4900c00c819441e40c0006500d41440084290b00084007441d542c0c070785801c0250541d140c07644544541d40d1510300708401300740700c0184070600464002010034001106000a13025201c0c00302140d615520001e000111400c1d58001014807084080383c8000b140520840e4000320b0180040d0a1074954010b45243d203260301c01c10703514011030b00c01e04000400307000c0861043c2d400041115015856030862500344000c200d40800c100788140d052004020041c00c045494003100300140590740130b881e44000400c02c000251054402416007501e542042c550380300840c40d41c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 791413156 1250 791411906 791411909
    0xf032d041a0f0606090310020403030504240c0809030109051006090c030504080d0c180e1803090a0302040b0307032f19051003140a0e2802060705160f 66
    0x40a09448071207803440210504020710400801180d41159907600d400c0c4186644140b10090341809081c5106d880f13103226101801c003860282d6602600e9a0401c203007900f010b203000388003d04458440f0b00c10b0f00e00c0d5a20003070080380c5940c40b804a507241c003c1100440c3c0544101030005226000c2c0c180c03d406042107560020003114034203a4140142c2c6580042a401c0790b40c1950064a417410410154041421a8010707801d0700003070740380c00c2031250130b60b800c1203e4000854004200009488061042c10201e08403903c0401c1c0a1501844c0303002c04000c00a0b401d80c0d05880300038096178695412001603030342408404015034200c080e011400e046400711160b01c0e550240c00c07040c0b0700c071340c500355101c40d0501c03601c0c20074440c0d02c2d82d01000c00ca0b810070080210004041c500340b000c03d07440b0040000c514040131139031030248514540200b52242109051406e0100c10401e0f0f1814407940f124108003809104e80340401990180c0301c1c29500e0401e401c02908099034107141c0c00300c048244400203209203001c9070000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 791414406 1250 791413156 791413163
    0x8011a04050112110d030519111b06092b030504050405090304080d0305090307062d0b03030d05040f0206030103050a03080a09080a08090705041503020a050f03030f032d04 75
    0x1050380c0740d80c040e00f480940c140002c0c242c510b03c003068510509140381c481000d24000e050050404104c010f8280c0b040341a900c4540011700c09080703943c60460b04100031690041403066001d92032842c02c002c03407203034000c1c106990304c80c4015042021400910380b21211003065850780002d0344403114203000e000c5501500c60140118030b0040000d40d061000f0041d5001d45d00ca50018207005240f018045010344000f82000813240000c10928001072628400d813081508040e60f80d03540080901810030602700714605424019090030440d400f076643c080211100f58000c04400140c1da165810300794441107426000039004a0f0000c004001e101d00001c1c007c1c0094172a945418141e603030b101c090b1090b81c0b43d00e04000c0802106000602050303001e02c0c0380c81c3d80814090200c81d00d075035540d4005810b842c103405240710b11042031141030055091244d80500645002d691400080072503c01180e928030941e68620302030030f80480421105803440200100b1143c0031070149032015594045000321140959048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 791415656 1250 791414406 791414411
    0xf0902040f08061b03090114010f1e0b1b0717070e160f1d030a06020a0917060a09031107030819233a06051807120608011a04 55
    0x50b00707250000c3c002c1d2003850710303102c4440b0300500364035040030617000070300140525502c4030f181a4400c42600c000034000c04c000d101d080740c0360386010002a036512403d0030a492144481c0000c0c070005848500300e60b8480032102e8411080c2541c0c41c0081c5c1000707403507040800d01d4022001840c0741c00c040000d85c2c0c81503880048000c0740d07a4a800703441c0c084c0e00b40312404541c0850303015117290020320701404000c410386480008802d14003141000181c100504010100d41c09030380841c000100c0c5078400e4901001d0714005081108132001403950039624080102081c00b800e48507500c140800d4410344c0010441002c0d03c0456800c15200c0c6405c61050b04031040f5403a8a44600d0004504648900300740048000d02918003078404801000c00c110990004011241e004010700302d400380868078400310030130302d901c95084c1182000b002e00282c007601c420364001c5106035002c00240e01c103191105100f6070070492a040a0381610348035490030b40540020750208129501e442003182e40015820b46009140c0000c4404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 791416906 1250 791415656 791415659
    0x100908190b06063109050a0518030a08011502010e0708010903021516080702030c03070f020f01031104090209010912080307031b120b0415030c0305010e010c140d060f0902040f 77
    0x14000f0f280680010000c00c40307902031106511244200100e00d00d404410a590581070325800d212040d00d0382500c2d0060f62a42d0b81e005c1040c0900e09451014180c41ea59000c0c518120803104000c10201e41030040d202c5611401104400a500035805500c03050030242c1a100f80c15501c040c0c1c14000c02141c0c40550241c05100c0180c07000b105c0d0602e88a00c5500a041c03040c00a2440240480e04d404c80201070500f9440104400d8650b090300b00702030300b0107601c00e041e4035141e90040c2c414005031081d1030759400c2c141802c1500440b201e07814071056500740c52285400684604500004070f51500e210b074420328020003500c04d581d0a010000000350702c188204d403814400500d104070a000300211004101000401000340e081c01000150040e080152005002040380003008902c0301200304644e10480e01c0c0c00310031a041040003401c0c0101c3c42500080d0008101e07640c15454080c0101112240320f52890703000048107101008030380c0c0658041e01e601e0b040c515072561141000b400941c014062009030301c240900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 791418156 1250 791416906 791416909
    0x3050318030303041211070b130f05030307020109151e050301140d120c030504030b090102030f1321030207170d1406030a080f0712030b100c0b06100908190b06 70
    0x110f90290358011717030130801d03c03d02e02022614008980707030003a01401b842030001076182001025001d0215860220403040c0e1501100600d2402c4603444103009400038081d0401503a0044503060844004444d00b140410103030038100d0303003403201c000100d4210031080c07095003085500402450585000c0380b001c8101221080402101042120000301340410a0082d803d60501c41c0307020b40780c864480d04015060984070741d100703840d0040403100221942c0d80030041204090b0750359410b5800803040040010034044a440d003101c80c0e02111000ca121081c401019640700b40319038100d41c80c0c52703008a03e13510500f00d21074803503446900012100101d00c0c200000d1000010407100124002c1100070010401c0321406e03510000c4a03000600b140b0070551042c0400c4000c1621401e002d0020b0030030750b400080084d19003080251604003150f00104004902d8003160018885890440d04004222000d501a9560502c2100c0140781d84d04280700714000c03110300601c901030306500f61814601c1410f161450f079480c50b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 791419406 1250 791418156 791418163
    0x3040c0e0112023001090b042d060c1b030804120311160303060302060d021c06030809090604060f080c0a0902250c030b040b060f09280905070305031803 67
    0x2c00196010301801041d81c80703500310b0302d8000551301c10f14600c0e0000340304500001e4215901b0400684120300b418040004000801c41e01c0341e042105d00b03001252140d08081103d100c20359142e401400190f43d4548500c140b8003070201207600913486000c044030b601d8540f600034940d2a0580b0308480c8020b242c2c2107241009d0090003800c040708000b0f0490380c10100ca54040c82000c1c03412901c01c0d000d040d40c418000c0050b8560790010701e9089880034001d40d940c00750b0202c071070540d800b41101441c82490040c0501c0010140e40482c0c0790b00300304981d520240d803200c100240042c401544591039405035044001250940451200640f91045401003130032036440754403400760311a83c1506041d080f00010152946441c80c031050b11007501400302c5007482c0f6100c1c0d48082c0100000d0f00c09451401c040300c200150780c54011103240106000b545c6d0200c0b0383c2440c110003051410000c0482c10030404d041e40038191820a036002c4440e640c2c2081c1100c880381e5981c24000d4599208505815412000f000900039074203000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 791420656 1250 791419406 791419439
    0x304030b1303030b04110d09080c1c090501090b04030b1f080a0203151302011b1b290318010e1905062a0307020c041a010f0912111503040c0e01 63
    0x5010b071b6450701800b5529030000740b0040c201100d0201c424401e504c10341c1300400c2031000e032031a01c00d542020080070719405003544405520040c10010140c00a00101008209031422654484000d581d00c0c0c4401d40c10f018031007101010181c017501c0350440080c48003400981802c1e0a40280e0940d1b914000b51108100c820f4012918001a480105900030044d407140d28040081d80c48641403000c1da03951980ea518420404501c46c0319003600c0400c0612404001c10000071503401c1c203110041c80c0524102c10102c6500000305040355600c118070200c066420207403c030744078040c0c2c2a002e80f49000003411040024280e403900c2038400e48140d40000c3d805d90b10942c00c1c14540e41000b400f50029444001c202030841d071004184c0402c40c0958500040c5a848500855112444a50302d07200b4592141c0c00040c0000b00040e2024100702050303130700700100080003600f03074001a0855a50500d4070040d00c04124200d00840c003a0522460010800081c02039002220060f54019445c2d901c45980c2c58002c1848010340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 791421906 1250 791420656 791420681
    0x1401020415080c0301120512042907030f031107140307060b0922082802010c020d05030417120a0b13060e070807020708072904080d030b01020304030b1303030b04 71
    0x10001404030456500d5039142040c4a036048840460f0103500404072500300d03074000030105a00419542052b211028141c4084140113842c9040c0029510300600030317030030181d000742403550f622080c50105200c2001c403814645c200341c800c201c0f850000036403a41c0340d002c45020360f80b1515004803400649004000a0300548402d5011900004640181d49441030911421560034508002c5400400c001282d03c2400703002a144034829076008060103825101d600f002041150031400f002c0d051107400c802929080380d00010904e103580051000503845129044807070340002c1d41401040103200303590704403908240d029200c10007034003135101c20303c030584006004128901d02d801c40001c22080c403814404d039102c034813031044411a175602c401241c140368140e0840e500f0f0002001620a9504c0065405072511500c0d030312283c0383c645000d6647d45c84006100014040646903e5440e0341303a0b07c06c005031000b441c0c110310020994200b800c40445200400c0030100e012074100508003850346010711840450105 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 791423156 1250 791421906 791421931
    0xf0513021207030b210f0c0105160308100314030307020d030b010503070302091305010803090f100816050405100302191d060d0906050408030f13050721140102041508 73
    0x6403120154040c3c10813a01d010740210a40b00042008081c0c0e003440c0c12440402000307460306541c066846030a22000007910340c10f109041101206000c00d03011611301c0c03e40c040ca0480c0300c40d103030104810401c00c916030014180742490080d078842050301100850042c0c420b9000c880d920b00b030100d010b0342510038580d001030221f03c4c14000681c046020ba0020215940010b20a1541031018240c03001102c10a80005505910203c2c207500242001c00000c0c000803c103c904407803940820900070140c0000622804070344060780c15a040c80c030300420981d40034060040402c1021460f8000050080d042600e9028164101107a00c0d0a2180900c01d0b005003175040c01c0781a04242d0721182444040d900c00101104130680c2c9841500c00b0410034030459000e02c1c42000130594a0400c007007111402500504050700c3c43c01385c4d07001c42001450001f0070104840720024907100c0340401c3c164a14007040a040041d00b14101e10000c1818800d0640c0204281c4150301e0041c1d110300c112580c200c0e800c0c01c04603a110f08044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 791424406 1250 791423156 791423161
    0x1030b06011d0d0f0c031a1608130813150306050411040501261e012117040f0308120105010504080a0b061f02160801021602090c04030c120201090501050c060a0e070f0f05130212 78
    0x1802c800d00c7c01cad030a60203420420300d442a54544005440c2d180c1e80240080c17154072050a0380c255060103520024902101c003408003c0030034001c81d40a00c0b8600c59203052080d1140c0501000200c4c030940e9094844482c0c1c0355003149000a411000000580e80c4424196008000410b603407020b44207048010007505031284065019980768180e900ca607546506120206100000780e003052501600301451007030813a203403030388000c602c2e09100c0310060300004d0600009010906c5160390000f020245190401140d1003aa00c982d0086a1010032800c504c0070a62030b288900042aa000200700c0520b0040c88104a01a950b400e212402c030f00807001000e1144160819101c0507162070f0600c190400400c201141c9055601c0d912001c0510b250390001e14010103816104080d507801c00034440c0101006c0c20f00c24a0444651042d644480e030040c11035414596954840015410402c21003000e42482a411030b4040e84501482d03c0d001000e20416200ba2080f410142d8006801c1c025104c100e50100000b8a168 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 791425656 1250 791424406 791424421
    0x302070b0402102a0210020a0b0c030a090804120506071e030905010204090213060e0d110607170c0f0c1c031103090d060501030b06011d0d0f0c031a1608 67
    0x820250380b059040210030341402c21813200d128980058042c2405030b94068440c144180100c07401d0b41e003c241d0964004450520202d9988101550310030b0003108001d913603945030b41030223004001400000c0c09402002c80c0218200110000c034a080d00d0260301181c2480c0e81c0e80100326041e800a0441c400e1540443c50f04c920224060340181503c1ca00c00d1001604054a80c0000012a007051413840301c030b01e107411810450280c1005020751110810754105242240603101c44060031440d10b01e45008480c002454cc041c48014030816000151082c6402e40c3c90031030640c05941c8244c4403000300400d001e01140d444072031401d00100040c0b0b102088010700303558595242552102c903510200c5040740010001b801833643d404002c0011140300d108001241e50640c1040511000f004103100c0c1801002c10042c004503003001000054442c0488110280412034645101c9003100321100034686066620088100920381d444406820304d807110844642e92039008078000c6108528016021615031404034194 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 791426906 1250 791425656 791425669
    0x60209010816050406200d051b1204030f06230603010b060720011803030c0b0a0902130c0c06021206090f0708010915081b0306100e0f25080a0b010302070b0402 70
    0x20211b10300351114800c5034180e00d0030b04a0b52103440f0b000940005020110810b1113421211110080b00200f080016184510941e0b1140c1d0002070300078006c81020394104282d5403c401d044260a400b080284614000c40c203094000580c0c42500c0783d4205464800c66046c100180c441150300002060403442c09016010250365900d98214100503041243e1880d04826618440055100303582d00e8a000125050030429403501803d030402036070516401e1800350756249051503c1e08006000003d403114041c406641c48081c0300001000b00d400800d140c00d02e246003003141c0f4807460303003610b0020542d81c4440f1050759502045a060b0049696500184601c2280d90b00114400000c0b0207039a2500342c0311500989400c0403c4404000d9044011402209007000d11103290054541200d00f0022818040c1d802c00e2820000c2004044a03c00f100085001c1d9101c400d2803a04040150103519055070010001c114200c100c0310049207901300b1880b68400c2d48240b0072106000e4000e040d490322911aa820880c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 791428156 1250 791426906 791426927
    0x61803090a05120a050d110706030606020d12022b06080a0b0103060b06070206070818060c151515070302011a0d080318070620060c04151407060209010816050406 71
    0x54884c00c03000384d0001c0c104120342040807000f51201324030190011840740c40d01c0b141d44c02880416040c0442004245c1e00003442100c842d446003407810400a2010f24407000f0300401c460480742c10015000001503890241656800140c000020f01a441d1110038180d61240d01c980003c101607042801040170407840c0e403140111113001442240760154540004416403c40395098458000003d95404121051510000c00b82c4040e10a503060522070a089a11140420602481c0012079800500100d44020510902d0400104ac0d5100d030b0030a585048400d81001c9000c50240d071034520a105885001d08441c12031560050142d602c00380c180e510084d0b1070f00054040b501c00710000c01080d1107400e05101ca10040d14003030780d546000c1c0350101c10304186407440344803184c105d400403000d0103020b0070180c003114140c0e005040f1440501c040810101e503083d00d21000048000e4012a452007000305076001006540380c00d82c5c1d0a0b070316844194804070b035400c2c10a00c40c0040340080104000c01d5004014498 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 791429406 1250 791428156 791428189
    0x11503051509180f0304060305090f0106080303220803131401020301240c0204062403110d0c090806010f0e1501020607030c0c1401091704030302150604060b0c061803090a05 76
    0x415000d51348502620315007007604941c0100c4c0d124410008000c40030040a800c080f106402030192a141c900700036201c1c0320140c5802040f91303046094440c0626013001c0d159201b9030044c2c110350780c9c3c541000d06030000410084112008150108001002c1d1300500030341e410703a54801ca20054200b150010b9489005c1c0d03140e20442440072401e048000340c0d90b50f12460300240381060b160074103c0e00c809051001e640c4098052000e0618280f880c4440e25000b1041c1ca42160300040000b6981c200c001007030700c054165602640591007140c00105054100305c08060403502415841c4000c0d484c3c10102e01c0c1d00700406131046006902000016003d1413007600440142851410400c4e6885115146c00c0d01c0d14194441d00e00030307603454000071000c003c04408148181040100000c2c00c050550f54000e4440442061021140340c1020100f441540c035940140000c00c031034404595650301c0094207948400c822502c510a001000300e01ca03040074004003c845802c0c600400c0780406508100400c01c41c070401e000d449 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 791430656 1250 791429406 791429413
    0x1030515060c0f060a090b06060c0f0a12031802091b0409110306030c0415062a031707081504110702030106121b0e010b0a1701150305150918 62
    0x10340d103460740d40040201d0034040000c1d201019803405810b107000d00103040204450b1030444800e020603016560b007600305d40200c0791683e0310000181c0c03051a200c0700ea00c032010140a003001140400c16000440c1d82c0c0501c15881c1070110b007403203000e0701c00000300520001c0c0d0003401c0079000840300f0382d5045403e280b13195021941030800340c85941e0b120032107080d04070816441d80000103002c0700d807408210103d90782c0c404450a00c40355030096241110152144034141c180000e41c2e0803111407541c3d088106518420135160134a5441c3c3c1420003c1c1181007180c600d140c14401503000c182641c2c860a0442d10900740e02814080b480d55031000e1100400f00814030050a050074800100184d03420701404005040c00f01e0403d80686071400c0c85a49080b00c8241f120f0141c00342242004507005400420f811184070318521038851283c2030095464807000650402400c1e20b06002242070f4120f9107500700c401410787c0d403c01ca16900c50012211600c500b038846a40900100d00240c0205070f0b039101c00310000b42c0b22044c4d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 791431906 1250 791430656 791430691
    0xc170112030c0b04050f1c02150408250f06060e090c031e07030515090601060f0f030b0d0507061d0604081c1806080610020c0a050402031e0f0402180705030105010305 73
    0xc0c07e1400e07044140002e20409803151000c0c0d541006a1900400c03110101580c40c20290f480b008103200d8503028004000e40c0207608541460102403015209401c0880364910300c6c543e20f0020002e100c1030054000c40344000c0045542d800000801d0001c420303001c2c0c0205000304440d40140346113074031415041c0c61841307850408400070780c080c00030305602c41c2c890351075148a05290504074101201600920308000320411940a13056100b8400040340183d07003400580e031f072401004240c00589108000d0064411040c0000364180e100780ca07150107401000302c1d2540f98a405c030810100340308a102d50103140c0c4c0030304c603c005c1c18101a400940040514140306d00f0503403441903103400c004410391100000c02c0c0300b8400c000450130000c80000000d450ba00c007400704c0140107400107480c0c400c0c6005260140d0350100008d103200c200b0660100307000c40d008501c40094602040041d50080c01100e00f207000b00c0241c060580380c00060390a0a010384810740741d1900b580e007403000440003040000e040498076003400c40c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 791433156 1250 791431906 791431933
    0x91511090607050606011710031214071401180c0312030902120703020f0103050c120702030d0e16080304080613060906050c1306051c1d010c170112030c0b0405 70
    0x2009aa07110f40050507852400c64005005490100c951610701072400040040c0044800c02c11825a5031100c6440f4541000003800c40e51012a0004410341c1d03034002420300b003880300324424000700c014240000c7c000320280c1041030504201070f4400078010000000e05000103503900560010758141841d00285040060700016614420000b1003d0150041072052041d4106108407403150002802c1c03d01c910709010180181134883c8045040c1e84000c21400701c0e040318400c0c0100d0762500c21007101032100c032140d0f01d419174070f4822030702c00031507048603060002074008004000d44003100c0c08480030303010720394600310340f2441c0c10350003801100e8065641e101a0b000034001d00c90a07001d0380c41720810949848260800b120384680d1500b140083c060144990054601e03452503440c4a400c41c0702001c19030320b070401c4130000048041e41080030729500b0710354400451640305200344c203090f42034042105543d80e54402c50641a440c00000703030002e01c3c414141c1c0c0c08a01c0d05c048040c0c00038400c03022168011440903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 791434406 1250 791433156 791433169
    0x30d181208072001020705040905010f0519240e04021906050c070f0f03081305032a0109080c010c0501020f0d02070c0b2d0705100c0905180105090c190c1509151109 72
    0xe07107074ec1c14012400011100d09030307184500c840d03c00341d4034042d504101e00502c0c5056129014481d0642c1408150001411516051510b111380c00035480c10304021920303007002411941040c013031544180301d03d40001800a405040070822142071000100d44c3c2811510b441c42c460b489680381c035202d014042c90000752a00c01300040d00c2d000806294062010084a400800d8184076060950411105c60010301000790013061500c06070900342400200a882480d050b800ba01442c58541d507201c20110381030382040042e80040000a110381240b030f03121929496421315038091600441d0302c079505003125950303481d240d0036400c0701c01c1c0d400f58200d03040050a540c0c0d03e140441d4800700e1044d15480c0d10350703406c5050f003104001000e0402100d51581c996003034090302994403014419103220710070b001c01140780d107120703402101c1e140c25480f41006d91590904001812105502104403205544801a2144d9507060300c10f41a8407607104e030070107504aaa5110345005014652510003030242c0c02c01090030151fa481 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 791435656 1250 791434406 791434411
    0x1c1403040602090a0b0c07090617060f1801020d2003091b060409020d140105100c08071e1103100203091914030a11060a0209030d181208072001020705040905010f05 72
    0x146d0042c031116007480d82d010309540203644601e0401005084845103040c01183c4030b5841000c502c110589540d0716441c1080c2402d01254081141d407002403441c6051500c0c1c3c0184008005140b8104460366003002d41d40418030044a00403da031b007120459613008015601c11342c000000080050b800d29031102400c0040fa401814101001691000c402c29030b135480c024040d0043c10101c4610314110681100070740815041d03400140820b200094402c04c122003074400b08952003d43e42c41c0c0004101d00d20340304940740550404644240302d1280e00000030700352402200d00c20352004000d803030403510041c0c900c1c0c0340c00e07001075041f9000c00d8030a018400c00d000400141000d01d1342c55443d402002240041941403070703409014401c072140100080ca625031800511004580d0440c6004045017070242000d041d1810346800c2400840b9101c0481340070701c05441d0182c0070540c05104101c2c0c40e00700d0510346a02c040c80c101d502e98056000502d08103e0b601c1c150b408200090300801c0041482c400b004c280b1401c45508 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 791436906 1250 791435656 791435677
    0x2c04030804170a0302090a0b040501121805060108060f09010c0f0c060608100207170c06060d0c0e2d2e08030c0703051002090112020a051b1c1403040602090a0b 70
    0x2080d60000c6140c2007c0d03a000070000300d5411803a003400c0030700080c440242c0c0380c20003000607150304904124110042080d440b050b0000103540c02540c507100c10507100c2c401a18003d148085820105110480c184129000186183c0b10076194901444050716180744e014801d0b40c41950700d03500050200c00c1131180c01d0302440c92440c016544d40c411f10341410f00c081031624822070a5024089030003900d00010384503030800c000300c991003040c0426150001202140c1d0300028041c075007160502c076402c81d40070340ca41071152820f01703a00c00700c02004003135241c41c103000c64112108000c94071042001907000b0b0b07141c003100d29404054400c1d80d80c0320300301d161542c0d102004021455001420810500c0030500011710240c000000662400e100440000c0c100301c015114505503072f0b8001819a41640258100d13200315425110045000b0340c100c08181c1c6030740d1406039000008280c40150800b0034424a072002000c6144c80c1d819040d0b880350f0b1100303402504242d40d55074000310040804030780d507000d1401a0a80c00c40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 791438156 1250 791436906 791436911
    0xb1801030b072c011407050f030403060b100c022b120f02031c11070b040c05030607171f030c0801020309010b151806130803042c04030804170a03 64
    0xc00440081103e202101c580f035690800c43e00107840f0010141000d02c00c0c0f0301c24a028926011203003820465803180040050103072043d407803003100d1124084080c0049034015a0108030608141c818000300240e0040100f0000b15101100401032500c425249560410052911565000c00c58141c56400e00000103850110741c84080031a000c1e8809800c500c0042e00b48061800c042c1e0b0f80005014010b6050400d1203000c0d1135151708024442c1560646101c3c64202c0000c0e03509042c00d003484100b00c0c200740203050280c010704000850b140c0c0286858050b8243c280010300340366a0300c1855440c14401203c450000300003204001010610946406001c0e0410380b00042ea0790401c4083c040c00c588209100500a4600600035134142980100340c50303045004000f40f00808403d0400509944100703001a0101212100040307810304001028100350b801c1c00300307181a40c464026101400d0041c07094404981844040000e002900ca00d1480e81c01038854849180801489041c503502a0440041100001d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 791439406 1250 791438156 791438161
    0x1107020405090c0109061b08030a02030720030901030b06090d03050a270306020304060e0105160809030306061603020309090406090210211512030e0114040f06030b1801030b 76
    0x280901c665908020260001e150b07940080001808001c014400d000521101d90f503981d0014041590400e40e880c0e1008400f6a24608502d5070b0000f50015079000000602c800303030303600b400303515050300d402120500c900543c1803c400700011805025060440c940000003400344140e035403034180d102100d580c801d40b00d55846560300e0f100102141847e850300143c0300703000f0031020038821400e400407095075040140940d13256550f081c400017030042004074010303c0d03103080c0400c140761802c80a184110f1000d0703a42c261080c1c0b101013100c1d9407400181c4800e0f80c8201c0c20040d54021108028212599520a0060700c3c185849000096010282102c05556843e200c0b001401145024503030412555444d0070041e0910140700c1c10404600610866040025035800b4903e1400d1203034650100140182116015511618500100000e60f50701310310b804a10000c07401d0541c2c0c0c003100150f501380c0b01c1006a80c00e00915003603049000d064110760b040c1d0044090b041c03074080e442d130034081c4501070f5004460f00400360 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 791440656 1250 791439406 791439409
    0x180b160522120b07120b0d030e120a05030c070605030115110f25061b0809010c0506090f01050f091513080705160605121303111e060105040c080604110409110702 71
    0x98417014040380080d0b140401c001e4440d5900ca001e480c1c0d1039014542001d61020200225104561002018416114010841041040010062816000003426264040c0d0745d081c0c1610b0340d000038000c40f01d4100403c02c000c500c2c5441250700701030b50305419040b00c40b0005403010f10f0b41401c694110012583c2d6494250340c0c4803072003a003440c0c00184694509500c460400420040c4440c1c2003440007040d23118001440b243c0c0768030807405d0b0a5140d4002e0181c51071130a100e05455910104031185e83d10b00c2d401c1100140200c022504018840c1c200d84001c2c043d15010401c800c2c0004900410442c40b040c1c2240d19440410301c418060240e403440340001340581411100303240122001079000504000c003c0028068007070780120350507000300c41039003420350890441c075060b5002a400303031801110740b10384080441120101400f0840c0f80003441c05403a000e903250414030082c1d4014908a0000c91030810200301130341440d500010718100a42d81c51030030142ca8500040680c0c04000c0043e0000c4404601001075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 791441906 1250 791440656 791440667
    0xf0303020106060e0d24020a020105040606080705130e1e0c03160513050a0f0e0a140601030803180a020415030201081e0c0705030d180b160522120b07 66
    0x5001c01c0d080071360764555480c000074051201c10700020038115085c110304400c10381d0741c0d100e007034072003a480015503e035005c0500090082c54122401d80b0110b0910000150703410300401d03c40161440a080c103191018001e030120068040c0c8543c188062044014200c0301c000c58075644164614400090001e92001500701442d0041d0700403110000d00207950100025a03400300b02d94842600b81c800400c3c9a83c87c9520300b07004040820002c064203060024100b0300038004141c6121451045c800d550596501383c030417554600003408028a484001c0000c100440c1061611404858074541141c0f40c1000c0b40d80460b0640c2d00c6000c5442011041102c140115a0044002039204e001d0791581c4203030b5520390076561401c0001404500229038001072941c03e10000780219400c500f8910b000740140621411401c0515005000c01e81d45d400d800e030041449140c05051080f066500c52380d6180c1041c00462210800441d0180c0007001d41d07814400020300c0c8005040591580b60103908001624900708501411 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 791443156 1250 791441906 791441909
    0xa1404030501050708040318051f11060a0212010815130623010f06020f10050403140309030310080109021e010516060b0108011d041b0302061303021e01020606090a090b010f0303020106 81
    0x240c446090380c0a0112ba100d01003008202814965085150f4902c12400d64242c081a50b402c0d14a000d10010006002c1c1250003d15880b658040340d45401d0f0383c3ea2140c04d856001c1c44401455855242e404030303010200c00c410000c842e60107010001144220070800080400c6c4541c140c0c96031034015070040081e8540c2c0c0e15008000c21590011303180c0301040f154107030b4035070f00e07078644107828180d80c0d0000c6024507210720160060070201d040c0300c2c0d0340da04000343c440760760303800403583c0b94204012114003040004040c014820000d5002d0419070300d0484a000c1c11008542107001141000f40a01444001001b43c00c140121140600070005045451800040104a05070820000c43c0141c20000e581da2108608040d8016040b2410f1404e0381000a1108403c0c01103910103544504046880035a81c0c03041d403814000c4074421250014100c1c50705c01c1001410b0529503083c1d0142e001180000c2c01420f280c0940c0764081c02c5801c00040406640d070324100701c21400c1e0404a481e101072407040c400c040e024450b000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 791444406 1250 791443156 791443187
    0x50601020d08040204020c01110304050c1017060405150301020715060b07050d11030f12060109350109050706021e01270c3b0c0a14040305010507080403 67
    0xc09280392800070b4001c10016000078080d03130340041c048000860030b6002210b0354103486025035a07410907041c030a41c3c6188015880d442414500d80592880f4095444150925800d614004150340c0f220104001420300800740782c00e003003001a080510f9542071006102c3d40f4441c0700102028085809a1002c0750020340008a0500c820051071011800005855000c06001c6c504801810150314034a42540151041005248004108441d64038002c245261161800b070380c40032109590348401d15020010030011020b21074440c1c8506581850841500803002403020001c514452180d54542c81c181031a4054030040c1c01c0040c03028011488a0381d11303007a1112260003404940b607400340b05a48a01d50003815060300c80150360105c00c004210001d00c1c01490382412483d118105000060706280e00c0e1400000c1c031040304403202150508000200b802812009005410f1110b403000c261640d0704014004e414099051000100180090081c10b11800071951448100d08240ca00506a00c84141145 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 791445656 1250 791444406 791444413
    0x1120606050d0b1f0803030a0f0f052203050906130f060206043c05010e0f0304120807020622030b0c1602060a05040f0e07200a032307050105040605060102 68
    0x20b00414034a840c0140c100e90400481c441c520284240982c0c02803095104640502010080045010065000f0310100215150902410700c14054a4048a104542826002154400e0649a00611414423228610908006142103a002c00003100f0b41c201c160b184a1090200b002072080c031000c650389500410a500050400b801c007942d58075030340007840d142c0c540260006844030b40010100c8201e4044000365442880c2036540380d081450107054048924031851241c800500c484000c00000c0f2011606580c0c0f112204180d1940c2e005202d40c030240003640d000c61700744900700408100f41e110241c40c41c0303000c20007002c2524518080d0b45550009003080c0100c00180003000c61001088480e08072550304845146c0da8010450040e5040d00841c1c000704404101c3c8007001c103138020a0321440340900c200e921030079800355105258009009030941d0141080e006600220002401803141280c111240d2555801c0b1031818800c240030341d009004103a0701a0b45600a004c1403018600c121500003031700b88041c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 791446906 1250 791445656 791445679
    0x1020a030b061c0207080702040c0903022b1103011112010f0b1206040c03231509330907080f150a060c08070605010315050709150309050c090112060605 67
    0x1014083c106600030400e04540028003042005162001c4411156004100b040742e8000114000c1082d1841d000881c080c411480010b41a400310386c443d204101d24890303940001c10f14a59034101c1100301c401c0c185402d90348409040c01d00050200160481d8801d500042c0d240b51b01d0b0030011540b20010744c0c01446a80000c02030302c50071f5a084000c00d64000006c4d40d01103145448144d088005010b20200703810b0012003288515101ca03035442010380201c0d041e8520781c11896802c410407201c41c50583e12801030344008460582c440c0d92100d00142c42003241500c5000c105d0b00040031604204003210b901c4009502941042a0b600703444489036000a03251502c800620840f07070101d084c40c0d02c54000d0105200001c0c2c0c41e00c0c100700c045422a141c0030343c000b00601165a42e4502403089403200c4034202840c5d4140310001d15500d11504000085511011407a02190f415001c00c1e001841860f40a4a96004013054449175441e049420350091151014040c41503449040c40b030300711880303a0003642c482c4041101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 791448156 1250 791446906 791446927
    0x212040b070303020309070306150f1509031410020301060503220834050c150703080609060301020c011103100f0b12091e151501021f0e0f01020a030b06 67
    0x1d0700d110560604005941e074958031052881c0c215141d1004102500340001003c2c0c020001d075030f24080350742907203140d1b0301252118803070381c10140500984800541c17140e10070000b02c0e01c803040c0781e4501c1c0c2004058640c507600068410301682c1c400d030013440100701c5c00410701ca0312103c650803598440780d480e0061420b2600a83d41c110480c81840f2117040c4128181c00358001c018888042c01c03000c640d00c007141c112006014981591541a4450310a00c03902c00161a200c3c05508401180d0095602d40c0d2880241d9954000308160070388060003c980540d82800107445c1040244250700100440741c600c5916854800b0450350180704c0c9401c10110080d00c071201700400350f00709060340c5101d00010119003280d075a50018501c0c2c007003038121615022412840300108402c02064940944400521010a40e07680c02155884162114071203801a400a0b01c516640c81c00c0891030640e082d803440c400b140b40d81c02040301c646400607100031070300207960024000300c0507901485103580d14142074030000c4c1084a00c44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 791449406 1250 791448156 791448179
    0xc010825050a21051501110a0b040609330606140c030c1605041401180507050c0d090801200f090103060504110304050f061302040902031903050a021204 67
    0x11140e024010041402c0c25410b004441540e21202d408526003464072031401003d01802c0d056885210044000c030311100c055200d04035500c6072526000042c4030705519651800c10680000303005a400c6030742c548080b00080c0072000200c032948010050072440c0682c14420075600d2822440e034860040c909141001040d4001c0241030020360110415910750f406098a03034210300c520202c140c010f025088445407642c10030381c0c0d007800f44c50055400304030500d00c01001044000d020b0054444801c2549071802c0c481c42c0540000e41e00c04240e00e0500c0c10300545c2c102c102d1420f141200a800402d010501c10b0003210310034410140c07903001c0c0c2203030100184000c424850861243e21781d40c0b6640b180006804c08503034020341201000380009071040014030054a4081060b800c1a1401c9640340211100660110070010f44c0c036001d80c1c0a0405044083c0281e82000300400000c8004c0b41c0500600c01c00106070b000d03040c0020082402612050b07521242050000d04046038180503c000400901c000d122003480f08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 791450656 1250 791449406 791449471
    0x1406060d0f1505090615060711043918150f051c02040311010806060a03230a02120f01060903060e01140403021f020909160c0b07020c0108 61
    0xc0c50000840050b05051030b44001070040600094240010b1000a0b00c0c0020308511842101c1c5000a5054402c0f003000400c1c40307140f9016020b089034031181911460131741e00c20b00d12040b10320f041d180c1c240c4c1c1c080500182d54446400c020180703915080043e907169002100c2c5a1408091003401c0207250400044180036065a141042085032070380d845040c00b802582201c1000c0b08140c5e103030b203120210700f841e08080d51050000311100c00c0c1d1003020307010710350255070003600804004122906024003c00102c0003005ea083c01c11060b00301f159101c180e400516029680500c0c900c01e0b0242c0c2e10002c00d10303052002540545006040403484004000659102c0002c8003a2503110f000450581804564580544a01d41102c600320f002d800a010415800080c0700141c010800d8070710441d0100b02c079081080340985000c41e41c01450210003d601100401d11030060190a0b0408040480c0745880d130b0340c00c1b0f440894402c405a44910705403452581c010b032140d41d002d01240304001c95031000c00c2c081c401d42da000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 791451906 1250 791450656 791450663
    0xa03120609181e2013020705061909020d050d0e0d030206010e06040e010c08061f080c0c070308030406021810270b0d052a040308031e0906041406060d 66
    0x7540b20040c082001c41c1c01d85680a4101d00140e00c0d152408426444c00700c1c20b03650017882403041078002e08405000f0700a42d105250401e014140666402803d05500805400320aa540703541d0350404005035111021000041e020f000108040045420090402c640d540b40c003d100d00790040e000c80000b030740054110f040d610343c40c00c0c100381d585400010501815028824801307a5090010321030190307901c80340030791041808890f401d41100c06c2c2820308401c2c0c0352280e104400926000c00207880d87e0540001405154115012105143c0d603a4580d080309800c262821111a0f80014140d04101400e070500f030803c444c1150540908880a80c024040050640004001c0c01c141c0b080e45035010103028000b001004001c0c140741c7c0d03030503440500c0c1001340f10446002490001c000005400c80410f400c0780311400022400f090b04d007504680b80e50780c0c180c00003400030305002e8010860403000b00d2854025801504001d0061080c1d09061a0101290f080900703a805140d00400801c003056444481250070700f0380 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 791453156 1250 791451906 791451923
    0x307080f03160201090f03030507120305011505090a0b0a0207150201050610083303010e0601030f1502040807230919090602090315071103030c0301090c020f0a0312060918 75
    0x841c0b00503545100305d0381c00b1840c4000c541e40700105050300000208440c6205400c94004021030100c00d900f111400e026494400340c001e2103002c81c0c075000da8028181114002c15645610355104030030581c5903c03a1a556005030050001040305c0080507002080304501c80c0002e100c41c0ca2300101040b07181c451b15000004020420000ca44011080900070300c00e0b1001c0080302c440d0300d00c1301989082d18124420300c1e070b000350b10f40720307240d01464400b14405069039031200c00c44012402c941c0303c16103914101c000403178009508110000d680e01080005900600d00e080004c8105c164440030300344019400000580a1380e0301c0010490852409841c80c101c5200d19480050300440c103082040090040e05001a01407042290b8024a031100d8040144100081e130346001c01480300d20500c2e45c49010a541185e501041800103000c40c1126803c85094020b19104480e291005440d44601e4085441015004501182c10a107010080707030060001401c7c6840003801008030740d42c41c1e04e0132052050400780c035824 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 791454406 1250 791453156 791453197
    0x109110906130606051e031003320d120c0f050f0909040f05010b0102031c2007150b1915020717031804050402210c1302090307080f03 59
    0x9036031400c02e090b0407a800404111007070b1204000b03051a0322419080d8460030507440d0362044082c00030200c1c3c0c0300c0e0f076403030000e034031042e00d143c0e074200154214044081c00d0403600d100c108081300d07211207220803401484000744080390441a02404019101c88102c2d8a24100031480e4401ca030012441c81034605540313070040d562460031022907064051100b1280c0c0c030a80140612041c88410b62001d03c8041c05036000300001030f04c00c0e0059940380b040307820b0412214690108000c91131281d07404500d2030140041c0c40e100c6212005550b600c2c550246200b11382100011703d801e260103035288241d4015a000741c54480c4c0b0002e0003110001004440d03c10902600c1180f6500301a141c0f0904c170450007080c0d1400c40445202800c442c284c0c5a80180101781240e02e0b280348081c0d09881c050081600803500a440220100301ca035013003c01c50702164810402c54403031040e5102442d10355100c3c11006c00d040d1000181c89880d10000c06040000700c0d8469252a40300d124984040640402251850010080d0021411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 791455656 1250 791454406 791454409
    0x1031a1e06220501080f03040f0e130b0a0e0d0201060f030f1b06050403171206061b030c1b190e150402040605030103060f05040c060507080906190207080109110906 72
    0x790711081d0b200c4011290915002c00000759001103042c0c3d00450180d800e241407400b03d40c0d9407406181710341d80c014200140100b1100d20031004054006030f19100220000700141c0750780f50240320986038031010694400d2000702c0080c0a1010b01d640d048a44003e000b010720340006041d2031489800050681c20b07400310036004001005e940c4045103250302c14040e105c16a5010702802c50342181c40183c4440b81038010303600300000c4500c11205003e004e41813641c980d0701d40405114054001ca41954020130b99111010000b8800700040c01c4032500d0700740201000000203414510020381d2417140b42c00f401040c1094120420188101c3d02030750306081d0040001d80d100d25150145511020741c854006100060120b6005d03407010065041c0e900800c024089040b581c10304000b119005c43d0054103280c2e4520341400014031400c01040b50034003031410316041100c0403001421036884250301540810144062817410340d0180300030b400502c500b00081100c0945500c0b80c0c400480c9025210384100c2c42440041c265 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 791456906 1250 791455656 791455669
    0x1503061012050403090312020106052103120124030e0303070e15040e0a05013305040f0b04080c010203130905040c0801020703030e0c0a05031c110d0801031a1e06 71
    0x20801400701031100b41070504000e452071029020546006a10241428201740140508421500302821181c8920b07164040b002c5000c480300082c2c500c0b804200004030350010302003212400303401c428bca1a8417812102c00c01507042180400040281800d04010614404000c0142e9900540740c0c100054800c1e1205c0001e0007040740a94040409900030801040000e1411102032140510502c1004035980b581c6c2900d02d030b00f198131850000321345440b451b04a08020f43c01c02918240c0e0f0b03420300c141415140c4215003448401da0700a11501c0e900400c04000d03280c0100b18000c0d0003003003030020350720f05400e184984c841180b82e4001c145c3c8045d103c4001c10108051080f5036002000e03010021902e6100d581350060291012114021480c03040c407519405074075188070039404580005000340138181d0741c0c00c2d0034400300b95021541400d00034015090391407020284420781d9030503010b648040c229811882c2440749150111402d5007181d44410030840e00c120803544401f06c40318018140400e076950400028103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 791458156 1250 791456906 791456927
    0x2060f0304051203070e0310060b07030c0c0503070902091005040605030f04030507060e060601030605060901090e370c1713020f1309030e030a050c0d0c031b031115030610 75
    0x2843c40000304001c142076215150340000c034001c406407000001c03119003200c1550844d01480c184650108032080006e806040c542441601c81d07155100651345d2240043c2c20600300d5401031408640000340c0b00d03801c1c03030300d0203004154150f02d080c02401e082c24038100400320b0000400f5a260032540d50041014140200c0941d040300780e101c02d060200e1001ca80e42a42c4482c401d56095010900b4048041050302c0c0603400d4034003818041c0c1d14400201c2c6051002c98498030007074841002c040300502d140041d0781c804210581c05c860340300040c0e468030703001600340d400b140c1410a03c0c0341040410a00c0302d0210b000c01c003407641c01140704041c6a0350305d8103500001d05d40d001814101c603880b10103481e00801810850704456940d0f8000c0d2180110180a481456103d00702140d00920503082106283d8191800c4051076580034003811509420503202d41da8140d400750b1100400d44006031001d4108100008a608d0780400ca20036030b0f0188042c00c0c00d1403042614007001d042548260329881080c1005031040d0710048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 791459406 1250 791458156 791458183
    0x50a29032a120a0902040f050c031501090b0c030a081303020304060e19150e0f0d03031e0501090518031222060906050f130c0b360a050d02060f030405 66
    0x1c2d0780b0300708000d03114010150040e08a000b107080c140e0075002050b40c0e10500b4411f0409072400d41c503613650000800301c6000200700781030510034108004513258920201500c0043c1940d030003996544d1298501521115008251135a071100c4c15480c08000390b404410790b000c03a1003a061a01c0369071043c9001030418001c88000610030401002c0001c0c1d85141c00c0150906070245448070131159a0800c14000071543c81004240c01044000420001034030960040245104450007402242e00700850181039880a03401000c03010307140c5c02442016a4801100140c000d81c1c100114542240703100c0c40c030a0510018028410b171103640b4a0124018400c41d0408000366014400b008034081a01c3c0075001080e050b194412842c082e640001d448072031014055015640103a500d121461030700a43c41c070303107a0045e16000207420b030710400c0b5200201444280241100090002401700315944240100d07040c041d40041d11846110080c0c0c000f50319000201c9084403099072155a50b5039850070414a0000341c01c200c45d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 791460656 1250 791459406 791459437
    0x90103021e0a0f08070207140d11030307080421150f02090604090f0b0a120b1b0d0e10020f0904020714030301180513020a0e040606050a29032a 63
    0x80b0103281c0c814000f1143c000d2a03166860b05464600c41203903030704000d020b401305444194031200c5c42494030b2051880000d02c1100059855281040400d0658108043c1119055008501403022803900e4909407040009004c0000000c0389a446080107201d050250300e00d81551802e11a0b0486041d40456000da480903003260360302d540d503205101c000e0888075000c000c00c514140c5840314614054a02c8412607410217009204920543c84540450001034001900d51803000219140c0240034009440320540c0d00c100007400c001c00700301040c20074411110300500284100710500408107040b05843c0240c5045d10010f0301c48196140955001115101c2525644008000002c0508040c8490180780d41400d1060180303032510044106130900c1c80c48003d51100c3d2995081c014081008807141c1c0c058003890000c5069641c51000c20f800032425080140300c20b0b0b0301e000d00d14100d0585041c0c00003042144201e00d180d89011008140704031200d603003401c00400205100000700c0d00d4501540d0030b10070100d120 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 791461906 1250 791460656 791460667
    0x70f14070f030516291215130506013504080c0d0207052d12031b0606031203090a0b09030405010909050411092208071412090103021e 59
    0x40303460355250b807104403010b1081551500007108810000000c07545000c01c584e0102510042c0c4644403880285c0042081c4018414030355940002c2c40d0b05409608244070752045143c90314180704203000048245001715040c04140070640e6800445060300c0c081c0800090398901d0340a10359001c46585c0c02c00b03031420000703071014401800b044600901d00100104211001c2e050064170507611004244101503200f0781025000030260f03a2000ca1003601540b4501940d403e038510340001c0c0304401769520420a40c0e00101d03148003030300b0b00b603444000801c000e2401071082d403030001c0009030390301c2c1903d441c045d002074040049040d225007000703001680c81c0c1c800e00181c1c81d403508001c5030703980e600b180c4165400200381c0c0e200041c1031b00892203001d0286404c00d140340c681d68401e001f0300103a50000f4010102e4281d0b10100d40c81640321411003903800a1054400a59404460418140c07420300b0703848025481d0840c12012004051220031581342d0704080c00d01503100c0080800350b144c2100303c500c3c12428020b0002c1c0e07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 791463156 1250 791461906 791461919
    0x3040801090c06020705030f0703240c080a05010b0702150706090f060506130e1509030d0905011d030c031605031201080309010207090b0a260114240105070f1407 71
    0x2a0b0000740c5806608448105690303c0c20142e42e1908a50003c00d20340000b0310030710100c0c00c641002c90314213042e02c000d5261580d52080030704c12a00e010103218000b880110901502003282e000f61070043c404580c15038102041074000130340c20010618210b0001c01d000484c1401c0106582000004581000e9951400c0d01a4140180074100844645100755155003000451403020b01c20313000811220340040c20110003a4500c110807000241c0601507a22041c040e101d4003c44500032451014802d00000c1a00340c0c061403c0ca54240b500580c0b41c0d45174105204510b1a060008103980c00d651482d80030b9030310303403000303040880c01d512810346406212401000081440e51002004002504080c5e084031034440d03455000c00704589000c102c0e540d004003012030411640c51101c1400c0c9903014210760480c05a03642460007030845008085505024a0312000c106044032000303415140c0c0c0c580500300d41a9034541c030300001c2c900d125103003000745900200303808a001d01103015185a140c1e645802150f0406840e0034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 791464406 1250 791463156 791463173
    0xc070515030a0e0a080a030902011707020d0306080312040312060305100204051e0a05010c0c0e070e0a08010e07030f0f1a0a0606020f06040b0403110d0c14060403200304080109 77
    0xd810300a030606040c0c000b292643c1c001041c1318000d401000c00b5041c4172020300110050710b40030302d050b81000044500341d0700c0f02c101049814002c21040d0010010725418a5010b0b0503140c1580c41145035400a01c0b8003c035010701e0150141d802070703040c90907206146c0c001c0d21100040004d034001811030b100d8640d008440c0082980240b081d560b003101e200000301d0340003405145a2a1102600d0b0708100304400801030740d409001540035481c0315407204024107031a0803055410322000c42c2c1c9031001403040707a010300c024200841ca40b40a001802c00034000c1403220002035030b1342e0680c2d100040880c47d103250000c05022410860904603548000461030005002140340308089013980c11004280c0b520500050140c0009507080340103110710040d0465550f90f80301c03071480000050040d001d200f080d8400540001b0103001205a07101c0c0ca40324040180014141509441100241440f41f03901003404e1001298100c8c00d01e03298050144141102c081b003550f151030442c025070b80321b00c40c59801c009080e400c001444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 791465656 1250 791464406 791464411
    0x9050601060801091a0405070c0203030c06220c0501050703051b0705041d0a08090409020a0305060f18061501030b0d0c0321050f0337110a0f050c07051503 68
    0x6039a803007550791320b0348008021100c10a00d0325441c41149031001e507650600340c1105030701c480d040c10011244002900480e08503405262055102d030040000c000445e84080b020740640300251040e41003840c0b0360f0380c440841c800300340280c60500c0800b0620708100341c421380407120856034200260074200f003065000da58841c01402203620650504420100301c1e54441d00c109003095120b40106480c001c2610341c44010350102d82c0807504903889a21007800350b101d03004d00000840c0700c2e0b8000c0c510381c90605410815800c1c06040c0d2401c05100700388040b12000c0000d8026080305c0406081700003041d0790310058000b841d0070301d0b100780c000003512440350a1213070650b100021207004802c8100d244455081c403028203158040f178940482c17001c1c0f102400981148020b1940000006041103202c0c845d040958064030400d0180600c2ca11200b4074200343d0019406405161223004c00d00310308041900c1400b800625030500303200c042100104904a8800e0100aa18000d0101070300344a07417030401e4030030901264000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 791466906 1250 791465656 791465669
    0x1e0423150c030703030b2103071a01030c0302010e18010b0a020c0a1505031305010609090311010507122d0914030304081b0109060e0102040f0b0403020303180105070609050601 77
    0x3880c10300c035030305140c000444805080c050081c500e09141940c0580003810600302c129000a040300d81034003840540c2e0070750b614202e000c0f0010754644505180c040d104c4026940f24541c0c1104400040000a21845460064990900300150048c40b4000812a480001600140d260351884000111410b40704020088400240e003600c14108003002404810007461284908100c10496a01201031103078000c2e41e0458444a07054840c00c0c002d44505003982e0709500190340b407643d0740c1000d01c2050b410001200400d030780c46000344a1440c11040141c4869200c91020342c5ca5511007400c11000c0f2405441c11030341ca00c0ca10f004507841c90303046040301c0083c00246002c84462030414005040200c000007660b12403607025600302d10b012061000b004c60504c0c0b00c18141229134840b020744000034424020300c0d90500070f12000603101d61401034514083c4846502130201c40d0820041800581c07408021905c1c00c405000b0095036030084003004a600317110307401c0302810b00c0b85095121030410801180d40350481d0340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 791468156 1250 791466906 791466919
    0xc0c0a120e0a08060c13090e0312060f0a030201030209030106090e100e060903070f080f0d0b031009020306040b04031b03030603120509031e0c062b0b061e0423 70
    0x15040900401c08450b0051207002d901140014039007052810091100000341c0c1e0341071351b50907911a1401e06440961400e07504540000c42d03031440c1a06d80d141540d03880719080710801410f09000300407400d4102c40e4000a810144c0025007100e454500f50003c60040512010030000c00313140d411703020b40306d814541c1c2c5015098149654100312000001d00140128000800b40d4900601543c6051000010820031180c20100f448481542e8040720064511121030700f2010503c820f0310f80405041c4011100c2b184121440d041000c00903071000a00b00d5400350780403209c0d0f800c030b86460505407580c5004c43c0318201082c1c0340c8100d1504155068100300c046901c0f6062004943c2160b000a075004d0084402d5260954424090000e8510f0030001b1240d1101b2a00107aa56003180040403440d00c7c0e011046010041501c0c0101800044903446100000355a00c1020030800d032900000030361521421094580c4040c0340380241e02d0091142089400410328814a58095508038240803100d81c0c40d600f14a11441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 791469406 1250 791468156 791468177
    0x1b0305330f031507050a02010f0509010507322d12010608040b040209040614090705030609010b280503010c1706030a080f0a05040906030309080d1809050c0c0a12 71
    0x1000101000f407a190309000060642e1007010440c0d280d04048a01d80456499520048402d04940304660250400c4000811145400d41000d842180b003100800d07014100a001c203120340d6005600103d410011208040e91034482e0b40c142d41802035004903a15404144209140544403501c0042c05212803210070340d412681d0700c1c3d40c00d0b100d280040b18040d00610401000800600d03007a40629070140c882c14000440305000c03510038100070f04c02c80b00d2001035402960140440c2c03508206481c1c1c003460000007802204c40780f00c0450603207031045142d8032403080401003103400000343d90707000d401800020340208140111603200502030fa9942000070f5940e007075100419401e08001c26070660442c0c0103024585408000e4440051580c42011548200302c410b100202c1c0803441c034001c2d4002140660f40c1c00b0300050812404905004080c40008188032100c07110982c502d0302074071340004442295800040c0b0f50b48441400030079125619401050b8040c1c50800c900b0029543e00500c820000c175514280e111 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 791470656 1250 791469406 791469409
    0x905100b0307020703081b16090f02040b040909021c0f0c0602030a08180109050f01151212122a080a0903170403020a0c0b0414041b0305330f 62
    0x501c0181c6442006800c40042400481c821500608440f9100810780e240700265106c080c0c1010313010740c460000280c03c00c10070010500300d4001c1640c200e4000d00d04600e481d161451220003441070748030760158203445181500035542c41d10000c40242a100b04113590b00e402c80c4c503200341e0726070480c2012030b4000b001080c04520588000180c68036440c50341c07203035099601c0303589550340c0d00c210f21084240a07640750111440010b109200c801d4241c13032044001300340301c514a0041d0340c1d00b5a45801039824a25009081c0010071131080d605208800c29081441400c00b04070402005000d2140341d50018204034840c12000c0c1010085440b0003410f1641e402e001901c0b040403140550f01c00d41005000554503c03400d00500c030810000c107030410700c070340115800682a51703940403404001c1d034400811038801050400000e02d4004d0320300354141085404000100e00301d03040d407503070920040109042690302c00000e050001d4032540408960132415042a804003008080410b0481200d07045025140075007050405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 791471906 1250 791470656 791470679
    0x516230d12180e01030302340618140603040605150a0b0d1103060d02120309041103041e030804031d03030d060504140f01060f02100c091716060507080403020307090510 74
    0x1a01d6151f409018120240028022901c0304907805030340900180c10b915001c001881e41d510000c100302c2c9ca800c101e80010503001116000c00303502c1403c41036640442d10469130b0760712040300e034802da2002c00007070b45469203180c1f10020120051000c0c1c2044c01d004000c0341c6407070b201010381001c204074031003840aa031408034107100c2c03404292035903070b04650200c4d100c6005241180d006411701c0c00500860781480f0411000030191100401c0c4400c1070200007052000780611803012044002c80c0c510b100942003c207590040034050018805020040120f1000c5082505500c5940900c072004040340d403a1fa021030243ca0007040c81e8803500e44a00d24003540f80300246a4454154030903a00c032804615a41e07c3c1c20320503255044166000400c500a81a06080f401402e115200406165503038036400c40e4103000e0340b07009103042481f00c4400340c0d00c84603c2410080c03850b500041a40c100d13103040e035203030304070b500d0b2408560082d03400003941802003540120b0b6052641d841544a20005142c0100c070903501c0043c03865 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 791473156 1250 791471906 791471909
    0xd0c081909050310060803180d080a11060a29120604060e0714150a02070906030c0311010e030604110109090908030a05160c1b0801180516230d12180e01 67
    0xd054200f403025903803020103c00c40400072303103001d01140d09a4215688400180d405080101c012884402a940414900300425684130416410421050100d50404e489d1a01100302010f120000400d561415443d26001c1000d8000950122031f980c0c2070926121002c0c000a0300413207035500c60000c000070f213001e0244441c440c0010107002c9402906603221245241d5004080500c190311030b41c9400605c02c01540300c1c020055006072001409241545450000c015410a0040c1040b91411785031f1440c0e900800c0260b0041c0c0d000c9165048c0c64480d000688069090ba0302c10381c9000c2c0740009800c1840384000066129142d0703a981080075540c0c51402031001402801018000303980302600200250485101a41b05c4510305044107030b00b50703142e00a41c04e455a01d000c280302d0320205a498400c2020801c8111040c0c0030701480301d10b80700d00f007011085c3c00c08010f41e503414040d005c2da4505081030f26041800f042483c3c224201c4062400c000f0710103460707264054030201030602c941301300080311110040d0381070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 791474406 1250 791473156 791473169
    0x1051303020609072405040e01031202060606030f0a0c1e030b180c04170c040207030c0308071b020f1305090706090801111902010b060409060e0c0c0d0c08190905031006 74
    0x80140e141540916007017034640a010034444108004140e4191446045001f544604440052442e644070024203011018016501681e410300c180428000885000c551100c90200001b80034500b41304100c481812011005201d10540010b621800e685038024500038a02580c98401200c43c001c07a0081c1b0100031260300c14503000c01e1005000c50081d001c00c81101c0c6d0342400071540c640c100d90300050226409410102d0100c3c01d03a0f0605e404041e001514250303c00c109003401040c0f06c041301400c240240c134400c0000c1c07242d412980545180ea5a994100ca000c00d8008000c02640c6000c801c155581c00c1c1724000c0390003190303d41d03c0006010405001e004000c8d82d500c66824200f00c00b505664808110b00c6194002359500c0f411300284a880f15005000100040c0314086403e9250401c8280a030201a040c0541d114040101d0092248009402c4041c10301d1450140300080940c02c004543e80950080403540c0310308240c494202c035501421034000d580c030443c25a07559543e0f904042048415a100c2e40c0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 791475656 1250 791474406 791474429
    0x1512120708030a0605061b0c0307180f020409060e06010912120807050d0e06060f030a0b06150d0c020106030311010b09150a03170d06080304120b060d050105130302060907 75
    0xc0000c6004020310303081903041c03402003060750300e0700005502c03500040c1c81c041c0340040018502003100c104100c03440009100b80e018100c01030030102e52494690080e103a16000c29160070b0320101046082e4110380091a081d9001c215032070310341104401e4203400b80c0d8aa4002001c041001c42c1d01c0c0005201c940c96142d11800c0b20705003040d00c0c1e00070b6034400c030002c0c10701e03091101c240028000e14046005051200000c400a0444ea2600c00300b00404201a40d01d01406540a0700b916400900740703428164106408640342c1c00710000d01c00c0081c0c0d0510449080603a202d00307040c04404601d80540100042d41e110351245604090710060b0b4500f01ca6522499589c88000038000c10400d101201c0c00d14001500502104216600d9480c0e00c50030714002e00711540000f40003c2c16003516086403180d07101810b08540603501d414640210241d0183c00c6d85805848a44803002140f02c1d80c1d02c1d440003605550303100c0001d0215213400141403200d0500b520059016020b00c2e000142c1c92032022412205841b0481c004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 791476906 1250 791475656 791475667
    0x2030c100503040f0804080f100518071e0312032c100507030f0606110c01080f010b090102010b1002010906200d0207060b1f090b04270f05151212 64
    0x84000080500e282917030f5000c01004003184810043c015080100302d100000c11014481c2050102124001800344e20004204503d491a810010890508842c0c03d462681c244410200c1e030307409003800c40c2c0c1c0001d0802d1803032501030180c0c540540000302d20b90640d40c2081002d2075203074801961016140c7ea40030141c0c225010948070320080740d00c85500700610b407078005150300c540348610702101c4450b044140480c401c40101c0c6250300b0108002d5440c0502071800500f9400c00e420064941c040c180030b4800000d00102d06031410364400d42c005101d5040003016403480c002100000707402022011800d941c1c4a08001d2001c6840c401c020b142da40d10814210014030b8003044030394003170094208140803034889440f8500622039a035181c0000e02c6140d0b03081112032411500780800340c00510180e114600c0e44038240820802c040817600c400d2030049a204070411260740d4808100020284045541c1805261a0030310214007448070350100018810b5074039130088028541c140ba51800700305001e5510042c200003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 791478156 1250 791476906 791476913
    0x5030102043623090d0206012913050f030a0c051509041b110604020a0b0304081902030301091116081b0f100506040c0806011119060902030c10050304 66
    0x8120030034026840c2e811160703110090030260f40c207030000da400d52000c00303061240b070064180702a50030080c01401400c58800048020792110014030900211a0f000e9011b00c151003040000d042d81c0c0c10500152aa403048190110380310101c940c01920300404000500400c030707081c0000c4004000b900840740e504031625000c10131840ca641035603681da94200910440350182c980b07000d811401c015900220030100421a001400f14039002d640450581c041c0703041c800541c481e40250429604541d206079620341e22810540460b108a44072016042c0c40d00713106141490b030100245050350540d41040c0610940b004042c0c0a50040107000784040700c02004080003d00b810005140800c46c019600500b4800140c03280d0901048044044c00350f017104004150255240c07081130783c4000204c0341080740f2101c0042c02003042e040280300a051102e580c00c0e80808d040d0070004c0e91030000000e002409411041d00c0d00304090507450108900a100d2000309030444e01c4e1070a02c101c40e290007582e600d4290b82d556103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 791479406 1250 791478156 791478209
    0x50307080d142707080a08090108060607170a140d0c020c030114060d031e0203030f160f0c030306051203042c070c020105130920091011010e0a050d08010503010204 72
    0x1402d40f880f80c40360303001c0041c5410042c0030501c1a90302601d5041e489401c02c40000d400b950008044a20079201044000006041c03d010504480080101e05441e03c0c60200140d40f00c5841c0c104101400101003411070144200d030b088004180b5150f8261047d0b0fa1803002803500b40c4564290304d0070b825201c1c800107421401e22042003410790f4002d140503a0400b20a1801948003042102c442c8016000003080281c80c0d8002010507822519040070158800f003896001414143c9008601007004109281c4200b418800d0304140c0103402e0080c0314501000000c0720a80d50390f40305116125503c4418440315807500c182c011624141c203500150a1859941c0180c100c44042d51880224103004090181b202c4d094000a6190058041c440700018028980101e5001080011028400d1070b2820407003072003161684400003075011114107000744020280712130a405043c41202201480c80b4002c400024081300084a42ea03103501038440540390790b22082410b0031f03803180b80214602d005030305d080d4041500220 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 791480656 1250 791479406 791479471
    0xf04050705041a0910030606061e1403040f020f0301110d1a0d020607080f0d0626101d01111c050112020607080d060303020304210215090607050307080d14 68
    0x245c0d4852003a4032940c8000484030345800080000343c0d4910000501031704141150075032112418020203a12030114510158880244002e1413010a0241c400464a40c003080240e8400000c000348880c032124000e0541c150091462040c01d541040c00da609141c0352000c1c50014940d02034030900c41c00b49130f60240700702d40c1c5c001c5034125070303100c0100003008841300301d00c1c0641030800c0310710b20226445161051520078030b22090038030000b11400400f18820600b000074480c8021003c0000480e07040b024000185100d613000c0c01c220219424a182e0720020220300e80100b1001c1090150265020702074481401219001d010f001d22103500319440401520f0a040904142e501c81e01c9035615007060340905005031034072640104d0250f4808282070020003c080034079508601c41144112401109800103107584201150115040341e00181610302e0340c4803a003c071070100790044100c07580c9025900c0c00c1c01030fa611800800c0703002c1c1d00c2c0c141d884003220b15406c603040c000c1c8801c15440441c00c412910000103440030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 791481906 1250 791480656 791480671
    0x90804030f14010e010c0806030616030b030a05100603030320070b040f1b050a1a03190b1503010302040b010c11130b100801030b070503070c030509040b090f04050705041a09 76
    0x4020400442d8090140104c0704040c0d000105080c048110302524020000c1c011900c04d4000008019840f442402240310400c40b0340380c08103070005500082824020b0741c10b000360080c011540440d41e114090b401020840f8402e0750304219003d03950508140c881908600104285000c00908010072014607119411600a01d03200c444105280e46a88455094800fa4050007221500070841468481070310801400039a2510700400904610040584030042036002040c20f1800172030044007055001885012002e07201c030b2141243d0a80c020916042444100d1141381801c540e110603520231189040c5403a03121000c0c0b00c00050010030044806081c1410481c803607170340c1d403103d00303640d403807102c24190700000e5120008507505500b400024880c000b0300900900034200188a041c0c0e07400b41d00c034a0703255014034020b62103500700400100070700300c0421a650b00c04801405e1003540001500f5050040344202c0c01c86454030340d100240801e807010201c0001c0090510800c8180c14200b03078150f11703880000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 791483156 1250 791481906 791481923
    0x7030b042405060103051501020c2202030f16030207111e040501090c02010f05060a1502030c030f12070c022b02040f05040c1a04091a0411030910090804030f 69
    0x54988032000d0086481800490050b12002404010358243c41069000010fa80008060810070030010790b54000c000c4000f401220b5200e10360b54030a55001c4110782d522000d0000395502c3c2400303200d510704c0180c02d440b691105504210040c01c042e000e40308480303902d036104880785034225003c0100440443e09140312241c01c82981100c200e10780c2e551240c11301030814482c001850740f0a0040003800c40f8050044203460506e042e050054503600c246d598130440300042c0e4004040164004201d085004007210748016110114442540188881c06021116826840c001e0180d032921000c6452080050000c6c1d00042000f4071005100e15191400304030080b0b0b5184036040340d1480d40030504075105070000c0c0a096948106110400c65203220503001130440388118801301d10700489103041d41c8220b110b0740101030b9449892003601c902c900c40c41d10225030b00400070002c1c4810004001c0c4198801c03907c6032641c0c0101040c00c1811415841081550798100521600749811659594123113280850166031311003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 791484406 1250 791483156 791483183
    0xf060f130c0803030709050604050d14032215020d0801060e01210218010f0e010c0609140706030f020a1403100f08010606080a05060d0b061207030c050a0b040807030b04 74
    0xc031540718800042c00c4a000030b60742c0b480c004100426139138441c0c10aa109841c1004204999035815550241c444d8206244814081d0b616655614520800100a21501c0702514250400d10710340802d01c115200030b081040300c81000307007040303071150340c2098900c02050812005100c86417085045205541c0181003220400e001c6124207241c0000032680b01c82090f4000805440f12200f010034100140e1003824100341401e0740c02c0c00607180020518030981000082e4501c2814410540c012001c06a000f003008521802007a00003615184c482c003460340443c0c24201e050034050712620890300385c084550b03201c0c0b4101c5001c0605c41100da00c054001d82e44620721400100c1d000c90360031a04002054084000180240381c10340c09040c0384070040506c0724152400040081a481306400401802d42c00705104105035160700c0081d0442003540d16809061003000d02c048200024440b000003036803070454803c460146c0c0d50400030414400c40c040d69607181c0040c0c6003080000c04401c40c0d42e4105200d06225a4040b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 791485656 1250 791484406 791484413
    0x8060d1e0623010f0801020a020a06050901060b03040501090b100506040920030117010c020105060607110a0b03180106050603270102070812010315060308040501140903010912020d020f060f13 84
    0x7400b44800315814034415401040344003109845240245040c0703000b942000d854900283d140d17000c1c9032000e42010344032000180003040a44c0584040d04051120a03240d00341810806d00901d13141c2002c54044040c000801c2048071078048031000c66800510052a00d41880b0f48400940401203030001e5120b0200d003801c1c3c0b40c0500703502550207004c40414901c2080041e0000d40c1c25a03c420801c0300c1564034003020300034261210000c03038205a400440c040c01c0e918102001c627003007920716800000c5490021007400702200340c080c500151011440000e1042c9a01c4004000301c030300c000e8540c0d0807a140d002c4803660701d2070038400d240900e42075a81e00041c18160305868130721a0742c0c0003605403c1c125040300018010054100f50b13408803003103403a404208031425552605964401c40c000d05041c0440c080384441c1048690084490145009e002804041c0180c40d250000d4011440f030b62025004082c00311903840d1000410b640c54403040340c0240a127440e400040c0400b071101600344018007240b1108000070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 791486906 1250 791485656 791485691
    0x12161a070503091c0806010e0d05121309020414010e120303011203080108161a0d0906090c0e0f010e0c1b070e0a02070305070204020d02040503060c07020108060d1e06 73
    0x995040c0d2952a56854018001070801e604d04000d0701a80e0480c002c1e51000b80d40c808607059008000b0300f0f20214140c60a80040d08010341100002c25503c03c03030b100000e0740c11050000d031003070b000428081040541c9500c4001309074062405001a003da11a41040d00d81d0710401254425100c0504030007442c10039515a541940d0090304030001e03007a0010400d50806034004074050040c184540034000c0c00150610100d03160042d48035055143c2600c1c0301041084403120101c0300c0030041c02c80f0030414507219103054400b805a1081c1600c0f07840100500041c2c41100226040c0308440325080c50b0216802c0001c0040c500320080e00600c0c6020080c803d028841039507860b4081900d81040017407010320301c2c01c1000c14840900400d044280c0d80144040c4001a800074240d43c1c40c00d50449001da01c039230349010004024020ba46c0450b0781840307408180100001a40020300c0e006000f0703a80c00c07400ba681c9034213010b480c210781d0000404071300200003020301c1d03840d83c2c2c01a0b0250314490140403840904505051f0340d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 791488156 1250 791486906 791486911
    0x1b0c08030301060804020a05090112121b110405150a031b15050c0705121216020a0608150a050918010f1a131119020709050114011112161a 61
    0x10404d900240801d42c90100b01001c01880c1c1110300c1c554540c18016000003401e1040c400a000d4440c03000301c0400107000390040016100e45144c03800019505040ca803040c0161540a180164070300f1010604020344207280d08155200039040c1c2010918540e03403c001c0c41d8021080c0d0035581c656040116000c4098076010740900640e0b80d03042e0712103400756401402e00d1015800b5620540c203201c01000303005004144a40e0b00c0c0c0103902180e44400089000046059900a00170f51040302d498010500a42100b0034501400500300c1700c043c1c01048000f03005540031603019107540914440c0000710910489400b00f600031004ea40085a100140f007025026a904810502c0b012007401e04010700300c3c10300d100000102d00d2403402c2400040000f0b4400740c0a40300e214015406001c0f10441029003600030000c2500820381c0c0101000150b94505034030780c14001840c0b40b140002d4500420040b441030028142c01c1e0700702000402da24000c005904111400b481c0d410803620203400e8a04180c1c0088c40300c1070f207031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 791489406 1250 791488156 791488169
    0x602070f0804150905031b030a02030706110601080a0203032b1409010c02060c0a1107080601090f0b1207090b012c01020105131e02010908100c0f09061b0c08030301 72
    0xe860302d0a080d00c0c3c150340401410304030200208803c2c01c100c03580c1d0006603242001410b107041c1d00002c5440001c241000c4d40703030102a405200f881c10001d0542d0b400f0035245107407400c0d02c0548240b80d8844500e10348500b80070340080d42c9640140002003400c80d29100e40e10a5117200680280141031040c045c0f8142e5140b07400c0100100c4454042181041003070140c2d440d84201480609001d10707044480300e0f00c600034031f0a81c0c01000000c584c810880c00701001480043c2032410b00704e411941e50380050748060150082004030450400e00104800d00307290303004852f008400c1c80641030b040d05000c0d00a001300001a171060400c0710014541915051004000600310b11500351402d0b61590603001a003034980140000f4512021810400c01040202040e528400c0c0700700583e00c010004d034001201c01c00441d80003095180610100130055685642c044580034106440b510715030f0480702c2d400e403100c0840f071103004c3c00b04003c0124030302e25511421086102c50b01c502a02000329454001c082e1441e002600700a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 791490656 1250 791489406 791489423
    0xd020f04091b1101090206030c03090a0f0803041b03030203031501231201060509060301030f05010f05010801150e0709050f04020708131a0316030c0e090c09010809010209010c020105070602070f 85
    0x18a01c02c1d5101c0344911404003000003e0101031215400701d0140e1200030b000c544100000f202289001d80148041c2a1060300a42c202484400a04182c01e0a910950341250180c2c2c0503002e580700b00c0c1d269070204e01141d4154001e1030440d540c510850300c1c0c800710483e65504000440800740840d441050610290300a034581e10fa0b212940c045001c11401c1061700103409020083c040c800b481e94403041102c1c1900c0e13014440c4032503101603250042c054815a02603041540c1080000b1902d1a015403001c03424200360f203030707c51429541d44a1002e44210548416000518036841445141000c03001c8013075122015000500e005135988419910380c0200341c480050303201820041245000001e200380003080740e100213919500b840c3c0c0d484240001100404c0c42410340703600c00480300901640d845a1107440152805007285480310300100658008d00c3c41c50b001caa100d17404910000c5052090314101c010607101c0d40703c241c5460700103503050b4201800855995030200100000150a0045890f283e845642c22 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 791491906 1250 791490656 791490701
    0xe060606071112062e050f01051e1801032d0e030d020a021501240e0f10090602012703050f07061e110306010c021e12060412140d020f0409 61
    0x2c0da144101d405e40000484066100a004903a03403200154002c0000b401c2240c2d5400780c1120022107043d10341452080e8000200d00e84241003800501c01080e620242da00b0000d10b00109010090580c0058130812100c0b0240740941d0480541c2d44102e15081080044905080c0d04041450503640301d56a1350300160800c032060507800324802c103128054050b4000643c0d000a0500381c01080144244551080040c003100c269101c0c2c640c00341c842e11141b00034107100c0060703404120180c0182d074148140e10056282030500481090b080714482100001080040d40c0ca00254400300d4203600310460703010710380004000c0400040e08912910b2844a4044105c1c0c0701c904001c80c000048802001204591701c20410400c2140e0380d101800c40761a590480d40050825010300aa070f414510f040402a00086028a0003c940000003141c521440c0f084410755550066408100ca08401350411090758400512148c0c4201d1402c2d00a8021200fa18483c02c1c213066480484105882c0c8001070314802000c065503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 791493156 1250 791491906 791491951
    0x60c150c0703020c100f0810210b01090e030f0c0c1003050114060703051e0904020d1d03070f12030906050103141b0d140712030809010e06060607111206 67
    0x40841e01c0d26049690202000170490058a20450040001e00f0401e00d800061070310f0290718031090250000c80c5a800b102c2d80f00149000351080d001c00d059a04414030300001440c0110360144494204180d0301450801c008a0981c0321160000140c408040c015501d0400040c1c44032101080d0036000e070340d004110342d49440b200c403509166044d00301d80102400c001c00000f03c1d0b0002d0483d0381900c0c03100c0c101c150820700096001c0e050b001d102442644140001488a00754969070030135840c0448401c083e0650624000da4135640344079080d4014051f550aa540c1800715514445070a40c540d0b060601103098411559550100c0320309800480381d00100c040c40d514040c1042281c0b5008403481660741041709038101c0021a11040f60741c006003040c41c0d514070700d20b8201090160310014054240542078195403480c005e000004c0468007a0002e6203040004e4040460004040c0d0003603002030f12241c940010f46d110121404441e041e2071303401c14050450101e00f61030402c1400d109904e454030205c1810480c0b50f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 791494406 1250 791493156 791493163
    0xa0618110d1a06010c171b01061d07030b0405071d010e0102060105190e09030a020f07030c052b03020610050111033001140f030a11060c150c070302 65
    0x2180c060255021810040000e1044242c0001da40030034030030020307155548030040341c0b0003603681d40082c0103070290390006101200410280995904084803110a0024000600d0072140d143c030820200032080c04000d0b810103c10302401c0d4004170103140101d042c840c54000f1030203039002580e0200020380b0035145990034a55071044803003100001d01c1c0040004400d07100007580c1da0b1b01805001e00c02c0308003613030440010348040c60047c003c01462140c66403e250110303210340c030781d00202c0c90b0740d0250091592400742140003280700c00580758000403151060b030030310082c000d01100304c1c46058042c014410344080841544003840444070b00c80e81c000d01140c80c00d00e4005c510b20145500050502078000b0444030710a40110541e04400c0c0c01018202e20101e158a0b8404171400c0005046120315030f400010a981003074400180441409558854000000310140f41d40d5480c0c0b030a01518107511400d0724411403400c00014180d40e09820200c43e401031a1520714000381009450884c0e0b407007000900c0b6000c00d034050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 791495656 1250 791494406 791494433
    0x30c070e010f060c020d061d01060e06031501230406080a1203110c070b07081608091518220f0608010c05030c0d053106110405010504030308090a0618 66
    0x91070144c00c81031550340030510098441100802031a110300382000c040320201504811680103000078440e4035a103210300780c41c54134184c2d003150080c0900720781c0003001d90501600320704840c2031b140c96600381c66044105044500b1a110000d0340503899107170006040104000d01c2034064019003100d082600b101d1805011582d40034007011310312100b4040c03400c2d039400110342d0b04200c0d80d070400171f15545d4140b0300c0c06181c148544080708006800410000040c022450080c021209082d5107265405011b490743c1c8049010324009141e40403081200441c1c10304082d5144959684001110301c0b4058072007020b030095420007002050050ba85d03c40411000d00c007401030000013055414001d1031410203100011382880b030541c2240d00c803902d9001245001010f1081c5607001d605d000e002071045a00d0440b1240d00c540700300403e80d55141080743c0503561100510450741210070586401d03250078a541c1d4140d4232020004c007402e00c180901000c5038040341a601a034241d000e00200c3c03101030070001d40745c4030050070001c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 791496906 1250 791495656 791495669
    0xc080616030c020d0c06060e0702100e0a020f1002010e010230040302031e040806010e04030305091609090c091107170909060d020f041119080c0a0f02030c070e010f 72
    0x1070640b80042560045044401800e0a1030581220856800c00c10080c02c074507031001c09004a14000c000c0101c0c1d020510301036011284805200b0600305407a9107a603000c1d60b5001940c401004695201d07140382a8078038100500c1103000104009140240300e0342260014516100060a4078940720305800c55040300c04824500c2e403617a408142090f4400030741d07a004151145800241106801c5000004c0720140d0b4010b2a21004507149503841d00e13100c0c0e65070b48013900e044000c07904260110303804110100d00da20038855001c010040f00b5190070740c480040c0081e0a0141c41e00100c490380410b6a0059008000001c10391140890f40c030041460030703054103903203044184003880c0180701d6000a40d890079030341904804210f80061a612240c000180216661820140c0c01803910302c1ca40c80c10381c3d9940281031805440207040d580d400030300303409640c2081c045485008055040003000400790040c881041201101e104032814074141100143ca4041643c1111058040070710040110466000700540078115 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 791498156 1250 791496906 791496911
    0xe180103050607111f0510090f0213092003060409050a0f0b160c021512040b0a0c03060e16020a08030403020114070509210c0402040909060507030c020a1704030c08061603 75
    0x182c0c0b45d408000055150054903003a48500c0800c90f2000c1c001118070140c0501c8034100070691760500345100075072150000407080030404200054841103403103150300042d008160310807030410480700101e0341c0d44014a0726500903034070b1300404007007101040f2249030581324640d203424181440c14909852103005200b1b00c518040c0c82a41c1d45880d900500e41c484980d410380b03001009080c0d4600d0104140111004c0241c800718180400040c0034100d80020301540404408214184401c1300480c02e55086002e405105402c490201c4c50728014080c0f400802c14041c815541200a19030350002c00d80c8c401d550542c0140e45402032000382c8201c0d0a5090780041d40790410700e1030401c5080204019180c1c0d06281c40c400c01d101c080744101c2030018488440f9484000b8401c55942c1c0d25004100000c2c80020402c1d1105403034100002d010030f000780305c0c40120584a030000c0640d2441030340da80b0102c80d000401c018074203006210000006070900c042c480500742000180559140c41480d1527000200c4c903844104060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 791499406 1250 791498156 791498173
    0x606040f060c051f0b041b021902060403020a1215060311010c0c05060301090c111b0d030c05010c030f0533010306031e02091806070e18010305060711 66
    0x800440e03258044030707440c0c1005006003000b410302c2401e040085140c00c25603040844004070034030040d803200b0f90401e03084030100210142801500784080040b03e0301000750780f1883d0915411440082520031481c401459030345810380720b40c08070300f081d0000d521080302100200c0d000000c02480380a02401d455481204000d600d2858076800c2c080840c2240d094140401451001e0a0200c01074005001c4c00019109541c0ca50703643c0309110080c4010201000041e202c05e421541d220b070041a009507180070196016558000c0104101d14030a8071402207080c485803c4074800050402c2c096450810415140020070b400140d40d10f809641004101111038020066130003030b40314844504481080740014042c20f18845000141c0090540d13400c0a01003940c0301001c0281c104400241c210558400d8400c4200c40c2c0f01c4a04000941080550586494010100007841c083c4291111080400001c010301904100c0301c2415509040a0b00150781603005001042415500030342001140c000101c000d00240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 791500656 1250 791499406 791499419
    0x902090a14060f0307050d09050c1008010f0504020f0d15030b0c07020d03030c090b0f19021204050d0204060308030a05070e01050705060412112e0b1c02011b03020304050306060604 79
    0x81c482c3d80034007810018040040b4041744c1c441e60030f40352141d40980040100318407a042c0130348c0d24180306481511440000208019441c40f5503615030482d040e5603003100d0014101820072010390010b281d0004e950400b404100e9408100b4000c809a0350608800c00c0c03602403c609298030348581c010320550003810200402401030711511842c110903905450300044d00700e10050110350089490340182e805940120340d01852040c0703c00180640e5000342419106a100160203036200c20150f036650540c0300c002d00040120b070502840703100f80e035031004000044681c2c99964401031604195502080300b5a58810049007070b82010a1140080302420020700304000756880d1942e420b8018001000307000c00011350100a400f800c800c102c0b00043c901500c0c1c1c2d840b8428414030080d40d411801c00f0034190f0030080d41103e00464030698604040c0507102243c40720f502441c502c40140b09181c03c90401102c0c1580414180c1041c2ea1520000d210f41e0246507510301d41001c0500e0284040d018034401c1000700f0081110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 791501906 1250 791500656 791500669
    0x40f06020d09081509070510111606053103051015050a0b0c0109080c0303090601060c0f0308100510030603052407080c090402030f070f020109030813020d0203070902090a14 76
    0x1c4880f0070302101303c5aa618140c03d0a000d00765002580003901c6007055842c00b03420245c4a07121700b1400782169100701403c0c0c407900c0824024810600410340c100480224400d1218403000581014940981c003040349800498142400b0792040c1c44581249201c10903000c400c0c01840002803540d280c2203c0e007400c280004000345014403404c525860002a0880284000c0d00003140d050b410210722a2a500d0f8421055100d40c021540c0340c1450107807000200da12401340440341f43c40c035000341d0103004040c000c1d5010790700801c02411010308007030000b00c0014a5940c4149000040003690b80101380149145890f5240c80c0f90b8078103258034406104c800d02a81c40088064076031048207481d01a00e5030b140c0e0200180340303200707030755a86400600010401000e0124444602d00414040d681c0041c0e8615041d0100d0032102d620318002e0004140310302242141401042c4180d90341c0c00100f1222101d41c495000a1600300c0e641c1c010704003540c012420f00e0003031504041c0da40c010012001c90f6170306440100c000501 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 791503156 1250 791501906 791501923
    0x9020d0308061003053904290c0d0309061401030c1703090f0f0105160c05010f050c0d0f020304090f0507020d021b011b0609051e0a0b010506090312040f06020d0908 72
    0x40000c14803146c0e070f0205405480280040c0c14100c40e01c0e540d0341c54042c03000c0d0f60f03e0700e1200d0741c0790700c0b40b00414030540f400b200040313a01c0b900450b0042c00344851403140c03c4024009442d401d50755142c0729081100034846a220b214006c62049174113800e1580780079104607903200100e54882c400d41050225225944680c2401c2c4d0b0410021160844072003003a0006950070700468031428021825032038001c0c104040d0300c0c520015580242c0745e04041201603203003290144035140d4015516004080103840e00c602a282e0405003492070700640c1e04082e1164101c504485044d401c00308150f4548051014a90301448807841c000000d1000d85091620900c3c100416460a5404c0f410013a84d08641c194038a04100d4118007545d01040900030329120f0f051183d660040d4203040e400c0004070008110300c0e2200003800845180e0f00140395481d40c0c0c41d110400100342c001c041c17100d400d40221000007000840742c0c0300800141c920348101d400c400e41011402464512484001410b202c080300040c07101c00030001d628807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 791504406 1250 791503156 791503201
    0x20c011b090602033c0a031401141003020c0a1b0e0714131211040507030e0d05091206090a11010201050c0315040608030d06170102090901150309020d030806100305 72
    0x72469800300c0c188030005c40083d9401c0718000302c000d04500741d040c40c0600510140803195414010070000781c19201e0444000e02c42e4a50b80c4601e160190b0090900b041014004940e504005042035011101107041c007400031402c40e10b00d0599a80d501e86404240c09000141081e0b10420146281c081000b4100ba10000d80008a1000c0850b5500f448000c80c82024080e020b04d21420011042034500010f4101008030f406102da400c20001541882c402e210f804841d1035003000034044040600000d81c3c466210035030064014042d01c881031014002040001e014160000c000c0085180904000401c7c00c9004501411a410442808140b0031514242c0e80c000391400d0b035001c00c1200000008009240551101f0607901001c10710600030344455121004803900d4041050030858101ca00c4d500300e11510103a00d501c80704040042c8504041040e101c0c04941d213504000036608626000140308104c1103a04034002041d0740c5c20441399041c2580c40e035400ca2a94141031009082802e04070580c5082d098580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 791505656 1250 791504406 791504437
    0x60e04050f04120c1b031223040501033305130504020315060d020a06030506101407080f070f0b04120c030c171210090b0a0f0905061201020c011b09060203 68
    0x40c02484401c02c07074021224500c0c5c000203880c0d0781d80e1400d0380d0248035a0b112480440c0c0c1e14464034820010740304204a800354010b01d00c5280504010054000340301984c5041058080078101010781484610502c0243c41c4071150145018540410000d20003035190b80102554103100600c4010380b400580c250440d542c82c00c00059965502c0041264001a03000c065804425410300080c43e5070954803181c02400140e0300c0b1440e000043c10160340b580d602c807905140c01c1e0703020002000410310314809890b10f003d07580105071400000c0d4540c00310002144600b500c0f00030340310040c041040140f0110302d10040c61424809000d440c0741d02d000c0c048003810940030f041d07500b4103144820100c4607007040b118211801400c0e905181040c0702e501200450718041c503005140341005c080e50520f0f0400e450402c80341c0c124000d910081c1403070b066101420001d0012908104e41c5451804c100c0820f00240c460070380707103400020f94903000d252000b1524940041e40c0341401400c5105011540c3d020045070102d0b80200300c407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 791506906 1250 791505656 791505677
    0x91a100c020d03050c01150515090303030103060b0a121208010e010503060f060411070b010f08010213060f0521191e02070206090d0804080d18180b0301020301060e04050f0412 77
    0x744c4092062500104407946048405104182062403c1080d200141c03040044004843c0900030144580300855905034070904c01000007500d030b40c106044115016084000d41640c8521556420000b0030080340c0000c1803240000d4841e07440f500b030b00d0040c46034021622036541350901190300c6500145c1282502c034071043c0040d200c0e480e40c1d0851011814481c0b529642c0341024203001404d03001c28012401544a10f2070009240c0b04140251080c0c40885130b170701604940b500c101030b103041c100d0414203028000284242c0340c0f2001c0f070154181c60060390815044c0c1c289840d20794035502e0108104940030003840c1c591580700e00900c030001c109410710358210040e0b40b085079000040140c050300e1181a884003600f10741900704203c501c043e0040b00c4050041ba480240f1402c0c1c250740d40a00c1c00510492030790966020001c8044110b03a90755045405071000a500d0066808203003642c3c0b090f08501c000c41c040c00c4000050b0b003020701c03409612001c881e1040c1c41c2ba043c142c1e2003205419000301c0c4401005903d003035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 791508156 1250 791506906 791506913
    0x5062404090f080c0c01021c050406080405101103061306030b131407060e120102030402090f1f14120a1211120315270c0a18091a100c020d 61
    0xb003032100d5a04902d00644a8203800900ba61350515480d01c24014000e01c0b603e40d1201211071854010000b55455660078141040d074103d440303405c010019101e602c600150703001c402c0e10a00c51245440281d6030410750b41c2c41e240c0280002c45211034440000d50f450300d0f80030404a40707443c0c82c0c0381e0002100d1041410491447c1469a18000341c01070110640c040d03c400000c2c1c003500100f41140c181401c0c0c59203c203e0302c803146170300d080340021100607420207510400a00c040c22001d4616522004402c1304090480f403404862040d0034158112a000c040365010892040c40d003c0c600720b0304414144004c002145440c1d580802c201c2c07882c00c000c01805002c40303207841c00f00320902102c04507548210780b9907140e2400c490318000f80e0400b190010b00929801e2001995605408000603038031190400900c0c035500e5032042e422141e8801c00b403000400411078103a1486d42c50f000031010041000810100d10501122002110803903244d00d845d204105030180240c280d46c0000000c42c0c07042c0c0444806541c6401801d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 791509406 1250 791508156 791508173
    0x12030c06020c010921141615091e0c12170a0c0b07120f0219120204091503051e120c0718050411010206150904020f09090601030506240409 61
    0x50b00405c14808000194000380c1900d0343c24046001c0380e41d40001c481c200c05054042446401c4004003c081240070750f44c00700301c025100ea80118444d150010b400105074458041c0d010f14a0700d81100380f6a00c40030740c2c0134011403d01c0d040240c80480c1c0c108040a20544e00c40c0c00da100b42d01000c0544110208804840700e014040d80c40e00c690300404101982e02c0c00c220018084010b041d800f0036440d1400b90100c084d020780e8800d550700000d8410103100b01d0006800140c890202ca03254031007900c1e800f00004035118016008111080000e49954803602e415454410b0406240e24094810210840024200034000044070682c80304989c0d40d0603568802c2d401c0090034040203030800f16810812114400c01c0340d40940c0804c0c4030b14025240030501d044a80012600d401003910400c440900c560003070720892512030540d5401910017008100b0600e810008a20100003c9039501d03940d400100c010010b101042c80404c1e03100b208043c101c04000560309100019403080d034a80c0340039551760f8520004001410b0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 791510656 1250 791509406 791509421
    0x30f0708032e050f0604081510090c09050910081c110f0c090702010213180e0105010b0d0e0c030f06070813020a0b0304110a0b090307080307020609100512040602120112030c06020c01 80
    0x1102074610310910281c0c1d5896161094427020b0081c441000001100e5620b407186410510095581b0084e0b14580f10400c2000513001c1c190159240c03010390001200c0c0000c00c6100700d0b41d541d121000e40d43c0005510007601c2c0070580c1003454072641007146910801d400c003042e40420b40307504840d060300366210310004a0085c0500060107605d0000541c02094580342c9040c1503da02506841c24852000040911030984000b0300c14010030b03c4040c0425002740810b500126160300d86c04045403140c0e6007c60019141c41c80316040e04885401a0041c0405290f000e072915910441c1c810f0070340044119980400d40e02202445009030b400e5001c03012604210040c0c10307404880710000c01030000342d81c40b200c00516650102480c28460f00c500c03071000400759404003d80b18401e4000340040c0c20086500c06120103044100c442004114081114582e01110f81080354043c501450005848007400c22606101c040181c0060128040c2d040b00b80000a60161a1541090b402100503880d0301c0110301081c05810913 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 791511906 1250 791510656 791510669
    0x3040605090a08210601051e031306060b130b041a03180d0206160906120b01030608060112110a080613210507050c06040302030d030905030f0708032e050f0604 70
    0x2074145801680302c140c000c2240c8200340d48030403170701c40700015201c1c1c0c80781600c60781000710080304911005081d00c2c0903691140c1e000f04081416403aa540e6501129455002000d4000300071614050740d081c03582c200e20180484940311703441c0c070307060104200d45c07403081c40034450700c200001001401d030701120310001494280c2c280484080c042d024001a441701000c40d00c1e0310703080107001560b4600307500c40c10124044540640720b8409110b540018174000c1e0248100e1a414140c54400005078a0004c000c5203008051040c01d84c3d808542510b040c0d0300c2d401c4140d541c24070a50101c4000d010b00c150100e0115008070400403d0283c403501c5145c218200010301510f1f52410f5600e104a0050680000080c40c455114001381c0d44000304040811445000764000070350503034005580040d15601a80c070100a080c013a6045904200d80c00005400962140c1c5c401c90700b62002000384502c080c22140551107820500740005c0800c2e400011201f03420100b88641442200e12081d200103940f140c00460340909030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 791513156 1250 791511906 791511923
    0xa030306090b04060807270f0203041b05010e27010b0c010f0c210e0f0109110409110910050307030c0501080a27081c051014060315041b090501180b03040605090a 71
    0x408900b12300094000f201d050f07400c007030388002c0c00a61804019911040d94016180c40c021070403590705100c100c0030482c00c007501d43e000011070317401110302d81003010b4024000720214a0355a29015040350a4031118114585080e041040c000c200d01d820040110750707425000c107000703440260078518001404070043c0064070350141020405117120190045c00341c650058800d258405040000c0c03108882c142440a010700550040101892900905564008207030001044049481e6800203040413199401101c901c4c0d01075904000381e503082000702d60320405110f8104240d81e650302d804c0d400242c00c02e8280e1403250b10560440b0800041109440d030501c0e120080c00ba0105a040440000303280c1500d0040010b004240c000810340c3d541d80b192a02c3d9070340504410305540303828000300e13800d080000752181d0158a440c10340c0c0c10300d4001c1e4035104224a01d5035500403901e103004009000c1000c3c0401070380031500010f1041c090315038040c0807282c0041e8002000a1603a0300d1788401030906500100041c2045e8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 791514406 1250 791513156 791513171
    0x309010c05240601091d1f1d070908060f07030b01170c07020910180b0f0303160c090e0a0f03020114040c09061715090c030a030306090b0406080727 65
    0x4100e4180c240c0f103207000380c03184044c1644991507500742005c0c034290400e640d03160318001080342604854440c9852088444010b086841d0400070184428003000044601040804c10800950241e4541c1c0202580005040303141040c00c1417110225004004200745a2107080305081a4403500b0002c80048900c0181c45050401d2004801039a1060300709034030842d104404900c0f8141074100440c00c0300d0310440d02801c1288628503ca0150044800c2164401681d0090b040c264809100400031745030f407a031300d142c1500d02a03e802c100b80810b581007040901e19184c480641150001490140c07190042c40d500000c0ba03592404038050004d0518001e036100c04482403100b0031500121180590794249018084507881d41002c1d0140b10484c04821030580c0603058101d504501c030a607594001c01000142e54050300c4c81c0010924208225400b140020b0b50342c41c0c10014051a40302d00788400104a5092008900d03100c1e9040d50380045000b00703940e181c907904c0701260b4004a07035110311030031000311010300010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 791515656 1250 791514406 791514463
    0x506060a080f0c04081e2e0e070906080c0316050102100213091104150e1e030a080316030b0303030105010c17130b0309100915090f081b12030106020309010c05 70
    0x42c803a41c0071141c414030030513406059440d0540040440303a2501d07c4410b44505441101e90060503000702002800d00400d04c3c007044032829801042d02911100740100b107078011403014103251141c0c0030360004820040820500242ea80072800842c0c2410500002d600ca514149103415040c4040d80401c0e10b040c40c02c094000080c1c03403a000703407085800c114251411030311540c006032862145072804982c072541d9910f08101180b036142076028069005001c8685410507950780a441c2d0b801552160500001d45805089065050107500c5190000750082c0d401d42d407420001820300c1c001208010480c920321141039000b5412310003039130300162000661118199545988000a41c02039035032002c1401a014110250b115034051203048641c002c50100a4089414030305000b4110364070122002e0b41081c2c8080007064414000d448160076a045546a000d28800349d00d01e00443c0071407105070700f6800c8c03004204054000c001c1d00c40040c020309248c800150986003003410b180481c3c4914260b84003a424070b0406 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 791516906 1250 791515656 791515693
    0x5100213090c08041403030c040302100210051f29250606061e0c02010302031b04080f0105090a030f030911031f150506030105041a060712030506060a080f0c0408 71
    0x25406000c400045d054807201c1207480703200c00c0b10000100c0404000801c01410203a031071b1640c8070b8642c81916845200781d8849800e076102600c0118a5417140c0c851070800668162888000703148412030190200f1f00c3e401c0d59550013401c0108101403000104079814641008560034180f00c5880c1c10104004c0ca40d032504c2c8004090300c0c018900003c0c410300c0d01c1c0c50703144010341000d1980c40f60780c0c0300c913552404240c4c011006584002c1c1814945001c81900c000f043c0e40c10800703400644071038400344c87c1c40303d0144106401c68100500c0043c49501000640e408243c1140740c2d06040020707840e0225006606051405459220700030858241c07203542c0328607991003000314001c038810505000902006180034500802c43e2024010300d035001000300010003c0c2c2c0781681c0801c0004a01101004034820400002100394001401c10340381e11541182903403906a061256a034000804c83d161400d00d40d03099801401d00d000188203001400168000c50178a0400ca01501c1c01440a80100c2e06404c880c1c40d5080c09 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 791518156 1250 791516906 791516911
    0x20c0607120f110306041508070f1502030f1c09020636061b0f010c050403060b09010b0415030b060423040e3a030b1c05100213090c08 59
    0x68500c1e10b020403050000c1d03406220b48907a0340c00021402c42d11036100b044001c01d10b40e40840f401c0b101c1c480c000030700c80800744289801080c0e100c007005182890001d40d8485c040300c10b903100085400c10002d4008100c070b10802d4841c2d100300c68260360459078076840c01c03100510080001a40c03000d0085940b041c4014001d00b1420f20100c08542c0340001c17505c500422108294000342681d0004003400129540b05000f40803c025007001e00441c1e04010a08100c18212444145480c001032070005042c02800850b0089001d03408040e9990105585001c50841050003a80544010400e0034055541c505100341c2043c103048100500e101d903950b0b83c80500c115400b030511403e956840e4016066145840c00384610303100520494090810b005004100c521045601004484e4405101c8241e06910306105403522489003241c9002910f0785510080200c20040183e0400b007152080d558000006e801083d200c2d40f01d07848900140e16100000601c03800c02070150000881580313000b16107540f06500c504100d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 791519406 1250 791518156 791518187
    0x2d051e040f0e06060f0d1505160e03120705100e0c03120708090d0203100f0b011d011e030b04050c03040b09160e0403050d0f0606020106060518060d020c0607 69
    0x310030000c180c106802c0d00c00300008400c003900007000040380c07400d00300780c2900981c80040a54502c011340e651084210f203040c0015a40b07c5540d60104401000c140b0405201820307941000602140d00c800081d40e5090029050309000c40085a11020400c08200c50050382e110410203108a20348030310300c5551200e240c1030013403182c814081c2e1700c0c40c0c41083c0c0c011101c90a8000c100c0701d01d418ae850303042c08503000320b1440403a0903110324214110324802500c1740c071076042c04000001c42c07040341c04400141000c0000745109004918007039007131110303a00442003101c29100c101400c4000031001d80160003d00240384010342007400d160411210800c0300e0021440740e40310740c0d6001d040b501c43d1280640d0790101d4803400700400b49a40c03411300c440c4c140c03840c14642c42442407404510382446030745194240d9242c40500d608940d154102404103a8080c00369034054003480c540a4100011000c4c6a20451240d174981400b0b07035400a14111980016012070310b2481150040310001d041c00880107140940c91815503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 791520656 1250 791519406 791519411
    0x50f0a0c050c041a0906032a09101206050c090315041e0b04031215170c2d030f010c092103080105092502031b072d051e04 54
    0x22200d1800e4460804804d421490960380d060307000c0107004044601411480d4123100700344016100c41495041c40721341c42410205100710032118003d0142c90f41c070180800b084007100d90f40c00d00c240144208006001c681202e0003140740d8550050900a901c42d042d025501801854222840f40c012019424013452080b404024140050789403070701d09242100d002096209040085000320b03201c0d5280310000004014005611031705150140e69080300c40d0710040c8941c98000022402c624140040c0c40e6582c0c0603200c0f034400b001c903205c004c450b0419505940340402031a008440050301d00304884a0001900c0c002000f0781c0030741c41d4000d0081c01040c81400d00c0440800306408111105003040041c2c0c076456103031507281c0d03404c0070100403410100804401a103880140d00a42442040140562000103900a5540d9980d94481c1d01c088907850b0102802070740c841c0c1000c008000040c020350000803410010040c0c900310b00c1140d00e0450a003940026800400c030707141c0070b9200307012885240c5000c5044504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 791521906 1250 791520656 791520673
    0x603061c1202070f0b030c0406120204050913030f0305060603070c03020a02030124080a02030a02060a03020705071503150815060a0305010507030c0e030c09040201030f1e090303060e13030c03050f0a0c05 89
    0x141d185d41c2c4000c480d11503490704103210800000c0d014016800300703540d18180c0981003948600202da611581102e0240b1003c0c034448081c41819008060450348141d01d01e010311191a00702c0103d103491002809420800c0200400001418030a0020244c0c01d81e000b0001e02c02c0040c0d184e280d900c41505450a00000800408002142c89000401c51011503014019145c3c0310219020004180c11008410041c15000c00081001500500c501405005050019000040130042c024112040080d448056404004051207603250014464600c404680003664066403010301044280c071007a88000d095600341814005a1030300360f040900000595611000c1d140316100806559403004001d003504404103001060140d4801e8116030f40360314550170302152101054550001c04681200400e583c1d0355039105020030560b01d03001c3c00000344181c0d00207a640d42008828403090411418008050001041c2c1d06030825000c3c0c019103020b200b0041c043d5848420002e000740c80203202180480e03c0c0e010350310b007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 791523156 1250 791521906 791521919
    0x60c080f01061d06160b042d15020f0c07080d031b1808070902030f0a091707030c0f0503090306071d0607020f0904031205060a050603061c1202070f 65
    0x100c14121451030b030b6004408075250303a102d040030070300402c041c2d0411400c12901c290304510b1040103800ca441014003070014601810001a03207000d90203030444121000f00c0c1c200480c0000e40400c420150892a00c44103240a51490b50091040164646c1c481c01c0108191156000c00320b240300c1141ca060b01a40c2449030b01100440c100d80c2c0c090750703000c451003020140e460614814403100300350005050130b1240403500c1c4d1103203c0c60141c1990155210640010400c0010440141d00c0c54221902d1103003804503084c01d40c0ca18001c400030f01d0640146c5480030601c41c003810301c07503490304c010f103908610341c00b8844901342490b07a1039a11880d0710314041e200780c00110b81503d220341641c6400750f1800030181046000041045555880b40714242d0f03100641e07001600f442e07585c03000c0150089119444413100941601c400c001030366030040036a44540d07040042081aa120801160b51241d0300312402c0380108003070401c45164450140e0050003101074010701958032600040c56000382d0351380c510031a900555070107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 791524406 1250 791523156 791523181
    0x2704090f21050a0c110111030c0d1b0c03020907030b1309050c010e0f062a0607020706052a01021327150b0a050c03070533061207050d060c08 62
    0x15520f40000f11014818030109618082c1480300e0b01e4140f40100a90181c10060381c0703960498811403481d50004581d1001c1c65070071040a140d10010404113028400303081d10b41c040d622400d480040d01440074000041c14041c0b20780e120b0b0400c40fa00400d54049052070a40000081101c8181110544034902e400404c40d03010b500f002012400c0280417a0840340144148501a0894814030514454003031800000c4111850032070a00e1412600418082c03501e40c00080c6489540d40c080418802e0401010842c180302c1c1d5a02480344440c105009485000300c41d40318024402c801d151001003405500c08505200740e000000c00d00820404600d080d030b01255102c0085560170007082c1c00c1c11410703050801424900e00c018088681c200d003062420041a130b1201030540e0b0020f4012589074000d0300301c0305201151081002e80510039480c1d251181c40c0360031902c82d42c03a0005891144902000800c0d0002900308001c0c1001400707010309482414611464000081c0c14105403600208280f84d0004a508600b603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 791525656 1250 791524406 791524417
    0x120f06030c040c031104090b280e040f2934022104030b0f0c03041401020d0f091101030912120603080f130b2704090f2105 54
    0x502a104059079201000300510040400300145a104c0380801d80e1070300c0d0312000e08020400b010010444c20b513120100400c404810040c0e450800c1210111816020004503c0041c1e682e800a6050f50391918240041104e402c48001010220008503070a0404200c801e003c0454900b00d00d0311500362280b02065090203a40c0c100185500e200300c004402c290716805d84651100060b005403000c0c5041b461081d20401c10252200c8000040054100208680401c42590069402c0c903c0c04c010704040d40700e030010340300140002d800760440e4924100301040039411a18079640349401004401410750b2221f000c1d003210501650b02d500c075140c40e42c2d0f15501138007403030f4091a8880307050344c58190501c0301070f01c10a20300c55480d6280b5613613490101c00641000010541c1e40304840d41145c407080c103004800e1030f40406d40c020200d69841440ba0340c1c800f4100d845403c2600c2240c05421802c2c92a00001c580101498540901a00f40800200303040c00740254010680150340581c12111020030003003600d047c8140c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 791526906 1250 791525656 791525659
    0x903010e010e03221a03090c0102060601081f0e0106020106050111070b071b1a072102060105010309151805060f040308040b0720031b0f1b150a0203120f06 68
    0x100004403070380e6408100081800f142c01301d1031254030380310820004400c009442c40200441e000040c000c0f040c0c410401182290001d100400c0705181c03180000b0010240a0302c0d50f51450410210407003c40303c03da03118005090b01d4040d20fa510369491800138003030301035440f40c076012450100c001c4100005c049902c0d41562009070416140269035500c42000310118807104481000c0c0103408540c0c0e80740089440e44038060100e076039442e40c1103810100300d16801c1e51a03c540d4003200505007241c2c50f0700070808604644003400c000614071981c0c02e040322a25408140d40e0049481e18401e40e103403000c4100200c80e06406030045516070f98861120103030036203003a00c01802043d010400900043c44481d00541c0c0400c451509400d0605400c10488040150000ca4006d43d08041500806443c010144810000c1c180300108030308a56402c841d074561126401d0b00014640380203207000c168581d080e41840e0220000405540c94446500007900c1f80c1004402d11203464880c000306401400741404035014840 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 791528156 1250 791526906 791526913
    0x70e010903050c012d090302040e0d0f03050601030b0d140d110a060b0103141305010b04180233040603060e01030312051b0d050405060105060f2d040602030903010e010e 74
    0xaa0000544a80864000030040030620141294107485680c1e0a170031028199220090102d0a52040209030785003148803004552198038140083c951001e03007401090014100000c040c2c6070b0500407005810b01204040d0084020b00ea40400c0201184c100c1102a1005064075101108407500303d803400c9102001d09160340c030003808080445c01c03590100f00186c005040004103526078550b20290800104c2d003143c03080c103552001c402440001c1c080d004c0001700845d030400c4256004205140041c580b003001a024241510815041c500c41d44803070010440034116200c1e14040170a00e00500d6031107030181c04000b90a140000480121041210707068961546400000a0014450800500d001000d080301060841e001703010890550000f4000400c5981020405140900708203141510690102d401510100600d0000c840000151014803141f00d103034400040340c855044403035602280000790341200015001890079000402003800a0080d40240001d42041d40704600703c40308212101120b40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 791529406 1250 791528156 791528173
    0xc070303051b0a0f0b0702070e010e0603010b24180603010b0d0615050904050406150f0302090115080609090f010f05040605060307030c060f051c0905151005010c0f0f0506070e01090305 81
    0xc510b030b005170740c0c41002d078811180300aa8403070104a9590f400e03400030310b058800c001130000700c4c1000c2c054510b02000c16902c00a0414078400d00b80001c01d05030030100400c04002c40e4524161001c0c90703a103035460350010000c2d501d9507103610040340250700c001c1869a5032071a00301c000440c1e1103a200c00c0c40b6200d40680350182000594820f00c03018010081044030714903070f80c0b620100010710421403400a020003815000c12141184103010810303030181c100c44075401e011900601410740c8404401e501c00c406403005111038460100551420a0000c0002a59401c00000d81d40011107507000074440c0740680001c0c0410744032601410385407801404007805510fa260000e101c054003c101c0b0300301d402c2251520030300d49201c150001c032035050440f01082002d5102d20318281403003c00c00c000180100601100c0c44d442c00c2852a0940080345442000e0500c24505858030500480718902c010040d0008040d00c2040c40798600039855000c01c9444d1008039021001d404c0d159486140d0038402d89902c00700411468 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 791530656 1250 791529406 791529413
    0x1209081c0908161509230601080706030914100902130b3715020f030f181c0f03080901112212110a0b1809040204020c070303051b0a0f 59
    0x1890900300c00c1e41d0710961350f031607000e5a180034400c00602d58003440c1daa210036904c5050600400031001d16004007540b020700144203400c80070441c08115507075410006103101c00c07450700ca514811500c440001500901a004284e024203800c0003080d140700b150f8000540b90450080800ca60401b4800c40d000440100c21a0006040220002040300801340c0c00c4011141c0e03003c145910245608400c410003000b0184c109090340410665004d508100301450910b04220580e000c1400307084c446a0101c1d80c5074200300ca4548403100416101c55200c1c101e561000c909040c0dc681644160204400140c0d91000040441c08181700c2c08842c9804501150b150030425121406400d43c81c0c04418102401d4610001e0701e050428051416144581c42000c000e420b480c0400101142550180c001c00b082000601101c8000400c80740c1020411981300303c0079201c1d40085402402841c2c000c203514426101302209158001000d05500c40c40a48024510151081d0303090b2518000d160081008070340c4c01010000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 791531906 1250 791530656 791530687
    0x101508031b0705060a05070203010b010c050a0312180f021003061a0d0209031e01060b030412210204290f310608060f090907060f1209081c0908 63
    0x441d01d08030215515103403500c0c00540c141c0e1152402c0e40c042030300000c02c0030850800303005150709128242480e800384400360704c0c3c05490701c41002c2d00908000300490700d9840c02915900140e805158200c00105442c01c070b00c0c1425840044200c282c2c81000b940800f23850940c424060311060f1000c20702006400c0c135401200c028203803c01c1d08016201da800384035001142d141000030070f6030206540e215503a84c400e5a01d00300d0071180d154110300b1584e0010820400403481c00214189496010300e012096904490241c44d000502440e010344828000a4009000400312a91083c100c3d042e40c140b003030102103c3e8100d400c0d80b16008010000c00070501480750100c40c503807980456440307100410000f040b02141d0307103490103160b40c0100010504a20606c0500e00307004c050042507107421b41e2800540e08141c00d9140da141d189102d8003041282a03c0d0100c4164821800c00141560301c3c00207020181c11803624000310380042008150340c1c461161508070310901802541419030f048148d103483d0100840343c4800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 791533156 1250 791531906 791531947
    0x21005072414090d18050303130e010609050609010f020a0210050c15130b1003060e07031101030b010e19080a0c060809151b0c0633092a0c10150803 65
    0x1174144110000a01e1b0344081c4020803c0c5400d80440400c0d47d070500d00125440301040c0c01520070009111004e02c01915688102c4900da00242082d0241c0c40c10001c1c22881c1043c1d91000a411038143d400004015400c9409801c2c000300c0c840580d0108990f82d24814480401110400000d01c1c5203012a0041b03400b00c00200e400419556500d036001d40c5a4566070f007595554030200c000e9070300081c01041070124010001066600910b1305024809040300000d00060b0b00d0f015191082034003402c00700c00c1c040c007142582c00402d40324065904960843c01c18a00304d00780d902c80c510110390540300191074080081605211f6068400210301692941c000b00c00400002210240d00490308004080750350000300141d51051824481d0b0010b0f500000107065240d012400c12150b001581c0340ba03401c03103035988003a12940038202c800780030759040f04584025030040124146c54000040000c46415081d008905030a103005940c42c14052072904814805035003040d4811684941c1080c0100d200e0006210302c40d40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 791534406 1250 791533156 791533187
    0x717010b030c091f03110a08180705030f01050a060501020a0c06030b0a05040609021806030613020f2203110303041805090a05060702032107050403021005072414090d 73
    0x1428020110f01095800c5919210003c150b40301c4094202e2081e07150141e6560468484121402c1a0040c04040c04044014102d050401c0400fa298100d452003007183e81d000b804001c007116101d601c0c0c041e096000380400da400f40c403805e04090012913294000100720300070b158031890902c00c0340c0c80c02034214010407044548950000f01072100041a6445000e001e01821020034010b90358034032004e00d007070b5522032919010f0250a0620822020780d40313131403050401c4030700080c02503034421161782203051500c148008030500b0080c04001c0003900c40300000300800d503841aa220800082d82d40101942d078050b9210317080e5401c200c8840d01001c900190401ea0308078501034200c0d078920003540d0707a01d818000103e4145005034008255002001582e84050842703641c1341000303a1315404c2c20300d001003c520550001074050000b00c21100545441041204c448540000b80c200005518101080e0000c086140040a060034101d00400b90300001c00118040e01064000f8a030b00c1c0203856042d14104120000c24 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 791535656 1250 791534406 791534431
    0x30c031815080a110405040b06040b0f19020a0b06010e1f0e010e06131e03201203032e09051003062a080402060409090b07080717010b03 60
    0x403540040d511118502801c15028608110444110010410b1000a05a0002609015200c403940404004444c00c0d100f00703071404a46c920601011444610481d4007039903a0207c0028228498110300c4040c080e42e0511880514210316800303007c0342d4a0184017005008103100c200030504a40c0114800320415002400b295510b5202031181516681442c1d08840400e030249089a03081d03922074502c0030001001c07980035080c00a203160000154a40c1e0041e02c910440003000c400c03c441301078003640b00442d40104412502c1e40e01048034086144c2c0c1080c0b40c1d02400010703640f07030080b0b07a000c000d80b0700c9508104d00c40c205801540c010060103440d001c0c1010104200700c203001c40e100c845400b400f40306001300d00b03100c0c9200745985410412500401c12550303116506d611741c0d042c212404510740b0b0b240b40103844c0503403c90f2154000141948034540c42440828500182282006001040e03580b03d03840341d4403210740c42d0703070717040c0b0151654800c0c1482c081005a280e03005100c0c81c0d50034805140c0003074401144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 791536906 1250 791535656 791535677
    0xd0504030c0210020705090c31030206040602030d05101224090f020f0604030b0a0c050f0c1b0603010b09120a0c030c1a09060d020d090602210606030103030c030c03 72
    0x8101406043c000e41e2005070001c5000b4440c5003001a10260416000b120503450100607214036102d80d01c24080c0032500003d40c0d4580000a03000080a03030185800030522660781d5503c0c00081d6503944000e81e103480c40c03414600000c2000e040140000215244051041d41c10580c0c4d540e1a00100005503a0400900145c2401400000c1622826009512544007103100c500307035004020101c2001c404039441014204000d000054030f00c409a40c00032a1000b02081940480c2e20170740b11030192a40032095400081103c3c80081000241c07043c21100c0c840c1038002c0800560300340a803620003405820202402000600020304010700d2200c0300030b200750260381000700141e9803400c40070301581c07040c0e50b001a56041880002d40d0103c1c040c140601d645e0207035180442e0007010880c14040c3c0000f41031041e50229840080040c250060a1000d5001c0011941c174489803260001310040348410184190907000080c60504219081742d05890309a03e6a03100c000080d0780803561840c50000440c20000c11649 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 791538156 1250 791536906 791536909
    0x30b1b040b0c101112091b120a05030a0e1e060412060f0204080a020907020d021c0c0b090304090e03040b030a051b03070c1202010b09190e070f03031e050d0504030c02 73
    0x42c8188138a10035a841e42d40d2000c4100300d00101c1000d006021190020130f4620351320355011002c901e043c0c00c155007500041245481003401c042c101c80005c1c0c581e000001340ba02040780c1c40281c122920208941c8603084d03801c1501481444d000e00d55086412120400c0244450740c140050450654403a00c0041542c500d41a4601c003030345c1003540119002d902c25a490300443c90034003400c66010031a480140791510000b03170300035500c2500583c031400c860b018420001c503c034800d07034042a02c580c0080d461003143c102070034a01d5403075110b40314210016240a85e40020884040100c0b01200c040c08912400d5469691000d0010140540740c41c074800c5204072030844440c003100245208070b81076110600e04109174240090340c40c00001c0c044045900d80f402034901c541d5605074282d0454490404e6040c45000500100c1c000c1c031046685c0c4072213214040c40010758192348180041503134482d03903401c3c510112451030a2071440855510070f0200e0400d104491500c80c05510443d485030003807400d0301c600c5a4a40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 791539406 1250 791538156 791538161
    0x411040b0d05010c144e15060c030d150305060403030501050108010911070f060e25090510150318060506120303090c0d050114010f030b1b040b0c10 65
    0x107000712001d94440114940c0c16400001c01d82d0300500f40e0f8822490500d40c030055140d0a00c900060135004060b181d50111031a020700082c00544007100002084d840164440b09100e481c1250030140c100a0100c80710250b0402c0410b680103882010019030800d40480300c0400a045001c00c8528000c400d0b442c000041030041051902403402914001615410704000400c00c16050304100e9420b424030a0183e1460348a00440312019045400b108844110f8601000030b002640c540d4080e03881440350300404480045031041c00101d14003201d0400c62365489404082e00c504503901c500408100e842009242031071103a21081401a10300040c510154a403010450040e0342c50955080380e50360100038180c10405410001003100000450035850310240031552014610728541c020030300303140d4510400c5000d42100f05034010717084041d01d1384c3d03031913007030820101c0300c41d12081e00c0c1281c5842c04528540e11602d289038030a0200071a00d0f02c0c0600705259244aa8000d02a4034658032940b485803c91407802d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 791540656 1250 791539406 791539429
    0x5180f061e12060409021503270705040b121905150a1b081005010e0d020301060b0703020706030b01020709020a0e0415180204050f0d03170f0f1501080411040b 70
    0x7001100d4603024a24211100e1090081c20980964502100c0314090f988800702d080d0441c1024102c1c56603543c0b04524081d010180c2c102c0c10111292010345c601c02200701046030750035100280d40800144110302c040055031048460f04c941d0b0f071713000100344030184100c4010b210400f900910071039495000b49451902c4514040fa00310200d1079446017040c0002c00c02c030b00303180c00390412482d002c034060030014011628820580700302414880d0540000ca000d03200d80b040501c07441c0d001002082003941c3d40c4020521036020100c1240140210319022500381d00031300c100411000c1c103900903d4030508010440000b544a1203406081c0001c019036031001e80e45a01503203200800d0008000300d00761030701030034101d902102000f042e82180140401c1c0529100c46698815040089078024032210319401c007510b00b081d005480003400c0a01c81c003008030030820707111001d008000a240c4420709030f0760b46001052401080d501d10780010040340210300424a030345009018624001d2000510f144220001042d00741d48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 791541906 1250 791540656 791540707
    0x507080c0601240f0e0103050603010f02160204060803070c050907121e051b0d270308011a04180504140d120c08010503101109041103150105180f06 65
    0x11219040e0300b40103880012a1000c409092040d100c0c54611005001750480c0d2078001c0c105a03481300003884503a02508644012421a50210b40c0d4600c100f809060070086680d05034015810420001404100042210703561500641c4030380140381402c08101074100c000d0703c440b04003c40c5241c010303901045441a40f041d480b5080b1020030784c1003e0400c0b0001e507080200880b02d58002e041410150141c010f0403203034518619040081e0b0b000d10005c5054009140da41134ae541c004020980b0010150095412b9050b55119411030300c1c44041408014038610441c09007103a0b4030815281101d602c0010b80040f600a44582c2609005d40c00c00100300b8a020f24134414070000460019078120300804c0e43c890780610312401d02d07201400d58100f00111b5503490070040354a2040345d55030007292117032003094203886080100800a105582c000e00342c207441a01f0940304002c609150080c40c1c00c00c1d600070030440700c15458011803400030003001001c22501c80e100c80c0801d50001d004114440b02d072403c012490401100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 791543156 1250 791541906 791541929
    0x41107020102010c02010e0a08131a03041103030415031a061c0f09020f100e100306031202010b0913080f13080d020705012003070f0b091207120507080c0601 69
    0x180340002030035151100048003d5924064685040e01800308003071001a82051401e175540180c064048858101036020b0b0303813404190451700d465204010010f5002c2c50080b02c0d401d040c0101354040607242e1040d8460707610076506241c20708012a001e40c01180d64104d13048a500c2c2e080b804040481c205910441b20680007000d0007215020540032841910440b07018500308016150150f804250524030101c000c0344a620302002d07240d0041d200d5500e100c41007901422080d00140c03603403006409008030b0300040b00d040003410048a0304610502c00d802441c40b004000c8a100d0300c0d0710004146c035214a18042c3e0b0101c1007080b4000c0107607801d03401029140e41c9002c641e2111843c0241087c00d2007001403003502150080754003000103030f81c8211081541180f000b03902e01c4100501038541d243d8450f40000919420401c90708c401484094dc0c2c2d007a00c0355054030141c0311204980154900e8501c0340c2c08008200c025100d000700c1c2d456100b5009403159134403e0003440e107010880d00c0c1003450a0001d034440054442c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 791544406 1250 791543156 791543167
    0x171005040627020907140705010e03040329011512090f210e09071e02061b0a0518030a0c080c030c040915240609080d02150703051003020411 62
    0x401d400d0004100010000a003000c03842c55800078402c02c1e4003801280030000600003a4280e9040b0b4002c945d0380d0346d44103000300090150309103d95200d8100d44000e84040d1461152456400030045900000d1504803c4271441d980c00d1050000880c4061500c00d003c01c06125803442c6002c5580c414800741a024174109110b01c0729a240602c041c10040c414200304613400c00503908603e41100002070b220b030040790031202e036a4443d8022548901c464902d2791a80c0c0c032070301a11101d90b4000c56501d011300010001d001c043c490300d0190441c10f00c20002c0c038000190f02000044080306d40184204202d0b4002805d4820311103a030348a42c1030f04001c5410400b0150480081442070f494108900107080c0c2007980c05018204150721859456000c0b12501c2246644889002c80000d8030006402c2d950300503c0d0b010601c00c0e80b210002043c210850103200558400c00c20301c8038520780002031342a20001444088495591110b4080380508006046c1d294400c00c6a2400b0005075181d02440400e02412000c40d51141d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 791545656 1250 791544406 791544431
    0xa0e152e03111507140a0b0103061515020718020906030717010807030f060b011106090106500d0b070f0815120309030105090717030406091710050406 66
    0x82c42c1c503148451007100c103691019503040c808415544032941040d070f1444060101c0036002e05121006c40b000380a410f2000c0084108403569002e20f00c0020400940c9450707507100c0341d0041742e0040d03203080d40002d6400f200007040002c0301d10406002014003100c0240c240010040071824a80050f200385d8042400c10f40310410102418000c00d0040020000404d102403443d01c03001c1790b41501d050040c0049444404140440c0d0003031840c0c0444800c1d0340d00312007041ca007825203503009141e940110003104800310100840160035061214500000d620825101c00c400c00303412400520342041c1c000401c000551030204c03640c6000460301003c1c0141e00040d001e02d40307590300401f41d844412100040c044941c05002626542407800003c10405840c641c1310401100040d0b071440c01410000740c0c4c190308103800c101e08a6800b085440458546c1d21412091141c40b000c1d075a01c0f4091401113500003820f121003001010b190000071203654452005507490034100c1101c050648904071000d0300ea403915000d600c141d9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 791546762 1106 791545656 791545673
    0x21213092a050c0705031c0302070311060a02030708010602011b110309060301081e030703020c040c0519021f02120103020411040503030417060a0e152e03 68
    0x1c40541580184968401e085035905402252400505401c0000d26154104c80581c00c41c1075100e0030741c03022002900688002c0d82001002048a1102c030828405d0b01e010b04101000540d032460300c0380016211000607071028045a03d0130380e0b0303460850f03070b15903007804031115038904105d516540300d800d80c2c81e5000e0740d0300307150b800800040000b816180000b0721102862098900500941c020001e094880c0540000940984c1045007141c50620f46540607140003842d07400c2080c1008013030982020520714440140c405640080e80c8915480b00c01410342c082e040003240300754a0141c0004a04002ca141880005d026070345032400341204100c48420344028041c0034086030b8481e940c9401d14a941e03811303809001c200c3e005400208000340c81c18014212240702c030500400c48506958150812410002d100b101c5654180781d0700c000e090341051020303002c280b03a540e100580c1825411300b50032 = true := by decide +kernel

theorem cover : BRFrame.Cov 791366906 791546762 := by
  have h0 := BRFrame.cov_init 791366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 791366906 ≤ n) (h2 : n < 791546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
