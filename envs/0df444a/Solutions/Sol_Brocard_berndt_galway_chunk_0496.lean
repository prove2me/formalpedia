-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0496
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:06:15.416901+00:00
-- url     : https://prove2.me/submissions/3b4884f0-7be0-4600-8b21-9978a03e553a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 89028777 ≤ n < 89208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 89030027 1250 89028777 89028787
    0xd120f0201021c02040501110a0507090c0c06060e060112230a0209210f060f0c07030c0c09050114040b010c060b2d0f030f030405090c0c010216030e0a1208 68
    0x8074020300030b2000321440003040d03014480103008540e0041041d00c03400c0c0c0c1c074940400c40b003500284d80d80404410040c40b41d40b10b1001002421039550140e6158450303131801c10031008098582c0000c2da4000c2c0c029244105002041c0000da43c0c0142e0040d0a0b8003181034248500c0c5600e824111034112100e20200c0c04011601c00140035640f503904650002030018004e2540c80c5030024807c1440000350f44400b8203100d42400b5050f00c2ca00041d4051080722440c841c40714958814002c40c910350400b800490611000c80b9503900040c0350070f82144040c003a2004005010f41c58007200315802c200034030380c25000d0340c988403070061980d80c0100c1c00b840f100e410800100e40f000d40040403600752200305c40b210014480300b0078600e07100c100c4c1b030b03207032400c4000100c41e800142c103d00810942c0b940c8400b02684110340c01003008200074104100a650700c4285580d00340e040488040c0e8190030399001c0359001403d0001d403044c103410140c1008050b44210800e8401c1800e81b0b0070300d0b42580d01120042c001404880001c60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 89031277 1250 89030027 89030057
    0x60e1518040e10060f090207111003091401090506010f030b0f251701050f0901030b090102070f0f0212070501020d050c011b090e060d080702130b09100e060d12 70
    0x8800c00c0c0d58000c100c0e40381c4403d01e00850000c00c8140656080322201c6200061a0a072034001d031000a41c104945000c2d10f02e14104001481d808980c24005054482d01607802144c602c05c1103503481503c90002044200392031504a0030820160800b01384c40e640d945050010841c84550746c0c0c0c1c4184c1010031079504e41c488910040610300c5c18158540d500d03141030600d072851940000d08034050701080c614000c0d280d8a5404000070000c0001c2885e4204541000400c0800c00f00480039401000c00c100061a110440e00c0d04006024268815518800b00c4c82e954401c40c101a40030b90f85004c0380f0005812403c0c14040001c1d12024540700c90f108012010400c202c4200c1c081d40045486030701c0c1007146c1460585180c0103090420306100303201e04145c0c1d4000140c0b0034106012612141c0da880000c0a1034800b0540c01c0052444200a050800941d207000070b00300b03608c4150200f4011400610540030702441d01072a012b01301c00040100c1d011b000400120350000b15101198032030076101c0c0c1881c020284142c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 89032527 1250 89031277 89031281
    0x26030a0510090c17011d1603060b0a0819060e060d170c0c01090e01060e010815030105070302030907090e060c0f0d020a050d060b03190c0203090306090304060e151804 73
    0x1030016501c42e840d00098504080d048004048003006107504041c080e0703611240c0708101c0e0491012a0307280c1c4c4e4050005504901c01d801c4185119107076040001c1e00036242c0d034003040c01d504241c1011001c20030040510aa0740c0f409442d40c04c48144459041c803525041525040210101401540c000c50503106444100040d03d072030480018281541c01d9111003d0400882c0e9500380d40c0c21003030202c0d00c0e4001c041450005144420305071082078484000c0500c10390011600b40c80018071924902081d0301d0b8050710742c2e03000c0c0282409039040c0d0b0740141c0c503820800f20507410b01010354480039842e480e110a2901317200001ca03000d60310107038400340641c4603000d440020006104810b64039900c1440040d01c2e50320507800401400701c104403c10104141030315079002c482d09200c00c0c6e81c5034550808200e04c018000c182508076502ca65840e10542e401c01441c02c0200f890840156080221a04041418045d941d40440740204200b41250104030030048407180b11000e1091000110070000350f486295050784841e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 89033777 1250 89032527 89032529
    0x40f120302070b2409041a04020f0405090a1103030403030206010b0306041d160b030112060f060807030b04060506180a0507200114090c010e01030209040b0402130326030a0510 77
    0x1c080590041d1802140f840d24016111001c13042401d403400c000d000d00e00301814400c0c4100d40c00030404641c03030b03000104600340d001c1c0104126400411b02005516986960042900034410100100a5404286803139030204500700d02c0039009900602c0104046940040c055046805506086a0301c0e250400440d000c1c01c442000ca0840901c80c0c084038800500006055002c000d001103030840700d589401c802c20041c030080c41080500f0300d91065090104403907031710094400210350b0000031003036074400340141091070035441983c1e070000d041c04201c00d010341d42c003500d640040c0845440023110400124840d20071400303880c1c584541d0b03a032000106000c0c0109110380c240002100341215000208981c50701816000c3c0800c00350441c228003250203a100019495540a0161545510016200c0045000350800f40fa4998060740b51031030040f0585582c40240301c0743c8084400c0d10400c50641c2071900c1c10b0f5080d00088102d040e0084112980401c1d60b506aa401030f810400c046a10340b10380450030300780d102c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 89035027 1250 89033777 89033783
    0xe0c04080106080601080d020102090f01052b02090a080a0309030f0804050303030c03070e010e0604091509020705010204030b0c07020901090504060b040f0606030b01020f0601030303240312080c03040f12030207 92
    0xc1d002d0003295190002071090f049407000d4040b128180f0600200b2400c3c0c0c000d07000751503080400c40807405010740c0110f01901e0a00c00040810301d80107220f01e0f0882900c0c8403400024541580050300c501103007440c1046c0c1c0043c1c50103000801c81036046580040080c0102e100c042c0810101403030410803c010700c1d044500514000302100d80b41d0900301c0304a4100c0d841070344c1940203d038483d2840603065000b42029106284020811b50070030780b0380340380701e000f4000f0400b0007580900c6800300455036500502c05086101c0c0510001a200e5081d45040086954007400e61640c5070028041c0f5001a91281105030542e00c1005010400c1d840398541103026044012480313912600340b0350001190030b41544601c3c129202a034042c00104050001a6280d000200c5e484a0542141c001400400c1c00b03600407101941007040c160420248595002d00104125001200c04460240102c152542d0112107940c100c000030001515605103135403a115528001a0000c112007191002114624080d606880a440e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 89036277 1250 89035027 89035031
    0x21503010602030d05150901090c110a08120711060411040e01052401030204080307060504020a0308030403030e1c050a0c17070605040501051e012d080609010f0209010203040e0c040801 81
    0x1840e480042d442e60131024880100c1c615080000d8004000368420710741c4007401801a200907403c1079041d2000d400c1400381081441006508002010f400708940b800d118001c000c3e0b10f0b25900c2b10504080041d40141206003004108e1100700c280701000710340c8036006a0b122110b102c4040e85480810040c00d5040c411081c15483e00081000480c1a81d02c9001940d0440e4644910480c08400640807030285020f0030003150303c00c3c0414000207a0b1343c0d0160b40c20900042552000a1341d035a00c8904941c4121421400a0f4687d20130361049042000f01c1804c080c904403111040b003010f100028124003928400e8003c001410501e901888100322090340c400d91100074507940c0308090304000740506419101240e0a40c60400014050003010000007080c0c801c20490b54201d900c0c140c10744140e1a80b042c200722440c60038600300720984044802040060400101801d0035141082c00c1701c1c01c4844040f0010192801000038030010303070b0b0110447c0e0030b6840f0b8402c2c1040c140c42d002400e4969024a0b0400c20140d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 89037527 1250 89036277 89036279
    0x1a0706110c010c0212030c09010c0606030b010308070b09013c06080a0515041a04060e01020a200a08031b04050d03050309100e100b0d023304150c02150301 68
    0x1d9043d048000c0850298013104d1400380b00c2640103113907102c00c58514500c598288240006903102c3d26500d002c0d1806610b001c281c490300e81d01c0d0514040710a0740200c82d50302000a40b9400c104003028204d038084c0031100200001c1c1490508941425204007a40d0300c8800e00c820740d901d18844240c41201d0038800020100704094031808855075640c4840000d6a00e131003404035001030580b170702030540d1140717030b01c02c0b44030190b00c0300d0385010081c14001810850b4a035488421b1000140024805070a81e89215642c58100403030041d10449800c6c06007004200d160080300810002c10724200489030080d1030a82e031000c40d51b6925003080f0460049800c015449400303030132a40c01340744d8004051402800c01005488620300c8007041c44c0c0440790f0408003101242c0024041d03001d5a250f070342c8041c2103004080e098443c06405a030000301540340441c29171645000001c0c281d5002012a800d0b060807041c4200003920b840c1c20160161001ca00003a00c19013044607001030401152204210404800d203a4001c1e036031a5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 89038777 1250 89037527 89037547
    0xd0212010b09030708070f06050a05040b030403050301050a050306060102060c1303020d0c031205030702100b012015060121090c0e190b06040b070b1005060f09030c0a1a070611 77
    0x5502c0034038594401e11400f0360100e6115008207030b40c0200d400c0403080d101d8091600030140d406800400000003445070910000030090740000055200b14480d40d0740c595250f0500d030400c44140c0c030342d4005a000758400c00400400783d8000580b035800c959005d11143d25030019003460780c040c000700c3d0802500910f070954003504000300d814042c01502d11035186500c40000f141070881781c60200300d40981c01030f07005545105140b0f5482d400440860f5061510040d402d503441c0214024a4a072400a0a540e1115032915402602443c03096009482441c0605a4072000030740046518051303280201c5030390362845800c0400075075007219001461601c81400440c42e10340407000003001121506c1c0201070410681000604c1c08504807003d5415080c0124140411511000c848001c014008c80755100b40a40102e07803580c504024102d429002245a0355900c100c105060070b2000c000c000a0107444c2c03010007402050b80782203d0f100e100c40007106035a00c6d131256050034409819825501d072681e810005d1443c43c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 89040027 1250 89038777 89038799
    0xa0603020c01050603010b010801030303091502040611010606050405180c0c01050903070309080d050403080c070f090e010f0908070b04060f0203070801080f0a1e060603020303030a050601090801020a050d020d021201 94
    0x60801c01c44020006640c41c5424142030301c0d00e00030b401c1e000488000c01440001e02076801904400c5c024a840340310191030004e0282280d10607001040410240d8070741f0b40010707209029480103011545851410b00d0719000100c1c4000c058001c100f103042620200040000b0300f11400d884a8040d510020b20081c1084030320907480354401c00090780001c081c0c03107000ca4065030008a0300910340311503440e28685441d44d207440750641c200507040d041502840c900003407860301c409214001340048510002d1500801460305007180c0c210403040a20508089042c2c2c04520703003800f6200080d821a01c0d8000c103a460346440c0380102104906803092500c003000303102d0015800401c240c180c90380041100c4002518000726607440706050001444550311554885902c103030000e007889900d01c43c8202080c03050700c80c4c2c00641141c0040300c0c1501c401e035580f0100095580c0c0502204005c040500007140b038520600700040c140d1184840114a00d500041d000d0014096a4102e40303822003003030807100712540c64071000c0762 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 89041277 1250 89040027 89040037
    0x60c020a08060108100209031516020c03010b24040f090203040b010608090c0f01020c060d020a090f120609020d0f0c0608060f1c050109053c1e03090a060302 69
    0x80905085000440d14007030000d5000c1c1a21400402010169403c14903030000c0d501a0b00703102c1d05805010f80032444171410001d00c40c000c1c8641c004d407011107000b58000030700c0c0c49000b0050902c60780c188454600da5441d4038081e502a55030582038007006001504034a1202d20669000da8928201400006148042c036800380d4011440781100310300c0760742c0c1c1d100125174100d0155802d03401508850140c00651400d1075240382c0861040c015a16829580400070341c460700f106150b08900d580008202c00031542c4064501c02808608508100c0030b03041c082d09881d01905620b0007003549507154410015903903482c6201128940c000090141061245001151844544030f800042420300d0085a45498000e003c1c8141080142c000d021008601103440d2000f00740f40400d44195580f03900748004200b040c41903203006d194402c0d42070591328000740c404c0414043d4804140c4900300c1d1604201440b003000c100740721801242d182c0300f100303450120b0005042d846031040480e8451110b8100240355a00f43e00500f0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 89042527 1250 89041277 89041279
    0xe0a060c0c060e06270607050307020a12120809030702040608150601050309031204080f160b0c0f0a03020a030b0303190809010e0c0108070c020409080d051e0105060d0e07060c02 78
    0xa1107a90701c070000d45220302407800301c60303002d08140070030f0080d60181103101616018140f01008015500d002003901c0b948502d8007500d480e040090310000b9030500c078420000514500c08444031100c1301d40c60300f01044042e28010f03420084181c000c00c828041c00c0040d01c1c22240c00130002c01c5455900e00501c0d59400c8031070940074009500c9800502d0541c000d8003030380e00c240d20300d80c09149000300c5500101d8107200010400c84c0ca409050141c0044411124054103c1540902101000620340d0424003010308009001c000d001004018030000124482c082d40c80441281c2400360f25030a661500b54040c100000d04c858052001055114a090100041c4103512901d6200d80311191a480c3d04207003600c0d010070713405031964003e402090031035105003c640da0002207443c08030001301d01980014260303414080261a0200046604400101d69218140d003040292641140d641c480c041c800c0c0c079540c0144140ca11840000c580c1101200c3c142e0803190001040905880c03099454045c0074140041d03043c800d07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 89043777 1250 89042527 89042543
    0x307090c080a050412140706050103080a140903070302040908160303060f0b090d020906011101050405060403110a0209070806030102040902031008160807050405190903020f0f0c060405060a0e0a060c 87
    0x45601d02c0d40b944180c2e40155000f0f100030452282c4140103551008807040d03100310020741000020045100c1e88200740c0690300c1380c0300041d0381d40c6000000130903c0103c80e03c60005c0b400100140140d0740c0c2d001860200700d90341610003040c0314085041c0100c40703010740200d0030466244580c0c84400c06615600030740036110f8445003110301c40d48035101c2943c14081c4103061504a4060103000000d850000c0b0029480f5030b0500d001030200080b81a92800d5a00640c0c08842031741c031040502c401c043e00308a203200116611402001c01040b660001030310840080d00c0d81c7c080c400d00300d0200b015910702390119005460120001d5640c0e0406c40c0e42c001e01a030191041c0a224000d540c010213904500300003074801c45902c400142000c5003002c04000041001402d0743e61400004a9010001801e03070140700703100b0f4001d401804480c0c4c076141300d090410b0740300c515072003403a0081c460300c2d5600d507204000d0b00c09403241034403010380340c40e4400d00c1a103c8000c0e540140e644651000c07000100c90764072030741d900011849402d0f1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 89045027 1250 89043777 89043781
    0x1003110a12051510050901090b1c080403030305150303070f02011b1113150b0903190f06060b030108190c0f0305061b16080703020a080d0e01060b03010614070f020307090c08 76
    0x401e1000b0310b46001c5c1399070003070072413004100318541c1d9044204074a00003080b000700301c0c2d001034160f5103500d001c0c0780c01c4900c07844c0841d0420505406109141e0b00c94180710003801032020520000e5200d00c200d0b80c00a00c1c2c84c428121240c10740e48155840c001044402500c1403084801d401c0000003010356151092050301e42a01e44088180c2c140140941c40301c035403610842c03850406811500a8124a0724203426215608540503030010b29840c401b00707036010340030920400c01c050a1000070382e9a1504900003500701000100004000015410000c0307403440e42ca607900302c0311407a00309480009036110718030b030000440000c0b05222010410502900310307141c52040400b901004008140503181d1a0891100100322010202e0401802001254404d00c16101017060956441000382c202e5890000c0503980c0317000e20071600909208490140917000d10300d84c11580341c00c00050854008030042041e036840812124104403003501c013200c14607401429a0349042c0c41700e95010081203041c007641c0c006440500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 89046277 1250 89045027 89045041
    0x3020a06050d2c1b01080115170408030601110a0312020f0906031510030b100c06021308060106110105010503060601140d050a0516030e0d0f0e1504080708061003110a120515 76
    0x84e08442c40d010b86404070a0ba02e0b0400b00c5280c0390501d401c0100303208804481c034440c1e0908400a902c96032203400c80d6a100e09000000400c0010b4141c80c2001942c06142d00300c0109801c083d10801c18075901d180540e6610210f42d241089000d441c00d100d030041e4012090021061664011005901007500c1c103824410b20307440210180d5200c000060780040c664140100803034410855070255078000c40b0301610f0000955400140a502c45d84100740c5908008010f00c0b00552040c8003194005d400c0009028a505000000703840b100c0203400c1d24140400c0c001d0242c4a402e081003a18916180c5400400262412243d88000350004072031a00c0c0172403820702841001b60080c0718600311001407600500e080320401c08196030b1101000c0e40041401044018010503075202d0350540d20441c000304c12980c580d0f24001c40303607190000315000ba09040d00658104100c00002c0800c103800c0387c2d000800c00e1641d4040d140800c0d01c0041b69000000b103075001030460b10074403074002015140d03290201300000d0550f944070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 89047527 1250 89046277 89046313
    0x203040615030b0a0209120a050705150a0219140609010203040614130204090620040509070e06181903060912030516120b030a031106060a03020a06050d2c 68
    0x80401003043c03120b00040303081d80d502d0b5405841c403c90060928011001c103415061710300700c40352008842c540d002c00c100b840b040c100f28000c41e14074020941d44604100074a2006512034080c03d40c1e480c8050f44020780c0f4828000f0950301c1001d04a261301c203445c8503050114106010b5402160280e60590500700445540145031a40d81c1c841d0100030f50f01c1e1030301c0310781d982004060250f401c01643d809840d0f0100c10b5546100c04e407a2100c401c2c6464445540b02d29090a000240d07000a008206108500040018545030702003203886c220800808904001c0c0c00c100055113400031400400001086108088100411644152040d901072401c0030710340105180c3c1202582d8040380e6010b04508007914400205005100486460340724000200700750841d007011900c1e0010300d110580000e0351030034004440030401c1c00708540007e029101c509070b0501b1600401c0011243d44200000c00000242070f0705c208490b0f50101105040c1c1c0c0c40c0c000012000351202031614120101c00420034001d01d107806030080d41130 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 89048777 1250 89047527 89047529
    0x1f08070302100c0c05120d0201150f060513031203090201030b150f0717071a0109141305210d060b0720180f0a060e0417091201020d0203040615 63
    0x103081c03840c80301c0c080c2d80480f00710510007812600700c1c1c1450004181a51241d450b41241c1000e00002d0203401a0307450000d00b07444440d07291030b9882d00c0c1c03d0000c1c41480100815074040d12041c0c10301d295540f840001090300c1c0c024a030710142c142000c82c81d0710706916505401107280507000341e0f0b090002d05460302c10021110b0f040500550100c408029041020f0080000b4004890055130045041d6100d6415461168040c107001c42d01c1c012102e40410313100f4040c681560240c0010342d0b0800103000c0540035103400e0319002d01415040350300044000304010b010803042c14140c50030305086040e28083d11000c0c2407600404181d04c5080c3c10520007049034480001515555908480c00f014296542e035007402c0854410030542c0e40000c8140750340c0b1503903c0d1521100e80154040d81d11001e0b2854074241e150200e0b103e58118003002c24444041c400416010100c00c100140c0c02e00000d031750b400202c07000803061810900c03492115400413030041042e00d010b50285100314003e11043c0225900c000c1e04035002909 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 89050027 1250 89048777 89048779
    0x10302090601030527030c16050405011d0402010c022d010207140102061609030c060e150403080909180d05031005030c10050309030405040e011b02010b0a09090f08031f08070302 78
    0x8000140784040c1ca0140d4564105030b559056907d800c0a0908490808a24030b26041c25500503100030042420144540d80c014409280403043c400000354465107206009480a41002010240d000955990b0481c0549000c1881c00196004104500102040e0301d800b05980c05800b406100141e42490f1694511600405034003804181d590215039480102d0ba900250003084031800f4088001030b2101c0080020382400c0d02d400007615a8102003014612001d00d4400da204414401040050710403000d56240e5541194805410740d141040d8015014429a9508981c41102c5080000941040065001e092030b140c0303e803501a110806d02d5a9501015851904a588813000d102d40034481c0c00a181c1052030001903030318060f510740000e015507851540d1007580ea59a1440042400441009a4940d40c41e5000900c903a032024400985079040c18813410048940780c5954008002e101103000440c1c6900070340c4141c9909020107180c03509900c200c1009014489060049901d120001d440002c4a034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 89051277 1250 89050027 89050051
    0x2060403031b0207051519020f070807050d020f130f0b01030509010c020601050108100f0306020a0f080123031906020703020706090b04090b040e101a01080402180603030c0102040e0103020906010305 87
    0x40b4103014460301aa046c001c1780020349050007200325038141407844140e0904a0b9008082580402e1203282c2448541d610542050340032400410036500e80c9680c0c0d083c0130303404507649441c01054030b02194522a00c000752901e500d180c03080840c00314500754000700e5400310030381c1c04000c00e5442e60080c50803100c00290500160f4003a0340104503561142c161035901c0400c082404000f81d5580c13a0013105000f498001b00c466640204024005952110f8100c1180c00249045513155240218040c5500c109594400f04140c010780800c200c1d481c1082407866821000380b4110709400c0328140800207400c2414218014010780d0800280d643c4500f40d5901a9a118090a841d2501d13140000c002080510101e42d0440e0312206d4180d1b1043d020b04c0304442801c00208042064524050cc1001d41c9042081480c180321000040c400980c4404001da080018601e01041c5503480d590300080c910b01512070000c83d10f41c00002c011842032015881d480c100d900c20f80e00d00c400380c2c8a240040d010342d41d085130f1000c4000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 89052527 1250 89051277 89051279
    0x3110906040506070f170418140601030b180c0306100215060405040c03080a020708060c04180c0201061e0806060402031303030b010509060403030504140604030807060f180302060403031b0207 84
    0x3c94910020f041d480d1150303141c0341c425103440c0c0e20015620000ca6504401e80c8010800b007281d50301501202c6407111080b04108414660146a03481d020005020705d410950780301e88104580d100c8d0021409500196900c140f202e29000c4401304007a0f00441c0c50074000c032200184064881c1c0005000c00414480351218801030340c44009220003020300038002d13a4150241080080868200401451030441c41d5000e4482d01e820720001314502940a001142c21050801003044800c9180c41c5000000711095030201c0c1100e002039007203026144130303041806100c10076030140703102c2000c811034503080300c09400a8a569960b45d03c01c100c100d01007143c19102c07080510044a002910030b9001c0300075044141041401c110301c41010540a0b00710b50400ca003c900005000c0c07108251040044600d0102280c019282c1403d655900c030302c0d80a1002c00511081c1ca030010036011000c1600f2040801500100801c0d4552040c10000c0d81c40c8000e540c1600402c3c41c0042582c00120400031801311818160000d200d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 89053777 1250 89052527 89052529
    0x6150c02090114060d050a0243080f0316020d0206070c12092102120d090b03131203050a150821190206010f0803120705160b01080d031109060405 64
    0x1144074a03c2c01c560010080200d200070134010b200f10340c042c915800e0010780b038071a03510062080c0312030b551841d8100500c281c150368502c0d00d4280151340721080c0000200c00d01d541ca00d099000c90080d1540d5046080d000300c2000520301e4680038101107c0c04950840750803a20300c03403003070b03807614001e9521100041500d50040085200a08a140780031007929245c0756940d6a20f41c03000f05c3e400403541107602107038240b0001041d484c00c545250000d1030440003824145440e5070300a8002c402034402c0f01c003000c4003c00003d81c4050850b10925456800030004850a5400740004008001c200c60703601740945010425003e0a499000c49402d035600c0000a04c40c188000c1192000d2040038414121740301010401c90804684c40091f082c1211a02c0d0010001e550403d0030708181310290b078001d40305030341c410301c1500528a4030b0703a002d0b904400d66042003990b44070f1040072010f01088000014103803203d2480002107014000504c04e202d580c1c1079034100940c810442c500000761086211541c1c0c4514144414042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 89055027 1250 89053777 89053799
    0x50d030e01050c011103060f0109080d0f0c0b09060a050112121107030f0515060108040b0a05042a05010f02070e060906190b030f060a12030f0207081006150c020901 72
    0x100c603814103002c0c1c200f0140d10105400c0d6503544804200c841008800e00c901c9003000741d0350b106050b80034284081c3c0c440c01c0c540110b1755449581801410010100b98001c103880c05000c001444641114411515107805a400341d650035042ea11803121514107000022148042d0f040c856995500c510061192405650704a80c4c0e1401e1004141060242e818000f001902404c2d50340681d030301c180090400076180702c1c200e401d0201e00600090512211404000010713140c052180c2c0c1c0105542030000d174a4950382041e200852543c0000000d41c9013888003940508840225001110800d03690914010b0504004980f0341419100710500910080003003625131820074801903001e40f01800b114028500038034409060b030096440749208000000a0111048405940c20350160080c0d451070b061624000009405a40f160005001c112035400780e003004502c2441240010200ba40489050791085104500204114411400721403541084550301c18061440c0c00c0c0c1c01500144504642d80c03030310b400601 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 89056277 1250 89055027 89055047
    0x3020907031d0f0c040e0d0801030f030201021c020c01050c160b06150f18010519030e0c040c0917010501061b08040b030f07121b050703030204120b1b04050d03 70
    0x3020030403030004011031681005000d04695500b001801084a84c2d03061204aa1004210500c503400c00a07140c1c00310394000300002c1c1180d0340404690542c00050404a0080c040c1d0240c021030800918002030810704c2d640c02504011240c1c1001300681d44622a800446202d01c88807980000c5c8000071013004580710744c002c1c03540071001615400c200300701c0d116002d089074464800e28120200125030f81e043c20a8180c46040b20300703000c1c2001807802e20980080c0f0001b070104941c010404d03403282a01c1d0440d00302400100b0148030043c00a10112040c054090151800b03401100454081215588105141405071354100e4a8a403a0000d441003601c940b4003980014100540e429039041200203145007080e4002c0d4480c0c0210180a80c41e1705000303074018a403140c0f070000c0c3d01840341464104141804c007404204940c003120309110340c1e10724031840d094020f802564031040b5111040aa440248041060014841c83e544030351101c80c201c591440c40500e000d603024013030b0030010030040d16000030b00444c0303000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 89057527 1250 89056277 89056301
    0x20d0807120617030c1501030c14060706050103051b0402070c210b01092a09050603061207090f0b061806030601030905160303020c01030b060306091824060108010302090703 76
    0x2c64295107070000400085400e01032080c1581c80014070802c110400d002c10103000001020030103095155443c2c45540840c0d50003160b59a030300c5401000c8040c1e0b00c000807604915848201403242e9a52400e0007601c0740c0780c6106040c0300789080d0f0000d05541c602031007182c2c40c040c4e00c030141000d281d007030524425202e10010744c10300d841180d10308100041610112124000c00003c000400e01e5120810800c00c10410000119540d6030005d111000c0d44d07411196076421780394182d5000b6140e070785620009915001440070304c0c1003400303402c0c0c020a02d0b41c0c1c80e400c644101010307803005108010034401404130300d00c0b91031042d00c040315104040841c1407400100650b006841458040760100551b280d5505007500c0038000d6070842c00e00744040003010340502110705040000d00b000c004c0e9240c1800440c1c9070b8031008010611275164140011204003205440903108000401180d80446441c40c1035589000001040e04a5111000008001e0f62081c0c00c9c1c00d040c0d990280550502d611881e80943c05403100003585 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 89058777 1250 89057527 89057531
    0x9090e0a0213090507050108061e0415030609050606090f1b0f0c010e0709062601020d0c05040e0109020f040504020a0c02030609151e0403120902150301090507020d080712 75
    0x50141c0d8900280900402c0d0886000a90040a29010707203003040e83c4e44002c1c113006002080003c0c0d96908580c400c5a035050310010500d441c40e490024008001c4240d40200c850005d41020003030014035444000d841d441a0100c030300c941c8424041004000c0d0850358220791800010006800403500d4803501c005074001513110781860307440610f42115400000820507a40c5d0354180c1e108a103601004103c00416600004004241c142488103500c542801c524850380b101c9031151442c128000d41c110780070030011000030002c000120070001e00382d41c01032141156510101c40042480680351080718044a6044e2140340b401e0719150502000e90045110402071240744c860301d00c007603241809000d200d031032903802515103900440d14050f40e010000d0450b102600d000e2440caa82000d80008494005405081040350701c0301041c1903401034802c51600a4000c0e0310180c0411089103003c01850580341c0c041c400b4420395983c034404a954240424840000840b0b00380461039485c080c0c0f001ca04402c0b510640 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 89060027 1250 89058777 89058793
    0x60603060207120f0f021b010e030106030b0f010b040501050d1107060606081b040e0103033507030e010504050a150905010911040c090b070b1509040f021002010b0109090e 75
    0x1180102e0300044426200d021040344505102a4014003681440b41141007040071a03c1d43c2e00021755030a500003540081d043c1035030403031034aa8020300c0303a0315481c58000d000b0f11142c0c0e100c0c40d040c4011001904c038035880c0c11203040003180c0700a640c005e4400b40c80060755410700301031000000348064500040c40c0c0c058001e04001140200340e650180101804040c2c44500660420804500c502030210b110001c00c90011b0006200318020062261b044a07010301c1c043c20784900c070400c21000040b2170a4000c002d1500074159020b0400040f03601032040f0001e8904129500c1c41d145001e09a070340c11540103003d03400890302140050b031102d0703102c0300c41c19103d400040d00903d00ea42c0c25084440901064035504c035500c9003003d4520305801380000f1000c00e850a01826441c141503c8600c1c000c0d088000e242202190000380300c52075414020340b92400091100a982c240780c05c010014034062881030740650310810003500041d005004030010003038107968102d0074a01e0301001f8801480c01c038000780001d0040d004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 89061277 1250 89060027 89060033
    0x50c19050d180c08060705071a07112b0306030b0a090c0f030b01090513020108070c030c0c031202070602010b0d1407121505060d030503150a150f02010e0a0203030412060603 76
    0x1d03031615043c828003a0662840c00c09020914200c0014601000c000b402c00450740014980c0700d40c981e0320f1350490425095915040400d0b503101b40c4650400119204401d50050303120611010158440c00f000c804140751910040b0803016140c90707010150802d003c0b1000b0031035110040c0e01c40c030b696500074a00c0d861440d44030300c1340c804200c0d020b600a464124040300188104070391403140703603001507445a40301740103c02640064041d143c003d0107002032014140140c81030500403884888000d0b0300c800c08008507030b00d07880c005001612440c8104014842c4840100321180144107414200900410800000300c0664554001941c6a810071041c5c1c000c00c1c0e40041d03a03184a0600c136845d64440c50301c4010110245451404503a40103105511030402850b501001c0381e0804101d03504a111001d0480410b03104001042076504240c1c0010700b081201d084000000d5804564919070701c210f94002e01000404c110650759a5011000103503050300f0810041045250a03081c203000701d4400d02c030105640c5d0f680c0d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 89062527 1250 89061277 89061311
    0x180302030f0106060915020c01080a0e030f04030b060102010504050c210106060302090114030f040f1b031113060e010e040c080f0a02040509190b0709120c030501050c19050d 76
    0x102100702030380d100d00c0180f184a13040300317041c0c028002c03595280543c01810301000750f4940c40303c05101c1c140000e00010603021000f5400004800000c8006c813580c98160000129403035000d44004d90741120a04045030b030a40c411b00400d0300854100d401408801012410482210400071868030000c0b0008400c0006200030301a510082c450794500580b2400032030005070207100400305891844d882007041101c03092152000da03070000e4009081c40c1c49458640360410050b00b0a07001c100003000303141d40c004204201300c541e00c944920183c5110300c10b000d10304420f409640143c001d01480701085001403100040300046550720502824680c09807507174038280641003148200c460900f9070000c0b0100320a500f054003850b0b4115820700d00404010b5450350300740565490001008103200c600381c000c1030f0310340c5c481c8064402408840c43d10161411603841d044000f00700c1c0c4d100842d80d0b9400c0000003108041c144003924148100e40482c2c0d9518001500122069030100d0514021140d0743d030b0312000360720000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 89063777 1250 89062527 89062543
    0x61303060615080f0c0304080d0203190f0e03030a0c02010209120706090605030f04150204050a0f03170406020d03200304060203090c19050105070206090d260306010f18030203 77
    0x14080000c401e07080c481c21058800641c0c652106002d003c83c00d100420941280307056000414042042e120f455901d081200e521800c01c0221400b030011061104015021b03032041d13820061044104002000704c0300d08010b80e00105241030b401c0d001030000a00c0850142c110415020244c8001440c04107035500181e04c101400c0d074210080c4c1c0c0414420b0140c2c9800c25081ca0150450b42080c500f14540009900410000100700800004a00c0e80d074000191441d01960041c00b070007400028666158000709a200d04203200644142070540b00c01c150794104003003103c00b42c62099000d88890880c5602c00d4000c2e11701c0b40c0c42040d05044100e072030305060b2252009103000d0303403151b8005643d03400d00d44682441d01070300203034981c840e4080050021f0200e4450049130708449003800d00356250206400080e40a0103000d03a0315410510254004007001400c06014a00c407810350405512214842440e080c103000c200c0b201400b066504070784109181c0152038091064014006100d05c0948960200b030510b024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 89065027 1250 89063777 89063783
    0x130c080d080c0310050f0a03080307020a050106050604060237030309050c040b030606010c1e0305070c120f0807050102190f0219020303070b060a090623060c120306061303 75
    0x10480940000390352181140b030708605020b964605600f400b40c0b210041450380d2217418030a42c00d0010407503150721000030070002035030082c2c8601c0d140c3c074103001d01a403140c149140440d0a03502c0c140c804039032450000252010b507515a8020f002900e9040344207a90310040c001000a8005c2580c0403444038801013022846440c401c1d036010480000c070b450010b14184c11400b000340720764100111280161400900c0c81e50080c0309103084e00002116003804410812101083d03c00044820540e405154000c402803044901c40d0b1500408681e07204101c45050261580041102d1640001d0102041c108005041c52a014400051620940c4d80e10764099002814603e004556250044125207805102035941140f040d007544800b41d4095000a880c0e00c611500109501040342c0860043d0f2654410f0101515007400104001501c0f460407100880c500400c40205400c10f4042820b00e040070b80648500d41440e4005001b0200ea00041080c281c10043c60301e034010320248800285044036074085001540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 89066277 1250 89065027 89065033
    0x90506030a05101a12060411120a0b160f0c06021b03030703050604050603030f0f03040314040608010f061b0f1e06051e0709030308061504060e0f150901030203130c08 73
    0xc410b0902d42c907013504500b034860506001403143c4208085070840c2e00c1a03110820300c41000c200000034140b6441840c284440c3c1c80b4481c00d031000c21841c07400f1503018070300d002030304240b030b81c504034044035040c800c0c00e2044000b446007404d2500051143c0c015040783c045006040e04c032000409080703440c540040740c00d44006501c400034414941402d110301d40e04070a058004e58070386022409080001c0c0b00d46000340e86030341c1c0000002418540304d0b00c1000c4421098420540d03650340e80310070040c4550402e02807280c280300503d00c00944680280b410b219050360b032090394982c1d0281a00c9190780303070281c080141d40e6000e803100c2055001c03607541c602a847c184190710000300c9084c07055452034038a0382c140304525021001802d0100c0c2035000342d40d24003240d03410700d0218000c0d43c0d1a4040360b02c4032025000707183d801d00c0210300031600030741207140540303092410b40d141070b5029030303540030040b41503040032403001c03111400c0282c2c0a265100f81c00a561040307042d1504184400079995485440d88240d1001c040c40e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 89067527 1250 89066277 89066291
    0x90b2116090e0106090b090a0f0305031804090c090903121104090f021e0a02010b0303070605041b0b180105040f090516050403080910030f1b0e03070807090506030a0510 74
    0x5800100c0700c40501080c02c40c00b0541c3d030500300060905030960180c1c0034413540115140140d03565002a09003d003c4e414001e80780965240307881581da800c410000400d0321601035191800342024450358904540168402d400d0710f02d030061401c001d0991300419001c2101c62018045044050f0146040c07009051b141d559a0b64039000030841152035071120000594010010035551011003101524403114401e1007581d52815142c00345d0040c20704140380754240c040413664009100301c550040b0702c42c5019100914400144040f00300d928965030250600701401488000440e0000d10001c0e92841010f041040c50b003601c413030f00e001c003000c80799100005081d00c5904210300c14010341082d0030400301c41d052440c140380c1181d5800300f45000d010982c034041c480205401c00180c3c425000100b0400a10008014103840c40180903408556202c0d4103000c9100340841e860141400203050b0101c803c0741e0040c015290030842288042d04000e450240d06215844100300810402e0203060080301c0303004070005010b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 89068777 1250 89067527 89067571
    0x3030207170601150e0109030501050f18030a020604060e01060515070c0b0c0c06032706010501020d0e090a0504050a0c0b040819020906040b040e01060e0604050f0106090b21 76
    0x1d4035102120541c1d411a000400440070700341414000120b06080000082e500140102c54102e41d0780e01c041c0c407540c2800c042c84202d205214000c1c0c020003000c0c004080110400100030740c2c0c0d214941b500c00060f4449800100400c0d02c0e540030361070f0460b9040000c2620b550351800645484104810144080000a07410b410001b2030740e0080010917a8480d0582030086000c80703980c0b0380354040021400b59000000091940e03501c0001009005480c920750a400d070403820a80351342d05401d0040d240503200ba004041070f541d0041010700d900c00700052240351507556614121000d03240240007180d05202d03056001c400240010100b0000c5c140e00d4810b03c0c0c443c0d2508405070b14052110351201201d8088050f0b807000340e16040005540722500740c4000c100c244aa5010600418a0030202d2040b9403901401050550840c0156809944110b906000d80c0d00c403900e20304075184080c4504408503103810000c010701c151003800341020403480c101c0c0942c0d18219018185200720112a60111442c0a920b12011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 89070027 1250 89068777 89068799
    0x4090302060f0a0905070e0901061a07060b091b1b0d0c05010507080f0718031236050108180613120801140103110c01090c0e0f06060702010507060b0a03030207 70
    0x10240c0720007010310543c0d134541c440585900d9035028207002c00000e000000c900d0b0a007500210014a40d03001050031507400c41d2100d0140d50080f007421111181041104580c41c502840928061054102c89900c00c0b031700300b2071684066209400510b1903c0b0448882450581c043c01014030700c003507549601c86d4a0301c0c1c0d458038608603600201182d080c0010081845480000c8405881e480a00e5007844c2c80800f0000582c1c40d600d03403a907440141360304403030750b12180c1281d40062110049904c02c0280402e607110403048071000490850513207c2100c1d504400c006661188210f69000707a009402c400c241003454500504260381100d000d114030901c0c207040c03020410f41e01a0007545000b0f0385410b003d41e5062250003200d24200707824541c10113071904c0c601100c001c0071008075108041040020000c444c820f103041c0d02c18403801d1280d4111041c00c0000280344409500080340b01e410f0080c8050301e002800d50042d9040d410038003050b00c006668001c40c0d0b11549504000601650298004103074091400c400c01c48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 89071277 1250 89070027 89070031
    0x903060a05040506062e050a090f03020303090f220b1507030905040e1515010e0607031b0305040b030906010509160819021207050a02010b0d02030a02010c1104090302060f 75
    0x81203501e00010840840c001040c21508514101c510034182008615244950b40500420307a10200e40c40250701000d98000008021040341038035110030b200d0313032040c100a103801d0728403002e0f405410070404102a0300d06401c0540802400400329508074142c820304c05400ca030303902d248071a455a160008400c81ca480030300c5521408099a41c285040c03042e90340104410071511506008a031548250411100140b20080c0c40a20040042c0014600500044102c44011000c1d501145011a44200c41d040c07501c200c0c0d201e07a8050710380201c0104281e85805210444540c1a41000028072010482da900c40300118011000d8000415095042200b08903100c0000f808010511507104c40e890b10030380e0080101c80d40301c01100840e1032040c06071140c07180648100280142c403001c04c00300304114141c200b4007901c007030725480d8020083e5a60880c00c1c002620708541003c0d52550100510400542c45200e55800140c03065048205890103d0049410344821200c00c602682006040010405010a2480d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 89072527 1250 89071277 89071291
    0x70203010605040b011d01030b1003050a050705040e0708060a0f030305030402040c0504050d0807022e08010603060e010b0a030f05101d060607030c0c05090708040b0a05071d0a05090408090306 84
    0x724084013440040d01920002c00311804e0180c800113196140d07170090317009904c030b0140a404151014030580b00100140701c00c81e1260340941c42d11340403814251160043e44d0a941c81c14560741c0c501d488071a03040e03a075044001c020076030064070b032a000302d02e5020f2007413244000c1d0f109844040d16070801d44100010745026800c0302c000c009060204000a0f500c2020007104290429407540d505c0325240003040c0204400000c40d04001001403900e024201004600450103403607a881c0c1c441640c860320100c0c00d40d0118071401540c1030340507005100300b111600c000d0003651040d090000f02044205000c5045c1c41044a0466502003401c0040058a0385484a445c48440d1060480c900340703000400156270f401030312005001c200d80710b1f000500300081681c0b00c01c0500f00080c505d407075619049000610043c03044030300302c605909141c08075071482d03d00e0299501a00d49a103030210030040c952031101011550000b010744c0603e0002c4000307140e469400c445405980588040c9a82c2c0c0f0100301454941136000d4404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 89073777 1250 89072527 89072531
    0x9061e131406040911040903050d0e0a05070819060b01050d0c0207060e01031b0c08040e040c0311060306030d0e01020114160216080d05030c1b06040606120c030807170403030507020301060504 84
    0xf00c0c00074203007040c1c400d4100003c80e40007c00c0c038102e040c1150300b4000c400d9150030880c43d1100c040c0007000001003881c1030070b1080c41100d103826140d2110a0311070f042d07026811701c0d000301205c0030400030300180c03c070202c1814180b42041c1010340252403401500c08013588240940c010003018001c5560014004a00f5002030130140044840b04400107544107243e2402e004024150b41c0c181d00f008011002c031001442c140030b25600d20704250402d14a032814611044074440e5503e800111981814002d891061070000c0250042c13a881d00000c1e10007082110102e81155a60a007007499507090302d8019000311aa0408041001940c0e8006072400340486000c1742d8070b1751a040c0800402000055501e001049854515105cae200c1013031088aa00801040441c44001005002041940016a54400c5000d2a020b0000698480c41454a50100000601a17400501303007400407900220080038414400c200340040d102c3d28210780b010940190708210b000950004405003549000d00501000d81030403141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 89075027 1250 89073777 89073791
    0x6040614030304090506030307020d06060905011703120403030e0a030e03070e0c0d0b0105040504020406030207021801080705060304050708010e030c01050a05390d02040f0b04030209061e13140604 86
    0x82c0c0d64081d03446410f01864035080000d619450620656265a9010b01240c03112041c03841c0440181c5030900503e4400c070b00c0c05000140c00039942c0102d0681c13000c14400f45140c8141070210300805034000300142d00703043d250a20000222020094841420b0007583d4809510080208040c20681d007035000620210315003080c401c1c402e0380b2600300d40c03040740740c000700103100c5902c5401a00e45010f95400158498408a030000301c1c282c1580040901910071030302c0d0701e004030a10f406064803036401c0c0940880c65201032001e1140d420180000c58010340500110b424880d5a00205801d41303010f030303c00391016040030442d00300008090081a070481007012050101d07140c40440d00d884100c0c44e6400f040480114a9094000e051940c008101c0034182800079903100c0701000c00303c3c081e602c039215030130070302560070700024445c0e201394103a41c25258010450012600c1c0e22042100600040c0003140a2008441421502d03948045141c0300c4001100d0b0040f8804880c14208591060020a502d0066040c010b0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 89076277 1250 89075027 89075029
    0x1b0b0f0d05010e040203070608070c05030427090b1504021b030c061602060c070311011d0c12030409050405070b0304030f080a0902010f050d020f0d0b09012102130b0301020a0806040614 81
    0x1c0c070354191b508e18a41034819560300340d82291843e403890b0000d4120300000038040744258603c0f03444105540c0221400060078a402000070031250b01a0000e0241c00e01100801e60380741d0848044003185900420260500c0c4c80a80003421403001c0004500480d80002041e0500b660144001c0da84a0b2186107841803841805501945441008203100d12184000502d0400c141c021103c554000c0c180754000c1060343c400c682640d100580c2c01200b076009208800c01d0180900d0301e00e80841c01d5644000c05141440c0c60000d2040241c034000c0d10445950042440105400b004040903611550003031341c801100001c608405400340101034040307000982440e09000150341c002162044074509032415035502c04041c40350900034001c541110084041c0010040004a102c0d00003454484084850041990741c40180204814100d0b03039007604406440402000742c43c254445071500c104421000c2a46401c000c0001e007268042d084480c00300f2942c800b44043da06280c81244080c0542040182452a40f00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 89077527 1250 89076277 89076283
    0x4150b04030b061f0f1e02060103032318011b0303020301050a0923090316030e21060a0e03040308030103060509010b0f01050f21040c08010e07121b0b0f0d05010e040203 74
    0x2081131020701c28035040c90b00001d4880c5242825100d05041e040140682c0d8890003034480c2d00038442038001801d017a03007205003082d080806940c0e084101899510704124036050a160000c8038484506020084910248900300d090691103502d100f581c0c0183c0d02e604120030801d856403030b9086403807002c0c60115101d0720741a08803402c24880d044076440b004196201c07803a0614610030b003603544590400707500d0b00e01d0030160003203546c903e076000c1142c0b0a4603200d400058648080140d400c2c0c8240c030f50000002c103911860a6010048034201c003002e0300d1801340c407512a01aa40d20a0340304850943c0c0d2081040341c080d400784289039151f00c084070140c174016030b5600020011b0040c10200f81d8200b1000a400390380719040c100244407185e40090410440c509418a42e594801c41d12801c6440e5080a984032002000858050b05840e94070558420b9801c903500e81c1c14030404040100300301a05483c0d004034030240c3d90340281085550f91444640c0c0c500c0815075000907914180d00410195408405002c01030b5404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 89078777 1250 89077527 89077579
    0x60f060c11030d1d040203040201090b031009020f09011b030212090d050703060903170408120411030a080904060801060506090909191101080c0319020904150b04030b06 74
    0x286803444104900d800c06040d1800001091940340c0720b501500708400341c121641c3c4200300140c280c0300710001034900a00c01030707210440b00240001e0450f8818400f18682ca80a1034004400301c000f84100c03901d170511281241d005455844407810702003006000341da4003000c0c2c400741e0000c4240703003140305c05981c0e000703176a540c0c801030814000b45000c1042225910780000e400b5601d50051f044a80240e500d0500300020104400160005000c1d034030680010041190103c0c000c541c816a21440c00d500c0c19031007a944580684100c0741000301c1a0161003603a010421044500d0141c60a6076642103e041080129041640050301990400d841009942d0700d001c03c0e0380c00b0180075156540150f4402d882c440c140804110382055080758514008180004010030f01e1406c0c200b0780742d00c020340c1c44162401700c49000440d100c039440d00740c04d15120b0310607200350060301e40b480f005080410501c01401c8800d1611550342c00c91b00c140b0201041c104148507038240301d5500407400707540d104880072840415030b9030982c031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 89080027 1250 89078777 89078789
    0xd0905060904180b0618070e01050a05070605070807260103060c020c030706050405090c0403050c010f0e100302030411040e210f04080c100201021801140d0e03030108060a060f 77
    0x40496000140d88440d00000c85212a40700f502510b126149004030b0720520a0304c0150103844008001d21400549150590261100341c035007842c03407002e040c01101d413640213086078410400140300d04e00002d502402102c0c056180e58542002500e00280d005090840030000c0c1c0b009900740001091480001c94009070640e40c001d071001c43c414800358016845c0a01001d0150742520440c50001003890b400f50240080c0c5104480030030721601c5582c1301d5031440c016804013400540141141d403200d58019180e00c07090310708038100b038181c10841c840001c041003e08150000420740004c1044100000701040d0000d000c02200e0410100c90204a0f86940c1c800a0740e060220665500000600d00614070544101c55400c42d00300369510748846081d0785500f4036030303540c5d401541c1d00303a1a41c02c1603006000390b649229083d00c40c80c042c010540011100d9403030f4400b40c00c403400020040c8c501000d095024100702c1d419030100642e52545081d469915003200244031454031468000140301c484c00f400c494004070382d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 89081277 1250 89080027 89080039
    0xd080901052715010e010f050105030105010f0302090a030203070627030807020904050c0301020a050408010b0d02130906020d022206050c06010605030601030b130b0f01050909010b0304080f180f030d0905 89
    0x10100e4607500e4542107000c3d00b180000c41c8800050a42c18000b0030505860b84c0c0c580000c0425590401590180800c0c0030721400720303040780e0301300e5107641c4207902a103210000200380000d01070341d98020034148090f541008001564000c2d01e41c010601c04144884000420140e85000360301d9034958864500940b40c00a1040610b20003042c02c0c01010030103545000700040c000c665490440d00c2c007810540c031a02c101101075003071504545492510070450342d550b03a00580803072041c0109650702d070018000a1011112a41d0030b101c0d80c2d400e01854070103800c030086c0c281e00e01c8008a00300641b80c3c14070501544400100802080b101ca4018400303d02a0b044410340d003030450301ca44a40700181c01170030798039a02ca0340090001d0bd649000d01031036001410f0f4001c00b0b60300d01c1c00700403a4200464191240b801140e41009214004005420040d401190703c41e02801409042003004880059203a0200d0040703030b003040405402e803c10340b90442d0a072081c0e0104500500b6055003a50010307151500d03601c03a252050f1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 89082527 1250 89081277 89081341
    0x10306082d100c0801050a0603050702070504180c120605240108060d12030507030e0a050c09070212040909020a1d06090621060108070f050108160302070b01080d08090105 75
    0x44000c00c02d4804406550109010310381d542400100101001d01c59a442850340120014029010340704080c000c000e20350151490904003400d12028140050340d2002c1d0380350240302034001c144031281c1d42001e44444201904014640d00b014402e8130300c040e040095100c0c00000003800060395502a40781c1040c20700303002d046951041c0004d84460500740f8064802080303940d00b81c9840e43e243e44000c0c03160386d4a4804200411884100715990018004020b01035800b40100c5074081c9002c0030001c4d48000e8030301c11a501c07400e10000f264115001030f40f281c60344540f1f4442c01c1003180750441c0414090302c07200c98003c5040d00e441141c60400c460180919020700e03640d030003080180e15101c011085032104080480e07a00c0485c0c940d0269102004d20500300180a10031b0046000d4107216a440c0864105942e00d090a03214404a1070705c1003403142c0182c0605600f00b01d203000240d507002c0528002c046a84c0500b800c400803000107441c41400400c9204a13901d0300041116000c084c0c4888440c444000792048012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 89083777 1250 89082527 89082613
    0x7030f02030a0605070804020405160203160c050301090309030507050306151e060307020d090b07080f18040906060302090a05010f1a1612020d0c030e0111100606050901030608 77
    0x90754003d8041d508003005c02c80c24503000100d05000c1d510945d8200001d640c2c0c40300188418084030200701c0141c00400003600b1040c0c11501c01d00d103282c01a90030307225040e65480082e084be44075a0003100898407000c420014003000780150401001d054000c1c180340e1070f00703032800c442d11014083c0b03003841002004502c000c0000d075148a8000044068040d5a41f4100303000042d50700c000c8002d16500141046a001c550034540505075400e01f036101c8816404c052200601714040d40100314440c0b05115580d0f4443da25503164014ad040c900d018100c000b440c28198014000d1003000100ad98142c1b42c24000100b000c004800981011200ca010303690b07040c1346030340e01c008a65110310b1003c1e42180800c14581c1d420b100c01c601c0300c01e00c06240b075022217046800340002502c164100c844080c000c03c40e03440303030159194090781d2101e20868402060342c070805d2000442104075007072608240001000803940c0101543c0500c286405440d00c10000e202d00000b00302803d0311045e9661845030341d01c03800e10810030351b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 89085027 1250 89083777 89083783
    0x114120a0b1605130b0f160b0105040f180803041a0c070c06020606010e010f050409050108030c0d0216050d030c02030a03021b06120103060c090e040305270d11010224061005030907030f0203 83
    0x1400380030341d003031f403503207609410400c1d203444089c09450300c100c0c035140a10b45020540c0c03040c000040e56044104580c0000c9444261081d08000c00907603411221100d80c2d00035014a10701c0502c0f40c15041d0714240c440040f42001c8800c414260007200c155408507083c0281a038100f40c05000d0b40340309290054a004a8010489041c0141d034003840c1003504080c008584030344040044c2400d040c04a0803104c440040800490f59100440030100c040000e12500b440b50f410054407000c1420b001c1d00700140c41d4102580481d04e030041ca001c0c2540144c0040c4100c030b081052440e8241c0c6002c808944c21406d100000170b10600d2500e06120041001d0341e90b010400001d4003a010020042110b100707e64100d01c0d01d400d001c0c020354001a449070040c480c04040003000f0440802c641000034014104000150059480c5000352201020305815840b403a00b0b840c108240c900a403071360518110890316801e0500c0760901408001c0b503104c004c02c1c004244200700b41030000040803002c0b66001100c6549810040c00401d003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 89086277 1250 89085027 89085037
    0x31e010209120304140f0d0b07020102120708040b0709180f1d150a180b130b0a0b09090a1a04030c0204020a03020711040c080114120a0b1605130b0f 65
    0x341100700c440c07804012100100151044542c0d400120207102170090800c1043d403016400981d1004015112501141042c2080c0c0c1d0301200a0000610b0b0540042c80c4461503101180c0300000101958100010070408500d600e80000d042d00380306404c00e0030300211301084003000e13070303810300565441c00800d07000035440d080510f4400c4103d14071416011240702c0b50b52140c04c9030740c00070140012040851003211152044130755804850003032124008060b41c4100e00e400c009403800751480c07040c408042c00328452110380380c000e040100c030010304054600103000d581a001402d0080300e03001088030750046060700e508140750701895410061907641e1481d041d60048548140030f9009407004c225140d103542c166000705205070084580009943c0003408020640d1080a00748000542c014010050b0032840003e4042ea000002e2003d0314520316208802d1400e06c500c0c005507000040344092142d28044c2184580d0644107926002d480c0003c0004040c143c98054840c0010709200084c0031508a009041954 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 89087527 1250 89086277 89086279
    0xc0813030207030c0909210909020f1c0e010b030a0203100c110a06020901080c07050718090203030d060611240402040207060e010e01060f180e0309120a150605031e010209 75
    0x181400e8443d54000014180f01030106c0e80c4480380c48050145801036914407a0b07c00fa42d54a865409003480c4036100a1340140d4880e031202102030055440580005d140c0060040c410340d40011200300c0e0442d020709440840545900035000041c00ca8050f07100480c400f603001da80c1c42c502065083c0740c034004490355056000c2d0000b6a00134014403004000c0150014204080c00b66204100e43d2944c48040c0d1940c455440014445e91011104000c15061410001105482901c002414900c260040703030955004151416115564400c28801550402c204031400249080149130b01c10401e000082c0f41101400c50301c102804003000038046507620b404070b51503a54002028000c0012400680380a007401040c2e0343d8942d400c003000400d0754482d8584540850b4402240181c0c645507c1d000407004101e00740022040b8001013099403410b0b1540075184c024189004001c210902c81401d000d60340640100d50b00d81068141f070020002564001801c00c42ca04040c40050820000340307480c0e03402441800300c0a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 89088777 1250 89087527 89087543
    0x305120405061506030906190b040e060402131806020d091e1208070504051908030316090e01050121060305120d0f05010e1b04260c040c081303020703 66
    0x80304115001c1001e80c09051500240f00c244a090010412540022184511603902810000b4142e00010103180a40c5010010000d04885180045001d90341c400610040c1c076031200c1d0501003181082019003294058600041207521540702d101540d402003142c0241c013407030f00851b010b0703441581a40103480071603010001a80c0080e8411511880045940003070300d0b41c44041142030b81d82405096110702c10b552076a2258a068240342c1000701c0702220003c83e400c00b40041f00c001c240181d007080203601414000000b81101000e5550040c03008442d600a8840d00c0203410040281340d8011603844111909084c0c0031613402800140b01c80105526440500148940b9039084102ca00500042503500781554044c000d0300c05052018050b51028414603086403040c1d0005040c0c41000c4004040072075882ea4005d25050b40c0f032400d841c007481105000760000f58280400c0858220401038182e5501d81036400340220310700c204010317110560051000700f5001148910804141c428031290003e5548110780e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 89090027 1250 89088777 89088781
    0x5030a08070f051609050f0a11041e0314010b090a06050a030b061810170c03060606030603030f030c090406050418030809010906020403050c09010f1401210c020a0b0c0702010801030807030512 84
    0x303980c05441c00399031407242202c441020520003208c2c2c1c011b042c400302c41c04240c14541071900c402c04140c0d058918040080b40780813040400000c4800c4040801040301c4400030642c8080310040107064076026042d06030340751030070701c08100b540c590003076490449c0d800110001e00c0f0f954440200760230070040c154a60030001e0720b03001c101d03810084800c0401505c54440d0300003250140068007950319200192500c1d45a8425000104186003407001582d0008018041d00d0030551001020700030f03600b050360102000c0001081610300c0381824420f5000a05040310244030401d4041d100420414084801504000b1490005040c0030b0094224084461707101d40f003159510355908103e40ca44a84a21044c402c50034100001844081d619141d026203040c103004e41414082c982c01507a0094216036090442d080d03000b258405250b6602ca0a000b80b00c040d0041d24bc01c58240c42d240000303602c02008980804014090240582d91102000b41582c1c1c1c05108079551b00500d040c282c0d078900414600364003c1c42c072041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 89091277 1250 89090027 89090039
    0x6090f0c12020f160303021c060312032d110d0902090109150b03060a0e0906040210020d09031509060213030c0e0402090a0b0a08120403050705030a08070f0516 70
    0x40903100c1084940d4608400108400d00001030f0320816425100c030420034003c1440c8000001052200140f01742001403800c0b50100c0001c0880c1e000c2092803030300c113135144801c00078003014075860f51600e401450b041007052903014010718a0104000780d0740d810841d04018440c071030420f620141d207041e04120340c161201e04014540d000380c5081e00c800c90144400f003000080300f1003140100d0480d003e290304841c104506080030b50000b5000104541d50018040b600014141507964506000f0f03004c5502510301482d2600621403114046000081154070000d041d90380264040d008400350303a8015894089100c208803048046c10010230083c0c111382c0300080d55030b1300406000b00300f42180e01c1010342d0a4640e60700c980c0c3d0421288201d0340139400508072000508208000d42c08180c2d469001054600c04c0c980b2422014540141c0c00d00103020860009828010b0001c104840002004114000c002c842095580c3d2030986c0560301e0010020100758104908001c001c2c001c2051035000048641c00c2d0580e151 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 89092527 1250 89091277 89091281
    0xd0203060a0f0e070f1512050c0918060a180e0f0a120c030203030c0702040f1113080105090712030908061018020a1d010c1704030219030b04110406090f 67
    0x100e102c404140b920004180620b00030a0348000c0b1044440a404900c1ca420a6141c900404044410802c04440d048104004281c41110701415500c2c4400d40c85504800c14882d1041c43c4c1580c140d5480a00d1007040907035a82c05840400f610300100344940107070303181ca0b6214081c01420042600300e00030341c01c0d001e60510000620000703440c01401e4400060000300c41c16909000210070180058004100144c0c65031b8502e402442030610140c400201c2000c9c03540340340102e403402d0382c07a001e43c02d0001481c144100ea00111400182851100801003400c192034555916000d500c00d00f6203c95102c9000c00615000b030024400804142094500c6850103040c100f109280718020214002800d600d6606042c603244240c0c0d02c5050b4546a0004c42015440c80c11400d1880201c2d2504120382d80d0880d500040329004120742e0380041c05400341c1c40b00d0842c4100424040b407403090b00c219044908003040481c2000b07003001e4100b50070204803d88d910101012401800603a080400c4241c10686080b640e01070503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 89093777 1250 89092527 89092541
    0x12062404030b090c0105040b040b0313060f0507031505060904051e150102010606090e061212040e0609070e030a06020d110403050a05011d0309010806040603020a03050601080105010602060f040308060d0203060a 92
    0x9034213441406102c0310041d503450090307000702d18003d841880203010070440d507801960007941003141c0f40840000c1d50340300400d07500503030001c000312601c400034008016050300411200d500d10001002d419410807022900b40d0041c000c20510036912040441c4002c181d0864441030308160100e4000c00e4030341380078140c0c02d60388a29011401907103172010012301d003807080c5a00820f980001c11804d281c0e8440c003041202403440e42d0981d036000d000e04120700004404031030081c070091014885840907803524004000c018030b0001c00b450305000d01d200003140030380d41c0401c00110269015200503100c1c11008002e50040c495003045107441c110024022050040006202c0d0768503108100070700060300f032142c1a0010122044102400e58000d0098005941c020034040f9401600038100083d030302c2d641d80028134100c00c0e0b43d00940e800c7d00400c006106c1c61000f0f000b9540580403500090107141441c3d04500240c0200070009030800c008180420b00344e030758400aa56016400600710b4540d403c045541500420725 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 89095027 1250 89093777 89093791
    0xb060c0303040b0718052106130c08030901210204080a0f0b1b1603050c0109080415020102090f09060f030604050c0307050f03100b150408060a05060612062404030b 72
    0x1004000804441c4911502c01d0400c0c1320380070396940c1728074000900c2085014140003444c1c81c81c0700c003400340c0404000c0001c14840d200b03907000d0391494542c6003415010b9011039040760304a50000c00807189241d8001e00201000d1a90701c10840641031082101d50080c001c6400006403070064011540c10710850b442c0ca804501d0140d14100000d850f5500040c07401c0e1030403501980082000d01800c0c0307204003a00f007a01101070083c101a4640036003e071829085070743c0c400c1d0494103c0c1021a040c002c01440e410711100d155240e0000b10328150071280042c1f07084590412081c840c64505001440c00d0721003c12282e201e4070047c044884c141030a2602c21707224113180c00c11070701a1080301c0e00015a85400d46141c407001078081e010305680440300d8000703005000b0401806411896043c2c50f0091108540c0003000100070b404050080e500341450494162000642007901c20001840001c150240044c1c21302e40080080320340d528120500c0b0b410312102154100201c440000c013040000500414010301c51142ca0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 89096277 1250 89095027 89095043
    0x30f010518040b0c09010c2901080f03090609010c02030a060e0c0d02010e040507090e0c030103050615010f0e150409020301030c08010504152a050c0106051509040f0b060c030304 78
    0x502190848078580403030700501103283d0755012904071820080203000c00328062426000c080b07581d849102da500c1e15404003039944081ca035660300601881e00325082c09800f08401518140700c20102940e924000e010398144070b9040000c151555a020360440034407150301070f06a0760100ea250402c40f0040195402069203800742442e1280c01e40381c00d0034400d0819505031a5003000385011800d200043c480200f903581403018210340400c0d070129000c0b90340d1084400d40c500a076690b0446c80d009040c42400b038048030020b00341c2e0f14803866503a0440140302c030b204598a40310301c040d590180051480441d2512003441312100103400701c0d0203201a0001c40c1601e0143c90901c0020b540c816800e401c03108221009412518040480018841e05800031107060304000c501d040201c01c0104030a88000600c26140302080d0000f4060880031000e00a00c002000111840e410750b0311401400c0e5081d124141c02c0c0c910550340e0b5000542a00680c2d84120f000000c0500f01c1a02c450102200c1540c039071050701c094801c81c07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 89097527 1250 89096277 89096299
    0xb0903070311010b010f0305060d020402040e0a06151710050406060c050610050607083105100c05030a0509010203040b0d14011406040605030901020c010f1b09210f0503030f0105 78
    0x881401404a13400040e500c10030400c1050b84110001c000207408654088217015640000da540c9002030301c060112a00030024904100101c1000c4809941c00101402030303c2d40300040940e0400501d980100300c1c40040ca070265101c04160110031520741045c1ea2107031800502050700703903214818100c0d151080c01102c0c1d140d12601c5010103000003034400c07240c2c0041c08100e082c001410b100301901c802c440d40c11088a44922101c5581f1900003181050700c0100c1d0071b2881042140380102c101c95441c1801c1c14070b6000b001d6561079007a141e124034012714050200006ea0241035902c00c10440d0300804001030050780303881c007522285010381010754002149c100003000210320802030802c9148280c5004050511349843e21100b0740700ca400040036500a03550078001c0400b840028000c0102040c280b00e0300080744a95601c05061701c80d441c80c400010032042d808148804100d901d082a0320300d41013070807103005405038601400d0100c2a80c10043c00c4d8000441480800d400529495060301c0d030460f180c050007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 89098777 1250 89097527 89097557
    0x31006020f07090905030409050f0a060e0f06060a140d090b010602120a032d0605010f0212090f1903060203060a050d0305070f1b0f15020703020d0803070c0b09030703 73
    0x20764420340c0421554004220030010188907a20410000e441030055a013001d40c2d0700528001c0351011a014044624500200940340c1c1e05c9124150103000d40407032070003482c14520400949450014156030007600300144c84c3c0413072070240e2608102c1d80c00c00110256514021102c0e400030b00701e9858210f4008041c0c0700003040d8180013007040e5943e07a04451266061005c0c02104070301030307c001c0010070205110010102d5070381c00b801004440c0700300091004100703e0301d403600041050010118050444d0000d801c00e0240c1d05140040b698000c0040b1941d0a00101042c001116086012440f072410303d02c02d04004100001500a1480740c0750485d5150030b000d6554050008100305044000d0000303404000b850009007407000e010241d14000c807184020500400c1081c01c41c1c00c06504011507544562504012809074658a1541025184068a0914695030200b0048010024002c1414a0202c00129614450203043c00e820343c00c0500c550341f60800011041c0c5a500485050303000405400c418880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 89100027 1250 89098777 89098783
    0x314100504050604060c03060f0621051005120f0303180d090e0a1a031006080c060c0304050d11060406080411120c010f11010207060203010e090a0b010306020c160b03100602 76
    0x7046802c5806070003e0340d500d9850500500c00d58003240141540d8100c0810052520308a1303601402842c4c9a80c035044c41741116106104101c006803032a86420310003040906840c10401c1e104561050b2000e034507880007005010308000080c08144070034030010040003814021800399034204d0340000c0544200c41e8800004a6000460b8010700c0c0002d201c09022a03030001d00b0754412000700c114011400416014840081c0c1003c101400810182c2e840c0c800500087c60309120781d000502c8200d072060300c0d10445803030a588a01503881403e205401c010304007011311490041e180700102004003c0c0356241c0d214140a000b03e0016141502d50800128294810341440c66031509114003980041c042d8820440044804c0704003808103204011401c0301e1940342d10802d00141c0403481c0300e01070268aa40c145000c9130f500407002003803849603501c04024040807039030030300700359064a8002001580c0d503030580c00c50500c1c040b0301c06041c000001910400081480341305002d540190390710300c0070345003140d0340d0001269 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 89101277 1250 89100027 89100031
    0x50319110a1d0d0c03290f06031603032003070f020616060221060303070b15120604120305070c0b040201050702060702060d050106020c0301020a020c060904061502030405010e0a03081615020403141005 88
    0x4080300062022803184122a45040d2348284000d04440d52212040e56070013041c002640100d0104111140d1402d40d10402d00302140245040c0c0b00039400e1941d5500d500c0303014160008041e020780e10003d850f14244c800710504080342034001006558404820364802080c01e011448480001211004180f2134a404001c032000b440d081000d14860392101c0c04110b12401400641d258000c98409640b80d0044003072041902c030394001d10402d0708980180c1c01c0a4195040105100100410344c6030000c00241c040701d03c950400c2d02807a24544034191840800c446100d0b421010b50b2001c0042081ca0142125400007810780741c1950aa8140580103400e0500344e0103000541800340e001441c0c12842418210054905110010008203d15644000c20985442031080304801038100290510043d40c00000300c00d17000b10140c0e060000145183c03101c0034030b805044142010103118071132a40074802d203601c1200c407001c443c103000c6654582d645081507800c400b0401c4240140103c98039500d40120300d1003124 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 89102527 1250 89101277 89101343
    0x430080610120b030f0d090305060105030604081b03040b0c010e0d0e131e020309150702030322061b0906030b090603070302010f110706050319110a1d0d0c03 69
    0xc4401603412640c00180181a09041e090721075801580200d01c410040002c0a030403540380c07c00590f045040c042d0420105070130641c082c0e844001404000384840c804c48255a134880f09003018490413882c0a811481254804142100007003800b0708841c2c81984030550344031a180032180052002c11040d900020350550b01607101c1902919850708400a030800000c6914074007040304501003145480c0d0890304141e590030910703805544080550166081202d0708006540011400c5140c600c0d080c1c0c100c42c60000b1b45003c807018804800082003075071f401040d0f031600c0210800c90100150400100304441c1485034800007820f0000d0722000b8240002c01c40e010300b1018025000d11030441e00156030101209807414100000500380340c4940400f40102005081d41d941e80d59940d00302541c0100308480d121031401c8065240070700000028568204491031703400c49050070003c2d1446003444a40112203050600c1e04881c2c052110010844014110001d8031720a140d588080c51080c107500350349042d140142 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 89103777 1250 89102527 89102537
    0x70b0c101e090606030f210c02030304060c1104060e09011a09060d0201090b0a0201020a031a03070509071211130e010602030f0d0b0607150b0f03030906030430080610 73
    0x40e01401c12203821400029000384008502c83d40d40f56249003158081950940306480141c0c0080039591428092002c222810f140100b8a4489500002d07180c1c421489003600740700051000b201000703041070351034242400042c07040001c5552aa0f0b501d4111604aa020301c15500c0c10340040b42c0da60041655152065010709840c096a0341c19040c0f01d28003d05013420384c14815044000030b0356054080c02810400082e03070000d620b400c1c20910181c180d4601600000c99400304844816a513140007c060003201e00c02c40e51001a5101c103601a10380340d00b00c01e51801d00d07500b00303080c40120707101820042402d001100300c689002a5500340d04081c0c440c080c00340700016081000780b25900c0382008040d101d0b0042d0184e001031100703032010026503117501030301c0200d03071514105026545011803807240780d40e42d9400707959840c2da031100040001d03203034070400d0b60480c0300c0c80b00030000c1001d020712080d4440540100a400443c500030710382034052450b40302540ca400003000c040001e041810100a0b0810301042c0741c5030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 89105027 1250 89103777 89103821
    0x406060504030503041e0816030b0c04031208040204020d06090e070b0f041221030c030e010507020703060203091c080901230a1817070501050c0901050f0c010905070b0c10 75
    0x18030700e00c201c6917442d40c0110414006c0105103900e0038840005400c0003091078141403481d51400000841d001410b0180b601c00c28042000850a42500300c2046005403410b00c90039502ca100060007809000e144041d82c6180c0500804c04140584c0702004108071541121403080c0d840381291058882c1480600c0200320030702042080c000c16030240501c00e40710b202140d0103074000d02e5001c41105107030515540081d48070300917405000d40600c680d842d0100088020310151a0010010b0355510440c840101382507030020016010700700501034142650404103080344c541c03048440041c00e1200c02e444c030280b01c0d40780aa440354802c074515100020000c40500c1500d01c1e6403118032032001840403d208000001c069035240d030008100c1002c100001d110f42d0001600c9180c90704040b802c40d07100500e0b65000300c400708005a841c0ea000307000c1e20a90300340300c102c55581d998021022030141c580080020000e1041c600c0204c0c41010b0311020308000d4240204551030070705c41a00754800e84034561180c100d00d41c0350030701c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 89106277 1250 89105027 89105039
    0x22803020624011404080102071101110f030a0c060f020a080f07030c0806100507051c030c030204030503090f0612150108160c0602030a02090a030501060501090501020a08180d020303120402040606050403050304 92
    0x14000c41d52802c080002400d11780c0d80c0f0b41b1b40d401d917406241c04451420355202010780b150717000320628245208100c02030081028420325a50f680c42818005c2052004d01003e1200700304040e009954140c01c09041991101c420220183c4900d60903508504840b03545070000b280d0600c603100700e6401c0c0c01c10356101d440700d468507024040c91060100c0413104000c02004440040703081004000c40c0e5603943d201e8030311410480030b0002c00b100c01c18040352081500403c01000460780c0042170b1280540c007200c810b00a22510000518240305180841c20411031640800c07c9444081100400d03008081c1c81300c02c51941c0b1030400c2340c101c070f100a00907404100700d40304910214003194082c550208241c00300624041c034550000740c01400540c81162240c5d100c0a051100356070103034203200102028001441c14901542d50b9100320702980074044c008540031502464140e441d5148012201d402a003038a595540504281c0340400f01124142d00440c10400c1c0010294030400c2120200e0360440c015600b800d042c44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 89107527 1250 89106277 89106287
    0x11060c03130506070914100504090c020106050310061a0a050307030903030609090b0109140906160c0c0e060a14030c130b0909030307110102040501051902280302062401 74
    0x15016850007000601c0907400a1420030020703005007071589400503014a0140c079804d5000139151018095090f60008101990300300b000e0b1020745e01700742000f150149181d030040340100b050340c1c0301da58944502d61100400f140240d01190594008044000261008940d0791003980316800c0c1040c0000c10410000309030503c00e92081c8035407482480c010074580c0e69000c03840180c3c0c0034140241c903280310700c800400a14102e0f200380c030440e100c20000c60010785011144240c684c84000e02042210b8034180b11508158840d0300180100c59010001c4500e0b5511010104000d24048540b44d0107007040c003801044c000360810030802500f200400070300759182c0800620120094681e070400629440d0a02e440040e5a90012103109200c100700840d101c0c5020a0010004428140c4e1031580381d2040000b801281da0050445030907900b4840d1012440c0c1030502c0c204c0c03910540064004a2040001e40800c0484000700c1c4040218000e03030031508507417100344100c08100401d100310105401e40f4040c030140c5501803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 89108777 1250 89107527 89107531
    0x9010507020111060109020a0201140601140f0c070603020c010b0102060108060c300601090e0c0403060c120c0905041103010b04030f0201021e0102030601081e0a1104030c0f051011060c03 82
    0x625041c800c030a0f5841089103000020713085901c82503004201c0c6031206a0921420500c40c81d002850119130030000c0020b48581000c00c06110b4407400000da40064a14450440d0174840201f4219030fa441e41da110001c00075040b0b04030b000c48035401c2c42c1c0046110340c0300054017030585181c2001740500351191114805a0340c407100300840ac0030001124100e0f001d2024456031020424200d50038941d10341200010210b04454100e042c80ea5200f00600440000c01b00686041d40c0d4048000603010744403603000d40d02e0f10045103991400d42e00f4078410900321507201c11400101e810a843c2400405040d1580344102d000c2400390a4400740c00340300800c0031505202038020818018015948014986982c0000c590078854640c2c015a40020500140756480f80b0781c01d81c041011f11240302c0883c6e81200c0140d00c0c010252240c0324040d102e00d80ca00800c040c09040310011540450291180d075130703820f4425801c44443c445d146c4242924001d8005407400b4604040e18031b0001c0000e00303195580c00d02d840c801e617040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 89110027 1250 89108777 89108779
    0x10912230c060403081803060f040f0309120507030c090e03031501030e030a09030b070305070203090f040605101101271202010603080304060b0406050402211302090412030e120901050702 82
    0x500884406580b503880040001d58000e1118582e60904aa0000384200c03c401e1003a01075070100080201080741d020710560841c0e40110580048030322410308a40b943c0d0700d500440d49290080c03014100b040710000d6442d0031a481104070380c0407103039100c07583c03021244d1400307900c0c170503410400000b104149422610f41860005050000e0a603400c28601451600016a42d00100d00680c0e414004d2110440030b5039845002d074a0180a20b1600040007500c900440c1c0c0118002c0400010b000c03071a0750340e9000240603203800707400c4841d01d80140310001c00c070207001d006a202e02d510f8184c484410f1890f245c400f0028001802042e03003500c81686d40d84030809200740d150821550303550300100008803624020340c001d50003200e010940c004250100011074015a1007a40324910411803188102d100f4210000505034000c400c94159a814110040c540410480250301a404108000c20840d030904600e920a182e07a408220400d01811308996a038002c86000c40068414400500300e03600ca0001860417501c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 89111277 1250 89110027 89110033
    0x705010c081309050c0304051b0109030201030510090f14010906030302030703050304050c0310060302041503020108130f060c110706091d06030c04090602250b04020d1b060c0201091223 81
    0x150303c84860f42251400e40341c0c1c41500000001340700034400c0410030070b05540840300b03002d042c800b140c5001034440307000ca00c0002c0c14503031600b000030001207503500403034000e01c1040418011b082c070046400d40101078042c6112403444c041c000100c0c05850758401d202c00d403949a0025854140c0a44064426410060045405202d007911000107a1000d110082d1031003010f10000c1052403c610400041d80e1008021000144c8810000c00150fa8403c40700d903002741800e541d00b5010607a500381003800c000040c0c0c0181090b41440f4544003050341c0041450b03100c0108400b9942c009071500e0003210040d41274401c00c3c09072030108258030811142074129a030444802411620481d6040c0003007001d0740e9150f50140c4a0302c0d0302180c0160010158603101c0008a0840d500d000e0540751a56200e00c0c0180190001e402008003100341001c2064134440794003a11070480e00303122004e0342e6100050000d01c0914049001440c650000140c1c0d0050302d54100089500000021074651041c0c8101d0405500b8814110544 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 89112527 1250 89111277 89111279
    0x503060607050a051608010209100509010c0206070b0f180a030f090e100311010207031a04081c051b030402130b0a0504020a05090f0a0b030c030601120e1005090705010c0813 76
    0x4900308400c218030f5102d0005412144840035014030010310903800300e02940d00400035903245640321131445030342c030aa03403c22603180c5a000380100d48cc1d801250000b904050009200024418180e03046441440018000d2a05987c0e411003c00da104402c1c2c140c085d0f50f80010f0386200001e004c2c0c2407042c5e09003102c2c07a0a9641e150788061090b10642c0c01c0e50300c0641002c610605005014091a042c010403400b07000620410b0b01c0c59a80740180780c01003146d00310103600b402c00b00703007007113140021030303a5082803410f10841706003000e004040200030655400201c2845140c1402000085009891140780c009180b800c0c0c0b01a44900c11020b040faa03c05194400310b1100007003400e40e11403015292a110f99a601529044000c050040c119100c0c007a581c402c00c3c040100b0850342d07241c0c50440364461903205003503031a0344418006072040340d44075050740c0c1c00504000c85185000380c0043e4500350800c00980030f003d40e84030000e10503200c5856015090016601c6100305010036070000090045c8004c404544e6004c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 89113777 1250 89112527 89112533
    0x6020708090a06030c12050105030d050c030408010c02030a0e0406030b06100c0605090304051212040b130807090509010c031515020f03030405060613140109090f050106030804060311040b0a0503060607 88
    0x4a81e4001c030780845d940c2d0b0b05144240d42d00c41319011113950001002c000c203504210020b03903540988400c45040200c005a8003002e90740600c00d0b10000e0514000030311440000c0354020751290171190301b803000500f00c40c11840c5185044c0c018034040f41d40108841407035480d48428048007007103887c00c90082c8981070364107000180e140c0c860741e4401c40144002d1611a4207110400019524034031440143d0340c0a504080f84120210040701c0448001e40c40d240e03500c9240031040d2564200e940e10014107401007490000f03182d005508100d12454580b40204070224842c1010b03012100600b8040020080d0100c0521100d080c41d41c407101010300c9801120300f07554509081d81c0c13555200326401c0b65070b6040003003400b64500b8181078401c00c24441da1014031a00b134940c0065220000140f01d810360283c0c0302e4000c042880798403400c000160760000024001e940c0c89040c0300400d0ba1081c458400003a2030701e8001382d08080140151415600d222100c0c51400007045401c84180d0405409070340c1c0170710104606400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 89115027 1250 89113777 89113789
    0xf0521150310140c03100e01031a060102030c0706030506060d060b0a080609040f170c0303040303060807060512061516060e150114210d02010b0f0102070308070602070809 75
    0x1040811410040c02040c0000a0509201e640290700d01482d0810360038074201031080704440d9015095490340e988035680e86138072080b012025802544040140b1001009019201d00280716500d0301c0020602176448060049a0320b2142e50004842034004000a000c0705110350000340d0040c0f00100746500309805561090f00702c0d200d40d480600d15400001e000c0c0e15994000100c503a01032002c4680145500d003030740390807000c440c03c04030080c5215444c408000c40d0002000990300307107040c0b1070100d0380c407458249030140007480c680c01108a1846415030014455114200b2540c070351020f2480502da945a40c01030080900403000e400300740603024070243c0c0340d80202110901103140500e00204500b0a409006420521650f0840c1a0179825100601020111511140c1011420b84402400e0841304078844940703100e01c150040d280c05643c45411200d907054100340c09182c82112170000350480038005903030b81e82e100c0c0f1000708030220503c024008100b60303501500700b80e80602c00301340c0b80000e12000a10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 89116277 1250 89115027 89115031
    0xc060605040e0106090b090105060d05060a0b071103120a0207030b1008011103100b090a05060a03140a140c190c1a13140105040b0610110109031e020303070f0521 71
    0x1903070344d110410400c00010307000b0010381150a903880c806c0c1e541414080b800c039200320b4098150154072000456401d846070001140280156122203032680d0b01458a0b084c482c01504902d4440e11494503481c1414501c0000c40340c044106800038500d4926580e100900302d1b1008022142c0708a004a000076030080030301502d80040381c0701c080c00d65a80b900d0060106984003d0300001c42c7d41c00c05000701d60003500c8841c1c0020039a5021101c00d501c50005440407000381000800410695140c82c09006011100ea04941490170300802e1009090780c4845074001e03e40184040e040c41d16000703003101c800316802154032140160140c003031080c01c00111000001d91900030388404000510348906141441500c01100400401c014001c0c00941040d4840c0500010b010b800c8a05c160004407070000c402c0c1c082e6088080030907428000340000103032400c0151000ca070f1081203010138200707d44140140351010088a01c0303030705079884400e2840c809040071138403500400c030f580c5044039040c07190000b00811802e00c14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 89117527 1250 89116277 89116301
    0x15051e240304050609060103021e040b0d05071a0309031e12010b0910110a030e010302040305060f06010305160207030f022b03020c060c06040609210302030601030c09080c010c06060504 81
    0x207940307041918007030f0b1401d00c0003000300b500394102c0e40051005030345032201c20100503842a903000c00c800010000400402c01e8143e010b50100c0c40c2c005d420308100021660303108580c600e450004551590b031115000a10080351505001e80007001015100d141c07148105100c00400d01043e81005000e10440880d900c00b0380007000810008a42154507192954943c5030301c804c5071503c0c00320390000420007651400452001414840391454014003640710b039040c0e0f0f00847e0071804945450400110590041d601660220f00081c2041c0014620702007100c0c0c124500249580140109890742e1220502c0c1c800e0880101d910a0707e98061850f5141404514401c4403921101980d40c105180ba0103441d1070202c9030981c0c0505030a01550102500c00f2662641c40b50f04140e010541e02840d18060300c518a5090140f51000c07540c89020645684c5030340070354401c0b00c0a8800704040140c2c1101500c9203000d900c50941d0035441050300d1041948541d80709a1402c3c4244000b15060780c45000181c02d581c07216940c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 89118777 1250 89117527 89117599
    0x1115010806010501090308030a0c210203150625050a0209090105060306180d0e03030403060912090914160e04110702040f05010807150e03070b030a15051e 68
    0x1804540d00510003240180720908000c9001441c599451025010080c1000001d99881281a5216025201d1000703619a0740000040c090818003128000350802d480b04600c18040c10300200c21800c201d412282c550b404001031103003950f41c1e45034403090b08a800c0d0b4112954000c2c02083d00058440c03c3d61580240013105c004039440c80d0a030207052a280e802841c00428101d2000b5540120401180c42c5000e4030042c40c00c015800010782c0031a14601c256800181880d01d000680402d010181c0d83c0c0c1c045130b02450341c0315010140d440b030401c81551000c0005034140d00a10002c6600c0540890341522880e1107410480d008149400024084445041095590794000174405085261500c555060f581a9040411165041c030020940e10003182c0940041d56240c00224200c03240034005c00d1103942c000800f01e0300c1c619121106480280c100742c0e070500c1810f0900d240f046c2c8144000c1c1d035440603100b0140c8a80e2140308070031030312243c5180144050390030a0505581a1001604d401101141c0f4101100c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 89120027 1250 89118777 89118779
    0x40306090c08010b01210b0114070318080304060206071d09010e011502060f070c02030703050d0f120911040b0a0504060902030411180f0a0b0d0c0302040f06031110111501 75
    0xc509440742028080e0400038000c903460f020030a06c550031040010140000100314280a0060740c2c403034100c8043c00144d44c00401c02108050703008900d41300d90382c107202c8081d60141d078954565581e40a0740c015400507802800001b04000d1040c0c4402c1c4400420300f50307140350101200f011981001d000c0c0c00500d0b0004030040107025031411340d60380c03400600c02c0740300401d11890591011040d0305005090001002586807a81003955010000c15001c2c5400800307880c81201141070290904480075241000b15422000d443c04150f040c0c442d01c004170b504006281e003a8480981048010501004803a07480046144045216199807007450064804084010703904d007040d08081040ca480c0a9a6510510540ca40f41d03800050500c107094001c031100c00710789040e845a0f00c510020304089060705400900703240b540c406002c4082d17035250460b8000e4404100340c2034140c24400030b0711400e0101600b50060104201528242500828100f00309440c051211000c442d46280c103004144148203174030030788480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 89121277 1250 89120027 89120039
    0x2210106090f0b040302090912120921120c0f040306230106050d0c0203040909080d05070207061b021801030b01241b0609020310140c0f1c02040306090c 67
    0x4101000380c007080c0680c030b4480745450301e44109441a400000c2c090350301d44021801c4d0f1a4100101d0100311049011103840b01d45a01484d840460200d9160a183c0b103074260501101030b00101d84c15403d0b42080385c442c500501034401c0041c80c03001910249911000b000340142156400002d0000b541c4103180100304402003d41030074504003049400c001c0e00d0014001000590b800100f126000644030030081801a140d00091313003140a568007582300030b41404d014600300030301140100000c0c0000344041102d5100d5507003c070390782c40345802003a010500b4400803105030f0400c0c142c0c6c0d01c8818030040041e541c0c036010b5a2564407059007a401140c502031124010311821102501c1d00091482401d40719502a8100750000c09045118010101c8a02008040030602a0940215010a4001d0111841008150511401840a41038041c40072011202041c1031000e0001100d030b0155200708201d080c18600b102c25580c2074000381007000c00325802c0100000142082c00b8140205024090120300545008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 89122527 1250 89121277 89121287
    0x5090c03010b03010c050301061202090307090203041505010303090605070f06060602030913020c07170a0609031d01210507170403020109020117040c0b13090e0a0c0e090d050d02210106 81
    0xc00b10303c0c4240d05110706004d0f02e6503c14252411103203a45000601c848011170800001e1041c406615014000da03000031038445e0568000314003c3d071003040c4100b03080319000c2d6a20704458081c0001000240f000108005da43c1c40391001e050520b014802c405060b41403640d070002101c645510a00c0036802c081141c1c0828905001600941c0803141402c1d0301d00202c1c0381d0560b445003094041c0310000c949a85c08150082c00c10414803a0326035000034100b2032507840c0c0c1006002d900703d0503507220801d0204103444202d5403055107444290005c42c0c10a0045000c8141508041d0000408078000c02014124111400c140c1c0420903000703038025000018035200d20300004000c0f1503071600e0b41850380142c070b080c00000380c0e412000c042200d5183d00c4150700c0341e402c1d8100c0c841044940d48680c40060800c400c461624102240c0100c286110305c050310f500031ba80d006c065610160440d80550660001c200003d6010f0082d0010714942d43c81c248010301e0888180070207080800013041130458031704032000511030b2503044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 89123777 1250 89122527 89122541
    0x150b0c030c07080f0706050301030b0a11090301141f0503191a160215060603160905060a030b03060601030504050a080915220609140423160801051f0e031005090c0301 73
    0x184c0380c07c502d95815a210700c21260000341c064074055a90300f9003401044070b0350003510300c07007403004009015400088815031380321a0f0980380c51104141100c08400441003041c01da004482024001c0c0c03e285052441c42c49440496100a8075440316000d01e201092294503107140c0b19a442052100800a5001c0300031301d44842d044d800c80d0202101000c0c450306640c2c00090f2a485030304044000d540003890102120240255848290402c070003082c401d280541580240345030440c260126121035440350011000d0700d4055901800e181c0040301c52401044442e40200359800300545488403901c030011040507107a01850380303240d50306400d4960201840c07000c00e03007800820061600448a0b0305044420608000c03a035501441255200610400804040f1841c01143d003464010100341c900f101150302c0000d4500003d40000e02c08000103d400d145c1400801c80f06c1c90300540e8840e51500c0d40c0c8054a40480a00d03105505110f080402200c0c0c000381d0064500c1264420301406060381c01d030060500795484 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 89125027 1250 89123777 89123789
    0x3011811010f0c1113060602101107020609120109020603071706010c03080c07210302040807060f05042102100216050105030609041101050c01090f02090a150b0c030c07080f07 77
    0x410b46090220361140846a14580020340004180c00c0c540001e0075004020450120884c2088800180a900403e508003103c1c85503006201018458140b80790301c0c030640e50000d50010341400b41c103896042c080d802e80a9412154000103101e2800d40000b00d035078004550a400141d1050080d920343c843d40e8590f2900300f4002e08101d404001155400b4103520402401d10401c02000b00d0060280540074150030307040c071044000388818040403c0014041d601078014034485120310200080c40903c10203407100d01c0342d400d94034281424141500c604502482410140400381542c03c500c01503070310f40c0070ba18440d2580350003d0160511440319801d000c0c200354040c6052200038010000b068443c0780e9881e6000c3c0d0301c01480000d6401d1140180c5283c01142c8603089075610780030803141088888108111501e000700c406102954907415804250b0309102d042c0341a207207202c03c0c01c0081c86810301c050f100c0c4a2148042d241030040081501c2e01d0001c841e07020060303e6114104107002080c0500418002d07101c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 89126277 1250 89125027 89125037
    0x6030501270c05090a020904060f06090e0c030403030c0309080a180602030703020a140703050d0201020c06060607050d1101061a040e18030a0f1b0b09160f061407020301181101 77
    0x40710b5240c2007001002403181c0d90003540c1c0c010000301045070b03980c102c0d11480c00c010000c02c009038650010380c0362440c0074001c0c0d10104941017000f240c11030200b1000f600ca07407413072000e00740355540302c0e030f4214080c024035404032042c1901c070482d4000164180d0041c203141d41032903490111940317455241c500750100310b52150095410400c022008a540410610030440d0030903824417101d155002c9044c030b4a4000c1d44050468080c102080012903419002081000203102c101c500d02d4840000f040094890f0728401070113648400f80405005005841c449030000e0802c0000038240e5a07818a1400045c103201e04011440c0001802d0259500d00350f0869040100721110401c60007095030ba41707a882c41111581c400f40b000b61841e0000a0348100000f4a14000e400744004822141d403a1004a41c4401c0c1c80c0004140030b820900d0000c0d00000a8600072203096001c1110a00c0c5001410303944400082041003540b0760070456003015031000d00521400140c889000d0341203c499003800f00030b811003d601581000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 89127527 1250 89126277 89126351
    0x30c090b180105060a210c1110060e060112140702030a08090312040803040f02100e12060c03180a020a14101701090507020f010c030c020d081e0c0d06030501 69
    0xe01d65009885003400d55080a1040c0d0070401b000c446900700d400c0303003030f0001800c05c00301c1d55032668850210304072085c1e000d08980d12059017084900c151207003401491070303030344072000081c059600c160608030988003032210014030307103c03e07a01c0d5a494040480c2c0c2c03070780560b0002440c170401940c0309811079400503040000c0d5007048010454000003280150000d409801c1c0840480d0a02c50460010b07031b20942d008101d001101c80651018040f510001c2e50301c0d110b60440032018030060004110b040c401ca00310301d415895585c1d128072000c0c10820300d5000a0440c422a0324007001a150645240050051806d01d1421408944100103e05d804901e06070200412a2103404c20a01410741440c1543c41d0483c000c10703683d644500403440c1000221202c01590300b00f0f100c6502054040c1d1045042440c03550a440c03500b0200242502d90030070503034400c0f06101c1c3c0b900c0c40146000004260302d800c6190020103034640200205008151034141e041952141d641f114910f100703240780e429821134813486101140d980 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 89128777 1250 89127527 89127529
    0x3050c030105011809060306050a0501051c120e03030d022802070b031513050901060501050708070f0201050f12090106170c2209050606090601020102030402100f09030c090b180105 79
    0x5000c1031180e103051007086580b03290500c200c4219500a4800c0c0002000f0350707940ca05007007015120036606400f0440ca0180003160324180802c00c0b0725048080701e50001c50300c10725603505900c995510080803c00100358018900d641d0180010000c0e44e100350009a15141d2960801481c0e80c103095078121505052481500e2140d00810002c0c2150048010580c80307a41d02541d082e449a210742e50154004000c543c0c07031030860416400503000c1c01b00e80000b00441c680f101e0054035903101e0781d030001d0040b050900500c00003c070310401c1594294410315146041c803131441040301d03064000840d04041146c0e2a42040780241091295000900061b070f041a41c11202030540b81d1250f1602e80001d0103451500000d00740a949100003421981c2d4006041200b41201e0a0041d00d0784c80c195145c61143c1c1400022582540c814001e0303c1c0602d400400e81e000e25010300c902600e00042200d540d20a0100140d80080400d0302d801880d0002d0848190102c0c003819184100041203108400302d088000c42c00005200c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 89130027 1250 89128777 89128801
    0xf051611030703080720240d021603090b090a0b0d0b100801030b06060306092202030f01093516060504030c02090702010c050a0e18070c02120703031d0409050a03110d0305 75
    0xc4d040c42040701c10b01240100694452501c00e1380f0b1100c100074000210705501b810910301e180c02080c042e40d240ce00c5140c45409201251241303509031030b0f100850b100b040c0407100b40c1c000200000300c00f03c00300044032042d00000c00c1c80089000c46140208919000400501800510071a80010102c1d0414075615024001601112002d001d208403d05c030f034120680741c000c0400740d20001603002400c540441c8002110b9a01900317030450121051800324030710300c80e40046141e8146000781d800200c0714000194a41c4400d00741c00c600d401c1c130082c1c400f0901040c0490664483c842c0106e0107a42e6007030706181d843c014088600740c0030301041c046a1501004080d101c4e80720b025030b0740c280f88502d00040359030803c1c80018000e0200381c48869145450806000704243c001d00350142c0d00d4402c0d03034221009803207c0e07009a1118114407002e804079483c8480c01c510610068a07082e42e14000410004610f400d42d107420345803d1070b0210440100d10181c004034406c0200300920054484a071900b48581e1424000c2040c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 89131277 1250 89130027 89130049
    0x6090c07120f02191b0e04021311040b03011d01060219032001050906010f050a0e0604090f12030e0f070501090e0406020f03090c100f051611030703080720 68
    0x20824548600e0820b9403080c0000800d107120500e580d43c5080141c149664899140d454801000500041c000b400039040344110303110725001131034048500c0c1da1040340c0303007d8080d0b0700c0c401001e044104404502c01d5118030185010f00414150b692040f118060509c11840041c0c0140043d03501074611081030810b4100700074402c41e031519141100c89980780b201d4040240307410300c4041075401c000c02c00001070300c0000c0c0fa1f41280c80c80001d030503126903910b00f03000304204103000e0300e8100340d81c4800041c95410690810241980710300060200001c20703407a400d20800100d1220b5000a40328040d514441c01c04003c52012071240d0360203009403528000010344040024460031101c82044c0c5c0001d0103210169054424034844009559900d1512003056519200c4121485104071180e00744003064038800d406010040c030481d150337945041182c06000d0508142c40308210b4003441910701310101a00c043c0031000045221f01d0600751164014a40401109a03201c101440301801e25a070414a59030365031403907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 89132527 1250 89131277 89131313
    0x7050d020c15031b1b0109020316080a06020c10110702030606220b2115010603050714030a0608030c1e0309091308040e010b07050d020d121802030109030806090c07 72
    0x1014100d08507180d40a42c02145d0440b04607131380b0122186801001034100f030441e1403080b800e450032001b00a00c0c402100016014440866020f0314541e00000c803154014258443c600e01101d41c2210910303158010784a601c8030740842c1d00700101d414002c6080070001280c000c03030211401c00020054000548a444000303502112150b16040345840c039460f402010700007503407180c6545802c0e522204c04030f651000d11841d808a1150914000507031507210740b0460340101c05966580200c16074040300044260006032140c44142d07a11000029170381410401011a5842080902101840200300d600843d01820042d81c2c0d503041000702018556426805543c0b105803070700d04061504041c02d1100d050b000380c2e000081041d0786640041015403c641c0907110481c8a401180c844d0440791078201d854103941c010080c046005078100301c0400340e16820800196041c914201803003032481d0002400e507200c50300c09402041d0185d003031000e2410240c0c140780d0f00c91041344040d860207640e590b0761301c81250898414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 89133777 1250 89132527 89132551
    0xf06040f140a022d06030c0a020601080102070213090809030706030b0a0611062802030403022112010302120109060609060302040b0a0605040603020f16030e01020c0109050a181107050d020c1503 85
    0x1105070313400c8240e4000e52002003d001d0765241d01e0b19802000709644a1244480544107900001070720010500860300115405014100d40348100080f90300a00428042100d103908144060038103910104142d500a100c02c0d5404120741c140c120900540442c5508150b0070450150703c0350000c88000501e1942146a4030601002d04d10b41040003c8030003070306902000940d00010500c41071582c0021030000341c1000700180b101002200c003140020f441801ca80c0401480208010005403072b01d034031441060b441000021070503022558030038080f1101c0c1d030025050581da07418280f041d4205445021701d800e03030540f2800080b9080100c0502240620f1103601c00305500011f200e40200140c0040c2d0f464030001405410400300545006011300303c452065078010b108070f06502806e58421028101203d001411118883c0c4c10084940e5407904180c003400026134540a0310759040001e10010700c1990b0103034001c4d029a4803070500c0281407500b5a01c50340d104030300844115494502c2ca40803a504003013034050b5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 89135027 1250 89133777 89133829
    0xb03070309050706050a02060106051611061b0615191404090c06050d0b0f0109030605041a160f020303060f0409050705100509030c0a0b07030804050f06040f140a02 72
    0x208801810312504014501c1c041c0000000308280c01201500a4100c00c0d020345d965a038881000304c405000d01c464560909002c038143d20040b41e8000040b22841c240030300168070f807441d18800f582c03175094110040c2400794000c40411450310b261310000da103041c0c8101c1c1c001604840c030480041051a43d40280782c241008a00c4201d142d03900e590041c0781c25540031080b02401c2d80d82d0b10340541540c00000d05000d8041c109480001d0a1500c22032801100ca416110465503038119120388008010082081b20316841e0343c40f40003083c4019180091064800002400128041050040c8041560741d0104203540c018000d0118580d10100203003d80d943c280e42c00251a0700504099140c80c402d5802582c02844610070625038070b80c42030080070400e600b941100d01c58015002030040c44480d901c9400b9085005002c6080000d1291504980050007042155540d9101c2202c5505000e4140c0d0100c40030f8a075004044100522814003403600401d40700a0300340079000b0b4012078030010700e0414654188040d000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 89136277 1250 89135027 89135041
    0x20f03010b0a1e091103010810060303021015080307050d0f0207030b0c0a051903020c07060507020d0f02150a030b040e06070f0503190221010515090f01030b0303120a0605030a020a0b03 81
    0x2c400f005020b134490601c0b500540e0382d07102207a41d100303000b828607600039078903103130700700ca450340504000c586d4140d0041c500d4800b104101ca008040c03105640100c0100301c1000102008208050080c40d40980081c11070846030840240101114120f114299041144204041440f0341d4815501c51601701c02940d4881d034000c012240c6100b0800c0c0301d01c900281d4084000c0496042e4050000343c01400212018141c44102c01d881c4e60051500095101c2000c078030282c0064808649241c4882c400b82c41000c90010540d0700c00302c3d540103520f40c140020743d5440507101e0391500e405603030b8020b28400e01402c1c0710305020704010581a00c0000610a1020000102e40d502030707000a900d0070109107001c00c40d105c0740d001e9449480100c2c031050f9010380750360140002c0760601d41b000d0240c4180d450030582c42c3c9000718500c1880100e0031000607150515641c1c080030b2200c5d46080c802004d00d4500301c4113000441c07a04140e9801122030940006001e0b500c1000350a0041e110008007800383c6403004203480c2c40c0c0d078440d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 89137527 1250 89136277 89136329
    0x11030c09090316020d050607030603140120130b041202090109020708090f130905100c020723011214040516062007030206070f0302150709090b01021612020f03010b0a 73
    0x12400031b005129030410031110f01d500d9840710b41544c1c800c003200005500b03407440042c00e8031505040c0b14150490350f10302001605030100140413440201c100d0100d425174849035008150030941c03000e03203c072100c141c0e100b0851502c5c14540c7c6c00f50600b00000c5091441c2030319002803500444c03031001c0c0900f9450b82a1000e0360f4503040c0301740c44c0d151003110a000e08021403030855200e850f00300f540100c1500300391400c00158004a20310301602c070040e05281c014120820310078000250442501d0501c07007046d640010303240c1c46014681054001960380c10242c03c213031515915007142c41c90001440c0324950003d000c80ca601c07641d5049240d01c0994200c05034481801c80d076040c101c035580000c0d4070480000c1c0d5842040103444010304130314040e40030f40324002c40340101403004082c220b51140010705c03030380c40030301c0b0390000390f80300f8034051806104807003440810010804c69803400f034210548561146040c50110726102141c100840700c250300038411400850049800d802c3c01c3d015208003000040203d00c00c030300f154 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 89138777 1250 89137527 89137549
    0x40f060e010906030201020111120f0a0608010c110f1209010c02060405030106030b040b0708010b030a0f14071e0e0a03140316030e120a0c06050d09020d11030c0909031602 75
    0x1600035544650752000480010441407008034090350800022001001d003041c245c0300b020500001e0300718581e0711400146814000204080034003075843c503000c14201c109100300b00e208100703900c48000400060303000d030707141404103000c503500b41e03000164a03824500c4100036244820806e01700740c62461a90b1001900034060b41d002140c0640c80c0030f200209200c0d0414980d07024600880708005283c40d004c2085a041c80c0901506020403020000319031010003550211000d141000790003c0c5e52540d081b41d90461804c15500c030b40c009120320220b1040c0c403c0032032a0b60303110039450400c824041d075410045110102c80d84000b81c001c504001c440803a0700014000c40740c5800c800c0d50304039010b469600d0701800040402000a0040c18400034406040d0300000309440a80d410a0400403070920742542140d403544000d0054040d69260008240140c4480812410707140c4660b4080f80b400215409140c03400c2600f400c91403007890080700303204018802004943c10054404541c5501d49603600201d680c6e4220 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 89140027 1250 89138777 89138789
    0x15140c07031e020108090601030305030103110a0302040c020f011d0726030d0603050d0804081206030c120312060406120303020c070e0a0b030f0606010e011b05070e0a0606170402040f06 81
    0x5109018040080880901118103100345c865a170070b51035010103030750b54280c24000100030900400c01480855076540c018400304c60014214140c1a86903804034060304d140418030400350b80b082c0c40c1d10300403080a010b1f5007201c40038036500032807010040d401c0907a90311344c501c5201021070f400e59150600c0360b03c02014841030528030007200c0e40d8401c00520380000741014801a581c500640d071800c61094860170409000b99007002c015402c0c00004071915050102c003505c400d1349449039140300c22194032420100003408034804040d6480701145c1c0c001d03d0b84000d008010ba4440d40c5000402c0c00f840138000c90450600c3d40600c0d00584a107101c15446103041c621340c109007a282443c0f402c1000a40c2c09c0d80044582002c01c0c4d0945981d0784100480913501c1000707991803808212419054000b0354820040a612400c4113a4402c1492809489207401c110b02504480f0f541344210040203070100071400b40308010041464508411004440c0c0322183c800007401c024855a22400b2807000d6413840c6d0082c3d806884 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 89141277 1250 89140027 89140043
    0x2060702032b090603110301060e1f020115090b0a03031d0d0f0201020c03011a040c03021903021b0a0203150604200c0c0a0f0b03060d080d05010f15140c0703 69
    0x21261400195612070300c5282c000452000c808603400f807081c0580b40c9011000743c0e001c1d04503402d268054030b040c03200d03000f07158200040704100c1c01c400150785081a40341102e9000001c20452140c070030203141c107264120041590408145070b52907100d42145400f1a5051301d010202a2200240043d030a90304180d9580d00400d41e59111040c40341620030492154400d0702110303540b54010003814261131340041001c034680000e041109603801d1507002048801d03098900189014070b6811900701c005401c2c10741c2800280e010403c02881004c86029009904915008003244003859001941c0d4905400d110074605041d000030540980322600040b03104504952002a941802d00c141800703a0414031101f00c40d48100c4000301060301b480d00d14078042da10400481000d040c10010b00c0c0b45550710240c040c2d070308624030705160804540c07800058224181c03d0980401d035545411214100b101c190380110f408022104800041d20f44c20510311101c00d220b804081e07440e200c6040c507160074803900c0d502c080d01c42d80b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 89142527 1250 89141277 89141323
    0x1110601060503070801060e0a03120504030204050c030108070803040315090c0e07021f0606050702121f060302010f0512060d0c1a0301090507170a05040809040c0e090a05130206070203 81
    0x35030004099803142d41241d503170400d603030790710b0204030b42070185400c2d69600100ba40d0780c1030010505503102c450354001c3c181441c92600e9503d50114ac00c9400c1150b444440400100061258210500040c2c004282101c0110b09140c150344602c0f4525800c26860241075a03900c2f8030f41e00308003414980500078000c0c00d08800842c40d0040020b500c07807068100b0882982e07030003c83c00802245500c10394003910700982e100350070060176074280a0541d03403545050951340305107884424250f1440c3c00c24000c488400c00c021070380f2440c500c009004540c083c3e08150a005c0d050280103a40800280e01d41ea01c46811581403841c9013541c282140d0070461500604483c41c6821004114101d0f02070007541290440d001c00c01182e5641e0404644041c81c068040040b4444040402c403066055001250054050141c0c20310f000c1d0680d000404075282c4a4101d004184030319098103075443d21468103035100072204428801484d220903d07100c90300c16010002d12584020403a0000c0d5181048016544074040441c00040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 89143777 1250 89142527 89142539
    0x70306090b07030507020d0c020103020f09030a15050a060302010c061a04050711070f0e1603020c031b0c090f01060f050f0d0605240d020702010c0204050c0301180e190201110601 78
    0x10110440d4003401280c11310010542c01d51000070035210b407001c03070b80d50400d10075001d0b40114084d610000c40740200001c2405014001e0346c082c0a5808014850b100c5014080b4141c9010015103400404000845181203c1000942d80016540302c0d0607521200002e0080c1c0c56819a04190f010100c0d03085c0c00c03514103803c1000362074208980301003404507201141d640c01c0e0348003241d20450b00240105480d03c80d0000126194010040301c0100e050464180036084c4000c6102080c5507070808013010240c403010b24140c100110061002c181d91072415501380006107000840f002c20700e441032003054204122460400c0344284684250340c00050020601661950804600f4024081174050346106226140c1c0b014000d0481404a806c4035400004850408074150000c1c0c0082d0440c84050703040c400b0740460760005a407684035551094200c000340d00d41704d5060100f04890300000007403081c40245010703003110b075190000a0b80c020751040704031002c0003c42c00d44012501c4070b20045d16002c051044500100700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 89145027 1250 89143777 89143793
    0xf030a050a1104061413020310031202150612120a0e090a09120503090a020d020a05090f10080f120a090b0a03020a2c0112110c0604060b04050f13020307030609 70
    0x507414089800340003054640507918142c401a5070b011b5480040d040f011044d0480d0703174020796400f0001d03100c1450b040c0c0e581c1c0c481c10a00d600c43c01c0b990006030802c0b50244e075030340d0580c04410780081d000d450007250786000401181c0c3e03c1c2040c0b000d040c203d00001c50403005003440b4400c004002880a0240c8215060090714400135000f100c03c100d130b198a46041002c0c045208400780c80c842d03a0740030b0040505547c903802784020b0069500050b40c01244d841030101e40e54540b0203031940982240348018a007454510206144c2d180d05811842c8a500501c1011000c800005801010310a6405e0000d945025511050b60104240e0744000b41c1d4080114a0308a2079406038083c20000030b0350744403d0700d42841120280701003100c0d056424050030780c2e0409024036501c41c441d00c00c8104000c1100013840000300000c010030360080c5650944560194080208028081c001c4070311300d06043d203003444103090403c42d5240c420b80c01421504544c02e41d051002c00d666040154400654000b14100300140c102d0400c284 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 89146277 1250 89145027 89145053
    0x7050316180207230a1e05060c130e0a02091504060e0a0e13030c0203030c0a020310091106070309050a150305060a030201021b0109030c1203020607050a050304020f030a050a 76
    0x40302141040c1d202858149030085440c101d910809a88100d480329809603d0f100c0c031090600700c244507103220940064400140c0c0c400c02e01030f2981d000d612414529281d490007000030540050b416051280c4501030258404160503140313040902e0703901e5a0b030106440000c1c000e40c0401c5520030035104081b0a50403140d0300810035200682d8442444170320503003c1c000001c40a1084d0516200020300103500341050703980c0060000d20a03d080101e240c04d03a0002459500004082c84041e00721001071000c6290421460018603181c450921141c032554454102c007072894103405000e1100090114109072107400060042c0c40c0040c510442903440d41d041c8220390120a06180c0030074902404526146015103d01080341d50586c0280300010300c00c0205191144500c40203414071050900100009a10400e01c00260410035500c0002d18110b00f0000c0c030342000a460707a01403010030018071002e81e07030000469501c01d4042c0ca102618003a003e0201c2e02d08003824202a07c2402400c02e460104210520b40360 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 89147527 1250 89146277 89146289
    0x20f0a03081902031009020a200606030717030301090c050c0a0501060e090118080904021b0a020306070c0302060408090127081014011809050d02010b0405070807080406090507050316 80
    0x100600810507082c0101d01c01640e686840d11300da044c080002410340d40040525544910301414641100381c6039030800c01c660242d1040a4000720200201d40c141000000002c1507442800c4250340400c908240d107900c010301500c500035480b00803080c113150243e0200da0741c0c00078820449084c05071904000d0700030300e268011888421402c50110700201c4050150040066100d2100e13061301c0c1903035a4040382940601440d80c3c00c13a80034854208094400c0c8441044800300c00041c1689071100e104143c14200c1c02801c00c020302250890b0580425800103103d5441a030080c11156245000401601d4000401001c5070a8014040300d0414081e01c0c40d11903021a00c2c00800c441105070f07490032840c03d0390040b9845528480e05180100607c5244940490820360050740008203080700b5140c59080c0264483c0f0040075030b4403215410680e0620348940b41d442100c3c1c0c9812119414000c00082040c14081e02c09082c05440f2000c035814401c080c002c10700281402022500400d64400b102026400030b4405c1d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 89148777 1250 89147527 89147551
    0x2030d030c0e010c03050d050a0e1005100b070c06110a0206030406090302100606050a0c021c1208150d020405040302070906120b0903180d060b030a0c0e1602120a020f0a0308 76
    0x90942c95014800c0c1da0a140e174551100e80c101074204803858001e003001045003141503112400c0008180c4280002c1d8a213072100c85001c141c0345002603109801c450079501a1269440c1000f2040118980c580020706580017803814000c400c0010314a40e140c51405040a5800340002090104120035a817001941c1442034007a902c0c045c1c20303240e26200b1038180f07204410204004200d204000c1348940400d4108502c0204091544c228091038490401300001c400c40d0600381803800d405c007060f0044a416400b100b0800e010500701301e0040403403482480c6101c024080c58660000c1000c06009000d40c0000c0c000307881081000507901d440c40448400c0c2c1e42e60030b4541c001c6200108107410070100850b176150001e5180240865284000d010880c156a001610301c0c4e41d6580c44d241040c0d03424011000804d0141c0d80d81d41d0030138148100030314812400350807803c02004ca14246070f14107802240c0c10030070141c4803540503110b0081420a034100002a03c1d031240a000c2d01c1404403c1603081020940034102181c60 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 89150027 1250 89148777 89148797
    0xe010b040503060f090c1c0804030303050601111b010f030b12010518010b1c15020408031324050c0a08040b030f010e0705190e03030d1a060708070204020d0902030d030c 74
    0x340c0b0b0f08030f80080e05c0022840d001041007075014105003e40207413055108100e00d204100c151203100080c1c11907081180005d03103400030701c6119a030100c150929400000c0140c1074140c920030250022080d602ca0f424107100401075002c0780715000347e101403096000941a0b540c250f4020441c2e82c000c040803140c2111040400b0340303103414844148503802e190703c07014203440840403401040d0200490002d0044a4038000ca50600c0c030194010f001034802018000d00440e291500000e115580d800507400084c0d08042c40c610700243c0d081d183c0701074402c0c0f00d81410b080740d0b6001c002c60107604040032224068640e0f0b100140001d846040ca42c011031103840c00c003814030320b0759807100c01c1c582c5a15005c1d2a41c900164040c00b0400066210381b013600200e500506001c00c0d90100f8001103415034110301c000701e5a0303c0d0780e0740c042d84801d4000312445d400080103c90480c6040529a41d441d40c43c090013501a010b2513020a004d080c48220358043e00707c5030b030003c0840d041e840c0c1c0b140c0000c014251300c00c8003600141c90410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 89151277 1250 89150027 89150041
    0x9081204050307031419030306051503220204020c0d0504051f02060106081005040e0c03060c0408030a030e0102070c0b0304060b030c0105070605101a1b060403050f130e010b04050306 80
    0x41528155032000b405492142c0c5951940c40000b81d5402080303050f4002c580341c031808001c2c450384030980c0503c2502c3c080390b100d00e81800c02000001c00c0007400d4640c64104100802c0440b1018039821850001c1076800c1d1000d8240041002801070025281051140c103501d40d00c1180c01502502c00c031142112140d040301300c1e01165240d40426030400b400507038048401844194000c0081e2a800500002d00200b0290307079900240c181c8120200f008050b400565a00300c444c01e003444420f81c48100d82030518501460003207501c1c0d50b84684400c0e0010955111100e0317443e06000e404485601d81c1211141c0340081e1508641c00c0160f00031349080f1501442d01d048100541004aa510510101612250304090141d11160040c2100030700c0f510785031603840380108500880c41e655039400700d01c24003a06d8641b4110038503d4000c0d207942c0c00c0d1b104954800e408000010740e01c04c0403107100300d140e801320584600c1710030b00303032605650316401c008900702c0780c100040780c5050410060022540201d046a41c0c0740c039404c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 89152527 1250 89151277 89151313
    0x50a090f0e0a050c010c08090310051602010b0a1502071707050117010b090105030901090b0403050901030608061b0c030c071e060e1305130501090f02040b0a062f030a0908 75
    0x402c02032403500030050501d881d42c010840c101d20280901140c1b0701d07041d030441c000790a09080b000f8400456959809002c5141007225099607140b03202d00082080d4408000021070780c1c6014811896201c00c28694255084d1090002000074801b203a000c84103140088906030303c458981c01424009488000c007040d001113841400360489905881c1d652605816900440381ca42c8014820a950741d00c2d41610b500180160704c240e0310503402566501d4035001260001429180141d11040c0e0741e50000081c0000d110140d5024a11000030348113903680c81d105c080c0000d041d40580d08820078140110320000503c3e03a51101a80503c01481c08155000d546843c4207940f049681411140c1020110901220084c5158000f503000006007034510f224480079541c403425101c0e0303c0001c40d075075542100b4002c11410b19002c1e9001e1900225424440b15080900050003540c00b8031005c12040d41e00c1800800d94000042c0017100403000205496a800100b04090010700d0f01d8841e10340b40e1311844151000c420285 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 89153777 1250 89152527 89152543
    0xe0d0210270608100e010905070309080307020105150618060306010e0a0e011e06021b0102160303030e060903070503030f06010c020907031e020301080c01080a020409050123030a0f030305070207050a090f0e 90
    0x205c11482c3c0d43d03428500001c00a01c80285140185603890f0b080c0f001154040c000707034ac410038155001194a1500c0001040b0b100c4030810101c2c00343c0c006000d0712a480100d680d40220f200810f4a005482c0d555102c0121a1002e014104907080211402c0100d180b84e02e1440d000c2c103944042d9200007682404510100340d0301c450348640c01c01a0406011040e050316a82c8540ca45804144121021a1421402c4c103481040c650300c01c8000c00c0e622580320321685404d014140c0d2002c542c0c1302850800a40b911196120301c0002c01c040c810b18580b2002840701d07802550780001e042e401502c0c3c000685052031010307008208040c144003c1c40c20303550001030030503004d00890f416154010050705209a0307650042d200c6030f40140a01403295002d01020402c070405204040c020030a85cad00d881040c25840da98503060321010040f8030300a802102c01403000ca094580100b0b040d552501e4005040c0d520094124102000c0741c10466020540003400204042507820420041c0d4a04200b0020807c81806065031074100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 89155027 1250 89153777 89153789
    0x4030e09040f02010509190b0c0115050a03030c061103040605040302100c0e1302091c0209011208090d050309030109060501051206061813060c0513060e0d021027060810 74
    0x20440c600d02c01540704201812640034051302d010442040c0c0706070070401d4201904445400d031404203c0c02c0500300240100e40b044ca5152028001150402000c184041400c0c0005801e2094064001080207601e07400060150b03045111a500c81c20503142441c043c2505076010340c010310507005040300e040003030b20980440050b181c50302901c081c103400900c502c0e07114610044503650382c02c0c0008038058941ca080c090020400c020a800d120007c1c0c81006440744040c0c0142c2c00032810304001100140342034017110444502245c9903609209503250852551284640554240d42002152402c0000e141c0103241604c50480341480044100007401d540c0300c800f254901da2065000ca034900d90b510000801a0300f1200c000c09465229505032100400d07100b40d0389004000500002d0034081c107038034046c480f0000e4000da103042c0e00c20640580c00250103034003640000e1720810911400c01e0b602800381001e070034803a56040004200c11006011101505c009100d01c402107545c80c0d0001c3e01c4001c5080d445010346003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 89156277 1250 89155027 89155043
    0x30f030e1c03050a09140a0201080c19051c0c0801030b06060a050d090c120506010e070912030e03101109041b02030301120807150f0e0102090102121e030c0304030e0904 74
    0x580d41c90440241c58094450382d01d1983c0d070780b0844089011103848034440d42c0e082c8014030407461a48001420040014010340c40707030030305220054100d00d04840f6400422414a46075403100b46220b400207010308607040c41c0c0340c917a1a0031030300300c45150498141412a0b0140030022166659001070000600c56541300308001502044014107086c01030340f00415140c022142002141c0d00ca24041588030601d00e0290360a031f0116004100c4001030400e902e511101178506003040525105a00318071b0104554000d007840001e160f241d0701078404001d0008050f41010050004500f07000070004560301414486010b2800c0c0140c80c80c140d060420b0140030304030240e00641c9541c3c030707184c0c0000350303580000300441c1c00c12400c014080100e40003c850051100024900051080910381c0441c100d072040d45007090345034014090200b49a0300443c020b42611038100c049036889924004400c82504111181a0840c40100c1405010b80404028610842c032907110034242c901d44904108a04404480051000d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 89157527 1250 89156277 89156323
    0x50303090105030a020403140a050601060306030f060507180909020405130803011a0706020d0e1e0304150201060302040608010b010210050c07060908070c06081005090108030405040504030207030b0103030f030e 92
    0x7520950055520071a01c460041c14903440e40e803012000001c0c0c040c5c14520340d204041301c3d410300c0001d008441c010049810b04000c200d2441d91a04510040062b0141c10700c1d50700c10000780003074020f80f0504004401c00c11100364042d210340c2c00c14002c00100205030300443c500380000744601c2c810000f812580d0340001341641181e1070012080e4008071001002e50300140140310710300004101e8000303031603000d0398804049203000808482514184044449100020b03410510240f2248003000710f505032058401c0d20400d08004041c282c5c0909540e40c8001e4020303182802c001030524040d0b01411540509074252029030400740b41002c01c0d00ca09491140380900200505000509103910440940d4410f080301d600308607154032661080ca02a41c07008002c900c0540401c0004920003c0d141302511086480029950510b0801a600d01850244901842d980e07008941814002c220b01d00085034022222826580c40e841d00800c103036400c0042c0400f1a040494a03d941c2ca0302207413101a18000d642d03141c80030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 89158777 1250 89157527 89157529
    0x31e011d0a081303150614060a120b01090503101505010504061407110904050c0f0411070b060d02130e0d0924050904060b21010302030a0b0903040b04090c0e010905030309 75
    0x1550103075100302440f610402c000400284c004d0070020802e2282400040c07164070701031040841c1c010160000e40700b80c408011108415422541510800e1000e00c00042d500c0d1544006a8075102a40c1200d41e05118105039402c015035190070420030448030310700c4804820307540d100564150096014031008207800c540390010340041100070700a418050319007107200ca58a00042070381c070741c4140e40c15501a001040c417200a41000c51031500c0820003920100480d004d4444044440d008141005121121035004260740da43c941000803100c0e60014002d051150100c8030410040490001800403030240c0c01e22108054000d0041d042121000c00c49140001c0401200601041c007241004041c40000d0120880c6c507207440c80b0b00000b81421010280d600c5c100003018200400360710802d2a080346804006100686011452039115903214a0300340301a20307200c0030b141c1140150303001044a0700c1c0200f00094084c95507040150580402c1c0c94400d40b4000910045a00e45081d00540d5011f910130010300d03000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 89160027 1250 89158777 89158793
    0x60221010b0f0715050403050a020601060801061d12160e0106170c0d090c090c03150302061207021005070e09060411090f01030b030f0304030308090606010906080403030902031e011d0a 81
    0x2241e04c81c0c00110303200c54201ca2840205c0f0b605903000e40004201007520007207641c0400006002d040a42020030b195031500000804004002c0035034200112001c60300d42c1c10b51a0710504203500440b07030703040d9000b18811103c494400d28062080210307500d803403800001c01e039000344054182521048608442e540c0c0300010003000f40d104611503106240e64107031003004180c2a003032000161141e200d003c9940440b40b80d005041e07542c510b0201c08910035084003000142d07a60f9044950710b0808038a4503110755030723069043c1d06081c0e00c0000e04405500313220411400c540e1003078158070300394422a440c0c5450b49600c1c060001700c645110100009901c104101d928601e0300d80f07020203913844c0504d80070540d03003c0580403904240391a841c0c0a4036601c0030038240308044d08600401c2c0e00440b0b4000401d00c03460100d00092200324248101e4085c00150800316051500c613030040000301784c02400700e401000000c0111903611600f4a00c030101940b921020058075010107220409481034900103110402450b161020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 89161277 1250 89160027 89160037
    0x603030507021c0215180418020906060d0207050a020907020109020a05091f03140d0f0f0309020103020c15010806090c01020a151506050306130c0210090c090207060221010b0f 77
    0x466800045a104011703581c030009400b503102c01c3c125564079580c0032082401d9522400080d18406c07402c10030a4060007406450128410341c0441d0480c2e41901d5100c04075140344203009049502c1400000c6000c184a00020f00344055882981c41f00300ca0340c1c810b18100c0c00c07610f207100000c0d4005482d030340c20051803415100c05030f003001d01a0b40d03000c05ca158100e492981079103140e00440e6150103500f11110120f4050104c0841180b89082c07100c8043c098800003001002d0040c4c01200341566218002b080d64483c2e41074808402c4540115480d144400d01c1d0a64005824410142680f103000000340c9500c1c0e01141f15506108103070018060b000e07440e90351641400c0100c1190081d182e0f280c01201300c0901012012006060356101d440d03490030484d0a2210b030030341c0c510b6182540303800c1c04002c800391940004e103c0034404001800107281c2c0e241c1d140c442c80422490b404401e01500115044041c00713016401060f5241c000009494160a54210b10444000034420304501d0b000600c0203c07888527507200148 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 89162527 1250 89161277 89161309
    0x301020c0f1014100b130b040b03060a05040b03070608090c0418050606030a11010c020d0516060e0a050a03080c190803010602210901050c070509071e03060303050702 73
    0x1500303103090544000d00c0e0400c00101c1c482280c2c0280706068031080b151080701119500c0300380201d11460001d801d0003c00905115282401000090400714003035030f210b20501030100c0090566540d99035000d03c40503600f0a4400511480341c1c640c001850340343c24411645103100203006441d5030703441d1083c1070300d030003030000c11040c0c0e280100541301076243d03101c4c820b40e00703120100b10006080d00a1410080d01c1c1807001080c150180d800030110381c1c0840e888070706e08104c1c081c003440c11110b649420300c08180603a50480d001060351058006410310400302221110549943d80d80f42c7c0d580e01d259104100400c0950b10515070003240f485420b20204258100034640001840c0c200d4401c3c0d1040c007804401d2152042d0700740c0ea0408040010301006a040c04808e5424502c1c3c000880b1020506900c00600e2040c01d603440d0501400080113800700906100f81001080014060300c0185060751014208402000c0c0b140e01001c80740718143d94060180c41104143ca4142d0350ba182841000d50a0206080f0980009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 89163777 1250 89162527 89162531
    0x150522060b0a0306020c071e090e03071a01050f03010b060a030504020d0c0b07060b042a0212030c030702010e15130c09020307020d18031a0c120c040602100c1b020301 73
    0x1496007a121102c03481c000b10300c20180140e072880b10f11403441c02c0421941091140354214540241401071036072182c0e064441d074420010b1070b40d141c2426945140300d96800242006000840c805010503440da08504845c0251500801d03810380c44200760807220b02c0612154044c2c818040d0a1a240c881c3d8402540b0178400780001d07025441c0758403604d444000f680e0040c948000000b40075010003140740900e01c0d41000035074041c000817030313260744e244180c500c081c149100036039a0070100382e40c0b544200004403035466a10040b42d52400d00d81000b150652084400e9000741d030810041e03400080740025203c204848182e0780d200c070341d110210034080c1c404a84400f138420110f07618001c2031400140c40294082c1c511a0010907800e07101c02000382500d114071100c0d00d6140d90311041000881c6d00c418442c49500070300b00500103195a10801c4001602400c032000304110002801c0040d0f403c8294020030945001ea022140341c206510b4056003542ca040ca40c441c0002c3c06a00192a02006400140300c224401400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 89165027 1250 89163777 89163791
    0x12071509051207031e02030a1502090406030b0f07020a030801060302090109090c020a030e03060603030904050402040204030c080708010f0506060403080c010603060f020909010e0c0a18120305030415052206 90
    0x540200c01149600e0800e803c410010001c1241c2c0c0000398104c003031494001c0171618a01e0300080d84070a40700030301030a80c441400b003100c0601c41c3c0d54101c17170902e100108100440741e10f81c10310310041002181d40040450010021a40c52800000c5441c5880c0d850340e920010740e800d1420803400794011506803810b008800d1800f164003002c42c0241c0b44140c4a47c2e004101c200b480f414010060b8101400080c000c1d0002800c0c030203503403808000c607140e0440643e030115090b119440071800a118031b51000e08a40e1171180080364000b00403640c40100c6012100a00601c01000c90080031074506481060780240d0030042000051198005403002d604182e0000507140e076240c6406054031880344280003269400140b00c0b09524011044502510341e500c0b659101d40703041012100140300b02680c4006001c010641d00b003c0c1c0359200054005401c407012059000281413501402940059030116036101c1842ca4114410602e4400e05109505481d002d212030001660b0860401450f46c0b0150740302034942c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 89166277 1250 89165027 89165029
    0x60c070f1e0c060e1f080c1303050f07050111061e06040e010507030f0f060b0703050c073201080f070f02100203010f05030106080d080604020a0c140a0507051207150905 74
    0x80c01c01400f41e900c80c0f94000c0d400c6000c12410110b5070340c406078290140c00702d07005c0c101c0c0e000e19150b5100342040b203400d980d10705280640600d200d803540001c04620910711001c0744400040b50050423200203803984001d4848600c44135803201c5c42103e141081504100c03545480b40d1500d5000c1d60801d0f0064000a503200d103145a160947c2c20488a200200791218050900c49505100d040c44100050000b08140c0c3d0801401c00c030f041c414581c01030100030002c504628960780901c0254000c003a015200195070b0000486c040d050329100d0131104c403c40031821640c410354018410188582d1120003210b1050b80d0340d0400341d400848114041c005c5109907203260203a0900c0e440114040c040c044002e51086142000300b41c03e4a21300d8006400076002151210929500100d20700c1d0400c0049802681700d4400c01d9088841c40a40100500564900f051403a0880301c0410750307040c1030b80036a059842903900c074010b10200c8106010b958149a01c0380b8400c00c6110719030854584410428a40740324001d503184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 89167527 1250 89166277 89166293
    0x403170406091101140f03070e060a02010b040612050d03150f03050c0a080c0108070e060d0501030b18120a110705030609030406090f031509060f0e030a02060c070f1e 73
    0x440031240203645a403001d09000b1240f030080d00d0b519003403030003006141070061182d840307015a0403040309051303010000c41c0d4164000d41d0550552507001e00559100d83c01c010300203000c1c01d449654240039618040d000325100349440d245030541c640100041000e01108a003c400401201d0009041c41c0015600401c10515000c07640000b0750040d001480400001c030701700000418694064000713a40030300c03899501a60400304880d406102410442d605030b0011000c2182da00c91400401c9032280b8150000c4100000714100f02e02803400000c0d40850090a005c145d540c412620b403204504400c203202030050a0320520700c00d40e2903e0401c00f540c070400d60300d034046890f02e50203071004010745d040800c0900c50307035503c03220000040025000d000700072031643e103440e0030b00d003000c2d10321008107a103410441c0284400c40d00b00f2801c1c0c01ca0708000700f10041c1021803a1303880c1d4000442031001801081c1c007040c16104840c3c107440441d0f8100d03001c404806020f41e502c0c0034482c0c518102e000484180110320010a40c11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 89168777 1250 89167527 89167531
    0x901031b020a0302100905070302190e0a0603061d060604020708070602031305100b010807050c011d0d091d0606090d050d080114010f09030b190905101103010806040b040317 76
    0xa40052600b80d9541c6400390600f803204011146081c5040204004070700001602411240c043da0100940c04072070018800020f041e80140c00100e40420a0006003030039544680102d80c0034000401c10300307a1b4210000e007200c41382c0d100d55005501181c00705400d0702c0e00d43e0040090703601c5210340c5417801c1c4045d03a400d400d0360821140c030390020050000d50810700c0000d200d079134a18100c1f06010891610b040c00040c05200010304030404024000c551000240e07025440f4140e02009006010400120b54034200d6403030000f2031800000a072032440000d142003074074000c81b02c91001c828190520f41e481c4810701c412508038040441d880303004a8031401c04680b042c0104242d03400c00390f8485071250b0400c08441e101b0701001c4d0015040114a1881e40544d42d84803822101707680c0c0c00080c0303000f03d0704c49607078444d94055004a0060203900e49802d1400308640022190348582c2c460324140034614203054210b08030f01007440b80c6011604030b04005000941101d145640c06482404e203075407074110302e40303140d40c80941c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 89170027 1250 89168777 89168831
    0xb340b0a020703030e030301030503070609140a150606030c08040f0f021306080c01080408030412020c0a0608010f0e01031a06010210060801020304020f030f07060813020316090b040903090308090103 87
    0x1c00540d80040c5903060013902c2200d49040000c40c0307103502d15a50030f03a880c480c801c0c006e0241a610071540c03080188030303282400700c5510f40044444178041030a0480705040409401d0040c40d1415000007082c0d8020b001d058616050340c1c5680030315a03580c1e1200740422244113002c440c0005495072100040e030b00c1c14010400d00f44031075000a0312070b06029242d45000b049a80072030512404404010025010703c00301d0b07520640c40025500050b031448002c3c0e2500364000c21090f844440c000300031034403c2e0702c55619030490320000c03044021180d42c1d01c4124003049084c00090096841030b803802090340e1940340440c0d04440184121250050300100315001c40c0d10507000240395075000402d00081d8607181021086040046000c1c000c50380414110964031140c0e4071502c1d013030002c0321000403a4980e4141009030750507006401d503204603e0600c0c43c800341420601900c0440380c80c00400703514070304162080310805581030300d50440080c00d6031200039668000003285410540c9030303943c0c128000b9590f180c4681e190a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 89171277 1250 89170027 89170031
    0x14030c0d060611010f090b0c130801020c0a030201050109090c150e040c030c02010e0106141908060c03010f06020c0924120c010906050702090402010c020d080c0d08010b340b0a 77
    0x307043e010300b0b096038400c6403211415818408180080341d601030f42c4542064140d81030301c0d620f40e6443c1d602d110f0202c5d140d1201006510100c0d01514003030340815001802031081d8000c21481c1e803070b0088001200d220081c06000760b40c0400e002e00c00004440c0c2c0107800303544181448850b0091001c006001d0364906402c010021b921403604025154090280310305003241c10b0000d11129060003001503040500140705031091122401c01da40702c00042244101170128401542c04602d00320a0310348050340280300341880c5900c840d90014000cde10104150b0407042005000800d10b440c1d5035502c00883c46450000303440c51409180c05000c981e00c0c201c2c00b2900320b408034054041900b41c0c100240200485610040c144402040702c00010f03a95001415442982400c002d8140c00140c000701d1000028808018070b4000c00044645e24281c000a0701042c088099a410070181c2c5c98000c2c1c4142e41c05039a10403642910040c288a001604504019410102c0d00c080000509055200c090902c40c054444100c602c4e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 89172527 1250 89171277 89171297
    0x60f19030c0f150c0201050d02070c1202030708060f040201051b0a05010f0510030201021011040b04030b0a0605040221092523010801030b070c0210030212060a0614030c0d0606 77
    0x1100b500100c500401000e51072140a0000c0e402c0601080083c220080c10400006403181e039800c0980d0603901c1e4a40c201c00d40c00c0c2c0194441001c1d09060300b0129042e4824072680b4000101c0c44000540a4410304005001c420103880350303030041d251038200304400400480c02d00b5200c09503680400000010030b0244001203012900034821400b241c0000d0903101e482180c070713041400583d80010b8080c5a82f0380d0040000382d0302d1641c4d4000300d800c3c0502d800c480d60128000030000280b0944081c00381c01188442001c02c0000c1d40c51040008920400030840455134840c04c03000c00d002e0140c0407281d4481d0340300e000d80d0b10040c0145030300030224019134136940c007650201c0d00a000c02121030003003400300c1000f071400e5a1641082c1c80042c2807410305100052401024a0025640d0b911030900400c100c1e85c05031030403090b041070384006000b0350440442c100621400c0d0300064018035000c242541101c149840d4000000040c00940b4041d80c402895000801400c00c03c9450900f0607101e810003c2c01590341c1d00d0318030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 89173777 1250 89172527 89172539
    0x90209130b0703050112030c17031f0503150103060203060a0305030c070e090d020312071404180b04090c300b090d0c08040b21091014040506060f19030c 67
    0x2280180141d0101440d04c0014800e10368205202d035030154140c1080c10500c400c038a4000f41012052540110784003020050001c0441c82c503c079142142d680c1884010303c180c5490a25a480c10041202d4144410000040011409a0b401550416405040100314540301d4071584d1540c0e210307082c1c414103917001305000c11141030111816501300a00001a040307103006400025a00d01603061500d2241081001282d00c160051000c00c40003041b0100c81912a5612418005a8420020001646424802280315600d4240b00b03464007690700c4003d0204c4141400000d06103e400c1143c0e034100054641e140c0311800300b8441e6034400042c4264150400c0b450068481400d141c02c05190909200b910382c0407400158400059409a400703140e106903c2d1090240c0717070021300b01503007184400d08100405100b4100c0340850400d660402040c400e00c0f4043c441070640f201d03c0c004075000b4186400c44008a0390034980f0000070507281d4030050520901101c80d8103218010819a8412075424841c20010001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 89175027 1250 89173777 89173793
    0xf01090c15080912130305120a08090d090b03070e0612040c081b1c02041406011b02060418060e0903180108040f170d06090207060f0507021009020409020913 69
    0x388041d42e00d0000720604180720b0040c2d80e4602032225251140011035020b2942d1080d6078200003c607040411078106041500003100c0301e6020400c41c200240c850310000b0038507400002c0603112540c1550300d5654081c90505040c6071a040138010350308110030328502c101e1a80e102d9003e0628001010035401c240d0515241c4030507081c40301d03403040c0d9880e005111010481c2044a0382d180c84280103603603405400d40140b0b000843d404000c01e000b58003614040481400d203000080161248000303032904a00c61101490064000d500040e00942c0100300308401e00007030540d5000076203404070141c0302190450f1602c002d000f2082c0c04640c680b006510215100d80c09050b104a41d8055800c2800d00e008142410345038209450745140025103c4043c0c4075441c2c1e101800d110841d400041c07408406c10500f074403504800041d601100301681c0c01d504281018100c40101d00c1403501030b59690f0010311450440009001c00303007a021900340c0c0d11981e0f0742e0342000584c0b11100d0f580c5c0300c0d01141c4180040314800d4544114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 89176277 1250 89175027 89175059
    0xd0204170f070e04060509100203070203030402030115050a03030e03100e03030723030412020a02040c0f110f060f1f0e0105011d420304030207140105070201110f01090c 74
    0x281d141e00c2007900b041224070010507150807541000c8085005d80e00c01c84002d1401005a1540c0c0242d40b001007080399041d808000340d400f0358070840003030088002c0c520749070303800c00c5403401015440b041c9540c00f040002e00490445081410103000c0d01d410000980c00081114403088141e48141c000002708510a64022001d40c40c2401d104c01d040c0f5200d500742d28a9405000c0244024114111032130008419802081200c011a50042044c840503078241da005114250081c6640c021a441c90822500c2e503402003902584005500000c2070300d40e80380403800c065a01c0c050701c0c4440c40d9100040424040c211154040003900750207185100b2945401c00050a0b03c032801620003070110982209501c81e9107058030f20b4404504180900000790b81400380200300d1f1030b2801d42c41d400d170b161201300c20701c1903004d00013440c030403030003502070303810030780d5605081422010f0320320146001a1003000703d44019809203a02062060110007198003010b072059000b0b00b120b1106000350f83c0255044020840d000084004003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 89177527 1250 89176277 89176303
    0x801060201061a0901021e010c20060601180b030a0204050a080313141c060605090c0415050f19020c040b04090201080417070507091401050a031212020d020417 70
    0x82154500203800f542550f4028006420b0b420000f000b09540e0b100301710303d48250a40d80c190451060060601074001c054115010000c01d180c1000c2006400350110062800742c1144003034210b580d281d40045810b51601134159001210ba10000302d01010024080d40c40b886040b080160344a05040810428100e1503001a81c250b2003040031080d100c140d1804c80c0d048a1800d170301c83d074801e0701d05030004001041c03070300040aa4020003901c200a000b2260000021600c0643d1420025280c04030040031340e11907801040101d000072000302142c070f4414402404401304000144d4248406c40b9a40e1103110740180b19607005030311011100c0d20a00e0540300f01442c080c42201e0400c04079541d50700103414080003d0000e0984030048000c48903422013102119615030f8420140c44540b41c40726000030003005440c40307000d4014210000400c0c1410883c1380a003d0307c0e044000c003605c0140140b011500a0042c043d02b5007044c0c0c003030006054000c03490018101901e510200f51905400ea0000d1a2400c111a0715507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 89178777 1250 89177527 89177531
    0x4060606021501150f050903010212010e0c250203030d06030515010602030307170405070b070807030e03060403050f09040b09090708120a0f0c1106040b070605100501080a0e0f030c0703030801060201 87
    0x400440d04140d130503030044800303402c01803a5092030850039039543c060900820b0701940009444d00383c403409000b113103060b107515134146803050f2541015030b03a4078014840c171880c14010201070316440b444c0d200c1d5082880c9100800326440c00307580800150035205d1551040711954009032509052020803041e8034098116440218103500d48540e005091003401e01c1c007418021075405c00700d82804030500815011f008c990305c3d0503580701650b107410a00d9502c440c0050707000401c4414020641d00d0003003a01c600a581580d150f604104100d000508164130080761701d035110b952101032212a0301c64410032442008a000a00340c41454040414107018801c241601200d00c2007105030a810703000240b81901c0001854455000b10380c0b4582881d5940c05c01c3c0500780e2282000c5800200c1e040640000c01e000781c4107000501c5184c43c2e034800b009140388140115404191040700051f010050390348003402502e600d00403200d000000840319401c6038032400114140d0f410260060003415000b00d0380c01d004107094402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 89180027 1250 89178777 89178779
    0x1207091508011811010e180106050a090f0f0510030b030d0206150402090a06051608180a0602010903020d110313030609020118030506280203160f1409040209060c0604060606021501 79
    0x203130710000c03e95003035600c0c180004544125542d850722030341c0d03035246001004004c1741561214000b03862604203060f4080002d0320300b140840c841e0001c20200c0103c4076000004604241000100701106041c445a401016031715951071006690030025110b0850340e80d005010742c0d0038114840ba0001c48181c200900450040200003003944990301030200300d44c550301d03102d030705c607098065584075032559030802609400c4003103107061403c11082551465078402321020783c03146030b80d940c0c241d0a9035a42c0c080500540c215071540144035000341d2956088000000503286000e84c0d05407031800d0070004da0800d441050f62802d041d4115600440c038425030b8a0352091800803149140d40301c566a11004003508640000d040c1d2071a40310300c100c0d02c01140711244200079501c0345001000b1036064070844010b0400203c0c0481450131780f40c0103242d001c02c1407500407940c40c64103040400703010180d4015901540c008104101c6550490070500a030760280348120740c003003203041c80e10500074030f00030300c2e045a1015012200c0c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 89181277 1250 89180027 89180033
    0xc03060b121f08012403081605030f0f040906090b21070527070305150d0c0b04060c06050f0c030a0b040b0604090e0709051512070915080118 62
    0x4140c8003041840000840596151240580b075400c6401100c6486501e4080c0400c0100d81900280605090365940c1400f080a8110f40034200c803182c8405803060b03004000e030021908003602216032041c0500101c0f498031400e2035071078104d5400400700c0f44a003000031400388407000b0076000f02070042140403014400000102c0005402c01c40c8120005812581d01c9082003500c8014052040203041c000c2040346981c51141056500c0c0240f86110114114120300044a10780a441070b140214102003100b12091110818414a1000000d0a803220641c0c000d0010703d00e1071000003080039000e1651528000d40361441c0c91000d440002d0881000000e1001c108241540c113141540c0e481802441c2c00700d11005040c000c500200860140300790031600016002c078820003540c001150b0800c1a5040700c03a09559118a54200c96055984070b0000c0c40e006110011885d106000950f246080016a59000c0d51829503204450004655140014240c0000c0044207028460003404904030801114411050340d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 89182527 1250 89181277 89181299
    0x813080f0a03090c03140d0915050703050408030c0102071208130803180607050a23041520010b0a050108070e060a09050d08030108070b07150f0e0114060102010c0306 73
    0x400302020140c03010441410452003500001c1d0000c0c0c0040c0921081c40c0c072410401802d42c070311000c2109501c13400e2117441c0c1c00c902c00c03030488040381c5100c80209290349101d841101c099000d44005d0301081824000418071106c00d000514200007841d00040e0ba0394800d241001c0301141d0701c151001805103202c20450385100800c80c9107041e582c0142503e680c1d5480c404080d4801c0c1e09a90000f07100e108450800c50306a0b0058000c0070b40901c0e035200c1000d880005540d092000680c401400c5c2c2048060104000344850881c260503580d030ba5080c9011404600d0300386000d01c0740d40542900250307442d4010502c103410b002c0048400b4140a01c0c0c808410328025074040c1211000c204400c4c0284c100048600c07046125000000c05840d004000d1030541a0074102100380ba0028001d6151501684070001214103a2070708540c10158880b2244042d59400038084005009441007030310b1058a50100e050401401c0c40790840c4124009400b0707150b41420f100081c21284a03c6800007494540b800c02c0c0f01140c124 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 89183777 1250 89182527 89182537
    0x3030c061603090516050a05030f1002030402061e030a1406010816050d020703030209030f010615050705070f0e09060105030607050403060506060403020913060c0f050301030303091b0f06081308 85
    0x41e4030441d0606901001c201c00419003100041e041c0d004101c04070305800c51a680c0003044a1040307503808804c0b900c620406031200480304078001960307c043d1500c1d2168100c0e4000e0b542c4507000410709803c046004046105281c84000106144000082000030300085c0d07204260482c10811a140b54034a050700010303083d03480140581c0380c00d810000803014a288a0f00c00c80c0e40c0340001070401d6403160300700c6c42d029010f5049922868464000c003126003183c0742e0f0500c1035100300d800b895a500c0880d20074120680384c0d035100a10075984e9000e9100041002040d60300c40d48010001d4030302103503141c60030080243c02c1c010181c03c401c2c0329401050520a1845e444016241500d4000704009503648071840021054800c9a0000b07410212450401103001d480400481c0b03000d009a400b40440100c03500112002d645900c1d003000880c60920051002c04e121741e102c0e90005120f04d100b10203950980490101c01e0420341e0040c00c002401c038506011550313200003082d4205030781040140c00003e10b581d03000c0103401a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 89185027 1250 89183777 89183791
    0xf0304030b0f130c0b0c1203070f050c01060e240a030c05010f02010b10090305070b091f0e0306040c0501031a0a0603050907180b040606051309020306030102070b1006080603030c06 79
    0x1440b4085510b901901e030020802540c004500c10400e980d807180c02c01300e40c00140c031480c00c6000c3c100300b00e6407010909084a1041003940d545084400d83d060050310160800c5809014030340d038070000892241265600c090140d0148402482c0c44042e8103040c030711072290f21740c206005d0035141404000207142c014400081c0d9109003040f04e0400c1c07030703030408a00501c050500b180d80070280d5400c030101342d60400603031010383c0d00900945000c0d40e10365034150071070320803201043d81011f25188550b1030040c00c02e00241350350804c2d180079480c600c4a0b00000385400030036102502c000341003003000c103d503617010307c54035051228001a24141c0e80a00e4001490340381613215a005040e2203000240034000144410006881e10030340c821100c040c0e1070081802851032204c52400345e4030b00040411042c0c0030740d0595035051041e440031650541400ca4003406500b000e480c0d10340642d000d00c41c010029898544691103280082d083c15619450b005000f056042d024284c1402038108000788401e660300450400d0348146 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 89186277 1250 89185027 89185051
    0x60f0b090403120f050c030106090f121e083c071509050a03090914090309040c05091203030a050106082203020c1305070f0207050105070f06061205030c0f0304030b 72
    0x19000500c03c000d40704664005007402d02d4601001801c41e0341c0320156041c0c4002e503548460341034a59401d203891290501459150101d45040580040c0c94590400d0b060001e81c80105c01050036680c0f409025040110385011a1528807945003102e20050f03c11407035a026400304c078072100c0341050301c0c200c41e10820501401c40c452040d10380c103c07142e00d504003458441d401821128a88110709004100030803070f002e8150040e0901e5159002e00c0c8865405600a084100c09145400d40c940200402400700c180481e0a101e0207103e00740c810f656051505252400d0b6002565072403030589094422075105800c00e405100140d414058180300703007800c4036140308288800601040300d501301a450048480b03a0350341c0c0300312000c980a80144280c2c02040c05407415441b00f030342014405100780e860300b50703502425000403824441c8601150703040304ea50300001c0c01920001501ca49a040b00c03200040c204005540d582e20000b45984000c104101c090b07102a90300c00a113040609603a504030104202501c0b40b07074212 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 89187527 1250 89186277 89186297
    0x1120f060207050a0b0708011a04060503071101020301060c02150f090607030201060801020304030c060515130b01030209060d020307090906030b04080702120f010519020708120705041203020307060f0b090403 91
    0xc1815030484840c660480100c03a00c001c000e1900f50764048080740c3c08000100c402c0c00014681007101d00c040c0d00145410300b9141854140b40044803590001411103080041c804070302036068800380b0003140600150b59540760102294010320156031005500300510100421001c1d01c000c0d038000603200307521411282143da506150408902420150700007001c0c035440041032200300354101481c644031600c10346e0244180d070ba45011940b10b00c0e6403104016000a514046400c81d0b0825034450b456083c2d05060041c1040003801c0030603110341010b40300348015507000090001d003503040420f8800030881400103020042c2160f8984003070500290006001d8000803e40310110b641e61403031094030991750411129401200c0c14014040c000030f8440c0c00f4040c08128110080d00403030b000b25101c241e001507055240800d090100309104000070220b8003008018003002c01c1c8401e4500100300d502c3d020307a00a60f250f031618100308040b038030000c3d03900703001074a4a00c4112a03a02c50b1800d195009400d070034139060f10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 89188777 1250 89187527 89187533
    0x181b0310020906070b070c060b0102010506033301030506011a0315040203070c08130501090506090307150903020907050a090605120406090303020408030a05070b060118030f081c020c10020301120f 86
    0x107005444c001002640d00030100100f2643c417003d82100f06005e10424001c80b5402d9005a0803100c0c1520025050782010200c1c18000303d00003440d4480b0841d5505074180807028444403401c41200ba003080740d44d9042403004011901e00d151008004590312409140345003011460120121540e100c111301440c1c000c40082da546024495a100c0d460300503040543e140c4009403144040303480c40c040c131404a802740c0d0001c5641c3c2880c03816640c1d11040600100011410306108191030328050031002c0401001040202c01a11000e000030b01409040d2142038603080c13000006040c03154a42c110108004081c4651042802480c0d003240d00319401a000140340c070b40c0d5040881c042e214582040005200008010803016806001002000d0107440010704e01d072100001158007118081c0d2546922081c61b20030300c082084003109000c00c500c0b88507807519114848802da5071b0090501c039410074984d404650480740010610429610b9603540d14210728540c1803070300e407094185d01e40b40090308900d0520f01d52010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 89190027 1250 89188777 89188789
    0x10b0d090813090905010c05091c08071e0b010b070803010e07031b020703021c020d030f0315170c09010b030703110f0403050d1107060e09040f020405181b03100209 72
    0x301c02c5442c020351000e80e12440729070f014000c140b400301c03036039841c5ca030a2118942c0f04009881c00d510001b4407403440c0c150700b81000b840074407502e9000d554282007008982c00091103000e1240e012045611014698411800e01c02030381c0720705030b015a0b00d0072420800744002650309002c907810345150201140d1640c5804c4030071002801107481e6480c40003041409401d642d034001070a84100c074800c40f214280e5103405401074000b0080044001d400004035842c250000303016218802090b4030605d000a221200d1051500c074202180c3e100541000401c090a20819028401ca6148040945803501300d5458481c00c0034003440000c02c801700301603035054580d000e00c2c18682150b040e201080c2000ba2030350b07240d0a0880e00c0f480303000f01d080089010381140401103a03000ca10241200d10720f031106c40b640b80c409814008020300040c0119429008412083c00503911032003124000e8040c8202c40100040c0c2c41030641c0750249052030031010780b00b00c07110010711390f800140b244c900d241000300168a0751490300100d90 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 89191277 1250 89190027 89190037
    0x6030a0f1e051608160306020a140301030b1009050910230408030a05070908300d090201020606061806210903031b030c0d1a0a12050c010206010b0d0908 67
    0xd100c205032800707507040c03100010321500141003655002e03961941d50200700c0d9854121124000000280c5002000441c40f50750140405140a0030226904000300e45c03401c0701d40c3c0c4240c00455024222606000c0d003028642421400741602280420403800c004100e56234600c81480940c55841e1600b07440b00f901040701e100d904221462034800d8919040038a0500b0140d001148d03198076040c074080c0010400b600c102511030440b10030300c02500e10303140e0f22a22103036124981c0b240ca1444851024202900b080c81c071008001c9031205200002e440281c1e4400203013002c40240216110300c005101003030001d018236843c031003482c00854030341c1da4403007006903030212503806108e0b0b030075900c1400010010040004401140701d46448442b007056405078403d2296640402d90344000c20041c01d1041486041c440e0b8444100c0d003480e40c3d51080f505581c03000050a00c0d00c95044100c3d48103200031007100b0403070204880e55408a01b400030784003540c1082c01d60901d038041c86071403404140c2c03500c00300320500040e017080311 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 89192527 1250 89191277 89191313
    0x3070f12020a1709010b0d081207050f180103020f070b0405071e0e040f0b1f0f0303080c09011101230105040e061906031209062d0f020c0904110a0602010506030a0f 72
    0x39036415623420700c0d00e4160001001d01c482400d410700001c1840d8824402c03940f201002800c40380c1444d901d024030301e0f03a5840350b605e281d0600d5820443d015814440c4405000c00310302c10a400007252900b0b180050410301c4940c0268a01842030010412a0300100c00040c15100301d140c820005554500300600944201040602240390240c01d03c08890b100680080c04807582c81803124100d643e034031092061070380c0c2d032101400240c03404c0007248503812503c3c000c01169105160280150895803012400c40b428649558007101c3c05860540c07000c04100c2c0c0c039500418048030100042404001c4c038948410300108141001000e0031010204000c03203a2000001d113412502100da2461036580c00780085076980512004180c3c05610301c03040d145003080c44400281c0d1200e101080c41171205090f10515a80001c540c02d41c058a004060180c880542c1548114040c1440fa20141c1c0c03d01c05002c400c200030380001c000c5904040810600b03440004500c0d2090781d100700c0c217a050b032416050101e81c200c81603403c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 89193777 1250 89192527 89192539
    0x9032304060c02031f0617031216110f030a140c03070f0c0308040905060108160c021c0602030a05010f0608090a0b040f02090f060f0d020d060f020405030303070f12020a1709010b 78
    0xa03611754011544084196001800b00f0500500305404183d0750340100d514034440002c0890018410f680c0049210070300c1c00c440e0a1007404004c8009495003840005807010b14aa403010464650207079012002480000310014401d2804022035480d5490703110b094400380001c00f0066010f42005011600c801c025a001504e0544036030f26042d050300540404d89082e800100c0c4203001c10301700810213600c002d00d40744a0b21444080003d07582884106880900c0c044001158000f0072008240180000c610941550f140090190304000710424010519088481003216910410189080c000341c511800c0e07800c011002d030aa5681d180001c03007c5540d0200a400220120500405000d10300c01c680c012401141c1c81c0e400c4494003010311072081300f10803001e076102c2001c44142c00030820381ea02400030b0407040840585800d84a40100e8030b99482034810000003250131524080456100100b40b2071842600350961a002d00208004c011213490f65001c0c4402100b00f000c81c4606001750300010b018032002e440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 89195027 1250 89193777 89193823
    0xb1e0c030f070c0e060d0308070e04060906050a0b0a020303070509032b030605030c0a09020c07030b0f0f0702010606200114150909030a020d081e0a09032304060c0203 73
    0x44900c0769001a941103a040840402c00710b100901c00141034814080a00300009004080d10201e480c140f01415403010312000c91040c032825100c5008d00c5015164500002c980c0350700d0314090042004040c2d11020b40000244168001d0301d40c08011250010310a00c1c2694541c003840002a0800e864090030021038002c0005c90ba528440c101d0030940032332000c0d141000481d82d1a41419110303c8400310350f83d4010b24405050084a0031580a00340e000000022590b05036200e50f01e041003500c060b0340750441403600000304844000e80d50811940010740d0700c0240442d52511701c01502c82161903000f841c4080700781700f610000d007109502510001944402071039403410440500c0101410b20200140104001d60009444000c008101c034841e0b040b030790040c03451103603c540849151402a108581100401c3c0c81c24060818150000d03021b001d0700300780010101d03a281340107003807080820360000da11000c00f140015220000002c1e202180c285040c94401c00d039081c80041d0a10350703240c0411850340381343c01c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 89196277 1250 89195027 89195047
    0x30408010c120f0e0d050a0e0301020d090b1e13020111011505100e0f09040507080f0309010318020d0201030c05040504020d020a09050d0807061503080c011a0a0b1e0c03 74
    0x40c1c01c610070980c0b05030400c074021001a080341580c07100300d04030135142c1c0000c9040580c10711490091604031054034105104580c0d140c0001c0c00e9a100305000e82d010342d1110300010520482d19801d58004540e0142203d841c00541c14100380742030000c0c410810240601035820079a40500355950035031000d5402040100d4030030403090000c108a0042c2030003082400c20038901d05000b50382c41180084000c2204001d01c040300100280305000400c08c888030300503004005180482000199501c01d50b600245480f40c0040b0001012110036510721001441281c40b4100035890300c0d4441000260280303404034280c016a0015070b5180710300d0b405250098800240121594030325405030090040c2540d40181031aa154200404105150001740000c5e500708222070008078103501402c651400e581d008075249980b0f488807551030700700c0c0c1002d900d203035110b0514100419900c09803208510702180c00304281c0b03040070420000c2e80240d82c800c0b4410300340c45819607a9a0000c1040d584c0d14482e103001c0b01c0ea221000f00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 89197527 1250 89196277 89196287
    0x9081605060708090102043002030f01020909100e07080403050912070e0901020301061409040b04050406020304050d05040b0d020d15060c110307060c02010c0201090e10081504080304021002030408010c 88
    0xc40b501c00151281c00860324080713041c0229003c5034a8101c1c0301c0d04110105003001c0c45100c40d0469010f00800c103420400050f2000e00007100c24440340340005031110180402d100502c0c000a000e00d02074540c0c4e0200744580c0721103e503400c2d0040341528055401e55103e24050b01c142c441d603040c0641c40300c9040d2103402a03050010300c0509607222160100d9103030300e03901c1d0002d01b84e0000303006046c04208010071807403840c2c0c81c01c400b03000389a000900110b91542c00f03001142c200c8600b640c080c0c500a40010812007444410040705c1080002031500a144c240381c84001032060286040c05026140c0004542c0c24054694006c00041c2240c05911854669103500180c10181a00000c40320500d400e441118546000300d45241218040c2e161106420a20341c011900c20720100750803414003522000200d0841ca10034089131213614550102c4444a0500b014186040407030000040280040410040000c404e0015640c104d075060b84d120314a8481d1003000c1c1c1c1180030b03d410141c0c441d0b1928070b200f00440c1e800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 89198777 1250 89197527 89197531
    0xc01020703030f0606090e0a020403150207031b02030601140301090203071202031b0a0306020a02031611030c1c020402030408120a0204241e0e030a110108060a15030908160506 77
    0x10b500d0801101d04102a01402e0b9038072441440003003403c01008226010002c2c9400d40c0c080c07030000c401841d00e51a60366811003106045000c0015a0380880e02c8002c00d03800110214600c0b08402c41911300401d250f00082e51810140165141940300d010a4074541d1800d4100c40701e100e5009007540d0380b0940704d013142d140003451742005921910445140890640c1040c40120814102a00d00340450b411503d5044c044d5001150001c11440104040c481c01003207031410101c2c0c9446420080c407045080c43c00c151510100050305445403d441d404002c051b604070f403036011440d90580e405a100d5030b60707003041c0802c2d00500c4060315407010480c0411603000082d5000f4401e8800000c1039a1640044d00001d0804c0c00d2810411800308004030744034901c0d2802d028002070f0500c401d1521200b6001d444001c6410f046031280c007242c0300022854070075a00d603003092000b0f0340034100355080c5000030301c1c2022156400d114406900b041c9580c40740300d0014000c6080c201d511007001c00c69612000c4e4000d1502c0d659035682 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 89200027 1250 89198777 89198783
    0x10b040e01090c0b03070206071809050708010504050a1a0f030109080a2304060206040b061f0507120806060a0809030405090103050a03030501140d02011d0901030b070e01021203190b060c010207 85
    0x2254008104880c941c000d0744e01810315980140301590700d4a49c19180c282d042000e043c0440540100000c1e201c40500806204a810781e682d4500742d4540020b02055480291100c5022401c00fa0400501550040500b40461040354400646807504003c02e005056040010b445d80c48001103070a0519040900035801829240303284800703030800c020070800c0c1d0049005138001a00440d02140100da2012021904040d000f801e00318103005000700440540741022344040403800100700b61060100c80b2a804010110704c3c1804120b9141280014481d84903081c1004180416480421201402002902c0140001a0102c141940c6034100f80b41d65a030660300803800642488004122500c3c00c000314484414090320282007416241e00558041c411280345244100c20b61a8008143d510040403074021402606042201e091401d002840d1a07410482c40c0c0c10b640c4444c90000c03002c0c4506d03084070f17401411500c129500b00c142d581c088000e041c00c1d812407a8012404619094203803c198010f0016500c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 89201277 1250 89200027 89200043
    0x1e04061e080f0d0e130f0e0d0306150507030c0c05100918200a02100507030606020f0a080307031802100f0e01090302060703080712050f2e0501030e010b040e0109 71
    0xc002c441855503180f0300c0c1d80d180b0000d10308074040051810328003004080410404801314040f0714004055080b20740f9400b04118590018119650554040c410107015001426540c1d00f0074490b0540038100b4407072001e004007080000b1001a041c80740ca4520b00c400741500400d0a241912180002041844103014590f1784060310b0710000c206074014480c62413a00031044032080940c40e824000007081e081560154190b0041c1c02e90358840350703418402c981c441d01090300d00050f880e0601c00e00900e0065004181c1c0c0d050391000c024400410468810751b13500814501d404518082901c620508401c8221340081d04206066142d446640e000b0341220902d16143c0c0e075040c1c801c00311174011254400b503440040d400403420040000400c0c1300b840c0c01c90741b00700c0d5814030244a2444101803011110100c0b809154a400b0806010210080e1841210940c0766240b406565001c07550b80d09411100522429050540c0d03a030089010081c29000101803100003001004140700408c0c00c40d01130001c54801303c902d80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 89202527 1250 89201277 89201293
    0x2040b03070f0207210b16140d020702040f05090c060403150b0d080c01090b0601020a1a090c09150f18070c1110020c040b1507030305040c03150b040f02091e04061e08 73
    0x140c003050340e034022080550344040712074405008c1052103602040f008445550201b00d16009622a4020b44024582d000000038040c9010214503003000340c080a136600c51001000100081a0a011110550016000d0001c0c040c4d0301c90000403070f41501d1181c010700071600420f0442e0034440c190320244219000710440d1303040d90b5030700c40120b072070f1030118900800f10b0b114060501c00c2c2c900705030001030340080b00d0b00480d00e441502c07000084460a00320b0710414440380e0b80d1014482810000004e1380d0012080d6410103e0400c200001d11074007200415403070400107070450010038846501da00a11040b4080c00c0c2204008910500a4882d801d078100325004038103101090440e814501c4440749500c1d040c1500c141400f505c0d5400f10050b01c0050700c02d403880e907400c81c004800300c0c0c0b12164142d1600c41c010301c0018042802000c0c0401d842003400388150240c4140180d02030303501c030400003014805101403402c0102c9103000001700180003e0700b0003100d00079101080b02100441d51904800e5031200d00c110350401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 89203777 1250 89202527 89202541
    0x1012031806020d022d01061e05040902090a050402010309060f1508030403080a0503070210060b0c011505030304090902120601030606030302070b0c030f180d0503031902040b03070f0207210b 83
    0x8100401980b40180e109140da2002d0721400107003460901d55265405005c1001c07609043d0a484580e0400981c0c000c1c1006c0170b1074648440d1145a009020546043c01100001e400080e958100203010311501da80381da0009045a20951161032000d611010400c208206280c0480080c6890810351040c5410b540780842c0010000080d141200c0c2e00a040c2440c2c030b4040030b400c0310282c0010340004290311540c44521303200c03803480c050f0202400d0916290364950351000707001c5080d04e04401c03905001d2032624030103100644020080710140d840c010004514154548045042c52141a500308442e00902001108110480e00442d08480c0a9821074007155211041c0250038481c010100350321794800c0113a0300b40040b008001d4413100c1c161000750403c0e1882d032030100716140446441220365800000c20014026051021640d008540c0d032002c6080505291541e041788c4005003416040c455107028200782a8400c100d4900a40312406106102000150f0040308081c6494021514400b02c03030009082 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 89205027 1250 89203777 89203783
    0xa06020307080703110f070806150d0213051902070f020102010e0d050a0e120307030810120507050910031a1b03060d020f210601150f09060305101203180602 69
    0x24079800001c030310718103442550305850442015100d07101034004d40d51b42c0c0085c40800d100c203d004055503c0900401c0c43d01c501007030000f940d1450b00510401d07404182102584820a0144081959210001d100c0e00d8040c010451504c40c821a0741105000080c41e0b0b0030002d0102c01e40c68810300c00e030000d02c022008140c0c0f00362546041319844d0005203003406030034141407040820030107090011300450080002c0504141c21680030040990201c3c98603004d200400c641e85403010000e109104005450040d50f99030591640356038440c1c107100341081c0e00491010a011f2840c080116407062442d11a1f12250044000144d0100c031420810103000d204c014660900a0480380309000040900258280f641d0800500b14030104803280c00c240060107030724030780b42d83ca41c0301000140d0305d10090940398900a12004104002380085040000c5403017000c920640007000601910800d050101e025074444112040c4064a64030040d0724501d8180d50009260300103200792401c056183e00d01d244a03803a0350003607036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 89206277 1250 89205027 89205037
    0x50a03140c1c0602030a180f0c050105090102031e0d021603020709050c0301030605071202030915180c0904030c02030a030f0e040501050307060f020a120807020615130b010302090910050a060203 85
    0x100d40d84502c0c414001842035005507070000340303480001803d0b1012100c4040c0388078120b07002c860100c8030302c3c0c0040900041c4e6410300010302091030007918104406000075141e001e1100d12000101c040400d0303400e1013040406603211000010402c544a04524803110722004d9800c000743d016000703004001c2052025405618400d814a850061659195544010052800070088400c0080c007e9081e8100ca825000560060b60440e00811100c4800800350382c0c08040030304800c803214a01c100c0c0215900c004070301c400404000f100c6500c495520340c1030a4a00141203d402540340c0a050780c45001c168002130038420b40945592449000c446010902c41214401e004482c9c2c10b500265041045911800c00b9401518040c416114000400c0d070b10301e4288403160503d480850340343d2003004502c1d40d0400c49280c0c01003c3e1145041550000008282408200c0c00d400b000503480d1140c034101ea90090301250850040a450340d0740614080d0000ca01850b068012548260000e8800061240c400410b8070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 89207527 1250 89206277 89206309
    0x406080a060f06050a021009060510061107031403040e070504090b06121b0405030f0c15160809180f040303060f14090a0b03030408010e1905150c04050a03140c 70
    0x4200d80c10f040060320140c02101c03008045224007481090700461501903c041c00c2d200d00000309950804166060704c000321504540c041201c3d030182800880800500d4008036030300496428903d2001e6081c1d142540300710382003803110318896410f00041d04d901200400803031301042d000300400901502080740521403800c403042c0901e40d44c000302d011001e101c1000e0100000d404982c3d4602640d410209040180300c11440d03a5a41040c003c030242400c04551400141c0300503043c242c47c040040341d1016084041c0c15001c0c0000102060b01d00d91502c44005e40c0d0110140441e100318945020201000c408200700c03400c900007418901e0000d064034200c010071040d03600042007030500111003428841e038500010a01c6070304a441e1440d01506450034401800548000d00010402c0e1040b80030f2185082d080740c3d044201011069801000f00300302007541c6561500451041c88542c903038050407401c90040c3e802456100000e40000000c00c480d01e05004c142907041d83c00d4400400702c01d8200000d80e24622824 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 89208633 1106 89207527 89207549
    0x522050a06110606090c0d020304050118051606081905040602070803070518030d0e010309050c040e070503060a270326040212060601320703050406080a06 68
    0x1444e0f01603015606440c880c102502c82c40440c5c42251540031640794044089002c2080c01c1d0049040e41070707a43c001c1c1c9201086802d140b611003d1042035030307001c603007024070000b2018000d80750144941c101051075098004200c00c1c25016100062007140c440b54200030420004aa84003d54061b2100b80c0e281d9440300e23440000d8403280c07a00051010311075840f80500740c81c040d9018910f44000c03c1c0c28070780410014420710b8030514004003100f880380e01900340702c40c003120130324001074240031614100d084403155200c0c91044005c46a408a0042a9980407000240440521000784085a220f840c1c13800005010603965481c01e014241e0304646c48a16005000035460190703414200c2100180140409003040c50000c0c0410b00c3d00c2c0c0d00303041103100d81c6e809042da17501c5000c502c1d24000b1070b078800c03e591024940342c010324540c820b010303107000701790170402041d0000845d21440041d43c0181e180307 = true := by decide +kernel

theorem cover : BRFrame.Cov 89028777 89208633 := by
  have h0 := BRFrame.cov_init 89028777
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89028777 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 89028777 ≤ n) (h2 : n < 89208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
