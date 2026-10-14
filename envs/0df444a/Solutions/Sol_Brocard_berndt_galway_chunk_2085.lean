-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:37:14.003119+00:00
-- url     : https://prove2.me/submissions/920b750f-e31c-4faa-8540-5cea273e78af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 374820143 ≤ n < 375000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 374821393 1250 374820143 374820169
    0x1a270102042d1406070b09070923010b040f033c0209010503030a140a090905040c050f040506060904020c030729010b0a02030703050a0201020c011406180c2d030708070806 75
    0x481c50405c840000501d0f4090241d400000940c00c480342580c8039512002265040c0403140300c010324028101c1c42000740c1c01d840710b0150843c0e015180c1400d140a810000b91640c60000130480d4007a0300e146010405410045061030b10001c07003886c408007205010010355440b080e0140d005003059000428107080000403500f502513981d4a6943c0e0500b28004200d5030b4114031641c608004024100003030240c55401040e01031400b8107003600c480c901d884c00304102590122045030249040000b00510f0780da640e0244c800d4001e0541d40943d40f81c1460003424214810944000c11150840b844c450500c8044000c0c4030300c141d102ca40441440c0d884440940c01c0d8015901040b00581c82000a280000d103d00701130224010b060002509160034600020b00355082807400c030211859502c00c0104600e40421200403982d0510412410750424090224603031050000324600406032056600c1e450810301411050500030803000c0d6241e0800000003042070b8815a03101c000100c1c0d03030380031803c2e138a051802203105c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 374822643 1250 374821393 374821399
    0xe010e0307020f09130c0b0d0605030d080103030f030902060c1b01020f070308070f050118020f04142412010b0f0f010c02011812030201091a270102042d14 68
    0xf640807001c101000400821a000c010403852554002420118a940c0601141c0c00c2403a1074004040104044484e04e9000c60712075030006108031b0380b01e90082c2c0040d0541303130146490404000e030120290050304d082c0c080290030600025500412000214000e00c0c114035204201440d0f98400303004a0f07030341c03080f40c6107405d040d0010501040000c407044003e02d0014072682e40090080c072161226821118240c110030341c00400217860004524150b210640203900848003080b00c082d002c6043c50303e00e40c000304044511700700c0801c078100c4661143cac030003012080010218428081400340c034502070110041d00a000b1694060130402510340200c078200d1551060f51581c5179075003e50011240b4404210746603800707444107603011030054410b0924820b507174029000421442c44902d801a81c10100d10004003004507400c0500c015011605001d401c1900d07070320100c854115034510410300a00c00c96012413458030203070040d080c00001c10600740f4445010080c119507200d03591849a00da2a0305007500c1a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 374823893 1250 374822643 374822659
    0x11041202090c0309070b0a031b080f01050109060e010e120a08040e010807051f0e0316080601080105010b2706040e0930070f02060301030602070507080706020a060f1503060e010e030702 81
    0x1b0540414101400e041c2e0110710300440e403c41c9400290124510092070000050007804c20485001104800540100f80a191400f041890547d00905441150010700d041112051180c3d020741c0c1c0c0c1c6482c01008010b0030096401100103440d108500d940144a40f242400e4a02d000045a040102d07440d4225840641020417408445000340c81c0c02412207203280a2240c0c80c10391800301d072030401c034543c1c20aa101c0c1c48811160f080001c0035142c2901640300103002e80c1018014408104081c0170380b50311440c00032790300c04c22201c450422154500000b40e00c81d008100403900107002907150701c1c1140034548200c255521111607131401d9075900600c850705d201c2c8003034440c1100e0701c40c194440209443e9000340000b940355101540000c285902c2070744255907564012645009008003401403900528006000b444021300e000e03000394481d40601c10140c801c5a4031348401e02c0b0743d503041d040024a104202650102680c407403030014020042030440c00c01c550710b400d04030804110000704a440281d002001c4070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 374825143 1250 374823893 374823899
    0x60f030201120906141f050d110d050f0c10050a140c0a050a060e06130c030f030e060c0a17090609060304060e030c0309030d0503041a0a11041202090c030907 69
    0x51004503242c40740400403903590540c8008603d040c45000d5444038240500803071801c0011550501d461854021030001c51086010840b55a4419250881c40c0c1d01c4841c1500321034134032000030520010444080d00500403144206c07280360300402c0300100d686040351541001c10012000f15070b02d0149004180c0031880306542c540c941701c10900680380283d03140d412240e20011540d0740500b000c4200500300d4000b600d030444020162014000c05521034440d400034200d004181e2100c4080e20150b1201820401c41c50080d5410f26100304040c00f42c410020f000f0981d504002604180d440380509400e45035024800700340d001c0c880d050411140c005900500d058148103001c0200a070541c0003800458565680348090300003017409101518408020740040c6480e2402007090508108106094a0400c00d0405c2000000f400901c554000300502c203541000b650f80301008200240401018920601d002060016400e072007280c1210145100b44c03003a03060380e241c42d065039507103000540c0c0c1d00c00c0f0382e00010414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 374826393 1250 374825143 374825147
    0x804110f040222030228060309050313080c0103050f270f0d120c0306150315030219080c040209060715060308040e06010807020c0f12030706060602030319060f030201 73
    0x544010320008000500c2d0040c0c0b000ca48007040c0f25807043c1c08a15416640410540c5000041031030301541e40c6a10b07001070860a10200140103481c0030320010303d56512170f00d80c1440020802e480d1a00d800050f4a550780d502c91014a0381d0344a000e031032600003400c0000141d0362112880140380204e1589803a15801c40701118a09000c8607960850300c41482412040c2210303480400400c0d10100464890000ca06d0480c0341d904140c45103078189005140c28100100108554208110446640e0389400540b00c0c580740075030101a00237500c00703580000d04000044019000e460702001300c41d400811203041e408000248001e0b4098004050340c42442070000034040b541481c4466a0100c60084c00900c0b95142e9031244070769005504032580098004040041c10b5030451009074201c03a85000504010440c0c10006120509a2000901811261555900c1d2034010000d64540e01c1d070080c028005192907101c000c1d030700c0d00125604c510510855004003802502440703400d09440c0c0301400600c980e4155001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 374827643 1250 374826393 374826409
    0x140a0305120a12020d0207140102040608011214060a02180d1e03091a070605090a0b06040c050f07080a0206100f14280806180601050d0f02031506010f080411 69
    0x14600500c403190001c24a43c181510003806081c04000c0b0050700c43c2c0c000d04110171070700603000d0081d0650703104010501181c0c0d0090005070451300310307074004181003449180c4900d0520070741103100b00c244506403d014000201350041c041030050000040a000000d808000048041020140c10102101c1c03261146000d040c807245401800f80c10209000ca0703a650185459103c1401241d45600d0f000ca504c034100610ba00a8542001d13400c030040c403000f8610740b119040344034045c0803036104594884c40c600c1c1c1680503200380c50580f070703480719001d4441c9894100182c060b80181d8840b070041c041d480020700c1c1e2208180c03000707040d20390502d018007403142800843c07039070904568021035200140041d80c1c3c07a0b04024000782110040a003200c030101c0c5140800d01c07032500c14058201e481c8181c610188c08403003900005d0050445004440c00107001a0b03a0800e242c1c203e0b4003010194150282c3d2418000500d034000380c05002d0345d800e03601d1002c002d80e284e034116a890001d90300105652483d88540d1000c0c501200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 374828893 1250 374827643 374827657
    0x70513020d0f140606282604150b030d0f1e0306211e0f140102131403150a0f110703020d08192003010f140f090112030302070813140a030512 62
    0x282060008140040d80e107401a042c0d00714009003a444080204002603118030301105902520188407424ae084002910740a40c01000c4041101c0110321159043c8a000180c030b00c031800d000300300400e0300320f1030f4002c000c0e1110707019018500b00c1103201e0060100103880c82c0c3c0d800c2134201a01200d107640c16400ca180c1031150030026074143d041030b41042c0100e90801d1034006044450000142d481c0c15400160490621940c030500c0e16041c026800340464070049907070b84078411500b03848000c40e1f860a02d200c008040c3e03440e1612603140b074100005855880c000003007034070a0180d000c8a40581602004440340e4104403412341841c115603202c2e40281c0700c59000400d06081c00c00707848641c41c1001a00f1200c40d00242e2150084030321550042000b00480c9101101c085019038280342c40e07130b5907c80828184030341031007000301c550000740d55402414070a9054a0b13100360b2003041d00d40e8500750600500c00920f03003030040440384405540321a0461038201303c1c03042202d81c44000750004128403480c0c0c1b540c0b50003c1b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 374830143 1250 374828893 374828897
    0x3070b0f0c1215100f020d03090303020d06031101140a0e0603070c020d031d03191106040f061214090c040203090a0c080a030e03030c070513020d0f14060628 69
    0x840540080b01c000d45038288240c007280a032403429843c0c4000c110801d500c4011104c10301ca0615583c20410398042440402c1d0351075420f0114401e105481e0890091103030300f14448481c0d18240c1701000f040101502c0004840c0240d880220360f10382c10307035820001c0c4281200b1070302242100506010314100000907503440310203810300d00104ee0141e00420311151641e041100095506104480406d0380c105e14242210002d070f0083c1a074150151a0b20701c6030f2492880501001c0d8842400c4100d80d8403d003c4602401c86454081ca2203565405c000e00404000c180100b481802c042c10140c0d150540120f045c030544401004001040019050000a50000d80f564800d40520410705c4040ba420700c44e0f80b40103020100007880b03445418103000380b145901c1c164580c4a600101304101c0b40010025824041d14001c460009401c003410710300354000c0c07281401c9104030700d081c202c0c1da03000841b40741d00840d031144c1108480710340340d5a00300800903188a4512a550b2100c0c2090314161582982e03490f44007480614 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 374831393 1250 374830143 374830147
    0x507050115090f060614090f030312151c02101808030c01050c07050d030b0307051206070f0504151805150c0c030d0801030308060a0b0c0106031403070b0f0c 69
    0x6448660941e00d1a001c07280c008801d000c41081200c0403807207280000d01000004001e62070400100500f001d0420050320941000400c40320038503034404460420190000f030880c1d03502d0741c064840741e1120700704842e090b280c10707041d86401c820741c10940c4003284d907800351103000c0c80604515400c0118070100d80c02c00c8020405a0000314484942d0108800060543c1d80d0003141c0710f1400905450075190b00812080060038240840c0c40082c000242c0201c0943c0d02c2d06020401e010407901007072400381140d0280307900501815403841164004200107003d002d280c1c0d98140186004107081c0e4241c851031060014643d039010304007084520480c0f44040b500701c039940c0c0c80d5180b5a903c0010b00749085180c0104130342200060b20b50700158040005049152056001c4d0024883c1c44c00044c042420521020b4103224910000900550300d840038400138002d1003440d1074851000721030b064020102400b08907200b1200f108100c6c000c0c100041a41c6545900013610241d5640b050b07071000b0602c2e8050290723481310f041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 374832643 1250 374831393 374831407
    0xa05060a0c0806091513061a130314010e0d0903260a0f1116180501030f0f0221061603052202010c08070501270201020606040b060d051504241505 64
    0x2400d44170800c20440c0755001c6100e03401c000c0122807403648c4c610140c0120404000c800084907945c81c1c1201100e401ca91182059001e444009001d01217000c0050b506010b6440703001c0c61207420903120411743c4d0188040712281908520314070031840c2e0b41105c0c4441030a0038442c02c5280b912902c0c003a04020098607050f520301c41c40e21f02161400040e800c3e103d02418a4403402e20455000b10a000090b0a0310302080c00903514585460306a811135150280030302007200865410f43d15072615140030050408001c651a10030802c9040d00d0b410140c645221003000e109540151600c02d00500b4098100b42c1e51402c820368603a61480c0504028040c01c906000640e41d440780412203d802030903009000d0000840c080291118254550a0691100701030344001950803003d070341c0c0000e900f64090780540340092000b40400029016001d002c120624a90410040008040e2101c800c48158101a01c2c00c2c0040e03001110580036034041c5022601e0303968101681004003107024280e0101c1e800050400d82c2c40c0400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 374833893 1250 374832643 374832649
    0x70e09090706080f0c0d020d0b13050609010501050c070905071e050a020c18042a030302010b13020a0c0314040308041e050301051302040e070906080a05060a0c08060915 74
    0x801140c49080300d400c540010000079030404035455010541c100b0509891401c042030f03002c24040d00c032410341410750100700a54584e00c03981c041c869812004140041d80c850f8440a02c0280030101c90a80c000c10280e07000084030f500580036110801c1496011b400c80c0e0303051132500401480c2c000c10300000c11644441241452400c200d82d000004425526156210301e00e80000e4a46503140310b4484c0150000f11041d5100300c2c805200a40060303218080c0565800d012114000c8030450b081000400e1923503a400204050301544204411032003036a9076800d000c86080e0750f0080b07000d251a081d0200302c2225088001034807039105884103401c1070440302d00b0705803031307840e00070747c070340054101940081401034281480818152030f003004041c05c84c024003062422003c102d6100c00803000007030080d03444040c0725a007140240f0a00c0c01404051800708001907030350820382da036882d0340c0c03a01340d41a004590204070f000700e4034000c5650508181e01c4490317039070300ca0700c080c09407440004003015800c00c00d1800c280010f40d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 374835143 1250 374833893 374833909
    0x11190f080f0a0504030302011103040b1f0816060206010e060f010f1103030a09020f040606120c0201060e07030c1202120103020f040906090c061404050901030609020303070803103b070e 81
    0x10580c1d6100c81c0c44d54150314010742110284d80301031030314403014010007001422444010303034400900124446c0f281e20a00c3c011741e9038492500300315000d0003042e248265064450b02c040b0101c410a070700701c448603603030b03501300d1f9125490642e02103800400303c0101d006154010000c020510503540307011411085046440c50561b001524040a0192601c04100651504c0c0303640c0c0c081c10301c003100c082065a01d041d001606401d01d04041802543d10380a025070306900030b6120800401040c01a040c891402a000800403c407245d01d46010801d00742d8055400201ca109885401442583e50341a41c0d00b50307020060110b854002c950361042d281e0805200145003800303025110762081c003102c142e00d41010800f42404021100c5a829103c0c04d010400c5159a0003072001e04482d081440021340b041140007290551080c40000703422942c2c0002408800300c80f101009085a00c03180b51540e84c4284011000301054041c00a1900c0411501c0d41e0086042e000006981140340e90400781c403035800c0d900210b0924 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 374836393 1250 374835143 374835157
    0x9070b070f1e0f11130e060a0b0a17030408010c090e010902090a260d020f070b030702071d010503010b06040e1b0d090b09060703060b040b0309121911190f080f 70
    0xe509144c90085003820045107410308014040010300034008504000345d0b031080001c1040410a84034007500d0b14030b80310050794070041d0400e001e01500120100d58130594a911512034580658070b00425584242d1240c8840e0041c1d500c0144c1c1e9100f10307440d140122019400040e4030311380c0003d60040000b030100e00101c0401886107040c0c50303800c0201c11900e03010706002008424100355000155101513080c4040344d0b02c02030f101c09013652910390b29800340c100d1410049400604110f0040d544001200041c1c142071412114228000d000d8411071905002640c00341d44225544280103101083c11081d505041c0c02c503403407507502c1c041c0c00c2c0101c1000100503607402910681d07414003044203003c0f0010060150a40c4007006e410305121042c03a20134038283c41e1083d480303404416940800401e0064000740245c4013032803c42c40c15a034981d4200000418465126409817000c5610020100180400842c4500001d10342071411521080c05440381c10324020103080803111040200100101b0b01480000b40040d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 374837643 1250 374836393 374836403
    0x200a080a020f04020327011b09030b06010f1407021503010612050a020304050a0b0a0e0106032a060f050c010e030d0605090f04120e1f0809070b070f1e0f 67
    0x44050640140705440416800b00c50045004004101000000c04643c1c1c0c910b0540714031081d10011198443d50040c440ca00c061280b440c01c005078006244d0f400000ba5003a24080c8818440e40d807a00030040d200c2960310b54502c0c0100e650402e0001182040030041e28010340007800c404007032101c071400030040b90301c242c22500c04206e20041000d0006024800d055101c80f203204114034504245e02d8080d62804040c0c0000c04903c55400080c41c4010309800115a08002d00024000780780c0300d00c2d0201402e00404260001001080c103010710340c4000ca41002d041b00d810b43c0707600b8421201107000719007035401003070f0f543c20035902c2e040c003103000040c01c00c02007000000b8060001a41070801d0100002c16030003800210b40c1d540300500340800302e420840014601e21503410030103041103022001c1a0410582c1150072410154078180003a125000003c143c4159a080e0030f0350a026105d001c0506240500d080151001110411290019040342c02200041c2541ca8005039075644036030320722640c00d00b03940382100d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 374838893 1250 374837643 374837653
    0x82206060603022d1603200705040b03010209180703230601030c0c03050a05092d0a1505041e051003060303031407120507030b030a0b040209070206090703200a08 71
    0x8034101104400c07049071396503100003125020700c110391140c500910001401007608040d90104160003100190001c802c003e04c0300890360102151140c44020603c1500d004900300441102c0038a810700c00c0310000c402c0204040044034041500300421880201384805041d43c4041d10b00028005014082e07003a42800e05400443c030740301c0001070a4070f588e403601c00280407000500e0000690044280d444401251600300e885000c010002011103004030480e40244150b40e01d5110440001030030300118000503a038144103581d85418074100d0b40c103040d078008001001804140f140c42c00c2128480c0c0c924840244020000f82c8400015a844044200130340100c6d035200400c00030903030980640311180f51007002e102c078280f030300e1340b400b070310b0451904c0c074000d001a52070b00011100f0380282e0002c41c5440010302101c0d1592101d20340055850300a43d4186e11a00315400080e021500c0010b2062040d100c010181101500c2c5d540c0b8a00c950150150018840a0a0041b00340e1615407000000082508000401e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 374840143 1250 374838893 374838907
    0x20f030705011b031103070c1a01061d0915060c030405041506030c050a141b07060e03060a180b07020708190b0a0b101121030f0a02070308220606060302 67
    0x1000360f030b01e403055401030506108104460b1514201540d070301012034109107a241d140b5141030301e80c0c105884d454051200e518000031403100da0040c8030b902c1140300e180001c48071404070020002d4030002121454489121050101a50304120015020a0900d0030850b410961143c1c00501620b07260101c00b0106c80e02103808104240d4540220f07205041242402450710131403a0000f40901820000741e0407000b07001400da036580780410b48500d0080f61001c151100c054494500903c132031a081c040310302c2031003001c1c0820b030f9100f554070520035008140808803041012580da58001900300a100c003040d805500360003d06c491061002d2507646080032a049c00d0502c42e4600a01b0030700e0081c2a041c590751400c66481202d403070700e8061078038140c8d45007405014180313400c0c0454a4012484c4040c44401c1c0c105005403200b04d852000b95018800c0145181c01f20303602c2034070800403802a84000340006054901080a003141c0349030070990268020000b0800c00140d484500582c0c110f64081000258005414 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 374841393 1250 374840143 374840171
    0xb030901020306190e04080304030c0c09060815010b070308040203070f03210206060a03031206080316020f0d03050d050c0d0207030f021204031a06012a020307140603040303090201020f03070501 85
    0x210f0415200e1144c50400303a420458038040026000300b009222040c004003003018540107c4240c52081e03800842c2c1c442c041c2d1030300484400341c1401d2240045a20900707503161000308140303a05a0503030306810368150500300c880e2011224031001070403d03a094025840e022421880040d202c03005140204c0b007211040c00002c001c216240bc1000700700045411103c140212a0b481c02c9401003140c1d0145440ea54103a0440c1882009201582c01a88a0700c0000341000403010115040040c9038003c403440240d401044c814040e01038008080100040c008001d1912003810540c01039030002d56840c00e05092100d2018503008070fa01c074080c2071f00400d1030304075a00c02d0182e04015001d03201c00c081d06001d040c60b10355510461002c01045403081360343e14800c00039034207910401e00584070701d500002c1d0108040140c11510491103501105a000e4025000007180542d0002441c2d5085c2c030f4080c1605207560b6031503d0440041088107401c80c11405030036010b046049007013005d09540ca000708000a0b40c0303e080307603503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 374842643 1250 374841393 374841409
    0x1308150a0b0f01180819060c09060816031e090c0504060605121803070f05010e0304030201121e0204090204050f1203042105030a0504080f15070309020a0b030901020306 74
    0x30309a40e160400060314601d403030b0300c501d48540311020b0800e11043d182412854503616103641081e80e00d48102040f02c101e100a460b540c1c42c5d81800751008200d03030107507090304656620b43c1d03008000c04107100402051201840b0141210760071014500000c54001c2d800300740f44c103035115200a01c0100d84414064091117410328000b802001d086038100040ba2800f40003404a000b80310f94103070b64406240c0020244224882039402c0f00103900203607940e400c0740f071a1055400d00009400d070740035803800341010280303139001040764240d80e0140c6a0a1450109010200c0074003c81c608000c4208804030000c0e0050b0642d00103032010703064007800940c03154140303c28030a52a4592552500c10010550003510501020048900ba210b03004410381c5100b241c0020350520f141c034428004c2407480005049840306e98018050001d80d09042c06032100402d500084607550049006084441400d0b103020501036030107075011141e101c0c4040c1041c084242d940100000607041121240c141d41d40000c104a0603107040c4613 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 374843893 1250 374842643 374842651
    0x60605181009050f060705030c011e06081203090c040908040503120717131206020703030513020306070e0a0810090c1d040f020d1e0203060a020a120908130815 70
    0x9140c8090001c010802040307034a99102e114011200000300400944540c41150041604141140d64501e940c203d4035000b030080e1410300800007107149009041c01414006d0a080b68940d0f0002c1c0403401e0102c640c01005c2d8406001500c0303078841c07040d43d60040d445034020001181d0140301220344691400d002d25080040c544800b03000a1820441500083d909030b01c2400144000e50f000c0740c940c1d405010003503281c507164012003c03c101700700080080045580040508500ca6a42840b03541c940348131078001080b00c3d08009605401c8400050401442621203001e203860040c500e100082c3d4500980f400c100001000d6041d1075214018441440b659070b500354020900704c0c0e000701000c6e80d0500c0003504030b40e000d000100206940701052040d540c80e1260813000c1c0ea001040c80705420901d0300210889801c41c5c00490280c040c0a0029614402510a0300e40b401d03107649464000070b110003d554014004041c3c121500740040c07021447c1080200360310800740200c040146446030040c4c1240a2401d4014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 374845143 1250 374843893 374843899
    0x41805060a32101707120f050613050d08160e010e10170601110d03020306030304050603180114060a03110d0f0b1b09060909040c0b0a0f080c07120804051006060518 72
    0x40a40c03840d9130740000d0b00d40219440742045644000541c5040c0300c6c07542030880050f10a2080109005601096100e180055881107048403a80005198280d500d02c0c81241c80c3c2001c8000040e04407065400780804103210801490402c00e040c58034000500b8061244041d0303000100d009a01800030802100b00700d4105e8000d01b002104800e00d090101c0c1d031203030040340c040201a00880482d41a48081080d94090301d0024501d5850385845c44c1c001a00790031060543c040b03503081445148400d00b076100218000c000240555201c0c1b4215100e55040941515015402480c07504c3c841010403881d8510010b524400c034602200c6080c24039000355581d022010360450982c00f0802a40300d541c074001215004541519401c61036580ca080a41150301164450516101c0010301c40030440c2d4003400d000001c18140d155244d02b6124002d0070702480c010042c00400810185102c002d13220301420f0005d03840340c03050045901c0c11004d070b8484410380c2c16950042005c9040420f480618840d00c001100e0848001c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 374846393 1250 374845143 374845169
    0x21305090115050d020f0406030b010210201804020304050d020f030906041a07200114070245040b01051e1003091709041805060a3210 59
    0x1020858500d02c0410454090001c00109925050b155805031101c1015440e07065440340ea0f03c500140c017410020003101d00501075592941900c0b02c080c41904050313103a00d03059000390040c0b0300802c1d6460b0f016400c00e500342c1040c0c210038483c1d55981d000a51013240304002a050380c000011000c5d180c808100c0f110303145504184546074260301c940c1c0582e4104d40c03241640006080e0344103500840c03403003202c02c00b4002c006d20f080700c0760f200e04500c0c074092114903007a80c61906050304001d0316260350040450003541710160100200f44102c0d40c040c2401d0940b50305040740d5022009040724640140d000b000c846a0341111810441880710500c0490700420098480317a480302004003041103d8401080c41c2880780d81b4003100c04000505c00e500c02400c507940302000c460660700209030310f4596082003900510a80c1407000c520544c050100755101c9040d8001c1c01011252110a800c20182c086040300702c0054254070b800c040402840d11b071000b101e400402c009002800c085801c40f09903140344d0080c000320100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 374847643 1250 374846393 374846399
    0x60f0f1d0708060d0206030a0501030314040501050706020a020c1f03050a0c021e0c10030e0c040902010c060b04150e06041505010903170d110a110a030e210f010213050901 75
    0x34600e201a030015261070600d9040e40d0f40310009600200242c800b0350041e070040108000c0b051039070b0160303043c0da0103a00d42c0c0d008034100a1b500b0b4481d00ca18000e00d4001002071000c034001904c03980281c00907200500613903246100480115a003806000383c882a0841c4000780c0c10841a01342c0b2400d078002103511024082c000e00500003960380c20102c4000e4164440400010310400420b20100d2244280108104225031024800502401e401b0031000307014022100e50018524003442840180d0b82d040c0c4410480c041c8607282c0c84000c10801c91141c0d0800d840d1f8501c0310698085000352005071041c81980030710341c10100140001c99606071420411400080c0040c4030680c1c0051000d412039a108800c00280160258845010b00034045066906400c200010800c80960030280c101d00700c4070383c0c4082c0020040181103a072a20382d10740c060082404075100c0405820903040c2e0080c4901c08446040b02400c08009807450300300450a03114240c1d5002c107590b43c28130300e026019802450200c41c0b518032941 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 374848893 1250 374847643 374847689
    0x6100f08060c180f0405070c0506100303080f0709030503070803090618120702011101051510210203040f0f0c050a0b03061003051e070503181b0402130504060f0f 71
    0xb25102243e4207049410303540c4407480da140c2d500c0318180c11001d08144183c3c1011440070f48a2410000d04a406005042c000743d06c42c0e490011040482c0d4242ea84d4400b503803208003403840c0b03446001e4550700400140d05c0000c00810000c0000b0017400c0d100e03c04a40e030341c0ca00704410a080c52000340c82d0004017042c4e401d404560003000102a40c2c001070800c90569909514401694000304903412003019500301405c02214260281107000240d82c152a0701205528040080b2030100ca0809a8040c6407450002c0305429a03143d4051340d40248180300e80341d030350394450b255110060f07000c0f44103c0d5a0204048203101a0402c010072600400c4c2507011141103042900002d28803000c660342ea0070070160380700300090201142c450100e0354030450003050001401e00c114000c11a5008940403200100034018080d00c1d00000100017002c129000308112000c0280c07000c0001951008201005c10301d46443c01085558603442810010440480144403081c81c18044100d2003a40350303c80060400d10700d1000071107038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 374850143 1250 374848893 374848897
    0xe040b0a0b030903070b0907080c060c0714010e09150a06020307030206040f060b1e0423040f0602190503150102010603020105030703050a11070308100806010b090904060e06100f08060c 81
    0x2010044580c0d180e50700d03d28200d2031401008405080c80c0c100c03405101d00c1d808040381c48015134504409075a11141240c05104851140d00c80c04100c5a201981c2000703c3c40c00c4950f682d0784240e0500d0590581d90745079000800c0300e4400e17910010b0103505c41c9241001440c00042c074400600c00c0d40061070502083d42c402a4503244014400303043e850152019008022580d1b01032014035100820040c0c2c2814442c45044ea02d40195a440f1701031490220000c11604801c1070100121032030001c0354400b0350f640c0e5514201d122204100b00c0781c0c01e80a001c1502c2055003641c40c01000c0405541c1da80d16442c0c040c1c0c162601d00346251003030303055900d408000d01c0542d0303021040300d40c815051300303001c40c071174807000d41c110006c0c103d02c0c031010030903400450260201640a141c02d80640c03c24030320308481c5078450300f00a49a010070701c203203503008108000300c07445802e000c2ca4940c1d0080c01070b0350008800026a8a080c02c1031350031214000ea510143c40d0502150200b00c1c1d00308041c2a0990041c01c0c1442e0500c1c01d00014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 374851393 1250 374850143 374850149
    0xf0a05130807050109260706050423090612100f09170310050d15090b0601031506120b0303070c030f02010f1e1d0d0b2202090c1308060403020d0e040b0a 67
    0x5607283d41100398031b010304201051801c0c88014216a220f81d9036600080064115004102c0201d59804551406180c013660454900400600b0044681c4454080280074408100c6070013a60168924441018060344144901c291140340c010032078101e0f40ca4440c0b11122400043e40300741c9000d1090080c51220858444113503a406d540d0180d581034241401030b4004030000030381000a0415000c001000001140a4061003081c0c0703007031103032030104e414540e01d810650040c00c0004039408048034501030039800c03644066401500307491410b01c1e103171242c2444d00c803039810a403070740c0a4601d4140115640a1031090002c0b107a46040038001079140551110502ea03800e0440820403944090388810541d440080da044500501003800c40c030492901c0401c60703c080b1806038205000103919122808006040300c0785a60040403407000d0f5413201e102590640203250040041c111080c00482c85400030000385000d00d001e5001404c46400700380e00103040032182c99489001e0303410015000e0540c3c4441e003d610607 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 374852643 1250 374851393 374851409
    0x70f02090c04080a0c060e010e030a0201140c0304080d2d120f020a080709060c150f06030506010602100b01031404060f15030311070914041101050f0a05130807050109 73
    0xa1521090220721442c0266003000796503000d103500a00070070852146410480e038541e02c0c0d0b14482c032101c0e00151092199540c205806411200b000001036208229a4a41446044445040074141001989550001d82099605602c5052a40700c030a4003e591000040250418006010f00300c41c451030b1402040c1112a0a0240310000c01c1d21007001d80d003001c2c64450303000e02d0454462002501c003d10200007a5071072004101d5140d00858003e00c10501d060b4400d4018803041003280b401e03240d04c2d0003440b0100046021304d0740c5004c0400001c00901842c1d00900301d0368000d114001e066048003044460003c041410716261680384000c0d40050780c1403c2d4400d4102a0001d078071000809948042c3c480c1040c05d20480310100c5020080640100030241c00f2008002110300440d225400320044440c02c2c442c01383d50301c2a81002038001001c103c03111101c9607042c50298100428112501080e0300020410740106201040c4199900703540030200005010500082104914101c00070742142480c1c050001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 374853893 1250 374852643 374852659
    0x11e03060b010c08030901090b010806090c011b020907210501030f031b0c0605210f0c0a030f0f020315031b0d140d051b01060621240515070f02 63
    0x1d6030b010740070203291583c01103d4240c0d64646400100d0092070072890895800d420300303001040c9402e0004074180304a40420041c00d42d174110800641e0070201c01034400d11064039242810006131100410079009079103548a458054658400000e2200409000310160794074010040001c24030070361280c0c0505030907040c52560b6214080c02000703d205025009040c400f070b40640091090792180c01040c41d034161105110541401040700c070003840099441d007000c808500007060765001c41100503e25141c4604000594503482c0f01c0b100c0030b46008008181c400740e030200800c410440031240d50000040100c01410341c1381c0e400007a88580139841c4985501520000c4001010404010b42e154003000300c04040318015025140014900e900c0701d1441d4186103841c4000b1a5182c1050040c2c030141c0361140c45680e90051840031071258440929041070075691122002c0300c0c0383e14101e1042d45030803404182c0c0700703003e414807060010112401d02d0764207004004001000c0418000f89000203440d504542c202 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 374855143 1250 374853893 374853911
    0x20a02060a0b19150f030b0a03022110060312180e0603010207140105100f0b0901141b0d0306120b060609011e02010506010e0a080a11210703020306011e0306 69
    0x1882c20696100f00b200010307090507001c10008900c542c1c00c55488259030b110713080300c0b44101c801c40c01e03104111245600045030810a000502e4210054100e12003040702d40907207082035460302c0b841c2040300601786402c25941c0c04c003807061101c154034002c00100141404c107049840507100c0031044180d841142c0952103918045221030f5800c0d011110002d40100700204036541d10681c3c0d50003808161542c0c154244d00c01380005501c409499081c0c1114644000c16041071100d00055070a605403540f6480414420001e40301103a83d4220110030101c9060001c00704a1681e0300c000e41100e0301030700040c01855a1068520000301801394460b0b00c080d040d50000d488501410040c0e40981b0f0640c24171440c1c204400401403400da055008074440c80b0f09a03130b500b50600c0c0324011300004100c64040ca8045800008100d00482c1c604110506060700c09004010745003000ba112002d08000782002d01c0d681d4012100030415850100442c501400e00070345041c070030a290550080700642c10b48401840c23a42c40d00c001c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 374856393 1250 374855143 374855149
    0x140f0a03110906040303080105040f0b01021203060102010b090903070b071d0607060207060203010e0a0f0618090201020c1002031305040e0a0b0403020309040615110f0327030d081009020a02060a0b 86
    0x82d0b80040c2018040c5030f101d030344034035000e4034602c0d090244e01d025900d405079080301d9034603d00888404660680241c24099407800da41040c951005000f2819503480c1c2800e1101600d940141510a481c600c014503251051803500403202107001e41200c0070840d04800c4441d0400c0e0a501a0580d040e00322400d60741d83c8414074010b0068022007401a01640c40400001001d6540400c45885075000c54070802804a036405544211032a03030251b81140b4250301081000e000480d848040d105005004840040d09007034002001e280325517800d800103800100c0c0300d40b4400101000c10014000450f414454401007900c080e90f12031010901820940001011405050007030080307814820b4054030034040345403141003411005041d00ba1580019440d800c0e203540941340410304014084112015500c0c2c2000c03011030b4203170000d189130000300f842c440e150801051b9804008520903c8050344817050700d07103451143d100c40c02c41d00364001c00000740100302102d01b00e80d000c200540d000800c4400055160740b20404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 374857643 1250 374856393 374856397
    0xe070512210304020a080102040e06040e030c0105160e03010b031903120203090c090618040206090a0504090b0105180106050406050307140a02012f07080f070803010e07140f0a0311 79
    0x206250280e58401c180d924072501c5005500c9203000f5699024081e65880403a401c03031086d48201c580700481c4001040c40785c90650481c2201000c41000c40f4140390f10751010900710b444c1524040400d82150581000c05a00590780750400c0307d00710f000f000032400b03200109072918044a030045aa01c0c0d0301d0b20410426002c1c4142880d07103c8081400c5403246490b203503250744d400900840c02d03c42d04440b800640e01d8a810340f08241d10800c00052100c480e01c43e0f500b8000150072209042d58011040d9802046541312442160201400f80f0060143c551503c02031255445c03121030708881a495400061021030f40020032681101e1041c5082a0b4a9403169400c071480c5081c50b2003444401e9000800c1c0072500c0d4150080740e0a182a0144e404501d811f4110700c000603c0350803025058000103000001c08a001c07500a4041407091000d150b01d00303070302d50b0340f00c010359402608600744010270130b4107000344164031a16545002074906005440c00302e594800c0740445c0520103040040580316210203005881c0041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 374858893 1250 374857643 374857663
    0x30908060103050c18060d020f0114070803010f05030304061b1b080a060e0d0f140904050f0f010503011404060e100c0905010831110d060203070807030e070512 70
    0x262102961203203442602c1304018a40c0c00d20032401007500c0c501d2810711000302070007843c00a00c01301e103410f26035003405508043e02c403805051000c0341e90340b0350040c14040d00400545200c0c101d141d03600d43c1051207020b0b080906400c110300aa1041c4414010541c1111814594255142200c4441c4040c0d14260200303040000300401d251401000000e1480c10004070800117900c5050f091151110750a281580d40000e40783c0c0200089030300c21404011801030184a0211242507601e0b458400c3d00008102030315020780f408500600304604009514200c11a880d01400303081b00240907601210207007559801020b03001034103031696012250032000d0104940c1540402c42201030101c0d090414025102500c03030b200d5140840c82010008041260058414941c24084140d20203403122024460a106a1600301210740203103401402c102d95903007003422040d441c0f00e9000036950b0310700030000074102c0380040c10550a240c200030280134241c00c00b09481c000e9610503110000340740300445480b4034020b8184 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 374860143 1250 374858893 374858909
    0x902060703050c150c0405040e07090603030c0213090f02120a06110409060503060f1602030d02220608091027060b0109050d0507060e040b10020109170a08040f0309 72
    0x1824408150b08000504003010301402034070840e4051503a400d814501c100c622210046003007005101c2c0346815442607040070394190071a0200c80d2122444802c0703d016420035004a0420341d0200c0844c07030000303507680041030345010078003060032641c1e10040801c11000c0001e20409419009440c08041002034206864210310f05009042c0d5072460106258030a0181002482c14130300086520304000401d00d01035881c4001c104500d80d90740c240d41d981b000c0742c040410114042000304603406c500da4000780c6005401140304001443d0007100e07040b100e0016a0200042c41a140c0801140c06000b149010748404203100c0800d10300d4400c605d2114a40700700d003844411145105184090014a501c41d0007820300030380381c80c00358540351020000d5006031000010503d40c00b0980600816109500507142c0380750240000c40d03481c014400040c9128803021004c0300503035444e505042071000012240858580e1048074030720f4001c090800078a8881c0040000e0900b09000ca003001c1010b100788004130003845c540c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 374861393 1250 374860143 374860147
    0x110702030d0804050c03070501020a06020304020307031403120a0921140c0109050f0c100e0310050a0b03100b0d0201141e0406020d08060913021f030c0201060801200706090206 77
    0x32140500300c082d0a60301600c0510820002c400c89041c0002c01c2002d03110142c004042041d81076650303c0207580000c00c100d1700340c001d0b49030020014542c0f003890350410390004007460715040383c1018000c441d030300204141089070502410744041603100740402d0385a81010200800d6102c0326100756176085d064480042880c00c0004c005101d07200651203030548a00c0790302514503642d0084002da41d90080182c0450303008024500b6980264010b0b1031100f00c521014040c0c0d22040101c14110046542c115000b0722450740f20034901045180c144070102c0700c01c4040d80308100341c00d10607002c82d520900c050b100a050041c40500f6414082d09081078400c455954100310002e0070340040000b095401910a0034054032a101802040d039010740700b403038031032840036160150566403040b6058945002c00e40c00d80c0c11504d500d124075046010060f8854616a10361030106907624000750007800c488492340594010b905d04441015030014138058002148590384a480e01d481640c00c003440104a4031100030742c05180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 374862643 1250 374861393 374861413
    0x30f060f08010b010905030c150c010912031b080412051c0216030f050304080a032703110c01111c020316030c0c0e2e080a0b0a05010618060311070203 66
    0x54020083d0041c0a90f40c500070240ea13041855a10a0402e2250354000031407801905103221181c050038070102900f00114004025460760891600c90343c83c8100000e807180001c91010a035011a0300b00c203240352500a41c00d18040d203600642d07132071a5060360100140015070582e180140031003080c190401820865680b610f110f0b03000d5190f80d040340201c3c0466035041d075409400d0b018030706403413145404c9054a46091400c000c200e0003440340c680d4106a00c0c9819100308400380c3c15030128600c080c46070300e4840d03141009240c0349141c40354141140d4100a0001c04400d149036012428165a0f400c00b403910171201d038000d000340c1c158000e00108104404481d1a683e09050744803000d04041400780c203040d020705480312800c10411604403503c3c0102050800029000c45000081e0400c0311548000c4002e030603143d00c4a2410244d2001080e541d4140c0e4400b801078a15891244500400f0103060400200000d0324401801500522540c3c00741591600038000400c00001100c8482b907005040d1681070003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 374863893 1250 374862643 374862659
    0x13060f0b03071112040308030406020d091b1e0504090305070203030f03011503060e1501050d14010905060a120326010909030e0103020a0203220e0c07050f0105041101030f060f 77
    0x11036070b4400107150140c03e903c0a00000c16000c0d8812805070b1810f1409065480d808029800507104864580e03003049803880c10305840c801e00c601707148940c065002ca10303600c680a04c0395480079001445148008400015000210400001111025a004981c0c880d20382820345003401043e00c0030303405000001d1007290b28129030380110b06980010099003450003e03d4001c0381103403010b00640300d85448a2010a2846150030040c10354040149003991524401d11510f20956042d44003031704580e480e50005100c4465540141c0e40d104800303035000014549084401e00c0c03029081e101c00307801d201c3e00b811302034104228404100030310081d804152844d03581d112100401008034072030a400248801d0030045040d1b109000300c94040449900841c2011804850016103040000000c0f044103244040022100040c003000e07485a5413071501c0540710303c072509100e4100041c1d410b00b00c400d64908030130407001400d091400d4417044003e10300014040c40d0006180c0040c41c440c2c2000c0c20b13280100e500040c2c200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 374865143 1250 374863893 374863897
    0x1406010e010f0f0b03190f140a020304021008190c090503190b011a071208010f080c0d0f03030b0904080903010c080f0109021c09030905150a0e13060f0b 67
    0x14504150802940c0e03036003189214040d014050020100007241c3c04001d000d900c2c0001d15004592440c204c800340380b24880c1c0320111080081408001502c0701e201c032070401400852071f64050030700a01035241d440c29a00203800d828287c1e03038490900449101080040d0100030b07113080308140e2504204110040c00402410141480c0300c1c6030700c030f0b218030f030f02e100c3c10300c251001c00750102d0382e0090101c0c042e170742404034072140b041c4040410032402030140420004540070100580c0703802450340301c400c41c07541064140710510700030303400045d2982c0c000800844030f9120240c41d4400c1075003000400e1000051407904030003a2205000d02540100507200b40b10600c0010002048641b004034020801c041c08080d0541d1901c5080303807200c8616242030700400081c0020b030010224030401400110135040385408407000c5500b0068190300007449450280014104200a41c4242e15114201401e12461450007402d17244c183e104140544031003c50300d504114a500850081c10101005c44015910741882d4941d40e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 374866393 1250 374865143 374865149
    0xb060a0c051009080d0c0302070c061d030a0c0512030a09120c0816080f010e1906110409060504140405032a0a0f050105100513051e0a0212060913021309140601 70
    0x843c50584406d04c0ea83c064422605041d500a45544200e40b500700182e829504c00c8100c0d105d0b1030010020031041c0d6a00340003c00c03441d4412501503e04030304000a00001d81c8403c200741981e60720401214100750303007001d8000126991001401d2440c80c0514001e104060180d04c08100c07172150002c8080c81c03200455100c42030b0781300d800807103c500c91a1903240c0d00341d600c07590081d003032608010000c228800614040d0603407507005610121b0b80003504e10144180364130640c40781040641d00c02090215252901032095002c5070034503c0e80e00b50425480d02a241d01c139211b828410b503080c540c1a204c4410a40707540c28008540c01068034200c034010b0520001c5104011000c840a5207040300061000794610080015128060f0005900c000d01c2640580205400752078004035240c211007a02e01c80a640904620940e0161400360300c4000b801c400081900025007241c0c41400c410040110030102c03100041c504940450f211a5803402068020000f4080c4c00d4024113040e0f00440510b0745160700041d07140c12 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 374867643 1250 374866393 374866417
    0xd090303140a0b0a14150301061d2704020a0b0301120c0801020403081e0c01090807020108090c010806010c0606030803100f1202100e03010b130615030b060a0c05100908 74
    0x10300e0341c0c2d1151000031500d0300e4502540c021024182070045542e240116060000060700f0350085401001400941d03800903031044000070401080000a40c040c402000c02180701600d26940b41143c0740c3c030840c005403c0b41000c0e0030840802d40014299a2500781250007403400c1d05041e50b980d61503544000100800540980d80780d40c0c0c181000903c030340b0520803101180d401141c4281007101422211b494444841050300d0522400e000c080b110760f400303101d510340a41c030a0030401da85410510024180c0d4800400720490754021505081c91a41c00c0700315075030720030341c00d00e4002542241032509400600140e000503183c85008000c001c0700700545c881c2c00c820790f020144030300c40990752003603400c110383d0f4110b00007908800200950725100d4003560407040d0a28005001103910082c500104010320070103c0c00d4420103032149802c00914604621481c0f008940e4035090210300c07195008a88544542c0d5045010003034002858024000d051021032601180c3d20400d00003226a400c2c20300c003503000042c428007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 374868893 1250 374867643 374867681
    0xf12140108070f1514040f080105070e120615030a170c010e030703020712021c032012070212010e100b010e011d040504020109270c0503060a030809060d090303 70
    0x8124038461030700d204039100e615079880161041d90088880000a1714464400c00d0309100124588942e4011039002d4a01c40b00006202c3c036142c4401010b210500710b80600070305074041d551039401c034085849540606030126850b2103032514008207242105082e4090603401c0ca100c10b1011480c0382000501071701d2030003c024000e800300246040c1d22440b40e4800100940c0c0b08000800c090f5000034030b020406800200a00d032800c0d04080003041c1120704060071000107100d0449000050100d00c400b41a140c5600d0050070458001c0c4052003151003500f00203403051141d40c007000420402500545021403400090b10100d8080011a10143c80f4180c0c580707002c036204d1842409030354400e00b0103540038481840c0f243c00c8001248c0c1848010300010301705904110103400b001c900c1030712801458403c0080d13a0001c0325250944904181201c0c0b00c0c400440400a04206200d80b0f9561483c00e03605880c0c2003036609a66030130010000e0081d100c0c480b144c150043c18146082c0a040d0541c0c04001e40c46c907e080050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 374870143 1250 374868893 374868899
    0xa031b03020a0503011e0918020103050903040506040501081f080709050903090604060315030804140405010b03090a141c0c050c0901180905070f0b09030d0c0507060f1214010807 78
    0xe41a8002e0003445400124240010000264260009100c4060301c0180100f640c1d29051a00c05840541520500d07100749802c4450441d40c3c1440b8160340300300504065420b050500c0c0002c0c40314490ac0c1304460420a030030003c5554014215074001206042050b04003046a46001c00c41e100c00541c800c0d50032240c98540040c203409800b104480000400500d80791915042c4003041d8028801400b442e04400340221001c40090450320040002e4070441302e15001d071440a4080006882e1305801c03096440c0340c01c6c070038021200800142d80403d140e0040144290051154490b0320700342c01038030207201500d0070602a60400f038000d850744003000d00504c1510072100c150410300281013001c0c480c0400070007007007034009014600c070341c007580104e07100301c05480480d5507405400c02d00d011260091401400300140a44040c64108a040c80100c1a03007005030b118665501c0780d50311103119104040900081c560f841c510780d4440e800d8072031044840d5004101c410161001c0c2210307164240108002e51042380c2c804 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 374871393 1250 374870143 374870147
    0x70f050310050603070b0307170114030106080304080303041118041a0609070c15020c0a0c1706071205070509030303040b09010c0e03061602030423100e06030402120f01020a031b 78
    0x82e40700b141c1c080e00514100349000780d1800c044c0e000410840030080d007400001913030314094040c1030080498141c10000444520105400c4030004d610072425039004100130007000d02d01000f40c039403080d081084500c4803408100810304040d0060101c4a64811003401c100810686856050503190700d86a0280d00d80d440ca020300680d41425140040070506403a0844001840400b0102a00c01c680b00b0140c1400c400103003003403074440044400c50b459071102c4018048128210301e80320500b00080300910f8141000f00c00505809103503113412840d192200c000a4800303015004030317121040050100c039070b00e01d460705014840c030000391803501e880d501f861000080c107445410030703640405005020b0b20094442c0c240140140ca040c42c82d6500b0340c00309000c000b4405100415001403106942542c0d00780340c0701c00c1c0420042c10440b41c2041c2c1400301b620132045560300c0700b60030f980d4020740c1500c1e81120004680e40701c034946441c160342e01c1c542d50f000050795000341e5407603004084500000003440d00424006802 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 374872643 1250 374871393 374871401
    0xa06031b0501081501110a05070837020d0812040c0e160e0307150215130c03080306240a02010b03010207020609090c070f030f02061501140702060408070f050310 71
    0x909002507124004580784c0070b49000d903400b680c02c05050055406000c1c212642c00d18210040a444d15004103004002e4244140b1288002d18100521003910b6404600e00c041c405146e00d000d2004004c10505010440d00e5071001600c0945d0000b0312180c5507803450200307a170f044200310780466180641e000300080c0040d1007804240942000c121800d131007501400119100b0341c58504050380341c401d4030f40c0052466240342448140f000640c0c09040801325400d6401c55038200941000300c1d4101c2c0008000c00b01305940e0342941940d82c4030300074a680b41c844d0000a07011148004201c1e1240304d603200d078144a1030310701005186044280c1c000707001003840a01018201c0c00364070750285d0020010040d03850185041026654009014000701b810f28101e916000c59412200c0401c50101e00a4400b00382d40d42c6c1c0400806a00145141110501c4030321800002c180c1e00c41481b05008284010460900f1580d810042d100540b2080c02144c1e0780d603985007001110000144152406030041d4000b01c1001c000c2402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 374873893 1250 374872643 374872649
    0xf310f060c1506080d0914030a020907050c10020408120405090c0903120309010204030201030627052205010606080615030106050711060d061701061a0a020c090a06031b 74
    0x204002406260000c01d036900c0c1c0740100200e51101c44441034400031402da20500000d00300e0100148042c00c0b642002402010054010f003410060312000c444c0c081c2c0e8000707854404c0c1941500c91100c580c641a00540380380c0200c0c42440306c6400b40b40c00041030300c4a41c1e8082c10443c0e031721000f164110202c5100d000280d01c00d9008150300407000c800042d0b101000b10004003407461000d01140d01c90000707442c4840940e082501c007203106940004080040d980c0c14050500070740440484100030355210b102c0110314001c2e04840504960300c4d0400140282c01c0c1204041c10403180f42200003080c1007900d080c40c000c10050044501150814004c90781d01e060000c1c0c8a600484556600c0c0e203943d0030940261400e030001c020482c1e60240c144104080c0e52a040c0c0900303020708580310080703510342c14800c0e1031420030764400744020f0a0707140080130808078040242d1182c84840200c1190b075a0020000c0480c20036800c1c0c242640c211b0364440521001000c542e200328100e0780201048821074440e05100c00c0a0b42c040c0c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 374875143 1250 374873893 374873909
    0x516120b06090f0a051009081c020a0210091502060109050901050402011b0c180e0708010e0309090c0c010507231c1505041802010e031507050f0f31 65
    0xb0001c4442420046030403082400010060784400d1340e15000208404c00c0c0350801400a54056401c0084c03c9040000158007200b00d08000c2528040700c40c002d66801d184000680b140400095480000380202000000742080441d000441c1084c0342010307545131001c4c40380c10040c0380761000040c0c03c03a00611880740201d50507514a1301c030f80080c01e401c00c008203032440152040c01a5a1f0b00245104c00e4171b420b8100702c0c01003280810100413044400b070034050301d03610220507a4100689410f44c500e001c0111001664100c07041075403601d8203c83ca003414001d02c0c544204079840c100a000555810040300e21241004907111608440c0540000c8180d0145600039486c10108102403a00000c5c0f43c3c003c65121607212509000a03682c840c001015100c002a04030000e00301000b500c0195640100002030000702a0000e14041d65228908480104004c000908110700401d041d124003422404840305d41c01a515480e40720b00d505161020a040081c10b51581e020403462200e40b01116160701908441601c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 374876393 1250 374875143 374875147
    0xf0a0815030a080c0118030e0f090106140c010e0111031b0405060703050d0917030702010b19151116050916020c060d0906020f1305180c0f040305010516120b06 70
    0x20781e40f6440150013030341340c0a943d5500c1e5016500c103446002e4200d09030501070b03601d03c1c030410b04c0070080c070158640c04074282d0701646501006105847d040505020050f500c0b007016070743c44080c0110a07005040d02211404154200501c0c600041044005507000310701c01b140014070350302c80444c1815203103d1441016040b21302408510040b078011006800d40044031000030802d8001640c800300b8404035890303510300030600031003401022542485020300c01c1500b51120b4203204005650360145c11a544074410000702c0c80c59115100521545115202d502e00740220340201c9400c551140700710225000740b03401000c0380347c00a500386070081e802c40c0107519160090f0410b5545442485120350189006419103601c406607440015a40d10050104403400c10995031038558a0813006c4035800c59900051242c100c0c601c1c0c1040c800c4620784c202c1e0304014181c0c521a501c503450401e4000c1800740d9400640254600010010902080c41e120340d61861030360b0701c44824400302d404600c2120313801d404860b0005c0007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 374877643 1250 374876393 374876413
    0xc05091015030f321023040902060d0203090c09070c0b07020705060703080a0c030e151003121d010302040609061206080d11101a0108060f060f0a081503 67
    0x298019003041c509468085103620342468081c00c2c50200d0140d034290305204543c0c0b8042c1400084e11590400300355000c05490501c1c0600001070040d41d61010080c4c02800b413091901603580b50310403103504ea03002c0c00e5aa01c0b0381e40ca115a000940044980401900400360440c20900d40911103034400c0c4035644132440c2040c9240c40d0b030006428018440e1040d80b207004004615641c81c0009401a04d100c1d030740c3d03114245401c034128000c3e902200398031020305040c005402c031601c001040c4402c5040b20320380c051419603122210400880b10030b6201400e020380c1c800303101c00384984c00102402d031008101e5011008a07135110045040348101c0c4a9400058660442442030b039228034240c1d04160301e86140807882948a030440d9041c00150703681080424960310803550501c90501c011086002d04103820080c0111400803420144055007842d810055460001013503503550844400c000d4002408180d220b40b400703c040303d0a82d00c04001c01e0041504000003440f4119060180d03281d00b0009000380c404488 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 374878893 1250 374877643 374877647
    0xd0f02030f0328050c21061f0203131205010b0a0305060a0f15060e0306070c03170601020a150b0a09060308090405060607140304050a0b090109260106030c05091015 72
    0x10f4550801080040440400a90b00c9035000d542e0040d812241c100355a25060300e034628603103918804e201511700f803c0c4108031a942e140b0950842c01060424a2280100d40030002c90462084074502c482c2481c0468000c556180c1400c01004c01c00e2090380204004080307101007010b14001d03480010125401140043c8000b44140c0200080c08591400890700d1515045a0010707641c55411680000e800941c03000c990b4039003049801d0b004461420304a001b07091545000700030700400000302480144043c04901181d20801060132555004000c00f8005c213000724400c07029008400140384110795940c00810184024840c0700d0469a00400b02841c03d01c200d000e000281400903d2a68400c200b80000030110714003420080325035400c00003450b0b4071828003042091601c51034118040c040000e002001061341c02c0308200040d01e601d8100d0400318618105240980f0345000f4082e0a40e500b800b10000801120b00f0103a010f9074000c4820061550764445d5191032040240b082038101c2003515004a4054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 374880143 1250 374878893 374878921
    0xd0810140d080a091a03040b0105061617040b0307020f060c0a020a02040c051306030608060a141302040f110304051903050a14190e1e0f060d06090603050d0f02030f03 73
    0x8003142c105009281d5a55541612541d69610240d0310208000204020044200f00d230782e024000c00c03241ba0742018207141c01c010741c500c0c001d50002c10280e00c1c0e01c07416202d8102c40741510f00505060306516500c0ca01540300039140c0031040910800c034454500440d0070050715206596008000d42d0080050072196020030002d40251420b10041c4103007000601e06420b4103500c440090f0110740c81c041800c42c540300040346007a500034002c1400c2e0703140029068195441d030003010f411080702c100501c4030300010b00000300240031b41100c0c403408a1401d20040c59041020024602c254051400d8030345550401c080c41e4242c902d0a18014002142002000300050085195a19651030140c0b021b0511088040c0000c1059203581f12101080380000c8041d035502d4101c0300302380d02081890f020180d801000b0301060301f285010041c98401d25001c82c01c5104803489a02c208000e001100041c0040c0d552814082d440d6104220035800103075008808103c010b000004a668440d03040300e0292642e80c407144104486 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 374881393 1250 374880143 374880157
    0x110c03030405031f020c010e0601030b06010c0f060b210d09170601061202040803030c0403060b030106151b0605100806090c10031d0105010b190813030e0a03050d0810140d08 76
    0x4036a0a001c82051b403902481030f40190210600281140d5065081603414204003c04260402c40a0030420303000a0602c460041780c16403040c80402e1240d01e040c00102e540d000a2080c001912070700c140c1c490104000104010a0085621401402c5492341c410041900907146102016030002004216241c0700760448440d929034107200608050b2181119800c5510a44032107040c0c03000407034180709004151054142820701280200a000e183c10650307045034010048100c00c2c0038602541c0441042280c1c032040c251a40420104403d00c1d0a02c1d15104002071405490306034456a00000c80c150300c0081c1101c15140003c12604004400c0b103011005410074034a41c81d070886501c0f06603040e4420034044d46c0d010304106030310192212101c20b1614080020100428204080e02050008142d4000d0a0340c0c0703829018909800c1c0507050b403010801c0103505070300c02016446000b04002c4950780c0500024090100c40301c000c0c1d40169584296514200c040c0e071410390041c040a141400a07540800800e42 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 374882643 1250 374881393 374881453
    0x20909030f0f0d050105031b15041703030403081e0c0f1b060415020406050d0f0618020c0610060206180c0a03030302070605010b04030804030602070602070f03110c0303040503 77
    0x30307240a02400284507006007281208280e8003003501d0a0700940740c000c00d409400142c00074103400ca040079458158280a5000300d01841601100c4100e0650b040b00b05c82c042c01411500444111210450641c0c960046a090300042c0c3d80d07001042d42a4080701a4100041c031035541c859035512101e103401400d91082c548001a000100a80303e0003413507c4a040c40e0b0024a06d0282c0b8040c0340900b0011821540c1e410904d0081d88104400e200494201c41941c61b042815000000e0326030318042c0460007844290040f0a266110394104186c40701c0740e070010481f150000080c0ca10a4036000c00307200c6802c403603004501c0943c1000d000074254001b81d10620b4410400c0b107080360389090380034011519985a940080d170010380c001400e10103011280c000e0500429134103000f1072a0500d151521121030040c0d000007041d0503000503140d800d108894040d02c00c4142c110824225141c4c252a014144003000548140315010343c6a21444a240200564080310006409003080c111400602018602038144e5541 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 374883893 1250 374882643 374882647
    0x601080112030e181311190e0a09050a0c0f0b03010f090c12060b040302041505031c020c090a0b040b0d080a0e12100e190c06031a2e03020c030702090903 67
    0x109400c25011958005c0c1581d03040400041c40c1810b180d1001c0c0704c686012401000c514010440f065002c25101c2c00725441e0704400901d50301c031504800041e1220300d0b8080d14070700c1800100c1060291145108049030400ca900310410350740d8070842192030100b441046c5556020a070f0811000901e80c02a500030607044c0790184601203815406400c0314400c1e0030401e1444e101140510460800d8401d10203c1c60816951145407441c00000a95400060654111500c80320003c1c24400740200120701429200038071000706803510f529184010301150300d82c14451401c1070004140c0c1e003000d06040c1c04080e00584002e140c0006500140c941c040d120b00d42980100c0361100701040108140821440d504080001045524a1850305031500311085c00341400103c95002213000519203254510484000f414081803412900c80e001002d4035482c001035422503548004102c1a10342803140c40c0c012007918003612058210380000318100e009603558800b19134000c01404000d0b103403000c9250303484012007044038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 374885143 1250 374883893 374883919
    0x1c021e0d0605160f1106180304080d020313050609031b030a020a08010b040b15030402130e01020309250b03043e040c0503090a240e150601080112030e 66
    0x1002c07100115400e0750388a003005152403c0c164050039145809400340761510b0122910410035880d00b801030f041005101402461090303140061080c0c50041c44180e0580b1481060320780041e41302c5e80140c0b08032105140440000c20706252860941d0341c03456019008090076981c041040070007403810108107900d881011443e1005070386032032420010308000000401d5900c14601448251180d100b0845c2c8151aa054401c02c1503103203405aa50240d01160100d0006800010020040c100141c4941c19540000704203d541c5800203548441c14807210142c200c0b0b2003d41d44640071000490154605c1c0c014200041030200c0c0368040c2883c0c150414444140e5060040a83c00388141d403002c1d910103200d40003445400716031901d8850450b01107042d0520074074604c0c04640198440b42040c100800d15041100800d003060207002c550b00e03604040c2542004060b0640d200c0c00d035a0103100b104440ea80303540d800000c0040d44914900e904882056840380e403000699035007500c2021496000301d0b00040f101d400d013 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 374886393 1250 374885143 374885153
    0x1b0a05010f050a0e130924060302010c060902040204050901060c02010807050a021002130909030914100c060c0e060a031a0f0d020105220306020a08070201090b06010e1f08061c021e0d 80
    0x10702c6c030540c820707144032803103140c005017400c6c00803030070180840d06c180790040400150340c03c40381c985417003036200d000019035000502c0094001d0003140c0001c1c0e08012003500204020340c002d06c19900341d078001d88601280b650b40342c01c116850310581d10b281c0c00507000b1202e1420006000d030003800b161f4540c20542c6903040d845110750001c940c900c2009070000351503948200518089040c00340c43c1c510b01601c0c82040d004000101401050004e54003e102e10365070031214140764030440e00161404402084c0507a44c141c0110700a000d04a0040708040031030802c01c09203410f10b0001400649041c0251040507848103079001540c168000c401e180c000c0031103241c2d01011440c2012038a1000e188203410060b1105c106200042a200700140746809580c5056152804981c061170287d911103001d1a101d441d000d00c50022454584d100e0050012143c61714854403581c80cac00603078141c1b080c030040d00d4102031191103040309110108880000780d08000c81521508040f0080400c0180540c8058004100b1700c11316550 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 374887643 1250 374886393 374886401
    0x103110d061118010f03050f0f0406230603100926040b0f0a09120f020f151206040506010f121814010b03070b3402031b0a05010f050a0e13 61
    0x120381541c81c10980c10f0041d0703041040e1760806042c2c0c1c0390801103440e102c60396500408c00179103036208242101c0005410000f56401c5079a00c031510500102030203220108d030045002b800c0d03403414401e00440301d42e03450136140b80c85070000d101c0d00b042c0e40c00110302c0981c1018803e55101c2040c480d800320100000300c2c101c010080200b60111602c511941e440444150090048115400070a41e900642e01c0a0005c5030200e50101240e50701119880c08011004000030012030182522411522011680390b007002c0d00c00600728402c803400d48091009030758040044031800103e5000744041034901b2880c84680c3c0707950303110b601a0103158540005a56450300c2d892324510000b4040061a9111182d070011403c2c18420701c4004e168692149080003000810301c10340c40304040404204c020746208139150001c0c5002a00c0180342c001e4191403940c8803810600c91581e0113520003a004000c0e401c1b0001e02540300c0e05c030110208200340e42e800e0405802c04012a404250386c0c800940c001c4407410b03040c0001826200d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 374888893 1250 374887643 374887657
    0x30605030a0b0615030106020a120e0d0605060f010c150e01090c18060f0b0d0e12040b07200604120f24050c0c0d20190201080a050103110d0611 63
    0x802c056207803000401c0182440c04c101046224018401000400d400040741c005080d80304002001c01901c5403c00c850205c00101d0903640065086030754010321400380d10070307401442c040d910340240701c8244005440800040350018202c3d0402040d440721420f040c2c0c0501801001c420000c03606540742e898100000015811440703400984c030b46a400016418841c1e48014400b018041900520b0015850400d00902014807415a1a40d841d84020001030056642c480c08826045442c2c540b1009009aa5041914200c07211210800302d0b41c1ca004c16800c030042000c0009000d03d182504048001c440b0f84c1284104444e0644244160701c0051441100c1ea490365040c405e4180345110308074000815034001520300300003000e0070450b103581c444000c00d000c00c1d191858200505074040d03a40507910340766003050343d000c0140202d200ca89503040303c03030040310b5015000342d0b1008001c1e1644801241215028440103044903040711010300d03103003000c1140e07401d510b0242c00e00044d0216141c001882e2580980 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 374890143 1250 374888893 374888903
    0x310030c0e07020607020a030206011211090a060501080f0c03041709180703060b070b0109051308040b09012010050a02070c080c1009032604090f0f0e0312040b040201030605030a 78
    0x60801610b01d5040010592014151004080704056520701940340c40040c0a4100101090040b94003444103032041d11031080405440f0302e110745050417001000703003a11b000c0d41e4001290203004c100c40340340900102d8090399400090514540f00c07540c3da10500e01ea420324540c00c02e041403110000f15a5102984101c01c050946407460307515002030001c0442e10540c0080e41e0042e010311046010079884c800042c1503c40c2c4400000740b545402e4810740b14010720640007401d0000c0000c0100b900c403d0000a800100c100380c0300c4ea42c450f418504c031140b0085280382c00702020340c08076000390245030440c2c0210350046000702d4010b00d4294a61107858400700d080d001482c01d17900c03626112a16007000107550030707000514034054003100d085554445000d000291035801c0f4144083c0c0801904801e0700448000384840541000030380714030b070800405040c0c1c00c0d0710021202c0c507248004040040c08000c89083c0440e5204900450b50307256180b100851000c0c100341c0c101a569980400c041e1020425011814001c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 374891393 1250 374890143 374890169
    0x81f210203060903160807140304030f0b0c0a0f03150b04090501030506070509100c0206040f1404110c0304060c11090f01140d110d060f180c290310030c 67
    0x140c014146021006046040b0b00d500c1017103070b00c60000800a0f00c40034182c0c815002d5a0fa0040c60500703001c8158010144400d90200050000030806003030006d400c1c41d88205244559170351101011162070150342084400b0460982411844902c01d5108110860314490f50300307100b5448141c850f01c51340250300980310035a6500014018040104100c03980422203281c440c0c0341c0503c2d000420300c0ca00d1f0710040c010520519000c48011903031090107440c041c1c5058580300344090394a500b00d07440050040f86140c0618a4034042001089000048075492a200c00085203042c1c40c041d0216100b600700341083d9080c54030720fa0390358190341d110052140520509030f0402e403d941014800d0007607558445801e0302c1107001c54565400106100110b0440f004200d030364100340d4255041c9040030b80780d070540c0c0c04407c62808802180024210320445072070341c0564940402ca03511900e10140c90700d40d02040080994003c60a0740c2c80c18410030085038000740824404c410b9690b00e80d60040165082d4008002034441 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 374892643 1250 374891393 374891459
    0xa0b0c100606020c120604080405100306030b0a05070807090614130b0c030a0f090f05040221091f02030108030f0310030501060e0f0a200903160b040609060f081f 71
    0x3a05e254050b81c0e82601070216814107a48540c1c071442280b1909001d1480c0c0d0074803690180c003a52101004503041882910585094044100100b00440e0303003070046800c4401050216100f200d00d41c0643d81e054031502c0070607064410322940e0f0381040c81361103c5003225071030100f20207420074003a042d2980414011611034400c60000341040a402040004100454004000940f05040c07918100c480980340140c0c0c400003440000d501c20484805518210540b00910038000e200007130b104010200c131600c1c54660118004404242e00c42071240502c140c0c000d000030581c41200200a44d0800040d25a00c0012a6a55256400d40b03140d40d11100e08170a8020400a8148584400da54400c0040c07200300300c1a21010048140229101c007c41d042d80d401140318405a1400c120ba200800080220f40344155520b01e40307680c80307070711600034400045c030340c84800a849406100d0368a208401d9856406480d519035294007451500100440003101151100207074040d140442d041014a40e0045101b034025 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 374893893 1250 374892643 374892649
    0x80d02071e15051b120604050105030d120c0c0f06020301290a031a040608010b03010e07050d0b090a0b0a2c0c0108060a0503070e040519020a0b0c100606020c 69
    0x10000703078030307a0a0311200c01c0d0000b6510610b0050300140e03036030001420340311120000782c120044000c1820400002449805141c2d039210f090344140d03000c99041c010b50380ca03401415107450201c00c040d400f04000f007520341c0340d181e11074000c1400c000180c90503030106489038407100100c854410f003e541059000005008401001c91440c074840c3c2c0310700d41841d03030200d94000301140d40720301040d403030805507184010101442c2e60b014000811000910a00080f511546a20b000b04980920184203620300f9681c01103460300412540304480d4020400c0000d1901c03504c443c01c4074400204603805601506106a00081040c1003943c020018504001150111841c002d0411302041e0b074203003140343d18003032a0400c40c200040e244039420802e10302400c0342e03150348001c00c01c400c200f60807039541801103980208031100c244140314480e6008100311a44c3c0411445080c03400c600040700030790001c040d0a000e0040c014808001c100c003100d50000c99071803142c1d11507054100c5015400a2005030040c2c0300d6420070b86 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 374895143 1250 374893893 374893913
    0x30702040c05180f09010915050301020a09060e040b03030405090a180309061101060b0406030c020a0b0f0f010b0c1c0c020901031101030f1109010f020304080105250c020306041e080d0207 82
    0x20013a01c1e0140105008000a01055014859a90030b02c5e22250307020340b841e0300c84d5010401410b010740250f40350000342c0c401420380301ca50300621380000e00d0b44942c4200c6141c1400b41c91017140018018500c3d041c1003c05200c009035000341803c2c9000d031501c10b22120b00107201d10a500c20b6000c1d541c0c002c02c16003060340003010510400b012485d26814800c0a2041103003a9080b00c00b2526030703040014141103c40c809a00301018408041c105e0100341042150783e020b00c0d1040707442900070346d070040b44980c0c85000000482c054000c03001c040c0d600c401c40100c001105003400d030001c2082d5041050281600b9400200501000d80003241c503140c0c0c608101080c2e50f014040c044540e069a00b00b805504600807140640b070182c901d03d43c1c10000003071500e04906000b40b049401400d0564000c0c03040e481c10101802d41e80c1071495030503010401c10a64452828415803000e0140d9070b00501030900c039210f6444400d059103900700c03007401c4003008681210001f000240100003400c00c004c005a1568640c3c01c7c18943c0f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 374896393 1250 374895143 374895187
    0x1030606050108040b2202030102030a0f0c050a02030301060f0c140a05121e160c06050a0e04050415091707050609060609040b07051e181207050a0b0903030702040c05 73
    0x10248071018400007480365844107500c014091b00c08020114908a14040c5005180d00a901544000b0900a500714250031042c130100145109100b4401c800208660501c079025041005030010f1005000003486249421205403581c508900c001c405522035541c064101d80d01480e0687c4613141080030490f0512004120301800488281440c601c0c92110307460703c003001d40400c41d140c8001080e20410300c07407420441e0595005600642d440d61560409045903215290b54404510b52100803001c03441d06d03000307980c8a550312401d90504c0d141e00b4506c0c5009801c205400b10f40269500c1c0380b0b065008039440140c4030355402000240040d0038103410040c1080380240080d4026000386040001017071442e00031a4001100b0310385941e9644580c0798840e0181c142c0c3d04801c2a401c800213100d00d01c0385080e0a90b0078059401c8804000c1700304441d03c040d80d24071042c0305440e00200507100400c056080a8050103110f940601520b282110310b500242c01c4072000d00d50207000ca1000303c5e02074401520398000d4211 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 374897643 1250 374896393 374896397
    0x106090f03060906110412151a0609040608010e071e060816051201060905030d020601260309060d0203040b070f0203390d110a0c090504050a0b0a0203010306060501 72
    0x42141814a1080c1100040c0409080591146542020884598080003110a2100e0280d40325500e0303041c21034400120b11016683c02d417076501140081096072160051400d401300e101c1c040843c2a000303111081d08407000b091343c4603503217000c00140c0325420300400320b02c1c05414001d0010541008441d180f039441392101c1c54100b00320310b40c0910886401c90f100e207070080a601400c0c0300f81c00019000315420700c03034102c807040710a0403030f00002181500070071800e0a41e802281651894800c10000700e03511002403203600d00c1340300c03404d610034a158400c05800c1900441c80c803e99240c001c0b0a008624075910102e407000806c0e80c00000c01c001c0c0502e0841007038103c0307000d1401018607002080020b50341c0c019000750341d114400901c3c000014510300d0041d084c2c0d0f100680348818100084114640d11800324000490118000c04040c001030400820390b41203007070f40015140707860fa040c004403100400c0b000340220b4052003001b0380000821035800402e03100d1600300c0d03c00359580d03066241074015202d00390f0140b41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 374898893 1250 374897643 374897657
    0x7150203130b090a090c050409110a09060f03020c06180c060c1002090f030f1c1803080309010b1f020d030b0f090925050f030c06070b0a020f040602010b01080106 71
    0x4108410031109100302c40307904000c103403641030303c100150903c1102ea00200615152990f1084065000b0014000b01c410407402006000c1c28000c200213035202d4060b03100c1c00226903000030b014250240d882403c1e040668580141005414074049180250582d07852f020f4903a81c941d1321201c00001c001c16040c40340142e031028106541c12100036620240c0e89150580720350045209100d0351034801a000b9802c10003421540c006580c081c0380c0ea100c1500d800380b5034041d151807085182e031a0165002c68484001003000841491450315400e040e900080c100039015502c0304a54041c543e546400e601c80d00c1c140c1500360080200c2120040e2030446903200c044245820195204410769911082100c0c0c0740c000d0310380303480f40e030f803400315081c2082d2405a03a50500c1081d40721a8143c0010100c000040d00c00540300d408005034230508141c0d40f99074404009600540401005000a4144114030340100d400c2c0c60160911442c07980702c1c03c032034210b0703004900148e648500300f48080d07910110940c0100540c1c18000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 374900143 1250 374898893 374898907
    0x3a0516030c0f051e16020a0f050a090525020d02070e0105010c0f0c09060603020c0105060f031f1b0302181207152003030615030c070f1505010807150203 67
    0x40d0901d00c1e44614603091040100d0b00644a240002c00c580e40c0c2d0300c1d03000c207943c0c0c5c03030201340020300d03582c100840160700655000380c003c10301244503405002502c0000700041109450410100b0103084002d040c0803100341d595001000140141c02050f02e0303190300e50060b0aa00c100d0300f400078940b1109a1114208212000041020ba6089200f074094250000110b000b0781c40c0c64140690142525407004002c240b6100001814079450384c09403150000c200024027003a2144410131206000b050038107581604600c03001000c1c07009070f24003d681d01114200116100c10345241e4000710108041507140869000100c540c2c1c840d49400c00b040960300c08603038059108952601d0150303906554002d1045880c41e03155269100b90007020b80119141e00211400346480c0d40702d01c2c7d5034603a00107490072401504510301300011607810702d0031f80f0b1050300d448204d2400c200355a12506400c0c1c0d4144810f07101400992a4440e4513441401140c0c040c0c17031004e0040005602d8603a00280d880c1d21040c1c0361341103400600c006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 374901393 1250 374900143 374900147
    0xd03060f06080a020c15010609123804030c06180b042d0804050301050c07082a06070e010806030706140903121c0506153a0516030c 58
    0x121041c0c855a14000100d6074901511030028460600d0910140c8111041400d990420b03000302ca040e5a019510b28091941d10b912a52030700940c2c2c60010554064120081034802c200056a02042a01041a0380040940442e030003141e1007610154005041e01d140007041c03041501800300250421035008503c42c0154862840c01203004d40f006290740f640080700001500744224410343d002d4044070740003c1c0e00d002e240c403140c00da000b8443d240c025424140050710700c030030303c1c0e0907501c00d0354103c280c1ca0326006143c2c4020341007050b2a074517403403140c2018030052100882080043e11492460304d0302d960410010001501805004100034030075400004244009a0700098111050811480054858100100103400e02c424000c52300c401d240c0220741c0c0c846600f444503201c00d0078942c0310030800103070b181c0701c0c10b1065200e6034040c041c4c0ca00ba403c000f01041003030850070310a000700a56580100c41e003480d03480c2d000c000c0c004030041c2e0301403900d034024007244511412100040d60352a083c1003000c3c0d0658400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 374902643 1250 374901393 374901419
    0xb1204020f12010e150705040b030c0a030f051801050108010204181a03030c07320d05010605090a0b040b0f03060115050906030720010c081906030b0106110d0306 71
    0x4001e0266100c101c1041140e00d80025500b00703500b6a100910203500f403103010960f40c20300c05604010f0541ca03030022400181c01102110162008003010301d25603528600010141ea10425420f17003059039800020701c140380f56110b00b500669a8140b09150748030f0030700c040c0c0c0c20b4034010381011089901c100020081000c2c401c1803001002130480740400c0a02600c10b85812283c06040c01c3c80c0c1600001841109241d40401c0034010b8a000354242c01d008400c09282207160141404042d80c81d100001e40160350345480c0d0380b08001240305000100d405602c0f48046000c0e41801d440c18120755403614182c404ca442c0501807a0700c0e000c41610300003010002c11001030381d602018401c1c038200800000840990500c194100c03101d9400141103507075682010580140750183c0c0c0040c040c407501030001c00103814941802400811100b41ea140c0807580c80340400040d07480d503408025603941c1c0e40d5100c000b001039148403100740244520f841b0340c205082c07418070650806290b0710b40b40080618021080c0301080009013 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 374903893 1250 374902643 374902651
    0x15080c01180306090807050d0305010b030406090525081002160f02060c0a0b07090b16110109050a080102070b0f010b0304080703030f02161118010902070f02060a0215010b12 76
    0xe4100d056518441c20624855026000500b02500b0b101640090045100090421500c6481154940517440500703d04030b5200307002e034040041e07040010034040389054016076000c501801c155600d01440000c4481c011402038642020361401d03000070400c19105020700c07000c02138644001d41c644146a01c00001e401c0e801030300204000b01a064100564982c030003503d4030349881c030049814602e40e50801090b18a0211100300028030010804600300440c9030649030810801c0c0d031400c402035881d56410100b147c0c1c402a00741002381c1124000b403075980c2c01000400a001c041c00040e90723041c05080500c064000140160784030712121004002c1d2182c0c0d8011aa4011340150401d502c4050a04c1d0460180600c0d050100c00c2c603002040c424000b0720100c3c00d0f44550307071207250742291b40c50190003448600900b02d051428100210001001290410303001854054807070b005208440d0120b5000840340d811121040c00168401c1d1801550704454403480b60140110002c19401c05409a11807100968018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 374905143 1250 374903893 374903897
    0x10305070314041401110a0305040c090e032a0a03031415011e120e060601030e0d1209020f100207060206061c1b03060f0903030b0901060906051e030a090615080c01 72
    0x100c40000c494402c0d03101b00002c80120300d003030365079040c40040100036120a03074050740c02d10000000014444058428040c841203941c002d5810726242240c0405460280c804080b801030107100c140408440c1030040c1010f01c0e21036203001030b200c21440510860030000811000c3e0b040c1d002043c1110036a0803803400c1c611902142120480c040d1303000003c407040e000300c001000046040601d01c101c49403020a11501c00d40d000e03078040000f8130031607820f030340d59284400e208000300d840341d050138007076007020b40004411034000307040400745500110110b5407410207034500c032005801450701031005650520a040d0010b104540d608080840720300086c0c45524020001000980801c0080c1400003030a80315400540d00842e00704280c40c541199000030702220306040300046d2078200c0c000581c1ca000580c9038140c1c3ca81d039881e980c0e82420201f054071158041c0c224030190000c8640110148034034080210700c00c2880350804204c001141ca081415981d8210340c2001c0c00309105000d0140e81400211810000700c24 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 374906393 1250 374905143 374905163
    0x102061303030204210201030c0e0603161103072f030303190f060b0a0e06030108030901110a080c3906160803090a020108310201030209030d09030201030507031404 72
    0x280707800c0e80244200c1d030250820703410804c52074402c0d085404844070703068000c0c0c90902c0740507200c140c102c403000180c0c264294080c1c024804580000303040702c0310004140c480d0a10507803400e031004081c2d02e035402034202200d452842c1c00b95a00c03c5126045550301c100d03444082e244043c2e92040012351a40001442d400f07900c24082d420300d01c0030302c158020b03103c095240f1000b0000304e6215400d1810581c444281c58001c2404502d405581d82410742c21241258000703030140d070405c00c407c001114543c0d84440c01c90340500c0b5220700321000c40c1c580001400e0503c500001481c01c62403604900d422103202c40461240342100c03610101040d62030280041d00d107502151804c0c2d641c04640001170b0708404a03000600701c104003000700001101c0018075008018000d80310480d440e40c0d6500e40da070001c048021918503620542441c01180c1848100c031245591050502500b0012a80c011038030b800e02a03c401800140c0820b010810b5582611075543c20060514062140092400ea00884d18401410045c070305192 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 374907643 1250 374906393 374906431
    0x2f030f121303080a030c030606050403050a0816150e0709050412030504050304090e10060b1318060e2503050603150a0e070e0a11090f0d020a05060d09051b010206 71
    0x600c1e2056006140d010203101d07180c0b5900200200140242941400440d241084c0803600a0054050f80c003203030791203001050303d0421a9a45002d5030044228607003002c007120110705c00190030802c52142c0a10031038001402e0039a041703802d803801a00d80d0003400c61700e00c0c0c1401d0101003060380307618210940050401250703a0312a0f00e001880c2d40f203154010b00129280c81c00ca040714802c0410114a05134901d4020320400e03466442000d07040c0315038800101c00a10900c03041004e50b005c0c802180c2c0c00c4078504000100a03030359040b9441d407110100c5c1c0740301841c1014103e18040c80e400e01d052010340310042c582003040780790000120f40d4a00039140382212042e00400012192506a0000740a03e0b01110aa401e03460f80c4094034800000d055921410701400d040700d10885660100544003440c1c0020210b01c00105104240140e0008803041607030011102c0b03002040c0754445000500c004058140300082c42c090504000d03060025041c07501c0c40580c4400014036640c0c2c1d00095283c2c0261645031103250b4145 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 374908893 1250 374907643 374907667
    0x90f060c08070c0b0403021e0f0c09070f1101110409240305030d09140708010504051905070b03040807060608070513020f03010311030a0512130e0702060106050f072f030f12 76
    0x407412240004665410311801c08e8050042380140100100030304884822003c1004c0000e410000c0380c0f08800259041d82c0c51a0312481206040f45003940c04000085c4a845203030015140d91150700140c01d1661161010540c2044071441c5c080c4a00c203030f00702c100c0a581103075921a10b0f4030400e8a01140039860f40a0308060100070000b1001e902034607422200182e03560fa46060281004880988080c040e481d91440265540d50542802d164090084c060300ea0070200f0460264101420a5610380c800303000c41d00c00203546200b500041d0240300000d1400c186043c04000124505640c0c224080340144400302c480f041640a49040d03e82c4003240c0b0704500f5492011914000e8040070240c0540314540d140100444c1203401020a0032844450580c0151a544104150b030030a4400400680c405001000264410000740c107018940490091800b80305480b0075441400d018400f95016051440703251301c89034009070081160405401a00701c603440b400c0e28540f40c400c07030034010f042c0100000d00020900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 374910143 1250 374908893 374908903
    0x61605270f191401021b01031d0604150501080c09040b1509040606031a010e060d081c1b11030711060415020d0809010501080309040e03040504090f060c08070c0b040302 74
    0x31501402e81107041c010080100e01880c2c90384950300e0340aa02d44a480c1c45940302145541e000300364281242d465900d118011030090107070401c1c0411403c02000307a100707841428401140500c1c05451400100e9824040788800c586042c0d101c680d655001103003108003900c644100c42d03030040d0030040a04455440710000750401d082240420760103000d070f104102c1088600d074011ba050380c0c01070140344503140156985003281c800070302401e0214443c0310001440307031400205000d5041d00c10311030a81000490010b04181056a421050005454107984c2d2950420354818901e0708105150121b032a240b541001d544134420050083c0a404c480d0942d1000c1fa11010112801485001c41600d803046403410001c0d01c2e034035800940390009520402154504c40140034090594035580f000d5403802074880304101c001c0c503810002c110b1a0000380400143c0343c2c3c0e02d110f01c01d02c16001e140c2c0c045109407146003240031202148003541c2404080710600090551041c0b40400256102c0c00070959500c1c0c5080a86c580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 374911393 1250 374910143 374910169
    0x501110d1d03150109050604140112151505030c0d0308070f02070e1e0a0504030f030c0905030f030403020a0f0807060e030102070b1015090803250c030506160527 71
    0x16220303d081c1e00071001c0c88400914103c1301a9101003110344c84003002c100940700c0e17510200201803100b0005201404048401c241414441c0402003803002090200744180e0b260000107804480a5035000c002909060201280c103c508075150300005105940250217164043c10541c108441071940c82400c034020403000000d403600d000da40c4518a45185480d800880c4030301150900c20300c10b00400d0202c01d160141c00d0185505494540070400100c004a00801300b24a2510030403d42804c0003d15032001d018203030a000003a4044c40d952801c40c01480400e05092b03100043c0c0e48003403007040001d43ca02040c03d0742992140c0c40c0101132180e000000038007900448501501109004003131100f2406220304c030004584060308a03c00a025041c000e0b0b03443d0444d40302d0014035410070072400320f40340307402e42d0440801d00b030780414035800201a8032140920001c6030801c40751a44a44180095442440211200b071660ba2a0003450002411180c41c402e035907920703411480c8400200b101100350746d020300151003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 374912643 1250 374911393 374911399
    0xa05091303111e0120091302090f090414011b080106050703050403150c231204260304050105010509010501210f020711122b02010209040908090301060501110d1d 71
    0x400c2502078168000d050300f0a00c4040d42d50688444440d17800036a080d542c1d00034005000d501d0b004602407415000c2d40c01401042d0340320ba00d00d901600310350344600580b801240206440d240f581031985049007118100c92081c41016010810181000d6119041505403002407a00f43c0c1c40d858640340c02c0d10240510b810042440d2111f183d40310f0360800640c01070340102c402d030780c0b442c8400e00e0507070220200342600c00740711144000c20050f000500100028503038110784075060f440c102c111140003589465020f041e260b001d2001c0003040c0b00038064240035003805060222507425465244c01c002030102d0f61418811404000c000307050b9881d80e48583e000304070741140e030401036580e0062480c21841c00c0b4410380c000e600c514240320800c00001000103120010764410b101080810045211030400151090700715411903408111645440d211030188020003803080400645a1180f80c1c2010309444094020604100105808421105001801c0305420b122410100d00b18100a170740c40e44e048221034003c0760 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 374913893 1250 374912643 374912683
    0x150c070b0d140915010b04081513060509100608030a050306010f09210c08010209100c06090203012307030c081302010207051519110309131d0c0a0509130311 69
    0x6045040404c0c0e418000064201c094030517038940c068050319011354000c0e54526801000006002c90880219070380040000750f0035646c0c200107690f40300590b98100c80b05d02c0d441c0c01c003da6500d81d4202c540242409041c00708040e43c00c0100c82000141180002428581000001130b01890400d01410503000500b0200481c0c0d4200314035800200110034001c2804c551240003000f00040c14070041c8240d98054800a200c23400103d0120384c120398064030383c10b041d0350340e40e030b00d03074280005940921642c1c0119400074403440406004c040600074440c80108000245070030b018040c0d110650291440da03105030150708070380311121036000407403401c8400d820807a0420416a843ea40c018007240280c5002d0300005840c82000341c00342c01c204c482c49801030784071005910034091304000e4a084240b410b00e0103003448001078100d00d00da0080040ea00b0307404684100743c2040c40110b41c24180001c03084098502611031072440d051456449242100040c0c014082168050f08852094401c0c000b581c80d005541c0b991032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 374915143 1250 374913893 374913901
    0x30816080c2d030301030c0303050901021c03050411010203090f04050c0d0513050105070215450601061409040c021903180e040803180304081209150c070b0d14 70
    0x11411404041c40c590b140700454650b100344070000200d07810f0743e40c801c013059210303499507405441c103400c8611060b042d0f0144c811040070408030745503a21251801c03950041044c0c1404c4c02d00020701d07a00780340014115001040400c482c0e407a00e242d40f0102e2482550006a1a82d40001c90001ca000c3c1c101c070b1010490a020502c04800030340320b040c4151a0103840200050b45554605a1ba10030340040080d001c0d52a160006240902000c2201341501c2c04800701100404401c10220751698903a089a0f07031f2048044c003da60840d4104180c5016101604280007421800c9424030100c0c043d00c8501c80c840c0351659410b06000d4420b00c10605c6004d03e90760903c003050103620300600700f00c45910746201d039080c00503030020b0039080c000521401540c00010345840c5490312903d0790b06001c1c4a032503034041d030322003040300007001001000fa11600c890a4618a034449150604100d66002c08040680d4030071003c1c480c05030035031000303c0c075441204d43d10304440c0d40c0d134603410000e44041c00e2910300900c01710381c0c0b000c100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 374916393 1250 374915143 374915173
    0x1a0604020c030d020d05010e040c0303050a03090c060c03021204060210090204060b1606050a02030c0d0c03060308041707140f06030702160e070f0810060c030e0303041401080a06030816080c 83
    0x5d07282c000c0710683c0911183e80c8651654182020488003e805507400410800c04240910000e040d1900185400701d248d05c2e0b035890740041501e05500c0f510000301800206401e241d0305112007a2044078030010355140c5450001300a6940c8180703c0348112540c0e40d003501c2400c40d130b100c0e84024010011403005580f24140303e41c3c100e40e04054024241c9450f410701c0d002583d4403650780300300d911810300342c4000d40c102802c4142160003808106016802c3c9699400003202040380b11018000410780030b09845000490030b04900e042240e154003c9000d015419440011641c6101d800d2019400960f182912a0ba807010b089241c006a802006000165450040f5101c40e8000304684103001c03036221568440383c1c1400c1103a506900300d4183ca103002881134180700552140311190f1159003e8a41907010104d800c001a003103a200340e201581e200320350010181d042d41c1000030303540d100350010300400156203962645181071141c5c4d103840c0c14045500307003614104400401a0381602c800c14045410007940340b010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 374917643 1250 374916393 374916397
    0x7120203091206041e140604051612020303040302091b0406030227150d140f01083f04031406010f05040e0705040b0102030903030a090e0c071a0604020c030d02 70
    0x40c403402081402d4440070751100000300c80b4001e85e8011060b44051341622407584185003229400c55514041d04000b1441440411410b40100d00400c00341c50645110400c003450171031980e0049242c0d5100002640144c1d03008400e590440b5019120140660386040b6043c9071081c002c000c0400300c51000c2400b0030466415405489041011014401800600084140d01400300843c0350707800351011084140000428016041030008000081081d0b8003078981165403200071141d007501c2058001c01085202002c014000303041c1c080640c0c124011070060b550f03440072200d404144540c0001c02002703003000c05100701290002c5810640d5400c0002e0750035000c82d1501c2c02031058143c040d01400f404115031410b03209444082040a0040c08118034000910000d8104004040d0542c04103100044c1140c405000401500d4100d40e60b003c032207410140c0207400c1000107401c11440a00a2224400061408020400300702d01114600c44503501da20001e0042e2060000301041e500002c60080300300b55607900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 374918893 1250 374917643 374917657
    0x2030c070b0306090721020f03041203020c03120403021e0102120901110d2f120a09080306040b130c090f090e03040b0f090907090e130c05130207120203 67
    0x826514069622448101140030994815138400700d0440072684444c015401035060002c95040800560a192200c5c0101d030001001c00800400000820080054840e945008a8030f1420308509088005420950324060096004100501d485c041010326000300100c680b80800325494900c209d100f000381074040d4021800c03c4081900b48004078142d40010700a61622800360703200c4a00b020b0341d40c10481e01038000b11500c03040c400c3d0100003407100c664202d41d040c1d201d00b9025039215521500c40c01c80f100d410030300401000701d481c03610051200050302e800442e078121100300c90119915080100060f8a001d40f5000c10028500c0c0c5003010390310716001074210044800f07460915040d15900c2e02c1c031a0550360149041c1000c0e0f08100414409003100350054540c81c1042c010440c20605031b0740c0403400c00300c01a101240800c034a684104680291051516445684170491843c2c0d0030480e580d404804005000d4503100f41d01d608002100da810507410f85482c1c3d604031100440000840101a4803076000700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 374920143 1250 374918893 374918917
    0x518010c020105010602030d0c0e1c03080a05060913050f011d0106060509060403060e0f0a050c0f011e0503070e0414060a05011422050607110405150d060218100203 72
    0x94200d1640e074010712882d812a82c0390f030095842d10039000550001016100c0a2405000402d102d03011141c89141074010040c0803215541954503d9080242c04120020450008141402d04200b003588855012a4116030090038032204004a45485424400346004050036580380140d801030144550f109400005880e02c02080071980300e5004403140c0c0702c2e4460340740d002141000100f00280d440d5202c46540384028083e650000604e512a900b000f210180139209548401c2c4a85010324103038070000001002420b060a602210880d100c0c0e410b0072840c0e102c418040088001a14103014034095600100002d100700800041d0010000f03003144241c3e21140241541d079000300c0c1d07650144144141140390303602080d04001c1003140c81c54020051803040300c0181a030701c200060301e451316000350034064412100c1d000300901a900b40001c0b00c10003071001d041140074000c090665100e440400d031240c2d40101300940e6907416144100d11b403601e40c2e03e02c1a005404814080303d401e5000c000f41051605007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 374921393 1250 374920143 374920151
    0x23040209060a05151303020307060f030c0c02010e0112150e0f0606070308130c0504060806092a090c070b100905061008060906240a03150602072304051801 68
    0x44018441c480380e442c050507400c64042d0304c0c1070070070340199805411180d550035080d0b980180c4a9000c04e0500480703a10800204440c8a000c024840d01402207601c584100d2800254141950300024400c414014004e414020b100640d0060231b87e040d001640884074510601e03008686e140162640b51008446a1100f00014070110740e50b494040704692107e40c060b50344000701c0d01c9010004501400d03c0c401181c815494060001d41078403280500c81c01055000041c011a1400b8002c55043c51205802ca4900c1c1e40c0c42d4154802211001a4448031414155040381c4550b40c2e02d2403080880c4036041001c0d01c03214001d0700b0000807003004121002650704401e000c0c030107500d8540c01d109000d4030880704280416501000540d040c1407026200342d0149000b841c10414405425090080b0540c010502003002c00004083ea045601030044411503007001c88944003c40c6400c900a4441d076903401584034040c1c0070b11481c049044210220511554018000c10407030402404a800148d00032100202035424 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 374922643 1250 374921393 374921401
    0x60801050c0a140a09030803130506040f0308130b01060f030b040f2003010b07080f16120e09091024080102090108090a020a210c030b040308010807080a02060d23040209 74
    0x486003920140c0095441c1c4040d20782c1150782d011f000303800040010454100001d00100812410020540503a020342d1041d54000264200200724200040411801b10145191100040c4801e81c40342e0460317140b403421741d0108404120440180032141403c07a4010708180b10600095650b41c4543c40c00c1c0b44d403000c442140c10f41c860701521240400d01ca0b01180500a00181000c0765251000300b074085510201d103454034448101c050210700301050290340e00f03001e001c425660366820032103060702e420089500d11918034108211a680356054095040c50540b1904911a03000f550008981c00c01040030742100c100d0b8840311039900030340006001c503000556180104100c900c020600410960b00a4460039280d070a085682903501541150078140103030041c403000100780c900c1c0344540514802e6044002905107410018100201a00003011365000240d003003101c208006450840701d82d068030300c1500d8031040ca11040c024940d0402078049171581c0b41446d032116040c80c600f103100e02d02c21540c00000b600c5e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 374923893 1250 374922643 374922677
    0x418050f030d0b010f0507030c0c031a040b0a0b21030c1b09180c041113060c0b090c01020d0e0a15020a0c0902030c0708090f0303040b0d05060913060c03060801050c0a 73
    0x4a84217094045031007000b001000c0381c484e455845000c0e0140c00036401030340d41d990307400c3d002c8166110041413641542040c40f04001d8015402da401c19107042c0140007541c1d55400151458242d072540350803001120742800c080e107c0034400c0c1c0d4004800c00041c0c2d000d44030314a00004a04d40450800752040b400180007980c2904001d0040d503855820900a02c03103a0900301c1880000c040d0110082450f000c20702c075210715245101c505001038220340d070b981d000307140007454840c5c04038001078084c080c581c012001520043e40d0004001c010b507011481e140300a09444004100c00000580015400144500800249903000a2030f0303510644299081e009807691681c54000701d000a4416840d1034404001500c0031617030442c00740210001c0188185000400c10740020f10310f41c49a40300d01d801170b5003c20280014400ea1140a50102c1c080d100034840c2e20b0041a49240c0940d00740c0001e2019039100c01840740d1f18443c0d40f100b8081c000e00d000802447c1000e0030102c01d10f0700100d03c5200007907010000c11403422 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 374925143 1250 374923893 374923907
    0xb031b0f0a3302061b03250c02150705030708070305121e070f09150201060b0403060903110a031202030c0c0d120c0e0f06070317070513080c0d020418050f030d0b01 72
    0x41d0390100505c07002e01d099441e841e8a5400604140007000403082c10041605d03221000b44800d083c2603c4140e030320320b030f144140100300318112449060088140701d0000400d4000c41200c003c10361011282d640c1d100e281c44c041c0d43c04d0042c10104900100e042040100303004030300b5440e0f00b42c2041071200d031656075138441c801c69003080da020b09040020035103c801c03c458084210754021104e80c070700001c03410326200c200f503800d40d81255001b901c0c8540c83e44800020f058002c024000c1c0b000300000540b070010070f113840240200ca005240d0b1280b8a034000009031101a813035040c0d85c0841850700c01e03a4890410064001c000030400300643c1c00241c5000110030406001c0c5048081d0760384081c01280c100b45000c010444160406c3c0401d4090016135040c0b03421454040c030415105210a40710305403103030071201c81e03110600320a0300013000c00c1d0302048140318165142c2c03034083d1140754104d4010505c01c1c45102043ca100e122600c00500d00e100384030b90650700c880040041d003150b42008604010610124004490711 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 374926393 1250 374925143 374925151
    0x4051018020405161d03030d0e0105072d05070f080a020a15060e010e060301112803020a050d0b130c08040204230712020f04090903030b031b0f0a330206 67
    0x8210a280890032400c011603611115450081c1503030305007234500f40c804050b540c2071520320f030081e55100204003141d030f0002002000f0b8002c809401c0c5050149001904c050081001362000b0700801190f01c90421400407500c0108a6011121603115150200041d40d600410320003150901c000032100342003c0300310720650044a15034840f06040e64a411000c82d10010054440c5816540380c1d00c20624041c4540010016042c009a60400c206503490700d442001400c0180703801054010800c414081e540502600c0b060294104002648285034002502d041c814030b624045190030095448583d68000102e12300c640d0003a40d00380183c08240807428030300e201d507001d8801030042400c0800d02c103601c00c900580c2d40d10484c90005192010ba000100026002540120100354448003050105503150040948030b2009800030000c14402c2c03980610658044070b4000d002c0c14059140403c541e89209d1940c00514001050740404180000000c9000284541004240c20b02c90041d03015107100007101881 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 374927643 1250 374926393 374926397
    0x70b0114031902040b04090b0f0901021215012102040e0105030102040807060c0c051804031106010510110c091f150c060c0e09090120030c0706050405101802040516 72
    0x10000796007100d202601c4240d581a130300560f4466a900407521240301d1040054002d2044040b1441c1a034400004080020024082c1c3d90050080044602141ca41c4503006081d8004489610300b401d00100c0720004d84455519000c070010246451404003a4002c000b07448554075004401c4c1c0e02c500c1498242e22641c41000c00d075500c010820815940b20f4588068010310520001048603070f1180011100b100210b081198036004006010400d0380000030034482d500801c002e05115032415000030001081c041262003480030715078115140c0e009c24002d03904002d6000308600c0e401d0801095000c410102c40e0890740741c0c180091400310b8403c210314210580c0582a41c1c03201c006100907500c4402403c0e99000c0b1000340300d640201c8100f1a40c90011740391003520030030000100c2002804041415840c03c0c070b45114649000c1080c091815200350488070340303503008400442c068983e440c2c00e41c41c1002d90045006101d2409400e0f01503040704540b01031a06000b00c0d001c0c421610b07a0010900710840b09841140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 374928893 1250 374927643 374927653
    0xc030c050408071a0403080a080105100e10140c070909110d0809012f060a051305030f1e040305100f02090f0d020a12030503010305070e061012110c03070b011403 71
    0x41a07040001035103026840001d00e69040941c1d036070720341f440780e0004200800481c0d4a100148258204101040304200c56072401070125030000300411142803030381c0b85d180304019071140a500d8041c0d6560898030140c00c0c003021103654680c0c1d40907541c01419000001c640c40500da01c0f0b0111189400c2045041640d00401c180380750441950064072450111845110302040d500710001c103a60010001842c0304103144050f024a25284209000310f450042100308005103001014001c50000800ea80800c032408811544c2d940600c0b8900c80c8440008100f1840e4100000e40402000300103d20780c0052414000c0c28006101c01c0004101a8015599a141c0112010211100c01d141110320502c040b4000713031191080544562100710081440d900c00e0300810b00020041003000b1040064070014004810707800054141800028002829000120204005400c400c0020211076001104941c4408002c0c3c1e0340790840180d076502d9400c000b90995500c4441c0c0000203100881281d03610303035083d0080c0900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 374930143 1250 374928893 374928899
    0x510050414030111030103061d03030106050d0203102706080d0c030c020d120302040e0c0304171b030d0504030210060f0510091802030405060a11032410030c030c05040807 75
    0x220440c090040990640d242e1130741c200c1055103a4010350186000d04008145001d2188264000713099144030000198001c000420000364440c1c00d442d443d02400002503980e441c1c00e00c2440c0a11100e410200716100e07080c0380308200b44541500d0840c001ea42d401c0505c26181e8510140b0740b1101c403901c06034007140452801c1d20010f44200b0450034114401000034107c0c1c81c140e118100c1504403200d4460103c0c0c1d0005042c8034012804003406e03482000c0e50185459403501e90b0b6401c581d00150405107484030b1003c030344803130440c2404400307100c014025011240c481801460303001c05800283c90030750240c0140b481940d414400d5008500c01e8914002100828500e0001803000303101c00b8490380c06c2005601e0a0114020700c000d12414000c2204ca80c0141c0c590505080c5142800e40c050402c441e210300c0c2850400b1005114030039203a00080c480000803807100c6d4043c000702c801c095101c1e0340b075022030a1081e403891150140d020034804e28a5540801c00c4000a030070030b0311240316078040c04d04641d01c1100c01b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 374931393 1250 374930143 374930159
    0x1030c050d0305120c04050a0b0408030a080c040902030408031008010e1f150816120b15010302040510090e1e010b13030c09020a0e06120f0405160603140105100504 72
    0x58032070310b44203290451910191208008400324141e0b0141c0d032403100010200010300c0c0c071168001c00fa0100314a0315180924003400159a80309030114002449005000901d4411400b0141c0c0c0c000c08082c0c1c0195035900d401d26001c102c5030300c101d80c942d0040e0174400703010464640c14410048032440c40c4008180c03c2a000c01c040340f40c0c0300c100d40b08001964940d290901140e034400400c0d8024400c2c6c4008141c101c503c01c54103e1000d100d60400c410600e401041ca130041011042e0f5550084146000720000030080e200480c040d12039600714a802928070448840810740c021245004c42e240e202c2c0890258560032540c0304500d940300765a65440e0540001130001c0082c000003085240300082d861401641d81340e0b160040c07505282d00c6200350580c007280c490705907034000c030825411080482e040c62801c6000740080c0b2101d540500b000b501100035100050070072030104010400220035058451031150b40d810020040e220078505207080b903166500018450415241404916046c0d8031218181070503c161 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 374932643 1250 374931393 374931409
    0x20301150305062d1f05030c160605011205070807050d0b151002070906090506060a031815061809080a260c0a0e010905130b0406170705010f020601030c05 68
    0x2654400013032464142e0343c503a181e001000d00d843c1024608030b03003004c0320104a12040310402c00003420815503144100c0300d500c4811280c0c4858004021a1200d031110b90b00328588500d640000e08071403500d00081568001503c0d0741d01ea15100304c1c100d82d00744d0b48441c4010f8903102c0c5403143c10b4008001180090000d1080c50b0340795800100c078101000d4507030b0a1000114800d0303210050801580280b02d0038010030310395001c0d41014243e1103000348210f04180300420602e2048002c0603013019075460708040040101107022944540081089800e04800f10254004014600c5040c600c10354019a01e0701800b214005c658886030810326481c204002c03030800380c07862260030804005010100402e24a40c0384038441340c0b0700807c82ca030440b0b911b66024580c0a44040600f82106050040c02d403000c01503907462241a2001034441000402d106410b20045805801c16810802c00003c58141d006a58140011020101d42003660340c00c0c2d04424040b4160380302c007001c0c000a081c0440e182024003241c02c00240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 374933893 1250 374932643 374932651
    0x101a15030121050604060e0706080408040302090702030c01060f05010f14041a0c0a0302010f060605030405070311030115150e1c1737020708031b0309030f030d0f020301150305 77
    0x20203814404081d81e43d207030400c0400c58044400503514000b4a001810030484003010b0710040c2410b00241c1020344402078280581d100091050740b6183c0080c2c08a4820320035907200043e00e034028490310ba141c00f09009000101d000d9a8000750310381c528105402d1140c00000075042c0039020f201e00d41414151411440c81e403503040040711a40c10081c00c1c820310700804c01b2881113402a800003400c5000b40e564103080c1c81140d0f01101c10410709209101c0454000304620003125800341c0358005029002000c6405044528082c42c1039101d19400003410f003100759030b8004d1910356540c44403841803580b000c01440b500c0501d40342c10b00c03841003415400045d5071603c0c1084010202e0452030b0808242e0030f00c0441c03d540c0740c0644400c90180030000e4112a1402c0c10580c842d11180c006000100d060121541d52030040c207100c00401a1125072064040009104541e403c1c00c01070140d800c04082c0b00b240540c0e0fa8441c48005520514021160200ea04e0601c20b40c0c0c1030b516514400c9003000e022100440251130090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 374935143 1250 374933893 374933939
    0x1050703151214120c1005010810090302010b030a1505060105190309030c080d1b031817070203061006020d0302190e18090109050c030304141002010e101a150301 71
    0x210341c40b41c1c1400c0802c8880240003180c18410f85e140951210309041c0090101c0c00c00e185418840107229402000c194181001d003d9140045e0030000d608040303015001ca80912a058016009120103006a081c919074040c0d045101c2070007681c032810f004541601c070300913018940b80030220b024103001e8801d400030fa820304c1c02450301503100b440545400e451940840551442c265840e51407080c0c00907541045e521201041c10304100030440c3c01044000c070700864200400c61860440b603081401c04060540c0c01594001e8129240ea1074041e074241a403207414000d00d4058402c2c80c1c041c03840c0606c06c1c000c40f6250700c9882c40b24580710408100c10351790f1646d8524a154461a000c40d02c00c1e02140b036420192041550f000089141103890a090b410b104090581c035000703030801c01003806284254036110103050f900381c2d10f4000642e12910308900401c500032504801e03002c0d0351510822020260002c01e040341c1c140300011813056070401004000c01e40341d003801d84811001d0004000e007160040103076941d0703100c403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 374936393 1250 374935143 374935163
    0x1a0325150504081608010507021f09060617010b0111030f0a0f021032011211060f040e0610050a020c040e07080f010606030e06010303080c0307090e07080702010507031512 75
    0x250031004d0800c0040b2020004042140c075040140da082402441d800482c24006410215601c2c2150240141241444803c5a40714a400400c024003a400540184001022004130744080d51100b40038001940d40240000c1034450268141707400401102c108890242e402072600c00901070a65403082116072460a600524030752441101490064192040488445840114910603e140400b260358001590800b02c00300500074202903402180440340c02c11420100a112000002c000d840f94410010101001040001e07003d46065105d6015100403030f4111880c00b90241c040344d1f070780903440e04078005a202660401c03007030a00d64014140c8030402c1c1d080d2000d81e51a02c20319490002040c4141035076a56440003000460390611458607445040405031656502d107403401000c415019000c402480800004214130030700aa034488001c3c030007034080256925101d4400740045204480590155003000300103243d9920a00ca03800c5107030074041c00b07001da80741031202d40e07810013540c47c00c119040911 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 374937643 1250 374936393 374936399
    0x7030b011b03030903090b2a070f080a0507060e100c080f0406080906100305030f031018020901020616090b0306271902092b061a0325150504 62
    0x208840350701d030349000ba24041200301580c41d0007000441c3d0780e40940c1e5440e0b4244075140c0d010002403508444082e2520600c3e60041030301a00504040c0903a0180300402c29142000810346400b00d86151000d0180054032006aa581c0003a20400c0746200d6080c2c1c01b9080c3d08183c9443d03402038041d01d01407406140d500d81406d00c0d40f6011800795100f90030070b40200d10000304002e20144100121544001e02c0414104a02c3c61941c8003540c034011440340d5491030310048001014048100141c600405122a03615494890810010025444080454014040c00c0300050808220b504a80b20141041c0d444945c01407422601c014241c002030444c3da4401c072a081d0350040c40409403005003081490711504503403400c0040e80c10440c1c2d00d08094010b16140103202d03480d001c2c2e0f20f4080100c20880410b6408806000920425850040a40005010390701e440da0555070381203804010184003405504980300c003034081c02c0c3e0b003139141c2c262203064104801038101400321103001c1e000c500305047d5074200303a418151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 374938893 1250 374937643 374937677
    0x1203030e0f030c011d1f09062a030e0606040f02090901031b080a03020c01080c070b010305030a0e19060e030708070602150a020307091a04050d06090501060803030108030307030b01 79
    0x1042529a0742d92011030035508805003840390800c1203a44803060701c86140b40c8155030f81c0391a00080d04914608501464000000490b00450341265009108001501880c0705140703071140403508650501c6086072040110034000e1003000c4145014400900890341c508042101401051046041c202c1d02400003101903240e041c5c3d07280c0610b104205140103a541d0610003038500280303602019031540086002d102081c1c0100301185649003e2038500c00300d41c1d0300d2035250494402c00500034542060000000103004010018140411803030350f611315240b000c80c041202214500125421030800f0b450200412801807150054045001d015288a40d559840c19401c2a0b800d41c1700b0702c05a00203110f6141c1800e94402c0e0390790f1140d00b0400460441c20308100041c000d15a5000e201598801540381140c1d90f1004070554004040007040202e65482c0c40c41e210340500b8040d13004840d0741d802c0c020041180c4501000352410f0360044001141581d40c0c0d101c089016180c45019075050014010603140550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 374940143 1250 374938893 374938903
    0x1b1509060d0b100f12090f14010606020105100605161704030302060402030607050c0a0b0901020f040602030c070602060105010210021303060c05030405060105090601050403230f24010b041203030e 86
    0x540880001140c842e601c00703000d102030110350701d04200b05000804030612a0481d02100000c4a00e05001500d449103103040260204600d102822901049514410080e015001103003580d1042d070092009441da40741c007c003c18264000c08010800512030ba03c103801810340248021400384c41110203405d0102c403914510f074040d420540050b040f10080100390300f01080040c0c1c01c03448600c0c0c554641100e00c10011f444211030030b40100382c6092540821f400300300035016a44155040784400781d4403551804069030fa5448020350758818090b525000a82d00c5c000b080150403140d06070050494554003160840080d4016070003142c8500e5200d0000c00440e0141c4558110421543c03203840d603900302070810502c1c002d8140e101c0b500c500302c00410020b01d130340e1000c143c0c1c0440f03611110030b441012a003c05c900c40802d8040d0101c0b464415041c1c0c0e00003a081c00190003103d000b14040c110030090326641c0e0b07040651000d0049800040b010001046041c04050b0a13116550083c6400991740f800a80514184 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 374941393 1250 374940143 374940157
    0x2072d05060c0d020c06120a1808130302010206013533061023070f0c031b050a03123e03030402030606010309050a0b0406050403030506031b150906 65
    0x10754068400750f030703c1c80d404010f00e0020180450fa0326007414404045c550403040c0040c04244110384600e00011002d8080003003103011503000c003c050b1103a1543c1c0341560001070b01e100690043c0b1960000164000902c03040c05902e21080801d12642c04000c1180c48154110101d04100e51280031540c544051b020364041603140c00400c014064005400c00245450300302400b554850202409107110950704001350601c0c010003014025288018080016014046c02202804190010508a0030003030142104c909030381c03044d03070100b02102808503a10042c031046d000b45074102402510620109850b440120407a1480340741c42c5803141e591140c408030300e402c00f40c031840703a110f0070141103404410086544010f070b046120040d800d51a0980000356101d80c00790456050658825000d0300340306c1c0c24040c00d0034158200c40011601d00b45072400400070b0008403020b80c00a898080410024a004120b040043c1c5200e50314640310501c1008010001c2d00e40310303090b4218003040001d240d1a4958402411003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 374942643 1250 374941393 374941417
    0x2d2e11010c090501090b130e0613050126030a080615190c03020d0518060d0b0a062708030307030f02040f030c051801060504181e1b02072d0506 63
    0xa0742c0d1400002604899407504000841e540500c0203002114921102c00c1c02c584031071342c0b001c500740c0307801000ca0014090791041003d2141403d0020550960361410224021580400d0317180080b1141c2d000c2c1d450380178010342180068a15000319a0525000c49038204d5650000401032074206480300000b02ca4005091440106115061450034150184002c0c2030810040c200649045e0148140c000d030008000209842a0f5000c0f80b400c1341124194408191004090032032a040c079254040a440080c5c941541d68011f1180e00a400003600094908021182e00400071340c210788960030182c000d08151032001d07001a509000010309075100c600310400a60040319081c04685c200750a0014440f0b111280307000c2c4000c10001007040391f600400700c0702141c01030881d00028460500c440c3d4090000c400100c6a00040c80c00f13488400d5005a010700c0c0f6012242083c8640c545a002099803110b0700d502c01d848070341b0450a494241c4003a07102c07148003801c81c1182d07440d6000317844200286440e040050382002d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 374943893 1250 374942643 374942657
    0x60902031509061009150b0304051006030f1104061202060c2a040e0c0a061101021c0204051c21020a050307080c070f1208182d2e11010c 60
    0x16000c8a4110480f004d4080e18105010031600448406c100704e81e07030320400b510780c0300000004060000c148102500080c5110303080c80b02941ea030800000031810381038151518584c42c24203907a185440d1180c3c03400c440e061503003400109425000c002c85904010185801405103040b0091074100802c4007001019140312150f5001e02d07003c09010440e840d180c1c030000b082c2c1c00103151214950b034106500d001c0700d525107401d003002d01030401c1140c0640989550720004203295485400d80c50080c5e0050300940c0c42c1a1801c4025041d1042c220411408a07800a8840074100c420308241d103541640114016542d401120300f140941d6542e1480c650140b4001d039041d49002c2015614004e09100d1500100180c1c1c0799054098200f100b00c107010b41d0580b1009007441c00000f100000f803c0c01a80c44001ea00e0010841c0c006801c0c4201c43c4500e880000e8807040c409100001140c2a900c5c0280c2c245060300341d01041d6840740034041c804000d042c41c4000300241408840d480134044903109004030703280740c1f0071665001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 374945143 1250 374943893 374943901
    0x20408010c092907080a020307030e0d0c0b030603011401121424070306080607020109020907020a0b01050d0c03050d03020a0305011205030d1e020c010b0a05190306090203150906 78
    0x50868800c1d040e0101048903000e0100401c03100c80c1002c05100740d81040c0401900c901000c1001d1912685000820782080441d00e03840b00d94003c809040264060f0312440391582c040410440c0c004009040104072400c8040240801c903000307406035074445c40c05030001450310f025904281d1000801d90001c900e80454011742410000c9c2030541d419451081c2004080b28220000941d0f4115910000d07541002c9500002910040c401e410003002058900b0644a0030705040c43c00a01801c170b219002ea0182c0107280c04285501d10001d000010301c0d41081321014264217110421240d04000b0340d069a14421071070000c0003003072003881280c4842e00c0d29100141d46980c100c0d800307829a20140c1c030015020803024401c80200c2c40c00f00480b40303400036822000440306103000e41900c150850685044070f540c408030340f000f02244150b2110612001c03c43d03200c118140d81310204000780d07987c6c40d00c6003242d0341c007140308000180c41c60300301c8801c45200070140e4840c0b01d010550b811005804941101082e80204144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 374946393 1250 374945143 374945159
    0x2040801111c0c02071806120506160801051509040f18050d020a03080f040c0e0a061406070c2304020f030f0f040308130c0509010b030709060203070b13030e040509010204 75
    0x500e10b000c591140600c82c0140e0104080e480303007064440c080e02e07800280700074044180264440e17005011041d04402246250b82003455031050111003040558a0000500e10454007032003020b812190010200001d911024001c03c4180d0402c6c0c100c1ca07000741c2c9507038548880c412180100909403811200f0b0380ba8000c0c0c03604203185054400c040d641e05641209030360703002083d40903020591010b40300c54103406640751403404c69483c0c00f0540c04240c0300c1101a0500c40b40c801d07640c2015007111041c0c550a0050546a00ac1025621503048010021445207002704406100c12036012144191080c07501c041c5640302c000b090aa81c000000e036200c801c8008200a8080c210207100f81d0481150f800f450302d9071070607030750151400c14003810034901c2c840d05401e0324042080c0481d2020207418050200801969104007182c0c1030341040d0350000105800840c08221710748000f0550301e0141d044445508281c40f8030075802d000d10806032081c1c041104503400c807071982e00e40d4069540034512020005989514210072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 374947643 1250 374946393 374946427
    0x110f072903010501090b07050a0203150603070e13171e0403062304060209060c15010501140c060114040b040e0601030501110f0d0203060103180b04020916050d09060204080111 77
    0xc29011110520043c401640e01601800503240842142503807028907040c01e074070340505410000d616106840d002e0101201200c5020301503442903040710840c0342c40310041004500f0845401005e540070388100030204100f50306840303a803079044150b036150030000001080400440c00e5110f12100c40018100100000c603c030718072400c08011114986240b01076051400d01d400604058038941e0013190300c00065461104840390390b0706003003c90b10000c4500d215203450060901c142e038003260468480200d69070301c8000b110075518501004c1c210316828044001303444407018116a4000b55100f0091106488600c0350b6860850707068010440c83d0f1452a05c40d0039100e859025118509041c09801244110f0f64251018001195800b50301d03a50340d200100c0080400e00708600c0d203210501c2118003844819980503000f01d00a603445800f43e560f2040203c0303105180445034000510400c60000e8001c0f031135100001e500d2250340302520345582e0307034201030a40705000e010b94000300c1c00248403160b549855030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 374948893 1250 374947643 374947709
    0xf0308160503070f0504090609060905010608090a06051017060a0b0604080a0b04082a28030315150207080c04110a0503070c02060f040608070e030706110f07 69
    0x25803400c54880103540184640400b03851602401103012007040c010703000c2c03800e89002d02881d00c4204001a506d0800340041c0400d880303044840341c500400407410500c9880014860083c00d8024600480b45070f54210003800002c003070715820600e0b048041101910350765981401454040140094203000d1005001c03205541d41c00303072064404001c2000056404511110b1389508424014602e07580d50408089510800400214508070400440501240307102018401c10407101220266254040700c504144800c0a644404034041020100020b1081c0c03c0641c110280d0118403551664811030100141c5d141c0742444e0240c0c21902c41808902000c01140d03641410855090068800140130030915106986c61401040380000001700914003032001d1920701607000d05113940d01c1e40151404c96040e001400748500062040c00030488440c418165490b01d8640100170b008070303a180910565012801001c15245400baa0742c0561103d0402d01c0b081d401000c51000d08499541940c03208040042d03400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 374950143 1250 374948893 374948911
    0xc030b18011404090809030109050106030c090903120509010902090411120a200312040b03060f04150b0313050a05070501020c0102070e160e030d0c03030b03010e0a0809010302070c030f0308 83
    0x20004110600000380001600c00d025100003a1804150a0504c146c1c13044165850301036081c084030300f0412505501403421a030142c1c0020b880252164022800e80316140e0000d0001403e1004860250080b0752059411503881800095002c4039980031460801c0103e030140c2e524180440c030034180d42040e42c0a0030900107007002800307030310046985081c000300c4c400d00941540711680c0072818560701e0400c40913001c194882c4c1102c0d240c95588645150780da00c11103031140114054540144141050300441c0c100c40d150070000314005041a140880315080104080201c00300c6420305404202e0a01c001034020f0300404c0544400383c100000a403412200708201411075000e803070104001014220b8007a00200c3c0404800340480f0020421a0000b180160701c0c0c0d4907000344e00c00a541c1035003105800034031901c01c1d203013408000060804c160803201c84404a0250307410a41d50f00001403445001404041d0050400500703111a0303442d250075210088e04116a8400d492101c94141500440c0c481c0c4e12002103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 374951393 1250 374950143 374950189
    0x9010c050114060f060a120203360d0c03170603160b0403020418120f0e040c02160503031306051b070305030706140709030206031b1306031803020d11100c030b 70
    0x54100101f0300115200007441055000c8045800308100c9180c11040c104070b611801031104034a440c006030f02c150302100080c1803007030540011241d03004124100041340c140e212004681c214401c100050032000704000e502d801840b0700003982564001448000d041020802c0e51218118030500080702e604031454400b0003680101038000a1a4020802d401c5c1c91902e800a50009192419290f54900c3c951590b40541000120314010b540003401400e00401d04c00f5038420a07644905040d1a80305030049400d800800090070701001d4012002051190103107202e0040429100700d0050a02109410482e1190000034501c0148600760141c1c0d6402d00036810204098201030b04060700030042440000e0280c070000c000101c5141c2009510407160540e0110b040d83c0391b501c2c0044041504140c0140808203140c400c1c10003000300000591450a40e0680081155500310b0005a0b010b10146020004520170418441300310b10150040380da4224154902003102090b02041000d112101e0b80c0c0788044c4880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 374952643 1250 374951393 374951407
    0x6050a090f080a0c02040227090421020304030501020f07031412040201080402280f0608090303070804230309010914030a06021b16031406090c0609010c050114060f06 73
    0x30318811901e0386a401105a5583e0402e240300f40d464004240f8082d6206202255020b0352041c0800707151900070200c40c4060302c015005040006070303031042c1c0b0040c12800e442125055440923101840503081742d41d004a03400e0660385e5480a09a9221260000c41c9540104060041640003808941002c1400d1626800c2200a01e071903540d09600400280c100414840410155260003900001002100c05e8119010781c084021000d2240248174045801c0c00c8440c000481c01c0c452003005005910503000344d850f544405c0812150340c000030f40240d500500304184003240084955592840d41117130805141c51b24148800504841c3c020341c04814983d00308540801e560754081894030045d41d2018005841c1d00aa00d4881c030304400751060f51803103200303940e10751000d40400030032030044a10070301105411a15402096440300c00c00e0703908540c194000140074407680b504078042c1c2407c1340c040c03402800700c25027902c5203400d584101c0e412800c403c07401010b100c11420004407a809000303055030320f40d1402c1070b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 374953893 1250 374952643 374952653
    0x8070303020c01081306021b060702010c0e0d11032b0c050c0d03140a020f0609030408060f0402040f0c050a0e0f01140304020418030203181905010807030605031906050a09 75
    0x3070b061810b410441aa07000442111400600031052600a5030440d105c4441c80c0b250303c0078213224111340c0b02134850b170400560840d105000300440c010256640b024240d201e502400307101d15440c40103c60700305c0203c0c844075507502c00300200204004000d640420149a035035042c4100c010303c60b10f400800001d00b0bc01c1020650014110707020304000d9480102e01c490600b000c4592416038503004281c404001040303020198001010044402020140c924a4030340000d030036076034070072846803c3c8682c020100044609c124250500d5103d400a07001240030841d00c0c01c0304045402c0010400080388000c1555040140d01c040754029400c000e03108206018a07a20001e08507080c09000a55120400030014007113440d540c100c81d941d07000700c40f03600590002c240341c0a51660003135079070404405101070b1581607034a0091418001031800c504034521403410000111800100100f01900741074a0b140c0008041d203041040080c458039401d10202e4419180c035060056402c05000946c15030304001c0d02d03401050f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 374955143 1250 374953893 374953903
    0x1e0d02061c18081215060d0609050606090a120305090901090504140d1b080706020406020703021302041206020c19050607390312050c03040b060405040b07032705160807030302 77
    0x1584075500741d40303079545d8900021104800b514403500400c01181760503580072150000c00c107a80384600c080c485a541c100c1840154000c09022a030300240c0000208025514040140d11a60007803a000c3d24061415010404105003a0302130040c0c1e81d990400c000c01d000c8a04400000c3c881d050002d0450303142400c000501c5a034060002000640fa000e0100040002480c2218441c0d640030000b9510f030399803614040e40b03444030b40c40141d00400c1c00d10161811802213108503001ea503070040604400c034045807a044020f402052240042e440355600400f81000640580002d030751003800105101d00e0620740c01010000d605a5001405207160b0001e0019000d40407241030401c24540c80703045650080c102241c1782168401406822032404040c490b20080d804c00642c4160b0003005403107569200d02c01400102c940489014000104040210380c03007600c03a40040c81258030310380c2200d419508a03404071215684811088440b032b40000d0444d1204180c0075038100040c80080080d141052031a02c0c00b075120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 374956393 1250 374955143 374955157
    0x90b1c1409060a05090f0708030a0219051005040305040801020c011e0204060e0d170a0c0302073804170a060510050a0312021e010b09090303061e0d02061c1808 70
    0x4140c886000130101d41d070030031142500c0d045007401c51f50295a5440025102c0d070003c450003005001d2005130304015a11004036445c529070040050620800c580e00213001010060400c4042050400000908980074000b42c122420030100000c1c111046d000b0a48100110100104a032401440700b0400070360000b050b04402042503580c42c0d404251468001160301c1d9039000c024000601140a5007210391000900c441d03244280c00302d030b50307194543c0d088d103401c4400001090384007040711040764240e1150414500140c040d41d03000d5414651901030004140501060107001076015940e10340601149000740c80d0014203801c0034000850528001c110103041c1400302030462944000b00f000304c02e10030450000105101e44141c2c4409241d0002c0d917000e0280f180d201c1c0d22078003241010400181c004822a4016074000340030b40072407e0300e02d180e09204c4116450450344071468049044c0980c5403170000b0405103ca241c2544520711910064208446d4500030951520940240c0d030b0b40051407240c100c4041c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 374957643 1250 374956393 374956411
    0xf0c07030804380601020a150e1c0c1a010f0b0309031e070501050f010b0d0b0303090402030403090806180d08060d230c01050c030403080901090b1c140906 68
    0x1c0e40d01d034240b601401c082540004000d403092114500112651a0745460004100f1104035041c2c85200049940c3c0601810103060810342c00b41c6030040314219803001c054000c074002a241080354000404400014120718040420803810344070042041203220007410141004244481d94104855041294950f0240240034900000400c6410408000391403402040034900081c00008840030b050031340008208543d15030070071002c0b4080c5151140c034607050340e4103118907a0824011451380c001614400c0209a00342c0000c01850b8201d440728001540710718042e49690606602e0510584d29004008001d404800f0b1002e450084801d0013107014200e0302c00034a80740300c0751380318600000c4400340703861401802c0f0254a00d9600c3c000084c0c5c014525100000404d4400d261038101c010350340b9125014212076030b50010001440010701880240c801c0741018509000d03651784907501004907501c5032003460b02c07400030340001501e100403a005207102100b100d20940d04a0501c01d000c03940e80d03400a030003089 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 374958893 1250 374957643 374957657
    0x1a0402040f14060f0304050d0e0105030f15150d0203041a01081908040504050a0b0f030c011b14060108030717040509150102010f0906150b270a05100203120f0c0703 72
    0x2e00d075a41e901511540c201c6000c40b56904d04061405642e07568518202c1c2d00840c9171405440c2580d80150140c0380324000c42d00d010817641d510810038039080c1c3c3d9210300990384108007070b0005040d00280c101810304840c80d01e1005945c0c4c01c003820914055178100130341201041503607005014141e0081256100c10301100f0b11808956204d15001050380115040150031902d05800c1243c101c04a0b0403507000200c09540e00c41d04d0040c91010b041d103a840440100b07001c600a0300700c2c0c5508400ca445418010703409145002210f20800b4a05401c050080c0c0c0320452035800480e04d4000c3c0001036200018400c60004020b14152420b408142d48040c0204085036030490802c64000b07070390003074200403c00b041004081280d2030071071038800e005121b461400d10f1485c03039410022038030340b46010440d16507000344100b8210041c45c0c4c24400329006040815141c0021003400e0014060300c0d420506400f194054016548490f080500303039080c01c0005004450040280f010301030b11445d60300840d464583c041c90700003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 374960143 1250 374958893 374958929
    0xf030d050408070b09010b04060f0b09010804050703140a0309090219050903070b04120605090c06160f050d0f020c0102070609123014070c090902030c040f1a0402040f 73
    0x2102c64054120040e02c8849410200f20003944107600107070034904211001c019142c3c039a107421080c00050f009811a02900f0400e14070258003a1890303a074010311400032035a0551f00c03030307944081c100d000a05260700f0751300c0011043c04040d00071980f0360191030100c40450600e40811030001040f61908400c4061050004941407582c80a102d1500580000110607942c0c030307541c1e4840700101c0d500c008152141c5240001044001802180c1000c00302001001a418005070034000924000c0510080300e825903011941d000040e0280000846420f02d900d0300246140c0c010406810828503140c1ca604640110005008160304406a5400c0d540c64050342a8040080d15041c010205040030a2005004030410b08210303940328041c190011580d50355078a404851203105003060b025504004001420b00039040c4142c3c2483d0780007581541c00241281c502d80d8944000c10100d42c210b03030380c908210b43c440079064081040344038000000401a50210700e0107107800b40035250644c81e0700800e00700c0e8000758408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 374961393 1250 374960143 374960153
    0x30426030c0a080f270f0103090b0c131a090f030f1c050f07060e0f0d14030c0412050106030506061c140304030507060207061d1c02030f0a0614090f030d0504 69
    0x24500c00d0444107110b0104103041c3d000060024200170f6124811044883d4a0000f9440b90281039040740e8080d64200b52622121b40c4848140c000744c181400c1d07c02c800c000000d0720151191031031200704042e21400d0b914420041441030461b100103546009a010100d801204000020304590031a00d031924a52104e0b0f0804040314a441510755000002501180c1002841031035030258008000d8076084440d0341652040303494a5000544030320300414405114080c507443c00c14000c40d4070501c03a1840c180340680340d00340344514401500b400e0311346a544400c28002c00a04101c0c46400034402c0b1200c44a208842d868403104102d40d82d40100403039a56000a06190402c1003070303401456111040e5182107444600c0250740d1203461080c00006285068031010005600742e4402d5900006002c40b00101510b00030540c02d100300702e40498151040c0d001d0403410100a0190750105071040a0200d00030201c0c2904070320840000c0c2c5210841d0f0000d0401406002c000002c0304c0c4184001c807030115050381c442c241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 374962643 1250 374961393 374961397
    0x12050a03030f021611040f1b030c050f030123010e061602030f060c0304060605090c0901050711060301150206010b0309070501210203040309170106030b0105041d030426030c0a080f 79
    0x2c11180e2130b18200940c04000c0d6a0142c0c458005060b281040300200605110054860b001155520b501c40e1059007130450744a50000b0000300342a04242c0d02d080c44128605100d6842607025a00c98000040d000f000801e0318411100b15001c2440c0007800340c0258400510203110b5070505524046105a0490841d10140303c0040d400e84260b054541c149040e620201041d8400c0b5001c0320030f40d1811601240900c0c20705000e500030b42e100d80341d203801c04140100540b100e83c040c0c00c003928000090940705806903548401540030b481c0c03115030a070a840740414064a800010b03000011600010320412251b0000040c031107007224024a001c244d2620403403801c45003a154020b2009800d80004104005c0c19041141403045454140c01000142c0c020b0b40440d08950700d50000030031120744180100401e291a40060f603103509400f50a00b10340404541151840e8401d40c0a40104602d01060440036406480900403041c4414051072904041504140e143d200288004112500100790350016210f1201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 374963893 1250 374962643 374962657
    0x10c0f051602040b03030705013602092e080106050306011815150521070c200a0e01030204060b0403080301090c12022101090c020712020f0d0303090303050112050a03030f02 76
    0x941f5580e0400d41800c1e40601500c213401a450404c0c01c1d420040c1c080c0d160000f944a182d11408000c01140c0356003007203069170340036201c1102451b00c0400750b401d5011600c3e551801d200006200000145401001420340765158001880303900020010445441e840c0d2048042200d4a040042e10b0456a111884980c032940c06c100c010100390200e1054498204009250f10250b000b03ca181d4403140301c0041070b50490858107100001ca03021510400500c120024444405007013111403d1140c0c0790b008070b80c100d15154814820740000343d0040056040910640010f0b0000e540c59514103829a01c64010b50310042c440c6164060b0b035460102d0007540302d69900e002c1c40d5800d030300030742da00c2882440e103104190300844456039800500c00000340b13010051140c1803020090360081c0c280103240445281c6110b58086050340c0007000703900642610b5540c9448000d54a1107500c001550400a00b0300804a070700580000b0703221b6540c8a000300200d1070004850940c80e9051501003420071030100c0c45030103801080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 374965143 1250 374963893 374963899
    0x2010513060305040506010905150f0307150c14060c0a12020f18030601080d2708030406020d0e0f0109050d02040603020603090724080606030403110d0e0102010c0f051602040b 77
    0x88042807a0b640340c1c108600030360084d001c0f201607981700c074070050841e402600c0c0307000031100c0c4624050150400f16404030580f08020251082582c1c0e50205030741040c03003074042c0c0001400074030002e004c1003411009031014000035402440103140103400c0079644d2050000d00c43c00d102e60b0782c4104460b0000c1e0340450780e01c051180030050321102086020201d20b140c00e01c8481c07007030141400105d90b4140001d801a101d1159903981d54890003449900342020b500344c001c0158411542c400031500d90400c000920080c00e107607004040c0d030b28030b4460040200319112811032080d01250a642220783e44811208290ba100703c1d8138130054805440001c0007000780382e000035085500030003084045c00b0302244074022202080d12200c08015006582c0703c08005c00c1c18454042480840481c51900b005409141c2c06407190424000c460b802c0c0d06104d01c0c00d07826803032040018400c00d110f0308203564280201040d2100c542003c04061000c0e0f9000761450080002d06000d5240806100c42035644079001042012006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 374966393 1250 374965143 374965177
    0x2010e01080a061221140f0d140421050306012003190e0a06030e06070c050a0f110f0301020307090510020c090c04031a010305071203030b180f150a03020d020105 71
    0x3817900003041c1000040c400000b001c0310703441c0c610382c078080c04080030507000440b040303884c140d20003c184801d5005845209035aa43e01d8001402c030300780f103c0c3c0e643c1c0100d004440500c0c410142c0760014640703138441031021f42002001d0043c8103030340e60800102d03c4044d4841d05071102103002505a240340d40607a5100041c40101c125100002a820103038288090394140c0f440380b815920741a056080c1d489000d00c0c2c510b55801000011811071003415003161282c41a0250341070450315486841c00711a0106c01624042026003000c5518030b4454002100e401058009500714078207130001030f110401a00c992801402d01c100780054042c03090200074080ca1006142e8641030074141e991011903005800f0417116040071b641c041415001550781c0c03030b04a030342c04001000c1c21810405d0718150f01a14041c1181807684a00f400710180d52178480e0f10201d0304a0280030b03540751600400c403206a6030003805450001d042810081040c2e00c0f44501c0d901903d4054421080c0e046c19072004070b43c14402d201900d126003200e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 374967643 1250 374966393 374966429
    0x3080403031b08071b030203090609010e1e010801140306040b190f020903070b040e0c13030209010e060f040c0c02060903070906080a030e1009060c060902150a0305090a02010e01080a06 81
    0x1401284c055040c6a8890240c12071201182c80d40080888001d8050780c800d00003500310307184c800d0040441080602d8544608900200400d0828100a00480d4924243c400d8804256072114400740148803086200640c0c0c1c4d24400800d41f00d0501420103409105180c0008000c569062440404208007000421080d86a443c40b100203401c540200e034864020100009464082c00064a0075980c0c02c140b80c01142c2c85140071100c45901c0b401412800e042454000000f681c1d45481282c0285590f01e25a40140f500f00208800c0c0224004a82d110300d00d850b2100c0780c07495104e0091412198180c0318255102da032500000d103070001c02c0e800310f5651410180301280608002c200560200c0c0b20f91612185112000b08010300c00c0841c01d5010006851140200400b610440b504009103005a5000070a000b1075004240034080d1140010082b510008072101d0140d418802d9952191a0002070501c85909a000901d030b5244030100604220603074004ca9403100b40369219500a201400e0207041d5626 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 374968893 1250 374967643 374967647
    0xc0609020117130c05030a1a0a0f09080702130504080d02091f0f0f05040b0f0f0904240f03020a09050c04080105010303020c1206090c1002121206030606010c05060403080403031b 78
    0xe2003c00483d141ca440100006207401e00140c24141603074801c50709a4018600e0910300d14145005000c40c0d0741c580c03118605e0440d0700a500c980d00c01e03180507600d55030740d84e00a0b0040c4254510f003190b803100502d01c3c01d420000881d2010080d281c1d10050b081d00965131300880030024400e410342e1403e0718000ca0000d8401242c0541199070009041c041d44c07140e00840911610a0351140030324442c2901c12281041030b0b04d9415031480c02803001146110b0250305145558010900300da440c005995504c07003002c05c81350345850708041d00000500c248900004003d007135078041a10500540704031468280ca620214060b45074035001e480240008138020001503070740381002507a8803500500c490040708401d80c81c1c82c1e50300700440c08501c150002c2008040c0702101e203041c0038061401402c03400850203901c400c0c0c4240500c0500400c000401007400400a0422070201410104003030b280754184451494114000703000820400d5206805040100d000d07616130030150007600c1c1150b04543c140c3d14441d02c14072002e07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 374970143 1250 374968893 374968921
    0xe040b0a05180a0623150f0c0610050f0a03150b10030c0f0f0f0e031e0703020f100212030405010915020703080a0b060d111b0307210c0609020117 64
    0x402d10060034401943d50303481c0d1841c080b0484450321740c4820703520352109040c00d001d89416841d0030059045864400140d0070740c46960800c1d405850560000303401d0108a4407a1451a0051702c8100d811040c0c0754460300000744883c0480c40014a48580815000c103c11040da002003940c10002c2d040c00c0c001922070310000c0003000d820300c82030081644580c2c05107c142c0b09415492600c1226201c0d2214048504000c1d2a22090700d0201940f40c4500f043c01001c0c1c2e84000c0e400c041c15034500004050071401c502c104801c00d000c48002601940140050000c40c1da40000c000d41c581b00015802c0740e698541d030424502500e03e140000d480946054061450107a60f0341c002c02c02035011740d4400c490358072803104400513228a941e00c5a4012010300034441010140e501070000c0140c030400541c40c021070143e404000c100500808601900003184280620041e1444040c4580c900342c4000301306200098064960200364101a051715136403e40c805c11a40a2542107151f00303141510980755142840c1e0403070105d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 374971393 1250 374970143 374970151
    0x20703050c16050d060203090a02330307090e100504021204021305070e0f0f040c050a090801110d1a28060302040312050703140c06010f0b0702010e040b0a0518 70
    0x1480b881d109048807048071032001080d280e00600601001815880b5000a904054000c80c000d0158146440c0103035900341d00b0264040e0502446518200f8601d20306207040d50704050251171450070010802c00e958055101c43c10b0f00c51059035141c003034484a002000e500000d41186030070901c0004c4409400841685962149200701c810f0207003903100320480015140b05480884c007181c911446103c0c00d240c6468000701314000540300030240501140001c05a03414859907134041078002400c0d0281c141c0c0225440003900b81c080003404041c17009030b410bd406103e40c0110307051065907a078080895080000020820810081c0081d0803251100e11142810280240e04034140d070300079000090b150b0090003a0f8007100e0304641c1e00f0520490b058130503240ea50160390110100501180042e642c042c9139000b070b02211954000031705032036051004e103030050146c60308000601d5106000e4580140c0c2d00c040034250300c00c1d0a54012895405a00224442401940002b94015469800c00a01140b1040d84901c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 374972643 1250 374971393 374971417
    0x180201081015171f0303140d060906050405060316050d03140c1c090609031e0b0112021311030a0f0f1805120a080a150e0705031e011206050c090402070305 68
    0xc01e4960f4030038919850354480b182c042902c4144010008203001c0c007887d41a11070390b0302c0258640300411a001040b10001d802100015a494605025a0038144682513000b0b105500800001103041d0714021502507511070399224200c0540c0e03900802d44510f00c84045408c4844105803585141d464050321030320070143c90402c0051603140312000c0d5104045540c01c036511078407a008990b0643d00e031120a4117034805550f10015018016134001050066080d00031b04c070300800e1642e50f45d010310411060ac0e42d000743d5030b03071361364108124040300e0600380080301d0708000b44c220002a080b0540011402420641c01903002480c40c0c20303030b007421500300028013080d8540b060040d40d1118045031144445030141514000000341d8540008018007682c1c0e1001c841c15115025165855940d03040c41d44208008403280d000050000c41402811410781c2c0120100707004e07108006000e0342c1090b000c006841c00c2000060b00300c0380c40d40e000ca18402d00040403142e9015001c0c0c002d540d900c604e070901030a581d01c0307403a20400c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 374973893 1250 374972643 374972687
    0xb310311090c18060f04050a0b040603050c07030504090504050a141f060807051507020604090b09090c060a0e180a060303110609030904330f09180201081015 69
    0x2e0300c1c0c11070200319516503040b25600c00c010340300802400700f00d41151107904084507007000041050380d10700c89050028440c4205e06a950b904082c0014251100542500c5030f03040140020b0000941100c199426038a000500003003079652410704c2c0303180460a040c06000480c80444103940d803d4045030207182c800d011404903202440760b50080040382c45520130b640c055080410244840d00d03082403080d00041280400030704040030b580000b1041e03030190b40006015942c1d451038060300e082100e02030798042e10f11006008035488050206040380301d241901020060b1640e0300c1c5599654070748011012520001d201071503403912510b6440105814041079002c500303201c0d032040c0c02020001e1154826402c42d4080e604110a040501002c2c041c21500000210b002c043c1454054480304c40342801910f020700c5544810f443e06248103050b10f034ad43c001641c0503051403541718500e0348170741d180e0041c1582840c0c01641541d40c9100d24128031742d00e400004804c24a0450303854110351061052500860080c0307880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 374975143 1250 374973893 374973901
    0x50606120403050c0d18060528080124120b1306080d0219170a030b0603090d12110301050f01030b060d06050f0607260c010c02060a0507090b31031109 66
    0x6d00d075210484c0c40f00c001c0184c944814000c5130b00c9000904241e900c640304600c40440002005010107504103409400500d006c0010031804d600440b1144120344004401c46411844c0d00000301a44034481c400208030382c0b40c200c08070141e25440d04202c9501320f25942085401c0e21034845585800400704501c0c0103104000100301032582c0082004401c40e4080c4004013100c0c805446e600c019005400e601d030030b155503103000c8040c070f440700002188140d04a001502c8004c00c03800c001b40404041c0049462414031b1b000100c107451100b40b045038107684040365500c41038010b400c012009440c01d004031035000380010030040c40109581c0c01203410390354100c5906000380c0d50030007800401e018030b6401800c58103140c00c1400103054031083d00c0050131440c200c0c4c0c514043e030400e5484c2c2520025000380c40160300010800400041d01d225042c2c002d02c003445c01c42d210600e094070500f198017404610345243d814403e1180301104040440850b501d0303150f00c03980d0010b0358900f0800700e01a0359400c17450007000900005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 374976393 1250 374975143 374975147
    0xc03100504150c02030711040f1d011a0d030509060c032209020306061902010b030d050406021606050a0503190515040506030604081e09040608030a1803021003050606120403050c0d 79
    0x60000d0300944d004501b001030b0b54a408410610b0303840002e82242c0d440c0342c034000940c154043d8a8118230310035440080844860351407421603c403072940184080d01450304486a50392358060000b9240c0500c5c0c0642c8401c41b01d00010103d03c9101c08452035440000b901000d41c006143d07042c0c10a60b945c50a115169584895020981c0b100300d403d80d500002c09c11074410940100c010039034004240748000105841c1000200c0c2c503180e6240203080200303030f020900700081507040041e030303c3c14000b08050f0300006203000300140040c01052000310131303c2800f00000e81d00c40c0c100c00b8101036540017034009112505191111a1040880c020050300480c2004002103c50800150440c01250b120400c3e40c5812040b1250030862019050b241c280c10904001445881d903584c01480058911a40a5a6900c0c2d075200064407111344025151001605410100003507601d0302c8065481e901c103400c02150f1980d449002071080d1240b4694941c01e00c0c14003040c0010f25034007101420034000d0300d900316040101d4040d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 374977643 1250 374976393 374976401
    0x40b0a09080f0303061c1a0411040f06120f03021501060c11040203040f020405060d17130503070b0a0e0105070609050a020f1206011701110c0105060f010518010305090c0310050415 79
    0x20b40d4100c12840341c0004041b144031000003156020703450310007242c00c1000c00b1801c0074a05980c1621040503032030070000345251502c1400340155410404000741c91815a03040c410110f20b000203801c3e00f00030300100e01458002d00c08060072580000400c0c007503607112540503241348400801078619036a1204043d400c0d007000c0c82164000c07034100016201c4008140e003004050200100816088a1204031100c0051816001005d10610034000b41d6202c2203869030180b003282156000c1e51107640014002c100d6020381c90b044a00c03e00003854000300411650303005075101d100c0c82500929241c5403689a4040c01004100c61515900c04c8990040500c401000c02c05020381c1c009901d80380343c201d00c004103c0c2d0144120304140c981840170020501b00448054000e6680042c0103180340c80c0d44500400c83d2a00e0324066500c00d0034400d082c043d04201907140000e1207880b6952240b4145a951004104115400c201008034840000c0484255100820751840078110541d0111030403110300c000401c40c83c8050003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 374978893 1250 374977643 374977651
    0x90605010c1b09020a051908040f0f02040b060a021005010608010b040b091503010b032a1219060803090909010902011e030906110c0c03150601050d02040b0a09080f0303 74
    0xd5401250076003070300c0355403288298180d40160001c122400045a1031140040d0800659640b120303900c2d83c200c1c801d000400c003406c8041c0707010407003000200000221002c424054090300306041d03019085281c0b02003802031048140c0340d42d00190200301104041d50000c3c0e1880000b07400c1d00140070b141d90b42c0302c051b160503000380070700a0804000c1c0300030700000c00b01d00050300c2d542c0c030010031035028440e98042c00a0b0a500a80000c54940d00020412000d0b01e00d8841d41c1104000e000d2404d03031082a8a142a08180541940000284010b00c0402c048046404041c0ba040400380070400c42965070300040f90b5207a01905400c0c0c02072000700002811000103120714502d842d0183c45500020001a01c41e500c443e110034022000c0c199100e040341c01080302d500c6030032401c05465071860740c0d828003181c0f1780349011400304503940b096102542d080744070210000300030340208081c2400e80c1c54108054a2001030700031500114054003010412240c0036501462600440c1e1403c8191828541e0510701c40d9100e1104071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 374980143 1250 374978893 374978897
    0xe0a0b01111f180804030302121e03071707050a09120b270a1101030b041a04021b030d06060801080a120507021c03080105120f0601300c0f09060501 65
    0x600450061488440b028248412403800011000b90044860740301801c5030307005803059400840c0038000c040e010481c0c44a41d001c00d0070007070308000040382954414a071000c418a81070002001080e180381c014107039270705a152064218242c9251041000306150441c01000c80003901c22311000419800420503061020717080305500030242d54040da00c06580700b244079500d85d02204850000103240042c005450250310400c5a8002d02140500041c141c6150206840c42286017036580c80560143c002c40003020750090b00c01580301c076105051104020000301409849001c0010f202c2c1c40580c503a8403070001e44a40e41c84a652907600c51140594503044807900418100e074005c100902c5074002e50183c1100c92008007402e809410040d50700d40088040c1100310041848440103010906cac04002400c0d010106900403c0004038018019a444034180b143c200c540d8640c18103500f003c8d460210440140b140b443c11030319120114a00322401803810310410700c4801c2c003040d001c0b0307681c501806a00102d400507 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 374981393 1250 374980143 374980153
    0xb100c1511030c161b1503020301120605040318330804110d060f470409020315011409040f110a080d020d0216060504030b090f03040e0a0b0111 63
    0x1000c0910f0164000350010b09606114640d010010702404202c00d50016920300d01c0315500e140000c0c08943d203d4401d19a01418010700061149a07401e03050b500b54941c01800105107900ea608094504040150b4003640c1c080722603e02080034000300c02a8414045020080540e106110307004403054509250b100c40010b0381d060200d804600f5030700e02c103040310388010080c0c01c400100d503440d0811600c0c2d4100c5005000c1e252041c0c0c0340d14090040d4080d600121510510000103c01c15008501a41c04840b100d41f100701c0e101c5510041c2c460ba0b02c894040c503800380c100c3d61103051100c986886018244201641c9075640c040f151341f90b0030551a1103008984c00800204e010a00e0ba94000d4130308070226034a50445205c0d0360002d000c070230800c03011031541240d401603e200912680c00904001625100d1401e170345101408012080c0d002c000c65080b41d401c08491003103502c400032040c6c100707074684428100e20b200104000c1407070040301c00602d001d411031910401c272a0340901700569255481240340d003855000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 374982643 1250 374981393 374981401
    0x2d09082a06030a02090402030a060303020f16150912050303040c1703031501020f0d110709110301090203070c060e0c0901170a030e1903050c0405010611030d0c030b100c151103 77
    0x4104003568203c0741c03004000d4200038400780413401b20380085581524640d21900100145501840940c600101710b4016060f55600c0a184071141003040c440d00c0e448409148220900358460710700700002e80342c0c140001719022580c1c10038a5a0380c1003070b20113135104000f80710b000030b645a5440040c440c08004c480518195551800c248c2d01e05004545aa4190300071414003414a4000340160020003c1c00c1e04e0301c20004044d10b03442403425105422401303c5515101c03100740c3c40104101503d045404101c2c02696030740e10690112030002034030000611003810050900c5005901103080c1da84000151000790301d80c0c0e81e40e000e07840d42c03c03145d22108040e600800040c001092040c480400400301c098141d460083d070405503414105a140c0c002e40711a04a120310105615140c002d4a0040989140801094041e00c42c56501c900c0368010350108503a8600280000c2400b07038001d207200e5103004028030024070b0043ca01801900380c1210845640c07010044c1403003455220b118103080154039070300850541c0c0d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 374983893 1250 374982643 374982649
    0x3050307050c1c1e08070b04110f03061f0e04080c0c0109050105270d0804080c01020a020a060f120501060e0f10140f040b0c0d080a090308072d09082a 66
    0x38080e1500d4102001180d0a000032175260790007030800901c210410b26003071415082140c4065440d10a9611a290088040242d075070b0001d4032a410508211a112100781d0b40e4030034500141995004100250089041005100c0150090211040d404058509040619004461018403030240f41d01140301440900c00110490006280400d412000e14007021b100c180028003800001408640030300c40040c041c001403a09005d9000500c5080c00144940c0860b13134000380c0c0b20f00c1503014080400922682008845205810b02d900f01c1c80c0c403c00410036541c4420005028030508204107014484c0030011040a00780102541034a00da0341c1d84403e4804046003400b0180e44c08039803010381c1c404080c8804a02000c00e00700a2281e0441c01000f0080f01c80c000801030310710a03000748243c41c0f56140c00003a0b001300f90000d481e40d92040b01450103101c0075842c00d404290440c104072100000d540b000100d00000c0b600300360702c1020b54038070384104c0b05000640341c00c00b0f091000f0300b800000800e01c50f078003e00d2142 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 374985143 1250 374983893 374983913
    0x6110f0304061e020d0b03011505100507080706060e01080c03060106050a0c140106121e030203040302060f1306120e06190905100f05160203030f0f09120403050307050c1c 75
    0xc00f4405481e0000a0f10300240b4059800c40b12030209400d6030354100c00c0c52807409105260021403503140b1801c1c00e915000c0040c1e0554401510441800b000060150401908000b15548568042c208002c01500e0b40c00e03074520340000340508a540e1140102000300351400054030f80c12641603541c0c0d24504865003c04540f002d44038a03040740c00e440c41e810500b031850428000e003805060310f60510003051540c1e040412000144081300d03800c03d10540c0740c0c1d00100b0b80c00300494041c0c0341c0544800c0da8403100c0c05122100c0744101031a5240b50401c1c1d00020889581c07003000103854080b8008180070302d5400c5080e2079200c0c5415a042d8003266964860890110056002182c0e40c074021802d03034003482e04510080d0159400c3d856418000c590304da08010398108500c0384581201c3d1180f0003036046103481090307a021202c010386a614203608907000207144d00c104200000d0000011143c4589070380d5286030072662904030181c11580e80c003550b14844054108440c05000151200c010120015100d485004100c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 374986393 1250 374985143 374985161
    0x1a0a03060801140103061e0f0f050c0705030a0c081603080601030e07050a17030c03031305070f050906090a06051003021305010c0209040b041104051f06020105010f260d050706110f030406 82
    0xf864645580745000c0c1f0140b06805c0d1701c050400c40460f24554240141003125001480b01c100702c10240900c0000c40d1000090311171008090600c0c851082003403d0010207805510002d080081840c0301850030150b10001b00341c0155000c0e00d0610405010960442e25004075001e030940182e131a100421040d0029070126801c500d183c4142c92500e00b412610b42d0960b031046403500c445d0341845501104210b07082058030010281c500d000f50456040c80300181c0a15400b8029a00c1030301100045547d005007580000018403006048400c05002003c01074040d42008000d00903800c554200050507500542c0c07860b4150394003d003200c0150b6a9039840b121004006041616040404030050140e0744070b5115090180800c1405a0454000100c09000d104401d402490859060100400caaa84003008000c140c40f64201c0d4807000a444a9034078018211140b001c0245d0310074a0844228140c0103001001405d02a103c2402100c01940300000544500b28901003a41d40c10130020300420710b5039101c0460 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 374987643 1250 374986393 374986421
    0x507170322020d05030a02070f0e0106050f030411030d02010c030b03010c0e220c08040506100501051e0d0501030b10080604030c080a26090705091b03101a0a0306080114010306 77
    0x158207404e44039280780d60030010722180136a010403400e1180d41c200e015039000508102c1041700b2950b0425030020101c0c0a03d19034001d0116000c00402c0c104540c900501304480030140c1151540518803c1c02406800303040c60b03c07000300c1e01d020200d41c5581010301400300c40c80040d40f00c1e240144109014419000c0003050200460340070a20000300c90151402041c01891296039050070a00341818107031f013050805001e00b07041200604040080366040003d03520084910b2021080480c004e0030714040070312560350580c1c2c806241800101c100837280714114003503400c1d145005003854455502c17035990182030310b014020418071280342000441c2c20300100500100c4e498040047d4260b00149610600b4204209510180381010800724a108200340c02c01030600300e036200038605001040100040703105c2c181204038100000007800c841100d13100304006041e00c810851800703d41c0030b04141c0c5034111b0301d410f10020341442c03000581d2130702c14020f100c9440c6682c4003851a81e4615035444004044c502540d411b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 374988893 1250 374987643 374987659
    0x512011a0108040f06050103060203070806011b1209090f020c0d0503041515090e0a200f040c02010b030a060204030c0f14040e013b150403080603120a050717032202 72
    0x1790039001d03841c001c520406e400360326802c1240001e058075400420150403c01251603564040e1b0321a044451116044811b01041c00440103049620000540000e00c07594180405a0940101c0c1d40c000e2000241c0307002600e11703401c05248202c0b00b512040d00c000d00803591030004d018a41c000c99012042c089004420980c10340d9844180809540340f100074a0050740140d910030060007240041a502e01d6060800460f507051200e00181d04e466061340c40e240640e036100304150002c0d00075481060036081c0201102c03110313440780c9400d0340a91320500046441078180000022001111081d24050b01c070500088a01d00629000307100040c0322904c08c0c01c0d4203640352000924000c00301e429546d0707007026070580030500001c40c001c0410170428200100b80107504c1282c058550140c0d800f1515005030745031420b07221713a40314000040c1c502030302004590300c00000007950394032654128000f48181442410381e890066411010b6440c6804216000c0183c0241042410407a0008040a602c1c003440180703d01c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 374990143 1250 374988893 374988923
    0x6131a07030b10020604140102030709140d0f050f0f0c1c060b0603191506020303041e15090312060515160b010803040302130203041e1406100512011a010804 69
    0x3d43c005640c95002e0300560006002c0c0002d0000e0000c1100101041100a52a5081c0030400074000500d512419504503050164000316513228500c120440d608003043c49c092084908040f500c0c5c1140b51640000c52140d40c01c40c45020740c01003400001410020302c100a4500081c401a085851741003003210a140c0e10500d42c1a6540d46030051401103122070b44446110191002402c00c0340c941c4403011280c00c044003800c1101507400070032240e0180c1d01c00ca0146007988581044c0c2d18801c115071004201e64810207102c80005241e9100d151080e00a85e103c00da2007214144070340072503440d8010640c21070410502c1e51900002607005124020403140c044081c0344144d25400104842a00001d146410004080041d450a10140d030138520100d0000c610310304156960f00810700062100d045489540c1d070140060051905034051180346103010b996040c0303001050302035840d0b0316010301d40c851401b507210044c150314140304260b440c1121031030000a01010000550704800c0041c030032554918030000c10b07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 374991393 1250 374990143 374990149
    0x6011412150618040c0b13090612030e010816080c120a0f110a1b031101020a0e030d020d0210050606040807060207061403090d0e0609040e0601030506131a07030b 71
    0x30140041c0180345640d071410305008011842c04050340031000030700b0580c10302021402810144003100d0701814015590381140c0c4105844241c550300c6901080d14018000903050322100c41c0e4500ca911079541c00e8604142c00c0c0c015500e0039425240d81d080303240070303800318454680074480e0b0542020008908a041446510900240322401c440501d400c0f501ca2400108100f45402905101c603200380a880c1032903105d02000380050a5a1540a64801c1306642e0206250041e0300b2a060700c802000250369804860101800e60f50407a20120f00034810708020f03000c064408134400300014040d6014241e8020300100700405002f020344195484070301040002444401007040354000e211039005002071501e440c50141042020078105214038408100708139010002040110800140d402c000d810728908201140c07403030041c64015604603103420030003041e00d00d002070818102c0340300c0c1003194544d40d607850307004000c0310811500600041c111640f02c41703c48681640740d58804032501d80000e48280318400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 374992643 1250 374991393 374991403
    0x50708010e030c150c0a0509010306030605010e04140c1c0215030f0108070f0302180403020703200a090e0604030815040519050a1b0f030f02040609230306011412 71
    0x9480d5403001030003c6401e00d0622068131001c105450440142c0f40030701c003050070381c0b084068070303010000000b552904aa0003036007e40c0145400a00c104032035a16801400700600d0140c400380c401020007010118180c10000d00000480d40148c401e40d2031034081e1102d0f041c500303441da00490780310000c04e4500c00d10180ea034002d0740c1300d0126a0744084080d490081e50505145060300001c540340310301001070002d81c596140c104001010034046845556541c20100d0600e01e968000800b214a0410114820034010000400d10201211608103450342c0d86649012604d159000a03107540180300024040707401021065403051002c40c0e006c650a00c0d030000101101c4c022502202c0c100f030341c20210103c2c03210038032031994000c2c181c1204200502c3c00005050080c1030b1442c0403000c01400809440030148241c001c043c0488508100355103c94440c0c0d8082e0061346280289044010f01d1030b402d10040e41c03418031905580d10054041c0ca8140d00301009c16501e641c0c4180301a4102c240f005490a072041c1c1040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 374993893 1250 374992643 374992661
    0xa02371a24100e060d180605180721080d060b09040e0303150d0203030706050a02120705070203060103060203150a0e070305070c110402030c0c030a0206040203100e1209010c0c09050a0609020a0206040f05070801 92
    0x3031030329040140480406512140c00c903252b100c1081407080d07050b601c2602c03001148840884c91009140c2c43c1c040180c0c07041454440120f41442000609800c0141c0503100043c400c582c01d200302030741c544a2030307501e0004030317240485000c02c0981e4520030300301451001280c07400541078900d03002c0c0688500c002d540c0c0555100f03072556800a010030301810504034140d040811480c1651800c1c00c135800282c0d49210600010740b586a000000c15211202d0041c200d1100c00060700c14940241e07549403071011850219030390000300341814000f911251290010810071540007a1000c03002c410710f414880250002800e0964682e41000b200c14280d07000c0012b0100d140140e8001d141034a4944181410409541045481c1c5401d14258481810300410814090b0b00342d40540e83c0c60f0303000031004881410b49204003902d2084103440c0820b440c502e54112511448101310113022041e178501601c000c0303205106404005812207404500091a6295801d44442c0100d0840744026199440380f07007102c903014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 374995143 1250 374993893 374993903
    0x9020a0825050904150b1c0503030f01080601030804060c021c08070c080111040e150613090606021204030602090a1a0a02371a24100e060d18 62
    0x1240c070505020101080c0d0300a0401540c1e0b00c42035050950342d8031400144000458441e41d00c03800005003d880310040500d1070f40d118441d40b1407525050a1035500c81e442030f121665040340c0311002145a400002e03c42c0d04072988004ac41d45403500c0c000c8229600c203054001241e01c5200700241c01e10b40e80e1091000140580940541513a6202c0d030714100c00004034070380c00000c49034180a002115078400340281c4048810f0840c4411207595440000d44e0140c8045205030f502c1040030a90258841c914108102a40c4490b18200f140e47d4417078105999030300400b803805411007010030040c8000380d03180c1c000e0034821101400c1c2c10300fa01c0d15508010b412409061240d50310800c0440c00d0000254100003419482003840004423010401eaa0044104d0f5841d42d035000840145505e4013041102d2a01c002101d2181d0b116144d009080c540d0f848228a04554603000d58071524440f04075882c0313091314100c44c500029440d003d00c0c1c0d5a000c0309006e0b040e0803201d4102d8105a80d03603044400c103000c01d081325232528410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 374996393 1250 374995143 374995183
    0x1803040314120a030e011b0503010b0d020d0c081b07050a030e030f01060602030d06060908060402210307030c120f020705011101021330050309130209030a0b060108150904020409020a08 81
    0x50b00d04542104c1107d001c01e031a035950103d0400c0302540182c01c580c107444602c2e6207199100105900d10700030f0711580c80d0b0719205c2d40c60940450301d89540040340a01038000d2010380ea41800d050101c4110314001c18501030943d400814241002078000e0352400307040e40c000340c03d0b520800e50101240e403c48585034451405030300001611008111648181c5d000f504048c202011401d0400f003445650300d00041000f405140c6000e0a1080b82421a0840044052803400ca80d0b85805614005040c0003800c0c80441304404454003100401c4e02038001c03010b0f045810381c01450f03a10719007001142d40d51104480390340f807035500700600d003160190105e8210191445c1c0544015040240c11611034134111f075640d0301d255101c4189040e000442c0030085407801b000484187c0010500d40b03602000a03c120b400d001e80c584259a200d5082060714540d251082e50241c072140314070f40d00c1d003000081304030300b410f0700f981c0c07000c2d5880008005191540c0301c20741c8113001406110a81e0380f20281e041c64103803007140c121102800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 374997643 1250 374996393 374996411
    0x61803030a030603052806050603030702060706020d0b040b1c0c1805010e07050c0303011203170108010c030b03010506030a080309011112011401090b03010512150106030209091803040314120a03 85
    0x1041250790b10011b036001c2010000010000c022100764000d017001000e080c1c450010500941c0d0070010707200030a40041c101075840006141a0703000b03601c00040441c03058105203030f00c40a85403034413803118010f1010384003000c404140c40d50045045541502204c03031001c0300e0404a05a40d4650071594511310b508000592941031051070701102e04c00030030103010028104800a000c6c1320100a580c11142c4a26881c5c0c0c2c0d0f040f41d450150307503000d034109100d0841c52400340001900b032415044110303007c040740c0b82041404107180c10315003664003c4804c0754140e8440448540001d1042000b140d208801030300000d02144c2e5a82505070b01d502001840c890242000d0041c801c0100d1401c02c01d0b101c3c5401d0900c410044c0c944132401c280c900051188501c120580d01c42841c1002d01400345c0d01a03610b2610140c0c006603102c0e800a40207401400310503005e803010400041d414003103491007040e0f20014030011360800d4516034422801001c82080c14030f03207009070002241038040d040d001e00055030b4551004070701c03000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 374998893 1250 374997643 374997653
    0x10513200d14090c033f03040339030e04140708070302211905012702040807120f0c081507020c0a0303050a0306050d1a010f0311061803030a030603 65
    0xc0c3c00307800c0c240c02c003c4851910b9a000219444406507541ca15468410028104181030600da003126000d0b01ca1842440030500700d1400840c400c038400d80b162a498003001104807401c00c0e9511090290700756005241000420286800ca0784034400d01d80346401515140c0481c0c00e0303610b410a288440d4184000b40a5040d030000811580b1651032f10302142002510444165860a1002c1c42d04685140301c0100d1070702280c1002c0c41000c40300910341480742c6c2d651603110383c9515902d5420403c04941400d08100319148030700880701110310344001091410700f4042694040400740b0011512824002d0000380007030f9181950000501e03203180034050000043c00716501d0103a00820440442d040107031f805220760b440140380000e072070b01450034903120481c401094000704841d40200da0301c491003074025410000403500d03d0380301010005241d6401e90380d400204503980d120780001080d000340c1040c01091414450058894025a482840390750303e030b01301c0400d0650303200310302c0e03000000e07243c94050003444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 375000000 1107 374998893 374998931
    0x1b0403050a0c090606050a1e03060e0a0506040c03050f040b0702120c030705010608030903060a020d09021005031006091a1c1d100203010513200d 64
    0x244441c2031480b0b00d56510b124041d00c070b504044011a0042c03140b01a118014002d403a04d1102048019400c0301000105007a001010354178a00011410307400c040703060150031300b00b40000795820903070140402d85000901c00340a050034282401802c4a107900282d500c150410004d00b1503413202c0d50f04a003801c02c803c2071107200e1540032030082d0712400e000c801007510500c44c6d4001c00201e940c03482056164014494001c1e171642041002811a091540003005c205043c203200140034141c0364005120b400355800d000002070000b2041001a100312140740f40901803a091404030103103000c04040284280c00b00554440001040120309003580d500f580d04204055a401e10807200e40030b590a072040c0054503a4003a03885847d0032880910201c4c400c07a41a504046c0814007400f80b5428030901505c1742d24130315030308145419064001007181d03d016181c1d00c0840301d80070448082d0503074091084 = true := by decide +kernel

theorem cover : BRFrame.Cov 374820143 375000000 := by
  have h0 := BRFrame.cov_init 374820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 374820143 ≤ n) (h2 : n < 375000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
