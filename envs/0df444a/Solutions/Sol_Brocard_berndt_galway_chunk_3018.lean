-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:53.272981+00:00
-- url     : https://prove2.me/submissions/ae92a114-8cc0-465b-8073-144c226b2e33

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 542625899 ≤ n < 542805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 542627149 1250 542625899 542625911
    0x302040f41010c06020c0118020406060206060d03050c0c0a0620010b0112020d180f0c060201090f02100c1220060105060715060b0403140105060a080303010b0901050d0516020d03 78
    0x31550000802188020b41840303108441802003000075010746003000103c100801241109203400d001055100c817080e40600d14120000c00e081c8e04c0801d8032417150f43e010305100c5200c5a0b5507000c40b0941d010050704005400347c00034004042d900d41d0620703c000d02103581c1c2c0308100080210562200b2a00c0c0356041040c1e072511400045690300091a0328002c10308600041e1503401c1880d054000d00361445000c854100b114821108000b12100c01c8040c1c107009201d2140c4040d12503100f80d00300d5007408005007961034032003803074130040c0f601c3d003880c403074210f62440c1c000da032643c407940c41e00341da2129920320304085043d4070922422607481c2c082c414603c1104800500300b41d45481c0104d101752080b14006840c060b11003803000c40f5082550008401012002807941d620b0360b603030030440858940400c51100c2542404042030292130584c6441c8142c0791034801a61550346044102480c580c82018040d05018080c081a0b00b2211a840b50381d21800301040155454140400e0080c03c00d003074000d8000a00d86080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 542628399 1250 542627149 542627249
    0x23060409052104080a0f0b070f09030602070228080d0507120305040c0e0703021803010e150912280f170612030a02150606090303090f010302040f 64
    0x40c03040150b80c0c0200480300302c805408090b507001c0c85250001003442c8210042241080b17503500e542d42004e805810800c4079601d0b09202221352000002440c000504007031820300105911703900800c807841c8002c0000d28401c01c14042604006d403810002e0075140100c440401c000c10051111500382c40c0a807130584c0c0f41c40b02a5640003801100d18180e070341007560341c5c0e0004042120f04524000505a500401003207483c041c0001400b03540301c065002040113a54040c11050f05050058002003900440034040303c0402e1000ca0b20452801040c04981d8407a01806400725801440140700f01040d03003400b1a41e040c0003036810080e44071213613140010085416110400150700981c61500310074041c42000481d190500054410052030f00c00e65260f020020f10300758450707000503540342e042402108140142c0e031854200280c0380140c401d07058040d0010054109a450300c104001102c0005050050a05486e103400d4001e05400f034005100d61000030303c01880c001c0050b040c4119032004c40c808100741075000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 542629649 1250 542628399 542628403
    0x30c020d021f0b0604080a0809130b0303160302010f150f120c030f030e100807140408032506140709143610050f09010e071206030203012306040905 65
    0x8042e0500d25a50700e50300c1c07103c107503610340407500145040c1d800c4981c0308142c3e0801c5081548414580c2c1d2240c000d149071030180010302d025209400c2c4009015609005003046440b51030406428100d0865585074001c2586114a229040420f2a0707145d98174200c50600203d0441d80c00b45802c69002861410707403002c002618840b03a0001e40e07070321120002c00e41e085440c2c00d440903510b07016072560113440714903103103a0703146c1c403020b0310b4840c0503155a29007036280a800b05d205548914040c9000c4ca800401003100d43e45904140e044010748031080c041101c42d510344416049803003076140710141c402e0000510000a600885000250070420841e41161480c107001440c4441d5408080c450141005040241e0075907041c142003442c1c1e4504004d000701d103440040309d01d03481413601803103204020400341c00c015170804c502c941d4140c1c2d0160034030f41103580ba400001e6559041d81c55150340c4079615040c004c80113807000c0c020706c545001c070700003103040b07004040f01c03c402190030040c243c41c0110b15240034040880e0300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 542630899 1250 542629649 542629693
    0x1d092503020301050c0f031b040e011206051503190201090f09020316020f150403050d050114130203040f020108130c080606010f02010e070b0310030f050c18072715030c020d02 77
    0x1051510180f41c01109008c0e5225011303d91225a107041e81e50000100000d4412504080604c51803003003005584000070210a00c803081440c9405078401100380740011050780c044090140141404180340d41d842f0902015040950440e03d04c00e6004024800d00c9100000d40c210b20744a5030000e005d605404240d104d42d07079901a68611100042000403d05040c003440c1100c210f182d01e948280803d617195071114840040214586001e81c1c4001c800500107031a07813003134038003541d804600d030070744800b031070700119070340e01002e000d143d200c1402000910010709264041002000300d00060700552030030000260100d21171004800559040c03d0455000d600089041d0083d50840d002140d140e48590080710282d4109800003008842030ba00c002040c010001101e02c40ca520442d00d8007612800c1c40b00b4221489410b43e40100800c072203209a000c0c1d8121000440600c0c44500d5024000030350325150040700004201c2e1540c0402d0340c0b5000c003441141c3c14060000c2480060006080c004103103561101c6101c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 542632149 1250 542630899 542630911
    0x5160e031c0f0e09070c03020c0f0f040209210d090506090d260d0e01050a06030203032506051e010b03010b1605030c0706050a0e0a1d092503020301050c0f03 69
    0x140e1a0082c040c0103103a603858018010702691490700d41124041d000302c0e240b5006134054400d0315494189490041d010b4003500001804140050400e501800060b40008400070b51001501c007100c0340041139112003108610020005000c500c20b541c001912000a980046000c2c6408004005050300e41d62a1064800d034004038178800d0056103903410120941600d000302c0240800550142840c550750007100c5410010b100801c16625040c107500100d803003912009401d50014800d6080c0c5120800405000c0c1d108608501c11290040d902c400454074200e503441da0300d86182e000681c8200b03030b02e000e040c05403901403400380c915410f20f440041d40f0301a02c8001d0304d59035014120700040002c14010707076003e00358a000300c680c0141c8404000c1d000307400c50f00b442000584420001001443c0102c10702c0210b5142c111450403000305030840480004005010310b004d88960a00454404448050301c0002900c00a00d8201d2504500c10142903030300150501a2010f4140701c4203860701d04403030450b038201d8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 542633399 1250 542632149 542632157
    0x110f16150f052d0301091d01020403050c1003090c0b04030308070206091c0e0604090e16030807201203030109150f060e120607020c0a080109151e05160e031c 69
    0x2415900400f80350701074207481d9400d006400700c00000c00007603607009181074850060210404c003030b6034055070b4201e0080384400b622a074020059030f007280c200302040941590032413030b01140120842e1980c030303001c10441d03101a0507400001820403d2581c899007031500700d65988054502c1c1d0420040488d0303034040c1d0308003076030024605002160103a0b0103620042c0842c03101612254a8907600c00006000745040d07802d980c0036008094401c070304002c0c81c0008105a070303400450316003030015680300c0c084c00240007840e07440554240800000e155840500c2c880340490480d00850b42c0b0b606162403e0f0a0b240c518912190f4420705007010f025514020340d6070400d035043d918240013081c4174030780040c520003609181126175000c2c2400f07200300d4650104084010341015103145030800c0d81c40c052107080341e0398018060b00301501642c070039040309035a41040a10200c4c00860035540300e00e641d0000101e40007644c01c61040d203041e00c00382d00c025400484007084500e0850207041c0450124449070302048109000c0d00c200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 542634649 1250 542633399 542633437
    0xb0310060e0f1e031e010b10020d02150703020405041503031202070809040c05120a0e120a0f030b060c12091305040c0e090a14210a020706110f16150f05 67
    0x80c0d10108400d6815005c041e0205196080c0c03941001e00038180d1b080903038001c40c038a0050140d854000150320800e181d4586c002c003101d042c0140310b00582a0b0280584007015001c0000141c1ca03038840c01000d05284101840b0151613246180181c00003400e8400648024018040040031400706020354000100503a00030800000440c0202d60a11070014a212082c2030b91040c0300c0e040741c56610030f68500d0184000c170750520403040718040319400340707000880025401e40301c4d02d01c036980300e9007100c5440e96000d006242080c8a455116007012100005010103c40200d01e600309451300418074001d444001c82c0400203401c264441465084c040e0041e0100d014120700415100602007001c60344445c0c10440d011100080c1583ca81d4071034012260002c010029815160480d881c1c40084070400e45480d0003c142c0786113000030607038500403c041c1c0c04115029101024100d0303501407001841503060308408002e0103080800d18102143d400044108104100042c600088e400404aa042c130070030038071140308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 542635899 1250 542634649 542634709
    0x60307060504120f080c0304080c1e0d05072301020105011203080403051b060f0106180501091e081507021005190e030904110c010c030e060403080c040b0310060e0f 72
    0x740c0b4000304000c5c034407040017034820b406000203c00384c01540d07031120030f03100340b03062a008100d5441541c0d030002c2c0100c905c59414080c140380481c00c150340c081c1302d4000d940e8119624603503e1080507044e1010030075181c01000070304281d80d0a129441c09011042c00c241000390365610001c0084400910040a000c00094841d00c08142c000108014001444c12205680382c00c6201b5420b0501c2072080c9030201e900803c0304800c2800307010441060302e0040e942c10008601c0d20021680e0a141d1a02c0c402c00124012804034024409119145080c8021404054141441a4028a00002448c0c196001c61078003003405003450012034030824041404a01050030003190144604620411300e4071075103d03160000f03880013429000081c00308034680310001c01c420045041e05406031140a601124141c00140000f4002800382d01d0050300721b2090800ca0742416114240c820309640141c0e40d04842000704c81c01003080c0c6e9031103502020b001c00140c40f0303c044003003144041020200c0108100c0c4160342c0030204030308 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 542637149 1250 542635899 542635913
    0xb150304060510031e030305060d02031513150504020108011d28020a090609080d02120c1507050903011104080a0314090604090608010e010c0c0813030803040b0a0506030706050412 79
    0x44c503003001180814041100c0c03000e64101080c42d00f00c02083c10540002c030a85005509961640c0d0040c02a08a000e5210000203000324010804038910b80303c0000c600100340300d4080d207401da08120800003820300b030500000d40140d505900810082d070040042c0c5021014203034150b50415840a0400054003a0200540c820881000d1070301a0620214100034110360010750181105c0060700c0321100951121800c580b244a0702d007007000560301525002d007803990148000d0184021010507130f5980a000c070303c03802e68600141c81580001e1800710310628103250030300c129820400000034840c501460300c4003035070311071103071b82800703800e000003401410004028035044030034030703580240819038071501c0d030741c03450010f013042e00581c0b074558030303284a540184c0710501c10448a40b04c9a201c10510244aa440d0f4000d580000e94000481c8664603001002515407030283d030040344108906407581c030b4000d10340c4080350b000800c6148079a0004104011a6822100301c8003500c000c403544200c0310030380b41812a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 542638399 1250 542637149 542637181
    0x4180f11090a0306050c0d0207050c040f270204230114012a034401030c0b0c070f03060506030c0315191404060902130b060d091103011e0b1503040605 66
    0x81f03407480c0001022010400085000d4000d486c044901f00102c04181ca405800c1b550800d020b041ccc02c1c4500c0c034007031040400380550701840d01d20041c0302003200030130074020b110104582d03241c0c40c034a0040c02d4014041c03a00200011b4008003400e28082d194112590700c40714104514415489807084142800014503205040244040c070b488201011641034148008610300340c6c41140d15800060b07069800780c1031210310060f03412203401404180c02c4038100303e00102554400c1800840d54403507103400154003a0207040c41c50040d401068001002d2074540300785410441082401c43c0319030080024074960440c000202900a8490354080310780f000303a00d10400003440d40c241d00b103030040c810008210070041107420940c031851003910b004d000742004610700c08c1960541d8044562095090110100d280c00c1a88400c804502881301030310300401d10008a030846666603d00d012481801100362007030309960117030400024090312081186508031040c0b180c036000180004265070340b648041546105520022 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 542639649 1250 542638399 542638417
    0x8150f0c09030a060c021c05070507090c0c0b0106020606330d0608070b091809060420040f060f060509091602280b0c07030507021504180f11090a0306050c 68
    0x104200c170905039020303595608005010750000c06a02100364441e10030410784600c164800000c00c001d03403d1100c010b0160422500d1042000b45900014010612032100c50b4000e044540141c082424800140022204c03c0e154480080002c4503032211040c5500301c0242c1c11805895030700b92600c1049440b107010f00f60a40c00215240700b819000701d041d0310010010b103003c41049036040300c0034503003005114010f1401c0b00c580019402c4000040d01140410760b01c0311181c0c40c400d2040c0c826a03107000016045030b0701c070120714049a03131750074050000c0d800f000c101c08040d0070340d410040d040c42c0440000805800000700b00861510441c0c01d501a020b008100180c0c0480720401d089241603005595028903a5050070107a03071701409a80800d6840c0c0c0c003041119240c40d096a10740f4540603861302400038039400002c581e0191007080000180c0c818000308100c0c6030300403041c0d0205040c08405d2007001940c40242661003000c1d010000844070760754600505003141e40c410310110f002d54510380000c486005500d09 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 542640899 1250 542639649 542639651
    0x6062e03150602011a03240603100509010209030c0a0807120f020a06170a0b061b070e090109142b050d020a05120709030c061103090d03050408150f0c09030a06 70
    0x440c400f50190041c064450007804802e9159494004140c1d48820060f01a80300c0f1640300541c0c8401e151040349907a000501604803407001040740303500c508480b0700316070000c95654041000c1d003007460184a92107400c5412034450840c40d013092101c0b91078206a00c642100c1d01c244440c0c0b4070400030242d001800098000340140000d650341e43d400ba204040c0c46001e8200088054005200d20780f59106900380f80b44003400c020b040007114040315885c0901d49015600c6889229400129040600703c254409d195030000401c84031024900300b442c001000d83c1c0d500c2d558000ca1000040c1c10040d03100d00621602d0460310f09003d4917a07500580302c2d482288174000075680001482004950400001c0c00989400b9000842c0d50380c42030402c448400c00350000070040b40991100b00155407285124540030032000095902e8001e80c2c0307000500c42603103481c0c11004640e011408001c50042031080e01c1082c0079050110030f552405141005099038000c0c03041034000c0d00803c62003640d480c1086082035030356000e04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 542642149 1250 542640899 542640941
    0x20d0e0301061e031e0c1802070210052136030a03060e01151d030705060301090e0613050a020d1703040b0604050601050a02070e070203070b0c040806062e03 69
    0x190721000b10308078001543d000c1c0103002c41a01c0780110182100d40c01c0d0b00306d00b415134a1800d10403100b180114288440b07020365024800c620150b40c501c04110741c2480715499a03a40c0b1041c5038401141d80710b0704110486010344100410403070b41750719144a016041080700c1e62060003601d15040550f1303a50905003102a108c0031841d068403a0701a40002c09640364400d0302c2216a0740ca104841a12005403c103400107504d50468001881e010f842c2ba03102c100d4005c0580785825220b00100c0c9454000364400c01c200781e01d441d044401030000f0300030f160708281ca8a0315104050b96645441c1d0b51000609402405455003a141405101a03c503000c3c10014050840c81d0762802d10f428810000c04007603810901c60341c54000031450301c1d80643d08807011400b19401529009203400f120092440008125401b507020410110001a0301124158850f1113404009600d0300d0928882c03030b2030b1181c024200c0d0b000d00c0c3c15007910940c00142034003018040c6070080311034a400c004014201c0280c442c0b030303440c2100041058 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 542643399 1250 542642149 542642189
    0x40803090420161112010b0a08060702070e150d030302190201050105150c12030405030301080609031614010e01020409060504050f100302064e0403020d0e030106 71
    0x2000500301250112000e100d5200001c1a44411035051a0244004038040040107503c100000d1545881030240d520340003104076000100700c459414184a2070280d550b506514010f181c80880c0704040c241075001441245400304010355100304501480d15204901c1c400991001c207410a81a41c1c0c0314050a18050b800043c03070041c1c0a03400124214842100c5c040d01d48042510500c00c841c1210790090280d80c0e034603e070685004c2c83e50300c50950607480f030184181d000c0d441101d0000441c001c9114600441d640d6140074852403c0c40c0c0f0140045001c0d4204208504200c458143d42c000d03807980001c8281400c01d060700743e640c018104e0080b0308650354004140007850803065805501200c10682c0c082c090340e03992400307000d51441d0032140100c941851060500150070101c010304003025079090302c8001ca180c1100f00c0c0309001a40324038480092018002d0b07503a4404a41504142c0c3c3e981c0e0740e02c1c3d1126060503034000e901c2c1c060011000301040b90700005a60702c0e03942500315500034030800310030a60009100d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 542644649 1250 542643399 542643403
    0x15021005150d0305071506031103010e1c050c01201b03030c0a050918040c06020111070804090510030f0510180c060809100911030f070e041b05030312040204050604060807030b0703020c030408 84
    0x1259a44ac401d518024440101580104a0070b0740c14003808240c0000c641071000071b641c40d81000001481d81c0d0b680b10341e8460b80100401c1d2100d49044003120113510323801c02c02d5004201c8854640740500c681c105005004000702401c05039900614035050803a1120707051000f0800444000180c810102401c00600c001e010180c0281c03403e80d9941c1d4028001e156103040714411030b128908008160100c2004108581d40c2c682d0310550f0450040d09014000070755a0310781e508207142c11541917800381c00c0b500c16883d030b08002e880740001d11402c0c9080d4041c50366a0382c03100c8211148612481040c441080001014900c007440002c9407000310100402c2800b04034103007a42105c10b0405032901034030070701c0411908880d00151100440341d88000810803079449503030303410140c20b000860802c2c402841c0004074050380c00b800606229480145107a4592074607004000969001804060150785014000c1c00030007004602c0710140e0340c0240800c81981ca485004500070300c03e076801c40c50a07000100b4045005140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 542645899 1250 542644649 542644673
    0x7290702010e0703080417010b030d02010b030c011b02090c0904020d02040f1703040303030e01111813150501030504141606020c0103060f180615021005150d030507150603 75
    0x1958000c019000b4100181d0350350f0149400301600d80e00e402c1c0003c1116220311844e40c8140900240003064405c4041c0100c1d190101610031207016035180d44620529003010829411b080c6400d10345090f0b10307441204d1014210500d098041d000f120b040000580d28680c4401329000d00d00083c1c000c541d2000e081c001030000350007a0050400d0a10310200000e0034058282c900c26500b409c80700034516003480c40d070b4240c00505000a07a03207855501d444c51226941c41c880003501036640810b02a16a00111000300304010300300164640c1c071586045240c200c034400d1256680291130080c00c001500d0744650401d60ba1680110002001d5880340e9440d4100e081c031040c0f408400c840c010380032503004075001001901651300b58003031059180106542004800c40c480740c04018907410101c0050465114aa2034204844074030401c0c02680c8144441c070f60b13945040c4100e03640081003038022440e40001d0320004d420040300a07070140c104140031482f0014020350002034504c2c041d50b03050421555507245041124110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 542647149 1250 542645899 542645911
    0x30905031b060109020406021c0e090103080a021504120c0221030c06010e0403020a060b180103050c0307090b0619090b040305100c080601081924141806060729 70
    0x3555000080d91321a5000752010303180640c015092001a64488541d40f4445141d01002c0140c60012440e10f40c0742c102d0b09034065401307038a2b6030343e5507421502c01078900119035a0310201101010b0401000c40c85503103803000c160301c8500d401c070440c10340c0340000b4140c40380300789015824000421031b941d050040000144446490300c2e00f0345003a41e90301d03c3e1040d42030780110ae002d00541c000c1162580040c0c0c80d40c1c01b10402d000010124111780340700d42089103100c038098204696aa102401d011041d00d0100b00700d04c01401c0c408801d104a2260b42d01044407401102c403404c0c9049005265008050f0049070280c024080702c03041175444070394a06225541d10112103212200c1c502d4000c16440d082d01c6940018030170380068494920584559020703070000c200740c0c0034034460580d172848250203410a0000c41ca901014401040c962a414048401c2c0e1149003c1881782c81031264604084032140b0f00050b099201030111943da444503a00e04103a04052a25a5140c010583c1d5010300e1b00076035006100e250042c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 542648399 1250 542647149 542647153
    0xd0f11060a0b1219060b06120703091b030309090f0603020d051006060903050d0e030c0301090b04050f0f0d030e0c0d0303020a080c2b1d0304030b1b070210030905031b 73
    0x203070028041c3c1c0e45445407108408414104c0945940200b00141c0000d261424050038840c41d080180c001c0e0fa19209003a15690002a20761480c032003071141d00951144e48620034000e0300f034104c0c95541e018103650319512400c0321254403010a2a544840795120b54000c0d900074141089000d181d1400a4940860148030b5540900c0d00b80c1c01702c0e28038030907064001502d42c07000080c040010800c800340c4903403016a850550501c0394003226605a2028080e400040303210308420021428545042400c01d10b00d6103101c445a031106641d411031050001c1c0c0c059014407070341000142808010b0f4000d0408402141268020300b4004000b004c05525a00615205181e46c5d110070960302c80810000301840303414150f4000320400544040000010740e050490401481030010b41c1c1da503492452400180850402217842e000071501b0000c2c003d8942c0490782c40800d184802215811010184405005da100061300481d240d00c65000003d000f1352051110030b400400b1680c80d00c0303a01c8880c0302903200b003c06148080c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 542649649 1250 542648399 542648419
    0x40f0b0f01061704080706021305150c01060503010c050a0c05150f0f0a1104091518060519050306010b03090a0b10080f06060312070f1205030601030e0a050d0f11060a0b 74
    0x2690820ba00300380135551011071030340f900344a03840d8403010b9008407030356214000070802d00080690300c0c80030300108d0004e880c91882d1103001200b81e0900310781103a80164003d9052104d4150500d47c04412a004218282003603c070401550410529000d4100c80161001c3c80d41403d00c9503681060480b24030846d01d0080540442c1d44100841c4c1c15140050364000304e80900340070521400a80d904408076072100d5070090301040381d0302d442482c1d202910f01241e403a030981d550707424030003814006200e640030708464112994580c50314005c02e81da0706c0148a8903110810200c0402e280c08424800c0c2c0101c01d070011120701480c103109518000b6001c441c400c1c40c03030610900640000d036010102c0d03014800d0380018042c10070300300400400d03401d03a80038403000c5030001c00080e04140003401e488000d0004860b01e59a0940703030700d0a50005421a0303822102081203610030080580040d60000344212984000e00d00001c00e80080b6a0a49820707800003402c000c1400760804001c01e0a0041c1c1c0f00308c9076854215480b26034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 542650899 1250 542649649 542649677
    0x7112517070b030613020d062d06050922052e0b0a1b050604031209020d150b0a180f060515180405010b0711010203031509040f0b0f0106 60
    0x40d06220a003850300340d0001c01c0100084520b4034042c591086018000381d0b95882c683c40000100e0344007407900300e0320039a01e40d01802180ba8441410110002201020b100107201024141000308030b40b1070306040040008041c80316403207505018500002241203000e911111554401c05400101c0d103542d02c2511000204914007007448040c0440c00c1ea288d01203580350708042240840b5440781c589201031024221440c582019004d2810303001078051000740440741018a0003d120000c1d06103518141800c080c00031026903910744c00034a00725031183e0302051403241c010030340015085818480d6401301e01c0003400942c0c1e1600034444514040d010000f0807850b0703200d0700f4000403180c3e1805000d400c588020104450702d04041e0042500b040e490240c601c80038031071700c00902506c0c4240c015a58101010445000300200180c1250429009001075802d500d05003514800c1d01303860842907441040e00780082024851700c0110f038000309402c1454052680340c506200703a5550b800b031241d1400100b50a41e2605 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 542652149 1250 542650899 542650919
    0xf0b030d08070504050f06090a0602030a03240e0a0b040e0a03020c101709120d06090b01031a06090a1d04050d03140408030a020d0c031505040221071125 67
    0x2c810085602c40c0360405041c0f20078803c0c800000e2105a400007400c02107000c00790344008281e030040604da40290743d40c0c0707043c0340010160380e1100710350290700403c40c680c0075180c04404403600c00c0d0b40d4030310091481681ca1401000c041c00c2400306150f0028030301742c06198a500301151002e8a180241c0803a00840e00410a10242c046403407082000189000c0c0700044101c052281560401c0b000000c441c1160310055801d1900d03030000500207201c607030300c050410205040d4004d107000a8000d0034204924860001c451061140ea807503840c3c8103040c00200d078521303503032440304c1c1c040a06181380610504c010b0f00088c003464214243c40a071140c1c495541481519803190140003403198403084101905c0e26507503200d059981000d03002e507603001d4081c06002c07400441403203103010301c0504d95400f14490104640907000a036194102a005500400a403400840480000d243c0761110b42d564002540c4c540d001110707070380c1c03a828028945003e11100c0c0002a00800c0302c2c400064801004289100d544031907030300b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 542653399 1250 542652149 542652151
    0xc0e0a0b101101060e0411040e120415080105010503090d0302310e06030307080a080a020d05070c020406060201060509160903020d1a0f011508150a0305060103050d02030906120a0f0f0b030d08 84
    0x101f85a48211400d04d240c20160888580403851804580002c0d48201d581c03812500180c00600742105040f40040000390f0002030b80d0b00404080c05d040e40f56003800c99225841d04030380344030807050613000075110314005591000c6003040c9480303440350f12458a0840807801d0018042c415610f4552440020a01a00c1c010007150011944103003401d01c0c00700388450540300d441000340342d0304015030300740600140b80c003260203000d200d0022551241000c500760310404c0200c0360207420103011603240c100c0510664556040480e000110b0003400f10342000700d80c0088944040c980c00003904918803900c0c0b402041030205058088403030052000c040c1d17503034a070117401d1008424491070003241c00d030500c0300c0c01c054002c543e8a900a4110300d1752002703814001e40400c410a0030f51f0b004a0b4141d01040040040c00802d00140342c1ca0321040c40910310b801c200400083c8240158800c3ea04061004004142154102c3c1d0000c801d907100c100c0c2c14000c040031045080e00800001c54120b0090054040210034144030790f00d01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 542654649 1250 542653399 542653403
    0x102120c040621140108060412110c0f040621210c15060302030726010b0108010509070e04051e1308030c070212011d07080304030c0e0a0b101101060e04 67
    0x2103c2e81c9141d910500c51024011408042c90791031903014055031034803180c5800f1b494258000c1c00e2605161404d29000c070102401c10040010b00050520b0180021900d2070307060808441c220812005600082c00419855000030342d84007540b501140034525800c600a01580100442d00c0001c0d20424015015050304185500083c820444800040c0c40408890803654110310000b40e255102d60101e8580320382d0f600420303024408000400c8001200f03080b41c0110510460082c02826140c42c00a030017103c041c00750510410702140001c544a105041000c10910014024041c600f030030560040d25044a2501115075003a28000078008801c0d071240d01c0b02c86074041d0b442442c0d0b0b91001c03c0302c116500200b4041b640814ac0c1c14103201001e02c00d006801100a492000b124111031a02003285050029031221a00e9041448100003003040c03d2100e90403074000542400c4640d45509408009104848895600c80c10400e5429a140da000f03c0c1c00c0c0000220340020400710340c8440180707010200403200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 542655899 1250 542654649 542654657
    0x616030e062206021209120a051006091a0307090209031504440a05210f061e0603043e060c190507031a090c0117040609170c0102120c0406 61
    0x1b00b42e80c10304100c00580d81a403800019030742c4210107130740e42c14100302840b0350403800c0c0340d10f865051281041034850114140c603e0310110501180d0369000c651294481e1007070040b039070342c041003143e100c1e1070070b0214110314a412125003d040ca00740ca401100c88811a44000f24902882000c0a0a440e081203504d80307041c41200ba030020a20403001e8180d03a43c0540c07007140070041c051001d540e4103010040360291110841518020b5842d000c200409e1800c40105482d2090a002c404c502c562240c140c3d80e100300c140f0a407070345a83d03552141050301c0b514054104110750b02400d1a400090359500c0c05d00a40707081c440303004442c002e44400b010090180a903400c1d0a001d40c00c071050000038060304030640000d03548030300300b902e0400341d40e5160003298129800052500482120030005101c00c18020003407001c1007401c040400c00c252510b100300001006000501560f03480046209000c1060407511485500d40c801c0c661703074840031003d20301035081140329018081000c000710700c0c400c0b61101690240c9a455413 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 542657149 1250 542655899 542655907
    0x60705030a0309110f031c0315060801051504050904060f09021804020a05100210020d0609021c050f0f011203030b09090106050a0e040218070507051b010e01030b0616030e0622060212 80
    0x780344508047c2d2a1502402d01d562008010f10202040612070000c2c15641c45a8140d9071505c0c00740260f4000c60003410000d5a401c000c18446551082714003604182c1111000441c003d8107484480284100074010394044044641304d042241c00d041118411071007540c1611704c003543c507414840081c0d610000b031005608504641d500c1210b441d03001d03041c03901030b0980100d0455913880c9000d040380d001c0317001400c0c0d00e202c0c48102040446580201c3e81c210030307040700800c1e17140340551600d49035031418001e81075505030f440805000e06100750444050380c44c0091416000c1c3c200b8543c040e00a240034880c95005468070080080c44016240c3d844d88100d0b00a0b111840000c2540d640c10b409200040c0100d0600000303105840206000300001d001002079449000500c0e011400050154050010982d041504001c6804015150301b000d41b00301000a90801c800b40c003451a05491025841c0100c0c2d0300b101c4045002c0c030712107400003d00101d04c0244100900c00c25100c800403620754542021403510381da0108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 542658399 1250 542657149 542657173
    0xd03020711180105030f0d08070f1809060807050d1104090c030f030810051e0103020a0512040b0609010b030c0307080415020307030c02060711060a0902060705030a0309110f03 77
    0x500240031a511550a140320309070a80300241c002401001e0b4415042040c8006100d42d08007008000782c0003040c0d00050401501d044402400d100e0010000300400005201401c40ca0303001d0034400d562454151a000002522240e102004009522504403076105000300090b041c1840d03d8a000d030190040303440714490458805201c007a00a651040b030b155180c0d21000130100f08251300310140d0711300c80e541c0c00c00c20b401e154582c004801601d4000b240308078254000c0c4010010603d0410b54014400e00740580c843e0090942941c080c0a40030350b0380070082d582e900700b004218130b81c00542d00c03600040350b0b01e40c4203988a8610384e03240c0c0400c4910100018007000468075060140d00c4055000b88200c0441c44200002c500441c140e8009440000129440f26104a103032501030014941c0000149421180300446c4000255503c802400200c0d101e030761905600150340301c1d01c089480360343d04402280d43d00d005000d0010001c190414090310681e81b0743c9004c9006142c001c2801803400c04c014010302c0540802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 542659649 1250 542658399 542658401
    0x9090e2d070b1e03070c030201050105181f0b0417100507050403060209040615021e060610051b0304060c060f060b0a0e030a05070f06110a08041710090b061e030d03 72
    0x80c50300702160301c00c03600840a40b80f603000c00641c418091550340345051445481d000c0e0039142c06800c40c5108841540b40400218010b00360300f544032400f4080c0305940800084080700e00010b07500f000100b00070000300400c0340c100b400548101401c070035044030800318003e8900400c0f82c1064a000340000e90410080011820f41d40150158017001800010300584d2480d110514203540008900560000c840c8200403444864244040f240203c02600b080d142c154009800146416030100c02d00c00b0101e848a40036802d40d10245e030700020842281c1e07403903480348070161411801210883c0c0140c180003851041c49524004c0f40115020303401c6050030640b144070b0655209080309281c2ba0184109207040c0e011581c00c000315001040d0f6244e05141c01820f081000f0807600030b40c103011200754040c0e8810000030342c403031b0304450407180400155071102c01940042801c00c8000c0c2c1c244590750341010180c9083c085d1402c06a80140c0b0219240080e514200c0541906006030000f0207505400008035542001d0007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 542660899 1250 542659649 542659657
    0xc080d231c020c1902030f010507020c040e01090209010b0c0601061e050a03021e040f0504090809150c0303090105010e06030a0330020714010b0306040b040f020109090e2d070b 77
    0x107424000d81068094040e86240c918403c1d0705101d000c64421420044d41400e00c440301c0e005000b10000c0c0041e140003100650741e05140032080e4046c59a41030311034240c040a51044503034940c001d28002465949140d88202500081e02c0808a030143d000001000c5002d444084e601e04d014040301ca1307044210130008e41d0150040c2c2c8040c42410380810220107809190304a0780d640900280180c2d0303c403810850301c0000b501c615001039020f286401008000704842c10140c45d860329046400c00c012030142c0740701e00224000c895003405070784008418030032210819000541030321090382010759940c0d140e5007059900d046108000c3d0200d621903110b50a1150380000303110641c088c072460100c20100c03000c3c1d514100d0f8440c074030581744032103903030710340c0a81140a00800a02c244110001c0001e810a902c41c1c01002102600081000038070301c11050441e402955200b00a00e248101040484802c05100707440300050462034102d0328009400c3e00320350328100858480c0d05900d400401c00b990400310300540300d0784 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 542662149 1250 542660899 542660947
    0x1061805150d0e0d030e011a04022a060403180b1801030e1b03071d071b0f05010b10030c021518060106090f080601061403040c030c080d23 61
    0xb0080440026424001ea0400e404410000d0091400c810700090031a1059601300010380d062941c3e0100c9a00c2503000c002c5442c50403200183d03600724040d0043c108800407042c0d8030035280c07011050002c405000c00c0ac01c0c42117010f61908800f50034040c05e070b500c6101701401005401c680a00900e44c0c2a00845c2259003951010b040c0040e40e403494850782e61a1840141e00000440c8070500000c1381d504007030003408002c01001d4180b402511444024250041c00184200b04214001101e040213201090b245c510150300300500600f4a402c0d03042c001e019140320b00703c0c076025211900044200300c1c03007032140810a088175800741607441040112070803180c0300640990140d240c1ca03003035440305810a0146600900310364072a03212403440d00340300b43ea1800c0030764030809441c4c00840040113015000508282c80f50421134020303a5070380d500d2401078415295500050b1141c01c220301d0200d004000040c4600400846445811850900c0c80c0c414407084c00f20303181000c3c2464240400610880820840c8071550 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 542663399 1250 542662149 542662189
    0x1305040506090411120619110307050f0a0504031b0501031407080a18080a050a090902040302010c030c020613080105060f0d05190206120903030703060b12071413081501061805 77
    0x100c000509a4640402940c221507074006142200c0c004540c1441003800a01d442321501d401c44c5040380000c3d2440c00f928460041d800c10004a046080c0d106004860155511018500e02d0803016250b86003100424084c05010901e042120004900c2040382188100d81c641d40d1403545a489103000c80c01342400c0380c0040041d1095416010001d0702c4c00340034041d20083c07a40e903140c0320003201d4802006035849901c20752540e4410041880580d0348054a8081160141020404408540b000c60064421501080c4c24205a0200450f1410040d006640910812149010542402820454581d0301010000c2003070340084121040d00307100040030030314980018035079030402d108a40c0902c5022001c903803218954200004010220350584034900107002c044c52949d0070001d00c039002c148040e9024140d6028803060019414144a490b0101c8081c00c800201d48140b81d0354808041e941c0e03517041c200001d01c40100e1030010580612504840300469160485450014a4541030049542d61040702442e12 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 542664649 1250 542663399 542663419
    0x50f04080102091e3604050a020301060b0a0804230a0b1603021c48030203010608130c0b070818061314042c07170a031110111305040506090411 63
    0x50382030414140d06c11030084004c1e14101743e440c4105404c5a406130011005ca0b04244410304406600000c0994410390017941c21688000c20009003004090040a00c0142c0c4a11030651003007111b0a0011409010b041e065504e00c000030300c000b50706a004000c405040e03040184429510900950020380341c400909500c403140c9640da03114500407041c0724051041014911015440701c000d03500b03c8110501c100d00d021030955040c008000d0640342c020300300c4042c1403903c4c21140140800540315600920300c0d801456030780c5829203099249508078158032841e00804c0f010441403030600340c048840114000004c103280f03906007000c0300311742d0301a4a01c40703800030355039004400641c50204082411103c9005180d41e0680041441490301d4603d800400400384640f0300f11601440015417121100c0e81070900843c6040140031003881c084003180c01201c55810601300a0303040c90500000c00d156034014110040c0103071510103100584100759a0950030a40f403800003004110180038107840399100405030a00e03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 542665899 1250 542664649 542664739
    0x50a140403020d241406040903021c0914040207020307030b10030b0a0614010f0801050f060d060b03010512010e1f0b030703030210061205030405040c050f04080102091e 74
    0xa244103101c1c04a40020003081118446118113205481d80204003a05004c440e45103400e00100c44005000f10f80520344a0942608250091048059409030110b54910303a0f22014401054803103a40f003803080040311061080c4403800c117402280e2010b40c000d8003c000c0149181c2d9400360200000f020900d01000156010000602080900b40a02036400c0b0124901d1300302041c2c4200c011000003003a0501a00030078142034150405181c60440300e0031503e40700c0f140c0c42000440c28130b00c82d60419002252401c6c03800304407134001101960503103c059504608011540d04054200e0700c0c610f5003601c030350b401900b000e203032100c2079851b0007540c414080010a07500d485502084c5000c40942045015820a00c500e0b040b000301c620a0000400c03e05204402e102c1850700c9a985920503801000d01407504d4184000c4c20500920481c3c202030990b4944550300d82c0d03555002c40c002e401c9002c075280700d001088550102300710b90203400007c07c04000c0041201e0005d41382c152400788058160303240100288401082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 542667149 1250 542665899 542665909
    0x6070f0501020904050601030203130303020c030c1c020d0809100908040b1c050a0c050906090a0f0609050406090219030902040e03070c030c062a050109080304050d080603030a050a14040302 83
    0x18146114030009611510400200001e51384010512410107105204203c3c002c85407117540d1001a0301801e00594400c48907590509610401002c20494454140c0e08504128618175000ca03501d8160300740d0300148604181102c0724041030f00c1042c160ba000070002041c1100c0c552101c1d402d140708844291405954a42582154004010020649154000302d10f00d180c56401440ea00070020002081038282c03040700604940240b00c1958002e02021952803c81d071900d40444000d82655010004225070740e010081582c1814046d003030196040c4040001c0308009030003500c0034112000d41a80c80c0040d150310171402448800d0007a6802038440c092410b4070700081c4001c14555004e5040740040c01c0c1107007449001c0b426181d121604100d010800080aa4808404100c81409030344030209945910b0a0040c00340074600001740069800009000c100040000c4507842438913203464449080d45d410341003540b64000e03071321003001043c1c04204054442d4402c0e420405080520409141040c0c3c0340e4010034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 542668399 1250 542667149 542667173
    0x1d01170a0c0611060c1303080904090c081b060301030f02100903140102180f0306071808030406081815060d050709020705031c06061d06071704150504030803010e060607 74
    0x5002c40c1c0303041d020402000b0705014240c0d00032249031201e0320b08541c07a1411065140341f0312010f0902000405c079404955101d0300045403081c1c0010065811a8031380d000300e0388580303510050001d02030600c59070721024140300c0d055034100e0f81c100302018113034910f54003446910294140c2e00740401480c400044006030500303240004c80c0c0894400103845d5a80140d120048804101c01107109114170021710b281d41c0e500042d4643e000c3c03864034180380005c100380e42003801c5403501d4000203124080410042001544020001d00c42c045d00c50b000c6504401c60300e201503c0d003500c0c801c03004003a400e07103000030541c0c02d215441c0001c9922070003c46490326520902d050407a00719401c215543c0e0030000d402a403250040c58502103a1441280070000c80307240003806400c10642d20400ba000d01060503452401f50396500c01d5648498000780c0e406131102c18007450301015031090040c0514580b1940c0b60080092084055030140d9a000003000c1c6180d09105200b031414100a25096211400304034804c006800d0704171030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 542669649 1250 542668399 542668409
    0x9050105070e0f030109080a0c230c0f0d030f0f05070b04050604061d100906060510031d0312040809150d0203011514070f05210c071d01170a0c 63
    0xb00c0e0075040340c0030072124140f401890782c4240c4c101011200415180000c9030410400c0e400d140200396a24906582c003205d04904124040740526110451504041030341e2400103401c17901039003041c8022040103000340980c100a0300003030b1202d032001807103030141c0c00300c2d84c407180c80382000c0d810682903070340305040300740c0403141100e81b60031074420b020400c4103e005a044a061414070251744480300c500e169030360b403650368540550f15107850a403000e01446a10080c00b07414080c003c2210140c480c100940038006040072078403481c03103460540501e44404400c1e102070440c00c80c03504203240c40b1038035010034503008026010342c44507640070b91103203040f0020010300c10482e40e5031015850350300d0424040c0062200c19821401d01044400300d1441610210480e008683c0c0328250b400140740380c0c02c103640f13011030a5101c41403140c07940704104c4010b09130a0150880380f4440007220441034840044c1300a00114146000d038281b078044c018041d513846200018600d181060803913448070b44c0382d19020740814041e442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 542670899 1250 542669649 542669657
    0xa03120e0a080d052203030c0f0201050714031e1305061b06070c060b03162603220803070209040b092a100c050319030b12150f1003020f040905010507 66
    0x3074864a17444c10b11000d12034403002510440901d280d902d000d0640800280018110044c55000800f1603029100b035171110b58001480c2c84a20b01d400f8055039030ba511080e00721031040745145001444400032812190010300956104c40340b0b03458042805040e402082d920361444800051585a1842c108003c0340300d50210303600d482007940315090101c121024402810300079009140c1d03060740c2c00384043c0c4541c1200c2040100c0000c405c14075400c03001c45044194a00d41c140000580045d80d5030382a85a0241a00c80040b00109956110103007541c0348118180250824000800600416030180060358003495031000d54180850024020f40c3d15429044402140c45191446030356908100c600340d80007076030710b040003c116110368079003a50300d004441105804c0d00c038001d02c502001d4803030340202901c2000a42940203c02142e00c0444d2203000e480c0c0c6c01e41e003103011903001446040b05110803d0003151345000004001c3d00310340a01c1040c20800b481d45401544800c01c20001800034460544280b1490f0b40b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 542672149 1250 542670899 542670907
    0xf030309060103021e06040612091a0106090e06031c11010c05031e070c06020d0e0a12030c0804030f08070504030803100f06030e0303061c02030a0c06030b0a03120e0a080d05 76
    0x4100b109000d1903110b4419900482605c59810361288802c0780c0a40e0500e00b008803d200394002c541e8054016003500400044040c2100032204000e400f8850688180c0c1e114601141e46440403064040011901c180d0f00da4421218100508181c2c1808800e441580c50151500f003d100030b92400e5036a56041c500006100204124401c1d94900155583d020a042150041e00700100010910424494050240b41e070016040e4002002507001910081021090b81c040700554280036540701031300500440400e0030324450700c1d4407038802c025882c40b4940c544c0f10560741c40700c00d04044680b82030007800201403080400010004c80c5450020b907103d048010349000758a41000c5000d61210659405a018942400c084042c1030030003200387c2c1d074072810503199081c080c07400808240705035442046c080d41600490001c2803e111110580d40140e40d06510305100940b201828090031010314800a051400030014668200788038080041e4429002048040500c2c0c4031058103013002003081c0d0b801d000c00c00010f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 542673399 1250 542672149 542672153
    0x3040b040f05062704021b1e070b0a12060b07120f0810031b05040c0503090c0d030c0303181b03061d030306060d090501060e180105012301020f030309060103 69
    0x524007024081c140e07000c5041c86031411000807209501d26505040d2001d070410748046803619410340f030b040c80c81c01d0420f903070075120088800d85541404411403184002000e18883d04a0b00103a200101c5008008540c80c180180d2000c0304c1501401944050981e01c5000c000395110138040a032405902840b8010380002111134064400c1200e5220301c03060008440070820700000c941290300841b60040c030074045080c0f90749020a03801c400342d001786510901d0940904800c43d4401d0296104403003860131140710700c040404100040b108140024001008401c4000000f882908a8501c0500c0081e810704400c0c0c040d680c012200e07200d007442000141030054100b0510581d8061148000422031596410b8283c890002d03459110040c00b85000340710014416403242d5559200700d440642083c001c10000761140e8a02102100c01c0d29240d0a098201c843c0340d016400c18480c2d24102d0745540c4c9030b41801100b600d50f80c0701c0d10306511a40ca0541c0280c246840c80104140700030740c0314145400c041c1017a1341c194 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 542674649 1250 542673399 542673419
    0x2150403230912070e0109020a0201020d14010e09060c09130b2e03050915090a06110901030507030e071a0412050f06090307030504030201080c04030213090209090c0109030b100803040b04 82
    0x250700f0303400f0b90b8001c0004100d40407007a4a1141074400c00a00982e45a141035810b13406441b890441e0107003145002443c080011603240b80714182c0725a100c80100b640c407020710240e5100300039540885202c1040010341d510340f90030b06078448901d61780c500c00300b040001400000c0c468001c02e0702c201007071616504c03420f0092018507510b40b009002402c00300070600b88844c85581c0e07110300ca210b08202c2d00501c008920301e60760030440303e0714007944400d0030320544817011a0000503821811042d07000c0303400c4c80041034030b041c0240140e221100302900140341207440c0a45009034a18405c1100c01d42a10810004c01c0312143d81601680250041005085035991420401c0c54910010005500303a0014003803d40045c2e8008115030450340c09180900507078650145d120400e00c038a50000b54000251800b40d5241d41494100003440c40c001c61b259035190b031310719801d2511026a50740356800560300d61000d100045003010a41e030860207281d088000c150721456032501c2c550268200c0e42ea11100070908000c0c2c400d403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 542675899 1250 542674649 542674669
    0x803030a1a03070b040509100b0a030f0b09010501050d0c031b2c010f11240a050a05010503030702040f020d060e100506070b0c0d091b05120706021504032309 69
    0x100b900208200303071914100341c880c0e00941c01691721980840c40401c40b181d024454030409400449080b50b95085100c201400800074140c43c03020041c24420b1520441c60b1582e5070604032803060719501d1512701c500d82c02d00c005148407081c06050503592201c2e41010400085500410f10740740c2c40d02501d00d84861503100041e00e6051256521902483d4459a10f1b40d026240c0d0a40509605208403604000078055007001e81550b420f00e1844840c40d01d1840c041c200c9410540174805454041001da02c46400e00800e07a0f20074050740d44c06620400c01440181081d501c000ca0105100e00d0060070458144643e00607110150700864030106c584c0c0a01c01710b0241c000c024070050404176075180c6803010765951035101e00d000030305440c0d6006000c42c0d5184641c000740c21210082e03034004030504944600389045c050b4640540203240c040c2c075250240480641c00000e204003a039001c0c1e001002c0d606040380d042a40000001c2040782002101c00021840c0000600c4a10524010701c11198540c00c0240a1080c0160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 542677149 1250 542675899 542675951
    0x203070c0b062707030e0a0303090b0601081510021f02070201021513030c030e2223010b09011211030f0a0b0f12120c070305160e0c130803030a 63
    0x10544900f0101c3e5408038500f4114003001c4150103441c2c1d03031a003074150003c0440032101c00d128000c501c462010154540e000c041000c1c0708100003011034452000440364810111240f24000740030140c20b445a183c00001c100c40a8018411500d250380e000350040154807006a004080c181c000c01c8510466070103112170107041600f51040c03032445c507103074410b04c040d01041600941805100c070f4420b02070610465145240c2c95016001c2d00644040da15441c2a10307802220010b283c40ca40f07011801020b510a42401781000009450b001590070041101c03526404a0303130702418400500c079002c40380d811501610002d0b0132018401e0391030740380c41c041040d00003200808000c02a40340c01c2d48440c50b07988400b01a98101d03410f031214250421404281d034030700207000020352081140828550b02c0c81c0310001d540700c1500d22440548018214000749024403d0480c083e82010304040070002d01c48440d61806001200d18481702045e1007940d40c480c1d2401c40d8803d075003906019841d2000030300550025000005000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 542678399 1250 542677149 542677159
    0xc16030501201c0207050102070b011a2701020304050a0806010e072a03030e0114150a0f06030b01030b06040305030a1103030603070b0d0605210f0d08280203070c0b06 73
    0x24451000154103441044401c44207500f0340c1a410030600e21035810f44100ca035202c00210740d10485810040701d10a0309105548039000f03403107040c1c2489110401070306c0070052514083c4220804002140b6800c0010b20010f03070440c801444006001d54811a000c001420395001400d490750411001c40000d0b00000d0044080c4500c4914122600e048a0700001035000f020741035050a151a01d0b08501a00f40c20084422540c24000084850413108020a025942070034107071044070400c0040c020481441d201c0c0d00c4c012010700204108a500a03003003200c840c1c00514002030888414000502d0581181d0015103d550010a441c216a03800510004010490380000c43c11442c24400080d81e44409026a140850f404121f1440c0c0c1440398200c900034060007461a00c880e1400104800040280e503560003061240310015003a640c0f0101e00400740360b0075551480300c5075036400b0b0200ca40500e401d50400c03059840014505910080d48041e501035803043e0f545410f001c2c06070034100e140403400340c5054414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 542679649 1250 542678399 542678441
    0x240403080d060503120a030c0c0b1810090c050d0302030f0406081614040b0a0c0602070302030a0f0e0f060c1f0b12010b0a1a1201060c021206040b0703110c16030501 72
    0x8a811700305881400980d440d01042d9201c1205d01241d40c901018801403160f030b4030200b8803172301000105064040c41c0041d0700310b42d041c01e0403002c2c58082c0c80d0004409020180345400c144100c0c10b01940d0b01041502a0040741e01d000c1103840c068103150300c55031042000481d50014452070203403154160f0300d050900d15103c0410070346080845050b00c541d110724505100002840554140608030014001e500320008649444007800d0282d00e960100c4841c10009094074401307181c1e10700a6290001d890700c081c1101c00304401150610000b5480103035215050320446c9452510380c0100342c1c210b880c1013039204e0b001c0341c540400010301210010403440c000d00d5074144410310880307803034581c03003e000c8901c0820900c040750070012501c0140d00c0f4034810b00540031a01c8001040b2160006001c44020344241d41000c070000c907102c09940c8404003680c000b814003000c03030003107030301c0764465000840d22680e24402075107041c15502243e841c0c00c01010b021b0040d50842407027042800400e11840c1005034a0314200717428 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 542680899 1250 542679649 542679673
    0x21e0316110606130b034303050307020405060f120109021507030219080702180417030c0a030e011506110607020f030412030207180203090d09050f240403080d060503 73
    0x1c43c2d0380c0b01084c1c400381a134074182d8030790651b4200030985050749450403440310801d0301c0c50402e0b18550944115840c3c0f2038220710400758520204804000c0f80d800c24040c4d824070002d13500b0071019200240060758003c0e50381070340410b0b079542c0c0101c8944a1001c2c00c00006d200c0c82c1441440240b40d0403c2c482d04030f009040c08600b010903000b003101212010403030404464000d103440c14001c00d01960401079006404c9848002c2c46070004c00e02c940c015801000003c80382841524607603c948170403902e01850001c244a00e0034030b140030b83c020201812443000041000c0da800700900d0410b00725603005500117507426150b160035000500000f500101c0500c0584914a6150307401070b540c1c800c034802e10400e454031565003001c0c50720034406000a08400f00c081c2015101442041001c0e420542e010075135030083c804a101400e000c2c20501080700d1025012000f1041d05000700088401d0400d20100c101688810b01c142c001c0c800b600510203103201d0701815486040d840c150104403203080d0800c6009611240c40139503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 542682149 1250 542680899 542680909
    0x203040c06021609050c040b0310090f0c1d040b120c01080f06010c020105160501051003150608070603150510021617060a1e09050d030e0c06030406021e0316110606 72
    0x10913039030300744000714803526030000d03003c80761045034840710013100c012061100b24008400b10750f007140d444000a010200c0b80410080403141001c80c0c11000c41c40c1451007000e8080e60308a8400102c2c0c1c02000001c0002200020030300490400080d030800350803605140b031056800c075440b02d80089100444407403e2030090001b0f0500810366030040d0520a010507071482c19140800e401c0f4078558003074004d0005003800d910026a403251408210390142d0301c0c50a01d007940c07920744280070407074210030000c1501d0b07460110f0940050008202c0b66052030300c00e250100722511a0420604001c04550007410601c690003041c604480075034000030b00790150408030443c02c00300002d0f402e4014038035030320015000745110704c0041450b141400c00403103103040945181c1404404a1b03c10a41301407901d00307000701c0246040ea0341d03d404c00c5c40038003644004180301040100300d4907806001a1880112603040900d56000c04c42101e800031102660070845004410b400d09902c0304104010554040050445041600c0090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 542683399 1250 542682149 542682193
    0xb07030c0521041e0c03032015060109081501060e100909050c070501230c0f070f0203070b030a020c0115030f12180905040b0601080712021804020408010203040c0602 73
    0x1082d00300200c0d000c54180014000c001d000c0d0f4400d203030100e1811800346441411012a4031082c0e01060000300100d9208a200da00b006910800801034050741e5003c00b1084603000d4050728060400490724400f041d0310b20304200304440841195510500f03585003500003842650103041d250302510849203d0079150303400c9058141a10f80d0840c0108080c0e030317804090700140c003511401030110340c00c003456445080c1060200480400e1490004100f645e200d12581c48580704411449166000412400b004607007011000d15565200909880755507990b030301d0b1113030f540e0015150841c50590005100307180400903c5030305209904901012351584c034548881184a00c401d074080c21846034030004840e12403160181082c0d058441d84400015a06da0b11508001c10048038221101385501c0007288480d800782a0140c4120825503d0400211441c0d060b02c010f90403021703881110507560600211541c2d200e00107000a4580600016102d2909007410803e12215921110070740d001140804e50600c1c00d40054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 542684649 1250 542683399 542683447
    0x418060501020312060402120f090606040c09060c060207170d060e060105041e050924030604021c05100c05272b05030a020304031b1d06010c06090b07030c05 69
    0x3404459a840012078048d10a5682c480e44090a0700d081043c1b01c1004620fa50203403a240c012070f60301c2d42c2d4a50a01c4111084031041c1804924040c4080011350320a1012021441c402c050140c00c016995030380d0a01e0701c3da0307600c00017400300300441e4841d1802464440c00380104400309100d02181002000039103907226030301036064081060b80a400207101000c040c44001d110141c444401071a03d0884180b102a0040d00010311f00c0124001c00450319000410798051a0000d1503005a8614908a030803943c00c03600081b9150300403085a640300300f0062040000d00481500c1e6180d40e545140c4d000d405602802c0c44e240c503501c00c00d5901c000540c6800c0b001d900401c40203480400c40031100c4078801c00024406100418500c4000b410040d050f5000c800352040f40c1c41070f151504044082c0048120b0b403909801050b50349084d551300307030400c0d10f0b660781140c0d000441814502450286600d400c000c0c0c4031181c02c01c1e60384003c20024090401d506110b0403203030324150301c1c015040c00d042d078054020010101e648 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 542685899 1250 542684649 542684677
    0xe0a1b2108280905030106030c09050403020a0b0708070f170406150308161712190e03030f0f0702010903090302040c021f0f05011409061915030204180605010203 71
    0x34042011040494008480b18040c4035011515003008109200074079030120002401a9400245420140502010340e1b52014030308072018140041e040003020010029011413240121000110390405100c0e4010f500ca5545c9944602e05800050100f4003480c2c060410095140080b4031002c40b400703500c1e50460340c403da011868229001c000141c0d410305130009480c0c140000307022203881e043c49101e1881603111ba11924004041100b1500840c003034002d0310050241102c000608003402007410080c145041030000900d202c078040f01c1440d5400448034200300324000b6040c0f0038003020301004140d011505200070b000e034a0704d0340d0300140b6030305007480028002c5880d15400343e081c80c02404106e405101481440c00b10b540e0040b50040504903105507008024500400482d590384580150903803940701400c100415110002072000a40c0c2d1115141d0000d0520480401c040710f0901c0c003442c2d182959580962501e042a4152800030b00b030001d20b0147c1440c00340100010f90300803003a15507480842c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 542687149 1250 542685899 542685959
    0x309050319031d0613090221061c06090f030f020c030712170d1503030e100c020f010909020f0d1a090f0a09060906022106151c0e0a1b 59
    0x1042690090b072100c85640810104042090241b9034041c00d44980012007032004080010b00d9903852102c1078500541126882c11004691101c00c4910707070b2814804d4900062604654403a00c030641a11a0201d00190ba920321003036400c0c0d81001802140744d0114064078a03a840d0054031118100982c1005140001343c04118400c4210a01541e00c80c004240b0140407421304c210010380c0b1881c2c6408120049080c0640c1f40905080642d001c2807160416103400340300020a80800c80c08040c495045810010811f00205d105a1a03001902c40305030700d0aa000c0d01c808500f102e01c070599451424000100203040d0b43c20341d150391481022900a2018016003150b502c40c4500c660181c21001401790030982455180b0301003088582c000e02e209101c5e56084c40031401400b840c08042c0f0700544505500000d0310941000403043c6100070103481c80c200404000e03074070050302c011058942541b10356440390090f1036032406020400380035444181c00507403072144080c20400d11280d042140c2c00610000c2022507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 542688399 1250 542687149 542687207
    0x1030201031d52080d0903030509040b0315180a1136010e010501050a0903030302090112050109060609080303070801090c12090b100b0403030503060922030905031903 73
    0x2039140c060402e150038018801041c0c48504015592507036600d510390010f081c40c0091000008071310501590000c0c1d81e4030041500d1500e08481c180c01000741590b110b82c0d110a40e000741d0707500b04015074000d1b4420407010032614110046003041c51504041d00c3e06034201d41140c400054205101404a01084884c510019031180d0f040701c41b00b91103407107052059038181450b90b0041280c0310a90407a0200e045858285e070329003004441c1383c059544c2400108590380310a0000034020f8001e8202d412042c549070360780344c03200c0052000f6120700383d02562681c0c0c0e5681c07040c04540e611852030406805c01d0710082d455410500d200400b03c0320144a01c8243d9951480c04004681c454995400c030004010018410542e0303034180401491001d0f40e203150801c8440100240d9840240140c60480c8d40603151242550744d26424000300390390040c180c90315540420149400c40040c003503e445002e0081c0ea41c12591824902814540240c500c8440469503e0324141800030703501030501e00528120421118542c5980 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 542689649 1250 542688399 542688463
    0x2120a050a0501020304110d0b19020f07060f0f02030f0a0f020d0c1d1507081317070f0603060b07080912010e0d1205010e13050309040c050301030201031d 68
    0x1180006003103001d10380105041c420150044c6015074011604030101d0001e0504004912104500050058401c0400140d201c2c6000d1032100300b08100e26400362030440110f9810002d944030a1007101c416541c0c064940952200740315440c0603000e80c4604506d581003414001c4040030300240301e4506030752110a840700307448168068030984c0250310024003140208260141c070002c803180703003100903050015081c1e81c41d240050302c00e0141c888103003805141942c0c68886440c20360084d100c40c60442496600024002074a28182d443d5040410150038075906114040b12180c04c41c1e4010300815082090610002c500b10040351101030b48090102d64804000c0c010130304100d42000c0344503085d460f000e40f600c2c0090700820007908001d01aa5041401c51020002004a4000b8001c40c070513010102d0010f506584000d100c0d5210300c0c000c4003243d041135804800078040d600750b085c0f201e0029102100400031940c050140b130410012a040c5148061110514181d071190f00300031800e1041202140c01119600c1c2e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 542690899 1250 542689649 542689663
    0x50f01030212120d020316140a2d0306230f01030f18061a01051c150306150501110c01080a0b060c06010e0411011106060f0a0e0f07030c090e01030212 66
    0x243e006916150f140101c8040000d420850b85d14402c0101c00c101070100c00d1141c2c110701c240c241407540c154104802a9402c6400710710304603001d0842c406032220441c0034007c500200881c844c20f550041003c0b810121442006545a1014042440800100303038080d61400c0c402070f43c0714800c3c600010141c80040040300a0107060102402e50029400386400f888841d4100c1041d03140160441c3d0740281040e801100c01e0b10884070700c40e4207000e600c109000400d40607007040903e401001c542513070994480e2110012a070800c041011011035100c01003000d540c000d8401c1c40002130240c080c1c00c0f40040300c0d00203400c90b4001000c980609135280780701e5105581f0901651003061400c02250340c15a11040901c3d000101618240c401c0040f441c04a4190342c03044902c03103c034258603005070660303840d0f0b0010f024581498000c01c0d90300151041c13020801007688a5001c0c42003010300031403101c2c1d0500100141c212243d03030400c003080008042c4140321214144407102d0441c1d5064626142c403071701c003104503402c1c591 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 542692149 1250 542690899 542690923
    0x3030f1704110301050705131502030712030e01050c120a051b13140405060d08030601030f050403180501090f1202030715051e07170a021e0f060a050f01030212 70
    0xd808418407050240680165408000541c02040540c44010f401c1d5200d0288039034554201c03440050500820a000540c030020410300d00440b8105461551101108030702189254002a52410141c0c5079081c00d0242d25000210f5035500c40ca0900c016000101404005080c00005a1030b0808240f00504140c5103800c1059050002d9480703107201c081c0001d8064880c451008001c1d01c1d803c4c2031440d854184a000d001c1c10b00144a0b03161107509075941b5002b50001061309040c036a90385281e8030003006130b004080c4154401e07518041014070b040b01d20451200309400c494108101ca01d410302c0079040040300602501c00c80000423000b603903503200092501c1ca664210401401e040d4820005043d00040503280021050310b07040015500008004214002c01001402480e0500e103072000040c4000002d00b0b400b083c0784190707140c3c140084039100c0045c885840c6554540d00c04408030a00860500109800c004a25418015410300d1000408042c0701030102a100c0c118100c5021941d0004010341c565444d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 542693399 1250 542692149 542692187
    0xb0304020d1b080f01020d0e0c030a0b193803030306041107080a02030a0f020a08090103020a12140105210606060a090f0b0301060306050108091e010b0a260a0c03030f 73
    0x6074244130203010390458880b014005003000e401210004000c541d600103000c014000704003030710068a41e0351035801c0c0640010408001c00c81200043c0c00c1a006007038400c82c1c0b004c000c071080d50710800c44c40c095070380580c0c0a504001c030f51081c14809942c0030040380e40115089401148010a105001d00386100d040c1004055034400500030116035004409811290b22580341d80c45a1030304110142d0b160501500e000b400d295081204100a600075030180c00404101d10b0280822180c11646808139100c0800c1100d000740312400401007460130041c032546c120178181c030700c2550182c1c24401d00d994640151819110b480c010904104031032150f07110100404504201d4010705d03568141d5090f00303034400c0c040c0b54002400d0802c0800c0d2540648803950050180b040202894611417002041d038141d801c0380c480c020b5403a00b105410a5462440280150650215242c00060211889041e94018070110500b940082e407800c00420380d20851201220741504050f024000307020421034254181046000b030300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 542694649 1250 542693399 542693413
    0x130509030c0f0a020f1915090512010e0d2d0e0a0303080103120527220b091003150b03010225030807090b070f0602070f0f0c0b0304020d1b08 62
    0x460000b0fa2644514002c1c4ca8010841800b40d060100355441e08503060640300400104010720b240b00b42c801003485242d03140c4248810349420000b01c2c071000c1c21800580580d1070350b4004154242c10300a04401c0301250411560b121002c0d0716140b411a51040c2400624160b261900c890342c2c094041807000d40f90080a00c0321860301d9140c080e00220081c00242c035a0004040404c032024000d074201c0b0360181200448000c5c92004460301007049454410b003542219801041c0010a614202500310000420301c1c0812941d01c0003040c000d0302da10051070100c3c050103a01003000030410352150300d04080d0340301d580030030003032000400310740640b0402c08801e1403902800c1000c400d04102d45000183c1c01c0c400d0351800c1c19070b2182d15080706d80304110300518420807010428103001601040c4458a80c6120301000b50070034900340c6035015820100e0800b03540c50a0300045050421200c41074000282a0050b100740c1541041d40104103014007100c4014500000c4001d042d1140c032114420784000c20006003100c0700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 542695899 1250 542694649 542694673
    0x405010b0a08010806040b06040c020f0f070602210a120e06100501030b0a0e01120f0c062613060b0402090307090f1d10020717030109020405010906020c130509030c 72
    0x145901c040320010000d40444000301350300c100818068040c2da04280070720450b03201c1e04200001800119141c8003548180152070300c0a02050100d840c41c041c810b000b03020010f2038a407019003081b0082800c04290305841c0c000d241118442e0042d200220260701d0300312024107090200c04001c1c040b00c0d14040342d51088a04014001840003c0702056440a81c1c090140e400309e90103100441e01c0c507008003010220010018020070030304100060042d4020100d80d084561241c94900c203094498206500003895a0300b041c410a1040741c0d40c08184030000c02d282c83d50300d800d030240291000c0901c030090075681c84290403c02c0d99a581c06030794504030001c041d1036a0340d5440108000500580b560100981d0401180c000c40180c00e00044c2c4c4910100406001001d8203200801d00941c0403110071140420000b000170540722a44002d10f021780003802c00165a182072800240c8206181d5100e04119400303c0740d69940f0751a0b4101400c2c0d411440702c400708140d1101080d039800c502071941141c980748a000c0441d09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 542697149 1250 542695899 542695919
    0xc070f150c0510050702120304111005071a0a0605040c02060a0605030c090a1119091a1801110c0618040b12120a0c020d12081014010e040209040501 65
    0x440c0c540105148103010100801d803082141c40e40c02410395000384500001140594124a9001d84a4415070714940c15a040c0d642c165002642c06440004a101100c0643c0c2056001c41d00d00c00480e051850030b041d05650b40214400c000100c20300d08800d800013058211605401c04400340c030005006000560200308021741d919821611194820b0a080c000a4681804101840301920161000c901c07581c450080d6409031071038106005156504100c10144902005112502e07512281d03114003820b441d0603020560740582c2c10903644910b100304000c0c80031203c1c000b880118607500f07007040780c9c1681d6007a002d00d00f8041403142c0c1039000f960024081c40038001d94616854040d408903420018855800305010080503104000c0e88568800d451001801c014207018000f42d608030724141c00c60b8406980819510302c040a802c507110307001e0b60b0400c0d2000390084806688615150a00d01625190481034980600000307103c0d41800551101c00209443da50100d4580d03040140042c4003a5070340e64480f030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 542698399 1250 542697149 542697179
    0xf0301171e0705090c070507030515090304060903030e01120e0a05010f0c4404050606030105070e0d320d02070b03010905093c161a0c07 60
    0xe011030280070006050a1000c108401e03452406100030180c10341410180024004050120902e0328018448040010340402070389000d584504068410307444039010300203100d4805025800c2c10740081c0828400f069100001d1804c503905454481c81040100d00180c85040c170b101205c13031000e401e00d29a19003491000900e0f40303005101d01e008003c04201b50401404982c000c14422000640c0c3c0c0d480302c010f912440c0d1400b0060040104130a0000908503003044480b58100000240074100304100001e002050282030352008040c3d009000601d41120010030101c000d00400c0d1040e480540d2101c10700071030300c0402034120801d075010142c002d5845034145001880300320300c084611070403e40719036180c030118a4408840a4607089400c40c0d00307008aa20141200820000fa0340c4144e16250f000c003200100f08103000c4d40c01c1e2110050a2000310441a092040c5a91000440d0701518142c503081a448040300c040721070280700d5029001d41204200d40901c1540000d80003880352110200b00200552000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 542699649 1250 542698399 542698439
    0x180d061d0105101e08010c180b07020a09050702030408012408120702040207030509100e13020418090c0503030423010c020d0f020303130e01050411030c041502030f0301 74
    0x91030031030000000e802e07030340c00f1903a865224072a03070000c04c001c129200d4441e400100300c10922034095103030a1501d0031101d41703030b00e5040000e2160354010072000d9104041c0010b048161401860710a46401003441603546218104145035640d0024012500c2032081c0c0b400741071260002d0040020000740c070041074651050188a8540031280090b0910300085d6506007181c01ca407030030782860556001c0200a410224055050000400c081c2110380d4880311801c06400b441c3d1145034000b4212410301244800c204400c030849031040000b40310b0313160402c010100c0404148000300c0e645000c0e10f8000c91344001a44150b806200200d0081900c1c42448108600d052100c80a07448032800075004480740c03100c0c03c1e006500a400c1d11140000f26400e014030580303d07400074041764035000c0e0048840044552980c41900c02c95421401406249001d001d40081c0d104140d174820701b9410942040e031503d100d00d109000c0c1d103d0410050859450090040e584400300c080501c1da204d6a44d07080b0000342d11600845 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 542700899 1250 542699649 542699681
    0xc06060f090c0306010315090f06051c060207051e2506080609041a01120203060105030d0e091e0f060f0a08030f0a11030f0a0207060c0209040206180d06 67
    0x148090419036031261400c40010004141d03510b0b8944588565070025010718105a00c91840700790100080c401ca0000700615600024001c1c001c19100b0122030494220600c07800111011800d03884d006e8000c032500d40c1e00080c0050f42c1e4003152810a24100381c0c0b107034104101030401c403a50100c4401140c0100784c01b820a052a100e07000300007041098160f5401600081164400402c03028100940c840da4071038030507090042000b10080080001304001d0784848400d8203800d0340c0101b1410244030082c01404160f00070a26031800004c0644280069068075006148682c0019103040c41d6088800c07080c030101344510060b08155000706101d02046520900400d080d501481090804143c4071040311200c8001c0c1d400e00d0701a0361940e00780d600c800c04203020003402d42c1c1e40303000190090000f0032201103603c120650380e1100c20740c00ba080961039885070040c0181d0458440141c2c0301d004146a0240c0e04998040d80d8403112145124800100140d4540154558254004018242d0f00640413141c40360780e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 542702149 1250 542700899 542700901
    0x5091302030103080a0c050c12060a06061d012615040605030a021305090a140604170307020a3c0b0603010b13090809091f170a0213110a050c06 63
    0x2400268442032100820141c1c0030020105c0462140c07511a203400c0c45102035800100301080001d84c2c207a40501c0766206a0017820501c81403a6680c45002c00078422400c042c00d01d55511b0316a402e4541151070003a061040107084132422a80ea00608540c1e42545201e200b100d0820a50b100401c68400b5490b0b80a5032a2210210f220f00e8001044140c590f0b00409625424038407040c40d4000d484081c040441707510500841c00c00040056082d1411001100c00030083e600c0e10b8140b2802c400707902c3c42c50249081040080c007600a03400705d809600142c100303080140120620502090544004850007180030011020110610301e610386241483e00030300c1901c3c83d580b039104c20103007228081d140140e481850344120303406201c00340c2c0254079210700035000c150a00d08604040b4004180071900a0369600c00400b060500d5001200d50304040c016510ba5045203401070087c0030390b20f95100f003000e0302c180c3c510305581c9803c82a03a080042c02c4642103000750b0301c1e42860403010b0144e8102d01051995401104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 542703399 1250 542702149 542702179
    0xd080603011a1c06021b031c0e120a020705060406120f0204141201060302030102190311070b010b16050712031d03060106050711030613030e191505090307060509 71
    0x8040c2410380000510f140454a200800307000268420503045910320b40034040b41007950a043d204408180004000e96940d00c2c0070341c084013800a014051040d02803501d4a08110383e6800920b000c00c00080032401780d41d5000f0b80500382d00d0320031320303501c07242d80114001004079400b540900344940109030544240599580d0750510030680c002d5005d441c0c2c02c5254911840c40381c5c9010841031000715455800010855103d801080c2a40e200150402c95481c1c45c0311030408955242c4a5840ca00c0e48400b0068105110f0703641d42500c043c410311940004010204501840400c4202886c000c0c2e5403280c100c903040703540c0f1440796114000c01030060f00419071325160b003134646610707a0403042da0a0f0300402511040e800c06a0a40d0709070090b03c0c050b1800c1004c0700c0c81d084142c0b0100903030307402060000c00c0c200c407000003494014045411121b1540c094604040301c45907214043c1c199000303581469102e940108d00c4050102d599009941d2100e50512591800003075030340d00300c0000d001201c400c0d14681c0d902c2c7d60b21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 542704649 1250 542703399 542703431
    0x31e09010f02010615030f11040e01150309120509010216060305091002040305030909190e010605101b030807110129030f060a0b010c0b09060105030c03010c02070e040309080d08060301 81
    0x3d845401d1280300c66010a03005c1d45e219610000040e0281c400c0064285c00b0590b12a40d56001908614030101941005110f00a0f90b044003c400c0811850309000088842c1c0c0e0784601c4140110b1540c0c1401808545d050142c0e0007400382c81c0070795005040c01c2940646c5c41d04000c019090650300030496011307035182d0525002e424004c941c140c035080380045181050550600c07490700c40050000484078540580b802503050329026040050300a0400800c15030308160400486c589142405401e20050248501444400592054400360103003040b10040c1d560960580c0c801001c001c0c0c00d43c0769407800d1040042c0e048204124001d014041002d10012000e64061680d18110000c0034203a82d0300c164001000800140c01040b80321506142c1803d954529542c2e4220700c0320180c03480c00040c4c01c4040140010b0408010b46507a045046000748010030b5680b0005e5194085030041400d0040c10100080a16005900e40c1008201600c100c0d0700d000000d500c003c201c0e460650303103c1e119500700b030f030158004620 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 542705899 1250 542704649 542704661
    0x61d0a0809120102130b0d0b01030204030317150d0803150904030207140d020a081f05060d020f0d0503070302060415090305250c0906170a050705060c031e09010f0201 73
    0x2200320641c0c07900071001d0030061400d505081c5003480f59002c020101c04c054407480c0300c1c0010920071441d640c81e0341c81c42d034640c0d003640c0c4079140a0b4101441404100007291b07000848103440ca503416901c60064071040c11400080384007220311500b024255070640100081c14009510414045a00740f020b41ca0000400002c11010344002c0c0045e40a61424052040f1303400300c0c8444080010458031055000e503010801c021000d5000d49042e80026081c200c00c100121602c1c822180b040604000030b2510400055942111103070107801519504440c004588814800344103d170380043c200c07a10b41d926441d00940d07032031084400300c55213040c1c210170115103581c50003488010365042d00c2e41d0b4184401000c0fa00480685010074a940c100d11181c0d10011400410248000c3c000b050008510300d03041194204001210341c03210002a400f81c04018003046000c9100030540b80100c9419954003111013805145001d0404000d01c00780800b03c6180b8900c1d205801403001d4042a00d6501d40c01180c050182d00701d030707a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 542707149 1250 542705899 542705903
    0xc010e012a02010b032409010c02120a02030d150611030c03160f02040f0f11090d1209180906050708040b04020603100f08010f1b1d1804061d0a 63
    0x1a60304010001c000c0d82111420050362000103464081100041d140c0020311a0354520948080354510529460b40e0045034000700341d5009200d0070300584002541c42c003a18480c145d100002003603402002e8401e208541c045041810180207502c04201c0c05002c80040b0f02c5a000443e01501e13894141c001c0c0401940e80001d582c001450401135010940480314600513000c40c0c0d0307809010000e80050f030740e42c8201301550b41c0c0c2d07000000b02c1d0740d1004840002c0345c007445411000d001c0c06006248150307035680003012201e6407040408215100147c8103552000b402c0d04000b500038244980e07408415215480b4402c1c082c05032805114a0702c0d54042500c80b101c05850141c51140014001409400d00a0082d50814282803d404034a5a15400e40f0040030380c640040c00f10365117a0000810003c898010b44404400c1d282011004410000000c4c064120381c0751a1254500c001e00d034041c0503980d000c4034007452910441008407505c2c15207458001060581390262401e07805581008181100044c00142c041d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 542708399 1250 542707149 542707181
    0x1030b0109032d0f0b0103060c1407060b2704051e060a2a0804120921021c060209120f03090d02030106121a0a0c0503130314040b0c010e01 61
    0x100f486000c40000d41100541040290100d025240021900103008660b54010100310300954194541402541d580c003035200308001e00c007006e00c00c1d42d034200b1040302c3d1a00d40c40307100001e80310321902c007081d030071844c901e6214810152444070104982881c00c01c0303442941719034242c548030151007840000c41048400480c409922500000d1840c81700d41e4400707105201d2140301c00240148182039580d1031900c84500c200010242c006000c10080f1404016401d00c2a0342800e580d40d07402c1141c12900701200c100e080164910940349042551a01141c0140311040c80c0c42d0300c5030305d02041c03c0450196104007860b5014034025100358240031404508000c080704081c000d03524005141080205490007903900780d9055503910360000740c110001d009190058814141172070940820181d1011070000184030554950a103040051202d030301c4003c0300c0d8440e400c94444603041142d41000c4401001d420328100181000280202c2c007000030502034410300070301a0090010301c0700004520b090701c030305040c0b0008003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 542709649 1250 542708399 542708423
    0x12050709060906052128091214090301060308090907020a0c091112070c14060105031e1614031002040506040902070f0501060b03040218070f182301030b010903 70
    0x40e4818001402c040000c005030110300c850740c01d00d0303003091350b415078000c1c519100329052105944405140002007000c02e403002c0007c00701a403150b134030a2a4a401c80c804102c58040c00000442021081d200c802001070000c11180780c482c0303080c080d60b6100c82c06035842102484000303124244005201d006042d40132514410b80c61420140030058011100030070301074041882403100c3d40501030070035403048180d903031075890040203410000f402842401070804690403c100522140d00c00148440046150011101400390307100d00d1b40d4104a071042160558480d032003000204070809600d10302c2002c804900b81e40061507181400c40c00c034881c910509400c890b00344800c10840d135803035003d803581c2c0340140000380c103e40d0569119821a0425048101c1000d0080700b84002d40c10140f601d903070302c4500b00c0102c0c000c42c20607450140500b42100c0c100c00400c02c2c011001c86480e000c40100324010003210f0790f0540d504012507044480c4a00080c00e59000030300c0c10310880050740c0f007241000201d030b400402079014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 542710899 1250 542709649 542709659
    0x15020a120e06131104111204060b2403070c02030109031805040c080c070602130e0a0f020a02340b2101060c060b010203121305060a0b1c0c0312120507090609 69
    0x20713203840000d80c001d9446000301c01030215030300100003404050b855100780d89000d10303201c4e04540250b82030b2405100c114200ba160645400303444c0d0341c00198107514685a548032501243d21b007186480082d0954200303400142013581008001080080b02c10701c807207110780c0310720911044a41540307820b00090446000b25205110842c018000701d4004d03840989040320180b0280b800301d02c0c661060680c080c4c404c00300460303224103108010021310001425894083c6090000b580c03507400700c02c105048440c8071200d9101124041e408040c1d0b07200811040542641d45410056541020509406e010f5100c13401629603008548101e05076034441c2c50700484d44515844070f400030100c07000d0703840c1548401c01020315000d0703241d03028a00c280380000806085100520305142010320140001c000107040100c00c1d00d15a581501400000c8080c000c01c200d5240c0034100384044c0f00513644007410744e116505401640c10f070301580014800440714000c0c0125200c01608490340306041c8603040c00074140c0d440503c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 542712149 1250 542710899 542710913
    0x61305010305060d0f031d030c0609090a14090a050f0319050f0d0f2a020601090209030118050f1c080402150c2b03150e0415020a120e0613 61
    0x7800034400340c29110f0495059481c0401708a4600003507003c80e40f41d8a003c05c1c0403507040030280403160158013416042480300045035460241c41105885444044009000d02c070003540561140f040605030705505013000f0200350744800104801b603526008440c10a5800384c000002c071031852040000f062043c808600d42107441d50032070074105210007010403200c44562513601a000a040200100260601883e9103600402030001e52421110f5500840148041d8000c140181140c41d1184050381e5220080b0003e4010031220400d01e100003410300d40d41c0305003e0300190321040c07240d26100322804031005084581440c0042002c00000075010f40000c0c0041c203005caa014200e10a449000c0e0500805070b074458204647d08650001d91024484420449042c4800d64404030045040401071220410040c0c1e000c51001d0003072680340661280441c2c00c02102001500512076000411502c1d0500918018582510280380c0c0074400c0c1020461100001e001c40d180703000e40345a21500a01e030700590b458070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 542713399 1250 542712149 542712151
    0x30108160e0637170609070e0a110301090603020a050d080306060706020405030d0c03091a19091a04050307210f05120a0503091903050a180314100b061305010305 71
    0x903006000300c4043c407220340c40c0c161100803203008607400c0ca0002e8140600c4113a007007180c01c10342c0c0040c0d11040c24051500d001051990580c1c2a14100640e1075403040e2540d0060000a406400c10200010000824020383d038089019a0700c00c036071002000d561041000900c0c0741c0045e000d07100380c00400c040342c07072807500c41e0040113a00c0c072030000903040c5a0307030390b0002e810070524a0040d004600d81d260880d040591045c05071002c1c007541d2030b05410f0500c250401c030b1518021201c100e00000600320b00c005030240522450402410100361460043d1241000e04100350414800d2034003074450098045850740f00d00e680c0000001c84140c542c0181c0e841c50720340d0440f080c140802550755026041e030183d05844280c0c020b041012058407002d9882c2070054402d441c120728030114003804410355981500003680702c1c084980f08081c0d4604030500030b41c2c0c20b001485040c21a40014001103c16840c1101c0d1500071030a800c00138000b00c0100300c0c0e030400c10141302d103501c1504401124445d441c0c40a01c0a1341c0070754046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 542714649 1250 542713399 542713429
    0x10f0902011d0a050915150309330709060f050a17150303191b03050702090901020d0203101424071a070314070c0305030106030e0c15030108160e06 65
    0x3000c1c041380e0307a0f000700b5004041954060b11002268690110506001801d600031414031410170f451032a103000d0464542c2048000d52210703a004051075145e0490b841840102240c01d088e240c80030307040c050000f0b03144501e1849442c0102e80c1d02c580201c0e84501a40503141301161310b4442461004100d45060046400207181e20065805200c94900680f002c2000c3d000c0701c203003111050070b85800920081d04e03209150300c10160300c3c054a9009000641e00c40141c0e04079550507500e01040b506e6964500c2e001e405503280c0c1e540e6483c4040100704000003200e15240c11a480c041000e8004e150300000d2007107400c03c10840c40503c1070700308044d0600070074a00090500502482c004020500382c0942d111021105403001000251900c0350031000068600e01603401071f54500b041c02c0c600c42c8564015005000504c90f6609050340c07400521b241c110280700b04442c2c42001040400810380200e9414002e42082c01140d500f0300c1003100c1c4021403000391014205450300000007030005d51f40c6d00100b000b100d12030802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 542715899 1250 542714649 542714659
    0x9020304060f060b0d06080601122405090309010f0201150506130905040f0b1e07181d040b011406180f1302120705090f0d140a060608010f0902011d 65
    0x2c0e14024280c50f00c201006030540e0380e03000d661907019103000c0f002c1e560030f40c001d6403d80e080200104042c2200401240c0110b80c4410030180e056030b140135142d901421404140d10050030001080b19000c008130042c25000c0c000d0701c40c081082c850601c120701301c0e00c03501040c00568581c800c040c041441d10a0151070b1007404020401e840503210340c20a810b03981c003910121070042031810860f041207288031240354814423140f026104482c003000da0b0061000040d1022042c4900b00c5810844c05c1403903000d20307000d041c0e14049949402c1540307403010410300c801c0304c003078808a50305000171034207482800300d00c05180c07002400581041c1602080d01d0320308102001caa45e100d00e0101c2141c3c043c0d11010204440764516190050b11020003900b000d850038001030000c2d003005001c00440040c0c0e6113820b40905802800d681183c6a89164600180b85894104030000785102d8407507401e0412a03507030001c1040d01e030201c000340721010702a241c0c06c2c2600c038501e500a01241c0c4542800c40408040400000100e2001708 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 542717149 1250 542715899 542715911
    0xf0f041b091802070803040f050102040e01031505150d03030e031207110c090618040f170a0e031212070306050d03030b030d18060e060c062d040c0902030406 69
    0x4a2880d8014203800a4004500d4200080002c05507100c0c075103268628061056180c410b1039038621209100c0148001c05209041152006100f000d606560245c460300d512903059503101d0501403a4582c04001c07031218070b4203150014160910f000e010001000c3c4c05000c002c0340c05040d541c180d000c0c4c04500504841c510040c403010340e02e54500c0e001103006000d1078a400c0da030402c01c40c408906101001409a000d00b188205012098558440d83d0040650303903c441422a100c03407500d030341000c95492015040b2422103804000000304000140034040e0f207501e58082c0e03d140c110915469005106000c5e8681e00140580000b01e4402111036a0090251600080309902c40001a8030101c40100540000351750b014000d080381020007000560386654108441c3d48120910600ba14440314007c420070040c1d072590810040c0c075042e0075030b404803000344195940d40ca0f20100c00c00c41e44600424880044442c00780d024074140120b50168003c036040b40c420480c4608050400010b9840904102e40256440c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 542718399 1250 542717149 542717171
    0x2030a031e240e0603120711041a1305040f06052e0f270c1205011202010e0612070c02060f071b05010e0a180b1002030c010c0e0f0f04 59
    0x312900c031001c0100108000702c90b0034000a0a080c04058100b070a41641207070600540f690006840c41b501200948007583c0c4120340d2810725440c011800b840c3d0f8205041210b402c642c80e82840340b4203644a82984e02d8447c040988103c0015030b40309480240402a008003240c000c590380d40c0115500004445610001e61002401b0072070141001e00302002c5042501000d01c900302c440350b0544002c00010456500745955080241c114001020304c4e48601903540c013807201058080c00d407040f5881500c403c10070956a40d09840076411070300742d5049001600c178800ba0085450a0f505a4580003144c801c0a0482e580b0810300340d40c0c800740d200090303a0000702400341c010200000b000520382c10740302e4000c80c01020030b00304801d900049141c028070305100044075500080e488240c08541150710040140d0701046030480818018041c91041f603411440108010611540000c000d01404100c10020001c1840c0901e08642000131070208a130320a4050581c00c01c81d1a16a004034460744009100189100c006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 542719649 1250 542718399 542718401
    0x5090a0f0302030304030e0f010807110c0303160204050a0203040c140319050307020102010e060601021b13020a02060916180e151e0112080f03040c050d0f2102030a031e 74
    0x5110308500607840003080004150303106044a9001f1425a040d0403001401000a40046802489a0204000d0a039400038031401000303d240c008401074156580c07018013405200320003040040030390080c0c0c10440880e04500303152084078441c581210350840c900d4104608946124a8241c10580c1441021401e24691041e440354083e054890030056590780224400a82035a010b003201d522160094030412049980100310320411500c01c420440d4046042360008d01c00111071b80e0703124050381c400700340200d8854001495500540390f11044034990503000604c590808124080e50842118403a0944203000054002591484245090311031009602030b46a00c1d505003158070320b0110703055205014110b08000300e0310b8054810140b4144901c9805e84680740203204100c0f00881c0079200100040c02d1041c00c1c83c3c4a0050103001304041301c650801d0810180b08418250299000d08003002c581844050206000213800300d1500034509140d822082a002400002002403102451a00701c030640b04907 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 542720899 1250 542719649 542719673
    0x15070c03030e1915140601030b0102250e090a1e0302150907050112020f070f0515040303050f06010c120e010903021906031811060306040e01180327030605090a 70
    0x283d06105030303180d095810400300020f1412141c01400c1d207820007049100032455400341c0e1014085c203002c9004510440100d2a048000f00d5841c01c8102c40c840d0004660206006d080443e480104078840076260065025107038030318640000c00c151504441d03002c002c081404000c00d660f000380184d60841c4408550795080f1481140c2e482c0940e088403800340080e60b004110b44120342c42c8a50114104541954050000d21641d4005011407003001e00b04410420300300052501001184e01c040024100f0345005030181c2030641d03c441003141607400041c041c2d48200e4500752080d82088545107020110102a0346410448484c0d50420102c03020220141e01d0302403114800004804401c0c41c614901180102104c40088400311007026150f1074001182e000744401c1460f010480b803190352510b070100068000c2c800d007240c020240d420440c40000000c0404414001039003e40c840c0c0c21410801301c3c080b05202c144400250350b01d40010810310106506a20160340711189c1c2c1e0888404a040e500c4200310400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 542722149 1250 542720899 542720923
    0x60103050721060f06090311060f0c0322150f110705041109040c0302070213050c090a0905041202060712020708040506161e0f03120b150d0e15070c03030e 68
    0x184451041004602c01e454200090002c4d00c6e20081c001e0455583d40442d00e06140c0340d61282d003002c1014014172042004a4600d041745000f16540c4824928100b4112030902021101010042400007895000d2450823048604940c2d15803002002182c001d44001120240c004101c3c400c1620105540c2c0381c500c100301940c4440c4614a445a912004100580300c450302e5110402d07005011000050320b9548400048000c283e20100b181da0303c0e240c04000da0b0044118480d40080340d5800043c40f003800341e208034040c0d8024a0115110228900c040e0303900d00040d40c0d1000000c4060403042c2101e0f245034040c1060754411912103103400d03034420004600750041c6005c4281206441d03056010450030684a140d01d03d9000b10498a080d0349440703020310020101000750030f00c101d1342c0c00c010100160303611480080d08003c1608090705500241858107800901d03540900704c2c5410b1400010020000310405005111070000f9a5a070325000229030514642100328145904c0f0f03175095540e68410b10052290710 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 542723399 1250 542722149 542722151
    0x70515070c210b090102070b040c05030c18150d02210609150c0f0c0d11010c030203011505161703071b050a080f040e010902070c150206060103050721 66
    0xc0581407120080c9000d07801206400030141c01044240b0845103000411600000d032403403030342d032a0b83c401030181c0b140d10001442100c0c0f510801c01000407141101041e22000c0d41210b02d82150713031701481030b10080e81501d4016008120300140c0c40b244005a502c6044001400300e00800c00c86a0202d4840103101e101d000d076841c0030022000486004005080d804482a00200b001c842c51001001c002031014000c011140400116600790b491444110303280c5071034500841d02400c0007481c0003000c03440f148007400555402c180034a071015120b4025281030711314401c9854050304200c00240c4050384405030764400b81401070480d1003c21041009000082c6040722181c1c0d0302d14100e04000e02454800da04501d485002c200035038045540094119883c42d80b006490399150100c20410f50b103402a540000011102c240c00442c0f00e2a03075030058441e02d071003500091483d0762030b82500e5500d4401d10050800503400600040ea4a40c441e401054000b0300a0030074910845145a90984180c403c800e01c0d1045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 542724649 1250 542723399 542723407
    0x510050a0b0d08031f0b120a0f020c0303010509061c0c0f091e0b06090a09091104020a0c030309030306030f030221030603073308090c04060513020705070515 69
    0x46154050764121007000c440c0203012140035954500b56010140a00924250385001d8a24010721003280001801c0d104a1142c1c40d0100700204070003040044455088850a2502e0980582018029140c9482c22480a03600316800c01040c00041c980083c00d40e54000001000d807084219805140b220b014010207060801038100413041107078151952000a105182030910b03a2403001c02c0014001840c200c0c0004140c001d40200081c280740139a581f0554004a032480c00600007845030300208681d4411031a110b61303070400c801040124020030640d500419444104540000e2017a42b01541d01442402e002609944076100d40052003602a001c9000d60b1002c2140b140c40e20307034040f116660340707440141d2514524104002c80d403240000e114030700360405a84020b891106001039400c1c1070f00b101c0340c1e616080404103d0005c04840054842040900a10b500140b00f03060501130442590000741442c0302400c5183c0a42000390700410f001d031454092000003241c3e03a920900002484c11112030b1054607 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 542725899 1250 542724649 542724661
    0x18080c0a081908010618090507020a17090f150715020c01050a0501170601060e01050912010507020109140c09040213090f03050306120106030c090507021e03070b060603190506010507051005 83
    0xf030020103820100c00d00c5041400c1004011400300b0f100d06a610058021a840e01e802c0004d03403034001a0500140780000002d4071040f490360b8080540103010b030468850840c2001d4405020400004100a40ca0208100302c40b402007120312826000540b41c406c0018545001001c070b00b400c480064034000f00c20340d02d8000400c00028101220034001c1900009000c0c01e52426002501d004440030501d4140b2030007052460059403445040321000d10715100034482443c0011009000b071680d00011103e01c1c0074603507922170041c800240050301003406440a01c558039542c0030040d06004440286810b5602c900f80600000c0c006801120340520030b40381c039503c0c0d007050b5040140c0c14103401ca0b0003156a2401e001080031554850380b000882d00541030001d1144c403810000c0f07041c454041c403038044039644085005610036002000340072150003114141150385913042000303018801a9007948081c1000e0390b10142c40300240c1e00013900440705040107460100c582d994681044055803900c14030681d50f40400c46 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 542727149 1250 542725899 542725907
    0x80402040506040b031005090c040603050106080d0507201507060f0f02120a0e031923180f061903050114010311180a0b030a0905010f18080c0a0819 65
    0x1400c80b40c110b0b02444070361480d10110b40d49545003c05d01e81c900b501d402c046003440c2c0307007445007075001c3d6006402400641e03103d080c251702800c0349110b030240510a82c8480b04071144520242c1e4071035035001248400349000001d001c09142c034108020381c2d10103c2c0d002810000341480c401010700c5845842c1c041007001c0d2040095088070310442d042c55100c1d004018004800078243d200719031241c180c0e00000b03000c0c01c041c01090314600415055105c00d8507550321030302001d6001108060452104401080340c00c0300014242005c0c040c110341444035156100018803140382c01540300c00f200d1800b40829045c48000c0d103030309610b622103284010121740c2da84014840c90300b041082c04c1030302d402030805200d500109942011030380f16100003011002d0550000405558403480380e900149190b2044d651a418807a241e5001054900c104890320b40c038280c02e240c0e290500e800740c4009a282219500031010268551046a0b03111059044040c003541c1000000503041c10042c120303101d0701c0c4188402a000050010b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 542728399 1250 542727149 542727151
    0x3260603010b030d020a0f0f050102130905070f0c080a1701090606030b03010204050a03140c0312210105060412080c030307021c08060d08450117010605030c0f0a0804020405 76
    0x80d0013a0002c101802c2120340003d2085400c0e64400070490a05981c1e046c00d1403546d621000051165000140007020481c254005005458088100708000c3c1c403103075010354488000c0134038603020454008900c004035100d50068940030155042001e2030740701c0c000c140d1080c61400d0300074254141c2d5628043c0080f130303810300c10403800440960003146007904100000f04c0c00703012440700610100d031030302c1e2998040e10306103c0340c3c071002009001c80714050003280c5004102c1c5c000c0e40e1450644810128001164400c5441c418100c80b800b620151909050441d400b650040140381507c0c80c400c00c1043e0302200004000562080050f0b40c080c07c10140c0400303c1d40041030411006104000c0101c091105d1a51101002030601d64000c503100e50350b800d070340100c04030528000c60051310849038040b0880044000c000d0400c1d0071005030f0300c0e000694412001540d802c030817001448140070140c4010f00c071082c00740c001590041c0c0503a610740d041c2440c1e0032041c0d08551240900600040e8404140070440c01c190043c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 542729649 1250 542728399 542728421
    0x827010c020c041e0c0c12050901120c09031e0203060103110307150503061c0204090b1909050618120418060605040506180a0f170d0c03050a0c0326060301 68
    0x3840500c041880b401c410607a0500c01140859440d0760391008580900c441820342944407040d90b070140e47c0598040c01e0340c0c0201c5000c0303000c14203d0881048030301d6944941081c01026403680b40c0018150786490321207401e080480c04030424481c1e004400343ea02004214000c40c80303801c002580b41d0781201071500301402544040e400c2c004409818030340b01d400c0019264419001d0ba03484049520015050b15010401103020b50130919218031901442080c17607042c1c1c800c0c400722041d051040c001906100841d2a100c1c070240c0f0369044000401c1031f018802e51030701c6000021104403844a1144903c0724a01e90103030340f0582c003d10200500044e682400d0060300000c00f224200541054501004150b1a22404020750644074a000780344040307507140d00c5482c0103490046c0b1000c00709c9071601907007142901d40400220701352080f0109407010620650410b42990380c5581c0d4a0b052032000c504c1039401c2c4030340040c100e00b0300c049002c60900642564614a03151011013107021020308104007411b086498102d02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 542730899 1250 542729649 542729651
    0x601080d08091504020112020301060509040b030d021908040b22080a0b180f010c030204140d08120c07150609050f0c03011a0903070b090913120827010c020c04 70
    0x108030b21903001054481040300600303003a00c05030f603940c03004079022003000c070580f41c07600d102100100305507034014007805969009031800c0061118040c205581e810800703141c4801079110441220591b14242c41e0450214414401d05080503242c0d150311900d40c02004000d000169141d241c444266400c508002c003d001000c003030300e4850156243c440d12210010104100700c0304061852211070801c01c0071440c00c155800080102041514004020758001c0c410702034501903a00a120207490020f41c0c17000c0d11640880410714107080300c04e0400b900c0381c0c02410f03900301c2d003c2440380d1000b1940121104400b42031700748001421074240b0075800c0448002904480c1c1d4a401c000c2000380580c0e03103400b1a81903d8036841840060686110070310454480c0e2500c0c150940900c00c030015030002c249014003c0448101d502050581e40c204d82c1800640d00c203800034100c540d182035640503444c061500c003a08465400103910a01510400b50003030800100000013441c5e550301758485a295041c0008988041c003100c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 542732149 1250 542730899 542730901
    0x60602210c0c1c021807020f150402150f030c1312120e151204060c080c0702010806042306012c12031603090e07030605060d050a0b03030c0601080d08 66
    0x801d041d96030490001c0c2c280141800300000d920940c64020100c1c14550091411003580b40e400b41c461110b0200b511408090311450310b0340408401d02142c13081715902d9640786088956150f40030004038448040300d00d98000410002c2010448507140290310404000c9611661103545484038903d0344000d5001c100440000d0b5442c00000d0b885081c0c10350303a40b0303e034079003804580c1001c4001641d007424030300d6030f2001d000c000546041260440800b584510702510041003803400000007503800060850300b8840c8540100183c0b4019801140c5880e04000040c000240c540b0303000c0b11004a02c0305038260801c181140000308011503902107080c026104880600901c41141202c008201c4440040b9441c801c40b145414043d0043e000c0060b10f10322102600c081c80100365508010700060500e014407241e41d081c032400102110302a005290803101c01414061404860f0740d00b42d40240380203085c1da03103c291614042001650104081e10704007804101406095141203240c034501f02000440380c091118200c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 542733399 1250 542732149 542732167
    0x100f020604020909010612060906050901060302030303070f140c03130503190204270b100b160303021810090816030b0412020c0a150e03010509250906060221 69
    0x21420316005039054074000ea00b6154100014090950b40d0094010000c03021070800600010f500442c0b65107000c6c1500300940c1e01c1e40442e140c00d850b00c0c1e0101a405500c01c2001c251414862043e00c807019000c0c2c50310000e064600d944d0b160150f402a58910081e52000c03d130900d40f0600c1840401c01040120010042454030703442d071020285107141c002e4413450b60390350f0103151900d400200e4848000d80300310028501219140850003090701751036480346840c0c81507020a07024081012a001b11154080b07010100500323690860280d40040007800c145000d041044c4119110341c0100d42040c8055100c00001c80d040007807541ca0301d24110f80350022400405c50420201d03135003162464015070001ca012008000c0c024050b850003400301025600010700c5000040c228640351003100310004240d4504420005c4182011309840342a80c01001603000300340c2119082403e4107a5804a0070f082103a03c01042d603c0d049a41150076940c05500540c0102d00941200c0441c1c64440c3c0c3c1c9501008605810700c400703a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 542734649 1250 542733399 542733403
    0x702030f0d020706030b03030705030a08040c09020f09040e0c1005030a0b01020109021509060f0d150b0910030c0c0503030a0b040b060f0405042a0c020301050a140c0a0c0c1202100f02 80
    0x4d12880f402d041d507418248543d51002d0044502581d041011650769503000c00b4000d1005004840a69601c04032034004200006d050080f1100e5034110a989800c100681081100a250b110b16150486c850501c160140e42c1f1101002c002207415a03c0b055100d14180d04903006542600c1c00c1903045900d070444540048c1d4072042e24482c4503606003082507e41090344046401d07072049851071442c059001c40c02c4c1e402c00e41160442c184010100c001180d007030747e98442d03041c114051543c82c980e00010328000c04400c517120358003801c4800e60f20310b0a0194030105481e6981150300541d20000d07090307165000d030400b80c2814041c601d5030000540e14103207051000c0c1c1559000e40510300800c2c2c0f040340c490811000c00044100749203001c00305c0c0c0340c120825281401020700120184d603001c070300035420040010640031140c8122409007040320380d42c500720b5032003010400c3e19501c0700c500c40c014002c041011401083c410010817010b8542004a00130000240c010489041300c40780c40c0004222070f25842454480e40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 542735899 1250 542734649 542734663
    0xf190902090c0304061d03040914010b030a0903020715020303010f050102032803060902120717060f0d050a12020604141b041515050a0314060906100302090301050c0702030f0d02 78
    0xd01c14083d242c1d260fa183c420040c3c0f01d11646008a4103080c2d40340700306140044000d00803101c000504001c0d60110740c000e100c218a0901c10401411020700002d4801c84e5a81c01000f0101e00c28810b6500b01070322081c00c00007868100c401c50005038000f00040c00341140c0b50f4031600107000240021400c16241080011407004001d6503000c8444a100e115040701e0702a81240000d00541001952108040301c88841c50980072284400010403075040210846109600a40511400361104503a10740c60805e02810125045e4200c1d40c1d481807090903000710b02c000220a20182140d4043c0074a8140350400c0802c80f034001c20a03000b00d07000952103503030869502183c032803100425a808225902900070040910b43c0551140301c0c4607450007150700e6103503400300083c003c0b981192810841d10f0203034120000b0600701212040c1c1c0104c15640496028500121800c1d80e4180e01d1030098900300115002c0703401d41d103003594454840320300440d0000840c07506021048000551030018a17881e10441e40096903844 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 542737149 1250 542735899 542735911
    0x50a06080c0d14190b13030e04090c03080f041701021305010f1e0203090a0f03050a0b04081b0c130c2a1403040503010c020307050c0f12060f19090209 66
    0x80c0b5018000c0800050342d80841d0b19103070700000d48016803044c0c41c5501d02d400e0780000071100c0302c0c04500043c02c40320043c15201d05040e015911003050401d45403d01c402007022140540341c00d02c00c0700c000000500ca22005041c0c4114070b2092680b607901c3d094944c0c0310342826002c4010664014002003400400780044241203e03000d20f80074070105060401500c00f2042d0040c4951400c241801510744160000010440240250f1761a400a580c90102e00001c80781070000030002e8008088400c003161880003da81c0181c081e0300325619195911903610301c40000502e481d00380d40c00500c465841807502070203801000f0650207080c40a001c2c1240002c060821380b211051121020800d041008007500c010010400d074020380c211400b03441144501e58907041032080c54482e6090841d503140c13003032011003540c1c50a540840141b640161103003c00c40c00c1c9881d0302e04982c0180340409004440001003140a002e270900c80c0b0a460203003410380e16800440519011309450909001d450b10042e2540804c4580c032074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 542738399 1250 542737149 542737159
    0xa0603050601050925030608060709050f01210c031d06070305070e06120a0209130618020f0f070218010b030601030e0601050f01051c06030b010e010f0e01090b0f0301020f0706050a06080c 82
    0x20f143c01e80103500900310b23a08802018411503042046075500180004103480c3c08907002d400550040004440d010309003441640301401ca85d58a4400340e2040e0411401410f542c140429403072585107003c40e00350140d12103621554010028440d0294040c41480c0d049143c5d85449140d104070000480d0710340c410006411000681040040d8003e07003a40d0641e81c0c0c440004020b200a20405051a40542840d01603130a8205880f00c0b24800010548201d410740343d1100303180f07420200d02c610700390840c1e0040c604c160f0b00a41c41c400c8403000e1b00c0c0c0d1040010301070560b901900d071b01ca041ca0070006088039820f855003146544000300500c1190780f070041016840c442407800d00d580304511203040d2003404081d40480101d81c1080380120400020b0005103058800008a01e81d8aa0742c807038841c200140e05200c2d01e0f0100750f035400144401c0300140c1004101500140a21650325a9507020a08a038007000c440c0300000310124a2104003e80c41c060740d80c0111400c0c10070f0160a041002d11621581040043c07803082e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 542739649 1250 542738399 542738461
    0x604080a0e010c02090a09060e0312270d030f0c09060e0613080109030806090a05041106071b24020604050712051c050a030507080906011a040e0a06030506010509 71
    0x7680c4102c0101c0091540a003000c42241410040c00303003e030104050447d829070400120a810407800420f40303180c6130305440a180281c83d0749001d102000c0321001c18002c49824580303034402c0850304200c03202e4081c49607900000c14102c00700c083d5007210103050400c010002c15a4041200c1a0f021540b104000812a10b60750b0701c0311641c1070038404030300d203030f02080195080c240090181600080254071030343d025900110695101482101129011a001006c241e0041054061414140003074450244a0b100105030902d804c0204020461594010242011264541c41c010140b5501d1b441c040311071030004144034182a41e030151100400d02034003a54000c94003800382030041c03c0264409284080003003106224038980000c05070750210044030086401c0c4070125100c0f510596003d0f00c20000f140103010f41c0e07401e02c400c140803d03061950b0304940d02400c0c000850300b43d001644090159280c22800110140345150060034240c0c1644154402c4aa2204206025030011001800e815000103050a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 542740899 1250 542739649 542739677
    0x3080a0e0d08030702010b0a12060908071a0402030c010201091a06060906040902040905012c071e080105030f010501060f0e0607081611090702030a05070218070512090604080a 77
    0x4425201000e81d2214182031440140964400254042c450b15402031000200307181c180100203080d0b01ca5041399100845010700441c08a0780000c1c14507108403901c03450030100340c03950f100c80e11119602c84160f0700c2460500085244c1080340d148040b03401e000034440340c1d9003600d81d00131605c140e8800b1000c214070440001e2407a52103078211140032400170060303a201c54882d00700000940290044480e42442d00c000495003883e01c09102c10720300500402ca503d0442217840c100c070280030140c84002440407200030210406065011a00c046085680785500e5626000800d8502010000d0303000b0180d240030014040e19030b01000c1c91920780201d05000071600c4425020070050706c01d061003d0280c480114041c001d484031391013281d0f4154092600000d00400300d04c04c03c510060141c40d0940540d10405c0386000700e44c041d00290407a036000a0500101040c84a001c0d00220021143c4034001000080c2c5403450240c010000b903000303120200241020b280a64402c409131003000309140502054240e034403c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 542742149 1250 542740899 542740907
    0x110f031e09121501080313090b0109090618150518040c1d090f06070e04090c0305030414010207210807210306210b040b220c03020103050c120103080a 66
    0x84012000b808200140e801103041e261101c4001645a440303071a00000050703110400015103155000b0003c01c492041d14001c2c0780e80091001100f00350600c038000c1e4001030415464031403040206012902c407880114155400c808036414208401c0e960f2000510520440e00c465100c1041c1000030460304500340c4803810807240d0030815038000c1080701c00d448400e004500b440a03007503001d4502e00c1c04031403a030502c080d603194881100701c84040010709142417403000d0b0b00d030680188070500c1c02a078010041c2c40d182c6e111642940e10642051401d5120440980701035641004088020151003001341c2d94501c21182d00324400d201d0081c044d062000105949040c01800d01244040c0f00f800240c10a0310001e0141c09406000369100e0303413030030794111b400c2c003181d400400d4109600980d000d0544002d5650b2235503240110304016000b076003c0c04040f4030340840e260390041c2c0c406015004881c494203075407071440010140c410040c41c0d880c0d0b1610a1000481e1240c0c2400d595054950048103a9160344610800325 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 542743399 1250 542742149 542742157
    0x10b1512130818010824060307171f17070b18040e0705041d10021803071205010f090201020d030c11030d0609060b040b0a0507080904050a0c110f031e 66
    0x40d080c0200003c0c2040002100c2c42d900c001280d081c1c03141c000b40c1c1c0c0c40006d400040c2d8030341c0c1c0802c001d8003c8601c00c000e203440c002c4015940700080d820031014045550a0300c1c0369510b01180c5801c64004000d07900d0704000c03c615440d030000c103030f10f040c80b2052843d039440c0303107440744218803450a0051012602c02a00011200004441440503104100e09038a0103101641c9a9085c46114062440c0207000d4090307000c0595000810109440144040b070741c5100e6000c0254041c1404141080400c5440800c541c1d081c0b14090040c001c840e0f060342c0e014218280300382144da050b00c002c040c0c54501180b003001030342c01080d90303540711085040004030181c903400306440b000490340c04041b4500001a4078101c0a149a1141c400c0d80c590310b0381080070a44030100c1d60420300c114011610f05c03240504c1040d025906ca00000c0540511604405003001d003003a0120342510020340f010b040380c603100c440d840015540301181c44a0070542d0001004080d031440c0c0d42e00d850384179001204941d030314403c21040700c8a0f1180c00326 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 542744649 1250 542743399 542743403
    0x11e0e0403050d05070225150e030123040c060336051e0c0f0f150405040507030c020f07061e09180207120c0206030a1d01060303030e010b151213 64
    0x20f000c00d140030380c402516021000e1920100c44403106200454101000e40302040da8508c9240511214541e10281c0c0d0f2800000301450b07140d900d07000c03503041c41440f00010301c2c0c442b0b00168410f03826080c545800d0000daa8a604406e00f050720344840d142c8915040c404020319802d01510544101241031502c80c0311482d2058040d10904c5150b1560128604c0d00202c801c08000090503951002c6003d01005910140c0d1641e1560090f0003a510b040c443c075051030304601d41d085145841c0c0c9002d540301c001c20f055540c00c8400d240031a5071181485140e98050001248036031098020301038030381c10140302401102d01404000354800d1500074410007a07000e40d0800000c3d2184030b80f915071051103085558081e60014600b1144503000100904560340100804035240394002c0059003141d071340b201e01400500c0460300c841584507907800745012158081c4200300245001e0f5801140c9008505051030944840b8a0102d00540c1410380822044141c4020f56803d00c4201070000c440303032212111008ae000040c100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 542745899 1250 542744649 542744651
    0xf0a0c0201050904060807060306050a0e0f09030412050c01090603140106140403230f030c030a05070611070507060201060b0913090f0b13021e1018080a0302030909011e0e0403050d 79
    0x6c1078515001076600100ea655690a02c1307401d80b2281030100b081c080340710740101c0352007040c080360708c0005403204c1c036904c403041104503410310342e6825104c0c100080b0f4810a56090308070b500d0701400ca5a100e9000009000c0908051040c58108040410007001c14420342d0100854002000051a80c030070880e030081d03802c40c00d00050b1606a05a144040c1240802d200c814401d44102442c11580401510540590100554100003d607107065600368403020b8122001651104513004821507040070b443d0050060340188809030802902a0841d0310a0300700d980007072030520030000940d403000503502d0301c41c1080c400428400041d02d020164074140050050160010748100b20100030103d01c240d004600031510307403800140d82d9150b034010612213081340723410400303240103000d2150280c00b18019a009456101840031f560b09d031101e00b0460348850880040e003000809085514061141501400c03a05000c4412518030042d440c002800d00d1140301c8507965100300203030901d070091060381d00120721500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 542747149 1250 542745899 542745911
    0x40302032a010c030b13050405010207060f050f1008190507050d030c030306090c051207141b1e060115020f070608010305101a04110c0102070f0312020f0a0c0201050904 74
    0x1c240c00000c0040800d540710356280c0098207007078911030f004401c44281d0181650500ca01d20802c201d000d0000208281c2e210740d0201704040004c0d443e81300c2c22901c01d00084000445040074081c164078140080d150005500d80b0381c0082c00800c0d0003042007004030300d04140c04039008800d46007060400c801075000e5a0302c09401b5015806040e001150f412202c1c2c440c1c1d8081151a4840e1000011204545907020008200b0702c55010f591004e00a070b00d400c094141081030440c2162200d084c070f0750f4040e46030410071407202c3c2424919401c1c200294015501030041504032000320101c0355075242414441e009864428251000c0d4403170080c840001c1c160140e6042c1c55600e034840700f015100c2d4400f8030003101c003449516424040c5a6143c424a589100c0307070f0003044000b041100412025207440d500c035052480c4100203503980d0b00402d10003044550311401d940c1c05d009102e810058680302040307030032502141c010411020f40c075074070f00c04954626406092042c03252807940012650360158070b05c903a81003803901c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 542748399 1250 542747149 542747197
    0x30c0a030b0103030f08012312010908130b0319020310080307031d04020307120506010203041e08010e15010303081012030e0301061508161b08031e060d030804030203 73
    0x220105060b03034040d0f00d5403203000912400c200c1d145ca200748200181c0c502c0c0381021217051810030210300201038004002270b22010464001c5400c444000004480d4201c002420048402c3c0605110000f030441c14103c0707055260101e10302c1842903441242110b66580000050421011510090041c105034800c03262507116620b0090308082e0001c0c02c50040ca01601c403022070900e090300032030344650f080d40d8651a20794900c1040d000a021b015100c0c03030641c0000d002c0440c0e0030307048100000d45c141c0000c0c640c40c001032070044164210342da01d020800d00c41e085105158095003500029034116649480c1540c10b540d120152700c44000c10310340129010403030000c034043c185644030140e1050098120001c0060320340e0341d660407070002400240c41340400c904800250f810781e2038000c24580142941071840f00e0080c0b07074201090b00180d168045907a804007006201c950814452510801c011640c0803910b5410700d000014100d0050110040c2000441c400203001c240c0b007070050701d210782d0380a070090100711803072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 542749649 1250 542748399 542748413
    0x20405060f13170105060a05041107060906021c02071403160b04210c061a030a11030a060903020703060b0a0b0706021602090114030f060408030f18060c0d05060405010b0d0209030c0a03 81
    0x3071b5040c40c441d100300240031540f440d2a01c07d4803003030402c000d03501d440c028080d500d20001d0702d2a083e003550030b25424000900c0b64401e03100b214a07180703208240140d80d402a4034100605044d110f1110104c2d41c02440024801600d03030b840c0c1190585c0103001c0c60059901c6145c09400d01708580c03101c0885141c1508040c4040360002d00313240808c0d204000903c00072101c0a0181900c041040466600d5400f81f00b0706804690054180b4540e00d6003c0d0a58010894986842050714100c1004a0043e8004103042003489020700c208075008404446a4249924004400c078090052034000f03014968000f9084840b07801c60780800340000c0c1d0180c0001100d40c0c1d111180c2c1038100c4482d070014002e016410784143c130013002082c00762199a02100d124115200c42c14135140b101c200408484002941d80d00d1500c1007107041080b07274420503a41d005603a80d8500001a802603420143c80036004909010050005011b643c06642d9108000303680113807103088040c00240b80043c0c0203040c40d004a20404007005102003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 542750899 1250 542749649 542749651
    0x901200a1a0906070c17090f0a0308250309090216141608010203061e0a090501090203070f1701140103060b0d05011d010e0c0706110c0c13020405060f13170105 70
    0x3850030f9954583d5000c1c4143e5414900d094000c0c6a03984060001603421000409402c2018001e41080362110b100f80c08184040754a401c01d81d00322502040741c1e42405040c602140c0c0401d020742107180c00700001c0e41c010b070a0050a0280284458010075591200b241c0c45015034461508208c2007114000742c0071015498001c000240c51a032400b222000c00e010f00c0500869006610140ca092040c800302c44d1007520303541c8070380380c826441010140700140103591b90040c0c5000c0c0c25210001a96410312030b0340075017602c107180d124200b03020201031401c2e00303e098004010304449120b10003c0f116842c2c10012002407030a5048040c4204021582001d849103561089060383d1380d001e1140c94041803030800540070a001d2040041c51244040000d82500700c0802900040b8810354000c11800001c081500081d00324660b410295804403002c02214904210540388450300c20600310f00d4981030401280c02c0348a090540440c2e402c0002d1036400d60381030700c42e00c0380051442004d0008010181c8000701e0281c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 542752149 1250 542750899 542750911
    0x1101020d0e0607081225050f0f0a05090612060913020d120219030c06180b0117280c06030c020d050c0f011104091b05031906030b150103110901200a1a 66
    0x200c0304007502940103004807010503002c0c4a4840c02c003003270748101c059150300c5035015004002c1c080c06810480d0701c461010303048815030002061103918205c014040a42002000701401400d0100300c040962101c0d000510380c1c0da04034100000200411009074540040b00c0707403c16520552840500505902010114200f40b00304024402200100c0707030b00c0411440b00c4009000c039130f144001088070028000340c08200f501090306807489080780c0185503c048004c5200b120003048424884410040703a03042c04c4000c2c0007035040411454410b0b80000b582d600700d40030b529042c44130009940107400300c00c11203495950700b4035000b40003040c403107038420b100e03a0028031410340b50b64101100101300b402d201c1c0e400300041010342c7c0c0d100d0450351560030303402d021382411160282d0702d940da240100c0402d1a601031180f00e21202200c002040f076034403000604581c0c4900c1c1a980c800d00500c03041c142070b030344070803503118514a910721641d28540010380d007410164040300c003c0164045c00c2840303807030401260352613201754 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 542753399 1250 542752149 542752201
    0x30a09020a0f08150c090d0f0b040c0e060d050c010e01020a080d021210060e3f0c03160519080102030a06030c050306072001060b0301030501091101020d0e06070812 72
    0x100104903400032140703040c0c417825a43c110a101056450031301f981d80144503402440700403800d0059840b100588002510213881c01924074000b40701b407610303041070030340c103c54180c41c0728110102e84c0c0c480329107078888940601c0c1000210350b1040c419a00c2000040c1841d50001984d81e6204441d8158800075408090b1648100d80700b0390000e2148000080342e02d00300d031480e494885118010f042001401405001c590080b844a402100a42200400f00d40728a801100402294034001c1002c0ca182505420001b446540038a205a030300700000b0315a9011143d080c9c411401d2550303400a81d400c1030885411006007584084100b0460b40c4a40c0c0101044074042c1c440b1b00015074803181850785030340c0d08a4004000c81c41109032643c8030a07480c14002c5140354468000070b0119150140b20616600a91040c1c846070346072551070080c0900c00c4041120700009000070022810039000241c0801c4001c40194411103003c5810400d002c440c0041791010198241500460b10f01269400383c102c0354140d40342c03010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 542754649 1250 542753399 542753413
    0x70b0105010c050307110607051b0112062318090a020901052b0201091223010203060108040f02010215041506360207020a170f01060302060f030a09020a0f08 69
    0x7540540d541503070301c50704203001c0e41c5041040c1c1c44461400c0e088000440d00310f20b0400042000c40c2e01480103906c1c040c00c1c40441c06280c442d90700014080c4010050105d4440d04e000c03010003900c540340e00180044a80c94500c2c1407020b0501d00050401340190250542e181c002e00c0800110200116290624038421a07102c501c03662a141808640250203600156100580305600516101d10fa40700040318814502102d2040c0c880051248101c60288111600b43c1010030070117000c0400d00791036080841c40c000850651400d440024811503001e400600f00010308580364080d07900c21710407100c43d18060500d0409d98106850100541c2d4007102c0041c3c0c0345845c1840c049600c041c00b1101502e02050307800c4041c5040480d0f914915602101c86032518503903401c202d0350380162603400c04440100200000002c030810306001850801c0f60b12227540340342c2d91504000303100517520042541c1c01507494044003512982c0b444000c40040401c100007a51103008030600043d80d404180f401015500070f80140e500c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 542755899 1250 542754649 542754659
    0x60c02010203040816140718240e0c09060a0804020f0117010501120914030408070b030105060a030209040f110310050306011824061707170604230c070b01 68
    0x1c0340401d41c1c0050010104000108900c8100c42c040d4031740034000c08000c0d1208800306200c514000f007590048504a031501025040d0000c80d215006200c0c401d41d200d40304144070300c001d13414500c2440c0150036801d011640407498410002007074414181000e00706541c0c81e00c12890141c45118122403c91103045181c10b44078841d403191041810005808142c0509039090400555641810700314040010740c1d9111414082070f4924400000014080051a500c9007404042810600240c0100c601c0410400041209407540b00488031071010500d4010780700c820090001e005030540817909070b00700e0b04090312500400e04031001036000c1d5150380da51044071607440d41419100c1c0c00922500410710302c1158000203400158000849442d004990b14400010110b104501c810241e00008005007172a0038414101d1000c000d61070b0051010304182c481b04c6859148410104001005a409103454252122801c010103180c2d0210040c1260400c2c403519018002209a41101c002a40d42c02009400011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 542757149 1250 542755899 542755901
    0x11130b190c23010e01060f0f2304050a020f03040b0a05090c03060105101808070905010905060f15041a09030d08010b2d0a03021306021c08090a0f0f060c0201 69
    0x464281d200440480a008402c540448a0684481480103540343d05403200040c10a208040c00340100c0490400c5503801d0100c0101c4582c0b04e900f0905400081d40c01c1005160442c0101c0c01c0b20200c101c90200d245c0da00e110700c250203030044040d00c1250034004001d000400500c3c0003503a2203114101002c00130765442c0c07401319954890000d106901a00020014030841c2481c0042000d1840c180c10305090500110035580320030700c02e0307034046042c40e0000d074818040c19a0b00d00800d80100a080b40510180c00c124000075001010148400c1c481c81c2c6050104101ca002c00c002e690003407031807001d6400038901c5580b4030718450744680442c52080c0075030031a4242c090300a040b914181c2c0c4882e8859818000b00f00300c4403c10407031181203010164160b000402d00c1c40c0c1c115005201030710003640c0261720b8090304034680c00031403415001403003550400b04054004140305180c248c0c00c0e40c130f540362608103501c90291443c01c0203035000d00034110411074035904043c03102c0c1d07501e1054220710592040152420582e030480c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 542758399 1250 542757149 542757167
    0x8060301060b04122a060e040b0f0f010311040b09010215010605070f0804080a11131103070302180301050702030a08070905010504180b0909010c0e010206060d0611130b19 75
    0x12019035014003080c080c0c0c1110b503840c003251038402c1854151550708621140088000003031484030107a02d1010030b100f1b0942c040074078002000165002e0060300300c2840010101520680302d00e005c4c818201c150111680310750491f449944c0c0e08508a41d03116210614030941d5800108498094410f0014021000000041113412141c480e03030b950b414282036581e1200440c080500c1511003140501c00030400840901444800794856110125600101418400340204544520480301c0c94600d65a05015001d0102c4c0d5221038140307001aa00c0d221182c500800c000303059070300780e0150718000c104101a0740000c02400703403100b02e8503510101da880000442c0c401d011402003500281c01400100180c480c6000280c3c50242035102c00f0a8240194001c0740b5140e00072106190303180e440b080c044e0743d0240c200c071069800201c00e01c0078180e00c0c43c08001003000d22100380801081c080d46c9181121240d02d42c10207648056260007550000346503115000113803078100e200e01107074040c0403911960b10240a19110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 542759649 1250 542758399 542758409
    0xb121b121c09031203050402010908010e10180605041208011e03020d03170f04110328141609060e13030c050c0a030b0f01090207030503041713080c010806030106 71
    0x40101c280003504500400c0410718041092100c01c0700d020001a07410308130380b58000d903a507400203218a018000101820042c0d0b01c1005039900d04032000341c1c00c11000c0b07030802c1d010418080114010103000c400e030080c52661907015281514260600040056034002100e6901260707031002010b9807a449210034036103044c8081c0000021a00c07080006091440124030545c0c02810106280510791010b440407030f50448920013048079400400040042480001d0401e803410f80080901104480001d5200481442c80080c218503902c144800c001c500c503c1058080742c03000c160b039840a04400c19143c00909406560141403c04a003c074000401d41e905501c216000000b0038004c0c1300940741500c0191160809442c0c9014030b0b401e0543c0c41e10740f40302040080d4840d40070780e601c43c07803ca00c41203d4a001a080501c010303004026400c00304c0d5005003500c0c0c029402071101c10114800d80c5c10300c085403198016110480141d241c0c00100840c0100d03608600c48001e0b00d07542c842d0f41e2040b0425080351924014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 542760899 1250 542759649 542759653
    0x23040209090f0703090b0901020c0115151b1a07020601081207201f12150b0d02040503010c08180c030d11010b04020c0a120905030604030509040b121b12 67
    0x64502290004860b03081401424000340c0411741e61100145110105c658000603900002c041010880900c00d981c4240c80000c9011820350800300705002d03500c0703845801c03000c1020700c00052580f041100c800cbd40c501035200da55071031001c0e078000b001d00a071041200e000016001c4c40d8000500040c0108003c120001c0a080561030192036540388294020007481c9415440a01a060440ea40700c1d100c6110304c074021a882421625000c0d1002800c442d140d00100702c0302412304070007a078079420001000b429507180c0c0c0401621800c4402c280c8000380100d0b4010f40c0c4c0341d0b0a00506013503c5070851b00b41c50140410707950381540d41d1a0310350100c0d42d50060311519501640526005040036104075001042c1102c404008520340b14018001416604080e160b840b841d00601e43d180d04102d00d00361450003500c86814140d40c19458040000d44030340000300090103101c80010402025685ca0b032158545110041c42c400e140446c6542c403a03602e42400c159211804904400224145810203c1d11a03441803900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 542762149 1250 542760899 542760901
    0x606090b0a090608070c020909030c0d020f0d0c15060f03021c0201120b040e1c0905150409020d0f020706051005010c05030912070e010803130f0b09010e010e0303042304020909 77
    0x10f00321400a0000c02004c2005602d0f10401d0060b42c0f40940300380644041c4c0c0c01103480d010485103ca040c4a12384104c802554000807858620110214412402c0350301070500c90400391443c1003054181d13400046000307a45240c4040411051404803000e02074a009540b054498030013a0310503c10390114000207030104d075442140140c85841e0b6040105440c00c05040452121100e800c020302d0012003060b42c0450501c8000000025a408100d80e401004121035200d94440070380b500142d0703480f882c042d40480300c3d00055501101d0640d81c110520b4118039100031076032070f809400d2200041609a82245c420b113034000c0005125031158509465050300580a03610703207031030602081900001801d204201d4054194002100c00c004480303680200070020285680318020b07160049074a80e142c0004100a0381c424091041005160984252000a0178401041814100180c0743c02640e1061554140300010300403954502d0141c0781380480340c195100116550303800081100b40c7c020100804d4008132624 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 542763399 1250 542762149 542762159
    0x30606091905060a0507060507030605010c03050a0201060b070f020f060a0e061b0a0803091c210b0301060605130f030f170d02030a05070206090610050f01030608100606090b0a09 78
    0x90110720752240c034485601406551140440c0454205030082004142c3c045000c81c01d0040c14024280e2000c207602d410012142400c1c0081c0820b0311140c000b81c100540401d10b841c10034000d50020010b000c808105545454442c0b52203407074070301c4902c0201e0060404c609443da25007401001d0f00e01003680d5484070030443d802e041c01d00480b500080c07103500003131100741c1a1001c08030090210540c82e1b40a00903180c1e4901c0d1812017946802d20b604180e9008050141c0220b40c45a40a401e1400e01202a50810101414141c000001e049040d0030b486d4994030344840014a1074102000300201c1505001503096a60780701454a403000061202034030720311440746610000744601500400c8952411296400c09020350061022030b001150700c80c2c9000e0b5140b007804031483d010440d050303000d1000002007195203004200700004030b94034460709001d100240f2040310a68041c0e0400406091840c08032640240310f40700f52800b40925118400120b194800007103010b008000072590b2000316912a640d03141e00c0e00e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 542764649 1250 542763399 542763409
    0x506061603020a0b011202091e040b06180903030108010e03071a070c060203040f1406040317060d08030a060603050601090609050d0f021f080601050702090118021e0c0d0503060609 79
    0x1000c210118043d8a44410018030540555400391504515041c0420740300d01c1405145000034140d006628445207c1c00f107040c25115003580d100768046c00640c2c4507125980890400081b160120002607044410001c54070340002c051070407601d64400901555504180594482c440c122002e0007900e10b608119840044141c03002e0781250092404040210841d19040c0407a0401d40b0b0403200303c1c1d420443c0905215800b1440f0750301c99054000b514440c2004c0e9000707080c0d904085441d01c01344c0c6018000420380c5c0c0d42e07414894011500800304a541c0d250210344c0c10000c0060b4011000864542004580b180d4401e20b8103200769149a00c640e4212418041002038840c1c0c00c4000316009010781041c000140c0362801031480c0700351021548c85c014011000b0103402c401e0000d040c981000024071112002d82e4036039000904440004ca0206501044000f11740060710482455410341c198500e04030f2030f910b2003d07000340a034031040c80540d00941402c1c402294144400c0e98420343c000b00c1030013481024580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 542765899 1250 542764649 542764687
    0x2060a0315120213090c0807140901091a0d03260f0709050a0306020c0309060f09030601170d051c0c1832040b0307080c0f0a030317090a1b150201050606 67
    0x50200940c0151f58410075894088150062072181d459281c600501d0301f03201d80c0050142000b0075050211400040c0d0242d4001c042068451207103604000080a150203918903404008a2803c0820b2044a070750a192080009031000c1000b02b03444400a0140340c403c04605080d00c400410b92200c1916540303503540030790490840345425010800605666a407504020b11884800e1b01da41520f0313400000805043c110141d000c2c000491a4100b001c0c60300e04082850003010301c943c02d242d40c82d000c464140c075403003101024606413428030b000d4600c1e84441e081030b02184025040d0081108882c0c550300c141d0f101d2101d4031000305054107500c540914204402c00c2c02e82c44454050400a580504040008d14100c00359001841a0b000f03107030043d445042141308004000ca059942403070300751441e9002414218420100b401c290b445001103070b1130035018041d44402c40e0f0440d8241070340079032401d8800d66030400380c812904d10900c0440440341c240c0c018040c0511400c401002d4600301210b41c40035403c02e0b80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 542767149 1250 542765899 542765903
    0xc040e03162a031406040206041203051b1c030e07261b01030f181b080a030806120118030f170c0918040c0504110702060a031512021309 60
    0x106124808114900e04041140c04074a07002d04004001d24604110442101490001000ea0401030070440940c40b03810480d000c07501c0810006180c8421803c04490f40d01035043d101403a03d8007005030303401004000641d40d4140c00e80d90b18924480e8400f0100f44c00310741500400001a4120071000c015201da002c0043c2e000502c44461414601d01110b01c4509101e600f15143c00464001d840809981d40e00d44030700c40780d40041c080c08220502c0e00340111a0501c0b400d5000910101029072071003200c600d00e08911008140480407140e1a51040c640904444001c44031b550040c504015031180480c1c0502420f4076128120014841e841c000d61011030b40d800c8100c9a060501c8400c1d1004034456540520142c404d079500029181c843d1000d0303080003a41e05181c0c002405401103a400d00010803182d1151404440b001c5070001f46495124030420000e00840d00003944c000ea010940208140d050b030005541100e400d108201010b0300e82000e41c007006948900a5001004050603100d20300050b40181c1c2c1c06c40c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 542768399 1250 542767149 542767163
    0x804060b0a0b030708100b130b030a06030c031a0705160b0c0f0703090305190c170106091b090e090a0303090203160803220b07081b011d0c040e0316 65
    0xc0d00c56601c004a0f500598040000403260420400721312035034074000f006810b40b6806545005900c4c00b840009900354082c140c11000b0020204459120940c0420003d5501c0320060081691b6420b0104040e12a10750b0448948203406c0000d0000340b145048038080d0120b400113541c89072854803282021440103082040e06d40d410080000401c038160301404c821031080c0c2e030b0311403014298a0054207024020658405052540c01ca94002a18801c40c04040c0c0c3c0303242440192a00350001d29902504055001c280c0711480c01baa00104900c0742026001003401940b90180e000d6038409d01300034288421609900302d03402c104152000179229030440310010340024212608078004c22100d0441203c0c07580b08081946c0b000994501524070b102c101464070744110a103c221f1840c0400098044c45440d10040800703100203006004560247d0004d124442214003c0101c00d5543d000c00d0b40444500d441460207114110345c207070286c0b9280c002c9408101c2000f0140d410302546689198070002c603500111400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 542769649 1250 542768399 542768419
    0xa111612110901120606090203060a12030203070f03030e0618101e062916020909030d0608060106030e010605060a182c092b18120c12030804060b 64
    0x16990503400301c0c0603050b1040340040c020308626080041b202c40b54490400240103208129041e986c2150b40c1040b94440c4d00e1a140307006051501b00c2c1103102c4d039000104000015a030041c28198150b001d84204541202220300c1a100c00308104140d007608126265140d102c1c805007003160f0303666000030f450070180c01a54280b40b101c9195580a54260f5004000001c2c1c22291410504103200300040251a40010721450500b002d01201840b64100101034000c2030780c0c002007a0920b01c104105c1c5c080e2402c1202c1000f5280c1c95012907912503d00384a1540082e040c0652240e00202c188610740440b40010445860a00005030039609003a107138518550741241500000344904000a0000d4409803040d440c1000b649c0c80a030320300c0610380280280c015076012015402401c860315000b040d040b0920740f5625604050302030203e0700c8080030322203151010324100d000184e82d0510790034981c60b244194a02c08809448040d02550100030140290010380d094000c10040ba1b080d6101009180c00a405440b403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 542770899 1250 542769649 542769683
    0x3060d080f0c012421170f030f0910060e0f06030a0804030309091b050703113c0607020604030e0103140415110c0c0609030f070305030a111612 63
    0x840340d003450b920404840310780a408840140014210181c210780a0150714034000b241c5074040110794010007003040145c6003448411101c04419541f11010f00840c0d50781c0c91074082c04403542c0c2041a14a088107116600321810003d802c1d0141710140c51941200b0b01450f43c8075048606404406400e50381c0600402c440d0802268199008202640c002c2d00d417640c0442c54984a5412180100728559020350550f080e8503203158060100d98500307030103180480394001b403001a1030814051086403444071010210744040e003020900100c00810541c0907011414400c0040d0a4a868044801d400160060000140081e000e40c2032021000c1d010324000465803c20043c800703d595003a1803e0300c01c44030f030301250f00524040f4054049405103019955007000c3c995002681e4466107100800e21404001c1074104480d1800c20801d01607030504411281040d0f0b80b418076039100c0d804202c1c2c2c400050901d40a41c0c081c20380c0002d412910143c800c040c2c40c02d081c5029100c0c2101c050703c85040311000021142d0380a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 542772149 1250 542770899 542770901
    0x507020c1c1704150905010903020405070e1002071d07080103020112111605160b041811070308060109090b09070503090c100203090a1a0304020d0f0618030e0603060d080f0c01 77
    0x489542d295a00e003020080c207034066a24a0480400a1422090105076402035521040b81c0d0b0558011403140c40d6004290350180f603010040d07406c445640a0701c004160b001410300d0032117508441c0000707182c0101c3d184400d2400200c8400010a100c1e400410055202d02c211111000d84400b00148d030300c0d00540075128980c090390460315001d0302c00c104a07003802400e1003c510340000c4a48007100162805000005a020b0307449540112070f01d841400fa28840c2c20b81201502003414441140c2d20030309480e0180616409451a07400a05403e4022619a00d1031258800242d8028650081039841c40000c03a07040d0b000400501050140103518132a6448040101051880da5009191100d10507414071911500c13650052250716100003018900350003550841e0f4006405031030b00d20003601c1d42c0c10603c0604603600b4001b40418500658990242c6200012090851180d41d803100c0c0100c81008000b12400250341d41c69004000446a000003036400000302500010200124200b03001454014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 542773399 1250 542772149 542772173
    0xd050702060103020a0501170708090a14070611070b0702090c09030a030c06050714070204091103100204080c0609091f050a060201020301030b10060c03080601090909060209030d030507020c1c 84
    0x10140e40044010700451400e445c00c940503040a02c1e00b11408010b0941815003078401404403418002818082030325080140a294012a00640c0b040801da080494003035940d10302d4810540090011441c0050300440400c4000841d800314034280e08141329902000820580544418503800c1c0c00c200e1500e050300c0910448208900036201c0e1448400d80782824025644014100c00820180321b007021154103841e42510490380e0160390026411041d85001d403081441030301380b0b60703040c4100e8124040170038864009205031031303610080da4480700003c406d01031940509215141d01100000000c0c80911000383c029a000000480e070281642d0303500040744c40a206c80d000f070310060350004018410702c0180075507103800180344052105003502c0c00074010012800640f00604000800d0040303800e070380c8030341e40311400b07400003034401c1000c180e1030319207500254000240c0034080e00920340d000d42c441307001e4802d42d841962305801500c004021031041120011051041da0028103507070703080ca80464403144000e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 542774649 1250 542773399 542773411
    0x602070303050c0306031e070f0f080c030604080304031d12010c110c0604060f0519050913140c070f05030d0903021209061213060c032702061e0d05 65
    0x1662440281401000da800c001d1040009500c104140503140d240003500316540558500e48503985a2101c902da403c284003a402100400304040010618042603880301d411a84100b040b611500d0510050548400c022034014224a0342030002901083c010011103401d001d11100702a039494000001488640c080d00c840c40c4243e6450460034149600a078001059049032001004030041003000142144034a01586c0e00300001c1c7c03c00201700e0ba0050b0240e0380d08910314051583d5a41c010a401030507500b14550a910a550310a003100172086548245008181c1c400d070400c03029518001c0250707860f030003c030007203500c2c1c4221403100d400320340244043c0424410303156012401c080a428024609284020000344c4190300300050070156031107404072092a07130b1b11540901c42c0c0e540d40d400c4d00f1f0f40c00100740c006880d45013080800030b066a8943d1248a55290041c0340d500c8004980500c00540780751280000d4100b03c0800034201181c40100c00c1e01e0030740d4103031505e5900d052aa030301c8200c10740c0c40c16146 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 542775899 1250 542774649 542774651
    0x120307060e1e010603080d0b06131d071704060e07050d0c050301060611150601090b03041b06090302030c0607080417070f120305092202070516090b1305070c0c0306 72
    0x2d22184800403410419102d004000910042c1e056840394036651044803200d404907903a81010514039164941030f00c1d8100603c240364090300f40d0b640f002c01c280d200d070a0112100054250b0009000074041c1116400d102c41c117155041c4d00e40e0b1180d03142401400b40f4040000c461091050019107940c03510105000644112003045a582c5084103040c01c1d00c4050b0481d000740040900d5040520703078002901e0030342544c000e44c3d4a005032504801642c2e004101d81040c410312000104000a0051580004c0c024401c2c00400d000030310740d41c44048034101e801d400000d6150304031000c41c6410b1300d420b401502400307025100f8185000d5440b0380c4528800c8044c0b40d1090780c0d80180c0402c0001c4050102c00d107005001341c444480740e4007091358004015102c2d0341c00c8503115085542031400701c12a00d03084d04e0500c0b04194400c642d01c0d04c00d42803840da5020310101d807000d04419607001041c41030890240c0a071200000d08000e0901c0711180c03a0340d01500c1c0062034a0204030740d601e0060081084803c1a20046029201c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 542777149 1250 542775899 542775913
    0x210e09160c0f3306080304080a0b06060f030720070f1802130f08010605030c0901090c020a02040f090b090a05120c0316060506040b0108041e05010b0a0e160f0509120307060e 76
    0x2080c0381500d00741d5101c00004c5d001441f04210a41010034446001603003c1000040d0350344035400036416000e00d1492881681c03010040114058014003141c2c0741d070020b90030a40c458080c1c0721503265904686d0049000844844000700315804001d0340c49010b003055803c015090a410a42c502c0580002d607101c080d40540070b8804110b802c80c20321440c0042d12003034000c0d148040d02180802c0f070401041c482c480c05941d035150100781c8140309208140c3c415500a1040c031408402203049405801c44000c20b550001c0080e004c81e584a0002603a00c01c07042d40100a4221045080000c0d8020f40001910003003e000c00c208103507160300c14698080100380700c0c0c680061281000000c3c4170071070b01444541c9061102e075400b07000100701510400115807500401e205000942403030203030b01421607800d0f25a0003007818080810301180360309000b807058004010003881480d40721070868042d00719100c0d0001048040143c030661381040c03070658076407480d000101c0e850910503540b54412100d0514100034035800c805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 542778399 1250 542777149 542777243
    0x9020a11011410080319050906090d0809040f020915070201090f09060609060302130e28060302030123060103091110020c03010b01050a080112210e09160c0f 69
    0x3c0c03000c0001d400143e0085003070400298600c00c0e000c0511720361070184107005c82c06030040c1c2ea030031084512041018042e840404001d103010403180d002500064842c5040103c1c854204030a4800d480c2c01c0c40004112074400c2000302c1c18414079074420307402030341040034811012803641c1c0d0180c5d0384001042c4a0030009a05032800400034661105500b00d1030405004003c100b407a42510040501901c5049940c91202d441304112040300500c0c001141000e05442c5401c90300d01820b80d8052400c07070f40240e000b03111404c269260440c20614200220f140c3c841d90360b01090803544a507004040340d034031407001c000003a415103000035190f1204840250059219418400030b034207081c007a40c00940e8007801d01da4144200444058488001400f504000d0b041c80800b003421701000d00c980d841c9012143d1001490120f100c1c200400030030b0b121032240e004144000200d01004d03880c190764a214800c642d03071503180240300c1c0e0300e658000c1080c41e4242d8034000c4203880c0c4100064072194280d0046841560b012003a2106 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 542779649 1250 542778399 542778421
    0xe0103030503041e0210140c010609150510090e13080d02072102030a0503090a08070503120f25030912020d081e220803070906120e0709020a110114 65
    0x15030000c0d1410180050100507110f04241c2c203d81b0445041131400701340c640101400358021040302454541c241500090300100710384c0019002c406502d1843d03400d5448070107210040d07140910090000e02d076040c042040c0c1d00b404410f00c6d004031901585107440302030740c0c85001d540d81081903110742c0c255001030304c0c1c000c0000e120410710710f004001001c14642c581000019450f4001c82c071022090004c00030020742408400c2c003200d692031b68003078010f83d101d03440c40c14055075039003000c2c009040d01031100b0089000800b144a00b1845018400510400c403a225025000700485001c0700c141030548803698100050406c000d2440c0340750065004241c0e80707100d444000c04000010301317640c61041c909a016a00c890307611880c0303036003d251180643c00102c07a000300400050089100500000e03404024005815440f0480c3d4040744c42ca541c035140e0a00012415a04581c06da0100308000d41c08040c0401440d049074000d000c12641c181042c500005c002581a030035200c07140032481042c5444800c100e007049003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 542780899 1250 542779649 542779673
    0x50603060c09060703030605030d08071b051009020f09010803211302040b01050d0f0203013308060604050d0b0901050f040f23101b020d020601090b0a0e010303050304 73
    0x21001411142010400199203104015100d8000d0301c1c00240042450701907004072006020107000c940040c0800b0500a200440c241c580d0b1000402a405420030445204a44000c040d040702c040c110009800448000905002c1003c03600041c60021040c00b0f665000042030090003800c0c080c40e0b8070000c504d10982040645440c86075404442c0c424008a0803140d8014030300107a0690b400103804203e02c0050300c40e801041c100200803400c040d5882c1801015401440c12201070804440c1080b00d60b40300002c1084c0d001000900710718408600c80e11551044001e95000070300030707003003d240c1500c0704007107030605400b008107440c00540c030350500100441c24810f8a83c060940714108595003080d683e100014003080c01d0180c0480803284c0318110fa462030f6144940d4840c410001c0305d090f200590030f8440070308440f8802c40300c0c4140b82e0440444460010800001101f5140d001c0c00300e6038284442c04005000c02200f03990400310400000c203000011144583c042c60003502c409451b0703e014a0700c6444682 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 542782149 1250 542780899 542780911
    0xb0f030102120109150515120f01060518060405060f04031e0b0a090204022a0c0a0617090c040203040804140402191d030607180b130315090b0a05060405 67
    0x200c100002e03007070509841d9616064030480c610200301c140b180442c5480454094118540c004007605102d01001c0c4802c00030318480b0103110300c900c00d581d20504080c413124001d104100105604001400b100c00c3c0520940110000040c0858201512400410380c83c1d0800c01865404010001c0c051090044a1403602043d1716005040a52039400c0e0b561140300140240c0341025064440e49404c007107607580c0d01a070301007441c5d8003071317140c140b050035114a50300300403081407001d150160009403246401d0140078002555026100c0c00902c5043d0705403860fa0003c018001d80e440e01945940e91110340d554001540140e0195000300c1e1124101601030501420450b10682b0480c41040100c0351062240d01070300701c03583d5a0400e0020141108601e04c00100c880078140e0b49030140d00f04002c403690b0002d00780700580d00c1e9616078502641e16030003034955078441c0001012010740540c3c02000007854451041c510b42a40c4800401c0b0007a46640d5040c0b5400c1c10b4585248c0039441d2010070038582043c5c85110361007a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 542783399 1250 542782149 542782151
    0x80d0e03010b0a0e190f09020127170a05030a091e060c1502070f0302010f1104080601050d080f1c0c030504030903350304051c050d0c20010b0f0301 65
    0x1c400b4400040b24075119100c0e54418201c0d100000c0c00e441890195140ca4104101c800d0115044003140301000704940392049000c60560108241c20010003c22888001c9281c0302c0f4100c89800d00d0b00c410854103400d104030226200301030742040025001c1c0042c0200440320380300c850840341010445103528105012032940204840010440180d03c2291a50f1407034104c0a42d00c0340010911000c4041c1c07090820140030031303c249650300101a415400071401410603d410080304808100440b0517202d60b104684940d44080c0c010f1010380741410a10300201d100d0408140752581c041c510203103507004402091b1620307400c112a401c2800e0140100d4210022514080055141070343c3e002e41050240d00020300042400001040075a0b00040340c8202116800c07511503080d89062800b5940b548200d40c12515805581950001075042003e08800c2141c42d40715182005081c0261074001d00e800100c40d01000317490a0041c0700c496082c000c481030f4020b43c4c8008501c090420051010350442201c600d406a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 542784649 1250 542783399 542783411
    0xa0e060c0303070f050c0f06010603050a09020303090405060f100306060905040e0d0822050606041401060f2d08040506090304050d06181a040c080303040803160c0c080d0e0301 77
    0x8003402204507540140c1ca403c1000000200c40801c540b07502804503499094400c0aa44114204000517024101d48540d03a0070b103e40e50341c42221600313595800340020f4055009010f51820b91800b5008640d001101a103102c00b800c082c64009808820b0391014500400da03940408d1040070f0303020b03a50f00060710094605000320340c0c1c030010362503650664000c810100404000407a03510040d100c851001045808100c02592149041c02d60700c80b64151420340c840d5240100721001e0064440000e4101c4d40d464640a107003c00b10300d001d45140300c00250440c94003007042d5003050911620440c080c00e80d45540d45542c0145000c2c03500916011020b0154001d5600c03c0c08100500d039900d00b9a503407019884000410032210300d41c80040940b0b03c691000301064580d104d012400a80c0c1804244505e0041000040d666a102212601d9100a5502900184c2c0400002d160360b002d46000100b98615464040c0c204106030b194200d41c9000c40c2c00c142001d42050110200255101072141d400d400c08070000c0043c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 542785899 1250 542784649 542784667
    0xc060201020f0301150c061122060915050909040807140a230a05030f1e07030e010e060d050a0e07050405060d0b18060901061703131a0903030c030a0e06 67
    0xc0b030b010502c075080c8140c00d1803010040881c800e1301404c0616074401c0c0c09028100960405800315008035030250100d85c3c44041000b040ca403a0b004400884000b0740301c4091017410310fa4020710140c542c210000c24030104020560054445040c41d9118034041c2c002540c0703600061601c40b0b07002c07000c03d0300b04c6090b03482152141d022840c17a15209041a003554051100d807131044050606221040c6400f500030b00000c030309061090000d40c01881c0440200841d13218000303418005010501880c400500003c0300d00ea04139920354040e405240b00318400a0010381084401000d100c00d651007100d10084481e200d0340400c0b13000300d04000c204040c20040b501840a85000000b161910000c10701c0500140760074804120f21407004941c2d100d0504411007a5006481c0680144c6d02808040c4a005807030032851701001c3c5642408400e45044040390700000c1ca13254980206030180f58200c003110070181c00c082026200c00e580400081c140c82c09100d01075a01c600360000c0103403011b207811028a005103c1084030410f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 542787149 1250 542785899 542785927
    0x60306170d050306180411090f010602030f0f0d02180a080102270402070b07050903061b19020c06040f050301060906030203060c07230f0706020111120a270c06020102 73
    0xe4007003841c0b034841e45a81d5040000340070840d01e261010000e680460a10051260300303050100e2254055480c1500340d20f800d600c250440409125540050b001803100b50721003400725004010f0140c0b5504010300f440300d0070f40007070100c3e0701003903c0e1618104480d44500c5030307050001000000340041d400071402d144603a03040c0c00c81d48806140088080c100040d1541507039446a040d40c0401c3e80007030f5000c000e850140000340c1541e00c01d11031180319210b000c0008601c00c038401203019140d80d00070300203801c04041032007000b40c0d6200d0304102c9003540500c09000c0e0440d110100540020900d4168101681d032502c02030500319002c0e030700010011801c1107424409078400140319504100c100c40b40729a6aa0b9030706008074902e54460540c05040c0c00070b0080e28a540000401001c00340039030701560400c650700c4109038222140000181ca44032400c2c401c0c3c607088007948040f503601125001c004189026450318006200650142040c1c182c260100d06105010262049102400043c0000c41c030384408450740788 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 542788399 1250 542787149 542787163
    0x2070b220e010b0703030b2b0f05032d0702181509070c02030625030e031303030f09060e0d12020309150406031505100503060d1b06030617 61
    0x90241110100c400800340d00c100940c10040c002006101c80750358480f1809101640002c60560000f4100104400d8030f00d41000110901074442d440c610b4402c0a003001c1142550b001181510301000800312007001c00d10a100406890340031607000c403d0030b0414115800000c5c1000c0c0d0a06000320240700650068075403039540c01d10f145200c42c000500e541e9500304a440b0940382d4002c5508154070105014426400540c00c08002d40300300c007a25241da80d5800024401915040354080e01c620304103111403558001da200525600c20641030b246062602c40c0c4100b032400403a44114006800d1076600a051588004128084e01292070403540309003100c4002548508504005822070200d205100d40d000e000300100c4030b2001c409450080000d03500070440b42c250b0003620410780070a00780000b0b0200701c1420030f000400d44000070034400410003022412075258000600c60742c3c00040c21030041000c506580c0d40c12244840c1c03441904403250500c0c02c0201130b1610340e4460751f400c004166404440310700104800c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 542789649 1250 542788399 542788417
    0x70f110c09060d0609060903080a0c09050405060f0406030803102711070203191103010207051009020118080d0e062805040f170c01210e03040e0f06010f02070b 70
    0x4141c107529144001402c00000c0c0400601aa103002c1308101003102d10b82000c0700f9540640c42d848c580ba52601c0425007941c034000710039800510800e8041c010352902e6801550844005014890410b40003070204088800d580c1090302d1096000c000c00013003600b22000003001c2c0c422820b015100d500d40035601480800c03150315410202e900d40c00c0003100b1000c594292080c80b50006c04507100000003100f0856403c03c504003d886500721400500c120f4101402107800d8150f10800401c3c031081c152031208018461380d6401c9042040025071b0014400c10f0814500150400c1c40141a07601040f81001e0300c40c40c0c1407080746004e807109100c4001490715800340007051a0fa05010fa075200c4858410442e00e51003140c02900400c41109008200300388650300680e100c05c403e0302180e070144c45140055440750818006184070120300100001c910245400a04544145400312400c1680f18271303404020100484161901900e01000c03c5119a031200f0303040c90075a103a0025009040c00c00344180d050b840b0300721107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 542790899 1250 542789649 542789659
    0x10f0b01080f0a091713350f060c0a08070e0d0305070c0b030a0f0609020403020d021014211509162708060c041202040509010b1305070f110c 62
    0x12407246643d0030041c002e60384503824184414600320000880d40049000f02106d000c4001d0118410340303241c03261071072112002a0740b4480741c51061044580320404010a00500806040c40d61201080010700e000c1c0036103203003c507100c0007070100c010404003009110004200d46c2000f000115200c40150019854141ca4170580c1c80350305003002503144400b0303803200d140d00000004100400e480f640c0b00c021000d9a8003010f00103030b0703074a0b21008142d008a000103036110240300760040c0185441c0442d44050300c03c5080001603981a80c0c0e00c90f2854000268564a08504003103400740704c6015558941c0c0840c0407890462511285000f28030702c685c00030081c0100b000c20010a908032401022106540302d000c00d20031107500c000030601045140e5034032a4410768071541010900160070882610140c4810032241e80c500c44041d020800680b80142140030903550340e9243e0559601c44203030a0191120250006c690380c241540010402e050500040c000c00085503003031004a80c020504c4c02c504181252 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 542792149 1250 542790899 542790901
    0x60108060402070f08040f08161401120203040c030b0f1918051603120f05180f091014030d09120212030304050c01020105060d0317040311011104030203010f0b01080f 73
    0xc0410024800c1840c003804900410382a502082040001081038070100c8200b070724166a10003250b9900c40440000e203110f8030208000f40107140200d000ca06e500c1805144c0366291651801603a000ca0340142e40a89006115060a00500100040998000c3c0c4101c1d0310629030f10341181c2c06e0600d02086a16940c2103a00c500038080c010059500b0900c01a4000041d244110243d10000710606003c0c80201c070b4084205607c100d910b4020180c00c5010035040d2a01c5140040d4550407020340040400002e03401600b510022155480b81d00140380700c1ea641400d09004507082240480315130003240d4034544203501c030607000340c0349aa000189800302d52111031b16012032070301840080c4811990741c2000249206c0481040705201c0c0c0007aa0000320310080e0006c21450301c2d440180000b0000032074010f00859984440405030041d055085607001e4081e01d8080e401c880140031540c25142e98012511001101040a03c00d43c5402e1003145081441c036002086840003010011b0009200148502440f4210b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 542793399 1250 542792149 542792161
    0x1211180f04020d06171605060301270e0c010201050907211118040309050d0b22020a08161409070503040303090501050a0c080f0702060a020a030b10092408060108 71
    0x50140d500540000784188949a1a8180c0754401c1c12998105e076241d100b404c004a581030b05a0301981e06680300500000e11b96802c1001d030203aa00d682c80040500c07072640c00c040040488240c0f26030314040c07030b80c07030b02030190b00c001c5034002400c0d50030140250003990080300c82001b03c203640c0c44004504c1426002003007c60710f03540c1007562204090310301c0c0941240d09500c0801c0c01c1070403489254441d83c8a5118460000d445109000301d41c94080c000400220305c940100b401800c20216034031402d500156509003080140d40031601501690388040b040c0d038003540084011145c03e142c0381001d401041141140a88540c00159000304050100820300074004041002c2c184642c102204158210009004a05000d801100108600c2c00d080001440e8140419541062038050900403c2070303030700138209600c484861100a41c0041001d0083c075503907000d0345103d030f01c0c1d015864aa400240d180c030410245860f030002c5283d01d074004100c841509001000d040740740c00c42045600a402803a0601c000c0d0303600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 542794649 1250 542793399 542793401
    0xe1801051e041407030209190b0a03050411180118200c070f030b01030b090a0b01060315050d060507140703050406030c03022512030905070e060402070b071211180f04 73
    0x240355104044903400f01000a0990142c004000b941d00039900355000801000051860202c98082c0e6401c91800700000300f0928402c0d000780d83c01074050100e025401c0c05a000080541c8880c0c1000010070f90101d004020101083c0d44c09045680c0354407003807007007280000c0403601040043c003414a02c960082040c043c1007104020f00c001811456150340b140c1500ca003003205d40340c1024070088030301c0070800000a40e40e0714082422028aa400f8030034244590030403800f94003810440c0c5c40309941c031003007450000d12039507661001107c8034040c200004207402d11000c01000701c0c44201c0c01580303404041003100000383e070140480d006c13504189000a0300224008084001e4421090f5801540c0304050784000821031980044200500c1428030444d0a081510180c09850700c00c4c0c40541181c0160504003d0010b400701400c1e4030a900910051a00d0441d40d2045a1854151401c0703000407a0403600980032001e51182070041e190b07002031103080010b032051220103203624008080c040c03207100402c600c59840d9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 542795899 1250 542794649 542794661
    0x310020d0b0306100e15010c060506010302091008040b061203030a20040929060a050c0a0f03110d03020708040b0a2a060506091003141c0e1801051e04 66
    0x500780c401ea810804058124110a8010010700c4c284140100e1141103120400c40700301b102c10707150340c48a068641c4409004010050181e070600d0340030058107a503555800c81d4419101042d03150710b13249060600b001c80741920010551401605000c1801d440c0c114008141c0340d002d01c0b513000205e09040100120005610414159000810045000304030b0014070b81004005010404103d034181e00d0a2100380d03200790000610135040300d010040204118400e1000703003984240c100c100d40003060b140d581c0b0210030203860400d03030004007180c2d0b000410390414085103192140528040d401c100c1242c0741d50903148603034400e08202e00070010300c3c040410700400001001031040306100000489049801888085886040350014a0080040d0ba24600800007a0058900b0040310b0f37078803403c5503260b000d0401c0c01e103208641403041d40001c41807102c15001400d0745100940d2001c40c85800c5138180081d0f400440207201041505000510158541e87c40c0b40301c01f040003503040000d03412640003040017050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 542797149 1250 542795899 542795921
    0x102060415090519110f0a210b0a05061503040503030f15030d0e030c010201110306220c0507060c11121c060f03110a03030c080306040b0d0b1f050310020d 68
    0x5507000d4400300c04800f0134141c000350086501d03403501d0007030100b0407500c504c1540b400b56214540d918140034035030022440703020f104030312520100550115108d41ca00000708031101c1b00c03416110410410325050100c4505221460f60424506600b03080e500d0310303124080180b1003a01200e140002030401640406094118000501528500c403100500106100681d11450f800f03882226003090840d481403007400701d07011042c1800340c19601c5035002c11514805400b903621401d8001c00d07401d1511095485180d142e031141d511682d0307640d040c0b80f501505807481945c003007061001c01e03643e1202450000c80c500c61144114020f0300c1d541ca100202c200a0491480c0b280d02c82d040c60101c2c04140285a441c025080c4c0303007d034403032035944041041084180d0255000080016554010680004070400c001d19088407004001266004421012905880740c00200307841300094101480404052215804008580203116948150820380841d9031540c40d5141864090b81c00500c1e94201a07040d40038035440c1c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 542798399 1250 542797149 542797153
    0x220b1204030905091302010e060913020904021b031c0504020913150c0804020306090703080409020c0727110a0504140301020d0e0d0f0302180105160c1d1501020604150905 75
    0x308221a5405c4200c20b003036000c80c00301d00310700058401480d00c401a100d96060041c442c2c41d410306440d18410207500301003421904580c0030302c02c8440e00e00b0300b1000380922400a41c01180c84580e00042034922500c9080200c0d051840c00c4213200258503103220a0b640040004030106841c011440e0080b1203030305e09502c05c0c2c10140760a0500c0b017141d900015141c0264001c908581d02a02da1a265a48420003484010840c0404210401c070b01040c9070003134001402c1000c241c0d0352080d604c1080c01c0624800702c2c21072003030f040c0d81c031407000224000f4071402362403400e002c0505080410426001d45144200c0c01f405520712141c45100e403255609404076011a51152824010748101d501c24558440a090002011656015601c0803981c82442a1900300c40810f1056016000c0d020056a041d03000c06041c1000424100460010409016043d001410303a283d040103040805003440107035a00c003405175814485404503000d2b05aa002602d0350304141c000030790128000d1041e00e0540180b260b80c05c014854 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 542799649 1250 542798399 542798401
    0x17250507020a03080309031e03070503070c15110a02100c09180605040e0a02011709060601050c0109050706050a02010e19140313140a0503010c0903081e0301030602220b120403090509 80
    0x906c002001401102c080e44038001c508284032403140802d8007007110b101000840600000b034940c1e119503100c102c014005c9042003021615040d111054401c0e132071000420400001d036600303801e0750400030000c0c4031414500421040d162607000900414181c801d41c0c00007003800340000d41b2040a0390103a40200300081c030420100045248240d100d5058410a9000c0781401e400a080c10b014501c10910500455000e0001e5690b100010740b41c0790000f07021248291360702c51012001400420003080644010f0301d41a48036880520000e094451a151986040e044a01600340c1e0040300551048a582c2c02a81c010030621140ca010f40f441c0148612002c0c00001540c0004089070540c00030f445011050310600f001d00c1c1c0f500249400d0f100518016800206540c00070004251642d020b000c51031104402400e80d0b4001d03d10300300ca1604203070010381c1d030350791f0000300f8804140341000c0400d111205140c48084903840d091840503d0f00407014074a910700e68010001d010540302c2c006000182500516800345 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 542800899 1250 542799649 542799661
    0x210e070906030b0708090c0402180910080d1809050402030a0210050904050f0405060f0a060f06020616020105010f0b0a0309020406060c05070905160516080a17250507020a030803 78
    0x14144500c02030f6030b03015a88010a00480c4140b084512a80201e0001c2208442010610000b540f219001200228040c41ea107a40c0b40d03218401540140c1c4107020701310000307042107851800c7c5a1f02c81e03103002c14803903140c54104403404540341c0e450440d011510001141c4d92140003003414051310210003580309990001741c80f0701c05c2c1c2003006800b5040701901c00b000295180c1c0540621008103441c00b40c03079036209000140b481c9002c0c000d06035000c0c6445902103690369035000640ea01c0101e503081580583c00c1b080803c52005c101c0390855501c1d074581d100a200c1940341117803181c5084441d004140d8a0031001440c1000f1500981100302203507400380c010410599030790760040c03807602d40d0b92088855001e8810000b40305135982c003800f4001c15001039504070006040310282d61990107410f9030000030b42c0000000022400c40c0c000340028010725142c0d40510440104460004440100118503844580103000c00303985641905414030951800d20783d5940c941800060310102c101d0b030000300042d07070000400132 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 542802149 1250 542800899 542800901
    0x1180b13080c04110405090709211a0402010f0c061e020c0c04061401121e0509100606050a030c020f0a060219051c0203130b07050403021f210e0709 65
    0x2180c1c0711030107845550442d141080b055690110f010021404107020902c60b92074540c140c140c00c05801e05104050070b60783c0449494a102c0210380303803105000f16100c203051280b203c03008100c00003c40c902145a161980c00a4050507000c2282401c02007160a080100a087c1d40a0420305040396003281c1c0c10440800210069405400382e42800c0c0529102110a410b05024100644111038240740d80e91481100458443c0129248405402d48825450780840c541602d000307000d04407040003003014900142060325007848102480009841c0c95004c1000e258080282c50424240303250100343d001c0840812480d0440440d230403c0140581c0b440c240c00c001c5c40c3c3e40284492164400111105103100a003654140108000c04450807207521101445520ba54011540030135802c03803007490000c482d01c46a00c0f51000329210001b10390000f42c14402d62400c4580884038105550320402c901500600050041c09403442420035440511190003086c0c00310b4002500c404841c404a80810f0343d6881030740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 542803399 1250 542802149 542802187
    0x1e0d02070c0f0905070e040c030f1e06050d0c030314040801051314030f04170307081206030601210b0703110d1b0905030a110d0b04060f0501050f0307030201180b 71
    0x10070040b102000000c00100c035001c0c05110354034540b1000c50440170101404003500c0d03414101401c25940c3c0b403814143c820284505001003450301205125046c10301d00c207004447e00b45d040340c0d100b800082c0e0410f000804544c07040c0c0c107881d811307e0aa407079000d00c420101d005002e2500083c00c0782d42000b080148030400e20b0502c06816008070701c0922869840480580c5070301c40c030820040903000c00c0000380400e005580581400c81c2407542120b2400806898007141034102407a0391400c070500e00d0078042d040c502000f81c24013401c44a10b40105140004100a010144c600c20080c5507144c407000040d142c90084e07200c98242000d65442c10b65580c1006058001030403580d21000160400c07039140fa56181c41501d880c0141c03100503004060540e00b64454100e902c01c1da40c00194401c195a03500c0b00080c007800512801580304410202e1550280c0844006035403058011601600381c21660000c19500003c15000322502800c080701c8000110400c80368500441c1c0010790f601100040d000105507480305d03a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 542804649 1250 542803399 542803409
    0x302060715271b1e060e100e01080a06050a06032307020c0607140a1104050912090f031203090f0d080c0409051302100503090118081e0d02070c 63
    0x10024500c962100b480800500b1140010b24042e0b510010000f401851069000d844851640200d841d80c0d082d4080c6450803c900b54600d100c2c07144c0042100c16000441d0b00b04c52103080b03801900d60b03c100b0070001d01800b05101201c7c10803403054040360390f9030311603070245014210140c0440741e0952510700c0a4007600c11400e9042e0020843e50b5012005d5885005040c000c1c680355014000418408040003282d0700108400d48035803400700c2d141c410050040019141e0184141c01e005400100c8804100c00c0340c00040c44102107805c1091118911480202182d1042c0d00451310741c00100c0030000424580070550701d181390006000000e0004806000480340c05400e0f000e000c440301450141000c91f19004152007a4890f0740f0207000c1408110b03d80d401030b80d4010003201114203809540d40001f4a084600b48403240814800010b11900010a0045c441d421a54403e00202e1002d035a6070f200c114480d02ca001c0f10b805401e0550303810400c190b03104a6400c02044101592075403510300300038001084e503200d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 542805755 1106 542804649 542804651
    0x71421071106190c11061513021810030f05040602120106020304140418050a0605010806061c02060702031204080d0f0f020a030c0312060b03150402090604060311040302060715 77
    0x851040c450403041a81a03010b0f5800e01400d003002800030160742780100507a6a040304240d00e0007103466002d0f41e07003814820082d1021001490015100306106003020140428000c15801424520160035020f0350a66a02c10050703070b0f43d205038402c041400352242d049900d1407a240e400040c0030754940003200b22540720303552102d0070481d03405001c0342d0b4181e50302c0044c4004c0004110301640850240c3d8000c805101d500d4021661910b1074100034855200041c00c041151401d1102c00b05c1c08889945440d2600e803507190481e0de0307c8002ca03d04001443c2040801400c40c40307400080d5005400740c018216400d440c2d101103c502002c00400c1d070510800d090048801141403203440d00402d640c4190903140d05018643d441d8070100a26424400e6005100c440c0d1036940388400c4804403000381c01d00090b010b0101403003100900666002950086000c11110f003805148050144040b00940c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 542625899 542805755 := by
  have h0 := BRFrame.cov_init 542625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 542625899 ≤ n) (h2 : n < 542805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
