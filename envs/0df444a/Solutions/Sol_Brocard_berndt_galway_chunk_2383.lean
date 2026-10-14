-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2383
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:45.149707+00:00
-- url     : https://prove2.me/submissions/294cee7f-d343-40ff-9486-03452d90e862

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 428417266 ≤ n < 428597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 428418516 1250 428417266 428417287
    0x504270b0a0b0d020d0b04110a030c0e061c03030b03070b0c011e0c020a060513022d0105040303050301090207020409211103032203020708010c0f020c01030c0207141203 74
    0x11200c1c4078071008141040a8801e80051281842003100002d411641204480c0045840b001d18658081d2040140940045181d0003207403100540d03034011920450700410034409224003043c40f81d803248050391840b140640c001002050b40040450280a0540d030742000019a00d041c04030300060704c16515001d0b521401c1c01c2d1058020401400e00440398071541ca0000d2050610b4042c1c0300c400b1030254020300e00e8042035200c0800415000c0e1080c44840c4100742c140740107840b42d001c03081c820040480ca15084115030b0000b0f0083d080940c600c581004002c00041c03000030f4010741a2815101e6178980140c44540510104000302182800a40480c0c088920054528800107500c140c5041995a80c2074000000d464265070b40010b039051160814041c071a042c5000c003001c0c1c1568010700a10480394070698079840b803421110075540240016080078003c1d01d481d0b40401402405100a01e002c1155a282020003034035000d0130701904503110207540540e802c83e078903400c406000b99a5041070f40e503608c41610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 428419766 1250 428418516 428418533
    0x504030302061e16200606120a02030703120507020a09050a061418040203150106020c0a0602060708150f150a080610080f071e09171204050427 63
    0x44114014410b40b0001080b080d00300d90445410301c0b10000440c1c050711400070741c65120035882c1200042015062400304001d10345040f4420f0994803801420607401d00c03005000400350a1000c84c141c2c0ea01c51a102001a100040c40004594108043e8801003030108000c9604e0b100300032000c1c0d030008208002107252041e079400f190048031111410081240c0e02c0010a840b800c5042c03c42d9030120201c445107840c991001c40040c3d10900c02429100030309482003040c0010103081c0c000d080181e00c4020b0034651428901115000307030030140014030180c501301034001c10203440100344000340c02e0422460203a40e10794115540d0f400c1130003051045d86e2884150214201d4000c07500740d87c0003c0d03070080070940b1401c0114842450f000350f40c1e40c020090340c41e225000324168001d0140f00c20055554042060301d8250100d0315405501e84d560880c05034600407448201d18188404506103401101c00001c8906d64001281c0440300141c80110b441040c402c1060349100c80780c1c030591681c00d141c125000c100241c82 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 428421016 1250 428419766 428419769
    0x3041112030715180305040b0a0905150a020c090f0a2a080609161b0c03060218041109010219080c0d02100e0a020105040509060307030503160c050306040c030305030c0d0204060504 79
    0xb103100700070008450113150090950204094003141c0c080000780716004800008200044d1039080000380c09645070003180300c0c0a028003041185003404504002003c5c0e051003290500041200d0f408000d003008a01544000c002901d070621255550309000302520a4942c40f601c070b01103000c1c8410090185000c050304c9080100c50461013440101e00240307030001c98203d0305001000075a41c080c80c441810540c08070594a440301a00c45c000f460100200049003070000745034a0a01c3c0440d210b400312854140802d0302c80340300d40e07040704100900405032103990001e03480c114003486040c0a8101091421700026a00c21a02106013900804001107840364000511004440d081c2c081040a15280d5480d02e444000d00d4000a0000306c081004004600e0021402070f000359009003560760256480d0789440c5154401503401d03e40b000d86901c0c010521031090120002080306a000d802c092419540381281d031350f090301004007440408400314003400318504c1560700c01100c8140440d0340d15100c810162064016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 428422266 1250 428421016 428421053
    0x706031401081c050903010f0c0e090105091911070507030b0109090305030a1e05010303090609050f09010b0310080f150a0e34090203090d0206040305030411120307 72
    0x900d4800d21088440d68000c5040712000d0000d006030400004200c031042816001000412506100f40c428641d42031040100310b0f82c5a0070001913000515101820106032426a940304405260040000e6103a01055661003181380b02d201403040ca15032441f900a12903210001e50340c07a4040b5060f000c204c0700250641c00c3d40e0084840121903a41e031a0120291504070710300900155040c804190600c0d0306801c440c0c10601582d40d03800c8030508a0240d00d0856400342c0c402e030f0000d440c4035410400580c200e8015005003c003960404441082500413401001040c8180b034040d000010004030700540032036100c0003a040420a403413122013240e20320b980e54080c070626500c01725403850105007040c040d4070501001740c0710900681f0852035141722081c24244050040400c6421081c20254000704418100c030140180381c1e40103072a810b0821310f662a120b503010180f0255401a014040441d4001065a030300c20750012002074200324240104802c0d0540c00404d840b94400401d0180800c400748800344a420741 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 428423516 1250 428422266 428422271
    0xe060103030806061908150907091401030204051c060908030a0c120b030a0209060604090216060b01030501030314030603011104061106060a05010f390302120301030b0a0506041d070603 81
    0x3500303000c1260601c59400020803c208180ca5901c0640c0980318040e800071a88203111050030300c100c0880c042d180102c4010f0004ad42503001480422011a4070b00744907002031804605107800d120220b4030204082d400000c078051140c80e08002c001d02a00f05032011070344403413040e0716030074003820960203846d00c00d02900109003800d503200800a214400c1d13544c00e040c010b004006c0b8103156001d02001580c0900019001003017084040740c60705080c001041508520240c4130078a00003402e10700100c4d4400c0302d82c0703810141000010404268880c00a040071a0404031107130ba41e46070714001174010704008500c00007441e400328000031581e400000b0141030061020a03160f007542d62004100400f00301d03000d4240402d83c0c82459041452080c200b1642080a01000c030b18a01041c5030700761608440d45d080110b0082614540030100741c0d05110181848807148159403c65056544820074208020314010205544000048103541c4036000000600c0442c1c03001040403030600c03449500d401341030085002007030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 428424766 1250 428423516 428423521
    0xc010e0d141801080a0b03010501150809160b031906030c03020f03070806011806050a0b27060a0c050a1515060525050f0709020417030307210f0e0601030308 69
    0x5010021074468a6032505402d45180700080107650a99015120204880d43d400c1010b401da10300b4400c0034081c098030a03010307000d80070018008101c8030700200014610f0300304110401600080380001c0d015a400c1c80c0c0000d40341d80e030300c410700e01595882d017914022031420448000107001c000340b04841074170f0080c0c039002d007403032688000d16540f400e4511440382682e10200c01004007440b1071041790a4210640404110039946000007284404542c125040b0450005142100c0704814036031800031080080840420f00c0d072a40002d592409141103c0c018055012100e8082002c140176041d04140d00400703c20b0b0a5644401303103c002c1020041c00e80c2d10110075080132032800d021f40f0507103180f1942d0381940350310001c1c6100d4a1141d01c2c80110300f119180f01e40c80d120034070791000b400201c02801e0310540068a4501c2e0548a050a444140031044640c0041040c80b44c00c59001102d03d0a0103001429401c484040050b080b0080c80102c0c030140005140c019000595035000c11801d040340e020707030b5a203212034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 428426016 1250 428424766 428424797
    0x4030e060d0c0909270b1012050f011401030f020105210702070510020304230f060a0f0306150c260403110a09140112020a0909030c05070b0c210c010e0d 67
    0xc00c00c0c650007174003a040c10300c0d130000090b522209280c0d0056101040d0102d903a9101c0c40580c0e00311140c0c00c01c1715181c100d0894081902004d1099000300c1f0044c400c00c044a5146440307800b001070b03403054007904000002946a40550150002d026400c8801e1400c0059140500000351501e42c04d00a041c4078000380b161406685100006403002c0e01c000d1021400c42d800e030011485503c581c1406201e0308428801c8003007429513100f201a01c2c1d04c803010340343c455410841c1030300101282e420350401e011201c0c8000b8004941640450200b2240c2c4d44614400c00001c01b400030804107030b041380d0246802d0b00d40050040108451041303484181c2e0825220000c0c01515000c041041c4d13203500307070600c010003200c6004020035921041403c400c41d002030a00c454143d140c100d42d0007550b480c1501074010405010f03868041017410070000005041e18090a42840003e1454548030540402e015100f070321100d10802701e20118000710391041018200030404400c841c0782c140d840e05d40602c42100072070f4403800183c41c03d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 428427266 1250 428426016 428426051
    0x21b15060415120218190b030106030b041202070e10050102010e19080a05220302030c0d03120e070f030b1803090f01050a030f111801020307050604030e060d0c0909 72
    0x31a40c10016000c4540e082c0203020300a00303240700069030b2041c104172210507007100409019009864a1a0403000807107540b5040041c1e4585204840c001e03807500c42c08001058070300c40b030780340c0155000720080f404807601c510803868044640c0081c0504131100c014407824101c41d013103440c1111400c3c1c000b07010594508500e1500c81c2096901201144400c100600005d80d9882c01006a81d01c9400c180e8100682c00c1d00b0a0600c0400301a01040058012014415868100400b0501420440b09035040340059a40286100c5036a18001942d0303131100694844401c3c140041005464050801504144e50341071541c0030b0001031740c103a40010b007051810390401c10007108607100d4541c09011802039200341801100c140e0b200c840c020003056a1000240b030505181e01407401080303200d08890742c0700e0380584150341d12100a5590340341035602c200441800079502051045d80310380c15041c2900d000070b0040102c0c140d41b0590524030742e820b10b4503c81000d1240c122445000703440c0e00980402000c0398542c20803d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 428428516 1250 428427266 428427281
    0x6070b070503092406060a050c03030c03010501110318090603010b0301051603150e0415020405040e0d02100606080f040c0b0a0c060b0d03050d050a0b0a08060a0b0d0c090f021b150604 80
    0x130310b042042c006012414581c004016020301c5d0300d010f0349030007900580340d402d41c2c00c2170395070b102c0c07036280080100681d60f40003c0300019038038404040e52501d08004990324612911a03006402407001000061036a41c080d44032221100f0060001e214900e070140c81c00d051440454407003004649800c400712904c2d002c20000c00d00b681e9104145800640341c6482c0e50790010a80c428569441e6003c101c049110344403401007603a20031070500146080041240301a05010040071072500c1e00d850501c0c1000150340c0149407540002d80a500140652030f00e00b8040401d6003150410300d100e20000805540300c5610901003507040d40102c00c104442144101000b03504414181c0c040c0c0003a0052101c41c0c41114bc80d804150006030002000075250a074001094040d0071503440200c49400110030003500d12400d006d902c00882c0200e40014103c0040d0396480058807450103520f008640e11440411041515411910b50400c10090074007041018800c4603621900a92210220b03410720012032501e040c10b000710070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 428429766 1250 428428516 428428573
    0x11d070801030f08070f0503090901080309010c020409020609044104020405100312050408100c020d05030c46020d0f02030f0c0102040825090b06070b07050309 70
    0x8603035074696152440146602d450035030f62900304003e10b0b8000f0784005208441c192040300516241e940c2d0340d0401840c0134050b031040f8070a40003002114050fa90192101c6845a4111030001d80360f81d150000c03d0440c001e41da4070030b030403e14115040800740c00009050300005001d002090003c0e41040c0b05240140050030b22401c180121000300c4c00501d09034004a51000a841c0712040f2190340351111030090b040e10004e607010031000607080c418100c080c44040c225400006046c40780164205e03000f551003031182105000c0000200c00714010807034210480d010905081c1e0b4085121010085a020014150700700d10b0004040702052080d01c0031550342560052007130b0b00034180c050640e4405403415130080484104500040040c803440041c0750000d08503402d82c1100044c0c07501e040c100110700e001c400091800b511410200c2031401400000009400d40e040090046089280c150100d440c0c0d010f0450001d00b401c0c0030078104080e03282c0c4480074512503040041110340c40108034100c0d1050300d10711103451 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 428431016 1250 428429766 428429777
    0xa0203030f0f070c0603051e01080d0c0c0b0307050d05090a0c05040e030405060d0e151308180d032a080f031b04090b1003020a05180109120605011d07 66
    0xe551001d8010160440c1d1588a40c41e602e400c029a50746540409290000c3d004a0340e904140205101300360b142a510900c10003002c2001d504140005039581c1c0b03408484c1c7d00b007180a5498400700540444044010600c2240203612410700c0329000d0b000750000d4120b40195803520f00001d410040000c0c40700040354101c4240b1000754145030502c0f014001f401c8803041e2034481000002507a44400c00140b041e0002e2480002c0c800c1c0b40400d00324107014136002412001340070b034010b01c2140d8400c5108020100c0d40818010354540800d00d8127291031601103030855102c0319096108082c1a000a26501c25000020030301c08207900e000f100d2410820035a82c0644030410501507054080b200d0300c0159041444601907412401e41c2101c0350b5501d51094002907103098456484070414201240c814812040034202942407080081d0020000d005080c5c0b5042c40e2150282d1400882e40a44920005440c590520a03105441c2c1c2c10000c0150400303104180b01c0950000b032100c1c140e602007030003134003880c00c1b6601c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 428432266 1250 428431016 428431027
    0x210170601030e24040510110307050309160905072304120f022106010501030b06160311060a0b0111010e060f0c090303040314011401141909111b0a020303 68
    0x440040c4220483c903203103480303000001c40c10348200f86950031082507064000d011038074103490041e080c0400b9101c804401400d212110b2138046181090f83c1e0300425501d030045d120f80d10f030388020f480c103010203d0b4460554001c5901203004820ad03000140b040c100758a4040341c2030002484104011402410701c22300d803506102c1400030803201498005000c6c0100e095804900203600003800e0007040000510000a41c4d1004045a9106001450041000b400c0811541502501149091103034010320043c40f106542e440b010140251581c0e044000311204440c0c03a4075040346410010010f6400f107501140026010210860050266070510607203e8081c2c2079586456103640005103014210301c00c24041801038400c0c9883c1000604010750058502a0112008400080c2159010b0304450301036002c2000600140650b6180780042d81000c0d81c61440c9520541400c00a000c60360f0040b0540c0c5003801c0d400c2e01064103582c060a080c0c0918120003200040c0408034503070710203920034000d4158106003c2d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 428433516 1250 428432266 428432269
    0x31806042303040515040f0b120a0e010f0c0e01020114040804210f0302030301030b1e060105220f17030a02060109050604090f050607140c070506030a09170702101706 73
    0x381c2000902401100e06264942c2d00191041482d0307403048240d8000032604002d09143c1144400c020701d40700862038500007842c1c9120310b0891f00140345422045d110b845002d0001700c00d41c00f1748442001c60030300b084145142c8500510052204552500640c20030f900c51603c100103000c101d0003507038020001031800d407404103a4444c03440c2c8064020704400711201d804002c100d00d0181c1d180c7c668865405156070b50f045141c054800040035000040c0c0c45413004100c5c00c221090005544c00903030074200581c64900703412681072075039014555082d100004510000d65007912449100a8489504182d604e03402c4404003250742e4000c04103484016800500100000d112541c00799410a90251011622501c01c0c1c0781c41c00b15007050300040301c40303030f000104205140d48d005000c50035400c1081c402c1441c0049880080d580e46400e0701407217229501c00408141100020f070310420b040c1d40d00c000700d003503c0c54100f002400c6036044944241d005012001403107003040c0c4202c82da80000d0800301452038880c3c8640c3d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 428434766 1250 428433516 428433563
    0x4031a162a0c03050a060203011d04081c1e050f07020f030a0309020307050d05030c060603030f040b0d0207060618110a0f050a020f030309070305150405030708280503180604 76
    0xc00362000300caa0b0901102140c02405145a0140036400c0943d40c5e514014031280408888407010074031014020510000810901c21181c0000120740542004181004070300014100510303880f000c2c0080d80444401c002e090b4007e83d100c0e0b041c1501b440702c1c0d940c51500580e00d0300c244035003403015038104014002d5910b0180c1d2090122500213000c0721482506e0f040414180d00d10b824058600d030b4008141c132440794504110309644418107034007650400080d41c11410aa0003a070041c00704480c00822441c00c103400d50760569602036044501070003503d50300c01d001c60700c24865104190503a8209582080440184412508030041d80e0781d41048841141300100c0e01c1e81c0000324040e04600400800b044011010000b0b58000d003500c2c000380006514514109203080c0b4100600130703285031440204000f040307000c010303180035a40004825541d4a12010502c2c19000f4032a0030001441c000d5550700182c80d442000356204015911724420b48050b09190240d81d07510440d001003030040c06440c1a54209500c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 428436016 1250 428434766 428434847
    0x30905060a02150a1a0d0302030406030b150d0b03060c03040b06010305062826030415110a08031806040c0302040f0f1a10110c01031104031a16 63
    0x1803050300ca101103c1100f200c01c0c81802e81d4040e840b542c549031800c00500301e80590044525040f06c100b107100025a401035283d0060780b00b460141550b50365401411b480300300d4031259400b60042e8541d524000b41d41002e0007041200440381c000d10481c000100070036500d5003183c0c010b43c2c04c00e002350701d00e0b59100300440c054040104001d0b001060245180c04900180301c1c81d4084000401c0b03503d151604085800080452507070f129078241d01140e0050340b00800100031070302941e425105440c0c2048030390302d040e0350715800c8032040c0c41940320b07018440d82030064190185001c0e0003a920700010044041300a286d840b54145c0d001303050f8035a40f00e2304000624099000704000002000c000ca17082001001c0141202d10380c1800e100280d100014510080c0750401c0703195205002801d2035103010f030f40c80b4180b9948021846500341450390724070b00700c90f0384000e1a050728004d503405144400c1402e0b002c0611006000165421503007440c1c2065a10001760240b8481441d0105240720034050113140070100c0480000e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 428437266 1250 428436016 428436037
    0x6060c0a11130f0504050d02010b060403120203160b0f010f050f010c021c1104050609070906081b0d0e070603061202060315120a12020d05030f0411090112060e030703090506 76
    0x1c18051103100c4442d010f00007244119040c002030504d45403c060742800b904c3e070f6a400459240551100d401d42c1e90106441c00d998009034840c6903804045820303407551080204031001100901098400c02168000440c480e1012401c406c2c6540d0b41e4944402d40643d10f4011a0b5002d03100408840e90b0754480c81401120f50700003000044440d660540240e803a184030101607428011107480d003120f508040c011a03400c44401c1e00c00314902e141560000305422702e6801880100301152011403680071b140c0b09544008441507400540c1c0d000915030709002092001120455400307048000296680641308840c01c030b8101529603440604682c1c00c10206a000400d501c9032000340c0284120640c031002440340c00400c82c00c1c01005644803c1c14411810b800a801190456016804981c140b40e1702c4400e43e40c0110700c0303050103941910303146400c503081c04030140c07407542023000ea1300005032410180c00700390090703805050308100340c1c4499084c90b51030340724030800580414001c50040209052038001030009080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 428438516 1250 428437266 428437279
    0x3061409070515040b0307030b1c2d0201050307110102040f060e10020c06070203030f030703021308060105030a030309050a020907091e0b0403140f0111070b1501140904060b070b070806060c0a11 85
    0x2207103400520b081482480788050b4140840110040040c0c10000807460502e002002f40c00043e01ca215140380811880020304002001c400308202c039004101030000407140c10000d41d01e4a450b5280d80c694005180b180000044011140c420039007400d42d144610300c000c41e40501f2082d806601401404d51046000301e8243c481000030401004a00000c1d50049089980c0940c1c0c4410307000d14100c0b940c003503820000c0c050300190010009542d0000e000600f8540c18100410710090b1030034040e040c68070855001c2c2d04880d5280401040c0c950080d50001612640c1a1150010302816a41c031041c3e05207000da040000b00411080c4017049070032034107a591682c000c0441ea044404c2c100c81d00d080d14403c40104840c140d010590b02c1c00c200384500303142c1d40404035148905a54914000081c500050040500b950510020300200a40c0351600f00c000940950710042e039461740c0f1132404c0801c1800031074032140051180808282d044c81c2640c1140c0041c0d0840c0300414a8541d1030f102e107071104d00d412000f00d51254 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 428439766 1250 428438516 428438531
    0x2040e070f03061a06130501080601030906050708072613050a0804090f060e090d03050c0405030d050306031603032114091b030106120b04020a03061409070515040b030703 75
    0x80309900d0314000b440c49034502041e4411380071600300b05500c06402d024424a0309008405a115204111504458007464a003030592941d0700140c004040c11f24000d8174813070610b010060075980040c0303c503024045c29520801a05498036100ca8200515000000422403c20125074070f100303120403041c6440e0152041e907440901c01d648030b006942c410340c010161140c03514100c200442d100e10404000303110780b144000452a2100c001515840407503040010306030340da000700b03441011010664002d040003400310341c1c00c94040000582180c00c00c4408510900c100078600368000b062440315011a44e054840744800d07c07008003110070540d03612054000182e0345100b00540303046650525401007414002400041c0c20481010701380f03c00c80c0b40c20500903070404408105528a500e80c00035038a801414030a180c0e2160310015001c45416840500000e080c00d0020800f810144080c038000d010b26002c45100795510401d0180740c480c0c1d080c420382000340c24841000009070385001181e0000152030009040d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 428441016 1250 428439766 428439779
    0xf0406080316080c030c0d120504120f0201060504060909210f0507080c0601030c06020f0d0e130212040803010f0f14010e04090c08011b0207030c151b05033402040e07 73
    0x50308009911005607000541f4045501d07009440003404024001b020f10451506844821684000300c0c00c880400009a0002c841c1b07603c00c0d407009020304002801072000a54075441100039027000e120a81d40741d0000800800c5c007401d4803854500144064980c0e1041d5101c4550641301e41e0082103003034600550030440442040800c2c800117001e14801c413001e00040d800d04000920340001078011038850b82c0301000000001c0d4111684201c2528110b03040c3c60525547c180a401034002d4054003404019070070b092001b00200c030b4014606a4044024001500d80c0d560b030031110140d02e80c4940342003556248004111548550720f8400080f1000d400070901082a540d0800700902d00d070300441c01a503481c541c041c55001c00d48210707007481c3c200d40700400205041d61210f4015a0f210b1042e1824601243d0401025a015440103810f000104440003011030b031a0500319225400014900c54400001e8400c1e0b000c0c00b0b20649845503404008241072a041081e8207000c000c20303010340308103490700c0380800c0040e50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 428442266 1250 428441016 428441023
    0x606070c030c0303020a060c020f060c0307110625080c091e0315150f01020c040e010e06090d0f050f1803010b030115080105182104050607110f0406080316080c 70
    0x2144290300a01d02041b4509102c811589a4030506007150807840381d41d910f111000502d50713005481010541e0381d940303543d081900d1034040b021080403140100380130440e440c3c40407025401d10fa11414000c0e01200003900003251900c02c22592071610301014003208915042030b05240a90083c401250340d50f00750740310000391610300a0000781c0c1d50401c03548200324030b00b0328091250b0305402d01a24000180e013420400070b9180c024950300c45026035940c1001e003407145025040450301d45955004e4403101e00740314101903110f247c410070820110f4100d000c3e9801d81845a01120480c0203242400c0381000e0100b4031120070803003400440c4d0b6142d900c40c070700c0d0980c680e020704c030707510f80a038050b64070f544000e14280d44103094840c000c000301000d50203011400040c0002240280c5003221810f10701c0c00c020b0b84640111440e016942095800450218101c03080081032100c0801c00b5030211181c0d0040c66440c402c000c16203d042c006e40040c1c0d001030010244454010100b00078051062100d01c0c00d0420000c8002c2c503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 428443516 1250 428442266 428442269
    0x10c021305070e1903030c1b0e0108070812030c0913230a060b091c0c030609050c0a0f0506090102010207020603150a060c0c05280e220b0606070c030c 66
    0xd50794070001d1000403504040350303100c2d00b003040c1d803400c07038480c03002c02542600c0c0803d01c006400d116011510408009095440c0c4070740240c1511031040c2d054032130420b5140d8010134010158a0b04c151100424400000544c08580080800040345969640b802c3c030136840d00700e9002c00345c0011b03200070380480c0400c041c000c8d1450301c020002826888159100e0b45116a1009001510410310f8a9014403000d44c0c20000c850035400181c401d420582a00c441e200c41d0549002d402410201c1013160203c100019070f045585d889000b80100c5042c004410200582214144500010001409410001410f011010300120801400014100780c56a000303c0c00b654801c40d03031450380c03002484051071249008006a000f400d46031030002c00b91012655841298981030241910841c0b803100c440d40b001c10004181c0380032411110b40c4524140d95a0444d02c8942800d0790031400ca034040c554030202d9410001680241c560b0041746980c40d0362200814070805074480c8a081d40c0c03182c50440044041003550700f2540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 428444766 1250 428443516 428443549
    0x60a031121101d0304091107050f060711060601020a0210090b1801031b0e1e0d03030f1802090a0f0b060a0e03100203040807030327060e0d0306180902010c02 69
    0x210500c4105003020884002400404003020407030703080f614040c400010b44090300c04c1840e00156120a0981400180c059440000e1042c03103813828035280c2d8071000c51f100e070003501a03465039410f50701c6070113085413960b01c1210040d0041e440455942e0240c90552030008a50300c1c50b0401d003152544030b0b41c0c085076990140c80300c0000d00031810703030301e0300156410721074603040d00d40c980b40120071551501d1008200c41c00300c0a0940c41413640410000c2c03501414503230b0104c1e03c5d2005002000c02185031401601400d408501d03140c0b42454072028005007a02a80003080407580209501204d503117083d070760300c000d0180d0310690340d596582d0390150b0101d07210381c0010700d0209455102d11003082070080c1050b1410501603c2690b6250060007440b0024680c2c0080d5044a58075042c00b084801810100000080b58200d00003d003001c00381c40745047c0199030b840f003d0340082c080280d550410458000b68148d0b181c0b8480e0032000000140d04400309482c03940203003941c0e84145040402a0416000103c480d40c48506d000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 428446016 1250 428444766 428444773
    0x90318010908120c1605031c1e0809071a120a0615090f060504052d04020d0209120a03081f03051203070f020732060c0102030105030f0303060a031121 66
    0xc042c0c01400c21181d2117607980d514482e4030300c60074400403a0311201c017a5110014680c1c20440c0c51009402451030015402402880290320a03801c84c00030080b036804c5c3c03524003150280000104030108160206e0041c00d013000481d9140c980308210640320781100411b0003c0482d0f4a15000c10b4010424442041c103c119641d298861404d00c0c0c202c401c0c0d20744642c04003052000c204001c214035121020142684007611070a05251614400d016018403900c0c0409907008d44000354031001001160b020344000074069912400510308160060340d40c0302039280c00f6000c84d0001d80042d5014442c56140b44055001c4a4594062a80c0c2e81c0c5041c5018000d801d100c92400e800300c100200143d106031124001c0340b4601c0184000d0749000703640c9c814401c000401005007050108040204260101c5200e200c05003e800c0b160340304070000480f4000d400c00e0281610034081c081c130b5549400c1001064a0084c203004103003c812078503641d905401120207084286c0c02903108900c1c49107407003007001d100c0e00320902c15019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 428447266 1250 428446016 428446027
    0x80f0702030d0305010311060f0c060a020a0e01030902060d090510050a020304030f0c030804030f140c0705031515060306010e0301022706041802030a1e0609050f09031801090812 78
    0x1014248001690300c001007601c0d00d00100b0220700304141f014414101910700390343d50070310070b28445000e1045e010304a0751440b440050000c101d503182d00800c041030060b0703940952500a60011010790b5040280a580548140041d00e07041825034425401d5900c01c03802c4515226100f0b4881041d00c008803004512250b01008010515403c0801c64640710013501e814006219507643c090803804000d4000703420070181c0d601f154000c1c2d015524100c20003a0a1501035240d503031000c05182d80e04034900806000c2c2c00352030680985240c00689160080c01d14000c07413908044244140201c0b6000105038034100a10502511860340b000c0c03000780351541c100c1340c0c1d0107810030044182d800210b000e2004603020303940411080001d815400071440300c80101d180301580c2c94841013035640c042d00b0254035041c00350104061440030618a50301400407900581014805541c0b01c3c4241030f20030f20100e40b14901604104194011014109064104140141040c116075038440750b02510303000000c0d840c4014580002003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 428448516 1250 428447266 428447269
    0xc0304150204031a06150d020c010e010606020304121b0e060117160e0604030c06050a1803020f0402030a0f02041518121e05060a06090e0730080f0702 66
    0x200302100c058240c0540c60107155956540350110844081c04114000c040410001e80d240c02034043c54640420341c05440d01e00d6840ba440080d444621000040e62030445280d14481d0b040c007c3c1000c4880a80166040c0343c902040307420700c0082204100c50031752400a251b140d01002d51242c201500414034289000e240803000948aa1100d182040d040da020004001410018401c002852003040c64203012001c490804030302c150056405c01440b54202c901e01203440781c0c4c00740c040e11000510742c0d00d440c0204203141c281c40c00303060280800394100d0320020650703404e0704140c2c0056030040d040503000981800c034100c01d101260441c0e040305070b19440300e8620305000d5901c1510b10f589a00c94110001c00140fa01c0b400d011182c00084c002000c4819584010449120907820b144c0004d4010059030f045142c018047c0005040c580605600c0626102d218044010f000034503806035070660b4060041c5a80184440c051100c0e8245c50900c035246101e00200098400809003800d0054440711a0f00c440d460320 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 428449766 1250 428448516 428448533
    0x3080a0e0109060b0418080405060702030f060c09151e16051c0306050a050a09050403110d0c030807050c0d18050d0602030105210330090a050d030e03091003060e0c0304 74
    0x518241c524009505c00011504c01d03000c6408449c800c41d0340e140e4644851000c00c3c2082c520490409046c0500c5c0104880d00c0000c0004100003030040381c1d030014500c171491100c1c00304d02410812005010645000d03e032161030850040170501c101c1d69400354075141035900c4514000b554001c0703204a105c2442c2d01071800c0e40602a40f0301074041107840200c802d0611001c2440554903102e40030b0140d481d080440d042c14000d44050080655010907205c03200008140900444121041200012401c400044429220750143c1d031114203070201404082003030040450303405c05403020402c40d034020f040c40001d480d80d0703403440f03000d0171403054401603100d61401082003100043c8002d4500c00100568064086040101c11200900b280c0321001c80c007074140c25160003140507110380d0b16151407026401c0c0102042e0000b0390010745072080046070078400180c0303800c400340e80d0102d40e5100990300a202c5500c01d494006402d40c619041440c0001c1c0255585151b4109540c0c160381c0102d481600105200a006404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 428451016 1250 428449766 428449781
    0x60703060602071a0d0203070509151201091109010c140a20040c0f03050a09020402040303081603150b0904090c0f0f0608010b030601031e0f0b03010b04060506040303080a0e0109060b04 81
    0x1200c1290321000192107425081c41003810076407000d51b000002405c102e000b8802d66001030701c0507103042c01210854030209220743c0490219506040f594000140c0d40c140e80c0142c1c0210f44141500c076042c50f10800040d14040500b2808a0745564480c0040141450410480b1480d13030150103100065812070200000c1d01160000c01c5014504000f281c60449820503c00c490f1201a8640010565035180e4428002d11912200a5109000080020516600c441454000d010000810b0001c0350074903429400c4070580700481d210404198000c2040000c10b02c043c06240c0d00c050301c00b05031a407640d46d0b29540088160000e0310b1900340028148503c43d00c0300c00e032001400c800e04045090354101002584a404010704040c101a204d489030300c02c410910a18a28a810f110401d000f49203100049001074641113030b40c24025840c081c41d0b050f0501c2c1c030340665000c656001c1d1560746042c2c25600d0031125500010300003241c00d030700e0700d06580700d14609100c0c405040b4000c440000749108000c4c01c01c02910300c00d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 428452266 1250 428451016 428451029
    0x13150b0d06020a020c031c110a120f03091709030d0905091501050d0204261609020d020c0706020d0e0d0f141501030c06090e06210c150c07080703050606010c110306070306060207 78
    0x78078060000381c51900d0300c000d468014100302f00c00c038504190807800381c20304140083c0040c6100364608520444c0e40040d040740481103003590341401d8003860407656118613102c1c15a10602c4d41c4d000c601031280c5161032101640040c9001454051402e813500160b03842944489034500070310314034400e6044400d42503070014100d0809000311482e885d1602c800802140500c03031030303c1d600141c440302c00405d680c1190a04a40300081e82c02c1959107110103912821000091004210a442052454500f03038407580c84543d44021088020a100d07183c1d15003110303840c03100c8010b07445a080d24280009880c01017900951140312092505802c052000b014080a58041c1c3d224441038801d220a503070340d0f290301c06a040700700601c1d0005280021101450701404800450f040700d9514040b0511614400050504988000442e45516910420351b559040f8911002c1e1454002c0b1010074079a40c810240f41c0c840d18040c40d01d010303543c015540060305015003580c496000c29540c440400411f41c0600151001307000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 428453516 1250 428452266 428452273
    0xb0301091803022104090e0105160509090f0703151205100504030c0b0721020304112b170c0d11060c09090406021213150b0d06020a020c031c11 63
    0x241e0340c1c1c0a5501d56040d034850030aa01c8000f00d88054500c0a81614010725540c1014000015602c107541d00a1100766449d0040a04080126a11038010411280080006084140180d0b02c100b104031880001800e000101922000c614030754120302007454000c0d02180d046041c81895900e00301c0e1a0442403c040e1080130309020030023010a80080050140399040601e0070b600780d03500c250840e0040004002042884c000d40e68030b069890301540950302c90340c03280e401d24433040d1410302046202c1c00c0440822005907061100d1544410001035003c544900c40c0241c00c8042c84000d081c05050b812541c00b0701e0107503020007910308809910064008110101c2c50141c100c07030034410006500c0f4880d029216001e03c0400006c0303003c101080e41203840803005650260500d0030300300c01d00c42651045c0d27003003911100c4610f50f10810001191003081c1400382c0040c203400302115150f0301c8001a401182c0a01d0035030094000200c0d641e102803041d00e0688600031008555100010130240102207402900c07401540b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 428454766 1250 428453516 428453561
    0x70f020c011d03580c1b0f050a090501030c0618080307060c080f0c040506090a030209160f050309030702120a0606090b100207080c060327030a1215060806030a0803010b030109 77
    0x802d10b4644401051303040c90141407200107801e010040028200303041854019016001861607001440307807055070300c2121403071181c03036aa1036141c003079450038040038002c001010020440b05000d944005460030069002c5105680d450394441c3c1507030010582651220380320a12040410392040040e41d114210882c05015424010000c11440c0120b020b20780c005d19002a801d4803d647c2d0040d82d20042d54000c1000500b490440408032000700f40d101180302150b00d40a2221007076000b50183d0b4415004880190308018080e0200060883c0c11640342125000344614040070420038000e0780c0c00780c0003642c40401d80c2d100010903c8800380d04c07445084110f400012041c0201c201c04240c40001c448111001070b03c903283d0340c0c1c010340c15002600e42041d504011100b00541d814000c0041c01841d1043d8692184242010f0030420030380d52074078030565052180c1c4d0740a100f01c41c081c03402c06410040203011070706400080c1e6581d60441c2d1080e000040484000700c0108400f2110380160261304034000d20b80b95160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 428456016 1250 428454766 428454913
    0x30d15080a0b191817070c0b12090703050a03140403080a0908070512060402042703030f06050103050c030a0509070816141801030807060b0414070f020c011d03 70
    0xd1100c034130700804a50b0500f400c422072403907850903541505e400c007205188250b62940c0500da10380c171040c2c000b1040c500070000905a04808604042202d407c0390280020444e1544c088444202d69031100c00300100c1840302101240081025054810042c0c4600400c1421321607003502d008869481540b2070310002c2d60310340d207458022071515041035040c7e03808540802c60380000c2e4150b105c0103030350340030649804c85c6078014142d0680200506601303001003081101c0d1500d0045003900c004031031100340103d041000c070b131074007229a00007070340426410103130352504c1e484442c3d05081100c030407000c25006864031028064110146226100310340e04441c5010131840041600d189080305100117400c0b81c2e0041508418442c031504141e09800c40240104080c0e2188000100502c0040c0c440c0c8000802e040054081c050001600d00c11a00050312100d0700e504518101d5401564121581c940601601090380c0003010802c0100c0e44501110341a603690750030000a020b81d41c0306250046034288000c076240c4c8085c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 428457266 1250 428456016 428456051
    0x9010510022a10050d0609090c060c020a090509211207050c101409010b10050d09022e110303010302010f08090c120309041805030d15080a0b19 63
    0x800b0b14248411030010040030404000c80e510032805421140e6400070001641d4050020403081704560710401c000c54942600310212001c2e004002c001442142d0144440c2e0f018004420505100412000410b41c8501c1c6060546d9016500d03141d035030340314102c040d511410402c5030164a88000c0c1c070141c1031107102a491091140060803403003d1140020f084c035614032081c400e03412210503240040c4071a8a8002c03484a40403c11100b40c2e40039482e00b90903005a24210080340c00c00940381c0d0308e03181080d0f99203104c0e000400c0c4080080303a0001003903410031610403000300d007914103d40b0408a24130890099402a00103914005502140d40040005000503030700202954148a483e142410070382c0d442d110454034018182862607808429a409581c44080000082001ca1401d4070180403c80300c000074004800c000a10040c003a41040c02032804813116a880b02400c20f802c0b40c44260303055038803004181840c020090503502c00440c141081800b54a4200c910300902040c502003025004202100d0807 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 428458516 1250 428457266 428457283
    0x809070308090a090c120b060310090b0301090b010801020c15010b040e0c040b1b0d050f040e250302090103050609040308070809011d030921120c01020706090b060901051002 76
    0x10604002c140b114064640140d410040d00c00d400c0308110a161800f00030300700c9420540702c042c1d42e505010000e1001c0c00e1030020350f401000200340c1c40c2690350502d060100900300c00146240c05640e43c2d4484404281a0821070740240a140700040c1d4400600b2584e505040140d00380161000c0f0703507001080220800d00032903085450a00c0c1d02021521907491068052140d036001143d60032000c03a0382d02a1280382090201d4080c0000202c03403109520f0f0409849501032800b003004c00900030b0004209409205001c2e230342c800750f00c101358a10800310744603c00e00c5000c0e0303100b02d8000036408203014072113507007602c109030700004102e5000d022490300c0d6400411055000b0000800c1041040206203600c3c03003500184101110200d81031288150754440a03540d03000103401c14440c14940c407204080c1d5000307401d507803400401e08020b002a030000010b5030241d540583c01d400303c599420412000419083e1091900c40c9102d8a0b00203524100101003090b2600184c02c154800c414000c0c0c3c02d4480d540010781e101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 428459766 1250 428458516 428458523
    0x3060303181c0503130602010b0f1c0206030f0f010b0f1b12030c070308010504060312110703080d09050c012a0c03021801050a120503040509150301090b0a0c08090703 73
    0x40d003030302811020814107180d00c00040502c8084030040400c00a010001e405131140d402c094000241c0e582e4001c0342a54030b80185550046040306180b081800e002c2c40c0c0ca403049400c001c00800b0402e030b079170100b001035208650902c0311111400c03c1c0000c858010151900400705040d4607410300144164026461081401010f880c12694440c6202144103004810440354030442c000e031246010107a040d910f0f40400022800100030134008212883c15110304d400741c3e50003c400940d509510745040c1c1da80c00c0608200642c0b4403640d4400400100e81200802c42070a1241c404120b007400d610f805464000d10114490500c5200980020400b0b0490741e4003058000301c40e1202000030250070f00c0e24890405400282d04469808a00300c800d1090700d4401d412108140c82a1310142e0365921100c1c03c018013588018403540040000b00101e02d007070000306400076007428808004070000c030000703400c5801e8154101d071400b0b048400c00c1445241807140900711040b600b000500b501e010550035444911600004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 428461016 1250 428459766 428459797
    0x1214072003040b2b0509030a091706040609170403261c0f020403061b09060207031a18010207060e060c09060313060b0d0b160f0e010f030b030304030f110603060303 72
    0x1540b04c6007000800031400c4002c51410062420045c100c07a44035404681c1038004180003840021b414141c01009601c40105240a004140c039951745407005400e030020140e640803010ba030301503614000e00d401040254071400c0425030306c0301c004000e110407600781003141400ca031040c002e00884911021412411113600d850000c0d02a4003148014005d0185400c0607100310b103414294210314101810500c038035007140e210450510b030741e40d034101d9982000d80001400894060b81000c03010244006a503005250003601e0380540030306803401422038200400a4400644030400c20104040910450341c1100b140c449440c034186c08440401c8003440003924000204032040d21086c00d10280307900100c44104000c003100b075092580d040186444a061b40c803003501000c50904410520b00070b051202c040c0c0300b56215801c0740820240155440e204042d0020117154944904140da90b40610007003000d1445454402c51a583c242042a03030301c2440d504542c0100810014849259000001d48280508400e5036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 428462266 1250 428461016 428461057
    0x1707290702240a050c06060306190905010b0d060504170901020c240f0706051609030b04020a15050a080a02120f0709091b02101a011214072003040b 65
    0x98842c0701c0258100080c800760007154685809038040002c007186003001d001c131409074440108145c1c9486c825680c0c0748000c1c000a001c0c46030300520350410080c26004200000328241e4800c0410392281800900f00c42595940b420001000070608140180c1b01c0b000f0350840c14080c00b140040d40c0c4107000150684110040807040c180701300300c010038200480c1000d83c4551556211001440c96802c90b0004442c02414400050802850745504100c0c424080d501c0c00030b041c0c40c50b125880000300c0584140e8010307208080118003950103c80b61080c001166442c40d175a000da03184000e00d0900e028081c5820180100300080c541d641c43c664082c1c000c0c8404c0b9920707a003070311065001d0303d5030280f6030b12a9403940e0504024140003201c0070540c0d00d0007111074090700c0303420031406021001c81d51506148200043c1c0a04e0191241d403040c0020340341955904070010f4030800040510f105508101c404400261550041042500c0766800004c03219480800540c1024200300c1c5d1451076014440c007012028400b10304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 428463516 1250 428462266 428462299
    0xe13050c3103050a020a0b120604230c030a060807030206030a020a050c16060f0e13110904150501140c03040612091b0e1006020304030b0903041707290702 68
    0x218074004148002040060781d078a01661074101d4504181c0c4106414440041c0701c0340c5500c11100c0c520304124400000f030352058108030081041c0c1c0c0c1ca00302009080ca50803a0000d540e00303195400345404800c0c050300d038030304241c0d41002d5078200d8102c18090342100713904000503100d4005503500704013010782c09a240c28035803604a40741d0149190084c0203100e42e10b41507051050f000055429070b9603541c0e031040d42c5003100009441604241c02c2c3c0c1c43c1c0140640c1891141d16180368800e0b40244601c0c03604526140c07003400002c007900c03500a45040040f02c6100100829a00110382a100c0507000c2c3c0d11a0070072565460407901d034092807084906220840d00c4540c081003140e4420407920703030700030744215050f01c042100c0304140c40540917010505000c040072624500500c071610342210901d0b401140ba06095958500f8449009000b0419612040c000030444168584200040c1d8126400170721005160150001c1c810509401da0281030407612205006041200c0840f121150140d03a4814068081074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 428464766 1250 428463516 428463577
    0x609030c06040b07030801140303120601050f0d020c07060c08030114033301051504180905010501030302061b070f080a0903140a050708010e030301030b0a0b0904030e13050c 76
    0x6040c1a4405000100400c02100d100c0140c4661070095840011503030300e485a040c03000ba5001000380d40b40e0300600042406150380c042243d072040b0185416400d0210381442d00100390007070000c113144603801090820600b40c00f0071988004229602d40714000c1c1380241c6500f0122300c810b0051954004480304201c6054400300711222041100c044810b5540440c046400d800108242d015154100c02400020745032070904a50b4907090040f001083c901890b040510080c00c44039072006110390388510354100801e07003c5c4030300d5000f14044d0b009012a45041c198488051605001c00d040001050103620045520802e802c80e20552011881d50707a188403e4059426522f140e200400c400c060f88140300345000d012440c1d040c041d00c82d8044804003038540d50104d00369440c0034048a001e500510040020031650180c0c0d64000c82c400e88005038007841100032402284013114241c01140094400d580c01e81803080d01b1244040003880c1c01c0000b402c1415903100303144607001060410404110404101b0302015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 428466016 1250 428464766 428464783
    0x1050a15030b061308010c0e09010b09240a081015031e0603051b0303070b1b0c010c08060901120f020405060307120b040201140a0c0305160b0a091403090f060903 71
    0x40c041600c13020900340d5500e60300d00394040c107001942401d02e088409070103820345c40312100006080b03001681c2014a652000d80060649903402000d104881700c2d005502842a201c0e50903025107035680c1c01120901030980f050186c00c0f1b680c4081c85c0d00b41040716440d007052a0440f200c9034a03010500341d410716200c3c00c41d80111501500342e00e24100e000070070002d0010b000b000d080a031a04816601c0d010204043c0c13a4000d214025040c4140c82c0e00052144200c00d2101c9815016100071038100810001c41c6c41c03c541c1204540004148620280001490805406401010342910410008110ba60382011902103041d00074042c1d40c8030008143c40fa0b0342400824043d002c2d40100ca800d6a80500700300d403c030b903c00d96007030380030030082005030f08040000300444100d202e02c7d40700e0500d80c0905580c01c8406900c903982c0589d1480c807448400f00010300110132240900c0041c1000b02c4c22407003034100400745c01c1d103140b9002e445a204001c0b0b0200c94550a0360701d12045d80c00c03180c1545540050001c2030405080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 428467266 1250 428466016 428466019
    0xf140a0324031101050903340806010509060f100f0306350312012106020f0c01061e0e0a0204030203031c05060904080403150e0708010c031401050a15030b 68
    0xc0000e190301e011a50344680003182c0c0512a240c81644040005488034130502c00d02d503400d0380101e03454000c11144080007210440600d442d041051107402d8150210794402d402074000740d04104010417951520550003508000100c030900000620b030400141c01c181c42604e44003d00020b00d54502605000780e21480092030320340c8003440150074464007120707198440704100c0700e140c3c00003114000c002000419100140c0d00030f0104040360342407010010300203030b141d03a1074035040100c28180d800290b4540040d0200000c0c18490703d440350340b448440c50a45403960080d00a591440441440280d0885606030031948004000d070010740360300b15070308043c0c4203503000650144000038102030016032040d154030780004c81d03420030040c540b61441003020740711043d40c010f883c034074041c44244046068824141c0f0740d50f00020780011031481700d000d10b508000d041d612108460755514100041a43c1501544040c0120080921555814100060490909da0080c0c03901351003424160701d10f41c2d000754814902c0741e60 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 428468516 1250 428467266 428467301
    0x50d050d0206011a0711130c0e01080a02030c030708040f1b080c0312030610030603170703180308090f011e09052b03030e03070b04080d0c0206060906120a14010903030c0f140a03 78
    0x1440031001d049c8a040022807400039245200180e05441d8510a90740540d000d015042d19644400900700c910a50180060303c2c0003901da6000c01c00182c00c100c100700322413159080c2804051400482604069001e00d84900075009180f040d004804950101c1b907000708102c41c0001c0b80e001c03001c42100100780541000b0403261113546140141c86a945c06401001d03c80d41e969104003190100b144d10714a000d00c80106074440c1404031030018078180e60007a00c08041850b100070746070101c9507800503140b0405840008140200004e20140c10300d50061311040851038103c490181c030750003008143c030341d070311b04060101640d030030700302d50070301c0701401116800c40d085141d2000b1801e150902900c164481380f1240c816614121080d0740140c00400c0700340c8107480081c45043c07141c4d078030070a210141c09101c0394108680600400391000a80c034801103c00600c6a0300001503c00c032600d005021030350903220000902c50740d4030785003580e1035100400031030180321a1900c2e03031500440f00e0154050004000c1d941ea0210 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 428469766 1250 428468516 428468531
    0x210504060b15040b040303050a0302120f090c04090c03020d14030d020c1513110406090606080603190b04030f050d0207060c0e0411160c050d050d0206011a071113 71
    0x42904980619542140c0c2d818003440040d0b007140b002c3c4600d11400310034083c188030400c003103801180500086896410050311700a1800c40b20034030040200d0b10034036842d1303418080c4500c0040421007071810850664080109040d00d840f00e012030100c82c88001c0c400c3c0e8407400000104000244004990348100d0704981e01c07611028130f1400a5005124550030500c01c242d6509089204411814001c0395100880406c600e070f00d80300d00e0108180c1ca4001c0d50003680311400055001060300c1017100500322642c0b10015030034144100b50403d92a07490f02618500f10004210105041c1c06540c1d4200b603060034010006c030788182e001c1e0340c1ca0140000d680d80c00351000c030783d4005000f40364004211072981a80ca0ba84408408020401103034070f0a2220807150405001508040c0142c2c0200f0750000e00511a82680c250345000107a954682440100c8041d04005c0015200c107404002a40c094020b04100003198101249a114903000c0c1d5000a4803113030102c0102002620703000705e03100d80100009400c0c041c48 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 428471016 1250 428469766 428469773
    0x8130b04060b032e110d05100b0c0a02040b0409030503130f0f0b09010c080106020c0111010b0904110907020607080604020a0c14012310090c02250f05041407210504 72
    0x100c0c2138880001c1600004a0131003800700d40d8071601101c2180416850708051405002000070b20f8000e043c007890000035403000c250075a00318085d008040303011005180c2d60a451040c0405e8803c0340304124003550030034030310000107508101030b06e510480c0103001140c0d0070545e0070303e0305640300140c80c090002a4540c50074000d110102d01003e103d200680f00074088810b4940040707034085024803900c1c0041c0c1081807500c4a0358490403181401a0011001207038464950001961580701510111101d03610f090311a019411300030101c0303a110038a80041d203a54070305500054121000200303405c2c840e13a800601180c0e203900034080050382981201648006414070f000545c0204022048071030b6030741c05040c1301800e00140c402c2c3c40b44203d014101c00c4981a28040741b540103040888500e030154007940b0703c02c0342001c51401d4280c15416400400300802c62506401c0e004500f65500b1441c050340c204102d221319400074141880c0c0040301440c00f05402d0019402410f10507540d03841d4590f00780d00b011f0600051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 428472266 1250 428471016 428471053
    0x102030a05070203070c0e0601051308061e040b1306020715091b140415171606090e1504020f070f0b0c030f0a0e01021b0d080708130b04060b03 63
    0x61a03903a0381003226441e0110142da0b00d001d18000101028290b00d4140001404001d049030400c030181059401c04491150b503041c0944181c10202d000d5021004122902009411290001c60040e07080000c0741400d884001504500030314040c3c010202c0303e4a8010048242d040b80c0d81c10b6044042d4080620b076418046015001d941400d03100000074004a140603100c1da075041048803040e005c007074580b6081c8000e00c001303050b995038a08144581c040000034208010300119840320320400241504c048901e21a4500b0001a0494820000408000c3c40504803440d80140c00c0826800c00f2140c0b0032000c000100644074079128004020000700d0814100311810f880c040c0600c1c400c220010156031040d5000c0401c0c0002c841c030004640a0f00045408980c965006d00030010162001600e0010703c1c0032700003101034000c0504155a44441010340c0015441100f268000c6068070f4180e00b03031700340583c406a5031400c07004c02400114211001c10308101c910360014080400c064152441d0f400324103403a08a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 428473516 1250 428472266 428472271
    0x90c05042d09050c091203040504090309150302092101150906080105090a0209042a0b1c0e0c01030e0102091f09061e030c05070203100c0201061d010b2505010203 71
    0x1280080540d0200300140d0383d009240c8101a20004d803418005100c003002141707901c100240915010400002c2940e85032401061500d6010b42c17950140c80f80390406a2540c101d00c0c1554404051060003041c1c4583d0b91000c80303201c0b00c110031801903c03129640581c240100100040d00144001d514000070b0342c96519001007007100c041d08000c018a40d40e07442d541e0f8994180e41c0009510401c41c0c0e001400045403054061003055070301c445800361001c08114800c0600068101895028001ca100035122481140c0742c0a00102c2c030005121114207001c085503201030620290b41410307280c218044000d2000d605807207010b04000c0145060004602da054030501c11000c003100003030480900402e601e0701845621084001d03969510710a044450340840040030007514801c2000004c02c10700d4050f035000c001508072a41405000101044024000f908441c6203500c11640511005074503d61540c2d500041c41c111801c3e03010052380c0c1c860340e5064041c402007a094030310000480240240600405501440c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 428474766 1250 428473516 428473589
    0x1020a03080c0d330b0a0804150204060c060b01020f0a060f0e011503050c2407110607030215060a0303020a060507030905030408011b050f030a09020f040f090c06050304050601090c0504 81
    0x762084c0400220311042e000078010424000c600300040413403680301d4042550b1150143c44502d44483c2c0f115441c0084e0303442070307001000068060140a0510102b8810b00c1ca82640034001094a02c44c1c0071042c5440b60703031403100500f44540d40c403002500c01c0c04581012039140c2c5200003c00c105400282003540280c1240015107051103204101d40309400c005500c4d200b011400000ca00c00c0d81c0c014a10410300f46d0000c0002c030790007000c2800040e4151102000b03880c89500c02c0d0064103581680240940050800404043c86010030b0b5404101280d00031803a803542caa0040c0c00450240d880c040c0035005404010350062840c0b0001400007010751040d8020240da5185112805184d078005070100c0f80b50040c89986c1141c444100046401c0042d40c0c1d0105003039500c0a00b13408050514800018101e456421b4681d030160740b100b074007200300000401f80728003504171820401c5c110f042640701c0940d00c001c1401940403c03642c2e041415525801201601c0003020342420785d0010300aa40c2c0e80c1041103c030b50b00c2c9071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 428476016 1250 428474766 428474831
    0x1f020c01031a041d010f020a0909020903010b0d060905062401030504050a022101050a290d14030702090a4104080405091302060d020706090203030310032001020a03080c0d 75
    0x30a1b41d400e4074001c51b140b220580d070310f41182c3c5007800400c1c0003d40c4000c02d81580f6641e02c1c510400c403a103800755600b140343d0160000040306041410102d080200c01400c0350341c0d641ca070310344014824107920111100c241082c64009110740d41c42c0341041c80c00c02a4040a5440000030400081440c03001c00d800c011240703002d00a101c25100d0006420079a00c021442040c21604401903112241d15114000b1000c40010035895841c862034644000e03181c61001c080d501a00001a0641941042000150042604031080148440d40300c000034102c001ca080c10710010104034200c4007460a0b0455211030411101d41d40c000078202842c01109561113881a2402502c1c000c0004500b000807071035008540750040c000340e01d00682403240358000d501201044503d10ba6401403132015813001c0014610640f05a8004c242203411810580005032403d103114800760001d0703240d00626680414007400ea541e25040c584556210300542c3d4549005000f500c0e00b0b030f6482c0c2140b114403520801850b4813030042001c200b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 428477266 1250 428476016 428476031
    0xb18101b0f08040b0a05150d08040501020f1207080714030a030617030306010f030b010203040b120703060e1003030806010e06160210020a110d03030605030304080c1f020c01031a041d01 81
    0xb640d0311441150058040307004400040c0361203009400199120440c0f241c02c02d04950388400080e8040e10842d400d0342e555001113002d01c85540c040040641d00c102c03e000030040720050b0f82540200d8403a42000501c0004045100410040d41ca00d50402c07020320764003a0b984070b80050000a0041030349124418828030358078001030043d203010040f81d02030141030750b900b10600300b242d00a0340070300b60143d0402e04521003008000340d10100c0c3d802901c89444059503907205030a0000e4000d00f0784032140c10040b030140c40942480a0000401c0c3e00ca0201c03a49070410280d02e90768580180c1d40c9446070340f052070b0031002c00180d018000000c000c2d901c50641c800c0382c00d050420250b110407a40e0704054200180845041a00301c29140b03000059091003610902d80030403044e459002281c00c541140c1d0000505038402024030740769107482c00315921442401003150340c5041810364000c0d600c0c035080c1c8010f0305165844249100030303014030a0301001c4020141c41441068864a800d50007007112811a5070b1951a00c580c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 428478516 1250 428477266 428477297
    0x18150207120f11060702032a18091e19030909110703140a09090510030501020a050a0e030d05030f1b030702070501020c0604050108070f030204031e02010e01030501030b18101b 77
    0x45c1c5e40291380240041c02c000c05214004d1102c0388050020828040030100c12103895a01d010040388811804507100c42182404200b25240068821410004100c0811504552000020202101014005c80d00000599801c041e5607042580c1c1140c0e5401c2d06111002181e00f004800900119100b80d40d5042156400d00c052a15801820004070000b00d02003020050a60650003182d040100c0d08980d1401c107640780d0b2103a00b2684620031900100d503020800d01601c5401c0788002000c610190054028042841001012480000c009a04441038000801c2c9007420440d44000442c010545081d92170500031b070041c1d43c810304c80c80b400c0d00500c00c19050401a0420009407002c480d01a1100030040d101c5c1e0f2400d56640762221840010183e0900001003c5011080f4850702c0301d03101030302c040a020940c000140a90032400c4840d0515040800410001c6c0c0840303e8075500030851100040741c800019a080c1c2801600480e102c034141c00d000c0301d8900701444c1410050300321700a4850b88100d000303008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 428479766 1250 428478516 428478529
    0x11a2a03070812100f0b0f1b010c020615060703030509010b030f01061a071a2203030914060f06011202040e0a020301170d0c08090a15080f010618150207120f11 70
    0x100311817620813080c20040354401358080c1480082c04468a41000840c01e004403900c280f8006124250f074403102214800381d01407101a4001c0910307480345220303201410205656102d0110010200359540000035100103080d0310080031104010140c0703030080150318009000c1c00d424018110400700c1581d04070038406c1103008540141342c0c400030411034482000c0050802d01c40c01000d000340701507101c10b6080100c1c2d024244502c1c0314441e840003d66030000c0e0401e0071401144107034903861940400c09000f01c00c00740c2080203910010903c0c0c0765108082045900c006401903a0009001c0e00110042c00603088064000d14140c410080300c1000ca014030603090340d07551503494a01d001040c138558600001c0346400c40104001d0b003003e0648a82d0726555500c00701003100d0406c4000000d074a800520043c101c650328614010180d0745840c161400a203d88003d20b8403540c0b099280702091007500505150081c00801c1c004c01040900700a001e1290400b8440c000c03820703804032003001404910700744030724024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 428481016 1250 428479766 428479769
    0x1a040311010903121107080c010e01050105060703020a14030d020a05090f060f0708160b010b091206010f120f14100e0102130e04020a0e0106030b0306011a2a0307081210 74
    0x10780d505054490401c2d42c4000508440d02a850317042c40801c40b0a01241d40b41e4001d01c260030f1003134000207940da0701524040c03c542061b0400c5102d07030744c01c00c40c20002c25400907903a00041c1d0400481392110551440e802d00e10f109030140820340d2400481c00004035038100016000000080c0c45401701c4000c6203041219900c030302c03440d068507180d01780045d00c0425030580141250515420445031000d15907118400312100036440008003800015150041d810034a032088021003443d401030000d5418030308140c0214003240281050000742c144003800380400f80420b02c01040d00728043d01c4251912001d41602c2e1030007815004045030403c4502c1d13400600500c2100c0e0b0ba401500c0a010f034842c1020b40e050b10340d00c00544140d0b07000d42540408992105903a40060082106460001c0e00400903010b043c01c11a0580c4913110f5180c030070042c0c025284a0320101c9080824130b42e0401600d29281c0b40e50f8840c40c5440241403400e00c00400ca00003040f0307108008098102040f80400c140b680e4400210138959540d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 428482266 1250 428481016 428481023
    0x40302070314010204090f06031a06030c01050d0213030c05100519200d26040b15011b08070c080f10020a0504030f1a0603030301030b060d0f1a0403110109 68
    0x5420404952144182c03042048603100141c03405644413800c90a48000c041c07040703040c40c0d6403003080003004400008000584a00c5107590000e181880c0007035103071100c015185040c410b0000c0c0c8410081036030390480b520007070003078540400180c5a081040750421280a15405240d500d0815042107000307205840000840d2901c50030030070b0003140b00702d170600240b082c040d2110342c0b01141030030059000c1c0140100c0010f03e642d80d0f0050004a0140d5404083c0512000c1c20100050b041c000412800481d080e806110407442e01c0b620003d140c01285c0a058038018841c10920a0703542404020000c801450024081c2552422050b250320080f6100c001c0100070311000c2e401118440704124458020f17118080707160800500303080e52510380e03c10304000c80710122002400e40907920820954030b0700c000c0d00000168025811507045039290304c0d1030900502124801e00301807107003808100403e0390950101d544284528a0031300a20300e071940c155000e81d01200400c69900d04080c0240c2c05200da084003070303003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 428483516 1250 428482266 428482273
    0xc03080c0d050f1603050909091506010e150f07050f0109020411041d1906060905030f0a08070618060e03120609160c1515080111040f09050910052706040302 69
    0x44000c4da030841503c3c811001c0c0311061000310f0301540e94107003062107061440e000c0e100200f0218917000410034000c00d01130603c04120101c803500e03180c2c40002c00d00305e203840d119940d0740c1ca606080305285000b00c0400904074400c02d4007105504c0c90640061400b94800d46052101c042c80710b000041301e00450203141d034894070302c07140c00428070888000d503500001d03140400304596003080c401c0402d03a40150024000320301c1c0140c0030007060030100000106458030001a201424003a236509502d4881c40401902054484049246074102c038040154030640c03060003040804803942c070340ba8032a04445554071b10414940005100c0e4109007038650701c24051039980400701d14090405440452141781309850b0710150b0780069042442c140700f0280e000b070368580110406441c0080d10f07401e6490082c45449824018402040354042800d03a0304241c40507104080f41698850400d58581290440352550031401c140a03c4911000d04c03050489001440c20312400410010a01c1599040165802001a40f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 428484766 1250 428483516 428483527
    0x120b06060703030b09100f0b03040503041e0f1d090622060212130c06050c070b07020102150103031206060207120305030603070f06021e0604110402090604030c03080c0d050f 76
    0x500100100003461290500195501400000c01c07007074201210304162111030010300303115101010010400528810b05ca02740f0714078090b41d038035841e80184d00c19030381c0000178030649030480b80345800a4009802c803000308205140e501c20388c28150348040074103010b03920b01c04404a03070790000c0422082d02c80d08805e0803402044464014090342c01c20641400c0c2d030655030a00030710003d4001100007a004034940301200c8103c0e10542800142c20f180c80d88000f0a0000810200b0f64a010102e42c03002140c45004d10a926003035640010307414100358070b860030005041d120000c010140c03c02c0403070182c07101c0703d0780810080d511240141d03a1200a401031054030381d40c80e61488000b911440c004c5074003da014099a000d550380d06821078105d0555080800503801c6a83c1031100b117044480e2000c40c1920b0107004100ba410701780c50b0ba0340c90f10f00c41c15800c1c1c000e5030001003e42c12a00d070541142d00a684c80400300a820f540c80c180207005401642d04041c1c031f4010b007044005450f10031400c0e07c407442c41a070207051400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 428486016 1250 428484766 428484769
    0xd06020307032a020c0120070e01080c0108090c061308030c0f070b0a020601030602090406080706080712090f0f0c0803040b09030d0c0b1302010c0f0602190503090d03110f160c120b06 80
    0xd40c187c800c00003911822204402c41c4030040c803402c001030641c007081c1c41e10341d4100a452400e145084200a041085440c02c002c80c0000009840c10044007e030381440c1c1c0d4100111810444811075004070b40144800510b142c070b041700000c1c1921403030004800b550080791f1030ba1000006449112514001a0711881c01132000c5515076000748001100100002101c0790303034082c4a41040141c0d4082404100e501c4100840c168014008120600140f88100060030f1542d49440201c072080d8006080703024903510b01c408102c0412180005407902c8012a5102d503070b10001d0007840d07807066202c81c2c02409040e82d4040041c1c019940f0194030317640b1480410065a03284c40c8200c005451100a0303040014210b0441c000c1000450f00d58002400350b24050307601e0301c8500d600401c2c002c051250104210040041181c00030012401c204c4645175480c01241c00081e40304000e09a0041448200c02da05001444440c4460162140d00b00030384240c0070900c1c503a940340c42c040c030303114504440645454000300c0091385d50b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 428487266 1250 428486016 428486027
    0xa050d020309030c060f0117190303021c241502120c0111030a05010e061e01051b37030c0305030705070c03050c0102010b030a0807030804020d06020307032a020c01 72
    0x4a28402c08503810805446881413406800703540441c415900e600050005614015030303a10b02d23054102c001c022038007000c4c442961180c041c8002404065011960f000f002c40c0c410300080d03441c060242c0038440301e082c0020500100c601280000b111003800c030340c009030800d0b41c28200c0c0c401c00000e4020300f6043d03a0074041803a07150b0101800002c41d56a4006c07000d841c0e60b8090245020b80e031524400a080c0d81050524a03085002500180c0700701015007600d04107000d0300c0071501805200f13281003030302e4a20035201031000760781d598020721040c020040c90924002035605121501c2c07079040e0010103040004621051548000d081c05030001d000c0e1450000401c3c0034000641c0c00c4003161614a10341784454131001503055198004403095040b401144226603424090003030482002c80180003104803d56880c1e0707151092480050174850558001010356403042590412a40c10070000d665030318204200400510302c00b0903000004659030700e40c00c07908040c4e01d682c480c40031003500100070242e10103005440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 428488516 1250 428487266 428487271
    0xc0c19060503041a01061e020102070b1504020403050601080a02091f0504020708090918010609060617040201051603030203010302090c070206120a0e07181406030d08060102010b0603010303170c0a050d0203 90
    0xc00c070100c0640c0f8034204e101c9100c41070080102d6607400f03d600403400d400305501481c01070504110380c018068603000c240b01c3c040c00e64100114007d0300c00862001004500039015039030001d00540549000000c1041010600c1c2200b076208851400042d55203410486450411440c03030106201c03110024403e60806034024062036008900081c2804a10000242c008608413045540d1181c0c4c5403030303102c4841c000d008400c0034080e103c1c4c0034014242409002003a030500407811022105900c4042421759000380104c9000c4c1c41c242e040300d04141000d050240c00782d402031000320300520010002580c6a400c440a981c0c400750f005003410b1030060300a0019410050140a08110325030740e040855582c001041250014440004403240d02d07003814205400b19401c500c10b813168042000d0411020341c0d00866141190036290170560019103600004074014190145504d07005840080003100f032640200c0558412442c1590714125070341d5070081c0d00482c2c002c8001c5040498018010441d10384010f402665 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 428489766 1250 428488516 428488523
    0xf0b07110f01021c09031103071229070203070b01090b10180306020f22050f060901090f17060f010303020a1209090f0f1b0801140310060e070912030e06071103060a020c0c1906050304 80
    0x4049504e1100d0300a40201c1901d401c070240e3b0000611408102c1c01030f0300390380140840c901c10011070441c8408105210740400d5081c04101303141d4080702e00d8044000a110255400003011919050200c0ea400c1a660140981c200700704041c7c00030301c03417843e4100150780c2610320281403008001141024488aa04588501c505000d41c1c070401144250090760b400c0024038402044e019075200c0100740030b0030000060100203c1c9114000180082500050801c0301c50b540400c0e299401802074104a49034010f64201c102101c1c180b00d00052680742541080080f100c0685c3d041029400d081174001000102900c0d9001281203840100810010211241001400507043d6030740745d40701c425070b00221509030300325800e41249401030215140d44505000c02a1142104c3c5560089031620064944000f4088907440b07103800290500800c14a0441070f072002101508460507800c0c169101c1029412669066640d4820014070b07035050b1810000e00e80a1100c0520b1042c2c903141070600c00c0b14540d10041059 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 428491016 1250 428489766 428489813
    0xf06081302130b100e0306060108041a1005090a051018020f0f040e070503010f03060b01050d0903020a03030b18130501020c0a0308010f0b07110f01021c090311030712 73
    0xd0150300c2c0c0c444150341410001c030780000c2d0480c01004000d0000580c502c04800c10504a0b956006a100041d210390003440034200454695170310315282c80180c40c000c140c607540003a1101070241c2149130304604401c0d101c0440d40c80b140c0b9966050200300312541101d1000c401c480d0304e04200406540c2404000414401c401c0262600000340700511141c0d0122900844c2d0040008040000d0400301c03052a4222013549005071a5502d03240c01e41600302c6a9020142c14295141c90052301c40e80500c045600c600306144091221004500740603444180c115010750111742092080040e13450a8840440401c00041b040c4580d61100c800f5151303118800d28040311250340c20000101c092104205403070740d641c800da9071a401c66042610a500c050144e03402110704800a0120f0300c00240100301c00148600c040d02d02440d41848a00101c0c034003142240d00034206121a0700014605500206410640b030244881136141e651721400c1c1595030f10320788900c40c1d8034103404200030b0009800e4503108003050000e0702c12 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 428492266 1250 428491016 428491051
    0x61b0d0902190f080c010e10110a0b0117010c020316060f090b0f100504140a0915020f04080c030c03030909040305090405070c120815100201060807081609060f0608 72
    0x10001d000120f4100740c61000d00600e003040b103420104200200750b4020f2919803060003410003c03522100b0300720760040c03d0015191030003040120400401d82456080b40c800040c0f96561000746810012203404075182e9400c2c007003260f048a000004031421821000540c110303441d00d54654000501b401e402c10312580f0303210003590000c140300a400038010142c200d8100c1c0141440c2e20380c2800c401980d4030040c09181404c003c00e00080c0880d00040d071082101070b022680303501d1403400790310103901e0700360403130f0b2452020402d040c00c075010710064002d0b00c0c8542d040b9448821804201581d64a2146080354035031300400c413009250400890042e081803003410200d003406948000181601e800329092000941c013007403041e090140000404015501d94100881c460410000c0c0440600351f400b06070b8040c3c08066411200e40b4802d43c8860300406d000e50969500740d0b11011200d494074076440100c50080e6607a0004501d441c524851601191142803200407450b15141040d140194020107a82988440070b20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 428493516 1250 428492266 428492299
    0x60a06201501030c05010809011107060504051009080406030b06040503100e0325020f0d02030604110f06270a08030d0f110a090501080a090201081906050a030b040302061b0d0902 78
    0x90282c041c5224a007800e594505020006241801c0244400c400d80e040030348101100c50f15104a4414a400c003c010846503180d040061500e013001180c001182d241c40010700a0102032800341c0107580840d501408001200300400406001d603002d142da050304000844108040c20b50312503100d014844050300d0800c0407280781031085485d01a080442405205001c00071072500d00c0705030220003011581c2800000c1c0c00d4001c80c2d80c54400a000400c50b100c607524000155549000c1d8041c280d50041010f80d855200b421071507071140d10302100342d1106c1400a6009114138140d50782005481c038410056040c282e220b1003c0d00030303105100200c0b02540d96443c51191499015009003003a21040e110180c0380340c030344400141000b800a0145990901c0c0103d8000140e9100c032a41790003035203200d500c1c0c0346803015003c1a030040c01607900c09980710804520010821a404249a2180e4042c0d02030f03c6040d69070703001c00300c6000690300b40c00c1d8070980104450250019580c0c44800725600141c0f900d01c04102c030b1070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 428494766 1250 428493516 428493553
    0xe0f13060f09090b070f0c11040605130f05070201020a0c060c050f030a0b030f010c02070506030402151b0d0c121b120504030c09020a0e010c170d02070201020105060a0620 75
    0x30401c00350301d038540391010180b00213032a140b034101d2000c0c030385404c4202c40a44001c001140b80f401c01844142501c000810654503604802e014100c000c00700f800c0013000702c00a0380144a14044004550706103070004910600601c20f03120006140c2e1941a04250799644501c020941110008248101442408046166203000d14400c868032400024482554000c244ca800513011006150303030b0510341219130044d4003140c590100c1e00160761803910ba84562000452843d080411044050310204402404618402c07414544510203000d542200b012400c0840310003440200290081249524034803210b07109104800041c4030801c604209202943e441441544240401c0000a84003140520500910031902402090b00c0c0e0401c525002c40b40e0030250100c00c40420032418070030250080d1040c800c803e040140b04403102c0c103809546080c1005410000c2d0400c80040c2c0c010341c40c260021308107040c000a20f10036a01c07552a540b004007501c03040e000c4000c3c10904440c03d54003510b00120410700c1140c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 428496016 1250 428494766 428494769
    0x309060504030c0308090a0840060f030e0304052b03021f050118050402030f060408030117030a140d150f0614030c041503020405180a0506010e0f13060f 67
    0x343e45001c0044003d050007843d04c900074014017103907007003d141c050000e1103507401c640c1403c020791200035002401490000140b003c4040f04848403800b16101c024428900341d00405544840d282c6180740d0407202d408030708682200100d09201da0040000f4881483c141a0030b0b9402001c01104d500c0c8400c0340b440440b5641482241180036070f20030103140560380f01240000028944d4103804200c55032400d01048051480401b01100704c035950004101591414401119400d83c54402c03035100d4109443d00702c03803e6000b40b062010000403a1980e5440f28000320031681d00c890070340c0c0d80c904c0005403c2c8a2541aa02c90000c20650343d6550642140004052000720018000d0112000120b0f10b4524003401e4840302c10181d0007506d004104118070031035140c0c02e541c140d0b00717010011202c0100d4a54154020301c210b030807465104020070203102d200340c2c42102e010700c600350000341407045031074140054900e42c459030a01c6038841c3c6c281d50000c0040c00c181c03840c4251750400000c0030960715540d5140e10b8107420355 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 428497266 1250 428496016 428496023
    0x4050603060f130f0b01050a1b11100503060f010c08030703110417010203040b0919080a02100e030c070509130f06140c030405071509050402071401050c0a08090c0a05100309060504 79
    0x580304807213a000464414000c41040030300b03000e072034000d40600c01016030403204801000c1d00303d803850300e070140821340042800d41c0350040c0c03480c40c214000d80c6010b131a940080f225144142141c207186426548100c0740e07000c00e143d1040781e09049d910340781c0302a0083d103042e5880c2070f400c45040c0400235146903880d81034812007c0e070070700041e036900b400c2c104110300d840000e000840c26071081c00e82200b001d29080e060810150400c01045e180c0105003000c03828012880700c1d901c407143c03d00c050000b4220010004007180766010085a02d91580c070818881810700498a41c58032410384071080011801007400c01d0100c038414030002070900d42c11000d1b541000d80955440042d20008802c00040007400c200c400003400e0785004a401040c2e0f4818001c02400e054041c050040d500440c02d001005080c000c492000301e0340070024402443c140b0765090598100c0c1001400182101022800f804008141000d00b81c10107084030060391b04003070a01c01034103c0c44000000301a522003e48000c44e84038030649000303a21 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 428498516 1250 428497266 428497271
    0xf0e130510020d0f2307020a020301050720010e031b0a0c09140117031c020c01141b03090307060e0f060a020306041a01120f0905030712020f1204050603060f13 70
    0x582d880703c104807005069000b1650340703456050000d200d000032904403443c4490500902590322080104d04041c8210002501503080c003051003c803541000c0d043c81c845601c0088404034402c01640301d420707500880708100c43d9030020030044214009454003c03480030248800c5500104480da14854980000e80c03114800c59a6403400b91108203a5180d500d0043c14401820140c220880361460748a1003413041282414440c0b031403110040c0526015210b010303841c1d10007003100c0c0c10f009541039805c1c4800c41d19603001c00c000ca140440c400010b8015a401074003007000850810072107a951030000d001c034180460441c4a000d4002c001450100b001e039200d071860120158581c2005c2041c00191000010700e1610754100d000d074009142d900c0781c41c0d2425002d0500020454403403031041d031001400c207014080e1081c00002640c2c01404065074074200c280943c4d13400c032102031520015054603480250b8004002800c1004200b00500d003d40165030040d900509040d81c010080d00040c003140c02c0c01825110b0b01d034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 428499766 1250 428498516 428498527
    0x6012a0506092104150e0409020303190e040c0c0b072a03030c0503150d1707031e08010506030f090c130b1008060f1504171006050a0f0e13051002 64
    0x9803601442d1540d503040d403c460f41014213002e881515030200140300020400c002040d01010750321a00708585982c0c001e002d403607840c1000703801c5e064159039130004600821560020305c0858102440340c0c424494003a510640c4030403666590a59040010b4801001c101c04440c82c140c42c040351304811003403c90b607070080742044000d034030700070341698046455281030000034410040401034039039007410040800c6a50002d50542d0b40340c02e01880ca81c152143c0c01c0c5d12400304000741010741280001d40610f00c0c02d0044e030004a1010f00840740c0d200b0900905401034010310114070401e103840611500140c1300c8082d80c280724100400700b0f960051100c00404039540b1144032040314104501c0d40c14500313105141007406881c1580c042944100d1209070316008005031f0f0b19002003004800191009499004250074501c0a60400c46039981c00c20181e5107905440c0c400c000400f8680b0740115400c1314080b80104220301d25050300030300a00401410310a41c80c004041e804e00013502442905003014280380c0c01602e42 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 428501016 1250 428499766 428499793
    0x1b0812010f121218090e03120606073c03050702121204050d110402120910020405031002090d0b0108010e0f01061a0c07031e061406012a050609 63
    0x75103600003150604186501c4010803007014a180054090742000901e00200700b4111415001560001c1502491700340b2403565101c2c04002800300031200d81180021703446020400034a40300707100000380803402c00701c8140a40c0b05140d4803004241c038003030270200d85103d95000c14440b11496800442c00150000345290440c50f216540100c03046400c1e000701070035100744500381da941c80345020740c0d8442c2c1d5a800c0903d04109102e5007425840102810a64a60581c0700e591021104160b810760101d0080030700084510a551086d00c003100c40042c020508089031040590080d40050000c9030021030204080d800b107040544054000d148200001a54040d019600c904080050803440d101e6414107600700040d852a0322514035030101c922051750b0304c640c0c02048a00d0405954001420320f011001000700021144402040881c020182840761005500701030340300450848400d03000c02c07080c4020078882860030511080c00321a01c1c40600c05040d40d605c03507618121084500d12840d5110310f0341403550 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 428502266 1250 428501016 428501039
    0x6020703030f1107030212030c16060311030c03040f02310b0a06211e0606020705060306061b070812030a0c090602030f03150a091401140a061b081201 66
    0xb003082610b040412110b01083c80c0c3e40799603181c4406442806001f43c0d82d81d04003402d01c100d880801c941412241964040020124030340007070312441000c02c0c600301e801140c00041c881228421019250554a03507a0703680e80e00c90707000814000030380c1c00064440951701003010840c080c644140446020400341401c008403c4180d480c0030344428000d03141003c3c1000196041540040c410a6044039150042c0d000003510000341500c2001407010038591020001d0174a01c0e43c050420b031141c2c0e50030303900c5441c0c5070410f04c84c0f036100030758440e500309408000d14124941d1002c00300b91315610710402d45000c03a56550f0064908003010326015140c05000080c00443c031002d101740843d80700d80c0c0c107002003080c0c41c0c80c0d00a52030740540f103c10080c144000000920500041d6005100711800a100c0e2566545890b4003034010140a1450001700c40c0740300010070f03028104180045c191400811917005076041860460b00303400c4c1c40e21901c803440045070041002801d002c01038800d080d02c0d6200c0c0c0a081d890305408541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 428503516 1250 428502266 428502287
    0x30c0d060906060905010c0f0515010603050f1506160c0603021317030f1b070b070302010b120c10090f15120c020a030c0f02090103081e1305040c180602070303 70
    0x581e285004800c000d0741d40c01c000d40804564007403d000c0900c100310f0034600f40b406103030000104980110310100b505c7d00300b64050715041e600607647c2005940e460407144282b1030425030700c64840c62810b862802c40c41c035050005180007002518a82c1d51847c16a0781d0010703d003465085200400e80104182c017801940b4200200201482e04001410352015581140c503031040049540f420640002c03216502d0003a15883c1e040000898200ca45565843c00351081a40000302c0c110019420010040c0113843c0030f0034030080c400101d0020341540801c21040111200c045c1480009000740c9803c005003100181d10303090001c01c440b9540081d01001120014007c52541d01d00203a400c0c9050b01540381e582d03000070020a86036050805c01220301c841e040400c030b689554400252f10000e040c00220400900d0405002140200c44c0d50342d80d0340710510304203010303401100e042c0320003009401400c0146181030b4025203580c2d8114108a0b090011454403604154980d400c44009030b8030402c81002007540c4a88a0360 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 428504766 1250 428503516 428503529
    0x703020f013303170702060f0c100605030109020906040f0b04090c030611070c031709040f0f0b010e090a1503150c02100b09060f12030c07030b18120309070506030c0d06 74
    0x95046003541e444c0b4040e0003414200c0c0c5045280850840c0c00c64485401302c492018002d146142c9503000d44d0403003a640c2901e420b865500e282004800035040c00c0500600065a9005114072401d9a4640500005101c07900440c40041d8544050402c41d46a902c030790301103540660a1590168114200f0b5410b0702c261884071001150100203000100302905401802d595104440e4589111080c410701098004c003242c9a61040c41c02c5c0c104111209294484e19a00e000c01d08144140c00071030300107540e030101503041c50350805c03c079100045021003d40d001080300e41c150400030600c00e41740d8a90b83c030826140c1142c003135801c1c2ea0b034111000c0d007501000030503440b08010205021002c11140410484180a8001c50140c2c44132268198240d903074010a844244c0300b0003c1700d0311440124005035030744401e030bc4203032a0810402c01103140c00b00c151704010107464142000b44079480124610440c191b100600d01d0102c0c1c014032901182c03035620310780110b024030411003c3c42c1d20b4080481641040307494030f07800382 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 428506016 1250 428504766 428504861
    0x9030d0e060109111921110304060b03010b01050a0806030a05030f130b030c041e090e0d030b271302030a0b0603010b03151603020702040c03021b03090a0b0703020f01 73
    0x7041d0a144449035040001a10720782100d94012030700c940800050b940702c804c0355482c07c0024010445a071980507600c194011503003440300080010a06080f6910414214001181048228081d50159500302d411000103000c46400405545400b402e5400400720885e0100d000643d051810511307224813030180c0074ae40100e03861403d00c5416100c081c03107184640050701c90040c2c1d144800492200303041c0010302869209009403145441080e803107001030003030b2201191801114620b40d060041c0d640c2240c1c4804580c903982507003080464000600c00414000ca43c02d000b8501c00010303181440309000940c803801e800c0381c6d02d040041c205403d5510400010b13029030321650303540c8064511108403a81194180120020300c424006080f40a03110741e5401a400c00d08210240109650660013003120400035014120944101c04410b61244103101c011903001c0450b510911a1076405401808110310074011035070f030f407030040c5040d0742550405c002014100803614039904c0004a480d1b0380c1031a004070304042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 428507266 1250 428506016 428506027
    0x2071b080105060102030304020904060209191e030b0a05100b0a03020301060306170d050306150c0c090708011a0d1e0603142103070507050a051b040216060509030d0e06010911 77
    0x6d64a0100800181c803411007100030074248001a81124030300d40c009000c4440000d107140b143c0c0ba000d45503108030101c058180f1290001c82000030000403d80c2d074040c440002e581c480f980044094400540ba8140c038141003000052020858801810209956140540c6a41c905040a411240c4070345c030920711003110354022000b084001c101210748040368181075481e0b480700b02c0452200300807071544401144c0c00145aa80341e2400003030181c05614102d402100641d00c2900850311164203200d44003070b44030302180300da01c5004804003611004440041c0000c0d01c09070141a8522085801c001040055840e0700c14800c1c002030301d003d806e0641041000300b1400c1d1403040d02e0340c4030b22740782d45840300300307480200c0424190391059003100c034403e07005000c40e107951040f03003006c680b01c1600504441682204c890016541d061600a9403503440c0c80c3d4000003004406502c0303910292500608800322030008100880c43c81105106d6170401101803002400075604144514003184c548107082850f19005116 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 428508516 1250 428507266 428507269
    0x70b070203030a08150d0305070b28050a0b040f09050724080c0705010c02060709080d0f0309020a091d06060405060d02310c02190302072702071b08010506 68
    0x101c0e0f101802c3c52400c50358941d00c0d07861408840102000311540038064010041c10b00da440742c0070780080c0307004000c0d00a0b0764480f0341071a00b405031a8542400701540301140001c0e24091340c1c1c0400d42c800b8540d5404a80061150002411540c948140f0f052031030740c8807244024403c0c1013103801c004c0d200036548a140e608040d08406103070960019500204504000002c01082c55102550800c44d4880028001d1012241010b5180e0320300301d0741c1c41d0018200d200009820f034800280380342a80301d1500c40401500019100b01c000c2c2a42d10010b0340c10014040c800651054035116140080b0f060184011002120001103418104050310b40c2d0310880c204000d00503242d580c102c0218001d54100c90644168401001a070b50b255a03030301000007900780c0721824000ea4511604034030200c0c4203d9082d114001104c0350071150003030503804042c1c0140c0c0101414811600c00c018038250c0c0424003083c66816044020703103e82030707900001d0300702c810902c07841c42d1100410800d5295805485294000d0005241000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 428509766 1250 428508516 428508523
    0x50319051507120903020a02031501030218010302150903010e0f071d01050a0909020d050312060f06180103020309121602010908030a0503220203060f010e1503060c0702030304120c0305070b070203 86
    0x80800f0321079550140502014001c1182c00941940a0b040d0380c01d41c5900b80d0b600d86004400d1100764083c1074041d003030401044120341c0300e42c1030720f900411503140740c52403042c4c10311650802e542076901036680304051741d0714920402002070303200d8009005017070717141c00c2c5400e4181e80070550012904541e207a400610050755844401010341c1c05910300041c10424500000f814104c002c80040c0c00340c0000600030813135409200400e446510144d552501002c1c880c400d11040788640380801c04071441c0c403107041c0d666611a80045801440c0703074048410b804091590080d91707a000303204200f51054020360350001c550b008a02c020081142101441c10940510701c007404c0752000030029420762803a078180c80140065101e22003c1160080e0480c1c0741490a5905d5140e903840038040c1e400c2e20540100020209500320a102507242c402030f0151100f52122120304000740c0001d80102ea160005000c04519440381720f264440c65030140b41552105840d60400c6410b080b1682c01402c0d984408000a6000d42c4000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 428511016 1250 428509766 428509787
    0x60506030f090f1b040f06030c0e091911010825050306040b040905031210090603110306100f05012d080403030c08040b01030b0402130609020a030e0705100f09050319051507 76
    0x40e540424180c1001b00150300604c250741005140780202a00401d1403080010858840c840c40b03411102512801040b207e42038401c90790080c0500d810200d480c2d515440740c081141c00000c6852180079400310520001c04210302c00c0d8a030400142c01004101c410710f03241c01100d81c0da0724181c070100a10301503038031607544034031031000a011060300f40b40101d550382c801d589000d0300074001c50314100031240d124501281d0070310802803414424440e204c04a001c513680040b006040b501d0705481c0b0802c071840c10006503152290f00211900341740c03031481d215190000032100f200361014a9590840349240a1401804860042c601481009412010000051142c0c0500c6041d00c1d0003584410041c0e55510000c3c44c0c0f000b000c0c0c0e210101030300302000047e450000d80c000d0406000b640d1014441410600000c0707503a022503103c3c0301c1e400001103048294070343c0140700c0c01800300c0451410706030701c07034548022070301d03004a4585501e039030200c2c0d209040510a081c0100c0e5040c10142315601403078203000c00020700310303c1c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 428512266 1250 428511016 428511019
    0xd080c010e251505210f0a060506090409140106032603042004090f110f030105040c050f030708010c020304050a170a02120c19090c0206091f060506030f090f1b 70
    0x4a040400019004000b50307850044240322416490107216000301c495170050381ea90042c0712030b100201c3c5120ba402d00985041e80c1010b0f0145007400058000c01014141c1d2038000d4404601c00d07000401030030800c1c080c030f201440c09041100031006d000306c4080b80f003441e030310381e1842c101205209200c002452115002202030410080380111000500081c0017000c2c030b200c005140d01000b83c070580805c03005d0002900000000c4581e1980150503000740750980d10122001800007070f0b903a4040c4102c1c500001c00d20b0690760060221038900d40c484440908441a00d4510009644003141c100490300d00300d1910405441c01c0000140340501003001969650034144e4001d210f00c000b42800d400e0004100584000c941000704086001c50b00181c0c100c0c8018120f0044515083c10000812102800040d07124040c082d01c40080242e96529086c0c1d980c5080c0a5084103400c039141c0390001800d55460000d540260140d1116250038103041c442c05141c42440850805030b0740000720480e4266802d03240c0300721200d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 428513516 1250 428512266 428512289
    0x40201020d080702030d0c09080319020c03010621171206090a02181002012d06060507080d0b0609090405030904060801051303030e0f010e070f05060f04140d080c010e25 74
    0x480340408d80f0049601e800c40e0302c10380310100e610310b100c4000f40d4080c4100070854095513043c1c10503609240c2a50024001e0004420b000b625601c003030081c00480000342d9009a2800c0644515122850320ba80e000e84a11400c4c42c0102040c401d01e031410403100b6410124020303003145040d00045226900b011052100c42c80f4030003041221070305a00030b400c02e59602562900f0040078101c0740350162404085c0010510741d45152000c00b01d9024003c00444100310b0304090540e0814688010f000007603c802c442c41c907040741c814001407415407110b201c0c040c085e82c428005140c0703500703400c41803004840c3c80c1c1d846404113a0600042c41940b00082007072521450b0189070105030000b913141d5051602c007051009594075860000c080c0003808005ca1408280d0b1352414104000541e03c03800c010150241c2e0707015203170141c0100010000300c065450008002c02000c0d03e95140503a03203845d410540d0300641c0410740301d031b51519403811450030144001c25039109003e860302c20516003250794204101083c0030b601c1000701c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 428514766 1250 428513516 428513531
    0x3122007050a060e070303081e1b040f03031706190605180306090c090f06060f09030f01060b0c33280219030c0e1c080304050303040201020d080702030d 67
    0x1014000e00e800d26811040500020b08410301c9681d81e500700c1e03c410b500048c440f1001c0340d1400c10a442c0c0c51800018160380089903100d860080c8100b007810000387c074204004100009100040c2102000114000d4580000d00360040c4807442e04600c000300b40e07a11440b0354032140031041c0d10038003000060307445c42c0c6042a20355020301c212901034a03c14014940c03610a6108200e811080018000c81101081c0c1780c007101c40d1205ca079a484841c1c403d84480703a100e5411300c00740555035501c1026010f0072100078226007104101150640c21074802e5044044441400112452440d404000d2070440d10b0034440f001141f00444454101560442240c4d4901c0d2003c480115881c01f00301842c00000d64004c1410340e400ba004004540020360008007014080c005d041c0c8100318031030180c0b20b811000c1d00d1326125a0101c501c403008000100d5514240055450f042258080c041b81c124005540725030300c03840043d956420103000180c504807183c035280c000c020f034403420880b54580c0803080e621840110900441c260 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 428516016 1250 428514766 428514773
    0x3060c03060a0302030a0f02031c090b07080403060510050a050307030804140a2301090510020c0919320106210621060b1c030e0a050a0b030403122007 66
    0x2c030355102a5043c0302e0041c40000380712040d0038036840075108808444644004a0960b10105181c050b040e001c980c1c104000c00c115207030000200307000b40c1300d0308800380741c80d44a950300002c4131815640d00c85135410841d81409a420007588030750140804a0003058074926545d6025094807641c040c1d9540c085841a031001c1544480340310030007520101e41d120421000104102d403c0d162200c030320500003000ca000002c0e56052034401d01c84a900e081d03001d04000a106020b00a814902030104140e83c0000011792003050031911400307409580f40112840c42440b9601d0b08141403a12061860300c01c10310b200101302c0e01e40c000364810556014a40300304c1284406c60104001058180c2c0498040c40003291138103840102d0304188102c0500c541410401a810b0f9000d02c100c400680010b013011300c501207020f00109002d102c0424031814020200f604040d15075021039080329a5900003048030b0000b0061008042d00315800944540c14040d0812504100d603031000110a5900080c1100c00000101181030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 428517266 1250 428516016 428516029
    0x403080f06191a070f080307090504090b0a18020a120615060f0f020c091e09010c08070309060e0d020f121c2f0a0908010e03030402040507180f090b060903060c0306 72
    0x401c0c0e0443c9580c02d42c03048601b80380b156039100f112440005544400040b030a0704e00342c4a020700c01e03508240915001c1d59001c502100404041c44000d20303c2e8403e1199000598030b0401c050b010300b1000e2080440660207203000810b4030201e43c0c040e40d00c0f00100009105c41c4d42d120a400400801da80341000042810341e50903420211106a425001f080c00d00400a00070860b12440b50765000c0110812140da440c1600301d822a044440740c9800503080b0004580d9680c4a904031002860007982c00082c0b20b90360b07441ca940b03000a074050120258204400148075440c041c8941e09101444038805842c0510750014100b0101c0c0c00e038505540142d0340c905404008d048001318030508289180204854086983c0740e050075041619a200081c940c503031b0200313403290180102840c6440100065040d600c482c0d0800020b007000420040410500c0c0c28078003a011880d498000c0280100050714040909242c040c4c4142d86280302240d0003410104810000c41d20001803017544200c41c036605d5610303070700c810000409 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 428518516 1250 428517266 428517277
    0x120601080403230717070507030212010b09040f0506070f080c031b0304050f06130317040f1b1a03060315090708011d010f060b0301030803040215030403080f06191a 72
    0x5518550021036404283c080c0004d01c01180100400d090b82408a0740d02d051721710032801e0003070594015403410401424940d081c10381244403440003041600851000c6000b088003198103948074a40682e4203070a0103400c3c002c142d0041403502e41400440c80c5d10b40050034450b4007801c082e080c030000200045108110174a0f5000c025080311365207582e82001d090044ea1200d400364203404030700900010405042401c03440280042d803503100d55840701c0003403100c11460349005005850f080450540000029a0003002d03003602d401c0c240e880d9101a00f0101c4c195100380c9002d080d00d41d000c02c00c000744030741c07a54005065548103100031003c0406541d1403041d40d0604035107a102c005550300b4803042c190b480100380412040e909254000308000b24000c0464815682c481c851041101002c00c01070000c20304000003503901c00d00162a62100444c802a11580c07a4811541680002c1030101170151103400c00000a40061080b41d9014016580b0102444201000e00c180c0504520303c41c040c88c180007400d016900c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 428519766 1250 428518516 428518547
    0x20102071e0b0708091b03030f070f14060408030f0402030c0310020a03270308070201110d090b130b15030f030406050903101a040504020609100306080d020102120601080403 76
    0x51030a0301806034039081c1030910000c40d880050100066902486400d0052103a88001d0040046140d03c800680c5420709200700107416020421519100c0c030b1b030340002040007034407440a0480c0e00c01d0a01700360340c02c1540c0105100c80c41c0c001c40c1c140004245803009994011243d003e400c040c94546100103442c0c2107903100b203a034060248800010454000307501810100045490502440700c003d56014a13100c180c4802000c001081042040464890a6040e9000c1400d0000141c1c060500326002e10a42000c03071584543c0b61207030032a0040040b8401c03040d030042e00c64441514a0925560740f080460300c010310307000c1a40036540c903519056604001c0345603c0211003054039071f19078581c0302c001c00903403058030a20300030320800321001909400340c800c041d8001c000580c04c00300c80d03500070208005010f0240c002e82e4440802e100405140e5a02c442e039204502075928001512031906442a041c050540c10340c0c803d5900c10b100b140d000d18040c01000741d00040910b842c0d10325540724902506e0902c0100e5100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 428521016 1250 428519766 428519783
    0x20c0f0f0307090b10030504020a030f0311010207080403030e19270207120f020316060c05041701050f0c040e0402040c030e031b06060619120b040c08060a050f060f0a02010207 77
    0x40c48894030707440140b031304000380da16041e15412454260141c0700140c40083d006400b121003040414044030b81d40050034070901e001c801c91888050100c0c00c1e03801510040c0c1703000ca0000740030010503411206003039403494281c556600346580442040b1184241d4030442848821100385e1429030200500288a1102e0840c01151295840c0c2070141c1c241c02000c10790310101e0704022403040c2e028000070984281c0c0407140c9100c04100510fa568070081d0400484601c1804805d01010548840480d40742107401441000014649484842c50015407005454036a051b001000b080c0254442913841c60303070203901034501051241b43d070700c4128001e1041c2038002d20140000301d9040c0e2040f4880f00c00002c2c418a6908840480c0c50300c004000b917170310400c2003484a00e03510b2001e90b44c0d640d003c1c0401c090001c00c1042c0004860f82c80101080903079401800007000a420b000c06c003c0d0354a85028640040c003419510220868248004a40c0b07901c900030303d00c9040040400e1074070750903100350105ca5903241e014106 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 428522266 1250 428521016 428521019
    0x708010f0e0c031f020a090e01150f050a020706050705150412110c0d060c02120c0127020a1a0408011e0f0e2107050727050403020c0f0f0307 62
    0xc54014201c00300c00301c01034011085004003038540040c1c00140c4260f034190915030398008102400084d80410340d04814041c51300400245510000b003071034020b10031034404040c000d4060800800d10040c036101c403424440144000c20a0300e03070000d00d40c400e4400600b4510356801c9541010b07468006800d41da080f03203c079850104001c0101d0404000c4504c140c0d910b03000e04100030444215201c01c00d03422400d400c00c07080c048140206500d50000324101e072081c0181d07002d0070f5042c0748680f448c1e0b11011303005885a4481440c03076651a100c0c0000ba000d20700b01c00c2d001c1054116640010300c0f21000344904d5a810108080613140240307030004a80003003200b0402085080000301e6046210020481c8101c940c034a8018403081885040c02100c44e1003003e000070302528203200100c0c00c4400000034120441580074003c40e030000c0c1c2c00b0060b2030041e01020b4010b80340c1039100e083e0a0901c4601540c2103007034030b0400c4240070000b50002072180e403140c0704036038007071490b4040c2011505102c01ca0112903030504c5130000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 428523516 1250 428522266 428522291
    0x30e121221070201060308090f0402120a0b010f0203090a0608181005040b0609040b0105091b12040209060321070303110d060609170c1002030c1b040f0b0d060e070801 73
    0x20712400c0c04a0a0000d00d1040c0e039608070076822030b0a20311020740141e10030000003550f8a400114a101d860b0003c10050070203013451004c450199080318071048a0781d88070240c83d5150b822040d940350310340c0301e803005500e4401c82134081204e040103841010203100d84080800c1c1c0c1c0720350351a0301e51424000c00040759180f082031801180a00b400b510103545a000b0100441c007641002d46159200c0c54110a0040f01a440c060501c00c1004000b45035545911201003504142e060304401030241c003020032120349150030140100084814050100c03407083e84048641c80c2e003903d4010715915074812025101d03807240894202070340031701850085100c248400285401034440ba42c1d00090a0341c209580e000c1c0072640792503110002c0840c0c01e43e41380d0b1a0b80403401d00300c0d0324070303003425440010315440c410341e1708000d01c0614061411661a14060071141c58240040041c1018030426540a00c1050284040c0d00303010003164010303040311800361580d91a40c14013042034a00b0411100100040002000074004221 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 428524766 1250 428523516 428523547
    0xf06021303080d050f01140319060b0d0f02091501020a2004111b010b0310020d06090905030c0f010b100e0102070e01140118050109050105070609060f020a020c0409030e1212 76
    0x71217011903071600100100b01c1e0400b0401984d602d0001500078000c44400c44440003814103900c2d42140d4180d01c80703061441e10b07241c2c2083c0d481024072401345002c403802030b44104551880d000300b540c08007030540201f41c285030713a0004200903050303000710050f0000c560a81c5007022407824940990317007150400c3ca00d0030f80603040e90014400004100f0282d0b00300c2c000700805d1402d032401980340340d81c16800041c0703410042040c1d500500044000b600c000600031780c1d4042441c03e540d0042015582e5420228125440c0308007400581c504aa244008004030940c010005448040f13140c07525040000c040c030b1024890740208691400b0f4001c0c0c10503100d80f90313500ca041d0b40c410701000c1e03a2980043d810980021545030701184030000e03604141c40b030070241d604107001191180c2200d001a680541c83d08030210224070300744601c60075442d104901503900d0080b040041d00d071100c24503005010f2407402c00c40704007003030b440003000d0740c14042112a884081d03042c034902807609900c40021000500001008200038480c0c4c1e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 428526016 1250 428524766 428524771
    0x302120c030a0b1f260f12040f09020f0a0e1c111302030f0117100c0507020f030a02030604060b0a0314070e012106020f0403050a110301060f030f06021303080d05 71
    0x840c0381002030031550520900d8000ca128400e510100741d64040840485e40341c01084a040c86406c4803188141e02e504a482c14010320902ea245540025003448011300d001c8180c006800c404a007545090f070b0320401c10000740300d210450070800225581002a55443c12a603148802240001109508043c104800044244050780c1c4c0301d0740c1d0300428600b0014043c004e0b07034410f405000036140300b40c3c82c0403a02c3c1c0340601c5041042100340100b00c114480255203115650406d40590341c1c50780c44030000d01c1030113001c3c82250440c520030b50240100c800103940c00071714a540150b0007240441c4410072030300404e490705441d4000030068030194100100b41c0200249140440b429804640001d0b641e80d0343c20035504960552000c01201c200082a001c00d082d0b4000740603d4140705030651030141d0700d442c1c050030421512001c0311850101100c807921840d00340511009000c0f460406481c8a00c0c5540d040c016a1303800030700404440e0013141c110b56800740e03a0071142c011070304408070940c0c40080b12220300090004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 428527266 1250 428526016 428526031
    0x6053a0209102402100c05070503030711060106091223030408250608070503040804030c12170307050a080901020c0303040305070b0708060d02060c010b06040f0303021203100302120c030a0b 83
    0x1540c07150f56040780120f00062241e18580c002e442545074000c48080617090b82c11079078041c020b0400401000640070002140b2074071659542c0c06d1000725802d801030a044042c5d008404104103813105200c10070091385e01d084602c1d48860ba100c141600e0f002950025041c035140300341c084c0008075001070840b0f0085400540c0e42405540600c5007421544901d80036016806002c000405013000585801d0140c4000c43e0828050030300c480c201039890b0380d51a4601d200340c02120141100d100b501c0308004041034500f0455841c141103500394941440010414001c0d41c120408012a420116080e0328080d81100c001716002c0060320b0f03483c50702e42405805c07a402400c04458900d03413940014140351141c507616009010042025442030f0240d000c00c1039980241005419030355990109002903512000200010700d07000c0c0d100c500c03440c65402d0282c20004007024030918031a0810412540d805690700400c1501c0e4101d84101201078031a980514201c003102c48070b40c140c850310b0003800a1000348050103210380354 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 428528516 1250 428527266 428527289
    0xc0915180f04051003121b030e10020f030313061d0604200310020d0e0a11010f031a1207120c14040219050904090807080403030306053a020910 63
    0x741c250901c02150f800f112070141c0514014014000505800c1100f074081440e0f24120340c101c520000c0b012108a4881e2003217021030b10080400740c2e242031540390f40200c071000e800035000007040f2042e45500e03880002d10b20000341910702100f5003000703d0703680200f6408cc95286005181030707001c0b0f0b001d40d0f6400f00399801e841e050341210041500d000c03041901884204043c0180c110380c441813141402940160208000311910743c00380b420214020010610142d003d121000c024840d05c0c400546049084c4260f84105800d25210140c00a1f10921003443d000050700d1100300034241d44a103034100b800d0780d08a10711000982d07000005100384000038006446921031003491035407244081100f00d104564244441400004c41181d01a0194014154001c8082d0021820b42c8031651341200680c0f140108880e000c00c0481d051081c1030f4180700d4030010b001c0c01c1d10000c0480840a460500701d40c15208049050703901020720f03107100c0b48030001c904c00180d4040e00001c040d00309501d003100c01030f41e5405800b02142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 428529766 1250 428528516 428528539
    0x806180a060f240c02011e09030213090c0b0705160609050a050d0f1709030a0302010f0e06040314030a0b100e01020c030c0105040314031b0a1a010e0c091518 69
    0x22010410201c4101481d008020f512410715425101d403c000c40341a07052010b07040c0d142810030302285403082e46085070340e608040c1034210b10400803003a00010300300c2e0981d4602124900018080c0365040203488070300c80c1e603545504491510364a0981e800e003c0e109206141c00e400506075030401c111005803841150601c084d123448005019104091281c0541540c89100100000c02c040c590325400303128030868468641004207011a00c0c2118004e070840040c2c5d55030707035440c40c48203803480341c03004c0f503500040509101d08042d03c006040b000d0103c103004004a00001280c4107a046a01c01c3c45c0030302d000751a900302d66602640191400d011b009256025000d40a41d01071146000300c0c00304e9007010161251418282140c075040301d0303410788545014403403104010040c040c8001003040b14541d10341e2001030a180320f40d440d10103100c89016100c2d0868030b0300200144924011102c40c00e6100740d81800c1280c59240c41c41c00500c03240301c005400d00c1d0b00f550001d17800065440310390a4505241c0c1c20340380580b0f040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 428531016 1250 428529766 428529779
    0xc031201150311040b09031203190608070302030309090c0702270906010b0a0e06040515070c061b060209040b0a03030201051e10030b060310050a05070e010c030f0806180a060f 77
    0x490200d0403c00600c0c03403c003c140302c51000c00024020280c000b40403039100141074104a141a40f01780c48105072082546001084c54000d40900303005003100d40041e0004a142d94003080c0d80e4041d501c5064810386e403010010310440070600a40c0d8000c2e40003484101d121404000c9403241c01100f0140301211642c2d040080c00103080020142d040780c1c9c0400d0940d203810b255140440382000842002580114100700c00181969005440b00d6249030811031160f071600640307000c581140b41c03039000800303205030000c0c0f485c0f070300c9810811842d413140c0142026a40303800c00800103005160305103400b139210020328404000c0c180c0c1584014482e40caa000e4519200d14000c960709101002150035410000042c4c07030620003d460380b1011a08504041c1c1160105041002040113584c03045a51200300303941c0f101000023290b402032413108219030a08145001181c140c034024511903a0001140510120f5004a000303a1910001661901a01c41410401d0304008054001820b118801c0e040d1401400d240400d18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 428532266 1250 428531016 428531021
    0x110117070f08130c0806101d0a020313050f01050f09010b0a031214040306140a05010b120c0c0a06061409090706081302061612051c09080c0312011503 66
    0x914081e1141c00c84416000c07030440700640020501d6812100700c2010000144040070808003614000001d00f0301c0e0324260a2054140120341d10120a8101250a0190341c240714400142c021140c04005a07603591601c041850800040b00010300c10301c40e590a81d99880410343c4801e00804042d103180f1480e03210050900e00b138401e24494140d20003030170042007002900300d45a01d1071203046410404044e0300c4200100c142c0d50080e90046d22076a4403900700c28400a00344a60317a5000d00305003010001941030a070841303028020202ca203901103d40c0c8011940c415540800c2d200240105400c880c03078185a4034054000d41000d04c1000c9001920007030089861030b021402c00d00c16401c610007400064a0568200c4100c44c1c040c10310381204803010590390140c1c0324200240b1004581d0300002120201c0ca02c0c01410b04410801c2c40c108220040c80704000d40f00741114445145d041c403c40c04202c550070740c10304114030310031120490564800000d05044d40340003d107519040701e03d000d581e070400500404080c2c0a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 428533516 1250 428532266 428532271
    0x1d04180f0308310c0e0f01090c0503150d14031c0b0603012d050303070b01060e01090b0f09010203120405280b1b0912030306132313050604110117 64
    0xe1420f80401d192a41c920920018202c0c1e000e02c200711040c03907981d0305180d81900181c651420103c4070744014048180c542c042c40000c150b0b01e261103491840c0006003d0703400c1c000081d6a501c00d00541002c0b00078044840c030700c0761400300c1c080c09803691880d030703004c010210f81148041c00800c1814100b10758202c0c5428801e484c12a6003c0e806640090800602c515012214411107040303907039410b0340418592010800fa1440718400c81d408125941040b10207008031300d0444859040054050003132296141000589080f000c1c1c16081903101e030034140050342940203c1500c5c0d088042c0c50800c0005001d0005a0b0840c90300c030300c0c4002c06400c40c500c0a0700515111401000c4c04584a00000c107403410560440304082103007900c40e4904040000c400103a26406c0701080d809290b00c080103000c901d140c54250160f070216000001c210680d4080c01d05401e0668013098004000b8040c4005411925080105100c69078002c0a07241240351600d064506500c00000090024480d4180c800901006c100c6490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 428534766 1250 428533516 428533561
    0x611041401020f100209060d09080d0605030a0f0212120309010609050105010914090a060914070f0504030c0e1506160506101d07020c1306140102030a1d04180f0308 72
    0x402c0460001003101a500c1449a150010410023008824862510400601c14418800284e40e82d4955807102c0655125821a0f4840d0700300000200009400d41d1080e0412035041d02c10060484402080c07a041c4400a0f10030460140008200920140e0641c40481076820800f41044641d80b20401140c40d640340d802003140e40c850902004a07146841741155a012428810205086403518490b50550b591501c0d2005541c6011061000d8190010030100d0725450f0f5217041c0e0300700f17491601c0304200005240315260490304c084012070124a030304030b0748111626010303115a0799090240b00510030b100f1040c4082d155402243d0201c1e079410815111070084441e02104d82001389011041c2d00304c0141e0151990040d8414000401d00c2501c8800d42032221203580d880c00200685007480200001c9100103116046400400c402c071252034020020b06c5c20400a110040c0380c107403004010900030030b08208407110014003c03a00e50208081d000c00300c001941302e40d50b002c00c2905d0b911510894501d80c1c07604d80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 428536016 1250 428534766 428534773
    0x11b23161413021c0f1a0102011107140109050a0b041506060c0305090a030204050a0b04051f03122c0f0d0b0a2003040609050d050903070e0403020a0611041401020f 72
    0x418208002c0d0094241c0d019050035104d03440041442641c21a00810000d03c5055150a5110181076228840d00c40b115800c0c0000c2c8035001803500c21070f88038852420000c00d8045c4081241d00c00750000d6109600c2240e000d8215164840281000320740750400300c0702200c4c6107450140250210070540a42421981b041c0c0703c698004586550079903143c0c00c020145500b03d6069280000940c0c1d0742d0098a008100f48800003450489203014002a6007004001c5151940c1c48000c0c0c51130740119034080b20072030360001100703843c0c1c40701c0d16022592810215042c04120320400d500f40e50b0200e682070440e080c03500071641030314551000c0b024456220948440a0315292503800000d02c0300000d034020401000e00001003c064040000038503085070000d5405540c040d40d0745900500304042002800b46c0ca450b9402c04d242480d17108030000b66200118001c11241010083c04a003c040c020000907111541c428014800d81c01442040010fa401070322419640f114a800f00d89035550000c034150b0403041110016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 428537266 1250 428536016 428536039
    0x721020a12030923030d050c01060b030112020f0a08030a050d2a0807020c03071805060a0b071104020903010e060631022d0702041505011b231614 64
    0x4e030301030044101c4140348481003410840045517010701c500340070a002d0391503075500e4001144400d0300f100e000781c00c0b013545404200014849003404540c00068141d040300d4980700084040086200511180c0c040e18181c40f000c54503004032038100303014284103240703600100500c03180d03074140d078440510f10000c4002001041c070044c001d05110311540f41d413240490044941406640c40031078940125135200c088265112030101c1c070085000c1c094160050b0045030f0040106003030010307aa405204440005250012182807011240c4890701912680383c8014000c005558411704000d4030344404a0740680302f1003000e4039600d070084503a0a0507003000e60307811030b150101100783d008100951007000c45810902000f071244010f003040314200588007004030302c4152076a440d84140001da9050000c80000c0d082c0401050201d03982c07183c000c3c0030074490481c0a8031480004d09040c64a10f5000101c1c648034141010b95030792001000880f4400c8900c5441100781e851780c0d54006842d02c028656149a010540a20 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 428538516 1250 428537266 428537279
    0x1207030b10080403270f0b040e13051c0207030c090c0e03160909110405010f21151a1201020a020f0106050d0209070306150905011d03060c0c0721020a120309 69
    0x40020b400080880806172151501003031a044222507008098030030740003d041c00b88001d01d40340725810403104641c80038800d0715955200d0b100c40410301e05000710801901d400d0a4076208200d42070013180c004450303d220640300c400d00300c00b921030540c0d04d50100d03e440c200b002c0c01d820002590149400c2100c06052518240310a00d40901101d07001955500c180d049181010341c0c451050302e000b007a034050040c4400c3d1820b007113400300c46000d0a055140c040c1c5a0030500c0803402040f168000c0e402a0440082d012111620103264500c110301040e410826490080c0e03004001540180710004154088030035020720841d00e142603441c1e40c014142c0050041e692580141412150300d900100c05081c0844e11640320f88050f0300c5004500ca1020010364106420000303947c1000114510b03c1c0409a00e0b103c00001c00007107a80c1e004050a440b4400310b0025010414810512480d005080100840c40c88280c0e100451241700881135000d0344600804840002d9410049010505003580f54584c1c108003031a00d503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 428539766 1250 428538516 428538557
    0x503100e0a02091905010503061309060c080603070b071214130305010b0f1219030c0812040c05060a080c030c040308070506071713020d030309060e0a0b0702012a051207030b10080403 80
    0x1c0014030140d2210b501e100003d33114040c1d07241e0b060003640c0c0c0a00914210003010b103000e10903804010680c5080103402d000c01c024050281c103200da9410315049040603ca004c0c070f86845811004c2140882e0020080204401901703d803800140441310f446280c401c0d2010050b460b58150b141c0189036000b0b02030038800d400403003903007640180a414111120a01ca480701c8481b580b007001508042420360b42040304202d9a488400041e0070140c4134182401443c000c085c1800340081c14655504001100290300b03200c001c0c04032805982c0c843d44940c0c0700c1109142c06507407800c00703070b0301e074000f00d260b02402881018040000f98455504041c0e5030694540d00c0d0280511030740d00f008150700b056210f02503a000724840340600c6180b08524001000308000500301b440030034901901ca00210390411504001e00e01c10340300941e030003142000310b0a0300328824a0042e180d91007806003841181130384038108105c0980561200c80051410358088080c484c000c541100d0b019401c480c004e01040e11844140384842100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 428541016 1250 428539766 428539789
    0xd0810081009060b060412020a090e10051b040603020c0106170307110103060e04140c2d06070c121403160b18030c0c011215060503100e0a0209190501050306 69
    0xca83c00501c0c1c0000030085802d543c416040000c0192082010b002103041c43c40b10131005107080c072020000140850480c90f01c2e280c80c43c0b00c23030b2102921072001c20026814150b2a01ca2000b12900061b40c4661301c00c0c0c0540071350010032940031654a0000c00098148040985070f580c0ea1103400614a08501c6946070b84044480801301d80c10155114004100000410100e0380180d001d0300790507507400c000028403898581c01c00729540c09542c19151503510001e0501001d2443c803c1a880000c81078400b101051082c0038080000e0104c80302a0000101c00307405800c40d03461180207800c4094403ca901d005550b40340f00d004d002d03151007980040c44c40003259641800c0364000003002c440c031441c5007281c541d02d403950300302c083c0c0e03d08142c00090301c00034190780000519800b0748108601748050300110880d52260340300c5101c1d040030711400200141b0249100340d0350001408540d07042d600c0f02d00340307444108020f41060894900410011091054440b0712054810449805969080c5559540c106014002101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 428542266 1250 428541016 428541023
    0x50c10091511010f05090d0e150a0c051606020d020d1d061204050106060306050a0f03020f032103040b0a14190e01091a010f030807060903140c0d0810081009 69
    0x400c410414500b080c01040803190240c1004101414039024540c1400300920551041c000420440304584c0c8400c00400140340c15403000c140ca4008441d415105001a4500100240100c080d88080008400e02e00c4d41a51a41d41c2250905513041c40f090340c1d00c80030020840045030504c100e19018284124030742420704c0000d8030160424280000b40c00d15400286c80441c4c4a0b5110b450501c001541807081c0401001c2c200d9002d02800d16200c4680c801048501001c2e006c0c42c504440b220b41500c0070006540305034680b443c000c0350216500e001364526001a02c0444085456202094510a09000304440741d041c003618200030341c9503020000d01404e0f5420581594544940210a410400388a00d40d091401040004150641001c0c01505681e05070006103841c141d83ca001d00c042840b20701a202080d03031052001031040003908007901c91803a000c040f6841c2800000d00e41403c5000400d0100490510b034440780342c039885100000441074054001d514043e40303c0d0f002860a0b00c201d42101c40041d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 428543516 1250 428542266 428542277
    0x20315030303100918150c03050705090105030a09020f0a0303050403060c051207110f15100f0803030a02090607081b0615031519090302030c0f0303040f1b0503030c0a050c100915 78
    0x7030b0b990b14003039044a11110006d905d50384910302d0030b0113071301070160550007901d9280151420b05254006007003408003500b480405c81e076940e0200c0864072015404142c456001308210101d603924a401406035206020460b007460a00c2e0445ea8074a00440564001030044078105901c0d0391440412520600c0051380550307a80320310030202040060901c1904418008106000202e00d0117550355a45441654486803c5010741e800030407c007003001c01500d0f00a085001d01607604d000300400162180155100644001030009507001003505e07501113070707015070b15010982e0701999030088080d403101090315107550190013203c60103410304030444e2101e5115a400106141c040c01c90701750b0400319224940304901580c80007441d01c500701401c0040d41c1808076000000c6d4554035040c1d440c4400501c4844000f4000e528103e80513000b03008420060003d060090220703038940e0025030b1041d90b52594802c00ba507850044203030b2110359042100e001001e068068843c0d9464902d48081c804011301d810101c6410080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 428544766 1250 428543516 428543561
    0x20306060f16020604081605100f050c030f12040201030e06061f030e0717060906070c080714060415060602030405300f030711030109030e0f010504030c0305010203150303031009 78
    0x244d40c0e80c0900040e00d020b000a0040d0007003074055000442094000c43e1040039059600100207a102e019101701d030190f0b00d030894842d802100300c45d20754041c56801d002401c502152030202d03200c6610b860352046000740da06100703506050850503280e05d01a1381e900c0d0401036800944102c0b00c0b000d20340d00c144501a103000a0900b8140305080e09014640e0000c06203402c1e003030a04001040d0410540c2e400c441b9503409050316041541010f0000b414020000b0601c5c04041044400c2c03040b500c0100c841d41d45580c09848a41c070707261400700b41030820710181c07004192a0447c04107941c7c2c07001060300e0a03200080e013482d0140c060f80c1103580c251819694900003800d02c001200c0f040c1142805242d00860a020045440710110b25043c0d01c100e0407500054040ea140980041c0400d80c00b0840361754015090320607016032400303840100d80324407da13000075100304180f80300082000415801503114200c840141303251485420b0415440c0c3c481a42d02c0300607110724180c28040d8410b50741c07020104820050326101244c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 428546016 1250 428544766 428544769
    0x70c050c270a09030f08010f180207150e01110c030306060c1e0a02090f070804060c021908040302040b030106030f060b0f10080907050910090509010f09080a030c03020306060f1602 79
    0x210382221080c2402c0d4070741940304101908100004007182c4282040152581400300902c0303040b4003442804a580f0185c0d40b0300107010f40e20f030b04a8503201e4110010306160441c1d81c100300081d04040c04103a84961030120900006a030440a0b00c5500c019100554030b591a250f040213400d800695100c1070600606050328401c20b00401c2d84482038210101402e401d10300390040000c0d07108014801d09100301400b0401c501c00e83d0203400d030f0781d0081e0700035400103082e0b8005408a140410304008072800103841c9042c0b2050101c0d90001c4c0003184d1084a007400150104e0041c142a501c052000901e82406481c1001c00078545412180b800d00c8050b12802a0850741400a4190080007121101241d0303040148a002d400900121024001c1524181d0a5003000044401c46001c00e1040e000115a00d00104010500a41100134003201801043c0803070050346c142910f180e88904107070000310b4a00a404481c0d28040e009403403003a1801003805041030340c440740100f900e9005c003035a5410620181c004c640103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 428547266 1250 428546016 428546089
    0x120b030c0607050d140703170709050a0b0c160b07080f0d060b07020f030c1f02070b0a02010e0706020607050a0507020118560c07060206060108070c050c 67
    0x1020300600042903081e135040c0e0060008200f1402441d8a880304003c420080303034021040280b04074051103200410b5503402c004849800082c0c120f251306c40c0d4031040015454801d00b001d00a1404040e060326145843c01003020340221452040316101c8809000e400c0200d00c0540250403001708460396a4600546d002d00d005c02c41381560840d20ba1110082000c00c10f41c01d00500f029034401c010380080003d8003000e00021003941c035030104011800403070b01e90400390b980b090001034010402e00d1001501c606504030301a0203070207243e510140360300c03400b080010701c28400038803640a0303c103d0b00c0385850407902c000c0c2209c0940c0000c8069040c8040351640d0150310113a013202e40e0046c201e0f108460400440c0500060709000c950000c1410302500b03500451404400041a0500e12100036850f0005c150801441829029840500c0410301403500009207054021622621481090b6910031092b03803985401c0d03940c00d04103800a08107501485069445c0d04201142c16040010710380078803451181741148070403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 428548516 1250 428547266 428547277
    0x201050c06070c140f060a050c07050604080c1c050d0c0e091807050f090604020c010603051009110108040f15061226070b040305180a1403060a050106120b030c06 71
    0x41c80502050f801d20604989101580c10008041c001d0340000300c5205994400141c840b0342e51680d1500800e44888588080302c1100e64014103a900500e006c0c20014100d401c900c04600075030041504810b0901c01038500b4985444d00c81d01c440f410f10326824042002401d51705014410f102211040060070360319400348a20848500f40003850501c001a0707460709040c040d5000314014100000540c403103580740460300340d00c414152801604d44c15a2280507025144036400649140202c14601700c46c05140d40200524500800c05100110400401141d8005040f1009041110100d02d41000a00310b10812941e041c3c500d02e010888503242d940a28001c0040131089a20141e61a5405840780900a9074003090403004480ca007041115110140303030200050005003000400110540745407100020380440c039101404040d6000e8039070700090541203034006104d11903c968000a50304400d6801414181c4035130365034840c4000242c90910000e840c40c4280340307a0600030b6000001807901c1e10301c080c3c01e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 428549766 1250 428548516 428548531
    0x2315040605210d080709120203070504020f03090105010e01060c0f020d050706120e0d02071208041e05042901031a031015060207060c1101050c07151404210201050c06 73
    0x100e050742c6501d10b150420341c0d0300c42018844104100071649410610120440c6e20780580480c031880303148006810008c9541100354020b1002c80e41c00414a07108000d18441c8000c030000700170300d07603c5001e0304040781e0003446034000040c030072030303d14000503000c019881802c0d20180c01c1c61020305107a40d0b6641010b00075006080010700044c4100c50134503443c041e440b48540d080303014000200b000e060003501c0e043c0d50b0140500f002081e00e4090200040f20048400910400f084040501c1d41a020240159109d2040da4411781c10301e1035411844c01080d11040ca400100700010780892686401076014280741d00c40000072220b01c140304102c0c0c4e00c0900c9080ca9880c000c4a001031100c1c66601211081d0402d40c10080c21980110b01c240801604071500684407034224091a40034071201d00100c5052060b5020741500b0f003e82da9000840c0c680e0a69028950071250325101c1d0240b052001c8a203c0f80140e02c50000702c1207400036a076443e8035081039001e44030350062603c4c62a00303014058031382c0317000d8056a000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 428551016 1250 428549766 428549809
    0x30d140702120d020733091806150206150907050d050f0403030e03120114040603140106030b010b070c050906030102210106080714180102030d09152315040605 70
    0x3440f07182d5041c440000074201480080d485013621001207039410440307070400340024030700701c111001035401581e0210003000800b5924080007194868240a0103c600c40c2c444100003100e101c40300c042c004591a84105000300e520a5000b4880040110540c1e02034000b100f07000041052400c6a6043e000726841505140100c1c807160815142c020201d0f81c04018141c2690428000c948118001c030718202d045035016040904071a01c0000050024543d5610040101c5084245905943ca040d0846030880b40a03606500450780d07640d0041d91184201c00c0e0041580ca5064002c0c006d5103132003403a094200d0b8018000506003404032901e015000c0c041460032907052080c0300100201c0707078400c03d81da62000451401d1110402450b0150701640611a801c0d03178898240f25411009274400c0082c1d8247c801d10b98000c0c4446150f5080c940300705071062180b00581b03410702202001429904e84a243d4030542100d101d002075403440c2250004440801c6250380c400e445400016182c1e441090b11421200000e660 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 428552266 1250 428551016 428551033
    0x16081c050405070f05130b03010b090a0c09090e120c01020405090415050601020c060301060c02010e0907031505040b0d020d0618030e041406010f0c0201020115060e0a14030d14070212 80
    0x40c0f49840e68540c8403a1011070088002e10581e1034210040d034000c00725072030200b0072456a0300060b0150030b0462351190055040d0041100c884102e03003002032200150348807a035000740c85d807000009840c120048560140d102602403200341000c14000d200c80240840014141030729003002a80703001c41540c0170b076004400b00c04482c4800c49070340b0401d0341001d0f0034001000b8440313000c004210503000500c500f10074095203007181c4040d64040c0c0010400342d240108034080520b00b030280178009207032480401d183c0320140c83d008a03113401c003445000300404004043d44001c011940c2081084610034800311040c50311200c01c55144010003d140c42c2c0785109445508a0f240303418180710485801c001503404c00d400c8101071204a036044403900305c03000c203a4601143d43d803000e400140d024000900c1142c481c5400400e00103251a4001c03612030990303804070785d0707000066515504084a0707800032807440d07856040203201510403030040c900614145045400c241c18190f65800040301d08900d0091010382d604400030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 428553516 1250 428552266 428552273
    0xb0604180e060a021306030507080a0507050d0c02030a091a030c0306030a12120506090f040b1815041202070b161a0403391205040f0312032016081c0504 67
    0x2205d002d8030302407400300094a8007040041400401604014250b903aa4001c01c0360648100704440c403a800080e02031100350b404840080d560360290340b0303038000907104803000320f001d0b413060184c0d1241d85448441b990860701e6500340c4013503603400600025803520031410503000090128144c1c866000d100d0300c4140c460800300d4492015200000c1038644602c08076002c0118001c3c1d41002030b41c1003500302050340b402c0c2e542d2064294049607a640a54003130f21a4250328418507034042030552080b403007450b091420904040c000da079600060700600d40e0030f59007404030a4a940e500750f51120b8190080c082c04500340121440703a1807002c000e980a4000030021490140d600614090a041c1e65860504a04d201140301c000c641f2a905103401c007d118000407201c400803a4892820b543c050013400001c14000d5690b031401c0341044044081010110f418201c518505814402c192011001000f400310300d4821000049403002404100440700c2202c00c5c00708411507074090703c1405034034600300c038001a503062508 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 428554766 1250 428553516 428553547
    0x515030a050609060d06050c0f0708040807080a1a1b040612060510020a0305091f080415021218100c091e03080f0309010906090b06130b0604180e060a02 67
    0xc100b180288510028402a40c0b9070b20f2803048510b80101d000680c40d114004050302912030620110070005010546a00f406035400050045a02c4c030350071140556621a2040d4440c820514044e04162044c1e1083e1948000c00c150319500810940c001c482e0504020280a55508540c11000000d081e0102500c0410010b03c52040a480c089540c0340c0350503615840251354080481c40101003145c04154504240c4a000d01506040c021101503d0507140e10403005003242d80450701928041019042d10b803c4540b24822a544000f82d01d01100302c640c0c076506030210380b451000c008100340c42240d00d1200e000880d880392004405069450001c0e40b8500032030714481c3e00c800c44140c0d0401c0113403107040001924500c00c54035459400b2140580329551400c0d518010642c05401900c054200b010740400c0001d000d4602e449568201c82d0380da410311542014a080350303d07142c01c00350021410003040c01248a500c1d048d817a0402510404035039007000d40c01440c2880802e0350b00c01d5036160041031500c2d4101200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 428556016 1250 428554766 428554771
    0x1a04120e0d050607030e0c1309050d0801030218070c02210708070b04060c0f0605040c05090f10091d300307020624100c17180405060a0515030a05 64
    0x31590740245240580b903150b110720003d440c0205040d51031140002021082c001e051a450000b00059400000601c50304003900c000c40c2c044649002c0c2e01d800581603070045070303a24162500580850444940485103241041000c1e100c0c070300313000c4400308000042c0c0e2041480400c0141000903885054a0315030b40d1031400099070020070803600580414003600f44c084003502c08440c0f0f03a14288110b909607042640b40b102d0950350240c03405082104000611500701e64100c225a4165120030840d40c2c1c103400006541d10903100501c3e00e002044040003411a03a4010010000740240f20041c101c2c28030309030070300e040704400312400c03050300c0e08030082040008500e8040c10340c003520711803a00e03510344043c0003510b0b07100040900c038100003a10a52070140d00504200e41110001a00c6607000c44c007540d0b00604080c0500fa42110100d105050302c0c1205902141520701d03240c09800c0d1040c0030800402004090100140f481740c0001c0940000035503656803008540440007450105a546e0030582e40300130959000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 428557266 1250 428556016 428556019
    0xa02071a070f050721050a020904031e0203031b0a020a032d09080111030103030f051309060b0c0f032b0e030324010f0f180e01140108090d0804020d1a04120e 69
    0x4000c1740003c0358006ca1030710711255044071404000c2d61280f90541d00e26130000c49404100c05901c1000c0010b68001005600841c502e9505421100c60310254055520030300140c640180c001c2801000041d000c1c1030191041d1036810400501c1c50440d00007081c0c1c580c200120500016100c680402c4075050a101d0f0020b42c040000f4282e207107604640303016041c00c000005050401c44009407039a40c00054002d035402030a40c2c0d13135081c46480d80c1c8010003401e54101c0d540e0107545001da03074107074201150000300b103804c084010f03200850260030343c1444450022103414184a0070340c407944290441c54051004601c2180c80020300c0301005142c01d101a240c085a480aa05202203401c607880d002e904100080f84950075841c0c4290341051510b00260380d0181075000929000c040000413440725468010030017080310a0381c1d035040a80c0e400e26220781e0361a6420010300414103440c0400c0260420404144000d17016519a071014442a007804000300c0003110250f07030141030f0882071580c69900c1900114110030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 428558516 1250 428557266 428557319
    0x1b0306151c2009060c030c01090614070c030905041112041a09060103020604140f030a050601080d05040b0414031504080306040e0318011b0807080301090b01050a02071a070f0507 78
    0x4010020846a100c0c03d44190320888001c1441180b80c0004c00c200e5856500c114001d000b108501c1c9014006881d12203801c0e0341802c0140000354502c0c2c4241d5840e418150141d4801249070f14100600001781140b481464040d60100304801c0700c1000c074258a8055440346d03d070104546000c00b614103c00101404010302c07034000d0310041015944d4003042c3d0701619141d806042111100700d002840f0b040d602e10415030180295044c603800c0c040301080181c12505c5140944031521401c88080304c052007203000d24024a00c09101c2440152144034144c05408000303011120f040803604103100d0302000407181200c0425001013000500e00b05402071080b0001c9020041d42800341240c810381d9800380400c882c0f4108940384510079000703a040c0c201d10b10760325002050b07550f8030601c42c280f001150307209024510b119801c14030840c21a500c0340c0c0440f520074070198060254207040c10f804190481411641c4001c01c0c40900129011910382c0481c1e80d0381610800040007494504444030307440701d20350900e144034240e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 428559766 1250 428558516 428558561
    0x1b090501051206010503070504030209130b0c0405031209061201181109090420040e060a06050a0312081e011508060307050a0e061807020607080f1b0306151c 69
    0x111140340b40c2c004509080540e01e0b65510041224980684d40c0080e42c004005000d024508041068043c1c1150180c505601d459641c04803080543c843d5220700342e09940709400c1100b40c00b0200000e809038000c004e0502d4903103a5071180d840800328080e001994442c48980050310300c000c00e44254140031490703e030700700d040192600000e90440801040500320880c1505801400c0301010890924118001c1040060101d180074590762101c00315003220009140c04004034661400e4189842140d84c800d600400d20f0444410031204900f000e40141000c09150007040c140c00c40001d03945001c1d000d49155000c078003041040003005103102500c01402900030b071600380125221034580600782e840400c0200540d4450304082010407041c048440074030103402c41842809030f800f052450040c0000c0d541c82c10b0319240c002400000800c155071020000c03881c0c003495050810200055540700000030104120000d205109a0140c0d0000040510003450306c0b11010345031000d03100e5880051845400482ca06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 428561016 1250 428559766 428559787
    0x150207030c05010305060a03050115050f0306011a16021c15060e0c0906090405040b16050f0702010e0d050a030513060c0c03170d0212010302010906030218221b09050105 74
    0x10380101c40c1051740750350005c0c819860300c00e101c1d0002d6030301c40005c01c1607000342803602031440300030300070f41d841401c400000c26210300d40060614160391a400340c0380850100404400c809030b0015562070100d043d902020b402596442081015603804071401d810320f4010b07407400b040c1a4001400154401c1c0c50503500b44260800940b0345540b262819141a5540885800084081c01400110347c0d00c2402c000070002001558103c1030300031a0090400c101d00c82403a08292100d010710654000c1c44a0184020400342d8428129030302c1c52b90707004c1c0424011540300c1d11500d00f00744000c00c041e808a03000240d01e03551400d02b11849801403120b403506000a0045584a1020920340d00c000303000350149011108855620104440ea0001050401c640d910b404626000d2000000d2001760b000c02e030501c0c1c001070300e24000c0c000c070380d00415090640021210040200014541e41411309441042c025005a040860504c500c01f07540504080c0c1b04000200300310001e00c1d008541e04400c0c1000310074010710400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 428562266 1250 428561016 428561033
    0x2030307170619090903030e1c0c0206090409032a05060406020c1203040303090317010b070212010e0a030504080106061103182d03011406060403021c02100915020703 73
    0x1e0300200c2286045039114040081e00c541120055900810010580003d4240c4280e01c0441d920f8460307202400001034006102d0b44580c14a45415640005020800c6503d44203204800b40d041c4003c00b80c41c10940c0c000c010404403010408120040383c124200d800030507000e110001e1106070300c040b4107020a205555201e44400000e400103015075000705496000250a111031840000d1461280d0b480c0c0c81d150030f004000c0c0480110540118401303460000340706507200c0a2605039916030300554a0300c5290790903c120880d403076010204c19507031542d0581000806102304607026003c1d0742c919880f40c0c1800d200c0d9086515643c000014403c003a010b0488054000c0151040e2600801c0203402810b031b0303c0e0124001003010780d21005074031900e4985501190012072080e8502d501030b0006c0181203480c082890031081c05030381079a44900d081c4800c01c0113240c801811201220b0804482c1c2c03101006a0128041a02186182c00400c0c00c0d802c092001c8060080740510060442c801040140d1450300c40d60007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 428563516 1250 428562266 428562287
    0x8010b1306081513060c0f080c0909070f020a0b190b03070e04080c0f030409020a020c15160204020403170903060a0513030804020d0c0326041a03040c0b03101502030307 74
    0x2d05034203c00028298030200031450500c1908400c050005d1151600000c02600180881c94040303040503011a551504080980302030480280c05e000346511500720903585c5400a0b41d00504500c100d1074201c00080340b806890303005001580d88a82825800c0d01d490f01510818660702c1d0095121480c100f10500301c0c0108150413503080039000d03a654026030002810040c00000e40c0e02540b1000600140d114120b5006103640c480650a0301c2c800c071160000c01110035100c040b0600741c54010f1056032841021048281d0181d88001c1c070051500e583c81c0c1d00c0c02250510486489c10300ea60200380b111300c5080c05d010050703100c01c00c03080801541c508164548418115038001504111320715002408540720150000c1200760044805940d8990380e02d010404403071003500b540002401041c2d060300c2282040300b40d405840000314001c2041525001140d100d800007881540c00403100600010840c1d4020011402340b5000000c08070010304204003401e80c91814405082158001c20400403599480207070b111 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 428564766 1250 428563516 428563543
    0x20c0607050306030a080703020d08090d020a060c020f191e0b01090b040204080f011512050a080310120506010f170303071d13051009050f0a150f08010b130608 70
    0x80c2c80b5114040424a040031503040209400703c00940c210616400050070030b14014156500706017655036008058403112450000c402582c0f0058910700019080d400192010a0078811900c01126100040345002c2c050f036923140039205034008020500010b404440d1241000c0140c5014401c200c0e0b9801380c0d661814440c8600007940c40d00850031940e6680c04a8000340038600132124900c0c81d50f2440340c020980b0344581c440200d070110001440e4140164214049038000c0050310b038030349841e10740c19003c2d40010103d030782581d10814003081c14040350f440018003502400090825605110041080900541101000c900e2000360042200400411241e00500b24500b00110b24105a4410390840070b00202c41d5010514000c03043c507094842d841280314440c2c6504285000d641d070790b40a4110380e010340b0301895841c05400090841000780e0009045180d5000440056031350b0307034003d5074001000b5041804d8a94513194861480e1500c229841840d218958040005a02e00340005035141d4045002c117 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 428566016 1250 428564766 428564777
    0x13030507060908030406140105090903070209101509030510060f05010e2d090c131203020a0c3c1505040302102318060306220501050112020c0607 64
    0x4003004550303000344034a0b40c0c0c40044180c0b2810715203440310282444070900e192130505840000341070700c4e0040c1c0c003d0040d8000380146241c2545a028000d5102e802418101000c8501c5c800168280d04002c00c10700200b5070f69240c04000b400c1d0710389113040c01215144035240b01d091000600070138642c2c200b02001c0703035024204001030307440941c00309903022a0f44c1c840141c0450f54000c040003843c64880f0810070b080040ba5001c20301c1d40e51180e500d0550242d400285822500e0100622038540d6840811420a011380111402c0c0d0a10b0354501c0116259034000b5840400f10324440541c90316492511034064007042513544960910070314014802d4940e01c80c0c18095811407600b070310428000c008490155030043c114954480d80381e000642403400169090350b0301c1c001c2041d0050081c42010030344910b4028514400383c0400681c0c1040400c3c1c10290082e503200c148100100b03000442c007030b403070300054031412008140740d0b25080000d0040c46120090808c81030040082809001000c1290b591125079030504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 428567266 1250 428566016 428566027
    0x3050c1e030109060c030b04050f0a05070203040806040c0f08030c0a030e0607080f0301050a120f030507150507030501080c010f02061f0b0c010b0a140d020103111306090914130305 79
    0x6800d40e040301022150503518014809051200c00d400c07903000c860701520280403814032070003884101d81c4100d0702000300e40300380004100715a14980086070000802d03c1243d0400c1e84941020782000c40540301100c0c0f2502e440000c0100b6111004540c00800c0030b2000b46041c1580c50400c19103910458000404210a5a446001e20b035900410307104c8254019140d03d403111410a8400c01030b62003800341a00c1a00c40801c005408002c00100b90b99180d0b004900f40c045c2c1e140c41e80c098a19400040080340c001c400c0a150160141c000d21800d40320b44850340d0081055494540c0c0c25081c05c022845c0c043c100608800035001c090380002d0010780191f4400c020f104003854940384040403000c82d400604031a070303001503589001d940c150045000d4800448aa0101300e070340341c070b00f4104401c070302500c282c00010780b5001201640c004e40c040f1020361501c41c0d05501d000e4804d00d64198890f00703034008902080d020a0140040780d03080c410303c109003000ca8003507001803e045801440d0302d65280001000c00c44009030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 428568516 1250 428567266 428567299
    0x9061608040f05160902030a1b09030602030402040b1f03060b090f0f030703051e06070e0a150c12031a0f180907090f05061314070c060605120d11010603050c 69
    0x3510f0315040e00d50442c858190705c0708043c00103507205480c503c507140d060040000172558201c0551600c14910b4071910141072861350f41c40c01079080100146c0e88250345440700c506640312520000c20a8020511380102011800e0014003117800700c1d04494031515040c0602c5030a80c80d0030399152001c2c2e20484084888111140010346402c0c041c0d0001841c40c0122461042c0c0c040c40c00303101001c0c506203c001c2e52119502c140c0200d40c0301200461440e4010340300041000307034500e8243e0304112025540303481c000f04180740d00c03007a40107081d40d401c4000003507075102d03104052040f0014440c00b5030000c86d041c51045a0160000e221b80c1c401c01c908005183e500d401103010030200304141001800f014070b040c46110303403503800007000341400ca4038a805000841e041c06404140c0344120015500f1603400c19135542c842d0f880459010040e00c02c03c903501e07507484078080f41c43c0d81d030f441900c12a1841300d80104410112030000404a00c01414560350580c1005010300c0041d00c046601ca603100420354030210010314000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 428569766 1250 428568516 428568523
    0x62601051509310804080d02031309181209060e01080f040209060d06050718080609070b0a11010f0f0e0304030b07050906120f040506091204091503080d020309061608040f05 76
    0x41103a036403d581d100b0740000b044038020240086940510558a441202090580c0c0764414081f07248008500c030324051020b20744550006101804884a2420b0f00045549407210f440301d0b2003079440480e21040041020382d900070740000d0340380020f1070a2311190515071081881d111029000911581403c8006000c5841d19400d000c2d03000d800040500c42030601039406414030a000080d40141d04900c140424007480c0011401d004a0044000b421218030f0300c0c05050b0950031030b500710802c101895580680403002400341400401d540680007518101d203440e00c1e0101c482c40002b100c9260000d0100700082070114011036070040c01800c0c210380c0e0b40d03000800112144620074050301c80005142c240310a600500c241180300318405c104a54540d2580304815503a0400d01c044a640000e041000703104643c2c464110032001507139410003003141516980c81e02c20329081070f03400611442c0d0100404c0208441049080e03080110001800c5102d60a030314024024240140041c0100e48030031111006c100342003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 428571016 1250 428569766 428569831
    0x70203090120011104031104050a0b0f091b1201172b201b0102010e0c06070204020408030c060a060b07020109060e0a0305030a171b040509040303062601051509 70
    0x4581107a51a81c80c0c1c03074110704a10050407164010b5207040c002404020107417140c440d040400500c8041c040141104008030074dd0f000701030380c2e00f081f02c0410f4000070052590140403105068803560681e90304100880b40800f120000035541680002920080101005001c895182d580c0030058090f101d00d950a44070104030492003400c094859490840c03103030300481c0c244404110000078030034403100103004a0036103080d400c2100d095005410010130078a44003000385200742c40500b002d810315680e5400c1c1ca041d074000c088100b409030801001c10030740a1340d9120742d101604807882c1560403ca80c640000700288818015441445000389444000da614441064000c42d40305040b80d80c0d030300e20190000c2101009560b12018244000041010070f145c1c4001c402401c00c0d20b0317403001d052516010420240a0002d8025010305680d49030200e0000d00f43e1441902840c03680022651038412444003d003155401899401a800005400429a512241015041140d8880c81c25508015401c50001d03030880c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 428572266 1250 428571016 428571041
    0x11071a0a0209100c030206073b0405041101142a0c15090406050f151303050a030f0801080d020703110406080115050f060309030331060f0507020309012001 68
    0xc00d59015940c8001e00b00b051522076420344489231500d52056401440100c00381030881310404158001d0584020101c03403400054000301c0390410b022010a044900135a02a1061035800384040940d5800429054400c048240740c030389048401c200015504a50f001a214500900d0303000d20324001080014045641300204413000440c5200c101105d10360040b43c070140514181032000600c2d181c001201071000101500049607038481042441488d030100c416090380c4404200b021000c510b04102411241d0712a0311503d141c4040740c640502503520503400503500c0d40c4610900c56107242e000c2144070480b50311403035141c0c09805034400a0080c1c01c0c9a00030914a44c0707000c41e2610114240710081d42110740070b540c60101da100741c03030900a0714441110406103560040012905040300c3c0c0014110314104503a07040c1c6004456900c002007a100e81c007055902c43d0f159034060581420510a480d00814503000942c5480e1038640081e20041804503c0d4004403000c000b0440440c50030f40003005002103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 428573516 1250 428572266 428572279
    0x7050415090f0f051f090203040f050f0a051b0102190303020c100615080f0114060d060312030501090510060302070809060c1501050a030c030f1410020c0111071a0a0209 74
    0x4031041c010006000343c425049225050801080300c03080c01c5118900013150351210300501600704100e81d4081e5202500807284400342481200104a060001384c2403c190000a0184510a420300c1f074600100341ca0b0b420a5240d40040105084c1e030005021141d0188650b086820310041e03003001d4000f80200b0760317005494040c07000050081e2055a114905640c40c00000c00001c420b040710440d0503800032030b01007540c01e00d004014009920061010728100310000d05c51843d00c2000e5208009a8229a0040f12280e07103407000c6040d42a014040c0d54003404254030200300518000c880709101c2e0210340b180005155000071180140100c0c00c1c02c5590f0a400900510359035a9245401a0354098440181113011030f00000803440d860240d0303100c02182e4008010420030740c103685850300e048080340011905511704060800c100c078424480e0448445400000607240c90618a081d82982c4e20801c3c56010900104902000214420b5039046000d5441090040c0c2d656680b030710318020b204101910f9840031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 428574766 1250 428573516 428573531
    0x50d030e060406201b0105031b07060207060e06070e0d0212070618090b030715030b1e1503060607060b0a0e0c0a090501020a230c220b120705041509 65
    0x6412031040d80000d064a420034580a9480c4d080e01d40350003591503c400300c1d030096000b81010f9071155000d5a04a00c4419120449501c03541482c1d140c0d134840a0211061500481c159040c00228441c0e588040e9001018100625191500907c0954003d1180b440350166025000a54481111300c40c50501c0c41c1d02190b41c2e5a0b22490060001000000000d040c50041040854500c015005504080c3c1e0083c008020303160925005400e0105421004410140c3d10810000c0765a0703813540001000406940c0011040c10303040601c541800d00d04201440e0001c20024441c2980700c0d10100c0d01417a0f049100016800061000a20200305503800b01d6020300903901809141501d940003454081c816407540c524031550b41c40160707140e00c21004007a0242e603140d4800d00b82c00d82c040700340010f8882c1e1f4800b5110b0003400e5400044550a890a85615100c2002c5d40f11100b104140b1a02c0745c100d1041b280ea2504941a200c1990b5031800350003801d02507503e903000740c2c200c0582c0045140142050110078400e48 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 428576016 1250 428574766 428574779
    0xc010f0204052e0f2f070501090f140d020306010312021504020d021e06040b0c0f0c090103060e0a0803090319080c1e0412080706060509060a050d030e0604 68
    0xc1d005030150074452507400303401d01e2007464540c03101c8003c840b080d04402003808901c81c0640703c005080c1103000900c9040145101e1a03c4c511718030720140c21280612000490321181400d152000b590070250602000680c2031062800f002c4e9680c084844a00440341d00f00440320200c2c00e01100d200c2e009406104e00e200110420410b4603003541d680c2620390031940154822508000c0c482400d8030085d4100c14820f15030000b5003000d4469045a00750000f03000921400d8002082250b0304c0b941c440d00e00a0b20200e4804401e9000b4025003c42c0c5596100520301d843c030800000d141c01206101c0242001da841040729001c50f810b010f180942900302804a40b00d140141e140c5071250700070107070b50344030100034204002021b0145a185000768000e4a4040c03c050a5030151001100854804003000300284400038468018082c05801c042c494101c03141c5820981c07908a0545100360010340c480c480c800c04000c0251100309031b0b1030485104840004c00705595040c140c946403503600003981c103d20005004900c0b0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 428577266 1250 428576016 428576021
    0x6020316150615120504022206080f0d021204050a050d0314180301050f071b0f0507030507182009010e09010b04060f0201050c0a180801020304060f0509150c0a050c010f 74
    0xc020f0151a1040c481c02c003014050304990044070001d42c8041d10041024062401d49079603a146280610000340031601c0e0101d031460000c468181031712643c050092401d02c254140201030002c110038240384c0c1400d04101c0003d03091a05409058000c6800742941401d1520503105400c1d103005414080769a400d0700c41e800d0461000c4001441d01070740c244004a10010300403050903100e0961039031054103e403420508187e4004940c4020341c1c028110b0903044020900502c00b020046d4400c400800703246140c80040c21006280740c071201f480e6850a50714480e151070181c40350710003141c2800741640d81d130040b8005a6540c1010349460390808803007000413035034000c0400140143c4145803607441d201c08101c1001c901341d40040f9083c01550809010b00d84001d8028208402d05c0e4080070324480740280c80d4000582242c00842e425111507468480f0001400042d203e40740e0030039803e0b03018158600c0d45400400507811701400d00346144600241c0c0c045214030950a841140d406800207010405e81500c08001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 428578516 1250 428577266 428577299
    0x230060411010807090509060303132607080d0807032a1206050d0b0c0906030f01090b010f1707020319021f140a0209030a022e09060203161506 63
    0x400c84481c5101d0755096014407840362040940ea660000501d0410061202c680c1014120b00d415100900240f002d45000c20502c60107018402211003c800000200c18406900c1500079010b5402a8000303010307410001c1201444200142480c0d8083e84401c2000c4000741442028851844032a8078001000e204c60066958281c1196581045100004c014401214824480d490344010b105c00c0c103034009003c02e034400354404460048a07083c0a0840040b400c540e004442c650000d50f0454014400c0da03c040c854640d11000c203107002c604445030903501400300080c43c10080400c404a0b00021440340c4200115601c030800c0c041c0c1c1100f44d161400000e9a100403440018800b100d145642c1d4909103850711072180c40301e40d0591400311680712004004002e51018a8558141c05014005c3d03000d80ca4440d040c003c4a04491191000b40c17041c1c5484c40004101907016200708140410104040b44c0c0c00015141c1081405031400060411450058080c000254144d84d4643c1010030005121842483c481c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 428579766 1250 428578516 428578523
    0x414151903050415051e01061d1e0a0f030c09140601030f1b0f120207050c1509150301140d020a210f05071802040806070f0309050f030a0f11060402300604 68
    0x20440c0d80380e6500380e41189004801d01007047e41c148540302c080c6464150601e04500403002c0c0b04040c00c131440829091003054000c80310a002002d02001008ec444060f14002e0206110030000c07034860049000d141600500740c0c604140c1c4032117003000090035903031003983c210340c0411844090140002c400752060203440c541c44003140d104882c03034852001c180211000c80350f0140160440c2080001040039140f042150b00311a000103203d04013090700d84c41102080d619168040039100d62404402d0787c0300300a008909400f81e00703590310180060b02c405040750141c0301410088030326142d444030f103881c1d5444000409000c81069007802001d1180200b02c1d1b42c2580d83e0004001100d610071808407060384182c0c40b546090385d2081c000904920301c528488034a4491500e4041028481c680328646000d4040003c9086504000707403210200d030708045c2d00e440c818001d00b42014080b0400303c3e007036200d43d4000c00190203060103180005500030313450401031052244070a800000321561a015550303110468048 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 428581016 1250 428579766 428579821
    0x1060e0601090501080f0112080d0204060302040e0c070b0f130204180b100807090b040f0c0e0102060a18060f021b0106030203070b0708090f031002041415190305041505 74
    0x11405501c0b85c0c3d0032501c40c5000e01000c0d00607900e0300741c5100c50301910020035502c8680900a100001816000a02c01044070341d40258071541802c800d11024007020b040002c000c5000c0005600143c485101c0942c441441c404407240703540c40b062000c82d50341041100951040c036050100c1c0c9611100b0722811126405050405043d94541d802078251421500400909a1052004001c10240c0c0d802107848604007500c00302d2004042031401c0241d8010a00340702c00302c1d050301803d00c0300307590410425034040d0070300034103004440a00205030100e005080c0080d100e01e45840701040000740a070103c60843d01100d01030211410303207045840c001c00c10350000301c0c402e0045802c0090a83c1404007529030207030b003202001d840e00191400b04003000628034001900350151403a0503400b03250610152000303000c481d00c0305443c2031303044080140c40c03400f1070003550840c841802603550060035812451501c4015050000c0c940d02c0d41d0900140c6101c0842c030f0b0704a8181010100458415850380400701e4000b91000ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 428582266 1250 428581016 428581019
    0x190b060103290406171b0603060607140703020603010e100b1201120302100203070f09150503010e13020402030c0705010f050115180f0e0108070608010506120a0b0301060e060109 78
    0x11816160a002584080301e407400c081480c0228040c000c03018588002d100081603075540700340390590082480400e1752904000401281c2181c002e41c0070300080400c035074003891468000c000440c107018000b805000252805107580c010b07502041000051031f0018981d83e12507039510280c00401c9011504081c9110210030002109080e07141601c008540d044803203c2d40d40c0c09c0007400295480103e1046c1d0842c8a01c1011000701e0031107100a6000701915500e18403201d9510380094801d03e0036900140641e106070190580195100059070b043d180300b0f211000c000d84852903151540411380d000a03620610000134401d00c40c0e40310380100341181c8504024003400301040b0508003155800d104081c42c150030380c4c2121124900c81c2044544213004400c49850040d100c0321030030001907494100c0c000c013002241c0148404041001800006e01461400040560614010450f0360180444405c064925000801c0500301103801c5103400d4500070b0020040a03035070790103003041e515090b1106408108110030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 428583516 1250 428582266 428582269
    0x1806050118030c090b240c0c061303062c01092d03141b0c0306060604210201050408010c0c110411071b03120c02100504060c140f190b06 60
    0x2202040b01d80011030380d0700140c900310850000d000c1d001140c0b41d000c0010782d024080909040c0030503004a43e06040c1540320003142c08004c1c070700600c0c3c03001c2034800c0100780448003418540300c99210560f035209a01003101c1030700402540c3d0580860840d10101202010318903811071055100c0c44815000d0500d076103031241081500c0c40c01d001c141ea070001d941da02200c00310740403034014031142c82c1010388083c190b0700c1d2541c01925511000c07113031150940300780c21616031005145010000990080021500b0900d8286050050303c2d55003680842440300b085180b01c402c4c150780c020800c6d03c00408442c0000c0c86102c81c403480040121b9111b10080b501d8612401d481c20711410310b4030900f83c040c1d50800d600f130b1400405441e6001d002118502c9450f0b044403200f170110004200501d40300d00710001c0e803241a0210303028410441d2403654010040c08104080c0001c03c12154820015003860717402144410004108146c104e09100d41c018910419114200c1c402d141c14000c0c0b210046064090140c2070501d4a8000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 428584766 1250 428583516 428583557
    0x80709050103020403030c0b15120106092304110f1201050f091c0e0f0d1401050702190308040309030c08030703030e03210a0b030706110606040c12020f0418060501 72
    0x10240c001540c01c051f0f0f60018040403c9039802030020109127000d840701d0000603070311a6003100b0500159441d03010402c5203001c02d0054503020f8000700701d0407d200c2000381b0003145406008001030100c1d083d850685400e0b840d6883c0c1c07420380c0314014005030314443d10404481e020344001d031400c4400b0a5440c000030091030300441c1c0c10004c038404e0100020740e1641c5040803030341c2c03203807040c0d0303950384410b200e1a0301120383d44408061114a00c500240c00302c0c00d440810346070031610010700700015500b2580d00030000c1c2521002a2000690600300703504241c84034103003142c4811460708010300050000c20040781c0c0c001d001020b080558030a0781c050200000c418041501c034000e12008030401480300d04161950040400400c3d84480d40e1742c0d0004101c504940000c0c5005a0b5a02040108040c84041100180d05001c010b0b8000d00a407014060301c40d1115005016140303800042440580c04141c1101c1100c081049030020a8000301043c14030b203007004030100420680c0705803408900c1039040b80780b00ea4402c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 428586016 1250 428584766 428584769
    0x1921110d03051804020c070815010e0903090105070302010e07090b0a0512060c031308030a060e0a02090f060a0c061407030501170604060b270a0e010207170c0a020306070807090501030204 82
    0x181e44240c03c1140c0c3e0340e5a441941d0300e00703942e81d80c02038082c0300098180b501000200c006001542c000c210090302d1404d00c00707554106808c803d14242c1c00c42c0400540d403000008961070310b0030a182040c0d035885141030890042a001c0d49121160280f64030001d0080c10942100302d0011003180c2040d1900d036603900308443c051a641483d015078204900040100c0c12107405507601c0444001243d84800c410769070001c56500450314807900301d61350901407165a04500d103055202c0c40d5107104528201c603000018404e0012141114411000040c6c3d07840d00c2882514806111035004200b407050081c00030584801072000c036402c000091410000040490111171703820ba0f810175400203084d80c0e84864a40b98058108440c0e0b240e006140f42c5010000d041c0b2190b1034032280051025041141e00b0962070032429510f030b441140209a005004001c04108000078150320444182440c541c2c0c0c424982c4224281511000040d625001d40c41c06c00c5a655003200a40b84195802e9070b410004948850056040340520f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 428587266 1250 428586016 428586023
    0xc01020a02090903160317060a0506161103030d0515060304020a031511030a0c020115061d0a050d03021b1008010b18030f0f061605091921110d 63
    0x360000d80c09400d00c11000c070740140588056928112032101070641c0150020350450008188401d640706e09115001c0442e0003020031200080d0080ca0100011020700501001c11408603048901e0005c10442a13054528544043d050700e8441600388080c1c1c0003082d00303c03203020f01c054210710301e901c003071914108032480703a68020b01c040c3c0440c4c29038460b0314622a5600c07208440e40ea681021601002200020b507110300b40458004c40c0080c01404e000b400c0d03660112a100e100315408a0a03c03081d1b03000840454082d03000d0150302c900c0b0345814006000791900f50320103600204e941103070405165010540041500b0050b8881100e11080c205003e60f115060f558440007039810320040c040142c1e60001405403d110550300c0c444000c801300041d0400e40b2405160000e1f0703106030000252581e06002040d80607a4104c0b4480311003050010241807485000340b0240324507492080e01c00f5514415501001510140041c06030f070079001038400d002440007810a03034403c002409405203618000e010208000c0c1e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 428588516 1250 428587266 428587273
    0x1090b0c060c0f0f12160c05030f090f040203090601170309010806010318170c011d100e0a0f0f0c1211010305060a0503121b030f07080322060c020106080c0102 70
    0x4030301d103240c04503400146000e20200c604020a0420885000190500f00c059290424550418141680c91b039410b030035950050104640002022550120a0301e995059042519035610640000191482059412150300620101c00c3c00000c01c0c0000b98141600c02c00c400d060000c81c49000282ea4902551100070300003980c280000341d0310b502c0307034205100320800c1500c8645810380f2961485040d040700c1c2e0124072044004103400280200c01d0040b00038100130649246ca031103814528868560040680c3c0d0007646032680c4400842c0f08040120b12040e41e0041d907121081c142605e0007002041084900381e03032442c0d80b8a00440c0c140c15884005a440703500440d008142800d510041d000f030308008050030390081550780300241031f440501c1040b103045074905c071203681e403401030307010804518802c08640c030f00c0d03401130000c0070204210300b04a0750095086000a5140c0c1c3d5104032201c146460640280f0b02180a8a480c00410503560015415112150001d0280540f6804115903484c101b14850340140e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 428589766 1250 428588516 428588521
    0x512010203180312070c2f0f01050901170612030a0f0e01260c0d090317010609120b0c09040903110d05090d02060d0e0d0507030e0901060504090515100e01090b0c06 72
    0x1b03001c2c1510801c03061040600d048202501c031480460380c0019480f58000b01d015060800d80d47c901010a20f0352124242402d81c1001c02c07240000700300291a4009083c0b12448002280c0749507034003001d40c10350491090403203940e80c085c410f008040901f5007944d103000c02d0300540407840940c05441c100003111202498810340441d00501501c081c80b0142c588035000004000c08072614040380140005280291101840f149914620030800340301644407000304406110144005a078665030002440c0e080400281c59480c0c2a070028114442c01d07041591013803400201d18201500041c4001e91114200141c0d62410b1a1040980c3d50341b01e04501d255000348801c2c40c40d00107203005800790040440020707000507030030082100c1c1490080b2445003840840e6021490800b015170198101c02c00a00c1991004220b5141120180c864000d9009000c0025210780009140000c03d46100190110042051000816042005e0089490b000340240098440d12001c241a1190004c891009141000500d903071b9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 428591016 1250 428589766 428589781
    0x30801080d12050a0b0910050a080a0c0312090e0f011e08030a1409040c0305090616080412230309010b0a0b0a03020c030d0603050c010f080f06010f090512010203180312 74
    0x7010010003400c03805030b48120004451b11081545803044821940c1100c60f282050200314a040740c1d60b020081a5001e0201400041c18580c40c0c0c10445c1e610010407090b10703a401d04140c5402d41c56401803018080f0741e6040025440b10244080d04030341c1e507580701d21000b5030742d80283c0d001405a400b03a03000c141c1c8100130411440d4401d903a00840c1003003030340b03007642001368080000c0e080d18176039806280003940700c1090040820003130201b90b40001074030703018003884985044003078a020030080014144000c4041c01504590050200440c46a4480c121340e01613038040004031100e4000b40c0d142482503186ca006030105007010101d1038182e1f03074290321650500c084070404901950104510179460700050190118181030390040b44051441480a000e104e01d0710b400041400300705500700300c20840318400b803250001c814500b0680200003072808000080c44803006980805465200540101002c089400c2055041d800386001c0e03891038104000740b19011052035624045c045040503803c00100205940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 428592266 1250 428591016 428591021
    0x2010902130504210909050f041406040b07050d091a040b0105011d04020a0e150d0b010e060d0902150a050c070602070302030304140310110c070f0803120a020c0a0c03030801080d12 79
    0x404d011494040c040c96100c4201d4800d864054030072400401120050100700000d008108240d100f0200042000346030a4540444c003070310103426035003400b0300066405030545e2503030403000c22140c1010a0b000c6003603002101444000085506640000c5e85100110340b56206007029036030704283c400c09036034001080c410400254441112081446000b0300145025121280b40302403458107032080c0d54070391b529407044006949984065504200510b0000c40c440d5540c00b06032040c0240d50700d0700040c50415440400c00100482c0c0c2c40d0074401002107050301c60180c2c4140246100c09104094a041c2e80d5190b030305a84d180d61794003000b50301d50400d1005010300c140c688442101c20b4030090448190300c10a141c14003c43d03032214000310380d445001400480454080140d00b00070400a00d01c00c50107072800303000c0f54413402802c0c0d900034400102e1002c91824919078041d6002d0f40c00800aa440d07030039283c03520100760229803004074042000076000055000e4040b500306518a015150b0514880400403800d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 428593516 1250 428592266 428592323
    0xe0112080313290c04060c0807060f0510032325120b01242001020f040e06180403170402061209010204061407050309060703120c02010902130504 64
    0x100b00b544600100c0114000042c0c1c6480303042d080d02070b0a0601d022a0004544032001440b0181e03101c0104010440c070b070740c410005034850390054500d580f01c040d00e06c2c1040252159100c125201800c3c94140840706007404d1020080324401c078003a03230021155200d52225074401c0c030004030040d04070760002c501180300ca412a01d65025140c00b6840c5c0940c6a410a403c001d00314041500c640c1c0354100140f10310004584a403500702840e43c21180128121f260080c0049d001090784070002403000032042c2414025019130300392100d40c0c5602500c853310b880e51041a560200c42da24883c060034000390882d46400303181640034907016620f6040f140383c00c0051380030000002d4400c1303030004800c11035041111610b1010f240103d0b5a4800903954514100c001040d220301c1c02c140156880c0208204000600000115040e101060343e0142d10f4012508080c2d51405c181c16840000c541090340c0b4065060307040d0702c54180749100300c1b00740001e58101c04100d011541e04443c02841241d200d002110840b0081c0d50329072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 428594766 1250 428593516 428593531
    0x501031e08040803160c05011b14070f170c180136050a06062c06090a060801080607080f0403120b04020c0601030b0c13091503080712090e01120803 65
    0x1c1c942a60780034544e01e542e01c00510740e40c288007400e078410100b014030b660450080400340f800412080c4185400c004004083c8001006015401ea840f0202c0009002c1170000b0304005036101340031981d0f120b807640503907403210914529001c0c10070110801d14001d8880c10083d4038070b0594140e2a82804141e43c0804065804002103500e41c0c181d513a0340d202508400f40074a02c0c0c6207400b050604244910b00140e4009801c81014440c0300c074900075815060400c40304100c00340105420480c1d41c1f4501240c9103102c0c103000c81d42c11a400c4a000318025030012141c80c102d030082c0048409a83d600f22048941c0c070742c159100c07034903045030710301080200c1d100e1055000c10701540c1c180064400e030350200190890b482503e0340000e40d00050010024441c0c2680da482d0711031142d1000c0d91a01240c20540404c504250103040b001c143e440c0200300401d000442c011010b50b501001090707450100d800c0c094221010b2140d03850000b80702c082d000c500c4400b010701282c100e071690741800361140d0240e502d041c0c3c070750402001b18 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 428596016 1250 428594766 428594783
    0x25030201090b040609060e01020406050f091215040507050102030310092313050f0c0f0904240f0f060b0d090201050705030a0c12050403020a12080c100509010e010501031e 75
    0x1c1000c10144a41c0c2801248980c20000d8030745e0135450b0000c01e44803e1a09440681d1051100304102d68002d822100d61b01c0c0e6692243c0d6a030014800083c101c181181c204030032522074a45044110140440a28050b0307000d1000c0b54115550b4500480e568031089031050240480b4030780800c1100708540056490141c560347d45110340101e469980040c15084452504948184492100b4407400340200f003043d451240181903413034042c0c004600b5024180c0341d001d01034000c0340c0c00a004e01208010001c0001c25200000411590b12041a03000d803d0511090507500d140120b5101020301912a05044401645995040111140465000346100c900503414010f04210301030003d50240000d0200c003610f9114844c0088450811140001004500c0340612208101c188090395034041c80c00300310307400c2c3c10161003104503d18101e240c0d0300039040c03095100d10074042840c0c030300c03941600014880e4000c00001c01c151004584c038142a02c100b84005040070b44507201c42c4480c510050004000d45010b840d11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 428597122 1106 428596016 428596031
    0x2160c181103182a090f06090c0306030106031a01080c01050705060c1e03040f0203060907140609030316030305010302040609020c060609191a030607030225030201 72
    0x3a07500081c0240c0300300c0d8a10310030480e0140d02c0013040a000a4140d0354400614400040b0311428403071a040000902502c8107030105a1040200800e4140c55483e1030362859955840540a00c1c1c0654031214040041500e01c2801c4103403402c0418083c0f600d40c9060b6401b403c0007400c80c0303000d0420800b0420b84005c03600001e0010f802c46944d01c80c165840c80311598000306000051a003050100c0040308202c00e12500740310a4046900039030075108a907803a000f00c40d840d00428000d4030001e0350307200204011420072001400d840f0740080c5c1240e25181c450240c03000003801e403640c210006600c440c0181f0031410540035003001080030710410f6050801c1b065500351600c8000309440d00507240100080c00b81074141d401d00e5055980100c080107030b1710010700e229031541119601a402072080c1c50201d443c45110707108442d4a4001a03103060186418800d140c1c0645501c0361085d001c56485d10103 = true := by decide +kernel

theorem cover : BRFrame.Cov 428417266 428597122 := by
  have h0 := BRFrame.cov_init 428417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 428417266 ≤ n) (h2 : n < 428597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
