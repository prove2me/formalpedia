-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4517
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:52:28.804814+00:00
-- url     : https://prove2.me/submissions/cfca3b9d-8ebc-429f-b988-6dda0b4894a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 812230215 ≤ n < 812410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 812231465 1250 812230215 812230249
    0x706060e0a0b030607121d010c050a0216050105120414121c050702060415020c1606030b010c051b0d050f06090601080606030601030308150910090b030114010909050712030e 76
    0x5203003084140f0354803a240c3c0280d0555242e001c80d040c00d0900c0e41035007440100c1d03505801c65007000303109c034222a0448000c050741e160990171252005690309240309001c03032030701803180019010090b102d4801800c03564290024095101d980850604903031040c0b130100883c10420140002051a012032019580b80514441540d0414070151515a0000b034940e6002030000b0102020b030000c004c3c8070041c031f5040c0c900c4400040122509090600b00a0741850050701c201c1002074100300306014594407400c0c1b450900e40d84440102030203013281c01e1a10100c681b200d05036400003513441c0805c003c00c074104141d050240c038803c0506030758103180c0c540c20b00b400416004400c6030341c0040b00344144c40c0c0780003841030b04590b091710304400c054440b8016424003101c00c60819520030075136401d00006100210403030007112006282046406041c0301818240d61080c04405980b0740d202004022407034040c0c01c0482502d1144080d03401c403a80305c1d944200c44910300107041d00040c11400c000600c81c10803502007030313000c800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 812232715 1250 812231465 812231473
    0x90106020708120c033f040c051c0c03051e0a03080f0a0f02030a060f1205031204020f030d0908011b0804140a0215040e0c1204020f0301060b07030c0c120804030609080706060e0a0b03 80
    0xa0701c5035500d1020600c40c01303002b5840d000a00140c088030105184a01368001d2400030310f46e94905200e9622411816207134002c20b00c1820424015000180b206805c560540300d20301c0540e10039040326038030302c1c0c0180200c0d4010340711443d004c045889032005500ca01e0302c88200040c4a8100054045015102c1d00144160b074130055241012803000015614490b03000703003e12038181d0715403001c240d1644083c0011905807040c03104c1d0031f040c1600724101d0030648001000801041c01c1185400012044141c2d114011410340c10114010412481c540f560b0b811008080320a845000d44c08540000c0740c3e041c1030a80008041070174405250581e0909401c851480010f6040030091114504071a8010340000d100342014460b41c1c0c101c4d18290051401000c143c0341035511182c00e82006440c082c4c1019080310410000980450310414445d00141c0c03158010b01c07440c0c00c1034155641c2c00c0040104440a40d14a0010322245000070424020304003c1c4c42410900d60081c00c004510000356910900b40038400d0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 812233965 1250 812232715 812232721
    0x2120603010b010815150301090f0c02191e050d05030115030606090b21090a050c0a031101120e011805010506040b090c16060c05040302090106020708120c033f 70
    0x2a110310f0b02c6030030540816002d5a001e110100003103035544802118220124044000954191036034030420009007010000d00104500610480c1c0f0340581c03180dc102c0ea1201c0c81103100c04542140540c00d4522803042517011601f003507448076482c0c49426059a4006440000144140f003c00d8140007101e0165003001d0050a040c40c074042d0800d070845c040c001e20590049030700030034200314a00700c14103003590780c0440d02e0368104840a507844040c5072030156541d110705031244441d8108074034600100c03a0403a0894088030380030801141d0b000c5043c80d41141c21070703c460003900161401e1061040c802146140180c06801d103103400c17800e603480201003512031883d0154900032030702c0b4908034035841850303210001d680b1300d10210071900c180100170024180d90b1600d1107400f02250890014010381e0b008842c000c0d403603070740c1e01012130b9204414015000d07581c0000200a02d02070100b400b8000b8907a8510651342418807031250f042c4103100341c8003500c40170101c00129a01c50141005059501000c0703009250301c1e4a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 812235215 1250 812233965 812233967
    0xb1006020d05041512050403050d0b030a02090a0c020708010c021501090b03100c1103030c1b0307150f06030206220501030b010512040f020d05060601090b19110c03030a0302120603010b01 82
    0x3c055031044e02d000082001032004102d116601e42500b1810b803100130012814641002090b58005a8041c1c1c041803078140c44038403034540007030481c0d80254000c1c2428150f0b5281c0344c1150107004400c0680f07095114080340420303800c07004c0c005d850140500ba4002c00110440050034282c0c4981030303210300c81c66480d02e07229030165100030801c3c82c0080c0c000100486d0714002000c0484440654105000c19030202005000100310050001e04006e010540d002c40929588101591640b02d078681c004d00080300000e08030644c1e4041c0d00210800808400002401d990701d4000c00c1107680312445209602c0000d0000d00a1944d00026401c0680020f02c0c0800500380d112001802500c03d5141c50f0390b0545071900000c08110b50050700d244150350107400f04031050700d14030f040d03a0b4031001501c885004c5082e81ca4007245201125007038a02c8070707444a000b1030020f110600180c454a030020325922460080b0064940390340c07820801400c0700c8089540c010b94440843c06410040d00e0050003941c40303641801112482a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 812236465 1250 812235215 812235217
    0xa0b06071109181504210215041a01080a03021b0d02060d1b020d02071202281e05090c040608010b03070c020a0306020306042a0c110307030b1006020d05 67
    0x140a00341e6109069880d010b0086115001149491040d13128920b00d808807640380105450090b4440d0102584d104410548440c070100030448140040e446903001800804820208580142c081c0b2901c0710303085408643d4400800090700855203984c011880103042680c1003103100c203500790782c181d1001c0c4826001c00048504001c0302003c1e00c10300d03010400903281c800c1a408510028412500c0f072076546101400a51112050711003100540500072000a10701500c10328000781950040010101031035040c0c8130144100e4242090084290b0804080703082d11001c0102c0341e800198001c45600c1c14508010400000402800100750800511041207202d03004400a415140d003103112589030358800c0c000b01d41c1480c008001a43c017102c4c00400000717024023075000b140280c13015941030100015120303060a80c1300456500128040e5a1089650307001d101d0000191f03d1486980c10312240d900b0040020f1401c202a00151034444210050140b039503108000d4200a040383d0002c1c2070700001100014200d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 812237715 1250 812236465 812236493
    0x1513061d0f0a0903021005101a040b0301064a03011107020603040201110d0f09050f130203060307051201060f1508070c1e030e09090703021e0d0f05060a0b0607 70
    0x300300e443e01076520415000b4014060b070f4588543c0104503e107001114544444190b00ca00d1420f01c6030801c1c0d40d41a846a078003180c054520040d107540c5141d19099088606807903032990280486c00383c0c440700300c4189212a502443c450b0405090b443d02d5004044203440c06450020350f48281c0c580494030040090789030a403641da540494000b42c6a580b00d00041e1200450010a004180100314486240a0308030302c0d06441400d4a0750707124900703920341052080007482c9480655018011729501c012400d41600203640c0513602400f80c0380b0850b03584000c181504842c81250850365100c202c244041c102d5100140014080a031401c607002c4117620001c3c00e503050140940007080302d861034120078400760400081214007808900803100780203040040261003140006407040c00c084012514503480000c1c002c003940d40003081c426126840300e2002683c6005011003a0b003101e2408400e502040d00c41a0130701c803e40c015000707001d40307240c10181e200444c0d0141c82e0640c4603030b00a1008102042003402c441d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 812238965 1250 812237715 812237731
    0xb07050a1104061212080601030c0c150b04020a02011e050402090c0f0f07080307020d0e032e1b03060e0408030a02070203010b040606030e070503060106171513061d0f 73
    0x2200c030031541d0100707000d0000c6410651161200580c00790401050f0600c2d410b40749019610b8981c1501c800b0011010380c1c82500c01c81d0001215a40417401259800465402031800021f00081c065252004030782079811250304100541d54441c1000b00d0680d003050382c4030545880340010400382c40c05600282c19040054012014907001291440c540c141600c111100502e8001c02561038050915100d201640304580c41c00041c0a44440e4080c03c90007600810000807000b40501003269403010f031a0454420320030360105105001421484034180c501c941751000310028558044007842e1503002e03050719220340c0600124990382082101140c1c400c010b50b80c100c000d01e01c000da81c2d409036000007805072041c1001c01d03a2141c507220000850940503804017075000b05034800d40354407270b80c0c800030588c44000c2440707120080b5515148200c0e0040001782e85680c0006050040e00804403003030042400c400c18040d404000d241d41e9482030103481040250242c4041c00e04107600c6da02d203080d490040c100000070f40218 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 812240215 1250 812238965 812238983
    0x326010b0c0709020706020702030c011e1107051221190e03010207060e030d0605030c0a030204050606070f03050307120905070522050a050f06060c070b090604090c02160b07050a 78
    0x32981d5010711615004109031241591201c1c00713410b01d48003d40c0004812032280c4544501d01980f54060006030144503040e400401c90303124104801d41d00c040700312018070018060303804041596a40e41e610b10b8545402040205040c841045108202100c0307603641c001c0c8104188882c007280f00301d03032100c2c42482c5490729000060808903000710b40680148403009046506154440100700400805440d901035962800d000040da590b01303140c1c84004a4188582103c00900140094100781c0c11040d004240178041030726003001d5482d40c603c0d0080400040700040c60000512890344e500858201c0c0304c02920310100001c2d1042d50f2150381d034900c103102e950301070062541c4003c101014401c084048044095090285d03107403800c2c1000092070111140103400b40b040c80490441d081c2001a100f0f2100440010007aa078207080003050180c1108e0784080d03112034100404a003000007401442d9581c0000c3c0c005000c824819113030040c1c03042140d003103100d004105000b01e030003085001940541d42c9030803400e01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 812241465 1250 812240215 812240227
    0x3070c030512130506010b0f1902030f0d06091a0d11041104030f1a09060705070203010902130e0c040203090c0103111909060e0a060c02040b190f030326010b 69
    0x1a107060160003291008000400c00b0421a44400c81035100c400d07104d10f060722a103030b88604404149028503000020b0040d0107101c40781041d030440140c0c11300c2c916140116410007001c0900c00799154002c0d500f8032607c0342c9400d801c0148400d540558504000c05e0460155580090700c041246008a130601503c1d0084100001a058403240e00003804c08858205540d603c82d202e08100d0541c030f043d0101150460b07102d84641e40200400310385d550148008802520740fa0b250003504407159045036100340d07070656071000c0170310059032000d541c0e240d40d020302c0c85c0101d41021007240e11401d05050601d494021030040041101004003c1062141c0500908000600400c040400c049500800e8505916071002c6c1446810082d000344581048400329a10310107102c0c0c0344014000c55400310301c2140007240b2580b0b00e4070010320f0715410014442401030801b002c04181400c0001e0500703007642c00615146480c4506106040c0d000402000310a40002c4000c500d040750100103101030414400d61f55601e00205035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 812242715 1250 812241465 812241467
    0x105181303030902090a0c2c1009330c02031c0e100e100c0201050307050a030902151c140402190b04080102181806210316030e03070b03070c03 63
    0x31828144c000d01180c010b4544200104010910304410501052841c00100103002e00154200030051042c900b980c080d002e0b86091003e1070101420180600c44645c6c808117041c00740d000300740d0b04050742440550380b204116202103015690240e0650801a54040003005600c000032240196003e5618009540c00010002c0300c0741006440000e0b4814410801240c0a0340d000140b9451410129422209020036071019103001c640c20300001d000c00c0c0705100145003070b070150010f090001c4040c10081001451540010b09418404400725520103001c10303954510506e04030a4603070104180000c014000f03072020384000d0301100400081c0b050020401d20f80c44441c021044200815101d0350780d0351a50784403003289020b504400ea8040d51340480100d02c0001e480e19000302c102454012210020342c1d140d103000d100a80e0000c0c0409041001921007601304084100010501c0d034a01d0005890f1100341d0340750042045140c80ca03103a200e035028480900a2208440840e13401c510241841d894a03503117498 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 812243965 1250 812242715 812242721
    0xa030614180a09020603191803080c09011b0506010e06180a0c0203071b0e06010306061b080f04090207020406080106030308220f0b270703022206031406010518130303 73
    0x70340004000c4180466000502c00725030107414a0481441400c1404106481000d080d0750040c00140310140812f411014410040c60700314410702d0301c041d1011415050792004100070900301d9031548002c0c010402e08115050280e00001c017100c4942c0030360600795810f041c0c1c00c0c014180302420f6a0743c00c1001042c0d4000c20441701410741c80450561103029580c0da444940400b40305220946600c500010400d40c0700e8810740c0103030391540c2c90b10040c091b1009000e0999400381c8100700c1e00c0d039001300115078490040d00080c20013080705500141c3d40d20342030b206220035903030f882c0e1092007540c1c1051303070610020750865041a0302c55580c106200d01c0048503916082a00b012000c09040000c0701d031040b0083c403071145038013489401c2580c00158404800c00c10308684c01290307003400d44640c2210009000518010420b08000c0707041010160301d004501201d2021601207510840d1219002055001964400d002440c0100000c95054804407042c81c00c400b07110a00600300100d506a1044030010076002e54 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 812245215 1250 812243965 812243981
    0x809030f0d150b03040b0a05061813081c0e160e1b180910051f02151302030d0311090405090118082a030f0c030c01110a030614180a 58
    0x80c110102c40340c0e07400300e01002d5801035034207a451006060005814900c1030140a001c5c8001900c1004c5101c82880c1d2400a640301420072000021039504520106880300e003d822502858208801666090030007041124822080004c00b82c01c07541c102e1003441200b4241d8070444010b20580060340e0786100140303091050b9000500948103000c05e10391a81095030309541005001070b5280400f5849190f41e81e04020524031a40d548660155151720f40c89461614030504200745004441e0742d0b6074440c004441a03030003182c440c644200c98801880542c9420030007039101005c00d0404005011214960401c0e0f440b1b2034880c180503581342c001298418000750f10030780100061512100f000c043d64030346000a5030217000b140044d003803880240e42095924940b1a443000b47140900075454006c00182802c640d8020414180a9000070710034814074880030701902ca005080784210503a01c0801c420b0142c12078800f0b40080180030700283c5c24440d1a1121841840d24018103005100559503480304000904062 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 812246465 1250 812245215 812245241
    0xf030803040b06150c03030105040b01110c010e060705070914010b18011805060711012a060f0e06040c1a0901120f0b03030a0801050f1f03051e01240809030f0d 70
    0x641300c142e198041b0281d03050310030403282030206d082c1020044540015103c0009503a03008142c80707014941c0185010301040e40041c0416042810030340351181006515880004c3d1142c55400a90322101621a000d004d132141d040c64500b081076000416045040d4046860305126422041e181e044841e10380c030800901c40207154640d60b106502d01002d175154164201808128984a200410302d20040c600c050b01d4802e03d40c0801480740354440b4000b07082030381e03805a640c1c0d940e101c9003c505031041c000c0b02d00ca603000d420514421492b0052042078810860768071000840c040c07120302e0035a82d002d01914045110b00780007240c1d04166039040c10080c0141e4040e95810b2200042000505070010300f928104c560841d81c0318540101642441a13002c440200c203441d070180090f41d901524001da01481d0040200d0080c8142d403c50400c062260042c2a008059148042c136900c00c070840399034000002e081030b0b924060390700d401c107140070701e5a038040c0d0a075282d00c803e00815516414901c0f94813064000e11a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 812247715 1250 812246465 812246467
    0x90115023003071205060f030c09040204110a080f0a0b330a030c1206030c12050a0f06020c060915060d110d111201152606070e0102070f030803040b0615 67
    0x42100504114810b0403071002c01170400000410b80c0c03400004410341100050302501504031805c08001c056480100104e9105070303140d4406108000f60f0015140810240e10307500410708091880c4443d04200502d001c10040c100b0f044290541c403a505031f44401c01e520401032242c82c428164103111103421104000d0700d81d02c00b040003114181d154020205a11076500c5001c1156008036440c020760301540000740c042064540208003030440300003000b00d0f55000790180d0300d4000080d03417800450035001106840f4142c000c503409008034800d206054000800301c001700207240b00b0f0007e92014001c0108214880c4181511030810b00ca00041580000840207005036000a41881c204181402c801e0110303004800c5400540d45402052050711114001c4402d42172080740f51441d00e004641c00d040404c0405103046011a0640c0e0b0b0400480740181181d856419030300556000080ca40005540045200e8160306800c1001c101c0300c00c222900150080076150b800d03a664408a0446c843e1411305807031800d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 812248965 1250 812247715 812247721
    0x120813021e180f130215130e010509040f030f020307022e090e130c090f0f0b0102070501050708030601020c09100911031e040303200405090115023003 66
    0x210100e0145080720886900c614a40070002000c09480d088611246880c200f5000c2403050602c2e0828800c4144011301208a403840e81445000f1a080401c0041c40000c20301d01c01d01008d20b807454003901401d01900c000285240588449600020804000d001e01c103c0503c0b1114051090003101c40058000c3c03c4070030507040c6441c1c80e48414080250000741402080f903100b0625106080c2c41d0b0031500030400642d130070740f242110710347d403036041c07000845800f5401200043c8402c614011060190034290001400b4000109128281d03460782046c0e50454000c03c2040c4105c1e0781201c140d404460700107032a82d0300d9541e100c0061745820000811690700c85c407042d04103d44413948205c0c8400741c3d48601030a00c2114807070000d041044c0801d8640e154158203401c0079a07450080d04120641c024000d1402184403440c241c48507486a1104140e01c4085800140170300541c1860701c48603006000701103400b038183c004e440700251100306034220484543c0b41080c491021102c81c40364403009080c2080d1070b9541e41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 812250215 1250 812248965 812248999
    0x1061e08062715090106091e0906060810050a05060d02030a090b0133051c11040612050108060c03061011100906150810021b0706050304030909050412081302 69
    0xc9412103c240c0c0d140100c0b400e402080c10300510182c100e0f460b58842144903414100300300c06d400e511032440700c0c12481d44c000c00510101e55000300d50040006445403159802e10000307840c40030748243c2145024180441007000a0f40b5218221801502b12880050300d94880e452584090205940c0190511049c01c5c00231800d0302d18107002404d4841050103044003400210030818803126143c070700c100824010300182c03a1030392100249030340c0040540e00004810140c00b144c40b103d60043d400010019a00e10070140001c8010722440d800340280c0c1d00103003814034029044550324440202814040c031545c0070b801c1c00c414040c190004904004030241e9400c480c8810302d210003049204429560542021613200c114604030500d44103554120340600880003043c0c003268040d40c8008007000300707200c03c5000211030580c20301030900900000d696040c0d40f4241810000c01d500d0182d08902c400030725100a000020307040744066190005141841c01640d610302c0c861460481c0c0c1d00102a40102c1081043c005803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 812251465 1250 812250215 812250289
    0x30706050f13020112050603190803010504110306030d030c1205041b050603070c02040b030c030f03030106020f06070905040b0d06050406060608090d05122805070801061e0806 77
    0xa840d00c1e025544480e629100d1040503602090000390210300c8020816131105c800d0380040c5c0d80800042c080381d0303800304540c2c5c0a0f101e072100c442040d507900d0b50104c01409949054000c002034220800e80c13803800c600340b080010b500c651059000300241569010705050b220302540783e200d2041d4503041c04120510702802e00c84220300d0320b41c054101d00c44241c0340100c0c45140100503a030149030740307a640c003801210950a1000074144c9840d455810f02c107144000085a07001c0201e00e070010100710146032217516100020b80f90038515940c1e0302c0325811420401001d194807191a4044a0040b030703010928004010200c0d0142250f803001900035804c004c00c01c81488040e401080441d0991b945480c03195460150023521540008494400500100315184580c0900b034416500400c00c2c02d410104250003103128800484200d0180a46039151030800c501c19402000c10303030050005040100301c541c541c0b2445501700480c48000414020404007180042d211700740c80244890035685003249542918400c540c1c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 812252715 1250 812251465 812251471
    0x4050a0b13060b10020c01110705061606151206020f1c0e0601061d0d02041803020715050f0327190c050f0d14010e07030f0b07030c08062103070605 65
    0xc01ea003440e01d01421814182e40b500c20325a002d50142c111b4090b080011680b03034003810040440340c0308101c404a0b041e51071030000c3c217040340c00b1030300b030100d80d101e03443c00a050301c101c0100308903080100c2d1001c07c800e00c0c1e01f8201d151a290b00c0340e40103a80340c4101607091003900481c100c0001d18140c0c4074454176654200d90007600724050303500403104560f0741d4880441d80f122807046510703000d42c105a0071030aa410120b00b0012400d1000704081000210352044240211041d00c00360010703485920100918103c240e0f082c0c00c000864606145041007428400c070780c80c44080c10700d25602c00f440f4220718030585200f824842107078140d030a66400000b402003290318640900c1d001d031000c040591000905103088107800d004820040e006100344032040d2982c22140120025101a0b95240c01400540000602001c000f03180f20b201c0000c5144450300300582500c000810003400d1621307109840d900c5c25003049105600685c00c4130100208108480b00b110188011500f4174001d02c8085801801c10030182c0000c2c0c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 812253965 1250 812252715 812252723
    0x6051b0f2d0c100606050d020d090f1a01080c0603070f17040c1505040f0b0307171e090a0b01050906030a0b0a0b0405160c110105160f060b040204080c0904050a0b13 72
    0x8024144070200340708030340645c03280034041102040044d6260403660043c051002450000051100071922103000e90300a41004560f404038511600740c200300d0b440c1c2c2c01409880c0d0540103028030f000a00c041703621440064482d109001394151180946031059552440600e6420f60b41500c1c1e06051804505500e164000c0300182994801c1800035035104000b950203c0300c00942000313a4600d000300c0300701d895201510031001c02c902c2c0c5080c8030421a003490030600034032540800b403203650030100f03009040a802608c0e4496a4004000d6900072981c20028681034400885801030240c594000103481e0040010004103240f1004040160034400e6500141201009440c14407840c0d5032480c4080120440800000200d03068040110100300c800c2c45100005030103040040c54903402101b42200405444401c0712510101021802003100e035000d04403030781000343c905500340740c241007a0a81fa0039024014078000d019400c009420b100b01004203c1c621500b020b080b070704905103d07031280f01503811054196 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 812255215 1250 812253965 812253973
    0xf120e090a0b01081b09090c0403050c0409030507060b0f030f010506180907060509040b040905060613061206020c0a08040f06020d02071a03090705041806051b0f2d0c 73
    0x49034905903028002d00002e050755403103455520a880c020010314800d2595038050010b000480715a00e138100307128000d000d4034000549840c03440c50210f1038096103c0c0c006003e0b50500000d100021340140981d410319a1113080810422401004a40c09001e10b21142d90305d84100d03000c80703040320782c1980302138024a010f40e401c801688800e08004400c940c20380d0b40b50003560040030108a0031744984041d00c4607000041c0042203141105c0e0000302a5002188142e8058004009101841c07502002c110030182010314180321152404688000d82c200c4903402070030300e40d0001440c00f000c1d607040c405500c240d41e100d022943c0340d6868498440d010881d6000350005841025003c0d0500b42c00033415034201d80003403624103040c0399072801501180d01301505c801d0180c450010042400e0350399004150010302042c0d103814020000c2d0a100040da14041c00c101c4404e0417010b290b1420102c0341e0210307401c440760714a0a6a9030000c1039a151603c000c0d05040c001032401c84c0c90301801001001c002040b465601c4001c071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 812256465 1250 812255215 812255221
    0x80a11100e0c18130f020a0b0d1802032a040f09031709030304030c0323030a0b061804390305060102011814030d020408030901171e040f120e09 63
    0x120603d00225003c195140f20404002840014001c0c50401c02e54401d05a0081c280666404110304091603002942048000300340c028100c156480b4240030b89455030b110b0301c0854120b401180d112401610720f12103000040740d03060580d00b4005441800302c13401810811150800c401207400070f104410b402c4000406284050301c40c104c0b0b100200d0f00900303d0b04059851038030303607a88c2030b51440d40408007141031240b00030030b07120500003803090003190075803a0303081c00c0d81e074034110905008803400e801205203c1c407414010842c8200201d901323908c0c104401d80c0c0015030515141100ca8603080c1000002c1c02c08070f0302400084040682645a4403403102c0343c0c0741448240c81d0b010069003a142c8104c0c1940101c15002d450b113000c00c00480d450310282000c0d03411b4034605410302c09031074180c1c0d1054010b014141c0c000034a4550a5921800050041001c81c5209040b41460303200f1f0310341411510b0208000c402494082070030700c14035600504081d64080c602d084014424100644000164100305110303100c04000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 812257715 1250 812256465 812256469
    0x271e0f120b10270b100807031104030804030b0c04030f0302030c0606040623040f020414030c010801260c1201050601090b03010620010e0a050f06100f03080a11100e0c 73
    0x1801050f20101801c0041045400c1941a0843c0f140303201045415118500012140c41d145400300125425640b1039081d46081c040c0038080d180011a10582c1c003004210800100343c8003001d580c1035a03800604501c03103445961014142c1c0c001c680002e84401d0012840c4020960000700070001d985020302540c05030f540e6502000200d0315148509411500c088560041502d501080c12049801c028000105e40c4540700c1c0c4c42c0100e130000c0d0003030f02c990249019041140e00d81040f031101205c3e02440c04821642c100038040340990180031a0641d402c01100701e00d55440360521105040101c0034014400012286038001c4c003a280981c0c246001c039014080c0032800c0c07030003441228184d90785a200c2401450030318180042c842c41c0c25481006a5503108900070100a05000000105005800504942c41108501350400001400d55400000d241204201015000400008480d0828080c070703258a03c46d0701c1560000b4040c0100511070003618146804061b03e0351180c0d04071034402007201d010500c8441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 812258965 1250 812257715 812257741
    0x3090f0c0a1802130e011d010503011b0c03300c0311090d0602040f0807061b050d0503060102150a020c0709022a100c050a271e0f120b 59
    0x410304000503a4200c210755210a8000b0710781400c4d01e05900d03155541c2c3d018044040c10013a00282c1200e009440c1008104124024550150104500800c62600070740c9511010404406554050040c902400b41c01c0c54000c101c00078020400080c0c152614030800e100c6001000f07150b000e40709041c0b8120501ca4114443d21440d24042c1c0c2400324186080144820001d03020721640c42150702680801011440c3d9001e84445801000c1c1000200429401c2281c00303020380c462044034000c05048051000701180c000030f80159980507609040d42d0b42d449150040b0304121159104054154451084c804a03040c242e0080520720030080681d45000d85600c2d481090b4400d402510740703141c00e50483d06025080300c2e0306100102ca1781604030380321150803982035000d50b054001100c02181000c02c2d4241e01c550400020b61810314228504190142e043c190081e160000d4002c902c038444000303000c8540c3e07140780c1500c10083d040c0e00e03c1e031104080c0d0360803110880c0e01d0f1608046500b000b00340c1c04641b02ca07541803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 812260215 1250 812258965 812258969
    0xb040501200c0a15021e031501050f0313110405070804020108010b07030203220e01030b01060306140d0f020102070815090706020609071a0d0c030e06060108130303180803090f0c0a 79
    0x40160460790700d65181c4c40f04912240005103100b6608008484e2915412400d0040600801041d02c1c2c40e45401e150944059421132015410301c50300300040c0101c3c2058208403a4800d8521103050841d91031420401c4040396442102500503242005015405410040e03540c86140300740d81e08440c50b0f884245000b0903000750840100549e205110485010040000565182c0044c151050640765a00e807480201f03103007a03000303030340c07503143c1a005018041d41030040340c01a0210a40d01c1c9a02650310001c6031115000040140055094070303808011688280141d00c000c00072070048502500c0580d901c6004440b080c0c41c41c1f0702d9441160b80000d0700500118481d441181141c000e08003091401c072020a05808001c2d00505040040280f0035201c0311520075109000115030700000e811603601b0082e841d0040190242c0d0500240303804101912190041c0c03410f0103985840e0100fa100c008510700d401e01400c80100070000c0e0000300c204140e0340000142c1d0b44846545200301d8051402c0f03207043c822458414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 812261465 1250 812260215 812260237
    0xf0d0605010516020d14121b0a0b0601031802040c02030a1806080c0a02100606091502010e0c0d02030703020d03080405070f03020a030201050a17010305010617030f04050d0f0b04050120 81
    0x1001000c00b620f4074804d07803d1120b001d00f10501b04001e0324440503040102c2d1030070320440b00174089142203400452031804500295084000c180c4480c03142c5440c40e41450003000d007410503859584098000080e41e019035002030340541700f0300244180c031030040d4694001001c6500050b03d502008a84240401d428404692142e20744400315184c00c20900020b0f84200c20701c0095206009000c05062542d00c00c1c400100000e540344a03448d4204413004003558644402402103a04004842203105401f10745090301c0c5004407201943c0035050b102103410700c2e0259001940c0300309009810418160841101c900c036034440e4080e50144c0b51120014084400d481c00041d40000d01048103000550140c0000d1000700501e00b01104402d2459982c040035640980044070140d440c0c2c00200803007003001c52104450340d80c28001e14201518648249614081e40c1309103445901c0350064003080c001c11204450006401404507540c924190414501a01d07075204040c1d000320841d15100082501c41d0140c5a0000b62 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 812262715 1250 812261465 812261497
    0x80f07320d0b011802070b0a050615040f03030807021c081803120601080c0a050a261e0702030405010e0d0611072108090607030b120f01060e0a02040b0703230f0d06050105 75
    0x90b060323003200106401098940c00c13040555920803940208005000141a9540180400d504601d00144454000380442040d540310302200c03c008989080741c2c072800c010718034060345a0b03625a0200804d400500c241c0700c00f140000104c0d80c01c0b484083c547c0c036205500a88805810740c441c1d561440c003a20070165034000081040c401004000d11664000c2c0080900380c030050360055642c0441d940c481c0c8242c0351001c0c05d0444494080141130503d0710b01da03103d07403030b40051814646880e0010741458000b980540c49101b227080c00c541041070701d40c00390b0495400000070b6a01e40c419840d0103541c9860b90a10050707600d604003234541060b440790004521401d490005000a6181d42509501810081600c41d920000640340c40c51986e00400000c43e2220800307001007615442d18280c641000d17009010405d0040c01040180040c030000411242d44943c14a003190803d04401e00d40340b000350b02001c0720010003000003481c1130340c501c0c184040c0c00c9071000d2010401c4800c0e5140c00540741403050300ca44007440c00c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 812263965 1250 812262715 812262721
    0x150606110a080d1b050c060a0203010503070b13090c051803010501030305040b16141b0405011401050a0302041809060f140a090c0305010c09080f07320d0b011802070b 73
    0xa5014040c000040b220710f408652560440c01c44c0100d51070b202d41400c0090400f0803c5010341d1410071440b42c12911900046180d0b50502000c2511500c013406100c900e00e90001e800c42c41e501039070040702d00601c00458100310804c2d4014000b0300c1c5a01420343c41c402c252603990740d407006140c10f225950403240d0640391289003a1804000740038940104030300c800070040142410020400b803003080d0150380c0d010806000485c0242c6610807080c0b02d17044006018616010042c084141c00c981248400142400d00c1500c0350304400d812800780c40340303811101014003e80440c0615010075000581014441d0710107010880c00e8481c9a4110f03004075003106003110904020541e640307290784c0904626805200d2010215489444450030346000303013092000a0842c00b02005008801c0c8628001d404402c0d000e0501d0030300d00040c0d5520404500c0e510400e18008454401918002c90b00c040d521070000707044d01c520351600303082118441074248078060000001c1007555050786154802c840e1805d41c00f900703002c0540c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 812265215 1250 812263965 812263973
    0x161d0105100c0c0f05041514011b0c150809010e0a140c090c03010e0610050a080a1b0c120c02010909020d0243020105190516150606110a 60
    0x1020a09140050144050100b000303c1c814512000c091301c400ca14407031404d0320741400e1004503504580c0340d100102c1d01850500c072140d03000705100d85c039010918120038800c41f40b4a002d4100e08a0f144010030034080e1310b200064242d881d04121064112644039049103071350304540d02c0d090310b802c134042070556084060308030002031120b403503500d280100e4011520000d03804008164400c0c405c0ea8403106100010004003d00b282c44181264050030644404d03c601d1060b5602510700e014030305a0b0020300c1480030000381807120719803290140300f901107042d83e00c1c0144020042c00c0b031410303040161b5140e0b2144200c040010701416601054590680d5005065442c1c0150913000f03401c00d4984581c040c1d02040b00542410030b02c0c1c002031019241181d0044411681030341c01004410020040c80240491901680943e801c1419a01440300c032080854803c0f80c900011a031910503030700a03005001c2c0301c0440703d0a100c0d081c0c0040c800064031400804c803407130302c0b42c10070b0305c000c1c048088164140e480b020707007a0002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 812266465 1250 812265215 812265229
    0x51302090901021c09020307062a06090b0c0c01051627080f0d121103180c03030307030c02061b070311120703080f0601080603060a09030c050f161d0105 67
    0x114105400041c1071961020b60301313900b2440400e0900c0540d0f1214082d000b517190030f0204a008095505101074440d03070544000d074100d00032400ca405040d42c00003040c42880703900c6e00301c1d211003a0301031f5424081380360101a0403110340060b03111aa01d90700c1d08000a41904030045903024040d5192241410304440c01c482000d01c21660603000c1d48a03011400014811004000e55809440840090180341c0c3c0c1890740104080320b10000a04501d080611034158511003600320b035084030102031484040c9610300506407800b010100029098400041040255503060740b040b00d02d40c280340d00391980c60321126003241c1240f200340d200c4085c02004001100000e4003842d810700c48425010160351a44440c040204000e401c012410340205003004100023a00c41140103140d031280d400d080080c2c0c07504081700441e071754850040000b41c0c4655503d10101c1454010b80e101000c0651150071191421401c040d41a02c0b41025100c81c00008819100400d0405526010f01f41074141e60041c141c0c2a8a07000403c411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 812267715 1250 812266465 812266471
    0x1404030e0d0f0b010b09150f090d060902100809010c0305150d0c0807030b2203090603020c0c0910170d050307180504020706060f080c0303040b0714030a0305071205130209 75
    0x1400340020081c0d800141c3d42d1284070300034980214040e0f2034420f09024041400301456031b060f540c413405c0010905604007035083d2031410800742da40031a4004245420b0000340100b07180603511882544400115590208885106140e00c000038080120b8441c0d060b4252032003503841e01c10204a44204c2d00c0d0301e0511400b0b0346200740c0900c1d0a1982c40d0b0351101044c3c14806244c2041d60005401c0040217102d140d0440c01c034801c03d80380350110200c089540c4000745500c0c154000c0c001090740004a00c5488d240800c588051008000e015140c80d040c6440100d5198095100c0e90b41580e12650b640c140c01c990100381c44441040035141c1c80c0c6155200d9004507428040701d401074401580800010800e40c68510241c40702511170b03d400265a03003440150510003d040d4040c00c0541d10240e0359442c0340d140132050b80c0460702c22422098442a00385094800032001c113005214522021402e0042c013a456080180681000d4450b6007403440f5001a0030140d84044030100c035150301c4120900c0040c18143c4110394 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 812268965 1250 812267715 812267723
    0x714040f09020d06020a170f0622060801060515040b07080f210403020f07321503070e011e110a060c03061404061a210c04091404030e0d 60
    0x34079016260300050007050f503100260b5042c1d0707003c0b641441582d006818035040c0c2007504c41078142807405400140c140000140041c0c0500004085100040000584040182543c941c10310100740c440340018000d000d10f22500d0b1144541c40b03800c1450742c1c1c0c01001c032001e5904500e9140d00e840741c0368640144da41d200c03483c070210203201013200942316400c0d00c02085021542e00c60755962410b050070001e00d040d01410091803190003070441080002d64110000300b140344554480305840c0d02010b4400490102d615680da081410044000b0044604000542c4144011b845503110702903540011206151700c1b0302c910b41510030350380d1001c40f50340c085e1420410108807401180e0344002e41c2c3e0342c0c94040d6800c1510510100303481d1103060104001420401440d4078081d00e00300145483d02190603d011544040e201c4140310000b203c0c400c1901d1124101400e1070300d048a520707641010422046c3c103500c5071007040e200d6071070702c0c044506040007040018012a0507580302c4240280f04070800c540b103500c0302000c903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 812270215 1250 812268965 812268971
    0x70f02070e0a051e070e0111070302030307050a030f0e060d02250516080309030d030e1212070306081b090a06030c0f0302030c01020a122001050901051005030714040f 73
    0x358004907011070a11600d120b4a0216640c1003071060b110450240c80160040a80550104041e80358094201001d001c000d290a16011400b15140e5007419400c1c0c10207034050100140040c1171110000310903c0291082e940d4a00c0317441c10b0081100c01e41200c0342c2d5254000c03001c20066800d01e000c1c0c5c0180c001494107483c0c050030380009140d040710320300859100300e406402a14801c0701854684044400910400001d1172074214020300298441050422030070526540300d00c489c00c100810000744a00010140441765a0028600c05800b620030883d41c2d100000e0408201007250980031425a0010054036001501580303502c0030071070301a200803d40722505aa4500c0080403500340800c44004202c0d0300f6590304002e0035401414200182c104105040d9072205030b03660f000500e0420a0705134416145454450440c0041e4807480c0038070a494200e2480d0700784000d12081240640c4120b015404148488036600d6507402499200c110620420740101141000c170200d900b01a0403082403290410000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 812271465 1250 812270215 812270219
    0x40c03020c030c0c03070b2d070b0a0501150c3203070f06050f040206180f090123150f07060f020304050709050f041110020109060e030703080a0e06070f0207 69
    0x994519004800b43c624640e0000760740d44410304062201c0005011490b100c0c6140a4045183d080c145102c079000c082d4105d01c810040d041000c0c00c80503a0000c95001c0320440d8542008452540a440207024900c4135164030700e800755040d80264805d114803940000c000b5000300d8601441740c080c11615450101e55900041180030034541403001b0031030284610401f01405082d81000011550028001001110b1100c10b02c8096502c6509031042e05c0038100401d1800180075022030040011541042d4000d02490004070f45002c00701009000c1807200c024865074610503030108140700d41000111070501000300000c4091001c104010710900e8000c00011031580840000c440490307000300d070191150741200d042030002441902540b600132802d003010490b98103180d15040544250760700a60710035600c001030181054003c2d0800150310741c00c00010000d401014203003680f2940229002c48c0040e0001d000101311142902c03900c001c0c00d4920004110340e0340d8080e41a0394a1103810000790941c4540130300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 812272715 1250 812271465 812271487
    0x204060e090a05070e060f091509011205240112050f030c070f0602120301090915090b070e12190c0b0d020405100e0d08031801110a020c0901060905040c0302 69
    0x640d078056040c40004228104183c00c1c00c81c1051303510341015600c05020f44c103000c050b0741e891055455004003207601a0740380e00c4a1880f40307000001c41c0445c82c0c012020307000006042000d610890402da0080080d5035490840030b201d4030b202540a11036007010071211005004034040c2c4e00e60002528420401c03140819022401c02d80741d604418014103580d4480c170001c1c828001d40d85d80000090009000038103420b1560054900b45002c14050203201035664214a814043c4001d80c0000700031501004002202903070402c14554001240d0004c0411407010061026007482908041950500c401905048442d40c0c10450104100602541c8a0f0840a004140300141d1801007100c0403d81800594a034a0003042c0b040740200e18080d84140a0390700c1e001180d68840803c2551201e9220a8450740c9507114180c00c140c1070f80700420201a503103401400801019880000c00d00849960226075174207800c0010017006603007d0158000086801500700400d081940207201102560309016041c040c1d038440c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 812273965 1250 812272715 812272739
    0xf020c01020c0a0212070806011406070204020a090609050d0c120305070b07021b010503090d0f09120c030b010b1606020f04030b1f060f0c03050906040509190f0203130f020406 77
    0x5150009400521100c004c40ca0310350742c1c01010602c0500a00340d00ea241118080d1640c605200b520b0030070100c0000c07500c0903a074940403200106c4e4024000c5450b1405044010a450010b000d1080030a0540b4800714607850002d807088221a40404240b41040c1840c002c0700540c3d10385c00086040c85000d015980014081040b068803810841e401489001000401214500209210203044c80701c20420f0203100034002c03d0b540d52844071402e01001c0000103e90444810b1466480750001c50081c002c40c100f004080c2e11070000703da0158600802c180d0701c1c0c0d01140c02a100f0047d90910210300309802c24005441a005044031035420070782542042d5a9454007200d10400321042c50019418100c500b4001c03024501804c003a11607450440c0701c0e40e11144014003c6000444003a0030f0040104100b50941e40788070440c0c0c00b40501402c540c0c3c0505203001150304401e182c24013450319504220a4844807071305031081e02d11413040c000b80c10706490781644810020300f040c3c03d4142c3c4c0068980b0000304440040007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 812275215 1250 812273965 812273977
    0x9230406120f050705010c031b020d0506010b130902040f0303140909070306080d030903080c0d060b040e1605090105030a24030506180c0a150216060519031e0f020c0102 74
    0x540b040d42c207003801e1414900b07244031904907905024a000c040c00120b54000d900211096256000003000c021600000d0b00c00364a100c002011840b03448004102807003060003408034a400c40282e020407645600c0c140c0103902640c021000014648802040800e1280078841c1200060701c0f4602d1607c202c1401146548070701712400700c046901d41100b0450240e04100610900d0080d140811540116907002010f20740003826119505201041c50860940d60b648000300030600061190ba0317850f91607402115102d42154075030626401e030350b4441720090052040741c10031217050313460a1442d82c0d2482e880700180101244041d81000700c0e0003907607424259174800000741d03001310001c0c54a07291000c004c601010182841d524980c02a0300b100300380707480d400d000340305441e0364018981c4207580300340081b8078081c8400b1303440406900e4000006401c035080002009203245034119007a246506e180c0c181c09860f0038207801e1520b1101424a0340ca0140954020301d0707221007807000949030070810002d49007039030400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 812276465 1250 812275215 812275223
    0x115080a0203100c1232100312020f030d0c080603030a0206070f0c050d23210a0e0d080a05070f0e01210c080f1302030a06240603020a09060923040612 66
    0x106840601201a0079440c622004080039481041c5403850140411040b1f522008212898034804401341c40c2c020f2100c00a88298042140d40301c00c0c1c0d8644803809031025802ca1408103440384049079080c2030210850341402500d800500150b110148100c0d0210038005502c010440e110b801040042c000380220320081c40a540c0b12407100a480c8644424485c0c2115294200d4900704000d140c801c42c1313420640094002c01070000e000e561042e507050058022000d40103080d0091044110308260400000e40c0a510840b50400c00390f5611001030321541e071417903c0407003c03440c1000805a03035803140400c2e410441c01e00816541c40083d41003480291150b40030080c2c04210000d040102e91180015560f600c000803040310070a000507034001c20b8075072050440203807100381c864240f00c103c0c110701d000b00b100070101c8121a0b222240d803600001c00a400c00032a02c40040d00708039001502034481c880500c203480d85034400c10384906406401d602420480400c6075000f1307484a600041e1544000c205085403805 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 812277715 1250 812276465 812276501
    0x501020c0319051504120f030216021302070609080d1b0905060c15010b21040804030f0c03120c02030f070e06010c03200106050909060f270d020115080a0203100c12 72
    0x4074440c09095003403e841e681f02054414010100b884120004d002c070303040d4058a0600c6181c5070065000060311030b10310007811842c01c02c0720355010000c4010042925610107a0100142164160300441d4030003102c140740c3c00540c0c07014090000340380010050001401e5a4100c03035111103a414180c0e07200300c09a03c09000c0c110042002c8607e11039185c412520400030a00c2a021860300f90750703e004a0203540406040f40010078005020821410079480241d0303048506454100300024009080c0510351008074024010220046c0240c1000036031308082d00c3c1120005001c035030b0b94000444856001c48010b6041210103903079000314000440801e03102d00f0202d0000b082050400c024172a820760003900954880c1d0000d02040110f0408100e41c54104400e8424000048403850b036055444044202c024200c2c01070265038081241c05501040045d49046c107440891a500c584094481c2c40d80d20b00603405401400b09000d148c48203a00104103036001e800d0001c4040b0000c62520109d410030348c9003901c0d540d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 812278965 1250 812277715 812277743
    0x7050c101a030c03010908041e080304030f020a170a030503060406030b011403011d0c01050715050a05010509100e060904020a0e090a0611180907140c0105100501020c0319051504 78
    0x1c091040803041e50040e4006d02216556a840111500c100e100f214200f81020301c0001103c81c4442c10340c0000c0c01c000c070440e42c82d81e460707003407000048111500032442030500c0d000010320300d0320000f11455241045d02c060002410f45440a17074655000820081d8031540d1860040001030400d004130780039140b5100258400c801c44000d141c00c5075034000d0a0f80156002000061031000d0008200c22407000a10341952036140e9407401c0d0300070000103404140304a0406081201110301d9511080c102c4900b101c2000c01d645940140e05118400b500401039400840000a016030034a20074003038100e0b10180003610190756078441034518544c1602d43d00d0940c2c026405150900c06039001b2036140741e80302000c0510b816034264181401c40720740c00c4124000d558210004203014025042c409040c90b000c11440e54406074410b14900038032086a5411a00d941ea580118540d403000942e2032036144090b0041c01848030a04442003185401d42c03040319944074a901c8000e550182c81d00c881c2c000c40c40b9444a0201c12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 812280215 1250 812278965 812278969
    0x2606060f030a150213030b010e3304020d1803020c0604050f060304050c03010c05070b01061704060e0f0105090a060e0105040c1e05180106020609160927030503010e070801050907050c101a 82
    0x40f4001e0002d2003620f1105840078840c0384500c103c0240c1c541c55214030280742c0d2203032b004100a40541c2c181e80c891140703032011010f2035654840005190501c070b40d0a850f0404515010010903000f075002e01a040500480b0010b610f060440085403c54010801c4500799144040001d0945019003e0342d40012004520f6508005000c0c01c000d01606a40c101305084a8045011000c2041c009001804031515800304400408080c0040641c00500c00300a004070300c1c001403040c0c2d4a90758244c04481c01480c041d20110841720600c40c4030301031607101e400205803e02e043c0c42080c2821281d030b8558a102254040054507948440c1d00300c0e01c844040e2508144d80d0314059020f4140710b4010070310000340e003001103c550086e040340704040a88128880001d0300042039242c00c90f1000d183d240d00041c1c40d4002041809254206001c2c5041b501c6140360260746a5805001b103600c000f0a01c1002e400580e507101042c5200e0044000d00102e80341d003401ca92007140c1501c0703c0401d0b11a40c44035034000141c4c101d01c2072018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 812281465 1250 812280215 812280239
    0x405060a0c18030f150c0503060418050f030903070e010b07110111190606120b040210230705010b0d03090e13240614030c10092606060f030a150213030b01 68
    0x21643c805c020080300040034005041480000c1c1310174030650742c800b0008032540000d81c91030075031900041254486800d07019001d075a90303c078000e035600c42c1c0f0030750a001480b4880d0900e0a4180d40150364a0b50800c580d954480303110031100c0c224681403149904000700601810040a200c05101030240745200c4400d0a009080b20b00700c2d000140d04c000303800c041c0c0002c5a441382d030340354216038140d80d003403c00d816444044500880c1042031100c1910380310010b031400c9202002616286009000810103104c429040010418120343c00401041003d50100f0030510700c0c141099002c01c1e00303ca0b2100001150741c07080303c807640740c20808642c2c070280e014003c0100268071540c0050101d400409020271411000070740d4500b151a8198419003100d0903030017000d441f50810000034805414002d0405103807901030001a00100400300041c4200c00c0024068035101303003002c05044028001d010181910744820500e13040c2e8808070004e0640030094100482540c05902d03000b18005c246e000a95414882c40b0b07060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 812282715 1250 812281465 812281493
    0x42318090625020c01081009020a02030702040c0c020a0b0f0f03160f0f090b07051c17130f030302030a0e070f0f0b07080406051b100c11060405060a0c18030f 69
    0x30100b4001a01c03078074903400090340301d2405402d00340a04075030703500051500c82d12120b8020081c104e00109021121940003c00340696900c00c035820300c0f540202520407503105042d80340c065448640d201040210103030001c02001d80350450003415180420800700381c00d0b41d5009481c1c00100005904000e50042c1d8021155060441c45181034554030807154001001c03168540036008550300e0002d01401048403c2142c64030a81403aa4492001c0e003080c203010b40960030241044580e1000e000006400460320101181e01562009602031841c0e0385032012030094100030401000195074210031400c0d04010060710004100700f600b000410703800e1042d900001070a40c2e000840781481485000300103662102940d09403004c0380340140d203070340440110610130100070780440c890b400744501212010819400138040d030900d80d02c50325002240081100d9481e181110040e01c1038200c140800c664050baa0083c0d002c1e10260f150a0a001800a03003807001c4000c903a000b164803025900d420b4040100080761018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 812283965 1250 812282715 812282761
    0x5070605071a0c191b03092c0a0e190b09010b060315060a090b04030c051c03020c1c02182d070c0f050307060c03110423180906 56
    0x5414212882d9015016922140d010a0054400b50306268880e0141020400c1c2e103a032605e84401c003d00700503004075101d02035481040405100c04940300c1c0c804080e0b050380c1c00d03810b0083c0d600380e8440d80c842d802000c001450b42000c1c01107003001c04030204c009800080c07543c01160143d049003840e41e00306085071000c201c982c1c0100b40a00411000840108084000a00030b66020b980d03000548812103a04006800c103e10b4050045804428400c0c602c24410070b0312000c0e6111822110004030201d804000d5010080c016070007075825000307604260380c1064200e59440c901202200c04d81e4000380007000000480411142400108003400d075100344911100078407091030a41401e01040c0c1e11102040007009002403103508070b02641049480c03103956032584d0b0000103803520390380245090405843d4150710580042e0400c050200d0400400303007101d044031010750181000401300700e25949100100c840640c0e01811060314802c0007400d12098500c10351005002d00554586103210311049440480d1881c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 812285215 1250 812283965 812284013
    0x825030c110c030604060c091a04060e0114030610030f021206100504080604121404031a0f01180f0b0a060207030302060a0515090603391e1c0507060507 67
    0xc505510041100385c0c22641010300410902c1420703009841170300a41e488540110f071507803211b01800702080b0240c015240d056503080078902820740115410180141110803070341c41040410b803a460400c8020b00c0308503c605000c02e10800840c040012a00b0110000024400c00001c1101c0c61910a80180411040382030060503d07041c402c02d550388400082000f0140240040c014880a000714481c1c4512081400e0032542d0f2900ca11b0000829082d82c0c83c1c00620a500801040c0c00200c407019081c165060050b11494a6803031000a101400ac5001581c0315282c2c0c4207485112901c4803030340c4401800b220740041c0041465403078002e00c1c00c5801884e03807500c5461b01c0c0030300034540c40c02a00040c0d210380403100c501d901d03201c0b5000207080241c2c07841c41e0083d00c00c10f03058105161000445155450900294010100306109c050100c190b100c3e1075008400c030306440f4104010316013840c403001c803032018a43c0c1c0b5103074003080e5407910701d0900c080d0498070100d4008070b070440c20021451040e00481c8a0041c2107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 812286465 1250 812285215 812285233
    0x40617010e012103171305010c030603051b040b040516020715050d0b06220f050a031502130807030f060b010512070f11060f010501170106020d0825030c11 68
    0x680440303c61202c03105400c50850040400e1500c14800401000d100940210041c101400d042c1c50483c1c4841e070440303195003005071511220380079204801c110303900100500004602601c1103103440412103201c9078050340d0b4054420300f42d00c5030311455101e100648c01001e1070b2900810081d00c2d2844a0780a40c0b503083c0d210491260480e448070580d001802ea031300000c1200251070000881794003a00c05002c044c15504029a46040283c5144808403003400b00500411034032182480040ca081d40000b42103445201108003100e40c10758010150090091240e0307020a80f0340703c80c40d041c25000c0d0b00c113a8109501e060a00244403881c0b2852990743c209080c001d1070413000c7d1405202c80d110007424042488403600101b00140d0180c1ea107092454140020340d58640b0300306100c00f0344044d0a00850380000c0305200d07030030045070071907800318145c8a46030000c0594140c1c402048946c00d20042c01c8071142100101e8901101c45815616540c0c141280c40100f141c01600200520400d40140480000d43c044810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 812287715 1250 812286465 812286479
    0x110d0606080c03130602030a02070605070c110f06120c040302030a05010e06130b070804291b0408030d050702030f040303081b090f060f1326010c080c130902040617010e01 75
    0x13400c150340904007584035915018202d009004800c0090000c904020401503c594004404d0005902ca4902e01ca47d02c46800c0c248000840540c1d40c642c3c00408c1001951008040003c026500c0410083c046103000d4803540800d0a002169100710754aa450302e500c50705094081c4041540484403030f1045190a440b919035290404010744980309001500c40410144020418a03e946e50464051850003102c0e01940c908070f080200c0d800c5a400940100181045000d41c04903000c58000c2001036003441c4684031010014140545485c055200400c10403601c06643c0e4040d100940c02515521141d103098401c04107180740c19504c0108031081013160701350503650202c030040d25138400c0ea490340c0c9442c00702c0109640c6100300341c2075900081402e50001291404089115082c24907401c460305411110020355003070312455907a1002280c04280040d0004030385001602440b5041420b100751250354200ca94100d902c40d400c44800912240e01c402e0032103161408040c01441141d00060f610340c500301d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 812288965 1250 812287715 812287741
    0x2010b011706030705120f1905150c040302130e011d10021b06040b04170c0a020906010201232205060c13080d0305070914010905090901110d0606080c03 67
    0x200c1052507003014041541500c3c2080f00101400028181320307001031032a00350b02d9031404c10140800c240d20400f60302d05400d0031610103e182071a8040d00610310458a80b170b14000d010302c01851041c000d08103010020150740c1c3c40700c0305100f80c0103080300020350096001006094980242001003011810100e4601c2c002d00001d02c0401c40072400001078982d5a01c145d0500b00145001d2250b20034817a010600090001e202c040e540201d20840c408218050400045102da028902d682c0c0529001002244054144041c060394408014400042c0c0c514080c0144516644501c22113001d180e1031904208144c03010f62860078215248440c00103030f500c0156241c59680d100148405c4a41001180c1e1a80c550450040400608000380981c0c0d500042494003d00408084a1401c00034007020000200310640300b400100000c07069540540319070510303051001030b40018015151541d41d500c84050310b91241d0000d8038400a03841342c0070480501e40303200280015030281409420345010401d21025100c1c0304 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 812290215 1250 812288965 812288987
    0x80a0801142206030c090c09060c110d0206160c030201020c0114030c160804090f051501203a02010c091206140408070606141c0609050f030a030c02010b01 68
    0x4400380390302d6400351907030030043c1c000c40d80010039005202c400850500700641154050b811203546003410300b9038a0301c1c11202c1c2050860701904c4000c00c0c0921a040e41040806420300d00d001030002442c02419203d4250a41841441580e2116043e0414411503906000c01a214442480c0003a03950b0595807104402d44400340100c2c10b008070010f91616120341d82040c0d0030f0340c02d4004906d10b856690b9182c03003402810b801d83d4840c4407180381000145040310031200f68040d051045e0761b60310003035011a05020a44421204401c082c0c4a0110411001c2ca6201f0019200302d400010100409407104402503410325049041002d59062240600c4440c0e0300182c03000854404994110805c009030130480000d005900f040200e9141c0c803010070040c040e210004003103482c840d400c01c00c11240e48000e9100800700407441158882441c1c0c9058030081207403d0720f0403a081c007903000050000f071165030b550b1814020790030808040e0004203404c0783c0e0680500c00c40c0c80e08001d40c0001c0c800032516100003440b4000751 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 812291465 1250 812290215 812290249
    0x904030504062f0f060a0524120102070516050307120318050415050114030106171f0608010311030a12050c1f0c0f021906050a0e010e01150b07020a0504051e04080a080114 75
    0x3e0306d000c072300715941c423050303e040c4140f158021076483e2040c2c14200e880304400101000ca55440742d000040c64280040c40104032401016080c0b403d195175541166100b031b120b4510113542e40e0a060200b030582d928407a004541c8403a01056604030300e440300241074072045601455245a0a000402019030031089181034030b5010800900c0070b595000301c4804000003102d5080c03250303180e62004103003250082d0910741a03e00400704425080d0052003015687c51501100600b603076038150007252664003e81c041c1240301c104000756440000400b50401200e9042400350700f4240d1154290240142c00408a08080f5560310180494201002c031800884040400007004684e5a03400142d016556610600301c0311960707402406140900740c21113000c2c0000c030a03113031040c1d004c070500010014032482c09c889503d54041c1140004600d00300800004000052003510440d00300d100c551301007040c485220740725034840c5100588405101e4001008000160400351014070000d054201694603058525890540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 812292715 1250 812291465 812291521
    0x24090c080f06010c1401020d06050a0b0703020d0f031805010f051b1e0c06100305070b0405030c1201021e190f0c021207120c030b060904030504062f0f060a05 69
    0xd21300d403c44910079005c0800800f548045000010061142c10120494408548981201d0f4452007602c0d003511a006005001d607116283c0030104a0140000181d51586810001074400019840407006036007084200c0c2c0b00e035500d00c0a85404041c500c250341d040820b401c2c444102d0040030394458039034490402640080850040101d0300c080341d00085035a03d001200c1600c50724101601402d0207508507001c116440d01847d44007007407004844040e5001c58200400a0014030a60300601840a00d00300c0c000e2a255001c1080074482e07186041c40c2002e0705040e0b0080c654414049010300a010014035625082000d200e03407150a181c2d01405401d4070036011141c05d86c0d400c412902d003920f440701caa4001684045034080c0754041c0411060074000700c03401524408000d80d20740b400c102c0c111000b02e80050204409000030b1000d1031040542d140c00c0d105840e005003039081005814040062810181c00c000e40c0211a04003030090103010321358211825404c00e020301c0c02c01400042049101c0b000403003d13445 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 812293965 1250 812292715 812292737
    0x30702012a0c06030504032d08061f0f090902070b04030e030f101e0b0604031b0509040f2a051005040b0c060105030d020606061b0124090c080f0601 65
    0x4054601e41c603085520800c006100c558810000e8040d01040360240c000c16030781c4c0488207102e90082102010380010707158a0b0b001c0c42c42240c0541748404040d01c100d40018440030100c07000f0300c040040e10690480c60316151000855910018024201900020340e41801403060700009100006800e80090740341c208120782e2181e07040405d02c4c0201d0703450001418441e0600c01c461884407540070120341e09607195104031000d201da550b901a9070300040403c3e0003030010070040011611003070401c04130721841c1c1d031000c0803569540000b50469a0540d01070711801740c501003210400c062000355180d881d00340302920b0225205401035900c0288a40300f0030380902104075010280034462001c56029040c40d26400e030300c580a01d44010f64a030300c00d002e0a17000c1d22030304503181c03185800091183e1244074000c2c5054035100e4200e8114401001c4540c100700259210350b80f0003110b0030010301d100c0c009103040015145103880c203849d1609441651150005010004007880100024200c8640c0d00c18400c3c00d00411140d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 812295215 1250 812293965 812294027
    0xf18100c0b01050607020402280e09010806041b1a03012309070e030f06041a25120905060406050f0a0b03070b0307230409050a020c030a0309080912010203090f03070201 74
    0x42709000e003000400c0c5000780e00201c2c441400c42e1401c1000c2c400d6890680302c4500500b030011600302805800300991081000400007a03001d000e4045040e10112030b0205036644080309410f80c1484032540000c28804001030010401c3d0703101006500c20698010007040d90301c180440c51142c00941010308000906084111540f800c000c0c0c641c28480780c00072282c1c81c3c6054204032110308002131002e0100c42c070610114504002541c1d5440e0715840034a150304445c0d000c0c3c2801da40034644030349103685154480c00400c000c00c5050040c44e12481c014075010644e407500b40c01d4000310301b600420004c410707860310f103903280350f41c600040c5601501c0302f90103880d90342d4031540c405441400c1c100071800380d4000c0b00144940c000441f100134200304e0314140c005100c1502ca82d943c1d0011380c000d0714007840c60355205100c120201840307500803010381c5000d040303610314001c10b4001085983c1c070f00c603c0f60f0103581e4000042c032015602c100010100e241d1100061801c2228a80c00280b904003004591407400d00c903042050415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 812296465 1250 812295215 812295217
    0xf0b13020d0b07140d09051209061c06090606030f1b090302011112160c05040507050919081605031204060816050d060609082e020c030f18100c0b01050607020402 71
    0x105045048803505c80c540e00104501401450380304a9050040450500b02000780310181c1d40803110086c0001d090281c21205c411104200c0d00105800369141d2000040424036072041c10302521041d03501043c150803e80762603098541501150008080e2a08000c1007079921078486e00079a070b4240b1740690403000c142031a62904140310030211528030006403101e00c2c0c0030300750506007401d480f64040c00617456403107081200300c0764100c400c9004284104540b50551130242c41c0081202c603854981120183c951034040d15006d00145020b900c017400440130f00a61500304243c2000c1c506d07a030806860302c1d091480c000c0000e003000d4600001c038512820041b0740a8082c0003528080b40f207200c1d04220141d0354010080001070b0604c22400580106440720307401c1e00c448450b41004003a02c02110300c103400d131300e80644003d500601e02c1c04518002841104500c4580c40020b04800c040f4038000c084404009003004050544200b5890512201201c4030000a20003d09681116804c076109922683c1d40e0001c2406 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 812297715 1250 812296465 812296487
    0x7090207080c0105090d020601140d0312021c06090605090c07020405071b05010f0b04090f12020a02040e06040501050f040f1704030b1015030e0601031203180f0b13020d0b07 76
    0x102d5400e000400c003144400240e0404805607560840d00c0990344d41b40100104100c41030501e8202043c01c0106001ca4020100f0b581c401562144c01440d2529004044009000c68180f0b008541d48845041010110300d001c0c40d400b9003402c903900002400c1000b0346e10214492003400070f02075a00c400c000b45003140103024809054500b00003001c900c88107458100d00074010050782209503032600740c026006083c00d01c0741144144d0f0000d8004031000160312240c028041c545650350031881601d404000503102d50203244054400900100464181803404a0a544004050b099401040010071003c1040261000840c42d04900c0d82611600f4121100b60a80710748c4d00f000e0710149041d014415203c90114034001260551201d00465841e6494200c065503a00c502d50201a8003400042c0081001c04950040011140c10700251003012294140000309110310f080d104645554000000d01c280f1301012544808010000c1c04a00611743c0040c0201561000c05031140d4417540000d64040d009150803c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 812298965 1250 812297715 812297737
    0x20a0b0c03091f08070c110402040602070e13200604030204051317030c07061d07080d090b0f12040201201608061b0d06030609230703050709020708 65
    0x250300c03019203200c196658003914025001e909444803681c039541080c401180f0412540e95020500e031200303c411990200641b03415107100c016030120003c20740d614030041c0000c0c88903401520940c1d181628040000c00010308009a0244103101030002444a04001c10350440100407402c109038400081950f0b0f00640e00000d40040ca01402c3c821401191041c0b88440f610410140d21103101d018000700307450009035281c00c4c8102c010701505002440503040509600780401b90481c00c250080b03480b500e05440c5900507000c642210001400e010380c4140180c002d05030b0340050510300401008044400d108040780c2020320b40703444004c2400c582c0300e0120f104802d600c1c40b07070030216444074000ea00d03100d15080d54821514141c00900140e01070300420392911680002c641c840b00700300c4c81c003240200f41e445000603210303041e03507040d0100019890f4440da490150080b24031803420380c130010350700e400306c5064003c14a0035482100c00b00001400051400152550023130056224a85880d0120b007038040d00d101e043c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 812300215 1250 812298965 812298967
    0x718030c0b2206020d030b0f06030a021c021801080601030f09060204260303010e0603070914180c090a021804020d1b081006050f040b0a080405010f0b01020613020a0b 73
    0x201c4480041c007810300003952030100300c1c18821000d02c42e14001c1031481501e0150b044689003804c00c9010f64403800f13040c20054194290141c40200261640c2d0049544d801785940c0461034041c410b20a10311414001c0249408502c0c065400034001c1c07810800c66010b41c10010b0000009090341d00c40e81101b104185172035406e00a848540c600701011350001d004880e02c845085400c034a0000301e050320820301955590245255900746024280284001028243c051045042c00982041c0c02e04c500421404407411400d000d04018030210b00c5441d1b04868010558894012110300da03031a407855a811a010540050361005001c0045130f020288410680e4000c0c40815001584010b81d0001c1040c624188503c05103252517900a844041c004d8400c0d19240ea0318620902c509401240240302c2c6120b541105404c01d82d482a00350000c1e0b1000d1507600000310f4500500c0200300090281101401a244061045411100000795550300c01403008410b4562103a0410030354032210913300c05800d4201c45a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 812301465 1250 812300215 812300219
    0x605041103012328020a020106180203071b02100e04151226030703050603010b120d021e12071e05030301210f080c070905181011030718030c 62
    0x30054146440b012940c804007000f000840d038000c3c03201c070002e800e107441c01400c1c0800c00401c1110001d4001c2e14074002990743ea03203001b240c1c52480048801d02c0030504840540d484c9490200140070302040600c0058079000c01c24444010b0303440c8bd958144064080c82d0140408196100150140000c9070b01c403100c00703100c200041080c0c0103000340314105d68018124080300000c0c010040050001c2c02c0313031944000c1021320100d00d07414030981045802c408003c00120700c0852140005651352405240d0306015030103500f10003045501030100ca03901b8003003042c500c01c20f5601a0031041c2c555158904180c40000c0015030078023006241003900011180c050052107208c1d950f4030b00b2582c2c0707610038083d43d400d2484203034000010302c00e81ea01001070103512130014a0180c010f0399940c085a00100c2990595001e030401c049070008042c440c1600c5151404030074140e60b0107655403a4100392128121204150400141c908540180412260421250700c0c0160b0b08440e002c2e0a0540f0300c00c0741e0401030094280e1140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 812302715 1250 812301465 812301491
    0x5130c141306030b0306090d05070602040e1303030f0c0509040c050403210206152b051209042301050d0c08060702330c03060402040819050c0102060c07060504110301 73
    0x31016541180c07010494540b0450401da81c40c46c0c00c5030044819404140c542c0c00f083e1054020b01801391040034003504161725480b410001103001c4680d50080d03882030810406040d85400b4040078904481010004c5c6d010b02070000b4024441e4201c1580520744420340c1d81e1280d072240341164021600170050701d400440701400138031030070000a500c00041c0300ea2004903102143c102c40c034801c2e49000404070040c0031500b40c4001450030010582400c10036034510760002007001400400c0d803490000d180141e0f561390501c100f004031014000708900000000503500c444a1042544506450040303d052100306041e2910b6280e02d440c0c0d4100049a000e880144030096800007500b80b17884110a045400d031061400720500e800160004c0c0d40391011400d800b192803000004001c41e0031010261025140030340f82d2804a184c154804603201480c024803100006010050241d811411824809040c00e81441d600b29000c6018841000d0003255a034804a020000f0408a15900d0b8902400a00c804194240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 812303965 1250 812302715 812302747
    0x10207020415081506121009020a1403060a020f13060905100f050d0c02030d09230f121602091602060f0603210405040216170405130c14 60
    0x2504a004508101280d03002054010405058801c40e100500b2135074681ea181d4028001c01a20301900b180c144050882d80450a00085c03030050203841000c54416291304c1030280700b01251f4003411080c4d2001c41d8072402d40e90041381c6550400340c501c20242e156501034000300ca180c0301e0711390b0412016088903070014103160811080310446000325506c80340c02491990a03501241e00903004400508100030500340128140e00c8214107035842d104a1381060368080040c41164940541a181050103030780c184400ca01c000c0d04281c003046000054048000620035466841c8900d4541c2c0000c1a40490b00f070f031002c2403a045111051360024803104042c10158403842403504035452900040c0124400143d0000c209070207140a0800500102240752041e440d2903100d0601c0c864500e68a501040002010761383e40c0080c0910b820340c0e00145440000503d800b00358100f40c0385440c403100b101400b0030403a96884240403021014010404181985440022204514013072810114040c01240c44207851180e03103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 812305215 1250 812303965 812303977
    0x11030f010305101a09040510061412011b0c0314030109020a020d020d0f0c020102010e060c03250c15020c070e062110230108100c0e0d060b031009050102 67
    0x707098a04240f01e460082040d00c14201804104a280340c5483c501801d110000c140d001c0d0207070b8259a10700e40100700c454140c50240e07005c0c1c0000784a0308010754003868464410f04449050728001c103c01e0100004c0302203440d41035410402481078403201102814007502e09110144e8088004566039a120248a0003c0d00a0308910005100710b50300f0102c2640001018500c140b43c40d21400c50240c20608108c40c080f4050354202d0465494952035548080104075182c01001c01000c0c2a842c2d00d00140b0a1800c030041e042001c1e1140c4080c0b40c48480c803034002148154842d0400c0c29404000c0035a00321101903c215840e0345941d10400c4000035806400c0a141030049804881511075040105109550344c041e40070b46d0f0a05802c5605e11500340681c41c0e120445c5a4550b961106000031302020003910071a003640701d6040350308861850720a0658501c644819603c0e20b08201c010920100c01051420b102014003c01d22540c6103045800f641e004c00170f8240c0664100b005010451041ca8440c0c082c3d0407803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 812306465 1250 812305215 812305223
    0xa020904060203060d330209030c060307020307021914030706050d0b0109050d110a150516021908031218031b0106050301090305040311030a02180601142808011206050a11030f0103 79
    0x41446d0f003084103114001c9841240004000b400c225030b000f001c1000c4c0743d0010744000e055110420400006132901c800d41c025800303170412180040c46c9090601c0703421848641403207110343c10002c07050207402d4000f010743c5e8243d12912800105079040ec0010389504407141c00c15a0310140c9082100e0070019903045584056509540c40c0030320320b41d5050b82d944800321014610002c290180283c1280683ca42c004e402c00c01d00080060750502070030b0491400900d15504900d40603003001950103407400d00f4142c8030ba00440c072000c0061005035448040c0d501c0e80107941c0b10114540d501c160400d8100c500750403031006030000400822121904d403030042c10913842844115004500d41c8410781c2503107030108101c082146c021f8131a85d10108a015103901400004180c14180190100c500340400c2c0301d0405080b40c10460720f00700f0300c58510101c00c1403141c5802c807010820008e4080060000c081544003c0180c19404480441d558442c0509440900740c2c401400b41070940c00f10030460351111254100e4122401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 812307715 1250 812306465 812306543
    0xe060a180218010306060f03050c04030c0303080f060102160315090c0801061707050102060711030403050a03081504110409020c0c040906060f1d01030f0302011b0509040e0a020904060203060d 84
    0x110001134042c2d400038031445011402000803005003078006e0300701503400f0040b07414680c501500c03075851617469061380d0426000541c0c86010442801c861702680c40c0c002009000515420000a2081984013011b0200070039402513002d0070141c1303000385c0d00a41c110640c8950b00901d03040e00d03408268001d1007544100b0280e1042e0b400d00c04483d100128910060340c2060f4060701d0359075030313482041d200010701c00c001d20b82d0761004100000128805001104a040c0309a84040c05410b1444483e000e81d84009021440340d4940301044217200d050310111000c980c01c0100c0540c031440081709041c00d1031412640c2d95041400d00c030010041140e03c0d4024804d6807a8802c1d560013142d290f40d13280028688030b000030030a0500810050010900080004c21110320910001c0341c5002900c0e2a403107451060308102000c520081443c076000d140078090741844802603801000034014507000620412800b0300301a1840d503000010814946400038409007143d00280c0091115075094200b1000c1c52101100c40100f00c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 812308965 1250 812307715 812307757
    0x8010b0324070c030504030807060c030516020703030e01020a06090b250c03030b04022a0f150c07031803030908070b03041112190b090f0d08010e060a1802 68
    0x100c5811a4078001104803440003a5a411001d0b162075038a0300c41a02400018400000091210700c001d00d00c3c54412480410810101040035080e01e1018040f01e006000515413500000d500145600480e50189040d030811800000186d04083c1e882401038049410041c00000f071100f00c8042500407018000d24034a4082001403955110304040c1c4640c001407140502000440d1082c0c2102d045e03450001c0005103854240c1404110061900c01988106052401131980700744050001c031321041482400f400c40300800c140c000041d00001440e100000001191034400d0500c1001850914402c940c42c0c42004c40e04e07428050300a0031141308484440c8945400401c1e291800001c0d85e004560100c080f550030300b007003020042c100c41d00703030404060307407249100c20b110090712000c56040d81030054240c0300150030704105460502c4e244020b50100d5605c813101900c0d0065012107010f045900d0001044070a407181c07400550501103da00006810400032161100fa030101c1d4000c0c030404040d080700101881c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 812310215 1250 812308965 812308993
    0x80a12020c0108010b03061305010e0601020f060622090f052a060f07140102220b0f03011205011b03021b06090d030e070b0c0106180207020a0501050d021308010b03 72
    0x30451800d0600140d83c5900400c0030180e010f003e9500990000c0c0070440c103e00f0241c80c4030849100340d020380d0001d0524001c0c001c1a580600a4404c410b1610024001034941070300883c030440100e103042c451034145e85c401504118a00d502158039283d02c900c01006203070241c00c10b25658840c4640b101c4400c0c01c08111040d01d0a4200c0100008000141180b4249001d48854074003c3d000500255030b100e0000750f805a40200030302c02041c00d445841c0700500750b9a03c0304028108907003940c0004249140c10032800702c0a055400641741190b0070b100554090b18005c1c90302c0f60140a00e50b64407a03000e00509003d07442c075901500035050f00540c0011403600140c0e00d100e90759480c0c42c240c1b19881c10b03420050680300d03168405d81004100484100c1151416135540d100041907034440d0a00c98502e23550307030380d091040060401e2450007454441c0c03015420426141c000403840c446500c40c890500c2000a035500742104560195580341d09039002c40250345681e243e2081c042c08503418010b2180c02404540745400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 812311465 1250 812310215 812310223
    0x7020109170c040b01110109081e03240a0f03060609050603030901080406050702330105030a0c060e010e120c0405222907050d061a270307080a1202 65
    0x7050700400240502e00010041c00300500c0c8000d134503810005200c142e1032108100340a401c4821344a084010b9540400b0300c3c04200da90008580c00e22a24420030902c1000440b2007800e0381d45164910425001c41406000111110761940c0030402420407032900206002041c1d00ca801117460011051095a032004101078982c0304002c0294007103004000070802050080d40a40c1c0d0000d003d00480c0d55555150040d10444001e001902e01e01303c08240164088031280c4601c1c50042100b64001d04803d1602e82e03c511500358113001c1c01c000c0088220704034545078401c21450602ca20054000f001c884000c821283d2655002c00c0810b01980c106030200c1c0031445100d489009007018403008000c03080c0e07545d4919003040201050301d5406142c1002d089542e0f01010390a60180150351540d030396829840011105450003540450b00e69182e03175940368604051141100c01d402e83e0325042e084000f41001d02080650340c0c81400c183c1602c1002c0340450341c0c040000d450301060740514034903014a02500340490b81c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 812312715 1250 812311465 812311499
    0x1b03120f090b0322151a1e102601090c080603030a0909201603020106060804081903110d0c0e0a1520150f0f010b04060509011b0807020109 61
    0x14138003554006034190310b0421241e010140711310284000d9004031400301090320031a5058500007018034036003141920303191070320004202103149207040104c003200000b442a0182e005400510921040d035414113810b0384020482141c1c418003499032135841c0d524a000600d9842c0006002c40c5c01e40c40072465620300001540c84a040315542c2d640c4030303403e0240a00140c0f1721401c0d0f030710392980b50410b048400700856028114001c8086500c3e01040c410b03040017429a11143d20280c04e214144080c8004103480004403183d6041824044005038490a011001051120485500c4440115103101c00c040590001088201590384100025204008001d00034605200782c0c01422186141200c41e46d025890101c0054001c04031407454602003c0458100405c03485c0b80b40b8820b03200d108128200300b580c0c001e10303001107540404401c6581004002d80051289000e482e051000100e88911142c1c4501030076170050300000d01c4100703210780d107141100741c80e04011000ca01080804030045031a411415145030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 812313965 1250 812312715 812312731
    0x1d0609070909050c0d0f0b0a170f1e0d1425020a230306010b09152b05091c1b050f010b04060501020307150f020904020309060405010506030f0a1b03120f090b03 70
    0x10623649400044030f108852000ca0644c03034040c820750091104002d110320080040841540452400203103569424014062004c1040c44042001407801c241c800058450070140850b01040040c420000c1450290090500951044ca00d6001050b0303400743d01c2641a1103c8000b0f180ca0861005500b0951540024050245c42a205119802c1645015a4001c45011003088801c2c41c10f02e080090400c08100b0000e18078420003511454141c0d1081803040c45c2d40310040d04082e1411482079034640f00d00c414103c201c03008000000c64482c80c03542d103c540340d682c3c0b280c1c400125640c9540f01c1d1600d501070071a68807418859841c01e1000110384d4004800c4402d051751105402608100c490041c0c401445000a25508558240046200340d00c8601c0118003807902c0380005d042030710300340c40c10034203482d001000517000350030061a860200a0002d41c1801d000d034480812540400d6503030245644504c035a201800d50790070100103d40e565005810718406651541c0d8040120f03850700d0081c01103103c2500c00711 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 812315215 1250 812313965 812313979
    0x6090f060a030f0b040c2304230109120b13050721060509060c040b13090c020105090705012303130b040c030308091203010605071a0c040f1d0609070909050c0d0f0b 72
    0x603090000d008011038050480d01c040a04040e141c1002e510b84044068400d12144044011480c8030b6030820200f5009201c0460703240f644cc082965045861080a04294001500c10008900300442401f0003406844880311410000d48202d2100c0103100ca800800c0d601c0501e0203010940044012422920824442c400c480ca8589008074042c507540c01171181081d4030301b0302c0c140481c0060782c1d4040d02c0c420f5111036002141500b02410b80506251041d1300c158140310034a1010081244965502c1d14011501c1c814036441e5501e140794215001858900140720300b490038100800c00c180685500c2c1030301d010381e85900c6540c2e0b412100503922500c60600d084503d4041c00108101e500c510014007416115501d006103003081e5401c9804a113900756119156504045400c7c403070341c1e0000c0502001416201e030068000005141c0c0010002c2d4007900140c02216180c0005203000d010303506000c01000e5404c001c1040d07103805000d1130350300e03006194890401ca08000003400c0e54105806824840f0784010a14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 812316465 1250 812315215 812315237
    0x130f050c07030e2106040f0303051003021c020d0f060905240115210617010b0604030807021804061a0103020304021f020106170c1008070c0206090f060a030f0b040c 72
    0x1500f1203095041c0b544400220a0f0004c905414005c1d00d00443c4594146000542d09160207000c0e1070009200807070a20b01d030901040982d80d94010003604e0508a1901c03410000f160020880c40324061001829483c0c81c990301404001c069484542d165001e02c040d659032000c0f1001e0700e1012041d005002c80300713581ca10010b02c003024610074101d02800260030b014140e8280b2103041012810410a80080503540c0c1408100145448030805003107000d110082050300c642d070300061007030301031801301906913a000328851003192150b5021501400340c1031548083d500d000c0c900080586152161550480c405802c108005d50090090b6801194010059081030115240965a113240e42c09424215920742d5400a98403101c4c00501c84c0102c4607801404c1040540d1050001807207404c1c0f44e00d401c0200e28420000981d62041207848119070445101c2d5071802ea45000640d44200c8250203980322070b0014040500360303095440040440c000100074841490440204000ca8110b0200d0710041654410301d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 812317715 1250 812316465 812316469
    0x100518090a0b09040c0f060c0201050304111924090b0d050a020f04030c03020a08030c0304060807092c06032808160f1b061409010e130f050c07030e 65
    0x54194480c01d11100080c00d40d03a040c000030b4009405560076160714501d810107121035803041c6c1210380a00000c0c20010602030f8281d0000304207100c01040905100011040304c1d000b5074030940c00002041c10382d003024500035200d591410038154490040d816420741000b080c000c0074090031100045800c0601070900b05012540a10040d0100511f55214550300f001480408000d0402400246014141c1404058150700c107100c034648082c3c00882c610b83c028403241c106200004215025607205140102c0c4c1034403a801e0564044000707412030403c2e1011810341075043c0e6140d0303424510413a1405003e001c0c90b140c0209145c3c9408448a407c20040a80c41505c0700302c4240702003111825111b51540e40c0b8200c03c3c020a07458603036508404840740c521159210061140100382c0c801c503110b00080503074515240180c05418074042d000c0300c48010034042641c540c01d82c02014420b80300240585420702e14009040d201005144032522003171428682030104940281400a0b94080b40d03040c3c80381000c070151501 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 812318965 1250 812317715 812317729
    0x30d0906030b01020c06040f05010e090f06120304150815241c0606020706020f01050906060f0d1719111e0a0c0b0a080a050f07141e09100518 62
    0x20b24154420f09001c0016130301c502000b40020720600812080003400c0800040c0b4200503981d400341300350781400501103003104050015400003001c403860310b00c0030741034038819096010703542c0216440c0840070b880304a00c6802002240c442c10312022903450310700d4035000b0401039649050300d14007914982c8000c45059443d4034014031f50501c1e81800c142162100c0460364050798410307001900160001d40341002800d4040210320020b0b80340200901080c6045801960344030002007000c1c5c0701d03a5100001100b15101c54003038821258106801460740300c150740492829170700000a4209111050285110a6105242c201404a248009851103521010010300303c1c481480c40610b85009851041000400c00d0356a20010135a000640b40c0716111403001a00c0603030014105c100182c00e0204005004020440a5a0046450622462603041101c5602a50080120f5805400600303511100b40740396035009406100421030f4a141d450400041c00c4446024502c0301700c0501024100116072071808a03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 812320215 1250 812318965 812318981
    0x7021b03070314030c01050f0f070f0e040203040b060118080c0d020a05130c030b0f0d030807030e070303020a0b09010b030316081318110301060e0d0615030c06020c030d090603 77
    0x1001c8070907542d143d8881020046034589010711a5100183e500703101e820a01642d030380842c490b91030804605d01000340c0d003001c07200107200404104c1851004020b0f20700605c024429400d003d00f04540b285424602038010306015034009000c560807008a1103008a070340101c0f01503640503c082c00c9030107208010b20051491460040b0b9021228440108158543c0c000c102101881d08d440800c03191900703000a8100c581c2002c40601410780da103c10b040b961121020b9840b56545454118400d40d04ca0404030700411188802d0b0407030b8015000e00000389a07000625488060080c003810205888501409089501c0c90b4078880d05508140080e0f17200c1031008980060950140a038580b80842c0c040c03082001e55101c0c0c000c0880315100a154400c885110301c18124085803029000b891035051200151a100c12038050364401c5180c08112002c00480e40c2041228030040d00212035116160b00e00390302000e8a50003440d0042c0305040001c03026150006800001044944078800298200481180600f5036a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 812321465 1250 812320215 812320219
    0x90103050411040c0206012c01290a09080114040512070311010219181802090402090915030f01110a0c05161403010e0102040513021b1005010302010f050307021b 71
    0x1107100d2024548030744c0a028854201036002d44030660409101030301c20180c100307902840d040c40d000000c0d441ca282c041840d0544081500404044003022000ca05055102c0c28a05110305d022490f0400b8036081194042a2103508000b40030400654180160501c0201d50242c026440208084d8000c01300400030b0820324002d24100d0032051868410b01d00361ba1000080441c2c822800410840a960002072140b4504d0101c3c4d107401c035035140c0021841c524990300c3e0304c030108a600046c0d24400e55070f070f941110702c17015020b84003e0640c50108010340c042a00010301c1c50090080510f00600c0701010312031001242c070501081d5080540034031341118801c4415004980a00c2034811000345904a15400350080800e14058105800c10b1b2081c1825504a048001c2c1140c1c014401480140d4aa254080c105550014016203c071440001410a00d5128200d07982c0e41c010f80c0c1c0380c0740d4040e00e1600400d05a074005c1e25009102c2c080c150b000c55251100301c030008016080b007401d0710700079000c0001d100405100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 812322715 1250 812321465 812321483
    0xa1e140102030f03011d07020d0e010e0f0d12140f0a1b14060a0f020c030d111e070b060a05100305040203070f1e090e120f1209010902031e030901030504 67
    0x3e00100c41c43d44280c01c101440754003548100b91501e04006a05d500200c80e10207000d484494a80140880161025490500c0007003003040b80f5070380b50070a10001c0240c000302007034042d0f021401c224051200c0f41c0244400a1034401c5242c002200342c004603003200d4018904149880503d000c101d4a03102d40352036864a081605004c48003182e001b19104100c0c292001c00341080c1d0804804200480b150680c0d00e80d0300d14014044200442c030301200707550180d40342d4140400d07442c26404d400741e40c0f8400d6059850142d4039206103501080d9440000d0100d0034442c1c1007500f95921900104021840c0c03e226107a031003212864800b1805100740c00c07180c4c01510240844441640b42c40004c40c1050207500984515400b10081c681d41401c6000e04d900142401007003000942101c012154607455020001101c04a00151002118194400702e07506983c2d00c2200d8089400c040025601902d02141e040c0d1080c07190602075500ca00d0354a000d5041d101e00840114580402c410054010385070081081d114884 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 812323965 1250 812322715 812322727
    0x7150b0d120c15020f1b0c01141b010e24010b0409202101050f03031e09102c1f090302130501050102120309210702030a0803060a1e14010203 62
    0x210f58006040c0c07000d40014a07940300c665200300000c0d69100748110700341d6a030011045c50100d0360083d40e1501015500daa1940ea1402400c8141880210134010300340e41d98070306001403e02860200340080307541030300203814541d01d07800403d0018802e0b0070f0145204001c0c040008001601c23580c0d00c6044191a20301c40c00080280b50100c400c0150072050341c0d40340004082e4a4018042102c80c5d900f0b015160407210380300c20610034130103e41c1e207008110715181e44018244414038a103c0240c15614045001080035090b400c072000000e0900d020081d407118085042c0c1d003a4418880c103020402070080c00644070a000721001c4221031001e03000703525030300e06118101c80044050f88841c41480420440f91102044a5140c6030009140000300d92420f03600388010f1080c840104008150220440c09202d05d10780040090b01701d50b5100d104514009504d840303440310030342c100a0b907000517604c5640100d42441c0800e58540702c003240b00380f80f5a18080000c0e03c0901c14000036004142003a141c650620480781824 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 812325215 1250 812323965 812324003
    0xf100b0a0f03022a01152312030c1b092a090a03080f0909010b03010e15042c0d0302040303020304150c0209100305010c030e100c02030c0307150b0d120c 67
    0x4071546000545030f519106606e114542051006c801012800780c84460183e07002c00700c1310000c05c4828840e04c00c0300c070551958640d03a0208255054422940300369800c118144000081e480d9507451100c5c042c046281c001140c3c01c3c004a030006441c00824a6808c002e8410b100542161344121079040d441105001d001c4003144000014042d007031101000240c1d40d4040d07104001425405a21000191100f04014480084250709850300312400b04000f010340d0381e10f0303c005000b910742814411020b6442002c22003e40e511442020081142c400948589544400341141a48110b00000d00075910400003009018200000400d6402580c50403070300641055000406800c03042e0340d030080e8142610b4060013400000e200b16004501d407800e040203041035102c00242c48440f2030890982c4950390f461804c110324000d104a81c40314012006803556080140340c140d00c0041282405015240383c80041d020714102100c02d004550782004041840c00c5e280740040310090716800d0111081500070301d40281d20 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 812326465 1250 812325215 812325277
    0x11e0e06040b130503010e0606010504030809030111070f03030605011d0d150c020307060e0d09050d030201110a050705060f0723090d060c0e010306050a0512150f100b0a0f0302 77
    0x80350f42c80c10306034100c1c0b07840c040500b525581081440b20703030807040030b00c4900d83e00b1008950031a81d0203400313251108001c00000380104043c1100710000c100005140f020803010b0103051315054030030f4a041160302c1d01d07500112000e01e0061020741000b0301c4078888450b24640210a20442889036182d0b09100d820f40d1000c4c0d0903600ea40444102682c40880c15404124081c0601d40c241c00d840710050401604040008059140c640716190154001e1160746003814400c1d0405d881501c80c490b4800c1e5a401108001011540240019259402801c01280d0450010425a80203546503074440010004112001c821400c1190300c0342103803802040b040025441c0e4a126044080c01000001001c3c03c01c80300141000b401c5e041000e04140c42c005003800301d40d07564003100d420f0307500c01d44ac800540401e02e0299480c241480100c1c104e9007828204001d0005a80580030344601c07400d1184030300807640d2300882d0806010718a040c10104200e88440200188a0340c0505061060980d941c50307100ca200403841c0c00c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 812327715 1250 812326465 812326477
    0x20c071706010f09050c09040b1819140603030f2a071a19030f0f090602030405010605030a05070608040f150c080c0a090b210906010302030c011e0e06040b 68
    0x180e034000d08010040d4410022030000141001141400b06103405414915544515041244540da03299020a16615480b031210351845d81c184055940d8208852280380b4040c28140c00c400702c6003414405100c031100191818002c0c400500194240a0b08020024039904010701c69440d400101c4845090803140191200400b0341000140620a0800300700c0c503030382c28201140b411008800c02240e80c4043c2e24042c0e42259450b50310380029083c3c0d41d2030410000c0d0095107030496600e0300f0000d0b81d0b130a02215600540c040c0380314800811609903260300341601d84055030030150654000800402400e40a1131140707a000f8490f44001200e5012035940c107200e40e000c8400c0042c003540e507443c0311000307039000304020f900040051803060800b03502c1c11000303000402e94002c4000301c50000c907405500703200c81d01a00e80e01414110140f4060705c0e20700e03103c1d42d8410091005031f22910900202d84200c1d4001c10b0220ba10b80445120420810304180007900c00440e091142c64200c501000b0018407640381e0406000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 812328965 1250 812327715 812327759
    0x302060f13060e1003090510050903040b0a02071508070801030b0703021c091101050408030d0b0a0302100807030f060f030818040e010911030d0203120c070c060504062c04020c07 78
    0xd49003c40405100c080030190700c0d0a0241490040e0100220790300142d040c0c0043c02d03103e07002c03540c1e503070348403155045010b036600c00e01d09100003040c0c0d040440c0c1c011501c0b80941e41c05024690000010f80c40c00c640c1140c003a20f0303400c08200c502c001400410711404906500040c1400c02615040000302c809241010889210700c0c0295a02000303400c22699203060800d1000034a003690600d405c10303540513205d1051003561080070796100300000294555144840055130001c1c252500309040c40e2001e02803817001c942880001c2d140449a5600b40300b136214840c00da901a1032005825801d6a50304d501c180e00c201e4440302080c40192143c041a641ca00606801d2a1143d00219002025280c041c818041030201d05100f6005400016285540007044d986071042d82c4038081d140f5190415000701c03d2040c524080c1c000100c0240c04504d203500701c402003044030011741c0c1320090350503032080038032001400003800003a0084040e03600f00a45040d4010341400b240c95401d0b11103031360b5224000c140c04a02c60f81509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 812330215 1250 812328965 812328977
    0x3050318040b0f030303160903171308010501030c0e06040b0405010b04060f020a050a0b0618070e1f08010306110c0102040306051e154b190302060f1306 67
    0x1650504080c050ba03440040207840d400005030712440066260f000c01040c0f40480f0300d052440e00e543d6071088003031000968000701016110007007865907400710350041c00e0440b4035200801001030807001c14865141225003107410062681d0806041c580913031030282602e07900130340341d10a0140940c1d451044600802420a540c0c3d40d0f03a1401e00c1c0500208241c0d1844820754110f00c040c4800701d0070204101180680c44000c001c1c15969080c00242c66640e013050b0381c1ca2259416080109054100c0c60078007207418102d0340051481049034120b141e040f9540004030004030f2141c010400a201d91f00f2540346502d40840c60790070851014002030032600300b0351050720170b04d0f125400d100f80e021208503142d10f408541d84801c7c940d880e000803544c4c2092000110140140d441d4205520075009560400103411550780c586c1e0341c6010100b4241c9402e0507a108040102d1000c4c04100c0740510b010314802400b0720111220b01c82c1d00b0b18640030000310344c01000d0500c0e44090b08001336000d80ba039410824020300080d444170 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 812331465 1250 812330215 812330257
    0xf0e0703020102100207080f0d0e0d02030301060915020a11010207181a0402040e01060e010e09090d0210050712090c05192111090601090f080c2407030c03030204030503 74
    0x2032804410101301ea04d440c0c810000c800200302c80608544400700b82c4c81c0819030b2001815030240043c01c1c0c82c0b09040c0d80380100350400429940c0880154120303440d982c0c45e400301540b200c07041d0320a08a008040d6001d82c1c400030b040c40014040001c420b40104050056401c8580e40b0400018500c410300600d031701c055981d04660821070720107035042c20186410755046007001c0c2452442c0450200c180a004140450b010035110960b02c43c08909811281c00360564a1506141020594a4030b032080c11401501070440403042070034081c81020b104102d00d5481d030710080445442d9000603e0b10040c10358040b02c0240002c121901c4c1c4011103c8c60b240301039500c1038864900155050f070300001081c111110150b0310360b80f40204003038610040c1144002c4800303070000e85411005891010300f96000820012040000041708074012a20b100880b80686451803094184102181070700c04c685d014400c00c20041c0440004030f442480b462500c14401d0034014901a00c907140c030740c59504140c800c01070070703e142560 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 812332715 1250 812331465 812331467
    0x70603110406020312040f0f0b0a0e0d0210151e0e1e0c090609090709080c121209120609030d1a01021e070506070503070615080a02130f0e07030201 65
    0xd2400540c86180c640e034240342c10180002d48921403107198940a1201c103000c10184258016140c20309948925001c0d5046070303500c6c1c070491510089507041d000070f00c0d10b040d44031000310202d6179241540319540030b0510419103500e0903004000e81d8205524481040f40c020415501d0800c00e01642c880181a8201d032914240700522105402000c07041c3e02080300c141c240b004512981201e80000da880000d5880703040b40340108400d4001d4440d12644150700009202d203454200c145d1109460400c010303a20782681041c00c1c0b0031495030b1541040b4195000300702d800061084a006041e101710000c0103882c2d04c0d5590503170189000c0055501a0355604001160341500c50f0034494803003e50540e00c05075210020a0002035281c15002c1c0801c00e03119905c00920080710f605000c0c64010300001003ca5440b8412420881c3d62900008802c41c1d1441c64944c0e03003660b1b517850707059a808840b40c082c01802801e200c0e5080c06401d00503540807202040c2ca4401800300c9550324082c110030100c012008103c154a5400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 812333965 1250 812332715 812332721
    0x9030c2b02070b04060e010e030d09080c060c0613060216110f2b020310060e150a0e071214010e0703060f0506090103020702030703290108150a1a0a08070603 69
    0x80031030103540c031911040082400d03100541d4200c46042c00c050300049a9400140ca84050303c1d042d46500d8021071a080320000e400035028020340b081041250080c00082050004c0c51251641510640c1d02250024060070707141160914401d2140e40c1c003500707010b045119141161208001218052500020740d0050300b0050694242120121007044104003100144098100141302d020b202c003118003402c00654030b04014101c00b071283e24a040000941d01d45180c10358080a031200441c1e0b4400418010381442c09284000c00d88600d0040385074551554282952400d80760901d280b140794407900381d4603000c0d440442e124024102d0403940e000c24941060b0040032241681c020207044050003406000d143c40d001c00b6119480000c0c280180d4412450000034a000c1556200038600f50a5400061180131300c01c01e84050401440b42c40741036a40c85405654903103001c0c0d1903600d2001008400102c031003a550300900b83d8128034170700c9000b07a0003500f00492413040b4a50072820950b4492101040426071501c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 812335215 1250 812333965 812334043
    0x5040914010b010e0906090711030f0d0e07030305250b100513270302010e0106090b1e0303030a090f020306090105101a040504091a130b0a021e0309030c 67
    0x118010348107101c4d400016140a80142009006042010004074054001e001100c400700905046940390b0040310002900c541c40030030480c044504021340096525000030b00d0105490b8581c4030b490800c500b0200da22102c08250400c20701c414000c41008000c00ca0440601d4041d202280c1000c038410f0600d0140f18800340700c0d055074500240350109010481440701303030001110303511890220240d1074508040b4054160003031402100d52800c14009100140c60b409050b116906540440004078141051100d59000051140e0150010000a010480207501c03480000e40309141140980000d40c01103458039404503140d08071a0b5607101072002078003100742854028070001c2c0908002942241e03400a01d80039500c201c03401181c54950840c104141d05103c0d091481c566408903605142207101e0351a1840d04050036180d030b000010102c0c80c0c201090080300c240c100703121540da40c4140340d0700b881d00d540c0d4030003400781007030340402c0c00040c0c0c035081c082c1f09020007550307a20600380c22810f0128a40c60300ea858a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 812336465 1250 812335215 812335217
    0x905192d08070312081b0a0c0219030b0601081005040f0219020105071103040303090e0a0204080a050729030735011e03050d030902030a0c0305030c1501060207030b060a05040914010b01 81
    0x5c14104005074840309400300e140c00080035543d80f120010a03090340c08100403a4025405210740c81c4400540c4140704400c4122805900d01d01441d03203480d00195010101952445052031843c60705002505264001904000c034940005207030000e1074550310341d2444031509000040c2d45840a22101070f034400034411040c0c4110f8040c600d86442d541e00a8074a03032540c415502c41518800c0090114401c2d03605980081901c4030580d1440003080c03030510744991660040100305500c14560b46104040e0420b0102032090001c240c503d5622221400c0c0d55041c4c0301107400d0002250000b00c08103c4800101c1da40c0c1d120000e802d1000320307506120141c0c8019024100e0390b103498480b00010004035a001800741d0744840d03141000102c0010600110b170800700c404d4400307042625100310001c10880000010304145034103000707071840c40221282c0d0194030b8070284903540060380444400d1001c511401c51070b64201c6801419140740a81c3c800214055540b2900143e0b075140c090b11800c3d0303c5c2c00c000e0107580d00d004c800f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 812337715 1250 812336465 812336477
    0x14060f0303160807060e0d0809010501062124060e0d020306131703150405070201091226010b120f04030c080904020706090c060905192d08070312 64
    0x45900880c0e528003509041821600c046035425042c0101d03d011260700940101051080b402d4540c02280c1e01c90280f9001c40000d81c1e003000044d001403040c411031f4144c4000755100d401e9042400c0c1c1000104058103074054440c2c6e9034158440d0214115000001860b03205940340034074030703c1c084010b03044014110140d80103440110361000107070b8012a4450740f1594026045d0900c955a040032040c004c24801282c50380d02000080c401d030301e40341080302100035404541c2844140c1e2000fa08a00303035410f99900904070510014032049042c0940c8100310b040c0789850b4003480280183c10240301c840070a0303003c0740d5240b00c00900c02c05400c3c140740603079a11410a5a088501c0c2c100b940c4c2c001c00e09910020081d043e044c1c00b151840041d0f44c2e9404448249820030344c00c1c0300c51011400d202c46104240d10420001c1a12040e0005450400b00c1e152070320700601c009010342903803400d000b0f40341da4584501507203e4038124940c10344650103011002c00c080d0804100622303009085280c05c0c401c0006c003070090007d0150f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 812338965 1250 812337715 812337739
    0x4111014030106080403120c0305040b0619090c05090409120f020d0905130615090504050a0b0d0807020307080a060507121e0c02010209130510150504031b05131406 72
    0x200e1a0216811920780e40380007a0299a00e0030200d40000380d4030340400f2002c0c01c280e042d03410954141c1107117029901800c1c82440741d403680d10802c80d06c03541d03519600e442d10b03690b00400c1100104540c4546580d820f58100b00c0e01c3c0448420005003101d50742c8401703c405405502c4154150ba60240301d20401001e0ba0004001c0f1401340040642001d8052048034801c03c83c2c0c0744d01d04000b803420b0f040180100611307016500c6600c40003001070303e0301d10680182c9015515140004401c0b884500812040c1b603c058841b5551035070315101c285141d4404603046e6050303c1b82e01e02c00200b60004000355611140103050005090401c107100411341d5080307009050400e0304040c8640c030305c98200f501e066041e56000c640068402000b07582603019000e10780783d03030b548030300403074650020b0000540146124031008012008400c0c0c40d120340300c031741d8502a080c0b4000600b081c80213000091007101c8190b009112003103a14461036440c0c0000e1548205101c640100c1500c880701100200700104e03045400c11340444400c075601d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 812340215 1250 812338965 812338997
    0x3110301050f16230c0f030301060f030e0a0512030414070e0f0912130602011b1e0c08070c080c010212190c02040f0e07090b0f0f030c0306041110 64
    0x102002d04248041c3c41c00d0b1441c56145070040800020300076000c20707070070703440d2112410851094000c00c1107800c0d5406a41d80f0340200200110444e1706980090b110341a203880e5803103040340140040c100c0114076101c4c109800010174020414000c249109640721690307860b00313107065154240f1240d2425065071200c0c5040c445c0c40300d040841903101f03140040c2440c141d51800000c070300c0c24000d00e403005416240040c3ca6030803c1c0d02840042c060301e80325002032089a03603242c81d818040c40ca40f0b10746000200baa41d80d5980031002520756051241b014a4060264140ca4940f01e80325031202c4400c440084190108002a04060121a80040090016000351681c0c8418a80340740701c2c0e1844500c030021441c0d8260482c40c00364142002c0160003910801204400d0203154004100031005007100d84102200082c18206e280514a440c0e80f02428406000700f40a00384403070310f640c6042207a0305001c0e800d55185151810001188181c0c054000314022105180074049280a40d01d04501003001010240702a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 812341465 1250 812340215 812340241
    0x12150b0607060b18070e0a0e010e010501050a050c1009020f010215040b180303090d080f04080a05030703090605040606062003070b150a0b04051c1101140c0f01060311030105 76
    0x1042e000100072030003840e80070010386483d41303000e80c1c9060312005070107010401358040c040b100410002d4502c00c429540322101488004804d03c1001e04005e0408010f125a510070070160103100110304140d41400b0000300c10504050103030640300c0d41c1503543d0100d48150f180c16016a01c5451080c0040d01044100309156054840000c0c0042c14070301d050400318007114030401461448001c100c0c10342c0d4403801c02040b92529000340d0040b13840040e1140d070124035416000c203605406035600c600294500f07140000141c0b0700e508020303c11418180d0f10035524002c82c813103015040c40b0300d100d0600000e580342442e501030049454100a00c0d040c0074964650048400004105d070300b95a006950b950240c0c1e80d01e1a01c0c1c20020781c0c0055650030089080000a0305090300b005401580c008076950440e80320540c4a02c110085807940203000703030707007400da01c6a582d502a410030700c8551101403000c0c1c581541c075803145107400d0404502c8002d6a540302c4041090028103146c41c03c2d40b001c120300074021420505400c00328 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 812342715 1250 812341465 812341477
    0x120901020a0204150803180901060f02031611040c030f0f020301052202070203010e2107082505070b0c060a021e03070512010906060f08040c1206020403080412150b06 73
    0x1444e03a4903540b5680407080190344005000a0307003203a40e10341640380b8003028504048002ca00980b2070b0710010442c280551108200c045a42e402141080e50952a4a01d007021150003580c440a000e03100d81c840740c4660059010340b0b006614040340000e07004071180d003207924840d1043c074050310500040c0107a559081408500c000085450248610b030b004c5414028032620034029455072a1000840e08a0808070751000201082c505a02c0d903241c04901c1002240301e012401801c1100801041c4d000483d0304003101040c0038400c1000d0a03131030140c0d882d02e20f841403980280031f03a03a03070204105450180c01c111060b40800d20400a60810314190700c00d070815814000c6001c00c200c800700010342c0d810701c58401e680e4400703000c3c00036182a503501c0180500070700d114001c220025039600b8000141a020348000390099502501c256102c030320703001847d5150020b117030341110000d07001c02000003ca90180c0c060800344c413a9002d010038108040c54038000c021101181c8240709400d00682c0031017a0f46407820f40e01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 812343965 1250 812342715 812342719
    0x2160f0b0706110307091d16110c22111804050903070b10090c05031306240b04060e1008011401050d05150f010306050a03171911120901020a02 63
    0x2849802034a400405002200f004981810002c420050303038a5000ca04002207400414005c65181110424204020011543d007101b0700258850749582c0382c403030390f102c1101031900d0003615680901e110002c0c03d216030324040c0221601607502420000d01940c8908195100c0d10201f503032528200c003074820550001c1c80150b40c4226698000280c03041014011207982e564040c0380c140c030f50b00d412030219080854a006048130280b5040300750010324000c8080340d01a90741c021800c00c21210320390360714025003000c03150b0b0151800310000c188140e150311400c19002d0200d09104548507800e11000500141a80e00514071031980c0d03d0b07101a0300b540241e5842d065460780d41044030080c40f404c0041c0c0e42d600c1000c5040c50340034a0101003189102104c50715801d1044215220380380154800011030130354081d030148680c04106040100300040018003800f079400c01003115642404c0c0c000d040c5c2140c0050070003580000c10f60802e00c0c1c154204060240515199070030706201e0514401c0d10000b0b540c0c0400c1c1d18024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 812345215 1250 812343965 812343967
    0x90b0a090b180c0a080d0e15030a09020a09020a122007060c0e131b032915040f17031801051303051603032c090a0f1103010602160f0b 59
    0xe003545001c0c0b00e43d45072510003a250080d8140c0d0b41c90440da943c4615602d14001a4400c101500c95203400a85034640c11280b480d024216281c028054004000319002240d018103010400a03802c11280003420020380162a40c1c1000e2058800308415955250f04420481b1203101c1c00500340724075441502c80701074210305c00140300c500c41482901c811106d40c403100c0d0710280c070420080f1403468981010141011460381002103961003002034065a0142900646a103070a4240c02d02c14003580547d181e501c04001d220490401c0c6000c03c6102036030083e0421803101d051954180a42640d0350003002c45008200010742c40c000c2c401c500301144194010b086810040001090b404007060482a00080c2d0741000a41d0310081030506c04016240301d03031004601140c3c9000c400c07181d454600036090b003000700c030082414520209078104900000018081da854942d540e90044242d407852003412481c150441e502c903035a50516030b000c0d107000640b8080c22101c2031034403400d2140c1a80d086045084800b111052 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 812346465 1250 812345215 812345251
    0x71e0f080a0c02060d060305160308181302040806010509090a03080f062d03010c02010b09040f150e0a230c0909012403030306380c0f01090b0a090b 65
    0x8640c4080d1500b0060f500560108001c0903074072056000200702ca1044003207494522884800c01c10700d00d010302c00500480b000340a20241501c2109806003205401000401041c0750714060100700d07002a0407540540e800b500050102c2c1c10084806500b0110210007000b02d542c255400400c00400117110210045014022900070344800103030701807541c18446d5805503580d210312100312648000300007502c60b42c06c140d001c400ba00e0040c130644410100107420716203203030746948030000e0700e0403240400c8440960002c0045065646032040f4100000c2c0000074120401003810010850904a1408600c0081c0c481c10b280b880d8000140030700f400c0900b0f5454003219927908200c035005045950f100691302e03107007001840c0b082401c07880b920141c80c0b00348c808011050312441c195685410005400c0c6003075403003400700c89590807450540d140f00f48240e00070320318009600d0002424245d1059001605a444844010405c8046c07041c2580c800c2128a0400403203680d602c859a82d500094000c803107009040001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 812347715 1250 812346465 812346467
    0x40c030605030f1b0d05061501021c020304030c05060306091b0c03121e090d3005060111190303020304051606020d030f020405060307050901030f050a02071e0f080a 72
    0x58001090002c0507189120070400002e030f1284285451034984184400202c1914640300d040322004135000001085c1707650700c00d4481c403e10f403001c442040c158450b03108000722020207902c801c920303100036a000d581c40f140740d89000c100580c01a004070780704000600c2009040d445100715641c1c00400b201818007a107140d0f03c50700348503124a0305e0b4440035000000d1081c880c5102c5401050080d030b05281c1c51814404030303034aa4041c2800c191090001c5410151468000500c110850f40c4212030849440001c030300c420704804508424800c04441340c686610801041d507801c0900000802c1d0408094100c0e802c400c04070140604490000800303044d40800820240402000b62456040d587c004114500d40c4070074001c0d5a91406c920084002401d01400d120280414029502100d00150008e404c5440c2c017942079406410400b162030401d82d46410b1641d0360a900d01840b40501c24070800141d4942290428440f04040c015803034113501b40d480180390001d6001c0b00e500c0e0a072130b008000f036034035460b013440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 812348965 1250 812347715 812347721
    0x40f060306050903070308010e07020307120e0402031905182116061410050a0e0612161502070f06031d10050703060602060f0a0515090c0c010c091202040c03 69
    0x1014001c1d03807a110400c6054140040104211703070007a290381c1066aa112039948a82c842210741400507007061020f100010390312040e2980d080c90034200085d40d652070b07902241c00c0b81c004031000e45038515240e004807015140e521456400030700c3d4060760450354100c0058107a032026501480e01c41851590b010a008900c0c402c15541c044082c042409484003250401c0350181c44e41009002c902100017002c1061040c01c3c0c503400c02111000361482100c0c51901c50054060f010081c02e0a410884440c6d250000ea1000d010b003c1414044904400c100c501b4000c590541c25021888041590310580c414070402803440c10b0042101c00c01e02d80410191500040c1d41414501c12500001c288150302c405681d9002c00d411543c4031f100a560300300074040d66500201c4c1d40c4d003020303200c1014145004000c45d1014249401c415800303250381035002d0700b501e200400b00f0317880c81c000c85031582007140104824075842e90a0040b01c6003100c4038075040d070b0114206000310243e07429284c030007407041e0f6032410105400c1c0d0284e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 812350215 1250 812348965 812348969
    0x903080c0f0a050102040302010207120c060305180a031d0105070c0b090604030803010b031b272b0606080102031909030e042a0206070212031e0405070602060c030411040f06 76
    0xb0707501603800c60315000d8082d401a0104030b0160040600c08940c0141c40c016169040c3d400901d040021894094260300402024004240700c00402c5000d0035945020011501c40714403941d142c00b2840d240000c030200c4103c0b245000350411004029040104012404040a1301d41d0358801c0703541c03010500c00040081c0b060307500040071840040000030f403150400001c1c51051001c45926500b2007000d00094010744145003914482040140e2a0303001403c050076030105107440509541402200001e00c103809403001052048071050b180320707100400003580104001004040000c0d41941408104150105400740400300d20f80c0e44c0d00c043c0001d151044841c41d04142c0042d000b000010a1101c100301e81c000c8009c0b161154001003500041c04601c0044d29500c03c83d1160f010300003081e039034800030480b40d001422288050240120001380c3d401340c4464035000310310803001402c9203442c03c02c010303041260052510406540034420040803030070b085114828450101d900052000350b119401c0010240340d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 812351465 1250 812350215 812350243
    0xe0613151a0a080606090a15030b03010f0c0e030f0c0607150204060c1a0c030106030b0d0c060f0219030504050d0812010303120f200f040b07050304051509010903080c 73
    0x11420120303050300300c1d50042000000d1951624415503810003407019a1048024050f04856200410402000c0515602c41c40400600e00880d4210301d0100090a4540d89950040314680d14048a911240c00c202c00403411001a405440c03a8151442a140c0f19204080d00a00070301001480c40100580b01104001c061111401151030320380741c56008240c1d03000358074100c6401040d07994034034008005800c21031040c000c030403c0324590303800c00b001280600300081031142c1004900b800000040c017544400005401d0702e641d020042e809a1000916104010710030304151188102c40c2c0c404294400100c1d000d6810660310707203182410900e02941644544580c6c0c2c00d50f0011000040b0405901259000080311107171010310205034500b69110848151f4041d21112080e007649001901d03449101901d01101e5403654135091542d1103400c1c0344c003a8004881201c040c0c02c0020140a14034260781c08515510311246c100341894010b2002801400f19804007801c1c081010401448144003000403403150102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 812352715 1250 812351465 812351489
    0x42a0e090a090302160620060f0714090306010305010b0a051504060f090e09060115030b011d030307080a1112040b0304060b030f0304080a06110307021b01090e04050a0c0e061315 78
    0x50340700010100c00c2141c6440c4140c00710003147c000c4107440010030358002c407c0201001e109417501d90054640c0070482042d00204101800b1069042c0d4003800624000c500407400071441b01c401004011001c41c0c90740020784500441400d00d0318290b414800e44d01a078600d800c04070b02c40441c008061740c6000442d0302c410f43c5884500f0410000b082c000c21220304030381c66140c0c9549203401101c2c06809a91808003050300007803c02444102c1d8801001c142c562442020741a01e00d002c2881e12603a000c1d60010014802240d0051842d20003041c04104010782d0030004201c0d1b5080c11708000b4290903521015002030801512011540805e640522103242c0c0c00c2141800c59554039a200029510b601045000b910060315100204403502c8521341101c2c4a800f80d0303400f41c800c40030021010f05d8500200303241d6034104035098802042c0348038202281401303039000d14010001c1c2011458209001d000d030741c01c0101440321000c1880030381d8480241c0c021025001e08804200708440c0c01003060f201c26650312100302080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 812353965 1250 812352715 812352719
    0x150409050309010806370f08030301031a010f060e12030319050f010b030429010f090c090b0417010905030a08100806060603160c02042a0e090a09030216 67
    0x140001c01000e15440030f0303c4048540d601d01040120b080b030007552030414201e1052090346002c429060703101248a8441001c450182c403146050300f00e0f910368000d01b00300d0784004014018007016108030941019120400a569818200303084201452481030b00f05101d81c548400129a41d00c20100f40c100c05220100e9880e85860002d0411022001c00714403807140c900008105489054018a0705a8003405846440c64807140d440103494030340c007484550702008014800c80b4200c065030445009080140e40070789007605196849c401c0b078200d0070040c01844100541040802c544205032000c17110b040a00340b08103403180804030f0160101400040c50350000040c0000c5064111603130a020301c0c00c4881c1d41820940303418445542d0710041c0c03035941c1e0105027480011960700100c8400303010010f8902d01072804241ca507000c107041c0c13551200205600e000e9020905032094034034143d900502440c4c50898050040c5601150ba8032074040c04100381c1c3d82d2903200190925008002503484440c00c040d099800c40e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 812355215 1250 812353965 812353973
    0x301020c0f06220519050a1a04030f030b0112110d050406050f01080708060406020d2406031113030605041b0f031217060d050c04060305010e06090a0506070305150409 73
    0xb82e0031500d019034003055000010000750b03001920814143d21000070710843c1080c401d410328050000500322041d20405101c40002002802c28080d034940d04410b0b1611400c01d4a07000d4840c81091244504140c68089640916070b444209011101c43c1d1400005921424015048071071140c41e051654560400c1c040c401045403580c0304d103110391110b4540400b20b1b40c0b152105511480c40703106d03154040d4089004140410402e038014140b00083c500c2c0058244151101d01d43c80e4104030441078254002540100021605400b40040030045445258900703d9030b241c0101a49005010260070307140c0c0d82000074104980c8150004d03020b00301c48000a00c06598401801000d00306001c106c0c0d840c046c8121100c0414001c2988801c501d4107401c0424540d40e0345028813864215000b020f43d0b040c40b98000c10080e544035842407201442c001c000110382e100742805220308c1c21070041c018116075403100072100045840450801c0e00281949000306040e100c00d5130f0080d04450744001250711501c2e11410038100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 812356465 1250 812355215 812355223
    0x20d0c0f0b22060f05030a140f06030d09050d200603010f090c02070b04090207050c1201020409060e010501021c12020d0504031d3d0c15020c19020301020c0f 69
    0x20760304074000320051074070b02161601c0c0507568800c66012400003404204254000c4018640c081480d1000051010406441003003041040d5802001e806040040c028142001c1c020444c049800d414442601f40c030f00700c00309009100d0010040d1060400b012351a441010510007a802e01800400064407561101c400049020705489003007105450302002c04800760022540004a0f5804020b4070b091508d0241410080d612554003140c40307000310040c5034541c0e9130303030141d25403618400800181c175507040045480407108150440c29020340d001c0010041e0ba0780c00607150031000b9045009901503455810241d070190a461001d00089002040030800b248840e4400d9203d24002c0da58001041900810382604041b00024a41c2000003400a1140075040c2c43c41c001c0070382c000c00300842e00326410140c407034000e0f1500c89201001846181b0210305000c1a000c41c008040903c10085240100d06810980d0b1140d100104000d00c08a603d180e0043d50340039810f40310f0030082041911000090340c0394481d16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 812357715 1250 812356465 812356477
    0x40507050a08180d05180a03030306140301140403030b150c0a03120923030708070804080c01080f0412050705030a03060807060c0b0f0a110f070b0f090a020d0c0f0b 72
    0x1220040000c4003c014003030341e01c0c80310405101921054820130022105540500042845a440007692083c1919161442d500940c001d0380c0014029003451000c01c540d03148401c2c50f51003030f81040f40701c0760041c8040c1ca07141c4d04180c2c1070800048400c03224020800406440c030043c40c1d00403020030f84c3d003a1064045a03032031010b4442d64910641011f0a40c0c040100d9002010150030104403402090147c050803455880e186002405c80341402400e07500c03422135501102c02140c0403e80810100b1200d60704100013441d440f000d003840b8190740fa10308015900c1c054020005404a00300045019004d8014411660001c0c2c0103000e0f20b903614410007024014040c0b80c0b01d107040d5031286420004000d4410652010341950050b14200103858000c0c24603105d11002e0045200750396510305400385019600c00032310a001c5100b54598a80145090503160110002c100c080b5204060080150b5500041862200300d80d04856082580d4464101500100f8858002c1040c1000200d40841e0041d00c403000761032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 812358965 1250 812357715 812357717
    0x12040b0903010b1203161119170316080906040504050f06010905030607050403171308070f0e010e040b040510020c070512030f030f19090303050609060405010b0a0e0f040507050a 78
    0x4030fa8144140560720b40e290f00b064840740c100b40417152040c003a02998060241c021a201e550000c2c1400c005165400c0362099054a100c480c0d804011010103100c08281000e900000703582003505001107920362290b01c01009140c0f880010b07003100c20380d4480c010b03a0f0203408050410041842c045048402d17640701030701c90318041080204005500e20b000201c042c0f0882c4196034407800e040c40c66440d581045884003c40204203000c1c0030300101240f5120508000306104c50040c803401303180c41d50030301e01c024241d00104d501110542c018444290602482e52f00194440401d0b41c5650340c608003030b03040001018403800742c20300000d0702424022000800006450007140c60b0122844503ca406589101304195810414003e00002c1c0c10f0903200215554080401d2000005004030040750b0310031502d4400b41100820395400074030065042c601d84a42d401001610208031950502c3c100e0070a50003800887d40c1000400310380c030003140c0c4074019075030303900d5001800c00d2000741000341c4040c0c055000100004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 812360215 1250 812358965 812358971
    0x2120406050a050118020d060803130f1707050907020c0d0506010906082b11060f150d03020705040b01110f03030f06180133020d090602240912040b090301 68
    0x82e0800e0040c8501c50407600b40c640c4604000b00b024100b40e0280d0060b5480340250b0360344003000070761a4402d1004203902e146085008001c1414203080101540c2c107500311000f00003103104490741d0703c00002080710a5030300c12940e000c1c5d940d480d000c0032031400d01541011038000604c054541c041003400200b03181a030301d007000c0078420b094454800e41e5880141c90082400c5000f10700b05121400c0081c40c0c00c11115100d468501c01821100403803519054041e00d01e071401c0c2c900c0340100001e200c03244404868090b02118403081c00d201d6510029928480f600446104a940c1c0001c0c0d060b6070700485021219800301c0c0181e03000c4c5c00c1c8508030b480e142d41088590412402241c400915545024604581d00100c44440c6d51a517901b05108a40c2e160380d681028840100d00380d0711000d21a40010129807111415070080c003070460700c000020000340c000e40c006010341d48a407001c0c08031004054a03420040340b01c400b40130400d664045c0380034504070aa41880125000002d400f0984c3c11002c0c00610a1601c107034024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 812361465 1250 812360215 812360221
    0x618091a0102010c0c0309050f01022b080c121801150b0c01050105061c0c0212041e0f060e0607110901030b100f0f05090a060f06112104061b060212040605 68
    0xa030b81205c1c0054009000808040c0c0501c01854095950b811503003041c070407030301091500c0c00a185214a42900c1d20308448030003131070126060307000550383d0344a40e016294500340252031140c0c40441d07801030801d60045490745404420003a0942c0a280d81a08540100b00d0041d5910b50b609001d42c4540200d00980d402e000012131241040310488450482c101e01c801526049144000700414500f008401140140f55030114040314080140c00500b81d00104005034868688144900807503640c40405006241841000120740006544503119000d82d141580c4900c5481c3c890101e102e80384400d0b40c0072031000000b20070f00040e000103610414031700b00103a420701d84407413101c00c8400b40351003182e202c8000c02c00140250705003019425001700c1001c42c089191a00c45904c940619095080000010408403418440e036000304840c40400410601c0101012165a805905c91003039000b5078003802010503441c01c0305454503000c588810b801c0902151924040d103440b4010341000c0c8c2d000d517006070520f008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 812362715 1250 812361465 812361467
    0x1403070503031903020f030c0901020607021c0c140303040303060f140603070e0423070f09141917010207030e0303131404020f1803061b040618091a0102010c 69
    0x86050320001002141041c2c080000040c0b00c02c240101e101c1055002d00840c00c42614441c051401805e100800c82c0e01c60149000080c60054003c3c51130701150301044858801d21003d4900d03940a01080c41e0004070341c941410444c0003e0007140481060b880000100400d150b80f60b4401401e03181c894040c04449507032400fa4042680c03902c207040740d2050041011902036030050b145072800d0ba101510208a600c2451a0440203010318002c94060b8001c00003005000c0e984000c24000354200303810450403440c10141002c008440b2207445a016407000f212410025810400403802417085503008001e410380d808580e40030350000300b4200c01095040d03510624614022060361840d08408020f401e03444d152040c0701c401984091078040d0800d80c00c00410410152a00080400207420404541000d100748103040c030709a801041d100500c84034607031108001c002a0211000c1300c100c0e140110030582d50219a44141e00c0301d500080086140130041501641e03414004081118260000c00008d0f039100384c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 812363965 1250 812362715 812362723
    0xb0c161a04060509210604020310020f0301050607060b0607050a1101030509061306020c0d0507110d1a0406061205060f010b091516060c080103060501120b0411281403 73
    0x10601022403050009004882c440d1010b0b05400d8801050312154200d164003142951000004030101500500c0800080d41010084201d0100c0d100300214500036428544201600041c015107100d40000168603080c00b819404c0001e41d440028020ba540e0700251400d0707a92b480d24031004541c0c0800f195061285903000f4401d2600c03030740008004e0040c13540d4401d400705030302034010700c12103a01e0b82c24041114200001c0129403003030102511071541c4c4452a050011500c507800911520803821421010002045503c1c801d0f205841090644440d89842c40e2000c0503101030380001e0008104444010107205002030305a01901c000000d150059032260310316844d0f40310701000150021a085641e0340d0030580e0000400da0204401c00f050320074101e41da62001901c4407101044002490240103109010091094078014a0b20403000c81e202003d541d61034600000050001d409491804014260741d100c00c0d0891310710341d4a01d00c48220404c1840011101c0644d240100b81c2c540b600f205a680160400107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 812365215 1250 812363965 812363999
    0x40209191823090a080d0b150c0304060f0e040c08040b1005090606090402040b040e220515130501060303180e0421120c020c1305040221070b0c16 64
    0x48100c942d4101d0000a100740b0203800f40440c000740c4a5100e007200829141c030090914030341d0060000c1007409040302005402c200c48001c5080e025010440d445083c0700010855048410506208689405040003641c042007403000c0c1581280c204144007105c19448030780c1030b100d03610500203021a5101c0714800a0104500d0041075080400100412402e1801401400c0613260080000d8a03040d11600a18261780042e072102e00d00a04807014822240100102109848000714002c01032a05a8554541d10000d00c07030311880036501070380403488036540711084400b0180c07c440244405966460010700c01111908052200c041d60b00c008186207010b0800180102d402070110401014660300364040c160142000d4820702481c626525809000b5005408450300c0d01d8000d0700c0202c004800f4000d40949600782c034103030107141c003040200596540f0080d400000403080c5102c0240c5d00e0340b6038a441d10f0030582041510410104940901aa0014510024200a002d030346001d9a4170400ca9090210315 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 812366465 1250 812365215 812365241
    0xc060c0b0f06060702121e0307081c2d0f0c090e070519080609010905060d060905010e0703080310060804030c060b03070b040909050105011707050405060402091918 72
    0x2040109400c0d4424414190300000010f000c2e41c90300c1c1c113645c001000b0041c01d00383c82c81660480002140102c1001d12402401e10351400514a00a040c0e036a0021903c01c00300e8841c0b030f0704040a6030b1141c40e03503030798080d6002d000704582d1442d207412815198604001c0440800700f800381041d210700a42e081c0b9000d000149182511506a458104050911490001400c41040080501c0003c1d004904444461007600c0c280d21108500d0800000740480018143c202036001c0d82000280b014986401c400d2020141c4c100400240010541c0b802501600a05401410520800780d0120501c00c0d26002940103804103158a244a61b80b03840940b2161821140540031a2503102443c0104105800040607910f00a094640840c2ca40e009207006810980000001c0b50344d500003030782044003d00c920b0780946191004c6000031030021480030b56540d200e0044074004e42e150700101389280c5481e01a101a104018000d6200002465500d6030802c06889500104001e1204a0640118500c2014140d01603 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 812367715 1250 812366465 812366483
    0x3020904060b210706201203091203010302010e0607020301090c06020f070f050d15060b0a0f020f0c031e0312040f051005011d151f0306080601082e0212040c060c 71
    0x176002041c0ca0304503950100c51800c032481351164551413024000540010045c1241d507440741427241c043d40c686040c500b03100d802018200f00501c003503a000505454a55800c68640e80c2e2405140f01083c090a00d00718001c0c01d0450485020840503008103050f20703c40030040458103625658406060847c0007441a280c00c10301603000d030404035901000300070001c1540c40700860029074030400408507a01c045c1140000440d40b00007c010b540c0d0600007801901150340082c6000894480000e8840d400c1074070b05c18004052046106e500b00050054030600c0180c000b00096030300c3c150400084040b80450208c0da6402905811034124100e03100e020305071419a04000321300c5032000250000c014019002c01c0f981400030350b008a040d034421100041014603501c8085122054110150654040d0740240800d0b40100c001403010a000041c2401e4455840b08011100c01c06160340040e8000e0365401c120341c1c01d000081a12480d44000d5151707004900c00d40080341059035035031007101c000d043c80d00010802c41e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 812368965 1250 812367715 812367719
    0x703062327030f0a03020315040519051f080d03142511011e0b0423130f0606030314090607031218050601081e031902030403020904060b2107 62
    0x250000000007000c1e000d01201c0c0742540d155100882c9404c04040790b00000d40000401c2440500e01c00921440403042d40d045c4181d042c8860340c031040e20700c01d81e4002c40d019604e00002c3c1004a07000d01c01c210301c2c008647c40504a648451940e92505241005200070030704000e014400e010a0300e071401d00c9996001d4040307444080c00080965180c040700604410892581040d440384d00080c8143d078040011801d40c3c0d10302200e400e8a84054860708442284540c1c9082c402c407808601b6801241c11170b032040b800783e08455458800140d2905202e0801800000c0d01406010802a0503803003403081c3c074082d884402420440c3d0320b144001e4454a5956074000c14144600d40001e80034850301004850700c900b0108031000040c100030100d441107d070544655200100400401307005000070300480740c56010184c1c092a80160791640ca10031555403420481d1217000030307004980b082c41030740c004c0d5600400e0b0400a00701810400050054a01c00c14403035042c402544800046001110354040b181303201a100c218 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 812370215 1250 812368965 812369011
    0x3060c050a081603140a0c0e06090f0d0203030d0c020f0c04110901030509070b03130201120b0a293402091b0c1903090b090d2307030623 60
    0x700291030f15018591507a0310800c010954052880c8600c00020340020506400e03680103100c0c02c00e941c121307030041001704002c44181d04c4000c0030324550703e000d41c0c11200511051020a01d50300c2480d0f10507071414541425405903950216140c6280d07141007045801209804081208590350510b4080100104005020155000b07800c1554007503031050503240c00300c0ea6440048401c0c2d000700c4003420b100c80d5a030780900440d078000919105002107030808001480c08807000c9040c00b175040c0180115440c00c043d05440108800c1d42d40d2088119400c1c00795181c681e1044448034079080610700b41808502860322000d42501c40803140985c0d40c0091102c00c0d03903285c8949860b890340d910a500e0280e03410800c00b200351072404202d034104520920401703012050f59810014246155500000705800040240d11aa42c0da981070388141d03280c00c0416081210004803461070007810b0103040e041340d800f90701340000c1400500ea01018100c0004603022412642260601b00e60303050807102103502c05c0546040400319 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 812371465 1250 812370215 812370241
    0x103050402040207050706090503070b03090618030d151505030708040803060d0c0b0703021504080403061512050604140a0c23090408030108010c1e0c081b0703060c050a08 75
    0x49030000d0401450010b180d01c5d5a4100700c1142c204401190711050108260f04042120034000c14003440c0c00c50030b6003400000d603a00d075003000c2e107000889509000000e0a0000c18030407910900080001001001d8844413804148102c40c403802c00d10500342c4042d600c0c41d49c01101104c5c030811440d5900481c550f200d50716000d41d500042c0102c1c1e0002c40000d00d0318006007003140107001a0400c20102515500d42e8500207103001c640c000b0310801030303107080103000001c2c18400540e0b0a030303540060003107401f105003901c0026922840d44410826032001022030188400400c0d1240624000e143e646a034101c0310714030907602d4440c050001d044600d55a810005a05185041300380c040035541070390381711103012000884000080e14250380300e41001004001041c42427003081a0311009041c600010145400d41e800c036920500ca6090a01011b102c0e032000300000d0030100c42204094015580740c2d05882c40803940d40300910b01088401600c0c000c100402c0900500c2950585440c80e0f9030421075964158540c001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 812372715 1250 812371465 812371471
    0x30a0b0405120d0e160e16020111041e0e0613020d0f02130602060906100b16050f1510030209012106090f02010e12060606250303060509010906060c02010305 69
    0x61800752070642030301015040c00405500c0e840000c0414190700f00b81191741017111801088099801c06081008034024a02c04d855101c20006107142d020603814505901400e091844c0320045100010b002c00c90f240c102201d045200c00c40401c00310300c40d8448000703181815054400c0e5a00c0a141c5014810040840c0c0041c91110149a00402c0c8140408941016a089081000b424003d46071342030004075810041194400b201c00000c0005050554800c2e4094616000b0014104030011f08031f0030340c03a1240d40c1880b94552000072131b00d0801e20301d00815190a80340050801480920700480c4200c003001c00d48600340d940045c00550a45d103042c1c418654031140805c01c40030448285410390102d1458400c03520340601602020161078100d00c0010721008250407007a01ca03002c3c880f0410705030320300086c146a0081c810342c0c0d51641c80d5111160741200b40300c15804100c00000c0085218201681600f056040f02c8060b42e888007240d03200c070440c200b03481090181c100021070522844000d9842600100c0d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 812373965 1250 812372715 812372723
    0x3100b0402090a121a040210050a02010e0609030a0e010302071a091e0a12170106030b0f1201020d0e070b1903090203030703080114010203210a02190306080106050906030a0b04 77
    0x440c1518410100d00d22260303e84c081003ca00b9854100c03020721002c0740b40e03200d4450340c040b08040c00d80340c5a070018502d81c103c2100d410400c036010480040c0309000b544040e00402c402ca0443d4058900018403995076031144401800103140e0940c500101d5009001b52410030b0344c0000c1d803100103a142c0c0d440c5000000000d0801c0c640744200901700640300c0746007542d141c04101080242502c0e0001d81410365102414043c1c2408101443c10788034600180032001a06554252a0100d0317040c6034400001d01403500480015805042e035031002010110541c000d1040301107600d4288081d0940342100341d01e9081d03602c42ca12464404202c1441604400b11200c8152040d078140000c02c94981c2d0046855030300001070440c0071840c40030043c081080540c3c00507021110074402140303408005542a07204000110142c8115481200407410a003059010f65160036466800c1c0c01c060701c00c50800501400c046d100e030391410751a01310045060304090030510300c500e00c044d000b80100031907603950100c10140208280c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 812375215 1250 812373965 812373967
    0x105030406022d040e0106090501120b01090824010b03090d0e010507080406020d02100501050d02130b03240619050f04110c0705011b1e06020702150c1b03100b0402 72
    0x94462152602c10700e02843c1d8000800d803a1420b10f8030041c042031060b0480303410300010700010051681d0000f440c07540e296007a83d01081c281984001600c4031082034003da8510300607100b0076210560300b11084076811034588501d01039a41c1e104848003281c403054400c1c9006400840f0b40c0c0d50312394010242d1380564030040c900306190205544034807455811a400100050708400c07480c40780c00754104207141051104250810965144c840081c0c11100041c0000307018180b0b103465a00004000d600404070548041c00780c403003403101041e500a09491070144d40b2000e03465400031440900340701091007008a03481120101c580d09000c108408004d4030900664015101e03182010344d46040c00142c0a0b2228020080c4a0139090000143c04005110f00070f070881d2501441d4180461200f44032202003901c000d0f0380bc06800080c0c00c0c07507000391143e004082d41120030b8079004009081080010300b1501b070401c05540072802000d555180c03080c2981c0240741e150340070b503820390380070000c5a00181007070500800c01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 812376465 1250 812375215 812375257
    0x2120a030b0301060b0304031421040f060c030b10030c0203090a0905041a04030e0d050a060c03052406030402100908010207080301180c0e010e01021509030a02120703020703060b0d1a041103010605010503040602 92
    0x842b60400c088070100c03400300381c13402014104221405602c50400044c01c00303002591031400820b82c040b808005003400c058072442c0040f00d2900900c115404020080c0079a00d001da100c1e040800070300b405403000c40d5500000d40c1400d03888000d41e11a070303000d0b617890b54401203450046001c10030b58200c1c00c02c2c203403454050340026400040180c811000b04603407503100030445181600181c100c04805000111051810070301c00b41e0745a581508030707540a581190b080e41e02d00c1e40d221085030040c080b40c0291105600c009040740a020310038010354100c0e88921303103a5044441040311030058450103000d481c04210503100ca8683c96009003038400f550701061040f24180e403580418042460820b0303a0a00c00c503000000d802c207459506011f102c0786c1468001160b840c3c000940c1d4000c0d69025903102c040e02c0c0300d54a00700d01c83e050303448819044d00c807500306006902e105c0c000c84498400072001d4070b04840640318000c1c1803e00d400c0600a5500300e0b070050f1034540c1560b40e1070b2100c0000e98030000315200044011000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 812377715 1250 812376465 812376517
    0x21020a140301032109120b090f0d12050a060f080c0415050915040b04240b03041a070201140403120b150a0e1201050106090810060e07050a02120a030b0301060b03040314 74
    0x2030001047c061002c440d054242007a1642c10807500c00a0f102045d00445c07103181e023a80c1c012040071001c0e08030b80800a415564203644000404068210740148103009034001000380001480c86c460800c222001c01c40800c1c0c540c4c9500ca041d0441c072070107400a4615000612051495008680310310014001150600340100050f08075400d042c1441c0c03042c80214004002e102c45031704a030f00a0030f440e220f07007440c50030903846c0c2940e50500c910250702d20058030000220b000342700307400010b4040303070490201d041070030507107000780480c0380f203001200503d840c003a801e0b0401e01c0c001d1780400143d524210300c80d1508804040448074000c0b1014100d40080b100b0028250190091186078000d0050795035440d0f03140d0420043c2810b111006181102c001e0405106010346070414800c15045403c0e420b21558a14481c030050382000a414591075921001141a050b1345402d0381100713035941002c50080016540760780c2080380d02c0c04140c2d805000103281c0444400240f600b4070060070010001e800f00c0b64518000b080c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 812378965 1250 812377715 812377739
    0xc1d06090a090501170609010209061b07080319021605010e0609150f070210080402032e05150a0801110a050304050f070305010c030f1a060a21020a140301032109 71
    0x1c010b15480304803100319100307113000f4400c10740c0107c41c000007503283c400c000001408a020b1244840c0b10780559800014491000700300c3e040041521034242e07500e50b2240b08040c3c54821b0105200000b5000300e0760391044003140c686100042c1c030b005850b8440b541c10311806006540d04800607198010312010b03485903d4100c03400103403e04e030703e003880410b9480400c3d2052000e8105908060001c1c4503d5409000c0181d1303010450581c0310130055164152030040380480803140c50200340501c200761603c2c0500c112824800500c0744400b100340c8444000c0341d610b210341c0b8207d405d4a5207004403901c040c48446a140d109100035504680200100d40c070045802c41203600303040707030341e40215160380d56854068426a0107010700312803992520000c0204104102c00400410100e404081c0b0407080016443d07078050044014100f03209060324011a0601c1d1080090020740c081c59000d00860004030904101c000c0003c07c890680c1d90261402400a0784554080360111907100004140b0480b10702c00309504031645 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 812380215 1250 812378965 812378969
    0x4032d03142701020d0c080906030424050f16050f130e090a030e0916030f0f09080301030516061413030f080712030221100f0305030c010c1d06090a090501 68
    0xe0001902d803854000fa160241085110050004400000c1c02003202c160990301c0d0f0a400382d4007113503030b559507150042c907440c4d000b40040300150340b800c00c4105505050b03025510410092030102665103510b01c031000c803010b80c4081040045c0d01042500240000640a401442000908811580d480360040c40b8646004c4481e40000d5104091080906a01c02c8007035000100544003d0390303e09000e0717031480d104000c038007554040c5520340000442140b03942d804126110020103003080100b1091410100f50342c400e00c03003914140306040250f1a4030448524040842d1202c0c1c8800043d1403208040b05c02a410104010303c4440d40d81c20000041007140c06426480391281c0803a030398400b0f00d407070400410794016081c90f003014418841c4034400401080901600c18000c4c3d110078282e9030b03581d2040c06201e4a0742000020080c00c4000104012000010f440da00354010700070702040c43c1045045920011400b0484a52071005c500d4034101d05050000301080300001d0044051540c85003d100103549003a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 812381465 1250 812380215 812380267
    0x306050903130f05131d160303080603010b0904021009231e150d06180c0807020a030507020103050a201306090b121e09010204032d0314 60
    0xc00c44030450088560b00050b0020003e000100b500301804120382140300f00c0280c0c22182c0d10126560440d90f003541451101540c0303802c99540c451012042d1040f0903041c40300f20049104500071482c10314041c0100501302c0b601a0030350035103a40d603808114010007403030001c03000d0281000001c90501505040c0107803806c007030f03c0da5060119000c01444580a5020450760011000702443e40a55030352250030428070b46560011500d500e8400d9986c401020107512034042248043d403000440b000d59000024111210b0f01c0c2d450306659540c20581c0c492114000040018a0804c2104c00643c001c1c0d120603002500d0610009030f500b9616803e19030007807824980815003202007000c00000d4141645000544a1490445807140c60a6032060b032034003c01d0350030340801550b0000216588012000350f2084242014600329600b00003107610700031351041c001600c2d96905414010200400030b845544040020390744a200c1030710356141161841c82a00300ca00700c00c1e400f004041c01c4201d240c2c1080a41c0c80407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 812382715 1250 812381465 812381467
    0x6050a0c08060306040506010b0903120c06011a07082a0d020a121716020c15040e01060903080909220303051f05010f11100f0213060e03250306050903 66
    0x505103000e0501040249014402e6004030100b00020b040454800d044480007006191541c3c40c0b480002d04185108400c181c08460108461001c4940043c116040f038040800d1030020061001e04d000305841030f105c024000308001c1042c0444030035042003103807051340e88060440d64030b0700703080c012402e000844000c0700050b4020070a4006108200100401c11995400d00e01140d0482500030341401d1801020380175060010110b11480300e00134850160300f90340041400341da2100e0b5644012182d0070038060b10142007503171000070542d076010304841010307241c0220259040c0394011040095205009050044010302c495070404000510450341c4002c910a032008502c2c0d00d05985042072004c04010700b00e95000c1028030400070340e41c118810404800861800b00d418450003c0310718540b82c00a82580401c91402146040d80802a4050300020f050110020082995031a0031030b0045422031900d80c2c16005940719280d24440b1900d88440d880380c6c2c0d402d09400707981d251900c0c8200c940c110351400032608 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 812383965 1250 812382715 812382731
    0x303090b010315110c1902061210080d03140c0d0e0105340e01050c1623090106090b0a1b0305040503161203030203060d060c05090f0d080d020901050706050a 69
    0x42e1038081d0300c00c4006880d2004d0704010713a40d45d90f42da607280c0400030310558a942c2107104056444400880305a41003000d03150700a0b041c1402c0d1101124107500ca11051409010b14207030500d44a800b507514000c40c621802c600c01c1c0c4a0807001c81c156840741c8149400d5907070f00c035410240703624207002d85442104007035988010200341c06140d995000003a0008140701d032100f4115401d01d600300340c6407070450500b0b01c1e01d00d48a03901c8408070b907d841e038030344142c2d0061aa41c02e0001120296645201041d003054042044030350200c509000000c1d00c00c0c0908000724803080c0d4184410200c0002414864500e85050441e01d500f0000c3c800f12410941011b0b40004d000003410701c25800e0810070692440c034446001340c1c504ac600700c0c400b0070b01500d020005080640020200e1030070781c0d03000c4420446540042c001c00c00348101e40300140283d4030500803140203000e43d4130340c0c54a0f85001d074003488001e604000e12134581000e070242480254084001c40703050001c01d0001c2c001003403031803003441d129041501001031208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 812385215 1250 812383965 812384003
    0x9060c021b040207021311040f2c0f0a0f091b030c05090114011b021306090c02010e190501111b1207050d0806030c0d200105160b040303090b0103 64
    0x503000e80c00d800c0c040c0c3d0042215200584038089a501e4882d5a0240041c20503203441c800340c3c552145178400302d0015001c55000c203100c0a02c5c1d440c015240364004082c4000c070b4101210717683c1000c0440d0584440300101d00020740c5000ac136080703000019400c8400090000113551200c1d083d20180c80c2d48021024094803c0c0304021010420201500c0115050304040d85044819210740c84101015810403d40c9081201c07031071400c4400414140d4010b0042d000c01107802d004100a0402d441100c0b52141030034031420403540103201d038455150700a4050300d0301916480c0301580340151100c00300c034959030703ca45031404140b00303c1c050f0032110114040c040303841d02281c0d170240c900b031041480203020725010420b00000880005441c01c501c8041c0c02c0030704e0a40d503880006418668912140c0350401110003144081001100400c480610564070344203140801c000119000d0240d40c420003410b001001180010414a252843d40113100c1e16010441c05d025a07a0000d1800080c0e200301e811100e0201c10b65514 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 812386465 1250 812385215 812385253
    0xc0219140406270b0d0f0302060702100519150f030f0507080c091602010f0509151e0c0c010609061d0f090316080f13081204030c061209060c02 63
    0xa00c00243c40d000d180c52407040100404254801d80411640e4840b0340c0f9810b921521050030141e50042040e0080300100d041c065100c0100b1546003005002e9001620080c110511070103000b04490802c044100d5004144e400040401d0b600f10002128106070000d04219141c0c5450b001c0d5200e0801e0440880044c90564541112900401e00301d40040070707a00d007113840b51800c290384a1502550010034111488003680184405112a565142400c04100c130945d00060704900c500130112036281103584201c004050400f00c0440540e500a0350004141d00d918694003038400302d164880002222039482060b482103450591040000241c020b0380143d107403600d89105503020718410380c3c6283d80c0c60f104036016200e124403851a01c1c0b90400800316824000030078203542d00744080700d0b0741568a12014001406900841c800d0b00e585102e51161140c141c102c0344141d4080301d503c186581d442c503042c0102954507000e20b603801c00c2c11030b40c0e60b100480400c51a0084010300c40301a00507150616814411280c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 812387715 1250 812386465 812386469
    0xe19030f02010e120a11010c031a0f15071b030b07090501032d02040b1209010509240627060312090d0609020f0603010b031f060f0c0219140406 63
    0x75039240c41c078510003004010800c10607076901c16044555440300c8500540d40141da140f107092040d0701e403032010181e064140c1e001940d4000c900440550580e81c5c2003c0210445000e010030385c00c903480000b1102004c0e50f0b10040c02016110f0b90b0460560014036041c1c0b0304641b2554402c0d62288460005d110359a0341244460010300030a203401e110002411309000401c81813040140c880600515032010714030b0003503050b60003806c0f07070081e003030341d204120784000c60000415100071101e5441c007404180c6020000440b205214482e10b4400040d01c01075064642d441e100401407500440d441d181090a0b001010800702c0c1102d004461882e141411418185001214404031910441c10002c0302020303a07407480c1900d02c007684420f011442505510200b203102c0c3c200010540c00000210021501c02014000713103100c0d41e000e07110715460003140c3c0c2060700034210300d204072404501c1040d1600e807914810440e003850280090100000c00d01521010022450180d10242281c1011110241285054051400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 812388965 1250 812387715 812387717
    0x616061b05030a0518061317040b09030105090d1710120f050c0105031b03090a020d150c05071a070e09012603070822080105130b100b03010909060e19030f 68
    0x8070245e101c3c107480381d86036005802c0d54024031030721840004003c81e00039484d602c404181c03000e40e2226a54071046015401140c54a446542482c0002d00b01b610006154060380d01199940303060800c28038880e100f11200071b170100070108a020000b090301900c0d003085c0400fa80c800c0e013422104c0d85103814864140340a400416041003000c0051200002480a150940e2955000c21030b03666140c031000f0a207001140b2030b0094020140544906c10f02455680310140c40421440a03c0009401602121284640360000b44100e0b2104174400c8040500700f01c0d190702c40c905050090031044c20f000040e01e5494240d101994103034002e01d0210010350744110b0075640b10250320056013411419035a900311802990740c0d244514040c841c00d04140c40000c41c0e0400101003050080009043c1040008004d4100c0c42c801e0b80e2502196001c00c92140c42208008100c4420070855401c40e428542c5050103804da0100584009840d2486151405010300c4010240307004c0e036034500006070452038064006511820300c90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 812390215 1250 812388965 812388991
    0x90305031f03080901110705150408120703050a08090c120c1003090c121a150f01020c03070302040f1410051206040302150a02072a0b0403020616061b05030a05 70
    0xa52003e007030300d0f1145000d003421109030170a28009460075006074000c0c1d600c0303014401500b00200c1003030003c0003034404140c1a1883d80c0e90003211072441d84034041006000902c10442c81500358030420823144c00c8002c000c00c0c0c80304070031100c00180208180060072890398000100003c2c05160101d15801080742c241414003a8031201d071214180309141e481003412100b425550001000300311507042000c4ea40000c0b00100c0ea0909628442d20341c010b00c0c0e55a40110b9011a001100d903000044d054820700b0010014480c1c00d086900b0702006c1c01c0c4007008500c01e45d8071512040850083c030200385114620034030364001030a00e024104104561f15103149113040e0060003c2c040030a50121b0728120030724181c5035040e12612a02107001c02840740f0710001d008050b00e144041f84103440c50401080d051510142c50320450340f03501e4080000d119902c4025030000c0200140c0240340841001480014040d030070004840808214102c6c004584e18481000508004200001c0030f134076101d843d401c414145145 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 812391465 1250 812390215 812390219
    0xa030606091d06090c1207050301060201060e040203031c0e0d05130f0e130201141b06060411040905041713031401090c03080c070519030203070b130303120906090305031f 75
    0x41c20511101404a5004050304d0000407500304800080380d500c3c840b2542c18a06916043c213005200b03070028002d0f00010750826a0000b4004007681146004a4006002d14074294031407800d06001e00f6074810581a99031203a40c00045080148200940000203840345a981c2ca19841410400490b03500400c20403c40300d074080c0106540560500e5010300c0d03546114150700618001601d243d000c2c02c107828001c000001d105180d0300c0791000f403a0748030030310035003200c40d44d445041c10801a01c00d66030f5a20141c1c042404108500d4600741c2160b90000e003e0300070760340055424032a407140360f0700002c40c5550912940404108101c8124045040c0208001c02040307190019079071075000c1e04203484003034150f500108a00d58100c60a00c0948000c00303004040c0c550a60160128848a000c07034442a4800c4c00382a00028807558a0b10498043d90100c55801c0e21243c1196402d0790040b162000200324942e4071000f1b940044d416114000e56240691590780e180d1620743c1341c1005c4000c018482d012150041c400c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 812392715 1250 812391465 812391509
    0x7170f010605091e07092408070807022a030a050633040c03020c0109120e0904021513090e030409111608030a090f1104061a04120c08030a03060609 65
    0x300d514400d544c000450300360700d442c20111080c003019002025002008507202c1300c00c0400c18070b8080480004d4a138110710b5611240c040e00d511741c0489450780035812001128250540c61818a11441c0c5a2a44a0a280c002d4000700e0300e414411102200c1e654040c0040c05025189040000700c7d60441c9100d050041c00301950415640030203014282c0103d0701c46a400820f0303400f0380c059030343c01d605030300007045000c0160034180c0e40a250010000c000c40ca1903084100704c0d09103110414070854019005507400007070103440c4109540551344407100307a0004031000c00e04d0699130103000381011481009580307030350600c00c0200403901016442024000c080156040000311404201d18040e003102050707840f5a00c4600b040054913040c040207010201c98602c0034100802e130403200381380282c25070307082009544a04000742e5800a40e0a07690f2141c0e000d0104000646008400d10902c0c0d201b1000c0d482c907166910003070352540d003003074094201298a0314401d00c502c43c1d200d090407004210a041c20590301402c1d4103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 812393965 1250 812392715 812392741
    0x10207110d20060d0e0c0f04180f0305090d110307170d0e0307150518030a02241b0a02010f30060e070c05060601081b030402010207170f01060509 64
    0x204030901c00716038442c984420307034420066440c01120a003080c040710b812000c41c10348400307054451501c03400150041484504051142c040010528a585072112540b030300c0f840400500090201c04000042015419545075401003074242da12403520510b080250300109810161a41c00410840500522040301a180091018a0382d1500c0c01d0800a540d000c8010038101070880c0c1242210303d0341103003080c0d056980240100361030805405e031810940c80c00001c040d100c1400d907402a500c0001208403441450840360060f02004d28100900d10f012049224030041103010307254118203401041c141420341d604104240c4000510b0f16007154641506600300c1d903899964589141c915a10a0200c1110113140d80f0000190030082072989181c078191074002c00701744601c00d01302c0301806a64080781c66540140205070150240380340c80000092104406825900020000da045105a42d000640e505954042d800781c640c01c2e0014108144080c552907080d51155130003140100d201c079040181441101f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 812395215 1250 812393965 812393993
    0x1e071514010302040b01090305030a09180c091a0d090602250506180718020406020f16030f111e010e2e05040f0603090b090604150c050c030705010207110d 68
    0x194005805c0701c0203801221552816040100340303200000c0c503420141e07084900681203800e90303c04e00210060a1060710f040c0c0700d0b038007000c4000c542c1c64801404010340c103d80034111500031803110707030801410355080010b031102d0441c255011540025001c0e01c8051000c0c54244812462080031068a401c1c0c2d5540e0380c4001c002d103409106030000c1c0c250405034000340109801030290f010041c0e40354601729280b60083d806407045001620550280c400c1900c80400c400594540140f03071a140913156403581d5001d00c03064582240c0d0540048a01c84283e65042200c42114413500d0000444070001c0d00050301444458013003034802e10954541ca1824031310003290000030b10201030450401c0c070780458159914091508002800380d08904085801685540000c0003a030080320007444075103506e0029a284c81040d07401404c0d6070744c02082c0301c64074000e581080c00703009018600245000b42c502c001a056130000c06084800d65000910702c030920005001003203030824100d4140407200180d55404030780701c00365 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 812396465 1250 812395215 812395219
    0x1b0b0105060903010902060706051012080f130e070f030518030306060c1914060f0702210d020f040807050102030909070c260d0c031a0d06021e071514010302 69
    0xb544007040c1c5080d080b40542a60251003940c03508803914060b0b0207001c044582180d592034007180040c0d00a00e80540554440c1c00c00390a524240031481800f0f0260b124040c00441c4d03528051001035440040301c0040d00c104440c1e070702c2c00b0300140074510040135101c000e804660004065103100ca8401000300c1240d80041d4101c4240703654103581e4150303c5c03d00b0498031010350700350b941c144640180940d0142c454107910941d0180d6090307a0781c01600289504042da54440142d02c02c050a40c0036441c40b00c00c2d00000542c1c2c15481e0b003413860000014060f680704a0401800300d1020404021194082011101801c000d001540c2059003802c041a00c0e0b02c802000c120401401c4070160b401d0005070f502d0a240c80c80d241e00248000802544801d45542c86070402205651a0004103240c083c403034480c0a000998405498140e590172401300441d66406540a4034090b500308110011001c00e200e42b203035080d00c7d024009860f031500f418055407580c00d00f5126003480d41454420540c460f800c82015055a0381 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 812397715 1250 812396465 812396467
    0x50406050a081009060303020f0f0303010608010b1e0a030917090105030708220f020907020a0b070f091502010b011d0f060d09170d1d060414100207080306011b0b010506 74
    0x750000c6000f00703e06507000144042c60071300088240340e40802d0301300c1d40385605030840b00510301403880c00f95207100900c1400d0020f0305a00c018481482d5000050504480d840c040680981c425088140e56900c0381e041c03040400da071442098100004c083d141610f54242134000790810619100192032440000e001b48208080c6400040401032902d81c128508001c1000407500c451103071a213569066003a12050388900804400200d00b00d2002903044101d5600c419259500c1d1119001900c1035890f0050340014003000042c0401c8410540c9044a405100d5900105d554961540050310701c581490b100740580895030402c2249403118003404040340410380d41140d0341d101f0189020020002e01d02d00600400c030000000d11815202c1d07018100c880580c4604100c002c0da0300f007208006440040340140540c01c040e0019010580c0300100007091504c60381560041c201c074400c0c0e60120303440242c0c111412400401400f0b0a5640300c1c0301440d1491060030401070940e81601c0c1d084074240c0511829110b114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 812398965 1250 812397715 812397721
    0x1121070216080d0305090a05120403020108090d14090f1203070314030c03061e09070e040f020c19170307050d0c0e010516030e0a0e04120e1c080403020a170d050406050a08 75
    0x80104140c07c5a590480266284001118019001a4010300c8240e000031106400728480d00804540041002c815496214000b050440c0c12030898110f614215440601807000c1203c82c0c465108190104080c1d0016582d0342599207000f07800d0180d100340300000e18030240100302240e0124411650049008c03504074003a51400340c400e0b00150807100d0344c140c00c07a1055003440300342a000b041081003840b0864044c0461218180500203e0050603028000341d40520213204002e070038000c06411a9000d110140240e5030401e2103c001640f0a480b981d00041d000036406540300243c0c030032562264a545010303103202824030300090250240410b1410726109201c00c100416025481600f00755a001d480803540d40c2e0b5458090405000443d8250b5100c40e503c8400c4c005103204a0310070102c94402070903244604e40c2d42a0100308003030241c404841c0d58804200200150b80c4200e090801440c40310a000000090355505600309045404e42c401801814401071100300d40200545c0c2e109213852030701f10900d030313 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 812400215 1250 812398965 812398981
    0x70c031b0906170d030e10050402121509070f06090302130b09101a0a0c0803130812091c080a15120c260601091121070216080d0305 58
    0x1a0302680003412a500d081c400103501d0903160300b9406100901d5040e600c40030380c02401074007a2050500d280d590354001903c80d210424160380400e800c40e0000d08071803403c00400002e02d140582d05259005c10128480030401c0c04281000404060400c07244c80c52203503072510b074010300070000c9400300031700c41d514102c0d14500c15002680300d1000c0e01e00081000565041810058058196901a410028043d04c40300f00203560054100d985460032540d41c081008069241e04004c0d410107489a60105507420102c40410700c081c001c2e11190518000701095401d090b01e200f0300d05a401c55120020321640da100d046890380002c512544042da040d00811000609042c4442c9a105a00a42c0880700c600c20b501043c0504902c054013940c1417003191480425107020150200614000d40b428281d111000500200419400c0000302201c4800443c0c2402504c100e241d221800426031405100e8950701000060b40e4100140e04005d80340020040c0c2d5142400c1d50146c03140070030248003080c9526400491080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 812401465 1250 812400215 812400263
    0x60f08010b0a060c052b09080601050607061d030a080604060e04020310050a0b060f030f01051c0204020f09120c0103200711010216060f080a0e0a030e060906070803011a070c03 77
    0x2001c0d55070100b40302440d0410301c072585800405a6800a041f918001c141749000041c0b0505030740004002c2410700300c1a5a4a401900241c17010684996184903248200d65040014000e105d9858403640301501d40f030000d00003201d805901044480c4140001d01000d0b880210b1110300184032104049610390381c03170389908060020703490721980100c0b0005080000c001310101031802491918046e00050740d8075410081030255900c101d080404a400101c00185042d038020000707070000d0f414a90134a1521400104070aa65098a202c036070404912180300d0342e8184130380704040c1a60301c00d843c80342980800300d4240e8041d100004114250140013402c071380e8020009076a5000940d05240401901e45030b00414a04c0c8126842010824800100303019900c24014145030025042c01001e0080d00c60300c041b525443c0803140d06402241c10001102c1540b10075000704460b5020348602a0389500d03084800ea0041c90003443c104420000b480030700d0005046881290440e9040350002c2c0700ca5071031010100d84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 812402715 1250 812401465 812401483
    0xc090604030f0605010e010819051f02090405010603020315210f0d030507090e0403080a110d020c06010902070c050105070305250209070311031602010b090a060f08010b0a060c05 78
    0x100a4011400208020380d400c94500210700c540c0c030610241e40c0c0c03051002d44060080c06144207a4116025002c83d040744868003040a41c0203800301e80c25800d00c240c580c00c5400030303101c3c040030498000540300e03507606150141c240146070501e0118a1031070010f2116010301c941c10441881030f0303000f041c2007402640016402c5c40342ca52603015a501c3d051001140b40d51070862015003c04a804c0c40000b81c840307070240d40441e00b11951010100020350310342d40d045580c0c840060445a00c03941e11226001200c0d181c00140500d40590301c40107a4854100f914145000c005a00008059004000070f00000c0d10340c80307540044800a08045490b112149825159409101c1510001800c03646c900350703040303541c5e202c22101c2c03500a0300c02641d951104102201070f16005070320300d00341e8070701040821203507034000198140018440c800040c120305401c000801524080c1c810040721a1502c9060050000031078400c0001e00912008215059510700440c0d100003640c420b81081c051491070340414000c0c1032105406c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 812403965 1250 812402715 812402719
    0x2061f050a1716140103050604150807080c090606040303030209030703080705030304060b0105090f15160b2e150e130c0813030e0d140304090603020310230c09 70
    0x1c0969122100d050550504010b201c4240c070455450b40300203000c445401c03050700c44100c83d1040101120006401800d0050617060f0025590300783c20600da14441201800382a007080a00a204e140160040c46c00c0314941001d4414001c0f28107001c02c070360b100c90880341140e925040241c0c80b48130500001f0709003001580040c205d4580000d05104001300480210710940c450741d41080305900700401142c1074000c0031507444d044001c10681d40c03014034061946010b45250395003003516001071304025a40741c000d00e03242100e0400c054001c0c88810101c41840500d1a40e450188050801c94103603c00e103074203824403c001312000495a03c0050520941e2240780008010b0aa0403c046480090000400c006000580040c05200104010110314803103131240d590955644450b500c0380c00e00f0050410684102141c210901d40b00d015a901d0023400940300412101e02c002900c58510b0042c9410010043c0c02c042c403480c9030064403400014010003078130060006001014582e5200390410b0b140d031048100c000c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 812405215 1250 812403965 812403979
    0x1090e0411030d0c0201030f09030e120319030605040c141206061b0a0231051f0e040b0115090e040203071806090b03210f091c12020c0102061f05 64
    0x80700640d0040310701581301c0d10030ba070308000b1414001c1404044400c0880c0080008550104c0c422407854032080001030740c4d074440c0034ac038030f00100c00780a114281d180d070200801298444038108a5440c00e071140a80c18045400c100040102d071001800c46842418952040c503240007000c9811501c80f14280d403504403104110640c0c1c0c441c4802440e6440d21004001ca100c0d04088403034a4280c070454410840c41911031b80d0000784d40c0541d04000d0040c0c1b038010032250b405030b904440200440c407040c02050003881c5040013031440b4101414890306c5050141c0243d5200a9100500460907030b0100546041391811b5004180740d448034800a03080031210350008458a481109095038040720f03038011000c8840e810001c00c0061040401c0c135403a02d18980d03450764a2090300c2c02ca860300140700001032129120110141e0714081d00c2c003000070104005003068140d8046000c004104004090240e0345001c01c440c0004c102c003a80e8900002d5684000600c581d80b611f413510407180e00340f400c44030300a0242c20014012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 812406465 1250 812405215 812405233
    0xb030a0203150409020a060c0305070803150109080c030a0b150909060718030206030c07151b0f0203032401021219020c0105031b030414010e0f0d0e01090e041103 71
    0x5600a9001540c2002c0400c100c04020006881e1a1145801c801c1c0c1c040c007000d071030a10f045001e03036411000000a400740300081000c0b0380042c0342c0c5002588566003860f40010350301246000101b0820094102e003156074481200c40d14140ea00090040d42503500444500103035503121a11415144035000043e0050f0723141e01848440940401c15030300c618060307921542e0784120603000c080c1f042d00500c00603411a5040011404180602d001055011701903041045002030040540088900c0e6070074011b0b40110140701d10510640c40801c2c0c0f00d45111620041d421802c040248414900c0c0481034400c0c20500040c1e001c459900a0000300610128000b049072100050401c907540700e01c01c034940d0030042c06984440d05056000c0c1c8107590085507010560049862440c4009035581d2001d441500e200301400c806134051503003406040c0c140350b400e10160100c00070844000b031a01c400003079114184000b1103540d9940b642e2101e030b2001210848001e001aa0f115402c044c02c800f94920211501070040c0301d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 812407715 1250 812406465 812406481
    0x10f0302060f0d2a0203040e010e0a061703070c1703090f011803050705030f010908040b07150603061e02160623040308070908122b0f0e0c03150408130b03 68
    0x1318012408080660f074001441c048003241c90f442140182c6d0144070780c903801840314129942e0720070350100544000080750350300c500010b40120322849902c805544006108002c200400c0085d500800350030050031401014036612544901590606601620740b1100400c0079078424081c0030a41600d01070400d0300e87c3c0c0c80c0c0c10200c3c0c0701c6000303000e401c2c041e01c540011007810080502c1408003090300060142e081509101ca6054140d100701401e648440040c500546074820714400d80008511540000828240214110b90001020b42000b041684140031000c2400c2c6241c5140300540c0c4e0011000500c0301000d01c4440844404040c600d2034a007035442004200341e0080950340c0681c3c15515201e403001da413401c0942e9101d0721a501d0520714842031160812000c00c04020a03c2c2c242c003080400d03044441c020f00082111200b03143c6843d070548503042c0245a406c2807101c4004070000344c01811103031801c104141078a06028100030301290000803000f223007049049805001c1c0c01c0ea011750a039241030000e8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 812408965 1250 812407715 812407751
    0x30b09030a030e060603150403050c06152e03020703091a07230a0f150c0e180907050f13050a09022803030503070e120a0c060206010f0302060f0d 64
    0x1c1c4002c03d1a01092020103080000c019209601c02001002000b00019280d201018060801c0b0144003080c080e51007401414415144140d0f43c591007104148841820448103c1f0011040c541500070b44c1210500d62000e051544a4085107007000b40c0d41d4501c0349400c0754071a40581c4000d84440c138540d044006031490400400680f030240a401c01d100100c90040b600e503c00031a03803601c80380d10080b008030000e44203c0e44481b0060145650b007200c591380188000c240c600d42d494160005801510307080c690326120f00d2038264500d5904c0380c5030040c5042d00e820755803114607001d51445112110f50181c515034904084015450f000c03c0b00380103d04040d4600c01c0a09000b06040703200b070480003000001c1d001440027048160400c0e0300d1464806185440030360302d50b80702034003c0c0f041140c07200c10001d10381c503141036600c441503052004169480a03400e0005a804132900a501190825401001101100281c9005698040314403070f41d5548907201b000f03680c2c45503101c100041c0d0706194903007400c83c090324 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 812410071 1106 812408965 812408977
    0x70c03120905060d05060a0b211819050709060303120e0f0a0f06060b03190507030b030109050a0c0806010e0c0c030d06090212010501091d0405211b030304020f010315030b0903 77
    0x2400c01da0401140400980340034012f40d40c048104a000c00421004124145003000800e0542c1c0d8014591000300a003a24850f4594461102c511401c0c03004103410f111a41c11112074088074a850209079000f00d0094030300c0ca28041000894140c00c00450744144016000140900e075011040b00c02081d003d0140410543e41e10040426500d0900c03858141900410040801c442c80d403401c1404501c8a030040d0b07400350003030001045071940306a80c02d500300d0001060b582d01c07914460005895405001c103554802d900b04000040c0000131a0b00405a48050200d00d8032141e8940f00191818522132240c207154843d0718848401505400146981080c4544140e4022242c400395680780701c4a02c10a02d2440600083e01c516400782601030305100318903600186003075142c260009641020034821241c10b0544a910b80700c240702026490b00065540028001c020b4249044040d95a070400303 = true := by decide +kernel

theorem cover : BRFrame.Cov 812230215 812410071 := by
  have h0 := BRFrame.cov_init 812230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 812230215 ≤ n) (h2 : n < 812410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
