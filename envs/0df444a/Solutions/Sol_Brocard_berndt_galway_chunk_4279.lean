-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4279
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:06:18.03929+00:00
-- url     : https://prove2.me/submissions/97fb268b-a56f-43e7-9504-564b37e76277

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 769424460 ≤ n < 769604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 769425710 1250 769424460 769424473
    0x3060509014e0c0503011805061302010806060a020109021206070e0f1011071206090b01271e0905031206040606020a0b100302210f0c0a0e0a0e0d11 65
    0x1e030b616100c1c5140c0c07408240150680780d0038004081003448001c1c0458800c00030003400d141d0f50400700e401c1d50384212078901c8103000100418240081400000d500c04100d840100c0803000b030b6400038000c844040c040d64002d01c00030440484c1c9500075401100b88035001840990300340040101d4a80d031f07410890780c41c0c0001d90340a0052800b070403c140c0705c290310b08c00108000207240c0f814604803a100305180003071030300d44916400041d0b005110407100c90341e030703001711404520b5140ca81400c61502d201039101d00d05c59004003502e0168044400290580d1801000001c00d10b100310081c43e0200f9030642d0961102d2910380302c000400c0204c0003000300000040c50180c4103050f40c440c1c08000450340c8510940b07025800c410f8000000400101e015540f02c20040d8002c010382d0b4580c1c0101d0816000802c82d02d12010b1411910441c10300b0070000c111074540800000c040d80e0182030003007000c0001c9445084050200e900210b81c0c00d0085400c541c4417510706004980c204840c03080c00030100c210341c542048640c0a0310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 769426960 1250 769425710 769425779
    0x130b1603030f090330110409051012140309040c080108010506191a1b0f150112030c0303140702212701050c030c01150b070f060209010306050901 64
    0x50040010b544e4040e29085010031500700091074080e05402003c45040114050720344541507131040307a003150a69400580c640d070070181c002086400c05840c007403a0180341501041100a080f0003000ca49038000c8180b40c180e070180088520b9402040e0600f039010b411b02134102070040d413061000b4100d9034000c2c024046500c400303013840088941c10708680080301a288051083d01c014100f600c0c041c20400601e42c0c90010351051081d18100700e01c40c200c040d608115200c114001c1d0070007840c2e25009860011044135450b00040080c001c0720540c0080501000000304418580a40d000d0510284500007494442c0f4003100029114040940940d20720020841c040e055803040600b500c4e00018042c0d01c2c0348400c1e0b0b03000d00320349840341541986410440100301e964880700090000e041900030000005c9082084980700540704c103165080442d4900062144034089006010b00c00c1c1c840d90440c1005940700c0010004078007800320381d04101c0d04010708600000e0801d0010024280500e51494001d81d4a90310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 769428210 1250 769426960 769426991
    0x2030a0b0901170d05031b040906080c032e022a060a09020906090417191e0807080a063c06021203060120210903030f130b160303 57
    0x10203050f40d8031024031010b10030300410045402014001d01500325602c1500c9114659200d6040190404d40754041007040e0700c410841001e00b482c0c1180540f10a14910f02d43d8500340c181755098031092560900c6004020481d6411500c1200741e680d13110100030502240409041c5036507214443d24030030070700080ca01c5c109500c203050195900a15900c099181c900c20040070100c06002520b400c080b141c8090040c0c005400103242c441960115401041e00707401004d80424420000d2151003800c174405008100e0303004c521568046080c0c10080016201e46442e0001041541c00145d03882602000b82d134035105140d15840200d09103a440d1003140c8007200d91030031083e01d440c0300b848050790210308079403281c600e1480038503803284041c505030075800880d07010b009102850628811050300000140000441454100312114116802e454a020021400320365a84102450107a044e00040b0f40c0182c0c042c1c04203480001800c000404648882407088010490034005204402080c81e240c03001454245 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 769429460 1250 769428210 769428239
    0xc120f02150a051e0d05070c03080c16150b0310020403020910081509030f0d051f0605030109150302100302220f030803090a0204050705030711070e060409080d02030a0b0901 76
    0x5182c0e50f540c04e041013805040200c00440c0b9590742800d000340141c0411980b1807007003901c540030340d42e502c0104480e141006023080703034081d00007403480004110510044040405c1800c980e40e112101c08195104044004020715003840030340e030b160003910215024281603401a105890013111444405e498100d140201902075101d0f05001d40c1100030360903098040341500a1303000c0181307019030303190003d405103d4400354020010030910a5546e018003a2688060400c0c20114014442d0940200d08004006e845804140700f4589a140c851440d10403c0000a418400443d40600142168030301210060041d42006440210300c0130700603080118a95032007080c000f155196041c038541242140c446882d00c0d800241600303521300c1110020b000585447c49020710852165642940305d01745600000c00300440c8407915031640d48400c0051068508840c0c07640e4208200710b800040080d45494220207070f0141810440364144040100b14001d429034000807800e171400c03629846143e80b11010100c0400b03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 769430710 1250 769429460 769429477
    0x161e0207081614060304083016080f09031209010c03050606190507020a17060f090f1b1f02030a03061208070201031a04020d0e0d0215130c120f0215 65
    0x1101035840c4916414035000a41c6c101d4003a180700e5240420307981c034100c0f4260288182d1121300000011001e0b41440c510049500402c3c115001403c54443c800002c0c1000d40140c40d50058070010008035243d41010011221055428a2940361745d01d00350441c3c41c002c04647c486240030906020000e10f03185040300882d110290803030318001008a500c81c080b0780541190004030303000607041c4001b20394504c1a407004000b0751100c00080403280340034000c000d01a80d000e4140d1b992607101190342541c1e96400704046000001003010301c0032411154000600c4098104d40b005110042c3c0c10b0040c0100758040000c10001c8090f0b2070a01c200ca5442407030401d421a00c85c4050401802800003000540c0301c0d8000b910234440c20081c1e500d46144c0400007404076070150b149500ca00766104110311a0700c03400d200160740071503a070000e8081c4030204082c580080400034541d00300c80c1c005981c03c00030001002c046001501440c800c48030000c0c4a450501c50514003184103034450420102c18100031528103080381c0d00744 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 769431960 1250 769430710 769430729
    0x50d2310090b1501091508061306080a0303270201140f03090604030f0206010b030a0b030f190c0b03010602120a1b0c05031c14090d0503160b0907060503161e02070816 73
    0x2407103d51411100107c015100ca0741c0a018a12503141e095a640100e20291200c840a0300082882c0d00c0c0180c100c50380304100c000101001031006005c0c15208016981c5d02d902824041c0c040442860061a10311038810031803540000441802000500018013510a034460f483e0249401c240ca00c1c1a80e441809108094001000b040051440c01040d00001d4020102804a9410b0b07280001410705103010342655418100403107418206200d8040d20102c000d0040300f9036203145505000c402521690003004e80010442d00041203422180719120342c0b088680d40552040d41070001c1e24041c0d4111549115891180c4941480a104413001c620a41d1003407205496001c080420841c072103045401065017294030902d81c2c01100040380007400204134210040c41c0d02045070505281200b00e81f140500041c07020f0340401018069990040c0449410680840c080030504448031000c071002203c221000b2000010b16421000407600000c0c5501610340d6181500e121071001c2051400480c914411110b01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 769433210 1250 769431960 769431989
    0xc080309130e0a0b04030e01030605061201060c1b030c1d06030a020108100b040b07060e060f0601031a1008040501180816050c0a03030905010207050d2310090b150109 73
    0x460840303500c000004910b4a0079540008201c3c1c0b02c954a15404079001e40200b200d80749420610340e40b40c410314000e404111440b40c100560030203110300082c0305002e002c0500001c000303c2c00501050040d0204000041c0c9601ca01702502d134038100001807454454241801d000b4100c85c8100a18025054030948001d0014201c400b802e400440b120f24010b080342c41c04105076031012404515000050018103894090396a07280500d141c80d204803034841640c840c0b41c1d0000780900918a000300d0840da04400c0c2460b000c118203610901c80084c0c4040c0d41c00031175101404481c00002c25030070442c058402d038000e4000300311000c1702100c0b001c046d0034012002480500300b080350080c901000841c405e40b541c0520101d0341080000390101d040358840c0c4d041617000c075489040410482d03a0401c50100901340a440f0159405425560070009400c2d950b0540d04070078540d002203904910800c6850108415120144180d0101e81070601c0d0a020948841c2d02c0c41c6158107102810354010003442c0129041e4880d400f42 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 769434460 1250 769433210 769433239
    0x50c07060c050d020c010e070b040602060c1c0204030f110405061318020a08060f09010b01090315110f1804020f0a120e1f0507090510050a090906120c080309 69
    0x1880158105001d002e02400780320315801040c400b504175101c00400000f03e000c1c0c90807846107010401c1d44480c0040350104814072449a0200e612900014090100e41c0c4079819850610025060300d0340780e4400b2440894000140030144943d03140d514000e04009200031080814482507035401c80f62150050049001030329042140d034010b800e0103841c5020010b2501d401e60014902c50392a520030421503100c070081c0300005400050440e00505041e00800c0111a081c0c00079200c0704803440041c06049124011740e0340d290b0a90014588004407103915552a800589058601e802c43c5568042585619420040c54100352007107502c072021807051941071a04400046600304802c0300c850031281d0301d9542c0c52a02c2181080195542c040e040c40c4161180c61000d02e03541100c4000380f02800b041000e6034100100d131200c401e90103510109107001641e03900740b000141c03035000c2c3d1035000c402d442d80f6100000aa070800c1400c020700f1720340b19243c2c407440a50390b810417603500c0c0a404405030780000301daa0f0a01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 769435710 1250 769434460 769434473
    0xc02070e061c0501050f0106020d0207060912080706140a06050301020f0904180501020c010b011b0c0b030a020f070510060b07200a17070509130b0c0310050d030e030c04050c07 77
    0x16000d000307101d00b03100801080e42e0f81c9094802c140e40e441800c1030060014400150180100d042485244c8028a0441d2400b1001031080300c180c450030252032603080300c00040c490000304a41803d50402410b110840700c0d4402c2d0b24015204441e2103804900c1d1a002003a0761806008a07034001e001c500401d0308020650013000700412004602e00e0020b22495605070000b407083c0080c000b0f49441000000d0b120702c55000140148009041c8270900000e440628000503000002c1c4409941d08419030310307242c0e540c00000c0310080c4100c0f0b1014040d00b20100f05802001000542c0061040c2841720030310040b56a003c0b0303440c1c180618000107101038146415680d2100704038464440c0d00070000c14418034260764401c074410380130315101c40d0040b54111074024400380c00c0c1408105e4002c0c085092401e0040c080380c80c1c074601c105016001445060700040031614208130029800d002e4180206030107038036802ca103006400da5100c0f4245a0181c02140041b2580d071034148107140c810041041220f2511400d5580d42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 769436960 1250 769435710 769435729
    0x2f0a0911040e1513060e0f090a0b0a0e0703150e010e03030a021c061805010e1506090406150c110916080703090803010f0906091503170f1306030c02070e06 68
    0xc000d0f11010a060b000d4a81e51041c003142c0307204040c01e00140d80c80c24100c0e03203040b0301001071100c141b000418050002d01a00007901c10181780e00001d2105594071200c0e41c40c4041c10102c500000c1d5071240c02e0380032003800300301600300b44c0f0760030b0054007048102c51580c1400e00780e8650095507111500181700185439084941c008050b518140400f03c1600c0107101d401000b1181e0030307000710190080c203005202d541204e501c54180034014003207043d074217440e04501003400c400c101d91805000300c1020407050910740b240d40042001c3c124180c522985100c80503001000d9a045100c00d440c034a400030100c07501d6081050445008801c403000b021040c500b815815905400007610100404d03503219812004215800302440c040c1002c001800743319480d00020320103443c2a42c0003400f500c0e20308802c0e80e1003100c8403107941c0100d070352000c02112040000c480105890141c0d1103206107580f0b0000e42d6003c5c0301d419034491000c0c1c421344d84003002a0503910000726950707455402406072280b900c502282d03c0d4680501305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 769438210 1250 769436960 769436971
    0x106030b0414070f0c150c081821180d0f020a1a0f0c0309041505101d0907021e011d0303060904060b0406210c060804050303040b042f0a0911040e 64
    0x101282c0031540b1001c01c1240d031584480720024140070140080307032801185066041c2744600081990845411660008140903403502c2a084000034046a001200c0c5800034404800140381e61011811410080003451500c3e804034450f0b540301c10b0104210103854a8840b10405c00900c440c10550300300300302c84482d400000b4050741da10090014102a54503401346c01354204900441e140003910f00010b10405140f01d40380402802075125002c81800030b108120700100070304803048102900c49210903414451b2501000150300c14103184410030000541001c072843d001030528010240c00c2c005055160f000a8800a40c0300c811800481c003c943c02e42c00c100c06241004000040c019942c0d440840076003040d400c42c210180308580d44c14140051400401c0c001c0102e420844124600365a5154491100410061103020090045000c1c0038010051900740c040c100104407200400e501011020340c00700309110b11030080e142000c5501640d500814032585103010605041604043ca0380700c0c02c1100519 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 769439460 1250 769438210 769438223
    0x4030c061719090c2d151407020a0806070e10080403120906060f0f09050106032a090b0d0e06150d0311030706060f08010f0b130507170106030b0414070f0c 68
    0x221390750345e45a41100218034404000c810a084904262500c40314584c40b6060703000d142a10411400e41010301c00c8614082c0c1d501a5030340304554400584440aa0b4008000e1482032a08106881790054107810f4032000c11110301070228512401151044170885000f800104944800c801c144030315007001e00d44920a601c042101e80e1a01560080c4050940c00702c3c0f040c112070001040800c4c0503124040c0500b405203820b004042c088804508500411a855280740c1c500a5590400c8d620800c410b0300944242c0321115610b140c109402d001809200f0b44481d443d015a0340401c02d6407420075100600c8417005052425100c8580d2019a0700780b5003031605094a00003041284005400d0b4440c81000d40502d0084020150500102c5421118010310042d000c600e0709040d4050780d41c4203260030365030100514003c0744035034540500708d078200c11143d0341404c8690400d0000c10055007640010038071300e1050b201001404002c085012a401c400c0d101000030a0405061200151150303131120420340c0501c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 769440710 1250 769439460 769439483
    0x3060d0f0c180c08090c06120403032a122906090d03090326071101110a080409140618061507030306360b030c03010204030c06171909 59
    0x4911403000e004511035450407507074445200010035040b802c00c90b0000c51704d00051980124503404181c0c1840b81044144c0340068034000101018440c4e046003e820a00c541c2c0c5c0c001c030303400d10003a0280b11002d0b44540404503484000c08850103040f0300c14420020303201130300383e001d02040e110100203400d50711001039000003041081110139101e20b81c282c11494443d90700d0390358252440c02c050341c0c0301405003114005a41c504603c1900600079000340c5502a030001a11a024045040141d4200400c1410304016015084010040c4001ca01c00f400445001c034905021016140009035800742c000c5400aa1104801030707600700241c40307405d8035a44040f0107071201c80591000740c00a11031b03421020080340004e88480040c08120b14056a040068401100e001215450703c5038620a090458203120300c4980e540461040da6a0704000d01d000b0444050700031513032907840741400f10391202a4040e42c0082860850b502c645800c0480c10300e84109170924084191180004280300078004602c0b013690003c1a10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 769441960 1250 769440710 769440719
    0x9030d05090402210108010c0c0305030408130302130e10061d0a02070b04080307120209060d0c020c0a0311030c010504060c060216080c0a110f0d11030f0102040602030d0f0203060d0f0c 81
    0x1e4102c81c03512222800d130021585130040103402d40329521188420080342d44012800a80c000c4c4c05c2d02d03086948441c41c2030b02c0d00191500303205102003039440a58820041d034825070040495034084482d06d42c50070151074407074400e6080b00381907800e0340c825070810300310442c10450241d004009098114180c07070b04c003526103c03094840d85164070301907400b540d02110004c01e100070182c105071030031107a801042085d420300e00034000082081c0a0084131404880d280c00f08030140910a200d4480700800040406030b046d601d03800c0034103065446104142c00b920481502404a60144080c1d4044925a0b9142c1000c0b448680d40d460103034009012240810500300340340c80020320080003814482c450702d0000c00d460481801e0410707500c1c01d905000ea018039020344402090f0345407009151251a0880001500383d15690082403521a501c600b0740f070705510220b0007195490f03010004009094a007203040c0035210004840c3c6c4100d10041e611154401150780c402d60000c1c1c0d500080b00782a5000301780820000d80da0303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 769443210 1250 769441960 769441987
    0xf0f09041401020a020f190305090609011416050c12280507031101030b0d0203071205191a0702010c08010e1f03030203040f0e0f01060309080408072909030d05090402 73
    0x240e0b004c03005038000d50490360420104101c0024070302c081049814500d0b10585025241e0700c15a040f16008550008507801203034010b4140000d1510308007078050313a42d00741c0d002c00199500c03440c0045490703000390011100c0a140070500040740c0340383e04001d048000c240d0310176030700507030f500c20506a404a42040004040343c418020203006600800c01c200444caa1f50000608071764503242428401c07405d100e07009000d6140000d1140540300300d84a03980b038140c50ba082c01840c0288031400c2e0b150304411a882c140400c00101c04c140190310101c000b21403180c48420003a030030b0300c52450003403001800c810010000d10100e142029080804200110901201c072130580103895003540040c1c001d81e00018040188103d0503510f40c0080c1103148101c0a2400d1400c1c0386164001e040c41241c04254540240b002404941c070101e5005064480c04c031028699602546912130600fa8051841052403413081b01660520200320344820344028060b00b403c0b01c1e90407007070f1129048848259000ba500380882032802d0030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 769444460 1250 769443210 769443217
    0x601081903111212010e07020c040c051209030901080c1204110a0503061e0711030d020d0605030316020102010b010507030f180803042411030f030901140403080a0b0f0f0904140102 79
    0xa065020755680703030050013070499040c10b90000e4400b03c966801c104c107140d07002c60400c0c4000e03421140800c0e2500b5804048460307000c1d40c142c90030a002c84030b080c005410000001441103450030380350360041e591001c9002109000d490340d0754414008100008000401240044102d040018065507405032174a000c2446c0c21000c554919071201c1020503000800712000649a01a0243c0740880010080c0030490b0b84901521445402c03450b000b19951a40800355040308000d004003400300c2c0c3d1550040c001900314031a90344416409546000103441840d40f0030070886030295015100d40108083c02001241c808400c550b030900701c0d40300c43c1030102d410002800100300500840c441a181c2840508000b61054030f210440c00620410000c0c208040034044281c40300104004e09850f142c0d83c841902034094020540c100e20390006450400041540000906018811030300040010071445800c2c040d41174103102240d079108044111800c841e00c2d051006d1a8418410300f6501d00c1228401d683e5801da80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 769445710 1250 769444460 769444483
    0x304050309030601051023040830031312030e07090905190b2a0301030f0317010602060613090b1317040e0403031d161502060108190311 60
    0x10000108848189010442c684c0500b0b0119551a03403c0d8980801501c40c00c010068208695680800c0d80c00d588003e10a0b28000c1454000340d840c113050740300c1c807548203901401c603111444044240708490b03800b442e01600e200700100d041c000c411603240e85030203401c0c46002d205a0101a1110044031402405204140007040780030008680000145882c0781010b50207041c101f40100200c6004d00840d0070080260780056151500310312005e00c0858060304132210504030148010000000001c1000211209814034020741c0c0c1c51507401d8401282c465490420701c01c580059014030301080746858043c0e00510100858070f00001c3c050301720340d1002d400e800308a90b041800d900c808504010321240f40f07002c1c10131309441e0301001e1130310341404031103079034034402420140401d40e91340d02100da0070401d456590884100c42d012201074408005002c008040c140c0140204808581d02c240c01c59800005c03a281600c28034005080d0b40c0c480caa03080016981d03600d409800300503003229000d02050701032241c0400c19 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 769446960 1250 769445710 769445713
    0x111605030c070e0405150606190512090102131802040f0f0504051806011a0c1603060b0a030c0b0708090a030b060406050d03120f2405100207030c0308031308030405 72
    0x8400803140716050011039449003068415502c00c00000550218480c4000d08000701003103542d455400c003144550041e5440307407810300d80ca42402444290414040c01c050300021904001b1950307000c0d0418280d01803800032512040128201f070281410500700190b000f100000c0041c1015611104000e412102d0740c0309080100d05810700313026504217401074951044003a42c0d8809819400300e08240c0d00c0f1814030030b021564882503810035281e200d4404952008030030100710f40c204508941e400d0f203400724601c004c4230120f140c034445290307504241c4001b20849030400c07040c4402c2d0389010030b40750247d40308040850350005e041000c80600c0da20051004040e6001d003000d40c100b45440002d20048034000d8000d40e01c2010498000d00c002644021902c1540c1003440b40410300010045042c005801ca6038443c6051041644860310304a9141c00041c0441e1401c4030780b03420b140341da06016a00d45001c1c2c0406070403038014120500108072550000c1d034011020100c040c80c440f01580b5240300f07940041e039044906 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 769448210 1250 769446960 769446967
    0x60d05060405070c050303040f020433080706020d030e010603050d0c060e0c0a030807050c120a03030522080f0f04030b0a0b01020d020c120a02280909080a0311160503 73
    0xc5040ca84191540300d02c403420030310f4000d102500e440390f5a005c000d0000301388109402c00390045485a8020113050352204800c00005211640011710b180034900240007104264440001c00c0715000440c2d2040b10b0294000c3c1c100d140c40d0305001c401402d00356990005544d03d413040000040c0d4104048042c080c21a6190001e80d0154500b12017520301d11004402941d101c0d13110126183c0d00c6164502c1140e91221840785c1e52070030352500c1d600304010100710f541d00c054462111b0110324008500b1249407032081d60b0030007455a4405031030f00a808081c000d40104262101043c00055140000309100050b107403025040c4124a004084e0701d034441d8004584e00f04154090116840c100d00464104030002d001a0045000541c0025521501e194000784900025007101d041d03013034240880610701e42c002d45415600700f114640c0c030b201a42925045288a04084000900280940b1807125034552103030a00b868800e004104402a00f0504501e000461042040f0991b001c0d050311480c690324410806940c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 769449460 1250 769448210 769448221
    0x1c2102070f140306090c0f011d040504032f0c060903120c0c0a0e06010f120b151305100912240606020d02012f120906100f030f1103010b060d05 63
    0x420b100a469903106a201071b100311030654030b901103060412004e180c01322002c030054200c2c1000e0301d1900300d9150814500f00a00c07061651200b03140903404140d0041020308021030594400c0c4010040001c0c00e03d80000803244c503d450800020565203800408880c000d940c090340c0282503038444650a0b00da41d11401d00751119040010802c8002c081000c018509440d04174000381801c140100c400041283d03580f008171000c889a40000c0070100081d0854980d42c014083c03807985640107008a052070001d041001a440c40c1c02c4440c94039000c0c5503561440e00c11320f01030751002410401101101c03801032151002c00101407410000207152035003000820424034104029040101450503507085904004060b00503201803200c0c112452a02c003a4584c400c0c0f24458241c2c0c142c01503100481c1501c3e94001400401a400180180198080c0d10b241c1c1071b20342d941602142000e2203101c01070080310000e0b14080480c5181c09102c0540c90043d00108007100220f00050180d1310201013098030642c1c0f2001d100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 769450710 1250 769449460 769449463
    0x5130e01080d09060f0f1b06020301231e010c02040c05070201080a151403010b0301090803040b010806130602070c05150a081003030e09100b0403111c2102070f1403 72
    0x7842005903041683c038941c10b00e40c000306103006000c00481446500328136460fa551081e01c500e81c658003540d40344420a006890014041c0d4020700c00c1c5aa0000200144404a12003207030b945038840b0000c0c540d8111003400003c9203070b02a103154103036050110704c422030800f503103130382c00b842d8a4644160343d420340e10b41c124030000d440010060301900390585800808030303c02c000c01079020240c0d400c46c207400c3c1865200c400040e0141c050486900c0c1c240d4200740190080052000155001d10f00c90746d4041c80c0caa0301c96603115030700c00e0201c400c103071030b4510380310120046085a8000c0410070700030103400103920748600c042400341c032028000c0c02c550340000078081d481960055640785c0041d42c3d4242000d01900c0e68600a00041c28409028072551060000c0b40c580d40118101c0e078000c000d07a0220b5034a8540e039040c03c0342e40010617003500d8024200c03e50380ca950700f41da20301d403c04040d0b405074156590b103a840c101e00b00a20031840d625825403107805400304601411340080310081c441c00f540c0c0c800002c807940a06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 769451960 1250 769450710 769450723
    0xf0f070206090d05161a0103031b0201080604020f0c120d061d0103030f120504060b0406050102060f0a020a12020f0c070e070203180418030c030e150f090105130e0108 73
    0xa10440d040300781401034021021034440450780252a1141e201e40f1792185043c01038507400303030051042c01c0703003006c441c0311072a00e0980b01c1c1200c1c02611381e10390940304440400640343d400c1800900003044000010740c1450690301400e03034660040111070400030311003000c0d03191422154500078081d0b004160290006c4180c05658050154401c441800d40c00c01c10a20b07103118810301004040c0040000c0c4020820710800d00f003400c00c5108c03507080c801800c0c50b00b0b02100070424001d0303440c01a07061a0020855500028179036000c0d0002400c5404140c0d0744561540003500003442420410000c00314403403802242c0d00240154108100d00203540d44c3c5669009132a14845174040e0b08a0700e00c2c0000c1040180d0003005580e91001034581c40c0503000141c00c0002c0081003000e1990000501d40a0300e601415481110071380650f00c40c4e201c598401161601300b000c01818002c42c218001020881d8500d4198104080c000b1602c0604040741407130f69800c4c1c0b40c21030030a150444119030301803c0040250031010400c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 769453210 1250 769451960 769451971
    0xe0703090c090905030301030b090a0c0f0e010f0602030a14090411220506030a090615091b020c0d141005091005070e0d0f030c12031a03070f060f0302120f0f 69
    0xf080403980507034901c0e86a0105100203416030010000190f011b140074841c04060943c0190b4800c1c0c556200c100b01e141040250140d011081050310000c14a250040c02c81c0040d511650011800d050b480b4800b21028501b44514039020407042c0101821030700c840c09505410095240388940f80c400888107008181d5092030389100008003131404000340d4403901c0031079800510040003c00c2e11712070b50a0040113002c000c244a0715010354010000f4600b02036038030482c3c1c01940d5040000081c1813800341248e80742c3c0d22504d0280d1000c841c400e00400a0750075070610150a0515054403407940342c100500e02124011501080140c0001c00c2d01c1d40c0c0710005108160b8850700c107007058204100060f010130001c0c0b060740740080c40c15022222100a0500030004550380c29030000f1803500d60100a030004000d0000c20a0b0502c428000060640c11850046640000d032500b50312500d110f04c0c03600c0700c200d5440151640d00018141e080100a01e48141d1461081c82022111a50700071800c0c21000280ca07290300070720 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 769454460 1250 769453210 769453229
    0xb180411120f1027050603011a131805010c171009110c010f06061d06030417130f0e341b0b04110102060f0106050706060e0703090c 58
    0x41c800c14414031216664100c40c9000c00400e060740e0b110300d0040c001580380c00900c0d1010002210703241240031300c1c03d800344181070000c040c07055031075440c10b0500741c83c800b00444450010f5101108039034240724000d460140c00c104800b24464804406036141010310100c02d0b5116512001c482e01d00540004010018040b001c1185000e490308040b000402c03080f0740107011259031203004055031005540285c9862848520007008444d214400d900001c000300c4c41481c0204200b0802c00d9100d440c80300c4000540c44c8050802451aa25a500c2134441e80c108182a158106e05001c00b00f20016403803000c00242a9110f00011000d0500b10102039441c0020001c1064001c02008500c0c0a144180c1420b54842c01d600c00a400e011034074070549100403a03403019420700388904203010900c545030443c00e00884c05201411900312840004984483c03003243c0b03001029082000412025101d2001814460300030100020386a44822100310140310560b81c610010751900003c10a100c411100c00c401401c2014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 769455710 1250 769454460 769454467
    0x412110603040314030703060314060406150608010506070f0614040c0b090d02060304020a030804230405010b1602030c120114060603240d06020307021522110a0302100207170d08040b0403090b180411 87
    0x81c004043400c205002e814014100840c01004002c0c0d0034400340354041e4809014070209002004609412504403015907000592100c0001d0000c051001c403240c582000d03041c0c1490a2094082c410781d94005841243c0003e5103020020120307040c900584003500950740e400070b0595204280e159030307001109015106e680390400412031a8011011502403400080c4024404e4285000007030a180b61030b100c843d00444c010140340c14102c4c040d4001c440c02d811300380d1020702a455000910609020445c2c801c40a40030401c1104401c064062031b4101c1610007c0c08100b840489070ba070407041c1d070002d0342d1400c05079010500e003d0140e1307282600298032403000401c010007124484001c042641d00404d01400141000c285000a038540140c1c0c14003841e000342002e4003190001100030341d200403910070b40c0d0241586640c251000140898100f04079125540c641c0c4040c0c03107035140c4102405010300224140420410300040c0e0750741013000f900c2c08034000350b20f01929240500500c0292800c003040e0200e61074041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 769456960 1250 769455710 769455719
    0x1030504020f030d020d020c1e04230c0403150902091b0f0d02032a0a0e0a03080c071e031a07021e0f0706090305030f03060a0902041211060304031403070306031406040615 75
    0x405027107290613000ca4000c54800b024000a03030001c46461b08200a1001604c1045090605403000700100c0344134a081c40c140c01818450b220440300c8041c8025846003140340070032040303040d85d10b0f294118400d80e41468034050b40d003180201540d00070780c03070380115a401104000041d0540e01001005083d19100300d200340c00d031404141c070903210f84a001014840130f01e40c540d0040d240c450b4100301855004503483e40d40c420380c1c20f08a58503091482200c03185c10100d15451050790300da00b080c4040b29441000054041c01041041c89440c0006100d88114410b0042d0455024000b510f0403400c02c00e514003900440c07000c4606e980c00c110258008006021132000d0400c00640000300325450764440300c00c03490301c946a01001807454040e60b8072056500e80041404502c450700c81d240c0e1145144103400300e00c900d2441034148020360004560103800714a11903920307022040d03540c00841e07110429103000140c042c0c40340d4404424250700c07602c00302e40d54810402c1108100e224411915420fa10080108905203003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 769458210 1250 769456960 769456999
    0x2b05160c1b0509011d06010c030e01030b0d0204021303050706031a0405060a050a080f07053c03070e190213030807052b09090203070c0201030504020f030d020d020c 72
    0x5410020040d0581800e001c0820086580400207400300a200012550b500e04901d02060305004214400208400c041084c035800750603150340c03441c2e042c1c8540c40010b403074100650041025840e40c03a00030302d90266190042c0d47d544000c1c00c62507110710901220720305504010707240c40340f2908100705240c5418a4070b81c2220f060341034020004401c030340214196650b000440d003041c000b9800300360030040541000c40c0070b1034045200940e8140d2541111402035a500400c000c0391203140c0070040c082c46403c0c03100e40f11450406905614001d05441e0b4444a86000c04240741c06a5944405a8000703032205000458400c0034807251202c2e050b43c1c095042c200b2500501d05d0b00d0030580300092515038005016010010188014210012040e00123898100c078100c10040288a1325405e4001540022010444600b14030a480c0075940d142d03181d920fa45d00650041d0000c141c050010307640300518400c40011a0303010002107500b4881c95000d4008803c1214002c0d203001325880b000b83c030804000a821808120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 769459460 1250 769458210 769458227
    0x90b0105060406050d0f0b04140a0e15190608120403020901050904080307052104120806040606090b07020301060b0409140108011413060f0c0908100e0304060e0102032b0516 76
    0x242d08000094288044240c0402801032001c0180c1150034079000780201d0184031f082758422081d480040c0580080344d80002c1d01ca1007418044000fa8007110080750b4100a03502c245041814004030001e00356880b0a607440c03500b40049850160303840700007030038411400d102e004240100301c150f400d10103070300f0030b41d443c40483c0c040209004200480803810403007090840040c01c001e02c00307040c20140c0605245c1001d42e10160507402c074101042c8040301203410342c01c0512a210890742290b85a54216040c29140c00303081d800080e0a0340d043d034031114042074004d91100104028074040000094010400d0740082040e04140e0041a207640340c4214220311201c014003603070340b200d444010300b4401c4842c0e10f8080c00410507040d10108142c03502c0440d4101c0e80e0062002d40c1034031400f000b01e0f1540300e00c101400741903c144810a1450360000c2c0010040c040c0240c2d0218500c00050042d01d080035500c1241005a00d010f2071800883c0700340a00c00d040c80325883c41081c0c1c01164840d40e02c2d00f00e050401001e4040d10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 769460710 1250 769459460 769459477
    0x303010b0a05030709170309011407120806060909010e060108091f0c260402030c1207140105121f2c060301020415030e0d0c170a0212030a090b010506040605 69
    0x10301158407070f80c1000301170a002d0b080c500f8015080346c0d844d0b40d030b03811030041079000c6998000451030041e60401178410b115800311243c03c902151700e40485100070003602d01c0341c101400b0f001c244010b80d0340c500e1050290820050a40c0c0d9490031400041c10001e000d0480841500116401c0d1810203d80445094507900321901107083c0700301280c00c6424001c1e07110f040b251502d4140b15084000070070461107000304e00880490f0000c80c0d9410400c03508004804904420b9403100e84100b2a204503010349801e8000141042c3e802d02c44111138018250a0032501c1c00a11000d0328407116010904100700400390030071b400e06941c000042c0002e540c00403c210709003c01010f02100184059800350100e0b000303018280c04d02440b40c5918400a8003074003411041104038014150180e208074411070603212400d400c80b2500f00c5a4080c00c243e40d0040e485142088114060900f008461151007001140038210040300000d0303480755030600317840f0000c040e004070388500c0c07042008200c1d2640c05001d039070040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 769461960 1250 769460710 769460717
    0x2060a0509010c06020a0e0301050f06030703030e0d050601150f05070c06030203060f041a131a010809011b0e190501120f09020d0c0302090f220f0516090e0303010b0a 73
    0x407056540181c0c0c0311401040010511400001d9024200b139101d6449110468154000c0c00746440f41d1b01c4444500d142210b185406a00600c2c041001c24415001d10b014480003400e0f010140c2265140d1600303158090b049a04c00700d4401c00700a0300740d80e00c2a18905080c0d101d1408a0500300a5901d0fa0b4a5031382c14401e40d000c00d900800422800d035111000ca05240034000e0040010340304592108000e00d40d4910424801e0f00031007900d03155200503014000c1040d440003810b9070601d40c610019604000d009d002c414840d0350b03c41031804003840c04038503d030032010b45840d81340c2500f5644c400c00201d402c614022403403120000d034040002e40d030490002d028407540c0c1c0c03201049a04500c0c0b0001c00900b00d008020390b00c101c1400160b0103010401404400740c134026540d41409a40fa8000c088121400380c40e4a41c14410000e007405180a20b240c96206151240c00009094959600c515180c901e10201c0ca042003d0a150304202ca00442d229441d00381113910081c41c110f40c07404031062114041c0145001c01d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 769463210 1250 769461960 769461967
    0x50903070e04031224061103041e0e0c03061e01170a020d0614010906022a0d020603041101090801090803041b1806090609181104020c0f010b03011802060a05 69
    0x300b40c09184921400000848100151500780170811905d10805507200e039910320310140030031010301c40e681110b08a04584020b42ca41890074810088802e8203c020140f0000186004541c5000307600308103001d0003100000d19283e050000c1045a20381e0709113044101c8403120f030074101d03080e6000305540c14a000314501004543e61802e11404c048d00c1071070414101c091404401003003514011a181d0b0350400e003a40c40078505a00e40301e082e42d540c1500c20614041641078491003c500c0c41c540c50300351001d00c0c05001020b2940c1c441e408503019400640d4120760700520742c400c903030071341d644030305c51200401d800002030042508544070003500e4400980094044803000c0004d4005104501c038440040030041c070045011100e450b004da00604250040c520040d061080020310074529014040d005d2085141c0079140011503035400001d0310483c60001c1d04940c083c080fa410710350041c44004140c24480c0000704410212201b0103007142c2440030a4000c0c410460140c5c0c0c05a140d0300d091300c141c40c14a0800c2da5a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 769464460 1250 769463210 769463213
    0x10510031a1b040e1906030b0c03060a030b0403020105071413030f020415031b090606120b0d0b010914060d08031305010902101d1f121d0d020d050903070e04 69
    0x111040040e82c0603041800200022240c0048a0051250104035904401e05c150f030800e09041d2085840041c15a00e040700c003107130284042c0380086808c603400410304012169a691803226460040f036080d00580d41d1a010842050341101003840401c41c140310251402c41041c0c90524a03582d14000138100155441c03464046455550002c4100384036803400b041c1203540d038074102400c510000e46821082c0782c0c0c0f10300050030203d503019480942e44a0740320300015119402e080780040000606495002018640101c040307490b40c486d03213000c3c144055000c26440d11210401e1a00400075005a0168000a04200100b901c032030a40750030442000456000211a0030544e01411140d40003a40c4104044e00784848681c0101c1c0c800d14051030078a80c0c04040403184100030104001085040f130324400c940311000024072410002c0d4042d03072407090003d01004020791060300c5003240740e42d03801c1c580d002c95100711026404001c0c8180d000400c1ca4120318000c2414042910341c046803240f2405a03180101290 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 769465710 1250 769464460 769464481
    0x30c061d060d0c020f15010b030c070c060e030f0304120f050f0321060907200f100212010b0a050d05040204021902010f06150816050f040801060305010510031a 70
    0xd6811000608064651003445041d0000f0b008074079825001d403082180601c60782d500400c4a0420505140e0381d484568a445031808096100610703c80403110100414800100341c60b241e1030240a03140e40c0e51001072120000d151030004005446115070744180030401c0f1400039604440001036004500d1841c2e00070301d10b400c51030103159841aa06a01001c2403440041c0c001c686aa4a440c02450300d4100c40d031548024010f041d00156000c100161049000801c0301c201000b1134503030b900300031003103d000d2b0000212440c1440641c07046082c4071600010b4140362201b4000044c1d02404002c0c0886d131600c11425000f400d5441003800b4000f4054543d00003400750354442e810780d0454150b24910131344909003620300a0003040d049182c071500924102020442a50000b000102c00344180c41c0c0340d003c1c1d00c5200140300c80c031201817408020054100314411114621f00c01510080600b01c00103d132490540c42c0103801e41c0d40c020100209034401080800c0400d11490300410151440c41d6184515180d619020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 769466960 1250 769465710 769465757
    0x150905100b06070b0405030909150619110109050303090601080622031403010b0c0d02010501050102190f0503070507030309050625110613060905090405031e0403021314070207030c06 80
    0x14000108131010401030200c080018840754000f1100b56600d95141c04a101400c2990140350703421103014400c0c60030700c5000e04003070a500e054070f0401c2140d403a031741c0d00002d00752182000c046a42e50004014840c00207003c000190150401101a041c1740ca0300b80c00340303548082070b81400b00030600e40c06c13216001d150140126021130694558616030320740e10346903142000c1d0701c8001030700100d1180d0070401081601c1841010305840d0141e003c2c110040b001c05291b9504041e010301a0340e16641428054001768041000b801842c2c03140b400351907054503500f0090442d2546d540014020b84041016022040603078a107008040180340078503c2c440d015050403140d1803041c503441d035003203200059803509010340d0b1080281100c41c1c3d42d440c0342510391108140480c0c190b05442c0141981d100788803c03103803140c60b0010341c007841044280032744c103055417600040c180c03646d00041c59101c1a6501d1202070120781403000e06a1001c00c0e03000601c0c130b2600d1075540400000b043d100704010000000390350400f200c11442c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 769468210 1250 769466960 769466963
    0x6040b0a02130e090f0105072f0307060b030d080405030a1110090c0510090506040302041125140d09061202070812090d1d061b0109030903150905100b0607 68
    0x110b0140e56201c0846806a04081d6085540c510581c3c900c14086441402154403d010503501d10103501c00d159550815446480403510001004400014024800300090000540254004201a02284145803c0440341030091040180440c2000301251001044502d41001450f05000004140c0e030741c241003120b640c0350019458241907211050020031000c00c07060b500300f00d0302c8021b54041c44000ba502c0001c41c0c442d4580040041c441040540f900d541b04200e60160039132550b00d080c40c60002080481143c0c0c080d40d140d01000d000050510a403507030311fa501e4005140c014214401814405085507006128020400400542c0c10214848a4056900b6658070060494466580303203283c0381628022100d4200e20300c50200d26080d201c0c820016800110245881c40001c0c0c02d0741010f00015a114041d21a10240c100c904130181c0c0c44c00f4401c003c076070340c025590401c1480c194580358000c448080d804480b61420030500c1d201040c030218900104d842c90078400103d080f1800003282031401007500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 769469460 1250 769468210 769468237
    0xa0506040f120c03140d1206140d0204110a0305091002030402030307021306051009030b06061c050403022e0b010503070f0c0507080303180c030109150203060a05030106141f0206040b0a02 82
    0x1010a45d81c8001410040c2c909072601c80c2042c403200c0c0003c15003100d1091003006460710600d4543c031643e00f403d04081100741d002510204e684104455001116030003d03c074400040d94410400c1941c0390140107070303d01a03046440079032030b604058001960300e000b410b0007e40300e07014403600c2c0e030900342d8140d01080c000e00e40640225144404240c016004010900c13040d07990018400000d000d62400300215503103030503490f103e18074400185822100810b4001c104034290712a4402d40c44207805400203081e9a44e00d0b01c82c1c0c0c40d0340042400c14080a60700c910741d2203418883d01b40107005001d50042c225510000e130b145404408102c02c5d0401510b09049076014a1440c000001480410f02044010304000312a47c0c04849500d060081490700321040d280024007101010380d03d02c01d80340040e40095401c00b00080042500d2901c900009003181c1d51580705c0659018079500b41d400d070b41031910984154600c8041400c02d00a00c42c80084e4807450010001040614500002600b8000c1e03541500e844002150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 769470710 1250 769469460 769469483
    0x1080408030612070605120a1b0c0c050d290f131109090d170103080711120d050a0906140301050103271b091b050f090d0b01050a0506040f120c03 64
    0x85c0c0a0142c1c1c1c4550040c0340420207150008803600d441c0d0048024000c01c5442010505086c1141107800116820088808201c6e4010005155507124034803a10a0702031010030000c5d0340c207a006400110070580c415103100c0c00c542e0421818500001300681c4c00002c800c40c0c2c01e5240304910708100e65883c101d07082da900c150500184060144009008020b00c1c11640f26110030140e00d00c01e070017801909120041200d04100218000940c41c600b5982c418017014004080c055203c0c05d8050500c084c003c01e5400207000842c10513070300c030341c0310010700300074403a5040641c11003038a2204002d003407005004081c1455100c000302c00b070b5100004061407201e40303919400c6000756410f01c0e02004084201a2228845e0070140340800c15449502c070700306440007241c100441c91203400c8803d9440390403400c90f20001c0d0344140031100312a203560540d00c5074507210340320700816503060004000d0040801e40001b0f00905041c0030500540342186007031001e6841050344191030b05603a140401c002002500b00802c80c01c10030707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 769471960 1250 769470710 769470719
    0x30b1302040816030f0204020d0908270a240207031a0906071b03080405071a0306120106050604030303181709032a060d0e16081005060108040803061207 67
    0x26405071098034000b0040d122110140d41c03402d0070000150001034030394070402e40c4001c014a407035801070550714440b14000c01c101001d078032001d013503402c800c070101c0c10940e58140c101c08185600b140101d00e000c0440350398400604080c6004030112001700c101c3c607090103413086c0b10402030080120000442e800921840d4009200600c070003e06010b5035040e2644c8a86004500124001c0110040b00f048015076128840003d072812140c903000a0310644450146010108041561315030340051031980c401400c5d0b6a05007003090100c80010003150003507036494a00184402e0b50fa20701203074102d03174041c40c012840b0362540040508845115038000c11001c0c4c1d0720f84040305281c40c00003600c0d02d03023821019115003280044500c210308002818107607107401401151240d0741b0301240607001101c024000040c80d00c60600c0200d242548080b0b0071603e5013000d102c10407c5031010402001c414003424018042030401c007002a0600c6000b40c0000c01d01c4401000289a603124220a040c0401d50581141d001380c0d83c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 769473210 1250 769471960 769471999
    0xf0d09050a0b010b18270a0603051b0102151b071203230109020a0e0907110706020f0d0c060e100c0306050301090f0204090c121217131101030b 63
    0x240311040340e4031002c0c1c0000040502d040c1c8155031800701c03854440d48030615103900b0455408140400081e014007483c1c03030b41c1c25021070108107512541100800158080c1181005071815180c0715001c142103215a8070204283da0214001c1110260b102101c80c0c244c0b107006003040e8918120170503004140700496050f0601004858400359010300e0b480803c00726110400c401c00d0303c10020386907103080b0001e1004205c01d04590340101106045c030b14103007150000e00c0d000154006420b03205440042d07005031191101740c006000d558010f000e14002481041000a811a110105481c00f03405104600c402c24060240079001200c0c007205400541c2d0742c10307103c2c400f04002044240c51250001e880c256010601c0c0c24144500c05881d9000b240e0007950007501e50800015004100e01260b5094800c200014003441803c1d0744a242071194031070500001a881000341b800c8100b640f010a01800c400601944482d50300c26550107507080794906540c00d035000300581c060714405141c0c0e9045404800b6504c0107448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 769474460 1250 769473210 769473223
    0x20a0503070812010905130b150411030402041b081b091305070807020f03030114010306050907081e150d14070806011406070503040b03101d06010801090516050f0d0905 74
    0xb038031091030b50140d803924601412120119040441047c10911034030104144d0b040c81c69200c1d5110081e074407501d503020041415a2144400a0002c24002c014481145082e020795000d2081c01c01c47d10f1080c52407480e00821445000d4001074544502041e00c140000b1890100c5512090161046d40d49082d0700d000c1500500c2c01301c0e04030300003551010109001502c040380305441d158500c4015415a402d03d081c00038000840b004031410b040c0c1c0c801c0d00180503102c0528041c49480c0c0d5403074000061419002500082490b442c0402854075260204544030030b40880d503546100041d40c01e0810b1429078981029041c208074a170002ca4418410001100400062000d040e640c040408002c41c0c0046400e02006008000f802071080d0002d002c14441244140042d652000c4041c0c0d030700c4400c5aa074514440c041c0983c0301d000342540c01e00010040c207940c1100900c0d00400c0200340400641c40d00e440040300c03110038411114200500090751801c004208001d03201c100750b18800c10807020159140c000d03034844 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 769475710 1250 769474460 769474477
    0xb1204020405160c080913090f0b06011803030f020f0f0a1424091f02040e10030305160f0512091003020a20100c0e130204180c020a05030708 62
    0x504000005100c0711640040801c1480d5940b40d4a840000070b95841ca51600003a48858001c1390991380458813080c1c1e805000205070103202710b84c9904002c0e040c60000342d0b000410b002d0510160140b0b070460a0322180d692011a6003500d800e03c003518400400b00e05041090ac1510500d02c940d60760f40310802c40105020480900c5902c00d40c10412003a080d080d00e80300704d18202c0e51fa0170500c4000440c140c030841d40e1194003000340d100f43c1d40b0201d02c01115800101d0342d40081161250301160a000c070300008456507411040162502c81000d246540040483c819130280581c54044140c075041000012550504100c0d40101540c807042e40c10303401507807a80c010420080c81840c031101300901460082c4216000c4c0311342d070354840d001e52031901425500c281c070703080088900b481000c0d2880c80405446c0704424896a1a5544007100d00c2c0c80c0c81003107001d0003225240c00c0b400c1e2041208002c4002c142d0141d040491400d003000c10061440302d03040e0305100341440003500501000440e0810403119030018802c51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 769476960 1250 769475710 769475719
    0xb1b160f080f06061309030c151406040207170a17010806070822020f01051207030605041514040f0b090702030d050f01062f0318030607080c041a040b120402 69
    0x32821280c18a6803000184d03980d54000d8007002101401c0601a0000b6100c1030181c01c043da401015a580c00074100c60088800e0035140d40e81c0207080c0d540216000c0c05c0e03001801120250b04100e0300351100789075400b00149040c0007140000340080a14005c1f9000e8801800c1c941c14400d9640c1d440c140c05486a070300302e98030400140c140300001c42d02694140814a00c4084103450390103450503a083c07004200410903000d05000003404544868001058046e2090400c0c1c0e030049000c9203803105101c281c3e515009000c03019040c48506116409014240e02d4407030804880208a030800b66080b140100b0980b40ba2079000302107071342082200c40d0004001c000c00000d1a0381000030b43d0318910760800304c0500b8021540020142c0184c015880c000d104040d4a18040d10a08072202400300342c5d2790b255a001c030b40e2081000003c1c1107480001c4c502440225400a56418201c0240c60b2541981106100d140201c0400b4a540d440d80c0c01c14180714006e650240121403126640c1c0d00102801074118641240c080744207 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 769478210 1250 769476960 769476973
    0xa0b190303020c040b1f1101020d0c020a020f0321030c13060512010b04030209070305090c0a140306010f06051902150a050415060608061e0303030406020c0d090b1b160f08 75
    0x43d0816080d1031034020b5070010380c101b881c070304140b00b02c8010a4002c441003c0d0f64090050b9421f044e010711407805068040d40091603c401c40e2b1042c8000807421000841c403e0b045102d10440c5400c0d04402c511245546c42c940c29501c0ea61310030821340781c2c0601c440c40c8245059660000c02c045030814014185007840400c81c4411740e0b80e601c101070584c41203010094000315080c0205036550301036040b054101650405456598075058040b0358035102c160700000c000c4940309840b2120f41424440140504020660305440c00e0030326102404078491068100c010000854410041c40d02c02d0141c00c1c60200302841450060805061380000341c034094038160b0310b50040351f060000c070a207503219803c01c9031080d4030350701c1c001d648180c100701c0c41001d00003501c3c0403400200044d644d20381c2d0034401144200e1160f01c005132540101e002c06494003541c1c05001060012203002440b1f8150b02c0b509403001840c0c1c000c8030022104c0315894543c00c01c0c41e502c00340403d2511200d008140b801035980c900e8251150038045901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 769479460 1250 769478210 769478231
    0x3050f09190303050a0920100302180607210302030402010905120606060d090c080a03020106050a030b130c08010c0306060f0906080c03040f0b190b010e03060a0b190303020c04 77
    0x101d403840c0180e540c103402182024074000034000d40007154046003090740050f0040d05900c514a00710380b0000480000007241d07005403410303d00044200c5601d01139103400c5040030300200d000400e0402541d07280b8402d002c00319841041108807590150020401c60800129003c004400b6002c2d42040d5001c84c082001030001040606210b0b0306041100303a91030080000e43c030b40d9020b10540d07900a40a4103402c948542090001c1034203541c1c210f0080002900130942e49002d810000d007142c04542266105002550042021070840c01410b508110140c014000311401454800464041980048201d50a04c800120300c243c251f8800000c5824540b110400000c054404440d403080c54000c280115040f030020541503980440a194068410040c180d0046801c2e103480d00c503181c0446921480c0d106001c55120450218028000c1228003030910780f12451000000948403500100700c10f404a41d9044540700320740c3ca1068101c00342c540c0084206132a6240e085c025161039440108500507400c29404a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 769480710 1250 769479460 769479463
    0xa0c0b0903300d271a04060e030c07091808030a050c3115021207020f210f0a08070b04032015011a1b0723030c0907021e0304080d03050f09 61
    0x88900c5c2d4030207082c1c0e190142c01217800d44074410140c0140c0d40b596482039001e06c1d5400c00c02c002c004008558000300201e0f8a0000694165410008040718030ba014062480000704d040c002e40f500a1008840401c455840b00080c0c0002e020b6040700c03401c51482c21001500c840b85c0520691520140c5009121819172220714010000d0b4509915100503806041140d0842c6085c1001d0840d40d44014076224100900d8030001e00c0c0e4418103070400006408001113000ea00c81c003008400034140c100da02403c042445034441100c3c5015480020b80703032500000004080611503500d52680310952090182000030703d10081d43d551080300303a034514100c0b8020012036400c51414800001c0502900d087e458089000381c6044414001008404280f003600c2010865054050400000201c82038000402c2450b0104040c03600181804142c0030b20145400d0156041d07011070780c1c2480784407480d40080c1c0c0c0d00010040a107548111f41c046402e82c0142080c040100750706400850090b510f03110f075204546c079441c6e4003a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 769481960 1250 769480710 769480781
    0x30105070e091b040e010b03010f080d090e0a090c080609070504060b031635070c020d0b0c07020909011d073807050a0c0b0903300d 58
    0xb0340c04001080081d0070300d0422040c00070010040d40c101400c059588240c0c0e80300e071200380c101042c40c3d9001b1006200f804113140c04900189549001083d402142000203010b0f08120301030a44200b5000340004c174044c145070000103e590f88040311141060340d80302d80f5516508165a4a205800350580020b4a81342030700456058075803424945286031600e100b6080220220a221010b22900120b4401c540ca80350b1012600034130003280a40c902d5905022009840c840140701d00140020070f0180c2025860b40c7c6540c0c1380c140c0c1d00000d403200c2911403030410704807030280c060029030180c460000c0009002041d0403c20290083c5040c0103d091b04074540c090300c030600340c010104030420302014114011102d007a00c1180901070414408000800c0d0034400c640e5010110682c2d955011021000800641c1c080072001841013600c15030401140200003911030600300b2400c9607003100303039840e442040140c9103020700c91060202859500d826450820024152800f00d8901100e03101200300e08104151000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 769483210 1250 769481960 769481987
    0x1e150c12090201090e04050606031005090318060d15050f01050304030507080a0e0d03200d1205040503090a1508010905060a0e0411220e01060e013f0203010507 70
    0x10300c0114062118440000c10a5190036810001d0702000040d840f0050401030740074501980c0686428581401814038041105204280031071a01c0e080085040010041e54083c9428001c2c4042e00300e62100041d60602071030480c1d04155141c4908030710400d202d80e04101c100d4805980b4141e014080a0040d296400100d0300940407034420040400007034010070041c66101054200700c90030740181400720748068803034241100420030b80d44000d40b0400c11a180a4850340c203020042800d503215400c02008110f880b840700c0e94007916076000c981001024010b43c0c9030301101901482d0107680d074a01d041460703481c100d00d20b408182d0402c0045000c51003070040701e114810141c0320864141c0741451342c595040c0700810503210b403181e4403001c62680d0754644016421440405801840d20280440300045134040303024044641c0c500078082014801e114209411200c100c0c010300140d8900f81000c10010f4061034824800c100ba241c800341c003180e15401800741e400d000350001c006694800f0001d4402100701105c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 769484460 1250 769483210 769483217
    0x1030e03070228030503030f040318030320070504111210210302010b120610050108040f030e150d0504030806040b0a09050603012301031106031b070f1e150c 69
    0x2280400040e11520f241c0754000c0d42041080c68030396a4680c1402e40d08142e600350180a054800e000c149548150035041800b14a51078491081ca103590160260084240c0070b144082e2070b40d01803682c40000e00001c401404058800d0051803480501d0098a5100c100c640d904000b2032400304216008a4040c901a035007801e50141990203070030030190b4040b172040c4c0e04604664884000090a444d690110b459502c051001032070642018002d01209100e550080c0e4104000740c0e040101150540c002841500d41500740041021142d40210321020080d800f42e0f110700b480080c0d03010b155039082d8001440f5174000ea544407015110641040159501c0206c40780d031110b0000340038080b0020942c422500850300400010300750f2102c02c0b003003105914524541c55000c500c00e00420903c082c0c0c0c0645c1040500c1221041e265150610200d2100906018520a120307004a0745004000440d0300c03420086811040300b000b03195030640b0720400740e200c0f58001c440d0554100d04102c00b28001c0d0040c40e0030a0020744 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 769485710 1250 769484460 769484479
    0xf1207060b0d02031504021f140c011407050a2c090a150e091506010c030309110904060b03010b0a1d06040902100f1407020a060c060e030c0a0201030e030702 69
    0x300d40304007038522a21103903402502c000521006070740410507544120841215008180b03045e004001141f00039600d140c90074540f002c541001c003030780018501d13480300703000742030b9516603070400406401000300c5e120000c5454860402e00c86102c0d0030002802c05054140e54400080700d00c0c0300104421240901c141c58441d01106034011585080c8041d15800a96240d0008141c440c00300121030140302030307102d20030020000d401c1c0310f06003a091184450500c40e0090150311070400d40c00091030001e5400b009400c16944a200000300406030588140c082402054001d50b802d00d070501500410354a40070b40e200303601e00031184240d810107003200380803a07440340ba215411580d911074900d200f14005080c04e911640d034403460401a0740e03804120650342c0b01e56403032a00d03900f00e00002074505210b010b8141e0780f010b010311010005958841c152001c0d54060714202c1c11714030b198509000584218110020309000218150040f1000041c80f07600c018003d0741e05100c90007850403840d840c0c8c400c60030b01030340001400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 769486960 1250 769485710 769485713
    0x1808030a2301031202010f020a09060206010e0709170708031911211315030605091005030d0c08090307080d18080601050d0218161d011d0604091503050f1207 69
    0xc00b0301ea061904c1d00d000100b00340c000301c08040d081760b000e14031100101750000004e01255038100002409841c181d03411030324a0910550150456865201e8480f080003e0088040011420b1140c40e00074a82c040c00c03aa00d4440078802002e80d2503610300c40c0c00016645030100c0d0152440050114243e820901303c0a40c1440900701c3c17940e207a40a6102409140c024071000a0480f500c0140c400c007448065400040c120b00b00420030021110140c40f0310962407030120b040c400c40c0e4000c1040145045241070540c404840c510704580716004580b48181d060080c00c10008001d0404103615056001030765503a10010f000a0201c02aa59a8010b1320a40d80c01000103010b282002d00c60130840b07034001407012842c440e5030750500310480c4048800f400d00c00c01c2d011080d07151503000070f03005800d401014000e11255a254000038051001552425044140107140d80a070b5158901110040d201c0c1c094140405c2a100030030130400d0080c2d1008544900c12405e15282c1c0e4600411491003400c4050b048604d0030106 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 769488210 1250 769486960 769486973
    0x21b06040b071b0b0c12182e05040f05070b0a020709180b040c05100507030f0c03110106090203160c031e05040b0a020d200c131808030a230103 63
    0x5425400c0192100b8488020100e01d00c442d95604c90180c0e5101700d0707035854401181d20005c8001400c0c4070440702d448403180010000104a1003203442c89002c0140040711028143c0003982c4552010540301d51805061005003c840c0c80c5440d40c1d540100211810f90350b440100031800d2184010f07250060300600c106104e280c28a8015596503036288550720004100d5031a1000708140c00d8808844540f01302c0e03010420b5003041400b2036082401030401e9402d260254502900140d003c401840410194600e01801c060084200d00403651080d0000c01941c0c3c1c440301007400030341c01a2808240401d40c06c1030450001e1007201003040f180d03855901d50728010b40240043c980201440d800d0024808180310100d11031440002612151a166005110300c81c3c5e60740b400380c01e0081200307401a000000c4040d1424150001a01990f082001e4954401e006541d0704000000c00020050384242108221900240202c01000d54041e5403406800c0012071210716514104003040b010000281c0080c00042011500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 769489460 1250 769488210 769488227
    0xf0f06091f080a0b0105031e07120f0911040e03040608040809060307030c0f030c022805030304050105040b01091b05030a180c090c0e060409020702030f10021b06040b07 74
    0x40c0601007244110312180e03041e00301e401c030030a0100011030450411072460b400e40240b050840c020701b407480c03070b600717001e5040d03400102203a411008085050011034003040c46101461030b84540c040d41004642548000b200103010000002d440100303042e100301050346018071829609040581c019403030075181007019074a40c44018030595505e1818445000079031100002180b00d044160b400007080c5410040252204210014000c00c0514042240d00700715000280c0b281100000203441c1c051070b81900003207014040115000300a40004000e000c1003110542085003ea84100e21180c10342e030f00c0d62529001ca40121580305c4101408105400324640140300840d00600d4480000c43c40031004c4000c03602c40e0701800001c803688031114408215411080c401d440d032111207072801c1c0b04001c0444001500e64005c9004814110341d000421004654007000195000b6420f4003da400945072008050025041000b00040d1140e612441d00134051000c941148240c3e8407980110080d01c0c0d0140889a02c207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 769490710 1250 769489460 769489477
    0x70e0c0d090c122f09040b15032505030f0607080403050702190e0a0b0a0b131505030703060b1c050606090628092619050c010801050f0f06 61
    0xb401e540020a56182181c805480e044c06420707680d0500b210101ea401c140c201a03a03242403895900d2072440c410395510b40d0141d070080c1d00320f80f0044075500c0f100c080c1c40c0c0314450b1004c031076403511803160001c603a06100ca40011a8480340c1c6601900e01e80d4400070316848a129091194482d004880040d609600400296130428082c1c54102d00704080c0b80d004c0750352203120341c00002120002d92030410540080d04140c940c042c03c0401c0520120141c00045100004d40380189a140c2c1008504d143c041450903502000624000a40b0f01450b10180c102400303c0d0300c00c0d0f9040000908110004c00c410b41044121a40c0300c4840c3c648495100d81811500002d080c09003e569012030100f00207141c0d5500d66001c0d100441468441c3e803109001749015480b80340200a281c41440a0134030200040030009405ca1113032452250702c5c902260700c0c2c0e80c3e418240301d0200c030300103058854402d11f00d0030f2010001720a60750030001e032201d4807aa40c03900c04120a100d8004140c550084030b42294041a0600001400c0c031071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 769491960 1250 769490710 769490723
    0x6080903090604061106010b0f070308150612090f060408120402010c15020d14040c1703040807060c050d0206240103060801230c04080a1101110708060702070e0c0d09 73
    0x81c5040c002480650150b40144006003d01c02000e884044c144201303401064441850344c0750284202400131a8011040054148901d00d400960f008020307001120301d5100040c5a9681c804c03ea20390301c02000c0e0b00381e803800554070440f44111401c05001a19a01458100c81040e081000c1da0101d0074000704000c000b20b04004088007141c0002c2d1820005080c0c1e1402d07001d025071103c414010510854250f140c00c0c1c100c410300e40e814000407510b2005003006540040000407104c600a03254545140b00365840f88005104a04000031801d41c080b6203103030f400c0d1003581541c803a056015002c9030340c2c000580740b5944e40d5407120816520101c54001c50f88000c074040c1004100180d40b00810b508581d5590210203030884c1c40c458442c1540208852640d00c0319440f020103041604001d10155501e07903420008000201045a108060380031340100341402240318101d844507501e61561a443d060b0680303ca401510440c400030507250540306c005403080c180e407011942085006500b00c4050210154192002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 769493210 1250 769491960 769491967
    0x150909030d06030c050f040b061824090f011701172b110601030308040b15060a02010c0914030c21030c03131a030a0b0307090c030603020906010504030c06080903 71
    0x70400703a0050340d00450048410001980c075000a004281c00c0d0f101e8800c2c030580c900710728105280d440703c1c1900c0c034944103200e800801b5250070021551084400c000d83d400038001184040405080c1401420042020743d400d02120000c84011f503501c2c48021101c20000c40313120010312440500018841e1008210340854000c220030701e01403000006030744500590000110740600315990043c0c00034000b8940840140044d602d1500e0040061101500003402c0c5030074200811801c02048603210540c1c14010714083ea1680d03600c8000e4020105e450f6000040b520460000407c61380b500200f0020107400340c00342501404500130052005900c0c0c403600d0340c046001802182e140c6041000d80300407400400215900d40c0242d01c50039240d2000c1c1e2002c040034043d0098000786202410650741c00c4000441d0101e0b421018100003410038165400080c4110300d403035040c000d1507906801482c220781c002e407140300e0240c403100011103152166010207001175214008c10007086115038906507000d985402540e05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 769494460 1250 769493210 769493227
    0xa14030619020918040506090307080a0e01050d0e0607080a021e0d0e0109050f010f0b0d120905190e011403060c0c0c0a150e0a060914040209270f15090903 68
    0x2444c50510720030052469400c4101700801108010f05600711290600450a1420503640e00c900b1380b0985100100b0440d5401000140d41d00860981c3d00c0e520ba01c0409102003040300402e00c0e502d82007100c80c400040d12081c01314840d03429a100f03c80301f42d00307021698075110301c441c14008442d621458829603244d51740c0c0d40c0c070402c2407003e01c140301005201d000900800700341e4212070350075501000616801e035890705000c2d48c3d143d40c030702c00014505030b80140034400d282082c2c2002d0f29006026400360390070462041281c40d582008a154030150b58406040c0c00c10382e40c84584400152442480d11034059000c3c8000c5610084a04042c08140191000319400c031503164000c5044107155070f0080c86501c8292581021441c3c1201a030704001e407090310b0441402d854540001d026008030b104400070920013042900c000d40340c0b60100c600c0c0400180132004401401038040c268143d4907000b801000303c4007000b16480f0001a800140200005111119850390032420803072100b50191010b41a84010030a0f120b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 769495710 1250 769494460 769494469
    0x27051c050918040b1e01030308040503190f0f0e0906060705160305011e0c140d06050402030c09030c010f140d0204091d01050709030317070225050a140306190209 71
    0xb001d44032960302e0000907051900d48888403803030107010444154010344c3c2c600d52405045840504498062a01c050396890b181000303411032040784451002c0401c585080080341d904080c01d40c0d58802150b481ca09112000c0348121011610305491550102c002c00104800d40707000710280c2203080c003c43c203594a80e08018a80800c4042d660b000f124070740d4441000708101195220b2000e440d04004806011120358070704000c044c00740755901d8090548011034003c416248907030201010700b0000d0000c40da2030808040050868000c0400944644180c14100b03189510802c0780b031480c60100c0d00c41d40c401c01400c2d001ca81154200380c00900741d580e42880001081c0b01caa0050003440800350445e00b0003c244940e945094800c000c24000a20107003040c1000000d45c4030f100080c03850180720022001c0d440c0c4e010102e0a0882a8480c40700c9080008080e2680c55181d0704681b00301d40d000c030346100c00e00b0790750300540c072010320682c0e222a07064106100241c504010b4a20345c40d2641008140103140c00003000000b03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 769496960 1250 769495710 769495729
    0x5060304050c01030b060712200a0507051906050d0f09080a0809060a420b03180a170315090c0d06051504060f02070306020d27051c0509 60
    0x981e0716038000c50111009507010311072211681016228945001c031642c0b100c8200091918109040101c42031504c02283c140ca10301c0aa07205001d401d961036402c0300d0030901c0e91004a405114400c40030300803124581100d02c4400012540540c5032107081c442002c0452004001c50b401200145031603e500000040406004100b55180343d11100c1444c14411a0b01c0e11b0003d00900c00c8650b185040d0440100080140012504c0c5402d4401000910400f503034548612001004e600481e0140750400300f5003c01c808081e5200f462440b55010340490072000b040c2d50782040c2c2d400070b044083c5080140740a00b14500045902c050940980c1800305203800120304006411200d21000c81e001140d0f4144440b500e0003544010841240c00d00d40c10902d8282c003a04c148594800c40f028000050b5419060f64024090a4000c58120b1400c54442c01035188590150202d1110a803144c0810304109000c2556a6099640b06812000404001c1012401d032030900d40190010004d1102c24407010f100c4c0c2c0d8919022 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 769498210 1250 769496960 769496963
    0xc0d030f170a06090e12180f040c020a150516120b0306160207080304050906120a0b0a141e0a050702010612211d0105091f11060a0e1f0605060304 64
    0xa0030034902001282101c0b071030750405c030b8550402c11060391415508400d80f100303014071105031441a042c05000072000e0f52804040340c0c0060412226038800d0740c0100b0a403040f42c0c01a4081050030906c060071408450f0125084103a500d00030801c007170020b1151000010ba1004000001420b26105001030300d030840441d540c0d0050024164100c0540394184100c000070f10340840110306182c1040009030003114024881e5000d402102c0f11280010700070460300c4402508000e0440302400c1c0000c9910240c14a130340203034074040c80c400115140c0d101000001d41c251111544000c10b80c0c54440080002c0e040180004007103640392038002c6514100c1016442d441842984090003501900b14000644200e95000c4c805204143c118803180480c0205071181503642443d0296858501c0f00c0003d07004d22086805040348040c001040444940007500c01c9542c005c110102ca029588103992507050303603031030b406d07422094100c1290f80f8400a83c15108104101c115140810050f40b01e5012514036002101d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 769499460 1250 769498210 769498231
    0x40b07030e01153213060b0412061104050f040b030c060a0203030906010905040309030305031308030c03070305010b16170c011e1803090b07142d0c0d030f17 69
    0x342089164016400c0d50f00d42d00c060300301da80c480e0402c1200610388419011009010f440d0384005c004190a2586c000320141500111042d125038607055a5000c29680400032161940b90100311910038608030f083d2421500000c064451030b07180c6006000c050101c2c014820b41500c1045012529036913444060512407805178019034032450000c075003910b8414181c0c0802101844c000601c00800c0e07118030104140ca400d800d005659450f040820360000d510188007600c203039004000e000350f0302442c000641c000c1d80e09a9003800780f81d880d08210411442034030300701c07054403120090440007e5030342003030107211100940025007404400c506080c00d691164071404030301119409951a90443d61040b484c000100061040c1103440e44c0e503024141c0a600c0c06000050308012035040e08105100c200181d40500d20010358407112a20f9403040380441040c85d038513069009802c03241081103000502016001c0000301481490202a10b042c4d130500b489103125001c0269001c2112050481d21141078042c149036031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 769500710 1250 769499460 769499501
    0xa090f110d0c0801050405010501050a110c0a090b040b03071410140a08070219080708090d02100504140402120115021903170c03091e0106090e0106240503040b07030e01 74
    0x40b004210600c160022440355242ca0014001645d00c002512800c110300c0c10030303c5443c526030301d8091501040c1038070294040c0d101800894403000300d4100c002c1680302918248040f0541c0c40c1010b4641200e4011803480c209400d02c80da0b090310f46020411108036807030a0404c0c90f40d0703480d0300501e155400441c01001060060091141da10750400002d0341c20800080405001030659807000762504c6600000340281d00003048822590352550418005958003c02c2c1d030b40c4100300d01c00050442e8016114080c444044003091a9003410240225810f400844003a280c04e40e00300411a2007c24041001d0f8045201d1140701024030040c070b050b900c8010780240ca844c50302c2a038050941185680041200160640500510500d010300040c3e0344c20814a50081e8100101484511401010756611070505d4608244449000c4041035000809807003801c0c11a5940d107031611031109162038010001c00c00a0010030000340480d0a50702c40740d40020240c60302081400d0219411425118000d280407000200003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 769501960 1250 769500710 769500731
    0x15022a0301092001110a020105031509091608010902031911280b0a0e04050723090406080705090406020906040308071a160c030507021f090311040504020a090f110d 72
    0x20103c1420000c2441c01d1080c04501c032820b40e4580a00300e100a040c00000310201d041480c0c01e01920383d4101c00501040d000e4900010300355904c0c9551410045032001001d0042030544040c015088103e07000b40060040743d507190100c0185801c070303c5042c0d40010440300c980d915076403000144500750042e880d00c864110309000944c4060f06840c0d008250141d42005540902600002000e4560004a0700043e0540d1040d009517010076454150105034420b400d01e950041d018140503100302607044d01c007006081d89503000b180d81d1302c0140c056607511414960000300080e04540042c400798001910311801c1507580d0b55560580d4102ea401100c021800000840c11402000400c6a022566a13861150700d80c0b00c03c800fa10f503501d2401c001c0e0070000c00144490654484410312103401481e41180e079084040c802004204c0c3c1d10703d0200319019090f0f003841000b80d03d070500440d401035400611400820f890f212624000b8881001050314003a19817801e204106040c1c400341010b010b00000216807400c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 769503210 1250 769501960 769502003
    0x8041b0f09150e010b090a0e181b060f0c030403170405180c030112050a1208011a04032f150318010509030f03041a01140a15022a030109 60
    0x256845003a00c1e0071150082191003850b4182e50f04441524a055a5600c0e6030720225504036030582042074203204231020700c02824846100000070100b090141c03040e0728400c18649010443d52082d451744140705010414a00f101072000f40044445030b002c0b280341507560750350f0082660522589541100740418100181e0034941409a480c20051194407200d2420821102c014001070142c403801d00700b000001010401d04001048130503401c05007480d010f0000b07080041840c3c50901805152400c11044100707886180c0c0240e0781640c0e4414001080d052031803004812101107010844012544a1120b85003521180450012014081000c40d07684c41d20841c804c0b03003214031002103052a85414104441040044180d80901205120700d40c0e807a1220f08100740b1070b500049000032103001000000a19a808481103181a070061b15010200d40d0394101804188110041490142e080003103002d01000001c81b0032603a0320842541071001d5081000800d0841d1820300e011600c510014000000e90141c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 769504460 1250 769503210 769503221
    0xc0717070303090618170c041805010605030615040c050d05101703070b01030b04060209100206040209060d02011d030319090512010c0906031e0f0f1b020d08041b0f09 73
    0x41d50501601d080a252041c20742e03140280b107042002c0c0542d0001c0c4203500b06c140105640c2c02001401802240c903528542e0344003108103102115150b2810704001441d04003c54030500c5540004045140032a4140500c0040d1104285460030860104840b6549030f4840c4242801a40341b0820150000d0421500b850b420020707001c8444e030750707000b440030000003038071828460f064a47c000070140441d1103901c1d00c2c0000c0e000d80c09006901120200c07009240550029600d0301c180d008807035880c41910381005010801d40c5000002c0d0004960016034220b00d00d100400b01f51070000035048900c3c0c280c40312203c0c0c490384800c8a41e00c0002d80b02c03820400c010325000e400c0e8400b0400d000000c00140700424800341075119148500c10070300d070300e61003202038410784c807a6800862240b0f0070051010341c40c4000c404009004481100c00528581034019200204e00780700e0b000c02c51181c2e001864401d5007240e0075200f42c00c0040040300d0404c0c05020070300c00e0b1112180e4110040a9000c0c6200d281c07400d03d00f020081d1107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 769505710 1250 769504460 769504469
    0x180603080304140f06100b0f0408070e0415140a020901020c030106080c0108010b180d03021c03061d0609131e08040e0c0c0304050112290f180a020c071707030309 71
    0x3170040003406204140c65451104840e61000443d513a12030301e0521051301d006542c0502c040b4003a4600011f0040583d081480c8a00d12030301c0e000b9510401c07804410105d614450031035140300300140019218642c04d83c0100042c100c14012210800c1c511030001e402e5072030b641c1140d1030f140c2115130201c10039604800800d000d03050782c0f9405410041031000000e030150540c0445881a04125150701c1418024400d005034181c0c004030000784a8008000a000340042c1d201d86004200c1180700f0040c011842845913004510041c4004a241ca5546060140f0300f0f00e82030070f86030b081000440101e01014215503040e8180714204941e04c0e0f0f45405c00c0c12403c91030082049001d414200310340b046607500031040300c00303030346090803d40024480300002c00000d05207817484200860400d620b90076036810814440c0d55400c001c9449158010161050040d0034600bc1c0803041d800748410b0106590103030540191210030780310404c40d8200703540c4400f8802e0140d070710803031030f0700b0398000010034000c1c1740d4411075403800303013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 769506960 1250 769505710 769505713
    0xf130c02010c030504152a020304051003020702180a110c010c080702071d0703241404020a020a1e05030d02090910051c03030b10050c010b1009180603080304140f 71
    0x1031a01c1d0700c0d030b22501d106c1c065001624a035142400e0750141c4a80d10510140d084480c040f18442500e0403000e0b6513135002d402014072865203403001c00340c010f10078000c035030380b0745e03405400718010292281e400315010002074040200d083c0c40d12441003031642c008000e04100050b540006c81d4280f00c039000a0b1101001070907190440d040030f00e050085640c0080000172080f0326281c40e04c00703171740c2d4444124010081d00000c02c0503d4100d4070240243d507040031448040c0c0d0700b0420201b507401d000b0b5040104070300c01e500030702e80940c10a0b0b0600c00440c080403090030401c45032010703040f080d401380c1e42c8080c02c56000e00164007100760302107801941800e041030300300d604c0407140c0700c13074401203050400107141030201c401001e502c443c0c5071142404051003504004583c4c3c0006d0401e9850007000c00700a02241c01001052504c0d61030007012000e5403400035020400950607844001e09281016640b140c240d020840c003992498541c580040010500801103100d00e0003450341e10610038001c040c141c10160f03400c2100146 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 769508210 1250 769506960 769506971
    0x210050f0c07150b0901080d0807030c0e0607111c14010501180b03070e01120605090318130e120705060610050901030b030703020604080f0d050412060b0f130c02010c03 74
    0xd062016088480550f085810110300d5000078048030054000040c00c190040310300000001d01290002d0440803058268488503001d542e0f480c411400ca034151a202c500203900c0b00c20305400c50030000000c1000c140a500160480015500400c09804a070b0580c004030b40390b50119102402505413000e60102401d0b0300a00c1154900a000718203032010a0412500d00d40d40c1100301825034042100e04002d103d0703d004a0700c15a5038801c1d40f02002180c240654180c0d05000020307071075040110071100c8400f070128051000b80d400c441448000b171140d4221703802d51075488465003410082003204241000b10b00044a540e00e5031403514a081c0070b000340c02140144100040c039600c8640010541c2d080540a10380000d01d081c1fa440080e1404500303910194000c01d000801113243d00c0c002c04c01c01503c95000c02201c60503d054007048849214a02ca40e081c00c1a003c50380c800000c5807500212205280100041242030076180090740d03107a5503011368081c0c0c50356180c5080850b50280100e02d0220031a0404105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 769509460 1250 769508210 769508221
    0x3070209160e0a260703023102040b03060a4106180103200306151209010f060501090605030103022b08040302010815060a08250210050f 60
    0x40114040c00e1100c00581202603900348500c1410003051000004050000301643c0d1a2056400d903449560606842c407015000c07a881080081d00c5411250f02070310684548280b101c1908046c0444401c1c10344180032300c2405079007117189001400251000d01d4105950f4140002081207160242d4404000200d05c0004580405081003240510b4140702000f8400701c15140c0e581a01e048490304565407110f03010411070303440101c00624004100e02a00c0802c68804100e401c595070340c9207003015001d001c2c01040025541d0402e408861107400d08589001e0600341802d0840301e08042c100d9100780c0d180e55442c9944010912070048000425081c24445415801d00d0f2000381507200500001e405280004038400807140c0070004898042103000d500d1000c41010300d0b2000e03140d4014881a40080c02c071002280c403010b6000c10411803010010140d42c0740a0a0240c10396404034010201960741d00c68050b82c40c0c10803c0030081d00d03070f90101540074146103039282c200482242e50103460031800800003c01c015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 769510710 1250 769509460 769509469
    0xe010806040c0e0907021606090e1e071119080c011a1302090a09111305150703030b031f02071502030402011b060b04020417010c030c0503070c0c0801061502060108030702 75
    0x72080e00f040d13541c44120754481005910300181c0001c3c0c0e00d104030806000050b02640003140109540319500000d009440b540140c4001075015240c1c610511005004941c007036020b45000a5007200d01000d0364541942c1c0c84100340000180c620079a00e5000c0040d6090f901c01c1c007882407040c10a01c014443c000300d100c140c0414071800c0e0900700f001415a001070400709540e607a80d002c0004081c00703401400344140050001050750081d042400f0b209200740b8001c202494072180c41001c52080b20b1090341080c0003a10101d01a084003100b9507010b00410b42c402001354121b814100304181c03004405a41d03020140781204001c5a0010b1000c5458030600030b02c40181e0b4844114045202040342207012003c183c1080c07002002c0c99041c00307a0181c40050300092450b001c41801101c0d075074a200070010403c581100f641a100a80c4074600000c5003000081e402900600392001481c0c0549000701000d9296081c503821281d8030f0300010f51000c0b505100f4a12507904020803405050204040e500308203c03680401d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 769511960 1250 769510710 769510727
    0x170a121404050601150504080609033a05060d0f140c030111090603071101052a03040c15031e0b030705030312040816021f0912080306040507021c0e010806040c 70
    0x81e280c0f517415480d04a0081d11031000d840c0075150060a5a169040904080da541e41c4009003001c2088104501503024214507034000c00c40c0c0111503100204010703501504001080000c0246a011340080340744030115400c1e11441440e184100707400505104a04415071910021044843c4240e0400300000c8090301070400380e03545001c2c1502c40319181e03244c4500944104400c0140c0d50030542c031304000c1140344130225404038940f01669581c40e010480d1058061080e100446001c3c0c00010f1928040007580968150f543c528051460700090b1100b407121020800144540d10031001d81c0c945040d00d4180c9400d210b43c60062a0490080d4900041d030180c0c501607410041002e00448004284550810001c4c1440800c640c6d00070050395552000f003508105d4143e099201d00f002498500d8040341c040c030194040407110740c000308014119541e03c003c0001038503008100074210301909030003425224030715885d071101300303c0c40d11842104507842d0001001802c00810062069007072825502c4040c0e0011541d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 769513210 1250 769511960 769511969
    0x5061801020a1d240a0807032702121603060c0e0117041b030f0b15030c04020f070b010e0711031614070f080d02061602060f04170a121404050601 64
    0x2400f00c01107000050890808210796450355503013000d0300315406440002040501e6954540407201d40b42c2600407402c9511180701001400d20880050101c45480080c401e034091000f4000c4009074142e00741d41d403d151058560301c1800094076014010840385008100300c0d907440c1d00d0310604c4000a00e0008000c0070300c04540024580132440480c00707003c40d031003040101702c690b034941070301a42e030701d240000e1881c114607400e0320100006804a80ca0082c91428071040c0a0002d00a22022a0080402009500c801c103001c60400081100350300142101c06164020544e41170030742504c2c9000c10010f4801c0c46c2007001c10200e9001081022000f94050740c0440045801941030102071010480c0d50b03107000302a81000c107480600481c0020004000107900d000c040c20381e800d59580d615407030080456502c07200c83c15805600b02c03d001506500030200758680c014060a1840d0b04003203981031010003640f091613030800181445104c01c1c4040b10030f004008800303409440b1814a850203456060f00c45206014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 769514460 1250 769513210 769513247
    0x60504090b010611030f07111206070915120e010905060c040302010c15022809050102030c0319050f120103021c050c0402030601030e03130f06050c0d03020901050d0905061801020a 79
    0x2030304013090303010802e4070300c080307080d034403403941d802450900000401135209918402c00001c40f040711080fa012170100c0c0a4030182d00e4108465042c042c056074151041e0b0704510402c0858860205441d032580941094219403000004900c0c0c3d1034242070303081400081c46044100410001000140d07800a07124083d00c0d00000245420304a05451030068410906000003081c0031540c1415003580360401400701c0a10b588801448a955000580e268003403410180c2e8260403d1000f1035040070302d0000b000042c10189000e62801a22a458a0891700800440301c1e0001e21900144210f0038084010303110340c10220480d10812105590740741d512603500c2d1340300b801940c01002040703e6900907049003050400c001e003540d8546040101d40107990645104011100e00303146000590301e40140101e603e4400c86001070000124040815006580072200060400008110451496103248a1403c0b0b0324821006030030316041035120080301100b000a55200c6074810007200640fa40c01403230400c841005440c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 769515710 1250 769514460 769514477
    0xb07051303031b0b04060605130902060313020f03030c0d090b03090d0f021608060618090604030c0507050409030e0114090a0e040c08010603030f03150e061309060f0e01060504090b0106 81
    0x4003ea000a0b002c0d03080203090040007002d02040140340e4000700d0580303009071141242a080c9041d06000e880c07840c08040e4120400300f0102c2c00b02e0b103005d086282000d0025208032500b4170300c6004a443c5500c5955451581d070000901034020320707403180d00c84000300380702d001880c11402d00d40410b07929081301d803c4800a102e11012651000da009106512100c55101d4414400c113980e1503a25440316000c0720982d1040e1f601c03c0500d0801c0d18031000302400748070b1403002008541ea0310b590540e9203041e00602035826200f10140055160303140e00520051901c40d58404111002020001d0100340011411000e4040b050115442c903484403011312046a0b6015083c01c0c981e00e41d420040d00b4400c8070303000040c1079401c085020080c1900705002d62002a500d60742040b24000000d600100c601e030310700600d4050004200071441c1441d111000c1d000c918016a4001603d0146a941c002100d901d4a0b202e40590345540001d000035000b80705403c004c150a40d81403009034451355450004240c14000c10083c010b082 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 769516960 1250 769515710 769515737
    0x40b101503050a0e10201315020c0d12030507110303160309150905070e0c0d02182d01020106180e0307080d090c0915050f2b0b0705130303 61
    0x1d03080350640104c3c40d8260703410f201000c5040700182420b8280030001400101c108108011007008a550355145c0080c8407880380d042000c0b20310105050508981103120f4200c40c0e101c41c0d40c0302900040d00d240318049010b2400c804020180507204010700402c01d0007200c041072020040048216580071a40200c5038261440800d02540240305001d400341c44100c14250a104500c3d10354494107549000c1c03421140d51543d40c07641443c0140381150070650003641442001c1203050180c010f85020340c6040740b108100c443d20760100744071119205258894100c0460784100200001c4a8400780750000c0c8000e10082c0c1c02c1a0450300e40d046080c44401d5401e991307101c10030890341c05006039050580c1c048042641d410841c61b24034042c1201050690b007102100c0400109240c0521803280d4002518170142680b502d020204808400308402268108035008034034500000302c658003006a590b0f2a80c400c04e61450b03400c1060340c0150040407401408800c001010324640741004403405c89a15151103e10703e28613 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 769518210 1250 769516960 769516981
    0x150b0a120506010c08070803090c0d15020a2703060f1505091003050a060501051c1a150d0606030b07091d06010504030b010b090f040b060d0506040b1206040b10150305 73
    0x1003074045c101c0701000c186442000007000045024035500d070b08940a24040300c003040b0703501c00030400007018814842d485011100440d00a006c18001c40c1c141251100740710700880500207810b42c0c0004c400300c0c03000810b0040003018070995040d01485001008140c041900710116080e182c0100c80c0309a074404000f41c00c81c11452959000340d54488140c1c0c05044403407a001018050a0140e00d02c20386e0b5444000f0074040180341c4000b421600304100301c11110b19030000e2042071001601107400c00c081440048081d80300e0070746440c0780070310604001880a29600701140c04e000007518620401c100d0800411070110b1b200c0d490de80403000a00000385646074500169441c0c8203903400104110070050001481c41521805021100700581d1407800c211980c000b004225038650490a5200106001510b101d80c40c50b0300c07030342c1c0c84400580006605845100041c66020a1310754a0003168814410041040814000720f0b81113000700e0b40400b00142884000c1a8004810540104144c2d5820001b030710141c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 769519460 1250 769518210 769518227
    0xb061606061e08060601020d09030303200c0a050c1837061409010605030a0e030f040f061e0207141c0b01080f1609020702030708060109150b0a12050601 67
    0x15100d801010121100039000b4070b000d901e2107000c840c1c1c000d80d0b00003110f0b0350001c01c80e040f2100503503445000440c11550254001c1003000544410b800401401091800102c4001c221400e43c1c03034001c04e04949c40b440c0030351821400c441e200380110080700740e0400f06803428100e9a00404900190201c5040c501082401340810005030501c0080100d07181d12030301380301e0b40004182c50340d040340b003400c841801c0140510140c0a20070040042c7c01007000840c5928180d0000c00c092400c2829a03281080101943c01c45401c503800000c505c8680700001c000d01c2c0e411101700a41c200320781c40b030009143c0c2d0005000e5241d207803601c03944104c03410740c071081c65060362001d13450310a0701c0c004001c410080e606824441c6d1650024090380c0c1083c0700310540b41c01d01803c00a03004465060000015a044e81440f802802a400c814001c030380622070302e8004564a003013844154045c0102039000540c10007484001e4103407101a501803172003500100b1070f00700096404a500c2c1400c0448003008103090b124000121907450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 769520710 1250 769519460 769519469
    0x1109010c0206070b0f06040c1701032003060f0106020d1103070201080601030e03030f04122a0f2f09040302062a0a120f0501052202040b04080109020103050a0b06160606 74
    0x130042002c1081c24000c075034101317001c1ca2064604020329105804103403040c80720303801c2c1d40346038a04e590010400038940200b404112200c1c194000f04c483d002c5c40c0401c1c600101510000b4111200200500009504202c1d0303200f08030342e80c030f444138642d4031454070151648100040a81005651000036103103034001c1d00410b1003100724034120380d507d103400c00c4184000390007a1822a550403c0e100c038000220300c034070032000051811f0507411408a00b401c40300081800b4402e800c4a0b8848001c01c1100800c080146031202140700314214454002c0b516075181844400203569403080d43e140c4240400b00e540064401c1d40a20712131894810101501c14989104820030000580c8071000254010641e500c0780c04030580c0e006011040c424455281122030a032882409410b40200d48143e4031302c0115060f00d556002d58850f0000103148c40d880c1d1480340083d0b8000e4000c0000e40e0745810f009421075130306214040d842400400104541c00043c0d00107403035446403402c0788030b21064503601c1c102031103219071140c402030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 769521960 1250 769520710 769520723
    0x50a02190510050106081e0a0e01061203020609070e011e090204090609050c07050d14070c06200705090c07080d09031815140d140a0e0705041109010c020607 69
    0x40c9007403074202e54a8900c2030319a0603250506000103000c5002d15a00c50003216220302881030401000042030144400510008445031500d1592620030404c1c4540c0300508900121070030b10541c0340c00d000c1e00d000d41c040c0561800b0f43c1b100808001001200c000281545c0c810401c40c181c107429a405e9110110681c6c204285061002400141c1c405280c2e003d402100d140d014188940ea60312705040f103482c012907c001c0e1a5821000e60081214402c61000d0201017080e96a0b07414490251078040441d440c90b049440400c4502c0302406114092550201c00c02e1098002880d129040c5004199440005040d0326050320000c680386041084100a031080400d440000700001882820020030321806148040303080c0d840842c0220b1f00500320041541000c2c002c0c0c03111100e1580c482c103080c01e50762000c0e10007124540c0d00c42d21210b205511610090107244001c00102e0003050001c03981d03040444c0d81d070100f03120320701d0500810300552a89060741d5214000f420200075104660000c40c4146c842c060000b000f1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 769523210 1250 769521960 769522003
    0x30c05060a0c0908190201181d0a110901020d110f150403030b060f04120c030f060b0102010b240d021c14070305190902011101020a0509090603030a0f050a02 69
    0x30340154014a61079000f0343c0d4101e031903650350b03501580b54400342d2203143c0054800e01c00d09015500032050007840c9031940d524201c1c1300e6960704205006500343c40c11908a01d00a03410700c0705040c001d00035500c0c1031042d1248103203009100710020f51340c1c085000381c580502520074210302ea860020b11011403030324004800d0311003100704a03545444441040f5801c8010903d01185000a41801c005444010310b00d0500d80d441c15050804055a0710b4900d03a003100c4c0091034020200008048078005403a180c8501c00228480003d1070005e42500c0600f003940d40182403084840c40501206d100010310519604e160701d03501c840e80c0840308082e10030109100d0840c014a81c1400d29007070a640080341c0d0101940f850040340d203642c3c0c401c6080e260169a400010000818034140ca08141d5010f141440c0c81410600020060005402d0070381c7c21000300386c000f00d40040b1304a0041d00742000d01691048084010b1481c180b0401405005400c0204820003006004991214071078020482289d01c59900c0783c0300540d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 769524460 1250 769523210 769523221
    0x10e031f18060516080f070e0402040f060c022d01030e0102190504061205010f03110d02030607030207050c060915031305150403020c0d03020706030c030207020d05062409070309030c0506 82
    0xd4803054820800141605280090440c850105c16009142405142d0025211700303108070390604088160a5000703070300304030005004050421402c010032060f1555600d03848e150040040c00416aa089140f00391080d811001600400d88213a00c84442400c0008410204640d441d0090040104c040c05d50001504040f08142e0040050300882e021969407100084079844500241c031401e1142d402000307442c080034400104410a21b1480400280144803400aa600020301c4c1c01c0307090343c00b0f4021030307400600030003448014401e0611048041c0c5c1c1e400c0c5000b050a0114968580c0c030f40010024130700200c04918104a5032000350a86034116084800c0180b005401d589009000c0c4c808a0151003400d0680d50a400c04804080750582c0540140030564030f044829030140c203a000803201051740c0ac101800050342c540c4041902c0c107015074001c001c1480c150190b410710512022580d540344503d511030001995880469951110003880c0100c1e5891079481c09403100d40318030308010901e0044070200308 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 769525710 1250 769524460 769524473
    0x3030503091002190c02120709020a030b010e0a050108041a01150806030115050402030705091201151d0a15030f030309170a080a0b0d080703080103060605010e031f18 73
    0x103001c1c0d080e81e800c2e2141d80902a0425080b0711565001220000a041ca2010f0310790140550117105e60010f49801d00d80801040c0d114201f0300c4540010100a9020400b07442c469414802c0b0040c4050030700380080518030075000a4140354440c840c107410003c11000007030400c01c0311150440b003c02c20030210501941c5030340d911030581501061090008481038005426407078140030718023692aa40c104180c00a003008103000113944001d00003005d20508108881c6591640340700c015040c407003070000003030f54041110300b841600d0030b95100d5034170240d541041900c090030b42d03c1d6040d0403854001c80010300c5214030a030b140816945500c00743c5210480c0e2560740070303d0740641040200b00d02c5891050704420070075400c0e4416025000c842c90000d00e03c40006021001181c1c409625941d008140211b03410003940c81450b140c2c0592400c800003011040100100304050040a0240c8002d017859185480500b010940e624400d0100d82e0f4070610144500d800700b039450707101100c52030400000d40010b4400d030800e0f6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 769526960 1250 769525710 769525717
    0x1923060708130807020d05160308030f010605090a0b07050a06021b0606040501080a03081005031c0f030618020702010c02060c2b020712051204061223011815030305 72
    0x9030045842840010040c0201e40b02c090740701507014850341d007428071540a000b86000c401001304c44500c00c1d0384418117144000b112660045200e0350b501d035a47c2c90600c440b020b40e143d061340600c09101c02403040c241030303646031125042551441d0103c10b032980c040f8281980341c40c1000c0e9014203ea440040c1c0505e00100e02070005083c0b502c01c0003240d0464661005100c22034074240300300d807a190009148400003e00c40caa0164022013004402c0c500d00c0e844100090030f02040403d00702c4070a08005e025100c040d04210501140d100c1820200a07041c50302c603220812142008580c1c2089900080803070440e070013440101c080361303000360a9607102d80e10084c5695407404440729011203900e00300110800c03002c00644188550101d68080d10901d89400181c1200582c5000b007255170380a490172200311583c2e40702c0034100806942da41d03280c0c02d040e144028000c0394071008046400c980356034481502d40c2013100030941166000303c009903211100c044420000c0001442c200064800c00d50008145503000018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 769528210 1250 769526960 769526971
    0x60501030b01110d050c15130203060a060605030601050d021209070503012414010c060203100603050c070c06110f030f0a02150f0a0504020d1e1205040602192306 71
    0x100000079086006440012800100050603400300d100c840d507152080003d021054144001c56042e81d640340c41c0910b80c801d044402a1128034004600004c0d440c00300181a0414000c5e4401c00c603250420303000501c50b1100030242418094000f4001340b00d04d01a40c115020f840c41c110a00006c0c1c141084c0040c0c684032a4403820b4425801d01e481d02240954400c10600314070b00314054080d0143c0b50a40c100c1111a204202354148480c3c08142000310f201400210f20850860f03072000d6203a401d11801038111400505540342207541440034500250b8880c00003400c0d00e60a00300003014a0311803282e2490300504440d00d1b2011f0002040200b00c100c441d4014010764540354080d2a40b00925100d10f0310f005c082111010130071240d0f40c0c003281e6080042d0f03001c1b5070414000b07080404504160b8480125101d1900c440600044595860790280500302e43d03545100c40c25468458070b41031400400035038031000c090755004000c001260b00020855880d241e55004245040c03000c018a9096044685880c1e04546 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 769529460 1250 769528210 769528217
    0x40b0103050f0d0813050106050307030609020306010e0c07031107080d051e0304050a08030903090409050a0b091204030b18010905030a1e121d060c040504180f1b0e0a060501 76
    0x1080422500b000c0741c0000c1c4031030983d94000d420b607100b0a11000c200c24a0714250f030b095607982000300c1d003a10705101d90f1028602900010444e41c0161060500d030810582c081c04401c00c9040c02e1006c0170411000720b5505d01e82501c1c0646c2c00c2c50300d03c204a1b00f0000d840d40715110a1254401280700d1641100c040c06002c40f03a1180c0c1c0410342da17461240322607407008450003003d40e00070020020000384140065a002400001101d08052030100454110340c5820000c0d00c16030305c29074180302085485416503a204a01d2000341c815203805818180c0c4500540c003004004d12200c00c001400000da1303106540d050705034880244000c896509000392241c1c8481000400903c00ea0700b103030001403000351008403880301c50b80e5403034200c613020995074020014000c1032001c5020300b601c4446c90344004c200700ba008141300382c0c07280d95a82c0b80ca000c000407514045001d1054012002c81c0f4404101d41010381404540c11141a1805800241e84800064025008444004814000d0040004260f4086010740d130003a00d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 769530710 1250 769529460 769529473
    0x81902030f0c030309130f0c110c040915110f030c031f0602030301140d02100503010807050406030b01270c02060f06091b0f040302040609020d061706010608070512040b010305 77
    0x2425281c44860b0703000b0054056004000c1041d040c280100101390300c451000e4002140b0f800340c1c0c00170b01515510b03403085d40003e600091041010609001446508808440030084a00c0659626441008140a08441e40e645509015650500104445658984110032a528a002c0521281c113400a988055803d0381e85000c0d0181100c0307002205058407850f400030340c110381c40c1c41c14540000c031000701c8268004044804400068032101c47c1c4225100040d155152658140711599140401650250b4807490800c0001c001280c40d03601114159802d41100e5064405406060002c04060700300b010060ba10344140403107050307804102c16000304650384d13211051351105c508001c80d002e410390b4086400c0c400000c411b510b0380391040003090030760031840400e42070554a03000602240c01a0b840003828030b4000402e80c210300c58505c5850b01034400d602c5840c442007100710340155200b40500911040c0904500843d0425008006542d095040100001da0524191401748017216007803104540a01c200c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 769531960 1250 769530710 769530733
    0x604020c03070b0a0f540510051f030602210f07120b1c031209051617070311041407050d0c090518060d08031f050103020909010909060608190203 64
    0x180c0c22040d00f4040000082490106002d46c120707800c40c44544100700d450210702c0350550540b074100e00400c1c20b006002910403050611404820303030b000100092840303642ca00610a06000f507522040590b034000b1801038641441c5c68958448400306071818040003104010040ca842d108003031180305c0c0d9840c0da103e02e100c0c4004d01d4010103451055035000e07441210260344040345c1c112250050300c0c0c2402441c1080707001e50f050b444c5208480d030441d010f540c150405640800700c807502d0307400c910051901350107641c040038642040680307070109400000c01c0036600300c8080d505036585030032059240400c941e9821550500c164054500e50144000c3c480e418242040842c2c4940aa80131000312603014124600108003a04070591081c0c0c010141e65100e642e1003660700104031840301962090741d4090315502030a202518106041c91503074005ca04143c0100030a1301191640c10b140e40c11104001c1d400f050811091400d034000e00b020382c114a4051041c880014140341c4007005020301036000390b081d0b6001c002e06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 769533210 1250 769531960 769531991
    0x1d0d0302030c070f0627020307050315010b033309070806060912100504050a0308090714060d0905100540030915050a0f02150604020c03070b0a0f 64
    0x1102c070820068818020f14010890003c0d1001300c0502c103103000260706010f840c130303100d003406403041e0405142c07110460301c0704504040120201401d002c4006081d0b05041c51000e10000ca0140620180080c002c03000c548940c0d4a5003440c500405030030440191001806081c1181c580c0d2100d00c0c030300c00e9030008080b900c0b081c09280401e0280c100074105515280303c0740c040c05100000c100f0200340c1446043d000da52410400c1c072036540624031403000340c11a020035081c02801c4200c00380c60b40481d500900340c200071100c0f101d840c0b00c0340f000c001d031106a15030140d4650b02004000c200d402900c01e0040c4026400748001580c0050710802c10840c45900b02e045c00c8405886181312640d080d9aa40b60100b030508000c008000c464074254800c1c940003110b1621583c200001a00c5181c08601240010a00d4202950828081c07800c0c030400b4030090990f040d090720440308110003c0e00c0c00340155800205040d901d2130030700450b21a580c110400d4049410b100c92004010220010710440302e929094440115021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 769534460 1250 769533210 769533217
    0x14010905100e0c04090f02040510021204091a06031f0b0a050706090c080a0606060f0309031d060d1805010e0106030b04060b0a03140303100f05131e1d0d0302 69
    0x190701968400c01d0801d2446011081e000c1d1008000e180240700000b403102060007100401054841e0150300c80d8680303170a12096000d501c0c114070a5400c101c0c1c4613008501890290380c1221800c25002c2030700800d00380e40302441d4500d1200b20740c119200000304001214620710180c3c2100c00450801c0d0180d41e903203040d1885008100c04080010010090580465116000b40c8a002e001e035140c2e500d059038445d4101d00c1c040c06003500300c03100c80e01c440b0704001c0782c2d4004041c802c891030369050a001c08029558028080c689920100b50510549810721660f922064240ca920200c140020454200d01c040030070710741e1011036402c80e915800d182c136002c6103031818001c55084a82c0018400d58949607030392007402a0001521054210b04807203000004145440300851000109a000e1603590074400315906a250080c0c0019403074140d032031405c03c81c83d2611b0b8905071146c0c03403500000808820f907402074640a0304a0a681c0145070602c05c1c440c800032980700b1f5403683d0500c8481207034080c4600700780540a901 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 769535710 1250 769534460 769534471
    0x150309120415080c1926040b0406020c160f0e0903040311060c010e010c0905011106090d1218052518091a0403050408070e012616080114010905 63
    0x4100915280d10b89006001e15030300105207070002818801d00c004440b11080807180407030000f03101880070a00a685194202e4009480038080381410314098944881403000600010200c40d0300040703980301e6500c1400358050343d22015240d0459240e031030380307207183c02e907a14050013404600c0000030650b54400001140d04480d0b029151500740b050a101b00301445d080011880510b5490b00003c405200b02032040d4840442c1e142c54030075030941000001407558001406000040d8407203428804540320000c1c0c2c820101540749401d180e409580000a80a0901c580c0c001c6a00c1480761440c208010380480c44600c001c1c0203017200310750940501461001c0b000c3c42d00c00c4843c0481c845080c50050070f40c030b8016584141c040c1460890780b10380d5480d002c03d4030404650aa0004002040c1804030350824020180100300103103001580d94145140c075448014204d804580d20140607080d00041d400c20b000101401842d60fa21044441d03880703a503c0e010706400381e88440140710741000031a00c81035034400c6c0703400788 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 769536960 1250 769535710 769535729
    0x40b06010e13060603020a0e0105092d22050c070b0f071403190b04020f040e091203161701080d080c0f131409010b070803151503091204 60
    0x16214600192000070741091800d40000c0c0b4158400003800d80c500600c00100304580e00165203d00e03030b010040042911010441c1000304c200309100352a9540a0310180c10070207010050324500c04404445641d08001036800c6d000620041112201041401214141c0c200c01c141032010303941c0e9001c0d540d0b4074400c00000034030402c1a00302003000300000c1d001d0261702c04500c2c1042040c64130326040c20f644035001114001043d45c00c0d426540304002141c007442803036810a407812350514003032040d6080745024900480e5001c4690100043d00c40008010f560440000100348540c5c0e0f08000d03002c1d400400401002801181c005844107820841174a40e00d030481c3c00e19405041c08410700d1404680706800a04504072000c018404561200304103c020203526104982100d140391070700300d0303203610846c421042910840522004010320110b030002c460309a03500001c415a81da44411205100384401c03c4402d821000e0b21000300d449009840045000d440940215080c9034a00341c5592110b104500070401403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 769538210 1250 769536960 769536983
    0x8030103030f0c0f0b040311160b13090c1206080d09060f090807080a1a2208071707150e0d110c1503040b01060503042006070b0a0615020604 62
    0x1c240320320035034004086240760256512845840380c10f6800c4150400b640c48038800028030080542020b0490302804540c00589500d0003a500507101503401803041e8250141d001400e86003500c20f19102e8000f40035051010040c1e207855201c0182403544c0141803500091425102142710080081c5c43d41c0b5246040d0703109602d00341080713000c40b01050414503a9090060f007540101d02084140300400c003601900c0c009001e10344003800c1c80c400c0c00f03600302ca10701e1500c40c00400340b010101e51102c801c40c1d00c21003101c030302c00641400d103024081442884009400d9107056000f501c00b91005400401520b40510490503000f4580148a0211114020503001c3c580c0500583e20007240a6100381c445a402c2c00203407000c5902440c04110148039070400e1602c1800008104010006240c2c4100e001d000245040380c2545020340c4c8182580311100b4056842100100e59121680d4540c011102d0740c9034401ca13440d00d80c1c18005240ca025003894043d0403070b00340f8519407110344079200191052155800c545035964 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 769539460 1250 769538210 769538213
    0x5010501081b070314091302030703150e0609070c1a1b0c0a02190302042421030822210c02010903020d020103020c0f030309010c0926030903160509010e0408030103 72
    0x4140204003103ca50005c02400b22a026942e8124000303011728000f0b81c090f9482c9040c5800904948081e0015084c40e0807085d814042d4006030003007070382d0100c401e4500124a49840340144c901407004030004018020840507541540d00c2d1080041c00355014581101980c90240d00f16402c038015112045155881403042e000545040c1d0900450180301010300149151241c02040684224200000116007210550420842c2d10304c5610300420a540d2626040040640403015000003000083c2c00c1000b00300110302e10502c1c0e141c3c564400380c070b000e90a04000c4c03110b14200f58283d440303c0c01e503d00102180d16016006001e5641c0b40b181f0b5174165106441d1a05583c01c01004008402c070581c10103500f8000000503403001c000e0800c0d40b00441c0c00a544030714001c19000c3c00d4440c000c1d030071000c00a180f03900b0050408590320801c414400040074092145001c4146455401858241c2d9854403c1e0510109034101c540011070641c0c070b00b5a18810240c0c1c80340034640c5100c805950013442c04004000400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 769540710 1250 769539460 769539467
    0x60206070819020c0c090108065a0f0105030d030f020f0a111b0f1c1b080f07030c0303080703020d09140f0a021318080403030305010501081b0703 64
    0x81d4403591420100c41c0da80c481044000c100d81113000300d0240d60f80100c1d1a10041c3c6009982180100001c0c03000304064503000c0400051040d0f100780894081ca50149100040d01302050f01050022401c50b09a80b201c0c000a01e5810f0110124051101d00d035280b0040b5400e1014551900e0503070f44003400a000c00b112400044008005280050b840d8690a000c503480f82c10001004004446569541000800d01c0503001c3d1f0400000d0300c0c100c1c0c2e42c01c0ca82810170a0b9629100801000103d080320340140c02550003801d603c4103004248000c041d400c02e01c0c003030904080c4a000c4030083d12103d40072120000441c0d03019650b1a40a804007401c0b524140c00b0401c0001d204041160b80140c1502d4007509240c0c03003001c241c0590707911030300807214440b1585d44020001020040c81403003444200c01043e04800c1a00480c2c00005020070840c055501d0315002c1c0703005207902d03840ea031910f9800402030356625901e08004000306028010780b80050101c502186a0707100e14001002460f680c2c40c1c20a02d0004544d4064 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 769541960 1250 769540710 769540727
    0x60806130312020c060106141303032001090501051905040f06150b0309280b18031605060901050906041203020315030f010501030c0603060e0114041e200406020607 72
    0x1142046842d0740d0300d901c1c40c0c000d070024001003482400205690350610034064484c8180a007582c0c4240000d125024220520300013003012660581040d14010034031054244440541c459102e55640c02c04c40040c2c1080b005511191180703502c901c160000741c5c4041c80c0c05003520f8090710b000d850020b2003c0d4081c0410556803240911010010030100b0050741d130180c14855400484461541d03801801c03a45080d500c06805003c161000c10481c032005d461070780d8501080c2c0306c016011646128000221401c207010400031122002d01580006050040604d443c0750b6500003207038001a00d500340004038051400000344c280c041c4e540002e136641280e415410880c02508003c0469004c600c1031202040f15032400c2c80403900070900f400020030349604500701091004441d0303002c902054504030040100c24aa420f00c941911508402002400e1101d030000d00544200b160f0180d01c0d00003070140c3c10501540360b01ca4a1a02080c000c10b500940140301046000c0c041c0b80308038030158110f81d0000d101948070fa4440c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 769543210 1250 769541960 769541963
    0xb010f03050c040515100f0207090b1c0c1d04050d0f1d0307031a0f0f0613020702030c06131401030b010e1909060b040e0117030a050a05120c07110406080613 69
    0x400d5071805050b000560301c1c201e01b07220402080d80c81c206404043d6041c0039100c09060358120601c0140300700c00200d02c4040300c50780b184843c8402d402650040094444c4940300403d01011208401c81c60740308854002c4906460884052103009264520300b400f5401401d180d4050b6240c081100c0c040700034400300307800b81c000800d030700d40034030880031000528135840e81d420016130481c0d01d03200e0702d0602e2801187c101c01400020009140c3c004000503641c0f96410b05800742c40601000d41c440c6030034030100e490041b19400003036011f480820f500181e4130030008218121804105801c21401d20740c401035080f01c0e659442c1c07a00003002c00d1854042803c213042207905042070003084200086d5a03090701421500301e034102c08641342c0001010880baa44c920421805002c140013007c6050300721101c0203550313104008030b00c400e11030003065844c03100780554280c91408401c1e0141d04c11a1a01c0e001c01283e541c82154110350704a8185054800340c01c00f40b0511065070f4100c2c008291684407404012581d2011450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 769544460 1250 769543210 769543231
    0x150b0c07030b070f0f170a090c05040f020901080f06090c0a021507050406180f06080c04030f0b1e0405120904020c160e06030f030405040f0204050d0f0b010f03050c0405 74
    0x100040001c0d20810514800c1c00d0740d40c4c03000303801c2100d42002880408171001ca1020401e010300d405a8813251030900540000a654000900005615050703004000395406668000c2c035204408072941501d07002400180000d80c1c030210340383e540d6182410086000e890f4550085209400641a0218031000f41140c568a00450f81199401d5101c1060080f04407030b5013000a0000c9802c00c40b00340c000c219200c0030105902d070814101d052801c07034144143d1030b2046004001c000d0010403045c40c9103508440146803c240f8602002d00e180c1000505174109943c0401c019500c80a5a282107061040d200d0040f41d124018080c0c1d074a90300098511604901a02ca600031782c20408130001040810018090180c0714400e450395901e0504080f121050091600c0e0280d0410700c6203102c0d0400200449050328021507000543e110000c07480b070001d02564206036040324141111109001612200c074640c1071082d41190000da8a58415a059100a11000304258070a5a892080d49000d400095102900302e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 769545710 1250 769544460 769544473
    0xf070815040e060a150b1e070201030603050a06150b0723010605040905011a030102131a040e0702160506040b0405130207081c0c1704030c06151806050301150b0c 71
    0x10030703080c2030850544d0424241540e4807182a0380c400032520b500020700048000c1810a00064448520590410301010094000103200c030110fa0107a84074034051504401100d4044482e454400024100300409100741c4006480000c0e800d840032040320301084c1d01030481030031081a02101001034950b810141c01554903081c3c0480c0c9070721244a0b22042d540260b00205030346620720080740188101c1080d86004c0d074010800160580461290301003282e6102842c0340c00d03c200d186001c0708a00840d040002c00c59016010b1004481d4009001e0003802000030b07400e104150f8030001c10805100d180700b81810310381c0034402040310b0728004c0750107515822140405858546950355a000691003482202c03070440072031020b003403d08810b201309020805242081c10081080c1480d040c500d50006000a00700829150200100f00c603640103100c064481c0100c0e0044503071212083d18440020800251560303180c400300069a240500400b0040d5099440c4121305a0400880d20441d40c8404503086240c410071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 769546960 1250 769545710 769545731
    0x90e0a0b13090b060a05010905060c0a12050304050118150b0a03020301060602060f07080108190809040c0f0e0901301a01051c0507090b04140408120f07081504 70
    0x101c00c1100c18411100020301e407140c0c0c0380c01040b030180504100d014400858080c892a60400600704c2030b1542200c406440300744500c0340340e2038414160001041005c0480c803104129070000007443c00307070344150024030070107140c120002150580000083c0c2412070606440354181042c0d88246150a8007400802041e5101d07004a800c0d07842d198083d500582c17000c0200030b40d4034504034000e1f40000a034035113082c06514017002031341d580310320b00040130364241c0c10510f0a003004490f9046500240001c0e0060140181030074018140080141c1240082554000c000d060340c03900c28842c0c0d05a50412440403114580030740c0e4008000c0d5100080800b80d0300104100000c2200701c60a242081d503410640851503041006006007400540c074400d5001800100c0b540001e48007040c0c4da015a0100c000002da0050740c0000580070381960141320742895051000d000c103100c18540100303c1c610b684420305a194841000c0e003100c540c4102c40e8040040c15640200d0702c43d000140c54034421100c000c00100300040714 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 769548210 1250 769546960 769546969
    0x20313050601180b090c070201050a05211510020318010e030609070515041d15060c0f1c02210f030906090f060921070804030f050f0607090e0a0b 64
    0x20b030000d000d0030b02c1c0c011200b03e105200780202d44060809a4009403d400c14402840d000d000f071100082c14030501260f00e0b0760702c0e40b0800039200d054140d4400c2006a880089154403580011f41d41ca800d903018800e016011800c1c40d00825100103e103070b00840c03904209408078032074552901001270421415495105040d5010080c0c42d00412504001d80350b040d144ca42008615070a410340020062028001005102e504031a6000b5881c0360300681c450b0356450b01102e102401c003080c401035001030302003002040a8030004124180c8044034080780d50600303544218400440c012103c410050744102140c0c4503100c07013200008158100c0c1801d00381002e8003200f82d50781d039410480d0711a425030310500411506080821401480640b140040c04560402d6080e098542200440f50301c0c0741844900b000c10002c0e1540100c44585070802c0700c8035155038480c608152011140a0181c0f5a4403801d00305051035280407860302d0003a42039442e1074446c6417400c0107010700441b0041100d030280703540d4010800c2c0c90302c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 769549460 1250 769548210 769548223
    0x121115120711070e0c031009180b13080f0f0c01020703030b03150c160f050d020c010908031602040b0409020301050114010306090506060a0c0507030f0f1205030f040602031305 77
    0x119003a829105280120000b0000c0e85640007401d2164080141004032000300c10803da0080101030000c3c0c1d580c1e0307903846540b03000c4440368001500c60f49070080640240c17120440102c441131003104039200c035803544800c0c508540145076000d480404200101d612144018000b0002070400b205224108500e403112942260041c1905401080c0c448905400c2031505110b2080341040c01c40c0301d803002c0e0400011450941c019800891a8030012510100a014800c900e00b82c110380d005044418203045688000d40300e0004200c8140894810200030800000c0441900e00060030411a89104042a0200006442a203041350f4009683d03008410168400b80a140d004e040035049220303684144000040896a07107038045607161749444180011a03035020110f800c404650320b082c0011b615507007807040c1000d0003a440144000100a0090100300700c5447d611207150140c607041e8040b503916001540e60703100460b01403445403102400900082c1c0c0741e5020f150808418804070944441a696040ca03004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 769550710 1250 769549460 769549477
    0xb010e0a05060c210a030501080313091a030f1006050612070507030c0203010f050711071a0a110f06040302010b06030702030901110c0d2102010b060f071a0114031006121115 76
    0x440022000c03032951b0540229401020781c0d0005501d0310f484407034003c082030a00d004154103030f42c03240d0f04401402003410703030410110302c0201980e0501c408401100d960341e036040e000c100803901305000080c1b186403090507038540c0e0044581454640d80c40c80b02c11a015400410102c00b8000c0001c4080d0160302e0901c2015940e90300c92000040e80c0c00c084501500410307102c0701c41d41b102d500c071050900c400e080c42e41d0138814006c0d140084684918803c1816100c03a040380e8a804018071a4040d0003100c01800102c29001e60f0280d0001c0040d45000028412079100441d801c4015a10030008241d0f90351240344143ca40150310001c4d65415440c01f0001142ca1340b00006c00c2c0d6850310f418141c0340c6c01c0c501c043e14490304500c460008100b02181400810303024015000f90b41c0740c4500200e00c100c20301c0200c1e040d0460240400030b2621440d030311043e0740c2c011480f5643c881d901030b1003000b1003440103d00134400e40c025652411190701c000c1c0050340d42c40c6c0140709080c0d0903940021103402d800140d146040301811614 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 769551960 1250 769550710 769550773
    0x8072f0c010305010f21020310022107090b1b07050603090120181905041b030c0e09010b0705030f0703050403050f01051e04030e030607030c030b010e0a05060c 70
    0xc20410001000c1d80c8060b00500200821610100840560307030402c51451106004212081c01e500e00029040500b100f000084060000640c8a0035100660b01ca510510300b140181969448449044800215500800b81c41d100b0801001c50403480d211800e24100c08114100e07101e4544800120b4141d800641e140c0480d030303464041c185024400d2010b102a44000141138600380900f4004055007648540c06031406070280902c10103c0d03040e5403c450000e00b40280007489202040500800441d540801c8400045c0c034020300e490389907201d030001c0e20459100400408990b420030500d5001c640c0103481c01c03246840f00b080490b007030340c606501501040307000307483d12a110303403170742c24035a061141d4100c806081e40d00d010100590841130a1604040007100a0b02140726500c42c9019229501e40d0340a1a9041c40341100304904183d040e00500a4080e541da07041c800b100050b001511aa02017180c41544070380c900704288040e08002010f000c1e6951001d04440b0354a01c03003d031003d65400c42004081c00e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 769553210 1250 769551960 769551973
    0x190c050c0d03140604051f0806060f030d0801031407030b1305010606051309051e190608011529040b07060c05030c180f1002070f1508072f 61
    0x405080c02540304480d41c42c241800020f090700d00842e40700c00001c080511079681e400100e2100c15080c1c156801e04148440200381c174035101e4980710754851084516030f1140c00d0f040084202130401007400e0b003038842161620302c41c40e4210380d58036601601c000300c00742d043d105250001012072903824501d400b44211400c0082d06e00010b0400342d095030005d801201c1406802c100d144803441c00e82e2084402c481000700f00080c2a2102180540d411440580400c1124505020300c811500114403030b003109984040704009a0350790309640d5081e41e01c03000080c4c0004c01103410400c0361306c0000b10004400402752051242a10f06100c1100803504136801085c0b100c48085981004c101c203900c10310310701884904060303041d0310f8145202100c41c401e120550f505800c14085000054030303141c0000c426950002c0404113030300d034841c00081d6945d40c2c0b441805140c030038201001a0114104035140050950b50760395141e1562210010b8560200c0e000c881c2c2c01d0960303076001c200d03e440c0e0315503042c1d410400c0203000b4142e07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 769554460 1250 769553210 769553227
    0xb0613080c030d02070603020315091906090c0215060f0306090a06061d07260127050402010c020108181207060c030c09140a0f1d070509030c09190c05 66
    0x240c0900d103035407079000740c1c04101c3d58100759400180708000c54101d4034026a030303070340c03141c8111405c08049182140c22496403001d000f907001c0241e6107000d0040e140d4100f0003541d6901c90140081e00e451034003d82c05608129080e00d0324100308426030380d200c10701a11300865030203c400403a240000440380d000c040c1d005099030000f0003c044c05200c005140080044040a820303010700c1034103101c05002c55050114546000189080009415000d41c4000c00c40000a43e501d004000042c3c10041d0780d070410500c4141190700c2402c5511440703006980680d00d05012148039401900e2550014100b401c0307445001d66988401c1000300310007079800320b4100c500c640724001840c1031016038038844158814541421020120103038094503080c2101d00500b5110b42500314540412a080742030340000060000310711000c5070309100180301c82000c0d030003009444480da031442021122030180b810030651582046552420b54500310031407507040000d0319000c1c25806024000d4204880b0b40d100d0030000711700082844030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 769555710 1250 769554460 769554463
    0x8090612041407060e100224071b05030a030506130513030314161805091014031b0d020f040f05070906051606050702011503140105010512030d0b03010b061308 70
    0x741006090300c0100005410304c1c07000350109075194481e80c000c4000c8564205000d2003006513080000446200a0719600507007292045d4007030032244100480c0e00000726000f0070b0340c102a040ea03805d8100b405181821205034084000d4a80601040e42c8403101c0303001c11004d0016032083e180504d42c81000b901850750303a4640a8152a841020700e03419440140c1040548403112661480f81d4080d0b10740344100d030301c2c11407e840398840685c103c0c9400a81c000708000e583c000c0000d28606540e042440703290000c43c000101590343c1040000c008041c80e0050740308581d42441d02501041501c010a60310200c81050301080807507440100082c802e644490038449616001104000540b0003850914500424145028000460080e004002540d03410019070900d10030741c8541c1403004000c500c0081d5590b00d090000000b5030710a8208259403030040001000e1070314004070000d500040e400b550a020861400c1d20052400100180c0c26540354201c2c800d040d910350008100c070a1305411080c086030304020803603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 769556960 1250 769555710 769555733
    0xb1006080a0506060d0b06130b09090903131701090f030518030d0509010c1e14010c2f010f02030108070f171c090e042a140d0809061204 60
    0x1c014036240c102030000545800040301c0d604032901c2e001044408000012480900c1080e07a100c5007034500fa8004101e05038150003c20101404440c4091603440b03804610340c80b07108801d00342d000800100410082c1c880403040c1da030640700d075101c00000c1036206a00c444002c0c3ea140c1004500007070000a4000003101001702040c07001b201070700100b580c900004000b4080c0d204035024035061003401d416803800c10858180d185544c031002c3c41a410300d08020301e01100a2001c03204c0d030384601e5007001c0c619840103100d0b5040c5907140340b03001c0c41c03420301c0c940006600c4000484188485c683c0d5480782c0054080c84228001940205015001440c840740b81c2102a40300030020341151001a41402e000e210f014000502003000c1c0d8814650074928121000069483e4100ca910601480a4860400080c8081004125800a800135001e00c500240300c400e12111a550700030059901036103810f400ca9030915900c883c013114410600b0310318203e0a800019032075040848401101c0898404000801450540a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 769558210 1250 769556960 769556971
    0x50d03060303170702030f090d050a0b0910110403030f170103080405131505040c05040e040303060303110f100b01020c0d0501050a0b1f050901030b040c08040b1e0c160b100608 77
    0x2070f50490401e000d000b51640326030048172072094408038038191250380d969220000303907510104546171440d0924102e0308486e0211090341c494051080001c042c1d03c5d55014803000342848084803460227085507000c1c0ea074a00107608610410120381003a00b020040c00d98424080c41c005c2d1b07000ca4030b4615003810030408866603140d49031035a00702840084038658008620050b00c00c05c4801140f100c50125044030680540e03809000b4040c0d081091206150300740d84564242c90090703444159554540c0c0303445956640c603034a1044140e128046c40d401c2429078cc0c0c400480200144180c488008017a40008e200c0168840141c43c1c0e80d41d208140b1000f084144144044d240b810b48912201e07000443e134502c0070012141c051400d003c2c0c0003515042682c4654043e5030170700402401048000e280f42e600804001c4111411150f1445040128001103803c1c20f810100360313142c107101542ca5851384c401e02c0080d00300741e91202c00c8030805107014002400c03606245104103681c21580c000d2500c1c005e0010140c00c0c003d000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 769559460 1250 769558210 769558247
    0x60f05101a25240c0804020d020d0210030f060b0306031f0b0d03080a0c2f01060b0d09170c070515042408010f06120c0e040e0c0415050a03020907020109050d03060303 73
    0x14402c4d006600900380c1030303000c0c0c2c04072200b04882c901400443d0304010038000c000c0d88004145100304145400d907000809a009261301040f07180e132101031440c900e100c186c5200d0341c03551080d4a2103010345d440d11100c55501100c0900802c110a00702c01141c03030310791505011070214070540200112248284200c5604a92a203081100864031849040c08070758a52502d000c0c481100f500918400c4007500014010520f100201c1ea4850403800290000e141e0340360119009100c0303e1844184d8218042915120039802c8013908030945400c00704588042d048a610043c00740c00d00c4005034800c200100c1002c130609a0b00c48051711007558400618004050b00f10201c4400c2c01c9000340089640070180400b250300c0d2400005901c6c01c54502550210030001d94181c0c054100410401007810116443c54440000c0d60700b88100040c0e00c2f4090034100130b41c0a0300b40c00c000c400000300702503e09502240e13000a2203000001d208401501c4a40c07c0102c2a01c075a80401c0e11190f080041507071040001c2c078100941203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 769560710 1250 769559460 769559471
    0x30c040e0c1801260c030706052206050f0c01140c030103030206070512070e030102070c060f021515010305060d080c0a0c06031a01120216060f05101a2524 68
    0x41400d03602c201e103490304000900c4c1001030507100340d6040008401d017480050071519403aa070703110002e24652100300082804a03565418101040038040400242c500a458881c1008110b41c0045d03c2c130b80200c100840301e5900c8105060f41c28034504007a90041c1050403626540398114100645405030180c00c034070400c60f0820940d1300c20902c1400442d004915445c000502c1001040081e0190003038000240405118680010315140c2105041c416800f2640a03034900c031180c99105201c0350401c9079264100b49800c40400c607103611990105074030071001441c41242155545820955404c8841b109030250300104a400078070440d6454240103281629042c4400f072081111442c1045503940b00342d0600c0a80c0040d0b100044182e01654000711703010030004490324030303401c01c14003400380b00342d41420302071400380801c22080000081d2002e440084541039405003403c011141640c0c00b1200c08007584103445171024044032508403010301d841c06010891805001d40c54588140302d07020540c803058600d4007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 769561960 1250 769560710 769560719
    0x40b0306190906060b0a0c03020606040c05040b09011403010e011a090d060b0f0402070812090a0203030f070219030605040539130e0a050c06130b0306030c040e0c1801 73
    0x1c00107618240921280400c2121031854054042c010a40112a048002081d003080d02d0790f00595042a1501903821100b1030f03242c1c1c0007400216001e1809440010340200001d10220242c1d50040c55800c03010f15102501003903542200ca0980c00c2a0054200500e01e13200400c8500c1800202c0c2d600c15a10051a41c6440c0910002401032617103508000d150703e46496175040c0035620890460b00750702d800380c13082d5070751841850140340c4c1e58000c00004041000030004106461400100040f00b641d0180044d85000c0b81c2c20a03804068001180483e8010100d00e0111f0341c1140441181c00214400d180104181c2022b2520509145100c0c54042c042041c1002004110020950308105411610654001c40c0748040105e0041110690814407603810103100440322500010316101c00c41c02903040e01e602c66404020071440d8440c03012455904044100b00380070000503240110f0300071400070201c55002010f41e0119051700c01c0c620488481e504183d0782e00e1071504105090100d0b214407102030049940c11b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 769563210 1250 769561960 769561981
    0x315060b12060d0c03050f0c0316082802030109060b03300a120c080402030706081e0903090a0324090f170408060c0403210915050f0711040b0306 64
    0x1e240070303c01c03142e500d200c000b808001102c18014603003020a442d80380004082140e650340e80e601d100d070702901c03c032240740f0409107542140e0415202d50b0409400650550b1024a1201c8161000c54260f0021503040c100169000d02c100700d182485240045041c0c030f070300c2c1c08040c1000303410001e0000749010003642c035002c00568141c481d56481d120302000d0300c50b81da0040888166400404c01076440b0b01d4020300788071250f04042034a100b14070880407200e00c6a01d0303080c1240c21120a07242141c2200703c8880b00b200b0000c1002400b5440078a00088134207141c1da210004400c14116481071302c2581d9410184e0740415121070200985490540c0d09001750880ca549103603100020840144c40c075031310f884c1000c4001c112241110001d0000104491807410040841c04280e80940310407030b46004c0940b2000b550181307602018000c03410581b0340c60700e030602c2e051101d03801105800d07200c401c2002c02c00400d403812540030f010b4840d1500801604026010035424002110700c0360b11040c0c42988603004000440c1d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 769564460 1250 769563210 769563247
    0x1406030c0a050108091603050105060a05150d18050607031d07050123040518060405130f02090702012301050a0524091516050c0f0a051e0a0315060b 65
    0x42c2840c02c3e0032035680342070501d800e000010f04018081041940d0000c14818150400c0e40101c0c811122900c4642d80c0c2c1c01040f503040c0312151020341c1a5801d10034003002c88450351120103000d40c5e505205c501601c0540e26182045811100d2502084d42da00c0f000c0c1112181e02c211a20ba003204400030071186083c0740010b07003a003c040014002c03259200c1619885241080103035030003040054820f4040620804c402140644222040780c0203614202c00030f9100da5035007103983c02c015005030145541c1903c039024006000740040c2480103541d01c40310700003c841c001202c2c002c900b840c40d5545100c654141b204024511026074850780c0f0840c008078030200c11031403400903003a014101814544d5541c5403000461507002100080c88080000800c00015501400464010851140c819903810f100c0721010044054142180d00d0342200c1c401c8070600c007506040340045045242000f900000703101c8040010b8106c1e00e107410440d200201000541c01a031090301070790014106144503141003010061a5001310803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 769565710 1250 769564460 769564469
    0xf15080d0518151306022104030b1f0906030203060a0606050f07030903020a0e072303161b1406010b0c0a02060702040b0a060302250b070c020102120c011406030c0a 72
    0x12550400d0a41e543d41d210080300c01c004812030465201c2d02242591400d000c101c1c4a0324000d40105540440d1059160103135400c6a100c0b80081c604003030442c0c40326240c5020080640c071600799107070300c402043d5619004000080400d1100402da490130740c410705007403d00181c08003400341d090000a028580d04181580d0350285c03006038a50700d844190408462203da50750000e0340000120700e012480da02c246142903c103007016200d04105800348440018200c0089401591000e41800401e000c0740d1138847c0c10300c0088071032a0440350ba60b022000c216180c02240c070125000142800c3d411200d400c1404a140140607841c0701c141080107890b29a912080e40c000d0080c85564009003030811903a41c0c0c0e2040e51001c1c0003501c8080d000d91140c0020300250302c41d01100700c0114a0000080036a0300340012801c010f0b038421103818442c1c854010680c0c0010086ca0100c0c15405410310036428030b1442d001421307506001c0700001c2a00301c22a960315008a40c0a083c01b4002e81000c5070440e174a84550811a0854 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 769566960 1250 769565710 769565737
    0x1170106080709120b060103050718050f1530071710080114060103060803071127070513120206070b1b040308091c1e0303020d0f15080d05 61
    0x2d5480420484501a80750401030540110403012028840c04240440c419a001e8900300419241c004054503c141d401c01e800940c899030a80a12045c101810750001c811030191a64594407024522241c1076084002002815640201d1170700030004800080c0b00000010100420302c0e05012000030b24800003102c0305c45000e0440c9000c1851182c1008286004001400c02080000719201081020120564145000a09001001c2009503010080316580741d80080c0042d6189990320610210124140441ca4001d80800c9034019480c0803410881c807459042d5955556500c68001010190036241c1080b4115500803000c4001070b11000111960140c208150b001950794240e0824000c0d00514813900b050305001c1400010400000082e00783e91380212030823080f01000c440e841e20340780310070100501480390f005c0100350b43c802200283c441f0310380240b401501d00a03041e12220107507505000c0c011141560b612070304c1c28800000c0c03444006401d4030800782c0700c10721007104000d00a0041c04a6405003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 769568210 1250 769566960 769566977
    0x3160e151e0406031424041505040c0203040303090f0e071b021909050c0a0e061c181415070e03070f030302060117120a1b0209010305100b01170106 65
    0x414010030251000705080250329034a686811008003c0c20600488404215000001c80c100300c129594200b41d011541d5204182c04820750104009803020442d400d000e0011080f000c51682c40318014400b040f4603640080d5a12490342ca001490500e0503030100b500350081c02000d204a0701a00b95103a0001e00500d0201c9007151501141c3c81d0b0f203c0c0918000b5400004180200940042d40500c082200d206a2003080260b545034180c81262107030a416800040b481c54450300c441c54034101504001c0900103250074180c2c05080c1c5c240440f808000d6480ca4010056054020802060901d0101c030031038001410541048492400315560301511080c244101c03506020b00c0e0f9101081018002c00c0c88442103c4015901e0074003a48603902801032070568000110980301c00c2c01c0000383c00307200814080c0c11924000798018122000480032103070214801100d10204050380d500c14100e130113580100080c6c5840c0c004d080c81c0e6030480fa1200780040c14004d020b11406000181040e100f811107544c4d0038450300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 769569460 1250 769568210 769568227
    0x1b020c010503061314190b0102030447031902070209010605030603010e01050109022d030a091703070e01021b0105041703070218040c0501080910150f08010203160e15 73
    0x40c00280100090101d41d0108000391044200c046c9030050b0340005003007244031640001261280300d94010b0451502c0b41d00380f40060103041000101480c403c01c1c1540c03420702041c02c55401c0d900d0705105d62004050001c020701c08400a00100200c443c0c16043c000c6181450782c0d40071401e05030b814801d903030070b115005c00020b241b51000e410600c000c2000740300030810781d070710348808078000e401c000300049466030b8202c0400074a50074890b50035140070010060718219524100d4a0b40605100b42c000c40e442d070f600132048503000003100050b500034800c980385d01544608030b5000a01d80843d0301e10100490204080c04c03942ea036008021074094900f9925551300c110340c3c1000386860340c45500ca00035004010600c00c1c45d8035401501c8001d005500c03503040b401415980d10011a10100d003603540c85410b80141c0003c2032020310700d07440607512000005000c44455941c07210300300d10003c5075001d25200e9400004016101e2221035452420b01c502d82420b48014500c40046882d18101c00c840c0c041d0040c0c00202a003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 769570710 1250 769569460 769569499
    0x10510120e030f1c0b040501080601031103030403020a06050a11030a0f0c1a13060f05010302060d15050907020115290a030f05041101020118030806040903090503010e011b020c01050306 81
    0x300c2c03c10408041d669603401031040765021030419943c00c00d25629140740784000f80b4041c003403281240d2500c0010101c90b401c40c1c90b42841c0a403640100c56051004100020041c1c544400300e01c018540317500c90541300c682101d0090300c03100841700410810b820400c4158585500116110210022807801c01800c058500d0440741c061602c007404201c452400c010010303140c19100d03000b80c005108040a0080d155144860820f540c420300009500030404d12880f04020b9995015813080a890040d02c0c410b00d54820114030311080c1070b02e01000503511180c3d40684500022004401410113003801c0c080c40c820240903000c6545e80c985100070b410000540400014401d03080000400c2070741c04104414105844c044403040c0142180c58055401c07c001d4941072084402e1022290b45c05880351415542d581e001c0200502c00144100e050081000003c101501e00b40310b403200c00f1020100001d40d5140c402e0020b0003042d1410b5500c1c08542c0000204003040c4d0340311040c1ca40181058441c0c2e200e9034128101701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 769571960 1250 769570710 769570717
    0x4080d08281401140a08210702040f06030605180718020f04150c0b061c080a11010e01020307021905100b04090f052113030213270b010510120e03 64
    0x1814820842c000451045824400c011220300104c0f00705619940d214025034903a102500c580100a401d1042e9142c9040710344000e0034003c0c4001c100040010032404030800f2142c407504292202a90390302080088400c0ca0050500c1c104007200034403100e032a00a80d0b80c503440c0d02000c4c4440c0940c000c9a10301e810141d00c429a0042c00b4114220003000c03103002c000602c503245000f010750325510082c0c046001030070081060000c5c6403603c0c2080c2590701c481e0301d401200350700040046003007004886482c64400000c0c4200c609808160001683c0d906000c00024506030041c026180e260301012800d40004100160424401911441c04039800b242600020010064401d01404002980e0302c00804c2000204402c0d80c03501d40074282c5c0ca920420f004451046016010711000c50640007101403001d460b016208241d0160f6074072000c03908624645280203121841240303805000807007203404082182c2d040c6040e01412003510b0400740c40c0c0403100010100200c2000d4000366968031903006401d40010301c03c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 769573210 1250 769571960 769571981
    0x170c0c0901080a0c060509011b020310060b03160915030513290a0219030f09020411070b06060a0c0f050c100207050103050903070f02090a02120c04080d0828 69
    0x210640e0360351200320395102c00399007000700c60600c14204041002e5000d00305030b07003c4500c10303920380a6a074140131800844d4a01158160303032600c924240429000e800340100030140c011044011b46034100145108400c20308000c0184c05e00c00120710901070b144c41040c9640d1076010728600800c07580c031891900c02a10790011001ba000c091620320052540d000c1014840d522606c003042d107082c075070360490150f040340600c41040f1426243c440c0300581e018401d820002c2d580310305000001d10003030280e00040c1228000c1d40079008108000c603c0e00306211140e048954015400c0c0c510500d04034003003000401544c861200240000c403802c0002080c400101b00780800110f01604a0701480c170040401f07542d6051a2286500080c200400194031311004005d0703920141e800a074007010010b450b801c00000c0d0344001c041c1442150b00b80603210750034542c4a02c0758001d01c00300c5480d41d940c50800e03485608200b10b80e8040c10504c400641802a503c00b082e4454559492200303a000355501c0c2400d07200054001e0000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 769574460 1250 769573210 769573219
    0xc1b0f0303030509060f0708010504020a031b11060c090a120302030d0c050417070e010326040e07080109091106160501091127071b0204150509010b07170c0c 69
    0x8410942c05034411400342a05004071055a600c20200141e0008202c518200156025004100d58240368010708003400c0c19084c04602c10310800740000380300c40030700e80c3c00300011324480c082548410b00780030098002160544051802d030120010a01c0030031107100368108005e910039450189071080c005c0e103400728115242404076020280001b000e942050050490740402c0744c000790785010300040d425003260020117400425a2030b6031a9616042038a400d403510848188400101c201340c0c84c8002c00142403540707020007403030611403001081c410050300302301d0b81c2d1840c060443c07006c980c1076401c81d918134808030345581c0e484c01c03006008469001e0740080200b8640c00c049807001084200211407034005c000350b0741e801c14110f002400700d003043c00c020700c10010045054041259075120710307158010781d4400e2094074072440081d03010500321222901065941c00080f81c041c1f00914011100c0e500401e1042c484c103062160170b0b26100c800f0341660481e04019000080c050181081c140a07c1145010061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 769575710 1250 769574460 769574489
    0x1050a0605040606090323120c0106080d1b020904081308010603060509121e071401050601030b120c09060a0512030712030c08010302060309070b19140403030c1b 71
    0x4500402619090003410b1082e401c1c9180810b010340328192600490f900702d43c110342030444070204c40320b54081080583c601401180b145603c0c1e01c2c041702c0100002d844101c00000c8091400e00e6150810140013080010402045100ca14102d6103d11814506070111404402500e45241615480c031070b210a10018030080740340003e0f00352066001e001182d02502c014001595050f018944440340560800070052051107070447c10260740b40c110503070f140400103c80c505510740d22114003003103003540e068515a450b54200032495034940070308103001100343c0c0c0381c8108001c0c240d48aa21080342d000b041e40192010070000d02c4076610300c10311000400010f803c0564800f80b40c0005526940501e00c1a1420340c420300c60f010620703102b441a0b05030700d49656107180959081d81d00704006a4009490307010644200c402c003248070952a001051201b02903040d0a107111040c08010785055036400062480d40000d000410109030840121079440754844909410138508a081001042c4660412140c0a120307a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 769576960 1250 769575710 769575721
    0x6030f0e06160e030304050612041502030411040b0a0b04210c09020307081302060313061b080108160806160504090e011a030c010c03050c0c0d2102060702060105190302030105 77
    0x1c4900c103010404a81c0c90524203003003c000d0640c0c0f13100304d2040c0303900302008105220315a0b240f0340d446074010384a4030060010358ad10a0b00358040c1d07001650140c0340e00c1ea81c5820305c002032529228030b80640e8000e580100d031481c6009840c4001d40154441d20320a142200702840f0b0300c1b2541c1610714111a888000700d041d994507841c0900080d041204c0306000b04e01c4940204128801104818801075070003051030b0b203035541e448481c003040f0741c11983c21200c83c0d4a5402040152002d0315020038107d8060350b603040b056140c0281d140c58000e0544410100d000b00c0281404400c4020481e1640210b800020b07900700b1000d500d0850705442680e0207015075928003190101d1a01040d00540404104000c1c0006031012940c101a220305244901c54003240520130f0300000070740100042c0c00b054968038180c84089100d0740100710100c0501038116810849100d0308041004101c001c080305080510080c8903c1c940000d000e9030300c14044c040d45104400c2c3c05681a0580380c0002d408000d10340c042c000341300b2800c21 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 769578210 1250 769576960 769576981
    0x1e030c191d070e06040308070809060f070b063c030309060403031e030212040f02150a02030c010c0c032a140a020102010b010e030c150403050a03050705010f1506030f0e06 75
    0x107480c0b40001903c1d42540c000240303000815035041d01d4020203140c0c44c0c0a010741c1c40484540c010014685c001400380303c1c0e58003034058013020303028090040c80d095034240303020010030a0030024003045e10b0352010200812820380d400004400880c0140401c00e2050700403100000389103005541c0e443c1d622180010340842056802078002003101040f941d50f042403a0704900940c1680100c505100f080030b804c80004021078130907103211440500241070b03507003101000c0c1940003060380141c03d1200568000100c08102d15801d200e610380c0140e05140c0b04200e035901d942c004203242450b02601d884407443e140500181003c4081014450758032034410410908180c0340c0d6130f01c03054007903000da02552030864422020b500070042c2c03104100700140a006003141180c00c12803000001078071000243c41c01e200120000304208100703851903010751206522203516145c041d0a496014403020580381c1800200071004031040d051005981c0c46040c0030036022805000080204600c443c0d0f0340043c4034000900c2000b43c030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 769579460 1250 769578210 769578269
    0x11090909071502060712020a090f061713170f090406150f08071b030e150418060302010c150f06060503060a091a210d0504051e030c19 59
    0xa400700c8480102d003203032505a8440c041100d8441c04980220f9402c1e00504182e40202544c0c009410701407001500d0720176480f44003045410103008034504107034090b011802c2400282e07001024021804541680b03540e61100c0c2c80d40c00403034081042000c40d03c01c401c4801c480903219000c0e0090010000c0580d01d0450302d0380780c0b40801401c00400e00305002c1101d003500c160480d0b4030461142c0c40307207241404010595852018040b40540c108842e280440c42d07070341e403400840501c02099410840e00c40c1d041a00d4803003000007170078101c000d0900d4800100010b0b60000c03240c10420b500659800186400c0c0410340004d4100d055503406580d26082010a0356030b003080155000310405e5580d880b40b181c0f17a4007154110b51100c481024488182440228989007009105031500344281c1c1e502200c1120b4000f05103003085407034040010981c049024019030a10001c02e440030403d05071810401c826040200e0346504d01c4585040c046c0454408000b441c0c11642d03440c00081c9025054210700040419000d00c40d0003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 769580710 1250 769579460 769579469
    0x1e090f1a03010b0f270906070e061c0504030912060c080601020120070609080d06291c02091c06060e0405030a2d02010b0a0501050f0d1109090907 64
    0x8000d0040340c80300d040510500c0000700307024080d10b110760340340c10030068844403007408000f580462002680c000d03007172680c5440c01001d4040013081241440304002d03061b081e65803d1240512014052558134843c045491003c955003490006aa919141021541034100d82c00031126170450f8081078040281540c0000c00d03041156640000c161181130049003654000c034010489908080c81c4071359030040b400010300d05e4610a01c40010100595992150f20350030041010040319601d030720820070306e9103040d110524200424070411450421400d043d1a41c0038424800044807080d9540b1071504055a04482c4c0900d001031075080d042007034903d40c00c07030810101d00880c1c04d181044400104000000c541d14000d95014000c1c60401e04068012030744003100c2900201180c6945100d6055034066400c0d91600882c99400440c3c8000f14209005419549500c1141001801c02819551226420075100c0340c0304140d502040c0c01c0ca141810002a0140c51440c503800255901440a0604001580720403103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 769581960 1250 769580710 769580741
    0x7060e0d0210061503020f121807080114010b030601200304032306070f12050c09042301051002010b0a090e06010f05100503130b01061d0301050108071e090f 69
    0x3414203690006441640c85112580e442070b05031844468026000340620405107c2d88908005115003083c0c00c92000b0f9840300756882841c1c40c030707401205003488800003401c2454000d028001c410740e0180c01b00e140500c074410341c010010000c100f042c0c1c414411034500c641c1d0b1111a200e051900000301e510784e801880211006284455800307000a0f0b01011910028042d0f8085c0100e40c6d00e10303405403989810800040c0400001d016200f003600514816203000c0c0310781d4545592204c010741c0511080318084540d40e8105003640c00307d8240011b034401d0309810b503030050303500320150414500140e0140c1161242c20764405134006010950880c55808000e01c164541c0c100e841c1c590340c0e205141c0c0d00b0710850003500d40121648441140d5140544011b5401050000030110341c0c80e01900c810750046002c0c0c001c14001040c0701a81d03c4040301102c084102000124003c01c100d5151505d0983da44425100e07442c0b02d11014042d601c14960035480300d000a03d0300300f406116008688900000600d80e0b80350407540e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 769583210 1250 769581960 769581973
    0x20f01050c0d420b040602010c030e0606030c1309080313060612050d0e1201050403020f010b0f0f090403050903070b09190e0f0a020c100f0b0108070206010b0a020307060e0d02 77
    0x6160020403c40e1102c10102c1141e085154040a8055100301107801c1c0c0b80046506180042c0b201c0c84c0d800104000c2c00c1d1580000786282400301c00409903113555800340f809500410600116540c04203590740c0d00c170f00071586074481c400c03280da20001400041d2030140c110720f8040b00300140351050700404140319201d0403003040b40b25150440c0440b001480c0402410a034020100c0f02071043c011820005c0701817006118805012034020b2103400c1d1001280c0860060b007285040d8941c50f5424054a6014041100e07012504400040481d111000d00d06650344180303c0040810141806070b411201d901e11f001d0281c900c03032a101c529140d125400f413642140102c0c25100988098140134890318151202d80d8200d8080b511000454a0416806803541800d16800c04c9400220320342005034500e00e103003d59010441032820035081080b5503107006418107000c0800c04110341194003240350703415180c0380003146807a4001c0c2d460072482c1d40a817005c01001e0b985401822003003d40b00007160382d8120515801c031600c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 769584460 1250 769583210 769583231
    0xa021e010207080301090f02040f2d05101206051512070f0c020105070c09020d06030b1e04080c0a1718010c0309050111010f150806071110090201020f01050c0d 70
    0xc074410b00b200a0100e0000b8401486028103980210884804151016003440e864003100450382500d40d10680c3d0380c1da42d00d1721040b000704004006421008085031881041c91414011a03c4078414035840d84c2004500e0702840c03503c00c41548400c01800000e000554070901c0007205404990120a01c2c0e00900d50100008214a101d070320b2030601041d140d0b4810b0702034840d0f94010350302508640720031035050a40c4d4001140020447c0b000d4600d009507003101061740c40c614240466014005803060100842c503c14140b03c4000b006009604150300107d8140e85070a41c3d002d4604040307060304010007140f005c91086d008070203040003038040190300d01c001064042d103140064036409402c00005011a4544200300415801090040c041842880002c201805019400c0d0700f10b07000d100e41071440c0c60300b801040c4850441000380660156550031302c0c201841d182c0c14a00c0c0e54100494801d07058030340710701001d000c5901c00c2c0402001103402e17500038009170030000b020000c0b035001503a81c1840285450001007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 769585710 1250 769584460 769584463
    0x8100c021b0607060e0606150f030414031b0a020f0f010f08190513030206010f0e04080d060302040510030b07050717130308070305091306080c240a021e 67
    0x121160020498003200001501c411005580c025078403030070a224000100d042d0340100e484850515025190030320300801000502004c3c2190502080320038014040142c0c0e0202c01c80340c0190b00083c40800c542c42030350603546107101c4c0040701455603e080d803916000072400607490a10500c00c50310001001410000d00c10180c0c0031415150005000e11000799050f03000e1031030f4a401c480c0003d460124101e6881c81030042d01c03800e0340d00b420b0241004a1080602d40d050000754051311051b401402124507040c040000446d0280000e401c920002852403030703183d6076500090007141c1c00340081c4028035010000344003041e0f07241310a0340c41140c0b980019111500c90011292002e90101202910883d107241c84041904007584500c1002008030000c00452002070140c51000c0c032a0f81c078070355184800410b10444081c0e20401e82807003030030038105118514000c94081000401030302c0e0300b2248102c481880d9081024412055401080040d0800d074403940420340300e101242c1c1030b0b03482d0381e051030004c0c400b07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 769586960 1250 769585710 769585721
    0x402041a060a0c140a03110d1719140403080a0507080615131d1f060c0206090a090204090227100c03050f03010f2c06130e03040902040810 61
    0x12640716004000b0300800d54003030080201800d00840ba404524400c0c400c50a00d805a407070b4003513000c83c241c3c1c40c0d2100700403410410003c00c01c40901d411107031044120340459400b030000e01501603024031115000f0203410250b0120440701c20034030071110941098280170304082015600700001508000014507018000c58205004034406451a00411103080d0b61344116045001d0541255040d00790018145809007010a0042060071400707209060041c04600c2c0544604003078014940c20704e000700007403504420200c0368560140d445c203a0780c4280b1000035a000140b0b07001102070910200c0d0115001d0316a60240c42045510803ca512260101ca81d90a00901440e002039010603040b0420701054410f8030903d511a109041a5051036101004d88070241c00c241c20030180340040c402d04010032240c0f001c06503d10203d040d07420b2303400ca4070b4006404244c84000c0445000341d203280c0c030440040059600c09022604100140d94a8603100c04004010b5440f900c21591144a107905512481c6202d2055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 769588210 1250 769586960 769587011
    0x603021911030a050d110a02010c11070602120711041b0210061a0c0a0f031701050d170c07030602070605040215130510120c031d03070803011202040608030f03040204 73
    0xb541000a4180c040f1882d03400140100d81c115100c030980031442190070040d01182166400218484c0106080101100c10344100c2d50520f90042c0b108010440c1c0204075031507030316030003140c1c0ba50340c0c1d4150902620358024801c545402070b00c0d01e4850002040c007241c044250b48101d90907241c044443c84409810b84089008103030301841030400740542807a050f001030104024110079203501e802c180d00c41d00c64015000038154046100444003d11903181d5a41c1d49003d403c1c11214042071800540310300400711307081da8940d401841d00184100022504200410056070301039815036840040d0710f07210b8081c1c00f0544049006521648207103000e400400d00b55985408007804043d2424a00f80c01c02c0043d2140707014010901061851045040710180154520070321140c0740480e0400945010754914284582001d00d6030704288203501c0010350b6a0116030444006603110301440c1c4090000400520b0382d070348922258400083d074101a42d440303a01442c800c40c000c440030417410200703110301e502c0485460301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 769589460 1250 769588210 769588213
    0x70915050603060d05070f0b1801140909041115120603010506010c030c020f15070b01150f030509030415110f0a02011b0f080c1b0a3005070603021911 66
    0x4185090640244544174051800c44008a999281d0b014480e040b682000c1c041c41c07000901c0d04405090719581c804103000038a013902011318000241c0380a070250080e5244502c420401050601046881c900c01042c0c0c000c150028005001b45403449640c485900829040b04000000c1d00c2440e040c0300e407502c07800040c2c4500c20f80403081d5500301da41c030b404400200c0e0721240c0c000c1100540d40310740340e1500d640d8003404501a075480da1410b003042c1a4405a00c8000305828090300f004605612028000704440305040110301600c43c2c441036030a50141c1c0d04a0400d800213684192078156014031014050301c421019544080c40c13118160340c0300d070090748000e2301280a5901ca003012205050306003044500500480c9144034143d81c80110650155480b4111070b40112140c5405032460010b030ac0c403006040700e40018441c50301026151030b81d41c4080055045454101440d1030910b110400c7c4c00c0e55a21006956440d6190707503001d8029040310b101003442c030f002c4141406000d0301400200d21640d06050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 769590710 1250 769589460 769589467
    0x60906010c0606090213050909010605060412050703080c0102220e0712020c10060501090605090d030c05160e070e040c020c10020120070b0c18042304050709150506 72
    0x14015141e80c064008125009940c1d441c0001c3d414246201904042c440000c900407040d02d05010407490b0940900812034592415108000a5482e01d0890302110010300100c181c2c3c2100d41001410b00d00c15a0014004210029107100e81441c198000d00c0740e10b00f10b80ea824074904522001c0c0c0ea09402e0750045084000d2070801042c1c0c0e050203010442503400141c8000341c60140f000341528207003414100c2c400b290035260301c2c040c0055a0000342d810094149850558102034152000a800d8600e403140901404640392501c0280b102c00d20000340110350f280200310002c0c5d5a80d43c0700807100000c0300e802001803c2e019004150740350038090f44410243c568020004c0d05001c104100000d00383d03012020640d03503901d520050344240682800d80090007045c41da616905207007400d440420000b420541c003100308101a41e50301514585a25034410192000903040a00310b41d84000d80a020401a01d0200041b0400003000400500803054030700c5043c00707110350070509000210f024050300a4039846203082c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 769591960 1250 769590710 769590721
    0x270c0909010e070804020d060914010615020d021504030201090f05030702041a310f0501150224100b0309030d1a2101060308120a110f0711030c04020d020706140609 72
    0x6111f05030007501450300003620f40881da0390311000c2c14610307074030300b21903511664200b1028036210580030400703001d800580350f40d02c0c03800402501c0701d614550702c5072140c24410129080c903100750300c46060a41e0012440d150721401e820030319541d4204c008228410b5040541070390115182c100c0d003400085015000c6e031550f0b41d5906180340b5120a1100342e00102c9004003200d61091818003520340c100c1000c0300c000800d5418036030b074030030988400038201c070955108800018a01a80c00e026207000024541c0390b150320b03194920a010754500c0c030303030004200c0d98004c03040c08035004000c0000c0501a803422002c00860286101c4c0820840b1303034600342540100582d440b4502e0a100107010304000140c3e4000107106602d955401202c0d4015660300145405408104040d1000c540702d00e040b1166224501070418030030200d0008640714261004080501c2c40160076070644041106981420b00104103544580c10500000000c0d045501e003564405c0c140014500100201c40941d8020380c805040209541e42d00e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 769593210 1250 769591960 769591969
    0xb120a0b03010905011b03050105060a0f1404030203120c0c010c050316080d0603030f0f03141306020909090c010e0f060f21010303080402091e06270c0909010e07080402 74
    0x60560450701552181c03190380001e40e01b80706d40d00c266600c0c1e442a014210200200031f04580b13058001a020703020800004540d141c005241c0440d6203503d1900510325803801000440d18080c550009400d031041c18051080011410080c200e29440402260b00c24a4040300464554a240c040908150810841440e070440c1e01c64504030407602441c055460302e40101d051500700c550030f80c81580054000205900241d40c8161580900c5a451406000045c4801c46411940001a116180001d00342d00e03c60100301164041e1400748a00801c0d43e903440c5041c4003131648901e01200c0780d900041800190f00f100d4030741000b40c2c0d100044042c0c821030410801515140303c60b031051940c090140204404901004008101103001e18842d6880010341d040c0341c0b05001019501800c0c3c40d007586092000b02c0e010034010840c183d4030506c115004807041c2d1030b4040800b0304001101d000894221160100400024140010060307400f054407005410307a85c450b40c030700d48580252212000220880c0206025191 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 769594460 1250 769593210 769593221
    0xb07060b040b010c11010e0a0e0f070503070e010309020d1209060306080a080708210406140a18030f200703140a0f171213050d080601090b0d020904051f0b120a 70
    0x1814a114a007031303031900048c41c8458542c0540786402c90a002c00442d81d11400038150030500c14100f480c00c0d801d140002602c20b1030403032080da0425959605c0e2100f5940c030b00380101851f542215840c50780c10940d82c2d00408110f8540600b401203418600c00244421001403416003164001c448641801c2c03541d5144000c03036114009802c810f400b1460158035440851040900a504c01c0000007181e07107025800300040a00100444405482e210645030310358880c05001251660515003550254282542980c600e081030308114a5902d58515601c1000c8002885000362801074841e480560b00700008265901c1c44080000e080c1e01c0ca043c80c1000041c0d0300c17061a00b49031310440e0150301b0324001c9120a22216000c0351103103030418500c28400240181808071b800095054074226089281900003c0c214030340c2c611070f60036052000503810840710b01d0340c1c0c1a1405040010800d0000741091440c080b6522610010601c844075a40700000700d40804008a4614402620006000e940e507503c40300e0003041d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 769595710 1250 769594460 769594493
    0xc1a090a030503090a17030a0612080901051b0d02011d07080c12010f0c031a0a060801140d1b050a140a050423042103050609041112070b07060b040b010c 67
    0x310349039000700006d0b26940c1726051000701c601c586440e803412503d00c00958402c0d911100142c0210b050300c1000c950004100ea450b020282080350341e03a428008140d60620904055a646004035a03c00b1007855040d0450921003c0c64000c50350710542c01d86526896145911800c9403a0303020b103d5040d1366007030020205145e8004400006045041c015400c000e0b00c09040b040390019503661041c144209801400849020341a161400a11f080000c05800c129043c0207080c07020141711550076040e901e03981d40e200e800740d0120303085004800e40c00c155010380645004031407145158400103c0c800c0c00c80d00400002410080c00300494a00d4a0203102c0242100900d801410b56030348150790304003090f0020386002e60302c04c0c00e1989104050181d078440e03409100316100c0426080c0f400780715056079030620440c2c00c5a08918580420314000740025013140c081d41038080680a41c06c1c000641c030440d00090181c1030300803001442203801100822045030341d035400041c0480d6600c0317141808211154404200304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 769596960 1250 769595710 769595713
    0x180e010b2808061f14030a020f0d0c0801060611031204020d060f0c090f0b040b03040b0915010b03070f0305040b073911220c02120a0c1a090a03050309 66
    0x110703219450141010801c4528001c0d81d4136119403854800340c2000c025005004074a5175054680491002070380754582c0c5e800c0a8410030072441080410342d40e041c200f01007254000010201950303a40c0318a1f001c0c01c528400d800c080740c1340100d10303e0203640101c22a00c081400b80703100100e60362036a00300030700082c0c010030984800e5074444811000c50712611420300300c060f541c2c690f81071003403908171404940045038002040c03107a4107110401482c0c0000d03040d280c000e07a00011004080d90f440741103a28041c2401001070841c0e414034000a40d820866009500485840d5200342a95080140c1501696016200100350000410000d0405403203844200c05200e000208100404e83d0320784007200a0340300340510301010741042c0200c000c1044501d010542038900f03440d04030903460042000001c2e29104161412000e44440007490180c8c42400383d54000a05189002e4aa034203909004140f1351120008888c085418210707042034158144d8040d100340c0085d0028034003400c10703070360417145070304080c00700c0085 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 769598210 1250 769596960 769597039
    0x100807030b0603130b01061e0311120708041b0b0301120c08120406230304081303050a061b02150a02071b080f19020a05010e19180e010b 60
    0x82c0d519032000f14024402c040e80303100c410801d410210b05038141a80418184201c0c0c0c00c03290070000d1503000e100180095030038001010324010190740603501c1581c5861101c04035002c200504075402c88a00c501490040d041c1c0c0c00d1501c07801c1d00e000414034081c029010801000c0c00100a186081c98000c103c0f039204088012000f551400c240d454a0307802c202d140c4600d20045814411290300c100c19080c5201074498640c0082c21009001c00c181c40081c2020b0328034003000911200340107504803040e0066a01008803240180c0d5824128010050310400981148000e4000c0b101d803440060000c0400a1407074045e903580e00c503605540700030f502444084802084115840d90640908075150005020800c00340c0300d5000108062410720342545000700d001c3c0303810340281015032941c1c1e081704296142801c10321206101580005c1c1100340c0300b18003040c8401548000b0549249910702080103d0303610700705100c0600003040d00e0b03090350023000160f03030041e940c0403418102c042080c462580c442001d00c1081d44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 769599460 1250 769598210 769598231
    0x5041a04050f13021b0c010f0c0b010e0603120d0f0b1f0302160605010314010c02160302101e170705090105031306020c030304030503071b0819050d06080601051305040210080703 78
    0x70a000d0038901c0d45e030941000300034081c2540c112649507859229881c0c80ba11803842580c81070150720040c01103614903040d190004189071000c10400440071112140a5100c500480e440c402900a1000b0104214107014042000c1d003410b800003040c07c10712081690341c003200008110002c2d00068002c0d0501004114003c3c041000d511400b40618042c0300070080311400300b00b600c0d09541d01d0280742c0c000c6501c8248a0040841c4031540c64081d03a03030407036044003480018641118102802c451751420114200011a00c440e081041d080d81c4d280c603149030015564840500356450b02032004802c1c00701c0d00810014510707501041140c282c00f4800d44005041401610300035145410807503040340807a0001041c000104e4000020038210440102c1c407050064044e07403101c025004002e01503420114032000380e10b545003c0c038103444902e44010020001240d9034140d4955441c1c00380310b154064141031085100f04813850040b540f040307801401030204072080103411946181c0c020118401c05135980c03610b24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 769600710 1250 769599460 769599487
    0x1a090c0f0a030204031103060402131112010b030609090f07061b05060c13050303031501030c111f14070512070512010b070b070315210204050705041a04050f1302 71
    0x701d4056569401070700d4030b0652a200d0207030400c040c0401e01c00d501540801c001a174414543c01862909404c001c00c1c260380f040480b60442c080c060440c501c1e20311000010a524035401d02a41c0302e000c0403a450503094807801d12041e12414030041301400380d001544107004060041c098401c0b407407807140b40030001d0707016a15803905000c02520240010a00050141c0400b070105602e0310203400100e001e146182858428000d003804000d410a06140e00c6000c0801040c0c01a0b0355002002c403900b041c1c503055041e441031440415884102060000d1824801c1c40404036104025441401140c070b07041c0c07409004011808070440d00901030402c2003401c00190a00b10038001000303000307041c007480e11900d902d60fa140007001c805004208108241ca0437204580d42715030240b038401140c581007c001501c4514546c10506030380120720186d005800c1c4030601c00142d0740a4003c00c1103800da07465607800d410044070310885078880c038802c01c1d6022144039030304e00041c5081c0d080c51082c047c64900c01441e0032076028904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 769601960 1250 769600710 769600717
    0xb0c1b0f0a201e040e010509011506110d030207150c05120a021305040b060706020309070e0105030a081206010507060c030b03010b06160f11030708011a01031a090c0f 73
    0x20030094200c0c1200104014080000c1640980c1e00e5020004905092001c80d61905070101c410840c01640c0b9940c162640b82d0f6808541d035820030000a00981c41c0000e045806403001140003040f032001040c001403680e12a034600b07511045454050070200d980d01c4812000782d0003604007039a8100381204507030404c284030711403011903400c0341c1c0360142c644130b41140711040d0241c01091005040d0040242c0400e444d2080343e504280d800480d00010305000c0c002c04a5580d0142d00c100510f0b8910000078000702e0070300003400c1d05c104c072190b40c5d10558980c0c8880030325882d403450940c0142105418003410000440c01540680d0009040c58202c1c2800d0a80e1151404d1740d000c0c00501020a54440303a882e02e5040c20701440e5001002581c0ba039141035480040341662a2010002404004070955a4410071003801c0750381c0c030032160040c200c2c0e03842510780032103900801703001c424070a031100d00c00c0a400d2554001c1c000c0781800c2000c3c001100080e80010709012203041300401145615000308800100c0302c4a00028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 769603210 1250 769601960 769601983
    0x809030c0d03020633040e010f02070b01081c02030a0807030908030a02030915060a0509040204020706020708030f090105060f0f120717011107020f2701030605071b0b0c1b 75
    0x910050034900c20285c3c00340030318075444016040380c80401a40309040440103111540603940001c80501c0105068018044074000c1c80f441030001410344240591014002e0503038031141c1c280c50342e80820a1207a00b0f091030509000e030150f0001d2058003070300d50040350119030000c824140405d41030660390300c0e070340e0720b910444020758000e90100601c4102c0100300410034140d0103198042c3c02034100384001a034052401c0c4113091142e48d031080060219103031764042e82d420aa1000e0b0640d110001458141c425410072100030303951180e448005207010005001d91402910054030514000c008441070105404141841742c3e048100111001c5d24907504000c481c0081000340041c144500c4846c00e42800c1d160600f000a5008100348002000345e03546011189055104a940711004003003802c9040c5d401760403586940c40851904000001d0081c00d4104921481c0f02d5543c2e0380e40e00fa07207154496410b0103101c40c082c2013100040c0000d040c1000781c200504406140103202c00d95000038001040c07401205549 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 769604316 1106 769603210 769603213
    0x2030d020c07050307090606110303010f090902031c030b031905060a0522080909221106070c090e06090a121b0f05060103110604030f0809030c0d0302 66
    0x203282c00a19000d002c0c3c03041705554003104070081009100d08808201a20122a44000040100e905a44201003041012414a01400b008011091040341c05200b50303040c050541103035008040b541600da42d000b0403094030000c1454141070010910703a4403002c8079030015002460205c1c64030360045140d5400503040d43ca8800402649132051201306100d00081c5026080c001d51a0007050050016510000c00c0e131614110b2500c0b0321031010160f8542811550a40005122a003100075419801030101d410a01c40303449072101c0c2030a0b0303400b40304813a9442e4103002520606000c00c0307620401c0e04010b48243c2ca0b5584a4030b80058903000904104031840354140c100a80200a2460035a08160b0305a6185564503006035500c030280820f0b40c541ca501100190381c0d144c510704032000d0300d84c0030043d61465030301d50351850003a130428030390540d05003c2d42c2101120340d1074440d403905040340640d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 769424460 769604316 := by
  have h0 := BRFrame.cov_init 769424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 769424460 ≤ n) (h2 : n < 769604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
