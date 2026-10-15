-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5491
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:01:59.59012+00:00
-- url     : https://prove2.me/submissions/d9cb9994-9beb-49bf-a028-13ac523d860f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 987410071 ≤ n < 987589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 987411321 1250 987410071 987410077
    0x20a0e1e01050d02070f0b0609011a03190b0306040b100b071104021b0f0703030f080c030a1d0111070b0708040b0f09120d020705060a1104091104030c080f06070e06 72
    0x3040c100540012510400399440d0101c035090341e03001d840e003203202680b410100b0840c4801c2e5201881164404000596103103c0d025800c13440c0522211b0a203540c503006110803040a04a1490031660740792804009a56000e11040d0310030390007030f030280840b4030b8507415601c0300c449107410040745518244a050081000b003212146800c2064400684d140040c1902d08071501c00c80b0a030710304c41c0c4201805000f24640c041000402c070382c0f02e52215140d15400c0032042c6c8142401f2154240180b01c01c0c03000803403070038007504032108034102c1d48142031300d10046060032401c2d40c580c100644200c1600242810800c00c081160383da1140c560316005a00341441d5a811074803000182c880b015110019000c245212010301000f140c1c00c3c140c16081d541d845801c2c1e44040603410450090703819014690000d18000510300464503500524242c083c941070030041e04c0001040081412503607214240008400100700140748006001c0800041542c240020310301854014010012410048190001502a2185016 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 987412571 1250 987411321 987411379
    0x30f1e05071502220e092109010915050c0c0a0b03011208091c0516030308181e0c090112021c1110030b04110c0304090c1b06020a0e 58
    0x5503241e1024940d40000070740103420b11080c1c240c18a00484c1c828004285860003281d45032030215506a8461094944841c494503044140078000313108413103032150460041800c802c05040050b09545c0742c5441c1102400c00c1b00121000c900b000444614040c0200326000c66110110740c81c0100d54203000441030076000611440c41d0001001c1055001c00c4481c0007500d221000282108094035040445004d1008400078252154060017200280703001803200284180c03601034903158035540380d0201d0300580200d03141009980e4000d00789554044120f8171810404d246803600104450b48030782c41044500241a80f01800c0052046165001a150041001c503480c640103101c0c004400305040c10900031103c180003070f50281c12800502131954056004140105c4240c0c0d040003210822802c0700c00c1b0b8030440000c1d00d59507000b030008001c41d100b00e4001d11000301142c500182484030800c6031803a00c4c540180c04440b104d4003c11f0b14101030764000c0803551100b008640d100c2590b240c9400d107402c0c011590a07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 987413821 1250 987412571 987412583
    0x11190c081e0712030215090709060806060f0906010201020403021804030206071d06070305040801180507081f020c0a0c030804140603060117042d050601151b1a0103030f1e0507 77
    0xc403c018540240410300c030211840c07134940c1ea20702c4c22001036038488800703000d0030740704a240140c0800e0800c00000c0b428401c4201414540701290620108480c288008100c10304544d02000b0100c0180c03039a00d000d00088000c05007080142c14149006420300030001c1400007003100303565010070049010400c61080b410141c84032580c802047c10112040d102c4ca0b004401c041d820142c40900c00901d1101d6800703001c0c000e42c240d9602a80740c41c90f4903100d607154248a01e01c90080344005135003641d55070050405089107002c0791a00d4609983d40c02c0f10080c0e81d442034441050204007002008d01d84c0c240c26500c0881103c00b00d1551420100207400740300080369104c040008240005c04111000100c82100c100b200b040294070580f070001c0900d25848208200d0b11030084100000729800200c201640c45842c03500e6400e181c1450013625203180100e60400e07100003140140c400c104085000356140694020740d1420301c081c1100300007920300c1c2031181315600c40126000201400c5c0b988001a9040c0700d0f4001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 987415071 1250 987413821 987413849
    0x80f0403090e012301020102040f05120304050a080a05010b040b09070f02011104090605010e100c02060a0519030207050d1404090b030c04140f0a05010803030711190c081e07 76
    0x3040896904a45810881a0100d820000b050070b80510551007000d0b096001e81000c481c039843d004a080c0e00075071150000c03d20302c0600c1440503241c10807010030846010800c0b0303400e0075951000a8006001640303d150315410190856042c40000e00070031840d143c05480030311510600e00301050b070300d0034010700c810100960700e41e40060007403003034100321520348014007004d40741d40d15542204024000392040c2400325009560084103820302902c100c4c0710324256110304030100c099400b400703180c1d80503000c8842040410000324003210804c1a0a44c00c00285560050729808103103002c40c0b4280c00d120352007060040c003441100021b4003800840d020f5420420011034117412400c04a89001c0001884591107414440c010b5004031404040c144100404241010356803100c0ca142c5003220b40c03c0c0a20541038008000140900b17014141d61168807441104507009261200602c440c00104820101c0701d419485000b0002d2007410002d5416a0f180300002d008a002c0001440e6641c040b144a001c410101d0ae07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 987416321 1250 987415071 987415073
    0x271006121805160510030e0d0509130504081c0b030606040c0912050109120c0f170d1a2407060b0a3f200f03010f05150105030601080f04 60
    0x12850380c030741c160300604842a00a580e2883d607440b00c414020107000e03002084e41904c80314440d00541244040407405094103030003250b400c8900340e1000700b0307043e040074000c5a148415500c82c82a00d11070b50051b00c015441d1000641000350100e00040350034100303428205100810354011403c1900132000316400100d01c1c00305130054a00c20340c00e9028003c505154001c0e00d05000f0103400000b4040d101d11440c0300348200b1840107942d610110b48029080e0b00021182d1000203001181109800525a01d102c0c286280d85040d0b00944072907850070003500062101c200058241076540c1c100510300007004407011003042a10103128094000068425601ca400c141405e0300d4444403007015000f410352030745000681d44c64098070803150200702c1310b80d54160446c141644601107030a40050713511035101c1110340303022190301c01c24a607001120750b4803002501101c0003941d424800c0c550103801d00c04000c00c9a1801c01841203200040c2d84007641400000c1013005202d0703a0250455901c108000d202c034442e904c83e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 987417571 1250 987416321 987416351
    0x2a151c0f0b062b0b060703021c030606050f071109010306140f061804020f0301140115050f1912020a09080c1806010f1b0b1815011206020927100612 65
    0x56003401c980c05c0301000503000141a40860b0203804100c9000d0b408400c0f02c0a800e00b1001c8070f002e40b080c200040d406000e0250352a9480c1c004000381d0b8020707084141e500703041400041e108002a0702c11608590b0313030125041141c00164003542e0104000c40c24901e580b030208045280c0303c2403050301c1d1050b00940f6000074215614805246018031018000304881300c1c040310709424071202806101c83c0d4680c107000304242140b02ea01100e0000160941071403d01c1007003601c03195044442200c0000b4090b00110312005030f00d280c4040c0c4103002c0c480d568402010f00e000c440c14200304149c0c0440b8007070140320141c1842d00038107850441c0c202c1002c1c40c00c0301035180006000c41f0150b1220f41d4003e01c25800178084020302104a040314010020b0364030000384000c0204065680740c0074890000c4102156000420818441d48182c2440c5070180001600d812420720015140c000d5940b000000500f00300c0300007261203400d004a0344c2c0001528054058a4184000a403014609031905070744140c0360396544541b860 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 987418821 1250 987417571 987417581
    0x200303191116021327030c0f05011b0c02031c0207212003100b0102070504050c0a0807090602060408090105090916022a151c0f0b062b 59
    0x1581030400d5203070007811500b01d000c1880309005078070800a0030101a250201da114000c010100c0c3c002c0c000000103c05031030403800d141154240d0600c004481c0d18400714581210317002505215800000e80c4c01c1407140d900342820402e0910380304110142608400684000600c510003c1d00e080310b1210804060360200d00c0e081c403d402c02101c1914914030460b0401d107030681801b0862044a8100800918103c3c82c8410f040c4800040d80c160b204115084402b141640040400d88043c4195807025480b180481e099030004d031215407401800250001c4a5030307001d041d45802241c0c600e0920301c41d500d042402503881c1005000540340020004032214568052000c5854815002d0000801c40c5400003601e9440b0180072440805400b6042c456110a0306103201c04100240340c46001039042e54400500c28501645003155854003070800101040c0107601d200300702010094240030a000d0340103404401600c5011660710301031001444070001c1e22040154440c17107507050041c107101003410b10380141c000d45 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 987420071 1250 987418821 987418841
    0x1403100b0711091b1902030c1f0b12030d0b1c0b06090c040b07080c030f03010f170d0e010309020a1802130b030f04080d06080d05030720030319 63
    0x1000080c101d0100b1003104000040c00070101c80c0e401d40c959a80c510740c50324031007490780d65040c484100102510303850700075100703042c403040c0e841183e040c017034a180454a080705903c5440112200030540c0b8001c190240102074a03080c042ea00000064000c1e59040d0b40d0380240131003100c3d21600c2d07014000c600c0e00d55100e5a4520f1150840344664212282807040c6200d00a4481720b00644178040011071022552044500300c0e0001d03c0201d2a06070b05850703000d9250000d000c04029400100030645400e031001002e140a80b00941d00507821034a056088400d03103000c10174014542e0000341c8010103458209426507500b20080c00c010401d090700d48000380401e6003a803c0482811180080d107588140300e64094a000d6010b9250303403883c55180e030000c0e940c9020480707803100d002042c480040c1c000388156000c2d14000e0790003a000318009445410301c500b0104400c0380500040c9010040006c003540c0440214042010380c01820f552201c00d03c14a0348901c0020014800441452034922300c0c100154441d82c1a6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 987421321 1250 987420071 987420089
    0xa020d0606080c010801240c2a0819030c0302150901060609051909180b16080609090a1211030f0a0311040608070e06070605130b090a03140310 63
    0x40069250050082815000342c140a101e51a515030ba95401450000d040c0d5001c0c5d41075552100002c0c0d09058803603e145034030010021107120304030000c0d08281580c100d00301e0740000d061440c0066a04000d211010b644054000d500c5a0424680400a11540f001460f014a0a012030f121b490609902c0c101d0420030020030300690204210a0510640c4160184c8103a6502c080c0616a52410007881e03100d8020100e880e00c0c1203942c20000c5d4001d81c1d0040388405880c2044c0201c008040d20307105c4118030202c5241c03444030181011240d0090340005401c1d030001003146d256045040010345103a54101480c5c008142c1098912440c1c102c5004003150b00310309005204aa5540045e800c00c02c019802504480e00800d05100c0d00e091901102d00c191000e0385d08595550043e549c0e191003c0342c14810300c082c0590040c3e000c00c00800454058040c06100350820b06845ca040c80640c0307002104c480d001070240c5955040701c0c1c440d40000398031039040e09100d81c1050000da04c9444001c003800000a0543c0801a5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 987422571 1250 987421321 987421339
    0x423010309050a050c0a080d051b01061d0a0b0108040b0f0c1b0c0f01021f050c090a06050a110708190602040e0405070e0a060f060f0e04020426011b0c03020a02 70
    0x402c1300c0060070003206007056400581c819914603080340d03076020594030742010036001d2152640303507402040840000e4001800104810707554032251495002002c0b5020412072211080201e03400c1640591b5011f00030a1900345814540303911444480312016180e0200c0e80c400c0000315610302c0d042c2c015261001c44442409003e44000c040c03580c0da5100510304c00d0b0040c9503800c034007415580003003645c0c2c6100d00740c3c4012080140ea4504100c3c028907000b04a040340780c0043c04a8012501c4401030440540240d4850320b80e1102903e4014122205100c0c140341300e544405014004400b010402c11340c00d000111804410100601d8030310040d0165070840d01d0f4000701c0c40100000d00500064050856114242c0400700b621042d02c00001d0b10b502c1d0084442e282144a4100a403c0c410500c881d140540c500d00841b801541d4000541a03030301c0f0394405481941e8400460b98450400001a010300b100c1c41c008121480c0d0b05540c0c0c0d040250080b0703400d001d000c00484000d0602d802406101122a4020040c0803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 987423821 1250 987422571 987422573
    0x50310050d17211303030501081203130312140612070f0b0a05160605061c030801140613141009030224130b130602060601120f0b0616060b060423010309050a 69
    0x84d1003a03200f038041d400a0708180002800c110b020075140c20043c03000200354516500d1081403142813183c60b008404000d49802d600c0c1c40191284607002c01004000120041c0382411406c00814080310769400f001c81d004410104041120340742d4400448001903003c1c1e4032000c00c0e40707007074a050050b540c541c1134445101c440c0703508001103070340442c0c45080104c45c4108109090b094085290f420200014049801440144448070b035001e60b01442042c02014145030040e584035a16500c6020b51004900d4944503030400c0007407400c02204034a000c1540b41900342203266800161031460120f900310034040f081c001d100035461011049420030a18040602c0038181d8507603c5001c41d81c009458042584612140030030903038400b01c0d015016060580d01d4100c01c41c51940d01e140282903444404041c20b603507407065032071230300c1e04000341c8041428454100d04020403400c00f0340c03d403201d01e4552440740303004000a020100c09013001d8442e00004022042d000040240141c0c0200309506c000745c0103104450f0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 987425071 1250 987423821 987423841
    0x11a090411030106170903040e13021801080d0507080405060c01110c030703030f0b130b04230603060f190207050102070807080315040c0f230406050310050d1721 71
    0x54104d80c60f41d550300c8030510b01003a80c1c000d2004159180c44054001300410441c00308840c5005800071018a682c410151880d40000c80001800e111540000d01000042000c08420b20010301d12920340c0c1052441c0228030360382c00e40140f055000c0c1c40e200b03060104030300c41d841100f507100e480798040b0301c16102d54403030703044008950300d800c9444103d000900b041c0d2000d108000c240a1101c1d48040a060030810312049203180014000486005402a80c1c58600c0b039800c4a51000d022a030310700c0030101c101c0350b081a106050403e64010303c9060b4468680c07041c402ca521031300c900300b02100d42c2c140c80147c071010203190290180c81403020141c06440082402001c5c041d84500071409100b902182010003000b910900042d80c01c031040c1c18000c40c584001c401200e40c080d0400440490a40315044412695070078201c6c0140c00a401c0b020000713002004001c0c0e908400c126400c040c0034102c03030040c1c403134045031b9030780032890021441000c5580010500b0442003e5100c550114010003590b400c02900d41078800c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 987426321 1250 987425071 987425077
    0x90c0c200a08060a060605070c03030503130501050a06050910141903060f0e0120030c0708090a08031c1109060d0b040c0e010f090506180a08030d020403060e030c06011a090411 77
    0x41913409140c0300e4006015801103045800981d4400184400e0034510744042d1880c0d04000e0000c1d01014a08072100c00060081c8901413003090800c00019a03282080b0610900080050403000d508402490500180c2c0c980c1070220544001128003603c84030344034ac000d40ca03901d410b91004040a003001180360040000b1b800246540007080c00030040302105041405000383c44039850030700d501040001c9030702401c0b02001445950301800780c80c0d1901218101060480c0c40d558405915900041202e902550416244801340403100d030042c00313891490312102c00c0504c5a10070381803050380001035042e18114582c01460103508018400c100d00a103840003c1e000001c401c1c10280000c120592000c02503000f610018141c40010342000e05000c0c03245200000843c0f0102c10075030050101000003a18001080181128112a140940c80c0c80c5103161042c01d480d1182501e11180e00140480040d0850002e020b0781156510044c942c0710b169151082942d0344101c170800b41d0050308040340c600140d0101402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 987427571 1250 987426321 987426331
    0x506120f0601170a0308070f11060a02041a0f0f03071101140a050912031303090e04061a0d08071b051c0c060c0320120409090c090c0c200a0806 63
    0x110048541582801c40e10707510000b8005002c5078041c404114610b106848088490448d030400280d60301d181003541c1d2601e0310440d501d82042f50000780070322040100b646140e4070755408160040c20300c0600d031f003080809c2c0100c03d140381580b1004800200558801d00c0140580000709008002d1a1001c1340c1c54007035134408441441c0354600700004120701400c0040c00096041000c0c0d07141e0300f191102c95004101c404004015000c000c8403034004104040c2500000d0b0190344111400030307071011411805811062000141446060000d141c0300101e141101100e0107180e0002071000c0f01200034481e6151002d00d0b0b00b0183d00080c0b003211442100e03608160b600c0300f9500945144174200c2d80e03441c0440d00b034050349900600040216486020344641040503031400c40360501610070100000c105c0a4044d0081ea00101e401500c405950041c4403120300303040040c040740041400704224001e0080c1c40c1c60707070895006100426682c01700c0c03109010241710110017040140340e000c2d51a074940c0c4995889506a071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 987428821 1250 987427571 987427589
    0x2010e060c0a2307060c0513140a030b0f04050c090c03011e03060c050a020f010504021507050c0d0c05100207060935010c09140a06030b0616060f0f05190506120f0601 73
    0x5001001e10300900a6407114640b0302d00e5600150304040074031400c9e40c85410203940120460304048000b83c1c0300c4002602c12104003405030514602400c080c1d00d8140c07089007260003801003100340030500141c4070031030b8151440342c001018030081c43c60900c0e07034100160f8400341c1280d16040d02450850740c00f000a01590729541d00b00c5040003d116121400c031a810b0300c00079444003e00240780c0b1629041d0380034005d054020410345942c4070740ca001061074411450000c9620410fa0103050040e0320b010344010b06002c81c5c81c4020b003006410500050480007190041103010344010341c80c0724040819000d40b444129600225404825211803418040d21038103000c1004540c0c07003003012600848003812041481c0e03000304038505441c03420354280e00030300d00304500d95000780e010481c0043c0d4000c038440840f01380f403058800161501e401d1440070300700c0707241000c1105810304040070b0000f800c040351015880104180400500b545074400000c00b1702c0e564403040d0300c0d40d01594600ba08800b00200e00c1c5070407a44550 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 987430071 1250 987428821 987428831
    0x1050a05040e1902010512100e0c0c061b040b18030d0c0305071101110316060c021f0b0f0a031209120503031b0f0408100c02010e060c0a230706 63
    0x10800040d40d200030900503440d40300f0010000c400d0545080c4020060042c14110b150413001c05c04444c4583c0e040740d2050000f0601441000010b00c101c0c1c1a41d0b00c1100700d840b103810038280500344c546a40002d850131081c0030709400c08103603904c1c2190448008000c0c40d0f40342d6646069000000220200c4986281c0c407134000d00c683c404105004000201c9004e03403565a803441c0004036a10b5024400c000e1403043e0400c40d05289264040504000812484144800b000e44861083c6401c80545480b03203a0b000864001800100fa8a0801400c2412441e0610710200d1700d80480d4001c24088644111981e5005805502c00414811100d2084545c1c507003542c0c440310003685480002140d000d039100c0040460b0300800005201100d184003804c180d440f500c0d0300500e0f241c00d1110108080e00305170040801c54000c0e0703680b0300404846124401155500b40002e0140c540040301030fa481b140014409044c03110009490340842d40b00d80000032a0b0708080707030604000e9000b41030200c038580110500f154500d00e0304c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 987431321 1250 987430071 987430079
    0xf08060918120d0603200a09091113050402040c0e10030e0c0a0f0f121e02030a021504080105060a081e0309150a0e0f1302070615030303270b010e1312020601050a 71
    0x11b44c1c1c410100801400d035a201900d88810700c401800004015100d00e220000244525540e45a903503000c00703000040403686040c6401000101d800c07860219080c4141d15000084070345504c500c00407204250f003400140207001130955400c180b20b107015a50311400340000440c048541e103140a05a03098000d100440503140c0c880140ba640d01c101d000f4203c0c07844080e10550343c1e80440010b10441d40b02806445c2c3c840ca20780e0118800b005d05540d10051070340301140030b111411003441140d5100c0c0c8202d1344c00c0007082c54101d0700ca817203680e600190a03412208400c001003080e002c2085850300a0058500350450005002903451600078020800000d10078000c010300c40d281403281c00c030000100811032040a0688500040251310400f01110407640b03400d82000c1300041801d400b40118065200400d0801d200001075142d440071564140400c0c003400d003840045051040c080381518203108a11f12951102100d41401014488000700f10845010851411a42c0030618604980741a902c5001c0f180c0c41d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 987432571 1250 987431321 987431363
    0x1a0403080a110f09010c0c0e0a0b01081303030b150a0c060c020d021b012102030108070518010303030b01051902011a060a2712030f0f08060918120d0603 67
    0x2c202804500401406020040780380c52008041c00710050603d20707090305a90b0380340d810602140e8450044401d0b10400c10989221602038100c1e0142c5c02d1034074201c03915000b2240d0302c440050201c00740c100740c2d0758905000241c8403043c0b04142e1b4070020404644a0a96480080c0320034250355040b90303c2401c10796460b0280b40001082000b0070455009060200840d2055620390326008007460304004903003943d1545054244500004400c0341480982c2c0d030342c1411412032030554140d004c507005450741c0041d141a070040703c4e20070741500c0e407502c0c0110b0f00e404044012101802001d45ca80103002d8003a030010a02d41d015030009020503042d24540d22803403204020030440d4010001eaa0020500101c6104603038541c1c1030b640021080030005980c1071035150344a19082c0d00314140c003200800c5640c00b240c081250130100d0482d5040f40f6103400d0005190820105e040d102001e080c0540c44005801c4003003507144213102c003944400401200903183c0107070a900c1e1001d40389a10040e542100c41c03440c40048070302c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 987433821 1250 987432571 987432581
    0xe040506190c020303071101020d020d1b0c080403060b01050d0518011401051806030109050a03080f0c030c071e0212010b0f18130c0e070f0e121c05071a0403080a 71
    0x1941d40c01850459403107081c2511f0004c840382c090002550300b0801b4841c1d44025102800c0054040e50b0300044402c000101c80e01c0f00003107207080070180040605103500140b00700045500352544581d0200f58040603c0040c0c48138041c08013a8203840e8102400c000e071010342d0420040b900e90841d0000d10880506090140d411003003801050f400250310300c1e203034915101d1a1483c90300541e000d000002e400c286c603102d460520309100f2084000407032500c2445a00c1c1d1040c400290000d46840c091899410040c1030600b1910600c240204448404100038111151503072030403903015009030a0311825461100c0703c50007480300c5600350380b00c1c0e03100c41100c8010b07040c103042503a00107034014100842c50301d8a07102a9140103860101f06c6c1c401440302004141c0900303c0511a01a14040d11066401e180d031100250151070610f003403a00800c4426100200c19500003030000c19880981190400080004011111441001d801911410412040c2c3e400d424407140460b04c114069650060240ca5904e50501528 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 987435071 1250 987433821 987433841
    0x3100b0315040b0c0a020a0206041508090d09360213270e0f03040801022502090408031305070f0305010b1806061b0f010c020d020109030813020a0e04050619 69
    0x2c3c00342c0300082c0f402c0c0d42d080c000303002d00e0715240100d900405103580003030b02e5070b81f041d0400451035001d03c3c10844070316001a04150410352580c00f40c03c1c540040300d00180f44001c6032050180d04240300000c01420100c0191a0110b801030704540350340411003124000c080e40c00b445801c104d2024501000401c110703a1a815400400d11600c0081000c02e619410300103081c11022540050040c003131085400310007040140000c0100100250f02e4000017800241c0c15455940c410382e56a10320120080160342e0030041d2030b0700c00c0e0f200204948a403940142203038000c5031400005e0242c45a04404214402900b899508803840b81d0005d10602c001902440f0400d070420283c940c1003001400459024a4141e01402203250720000600e0001411b00543d03140c41c04980c181d14250355a05401c0e1115a03041c011162030050900007800b50100c5a60010010b000c0141403440c12149a0803140440d52030720014401072550000000150800b41042c80d128038054600341d0720040d03514100c50565225000d1407c5030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 987436321 1250 987435071 987435083
    0x1e0f1e06031a0c0c03030708070201050601090608040b0910090803370f0b0604090c080c0a210605060310061b02130c09090627020f03070c060b03100b031504 69
    0x40b024403900318014a000f0304022a0b03d9014003881d54048010009580700790060b507208001418521310280c01c403440500100d0410a04400a00c01c00350003184440e04075902440d021026038941c000c8030b0a10510141c020344003030802080c1014888104081d41c02005500d05064044142509690140c210300035034411403d0550034164810601e03520140d00000c4048012500f454080002451503209030407502c040396030790403081038040d4081074803940016041c0350545410a21040079095039220800150080e180142c032552508240c0c200d0401040040e140c00c4c3c80b403e0001d2400ba030040036000e0000081c08449054090b4904406107003001500034220403000c2c0030500c0c480703010b40003c8041d101400f03648400024a40024810f2070005d10183e038142420114020b840420106000502c9005a0041c400036660003007207401c0700e030060201d0a244011500130b00e4040082d2000c4512143c0c1800f0700400c8401000942d00607460481c2c0403001c0e1890044215007200044106440183c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 987437571 1250 987436321 987436343
    0x60303090b0d060f0e01060e01170619030506070324030c05091f0603020903010b0f030c1908100b10110601050108130b090a020918030304061e0f1e0603 67
    0x50141c10304024280740d49022030100e80580c90b49910451280c443d07100104208100c40104801c69001500c1801c4450074a4a0100781c001408038074502c0c0f0019261074411840a01500c0c0500c20b00100000215803080a0300d03114904408060024850f480480750b02800c2281e81115808012800d4000d0b40c0c4c0c0a450109920b0408042c005c2c0080c0040c5040b02469100c0c3d0b103500c110701486040701c02800c1d5540d01580d40c040745000d060035106010080c50040c071340016810919900814000f401e040103941070210009658142200441c6035030080c07140d400362a048400ca04001d400c000ca4080003900c10441e44880c0c01d4003241c82c44200c028850351900480018447c3d5885051025042850980c6030740b00b1504684500010704415030b0b01d095107034000c403000402c50602c92091a4060242076034010400060b13030f441ca8aa00c8014002401c10303648903042c2000581c41040003880c078024070301c20880225010554030080a44200303188400303a0b1003c40c0007000c140c501902054950204480c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 987438821 1250 987437571 987437579
    0x6010501020d021216150f110708090d0602160b04170301060f14090a090b15030402090a020c160b0714010b060f0c0a02060a090e06100e1207053106030309 68
    0x8801d03000303981c60031400700311821755030089401e200ea0074200a05504000070b0340740c03a0030268005c0f01d442d100300030313000b040600000780070440703c0d0250750100c41c0590380901040b80030700c1c200c0e00a10405085400384544802104244a44011120304c00ca10602521801c40c420401202c8180000d1180c20300045441200100240c4241c07249079040b45081d10103400c14202c2400a120f45c1e64070f4010004150760f40c5031011151410b020794000301e281d00c030b180501e103080c40e401150768408005c203489c950300e8002030708090031003041100c50150a8000c89055005880e11040d0300c50764081d9009131894040400c500b5000d840600c00c18501d640014a80341c40c02e5801402c415040d003003507624050380e000da48520f401507221840281803080f4550b865920807414580002e024003800b0741800d004035260742004c05003c1d00081d041c010b148041701d00201000445401d503103449000e801c000d4001410103030104401c9151000703840c01e04d000030780f90726074140000035a6084590030700c8054005000345000300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 987440071 1250 987438821 987438853
    0x70816090911040c11070b0403030519120515040f050f1f09020d0507120608061521010e1b180903040e070c0b1e010918021f0206010501020d02 63
    0x1004040c402d540700081e000b48500018102e49189041d4808074184c50710151030081e0602400d4094042100388a06003810f45e1802080c5000d03c40468080005014000c910a4001e50049a5060008000784854540010340400c0b6107000c61540d40280d0418080810b14106401002e00c500d044d022482060365441900d98a8183d04c0c481c40d040c082000c80000c05d420801d0300041c0508920808003140c01d0074070b07240040901c014180040c5085151100600078014003040507034114010070b078084600c1c40103600240901460b88003240c0b03002d0740724069902034003040d0007030000203051505607036a41e07000b41d00c1802c801c07040340019544018400b00c00341c0d02d000700d03020702900489400c00300c1e41016101c070525819160700381c5550f400300b03038907400010410043c1054603030300140243c18811003407030300d00b04032405c3c64041c020078113025240c1fa030030704480d030b405c07811011810b80044c00c80d1843d98018844501074096050001c0043c01134400105440d4000100840360000c0da5000700501c1d1007043d915 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 987441321 1250 987440071 987440081
    0x1080f040209340206090303010b090409151802120708030409020310033f0c14030d02040b0c010506010906050322021003140114010e0d0515130507081609 68
    0x1040200032901461031080648406024a070f041640390890080c82480281c90f0220003404682158400c00041c00708070700510549150030800c0e00c0204003004540b034070b08030030100f0f5003800d02500e10742500350b0000c403c403c0d078180c80d680c000d40d2141201100480f005445144a014030103403a4410842041a031282c0c0c2e00035940405022f0440300c1e0f141e120b42c1c1d0712603201c0d081001903030101000c0500140300e007001c491860001101000c80c51148040b500007810307503010280040c00e040a4646415006107090003203420721409090304658854a50f4000b400c581c01811102c1e07010f601c0d2100050740e65000b001072405544040d1640d074115523404410f43d05580103119050010040344a040300182c60306185514028102d860100f135080000342c1003100c0315416480701c0e0040e40380403030310161a41c0056484060704025298501000600d00300f5a2501071000a0880d41d10000c004002c2400b4044008034442882101555034191f07a54007403658400e080c5901807400f007010541046050196804 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 987442571 1250 987441321 987441331
    0x1b21101505030312150405240303161401090b0a060906080c030c310506120a030509190f0306060501080112170c010f0f0b0a0807030f031808011802040b01080f040209 73
    0x8080794400790401b0909545065840816580c2c0c0340c825800142d0030382d20f00580000094000318109007854459044d08607081c24050091142066002c00955080d0462030065411003c0b400041c02c25500c1030000380382c54400d00384003600d040c1c00030885035404102e1a60500d4000c2c0140b5841d00c07101d04004034007083c1c100d0441e100e0244810b130242269034002d009a910110a000141441e2190502c410101444501c1c01c1c80d4000400d243c0004c0e800c002540c6d840141900c480820704c00c02c00c0e5120390040203030400303402c1d00c000200000400446070024003d54000780d8610045985ea032603405e41154404000070b080f4100e02c204400801345480180c407546000e14000328007628000c82d1941181c0828800303070442912461805d01900f0010401d00040c900c1800410060b403a5403aa4000ca2900203402401c001100030214a15000e450740240544060002080b01403030421404006400c01d00080340900c0c20140c12040640c0078000b00341c0300d400714008104003565107608001070b41e040103007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 987443821 1250 987442571 987442591
    0x40c0506091809030306010306051017070318050616090e0a02070804050613050f0f01020616030915050403170606090409060f0e0106030506010503030306031b21101505030312 77
    0x8900c84107415580348600540180014590717a00f07148000500355000c81e0040d03402185140d0300c000800d030740b15040140555114007580d540c0d4441d440708402421a030b84400c00d041c0ca0b0494400d00340080030410b80d008075a0800f0210304090144801d5400320000d2107a0f20406e03501c000001c04030100707038000f0254170344148070230761a00e901c8200084082d00805848807510540c82c2090145040100007840040c40880d0b442c00104403900c0001d60700c000c01484000509594034a5003103480c00b907005003110030b030301018181c00e1000002d01d21f4018a02100c06800144e01d0740481c04111544442c05070003180098065860301980d6002d10014059140e070407507556903200340300e6000308114401c2201c2516074200208805165040652801c01d0680120b8405d410800c140503080c0c0c1d00054200c422611007001985a110040c001903145021105034107960b091144d4000a4400208004400010800c401c1090001d0403880d40224030321380c020160564410440c480d00303411645120765204900c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 987445071 1250 987443821 987443839
    0x30603080a0f0906021c0c020307050312181f03050405070e09030909060f0604030b1b07060516080906011403191a070e0d0b071808070815040c050609 66
    0x560303181090752003003030008000740b806400c82c050a584484072400030f00d51440144010000e6000c0b00400c00c08019143c1c041c000c030200044215101803004c40002c06008054906031040040c29207100c1d8000450490b8001c07090044030303201e182c2801c0c55241007002140b0030307515425115081d0300400d0080c2003a6814480c84000051a0a980c0e081d580301d01d8800d0051900c4002c0130061040600300600140d118484a01c150011912080241d07401c9039005a010111a2100144031035400c0780301c00e0b40c0f1000e0400181d180305200c4a034000340d000700381402d012120071404902c1280c5481c1c06481001458000400410880c0104040c4030240383c8010256004640d009414405002c0160001c03a80b1000b42001d4502070710355001c140da8003e000c6d080000ca545c040c50b000030740104111100914140344840440c02c4544944074031280c40305005203010f10b464030354460651340d2220381f08000c000c0c421070150304040c1c16001d500a001e6580840140754040c1000104045a0004405d66070008208 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 987446321 1250 987445071 987445073
    0x3090d0f0210020d030f02040b1e0d182907260a0c02060105030d27050d1103010f0b0f0f1f030c0e0d030c030c0204150803040801141312030603 63
    0x86a030700502c562150000c02c0d1141c20720320040d0540300c1e000c00d2070184903c1030000f0046882c40390100d070b600b255402248030b520056410b40300c041e405000034208a4a180c84076200d025440184080440c600034aa01207660031181d411001d0022116440c000c94510b02000c190054001d1180301d1110700c61a070321080284100c0a542c440c040c00f265101d01d00d907114140c91401c5074040c80224094403050780a4081004c045101500c1c3c0b0310a041c010707560b0030444107843c600c000542c0b40c10010382002000004a2000740c03d109802c8107003040c6407442546440c100300c40d4010584610403407914040d03d44c03a14402142d04110240d01550012a0421b0007050041903a01d05024000b00c1da804a4400189040340c0131b030020214480010b58a02989002800c480400d40001e0b80d003a0503649490900c042c5121880800c0180c1480c0c0056901155103138400f1a28180c040302402c141d5044000800600d5498a0007800c0280c00351800c00d256440801518041102d02031420b007103060500f40481c0b42e5a907 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 987447571 1250 987446321 987446329
    0x30d110c0a050102120108121c15121103010204050f040906060305010c020303090106080307030503010b0307030b0a0b04081203010311091806131416090902120303130b0c03040503090d0f02 83
    0x207101c03411100c036503000460100c0c496801c820140034008a1000b4038a0810011081030381d03100e07136141c40b0340c250160100c0d030710405102c0c3c001d0782c20150824201c2031000e50f258030000c207140400b002203403120031520352009035040520a68044a800030491505442c444003800000c0c108001c0940b2044e4076087c010011600034001e1240c0c00315a40c0c000c0d5034910380a0b03100b508403085a004215190020011140441d40c81000e503415240980015540c2e52102901640107111116905030002400d180000d05112402e029100b00d90f210426241000c48107a100c103001e20003408002c0290141c48481d5601d401c0c55155030380d0240440200b003061900003114070340b4140080b0381c07240c40307011841001010803642090f0655001600c10051111182c401034804002d0000d000d220021075403900e00c9801c3d503580200c0803070074444000599a480c140091300b00740d190705a90303003030f6020212500800c0c50780d00040300b140e200d6038210001d1401e00840b03804101d800350901ca0f050714040031002140000d030f55 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 987448821 1250 987447571 987447583
    0x6070e10020a0203010207030522061d040912080907080a150e030423040b0d12031a061201060e03030c0703320c01120606080118020c070b13090e030d110c 68
    0x102940b0390b0303511f401c80c0850381002604d2b4a880c0b0804402480020450b491300880c0455250300443e40f90700c101203008001c42c0091030080d2002c0d10054007680e503600440e410101c1c1902030040d440c03d891949440b102da8991341d903101c400c024031144030100a1075028440d80d1140449041c01414ac0e8030b8640d690002c200d404010301c04448500182c5103500b5034920303141c45421000403003a03030801c2c02c451503034980080c60280c4603c030302c06040d00c490702c40342c072100c040d501c00e8015003000309043d03190030a4054242c0d50340000d00521000c00c08618550303170b080ca00041901d40000316400100131903801d680e0760695030b0385015000d0b014404002140d8001e601402c05203032040007c1001806055019000105850480c00c02103001500d000c01c148060b81d0310a072a01c0c1074480f2481014800c5918003800c0e0002c4c480d949104980c0d0081900100714a24403400a000300101d40155100b015214a540b004481000b999034075154400c10074104107800507080300c250f0003481c9400302d00300722007001c00d00c1c2800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 987450071 1250 987448821 987448823
    0xd15140907060815060d0b0a0909060605122b0c0212010912030501180506033a030c050306041a190e0c071e0c1d06030f06070e10020a0203010207 64
    0x504a41c5050120940c040c141960041d00d41030803102001a043c0481c0302da21890012801168680c0c84141180d00c803607003030400410101604103c000c50380d051441c0100558011361f8860800103c441c82e004600040030003203400b9140c4144005203c0342d0b0710b04040180301e20810144a111034030000580c1e2058501e406202c0c074240081a500c103140313800340c203e62151030604181441c00c401402844400d2840f25070909034220001110388400d000a4602a041042021005a03014030524080700315034401d89211203034584880800312545040c2c060300e45904038880050404d1001444603d400e820010030342d005000180300b855200c0010500034210b14140d650104c03440001040750310302c4032b80d80b10f0b0b2205070303050107a040c220a951506141c8000d0340041915422122810301401000341256004042c0d003a008a000702d1400c800c1202400200c0321644280100308021103102d001090071485a00260b03039030107241080500b0050303000580c40c1240c046110301d03108100140c400344001c011035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 987451321 1250 987450071 987450073
    0x90703020a0b180a030512070c0f0b1b030f0a08180a06020a110109021c1505090705100509010f0809030f04140a080f19080c10050f150d151409 63
    0x43c00c50401c0c0d54510403116440780e070007441410010808642c000c81e554418031451000e4030795a4a240c100100002941c0e044405034041081001500354950310040004111200306172002c844482d8040762280642480400500e000f0041401b1141c41000b8840c0e01042045007100c802c01e64200b0b19141c2a4840821504a5400200b058800f50861344402d0400104002070022141c1c590220358003840e100c102000c0ba00745030001070200309050207890001c80c19a001001246414244d10740e0380c4000d48900c40c000c403490480962001c0c411001c5841d109010f8603440c0301150300c3c904c01c94032214014460361a0b80403d001144c243d80502000b040100300b400320300756070748a400d070810060301d0180d807025540c3d60080c01486003040011075584000f403504003d150503060b490070318510341c0c801d01e96011114050800c1035011804d150340030600032002598240e10396070741e0904080303d900440a0759135000240c100020000340100003281c0c114101e020001c00c1048452a42281c060025a00c407003075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 987452571 1250 987451321 987451327
    0x60915051e010f030314030601020102071703070e0d121d1003090b06061201120c0905011d0a11040504020c070909050d030e031207030b1504090b1206150603090703020a0b 75
    0x101000700c0d00000c0c05010b400d035101003840d14613540680800080326900c0c605000110000d030290b0300079410b0b00d48140e0840810500a00c884d80300000985c400c4401c0400314210700a02443d07030a28044644406601012201100c9800a8207903100418018000b05080242c469801151030307e0b100c4040c154115200807825041902e010b100300072000303000c0c5000c1c000c00d120700c04400061416060449050a03d5145103042c1070402015840d400c0e002003080c1810714000181d6080c442d0b43c0f8440646008100d1003140d106e0003042005e40d160840610317920700d41030009101500d819402040f107041400200e4860aaa488402003603803c072800a0f1110b401c880007094591385c16004000120001e8005507240580412214100c6040a01241e00301a5283c00c0041607486464450305c10090b00a58075444030340e11004000540341102e2094019485010041c00f030400002d400c9000d4840c9506004d100c55501040c00040c2d0402440c402c898403c0e0100000542c42d100070880c05003c1e100443c641e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 987453821 1250 987452571 987452611
    0x90a0b0f0a121b0f05040e010e0109050a0c210608010f0e06070309020901060c0f0606150906020705150304024c12230a14060105070f06091505 63
    0x8018080c2c0400c500719030f07080601c62040a196044a10314140c02d40c00e00740a10591401c013210035000c0da802110380c070f0070640008900b114617203070b0547c100c072920034040c002e07940c942d441041600d032292003900114124007100643c4c0c0001142d2410040c24000000030029540d00080303081d00d90307110240c0750084c0d841c81410249507042c4000342d07000609043c02e110300e06a03036000c01c40b132440500c02d4030101301c11681c8000030020a081501c42880d004041807103034584a0084454043c0394100c003030042040305400081090020501d0f500311a00285000c00101e1f0100240140d07600c000c10403680a0341f400c100840940c9007000941d401101340f51a50b0140035034403c084400841c0e0064400b42807262061a140c055000421510390054484d0100300d101540c03000b880c1405101125105001c004002c000c07071042c007603100243c4007403510803c50345e6442d04801500c452160a201500302c210584840d008201c0799044010014801c0c6000c80a1042d65618002151b10a8030400c901c201440f442030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 987455071 1250 987453821 987453827
    0xa0b1b0a12080f100909020f09090714150d110909040302010f060b090607020111011514180609132f0f03010203150418140303041e0f0206090a0b0f0a 66
    0x181d200030b2660300402c55080c165084c0714011824480c80d030080e034035502103000710b4a401c42944182c0134050300d801028184100c0d180d403914814020b140c03101c0c516480118181c5000300d208810705400741d800c0ca152072550341102c00501500030710b03415070000c00c01c800411034a030388682520a40c0250300020300d0b64081e03000001614425841003640c0441400114a15900c0030110703106c042d424240007203030034162132619000d00310140c0d414600d01070301400014800c03000114101807840c03c030303105489000c1c051001c10307102c0c0c0705846840d0000321040000704054440201080080c1c0103444851400300301e090b00301c100b000c40001d92080b100c0503d4600400e070070f04821050f5034a400b03d00960841c58a0f0078030308080d00c40b03140c80921507038a500404000c65034802030078400641090128800d48906810644d4076031064a0031507038902589868041c00710030400044500d60700c81741c1402404000e07000c00c2415080312000740c1d440f816548000402074581c2d402000c100d507100c80d10989030541c1035070103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 987456321 1250 987455071 987455087
    0x7031a010b0a090b0706060801020a0306211a1b040611150f3108300403141605010e191a040f06150e090c0a0b1b0a12 52
    0x41c0101c40a1014484058018500718240d030300401680f83c44080c141400d102a04080d800852036520000d0100d490340d903d50040c005607803410110502181d1560900000b102801101510003c510103a00c14903e1003154602d03009003da00308035140e4543d6034114202648550f100c400450f080811816415000b8007904882d68010f0159000c40d14120100c83c200303210040a0900ca21103c5107203001c5507406221340f1082f18280d108418a1504518251007190310900915031148081c1c01500300080d83c10309051620000014050410303150360364140c420b00c6480911982c1906c00380300d0004074080b69203804080900a200201d0485448a203440c105200d0160a60903203666041020200c2d120520842c04291441255100340da91030400c409040c201c1c1000811003418a17140700095081ca010407026510400e916202a480303031141c203030ba00c0b50607103086030300522041c80400000381420043c0110a22445103038242c000441422800c0c441c45100489000030a2494421210f60100c8a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 987457571 1250 987456321 987456329
    0xd0c0c0c0b0315092d27030706090312150320030714010923040c112a060d060f090501050105040b1e18100e060d090c030507031a01 58
    0x1441d89103007440c0e0820320741e01c100042c0d4a40143d00500200700c0c55640004007840c00354010720091040190040112203081043e61042651071081030074056519038192070f003100c0c0090800031072a241c5581c0d5440c0203440144c00603014001564561a000c1c082401038680010300d034a84100b465040d49803010009580c0a120040c02c283c43c60800e09545001840e0026a107411080000c0c0004140040b156185680c0085101c028141009032083c01031816006034807108850510608079004421150702d41500c040701181e40c003900c044a100142c001e0000c01c02403c0c58140c8501c2d140032008110543e01482c140403200c2e50300d410421188d401901008050b01054109204a525040c0000c0003402907016200324001c0010321100040c4004085148000c00340c21003d8882980000100c041207450641c40d0052800b05a840d405520580f02010310f004001d00060500808001d100010b20f01000121620350400c1008400706204000c001c00271841180c27550001030324444003201c00001a80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 987458821 1250 987457571 987457589
    0x30906090d0c17071209060e030118060513020301060b070204050a0902030304060815091005010230070312020f090a06170a0f09061103010521030a0f02030d0c0c0c 72
    0x26071922220b501c0301102d08540c1d0814200815040d003049612281d100d02c02004110500c041289060140c224048008450242e25424013400d038507000e02d03086e40d40020760000c81c0f081040f07110300003031450303840607801000444105c0c0d03481c1c0d010303030109084804a4002441d0008041005811441c05010340c070b510480030202404018099030229580c0c1c0940c0c0150f000b0b01015400081d980c0e00041c1401d0042d1500400414440c100810b40d500014010b025160050141f0310ba940c110306c0008481090411011041e41c40728000992071090f95004407500700d04014420104c0b1003904290b0024220584203100c41075500c200c4541048040c41e0b15602481c18040414020416610703c281c20640c030540c80c040200f040040c00d1584401042c46450040a20385070442100301ca22610000d035040e10320603580c08025412013501207001034140003500301d8651042000502c0b80303105500c07449204010340100e9040c440c08408001c25036040c000103000007240c0c50400720511040028043c0107040c408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 987460071 1250 987458821 987458833
    0xa030b060f040b060a05030c07051c030501081b060c150c03010f061d01120902061303050601120c09020d0b0a03050f0106270c0905030f030c061006050304060504060209100503090609 80
    0x3c010900380d01500c0e20440500c4800b20020b88994104000c8a00c281c2d4800c00b03498040c0b00022101291030703400104040000d140c40000711720803d001030705050204001d0300800e26142058100a0b050340f0141c10a946405103402c805486101c0d100424002c50f80d0302c21003526503041c20742c030303605031140d5074094010070446041092010f01443d200011250081c609030036840d203520201c10140c0000c40d8000c0d00000001605184620019220000c0c0d901ca00309a49080e47d861100c0410004030340006000c450030940d0400645540340e00600e0140c120900102d00401e000c00061600c0c1d1a692080c0c2e80303900411382ea040d00304020701c9510b024003141886044904200300550343c901d1080c0320000085595502c0010405000f640d1090080c20000c0c02c860141130300000643d00d903000701840c502e10b4481d02001c905489003e00300303a0261026613599905541e1103440b81c00c041c0001420a40e00d85a080101d071a050301d0390b5498508004080e10b03215981e040041b4241d140c094000d001d044690072035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 987461321 1250 987460071 987460091
    0xd1418060705030c13050d0b150f0f01030f110715110406080103060b040f110d11040806160309060911090604051b250606170f1504110a030b060f04 65
    0x101502d070010040b6060f1902d071704000b000e0344160307190fa8100d95805018101e0b910200410060f07818800e80c1c422200c505104841d1040c4071590100b094120360180402900303881c607521943c00900c020403142008200390324001da03410202d501841c01550683c0e1400f180c008e1640203030003004501d4840c12400c1746040e240c040000c03e841e03418000100095200e2001802507511030300140500c10300b00c1420841d0305e0440403081607551010003d01011810422004044100f0f6001c1d40c0841d140440500703103565613585502c00c102e1a181c1c0340c606240c2d44070008400300e20719105a003e044d01c5160041608140e100c10000d00d414010009880340f41030408110500000203810031001600300009a2603466a81303820084d589540048480302115104001c244030b204c0e0091011100341c0f22160f248035000000058688654400344540c40d03204c00001d00b500d05d104604558443e000e900d5644401d01d030840010210701e4164400c1e5a0716070381805115035032402019010032840d046804003c28124 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 987462571 1250 987461321 987461327
    0x70c0b040812030603070314031215040606020705030a020402130f03030f3b040f02030a09060b1519141c050a020408060619050a030302011b05030420060d14180607 72
    0x264040144235260805c060340f203001d0200107440e0b0340c1000011409103407a04e030700300d0301c015445600040c0c41a4105070000421900102d580400c0c1d59028001c2d203c00401602408044d6100ca00029100c0d000400d001441406d1050349202440c0300c0d0740d4a00300041d001000800c02d100b184001800520854600344800c01d031070fa10400c2c0c45020b1018024264043c078009001884080d00c0e6944d01c1c1d00000410625000c07a9028242861003280c042140714031070703801d10800b180d241d0f44c442c0c0c83e0401040401055410b69030300803109150b0389480011007078200403100b81504440580103400000d420303165a045914000c50794812140401142018a0b10441c1c550310f00d00940180d0003103089a0030340304803d18085828004c0c01c0301401109056580f454024020a0f8081c1c4035000301c0e170028807040b0024424401c4a014136080781c21901211a0003919001099541003a0b40d4002c0040044480003210760040c010580d03444c80c10204a4a06a9400404500c11a0212200340c11513004c002c001c50f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 987463821 1250 987462571 987462583
    0x3080309030d0f110a0f050f13090609020304170d0b0d0b040203070b030c0708031b0708130527070e0901080c0a090204030b0106050a0c050109080702010e0d0b01060e0303070c0b040812030603 84
    0x20280b41124503283c121001f5200752090200481045000281c5180b85c4102d210104040381c80112003084103d0b610a50101203000540703000780040c220040d8071229240f0724001c0c00500b030080714006150246280054400603900b0400c80d01500700034104010b524060050340020704968000d5131540c50100320009085c400c5141c0109003a00200108040318008014585a0881c0074480c41c1d4680c13250800015603003190108020750700c4c01d020081007a0420019001062014035200b901d02100315080c2d14005034010010b2003009100d40780078480741c2d01c1c8854980280003030400780c0a1014140b09010448500d6013001f284680100310800010301003000081c111251031401b50740f501030f00203044401c40c1718113201600c15801d000428003482120740003000210305c02d803201c1d02d80380018000e00c101310b80501070181488041c4401041094007988600c107000c10010160303464450141d0311a0407641d080d400c03503050703000c000c0350034403d24504001d00100c080c0b00c00d094070b00f1860b043c00020fa42d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 987465071 1250 987463821 987463837
    0x40b1e0705030610110610030c0609081e010920030106051e1504080f03030130200301110d050c0c0714010c150b010909020705120306030703080309030d0f11 69
    0x10701980751308001c1c6841495803031170800001e020b64100d4106601c5920781c040c4280401c0d01c07a0807171a00c00040c51401100c90400b19030012000d813100384540c100e094030480d90880c4202d0305540f9030034501d0000b403040310194150700b282840040b02048100a041c2100c0d00d0707401c02030041013000381c005482c00307004e25180300010301203c41308242c0360f090120007614001d640c40200544102000701004032000b20282d0b06a500c6039121a20300c03001c402e2012180134400740c22914400840480d240031800c0d40804148001c000d5814502900042020034210781c0100044004000041107072494801a406a00d40203822407084e14286013032070b02d41e5034542000d480341106c41c20041360008010707400b500790b0b030703095680290340b52001e1040c1040900c040d044001c91180018210400450141c10500c250703820960400d0081c207268520040398a07103a84050800c55140c86404030010015049600a5225010040c007460b280d14402201c80c041d01d66080c9a0344205040101e0300006000780300542e8121 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 987466321 1250 987465071 987465079
    0x210f030a050403090312030207050d080f070311090618042f031f15180b09010e060d0c021501050a030305190e03010c021e070e16030f0203040b1e07050306 68
    0x58440303250903190304c0d950303030300c01031941403404c00200c2901d80550240c5005801001074440b00318511004072900e60003160074448142c50a40440e44182c8a45d00c00c0411790741c01000c0c9031800f4030035030000301c1030b0301300d40c1d104040010840c89916150500e4041c5841000720404540c50020034840342c050000c0404040034510314020001440000b403103200013440031010006520311a40300e04280b54641000e64140c1d01142081c00004510303400c3d10f40380012a0140000c0d2030801906030300459590004440710355101c14140640c4c801425548142d4485246a4000b0407803192030b03603803007220540160300451140c4100c2d8002c00c042500308c01242c00a8a0000300950500e400801c01d0b0f4100031f124552980541c40d15450070281ca4001641c00c8100c10b0202c2c0301504000c440f0441c541d0b411281c01188190312050012a039007142519900c5c00c0c0c02c145080120b04d0340000f4411a049810407502601e66415420602083c00703e010001c40400e04201e064084c503103031602004c0e125205c0944581e0103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 987467571 1250 987466321 987466331
    0xa06091d030901050d090c03060c030c1107210b0907080d020a1203021b0601170c0607020d08030405033702060f010302060c0102092101051e1b0912210f030a 69
    0x70161903907101a148030341c007e00c2560340d1b40d1a03080000c02800407501041c0464a040390030a6158090b0b1024440a12a4401000824200346100707101540d0740709561f02c10030045030321000088400000034820750070701005040c018074101c05103140855000303d1000303541018043e0f0010449000c0d540000350300030708015a803111a400f0201092800103000070a500401c4004a00b1621000c41452102c4814044410100702e9004125142c825200300039407142c5114521400038443c0c0025540c06070150003030b28180441d80081e45403152001e00e080d00a940fa210075000a40c2104920015003100d904c004c02841c60845100009150180400380c86104089244465034400350111000d00c84003802042411070003446042c0700c614410100b00d520750a100c0020050b401101d140d4015081c00030604c03041d51181c038801203040341c40422017002c4101c104118023090300c1e00880910815881001003000207031280003003031801c081c40d180f901586010441000070228031800d42c0d030003540c01c00002030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 987468821 1250 987467571 987467587
    0x1407211b0504091103060109060b0313060905070807030213111e0903070b0405120303060d080c03041a12011a0414031507170105030a0210120e060a06091d03090105 72
    0x110040040e80401c0d403040c10a907801c81040f03100a0340d1404c07080e090701120083d0f41c0701c1c2400c03400d44280c1e014002d9041e01c24000103014075041d2139850029070045500041c0b03031b0120303110b10742450500c0d00074000c2caa10891041046092450118804d401100c00400901065071a0160903129502541410b075840c10581048213030200101e030031740200201120203190b50343d481400240c000340b280d588900540f4074840e80006003c000c8a12504000300060400c65407a61040701030b400c19150901c0030b06c0144400b04204140040e05e40c3c5003804280f41d191110501d56003000c0c401d1058000b8680314481ca80300d0058000f0a405842c01d899801710f40c000c0f10100d20001c246132004010310800200b1a070f40504c0040c6410054603001611080e00300005a81c0350b00070b050799400b02400003074102c60300c0c0800c50f80b41c41c480c0d1034003400032410b550003081c44aa040c50a915004080e100301c064103541c0c0c802000501c40f0f51007185400c1c1c1c88411042802c41c54411015120b01a200f103a034140140003038102 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 987470071 1250 987468821 987468863
    0xa17041e02220b0f0d0803220221060a090b01060e0303070c0e011809020a03030305090f0d110f0a0b0105040507050c0a031e181806080a140721 63
    0x250b036070008018501800c42d1854410750107070088100c401c2c010403441c5134031201d6003002040c0305e8080c0d401544191a42c3c541c1d0076501c41c003000c0c011001028022001740f000060380c96803610102c17599900e0f000c0c218004018043c44c20f00f08040c1c046034010b17141c20400d1000600115041c0c0c1110707142d042506099500402090a610030400d004044520690002c1141d45000614034162804100d0a001122002d42200122a42d4202c0603520503036001d000c00000c5d00c240c11561744002d00106845107405061980f42c60042c4110101002c00d80340c0194201c4413004100f007003840c1d40c448005102c071b585e580e11646c02041041c0030b0035000d01d8660001500351030007201101c50890042c011aa144031a5041c0140f0712903e01108600d00d115068201c0003880c460816260003081c400180035155192055803e41081110f54160000da100c150016092100744442e40c0c6072070148450300308884014102ca400c001c40d60b040310703041c40301d4070541c3c02c0300104160050300d04079440120700c0b081021141e407007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 987471321 1250 987470071 987470089
    0x8060906120123040c0501020f100b0111061612060f09050408070b1e01090b090a0e10090804050f010323041b0305011d0606030d0c1e080a17041e02 65
    0x40c2d8600d01d0008982003c3c01e22031039440e01ca0380c0141c45c0c18101c2c948034001283c444001c01303440c2042e58812480410020102d80c030801c612070050600e0414034010420740e03420310900f04d84030901ca802d40f18044030482d0304207940032903240c4890010050356091800951a40041d030045102050360341d00014104070b20841101c3c40144c00c005a41c0d0b007450040c2c4015554958002c9135200c1003410000040d00a83c2d03400b80e4080300200508224503952458164401840c0a0b0001e090603c2034541416a40265208a40d01d05001e4460b0036551406e050503c41c4080203800140d04052800b400c1c07501040390300781c80c490207100c200c6805803030391141d0801c110800c180c0c0342a928214989030700041000015480f0040005644107403045050302201c607251200340440c0d169415800c00407512064601c100c04040751103100351203240c03a02003c0c0d080103240704c40d1210308941c4034100040c800320741a048100100c80ca40f00002c400e001d46019078408080c00f01c03003e840c40590042c00b00203800c554ac0e50f210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 987472571 1250 987471321 987471341
    0x20717100b2d0a090603080307170f0f060a0306060b0a0e0303040e0622051302210d050a0207150c03140306010516230c01090b070b220606060302120106080609061201 73
    0x13083c05180c0c1c0302d0602c500c0e00d910566a81c1c0106091036000a900c5a0200300c0c107204920402c0d008029a490075071400d8003a10090035182e0200810398048000b603c1885504c01905616405039110150a0005400d0200c140f00c001c1c800e60007407004000130740e40304084c01c0d4040016a40000300c10010f480c01c1004802c0c1c400d410000398206001c0003445c81207032086103202402120702409001074400000030400014011000c80d8011250012105000c0e00007009001d066204840029943d0708036846030b000d0040c1448009006071100b40c05041d84241d90340c10504907a51640e146051030000a40320348210b070a0b004601d05d43c1000700c021b000b072120000c1500d0303080b080081c0c805580750a90316100c5c0c14103080c45000c14806440450419000d105651030641d10a8186a00e80c55184500c59107005001409040409110741c0d080082c10f180100310090003581c60158558864880050030001c0c142c100350704000b0b2050412665a40760800c01d82c00c50010380380785030706028030203449000d0b0020f03040d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 987473821 1250 987472571 987472589
    0x8061206160c150608061005100e150c0f0307050708030c0d030b1c0f17040509040b06212a03031b1e03031033020717100b2d0a 56
    0x100003d031780300d4041807040c499000750444004c405e0325082007041501023501501c00045036541134400a08151480028100041d04190b013001581c42c00a40340c03c0016084146e41c6c2c10109210080140810105002c1c1518802a504284845034215500c01c0551b0030901015216100490f103a2228100c0410504558507042c0d01d03810036042c223120401030f682c1c00301c59003442d42043da40412181c8085d281582d00040280c02a41c80710344500800e83e0000d4101c56201d10110000107400b00c4000d103e0510303481120150a101034082442514003c102480308501125400319012650340441101c2034070400d0304103100c87d241020b03015450312003920610b058914500411a00c07058001020b1032240c03401c0e85603c4a86030725006170800342e19180c1a482c01101600740780e507a801844042902e4902581c0c41120000380c0e9440c0b041d0342202c500c200c160529000704a080543d01c15500072803084840c00d4803440c01030459500000d5141840740114041920300400707000304c42e95a03840410041140074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 987475071 1250 987473821 987473831
    0x4030c09021801090501050a031d0a1a0f0c040e18030f09030708011103160c1a010e06030d0909150f06030c1b050a020402070201050c070608061206160c15 68
    0x290350880298000d100960b1414a001d103036940c00d61050030382c80f040d41e5069440038103091101c0010303001703040e140240c800f0f1000300c41c010006801c1c0411081582d1400b80040341400e00d06025140f5400401401c12400c0a003000104280300030b0080c1290115010320071070041c1c55981c02c07038919280100c000140054080001c40c17444002d200313009010071100403404c6c0c800d20381e503a040e1242251504140709a03400b4051000030040f040c800d0706e08500c0d901c24203240300c1c10610b9648502c414160340544020384c0702c8a10041c0b20190100e580c0b25486001034005010020f0ba051000d041c2e00c0d43d91146251f00354507010300d1b240f002c50101c00d080081180e01d0a0701102c81c0c0b5072030090090000c05881d00e0010b2070081e114000044a001c0d40c1c010f07190042c020304030040c02602404044d43c00610264180501085101505442040300200900b0940d980380721605040c0200b14204100941058043c0e00110511518540291011170101030724101001c00b41d20911742060f405000c1103100360898940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 987476321 1250 987475071 987475079
    0x605070b090f0d05030105190f0308090307030803072c090f180708010f180f0f02012d02010605030325140d050306090703020a020327031212060a0302031c030204030c 73
    0x31030007446c161101114090080f5503c0a02d140c47c0207440d00c9000c5482c0c01c80c07481000820b0040005109e05440039054030340141c0c481c1c0350440c644e40700f52240310020b049042981003c20030428480198030b141211030b407103499042c00003907031050094002c0049800490100d440a140c3c0fa151135004044142603814055440120768020011035985204450908411890400c01c41c001c03800101d0f44400d004000b48115282c000c0f0349074140804a062000241444000031702281c07030003500c89c80345106455000d18100707000303003500c02030703801240240c0c802c2c0810280310828250007010305003c4009440440041e0400c4e001c000012485444107019026103400302d2944900154880c0342e083d00c100c905030b00c0d642c4085040340300741508800160020b00841c09840500caa010200c85250640301d1010702c54400002d0070240c40c03065007452340d04001044040c21580311042503010404a500c84101d80ca550003098907002034903021100c1150703810001039514000c0e41903d014603008070240c0a42615 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 987477571 1250 987476321 987476327
    0x18091b1c06091103070f0b0a030f050103060e0f1603020f04020f0a020304060905031c08190e01020901121505120a060c03060501081003111908030f03010f09060605070b090f0d 77
    0xc1d02c0142e603940c081000410090400090030b204440c00300d64207040c40741c50880548203507000540c0120401d030302e41115550080150050901860041030005000b0400c118454542004603980015a4110030070b030140400080000b103045a80554914207a214220000f40003840740045040c2000307404205100c038250700102410540e01203032a40361071162183d08055445074a4480d03000c4484e40e504076035103118032030424a80c004440c10241c454400746c10a9400581ea07080c5004252a940401c0c40f035440d6900000340d01c60845002002c02c4504003000704011003000c0d600925029100d0b07840c2080102d60308000e50f03030170a50130038010040c00246001c001c000d0405841175034000742012002c11a04018090079008a0764440a103c0354041104140414602840701440500f041d0100000b5100014401800b098486544855036503040910b1003584c00619080310704c03407a1416405118481c0c004040303a01858002d0009185d81c2e0b80d00a02d40e24001541c400b000b4039001b68172a8000040d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 987478821 1250 987477571 987477581
    0x807030b040b010605030105060702130905060a020c100203061309020102031c021b1f1802090a020408070b130909170d09060b0d0f08070204060308160218091b1c06 72
    0x4410700b04448940d07600c0b81d003190140402e0041c143d00c0102005034100604d003d4500d0210344026010100315007809442d2641400b41c00c070b680610707203900041d0308074800d4401c4c090100310889404d0b04600398145000481c050049e20007100450306d40e907915017006e583c020402e56548030070f000a80ea0388011a40c088402a401024074484602031851209005960114900040076074030101c511009140c0d02e501009081103020004c0c20080c407103403003000758a40281c44c0d48140f03890741015a41c0c0b86000c2d100c51400026502224062505015220181025286000c1250b0341d10002283d036220b0380c2405070a0511104800c443d1100005404d502c1e44400d412161036940030341c00c1007140480b40c000b449100d5031051700081c401c0c002c900400740060fa25401800c001070016000041c903e03100e0b07070383c0c009951002100b40541052401401c0841c5030203a031840520b44090b10445150901c0e4440b40e60b036002c18500689540030707215510249480702e280b4001d07040046644200c1070606c0d0304080c0000c1c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 987480071 1250 987478821 987478823
    0x2703030e04050402060d09080c0d020105150a05100e011b050d0f1404120f05070e04050d0c031707110601121502120f07020f1c031a010807180807030b04 67
    0x200a448061054507103441068403440d0090300702841c3c03100305a10b880041c000a038040714062000d00030104c903650104800b030503a214640002034282403181e21090000c054030321040c4290b410450a001d6900c48440341c01940b949420045400c146420068a2000000011071802e0750480e00040a0110000e100c010341803268446044c00210b00b2812290801281c880141d4040108030802c8030824210b811882070340190700c0c0d07000d40103640d070380e031410000103902407145486580240b006101c414071230400480348505000b214101d450364054140008020b104901000391000980344c2c5004d003400180ca01d0600090328850341e181c2c2c1d505110b20088034000d0320303842c072015903e4944191300e10888000607502c40e07016000d039407101100c60f41020010404001c5019003100b00390359020402c0140d200c070814100c41caa000c24410300040c1103800d01c0a1850000c0c1410b0840c04450341c009486680003103462500034230760201c020340c0b20600c060641c086802c51040c9a03000061150042216000d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 987481321 1250 987480071 987480077
    0x3090a050a1a09300f07050a0c080609060609130501090b011a130e061c050d080c13030b090f0f030307030b0d03090e060a03060c080703060f1d07270303 67
    0x80d4503040080b40e540c1e10382c407501c00e10004c8040c0118540b2152042046007001018200302e14002c01013503541c0a03508120402c0b100c2c2c3d071100343d0720b0b410021003600f0700340506002e02c004d0130030307160081c41a551080f02a104902408818010031411452016548000d50700300e4020320000c010f6284c0098100024860307040070518010b916020342d0403040c00c0b100300010a1100040c2035091080004011b100a40800d40c08001c01e4452424090850050000036001d000988980f168615001e0a52403004100c2c0070200801c104c54108030800801c07000680c6d4005c400c0e00d90903075030350446e6480c10840684e0210380e032184882d03004c04200000000e51240616580500c0351103076840611090081c0d5620060110340e9000c0240318200e180080e1960001c0f004080c0b031038a035034a8840c80c0840c2c1600340341c2000900214208841240c0601a0b070004000c0e18011000143c40d0140700c101c90000710540030980b40f982e001280320340b032084024907100700714800449101c10311101e582c90b1001d02071000300c0c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 987482571 1250 987481321 987481373
    0x507110c0f0d0b07020109020d061505010507020d0311030f0d0504120305040b07030b271503120f07060209040c020307030206010b1207110a0c090b0307090203160503090a050a 77
    0x40d0500300300c01c000180e406040400600c21594441c0780440b00107007010119980c40c0175400240e0b0301d92100c440210b002c2d03400080c600c20710013450708515680b50001410301504000401c01600c4800c600c0300d01c0d5405203011041c40c4000d0700d5150661180e45c0594240d844003140c1542c415403e54030a44c02544100790181810441040a4003640c070704550192000c948a000035140600a402444030a98020310907026101c8a06031000150b1003013410b07090b482c9160741007044503c0707581441c84240208400901410703440480090041c42040076a00e5a588042001c10070000c0d541c040e80c4284800400c240032200f81840001d6494200c441e00b0303001445020b000041d010070b420222051030001b003180f0105035689400070b548150921802d8051482840044004949103003403507406860200300100b0b2516480c01018036003402500240030591040080c000350324070301c480c592a040d5090a0003902c030745e40d082d241d60070020104409401409003458680030000e2028041c0c1d0400405004c1d500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 987483821 1250 987482571 987482593
    0x602010501170a2d0c150c020f1e0604121b24020f0f070f0602031206220e010903080708040f0b19060312260c1c050711 53
    0x80061840302c142205074018441e01d5002c41e501200c100c03000315414501011078441810b40a103008201481542c0402100c2800d220200216444007034000e0545010001d000c0c1035000074226162005015205106002508500d048101c00d0381031110401400300d0b0700d0750390b640721a100a041c030320804c4880b50a90400d0840010205144206441c10421003610a030382c18041600102400b40005c0c0540c4521580322074502d4080065009074500240a00400c2d4540340340c58400302241c1d00f004080d900306202d5030002045005400d54000c20803103080c0c0e040b400c203000484400642e841415006410002c8443c0c0840d015000b103a0158481d40d038011883d9218a01202c81c0c1c401030b5001410030070303005204808a000c1030300b003030b41080b002000d8041900c0c203404500212442a40201d4814210004002d55035410078a4083c48850200c01c1c24851034050b40c812551200003003d00d240200c01080b03a025400000992078060060b070b160030030590405d0b400242c0341d00b080400804e007610801c0a03001f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 987485071 1250 987483821 987483839
    0xb19090b0f0406030c030e0607030903140a1706010905060304080406090b040e070e06210405060f0c0f1806040b0c012f280504030b060301020316051c0e03040602010501 74
    0x101c4a1841289441c101800c02d64200e018010b01e43c904c1c400c0603100c15146010000501a250159030252030028001d4450702e030103454001c04200c1031140600134041c155469401c4141c501681d0944007140306075030760342c0c00144d8112616801c842e80020002c4104010420540000c0c01500e4550700c503510300e942c0d1000155500c0c8034074003413841c0190030480800d41240c0121009020b2000082c10103090490354591f20300c51004a0854501c40c034007d00520050250030301640d9080032880c5040b00880c5040d40f40010144a210758094552400042c0704c0c6011180030710140244e03800030540307641c80359103000d0181e147d00660780750040765180241c100c48804809001e20035540d55100281c01c1c455107210b845079035030440030060071014603005251504451030801d0700400289a1205d9450782d05504220720910001000b143c007a81c0b041040c424561b1088008404805441c42c01c0341d0703030326039510a102c1c4100c4070440325a00e250078487e05101089010010303009450540d8002c05c8581c0ea030301194 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 987486321 1250 987485071 987485077
    0x5030703020a0b0d0e03130e06040e060c07050109060f06170706020d0507060906021b0d020a050c0d051504030e040b030615040e03040e091b0f0a090507090b19090b 72
    0xd502c10108001000740e429102e001e444601400140001c40c512040465411030b8040c00e02c41e501172500c2c081c14000c25031503400342904040305841c10080002070146850fa203040181c0385c0071104201068207010044c094000543c502c1d4009014400e10352655103480203809140180f84038803c2c1c10000b15a015000200201114026030060a6024400e003080d500350340070a41c182c070070366107400300d03100810110f0008000f502c40545820001c0007450041500b010a84c2181000f150400209d12011440002e1030344800c3c01c08881d182c0201610380b410340e140410b5520340c1400c3d10b0702e403401c100a140c0c103ea00561200c0d41650300340310030004a400c15481d10012035950035000c403900102912420320b40c1c070540f04d04803403804481c0b411380c4030280155500d0080b0340c000c405a204440d00c80c000c5070a02c1601400f02c1c81074600c6203904000d800000c0d0101c100740900e01c2580c4d131320400500768a21540d918401010610403c0d0303079030074003001c0c0c4440c0001c6490001010820840000500c50058011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 987487571 1250 987486321 987486323
    0x11122505090a05070909020f0915090a080708070e10120b04050f010c05030a1104180203042108040b0406150308030115080105032503061d0606040c020a11180c031005030703 76
    0x80c200c3e25400c1c806131390006d4102c0e023030301c0d22000c006021140068030b0310b00030100840c00d00444641c50740b5205017000300c500036a41011840c0c0e08080c50801c45c0440c009064819940180e003d40c1407643e8080f0300001d9074005502143c0c941844000c51406d116413523221a028038054029108915017240106003a15030111480e40011410800100b14070030700c1e48500d202c1ca100752001c5141503a20111210701080ea04580040168000280810800d82016402050120401040d03400e4485130b4041e00c01071004101500d020b20080000d0304005055121000703800b0000105c0d00c007140c0b2400c002c030244e01309008010a003001c0140341c240150003004040d040f104014003c2c900c1d00510414541004802c1c002501c40075903039000400000d4040c001c0850070310a424039000001c0f00040d103d850500050f01c464020b900c1c14040010480d0302044003000560021a2042802c3c0c447d80401c6000b0b6030300800890000e100411703c00100100402180600b4890003500819500c1e01d081644030103441c0302c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 987488821 1250 987487571 987487577
    0x90f0f0210050a170a0e1608150c04030807060f11130f03020609190b07141504260706021908250e0102030d060603060518010311122505090a0507 64
    0x8405000a41d0b1390841d66480b0b1075980f004682440f0b400703c01807500302c1c02c80303001c5902c1900140900c03001c0310421a22602d4008a0340c0e1840c02d04020400300703581d1103030f4040a018a02c0010b006000d00150b604040d960944005040010000e84458178132306402049800c011a0841200040c074140b980c081007082c2d07600188624509001368042000350740001c10724080100c001240000e0700e11501c0c0281078518050f8140d9098800c1050f803140c180754a0070703058004c58111105000c049a0072245010240c8024040d0111407244004070041602a203030b00144003a00002e5040700d80021030052110450b1162202407168a810204400400400050649a1440e0b507a1201c40c9482112848070385d11040c0113480c0b400002c60089019206290001408640c80d00010001030400035064085100441104d05095045030360307208543c4a02c409207441141400324285061000b40711001403800d0f0400314280c5090000c90402c480112845682d1144507240c00044410340c80c4d0194902c10072081c0d0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 987490071 1250 987488821 987488837
    0x503180c130b0f090c0d0209131802040f1a01030216170c010e0604030c0807060b060339090f040b1207091b050a1409060c01020c0606061c050604090f0f0210050a 71
    0x51006c0c0c0080d0030035205e4940c4507282030841806665684a000b00c1c52079a465190880070b002e00610043c6c1d04c0143e2041c1055140c001b0740e03125840e16034a0191402000d190240e42d501201800840039580c1010150006030740e102c0d42c414000d00100209030040c42100280202003c440c151a29640e0407503002e00410b55840d091800103440e10010319410b845000002060041c14000ca48580c2049414182100f8209000c8150b501c448100c07699143c0e44d0388000e03140442115901c41c19002d0711480301c0c060781040511820b2503866400411070018060b02241c0f180c03085148291b650a000e00c00d0b04555803422441c0c1d01b85110028800c140f443c1951242490941040c0e4112245411800daa4410072400e0080d442c1d40d582d03010040059a0340d6100250b140c0c17403030610140c1080d9024040600c900b00c108604001c6010403500045003819581c00011a07903175580224000d0b03d03801c0d0000342041c1041020604011900c56000009030007541d0b81c2111802e4004d040d10540b00f400001c1000c10703800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 987491321 1250 987490071 987490087
    0x1e1807050c0d0c1b08060406022a0a0516050a06030203220516090b06030c0d0e1b010e0901030b04031116090204031101170105130b09010807240503180c130b0f090c 72
    0xd60001c00d0807801e001c03148051840d0300420002c08002d100e052b80b9868000c0e16a503014442c04000302400f44030301d41d000d064050700c0c0c000040c0d90209184110400d01d500800000c000f131a42c0e580010075003e22181c1450079600b103251058542107107440c8140c0301414090007060840340746c07107038084002e40070309100e203140c0701c0010105050700b1650f100365a5507112480881d60300d0042c080325040c9843c40303042030040c1546000140004240380c40080c055040c003001000424020543e640d00185c040c10065084028071071200c0c2131655402c514124100c3c4400c0002e00390305954001d1003128000c600d1035949a0889004440a07200d581c41a0424a40d600c01800180b4101e400014001010640050b02c0d8042c440030400d0b11100368002c0d0a41d4119a01c10481b25000d1840000c40408968804016004400000e042d030301000e02101690a0500319212041e50200803180c46030400408070180c95100e0703ca444003510200034058003500c0c10200002460405510a0340100c903c0a049410000d003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 987492571 1250 987491321 987491333
    0x3070201200c04020c0109060c200c0612060a0f0602060f060409020d081804050a05040605090f03161406150109050d030905040f110d0b1e1807050c0d0c1b080604 71
    0x5c11041103655640c103000b0001030000c1c82844640581f9480e511100205c542c0050504142822000381c0350b000050b54506030345d2484111014150456104003007922150003046d00458507400c944244803a0601c08200c2039000039401c0d2090400381d985a081da0f40702c0042c030040c0c8611440c001d4016601c8000840000c110a000c0e06213558030800d64403404034070b100040c084c0d903020350303990260781d50340d40038041442198050700da40400f240000340851300344021625528401c13001200300740300520106c0c10800c04420081c51118000ca0300b11455030500165420005850355951404200c583c1030016540c140404081101d80d00b684820081c07520f014113000240c07182d03245030417480c0c1c0e40c3c062002001e51a44041c01c038035800c0c40400100455100d082c02180030000c19a01a030301d0700c80e80700680c20396a0b2903880c4036101e05640140d40546074860159140c1c010f200c1007104500034000000091684a940210b40600030100c0039002c140c074100c1c00c10091200d000d07040513600010700040200751 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 987493821 1250 987492571 987492577
    0x60a0507031b110c040c180501181a0f0c0105090f160603270b010614070b04140a0b16090509100b1605030301060522050a1809050109030203070201200c0402 69
    0x420f0003562200c290400000f02215070a07030000000c5035001e4100c1c1100d00840034480d0186c00c0c2801c00c900c5541011040050301b00c010302c2540400021010240301e004156410341c1c01603d034480301183c50720fa17100c04240c00b8000841d0b00307101f1445545000c0804040018103610104840220704403442c1c10820101c01402002c89804504000240030801c0c40d80c00c1d2a030643e010380910388800c2d0a5040400092405282c1d0003003400c0f00c00c040c00701c10041880360800681140e807008001480c200c100e00c01074100720a020b80a0b00741e400f0042003283c00d0120421841156586944985140340c413581000300043c4140c0c1c01c5000b110741c002e02401800f8180001b09841c0c1c190990507040303142d80ba074505145034003d0f0030450010701e000c510721a150f25511003480b21414541d8036020051f007454042140c161b12489801031001c4500e40420a0348403a0f440390300c0300790b007003002030002070310f80e05001c0d41e41e40c090076040380040c540c813038900301241070012540a0710744081c0241c09186c45280400c800380d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 987495071 1250 987493821 987493847
    0x1e12050a21021b03041809020f040501080304080f030c0a0b04080f07030f030c0309031e0c15091e030206010303201501030c060c02031f0908030702060a0507031b 71
    0x22140500910707031401045100c0303084007006840940e880307015400707450096072900b10101c5954030501051224100f4405400d802d8024240f002504a181c0d000141c08012100f01e01a00035190200104034504040002c2040d1050203003260001460f04505a030f0320320a040c4110800c1c0c0103281b15200240c20309031966089405046030b5814124401c001940c2c60b8080d00e021800f2614005403200c40325054054006540058181000106115200504106203044410754000429441d070741500b400b691142078202d0300000304112140c96249682c0042160810540d80500c60032560402d070948400310030ba845070300d540502516465640c0589082c440e10090080500c121580003072441c0040000151350361014a20000a525600300001e8505d166045403040007840030342c000150f1000540c442200848040c08000500d50001d110005d1000c030303d0003014500c00006014000d03a0006940e40a02c4501c0003c0260391500038095017215000b4440c1180ea1000041c81206280148900313441d078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 987496321 1250 987495071 987495077
    0x90308091e03030a180e06130c05040f090e0106091811030c0907020a021f140f0f16140d1d1f0c031d0f060c0f01020d091e12050a 57
    0x20300c1c001c2000038119041150001c0c00110900d0250200c00d0800c02e80d0341c000e0170900713814550750600401085525403400c1d04007101e030340c44002c400c40061103a411240201401c0c01805a03454036440020042d0440901051503076003059804030f0141001c1c8141d000d804400b00001083c2c00007580e5049140da040700041d50305001d1400c0881c0070752111100c0c0380c4200074a9010342035600070303031041103264407407402404000c1c1a1030440300140d035001030303281d507420380501c15054460b1411445510035100c0d21200d0312407204040345080852001368200305120740300703500341290741c2441030189a03200d21401c0c101001902070b80c04282d000c00c0002c0b0040c0e096074041c000f040e0555104183d6100c94103009500c10028921042410505501c880d600c1090f00c04006041d100207150307000500405050401284120300c001440014558200460034101502e08000d64503079040141c001c0040c01c1c10001500c0803000c445200391080150036094050642c071240c060045c462503501141e05070442e501d80414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 987497571 1250 987496321 987496369
    0x315010f231c0b0609012a14100c140f120103141203090606090915090607090e07020604030e0310050f070f0801152f07080d09030809 59
    0x10103901c040310142081c0c00c1d48107280d49602c298802c411001100c0050a009072900c0491480c5503500703c1205c15800c0c00f403074416801c1d05445003443c4521040700040100c100500307088020003441c000d0800030034201e14165442c00444a2400e42a503100c09569030009049a0381540740021110251000ca4568402103040110880e08120701440a03007045da02090000103484d6016001c000d802e401c0c1441c1c5840b28118205200d002c0e5232030001800c45889071401c90700040e000c5000304401441102a00c02170085410f02e0b402007611340b40309454940000e0700c155004510403060004280c0610020360042000d565151030440c1e40600342c0c04600d40c540101ca504020160a40c000c0a0040c1c20200380701d203071401c045102400720207001c1f0600b81803240720700041012440c5011081d43e00f851605019a4204403801582180c0a00d48240059024441c02080f03281d02c0009980c81034070714074800c482102e094070700181da0f0005c4910004144090411101c1c0c12801c000c04030704010500c440d10508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 987498821 1250 987497571 987497597
    0x31c0c0309050a0f051218120c0607060921050901080702031603080f09060403020a0b040c051011010c02010219140705070e040b1b030406020a0207050604060c0b0604020315010f 78
    0xf09100d84490181c0350100d02c805660305105080c01405030304498a11051b191965200b00790345800180410b06210ba00000c4c00b8030001081804407001d918402401c050780d802d968a84040202403080041e07400003d82da203540340004801c039101460410540751241410703206001140c840000405285c2113020901c0540d80c2c49039501d081c00c81c2030b8442c0e111882030345060f041103802e5400c003c2000845501c06810700000c02e80102c0c91600b4a500040b224102c0ea9a504241d0000035195022a801c150480909404254041d1400344841000d41c02441001e400c0300c0300300c4c04d07402a2040909808460b02c0d80000b503a00a208440300080f19811a5013000d00e60f4603a0382c2889013541c42102580d6441d000c10040080410b40d25610007184207884c0820b01d1340a0240a9070700004200030a00b0760b000032000801802041420010f000081c05540e40781d840303190082031140d05038001c8442c21491404901145400d009030b91050600040280c070100400c001119004441c541d110700f0300541a803058 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 987500071 1250 987498821 987498823
    0xc020f03070b1b06060415060c031e091707050a0527090c0112140708060d0210020f07080f0a0609031103181507020a052b1a0603031c0c030905 63
    0xb01103c00b154204610852451100d0700b054001402d00780705130300d0608040010300401c5000d0302078403c40d2600381200e1019240a46403803040400d51010320342c0541c0c0e00c241e501c2c0c1c054030400503540f103400c0001c500401c503807103031303660740c00d540a0780c0c0c1e00c200c0c2c9070b10500c89810069908803210001c1d01e40b07504c50448011540b0711000094030404c10707a07005844000c00c0c5503040043d440d2030101c4c980040010002454040b40c0d0a031000d400182040407810100d550355a1310740d00d854619030010450302d2010700003000a59a0012002c400c3ca1901a821000990300000b2840342c03042c0001c24080d0a070300c0180da80d100c0c000c10847c0400c40502c11040010315002400300003400e81e2020b0410715003000d0760040d04020940200c0c000030a20392000300400350050301e84002400843e842030b030b41d0002c2c00d14400d4805245409040a20310f00e0701d00000c1e4181806070a020001c10300c100c0042c0082c0c1c68550310b091603124412050302c80d01d0080c0c100c0154806a40e16403081080504520740040c80b00d000381e41362 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 987501321 1250 987500071 987500077
    0x340b060103110714060f040b061c1b06030e0307020a03020d030c0506041b09021c0c1b030503010f06090503030f0d110c0a150218060c0106050a0f090c050702010c020f03070b 76
    0x2590703000030313825001c00000420030034950072a1000301c0c2d00c58545090f6440c41440c450003041c1d24041d204c4401118000a90740d00c1d03500b03404c0e60100e04001c1004440b002c0d0103003c0660322a40d000a810035034510003140020007142c1403640c001c0c05084c48242141c00b404401007121740b08030100500309849502103102400342c14000c0c0e10030040d5203403800c1a40301106804505800903c8a00e104200984001805900320880032041e07500c04608112800000e6a80d907c00100394420b40c079050145208043c0c0c4003000358140e84243c082c800c02c00d600c403001114510507a000e15609544204041d00d614203120000d800c0b194281c400c04510103180c1180414580c0224184401640c02468041c04100550020700c3c03014000035030071410301609440280742820020251406040300082408070740342c0c01c0d0001c90140401500445010366151051000c48010b48900d60b40c251500c01602c019900c102c048a4001d90142c1d100a5042003540800c03c6084a5221030395043c415060001404001c1310f002d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 987502571 1250 987501321 987501323
    0xb040804081f230708060316080304090609180f140715080901091502071104050903120708060108060f03030d09030504091817090607060f02340b0601031107 69
    0x2c05000c5115008821003a2480d07405200c0c1c00c0d08082e8115042c80c2080090580c1c0120b0a2404210035220100441e007407842140c8442400b03420068007080345030001000708120703640050104507260303444d8a660101c1e13168035840c15034900e07410300765408186072040341341003140154884108001c410300e803607140c261160301032080c030344800302c4080449400404155014071110020301448030544c0e142042d000714641c00b05c5400f44e02145c4c0c130046c0480c40649050017200030303004000034241951130a035640c0095440460b0500640001245248184c0f0781600880060310351070001c1c0c03104000c000c1c510346034141041c1c042c401400222284841c0d4007920103e5400380d19800e58540c1451500d0081d82c2070050300041e010110a41c0c4800100d00341c5100c0f140441341c0064a489030002800140c5610540320094060740c2085100300d03a007071507580145544483c4c820104a03001c14203d05a042e801d0840c402e98458110550810200b103001ca0083c0d403101052400040703808a0851103415034200c158 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 987503821 1250 987502571 987502603
    0x7170d2003031906080109050c040221090604120f02060105010e010c080d05040b0a02160605130804090c08070f1d0102160806060906010507020a2903070305070f0e06070b04080408 79
    0x42400f003996001c2c450440a048054000d01403003085458250340c8070395460000d405290300007000c0e994010800c00324030002c41340480c074081500f40520203944e90741c0c05a500b90341c05001e2070b03250603002d070080b46581800c0c20079402a2103683e103400c0065170f0184044c031089043c09401507a25000807407410040c492048109800655410503007030180205200518060b241841000344084805003014031300f0815511160104844d80d90500b0301d1145110901d004042041c040f8010400d00761541121160405503603030091103a5888208540b0710030100c404001282d140f8850b4400351941e5402c0345800881801121045168180c1c40300d11030b603580d0301031035a0b50820403d000080c85c00c4051540c01940074608141000300703d4000030050102885110020442043c0c489641245e0f0031001c20419110b46100b52646400c1c0d01c0a0081d08007103e0708000140f0b840c4040200da0300452a4004081d009013009040059541d207450a545002e042a0703440c12080c0400180072070104200700320200c03c09 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 987505071 1250 987503821 987503851
    0x13170306060d050708270703020f030f0d0c150606050415030608060c0d200910140316110d021b06071b060909140a091a011707170d200303 61
    0x204012040d2010010070f44c040da80c220360001b6142c0d1000038108150798040322a19548918103001a15094440b0207508440c0509181c2c2c80b001c0341c000c1007105040e400303546c3c0d040c115108845003c0445801d4012800440c905120a016507982c20201503915207060a000466030380711350125140c040c0450703564008900001c2c007850b901c481c074043c3c0303c0180081130034465481070b82d554117000d40c0100d4140d14005c2205030001103403544540c8580020016056450b82c0e241081c005803a202032042d1000c6011624210700415424800689025000b00380d0707024003004e440c401e01e4002d40e890040301c200c1d4094801d000c11800308802c0840e4085240d10003104036541850547e000d4462002580304518080c40c02403589002d03c0d030400001d80c0081d100000042020b03592501c0700302d031007000040246884046001286048000c800c9454400303102d01100e00955907103c9070045506503200407101350b00f1804441d090140500b20038900302d014043c0e40c98040010101d0300e03185810845a844005445d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 987506321 1250 987505071 987505081
    0x80a1d0d0b1605180d030215010e01050f060304050627030408010225030c080306040204090f0e0c060f1b1e01050105041b2309040603030801030b13170306060d050708 73
    0x20482c8485002908000c3e0030900300c000030003a4000901441801000c22020501c10181301344500d800c655058a0111a1561184620051007200b402180e0191202640c40011460503a041c0c91080b644000140100c1c0c0e1505414800224504046141c94603510300c3e980d074105090001d400070b40001400181c4458800b1598808821040d0441d01c25412020000c004241e022800801d6650021041c2e966600c607070000c00c00074800c940c0b240c00c00d1860954900a001c40c65004016901081c108a13800400701c0300802100384141c1c05501c081660400071781b8000b208040d0741c510104c0e003000548000f480707a80c00041d404407092200c83c05e00d9641d0700052050740307098802d00c0050b031564024602543d0302c080000e04090940d03135200780703940d000303040a00b003840d0710074125030280101030000c1c46031550300e24002d0000b0000b8042201c03c030003030a00041c00b44180c805004580c0b5006240c0380e0304c1400ca150001c0700355002419840e00074004001500c4113141e50b026560140c900c503a0b440c062840c0c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 987507571 1250 987506321 987506341
    0x30d170a09020d0305030c13120b010816180b1207080609030a08010e0622090b06061219090f12020f01060609090e0102162d080a1d0d0b 60
    0x200601214155180510300c5025031200f0b0256200140e1605140350b0700e407130b4032070705040ba40518402d050b494261044042440042d4250380034801c1d06c98120000c0d00d07600c0c0c1c1801074440034040c80502042c0b0300890104840c00b51040c0c0b10480c844070b074400081c91000800407900d040301020090395035500c404020005100104046a404640100654200412070100030100300040c803c1d400000c414602007141c0c0c1c0d441a41c85403403a280440e08032170104400e44a10040d110041c0140c0e030b01c440b0400000e44604005084554111136005c0f6105c8035918601441039400248107841500c82e03580c2c00707140000f03508412845030b09003c1c3d502c4507091981c280d0001d25048503c48040c07226410701c501045229081003041307080d0b031140c035804240110324070300036402400b80c40f080c11540c111414a00051000b5440d020b07504130351b403104a2801d40440c0c12070585540f0342c040c0c010003200080120f101c40a1146000034101240641a41c0e401070012000803d81807540006840100800d0305202000c11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 987508821 1250 987507571 987507617
    0x30203010302100e0607080a1b05010e07060e0a0506030712020304210e0102061b0706020f0301061803050606010c020114074e09150c020310020304050c130b030d 71
    0xfa03e4942001c0510507940810310a0050f440014031100d40442c0380750b0100c1c09106013040f84468610040007924442c208540a00b482503ca5455402815804291a445140d140c0d60012024110184461404040c800d41d0380c0014079400401070759483c88180703000d21b4001140201e01030340c018014800e01d40b040640c504031142c1c407241408680c002514050340c020603001e0b0b110a60042d884002c000c010b024140c1c91141c2e00000f40601d1000404139010b0045c4030155040e40e605d0360b107044520704244082e1210507420b00002d03120741d00c940001002c5621541030050301a10601d410503000b010b4143c0c080c7c0603041168112850280e8051750805610521a10f40701441c1c4070441c40708a00340c0c000d1780070646228510450340d080d1241181c48160740207440d00d1000340074918a40d98280300c50007004000440141c4201d109015208101150000d2402620f000d6500403000d08904a1880300f0400c4408180300c0b50100c0b56140e0404400968003804000340300a030544581104038220318607400080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 987510071 1250 987508821 987508849
    0x7020f0307030e0f06090f040b0103110a1206050319080c0111040803090907091d0414071d010803040b0901050d091b0311061207081816031b0602030904090c0b0703030203010302 78
    0x16042c84480306c160740300d04009050800540e000106001440c0040b400740c10412403018650000140031a070303e59100680b10000483d50208000c0341307844004051b29000100803e88420300c441c03401c200450013210040682801500c0009a145420401124650002e030706c044515007001c11405014203020000e103520510070329080402d01d00740301c5509503900f04c1002c1028000d41c034600003010000040513020340110380c2401c40d01c01d569510354241e000c1132952400c0014045a20001614200c0003003a10180d4049464290600e41101c0044a064104100d0420983c1d00e9010560200e1240880f228082c17420051450f4a91708600742007010150003201a0702550080210100c42404400601e0304940d01e1718044d021034540052a560840c002000380703525000380f044400c03410300c1203030041d0700300d9100380f40c0380e800d00c2c0748504603000103040d510424015030020050410a0320741a400260b0251068810440481c5c40390000c2c213464001100850200341d00000610039803803c4900d1000c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 987511321 1250 987510071 987510079
    0x7060f0b01020709091e080c2103072f010506010e220b011214070e1804030810030803130317040c050f04020f161401111207020f0307030e0f 62
    0x148840c00000355121024032074455002d82e1004660204400070407903800f0810305a01e412400701141c00c003412694062007015585110b5440021047ca01140c00003d120408504403411a540c51005a400d4003411200800c41d80500310b200b074070100466101e420b04d141c04030001819103414800581140c1211b00e216100d2404c81141c1c0d0300f001c00304544880440c0050740c000c580e0300003a00040e518000e1180f00442114201030480b0180d04005c1005803141546944200405110409001e03807101540500c510007104c04002802080c02005100d03000420a4009000b180c0c0c1ca03156881d1070f400a8a0f0750f034101421500020078140e201404000070959920514400e05260b80c0350854888035100d210301800011003800d82c66692503054a8502d06c1c102039540d5198441c6100402e07801c2d644004440240c1d20154607541201d05225007004ca0101100c9145410070030080c0ba11040070083c07000c0114030405240001404051014040861103900d030003801c40380072070401409541003c002401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 987512571 1250 987511321 987511331
    0x305010b01090b030c280e130e0a11010527121c1101140a0504060f05090709020f19080a0e0118021e0a0b070b0f250e1507060f 56
    0xe043c07104003240c0d049140d0001083e9181c0c464014000031004401e9071181c25200024074804e440d40192440c2454401150701c450b00d00760300030b403174000c45524170640866a440a0301c03050000d809140d01d4510444141006402c10700180804034201264031802510000105050109401c2038141c9144882034203001d01140115075600400010054280600308240c0c041c060805030380a5125549842560396600c400d49007482550300508004d9a0454144e460075038025a09071461050502501c3e11202401000740f070640d080020750800e4454880402c010001400b40305106110301d9021245502c03103054074500003a0150442e8400011800507904001144040811000e5034101180d8115000e5641140c01450039401e4541a0259074002e4001d031008281d462608001e400114418a40e10140f40e803640c00802c111071081e6815426442c0c035030940c041c0c410300d500e560046182c2d240b908000441c1c0340750001e21444503c0c82c2c5400721200000e5410300f401500d00490030105004542800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 987513821 1250 987512571 987512579
    0x9070815131e120e0108131110050f360d080a0210050a06140607020d0602031306020d0525090e07020705030a0501020a0201270b2e0305010b0109 64
    0x550301c41050790040c144580006502d00c004154204903110582044401009032424003004e0705405004259a012516070000111039175400109140c2199000f00a05040c4036400705102509689680c00c40601c04184101c012000c40e50001c1c00000100403440c8620300d0700d45040c46980c201c01a448008403210301c84101c0c55441e8403003c1e054041e40300345c0d04c0b503441860400480c1003880c140300e066502c50400040c09084603036500844290b400501e45c2a0842e000030042102521540d0030003904000401403200120b815540034560200980d540818002c805a80304006c07640404070304103071140d440d8140716208101c62990b0801700c0c140c803109001c1040d40c6d80098500b0041d4400c005003c0e00361000035980c584284403030b1004100c040c04481c0d0445030740c90601e001c4d40082104400543c40c0150300d01000c050000c0700707001c02c42c10550b4804807007050345541d2064134008108085c01c200018a00c0541e854954086059149421010440a04610b8080d0950b085010031a040010821082c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 987515071 1250 987513821 987513841
    0x501050c0601120f060515100c0c30050304030b0f010501050d0b06041a0714070f060c0f29070302030919050f12040303080f130605190509070815 64
    0xa0649008154200e183c1c4954606400341c03203025000200910705120034880c80d11101917001040351411126507032200f40040f01218240990740c805013010304c003110100714044030780045130071030a42001c2c103070003688010071510124540d04404540310703480010204180005840c03501c0c0c00920301000a0400d5140c040000c1c0280141004107000e613507250080c030707039680d2391004441c001d00c40700b076000130703043d004a82101441d00880d0080c0d42c00180000500c110110201d0040c042c2d800701c2c2e0719001241d08002084030003010144048500c4048001ba040102d4102d5050002e0440522500204180b4200c40701d11044c4000e8154000c0c54014401e1050180021130600d0b03800f00b40c0e000411950a090400b503241041860341d9200a00420086c00da0100e4440014002d407030080d00c0d1005d4503200e00c2500f042d005000c40300c1e003004541c0190791000041c0c042d00026008000c6140941c3d00b2001451102c045420640d0884041c0d8030603030b0100000503091264511405910308008070a291400c006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 987516321 1250 987515071 987515083
    0x6340302070602012909100f0801201e0705010921021902101b06240f0302060a120b0301111903050c040306050c071b0509132a08010906050a05010501050c 68
    0x1c00d121b80c08800004840c40700300c03140000145a0401b00c1289141c7e0b466401d4000c00a4139060800c90801540b0403a050138180100e440c5c0181840350702c1d0543d200c0406c61604e0b50020b22049803039548500c580e10215040403008004240301c41c020750000700c40303180003034946164000d1944080b40d030f130094040540d0700e1041807c18a07c481c01d02d01c007081390400c03022030310300032140c001031006240090000420300c082c19440440c612400f003034548c490300c3e104000d22280492000a500c40310806c6a60041807150085c1030b044c2c40e080c01c0200d04204910700003409e481316440016041c180128000c0345030382c54a62003000120550804101e070742041c4c032068100348100d0102811140d203507004202040c0640044030060394000400403005007100c20109000c001c3ca00c2070342c0c031928207400401d034400c0d03400401d80c9185500514850104180c076a0041ca90410f101c801106248801c20018115a0a00882c1480d40c8242400945850000320a1086902c1078008a040000601c40c20141403000142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 987517571 1250 987516321 987516401
    0x414011703070606090609060e010f140103090506090c03011109090619080a0c090b0108010b0901032c0a050706020721170f07020901090b0634030207060201 69
    0x4000300803201009501c1d41c8560000109020b103084d000207040c0100358003440a990000748144841aa02c0e1950015035000780280c003040c01d40d002081010541715991641d4180060501054688254030b072242005000c4a400c0c844e1340120100d030351989000e00c105100c0d131948500d441c1c289981358011038a625401001c0c2e17405250a1009003015030580d0705890b00420f404011181000d94614011102107407d00c5082c400d2820031024180e25802001d64034182c66010788080e04100444004401070902c400c544500a030304000180120125500c1144c0140282001030910407124a00302e40390400c15032004003103402a040a12801184c3c014000c03a03031654400305244402d49040500b000d071190b4034098014000010340c18108290380e0098207800d070080714101041c4c1c3e60394655006036298030100a40c081e4041101096102c484144014108040100a144141c9901e00304034050501407003078001d68030024080002d950f090051650780e420032801c1c002040c250031589120050340d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 987518821 1250 987517571 987517589
    0x1806030603010f0c1e0201020901120f0e0d0309050709090c1502010b2205070c0b060d0809031b09010f0803030103060b030307121215050609010c150f0b0906041401 72
    0x120390240c1d400d4001d203155843c006010001c00d86592009450f1441c0d062151000c9402c1700e184a460034010b03c203503200d0510686441500010542d240c0005100c4134007440c182983c0d40103c0c00210304200300c1e0012458131030301c00082c110b03128206103141000651000b010641091107c00c00a8020007070341040700c03501c1000c660801c41d020b800340d001d00382040d29640c101c160b810101c910500b81c1044910800305005041040f5250010101c172280141500a00f104440c140840c80a00300fa202c0c0c5071a060155590a0501c011000020b06000d4a002c6070310794400014042c85d03292400890843c010024056403010320352a040711952030b4001480054002655040b0346455510140104c4441ca54880c440015568a0034030282c8819602d10814100b00c1c9071070900d1989402080b003c10503140000d20b000c0c201a1241c004407080d188038241110220200403603801d051421340502c0345400182031000c5003540700003041c0b052180008060910407810038841080402c4408400350640325444 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 987520071 1250 987518821 987518827
    0x3c03030a141509040c15050301050a21030e010c051005010915120f1e12140a1707091214100c0e0405070e0d0507050306060d0308011203090f06120507051806 69
    0x814030170b40e58022540030f501e28407010001ea0111903030040045068070801c6407100359480d2104400f83c55a08480c42c03c07ea0281302e45d0f51040446c0c020a01d403540741d80c0516010a05400c1d41d03a0f114100700c0121005070300c03540c0b101c00504c40e0011502a01c008054501e03111000c5501d00b9400c030500a20400003e0a620401c54141c030500c01310107840310308404420448510300c0140d140145a0701e40c09140500011500d4515a0355400c51b00c04440031b01c2055036600d4285030b140c42a52146100180041c402c0c001c0302003000400c41588800810b038140100c16905850040300091420214881c171311400c042e15028a40c0081038019950000b224400d40300007070503599404050780e0340341003c1e0001d40e01495a000c0c2108108000802c80180c850503070958005450718010321258403c0c41c0001408101a5001400b00c000c0a580c40b0607482c0c001c1ca014840d295441d00003044040b402d800050004980c09005005500a802519002480742c07502c40d1900008000d0402c6488004000760322401c000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 987521321 1250 987520071 987520073
    0xf27010c021b300304030818010e0406120201030e011b11061e0a020a0905062a15070f121a010f0905060f0c010f0c170106020f3c03030a14150904 64
    0x80082c0d0b0301455007c90000c0c0d03107029544c038000c506004488140c0c00500114405080c60425010704011981e654810700c5855085600541c054100550312a03815980d5038400c0480f1a8400302080f074040507a00c9070241c107028501454200030b401440d03000c1c01c0e40005003000f289107003181303865440240350b50016140c140c6800b04403030448051f884103600450106152070719451312960a1804801e00400e180d21030310300b207440c64030f5541c424011304000f440000003074011409443c10400004480c0303007690b4080c0340c41100f40110340c0030b080200803070110788000c0c801a5800200d04400e1002600744440824034190024040348141800a016034402165681d00c0c13000c25004241032021030481800791190061000f0291149000c846d81c0c0000c6080000072141c0c00030400da9080035420029204004101102d6a002c0c0b941c41c510101c4060800000701d02c07130714401e405481e40740c000303000b039556820088608000e80301c420180c00016458081444510341c004903054411f8031081d500c04803aa911 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 987522571 1250 987521321 987521323
    0x70c0c0b0307021e15010303090807091b0e180717070201020c2104050904080a022b030908091e09070e010c0f08070206070503030a140f27010c021b30 66
    0x700709856621740440c0d030004820075810081c0ca03000d0341e0040e01281c41040d9070300d40341c000707881001030a4003a520f0207500300c4d0102403040d4100161440301420b181d00c501502ca503100c01d40c410403103254000504a114100b441c108030840103800407100c2c07000398104249200020749850540000c81d04c820344045d1508141c40117401520010000140310740780c0344c9003500b003c4509501c52403602d00103014404000b0400700d1032019070325a5a68070701403e040c1a10401c0242d00601104a041c0c82150f020301182d1041d82c0c0b00d4050b0104003402c0014000114850000d0100442c2e0242c003090038071413011441021030740d2250305462180c4d00303c16401100680703030401006511441a0103500502c0028501c411300c40c0005c0154014055040200310310302d00783c055068078190681d4035948804404006c140b20755031141104002074041c280c40c5114284540560b42103032900320307107240583c11075402e00c4291032941100070440b21094841c200940388100b10418281c1001034081c030007800c5c4031b80986030000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 987523821 1250 987522571 987522583
    0xb010f033203070501020d050108030f0d091106070809030d1422030c08071d16030203060301110c010605090a020a1403090115060c110d0308131109070c0c0b0307021e 73
    0x14001d0142c035607416060034094040c0d40300b49402480a82000c0001541c0d0100004031041011090012824101110f00e02c00152900600696008244820503411544e0782c100422210340b00e04402c660354804c031814141007524140152050207003000e01d011081c040982160490000d00f1110048440c050420400c160b030581c0001e0f000c016240d0780403600410000c1c40c207040da000407400090440030781e285000301903400c8480c440741c00002041c050015000350051604880014008030f10080c0c0900d95105a4100c0d5810f03100ca0303912880200481e0801039481500881084410b6103080400c3ca400f6001c10761032002ca9104034000000900c6840c002e500901c0f00030030905131000241c0c0e403804010300c2a80280c03c00d81d4460f00300004a0890325002480580981d8551140c4040365118800040c29400705007040e59042d404060115590791040840351080400c1d896101e030026090500744034515850b005503240c2101041400402e0380c00050360100c1d482502c0c800c104064040140c54240a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 987525071 1250 987523821 987523913
    0xc100c05190b0a2c010e070603050709080304060f0c030302070f05030a0906030e030306210105100e0c091503061813030201050f1b0d0e0318030d030612170c190b010f03 74
    0x4050380c071000c48c0c12513140d04098041d11095407440140c3c3d0f01d90341d4030380e02c82c071a41c4030b02008141d8016500075106d0084405c85201070003420018141030554484000b0016091812145030f000000c4a1003019040200074020b030015140400800c00081c0308203a0f280f0010301500e128012545070040c074030b500c10144071402c8080200038401400c00100c80c2c10b80505900036092042a141d0000e503044101d0425034454050051a45009010f120f180c4909548040c04c13083d0444011101d8810418a010700f05020307001018200b200b140890400908495002d000c000a00038004184213880e4175280e1040750600420b18166603c05d280044140184100400c1c00c0b0035010120301445850090161304051001c00d5043d01c401c61410304048044a415019002c050840048000d02113a1001800708241d8209800d40345170512054400f4a03020100303100c0280c50032040c5455080004440e441341c01402d0000300ea03900d1608603a0f0358207000c0718403d15035041d1a0714900705090241607002501c0c0c00707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 987526321 1250 987525071 987525073
    0xd050109081804140705030f090118050f0d0c21030902040f0b0132071104060b0a03060801060303080105091e011205010e0f0c100c05190b0a2c010e 65
    0x9040c1c8110141140c500d8507400b18030032840c018600583c0e00c86859120f100c0c800320303a0f4803850340e6103902042541c044e018019000b95960341006039844c070101d14000100c075024500800d141d0010500051800e8107000081c030420010744c103280d0006444002519110300d400c00300ca0015005004124010822024040c0d4001d06001d00ea0b9503c40315580704e64400c41080c0d80714100754500030700d000d2a14007100c0e40d4554002c138030140c50352151540745c081c00070a8070a85024040451040018083e034000d07400c4412034a00019030304110075018419100109948402800281e00d9501c5c043c1a031441403081d80d000e41e1304900014048070020b01445050107000d800402c4a58403950031146182112400b2142507207001e224032146c000019540410301d00e000010400700c0001c001340440c0b541d0001c000810b11203486031840000b54180500007020804115030506170445007440260014040c14130241f4070f00c0c107180307152580c0303142e82c600c01c0301c104888101080c50184544c050040800d181a071140d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 987527571 1250 987526321 987526327
    0x20d02031008010b0f030615010c02061201240503070c02040e0106090606020c030a0c1412060c0304021005120c0309120301081c020d0e13020c030c01090308011401050403020d05010908 81
    0x482112099050181c8500c00b0007009803400b107809100032400d4103054294198440b500140c655100a41d0042c40c0b0241854242c2c02003c0a40c086091070f0040c00c48844510340360001400740c6200c80d01f20101ea070038001030180951080c03000107840c03848060310b240200000381c0401c90a54945070041501406034000030024030f661145010000d01440c0074180c0140180c0c080c1059520340022070201c3d058000c0c1c0c00070822031a0a0415054115469142d50081e4101c070020180344800d0002600c00c481e9200885e940b0b1401d441040703040441c0740000003c0c80070501c4401100280040c1080c0c0c85802d01042036a00e482c0c182560740361040d075401e80a5000c4c03001002260f0030102054202c40d02c0d068841c2c405503900707016810713600d0341c0c0402c80000002d8000200000076207864038400b00350710191080149001064000710742035034000d00394618542c1d10749054208040e40010389a004014001212140e00780c0000002d0980c415840068030407010240c0714410b00000b94007072480d1aa0090030199 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 987528821 1250 987527571 987527581
    0x3120914010b130e03030123030d080114090114090c0d09030207210503031311040c0f080906100314010204050d0c3b04170d021215060a12020d0203 65
    0x40a409610b91982c000e10000306a81c01c10744080c0902028212140d02450451b82801c0800351818140041c100070100241c41106141d00c2c184030807603014240e0327aa40610340d0f0400f00000050311030052864044d4031518010005400d2051203100c08500443e43e11116482e801c0f1480424010710b50140c41052404000d6130803d86c0005410b070441d01540440c412501c50254040f1248a0802c4081d0640d001040020b240e400e010500c1c042d800d11030bc85804aa941c81070108045610b0500c1550200343d024811290145d040740742d05900c2041b00d0020700952074400d83c61446c0e40305a00c030091641000c89902019003000790166405002c015100b0030654209041400c40344116100d44500302d6285420b28511101404c4c0380114502e11100010440c512602610400c2c88010400d68400c1d117a810a0f0501c41c410700e005103590b480da101d0142e201c030b103408031a2500160241c48000540750070640d403403440e121181522010709550511b1046841c0e2144042e000c0d101c0c001503a1105840007003001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 987530071 1250 987528821 987528823
    0x605090a0b18061302031908070503030f150405011a0a170f160206010e0c25060f0e010b03100c203d0c0201110304050607110d0c03120914 61
    0x40040a02e00088418980781c0540001041c0201540690107801070540352806401c042141c4864600c00c3c01158a043e080351645800c5400550b1411400311080c030610200c0d1060050060103080129401c0140d5450040e500d480c94120745034600210303030f010a025000d81d0007180500954400310725244031030700e484030007031345103100841e101842680d1044001411901c002001810303180301520115954a03200782190a039001031150088003a0204002c41400494000070612184140c0c03000c0b600b8181005040f080d5500c0c101f00d000c06030314010703200b080b07940e00080e403060b40e00580070001112444400c040341e40303615400e200040c841d850928000a40030000381ca10542d01d82210043c0340e182d8504501070150710601490036041480071006940e003600d90b1018030002e189000008031038000fa42c0c0e41760a901b00700c4050794150486810490180e13003000e92ba4ad0040c52100203088103603c042c00240c40d030803916401800b0005d00e18a50010b02c0074690002044c0c54200944080070450007181d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 987531321 1250 987530071 987530101
    0x30c210e0f0303040c0b030a021c0b01141305090402210c0102120910141306030515120a081305090a0903110f070905041a190c0e06070605090a0b 64
    0x103500030700c100d10395400809008025030340a0307540f1050106038280b40c04000d40d1180c0011b041e080d02c00307a080003100d040c40f041100000c1907280032840852910110000034140d11249840c03c044d0349402c00910030700e40801e1100d403050720011a01d20859480b1030006c126000090b2100032143d013403440c100d2462001c00038540f991a5400d03400c072556102000140d034024000c00c0640781c2c20000088a0155083c05880f050020303180c0c3c1e001c0c2608081050b201500d1480c0f2960103400425600e0003400b80e92040c0f00140711074840d003a01e0300c603820314101d01010340d20296148080d14411021460003c028002501d16000340790003043c4801c9428050080f400801040340c045010072400b46600304040340215070a032072030358050003801c070b003502c1c1c25204405413400910450b02c2e040e040420708480800c24610500a01116504030085501080e180741291503203040c5038280001000714410b01d076100d800f100c0507598019000308880d100c00c101c0d90715150400500a09074400a0200012603001801d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 987532571 1250 987531321 987531341
    0x1706090111041202090a09080f0d0e0703020603040f1103030f0d0b191e0e1003120804021c0f06091401060b0412081b1005010e06061306030c21 63
    0x8000d04074400355844181e00c910f20810080e40440b2842c1d101501c1c2001180e94003000039100401d04130456981d046440d440200c0000e25580082520034600c43d0a100d90000720b51001e0052a92505540002d0b9140c000203000038030011102e81d00710100704035440320300c500001c058100c07038079009005105c540c90307040204401107080c90031080c44503d180c600c4400010300c00b410b0b820350400d4100348503030a0b031042401145207e0300c100d00f00000e0110a4428451007001c0c9900b50822031030440c9031804448080e400c0c103008100090041c80b0140c5e5130103e115501c1426048010410b400740e00e08010191030812003e00058601640715080c094002e4000000844030002003205680794803c44143d40100c0c003410000c9900c0c03440716800108820300420b038540d201504c8d1445004544942458003100740d4090012684a60041100c110481c03107540d0421000c4440504005d40545030074020492445140308040d1100040403016020318070313080041c25101206400c0480303019980001c3c21030100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 987533821 1250 987532571 987532573
    0x10605030121030c03030509070e0906010609060206010b0f0d0902030d0815010504060c1e140d120b0609220e0102130608060a0905060a180b040605010201020c071806170609 76
    0x100c0640042d0940c40701c5008030b503241c1c5400b030007450140c400b140207240c010300f460294030800c1001301d5001000001248204941802450b440d810081d0040076170341d0035405031040d54041e000502009200406a8148010501031203846141c441124400390002c1a0003075014000c42d202074400ca40c0c04242e0350320401151540c400349040003001140e06210728402c2100080700450480000358a02040f030f0f9040300d6070201c01c904041c0316110341d24000d2800030041c7e20340c2d10a9080c000b100344c0040c1600f09510026408002c440d840b0f00102e1981d20500b000203205a4010166658085290079420303000e101540c070800c5402d10303501e0b00b40c0c000e5203c2c5400502140c0b8000340012014455908035106410181810140320324043c0110043d14010309103030790088241d400800d0041900400b0714500c20030210115442d2400002d00084604507002507045900410017907443d180002403840c112091140b411a11070120f02c0c8010050115401c00d90817248400004015170400080c07450164103100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 987535071 1250 987533821 987533849
    0xa0902100f200304050901120605070e01090e0910020a020309011106010302011407080702190611060601051804020c010c0201061805040c0e04050a142d1002090a030b0106050301 78
    0x11605440c40d882400303580380095494085101d4500d4080c00070b103280c00c0100201c9040036140c00000e01101c4090b04200251388056590700c1c01d10150707024075a0800103a0411104070150342000812810b0f40c1d005030038801c10030400fc40d007183e03801c1000c41c21620415208546031100748030300948a43c01218058002000701c81c181140b480c012910780d040301d5058503550011074403680204020340180c0702c261480c507414800000962501011403052820341000e080c200c0d8184200a000420751807100e81c07003a03000f10b0806c030381642c20404448415500b005941c0d00e00724030100103000780c810010100d6003035081c402000046901504110203459881d4a0890055520500e20080b1641100c018101101c1c0c0f0f513082220103015480c107600f15014100b6a0005403050721030505c883c0c002380500d2659801010203a01c142d918908400c8104042003d0005100254407420340d02c10003140c0c0c08810541c00620b18601d170303444201d1350b0025580002e6201d403940c4e490300e01a010350424424203c2c590019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 987536321 1250 987535071 987535099
    0x702010f050f060d050a06020a0503161106070e0f03030706060617090727181104090807060b030f100606030501050105160f03030216292502070e0a0902 67
    0x16000301c5100340c0301000c100784260342d0359041003801c2035800c00c141c80710300618500c90081201d90008120314092a20f0f4250b590800c500c2c490414401001c0080410550810f07101c0c200002080241d08811a440d10041040240c000103503512030162040e40d00d4480021060200b0400e034000c00120f50854442d40c40f07255060b0604400707081d049501fa0b849411500043c008a80b0b20001802c007842c0d01c3d0f140180c00e42c403160440f81122100c40d91014800a1554070384100001c07540303802c0038078a0940e0248080486507540a519010740000200f0590700e41c1e001d04110385040042c070400004050031200d03034400740e110807402082140105030000b41050700110b19940034004480071a207a44082d900b4201207074403030101c1f801182108804040d000c1148562400444078284109401298051b00800c0e03100307035002d4207030400b015088111034080b0070014612400f04459440080176480104c07903400c0d480d0102e00349601e1780c00480b4285001c00a00c0406d5080e030388900c01840c400e40b039424954041d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 987537571 1250 987536321 987536351
    0xc020a082b090602120a0605240f07290f010e1816090b120304060c150c0906110105100b0705070b0c0c1801050d0803220308070201 58
    0x464400034080c5402005041d000481c9102540741e0303040c0280410004194526180064036900b0b041698100c2e00881c616403003520100f42507410101c0180d0412080745080003162441280300320030342e22500c2e03412a02c1c110620744030845010450250711a41d460007685050080c609040c1d41d20340c42480000e86407041d917214900d43e0780c091a8118048180c9a180205074185003c0c0240070380011000344c401032940500412070b03080841d21140074081c0c240e08090406003203419001c0c40d00c2c030901e2007070041c1c1940d00c070100c101c0c0c094801500c3d00480241c0507090141810101000c07040700d180c5004102403600341c2c800803410584001c8e40d101c1c0708080f45000a1402e840050392305408000d10200100f000070001c0c4002c02c025882001903422b915607801e0301044640010382c9d22041500b018588074a40d1504a40002e800b408182d040741c1c1e254141001b103401d002005000a001c51400000300d125514800e5009050f0010402403489001c1a07140091182c0d80030340e81c1001540c01c0c4001c101440710 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 987538821 1250 987537571 987537583
    0x150609050607061a2d030a02150304020a03080409060603181130060615070b0a050a0209030f0c03010e010b1f051c0903020c0901030503030402040504020f0409060f0c02 74
    0x40001d10060501d4a140c0b600c4000300750543d085615500764402d0003609445032015403919070750400b0000c2483c41c001e880a46648403400c041c0c2e10039000b03030004600607a98032a010000007e0b5800d40c035100e07038681c8081000d040c25600068000c05020400088203a415040380c01500c8259030141b0201d5443c1c8002151440d103190001e108010140413182c1c68100036203007115481c20f441c0c14046001e508001c079000c5d10440480100075400040810465040c46000d640d008100b8000316860070402d61110844a40080d000550365500c9502081c0e82e01141d8041d01c620b244010140d4100c4891607403090f60ba0249075143c18029404d088810711600010b1052265090002e001102c12040d00c0f510841031084000c1103205004081c802070003205403004c410700280d0142900042c1820f41c609020b4034000c00b0310160380c422822a00144002100842074079089079050310081003d0300c651000640061700e803071100b034002e480c100c107c005000342078102582c50000a0410804d108410784101e881704 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 987540071 1250 987538821 987538829
    0x1060b30010311090703021c020712080603060c03100302060a020d1d0d140f03040e0f0901110a03090f0803070201231006080406020405030a0804031b080606100302091003150609 78
    0x50811100c3c015103051000016030f00a04a150045c0352901c07008076600c140500b01d2282c45c555a0201c0c10b10100700090007000f000c3c88450070010741914055000a6480c07238000c0a40082c00c801202040800c90001d0300d60014517801460940c654090b298007e503a480c05038040310000c0c007004286181c0e501385201566000760044c0c0b0b0b001d280342031502c0350480c1074030b4034004c62994410028001d680c800b0900c040d00240407c000101d1603418101000c14810304050020b00040e45815143c1c54621386403c00c65441080c1810046902407203410141c0d1149009100504500000170800c03102644c10340c0000b02c032a000300348581c0360701c0c4001d1003100c86c0d4904075400122030b1111903051107140d00a075402540039129400252038107441d040868200182c44404032010300d00820f00b403082104140c07080303500081c4054580719040c5000011a81e03488007418040c060001c400320b00c2d078032034800c1c1c0403100b6000014210b0b0741440d060b0348004006100f021041802c0c0150309138003280f4036102c4d0300c1d17000c02c407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 987541321 1250 987540071 987540083
    0x605060a0f0b0f04030b010305150f07050901081302091611031204081b0f0105012d0b030601110f160e07020606060f0d0903180602010905150901060b300103 69
    0x100e052000d40c282e41d5002c0e003409149080e040c000040064071410090380a90f00c01c42c0502681e400c104c20307510b01610080d0070344020030703182010050266841810780d145803100346401201c1e51604000d043c6540014440690032908100404c005046050441d01084100e99139444041070003004280e180e0040d5080141484034000204010602c500c02030f098031045010700365052a9140e03909407500c440c0313070120640d40c1d46130030040003024020f0560303072040c00035140038112081c1a020407038403045150007114a0207001001099a50340b1170001c10940c15402030456652500081c80669605822480e46602542004001ca5240c4421941038001c3c04280c008120607140c400070002980c0000c400e5003071046c414000d2641c2c6034054040e040c1094003a0302c509100c208c4035000800d00514a410110a582c14948040000781000504071051590100700140c55200c4542c118050700c0c680d4440311007040041500079907001083d46c4483c88581614966044803d0240388240e03100c0709120107405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 987542571 1250 987541321 987541349
    0x7051c06050c0f04060306030201080606040b120702190516090212220c0308070314090f01050c0f060c03090706020c010c060209010212030a0f0e0712030c2108040605060a 75
    0x366054101a0300300421400c01402c1207819400001035030050f81c04540041e482d09010015942c10541150f0058000c0d03591503c4c007807c0c212407204500c245201c0c400e03145803080003d041d851003880070072410420341c10050049034003820850f9443c1d40c1d1282c400000600c01d440085c90002c82e208642c401c0f9510081ca561654071078035550074500704001c0c58200c50751403200210000d0703010b107420405144900c135041e880d1500c07820001d004001c0c540c01c1e4000450204078205551303848103141c0e943c498003464029a00c005021041d400c2a035494660056441a40140040b002c4950091441a00300e401281c007141d903228002c80c0c3e1114480020350204068000c2400032400540041606290600403140d000410704107034012944119016080680d03988038542003c00c1500618101152820040c82c026050450001e41a10349010003414001480811010002d290003015a0382b1024540101001121a0302819480c3c0864048a0082c90440091268504110107000f0b1f103070112440c0c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 987543821 1250 987542571 987542573
    0xa0308040b04051c030e0618030409020d06090c09061706010921170307030c020102120c030907081b01030f0e0705100504050307080d0306080703080304020f13050f010302010207051c 80
    0x1d40300600192030500441c1c0810145003500c405150240c1000d0b80c0000316503007441011410140003034030401104014844810b6490000000c6d2000c0e40e072480e10069540c081840a5002400141d121300392840c02c04442441e25604105180115013042e110355050483c1c0090101f002c0348101c88203808034801503c00e0003040710200c8000d22000c101440001002c10507224007036600c42c5000008080d9a00004000c003103a454000c200031054030340025804c2022001c504811820000d10f299259180400001d03500c24003000f0180080c00d528080d501d0400f0010048044040310000c803901181c1010441c02c03040c04240b0520102000c508080c040c22820b04042180c005001400d850070080140300100e8995806d121010060510100a001800c00c158005c0d0503540b0340c1d40058582d41081804002089091701140c1e4001e41c12039088000000d080001082c02c8840c4411240b0640340400700f00b010071460070b440c0d041e00e00076001c03941b025980703408101c0c0e0b000c4440200341e141c07001581180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 987545071 1250 987543821 987543833
    0x91015050a0e03100c020c01020a1e0f14010b0114090f12071505030f01170d050d231e0925031a24100e01030f0614030f0a030804 57
    0x7240c40035403910007000e00c40000042c2c9002d140300030700e0150310740e2200d403040d02640401c43c00443d15030a0010b049201c400e62603200c00007481c100e0074203aa5001c01c5600c400c02c40d01c1000e100c1511f92010f6100100c2c51a103902c3c3d0f00070000c0d0040b281c040f0714036441c00b0302d20380340c02c0098480485000381040c800103812424442d1500d55072102c00782c1482505408510a0100e01129408103e5661155141d241209003806960030680c80046a101103503043e003980f90011900900072211400d207603640c0e40b0100c0c0b5400c01800c4403188000c11010801c1080c48002041922600445003500458500d480e480b041c250420b07010769017010903510140c1e060310502d84547d0082c40d04859120400480b40e1780e502d62002c04078851458184d2010403401304040001440d00401c054459103640c52000000003010903071803007800b5910001c3c00404494070416a100b60416032112100340801e110081d642c1d000c0059816441e5a06482801001c854424035200044d0088002d80c059a49400c2030715551240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 987546321 1250 987545071 987545077
    0xc0c03110409020907020c1c0b0103021207030506010b0d150f091508061302120c0102030706020f1e042909101b0c050f06070f061107020a0e0609101505 67
    0x582042d240c0c00140096510072550307520500040e00034007141d0000703070104101c8500d44000360219038406840074000c2109a1081c505480d8103540303e0000d0320320b1404036850440258001801e5101d080008600905c1440240940d5a6445c030144420a00307181442c003007035160700902003401c100c20020840449a508440e041a0116000c450059101d0402d50304240088820509440c01100c02c102141800c11400f00082d4552015140c96036100f00002e40380d205040c406014284c010480c0c828140046c022568214100130305000841003100c00e100305600144503c460303142482c2c04180c201240860b451a40340f0900d09200d01c0d00c006841080f5040400d00ba543d020010680075901c94840482d030040c4415014070380743d4812a242c0340c100501190450070b035a000c1d6000340442c10000d01403001a10308940d201c6004070318554442e080070500d00520501a501103251600060000800700e800c901814050702c04805603174402003040c200c841a0310601c60542d0b02c8072104034030248aa406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 987547571 1250 987546321 987546353
    0x20d1a060c1b0f0301020304050102210919110d12020105100b0405060f0c120d11041d041b0b03040b0a0606210603080309010c0f030c02100b030a02040203070513060c0c03 75
    0x300f46010440070042403c9810444084880d60350016001d25000d0802104a102c8628110208400e1a002040b10744641101a41006002086c44204200b0804495900a000c009040000212024142020803c42520521000d546044080703014454100c541000b03035604803c213986014584030078002c1c141d10a030701405540400b40500143e101007400103c003803549502da0251503484086030b24003241c1c01550b2802da84201000200310746074000420114181c0740410b5078141d5075803810004040c0c5000010140349224020b000319900000c040610702030b81c050201562507a8a5510440c1240c405014000100e5641242e594940c440c118100c02d803955003000220b80240e5950740c21003603130400d031000c40e02e0341d46444d00c000c0c283c5c3c0d01c0000b13064548002d00d002c0c0890090164042e4640220310842ca5040d13864440041403038a0400000414540c098801c641e2803602c880010b1150b0000d1103074071540104840d0001e091482001c00c0c4900a80080c1402506031860b542c907007203190003c2c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 987548821 1250 987547571 987547579
    0x6100e0d06020406020d2604020402070f1403070b1303020618100513030e0102070e0a09060b12060106022e0b120d03060f060908060c0901050c01020d1a060c1b 70
    0x1a0100007101400904002c02c4140c00070120744901040240c0801925000c52044144003000030a0200c03581251580081d01600c00607030700e00d107600f8222502500050080c001c20708241c4011a404000801440d441d409407000d4000c07900d80d03040341c04075045c0d90003020b00184d024001092001500c0b000141c41220b1800468003019a0b044055065903c12121040c9002080c50079074145508401d00c3d00c4009024400340c138031681802503044c00440060b003180c684654402d00e0300104001584204400400106107550000700c202030306a0301c013424007071140180208601c4032820400e089004d0000d9a06d0441f680351200c13642d00c0d5400503c1c101c00c0d2981d00442b240c101d1070782418244004100c207001558089040c0e403c0025051000040368050317030070403030000810007410a000c90b4803500303c0c00c01070f8615a507840d0300b00107c42d02d00804620300307403d5200064000080410b54040164008892500c4441503642020403e007409280105074854120754400080e000e40c0c01448000054010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 987550071 1250 987548821 987548839
    0x4020a0302010318050f0307061103060918030904110706061a0708130b031f0f1a0702010201110c07080d03110d0e25050310020406020d030b041b121406100e 69
    0x18403298a02040c614280c06039402c00a45035083c040c19020341c5203103481546c40d50f072850610300080f503c13000c001040b80e174121403540583b142050b0b061080322a0100018014403146074283c00c14190b546c050301007143d000745001c90005404070003000704030840d44001382c114141302c03141c0c9802a160303004920702d08000841910201f044240b0a0146015070041c810300303500350b00f800d8103460320b100d45500900900e103a146020001340814041480121401c42145902d0781c00c6032006030302400304076a1002c22058082540c1c0d2219000203840021540c044c4100d03405109000006c0e0100c80c2400700712042c800081182c0d0810078480d400c4501800080070444944061030308905540c20340a52244000300300d4180100201e16007040362000074598940c0441ca09464018081c0d0f40341c0303001d900001819151001001e032a562648940da0300ca910055131f40500d885400b0041014a98040ca000b11918104000154100c3e4801c810b11075036001d0003a410740e41030000240c0d2449101c0d08000e5000303010f6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 987551321 1250 987550071 987550073
    0x813090603050105060405100b0d02130e04080a090b07030518120d050a021203100e0709090204060801060216151b020a060e0a06020a1203110c010e031308030304020a0302010318 78
    0x80c0c40303030000450281e0000035a03810450104000da40000d02a000b541017807400900001c1a02d20441c4c04c0c1105517403006948801241040007140500e921454048414500300414008048010602c06041d9521020500d0f02c030400b405490090385000742c0001c0d4140200c0c031508003d0f41e903980c1c0c03032040101006e03003004140e08014509010106208001000030811100b07054041144256241c0008212401c40c500244201250505403040d001c4100545021420041c001c6681e140a00340600042d56640d460b81000b4003108804c2c85071000612560082425105542000d801920700066404001007554501103a44103d5014021405072540448200607a100c0801d0002070002e40c4800b08034011000400c25544030542c00a0195009034004000261003145a1040c8109a080005102307110710080e000314003030b03101d0101d84c640c070b480008000002d002016003000b0303882e00d03c1141d5240e03c42501a489000c1694000d40048204000384010742c00391704200c000c0203060314442306000035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 987552571 1250 987551321 987551339
    0x2a05010b0d03120b0a03020f09071b03081e070915050405060c01050a0506010512010501081012140c0307030213051f031a22020f0a0b0c0705030d17040813 68
    0x1500d101103020a01403c040e4040d480d481c0203038207074600d0032070351040140e00c1c540129500c99035100ca994810b04c1414000f543c01c0b806924020021340e04032070300d240104030a150181a110042d0303100c0c5c036282140003100c121034181d4040544070703050f16600d1184980c80d00c0010008a0381c600d401d9014000c00b4040030030182c454401402c500388003c4004601420700030398000440303d0141240307041140800265010b1208000c0c0541160000c0c60215070f50360790f4140381c4a00100e150049418038151004020502003100401d1409400b400142c0340580000800c1503074901403880000c1d0441c0712098908170054141e40000c0d0b04c2002d0745011400427080c0d4400c03031400410340d04221200304605030508241c200200200342c0c4000144030103400e010b56040e81001d80c0c040418000e200e094034209064441e290501188018114550340c20303120444200c40c00c0c0c48a405d4013a01d0f001c6d1241c124000421442780180c3c05100d02104024244c81e00e9945541d100d80d0702c42c500d01c1e120820160000240018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 987553821 1250 987552571 987552589
    0x200d080702042d090b010918120203040e09010e0f060106021b062208010c090f030210030905031602011e050a05161a010e090a0b06010f0c0203061302010f2a05010b 72
    0x780d40600000c0240c4240340154445c1010780101182501e00711000745804010f0526075030250704514150310741000804200c0c614400d84d040020304400c05d40a103c2108815046580040348070800e03a001d420044c44903594619091283c0b00050740f010300f4201060349076425101901401030419442c20890403405905c0c90140a070358115a0b00f0184208028142807190004a80c41890402c5123940b4003604030740080703124000030b0f00c9081004005e0041c0c0c8c2c025131050b40344a0780f12040d01d8651106e8500b800c40b0f164040c805a0204444a0200200c5a4045003401240c01d55440f0a0b0605098081c110303181d822800003a81c10300c04290301079020460031001c10a8180c1c90000003c06581408140880c00c980035060f0442c591040ba444000038000181c003aa00c41003e203021504400d503008c044400351603208004e5014000c56084c840300e5008401c04030b441c04e000ba2030303402030758050200465140c5040e114000e034440583c105410405041042001c040340104004940311100c540020b03070800e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 987555071 1250 987553821 987553901
    0x301030c0305060106020f07061407060509010209100302070b130804180605150c0a020f0a05040f1a01090303080f0c0c060709050a1208120c04080a200d08070204 71
    0x2480002002048010803e40e0301600c410304c040c114034589216100d50300d0605010320030a0146d4074070034180450002095030005a00038005006a040c8a05118003c0d800a1941c501130591200c88000c40760081c000c5502166100c405013070940e481021074142005466022110080d04100000301e2013003401e400014900b000000040a40c546010000480e0007602c000341d02100c01d01500013880d20104200000d2901510320400f00c1e8020000074031800c02c02c1c0c21190340603181a000c41d0100701581e1060301c0a480d854003014000341108015600c000403480000e001500c540000341614402507a01a0402000030b01142008103071a8014144401101c0400000342d401c00c0800240c40c0040400c80140000e99400102501940303501c11580300346040341c0404010840481e501001ca00219801448404162100f40c540c41ca00a1026012100b1201030710b084800f0559840c076202140a1a2682c46a072251801c2c1480d07003400b0141c1900700002d461480021101440c0009600401c5050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 987556321 1250 987555071 987555083
    0xe060c121902070818040501050a0612111c02090a14030a08091c0f15060b0d02030402060c0304030804060305060603070c0f032c032401030f1e0609050d0c05030307030e070308030103 80
    0x2c892a0170074041240c90590019105502c0620100292a04400024000c0d244040041800c0320040406982845072010218060b00011520b4a0081c6154003070090001c5c00c4454151082d902c655001c1c1002c1c0100c1e145a06400040c07403000000c11420080101c103601905003040040080700203048652542003d44803e00350124840c10031003a2168601d00d00d42110040000380c1c14913524100d207000e10344040c02000c1c0e0000110307066580b020182c0d0303d5403200c407088940e2607481e0710300000541c119200c2d440c01b0a0416004c00c0c1d44d85442c2d81640d101d0901c990720641401d182f030711400b81c03000c500002a410b22050b58024542107440c00040065410015680014a81001b050520700601c20781040c205d01ca101081c0d0708940250809141166002040c0303010102c0e5a04203030030f4040c5603070900c20050035486600c0b401c02c0340a03005000c0c0705000d581a2445490000d01c00d845141e80c1031001444d54004100040b44103000c2d50003080382c0800c07002200d2030240c595540d1550350344281c005481c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 987557571 1250 987556321 987556357
    0x1909080301030201021539030c190c02100f03020c060109062d0608040206041e0303030614150d0f0501031110020d0503010603091a0a0e060c1219020708 67
    0x9550b010000c3c0036101003d06403203d100e26000100303914400f010b6892410031450b03041d1803c111550380303902c410b00c1068a1080ba41d40c1c1480d1927a42903d500c100c40303a4000028248201d4a060f000d501c10310a050b8014001c921400d9160f1022160b0250502100c414940d080c0000c40c024082007046c1c3c1d018200540c40022181e09001e480354110a002011016855011071005000b100c5081081c04484c0304e41020341c0107440300c0c400101d56000b190800c0300c0121210403d0340222401200c0b06003103e002c0c3e1410407025450b08100c0804062801070190408071030928550201220310061600c0000c005000172040c888018035802d4030401ea1050300c56100d140c40129041c50302c40b00c11200002c080c00140540024000c0c0900b1600052140c1014541d880300b284041c0701e071001c2c3c0c245590305105160301140ca081c0c1c6403003004084e03008081c81248180000100a8507018084610000b04041c8220481e6280e101c20640d8014a84890f40925000d101490000780c002c2c010b410402844208910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 987558821 1250 987557571 987557573
    0x120a050f0d0e01140a090f300207180c0e0d020406051e090a09030807031e06151e020304031b030807030c05010b0f2d0a060c03180518190908030103 65
    0x2007020003e030001031880d150030b0808000030400304880203500e40c420340e40800c20480b1b08030f0811100501c1c2121100c480800801c654803540825204103680c10060200c00e10320295250b001180d600810002c08a0403030785121280c0e140c58100030b00303d3b0f44020b0000c43c0068544000c510840020380c81d00e644441d071024100c1d018a80054003c0c0d02c1002400c00f000400d9040e20300a01080000c0c0c43d01041c540d6030000e41240046140c1c08070003208018005210043d41d40c0922903108600900d60800038400070342143d200c03a0003180c01c0d589002c4079030082d8201420360b255242c24120003404454042c244080c0040019100c402900290380241c844160080803030414600356070000103624407031075401c94024650398032404d00e010301a51140ea10300c40880d0040310001d41142c51003010780c0c020200440017601a501c00d000c45001c621035030390441032420402207012010742d40e01401f0f900000d8180c80c00c159001c0e0f480401d9208001c044910070307458030550201c08a50850304291801c102c00030040c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 987560071 1250 987558821 987558851
    0x131707081b150702010e15041d0a05070801051f121b14091507080c070e090c04050609040627050d0f0503310b0a06090e120a050f0d0e01 60
    0x8005524603104503441e1501c3ca90009140020b42c0c003000c1d100d0b406080101203045c0000e0142c038003070304045841c0145000958420040c08030201d4640032600c8c14840001c400621810143d030484a000d0681524025061010103400c00b4003141c0000300203c20150b4a99007240b4058000a0b2542e04581d2200c00c0922030000d141c003020f401d07a100d40050401c0000c2c0180c03a052a0ba0340131000006055460301468038214074988131383c844140c1c1d00d11503100e012481c06900c1550300e005200d69000c07520352040b031501b03010035118101d03140c031350050b403c8000501040c51034000d00b440c0440c0005c1c00700a00703201103d207801041d40b80c109603190b1344114065540540c000c40c001110b0821418054290728000c42c140410a2013440404034600700d0f0300c015444082c0c1013014540503175000700c00c00000d10701407821500520181c49104205414118080440c0d1808500030501240d040100381c5847c00d008410341e10395001a1821760808810019154001141e10034a1400c0f00342800104020a40c11100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 987561321 1250 987560071 987560089
    0x9180108070f08030d050a020408030c0601090b030a03081b211e01050f19050319060b04050f0703090f08030405151b040501031e020715050705131707081b 68
    0xa4658402002c2d801d1011481c008242c5025644400c40460755643e2110b140000e40500d5000c1d0f98148800708048030a00300200c1c805068401010b0108102c10000040640e00c4003a404d0281c040790010000c6042d400d0390002d4601000c8034401403030314007042c0c3c40b10505005c6980802000b00c2524900384185a8508441d001c1c0a2a80588080595040c600040d106203a4000a14810360700b0700c40d680781d0a4200e100d040000c18004042c1e40074442403188550440744220b100700d80d6a131620700d6290780c40c40c2500c034660280c8000401c0d0384944c4e6070444160001c04c400b05050300c48201c1001e0040004940d00001d501c201c1c494000341030031080040c4180d030681c0000d4a1400ca008140c481c01c022401d14000f5542104e500f480c004c11001c02486032510701c4000c05a60810642c000580070b424440c00880c060440781031402c04024aa5501900312900e004221514200340c10f1050100454002070140034104042c0320140c8440039541c6d41c0707013440c000700ca0042c22081c6151981c503c40c5407401c00c4030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 987562571 1250 987561321 987561329
    0xb0c0d031a3109020102010f020a0c2a030809010f1d01050d140106090806101802070218070e010207080a0f3005030a111318020918010807 61
    0xd000d0306040d081401c403051030030544180039901c550001e0100d140c00d150200305100000c100c40040c03004840242029100001080e405982801c1d58180101564401c441c82d5003840c1e40d42d0701e00303944183e54001c40944006100a030111103d0844103021810f508000700035449101003503a143c1e1080009828081040c2e0220140196004664032180720211030035501882460102d543c1c4041824910080640150006030070f040d080000c2030954028184005079032500044518950350344000c0a0b1200c0507004015681241011040d0080c9064020344502c500c020100d803000800310326484c40c1100202c2e0100009205080c148032103580500080c03000e0b24400b40507000d245010f40350b42c1c00150b0541c9005041580d5403400d103070348000300c0d0080745a03d01c0c855402c60160400c0b25008181e03800683d00b60100d00d103403040560a540c0c20340100c40404002c01c00001e4998940650240424025868440c40c1c580130442ea081c656546a5011403450207141d5020340303941480780c070710320301811500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 987563821 1250 987562571 987562577
    0xf09050c13140a081903141303030e0126040b01170c090a11120405070b03240f04021309060b25020d02100f11160e04080403020a0b0c0d 60
    0x41d58a02070003014445007500c0c11825194415900240810080c0707480c1d90260240307004030400840a848400d0421800500943c1c40d026206510350344c13015940700742084c0c003407964104a01003001034010518010628030504064000721880c0103404044581010741070700800c9101e04000400003407102450251808183c5c046014003040c600c590f8802e08218003a104d444004c000444030129500500d2072a080705040580b0392003241c2ca50f02402030709440807581801880000300b0101e4001080d2445002440d5840040301d5801391010b4100c11017485240c3c1001c82036100100c0d80d1554001041c24000100c41071600518009620b0101c0703250750041d111000d801c0000c58071207072000d240c41100f000e032072a030400076203c248001001c0000e480c50007900440b80901c10120150030543d0241c0d050441d071101c4008494608010380c58200b441284410100c02c2d560500c41c0840344040d441d4030074420520503140544a070009a41c5c103182e6031002c2c844100019480c0c1c41031100303025059604820341 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 987565071 1250 987563821 987563827
    0x311011104060f18081207020f060a02060702242e08070302011101180813120c2301140d0e0f0a03201b0103020d0c0806030c060418110c070f09050c 65
    0x1a5117035150700110301d0100c02400c020071081c0c25980c07840d800983c170040c001c2034a0742d01c50100b03e000cae4542c20b040303410002602628880c0648143e0081c29403145517081c10441010750703504035029994400000c00140d4100c0100b081c02c115019140425005d8038404005100140c078501c00140318a80c400341850103a410403900049036050741d800c4044c030561014840e6101c2d00e03202255207208807139a0008400d00613042d0242d0a0141c0c140d1944140c50780d00400d4400042924020f0140c1e0303100c00d20660009800f2111194489030100250080c03001c62000031644c20500710100d45448680d40b01e012894105407005020540c02c0506401000e0100c0415241c0950741140d0341d0302c0381c2800145040e000303407070750007400203038031a504442440380710805c100800036a2910003401440c0807501c0710f00134825030012005601d40001034600f2a4009012a9089a0140c4a05002c0d100401010203c00d030140300402c03004c0418401036001d003004003410303020310b8036251410069072300251440300d07682e00c20 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 987566321 1250 987565071 987565079
    0x61506200f030d1805070303030b1201020a020a14120304080406020105061509040c0329010807021b1c0b0a020910030c080f041e0b010905070203160311011104060f18 73
    0x10007a90750001c03c011000a00b9048034022424041a904004086000765000442015095848807420000a6440b008903120080c4200c2c02c034412201d200f005a40008620f00009850009280d030300c244110544000c102140c80b44078054009132002c03945207001140500c007081d424032030b00360b218404440c170301e41c5085884044100c1c0c0c403070020814015900d510b294003101d030294003c000f00c0c0044d2510040740e00c000c103541c13680d144034992480b8005000c01c1c0106c1d072400d00c005030032080c440c1e02020404000c0310240801005170b10b60f111080c224420000e0010200d050300034510710031502024056581c003165810081810519690380b020306203010a02d0a19507444850130b03a0008043c2100c001c980c48500380030303e80400101060300e07400c803010a04020461a0040c0302d04942c030701c41c0c3c1404030707445081c001e80e206d00500c0a0703048242203035490702d03010900c00e81c040240b40480c600009000e615894401820341e002c1d40000c0c0c086401c031400c0d41e04070340d4800020b810807181d1140c00140c0500b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 987567571 1250 987566321 987566323
    0x12091e01020306032e1a120102183a020607030801081c21111902010b040218060f0903100905061e0604021b010c0305063a061506200f 59
    0xd40e03090385c0616610000307090144e07014150100041801003501e003015000300d0760640070b548440d002420140107150b248626003441c1d440007a4100440c0d003460800c0e540003171900c009034045030300c100340303c40881038050241c2c071120028025180a9030310360340c686d810b1200452801041d2020b042142210341d05880c02c403988401c014400c1034449104089840104001c0c601401080d48851203080780094040303015001c135401d40c14001203a4001703003d11700403181000100d003d10321145903207481e1403005201c580303003030001804608a102c08003410a0011070100303107044041e00185074a2603603a0621828094100170683d03202c840d09680c0164060015030340408a5800313030185001f00d40116203004043d0300d8002051001f41044000c20604480c0d03000100980301c00d0342d0f0b040c0248c4541c4080c82711080f0312000742c540302080c4051081e21000c2c4100b00030380c02d040c408040d10300c2a074616000b2408410304004000800e0f0a503180c040c080418500300c00c00d0006800e0400203680301c0f1031840c4104c44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 987568821 1250 987567571 987567643
    0xe0d08030f01150507030e060315030f030d0609060b070f030c06050f06040b060c0d030c020307141b0312030f10080a2301140c070c03170414040603030512091e0102030603 75
    0x8050b21230076203035156828107403914030500b070350f01c0e074503007e149006601c0d080c0010207030801c103030104002d1098660b145a214112000382c02940903580040000d100800e40d40e00c4c038048a170b4420728080c0d031401700c10b0716040d044600039110301c3c250181c1c01041c00103074a014040c500c00c07140c040315000c1c940007078440155030701c0400e80074040134981c0301c911070001d00d030003031056815413074101c3d203114110140c8038030440c1c441d404d1003040148130040d90003a005c01c1c00c0008555188200000401740355485079180c628603503500a01d40b070245100d5490201c0c2c0a1030074041000742a20441103150050881c24855041030360401c0c15641f2030b0702d443e22500e40c40443c3d0130349035000b0221041460791584181400004603c1541004d001141c0f0521170712035440d80180104125090f0744602c5048030860b0341004103440c00c0e4800640040c03414000d00d0720001c108103289400100d6007088842840020020481d00c1c6141041a0200d07503003c0104141f50509000c0085a0344000e90003120044800c000104011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 987570071 1250 987568821 987568847
    0x20030a06140628020f0d020307020301150e01060305060303250b060f06090402030a090b0117060c070b190f050a060f0909020a03120207091a041a100e0d08030f0115050703 75
    0x415282d45002414000d108044015076a50b041da041d01b04d10340700c0659207a1010308228020b62801d50102d3320402c1604101044e60100404039401c1c1e40791060407009044090040741d41400200800e604100d644d40440c2c0c0c01c007146550f44003413004141000c0c100490001c1c4104d009004184001059558040c04c844009004880040e12500c860540300c00030704683c0c1c03004211003502e43c0045114840e002c804c000a2403220704442c45c039690f00288001c90300440100418503007940d000b244203c1000e1071030300c11240351942d00042c00c0c29000c0318079050394407e5440d103861581c0ca2005211650505040401510080e58144541c08955021481e0303401e051001a20080000185148480c400d011100c01419054800d0003413500c00840d40030910040500903110f1498240c541d85038030f048080c0c801c6a10070080000604000c0b40c00141c03288039803044c2d4242d002540f00562000982980d014500889603440c0210903581000407520140007800c3e032010900c030003441900c0009078030507407441b091 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 987571321 1250 987570071 987570127
    0x30c1215090f0605040504060b2e030e0c09041101030614100309081204110108150a030320162d121a0403110115030b0a20030a061406 59
    0x1000b0030080001c20703c98100542c05070805044c4403c0c030249030440010500100c0b00c1c00203031180e107030004058106800e0340b8204040031490720740c1c0c002c1c01ba610001001c4d0340c0340e080c1c950315020740b40011110041101c00300c0319821076a103d1782c2113507894800d01003d04440002c0c603504000d0a0009a0890b130b01004100416031500403560402855070251a8070388a40c1110041b0307420207107401d00e115000007a8450000d6145000a50890201000350b84035000140404080d0390030741d00c0427a00c4070024806410311046810702c40c503408500300b040203005280080751070341d0103042901080013050100440044102e0307030710083c0070113415002c495080700c402d49400d54128070f80e440e02001d00d0b0817400000946500250400081c1500b1030100e40442035a28000c004070300f6035106a500710500e600001d070207072051000140d005c40d200c2d441074141140b43ca008407007103591464049916482140c41404054a07544104841e00d804900141c00d910300311109810005a4400360a41a460300700f10725070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 987572571 1250 987571321 987571331
    0xf2301061e0326120a14060603042d11181b132313020a0212180415030b07051c020a090816030b0a0b010f050c1c030c121509 55
    0x8081d032100b095800003000a9400c1c3d848800340f09441320000012100d0420040c20800300e050080003030140240301d040010580390468403252188030200d21000040104100c028150b9401d15054020026800307200302c402405900d900d0092040c0c40301c0c81102c16410a0031442406245084e0024110181e2030300e6004a0311201040303050100a202d07036100317440e45044086118466400c403410b0030494802030381e50180015038040d0304012403244448050058104500411a4400901c024120101620b012a5468500b640090200d43c0010826204180c07108400c20403c4000d4001c65400f1059081c00c50401d140307104405191521058400071940d80000c264000034040c006075409000e0070000c40303c0c8003c2c07039282032600d140380c0e0005641890125001880c200824000ea8402000c180d40300c0050005540054403a5080122000c0e51401820394112841c090400b4130100e44419940c00326003c0c40285029140e44050520301d5100703030a0998501c1c2e10480171068104940d0041c5001035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 987573821 1250 987572571 987572603
    0x5031b0a0e040809041b030e1506040b010905120d0212180f0d0c08100e070f05011110020a17130c050918010501080d170f010e040f2301061e03 63
    0x3c0148508005242c1c041c1c83d1585c1581d08441d01c0c0040010f00d842c90b00c0400c040000c9140c015079900c02008141c81030a81a40050094241500075001403001810418036142d1180c0024800c4004080048c100703034014190103820343d03410854100c11800d1442c02d5803038070b40c00e070a41d50700c11000002007600a5030300e2068007001e80c031810741c0c0c600f01740c0c0c104455080c840e40301d14549032580d14040e0f403100d8060420f00f440d40b45800110b0100c00b20b5440e41c203d40d5205180c48c0044d0b9034088581c2c0718525a00130b25480c0d004281d2580000c003031203591541e0b0340c0c80760594102d12840054015010a0451108441090018266540c40010b44104030f4181c2919960307002c4440d003e10001044c460745500700b10000072802000101c030b065410003500d4400f4613441440c41d1041c04074085410b260325542000040212328a0704030f41581141c01000550b0090b03515403944001809001c0c1c0007014542011000c41d9a00c20a10415000d080d101c7e040d2181144600c03440707200c10042d8017014001c0c40d010f0000360 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 987575071 1250 987573821 987573833
    0xa05011d070507030c0816050c0303040e0f090a020d1b0e0c090910170312010b0307091404020f0a120507110307024b010201050103030507080706111305031b0a0e04 72
    0xa45c0c85644695000d660302c50781001e4148400910008440c984290720a16006290110030349068408030f0322100025070f180f00702c03c029201d000d0041004c2d4002d2100e81c80250700c6424004280c00d009a01d04001d0802c07032262402c291890b0383c0000c01400030301080c41090741d03402045500c110000c9400d14240d40759203052001145450748505c1c1c41148038031411803030b250040302420380d0000c000d510302c0850380e8900f04e09485110844d540d900143c0c0802062080d4803010101829016014000605220307603585542040d510407103103580860b00420386101138004038002c240d030000003032030001c0c510300304010401d0356400344c3c200083c03003510559100c0d45001e014030040d07250010074410f00d1810349803028415170b102c0381065440000341c100052070241075005004040c100c07589559540e18019240d103620361160818030040312030a40720424003242c90342640c05010b00c2241d2080703001d0b0720b078502030070103190440381c2c2c0865a00c280c7c501900c41e035a90f00d1040c41002c840203003210440a17912440d0507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 987576321 1250 987575071 987575087
    0x151d160e1f031415041406011416081305100e010819111207020f01110f21040830011203050d1e0b030a05100f060801140a05011d07050703 61
    0x15070343d014450402910744000c0303035200321240d42502c081100c1c116000c01041c09031011281223021524181b0540748040b8110010300070310400c03500e800700644860795446d11580c0450301c01c04004108450038045031914240319104c44209081c50780d540900e1100290885074018500c0c0813101c84034240c1c1605203450780220031403d110640c00c6aa8545020b0034006810b01651110014030400040715001c000c140300d0742461040303009000742404107603038190040350710880441544030010b00708070700c1c011100403d2500a41c46400410344800c044550729402c0c000c94a080c50701581148200c00c0c102d003599072050706507007901e410040c00f44079904041d10188502e06030b0801941ca002d0f8499403543d5080400d16241d0b1540009000352034014040650312514607802031300980090082c000091a11740c480c1c98070081d075082c041801603a4011803402c54000c220001030b8442070104004444d1450b2061901511040d010302c004402c0a0015404403040208084203000300040d4079000d140c055619 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 987577571 1250 987576321 987576341
    0xa0e090c04020a032304140a0f20030a030c02150f04090c0507020d0b010810050906060d020f15041401020a050d120204120f0203010606050a0e04151d160e1f03 70
    0x103101c01469000850804101c001c1ba4213031a0f02d42c0c07600085e501900d000c01c1c04c0032550380004038400d000c501d64032140d198044000d01018445e000740840f058a840600070082d090b4003e894000a2900600600010390160b00f10410810420003440105e24214015501503820502c000540c001802c1c80664403440348802c003a500010603c00d51007000a4502e541d416500c80405581c1480c0403040804260b03441560401180e81003c1d0020703c0f5030a101041d00c0300305000400c8580c4111001010410141754209144851000003a0500c00080498801c5900000a20041648686603124507881c2c107980c81e00002040102c0901a40d00c160030303011b460140401c213000819281c0b01c1d180109081050341c10890003942030041c00035656010304e040c2e0325503031078a80795820806400820440104055000480d81007003c1c41c000c1910b964600d2035001e5140461040c9441d810200581006401600e02c810204007215910f004103880b815095110380800f120850007100107504140c0103030582d184 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 987578821 1250 987577571 987577601
    0x1020d020c150906070c0e1603090b0c0903010b152706090d110405070c0b06180a0e010f02070c0519181d0d0801260a02150f16020a0e090c04020a03 65
    0x600032407c2000c4072886406400a68101404c121020740207805580d841680035040c0c1d800380300062101c400b500c00400707140d00000e000045d600c4030080012800100e03050440c2c10800d001c6441980500710030318490700c20341a5a0810020030031f080010f51684154079010740241c989506c100200054451080160440100180f000380b41145000b0201980ca040039916502c140d0042042420281401181c145688000c07001640e40e1002c0b1a000d4a00b50101e41a207642c0e403c0300d50581074543c4040c00146208071710b800005450302c8200728031401061841100c0d03c6010b1020840716a5501e010298984245000308003500c2070040d45203d50110001184203000310804520f00740d070b002208606859540443c42420001c3d0072101d0144581103482c2116548104080000340c81d0040e14403121514100e84035142c461b02c5010340400350000c400300c01040c2c860840d00011032610a065a0242020003540412440c103800102da0310340c4203074040c9004540c0044c1a9105520903004000d0840d00340e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 987580071 1250 987578821 987578843
    0x115050f060c1c1e020d031802030a0602090301060e010b0a030528051b070c0b07022b0510022701120606090f0f05030d050f0706060b0901020d020c15090607 69
    0x10a07420400281c6103001c4001a482c6049500015a04c0d4500c50034442d0b50790003443c00344ca5440c001d60080c142c00f659404c50901407140e11006903400c1000e050385522132500542c07038111a006050039219290050017640b002c0100510250756100c00303880e000540c1e45000320703658a4582d06081d21a8024841c9004400f46010160f25580c554000394060904ca5401604416050424180c2e034010030030700034844440014108244507003900038140039800203001880b01044066500e00c2c4155020301e81102000c0000310b082030103001d2012040c0e1280c0210158030b44910101081d49494880700c0518202c0764400128032a0b900c0313101d190021000c240b20801c0690340720b080c050b0007000d441c0300c0c841e41043c429001003000d00b000c0010904a0344050b00614180b142e40109507003d400810300c2101c10b88050000342c1c0031031b03001d001d408001d14201007a141c3d1140c1000c00241403844010910f0290350044803014003e841d56a080e80c0c8644200340711581b92191007001400610a059001d00034000c96 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 987581321 1250 987580071 987580093
    0x4031203020903060f07020c010810080a2105031009021605030c0a14210c100f0905300c0a12020c0135060d12020303060406080115050f060c 62
    0x5a8020803100348100d048403101d644170a503071000d4440403507442d0b0050f04032440044465010f07540f840c3e0459501d400d111150782c0c41b0030406140440260003640c0030381c0c01170309403040b072071550030020540015450514554030303081d504980110060310403020035070350004248000011002072a030310345034030005407a41e52041c0c40c49190b40c0d00d6581c000790780740a00841d590705c00d03d03000215011101d000c4101b04106081c9484956040e402450b1070085a000e29480404c9000310f9224480d030310003290303600168881e01818003d180c86615815105000c94903403210480050300c0406003c400300700306403560f90b401074003c242d061040030000200301621500741b60b0b40040d0041201c41d08202e013a40e449000d10f00e0501300050700305401c02d1001080c1458181c840943c502034040a600400143c80d8643c0d9941907615681c4800c080350800340184c00c0801806004e2500c0e008200007001184003e018138144440c01464000c900c0c400e5910400b410035044465880d03c105450440d10b1030400d40c3c440ca050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 987582571 1250 987581321 987581327
    0xb07080114220e0f0609030a08060303090f0f0609040e0601031202190209040305040b0304060507090f05090f1305060115030c030c08070809030f04060908012a080a02040312 76
    0x1080c000d00000d80349112a501c0d66040400d650010140d98000860b405501065024001c101054100c16940110b812814a403241044a90b0248210788003c41d07440b4081807004180420240160788260420806420315698006030242d00c0c44049460707000240d040350018045204204640e90001d00b81504400e4450000c9001812603000e404010300010b40c44a0032629284e440300c4035828250113203500350141c100038917602c0d4014828140b192805868208280e01904121012541c240d15101081022548010204005c107010120701129a040400044d24101c0041020b21918000400a682c888040c404c041069030440b003a1920f03561140b00090014200e080d07140b01190074000c00e208154460310030000b1810450750360703050a44a4003001c452500c000380c0300700e074903200602515040f20a000014001001c50b0707211078203440e00d0031800c039037950450040c1c030240b445c054828001284401c103840340c096000f8070f0440c004c1d9542c00d000e00024040c94001030301c03070f102600c4080600c40d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 987583821 1250 987582571 987582587
    0x20d090c03051b06040312140d0203100503162d080f06010614030105061e131706100b070303090f08070209151e0109030204050f100b04060801050d0602070b07 70
    0x4010b2081d5240c07580d01007080c0c08249800d803500f0b90000010031041011641100449080c01c00d280b60285020702c0c060310b09102d40d0094007480040c5e5900000f8402e02d068141054401468158090b202510420301030522006061192501856060104031180b892140e811201c00c0d0b40c002d403010b0020344894200341d4944021084100600c00c841c00414807e00944c02da00c100341003002250302c0c680c20070040c0f01c2030703030000300e4019041d0710301051b011009084e10021303060480304035101008452030000b03841c5d00c0031703440f80d18501030f030304800140105000c40c0d10a2009454441491690f560660729045004104d4480003400502d03001811200708802c0c0f000801c9458002c072100d0b85140c0320b002d404c480b5003403440543c55120391041d5240d025800141c0650850540c14184120629920340115054074011207031514000750050400c5010049200800081c1022015042c103040c1400c601600c0d802060007174078461116906000100802038048500d6254000c0b140c8030a07040c01840648480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 987585071 1250 987583821 987583823
    0x1d0303040b180a080708090d0b1918050a02010e060d0c02010209040b0f01020703290c030703050f070819110c070503010b03160504020c07230405180c011101020d090c03 74
    0x18503414910020303010004160700c500e44c2003124a4a455800e42e9100e08031782c080c95071a508071191003c40c0300800d10454440340301e41c501c000c44940c0c820481540350121440000c141001d055541240c0c00421000504480c0c000c0e030a09100ca0100a91800100c55008680d0590042800c1550050510f54190041c000d07045041d201403100c100307054100094068400341ea18010381c031840041000c02c45581144001584e90442415807802c100001e004900c403c580054003490b00000780300d4081c0d030603c1400e80c0a00082854506801c1587d4002c3c00c00038003a0070004402680c1d041c508401d6140ea115100c1c041c40c1c51401562118580989a199a69840f82c03030701c01e528110310703041c10707041c003280107001d0948a05800a0603410b00007080001e402482c031001c10391043e5100420040140b401411a90201249814441345035404002c1a10401441d03007019658081d40d90700c00c1c1900251143da00b400c2403c20855103d0481e030302500a009181b0f00d01b040743d080980c45428402c480b0f04417002d403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 987586321 1250 987585071 987585091
    0x2090703090218090607272705061c0305281101020408030d1a03060f0a06050d08160501270b0c0408120f12100905090c03030d1d0303040b 61
    0x1000c2d040d078040203c0007240e0b800c506810041c0040c424600c1078030b0090602213580b100c02100090302c04c03264854443c50700300d40507000281000fa00035901900604d047c610503003000740310b145484400310b4030656022503104001d00b84c0328904801c02d03001d142580e0440d0488812044115011661042d107581c85040c464003164625200d070012032018000c660079506942e000b9072605000038061070040103050f0010341030590501c118880c60f5414484039001d40c042040725032903820440114405c0341c1441e88101d110741940b1035984001f40d184c0042e11108034452601c0c0007440a1401d005024043c002c45480c15906070300640b103022600c03215454400b50140c4a140d007556903a04c0711640502c6540180b185070b44c00103150145031a41d000003880ba00ea15041d089007096040c44044c3e062080070f8a10752010403029600303111107030b258412158002e01039001003c3d812600008641c485c421004080380302501d6000310000c054488108440140b800000c40796070703191a003044000c3c042c1c107440c1c072115 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 987587571 1250 987586321 987586339
    0x31d041b1106090304361d0a0209010510110601062f15060303070606330e01110109020915010207060206040b0601051b060a140109020f04120f020907030902 69
    0xc0030030000d40140301e60040743c011450941040030408249600c1c8900003102003081d044c071402c003810550400700c0c0003801c2602152140300701e03402111005843d00032a800d5031080e4201c1000d80d0780c40d401d0790304440c02070310314911441020324101c94202003210082e20900c50040001601ca0744240306144918004900b40818000c4469211a0160f12640050654440032031002c0301d0700101d00716900300300010101c0b403038441180d5452041d42e2260b8442e203070101e8802c09401140b16031030030354440c14505000c030300201c892004000d04440c1500d0399060401042c0b1156644229095010403003158000b4044510340c54400c40030a0000d501c24160303801030003414000903e4900000d0401c2c01141d002424140340d9407964011a43c54210300c02d0318429040d06030074a806040d0500c0b8035401202001c02c00700f02e0070050401002146c5040e4401d0451504c100800f507001d540020949054444441c07083c1d96030506810704116072010018040d50040d421001d100d04c0640545c02002202d00c20340f40550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 987588821 1250 987587571 987587597
    0x604050d0521120c030601021c020d1e2c180a0b0a08030d020c031603021e03042105010917030f0a0504031209020103062103080a0207080403031d041b 66
    0x5501400021001004200d000b04200d190000c003d151b0110062040310455103c404139912944070019808000d070708a00b0b0702520160f400801c030910209042010f180041101c000102142070301a140002d03072140c1c0c500280c00243e00c0d41c50b070840714001400d18140c071141103034500d400e1000f82c8102541c54a0300d21464030a0820f030110608503a42c12001c0c3d81021112409000a54000e070003107116800104207100e10046108040e2000324081d500a1060581086400c80386912410000588e60b1060108000790320a602c3d40500400d181700750346070045240d01e007031400342c4030442006041e542c0c1111442c1d8605034106c083c6100b070200c62958101c40d180e2262400441e00142c4025001400e981e04103000400b182d00540280c1d481851300140c090340d9025031140705106609648115002e40720f015082c950301c0b031130407a0132014144045203001c80c42c2c2e03140700007813107113100050501040902d40808020003d40047c80c1c4103000d84240054000303c0110984a18040b464401242d03013008499 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 987589928 1107 987588821 987588883
    0x414060103080714060906060d0609080301060824031002070f0b01030506101d010627080a06051f0338071710090203060604050d05 58
    0xb0b68842e101c3d80382000754001c80d000000307520761110040c0041100301240c4150080c408950f0310556000340d00d8a100605441000501221004070001440d81d4120380e1180c480c000d001c5d0402d503400b042c0e5824202e08101c8240302500741d072150359040900c0c130250b80102400c902654449144c0c0350583e40d8172a50b09000d8000b210b5035000b040512049990304076184000d40b110500c80440700c2c2c0c032020758502d00b0b0b1051150300c041082428840c000c01d005000011840180345103110300898503025800d5613071000010460b0781c00d20f0440000c02254464041d108480f10758406400d01900d551901041c01111105910500119104600c9103a074510b00001440884c1400203085281c0200050602e221a010390300b2100100001c1280303030644140b039603054404840005840b03441c1e92022449a008981025030441e514400780300510900103101d2890543e070751400d802d075214001d401 = true := by decide +kernel

theorem cover : BRFrame.Cov 987410071 987589928 := by
  have h0 := BRFrame.cov_init 987410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 987410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 987410071 ≤ n) (h2 : n < 987589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
