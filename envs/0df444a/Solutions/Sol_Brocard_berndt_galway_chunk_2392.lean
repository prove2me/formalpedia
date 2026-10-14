-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2392
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:34:35.274877+00:00
-- url     : https://prove2.me/submissions/db7bd5da-561a-4b3c-831a-4a16914d3e73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 430035971 ≤ n < 430215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 430037221 1250 430035971 430035979
    0x5070e1c0f080d06060507080d0902010e09090d02060a020a05040611030c060f010501030b040e030901050a050903030304080406111c111006090b01022401090b030312011503060806060a1503020405 86
    0x841d1028040124054141820489010032585882d00000e40362030044510041407010300f00702603d070701c2c036454100b41100d80c410b0401d42440a00407001071013240c01150501081d50061400c42030065041016640050303071000214a070452014000b04076205a01a80061124100e810003c00741c0c100201c402c84100e0000303451a900703001d0b0a062131741100b8803c0500013030904100f4540c41c60700d0711560081d0384021707005501e0700500c2c8005690f150001000309040c000d06010f01c4205440601c0210301c6540301d400303041d0341c41d418940040e0021a0007141818154455980c2c100010501c2141241c00c00b281d08000304e0b41c204501d41c0030b00e8410603050050186040600001c1c80c2000c0d42c001c41011002602540d01c1214000f4074080410000781d01019a410103400402c002c000305e50202e000244060103880c6818034404122003244020b82c44410b00069001901d1011989031180102a0007100c0103002a8185a00007480300380150007a80341900d01c200007410b5040c000d0b030458009240180c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 430038471 1250 430037221 430037243
    0x50f180412030c050a0207030b0a0e071206060e09031c09052506031a060d060815011e030b1501020127020a06080702190503041d0a0f05070e1c 63
    0x4608454010403200005002c07070304240f15828014010002e031900358010341d009080551460b26038403403640303020b00341c401d00540e6103140440500c0103020003406041c0324650f42442400500c0d2100496889031301000101a82d0740c10b10220398004411100043c88050268144086104a01c0300814038140000d0051040d540d400340804003248903000c1409801c40b000001a81d102c6054040d9845668003c0c91210f640c00c000310700e0b1034400d02805030310307809000014825488481803840c00b0000100b9a4540035400c004004170100140b01c0307c00f4030181400d03c02082e144d41d552503000000a02140c030001790305440300107603034401d51200100c502e841600000c14460b40991503000700303242c042a8000d140884000c103100e4090f40c4003a000316250b500519031a00605050031108865a80403100c600040000103000308ca0500c1020030b01c500e064101e141410f18206180403601c4500e05103a00506000400c84030036005062354420140c00e6940e00903446849440c0c100080207080c008100711200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 430039721 1250 430038471 430038473
    0x703140c01050403123b0f03060606091210020f03011509060f0302031312110c030c0312070804031b090e0d02060a110403080a051c050f0402060d0f050411040b060f04050f1804 77
    0xb90f049506c1d08000341d9030381c0400e220580034107480340c40407601581c11131401c0010b51514207100040010010103001519000c0d4562400d010990303011480300c0e0487c0350040014002c2c00c582d1581d00c01f11884034140302001e07510300800038226a01c2d0326160414154088005071680410682c1c8045007903000b40c4007403a1144501001d03090140000f51070f10070303110714118040c46040003c1d0034107011400034010202540c40c5503544030668040d920484400c0410f210000005410013203402c502c04405078860522418101e901c0200d4031124002502503010030801004160045801078020491090100d0003848411100c0c5640c81542c0c0003c20715400014101d852076807001c040c2c10601801040f50500c0f0380b00d9200c2d14240c901c1903405100f0501018045001031604600422072121240c5020500d51618660901100c0f801ca9090b01c181c1c00e0a107801026250030300c80d09002d03200844840d81054400801c00100c1c0c02030380103c2c0e010300b03104a030032120ba40c0d40059041d220005400110064602 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 430040971 1250 430039721 430039817
    0xe0c1002010f23010311130912110318010f0504050901032306010803030703020a0e0d0b072007050f0a03121206050406031e02120703140c0105040312 66
    0xc036242c01c0d4040352820100701944403101000c10302600d030804140c1460703400e503141c903240c43d5103289040d83d00841d02814800303040841c1c010754074814060913600c0710b25404c02c1000781600420090108441d0400c01c0510000300342003000743d42011081c40c0c8503400b000d2001060f03445101d00d0300402d5200c003500b0000003c202080701c40814030004081e1801d4490004c080747c550300c100a010755001ca401c01d02c005a0b00510075400383c000c8045526180c04070044200100e00e00d5104050b00703447ca060301c032040000507a0460248d01c9000d0400311401c0010320500d042a0700c82d02180200e920a00f10300040320210758513080680f000e10b82140c001e000c41c1c0c1e951040500010901e40141d03502c0c07814803600084a05d402d2049004494200d141032001c040b48030006000d007030340c2000480c1e10003101014082001000c100010103103204003402c00031814807035403981c46c01503035401d040e0400904001c1440081e020210060113485a4181b094510000100305441180014400d09015202c1c1000003d81c4603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 430042221 1250 430040971 430040981
    0x30f040809032b0c0f03030207020f0a080f011a0d03080414150403090e011a090a0b030705090a0509010614030405010b100905090a0c0e0f03030f120103230607030e0c100201 76
    0x20f1550420b01000452030002d6411102a401c09031001480b00d01c8440424026002800c5851008181d17580007461100003888c8000640c114030f641d0343c00384620304003e83d001d1150850240345c1a0680c1514000d5030000303644400d01601c01001c000103000410b04000109103a030780e1240140c001e603800514288a00030710001c04841c143c0020380b8000e00061028001d10815041e140780000400e10b070241000c07182216840601880c0d00b100d9041c400143d09200d01c00518020384107030303a1380c540d0b0360035402c00c08c008009540c002912900c03c00b00104012a04455100324070100a06021b03141d030790350b06007070f401040c0410780b141c1c20402c006802c000385179101c0540426164122086e40c99611070070003032003c44030040510404250030742075401e00351400b41e50102516100400301c03072401c0d200740c0c03100c1c420743c00c004000c0b03440e454010018820007010000052604820031135110f05540000303e403d5503882d0141000080c5031741c075110340d02d010509120100b0114000341000d000d1015150740240241 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 430043471 1250 430042221 430042273
    0x901030b0f0a0e06280909030c0f0803060a05091e090a12180e0f06010315050a030c030209070813020607061d1c0509030c09060303070b0a0605010f030c05030f04080903 74
    0x350a0940341a160a200e41c0c45d0680421600c000c0000c141443d021400804034071105500b44549030521380000b80950300007100b8103114540c41520707070070900e003070040250041e0482071103007030381c1c00c00c010403071941e4401c00c0e00d90400f2902080f070549652010904205044101414000044000481e00e640140c4011010295494016240c5035550044940c1c0c502c00e80e0a814038072910008078141d90701c01c6d0400d554000388240e11030f0b0600d60300d0300001d80003451a4400c0f20741d6000e0b180d040083d441d041d00819442251410010782502c2c1c541c480000c21003080e08024898440030170f1140902c01950f0000c911040c2d00320100e1441e01c2e54200f143d40d0f40042e046004480c4d103076060181109441a005d80c0c0010001600400a40741c0d880d0800c00d0300c20000700340c1a0540700c2804040003240c0d8450b0081c0c000d100d5400700080440c201000144440d0200071101e06041c24100340e2550305603c2000c80b0b6110f130681041506030745523490580000c5c070420344c1040c0d03d44102d626180c000508451100043c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 430044721 1250 430043471 430043479
    0x9020403021305150d02301b0d030c050a0f1a0108010b13020d1503150c03050705120405011e0c090509070801181503080c06060d05030901030b0f0a0e06 67
    0x410601d030b414006682d012156041e140c21440f030158403904003d44c05a88042c070003020801107022042c81c1d00300c0c8890101038903001910990b0841c50301c5030240001d01d1111500325807011640300b000b007c1208044101c80080410000610001c10f021092101e00c040039400503e01890800605001d0f00005120141c107200316400000000d1045d030502c0343e80102000a0116420450f0f1800c440d40250400b00d10489000d031221441021030081d0465407001c0e603c0b90303038059030040203100c0780704c11690b244803000281842c000500104a0308003041d500035000c1c01e15950b00c240d5a03072415901600141101003200407010703180240c6a03410f40c01440f40003a01e40c1c0c401c1e900740d03654003c101d045402a00c1c804042003602005203c11030000c2140c0d4590011888007142d4882c0d2440c4a0010992a034401d80341d22001080c00103c0881c01d00015800c40d00c200ca0150019945032a111384038424a0695030605035a054070f80584d84842c00c400281d8000189801182641d803200d04150110849285100b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 430045971 1250 430044721 430044739
    0x30b01180606200a020405100e0703020414040c03150f080f070b09090603120703021c03200901091a0a030e0a05030a1b0803160206060301061a0703180902040302 71
    0x800c80144100400c456680e90383c1c00032100655001c003a4155801000b0009020f040c103000c2c00340c0c469018650080f4151104008403a1500081081214018001408140c01003000300704040340040440c403154000c8900150300503049206034024040a04c40b8415446d81c1000003990f50480c110b080c0c101c4d00f09070141c807410103d04011580b10903e42c013a05c5003000301031002c9440360800b038118640c030010160031204500e015400c084c01c0c540018204800681c0582c40180c42044c501040d502c044242e41014050b41040319003000c104182c4008050103200042400c8090340e11600c081c070f0003054160070404441c1000c80300b00c2c10f07980c0b050540301c000c242401e11030a0f181500041001926400c0006541040740c040c40458000b54a0b190b40241d2248401c091008034000000843c06421034071440b2460302038411010741040710041c03440e0301c203901d0014100540840c0e0101c4110a17181020301c6a507540940c6000d4944038051084410907204414021403a1001035000701300b135170b000f2218281 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 430047221 1250 430045971 430046009
    0x71e1206050d0c1208090306011202180603060604090501021c0e010b0d330f0906060503070b18060d09050708011401050616110909011508070602030405060a02070b0301030b01 77
    0x810181e5180000e003c80003020041000c40031a2952220407032048103250701d01094603000a281c00c0085e0041c440c80c80d28420041c08500d00201c0010301121514002c0707100d4508180041e0311000014801402113032540300c181c040060a6040320080800355880c101c1d80c0800030349210003011440d6100c030716580b0701012084a468a000003c00d02d80d40180000c09110001c18440c42824004205000c0301307014881d41411000e031805041c11003100101c0000d4803602905151066070500c1d8401030184d00300d804c0c1031141010400444100d140f1050320040400c1d01c00004c00e0782841925a4801c50780e04e003a2a0f0410804049002000c450754040240101104823003140c0303d00c007003841034940c002020440102c09408407102c1c00310b601e000c2e9246140c598100000b0555803c0101c8048106035910100c000d03000c0311003039114014020b00001042003604100d404ac2d60b074030441c05514403490010070105003043c4200103200c003419406174030341c2e242c0d46e40e481e1940d030101c42806a404040c001c440c04003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 430048471 1250 430047221 430047229
    0x190e01051609080727020405060f0909130201120c111507020607020105010f030311010f0e070611030735040f0e090d0210180f1a0603060405060f071e120605 69
    0x1c00c5c0d680200b85200c00c0400c0c42c0160b1100822408900076481c2c080c07000241c5a44c82d00e01901446000d02101c1d503032403000741e0070440706030ba00500010341c0d1000a0341303110160340d00c4000e400800c0d504000000302d10ba000e00003038450316240114610707584201800788404090540c00c050156100d5003c9030b111b40c0781c2c0803090b801d9031424082c00c0d40b009443c1100704082441481d6132000c0d6503040000298010300d82e810b0390141c8840d250100300c0d070351001004000f080c1c1d03c01580d820a0f01000046e50406c172059580e130002500c1c045506175040418101c040d01c55846024408000900d04a680d50b41c2d617070b92400e40056030092180300411001d5900190088030042213950a4407220f90180209204020a0703070000c2c10404010300c85c01104010283c005008440c1546000303008426501401c011034400805050004200034069044107013400009580068110f030011102c030503407540d0395289542101c848007081c41c01c0c192191801642d158141e00504e9502c078072030804000344491500c45d0140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 430049721 1250 430048471 430048483
    0x190e0c07030e1021020c0a050d1e170a1d0f06150315180d0801090518061810020307030b0f1203180f060a0807030f09030503190e0105160908 62
    0x30404a0b4072902800d04d1040106070030700d21842c0401c0c005042c80e0799440198642080714104a0310f50744070356104d445581d0060a844640039212b284240840f800800041102542000841c941041800403c40301086600154520319a440701500100c074600481070f0b581020015071146030003171001044a200f400d00d07001400c0c610140003060015258031001c0c440c080000c05000d0420000e440600e4482418020841e11441680d80c240c910f50402183c40221000030340714281d4500a4002440701400125070b40e580070601400c10581a0600c0055a0034210544414000c040c80001004903a07a010b62041c14000010760b031000c4141403003000e001070341c8003110508045510922900701c2240c452048101ca0100c00351040c2009040315000c100b03290802454440441c484108103c1e0565152164104080006c403040c08514996240a001e80c80007a20300c1c090210224210709402c50540c110071802110300000304114a404880341d080340b00440394100014550700c800103800e04001610f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 430050971 1250 430049721 430049749
    0x1060804030804020f041b050715150501050c1501030f050c030c01090510050d0e0114150d020103050606070c0f0911030405071e08011a040b01030515190e0c07030e 72
    0x2d640740d588941c1c08209019441e40019540a901c0d03601020100c001c80c4401e03502c202d0036444040c1c80f220546480d0401040c0804903150b410b2401015403042c6480c409188100c0d2070030308103259500310401d41541054822403522604c60b4061000008020301d11003131020b214040c505560071056868101a11805000070060004007450020300c5985029101503842041d00d04005141c41002e220360f006075615004071074400c2e5950400710740440c0b0102c2c015a0f0010202000140c101a540005450480c0da600f0203130400d695280061801c2d2100d6003241d03c107580140d40310070170598403041c812000b10240900710106041142c9040c0001c0b07171b1400d0303900496020300a040c07500c0c106040c040303000301c21200c03040c003514800300000b90118080c0302d400c14030b80883c041c1060410301c50301400f05554a105145042525041c20060782d0340000d80b0f14400502c0480b040035554280014207262603d50341c006c500800080030611103a20041001400c882c0d02c85c1c5c84500100c1045010804092a0a09 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 430052221 1250 430050971 430050977
    0x7050d05190605010216230909150108070e0708060604030609110f01030902030304030f05120c0d080f01141011030c03070c0801060f030303051e01030305070c270911030d170106080403 81
    0x4d0511500c03d602580d80c07150021447c90b10034886500c00042c880c6c00003611600490b401c5074944034903288165aa450142144500900149191407249002c004009010100b0090020041001542c8400c01c9030010368001380e0a020b10655030a02c4c00f02442c056407903900c01d2140940c41d0b03801c1d5000b0f01844c00580e0b00117014ad400d040c51030322206500704e00c41c0c000b120280a031400c261102c84001c000b8041000840b030007406805195140030700361103000303880605991034080041107803490084004c180e060069510001c60302848000390b0307190071192032040c02800702140f01c00c01450000041c00c401401140741040c1c00c0d9031012801d08882c52400307040c414095070394080c40402e0103a0000b40d0000c40d04c6080c1400b4415051444540c0396080e00100c0000307000103400014840181d00d80c0c4080c010b850140da0036118410601000c00c00501d40c0c2c12006c40c0c036207919001740204041c401000400140039a203620009070790042c41e9603145464500000c40c05000480d15601c29550148201e51640f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 430053471 1250 430052221 430052263
    0x5064e03210c070807080d020c03030703060914150d0b0109020a02061509040b04081c050f0a1a220213051e09070e1c050105061002011802040507050d051906050102 72
    0x113111084240d0014038107580306001000300021034a01c510003003224410b601d020315244e085c110001015074100d607208036411418024031040342000045c0f5503410a0710010506950000e00c400b00303829040410016165081d08030000501148a4005120b04c45480d0300307590b42c503038a001800b80303110031000d0180d81091003080001e00141c0d28490300364001e80100740705414080e20703000107203902c0604210b030f040d1070303480d4000c1c00348551424002c20f1700104010014070600b0b03803452400c108540d4600d80d00c1e200342d030342c034400c0c100100c41000303a0004000340680a56464192803006040d07040140310b100e0042888140190b825503029904209920f401050002c0c55101c0c02811200b40c0007200c80d003540819441c404c07030916400ca26840b8030040c4500000315480c0360400422054614145a070025a41010ba040e2817082560b203108071580e80c1245d0018030ba4603500f100310f800703001d0090020b80040c070b803105009884070900d010044219051005003c0c41c0d49981c012030722840101815034101c0454 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 430054721 1250 430053471 430053473
    0x415080115110a0f0f150b0d1101210624021207060609020a0206010314070e011214070e1b0921011107060209030105064e03210c07 58
    0x40c0ca9480d0a82e401c00201e80708024580c540040c140c4140001712040304070400c0c554100924614400da12085046081084840b000080313440581c2c1584020f00c034203034020442c2d00c140e019110740320340803240842d1415121003050080d0000c1c019805011055540191001460004050304280e14541c030b0380130f0700880a01001c0700000d6040b210088901d152030382c0300422164410b101600040b040c56004240c01d500d103061030748612190400c0d070038407900003c0702400704c00100441d190440b114002d00d102c41c4001401d20409081c4a201c405029008039103001a40d6043c441c421030040b1842010329140700841000b04885108803015941c00c01142034030b172280305100107100d880f0007144a00100d110300442541103d40e5000d04c000300d03202036000c205960281000d01c40d450b40f101055442c6a0002104510340c1c65206851054107480c00740034030394016400e501040c00700c406d5084000c2c45031a03884091001c3d2039800c00d10703a800012a4066400c507282c1d030b50303445042c060326510360058582882 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 430055971 1250 430054721 430054727
    0x50903070206120601170a020a09141c1502070c06030509031206120f0304150e0d08160804050a06120e01090b0109150510170108060609060909210415080115 69
    0x70102e45c140704140103149000780f420b50b000d80c800c1c400d0400042c0d40341c0203c1d50191988400d90031048a0f1031081c0f60644441c2ca034010801d01d00c22003204900311701020b80c81c02c942c4003882041c0d00720380075002040f80e20800c111040c5140c103031580b6880600460340c491050035501c0c001d080d44070720158120804a5824104600343c08100e000d500305483c2c2d0100c1c01c10445207142e001f5070103a440c1036810800d040d85258070172100c00c50368400f12280c03003185006480300740c2c03207000e64940803081d060241204401c1010f07060031140242409004108115540c2c400905110105101c0e07201090408681c05c401d440c040c071500245540c44503040750964248424400140f64104100190200304240400d0595078402c40c9021106159a041801074407880184091107040e40030f4215035000e04140225903492100355a0b00000640e05040b0a84c1c54005841c90101d000309061014003101240545141c0700c18001d00541d80c50007160540000000710072035800038244501d1000e40d562000c1e0500c1284 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 430057221 1250 430055971 430056007
    0x304050c060c030903061501020f0a08030c090607060f05040303050a0b1e04060e04210212090114041e050307061418010c0206030a022203050c28030b040204050903070206 75
    0xc0b01204407810000030002191030142c054902d5240c0c840a2a02c550540d80d0400200440d80500c0000d068042c0b0960307130709002e9000141c034a00000d4004211110aa1217138000e03a4070302e90f0400d0090041901c50400303a0001c0a041e1342c01c0c0d000a0400000802c201540d00a008450101500301c00344462505000c1c1e01072000c404500780c1c0583c90b078500088a205282e04c1030300130382c06400d80c038841c0810740030800103164090a07090103540247d544180e030b4010350b100b5161000d00c2803c02c1812074a80c1e60361041036200e50b80014203445a49142024034240300140041595015012030b40310300e44862050710321141740190250650410000307a48101a046020142d501c818103000c00c00d20700d00d078000766854004a034100f014550100e0400304401005107106106051b1490703141190b4210b482e059111564400c00c28000c444017451240d401d00f0300c044125845112242000c569501c0c0d01d00400711001c2550306a01c264103080108507842d0022048499607540102168a00120180c003a400c0340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 430058471 1250 430057221 430057237
    0x3030909071b06230906010b030a06180509070506130515160803040303062103030504150f0903020705090f060d0f0506040b091603082703030c0718020304050c06 71
    0x4085050b8000701030840200440c1118401d200100300d0f00c1d800300c483c141040c1662008201105048207000c9100f402203a240e06491040c00301c0d998039514424618054001a88407040502c42c01c0e800d0005128035500a90142102c40e06860f038066a40c42080303031601440102c010408041d00f0304020914006030003046000039140c02c1c81c140f440480e00900c12011143e01030f1503181c6e0020402c010903505102e684007810718550512920801c80a0191441020707200041c10f050f0b031240842e090000100052808143d15002840150780d9070f494607000d090352103021005403003a940c0100741450404e034128410198801142d8082e980d400401c101c00b4200481030382c3d002d048000c4900481c00a00a081c0710394060a01c400d06d80c1440880c083c41c004040a42441c11000c0703d1003880010354003c1290341d4070400403481d0034080034030392a41d40f111441c0f4807170395814480001e9464001401140282c1141c0c00d0301d03a1100d081c00400604001d9100454006006810184818540d031070014040e00d501c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 430059721 1250 430058471 430058477
    0x3060f070f05210703140108060702280c08160602010b060307140f07030c14011a010e1206090d032a030f090204050f190c0206160c05030a17060d020303090907 70
    0x40301c1d0101203e042d030482966040c0010341c40d0380b11201840580714110340106a40c03001010b1900e0895002903c1e4524401039601c0011305c0c500f500009030b044403009a05030740120105d094503544c1c0341e14a50b141051182141c561100b10b4000030414018880c140744180e015011034070b50340ea600b03c1114842c403e40b000081c1c40d1028400702c8440c03089030010346000e501c2600c0340000083c2c0e504250100510710361002c05140e0401942c40e00b0002d28176588015a0b00a00700f84804039103038000120304890203161131078244200b0080011945e00040c1200117103045803400c11250395003c040080020404030b160303e0309400c50318a01051032181e40070070400c0c1403800740042d040459030b00040981d0016904d90070250309010500602d2052069a4440540e03803020410000009150103034542c58000d00d5a00d500702c0f0300582c0d90341d00c1d000b00e00c00d8a039140e100060746c0e0b49481c20070000c0c3c0034400c0c06424241c040d00d910f000907418108030301e106030241c2d0014011410f1510940820070903641c020005410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 430060971 1250 430059721 430059757
    0xa0c1101110f0a020a0b04061209080d091a0a1103011e09020d020a0f020c1e15030f09061003080f0c0a0c080f01050609010b121b0706050603060f070f05 67
    0x40c19041c0211502040c2e0345002d8590384030741d40108001a2056001020040070400c42046403d40241030100c1209821801254881c1141080c9446000b40b050719401035041441103070030449480c8000215035844441000c20391121010729084400080403070030b054404100600207078201c0c0c1e00080100e00744011501042e611070101400342d802c5425012075558003c9990100150080151949540c00384014410484103000080b104c08070343c2c91108400f40030002c0100242c98035400030783d0000c009a0304075568102050074100c5000d044414410350300416010074854940d100a081c1100d0b0098035986c10800320301c030351088661040800b07241500c80d40305200c8c005640b403a0104014035444024042851108521600790360000344418482d00e0a0301c01441440c040c001075840d00d2401c1000c04400d50fa8911182140c900b03038050101080f60b004c00d8020820401c1c2d00050f10030b00f801d4080e174840d6100c0c9480ba0041000c02d4840c0004200c0c90070500d6016440354004d44050003101440000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 430062221 1250 430060971 430060997
    0xa27091a090106080d09170c030601180204121112010b01020a060216021f120b03190302150f011401030903020715090f0308040e0108030403150b04020909070f02010f020a0c1101 78
    0x4178104000321400041003000d001003013540082d650040000107004013408070806040006a10790105000d4981040109904401d422500342c1c1a20b01414020070380f51840c004504054628102c850300031807090440c903030b520f000000d040c02120326032075040c0c00600014003156111800394100300700140c00085100d00c140050395512100d071b00c1c2804905009140f0b9082a02d000380428540303200150a030b400c0040940c126200003500c00810410305144040e50036051408030f00b4144a20702941802c24480c0501174055094a4401e040316000074024041d020700c20300540039a07600c40e130060b0141c0c120030405c10198044d90006801d4400074600440d8040d02c80b0780d03002c10101c05400c00c0d10b070b0610114044c0107031550b0500017409440101c00039400e0070f10350f40c0e4a50101840c40c56500303940c0d446141400c2c280c2c407260181e4007015801050f1121754071b00200010034295450f401c2200641c00d0400c1310a400f2010b100301d501c2008140d40790300040f403064a40d8828540c1f5920241e0410250781c40c461 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 430063471 1250 430062221 430062223
    0x52506032307030c092108070311060a0f0501050405060d060504080d020a050c01060f0b0a1206090615031d0c0d1b0e01030c050301050114010e0f0a27091a09010608 72
    0x50701c41c021039100000c0c40044a03d00030b000c107440d41c10071100b80f40c06d150b00601c0040c0d520704424000343d0000c02030742d490ba01480c08032240d01090310034046c90f1050354140540c07103006400c25880480300c20710030030080c0c0e070b034200b04805e03500c0940e00c1f590045224802c100109906410240d8018066030005280c50880000f0740c040703034064641100006c0300850100320054080c02240002c03c640c603401c1a019060036101d0701c051050344281d02c203000d40011031205c0204c440e0080030041c0b04901040250039643c0c0f96505921101130304c00c90000b440e21b051000050a440d04200c554112000144200402030007032040f290034140c2d0a4031940441a4042c542c2c4503610782c3d0301d000c1c040c5600d1b800c0155141d403810384201034241c0c0102d482641000018404d2100300b41c0ca92400807002d10740041100d04400106042c1c04400349030350b07000f0001c4000031403140c0c82c0804da010202240320f5601c1c100040b00c03401600726018070384014210400000c9400110200207012604900808000104644c1c1c8041603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 430064721 1250 430063471 430063541
    0x3120201290307090903140703092103020f010e030409020c030d0501030c172a0f0a0303020102270d26030f010312032003090a05060109020705250603 66
    0x203905850103a01590103030b030406114243c01003481c0c14040c458160b0744d6401515034982e8982ca00601d6002240000c280f62060081d103000748824000c45404031015542c03896071441061003500940700341002d003007140d00c051245011855100f40618142820310b17034418042e60240a10682c984030610080c2e2060ba2144101c6000b544200304403050750f4a00ba143c6003075808110108070054001100d40e0940300710900c444482c0e50182600d0480341e00a030000280c0d111660721a094004e030fa41c1c90b0100826805500512461002e80d03101003112001c20f58800d4440d400740451500800200204030001d814442c080c0c110354100d040003d01040c110360101c0858000b00c40c107908103070b032810040017407240901c034401d9031111520b814002c0300038404040b452600b003141202e4005400000140c203144060041050b0154810240e4041307580d12940c450203500b020b1820740742c5020b6008400d009030005020500d008100d0915591940c0c50910142e0080c14140074855880c2e001d00f4100504881038020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 430065971 1250 430064721 430064771
    0x12090e0a06150203040605030103021c050303040308040606051c0b0702011d16050108060915150c07080601080114010b03090304050904031706040b011403220f1b060903120201 77
    0x200c0c2880c0c00619002d2000e80b0702d4680541d00100028015940e2000440e410b580d01074a51414000410040002076141843c01400500001c000d01c8100369002c50840d004d00e009000600001da1107408001412189880c40c1108907030900c40c0c0300c0011191014240c1c420840d000000340b4004118010302e2600745014004a03941108211385000310103010f00b503010b02401c1c0390803840c501c0d03e200861010040602040511958100c60807059031354103030100011080c00202c103072101384000e9020b5549455002d01d041e030307004220020800d03450511405070152540020348006034601110300740298005440741e085404108400f05651b103d014555004a02c680e03105506034254030340d050003205010b0402403245041c2104031406031b030300003003c0f02d2407410200c4c4141d8a03210405603c072890a0314610442d098000c1d00d0703441c1801381050117103003400e005840480380d5134034101c3c14441249040c007401010991000301400480c0002c03011b098540f51314000001e0101c2c41c003621000c17a0000e6a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 430067221 1250 430065971 430065991
    0x9140f0c190b0c03040305070b0f25210207090908070b040f020406030305180a0308030619050301050103051c020106030203070b0a03020d3e0f3a0c021912090e 70
    0x45c0400410400b005460000c044c0c4058503410020b03030516030340103071086c0c01c164003400c141629003c001a408080903a541c50380400ba00f400260300f45801c00e00d8280020300b103400340c0030b103590004040c645d82c01070078039840d40080190301c0e0140c0341d55265401140030340f0544140c0107140c4c01d0700040e102c40c071800024500948035a503c4005540075588a90842c0b16803034011021403908000140300700003642d81200084130f054845209000c2914040e0001d03600076a815030030708000005100002c40d280c3c5104151580e110720000d6117250507400e0305d01d03a101c000d415620107003080000620010240407506d005141c00351078480131020b05016540380c030350503a0f003a00550380e04010070180d142480f000018042e01190815442081088090082c004600004030740050b10036002603600805100800e08002c012120f4160fa005c8142d11032040400d207245039145c5102610028000078040e90456690500d83c00c41080070390343e10f45010b0742c0c0888601800105000880c01c00300304070a4a00c202c00c021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 430068471 1250 430067221 430067227
    0x302060105090717010b09030c0a0306050601141207030513050f0c090112033f0c080a09110d0c0512030d0614090103140a060f09140f0c190b0c03 64
    0x1040200c0c09030007815050074020703003a4041c042d4104c5040c2c003e0441c0c140006041e03c41c04039002003820700d204126060b074451a41d480101c10000d25610031801600700303985e160301c0c204004c00030a0b0307688510031010741e0b5100390000182159200b604100c0c3e12000b40030b981c07041d041d0b40e5600c452411103643c02000147c0c1105000a0603820224a860f00600d440c0c5001040c49040e0f40b009880b00c14504041014504811400700340d60501610140c0c8141a12181c01601b4902c0f1202c3c00017882802c03a41b600054128000c54002740c0136004d155029908408002101d148203410419101b416020480e110580450002070310f0307845007002c4002c2390b41c10b80555951810124400b044500a4000c0107042e1043c81c4403090507201c40743c081e41500d501450108070007080042d0359242c8000200700420807824a0041d09403101c071900241050307407003207581e0308a495581072003544405502c83c0c1c0f040e0560110a80d4490792403c00d03082c58540c1600c2d4038104825489180d81c10055004100c4070880d41c1c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 430069721 1250 430068471 430068479
    0x911030412030c1d060f1b010b04020a0e0d141221040507050d0f06020d0614030f25050306070e120a02010e04020703020c0406060905101407020405040c1203020601 72
    0xc8000140c1e100703014902000640200700014001000588450f503204024045511142e12100d00f1900100100d507020b64440150304040942006c1d1140000b105500340602c1044a08150080d0391001c0c12a44402480881030410300c03000d000c2444068690a11011010412610601c103061124201c01c240690ba0800c0c0282c107105140e029012440d4150441e081202094001c5601c40642d071081351141d01001c642d041444645115841c080d1200d44009803065130241140d0000c402c40d02c844105568001d12401016190404a00c00b1100b82d0841c2401c2c10542c0010403040d240c3c4121044180190360312080030a1900104565460101d5040c0a19a0203403404981c20b05042e004c0c00d0080081103210740c0002d02040c140040c0314065a00841c011080500900c0400b103404009402003102959400000b420300d078207486a18082c0c403061070626030346403082e444440600c03501030000e4980b201660030300c4000d110007881aa0101340901000c80d6603001c20b2005040180658020030442d414 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 430070971 1250 430069721 430069733
    0x71e150606090e01050607240c260403090e0603070905040c21030c2009091c02010c05030411010c38150907020f0708070f05040507050f030a0609110304 67
    0x807030f0802001e03098180010002965188200c1303214507807051144601c09140a9642000300004280c202880d0a0440c0442c281c1c0c0d010f40c4030400c45180c800714201200e028a03010583c44e10a840c0600015a810701c01d01900c21040800360304210050100c80c1455501e40312072080352800d84084801041a400130004010700c2a40e41546c00391000601007607687c20340d40074100ca0810640289980301c0642c1080d0301001d61541e408181001038500c403094500070000c0340d103c17030110b51001041e6151060a24007548140f042c04002c11541d00c4491568407030707850310012a603a42c54810704101e0b21282000009204900f64082c1c030484941c28440d00c003d20118180d20020500e800c040450002c040111014816602c1b401c0190180c404169940b90904100e0429810501641c098407802e800048d00303031400036501c41120340a00c0c40c204d49545400c10401501c200766800c400080c401e0100c00485080c0000640d0001c14003940094a59500c88102081d59540c103040d46810340e0100400c0103102d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 430072221 1250 430070971 430070987
    0x8070b0c070801060803042709030f110613080c0a0503041e0e15040f0f0e0d11010501030b061203130f1502010506130906060e0406022a03071e150606 66
    0x820001d04c24942005034155890199101e4001214881401a0144064040340f2901c2c104049800d0080d00017a0030b0241c114600d9900920006024010204002001003402405466040039455101300306881e00640c5805c54141c080940c020201c0400c00102c00f000140002d000b0301401003031190594288040e44805503200506c182840410000000f034644040039260300200c4000669900f810107034802400300f0600810b840303150100000301c003800004c1d40e80ca01c4a050f690403854448400085007071b40e1003844000c10140000c4007140040c9810b100d4800491180310440e030401100541494000c260f56001c112480440c0105104812100340380040341c407030320300080c0a142060b0b0040741100d0030b1751000700c402c1559140c5441c1000030980042c001030008150b11010342c01c1c58206540207500090303035801d0000102c0003440160201b40742140741c030524103004d54241289034035105401310030307004014a4400885074140c0000d14000024030703d0145810005400c50a049001c0c0c00c4c0d40d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 430073471 1250 430072221 430072229
    0x60302220e07080a0e031b100908130b0c0a0206071b1203030608060702101a04110c07051816030e100c03051f031106120a0c0906030b100c02060408070b0c07 69
    0x250070542179840e201e20000803a603103c030018080010046983c5249420209030300c03040007000307081003202c00c14899200003a00d020801c40845051940c0c0d5035402c4e0555104480b2451200d40004001e5030144c9002b00c041d00ca60382c0070300450440c2410410f9400a402da50b5084120061460405c802c00d0580c584212006400004000c1c222428080e03006551141c3c9400401041d07625884d8a21b0005031580c0230710744841e4040c0c414420800c0322441298207801c4654005083d2041d50030020340d51800b0182c2d581d4545c0a8020010a501d44060344005446800e807441c0074141c81354100440b0034810042215030703022003000052183e40042d0300800303840c00a440a1000e024820200c1500c80e6048045811241c0c0301041c040e0410001c1c0206000303010701c14402c034086509200f0003120619a030051288001c0950720802c086845560a60880382e24a44450700003100c101050340607405131050203102e41c002040c45050903614202e182c5407144503001034840b144089000d03100044208246000741c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 430074721 1250 430073471 430073491
    0x5030702102904061d16020105040f081e040e0405101a01050d060e04030203042c040807050a12020a02041a0325030501090b070f09030804060302220e0708 68
    0x284015055001d52a82201031100b140200c030380d00240503030311540410014800c0c5120004d0503c03000c000340002c07034011941841a1034550a06808040c03040c403c03544515481348140c0d181d00483e8461000c1742d00003801314150030110301781940010300450040d200074807101c005500e0070b00d098070b0a9403c0103550a4202d41740b0303041582c101004180040340110008081c0b802ca40ca5201360503000780600300540c17015280c404004180014158040010302c19210090701c8101074001480c98051000c0982403881c81075207200380420b00142600f4001c11840d4080e9045554400d49900c801000844070001030025911142044c41142401e0043c000c060341541d050390720b165100d10209403501b066440b00b802030229804c00301c06008030b030442c42c0091a0444003c008140140c0f5004104210951f1503c000c646149162069103104d440b4160680c2e900141c0103080620b409001c1e8003075041020118504031400340c8941c0140b00c03050859005048002010445003003114015104d820058900034030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 430075971 1250 430074721 430074731
    0xf0201030b220e1612020a0807060906140904060f14010507110120060109060603050c03040c0902160f1b06020303091507090302030d030501090524060906090d030503070210 76
    0x4482d0001d801160b500d1201c507008034042c1d15254000d0300b0211100c0003031414001240000c180383c41040c8445035000c0c800d4481000950302c0e0210266600ba05201c0c200c0003d08142050090314894003c5508203c0c41c190101e007090117020005056030003580141070f075040045400c110081200072032180203031080c01d00c5850001c040d1034100c005024412124103021440f0303482101107010b0201ea42d0074025600581e003007561605227a03c06026580324900000b0700344000300d100d80c2c0292040740d004a0f80008503a44003071500c0e144401a41100c014080001a01c81441000c1070400780c140c00108d104184052920500303c80d074170b10211785600918115801401000701a0034005a41c078400c0e0312101c5100c0700c45c3d4420348111840c4032180c10082d014021032064940690305504483c0c1610451881031006955501094480c00d80c948154117030b0480c00d00c2544103032700f45440103011250000e81740074505600400402c140c5240d520088000400c0002081415a07040c040d0034455810742e003003804 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 430077221 1250 430075971 430075999
    0x1020d030c140f04080d0c05070e070503040b10050303040305070918152a12060b0901050403061e0c270e060913150608160b03010b03070306030b040f0201030b 70
    0x10080250240c2c031a0700340e000107680f500c8281150141c4000304014070845150b8000c40e040101040071005048459102e0700300d000c918011441d40c107a01c50221540c6981c295501e80d11090300f40c43e4042c00003546032244403404221a20180003c00c0654014001800340902e000c1484045940c00c05000100030f00c00c01a07040003440c2101c28541c80400b1410204566070f01140e81c4820412811845400e03414030401d40352026045000a40c1c1c00e00b50f014104030060350ba8960814503c240361205001550070002480003c80c598440c0c1090880d0926446005004e200440102e42d0040e600700041044400d840700f040b60a00d006000265080d500d0030000b500c0c0602c2903100e90030180221344916111000a41060942a42c80f4115500042c50710070511040030080000c150078000e280060082c1c4d01d400b581115030707851070780c00c0743d00c0061345615517868100d908400b13030006050001010b45034a0004041188100d20501035409600020b0005400744001340445031a01e111318010804051500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 430078471 1250 430077221 430077227
    0xc160506071419031e0914040f0e150906130f030c0501090b0f01141206160903060e01051009090b07050d1131080705060d021b010b01020d030c 63
    0xa58410350140c000702c0d01d588202e510505011516140c0c0310700c03803000d441040c145907005401981c2a10045800d42e103c005c0070504079400c1c0c110f4001c0a6000d1400003994400742801d5101c0c1121401301640022500c2408200070300b041d42a02071040070700440070030310507a0f41d405d200701c6420144194510429011642e608121081c40c0100602803000740108030003031107020341001c0740d42179100140c0360300c0346000302c0110318071102801040c988400a05d0003210900303024042d9040d442542000b40007660300d48900030f184c008000452020423401810000005420380a0641d03000400c000210f402d141c428000040f0040c6035008400c514101400301001c00e8014002d55003202e40c1d46007055076442216600d501070701040d03a140c44420300000d6800022040d90900d80c00d001d80480c2c01d428040d04c0078070301c9440004940240703146504410720400040c602038006002400b129140941010074280d00030604410a0108080a945606d52803103d07680c184001c8041048908040001d82c49540b402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 430079721 1250 430078471 430078477
    0x8090f01110d1805031c0806040902010801230306040807021c030c260c0708060601050304020a14012006100504050115050906070c180501080703080901260702030c160506 75
    0x2c10180070301c05507454850007a03002840302030301015089440301451340c910b03020b9030324140c5100700c0020481004078a827464940903040026405070359201d101c1e401e0150b5802c08800d80041030402c5076501d284c68540352070030b01000b40704174017a000c0d00761a88110b0040c40080d60401014144180941c80000b0010390030078a40030000740c000c144600550403a001d182c0340c0742e17400d08100310782050229525010000001d03a03407064954100680d8038076203c0500544803808240c40003513104444580a200c001600400040d41c00414586042011088469264180c0030442d4246d01900070b0810012a5809120303d000100421384040004c2c3d8034001000d802011a0032040041040000d589061a5242d0307040e6070600c0d0300200384048595485440381441d00796a415000050300701000010410004628902200d0700300d5440d6103030a100100442e00c408000e40c90406100c000c0400b00e0a0310f00420300f1038411600b6400070755441c81011011454000084403044080411500074012034880c0025 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 430080971 1250 430079721 430079743
    0x6061112070f12140409020403050f07030512310509070e011b0c0503070902130807030b07260f090c04091211070e090607091d041506050d08090f0111 66
    0x104210f20031a55800329204103009141841c8503101050110341c3d480c965004001310b9104004a650704200001003d444204602c070150103a082011002c00c41c007040c50080003052212001309041100c140b200110040002d04501074410b401c0c1c600380020b00b820b9402c0d0b504a007013801c3c00640c05049900080140403481c0c6044900c6c2802c280e14810012800000d038003802004082c0c401268680a4040003500030040c2c40d040c40c4214040042c40300d00c007040140580e50000181c1000303130340700407007503c0740e03030366003958017851000304034220307031001420310101d028801d0815071f448603007441d080007403030a11014803039807056207460740031000104092007502001c2124240750f10352003032001c03003907040c10b419a0140d004107481c481040001034020035440d1144015454138104d990311090202000c0310000d81100c07212441401103000f1030341a0344a0f108007100601b0120715103441d04045a603200502c8400c94500e14046145007240c0b41180d450f0421803828a0104281002648501d84e954801c8003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 430082221 1250 430080971 430080983
    0x11071214072001033c050430020a08030c07060906051006050405060d0b01021504030305010f06030606120b060d14010f0b030705030f040203010213060512180c011b0606061112070f 79
    0xb1054040c0c801d1a405d0110080c40400200483e2406040222001c401d8070142015554010040c031805404500d030310b40c42d921140d0090150605a5a885c2015403015003c2d042424040c4003070030002d400d5004160a507031003107502003103074140700000501c40c0300e01e07070484011b101042c0010b10840c0c4500050f608071186004010a11680400c0181c0c100f0740b0034205000b01c003a2090070001419003581118bc100c8000c480756040d0b0650300ca0017202110814060480002c0d03424410003040342c481d8000da0300e101d0000b00000e1408841207060002c0f40c4112200140c082d07000c20040082600c500304800041002d9150300c2d01c1d515103504002c081e880024a001860082c41e03000ca41591800d42c1521180c3c0e901242602669840d00005172640d00a10f4205e20b01c035a41c0f00005000c01100f01a000103842c0c804007c1950b00f01010040d10103100320340102c2c00c6d012890440402003030303483c003944d0010519516054100001c0000b1503062a100034050610402c00708810b000044800701e0a00784d813a0420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 430083471 1250 430082221 430082291
    0x30501050f06070f061d16140a030b07090b0a02010b01110312010b030709081b030f01060302011e0311030f04020a0e04170906190e131107121407200103 67
    0x11401748000c18000369401d03105017001415051945000559007845000b04030b000440ea517031110341e2441d85e81c143c00301641000d00311104000062002021a810035018200400d40d40e489102c00d112541010a4140050b0b4548110703c525582000038581c201c000344000d0742c60111440039540da0b6134418130640040c44030000004080e0391023454100041c280701400e54000500d074032500b0381000c0c141d070740061086c040d0040400c00f07102c051054004030380e03068482103a0400c000d081c42900d049140c2c2550705041d101c49400d03010704e04140c000c6101d012803541c0040700707042500610000e004190020007031400842d00380008180b0960f440440500c180d0300c025a20714002000c24154043d000400d03804003800c0400000c800e80161003601ca4007410b9070301000125112019900340c1d10000307043d5021510070006000881d010310680300c0002040c2c1852080c0c5440b000b01030b901e59100080c00d40e0080c004400100c4654001002840c0c002803d1030140300d43c0e40380d5024200350b4880a00d001d19408046 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 430084721 1250 430083471 430083473
    0x607031401080a24090503030406050606070b0a050c07020a12031107030308060405070c020405101a0a1e020309031b131a190803280c030c0605151f030501050f06070f 73
    0x40350980480d120504d05001c00310081c900300c3d940c2d030000c0da82180e402c1d0400d80095401e0030310b201900d01e590780103100000c1c07a2b20303221110380040c80041d040440c41c20042024401580b591075a100003010001001d180306c1c07240d401c004165540700004213078a42c00004040011962086150b600980110340c0081ca940307500406450201200b200250058203000420200c0001044a04221130340520b008244103401c40100b6107501c120305551000c106826281c0c0d11030001c40321282150b04082c0110b030b2074651441c001903d040600c5502070540c03403074004c0c8400300d070501c60300e440460004001c0a20900d1041c00c07031640080144450301c3e001d030311554001b4200714100c1030b03030078001c00001c03007503903503071000d82d65050203016a460044501da14400c55451185218074503800740b1542650314041001101d0b641c1c0c1c0f01411000d0070401440e41c3e45a4031030f00035034910000580c03400300140003404140f1001c038083c0070f58105900c400e2080d000369104d4495074942c001110305041c0d01592142c503941c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 430085971 1250 430084721 430084763
    0x1512010b070b22021008070f050f071b05120d020c04140103030806041b09081902150f21090c0a060806040e030d0c111204060c06050402010c060504050607031401080a 73
    0x6180f00c041e601c084000040b101c0250440d182d0b6004aa140d9529000e482c1c1110f01519288148501c80b45220820013000003c103180440120800d40e00c000001d07541d07546c990000c2e07030109020101e809141c0003c00c060b42c81c0e41c0c0410009403400810b5805011403018060900c8050005100140038001804001421075940394081500305580c100e0440041e1400714000b032162580303002d69801031180d6401a222142000c00a520792a40240085405180c1301805003541d006880e8010b50800107000340c41603450444840d91044442390a1004581350810a0a2800503402c9083d8000d400da403000740500303a4084119079000d031084d078000c01c0ca40074801215146100c1c03000c40b13440203403401251800c9264000701100d601510f10040300e0440c0b001c4120752000f031103075118600106111000da58001440360704843d9020f4014141015408003686480098035800c1b80c040340c0c1074000a04100c1080d8161085445081400c0703070f01e0a9560503c262546e031086e8109020300301d101c4030f01c0d464000e100c5c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 430087221 1250 430085971 430086031
    0x81815090c0904061b02010203150607051515010306090c0206040803100e15012705013005040506010b0405030c061806280509030a201512010b070b 65
    0x700c06019a41280303000e08001c0014010b50800016440c140185074080c10702c14025640200f0349030081405103190041000714aa110710700031110f500a2100d010044000c40c440c96109170001c90510400711009030006080760140c1e00500080f5180c5508040e00c20760010700b05600a038014017050b92626403c035502c00c51940c3e98400c07000001280d040004a44004040030030a01c020b80b10162101d42011003005151a40d45101600d00f0020004108940c45000715001d070317058952407c2c012135085101607000ca24607420380300f40552500c0c203010400c8820000c0328010700700b0304085400c0c9401d10000030348800a146c84030348244800700c0e1040701e40d040c0ca00440a4480014050390ba1040140000036450401d95000140c0501300d646403c410303402001110840704005003d00309858090380c62031614500d61a414520341521201000345482d0b0000c40700c3c1150160032407544580309a147d203800c0100503006200a002c06000c8100050501a9001c1e004141e4100d003040c41070300c07a807000c05114 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 430088471 1250 430087221 430087243
    0x504090603060204180e1c23070c06020c011d040204050a0320190b07140d0e13090803040209131709010305060a06051b030705150708181509 62
    0x145000350000800c50a94004d000310b41a0141c1c00a0400044043e4000c4450200e0034101c140c220316a5019240d00d011a20310320380e81d150429140030b000c10104d610011419800402e02501c3c00248030041c400c01100c507200510981c03000f0803107180c0081c0003c10612203e0502101e60841800060041d40c582d0140c8002d400060070f4040c2a640d2410100b080740000f120110000183d49140e5006003401002d0101e10b076003844000614a19107820490f555001c004240d43c0c0a40360320500005650078402c240f22070540f5035030160380018003010041102030301b03c005401c003844d04c0d08420005400c001580c2c0c2c040e070100c0d01120070b941c4000740c41075004c0c20040010082050f43c0c01007000413182c24041c03c1c00a000f039030304020980da01d07001c0c40007030701460050070041501807002d43e1622101401e40b0085400038000d5a0030201c01d595124a4100b9035861120222841010040d901e41d10990041c1c3c000036103400141c0004444405030388900c6c013410340d1072007518400c0c005003000c0000c11542c2145 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 430089721 1250 430088471 430088489
    0x80d030c12020a02030a081b030c0307050c0109050c03070b040e15061603090e060603040b0a020d0b15030106081605191b050c130b030c10020f060109060f1a190504 72
    0xf400e40010020748aa00080131031001ca11410701041030b94096040d0300c002c013a0602d041070301d161a035403040d06040d08001e00f0f50040007070401600d040e10f1070a0080c03600e080d00c0390b00146201003040c4c04150500185800c4100c00701c0d03090204000c4284402c2c00030b5008110b607600f200d06800c0000c08185284100c0b403483c40c01d094442058020150310051707503001c5411070218007420ba00d0301810800c140c401070341d0181100c0800d0380480c801500c3d0781d0003000301000c0c0c030800041846104000c98203801054928251511000c0010040c5c0e64024000c03507407000c0380f0f002140407a0000e0030051f00c1070089024080c000c00c0d48813050600031780149207510340120f01c3c030060100c8a00c145807880d0307100e812952090084103a090100c01500d000d016525140600901520b00c0491800c140110750b5001301261007103200b14560114030840a000e1039001e03001c2d101d40810880d0900d030982c100c0c1c215540c40f5000c4a05003070800c1d52076040c00000c0d10040407a4a8001100c080c80ca1412201030040750130111342 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 430090971 1250 430089721 430089727
    0x41503020f06040f45051009091a0a05010e040f111e0325031103070b03100801050c0703090303030203181009050601050607050a021201020c06010608040516080d030c1202 75
    0x240b608141d0035079440b89003402e1701d18500010741d401171050000301d44015a000c01110801402100f0035042154000325680d84070481507910301d81301060b42c101803001c0d9050141e840030302640c2100e180d00c542c0e001d41e065600784a20351404004054580006101070624124008403800f005040c48070318035002030051800c2c000030728054100034030501c8000c000340b180c810700d0075000c000d030a9424200c1d2400c10600640122610715224100c0048540e80b4540d8940205180400e5000b02900510301403d28034100c9514503003800b41030f50031200050025503045805009480019a02040000030740780c5c0b502c2d006da186e413141a64038100d120303070034100030a50151031110fa10301a0254000c020140c040c6040329840d0344d03a0b00c1440064402e41c0300140c0b59410026540015050103486034203074008440005281461914811341007003001c2c0c10503000a5510001c0c00103002d402c2000070058014a4075000300f4503d0202050383e0344222180440c00c3c59203810750a5100e82c0130b200c4483c0082004141556 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 430092221 1250 430090971 430090979
    0x10507060623030d17150a050301052802040506030412020a1406071205010b1e0f0708090a090b0108061210050c04050405011d1b1605010504020f041503020f06040f 72
    0x9480b880c5400b414000e205040210101d2885000e0010700349040c00c200d030703c4d152100800c924000c0020402c0c1600709500250015954400344101403285100701a04282c0384841008650081144a4142103090041c0014070203076032100102e0380c0003a07003c1540591408412400c0c0e040c80000b0700c01402d0f07030424903202c20302d0500c0424003511600c8039076078084030003c050703030001d0490b1828050304111207001d0180840c40441079480e015003009050340ac0d0b042c02c0281070301c4010b55118030703412501660049000459414040142d001401c2c0d4050140a42034615000030b006c0b41000b821a4030900c01010401d0385a08207000356011282e000d00148854640828581d620760300611032240580c0c81c002c000a02d2807000030740c0103000c1c6120f01495520307440e140307400e96110fa08558200c02400c010450000e8040a02c1d50423901184500004074191400d0300401c001c00030000411401103082c1602070805019030303440740050325030494a2107019208480400c006015a40059551074808a400710f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 430093471 1250 430092221 430092269
    0xc240a020f0d0908070e0405010b0d0515060609280801020f1b0a0c03031103090a03030c0b060a080d050c011b0c0b280f1b030209090108010b0f0105070606 68
    0x30444000d0203040360188020b14504440b1942d82d4425011140c000c000b0500580d03c00f411102e03045401400003040010a580000e02d00324011441100c0342e500503180004509042c0e07080725030003181120381030704111541011030b248418850403070b50707400b041c11806190000e10907010009080b980c0021900c952080504170b44030780c881c0040c2603804240904c81460820b00181c0350581c070b90700c40c1d0300800f01031650b40c0c252202040401c0600c150301051140c0003091720b40c10b85141c0214040d6940350142809400d145045603405000640642c01074101030020542c0068500d0901555240c40c90340d400e40400100e00504024103120b01c004ca10395068200320b0381c01800300c2e00982c007a030a49000c41e112200e2404000c0402c3d0980100020385100001d04800c00394491a0f01e10950000403602d001910310b100d040310300e4548220082a400b24141000d41451840a0b016101d1a030080200c0c942d024006035190100c40540d0303041000c0050702c1410030451707802840051010700d41ca1020452080066 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 430094721 1250 430093471 430093483
    0xa0b0301180605040c02030f0a0c021306030b070c08091309060e071802070b0a09030509130c02280807030c0f060623010c1b0308030a05071404080c240a02 68
    0x2449281020b0380815285003600c200810aa1250015454010480218529500140b113400188580301d04040301580361407038844d050340c8010200140081c154502a904180040c111400300030400c3c00010014034035408030f8000030012580f010307010354000c1d1a0805000a010020009800c0c0404440f084800103064410769200e448050b9026240e000c964040340901e00c00507180d02e0862010610000f00c982c4003500d15070080c508030340b0744038103400420807000f082610380350303c0b9aa8140a4129950512003609040c54034180b400e106050400c40903000c084501010305407200000f900000c16020b1a20b11040607071200901a1011150410b0001890544901d22120309503000c3d034440841d0a0b0307140440010705848520310480300c0c0c1c44032051011100078400c0e900f03440c41e5000c0041035100f0041c51145455040100e49460300b103000522980c0403840c1c03140f5280062000380000800403035a004869820344603c110700402440000104105501c8215158000244c101c0b102d0750124030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 430095971 1250 430094721 430094759
    0x3090405160f050318010e0f07050108040f02060d090602220501050c2503020307031110030b09070804060e0a0f1b1d070507020a0801231009051008011b120c0c0206090a0b0301 77
    0x5270764046907103c0054079001c108680003402c2e52000380124006140c0342c000307400c00a04028000500320b5180d50b500c0b040b07a0181ca03280701ca450b03808504104c030041e49410100640828600181040c000191640e52a506040304098804582c0e4280e00d50700310f407112070303801140c004080383d00003543e80c1000b030502c2d0b0015401d00d0142038411100c05409021f400759128121014001030203d58400038104d032214400350080740d400d9124030f60180e1440080088101c001e006900c40d454100b803a1820441d4100d4502e1856261a0201010429014941c0601c03591103003c0c42a00e035603681d22601110540316640e0025803211210364040748064056000001307882c07803800f5492070013000d05441c0d804400229818010f00c5c485040500c8486141c0c0c10803a00072107480b001c0c2c9059516550300c642540e501401c59074403184400d010320a000d5110135030f06c10700c446103c000c21110419400c004c082d8401d0b00c802078010100082d908035691107414880004202c0840340c10b403296141d4601080c28402641 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 430097221 1250 430095971 430095973
    0x16231e0d0f020d030f02060708070e010c0302010605060318150609070807271415090103020d020c0304140325030f260301091104083c03090405160f050318010e0f 71
    0x2c0042c00075809034292702c1c0030314030300d44030124207108041c011103124022420403000c55403a0302d400107584c0c0711507000c0c5009a0026115a143ca640f1008081c42c088040f4600c00c543c1803d28203021254859182d8183c01200130302e088002e9585c1c8820a40c0c400c80c2c15071015006802094242401c121000d00d40d0342901c03021030078071b0000c030f10440070450030483d0080c007414948800c04c02c1e24060740c0654002d0100e03107400d00d005800d240701d00c0541e50540d0031581c4200080440341401203003915051002141c24118180092120a0580c40c0031580d003059000092000710450703103a00c10302a103108004920105000355207100c540084005101e03420030f00c5681c25180c2401039080c224030101c0284d8094034401001841c820165294462002458560070201d441c01400102d04d00030920b412040315903030340c0f001580e50b20106020b1000b00d403001050914ac0244c805a8400c01340e6005107a000042114601a6200d8444082c1490940000d0001d08510b6207894408161007070042130701e00c50702c44140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 430098471 1250 430097221 430097233
    0x170a080319181518020303040905040b071e050a030b09101509140d0f1a1b1c0c0e030d02100609060819030216231e0d0f020d030f02 58
    0x42ca00b500d01c030340454010802500803040310340d0440070f940500c00d502e00c03000d0300c1c0010101c01d40100742580c3c0700340c0242901c5500c400401061242c850039131500700da418500115400102c905010003041c006103c442044000540300307405610941250712403080c0100020046c1c100038202c00e80384411441050008000e4403018142940620303400000c4410320707004171100160580400c0f540407a540d41c100c1e044401c148070640402c039103180183c1c0c000050781c5541090308050341d00d40c0011105900030030824a0401000701c0f10400909105881607400c040441e81c0414404241c6201c020448d4081d014421204001690340d4002031030349400d00246401c00c20942c40d94140d0007502c07a01d000e0040b9591000c101e00d43c0e80f5201b90030901c005c81c024810344101e842864191100042590300c844443d009000207100115601c601030024494210f806882005803070704400300d400d0300c41c4449482419540100428402107141a802680d4020b1091407200118903000c0c190402070418a00144151 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 430099721 1250 430098471 430098491
    0x70605280b01080912090909070305011d0708120a030c0309080d23010819080403050714030d020114010b0c0f07060807110f0c06031e0c0406120213170a080319 70
    0x2c1410705c0b41c041c00759003143c5004080000c1c0044041c01608580d103a225062000011400030300c01d058516130554541e060b480807030040380740f9021403600310703003840c1e085900003140d09a5044100c032210001402c0200345088241000e5008020719038010341039420024801100a040c2d41c03061081c268080030200c810400d0f0884145170340d81c03d00a1448544c8800841e424a81c400264014124031400701286081e0301c2c1c0d0384150604a40343d00807606c40300c45000310006442c09001c2c044402c0000c1c030003000b12400340100b4452218044c41004106040000d8103140c462050094105082582007210900c2e07036030714030003006400f048404000240004060310104413000c40c1c40c040d80115100205a00901b4104005481d0300c0584412400e00c6180f8488d509500e43c01102c6115070301c08103643c1d45451034085d002e05484511003006000340e10402102ca8074a0512007200d00f5240304521a042421640449a00c2c104058002600c0c030322010081258082e4200e0110030300124050082c00b0303100035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 430100971 1250 430099721 430099723
    0x307090b03060403050c0a0501020403060617062401030b0d1505090319050a03020c160614040521030f0706020d11120f1f0305010518070b070605280b010809 69
    0x1040d00c0d981c182c0000d000b01d404244918050489142510241c543c040420740d6031500b241d006600480303a080d220042001002c4681d603110001ea98800040c15240c50602d40d0640c02c02510501c140094044240c0310b4402d9100b940f04401208026008240230f0025007003006102d072030511450040c50070640001d0b81c014000c030554820aa00301c1080200c00005001524150030000038002095424040040d661f08100041d0842000d00c41c801c0b40c0c00d80c10400000e0084000403c59503603840c0c01c0004200c1900e03440110006400f01d900401800c501c20540d1030304600c1004c10038800d182020443c01d0500c06154010403107990225000c21148018051003152405001c1c10800101c585000089420642c60b002c2d5600c0b40107081c640303c10809044012940c0d080680040e04d19039512002c1115a8920201d80200c0300c68001c0208411860118185890712807880007d10321a181c0780030480148900d1911100b0f811628005040e0a803d43c20100007400e07000900760005a07200045100000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 430102221 1250 430100971 430100981
    0x30705061603090c09090303090b0c0703020d050306030a170c160f05010305010b0f090d150c020139090902030711060a06240207090903020c0918071503090f03030b030709 75
    0x40c1c441031001c004d030710b456001001041290419018991039180000003d000d1564851091400e03d0302c9176101c0995040082c0350840c00003001092180410500c007007680c00103070351002c1d00c0d0700440c03900168400721802841c600036140811424030441c1442c1c0707051540b604010090f01c1070501044500703944d500044040c0c0b5801e101e81c1d0b000c0801008500c13102d0240d10002c1c80c0340040608079403000a07a40d5180d02c04140b204104151042e5180003a80440e913082c090605590228050201a11100a4a00c00e20b4410701c615a0f01c0031a10a428a1128002c000803c0200789030402151645080c0501a190b50511600c001d2540110760000f241200144a1038081d903140011190708c11440500000d4822940c0c00c02e4821344c03040440014041c1954013480510380c6c86540600401d12100081c00501c00e40601210580c910740c0c0d040140e01000001c0c4a007c95161600420710710301d44207000e0300246030b840c0000d0100c1024042c4042455056040000f40704415021950410b0342c0781d00b420b045072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 430103471 1250 430102221 430102223
    0xc010807082202040b0a030b0118090809010305092104030b1e01062001050a02090301050121030804020a05120d11010c0203121506070b040506070c02010c0b1803070506160309 77
    0x2d00490120a000c5850b040c1200190b80302502c0040c44108000014050b80e41c07550084548450030030050204600a40300c00201740303000c1d602401140c1d804d0390b5040690050032103840c10581d65070300041280070204000f803903980405045079031208500316841d180358450b000075100d009140011400881018444046060041c0d0902420740d09203101160728441300030580180340c150a89192403000280b280900803c101040140d541018505050942c0e1050740031100f490607a59000030203880c5840307007900780b5a00d481e00301c000d03564600c00184500100c2d00201d0b00803c0306005040305020000c2c0b06c1d9440d52043e1502044080f400c24160309854035050803000527001403081d480d085107503a0708650403840c220004c0042042e5500400d07100c0d0050001504d0501c554000d2005000f418020b198120441e8604038903503104580000c1e1920170003850003000c04654078002510101e0320228400c0d05600030007500e955020a080050f40d9410070b65940112006075170400c881c05004e48a00d20380381d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 430104721 1250 430103471 430103491
    0xc06161a074805010e160f050603091f02040902040603020c0f06060d03030f0f050c07171e0c0a0618050c09070f050a020709020409020a12110306150d0c020c01080708 73
    0x8002c07105101c1c10607002e1490308695640d01c031040100022420b1000050542d0f0080310314031107030b02e4000104a810002d88c000380c00703182c04109000b5200b0303010504d540070780301107651020300d80e2085002c6002413260340e06c0080550720204d004910b50764542c008248800c088000ca804c3c48580c0d02180d030301c0d04400c0d03403042d6000303c5480c200d500083c002d401030300411302c041c0c1002929030010b1a4000a40d1012510002d14800c00101001040550003103800c034100103410035400e04414024410340c00034400180202d640006c01d0160205008202d040351542d802003080c03000c041c4070b89041000a580c06011665401000305003100d0341010000c01d84600b4842d9505811b000d0080780543c0c1c940d00002640d01107004e12074005c90100000d00061004181d04440140d6681da040e00050441c0c0e0048042030380c160610030608a0b154182c02561303004502101d07080c810f00400201d060707042c0316030440ca07143c407400c1c4588035820907008104002c0290007038803030481300c0e602c2c69400ca52a403401c0300d103c000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 430105971 1250 430104721 430104827
    0x10807050d14010c18060203030708010b07210521090c060a09030803091506010516060e01020d0e0f06010501170106030b0a030f0b01050406080c06161a07 68
    0x14a440e08070221018010394a4510280102d51024203460390f00c004100407170008090040203001c40c048440081c402c2e1b101440c02d40c1840b03030000b040c2c2003040c0300351000701e0000310721041400f00c0664110140c00f500790314a24841111030015003c0d4000b1504100714121003054002120300c40d0411912400c0c0b80b8003c0d005d070f0a40c00f01042120f41112464404208d02140040001207124005500501d03e2100401d00c1004003200a1a00d000092550307041110600001e40b4039184c011803000d01950000000c108041d0141c0c20740d0090068031040c2c0310301c609003003d10004800c08521600c05403214000d41c7c1113030780c8420064840d1400c200c04074040c00f11b00001008024402d44c403410110000406183c0311590740e45440350441503489060759965036480041006d0b10701881103400030b02200c2e025141000107503001620a01400c14400c0d00322401d01c1d02d00c01005500c40401c3c0103c60074020151082c10101002424034844a6010070710140041e810410421000c2d0210245050241500c01c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 430107221 1250 430105971 430105979
    0xe010e01140301090e0a0213050a0c0c0f020904052a03061e041101021c0518010908070b0d02071205030a15050604061209050d020c031905070509070e04230f010807 72
    0x80140511781d0302c0f2080e406002070703000c010383d5038841103005c00300b01c69404034490400ba0100411142045141018000c04941810006e05449519803c180d0111000c0d103030b41e6502e00340039050510b00724030071030103a171900d08400e51140c040d100a01c003010281c2c1101c00c00d40c1e56a95454000c2d203400305205968030540000b50000300358014108c1d00500610554107014290041c000d8100d081410742004902c0104401c11000d18041c0c24000d0160b091078140d0311189008045900d50715140914500000001034065441c21103804aa621592048800c1e00041d003400e00106103030020380d01d01d150f081c180307110034084848249000d410381304020310281c0b4042c0b030b10343d0580d070200808000400c0282c03903111150214030107000401d0603060940140c40c202d000781b810142080d901c00440b402c017500c0c86000001048002411702c05071340003910503174604d0b25000c1c0242c0360414441e01c0544d1150418104600e43c0d269283c0b070103080c02c05a845104035443d0782e107811844000901031b16485d98807c0200704 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 430108471 1250 430107221 430107239
    0x50d0509061312090302090a090203010c03110a030c1106010f170a02030c0103020306010c15021b0105040f0209060a18060501110a030e06092209020910030b0112031e0e010e01140301 80
    0x12000f4507410a41303401c40e6250301281ca481c60031140c48030120368403056407065003400e00131000401e10903c0c0c10001c0e20032120001c52a400740312109000c056036500c600c50250701503961040d42c201c07401d040f1640d139a911688945500c0306801142c179604520284400d5284001a45c0b1442d40c0c0d00170f0261551011141c011002074000520140c1001007056030103010644520101d0030760b4400c440701580d540c2c8614040750303200c49100d482d0405030b03140008000200d104481d12240d0581c0c1168001540d0322620001081e8408035004100803950880030f20502d01d443ea13005108452003031300c60134000b00840b81c0c01600d0b06060000500895500d011044d075604e8070304014400f201d0014029075072003404021b50220320a541c2603030450581e0780c00981e000d505d01107030300c0c41d40480d5211070ba419090440e0b560040108c03040c03258100c0315480015820805000e81804127100c1e80310909580d0842e05544020400d23003080d11801c0c04a0540d440d50b4420394450647c420b08803504603850307881c1da40303008004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 430109721 1250 430108471 430108493
    0x2070f06081306060e0a0b010e1e1c05030f0c0714061902071e0509010b19050904140a05040209090d052a0f0a060b1f1d03010c050d05090613 62
    0x1111420f541e0703540855051482d2801038042c0400c91b10008608107210300250a03119031910752849a5599101001d91540d0101c044e03084030401c0d242d0030902c442002030740e40801c10f60030008010303000100e48010f03455441c00c0601540600341d8200c464070381d921561130b0200d580c1446034a4120100b0043c680c4039111031100100802c40718411104045c1e594244007141445c42c00036030545801203c000c008910b01003544501402d00c0c0c101061500d9000302540d01042480c002100c1030200c0030035000d01d40d6a80341e1094454035408a40c0030a10328007101071b10005c0604a03400c074400d109840100c0c0d200c82000692400400c46030b1110f614102110601c10030844245020034108000140c644010300000d1110310225070103038008003054243c514140040c0e03803888030b0039401a0400c00d420024507440007401c101c21642402c103034006005085140760110042ca072810303090f60904058480f2944e105000300841e00d203008042046468400100d40c645009a440c010802840c10001000c071b4216410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 430110971 1250 430109721 430109723
    0x10030b030c0307060c031e0f1407020d11091e15150406050405100e0d11010c0c1401120e0706050901020319031b05030912180a0e0702070f060813 64
    0x4846424103428000b03407420003640c10580000348650701d08810140c21804000032141012026100d0150b820402080310090316680e00820840341031080c10400781c1c1d8111044244c010b09006258180c0e8141a568142500c900600502d03034140054003850208107004441c0c0a1002c4000450302c03030400d90080002424902c661011482a0b4a51a038803210f0003003000700303d9900d5582d103032464003040184510311003181c0c00a01413111003d0700b02c1d6a035002480c010340c1d402600c586c8050b4903000100c40c050f070003083c01031904803a950b01083c440640c003040d4a190000f40d949009000c4044440b20542e02d038100c0c4c2c2001984980d20500081d4011405800d1840c07041c412a030030310500d00650980c0048601c21040883e903201c21001185900100308000c1c002c507070822901c1c508094041590356040000070243e03001c00801d840f0030b01c00096001c214410f0004024842c0e154443d00b851464007002c0c1e40b0100984a1040001b40d0320b807040c01c0060884811b41c4900722103035528450b0050081d42c2c4c82c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 430112221 1250 430110971 430110973
    0xf07032c0919180203010e1c031812030f0506180a0203060103111308120a05030f04020301020c1605040b0d02061e090a030302060609150d0f0f05070308030a1a10030b03 74
    0x12403140802c1a0340f0842c640d100408401454035485401030500b121032000c14144150062060300e00200c004000e00c001050940c5800181000300c24034485440c51803d000501a00e910030640c020680d1503000741c1085a4030942c02c014648408013008106111040300d280544450b40014400304100d50182d039008206042c041100d9400402501c541e6000140c0d00460030900c110a0061450070005428003c001100d454039014074003d0140842c00018a2350006482c4500000c003151000c0d0142c031030220529084410007203e0700b40e4139024400602400b4012860260748111614105860403240d54000d40311030303d0040325886081d0070786148104146140400c1141400580b00c90441c0030045009034090042400c1c01c404002e9002000742c081d00b6501c00d070001c0c600055580c011403083c2d9507071280ea40d25144101d4600100301d28203208010b01240110344001007800a11001940f00c1d1b4004c6a04101150801e44402c1000f01c0d020b513841e030000030880c086120b01c1e0103944110b005050041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 430113471 1250 430112221 430112251
    0x909050a020f07120912031b030e030f0c041505330301030f0311010606080115020709050108061008010608030d09110405040524040f06200f07032c09 66
    0x2c0b0a00e041a8440103040358a08103034824a00c6050317006111070050404249120500102510001c0a200301c6003031150701321910300c20a5081500442d003042103602c3c007a054524080c900c14941c1e488001019685000f0b605109000402030440207240302920b400030299801074402c2d02c2c3d511200107000313446208018500020186d034000079000742d402584216041050f03c100c0d40f030002c20040300f0320341d001d07110303070604034103014442d000143c4a05440b02041c0d03c150022051008a2903d8a5948980820741c6003c00104128401041ca20710401000c0641003225640b03820050032118144100c100c542c2042c01280f4903080c0f140c0010306414003500c1d40148044110000a040f40d900303560440d00f81d840415072411803000c00e20685480e25a030b40c10880c1d0703440c3c29101d00041d00070011000b098640e451941c0510000780d03512003160040383c01c8104e0b844030091696280f07070750301c501e400340c000c5200c6003030700305c9158031044554803880103400d02da0403c01000e009014400b20301030710310741a04c6190303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 430114721 1250 430113471 430113487
    0x15050307021603081305091e0a090f14070e01030314130e100311060a02030f0f160f0302120a020d030b03071509170606010519030b122104060909050a02 67
    0x301d100300503600131031403507544d4481008009080105035018500440d411810081041c401c6c40c4541030b51008046092480c0e0b8440c422a4010305403410010845941d0042d500203011090b41000c50740c14200b81100d030007580f9130b009940b000500344401000941e1000c5511281e01840000d007862044401003c00b040d6120022a0703800705c002c81e40c0703400c800402c000c200300384001d1000c481800d120a03a2580d1500300f1100c0d00075120300c00d601c20fa02d5010300000300d2140c01e080d06402c60f001108185010003a91115107000c41030040c0c1000180c0c0184140700140110215000486200d800c01da0000d00181c0d00540054000e80b070030240c0e4541c18080e8440024000207a401000980b000740e036150f0020390700706030194a0882400100b8407a40e40174008222690342c21000b01c99034821070b60a901c40240461004070080c010540c0700903080503072024000c0d01e9210000d810680c1c1210303d411202d00100001d210702c618001c2d441030500050001b0340800180c80341e84c0c071168008134001c00152418001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 430115971 1250 430114721 430114753
    0x906040614090424061b020405060607061b08070203120f04050a14010603031e0c0b0406180b040b0a0c0503070309110607030504080d020703021f02030c010e0105070906091505030702 80
    0x1840c0034800c00301d40c0c110343e201301d520001d40e0800904100e040100c14600120103030a100716440750000e010310303503a501084c05560f400041d00c44440d8000c2d02402505d04c01d04070328a42101c94102100403881540100d20210300200596442e80200020b201407580c83d6040b007110b807074000c0c2080d1510301404554030007141408003804c28014641c40082901491440c0084c5400e10001e50f05907030000f42d000080078584d1007180c0b4002181c010809a07115221804e1110003881c08400e034210350800ca1000c0002c0080c0c0b0348070700b4441c50144075105681e070f4589406400f6118014140d40004030104005203589001c1c2d0310440f50f06000d040c202400b005548045552640321817001d4000c91030204003084140c2d820048600356044910140034081d107580e001c2004044003018080a030549412984011842041500e11200380c40c0001c3c44140b1440340407038003e00d01551144005842c400c000700d201d034000c640070421070b02e038403100300300202604c08111140c0e08082c0007035046000301f18204818841c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 430117221 1250 430115971 430115981
    0x3060c1803070303090f0909110103050c0409140f0a09020306010e07020c041d1e070504110f18030f0a0b06040507090f080d020105010e01060f03050c0d020d150b09060406140904 78
    0x442616003e21701418800c0d004410705459010b912154200550240022031901406000080a080208064079120f184100600941c0c2003002941c0ca0f04010161080f134a28805004100503040703004152126084034042d181200d00182d0140d10040041100d40c80c0c00109070b43c485003e1060341c000d00c0343d60b4009030540e80041e51010001c00c08aa01003d44101400103100d40a541c2032085140c4040c18070319925684140725651189544d2054a454008180c0480b000c002035203000e01d54900014407031002468071950350b41c2c081d110700340078945006000149107d4043e0440d0f138a02140da2603034100006004020588000c102c4250000643c0e181c0d68100b050142140c000030304a4140d41c028020708481e4141d000e9511070000d240100a21a0000302400c01142140f4001c1317596a59918601c40794800c0c45801501c841c03001900d41400d420b298403041070601601c00e11104180d4820840302e0342e003d180d81aa41c444d204010802c24207000d000c0c02d050683d44204510304020001000800b214 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 430118471 1250 430117221 430117223
    0xa060201050a050705091e040228030b0a050d060509070506040b031501020604030c06020a020f060c041404060f171002030c0703020c122e020f0a02160503060c18030703 74
    0x103911001070202e030500a0140c558031050a140c035a041c420078000184d00c20480c44014802e01e20150410940c0d61140d07011100d49000182c003001022440501a10b0b4910320020720100080c81c09003c20050b140c189540002c82d06c00402400300b80c040c03a2221002840081c141d0240c920590700300190684804024000402c5610459500c1c1e19101c00e540712191160310001d8119040401000000383c0c000b0750301d12a01d80c00120058032880e922400740d103007004c076841d080c41c00d2103090100240c880194000384195018034442160034040c840500007074514078003907609a0071226209004680e01000750a80503034002c0102c03041000000108000c927407055404444034800042d00030141501002036201d071780003da6a0418425150080d40d444903401050081511441d08108465003510511a0280514060704560300c900100e0001c0080c0c1c049400400075001d42e008a43e40100c20240c941f0132640090003420b11a0345080305030a15511a03c10f9444a02400c5060021030302c0c2000020061 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 430119721 1250 430118471 430118473
    0x80c0f0904020702031002040317030402011d040f0509030c0f0718110f0a0c1124030a060f080d03060b131a0f0d15121104112206080a11090d030504050a0602 69
    0x460650030074081cac5e81c09054071300340c00040030402d100050764808403d0348c91441070321800b41d0300c110303160018015001c2490340300c008038109424448a24004401004001007004c222507090740b611820b40d880d0784180c410070205120103180e1112540203500042e03850a04543c0701840d28000780784046154224401d4100040c80c00c01c1100c0c204a40307c82407560f484411291600341418041c881070624800c138041000908010000c10034143c036a800400140081180d810b0465407203c1245990f046000750200003e414007500054140d032010484210000602c2144112404c1984004182c1c0402003005020807040040c0345134035880c0c0c00900f02080150401041e607928083e12410078050366045540410000e00e00000040c61001c0c590740d01034400c0c3c80c0814040151000c2d48841e019216102690500882c0c061b100c1010100d80d080c15516991140362180e25080f0b000c4044812050f5164a40101000701c1c4080d854a01e01240c4d901d8443d1403e03a15054451000c40e000030b1080e1301103009 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 430120971 1250 430119721 430119727
    0x131b050c070918110328060b12060403180e0108010b130510050f0d240e030403020a0320130f060902070b010e07050909011d07080c0f0904020702031002 67
    0x103080c0140314241c028214198140190410006140144484908000c19210400105035401d48080c000311700041d890b0800554008014104a11066041d5808a400d949400f80006580c5841071b41250300f482001d0061030941d640f80c0e401d417100e4600326418144004012400945070600d04001c40c060140c540020640340342040034012480e90103682a804141020100700341c0340340300150f071000c54604488080c000e086c0f800c003240141c0c21060014142c441c041b1407100c055510f2100080140ca2209420000b010070111035944030700690000a61040c2800350801c085508842c0c106c80d00b810005040755030525000001c0c0c161146c41c3c0080000649071441d031700c040007440c03056030020305e01001c040d4074010181e907480058036414043e20002c3e003451000320300918803401c1580e60401018000c0358265848940b191300d0340103804a0b03880b0424595000070151403044d2034090140000d815000d0800200d106c900c0c1c0190408941290026800d00c00d03400540d0f01003100300080c0c00d48001c0143e07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 430122221 1250 430120971 430120987
    0x21c0605090607050f1804050f0108150906071214090615030606060904051003061a0f0613030308090307170c06071115040816150c02010903080402131b05 68
    0x419108014084450340c2c208100300100300b41c109040307580302907a1040080d510b001d002c10010401032079035001c030b80080c6000c0821100c02c100c1d00d403050580e00c0b01070480d41043c0841440d00e5410710125103081d910381090340464461400b4801c40c030380c610400e41c0041004902030500c1071031880120356061035584070750188812a0f104507550741580034240e024064030300c0c019010840724894407014902465403000080e4140645100040145034810310a102c1482d1180c85010b2425103c10080d10840d10340c2d201c140b191070080c0441e1030901882042c010704528680742a21603100c003c00448481c0401c000f2603000a610000041c0d02107650b00d203598462000d254514684900100100e0034407207000e08100c0281c10000303441c407021000ca840303100c1983e903078608590307140030310802d00c55190302000c00f52003080b4a03405483c403e100707030b06000c1065480340d0703804a082c2d85603051701a0215802001040142c03c05101c49620080100e0021a8104003000050f0000c0c4060011500080d030104140d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 430123471 1250 430122221 430122233
    0x60203070e01090f03020609091b0f070312020304260f0d0906050f010305070e060103110c0d020d03050c09040e01091b150f0f050c070b0a0e0a0b0307050712020109021c 74
    0xf00280c2259007121302d0302815503021401d43d10130029624030684900d0005000000e09a58007541d50700030351328480c0c44004585554403182c0007100100d01184401c0121600d015035032007500d1050f40c2000d400100d0303440c40c440360840d52401d9050041e0f454000c02c0b00001031240000100b421240b21000002c00050b2800d010045400c0545105000000c400c0104003060700041c0000a42e24401c03a06203c0342ca0f41c400582c0240b03400c3c00c1e06e141d4440c0200314103650110120b1412800601c41d025650035400c0140218115203003261148280d0f44288090080d9040c603900000c152945240005042050b58580405800308030242a050701c0480809111440c40d41c0744400019000341000065284038143c0030b842104881901000c00c500440e0002e8140070411046004003e01c038102e56952408080c02460090030180c0c0d180a03045d407410025040c41040c080309d01c20307401a5100d03800d0100d9030b51103070855034100ca545001c40d0f40b0342003104056525404070f10800918005402c01540381031500c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 430124721 1250 430123471 430123487
    0x7020a050d080304080c0106150c051b011b0201180807051f08040618020a0f060207080304080309060a09270b03030306220e060901020403021c120516060203070e01 72
    0x2078012003065031180c00141d940390580f50001c0d031003140c59440303104401d8001e00419850b400085507841d210b444544e6a0f40001200c91007070b000d0f1080d00c1291b00954441c0503403214910409000414001403500710f41400480e80c0d03803540c8140b422801c0124000480030341c3c201a40c000c07030810b401800c8104044e152005150340b5407a445a0f5503600c0d04c92410018005040090003d420981c5600f5071050310307884040c10407202c40e801807001d045143c031403001001e803400324007030345003d841a0320000c1030501d0000141c9080707403c0c00c0c1c0107601e0241c0136410700425400101c41e860a003c2c2480001ca0244142e81111000070300d103000040402411204234000d07540403210f0039000707070002c00600145407070301800643c08520241c541c01d0382801445645000b8402d00c226243d59000702c00034807070004410340081c821a8000c0729940b03802c04800c018800090300008000f440d5038440f9079043d4185005a002d041c0c9460b012104900034112038560784180da00440d60b51000901c1402c01c524103680281c6a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 430125971 1250 430124721 430124729
    0x3031413091a0d08030402090403140a09030c082a01020c12030a0e1804060c141209070e0c1b0703060606170a0608070501050702030a020d030807110102090d0303090c1a07020a 77
    0xb15140f2107440d100c2c0c1c0000c0c400907002901541030f840008041c5402800c00b00b101c1c086125182d030f558241d10310002c103440d00f42d010455040c0e045400008852400061020050811140702540c40c5400303000d003500300e40b006000714194066100040745640e114108001050a11400303141d40341d502040c0140003441240440344903047c1e0706030409149180b004103950095120a001400d680f00e05030584400c83e101d19a910000030000d1613942d228440f104590280d8000e401b1104078949030200203104410840b4a60741704201800200c0048940310b405090500c0e404064501d0140c407030321104196003075500002d011480c0003405d200c6140040b08200c0e4403001460080041030300301f4447c161030700d00c0ca1040504000000c41c2c900190b5a040c0303c80c1030f0b481d50003000c5010602c510300e0041c006460840c2c10314045840c411740416458018002c42d00b1903100100403e1240e0b0803035030140d0040c0606a0151aa204102c9010420b1407034014850b0749a01e1807003041f40c0b03400440c41004955015500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 430127221 1250 430125971 430125979
    0x191106030712060b0a0e060304030201060b180117090c09130204021809060f011d0f0405090f0d050403030801062015090d020715050306030307050a060b090a140103031413091a 77
    0x4c8205d25450b0302551142e44144219026540ca4486050883c0540819004001d4040d0001207044d82440d1412864080100a8031402d02c40b25102000601085c411113400000c0d822440005906182000001b070f03000010a02c07440e41e0448940200b004c0780c1250b444100f0300510402120300350324141c0307e0710f54018401c440003003840c1d84c0240005c0404808142c28400321418551140155a0300e40c40f8045c44040034204006174a400c6121543d031305c03800c500e6807031030b4083c44040000c407512540490302600d800d5140c41072a40d103090307001c4030119000d80c1c09074200b84494020800c081410f0184505411010200960303170304000f03880c00c0c24600c42448030401e550100c40100816155a4a40da0760300d056400c082c2d0302c075690f0034040f070708522a02500a1139070240e01106c00800400c0c0e841122162000d903848600c030703620401d0440403601644050440c0750786d0b00700104000383c8610900ca05501000071003034244038045039280da12a185410400c401520f1788280c0000019040b040d0000ca04115 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 430128471 1250 430127221 430127227
    0x3050306150304020310022b050f07140307050a05071a012408190204030b040303140a0513060e0f010606050c06070e090103141f09150509191106030712060b 69
    0x98002079551804061051b030786c58021465040c40e103c0611400b00b8400d11148492010960744040030003444212002d00702042c800c2c003c259054414482c00f0683d502c20034006245849520060300c041e00080c1101c1c040220401c05900021601c8420541000114199030282c0d4100301c0c13100d241c00ba116601072414040200619a500e60000300d50340c1103d40301807103a0700c0d0090101d002d40a40b00d40e40024100c242440c00780400c02d54154041030700350604a948401980b00e0307120329810341c2d4041c0ca103d54150400c0318410081540356000d00303c107803a580708880705015160031450a4a0b000d0340100f02107100400c41c420a603005000441d4419044c1c0b41c15800c0081a0b4000385860308103000240440040e840524400182000f582c07903815000140528541c040c00c0f03d0030040c19086004035094807403001c0c3c0140d10001802014001e070001006404c010341c030404642c4512151000a48082801400b034000c15295030f00210f000d0f596540c0c9040e024000c0d00d845000341d03851039000c1c2031038034810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 430129721 1250 430128471 430128473
    0x5091e0a02042711030705060a0f0e01030b06040311011119030809030a0c080309010f14010518040b060f06070602040306050f0115091a0c07060203090307050402071707081603050306150304 83
    0x104034040d815038010703051341c0b10700301581c0400d24141440e04881e400034000680850000c0d003011100c42031500b0380e5140986d0212000045003070360941000c280d04084103000c28400100a004d240d0035404040c58450001040021501e14008812a0000490b44860034140c281580500410f50000026000f10300d040840100103241803c0c00360050844440400031071800f1400390400c10039a082c041040c025408040c80140d40400c080c480c2c544110003142000c5000c4904011692141d604820500056036809084c40007521500f21301c1944128100180c00001c2c041c3c0c400b800140d800366800003100e00d00345040c030030501d4042c2c100001c280e1450380e1700d90b0101e03405000101503844103070000c070102c00c20840604050082d1403860781c2501905c0808585564000081c244481c000c8049801d021742c5c420510089125000001d0043e61040012104c101d101d20020107540c2e01c1444214540b50076510720400701c5200e200110002840001448120714180040d0401e070030030892075900e10305207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 430130971 1250 430129721 430129781
    0x3010e0406090807060c0f0f0c0302060604020a0c0b0c090a05030a080a0f030902221a0604090b28090506040b0904060e011e05040b0106080105030d0305091e0a0204 72
    0x300010a03094540c0034100411608009603011660300400600c2040303080d10b03004d0459041c0c2e440304800506403205554010f4451100d050201d501074016141545440d014000654002d001e40820320112990800c00200704600803449a108000155103400400d0b0800101c0213031648200e1103903202d9280f840124a2030001c0f02d00c00746041c2440b160030a11500c0640c05002c084101940c4110400943c4030440005034085002c400c071510308100543c030300c001640204600076441600560213003c10702a0400d554403000d10030030000d096a145e01e0301c1e1041000102c03a80207045140c520b42d28001c02c0360044a00465400002c1104c0c01e11047d04418049007000c200100090f09840e242d031000d06821400703510000590000d420100d00d01c0a12011f400085c140540b41100c0103464240002403461040c00c440d4184c0c0c800030041c001c110038503c4210007600010305905428040d40f011620091007002042c04c0d158480350107840500c030a40100800c442c0142d420407058221032401c1e88650310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 430132221 1250 430130971 430130999
    0x11070308010603020723060403030e03040f0e1f060f021209060f090d0b010914060f0d021e031e0c151b010209040e0c09010b0a201f020a020c0103020301 67
    0xa4a4980103880b0050707801e1150401c4175480c82d01030a401c4911440c075940201051548c400e5009840922043c4000703942c40384d5034801c2c2d00c00c4500d03685d00800f0610551141c016119040707440d00f641c04421b0688504100041e1a0592210000c64001540441000d4050040c3c50480030f0000c1d000d414a1050700c049003951280b9902000e000f980058442e10940d191042d0f80c60703050b04540c8980f101d45c0c448d4404001040e2251480c004c040a42d400606c061801c1190442841409800c80c00e52030703c0b0b5400d1148007211052a18003036204450388110f80d0710204901c9102c01001022000680f0640c42d0045c04d1040c425900e41c040d00c00d44151a800d04111001c845044c4810081600502e0504440c1802401145440350380103091081c0301c4007850000424030790f02842228190442c2e640c0f030401c0c0600c0d200310080003010034610081c207494841c40610300121503003880705481810000020001c40342e0141c403503e02c045030740406c202455a074104402d45901d107084c2001c601e5035060501c01e001c401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 430133471 1250 430132221 430132229
    0x40b0105010c020301180c050f04020405130b060c0a0b010e0a05070804140a060204090204050f060c0d0509180a0608010e0f100903170a0b091b071115040609091107030801 75
    0x4000031800b039003151001d602103d4010100048070008050619100408004510030310384640106800441c00d4a0036108450403070307000800c016200c0a082121902402843d000658014401d10070002c00440600c0800c0841e0300c0b07040c50030003942c1090105e440e03c0700081c00314984245000b040084c9241c0002d039658000345c00840d5030300d1321a8110356080c0b91903c8000b005203003900104000840503000c0c1c000e00240e40381195a902140d444005100c1240074042c15980a984407013482e00841e8047da008091180000d081c1c0c03040f600c284440c0c4111141c0540d14007110360751301d04080221400a20070040000342d4400a01881d030440c40e003959513104500410040180d684003402c04040c026603048907054a22040c0840528000441788000c01216001a000f0603c6c80b001807151101c0c028840103050810f5040d5080021740d840383e6050701404040c807034202c80171801500000445070007400c000c00303156850302c16140c103020341d0f281903945400780d00c120b0307443c18030180c800a074000c40321318151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 430134721 1250 430133471 430133477
    0x1a090402010e0a270b010302160b041a01030b040c1a090103020d0f0914010e0604080f0d0608013201032102120a091d1012060b031506090708040b010501 67
    0x111500710b0001d00000081d034024210310b0281c207200107101604205036208504a60380402c8200c08420040d03040e8851503028240442c150401080041c091142e22504240904002000004100708100541000380c00a403600c21406041004105800407104058946030188941c910b80c005a0031009004842100d41856000704900414000ca940a455804070428051107590b4050800910200d00a0060710255007000c8030541c940c0d200061440c019548901e2a078506100c007d1000d082e41c02102000c0c1500c1e4035000c001500181c2400b50003d1103c5140b00018480401308034014401012000ca00c49942d50000400101c2c8903030400741a02d0824460b40c1001039540d40e022820030040120302c01100d4004109000003d038464506820348101d401411800e168043d8404d40c1020212590441030b50406424040b01d00700d40928101e151151002050803905030380064245201120410510850041005100d250043c613040d00b12000b41000111410180c40300c03461441c05000c1d043c18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 430135971 1250 430134721 430134737
    0x612022d0c06070912030302090f1005210f150307030b01080a060509010216021516060213150203091c050a0606081014060d0204060305030f0c011a09040201 69
    0x21060003515861220144003440c900c14803600d402099150012126420644500301c0001c192a0046488006844c20308058280c002000e0f5012000396015003086a0001413a4007440d682e600d801e0307110f040c101c50a488098440c04110101c13180584000c052090b000341e030313505026810b50001c00c10b5400134072208041a114103000040f91400b01243e2005050355a01400043c105101090b58045248164030500c040c5d29451520360a07409000d85c100304020700b0003404030047c682041c0700e070400c9810040c81414100c1d01001c00b905040310450a907102d13030300000e40c2c4a8007044425080042c080f030035031850280913480ac0c002c0d030701e0058004090143c0307100c1985c41d01c14020b410080c3c00b4550310900f2542500c00c01c1ca4150f0250200303110b4444584100e404000d2000c40380d000d00c406500c142c03140fa40c9903070f0350101003000303120801100740e811968800700400070903428801040d4103c4c0e0745102554504194104908581084802a03864148241c40310015503030f860b4800c1d0000d80903c0c0041c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 430137221 1250 430135971 430135987
    0x411040603150c030f0e19052e0b060406050706090c120302010b1531090212100504021303060c1403070c0b010e0103050715050c01090c090b0307061202 67
    0x80c102034001a040b1882c50554101102c190342107030204000c10380d003e03ca104401042d61080d40d00c10107403001d16801c207440c40d030081311800d40d00303130304050040c0e04448150b10044100080400c02e0082c080c0c1082c01442404001d03021802500401d000c25210a1f113018a0410001d20034003c90700c0081c42c580c0c640c0d404005024189031400007900c10b09080309a140402e1401a00900c241c09140e40211565103103407800c851220305036a07007000c0c4000c1000403c80e06034270010000003000c125051620a201001c00e1981c80362016003010190000501e00d0f03402c02c000d44880c01c22103940f10324030603070040142c0e042c1026017420200480364041401308010980240030b540c11000d00c031555544000100410000c181c2c041070303441c07441d40945141c0031907036200d03012042400c5c002d00026102e80e12020082100d20510007010381c1640303d61a0503420720016041203800e40780209000d035101e041c003410500c6103c0181c071444141e814101c0051001030725080b8043d007055003568489021035030102d03201c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 430138471 1250 430137221 430137229
    0xc04170a080a0e1804030e0f030708060a1e060302030a1118160e0306060a2105010c020606120f2d0307060516053901020a090311030a0b0411 62
    0x100d2031035070180c0402e84078008050000c00309082a40c90904c207400e000004456440d0701561180150b030140d03162840d6800c858280084111980315554051092a4000940c0d0724140106806a0051040400c5190848180c3c120340303083c1c01c0380940c026190900410059400050311108642d02044c9010041c13014800510000001190b05ca51000d12004104e400c3d914a074905403404415221220042104014140d98400841c0d045e604010540024824203282803981301d814003841500c050782038415510142502c2d100548035025030b1210060044e00c1c80e000c15070302242e0840e0401841c0003041c0300c158030758414001903400c2904840b07580c00c100c2070765500c0014500881d250102ca030340700d2607483d10302c000703000407104440042d2020a8506440d44584122040171000000b0b150780f041060b1102e0404c5294840c248802c0b03800b64800000e103600c02c0c00640745c3c00d903194503424641e51450078034022640110303298601c03a070001c480c4807000810165089030001d4100c0046100d0510603030200e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 430139721 1250 430138471 430138483
    0xa0e0402130209130b0306090a03050f0315030a0c06080c0307021b06160c051005040e07080901090b040605040c0602030f0d020f040305070f0f050a06050306040e2806050c030c0417 79
    0xf1a00200c101c00240c8842d0000c1e0040c9100407426421104113030b651100c525145c255401c402400144200000d090784201c0074042d64200e00d5401910401c605e45100080ca042e449400860b0b04840c41142000300c00d8110f142d49500c101d18078140d41c038500d04940000d40b20381104a91203500250000c201520341c9030481900c4400b03070003d68000420419042c02107081b0401e01c035040c4a02c01d80c1c41844086071160f002d80b404c6400c051911041034031041d40598500c1c0700100340c201d296680c2e40000005c541d60544160296020b5031000496040c242812880c22002d81c01c0882590710811642c18040b0014040b01c418581e034a00042e11072070302c03441c00f0740140710316031000d441845905030100d21102c0f41b04890b02102ca1900300c0c11005981c0c0d000707100c1d4400d80c502c105400b203503051001400031304158211040c01e08084041d942c000d40006010031100da4085800c0b2004070300034032624104011442440e42141150a501c4c0c1986480c49412030207100740d014074128400310000290720381c2010011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 430140971 1250 430139721 430139737
    0x150904140a0203061807080313030b0403020c0414091510061d0a030606061e02070e0604020702030d0305180a12052b05040201030b010e0a05041d01110304020108060a0e04021302 78
    0xa940031402c0401e540c4104001014070817006000d030101c0005c4869000084600059180007034114461654031802c00c0084000c100b603096000b20f81098550703a55510501c3c03078400d02d4080400f02da082090f0407500c3c5c6400300b50550038403600601804650100284120704940722443c041070b080001078048941481d00c0f600b9103411204620020041203625082030741903c2c2195103001441b8408000e98003030b81c42c2c0c10000d1002d40c004220a010128211044940c40403015101514001e090760203c2e203402800004e590009542e001841903103c00007041049000e81e1710005d10b02c0d0020be8840070303002d03039180b0303c0d2070103000c00011a003524070360b040744000c82100c0031081e8481460443c0140005000200c4040380000d00c0d065280c130715503016038060b00c60400c015098061060070501400001c00d002805615404450741007021612800d000704180c0000c103002080d103034241480050304940000e441d4611400b03808209001840901110741e40c0f141e011110a00040c1c0200144c00080c414009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 430142221 1250 430140971 430140973
    0x11040308070c08060705040b03070e150c060a0518030415021c0c02010906080f06040507140c0c0a09141b040e070c0c080c060d0b1323150904140a0203 66
    0x29501c007444034140440080321000d07001e5138916594030204a445e88500d0241c54034261080c004681150300c207482d50319134034102404010140380182d24418a5800c4040070441e503a0040e810003e41c8080c2d4042ca41e04040e05400070b08641000380441c0d40c07240101d009010702020702502d2401ca06108220004402255880c8a609140e0444c2d0003460b55011440c242c3c04100c42d4480010018480d843c0103124983c400018516901e5403001c00010707001c003801500030030144022001c0000c6040000b01007500c1c4500003441d2b05219001032040390601da61240e0801c605c1c00100b00c01c1d01c00c0c1c00145036880505e5583d69800b8003242090400603005d030780c01c061041c0c0342c544104184950402c81c00240103010b4041c2d081038650b15000c450362403421401007a00050244030700f00d11400700380c2104848141c01030030021010f6941c13003181c00300c0d48800240c006050780c000311004002464003109030050395800c01d80c40c005c0030074800b06480b0035000d0002414a408285000c404050034000f0780c0107075078028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 430143471 1250 430142221 430142227
    0x3030f04030c03061a010c1e0206030702011a06040b0a050708040f09060e060a0f0506090102100509010b1914060c010f050a0e07080f07032306070504030b010e07090911040308 77
    0x800c0c003407002d440602003125000d103000042c2499aa14105040034400c050f503c0e458018059035507000c02002000c0c807100210311405158005a454030095442504640d0000800082c800c41101d0b10003608003040e405403038200030622803107110a00300c0d413003035540381082c0d56110b100e440e24006500c41d80d072022030110b801c0d070030206017094030703402500466000600010b425200e0000300301208086100d02819030007881020071903403c00d40090070a6600500503a5691800c8082100c107581044400c26560303552880c5903101c0d8038040120810070907a000b01d8000f81800c2055420019944000f030742e01c1800c0104003d03c0e400c209400200e082940403105010604040c0301841c0a0426542600214000c216003c40e4840d0001a844180340c550401000f40c03e10715140c05a81d0509084011200501c103808800e0302c4004000302c90080042d40d581c0e95407140340d400c0034200702906800800c5076140c0a024009850b0f881000c1900703480140800090800007000321107428070403684010404c48002c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 430144721 1250 430143471 430143473
    0x408130317030103020a140d030e01050906030a1413030e0405060a150801031e02061606140415050c09100e0102070f180c08061c020d2f0102031602010e03030f0403 72
    0x700302443c12a4800d41c0e40001c003d0325190003143c84030041da10aa00819011314880102c1d200d05d200c00319000040c10f16500d04420500460010b9000300ca041c0d44454840e20107402c43c4e840140d1155201000d92080c0e220410300d5a002403840f030120a10b140319030b84030702c08101a684c814031701000403c190f284d10209800038600c007504814091109803525802018014070b03000f948864080e4850340100001d107400362010011070511044001540c0c800c0d500c1000450020b0360500490280d03028042c0200700d04442c003c1001a107030010135892100105200c24820742d00ca00d404078030286a60b0420400c01d6075041c0040707240c40295030180d035000034403050000da280000103607040e040075600c1c2e0a01c001d84140030b080d1849038056030001d4101c403418008007623214400070900310301c1e0b100512100c0b81143c1a1124561801810031802580c028641d4014414480f802504030300c400a0003d513041071000e0141c04a4070b1484e40c80a0f040c414206000f42c460703a024000c83e50804402031201e61102e0701e13 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 430145971 1250 430144721 430144763
    0xf0c0d02071b0f06090303080414060925050a03020f030120040504060b040b070308100911090f121c090801090602040602120301050916020f1e010c090305030304081303 74
    0x5049102c0d812003200040c040341d8454041501c005403901a1a8004618603541c0d0481da0548002c1056a2032184070500549000c0d083c00458050045c8000401c203030b0240d0300b468102d0001c288045c6c000ca000e00d980030003898407082e00c21003c9a8049400030458074003440406d014202031120086000c84100b40c1d014246480c02c080c0c01511030660b0100101d64403600c80d4a902d04c13a03406909014042480200c00003031091941c15845076000d50845e400581d201092000e41c0e10f20300041014040c0468118a181001052055040021204020040a0780c1d20141c0c030380c03c01440010f420710410404a07041400303803105d8001014848001c00c198652800e010303000b9042401070703c00502808000140e046036a034240c0341a507900400f0900c59480c0c401040307c5001e000c061103025130081d0786c010403100030140908e0300800b051075034041c41520320410140c02c48071180904014400e2070441440405c000100f529031042e400031000e550f818004001c500202d0940d4002884000c10804503500003003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 430147221 1250 430145971 430145993
    0xb04060e100b130b130f0f05040e0a170904020903190201181a0d0b06070605010810090807110f0a030323030411010e150d061503090302060f0c0d0207 66
    0x20250000c94a042c0c403403852081c0340c442e0342a04500400d2101c0144407006044000b05070398440322408a0f0700340e0781c038588020182c210394052946203285100400603400d01e4015090070000784009408030f1985a581e032103a60305540070b0340e2000c04021400010076129907049813010440142112010110075030130703a8046080c10812030000314000e020215200400080c841903400b01c0e4003101641c101e03c52500d03019000701c1d441426250325002e0009958175181c004084442c010310b004200da42c10400079a140040140d03212980350b25040d849004540304000b5148a5503000d030510406c041880009141450803444040d4002010f510010070590804200d100c880d0440042e4170451503654064440340c0000c036800351001040ca60700c5031180d882001c0078610000700824820701c91400c1088070800d40c10458503030003115556642440546007902180000e034099160034403a1400c82e03034000f502d0f000040c100300402030244010031403580d425001da4809070401c640454580303003a07081002e0030750 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 430148471 1250 430147221 430147231
    0xb130c08011805011802011d0414090c120c03030406120902090915060307053f030c0f1902090c09030d05091e220207020a0602010605031002180d0201030b04060e 71
    0x261805c001d600140c1e441c0b0340c50700310050b016110b10710701100201c403c4c0007507440c02e000982c1c071980c0c9a01e08414001624902402005c1a4004058081c0180244000171108040300f10b480e90008800450680c2c00004580584049180107181491002c80b0a00600320702080254060030310781c100986540d0014600296140c404214641e548605050540f500007070702815411201d00c5203d421041d440100b0711485c02e890030095020b001155120404090240440c038803d41c100003006681c14138100000c600b40c00c409409000b021001c2c0000c810312906d4104020700401c0900b00003111510303200203aa60b130020181c152242030004c800010950b5010510891042e40f5510032180500a0f03212160a40b800182c1000608222907103610b88001d6142c00210659808101e81801a102d2400d174400600c580c0c0c0002c03d03e00d081c4000c1500380034140010300b152920510034040e8601d010203d04402104c00e03901d10b480031056000480290482c180301c5500030782080f1001602c4541080228411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 430149721 1250 430148471 430148473
    0x7030503040c230925022406030d0c03021204060e0901060305040b0604180812071103030421140313050c120303042012010e070b04030b130c08011805 66
    0x5961111840395040c3c04050008000d02c4001d4800c0c10a400c0581030a60400090b00500394440c0c40b001848588115404110f0016000b02a0030091010f4070088000e070f021a41121300000d141c12000310b84d84400c2040220102308203800e0000605000b805404400703002a12440d036680e441d45001f42409030206030703c50060402500001e00d00740300f80704081c01035504c40292013a6448240410010b031102c11004000003803880007030070000da8400020607200089500c02d00c40c0d4685410040e000f1070360026000d03a280c01c10002c00c0002200c415000c600c4038590283c00442e00c2115800b1200c0d50343c1480040b100010001c184803079159181c0030404807910900c1214a039540203801d104403000510230800c00c0c1e51060002c1b030001003002a038813805025118a15080a8461000815084403000b015005940d14601218600c02c00d026210141c071114220314a00342c6150380340a845113008181d030840d05410b801040821201c0c041e000010520381009000403002500c00c1d001442403803908450b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 430150971 1250 430149721 430149743
    0x1f1806022107080a0c060f1e05070206060612041b0801090b0105101b02030f0a0b10080a020109060509130c020f010f050405150405160603060608061905060c01110703050304 76
    0x4050341c90021074541030751103141c85007400b04200c0141d80024601c601121842d85a20005242c1402c5100303c41010003605c001161014406522404550b0301901c180c0454001404108003501c1d05001c448000304100114415030f500d80c1000b102220595070943c0300d01e000d05000041d042015000118060300400c08100980da0311000c00400c0b010501c4640b0201e1807100000044009500b111429240090182c0704000d0b030304103203141400f00d20130046a52045a10511210505505400c006052503030b005080144150300081d041289074031030103040001c0022a42c51540307801040c008030701500c51091042d00d0607184040d4807540d0340c04c0044650343c079009000981c0005030041600880c0c100c40500b801d850003a1400c220441d0080056900303109054400032055201884000100059503000844500b0084000e1090a025140303a10500d4000f0040580b0300243c3d01000860b102220482d5440910002e4680544203010b070138544e40a003c84c10340f040c036402c000210300c914413404103414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 430152221 1250 430150971 430151023
    0x8070309080d1e0306080606010c050a060626010c05030609041407030b1902030402061602012003040e01060c0c090b030c0d1b0f030506040b040317070e10020c1f180602 74
    0x104544141c07041b13804da58044404100194041c10400c3c0103a4010382c02c0e03c047c002c6589509050701c84551000d440502507681c056a030300005c00000c5141c240c0c1d0710084c0100c9001c0e0708002c0442c08040c02e4944514144130114080142142680030a145600281d460550792800e10380c1d000d51048820000d03981c11202044020344240c400c491203258000d007040d040101c441900340c4000800002241400300e002c3e022036007210015103540344d105926006654403828a01c203240050010f034440313418040f00d542a1400a0090619901503074012440010300350b245030000703440d184801c1581900402c00c040c040c0144010008206140c0003088007010780540d40351411b003000c130041d10000c5c200343c024102140009000a0f0a190005e001c1e1406401d00c05c201d02c0601a04242541d0700400705400c01c10103441406e0443d1010111103407800075081100d03911300890740c944200150302022140003000389200c10f00030840900c00c50040c5049034169501d40364042d64500c11001c2d562091490b03218020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 430153471 1250 430152221 430152227
    0xf09090604150c140304300f0e0609040c1b0303050f01060206010305070b0c010603021806040b090c04090509030d0203070206071715330d0501090e060408070309080d1e 74
    0x9420041035a13204182001914204203d98001030310495281001003020740b1804130b2032003140010304100405040ca10308a6501410000c0e560120340c061100000c03208400da0340711400d403012450b040d540402d5016503410110348841e1006c4150410085043d1a101456403643c80b41d0b204081803aa400fa490362503040a903a2641d00340310041142d80010300901100c40d0110180c58292020070022843d035899500040c24408040072000c5914440e01c02c112a42c9418025a94111000d03100042c0d40e040515181015101d139010702083c0d15200c0010808501d01001120581c0d440e52108546038141480b009440d01010744413180040c1e18000540390951201170707a980214244070000d0041d500010600c1102d041b0540103a040c503030304180c0408e1891000001d0900340141102c1c0554944052250008892041e0403140e5458507100a0303072031102c800604190855007002d0030381e84801103858119003460541c0c00203441405440e0820740000e4014600d2112a6450300743d0002c0d140200c4001c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 430154721 1250 430153471 430153481
    0x20f0903010e0c030604031b0b01090903031d1e160b0918060a0306050601050c0a05060601030c1b0b180106080d030b0f0a060813050f0703060c0906120203060f0909060415 75
    0x40d13906400820200d00020f000310000ca00c07107040d1010080d40c0e65541e441c4c00000142c00da00000720a030321803d00104050f810300c58074100b01404107000c130791f0045c0712102c25514a40511030824881c1c2c024481d2148900c100940035117400000301c50301c01d060f298003541d40650420000d0b14007444011858610a4050000040c4100c001404003101d103860740d103c0d50003614004c2c2c0b41c45c1c1803010070050b003000940b040c0440e40c4154081c000804160819900042c11034008180c407400700048004080715072040302ca5100743c03c0e034200d00b10600648601450520090303440301681078561800a0006a04001050b40d080107006500d00304500c0e9919400d003c003402c0b00804050340815010414008107008080b0160000e1101c600c2002d100265035800741b51605a00c804503007035000741010810401d584c01010351820092070090031b00c515203040036142185024112101c0c0350044000b40407511005d00744912102c004218510324101010000d80390041610103803072401100262241b001c40d903000e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 430155971 1250 430154721 430154743
    0x10807090605091c02040905010504030219020105040b0f04050d030905030c09010e19240f05031216260d0f0203130212011404050d02061b0a031a04020f0903010e 71
    0x142c51425941d6010003080080d07803240c0c0d005030144801c0c5900546c03154812203241c1342c4510b00000d201d040504011780f51608425100c20703200c80d02a090360050740d0120030343e421508803440e150388444020003803a003940942d40140d03030032581c105000340a060b84011101c0c00c450084c0c059030103145a0301c2c02e012190100340110400141000045141e400426a000410b4604d02400040c50f920304100c00d050303880318442d200600350442c2c4080c0442130700050343d080207200442c002c01c00740400c220f003c01c550140c18041c50100f1818500b40b0709101c01c04030b141492940500c1f0140030b65502040200040e000040b848a01c00c1c9041c0c125042c0c80858400c483c0a140d0f4031614032500003040e0300300034402c41080800540d43d501c400e02500860f00a02030315000754403800c0078100070300114100a140400c0208501c03000c8007841c4030f20000c0c0c140e01c0100c40d10454140390214030040781110320b034561604015282d40061002402200761764038040500b02c2070f40120000d101c40c590907402c20341e80b0300808030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 430157221 1250 430155971 430155977
    0x609050d0314131a09030c06070f030c0512041d090106050915120604030302041701050f0621100605040f020c030f1b150703180b0f091005150108070906 67
    0x42031003401d0109000b420040c0c004a44080703650b40c032600c0914440103843c0c440d04c0c54640c00309074a00c141c60305210b10500c86a041e28414100182520b50145075011507002070140800c0400f050f00f8003c09011014865100460b82c81c0c0e92517858455203181091040441c00f1040d8610218405c0300e818000c0350b0031103000500058141d22a16005180e450701c41810662041401e1071011000c0804c0c08424400d5000e40c400507201c1d4a000320f01702c50464030346014500b07a490181041003490ad42a41150000415981a000901004d1020210100350155256244595240c0300da12060a401c00c0040c0c0d0001d56007400b0812400d015003069001e0100044002c1e0000e1141400c0b90490902414443c10000503246d00038850480c540e00b0200c200c0f003410f8103c44024200007525403d8090144582d8080783d10240445550305c5400ba006000703803064280200b40310100f040c4803800c021150941002032030410580c10034160f450300000e0b4440050780860300340c40001c0e04d058091009401140c40c591 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 430158471 1250 430157221 430157237
    0xc0203190c05120310080a0602040504050601090b190e060c01050403020c06130b0d02040b040b071703150f0a050a0807051e0307031e080d050a0b060a051803070b0f03010609050d03 79
    0x1c4140852904000e01217015003144c1800081d11510412030051074030301504005075900d040206201c240e510003810103050015000d020003410103240f003141d0b0707a8000860a20b002111030607048808062444515601070000300310f01c00c0a10042d400300d4010303031080c1c084848400701401803180c42e00580e600c649071850040020005081d0040080c40c1036408000f00510f0280c68580400d090b4205801c10b8003c4040440e400d020400c030103000e05c04200b0300c51001811842c190701d11002d0041100c80b16800703190340c0301d04a0310b035455842e820400741400401a904175500c80c2c5045569007001d2003017610540c6000408050000c007042c01101c013181c09000340c01c1690943e2141d044002e400c4c0030010070a0103100c004030100701d9200180409a00d015804a1641440b00d000c0d82a5210405010b200791010813030708800980050072106000808894158401c00100010781000015440b80e01000310000d0140c007604c00e80383c011810f8075280e03221914082d80b651300380310300e00481c2040200840d002c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 430159721 1250 430158471 430158493
    0x2070c0810050a0b30030a022104030b01050d02041b02010209130e060112030507050d0e18070206070c0507440d0302071103072606190c020a060c0203190c05 69
    0xa074402d170312054404000c01020500c10f4040034510740c08603803a40016000785900c808000e45d00444640c04010302d04215090600b50f840b4085a00c0043c421136100c1c84450b003066046480359001296206d042c9100c0c10290504208064040e43c00029090300c40e0b4222550f02600030404e20407480e402007800001d040a84c281102d40064501e028016030500c082440741030009001000720102e19481d554a40d8000c5c680f050a10528141c55101805114500010031402517130024109078000c56030b107040e484c00c040030f043c901e0030034107590000202d01400c00d00100c03414a100e1007501030b0007000c030002e0512110002c0360780440211194404d2445e0415003003205060321076006000054056000303104a8400040020304e0807059522007151542d0486860140c10340e034110715051802e40b0030240c8124030b45590034100143d140d00350032245030341d107200341c924051080001003003082d44440100440040305001a41c3d1350003108000e00c0c0e21035408240760300940307d107074010f0016500c58002c080315109 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 430160971 1250 430159721 430159759
    0x32403020607080705010c031d15160c061503030809062a0d0e0a050601080f0703020423070503010e070309110103270803090610060504120602070c0810050a0b 70
    0x12002c400e0728a101c09009100108000b84144c0ea000101a00c000400a0300a61400604241140800b0583c0c0142c062038540c04865a1142d0b844500400c4011062000e0700f025100c400380c0c4c44000d4070181c0b40c1100301e0b40c8030301c3e000d448006590080d140e6000541c2c8a0b45e106541308800c03100050030541d652070f2040304807580040d04c41d110b14800c1440d414a45c42e803031000304480c807918201045034001080d0005024050040a000d0103440020346920030700d4261040e40c0f1180ba10000b4004c0340d40e0800c00007071040c11280c844071103000e6594000e01e410420b80080298200303004542680142d4004900068003a106490545034094074504403040d03050015030092115071541105070300c82e94020360001c1002c4c3c107480340c45845055400d44a003041c402c4107150080080c2200c02c0c86a44050611400e81c1080c09d0300c0071644c18010386800d00d501482d1540203400b0b02c00004145022415000c51070a0b070100e800302c0c140c420080208070301e03510504624140d0b0f000308074603508100101c000c0c418900c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 430162221 1250 430160971 430160977
    0x1d01092d0b010504030f0308072c0d0503040902031807080706120b150316030f05090c10020111070c030303050601030501031e08121501020f0a020109210210030c0324030206 76
    0x20141401130505680391110002e4000c020002c500141c1400d04200e550b541100982414005841405d6a0004507101c98071040000c1402c003480b82c84040d14074803c2101c104210b5002d40a0148250740f2030815290000380c0c42009001d00d1294024410b012814000c000340d10803c855080c0c0d5000b0421544402031001040c440c80110b41001f040207802000d46100001580111950700c80d1810084581000030102c40400018803804c50500301441007001c00041c0071000c20000310b41804004682c100140d0042c4201400700710300120101d650014004040940344c00c8a00944040c4940c0c1d4400700110102e4100b400010f1090000e075000080c0502001c801840661003494550714040c8102141c0f405410221030b4000080c42201c001c50070703075078184051545810020020104d1025590010780070340444d008600d90980480d07074038060698940541070003c2d40180c5186240e00030328a000300509066070031500802e00704200580d00c100200c040010013406074030128009401c5500f001000e038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 430163471 1250 430162221 430162241
    0xa0506070c17030613110d14010806180a1406041a07120c030b0a09020705010c020f0607030203040f0206130e10060c0602070804030b0a0b13020c1b0a1d01092d 70
    0x482200c007417149200b03101d80d0a02c034401c1d500c801c0e1692120f101c00c10595101c15091658100400010403241c82d0019102e03401c001d858981920360089154110711b40801204080c0c8028008007860002940105005004900410100704c035103d0b0300c200002b00e00415900500050380700d10400f442e0405a5100840b02070041c5808220444518009081d004041e000701000319070005405c400c0050901c03808801b40303682d00240188030f040011b91610f809004010340140358000001408001c8028404c0112660080c8040d13144c0640d6414901410854040c3c0302007980490046a18034034a0880d240464409540b8271815504580c0c401d0080c3d00001d00883c2c02c1e42040c48040001002e41c142d03584541d02c1454006196402e4500700644007a406080304000b91041280900000300401c00c054400c10300e50310400c6a0860342e000c035284d801c01d540045481d070318003000020543c0d8000e6015040710181203051200701d01880040c002d5140c82d102045020100007040112003070b01c2d4000381d4442d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 430164721 1250 430163471 430163479
    0x3080a0c09350d09080f0106030803071d040f0903020d110d18120f12030504030e06130b0313020a0b2a011b0e010219080301090b1c050a0506070c170306 67
    0x10500b0320094a84044650000701140b1000d405000c3c40740200729400e241c0140400a00c01e0528540310001ca43c80f0280c000700030010b48172030740402c000803c84440354241c00a4400c002044c3d810b141c0000500c00498210010f0140e1040c031100c1c0c0340f00740c01640a589040018084042e1840802e44001081d00c0380396640d8006403e0000340d80d503c0751945501d41d4082c20208048880515102914441102008041c94903010900011a9120350180c05011090320103030b47e101195000d04075050000e0b841100e051070004200000b042e01e0075000c21185100303540b448003054541702c601344d041c040c2c60104d5807240d8241c5481c00034480c00c030b1503800c0000180d0b000041e60071440852003c900c0313503106010b0081242d4100c00d6005503030400904c90030481048860381324025a584010b041c0c8030610458450b161106441e414030383c0c031503c006000420551000c07045038a81d00d070480c0c8519a940007941d0500031980040c1c034641c02800c03200003440d4000013100c40d8001518205013181c00185c112908 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 430165971 1250 430164721 430164809
    0x1112030405040b0a1d04030f1e210f0b040b060319020703171303090510020a030509041d0706030c0503041505130812160f020c0409020103140403080a0c09 68
    0x10340a00349550072030f00f24048500700107446e060501414070305100841c2e0003000500321000c065507047d54a0441501801c2c545414075408030801084107403100d40140b1001c40ca011101d1104105a0707110f60011502070310705010f006600300810801e030004072854008c10b041030520000c2d05245600400040d88241000e0f8880130718150100381c0b00d04d041721501104003400180c002416044082000204400c542c4443d0b880f00e2400000d4803520402002020320001095400c20341d1344540100c07007482040c50510f900c078150908401d585026511690000c03a1070300f8500c280b060b1103802140d00c2550420510b0b90641c005408110080900030500c07659040070a00c80b000085031900185030540703400691441506208517008107541d10b50000f40b0070f00640170904045607401148541003101b086500103000001ea00044e8098150001c069508100e100100000c06801483c03590041004807401c00180030201c01c1920144030a00440d1308810384801c11441e0941280e5105002800d80355810300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 430167221 1250 430165971 430165979
    0x504032a06020c090109060303020309130605060a030b090907030206041215140901050106020c13151505040f0905010e0f0403030f051e060303040b0a12090503161112030405040b0a 79
    0x40c550405410240041e040607140c59410300d040c404840c050321900c1400c02504d45540e6002e076481c030030040c010380a13000004404030031015580c4280000c11001e092a50b490040b010010b00804507a40310500c036607003103800b1650f078010016a0405407640a07200c5403405040c80b0030303640030300c240760001c850101d503c040f04e402c0400640680480040c0c070042a94490a0030240c040c00c0d100705130014000c550080140e03000c82e94034540d40724004d0384d0134040018900d0150001030110b034456045087d0300c00e49280804212540071004004403000b00081c034891644441c2b80d942039038003e118003950300000030003090350941da840c661900309219090000c1e80354016526034055506c11268150342d403800080000c0d40d43c3c80c00c00c1c03095114004130099842d160800c026581a4003d00d661581003280300e0403003a020668a511849480384c0041c0ac485e21004102c001e040c10401c0c412003254482204541280302d42020700c400621040020301450402d410581070100416515501300d03800b1000c102e0000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 430168471 1250 430167221 430167293
    0x6140903030708030618070f03090f0b0f01061b21031805070521190c0f032321030606041d1518011a0d0f0b030d0201060303050403 58
    0x301d0b1520820016840340b81240400180c00010902c0070001c4820404120020741c1c4258625004013942c07c0c00140b1803d2030614505200962800804868040d0184036601d14070107580c504032801c5503140041d001c0c0015410103041c05070381e0001d20400b059154150303580141500e000c0101458035000842d1030002041843d000120101500d0f0b03904281c0c400d1001c0d0074412080c0c101090003c080000d5071101020056540001c143c410f17a212960340344500400002d40d1610700108a60901089080e0300d9003850061250456450707082c0b207122000450341d030280810025503800c082ea40a08448001810300015035000a04c801c0e40000d04010108003030307200900c660b8140380e19404040007071605608140c185020b205400b0321498103a40105000081000030300e0545107603444002d4001040d10300240240075007112440f5850620580d2070144d6180e0b4455004403001320201c1c1c908800304001682224814000038001500070802400411030050072040c061900a1008024903a005190 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 430169721 1250 430168471 430168477
    0x60c030c120e1e0109060e0904080d090215030708150d170c0d080406050109020301030804030f02030a0804090e0705061306110c0d2906060a0e0a0302030613020a1a040614090303 78
    0x54800f180c92220f086a465a001c4c0050024000500f048004540c034980000d08150713005200602036180040c0d03010003da0190411800d603070b400340c0071503c5801c0c89544001d640d00708985500c00204000d001032104c1c1c1c0d50740c82d1890420405400d18410f0541a11000c818405044603500d00303400401070070707807075a804004a180a1605644014040c1401c0c43d0200036a074040c1e1140003503a0043c4011b00102d400207088500b00e0794408812a86980f00d44082401c207022840040c2924030040b41c0014074409a0f0800c00c0d041a03000c0940300c451341c48200b00301c064020b900602c1c82a14000780c0510043d40100b1a10148044010403148520220800105096007501c402c0702c40e0504c1640044650040002c0c0382d00103864000e1040c098940b5801003290740c00382442d05401c10007116280c040c65100d01d40c64030040c50700036050b03451a00e000320000500c802d0400b404ca0180400f41170000d02001d180745180c24805060611070319161811030300700c8102c0101c0100c403ea43c0320801000145680801c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 430170971 1250 430169721 430169749
    0x150f130e032a070503030405100903021905030d030504150c05090a060f020f071401081305010c0302031f03260c01020408070312080601080703020c0304120b040c060c030c120e 77
    0xb0000d058803419030707400c60324540c003818040d0340d40c0503000501080d54044241c8064a01c00d1307405000002c1b0505045446003502d900282d0022262011201e900614021404c03e4540c140d040f502d4405212004408a4070121009000303131142e404240c4010001d5002080544d4880c50003a003087d030a030000441c080481d51240c4080780c400c21a00141c0d0f9014071650016801801c00303000303100e10385150103800d1303044404041c0c10049c100740090400403044100b0540c10b50800020002424652000f400950007500c1c2d030f500203100d010002007000031008460b0181ca80c84007015040e07045003c24000c088040c004062805a8140007074807178442c0900c003410080488400038003403a4a0350502801c1000449507180400c124181040071076604801f00e13980094161400690707a10360201e0940c04c0d8020390300803d0f08a0080c1c00d00106104030480f01c00e0051307006e01100c1601c65550319050710031041c80310009005c555031b8800c00001c51b40016031192040c0290031f0052050764401c000038a9150700039a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 430172221 1250 430170971 430170997
    0x60310050315070f050d0e0f0c0a050a0305100905030909091501090c08070f020718140a0903091a04090501081e03040521160b030f150f130e03 63
    0x12003041507150400101c81098429404440103080854000704402c0060f150714041c010f000441e110500d4080d40204144861034045c0c0380410612103590392580203039103e451162490540104880c0381c613100030380440e58084002e11004200002180c050b103030141c0f080d01c01d40800c0c05000001e4680801d154482c50700c20000d0b009600260301c282510420681205081c00c1c50283c100e900a03030400f12050b0010002e0803c41600c3c201c441d8100d2501c00c842d0840458405520600c0506c0810f5403c415026540f0040585407036545461101c1150301034400035000070560801001800240001140b00780840850180703065120b00844060781c100307904c03140d0554400d40100f191a200c070350340311841d4030043c00034600c2d00303282400180315648101d000700031005052000503907554041140c2d207603400f026082025140c1e6500506a440d403c03c5940c0145580807500142100c8040c103c80104594001e01601c03680c1120020300044220821003c24a25074903002e54400f088100054958052400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 430173471 1250 430172221 430172251
    0xa0f080d0c080c07030305060334050d03020a1506030204140108011b1d060c191704030506011403031308010c09090b1c170703030902040b060310050907030b0603 71
    0x400240c100e80805405908108080051110503590310003164003e58040c9070100d001c2e00c8540000f0f0600c030005c940c106401030800c2a41d20382e8411000c51b42c3c10012190380c0800c066540d88140301c0024558840200103800001044000840480000c0610201980700041d201c0d00c83c0c3c041000c90700003507011032a800b500001001800d00034040c0007802c03410190561003005684c07030094521030456540540314a1a002c0060194031a5002d4485403c0c00e641122090f28808107090740180401c03505803000400e101200c0d45090a0380212821039510070024130301030b8681214215801ca07051562603050100308955007004028030303410030291181c81e000117140101c00c0006020300b21594000000c10381020680c442c955114242840c48107840306a4414041561404125518800090004904001c150003081c50351650060452030b10940c2c04201003540c00c410803445000c21680410440089001400b190424044140d004a607074140410702c0e03038108001030310b0381c1c004940e4210b28642c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 430174721 1250 430173471 430173487
    0x622120801090b1c080a2105040c050d031d0d0807050106091d070509070203040512300a0c02030708010f05040507050109060212220e04060605040203090d08090a0f08 73
    0x5403040380c06190040f0b0303150341c0075a142c01030010425443c40005e0980780001c40d00d151441c0c01903002d001c2c00c0c0c002c0e8001180c2c0041141080d030040806039010b0340d810440100200d03c13814681c0da02025076805440d60384c1c1c0c2c0038820420008500d003140c501c58000d66813203413040011301c01d00050240c80d84100d0000c2001410400d00c0c504a0701c0c04908900004400241b403203804601007400380076a10700b50303078580d400c8da50f0308401c0e46544125480203400400030484502c0c5104046414488460303c0421100c5140c4009841803844090384680070204004000710201c560098604001052000c0d003074503a01f035502c03280d81d4210780e100e84d1a010300940320001c100070000b0a006a030041c0009080c0944090304010000390303521340e4404091440d0700d001618007a4039000d020030900c03090030442811200c503110100325160040a0324100c802901307020001c1054a414020fa0b17200714495070040051148400b01102c403503034003401c15480c500400c4a1100420004000b039803076103024860711980c80c416 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 430175971 1250 430174721 430174739
    0x10b040b0301020a0905060906041508090f21070204060e0a0218182205030f070b06031219050d020a0203040f06020303070c0f03051b010b01020c0904050622120801 72
    0x1000c42a10903481004400103003604220542d00359902075411988440948022074060b1145401404400d00e04e400902081c51740648120b1040a0f03050507a55111114201d0b155610a11800002d404042d08d5004840d22110300c041e1004a000401c0421040d648600e5142c1c0d0703000c2a80c86602503900000c00107003d61011401604001c825580755044045503262001b600b000549085001501c00000300606034016408940c0a034000c0180c0c0d80c0e032484116525034541c0f04d260300303c4001d09000006030803850040344035a108100c2003241e510304000741c0300c049401c0c00040c202400b8054144105080721030700388040c02084100340c0080d60b981e800e000c02881e644901c0c3d840300c811540100308100250307500c02d1583d0005030380907101c00c071111340c40e180035a40c9024403902100740d00c401c05d2a07504034803015080b00391035480c03c1e000d50314022075a8040c00b120a4003168050b040368041070218100b2125000900d41140140310f031680855450b1350b03240860320002c1e0000d00000ca100005002d41d540d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 430177221 1250 430175971 430175981
    0x5131a0108190803060918011b110a0201020a0803060a09060e01050103110307050a031806050f010f1a090f0111061003121e030c0302090d080c0106060807051b0c0a08010b04 76
    0x20040ba1100c400c02c4440c1d07509501c5100050403035014451060125017115a0b80e00c00c40749000c1890001d210241a280032480c0c1000e540040500060f011401300004140100f04101d00f01d406070f0240c07048942580341c03044d0740e0340040d05040d0440341c84400004d44440300d00c20080500005903032180b042d45000001801e807480000b10007403100082007030080140e000412984002c0c1c09040c0850740c400b840120180403c078006000e0180c0f4148020000114940d51070030f410303034405420000303001e5180c014404042c0e460241e4807000074410085060b81c0e18120451400c110300501d8801e005242032640c0e58201281612458a145100c038010310030041c90520401400c12289490303014148824030383d00c21104400d4408041c9a074490550310014880d804031060b100016299070b084448506d480d030303855440b045c000801c6510300b000201d2490301c650100c501542440ea582401c0520001808020702c41c0c0710307040e68a901ca26510903859850b0794220740b006111315800001e1400166043c081911 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 430178471 1250 430177221 430177243
    0x4030e0d0506090d0305090d080606070c060c02130e120904060f060c0b090a0804030305071a090304090605060702010503061905030d0929040b16021e01090e0f04020405131a0108 78
    0x500301b504100c0407410024041c4510041440d141c89540c03100000b0548600c40c1003806010b0800d21140450007503041090419641c0c406e03901c00030030f0461800309900b1030394480c1040d05141c00c045160124040e4175005482c80c1c10b4020320010354980d5452941c121400c0703507400640441d030465620340c2803000800001e5807150246000c2e041034203603135844071050300c114040102841808242d2030709004608441e046c3c00c00e60f402000c8500d00706500042c0d0f030b84c4c200b445500c2d109824808085a1818000c09448403164107849482c10740d201c4008000f068120100482c07804002c108000805030390070011101d0328030340c40e151203620501b4a0a824050000c550010000701d43c1c0f0f00c00300e124206084c3c100d40448860038103040d1a0b0401e0000c40b156100c02c14400395100101191852035030580302c24510351008262941041c19659040080900b4421603810880c0d114540014001d401c1a030040e40d03002801002c1001410150f584101000804048049511540d4001032040702e008002101d202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 430179721 1250 430178471 430178477
    0xd05010b091e0403030c0e0901030b1803120103140a050106090209040e0118060c030b1314070c11010503071b0b01030b0a020708090f0a03140303090c0a06050304020904030e0d0506090d 81
    0x1d00300388601c03a480b00b4026200030200b603030798400640703083d1040c141c8040c1c500c0000c000345002d507506c1c204150501e01c19161256032080040da09541100000204c50b40e402c68100e40d044660303c0d603191035800c0820400f6071710581c01072132200c1d400650700784a104050003000f01c0041e00c506500c81440201c2d4038608061800c2c3c1e160034070140300d6a032a10300521080340c0c4094003081400c42c1420403001381c80030806180d00082000c0c0c00d60301d0061150001d010221f502c0030f40d0005650740082c2100c0494030460054103280070086145211752091000716407010690030301106c104c01c0d0382c0e14203880b0f0015030030949107152100018020003134000707803040d04100421001d505000890b220301881d8852860658030a9102400c803d0380768a039081c1d90750056400c103200c807a00c1d00c04003420649030362044540c4490350084034a15910342c81e0840c1110165195a9551411561346030700344007590401410940500c20041e61031440c1e0b903905d503c4001c42c00d00c0b0340c016042c1801c06401c002e1034009408012814 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 430180971 1250 430179721 430179751
    0x20c010605120606040515030a20040507090911042301080a051b0705070803030c13060807050a050904200705011406060304030f050d090c0e130c0605180d05010b09 72
    0xc0721000068030f0b80c0100c1c0c101c40c0050349445031103041491051043c50503401d8043c001500e01400f0710048003403041041400102c8007414480100802c803007044849401040d41c4c68014000261194400c0c0e041010012a0529060300c5010008003480c24504040340c4905c0c2241d0507080d964842159600800380300818400c504003015000444a036440c0d4003000d402c40442c00f0002e00c203040103400c1c02080550281ca03070760308018154102c0740d400309544580110828a000076281c0c411001f0b24441c00142c0e403134504110f81c204045031554070004d1150360054544200754400b2a07003070304081d0140c81c42c04a16071b0703a41043c90400d081d980c91301c40404001d94403404010040d2207481c100c91344254180b411182c000e641c1d00d819610fa00134000c582140e80d00c0c202c1d42030700700100800c0c200244c941e0450200c03425550100804180300102c000101204c059000400050303010340060401d844201010f46030491340c82010031060183c0d040141c4180e9100d00d4901510b00f41140b1503500007c402c440c0c211 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 430182221 1250 430180971 430180999
    0x30f010c021b0102070905010f0e0903040b0901030e011509021314060a030b0a0b0d0501050f1905090603070b0f130b040b0a14191e03020702150d09080a0201020c010605 74
    0x140740c01401c286070002c296407460859450b8070900c1003202500350403104001c50358440c000400c80a105000e001034508040700410748a01e000401c0c0da0403641d4011216103000314403001100503208070320003c0c05075902d64503244003509066800c400906102d03800141c80d10030500e140320788500650310002008100202d8031f400c50b1a18811038984050a04022459049a00115014108551041c03104010100d6420340c1544290002c034102d640445640c1c0d0300859441c200b00034a403030003880050b0b0045400d42003100c0d05003000810390020380101a50909075440e1240b0201e07078843c4543d1107450900041105a0041d40c82d8004050031501900f03e0501d81020110009840b6440380360090042c80d40c01c01820280c0d090454010040c00003440911001c0715401416281c500c50302040040c15140d181d461140c881d100740c0d54590f40046c0f0744810400e80d41d6968420340e00041140300703016103d000403c0400c0108d4002c20300e114281d4001a074803048401018212140340d0400c83c451040381e2103401c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 430183471 1250 430182221 430182223
    0x206070b040b31020915090915070318060c0e12160816030308100f030b091e030a080c13060903050f0a2f1005040611030a0503070c0303020d1a030f010c02 68
    0x2920580e058520001c90b1b00e4000740f400700d00c0d25903000c0d00e0b40166003030b041007407246000c0f07a6201c0c1d4451007210350398144ca17100070076001e071103098030300c0b01900c0410711500000c10001d030040d01444105041816400301014081005184000410055a8000940c4082c240c1003880810700810514001d084610942001001c1e1082544005400c2150390070101da003510141c42100d000341060139550707040c00d070749252460800728201e401a40318010410003c1401c48200062a0701c01e0030007014518201080c94162040c02018090900c0040207106094007201c00010036005410140c0b00c89403820b01e9403a02d180f0b06008003481149507081448041d0001e0301d400d0700c40b035050240e120710003000441465001d0160702d2802c1500c0c1c0c03011844c003e8000c02034000006000380c81b420755617801b80f03103a8522120354a2041402c0803002600400c001140b45204000d076000b8139100345005803402c01070400382000d0b03e01c12011035508407010b86200c0414a020011016405441c01c000c0c40080e280713640107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 430184721 1250 430183471 430183561
    0x109020903150717090c0306130618031407111c2f010c1e0c0f0b0903190212010f0501091a010806011107030506010801021e0f0409090206070b040b 65
    0x31804c444440004c00c00c0c07608184140c411610010302101c465107043d000682203450044000e5171080e14041c4003041c29001117090350a129090340b102740390003410807d01c41340f6500551081c0c0e40c0050020f02c1e0039003075480d032079002c0710190740d41c40a405660490800010010242d4008100690044008500c0c10402c41d5900c00b140803d003000310213066070342411f000c51801000038000703044041082c0e0b0200400d400d440003e5074003201040da1115103070200d0104501c142e0501d40c0c0d140e8850140744040b0800e40417101c0400c0d00c090705003291206c02032903584c2510030496004e8403058036140184031711b2155108402540d049040c2c504566800100080d1011782c0c05130a00d030400c9001d50480c80000ca0070488070b4000d56011088440302c0d80d5070703440c560003500400112400e50790026110714022240000b560221560800c00d180b80034070300200c0200501c020320080717030000e00038400c14022600580c03000384514020a016507023807800072308a0543c02c3d0074a010507081041104913003840701d01c070450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 430185971 1250 430184721 430184747
    0x212030322020609060a02010c090611120a020a1202060618011d09190b060f0a03080d0c0309141608010614060c0304030501110c06070306180b0103060e01090209031507 74
    0x70328120301500c2d00204030a0711481c84143d030095400520100d54660540c0603a040d0041d0703945525010342c41d2031044451200711096500607034403850740f8007000c0c08510020503581c8042d004884104410741e0b104800e40903041002d40160700020204485070501c90502c21946504204c05a030941c1480790800c030b450001e810350480020f0041c0007034a4600108903213007600c4610800c00d08400300c5483c140c02c0d944000c80305140100221207800010f03041036503010701560345c041c211904044640800000a001c09107040c0c00701a01d89040314042115815070141100f02c0314007070119140d4101440154416642c00020903a01d492010046e000046009001c006800c4138002d64a5200c0aa038520f18041e5800140903546041d40c00c420318502a00104042501e810079a001507985c440c0603000c5441c01d108001404000724030314404940c0541c4000741d0808141000154240c4441e100c0d001051700341c01c032034031284c0c0c0001c00709160701c0c04004c45181d0310b00c0d013005032203143142c400c000034848a40e50817 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 430187221 1250 430185971 430186021
    0x70905100311010c060f0c0e04021204030c03090e0705090f120613020d081209100504020d1515090204081207080901050306060c0d020604020406060216051003180c0302120303 77
    0x702c448543d84c843d40100c00c0b0b442e00a0018051a5a500da0420081414000c024042054411801c1441c285802a1800102c02459126256403680ca0035182e05403048001ca081000701000414281c000407071003805108681d840c1070301c0381c40711350a1000c1e000c8100c2c81a031180020005c1600c0ca0f00b800542c043e480340300c0a07109070a4400510101d02c81c5024420300521412000c1a000414000010010311508503030303049032030070002c4829601c1243e07815100030390021420070888012445152148680b1007800b50001800100060511100030030307030700075002003600010104032003d02085060707000341c0e0b49240c09140211503900d003244c81c80ba0346d040c10b0606c0008030000f1303610f64a15054071041103010301a20082c568441c002511072004580c101d1141e844c089001c10100c0c40061000c1440c1c80108802241e2800c1400b00f14090001104000c02c040d150440c2a459202d80800c807020f0324811960344008600350b204006644000c614002e126510502c200301c4d64500d0382104c4052128618 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 430188471 1250 430187221 430187243
    0x10050d0b0a1e0e030910181214010905010b03060a11030105040504030504050d05010506151218010f0e060906010605092103090d21091512060816080709051003 70
    0xd1101c4403091016403010382210b150150009006101200030241801c08807030031040708907200341c140c7d0000211503c01500d622090401e1042c00e01d84840d00b070580340201e03070384120031174000551405e5541641c402c40c1e19945035004401d00b420b041000c2504040448000d12909031042443e40107800144038581c8a07a0701c5401190030b16028104540c050311014155601c8940a42041c5002c1c06061b600d0034050b070700d810201a00e03101400142c40c42021304091010640c2c031010071902c012440030241032855580c58801151048503440341040c3e0744000c20182603146000c0030420300b4020146e000000b4404200000c03100e50b82c3d9025410441d95460480c0490600601011072a501030b0805050b089011405000203001003081c4403c0d03100a540b29104001c0c0d10720008031501c408070f00c03c070303648030059008030301c00e26000e680c00c10506801000300050a41ea540500e510b42000740e00000c07100b2055030b03014483e804080c040301002e0074061100340440c0c240660102a0202c052001038810b0340c2c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 430189721 1250 430188471 430188491
    0x5060603093406020714190501200d0e0102060610080f04050307120c061503170d18030305071e080a022101030c050307080106030b010e27030310050d0b0a 68
    0x110350440c40003610b00c0e814050054075254040d685518a00501d44038140ca0840d954061510001f001d01d4038000e1141c000400b0725080056508500505030400151281e0304402c01d6000104a05c4001c82c030030f541c41100c0b032842c42d0000390400c280940b0703580c0128500955010703890707042920746402460550f5118055960703803d1041c214018818010a040408450500d8a50740201009052401100100050151003440c0030401d9540e03c002400c401401207074001425810016100384880c0e00c0001c17407030005090041015000c40201140440e5031a42030102060b031111b1606454605003151440c64000807002419499000744850701c4940c001906102d90500030360414501c644030209410a541c403490100480c2821303000c0e40d40a0301c541c4c400000c100300140140d0341102e80240c00b02203182d0801051131101680200401e009070030030003142858190900d2010820261500030310303183e0034510303c400081e204541c400d910400c421032058020500340000c6580203e100d11000543c09a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 430190971 1250 430189721 430189783
    0xa0f0c1e081309090b0705190e06120c0304030e0901140f012c01080912040b0901030b030703110405070507050c040e0705030703150c180605030601020309060f0703030506060309 78
    0xd0500b007040120b032014000900a801d6422503034a0300d03c0740308031380e03140d5803034220460b558042c901c2c6181c000d4400060030060580140003010a100001d00000d26258400081d00c581d024140d4694600c000c0010801c02455803000c084c860400d422583c446c150b51501c0702e0701c00291a031901c0b0602c114005400c040242e801400c50304040a4141030303203410600603503502203081468002c0180821003040c0003c1002c40702255000c03210b15540d045506107401d0000080c0d494026401c0d25040c19030700d803022a07440d0740c10401200110300c1402250322081c072420030300056131000f6011800740300080c0202c500050021602c1d0500003415180010010142c80c40c1030300c0c00b10103511175030f01400360720b10206c1440030040204d41c1c08079400e4401e004025040c0422601010221802c03040c0340901c0000f8011140300380000e540100051040301c2c146844080000d003e5031062003100780c10000000c0d8541096090b010310750740000c0c00c0340c5807030851070a411003540f21665001c15040b04462040c00c0400032038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 430192221 1250 430190971 430190977
    0x3070c0204050910110c0d052a06010801110405063007030e01150501050405090c090312071401140105042a0c0201020f190b060f0d06020a0f0c1e08 65
    0x380080c03061056050a0411a854000e136120f56009a0700707100701050214858000c4622030705003c0c00802c69101c2d2440c0844047d0007050407205a540302d8030b03400402c015001e0000c01e40c0c903026000342c011540351407101400c41d0050383d00f1048105040c40204003c0e514035082e6840c0b1044c100e0401c9403c1c900145801c0c250000c031513180c10050000051001480e03140c1c0c400d0210340b00400007000340c80078080070b0b0711510481d03108180c0044d00401090000e401c1c202401d40d00032818aa030b040c00c117084040000d0500c038011400d6000d642d004038000061003080080106001e99080080111594503c407a07140c40c00c2c140103d03401203403162009406102d004411088150040100f4140000130b004020081c03004030070281c0c01403191442d0f1f1180c004010800345910341007440075040384038180c2e51307442040e04001d200c60f605c0307600c1d11001101c0d5110f010400030228450800140d4031124110040d0078010114a4281001004181d1500003100e000d801d060991040440d040c00c1c90580c80c002c0e0b4144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 430193471 1250 430192221 430192223
    0x11e0507031b0509190513020f070501050705270d021c0501060e0a0c050a020a020f0d020306071101180f0611090a03110a121122020a020304050a080c090c03070c 71
    0x481e00950303500b2450392103000380c211408200c84541c61440d0101c2c085007560141c0c02010307804822065036000640041c2e00401e074942e1461001e500703062240d25568211076003210094007285001804030100c500b80b282c03140d00c000813070810410350303110140403403041c64590070028000c1030340c5d406070007041030a16001e61134a07500000030300505448000c1c05120f000d00b03540e41c0307401c90f00f001504002d5602503400e43d2210100c40c3e0060903100125000c0216030b03000010300340c5d004102c2c5003d200158500740449072003803119849600c941014120030900b104d050841070808101c40c3c41026000031020b0313000c030344e800381c000001140945a088010b40f0920030300b806154071040c20030300042082500e070086038a900c8101c6050301c1403940da85c10b0b200c5074a0032103c001c0c03c14003a400d1744001d038504603051140c545c0500301c0000345071449410340022607212040c0e401c0542d10200f0201b00c0d5192400041018200117005040c1d0841458081801000042c005036103240300840080c5080d4480c0b01e80c91441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 430194721 1250 430193471 430193501
    0x6040311101505100f1202090f041107141b0112181a0109060b041509051201090b0c04050604030b0a090c030606080c0f0603130302010f0903081008011e050703 70
    0x794405482c002d024030742900c41c2c980030300e8185441404040c0114240318074210507032a802c01a10000200b01e00075407103415070f01d910014600400d600d80d1110720941d8100c04040f030707209a40e100039080010800d0f02001201003989d0204080540f5900388803409095144c003030802095009150703031220051302101c1a54032148020344021020b00081c541c80c10350044000c9512002a6200c00307044087e15058000c103001d810b070401041005901010700c041d841c032010700c2d0500c2519180c81c00102807010310081840180e440d16030540038080020582070300700b05507441c003d181c103240401050484c003a9110141605c101500000c40d0072401d50800c5403159400b00074449032617100e02d4644010b100d41e028981451007140701120b41c41c1046c803a00fa6070004020500b50559654545441c10303041c01080440865480c1c4050b100d540c2e03000e020b5260020311a403684d07640d0b03242404400743c01c2d01980e480500640c2c10f04803007211b0303d0089212100001b8002c000800c0c15039510806078003600c0309188581003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 430195971 1250 430194721 430194731
    0x40b0703180312020a021005150901060e06030c0a17010915060c1101051b0604030503100b0c0a0206090307090219030b03030f190c1a160c02030303061c12050405090f090604031110 79
    0x6801c0d00044d6081c9c614408641e004074a91700c4000072036114109101091300f002c400c201282007443d81d02c01400070300c500e9143c0f11011580142c1c00440041c400e0340204101d503190312070320150340c080000f40c0b0007809861611b1084000300e52078100103400c500300380c9810300000045035040e0f40e040c81c00340740c814545102112210705103498010215801147c0044015000100c04100001c4980c00c44a01d040e100c4020b2000ea00b0b90f400300b00d0154045680213606101b07820b030000e9400c4550000c0c04146400400b9104841c42030035001c3e040e152400710040c400e40082101c96440d00d051410346100c4509102c40c04000d00b003804040d10203071881203014050300030304d810300460494403c118074400c201c51480c0550b21200c5c1d040039030768a500800c00179415003003400003904a04100213108a100070443c0c5800e60100541c942e021034004004045c0000303500010706000f40d0034900c040320703000600410824020701e40b0045040d1503250141c00141000350454607203000a0b0200b0981d04621211601080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 430197221 1250 430195971 430195981
    0x9010c0f230f070f0b0105150d1e06090f0b060306010912020102010b090a02070201031104120818060f03040302071a090d1103160608090114010e100e040b0703180312020a021005 78
    0x1039403125130102203403600744103000444c0c14248034000410880012400c3d0723040c5004900b000024046000301c000c5010f03410241031005e60100e00510000b0800484001905000503c003801569110380710503008040400a21541c1d985c000c01007401c0381c3ea11a20581c0300d1180e840101c1c0500a00040164484600024800c0380a410b5004007003852007601e08022407013100b00b01440390300440c03003141c109042101c0c120012400840081034141c20b080e070f64441008804000561781d4100d00301c17180450704080101b00c20582c041080e071000e850001c44038403410030030518100d8148101d000190290382003118040402605070707103032108060010260f0315685000c0042e9000030180780305280002e9142e4011071030448043c86070703400040c2c00070a00c0d000daa00300705808400c450040c140f050f940c1074481c40003030a594005c032900d000d1881007803d00440e0910400090644085030085510b220f0300c1804030000030317084000102c48500038800580c695588500613401c0c01d91825465602d1414402002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 430198471 1250 430197221 430197233
    0x607120219051909210201090518010e010b07050307030f0309020406080607020c1504050411040b07030f08011409190b0a0b0717040f0b07060e030c0609010c0f230f07 73
    0x3c0010381d039846000c01c0005202800312120160707031290f40348816101c0c461102101400040401c0035006043c030f40505560b50b000305070b045c6d580090181001007014014002443c90042c4180103000581d0070754240216601c4490f141c4c4640c5e00700030b003400034030a9086642030181d0440b0146680042c0304000b85e503a58032004e5201d540c116800c40c018090000381d4080351501c082c8410f2528220341d00035023032900740700610008144080020544020611001034844030380001060030038440e0362070701d02c11f60001d0009000b0060681240c18002c44403d003084072900c540000c00e510641c0e888040110303980542c8800014000c0d440282c0d00100340c1c190100303d0044410003130502070320500e0400c0b00202d2540c0c0e9840d050007240207034034000001c1103003040503101d188082c0c10b810303028200005001c03914100c5689550710484680b01c0030b030040e03020010300940c00c0c0715a40e20090310341441d4a1800182000030300010100300428440441461000254000311041e90b00c1c1d02c2d485a40c555441050741061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 430199721 1250 430198471 430198477
    0x70f3c020a020406080d051905070803100320012f010609060f05120307112e08010801110f0315090106050706060801020405060f0a0309050d110f0105010602060712021905 75
    0x160701813410820b002600361000170f881e0000603401e5035401d060041da40d2044440d40c109200700d03410800301303205100124a0f40002540200505002001401e1462400203002181b0400b00d1410b0840208070070300a0f40c01c5100c0001c01100c4131041e400442c40503444130542c20700a000ca00c10356103003000125460442d41d0100c820317540048100d1020307a03501d108000101c038031211106070513041403050000003146100110f8a005009245068440552010940070303030130354640740c80c81c1ca001c0003d580501d800010082c05403118400a010302c580344250301550384640c0d4003420006c8000000162004800720300352408500007444c8240550b90384000400c1a0842001a640340b490100d0015000310144220740885001620460518881c41003510380e07500803000c140181511040043c00041007400148080c5002d510382038040048216440e10f031880042154902e40c1c904001840324607000544c06500000601d0580c1e925020202181c01074061142c07244090002d8400c030000f0550081c000e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 430200971 1250 430199721 430199723
    0xa0e0706030c1209050a0209040f0803040f0b071e0c0201050d050109050601021902030601060e060c0d0f02010e06040b1b04090608060403141602010806030f150609070f3c020a 77
    0x25000700b103d420032012003101e0281c00000c040d580f200144100505215030070341d50103406100740d40d9400f10f468880035901c0e072040710304031101156001c06004004082601c07982103030252030a81030000d0106542012407400324000c1d0180b000d18034101d411603109600f01c0f282400d1a103402e000e103594811001c0040d00041c3d50715409806812001500c2d09642580b0040300c80e00103004054070b03445c140c419103085810268258000204000c2d10a00d8002002503070103d030004c2e40c1d20b20301440e1030170000342101c58021068000d030b0000d20034131000c90b01107000c0c19007008550601a00182089141030400d2140380e002040880c01d180001504907400301d01284110300940b14801e00390042c0c180d507200b501c100600340c82c0010b003003d52300340554031818129030f002c01c01400700c4503139101c820b01c50740c90007101001141c2c80d80303040400c001440c10803003c1340f03030440007c3c100880d03c001c00c103c000d040380b031b004244000101c00c60f1a6040e408503a80262551029010454150340a42c00b4002500e540135104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 430202221 1250 430200971 430200977
    0x30609060b10081905070507051c031a0d080901020307140607170106020619020d06080a0c091b08040201090509090303041a06060a030f09060c200c180a0e0706030c 72
    0x152185143c00780042510403208450004050001d101ca0300004000180c1000100300003400341d40f00007031080052174801d030f01c0480c0e44c05100308a07030401402d80f000b40d0100e00840040c0c41d18541c043e01c4140c080a00d45600101c041e80354280705004030f185019425028050040024450b00d8290f00442c0e040e02503107003680c50380720007400c201c0c001066000a2092100603404640000c2c045240310803200d0007040d01d50009071a00f07c00d81c0d040816070303401d604046400d0700001e0f0715408000a10000380020700c1c96002c280401510a8245030a2aa84125000502100c03200240c01c40e880b4821101c003a01004003550800d05044611603501d0f003085070112885419910711403003090b5000003252003030100400403450000119822009085003000700107400d525640c03440005101360041101011342035941c100700d880c1e40010318841c00c020700d46649854100e222403141e2a12114420b00328080a0381006819480d0b02118000821341d2503260f24460040d03070004100581d0541040105010960b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 430203471 1250 430202221 430202239
    0x607020a0b040303020d051207030e0a0b0a02091306030c031212050408120a060503190807050d0e031204031703090a020301062c0606030f0907180c45030609060b 71
    0x20242c1f098070a200480556940300700000700d950b482a004004000c200c0d4081d0749004540d642ca0060284e015035001420b15000700b020440c0c1d0804c5e0f20050000c142f11013091149070f185894107440d1500900002d844502014540c4d040c4602071400907243c00c517041e900b044517152908010b141600950034803000e0100e14008500e1072009070007280103498006001e004501c0d01d048885100308114002190901014040e000c0451824400c0204a05654851048140c0d6034020541000130017800c0100190b0107100c2400032800c1112060210029002280e949844030044030345001c00f1010003e40c150300700500032a00705454000d5150441c61a80340c82842c952803480c1d4403019501702c43d01038021406100103400400806c25150300980c0e044c080e90a04c6445240c004900c1c2d00128030580e002d80c403960742040c019408940092440b80b0b410b2100000300130780070041404080c18002c180b2074101940780c65001c3c0c03140d2441a009550104080001e09024540000908203494035184140101e07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 430204721 1250 430203471 430203493
    0x60e0703020309060129031303021203040b0a36031b1703060a0f06020a020a0b041811090303040905190b130c200102070c09020f040302010c020607020a0b04030302 72
    0x380260b90180d106003000c0c0420380e0a0581a0003c0c0003030081c01c0c822035000c0d13114010081c403240000c41c000c2a2540140d0309441c003d040181c80c1c0180103c2120b8130344000c008010100d90350710034654001c000b0000208083c20b508400c0000e503e075100e04021464a800000011030088030410000700b8466217500d00c051030103585110f0700311421480600880c0904507411440c150741402194801002484c42d09503a4681480c03846410041d040500560320407460354043d403030502100401464030054a44c502401e05880241c042c04d030721101c540040d200c9800311007100b80507064804152020342125100c6907220703488005044196a0106101e41500215110161a0041801001003d40800c606d02502d801030001002800c803c0030421506081c0034460b03800c0a10401101c45c5014005600c030300c41801d020141c0c103890791241d409103204211011120b940c0303409035000c503034090920481d081050b001103407041c807a40c20000d511134036540011980144400180050300c2c000e41c01c5078419482 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 430205971 1250 430204721 430204727
    0x60a0c0e010504030b04170c0703060b03071d0a09060213051809150a0b0303031302010f090513020a05040e010602070609091a0d060902040e100b0603010e07050f040b04030303060e07 80
    0x1800103140e00089003040144003040202442a82040c45446040c042440d000c142d0543c1d42c012071001c5217141c02c021070030000c3c00681d019000d00302504602418040389044000000440c140403102400d600840008010450070750111500a0700080b0640d0750711f800c2e4810095039001e42c060103104003811080300c1135812240d00101d1080401900500c40c1800c100841407038901d0081c01107000ca40c9840b2159030649080c009107018806201c18004620103600c00900840d00c420316140401c44101ca0802150303032041c04420000a500e0320040c3d03110550807086030544600c1e08410f0380c1140000c000034085600240d07241c01c6a000d40d032001c21407a120803c41d0b0070381308444030120000d07900350082852031812140c9150110700c02e100c0010500c0c500e03404a01a00d4442030000000c1e007080015607072441490041d81c46180045907030510355818a252182c1c403010140002c0f0800c000415002e4404000c0421034010740b1440f0b002740c0e01d0350740d01e14005000d001140125469072050303c02040a10340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 430207221 1250 430205971 430205987
    0x13150503070902250503070c0b0301031406060112050a06030b013b0106180e130203070602070b2d071506171b13152306070b060d020a08060a0c 63
    0xe400b04240d44c1d07515820706840c3c501c9000c5100761414007003005400001407001e8041c000801d41a501681c681d0b1540c100711820905111074600c00750022010440d00e41c0e8481c00008628013400c1c0b001500c0e45454141d10014001c940004081250140c001310b10340305090103140300340214015400300c0003404030300700740c903a04d188959144442550006100305401007040c5804903034980f4020750187d583b4004c040c070b440d5040e680325040030200340341141036040c144014030262200c1d00061070070500d8807c078000140308400c01d04401844c13500624492100d00084001ca403c220b03148191a0031541c106005a4070803c0c519007800342c079100c40010b69204ca1560000461f49581c0940100e201110000761894400740d4842c3d40a81043d1010308071402c1c0d407241e180d541c1c000340d0300c547c200c60400307100482403411441e00f40c0c0b000400c034000e0304450341e401080f00d00c0c4640c040203803109912050041040340c1581e2400035804001c401d8046400c8200150b46d80c4210079034181030001202204050710200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 430208471 1250 430207221 430207237
    0x40b0a02042610050114040f0509030d1503020d050f060702060601050702040c02070515070b060607240f0c050702010806010903022103090301060308040303260f0613150503070902 79
    0x1448402c0001203a46410580500c00c000d0300c0d00781c81e0002e64140c9280100c074400d800039036440020440084042c10140f090f150315030041d08003003007141005c0003425524083c40c8488004681c071602850b1810800b41e043c1401141e014001110007002071130303c4d0f51550152008003080b80310303540009d8599480090090302608041c1c682510303000080c2c00380400781100c00030030400d611a5903000259521079003404040f01101c032641d10340b80c44403803404142e021300141c41d145c41000140410b01c0031816885d01d1011400e1000d1140c0704058103011130001400f080031a221200e40351001000f175039a0858000c0c64814402d9880001590700e060042d50b542100d40006900304807106a80c06200d01070342c0c05208201c071810116810880403c0001e800e5900d190411280d5440100f401c00130542c005090040c41e05096032a103c1c0c2c1400103003801e42180b002041d9003001034084c00403c46c66200e1889a000044c611030061141101d540100c8800314183c1c0708860003440344000c00207407500c0c0d074070a807a404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 430209721 1250 430208471 430208489
    0x3070206090904062c0d0201020306030c0402131503050115080720010905030412060b03030a050f070206040504020d0516030902031b031f050115030603020102100c091d040b0a0204 79
    0x800010400e202c4104001841101d04a0759000718a80400c0052000c002e000011070103018640319014a403404c01203645511819a0b00510a000ca65178000c40c0c09040c0710420f4500580360300099a880015490b0740e0711002603128008214510680e0503041681a100451000e10582a0000048400a0341180e05074001070040852030390303542e00a40c10803884000c07400003003044141034540e1411035000794400d114a5401d0344690b81084981c2c02107005c5280c0403006541044040c282c05480b9109944600031303c02e80014100342103503610415217010342805401107440e07801d07454079040181800c0e20000044160150000001c82c0320740140c400c05540075003d4007a625180300405403200c1c544007200da040c024981003900b80f1000701c00c94030758014080c101280d00e5242c04400050200f82c0c40461040505015081c805030340c0005003400416480d040028110741101802c0b60b0802c000d401280d0040f0707440729600c070040d9081030081d005600610b03c0c40d101d522a002c204089210707900c241c40003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 430210971 1250 430209721 430209727
    0xc030a0e0f010503270304080f010c1812052b020c040b0d0609060b04050f01060f051207080603121b0714030a0305031308030f041b1802180a091d03070206 68
    0xc00341d090b0741144990a1703890711007900703c2019000582140c1280c1c000310b2440e0b00c92046011a26002d0050404058690504903880301240c8200c0362103403203600610085001c1071181c0030400004104640c82400018000020340d100e1803612100d94880c80c4100c070048c070549040c240c11f031500d0311808034448030040c455031008865603259005801d00f404107640c071395540c5106140a0701d41e802030500c00c2c012440e0780080e6604120000d4180c4a100240b0000c2040500c10031504911141c1c003280c020b810350507d402541d032001c00080c079140a40c11103180d00d60f8082084a1403140a008040350900420b0aa0749907a840350140f60203a03a400c08980c0e4180e01000f004404203000c0c0c0c1c01180c004400b45025842c0c200291101507241c1c0c016541041104440410402848100c15048042c8120b80c640580e19a01d800518403a20111306103184040f0b500059410b41611080140c02c1c0380300700940402030065a41d08554010460704c0c91000608010b00500d14a0800210443e00761650041010b41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 430212221 1250 430210971 430210981
    0x80a0f231c0b090118060801140402091003020f06071b08031305191208070b130c14100809161508060102120406080402060405030f010c2c240c030a0e0f010503 70
    0x2841c0441c0305c982200326550398201041250080c00f4045c1004107a10380142a4201303403040c000c113036400904000341910f99a009000507610940001d580d01c4c07084860b561940c4090410003049003507c03581c42c0f1a101d40030340001c2d600030040050300003154000c155240e110f507a1014041c101c1e1003492a2042c02099841c02e00144150000b092411400f81c020f282c1415082e0740c81c940b82c18015600e540c240d2040c42c00450800142408007405064984148200c0000702800b0070038121141c0c0e0b00c001400800000116104401c105d090022101c8001464010350345a103c0340444440c03005800001d0400740000308903500004411400c7d100c20703007105280c546001001c41d01c0d0000a402260301450401c8001084d550411007042070a004400000718807640b00d1020b00710b22612003940c08203140c05454003038020b040071401c0170008001d0300d11200a07041c901c104140050290310620301c07000d01141d041c003001c10010107030890b26000d88502c41004000e804000881101140190000d202000020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 430213471 1250 430212221 430212239
    0x10e060d0c0e09190c050a1d0411070809091302130513080406030509070e1911070b270105010e1503070504061202040f0207080a0f231c0b0901 63
    0x44018101c41c50898901c1c090b030000900b2118058940c0c105040c18407040300070301c01452007501c8603a1040e0414624080c00c01030080c1500780f0a80c495444150907545004d1a1744503608186401911180322954949072480d000a036a08051800c13800352003e1000504500e40c2510305204c413680081140311028248115030019041c02051003000480c0290854005445031004c0d2015000c1e0f9140422680307840b03111140f50076a158086440105607000303024000d0f0f444948031440441006000c45c804400d884c3c03c85a5105818004064882e03080070001c0f0f0300340c0383d21880c2a025114441814541c502d1004500381c0c0c00070b000b1404402d41590106a00480303400a00a804070080e06440b81660348d18005000c8404a900105d151825003050382d045150a12a5200821095004500f0007200741c8520a490080442c0e0740309004c0041118017100b4080c43e0241c070f081c131884050b02d030480d050303540b40c42c51900000c00c6030701400c4130800b488400320224010f052904a0290080b003407a8a00079261b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 430214721 1250 430213471 430213481
    0xa03020f0d0609020901060c0311060402011209110604080a05060a1b0e130c09140d080901031e0c0c02010806011b1e06050f04030215040f0206030406022b0b010e060d 73
    0xc0307422640e542840300050b217480035101e0092005032100540340c0002e0502400c000390047c0140c0003038014008000040c0e802100f03800a40d40400000140703074040d440c00030340d00d0307a011510380c0e8425000b18000400301000550b401805100d00141e80391030319141c4070700b41964a240e41c81403098a000010010f144c2c0b08450f030342000c2000a08060310f485ca001c3c000c01c211020384000724002035070440c052000081c111048481000240c03a80c2c5400c0016807503d1144d07002d5051154100b40e1210f0001d2449052841241d2302c12141c84410001e60001c41c030007a205034800d42c022408a880310780003500541c09400e044d000041c0c4840e5a4960742002d80d00c1701d240904038000320544ae10f00d03030f0071180810018491340c1d1041c04074080704849402c1c0360601a1801c089094003041c41d10707a520401c400100221000c0c0c1e4510b5042e10001c2d140c0e181da140c1000a401071081c000000c4000c008044a40c40350903110940c130303109035001002810300d03007401100c1c1c0380d0001020540099041141409154440c0e009c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 430215827 1106 430214721 430214723
    0x403031709070302031005061302070b0f04031e03140105121203060d0f050a02152a0109020a060512090d0903060f06050324060a03020f0d 61
    0x610300e052990190300284010000304006200c10407a10024507801015900d51100010090300280021507105100d10f03d0000b101002d0440d51084440d06604140344240387c1c0c0d140d044003144407002620840421048002c480794010403c601900454001d9602082045010407e109081c0068214600c282880c41d8015030010001a61b40440419a424681c130ba55400d00095850440d07210040c2410590b002800108600407480001e5144220307007010024001001c9885280a0a030442d0b80c400c0ca0382401c0d808001048211000c801001c0001184146241c3c0c00324100d0b600d03581c4880c010503000b0441c9191002000c040c01da0201668000303041e1003030442c0d0000d1000e1982d12010302400c0d941c2542050101c055009800540300140c1180c007421134011511641610041c8806c8641d010b050220340d0782e14040e81d03801c04580d0001d1000580039119400c000502c0e0074482c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 430035971 430215827 := by
  have h0 := BRFrame.cov_init 430035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 430035971 ≤ n) (h2 : n < 430215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
