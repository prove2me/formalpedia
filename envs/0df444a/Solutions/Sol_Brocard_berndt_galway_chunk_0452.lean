-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0452
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:52:55.481981+00:00
-- url     : https://prove2.me/submissions/c3ae6f3b-609b-49a8-ab73-6de58986ffce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 81115109 ≤ n < 81294965 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 81116359 1250 81115109 81115169
    0x8100b040e16030b01060503010b0d200f07020a05040525030b0d060204081618090c0b130501020d0309020603070f111608070b070203070501030b061903020406030b0d0b01 75
    0x201203008542c9140107840c1c81c002002c1c02d59009032040001666214000c07030b0f4a1209220307001d080708003030100c000707030740503541203a00344400d2121034141d10040843c5031030755507101441c1c0104120303000072042c0442c2400b034442001868220b80811140ca4200c03440d00300b4005030407401c500200c940b01d0810055009502180d00400098882102220b007403070404000d6102c2d000b1500c691041c1e00b41c2c04d5400300740c400c0030001d0381c2030582034082241200f01944041c00300324000711001c00c8220000318441d8941c102406200000c0a146555603103018006800d260f14601c210080608205c0d440d80036850380021241c000c0c0b054640440d2500b03078a001180d89015250031a08140205010b1386080c03030000e1075120039124900192004503640f5001ca0581d84a41503009425411600080207198000d81c000100c0b2840039002c00c1c90008008405001900b5140d40e000100350b0108050000035071510403040032003801c1c1c89600c110021a1100804480140701d5121301c1513803850502050fa40d002a98 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 81117609 1250 81116359 81116381
    0x7020f0d0b01060509040515131a0607060212130c0b07030e0301020d050901060b0903100b0d0212010903020c01030203010509180f0a0c0815011805040204020f0f030403120608100b04 80
    0x401c850750b155840140160300c0742d0b4509120b82d051601056502c4200030f12001103180007800122800450b56040001e0302802103120b180304000b120b44c84158540000030300025102d04001a42d511014007000410032000d414075003006060b00c24003000484920248054075102e103038045d200c0069203002c03507650821110741c9405500101e10150101120b404c8035004039801c100a02449454900c0002c3d280211400107034958840c022103c3c001106500c044890403001c0c1c541001000305402203a01402125580c00e100e81d91551918241075052005007491882413030154550352401001400850003d07288888a40d003980d800320380d000c003c001c2285074400001c20f441c03c040702d50500e440c01c10741e03622903040103000d0940c020380c40540c0c840502e8140c0300308000300011620f01107517200c01080d005200702e0300a41e080001207221444c5c0c40240585104030401e0a541b031070b091600030003d420302022582241d05100341805071800100b920503006201c0c0200141c4829043c8c002805069a08a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 81118859 1250 81117609 81117623
    0x30423061204110609030d030e16030302060f06030109030c1407030c09060501110109030503040b04080c0105010902040501030c02010e07120602070f0302070608090307022209151d0c030307020f0d 86
    0x154210070040410140301c2d60041c0c1d0600380d15000d540c188111407180201099254014103169004180a030f4404800c4192281c100d645803010700c80b00021401c515041500542d01440802070000b140059803540306400760024030141d05030759405424031900080080c000812440d141c1c0e40c4032010003d5800454020200c40d1a40707a8411142c402401140181c0e400192619019101601c05020b0041c100b6810343c0c0d0720349943e45503111700ca01504082d0048540c3e0400b000b001c141004240151406011410f500582e40c07860b001c00901115003d00f0014156418400303035074008000407440004546e81c7e081c0d040b140c80c50600e07200000307114545008020380c20049100c4181940010300703600b91038107911444a10780701c110071565030303002d1804000e50124003295880100202c440b115540c4000c01c0c000880c12484940e07d5203219084002c0340440c440d9201c422610340001440c5482c208024840680303815040000800d8891059140c00ba01605044800003903548a1560f00780c412900004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 81120109 1250 81118859 81118867
    0x1031e0504110420030406020901020703080c10060e101502010b0301090803040218010807270e0a02091b04170c100f08060418170405100e0405010608060303042306 72
    0x1d80364426402e1503050310f01543c50044110343c00301482c400001a0600d03c0101400e5640b19a2214003a44c0080c040c9411802000070010000323403914060415481c0d4000071f0140400501007440469440f81d100150b003c894030203102c00c401c540d900810980c1d4a41c501409403e00502042e800b40c00391080c1640c16600c3d04801c01c05000c0e0840195009903c03c81d08010040d42e4401f0f0305078490740030300417070005401c12002000400035007101d00703992001d41078109400700310301e0321750a0071101d00c18a02a5150081e1103a0411490600d641c103034050b03422030503071010070a0f542d01549103002c0d6010301c1340145038401100b9003203801003003c0c0b46845d000415400440f03200c098000d20000e80500190049a03c850224180340b61030b0280302c40c443c038400f603a0100d100c01c0c2d8403481559603034070311a0903042e0010000402d5a403101014049500900c1d1201080050203105020840d01e050f07000b00108103560080c040607a402104540440e0f07803d10980b10004004102d01e04403003e588451980400002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 81121359 1250 81120109 81120113
    0x1201061701090c08060c180a030b041b05100c0201080c0408012307020109080901120e030a0203070506060d020312031905070c02040b01030c020d0c0f050109111903050a0201031e0504 80
    0x1402c10030002d071103502c1e4101026501c42a81d60f50360300a48082075001410301507080c12450a00d00c0d5555142c0c020700c031081d44c030f5890322511000c9100340c3d003e40341400c54030300c05001400e42d415003900505058030400c091070612600102800c2140780020304008181c400b103001e1003400301c1914090400c1e00300130011070404144980d00d448114141c200100080000111028010700c02c46c1d80d803a8004850a01e80300c021401102c00340803070b83c0102403e0307660340030030300030080c04001a10307008440d074004541d140300508060b403030140300511152142d2566400c2c000107807004074603264108421884070303850340c558400d1043c0f11080d0821880d941454a000c0024481d0b025489040d001d0090740c0800229080d0350044003903032040701e81d80b40568000d402d62000b4501c14030700f0b00305050180e00c03070602685155540c3c070b09641c003044040c4d40045600344054854502507a003a0210140362201030080ca2175603490b2500e81200340c4002e410b241e502d0006508122402c21000802c400d00d540030801ca19180c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 81122609 1250 81121359 81121361
    0x20a030902030d2303060d03030b040f0c030c090b07050c09041e060b0a3f0204020c06070e030303010e010302011404170706030f110301090e1203010f0305011505010503061201061701 80
    0x118010680d0441000341c0c801006500c00c101c3c0d014503006400e47c15403201c541c900307902408014040a800070b0340c07030b031002a0800e2688a80184122166800f09180140c4400104944045d4000803200c0200700b00600028070001200c0065035010307240c68a0983d21400c0010301c42140e2010b45d9880048107136250304200081e404809800000c0342c19444440d195041d991141d40f903409074005014007070120764040c3c0380c025201c00c9000101411005458101c2c3e0224003a40c10640240c205684034800340b0003a990000030300410382c00103400071030031580f4015542003840010f00c00603040c05024141040e412140c081210060901540f81c4404a40c01e0381c02103540703903058404d001c0040c3c60501d0b03040043c64280941450091001001c505503402c115030b03030300180b1420581042622641c09124030111640d400346008000d08400f00b0072161441c2022402d40c0d03500d8540310258076900c40c0c01c2c0416138101041c0c94010005070b400303042c10140312400754010441c0342c1107270910304500180000e0f0f031070301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 81123859 1250 81122609 81122627
    0x7032d020f030a360314010c030513020915031b04060902070302060c0f0415110f0133090c110d02060c0708070f05060112061407020607120b190e0615030604020a030902030d 76
    0x91b0700c020421a0020f04c0200c00320f80003540c80940484d2031030710100151034010110ba8100c54807401c110b110542c1480040d181040c2d003c980484d150507454021003503d41485802c2c010000f01c0c070305501d0003da0f6a0000d485034402481c2e40c007403120100f110f00c00080200141c60152a08541f00707482043d002760b02900008070365000d00c01030b2103081d100c001508818010078030214a034046503080c119542101108489200d28900213008420a000071150040c2c0035408404c0a1b076103601e0282c1307c15441d0241802c411040000940d8049014000084244c034102d41445401000c0b054941010707103003e002002d045100a00030b8451400085498132811319524035147c420030382042074254406d01c640c00528100c0d000000360304064001400e050040207403c00c0300b1981ea1001440004240001d400041004102d010020000b0828041000120181a08218102c03525181c41325407139210182840001c050a01541d00818115183c07806600140405a80203040d154611040b0400030700d8440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 81125109 1250 81123859 81123893
    0x131a041401031b11011401090504020306100803040603020a1e020105150901030c0603020703050403060c050d0e010209031b04060923010b040605030402040207032d020f030a3603 78
    0xa4140e2008040d40c003038895405409209030581c1100f90319160b042e920b20401a041682554a60441d24140c03862954240d01030440c0810020b118281f1b80107052403d04002c0241d207442c1036103901840420b40000550301103404034a405070b541c0d52440e004860f04160071071503668082c5100e41d4081d0054042d0042d03445200041900b0700200a41010031000090a10015221850081051044502c02c0e001002d005000b0b040451400e40e50340e036000100c0e0064020310002440c0400c01503088896401134400c0306100034000c0d4208802840041d40381c021102c2c0d140424012015060b04a0302c40d90070017002400030b4002000090b076442000312580442c550b00c10040081d510020410607200016103003502c40580d101b40c01e40d50759500740002940190b030b09034144640d180c2000d5074514a490015218001e010003002000d0008002a143c04021100120907410900000c00a582c2c4040d40303002c541800b40242030901d084068440e01d09100800440c5122025100130041c0141c000402d0300c0c1c50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 81126359 1250 81125109 81125129
    0x60105120111030406090809060301060e09130515090115080606040b12070902030a0b060d09020414011203120209040c0f02070801090f022709070303170c030705131a04 74
    0x30036440c900303034200c40d405589010380c81420300128001c80d0340c0e5404100c00c1e03481400302da45460030410015003160000d900c850001800400c400307009081805032030390040d200c04c800414000031551003030380300d003410400c405003464070f0360004a62060035004085c5a180f00b0030340e000280c1e1030300782c2d41c0c2d1110030884010f4003960901e242c0c1c8010381081c0c80d40e6042e20205401034100c440c1000c40d000b010b03506c0a090140c81c0d1343c694181d4800c80d566a0001c0c688000c44035000030740781a9510522003681d410351032020322400203400400111644035018041e4580c5031810000c102445403040000340107800210760032510341449010255080240401c0c01c65032502240c007502ea13184401c0e0b081e5072101400824900c11030046070010b0030804080b100c11400d05860803d8901c1784032603980b621004603046242a80208010400d00d90000c41c10342405038555a500d401e0b1806400d80c216500c0302800d00f6081102c0090700450300302c4400320502c0601038900d808850054000c1401c1850b400600487c5001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 81127609 1250 81126359 81126379
    0x6060e060705030a0807120204060e0906120606010f090e041a0f070518040e011104090608030301031109101d01090501170c01030203060414090d02010501060503190b0a050909060105 80
    0x280340100580c0c14865014000310300c0d022004100316214180500104103012100c4100d075a4114140054000341960f40d03620035012004500f00521410090a0329004488400360010800d10106400307030721140070b00f072120144409100480f034104640e4403503120720514400303100030010846080b484021034603000320030319246c90010b180001c805440e180040f4404000c174014a440030b03104007805a0000b40000307050001a06c0b1f150945002860a2161880002d000d100704800340c03281e103003c4d2100b50010340c150345c1117070b8aa01c1883c4000500600ca1f142c09070000ba5850400300f0703064003422000c61410705400c1d03c080810b8060800b03000b0825150b0400b070021440c101112424070b4802080b80040900e10440030066000f540080e1516820640b64503e072a000c1c1c4d0040c550300c1c0039807610002006010b005150081c2190010f81001007040b03000c01c00c5c4000c41c020b006611171000c1c0441000100300503110005142c4040d25445150400c64003070400901e41c00224145049400580c1e504403a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 81128859 1250 81127609 81127637
    0xe040201140a09060e28090c0e0a0315060b070f051b03030a1d04090305070203010b06040609030611070f0819050915160204111903051302220606030606 67
    0x1940c0911442c0c500025151072040000c0f91054a000341c1015003e80700000f400d40007107202031054034650000c031300b021115404000d00402407041986402c114545190400c503c82c00041101c1024072000e082032030004610300141c00e550f841040104100306803180c1d9035000d4605402800610703d0269140d009070703903089150313010140c010340f00c004008014600d0301782074040644090181d00d885401801210088400644030b1f0b1280403800c078000d0712102d440345c4191040500707441004101d540941c400744020015642c00c41c4c0c03080e003940d03401500411210200031160445005603000500030800e1601c0510038082510f0040c010000c15a01e00301c400406c1d0a002c1e01c0511a2161240d0402035030280c84030545034003000781066100082144c11500748940024043d01c2c8a40b039507203008500000c0c250b001c841850b5050501e0492030030700340300d24585540d42c45010301d4164000303070003000b00c403181140c2c4200300b00a11042c020f406000300029a02e683c80107000385141c0c050240440c1205203642c0b0b07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 81130109 1250 81128859 81128897
    0x6060c111009030f2a0e01151b050f12030a0e0c1c11060a03150608070e01050304060f060905060102010609020f09010c0804080703030203030609130c0302040c1205010e040201 77
    0x101840584801c06420b255035210700013400c0c42101583d010790070144010a00c440030046032504030f40d400008a0550410741c003181d900d507045e444040545400c02407801001c0d0030418250b140c004080140d2141801402c286d42804440c13070307403003582e40034441002c08200c81c490b002d14080c5003107507010031605450986999440728240440d0b6072102405c41c3c0455000c01001a0074000d46c400d40c401100381900101040803608001b4240c0c0101740c5030b458920b03165541212000042200b490840c03c135050502001d0148001e14401070b0400c0800030000b4144521a0400382000140200420225680d42551001864103940407401035080a10024150049000f0790300060f040400302c41c80d04001c0001910031500c0f5100440f1540d50034400061350300c17002e010f5100154040d030091030341c0380341c580104059490002c11104900f103483c0400d00118890600c128150380e41542c00040704100480c040e540d603500c86950f000c001d1700300170000c90701c01c01408030035009034401e0302e69048801c1c0c001d070480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 81131359 1250 81130109 81130129
    0xa0e0a02071403070c0504150f080102030a0c020d0504060507061404140106060509091602010905030d06091503030807140c071d0a0b1806010302070b13050c040203090c010806040209030106060c11 86
    0x43c1c212905e42d0414011031419602c905990140280b400c4042d913550082150011007551107401c980c1d6000c0100100e1985500521607090401c0c4007800d0101701204001c0e0060140b4000c5908220011860720208903007980440104424421401c006103050315049211494000a2166035403d103100011803500401c240c99540d035000740030b000c0507a203040e81410800700030b8092204664030350011201040b0107200800c441d800f0910041806410808003030155000031200030720807100701c402000800d5000d0800b81e00415140303001c5007001810418184030b80203e114500759801400000030b80104000d150745516030555104820503594145a00e0880b01c0401409030840c2c0c1015502020012040403d58013060506005080035242d0b1100190442c1c00c556a510a01520141c5405e200082000c03504441049805601d140340c00c1840d6601c0d150308085c00f506100340e50000c19103694842d01520016803000d0000c00c41503503511001414280011402d0343d4003201e40604031007509140c0001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 81132609 1250 81131359 81131363
    0xc03050a0c0e1506130306090c080c03120f0711130915020705030a1b0b0c040501081b090d1103030c160b0405100503060d0b04060e0d02010b09150a0e0a0207140307 72
    0x10300d03e0210301018014150302070328200c05440701030400440000e10714459101410b015031652100a82400c00d09840c00140c40040d5210390700500d405004282c60300102c0b00443c0f00d249046844050525040300070044103804181c0c0b02d902113030454075250b0303164031183c20b143c021280000101c0042d0595400c0b031040880c051300c6a0402c00c00c107103101340100d8180e10004da00d54841c01424107151034032440e00302e05075a90044281c0002e0100704030344c5d100300746a4201140b50524000003030826a5001a0302c540e00c2064051041803800401f440710b5118000c1086902a041e00d56032603d2920681d1a4006860312205402085401040131084036007980d090323440180c001c0e510000c010b44d003580d03250001041d8a9114007045540400140c0c50071415010f03500c0b42002160001030441130340e09180440d8800421a0700d00110031340c2c0d47d5146414160088506c0c1c038100090b40300a4081244030754180c101c400150300d07010a002038200c0c035134000c01c1064080d010303105004031700103001c070b07103c1c482c2e0100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 81133859 1250 81132609 81132631
    0x30309050114092512080c0f06040819050313060f020c030c070303030507020604050a030e0423060a0501110a080901020c210d1e03050601120606030501090f05040b0411010c0c03050a0c0e 82
    0x40035000071b10b032100a0002d42d59000880307a05203c0d001c00c0a14000381101c2c1220780f294081119061034074104031903c00e0300c016081c900d0652909920381c0510030024440540059160300d20542c0300060740e4101d510b08041901525996022640020b030350f039460b44011030010b440c05002803251480825402d01440c2c1c804040c0c20040d4071500c0866064034480300c429401555000c0c0c104940b038140a4500141182c58280145803510000f04401e50090340d02c2103051100101119115240204171041402da00505c101d84419003000101d1501032403450082d00420f80c00040e20320110340408011180c0c000b00210b8030312500c6058111a0401c115003001c0c0320401c0c40e10304041d26402500019404001850640800d000600d400d8090300c080740c1c85900440e98910042c400b10340301c0e00440b4841c0885440600c1b9038203080c0c2d9042084100140083e044800585252840b80e01c1000700010942c1c200081d160301d03070340300d007407107a00d8403d24141113900441c007100c00030703181c6403030b4180740e105c1c1c0d04070740e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 81135109 1250 81133859 81133889
    0x30703031b020a0209150f090f0403020d050a0507021912080c01180803180a02030129060702060306090c0403050303040b0711010605091911040605040303021504020a030303090501140925 82
    0x950101c1c500c211000168000007c1d0f40608803a2100c420452080e2403010f031000e914205800c1c007a06100392032048808000c0300f04142c0f044607810404850805906480340d4100750400121620f100a10303400c80c80c01c401940c85204180058040a4803166000c40c0081010300300e01840520700310081d4400030100e10052000402c5808a000b51111202010055540b500401e500107821076606000600c80c3c568940b102c04118140044040411002a14800d2410001d500041d415003c010007452092180c000000d501020034000d484c001c3d0303800402c0f03c0c1c03a410240b600c88a0303410200e5808000811000341d40000c841c1c140200b10481d07001414a5030141c40f204841c000802880c1802c401d1152524580f40044103004000c1000340f600e5074615841d5411441c0080c240000303000755031111b80303075001800050390300c582441048950505000402a5103403901c0c0c0c4c09020703c1c0c0307000d07010040c103041040070307484001c6240304210142c0d00f841e2042ca8401ca405942c15450380c0907190143c41020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 81136359 1250 81135109 81135121
    0x1206010e01050f01020c1306080c010801080721050114071b02090402060904111201060801050a0e010e0a060b07060c09090903140a0c0b07050c060a14070c0212030703031b020a0209 79
    0x807400e0031510010710607150003241d24004036846001c0e1f42c034800d04641d075491082044120500460b00a1102460002e00e83d52515070300300d549415074003d840c905075500748400d50b0042400e0b008020306511100a10000c2c00000d014112010200ca40b040810171401d40c00b40a104003241e400040c41e4001c0c40b6440031b80b529001e020068004a1045801642c0d03111000c2020010710080d01600384c0e1580408540d40c14018020884a0113034000d40c025030509c40c09000a000c02030006054451100304070415550324081400501940c1c1c0c001c0010240c0080c1c80360a0101c281c008684080c10303078484407019a5502807140c115080c06401500044c80f1040d844a404c40f0301c001003400304454681032140d1100307901c886041c1d1000f641c1100c040b03400001e000140c140c00f4401c19a010418190802946801e8500300940c61002807906040282565100c2c0455039032480000e00c01034100104e94507202e8920b00980102040e440d0740c1c21490000015680c0c4620004201140681c050f1109105403207079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 81137609 1250 81136359 81136369
    0x1b031506010504090e030304060f092607020607081206060c030a05090a03050f15090a0c06050903011118030c0306090a02010507050c04110a030b18011503020d090503091206010e0105 80
    0xa0035050400a003000001072443d2140103000e001c61000300516606e00302480c0010480f01841e026105207401d04220902103103054181209030f1880252411501c0c01950170b8001c54410703040e00a41c0035001250301000d112044c2d028043c0315040503142c0b1490b454010800200340606d008100055000300301c00319500b031190020341103a19014203070310300240e120b03921704e814500d001154915550001491080c401d5450100b0358001c40303610060034481000c1c0e02c811850040c1d80c00f54609020000500c0e25094400354081d608020080100645032080e401220240001c54102c0030310034480d08809582524020a0642c007800e05076000b490310207041d90064800b900708040641d014040c1491681e90764a40b03001d02032180300303a4144181e41c0c5440e800060121040000043d002c0e010025074009002c1d000c84a20b815650300d00342c29100c8a210700d5080f4040d108020300b44d0091401e01143d00204680040034015400003128405003a1500580321070303175501c00744030320003540500c100100018204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 81138859 1250 81137609 81137611
    0x80f13081b0a0204091a150306061c06062402030418090309030f06020a110303070807050c160f08010c0206090c0d060b03061f06090b0d020a090e01090e1b0315 70
    0x700d4007501c440c0300d0745070001012603000000581c2d0601c03903400c4c4c0404005003c64400d90110001924828880e07601000c00d07511200100702e40d0051107006c5103416028a03001804050a0b407140c001d0002136210b001c03061029515200c020141d801c0d1030b000b44000c500100070395080d42c0c2c0b210415010030f440502c10030007074030b442d41059050003686d80e00840480c0424a82528580c0240c20160340c80c0c054200c02021004c414400c01c00c69081401400030321a4040c0e442500724016141c0162548401007440d0b0401b050341e01c5d0880c160314103240c000741d009a094103580869802000820448400550990b01e940080701d41e00d160341c009002000003032800c0d15480c2c401da8003410740081d01c8541a40803031b140203002e448481485418294444145c040c2c0f1000801410350b40c030b04140841d14050750342e10300c0d00501d25074076a465008141440018800d405010042208695511803569510300001c0240490b00103250280202c480c0d410345010140307020105103002070001d140b0190007900110308100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 81140109 1250 81138859 81138907
    0x2210c3105131a060a091109090604020409060602010f0f02190809160e09011104050d0305090d020913060e070e0105040f0e060106090e0609040b01030b040c0305030a080f1308 77
    0x200301d2a240205010890900204841d0a43c40d581d0741000c108100c41410306921285030307942050b03542c110640c403074010760b80d4154040e1440921504c3c0c00c80003802a00442d0842c01c45186003c10019505a054005104161180c0d80c100301007684030034068141e10403000d00000c1d40100b0716100740050311030f814980d4028890025241d80326015800c259a941c0103034416010310900d40c0a0100481c401e03c6240000500032030150700d0685845c003c01d10801c00d204d000340c140030b00030812100a4990060044c0c00d10b6000301010760358600403101440101c10414265102450080c44049885c0002110801e841203000e000d8241d80c41c00c1704010261084105800307520751100054000200104001d40c041c00b829240d0408030790800c56002d2010394010141403048180300c1c1400041201d0854103030641c0d4100440c481d003956a130810316100802a072008245120020301c005c0c110323501c582101d004207140002c00480c0d4890890506c1076454200b0043c22080040098940c101e0310380100d11b150603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 81141359 1250 81140109 81140131
    0x61d0408070809090a06030302060708042604120503041e080703110f0a0321031509020a020703050607090906050102030325230307020c190603050402210c3105 70
    0x15241e000807814000c41514400c40003511001b061041503018012694400c0b442e25121440b40b500303880c2d0304c464011a04000c50040c2d41c010b4040028141041241d01607c001c15640205240ba46040e540d43d512900c50a8461107035950200d10500212044504075954100180350403421501c4503100002c68203015984840c030070781c01002584804515070300075405600c040c540d00c0c0750006107000c0301c0c000c11042400c05103010100042c107090302921200f0b171110700d4001612101c109105900e400785a8001910a10a036010402042d500500f41419645039003070a0020a581d1801607070b0b64002964090030041052010300344000c9030b00204c0010800d40e14001041d0b61040070789001d803560014041c0d100110000410400c01d0f0100940c0303515010564090168407403504158032091b042c0c2c0525400c043c2c8030f4021500707554402507240c0b0b181465031500c3c9200066251071540e1125a180301c01d00501d01c1c074484030368221004400c0781a10111500740048480720000341c9004040051001c1a59 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 81142609 1250 81141359 81141367
    0x30603051009110402040e040809030f030409020415030513110307091a09010e010612050a14010602011d0303010b0d23070513050306010b1801032403020103061d04080708 75
    0x800e408101004800380c80c1000041d4503540342c28520f118003181914540582e0042104000a416601c0c0741940705800c50b003142c0e100c030802c82c00a07081c12070f11491001a07100218000c568448183e00070402c644100803845c1c00580c1841007982610021544121000d10010110002c180e02ca6041104860028191590503868003000c0c0f049411802c042000c20300042d10440040c24003081160242c548811805495854100d00030071003414480321003512074444000c00c15900480d001208020005840c104441d80c480000030300030314806148000000f410030b02c010041d000072003140c1c103035441d8007502ea20f40400311680790054000001c1030701d40a1616903103030a006d8000b18455004601a41da03050b50b504a00108603548849500f0007403003500103000411841440701c08503540d1508130300c0000703425500c074401640244010014250081820034403040192400e0f04c1071303001c1d00d100340c9041005513168440d0b2151441c500c01c0c0c045001c00d50790b0100f80442e442101400e1024820780f41d880ca4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 81143859 1250 81142609 81142613
    0x20f010213090501050a050906060c03070204050c034c05060d02071401060e04110118091d03160303050408250209130b040b1306060b040602060603150c0a030603 71
    0x8a900c520440607021070084401d210180850050a00510048444072141400c0100080050b2805803210f271260340c0018078012141c0090040e50071864000300704010502e4103080040f039a92080328074102103000c003014680041c00e12644521038003803000c01c2d1a880417103007001812151300a402107000c20540400050242c1c0c0340c1d4000c1c42214411580940c9810031450482074142018402e15580c0e414608207200343c0e008003841c07650264200d19010560007407040146d81d1041074a0b000c3d45512420400481c05156540203044883d000103e0103c1964900c0d180c0303612401290388098001002c00841c8010a200350820b6401030f0007003500d180340c903004622900140c0610200c0b0781103d44d5803410103040d0f04e400b0034103d038041600d0810400781e010540d1080b0a810340240010406104e04001c47e40200f50120340c0f82e213040d80b0440400c800b5171100c6401d083c2e50041d01c60390005204580004803603007000302e1020b81f01854040e400d900360300c03118885911070b00060a04d4082680c1c403480080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 81145109 1250 81143859 81143861
    0x4060c020a0b041403041707050f150d1a06030a0c021608030d0f140712060509012405090303070303060314070e01031412070308090d030e03040b0f070b0f010807060804080d05040201020f01 83
    0x219544187c0300400110b4909000d1103600f4000c0903825200306445081c034019128140c040380e400100e6200000f900e510340356103911100100707650560304400042308010011480d41e002d005640d1141c0c0071607501d0440042c800100c041e95005280e141d400600c101221b10040e5040440c1d5103200640c003098000c007801e461190f074041191044000b0711142446107035401c00d4800c44028120a50f00303048650704112a50345881540b100e00c4850818604039440454401c03420745600301401820389648103842d040080180038035000a41c3d20052002075074040050009041c4100e96103581e00c40303682c1e0b1030342c1c6a800341180e82d04640d417014011500444500c40c050401829110321984402402d07080c8207035958541030710010b10505040c60041c90f50700f44c9400000360b900320f44095002d01c0c2c1d254004015500140111000201600f04000902008030b0741d0006480c1690900700c11207003c03a5403403104440940054030051708981e81000044503419043d04003681c018010300440d80c1d6030440c41c0700d081c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 81146359 1250 81145109 81145139
    0xf0608010903020312101202010e0d0501020d06030c092d1503030f110109020f0607030201091502210c070f02010c0507060806040b01140306010302070c0b0705030304060c020a0b04140304 82
    0x80041c4c000140511440980058030390304401c006855603a02c0303084c0f10309a0b841700900080a030520045002c01c070595030f075021540a44a62082c029919048126420b6015000d40d0008451031040b03600e0214060f00e1510405900101d9491104405541045215403800c60070325019520340d01c82c0a001d04100c1d02c19034000c011072099585c1000b81000c5800105003004d03050801013140d04291007180565111100c500d0244c808503411581c2e1400380c0784c10b0380185460580100700d0f1011404000400d04654040c003110f54045803c03003005400411442410f030001c8960050281c014402c040101e088400ca9401451040c10504400c82c05505c0300c5141034081e611400000c1d40202c20021141494000e00c142200e0a007002109600205182022400028070080c10558041001020700c09058030b214002d000b80e08601d940c40c1002c0c00c009860750b00c1120203407007003410f1100c51309106200003041c01e01e00d60881110394083d101c5a54400346840c1c004c008407101e12041c400460780b42801e070240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 81147609 1250 81146359 81146363
    0xe060d020a05030708160c031805030601030503040302120607080a0c14070f02010e060702060301090203060103180b0109051008030a080916080a0b0c0a02120904020412050d0801090204050a05040f06080109 90
    0x503280d103000a8005c04aa500030030600e808401c03a845200c005811510141031030b945424940d0a0701405e250718000000164030984c0c0c03601c2132000000a00002000402c242c03030094640d40041001d107601240d44a50603600040050310784400900300d9065540b04000041c0b00c0c0c5425080714000c0000020242c100340300540e40c04441203802000c66030452401c1075501016105542011300d280c0003c0c60074041440384a020756000030000c1c0c5181c1c400d0380480b4043c0c03850a0b0301c4a540c105800c0200801c0408d000f954400d5240c81c0c0812008640740d868001100c2d003540041d440e10380707900300c1214800000f504d645082d11034200e1901c0c10b203019110701406008000001c28031010b050810b82a5124007400e505202c410800c039000d41190301141c18032600d11403210b001e0f901c0f083c09011900070700c101c0d40130354844030000a0000400c07902080750007003040b855655070810398a4840c2c84049101d05e100d81503110f00c10700000c00c06420290000c0304140d00f80d0f400091401d903140c0358a401d40f01c00d0002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 81148859 1250 81147609 81147617
    0x605150f0f040e1509060117101205030a030b030c060405010c03090b190e0f100c050a061506021b100e04020408030a05041706061e03031306030b040605030115060e060d020a 76
    0x130445410380711200c8000c0300c1e408079419003803410100e0019020301d1600400589614100002804504080680c04020509031304460041c807e5424015280d80042114200082c2800d0881030319160000300c0c0d0300103900080c1558130341490240199403520b6004030850034018001d90000f00821400040d100003442c100c500000b5041d940401041607098690007407190864424542d00c680304c4481000302c00032241401d4040f01003d00704a4940041306d00000c0216081c0922461003034040052070085a0541d0200c5258800100c0340500044503040040c0c0c10403200565405024400c0e2807141070302c00003030070040c68a600d0b250140d00b1030f800107080c1404150005400c00001e4811303120004887c420303002402181c1855400101fa0440b00c0340c0c0034003035211107003440c9020fa83c14801c42e03c5034003c100b113441d4980e0ba1920701038050060b06221a108601d010700009590406001d20821175502c43d0707500e02a103061030700a9411130700e50103040e500038006010080d07007041944000c200c201a1911 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 81150109 1250 81148859 81148861
    0x71a09030405012a11030a05010c0c0209060108090a03120605130603110a0305120a0e03010e0705130c0e09130b0103081815030609061f05030105040606030605150f0f040e 75
    0xd050004820a6000010061001c02148088404c1d41205072640003004070412101c1e10f0000e071501d480c00f50054103d510f02607480070714036000b8401421403031083c0e030382241d550f44100065a0003c41103540101540080d0200d03400030344106042e03282c02d250f440e400121f2a48610104002911800a140c40c00c0d80d40c00040c0b084c071140801440055004460740b0103900d0650307940365220000095200003401e00400c0805009020b24652a902c445c080c0080140140c84400c4641d100364178860b00340100d1a41c03010208602a40c080c10807040c105446d42e1740007501801c1170014035100200b00300ea42000300801c80740000c030411030113030081d80034130f18039621012502c2102450f40e400c0c507a071600c503420490100322084194419203501c00d02c21503000314a40da41d4008541288460702c60340905038040c9003800c0d005c80d042070145040c0c60098501300555a180c0d2025001c8072075074080d1b00d6202c5070081a9803080b000900081c0034503c08150a0707030410307807200c881000540040d0494007411100c20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 81151359 1250 81150109 81150119
    0x237150506060a0507120e09150405010501020102031005090421050a02070b0702010f03180506090706080603070e0105060f07151d060f010902070503070c06050927070302071a090304 80
    0x100400390041c8040721028903041c50070301c0150141c404d01000401c0032950a4100701c48500407408580001806000400c1e1480d00807640c14001800b201e5140c840c0e46030400100d01544144207a0b0700c201130f0410102c01c410b040c8401c129001d81c008008550080000e0221180510114440c4201d06801e480f2141c803001c140401a003407080e641c000d0b0010341003d11244003d81c0e4050312030080c940d03140c10005503c900c2d4411b031f440c8082d80060043d045103c0d03d42400403909000800710201c800036a140d96032522441c08064551510b486030a1510096034018002c1e89095002004c180381c10303171107403454091141d0392a42804035082021a84503681e00c41c2c0c2c545185041e0070f44448050801c090000d5280c8070255500fa44018069000e802d5408100d00c0108001003080340d10403a00b110203020b409982d40380040c00e540c4040580b070f00680195010444240034082c40b208540f015500a0840380e849003400c400035080008151406404011040d4103a21014900c60041c1c0c039000c09940e40c0d60030702e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 81152609 1250 81151359 81151361
    0x703080108120702060a03050a090203010603080a1715090915160807051e0c0f03030907030c05090403020307020d0305191205070203040509011502010e0318040605010906023715 78
    0x80b5000e00030341c110802242c80141d0f100c0007101c00b040ba040c00d0000d2552141950f4600400610b0320081d0558a0070001006016004025080500645d9281aa440c0680403100c03a071350780a494107656800c41d004000c0747d500c0c2203c00700d9480040789045031a00c56980842c0c0040c0343c002c4c2e9030401d505407041d401c122820b6000f03030600e510001900742a458005118000c0280d18565414103c035803402141181c6000802d00002465040c1c040c1113075201c0c02c2c54070140d501d4030746600c02240c000f07820715000990b506003082000d10450f0150051401d0100c5038080c0000c03800c007500d0440801030200610ba40d0201c0206000829500c166101e1080c002c001d030500040306d101610f004203540c81840100001d5890b851038505660001000b4000c4400c045400c0e0f0244c40001c000b40880e00010840310700821100a81d40f2149804441c14405250b40380015a98080f580c0a90070058010100101440107061301c94029200340c03180c04104c4c03d4030003500b210724807007814045034042d40071680d9800d03a0541d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 81153859 1250 81152609 81152623
    0x17091807080c030403020d030e03040b070804051c1502160c0e15010306120807150c02030705070f3210020f011a0307031211030a0c03030507030b01051602150703080108 74
    0x108040443c507605180d140655a05804483d0004240e11a4400c0c05c95030743c1401620010a40e42d42410748601941c50203100d10380180c01260f00612644c05102100e10b0148080c401c03241d0400c0550100b410b407aa4501c001c0d41c80041d0385040c4c2d6070701c1c003601000100f0040303140c0b004281031005040785007090098900070404281c1c4d1141058100305040c40340c4024158115441640016029070b107201703d26240c03600c800071600040000346000c40345c0c0300c0550044010310724584504140d8602030784602d0001c03100c00c2c1ea8020b44844003011450310850001c0007100c504010000d80514618410400002d2110307401070b0300c92001030f045030000035500341c000d004460141d4200040e44003203800d240c020940c0c5002038400034241140141c0aa0b070414060b001c020004001c000a0307980d00c0c0003100000d484c0450302e400840c00246010006101d85200748140d6840220580d18145400045802d0b025407402204040c2c0c4d00105030b0130007418030150300e002010040d1003134031030b02e1466241030150360030301c88 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 81155109 1250 81153859 81153871
    0xf03010b0a03060f061d1f05070f0803010306090201090b1305060307170c0d0e0102180118080d0e2817010e060a050402030f070605030423030d0603060510060207031709180708 77
    0x40019020003c400d250030111f44000d07a51134195229042410106601d01c0802401340c100140000080f05000d440d0b001080b045000780c940c1d40c00150703942e0341e041c1140704401920904030030000b414042407510400441c1c20100c00c0c0b904c4004454040702002c0c07161070036100c9061844001807881c0391000c25010300384001d81003000841c105035420f8400d2410403078200600b4108110f5020401212084841c40c078080c206a504071030321501c03040005806403952041013441508043c000d070ba011420b09604120b5031058224810445140c190001c4485940d01d800800554030340c4139100070b0400800031184510740ba600e01103028103040c01454145041c03820351a02c82d402868003070001a800000f01d0b9040780c1d00100c0000000e0a011020311341d4401c10b020300215020000c0c00ba030101d0382d5600040113032400b0744005c0105445000084890071f0080c8152400350300302c02c80c00c001241300510408000300901c925a4a40b00080b0300060407a45020a001403d84004003401641507014444503031051b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 81156359 1250 81155109 81155119
    0x90708030a080610090b0c071802030402100f02030d020a0804120203091e0f0a09020307120e120c0111030c0c070605030105011d030a0602030c0c120f03010b0a03060f061d 75
    0x260710501c000c181e2480241414043c401d01c412024080f417152007101c00402d440381259842d1000c06102941f160054444c06400040160300d0081c60801c9208681c012640205141003000055809039401d100540850080d40400e002101c0803060a0000300340d1040c080e55000003601d080e01e401e01080304100550021540709108012031900e9400080c0b40e0118170411990480c249140054246d1200c0f1a0180c1c1044d040309001030000d090380c000c0e6005541944a07503602900300b0346c0300c2d001c40d640f900759201c040e1700500716050b542e018480140200c0304164004a180044010b10004d10b91064642c50b1005e900010421407010040c048900a41040d1500f94510f516080000302064802e50000c14500b0300d150104a0a541c100522200680c6c030240554803854414488441e0b038110341d070f4040c8180a241d11112114500500305d800b61201c00b407819007146d0030a10151074540100114a040c5a07413540040b8648030240b207401c0c001c00b1259180741c0c02e503818404034015582c1c1c180c41030f8024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 81157609 1250 81156359 81156367
    0x70815090601170703120302030a050604090302060604020702030a0b0106081006050f090f0301020d0906061401020109151d060a050a18020f01122012130302030403110f040e0609070803 81
    0x11404100320341181c04040c3c1030500700b1003441e002400c0c03c0107039000030480c00031000300210490300360f0003030340c80344000000c100801d036150810700095600070301000700107810000c00500e02d0301d801e07405000a0307400901122503805140e5911401c0340f00c2030300001d0115080d0010003800040040c4004064251441d00508007090080f501d4042d004910f4000c1c41741c00e119041c90040d880c00d50542d0220705c0c42e032000303000da40d0180c00d0000080003180651600c3e0b154240004030103500500030408420380c89005100e884003100c0508006007169800082e2240c041d107018903101c0c800300952070051103846000503a50500c110190f08a4092040c84901d2500384030351900541da4000c0d4040005000f82040104210310b4142d140040c2400d0102120780303045810402001c0ca42c01c00a171100300144140c00e80e07140caa1f00038a860349210000300800503401000b0600c0003031030703003c40d403010312070b014004120201080c1c0000c0d0585030307d660003c0c030940c0500c0400c560407208001040090864102441c03070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 81158859 1250 81157609 81157621
    0xf06090507090311271005100e03030d0510050a03060b03100c08070807050d1814160b09040b040e010f150f0303030e0309040603050307060b1504030609140d02070815 73
    0x10300c5001149140710300d8080302c00b40207030001507075a01c0011410718622285c40ca0464003282500045010b034030300806110380740e070302500d02030786001680f1203000700110309000c400c8050f8409810000c144500e481140d4000007032645400c0380c00c0300514400e00c800301d0103524140c00e05180800c0000300d103042608095504610030340001169400900d540f80002d01c0c0d43d10807070301740e07110701c66604886d400c540b810546802c148015400d0308241c030b2050a50504c1059070001041d40c94800d5101c0c02500300650100f004010b40c00c60003415111405070011814401200001c0c0880b10081440c0081d6510303070726011002c2480e07104a00e4521030528901546e5820030b000c401c6107100500008091681c1c883e114103010303100b001500d8810300c0092042c003900f6224903142c0e80361303040510110390070f50418026940c0c0b8a40500490076100310f080e040c078105460340e128007010f0807a01c0c40507150814001c00c01002c0c2c0c4820302108480e21440d80041c0405441c00041600d0010001c9280c0c02c002255000d00c80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 81160109 1250 81158859 81158873
    0x9071a0a140c01090b0106020c040e010203060a1e1e0503011d0c0d2105130602010204061704080702090411180408041203050c01020c06190b01170c040305010f060905070903 76
    0x46101c0580201503100c10380d0004031401451500405441080124000241c80b640080c42c09100ca20a0705c0c140300a0502003030190907404156045680031172008004d02600c000754204031103030b100c60a12800f00c1550303401401c0d01c0c1c410f03010390780b5080880343c0c10621040c00c090040c40d825455a1034150540d64010254540b100f0032544014410020b100c4080103104440c242644264105890000420600300000d07207694007811100980401819000510600608c2a0303411507641e500e540c040101102012010044020811108240103102850260b1102c0c450b8502c50307403080102c800740b981400200040b00c070a48821041c0d5075040c000f000005004e2006680c207c400441040742c90b07841919050350a40500400c01800e50710114a0115980300082d1040c01041001031141148074140c0c009025201c80080c8140030400d2000b644051240038040154003286010201d800e00740c0f0b1340c0e0741500703540c3c0310294030002c540c5400062041203010b00c100703900400142001c181c800d03e03640d1105 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 81161359 1250 81160109 81160127
    0xf12030911032103090703020a090504030305060108010602070312110604060915020f3a0605040b01050c15060301020d090501050108250308030601050f030a09110a0f090203090109080309071a0a 85
    0xf062102002c400305004007070030001003014550090014a8441e10380f040c0100501048409170002410b0801190155009400e2503060b01d01d1940501101420354884884a120441d140700801036580b0308484000003d1007814012485040c020a1201042c241107802088480082030103c2c41000f054a81c2149001240c41d0481302c2500203206613055080714003860b0041c0781032481000080c070505000c0070240c3c45041616800c59080011418050044590340580c41054419520a00150703005d01c02410f03006503c5100240007606d0f02562500d0700040e10f0301402d0440e026074443d00180080706050165801e8000000f0f0b03221007903440d840b0020800400d0b032002038806440080440e0050748074070304507185241d40e2801030740c0e24206030b0281401400c048505441c0d50714007096025161030000c59100c01c94454070841c4020368240314004000390f0003d00300203800d643e10f00d050300000703400501442c4550103082c0079201c05807a04515502600c1084000c641d080420040300c03203040c1c0c10150746 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 81162609 1250 81161359 81161413
    0x30406050d0f060806041b0f050d032d0201020417010509070b030408070b191d0309010f0c02130209011808030f0304060b0a0e0106021506030606010c0f1203091103 72
    0x200b440001c0c12031042c01001c8076041000c0e2030290030200010301224070030003810740c00a22211024150307191a08a401000e60088035404100c0d440c403c00460f01c40c1c3c3d003200815402416603505407140c814101c81d032201d5000d1000c05030750040390421116144580902c42c40064078002e02161505400c21500d42c041401295901c80c0082301003418002da000903038048503400400b00d009400c003040300c4118540380c0d00b1a04002810302c480141140c6483c0c02130b244001c9540010b50800088000558420200940110401039219507070809a503070f841139498402011103005036902e1a0200043c0f01d1091054003c600d0142690100321680002086030300503049509182c0c1c803511146800300140c090a002603501a64076035010403031030741007115941224019001c032071040074070440e101d20b000011500386906800c9100018080d5000d902c82451051184412060044d0700740c1c0c4200042002c4100d00002a640384000c0003000304445403011550421070081c04011001044c400140f8811035034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 81163859 1250 81162609 81162611
    0x1b0103090218041401020409021216201207061406030f0a060218040218010207050a0f05040905030c060709030b07080c0a0c02060904060e04020a09050402030304060c0201120e0d11030406050d 84
    0x14140500140c6540c1100701d13040007507650345e60701d02402c0c0180d00400e01c0c03030301207011200c00301ea24410f4104011901c440c15894060411640c0c3c228469800240074030300f200c43c019004e20307002248400000704581c40c0300b45400603501344240c0b4807030b0004100502307140c02544078030400d0003100c1000803689000b507880345c0f0141c0d8515a40c02c1803c81d55400c0031850350058004100d0b40c4080d008822894102c00007070782164000c036076490410200310854031907140041400042404076040c5604812496402402202e00d01110544110f203003a1084508100048600400b072040003862020aa004103d5103031425040c1080c089684180c4101e07612a800c1c00703c01c20014046448410030b031031003208014070070482c6035903481d002d13441903004442c01c0340b0403116801c000c640f00c0b00b2449800e000d01d0300a4000d50030036041113025100038240142c20f906100701682e1038041c4c01c80a008040c1001000e4029100c070820003a8003601000d614461000b10303070001d01080c02441c1c0d221050750034035900144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 81165109 1250 81163859 81163861
    0x906040b07020c0a030308040b06040b0d02060d020403140703050d050a080105090601090504110a0206101a030c0708040312031a0916110d020601180501050d030e030f0a03021b0103090218 82
    0x300030b0b480c18203000b0003035401400031500002459003200340f00c1c2c4607501840c2581e0140daa00b508010480c0c01d85810990700c000ba058409015007004000b91540207000a0300524080c0c5a03100e00010548174281c959044d8090401070040010511126085415906042c0c0c1812000200949044014000c150180c101140005d103140e02c5500c44400a040160040001102c04da040d26015400200024050f120308008202d030281d003003c042c2c0072602c80404005010486007019019a0b0029000d107040e20814003c44000c5000e901c020401144600707059030b1010034400015082d1041c1ca408140121220000b84050751691644158807001c0602c00c86034140c0c2504054030500c6010000e00c0c15403003000d06220f200c0b43c0009509040e2050715440750070449507081c0c16030585209004503900f02405000007000603000e00398011544000500b91920440e410852a01c0d114040f2010340059026080ca030118440d08500b02c0111003083c60705124410146c3c0106400d0034912500c0c41045001e20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 81166359 1250 81165109 81165121
    0x3150c03021909150c05070306050c040b0c07060f03142701020d0902010e10020706030f020f0a0206011a07050c060306040b09010f030303050708070e0d08041203030f050f0906040b 79
    0x10341211440d030a05803841c2c601d0300919100602ca00c001d402a4a68106101120f2034543e00442c160030714603502200a281c15400c3d80e559001600c005044407017072001c1400085440082c0d4000340520321203010003404510710f000d00040040769421080b205140c546414150b00801e040405ca51200d51800082e07981d00681c10f00300320303100c0200071401c515440829140b00055503a003040c0e040038003d80c0c460b01850100d104002c8a040512407400c09070b4020f41040000034041d41050001e5419031000508203802003001c40000da102091800050304003a0041c005c145030642107040f5420684005401d1503025683d4070b40d42c14441c0446441201d0200000d039071541c442d0006c40040c00007401502081d6940c0c500c0d42c60302c0c080381c08100c0100741001c00088015110350a00d5210380883d60f14050951141014400b040384903010903601c040d01040080b0700c640d00e8001c40c075008c61003980e000a03140d43c01c015540c115034001c2c0401c0056900c1c01300b484908030000130035a4010fa0002104402c9403981 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 81167609 1250 81166359 81166361
    0x60902030c04240b09011e0509100203030a0609020a02030a1805030111180103090201090b1c050c07020103060803090609061303020301063003020d18051203090a060201050103150c03 80
    0x1444440360b102d8100b800441e8000d03911079503072080c1c00b40350401d8481d0036141d04003241540500d002071400603100d10110080985240305c4420250400e040041c6841100030201754071100c00000040540d00010500c01c000c25a486400002d221000381141440b1542c0c0009403030340702d60b221035400c100381022200101c070a80c0000c00000c050090003003082080203480c01045410403900328030b81c03807080380b89100254001d000c1c405590b94141d4511810034100091407440746c10489642c0d00c14251840c40b40c000d520640300c0c0f06d0241036401c0d905500d03144188001426140c07550016145500240440c0301c072501d40301c0960b02c800b07200310364890702c60188140d8490800219400a5499030820000182d80103045201c0c595408007040d8a244075646c801661008130028000200180e124905241505101d8103450807010340004140c0c0d4440d684000092048090181c42500b0345c1002816080e20314054075220002c0100e40000d100e02c0d85103031070703402d050240c50020b4403031140c40e1041d1142c0345101f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 81168859 1250 81167609 81167623
    0x140f101509080706270302030607110a060f150f1a0f0705010906090312050f040b0618040506060415080a26030f060f0307030f140a080706022206020a06090203 70
    0x4400c21200010b44e22032000304580002107429031456151140d124030040010b070400281d0307801a000706483c2d00c0b10402142d4910300e080c1c1e207103614041c00d401e030b0000880d036002e0ba51403051200310210f1f0426007488605003421459010a42c0f241e0070072410441c880e00315461a00e8900c40c07400c4280c0b5101070152002c0284101000100305502e0080d8032000c1002d240d00c20310032039010f82c1d41c1c1c1e41d1201d80d01b1f0000c012200103559031001c4090180c0040d002409100559a0000c2e016145004e480e1044884080c1d240d0b043c0e50440c3c032500403504000442c20305204003004403070007440c048581c0d446c0003d05a00c68400d1131003d007000140b4810f25601524510700411146024040d031681c9290690b0080b40c48a0241c0b242d510801c21300c2c00100c40d9240010341c00080e00d80040940c4504002541d88104103026039413411030900948100f240418000005450030034040e28015907500d2010304400d94841c666545042d00440f182004d21003650b00003669540c2030791007100041c1c59090307400000c0c03034540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 81170109 1250 81168859 81168869
    0x10091a0405072409050109050904061a04060b0d0506030c180705190302030402030c0102060c0906180604060c060509011e020703140c15090604260904050703140f101509 74
    0x140480030a0000c0603218000c2200703d441e41d42d5074419840d0b100440301c9142038420168040143c002103400b0610344d9211074000d144042c1002001810040860180c0342c0507807000c0c0004602046c1c864101205008071988200c046018083c2109040300240002c4021000981d071303a04480d000524070b9000d00304a0780300e505000100600c0200c00704004000e54000c9500f02e020f4098400741c0382c03482d400021041d0090b00010101d034201a42d207028006107070000040d10a15040d51000080a6111f22000388080d200e030f0b075a207410180070b50601909803030300034040c03840d103a142c01d404010350a00e07000168243e05071400702590b1030813241821640b801d10940c1c2c503607484200091700c0c48030b04030004640e00d11007071002020703845a8400341840d0f03d6050450b406015804d4501651401650041c0d50f40406604400018101907020000c1011a5001c45484001c642d0b5803c1c40e074203d5030703414610c5600001ca0180e2132820b1600310b140e0001699107118604000c600313035103000b035428020124600941 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 81171359 1250 81170109 81170129
    0x50f1008072703031e08010603020906040f080303011d060108160e03060c030601030c02070b0403030e01020a0503030103201e040f0b030a080a140703050f0a05090909060910091a040507 81
    0x1000004003401041d806100c100c02080c00e01035408211705c0b10f0600c60656044986560388030b6881c0034004da02a61200484c0355000350108004038034003800040c80c80c003600141000f56100e42c100405000c1158071854900c0340002044100525603030301c80300c81540100d0050460b01080006402a250008000300c2550f02d8001c036400c101c050f03001c84000d0340c03040400340d0b01400b20724592141a0703201c2c5050301481601c84410041803020034050445108582418170440c0d02c0c81005031182404d5820a800c00c0f280110000140c7e0807001c00e0030141e040c1140c08444130340b420700450005c100400c00d17180131507020700d490b060003034207000b140d83c0110700d010400740550720080c1c00c07450701140c42d900c0321411202141c0da403c00c0d2030410010030152914550b041d201c00346000f07075081c4000841d400454400040040c1080210219121404c400d40113020b000010042030511401981c00c2c0f50f40e0700e01e42d489082c5449050808554801c19500e046903245a01d54000d48550900c80d08003e404d81062a4003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 81172609 1250 81171359 81171407
    0x100905091b190e190c09030f12091502010501061404080a061e090b060a0e040c0e091006060c0204061e0302040b030c03010c08011401020304270b041a0406050f100807 73
    0x12450b041c4e200060b002c0711020480070005034025a009402404050120001414070a0028242c440707203461000c1c507402e120038090790b030300b003841181c131804001080180d440700e0040060f15008011010952201413000741801c0c24a00115500e02500718098210b030b490b4040e00d0080381c10800031051083e4036500c148401102800d240900f0b200c00e80345503000d128881000140082090300480c05654003000c5090101d10348902038501e107801800081840c0981c4003448900301d014851400241161b8407205503480140c010031040310000d6008204055182e0940080c05100080800c10f50f60b04460000d62030b0118000300e031404101400072501036183c0741c2c014109540000d9100e049442c22115120f41c8031280d001240c4070700841c81103044440c100f00082d00c1e1401c9100482401424680c0005820302ca0000040d0a0301d2680081c8044600c44c8042d100007403d2074083c03c0d01a2800b90f030a481c080004074081943c0b0b050803519407040141141c00f0810051044454003171180b8014450000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 81173859 1250 81172609 81172621
    0xf1103010824010806061207050a0e0403033c020405060313120f020309100c0210120b09090c09100b040807050906270601050f03100905091b190e 64
    0x20301c0300209a411206203102c034032855924840c1c2c2c0d1240c1030315401009006240c40300e0703061140d512949610300c015401b075068041856213803803101d600188801800040c0c54200741c00d010f001ca0303200850307000d511080803400036850b604101c2486001c49180040e0a098000b041c0c2d07010007130082e40c10980c1c5c804400010710030101c1240c601d058a2501501002c0c650182c10300055075031842c416120390260304140101c0da110310300412500510701e598208000840c04903400075040580344960301c00400d0390740303da078540711030306109003181010161100c2015007010070710650b0f629040e20429100d0740141d00020220180c0d90085402409940440c0307890341d448034000341e2950a603000310713401040d11400040e132754542107a6481b0801c504a00d445044840d040d94084d40210040c5054103025007082030340e420341ca5840045203c0c40308060704821880c2030171484400d445002d00b42d48401c0d03004406000d00c0c122401d61040741ea030700446d49234510b50341802c0804190503007640894200c80b07501c001c11103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 81175109 1250 81173859 81173863
    0x904061d091c0e04020f07060203040308090715020a080c010b06040801060806060d0812040302010605181807030215092e081b16060f0213031202011a01030f11030108 73
    0x80910291002c0d039816500c1c0d0a031031503041c503064801d070300041c655014400c400d0800b580245601034110313260515200e0b40e52a003200780ea1056030201c00103954841045022002404101e02600c0074000000058500030002551070301c003010040c2c0107440c006851141054250700404903d04064403454443e940c9220380c074000d144510a0180328082d1400189031440c00c85034580071503621112444c14500021512524114014021425990703600c0011070720381d5400401211a0f601001640710a283c030b202c0740240c1d402500c20502c00da41c08607001384016554003840106007990500815116140c1da8001031408100c2045841820703045a80104040080c19074000c0d8001c0d1174541e04130580700d81c00d900071280c100200710040000d05100307540c7c000200501200c0c00300c1c051503002c52075007441040c0d402240c2c0003420003c0c2000080b602002000f011410b2035000c10a140020800d400144401c2e20040908110460405640f1710b000c2c10114465440076059031101c12166453351b8440420359 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 81176359 1250 81175109 81175111
    0x4050d030f0906051204031d030115080106140f0603040303060e01060816090315022208030c0f1f0b0316090b03010609020418090201110d020a020f03060f06060904061d 74
    0x12001400c642030204010b80150f00b210140c14010b01c070040207035120348023144c00008101d120b0703220750f000140b07400c10384d0380c240501034000700788844c6140501d00e4241c5041c2100c80c5070380301403190483c4065001050382e80d400c0c404130308031058941d16038a9aa134902180100000c1d001044d10f20002c000209000d40e2006140e0301c588500304d81d9188040c01c032942a144403c052200500e001410070410001c800b980e0080c11401e440484241d4095000c84d00102404040741c000c04c200c0d134004200204d103010100942c40c0e80c1e44000025003030a482c21900401025010004100c0c69038840c0700c061505d4400300062000c0c0140300c0c1c9001400b0352911079000240c400c004006110b0f608029000c901000e081c4204c500b100c8207001321200c52812038900c5009030031182c07016418804070080303a80c0c1c4a02c003484601da04036a25409848007480c0da03c10480068411401580640c4c844010001041d0b0304800050308408105d071500d444c0c0b103001c0c000030081e00064019035903033302c2d080034000122080800070f070b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 81177609 1250 81176359 81176387
    0x1f0303020c010e0d020a230301111305010801060c0809060405130f0605180414070510020a05060a020c0309040b0616061e110315040f0923030408030d0b0604050d03 72
    0x203030b2850300540c0208130220f80c2c44a0003950084114204100c01c90041000b0051001c902440302d203a0704020780028211506191141c0200c0c100080540124084021002c06002c0c00d0810158650620324014070001b41c45000401e1032400154803c03055070390b00151401030000804a045081a04a00d0700280101155841495003010b030089100c3c40d01980314504441980240c900c13a50b41e80d00d40340e201e90440d20100c0075038010030f540811151120286100c5280b5160028008000d45117041c9240034070080404845510500280382420404011200c4000003202d000c514440c0741000aa80b80c80380192808000441003810b604200381174200180100e0900c150f1281495143c5600041c0d5003c100b03d081e84603010800036140014a184002040f500508001981c081104489040b954081c20540e03110910f04400d841148039509240403091203403000d9803c0c0f0785002141c6070b490082d00034490300c00f522214039104e184c940d030f41910024a001007113562110f90030305001d00507024100003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 81178859 1250 81177609 81177617
    0x10090f0605190e0705030a02010804020d08041d0702070302060d0203060102072102091b04120807050303011409070c0305160f020301060920090306011401021606261b031f0303020c01 80
    0x1e0b034084002113842d400b1140060050144611140d0044488000052040764040044550303103011076074010280c4047c0c44540f40790015910164855258440c0080488086501c085028001600c2c3e40d0b0654007510107165026880780c81d821300623424510240c020039840000303014480201040c810742c00e5030680c000d0f95100010389400c00e0105d100703180241140002e840800c010022a15540350050995000c1c0c80ca480c14081d00f9640da40c1194001c0e4026200e01400d0f40c00070415103480c0800c95045646410901c4241c0410754010780b080c0980300080c50b0507460010200188402550030303100c025030060082044035221135910000700102c114001c546103d801c0004580d0344240c0c22105c441c8002001441c80742c0c60200894014007040b00c19134110301407410ac0b404044010599135018008a8032000941800c11304c0d100c10030004152001c007024510307800c1c041102001c810030b10343c1d50000c007440341d520390340c4041c0b000911607013502484011440d01d5001061540c0414401e111a07800d9032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 81180109 1250 81178859 81178871
    0xa141006030606030204050d080a050408030304050703030e0904050601090209010207180c081f0302040506010e0603180d02160b03090307050a080301090b060405011e031b181710090f060519 83
    0x8401700d0186025080e0480c076008000c0c000700d2001d2026150126107442d01928040c1c840110a0858100b581c086965a112000c103000705600000000090682540c2c5810030f031070262545903403408107103e41d8105075400541d4510ad13034401e00c00d05003d428035048410034040d05451103002002c114552400140720400819100c1c2421040d00f140100d0342500c001076242107408001c0106000391280d41402141c085840710740c2c9450303010f5841460544844a404401c82ca0711504001c22740401c08115000743c1c51401501410708d048000760b6a049420544950702c48110910318440d5031406440752261504017000c101c0890011410307150103000c03d00120301d000007801420b00031409400d0220755403901520100304143c0c0c00c400340010601c0c0101d0403040b100301d240f48000e8003014100c0002d00e881c00c800403600c00d1012040040c10030240307890b1400002d849075601c41c0901c1e0311400c8159102d020075024840c3c2c1c04d0811400b10741041c2d08000c64240114410022501d22070725442c0c803400d2071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 81181359 1250 81180109 81180119
    0xe061b06010806011208090f0a03060207110402030c12100e092b0c0303020d0906050a1a030c1c03020a050102030a0f0b0306010506031503030408030c060702070812070b0a1410060306 80
    0x109143c1d0486811071800300d080200b5586050181e041085883e8011b01911050441596244100c0b40258001e0310010f0752031985061540c04101529841800b460041051020f000d410204680d1001c01108bc803400d42c0c0c0720b01c80401c02e445056800400b00d001142e0512001e15008564041c1d0070b41203103171114030391000d10511100d040040c460742d0702003140c56225101203406a001041c041d0718411002404414640c0c031881103ca041c1c643d0700105136580811041d000680e00900460380327040340200301180c203510000c0c3c900d05005280c5440d9000d1413819400b014001c00420500a5210009640700c0c9407040000000784a00e0350800700c003904010309141d0310708000c50001d050701d6024102615540c1e44601007180c02480c0640c81d6050302c000c00c80090340034018405440410440b1010b002c150818a20080c80d01403981c1181d8020303000320304095810720300141100c030241e6110365803407041d95500010308010020052a060501070110400c180c81c140c6131140d00075a80ca5840070804c403a00d0b0303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 81182609 1250 81181359 81181363
    0xf0106170a03020714120a0501020a030f1103010308070f0c06020109021302070308280501150809150f130f051507030c02060103140307080d0605030111030c07020f010e061b060108 79
    0xa10103000f43e04641e0003030110300c3c6101000c0c001d00300b000c0c10f8211a0f8000001640c9000d440c01c0d402d0310543d50114039803003415818040c030010071280c04002c0c0180125280c0e014524801031000409101000036284c0400c2104401120310b035410240c441030702540c41901138043c26045600301c2c0700345200415225038115900c244d41c01c0c180c0580c2d80010307680c0d0301c400441000d00c40408118a620303050b64114100c58250003400e0107880c4200c260100e01c00302c810081c001c070360050301a03880d903004101c1070704000e8401c845050b0f01c0a01c20180043d503898148180d1034aa844040c050301d00c10305400000188070b0002541c1001e07800261b1000643e540300c081c114115080c076800e03880140c01100c01000401c00c8040040701c81880c43c01524603200c1c1ba6547c61809a106d491004586503c5003c01c005a28003807284224000d003052100d491803403d004450803c0c070940000034454000e0b00c039400c80030f0748142d1036040e1040003c0d1141d40d0702c00400d0301c1d04c0c902c07041c03001204070b0798800c64002150758140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 81183859 1250 81182609 81182623
    0x4080901020c0111100b0604051207050a050616060b0402040302060d0e0f01150608180102030f01080c0609100c0606051018081b010807050c0a290c030c16050f010617 73
    0x42c0c1350103000303502e008003169405880f5078620580e20903801e00c00860320b507172008088441001800010a16945440c040c844450613a0740140e1166200f8003080c24114600907130031149a901020018981c19801d00150090250b6040a9003000000c00c40b00e40034440c0f075112400850960040320802d12140b040f05003a6811b01c2c000110001202400f0401240140d000c0c40d006503c000b20749079403928150103142281c10454034218088828801000350b1603013444800c050440c00d88035245044c40110204403600340c406851002c100c007810001003031019a502560292800800101412024860051690350041c00a05a070903803040001030351800001d51040f089420301442e034050020800555001400400b06014810200504603010100707126541070a44942511043c861051043c6850190b8030284004807a100c070040c451208404d40c252030307012300b521400c41c1d62030094407014040ac4140c83c02c001d1041c032030030345070140505041d0803000558244440c5599030340540c203141035580107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 81185109 1250 81183859 81183887
    0xd050619141003110a08040209070320090d02090405010b041a0f01051b07060f09080c010806190f180b01050a08150a050909010e010f09020a1203090e04080901020c01 73
    0x30405622444605280c500c402e81038406003000200c42c0544000704080d43c2c801c810500000d070003c001c0004500d42228581d801401d01e03e0200020500c2e6100b0040f07000126204030785e510f0022a611016503140310568500ca507000d0060190f46c242446c0c120f001c4d10403942c0891095081c40850440007080941d5010008001083e04043c8106040191280d502122808114020030003442036491005c1103c200200b84681d22003001402e07062005000030540e801100b140d8228900f21000f9a038031407001900103401303c580408030210146440b0030880c44e648000d10051588000040040c80c0c02c2d1864601c42c50068284030851415004407420f21500c101407010505070404207840102d40c815950403207a01070541504103866900281070030a040b100036959a45400c85d00315681070030300600f1000510300c9000c2c04030041d40e6000802d0046036000d21a008064020070800b8548640c0c40c400042c00ca8400450050405003002e014030b40c0800c0500f070152041103001c40595109110006541c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 81186359 1250 81185109 81185129
    0x1f120e03071a1b07030c0b070c050606090c0c0d030902030c0904030804030c06110c1e0d020304060822050d080105090103020904110a0e0c0405030c09091e0a080d050619 74
    0x807078512414512004040d1100303a0004211030f0f1024580c00c035000403e0414081d4032403410749a02d40c0f81880300154020002e204000780325008000049000071201d8211030110303440c010640d5036400c441d00a010b40150780c28036210b0403034141e0b81180c1661144406500a50645801c1040c2005220f1258400c2c0d4000b4002448035001401081c40303149150314091240740042040d405044041c2c0181e0400c3e841400d190308801e070104a01c4031403500051088002d02e015150300c0e0100007001e034990140c1d01c141014460f81c0c034006900c0c0d04030f16240a04004a6030403400030401035080c055599910410054003140300000082680d180c008503043c1200d5000b0075213034043d070700c4d540d8020780003400004003604605c400d00041250341040071090300c903003801a0300b1920307249803c017014644440d100340107029518503000d01c40111004160400c41290f030410407141038840a001d285007000c400c20141a41d80080ba0310703901080c0582140e40101821251110264512032a0003c580308500c102c0b4014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 81187609 1250 81186359 81186383
    0x1060801180b0907030204050f03151611070f06080a020f03010306021b06070305060315040f0b1e01030b010905010603230910050a050405070605071a061f120e0307 72
    0x52405485034940740191101c082030300d0030404080b82c0042415140c1102280c1c0106083c40700d400d150b509000e04800c12801051000c5481c0002100558054404201ca041349950700700c40b140203070b40c600602c078101b608480131070782d5606074108005024060707040000d500d8004103c83d81d03200d000340c902d81503002c0304180c40c69107580e1f5a80002c0d40054004090a40203200c0e0044809040c00f03540d1048a050300e0102e180d03e001410941000328842c040038103000b0b5401400045010030504248840e8030442210f015202c00c0344065010f800021148090b18141f8004000c000710240f61504844032490180b005989400098041da2a90900303403a4559180d860382d489004445583c5401088040581e400c020000b0000400d44a0849600380300c01d480d0400d000c2000000c100c12402490949003880c01e0100c0d039610903603170660801e20f00800b9051039020400d079075100035190318100303200d1a180500c45c0c0307103103400781070403440d5003400d160b03503103083c4144507080400f100701c0b08101d5200703110b1800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 81188859 1250 81187609 81187619
    0x62d010e0406270c1103040e100e0403020f0c0f01050706051810060302100206060114070317040f0203010b0f0607080d0603050106030b01150912110102010b041d1501060801 76
    0x2144000300e0240c0d401900c91000007502c00f80000c0358401c80c3c006100b510340140000d450070098480381880782040080e0f4031100615040040180c0d000e076518000402160788440102a03071801064114a02081c00034050108040c0c002501d02918480304091700d8081c15414200089110f269440b140410010010400000d14036400707035034080b403280c0040b024840080441c40c83c0034000c448a1054680d04d60b410701c00d41c074103035002400c095841d00c014640340c50208002030284140c1d40c13040e00600404074040d81058000c6c003a07103603d050702d5402c2c0b0b0014030305401c002c0011102d81c0010380c06940380c03401007180350404210302c0b148800b003e400e191612040d03503a95006680b0202c0d10b4201c4643d1a080840018001e0054500450145081c103030194100500001c0f1300514040810901110f584200300c0c44d280020022070b02034104000e404c3c0000d40000507030141403120300c420386c42843c140c0b062821301c12800759641140000c0301110b00814030800c5c4e00045240a01032034003c64000001004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 81190109 1250 81188859 81188867
    0x31b040e010f050702030705071509060c031209031d0901030314070c050d0b010825060e0607021302030702010e0c03061b04150503071209030e130213080105062d01 72
    0x1011940308000150141802000380102d070015905940107810000d2080280301c01001031401401d910007043c10700b044585c101800c0c01c070b03191042c0001c0c00004140f2030181401802e0078050354081e208180320481e070740d15004040400c00152a405204e6161543da02801d2000c09a8180c81d450380720109401220281000160080201142c81035030060011802d5140c00c9814900c01c1c0c403c40303c40083d94107152180341030200c4281d51014032000ba070343da16044080328a200e4215106410311202c00e0b40b8480c04640c82d4400e40c00080d402038090042c1e40c60741c21b5254000e5106103116402005a85003a804140e01c56445c02e098a506910003008540b451010144035008510b80d40e41e4149416607901e40b001c110316808042501141004c0104440c403504555031103103c0301e01c01010003c030115564060000d10603420024081c8102000019001d00650b045814413000055503524407640d5680040c0030b0131003128070700e001d403000d01c90b1008a51098051140440007a8000d400f64501e0350300111 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 81191359 1250 81190109 81190121
    0x309140a030c0b031015050316030b060703020d110307110402132403051e040308060a050303120a0b0d1e0501020918060907020718020c0309060f18031b04 68
    0x180d0000011900100080360401400014010080c01c03d4483c584050b481140302c8450344007981e100710442c0e150703502513840780c01c0700c0d03004c1c2c41c460070301800d0344000100f00c001300b402d0140150881c2d000a403003404d0503000114040b000d000d503541c030007100c40040f018585074081c10388001c00c451170b0703400c0035412031402c0e4020704000c00c04802e00c0905a03a0f2102003103c0a20070f44240c0d1800f402d890120542e1a5140c09030781c0e44903802d038011160000319040078074603401d4000e002400300070a290105a1a44d10015048001c0800400300c0c0d0729403003082400d080e03003181600c06098881c070b001d4155450341010b2004415540c2c10000c1e8043c140c0700c00c102c4201c0140050811601950300700620007940c1c3d03543d40c400c1c130103103095000210715203800d605010000101500e031600350361046d8020002c0310034112240000d040074010260702d41c031207064002d2542c01062a01e80d40100d000c00c0078140c80c6a03050180c880501090455020301c8524024141c0300d000050001d580307412131011810044c10903030044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 81192609 1250 81191359 81191399
    0x111806070501021b010b0901030803040206130308030c0c0114010f03021003090204020313150e1908070503040b03070f030b03030f16060c09080114061008060102030c01020f0301060906020a0309 85
    0x950314010003550340508a81c4074200880c0b40c1d001d44a5040c00d0400c0920030004401c0e403e949440d5030354156110058a4080180020710400000880b2800b03c0c40f100c80ba0002140c0c03150006849062149070008982c00042c5c5541d410740c6401c040b9a42503a52185841c102c610b00c41240b0350079401d507001d201c1d040c00c44244070380c1410f48801d105d400607215807008620501c1c02d101907800c0d044207481c2c12844030f42d49040c0d103003003c1d0800d003107007110200101d070401400504500d00000da121900d41290503024861025205010118000401e0111000214800d00c030550700c512402c201044150101c0e0ba06280b425055401030182d14410303c07540000300454480010564220390f00c80d40c403d07050380e01c2a40f00c20300080010f030b003c000c2403074240111001070100d502500c4a5182c030a02054a044003030302c1c1c1c0360412000d2008105603900a0045540901c10f000085d50350342d20010121600390320078404c40c1c0000d000d540c0001a80347c4040303031002d05150b0643d140301c3c1c05840c00810102d044881031003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 81193859 1250 81192609 81192619
    0x605071106010801020706050f06010806040e011d0c031513080307030f1a040501120506060402031302090108010c120204031e020301060906230a05010917030412241118 74
    0x10045040c00810000e4001d009060000d83d41d284d00786811416248007030503024400001ca000c0c48500d03030304003038810b9100700c040e10000741c00f02a1140d01c5000d03000101107851b980c103103503011812184010403042e0344100e064048400b07200c8500040400c100045801e40c901d5541605401b000444040040d5040071301ea140114158200007400000c03240c08803803107030b403d00c2c0148a04d02daa05103030003018014040c200100400320701c0ca454454884c1c50082840703118550010029110000c0d80503c1c401607038024002401750740e12a02c000703000b018020802808074400d900d80b2801e4180034001c44040e2a48022003c03100c8040c0140c416080d41c0c0228100d038955211400807800484500c266801445001f0111404900811030f60002e00c00d4281600e014040840e022700490f600304080e40112002c2000c80c4106100b01403041d800c500a5800c41c0c5540c3c050b04016078103118450002c20a070070300d01c62401282c01d40d03d2280b4011211810040c4180c0c0c4818031250141e0030b509074000c21050400f0304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 81195109 1250 81193859 81193877
    0x31a060309060f0c0307050904091532060109053001060501200607050a0509040906090302010b0405060913020d080a0c140d02030301050d05011b0e1305010b0403060507 74
    0x1001448035042115064815800302e42040080b0342000b248940048440101c10724606044400415920501c0051030103140c40d000365104010340310b0344904a841d1003040c10080b0381c81d070602101450800e014030040b007024100846080c50302d61071410340515416150171406c2c901d0f003c217100e24046c08024010300e0700d0f00c921683c103585428180221554165000000e01a41003030009010415400300d5001c4c001c40241010303481070344c00030340305070030040314102641c0f83d0321403440c11105445074000480d000b1342403505600400c00f554000a555500c2034000b806400c606070103000c100c3d281210703069801104440844c000c0a80300041c94445800545400540c20a50b15110310a9222101680008202c449140c091111100c10001e4103080c05010b0450000c81202c025500c0c001802541d01c00c00c007402c4c0c000100b003800d60015450400360b90012020070388442000d09041ea03041240c0d4095074456044c03141e038004921441d410385d41403901d42c500706030840c0c81c0e4400502000780301c80c0902000d01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 81196359 1250 81195109 81195161
    0x6030a05060709081e03030a0e0a06110403110405060d141914070f032a1212080a0b0d12180b070302070e0105060307030c020304150806041107050d03 66
    0x1124061042a0781d40751a0a06890b01c81c4480c50001c43e000c100705406021a4030101d51417010040340d80000700318001050400328980303c2d80c181001c5960041010b480c0130001c0c03d01c1440710000c0c00c2102e005021a009101c41c45082c441511401c8558652140d02c105158000900050b140d0041d08650303070494441e8500c0c4907079103c2d510804401515000300580841801c0c038000c11000f0301a000040f6000c105c1442d5507541c0251403402030034460000140c028510920129843c14001400d6103400028551403600b010100c004034162030384005064440010300201c036074025181303940405804101c41960f81e884114814031f003403541d001001240b00c0301c200400e00744513020b0b000d030010b5260650b0b00c01151402074070304200d90b48002d60703aa9102d80100490365400c41503a40c4003941d810085034201ea1101c08901350b00c00c540191241408334403c030b200165000c4a02407088805807004c200218103184080e0b103d0141c658010110743c802007c5091451017600710005001041840080c0c4801c51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 81197609 1250 81196359 81196363
    0x230d031b11040513050a0b040201050d02040e0601021b0d2603010f06030b04050417030406060305030c0309041409070302011803240b04050105010e01031e0c020106060801140109090506030a05 84
    0x89002650701254074110207045191a2040c00c3e0042c0031600014841103072030f511152111020000506000c9007100080d041d64042c2c2c080302c5108124107401c42d036072912045a00440c180030350f0414010300c6404080100020700f0910511082030051482c00003d079031356510341100d0701b000503c448808148072918010103000002d503010f0829803440c0210b9904201004084a11043c1d42d40c0c892420a010b00000c510001c80820310300c01d01d112541d41d03a580b42c3c00c007035025081c140d10052161000103114071003500c011000c4e1003004422078050114248003d00c503800034000b070361705108580000d00c040005601039000d40000c10020303840000039903a41e07291240c1c07c82050b21200c2481c10001040e44851841c2d1080241c00042210100010750400c40000c0007800c240c04a6030605540e500d480e0090382001c040b080481c1400442401540410200280130f070809210b8907020440c000004100c0b8a10910300c4540043c0c1a034503c04d4040c6000101d5024000c040d109580501521081d54041442 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 81198859 1250 81197609 81197657
    0x30d21060b0703020a0203100501180203060402130e06010f1103030619030b070503040b0903070c030b09030705060c0a02060c0313020118030203100b10020102090112050405160618230d03 82
    0x84e13009011034000380d00626080603102290001800e01e401d0041c851004c0c100c5044a60740e11207400180c41b40d9030300300401c009100c0c007030410f200c4010304d100000d140c0380c40e503021a01c81c0d407007a82c0d030030f445a00d0700e00309807074012a9400d0040c45410a00010b40c40d4100b0580040000c1c00404201c1092580c1e034662000510041d00e00307030005080002004140110034800c9900483c20800540c6404010707128020042e0050000800340388064010822098082094498041c1c00c441a01c40740e0400c10100075a551120360000098085c04000855a000c150240c0b071140c992001107651041499004444209032100e03600c0e41200003540220150f01c04000108440310a8040010b04080e41e00c204082011424915011a1300400c00c5040c1c90343e014240540c1c1d1300f070a6901240d1511580b40940c20040c06403044001040400340010310903910004101324204924001c00d2104d4071031138160b400e408040030b0303502c0c004031911002c101c605084081c03241c1c0c607000c0d20b807142e84003109030700142d90415 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 81200109 1250 81198859 81198863
    0xd05120c1b120c040518070806040b060102070614030a02130b0913020301060c030806030309091918030f0f0905060406030b0112020a091211040504030f0e030d21060b07 74
    0x400403101c80c0c1030010030150081512000c650354501402e000c0195951002c402415500840d2a04040741c1c100d982d8041c2d1903421303040e4805031740c0c1e49511620381c3e994981d400c030b605480385c214041c08940c244d40003007030350f8044c2d81d103951390703082c4001e10148030784170b035038409006158142d508000b800ea115110600004c00b500843c1e03425540c0301000006c0150607801c0801c111030321441040104103c1d0b821802d200c40c0240d150404648550f54440060f00714040c0380c404030f4104880204020048010700803200d6901c00b090001c000e010b41009600121000d0041c3c01808951507039960b85005010380d14054500e4040e16000c0c503442d483d28089110358109a0000d0003003521801c460300550b03040885900c0150705030b80c0031401c01c584000014100301f12403040000081d0025850010305c40e1440c41d014010b8405070040c807941c10a40381c000d1004004682500004220000000c05882e000c1503031a180709240d5100252440c034501005056001c406040c40890360310f0b0303400220440844041c0401ca8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 81201359 1250 81200109 81200113
    0xe0115111f0b10080906070e010210050112021503070e2b050303012d03080a05210402040b030309010e01030c03091703090c03030a050a0507020a03061e1a0306060d05120c 75
    0xa26220600040d00501660f040900120008100e0181c0700011541d51055583ca0a03484c020361313450042c0e01708144c03010800007040c2403400100700703405c0148464581c0c030320030b8030954a40d4a024071510310b540002d0701d1740f000040c1009658103440c6807480843c8010400202d0300d480c004128031030150701003c40c8104481d60b0704080010811409002c40c0180070951184d0046070454200424101c041d03045d000051140c1004904054103500c20b50a43e081c51621404454400c5d1b4032105100d41d0030700c00c5074100d2049051030502200d41c00c0102c04d8507291a01030311101c1d500c2c102d00d0019406010041551030030160b4a8100c031300481c01c4800404404480b0052040d62802d1654050782000403000505000350700800a66056035407101c12a80f0280b658a03020340c49024500c00900d40000135803002d1310f03981c1401920306c1405504d94400c140c00d0f030282000c001c00320880910520351a0846a1039030b1542062001405600302140c80c00e01152244068447e00240e03e0700c595400d0304504c100d1512a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 81202609 1250 81201359 81201371
    0x24030a060903030b1212031305071403010605010e01080a1d240603060405060a0e0709020f0c06010504060605160807020405100303030e0606060304120905030708030901090e0115111f 80
    0x4180c1602c103a03800c1101c1903510170b048503001281140d550080807038680040c6400000121150000c090402c0100d0340041500c50701c40d5980703541d4002e08407442d1038520a500e4010300045560203145258110241a101c4001a660720303290307000105100000c40755040840a106240d0707030024030030180810071110107544844200807006214000080249029034041400e01011640010304150b105070081c1000ca00c00720b9004d0344900b405075a0b40000007a130f00114155100f03100e108040c0110304000707000c4440d03983e616020042601e03031501c50000810002c00011000141c90800c0f210003501a044041ca0f09001c0da01140855604443c0b01d101159502014410103516000d02c50200c04444000c003090300b41007002031028880940002c10700407003d449825140d008501c2c01004241c000d003035510150350341c3d10040e01c9030303c0100f010b4001450303903001081c103180e030520b20ba041e41c6043c00c2032031514040b01e40a445054050325442d01c2480780003a040d4be0304402d09031868031200020004900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 81203859 1250 81202609 81202613
    0x40e330603010b0d020d0c09110408102c0a0c09021216080a020c0a0b0103082a071502030d11040603050108010b090f06010c050a05012f0324030a0609 66
    0x2158080d090521a9041c03d02c1d440442c1c0d5040c1e08060034540440c0c0a440c0010140360000c0c03080300641c401504203040c041d03200240b29003030f4007500c11180380c00281c80b030507040b012010b4110740c07003814440940d010201004581c0e0100c20081542140c56000711a00d9507215110600004103035031001e8900303030700060704004880d80b40741c0b41e9801549108a4042e145103c64024101500090511454507408074a90815200c00c220b12802203802c100c0001702561a0700349000301d1b60008090500d00c0c20440c00c0c0c0809040302e02c0700320302510301d81303409040700c43e0802240f20121b20500134414218403042c40105c0706000707180f00f400c58a4100124041d42c3e64900a000b80c20f4800580c030115460340751407103522840d26028619075028a8451200701e0390746e900e0300142c80c02c1506940c054070034030802c11b4200411205500018064154034075103000050200305585041180090440350a0400d2010541e140251041c3c25048002c45202007408911800400d16001c00035100341c440d25125224102 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 81205109 1250 81203859 81203953
    0x2070803091b03030301150c02060702060a0c060e0a0201120c11070f030b06060301051e040204090c030e010e030301030203071502010209040f050703060f150e030f010207030206070f030911040e 85
    0x40e06074143c003d18115850100b0201024100702c442c0000d1056504132481150b441d2021203000d03d40c000c10158458104a5008100c4500400f044800614000d01c081800000080c0e8100407a4141d640310041c201c40703010708000c0e25242a0780e0041c0320f0340c001c003010103502c20702030040901441080b01400ca46181403904040c6e00c05000507005030001c00050102d13881e1240041440c6609245554a1245a402142c000c1c8642e500420202d85400c541400d0164180c003c0d204410245009001415905094940300c0c813081c0b00080d4943c0c0156802c1204a0101c805a0616082c40c00018144401d0030040313400d1303031031008040c0030040e610000c102e43c45e600b40c82610b02414000c512040801e040004990303039021071f081220103200d0318808440482d9420041d400001030000300964840b141450040d41e900e40c25600c21010440e0010f1540486100e40301c1d001540c2d130442517405070303840c1041c2400014817040070741064900503002c032060061000500406181081040b07009000608180d8071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 81206359 1250 81205109 81205153
    0x90108281b0e091c09030f0c0b0d09051002031608040606080607050a110f030a0e0310060308040e01061107060c03020309030706080106120603021e0a150201141e07080a0207080309 79
    0x842c84401c060850f00710b542c490303401000d407a40407c070b94a10010f14100200d100303020749e2100303600c040009000f8204243c0754014441c21403113a02100e4190394030400b405c0c240e0000701c2c0e551980c000c1150711498120700c6420b801c1c6d0000e008800c0058502c0d01c1d4609503060000032618100071400000300011810350180714450348046030005851031080d05103403940c5900c5580b4080c4108803036040622490f64043c021800d0031440070f80c007044010364030325203404241c1140c4203512440300c100e000025120300940c000180520b482020740742580c2400401d84400030600350503021448280034002d025181041050042c00f17440d118a4810341c03402000038036402030100c075080550f0a200041005032a010070f0540c800e42012400002e41150602089000c030b07595210041222440d2a0b01403415019807000d030003000d181d080d82d6001e031b8903240004040e40c64144801d0121601e040000d4145129104041d00410448400340c501612519894181c0e081034500c48816007150307800b0f22000102507103030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 81207609 1250 81206359 81206383
    0xb0a080d051b010e0c150d050a090203010c02030301060503040b19050f04051638040b13060c0503160204180605010807091116020307030f050309090108281b0e09 71
    0x3130003005054440c03d81c96015451010313000303142841d070a1181004072807d03100d20b5000000308000340d141c000c45a00280ca10a40b00b039000c1d5190010350002c0314408011a4107a039020749503c0e2541e10b03159289181c183d030043c0700764228107818400c00a008128010103000300702d00c0800c1e10840c106401d049007083c01c040e504c44281e42100604010001003440c004003031010000401d250015112003600c0f81c941c2040d13101148040001c0c0200701074170081c01a00c10508450b4804200603100c210135203600891a10141c03960340144100104d600d060303d49041300c3d0f4409003002c00c410320660400c981501034410119041600c2c0c00050102d002d003001941c0003040700590900a01c5041d02c0010424410005030861072112000b00809545081108000559101c1603034000701c0002c0c00e0050b201e4010b0003c05214044003000005c0800c80003403106000c0305001c2e0000101d04c00034044495581400b2000c8980210042c8141303a074441c0004460000c1c0065070740110b083c5880c0824606000c410109 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 81208859 1250 81207609 81207611
    0x20a0b04051012060f1d0603010203010609090e070b04080a03020105060303090901030311030c030301090c02010c0f022e0c0c02090c0315010509190b0a020c0301060311040b0a080d051b01 82
    0x1c00055980a104070750000181c10104900d0340100c00c80005040c45800035001110451800101100e00c04032502c0b12410020400966803038003003c05080c0d03c4288123541c0041d410031000d20075014141d100c001040101c80468686541e60440c0030302580003a0700100031a0022010b1030249a0280100396100c0000c43c041c52522a40c00c000480146040c00003408124040c0f03e51010141c0c10401c460605e02da2404a0b5200e40c0c0d2401001d000d0488960300c10015402d00d500c24590900400c40351403881401c3d0080c041e1000a4441101d48401c112070054038500103040401c9183d081d03102e0118400040e68540703d8401c1c00380140030b00c00b81c010300004180d6500f0020401108034502030400c01650920301180ea42103141c00042c140c1145c0d21101c010424088d00004003c0c00380402043c0c040c2141d002c0c2d0341d03204001c0c400c15007284d040f484042d281811400722169680340681c08564507205c01450342c50b15130b4907060168030784132410b108500030820005090300030282c100c818030141101c60300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 81210109 1250 81208859 81208867
    0x30d02010b2803081e07050d0314090604060c0509060f030103030f0503041106030c0c06070e010206010801061a0a03021c05061f02100b031c0c060501060305090d0e04060e070c020a0b 80
    0x10b000c10140d218400a0902e00021134000c5145031000982d007408103907120384944a0306c0d103081c1b9507121203444086e030022030300d0136010b59603290002c0702c024880d000d400c014115660316a105e410140c102a040502002000c010b0950260b480700003800701c01c000d5942c0316881e036045141c060b200c922501c0892007805411700030000000d4000e404112040019a44262603899171510f807001790040d042100304a008800030040c20741e50110380081e60030003d03400c0700c0c12642d80d49001422100107010303001120700e0004140e40341441f604010b11014546160052515100011504000b83c490600302c0b4180d89500610103e45005070070080720210381080d0310701c4c01c4580703a03001e9550042c0d40200c5402e2a1148808085560180b10450301104900503011002c100c820000300545199003003124014a89000811124401d1040c2d40c85400f550b402081c5411601c1400e481c00c4d81c40e0707242d095100b61100804581c0d050b20f4504c00f402001291541e6030745c607540344104140301c15550091030900d10300f40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 81211359 1250 81210109 81210169
    0x30c0906050303040f1401051e1e0c031e0c0609030c0d1b060f1d0a0b090c01080705031902040e01050126010b07080d090b060910030809040f0b030d02010b 68
    0x81e00d0f00702112003101085c2941b00a050042e5481d0141f0500155410400c4192420007100140204002e000025030302c4504040781319203007002d014500c0c000354203074010300017000754002e115030260710f0018090b00e650900b21544112481d060040300c8215423030f0008a040582c3c40d000b040aa42c0d180220b08242800700009605081100c0340107030042d05c40c1e0b4461101c0045082c0c680d000b9800e03c080d80e14000b0007082d400c1d0b0042c0e51010a030408507002070800d070020f000c580e8007146c9124030082c160346518560700e45d080100c0391034001404484a0031407400318218a01484c0c070003440140040803030034000303604d44000580400840f142d43c1d208e0304460310100314054107450256054865101a6503203407a268144000103000755121000103910b000c0c0e04e80248207082d587c0d548106000c882c20442503588030728010480c94103100040a0010900051001385003507000000908920100064009401c20010786002c1e00d43c1c00c00d5025035503900000005040607400154442c0000d401201400500e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 81212609 1250 81211359 81211379
    0xf0504080a03080a1b02060907051203030103030806031c0201090c0e07020601060807030b031501030b011a030601050a12091a0108010204060e0d0c15051201060809191b030c090605030304 82
    0x3441e40201088038900c000341011300729601240000008070044103444060a50203540e48900ba2080761040c4500b0000180d18034200d071502054981c4040035604503445c55409a034030b6000540880e5040c082c0100c0928031340d80800340f9001810990b4008201c0741319a0070400c0d0610b895400c9448020003900c1003007480c030b8001a8083c11a0001d240c01040c613640d05500314014a08070418a60502410111000c040c02c0500658160303805451001e16503640c030301c412411030120007140c100c0f5400900005440e58014409415081807a08160740c0040000040808840c0e402c0012103900724004240c0e440d69071112461405807814000851400c0e0420002500c030b100030540841c80348440d400b01100704550389407140001c0a800280d21218440da840160032604a03240e107140c10700c4140e0001584d0361060340c030f440c0102e215401500800f500b0704055000c800009009680e02420145601a44003115494400841c041c846030450207007002088001d0325034580c0282d2103035000f0b0005111070650 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 81213859 1250 81212609 81212623
    0x7030b06010e0907230a020624030a030c0c030803160210180f0f0602190e010c110409050a0b0c0c060f09030a0804060f092316140310020a020703030f050408 69
    0x2c1810500d03010000703110042c0d82d840200c00c0c00717800760602181845800b07070002038a0303000e821129020b10f074000701c800c0d030b484078204414032640e810351181c0302c10310120307005001c00b0500a02070070000350156100e4a4425042d401900c4035100250400b81003101c00e50b0601100303000c618044401e2004c101e0301d40c0311245012000c000071f4204401c9625144c2004840790b0301100c1554090b0081d901d403484044151404001c0101d03503c08903803281a210400d6101e41c0d4203048960384529401c9504200c08207000c0140f8101d5000c840174807591840130007080c0c6050301544a0b4182c0368080303a4950b402000c50b4200b02000d07201c50030190740c580234445c050801105465021856241451240c1d45500303012001c1c2510584918043d4642055442484461a0101160100b035031078039030254441c0a0b41340c0e0f03803a0320040000c00da8080c072005005d441c40400d42d00c190b00308001e00321f8040762164041d000c07c1303a01540300600076030b000c280c08001700741d0054032100055032503040a17410685005c0c3c42d42c3e144c0c0b039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 81215109 1250 81213859 81213871
    0x1a010807050120060f0601081303050a1407050f0105100909050303070309020a09090b010302041b1d030a0b0f16020d0c02210a1b1202010e0904020604051207030b06010e09 75
    0x7501180010f40100d00c00c0c0b001c803401e00a008540c2a420501d600e4807814900f074404500145c0001d00140020f1804a414500541c1c5666000e24005110404450008031521143c00c2d00c541007003880c010407000c0003d01c29803141c00000082c142460142511440b40701c0d4407101155050070031003400b03d0404404e8036403017000c504000c030718030321a480090414180c0d030b042100240e1502100c442480200629641a01c3c03090f01d042102207a100c0f802d00d80e01601d0045000062890013440401c000d48800000b4140d002074115049034440e9512000c60500881d20041005c816504100107200d0904682941003100d00103821902d0001d503000300b2551003600040d0241600480c00c4c220181ca00300210f990410880640d00c0c0c1c9505485c3c440481102d82d08803d403211210f91004c81d110b1394182410380e040d5816140c00300702e20909002c3c0a881c00c0d00810585c0d0040d41400001201d4a8554008901700c944a016001c11070139441c1000b40010090400ca04110b102100301c03078a40c07201a4400d4000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 81216359 1250 81215109 81215117
    0x90b0a120f060207080d050a15052110021602130e0a06020708120c07020103050709081504081306020d0f02030310030803060a0b300610080709051005071a0108070501 73
    0x22450b0405802074071548100500b9900000754555840c4026400f6a016104064080c0000700000340303000b01c100881e0181036800078040c5440130403040c0c130b00c0c801e94910f10482d06403120100c4103800c6400300c0e00041c4a400d425800953b401f021882d08010303148425003689810402c02c050006129030b100b00341d00d00101400e90018080051101c100240d40c410301e501da21246480c9450034203219650450101240805d09003808901024050f0b50304000f916038840082c50110510300f1144c2c1c440e80050019240810100f004402c008080380301c041c0580003e03001000310650344640180f030107035104c0c495002c6410078014402e8904e4103280010407a500400404c1e2a0740300ca400140244200e503101c544d11850004d11094170001603d10710409a05181c543c001081c0c071080c5828003610b00701c904ea035208808074010000503004010454002c1c0452410300843d548075404a100b4401c00d030b41c40702c0800d80205011041101240103c0c81d5008a0010078606514061901d560f600f40d03800340d18180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 81217609 1250 81216359 81216383
    0x1080709150306030b0a0501030206030c070f060614010909112b050a050a06080102041202091b070302060115020102071a0901021201031103010b090f040210050403060e0106090b0a12 80
    0x85031003804210007814503041c5420540d65001c001500524841c84100e9190302c582c0300080d0391014500c1aa81206d802034501451039482d8070801400f0741c401c0204442560424400c0d9011a003144104000b07403142c5a0020307808080d110000d0900290741c1e018807030361030511000c025640504404d8a80d02c0c660f6000602500c0200c01c1d6403074401c45190a1004000d1900081195480403500082d004420180c410088180c0f244852400c3c1c0c80380f40107044204001007074200050401d00f10895000303140c1c00001c450003240c1500c9469550003081c00382d0041e402003005110b01a0240c41a00072124140000c5250031125500d010b4620100301300719560405e400300043d0100802c0d0100c0d600303441080081145983c44e0f00d000d001d03000c00e640ca40c5009610704110200981460740c100c5000b85607001c8010300c00d954030740c01c11070b55150b140c5c034010800ca810312001000403814002c42d50070121007030000c40e0042c203192040c4103e075219070105110300000da1040252907084604031045581241801c0c03c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 81218859 1250 81217609 81217621
    0x2030f0d0f300603061a030c061e04030609031b030e0907051603030f0c03061d071e0509010e030d0c06051b04060504090501140a171c0e0f030109110108 67
    0x120600d6000c0e82d15030315100c0d1000c2400c80700359a201509a0348502010040c0c0d41d1044441c446058015007803e405d0740c0511099125443c241028003807107100c80101340d4200c001c2a0512600d40c0144e80204d41c0380c0c2e11008000b08041c0c021204d4500e05415a0741c1c5503001c00c8a840003064010a0b4000078041c100e02404107154903c25803c590100011001c601248103091a0041c0104110846000300310b01e000404408144640501411244000b141542d0714102c0b0400c0404240040d00e0401484a10b422080340740c618485d03058010502038036610780f55041c2e0800502880d00040c0003a00c40c5c0c002c000c000303002942040318800c1c0160021000906036a610070a14400151075035140c080c4400030400103245a4044014000e44c0c0050206200d540d0303941c80099400c1a4145032030341d100e4003d007010b0005841c000d034052400c681440c12134074640359003400448080c1d80c07201d0341030000307020003011003075402d1095140a418400340d00800c000c00654540881d081941c41255040003000008600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 81220109 1250 81218859 81218897
    0x603020405130b10080d051c050f18060c19020106080a0501021b0601030c0314190c0501141204030c050f1c03060b090102070311040f060b030402030f0d0f 68
    0x14590140c81000103040c0802400803421001004884031a20400060021100d881d01e40c002c68620034020040702c0c100da101600d60307800455036402e0203661800c809101c0203c5001d482d014000d81810b1180700e0621000c0c01001d020703200d0207140103070322440a01c040803062801319190401100c611b041c0d04268880100c2c0906640e41c028012031240c2d00694003031001c1940204607410307803802c03011303142507040c0c00d5540c030350109201c081c3c4118410f01040011032000c107800d0b0340318440e0700140e58800f081e01c098174040003100d100c1555110401c2e0014401943c00c225400342400b6210902c500305040596040145440200010b041010000c005410040c1c10801c042d1842819030688060000c0c54035a8509840720351003610001c1c3c1004000581200d500049440c4400306074042c051560440d103801d034116046405140d0025601c0703100307800c821842e1080d100980441186075030760341401c0c01050b04e4a054068100f56581003e090300c9409a000300740e00034950310b18207051483c2740d1900340d030203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 81221359 1250 81220109 81220121
    0x12050a120e10021c0f0b01020705120a03030203070915020703110118030807110907020c030712080a0e1201090b06100509091306021303030818030301180203040c050604080706120b010806090703 85
    0x4450511640a40c2010f091b00040c01c140710a03400c0b04c04c2c01c0e07a20070400002d0100002c001c45c19400076407803080072a103e50000c50340002e180c1059001c10f940e9441c0015608855031804005801c03151060080006a4409000f030450034613140000410300c122000f1503c1151000030400d500000c3c500080100382c14192041a50040c41c030500c80c50680006500d580904803800d00c20302850708040b598143e01c20f00314080c19008107285042003051401079900000d40c1a03c03d0340201c1030a81c03060542824040e84200a10482506200d420250103014040c88052140810b0010501031110280c498401c05a88940c40e1481300101c400301e820140001c0c030035420280c0c1d4504000c44040300f4140c229081a00540c180c4480008480c1307096001034690000303020b4800c40041002c4100e0310700311a5000703541c0140c002c0c500d0300103c9540d54000b40c034541c415801988503070440e0108002080c0c001681d00001c40d0038074001e01c1410080c0000820510300141b0031032041e0740220108038054401d610039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 81222609 1250 81221359 81221407
    0x2f0712060b15040e010504110a050304060e0d030e0705060414060304060902060412050f01151403030c0a06060509070c05060f041a151e0904020607080712050a120e1002 74
    0x1d980b9098020b84101d680c4507014007510210003000024850410340f186102405202241a003800d00100c01200c00e540094002c1d205c0715100d0f12010654a0140543c00000e080d9442c009491001f40300001c1c200200b07a40100d200f42010b00c01009002a00081c050510a0464503650790b6582d0780b610340001c14243c20065000880070401150a5000398000c030012801881102c030140d00f07224408d4240c03080340d4440e00c4200c80d1110100130408a143c69503107420f10050541e030420504110483c80d001e01401c050381d0668440ba0100000d0400640440c2c101095140070302c00480076483d02640d41401401c61003030208a04001021b000c0303c1103d1a01c100c6001460705038a003040086241803185030404144070785c1002117080030f0a4201da540f004814405002d41c038842d0365076002c00503560003550080e01c0c1484c2c20020b82000030719003c0d148000d01c161341c6640d600d84801e620014510109141c909180c3c5141c8214040600000117250090800f9144056a00c60414512040c40c0c001c410b85 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 81223859 1250 81222609 81222619
    0xe0a0506030702210d0b030a11040506060c0f070e0f040b15040902040c0f0e01110a060b0607120206010807050405041e08040918020f0f010c0807021903032f0712060b 73
    0x1404911320300c0b2030000d18034001e80040030f10503014007400701511050403060081c42400d0021602c82c142c03c0582025a100d07600a20032820101e55400c0c0303e09052010455226a400006c024403111125080749a0850b1821800010701e151560301c4800400c4054942540110058241c0c8419607868115400b00c40d400b4000b4400e4855006000e002815030001c100041041c8844500c00c5504c00c04c3c40d0810f428501c802089135003000d07100c40700244104c40050f50080303c10042280440c00040c1c0054420080e5401427045615080c030860400250b50003103481503083c01d00344004514084034201c2c0102045001c0340100b62645170012051280c1d030f005030305003401c0c02c510006c0d142c5000758814889000742c3d81040700c40d0703010040100d00385c400688940030401c44841480030654042c090104c3d688080c14026034a42810f421408100781079008900046500d2201401c010103825030408000c0c42000c814806121900402d4985c2d411303024248401c1c540318540700620403030740c1200100e040c010300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 81225109 1250 81223859 81223903
    0xf07020319120f03020c03072406030b15030c0d060506010c0b09070503060c040303051204062c010c0f020705010507020d0c060201020a14040602060a021c1a030d0e0a0506030702 78
    0x82e01d20280c0152070854000b050107507401e02d2000e400f030b0080f12503010403100914542400341e50f03452103480d403400402c103051100a07a5141c04481d036100c0c2d100a11b001c2c04031788800380703024210420105d200c07103c0c10340250080c0c610450039850b407520741c10801d40d12003c04103469580ba00102d40c02e01e81108040d203869243c40c10b002140401050355420745006900307541c00c69444007260300346032060b444000c0000b02c1c00c001c1e40d01181c04000c2141e410600c1003030007141a00b01d900d80442442418092501101319084486400001c02d00c10300310180700c3d03403e154905400c100c0300652545442d2103000d0510400007020340840d40ca40c10b4040f0a558861080c2001c2915204002d000750464425440414039021030a00760400c05802c0c4c0c4c0c21120aa401080c0e5540e4905c416006900620384100316190000416a145045401520340000390303441c0d82c2100c00c0d0300e4009c1501d4203100745440030034010407280440c82a140c00c01d40d18141d80050320b645680751550398041389458103440307030800c01c3e40c00e0389 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 81226359 1250 81225109 81225113
    0x1090b12060f07020c090f0106030209030a0f12080a05040c05040e010e0708010b0307080303091f110a03050a0b0a062307020307030302060603060a050c0a21060f050306090c060f07020319 82
    0x40d1900d019820715405c60302518001000c1c4854954290344048120402c0401040024840d400a00c40980302406480011103156a00170280f450304600315070b07103840e2404080c410f40d44100d40a90144e880f810500c001e01f45030321107084140703031402020300a9460b41c56280048109400402003801141e0884072190b0f0f86101d01e6000300388000002e4824045e0b03040010b00c480001094074003c84074403000e030910140340300c100110046001ca880c0019512075442c0c1090100d490301920140b001d686000c07401d0302c0c1814520341100c2030416021b104840d036420500c00755034405c002c1024080f8501ca01205d0781c0c0581110740e82801101c4009516210f668400701c1019804581d850040d0f406a0440f0b44a80329051041e0503508111a8494041c03402d00100001d2485030b01d01d8005216040b00c0c00032217002c0d0400341c800341d5205400c030401a03504c0500c2000703a820b04020540d40560800e001d411265040e00001e402842a0b400c94464032a000c2140410740d038040c8000101c410140b4619100c07540ca034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 81227609 1250 81226359 81226381
    0x1090f0305100c050a0f03150302090408030a0506010318110f0607080d14070c08130915060905151c020d1a010305180d0f0201140a02070203060702010b0901090b1206 73
    0xa200c804642d503042201d060340c26070080741a94040b6099484d55074640103a21421001400600c01d45a45131a5241303001002d601c1e1111500e025034040d0740e1041d500e242444005041c0c4101510b07180c10186846c3c0c2880c088085001100c10b0b0943c8146c00782c0040c10880d0002e0510110703440c00030340c03080c0002442420445294014080e0240800040c4520040d80e4054101d1043c00c0f15001c000c10041c00710140010041401001410003c2703503401d81e016150301c2c550044414a140c4841c007807240207414000250045902d070020702c0101e802e10041207103041d00c85800c1c024451003454500d58802192503030700503a01079960941d08800e040080000050944c0881000e102d40310b80407a1501002c6052140c40071045203200184400516000c400d400007182e01c00061000203045550b2000b00c3c40070400302054850140007400b802589640c010300402d07040505c09042c1409682c508040d915480e00c44515160440c0c1d245400000c40020220210f03102400c8410402000d00514007040300030054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 81228859 1250 81227609 81227623
    0x50a1404150905030613050c13091b1403070f05090907080d050304230c01050a020a06060e041209060c0f02010c060f052a0304081b0303090d0e0105090d0f0201090f0305 74
    0x214101c80c5c20783c039a0020107400104110014203150862503c1c9081410900c1d062060100034100000c0e542490380c41c0d440c1a0340f0700c8110f1076801d0b45841c07410071894031108244a200c1004a015104091401100c1055480c991146a0090a01100080d40c00c50144002002403407500b05840240064540042046e4000c0300e0031501d0300b1400b90804d41200c501c01c490512150303010300500b0355112610054400d030300070380b103000118802c1b181c1000003e00c15000b000e00805100c655521141058034140300d103158012062001c0040018003001810b40c824440c1001ca41c0203000700c078815405000413502a010180e0103481c1e1410a810780000140343e61049100b540c81d110700c100040c002c840010341c800074000280f1030340c00c820301c04600442e000800610318040000c02900045c8a0300001e141190000c50b02d103003864100c0180f02d00110b8000c0c0400c003000c0780910f0701ca850300302900005400e41d6000940500a401d000115400b11b9001c1c06030311000d0801c56140501c0e6540d02c0c64565607500c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 81230109 1250 81228859 81228869
    0x120303040c0612020406080f0604020c070f0312080f04110103110a0f0306050604050102030f0309011401180507090e040b1816080115140607050102040308070c0509070c03050a14041509 81
    0x12007400743d00450750910a0301c040c1d07240c996071800503449060b21503c1d07405d0081c0c5182c1d8400da0030840301e21140010000c0030000c09420400c08035991031420141441c1c0c000c06180c400780f04010041252018413002501d030300680c0034003626000079040c0d004030014840321800c0085201c001074030140c0700b5040300e415103200c0141e03901800182d4544042c0581030103548a56400b692081c00500d0345c03244040c016580c00100e02000080c465a10703000840e4124081e4441440716041680d81c0a41903054001c00340c0c806501c0c2010061245892040306110300b00500c040e050800c00804160011010300c0800078400784c0904568195280c10f200d0301d807080c00352089424940c68824006201d440c1d5201c0502120494000d00d66000841c0c0306004450b4483c840c101ca45550800c0003200003120741c0d020b4410345000c0c0700250601130818003409109503014006409004485d804900042da00030119814811986403195200d0070078290b1100c9801140c000c40fa06202051440080e1588440e000c01115 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 81231359 1250 81230109 81230117
    0x1090902100c080d09170313030908060108030301090c020c030f0c01120e120a0c0512070209010b1206060904270506010b04060e090721050402040606020309180402120303040c06 78
    0x10155106880c601070740c0500409583d420b01c01314681005990103a0a81400381c80440c07401d00c4002c2038052503900889084040d11450b440500900d5400601d4801520905009044039410b08541e0b681c0c3c0c2c001482440b07105a1034903200c1d01107500c2403100d080d800b0360150841d00696082c60160342ca642c1c08940e2079002501a042854441b0f03564007c1400300142c01e005032900c02581d040c60480d0340e218400000501060b00c3e40c4030001a020004a00d036802c0c2d500c9243d0300c86405104000080d00103a0240d04200c40501c86080b1689205141940280003211882e0f038980c013420120303024108074150501001011141d040300148010811042315210344103450280c0c1c0c8a07814030b00140914094200000c101920f411803a08158502d5500b080050416a07610036a4004800c03802c2802000306180c19140d1050000318140780c05448068000342c005181440018008500c0303502d01d8452100309402510082015902c1c0d072901c120b5400c000500f03a950700c0c42c141c1800320788040c96100b00c3d4001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 81232609 1250 81231359 81231379
    0x30114060907031a060304021f02030315061801032a05030405011b0c03121d0f2e0b0a080303090319050304031d01020c0402040603060609091503020d150501090902 72
    0x500c01d12034840880c0010b13010311841c0301c00307034144000307504010012070700134807a00c2c00d91220710518115294a40240c0e4015541c0c0c1c41d0440c458105c5040742181580140010300c0030450052005003400301c1d801702032900141005259050005010303148054010050741c10000802569010380114451801100240881000007480b4140d8690410300c0c000011a4201c00c2c2c00000d01c0b6130240c50720300c5c440c1c0b04045562510b40490308100170100048030b07880c1c3e210340b00314551070105010200c540405014005501d00c402c101c90100807144082c0c58a12980c4c880400c0c02694801404001400d401801c681d128500800710355521740c80059807074091483da801ca001001d114100b160703c40d076890b607103460801e1426007041c1c40303410306444128190300800e841c0404988891000c0c0000340907998022500500e840b001602d00350864010b0200300b800e222131488820920f6009800b205d9054848400e00782079030a20030942c60b182c039002400c1c0d500308030001803581c669401410f2624001c41e111900c3e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 81233859 1250 81232609 81232621
    0x30b09070b0901080702032206110d02031b03130e010503151303030b012618060105211002040806010608090a030914010e030102123102041a0301140609 67
    0xa2a0301620400c075800c0c0041081c2d640c6544a0703400c2d01d801002d180101c80c20f1001640300000026240000034042c000342480401000b507102e0b028003250b044450252440101d1104003c0d224864444044600c40c491400e508541204204a0300e250402c0040d440469849a10700321851000f0300c5624403d12071034460711a00315401102038081c07004582c541d000001299002c2d4068a240100241400040c180c040b1403081154080c01d05c0ba000407400344000d2402007906919105d140e1b03507205459004000500c03aa4480d84549008514601035140081c100741d1942480c10025602c00901ca031300204002078810800140e05058418617124903896079101c6614a580d4410100042c000408100041002c94003965185e25888018034143c041e402044d00442e0070383e4003d0218040e20b03c02c00e02049680350306150320350700d10411014000480404400c95202400c9217282c040d218a5540c00d00e100442e00002902044c908082d0003881610249860b2841881d021148280a0a0b0880021b94 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 81235109 1250 81233859 81233863
    0x1504090f060e15010c06060b03040308040309080a020303030a09060e07060207081b01050d0c020c040e0a0203070b04180506030304031707110f10031d03040f031401060b03011e0e070306030b09 84
    0x4070540100c941c09280e5070f110001184d1101d11900c058131995603400f40800c200103003000075482513000e5214102c46040601d0300030881d15440d80460701035007103c501640142d0780401100e070414044034020644007002c0c10820010078a8400e810304503c10140002415600070a49000f114034440c00d480d20380b0348801c14281464409941240045e40070420503444030120341c0300216440300380c81101c0e041c407060303404602101d000c40c1072003005601c4010400110314003082250081d05460304c20608061500710240701c44e00950000301e01d07403505c840024042c0d80341002500c00554203c1da588070081448484c0b1601d5600048043e1031100203480a1049410190000800607001510034080034403500011401841381760302030030404165500c884c4000f03d0802c054000f82c0a00e0310700706500752031403a0210b07900c2c152186d410b906904202040045c260302c041541e04452200c10408a40c8044c52402110f81713031607400c080d0b110080c142c00c1c05039040c3d1641c08842602c0c810040e00c60652245071000d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 81236359 1250 81235109 81235111
    0x90f0c010e0402070f0c06031e0e030304020907020a1e05011404020a18060b0414090108010c02070e1f06031a0301060f0302060f04091a0f0909060c091504090f060e 72
    0x40c04a0400025112a03040a40c01441440d00600701d858800c0b005680303031000d403d0598001c000283e210341c5007400d801003900d2164041e49581fa007c0124132031244513162280070060002e0701c03801c404000600c04078001c0c031050f0a900c5d44440c00781411004012034a0480415020540c0e2a601e420101180cc00d0030081c0d542c01160010010f00320649410545008100b407174140c3c9004603201c0b48001513000c0050003500150901043c0404400c05103010301c000240b0580c4500302a0b03042c403100000345600480c090b4203449514880e204503035074441c80155004080161900034940c41c180010b03013581c2c03551003514006001661403200160007420142650418020740914451090342000180b4050740100000d803281d0313441c5420a5500c80034407048600c3c8000710040179104400c40d00c0c03246800b071411080a00e0032144070203c3e0800160244c0d03641c60042a60b8240d403c00904981e1541c1d4070181c446035031580d82d500303031f0307451f81c450584501404841016005250030100e0106440a21f0444c84d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 81237609 1250 81236359 81236383
    0x14280908010b0a090e010b12010b010807050f0d0c030b0618040606021212060a05060705010507090e2512060311120604080a080c0d060821130303030915060e090f 71
    0x204841424409400c00030403201724084903940d0703145031000740794841310700d000d800220800001801004940000d080010003c00340c030204641000603c01d000c8241003580c1074021600000200c01c01c9682d000c0d8000c00407401d00c241c2c8180c3c01314124900746000c4448110700301c41074a090018a5482406071781d0b030513072081510030300481881104500300c1500b840650024005140320111543c46011030102c0c0d0115900769030030b94413581000301043d04102c41500412814001030f14610f081080358010a2588128090b4a6480c1e11030b012202c2c820341a102031100b41003400c0222030707601c0c0b42c6002900b0344481c0450080282e289055854200450340501c1035400022140c0b80448044044405900061003100911014051119240c295105810290410400500412141403003102c00310f00281c28580348007004110042201840c0030707209045035814240890148003d1030030007440c070030250121156501c0c294000507c100301460300350080100005a4440d103203180005501c0e11514540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 81238859 1250 81237609 81237619
    0x221090c01030b0f06040b0307020111040303170a1d03070b010506090a050d0804080d03020c010b100921080a0503010510030b0f060c1e07050a06110604020114280908010b 75
    0x1103194000d0300000d122850003016410742c0d40809000940c02c0e0000d41140c0c1c817022011040005071070302403054804180040750441d0a1078596170740140f403180f04d143d01c02042c001c20310224000b81380756008895a6036031030800800e040001000941e0700c2e041a10140d80707940b250400061542458412100f4a0b1005000038802605107010f00500307040039007089881c00420480002c122409004900c5200b0f600d9502590319840f40e001e040c20742c0c0d40b00b9103c070f100c0e100c80c07211000c40c2c0350000501001c42c0c83e403841c1842400c074481a001c4d00d80c0341090014211600000308a01c2c929401401141a2282140d000c0748501340315030110200c481d4200070f990401074200d0034640f1441c0145c00b03440704126160844200110454420001c003900b270b0320b5900294007018081c400703481c0c0451213030041d04444c6410713200382d81a0140680d44442c082e00280c18010102060300d0042c1a6008480c8030030441f500c14201c44411186000c4190210f005110004214034004104c03030b003040c001d0000032000105 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 81240109 1250 81238859 81238873
    0x609130203040302120d0204030c0b031303030c020a0f0503040509180a0605060d0f03020f0c030d0207050405060d0f08130b0702060703210c050c0f070e0117011e022109 74
    0x1505a0095102800542c00d40c42215118806070300614000c04101d1440f183c0503886510718500651010000c0c0c001800c1e5010601c100140300c41c4078480c1984070383d00b501d004203100000c0001a42000b83c400300c00b4001c140000e100b0014010300000a2080302c5003039620041d10741d02c03040d02d800c3e200c513840301400700ba0300907200341d2011074070541115400020080c5408403459450707a5003400340c0040e800c12805604100d8034543d0240e414844040041400c2e00075105034007055500a403a0016801414440c6a036071001ca403140d100c1d9440c0b19651070748240414020703c502c0c100002540c219580012101e12901c0b00401c802026100b91a1183d0740502900e083c00340c43e81c0c06461123955010760b4000040c282d01c801ca1640007d000b10600f105564030740d0395807031004604103814024000042c0300705601c021020000710a6030170700e150455000e09814200e00108408981c09000425812030380c171800d4940309080610103500410150090012101c2c5444618404616841c0c0498150700140c0000f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 81241359 1250 81240109 81240139
    0x304030203070b0703030f05090105090105010504050702030a0c0809060f0d0605030a0b04020108040f050105070302040305011104080a030f0207030b16021908030109021602090a150f1406071a0408090f0609 90
    0x18029180703517803090a010a28480c0707502c0c140100c460890340140c1c00ea4644007403110000c0d080c4221805410255002d00c014540404040d54078421182e003401080b900d820020240030a4406880340017000074903042c2d59282c400c00201d0550403030b0141c03401c02440c0c280d00052a250000b620038040f5841507591616a56030f40042d07484440090080d01d0a00340d032425040000c030b0a01c1a91301c42c40c42524010380320b6007181800b500311890310120000c003003810003007800b00480014204107103903071501d01307070010180303014049092042aa200802581e0400f080c0543c10390b954510704404a150341c2100d400310480000348401721031510000c0c01890b020401800403c00e07640050103483c102c841d50034425012680401d454560841d05652807560741c0c0c10701c1104403400c12a00e0020051034a01400c01401c001c4280d410031980e042d101d11070000001d2140420503482304d003110741c5c04c401102511510301410f00701500c2c3d100005da0b0340b044000310025140c514003c0c0903170fa20b52402501d2582100084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 81242609 1250 81241359 81241379
    0xd0b0a06110d080a0e15010f090204030b06210601090b1807270302090108010c0809070803040b0306040905010c090305010e03040605190e0d080d060501030501050d020409031103071b08030403020307 87
    0x25155a035182d841744500d84120703000b04816001c42084680c448051f601d46000c0362880c0c4815044030340b0581c0100700800c0400c00d074200302c503000b0404450b40710901001030100300f000304001032001c8046c06000d0000030f102496501c440000101030322007802520380c0207840341e1010b030215124400b08840c00300d0f003114084100c1e42181c0f401d0350413aa6011941d12030b00007400c908401da22203100b0369100d00d50000c940d90300c5001503030085103040082c54800c0c100b41081d616402280520790703003614048000703916540d541e0010880c19400000801c015196803400401c192107e000070340b6190b0a2640603c0c100c000001160700320750980d50384904100c50050002d804050805000081086800c3d4440b4580c2e983c0c010f443c001846592002e50711200c00b21054241e0307819621880c1414940401044070f03440c2c0b000100708080c0c0c101c0700002c4150403807405072100710b4214180f220b1844007103142c10070004c01c0841c208440170304d5400c01038156600c1180c0d03507a0f84250b0000a4064000d148204010209 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 81243859 1250 81242609 81242611
    0xf07060905031b030405030d0207031a1b0d0507021b0d0b06040608030f0a030e010c0f0315080106060215090606011b0507090f060510020a02060306061b030d0b0a06110d08 75
    0x2041c0309891401800d81d96400250320b20a50741480c03a00f0028080055103820050b42c09042c5503400a403034800d295860742400f40320491901c081841c805c1d80041c407240241030760b400c048400b080d40545c4036655140311354010007044401c03402610a00c50034103590b11000001040d0100d006125030500441c07035640d626000070181c041500305848030000705040070140082d040c920803210303120f61a1881c802c00101516036400ba03403145645080c02d41c0b00010390141e0603a035841100d0901045500d40c9680c0180340d2101a400b01219519201e004070300540c2c042512001c42000c0580c0040e1505e40c0b0002607210b99058800b140821034580340c000c1e100204100b002c03040b50054042d50704080c2d0b039480d080165100e0400074241a5640d10050145250411a86610807100c2c80140750152702940481c445220240c410b0f889000081500c2881c3d0076404d10812450b84032900f501e499114142d490005040b03400401446100909c20104005120742c014081c1c8170022001040c80c5440c103581912810f038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 81245109 1250 81243859 81243863
    0x5070204110d05040201090603050903190507020928020c0a02010f0908060f07080a0506030604080c0a05030d0e070812120604061d010812090303090f01020106030209040b0601080109020f070609 85
    0x80c9482809021103000300c0074000c00b00002902059070700c0c0a100040031a08a50481030a240c81c00d01070000c5d115002055401072448188000314661800e0700541d411300402000070742c000481010482c0c289900c0c1c6110032000340c81c42d9080c003030304200e800f400164012020498000e510030704903000558030031000c2150003041c0d41001030081e030321108194100324046401103565100b0a0500240302e038003010040d44800c0040080219090040009441729000790014200d281c02090441c503a150038006010484e502c1000c42e81c3e42c580400c0300d84c0280050190042039070180c3d00e8005000b070404294007108107001d0045504c0d1240c1c0780605040701d8005002c44c0c0c0c0043d0b0321403020424071554040c0100910007650041000c0d8508401549400d001c0542c208500c00d0a0040c4d2a45840c00016a200900102d0342c40c201d5510400040307004005c25400658060b1500050000b84000c020302240109002c2c6e0340c02006a0721104154140d100d501403109190340200000d8000c00c0b441c0e8044c000480c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 81246359 1250 81245109 81245111
    0xd020f0312130c030308060102060f060d0228060207050a0603020301050a0b0c150403110f0106050a0302010c050c100c1b0605030109091106031906080a0c0b0c010209030316020f040b0303030705070204 88
    0x2071500d031100f0194084a03081280426407800c10700c929580c0410110394400b10401c0c56542a1130000c0200310621942d030030003401000c01010030304241c100c040151039034060441aa404259507000c009560b001c6ca4800c0b0341c000d5403104004275201d0300c05e0086030b060320b03006040c00b070304545003c07103000d0940d020594080d580d004a4401c040d042c49001029800b0b14020b40c1e030780c21b1707484040c0802800c04144400c41c541e960701d03060342000107403141080c2c079017244d0702420300841c2c000702401c145050100000420b40d108440c00811907130b4541000920072043c1c0244505c3c0d4040000d44281c5004003c01d00464010a8080c4010800e150594000c000100c1c0b1544111503420610000301d0065042a201810800c08460741c2045003003c0340300304c0700142005c100500c182c42e009d440d21403010310355020b40e4141150003d290a00d01800750115140410094103c03555400c045003205c0e039004020350220301c41d4034003001456071494180118330700840000c000d9459600c40b84000d40303c50340003950481c0c101d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 81247609 1250 81246359 81246391
    0xc1507051603030f1a0a05010c020102070503062d0702060c0702030a0b01030b190207020904030320160303060524031003020d050a170a0509041104050402031501020d020f0312 77
    0x2030907103400c92104562281c1c4001c502e0349145100d0b00243e8041c0b807500d00c000b80010b900300401d83e07a0f03e035500048440c03c0c02c00141c10102400106e041000c190002e9070540300c0d0301c080c0034041040784031000402000d101c0144020501c40c0c00511003420655072440141e0051003c5846407911000901170107100a04580400c1402e0b9901002c2c94400d070710503a4000401070801245c14030040480c2c0c1954510141149803a046500050310f00d0006170001d000c0507a14004416081c10020003150000c110f074445c640c581c50b1151b204d0100c00fa0340312007180040d0800c03000003107508150350000c0c404901107129114446003070107070a01507040113000003451190400c0000160329200c4100306018002c1d0050400501c560404420b10710389110001d6688808002107119603a100c82581c4d071f031010032240480c500d1103410800f615030003560445a84148000181320319042451803908804400fa000e41e41410109001a80c64074481d07211500303a504100041c00b40690041425039121301c203040d0303c82c80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 81248859 1250 81247609 81247627
    0xf1003050f070f060c15050901060308030f0403030b010e0102030a030e030d110403061a0a090506060d051602070509011d10210b01140a0b0705011d0d12020c150705 72
    0x1420280c0c804805075504041010b114162982d24114058011810944208170503641c8400c172240e0000801035142e60f4410100c0c1c01c0020a4200e080216003019030360f034503418030406403d0001010b41e03040f004a4540f8000a40d2540186000110100c0503000f66003002441c1c00c2c190054480d0148c1e0b8002c40c0020030182c40a02c3d03a501ca07001d02c1490003c0c110b6201d5055160500840c0c20561243e01e410b0b0400844522640d070300c0b010b54080e680d0030a004a00c545036000402e03440d0245804507035001341060100004001e25501400303107102650308803407009030b60b4800e00890003030038021034404040c1d10a1007105880300c0100650804140240a46142d07038444d058440d1181d4000000500c80c00020440c040c455802a11030140200400480a02080000090850f00684101c241c010701c046945403d1141c00c1d8404c180b2440780c040c400d1140a89044003036150b4041b4400c00c0f011545161070032003980c0240c400d50303100e03162071401410070300300c1c5503090740118000400e000704014081100310360b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 81250109 1250 81248859 81248863
    0x1805061206092512140a1e03090803040b09120102070501020706020702180c0307110a15090c06030209010903030c081e040501020d03050f220507090203150d0203100c12020f09030c0102030c060f100305 88
    0x12078403110840100c0e884107d4a401800c1068940c01200c2c15031080c441888a20500411222101403c0f15800f00448108070041d01a000319000a040303275101142c13503400c2c44042e4000300802d500c2120a1030301058020f640100000c008d07540414601d03002e20005d00710034003600300141c4c41c09084044400e08034199a510042510307a0100850160f114006001000646d82d8220054000e5003070550500c0e010300002043c050342071101604000d000421481448810301c02c482007203403202c1c041d01d02e00c040d4034a825010390151080b00e005119905081e0615403280c480c07075004490505200701c107600c4008500d0b06c040000c0e031070b41c15421480700322034001032002c2003400014060080003680707a1a22007014804d0315156513540d80159040f13248440140d80c040341000d42c8030420840080e0580e194081100c2003010385c0002c0c51210710000311342e03402c00c00c0403025140800040301140c601031070f43c4004a13103d0258480c3c85400e9400030000c02e54071481d0705e000301d9010303c520304a0134501340e40303444481c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 81251359 1250 81250109 81250133
    0x110a1b05030a230d050f25031112090f06090103061203020106030b0c16120509040608060103170f040306090201050d0609150f1805061206092512140a 66
    0x16014900d07943d180d41000d851104448680381e100e00903020100c10088040d100d0310071103e0209080f03030001489201350203104c0c0008007400c242c51141c01156154a0050000c000c126118600c92040750002440c2d5640441114000d100207040c039200d4140d0310043c48002c2e0002401d00341890380362000821200c54550504010328040d500100b1484d245080c400070a080c013804140b050802000300c0d0032005a840300031442c0356070000c1d4025180352400e9049500c0d00540300300540c40303400c00c0000140c0e0a000541241624041c1c4031120b070008007405d003160342e4401e89007404c3d8001c20501c010000300f10136078410b83e14280113050042c50981205612012101d603a0810380d05180c0d9000b0301c0202400c0c0c440424090003016184202c0182407000703079148001601044401252100300084054032030a40b43c1c9134005042003115078a04000100381d498050701d4011040b002e820020000e0040490320304c5004456008400710003840d565109e10030030b0000702e01003050500c04c1032045000101041000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 81252609 1250 81251359 81251363
    0x4030204021617040e16020a170403030908030702210304090906050a0f0c09090c090504050a0606121104060804020d0f320c0906030703150b10110a1b05030a 69
    0x506510a002d1804410f0000c00d0034401200e00c2c0e00b440180114050360784c07226040480402601e200090300c9500b21310b01341d441c07180200b0140380951800c0104140101402c1600d202e80c5580101944031307840151340e03003d04040a9845034000085c070640c07954651400d504010800b051b41d00e03103912032030050140c406201d803c8840c140d0390010441e100c0000d1140c0b050101c000300302404040d0500d1002803078500d030f5002d0f2003140e540d900721858119002d545170500801c006841030000e131809520351070080410b441440c010034201206408505828400d83c80c0010080d031b00a410310741028411111417a0040c000c0307030019204594140420b0101c06040384262003285524071040300c0051400350150010407451b000c0c041e401d480e07280d681000c203000440060039900303511196182c1c0c0020b071030321400c5d51025000008a003009241c100550700140800c00064800c0c40e580c0d071200004403500721800210b04015082060a10006000108252400c0b40c1000305841d4090320786c000a4108412a081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 81253859 1250 81252609 81252637
    0x30405030c010c091401030c081518090102070201030605030703151503080706060f12050a0803040f120804020a050d0b0615040b04080717060106050f03041a010602150a0605060403060b060403020402 87
    0x108109081045014080b004c8080c40e05114101d442500278010440240001540c050191000b00c480c1c0c4424509101034045884034002e141030400c00c1500035404100d044c6d00003420135001040f98100024440201d9510119151035000f070340c4819401403282140d91814001d041c0790000200c1c2c1c0d03010107004058019000050b4982c0341c015040c0001ca110b501518000000d852624040380f004244c1c1d41c0d01e01d4001400b555260b49910700150802c1013000c0c01400c3c00000d030842c0701c01e59030180d06248518825030b0f0f034000083c0c0700d80421160000f070140081c40881954006221800d1040d003c150200790f09085a0405480c1d1040543c1d640154020f503100d07a016240412a1302c0b40304d06020010008a03000d0710140d418081c0050862080d142d0302da00d080d400101280130456491024151099030b05d54220f0156100c0400a444450107400d685031801d600c404641103110522500c4103c82c001400c0c240f401c0e00d15503805001d4403080f513404d035005505220020250300c85000070040280e440d40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 81255109 1250 81253859 81253877
    0x40305030c011a0102030a05130e011701050a02030c090409020d15020a1d1c030509040216060b010906081315050702010c1202071101030b0d0f0501020c1509030f030405030c010c 78
    0x5007500310b8002030b070140d9003900103903904103250760080100c0714043c6092805a5944500ca0000654805954442002d040d1404000180314086040c040b9900703148200a1169445450503030069000c01d655100e452a010807091510707141039401001c0381c0d4801751103512000380a0f1031f5001d51881224900015580000d11720481c240d00002101002101484650b039485002010409502c4010107070030000c40d00c003040c40705240c080e03415194481e00043c0150740d1014040f440c1c00c401000c003401160110308141d2610000e601038000403003030b100c895842600c2a50352483c2d040c4d0201242909440312002c80400c036a80d00c00c2c1d40109481400d40780c00114514019400040040390b1004a500b0124414802517002451110891071341c1c8600346800305000c01c803440091541c03030311858014151183c450280c010010103402910f45401740c4402e58514200c48902d24940b60000c0312071100d9500200204450300c0c1c0450091600240982e0403a400c200007882200c2c00c4035808181a0081890300c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 81256359 1250 81255109 81255127
    0x20030c030114010309061e0c022109010903050f0705041a1008150d0b040b0609010b0a0e06120f01210203060406021b120301090f0b090a0c030209030d090305060105010203040305060a09030c0804030503 88
    0x80506d0305840564401414ae011380a41c508000e0050401910646040010004030580c41040e5030009150010107845e0058094038526680d03100c64441c3c103000300d0600342c60b0190006d003070300e40008110001e40580b0505418250840303107504000c0c40204a00c85892245480d500c07041e40c04203d43e0710503c8104c00c2814541000c11800400074110743c450000300d0010311051040c4000d0f106c0303d0030241440388082c580c4e240002d0260064260101341c100b0300202b005002da0019100604a8207003a10b8041030a16828154061038034031500650540d0056020400043d15503000300090030102c0004507440301d0f41d800603820507840d40c428500d07584010005005a9085108043c0101d0381d00f00c041005c48d000c5070100d80c9212005042d012070b80d50f01c119450701140030703804482d2841001401d8602c00e000b21100600b908641d404180c4062181c40700200b5030354000412541641d030400020301030ba60342d10082c8400b60004402c1241001004500213002804c01d030060009540b140d00619101e0400c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 81257609 1250 81256359 81256361
    0x5060a0504110406110a12020615010201060807050105030c1207120e010902100f1e030213050a030f020d080702060406080a050f0106120e030c0a030320030c030114010309061e 77
    0x16410007440303149041c56070b4a000b10b803982101c003102d0103803e0148001d05035a22150038a07001c508080c160440c42081005840e0b40485c040d40f00c0d40e95959454003140b010f200482c2284c0b194001c0e501103510240050106601407000b031340e80040005851480c00c0e85444451050310740079185403000c505c801410fa64101958080d001454801800800800c403280e00003a004c044101c050f0010300c00c0a22007003441c075100e1010384c000303400800c088890490445c80b00800951104103084500b140c03030040450036148c6030703219104881e007008508016180c1a02044803003921008100c612620400c000c0d0016200e4001400c0107140c542c55449403803a060210f101075640041c1480204d950240050019a40140d0b10841200d034510b0300158100319048602d207103109075214485588641d03d124420540c0c55000b0354101e88030300030f030500c6c02254080b003854240401d5602c0c2111280c1440140b0282110404c8c2195001051602054444081d142d26049400d036004002c11140c45200b080a44845 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 81258859 1250 81257609 81257629
    0xc0806010210090b04020d02011101050916080f03191106040c051315090203060301090501060b0703031104150c020105040506030a0501051002031e09040908030901090c0e0c070210210506 82
    0x501905108006455551520000d0005d00091051101844080669100e100481150040b02c8002c002c28103204844503601c03006074443c40700e811103610020800c0f841c081040d04074000103000940c10301c04030380d441a07072030900790003800200311904010321400c0b2020040107005500940d01c01580d0350607c0705000d0403106042d4168001402c000d0381c41036211544c083e00c0100e619040300162281c65442c0000d001d000052005000c0b50308001e80800c686130044018022107100f91002c10180c81341b414440d40030b004920a8141c09015440101d0700640514440b224540c814544249000e8480300080d00d02c2e0010b40c0d2102c4960b80da0350050042c6d0030501891180380d80b080c0015800d01400c1c3c442035100d500e44829901d1240c5012510980b1b41d280c0350080141d44e6444183e203901ca1501c5d414250007081c00041c140e5089105c4900041c0d2400324002103401030420a691502d000700396000d0146960f00089138100300990002140900449819003807800d070325400c408115400c040c0100203080b20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 81260109 1250 81258859 81258883
    0x102070b0a0c03080411060a050d050f06180621100605040605220908040e0906060901060c03081b0414040b03010228021c08040302060f06091807090c08060102 70
    0x1040155054050300b2140d1620090f600d80b50499040d0713180c1c6041002c4600c1242040d406c0780b000b284002400c0e0f0440050100c1c640315041c100925074070419400f0041c5802d840302034200540d480d81c154481c0c41c103420342d0340c4410083c00000706040440d0a5180000164039020800e4105048100001c000c60265400138101250140451410302c0c00040b0b1417403101d40b030404100c16141084800c801d464120302c80e141d411000403522035640b103800c441200c90441e81601d080c0116000103840c1e10701242c80c54140c403045e90f2402c4030120300365000e84207554042c2c002086146005100d40080110720000c4c00640f0325030b0403080640c6c513a03600b40001d0340c101503083e610990060041400040d260181d0b0200e6107484600c02c044034030006800d0b400c11603804d01004c95081c071103101d0043d10782c005e00e129029500c203908650740303607903500120001804241ca001c1c1d409143d440100d90042018823110384401c42c0708042e03070f4020340d48800c41c50868180b8181c48004c280000104281c0b90703014441982804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 81261359 1250 81260109 81260129
    0xa03050f0619090902040f060f030308090a0809010507020f0a03152a0c02061210030b150d020103050601110f0f0c0102060106020d140405120610050d02010c061a031605010207 77
    0xc0003542006045602c5400341c1410f041d602c2c580c80c0700b5940c07581c00c000c15440d44d00e0420000e5580302e1101404d0100d4901003a00841c103984040b4022000005580800942001c40241081c3f10240111140d6101e03a400781e0380901d840c0c00c01242c95071000540d02c001c40c807031000c803040b010940000c0e0041d964401041e04036460a01c60780c100d440d46131100b510300340020b031400b4000036200b440084c044d8014400d00d6800b1070347d1201081211155582c030481981e01a1440310401c0c1e5440749244021000054515000041c0707954460055020307801c00707034000e403050601232945959603c0c000d03d402e2080b0801c05060740811812000e00300d00b40043d0382040b100303201034040f560410802a50307441c0c40a143d0800c000364194100707540e10011040e82c0c050640145030f4580000e5002e4540d90760441565001d1855600c003900040601d08480301200d5268182c642c1f0340302038560b03220034004000c848031440d1004408084003100303940910800c0007580d80150f14040190800740024600200b40c1c201c05061 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 81262609 1250 81261359 81261379
    0x40918150e07031211030f0715090203030d090521120a060b04060c06111602011202030720010921020f0d09030b06220b010e0a0317030403050f0a03050f06 68
    0x1c1e0a02251400580ea08190354986580890701c0440d503504040f44215598007020032402000702c44c48004017140390103280001d50103240707901c12108489080c40000d60590041080040c02c0180e40c02807040c072400740047e00c071903079100f03880a00700d010082503110a44000103070038100c4000c0310100c103411080c01d000c1000440d04019040d512031003a4064002400941343c10700e000c20002d03030004103003c40d503d900c0944911945140396400000030b40100d000c41c0c0c440100d62480c0b003051080e2846403401d41d40d1110030502070403084003000c0d4940324080d469521076948501107804c07520024050440514110320744050440b00a0a1401801040316250042d0041800d10340c0d00440c0306040c1c94101000d5106601c9040000305a00c1c820814030132101c1c0c540a84078486c6149a01c0500d04070800e0f04c2d515034101400702081603200107130200a01401480c0e81072511b4040340e5000d140d11920070b0030940e143c20101030030240140c106103840f4001030786034020045170310308000b40b05402c600706a43c01050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 81263859 1250 81262609 81262631
    0x60b04140d1b0e010e09031e04030c0b03060103051509011e0504060e0f0f0601020c042a0906020106050d02060d020c1501030b07031a0d021012020c030a030c1404030201030c0504091815 81
    0xe0340b080c0512062041c81501c050643c0384060f2044030019680102d2010031103035112003300c0c00d034000b1520140403c0c84c1800080c1c81300c410300c0c1010b02000000300081803980c240b00d0240f11440340011403981040c50703691302043c5600d42c2c5c03288202034a2041d140c0740700c0303140415555401d000c004144c4214040c44000340b24460b41c00144024071542c00f2900451401c411001012010a89480c080c47c080702c0d0a4004501540000341d45096440e2039000f03011080d11541407180c941d101307000003504a1000c0000c66001c1c1d99650203060005c800c0415580c1c85505c0381c01c0c0d500310420a0f04181d49a514070403d21042540521400c521200d62500511039166450000780204410700d201030f00036044218040794251180304801488801250304540b1a010440425603d82000c10210003082c64040b8030f0742d1403809004122001605020064903150856004401030445403001105100041c4804207a40e0b90601640c0c80441000619102e07542450602c41c008038015840180c08915040318440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 81265109 1250 81263859 81263863
    0x1052502100506060d02070f02010e030d0903080c16080708010c030504110f1f0305010510020708030d0b0301110c0a030201050606210903070c06020a030210060b04140d1b0e010e09 79
    0x9000a407510004a50b40c03030b4800300314030780725211105907507a100103250420070180303c1551200c68000c1e43c0701601b41032807405055441002c03501440210b0111402000001c50060081ca01507071940259000c081c40548205c001c142e01d6004200503801c495000c2c440000c00b4801d060382482945014442800e280d200c4030403d0041442d458080c805ca04120005621600c1b00c01d0001051010003040000101c44000e009210a00500e446000490040b200f81031000441e8030581d078003040950324041521428a00804c000e940340b035015521032400b15600c014510140c0080104c4d4405040c81783c1c50b0303250080c21190010172540c8121024040903140f1948108902404104c45d54025015110408441d165001d1040014501620f449020070b4955010404204040c4203408403411141c00c0040042510a580201c90300d03154140401c001205040c0c543c3d0784001c002400c02001c1c000030b9162504401c0c2190b000190351036000c52700b04000d0022107006801401c3c000300340e51050400003c055 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 81266359 1250 81265109 81265123
    0x9050901060302070303090b0703020c070803030f07080406060308070c06080a0e12090f09040503070311010203060904060b0d02090a05160c050601050904031b03030609050702060921120901052502 86
    0x2400b055070201d90350041601a6100c1790b1466007103d01c051952034543c0006001e0751101c00086994041e0107000100544000245d0b030150310b0041c2c02000c00ea40340c60049480181c010000c0d01d80c17136240c40c00000480c10840062910700d009000c1da81e100d40c1445c0000c9d00c50f44024001c0e08000e80b602c4003210030700303002064aa40d10040810340560703c1d50b1020004442074040342c101c0342d009240c101440b00b0403100100500a181c03080d2680c0c0d10f1840c02c1c0701e0352400c03030004030745054000b00003200040c00103040c0e5200c0e04400c403008140032805a026008220044030403100c0084056542c8148140e40b2888000005500070602c1c1c611070344d0743c007561525221072041c85410301400b1494080390405014205040c1207100d02c00c1414034041140c00e009000c1c100c00e116401c0c9280c601004a62810310100302184640960700050a01b030181040c6000d0307a03046100075142c0f030f54003400850b100b040c9035480c2d2802110000008107103414809443c0340b400c3d28550501e5440805d0f1081d088034107070007140340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 81267609 1250 81266359 81266369
    0x80606030703120909150806070c0309120f05060f0106080c0702060f09031903031a0402160f03180e10090221040f020604030302030a11030301060507060e0c0405040c090c09050901 79
    0x451042c4100d4142d50596181e04202a174909040c03e1129052031841c0b080b00710351405c802c4442584500c038007918006503141001e400110110710512000c0b14001d410040d0380c1c82005140110842c940f034540c10f0020503900d92031910203c3e001000003991140d01c46e0342104c00f64521603d0029543d000860030300c5105040100c1c280e0100700c0e0311f003507541840720f106180c06804007001e0502ca540740080041807441110702109001068800e2507040034829100121110450442d81d141103031100c100c22061321008030100300008240c0c0c101209290101d10040c003500b000c1d402c40d8180400307449072702646500001c66451041c011202540d035a980500010603041c40d00380c00302c0c0c56905204003e41c40a003070182d00f0170000a400810141c1c004000d05030100d8079902c500c0b180400d08401500d0303210a00c40c61001410611208000c20312540c82841508480002c407820010303100f0110f01602c104032420f907520712069004229064050190055506c43c502d000500c031814030000070800e20040c003807 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 81268859 1250 81267609 81267623
    0xc100204060c0201081008070b130e15090a0b0a080a05010e0a0809100c0f0c09050610120b1201050408091005041511011e0501050310200c03250c080606030703 70
    0x41658940010078600c0503007d5002500c15654541c0402d60459100040b4030403581215400000c2c030044aa210a004e4140c0c41001d480320410f03c0d04020502c5005008003d2241d500c10203440280c2da0400180300408000c40038000542d214200b4038212a80c3e0094459039800817100071000920300001c0303a032201402c0341c0b051480d40c00110100d800107040d0200070000c0703000b20000024010400d0b21031003150200c2c0000d000e241d440f4800e0090103440c01d20600c003c41c085036070b076036020003103900709420f001c80c05421203c8500c100b42d0020300b91035003500c00340c3d80128000707040180d07800c207000c080340e01380006c1c14141c4c641031505a0313070040107000f14140c408002c0020901d41d4213a00c01c1d0854202d0400d01d00405012100005002c40186028480c0381d100c0e204101d42400c0024050141c0100c0745c0c102c40740c9441c00398554030b010a407540401d5482e01140400c001a1440c45030a40700c4450401986a030240340798058500742c40d40c000c141e0050500340d4000303070070030550b50360008090040d281c0c4512 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 81270109 1250 81268859 81268861
    0xc0e1504050f0919180b010503190809040b03120403030f0804050303070e061209010507091d06060d090c03081c0b0d0f030e030f0c040617060a15090207080c100204060c020108 77
    0x4c5844441d44c50144d03161200340c00c0601d0740b003824019100e04696103000e944c0c1c42920fa40d82d20200741c1e0700c05106100e440140c846403140c0001c81c5400f009850000e20107080851031000b03620000c0c0c202041d020b8081460700d000704091061561002d9031144000c590304007120305060035200c165076800014004d0080200d0510b0714012034541d0415995a0201d20300e0185007401c00c0e01549003c0d100482e1030308009600d011000800fa030050503c0c4615020321041410035841d00343c03c3c085254080d2030881748194440e111440040d210b803041400560007490351a85644541103a1440400c015407026104e504001c00c0010655a0b0b01c1e200710300c20303445404a448021710313103400d503510710030100b42d280e01d03000d00b40080288040100d101c1031240d208803030400c0fa160715030005107280a0000c0084a09500071800070390803010fa039000c20302c1c071500111160301265680c1050000d1380e000c04800c60f4142c00200b85501d400700d00b008081c4541c00300b100203500302802d1100082a2100401c4040d0400c071f2440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 81271359 1250 81270109 81270121
    0x3080c01060b0d021c05100611070305030318100b100c0606090608010605120109050604020603100812220501120207060f05010b0304050d030c0e0402030a020d0c0e1504050f09 77
    0x548030030300610072452a0343d2030302c25004a81e4025080b400784d9018443c010115615405400d101c0c41c0d104a601c0000d0003000c604181044a0144944000c0703026840b400781e001c00400c40400285100b55001c02c000143c460000010606003912291411110380c00d103103a176003841d84c503141080d11400305450800d103509010b0400c40050316859001ca10f07243d15185001c64000b006400a005888084c0e07400b00c800c50440c0c09003400c8a2040034080c1240d0402ca000c40c006150850086400000b034000c88103825450720401d40c10000030058565140d4400155030701c902e110580c0880352450600c080d00700c803902d80303400a000291100c4200c5d41881d4001001b0b003c000859005060142c1501d500b00b04d0b940e1640004012a0320a03102540e040c03107a1003458465520030f0050090407181030340e80400f81c24208060001030b402c0600502c000c540c00f400008581006031268007010161507480210061448044c06400c041c009407551782030764100018070040d02c81090140e6000d81c02e551040c8966509 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 81272609 1250 81271359 81271361
    0xf030f21050108150112080306180709030b0609090d0305070c0c0e070e0316030209040624150504060804080a05040816050f0103050103050a0f06060b1216051303080c01 74
    0x3882030a00c4492129005298480300c036070105069503090030494010075243c0f1500c010242c0c09110398400315412070410320004010b040a95017021025041d8051441c1e5413898220048040b01d040300000c40400040090004680b04603400c2a8240d54800060a01515050b180e120082e944c100307054658011820580c46041801001a0403218201d004c17501ea004228540b901078550300000790750000f00f0a0503107400718040032200818842c0010047c40c0d9400d10aa880004109480c031076654103001110100c0c40b4291140a00d2400c4500c4440381000724500640440f00c8407207041080601080c0001500b1408680c0c10503003047d02d141e2a40703c1e550088840f441280c01c03075400b41c003800c0e43c0301081348080c01d200402d41d02c0c1112900820410305004408840092101070883d5000a1040001c224420503e81a130b9000d8030002c1903c07612241e0014099000b001003110200c83c04040085809403028040541c0b0301e0b07441c0c0649800c0c420303111140220020300000d4030080740010700c4661400300f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 81273859 1250 81272609 81272627
    0xb0901020d1808010e0c130c02060a051306020f0a030e03090a1205120406020d03060e0c031302150f0912060408072a0b0406030b0907050f0903031b011b0c0f030f 71
    0x1250340240104001c030300c00c03175444025000d40c0d18000c5420207200e0071090014005d0294030303600c40c0e00820a60b079601040802a1001921428000041d62501d101080c083e00080c01604d40c0c0103c081d5135110f10100080031910610300d41002500b041c0070702c0c206651102c0d585001c64058003101d14900003541840d0f41004961026080090000039000400b59004103031300e01a00c009490400c981c0703668210185e980a400c4482c0140c0ca07008000045804101c2803440c0f2840b800902003401c030100c5a62080c00c140e0060ba401c000d1480041088001440c0110081a03022002d0b0003820490400369507007005806400380007002040000420b004640c00c003004a038107084250170401c1c10a59a1001101130b9000d0b0040500203414000700389868103018583c0313801016569180e61502c000c4680031280c6420045016625000401c5000420a200440161803604140001132a07541000000020501c580c00e80c0e400d208101d44048040340403003261004c00e030741506043d0548400b05a00b00c48540c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 81275109 1250 81273859 81273869
    0x6070306050a2c01030506011a040806010504020c1c030203180c030a080a050d090305120c0c0606150c0a1a01080a0b070806040615020a050f070b07060b04060f0b130b0901020d18 78
    0x40310f00000090043c0003451504079061010031514211182420708594461402507984941c41400100b0860419500601c1100b843c40103540d00d00e12040c16100320300304030521a00c00250003000780041c41602c0e0725207103412040c000040a01c512001c01003900e420301d07050068000c20f80802c103841002d0142c01264a011410a802c00c501c2c12145009000e0f0b07044402109440d050b46000101a40003001c11684403c146400505080c0e0700c4404210700e1042040c1100d4400364248084c03030520307108002401c00188204001e00c41613000400e00152401c0581c44110036501c181d0124000c40c401c82110b0b60002d90a24140f40c0e542e4038480401c01070925944502c0d2040351090500c03c0c1741e40c2c00318414010031300c0782d000c0c0c030607544035aa021a40d901c100c3c0900b2000d02c9080020744000340c05548807203501c800180002c119250391307640583c0900ca031603000f612120000111000907112030020540a001c0308180340e814801c00000003583c4085441d0500144440c2030b5950350b45484108074500206 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 81276359 1250 81275109 81275189
    0x30f1a01060201050103060b010c03020a140708030a0e1e061b190303150f05010207091d0f0d080a0618020a0c05030a0201021803061b1803010908090306070306050a 72
    0x25035501c80080c02030600b480152146403600040400c290301c2804285402034045c0d0080c69000c840d41c8a000500300d414107806a01e1003919800078070100c09201805556170143c84804000d41c106060081c01c545c0c0306d04042c2031004c0f08600b01e0032a5138101c00e8480c1510350282c0d4110310a5110b03406450aa1000c0e554a941c80c6144821020551b04d900240d03013200b54031003400340080d66400c04840c06140d500559001da040342906000790556523005031020542ea60802001d0b00c044491b15082c41c0c654420301450380c004800301084030390400c0c0c0440c0c0208202804000c007510b4034050014202904a81440040d000a1038443c91440b4440090009401000360782c1c3d40c0000c084007034000d40c400c0014503481221142500081e00e004141c4620800e1354000e1041e030913600140d034400d01d034000000501d01802e060660001500e0911804000902c03c0810b00c0d62a140c060806107400b40080030380d02010b040c004e0601c60798580d074100c6c004960031203203280f07a6041030b60260001c1c0322541100b14800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 81277609 1250 81276359 81276361
    0x70807080304060f061a0c160803040503060106141b03073003090206030601030b0a03120305041403070c030b0c04050405040c03120c0c030b130f0507141207030f1a 72
    0x808080802540a2841110f08002c004031005044055800f103125036800c4119420b03028103044030400003021400c40c0c103003c0d90780c00e1820300c04c00d005a0f9665003021266600100d818003040c10200503803400745c10036003440c110044150140d8001c51240c4143d0b806440c5000d81c20b84000d039010030031307207007800d502c41c2044000d1030101e503c0e1300c0e03144604101d081c00341102c120b41c0c150160203440391702823094014280303500c1c55480c80d00640c090550300d140303160004a2a04000007154000d0400d184040c05540c0114280c141402e101200b4065001c0b8520550010815180060031501c206400c5030313480104009642c3d5001c03141d40d001c0c001c0398041500541000f082001f005000000300080d40d01c15013844031030ba4025403044a014001c5038004001e109084c07014000f003051490b8840d44a40c40803004100605155a61091900d849000319540c0c6d000410600402c6104200c00191480a40f50b08840300341d049480d50303442c1a07520000d0840c1c0c50109080302030100c0020b0324400c0540221000001d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 81278859 1250 81277609 81277613
    0x10c030903030f0c020c0906060403021206040209100e070f0306120f141204090e030412110a0e0705040e0907050411040f1a070b06040e0d0c030e09010308041a070807 73
    0x240c19010030840000e4500510340403070751010f03c1000c0f02015180c0c010402c0d0290030301488a55800507120580c00142400300000681e148410b88025803e800003505140c01d251050015110003d800d100301101004c0003400308a0f440b140e0203600001c0351405c6036030300f0682d080c01d6008004903001810351402c81d154250511181c0e4100150040c49400045007210341d2840c1c403030321003804180d11311113088100420014000e5640289041c01c80050583e46820b9450842100114042e41c0827606400c0c006031020840ca01420341100400e07203541d00908516114000809500c43ea0050140a140c1000414000321003045040d01030240603100f04800c02031002d0780c2c0c0b000d400602c210404043e990307101084103003840160500213440380b800c981c1810a241d130303010000300009120365001030392045800e85a242c100005400c035401034941809159081c140100f0700d044a14825008052210040000131441d108507001c450440d00703108411030080702829414031030b0640140103080c0104403401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 81280109 1250 81278859 81278861
    0x50402010e0406080307020a0f061b0302070b1c1a030d030c02070b0a0503010810090317090c180105010912020904030c02010c050607030510090c0c0b0705040801060e0a0509031e0a11010c03 83
    0x206c514000c40308000c91a507180c1a00411031243e00031319001650950b010741e0280519410f1320840b520a0040e10441a11000d01a0168202400c3c1507a60340c040b4484650145040c481c0c600001c54032100300503102003a07030100342e0350a20b0704c00180400d44d907548210921407003802280d01030110904116a658040300d001003040c0c00c01e02544189000d100681000c1c101d491007036502580d8140c03a83c0403103421300c072070f54800c281e4001c041314001d001e0310820a03426540c45016001c500040c51140d02503504042c00107006107099000409400e060040c0800566900c90350254000c0d0307d441c6c01051440d0340d1004890590405200405e02e114007000c1c02011609600118452000035403400e0207141d959140b03005640c1c7e98200701c40400c4040c440720021030000c910b03996024880b8202140b6040c0c2d03070103030982151080d61001c000420b01c4800e000345030030b5501602da08983d00c400210b042469113281c3c0c00c1c0744180c2c00c0801640e03a200164402030540100d40079802007c80c0303030003040410811a0050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 81281359 1250 81280109 81280117
    0x6040909030f021506060706020c340302010509151210030b060928021309050f01060825021c030e0f031c180605090d08010506030c070204050402010e04060803 70
    0x300842c005540301c1c12000d00c0001c525000041c02c02c04c03682d00d81c81d080107004070340c1c0c000c2c0801e0380d01075002c212110f80b901d0700300400320103000b1458454041607042c40c0300d06000720761504038100801840d401040541c0e03105041eaa040300c011a0b09624041e00d1a400000314822048a90a4003030032400700940090340ca64000c0c04c50b40510081d2200f42d85d910f0410400c0a8112038900807803860440c0030b03040b040c2001110440446078500141380c0340306a13514644001190380241d125503181c0040000c080b06031038072507004000c981170818140c10404448410840d460880b01050080586011141c92081002801405501003240030320b61296200074080c0003110b807011580c1c0724540c05075240c10b10000407140001d4029940c4405401020822000f41001c05030560722001510a2503001c50300328419103004a2041c0010100b03541103101c050090001640118071a00c8107000704040240c0f40e00c200c0701081d904403000152580c03103200581d040707054092016003091504101040c2c0ca01c3c004014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 81282609 1250 81281359 81281363
    0x4020409060b0d050709061e0c05100f0f020414060f0702041404050105091204050f1504060305071d0d060902120a0c0801110c0d08070c050f0106090c0201050403020604140c06040909 80
    0x10704c000c1d9030740c0e4400d8a20702503502c41d041c001208402c0d058a0940002034002440180b4648200d4a01c500c0c3c403428035004003100c0c000410340d5200340d20039030240e180c0309400b0244803484043d410a807821042c03072600c584818049000c0c1da40015040c04170910380b001c5856056008108020b45050740d508040003180455080301ca661902020403900d00d40040ca10b0b1400c3c14001007545003e0501c4240841440810b00480c2c009020b203910301481e81d00e03803000c2c1001d41041e0364001843e140c601c03c02040c4a07080d08080e080f4100e0340103205000e848000c001540941c101002003121115403020a07d090075009890700c8034014840444d042210401e4140b085607082c4000b4005c0148600d20309000e44144412400568403000540c4081400381c0140c9500c04c20904041451141a40f1943c0c180409070b95201083d9542e1030083c8005d510760312440c410140c01d88000c00c003619260360081d43e201405880a00204581c0b10f40398100c00c420898001104d00c051b1025480f152759600681c0980244002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 81283859 1250 81282609 81282611
    0x703090b0105040207020a0b09061b160e0108060a0c140705060f0a020c0c130209031b01020601060302040b16020307080f0c0a0b28020321060102070e0601050702060904020409060b0d 80
    0xe12440c0c0b034002d80705c2842d00100009000313031406030844100e6000c01d0303400e07030010f00c00e202c0e1342400034055080c45400009500901346149040b2080d03041e070042c40c0c0160480800c5c60005111460002980c250321a000f02c100140010b03c0e01401d46224401200c883c08818000035003404000d4041459070041545401800c003e0f07c0d80440c84040c0d0192840b10b40c0c09034010200c0c40900c0c506600709076030503400c0e004018075000703282c0d020900702114000ca01020400150700054156410440580140304629045043c142019801c00d224400d03c00c9030038000e0401d07440d0005564080c0813810042110380101d411090840350129154200480769500c911801440096142050001c1b901100800c084a2080c045c0c1070a2a00c0704c002c69107400c02c00c512041c400304580403c2c004098516005405180390a1702c0d10400086c0303411001e810011084400405001003a60003d0030340f0800e030390443d011a1520b250b080400d001740540d6005050560504400040440314400204404103488078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 81285109 1250 81283859 81283861
    0x1703120a05011508061309080a080a020a0801050f010e19090b10020d180f0f0810090308181203010b03011a120105010e0301020c060703020316030501051003230703090b 74
    0x54030a048030700c24030403008000080c0c1881c20001c0d100b08181680803800400f584041040e9045000488001d141c084070500ca0008100a0094006c01d0069110503003400c15071508400c0c140040400b48188a0503000b0301d03000d01130040c00d03070007200c075442544400b8010542c40d10f1504c1419031000344510850006600c1c0003401011030401035112421762a481d0014940c20608800444907004c1c1c0424840c188210501c000c00c000c180404000001c01d44000206205401d2a050a00f080903185004040c540303001211b0000a1b04110314583c8841d014001800c040c125507511401c21422003054081490000f002140c20006000618141c0d10900c410409032540d901004c81031307200340040c145c0a90140c0c00104a03e601c01c802d004100c00020b80050b090400d01c80d01246000c81c02c0c0e4950000c01d4010041040d401c506000841e80203219140c01d00a80d4904400304d00110640307810b82d010561941903084042c00845484901c8070800640030303105151241008000b409407420807030300030603000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 81286359 1250 81285109 81285121
    0x50a0507110312012105010e030702330c030c0105010905090d080702060a02070c0b07050d03110f180103150803031f06051611030304090506030c0901030818010306170312 75
    0x94440604a0003240c3c0a66400d0041990b5011114810780480040b40d02080c40012420b015004070003440200650b125495441082500d216a2540110a044a203000c0c0701112300710641001d0045030700411030b96034400081d201d007180300d900401c081c19804c2c50300020f400c98181d031001d8031512104054032041b036040342c0119855282904c1010050740000c0c04541c05070b41c0340d03005080396813240d800413034116a00d00007246250410031007a82c00e83c000030b001d40c9586405000310300c48080003840147c60705018076920849801090b1407102001032000e03000c2d145901950185000718128800045060f07580c8884658952048484a84400d541c468407800691000f141c03400b80c590750341700c0b10b013021410300c0074007080c03143e0301e00c1070340c40900e003090511454a0a100030005001d02510100d0700c0d1403c6000d2500c0d2182c1c8068050280799060010004204800d003558400343c005d01003054943d040c240100e02030a455000440d1201441801c0e11504c44004000c10039070340740c0da014480d240d40e61 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 81287609 1250 81286359 81286363
    0x40603050601500d05183f0a08010801020c0706030908070c030c080d03063c15020712030503010b0d0225061811060706021204080702090108030304020f090613050a050711 75
    0x442d540031561018190381103074064658121198035040c8a0422070641180702461f0100000080d920000800070b08900201d61109166014142050007540303045415907103e99203403124442c0d4010165210240c808214845045034980764200f1000000c090301c138100304011091520031240b241c03182c07582c2c40d81c01c6c5019008140c02c03285000d80051074248821a840030a001b00c00f00da070240c10508401000d00c5a4410401c00a04003207030000514000e651f4000e890540c503608038604000f6240e0110f40020b9220003100c1c15245904100c0c0d850342d030001d075110064003690341c1841c00350001c45450024550b00392002c1c0d051a008620500c80d00d081e82c009030a012041c424082c000b810300444540d25410110000d11046104050041c502082000030b50000c0d00140d0702145c0082e80000d03144150302d40001c1031400b4020074030103180345051960010310383c8000c104c2014043c0c205000044c500e551809003145449401d6a414015441c0500c000700042100311942ca0120b0a0701401404881c4c0c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 81288859 1250 81287609 81287641
    0x109050903040e06060d06032109080d11070803120f06040b010c021e0306040b10060f05030106030f0b1903140f121b030708040603050601500d05 64
    0x9490080c40c80e140c00c02000c40407803000140f100307800c00003c00041e90b103146d061180b00011401a100f243c080c00d41204134085808a4800c038104201d03003c1e100f4040c8041c08204d03280700200c1403c1603c1e4842d02a01414140707402a88800d4050101051400900156001e40bd100d410070074441185641d8200421044030303003100708940020800b0b0101d100604040c00c640ba11444514040002e000340140084e240c00411203044500900300381c2404101000000c40c3c0c000307090103007000c420346500e00784010329a0005219803003c05446504850800c01c1642c080300c1c1d0350f00043c06810313210301000b0380200b503c0f0b407910049405c0174a00a0030422a4004030b030844c90305036a100031302301d9214444a642419084030341050805012941c1946505004000400300d0900c20b140c1c468846240c0200034080f00c01c02000141130022122110b188140c05043c002081c0303d5042071080380410105503000034900819000a01000c0040c2901a04040c20060400003560620078403196940c91004244404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 81290109 1250 81288859 81288871
    0x31a0616030e040f0e0106080c060403030f05030619170c030313060c0515072a030c0212120c0c0f040902061219020d0204060f020a051e03090d03090e010905 69
    0x3090002039400244641208050044014004150380444014003400c5480407810301d2003583d0b5824040204c0c80d814050b18600071402c480040c10b140c0303107031406414850a5183e02d001c02c000000000c1c1280d0b5141000c0c80103010441069015644800702564406c440342280320b042c0c41485544021450008201c58406c0c40d050b80c1d0460301c92601c00c040e200d51765050011541d43c040c41c98070488130031100000c10b11a043c5681c80a0689040300d0186003030040c051803400c5103000711055140401d4000340020821541641c40e000e013070701e0035040309041c41c02e00843c4d040c11a00001c1d812558610008613540c00c032004071940c41c125654642000203c6905800085d00590700740b01218400100902d1194040e03400a0000a15840d074100318040f640321164500c0b54590104050240b9540003000d010894403070300040225580c0d940b03490303a5604000140d215803002c10100990700b5030702801519a000d4024002d0f4a800103207180c00740c0206c94601400c1c0821060500026a0348010300690380104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 81291359 1250 81290109 81290137
    0x617010c23040306020d0c090801020403260d09080901030f05010f061107090908040e06091308030601030908030103050a0b0f1003030c0303020403080d060501120b0102070905040201020f0d031a06 86
    0x3a034031461141008000e9071812030314801c18400040401ca4600007001500206000021145010302c809001182103800c907619681c418001800043d050b00c5003156002080d029188040d6543d007842c0b0024480c1c0d9161321303902c509014140f41080041005071450760804d0b02c5c20321207070020049610464074244110404200d103c0400c010f0507005078900d840200e035110550341c030740b43c4031744556003035940c0b2040884850f0700c002010426406041c1c00c3c1500044e0071034a501e05810406c2042c0079109002c40c0150041c28008046502603000e0391100005950106003130f1b45035a92400d00640700d00c882c0c0b100752a14815000080c64640071800c50314425505020840c5002e41181c40840d4010900c6078100d0034076500700400720102c1e1980000d4180e030140601c021629908040004065000c0c0e103a50b41c0c0124200a1101c0c40c680e000b15490086c0c1c1c200d0310000601d6511030004034030300303100d40203003165900038018401500c550542100d21400000d42030500a02d800c6000d1003400e01c83c070307007115420b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 81292609 1250 81291359 81291377
    0x1a070e010e15070c060c051615030b030c041d0106080703171309021902010b040b01090b0d18050a03090f030b010b130314070302011b05031207120207060617010c 71
    0x2d00d4000b68504400707021011003401d1440607510001e4200540d044800882c004042075000c01000704400116030400c1058008414986604400e103080c141540c0c00030b06454601a000503181000b4402048070010403e01c90340c4241400d40003800c00d410000d070381d00d50901901003420100001e010080780d42c051044c0b00c000202d50001c60040d007050440401402c94454002600d105a00161130504501103034403100c121040e0001c2e08403030034014464000c500700b20307000a142c4e8000751642c0c12500007944240d580c02c421054000181400c25031001c4110000c50a402805400034a003c1064801c0e200da091064440d84540b00741d21130b17880010702c0320800750010711046074100090300c0c55000c40b54501d8603003501c1e60380b580107900d504500894103610401d03040081d50707400344c1844502c1072024080021400c00e40c8485440e48075603a12120307120306a1010520061141c8a08025130101c04030464440d1510b1600e140034181c280b18909030f50194a017608540c08041c42401c01d034202c0c0380c4603480d0b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 81293859 1250 81292609 81292637
    0x100302061209030d0504140d080f070f1e050405190e0a0e0a05070e0912030c0703260a050a0516120506030309040e03030703060609080a08030c04080a1a070e01 70
    0x20407070000300703031120500041c00401c0d90202c8500030b080c000c1e840740e292014940111184186480a40c0311107038100f01c0c0740428031002502d201902504103502d45480210100050002c1d03c0802c43c1540311901d141c041200c00102ca6404800b40081c5c0714100d51082c01f00005070302c0560211401c1c081c00702a000480702085d00320f5200c0c0d000104181d82c1d20280c90004c545070303c8803800d01229a00004016016070200b0495040c00d0143c41440725204508900314200100b08050900074000001e081c07108080a415011240340c00e02d900c4048071010400b0245070107400d10b4054603007641c05d10000740c01d0001040203003040d801044c4620109694403011482d0300c81480c40940310240c06540c0500040040c081d0360345460203031030f43d080701d000d006580d6400d000a005045418641c820010003101c4c43c0d060160340400324034a04030941144d00c081c2c80780c960400e8505244200c0c3d11402d0300740714582a810410a404003214034400c1c00012210940e80d1300c0b0000d9800381a00301d582030020fa810400041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 81294965 1106 81293859 81293887
    0x3160c121109090703031e09080f01150501080c120406020c0a050303090d05030402031509070f03060c02011a0a090e0a0203060403180501020318040b030a05030a09030b10030206 78
    0x42017881d60b01c00410004024180c812220a002d001d415102d202e40355a8001e41100c100f80c1d80550302100d101c6000b030501d461b4000c4a18140e82e00003c0715801080641c0c45448410105880e102c00b151080c2c500e810028012100b060f0f00b0300890028403070810008209511580080d46c3e00d0505115542c504451084c5200070058104108001038a02003041040c801030103000b031580743c5450100d10309041242c0c00a005111454400105003d2180c10645141c44190003c1001500700c2c3d00300d00c0d08024180398107400c00c2d0700041c104140070140d407008581c2c58000007910310501e02540000d09040042c1d6007640061500406860098002d044800042500340002d51604825040c00c8904140f060402407107107540705201619030301c041c0000010b5035442015a40e0b00c04035480041d18115a5010541b0a0b50b4814000b410241c003c8460758240d80c0c000703002034104176081e03c00c03070 = true := by decide +kernel

theorem cover : BRFrame.Cov 81115109 81294965 := by
  have h0 := BRFrame.cov_init 81115109
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81115109 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 81115109 ≤ n) (h2 : n < 81294965) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
