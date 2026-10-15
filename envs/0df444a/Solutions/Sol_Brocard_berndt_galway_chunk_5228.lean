-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5228
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:10:30.624117+00:00
-- url     : https://prove2.me/submissions/cea4e498-2e87-4cbb-8641-0793a5e11120

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 940107913 ≤ n < 940287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 940109163 1250 940107913 940107919
    0x170a0e030c0a110609090103021c0f060c0201060e06030d141b031305010903080a0c02040b1c03080a15061404090204230f060d0b03011d070501230a1202040302 70
    0x3035154544103180e484440c0c20080d20100c038083c410f84030509000782115842d6801900c0c996a607801c40c2c00340520b64050070101850840184003170400700c0c00414a00d50003600c621380200305140044402400c2d41c4060300204480341054081c4412950b0020f24a040310602e0304000340d58105540d1621410302a0b01162004c02c000f4035494105010048001d0840c9039801704013121254848004496901441c04002e285600070403500c0d441c1c0d030140c2071008070300b0300c020000305141420102080201d2880c0051950b03200d0040025020103800c440941d80c070031000301d0100b01c84403017401c0011082030385102c1d020600c80e804806072103121400702220003a010080040d55615074410800e42009282c4140b100c03007811409034412035150589041c001e9003801082c036805c0078a60460a801014034100c1541c1c1907580c0d0001410100086019041e4088402c0290003681c0c5050005407002001203402c1c05180034104a807281d0b84081c1007603545409540c0b07001903a443e400b2402c48000d02c255000a94 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 940110413 1250 940109163 940109167
    0x902030c130c1205070f0c0f1b0302030d0c020906150d050c19050c1011130303020318030105040b0106050310090f05100b0702010c08130905150301051303170a0e03 72
    0xc108600750041d20309414150b50f910741d410180f080680c200d500035901c020004400083c1a01c0e41341c032030325540c0d0320680a0409031284d04003e56800e40a000c402d0000340710250300a10401c151701d400d00144012820509003031824080c0b550006000e4a001441030f881030041040707800d214000c041c1a00c1d08000c01c10401c1180f42850341088045070410041c442031052082d82001401b44108159810210303001d00400004e101c81002d00c0c00751100c0300079001c560303205003e000c2c0c0301d1b551021010b0045010f50055903451101404101e02c1080d41d811841c081e81c180002c4c440060300069407281101c81d185003583d01c0c4c0d02c2c0c0c4410b4408200080d4010a400c074100219100c03100b004da4001402900200300c00d00c40d141d41c651140c2d01d14065064040d0225210029039004161440e00409030026008000c1204c0303500c81003008221141901ea0b804d040038150042406800c091003490b070001c5070314424000c0044103540082190a250071015164280700010600d0948650042e803121503c58003a40c0e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 940111663 1250 940110413 940110439
    0x509011e0c1401060906080316030f0309060c2102040e0a0222030c14090f1b040816180e0d050a05040e0c1e03160c02030f010c08041718040902030c 65
    0x2030107059a17000e0448807528080001510000c0001110400024117041c03c8100040361802d8542c21242c0100700b0a05848109120002d4424800c014024015845a1200f01804100d40013109200064919100d01c1004140a41c1114807a155413040035060056602c8041d0300c4141a180e1040460790407d8206001c04020004440b11003000d99800792804030007956103104000005c13405403604120b144512002c600e182540014a41c2541031400007107142540e1440258546807401c403c0c0c40c18801a131909211128400014402161008405000300e000580700b05440e00d030b84900b10001c0c800006540420540648140e80080002d804921410b02d86000d49045652090003c0b2800f10035103649544d10000b94416640502250001c21104005071002566100c0001c035043c0e0b03141c441c0d4148000d0300e4200f409081e2516100c1c1d075550b12942030514144903006681840f0086c82e07031081c49004400f10703050501c0354039450221400b0a6107029130010a00301100c140c012504803010300140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 940112913 1250 940111663 940111703
    0x60a020610150c02190b0724150e06030f03040b12181917030103202b050703171902070b1206191424030604110c0102031f060509011e0c 60
    0x140c100d4980e200b82030608a23500364030b51012169040e1492190070b10000e0f00340030140c4040d42e600e034407120180842e0032001d14840003600e0f40c5c0040d0b0004a001c1d5001030041c0752458001d180c01e400003c140d24100341001902042038440b17042c0002a034076141045d5054051000d920a00d14078542e2030106030341d8030350316420918242240740048420f01e240b2003888075281e0800003428144078030080f0f0b01c2d00c0d001900c9002c01d18100074208003550240714821003c80401d20441040407641001c840c2c0503552042900900f40509001030039005540107200104030500201c41298000005078a020006640c2c0344000340402d0180302600c00d2009203114003003140d04021124502184045441d048000d10310309010502820f012058034520100f0b1020464505003504041c2c0320b1046480c000d03042c001c4914446003240c1044620381000000b000d1180f003040e40c821011005007007149401443e24080d100041c010408480158483d004028915113500703104240c442c081130303030240c03d00004540c10009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 940114163 1250 940112913 940112933
    0xf0a02030a17040209010605090d05070e0f060307031e020a0918020103050903160b090307170306090c040e041401020409022205010c0209071b02060a020610150c02190b07 75
    0x20000304401c0b038080580c0030400c02c50540300ea0350003015414181c1c2000002c40301900300c00075490704011603a411400045041c810300014000030f0070020500d02c0d09000c403114030000500a68066005110b043c00494601e90301003180001000303161142a00d80e1020411005142d07020f03c03442031504078407021000311300b411110194001da030700b0320507601e520750042c0d00c82c441c0da000030150503e0003580f400001c06a0307149607406501032069900b4038809031255821000c0340d00c1144046180081001040d00e0003110306900003418040190806003000c040c0250302c800504044c04424000c001c5601a81c0250129400f0700400708055480d51640e2407420b4a03105000c007210755075884140e0100e01944140e50062207550020014000c98642d00001c1d14117941007520701c0d00900c52041c4040c0540c41340001000c246900303600400340382c075060940c102da6140582001001d0002e40042158a5074800d8440c195690110342c003a400450092201c0c004d03c0b011703400301c00c0e650f03030120301c0c94241704040e54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 940115413 1250 940114163 940114177
    0x80307050c011b0c03140d0509060a05130b0c2214011e20031908040302060702010e071a090d06020c0715210b0301092306090a170f0a0203 61
    0x20090100c5540f00514006100520b0140c2c0009448000d100011902c01c444551078032603000c80491a2500c0c0b000e0500581d04229032580c0141c1c044070900c030400c00f807440380580c82143d141182d211203540fa0b80b40d1613140400b61648500007400305201540440780f094808400b07000303800051142e43c0d20700031244036001c00c09240d030101703080c2c0c4001c004025600c000049c1d0f4101d56500d41014a0b500c60300b5481860f8140c416030910320062011418903180c0c0146882180501d40314244249071520b0000d1803c0c400038440d50469040400d9003055040c000380e80e00c1500d800c41540c2c0002144080341700c20900961400c81d40c48000309202005000c003643c000d04100542ea0b041c0c3d0304c241d0300c84003580c00114602d8250400103030b5904104c04102c00c07000c00d1881d406ca007004049551207804000900356081c4134000c0d6a103c944019800c1007810310b20500c000b001840b00a00030903c3c24684250300c401003600050031881054204104032400c1600b120324590000c07084a840c0c03500018000e681c1d800101d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 940116663 1250 940115413 940115437
    0xa061a0334030b07030905070b070309050a230105031905040b040203011104080c0411090d060b1c03020312040f080f0c070609050607060911060408010f0c050906070f05070308030705 80
    0xd03510220120030110003001d4035000240702c1c002c4d49520301e0890050003410400d0369180221240811300c1e01008004226890080da14080c03210300709010489400d555520041d028101741d07000e030a9419841c40d0301141e403103003404c03c10b440c0c0e900d59111076500850800f503030807642d14100800c000c01c40e1244020340554000d800800525200d0f14815507d446540288081680800c801c0d1010b490030380c2080d01c1107208440d2a904005c0e43e0ac0205041d00301c00340b401c0720310359242c018540032802c2c0704903a0b0f80482080f41090300b0312403041d10b000e5102d11844410040d10344a02002a080c819040c2801000320350000124ac0e5811010300c0c10b070119045000000e000d4011550700081003841030388918190355000344494540030045e502c4a000f06811030044032001d813484030000d095540c02d8040c100424044001107400d26000c2c404800f1510441c2d4410f040c420f050181140301d0300d56078143c0309056131003000e000c1641d40d81d00b003042c60501c00d43c0c4004c024030382c004204a03200e136000d4060400c50070790f2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 940117913 1250 940116663 940116733
    0x902030a1a01140309030d113601030f02070807080a020705031b1e03011a0f04140103150b060d240b1c0908040e09100902030a061a03 59
    0x1d0458951100c00380500c500280d02080d60080042c0d4034070080d60009900c0d0300302c901e000007600d42441650282d8154018411020860b0b265003032480000d9066001d44a086825003028550203203a05455031141a0401d5500d17003250849240340e40c102c5446d141c2042d43c0540b01c190a20f03085503968442c120103401801503c400107500d080c00101203201a1031600c40341084c400c0700050140144e06a26035011006059441c644951002c3c4555080b190203c54508040f0b64001c0078031031003104010076280140d140000d031040c0303080514415810360b41d10404141801a001ca248000f40440d04146507100000003410524070000e03601c10204240280140081540d0160042441552922804140620410490404900e041d061003511184a4000125400140c45240781c642094201080400c0f904e818040d026104004003192403c00050034000d030406a40401e8035000c1c2180700a09407510382c010184402c0c0100192146d09502400300c400c80740c0003000302c44054420082c030700300e05a08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 940119163 1250 940117913 940117931
    0x8061f090606080c0906091807140315040903050705010212010504061734030f05060606031003080d0632040c09030b0402061306080a05010605070f24060902030a 71
    0x5000d80000c8901c0354590500644d5a01c0380c01044d68804103481e0780c8400200a44034a03070361403240e8401040020880380e076091a00f058060010038821038640c00511003802001441c481c80c1c1e243c200b00480540b4003003840001c0745010f4405009110000700103500110b18101d5039520036416074100e88003142e0510007182d0716180003070b1a22140504001d96003103a103600e140a4000160003281c1201038230400f010580700800500c007034403260030485038006100740c04000d000e420041244c0000f400c0312502c1c510305102c520f41c044d4001521004040c030f0404640100000e1440d80900000d003039905c140d0085040c0c0025400580080400d0b040ea0410000c02100c0181458401c50340724403101d8540c2482e5a043d51aa140756000c000c0040303a11600c1003240d800c030122081c60790001019182c49494050a20701e002e0000c1c1c420513040041000018041e13400405c0e8042c076400300c11034000300c003501064160354050408034070040f02c202d40c09041000006c0c80048560045d031241c08000802c114000e0303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 940120413 1250 940119163 940119179
    0x27030c120604020d020645030703030311090a06120c0f0c02090a0b1203030403020c06070b0f0a09080a180b0306030d0f0c021f0e1f0c060608061f 64
    0x2400391200a0168800e00005006051042e003500e4914001000142000303402c0c4c0e1070800d21502c1c00041000c0d811b8178010017081590501500d4000101c12010490121215006c80d50b035814070f10010702051b45480d02591424901d60445684610140481000548640700540a0003082c00c4035210685008241c1052030305c50003042644803810b6484011002131f5400b0040e9910740540441c80b03956540d0070040c240e9480100c1800c00f64203039006107840e03240034140a8142041034040d80d004800030050840069203c03035009a004420501c4c40d01286c41d24110500106010381009100c104001039800410f50014040d01e00f002c1242c103c1d48541c0d03201c00d00030000c0e02090714543d03055401031094601442c0148000d00c0c111342c29141c14031141441e03800191440c9a10401114101200030606414590000c100394000b81d041d0f5541e6102103d540900c041014201c0b2500304000101c482e1038101301007600240018000c40c81200c14504241e40c0b101c104485c43e85299a00b0529400000341400b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 940121663 1250 940120413 940120429
    0x110d05070b0f060a15031418060f04050a030318020a0605040f050d020a0510050d0615080c07050705040e030c0a0503030105030d020a0f11060d021206010806030a0b160527030c 77
    0x300c0050b0001111610300b103201000ca070172004100c82807607200c010b801c054514405030a132117403062204030b0340d0010081000c0c0341451b0015000b02955503202c0100004608000380980c10316600d403900003001c168607164801d50400981b0000e510800d040000075074140d028001d40305940d88101c8101005079500100304010710403540013908005040c004001526004031100081c180c141882031400401381c1c14035080b5480c9030403080800c116480f0000c2001d500c40d10380b40d0300c248031410a84c50f01980b916402e230f68002a00c07849100d01c2c0c48440b0307281e180005200781c17102c000d83c0b14102c454007409807411945a81090203850b000340300300140a465244005000c201c0103402202d810401c80701601c6990f22441042c01c1d0701e411030b0041021040a035030703034401480c1c100a0b43c212025142402e000052903444007078203092007a4804280340c40816844590a41c0088883d103107220400140c0310283d03490b014500d11070520b489079024801e481e060041481d0420802101518081d460a80402000c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 940122913 1250 940121663 940121671
    0xe011d030a0602031b0d021306080112060b03030904020a02060405150f0106110c1e010801061418040e0f07080f011112040201090b0d0b0109050d1a07110d05070b0f 72
    0x907610004400020500c180e0065811100c210400080415000360604440d4801d01418442c640e00003500814000908402c2014100c140341001540d45041d89142e01c2d030080e000045c100d240e0b0746822110039502081103601c104006001507488603c1d595000c0d491b03440444040d1454055226048131100f007520460b803146900058051071642050300407030341201c0c40c0c03200c002c0750b104100c07001c5007a80e180d0001d81203611441c80641d62401340300b00010a08075041e03100303505001200c80483c1903100d06000b903d0200501c4003440481c0204000080c01900050310303080c0e800d008030f07202080841c401069407800c1d1048001260300c0c10852200b224229080c1004002d00b20078140070303800810740561245070300a40145401051b05844454040c1c045d8070004d40303241091b6582d580c421503541c0140500008000442d22385007a9010307501c50643c00c06500d40791008402c100b03800504810f02a41004048030780350012038150f1018024040c159510414054558008000014000f2070790f4072031881c82 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 940124163 1250 940122913 940122919
    0x3120903111c03120618051f08031602010302070204020f0705251505130602010e1e0c0f1807020604150b0f1309140703120c05030322060c0e011d 64
    0x810300c52510b041300c0d141e00d120b10405556440e00c0d400034001040c104560117500e281e407800282400d0403205140d42602a800a8102c00c05c011000c024244011054030075208840c0c0f000c0904100d1480120f00a10400d000254424400300d003e82000c00d011001d00300d1107116108075106410f110501c442c10003204d01100e03860014900c1c051101607219142003c0faa1402c0c10110f080c1b6445006c1c1c460f4040c416044100181e545070501c04058004100d0701e00414880000d0290f0380700300740d20070f9480d0301d680400c090103a1140401600b00c0e441d083d003a41071503010081a2005424000002900e9000c00e41d001d48007001c081c00c0701c40c0711441a2080c1030644400600e02520400b2240500a0300c15000302c06c0b03801c0345d90311070f183c00c041a4105015082016142c020300427150443c80d0401d100c01e00044035004109a040c200d000054000040344c5d0060b0050740401c0154420364024400c40e0038250b001000c076410000c24015840d0800c0206d83e881c00241c03221060300c0c10409282c10722400200242388c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 940125413 1250 940124163 940124209
    0x109170f030a021605030d0e010b010c03050d050711100b0915030606130e070e10082d030f0a050a11063c0f010e07090605220312090311 60
    0x500b0002d60090011102d00101c45554030507580710f850542d00030300d0710800281d4035066800403c0e1000e03c21110426030909000c81e100713105440040c02c3d8011500d000041076074482c080b4070980d02451094146603000c0040303400c48084111100d0242100002040c020000d110224110030b1100003e18080c440c054014503859031203a0030080c484400010b4240010b80c1c41086101d240c000740038940140c200011040c50a00b4081d140407407106580d0b00100381e0760000a0210310702a030b089203102e920034030302e103040c5803044495041504512a4030090781c8502c500040c4110703141d4001003d082c640300341d900c07454440c85106a00325128038040780c220321240c0c01200c08040034400405419049a4617940a2901c00c0a01e403031642e03110310035901c2401c1c207200030004003c00b04c0700f4164541e000c01c091400c114914a04107005d005401038400301c0c200c0c18032030310b003600901041650400085410080d40c00d89081500009002807030710780407e58560703010f540b8000d02400c00d0600d03600500410301c5462 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 940126663 1250 940125413 940125421
    0xf030e030c150a181502101406100905030628140601030f110c060103140312040b0c1e0306040b04060308250b040302100509012a17090109170f03 64
    0x400c196018012000c240700130240215030002043c5205400b81c4a074a08151405100c860040d240c9000780b0100c0180c14207000440a400e01916451383c0c210710251a030b206000030b03c00042d141c0000c1904501d403d8403ca01c01c002c1e600d000701403141d00026691010402d4103c2c80d103001000c0d51203a8210518940c07a890200b44176522990103800103990000000076200391a04064250b64071003038049179554072000041c0107100c510221154030b421080020b51801400142490401e40c00174400382423000c07944000740071007081d00229185400340c14003408640c20b58503140d840c543c00680c2c1341d6010740e1510390308040d9414144200e41c03c0d0782d003191005040c0321038800c40c00605851054520007005510700458000741c4c403000b0160040348a034000d80440d0060034940822101c0041215450b03070b06080700603909024403400e03070700e000d07040642e141b899111124007640c20503011501c40308007501310030030400340c00010740c8600c02c0c1e94850804006021541160380d04940900303908101d05480400100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 940127913 1250 940126663 940126699
    0x3060f040b0910091209060c050d12021210080f1203060405181605130504031706011e170a05010f0b0d090c1d0108030a020a1b030c030f030e030c 64
    0x19074011084000c4400d241503514043c2c0503609981d50499180300e180080c0e0301d110303400a511602500c05494904d00303804203926095691b074618480c050900c121408030300f501d0788058049070381c20130303100c4032014082c202041c0e01c0750224064418016903000f5401c0610074038070b02040118601a00410407401d58844800f000001d100c060b01000d89050212520001008103002e0202074150140140c1a0320b0301c0d240a11000904034186450300c10314080030000001e4220a0710551008082d4030845c0350f644840049c0c40b000343c2a000b04084122040c2c09400306a48100b07105402043c0d410031a070309840d141018010b840c828051920448420842400440c001101410019100e60030108200886071100b0f84414110780010f403105a07402c60140140c507200c00b08a00409080d40114a030801b4940025180c0442d1000240610314604c11400c100b60300d48110005150055005800385580345001181803404040c120081035640d2b84420407071401060311000041c1c0501030410b889020441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 940129163 1250 940127913 940127933
    0x10506041118120a0c060305010b0702010f0c24022214091b16020f010c120c06020f031501170c0a121e06050a05030327010525030e03060f04 62
    0x140f6042480c492104070740460800c4129140c42c0a50042d24015052020045c04e8400c144c0008608810403c001e00060341d0013082d00c2045140e51600f2517510b1404e25000392000390b012104c3c0358408105a801522440990040040495400400742951405003030240d60002c1d6100f0702510a1582d501c00700c4600700b0305010390f84120140300c1002030340f40d240c14182c25904000d05070705c3c000124907055411401c00c0c0701c0041c500407003403c00b020141e07104c1daa0906c40404001c041820003581d15417803020001c140e01a5101d1110390501d0700d80783d15242c003189054004510340c240c0060b0005412040d095940309081e4080c00104410300d02d0500310900c1518507a050b03014002109688000c8000c004031207a0700c041801d100c0d51804240c280c584410440070b0405078009610a8108024500d009034070b14203508840c28424481a1195107400c006840340d0046121501c4c02c983c0d0303181075411454000d0400044144213450b101c5071070b151b000606503a0392044600c3d00c501b04410b0003140216a003150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 940130413 1250 940129163 940129207
    0x20315040501080c2e03060302131a190b07321005060a0509090a02011d2b021804060f06030f020d050111161101030b060403030c0203070905011203020105060411 71
    0x1c1c0d245c01c408a252880e94409804104010010744d640b102801103140c18288008828010700050050011001e5403802e58000040d00610420503600c4812800072240c850034020402403282e0307034030b805c29800d202c1c030f070b21f121011544050340d45d18101c1c00d040794003028600c0403840203600038004400e840c48440b000b008064001a030298080100003078a50741d00c8009132041079180080c0208148510006d0004209203401d01e03800340034201c2035401030b11a50000356a2131103c55183c04074003580b1043c0481904406000b9400271440700007490099a203061050240313100300420000e00304001800021200e95000c002c014260100d260405441c00285a8000038000d0000144440d84c2051a51050744039900c070751007c2025201c05400d01008c5c0c0b0001960000070f003000d22418a20a001a10910440c0401402c4c401051070030801c0d903d0400039003000d80040d5070200841c0d41c4a6a1841340e007107e05000b1001503003440002110b034140313400743c250880034650f02c030760400c1100c03150080091201d00b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 940131663 1250 940130413 940130449
    0x80f041703070203011506020a030503041a0705070507061e03020c10020417060a0522061104032a06090b16080d0516020616050a02100f020315040501080c 68
    0x100000c1840d400c0d400894400c0c8480a0003555652068418913003034034250890404c842603019400c100d4a6008160810825031501c0d0595032a0b42d28501011a6800d80c1c1420300d540c000c103410007405541100050058600030003c43d07030800e0759200101d8040c04103080e414406204128034110540c000d4000d468001d465400303440d0801206031048040340c01560103005200d0400c07040034500c2c0f40601140b90030200141d4180300c24507082521141e400d01c404006000110880240c1d400e20915074807110202c01e096103a01da55640c3c034241803000b480941210711103072500d40301010b01e041200390f8400c100c0c0c0f1745c4c4c0c45103045c0034070f07003810014540c0141c40754130202d07100350500c0000120340c0d800501d8020524140041e080c2004820802c00c5842e410b52541590300c06000c0c00301c0c200c6242c58040c0c40790fa180c038040f80c0d9070803004012810320502c4031a0b4000c0b2070600183c071903810006c1e00a503110307080042220500140315001c0105036042032080e030400d40c00030810b05401d0b042c00d05400c10307405012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 940132913 1250 940131663 940131667
    0x40311102007140f060412290601120c02060c13050d08030a0e03180907030b12060906061e2b060504111818120a03060e16050403080f 59
    0x32804061041200c50401d181d01d800c03044062200829041d000a240002955911a5034003043c0200d5014426800380b45450250036000d007003040304001115100e4103082401c4d01a40c40900c0241601c090240d500902040c482c20440ca1018164420784080d501349038010700c030544903006a46180c0e84001c40012003840c0d0000701003940c2d11340b41c94042100f4803401c0d585680b403402000c020212401c081032039002d43c00030041c6079480d0011001240038400221400207054488410680080c41040d070810340000f400c80c1005601040420008d2092000388151030895951004204909605101c40c9880c055240035000440c10b00d0003124421310050091008003000e0b104400541d00703181031040301d14079242c00c200010840d032020300449219043d14100052a00705500540000004004402e59400c43c0f4100c0c8940c101001480405816864070b2980c1d0094100003d018004034001d081040e2080c0011076020191513540c140c1280303495480d182418190356480c20380d640704490143c80f40c841 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 940134163 1250 940132913 940132937
    0x50f060f01080402130e03090301180b041b09050108160f0807120501021605160602010c120504020406030204050a0606080108060103020306071d0a0605040620030d0905190302060f01080304031110 86
    0x903106e140e800b06200002142c40701110800c040c29541c0341c000d041c1d05100062040000070b880408a01e0300581d1000a03180602c6200854008030141a0300c000300300790812000103a03498004c242c9080a4001603d564100360301d555140b0340c601c100d0300c52921203902070202000700e6441107014901c2c00703120b100054600160282c200ea40142550021358a9400c5081d250341000b610540350307402880b181c0002c0c00a8000ca040241c025601c01c03800080303580d00c41b0300240855480f58800c8024550040080125080002d0000014401406a82c0c040f40114002280d4104001400c60407242d0040c01440300c1c1d60b50f40000c4032460140908640d203050489012015541d0b01e5165001401071541d501fa2210b00d0418010440b0b02019040c01c03680f048840c1c04080b40d680070044a2013000d50402c00700d0b803038440740b410078507241d06084a5609003400c2c1902d90105036000c103605020304682c42d0741042c2a607d580c3c8442d10fa2046110003055802401240c0400b420602480c0c0d1365514641412454080c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 940135413 1250 940134163 940134199
    0xd0f060903020601061806050708092d040b030f1209030a0f05150c0c150705040b0301092a05040603051003020303121b04030c0504201903050f060f01080402 69
    0x30691040740580c026100500c201c0ea4045100d200b54400c8110f443d01040c54810007400a100c1c0002c042e080c41000181100f40352104004c0490581c81d4541c1b0b400300110710340b580001c081c2944a030521607400e0204030006c6244c00200980420500c078080d0400142148a119440d881290000d4040c0200141c4001256004000303541007405140604411581d2071104581e07080c000700182c144800074040c505800d0340015251040c0f4619a0010840d51152042035500d070146602031842240b0001c004204007407150080e40d900d805480c446100b00305c64141c10100603c101d0140000030f42c0c280701c100042842900829048480180d40c101c01baa01ca8010904680c0803c1c00b0210020b291000e2104000719600c0100200080803000d50800b800c40e03544002000181c0304203071145883d4440c00c140c1407504203281505d041115001603031040c0100f00c408031030002c481c100d004a864100008c11020901c0a0b60344035100090071000d0005c101001941e2a180c040c005a0304000049402d015040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 940136663 1250 940135413 940135421
    0x30c0e03011a09060d02100804030210060e0402042a021537060b0a08041202030a02071a0c011d0105060607080a0c05011103131b030302121b0106030305071b050a050d0f06 75
    0x41f8842d504c1e8600e03032030035003004ad1811541c101b480141d40e24085041110300d1081030101d0f000390f8111030101d907002103040850003103204c1d045046d080c0101c4801d114022a000035512012101d80c1602580e079660750803014140b440911401042c1d02001c074803400c0c00c4030082d5a807801504a84d0f83c00110140c030ba1f188160150001020240450074000503c014050741441c0010300071180d200561400c24a544001c1d100c40251190001e64901e05000350504a50241904d12010440d03008006d000e1064102c500d590b0f00c10064111035500c0c003404180c9504049003102c041940003030030b04e440c1800400c001c45000441c050142c0d9036540c1e5040c40d0440100070350055004148465045c1000c458a05000754240d103001101c3d00000070121003040002d07004038180059000f030000c099110b10241e0300711400c050090706040c0f465480e004002c401c00d0341000141484a028946040c1e500090507a4500c0000041c02010b601c0403565004000601d001d50186040300d02c20403410062412640e140c4090b5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 940137913 1250 940136663 940136689
    0x130f050102030c030a18080f210c2503090b070201171614070c170a0501050c18032b0302070f050a0201030b0303040e0c0f040b0a030c0e03011a09060d02 67
    0x2410000612030b01d03032054054841b10040d500903080406050780d8900c0c0d0144250202401d0024010512503261220140c110390541e01200f4144194035025848403030700da02c6a240300100340c00740c85030926003220155100300201d505860b0f802099042040382d50706500481c02c00c90400c8100400c0d84621400c1301f40150041d0341d40e03495100461845100a81608201d207401c0707000341028000800803581d1024600c045900404141c091488120001c40c10a28218005030242d8240418006031101010050482c0100300c001485944102c00415032079500065540707904004001c102c2003414408034031880410f03034501f001843c0c04030540d199603444000e80801c0c1e0707407900701030094825035806000308401444214040c0d07250504041e000c8214240145c045600d251000c0b4840d42c60042c20402c460140045c500070a445420110b0001c028010003003200340042c0441d440b0040d5403c0c14000c217a4001c6c1c5030204c0591a210800a2040d00c01c1c0007002e140e800100c006540015844002e140161 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 940139163 1250 940137913 940137931
    0x18050d030e0102070201080a09080708180108011d04030e061e0d0b092a0702060304231b04110409090f0c120305040302060a0c0c080307052103130f05010203 69
    0x1412050260403503000d5100040c903070340100440f60050303a0011041d9404040c0420004403481c1d1410480c102d0300404030000c0101c440021080d01011128140da8a0302109a9a00e08a680c0b00c4ea85844207442c0c032002900240110b07004180043c0c0540f810f842401c1b80039088038101094010403c14450a460b1000c0e10300000040c03000c80714410b030007a50008001620409402d00704071f07030440074244015058030909030040c0781001c48500b05004032034400b900105400c0c0c1702d05181c1004052a141020042c118140c101082800f901004c038011280c0d002ca038048050089400003404003a100c82d01c1040c0d0040710410011070b4504043c800da1031301c107028015142c4608440e191058003030342c090f0003a185118000c5010b00010750b10600315001e030f9a06131a030399110400480186d5002400c0c11006100f0110020302148845001010700b501c1e80c0100100c60240b440c0060500031f546e03400c0c00c111100402000058026000542442101885035140f56120980c40c1c44007422a001659007181c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 940140413 1250 940139163 940139173
    0x7060c030b1f030f09050c122e0c020c030715021203161d0a030609080702030f06220506070503091f05060f1c0b270a0c0e0412121805 59
    0x8020b6140c440d1340d969103030f09682040300e0001600e0f501e5560207031f204401d201d840c20411130448508103000703c4814610266401040080f16403030304020240b0403d11007501c9161505038503042d44006010390a00300060041d000490508801c254261206c4903000d0940c0b160307050076503d2031240e40003184070710702c181c0072502040c0d80c10000401050000104001081504001c00c00e07998902c840315003200d03880b080001c0c03141d440d864150081c1c003d4541c007075414064540d00440043c80810002e00c40d820041c00703840700580b9101d244001c0800d400015020350320040009401d035014000039a08004410201c502c4c41090080f4064241c095003101290940c80e1414020181800004401d000344119020041c4c012484540010500f1524002d8146022140440c00c40c0100c20300310400480d0712070454280c0a0140e60060b640c5e008520125142081c40d2000140c2004180c820340c00b80d030f400100c0c2440556807100482c0c107541114402c680403603035884c5a10221091441410a00f4401d4000e44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 940141663 1250 940140413 940140469
    0x9100c03080c180d140c15041e05030d0908060a0905060f1f0305011a010809100c050c01140619030507090e0102270109290708120f010f090603030507060c030b 70
    0x2801c24101d446c03024050b808440d95010610446015a01514412112107030880c180d03040c0d6140c4c1141a5103c00e0300b5000719101013907129030200c07011043e05c40d0002110610789403034501d403003191440c0711f003e00181c002c100454501511092448d400004e0202e580b84501041094648851821b50085030f02e0381d55074507140d40d5000c00b0a16048502001d0911024a2800b0080280c8800078000c07440d0015075070741c4c0b1101e0418051407d442524507618001c000e000001c82c0050300044003901d00c64418800c0c03202c6581c1b01a049030703004080c1c03070340b020280400c0c500c1d00042401824007031400d044d155400b4400c040a14409010034a804d40112001b80390030b620b50317000905060403607000044081103c10b07800b81c3e0108054a00410b100240c0d100940d9150360b810003940c503008121715440c0c60301002d418080c504103083e4000d81030b543c2007800d480b003241d540ca08070402c0381c440e4800103012607814011000407036116403090040d5403160402280203c03a03500080c040c01e088030328102d000d0016884507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 940142913 1250 940141663 940141703
    0xa02130f170303060a15021606092315070f12030911040e120c0708010c02030a020f0a0506061e28090b0607140f030d0209100c03080c180d 61
    0x218a0500141010b14070714204071000c0740d0180382034000c034101516039403006030300f080c030030046c500c42d10303414401194086444120042030515240b00d090300c880526a481c60404100c0c1a20310040040100100550b10081d00030201a40103204240c8552001c611900c01140c0002411540051180d5000516050030b00e41b41700c0074032846003c240a10300d0411004119000060232014018202c2c2d10340340c540084120300342c0b802c1d4440e0050100da50802020013101c6130000050095031102d90240c0b10b90307481c06152581d450100c8000a01541e00003408200581441703144046424100005901c01100e60310104080c1002110b0300c20718401e06c40d52251072030b1a00417a4101400c43c00009119049003c0000b0700796000f0140c1c01b170039614841c0000c1d03420302c10401030f18015a8154094a0b281d0b00c072a0000c00c000d400c8098010f000e006244c0c800e0204a214031140600564192a8034030161100d0030031000075042000410241200d448100303466548800d0b940014038407030b5031400c19011070201c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 940144163 1250 940142913 940142939
    0x72411070231021b011803020c030d0516080d14101403031b0102190c05011409030a0e0109120b09070902030603030d0906140106050307020601080f070302090a02130f 73
    0x240c0d4294034010002441001001440c2c880d00e02e04000d016032200c0c01c51528101d1500e4440940401e586040a000920802c06a5020f90a40680c081e58903041d0000c0501d522408400c10104c000b40080204002da10303040c540c40407d0ba402040282d06220000440f141216203140d0203e490b4064801080140c24580c0d4040c405400510582030078001408007203a900d0081e180d000307000074111040740f00c442d4401d5069034020710303001421100490304101b000c0c044042202e0256040e50810460882c401c3c1c4a216890050203840025440c103484060201d03101c800968078030303041041c100c60000d80600492132071130030f4a00801c0300d07150b2341c1460400c3c01c3c030b002c0c0f1644c0320728a40341c01801006081d076004400c0c2c80c001c40a000c400700e041102490520014404030b40c19103000155540080340c800e03400350295108166076000c035595a40c89180045d503071407841000b80c51503800201c0510040c01c01c0301e0b04d41e410850403038015080c14070340320949299075141e800592103507a44600402c0784031501d082c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 940145413 1250 940144163 940144189
    0x513060603081206010e130b0f090c19030501050a0501080402180a390c1a0a0e0d210c090509090a0213060506250210020606030d02070b0724110702 65
    0x2860102c54101001040007e2030392800391013826501c0422558913124a03d1b000c1041310f00400301c0307076940742c0400780c0c0044c1d4012a40034803920f03582200060116000b0711840d4182c850042030510b0040c41d10004542402d00100100d030441440407214444c0c0b50385400e22402540880700c0825540c92500581c11940507540207846030f100c550b140c08004401d80701d4248014921351900c50030003100c0c1e0a11441c94840d0084040d010310414040250881c51588401c102c0e05124041c0e55955655850880300c01440b494030b50341501d04d018084240740c2e01544821014041802d01c0f010396075841e0005a00712a00301d400d2941c641283c0c01910840c44c0802c0c0441c8000c49440702040b0036404d100c0451001d000c2d50380d244c0140c1034084d1a070a007191101000480450f8000c002c40103030381c6a60402501e400c4207654050180c0305440b0b891600c0e500100344c55007aa801158140e0608905845030950490031071042689419100380402c10354a6500800d40c8509010450a0b909c0440780706100c4068a140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 940146663 1250 940145413 940145417
    0x141c080705071413110a05130b03070807031404050606060d18050304030212190f020109030204152405030a0504032105091009050c0103050402032a040c0e0112051306060308120601 79
    0x1001d1710409445040c1a500300286c039240664640d41e100c114003104600301d4200b407900032130200c1040300c80c0d580032833030390711074a134640c0c051201400c0b820700c0c0640d10308192001441c0b6000440018010b0404201901c10b0200307070f1a021034254a1034014080d0304a0501c42550305401c002800e2040d42400c0600002188680d40206a002d500780d2140d0402e072858a801003007040c4020400d0150380c40343c900c240103903400400410203060721411044241c6007a00c02c0001c0ca030004933407008564201c00f29503a01d8003544d1101c603d1941d89004c00002044000e0085051110b951b88684000c0401402404400301d8a2000100ca0038015921860040d15034038100c402402c000c007810009802040d8162021020300340414161150b10000341814440c0d0003840404590003821401c011600f6031425400205880802540e500c010303040b500000c14a00481c082621207119002000305507004651107804240342c440c030070b4003a54614043d40c21070350080c3d44500380032400000b0036a00d80a101e4000301e0074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 940147913 1250 940146663 940146671
    0x8090105060303210910020c1c08061e0d05030a080709050a060c0227070306051516170f0f07020f030606090a0b01030902030706020d09141c080705071413 68
    0xf48200340040558082e81108502c00540422480d40040006c0440d48203aa0015911040744d215059a106182c940c0d034104001c00144000350740f0b0103440502c1c0241000f810486000c0302c00728030a41414269541950803000790004a0080343e01400500080302003543c583c0742e00c1c10581802408070000d078000b1482a80613100c208405a040182c03100c599905031043c5014112800540e210319800c01240c1001d03038041d0040000c5554141d02c980e003a00e0003203d0308001c40c0e0b40e401d5030340b955000d100d0783d01d5404d07894005041c021801d0b0300159a050f1044005003440c2c03980700c40183c10340340c04ca50701000700c1650101c0c600c0d00b145094017001207038120a84c000c01c0d092030910700081c47d1400160040e203101350f0345c0c18401c01991086e0888200c4c580c018080300c00241d55104002e50b600620082000054500407011541440d180c101190801000309804c40d250145400b10180b0030120204541d05d420401c5400b000034000d10003600240044440d1603024a03a0b0824040a81d401c2d501c0800d4481c54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 940149163 1250 940147913 940147927
    0x30908010e060403200105091c0305101208190e101e11010605061908010e01030807020f0a090906140105041116140f010609060b09030c100909020a08090105060303 72
    0x700240c110b070b10a815140586503d110710720b0220b8104080700030940c055003084200060b1400002d9150501c8884010740b0000f02640c034021411284291401c641040c1821030804c4502901d103032504119025101241c0380c030291040e40b6520603001a9628045003400901200d42d103800500f09403c07951078100100380150300e140a410100e41e035141d51081c0000307910102c0a200302540501d0160001a09065aa6114103400c40442400008200004032a2800441e090440d103e00ba0304aa074081e880d54180354490f0b00704511680840c00107a042003400e800014450058080e03100102d020300000111242400417001021605810450003103003000481d201000303031380d4212460380c000c043c001030000b41c0e6482c5c0a55008407010f00c5000390301c04d9a0222580b0f1006500c403404988804008108069840780c504206004607158141d041d00200f0441d9514141941c2d041c0b0340d803203180f0b8052142529108004c08903081000b41500264080c0c041166a0109202d95038201208070b00841c01c1c106 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 940150413 1250 940149163 940149191
    0xf010b01090e040816050c04020708031503012304081303080a030c050319320a05090c0a06050a030e07150e0a1a0a020307020a060c0b100810150b0c010903090801 71
    0xc107100c0b2a05c1141c1c0f0000c0c1c41810f1100c10310404040410052055545010500300124141c00641d5400c101d4410700b80c000840746014421441c65008003a40740d1000b00b404e60810144800081003503d01200030050810290020a42c0e10046c40c0710741075548e1210050400102114614403080e002d2080030402e11031000616560b0018a03800d43d607002c942c034410b49290528001c244603d2500e500020000842c014404482d403912600e40301808100c3d55a520103496aa00050341e03e494000203007540c14821141b04034001d0008414605000c50702d00c40e0005814030f0203a041d030100401d0f014122520769026400320031f4418814045591b1401a030070141442e200e60b1042c4c0b044a0f620324001415910b290091050b10107107070300148682d114590742d110140c02c081d540c003401c451701700e11200050622040203245000f034461510041101c01c40c40075102e8010320007000d13007940300580882c0000e07004802d080140700f101603001c0003160410319403030050080e40c12a00b14180c1c507410584220340c402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 940151663 1250 940150413 940150417
    0x209040c0f031b12021605011107050d03140402010807020a150203011505031b210c0a0809030c100b120f030a1803050c0607020604030204053d0e040804080f010b01090e0408 76
    0x21015100044c6e03901e911005031481d00c2a0702500a1041d4203200d0050144401900546501c07401030301902c0c081a0b01400490440b9060720600d03a07440122001b10b000742d440751001c6075100d450b50045415050307198a85000381ca440d4102d83c0001600000140102170186070700030700b40c08940c200b96041d800c100301040300d0340c0c1d240300d40e0340c2800f4000315803100300f40040300e00c1c0c00d1312400419240c0340d9070505041d080300607032100c01c88201040c0d500340440c0480000004440e500d00f050720181c0b00d40b58402d0150720140040d60b5425602205404803c54440d00600c800c41c04c9070400340055a8801c528000030344411000701d08100c54010055040001c03402c003144961402c0400c403000c40c1e0700c0400784000b501c0d80c051604043e400500c1c0504108400c0580346000c07070401c4440c88211202824065511044904400c981a000000f05010402d483e818444503401c284124403403402d0507180c0448070b14050515444c2c00440e03445040b41c00d56542c0000c0c01c030000d0640ca40001060380340036100c4520354 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 940152913 1250 940151663 940151687
    0x14061602010603021c1707052514090a0f1a19050306040305030901021303050609151509060f03061e340e0a12021f0e130209040c0f031b 60
    0x1281e00c0842104104d48040200100e506d580da81030f031200e4040c24865a948592000013103104150006130440540712152042126002d0201c80e003041034601c1805403100c00a05a80c005075242c400e08003e158180c040c4034514020490007038a076080c0b00041216a00c403000003600c0d6910031140c1400591001b050982c0d00903054108103599440b40b852060091062018036001c120340008007004002002c80c68034000d4820100700c0b440c1d1801c41d248a820b0740e4090381c13184214001e5100e03440d0a41440c40c6207a0388624002e2a540c20860440007203820503604a81e12071007040a14000c0c02001d898840464100d5402c419000c110800d41da012004c210b036a850a800d407410b104a2844034510900010602d10070140584c0341296031110140c0301c102000c8412482120701c4410306001001c0d00710444016011603903099400d9469005100034980102c0c40c8200b116000c0200b148292682d001d00000d190a0fa903602e03258200d1103500030308948140b02c0c858039814000b84003181c020390001c801444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 940154163 1250 940152913 940152949
    0x30b0a0e250c0b010e01061e1b02010909051f0605130905180a230316080307050d020403050a0311151b0d0e03070c0f030302071406071406160201060302 67
    0x2025044800540700c003540458000c091480000020414000b05c5103680e040754015107030404200700c912101c0c4580c0d40c0d140c1d40317200001c89007a400c07620440c40c640540003450040c1441070b031a0b078a50000b0740944904a03101c0310403a500b590701c2101c0740b810b889104000d00462500d00d080c900280b0213000000c815106044180780c87e140480c0000f03030708450001000c10044100ca856001031b140824000c00580f5460300c00ea0030400c085107079400d007c0119a500003c8604405001d00c107a0381d10a102c0e08007500e01340411106021403100c1e06003902c0104055409000107080d0f901307107494001d1440d100d510710b81985d40c210820841e04800f020501603008103150460618010080c0c240485a0041030900c07119542007000d000102c40f800b0009100d064028621440c0c5981c5818030014000c50500c0b00400590200f0020081c0e5000b4500034806500002c190750b03d8817241e92120b0f80c0148501503000c0352500824103200010805211182c1e06200b00e00083c0003071403440c0c00080d100440c0d02c6108007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 940155413 1250 940154163 940154221
    0x80304061407021309030e1f14031308180310110909060103020d02040f051f1b052e05060f0105071103070806070818010605090c0a02150106030b0a0e 66
    0x208550300c0031003908130f07041d0700c040401c06140b540c00c00610f0302d0720100085010301000520440c1c02c0c4440d000d070310100400303519a00b0195804408601903544003d0941403440c90108007440021020402012020185000400c910580030308140c10710b408080300c15449481c2080c0326500e01007243c240c0e903031000111a0b804042d501c0d180141e019109041124401134800a40802c1c0c1160707000b18602a1001a1607040c6880110501c0c007035094500c4d0107520114160722805559203001030304440d5145e01c260b05541189100e0131468007101e8460b010100403140102c004a030340300c0c0030303c20315034404012140c0000d0304000c02c0004e4254401d02c40f000c1c00c42c601280d03040c0034070b031010010240104045000c582440c644100000c0440c0d40550300300b8100d0403200c00e40d2202134014081c120680314028020f0b481500c550b402103d05620221509056001d0140140944038400300c00c68000c020b262804251300b04c0d4501001445401074121500a021a00c01d0001500858031100c03400254044a20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 940156663 1250 940155413 940155427
    0x20011b02190e01081f0c170c0708030103210201060e0106140f0304030c020310050411010f170f0610030213030f0f0b01090f1a010e0613050303180a0803040614 70
    0x3003810110b402080121020000004040c8800074904000c1882c6029801c01c030303070303c040380310050764006000c0800040301da161001000c80307420001c3c3d41008111240c1c9181c4040ca50351504190826841640c22a81604082005002d0f10001d5050030740b0500c0200f180e1360414031040201c0340103020341c2c0104000b075244003289401c440104c84c1c2110760803021716207074a010700d4014104541fa00c0700304c0c06400740c51000c03440c070519401418010307648418000000c40108004503903502c900e0036408108072100000000c1130314030500d003074080c02c5000b182c0384e520f00d4202c0031f00c15030b6000340007079804052041200302c210700e030300c8420b5100ba00e82c40207000c00c02040b02e0401208809040e000603003485072010000070f180c0140e80c464812134a51050038042184e10500002c45182c408003943e003c24441d80d009803140ca409001800b1482031043c80c5503000e61107501084c6103420030042041e40200078419a1494500342c021a0010100c0c0d0000350b00d490705006000b00900c2c0504580c41641c0000f14040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 940157913 1250 940156663 940156699
    0x190e0304030507150212120f0a020909180712030503010b09030a12030b0a090506010e040506060d110706050c04120f050109171b012c0c060720011b02 66
    0xd03801190080704035100c0e141c82d054400e40d0040400188405413240201480491180c54244c59030940c01050100b0165121914a81e00460041002040302e501f0003142d48039079110f24040f401504e030f401e0026219900b0040084ca4030a680d0002080005840c2004000950000450341990501034141d600c3d0141040800d01c0d01170900310007404001e004405001d50f076419809041d10072811101e012240c4e684040d076404450042d40d61500007003103000c0070701c100c0c2004c0e0482900320030f01901003840c02c40c00c00100c60844029408410301c0140008524090018078015a60003a0b0100810342c6423a01e046a8034546007400c5c2c02c02050600321a070f150382445029071120550a8001c00401d02a15a2024800341c0c0d0380105401200414506102145902d0500c121818015500d80129524800525a400b06c48032800e50b81c08501c01c298504141392144005403200c40d01c85c8a0088080e00100300601c0c200c50144810341c1080514260100c07000c010400c1014280d405842c1e11514070282594 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 940159163 1250 940157913 940157917
    0xd030c0507080a1b150503010e070c051e01110a0e090901060e1003060c02060919050a020a0e0612011820090c0d0b0105070c0915030501050a0609050f190e03 69
    0x11030202d0307015008410b02440407005442075402d581e001140f543d9500e501c194503001a01240340c00c0028400d20040c400d0000744d00c1181d4002500d030910aa82d0300680d80c0b841c0c5410401d28070914080041c0d0b000d490700000c01d00079500156000409242040314a0070700800d0200245416803092810002003101170f003080d403200014080300e401195107481c2421030b1a0140c0100d100441d0b40520380340540d00d0980c404164a8002c039050f8002d07010120b9141080d50f00d0400c0810300796590300030310542d600140e070b520000b10024074200d2680d404514140b002c12009034000f4003400e078182d040ca8002c07807a4050f4041100340e61544035000320040c02d9490807402e100c00e10700d09074540040d04030003841401c400a402821507403817118414414202280011500c40c010030300000d1450b294120180078454080e00b02d2241d4001c00841c1c80d403150703580c0c0c64013030130f494041d20b0181020395904070038049003110b405815441700311000307040028107102c00b8404442045052400d00b0990344d80c40801e1401050007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 940160413 1250 940159163 940159169
    0xf1206050f2e080f070c030f2105010f091503050c13020d15090f1a06220303050310050a05060306010f0315080115171e010b04020c1014060d030c0507 66
    0x901107181454060300a00143d00a9400c44104c032140300c00105207600c540003450b1001c0c1c0c56600c0b0302e03120b00711a005594116803501e001e064101a4010400c9800f0280304450090a80391404001d9038540000c0707004850315044040000c200003102400400c0000494100070041a40c400740a50340c08040366000740160f100e81d40c0c04e00c0c20a019004010a100310400c19203e0180d0304210441034458080112402c014800d90b015421681d0070301c540ca03040000e40400184d107071a40409900680c81041c6800c1141c004401040000c001d00c804100348000303900142000303498100c030b02c500b0000096407a00000742a80e0401000511440324075120f80c00c10005042d406122049603502c40200a01034645441700d800228111040084c5012054040207503080a010152004544c030402c20180e00590200000e165902c5402200c1c0c1515240700500110640601400030070f00040d0100c4161703068100c0000c075505100d81440000d41c2c0300340c40c111840d43c1c141440421106280b0b0304501f4030800764 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 940161663 1250 940160413 940160479
    0x105040c170c040e0a0b130b1809150c19050405060f0306040b0307090b240910030e1218030703111009170304051c0c06031d0d0f1206050f 61
    0x5121106109400c5200350b454104e407ca40c0044111240b2811105610561a4001c1400501a0116112010180d0450620700c15a0800c0c000124a0070402605450041400000181800f0341e40c516401181d001802440d08502c0d080c03414000071040d0281c0d060907800c51038000040354459685a00811307150700003030140c030f40081c0d40b448910001d00961000c3d030301402c403c035010740c0454035a02e82c00c508540c585e800281040c01c035505002400c140d500c03000f818596503520383c1c2501740040007600c40a03069811195502d009000202c895482d50001b45800b030382c04090240300040e00e03503200030381e0504241d49041703034000c00007012541803401d9400b41d10003010f00742e11000f40d83c1c0040000d2040e204182d850151f2014580c41a241c019001b180141c01c1c1c40304d01806000e590300c290003e4440d40c1d0000300d42800c801c000d80307404d800c020300c951003000803074004c003c401d0425401c081d0083c1c5110b03400404100081c90100800c000c05d600f0070586210f000b5000d45401503039555914090000302c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 940162913 1250 940161663 940161689
    0x30c0a0516030801061413060530040c140a03080f040306090c05030c0a080d0f09210c05040209030c04090201051b0a020418030e010c030909020c01050f0105040c170c04 74
    0x2814050303c00b040a001c0c50000035549100200d0341c001100440e110280c0c0404181044d03845d0840840b01a0410016003140b00d0703030020b800100d0011880610300c49181142506600d0030189440c146c0c0180f241c4c4103600d00302c02104641c1c901d582d0744840c0b8040300d0b00450303004e503a900051881c89191049400003414203142c102da1106000100d030241c015640150101c501140100003003104480c110300c0740415a81c0107090f0740406912071600444d420f8520b080c07590403e80c56501014a811903070380f403540c2000031602d80e00700b07004080c19403900400d0f0965007185050f0401010948481e5000ca00c06e001e651154034000c2164070500490304d20401040c3c14085000e004072205445072188d08040c1d10031802c100c03a1038440d4000d0081d0250881d4140c496401c0b9060b0003005464200e1002d1013034091090b11900000c1106041c001448807440c440000995403034010f01103621000d040e0003450203507140c8040c1542403a0401c99902003240341300210100d65031118040101480307140c000051f41d01d08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 940164163 1250 940162913 940162957
    0xb07020624090a0e1b1503010b1b0703060c081e100603020c03251205030c1605100f060501030608030a09060818101e0b0306010b07020105071202070821030c0a05 71
    0x61145c4500c0710a104a98a02c4c0f000012141070496000070300404040110030000c1c05158034003e403001440014910548500c2070f036a445030011030384150b9100c0c02141006007081a6441510b14014010103008040034460508006a0041c4681d502400d400c3c1a800100740010f10010030075207017064180f00b900b1100102c008142e20a10b4241e003400c5446800200c00c2110690150b0207036885840100e60303550904200386106840d121441c0781c161070704d004408440c83c0001460050303400c4540d01060100d01d035031501000404803480799010003140e030070a00162050640c0810110112034407131030134602903211601c0801140c191071945202501c02d80000c070104401c150042038442e0000303400380d070220121110b5002900c0c480c41143d58140c00c001d00601405e1944005840218018580242042100c0da100e0703600f0040e500c1510b0250740004002c000c1c01100300701072500e44807a103195120b036002c0603458114a010203042860386500225901c0d500303a2186065402615001c240030031040d503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 940165413 1250 940164163 940164193
    0xb0306151221070b091b0f0f1009080c0604031a040302190c0e16020d030f110705010506030f0a0b0105010f11010f0507030501080a0f0b06011b0b07020624090a0e 71
    0x40814030440314070200c20001000c0c0c5c0c0e000700e04884000c0d030800c030b94020000c003901002007441a00780d5a030744c000311300e554828082e00e590601003011100342c0c44042c002030805041c903140c1200d0241e043e20031032041100f40001420044003001e41c02c8134100c4008542c94903e000d07410440c18800e00f001ca200d9001c0703907005000c08011240202c5106003c0b28100761500409042c0e4042c03000701c4500564411040200a1032003540318050080100500080c80d14202c00300c055954882001a95181e4480c01400b00030303c0c040c40081821644500101040745855940c016560414883c2c5414060b40001141109001340340811007158424001c00082d40418075070001440195988030000c0e140100118115000080d0200c1c007941142d2041c0500380181c6e600f0390112001803640b41000381c8200d05901e2401d05c501015480c0c1d2242150300024070309103038020f01e4408020100e010082540d00490710451301d003d0201c441071401d07148079080b9940c0b068500c0c0075110880d5400307038504c29040b41c1c1540c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 940166663 1250 940165413 940165417
    0x603041a070e0910290c010f02040f0e0f0c1c090303020a030605120a110f041805120403020f0603040615080f0f030a051c0605180601030b0306151221 66
    0xc1194040d600e40c55a075420840d11a0502551403540390607041c543e0032460f51221201c8a6564102103483c020300d040f46c0f20709440d500440401110703000304052005179075041402001d0041002400140c0c50044071100707090401074480200e03603000080c029410361811288102e0541840c1007406403001c2450020000d62000e6040b20000e0f10380038001c070f1207240500405440c203a07408020f100d0409141c8803400640c0b0b10802481d4003042107919100f0301e803101d0103030106201c241000302d102d200d020f040450520b2101084034004003010403091005a07100d0180901c95130040e5003080e200da5540c0307042c01c01801030f0130705884100d00c002e2000600c55000902d08442440c0b0200f65410b00300c0790000c0755980c3c041c29015a000c42c030240001d010380914824207624a400044011480d55518004250002006410b0600c00c9040da401c00080396090b01030300c184900158010007540c038010f69800f03c44582c80904601c10804840d210011900c02c10a003841611341c20b170100f001c0211039071040c0c038036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 940167913 1250 940166663 940166687
    0x5040c120b03150a2f040623041206020d06031203060501020316020108061f0531050405130b0c0301150f02060636060f0307050f0603041a07 62
    0x5503062440041c51402e01080028091030290078520150310f0300101070300a002c1703046034101c2d0300150750203025032100202070030203940220765105a652410503c1c010140709404a4405c0c0c810751511140e00115005411101202c2c00020304018142d45880c2034000b230f2180c00e25049500e810b020010050001d082002101d1420546082144c10354a00c0160f80b68000e820848500102c10b00600000d5401021a541e200070b00402c1000050144034111038222002460040041c80118010002c8101e0012061440c0a1004004041d0606601101e0200d0003805624026034403107011450050842c05444070b1154820b84588180c509034203a20361f580c00034814003241054800342c0903132846c0950448540202c0c41da02070710180c3d69100600c040144401940786502c082d44245d81d0151413069104c0c82198001a00368036681801c404121502030b481800611a070442d01c0208015903503100c0d900c0009406032107542e1660380b1810460707443c410304c008180c004104036081044c40c0750320403c4e403411303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 940169163 1250 940167913 940167947
    0x402181207030804150e06130f060801032a0b0703110705040b060a1b020405090c030c0103110a110c18010303090e040c06270b0706050109020f07140705040c 69
    0x42564240e4a4554840385448060038900701000244440d04130745080d40d0311802941007180345030305043c021031120b80c800c000c0a050300f01c11407070500c01c080c8001c0486008040c10302c1e08060650543d10384c409000c4102002e181001020310b49010280310100c5020002c2098500d1251541030314103010b02244040a00580140241a400f01b001d00d807611407074102d03a002600d4281000007410095858203052255000b42c080c901014070300503600c80c020309100301e2219010b054200b6429051500e8113040200040c103042c18050804451004d02e000e403449003009243c80e0140d42e801f80740503030034041c45222680e081001c2c03103079a840750402d425166040364480c1e903426125694490700085a0482624000e02001404a0410401c0c2c898000c90b54508880f920710030105008070400b6114400e942c0c484201c205010036000c061100c40d100d100d00400010505500d01051909140d074079200340c4500902da42c0d1201210307038030f102007007042c0c00c06000084c0c03041152a181d088090142101c03a842841 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 940170413 1250 940169163 940169179
    0xb071b210912032c1e0310090305030a0b0609060406110f01021303030503061306080d020d020c031915050c07060608030909220803010b1b0706081f05040218 69
    0x5118403055407140c0c0943d40550300d880100e8840610400003503d2113000c0030301c90f00440c039061102d95070b040000340160144009010320a00c200d043c141007425604410280618046c04c80340800e4210040701e0340704528200000c2c1d0100d24200203031840c001d5000060b002000450085909a00050b041d900c168003042103d01d0503c48119007400d0303120301100c25030100302892003000000e0091028542004005214006908002c008041103074240e0b48462601e9000d241c550450a03014400680718008a02c041d00c003010075540801d81c0d405840c2583e1701c0b03880d0a103605070240026814401c903c00d180c5801446035042c02002008603400c034800a0315840c1c9804000960141c00108442a58a000d80704c4007042c1d031800700c0c80000003451100410031100303002440000544500003107001c0c28410003407030307125440c1c41443c1207800071602c00c40d003150784400300a000d29900308070655840450303500292050401c41820032044030165100d40d03005800410344524088108096802c00e0f502520186 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 940171663 1250 940170413 940170419
    0x904180c140307080a2d0501050103020a05010504301407030b0105040507080a0f0617030d0f1806090203100911120303060d020f04061203080a0c0c0b071b2109 70
    0x60303c6031058841d000b41c81c0e2024400320005480c03103400705a130021850540c403d601c0ca010600703120b800410000c580c0c03039544034018401c51603c420400003800083c60141c0c2450300b44a8610510948003000c100180c100034420040d240c502e0010515440d80f0100e180d140900f50666190382c3c52041c08116a4040c1a4002155500b8184074036807080301c85940d035170010303210210004000e18a04d542c101c2403a0f111100803035100f0188009a00991b0300c0c3c0021507a2b00d0031400c0c2c21048a02c40c4515040c014105070700c25030402c4800b08140002904080c000070300c0c10151001a1078504640a078080981c00c01c00600c0520048001500d0081c4003550140030f420b81c41480705840340b2045036069403088d801703c0200c001d07050844240c2441c81001e0000901c0c280c442444081d6201064400c500003a242c3c41001151501806401d0b035903141d0f420110b0707030803080b0f503141090a58001c0c1002e08011020a821000da03e04801080042c3e411026850366a50485050030b890050007503100c0c00b2981d504000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 940172913 1250 940171663 940171669
    0xd1b0e04020603130f051b010e030a0c06140706050f010905090d020615010201060306020d020a11061005120c0409050c0427081b031603110a0c0b0904180c14 69
    0x1940c031441e402007401d0715540d1100c40007904551981d00503200300300c40302c50002c0001c104004c2c00c1402c0d050001038009405000c00010242070160018a000c1d0304111600c0c0b00046040c1d02060940e03166040980d800d5600e090038580c0360113804800b50141d4142018000003282019000741650250711f8280115a10100180d54903401c2c080ca0742c00580c84900001d07c846c210303000c4004181d10500c004901203a498440c80203a030801c03040e42221030360000b2804540380c1c02c1044040f2040019000c3d0100380740900181c42d0303000c92441042e0140054034460403c1c0d4405101005010b10014800c02802e0a641032196444032030701c1c1c405004900d04001c41600b51743e0205c0c124070074080c500b003410302c1c064941d440c1c01c003a800003541922240b00007568085514814409050114030640b2142c8003500c032400c0040c0340c00d000d055000140e800075070000707000c01d016840c032805071070700c450310b0f1a81c2d40ba004e404200107141a24400d03e40601c1803d05004115801003405c00300c911802c0c1001ca841c90040030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 940174163 1250 940172913 940172939
    0x506011106010510050706091b1a040501080615031005090c0906040b070305070f052a0108040f0c081002180901060215060f0d031806030b0105041802090d1b 69
    0x81005030380d000200400580c940b00c4180040c0568a1800d03500702104d03591188143c83d24100d08513205d000c4180007007440550244a1002400c412142000c001817502419a461241d03006c0c03d170400c41c040000070016114101103e0600d00044503042c0d0b0386c03403e0004906081c082d40071b01c510801d14403010580881d8000240c4008071801480c07c0d1425180c4142c0803215407003100100c083c0700050004d50013081d0300140c0e000c0c0c214000c5000d02800807840040512001c034119540b4480d80c1100c8050f50396136031082078907601c198000200681c102a03030908448030200d6601240180c82001d0400c03c0d01011500035000c103550b004032003a02c00c45214100f0081e440f0900130303400141c2c444911400d400e0060086250042e4000e030107401814800000704401d04441803007507000c2540040f50b85403130400d1000440041c40e2034a0b040100b201c4050008007a8465803140704c001807050190070720031000c503a04407a1068002800d0344441c4600f454151040e034544200484a00c60443e00010315a1034111 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 940175413 1250 940174163 940174187
    0x20c0609011b060e0303040b0a050a06030f02302104080c1302091806090609010609061110090f050d0318140307050d1d0f030d050c030d110706050601 66
    0x40350300c01c11400250401064802d03200603200a5101d80c070114607010103000070743c0144d01640c10f07142e003071518103001401d46801500829205151900401c041034000b400345039001d9045401145c805e080850805600b2140211910400403c0000d04020b000001d03258140e100c0e48118401d20741c0d00c44603a5103140c00340d44628a1980c20a213080001443c1403240d038850b4106030319005061000c0f41011901d00c160004600c006460344000b80000d0307140a810171548074000700e5030302043d5810100014404401031080f00c0034400c8490000c200e48400740b09028080d06034650400820f085824030b685c0c0803848442c150790b90300550b0314040000c5c1c0f0034041e802100030b009109051150050352586940660400c2c4409540410301014000900a001c110700c0410296542000c10340001c60f080180491011500d1062031105082121600d0100b1400340034001b908255860345544000d00341188900d644c9488118a807181c2c1d03582c2480d000014011281c000c4908024a546d48401529101c132090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 940176663 1250 940175413 940175417
    0x706080c0a05130902030c0301050405091f0b031911100f0503010513020705031606151202040c1e020d080606090d0f05031c0e1507090608131a07020c060901 69
    0x148105180500000c20804002e1148003d50b60350750301c5140b00701d800607600c2d50018503001004204a280c2405910f81021040380545001c03040381c000404640031001001d5212a161400529030f590140714501c0c4440d107076101c0c0194a0002c1c54160403130300c403a8454600c28103002503443d81107442034044800440444c1c0303840349580d003070400304030030100b4804000c07140e01d800304140e4002441c140f001d000d0583e42c50701400c0441445142120a03107100c2a07125620850418080142d141400c21a242d400e4040d42c0000ba4000003c10459151500c00600171018070308180c425429580000d6042c000d02b00ca664800d029203462080140c20f04c207148a0992000d0042541804904030203440100c4610032400c0f24a0100c1c69034603001d50002001071006c1d02c176a107a04400d80300074188421031103510300024030030440ca04000043c02018035030040c40304014188000a03c0c103420200602c0c48580c0003c0400c908091414542102a40072581c030b5006000b02d00700c04520381025410344000100503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 940177913 1250 940176663 940176667
    0x3090a060503060607060219030e01020c0d052d0c0c0315070f0314100e1302182a0a030c0f05032e09050423070909030c150c020706080c 60
    0x201040341c00360005044203910960810110002a00340e100908109010302e400514104009201400312004882641403a900400c0803030340441e40410130413208a21414503030307200d404040070040c0d5100c100e910f07491010741140610f03003000302e00400350403038949200882d01017200c0c02c130505413251400310304426103a29180c0030846031806403400f800d103240341e450b001454030b800400300900c000d02540c1c1403e04c0140d140c0280140c0e20490011940490040a84108500594040f809641082181c0c1000f1000780340415417000781c800e1851181c0002c0b007040c000882c0b40020407901607000105a40110b441c0c54036007010305020b0450300d8240051a141c06041d42d80f0300340105c00d007a10020b1600d07a0768000c241c0301001030080010102c050704165800003400d19081c039209070807280018100c40880358100c04200d182400140100c2274401400000c40c0800d01031030191000c0200d40b10003803042904240d02d070224810350f8000780030f40c11268201d60711540d0f140f80a6480c4c036030590f0206140c0ca0700b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 940179163 1250 940177913 940177919
    0x5190b0a0c06180c0510052a0f030703080f06093c01090c02070e0405071a070f0f06050604020a08130503090a0806010906090c0e010e1216090e03090a 66
    0x51084008160207040042002519195143c880701100c41044818200811003400300e810003985036062481d00703050452505034051114900d40d44004560f40917214000d0880c0004102030103007440e10f446901c00c4980b50a90780c07402500d44282140e4a00440303030040e000400314036250341030038091892400309044600001c000e2241020002c0d150290708940080e041c03d041595001440c000c02c50414001164200c120b0020700b0710a0542c801c40b4580038510500c0041000814090119038100825611680e0701c0104404603005d0420042d2200640700c80d00c809010071003040406192103020304000694903c010041203015503120700340010255000580d00140074942320303010034003400840741031124000c005010205517802900c11030300f05800400c006c4415000c0c0034041e210b010401e11081c0b8001d000104000805242581000041ca91030012610b4103100d2000c2001c031001980c0d001c00300c0d03900c40c041d218190b00c02c40c0300c5c7c40c2c640f400843c007010707020040e945215002400c099070340349 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 940180413 1250 940179163 940179167
    0x3020f0d0c18050412031103191b050702090f072304050d42200a0306030b0f060303070210030209030303040b0601020f01060f0b130b0309030405190b0a 67
    0x4010001240e82000982011a00011051254800302056003003c20b892500d894400382c140707448082d803014181401c00c2c000c0001001d81c01c0d6580048040750b02e024581e10020120003400a20780f1468502d220050241940c5901000030460300c4e0003514026402d4072030f42200071043c3c0d811941d82001034905906840d03c200401c00c450000d45000e074140c3c5c00d01c4d454200103600d200076410211003e040c40204c01c1d12500300301314684440e100321074481440b0300300e03900f90700d0041d00d004414082c9035680d042c1da0040411145145c01004681c011401c0d21602d07502c20150007060355000030303103ea080450024014900d0502114480c66014010b9030a1045aa0911008962050035282415003d10217441a0785041010310310031406200c0b05501e174205000064200780350015901d0881e41041020f22445200100c110120f4041401d12503690302001c600c0ba1200f1a1a08048010301c00002803100f40b0754000013074800d5810480d518040e10b1903000c26690405042c2c42540b82c0030000f40004482a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 940181663 1250 940180413 940180429
    0xd150c02160b070309030b0703091b0b0a12140103030503100807080a03030b0d0b0a0204060e10020601060807050903030715050705041505030a11032503020702030c190305030c03190903020f 83
    0x138480e08000404507101d580750326002c0000c07900c181c00070f03598201c924103200e18003114410b1145200c1d1080c4400d401c1c03170760103c2d007441000038078000d003c040c0c41140c20308a41544a03c41108079183d50000300d58582c540103002c0c0e4403c1e10658010045803801152020700401e56508640b101d0000f4118508503a40a40250034141e0b01e07107038046044c2107081c011401c500416413150203040d0340140c3d11070409d000644040d04412280b40201500218800d20740e40008466064400b03a04010341241c2e03460344119018400e007503950b17030140000b2030048200030482c0300105850181400038410303613442e4082110240030b80d1040950302200807440c03400030b0380114010350b0004003410001c82d248403103560700501644155000401c01c400c03505481005d175182c1e104102a40b4092509501c1c142c2c0c2c540020f0f54442d038203001588079500242c64501525800451039000316030040642e41c4582031000314985903041002402c900c007100c1018035503224400c40030170b81070320341c0100142032003400076051016134 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 940182913 1250 940181663 940181677
    0x80d02100524310f05070e0904060509010b221802011d03070b040b130504050108030f0f090909160e070914152208070e04020d03030b0d150c02160b 65
    0xc0710742c441e0000c2159071a10b41d10050b00542060200c3c00b02030728080d13130b022101e005000d0340030000c41e403030513440d29610361415581140c2c0050780890a0744903071519500602c40b0b025540c0d071081030741290440c0300300703500301240c0d186101d910100558408480d05c855280c11b6a00000d000800182039607428815000c0c40c0d0284c950090122040c4036100c2c00704803103d9202d5007108280da90045144019082641020710240c60705482c1440725516001209a40307004815100c0c01c40040482d4200340b0b8018481542c22105000f0300107102424010144c0d44c41c0c96400170340d46500c0404500118482c00501004c078059600c5903141c1c2b00d40c40c0b0f881050400224081c100c0782e4451340a5044071100400f00c8003500364482d002d68008500020000c1078410a110307a030203d902e40e0403404040044c04422404107030b100782c05071549800c0c1032300340c0340860080125184150b03020525a512206100800310401c00d5101e15480c1040000d583da9001da03503450010190140e100c0440fa000e00c41181c854001d0030780 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 940184163 1250 940182913 940182949
    0xf030c07031806050706050a0b2b060213151e0f0509041103090c01090509070806060c030708090f0603160e010201060b1b01150e04110a080d02100524 66
    0x50b01c10190752103502d58895010000241c004500740090100764410903403c402d5544042054840600100d020200c07404c030041540006403020855408030031040c0740e00c50b548076104540c1c036035100f40d503e08240110b0051161216070109910f0a0318012000915461708038030100d04500481c04007110000a6609040c0400c0300c03c0c8011a800d4440d40602c00d196200740c0410b6481f4540195454900b400001000b41000200e48080180b61501d040c40c1c0c0c0c20070203a19002c0d500e0740c0c5010200d8810b105141c1448024032001807080b09100540000d420a40d201715400e01d01903441204001c0140001d4520920345400b0200c0d03100c0d07090240d94080066035040c00085080b580d00d902c5440c0039001035140444e21424420310010080d000e01c0b41040005180602e4100f0504100191001d403030028001041a2441d0900324002d035500091720009140307000842e00740780c1d0b0415009444407903580315101414245404500140c800c4d0142101d501400c0c071081c0d840514181c04c0100d984070f5140601e003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 940185413 1250 940184163 940184177
    0xc060f182e0e0117040809030708120a08070327110a0e040213060f0e0a151517240a0f12050d031a0f150a170c0f030c0703 54
    0x600201c80d00d40400e0505009001865561821001511152a100c501070421543c4440d40d440d43c00581a055000b6410007011a110925000483e1801d1059000f44c0598454000c0323602c2c00344444c1c1c1c010500e515844e9100202c41d1206141502030b01c45490590001c4001c080c04002d1421707210040140b114007502c292990501c264001c86c0032014036070400204500c00204020550610040041e104c1c217544034100b042d18503000c83c91020305203d020703c401c030402a00101d00a1040c42d000428100b0902c41181c606980d10307d9513120385462201c3c6640401e844038400d01107070f074044100512450089180c03401e44d0010b00c2050070a100c00c403144951054194002144800c07150865201400ea00c13000c0205500c09410038a1070004103421010070141402007508402e100007181122090042c0c3d210070301da07585c0c540050400c0d0300e54140c0c4c40f285203003c10031804440d0f100c02c4400c0c3c00010100150b03196150010007070703010303c03c400103040d5202040000c101000101402000030398064a0454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 940186663 1250 940185413 940185439
    0x907030b0402030c09040612080a110a0804090b01111c030207170a021e010c020d0813120302130b09030a02150c06011509081c03050a0e0105010909050c060f18 70
    0x408903041074030041504d140c0802c80744918101445403a0182503038429086a085031617072860100d04c00d1181141c1000110080011081401c003c0c12070000d0b80000f0b00f070740300c6031038000110042c65240c07000f40c001000342d440288044d80c041801540c0705079124a0780c80d0081c2d0298190040c0d4400801101d850340c03403100083c1c603181444040c0c600c40c0481d50180034502e00340c0c500c003a40610302c0401c2d540f86034508103000844a40000720410315102c24144240c01d80d540025140070090b41c44405001640d500350703440f0300d03e607156008190152010542d6031186486210040244c0105140d0b03640641c004041d02c3c004d450061010b000541d2401c0364580b41c5015001c00c60304190081e44011940d03224240c084103d1500000e0302405030002c040106802c4040c00452031201d405c1101e22424569103a0104100c405541c228403206000d40009010550b074541d001c6004010b0200c040d80e00f4012800c80d8012403030244115000c201d1005c04440c00d2140d880c04100c1c09000000399203520a220030f04d41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 940187913 1250 940186663 940186669
    0x2d110a050a0e0105031203130321050a090b130c0b0702150435060a0905011b090f0b030601020303041b0e010321020d02030f220e100506070c050907030b 67
    0x400160540b42520042949400145440e010242800d6600d40c2010300801c400f0148034401d0548290700340c94200e034552540310090b69200400b813500c032103480c1804c04100031607a10360807059641d03104010740b01103a601c1e404466802800d00400500038101450104500d03043d603009046c106000078148005085000c10240b2650300c1640300480070011000141015581c040d01d261808a2515a038000b41da03e4125154131a0b00090484041c10780d105200d20510400358044c2103900034200c8403542042e03042002500214151141c00c0c102c401c50200441e040b0b5189042d40d010b1401a0021403c41e10345a89080007602032446150b11805400740c0040e103a0318102c1085d000b14082c460762140000303880c2604404174000d0510105661060903c0825994000300b203803d0003031162519500c400c16405242c044100f84050032120403400d85011039004454501035010f00003507001040c0050355581071080d907010b0b0203006411040b01010402440c00c0c0301064540c408440d10700014129428000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 940189163 1250 940187913 940187929
    0x30d1e200f0f010b030703030f1d102001020408120304051501060305010302210d180f0608160f020a032d02070807050409110f13050a092d110a05 64
    0xc480c810340e1282ca02d4801205007882040b03c0224150003504000303040d81c4000e00001c244840780f90801001400c9081d0114000c1300c030404421000386010f80c01007074880b0007044040750b040c0b4030380240010080ca01d1610030501c2110112046c0314060a0b012104a04102247d01300500540d9513004540407076250310204d003400c0340680120f4400007007950450041c044007a9543c130304034400c59000c041410f08200c00041c010070b01d00240c41c240000702a41524000c03024a25030000c0e118803c007103030108041d42c128100d54030070301102c0261068010b8145c02102d02c0400e1005c82c1d07015810140f800800301c2c0c480e20103c00d01c1c0301143c502d20210395150000300324004410707440b40c0040e0007100d07042c4641803051000c5401090100c0d03050001700e5280d01c0d210745107662080864400c0900324001909174640c2e51090140801410040003203180108102000d0401c602c401ca41c01208c001c02000f00011354444550340000a02004282e800750342d842c12056070a0180b1301c5d070700ca510620300081a80d90518 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 940190413 1250 940189163 940189183
    0x705010c080f0c0304050c151209031b030f030a0b1c030f030e010b0306190618050105030c0111030d051012080c0d0201050714090609090411030d1e20 66
    0x654112149440b40004031180e01c050144403d210041041c0000705400280c90104d180e03003103e82020791b4503552a1104c140c481d100703d600c90342030348030b040181c007072408005807104d0616030109110101662103181e450b8450b902500410020a0020a000200981c002d440118025041700f800d110044864899030b00040340440000382c8107803001440315414018142000c45410082c0060b8910400094070f4840c0201629100e4505091034000f9842a030000300041141800710407072040c11012040c0a45002d00800c0c0c081d116103654420b540d4443c0380003200384034900001c0c50030704141e45c1241010b840007a1103070828108111000c120768400e1602426014490b42452340d540c4003a00415003031500c00d03000d1500f5a403604040000254001540000d0031690340c0e00c0c43d64402046c00064580d001d0001d01541040d60842080104080800d00c1e100410085046541200102c241161700c2011010005010b00c10090900d170b101d8007030350b08004130305002131201081c010424100da02d0003213021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 940191663 1250 940190413 940190417
    0x1504110c010e010c110703381f051e0a03081603080f011422060b040305100902010504170708150105150703080c090402090d0b1906050907030207080705010c 69
    0xa8608800b550901c00c003a14040c02d0709040e24441090321000d61030350070601c8080d217885c0b01140740012401c40310608a10b031140030960b021518000072200524810700b220b045142103140a011945c50745042540411200014109603001c42114001c41c2c80d0062801d9141d007051300c004010000a012070041c182c4a0001d00109104041d1400d00a104000140005c3d907031602240c014442d413000c00c54181070b6207600340d911a880000414440c0c00150706162400d0b80a40b611802080c084902e2009004913405141100d4040340030403448000c0f07640b000c5009010450400003041240c02c020a035480506036081138640d4240d903000c0a6080030146100030420100d254014001454450b480c01d80701c545a240c2c40e801c010f010f540c05041e00901400180c100440400d81044039580c50b01113500309070b005000001403034218070707000c0e0308100d06a500b030000d002740401c101c030240410b00c6140d041300c1d401485091681c0714100300390000e61211000b618050006c11013030300801c00034001d4295040fa1a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 940192913 1250 940191663 940191671
    0x312090102030604060506041410021c05090a270f200c0106080d0203070209102111121209060f03040c090c031811192301090e1504110c01 61
    0x1000420040305d0703080c0c11182c842c9030140400e00420542003951040c503c82604c0c3d0341c41800e8103100c00d900c0c107400c02604440e0407000c0082d00c850a9400340281c015a101a81c402c000b1907250081003085890100070599035006141182d10840d2054200f20000c514009000800b40c0c900d105e0044416085281c04401d010001154403048009203d040020310441001d0160703150a540002d489100d0040301038481d0780850042001503607410341c80c0c00240031150481c0c040c54506c1019034402407034400213940400c103c828401d85d43c1005448903440561000c0902410800d00d00d0402d003e801820f0050307000705042c0400610100c0101c0154000c0740261102d459162511501d4000d0307a0b4018894000c0504101c50303000061520440782c01c00c1903126294030304502240000c40c5d25038111071092102c0d025110360000708070b201c19000c0e407103842d00345400c0a10440101d00640d00d0803964480d5003881015000080c082c2c156003415140200e10007417001c15460300310703085009030341c10a2101e418243d6403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 940194163 1250 940192913 940192921
    0x2502120106140a050d0201023d0912020705010f0c060605060f04170a020a090902011e050a02012304080a0201471309080904061712040b160302031209010203 69
    0xf210032420010f040440304540390710301c1d07640002d465088070700401c00302e840c400341106182034001c154601403109a06a120024a01069400103000d130101e05640e20941040e844d004c0d81d1002c20350000356401a11400102c2448080849072050301032015100e09954001c0482e10b0390b1107130020803d44480749400381c3c0712424624141c200080c48405154a0382c800000e502c0103071a2104403e048400d03075040003c142d40365000503100300354484041000e0080080403602e0b46900800904580d03102c030b40c020032803c041412411101402280d0100320300440030001000181101b0003082050a03500c00440d0084404200514440380c404105591111500550310b1500c040440c884240f01c0074050540084035110100302410342c043c50210031a601d903400303901480340035412181a0b181c003030310402c01c40c2da075010300d20302071100c0c00c1081c401c0d801460f10800303000341701100755804e80340b04020141c0b80031080700c540d05182803107000c03c03030542c0030900c00c40501003134000389a80701d000c0c2d940002d6540c1c64 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 940195413 1250 940194163 940194169
    0xf0408070f08070806070f0333080c090603030313020a031b171603020f01020109020604030b07031b1b0f0203030319060801140109090c0f06050405030c06250212010614 74
    0x54a0303008121142e103c2020401b03c0c0d903120000e90002c004604000410200020300708404110b090580c0c1400c0210100340848182c07034001180460b00640183c1d01014403490401011050980341e581c3d0684c01480403030320003600c2e0303100070302070b54401007545103d641c0d2a95002c000d540c18000601490315416000c1000f801c4844c1c2101480d90241c001e00050061000740e00d1010380b25010180c000c100000303400038280d000b54884004503800030003803600c2c2d0f0740d01d01d4982440c1004540500010741803440e103c400a25000640700710b0040d80d02e50480d00102c1c0215031100001f05042030300c26004808000016031000d1000b1800b450281004071521007604421a0556805500000075680340400300c1040d00d031002410b50664050350008641d8001c141480c4407040d0040d002440505004940011000e8011008000300c1f10180c0039076266502d42810001207000d046c0c042607008444020700030081180301c210030500340c40103040400d0500c0004c40c0300d08490003600840c0200c0b040c80f8100d52145 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 940196663 1250 940195413 940195423
    0x5030a0b07031a1c08040807080a060b0901031a060103020f0309030309070e0c071104020712020304030b10031203022a0d080609041115122403070501140f0408070f08 73
    0x2855000b40345030a44960030204820f0000b980c075014220540742001410450b80c02c5c111001003d0880854840d1a03c0d410510f40b20180074204543c01482c0910b10600c03400d141c00c22074106ca8000e403120100882110389500070f607070000e01c2141016420802c07410603007200805113015881c00b100440c0c40749404034400c1d2501546401541d10b00c1c1c0003004100d98006d01400b103501c0c5540c4007001c060b0354510348012601a01032150024416240c08404c1000c0c0d9600001a000700c9000d0280601681c5a6554070903542c4c08600020b4000044e0380a0846928040c3d0002c0081c052485151140090180700311100f049040c0c501c0c50503508801401402c1590240c843ca40007501151340f0301060610341d81d64225801000361803405154a40818081031501c541601c80c1c00c00c020010340224a030006101c0c00ca80903400e0010001e1840322030300f10407030400061240945a047c6c455481e00c41c07207003448106a401c90303a011070080c2e40801000c266200180b2000f001014010000c03030303680e800c0006450400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 940197913 1250 940196663 940196681
    0x1508011d2805071230050a1809021207030903120e0a0b010810200702010305040206190906110f06010b0f04120c0815222d030e100c02120705030a0b0703 67
    0x200c800500030328905d126001d0810054002405e06c5550384088a1080d18481c0080b003e0980b2081c82c048002108980e03a0001c000c9041e112112042035901d00c4020340481d150014040c1c00101d01d56408403508560380c2c441310050210750115a81d90b03e042e5920b00c84d003c403d03000450507070818840300c4003071141401030161291041401881e10f4414031175a10190041c410003034105900c401c0840e02390f403100030880b4292000d100780c503170200f0100032010303260002e2882000c000580c1c44001c1117001c0c402040901200c003c03280505510703482c20041801e036800c500d049100e4103208200014171901d2031601c0320b80b118401c0303050f5882545041180d03410302c103541c0c100030078100c00c800401848620500c00c041c11101250146041c611031400d00d440001c0306110801e0603084505051000301e5258400b884240e80320b076560b4034019010b001406070140301a11b003240403841c808050001481d02030300011208482c07408840c0d6540e03031640024a006c02455007502c0055054082c040c440f9454001d112032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 940199163 1250 940197913 940197953
    0x3030c0905010c02090c0f040e04031e0c081207050c0d020c092203080c071a060a0902040f26011418010203040803060402090a0503011508011d28050712 67
    0x4040f096000300f024458014202255054009450110500b5110554018000c54000008185001d03c0c005e0981b00f10f004020103a81e800c890298911441980142c003840d52010606050100d03000b980143c4a0019122005210040c051090f00060420002100540c55401000c14120200070700c41c6600d40600151000f4007054011500c1080a80403054030990500e007440c510396454503580490b0003a00402404100c0c0500d03e0201080b04065690103160b007240c1c0c984090f0742e00e0350b14800701c1c4030b00d11070024039803020181013004a0700308080c10341e01d0021803d10030041061440c1036003103c0680340c24034440c50b60201800303044d05c0501000242c02d01c50310000c40c030b1030a003511040c945000003040395203c1d6800248241d101d8585242d000002c0c84090000d0007480700d1741890b4a600f52040c0100031907507281c403050946d0007a01d100c0303229805103800064a90803004174120000714000c5070030555840ca410a142c1c001a004200d00001070514100d11510146280340c0340b4400349400c054030344 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 940200413 1250 940199163 940199177
    0xe0d0c1a04030e2803080c060a0c1b05150108010501080d0c11090a021c0608010e010504021503070917030d0c0807120b1c0f02040b1e09190903030c090501 68
    0x30f801411848003c0003c0b1042000007114010250211100a0620591120904000040100083c05040c000025605480c2699580548401103030220030b698000160421102583c40300d02c16200d1103076501507410340e00c80100341001c0c411500820380c090a010b070365a60040000c4003051000300e4408110f4603010101c0207150312040c10000040400c0d030b118180f054085803074062607034120b071810080c0072180313403004240303061003402020a881110300c60750800b00200101c40045c41124400e42d0f00030034060007001111050035540d0801011141849441c8502180e80d950120b46000c01d50895401560364115801d6081c1c02d03102102d65500038081c203081070100064001d09a00c0354010f89080c0083c1980500c40000c28060301101821000427a160540040c0078032000c6d601764460080e1400c3c0a0b00d00000140859880000d410440c45041122000c0380d5180010a9542080b04e100252041010389030390b1008480001c06c0c100c3c00b0aa41c2c41501443c5500300008900500090038a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 940201663 1250 940200413 940200421
    0x2060c0d111212100914040302060a061a090f030a0c150503090c040e070b0a032003130609021f020d110313030303020f07050d05070606050625060e0d0c1a 68
    0x24203140150552410105032410004180d03044001350080144410038080c80450340041d203980108409550981c0140142c0c000035101c0c00443c003880007282c400310310100140b02032580d00340e080e801000c400c070380c443d000f0042514240d60401c501c0c500305010b0761300d004005c0e1800c120855030501c00303609802800003e004200c000040883c8540d6480c0c000c0e140071035884050900c4508184842e041408045400718001c0120f44c0e16612171103408032401c1c00d42c0b15081149486407007d0104595982200010014080010740c0d2034101080361071025129101c010340c140003d04101c10130314000e100580c8a12108480c82d5030003080000e0240e907141c00381d85024509503407500c994905000150a0540000d86d041a900083c07085030580c0780c0002c00e641c0b601d088403d00030501e500c02c8038261342c01401c021380030407586040340454855503030181c099503850302c40d14503685121130a0442a280031b07582c3c41007010100c00a020001e402d14070b030f41d105016190b891910304040210b0440070040101036000700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 940202913 1250 940201663 940201693
    0x10c0305040803010909150c050d050604020403051f02040305070b0711041b0507050f0d020105011d0106050702042403050319110d051c110702090901021804150302060c0d11 76
    0x30fa0644400100104214400303003000313482e0304a80e20710b40c18114074001102c2456076218001c1c10280c0d88643c814807458442d10204000e03800343d800301a0030340c1c0050301c461808014003404003483c0c401d10300313004d424507a590300c41c00d091040607801b0407840000061030134204150300582c0c00801404442c20003840302d07440c00300030340c81005a0082d018481c00055034001e02c24100104500c0c04000401c880121a040e04002d010700303400e100d0801c10901c954070181c050048a80b405040e60b400b55590380c00c0c03640a4082101510002803031141160446c2e0f100c40a0490720703040c60000d940150001d65540b2000c60039501d400400401a00802c21010148000c4100200da004051620b91915a07207800101d69030b504001800380c955401a8608840e0a003850595409004114002c440d501c81070b41d03c1c2c0a5039401d07031103610140c90214903884401103182c68107501016004000141180d4020345aa002c0f07907040d804181e061000f40c0c4114181004d5a81c080c0d9410b0000c07025001401c00040032142c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 940204163 1250 940202913 940202917
    0x12010b120c030612100e0c010f0e060f091e0108090106050109050f03010b1801090522020d05011b0c060b1008040305030402270403020106050a081002030408041205030c010c03050408 80
    0x2150940e2070000080359583d0f45000d43e10f03000c040c0c03130026144043d0707010440c40018089858485864007510300d4102440d80540c4d00b0122034540c40d11011030306010802049240d03403010b082d0313016250040c4100100c6407190024102a2465011f81c17140f41e00601c0c001400140000b0021082d84e0b040100c28881642c0c0f100f512400c071001640d0000e03007122181b0000b070141801c0307201039401042c803050401c1c0c80904040458101d80800342c0800c2161a500814003a1300300d040300d214002e0348c24122030401030820703140441e0107501460001864640c41850b603214007102d5004040001c1d8410701140c24040310740325441804e1822901890704820f41c40001d4179500004101400b401400300c006015034940c00c4070f0092485008400c0c80c0710601e50b2035082400030003a5821350040d07103031286c0824a030034071035403402c1650103102c02800003142444100e006540028021a11403100b4031001482800408401207400c1c410005162550320300340c0a1401c44406403258070030141082c047c48046906042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 940205413 1250 940204163 940204171
    0x80d0c0204090218091c08040308131502030106090305010605120607110c06040909061d0733030c0f0504050607060509031b07090606140d0c18090212010b12 69
    0x24003041244183c0005041040051404259240d0710b5007000350301400410003411070703a1160342001d90240000c0c07080300c1e604000c86000300030681500c08201c1c1407011403c0b01500520a074440c988042c8541c3c004420f9030000c1c0e110358003040201c03406000300322003802840e025213415942904440445500503a841e0743c05400042800161040c442000f6420700508181304c101900856a496039000c0c001c00800084030309840c2a403a003041c0c44d80c0c1945501c42c80c00d540c0c003440c000301551800c20350f80c48010400008048002010a504080d0b030f42c0b011141c40c4e0b92008180ca000881000106020342941d0210780940e0400c20700300010b100076540c00c025203a40d1f58000d400050560b841e154214a14800e440e500e0700810441003201c140b0100c0001e804007900d40e101e4003400400d5580106a0715040608250200f07040b0500100803614000c0c3d10040c1f041c80189003044020302d00d0382e81d182001e201c94001d400702a17000101e515200141e464560b004049007000a03142001c0035880c410b03001c1020f0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 940206663 1250 940205413 940205419
    0x140909040b0414250e0f0109051305070b0904050610090306051e27030a140d0f1a0a092307031103070201090b13031709160e240306010e060a120b060a080d0c02 70
    0x80104502b140480d034000601a8030030100c2d00265140c0170840b403160400e508481c03003941400c00003103190070301881842c1101f0031074036120403035802c542e6400d014000084c44001c1c00c0c01542540250000929000303070040c0340d081441040381c9945056005a4130900705181d00c990b0040100d800129841052901e500c07480a05882e00c1d000981303640c40c003800320400711b10300c030a040c6151036540b640e1850300411841412146c10071600d0307a41d081310090701c80a60402000e0155500540c40c900f10751041e82d5400402c034a000035442d800c580d00c0c0740c46a0070a440700d80060399921400420444607594030394120460a81302220311035a950001c2c03820783c0c00e200c404a40e0b640308003c00c1c52848204400041c9000c01c203c440c400030340340d401130b1a41000841305c05096200306030342072180d030503503404940c4000400b50181800742e0030101c0704d020f1408042c2c9582c1e001102c140b000140c012400ca0b1000c10244680c040b94400e0804000b044031030f1040e030b00146040d40108000781da11503081038400014580c1a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 940207913 1250 940206663 940206671
    0x130b06120103120504240c060e010e0c030115090b0a05030f060a05010e060a03081804110702150f121b0f03040b100f1419060906140909040b0414250e0f0109 69
    0x201b4000c90381d100c1c41070f10081c04141081f007021009203064009450000400048980041c00c5c14209401c0e40e01c400e00f07071301041242d104184000c2200b5041203c200d800503188408465036407010918100601c12242e074150061070500c038480d10784e40662401440c0c007440e941060f09180e030002c0d5040056101c01451017078000341d004480129001c00701441c0f4070062040240d0f950a003081d504550085030124402c0c2c00200200280e00d6110042d0b5141c10b10384494181814108042c408110802500701410240d01020031408030340c500000b04110480142800e440381024a025980050041c054030050044c080c8144543c1a281c5440707403c030380f098ac030745104c5c4400d69004607055801c4104451a40200c0740408a401c68202e6500c1c01154420381d100640344401003202110350003403102d4103501030160404907020070200c008460f0000d000e540700e880300900004816242c00c030400441c02c441c803229841907a03d440070306959402000f00c46168801460034080e40c03520800140500050799540e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 940209163 1250 940207913 940207979
    0x31203061c1101121a0d021c030315082b030603051510060801120201050f120a05040303061a091203070b0106020708011b020a02130b06120103120504 66
    0x52444280c128495484030201c0484490801241c81c084450b038450200e004603030502c50000c1544a901d490541d5141c1d00120b90b2650001c0000619417144203076401401c00d8903080200c010000c58a80891081e11b002900101012002c6190049035110300110f810036140f1404903203507400e445401c0a480842e05011090301a8103500510264001030320307a00c2201d00380818006803202c0f1600544a019680340890303540c480072140808240607800141d800c0c45086001035000343d001c0c0200c0040c2c2403002d8101509001191340580044801e07250a9413500c1c107000c240360301417181e04c020b04800c54001000b840b180500d640140b040c02c20060041d841c6041001ca440c1061040e1903003158005005442942d44040013075913407026008180d00ba503c2c0c03101441000c0c24201103180410306a03009000711070010b0f02013111070034024403421200760310703010746072015607070741e4024404c88188408114803941103042c041d0780c0d00400072101003401401c10080c842d4124a000001300c0b2444d0100403407180c09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 940210413 1250 940209163 940209169
    0x60b03030f07060b0414091c02030d05070f030b0f06040b0706060504020708270112050601020109050f0703050c0a0e0115180e0f060928060b0a08010f0902040503120306 74
    0x801c181c0e0310103a1403404214041004080e410141c1e1800d800c403000c0c040780140400044142c00f0a83e13070400254060340f17050300d800482410611400055005a80c1020340c2014034000360344080790000c0001d9142e90f4030907030080c0c061096244100046c2d5808030012103070008070740c07548214024540061700108842d4204800c680010028000c098000d54035240341d45019004d5800244c0100c0b018201c9e07903d11490190041c0a00c4031000c416500c086444e404211540300038800030341158115500d80100034007107802000001c2003c1c00c0c0c80e0040211610f03608013141400e81d00b40e580c0e88030f160081020000c1d203605540d40c0741540d8560260909450340c00c2d0003641c0270001a8092400d503a5910000204110003400840c451881c8003d41202907862204200032100c0c2210003c04c4240440382049039401c051480c410106010000041c1c00364903803403250b055400c9912008001500303000103010500c200859140100302c0800306504003030070000003d0310f8085010035000600004400520565 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 940211663 1250 940210413 940210417
    0x7050112020f0d0501080708240603011d071a030c190207121208010b090d060509030d02070b071e1d011407030e010206130b040b040204020c25050d030c060b0303 71
    0xe107611240e40d80d400f20780d0b022019040074820415503028048000035418400325450000320904413404502c0e500034484103204801c09441181c156585084850381c41e501131724011032000e070040c02402014a0315110b4a00c140f00c003002d544202d0f00a006200401c1442d1054420106946450700f1648051030781c103d01d030000940c08640700380400400f400c14002c80c0012030907400c2d250380d1504426a215440c0752690300c2484500ca42002c000d400d04408a2615806181c1101e00c0005413450700107001905030983e0408001503919132440414800d01d290042c445669003500c05c0740c030742c030b10700c00d5807402620f103c4a50117400c1c407165100031000c06d170340c1c8250000e40d07244580d140e03456160b99060800401010303d10174218050b11410000c6082189460710040786117078040b86c44401d90b44c4507910103200b504040c1c000ca0308039400f403000901070f40b07091000e40d852100c1d800b00082c0d034034140c001c24418900f090f4891030040c1a800c1c9a100480d60101301702c01031940042010071000262800310340342d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 940212913 1250 940211663 940211677
    0xd0611030103030e100c0b1f0515180d0b1b0d0f09050c090115030e0c040e0d080a05010608160c02030303100509100b3f010e07110705011202 62
    0x144000400401015005041d8200c00c00741076611003c0e10068140c1511048100000500082d030702c000041c04048c40305040c0407480c1ba1104070044890345e68004150741684100502c1e541000105000260f440d41c6502c207091404c0441d0394a042c0500d5480350034a111016103003540761580d480062f1000e254850440d400e256140204014100308405040010120100d044845000e209009500751900380800c506980000c10340100c82c081c10b0000340c00420740707120040000d0152104036582980d0314803510007181d0303400020380389506103110001d0003840024404400700c0d20380401400000d50006d081c551200b40042d0f0f04d40d0600c0b00c28001d5882a06003200254144400000c008555408803040000ca40050755000403503145c01821020680c000d000307850f0802c0041c8029801c4290030b14501441800c07203007081642c0550141c0400402403041d11010009400800400c40c00100181090f442001841c014200222460000303444050610030181080340000350f24408268950464803a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 940214163 1250 940212913 940212941
    0xc0903140c0f0105070302190b1503010b061615090b09060f070f110309040e01021903110901050f041701090b072607021608011a030609060106080a0b03033f060d06 72
    0x9410701d03d27290303591010888039000c280916200078412400e05015106010030010a800e040c02c5e4080003070080080301c2007007902c00c1c01555614041030060340c8214049640078000260f110314011010504d040e402522400720f0001001c1001502684034030289041d04051401844183c4070b00452071075800750b080099889468004c00030501c140550040c02c0000c120190700c140800c0c00e00c4150704407038441c864001c050400b0081d41d40d45601c640c1c001c01807241421006410a0385512003204030b07419800119405a6550440d1030520101401c05c0740d2001c05480e04841521461003041428884180c3c10510204100d000c191414000c0c0030b0483c0d408005104184c00c00c0d034030101340d4040d0a4000e0100246e60020841c125030781404107001d88980350300b0008214907440c5c500e003225201001800841e13055519074040600d80e800b40020302c0c0070303039001c0c2c011720518400c20240088070310320f14114101251f0003032034030403444005600154044001c80f0030400301030700c42c14600007030048046480c10b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 940215413 1250 940214163 940214203
    0x80f09090f070914012f0a050102070c0e0408191202270103150e060d020a080606040b09070c0f050c0910030c0608101e090c0903140c0f0105070302 65
    0x1c0040003a04a9110314030550341c101e191556160f03803414400400146a0005a8600c0901c441d10300090354a4510914030800e84401190403002ca42090036104046401c0d1350005240703024041e410b450f0078041c0030307461140d9805081c5a564643c041c81803070381e41481d44440d01070554100c1d0150800c41d10f01d40c20100203540d82c000c41001303000000440d104c100c460464401c1c004040b035100f40315031164004800019503001f41009990781e600c1400421055100e19107100d00c40050701c6191194000f0300c44603000b07001c00e007401c00070003041d10320140d00e25000701004820015281d0f0b00c0404861250382000d000c0d2038598850820301d0420b107005507043d80000040d018044000725012002044038025800608502d844d000120f41c050000e440288400d54036407404c3c082c000081100700704000401c1d59200301c060380d40b43d051080e9442400c1d041e0115007034680420070310401100c00c03210550f0010103403207807003490f41c0010303d03040d00750500f1410010b01181c81c0c0c00700340c000c00c203500c030694441014070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 940216663 1250 940215413 940215421
    0xe0d05070512070f14030c09100504150509090c060313020a0f080d12290415060809010b030601080709020309100501081e0f0604080a02030f0f0a030b0a12080f0909 72
    0x99803400c45110b154104c41140200003041d00240e500b40804000080140000c00700300c82c00c00041c03007070107010000b01003138004000943d036542d8415101d00c00c85000813048081d1510007080a9000c00420541031a0003024508085644500c2102da002444061340d483d5108180041804060203410500c075568a648020600c000000350182d000321155881c040700c03004084220065a84c01040c442c0f242e14002e03841710603103800b202c035055204406040011040e40410480e0a40b502d15848000401d02041c140130f87c2280a004031407410700c056000386030035403502020030341d1001d01b40702d58200690b0100106c0d482c0c0340c0500c500c011442c1003100070f218650711401e015840c0c00740035040108a0620107040c2c2401340c80400c2180703403840d14a01a04d29580c0f00e45a60846034001c2c481c100440c00100501000d0318122006421140613100c0d841c1d4481e60003e0000d022103c2490003240b01d00c2040c2d40c1000f80301c40051440d40e0080c0e12001e42038071124412454420b50082c2a1200e501c500340038100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 940217913 1250 940216663 940216699
    0xa0e10020415170103030302090f060315030c06041d0705090a0801230c0306010c0206090d0f050f03040503070b070501090206040b13171b0d05030f0712020705010e0d050705 76
    0x508180c42d08940385503401480740c0810340d0407201250112150001110042005c41c0c020b5020304041c0001504074000c00c0d03c4040020900d500c21220000009000c450480c0581403c0001c01c0c0c2c1120301395101440c045c01d0800c02d00d4000126540c080012801b40c00042a40d441417090b40d16100003e02010041d507184d080142c0600008020303010020f40c201190000300001e03100c02ca01070035510b1040f42c50358035040700454680c10602c0703050760040c104002003100380e01c400c0b0241840e540540c403895140389183c9403280c01c042c2c0442203000c071079100b40000c0c0016034000c01c9510464110402d01d41da501c8481c40d106000d04000c60004c3e40c0182d0104000dd210910007000b41032810052408444031a21780b8414144001c6104080300d6a0348408144800a12400fa26014032440101a1980440240d45444c650790003100f01d000ca00d5000b08550702000719050f4150070b05107460000c1d041c1c81d410040000c06422040d0303550b0b48540520203104041c028107100e170a000d484040c00c04a41f08410b2102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 940219163 1250 940217913 940217917
    0x504020d021203030f0c0a050409090c0b0f18040e15071e030509010b03152202030d0e1e01080a020a110d0f11190f0c1805010f140d0303050a0e1002 65
    0x120400701024030b0001b240101c40030200c0c1e62400b89503e8281c1060708105690008102003d002c07140100c0c0d0321030201d1480080380c007030102200025043c42c0d5551700b140010182c10380c610b680320301550420000faa20840085002c0e2400e040d20001105150f03280b880840708140500040484008180c0040c0c41e11613040d00058454a03006000b804440b4074030041c540c0c0e580c4000c6104a042151401140d07500040c00d20704d0800300d900c3c814400ca12102d40e00001c0c1000180004140400c40842d00810f0b2810410b0110b00250301803003a4804070000d041c0080c040780001041305801a9000401c0010180122003450403408100c04450b50324001420213001181517030362040218032003807400000300c3c0d00010710150484584094080803421651031069480d001d19044803402c2030a06c020800080761645500030311400f50340410315501d402194403d40ca669006003aa5030380c80c00c2c1510241d03d13442201e4207039950620700004c0710750700c00c04107100138581000d0600c418007403581502c0c986da640fa00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 940220413 1250 940219163 940219171
    0x5040c12020d09020a170606120a150f11030f0103290403180801020a1d04060b070f120509030303040b2d090c0a0f0e0901060f080f100c0509040504020d02120303 71
    0x185c03217070700070fa140c02c1410004c4e00b0b01d049410055000c4000601b140c2070102c840c82820528030120366078000c0e9581c1d074850307040a0f0340c0c50840640e40c07808480c2e19200c0c1802030510711a207c1700c80902d10300700b41040103284c00c0140030107480d10a60395584d0a403d042010300c500c01d205080c1c00b81c40d40d8106490001c144c41c42c4581c281c1c0000308000030200f6001010300c00c41c0e50421144c0c0320f66811084030a541409460080748a560240c0e84560005440c800b130001010f00d20311804c034880d20f80d421403400ea40c010100581000812400340039102c41900d00004403a00b03e900070340006800eaa500701e00034200b0999110501c1030202e001c800384c3c2034400a81c01240140c2906040e100101c210109010742151180f0540745403880e92041005049060240140c0100d80440007180c4640c5442d900701400e0515401480c1c540d1000540c4800e5401c00c0c0800407250720146010b110006040390028041d0056410807880386940700e0102d0115610303980c4450300300b41c7c080c100c03610980004071000e8490304104e07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 940221663 1250 940220413 940220419
    0xb1b120a0b0604080c010c060f06060210060f0515030612010c0203120f0402010918060f03030507050d030c0e041a100203090907050705030304033e0c06120105040c12020d0902 77
    0x305500745a480c0c207200307a50644d80204010003401541d000111508608100256200b0365168044442c03480740d4080c1d40040c1000b038000b8800400b41ca10940d007103800691100081c905150810301c8103565032a03500e0b15511260300c1c1d1649a4035507030005031941c00c07040c4160080b5840d00140f580e0241d00400540900c031146020300480d0303a980c0040700d4034090704403002130018841000c140607800082078041c0c41e06161040011f136040d01c408410600048036001500403910224200e010840c00f0421048052880d00e0140044414203002404204a9080c02e86c03142c0c0c4c0390855000c085040d25003c69125034001c2c0682c0b4406141e400294403603003c0c100f0310340511481c0c00041c60f4a8082d10407141c0142d0b0010056186982c1c6840c1110100380c07071200291008002005031004146495515600081480b06600601040300d00b4600d0420b20440300c0340240e505100c03441d46081c0d1060240d0449a05a5001c101d8443ca56400c9541f1488a0385800420f807020402c5100c82410741d115811b000d00c25 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 940222913 1250 940221663 940221671
    0x51501031b120b06040c021608060a0e010c140901170f0405010e0f03190908340807030f050c090c0414040506060706090c050a06020c1c0f0b1b120a 65
    0x3210b200c00c00803100400503024280050128401c1c0c1800d60003091a4039003407061300c6a06609907903000d071103582c5510031200b651010041c045556054825035282c9442003008001c000f52420016051402c5c840410b07008079004104034586900842803089190b10701c0090790007030310f04080c249201420681c1c040d2419807030f003c501da040c0400011804004056a0020b40c10000002c40501070328081c02101c00030407500680029007208104414074410500825400c964444da0b0301800440b1001c209034110600201010003925102260303000541e50002914052a0b41d242001d0303241c591100c801d0b0340c200e41792104000300080c1030006882642c0b0700c1d2140312404000b04041100340c0b8400c0da80030364410300800c0502c00090044d0322484440344034030301e8003c0d0f4a5031080040d0311342a05903c104050b812100d201d981e9803800c1000710f01e141808619082d400089910307009034018441d600100800d031030300c0100e0120400130000b503080f5110410300640d585405900489581d8003922169002418 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 940224163 1250 940222913 940222919
    0xe01060504021e031b04030b061002190b1506031003060b01050301050a0513060302030102030a0c021606080f07210207020310050603060c0a0c060207030c033009051501031b 76
    0x3034000c843d003001000408040e00319140c03034140c041d90b00203000d002c2c4460000c4903100c85002c00e84017900c0114000d44881640d840d01c141885080581d0001200464206549000000168140600e00290007204104c41c80d070b140b810303080b400583c5148140e80080080100950340d0700b44204801500d1003000107000c2e12503610300640e100d000038000d280c0c1c0002980350a108a00345038000c00440c41003c54042442a900d8010900720380c000d0304d180002c9038544808590b8030703804000080001c9089420101d01500c3d0007030003450b8100240c82381e2078848810b008500300700d10030341c90714850303c1114641004400c0340000c2034009612891003203001740038250300d00c11009454411588118000390140c40c540d940e440015541c2d41c007680300181884410650100868032a1018000c2ca40c0700b510b130803505510a01b00605142c1040400310b4203e8586020000c1d43c7c807420040d00524003003500041001c800318075000f030038106840781741803121003010300001c240000d420030300c0b41420907400c0110400d61 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 940225413 1250 940224163 940224169
    0x90708010b0f04090303150b041401020705030a111503091518150604020f0d0204060809030f1228150b160f02190608160305011211060417010e010605 66
    0x22079540c0c0d070341e40301115105407030003800d080d046a04840d210b4a000101e020b10420b400d0302899a98002e01c10f035510108040c4038802540188500710007090006001c09441c01d40000c1c0c0d1070788600001407401140b11000c0e034107601d4248901070303c003144610a64492170012000c65440d21010807600c404c0368a00085403001410300c01c1132542000c46e801400401d1507640e08a04405405010329400c00d0b4204000342615850102802050518040241c3d4071894000014207a180107020440303950801c024000058a024049422401000d1031080160b51520308440c0d02002d016558001c0d00086600100c5c403034110b5001003d0180501ca6548400d922201c4411712801404d2400c101c250749114464003143d0043c848000651008045000f80e80341e540c0c0e82c4000d07035640e503c80d4006c1841c0006001b40800c240c110b10461a0081c501001950315002e1050900181060050640b4180304101c60007922214201c4000c4d29003000f14190112248440f00c1c000d0490002240c42546407010210b4145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 940226663 1250 940225413 940225421
    0xa020319090602250504061d0a020307051602010504170a02041103072309061b0c0d02060405040938090a0b07120f0603080d0f11041806050a03050609070801 69
    0xb480541c0207014030781c50088000c0404c0026100200c60038078400001401d51303202c1c01194003030710342e0544200100007501180b1301890006003032504664018001c100d842d981c0501620842c41c111492054002414001a00e4034481c0d030b08070701c0025242d070500400144000680021191090301c4c10840d071540b034928000203010541c1d0301c20004082074462640b592510041c0c44108103906429407518110310006921680440003000d6a510b8001c14141070244c00e01200707081c1041650f036050003052aa0005d05180f1640c0145d074800d40d9038004241c288464040720300c2840d100c440c181c200841c0040700072203d0003e20301c0c0090303081c604800003d215810100320010504c0d40000a1542600c6001c02500c5400c0400d150034001503498161925119150140c0c40c001c50003100d81c269114a00301c100d2054035030400c90b8842d85800c000701c24000c01706840442d0115010258459816404030780c4400191035940c0c810baa010030100741c04424010003091441c0200c4100c000c650f403440ea03c170920343c02c2e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 940227913 1250 940226663 940226669
    0x108060f15060c011803080117010204030c0e091504050337081306020a0905040c03020a0206040201031a130b100f09030f060e06070e030106050105070803010b0f09060a02031909 78
    0x240001c00091240341c14000040d01c14504041c001281001e0040300308801941ca12500390001000f01004010244000c0100e0003410329140095103054103546072101c2c2d040d85403051000d04485680062820f281c180100c0344e50034a01034209515052a0801035a0303a0040500c1d0740c243c180c0400001e500caa00d0030580f407078140c06d8000e0078054019070801a50014001000e920f010000ca101d120005100380c8000c201640c02c80c0c03a4070400504201c03e0100300c4600070140d4081c1481080100d01a0783c000403681c0d0310503424a8082003207061900300360082000320444075041064079440c4003064100750422401c490003514002c10366150180211040f003c200040000700341c214034144041001800c02d1070482d030103141c020920103011820310346880400c032540c00004003030328441081882c0038000c500c01410240b91150070301d1016150310500e44418400e40100a0300000d800c00554824015940f05201c020302c100e07111064107102035200c1d4400e0488035140c2d10079101740d42c03410303000d104441c1c15 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 940229163 1250 940227913 940227931
    0x150c080f090f0d0c060b01050901080f070201150f05100302070804030308040318091b091404021c110403110405070507060e01090204110c011116080f07050601030b0108060f 76
    0x192100c1492014505014040c84803500810b01c1c11011002c040100b041141003030b030703140c03688401e6a041500450b80200c1d080760401c40204000749150780c0c48228150081004402146e441e100c0b400700364010840f0802d02c0e900590410b000003204600981820101c49041d2203415a101000310220100e01c03504000a0841505010074000310f485181c086074080d110307052020849480c0005e5030005074259022918668481c0b10300c080d6440b0a1018001540d01c0c1e0414160450800c8210700309203007007400303540c0215401320307195100000c03503010300707881c160360120400a400d19400034209a40c0640415a81c2d1007450010403130300c6c10700d44292440740905d641d8050404e0295130b5040003420311141505069034030365115001596452044118030700c417020b4215a540e03031503030020b403d441c80440c180705460b1090080994800b0b83e46108101e035a1b00600d91981d4000d1100d541c0d5aa002d8814090010302c00c0e0800423081000d140071407410f0352001ca040b540b45595107812110b0031042202c2c0422 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 940230413 1250 940229163 940229177
    0xc090608070b0f070209010b0301260d0f051201060207080609030702060304150e010f02030711011416020f0f07231810050904080304060e060c09060f0405091003150c 73
    0xc02000c08081d095000f0005542c1e45000c40e0364001401c0800f081c3c1162821801c0000108518a0f80d0459101c40050301100400d0b41e500003811b0f143c840640c125490f0920480040200c1036522400456200d0045d03084140902d50b110000255a14054041c070b002074820304c00803451422001090f20000d43d40189007a1450b9200d6a44481c621400d0040316403560701c030100e50400940030700440100f12040c0c10016160b150190000f0210000b00f4014501645000000f120741030b8a002d015a0004940c00c540c501024019005c070310b0708100500c0c1094034041c00800d101ca0400c0454404100c13403244801d6000200c0d0901d96180035010300c680150701680e510301401002001140c40f55001d03c14100c040242d43d0b0354004241c440700e0840c0c0c11036405000000708001c008141c0300d0707002180b0070240180701500d0105d801880500c030b030141e0640700f0900410440c002c1c1da40803040703401420b0042c0080d521070400c005000d40750b80450000300c030b299010a03d1104050064031030032203215242d0baa0b0359 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 940231663 1250 940230413 940230419
    0x905010603170f1909050409152d02030919060c090b280915080f100315020d06173702040e0a020301020403080c0105091b1c15090c09060807 62
    0x184d00340f2603540c0c400c0103010701c0b00e200158568aa12402c4c40c100c0c0120101074a14043d0f08404040f40c90303410210255041c1548041141d001d55072004a220071032050041e640e0310f46000b03844c98425041d400c42003010700c4c8040d541c200304054020002d801581d40711030700b091f40c4501012955008400e894081074021516540c50821104149440003001e400c1c01d41c0710603110f40725203014041c00d1012030003051904007400084802c2071451a44a42c0c4003d0400e801c90469071403c10405100041d03400c00c503004207501003040b4040c0c1c80200186801c1c0701c1003101210303e04101f030f1221a00d800c142e242000700c003900354844110200c4082041d221102007800c2c2000c0341d0801c8001e00c1c000003a2502d5106407032000e40141c800744000c00146000d01c84041d00c903120203501c01d080d108014103129682c3c010241c8a84050402c03003600502c8802240e8800c0c41800b2107101540b8000050000780c801c030f41700c2c00c80b1403046656030b01108410340110500d04040d0344446801c0706445840c480d842c03103940400010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 940232913 1250 940231663 940231687
    0x2190b040b071809021c020a080106140c070306050106020105060321220b1315020d030b2707091e060f02100e0c09010905060a03060e010e010905010603170f 69
    0x1e6034015003e0428041d0010a20203020840c511030b041a001d065001820150002030b90710311100e5055552410b40ca40a1013580051001006114000500284e81d182e4000a510703a0140c0d088104140110303000e8a50300d0604001414081c4100c00c0994070705008280e4a050100e8070103020580300c221003c48004040300240103a00c8843c81811590201d08112003e4101203190b800508030040c42039100c0340c00c0b00140c021070f44168040c05820f4083c0f0f201021080d00828040c0741e0641604000034425903c82c04502000300e1101d50004205565828a41000030810b0890141c00155101d028140d281c03500e121803100860807100d030510800c803003000018030515070704030701c20050b1040d9004109185890810358221104681454001da81c540045041c81c0800a004100c6000207009608109011500241c0d076070201070040d81d220740060380079040940291171003071000c00c0200301d20101e03410040c3c0240b0030341c0002c681c05102c5094a0824100c040180c480d031806901540e4507041140340a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 940234163 1250 940232913 940232933
    0xa03030f020c0904050604020a0824060a120f06180203030301051905031608211935010602120a0c17030a0203091510060e030102040911070302190b04 66
    0x1000d08500c2800e40305101a00c9103150f59001c1c40c0309400610082c02c01d881000089619a0070200b0310b80d0001c90310699004054400140c5848100140d5440d80c4404000c55121095074000148400c200380c1d40808100381a000380800342d006210400030070032a03584a8010f0109560007a5042d0710501c0144030303901d00ba06202c0803a6040c602e80301d08295407580824240795034a0015409440c030b0300d004115071641401981d0580a03190403509510000003460070031800340101024070b800c1c1c1078120030f9003c0d000d00c50304040040006143c51003024482d81d0740c0708203440225045604000c1d0b500001d0300a0000074040e18102d80f480c1443e0614901c15800ca542046801c03050703682000306010b01c0c00d00c0307482d18001d40c000d03040024056620720700701100d0343c0b62070700142e42000901c41d20b004004143d5400015681a0354991400e5071083c102240000c0c0640141c0d04003100340c906e08070480d8480c014440007082c3d9144260240e5110303451419a103002c01c2440c441c041c1030884003500181c00a084180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 940235413 1250 940234163 940234187
    0xc0f01031107050706020f0f03160308091e100f0903230d05070507020f180a020c0304090213060f0306060c0807081e030a110301080a082505010b04050c07020a0303 72
    0xe815070800c9050740701c85144c070351980e01c080302603000080d04403101b080910510b852208034000039445c0420441a850120801c0c1c0c4000d01009040d00100b0181c44003401140e5030010b601844000340041c83da401925416040500c1003290b01c0c0150180c01d0031028006e008045405489290300c1c80d074680205a03647c005581510518902040200000d55aa10603640a410143d40b8641c0340e01c20762040c00a80922010440d00c504406524000105080280d0b40e610100c14807015031a0f00c032442080307196004540241019a0002c03400014180d80c29011000300d4900707a84040c0523903050300040e012650540070b0a00003901004052000c6001701c03008041c40c0f407040a8080c81c104a0060441c09820a406110030084e000800c0c04003121250249602c0000b0f81130308186154900110341d03564180c088401405035001160380c0d031080b031f90a0a444606200d00e0b046000103846442d16900800d05c82d02001d219628000c04a00386140e101c0542d1032660b8003502e8003a100d0308544003602d842043c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 940236663 1250 940235413 940235441
    0x1090c0509270102030714090a03060b0d0204180506011a16080f070b090f150f041103030706090c0605090d1401150807030b070e01090326070813080c0f0103 69
    0x440c03403508401640081c2e40c070b94620700b0001612400c140e40000c15140c840c2410070356805007800300c0011513072195084000c0745d41c80080000c002e000880407803400350264030003035071041c507102e2050303151503a090f110354040303218009036541c0c0da80322480c00c403111903001241c1141600c1031010000501c10030294241160007071050500380b0810a45000856202647c102c0e4800d2090051014003a0100900d0043d1402000a0b01241005550f011510040103010020386200c420102c4e00380001c000718045039140c054207480d0349512500700380001d0308a0a1040768030302051000094a584203c007601c444010041c4003040c04056a01c0e800f0407842200c00c08460386d5602c0c4015140f0380022281100181a0000034002d182e1550600180c10360000700b024041c0700700039a00d4072540c0c5e030100c150301c242c0380d01400c9102c408000a81204120302448000c5000e06000a194001d00c075013900a420f01010f00e40c80c40e81e14bd82c6134941c003a00c69001c0000d054024884500c400d500798081c0e000303446c0f0513000c0c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 940237913 1250 940236663 940236691
    0x40f0e07030f020103022713182301021210090b1f09170a0201020c0d020108010509040311010207080309060601091503020c01020f041e0b03060d020d0f0b0a060609050301090c0509 79
    0xb60840c420003020066007201c550340012800e9824145a5040e811030442c0340401c224144031040b070780f1000031490710000d100b4013003008200c40c1c0300303005881f100b101c411603002151a00c506c0f1440d00403237001035403d100c0c3c81c54210b2000407242c86600542010034400b03014400c8101c03804005100200003c40c000c3c0a0003030201d40401c8105107034000d002082c2000c0001c040840c0180006402c001c80324003101c0c0a415030300c45450150b6080100241100d0b81a1280d0a96680d6420120fa010300141e401c4805940000345000030700a688001c1d40c003038401340301030b59519240c0e000155902e4002d03201d0703140700741c4420f000002074a010364081c058100c45a00054600281030070041682d6120341c00c0301c0301c1c81d0070f11883c8400350054040000041c01c070300c101c000e285042500005450404448000340300e014454460780800c00c01181034521030303a00010000c45400c3c41ca076000083c1c00caa0080e2000030314201000a200d1030140905214980c214800004107030500d001e000075034000070003a203580c40b19 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 940239163 1250 940237913 940237927
    0x7140a0207080a081b061b0d0b15091801050604060c0c1e0e010905130b130203120d4212060605010305090102070c030b1e0c0a090909240b04060902030105040f0e07030f02010302 78
    0x90f050031400b003480d5076066032f940300c40f21402c00c488105003d44100010611900622154542c07400302c81c182c40040c104010070f003002e440d100c1c00c40d032500e41103907600001e44004980c00c100d90001d8482581c5440700603444503a2284803100440703804a40900343d04031502c00c010b021540002c03c03d50001d4041e049410101d0a075000b09207002004100c04004020025081c0e0103c0350511a40c81c0e20b43c0452002310311601d0020035115510880e14440b1090b0081c01c00018041d1040c60305240104103560365500d4401690400d140101110f1141c0740c0800c1c01c0070000b070b11034a018401c9030007240d4400f2404081a00356242c002c002c2c10001c081e51507040703000351030000400002001034402c9218110381941e6070b20000d0002d040e060b45501802c5010f05041d50400040d2450759405121030b4442c2244007070500645004002d41501d8a00e01e810520700000410300b55015002141603a4081d00c0a1180204010b003034422520102d0780c08100e03410028040c0009911181045110782c0149400340c14055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 940240413 1250 940239163 940239169
    0x30c0212030c0a050f07031211010204090e1501092007110d051e03040609030602090301060513060801200a14120f010311030607140a0207080a081b061b0d0b 69
    0x10104504500b580d02410f004420828204072141c0030144a402a166403403a5584442c2c881107076141c00c405000f503400e00445008000d6055a000f450038030307400e11019580c00d84050b15000486100c0c00d04a00b218004103c410541c05084001c3d46c0c002c0b042d03c81d442001ca0341c0003c1c0d8000341401c68802c070720301303012818aa49880b40d00b040d00f8010006004030880150100c02d40104540000b085900248403c0100980013524041126008000075a442000c40700180c0104203c0c1c100a42c4840039005000c1c07810001e520030b6051342e410130001c021601118018914101104025896000f020800a90160f01c21001d11b019001d40303496640c01c10b6034211440c200c9480c100c0d9441c001c0d0f85010010018400300340c0c0c0001c803070401038001d004c003410702c000020190f1100442c08402108001120360226100700f0605008000311400d5481e0403a0071b00c0c01d160641d02c221844400c601c1c0481d1103003000d4078080782e00b5000e5088002c2440b04441d044816280b2354102d6840405126500c4100481c951 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 940241663 1250 940240413 940240417
    0x603061302010c1b0f09090b0c210a050a0608160501051e180a090902093115111309180812010302011826011d010515120a030c021203 59
    0xc10140c28440c001414a1030445d221200b5a0000c10080c0c1030a00d8000070400c80c4215542010300e4103047c6985540240c042413808514403600c2c07003115030000800c0000d0030369a11060040d103001c001400075595880d411503980301290100300f00300102c894100015070052005280319100030f00e41c5400c6110002e00400c103600500840c1c104c000700d40c410035270b0a1405020007070140944500801c03140f0350b243c01245a14200400420301850742400a00a0002c8075040d82101c6801c4146045004000d1a1941d854050341d044041d03003500b00405810640810002d40300242c03203e11400d00c01c03a2800c148400600303034038812030310b003c9443c8091101240e03207500103200c03400b4904d1010b111949148001004402ca00300d11040100c000b00c000d000030600c9896022095009410141c020410710800500415803a8200f0650b500c01d402104099607042d00107920071903440721442003800c03115050080744070ba03103803049142e43c002030f0940c000070340509480700c4064005844036000086803000540b0716 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 940242913 1250 940241663 940241693
    0xe120c15010605090301290f040b030a08040801060b04051302032203052d07081819170109230c100210110a050418020c06010e07080901050603061302010c 68
    0x203000010760221505090040c020448032482d241d038407202c407c282c0c41c0c0307408410a0500d4411400004102c42543d2a500848180c074001400d81b6020744ca146425101c2d0b900c40d22810155509001d40003401c802c80b5829281250406003016070b0481042c6101d00081d800180303980072032205024400705400004c1d800030000d500c80c2c1c50306a0794078100111190790003040700410780c0141c00d500b01d820811500100b41d440c0d459103c070829440d031980d0f0b44010b400642c40001c1c0d80e04a40d8180c0200f4541041400769401c0703502001002035105041020113090794078004000d0b2a00c0c3d00800c1c6160750f5501400c020107001000741c15110030424040004880512069451300145d00021403000c0125241c4940b540012128443c207241a1703d803180a0014040e0f4421104071030326821040d2004007150f012941c3c11701a41d81074448642c1c4504064141c2c0c0015180c0c03070001090040068480501449000d010300c50050042c05142e40c1d581c5411801d456628080703040212040b201000288020b40c40744071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 940244163 1250 940242913 940242917
    0xf0f0a11040f0314392725201029090a0203040f06090609060c0503060a0312030e1005090d1701090209040902101206090e120c150106 59
    0x44600e9800c0c0301d4011181c0f0078044205410080c1402001c01c41c1000000a52417201103e444543c5c156540d00c0300c8240440c2c020340c201d101c060030042101500c2405400c00003d65600c17203100c0e100c1404a520142e41c7c1d0300c1130950841001003441d03103540106001d0344406a51415a030455565080c02414030302c241550303403140d43d00c4450140070385085441d030009462120445009444069000402d07200001e03060341700c0700d0740c0080030a09201c4183d100d5541c1701c0e0404000e004140751850010010420ba14042d00d03614030300360454105620540440c1d005100040c5503a085900b181c88000103030401550441c240359403100f26410141d424440041d8120420308001984d03d04034901c14100110240520300300580d2850944d0303407011449400d81034404038000181c84802400102c0c00400300e814000e9446040c80e5982040258000e54081c48400000e41c00d02403165980090415a14040704206040d0840b8104003051250007014010114100d0115803c156056540c9040002c003a004540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 940245413 1250 940244163 940244189
    0xc050f0a031406060922060203100314070315110901210905150c04240c020a03081803010515091e01030305030a14010b091908060709030b09060f0f0a1104 68
    0x1041d441e00c41e01d880e1b03109440b03280c0703040d414824046002d20340380041c0c0000c240381c0d40032001c0b40c070f01c1603801d40d42c03005194050500e2024008031904141d81c0c1c00785100c2112130503010a12603010040c90b00900300907007a9540418208031044006492005003501290001440060b0100c00d040d014007852a005004401603e02141038034803c060b0741034000e2550a00030000c0004120310b2000901081c03814000100c0c420021000c05021122018446006980200816004028005c0c0e18004002041828100d02d0462030003100b4076090311310403140e0040002d540b1603034460a0500010b02c642c449082003607001803803213082d00194030303000c21b8100360000b0304007101304951600a81306546d05070820b1903c64890b90b24204641c2458400c140c0d10701e00a06080c0002c55110600c000f1503406021000290303002c07407510600007041890988400c0d290360002101003602e000c4081080c0b409080d181da8812204c0e558142050075082010309155203103959908203140070415040036001420b110358680c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 940246663 1250 940245413 940245421
    0x50d0f2a080d0e1e0a0b07050f031005030d2c0d0602040306050f1003020a06140c070801050601170405100203100e091c030527070902130503190c050f0a031406 70
    0x40ca000c074104d041485000d5640005000003500080403191580d200130405410b0b55818022645030203140071024507820040280328003001d42c8041e0354146e42c02501100c4005c58403220480d21144188000071080c070f54400039021104011007000000e2030f0180c18404580010360314030040b41e0160f071003515490b0341c40e07050064055403038011a8100c1c0070100005561819a0001425603070a880798000380b1007804940100c0f49003060599203a040c096085c0e60003660384541140c080c08046940e40d00003000142142512140c20f40414050790700314008020040c0c4e44181071000398001f510350074400c20f520f040000c40600c685104c0b07200b6105030000d00004d40207990841c8080b1815201c00d0281070400c0d04004000c40d1405541011441c0901a01a2080303003e014600b03210080d0030150100c1d00000d90040440c0040d4261021150194202c5054038072415843e10742e0150218001c1081c0c601d25010880c928041a076071040c650300030314001c070482d40d91b50360a021400250556002e80c1082d8100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 940247913 1250 940246663 940246691
    0xf08270601081608120a1202070605011404061a0f041a071106030906150105090d030509122a0f0405250503011d09070e1003050d0f2a080d 61
    0x1942d581007049840c104090821031000c0c5c641d002e50324105103040b40030402d401043c2c8540540c070002c451121085545102908191010300001d00074030068074003085952105050621402c402c4078025400d00d80d0b241480b40b021b20456100152042c014101400045040e03c04900802c4602c5ca00110072540c8911500e040d0751036840d020102e52186030103208015a10b4008140741c1c0e44080c400600307060329810100166164041d0082140c0c0000c41041c903501016003181c01040c1580040714410f03200748820183d103549015074005d611801c0107041c11846001c00e10310191400000c01031410380d404454201160441c0c0c070854984082d500e11a00c020b407d60140c00c40c910085015190151a542c104294903c144201a922400040d041c07030008503800c405015410182c00c2600e49032a642c1403c2101030070000a60009950600402c0d000071407046c003401002c2d103030700c1d10342e125402c203c1c0b082d00c048001140c00310f108001048000100b000000c003020000c1080d85940740b03000459500d49004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 940249163 1250 940247913 940247923
    0x170610050a0e0103060f110409020a08130201020d0809011e0b13060305071208043605090a030c1505010602100c1b080f04170c01140a0f0827060108 65
    0x41107020303032030071441803041c0000c04141905603070704000d0215040d040c00300b90308001c004a038882c055203a004139000c141ca80180e0000e280b40b500390354684c180398451022100e4040e004200080c090ba020044c09003d080c050b00d085540441c00400010300d007602d281c241d01e6000001401100440da64441c01000c901d0a140341c4c0030b080244071b40c2008440e08544e52a0380ea40c4140c0941c01072000540032172002c00194134101d40103080030700180c402d924000001e0707018010102607010403552071941403000030310041c42100d11600860000744560351154030b05403201d1810101c10f0b181c2c40005100807600c840b603402024000e008035402444400400401034048800c3c2012940800c54160007520100100c03034242c00d90907070041c008640d541c1100104c0311b83c170303c22680700d0f03191860040349420760344034041043c1250040a03220f18a100c983d0054507032440c0308a0a107480402c044800315a083d80c850703941c8030745c0010400b00c011182c188188040b008085540c90358201507000f0300041c00460001d0003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 940250413 1250 940249163 940249169
    0x7121403070b191407031802040f060f08060c0412060f14100b120114061603090302040501090203061e03160e0115020f0709090507030b090a02090c13060e0307170610 73
    0x4800c00283c0c500a0843c4e10740100a03000701c00705034495510980050390011350607201c0da4000c10420241186049840141c04284903c0d0038003139180000141d0765102194040c8640b200404031890305040ca4804084156038240540c0c425a8542050408800500c0b443e8101801e00184103a030b13242c1202d01e041074064907081500514401c0c4054042202107504141c1901d2100300300d500b03a04510400304226014040081c0c0201544030507031814550172069150039a80242c5081c81903a07254803000082c0d1000b61106600002820304042080110780803490100c0380040a80300c02444401401d1030421840e0006080c86040d1001000440e0381604105924030307e90001d000c0d5103039001145511103089100b4810096240c05c20082007040511200003d5640507410745201e040419000e80c1d56400d030301080b400380d40d031000415850310105095410700c070850420221703801e050900c11a541440c102003d84c051082420101c6c0745580c0c107d641c25040346200c0144640e16141000c1d0101c4c0703c00b54 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 940251663 1250 940250413 940250461
    0x120c030b18090c01051329032403030414010503040609082b0e06010611210a0f0e060306040b010201140405030909010e042102030d06080106050f090907121403070b 72
    0x14141b00244002c00b0001110510a110140302c0880c3c0f859841200400c1800e280da010000f08000724032a504250403409120094607004401e6071505165aa10030381c040c0c0c40c1107500c00300ca942e02541c8500010f50b0302c14030580300462003142d1903480b0400c5400c0048640311400180040502d915001d41011210740024542442944c0d450340300710342c0364941030266004011907441521035210040001c0c03903a08298070704e1240090566908114207030410746030200010b00078610b0b0503440d44035100c1008100780c020125403850f156001040020001001254155500d0315003d604221081100c00c0c840d9000b480950368400b0920104065000c050b080b00c1801c0b0301c61000d01021650080e440032240b285a82c0350b41c441041c0002c2a4598094020240603190800b50f01248200041d080281251019600c0300c004004880400c40540401c032509503036944400020040d0f0004500c4540000d0300801e0a0344015a80d00c2e0030f5411580720050680c0c0c0c1031a00403d200a140420310f0350200c00c40e403c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 940252913 1250 940251663 940251667
    0x80c07050c0d3e0d020d0c150906030212061009030c0e04052107020603061206180c0103110d020a05070c08010b0913050a020d050f0a0303050603061303120c030b18090c0105 76
    0x21080a0300b00010707011030f0354010b03984080c41000b1505c2e451640e680c0c00e50000c90340d202441d61014185d40482c0d881d102c000000d0400900041d4160180c02540ca070740882104d807200c80e40e199400d0111440d0741d41e080e203007013084810380000807824124540000e01024030701d1304921300d487e04041e031400c056030000c0c55014064a0880d1448e0344c10070250390445a04070390342039494550a0024080308a0002c000407280a424144074022140700c01661000305000309030f5124644020040d403c542c040c0d5082162100f00300b01d00d0f000e4000c55070052040a03482d00380340707080003040e03100c00a030010141c0108045a5580c41500c0e082c1c50401103180e440a9603414a4241131403d541e0162070f1100d0110090045903000c4404007040301c140300400140000f04100e54105c20142001406044103540c1e481c000e009100109502070f220360202050190503490301a82c5c503000d920340f1002448958006000c241d901c14036210380b943d079286024000d1548503071804035420845252810150402012414400d003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 940254163 1250 940252913 940253003
    0xb030601120207081314030c0102010b010e13020f03070512100b0904090501110d0b09010503030703080708150a12033b010c02030f010e07060f080c07050c0d 69
    0x300540284014074044805070b22100345150010b60340c000c0c194800c00c8140815000b02e0082c4031010701900b0348500b14100c403c83c00d008401079007216410303140140002d1113031030505030b2410310390306102c4c200706014030042c5031200e16031400c1c810b40c1040d02c44400041000485100080340118a5500710040d10750300b0341c030607140a80e0742c101482480b00e03160049840318020010700800b9481300700280d00c5903c8442d41c0d40203202e64280140000001503102d841b00384000320b40c5003400400d48128940c1600c414001c0d0302c030b11405450b9010014800402c5411201001c00a51102c0400900524008406201a88c01842d02429000d41c0d04074009000440e12410812645101c1b0301c0303220400e001c61410102025200121921804402c0103034141c81303000129040040c0545c800c9220040d01401d84690b940c80e1f0b00c04540d2000440307005000225604003082c00c1c03102d450004c04c01c603485981211522005840840c1c45072030b42e40c0c0c0a03544c00740d181c0c210340c0d40104034000f242c21004410401c400c400c61 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 940255413 1250 940254163 940254167
    0x1303120c1a070905041109090a1b05040510051b0a080711040203090a0303050705040915030212060f241807021002130e060a0518060f010305160e1f0504030204060b030601 75
    0x40944503040c030658403a04400c06c0ea50b0003a00300ca9086801600002041c0b40800745000900446007000b140005505400c07500300c1e100d60151004d80b84002c12200f1411712900084503180c0000754641e0120340c08070f2200c14200c40401201400a200b8138046841d9403080c28002c0712910b02d000b0850050b80100204030603494040f84408000ea450b040004442e2503400b4105c0c0d0500940e0002540c0500d40814a85400960541101100c1c400c59020740001c20101003183c941c00d083c0d5070700100c484200c2c0454406140c80e00e10420060710200e1041c1c1050f0b00d00005840e150809601c29602008901402a040d505001c032820201001d0030551600b195020030101c50207640c8610701c481302046010450558541550000a01000700003c030f51184546d0714200102055580c0c41c86180e008840c0c482c1c6500174040d081c0309030200c0c1c83d4400321100c141d40035078040401c0e000c0140c0c40400504200c102c0000c10702d91440f0841c16650b0261210709610511040b10300b29041402580018400c11003160f03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 940256663 1250 940255413 940255427
    0x30b0406080a0b042a0e070512010b09061216020f0f0a030324030b010e060409080405010c11030f2401080c01050d0f0504062301030c0b1303120c1a07 66
    0x10381d009180f44410755071820f00c0151138040319403029000e52007000b003c54101c500202d4105980143d5403c0fa81500c030344005680c50310880105680e41c030000302c0100201c490680140500b4071010f4544e41ca02504000c130120982d0040755003103960b8400c4030360321a0140d41041b01010000620004144c1100d000703031210744e01d9049400040402d5201d5011142004d0042480790801a5014014126076187d11b80740c220700e0000d015a40fa07481145000a05914240c028500f8032904042c07040c0c0780c1b0f030809004480104c918817041c2d61541c1c0e8410040642d85042010701c58584401d4040d208041120702400c125025406a252008400c00c0c010300c610750700450515981002403c1050752180d0000c10100900410403800010344d15003002c2000b80407158209503807502c403080c5090310200c01c01c001c0491241c800e0002070490541c00303005002c00c0714003200503e00300101284c1003018540d255601079a0003044814500043c0100c0c0e506000c000454112104941d84400011160b190031030000340a0303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 940257913 1250 940256663 940256683
    0xf04260f1602090c041503150b0c0c090103050c01110c130513050a03080703180327050d0c031a01080606011b050102180f0307060503040b0421030c030b040608 70
    0x110030015080e0107059034101203281555024001c07030340514080c8407840320340d00035104880300518036582a9940340e200b071103055503084180e0311100441d170920128040e5600182d0b4420150b00c00d0300c6540800344c0c1d4101c0664021846400103010750a00000010114140020300c400399521030180b4a5213541d84100c00b240342d02c0c0d51507002071607a85007840c80d00c07a105160409029130203040740d410149a4070000d03191084505072000c1c850101311010b02c0e005032081400c00703000209959040b010085c1c0107800f0f1104907a0407400901c0040c0c0b65800a030240c454042c0465024404000400070420103c0d50030030704450942c10000e0310345c507201c0d64a0711500014101810401c2d800400c1d0590048000c07145041034015008644130101e4020710604103a861070028854265206400303100c1c42c0010326181a20401c0d61540d0558440d0380d2031400c52000a40210340d500180c55a140311011046800000c3c510342d0780d80030500481e0101c001d8102c0c0c8a800c00340d4050345c1055014841510002270b1482c4d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 940259163 1250 940257913 940257937
    0x1090609050a15091208030f10080a0b0601120e0304081209150c030f0a020c12011a0f06040e040c030614010e070c020d0507060906180807060c060b04050f0426 70
    0x243d400301401c00c0303808a03100c3d040b0411801301c103400281030041e1007018604c00e610754917920300c080d203a0a003245c0d0220910301c5007100c140e201241d610002280c501e8401e030000810b041800910440c50301000c01e9a00802d40387c10035510200341001203030001c011700c0350600c01d030801040c501510300740842d549002c054964403000c0e0740019510202034080040305c0c500b241010305076403542d410240080d15417442804451058450219407004808188a5040e0308044804038140b0b00748440240409039108012a6a20140070301c400070f28042004042d51141b0310500020700518158644141200e0040e981000240c483e18014030500c090013a0154000225040c811140304440c80010074081e80900024141e00501d0b60000f5115080380001003a2901e070f46518030380b4508107500b6500b043c154426980294001e407420808036003da003088460078001c0384045174007601007010074240c0e0f1007924204100900304041105106056010011118103940008080c40c41604560b805010300b55075518 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 940260413 1250 940259163 940259189
    0x110607020f060f37112d18010203070b01170d14070809210f0c04151509030503031302100f0f0e0f041e0b0d03080a020706020d02031501090609050a 65
    0x40da010442014050982c2010052107404020011703007a17243c000080413a011021440b099141d1902d0324042e07103c448050707600b80d04200005024826040070340300e015040d800108048400302d20b8210209010345060196050000c3d0409003003403404110319034420401118812852001d66040e04403440305130010000c82c1c85102240000c0c0c2c1c16410003e02c01000314425460802c2c00710041040c81100c03c0000c1901c00341c00e516410f2100b900d0f40705200c130030945c882480a1001c0c9000400103203010803949828400b06440b03a07070b2107256500c20b81e122011448000820710441c41c203040c070803c2074855403600c220b000d0407080340904590403070316400003408a80e01030541161039543c0f50b51400c04000b8014401001d80700384107a0b040055521011200d402c1001550132800c04980d84004254103a560850035642e6405a13402508521012154140c081004419607481400514000ca01d01020344003034640b02c0c0c001500c0c018050b03010780c0c1400510441000350b0390342c1d10543d10865102c020100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 940261663 1250 940260413 940260481
    0x417120d1a0409060f0f091e03110714090601031e09110a060903110423040203030405100e0915010e0112150e0406060b04051c03110607020f060f 64
    0x200041d0800407140703800070328164564050101e29004811044502882040351134001000941600c691a00250619040a201107056405880a090198007c2c50311b619102e24150000c1e0400e505980503080d0754200d0070031710341c0c00d20f0410703900394000100342410000b8040d5000d02c103032002107040b8603006003a81c601940c0709000f280b0942103c0b2041c02040d492503d52110340182c82e4a005000944159102003002480f60820703114a01400c0110890248640380110510280c0030300108100d03010702051000080030745030000070520140361a01d40306070400d1150144040301c0d0000b00070100000c1c3c064412074880e60040c1c1040c200c580d082c42c0603080c4210940d804800fa00494550708070540c2d400c0f100180d58003c410405009520036038052101541c3c0e00c0c01102c8901940c0075180d07000c116909140c46605008110101d5184603007040000b003140c8400c06810040126101c0000d82c0061700e41030700c020001c0c0300407a80464243d42c1d00403c1d0a05505600c0740c0c00c100410704100b158808000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 940262913 1250 940261663 940261691
    0x803092413020a24110304080c36061e0a1517010b0703090b0403120503191d21030705250c060e031902040b0f040f020417120d 56
    0xb20050700d151401204d9001180001307070352141070340b4440d0380001d81703000412415080c0802201c0032594043c000b80913540c1c00900704220700004048100c41041c41c8a40003a0754840300050040c40c00144d080444c175494000140400908050541c480e18282444001d59550f109581c5c907054a8414002400c160807403c01541d020719484900280104118000600d400c03144c80204505482a42d480c180d1a994400c507400174003903404010042e0580d01c1140704030038070410240da8806000d501204d209482005050100c914281001c0760b905202c80740b03640f02c00340c01c001e907104034000c1400e500d00c2d80f120706001c600e4500001c0c000b90704014002400c203140d071030301e8104814003401030140d452f440801450320813128034151003140045000d0402c00c440615012804800c03424510100100704101a0f08200040682c1d0f181144d106804414000454995105003c603588000c2c0700189d0f00c0d401c1088606200d407003104e92803015400500c000e102554414141c82da0000b00b0140030400340101e1b014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 940264163 1250 940262913 940262929
    0x8061e1306270501060609080312010e0402060712080a0b1c0602221415030708041103192609100509010c080d150602160b03090a0b04080309241302 65
    0x550601102e1007942e0041c400190b220808403411520f0341100140e880d40040e80b0381c000e103459403030a0103c260040008035640e07d4415840392009255603c0c104450361410b140c01d2441c0003040c0000d60b000300b00b002703449c0c080c8500b00040100300d807186415094121110b802480c0010014003554010580511848507030f0040302900c0500c82c1c6240c1129166601c904d80038003030f20501c0748501850980b1b501c0c404800e038112030060f00143c0d0740d40e11554850302c0e4020885c003403981030f43c0c00d0320882c00400b0104c00c01c20391911007207200d1481c2450107800310b110ba840c0051105000c00a2400c10020b8440c00e50758440032421410084c20711036240c991442c0140d0345a800032b0b86c080e02403d00000d1101020032142c2c800c100004441c98982c2d43c503500c500301203035076448074200c0039044688448107204260114029542c002c034142c2c103d940c0224030b03940380954030005990031a20300c40d0100500031051030912040c440c4800d078409810030f40302c0b2851009000c0c40041c0c45000403810104102c015516800701e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 940265413 1250 940264163 940264211
    0xf0f0306130510020304022b0b1005010e060f0717070807031e020c01050d110f070f030f030504020f09070c02150414010c21020f0708061e1306 63
    0x1050358040c0c034150111800d03109500d030040700c4900426820107040840e0744252800f40c2c1d0003900d039408070b0070110030104d04208100ea11856908540941200260495424900c030744110301c501c80e503951500700058260050315000910030403080c001088036404102c1503505e540d0f00309080f20901e00611841070510301c140c6101503c0c444001494130180b580161000d20030711a4900c40055101d00c4000480c0c5424041c65507038006038007045403030750402c502e400c0f07041459940c902c0203141007400840c8040f60b03403041c3c10885d10801c03d00080428181c002c0a40001c0400c5410f050001d803425600040c0b41c03030602040240300743c0f80200482c0b119481519603c102d190701912000041c01d1415004800fa002881140c400c503003920360100e41540700300905d001059200140c18850714080c0c048031b114048140c0524114824880c00740480d2008010f10002400b0101c01341c441820103034840c441c120084048080b0804020050009500d40d4020310b040c8203401031000a90f800d40d43c4001901e402d4503030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 940266663 1250 940265413 940265419
    0x703140a02031305180a0c03062601060e01060c031b022206050d0b060d0611070605070905010c0510110915030a0501091103040b0702160e06090105010216050f0f 71
    0x45012805190004000e180c0d50303003004010001e0344d42d540204508a1452a4080e01c600030a02c0030039541c40d40c640041c2409217085c140032400580300c0d00c004c111411101c04800310354003072403079000804000f03200e202302a00e9100c401164a42c100345d0f01030100002204e00404220300c0000e81010312514034144810716900401d44d000389401300310012030301c04150900c80d020314500400010399140c03600b20028040d070f00c000000c18079074940c03080040c0404000000d8411a85405040ca1810f0f803050043c00b141d8442d03000020181800f071b41c003e0ac03c0c2141d40000d4140b02155141d100803500000d4408400a42c11201040b2841052084801170055019150300004554000920303100031a01851042c90004d81c2040303260391303a84117107061350514034040c103a000b010000b0401042001060f558802740d1401113900701c04106043e501421116031003403000b4460301d414404507241201c1401d005007001d20040503489900031000d01005811710440d4898003421070301c000319442d40340101840c08401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 940267913 1250 940266663 940266667
    0x30f05010b031e01120303110702210c03060f0c0304030e04061701140c0f03090a1e060b0906030303180703021306050112020c070e2e0830070314 64
    0x54250000070b82003550300c00000e0700440d01c2ca082803400b0100090484600728040010001d5648054004040b150203848054004001c80380143e181c18844550f40d586100407a1001004101d80508102d50801e44510070b80005050008540c2c3d03030a050f6400514000944d0355035100e078502074070050b460007945a006401c000001541303842840707090b121102200002d005100c07818002486191041b60004900c440c140a58041d42c00c5000103185e20a480c002210305122a0351181d001039200ba00315079040d00c650a01c10410060345024000054005844030a45800c01c580000d0f1640070081400e030f881aa51690303900413140c04c126410045402504d10380c0d000c441e0f0341c14400500103030b0040901180781c0070030384140d9400724401c41703400f00b0700100075040720350800d01e06200004c8090040101d4001d0582800151422028030048050b49001740065051a048100d418a40545400307541d00d130155544440c422104030f0f40251300c244020345c5680d00c0308175240c01d82e0a111030750212500d0000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 940269163 1250 940267913 940267919
    0x120902150316020c091b041a040f170c100c02060d0914030f04120809091003060507020f070312090e07080601030b04110a03090c05060d020304140724030f0501 70
    0x30300065000310048001400a00c04181040ea5903048404115070400e03054400035000200203220b01a0310700004c840c40d480c059035203258807411608061807582664000034100303c8000c1510006004101942d1481980303c040d0106640350700383c011055024242203540d103840c032407007002c030188907e50040400d6140e0b0700c8038840740c004005405044030341c00c1d548010b40300f003030000109030b03031101c0c4040300214074043c18a5044026204061000c86030014140700c030300365595801c100301d4458680c007501d1a40c15031071810640190f40c006082c14095411680700c5070002c003000314181c400c0c3c0380c0011940200c40b080020490307175581103521600400d8942028032010684c4040c10318010130090b6000c0c1300000d078280402c030840d490720700750621622080000e618401d00a07000326004a0080c006c2d00c60040e0741d88007041d4a0740c4a1060841180c1c0c1c00010081046800d50ba0100c0b2801518001c08040307040051aa032000c10046003000c6a107003903080152501d12a4100307002920f003000c010320065075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 940270413 1250 940269163 940269199
    0x62a110303043201030506030a17040b0412060f1a040b030309030d050301170606060a0e0d051e01050f100522060e04050d03110a030207030c021512010b0304030f120902 74
    0x249040b00428100c0b01c0e05074210f9641c4a402558080c00d00140030300110800c0c2c0e43d410a04002020120f00848000d1000040c500c4910000d0802040d85254070410405640b4198080700c1360b148901d00020300d00092540360a00c50141044805010b0314000392051105000901e140600b0040326850302c5a1000805580d502c02c02a40c100c075016039251220810220703c05031102011070b1a0340e0800c2050240028880c802e0004c90403001d23001e4100d040e14070468641a0030918100e03120401c007504a030b81c804a00400748142d0780d004000c1000ba080600704129000360403581c40c84f400d44107401703080c1615009140c003075111a82d80c0100c1e0041040c65515582d105408008540c2550280903a82a07100702c18024090001d003140100c01a41c80d22440c05401da00039009000d06404004e21202c924005882d0129107508011151460584070352950840d5007440c2c005801101c81140c0034070501c00003a0700100c0300100300c0307024207082e5802899014000000d11100b4000307035114140d0003006034110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 940271663 1250 940270413 940270469
    0x20a0207030f0f0b0a0e0d2f0105010f0506031311130612060b03010221092e051b04060e12010c0c02120d1d04110c07062a11030304 58
    0xe20440d1084032aa46401701c0104a42010301050700d5030300001c81120206100d04084854243d0420305280c50303a507009640303e0200c40c81040c2100aa65880c014402081c00040110040c6412035071240745140070b4132600814852203400410034006c4118010345503981d5501c1081d07038040d0b0f5000b007100d555545608610341c0d543c1c4a040d01c43d58940a84400d4038241030080ba003c8180076140a48001c42c840480317000200000d113030602c580542800144200c90007503808805070904d00f00300315001490000791040703850250881104c10244040007010000c0003060f203085600a04017900140c0007440810340865403150415403c0d440c1540c0307403200c10341240d0b1f4007180368002e484000324180c0001c001070ba10124485e82e00b020480c20112900004039088205090b558040e20119030b040d42c001a210094100452824950300448001e000c0307164811130b8012440310340304501091120b42415108042010381c0090030215a403848450503403000c10449004140e90308035034828145903113441000c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 940272913 1250 940271663 940271693
    0xf031512030a1205040f2012150601020c030a14010209060d0f0606030e030d050a02070203010c0c030210091e03030615030b04050603070f06110c0907090512061504020a0207030f 78
    0x440d03075405540f80c52090f181325242c03103198454000d014080c216200c4180f01c02e059500c003d200b070302d6404904aa0b48070107400300440081c040091040c01030588482181d140c0040405045612403c140c10307043d03400040c02000544c00c05e00141d9000c4034a60894003a110b0a40216004040010900c2e4611100e42c0184074545080c0d0080043c59141c1c9000c905603a5a4030b8107042c1d650080c400400c86000b03039072041d60411030054005140c02000d80c042030a541c3c0d040244d00103d003928065000b4980c041c00980400c103001c8004020000301c503504d0000036520040080d02c0c099a0803601c0c01014000c1e44008094002105c100c0e481d01caa0400003805002840d0711140101d08060104010703003030020314841030fa203411951541103800c010080321000c0b0807042800c01c038421b86800101b142c8602c01540e01412540e0303180a605401c040510403035182040344005a540040c0410201d0400209c100d914400100c038096642c402c04c83d0101e2801c0000d0f00082e014445003c592410090303500d504480c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 940274163 1250 940272913 940272917
    0x1906030506030109033e0c010f0e01020601060e01120509010213061e0516060e0c0108071806081306061206060b12060402210a0504031b080f031512030a 67
    0xc107954020925003030307030074104c401400700e0b203240c06c00c100e0040d24140b181420007401c0b01c00140400d4503581440050b03020106000690098900c01c0c07181d5a204044103030514950400e000f040c01c20782c000035501c0c041441480200440d00c40d5403056607104043c00c1d0621008207005116038240501814002e502c10340804a61030300c0642c0000d1031a0103109120314517080528421940040740c042034440364070042c41c142c034081b001400a4000707104ca10851100481c500c0007005068105000036100c110083c0041007800781c41c0c50780e41d803540d52800154055420b20324013442192640c140c0c4200c4c203840d0940081c00075040140c04600c106510350100d5000340902c1050103c5035445480c2030780d600c40c44c1125806207444200003500783c20329800601e543c41040c0b0742a0038041d0090340a18030032405980602d04180c440050105142e8010008142c0a51072a450450009170b0f13a03c0d401c40c1d00c070358080d2201541000c8006040d0b90b19803061b206114601030026000c60f4201c7c0d2500c1d80300d030320042400c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 940275413 1250 940274163 940274171
    0x50909090d020705030c0a0e0702030f0a0f031104050f01031d0109140607170f06010507060c020d0908060c040302040504050307061b080f10050f131503020f0d051515190603 76
    0x144c81c03500140004018030050400e08a071814103140142082c0000d00c400c0075480208803c40d098225a0700404409206a40d01c03c0b80d0301069100400b03843e4003610f4001201020300c024071860740c070000412441d103400d090005104403100e40240558081030f210420551800803400c050105d500c208501341c081060030754940d80e071000f0095800e020300760b116044c1602c1c024001070491407000c4081c0c8e00181e0504099060841503039a000130b5079041380220006030401311f210b5409030b41014000c8040c2c25200090010340c580b0300030200d03281c003403440080d1045440d40c000c54240300d82030084800d01c40e0400414081c01c082d003000500400c496840c00e00019910b0310004c2c001d50100003509006816040f424405213182408011014400901c0c1f5a40001c0011038012124494400c003249202c2c6440aa81020300c0c2d401004604100801c0c42800342c03c4000702e2000113840400c08400d04000c1225111060711180e019601d42082022a150070070042910440c0840c14802030748103d0b441550188 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 940276663 1250 940275413 940275419
    0x51003110405071b0c03050318010807020a0822030615182703031517070602120a0c0c0b03150f0102010905071703221a0f0316050909090d0207 63
    0x84100c034800c0f1020300024907811007a04242d0340c0c000303580080c0c0d0700411266076026281c0e12003904651007407c0b4a00c5c412045030b02d0030040c0d41c2111b281c81e4841d481d030015041724031003034032000110311402d426425400500c50341714142844a004282c040d41d0461000c02600c41e0030480240505c1aa0180c4010012103103010410607500d40240c0c2c1045002421b042a41d00003c007000340c054113414422003e06487d451700712418880a40c40d20001c050030385106513446c614010143c04c294158024100715080f48600042110f00d1408a41c01d4802c4e0b40350640f00c42d00c150811050502c0340d5040103803980400130a2002e40342e04110102481c035422181040000c10b0306005908031401110000c08a0708803510802071191040e00d5000c0610006003035900e080340454a440f900550041c000b501146804010b200c0441c221380f10010701c58a48a00f41d00c2d042c591586001240001410041a500e0f12503002e02d00911075420340790407900c050200c07205810a0f002d06603c83d40110342403070052259542c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 940277913 1250 940276663 940276669
    0xa08091513030f061116031e02031b0312040503071e050d1d1c0b0703020909010312120203041a09030306010c020d02150307020a380a0f05100311 64
    0x2140103140c2282000115442c40e40c50290000200d10107541456880d080580c0c0c40041c80010002d2604c0000201d180070080c2c6070140c210f050006c1d113841c070394420030b0003980c80a40010803680c02910765030000d0407558900381c1d00c500c1c51050750140460040c0b07400500c020000c0000c0074160151290510649140c0f145400041c0c044c118980540f55a10040c0c03869000c2d0b000314210081181c81c4105940052414004207070b011001450402d600282c2c0f921a1081c000c195605079002141c40c6019490702c1d9000000031b2200c2c1041c080500a000d10301c030311141c0d160103040c0320725542000410540d00c9140030b0a000c82c50600c0340c4d20000b1084010707000103008040c040101d0784150700c140c540202522054091088070200c07020101d8008051500c1032208002440183d8480c00e000c1e03000b40b80d00c90f850700d03001c2581203a0011840090602480e252044102503402d0305484e031024600701016910032070003070050701822000d00b006900e00303000d2007000d00c00d0b10b181105030390050440041c1200340c00d080c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 940279163 1250 940277913 940277917
    0xf040e1f0209060d0f060806090703170c120f0c0601240305330301111908040309050103020a12062306030f0c03040f120c060b091003060c020304080a080915 69
    0x311a0f01c0202000300f54007040c0319900c002c01440254800050150b240d0511a203020002d07924401d0765400418100104080d950501d03114003c030306030460030221516006a0350329110340e5081180400441c5469040d4206000c0c2c954407009201180c200356910750300b4600c103410b842c410314040c440410f02e2002080c0280a442d00641038000340a40140a05284842c00c0c0c1c07201c44021010140320f0340c2c54005030380034010440200320304885250b43d00d0080010b42c8034007000d00b04507400e0004070005c000100780c101d07c101e01103510a0901598485103540b0480d4520141e0035008189450b01401280072140076454520709450780d05281c115030030b00c0d010000c841c081240c05901290860340001c45952005029542040c458600007803502c0c01d56a454803041e400e0002c17600020304140031030003442080e000710034410780305072010b280908280f000c12041c1011404003910640d01d40101662581c402c0007124020301d41c0c3c605640341403c90b0300d07006290b035202c2c00c48030380b060316040c12a8160b4011031b03003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 940280413 1250 940279163 940279177
    0x10c03020f251e090b040f1104140a0605120403120e07080f030408032505060a0203060a12050a0219171f0501050d0f1106030a020a020111090a060e0f040e1f02 70
    0x1c183d62495142001d000041c2c0301c2c5500d110b40180c1c4aa00d41c03140588280a95015200518561519242001201425100c3c107480c1c083c400c80b40f18031704000340364124040794a04144400c000c000b5030341e103040c25103480408040e1044030238946000d0889210000c600041074031a04419182c900340011100c56683c0101d00403002150030400c14030b10001d035401005003140b00d04c0310707a0308441d0403692150340c01c00c04101c5250030116000410000d1600d000e00011010744045056480ad82407a42c17a1180d5440c0c0d1600c3c001e0103020300b07a00e8844180603030b44400008010340d59001c2908030610280b152203141491200a800021000018500c1002d00905059550140c050a05200305844805048051200130360700c20101c40d0454400c0c0e141e28004500c2203104000140e5614a6218000d003103a050b200a521041010f21224241c0d0f684c40031601c04441c0341c1e107410005644e0760000075424118141031258002d1a004510240a0021038241e0019580d1000880220034024140080e449218 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 940281663 1250 940280413 940280459
    0xf120c0b0c0315190f0b04090b060a0f11100501060f12060b0a0810080a03050711030106050108011206060902031008070605030c04170c1201150b09090402010c03020f25 74
    0x1550340c25424250204100d0480030300004d80e00c6940c0381c03418010692950040f00c10f000000500b0b1103815003a0140d5a60341c02c0540c5d030a4a031090414004218400100d41c560405c502601061511300c0e0070440b403415981c8800c070812407565100f00c041c003001c110392402001310345a00000807100d0050711520301150801681030f4a0000b882c40c0c1112604d00c01051040f0001c1d10100100e52400100141d81075a4400c3d101c0680e40c0189051405c1c8a40300c005005210740c1c18a01d00703012076644040284d0450b0704981c2c400c140f401c1c0501c0e10300701501d1981c2000c04002d1001c0200300e03100e140c1031100c400b16034081d0152500e0603101c2000320b609110813640020504001c02c401c20108010300d4107000440c0201c1e05540748131103441f0010701c62010349080400365039152480c01e4050419042c1ca07900030000d000025240c000b405010071101c48000300068184882c1020440030316009004020032107488000b0703101c55191807024070340800841c0d85482c3c506406840c01007184050314668400d160460 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 940282913 1250 940281663 940281691
    0x3040203030d0b060c0106062c0a170c0d0606050f030303040b040b060f0616030e010c02011205060a1a1305061c0c020309030f01060801051e070c0f120c0b0c03 70
    0x3151110081d1101c03005154110000300289036445d442845090060819a5100c0072100b400055840703c045641142c00c00c0e85500300f034040c140360f6901c00898111030010304510a4400b0b40c1104508003d4654000e42d00649041e00c940d0400c000750f8041c20503580102c4610100c0700e150010706640e804100c0e801041003441071b01142c08201d545010b55408080188251041a4100e000c502590031800301c2c680502d1803403501034109900240000e01040080ca060100910315400003040301206410700000c856580e40440d005440d0610320b00080c01c440301840b03801c2c941c400550f4003580c1c010f420b02c0d620100781c410003107011b142007400c45038207042460414034030480204040e40141071170320044d400d42c841000050000e450a01c512003201000ca400020244d1402c5406800d413880101240c030259000c0140107000305408060b035030000c030341e1700d001c41800242e403405444041000e280682810070840c29000d99541c0a481c607038110344100d050004685540c0700262103400290717010726881d000b1f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 940284163 1250 940282913 940282927
    0x1080f06040515090c0a0e060a06032304080c030406050d0608030405010e100909051905130302120307110a211119030c0c1511060c09040506030a120e04110304020303 73
    0x1908041d60004c6000303080d21454803c00c00002c1303070494240d0000c404d000305003040124034580303564580300419150400340004ac40c07020413400107882a40c085845d035995040071505210402c010f413007c03510720300120307076403141c032148040d02a400001c4c1d00301d5428284940800d4100300482039030200d4506859a202c0150103d04000c000940d403100f0b1420840e40c07880c00140c40b44540500307400381050f40110040301103898000e03c04d5070001084c0911030f024018810340040d90000300000a0103007407030038548986501d5012600140442100035161142d501204207020101c4040d403649075200500143c09003040009841482255a00800c9034100540c400d0082d042400d503c24880d01c2864508120b0096503a484450802500310510781c1c5840c003201c1104030340081813026072200740002824685815514219288603540f1442e00071760f251008180c0d503403402c100c0b0b00b20081c1e125003014844000c0b40f0000301355103c41c0103400e00c5242008000341d002d0092104503800340390003a001d103103003030310f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 940285413 1250 940284163 940284193
    0x180a120b1e0106030b03030d11190c08030705030619060206150306060a090b030102090619090503030f072405091606030b0a09020a050408031201080d030209091f0f06050301080f060405 81
    0x21700701002d1600340c04204001c04480d47c50b485035041a5a0700943c0646440c02a5180b01180300c004a5a606101400c0c400402040b0f820b000c0d20f07404001032402c1e40d40d9950300400300300c00c1d072201c00d00f05110a41b401c4000c20b1003500803415a2107484004c5410003103203494401c2603640e84007610b509401819100e4280041d114a40102216980140015141084d108042201c59001e400e8030405ca2400c80303d00030117954003400d21401000114025070904c0130301c00001545115080c401000c00181b130484501071413141e0500401c1030704024003084a0301e46203500c4c0d900c450005084e564402241140403d006019100d02c18810101506016049040111981c000e60008004105024080c4000550110104010f01d192034440740e08094030f52406010a01d041107d03044036080c9401403094030a5502c8040b6056400030100905030301a844e90040c142641040790054606c4c03580c8070703034085840f54005006504035200e160440f60164a848032090311160309440003000d54100e60f000d155004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 940286663 1250 940285413 940285421
    0x140103080910030605031014280b030a08070809010e2413030c061d15030a09060b09101a18060a0311120106080906041205180a120b1e010603 62
    0x40450030001513068403200024a04001a000c82000d103031681e90f00c0e185a2400a20150004102d04070360340c40129540032180781c46084141e541c540c5030b03104010300c80e0382c2d0200100e10505411200150707907002c040c1000319955100000007804500b144051850b40c0c2841c0c90341c8400d402005460303032480d400880101616078441c44040034071000d40840840400c24500d40c1400809d140c0c2c644a540ca9614525440180c4640b081148200717015100031740c202c0c0400048079030002d4600c400040c83c501601c3c000c00202501903206801c041c21501301320031500c140c008072017a180c102c912402174802d04121104944681c10a03c2d0000095030140c004030b0400780023a210811541c1004690b0681550400000360045a404d580c80d80c4000b00400051b500310413016048484c01c40a02264a46a104d500c1031410071607002003048000642d201801c560701440052070b81c0c0c014131006070380d583c910200e40d080b041303010165141e40d00080881c0804072030604002031038480308088a00381c0c3c80e010f0300350020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 940287769 1106 940286663 940286689
    0x1080607030903050403120c0606080105090f060c07060c0507050f0318030a032a0206030906060102010b010f1718030d1515050412081317011401030809 67
    0x443c4d03101c0126800d617a0001a40c08011000807012210749840303800180c1054540000801c82a4064011501030500c0b4000c40e100000c552a042e40c5402054a0b110740c60b00003000507000155494000011840345400c1060426800303848450824407400c6d85614950000900055405510300d030700500e081003500101300210055030003400c2840d249181100c02d41d218003c0702480c4650000d0301c218182c3c05442076450b81001040e042e80c40d5000e0b11014095402c10000001d15442080c50b01000c840b240d84000c040d40d40c00101d200150b1021301000d021003141c2c0741c01111a41c0c00c100500054001c07000024804e00d0039070109041c100305402c030035a50140a20070b460340036401341c156001d503019190791400018191402445a2049212048940141150004165088a0300c000100030400000e1204030540720468400c003c0900005000750400d00040000d8280501c1d44128 = true := by decide +kernel

theorem cover : BRFrame.Cov 940107913 940287769 := by
  have h0 := BRFrame.cov_init 940107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 940107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 940107913 ≤ n) (h2 : n < 940287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
