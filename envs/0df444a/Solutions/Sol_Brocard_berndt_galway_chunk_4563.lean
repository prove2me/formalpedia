-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4563
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:01:23.959466+00:00
-- url     : https://prove2.me/submissions/01a068ad-d935-4191-9651-b9d47daab813

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 820503597 ≤ n < 820683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 820504847 1250 820503597 820503613
    0x606040e06130303020a022526070303030b010e031911090702060a0209041103090d030e031215010315060e100f1d060c160905060108090a110414010602030a02 70
    0x12001c5103851080c4000318101d02503000d9507070b00758020b401c46407030b0500314440c06001c0c84540c10101c5403d02400d50403e08051483d28183c000d81801d2424442140140c0d0900c201606007880003c29500b92035046c240801c4240d450381c012541c89000038011136040c8925100382170720080980e62244028010741c0b800c0c20701d1991505200c0c2d404800d49040d00181d110b80c0c002004041190f0160494480050010440e5901c01d0141026600191165241c1c2e40140903075045180c0c0501c6031032a843c450703501450402d900d0448040c0506401080c41d292a41c0c5aa58030040368440c0e88910314a006044221a460740c40d07510007040c3d544890302c10380c011500c00a4425045010ba941036540048507915652809141880c0500241e020414aa00705500b03200301d000d400f03002d21401d1400c500840324440760514015690081e42c501502407030501c01082c06000795030101050003240740f5000050801c583e014040810b004200f250500303803d940e0359200210300540c2c044020510101d80e039013215480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 820506097 1250 820504847 820504871
    0x31e0c1009020306130f0b04050313060e0d0f020a0b1903050601050910050703020f0f1b0d0803040b1e0a050603100e031b030c01051302100206060108011a070f05060604 74
    0x803001d881029605a018000180e00e00880e1082c10340c955108181030b0303002100035a61500c03100740544080f10141c00c085040d08240d2854142d29004104602d8040300c11003040340440d0415a041c80b000e000e40c0ba400005406644580315080c0042c005080100d60315081002210388000c203c127403980010f410140414865032045040d5681c0400080c0f00c00300c1d041902034117aa035030b4800c10045043d8003c0070140804040c0500400540e0130350300d005000e45008582c2800c42d4090080c2801e440740031903501400c04a594a015640d110398040c803150110b850311901c14500004c800740b8812080b03001d500300080452243c206e0343c006d003025030403140f000c00680421401c0d1025030040440b25882800f003c008040a40480c2c0e81252014003500d1410310300300720312030945000310784070000b103190f54401d2070842c01c2100315500144001d1025200070300b40b900008190b2441841140301d104510701039034040c10180700480d1490355212541d000882510310f070560f16410210b41d014820303440d01140c0d41003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 820507347 1250 820506097 820506101
    0xa06050906090904150e0f15010b090d02120607051b0118110f0406031101020d020609060105010f0e100e1207031502071e06051906080c0111031e0c10 66
    0x5005000d00d08081c00d6005020f09444020000e0314600d403500e0040c50714101d07521038844034800480c040e00b070301c2d207101c03039058a0400c0d88850003040300000d40041103010750510540391800c404841c040718001450001881c0b4410001c520200c40c058079061150f0741744c118004200340c800c64404030042e0a84011541e0072130f0348202e036110041c01482c00d000300003140650584030000c4002c0004e1030401d1940c0c003150455010b81c1040342e014401c107140b02170540c2c0410402c240d64503244000d080501e086010350703031101410b101f00790500c00c1d421022319034140503c2d8614000c100261103c03e41072001710b002407036005620450f40c000c0d4000800051600d001250300c074140c9400c0100e0b81002031032010040003d51009071b080e030b410286482e280d00d585c00a180c80d1484140030b2203010506041c043c1a007014404000300a180c171501c0c00d40700b0080724070046407980d80b0b001c3c2420b06001c40b0524020341421441225803441c04d405240c510b042007144200301070040c2e06c100c9c5c011502c102c2110501241 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 820508597 1250 820507347 820507357
    0x9050a0801020432040504031103040602030403051501060c0305090a0312120f11090904020f04110c0d09140105031e01090603050c0d08030402090901111b16061e0302090a03050102090a0605 83
    0xc0400d095030044c1c440c03400d054000d43d401c50310034a0400650f00c0140c03017060544d04184c0100006030400203040003440301c10040f10700c444800304048102540744c013501a01e1054015802801e110000c80c02d12141d0b51580c1540c0d008580106020540046103800140f0140301008a02d4541c0c0c540710002d908980d09200d8003c05003908500f45142856003020480f40440080c001c80c3d0155003184251203944990043e17008031182c2c2e03200c9684a142e2080880c0c2000c000001020401040c5441041203080076000010320040a0810303035541e446007001050f020b180c1030450300034803080500018100c551780e0706c10001c17a4042c1058074180c04008013001603560020002610000041c0007240251a100c80142e0f00244000d00000e080d810b02c05640c41150060b140d21460034032003101c04c8603100c406022010308813074034a840d403c1040c00c1120291003006d21403020b0020302c14112604401600079411138226240c02401d25010315520314210703000c3d42c0a00350050241092407000100306005009880d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 820509847 1250 820508597 820508669
    0x10e0907060906031a04060b270109051e120607090812030403050913050a1a030c1003051003050a051b03060c090409080f0d1a060906040e0709050a08010204 69
    0xb002d401d1801c8421006000000d00e154100c0c540701e03440740601d964a203d500001e150b00000552070712484142051704d203a2650002040d210761684003540b580e40182010241d40e000c8661032074072201c0031084007030008803407c400c3d0065804034001a11030000501c052080c0c49a56860241c69150081a03894203000508129810014804100024000e802600150101420201c608007807020001d0984405450704c008490340c0c0c81c0450054070392800c101a445200360028480354001c1000300e44103c2c0c0f021118000c0550f00e0000c5070342940341d98100b000968200b0200e45201d00e030343c01d00ea52101855109400034034220b8106041d01d0802081180c4510381002d00b080c01d06031500103000103460384c0c0703030100c0c0c002d00b04020010b004103c03034020b440300904450001421410002c090042c180032404900e2203642c007400404941d59070103048600f0340b4498120b071203454860500c180c40000b400d41003c2e900ca12449008161910150b020300129020201d20101d0300e01c2c9840300a01c0f903050303d4488 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 820511097 1250 820509847 820509857
    0x703170a0e070b0d150b0306030d0306050f040b150c0115080105011d040302070f090b0a080303010515071e0b0421050d021e040b1c0209220b0a0905010e090706 70
    0x200810108035024000813003464101180000c001000455210390f50f42055200c0d10020082c001641420041c540c10000e140c1020060f4505010003c1c0707a00801081c070358412501c80d00a6255a210b500100340310502801510740c8400c10198001e000c3c00c5c01d5401c0120172040300900041d0314005020303090480300d8039032007056101a8407503940000500100190154418040002944554014140028a000030001034101050020085030350301541c0440125807040c0018401c6940d02e2030984a40f41008140d66031712851854000d1003111180a0820845000206076081c0034138222030038455482a5140c2040d0410000001021880b0035070220001d8024000c00203180c0c403541c0104902c42ca0001918808681454680d04c0340d440343c1c105900160000c5490030b03808400c041724042510369641c0c1581006940c20125a80b80c0302c0081d15405504000c1d010454241c15600440b071406014120740340554907090200c0c00341c2800e01c140c92214158000060700790b20046815401d0710341381d50399 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 820512347 1250 820511097 820511099
    0x5060a1401050309031303030f180f15021216050f07060e0603061c150c031b0305042301061d240f13050105210a02040c0c0501020703170a0e07 63
    0x440c0d0b035070801481d00030548010099000300c10404526a07008600c80e40e151715401000841c000c00c1c08100045114501050310428420005004880300a0300c000d1440103049004050049182010000912400e0784e000a03d0f04495002c40c8400c44150740907030100e0341c502d41c0f841e158541e00e00d1544501c5001a8540c120050300f0320f4148000d6030841001804403401150301031481000b075030089403c035484d0301106e80020344951640241a002d01003404c041003584076800100ea81042d0803400d0100305551240041c08019a4040345a416a903412101464600d0f800701c0e203009218900aa510b01e50f0b140c01080d4101076a802e85c1b85c85220324000d403040d820108105441c000d50301c80300a83d408100d804e000040c40e1140001100d594141500215041d40742a0500c00c4019080d1302a03088107102e80b000104500700040d101c2c140c01c0c5d05440002d260608040100c91078492413000900d154000a4403d0034503901c254011081c241c00c0c5d2514103c1d031120047d0400300c031200b408860b40e5404c00c0030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 820513597 1250 820512347 820512349
    0x3020303060f04020c0118060c0e0108010302061b070b1201050405060616060e010e071a0f040e06010216030515010501081608090123012903011203030608070909030305060a14 77
    0x20b00000044000d0405420102080f03012400e46428001400c2031280001e503450500101c1c0c05002e21110701c0e070401200104600c2e0000302000303814040640940f5001800314031403e000a003a07520304100b24240d506185c3c0310810881e5582c80324000300b1409023048004246c0386418491280a144014581c6143c00b0840040a601c80d001d0b1a09031840e550340c4c00c1c4815441000c0c01001da140e41104007610055003418107e049240110504032100070b0300307100200181200d80102ca054400a03d0148075566505004034649804220910304515801c5000402c2180000c0c02001c8942c1c040013400a0f680c03100c00441e1a00c00881c3c07080c00709100503030015000d40c0200003194200304400000301d0105a43c20080c40080406500c004108851200408c40035542c1c18683c019440030206054410740c024584180600060280210b50128031401c40e00301400795100200812501c8141c0d44010344e2280501c0080034020303000e40c0801d040500207a00d601c0c050700c8403019174076107041c10030a03494210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 820514847 1250 820513597 820513609
    0xa0c050a0f03023403140708100b090112030c0305070c150801080d0804050d0e0a09090507050102070e040c060e18010306020a021902060711120307151415060f0706021207020c030a0302030306 84
    0x80d081b94054054014046020407051207140508141c1220102d54100315109100024405038004003100351080c006a00090388444e107040895003510b44192102c0d900d00f043c0c0c00c0030b0b00d264030000590180401c2c03840c0564000c0003050407074030060140c5944001034117054500039004c6400074519046030551851a90040041002d201c1020303003210141c60f02ca540d40021035441c110240d0381a0b0100130308010303c0da4108011000307858040c00801160805941e16140e181141c01154107000c000c0b9100340c410386450a103001200440c00d1168410b503035a04204000b5488504564014003503c00c14140a101d20000240c60941c054100d038509009911007503c03d107500818164001c00c7d0801c80d08030f15500b00080c11910f070180e5180e9061010355140034085484c0f54034965040e5a400c02004489145803210550b0101d0a448841d039605045c0e442c120a07104100005282c18400300c0c451103034131640e100441c403440441e0200c401940200d0304141e507500084900800683c0104006601801d042c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 820516097 1250 820514847 820514873
    0x6100c02060c1005180c0d03090b03070e060313031b0b0f06061309020307030b09010b0307031a0d1b1a0d02090102070e0703020a0e150a0c050a0f03023403 68
    0x20360380c0104183d603e000560788141c030092880b64040201d0f9940c40d900f401580c051041c101c4d8002054422582c01411014051058104107480800004c1c19940a030502c40d29070b00d8010512031745c0b440c104c100e141e13540d0b0040300248c00082c00700e9104d9041190070070705011060340002000815a544524045d4207000c000c180a820001c10300583c1c0582c5294144200a08034400000d40c8038508407000a0031104d1240d0b0301407086524600401021414108590f00601640b5010480d0440d008049a0508000a086030007501c69003005043c003581d407070b41c01c141c903803c198154400c40d0b1700e0021500500f1040310540d041d900402c052021444203a0040c04d4409047c0181c405030741d80c9500c00347c040c0e41c044900d23a011030340000d0b4684941c0c0d401905541840c030100c801065010410441c600d0600a6003500c9003030165243e00c4100b400000c0103811586580000618602c480526000391184107010000c18010f450010504241c030303404010713104a2030030165001415180d03855503800d08d009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 820517347 1250 820516097 820516117
    0x6060d050414030f0a020d05180f040908030a09031b230a0b070528020601120f080c1c050405090f0c0712091e05130e0715030b010806100c0206 63
    0x80e840c45640b081d0000c0c00075250010032401d050b501c40764100b2000e41092000900c88040100800041076100c0c03d082c14005500b40503a0b864040315a418081801455840701c0581801c801200700482185290001c1e01d20502c07030340c0c5040403600d01100c1075502a141c0e500c01000c206e9407260300c40511540380305800c13030300c0310070000c8034164507807501d40104030002520350350001240000d1440e5440c1d0001c0d120541c5d5030070100503d5410b02c12400094903004103000b80005404802184414440e0452410703d074190400e04241e034504e10a1451030380d0b6042650b000310469030405910446078000d1041d6000c60308040c00001c030341e0359403038840d040d483c0009203003104804050203440007141820103003020709100350302c030081220705003190b2060b9000d0590007006900c044031400d00054941c3c8095402d40780ca22000400c607210a03000e41800c12a00360003141d68510141c00040c0141d0749074204200b044001c0e04d40c01c440f61100010700280341070301103a403408109070300d42c020018200140200f05000d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 820518597 1250 820517347 820517363
    0xb011b0f06111603030621121b1401020307090e13030c03050f070c3f0602040b0309060a1d1c18030f02030f0102092404090c03150b0306060d0504 64
    0x280d000f0ba0200c020389440015000680d89000078401c56592148000c0480880b038000000304056580e1440b06d14245110740c8100700904044d03100c281d001c041e88925080d80101c0c01c984010300c50384914002d410496240d400900b0b0594005400502c580301c8071f0040704d0b10300d00031842c400c003031f00d007929078400382c003821001c201c9c04100003082035600b50301400001d8801d030740c0a10401d10782a44807003c0482000f1181c4244140d00351104062200032903420405460020903140c0c6100d820204002c1c000c69029501c100030003c10481181c002180092003201c1c4003100b004001d0300d0380004144448450401103955102c1800c00000d0801c060b100c218049080ca02800d500c1d9402d0118540810b081d4400c690340031681507140c00b180f80900400c00640c0c0000021030030006a000094400c1004c00742070202c1065060190b80001091400c03075016151840e828403920648140040092807046101c241400c42c807540400d45440070300440f8060f810081c4558106020608000002e000140045604030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 820519847 1250 820518597 820518607
    0x60203070c0b1302010806041107020904050a05070f080f0316030302030402120d090501030e030a020604350c150c030109020c030c0a0b0f090d020604060207050c130b011b0f0611 78
    0x20b200c0d6540c58458a002c401c006040301c800d1001400c0000082c16544c42203042010868a280c0454151840c142d01141e041240c0c0c0c0b11800c00038101a01800301400c640200f01021031443c04580700c4800300d80c1d1080032030307007098202c2c05a181c503030040000c00407140b81c9c404070041c0801c3c400c0d0059a08a4001401c000a120800501d00d2420210400f100081204c24204002c6503800d4440c0c0d514181c07200c0040c40c42e04119541c02515a600103100074165440c59a040b8110120030b46201d8407200c4c0c15008100070400ea60560909400c00060488140700c1c103a012594001400003041c0160050102942183d00f40a01400039403c00d642020062005101d585500003042050034595030003240b0001c454200003040b50f808e414010300001c43e607401260350211203035001520319032140c0c11203001a02d50f140c901e805030030084041060740d481200c043d1031344008651980664280351b000d80350f070740b00c0520f08042428507a803800006001280d1921050300426600d030400c039408804540010700d40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 820521097 1250 820519847 820519853
    0x510110903010606090807050618041d0303040b01150f200f0303040b0103020a0b160807111207150e03061303020703021507110904080a0f140a1d0405090a060203070c 73
    0x110504d0b400100000d500c10010041d080c03062201101419050703400501e4148082c03c0000c018800c0c1680e20701541e0368640481920701c0058088980000d2141902d9990030103050440c01c00f0000c0c054121841a05075400719258011805c2504000680e1500230204400003e00110300c0c500c0d1034914013500818801c5401000148001c0d4400c600c5224001101d505500600045203c50382240c45c0c0550100114442c404403094001c1405030701020b415a182c4951901c1d40942d50440a200d8005042000040c1c400501007400d000382ca91020002120f00c03004107044602e10b01650000703405030481c2010510b100244080c045d0581d010780115082565650f0208920068200304000c0d01c101c00300300c003030802200340c1055904010865440d000340c10603894242a6110f40e0900105200840c1c03e008002e50192500f0b028000141d50701c0740d00c840701107001610040c029203041506800c810304074405803501d48a0b25004070040c0e4004c00072010300d41c0e110002903101415003814080200440400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 820522347 1250 820521097 820521101
    0x1051602061b09120328121e0e010504050f0c15130806010602061009050f0612070f0803070b0109090503190905030a1118010e060d06090b0a0203040311060103051011090301 76
    0x40b0b00101401107580b203881c030440820003100d0411007103c1064105c034420b0403070713031003861f80740d4680180c0c6000030320107803500f41d00b104032020101e4098183d04083e160803100780c0644c80340d0300c10342c0140c050315841c8004241c41034403800344140d401d038031a041c0d007820388540400c04054003a018005103d41082601d500c100343c41c0c910268403480059121104002c48078680c0405040181200350040c02036041202c045041c0b41c00c0141720300c0c0195040c6600b0074047e1006c11000c0020042e064640d1042c0c0e40354083c05440354400d41d820740c0d02410741c000000c1c0c0140f0502c5948441604003002c0c7d41842c44a0751b1141130340e03030041000b4080010022000c146c0b5a414044018828400c140c8040f40c0b03060b000134804608860401841c83d003001e5401048820a45815581d001408542c04410384032145071050003044202c1c00034000101c403c01300848110564011800385029807608641c6070b11203442903550312424040207082d500305441c0350b030710a600394101c0c00210051900403410301560b4404203003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 820523597 1250 820522347 820522369
    0x90109020a0e040f1b110601120f0c18111204020d020315070503071202030702071502010609060b0403020913211b05060106080a1a09100b1b01051602061b09 69
    0x1c0c4803580c0301e1050441e5020003941170f0000c0c00604104d14486031450000e074440c08140b0603103222400c4c1c80010010000e8040f51500010b41c01488101000c3d00d400d101000d685031170780d0740341d80c452500309070251500c002001c0d00c00c0c01650013558180d1390b81d01da03b8000903c0d01000101e8151040d52a03400043d0303100d00c800d61055513070b542c41540b6441e150200400c0340864800b1200d1161040082c00a056400300c1c00e40241c41c50310394032a45004c11850102c1c01015583c0c40f801e40700e8071700000407a1301411000107004590080380c80d05800c3d295000c890091507000c00c80240f009440024451510941d02d01d076099254941c140359014045502c0001c482d01a00c0c41c08840a8022100500c1041c1e003144031aa00001e45c650200030f200d01c2c03100310244128914080714401c0200a0018500344070300302e9014040c080020300c0e0307907d85a200b2824103420b061404450155401e000010781d4400d14601e04c0300590045134010109610b591040e280030000f0304e0f150050b040400c0283e1042a02c0c1c14600350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 820524847 1250 820523597 820523621
    0x305061909080304200402040e060910170609010b0108012d0b0a1806030e0c01031a0406180b1503040f060902061b06060d03020304060813051623090109020a0e04 71
    0x1114034906490045107006038402044c400c6d4414401070140305101f00c0703015131107001521154032030341314024100c0c0700e00c01d60b9104051090b0414104000c5090103d4100c0c0138180c80002401108201d03c01900d000c1c03030074003400d00648180800c840110300c480d200100c10480c0d070001d0079101c54480784600c1580d488201c4240c04030f0a56a001c10011a80ea0400300c000d0030140b42c100300342c4d501414030340c1d10784401d035a0301d9041603140c0114035a2103c03140d915170b1a0441c020030800a20346e841e8001c03d03203019a214a040c0a500d08a801d410a0900800440300d00b020000701c240b031540c81d85d039100640c1644410030b0301c607207540d8071140700103845607401041c500512900e00021048014489481e00c100101900e02641c0303607940700c0700040e400005a6099130b4240c20804030356036841201d1032000c01040000307030075440348407800038480b04003001c040181e07240000c41841c404060300104004504c1128010f401a40400040001408980c0949407100f00c07485d007200c0c0c5203440b00000301600d40c3e001c040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 820526097 1250 820524847 820524863
    0x1d030307060207150c092303010e0601050909010605010c06110d1109030d03020f030f0919060219030c0903020108100b1201050f0d03050a0311040302030a030e0301150305061909080304 81
    0x303500340f21380303e110700e85044c00207403040c00b0494801c0b80003803e913403c44c032501a0808600d40c5600d003255010f490100307403100c00b40017040f0307000c1840c203140e65a010a2091500a984c4600880c20780d803010300480341620010303107a0107540c4040e5038401c8010b040700f0708004281801804a050122070724040e980c50745990030085a11000403500701400c1000c05940041403510400100d409403120405490b401703010a465403400f984c1d00045c03207082c480440f08004140724604482d40821070540d0103000800707030011a605820306402d00940803540d000002c60045414001c080005601c01c4a10ba03510200c00303840c00794002d640301214007003904086078440072440d10030014007541c200742641d040c001004940f41420741200c0c1e00c028003103101e01410390040540380c1c0d03070144094481404460045a015017281c46058244c100102a0003a00c51070a1195080100c091442003440030100f081ea500300012702255251024500440300d41c6011b00d0346e0080c0c480c41d030300d40850a02030203984107074007030019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 820527347 1250 820526097 820526107
    0x504020307050103063206031e161e03060f030f1a040807080724150e06011202130b07031215150516080310080613030f1d0303070602 59
    0x40608000d9150081c030f0405107400130400901c1c88020b0f0a0b10f5401c0310070300006100b0746d0b82c4010306620360413000c602e421180000601100c800e40d020b0349a0b00710703c80c2c040500e4607162081140d01070038034014102c0028000c520b08242c1c1143c0340129141c0b894484c200051219a20341041700001030a07402500c81c640014080e03c14800241050074105806001602161506950342c2e50180070303c1f0006482c900c00883c1c8002000800303141400000188c04441c0c000c00e403003202c4880a00030300d40d4800301d182e102c0741c400600c0c1a82071075900d01488050715489140c01404c17100740d00a4000780210395860191800010f42040c060004110050280d561540c0b102e00d618410b00a44200080030301c0e000c0c4109400b00101100700c072080d0310700725a40c80c0c01c940e03400741c000b400c900202070800c000d080380f54000140217054600089032000c554141080e101240c0c4d452000c02400078403404040e010500d210644840780d0701c0340d00440d111404041d0b84c10316400a8002107031458000e50702c200c0c0c00d1136000403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 820528597 1250 820527347 820527349
    0x501030e0721030e03060a0504051b090a0f150e0106020f0a120c03030f0e06060a090506031c02030f120f0a09021f030209060c010c08060901060c020904061b03050402 73
    0x3409401910000040001c145020045402c44a407484040b09800124440404144c0706410307003d2204030050440f030076410400c0c0c00e407009200540741201e040c030548030401048111008065241c8400810003540f03a0b560452090203032001c01106c600c0a0f82c1c0c0e2072150713004602c140d5081c000d0150050f01154540c10804003070b02e450348400c0c82811a41c000c4038080001107102041c0c5a45c0344d82403030f00c501c02030700c00e280036030140040c81121784210f0b041c039292468581000510512a172422903a91849a17900c5803aa4200e40c02130714110f8154011345c50310000240c001f407a01c084141d4030f1044a20781900d0384801ca40302c1d0480d0f080300c04103159100034080900014080c560b0007845084003001311142d990b00060500300410324110044012440d01e8401c103000341d0640c2c3c40104013903d070325500c10142c225107008011010b045030200388440d011030301c4c40c1881d5115605849480c1c99a000c074107525003c009403010300520803140140c45404c1c4d0020900c039a40742d84000240f5171004141070030544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 820529847 1250 820528597 820528601
    0xe060405240d240b090709030803130f0b131a390c01140a090c06111f090b360a020d0b0a06140f01030231050103 50
    0x41c02000018001c0907690000c1c00800303140c4003040318220780309401c0c0714040ca041c0300501c00b0700381d4200600e1401c0800000f01100c68025404180007203916590640d5082019204180d031408054414002400040c08204041844142d030500a1200c04081d0180e652408a41c4200b00c0d4107134182d403050b2801c0d00402102d00300d800c40c2490304818441c02454000c000c2c041c0e030700c0b140081450310000015407841d8242c841607c41e03d903010210409036034941c074800042c06006c1440303080308401040700005090641910880d0070850340310580c600e10520742981111040e01038120840e66005a66211103482042500240d4881051101064403646400c00d005282c1c4014105003040300703180b006913070500c01c001000001d06030030350381c48440303d00c0b440c0d88600d070007840040290840e228800308404d111004104074410340301100180100ca481d6811500441130010810b90443c05809400e60fa0b90302940242c40c450b21450341042184009009244940c686e07030030007107006840304909101e01d507414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 820531097 1250 820529847 820529851
    0x70303120b0312370f09030503191b05150901022206030f0c020618070308030103060e0601301505010e011809050a080c03040e34020d030221010e060405 67
    0x1030700d0b51344402c0ba0804d00000a0807140079400d41080b1650000b10f00d0180505008006540c2100441e621100fa051040180358003911806000c24514105854084d01082140c10b81d0b03607000014140700da1802d4012408000040d100c00030b603540a20041c80ea6200c90036000c5042c18051606d08641e5140500140072107480d964008545400c00504110254001480325048103488423407203200d00c04000c4103410031003560002400083d0000000050160070341242150100c000d0a40d602c40c0d80e02c040103946548104415004c2c00d401c050518856000f48460001d250300a107444d00c0a0500541d0718012510240c224641e0111010018021080070706018010180101c008000d202401d40b243d540e1a440044002c000382000154582c0051050040c2c400820000750300209908004150507482500e89107000042d81408003200c511101d40981d03014888100c0e00075284410f0840c004402952040180060003500e00507084260b01c3c0104016000700f040d04034212030350a215003000255400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 820532347 1250 820531097 820531147
    0x2030711010e0a120c02011e02070306020c01060503070f061403060a081014010b0403080405041a03030a021c051c0504060608120d0b0f1807030f0e0d031409070303120b0312 76
    0x1045d40700b80140d0700716034480c10300440d00e4010181c1d115a410100c3c5841c01907000180b1072400490f050400c2d000541084065a00880686410584a06100810540e00c1c800e550014600c04810200102844000d680000028045580d0a91034285082c034200341d40044004103560b0780c00c0c0e038892030601440d1502509a8030a424903051450f2030300e03500f0780903e010301841039a0314000d181e10030400c12002440082c0113010750740c50307100580019480304000d69030120024014050417144510500c06c450000c2e818848010489800c0700181d03000b084001d004407039096460402041381300007042084d031b41112240d80d00350740342c0044101100b607400c5202c50900070301060880d03c889654041c813110100c078a410100303110380e070b5082044001e0a02902c074048040d1070300b031526030345600104011215819645050054407101116044422030484c0c2008098120042c1440080c0c403e10b49070700d42c00040d510214021401c0e4001900700b480e500c010486441c40000d054101d15880240700c0c05a0903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 820533597 1250 820532347 820532357
    0x2a02010b010504151b0b1807080a120804020a051201061a070c05190306050c0403141605150d060b030103021e0306040312020c0709020319051902030711010e0a12 71
    0x407400308049414114031404005100500e941d80d40000c0c0b01c0c01030140c16582190346c1c4540c40c1000c160740d040300c1c04d80e40c0032000107004560303021070743d588001500308074030382d220202e0394141c84030003412580c0010140040b80e0182e8801e400081980e04c0780440d41c00140b610000180c0c09280201410440c1040c1d01031030201c2c0800c0c801c2c00040741940700303039804660041c1c4926100204440508482c0111500014996403901080c400300399115005842540c0c410403102d495461510000c83c3c0c0e4100b40319103860840707c092820b00c203d060120094800782c440c0e10040f420b0001c0001c6041c1600c0e22038210014564020004005525020f200d905c0c04103000750000b5440fa244001080c0c6840005101034184a44820080d904036819411998107801080545010b15250146803000e5441a12841c65054441c071002c20603008620a2501414101c04000145034802035100060740005000f03005101142c036661400c00c00c217010711342000c2d00c0c00020348550007032490f280180b07001642c0d080c42004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 820534847 1250 820533597 820533599
    0x809120a0b011d06091f090c021c0528030f020304140706053f09010903111615051204050a0201030501240327080c010609020f071103012a02010b010504 67
    0x9200e082c2c2042d00300f2616085e0440c4105485180d150f07219595104031f00961405c4010342034076038041103100103542011200303283c040724103404075114090b05191840006c000c6c10380b040ca060f008100591184010b040102e1928030100c030b00b8003260412102522039203150b003451280d4a03000d000b400003810341420311a0400380d5645c902d81e6000c4101d1200704800ca14405203d86280344000b0002c4071000f80003414070030707207021800e840c040c200c103140c00c4003c60240109800550320100b51420400e00c40c91458803254941940002600d0b03070210001e0910100f040054042c80c001a0320500c1603000d030300180040b1402d440010f00b11001680b244100d0030040300590f100d142d42005000072080c5920b00499001c142e1205810904200c1441c48801103202c00b4140030425444050301604400c60b008108841e680c024080c242c0c400c500403013007451810014900003652960501c240c8017000b40c000500e0603001e44080f0461700010910f00c80040039250300c1102d0f10303824003540031000c0003881c10f14202 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 820536097 1250 820534847 820534849
    0x20d030b03013201092a09030c090b09070e030a0602130807062a02010804120207090203010602160e010803040e0c070c06120b0f011b0302010b09071e090b070809120a0b011d06 77
    0x45581c01c00d00b481b040c8488055904024480c00004d0b01460b00310302c0643e4402c0c1d0f1200410002c2541c030080d6401924810300099150340a9540700d42c1d07801000e405010001960341d1344800075440511403555080ca00c060224000b1410800c035030180010751129158141701c1c108845507151401005e000380201c07800c0f20801030760310031005071f0001e61005200b0550400200281c1c186001904501c9440d0300c040000940c681e80007640e40d4900b03c0000b04a4a000c0c0c0b1180301c030001d04002d004080e102c1d4001c01c01044ae0858201d901984a00b1314035406003808a185e44590009403075a001d00b0000b1984021402a095607100d50108032004550041c034141d00c0e200060310f08400e445e1544400104004200c0515000303400544180e0300041100d1118904810701078208040240d03102c5400001c0301411000601034843d20054903510312926040c08219a14811154803038044a07812858052490303250030420000c403230038070b842107000c0f0f95a5030505900b01e2007001807400d01c2c907614001100380603003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 820537347 1250 820536097 820536131
    0xc02060a05190504051c090609061d0607050a0501020c0714030604020a06031d0a0c09060605040819241d2116021503010807060906020d030b0301320109 67
    0x9024811503010589603105e06145040a541190016111031007403200c01106500903101070680c0c9054480ea008103813900422919902640c000c4901c3e94841070010b044c0d468200d0141c44694451800c564a112140d56018261380151020080580c4180014001441c01c01a18003090701e0039001005c03030303252940000c1ea000040c0e101d01010b15a803500495600342203c002e60204250240c111030340820140382480743c9000d940306d4900281d00e4444045105441607044604903018038005020800d0681000030100340401c8045a045811014070301110038010303848100714214020004100402e8a01009060605500da04031034114588c00030031820114060301c0322090205840d030f190410f031441c10090502c4103001035402503515080344909003d100003036068031551020788581e6940c890090b503802d0018040c80b0050b0300301a0340503480d03901c2640528100a00100089145a0308801242d584003410001101156244449503181801e2000590041130324400c2000381880030710391050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 820538597 1250 820537347 820537381
    0xf0109020903101d120d05060f0108070e0a0f0920030c0418020903010216030f1713061b020304060809031e0a020312161d09150103020c100c02060a05 66
    0x41c12030b6941d0074016070041c00785544004038130200121401d51204101403c15a08400051181d19040c2000501d040c201222038210340441a11030382016119013000f51358000103901d080d17822001c8000005104420382c51644020031a420000072091140052044849045022805d502c0010018080303030040840484007250b2844010000c050030000c80a4003038859050602c0d0316600111b0702c0c2c4069281c092007409124402c0e19101001c040f0741d88150391070903030075850071042c49041c4001a1050483d40c0400801751041c3c500080d41d0070707240c2c15074403820604072100005902c08101407040c140c00078036254015130307010021814250450040000d00c84030355030410000d6000b28000e800c40b03008100355202641c40c40c0b00204c40780b0348105141ba00c0d05184441200040701a03851340848480d8580d00d540d0104040d001e80c1c6030b507440000d11150204801c80e0b040c109682009096000da00070300001d903002a1940000c5016041e07804001d240c840701614840c00340f0710b0038090000720299504542c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 820539847 1250 820538597 820538623
    0xc2303091002070f0311010809060603030304030309060906090b09010c09080c27011e0905070f08070212220e010b0d05041a0906010f09090203070e10030c060203030f0109020903 78
    0x400001d4800c1c008a081c9401c40d440100c01080b401008410403d540710340608400c42030703840c0c03039043e45d0b40c1b8520b5554041c103440c0503416400400124011a12075000300e0080c07402000082034409059403102d00700e5030001001e640f500480428014440301c2801000c1c04100c1c2071405100003410324110030303183c40e8500d114030b00c0764003282c18010315000c0c1010100e9111150103011a51580e43e00c4050f05a0050800080c49407000c0c1000030034184a284103d0b8000c189a680d5410204505a01590b54035409031101c03042d88030b80c170201f010b100280c0000f403200180c0d00500f410700c1e0020086800000c40160004030740420b40100601010130070720150741100800c240f022032180c45a08012985030b48244121031800c1d541810401d010f00000b6070103040710313070000047c0c80b020340d2070240d90116001c60700029499003010400f040340e08122044035411440c600c1d421200550f6940d00c80580030056803020000d07800c080204558010f02d50b00701401044006010340c98190030744c2c002619403441400c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 820541097 1250 820539847 820539859
    0x90f0c011d030f07090204051003020a200c041107061404020112270503070c0503030f04261f050f040b072d050c190f0f061b0c230309 59
    0x411050b0382c04011002101445006035540613840c2d8030803101175400350182c5401100a01d00804001d4441d00c03c0319240702c141c1d619805480810040002d880b050940c110680d48104424140a65594404c0310300c0024a81103855941060b850184265241003802e800e15402a070100700160340c00101c2c03000307400103441e030002c0e0b100c038000d202c09180800c9034511503144d0305601030b074010400f0000c0205903041c01480c0954071555070b0410186d49104034418102ca04000303100800254aa12140c04810085071480e0701c000401030401c01d150001200e41c00912410b010b2450b4480c00042c40303200c0e00030301c140c2d43e0b41105140035103c26040e800301078400000c1041140c035490500c800c4403450000c45c1b240c0c8100d40d00c001000035004003250003405d0b00c0440d40c0035500702140700d4403404000c0c852080c0e0000d81e0782c20201c15515800c1541d0310300a4203444950700c0c1d100da603d049114990070300211140d600c940c00f200080e0b09000000e01c04004e820805c0018044c04061580400402d40710f96400407144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 820542347 1250 820541097 820541147
    0x4030519121406010809010c120b03120d1b02010b01020604200307170d0309050c0d02010c0b0c0406080702150f06010c06050103060b03010e0d051602010905060c06090f0c01 76
    0x42111425041d4154005071807801039400c08624500b0307441802400300341e80d02c0e0f2494541400080c03c0703801e0203610381c011584105000100d0441038002c03004a41c80203055071080340d03040c8194035540e071001c000c038144203544506425503103007a0041e00140c0402440200144074010380040d40da82c102038006040ca455008810b045100501340300351410714003400f40d507105a55a2a4022825041c00e140c0d100c5000700320325844000c1c4244140c0000035080350080100c8c0d240c04050044c1a240700300186d0410140c000204080b42c4400d002c98001c1e400c0c81c2c5103541d118600107004100d084090403040c115003252001138581c074031600d000350308070041054100c1240c58040041e83c80d0007a4520081c049070400000209020b103d0380f0260399840280e00a01c9205801d5012540b200c8081c421040031070018020007040310480d5000000180c07060408002c0c01e5200d50001344940c0003017000d0103580d48120100580310109125144441010100910606603044000381c00ba00304d80c8207190000c042121 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 820543597 1250 820542347 820542397
    0x2090409080a031a121e0f030f040f0e2502012405031203010506070308190614030d0806030a0807110a030326011406070f0219060e030105040305 64
    0x20100000035840600745a03203035000c81028002d07041104541c607034440c400c9001c0d02d450030180c1c400143d9481401c0078060209800c0301081d22200b0003c14454188100c210910750490200000d0a0b011200c05c0c1a03500c0303910b45002d21a80500a4009100158549050140c4505268a103603113903410820310840c04a96440101d0040c41881c00d06100d0b003406400e07052428100303060140547c0d400b078043d40d000c0080d1031a0715420b8402032140d82d801150030007100010030311179240359801a058408034040b070b80ca100a450169502e94000d8103200660707844420243c5803c001881c0d2468950900044500d00310780000d03203030001c00e070019140741da000500030200404500101c0071140c001b040c0754000c039100d04004010700801d0002e210750780100b11100002e45500b80c03219049902820050640700d55882c1400181c0c0c008010847d001d5070035480706d00050b52014840415001c0200d82d09419a10b0700740001c000d1082c0c005494002c1e40340c072041c400420781c00320482d0300c1d48080d800c03012204d0200300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 820544847 1250 820543597 820543601
    0x1020901050d09060e030a09030c05060309030901050705011515020105070903080a12060f0e060307120506070f0e0405090102030604060b13060c0f08070c0e06030105160e0604090608060405120f0904020904 90
    0x4110801b40070000e8200340e41038208904034103803400f9080320706034940c8490501c900da100640702d00642ea0300a01807000f85612560090100c9440b0740e00100790034840501241c00720440380c000302c1e002d43e4403030b0b10803400720740c244500342c0d0042083c50503070030652441c4c9a402c22446400d084034100503842c0b6035650b151142c2d1700a0340040ca140d40c1c6c080d80c15036071440504500001614018403c0c0103080740040c0310000001c40207590381e00305000d01420349030040151801c1c1303043c50109090125684245190780d68500c203003841042c0c10703400544d89241076020842180d000d074005d40c0400b102070001c42204001d0185403010360700981020700008180d803c109011b44078200c002026004006020010403202c07045c1e440032506044806885a29182c080500307954040302c030290003040484004800c6d070f00c1b030010401c40c000080c042c03502d81030b11086240705682440d085102c80e41d1084c41407000708001042100c030b40c100344503001814140e0302c00c2650540e100784038115201e260081603040096480d0f03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 820546097 1250 820544847 820544861
    0x602030901030f0507271a0d0c1701180902030f07050108070f051b0309030f030d0b06071101030c0e131b02012d06090203130c0801050613051008160e0901020901050d0906 75
    0x10301c50745088144c11f00410485c4d0300881c01c4038100c071300b4614900707501c50050b40341204170720200403054400d81c03c12246049290301800320482c1a82c848480e09d002d0f86051004000c1e01c0b80c00b80c0070701441030800703002400b0700101405c80e0742000028130044540c190721600303449030b51411020360308603228895101c0e8514040e07010030642c1400307901c103900d40b45400040101a0044c41c90020300010700705030701700b103900c1c0254100900090b44108010f101507100764401c280c00c101c40c0c10328001300107041001c02c03001c44c1c0c0345401c1c14560707543e0407126000103450007411105001620003884201c5102c02c44003c40d9010a10280d140780308289a400f0072030003a0441405400c010108540320b180100d0318118040c0c0d804825252641000008201441c0602403035100b86c0000d00095040d28a85018100501d401021402403492201c00842d0122040c07150000030b84921500c44040341c2400c895043e4241c010b07001c1c044988c4100301c4c2d0641a6002001e8400410300a80d0004941c106418000054148 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 820547347 1250 820546097 820546109
    0x321b0702121c05070515010501120902041e09030e15070212030c01050709051c0c0b0f0c0d0908120304020a0501111c2001020c0712050a05070602030901030f050727 72
    0x600034040111030f40c0324000d44a40341c0101d040b41d20780110b0450303a200307040080c01782a0010f000c0340c811032400003140d00481c1941e072000c1c0002038a401300b5603d5284000c5500c08a904045d10b8203420002c4c103a210400c03003a842c0c005c580009201c010600c80444a00c150704000740280003031041342007514802c1c002d5410018107000244058a014540105540aa8040c00344078541d60b104020300c0d20340c400000060281c0c0f140e0110422414660039202507008a03500d4920080d0801040318000002e01c2205641241600d83c1040f140c02c1c00500340c02c000403901a5000e03a0000d00c10000582d407110074410440d035080c01c09045889480c80755506000d50b170350703c40342e5005c014071954203003523170241c200160000381040c0303842c1d20301e200e0086909030310545e146100030341c1c018002403082c03141400800585d07030321842c2100d0140240d03a940c542000b800d80e00c0100903800200300a459945c05000d0111294485001004140703040c99001d0701d0b44094504001c40160300141c0b207841c0b80704240b0300c9005045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 820548597 1250 820547347 820547383
    0x30301180e1510050111190b0916120c1a0909060414180601050406081c0216030b0103060b090910050603160f180506010f0c0204321b070212 62
    0x20b0480c850070300c01812485114001040c40b08812054000841c401f14003412518440c011810303540c41c0e000c00c80c0c0c03000c0c08150710f0b8003c0d024040c1e80201480c1d4000000c040a2a5800c10f415050a001180c04d803e5448803400304603180b0020240340c1002d04460000100711482b00d03003501c070b5001003130003030051134100c820610124061160035401091452601c421807401c864840e81c940081c030080d180c4c01e225052031503000109a00d4000c1015103c64103603242c43c41200d41c030013104000240c4c1242d0541c1b00346c81c00c400183c014410300c0710f1400b40350010041611525410b080a0000700e640d642450656544503980f00c02082c03d598060140310320f40d02d00e45c1000c6404d99180e400510082140e0302c102456010034040c1404444568084e080c0314010584480066100da0700d41902c40904d414000c03680b10b81d07607004483c3c1012007400f100201500c091070a4561403800040c14ac084400a01600c070660340e00b250b83c18285005030212015a82d05a80009032042c6862550380391581c10388050706444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 820549847 1250 820548597 820548601
    0x6061107120f0b090312070e0d061a030703150608031306031e0e0c04050901180209040f201201051b0706110a170a0603050a030f1b12090503030301180e15 68
    0x60000010b000c006c01c40700b10420264840d05402d031740d0404102a074a400c00e01a80c00440403039010760000342d585244821075150305415500082c203005403500111707110100808030719940c03a20380c801c6802a0900340001d501d084c1c15400b40e81d0030359090b44544801c154444402c209061003c0e41134400c0140041c00600440282a66070303900e5800311180035000d940390400142d4550014000c41c0184010701040c003007081e4098003440781c040300040c419244403402a207004c0010307450700c0704040780c41d8889100c1e0900d200d09104000c0350010180c0b0b50070749030b03051901388084600c0101c00c090102008403c038541d51400d51419001518111040306104500441c0c081c0c3e006811139001c10071942e4003c000c2207580e07600b240c0d41d070890300507001c05000c0ea44588241000203018841d5101c42c940c20303080c00c145503080d2407540c0e8200061150704440080400b01031a500359045007401001e40003c60203182150304264800160040401c6541c1d0003689600d1081748401e01484a402c440d0f4507400b400e107082c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 820551097 1250 820549847 820549861
    0x3071101090b0a0b0604140625050606090a0203090c06160f060609050903180105030a0216031e020d120b19060908070f0806150f0303040906080106061107120f0b 71
    0x402c203c80c000e0310b6500340250701d1080d1a18070202c4007910b4202c2140b600d500071a000384419a0403103103050307c1e400607885240d6441c0600d1850403d001d4450001040030f46441c40900c0720170b80c3c0c0074221400003801402130040306240450b8800230004180e0380d1580724016291142000f00b2806400740448030701e040c21000307125254010405135150240140296200e02200641d82c5c482d0903410340c07403d03580f06542d98056204000071a080350705428090706011101001030481c510400086000c0791030300380c903224907000d0500800c000e00e82500140c00210b01c500c001411601409000640301540e030711003000c980e0340700364501c403003141141458101d4030789459005d03000c00010f004140c01e030f108049001540840082005043c0c4400d00060300c0c0b00e4940d104504c004a1a002c484c513407140d00121002d183d9141000075000522500d5070108809140c498100d00710303610303600544204141400f110480d5440041d1403011566031496040185620381444034110450700300c000d110a020005010350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 820552347 1250 820551097 820551113
    0x5130332030a0b15030a0507030b041805010e01020301080d0e04113006010e01050c07090f0c08130816030e0607080403030f0e150a050903013e07080307110109 70
    0x700b064411003c000780400107081280300428102c01544d03400701000003e1260340d03207410080d040380f1141404100c5990f210300040580b0035503219007000c8207004641109001c824050440180340803802140b841d4144a1850384400044841e00144982a1b803031100944850344120700c944a00c0001680702d42019404045203854043c540411820303900e01606840b407043c10300d6008510503140c2003503020558005441036000b101143c142e5003e0804000782c001840d008249041d03950b10400980820400e10191950f4070185c85079000381290b81c08000000d240b2012900c640003c420301031142034461600716021103c00c80340e42d8103c8130104040082202076000342003a030344651520350080d01ca19a04484400c07100101a62107904d240091780c8101076032006003404401813604910303107103070744c03020909603031101c6996480c2921903411401c440c0e1a081507051980c0c500240b0400020300b0010b105070300d000d20500035010500c000082962180503281540740e80444d00000c0c01641c07503505107504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 820553597 1250 820552347 820552351
    0x8120406060e0a110909040f02030106030501151217090a0312180b0a12020c070905100f0501050f090906220c140906070807030203070b0f010807090513033203 70
    0x1020100541c08907145003d6801000d451280c11800d450a00402c4000c0004100c0090703c00d85441101e1821040540c50a000c2d4001841c003c000100b0900181485c100492030a68083ca00345000c003481200040d0041c61012695402c919249480ea01d81d10b0004503204001d0340002d04186100c10008201504841e0100c62000941c222200c8150782e1005618248640c0c8007103800500c507045120100c500035400380c201c2c0c0c1107840854100301c2c0ca80000d0000c460341901c41c0c46608030072a83c20009001d40300148409000300f807902d01d05202000107000b500d8000c1540581c41407424000041568403031a00400118050041040381d06080b0035812000f040c80000303a400281031880c0080301c4254a00407922211009080c007460682035031035900041c1c000c00c82c01c90840c0010451000410041d012450044440c0198903190794504150185000c1c941d91016000f14200000c1001030b03058030301c10301c0200344c0506082051540300c1165001008802070b03075a5080e0014280784c0b01009020010314 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 820554847 1250 820553597 820553609
    0x120b0406110a09061b020d14030c01020a0207050a0603060806010608090a021314060a08030a0c080415170109090201050d1508060a02210603030304081606110d0f0608070b070812040606 81
    0x14900b40c06004075a142e414105d10060b40000111145200240141400341c1d00700e1500c005503800c05c0014100c003426640000c9484c00141e118103014070551409441c4040205450304003005400d00d000200f5864850510529060081d031400180f02c00c1e005200300a038059000b000000042c2950078214024121b0b020b2519900c80d50b2000242d090030103003906419a012080158180703000940b0444d10340184241c00c454440d018440090001240a11080096020788820552500d5005802c40200b0142c4c00700d0240d0742400440340240c1d030800116040d4141d40c040119511001400401d8074056070f41c80100713503221300000c0111212196001c3c2906070a0490000e680c0e03030700414900504a0281d44641d4190010000710300003e14400c0200700c0080100600308101220381c0b1a94210380d40e00000844006d400164003464172214441c2911442100c04200103130341c10100c445944d0034650140100d22000000c0b501d00348003905d0107a42015044040844945c0790600d4208080c006c04c0c4264 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 820556097 1250 820554847 820554857
    0x3f0623061e13090204090305120901060f0306020a11100e010e010605090718082a0102030c0706030e030405040504080a030e03160f020a090212010e10120b0406110a0906 74
    0x21854624000c030310312207485031507031124940074184000c1002da08400d456002e48a41c0d1441c42e02c0c010f8440e400382d101158000d40720144c4a682228620141c07490060038103c00340d00d03104083c03101307a0b801ca00ca00103403a0420320040c0c96070802c0c0d0054461150518600c101c6102e02c80e90140740001d071750820314416519600a100d140350b050b00040c240d4480c1d000f42e59000c002000003c0301c0b40c0c4900360034481505140959219903981e0034a0301d040080b00303041d2442a21a54088602101c0d1070303030b90098602000e200443c6000108400e094485c810750080c44101512040c46050540041003903501809000b84204882d00307151a10150503482009250042410400105240a004001d0b078400710b1607111540d04000056558500c1c00c0d00d00c000881c0c0c0071005606c00314a52086201404084440454154040d4100702c00f1981e0480300500c4084503200d005824012140003070600c3c1d0540d9841003156400da296403810340d000c0c1a40301e80e0500c4459020402040b8698071000103022a1190380741c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 820557347 1250 820556097 820556101
    0x23060a0b090d0605100b0c0606010f0c02090609180d02010e0105070806130525020303060406080708070905101710110315120c030102030108070e013f0623 68
    0x4054003a0007000c0d12507501900110711140420b0094008030340c0291844650900aa00c40041c900d05030004842062594050700405c4025600a0091500345000e8103281100c0207450340010410381c2d00421050042c810b00c0d021a0b80d09000301c8901c6c26040d096000d84101c4140148024003c2070316002504466090401142c0c815010340d51103800380c10040d00010700007480d0041c45014040190802c89402d44034411039200901000c0c81d001d1141855024640d070341070075000c10041e52140e40024900d43c01404042180100000c3c0306011219000b07c041440c1d5540d0f0001d50b8031001c05d034803107800300366400100000d2080c0410700411140e441d000410138448000a4074000c3e0104803000c1003004405c1150702100c1c41c00c98040b80180076000c0032a141c204515000c80c2c03da81080c0c2c040500d940c4891401c1c04103102d80010700d4050720041d415030902c44d41181a102c070a10310b800204080c6000800b00b008a4400890081c108a81114091140204121401590366001400001180c001c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 820558597 1250 820557347 820557359
    0x1a0301140105010903080a0c0501060609030203010b09070807032a0302040f09020307140f0d141501020105040519171305010306080c0109090b1c0b0601180317090423060a 75
    0x16400c1c1603541c1a510b0001d09401d40d92100324030703802070016070140080c051042002031024040d20780502620341d500c948180c69803042c182999080401c2c03600c0b40c0a044208240315601c09009540451140760100306440703001c686180c01914410101308012040c1c2e820440c032605034001704102c502015421003c00e50301c2e64030000300e001c1924040c000921001d01215450a11000350105610540c2e580d8580003451201a0481e0400c0f5082503503214880b04000d1080c2002c520000c03030101c01c3c0020700c80d6240a659007074607559100c040341845d9007820302d2a004e0014801c3e1100030a80000d0005030347c2d0807082e0400c14004002d205180c00607042c040003150600c0040768180c101c401c182c582641d01c0c0d0a04401c9400b42c89030022040e000104100811483c0207008c4250f82820f01516079075509090050004000906d84c1d41c010102c840311900400024040c1401500b1a10003951100d40759480c010000b0702520f2125804e14566a140706a25003400d04603010b24041c034400c07503100b103041d503981da = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 820559847 1250 820558597 820558631
    0x170c040e0f100f1410030b03010c020d020c0103090f0b0a0603050a0303060f060e06070b0601031506050715020c060403051e0c06091005070f1202072108010503030f04090f0b03011a0301 81
    0xc020130243c0c90b00140054614100080450010701007400d010034100503041c04a4212104a503503d00140c4c0100407800801d9014803c41142440038a403c1c014452541c5503007100181001000300120340d201e00181100c2c0340c075030141d0055644401900c1d94002e86050040142c00c8902a00b980c1d5000643e0000d8820301520310020083e4000d407145081001c9603c4500291200a04950500d40c555220121146604000102805842e201c06484038402d0910701c0010010100c02d07844c0d80e104000603200d6040004d14242d0240c0d262800d956101030082610710040c80000b00c480454102061056045030040b801900c00c0c100c483c100d0303030402c845030020b4064800a4401c0004035000c10801d941e0240b28079082407448071290030151a040a5a8503400101160f20800400b0840b50558070350b00d80d8010701d06401010114011070030404042105c90f4544164130506100e690745804c1c160700e81c4500d4009040d500c400400810181000000c0701c20000c011500c2180b180d4038100c50000060b0401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 820561097 1250 820559847 820559849
    0x1090803100305060f1302091b0406020f0105010905130f11040f0c08070c0809010c0c080706021c0908190303090b10090c02210f0f131404020703170c040e0f100f 71
    0x45900c041e04d85130b543c081c44114900a064064203650454281d002060014010000bc001036401031426428110026007110010b0b00000141401c01c010302000b82c140d08011641d4541241c802c00009842d0b262030044d0f04120040705801c43d00341095024407603020791000c0c071508450b84443c503841e0340740300c0111260405400010240c1005001091295206126103a607680c0701c0d0490304040c40d21603000514000c01b9034022801a448020a00384c0c7c01300f902c01000c2509203d00b0581c100605040c8120b4803218002c0e069007080141100000038107200790024107005400c90384039041c0c1e0030100340710141d0314654010941014188140c00c41200d100044140c1c0701c0088294011030058081c02c00100e5500914800710749480500000ca2440007010051408609070404550380c58501100078500554060000b8410703032050140c030b000300c0d82045981500c0b1801c0a9019610b90301d0315000c40042c041c0d41c20201103010034004201e40d1600408080e801364801e20710802406541c0c10801c0c07506001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 820562347 1250 820561097 820561111
    0xa0204090c0e0a14130203040609050114011a0921060403090506070218040201050906130501140f1801120e07090b0409051002070f0204050f0703060f15050c01090803100305060f 78
    0x12003d041010058604c0344400b00c0030010107003000508004d0791802660002e40302039400542d1038840b801000000d20840100080c98800010356600d80f00380300744180700b080314941c0380307060001e20321800d0390300d036100c0c0c03021802c6c503030081d80705c102035041080e0ba0352030202e030201d0205c0d66034440854586420010385104c164028086d9000c50041050711850150261040b814480280309001d020790300c0034060030740030110701004040186800700041800d841c1c1d0740c070135200d003204111520142c2d2040d402c8801c0c6150300e0402d15009070341040121103007041a1414440c443c40c1003000d50000201203440e00807100000d40600001e007840041008039040044000c0403948118030400c40800260064580c560043c0007903035400103160040f8040e82e000702c40c041c07803040c00201000100d5030107101d0384018010f0080a030240c0c07410884504100b441000103039040c040b0100c7c003103028002c2508006911503002c1049500e80c00d000d269052980b029000071a083d000d048009400208035060051103449 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 820563597 1250 820562347 820562359
    0x80a05130201050924120f06090105010f022b020f0d020303190e100209090a1a0d0501090602040f030309080f0304092a080907061e050c070801050a0204090c0e 70
    0x1115070040d02d02ea032003001d2058100b1200d002861081800b0104824056904001d0a6840b120104030900300f42c40142035103d08035a0b80d0500440d41c0300c1800040c1981e80030f0904810401020000780c0c03600103122141c0072030340bd001b0f03000e80200d189503004021542c900d8088620350b4844044080d215000ca55601d001a403050001884401c2825100080001e030300b240080c0302300e4a403e406050200b5224407086d000d800242d011800d0070240744d910307400320310014100800103c8103860035250207103400c2c96220701c640c155602d0602100b988a0381200c2d602c0082156101d076a03044030291054a072109038049941c80740000341480d00402d000c0000000e44010318981401d1030b808000030401c840503400050791021320070140d4000108100455801074440f9110381c40d020102a1420f034568000030100142c3c280c20703100408035000c1c0c0120360042801c065840d94411612140f4007507195101c00c03a550b0804051281e081c6035580203000765038040505101c50501c45005542d40001c07004100c2e0088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 820564847 1250 820563597 820563631
    0x908090d031206211e170909070c11040c140301030b1f0315051503030a080a27120309021011060c03091c0e19050a0602060424060e090a03080a05 64
    0x150914040038004007070340103020110103d0340380d000513a400c8840d0082d9054001a18488501d42380a82d1540404a4070301b03410b140c00035999003480c042086403007170300864a0700c030780f0300699005d4044034081d0071200500603103139a940e043c442d9a42105072425221816015100411012007182801c150b1307800402c2c0d80c04920601002c000206401444241400c801031a030141c141d50030310040c06244450703904d00e0200e040a2800c20100e0f241041480310510000070800d031034054203800030503601e0f002a001c0c00615510300007900038000040b80254807205070100ba0030100d4000502d0001c0501c000201c82d141e0f503410311205054402039420420ba94050712140071800e0f6451500c01500042d482d0030f03907a00d0241c81c081b600c030110800629801104485090080d41054800c4070020181c51008020909180d1154101c00d005d8800d100c1605030104055130609409030466070080c401d0034414411031800200c015112102e01c03104400080f069000304041e106075000e014014248690b13002d41e98 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 820566097 1250 820564847 820564853
    0xb010b0c1c021c0302271e12010603030c17070f1e0804080f010e0c06040e0408070c0308070201080619051e0d1103101104090908090d03120621 63
    0x950210311004502c41e0034041040e40c204100d0040110107070f62805a1100798140c1d080c030040181c01c00340500c56a40034448161541da20f81c1f410302034444507100714858500c001c00328051012036840e04290758205640042015031100702c540149001d0040240f0b0f030b40c0d8000300d41c14144950301c1e018014030280e42d00200820b14508e0103440031084070801200042e4a640c504099820590000d81c0e9900030309015501900d0030700403004403258880140039040503900020b5901e010307500505909003d40030014080124480484014a4000c03d1108109550385810282940010012400a40c1000103c3e81c281071105016008610140c094003a690416083c40326180224600c0302c4240c806491100c2c5640f20b88582c003028034041c1c034810440b07090700300506107012201c02011094030714103130005c80e010151000781d41c10b95088480c0400d5000c5039007010200382c01145c0ba0190b00ca03500f495090205600f242c0183c40c600070020f000e00c000c41d82d8903000408014402e0b85c0301000d8503092565800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 820567347 1250 820566097 820566133
    0xb030a0b0a0e010501020d0311030f0603120c0c0f040203100302191a0c01050c0301082a03010f0f0b041a130603120c030311091008100506070605040b010b0c 69
    0x11220646000050041a4000184401485a201c030560704040c600500a80d42c0c1404510500385042c2000e10802520100f01603c074400101420381c0e901e020800328083c0e94092114003214502d01080689500140070b0b02502c07450b100b5601445420310200d550101e0a050090300e01c101d100c3d10403031014078a141c0a02c80c0d034500309030810094543c00e040c081032240040b9100c04030b00e2421240603880792019000c00b030840e0400b074075904400009100400803e04c00140300e02c11a07004103d21101b800c031035021504000105a02660f05508110078500c4d880410350007a801000c03410410310001170360300240411121800c070070344051074100101c0380050800008844142404800015001d642d1ba02d8002071440641c88890011720743d0f002003c203056042c0034100001c80a05d500c42e10382607410000030340c40c0b0014403078074050007c0c0c44005040c0901483c00500104000351801e6034600c0d040c0f410380001c0c04220380850f164031400002281c04202d00040e140320345070110040c1101000036141505c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 820568597 1250 820567347 820567351
    0x6040b0a021309050603100e07030809041d01020a020d0923031009140105063709051807090203060d080d1e1406030f03040b13080a05030c120c06010b03 67
    0x603808200074090014282c0c4070800a2403011800140ba0400c0e81c2098148001d0f030342d000d42d901d401c0034101e92205070041031140072642d01c16179541d80e680806020070050400080c0548113102070304c43d05c50040006400502c0c4c4051035a00352018440005c3d4161240007603801003081951280d00102e540c0e0b0551549222104001401c9a806604402d00401610b6209030110f5201c0c9801d030115548075000d00800d90452000c031101e001c6112030600a00c1c144402c407401202245044070701001c02241d008a510141000d40001c1c4000d26140c100342101480740c01110b440c601c560b0500054417415482070780c0c024407008042e101030b54803a4494030300c603412070b0b82c082204680e00c0c10303028641c1c01a0124243c4401c140040850007400c1550550b07046c0100412450094104841090181d48044100c1d01541c4000180079207814680000c040303288031710f0700b180d80e103071064045450512400201602e20510700350200c4404101c174030200c9a4a005003103459010b0307030011006015441c0c025015507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 820569847 1250 820568597 820568611
    0x60108070206071b02030601030c030b160e010c080d11031611030a0c0218130c0b07021005031b040b0304260a0c2d03020706050a08180c031024030506040b 68
    0x40c130000b4241c0020781490780c01c1c0e01c12118a90840800c00403c406640caaa038080c0c0040d0300351070210506480500311400c001d05c510304100c8010030441c02c005003a8150b482c080c1e0110410401e80300a50450384280d401038074100e621186105510400510402106038000c4016001e58100310302590195104103080d06c1c1203034480d0400a94000941c8003c0c0450b12503480c512001815400a0514107581482a006a103041408228400142c3c40d21600412044070720301e0036541d2540c50350074941c2c003860072443d142c168001c0004c0001303003100c01801541c05940101c412000708100000c0c00409105007503e2524035141c240041d11f5828019604003041c00d0060104282d548428507a1084206640d00c5141603401d1408000003070503810402540540100d04086182560199010700302e58401065203704000d080207044a5810034000c43d0005007001d0f0448101d02c0c91001c64002400c503072000500d030f201560484103054485410400200c90700300001c4c2c032040d200c503180d00d55000b070020104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 820571097 1250 820569847 820569887
    0x1406040e032106041d010501050a0e06100c050f0d0c0b06311104081b06090d110a0b03070f0e0609011707200109050c0a05030d050d1b030c0806010807020607 69
    0x2c400c00708041034819501700300c090000142c643c10700007003020b141104c1e080740e85d0000400c0c0c204019070f1220f2400458428180c18a4101d01000345409442c0100c101800d0500380510f6140050075034000302c180e06154400d20009210741c1c1c1c0c130b400b8403101c08042c007a820003101c10102c080c0d045000e160341c200030404044d0008100400381041d0b0f507815600550260b4090380c0200840003449500c0e484000003160b0403203501c3c1c6064410000071344c6400c131307400c40500038044400704581503a0310000c0541c0201640000070780c0720700d03044a0180900c00450680b402158121621661502e016000c417500d4100584510306090140c4010364002003008010030b0520861a09090b04d882140f105409122403800010903da0b041e40740c8641030031000070300c42d8015180050300303000584c1c011400d100103820758908151104100500780000d400b030001c1d110084000311201150940d03154015078884641070700c0d0801c2179100e800046852100441d0040c1c016000040494a624414100c01680220b00848 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 820572347 1250 820571097 820571111
    0x10314040c05100915050703030e010506010206150a030b01090204033f0c1b1d0105030304060e191d060d050c04230a050f0907030b0402010516061406040e03210604 72
    0x5c0745017000c0c0ba422034000708201045800c02c140d8140200c03c03000b5915030091116080c502c0011f951f800025040c031140d144c11440b0390b403403a201d20010800a681006400340300307503516061040254000d010a0390200f288040301c40340304101c5050185041c02030903042059850680c000040c550501122604100c030203030003600802d60040751421501c2030742030147d8040d881c110000c805640081c0c1e441c481001c04000401c40c1e680e000c0300b51401c898581c01d282845001034800100c0318160300c85024505d0409600200b142d45c0c00f2a5a5800b008201c03030024003946400d002c0002c1080404001070840d03000042102d06030519420044005005072082c195040d00c4480005080408840e04001e42c0e64480801c03080f4402e0107030700d642101090003d03080290070760312064030491000303002030b042c0072001454089103000310b410f08104940203601041584070b1018ad0b00181c8000303688445c032032070500c01c0e02204c0c0030b40030040b07d01d00c0b0202c852455180c0195501030510501c0117000e181e1165950103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 820573597 1250 820572347 820572359
    0x110f03060a061b20030a0615050f01121104050d1103010609020f030613020f0a030e0c0121050c0d0609020703030501171b0f0604030506040c0b07080405010518120c010314040c051009 80
    0x70040034180d202c1c10020405024810340c0e0340715807a0a5002c9c905c1140205203200099801100c155810030004501042e103170556203c1842d24440c030b51010b81c1000c000c042c20401e000144c08070fa424100d08400034440c0540c0c60020400341d00034a0005124008208081460b901d0280700651603035000020250829000c440c040318a6045482d10030003003911007403510304003074041c05007111a103000d081038025003030303117180c0b00c14101403020040342c17074541d1000491400d07000705094a40e40100000f05000e910744441c0303003002940084e01c04502080c2084c002040f103c0f00d0004c00c24a080c400002480e4508460004c0035402c080300c851590407101c1507501c0c10319911090001d101a6010b5002842c40382800e00c1c00c418811950b40c040394508105106407400100c4101c100c07400c484091801a465440e00103540707000400d8000026800416800c4a440b020344c08690348040e031000762800c0090710044101020030000884005122080c15101400749240109a444400c21396140a019503a1921 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 820574847 1250 820573597 820573603
    0x90a0b030712051006080412090f06091820070f02040504121403060d060504290703110c0309012003030f040b16020718110f03060a061b2003 62
    0x2464031000035060400b180c10b07100d040e0003100d0304030101815107a0194501240200101d10182005009004590907005002e20501481000d009880c03504607510f0f50760b84001c1c0c078200191040011000844540202c10f0740540304420004406100410308031144a142c13040d29070020004541d940c4c072130007103d00540c82d10300c03403280314074403c2c80c6840c0b8400300c3c004017800085003001c8200414104200300070242d190401480340307113a84980f0200c0c02d620380c3d162542c1c003503c00d08407a840740c624903010164101035442c4105d0190000b500d00308400070f01150340203810301c2030101d0301050b036204000b122255482102803d000c0006030543d0140404001c2103141550300640740305e00501403007020b0100340910b00050365084090100c100444c000c104001a4a401c518851201d42000c00e601400ca10725031038004200e54904800c20580e00d0003101c540740c1d03860b0825a580340c00f58a02c600042101c40c000c1c22041c0408005800e004400d074801e42d1503500b0642d02680c80758008a00c1100200e15032020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 820576097 1250 820574847 820574851
    0x415180c030203070e040818121014150a0b130f0311041d060f07180815010e010b040909020102070504020c03090f0f0d030806030f15160f050f090a0b03 67
    0x1800e504450a00d503004243c038080694003c02d045d203151500b440300080c90a8226804041003000f02e0760f2a50003100082c030001890042d00c24a400392141002c2c20240c10313409583c50090810640445454080c07011080302003014405401204024080c4441c942c03080c06803405020640c1304400b007d4440300c2c2e80b0213140b00361b4000c40b408400038070b01000c1840d03c1d01034442441044404115031188061075140d0341c860160202160b110104003003006588901d1103521420f02590311101c1882e91031a0b0159103a000015201c08402101e00120311140d00944403070407120910655420b01d03040640403030042c1380000c1e0483c154070a0100005003130700d60380080d00101e00c680c1d0145817106412024000c1828509030307160302c1041414003407000c5d80c0e150b0381d841d607200780c040c98401c000350340301e0000c6403a040e40100300040303070701c600340b0983c0d512120b07001010301ca4034007a5208025a0703200d4000303032000d0301e007142c0042c042030007427040e084028520b602500224000810300390b046030b0f4804004500d5401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 820577347 1250 820576097 820576103
    0x4090c030f0f030807020a0206040e0901060b0c030702150f041a0c0706031a0d0201080a0f0b031603170414060a0302190906020705011701090518030414010e04090209041518 76
    0x4460b404509164004460340d41c02403180c00030780310031800c4e98001801d921890050041c880c96140200e00380003403d50110019211000404e5900d1ba0952480790303594000751b80403449040403c0c1070031000051b40003607400e0076090308400750415040c142d0044601105c0710707046117117a4007030118900a440c00c0040c0030040c01f59447c0000e44240388154580c104010000c0240522200c409000050360300c03654030740c0e00c45140c07500003901080291034400a4240343c0c04c0194075108100001a0b00c105080000d01124031901500c4040c01e5850312200541c0124464a031560328142020011403c25000078031500500345401458008606503040492000803002030014000b180140f00c0280c040100c84090402404c2214901c018000948136031101405100c2c5616280c1012920700c4410b002003841b60864032045e0780d2510b403541c08003020a800581c4a0f0300192038512103070b0082c2824411004c003250040d20b0101250b540b61124200d0006806440d41d41a0340c80301d00c454052240901003101c984 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 820578597 1250 820577347 820577363
    0x4050603131b0e070e09013b0603010c090b030a09081903061415091e06191209020d12200703061401050307030f02010c082206030204050f04090c030f 66
    0x306041e01d580c21103030014013032418400e41e800100010769602c2412811150b501c481d2102403807124207094080c19110340140700154201e82c500f2100405041c94500c84c8206400030050941e00740811201100c442c8503000e00d210702040411002e030010f400c4104881d02401e40f040c80c2c00049000e540e05840d00210380070000c1d0f6240c1c002e0115445510004600c45401c0b03032444100110000f12550900c10b06851612901240d81180352034215170341010703003046009240c00e88030380fa110541603598203400b494000140f40b041e80034800800620403541c13840e40141800c22010113940d03504140040c41c0c005401880422104240c18081030307891524460300c80c9003e1321119145141040a461900e00ca900d4803200102c0184200d40303000a04a0482e9000700c4a001c4180c1b403800180c2d040111300102410348480000c048000e03018801103031280e4048800d00902042c0e407150118101d02890251076270207032100f500e0003240c2c03906400803800c00d401810f120a41d95580d50b107240e00b02c854800c048540c40c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 820579847 1250 820578597 820578599
    0x1e05090105010b03060609040510080d0909271113051305121822181b0b0a2f01090b0a090302060c0a180326040b04050603131b 56
    0x12028041e1a0040080700411800d5050030b03030005544c1d02400c2403490150399288005050b2a904480c500014402c05069401c0b02240c140c004003105c03803030302031a00c0e04d40c1011282c101d502502c040b8010440c94990b802c0d201c1108030356a4152078a0b00440c041d60101c501a1484400c160610650b80a8041900313034003d4828186806414040c050806034000c49080c0030084014128151600e1032507011100401c0341c481c008240c40e8080240313000c508250b8074040401020741040030b5400a102d00901034800e07200304100707005920700410300031611100d07028044600f401d400b400701400b6400541e00307145501840ba40c0322840ba40b080c0b0412880b02c0e912550341d00d00f84050411110b41041040c1c0040c0722034038a503140a07682d44805080d00b0000c0034000307000d0060301d100e42c48000d190348104003216080c40e0b8a0a010340d1030200c801d01c03156160174000610084034055812a800c80e80c003c00100d00301898a0201b000c46c0d080280390f4003811401780310b03000000380101c425020040c1651511401a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 820581097 1250 820579847 820579861
    0x4091217131e06060f1e3005010e012c0d110c0301020f090a0b040b03070525030903141908070203150c18090702030909060a0b0a090806090325061e05 66
    0x4010b20f0035040e1031b000511001070000d1020794440c62500c10029213010803503004aa142480ca001c070050152a6510300074034071784a548190000051400704061011030504040b140b101c0b6000e5009240302141e201c0306024403400d004031401412145031a054500041142d8042800d90313119072031040110380c0c0000e120850303240680701c000c05003521110060401e03040c200321420608c800781c116014082c1c042400840c108540c4110340040326901c07001041450240350245c05104d446c00304035401070721039010b081904030000b201443d0070780c808883c207040c01060f1605649503200110a0342c042c040d03a040c2c45c901e80352807003800e07000d00501d0111070751b540454980c0308031700a4008100c0d44641d0108041c484aa9800000e17103401d400100c07005401a10b6403000541c038004150f0001400d4100890300383c10454220041c1411a581601520030030b0b03403150503c5880e4420346513007510448082401c200c0d61500408541421403040c00300188404c590b603502c02d420031140c0c01e0f40d40c0c42da840340104919 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 820582347 1250 820581097 820581119
    0x1b110616180e010e1003050a110d0215030f0c0a1b3f0f0503240307170f0d080c030c0903060114011b0b160302040504091217131e06060f 60
    0x840800c14082c020024110340d07c00743c494200b8500035200e603109281d02c004075a45d03449400055540200000424072185036105040d070812140c100b541c41c00b12000420382d0030114120342c0000c001d5a1041c0d43d0b13100348a895881c9001c21041920880312401c47d0466100e2030103141d034881ca01030b49503002c1821004108413032032042d40c0f07a500c0402c000c03482814255500001940c1d006028030110350310407240c2e0910b0001c0054010342c100c6d458810380100007007107004031062001e105004001d41d02085003000d00150b5034a460f142180000d0092030001d2803044240c3c2c0a560020241600a803801e000307007000030324048003070700505108981200b00105540e08040084111200d0404680c000d00080e21440c0054a0040405041e008502d10592146100340d04540c003501000b4404c0100c10f00a090240245c10316083e08008900801c1e50340961100300c01200d8810209c602c9400c1c842d40f9a581d034458407900c08804c042c0144604805800083c046001d0b900241004203440f00c100c1d45001c2000b00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 820583597 1250 820582347 820582351
    0xf060a050c1c17130c0501050f070c030c06091409061009091407091d06010f0e130e011104081b04060e070206070f091202040c0903080c011b110616180e010e 69
    0x240e00944c40490b00000307420380c5001007101c5090924680381c90540905143c1351141100080000d0715002e008010002d01040e030a0a4403070680e80e45230074070344541710b0303054000380c03020306690140e080d80000d502840c141c09850881100e91a100802d180e8401229040d580c01181c4041d0f0002c80c142080120780d8000d001600400d895114069860000d035511140301401a000504000c5000408000b041c00341c1c690301c000040180c001041d2007603502c8400c0080104d514080215400c10700c06d030034541a00740680f02903074000d90142c60360706c5250805a9612141140c059003003926140002040660b90f05200d1041209402810643c94071460003031040000040321024003080da48144950040368940720310b900d42c15200002c000b2044a419204101d00703600041c01c41e41d0015060b00c0070380041d00b1440b1030072000d091103010784904c0b1070142d07401411368400030b106030302000c0054580f52241641e54001440707401d11141d0788104469945030748106401c03070b0a072700404d54010418184410350303140d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 820584847 1250 820583597 820583611
    0x909040f061514150c2b03060b04061b080706020c0c0301060f09020d02121003060608010b01141305090717181c0219030309020306060f060a050c1c17 66
    0x4000c10703041c8165807846010b45610343c0e0241451585070031079910514101e0300c15504034401c94440c410054100d903500303c1956400c800b1384d91325800b60410380c1e000c4d0140d5002c1c0c880b4000e1b1a801c041c1411030032075640822071076540c0a40120aa170704081407040000303040b000c1c06030901580e100107810303c880c07611090461b80e0380641e160120030040030b0800003262081d1034401c500903030358000c40c10717001019000b03900c1d090703c8a0168005010300880d42040000880e4407420085c065280e4402e040c900721401102d049000c03603015010600780d002c4903001000302d03c0f46044116903560700e50010a1181204640f000c01096080b010008900071a04031264068039626a80002d410742020f41030b00c5400300d8900d0210441c2c0d1900d82d510280c020300c0307004c002c1050b103130007410320748107505004018012044046c4d00074010a804a4030500b07040e07002030309083e009080d2501d05600c5c0d04040700d0590042c1c0036058036004070b007880c0d65500b10301c2040d103522003000d6485040070030f0321981d00801803002030050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 820586097 1250 820584847 820584881
    0x3070f121103060916051c0f051510050c030315181906120809010c022b03080105101409040225020f011d010f0c05010509070806090706080f0c0909040f06 68
    0x1000d142503200007118901c0300b1f25800c0405c610005e407464009070501440b0802e02506240400581e00124030a1a04a180445860418901c14003095406114241c150300594004200007164048903404100601c58040d16491103500483d4580380b450b0b90613100884192003001c0511a52074007801001d01408850f10801c00c0c00a80d0b1340c40440500c0303a012050306120b00306c0807c6040d560b45149001c070544024104102080220b0301c1e4110b0315140e14001c4000c5540600086000d08200c402918000740580310650442c601003481c40031780c0c00105245500c43d400f00840d103042c0144c4120304800c40c2901003044292180f501c104000000c0c4040d545040000702c0c413880c0400c905061060610641c00e08204044403d1188100c9040781d0315030b0081d00c42c1d0b00300414481e900b400041d50400702c07038400c019900c040c2c41d210a8a62201c14601c94407000138800c00c0422103424040d90f101c0e400c1201e0440070fa01c2d02c8044404540000c008a0b0103940d600414100360040c005540295201d401d004900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 820587347 1250 820586097 820586131
    0x14150108120405031b0a0f120201030c0f0206060103050a0e01090609060f02280c14030c06090d02030d1e06150305070c0f061a130e0f011103070f1211030609 69
    0x202e07688031419250360491034034080345c040050300e5080c0018090403405058a8000b0703102c240c1440015907210080b80001c0c0f401e09095001c6104024070000d0401a80c040e19007a101e01c00110085e000141182d00308a07506c540000700c0304002d200d21504180300c1c4001148546042c03e00c0411102e0070002012040d004105400c0b40c880b800904544400c4a1007000344075400a0000321000d0b50a984000d052032110090011981000070180858040490880c0c059588021403940c403503074100002c101682c414003940d018600107401c00d01d80a880e401c0901d042c1c3d008805414107070780542d80541c0744c82d0400c1004c04002c6506010780e0703901c56510b0800804040903561441c8006000e140094001561750503008100703901680301d40b041c450010302022601c1c0d0301700a038100514060300800824802d0071015041000103019000402d0f0020030305604507070391a18244d84001c082c81c040c00420005801c034489000c101d1040c4110004044000c9440b40703040400e000c41c119001e011010343c4008680 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 820588597 1250 820587347 820587349
    0x1518140f07050c01090b040c0509070c23150c03040b0702120a0f0201090605150f01020109211209050106330e01050421060b010c0c1214150108120405 66
    0x6011a0040c0c1d0358500b05070f540d00404805801441c13804002070002100700c00f40000c0c84034240311042a500c1c1140c01e5070540d01c0700320050310002e030140c1000780f09410341070309444014510303c2c82c0340040d80000c1c00d807000600d41001220410800b100c42000340b40c404000c1c401808186202e484d800b041c640001c2c040401e0780c44170454503010f43d066100803c8a44894000914401e40103294140da006606024600308900c840031200003003200e8034000c0301c0c4690703012000d600c140550070300d80c1e81102250b10740c01258624003820700031803040c1c8020700c00c03041301a00200d0f501d4402e0b01216401000005011410b04144807000c4070941101e484403840340703d4041d00c0f1810a20141003045003410040c0300e480700500142c98500079540810010840300d02550b1094005020740040540b1030101041603403000b800545188095000207080100034400602002040300660402a03006404c001d94010f072100f081e51074441d02070550550442c60400411402000b00400140c00700d90030400c5081c503040c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 820589847 1250 820588597 820588621
    0x207150e0f0703120504120507061d061602030304080303100906050105040602100f06120602090901120b04030e01030b10020a1b08150c090d05071d0c1c151814 70
    0x30201400902c00555500350040c06001102e00034229005040032905a03412308940318103051140c10041000b0a400100001e101110b40f1508100280041e040280002c08440c92014a1000700d80512007008007058054040010b14840d10001154209240c10b1502020903205a84e1000b81400000e00003442610f0b004107145214074541c04001a0b048185e45811000d4000c650003451410142c11104c030500c402500240001c038401c0c0c802e00110390707031428940350500045802a26400c1c8800c08a800a4071400c00690115014940403030388022801c0010300055421f0307524800b5a200ca0081d104004030b06048414032000080550141c40c6000002e54a80510046440c402803000e0001070b2051a0541500c10200e000740c141d01c0d0104203407626564903140d5000b6021581c05803c801d007000d41b201c800c0c4600c5842214501ca0511000031041d03c50105a8650200142d845000c500304a01c0d030441040d0090400710000e43d44100c0525a650840d5a060f580b00b0b5222044001c05c1070705000c003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 820591097 1250 820589847 820589849
    0xb1c060506031510030b09070c0b010b070c05191e0e0f0f1803070c0605040612060303124703011503030f020304090e010c1101050603120903010605040207150e0f07 72
    0x6644c00c01c0b1007143c1400482c02445007242c0560700528000900140725800045015040e01c01e08200c01c00b80d8840441d05001c0c0030f0614010a8246030140a01c918200244415045000f84501c80001ca403100020b0a41c5501a10b0302203c101a15038104a803011010156411080340d00c480d80c5181041d000489520000070921410404620714000c292442082103032400c5030002c50708000b09440c0c0500424940c054440c0c00000380e80c0d40c401c09003100880c0b260380112503164071480d0b030140c0151102d00c0070313200c01043c8000c800d042080a6580309440ca05080c034103201032000303900c24806184c40140c48440031241600980c580501d2040c0b0311741c100340000c00d80342c140c01c04030320581c8400d41c101c2c82c500c0b40313801005415003440d0728120f010005401480c4800240e46905410032010f60606003281c000300e0303246a0646c080301c03103210981d000400800e10000064000301d480b5486101041c2030360b0025004503454080c101c1d00c010f03250880d10440b0024a400006005002d0140400955540107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 820592347 1250 820591097 820591099
    0x2512020f06031b030c07062a030c14070515010b13140402091207181b080a0e16170a0503190507061d150903070314040b1c0605060315 59
    0xc00000f15846040b0264403007203560841d1201a038902d07169002010b150001d103011103829042c01c031002d41d003000709205004a022612002c401e08071140c04114081d094034a482401d0103081640400c0140382030f030040480c0c40c000c80c006e007500c5800038802c0911650503407100d80071140601c122030340c40c0140488007040b50448521144260a8000010024880c04281583c404040041c02c0702e5108042190405c603080d0304500030502c5030504854003503440c5048030483c5107984020716800c881c0541001a0802a895400140c2c02e040001417481c0c0262403110b50a007a15440040102c0064101d14008403032034200501a440356680e1156901c0c01214074121850354990044001c0e01e1140082d150002c0e00480c05220440051300400100b4241c036040c4202130041d0034915120f0140010313400e01030020b900c0154588105610112003803244004400d4552508100020f86860000040d12440d01c2d58000c0c00019990214944c007101d4669104038020702041c42084513000c1011400901250 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 820593597 1250 820592347 820592359
    0x12030c0f030c04090e07030309080a110108090a2a050d0b0705070609020307031a0f0f060f0a090c020c180606070b150301050903090a0501030501030b1b0c2512020f 72
    0x2c0c0c44403154001d0060340c0103440114504000150345080010340034084070b01076259240e100b03840b0841c0701c0c0c48400c100006840d180c10285c510b903542d4841d0301d81359407080015040d20700400459482111800c2d40b00488005090300d11090341c407913144030780444014602141c0c0744211036030f2656026910a4000c00c40340600c280411500240003070780d040705141a030700405850120b5220719140d01641c2d4240a60b03001c6c0c1401f1000542c0203904411440d00448861103142e00a513140003c02403001d1001d2205900454000400074141000b4080e00191840d550050014103841d08144a808270795650910a418441c50500509440744800c40c0da015400c500d41014640e01e003a40058914a0001c00d40c0d0590b2070501004240301c0044080e014840e81100d01404140c3d8420046090307507820b0001504c0c0c00d0101c0c0208030300082c9612203900300d0085020b03d40c09c02802402090410141d0840c04070000540540802244040c0107881c0190004502d410b400104d10740214203203000002d0700e603004076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 820594847 1250 820593597 820593601
    0x10b090613020307090b04030f120e030a111207090b181b090103020c0607081005062503170405060601080f0c16050c0a030809041b0f0f0e0a03031112030c0f03 70
    0x1600c66005c56000e0028180410741c6c0d965079141203220201e41600a60b21320555031188415207100e00907011560a006009140303020050700e9800c1002409001d4552180c9000c030341011981d424400c140040804800c00141c5101171001d00001a90300749421050a00082c01c100c00202d102e40201019035440180ca600c030b120304001a0024480c6400480c060b100f407000b085075041d4041c00c118811080c0c800b42d1101c180d0344000340201c0e03028001c030850044071000102104013201442e603d045074041e1400d15070b5401501c4403000d140000380da059500f40c101008200442d600071880d5500240b210303244195919003490310b401e150207429002c500406101c0120320900070b0400041060300343c0140080300495483c9401200e650150b8110750240c0d0501d0700c400c42d10340d540b00b031001c4681d001b52a00300c041c10070070904035050300380034a42600b4010403d04007086078980803840b0000d18484d031603100e80021701494040c41d064240c00c2c0720460600410070011001c10710420b0b1007181d4001410142c4076 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 820596097 1250 820594847 820594861
    0x30c0b040c0512031c2304110a0303120b031902061c0204230306010503030313050a060618050f040203102d06171614041d0d02010b0906130203 63
    0x90840c1d0b8000366209008891040707000d44044000c09166a80d4203038200c1c8285a24248010381d42c1d07005080044074040e1102d0040c0310500c1e00c0f4681d1061140c4048009080c5401c0050141c401a80040d000111070a030301c0c8400d20f00a126903440300b90700700c008112208032081e01c10405106d00d42c00074001e000c04901048920180c45004000c02c01c41c3c00207540312074940d03c03860203102032024001040a0031801070040d07810b0114006040e40d00107006945036548183e4442e9000c0806a0102d680f80b06030412500031400500c110009450001d00d4804040c2c4003030600703811f41c1c1000d48001280c9608000340001681c0000740b22001000b041c5011510907000d00014100f04118a040200d103034400b03010a42c600070710b92042d0155403440c041410b041c2842680c007540c1d01c01080440c1200401c2d04800c2c800c02d144000d00780025040240081004c4d1070941d00d10f52480942001d00482d03038092401140741940a025880c141c50055036410000c3c909040007907010381890981070842c6070b0000c007040c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 820597347 1250 820596097 820596113
    0x110d02160501050411011b0c0905040206040902040303030c121a01030f1d0c031507020a060b060c03070609120f12050403020114010e010806010609050d0b07020c040e0102030411010c030c0b04 84
    0x1640d0031600820044c5401c0c1030141d83d01d0340700c56200d80015490300e007160700e991012413419003440c0c20040d240a654280b0005400600c000f900503640048188070002d00300d031442c001000603510a580105007003860b09000392210041c07400c0b5501c201e00b0280d0701c8400501200101905140918011600101290a0900910300924860f91000702210a0001d540b00087e19800c2c1d0f54050301241c0e411030452a441c6240d82c020303100d920060304181408400714400741c011a100d41402801e1a14214a014103d80f5540c0b1880044840c140c0f03030450752042c000e4008a80c450041c050909034030000720000000c101420b0340b0940c0c026182d80b000458240742c400d50103580780080348588100c5550b154540f83c14a0b140034071034610700d4411070002003a070510944506007110701c007070600091162155500e881c407040003400c60b0110b1040d0742c40d0700c109503a0790081d242d0f010440d800059803414241030461000d60742c00e200c54140402e040c1c1da40c000a5102c5858100640c20400c1c0c0400c0352510302c2c3c43c0c48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 820598597 1250 820597347 820597387
    0x9030827041104080f03090a0303080c19032a0c081e03010324090201210b040c1d0907171b18010314070504060509030a02040905060603070603110d02 66
    0x1d0400d14080e0030b0701000d030b518002030060b202250304a81079031080c3c1244a41d40c1c4038000000b0b8101c0d280c0081040080c1c0204005a0800d41c401c1c51542800080550210401840180340000035101c0080140e1004400320a01448400400c0d02045a0b81c00f40050031145000744000c011316030003d01c8030580318021142c20204040301c02c0740c07640c070350b902c0c1010902044102c1000c22410b0b5942c91400d5031241620501c010640d0603102c0b0407010843c95003000f201141c0b00307030742c00e600c035100c0d4480b680710307a00c500c01e400d00060141c8500c03000303e82c1e142d14161a00e0001c2c001c1400303840c10300300740002c1540040448048011072801d880c09580d0b0140c064000489004407410004400301300304200d140403013540904080b0a80e0204002400402c08080000c020b403502d401041d0100000e210041c481e00041645c0c0310702070110303500c5825981c0030a04403240b1b0401982c10750402401d000940c5014045900100041d240a11001c400c4403035401c810b10a81401018442c1d00094a107804a03220030408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 820599847 1250 820598597 820598599
    0xd050705090a0203190c14220e070f0513121a071e020a020f0603070306080619200d021c0e162c0408070b07020c09060109030827 57
    0x1985900b80401c19401940043c0c62101e85a400c2552105407400c2e80e00c03a6500c01266a9202241640d039164071203115807003111000c28134100c215041c25851140400040108101e0003000c065240c445001800c1d21010040401002070401910024900259071502910040070500b016a146854810350005440100c106030316841010000340e1a0040d09403084c100f80040c10802500206100300e8444103030b410700070760003900b444d20030750316017028400f440d40014a1300b000030f40d46884050300e03464008110b41506d030202050b1121881341c0041d001e400244200c00c1e446440c40d2064020b5201c140c0101c10150601541c0030804026591083d23076060721201c030818042211410400303400da1181c0c0780602d121080342481a0000d400c44402400501094114040d0145003c0074500c0d01d00c003250145c000d03075030b0002c02c4c040d10007c04c0403450b94a008803103940007400c05046440034070070440c00c010300c0300e411300138051030810101d0b1802d0221001c00c180bc82c0c841003682c07604480d400c40b9020740403400d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 820601097 1250 820599847 820599859
    0xf0201080c120c300712050906181e030d140103020a4a070f0c021201020705060c04080705180403120e070603090b060a050607030c17030a0506120105090304050d050705 74
    0xf10803015240105010300702998600ca400120000c10031b080e01d500b544c01c0e816550003c40040c001c4134400c21070000030351781802914038243d03024104059107115102c0c2d8100c0c68100103203011a0b000c05110b4075626111030010014250f15580005640c05002c0c858044551540d1310601c0c000c4940007074801c41e107000d08100812001031a0070f8050740752003581081940c5400351001c45c0b190fa01594550160f0100d99852080880007035007400004c0ca000d030450500c40d90280400c1001400c2803107900d110307840607805180c849241c184224900f1016521440c01001c4206001108182004076142c1c001e030542011030b4a0003200d610b2400404082d24105058002c1c1d810104a50307034903801203505140a81c054813090745514003000300d24243d03407003400e5104600f00503803c00240119031034040d66026402041c500306c0c104400000b194000c5441050309944c0701c081280a2409400c0c05080301590030013080503241031851f580d542c2c03140740512881070b0031041820040040c1044008060400600b80b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 820602347 1250 820601097 820601167
    0x1e080d090302040510080318030a0807031116080d0f111c092414040e0a05010905090307151e15170f0c0103091a040f0201080c120c 58
    0x8018228000c078001288034601340800710380850043c42d1307441c0135a50060041c500d004814296910f04000850880390107025407036420000c184080d0203400340c103010341c503070300401c42070800068105846480c008100710031101c4280504400000c20501005071414065290a12208244c502104102981c00075109030205503021581c000080c4507204290f4807803210700384e12214082d0480d411240f174100b5007038103034480300034607441840d2608001c0a1503548902d45a1180c050ba031011004403901007a00751141d00400ca664000d2081590141c102e402850400d461582d8008990070409200c220b1162102d82041850801d00207448032200002403c008440c904007214000039550f1041100760b801c0e0648030030204401046006140f140103014081e000e03880d20055000b80b0115105070399011103d0300d9550301242c2e5621040c0200c2c02407800342010100361000502c550030041801e00c0d0a68107225901d07040303030121840360f00815991580da8894240071405458480305c060100c81289100781 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 820603597 1250 820602347 820602373
    0x2090405090c040c02010905031611060d0e2404110616060b030f03040b0406121b0206100501030e0a020420070f0b0906010e0a0902010917150f101e08 66
    0x5100c4030b1102c0603542400300d2a0b00c040140d013214844c51015000390010005a42070030801010040c03c03038032400040d291700ca00c60010078920f411481e5040e004654070744041212083c01c12954484800032405c1381a65090b880a450305140c02038030041001507030305032110042e40c0d1042541c1140fa078110310815a0505810300c0009080020000e9020b4041d42c40c0c0c24000340c10220850b0250f9a0000030945041d01d80302c400c49581c0c80e090503038000380341d07200c482040824070303214103071000e03515507000302120b0070410004080700f64154442030502d45021074072420444046417450000750100c40c0010301d0080c1c0514008044600c5941600c0c4030400110a0204140e4861210f0707500e0007100080110780d50800a01d0742c0361030a0180e11040d44c0c26100241c10310aa942284200350720614201010b241d0303404001c000032801e100e1302d00181d007240c90189800c2c105d02c0c0702703984c0c80303044541c0c0000385081a048125228426004030500e090754035281e9100465846d51000040c102c030011500403000240d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 820604847 1250 820603597 820603603
    0x211b01020a0c0b09010605090f1807030308012d051e15070302060f0c0706050c0d05070302090f030712060507170c0306010e040903020c190e0a0e1207030903150209040509 75
    0x242d0448a140314000810200e500501c0b900c400d0301c80c003400c2c1d45040d44030300402801840b0001c0c00004a0001d29050550550701800300c80025482511980410f5041142003146c0d1019041413011081c04103030088540e0441c04403046c22100256005107030404862115031110b800e1444458002d11100303640e44081810764000c00e0005d0081c3e00b91080c9494200300d20070a400e00f41c03044c40c183c1030148003080c00303d01d60b684060341005002c080d403440e14028030451020b56038115088400b1035804070301303c017950500701c8850000c3c07002140500fa5030b03410a00009a016845500030305020b50710000500058040d47c0700b031342d50b50102e00d40102207240600c00106290703c00c6901e5400544411a860300c941028080c04a400368141c01030100310b881081444010f810a402c110340c214076250313000070030b9824820528064403507000007245440900d00024540540c9003210700f50100f040140d0804258005440d0050300e6200d4400b41c2d41c81000354080c0b002c4c2c040c40180c580e0040c40e0800f0f22406003000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 820606097 1250 820604847 820604867
    0x30c0c070806070e1302041205210702030a12050f0408010f0f0e0d03091b030609050705012c04060510031509150e0604021e0703020609211b01020a 65
    0x44085031209500d8001481d01d46400392003110220f071040c52600c9807490a1902030310216000b003030050510b17613035809440401101c04403d4650b074014100300015040b080c6045a818030a50444a02e40549603020981e41c00c161900a088178603a45108007520f40308070210b807640325034052102c1d10f558468802d80d0081c000d0100400880d80303010781111080081b80600d0f000441800060010300802c450150081c0c018000111740740d5900b40c510740825407010079031070050350240c01c0000b90407100c2d1030f00d00c2c680307a4550015130501c180d51840500105640c5028522640c1c03085800e4555407510000c5406001d080e00819441010486441c40c8a68581e205011138402c240240401e00d0780c46034a4802c0345c2d18441650303c41c0b0a041c03028003440e21842c00140d08501c010308018603000703031004c1c0d4554901d848c0302e0791410700d03078002551070034954104817054100410f08090319640720b0600445406500c60307940c0c001002004034040c03034440e0100300316081c5080c5c400000e559605810380000c20154907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 820607347 1250 820606097 820606117
    0x30408010b010c11010e0d020a08030901120e0d0c030e1807030c0306050102250f0308090111010b011e051306050301050a0902180d020a030812070809010c080a021e030c 74
    0x7800030030042030b40c8201d5441c11403580002c1c168480c54180c0d030044441d1304004400300c0d08089034106d4000161141e444410013000501d000d1916050709070300041c00c22018407502802e031410300046002040021591010404c0c0c00d01707290802c0440c0c1d01e8290f238074100300c02180b03070310000c01c41c44840e00300d1907400c40a00c181c10658040090600602050b011a540783c0595401644005003480398801c03890507500055030321141d0285d2059540c001342c429028160400c80304a000032882445558005186182d82c10340d58009100422030140002c004188500041039070034034110620841c64060b00441d0721b03035080361350003009a0b519443c02074a10b50080c8a214010034400900041c04c0748a4800d86000903e0700036403000d5102c03014100300014040c10030a981c000c0510a00000003010075005000c4c500048801c050b440c036041e880648503800c01001c2900b580d05201d107600c5101c1c2e01001055010540304801600c0d4411000c01954011041c018107003c04000411f000408042502a00004503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 820608597 1250 820607347 820607351
    0x30c09050921070201030c02150708090a021207060e0618060f0c01020d050105092a09010519020106030303050c0703020606010c050106091e2a050c0a080a0305040b0f0615070c120503040801 83
    0x118524100c1c0d503105210361a01d0048421400f18ae0307201d00c80c58460760002c2d211021031f01401c07001e400182c0340003c08021200541e0104204000f00d83d0002035140c030120003224a1818488041d07022801d030180d02e00050711610000402c500d92581c182c0c02e0758040c01e600002151501c1d590003000004181c02c0c06294031072580d4600003022036400f502c8000014540709003142d24501c003905c1140c0150022000c00703050100074007004860b55a0f480c100071901e087caa00221b0418954100a0125803000e03141c4105500100b0010021940010f21990400d038207191106080d0000d00380f441c0100041e8014981050030411514441003141d19140c01500c04a01e0401c4000184046168600c0e030320360708054090075001d40145190301500c00381001a817204140d4480855940e40c0c0e032102ea110b000641e02295072401401300740074400800541c0301754203a032128a242044800600d01d100f88c06030342880000001150401c108110034041c0040c0900400144014001d150182d103e80150040002c1d0398 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 820609847 1250 820608597 820608611
    0x30f030e040203090c1521010614040506040e100305030f0d11070c05102a200112021b06010303020d260103020d11090c04061107030c0905092107020103 67
    0x4075051085a004070b428400406809039450b0a000c50100140421340c1e0100050243c1024004845080740060a200b545207000758180300b4064690482200c032103444c1d1000b4130003403026455040440b4251190541c0180342c56640e60710f1060000419000103246000120ba492503065242e006001e65100280c01407284010120400c9081e01a80030094900d8001820070809401d01110364100f11000b0314002181c0d40c02402864060299621400c1c10307032402e2808141440310044404c0c40f8242d0002841080c2441c2200007402131701e82d00143c105480c2d000460250309228041e10811090300d040a840c0603603036a0034081d49a000e0303040300c18042000085841440c0d81510304050170780b04009000d015590035030302480549c8070224000c83e584030702d034481e03c0041d9403a40c03a0310b0302c5012a4201c00c1d99550074058010940c4030340303604038155a4080360003800000c0c0075204120a440109000082580d6241c0f4198601328202c0c04000d0400e480398000900304a4050084c55014001e0320240505 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 820611097 1250 820609847 820609849
    0x706080c25050f07030b18060712020d0e070f0b04081515210f01020c100c05070f03030219082e080d050315030309031c0216030f030e 59
    0x44410010003103041000c4050144000740250951588040c185641e0721a59540740c0741c1070502c1084521070b8000e1404104001c20641001d42c4403402d0000148800320041c41e69036210f00241a030410b100e50049800c0c2c9803006c40d03042c0c600b80750501006004207480d40c440c05881d00c10701d0117000c0c0c2e42e541d20310300800d00c08299030480d421075059500801100c20b183c0d05594681c80c000d04000050012210f03028000e9071096070156203800c00300326492a03100d1150b11300346001c0c00b81d0320213400359005105951900b68041002c000301410540d007c41d1f850440c074030840d014030962000030442e007030b50002d50307051560641c044c01070b008500c10429820701000809039801030084841c4c0c01070004443c0345242c4030355600101ea0140c810a030407000d07415110280b00c1d042090841024001030404010420524101c18003038112080c2034001d0342c907000d0200d0100b0785a8008203500b81e840e02101100c10340301842001451550250b0141551549480b880d001c0f8003140422019800103d04041d41015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 820612347 1250 820611097 820611107
    0x12100f031a060a090509061608011d0402130219120501030c051e04020d140a05010b071209091b0e0f0a0909080d090b1006020703030f05030604091a0105030706 70
    0x50300e801440c0000180a01403105801c440c006221a030001103940001402400c540160303400b50360108060130051030300d4075102d100c580c180300e054800c20034248010000303016003c00c4141c0400f100c00c421812566180007180b1031100c0780e200003400910000300515640324040ba2181e00300310507a00c001481c42d080c0a0300c0280c99003800007501101c8461820001c601e40040003d41c000c04006001c40c445c0310326030025040b600031000700221b0a8807209480012a00010300359800398140798200302c15410190040203a0141c09402020844000200041c03580150615001840c090344c040c0000070100401c0000308100c240c1d01c00100b800c9100700b07500c511300030360038040c0c888000c1d200c0c0341102e02d01203001c00503282e251819905081c0c100280d400e01042c42c010095003500407582e410b51420301d074201d0a581c28495021104541150005000080e84032a40d0b649050300b51410b20b86949602c000103004214030f000040c019400729031040682d003002000141243c0e011402d6030540c5a91300020b0312 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 820613597 1250 820612347 820612349
    0x1725030f110a0b070e010e0a08010501050a0801020c101107052e0c0f030f020702061201080705030708030f0d0b1c0506060111030d0c0e0a1202150a020307140f0312100f 74
    0xb1007503c00c0000038410728400c42d40c2d0f18080005142c40011040e001e4041070411090390000c01081c1d45400050080303040401000000341400b600031071501c6403800c041364a410308040900002a22480f0406a10442c00300351041d1070b40100988458840000e80d01c4200b4120500ac809480c1c81100c3c03010051526114101c520062915012002001718408600401d000c3e20300c0c072080382d824804000542c49410152001400c5644680d0300e550401d54060700d801c5e0541d00c0184250b00c0000d0600c1740b9000482560055002584516207420b81c50400038041e1002418483c2c20070000351002c10032400503050700c183c05024800340d07401615690011541d5005031510302d461a40104002114407510f0f03809803201403031a02e4100c1c4a0401600000d0485010342d00401c0c00315040d00c118801c0d807038040704550040110034145450100c21080294070ba00415038041d10319089a1106000070742c00340054284070b0030000a81e5603030700c10360144102c5102c09440210300c66084220115401c564401490 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 820614847 1250 820613597 820613603
    0x309010b01111507111e0c030d09090225150f060f050904050c030106170607020c1c050a0503030a0c030b030d050f131203030902030c010c1725030f110a 67
    0x90f50f43c070040f0191074158064444000c2105400c0000c0d0504802d1240190300c50b600300b584124120070140b89445c0c0410a6105072098000b168100c0321141c000081c0340880719601c02c056101c51003041c5001400d4810802e01d94280c4840345001c0400206000f144401e078a106800c00a10390761078461002c6903124080c0034031030840d003642480f0074903090355110f91041c450000c8524140200011070709407000c82c0c0c4217014480c4140c4d600515400b0900160b544182c03540b008114210302100080d0660641c610030035000014240390b0428003109104000c035050304032084071f030781c0e052005001d4001c04801a9000000e40350202240f018500802c03000450b101e03581e0342c1824680c200c080c4400a5002d01c41001d00c06180000c00581900c151030140040c41c000d490000e01c9605a00505042000c0e000c2190304000c0c486446200280941300280301c141c0390311049640351505080170004d00150b09080e0b0701da261915110604140d40319419144021895132408509088148940e540340c610003002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 820616097 1250 820614847 820614853
    0x3081801111c050c0118030e01080a1802010c0302010b1509030111090d030305090a0b04030207090b091003030e0a03080d0203071b2f0d061a030c06030a02070c0e0c0309010b0111 78
    0xb8600c0d00e4401c0000d020000740740d0303000081c1c1e0740520110541401c08120128003140061100c0341c025a045280c4035400f459102c000c0c808040c0d0781c0e640340b91030303142454000e060020024200d400e06100754850302d81c01c0742c0a4541c0b00306c22541e0102e000b468001241c40b600c01e40c20002c88035104183e80080d14040074000e0201c1c10803400c0d654040c1c1c00303000300414000c031a201d00c0740280041440703a1201802036010703401a280703071420844008142c640000703925025604407018004050500040301045039054504604922989030000309150303116440030304403001c04522401d54240680c000c501070407103602c0d00c680349042040c1c0c00301072132044580031348064800e05402a1000c0c42645545240c1e9824000b0040c0c0090100002d4101407204001d550280e079920384416009480c40d02c0801c9504214002c05101c8501c4000801a00c001480050ba040c2c01158680800403440e004034050010b04204551a240090081d030040c1c0046825078855828605540c2c4503500580261915078100c10103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 820617347 1250 820616097 820616143
    0x714040204030809120a0506011d06010807050d2426010b150f0403021c231b0f030a05150a02030f0406020a0c0516050a05090c120901060308180111 65
    0x200f12040d820342007203170554001c0103803010000e401440b00d035003c0d2030070043c00e0215110555400c0c490300c10040045050002100c10700c4441500002920b0001c9940310b004038511424044a0518803140300394200200514440400c400a4130f800400781010100b101d0202e2000700000c05090b12040444035410410060342d107218001a240141011034000501900e4160f80764013085001c2c0500c4121419588001001e8040100c05048078904041003482d903080c07503030101c400d15103522074902d0200d020380101d40907240345d07102c00e90b10142e050340003000d94901ca9002c1c101141c417044801030202850305404005490301507584283e9005200d0404422610703a20356848000940c005000d500612080041070000100d08001d0340c81c60700da103c5404105107107844180a031441103600024403032460a820042030b4100b03a03083d43d10f02503101003d02183d485400410340109100e40018040b0300b00058450307900d030350900c1603a00303e62080c0c0c0d80303030ba002c00c1d54a80b550700d85410308032032005140c81e106 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 820618597 1250 820617347 820617349
    0x21040e1b0318070302130204080c180c0c1213030c0f030c0e0c1e2d16021203040602070510020c010f050319050406090b070c0c030210200714040204030809 68
    0xe54080707480c0140b021980c0c000d0300e80e00007680350403a1450b40c0c1403c41c1c0028044c019501306100d2180d502a00f61030310b02000388500044c41b100304c0010b215000740c90010a1510115000b00501c54921360710880060b51100100045141e88034140825202ca8a02103800650035101000301c10031a9007020f04070304454100003c401560102a00680c10011b081c0182442d01c003a03041044400702d43e5441480c0c0e42d00042e0b071242140d0403c56205096000c00640d240c401d0325081048074190f07a000c4042e0031a03e00c2c0c601c0090080310301e0404c2006541320108010901c941c002035090245c0300106c8200d0310a00710b00741c040760340b80c105110f0b82c0d0009d18200d000811040c003850107150070000e1924041004004100c90310704441044409803806c41d280c90070b00302404094144650007402a2600c13a1038030301c0780c1c0c13241364543e10180f20090245035842130308000e840c811100c81c100000c000700804002c503040b010703ca0352003040b8010084d07100350f0412603c155180c14404ca8080f40e60085140c1d0500f04290 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 820619847 1250 820618597 820618621
    0x51c11030313060209030d090f06030c0c020f0312071a0c0406120b0303040911070b010b0306090705180406060804030e03010204150509030708010207030807090f031a060321040e1b03 80
    0x40b03000ca07030450f001d01c01c0440315034060003800329140c2e49a86035054540740040c8031f034022040340e10920a00d07103042c1002c1034807a071001d0401007060301a66000083c3e0110004245045414903900141e0303a00460000304002c400e82e04c1c00030443c070104808031152a05100041c040c41540f240030081025810300c180604119080700c1e817200f00c000c080c2e80c10306544030b80d01c1054954912020721001000261041000b0351791404a0240c4a04410982146130001c003080110002800380b45c1800b001107082c407030f41005000d03101140314019000340035503a51510302900e9204c06680442c04560b4503482c28100c1e0a051081d00c007255601242c84c8212040c40200b40c0d155400540700c0b0390540148240440c92520034002405c500f0701c02e55615240780342040c0c000f8200145074010401800013400c040011582d00c200f80400340b0038602501c00c3c980c5541001038a04101404e423105150f90b807009214800c08400c001d0012201810501e403183c1c1d49400b06449888250051402800d800b8400f05592040030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 820621097 1250 820619847 820619881
    0x90d0f031106100e060f011106070306030302120a020304051201060b04150f031103130f0215090118120303020f0c0607092102180709030503030906010609080a02090604110403020409051c110303 85
    0x40c1800c10b408c07800790134001e007008021a540008240c445e2020010554100187c0000c80414401c0038106144d6020084d200d12841c0b0401c3c2c40f60b03101407070007110313502c00303501000003000d541000ca0385e41da56419013180d40174000d0703104901144c10010141503890280c00f403c4401c1c085454018a180c1c0ea403140ea50031107000b01c5090301c043c0380c02810140180c03541014a005185035513811502c41140100040c400c48034110001a01c9203044000c00c540d1514480c7c6460b0300394182400361b00c5e41c0c1d100070700c01028000e6900708078a512881c0d090000c03041e000502c10b0142c8820341c3d00030400045a0341e0328505088072100094011f140504403c407150007002d40903401402610b06001d0b03099480e151185141c105a503602c4050f041000100b00e51741e044002c000041598401904000c40c00c0d400154990030020a10350082d511401040c6080b4510b5040f40c0203154002e004101c0d0701424200587c3d43c44180781d000b00808503001035102c92502035884203440000c0c90008602d1680e41166442a07a400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 820622347 1250 820621097 820621099
    0x908150402040218150301080f030418020f071b230a0b220806060906120d030906020c0106141804080406050c01090c03050f012906090d0f031106100e060f 68
    0x14903130541a4644d00d003540005840a80300394140c49504108425041c00c64042030700c07645500070042042614450310500010800b40c1500580303030914044d410619100d0103000808010800b10b60701ca80c00c81408201c020f88220030020014404070382c101c0c11aa0020b203002580c0030305d0300c0a040201000840c01807019980d20303881400e20b008010340b10713002c520403908118060703040134007003054030f0501c80c40701c951181045a10301d44054004403419140d80c981c1d041d903000c05445661100600c441501181c205070110340007046240c2d0f03030300145884102010152481030910144d958000c0f4101155030380160782280500746050302d000c209a4650780039510818113552142505404900003140010040d80038802030029112219101c03421503032603502000d085840390007054103843c041010340c0190f840544600b903940c542d4030000b9150351520310300100200b4182c0c004c44109030740a0b002004140006045414a844d003040042000c209800381000e08000c01000650500e000e80c08681c203400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 820623597 1250 820622347 820622377
    0x12141611061602010b090a0f0c0e030c04020331050f150103110f100908120703020c0907030e060a09060f06080705010c02040e0d020d021902090f04061b08060f0405060d080307050d0c0f09081504020402 88
    0x47d03004d10642e040c0ad435000411801090840b00081c8901444807010480c005000352080d06900c1c00c030741c0c43c01007040c04003505052961141030920746846036403020b80f14005100c03080d481c010013030007020801103001e480c0b018007408241d10300f5012118150740c805c5524ac3c000d0021066480207120300b444000384a0740415032104c0088103055418032030680600035684003c1659009400c00005540081d450103c905160000070481c0781000300d00e00007a0b030006d2038600302035010390001402074070039100528020f019192099032501d80016960150000540aa921031542400c01c40d200c0104140042d4014030f540c00050100102d064600d580203103d442d00060031400d042d00f1070720304102030000c0008a080344003400003e14001d1510011840308032014451840c041001c01c40440b07605000514580012000c15402802542a1030000c07003030690411440c51851001044002c203221030b980400c081100104490340702017038070440740100002c0c10360651a541e01744802580302421401c0c01d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 820624847 1250 820623597 820623631
    0x30503060d200f0f030601090b010e060301091a010203030412031d030c0703030801090207020d0f141902040c0314070f12141611061602010b090a0f0c0e030c040203 72
    0x20b454207040140e030b6950400500744002507882403104650480c02458030626031411250f00c2c40d900000c0c4281034071201080400e1051217840180c1d0301409241026500c408048004070351405144d1144c2e06050100f42000145003e54006980742c2c031050360301030031a030740d103504e0140c801d030013a007145101842040040c2e0528a1600c03420781584c120700c04952181d0080c16040042c545c3c040c81c0705002d060b40c4032086143c60860742c0050386102e02d0241c01440a1401d00b80c040070302615487e440e00f01011041980d2082402c00d00c541842c05242100324440c9207070220781c0740c81d01d10034821018004011001480c42e62103c08094810324007144c54401000000b00c1c07640f81021150191006490482c0341c6203950782450803ca1203101811070582040060742c138200c00100b40c000485079000201c1c081d81440d0001d0000b022800741c0341e06110190084150014804504401c1d40400111980401c08220300748119004455685016280c0c543c980d00c0186a00032070b01d40365001b1904442c1c102540b070003071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 820626097 1250 820624847 820624853
    0x150503040615152304061b110d14060a050622060b0d09050714010c140127031b051c0905040504081e070321021c050717090307030503060d 61
    0x60b0802e520700c005910b0304421301e004410b0700d445014003011480101c0c10f1a007024001460000c0c880c6003591092280300c0c0504c02e10801e01c0942a04400152603071074584914204001546440f140c041c00030310804000030f0030303da80340c8181c2d401840001c01500303090000881d001224100c0810b07610707503903983c4c3c0c10002e40100c10800420482209080100d04c61178642000e900340b510a0f0700160384054084122180c503a4080500c1c42c4003540000c4c0400307031555a007c1c2c0c500400303062440640d10904681c048103e9914003444c2044c2d82c3c465030342c010344004400e0700706181101d101801441d541c01025407c00d9152102c95620440c5001d103403c610850b9590300044c1503900c180d406484541000403022010210260001c41180442d080149040500e80c2d0081c00c114003948004030103029041390020424164045414003401d48440d066900214000500200340686000300440d25056084032140c1041070554803400208001d18140602d030707102a0b07803030f0340b005105550290040c0121800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 820627347 1250 820626097 820626119
    0x60e0f030a050105220506070c0c08010507090311031f181a01050405010e13060b0607060903110606030a020d060506120d0203030a0c0c050a02042412020a150503040615 74
    0x540b8003620001c6000e0420801940b05009050071a540707407402203201c0408607200040d800e81051a0b4a000c000f180041e0515201019035a004014907500708024049070b40d900c8048042642d0107503420341240507109081641d50101c02010a50b1071007414026180b0516540c04160640070f28035014540d0134150b41c8005001041c8806600102c0d084030040c80715080500c160383c05000885179002407070420700c049000360701c4100001000141c0301d103916000e907155407096032182a4003601c244200300062802800185a001c5404928440c00f00064618034000503070321035007600a041001c0400c240d4440c040a450014400c6420805458000902c0c02e804c205107000700b602a400b5680b61705114410400f03541d80c1e0300d00306c0c0811256088410100d00d000c1040b02e405681143c0004401040200e035064507095840068150f80c0710241c0060060400032078072503950b00c02c031000c0c0325032911003040361903001140031500b0005509000040024805030700842c1c0c1d0300c041001c00d0f14480d1f030794006030075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 820628597 1250 820627347 820627363
    0xf03150f0e0d02100e19080705070320041a0a140f06040602160e040816060b12030408010b03060f0f07050906160b16140a0e0307061125060e0f03 64
    0x5038003c0400e42003024851040c1440a0081c00140482c031041046c021125520743d00060160040015004100712080200000465020440c4204d007144442426048010074003043e00550414040210350002c070f1200d40c9800350700170511079286091007156000c0320b0b151841e0580100401b26054400c0c1c0da060042d0005000c1c079401441b0016522035055116026a400441c0140024090100207000300080d40c080c0d070040c00d549406001c841c01c2241c045c2501c00c07095900104141c040c50310340c0340044010000d55016100a104c80005c01003856902c03401110707075161401c082c2000c5250030381c0744c24000ba08007286150050404000380009141d0382e00002894012058112440d0b0030000100c1029034416910100380f00100c92500024004000540c80c0c45080030000034421840b500840120f0706140c0081c0c21103100903106c80024120310340180d08074403140704d1b100e840c0034106204d0010184c0172004550109407607103009802d0b940b10a004a50341c0e07210040070108900b0382c8040000700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 820629847 1250 820628597 820628623
    0xc1b0f0106090b011e0f050d2007020a12020a090506011b033b040c0203130e150105090f09092b020f0d120507091d07080a0b0105031308040e011403070f03150f0e 71
    0x103034ac1c1f41c429204105565849501400e0100c040c0000200941d0701c0075240001c4400130507001c038580c0d44600048401c940b018480420b8a5000c004040c00c1c10761100010242e8450141240d80400c40b131070420880201400e84c0c0f04d041c06507104001610709280d048030080c8141c0f801200d041200061624003150000e40201c044041c0102c10407110000000b1044d04e4074800b03003032091a164060000c03403044000409001d00440710f030004140e6018040150000a04031800417410b1a603504040c60842040603050f000103108084280b00c0804000c108490b1400700740e192020762825a10404c400f81a0044c500f0052002601c40000c1041d000160741d030403811074460000b000d180144020700765100141c815030a192500c803d200b1541d82000172a174015074004000c190800183ca070030301d214030880e000418030f00100b8000090404078040150440002182902c040c19250b40700c000c50200b0621020f0503466507203040740154074880e4054801410000c0c400700c0c201d120f4021845c07614003085182 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 820631097 1250 820629847 820629911
    0x30301090c02100e10050612010e01051501080906040b090106090c0513060e011b02040207080c0f010e0c100e01090504020a05120105090c1b0f0106090b011e0f050d 72
    0x1030994150b05104200861100350801c000c9443d122114a82c2d44072034803488025035030b0340c02c0469000d94818a60100b171180c107800034081c002800c0d4580380030f0a002d4600501d407aa000c0c80c81d000d81d60090038110700c00d80016004191039030740c0d80c5070f00b07004101c00381481585550fa00000b160110301401500052810b6890f034541d41c01e41401001c500580716804002049240708001c2c5d1300d07a80c4503400fa0140100303030004a80400e014000900284035040c00144180d10025010340030f240c1c0400c01c03d0b2480a01c0d802001a03001965076151110f55041c10140e00828082c80c0c540c5150082542c0110010180b4240301d1154541021400f2070303019003004000b2440104d08810450806042e00d130140c00d042d1028a25420300c0d078600c0c00700b40544611801054680c003c0440b17820010842842242080070003404042e0b600d0082c070f8002d000125140d170001d5101010285c960741903101800d2506025581c0c054a00c804100c200e610740c001c2458800346c1500c0c0d54503440030810034010003250354004282 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 820632347 1250 820631097 820631111
    0xe09010b07120306140111010b0301050f09160e060d030309020907080a200922060306050103060b041b110304030c0e061c03020303040b1909050105070f09050d170c03030109 76
    0x101449402c51165001d04140c1070490a0100c2c042110f0440c0c40b02c4003e08280400c0c01022801c41d002d0043c400c040390f0150b1030001003009628421100e14014071040d010b86001c0f040e80b49584200140c1405800e400d01200004151641040e9100104043c0203203000202e00c0061f0b40080c40f81c46c0d0650700c0200044003c001d00114503014420384040020140c48046146040070300c151040c002ca4405070311450f41c00860441c03202c20710344100e009401c0100100700168880c40c14030700505080c0426502079141c204100558141846101e180401d5040d4195501c03043c100121030783c2c080d034180300003d0f0005001c00000036041d131140c400640481a11a25946004410704c0307510000042e00f541192003034045040801e80210071a034000350456030840d00340d991920000301e20402141c4d0075126501d404d19000030700c0b2041d8000c03030146c5c0d425503a5241001d00c01900706d4020410740120350341b15800c40740a200184400c0c012184c409900c410890a02e001030780b100b411504240d006140b81511010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 820633597 1250 820632347 820632353
    0x3080f09031c181d0406020c03040909050105100e13150c0c0b062d01021e060411060c0c01031806060807030302060c191b080a0e0109080109030c02100e09010b07 71
    0x7684000b2071425503803403803d14503121030201d030354120328181842003070014041414040b403601151025061181120f0b0390326a581c041c0c070700400c1c2e1280144d401d035180c40003048000561925200c102c51900c0b0284074540c80d0505800d005c961104011103015444101a211801e2240504202d10300c0740d45504400086030f0a029000800007003803035101d10281e404050784801c07010500c06441d08960608001500b500c00140e00c4e007a60394150440440e011001680490f8001840d10b00c907620490303845e07410885880c140501c900901c5004481e6801c00513180019511952001c688624071200c04003880c5071a488950032580b05401c84403c0ba0469503091090540411500350072072803800d84a031800145030980c0744548000f03e005810800002a401900d00c59960809001e40e0426100f40e610442c4c4500070703020910380288103003c66000ca0000a11503418840c012030740b5003540f503144908140707608000c4240c2503001c0f0f2109100301d014800947c2d407038004259020309600303816907945d001941 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 820634847 1250 820633597 820633607
    0x60a112406040603020d033c02010e0d051803010605131b0e09070e0d05100b030d14181f0806120606030c10051e0304140a03020703080f09031c 63
    0x1450300d40641d04280007040181c4886d005410080e0301458009031110200d041c023100d440100b40503508040d103c4900702100c0d00d100311041d0b030600c403c0d0000c0001c42c1900c001d40391078025400c43e00300451001e0000281490b04000030800401000f000080e0301901c0b240000d803100103212000c0921a0303106000740c14002c0c034032804034451443c0c1c149111034860040011b11701c00c41c0200643d08000c00540c00b5401340e10360800754815640c0c0311068801850032514008000e051008a50b40302e445a0580c0b0701c45503005d00d0302c2410600840e540c50340303004401106480c04891030032401d504030411145002e11458040004503076114142c6d259071440c185030302000785070380014804c1202c1d504040d09204003664005004855614213403480b104a684229080d1494040e1004084e0001c10040d90320f031481c4848801148101d01c20150740980b00c200100007596208074001c000c0160340a0b410600c04075280502416801d1995a5001d1800c1c0c20302e400f090601e040c0c040c4047d403100c2c52141041e0016044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 820636097 1250 820634847 820634851
    0x4090605190b0d090f06050708040605070507050604111f030203061306081b0415060e100302030106050d020d02070c090911090702250510050406090b03070806060a1124 74
    0x1140315940d00e5424207411507018401d00080d8015a41d45001c07a0007041417100c03c0c0700400c1e4102c1410001d5203006100600540d60840f02140e94616100c0020b032828012030503039603110b41150003481c5560726a034641290721104030380c580d07000c405405400d80e1409290301203612082543d13009600c0341025001c0c8840300209021000ca040d052240c00d1214920000700d4428024044421010071100f40b004035000342500603c4075801d44120380c0118000e50010380d01814004140c070104200710801c0c404804901007070096400041c000c000c0b140117000e941e0083c00184c0f410174001071910101c0ea860041c054400d600002d07016803981101c05c14482415034000d041081030b201221145811503000792540c02080700d14201200c0c0b030001035402191070464501a06018107800c01050084c803004d000754115129040000f800c840c804a002450350003546e0180301c054a4051203520f82104102090300255050b4007041101e010300d24482404200c40c00d0085440b44803079011141c86040d1107421140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 820637347 1250 820636097 820636129
    0x70b04060305091b221a03060108030a0c0210120501060801050f040603020f190f0602071e06170403121505040e0102090a0302061312050610170604020402031b04090605 74
    0x913150460059001c0c00908a054108903401141921425515140c03480003a8803000220300e4000035991444070300e61600303c801c8040301101c40607a80e4250199403407064151001c000f9270700203c0c4100604041c120900000e0050901e403440c009595180b4081302c2c4c00340d002c003001540e500c00400681c10f04844d1465000400c0d80c040c00280d0840d004a0400c841004130180610300505021030180d050648040203070142c403500c0b2204c01d5888500954442e80313805003490020103421812031031a5006130460444034143c0700c192600300078022244001600030000d9003849404030107101d14034000cac411402e03108000490501420700b03150a100845400f491021403d1384104001c0030507964500b00c1b48122641141c0c950b0341da2141c4c0d480081a4685607112a00803603080b526001084404107629200340307050004549556035404020a40980c2e0400784542e07900070001140140c245a00119400f1805a20b03050400030807405920142c2d2040e4802056a951510140b00d285042c2d06d1403111315003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 820638597 1250 820637347 820637353
    0x605030a0f14031b010204140d050624090f04030f03060b030f04020604080a0305091c02062a2b02030a120903090302060403111f120203040203010608070b0406030509 73
    0x40d00d9544400035041c0000280c410b5075441082038079034400300101c0c1c45228400703050501900603d16034901035005805141c40b140c940313048454480c106840c1c04212160460001e1080380c0340c41620f854540d008030400c62048050389403c10300b0b521a44911030140e80c43c58941c81c0d6a2600341801040e18011040550070582004070070001f2101020549030091501e2034582034903107803072000603401d2045078070800041c05400810300030b258004001e072050890907039800e02e18032100c140c40c5105d0f200d0f441000354400300503c0805c0040c400700844a07c05202e52801100100510301c003185000c0030f000c3c2e000e0420116180c0c0480500c030500d0b91340400f005e640000c505090b810480500a007500d540c005a0071662060440b00380361142074031100558025043c0b03036580340c0f20300f000c0381164a010001350242c1142c00030500550550441d207407170302d115030340c59114050419200001943c4040c00c160791541d21120017042c65502404510020240c61526039515850710f2409001e40d10002c143c26102d030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 820639847 1250 820638597 820638613
    0x1060603150509060a0306050c18040b1e0114040f0302040f0209030c10090e070302030901200414031513020a090b0307121a0403090501021203190203092e060503 71
    0x141d0000640e1080d10811140d4104903900c100100f2840c400c142d1001d06424102000e00600d40b0300a00145002d24000c0307014042c11140750700b0310080d02d0700700b09015000310590281101c4200740c44219800b000c4149032080c69120b94610b071800381e4010f41c0001040c0e6410f0401081180360600c92410742048850040d030510346802c001070345401d08511002d001b00300c0c20128169091065079000050543c030030300600642012a001402504112101c09203503290500010700c19a004500c810324980c100040c80c581030811170504100c506d070035a2150140310310f500c18219024085e030094480c01c0c01c0c1c80964401a00c0e4010028204056849421242d1800c00b828481d501d0114940d0300307071003d080c02000c080b000382ca0710115070780480c1f25944001c20b001060000b015030290019080380d0b0f0036403c888515100c0e121035200c078031003512a543c81c1010a0641d4100102d00d4015640c000001d906490614100d004500c00c595454240c02e41e4000e85040403540454161081802510080e00101313440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 820641097 1250 820639847 820639871
    0x1230a170d17070819020316271701020c010f0b09060d11040c0c050109030f0311390a0b040b010e270715030603050d0e0d060203041703011701060603 66
    0x4000c050821010001203e00007443c69009400e2204e1805d0005070071540c900c0c000d09078601d00d54045a090000031540c45a00000d1041741316403a080f404200ca04080241ca0403541c00e4500e00c9008100000303540920004054a50030301c10044d0b1100890700120340c444905040100b02c00d4010002d61081031125000804110b02080c40d034121030007030320005005484004241d802200300e200080166003442075610805a0007440b9a08150050720140719100410a0422042c010381c0f0b0034041d42658501030001e04894810414108c0540360389802040b80094180d030f00f0004103036030a90341c0c9964001408100000030504c1030050580052401050410400358400c2d80307400c0c088140c2c10040d40c103282d00c3c140824800d0740010719070030240e00c020b803c0a98000c2d02501c2180b006a85900995000d091018084c01e111000f900e0700030005489082c1c0c07031b138a0758000c1d0005003095465107400320011400200c018010350180244c540c640d000c010164901c039003034078401e4011404141c1499014648 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 820642347 1250 820641097 820641137
    0x705030703053f09190501020a0305161a100f060f0c051023090607080105190b0f040801050703060315110f030406020a020f0705060301230a170d 64
    0x1c42100d040107010f049401c060f80d4103650685445a1089807088950034041c10604008100110081c3c5003c030302800d01100011071045103224050158200b41e840c90f002a10450090506008400d08030303110900300d4a030f003212000b5141038900c0d44809207040c0722000340b5280c8044018403440419680080c2810030040c070100300c034004102030100182800c010880c09100aa40488406004000c001003405913107041c40c0b0301c02ca4651006c2d00b41d9000c18841b40b4041141c80c46102e46032165644e691070301c2e00b0b11902d607a00c001415402072440f000420008500001440705c0545681107a4480303040c0500142126000f6040d01e0038103103003110800005403d0584580110741c85030f1300040a042826400340c5500c941c00c0c11410380c017800010002001340c3c0e41e001d0541000b8a900315084a44005005a9079420343e010301607101c0024001005825903a2146440d6561a03c1c912404907001d4008100d201da466000680410040c1d0074400004104103c0e4030250b0a1600d8180d14800460f004400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 820643597 1250 820642347 820642363
    0x903050901080c072415240207080604050a121d120a05010204030b010807150e1306120b1b04060509060901440f0f0411040207060e070503070305 64
    0xc140402e40001900b440040c00940d25529000304954806404040c2280c000d50182d400c0c202000c4e25088540440f5400d640e0618141c8a0100726a0396191a1000f00c0100c031410704100e00852040c0745000c03076244414414640035510482c003c219481842c9016141c0007007041c0d03020304020212000203400346401c041e2488964007540c1006c07280ca0300344105818880c072004094080c1d80009000010848801c552504039840380302502d103065105c08154070340c04a910b000400007000c0f0000c5100502c0d01030100d143c1c1c02a0f130f61000074078569480100b0b041402c4a07805070b50f2030809904000141d445452800484071004a03030300e15044c2030400c0a4a240602c500080c010600030174040800d0740509049260b460070030300114684007001c000e214080c0c651044a15074219410085140d1100d8640d080b0300a4400203002c81069492740c400b0747c800140100180c0341014000380301d550544492000300201c901a92011800954610400745000041d9000d140207511018040000c42c001250f074103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 820644847 1250 820643597 820643599
    0x21e15040e0a02032415040807080c04290607020d03050d0f051006051e0304140c0a0315020c011b0c06050f0f18030f0a0509030c0d0b01060c0f0c062109030509 70
    0x1e80d8040e003500850200d1400c846c400705030781000200800d100f000050f405048074004401c440c0b0703081105003400255072041503036104100665841074034030401140d61013000030000d410103061050075000104503e2550409034040b03200003690140c1d10b45a80a101407030a43c6180078065801c00001c40d1030700103528800c040070080003141c642810b084003540f5942d00a49030b0442516814503040400450300c507951946042d2080d241c1d203800e1424072261800c201c0703401000b011100c1d11840107440c080d50102c1c6081505544c4d03040700d10080450002075102c04221965040b40c58207152400c10208c410203080340c02504400010042e803408100d81407688440550040906040001001481c1d40554a220354a5400104000e1012030780407000c1c0600000031400c942c00061100c0601c1003040c100400902050114001400070341e0081c8424000c203803149808205070003032900c0e40780c1040d003a608000001000d2848007620304c0c0c8040344107801d000c91007a040040d202c10360350152092081c03107001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 820646097 1250 820644847 820644901
    0x20c040f091a2a04030b01060f120c08061026060a060512040219030f050607030501140307051203070204060902070b01172527050a02040f03021e15040e0a0203 70
    0x22a030b07114a860141d800656001501b07030b506584590028120340c200d901c0c2c3d0000141f00e118110561074890055039118000c98945081d00e84079a0240700c4c81200c200740300024015985070300240000c54400e02c5546415030b0081c1092801e0072810802c00011561080c003c001c0140151880c6401c04100c0d40c0e0050340c100c1e4141d11110b86c40c0403041110f01964006803203128406800414040c0101d0710510805966808001503030321511820902101101c2c800d40540c8080e0b024440790401e0045514820300341d0301186d080038030583c002000d135044e50300f15403003194001c19201c04001a030000c02e805080f45042c030741080000c028120b6507a04150308a00441614050701c007000d460340080740c1c400340040f03131000c00040c031100c4004804a0011300324121840d2401c000648070070030a10a440c15141104045500301e45140c081001d12500c0707150418801526005043c01941c503082042d0781c902001d02100d44692070a080c09800120080412844070300410411031034211410740c01903440c2100d404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 820647347 1250 820646097 820646161
    0xd02030c060f100510030905060709080c0121090302030429180414070201150f0602250801020a020f01060506030f04060c0e032e1b050a020c040f091a 66
    0x203480003e94860f03002c1d0341c04c0541c224070f0341d861030352640011061030700440c00ca5083d40c036100b20031a0321042c0d41c400c0d200c0680040100b600a90b104410035a840362400184841c01690000c1c00342c03c68a00030002c401590000130708218403100030910310694100b100e848540b0030041524001c4506c5a070080100b000304c2c00c21066003903507655210031030402ca900240f100300c1c60f10301400790080106145810744c6003020100003c126441920080c203940700d550180844074034082001d030001a014802264100081d83d01252a100c244043c292202c1164000c1200d1b00c47ca016603403c40b016900064081c1070200104042d000701c5a482030340256211500040912110408590448010030000c0d072600030411000f60042c862823420a1660300c0210045200c02280b003c902100d200d50201107030b03580d5400044030014003407005800c040d12680107039180c40400d040003030f0450720152041041650b4a940d074400303020220f17965500c1c58101200d06041e0741804d04207003041440146491802602da281 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 820648597 1250 820647347 820647361
    0x90303060306270106060509130507020d0c0609052508030c0a0b04051f051005030a02100e01140406090f060c24020d02031009050f01061403280606020d02030c060f 72
    0x1443c608110300c50003040025200d141c000c0450b030200351520310401400d80440500d100310b10a02e80109035a4004080218030944282c0d007003014100107442003a44d45070700c0c401142c000c2c80700014403078040700400806131a004008140030f00d5078000c0300c0c045d4010300c80100130400000355846004d402c00c0314a00c45550b1403502a290441040404030f8144c40c00001010103000c03078021501810441d660644000d840e00107240e0b485541a801a5202a1910076072003a680140c226040720703101894480004404480104026805540048006001030200b0456540a1468a40a00300c60f02d4010a05e10280d121714110541651081c034180340500050040c80d03102c0d50440d17800d0009018159180d00d000100f0f195402d0030340c420844d03020f041800040300603240c42144c0d0305880442d1030b030643d1103005450101082c2c00007002e104c800c0c0311640001c0e89a171700071014000801c50341c00c40440c1e901d051010081c1002c52159440e01550b10602c20032000141c00301d0003c0d840030f100702000e8075a83d0f82c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 820649847 1250 820648597 820648651
    0xd0c0f0606090903020a030806010c0c030209060607080f0301090606050a050a03050a020c010e03070c062606061c05070f09060909090602211f0e0105010804020328020306090303060306 81
    0x207800203030040c3c94140594109900400c1d0102c00c18000d4072140842d90311a0700640c0c0d0b40000f408024841e420300720080c4010300d00315083d603801ca04040c00d07143c2044000c3c0c5d211041030b40582620780301000701100400c0f050407140a85000b8000394030342035050410000300a4000d0240c01980002c0c0b649400c006240c100e141d50540360900e80c048020700c001d07052a0510307600d0758449001a00e243e940741c10003151036070144c40030020b07880040303d90070481c400d5464070224441010348480e510180400124868480300741c0c0c000c040080c01e920008050030508009400c50a4403008030052110151041101e00d80091200c812510516404584003034945030410003407094041c03840c0460301c000039030203048002a82c454401c0320740908020172006801021814030001d44103079541c411103880180007030b521500b100d5402a102500310307200388400701c10504480c042c44656103c030111551052055150420074103410124010244d455418a100400d4883d0710080120f1143d007104c000d18040c4410203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 820651097 1250 820649847 820649849
    0x14070b04060507061d070f0623040312020703060f0203010602010515030d110703080408031c0b0a09180f0302010e0c01090e1501050c15040c050603241519110d0c0f0606 74
    0x54040e10250f50b1034403203650b40c0e03107c140200c1d000645000d14100014040c00c8a03060300d01b02101906060528595650382c1540c0b10100520450141725000000143c4900601e0b030700072440e0601685942c140180203007140e40003040d0010003404403002c071645880100e90f107020720705280341c43c8002620b01c2c0c1d00207203418800e50009001d200e0018000440c90b07404070280c0300c43c5109210040e505206035580e1000e503603000d8119940000d07590802c21219000b540084058400000c01000460080d150215914200681600541d4680c03044418140d01030200e070002d00c20900b402400c039810050170345111031005200e00d040071013101c840d81d69603018005846158207240e01720781010101416110340a10281c408684135542c013680402c03185048000d0380d200d605d40b000c0c000024010a5440410021002600c0390068100900360007003204060003880c0100030001480c1820450020050850301e6020720803510780c00142e00050303882d600c0400c6801064019140800645084c20580028205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 820652347 1250 820651097 820651151
    0x209070e0d060203010303090816090c0c081803070f0b1b0a14010b150a270504150e0114060f0903072301031d2e0914070b0406050706 59
    0x621840e5004016283e0001c1d41601d00c40c1d0b544c503203c1c0d552911583d0341c40c904500809120040340d80c06114040080e849001c0721441c624020441400d01d8442080c41c4d80b20300340c001e1000d14515105000740c00d040242800424501e01200001407500c01000e565010f140307800304110074019090035401e002001000c1070944c01251140741c801c2669400380c000c0c003881c02e01a0084038401e001c9442c1d03803406410b85100c0710700794543c4220200c2000031200503189800c45a0400b008040000c500390b2140d02c00c5698403443c0c03600d40d002d82428050030401c4050144d100000c101c0320402e00300c0b82c41d1505016184800b13030441502d5110400100040d080c16440c2d046007914407285a9405405205c180000200031400e80f0108003000e0081c1006901c0c1841900c42c851940c0b02c0200c62810042c001c4998060041c9a991102d030440d05400108c20b84802803025a11001d40304114022042c052240c2001451070b078040a207060f25143d8098824040c01101070070751a135500003a85044054500c08494160f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 820653597 1250 820652347 820652359
    0x70e0d030c020d17040e070201090b070c0201090801050c091e03030423031009140105160c050106031a07170f0f0c090d061509090f170d0e010f0b03010506010c0209070e 74
    0xc06504138106a4120303124075000112690081080300d03006101b22010180c010072074820590700e00d44181c80e1440d050000301c0c100412a200000c91030000c0c0304560040c2074003480d40f0760350003613070040203e1802540390300e60301495000b40e0941039a40c000202ca04882080301c2c05080c42070050350100200788001034a030307014050b000001140540551003203020a10600d4040380c00c202c0318554034201c1d001140c0204204502d4000004041c0c09040c60170701c42c0e0322400010880580300da490011280a408941c0503907400c107003e1190064021070f10000c0e4420b40300180c140351410091920003410080c1000010042600105114144020489041d510003900c030703c0300c8011500d0b00c68010302040c840c20010f407022050120310013109000c6c58800035080404068405016121003c1c40c202d01926100104030421141c81d1011090013000340401c0420300000b00e1036030029801059403418000f080c8240d15213020440d586c0c0e08104980241901079032140c0d165031703407048150b0340c0d10600d017a0b05910031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 820654847 1250 820653597 820653623
    0xa151110020406170f0708090102160b090606060703090509100302030a0c061209030c0602160f03051e0a200f030714160b030406020a0314071106070e0d030c020d 71
    0xc60250018001c030390840d503511030322855480320304d1101c0900350b070300209298404c004514001d21511840c1d07001000140018649100300d859244101d41141048410344444001c11410f448217110740b40d80a5401da1f015880c0411b50341d030007095103100f0b000380c2e0300c58518100840c100200e500c5610000e180c0c06822503841c403080d402c060341001224443d11000981d21010a03074909902e00034400400d0717160329907490b0440c4130b55442010b0341103003812248400700200741e680840c01005804407a180a40c1380c0343e90340c0d4000034680180700ca94113960701d2034070410403180e401203034040c00e014020f05090501c4810041c100c11614240b59408012242031310000c00d040342840003540d41060b403080b1000031180544800c800c400002862441484190720040c070002c0d0115580380c00600c5180524540050700c4583c9800d005c00058065807840300103448640e4880f078541e001c200c001c0c0c000750f076030500c40700841c035010004054004030700c0010b04101e40265400110340b180402d904ca40344c0c1c015000aa10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 820656097 1250 820654847 820654873
    0x90109080d111c1b0f020a0b0a0207120507050d0c0f020f01020709060902041e1203050c0114070c0506090c060316030b04020f190f0e040b010e130204051801050a1511 73
    0x2d001c2e42c4c003401c000c5a84450503156028003070401615048032a070050f01d414101d5803a1705100d404000c0622099540170010600010741040591030304c1c50b0143c94954680200781001c074540a210642001840300b66503502c0d02143c0707032003122410180c4c102e5044909014100040381055070b20b43c804441c0074103040740482c00f00940d4000d002545c0d484100304540d921300300080c40805a0318401c802d01409200f0405021910850042800314503020010a03a401007010052482c1d208036041030005d001100c040c2c04211080c0a4250810303694001010540030480025040e440040d103800822107000800307421141c0241c2006040f0a4020021510364000100c480f020354402c0c0c2204921001d01d0302ca44c0f10742c070b0140040d00b50841c03060361140000040c2809020040c07012820450601614011502c1259210303052010700e4000a1400760700c80f0710304801d1212601703556102e0703850f00750a08018402a254403010004840000840380b4015201d04010f8030f150400310003c60560050a20311b03409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 820657347 1250 820656097 820656101
    0xf1401060f08161d04261b030a0e06090112090b04051608060a0f110d09020f060c0606131b0f090b091804030203040f1409090109080d111c 61
    0x40750750030010f071075001d610990f20391a0000c55000d1000f0940c03140f0340b90149030502c000b42c41d034003620540b44421803103c850202c1810901c414040003503c50005900b244810030380090820010244c0c00660401460710030140444120081d06170242c2c00200b1040c00c560f124a594a6a40f41c00820401089081d0700b48001d581d2004c03182580d407442421344c110a82028540000121000c2e10003a00d15911a070201501400f101940b02c0d00d55511002c410016405040040c10400c400306000a05081070788144004804c0c1d440ca164170603003060066003203205000c1041980322404a6640b000404a4103801008090f160140000b5989564a0070102c0e9001402540c10190640764049420f585441d0340d8003510500d8400c0c0d401907542c403110440a10013042d04c0d90028800e0043d242010385801c80104081d4050788442102805400842c03814100001c0641e04049294028480c003000f548a8468030f00c03a25184010a665071003c038801001e044060390b0804250304c21303041c0030114400003240 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 820658597 1250 820657347 820657349
    0x14041d0405150f0408090103020d06060e030f011a06030907030503070f0b06093c090102090405090a2a051008070e030f0714060d0609140a0e0304030f1401060f 70
    0x1809201d9012042100160b950301144902030440c120110f84c0d039142d44075a0300750000d1160605140d000e01179181e054070507005032005841070b540d4505040b501c840c201031618212a19200e0941d02d0181c03900d0f001e00c80402e0101e0100c0d826a106556525110240c0d480c0804030391001d001400081600300801032010203030f04030715001e2100254581c545804110b41c8400c19034400700401e90080b01b614000c0700030f883d42000740c0704007200807500c1015152034584090048503a001e8907540083eaa0903945000c1c031034a0341255a0710010b00303400c0030640d600e441034500e5103015010041120b2080f03007045c14055010025040181079224899580301c1c02400810050720f0b0301d8042003404680e10078a08000411501505005000b4880c0130301d03100710035000e40764508040e41c02c000c0411101540c8035440c05550003e0030300400015a00c1083c1100d411205009440004942d05000390403501c42000015202580d408c44454407480e012450985c644502140340030480d9400d050300001ca030464040404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 820659847 1250 820658597 820658603
    0x80a0903140c0607080117030306100c0516091a0a060e12010c0305040b06010507151802060f0703030e0f10020a0c0f05010c0323150a0e040c0510051914041d04 70
    0x559147d0b291821428142c01c02d40c0d02128580c411310005140d80340010801030658054244030081300c0058513805e0521000d20740c1c440350404102810000b200140c41010340f4121580700c900c624100b25000207038250b9151044400300402c00c42c0c410f450307a4400344000d0b1003542c0d11008018070245928080c01030034003150b0980300c0c10300103400101d06500600490305070342d5009103003458500c6000c2c0317403000a0044400c07882c450a40f90286078010f072160301c02080c8000d004400c2e1611081c0911340101622842c0080c3c03c1c03103403c0404540c0c030341c0c0030020700d11a0702030f584d810160701c8400c7d00c1400c981a10403081e01910b1000e140e084142400303819480f1107003944042e6020f0001304003225244062007190010400400d50543c00070b51440808a030300e0034156030007040c0d51020341c1c2c2e8080c1040103040c243ca05485298081208001c00e01d4030750101001e0340054123209041141045070380c09440c0d440c076068420300800700401c2d0400c60060742150040e1583c95030000001c000080b4080740260225412 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 820661097 1250 820659847 820659857
    0x60e0f0412031a01030e0304050d0605061e01080c07050c04020307030e01050739082809120b1003020604060c1a0c0a05070f05150402091303080a0903140c0607 70
    0xc1c0c00c0661090041400c040220410310b03800880d5800110010000c4040101d8507000901012810744e03903101c070a00541d13008081c042003030704100041000c141920001c00c01040c6500a0681203a6008011160701000e110006c07a00c2e0625401c20750b0814940103c0d03554001d00c0041005200341e0140d03c071400c001d0240c0001c000940d01c029040c1c582c20b160340350030000403580708001c800c1d90f036228140703400000e421100c8449602e4243d0b951101c60308035513074030b8029030318131800300c0f4010000b0101d1031203440907407500c85451480c03c60a524100c0b002d1001902001d10103002828812940003808011613001d04419070b1981e682000070540c149148084465503d10198507030f0261a03041d0960141090840700c601c4d00340480c406a545900559084410f0383e810a41840410010b0103502c500c442c8003006a40d492400e4410020802402440d207400043e4101c00100465809990198040524000020404210304040d194004019100c3c00180c07400100003d0203000880e0150040b2096115 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 820662347 1250 820661097 820661123
    0xf0e07031b0207120206040902040311180712090f050a030f02010b0d0c090905120c030d1103070e09130b0411031c0509131d0604050c010302090306011701060e0f04 72
    0x501103102407280304030740140d02a80b001d000045100d1030000b02d592009090614099803500713a5800c0c1d800940c8103452008000c0443e40079801c00c0c601090800b05481c119002a1500100191103000e003c41114102a61041c40700200074080700c9924199801008645020346985801402d8a02d02070b4100015401c10007400c0d154140690380164071a0302c0459465854204401d101c0240f61001d019142e0344560055069102d0f0220028411100400b002e140d0f5006288080810b81e0016805074007410010801c00030180c0d40b040c82d4510000d0100d40e4240c2c5600d803640c030f04040c44008034002d170010714500d040c48200454034004c1c402c00402a415108414500030180284450046804012030410090200c0c2c2d490040344a91a01c403d03100005003403644080c5c007010154400f01c04c00c0e4190f105000b80414440100074143c45041e0910303081d4600361600c80403c0c1c5501c0c0c18440da05606581990642c015403081d004000030b0248545404010b00e0540b8001900a9040c0c03015155076a81d024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 820663597 1250 820662347 820662371
    0x230d11040617030906031b16020126040609020112020d0623011e1407080c0106050901234005100e06041424040b01090506030a060f0e0703 61
    0x100302e2200b100020301030340c1801500400e000381c903032004000b80b074140c0c0a109840041034041000d005203004811000c410700c0c0d07140c0700141c04c80560605100c4071510044041c08040d00404c017a581c815407005010481014903c01641c0c44095552412021800030600b41c40c0000294400c3d01140e000594030014a09849024000c81005002450004c0c1a80d503441816020440149420380c071145800801c03542c910720410219000004111105240002c50f0340036101c090052101405085642c0e00007940f40140100d2152041846080b03441c29006016020741d440c40003090346402d039151030800d001200d40400c14610b4400000b855a8040c450200711042400d02c1a5441a2403c40742c1e454014100b03e164094404004c202541c8140c82d0b6800141d040f200303143d428040c40c0116600c10b46054610b01061101c40c240100c6802549410441c0c2c0d180d0383e1050b0010100c030030035509107689494109506020340b090b6040f14082c080326a0700050821100b00202c1d2090410341d80410070011000e03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 820664847 1250 820663597 820663619
    0xc040605030604022103030a14160e12030d09060204031205070209010504240603020417010e0601060e0a03240c0c030c1b1809050111030709230d110406 67
    0x102a0319007540c01100040c005050207990b020081d44c41d11300301c04428400c01301d40707461b5500848001000c99207414445036007100347c0c14866007180700da84105c1403000d01000c000f0041c0610100c428400c0050b40c0088689150910441e44020500c15003480710f00c00a08065004c1c1d809031004030741c0582e01035952a5400d01c51411354401d0380c1c3c0144090f406910300f0301004003418409041c1300c400313040c8907482d038807020344040020014030240c1c0f000350701c4030302d00800108649501c000301502e690414140103e84400805e229040d036802e802c20390100c541c580d000c1080d89a47d900b000304a004a080b46000b5200032003540c8007001c00300310b0184088143d100084440c210104070042c0401c4000d04103400040d41c0c0741c81d01c4810200400c014010540c3ca01d50742402c0e8401c100a0358a0a07604c40407403007440070a0140301c2c1c850700880706442c95810191002070800c04548030780e51902c0702959040b007000c8502c8100c40c0d070050f4002c2c603201d44c07250a803c107c0400301503a00664401c510341040041d07210901 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 820666097 1250 820664847 820664849
    0xc0c30070305040902130506130602120f191b0606080721020f010e03070303091d0c030705160602040b030601031b02030a14040e0705030703110f0a1805040203180c0406 74
    0x140e901c042c20300713160040810181d007204c40351413002901040085031945684024000b800c0302c0442003080c2910f003102c0030b428052444035000c107030701302048540300303035081c0d9411a40020f0410501c1140d02c03d000b50700301c890001141503040709040c81c1c0307444010b22080d9001441070303640ca4025070f21b98566583c01104441301d070071100c0d558481c1e51b003c14000f514101032001c80c101030604003202070704555000641010f60030b400440c00710b58015410700140d821a5028160915005a040c40c50304200c01c1110080c00020503100400c50001810305c40b208841310b0180c00f480d0301003000c2d501c458130344120000c02e80040b110940000d14004400e8151217404c01c80c0940c0d442c0d25005103217040c42101007141d090660080c01594000200b1001418185449a0a105038203941e40c0d15100e0514803401811780702d22091060303c2034818440501c2c0c01e500300c000c1740d54001050600c400c4160016000b2a90400c10794483c0e07900c14804804c129040b071510302c1b1200d04e4000c0ea0141c81c015295a02004110344107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 820667347 1250 820666097 820666103
    0xd081e071401150f0e090a080408150108060402010e1e0409150f0b09060420030a05010312051201050d050a05010e0609161d1902040801021b06070c0b0c0c3007 70
    0x10110080010784017070841207800c00130400a542030f1a005d51280116944541e0110a41d0750100d01001c00c04041c0003042c42c0074240b820007401c024149600001d0200d0b00c0e0018007440b4800100412a0030b02d205203010b0705203c8054403d00140c09203040094032000e071400b2003c291030415000300310042c1103200c7c00e40d21100040040e09140c5070441840000c058564203032202c003591910003040344034100059803260340100c0001c10a581545400c0e6640600842c209061200610503002022002c10b9583d054907020307582c0100c56425070070b005260840c1c0074000f41055280224546001c000890300d00e100c0c00d803060840e030109a5410416070406403d1250344043d405062229800d404440816a0085590380c40081d4400002d08030780100e0388580e01054042c0e50000c0e00700300c00d20400c1f418040020350354014006511b0074460180580c0481c20b4001c02009252000540d40d011510a541c90800da202c00c480d0081108000c1c1c5003509881003030b44414219141c183d0620440701c1d030440b00b038a64 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 820668597 1250 820667347 820667369
    0x7030b040f03110f0709051b13052403010b0f07080705151e0c0703020a020a0810141504050406062616080d1803151d0106050d081e07140115 62
    0x45080c40f40001030101074801000d5040b500344862341c014119029145119102c2102c0703101c0e1740341900b000102d810f160080907060450010400001f4a8001507a04503007580961554580b420854404103110340d0344d008042801c0400c1101c14400b001501d010403040040b0390100c00c0d1a82d183c1c0000340000c00704009001a80c0c44001140c5850300d001906507a440781c01150703031198580e8001140901c19402602c110b900464801c8000e03442030141030702140314a071080d459420101c050040e103230400c0286900803900e03240480c04101140e40217000a103140d901010010742e070103449444c211b000c030204000e94800c288110780309060809105080310700c1d80c0001c20400342e807044103560b44180c80030b0300310030756111460000c007040d00072000d071041071442d01c80010750f000b008901101c28020800e030402c1680c5440f030103021b151503070002d21451f20781041c01d154940d9400c811302040040b42d010500d00c000404500d00381003000c104100b622094900000b80f0004c403010014a005006511503294046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 820669847 1250 820668597 820668599
    0x50316060c08131d011d040605040311060c0406021501080d14120f0412021b01110a020d06090209090c060a03110c0f07060906090e1807030b040f03110f07 68
    0xa07009412604600d071041c0402070500d0b00814902c600c3c980d03542e100b0010081010070f0f41402c80b030305101c21400341010140b0603c9001d4051280880728100070801802680e4030700102c0d0605000307141118603680084210b925600c0c2551b8000300e603070001c3c0308101c09803048404181000d402942d40c207060f2a925801000541009481115121003141c6145001741081005100e4854501c440034031842421541107079600300f902d40145010403421190085410140401011035108007080c0c5a242c030900c0d103090600003030038045082681c0418000c0d03124842c0d2042908200305c43c3c201800850003260700e803585580c1c000c107194841080c40c1107258070807400c1001005c201d010350321110080040e40d0a05041c1108180c1c1ca0349400820450001075078001c80301003268680c0300e04010007602c280d1805010443c40c2c00c40c5900b0866024140030780c008039a14114222440800c81e0030011074001401d0101420135082402100c0400c134000d800180446500c00b865860020f000d094110500c0000c2c0011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 820671097 1250 820669847 820669859
    0xb07021507060903021b180c0c0118050d080c0415080a06090e06040c0902090a05060d090c091401170c010f3501300203030403080c0307030306050316 66
    0x122404452042210001d00490012411910455802038801d07001488074045090381001c000c215071350788901c02c00381035003881218280080130b85c1c0c11203a500090b544a03c1c0d09405030303001d800a44009003602c180704081c0300900000040038401c103849500d60b0103041d140d0765032900e4184914028180c2c0944100c202806141c8100f111075072240750404009000e588030640023054a0010030014140c5e03101605000c24000c034001041e00915000d501149855802c80105002414a22840f44980c5000c1088000c2c440d8035000700007456030001400d29602d4a0f00300a0000303020602892940340d41000010821030346007844184400d0103540100010804c2000460341614841c0d0001b04000325072045400e4140103050b07154100a05000001020494030890960018160703c40c0a85a00301c0360345d000281d10030324090358440a81c440030240780fa001e00101346548107560000b010754500082c8070f440c0c0d11005c005001403e100b13580a0101c5a515000c15690301c0f82d54080440030042a4402c00c0700c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 820672347 1250 820671097 820671109
    0x6080c07080403020a0803120f1e0a24080706170424060801020703020c09012d0e07050918193207080903030405030a0f02010e1002180a0b0702 63
    0xc6a0310410019207010303129408940520b015a0007240658004a20110200200c203541c9030300c07000032402c0300c0e0f091405195520103005502c006442d80070005010170345010440d0415000a000000f10412401e4010ba4846010b5010b2141c0c1450b401008000710301d0340d215000c03010380c0e40d40550310302845445644981810210700002c1809010b0740032508410300c110381c00707421f00901c140c0700010b840e0112420080d04041140b03d0052050018400620501143c0b100c0408440030420390001d14000034803080c04090141d42040c20001c070550100700c01030754454010011104103a8041407545088007213032030740e05002d903100f000a5940900c5a400d004d0030380e00000202100f440c0c01d40a40315160350b240780b0340584008001d50b14030540d041020301e80c3c024900b5a00b1001c604000c3d0b03d54035054540c96100d0180501e1a02004080040c0c0740d480c500c00d41028003481c4800068503107801c0c000302078000940c0b2440d8078411344e5504150400461030041101002c403001903001500c1c03c54203a0030454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 820673597 1250 820672347 820672357
    0x81f0b010309020a03061e0209060a03050c1201030b10080312011e0302210f030403030c020904110612070e060a090315090813050108060409082a0a0302210406080c 72
    0x41010780c0c0b001c0c1c150140c0c1d42c90b8140f00c01140035180c00602a00d01d1841c001d842d0141d82c111000942c0100801c1d00c6985801044030f0400020303250014030358841400c00c81c82480761020805000650704000706c18404100801401483c80d143d04000c16030b030301c001c2c2d19141d00540b08240070154215004001028450f440400f40b00b49008200c20a41d071a54009440c2c40e81d61038414660000700c0c03990402c80d0804101d41006898120000e6081500c4e6030340040c00403404100081c080c3c2c240401040c2080803c00246000406c01040a0384501000407201040300085440000081040c1c40515450802804540c0048095600c034940a411900c03403003800c80c044004480c60956403948030011a092501600e45405c0194140390a149880700044c081f103400303070907070b4451840c003840300000500301d5040324070800401e5010144000101074080b1800b81c5110710320200e003d045003000402d5408220041001c107580c858500401a4402564050080d230055030082244000490440180000504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 820674847 1250 820673597 820673599
    0x24051018090f020304060b0402070b0a02070f0f080d0605420c0d020706080105010c0b06180c0403061a0a06140d060b04030b060f0907030c02030c0105090c030601081f0b 74
    0x190201c1d5540726401c1207603955901849260b0f4040180010031205001d4180e83e50300480d030550415105498081802e50040c1101001650004030b90b01005007840c202c1030f83c030b80c003d0b4040e42c1304041030400030003030b511103420703001c51502d08840825103181c4085801d20040203500d01602810003ca044a071803440e101c2030059080802e415400100e01610013400b8181612014080030065031801918013585070b0003982c10f100101c001449580d030f02035038044d8000d822040c240310380d40f035040104a41034000c000305042c41420104101c1d0714040d003c010801c0700c0c41203c003084003000701d1520034a03500210483d280c0c000c1c6420000c00c00e55203c0c0420030054054a0942494001c00f103140e00c00f180c1c010750003050070500c0400d0400501c45044070160f8084000c0e540e8030110038986000174104800206028240350f1740c1c02c40350120a10030030544001003640c90080103541002c03070180b1341e51000705401510034800e240c0085002e41303010980a00b0910141e0401d81400d21603103480000d014691011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 820676097 1250 820674847 820674887
    0x9170901030b0307260601140d11040c0504170a05031204021c0303060e061e090c0d02070b0115020a080d09110904200a0b040302040b0a051201240510 66
    0xb07010107980a0002d8002441c0f5000401c2400031004102e200030f41c10003401003000d400c00c3c00100401c0861100341840c0140440d0800061304a5141490114200114254000340b4100d018103055802070010400e48040c0c014425a549d01118120b507512041d20b4000d04c160024081c884401d03c42018441e0803d1000381402a0000c8031000c0541079016240181d0010f6214042005071881418165802440075101d46101250b4034401e0340e1034001d07014040b4090380002001801c0080c1c844180c8585100400040d96180c841e07007410321440c4070030f011b407510b803000d085400a1103a000141d90a201a03001c035510381003805501000c030042840040540345510105e0300c0e013806541d1500d070301d41300324402c2c1c1180d05040b07655056901c1c03603214001824004c0140700414001544541c5c15070b402c5a90407200840c41c0c090304400f252554003a0b51000c0c5c2c1041c18603032100403950041d004a43c00d58510b1000140704145a000304902c107206115680d04041c0074103410021a1188400d95100c0d5400c03080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 820677347 1250 820676097 820676111
    0x615062001020c030d1505010309240b0d060e0d0e0d0b0c09120f2104182004090c03150303110114090109021503091509120301060503190917090103 65
    0x1043d8210b6210400000760555030b22240b141c42c08281e05a00c01400c828079080112248550300d04280040310740e10414842c0c15006c9e04041d540700c90300a00030142c4081c040300c0b03801e2094900080035016544a904040c00f410741d594403460b100b20098521100c00500c1010103903d503499036030800300060140c6012003000c128605494a803022014a040b0440740101118604d80c41c1013070426070b5000c07802050844074606400d5040000055506440f02c6198440518502c5e182c1007006003411403104031082e400c048403003450b040e200301500460741000740a12469941e16401c808803080d040309140000340110051000c44c1c89442554040701200340000340958500180c8040035408a4265035143e440d420348900314100141c05005045a881820307045090020001c0d484000380c0020014001d42a400180414002c0003210359880305880465031300e58407240b00509030b40c0200c1e01201100c9809184c618140110f01c2200001e1390400b602507090b2034400d0500302c050f441004414100360b02c0d204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 820678597 1250 820677347 820677367
    0x7050912190308090d090b03061c02030f0609070905011208030619090c271203050706020c071a18010509130609050609130308040f03030905150103061506200102 71
    0x91034001802511400f02c94640b075844a0300d0122900c0d2004c003000010041048541010760a0300d8000c5000c580b03844d1654201c0756294013450311400080d40c18421090142c40115000c981140a0880707201a0b4802d90f840d00404c4054400c20b1103800c56001c521613000b0702084040c805950440002460180304640c1c0c15084010845070fa084415001e540d248030202564005400c10342c9140c01e4030b60b018045860600e400800f405030700ca43e1511b60480c0c001007081603c036600310f4450b164007001c215114400c4107549556020789005087c8030b0140c030703064800d5103083c81e825a01103d5403d8600040030300b00d4001100c2540010307003e2500f25a50010512080300540100b10150a410500251034039144042000040007c0d00740c046800c2804503000c04a5401403000da131041d0041c4d5851010705036450101c005200c242406007540c0284c0c030f0340c4840204909015030490307028800502c618141c025030461601d04611480c40407c0c6c0070782554003400c2c2c10001035500104000e00060400840340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 820679847 1250 820678597 820678633
    0xf040201031e0c090e0907060c080703110f06010e071407060c020f0a0f1707080301090b030a080d0518030a0215091603053a0503151903051507050912 66
    0x1030703940010598024041c000b40420745007646c3d00070b0070038006041e680c0c40c200c0040c203a110031441c09460318400051403004d0502600a007952034003000100c495404005468940b50030b001c0c000c0b6000d00b6003030030111309035a2107552041e0b00c800e0002c007420b182491640d034270707001404001d0750081580168a641501148148003036108140524018003032000d0782d25018010060310001040200000e00000d40854803901c2681e05541034003100040190049000924090b41044018030210340010710191000468100c680500e0042c0d0483e0300c4c0700d1243d000f071a10f9000e4a503581005034001c161004100a95000f0290026034a900703a480003076401015040b0540613400c00e65244d4803c1201840d0815541c8204e0030704034941405419035a098101e009030205400d1080341000b0380400070840346403441c12541001e40f401842d01040300c00348400340310b00502520044d1054007a402d5500c0441c040311741d00512503216980ea440c5401000790420021a0b00c41c4c641ca02c8620030341c6c0724440c480040c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 820681097 1250 820679847 820679861
    0x612090302160824010b1219050c090108090a080a0c0c2411010b0d032f1e0c030706230301060c06320c09030106090f0c080f040201031e 60
    0x10242440c1309808405184852645000396854054034004000501d42c8030700740e40060000c0c1c1d00b501541e440d400c81004c03252280040203c40b90f89084144225040702e800203081d142c50a88801296642e083c0006803921520ba0b8040c020b800c0c20800104880d00c60041924054490207041500e00c2e141d41c000c1c9084424a002d0070f0440000c00121200b041e00940849034403d05c081c004c0c0100c51781c80020904403819110f00609002151907070355501480112901d2041b4480c00000300d100c2004030405585520204801d000340505e980781003880d0784003090700a0f515030041c00400c0c926203040d8003211034034030b501101c2e2086641c40c00c00d21110f0b8240301c001c43c0245035550780c1055640080c14a101200c204a0342c0e8400c500003030854807100c0399105e0005c0b2078054001096a00340d500d00f11401494418540c81d598035518050b004104601075a104081402280c2010071800810f641e003510050300c01c0d82d00c1c50340314100b5000180158400d4114100f031600c441c0380e6407050010b0130101c009071644 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 820682347 1250 820681097 820681109
    0xf0a08030d0e01240e06150d140a02041d06011103030103030e0306181f021c1a1206010e04030c060606020d02060702010606120b040b0d0b01031b061209030216 70
    0x1c03041ca9005040d030901445412074007003c1c45400c01c030050401c1d1110252240b00710175030442d080c2c0010780315a460361000303000200c50005659035201c075a6180c4000308a101d1004d0703000c80d0381401040b50010544240c03019503451441120803801318507a010403048008041c503040101c82e1f684203140c400140099402507120ba01c0da042522268001c1504001008007070070002480245000c02d124000508040b00c018401c9200307a02e51132041c40507007c2d1040c1c1c0c928100d8801203d50300141000d8540c0034020346010481c0540464850303504014071804101421459039004c0b02c01407081c0404840d41c550424424146102e440c25140e880000b698103036484800076130840d008000c105174060054660004592008220507424600302a1030003c10403100240c559031166515059191540000d601c01d0f0014070714a081c2e042890020141d003030902040710480204850b8005d111500340c0346100b503500c0c0e40c46c3d102a03280c031100000300400d2350003010f50451282d41c060b490b28465a10060300900a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 820683453 1106 820682347 820682351
    0x105151807020c03030a09060206152409041107050f0a050d0c05160f180c02060601051c09060b1e03030702010503311a04020904020f0a08030d 63
    0xb07484400f95010b00c00003402443d903a0f080603208040b03465581c02c4030800e56680d004442d01c4000090760f0341d0007030440d44005200c01c00a103212054151400300650400010000082c10b540c11003030556500a40040e545007070080500c414bc004041100003030000d8441d40c2d5425a588845130341d41c0c1d08101c484e94280082100510160404480d4422083c0166131104192a407840c07061040040104510a040b80201300c14022481d10307002e150054000d40d52184010b4a19a20482c85c9503100700011441126020325442513804241c0140170001e2010703040d205101400d481c02d00c0c03281a000c00707800c034840c043d03400004440741d407542840d1144d12511898000c200f00c48011429405c000321100c81c400e018154a048601a203000d50760602000070708804015034500c0580d4040c0d001307580c82c0c0006003d42401c41e108191070030043c02945d0040d5071030148070304640000c4501c0e40c01e56 = true := by decide +kernel

theorem cover : BRFrame.Cov 820503597 820683453 := by
  have h0 := BRFrame.cov_init 820503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 820503597 ≤ n) (h2 : n < 820683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
