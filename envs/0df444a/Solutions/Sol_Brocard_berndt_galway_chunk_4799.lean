-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4799
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:46:08.417966+00:00
-- url     : https://prove2.me/submissions/f4459e94-412e-4b38-a750-8e937610c331

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 862949640 ≤ n < 863129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 862950890 1250 862949640 862949653
    0x60609010e0402010903110d060207080a030c0801030c050f0609040c08060a0602030a020303180c0d120306090501030f11240909010e1303050c0a0b0f0a0f0608150912030403020f 78
    0x480c0d020310701903208540c16502c066416040d6520507044445c02c90405810602000c0c151001070132620013007248501552020351220701410004040d00d00c80c5140c64200007036100100700040b50003403644192041122011a01e054150104540e40038a205007a130040c109400c00b40039942080c1c0003401101c00750b07102405103844043c02c0e030b0341e4801d00c07142c803005900400c000740b1001c1052036255901200e203070980d68000c200400140d164100002c0071b6960f002814035072054550035201c0c1c01c004203503c04042c4a1503155071200400040032290180c01e002c0502c03042c240d0703999035803017180902a81000140315401859519070158100c0756500d800340c881e000c004100120303100b10041c4603040c01c00c007c000e8405281e400715600e03041014120f1084c401c0e03440360400a0300070340c422840b45983d0300c0d0071500f51401c4002003056408299507094440d00d00344061150b03a0700400c100c1b16071a40c4003000c0050b500d40003642d030b04e40610340d60a61202000881448100b65002c2000301100d92458100d944 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 862952140 1250 862950890 862950899
    0x311130c0c1e05030f03070e2e1107060201060303030f0209100c1a1303030c0c12050906040f1202090a0e03030a1a0d061b0c020d02060304050304150206060901 70
    0x2140d010039681004a4506209440000c42e24015036035940008901002c0b650080d40d111440c5070403a20801d00046004000c02151a038041c8222044403002c0303502e00780c4510310388650011a010100d000d0f60388200402c00c3c090080c01220400d100a6045080b1800540d1f22000203000b40150b01045000900f008145844800d560094540b006002401801ca101c00003406881540c25a40126030781c40001c0e100840400620560b04d118800c9400e40482d05499403500404840e03a810715003091000251007600480c14480d540b8800010500740b01d55501c820300001080c500503540508820803107180d000c2100440c1c0c22500402034420755040106446e40c202c5401a0303070003d00d41405550040c40010207040003034000c1041e160b4101c0b503603654903681c04041004c040981c1c8041d00c2e51901c0c1c400407a51141c0c1039101806901d0366182600c0c0b0808036030b0004811003180701d0003900c202da0110100e01848024030403200208015941007843c00c2c01260043c1d29104125400c0c0e1084845400014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 862953390 1250 862952140 862952179
    0x708100501180e190c1a0705070902030a020c030304050a031419050304030e0d0c15031107020d080f03010f0311011b0f0c2705060109050109120602130311 68
    0x40c1640ca07040651081050310b128610300414016030316a2803881101e1101d0440e80248030b81c80ca01030301802c0c0180c0d8003800c1c40d28115401e000d07a000c0003c907003020444000400e01c086580320903907901c10300240c1e403a100d25003a00d01070f000d4000c1d004954080002441704001c40000c4090501c1d209807034100f020610011140c100d80105552482180304170a0000c0d0440d00c620300444e8403d2003070604a1103404035402203800b078082d000045814104c039140c2402035500d007103280c4d0f030404c0f0586401c5c081c4000b000300a95a030700624400078040c001403c0041c042042d03100544014405107088540c481d07948815046802c942441300790761520309e000548000354402c0c8c198035440740c0001c0c039031070099905a0380c1074035050540c007080d2010b811282d0302044103070300e0b0411200840c0c01640c12030404000c0e80d00c0c000c00ca40014141b94140803041b0f42c02c010720398105440300119411040c0c034508003040703824030401920500c0c06000070403500000100c2004400f4210740e4001c0400e6500c10400c8140c41c3c00715 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 862954640 1250 862953390 862953401
    0x209040c11070315020d0608100e1b012319030f11160606081c020c04051e0702012a0f1416140a06091205090a031e14070810 55
    0x458841e0080b800c00d00c0070030003042c5072209094a0500061400c8001d20f42202183c40c81d8021130f01682003101110050700c2640241c403041131004024082e41841c1c003400010264a17020201e060045803907014200014000c0540308004407425503d40d60002a4404400c11448030404400f0910300469241e4081052145140344d01001c0380807440c0002003001203255644441e011241607454003400f003507520052000b00a1301d121900c10615407181c040000c0d0801e5a00340005024500d88401c1162091400440b4012a00c02700e1000b102a03c0b0210128058040844132540e0502c8014002402c02d181c984004c017441916070380c0c4030031640b200f8000c0b01d00d0303441614025440403040c8200d03221140f05200313462030541b1601e920b6010380d04100d131041c106800d901003915080d560b1003014081c000520140b4402c90054541246044111000199490400d020290030888525115000030501a001c10003854000071340303400c1c41c8003420300c3c1c558460301400754541c42c0c042c9100401c103040303140c010b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 862955890 1250 862954640 862954667
    0x70506010b07020301180b18030f0304031407060c0906030509010510060302090f270c040305030307030b0a03020909010e0f030f04090e01020417010c08060f0f0d020f030d030209040c 80
    0x549866403074010389641c0354202d0314059906550707075150790041880c05508500c00620036881d030426490f0074440d91415401203941da85030740e04200b1041c5030310300d03458044903405607060a02000a650030406c2c1100386c0a40c0703c004144174a1312100040780c5130440340c000d0890301d0300c1e40e060001e81e54001025007620b07401d031044400c00b4540082400618003d80150070b6500d4082d00c1d40c5149101c8000050142c102840341340c10503d003031220b52003001c0107800d2191380003c030100c8091a1910350b554059682c80020078888c10195104400c0768190340d200c420741e006540061821446003410341c800d600810052104080c144664160580e4200c00481035481207000c1100c52800c00349041c40c42c40c090112001c6210007950300f000007280901a8450944c40300204100001da07080c1501d1002d0020341009e4600c510403117400942c034065031703150030300d0b40003e03801070f00e005c03080e000c00d0700c042141030750300215681d414010f40b000504140d40c1039026240c03101c403c0394184059100410140c9079100700c2a074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 862957140 1250 862955890 862955893
    0x409060e10051c020102011b09080d050306010f1206051201050907060801081f02300906010e0c0705120a020d0e0f0102151f060306061d060406140d050406050117030705 74
    0x1076510301d10f015040c50714099006000100e4000000402c3c006000380510703008010444404050003548420444100c404001c1c2c01d00500d58108400040c04480d040e11040d4100014249031099800580d0000c20081601401e41c1544103000107001d400f816040350240350034852000001001e5201c0c1d04881d040f600128082d001c13500302ea01c24190300c440e40d903180070480781d02001152109403641005010744480216011000e90300740c500c2c0444d14101410501c190b512200040c421600ba40300d482d03401407030211b107641c0d0395002d038501181010481c4136a2040d0004c00308014021a401040071b10726101c041d61032200c032842c1ca1041118941600321154016400111407102c0d25001c1c1403800c0c0c0000401c60f20f0344000106000f41d5000380c1454100c0c07800243c80303481c20000c1d1508495031320380a80c513000b81e03d4103600c50600402d080e401140305203000c0144030901d40c00c041ea404000c460801c40466018031080c58282803890180100388181c3c21854810312482c10040400300036100000d074082c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 862958390 1250 862957140 862957159
    0x311040b0105030a0f0e0609060f0a060506040902090117070509030d03051509070215070309030f050c0a2009010e061203030702070e19020331030503160c02060409060e1005 76
    0x4241e00070020841c0180b0103940c4e1b0000c680d94000200a058480d00c45200100312614004601040c814000782c41e1181c242d042c08002d0055668202c08e550943e00c410301c0040c0c445804400407a09098840003070440000d800003446529a80240140780726402907044801c25001e039801141191b5045500d00c0803961203c100c1c03549032808011131a000b140c3c902c11119000c9030100c84e1012060103542c200003003540e5480303400806401081520030b00341c10f4246075003007400c03074891641c850610440080c10312000d07403c103841c00c071b9014542003603000015180c01440c3d80c42c3c0394442035980f415a045845000c1c04840f00d80340c0b803030000446e4400c60b007035805090b03132078a0910013103003004018111301e627183c540010b807880704015480514800c2d5003801c0c03068100c400e04403114142c008012101510b4000c105100c20200f0381050031079802941704101c031140c600403c04120b440c2100400000e604c59800a03000400d04c184d90840b009032104400c2d680425210b031010303031003403120500c903194100c134001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 862959640 1250 862958390 862958401
    0xc0311130b070c050603070e0301060f080a150f15050f040b01050d050408090d0302100b010f0f20010c050301060216120f15020307030e06010801020a0905101103040f0311040b010503 80
    0x24002c2d0480c1403142844400160300c60000480940044540303000185080e800f82040d031500b401f402d401030014012210b802400c000e040d6488407114100901403407104503040c1303c40000d0790b00019010400b44070401011040c1091401041030742e2003058420300190511841da0300d4248650048408140c681a2500081046110142000800540380c0100078401c5000680f54640c84501240c4641c0c00f4009290340c0c4080d4000322603100108504120520303045002064210703443c0c07042021142003071940c26503204c0303a5075641c410045858949500705442e001c402c0b41c111000d1070507030740e00750291380030700c0014020390580303d8030352050050210b86d00e0071080100b00100c0f0441031850040d41081451030354214020141c0e0300c00e680f40000a0b94a1840c0c00b0540350a0154601510b8203038000d6103010443d00000303000081d41d0003142c3c40343c0d98480d12040d8840c02101d407458191855019a5101c5135201d000403124001440300303440e4000c0799404032100d80340600c5140c400041c143c69250558464 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 862960890 1250 862959640 862959659
    0x60c0a1805030303180a080304060207060507030509100b0a0f15020f06040c14060714280b01271a091e012313090302010b101428030c031113 62
    0x70365a888176502500300e0080128000000451259016500140c2c1e194410300d800011075400414090405203460280144640082503600d0340c00541c00340426105001000510316208603803080005071001680080c0140e411050000c030382030b00ba02510082c20840e00941d40f030b42002c0342c0081c84510580424000c0d22491041c280e074038003001d090103042198968174403441201c0f6601900c40d50380100c1c0344540940709514809500840d1b29040b5411802c41d940d0196a0340041c01802000c2018200d21500d400c9880c0940c012140c80700c0c4148880980d0518400180f001041c42c24000c5a4400c00154807146a141c8501e5404000003403400580c40c2080ca0224800354801c658103e081e01c1107a0f901035a900b90b2110082154540d0001e501075251070b01074210380501d11f8030340c0507043da035440c038100c6034002019090305948000758554822282100f03003000440d2501d030070480740444c40c40d000c1d0558958021142180350307071820010a00f400c40007900d5800750409448440b030940710300b842014031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 862962140 1250 862960890 862960921
    0x7030f0602031801051e070906051603020102091503040209010e090a0b10080106062703120f18060201050612060c090d020f030a0b0406061a0406051b060c0a1805030303 74
    0x280c0f0f541600d030489452440f6095410a66080e4030742e40d0108030001c500504029917907000080c900301110310920b01000509240038255207985903444000480c41450700039012070344c4220303000700143c1c00041c8601c04030006401c20b55099000301a15000480c018008009403401954800000c0c4640d900590710310361208002001080b8001c41c11400050512090150b0b001a1020b500d5041c105e003640840380700c51a40d00a080e1015070320112042010400c807080421700c0004e80d2070600c3d8482d511750411341d00c900440e42801810741c084000020165410f50100740282801c40355039011048041005a4172402a214400103080401001c2d402e80744c4041e00c075151610142001c0200031070344000a003029098841550b5803a1030000300020841e0501c40e13000905501c42c010203120100303820301401e900981c02007505012000843c40b650301204101c1240c0e812050701140c416141148411100b504038902d02c40200c0c44610f80c54500d0007083d150032040c1ca401500860555440751100b900407075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 862963390 1250 862962140 862962151
    0x7020f100306050316081911060f040509011205010b0118060c020f0d030809060c0717090402160309060e0301091e14060c0315040509070e0c160f0209060307030f060203 74
    0x15958240001c3c0d0340c0307051251054a0511005800c82140380c0713000e441c2855030308170700d126078503098034071480c002840e00300301075401841a1280c640310036a4904020103403286400c5190b10100c410000918000c03c290f40c3c0941c030b40314600030b102440c120700056401d9903000000480e0104c98241c2070080c1d6105150b00b00180d8001072111403440c0b924000710341d4003d900482074001840d400e0400040540410540d07070005c1502528624155032034407044c1c609506860000080100080c03545d10a5072230390140c580d840b0740c1c01e8a40990500c10710340900000100c0c4902000300302c041c2d894002520f8103225184880b5000000c07201d10180c0032083e0a0101c5900f00d0488003000401035a000030030301044014440c15240c1e10240d074038204504c40400b00b01c0c00075095403040c0d003848100700d4603100c0800c800c1c3c1100d02c0c5001da8810380e1500c880450003402035440c14a00048810421400e005032166101c070424000e0b00e10211302e4850000745525520240030161040402d0001000080c8171a4021907100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 862964640 1250 862963390 862963397
    0xc0323070b0c0702040e06010e0a05060609060c060609070c02130209190e0f1b2a100614040e120c100911030d0816030b0a120309090509010207020f10 66
    0x140360399481000c401c19995609145004143c810440c207240c8241640c048003800203140070342c5010300541000c10024046c600542d16840403845a03146c000940e01c8049009107002d8880486481c0555902401c45e400d5200305049004190719500500c81c00d440c2d142c02800000c080c00d00f1154180c0a58082000140c104540390194080c50007107202d0007000d400b480701c2c9a5041d04102c04616001c10300645105c0e02140d225105007020b80b0044c003100c0d00b82031114144528500440003100040e00e81c100c00342c42c035000b864550074a0208603071140068548440c100e49480300c0c40c80912040322404c0c0c0d440c3c1c1c8184e10941c2903d00700030146014008030801103081b00c0c44003548a0385401500c20030107040b1030001d00c00700c5201c454034090000c0350341c4110510300310000f40b03840702c0c210140c0d1407080614400d142d615003882440c0d40301c00c4400006010464403c020144080c0b0340203121103003e2080141c00303450072011032039294060003107a54154009112124480d50f0310100300400140d4003001013403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 862965890 1250 862964640 862964647
    0x9090304170f07061d0f130606022a030a03050d0209030d030609050f0912090102010908032a04051e040906050702240606030115110303040f03030b010c0323 69
    0x880355100c84202001e01038030161074450960440c403494140e641d000072040c020111907400c1c030b00702070f9414000031a0080703442e030791000703040000318800e1094060b4404409052075008120a40c0014810f4a40548189040902d8040c1c40300780c0c0c880148030305000d50580003003401c00c010a1042000d004035002202005140c0b01014000919200d1040f862902103902c0348400c001c003003602d2282c5680441440c01844091400308003a98840c80201849004000003090019903a4402d510a984440c0e0000c5040c0c3d46c0e0a045900706c8602c6684003000c0b18610140328865042ca54440c1514129007005d003c8004c04c0e940d504403000b480c1541e00364250020303030b00d6020101280160107018007401281d0003030406107001c010030120403030b4081c190484028100d420320125445000490307044030446004180b81e05000da0381140d000b001c84c111030300d151002000340400e001e12229100b1085100781c4040041c80034003401951082c03030f10440a800710b01418103075800c2041401d08100c0d400c0c403140c081ca14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 862967140 1250 862965890 862965899
    0x50601020f1009030305150d0303020a1206380a03020702181302010e0f0d0f06230717010506071203110703080109060504110f090d0b0702061501030b01020c09090304 73
    0xc1c100c103202404484940f603180c80300030300d5054807503160040c810340b0384a416000480c2c0070800c5008500001800c060380001e090440901c04c00f06030940302d560500510255648020281d0034600404400c000d242000010080054002a00301074115a07181ca40f4100112842e05400035007011034166040655440e40e910090a07440c0780900c140055094071206107941d000052441c440c80803a03078052444209180915542c1081445840340d00502d00054404640303004400781c0301450b000034681c0c0030170020010110700070150034401c101980d6840c1036480d240121030320700c610070b22440790000b0081200380080b4030790180314155445ca03800c0108040c0d030501d00c3c2c0b44065004d80c400b60000355142d40144a400318074001e2500520b070480f02408003106040c8640384070300ca005988410101d00140101440e2692124040c40a42091041c3c18920700344202a40300e500880300c90602083ca070807d941c966019200e090658a0103034011311500c0807031014005e10107406048d803036103803000f07000005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 862968390 1250 862967140 862967143
    0x40b13030c140313050103020913090c050402041203170609181203100513050103080327030a0c2603072604030e011d13090609150e0f07080709050601020f 68
    0xb100c141d0200950b80d0740d07000913200d40d2800c1c007a003080e41050700400c80c2c601c0951301e0f1115401e444400c1c031b030002000352080c54060600c00c180d6000c5500a800400c2c0001d000e21014600e801c0c46000751255442c019900c2842c0380c01030005c54500c0e5102d4060343c08208801440064803042a44690032140c8082d000b503c8003845400480704c0d4000f140c00c1280500060801c030f14031040c0c1040d50001804154156a540d41d801d010041244034034120405210032a48814400034654004200969036a0800443c000704913490b4a48159102c0504100203840029401e250141050f0443e00c8141991103a100450b049140100c1206000d00f144541c1003d100d001e19415000724842d8854105a44582c0005017072401a49180344224a03400c0000d182511a10508140c0c40c00412001620130318501c0c1050003800e081f400540740c00002544209c0c541c2d00c039805183c428002004039400c990482c100c40e035544505001c0c0400a810004040041008a0300059040703071050040d5218003c01d000b82a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 862969640 1250 862968390 862968413
    0x12041a0405010b030c06180621090a0b060f03100c090f0803131e050d02060c01020a0c1b080309120708030d150b0307301802030601080303040b13030c 66
    0x2941c8a95490481a04500d010085210920304c00d0342c0040c1002034a10500c119240403100d07050040c0c100041e021a40550000325170b4031121601c0380180c441c1084480103a0320b00c444a02200d0303e03444540451494074200001d00c40c0c014004005101c401d041d024044050304020801904ac064025004121403035a50701000c040c03d03046c801103858881c8402c000c40351040030790290b080480c3e0506a20f11007200079070454160740e0306035408010a42c59201184042c4940034a920480d48040b4122140503840300888200601480206c0c18030015000c901044140d0340c03007900c50320352080100486a0504466018004000c1010f070303811282d030340c052641941e110007170792681d050b0395100207401010000307205005000440d6001e410762030001d070f000d40082c1d1b0b0a0ba425200010011380d59135030503051405044000b020b01018404000d1070241040c0190310341d03504a00c64060350002041d003402c000300380e0388a15007014460140e1f48a14090011840c50441c3c00d03000c002e00c0940c0d110205500c0e4908 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 862970890 1250 862969640 862969643
    0x18050a030303090b0f241f030f0b011e080406090804240801030c03081b0318041802181302090c09010e030a02101b170301031205040b12041a04 63
    0x811003c03002c1c681407000b50700041030150180a000d05108181d1a03507020901481c10400b00031120f042c0001c0000c0125846d01c12a000b206061514003c20075410780080000700324104003800b920720307440c006503000006020103201000c54202c804400d1481004d0b076603009400380c003000403140d40c103454550356a845030b00910302108007980c0102c00442400840ca00c440058038100c0c8281d415a43c0d1086016138521002c2c003d0240170429600703201e01d500c0040054840c1004072640c5044a007149040a0706403001148202d14041e04055940c00c0d80c510b02c04100c0c2d0040c903004844030141a4000203000141801310044059030781d0100685800b40782502a40000d00504d4035402403000040c48000080c0e0f04d2030094006804400058403a01244260b819003810404019020700802003030103400d640b006005821403941c00490510720384020b50503640191041d0101d5012820159981c2c811403080800405042080d180300c81403c0038a02d4000717205114411103440ca042e012a85503005840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 862972140 1250 862970890 862970897
    0x1a010e040e010c05070c0e06090c1b0f070807080105010f05010507080d061d2802160b040b041a01060905010e060d020d05090601050d03051611090a0c08010b0906030718050a0303 78
    0x10b04200f4440c406c8100002064100240310303541c54200f010419005014200030600c030703008501c96810030303241803c0081100c3c50030115403800f81c081a02c2980c078001c41c802d0700014003c1d03001c0420b0301c034411301a290503516a0b0181070300c46480c0c1401101c8644c4004410383d05c105090000181c1d49040e0700901005195107409299500004400b649000300701520b002c0c0311503001107400c15040441c0c24211843c2c5150f60380143c403a6140b01e03400045031840c10005040501c010100010042101a41130080d80212070180507501c07158448000082d0a00400c00419140c5004100f070758400d0410b40c2e03900c800a0080350901180401c108240d0704000e64186540303445000b0019000000c0003e10300501c01216220091f0646840103403c034880c0d40c01c0e805640b000c5c034044200748279410310208041c40020342042050701c1c10700424001004014000c5001131685400091550160710544a84001c0140300ca40f940c1c0310400c068851040101e8040c0400c44184000a400c2d640c6c0c50211006501076103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 862973390 1250 862972140 862972147
    0x70c0b0c1e0a020f01030e10240902030a0c020a0803180309100f020d02032b20041e06080c0d110417010b09090325150b0909011a010e040e010c05 64
    0x4100130264400e000002d04040c40c14040c21500c520009407420264040000000c08621b102c0107508100b544515020036006070500000d01005a03074011882040c1c4d00e403082040c1042128100e0b107918501001400211042c8049240d60440030950811600c1d00c004507482c0405190100b9490305a10202201040c550103e41c0350094040c4426560b029461014602c1d09904030b0002e6030302030700815840c030301d5016a0803000c6000020f6205409020005200c4907981c0c00c001c02c0103429501901500c04c0c02032030080104007150b100080d01c400c0e99007644900f1015951401082c800780c10220001d0f00c0070303480e4026500011072303440c010805801e190441c01d540e07050b203001080c295400c185a842c024842d40c7c00300102d034807011013580c005954155031003600c4030070a4120b50510814200240c284840c0e254401c04414060744101d03801c0205850400840d5502d40c1070b1401c072034003d4a02011000102c1d0030b68030a61148162807103020008100040d00d981c401c0c2c460382110302c40c0e685000841c9000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 862974640 1250 862973390 862973393
    0x40303080702070506030a48020d1715130509010e0a0c0b0310090f0f0b01030504030e04051f0b0306030f07080703290f040215070c0b0c1e0a 62
    0x15a0441d0701080780e0000340002403500001c2112844010104203003d82d548901400182c401c04040c04402044a90644000321024403000c0d403240e03500007030f6054215890401081d42c0041340403e4055040d484000c0141103014000410100082100c10201c80703103104900749503102600c0c3c1c449a003012000060700d1512104407421185404580000d640c0070032094000145541c0c40801075406c401103464880d100e0000182c2604070541140508a0614146480d440d1075540010540b4000440500143c1c65070001542161015540900010340c070000046850509070444c5800c40742140c6114940b00102c0c2100089440c2600103408024001050101524080084141424012000d1301c616031810010940d034490900c0b0050800031154001e4881da0005c0c00320100c100c600461a0580f03143c1000404401001120200c1c4140c0003e107070100a108184c056900c2c50394002003586109040005c19000f58200400211043c49041481c44541c10305c85c0303030b20948051110040c401d8840340d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 862975890 1250 862974640 862974647
    0x90e221202060a090203071203090b04171c1b081c0617070807090e070909080307020105010f150305060f181504020f250b01381209010605030d05040303 67
    0x5020503c00714100004000581ea01060741f904072140c210440c02c0222143c6416039440306103500c6181810310110b000503014500400c2420400c0d141b2081d01d041d10320440c420710b81c10440c82003074800030780b03c44210101c120100303c419207080d001c1c00180b070408040b00d106c00b151084001502c01d1240d1100020042c28091409008825520b2400307070560f1410410741d203503100b6540c401c4940b241d0301e0306a6400b18140074440f40000e080c04c00c0040c406203602c0c2c00c000c0c1c02940195402801503203084000034080366040d030307c40196107a181654640d11100b44048000c1d18001c2c100f264404003440c4090301c1a66000d1010080100e050310901d050316281500070020f424602c403050203140100b003c0744030460030400700c40001e0b03411039244100c805038200b030820081400d0801401441403400104841900c106440039070000642ca00c0c400c6801020749080303140000c101e5582c000740074401c211888020f881015481140e0600005140303075140002803428201500d00404528001400d2003031550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 862977140 1250 862975890 862975903
    0x7180e01180e16031a1b070c031a090f011104090915180506070837060e1f0308070803131502041809020904080a0201090812061f090e221202 62
    0x1701c09441c10a6203080c0c0c4030004003d8450149081d90079000459004101e4032031490805540c11407100740740c101080703104519002d1b0580d9440007030b1248965040c10709a05004000504114070400c81c20700d4600b16415018040d5954201ca41e031103448070805401d1081d12803004008002000324040c2109800e22506101e0060915820080d030303402049054980000d0b8141c03400381c2c500c450500b58605d00c86011042d6a4001503005441c1031001c000348151000c039120b030103246a02c0ba11140a40e981000990303070b848511004107003920522009000c1000b000103036512841041c01c651800740d00741d982d2115100c003000d04007215a408641803190003803900482c3d07800c0004480810480200da000100316580080004154110014811710050320130340004258540c8040e400d03498544141d40d00809100841d01c00e8003030b505c90720040102c1d00d0741008150028056440d002103440c2468650107160b0700080c610b503039845040090a001000d000396041e4018040c900303658800840040003410200c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 862978390 1250 862977140 862977173
    0x303091b060a1704080708030414010b0319110109050a15031d06040b0c1b010515062a030f030406021e0a0905040f180b07180e01180e1603 61
    0x281c2403001c1c03040039400406480100c5040c03101c00714a80da50303280001e40c42c8a1030f40b004000350004001d2008110030710070b0414020744120005d00660008909155a0b121000418622041082507000100b45c100840141107a4185003000d201ea403240082010a034442c3e00029444072084a502a801e034103104a020100418800c07174050070590044a13030382c50000c0c2002c0c00211209010403410691041140c821000121000e1682c039180703840e05000701812134840103008070000389a005450203c0440d03020304c01004c0c50002052411001070610700c1141e9036062288010804080b100c1400405907214502c0f824015980d0807420035804501c0c0318015180114420502c0200742054202c0d501070180c40e01510001400804480351401038400d031590b6640b907103110300041051049100d14075204045d0380e140d2886240c00341015038220202885014817100c00c520040c80780f44940f01070200c1c2a41001004141d0b508101140360410600b10347d014440308044c942001040044600c507491032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 862979640 1250 862978390 862978399
    0xc010804080a03021624050c030702032a07090219020d0203040504180b0103060209011d0f012007061808010902060702040b0a0e0c21040f140f0303091b 67
    0x24141903a401c0c4032030007954461001e06070013052801d110706081c0b103614002504545046120900511020500703110181034116580c1810300062801451804032802200e09500071450040b480c00c400c403400040c90001c4070603207041107818003002c3d000c0090f0000b403c0010f1005070354901442e4204030140061041c07400355040350720341e42c420b0794003c02500c088803402e0300c01003165014844510b0301141d650100821900d00d440001c800e000c002d13070190404036000c3e2281600d624010502d03407021040750055136481407000c040d6a400d175100703007001c1d2500141414520b00e01450045103d0030440c65421041c0020907150740d0080c05454104110020304510300200408030264020600074403c11030041c2c02a0345a05800a1a4842092020080c520407080c40307461308100440007240d911008000d0f05004a4540940001104550090044d98001d103d110203040594980d4152040c8502194250144007000304072000c050000398482c0c1d03443c102910741c0000805040c080c06407814481c5004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 862980890 1250 862979640 862979657
    0x6013e060f040b0928020108100b07020d021318020a05040903080f04020102071205030301051f0c020d02130914010e03090105030a0b13020706091110020c0d020a0f080f0c01 76
    0x4225030800403907003140d005070b4100c405551300b6064515112001140d0030b401e083c1101e03400200000307014101c50b00b5200340d980e03000340d0310343c00c43d50264001c450003155500e41d0200a07450040c82e0080007210f10328405015002c0c90078510303020390215000000310701d140e403804202c541c00f140307425203100000d40001c48042150034071a071001000354000070b01420f101700800003c1030940e03000704002402004011f10041c1c05080c1440c1c0030b40c8980003071080d03d01440f1011510440c581440d0724000b403031056a074496403184419001c000e644120a1820381e0400c0035844003884540c0fa50241412103030003900b21b403030750200d984116400c5803060016060903400a2210410301c0e83d0201c1140d0b000020304a020545800085c0010a08180043d8207d100b920000f17600c03080000b5074010350b00440c000c5510034103000b00b26041c0504045c0500d5180016000300e00d0060842c0b41c906004a02c240c0081c0401030313141e4442403180544160354000854951005502780d807104c5c01045009040c980a29100f641d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 862982140 1250 862980890 862980901
    0x9010504260912120a0f03061a0d090f06050a020405010e0306100501050f0409050106110d030507020d110a08040e06030d0f0504030602032503020c010c0e1806013e06 73
    0x300c41c050720040522490b428024074540f00001c01001113540490524a966034841d220f0160041c84900c0710200424102600001c55108000381e414029610701c101d2441d11400741c0d41d4070f000701101c040807203800b202d14014402241003440390030702c145942a001a502d6040c0800508a21110b0b41d1140c442e5001408020207820303030b91001d4085800030709006407a43e81c8449000740c2c1c0c0c00381c0e81000f01501d00e000c1c00081ca4079400f40d00c11070094800400c0c0d520960208004400340c502c207c84481c007613400b41c10b015132a02d200b803141c0310301940c40c0d80503501e01c01b500343d8039119158070581c020b2160140c590203006843c0341c28455a1200f00850419920801c51140b0180450165100282034681d010000505890a00b070240402100100f4000003400381e034400a0000d400024103c4400c0d803a28404501c4a03006280c00c18900b100204014074000c115180414200e000a0425042046e2103d5884600340314411070b42c2c548405200951041040c0007011103101001803441d0007642c0043c00344513 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 862983390 1250 862982140 862982213
    0x15180b0d020306030a060e0703150212010b0a0e0a031a0906070c0206161a1b09030705040207210c1728031b0207330c030c02060309010504 61
    0x8030300d203005500c05601c0340d54100010b400c0400140001c0d1a2908040b01c00c20034000100f6081c0030b50b88070364128032134811803030412401c9000e0001c810000d6450103006211041820002e0804418a4549519404480c1c004142841002d500031940d4000300743d51280f10310100404198000540c030014440ad250004000303200c0103101c0c074041d00516001450102400720f50303900c0e007026a0070803034683c00500144004105510101c0b00307901c141030030451031240c003200301c0e0850f030100c5c000600400a143c14501000300035808000202c49100034411111002d180c4080c1c00351510300f0030344810040024030700b000b07800103042c085010b040001c2006041e50340840c4a20041c004401c2a00c12500c043d090310059004086180c151060b0120388506510010381c001400010b0b0f4200310200714920010103001c1c2080c2c540c0c40c411000008400e0306200d542c80c071070442848164020f2400300203590701600407620039070042e9003220f1142d440b20100800e100c884101003481140716031a8803804518060040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 862984640 1250 862983390 862983397
    0x50706020304060f02030412030e03030130060e100b0916051803251715100e070509010215010e0c070809150a08011a030a0507030207060615180b 64
    0x42025034080041014041e07a94000c01030a42081001c5540781041e080904c0c050304d40110400c0001e00f0a010490700e100040244ca0480d42d07511203403602103d41d105038240c40c42c400c544d2103450004080190300410114010b4441803030000d000b0b84050728a0700b624005440e0a4041540039020780030500140344041595a07501e49903030b00d40300791100b04410744d01440d00c0901410b1a07262241d05c040c43e0300b0100030300e0345032000c1c1a50b500b80c2c8501c0e9511132046059828a180c1c18159030810721030f20440d02140801c4d030390700a8010003203881180e240c0800e83d004102c00d4400c039001800201d05c400f40e80d601001200ad0360000900543d0302980b5145c0303000007d020007401803043c12404200f10040005070800e84294000c0103021000c040075038001c0d0803543d00308240300300000301d81500002e56103604135080c40441070f0301102d141c03459955101e031101a09000c2c1121042640c00c0040e00080307a034510548000d01408882a0311030966403400034494003c0140c0c09000000c1514100440d00119048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 862985890 1250 862984640 862984643
    0xc080405100603030f0c02010e040510090b090411062206080a0501061d130b03191e0503090d111201060807270c020c09040605010f0e0705121b0f04090b100507 70
    0x206c4218190710048800100c84284150418107140502042d052003d8113441034949800b410131032560705a04010740cc203010354000d000c62a060805038900d00b031078401005900c002524180c24411040c415086001c2298850400600385200340510030070140500381c0104000c0c601a1403a8204460000c06290000140c610812100a004602042907006074a81c1a00141920000420f80c106071078001800c04086070b8070b0420b1804100d004803400468440c4682020095042c141700b90148403401c104200c0548803405124286045980c079000c0e10007880d2205400440c00c0752919400a00e40409a008900459441503405d250700c0c802a0000d801c101e040c002c04030300786c20928002da0900060324116074001d40351070200002d1000c41d80240d4100d6410b2000010b20039550302095840d6401614440c0020382d0070807070603000204035003195400654803038484c04041080e00448180d42e129400e515801d020105040100410710b100742d88003224290fa210001900e00040100740e44a0640c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 862987140 1250 862985890 862985897
    0xb070f0c020306180709060902030402030c0319060b03031207030b090a1e1a030601030309060212070804030209040201210c09080307020102070e0703060503030412060b011110090f060c080405100603030f 89
    0x9800721135000800c44200107082402d41005003d07103855078400a0f60084605a0291080100e06800f90400207103104003070340d10401180d0312982540c0c650010341110a9450b034580301c20700c640c0700003055100b901e500640050302d00040540300701d000d018400342c00400c010510b9107171040d5022007000724400e500e0040f224413000a01000e402521222034604010003c3c2c141c400c1da0004402c0640000400c000e8581c0c640032240c03040000b07143c000032446101c07001010a00e00303110410050030106071580d005881414001d0654612049110383c12285480c1000482d44a0014031003154100c94a00e025010803030140d880c26071260000b03990341e0340911802409104180029841c14420f034404806440014140ca9650350b0303c0c582c2280e1801001025202c0c1c51504800524035030040445106002054001c0c1007590360034542c00004016071141a5180200202950000b580a108106411720640c483d01e2090619080141c90300e0b800302d0f000b41c901858440c00340003280c0c01030752400c0034075110715 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 862988390 1250 862987140 862987171
    0x130b0d0e030a0917060f160201200406090b03010f05041e0c0504050a06020601150c14070605030a050f160e04060506120f010b0a0801030605060a15020f010c090501080109020f0909040b070f0c020306 87
    0x307404a00615804a05540412418051241102b0002c1c0180f00319202079076842d000c00d40721150006244428481c0404071070802c0c40070009410260042d1000e08103910001032040c841e00902d4050303502020001001440001e0144482e103019124600600700510081c1900c2d03043c04407a68150003154020001e000e0601030107010840c0f0303401d00c1c41d01d01c00041d0545a80a0ba00c240262454209840d5a0301290030302000607690950802c20a2103079465501c415000c030070a00080c1c4e112083d010916070041d03103541d00800d90361a007000030820782010238000b5509280140d03c800400c0c034181c001c00445d003020001c1d05845540030030940d05480d080000010b9039100c000001d085440a64003e10040119031203c100417500450b011065814000080c802c0750700603182225140c90320b0042d113020960000042c48640c446034058181c4100780c410281c604004400014080d5804450072030390601d070a000c200a241e406050700030000760901b09041b070001c1c0c50740041c0e2034420042c0300309103858044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 862989640 1250 862988390 862988431
    0x6060706150b090f0f130c0201020f071a090c010917031c050a050106081314030f070f050706181203020a2003060c130b0d0e030a0917060f 61
    0x9501121585080c42258169180d603106030b10981e40024543c548034400d050365101050620600050090300014140305038a803030059030000921000c143c03141199400e0142840c0983e200c030007041468010002034903c4116240c0450506c0c1008000081d1900201c1c504681641c0101c03141060318100d00c0c0c0c003500500b20104c0303079103540222054600c0744141c41e1513a9882c0a0160720072401030090040c00c1c80142c4c1c980c031040e0741c1540d09035441c02400d902040444041000c4000f8581070f05031810a9034030b0100d9965040b84a03410101c0d05541803142d1941c2c60f0704001080204500621243c142850303500300348000002c201801d407042410303120704081c4007400c051080c06000e560b15032003155007131508030349401d9031038901141b1803031401b9200d004003192849240a040d0b404000340c200000c2d40c0942000c54030403064100142e41175030651900480e5140040c00d2001d8400c10040d55510000545400e01c10351510654014000080d0032080c2480200c80d8084510740d807100a0350004941c21046 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 862990890 1250 862989640 862989653
    0x405010f0c110d1a09070b0a030f1401031410060807030b06010203120f06150f07020411070804032f0907050a0e0405090d020f060f1f090e070513090506060607 70
    0x8a011050388400002049000c2005400e502121310509071040c0300d031640c48040d21641d8200c1d50140750300008041c040080030710702c0f80d0400131105448407000b003000b52107003024400c0560f080e0000c5400c2840715034001c01c80c6108000b041501c441700b50703090140600d001d21303c5031680141d00000e00a041c0d0040090001e0b4002c00480d080d055445002000600d854007240ca0400300c180c4d5054401c0020304080701001140364162410150b102d0307844d528010069080000400c1c52064030b1b88205018882c0f04082842403001e0f000a5004080902c101000d140c000c00d001c10890044240900c40305103da030352a101e1080300d56000481d8100b40f42e852300103040589240c0301c804000f0303078400c1c04d000070085950004904040c0d400807540880c0d01c004403409117a522000c0881d014141482c400700000c00c0c800c0100c1c4101e410703aa66480d5041c0303060319150694182e031400c0002d26442c0d030007808104602e00349a141c07103500d40c0c1141e04c01c01050050f40c0d0390342d484810180c04288900e00c042090b2091102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 862992140 1250 862990890 862990913
    0x170106031d0a060c02060601050a080112050f1b041506120b01030f09060605030c010503091c030f0f0b01081605120a150815090d090506030723070b0a020405010f0c 72
    0x5050449400c141245014000b40c448901130030014024040800e407154045c60a803034a4071415182d8440380da0070518031928592410700300f511075101d00340c19418041400d01414200d00001800310400003039103803e0005881e034404c0401c0f511900400100044c0f50f0002d201d80005900d04d40c04216031610800480181030344201030054607142250200030882c00780c1c03242c0110b0f08281c0030b0ba01c6602d4010019506400202d0f0000386940208401c130303190303854124012490b81c115003000100710017007015040c103c40440c060b0b224440e030f449034000102d68000c10300350746c043e844031450904607100707400c0100540030703003004100100030703900c0031951107060780d00049c101503000d60409611640d00d0755265640e042c01200740c040344046401255030020b002ca00a04024070544404646624100501805500c001c01c84400c220210b16694915138007900000880683c8500703150f154a42410400d80480025080d03139801481003000300810f907040141154800c0060a0403110042181000d00c103814 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 862993390 1250 862992140 862992191
    0x2060d091b0303021627020706050408040602010b0d200d0609050d09170d0f2102030114090f0720030f03040303060e040b0f0a0f020d1a0117010603 65
    0x10484180c04030780e0280040700c0c0007100c2c0a9800c076150b011100d0181e201c2c160090080f07140443e02c0f8464020200682c074007816a03070550100041c41d101d00c90703c551085032403c0d03400b00ca5015001a0401000e81c0c240202c2c62003000482e0b0311003a07140c207070395990300a808000d02170b00124900d1541e501e41d0350b504440441c40c00d4022030140041d00c094030f0420348901c0c0c0000541d0104844a002240405d030845c00035174020f00399801482c0320100000182d41100c0040051b50400a95901c005030813a520b00a2401110b0b50780b0015031a94101a00000640c00042416001e0340598040020708583c000701d5582203490344c01d00039507003c04280941c10384200c8a0900c0070324400019a1521941101c00a6202c0d03070003a0760070058aa1200030491070b4030019600902a180f5040c00310712540218001d20b41c015001100014421152011030f4007641c000780c180b000761716510340d580181c0700c0c51640f4000740c81100340380c58003803800d10010391108290f040c05403508050351742640b0f03454821580d0030501c1c5e08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 862994640 1250 862993390 862993403
    0xb0c070203011a09130308220807050d031113092a0206090607090825320f011d010c0c1410020d0207120203070308070b100f060c02060d09 61
    0x781803c8000c0300c0042c50080c0040d0240e4201c00000c4d032031000400f04200e085030300d545e60340480c1e20351500d040380812169600f103024400c2445804d0000f10b10b14000e2401612600140211614150029007200d4941c0842c0d034207100c04101246040b8102200361080c0c41915000103104035941140c40c030000c1507800c00d00c88901036201180e99a40d00010403174402c2000a08130f42466540c68021190002c052003809032a6000c0740102921451069502d40f400d41c02d10868064156510481024685541c0807044c02d00701c00c100d5614074940125181e01c582c03030180d5447e10346074150340c00244507000000540301c800c58032a08401c0385a104031052004070b41c03c02c10301000240c035114500800700480703a031244103116802054400038000f140b8020500702903005885050f2500181e240400140ca5013281c1c03500400002000252200c00a003051a00039501c5614520b4114101c24018103180c01c0788100da413510604102c0c480e07001803004402039054451039140c001c80ac2d24240507011440008080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 862995890 1250 862994640 862994651
    0x703080708040311031203151207090b09090c0114071a07080f1807050f1302120402031e0606150d09050d02010f0605090601050a0504080a08090f0613030b0c07020301 73
    0x80c094004090010f0b24081d0480800c02409102007568603078910310103554001c0d00f40001100b4000709407000e0100e07034000d489015084841c0c3c222600340200c5402ca030010f10380e20f00011403903090920310345034015070560003040ba08407600f0000c0c24030400800e40e4000d9040008040b402c01c1100780d40903105003801a880502d43c10000c1c4040e05200c42150f03c1d04148a85c800000d201d4010114501013040b4500c0290200c1414107007440813000c0344601d071039040501d59448005030704441c8010018020308005d148140d042c284101414040900c5100341c081244005421014001044442e004107048031211b44c014112a02003401e070040340b1005694a2800411500748240810400c81d04800d5034020050300015140000840305a400f07a660410100c1c00011200c0d4080d030002d2001c203256007001303400c0503510360f4850301d072041c170f1001118060300110701c08102c0d080010060000180440d90355050403840323141003602509610014111b4010030f07001c01d010000b4807044071940340d0090002e018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 862997140 1250 862995890 862995893
    0x11030a120f141806092206050111030a080a0f0902060c1f091104050919051c030203010b0d110c03131d09060f06010207051f020606010203040f0902070507030807 71
    0x4000c1259025001041c05842c0c0561101c1111085440e000041800e1000382500307541406100d0b0032024403140c204241c030742d694000c920360401c40040007080c0781000c81c105041c00d0006050807109030781801c7d40d900074400030404941214545510805004002640309501e90160b0040c02c801c40c4007035006070000079443d101c0900410891703800700c54070100b00039241882e1055001c41d000140c002d0282e550044640c034403441c09401070740d0415445000c03625406140b034281510b04054a608076a1980100d80c0b05440c68032010859480c40103e050460642d031500a5480003403013004194110300d45c0d12031001a5002d41c41064540d00704e01c0704126903e07100030030032100024045019110034070314010790031020401c0f0050700d14454002c44016000c5c50300e030713010000004035015041c207040d8021418080f8260720345442000303c59030301c105041014001e00d07202071308040b005441c090442d0001c0209001c041c601c0101c90084890b83e03413005949100e04d0a2603800e00c440c98100820b480c41c0040c1000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 862998390 1250 862997140 862997147
    0xc081315140415030213080f030c0c040212040201230a0302040609050a030210050f040306141f0e0c07030306050a17060c0723030909090d020f060103020d11030a12 72
    0x9103400025100d60284409a80d0380c000303540610721802c100307803079010701034076400e03200e07402624004040c68403600f0126101c0004070305010359090100e00c070b6800424503100a560802005490b02030665045140021180c2450b60708600100064148507058190003c038003081c000c50000010308904c4640c403100c04120003000b030342c0544034401c0003c08401001c22280380aa6030340048070b038010810a00140620b4042c0c445421030040400c2010b000d00001000c0343d4140101a0081c0d0f04031050455444e002c0d03d5115045401c030f0312407020b200070100510480191845860700b1012161246489121524084020301101e8009075040304180c0c0000407001c1c0c1070712090241640d48000e5854a079034225681006004140d4003815000506060079102c0300100040c8101c400101b003a81c0c5404c0c85080402d4440006942c40d04050b8071065a001d103091703061054604030701440d8003628143d45141c00240e21312041c03040140400f000c08402007007a035030030051151000c0d444202c80709801450100034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 862999640 1250 862998390 862998419
    0x60c0405240d05150f150301090903090f060f09080c0108010e09010e0703050d022406060a091d090f010908120a0b030a08070c0f03030c060b280f0e0f070c0813 70
    0x185d003c2c180341761800400c1c1c0f401c281094514661240d205046a1901007031a0141c49030010941c03c2c080311300d0001c142c90640104450240800e500c50701040ca0210700002c000131080e41c041e030380c01d8100b441d40341c86c1d5a81c0100c201e41150024000d07038900e41c44849940d0b004012460038442c1512170428000100000459210304503c02c0d6005c1e00d6a0100f4a8410000000501880098544903800141180c944800500b800c1641490100e11803a16071120034803800450300520b6a1210100c104500a8802c01801403902030300002440850441c1e070740c00d0358038042d0035095900c40c004440040c0305a40542e101c0848140d0040840d00503540c2420204d650398018417051311401ca0204e00881d41c40003915038941141d5040d520300c80312640d1504d0754030043ca01c030605180d2002e1302c0381903000c1c48496070414682c005406080715a12600c0c10001400680b41e0364410442e0002c10420085d00c0c40c0499080d5074410760798103000501244070f1800003520301c101281c0070b29000603410045480b283c040c140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 863000890 1250 862999640 862999681
    0xf04021209100c140c0109150509010b0f011202030c0c07060807030c0c1502031b040b040f090c170901060506070b01092a050a020a021203030702060c0405240d05 71
    0xe96080c01a42e140100c203595500e044032000c1000100342030600c140c80c0b001000101100000040e018160740c3c0d80441c0541115a140d400c01e45450603c18400303001e1151020102084580c3d1008408120001c0d11401c901c060034010b26501000046071440394404451590030014203413030502c2d48941c0d019108680a4612000191a044544082030b02420585440da90411800004003000c6804c2c1c4000e944020407000a440c195920710f264100400e001e0809841c40c0c403603081e20303030b420034203111034005266110098060a0089000c1b099400c080c101184035000140c00440d650384240aa000d0701c40d95020b19045200050000103014101d501c0b181698020641400000d25156030703203490f480780c03080149038282c4009000070303014000c0c001011800d103e401503075818050768002521100c19420310180c00e4200004000005074140a02a4005013035801e0a08141c248004141c1104540c1e50156411140d01140d071102622001602e40030184d11800b44154607181c1c01d14450030035800d04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 863002140 1250 863000890 863000893
    0x610050f03101d04020a030f0609062c01140403030209030a0c032618060903010b0a091409030f0f0313060f0606020c15031303170106030203010e160804020f0f04021209 74
    0x40800300f50540404090040d40c0040200c4102070447c2c44d0301140c1c01183c501159801e50380c0a0400000d02c0f58055980341c81607944045100404c410f9218024590315142e03001664035010840306241e1101e000190820342525005849800e204082860040d44c044050038030452800d0000c1000b007c1006034007640784260700c0e4190724203500ea500c001c0e4000c0c25107007000c18000822190b81303400c00a014140340b040060012551400d50030104480c51415048640000d4070790301c0e84001d00740301495890f0080d503100d00075403500c4a0300d0700702c008a0044052100001c171001020407a03800c420415640320f2604490700300314041c030b4500d0460050400f82b20b0344000d0302846042240b945080e8103880a890034610b015807540d5030b0242142c1c8900c1d0001e82c12000d0003109a01c010310700505401c22400f0f800907490040c1d9a5041007828030003144020455a02c032010321008088150340000c909401c40d505845002c03100504a0006100482003114560460720200710200c0380d40c144103030680141e10700d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 863003390 1250 863002140 863002169
    0xe0a0b0d1e0207050d0504050315101205060f060f0a090222060c02030c0402093015090f03190e0a0510050a090506071e050c0402131d040b0610050f0310 67
    0x3c0d41078031980a1f501c101c03540b641100d0102000034150fa00b030b96078880c3e2852118401305844583d04a0184510386090b10603500c0041004115281616813540110003160694049000d41c00040c1c01140c9500888000340d4000c20000d480035991a200d010f0740491011000710f0701e480b0b00004080404c4140c0c181e100f407245000c0a2a41e0a1610880e02e80f00405014038004420f40001c040400300c02507605a400c2ca52203140d140c0c600e0082c02031200d0a1f0b800700c00d081003030400c0d41200b0b244c05420408c1200c26041048070b03172002c18000980f0728050031241401242d082000300007403407043d15988015000841c0b502001511580400208551300e0f40b81c039000c01141e100c0c0b0a02801c1d005110340284000d0000118007071010494204050003031007130049880e110440c0001c0350580e0048008542c1c07152404006110520100e00484e5030030343c540c0070310a80c910309500c9484501c000600018001c0300602a501c41c1144510116407000440e407841c50341c1e03824401c8459081d0201d0b44036403000d004051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 863004640 1250 863003390 863003413
    0x5060c0c150c030105061b010212011e0837051c0201052e0f0b0a0314040c090c02120310050406050a1521050f07030c0e0a0b0d1e020705 60
    0x1d481403801121000c2c603040c156801c041c107000d015803110b503d5142140f040d60403015014000d000801c6000c03205001803141d03514061790a403070301064154034290758501a03024031030060001203c02070380d0089001001801802290414444000a180d118809400f0300351000d200001500704082d003002810400141080c1d5070803802c0341c0c019243c0391041e190b260281000c0c5245c0d80044484026a50519241580d440380411940c0c6600e13130200040c41c10101e070000c21584c05200f81c451408800c200104186001c1d90f03a045000303400c2c000c90309015944c3c0c5a00a00900c20064030030b91200c0002d802d503880c01c00d001200191070345446168801e03810201c011669080c0054030500700d9002d1280540d007010b0501d801d5600880410009007c0c03600c01c8041c0080c4034041c000c10780076541c58801040907041202c8003d00342e8046911040074000c03034411305001a02c5900c68901244c03000001c0545440f4038425100181c44c4154103442ea00c81d00e01038925903082503070f00034030342c00c0e1040d81142e4498101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 863005890 1250 863004640 863004673
    0xc030a02030a021212130603060b07030c150605030a0501020415050406120e2d0105071407020d06090606060206010e01060f0504170708060a02090117010b0304020d0f05060c0c 77
    0x12500000e4064101c100040c0c01803c140c0c071500c2e84001e44000380c0c1c15100c0070400780c9581e6040a0f840307009156420400300017042d0984522005480780ca80842d240120b6030701c0280007038001d40001410030814801e103d440b07400d154031060203043c00400303a13009944c2505000e070103500103000795205840041180c00744eaa004404440880e0401d4a5030742803501e612074000000d10514001e2107950196000c000400c0701a1264941201d80307000310184001c0c1d0480355942100d8005001000303002001801c00d4100403914140e0f0b0a095045602440c3c881e0070786460300c0070f0812201d00502c182e04015020440b25004076029058400c0417002441036a81d40d00112811064101c030170010450402c1b05001e1902da00240524018101c01201d805c40d50350320545240c60402c8a980c000039901080f203e14942c0d0050341030003044080305043c038442d410201c0c6100d044c1710140c0f000344a0003140c040c1004008595003550080b40e0130030103503011807a00c450280040d500140e003102584c0582990000007096 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 863007140 1250 863005890 863005903
    0x810021c06060206130f0b0f041a06010e1507061506080a0506060a2f030d0f0b030d0c02150a021506030f0715020a1b060923221a030c03 60
    0xb2503000300820b03203864440c0858201c3d00f200c00d0300d4055004040101081711651100e0041e035180010880c1e40c5450304050010524040b50700310400312000610105030380c00003801c0035a0f031b011245000c14625000d2054454401c0a20080c02542440403094249820510a01c12103180da25a10103c1d91a41d880d901218021240c0d41c1d4018414801101d01d10700c41c6110b06900f5185400745140440c11218080805010b4014505954000604090540a140030382400c0d41c00c005418403003d01c010707001a882e0b00b405da8007601000740788032104085d550b0301351a400100300850712071a40c0e040f94810094607000d1850030310403080e1103400070400f1410001070401c0b8040d900d10140c950241405014010741c0b424542c510218455000b5400111350b030303455021f0341014440700c40c02025281880c0500790300312903801403039007080d5007030b01384e41035040211740c06e00d05039049039003608211401d100519040140440d80406619000080007444401120040c038900220201c1e4100c03604081010794906 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 863008390 1250 863007140 863007149
    0x9050d02250e10050d0b0a150317030a09021f091a070f050c0319050f030c1209041508010c03060801150902032526061c0303060810021c06 61
    0x5903032a410005450000c0d07a550300103181d8515030f60300c0b640e030314005480710040c1841a110400c0c603600f4002074482ea031180507072002520030410306080c0341d51a901400c142000401182060000010308842c02540c050881c041c0e009181c000507182104001d4808151001c0d00004901c0c2001c01180e41d07000c400745002e0780c4140c82c51140ca0507000d651440001c503007441c4211020703c22025102c503603542c140200b888004020f8a200b903429103600300310f4030307103608030700060159001004840794a49e4041600034104102001c4907644903161404070b4000c180c0300e4001e181c2d2030f1580c003001c21403c10640203205025601e07682846201d0b00d0f542c2113401c0318102c4004601c02c8010680800c001d56032074001c2d50784806550203503a040c1480d81440400681c54a13107000024a8000d089041007024140390400c0b41c0b4040d114100c039140c04000b2031640301900000308d1a1a1520429408140c8203401c000042c003602e500341c03400074010801000180d009002682c2048600b040038802d03ca403903104420448 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 863009640 1250 863008390 863008453
    0x3090a12080a1512080a030f1e06050f0f0108071b0309181103070f1e081f06090303050705100f020301080c060c060403030513080307021006120b06010513080109050d02 74
    0x1300d60740d00c02ca43d44502503007000e15488805100c034135485e52160000718180e0005801200c03040e00c5010007100c050780c01c01c03441405465107030400c984071852402c0c03c01000b800d10060075114080c0503181c0000340c0c4100c01010580c181711904041c0d202c4040c0086440c0a10000d43c0031103070519010640c1e090078002e05104d5014000104441d11034100d15440c10414184041011003d001c64620703000d0507070310a0040340d0014140802c22100c0c00160100b49400c0c0c00d2640d845040410082c90b90009210180070488042044400c0c0311042c072507107820b58030f00341c0104035010001c8400400303900b007407196035203500078080c030a070741c506050b81183c5141040308041e0074146d486540541c01080c028100a1421000c000e0f05800603200c50010340c00f480c010f40003040303010400c043c50000ea45d015000f2074200c2c0408401c4100050700000719940080003424001e8403031007032909040c1c06c09080e9000036002d42c01c02c40c04800f0b0002c08107120003210426402c1e04e5500e5017002845c44400000130420011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 863010890 1250 863009640 863009669
    0x4030c020a0b09130513150501050a0e09060103020d11030d020d080a2c01020705160f2112030b1c061a0307060e01090b04410603090a12080a15 63
    0x500d42c03652160f9840324000341b14440c0422a5101c908903d003020104085080d43c41300140024501345200800402d1165044001407900d01540c64642d041840020f00440c0540b110f841040000d031b0301c01229040250450f688150206e0000756100e4016041001040384000420250031301809035803d59140c600004205540101c441040038420211500c8a035601340103a500048091064500380e40114002c48240c0381065204040751070a5400000c1c0c1c02d5500c081d002203400207020030a05550800055a0350724031001d000e501505031300303600d558408610fa10981060b0720b8039000004160107120200000e00c905803404030320310303211101c00b54564007190040160354414184c0703a071208818036140840d135540d2209040c0980068202219a140750156080d1a800704842c1200c130015070150920030300300c0744510300c0341e4114001400b80142030000024640c05001c0043e080803ea1000001e011010f103000018802942541c000300c50600700b110340302c24805a0850001612001a5161034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 863012140 1250 863010890 863010919
    0x30a0506191707030f0803070e100c03081f0b1804060608012d061e2c180405030c0613020609040507030b040e030a030b011403010e13050604030c020a0b09 68
    0x907044800c80c01c21607640704502002c4000380219290845c0180b0814000751241006080508072001ca4840d0701d00030215010001011544010154041b039018281810b42e03071078ac00b107100c3c403400480045c802c0d000300c14800010203034042001001e260090204c14005c0a50754410070054500c2441030b000054440c0d401440010b1070420b14034000d68a199048501c4848100011070795081648683e0202d04110b0009451020305150840450864604010743e01c040d00c120813032803800ba0b171004c2580140030011045a451b10640300a0114000040350a10703d080c0c82c0c865a6a0300240780361039503000b16070209130f81c096508a10000164010500c078104a141400d00c0000e0030003c11080c1015121070b070340815911244100c40c0240d001402031665425008400303425550342104950400040c0041e002200d6a4003041c0c0341510341c8072244a110361281101c15030804000358000d00306005800174481055005848103090034800c1c0c540700d9445581e4880401a4011080f4854020801c44203040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 863013390 1250 863012140 863012159
    0x31109040507110d0f0e03240a060e04080301030303111c1a0409030e041a130f0e03210c04030b3103020f160303090e0426030a050619 59
    0x95018501c0e19020b88a0950407058a14018a41d90b404c80860303c24036049107126408030032003030010015001441c4954240c59501807652803a22100062a001e83c04100f64a52640100300184425145001e031410103040080aa0303000b0301c0100d02003860f00301220405403100d015074030414189030784084d0b01801c0050b40c00241201070f0403103002414200c60500e0035a900d1040089082c000d590740800c8189140c188000c552890000d8924030000f103407a00780c2d42e52000c4071580381c042d41001c0812a0b2410741d02101c040c1071544c41089050101007040324405401c000301d0208502261002c12507922403800400c01c6106501000c0c0c0044052000181441c0d503000310101070003d5014841c01c20658100c00120001424000b00c2c01608114090f8042650400c04400c4041010b145803001514541d0080c1030b604c5e45108220800002500103414400c103620214400c000c4045040c1d0114048984011190710894580129600e0000461001c1c1440840301c0c1d001408a114142d540c0d003041c4812 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 863014640 1250 863013390 863013401
    0x80919082503080c0a0302061012020d15061e0506120a090c03020a090e010506031b0907020106090f0902010305100e0c070507151707020609060103080a0c1a1603110904 74
    0x1140604261100100040403c0001c0c40c1c00d24520340a0802c1040510303009081c40c0c0068003a050354900040144080280c60145945680e81140e03092013100072441d040542010b01101d4114041c580703400000d4030000390301c040e1078483c440407505c0c003810345503010000b1030300a00301210f4142286d440014408241a4041c010890068825040c003c0c2e83c0d0780041c120281315000000d03050f840e8080c1c2c1240240901aa682101046000e4492161712510450300000d0701410345200b181d803000800e218500079400507000d040c442da000e00640300004510005007a120030103d00092504000510038591102444140e946070741c4909036a442da4070301000c1a40007484196041e0052200c0000c00c90701c840c088944441c015190b212641e605030b0104e1000c0c0e14002c00c00c90564000c101040100e4902103225819298405600340e1036101d98182110000c0060000a1500301892078030202c690454820f00c2c86030051081c86801200d80e05400c80c155816040e0601207500e00340041d800c40d15140e08103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 863015890 1250 863014640 863014693
    0xf01060f2412090f1b14030c09040305091201231e07031a0306011e0b0703050702010503100806100e0903071a04050a021e01080c0a0804060b150708091908 68
    0x101d094544090319500c1d034818101d001017801504c404c00401c40d1010100b401c03240c03194120302600c2c6402454001c6082c612008000030104071001961008603544c10b00c3c13099465111800802c0b00300a411f17101010204040440c2c3c480343c1c2c0705000070b070f4404441e03100444214860020341425403a101b8041d809407042d01242c901c43c10101c2d0050003151803c0010f10300900e4585444c040d0402c000c01d460a5000b920740003425021420810840482e80150444642070384c20700c1d1203583c03a56641c4806c1406035050b000100340b802170500f84907141440401e120300750713038020100c01416260f03000300315682d10500b20b00030080070030010002c203804007410240346e0160040d001e0700d00081f19607002610710b0a801d01804904440e42c0402407095900045481e480b210415140c1d240840c1c50038003070030a600042c401001070340c4500d0455001e03103a40728480f0504e4a035000703031601c40d44185000300460700400c10340d9010f503058142c1070741c583c50b050b1694000c036180302001c2e0007003100100410503416000c402c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 863017140 1250 863015890 863015903
    0x50c04210c080d1d03060f0118020412060902041a0f01111002030412030c090e0105040e012004031406040c1e0b0403080306270604020703020f01060f241209 69
    0x4001800300003030104500504182e07442c0c103500048200051200e0b038113030181034001c0c0d201204001c2e80c0400d50303170301c141034540c90030b011402c0c50800044200070384150703002007140040c0505034804101268000301d400c0d500c00c64040c0002c51241407201c590003683c3d0410786e1311040800010400e54040d41c140c0304200004000d5805000071a2182d0302a42d1027907408458250240729007141541d81071140116a940b00d1600f40c480600d00004561024818081c3d94411030340d40c2890782a8040035030104c140c18000d01d140e80d5000c0d0702c20304070361a9a04144415580102225440b10401c800414801d124540c001c4400503060706056a4070100c110684a00807020f01469005c134030414001c01401c02144100503550741d0345401c03401d114100560900c462036109800d500c1f0f40c10b2811140c14035600160035500103882d2091410101d140c07644540b0302180651900b03c0105d00880c4e020b04a100b81c880c2c8049080b214280403200d00402c2429081d04400140d0065100c1c1007840c19400844519000c0c2c82d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 863018390 1250 863017140 863017163
    0x29040c050d060305030415050a022d0610090c052106010c0c0b13050405090d0311040506160c05011704021e040507030f18081e04080a03030b04050c0421 67
    0x71040b1616500f007aa169400441c01700210526010703000c03103503011440e1050820403c0f400c0a550b07035803400795a04c00e16103510880882011b2203c2d8140d0340e101074000b01e5411781064850720ba40c155040c0118401d03582444000c2000714003d000b01d44901d40d65480030508045c0d4011401d000380c00140c0041d040182ca11a81300c04280420b034494060031f100440503955400c140382d603d80d808156440f40380a58100010030100900100300a403080741c1500740800c20b0394103000d01d0003844c8a81d030449a8461408904400c00540d440d500c448030754842c0500700030141c1c4840040da1604040e0902c92428852400001e0040c1003505140b400030749408501d006000c020b038005020341c0c5003203644600090351a00c00003100319881c040d004e05d441010a05010081d05038441c82143d209494003208921205d00c41c09159044003c1154018010030042d10200030081c50001d01500d01c0904941c45281400081018030080d0000c0b030741207030030b040031002d4803e14010b0801c5070010001d10569050040c0e0703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 863019640 1250 863018390 863018407
    0x1508062d0a020a120b0105120a0609110d050a02120a0b0103060306090f030e0a0b040603110d1d0706140a030c0c0b070e0909060c0f0d060b180429040c05 67
    0x95500e030041140d1a40036842e01d25090000301002003028030801d070f0600305520350000340d8105040302c050311201328108119030b80d035035007000c007508050380131920b0107260911000350354040002078004800985802c0c44103445901d15001a40145095030700f02c109808049046414103070301016603010181004181d1565a40b52541204e081d120160307045003030341c00b98130704255001c00031040008046420f11560f5003000c80c0680302d8001d5000307c4007415540c1c3d00c80180142d008050300c15250640700240640200c0c1c1d8071a09480601c8144400c035441944804141e06020f200e50004d456039112100b410f1444941e0300710080c052220504050000707840003180461440d500c0390f40724407041d0316030780c007078103100000e000c1c1c4908000c1604800c0d4014070148011000600101d9003000c0c40410201c2e1117a00d1024203400606c0e89030700001c2040341c0011a8000d00e03040e0703090008021002c540c104000c070340740ca112500003002c941d405219900341c800380011070300e070135408141c0d44421440c2560800c42d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 863020890 1250 863019640 863019721
    0x308030a0f0c091511070503060a0912030e030a0806010318120207050402070f0204111308010506101b1203021303061a1c0803060607150906150806 65
    0x3560a034424079195010344008a101e4080d04441d07500a00d041c2074694039009846401138500310400c01000a0000789600c404403c0004102030007004042d07414a00f011000ea034002c01903d101115a50005070400c80c00303900900c40c1c0f00703003611711001541c81c0002119040310940b00c01080903062540e03845c1890120001903005107a002d100f00070540020040c102c000c1e01e010141c3d400107218500420070040040c05414446103060343c151008203181d008118841210f004024440704150340e404000103a100e01504a207008400c01c0d5480d014a030032030350048404020448140c91b0700001241e603100080c03001224466502001d00e0010b0800701e80514194085449501c1a502541c03500340014103580340d0001700c0c1d4841400c40c0c0c940c43c10ba00c00b500c5401000c11141c006001c416020000034810741302c5400f252965980a4620300c100025141e48400504c2c01c2c000c142c9055103002403100c3c4d54046004c03810142d40440c0014501581c0320300c000e0000060300c1d1810211714031342038520a4401003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 863022140 1250 863020890 863020897
    0x4080307090b1b01150f09021809090304030606060f080f0a02091c06111215030312090a0b0105101211040b03130b060603010518040c030212071e210302070308 70
    0x58010410400c8010340f624103003900c05040407000c03180c0180b07004220450140c08440e00702c1d40344040168035a0f030400911021903040d07209040d00411820b0402c082c0c500080001c00550b44600810804203484650494036110302142890200e1003003000b007440311920004580d408440c1080141c0b510300b6040101b010810411132400c0c2011440100d542004031a000303000c01403520000c40c905012070040104200c0c41c0241c40c1c2c80b41541c00b0000b1202d07545007442210600c402c0d1070854a080c2c100b091215503151741403c0103554100c0481c00204091404e101e080081740600c2e42c0e440400746e11400328000508490141e104545002c000025090384014042e41c42108103042d040c0507041c0c54100b10001c4030004044500c141c4013000180080c1d51104e103448522801e0b0001120a641d60f4038041ba0f0708200740c0c001a42c80361074a00c1c1c0f18241d1000141c1c0905917001215800d00d1261641044c4074130700304900030380e03049403918402e031507001d60801d018518160203031040320744041c2d032900c45440b0342d403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 863023390 1250 863022140 863022157
    0x61b02030a02060f0c09150d060b070b09160501111905030a080112150522080405010f031a090606130807150804020f091f0b0325050304080307090b 65
    0x30808211503030310380c0c0c06104003030340040084800f00705031400aa0b15405071290b69202c038425100c141e00e41540c00401000d9a0b51880790300d000700036154440c1800345490f082510115803241d08180014220407020400b6220f513940307000070180d402d040400558086c001421413054501c0780309805540310215000711250780b405000910f40e28209244020640c1c0c034143c01c03034101d0a45a074500d900003010381441048100010b1000035032074847d484e2010304408110b54060034040d28046190610031800c1c001c1045a03026214052095001c0f0313415020349456a00c526400b50103010401150b007000d40145030b20074001000706140040110841501c0d00042d0041c4081e980459004d206e056100c403c10003400c1041e040800061a1a43c00a01103084048425020700354040c0131400a601c0a0340003288038040400c0c450090361500c42d405455001102c41d2101030315990982a803008800ca270034980c0d00401ea50b0140345543d17944490119a1014207494100000601d000800282c20f401605064 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 863024640 1250 863023390 863023393
    0x3010f14010303140708041806080a0c05030709110412080708040f05010806182806120c0509160f0915020f1c020718020903030708120c090d0609061b02 67
    0x95046080040210302d4004d40d10002e00380403c1041c0108805005035402c80780d00320071034649091000300c80005085a035014104910981d000e400c20040c12038203800a0310020303010cc1d80c0490f030b50103182d407c0d1510b503032441450800400080c460a0688032141c02c80c58000c840083c54081c007603450709500d43c0268401c1e0031189000d00306001e1907038042c0d4210f07013040c812500b041107840c291385100240300001d02200025500c003101c207504000c0c034160840405050b21810841150343e002250806401c080c021140f500903100041183d240c8100281e0203503042c0c0346085900c0f481c41070f0681c0c03051040080e000910086c00000183e0060b2071844441320390840c0c0c0540428a45148000d01c5c1c01b5001000c4000c0d4410701c60448411076000601101b1034550b4110003022036810b0b000c04000384102c40e40c503034040c000003440c0d0007800032140040c8072450303806c0c050300510343d00e800d4017040c1b5010b1030220311f5202c0b607108000804038003950081d007000c501983d40010b4015408100307070403d00e40208002d015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 863025890 1250 863024640 863024681
    0x2030c1209030d060614220e0106030b030c0d0b0f0c0706110403051006141c08280206090307030c060209090916050108060303030112140f16060203131403010f 70
    0x4000c0f150003880020f0040c0c0c01c0800c03c0401000700905107020301101960200c05020b0381c3c0d41485000344003580144901113000820303584a07180100a015121750702400b034480e101a608541c1012400c000b0603542101c80440541c13500310084080382000791602c407142000340304020100715544155440c0500000e112603403a8a149407060510513115040e00201d031400d5402c0080400c0d04c1d007094440801114400205820780801440c010809940038000003008038869501c12400e00d5030700e04800e03001c845a40c0c082204501203a4951080364000040d410511882e40000e0148000450407449018054140861440481c0c0002d108a424580c81c1d40002040b00c1521404105040500420b01c0c0c994114545900800e13030303d21061042000c50a41d0561100c00e012011441d01600030012054a205c601c602d59243e603a140011200e50844180785070004080d80000200e0728215102003405030020325003400580c04944092007190107541341c000c8641c2ca51464800c9620a103007002d0140720303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 863027140 1250 863025890 863025907
    0x51204050406050f101101270c0b0703050f0912190212070803030c091c0c0e01060e0f042a08010e070e0607080703030902091305010b011b02010302030c120903 70
    0xb074074090f0340018012502e081c04c1d824540c07901c40d410511350609062144440e4910340e01c6500400b000d05590a410a0241103200080c4960048554541c0281d41904884e9120112694540304456008010035410401415580586000740c00324030001060080502c501512580c1031260442031400c044040d0707144881140380c5110081045d218600007000b100d41030980c0e9aa4038440a007041000c0030300800c404403555031700200c900c5c60401c0094801e5108200e032900010030705850055040c91500800003090841c0300d16420003204070b0050003e500c0c003544a050100410700340c200511a1000304002c0d020a04000d108542d140c83e4039941c010441d803505586100060028011034108601d0110003103403a40c514041d50441504403240e00e48c1d500d001d24094006041c01580203421028210800c03035680111180740382402d000b4402804050381d164011142d6000101080301c104050700800360140d40310758081c0d60302460000d005840c01c90401a0604044ca04070389a58841d07000084014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 863028390 1250 863027140 863027149
    0x7060c050a080c10051b1804090f0c0e0603010524010207081207060609020f0304140a0f14060a0504021c0c05041d070801180602090609040c0801050307121a06010c05120405 76
    0x55001c005800c9200080740c24041e00b031194403a140c0801100b0f07a55101fa0783e403a50740c3e0f5008800c495800152003401c0000c0c0d242035801c2020a02c00c1e101e4562204000544e641018000d10b03100e00d40c00200e500c00d41901040b407071074060740a10494118820747c10040f69042042000c05058100001c070141c9900351890400c080d503ca58000c60b00c000c1c018410500c1124810b010b59030400d42c0201400b10342042040c1041c0341450484003c1c0402eaa10f0400c841404904035001407a40500029603100341e4070384040344240c900540e0001d4015081210041c60000c42c05a040441441280b04c440040d40c3c440c001800d0701c0d40182100c903905c3c1c0340c4440280040040180300010100f01c030003880044987c84526651404108001d4030050700003901c2d000c55540e41d01107030b9160a0080c03003046103441c0000e00511611090040ca402841203e41c082828000c000d00045455408201da40409402d9001c00d84196030141c10b1034144082081103400003442400030307101201646055903110340c540010030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 863029640 1250 863028390 863028401
    0x10b040f151a0307050306060f0406181509031202010b030106030b07170112110a050306190c1d130b1005030406140702030d0903090b070615140307060c050a080c10 72
    0x24811220420b03040d114400c00101900d901c0030ba94109140c03640d40e0500400c8980c45462041400c003200010701103200f0f5003214050700341100704d905a8000b1a200d114020380251401d03411070108180940400004200032040c00182c0000d10021549a10746004207003500c01d6078000312000e80080c010000000d601c0741100004500d400181c086c2035161150a90014004000c090b0000059030404065501c4a40c0c01c10000c04024080b00d0381450110015244403550f1000120b9650426040540c500d10032044001d48036450020320704071a20440c20000c101c000c2c80c0e04040c000b51600001d240355900c60b1100c0d80c1014942c0c545907030f203203000d18201c0208c8000d507508222050b090000d021400d5800400d68580c2c4003260300000d4044003609056030f02c4281c650045946040014000e41045519000782c4603409600041c8c503801602c48080c0c00d800d0000b010b90942540c0140400c20001e0300c076064012034103000e6001d41d0b0310803040d0b803502240e6500c440d00000540c2c1c0301d404640e88411262044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 863030890 1250 863029640 863029649
    0x924061802120717070c170f130e0c040b13050a15020f011e0914010f0207150606171b030f0403020607181a040b04060c0b1005030309060309010b040f15 67
    0x5130071044408803181c00c00c1d0081c1044041002d1000941c04000e4001000e00300d8082c1e081c0542d88a1804014406140d03100e05010a0b010100c000d00160343e814055200d405086030914003424079042c2200507a09070410850b1044504240304001141e8a07820498406041c020b0840742507a0110344020703181903240100103140c0d0703241204001030282c640c1444080004904000305410009060112280c80d5a0031114000e51a0500f01610310000f1ba0080c45400d104043d68800541d40c858084103c0d00144074a07404034882c0c43c85440c0c80301c1001107403940031004094000021011a01480383ca402c22a0341d24900101c80040c0300a0540412240380d2110051418000018039400030340344e0380307107030b4850058a4180c0100c6a0b48083c0080151400740c0700b110341031034a1329516800107100d5882c640d000e035072243c1000045501407640d62502d005075a8003600851402c0148014404a5400246204603a558400480c0200d549901401d03a000c054084046074a814070030800080040c613612 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 863032140 1250 863030890 863030897
    0xa0e0718050f0111100c05031605250c0306180b06030307050a060f1d01150503030a020a1b240f0c0c0e09030403080d1a010309240618021207 62
    0x3010440c039520704241d64035108080c42d201c14840c0c2c80d4025286011303800038100040c14141203000e2401d5900c140950301c00da51a0145c985180c9140100f61824403452080da9000e0070030807c07260080f078010002c0c0e21518800d20600c000d40383d1700d07100d9404403002d1250703010503001c00c46142c00c2071240c1c4e0100950401406c50140d45400c0d40c0d540c0301e540d902100700008203800d442ea6003c81c0009110b40c000310340580740e02c00f001c40d601022800380c0e0007480034017221a4102e101e000d020909040010664581c0f0840d03400500054541c0e03190fa0301081c1d070b81f141c044014403c154001c207900182c180d044c4214481d04d007900c4c400180001c0060f101c240011074880c10000303128890000700d04641d24a200301c078401040441030b0b44482d00d0440c11482542c0020701004000245021411038903841a414029031900010744140345000440581c1c50700b04c130203003d20240c04080e000010802c60040014030100c6070010f0026502c490403c15003031040d00303035812135501145c1249646600c804141c7c0c090b8083c45c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 863033390 1250 863032140 863032187
    0x27010e06031c0203070605090c03030d0e10051603090c1a1306020d05090d1401142d0c0313140a02010e0a080303070503071404030c060e01090806180703020a0e07 71
    0x42c8003d590340985003018009036150408122682d50038400c2c21140741d0090103070b03a0380d03910460110000d455080c241062502c120001e070004c200680c840d090140404010a010301040c0c03940031805800c061406907041126031303a0010741040c1031000c00441344407203000c0645402e00b00513050b41551860b03001d4410764016426000728190300004032030b05290700311000c410070750041c1001002c2c91010700800b4240d45c84c058030200c50285500000f4840c10100d44954010b010003921016a105031685518000107580701158584103084091940300303940700d20800d01c00f0703095160320f0549403894174031002d2908015401025940e111000c01e0040c4801d988654406103407118155880c030008200d10704001002c400306150f0b5110301c01490020b04900200c94566480c1d040100f40ea0405205200c0400c204544403a080e501911500003180c0c000e130301416803075694000e1014000403000c0b02c5801030050044c044016556503204401400d602000242c031490400c80140400c0e00300c40c0d40d070b030f00000303a40c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 863034640 1250 863033390 863033443
    0x10020601080c010c11090c071e020d0b0a090203060a0515150d0c0c08120703050901231807091422110a180504021507030207030227010e0603 62
    0xd07100e01601400e1911541425407030610380ba0151010160b9584411b403902844071400b030074030150045500440c03c02d0004d11006241040000708218029000803480081c42d01140c8183e01c01940b1030100c450200303411201e580028180801240e0120003da507032000c0c0414031725003502940c8411001d6078040100141110b030b10016016104030003000c240c9540074202d003540f0902c030002e00c5030b5100d40d804d6103408031a4541c840c508000c4400c2400603141c14001100103c1c140690310183c0220b08883c805511149108410000020013007000c120920303488048080003081000300601d480380b00010303400501c003d44403c1c040060701101280c0d12080303c1a0000d40c000183e07042c1160302c038030074900ca00100300125050f55040d5200c000d03d02c0d0f608100c5032080c507182c0c03c49445141700f15021a0005080c0d10201e0050152322000f4006074040c50b8184014107180041400c2c40300080320b046c2000a80c4105030b40c400c00c3c00d0b00104025070300c610501229080800011000d01c044203e00b00892105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 863035890 1250 863034640 863034643
    0x30d081f0303080f18060109140a090201210e031303060b09040302030a0305070909090303090512160321020301031a0c120f041109270a0b06010f02190b061002060108 73
    0x2d0070041303900390600f01103648030000d0100c021480500505851003980d442040034018495101c100403c0c040902c0000c2e203038080c0c1c0c4102117640c2e60585800c500090041e014699184175003400350140d03992900d511045003030405c09002e1030410440c1d1107034180e06616100c02599480c1c0401401000c50100b4000065008400c0e100a88414a400116652207060440b40c0403403642c40300365400d251103140e0040c103034190450f001c001d0003282241d21403014410181803d22400c050b1904003c04c02c0c0c20680024410204681c604110400c80c0314420b152201c41005c03640283d1085401c0000b0b065446040d4541c600c070140d11081c10070340c00f410414140c2d0b80e03900003030780184000701005484001600b04403520007040c0504e40c0c090504070151a0883e154200b0806202c440f554030705080103020740c3c00100103407075410142d01405041e540d450b080011340d00842204038080650103542c00300c5c2e0484600130b940b072224900481400040b0b017007210070b00c02d24401a00b880003c54000b8401480203640 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 863037140 1250 863035890 863035907
    0x40515270601050d14010e04120c020303040506090d060f0b310b010c1b050112090c29030f0402040509010b0102120307030905030c060702010c08041106030a0b030d081f0303 76
    0x282803c00c60b55a0240e00d4858004040d00d00d044a440f09100c400440d900c41510f038580d20407485003412642400074139105454015500e5000bc1d890362003004103210905041000e080103a201400c1605422455560641941c000d034400b46c0905540f01c01604880c9040b011451040380413070028150940305000c00003d00c8500411320201603220210f00105034418500e0000301a084440001004842d1003007001c2a882845600d001a44090301e5040381511880b6004425034007041100c3d07680e1900201d0000701c0b200440c14400661030518081300d0742d50040c001c52107040a0381d8200765610b0103104000031540d0140c003207182c50f0315200f074440c91a60005045881200301542d599103983e15103000714050102c1c2000149140004144000e10000c001580323070140c0d14a40080c0804a034505040354801800c5801411406868010302d0300c900f4032500031504001d011202150303141290000c213151190046080300041d00350801c109258024410714000d0f0130720316142d10880e41c910b4400a01982c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 863038390 1250 863037140 863037151
    0x121106070803040b19021903060803040b0d2d2304020906010c0819090e2802090d080703051e03090d0818010903050403060c09062106030204051527 65
    0xc20880440c1e203902035400415240010b8003000d47d5900c09800c011801c0c0e802d44030400000c02d041c01000704050300c020041d2015078960039007040c205049807810340040c1c112000e07450030000c11a01c045540b50035619540e143d485080c4004610810124400c8441096a40040082101640038800140d950513512900000300340390200c503180030780c24900780034840c070b0244403400da0712140040c0034107400c910340800b01c5000d080303003d001ea9107221030080d400c10220844541c0e0120021844102c84865010780807405020703102001020660b514501c080d03001c035000f079000c51000b00d8210f0f403a44503d01902e101c0b0b51110143ca08505011480030742d02c40b00d600282080c8034205c000180e440a4122201d624158458000e2110130f00750f08020300564041d0005854907030908410102150181114130f003210040d5403400354854101c0b54400e40a1903888109c100c0c103469800000140c0c1d00c600500e8000c0041e0140311040c002564104011007c00007410341c1d2180d0b81c443c00390340c0318506400055014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 863039640 1250 863038390 863038403
    0x30721020f10080910091e110603090a030e030c181803070b0609070c0309060f0c0b0f01080d05090117060103021c1a011701121707230118080c150112110607080304 72
    0x87c0080c80c154031041d0b480684107400c140040304020184c54001801801140a0303240e00300880030203410b058403a40f4480c4030640144040b00da040c00d9400d1512415804885600083ca400107400d5200d030956105032000e440340f550b440d051145518110340d00541010290a05040600c10340c2e401802202861103940c06000080c02c4c09101c150140e1b00000101c0da01071206082441d00c0c208a41c5410000c0c01010303454810b01088090b054051001c903101143c05858030014102a504036035a0604000e01260405400303120b070f00c20702c0c0410b8411300822400c400c8049690400540705112008000c0d51540c10011070800d035540c951500310216040d03032144079040020203441c1c18030880e1412806940c180003040080d40000b8010078032400404c0c00c100140c111050020b030103c0301d099610b4810404003105084000b0000240ba880041c031086068000b40e41c1440045c0c001ca6003045400d80c070410103290f00176140b0381004803c1c110103080d0700e03007260101d042211a4894026900000b0802040b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 863040890 1250 863039640 863039693
    0xb071115090102130305071a0c0627010c0c03260f100305030a09050405010f031a07230c060c0a140c15010b0d050105030721020f1008091009 62
    0x14000c3d011100014428002500c04981e45c0c5401940c40c412442400021130154224280c100f1a000403a401c02c052640201050b0f11038107800072a000000414502e00d03030f1036200b0302002d03120030f004002c0012000d41b41c46024000c0b600b000b905071940036030040c01c401c10035194010750035100c00c010764102d401110a02c42075510001440c407801c58036000604640302c00300e4140c1303401d94031562550503640195014003040c0d90750300340001001c0d0380380402805011140280c0000c4000c0303490381540654a450481c3c0c030070500c00d84502d000c104c9064100880f2600040031803070354504001568000100c190500c0c582900694001c2403200b5071007019000410028004240072800c0000c2056803840d403c00050303959651204000c154450000302c00d0581c14200001800d140100c4e14500320358000060b43c114400724940c1c95049080c3c1001203034080f1030225403100640351500d82003030b0b8000c1c1d500c842c8101c1c24100d03205c40c500005d1840800c04030303051403281000034130918440750b000050040441503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 863042140 1250 863040890 863040901
    0x40b090c07140a0b040c0f060c0b040b0601030906181a1605220b041d150d06150308220308070201142701031112060603072003070b071115 61
    0x100000418013800802441d0b00f44410303c2510305d46d134422160100c500c5001b0341d680309410360f42c0300f8010501801400c024400580400c02040407075900940502d40003444800755503460003103500004a040120000d080030344c0c04c1040e0304401010488031038100c0c8800c0d1038000350345984c24018030b541904114001ca410b5130011008074541160380c50304004030720711a03145d05962000e5081071141c81c1009040411258000d80c08001d42802104c03c0000170384940f1000f400d000041c01e00150480b061b070f648171802c1031104181c14007440554410070329240c1d08c0072091030149081e500711261001c5800415002c00000e8086412500540e60a0800032034500510125040d9401003071500c20269030b0300c10392a1610076100242e40200300302624104000c545d01c0706001da943c000e8100105c08090310802081c65403030400d0145511035220301d0a001380c103400140c4008800c000080301c21031170740080f80200c00c001c800805951300011700d240655104200356002c40d5903c106010b0445030b2000d60000c600e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 863043390 1250 863042140 863042143
    0x2180607080d0b120d02010902180712022110031424131a06010f020106180b060702130e060106050a0c1103120a0c0605090303010f270614040b090c0714 67
    0x218522044005c0c0ca04104443c400603000e0404c03454224841c000485a07203d14009440300340c0c0c01280103039074080e605901002250025801403085144074284041000003150101a942e440354104401e20440300740741d460a035001c403024040709515a04000000309010341e2440308050002c08042080e54191250200c00c1d40721030240e82e0241550021403441080742c100044003d0260313000f81d80c1d408048440706812401c81d44a80030341c00000c90301620180ca4452a03800c415000c410060441d45494803690005019054010303001040546841590748503060501403140140407a08069142403040c400c0103100905840d8014556500210500e02c542c404101e0825402ca0290549030740e4007070703003030007800084121004545540c1000d000444000021050b41c1c100e5881d00034a1107030500301030a440c2e4460f86214880003c01e600441141c440105002e41c600601c2402007840643c55503105100640364104d6400d0302805145085c8020440d494048070441070300842c0e10039004050203c140e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 863044640 1250 863043390 863043409
    0x60f070807030e1003200a1b08040e13050d030212040b13050d0512100e0403140d0501030c140a03210c0501050907050102071d0103300302180607080d0b 67
    0x544c0c101d5220002c00c101d41d600343c0d00102c40b4a0182d140c0038a1044001551880780c8580e2111100103280a0000c0c1c0c0391070030014030b0340c030405d03c0391072550b00301500d880c40c00d141290102da00d240d14107000020300052290a202084400c013407840c00354507000e4407000640ca142ca006d07100130101c242d40000504802819902c0110b4140c0c440700b80c42000c03c03001001049a041240b8019207031203843c02140c000804c005500048580c1d01074860101c0e61551000d544164a03202c40d903050080401202c0e6074460180324550103507120b655403035107541c1401801c02d28812100002030158100c044284080740c2500c10300e80321072790580d0b24410749941040381200c0c1840400e00c000d00c03541c05c05080c400c440300f020401200b0b5078401e07800c0317404190780c4a0701941c110240b80760310f11030821000014004204001c06000070b0303916160b4481d12000700041070100e104032503c0c03041d000036070124400c004442d00030307032101296800b02c3d011800e01480391142c00181c070440510038100d5917940740c010884e03102c10029 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 863045890 1250 863044640 863044667
    0x1030b130201050c0d021e060603060406050402210a21020a11031006030b010503012a0810120c03031103090a1401170412020606100804120e0a080f010b060f07080703 73
    0x1035405c014080c2002958038960503c0b2004203d504161540c520341300050404c0c85100020028074143c0c489464140003400041d06c1079800440000d480001804820f624900500140000f4030382003405041841c40318008070542d2116403001c002076018107500180c40003035503406c4414019030a0f07000000902d4103020201c0340c10303918103080c1c00000340400c2000b036034100d81044c1c0003400f6070a01200c0c1500700010052800c00c43d680c1454682110501c580702070b035480662010400000b5803142c107048800441603074110351a05000b034050007055032000c00c220387e0302c51500040d41007501840004003071004a0040c02c00541c9111001d100c9684a400721191044034800c2003000d60030316040a0281c0c0b43d10b01b10142c0503119000c0480c21a040040100d550308241e40d59005490301c0d07540c1c40d800d82e269101c4680041040c0000803c4c01540c4c0d00071110000c2011030b00900c3d250b40401400d5007907a0100104501c03440c4240005a01e2038814401c455a141c2d120b01d0581d45e4000d146030649401003580b06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 863047140 1250 863045890 863045893
    0x5090601081f0803030a06080721020a1206090c0609060905120c0d140c0a14130b1c06200307230a0c031b02030709091a10050a060801030b130201050c 66
    0x4000a4900f008030046010301352800d41444001c0d04c0e41e400554a01d018071034024102003021100849943c984101c004061004024050307451366400700c0c0002c0d903501001516919910000c86042014504202c00280b85a00f05201410f1401001a01505040c85071500508140e030001c0c02c013400074081140d9254000300900480c1c0020704110b643c0c0d800440554420b0700c10070004407249d26107070341c2c00b40031501d0210140310082418070500005507000456035100704d841b112030014a0395014580d0807004190170455000b4103150134064103440d101c034080320f03044d48000340008100c0410401c4a03880002414a07510030b1036440c03405165507589084030802c6100205014503101d81c4031941109030742c001e0380c0e41201040c590309803041c0840c40c0140290315a0252000b0008414650800012036001d110040780900354105080d2846000b20740c841c840f071032041c1d001d00c42483c0c001c3d0381f503000e08818988103c156040d03030f66412050401034502e410031800300003c00708580c896070803900c01040c41e00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 863048390 1250 863047140 863047201
    0x2090a09081b0609061806010504091415090d0302090306072709060e220b100e04050304081c0801120c0503010207060509060a09150507140c060105090c03010509060108 74
    0x84041e103c0c02d080d5000040390081001040c005d2944100308542c1c40307034050150038640d207082e0800c40241151002100d03d8220a42c498149400030f02c641d0b02c0188007022020950b103003145085080014040b038080c01d0610501c000047c503100003407000d50041d00c60402039807044045142030021b00d00201111111842078601003001300e4075402c1841141c41040ca486104d4a44540030308a42c0d062040b0f4071401c440b03c0500b400030900210800e504030150740c40503261940c60305810151102d0032101a5200d80c40050100451078007004528001804e00d00a0b610010518030000c1c164241131007102184500310890201380001d1040050051000400840d6150000d281440c0901004c45007c1403500464000541c00c410310301540e0300032580801e03100654811507038180000c04010300090300300024a2814603164071701500402c0e50750141030050580e90b140404010041d6402802c0692070401440100030680701c1c103100307a4200c8402d00f010040d59031a0034401a4125021004a20320308030308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 863049640 1250 863048390 863048437
    0x2120408070302060711030909070909181203060b040315021b0c090f2a091903061a061209010e06160e12060105120a0807060f0b090402090a0908 64
    0x240040403028403a400b070b1810741e6990581a202406d218491034503d8004200c1c0e6130984c6410201c40e5800758850410405081d15803210500712a6000741511640200c3e00d01041423106600604440c40098503080c80241e0401c212a4450b0185110090660003540c0040410086a4055840422010340002e0700d8904074114255101c0c01012080d029040d142d001c24941040280940d1082e8000700002d500500002c00e0f0f8011743c8000320600c0c2105034140710400041e501c0d80700400c1220142e0344441004c5046040c0302c401c444020011555801c00d17085603100946a00381540c0549580b00ca48400560751804218058541010201c00a004160400107003045074100300d07001c2c2c2140d546400c07649840400703000d05081211080d03501a84080b0042005240c407050b20351000c0c0d041c40542d410300e5619510800306400420742290300b41d807a4505012801803521800d882d29030111903030320103800c040d00803070760050000c0c0c0303511a00d680724a10201440a0603044580c1440d0641a00b0840700e801c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 863050890 1250 863049640 863049653
    0x1e150f12030318061d071512060b0408010203040c0b09180c1b010e0c0607022b05011b030b0609010c0813080a060c0e01050705330f10090e0a0213021204 67
    0x40e000c170b501030a4240310454001040019104040d6010001800c108140c0c0d4007003a1060140d000da08038050352569004500d1250b0480980f00400325003001680b28205481c0008404c4255040550148010f2042d04215683c02403181ca02c0804000c4000c09505c44501000091040c2d50340c61005042001d8a03001180055001e0b1311126210000d849030f5080c5241080710901c5001001380d0b02100920001004031494461603c0080084140d109001c01c10b95032682920703180c0145c0090203002ea084501000e815000e0460b039040100c4025203081c030000d00280400c2450f6001410100700401d041141e203000c445003a000d060fa00003100c800303080514004014020310036900340040d10b10240080d4550151040c2c810065200018204540510090800400010001e044900701c0440840366140c03144001034001c909140c030021103440c1c90540901c040d042075001c141071501d01100c60b40e48800102d035545905034116000028180f5120300140a030252004000415100d81e0610080048 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 863052140 1250 863050890 863050901
    0x905010201061d0a0b0607150603050d0f0c0b06061b03180a05030a03050c0c0402030f06150a090527070c0c0f030f03051c1e150f1203031806 62
    0x4264000e001258603207062201d8811290040c1c0c4030388002e00049610482150416045c842001e4441c908120058031014000070121850b050b0b482d5a484050042c01001e20100f0400e500c507050502c1004001c0c0c600034201c0c03122907030103000c5215000100f141caa465004803804282c03600070032600341d42807006451711f960144141035901c580c00124400e80742810801c4404403000100504949440c98805039900d03402010841c001e80203804181449c1d075143e1010703500401c6491b444d0440351070b020342844141090354881021004060110500d4550300204500640d1000c1e2031040c52000040180f07003058501c410000304500740102000402c81d409070000e1030302d6010f00000c8260039030302c0d05250400095400094020450a4204404a8002c0c4010b02c410301c90018012718010300300035048100d464841c41001d0030540d40618040c1e442803400340030200080c81030030144551802c5d001c0d180c0004184500f084101c1c4501010081c11f000e5803029a580140403440c2c0c40041e6503141ca07400400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 863053390 1250 863052140 863052149
    0xb0409180305091002010f0911011106040506070c0c0b040b2a1b0118060905030c030c030d0c0c090203152803030809030c0102040b130e0717190c09 65
    0x6190005150640c0120212809815010340300d091030890400180030101150f001540103564860a1082c0f0000c020f1041c8030070702e8050280d103640300b443d000004104261451030310382d8030341c050014000030030008070320036810540c241041380e2210b10526003c80111010390081210400105000810101da90300918410b05841e001c210051150241d000800503107403850507050303101030b201c080d810f07440074540003c7d4601410902c01031002d0a01d580904c00301c035001200003c004141c00c100506040200395041c40044018000b000c0c0680d001c00d582d0100a6000410403582805d218148289100f0b030324003520ac0d2842c15580c034a400f09600c40c866107059002030144040042400354408031018900109840702d164881c0f083c40e64170200e5203210b0150604a40b03000804c01580310480910040009000448403903840703100710090b40d0001d03080c603404900d0603003100741046080380d4401c5030035912804c0703040a252640c840c0d00340f13400001c541010040490789010322102110f50800c2450080b076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 863054640 1250 863053390 863053409
    0x3140d06080a110a0e010312121d07060801090b0306060f040e0a0506070806010f1707091707091808120a090204060602100501090b030c041107080f070c080114070509010201090209010b04 82
    0x5940d29180c1c00004c070b40904c8050032802c8d0b500c4000d03007414401c5000026034a05200e01043e400e4a112000c0d100081542c13044a190780284400c004158202026500504494604000218050000c20303281c0c00021307c980c0c440d0000c1561842c3c03ea599501c5070a80056290071160019041c0c41d2040d900e88080d106080440d011400040c030381c0d8413030841100304d500a5500d982c0d8820081c440c40519481c0a00b0b1402400f28800021458140e0700c540464400e00e014014007680f4134000083c0205e030b0303444988440400041002d6004114070f10103c0742881c01e001003003941d5544407243d644c0208803a013402503005007005800202d0660000d4511314076181040c0c1000b150b41da8520080445200700b1070290503420403ca034040c9403410340d218240c80c1400d8071051f49007424503030314031040e0391000302c010a0b40740c0c020400303809010040130403001521408008200142d4852200c296a0ba002043e61041010000781c0f01c126900c03e401907004c1a034050310070a081e58480e0003c0d2034075042800380030307603a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 863055890 1250 863054640 863054659
    0x5010b030d170601020a12021f02040f0b0d020903030a030603061d12070807051603030f050c070b03130209010305010f0b010e0906060a18030807030806090403140d06080a11 76
    0x94500819080240074640e1a0b0118200d248440c0b50842e0400401aa0560089400781d10100c1d06408404e5030fa611994090441c400400f84900344100e0200e0f9841c1c1d9080c41888148007a02c210741200040e540300d00051a01c0d91038121b074160103071080304181905400f0118507068655019001401602c1c81480c003031001d030511803040003c0301c4050303c504d6600e0b03100d1590b500c00e542d035180040c0702c0d1134011030120b403501d0141c0d02c586181c94001002203a0b00f95406604006060744068001043d0040b49092464840e103003882c1503540d10180103411200000001080b0f907031743c14400380e1441d00d80c0500035400c99039503410168000c209a9001548640c2411b0510200750b11a15500c81480001411004170341c8a0405000040d00885582028451007400d403011142070f143d50400118480c0d0100c556a03030380c0f4a030040003070030b000d04040d028007514401c0c4400a0341104a42c04a00c0d0b00b242201d403580e4800d000003000e00201ea22140c0c2d10300038007201005008460103001300d00030065880840 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 863057140 1250 863055890 863055911
    0x106030b060612150f0a0e01060e090906014b05040e071809050615040c03020405091506190c0606050904150506010c230606030c030c040905031e070501 67
    0x52090b2050003c1d80281e110001e6801c4034107405000c0b80d020041e22090a800200000c05c500180c40e811404040c10050b00400259902509482c40500144c40444e10342c20004015651964180a940c7c0340d14981507101d280070702e802c1c11291482010308c8902c620440c9962403041c16203d40c08140042e2042c402c1c0200306400c260058184c0c031160400205240d0340b6001c14603c84207240c1d2030081071161541c1080c1c003c6003040100701c0c0195404d01d800c03e540706d4503800300710440e511030f80600240b42c0144400c020b182d0746d64400740d40c0441c8000786128a0f40e580c40025000b441510110b40545d4159240d0991030741d4840c1e405003045100e8101005010b40b900100904c01c0c00882d0f0040011480890104000b0456041641c1000060410740d801d14001e540d00c6c140d00c0c0010702000d600c0300322028213494140040203039070b80024003900070b4110b800c1444046a12115200b08107070055860704071010400104104541b120741d082d40030403246264003003001242da841898140d40355800c2406001c9c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 863058390 1250 863057140 863057149
    0x5010b190f0c150e0d090905060415210c06020f10021603050d2c10063204090606050a06030203010b03010509040827101b0b0907170106030b06 63
    0x6030105081c1c0c44218810b105951804040e000200030b40e58070307035143c400030070642c1c00805c030138010780f20240c039420701c018200300d01e0204654000701810710950410691404d624074180c5003074140c2d29640f085c6844204802900403d03c0120b000041c642c030445c04001594590100b20060140005e006550300710003448806003c0e4003408140c074800c0348502e203541300024081d90007000e502c10340c2c201c0425013180c0141c4500007031364203010882045950440703140c0d59200921080b030000c031181004200c1c80d82410324441ca800c10310990480350b615017400c0c4e2560880c00181c94525508001c106004481042c0342c843c0240407c0e20a2901461700c0d810041010360003802528140d0f00b440d0b0055003960318000400c41085406802035901001c00c00c02c3c8003401181000381c0c9061840050581202c800c0e103800d0002415121b4103010820404065551400c0b0402581040c0240c00c0000010300b62111401141860000e5210300084600d2448107444808190882c9080b640139107001800b640d00c0c0000e02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 863059640 1250 863058390 863058407
    0xb010207080601140103020a170f06120d020c0105031512070602010e031c0b060f0d05060909070e0a050402010e030d020604120c0201051624050103050705030a051506060d05010b19 79
    0xa0301001c1e240403101e216940b20f1f40c040c0c1000030240c034001c048800b408030850050401640c485441c0680d4600300015420846a08031b0110801c0001b00503007420064004c1d15020901192410800c001022869290020001c1801620020070b10000e0885a200103a80c6030b9031441148003550030322184208006c03004c4292503a1a034064005255180c002d00c164004010188007250303c400c00f406015400c00e08003024160074020154000b500d405d0107000c004000310010034034019548062130501c440e100c0b1003d07440c0c0113800c144002c9040d0f140d610059943c0111264a1a0984554044081c006038002183c5005a0040080c0501801c0d4110122101c00044c00040d01082c8104080410304140d03c610b02c0e4103038082c0f03036040d040d2040c030031580b49052a1104000009a140c03070040c400e00c941840701d0b500408048000317201e44845541c03101d440340c1c000600c0c0700445180c0300020f030716500c0391811642d50944141c410001582c5480b2801c0b9150060400f00c2c420301d0980e041c0006050041004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 863060890 1250 863059640 863059649
    0xf090a02011d0103020f041202010909060602070605090d0b09060f011409060d06060e0c0a1103041d15040915050601170a0b0415091b080402130c020c0a03060b010207080601 76
    0x20380401200c00c450344804540202d66150425900b003010b8803001d0500b0010380301812859401014842a900004201043c5a007242c03400038078055041202540000d5800c0c00c50303180c2e0030400d4807080d032200040c2d444000b5600140c689003200040011481002c20364500c1000714121458640e40c8480644098000c4410103e03040381480e000310b1002c0c03829080303013201e4900c601001302c1c2003512034104480b00c0c101034960054902c008205050665080b8603081034050baa00011810b1034a0407004004c44940c0e040e18608c800c1000c40417425030f0b6001000c0d48034904028105100360003aa00d46464089451040c04201910b460701060082d171050b10200b4081c402a00000706980ba003098540c010181070540b203a00c01c0d524030748500280341201e0844000d00a52a0004040e081001e40d040a0200b0352190020418404200b0005941d070311101c2400c0b0020003c0016a10f2a444040e40b51400045c1c1032940100106000002c00000c0d41169001d10401c0e401c0c1d0301c0c0640c0d00c0c00103d960781d000380503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 863062140 1250 863060890 863060897
    0x90109030e04021b0f070602070e06031e070306020a051c0c0e0103020a090e010305060108010510150e0103063f02030a0b10030b0406060602240601081803120f090a0201 74
    0x21807041c1c1c0c0c9800c0d00a0078220010580720600e45250010851412a660548402540014108210f9140c050016000904040c5401501403a0200000742c80d44101c20451016200712008860704442c104800005150320081c00c550302c014103040507160750448109035586c0c414460021000c11510b0190b985201142c3d00c4880190f0100001500650094550707402003284201d0001440880021882d00840c011005840700e941030100c0107080d217078020b103071031032840030100304106414071840100d030040c00a103000c0300f015004900407009455542d11038245240e00d82a5284007000301001e03040c00045a9000340520072000000b1082440141d601039450781051003180d010440c21030002d0b60000c14001002c40b810344a0341c54040c0c61100b51030540e03072165a148280025030f0104800102582e19001101c003d204581c01441c91820003800e0b40c1c1000910710201c0e0511904205101e0600110404d89440e140e4130807085401a400700e45002c2c1030503803038020a052600208440c02455010ba5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 863063390 1250 863062140 863062157
    0xe0d0e030d0c0b04170f0417010f09031b0503040e01080d02062d0a0e0a1b050303074412061525020d060903080703060b04122904020909010903 63
    0x440d0144030802000200e0385c0308101300490086282c90600030005482140800c544001c40361000b2821076007000714007000f0901d405a4200421740140800c0005a090680744030054110f146c81410b6005641c0000e008046070740c00801c590314040381e1203103110103982c02c8483da0380d1425100540c0411061000c8011112400a030520510034020b459114010308004107100303140c034030b6a51519048003020f039040410101101e17143c5400e1a010070080904030021401e184007500e425400c400403518105c60008a4544241c4005201c00050f14160303140c0c00c040405150f0304110380f901e17030059a00c0002c0d0b968000005e0868a4007070000018140c03000496410031400c08251108080c1c003000302c8040040d112030343c0d00143d980070b0b0b04030000e070712501010828031402d2602816900d030140c401028142045004d03c14006d9180a54049403124070404450011a0070300c009600140042c041e103911500c1c002e901b40c0c07196860340d24010ba200741c0d2402c29960705c00b0041d030308941c41d081000b40000e0011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 863064640 1250 863063390 863063393
    0x61b09090e07150e090a0b061207020a05070f09180f0807020127060e0607031d0111060f010611030705151e100503060a0c09180e0d0e030d0c0b04 64
    0xe40c800c180c10200c4070304441186440b0304071200c00c552051503c1d80050f0b60002140c05070704080c02180d400c50904a820f00645801d08006103140c007465449442500b16407001403443c5200f0060f2180058024040c0c07985035803142d81d02e14200c0c4460059891560511815402c40e010318402e0600003a00b0645007180240343d0f81c0ca00400798405042a4100400690b000065041700003141c60340f1020038800c080141d2038100064100e00015035041d10451041c020f140200b0382101e0007003107401624016104400c401070068590f81d140801c288014810141001100001c407064a4180c1e0416100d4070035410032511f03160b989104d0741c40020656045146481d051102c40d400c5140c02a82c0407004501049003844040c9041c40c0880720040c41c1000100c081000e41420301c0b01640144100320184007602c00c0103005840464188903641514020151464110000c0e0f8003001001d210748050321100c0884000040800d5142001d05200707000e001d81c0d20564038080c400780c034135480d808031a100190342c65 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 863065890 1250 863064640 863064659
    0x10e061e0112060b0901060216120213050703020d0f05061c030903080c120f0d1406220207050304030b16030c0e09040501091202101b0503010e070e0a060903061b09 72
    0x48000c1100c0b884d4440601c04103590b107444100c3e019040355802401030002d01e17103801d074211240d07030f002000d889904100ca07405601c0e0b9181c1600804104680440c10392039080e0100c00030311403040e40d008010700c0c020645100c1c0008be04502c0c010b680c226200000e030080044140700d15064210002c01080c07a0031404c1000540f0707080a0150340f0141c40955400480b1040307403200641c0729042100c1e1a070350008100581070f4003486480c1d846000314840140615102010614246402103800c828004001d1071141d410001d404580c4055480010b03a51142e07948e02c1c0c41d1034072000c2940d1480000404c00b03a08449140320344076540c1801c000f595569050011b210500455010203402658195250740a40000c9983c00c103000b8124005a40284040c4045030621021100394181102002000034682d00503a0b61000035641564030244980b1440d4030b076184d0980b1940c40d50070040303030401c04018000500c607420010510441303010b030700c091000100c000a00005540d080d070001d008561816400d201c83d200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 863067140 1250 863065890 863065919
    0x1030b0a0317090310060806190b0d14010e0c06090618040f090506010902070312091a0c0a200c040b18070f080c0a0801143c010507030203090409080702090702010e061e01 75
    0x1c0c9c040700000c1464182d4045800318034210310a65051020342141d10802c1024801c801d0000d43c440701030f102c5802034100182491141c84030b000c1c4101c60200b40100f01540844440c015a20000c00c1088041a84001d40c00585a29001a1901e004503130000882807003d0084400040d030540e01c850017201c13140c0e04000209030340c0c0c100b61034444080041c0044044001a01809181046052920750341f003076800801350070407040030042c001032850301030080304c00009240d200d414089401003507142890003c00c03480d0300b44110700d610208c8860140000c0540082c1d40c07510700c031565950388075150b03210054107145129400c0780000103986800100501e03c02d1218000e83d1900051400d4881c01c00312070309002d0b07490240c1c04a0441c4018035030707a0300016092940100354074800c0c20007900b408082e85000c0e45a00504009074090f07178840e141102004010b0046131065903004101000e90300700640000d00070240604445a07070312991010a10a8400c43d900a804207110051224140e00b030402040a151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 863068390 1250 863067140 863067181
    0x106080c0301030b07112b0f0212030a150e0a0b0108150405090102090d240509033a05071d030703171e0717030c04030201030b0a0317090310060806 65
    0x1c44001421b58080050001406d6240a05c0c0011031a4810090302050300f010300b170020080c000c0c900c00c0710001640100d03182c2c080c03a082082003516559000f01c2100500000903107582440c035602000301c0c9a13404603200c0c500983d0784030400c201d104004001500c0c07500040d21038040c10141600c4008a61500d0b800403030740b011080300090b051101c100d012580c40e0000765002c42c0e0040c403c0c0001ca022232410020b0f00025200700300309100e141414901d1548903c5800f05150f242d1100140028810200846540c0624001c40c1d01c1d102045040282c000208002e588500c0000c03d80180c48213101c2110000c00d408040c001c0180102a2941c0c0d2410341d840516800800d414800780002d43d0141741ca80302200e8403020000c462640c40b000340c07030102c2d0350317044605900384040018800d2100c10203c00e4140c50079aa8207090009804030518000346080390140d20080586204051440e0f0b40898039003d4903280c00d0550807109680c1020003c1401d90300940104011a030005002444000c000e07040001c1c2c41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 863069640 1250 863068390 863068397
    0xa0314070c122a0620070b130c0f150306052206030803040b010315090c061215060203041a030103150504080c0703030203280e12101d060106080c0301030b07 69
    0x841d8a89002d0120801910031004039840751803070106100050007010340b03460304a20142c20359003142c40d1400035030145001c0a40050b41500000d0084e08823130710400c00301034120a0f0000b6081c0d80e60301050701c2c1b1285000321010b008001c204000418000c3c0503c10655000500250360000f031140b00b6440c07018800396810722103840b0074002012501c424000d50185001da00c000c5510747c110b0034004e80400310124a14030b520329003100030002c208084c0200c2c00356006403400360004101071a0b0302c000f4180e07494006090340420000051032617000001071040702c50100045402c1c00c00300c0d90b49121030100340f10142c0613000380070040300b9040f425405070364440d20075040507007841209003039245410840e400803070141e40009040211480c0040d10b9030100e1302c3c515450603140c10f00c61801841c02e899000e803640210700415281d19200018414001040c040c0c00d020003110200302c0c0350054404110103065980e008000010851034841d9105038840d0400f560003d144d6440c50760384040d0b5220040941c400c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 863070890 1250 863069640 863069657
    0x1213060e01050c101a120a1214040303050706021c0506030c04231806010b0403030e0603010b090904020418030507061a01090b0f071208090f01050613021308120a0314070c12 76
    0x2a035441050032007121032186c0050112402a10b020030500000c44004414000f00105016007030281000311416694103250036a2145510700c2d00001034044c0a2081c1c5c0c60031194181340c2d90301700071913014512802085045403128904007080c80111060141d100d691040c0b5042c3d4844440b071554503060300110000029418114100354041c200802a003008114600c005000c0082c5035100400710807120342200c606286514100d503108803071203800c40e031a01440207103001409556a680c003c801c8222065008100340d4004d260040190740191000c6400c0e0745010000400070500c890308410035801a100c0c5442d0909000e41076032290004224030030440020002080024401c408410608120b6200c0956600702011564100147c0788450b51450780341608000b01c9a86100441e041200d0303609006985603060b4106d4100c0b10f5003900b0299152094003060341c1e030401c151009010200c129175042024a081100c0d103110f58406990120010b80c81144600125081035081c03001504181080c85c130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 863072140 1250 863070890 863070941
    0x70503010e0f0708010605090105040b151b15060907050f0c030f07060f201e041509060e01020a17130612060902030f0a0e1213060e01050c10 62
    0x2922260705000c405600100c039503241e6854200554009040c0701c40003840382d9420074002c251030b62014071455101b03644490b02c0c840182c540320340c1740000400c0b050050380d81e070700502d00711203208460f0351a22242d4818140d500d4682c8121140751802241c008108800c2d6440303c840c00c5034603800c07070711880d055200e0400102000c00010002442002c190414007500d441880c2090022280c2c0f250001480364241203517107240030490b04403032060200b01c82c0c060b40c50309d025841c400011100c0c983c994280140001d13000c50401150407142e030360b198056541600e101d450740001c030f5040e1004141140541d06c101515000183c90030064008c6e50348042001d8100341035800104980501e507031044010a004414440f69241345000386000b900c10311905500d07508100d011081005001080750340c24a41d5018a0340c0149818803529100c504100c08464940b0103d4184c650341c20301c14805d501c04a1030981100c40e0550040003610003403440c50700549580c0d00d00c0310781034010b001840302c04042c100c1c00c54401031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 863073390 1250 863072140 863072143
    0x80415020403111807020d1b020301140a2003070e181009050702030c0a113c01030c0206040b060109120f1704030510020c01061a0a0201110327070503 66
    0x20350188441c0705140038094103000710b000700c80f11010940044c2c4c00410502c5900090140102c2400f40b400304118182a440c4001401801400a500d54281040390b01c0ea65a11031005008104900c0e08010392808036030440c10201181e62070006800082c40050303403087c00340102007807080001e02850a01c184850b484c0c444240704a0744420070341c18211051100c011581b280542c0301c0342500045282900c0f242c0405c0d681c0c1c40c1140020911984486505066110b0318215413502030314506a99108c20709072025400710b03e102d04c050303246c010f20212a02c95584030340641540e501c1540c015040b0f41d10395031510311031144014942814003900c8c45000414440d400d2200e841a07010b0301000129454034030304452008654000c590100005100c00e201283c408200100c0a0100c0600182c0d5a45583c02440c050031030f503440440b4000340740829045804528004244507510781e8020820060100340c40d6507e80410381d4510006602500c10031000c544017003400c01c04100341811101c2d40382d91280041e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 863074640 1250 863073390 863073397
    0x170402010912050604030e0910030b040f05120a020f03030c12040204090c1806090b031504050c030604110405060108101a091215090a170a0315030323040b03040308041502 75
    0x100c070b036a031040d0100411b240e403204180441400449114603681070888103840d5a100c1404050036448641d400320b070070060f421040500d50340d80001900c156251180c0c4151454100c1c28200c001740c011907601003601600401101d1080000c42c2e2840d0400000e10101411210010700898110b035840c0400d402140c4500c035040d00a001c041240c1c1004a10207254205030340040d03000c4240c0c54142601c060069401040d0b800309040ca0007150107203a0340700d090591905282102480d0103014600a01060010321150600200020748043c002600c03090011511441d04a03111030200440280a1205c66450451403076075510300305005040c035032020300140c0e01200045140a155014107840b82c608091010354980c040001c4000e444018103503240c03c00d02c001041c008088203000054800d508a020f036010700c00e076104400014401e60b071240740203031107070a591441c0c85000350301642408000003a48102c0d0150b8100011840c1180c84d140d405864070b52000c0d204413070880c010b50800300d49108030b00c0078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 863075890 1250 863074640 863074643
    0xe011406070b0a2301030f080304291806060102100f0b04051005031c141608031003051009020f04020a02070542190e030d0302030a061401170402010912 67
    0x394584e2000181044050350b1003110885102400100302190080040c8030520390480d21050350780c0d541303140c100c0b00140400c49141481100250101c490516203400303501c1035002c00e8181c05040c45820301c160762800c048410034010381c0940c0d95203100c1540d580000030450290340c40031807980040340c002003d584049980b000c00000300c1004104030315080044181c221806d250643c42002e49000050081081904411450800054800c87d40140c0316401341000d800520284e100e0800441280503414248019a254071445400c2808055036226003a035980d8002c14240b0003002c80c005201c041d410208101040d03000300400001e41f17817180c00303040c062810031452461482c4040c490810300e04480c00e940351840d040680c6400d0b143c40642040398000480004112007003042c00b102281d241c00034101442d0540600381075001c000d505134020398040d45450701c091004507183c5110851068a00e001c150001ea0024032400f6011141e50340325810a00601d000000c454451004050b50b03440c0110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 863077140 1250 863075890 863075911
    0x291002010f0c1d090c0d0b031204090510050a080c0103050c0d0e0304060311030f0112050c041d0105010b070b0705131a21040203101d0a060608070e010e011406070b 72
    0x6200000c0a5580b9090f4156100700c0d01c107946820a0403410300741e401a004450015503840700f29140b2a40c080282090040c4800c4415039240e03100c5c5a1040030380302c19102c2d078400418151004c11a403074121020340a80d59058005e00c4400300910046001e8200903086882d48901000003a94030301c8280284c0300b020241200031a43e40d890b02400800715803a500e1480090700c018028404a40501d000a50448a5080a00658095500340345080220f182c991951047c83c080c4403a48050340d586800340c1d4251800020400781c1c1e41d90f50500028800d10390001c100800c80000941120b0145000d0304003080104c0103a00440d0700c8280490305200810302244a19401146418800c0031040800211401d680c03004903450600e5400700b6030b11415401e1660043e80c6801da0018401c1e904000c80c1000f0710b00004885a43c4090f05000c0c0c020310050094012074002c0d42004a24a030700001c00f24101d03600400305070266880c100395020088072651226510400401810300072034200d92016026010908 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 863078390 1250 863077140 863077157
    0x12140a0305031b07052e1a0409020301180b0a060501080603060609040302070e0106020703200d1101022401030606080d02032b020d05100f060c0f03110a0302060406291002010f0c 78
    0x1544401c800548015111b81c0d0300b0003c404400710b240144403502c110090758003240703420702d602c00070f80944807420002e502501c0c20310302035051105070080365003d6840300100b00200398881c0700440c5c000500701d5a09405511900129040381404d07500540d03c540170340b0540e100700381c40d07005540b0502400e07801400103a1100c003052091000d1301d02c0ba1640c00c2290000740c15440d403400c001c55001e1404c200c001c1c01c000034808004600703074024854803544174462400302070f20483c44000010170039400e00043e1a41e51403d403000c6501032001400e918641c043d90003c3d402c08400c1c2c07405406100c2c01c00342a40c108170040b241e070341403104039002070000c3c54149174000c103007403034000383c045035842c650303070000ea80d10500c0e007008c1080c07541090340300078919080101c4a212604030b003021784120296220b986070901c01c5c0340b41d4401b8103601107980782c0030760700c1490140b148415903220750300205045843d81c2140b541146c0d4a4809180c0fa80c141a0104001d00004ca40800040b210500715614082904085240c06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 863079640 1250 863078390 863078443
    0xf0f07030c060506040902030c01031505041104080105072a02040b09070302092427181504140c0a02010f0501060e012d11070801020412140a0305031b0705 68
    0x10300800e84d00ca00305540412800001d50000f0b66220151a44581415650f01c4000e480c5082c88440340c000d00b101503c1807010103601421000168070602c1550847d51034400812803161140740c25024101c0b19800f007403500c0c0e0b0f100e0080c50031030418000880e071055480010000eaa180c03401c500b44502255140140c480c208030b803d100e02e0031142c2d40725080c03100e000304072400140b00b8003050b200803903111042181c0d00303804000519100030208007059809030f0003c0510541440c0403501910440301d8020119002c0c9504003800b0541c0c0060310362404040321400001c002103122005001103820360b100125811002e1044002100d0083e0030020000d40032402140c203a51304968854401c130a0b03501108646001c4918400d050741c10f584456007002161802c04841090070007224025142c40b00c001c65032140d54416480300130700d01050131030b030007140d4030404400c0ba80c01240144100d90541c9800d8135540d02c161079602c81c4002298a440c1c06041403102c0700204008010b1000629020001100400c01e030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 863080890 1250 863079640 863079653
    0x120041a0d1d0105130302060a0f110c1e031c0905190804060212071e0804080d0e12160308030a11040b0c010b0d050a3e0f01090b030c0f0f07030c 64
    0x101903504011000d02c800000a900148c2164400a601400194603d0003008003001d044c00d50001f800b244e0000c01c1030600e0b900082274bd0040b1212100d03001c1001951080681d032607001c2c1006111840c82c2043c40b5580039009a00705c940c60600c24010f40745075406003001c2e045840c84968042c2d4140708081130505c407283c1c04000d2000400d00c552042800d0010300e950310305142c94009503902c85110701150600410002409071800f07040148103449a0031074000e00104240e25034903426205500c01d1151444000e800f082d074045462030001000c0c001400d549840d6a95030018003001405a69820b0403001103030114098400703031011070707561952030506201890079a072004000620802c0c4000c403800000ea000902800c811fa402182190903030b0a50b40b03004810040a09440540c0142020708031407912903a40c1c0c00e0a200040f02da0b10303100f440c10001124050310741e015802e02c1030f8003080803072007514915020b42a4081d60a00843c40e00d1601910740c40c80d5000b040c0c0803000300d140560380c0001c0120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 863082140 1250 863080890 863080901
    0x220303030f06030819020a1205030f150612070e040c02010902030d030615080903190c0507080d02120c01020f04060207031713030201081503011d0120041a0d1d01 71
    0x1090001c1c0500341c00d50700d81d180305109a08841280c0d4040d21170740c0c00070a0091081b000d1042d0804821a5004000d50014006a10441e1014512005600040c20400386400c034240c0300b42010385070038240a450810420302e031001400050500001e015094030607501d03400741080209113640081034a90031481850301c0c0014880c5440241410300c0c0081c41030f032035814003001d140c1141d0725204440b42c076281052400c6104404002e00f0fa80d90300e41841c070101e07400002c4034003003520440854035010307070b101615602c0d40081c030744400c0140c00c01c0d102c002c1340c0c0790f1140c040d1012a01c00000180340040e9200c840f5120b030701951103900580c0140c68100184652500c5d0303200c07041100d4000c0c81c070700882050500b17503246903030200034107008007a80070504041f90055886c00300080500200a29100d0407419061031035401c00316030b02907003804404000040251603c0d91401c09100e01c141c140750a044104009908001000c8286442480341c2c00e011109402032596200d100005032221185070050741d0309684 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 863083390 1250 863082140 863082161
    0x60f0f060813050a03080a0609020d1b0c050303010510120e010501050a08030403111e220b0d20150d0204031101030903080a05100807080c0301180305070b070522030303 74
    0x2d580510b450042000810a901d039264180ba151003e03030b5034080d0a900505c0c0c0c0781c220803e1300b8408078440000072501d038021280d021196003114003141220030b00f290341c031142d924024420740052004100c107050080c580884030303045080c00c40c1314420402265048400001c02208030307070f44813001004a0304002e181d04026100000186160604546454820080d41c0082901400d410400101c04000301c1c036003400c045000a0140c40055201c2c0c90b81400700d103d80c0321481500345007500d008130f3b40c9040c054180312a540804404449074810188040031900410031940044d40420805214100f0900414003158403003401a01c1d2421800c01d1490a4040c000c0a4103161a01c41c8100100ba0082803040d0700c0f0341d40034000b060703c0d6549000c1405120040d4002d540601c1408004074901c90b0126008031140c1c010b4000708024006850b2280942d1055207006d004a030040240740b001c07900300d5001a51050050030700e0f0f0b140100c0d001844040c2c10810304071f100345444210060040603418012800c050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 863084640 1250 863083390 863083411
    0xf060a0b1e2a07080a1b05060c010c03151202060a03230906060d081903020412061a0418060b0324190e030a030b030c06070b04050c030106060503041104060f0f0608 72
    0x1400c24040c4c96540300350003c0500b01111301c44d240d01100620720300c0741001d0000507041c2929080d001d10307018080d25103002c151002c01c0c28000414005400c030742d03030f20044442e136a552040c08059038082c8200c3d580544031080030540ca0f40030030f458481e0344155500701e81d4441400c035401071410031841070402c04064140ca1081c40d80c5079031a40400d4010058a100403241c80100e03d0400c403445040d0000d128a91200e0041441c141d4035030300744031441c0d01025480c1007505a00e518007000104100450f0481692000100e410303405800101d0500c1c0e1041131301c8003000d0110740750046603014010007159811f410380468001902000700c004508410111107121940c4140400522880e40944034000c0300c0c5038204240c2d03108504d4049640c00c1050800810014040e82c2c0d540c011800d080300d204c50304035001d4905203d214145809030605210701d604882035555a2411b41d110b5a07038030200d03510325042c0182c1c807a4484001191450a5124070001800111101a01c551501b040a003d400004184003280c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 863085890 1250 863084640 863084653
    0x60708121b09010305150a0b0405010305130203061b090612070e030607081f1e05031e07061d1f022401090203100b030403090e0f060a0b1e2a 62
    0x1c031501d64064458224090a000c075880e0703112441c1900d000401e02007694410303c3d0f410002030640c41c0c2c00081c0151042039070140800d94540c0100790f00c40a562000a4047e07100c140010300203060040b02009001e503940e0030130310f0000340c00d000903541d03046a03842c441c880100c10144010380d50440c900a0801030140c0240240b0b1030184009420903c00420420b080f90840d4001c1c044082281c4041014100c1c059000c82030002c0c1c0301c41400c2c00a801e01505010703124400c0d16503051584000c0c20b41d21014018010030085040000449003502745c8902003019100d171408036051075072501d4a0441000a071440c6001165600c40000d02c0d041802c0c410b012541d607410410100e903c400c81030241036030503814002d80d9036150b00900c1e091099680d481210007003004002d200c101584281e00904550143c071a65041c1d444800c080c0c0703030110060b034017913a2103265080200f00c00d0200001610603d41040607106407901082e0a402c005d50110061014112054006120040030300070131582c01a80038004021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 863087140 1250 863085890 863085931
    0xa0813020a090e0a06050f070f0c0b06010e0d0f0b1f03030c021e10050307090902040e040f02040f0f020d110c1b0f0a06050d0b010503060310150506070812 68
    0x604040703400745810050301d6030026609100100a407180d010307440b0604102c18940701c20362900b000019184500024081c055401c88a803046100101040e00305001c030b203c80c0c5800c00195403002100070700507033045a0840c000041350b210507100454078020400601d0b42c0c038000580c82004510703d0303070b5082c0318800d8038001d001181e80b1810140d80b079503042d074a0031808800c50b001c071722610707400540c916845002c262041d55026030000185014000c641c1f01c81917943d885594a5050380124050700504d03004240021f008240f1610b1901320050001d03000040c5a54060b94140903070b0301c4140303012402600050030200c0040340d40b04000010503d000b4850400e20106006d40d218000222150020000c4a0340141c0a958207001144242002459148080d0307880c20058a56000044451440d9103021006a055402107007140d1050000601400000b0110812203006001e0a40714002c82403c0c1c1201003034989407203004242c054091040d00ba121a42c1d0301c0850001c807001041d0008100c0604240030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 863088390 1250 863087140 863087149
    0x71805060406150f030504140a20040603031d130c02010c020714090f090309041a13110d0c0e030109030905030f01060e0606070203190312200409021c110a081302 71
    0x54002c013891802080300c1e1903c2c1407264203503a13900300c03413801c3d0b01510500c0b0f030411819199100b0881206100722000745c0d10601000304441d210301c070203008908000710460101e0840c50b040500740c3c3d001810a00f002e440300d0456400c59210801210160b959031001901c450f804200b5007000302101c0001417072036401007000c9800340101621640e20400800c000c2484240c0a01c242c8031030b40c5001d442046600200404c515800000000080c052060719005c914034081034002c2c0400d90342c1e044050741c03034044440224401092503410702030030041488046111690280941a60507000c1c1e9500c070300580c100002c2508019000c0340c0c0011a83c9409070412003000a241c40962220045803190b440c1c440b12f0010a003804040100b0342100001500c202e000c1642000e031800f0126a40402007103280f918000a458103910528120f4000703506000c10400c80348190018210b0181c8020a02240e0403200c050605490380c0c0f946124094102096000040350310201560307015031410b074000004001600800d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 863089640 1250 863088390 863088407
    0x115090e1504051009080a121404020906010306030c0b132106020d2705011107052d030c060a1503110405270c0f120d0e0307180506040615 61
    0xa980c01c0c0201c500107010b10505211a440080650fa028482020780e450909610340c00f00c4041c40c0850900051661000d03102c0c49400c0d10f43c1d800c40c2100c41d02d51626020444000401003402d030415441e1600440040c40b10b070394560082c03010840713032a19000e11112070030f10940c0c560000000e50030712809090700c54191000c9a110150840001aa030350403d034180c00241184151843d00e030010403060150b207aa00c0d550848806000e00020882407140e46220030940c466008088d04a41c82002c1d605548d15060380c0740503942c02915882c46158010410301420f54000b00b0618016402c004200003d60701d25020f000e060b0b5020050160186045644035807210620b448228000c550300c50004070445d5040c6079a0140040b100e003c1d03c142c05041d10403543d917120070f10a00e0300501021841c072400b401c1055174210a80e038604040c0800000e58a011114004000c0303a50350705204861001680d4070a01499034211402c010021826150500030300c4151000b40d0310088145901c226a1004036a02044a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 863090890 1250 863089640 863089663
    0x714150909010b0c0a0c060f09091107060e01091a070f0e010f030e010b06180301060b03100512101406090f07050301181509050f0112051203041a01080115090e 70
    0x7040d10b45208003541440c00b041014014406c140040000c01e0482d0400d0070303043c0210003650f5080001c7c0d01c44000209803401405007884543c01804480b000407440d801007900300003010000140491103490740000700299100707a040c890041d8083c8185541e1154840302c52521038200340d002100c5030700009203e003000201312410140e50b02e503108001072080d001040c40c031070020034a0b500d45035010110003003411240342a034480c0d0f107071240015400180e182a00c1c415145412011011482c080500c0600c030884218024a40a03002c40500d280d40c40f48618405000c5051288ad41c6242580c2403051034400600880d00401303589080140c01e0f0350090880381075480c0c60381c3c4141b4860310035062001800000040f14074a2464400104028080e54042c03485100c1c42103040c0041c0e66190a40180d00440007406480768001e900c0050300101d20b03500458016205942c08440030080507c001c5035074130300303820910041c0d4540d0217203080c00b20341014900c007416045408011000e00e088405569440351003c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 863092140 1250 863090890 863090909
    0x209061201062102030106200a0f0b060406080c090406020915030c120108010b131d060412090b1e0a0e0d0501090507090b090402040b0d02060403121e020a020918071415090901 77
    0x80444456406202585010f94400500307511344040d8640f450b000bc001711400c0f40100d00d002c04c0004c80718400100500e072000007411038170b0300782c03150348484000e903102469440e00a240150001c1100c050f02e030055100700b0309a48029103929011031562600311040c2e008800c56810581078050540d01c86824071890303a25800000f810011040007000303600008410210903002c0c400401061040744882c00b079a100c8155141079846850b99250685802000005883d0002101801c2c000503504801850b4401d40d90825182690a020000e0540216540b040342c05035110000c9104100c410070004014001005091000048400100304410340041c4080c5c804c0b030312281500c40580f2540000304030180c01422596666071a4140520558920740351440001d86c50309559104090081000d11030000a60151400c001c0170b808104403800b0140c0740900b8101c941501c2c20296500308001d4004000102c152050000b000c4100003106100041d00d510b0140200600c5400d0350350f58070254159a030550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 863093390 1250 863092140 863092187
    0x303110c060405212d0a05071101110d030f02040905270c0607020904060212090604170301030b0c1810110c0a0f050d1a130b180304090209061201062102030106 70
    0x202460702c2d038543d129940a0903170000881c50501a4058024660f0a009031400540302c40c3c140011510150381d9000840c00e40c00904100700424403d401507080c1111388203016041580302c1842c070044071815110079410103000d101286000f84166002600000e004e000703000d55507080c0300400d00c0e510403a04028030440c1d1400c0003804200b2554141c07401c1d54403000c0310811900c0e100d501d603969160207a900b0307660b00e0400200d01d10040c440a0499041c0d0f98041c5802540d0386902503e8001034000300b04507429404808a4181c080e181c003200c8180b00011940c403440b544894000d6103041c82c403e480c00307070300810180c00284071070144a80d225049039419910110b0994150600b60800701c40250800400d081a60501c10b40041c0b00200010450103074060800039114071462090b0242d401c868101243c1040c0b0040040700c401c0e0380034210203403015140c035103403918900c03022041000c240c10080208907026221868541141702040030250f0a410861655050000c05031064900100c40d00340401200c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 863094640 1250 863093390 863093437
    0x706050301150c050105010e09060a0e100906140c22050a1a160501060e090a030804021203040816140117011202040e01020310150c020108040206070303110c06040521 73
    0x1d10b003c000454001008022558580004a1040105440c00001881441e004c04c4411001c2d224460740c05158400400505a00a4820303000e441842e400342e5009075201000c5030030304484040c0c640b082114444240d669841c1095490300c58503441141c0048a03038400e01031204e500c885504009480c0c0c2003d040c1080032034190001001d224444400075400c601c040b0304070270800150801030030b41ea100d03001c0007490340d9184d203202d6a45c01c80791070140c002070042000c00d007d0b090a1102843c3c076440102568a00303500e030b50350646403a415440345252521005410000d16140900d44420340c2c9091900e5045000d00010300b945401040c001c80400e002100d2891045558542c0002c0103517141400a40d143d141803104103080c2c402511602005090014280c1150b500c1641000c08956050312548116140c5030207100312500b184c5811001e043d55200039540c1d10740c0b01d0010b46003280d0210300801c801e00c0d00346403003814001c010700c108410702c0c454640d210032403422800b079849035055202017490100c460f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 863095890 1250 863094640 863094647
    0x203120c011104030c050901060e0105031308040b072f01020307080d1503200123030a020912071a120a0902010c0c140405010b280507050d0507050f070605030115 71
    0xd0ba1070b101104a40010f0000401c10413601980803078600301c45400d91a030741c4210039110f481d100106207000417030400000d0300d00307444103504041003070042401d241025280c3c10a5000755000b80d0003500c2030b074900c84071010031040c41c54003c43c03c24030002201111082050000c3d58038010142e00a018010205003032410b544903500100725850013100500303510360b5a0803d02098410780000c0d0494003400c004000c1c0b103502038544c41c1b1008041300361110380c0c2c00e08401020036980018081c09a4603070200820102e9544a003186480c5d52072000c00f5042e818179000d0080425045040340825400007404001045c00000050960042e00342502290381da10310f01c0100d5024410540003410b400d00c014021501c8030344a02138600d05d201c02d4a040200741d1300c441f086007090085540e120b1044400c440140d00d021030341741000603100c0441c10700b90b080440c20b0360384030300301300c88025104001078001c103c030303030501208014003803040052744090011f090409000402c1d51105001c0c500200080c0c0b080c40700700a11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 863097140 1250 863095890 863095901
    0x504020a05091f360e0702061302280302040501151d0f01140706090302030c070801201e030a0516030504050703020f0303070b131704060819020d0905060a0c0306030203120c01 77
    0x142c1c250030010045d1a100540c40198054440000510469000413018005c110f030003047c2c07a0300200142d40d0041846c40c0b500b12042c503907060b00d04408a5480010041c0c8a900986003c0d002d07142e1890500b180600004011001c66101405441c4010030414125243ea400e03a001410003803814014110301da0001500c144a0403100401c0146411000818140e000c400740c190051004103a0b91426034400c1603034241c42d24100030605074004a001a01e00651400003800412001500b10b00311040b00ea00c4509a504211a0382940e40e444400b0044692340003030060010501d030703007010016810503440c1d4036940c103143c2c000207000c0c080b695100305c0103640800070780d000703290f204440c00b03040d107040d802c0454214080e04003180c4105800108003c84003800050750191011545c803000c035079a903506062160386040e400b81d00126400c003c0c1e0800c1090070700584101da4040c100034001c0c0d080a24041d01240e0944242e102014600314041c40143d8011071407071349940c03030142032985a0a41e074004500600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 863098390 1250 863097140 863097227
    0xc11160b16050d0903110312190e0a060914010309120c05031306020c09060a031709061b01020304020a0f050105090f06120103050601080105071b14070504020a05091f 73
    0x4209041019a5a80a83e284007504d204125500d000d4506c0014941d50301109403c3c000e103100103002d41a41003c2505002c496884207141c80608112254081114007400342c0045000808814050005417002c6c0703644040d200e4203103402c1003011110b03141d0542946109820004124000d6a00c0d4240306040040c0c41c0680340c01900d01040030354414011b90b5944a440703445006020300c0d00000c1d0146015141ca0702165002011104031100084e002d800540c002d011060740300f4410b102c02e880320000b0891a0200c0203050700016581d081500402402070110790040140c0c1c0f00122007480541d81c848169180000c05840810605080d00d0014900e03004007400da0820300904000001400030010740e0300c0c100d40ca980000c03c450b4841d040d04903060910494041030366001c81c1151400a500c400040808800c0802a03818458849000809913404410b04000068022941c03c042c2e28000c1c5800140f801080800045003245680140c22038886141841c2e403000845020882d00340080001306905 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 863099640 1250 863098390 863098393
    0x1c11030a1403070309140325091a0306161b0303090807030305070f0c0b01030b04060f0f05061e1005031008012406020604330501090c11160b1605 64
    0x1580388040d8540e03d030031800c0c082e800602100c1001a0b116581c00030b07074807102030180180c951a0060300200f00070900c05440d15502d031a40c0700c0f00140c0720519200700c550110415074034144041c540310406141c204c0140c840041d0f514651444242203400000041001c0d1303901d502c0510340b50a0742000c0e80200300005010b002c00b000020360104140d8981d0200d4400c1641e40c5a15a50400e014011284a90254801007100b2020b1740144081583c1c04a06580148940030100b19480b14401100c1924074485109400d182c9420038803130146000390720018003501000301400e001c0030f40d80004003103c0c429001841442000404152804000c3d0503050283c803818000b444801c2d0b10b40c42c0061121a0722205040d15101c103580410700d644007103042c2e4000d41d0000032401c0464a1191004413000c3c05844007185000c4420081e28100030f41c1c0600c6000301000781000070a40b0364040064100030340e0400c03006950f005002202040750404102c0c1084d0380c3c0803905651a81c100444500300f0304081800507005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 863100890 1250 863099640 863099663
    0x50c211b030a14070809091302030a0f0302240606070f050d020303070e090601080703050a06170601050a06020102091c050c1806040f050603190204110a17061c11030a 73
    0x31020000041c021061140d8500c0e020408105040002d4041e4800040c0240070170410018a0710303119428903008031034040d030800741d0881e030fa0003e0710b04151080111550001d122041c418180c040c02460064181e014004904404007140941c3c903400c0100000c5c45090040361282c14440c05500b04009154050304542902114220103583e90b0011034a0b040081c0c14114200b0242c2821071002c0d019a2040c0c441d10a01e8440c109d054000c1c1c4002840140c41c9641c83c140058114010241c15034541001e101509495041074244001c0f00c1c1075800403003d5a004200c000e00540b02c81d40600400c0f401c0e00c40c983d48210092404034103000118400f03075400303c840107259410300001001a80100c204071801c100c2408005450305c1510821122107a240e0040711180600440740083d61383c0c40c91009000140c0a50061940b08141e080300310b0920000701801d40320030301c46604178010f503040141100d402c07140c039011640d64860b040701c550004118426a0f00940c03101e840c1001400c0900394091004540f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 863102140 1250 863100890 863100937
    0x60d0f170f0301180209060406080a290411070b04020d0804090c080105030c0904020f0d020f0406060201090c08160b0c030c06010b0c07090911040203070c050f0715050c21 75
    0x26030b038100f03014160320202c81c0441d060030f0071003910813500c1c00100039015504252400304240c5110100030948100c070b40e19032012002282c0348070450300d02925803584000c0801040e0052004540300005040401c01c01000f1080104201c01c1820745e01c185d0440b880255054a8030f4050f4031030142f64011070181c3c1c208800840c00c9034000c08413a0583d64240d0407209000a01401c02003035a40507107011f9001865041c6120140c00c2c0310000140310b42c0003510a88a0000c080c0101e8125034865010b400140d549001c004100002e103445c040090081c1402024003440d50120b016230012140301d0803600050010303414864000c01c5c000e45010100c811705880e21903a486215420660208124016500804501240464003881032076071440e084800403608031b4400c42030100940c800390400f4113100c0d80202c0c00380040c03410407841038002841400f40c1a2185445900800310013025110b000b8454103000040d4051000a01d00301d0003035550740105000d0400401e05a480d2240500328480c0c0d8418228102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 863103390 1250 863102140 863102167
    0x20714010203161419140f190311030c0f070309051f02010615080a020d090203060a0905010507050724270c0f12030c020f1c050c09060d0f17 62
    0x3c2025000c1c2c440f02d4800d020b411894140340320710900903203140d010b813a240541e1886041901d00103601d40c600289481041700c00043d0319000145041100c2c00c022494030521a07140c005d0220908003100e0301802d5060030b80b4a0091030140300703c2d8440138600400c6034018140324420b140f004140241254a00903620003d034440ca030f00a41943d03000d9800c181c40000c040401040044c90400c566a40e0105515500703100340117984204100d54251307440d8280f071340160b03030244030850142c9800c01d80012040050f2402509541b4020442804c1c00400e21000e40481c15403502d00d800f180a4a55001c031100394500100c0080049a60020345c10b0741d4401031806000d07a809100c49014010400c403802d4036a920501060900d007401000d081c080c440c003200c03000074000c0c0c05542d041440107019102e001089800300344180300ca206d1044903030b44005045000d00c44148200a0640d100741c0e0a10040c2c5001408030300400b0000c3c000a1520600401503424480c07400c250103041d07080040c005c1c2d56001c0c2d114208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 863104640 1250 863103390 863103421
    0xc0b0403050306040b0a050f01050310090e0303071206050612090f031804060e060d020d06020c0d030606120506090c28090f080319082703210415020714010203 70
    0x60b000d11715010740c03802c1c18035025030144100c1d80d000b03010780c000710018801100c07282c0000d84842c0b0350300c08580010031031403218005d401040c1509402035071a450155402031081c9480d502c18840103145c440d090140751a41720440c1c00e0700441540300401911040421071610600300030400803408003151800420010b1842c450002c0c2e000c51b801c0c0451611060081c403d50380954040d544441c248078008010300700700c0d5030001c055010b008014200a40d02d0038860425541001642c00a039441e8010320546030014600000c05001c64410819882d210012411556000d8198031480c1c40101d40c5d402282a00c500e284c101510f2000d00d00100c0c442050060030b890064040c5440b040c400d401c0c007080040d00001a28030302c41d860750034080b604484000c140e0f202500502103603098804228814900041075040d640d25405150045030307070b0443c5661180840c101400401d80754408242800040740301401c0420344050030050040e52040c403464810020640c1c040003001039400481007120200c4034070703a032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 863105890 1250 863104640 863104651
    0x8030d1d060916050603010e011401050706060b04060909051b0c0307020a0f0510080408090d0218041406060a0503100e01020403021e010e01051908060123040f080c09160c0b04030503 80
    0x1403580f89a103a00410000d40401d010b030b50f01404c00503004003c001082c5041c01c42c042410f05000d407600300d180d143c1c2c0c01030791b103d0703004074940b01c41c001010003c1543c440020001016602410403140c2016000c071001404044510303000341da4040303028100e040c418000c90300101e074018000080540d03035506102c5030030920311407244030f09d03090100404503071300074a491071169074800140c07450052010100000340501150981e04100500201d0141078240710b02240280d001d20826080380c203102000f1460801c00506590141d0b10700001008540c80000f0401154080e414000c1101610b5142213802402a544044d50000c0780e08006c607034064207070300703084030750719081c2d82c0e001100070120300540b900d00c50313400d03841d0008003400c0703d045501707114543c683d0f081403051400c1114250584958a044203080300d441421920009040040381c0c10181000010041080500039030004ca50010317201003401003640d10700300c10042020303842c0d52150b4410035038250305c80b580c0c60503800c11b0b00f402005500122075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 863107140 1250 863105890 863105923
    0x50d1404020a0e0f0103060911060c0109060c030e030417013e04141003060302030f030c0c030607020a140304030203070609090f0b03061515070b10060908030d1d0609 73
    0x9010440111a000051042c4c2c25104009841d91035551500001c1c190707401c00382d4200700164521030303a40e503d510003072003e0085100003251040301e9081c8541102c401c2d9a1620900d4501058050811004000e03101101d1944d031080c900c3c0714500854502400c5525032000340c440401201c03110310414001e40d6400310710350307880d0038000d969050001402842140100401c103035100703692004500d0040c00d080300249040c900810b49aa803903012a1504910720707224002d030380001c54180c09943d8100010075102804600520340350901c020040d450703008680015200000140140500c4a003c0003110300440d4054115403140c0c1e40c80000070003000031400b0b000c0b441c9041c036201403020001402841140c2c04000d010301060749441e28581907050085000f0b5400045202c80140306021b00c1001d84011070089403081414684a00f001c010044036811060503c000e9007000d00440c1e000209079150b58003190000600c01d505400b15040303194807484003070b41c588101401c2046c1c1860100d114800754030710380d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 863108390 1250 863107140 863107159
    0x91d06041a101206020a27080d0c020916090f030b011a03060a05011b060906020904180c150c021905041104080c0607110910150c03021b01050d140402 66
    0xe00b8890102c00318482c0382a00990441003034003250382c580c0101000b03038850810414200c000c04455218411001d950002c10148a5042000e00303810b01406034042c40c0d5140c40c422a40c02a400204003a0002d4010010640b0000c07050b01c0050080303401c0400342402c450540243d03a640d00c2c1c80140c0400902500031580b5600002d401c46a91245c00e8071302a00c0c00502905802c3e041600440d1511205030502c480645140080c00c04140700c0d10980c1d00e401d002c0c1d10007690303448006090005681d100e090340d0b000d4081e00310b034903004110300f0f401007401c1c1e50500c144820140b8001c0700840705005454000b03940b1242d4105191070602c00c1500140480c2c1064400780016281c11008003698061072041e038070a40c008001c170100700d24200c0000c050a501ca010303200c0782d0520031b20110b0803c800454600113585e500041c14001e60014201084103d4210300e0910050701c81135400a407a05880d0212103041110070b1114929603000e40161003880303052400810680400040c20000048155004c0c3c1c040c02886 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 863109640 1250 863108390 863108401
    0x4031509030f0f121a04060803040906060503101202151204020f06090d03080901020705031902060a050408091e1c03080610020309010c11061c0e070609091d06041a 72
    0x107080d24035024143da200d04182c2c0750f0750700b4068050b20201640303010b040404d00d101e148036521351207804040e00c80304004540b80d50410074810105c88268201d00c05104040c410091840054400e201c15140c0c1c1c101203007007040142c40810098207007400c42150500d80490b800f42c1c0f1018a5a055101c0c0b80225a2100740c0c0c512078082c0702403449500c1d03941e5000010b0303588003408280140803080e0000000b0b000186454056101c1c2c030300b90340185034403400d200702007900e0043d1103030704108864005000013010022810150342d420b240c3d20500c1446405001c10500031229800c9411a102225030080c1280b00d40d40840c00c0301000200341540124086014400454030a0400d001c4024948c02036800652801d06682c0040d6200074035010200c5200310040c2c3d44103103640f2004041c121070984054000d0300c08496002e144280c810b810b216000300e5100c3c8408002266221329183c003258140e007400140e0124660320070103071410b0b0b4070102d405c5100d0002881304010034241c115000c00800e01c241420358444 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 863110890 1250 863109640 863109647
    0x1a031602071208270f21060c0318060c1b011d010203092e18060c21140f0718080705090f011512060314070306060b0f030a0e0304031509030f 62
    0x4582402c2e00710a1042c0c00641c0c0c6d003424413120440090b00e0303080c000c0306e007250503407a45070240c222411030442c080801400810700d21202e0741102800300310b01901140c0b400c1c40507440c00780102014040044000e074001102c0b000213500201c8800181c140e070780e598030035513100309010703500a45603401d20b4400d120070501d401141c1d1250b40c0403605554103840c20010055800000340071407060000070115030b80c0344940000c0c40343c03244a40c403688ca621940f01002e03020304c890803900d0f02400343d2590345041110440b003007525059150361007000801e1500d03803610f0f01c003021a03141d010b26000c08140c8184e44d81c0400e0f210400039211088607812180502c2e665034103429041646401e12460035034035544664068054003403845511419840300c40054026501e80303d078400d1101c214000c01298000700014018024503004806c003410304003588038034146c030300e4980d04410703c4024800c280055031f41000d400080d905000704c6008681042d00390092000042007280280035040040300800c000380e0360010020b00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 863112140 1250 863110890 863110957
    0x1606090b0904020901030e030a11281b0f090501030c0b09060f0c0c0d060507021203070f111e150916230a120c1a031602071208 56
    0xc20020980c103001c140ca041c800030f50841c54020f4181600c52051a83c0550200046d200e400300540da12100302c0401450181080c00900c0200341c00c84961a40105944850744076000942d0710002a040d0b002c0031340761809a807006034204e6809a82c0c420303000a022006034010505032401896060305030341c0c0d02c2094032020703c80d1200c510b40004040c002c81010a1f03400340505407c042c2c0c441a100381c5880980043d4040c200448122606a585c0c8280580c50340d04102c2c8415900422007010f2035420000400b0b4880d401007640710301000580c8165081d0108207104000c0905061203800c0b074401c2c16046025150304d0f42d400e08810200c1c0c2d4000244410301c0c0010407900d91350240040e1400b05080c204420041400c1c1c0240e50350000480e40c480220f41c0301c814043c0c00038400d251031120400b81c280341c05003541e4010352003c22860100306032448501d200c2021170350410410a01403181030040942641498120f601c8403404401c4030311250144001140107010307955204003082c00380008040008130503c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 863113390 1250 863112140 863112149
    0x121018030903021507080f1c0c2f0f28030c0f030507050703080c1207020a060e1201060f0501090801140c030907090e0c010e010903030e01230c160609 66
    0x340001c20030405070604016200d04c40004114044c50304240f61280c2110ba4480112129225000103680000100c201c8619501c034809900030320401114880c000e1540745060001240522010350390300c1507400003400f0b042840301b0b070412354982c00da85000258507060f0008000079113107404010440030703e0b20721034185101d0345d0540364000000310985405044407034804084080c4a4200000004108104000300007588a01c05056817803807a0080d0340d090100a1840042c01c0509006400c016a40c0c4000780b402d458540c41d00e41051902040010100c200130100034a19518001d00070450400c0c110140d001e03a4001c0e2500050240c5e81d10f0007600b25488510700039002c0c9080d402055640074450002d503004013540b0111136001c0d071101d04110450345412101d100f55480401e5520540d6007207410102008003d00f00106c01c18550b450140800d40c00804080c10800040c080500314000c035903808026200240d50360391104461519190394209182041c00d040b10000720000c0d0185c0300d00199815036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 863114640 1250 863113390 863113397
    0x50a02030c030303010f0e2d0115052d09130621050606040f0b060f04030c0f08060a090f0f0305070201080a05060a061b02041e0c080105011407030e12101803 69
    0x3585487d86004071020050700d4600503943c00c000e607440040c154406040150000c11789044154549000561120013503500f40e014007405000801c09440041e020034275225407041e8241c9441031540c068441d0b8401c901e503603030740103080c081104420030a03a441801502c4061505000685012488106205a20f000140203900020000d46e44e81400e4000807410303c2c20050101d0209105030004032503800048102c2d03210003010074104140500360704908000d205c69144440c81038204000f5a4413014000d00416001d62105020b5080240d08a07000340f8040e0080c684030945c203424a8000c03e15400088103034005446017001c5100c10f40c0300e00c1400d0123410003c0c14000c1440c90034038140c232102c0b00c0003019010100c0078082000540c5413802001540c08403032048801031100790041500f180c0d0f082a2071420441000c0040c0410398000c0c000603400c040c0840b90380c0c0c54100c145400ca40c0c070000040c1c0e040e001450701c120f0541c0310600048a15400d14881c00c01c0c0a94891031240103a4070701d84003000b4001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 863115890 1250 863114640 863114669
    0x80406080a022a0703330b0102030307050f120406050106020c030d0f0f11070f0807090c1218140105070207090e06010b0c0709022a0c130b01050403050a050a02030c03030301 76
    0x1156030301030701c4804001c2d05509584c3c1d1143d90380c4943d4482ca65070000c085180186c0c4001030054007158000401403401200100400301035840000d550340001064042800800500008003000e8001a41c000c00b6514003e1980741c50107290580c0509428801e03070300984141c0069403000c2c500811000b20049266a403281c000300d41000489283c6a003050210502a4010300c5240080c401d2004d07401400c0740602150810b46000f804518055059002917182c518104039450030301c0c0d0200c8007041a44c02210089070064203184801c1c12500a8440140341c0905501308044a54040d0006440781c0916003d480150796550b24403025181e8154501ca1142c015800501540c500103010b42140811141107c0c03040351600581c80485c0e02c2450044c03090620458620351884503001482030500b201406840c031003e69002240c4c02219030300ba0240b00546440400300207074466800d030340065070424102e40c444460303414181d441d43c4203d0030a80c0607000c0e5800034029800e001003164103c60b144a01f4040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 863117140 1250 863115890 863115937
    0xb04020c151f0306140702030f16021503040b240102070b0a02211e04140d0203010f021204150c0c0f0501062403050108061003061e0603080406080a02 66
    0x1000302000b0011001d81080d000c001d84400070001c0460040c40c401c4030000340d042001002c1507024140200401c0855004102c10101d0030038003420f582210b0178401130350042070518400507580850f50703d50b00c01c00c1c0c0c1d80881080148100e2514950162803c16480081c5040c052980c43c00c1481c2002c0650259220084c1004a10f25460003481c240f0028411340788036410000c0d507202c01900b20100140c400b000801d2001080f45000e00b1001d02c000000c40302490903180c0f4062001418107a100140b2074164201590250b4800303420012040e042c0500c00c540e41c8140e0f15030060007001c165825102c054800c01c540605106a119030300f0070041a84075008003000981d155030b9501c41d9100202d46079521000b00090301d0f4001039600a80d0b0307490410364420010030030402812610140c1c00350b0f4943d40840144808006000702c2002a6600100d020506400d4542041d25049150801d055805d01e0400000140040ea03400f50041e0780f81135449421a494030b0350540306038016200803198034000d0110616 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 863118390 1250 863117140 863117173
    0x2032509050a030f0c051908010e010204030c0e09010e031c0b030303010b070b1005180a0c17070c11030303090a031b0317061c030509040e120a051e04090209040b04020c 74
    0x1c04644540e94200d451742e11500400c034815030245404034168908107050250220078000c80c00013150480003142040c0c42c40e100d6206100302c1d480b034407041c402740c08041411440d00b9081200050040b10881c3e43d100e0f036004034001e200c3c0750b070840b000000b4a04401204903240100c1164100c03407681c60814203115468451100c1920043d14541511110841c009920384541020180b4088605050544c519280c00e41c881aa070600c03407440f0400500f42c4d10b5001c01100c910b580750b0420050b10b8540ca480c007452514003804c00b0710f01c0b856a8184000300400c80d041e04009048205648295141d4032011022501e80b004150340160040108950009c1c0c08180300880003003c0e4080801480018014103020015a09010480b42030b00050340008005090342458041c01c0d440440c603600403c070100410710105028014a0042c904120000402c0414a0200d0612360099481c01040075580d56423a40301900039071295092034000e0b402e0041c41c0b20799103864400c2d01e1084a008001c0d06201d2013551481 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 863119640 1250 863118390 863118413
    0x50f04060f0c2906100c030315050a0b0c24040305090409060c0c140c060f090406032406090b13050c0d0f0e01050903071218050402032509050a03 64
    0x5800c001c51007210782c1c0815040d0b41c606a10002d40320703a42d44107101c6000e0800444000800c46401081d01910011045900001c500c80301905480e001408031030042180b4509903070356001c66409020104040340008072100105042c81c5100101c0d050101a4001590580c1d00071085409502d14000054080f900075001040b0b6000020000511906240e40b0f12040350122124100004c5440400004101034036003d88004925030008081c00b410036400101c4a00c01d100600e10420303008100e0780c005484542100c0c01a50780610300d101119030300c64164240c81c0440c85050221800e05800080c090403a110381046100c010780b04a04802414030208090180074056503459031003040078070320310030443c8a06954015042408251005694682820f450010300402d0241c0c00800c203400001d005591302c100748038090304159200d0103224282c0c00c1111401d074402c9400900003c00c100001c010089031901840300c8142d502d1150f00e000104841d980c8890103900d801c00940442440442c00e4071020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 863120890 1250 863119640 863119667
    0xb01031803080901020d06080f0d08010510032304030c0507140603130510020f04061206120b100b1201050108091f1806140925030803190614030c01050f0406 69
    0x5d490070704c4011218085600076440889560400b0321b1a0030005010b001e000e405c450140f4110341154144000941e101503020303040303002d15648a038500840115003070051071504990488204a1909080160404c44410000c0354103000e41040400c4910010042c0c000280c0040e101c1c60450766503403040d00f06001425802e4802c1d105405000320440031500080034900c030244502038650b4605040541100d1b5071442828010b400d0880902140aa140c1030802c0c0c15040042e44800f610380105260441780141c212076400040003d00040192545141c03504a13007003a602c10981d40da400040a4880c42c0b0041c008120000d50310541110a82e142c1104072081402c1101c04000d080c0d03541c95004841c440d604540c0301a491a04201c8100c5c0203100e40006a5980c460710301928142d030f141d0224103562808000c00440d000704c003184500840c06403072002c11014040402c6466158400225607000d24003045202c1d20841c5807500f095446a4203817552424a600400d051600b0400c040e1003c0400121 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 863122140 1250 863120890 863120893
    0xb0307022e050106052a190f1707021302090306070f09080312070201182d061a090a02070b151f050c060a09030507030f031d100b010318030809 63
    0x41c2020000c1003449994000c0406840d0130b9601c90012030303156206001d40310810315008084a05081d60307000855602c0d5408140300340c0848550a91400140c002c840c008090108100540c10301d031507011000040182a000f264180f002110010b9000c0c00c0e845031403600fa405400120208221a001d80d82d020984001e0b4140200442e8450143c0d40c950741007444096100c40c0c0300014010903540a22410b5040c864604100c0d040160680f220701c026002c01d034046046444851038055035604102e10700c00129405001404405410f0980481081556809501c42c140400101c1d48007103451088911140d13000c2e140541035900d0320100e0b0131000e0b00d002030542040c010b01036042107103503c101101051010340c0f10740340c58010b80d50b03059107418801805a800c1c54034003410100400e030024155403050341c1c10b01d4501380e40c081e010300c124003502d00e03c040d401c07404158903c4868500c0002c100c0c4641031454981c10810042d80000440944241d1241217100301c08064020010900c1f810304d041e0b206d40d4280 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 863123390 1250 863122140 863122213
    0x70303110d020d05040213050c0712090f060512090601232701030501060b0f040b0c07031514150a030b040303111b1e0303011404060f08010b09010b030702 68
    0xd900741e069a00443c03264610540d1001004210f261030075440e44401d00007082007200c0c1c0350401c0300140b103100d460f10250100c82c401b904400744e584103c03420070107096000c0d0045e0781c8545e5211b0141041c1c1203031a581c1c1000c071500c000600d030b900e00080c0381c604031038070900b8104082c0b102c100504010000e83c02050340014003205124824089100c4106200040010154103589503013451407c69502d40c1040600f60810407001507116801002d80302510f040300c4030a40e0312102114441e2400034582c0c00207207040c0701001da0400a005661210440164901c58400f05985000550b403400c44401c0045a110b019500c06001045000e43c02c0c0b40d10038400e013000a40b6803401c103a07854042c0c1080c507162101d141540d4078000c3c2c2d04810701880307a4840213006c40306003000344403101d1a103070b00050044981600b1401c480800715a03568120000401c0000507140360700e915400301078081c2c048100190b00134030803078000084004800c070440b44941869800750103202360045202c10f00c0540c00030201500e84e942c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 863124640 1250 863123390 863123407
    0x61503030a030f06050918070906050d020f01020a0203060a0e1501120f0f0b0439170c060418050601090f030305031015030c030c0207060c080a11070e040201020c1507030311 76
    0x7258202d004400402c2c01c1030625041d00304c41f034600b4120303400c1003281e01e041c00001c0140d92038041034040f0035541150140500c946c0710004034a060303140703c40a9850700c41c500c207020640da0300b83c0c01340b0300c42014601512003003c0c1c80c03039a54507140001e12548103030000c0f806041000c01c0707106503c0c0c180c0901c1004003020300310382604d40b1352540030196400e5400461099051800c0c403c9028ae104605034512100241507441ca02d02008000c0d861080c078441524180c500e0320a51014001114203100051105440e261513042c902075001c00403810b0000c0b03910304070100e1015800341c06141c048071031010480d682107095a8046600760800b07400280d540700c10711408a402410031700c80ba400c000c4940e03000914002c402200400343d40c81c00d0041c505540103080d00f400b8440d81300d01500c5903035030491042581c03140c030707400c00301c42001c1201008001400741c290082907510a00303090500890003642100c5a1100d58800c1050f1406481034921181070100a25800207009410030b440740603000f40410f007803c030003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 863125890 1250 863124640 863124649
    0x302010e030d0c0f08130209040c08030a05030f060a0b0f0901050702100807030c26180307031d03061510030603020a0909020414040f1b090c0c05061503030a030f0605 73
    0x510305030303441c1c580390031240f4002903216003055001007541c50300d6003880c100914400c1000c0b00c42c4d030001c3e004050301800103050140040220000382030381c50859681700440c28000305a0782059518500c51101d06011070018600759001500391a0b10700e41151400c1d0040e080c150311139000345503940c1400790502041000da1354850740d4984201d4a07032a024464907040d100201182c503044124018440c80e4001c1d0310410000200041c4800400c0c5150143e03501e541d095011115090408400d6500c4005440c000305584620420740c1800c10071580000030120104041d00d5140446079613038401c3c240108420145000a1003c0c20310038a03090008415840b40c0205c0c2e091841c9401c25010503440c0e0001c03500314203083c848d8031040c900d1691800c00904050341d40d10305540203690082c1082044415003c003294440649000502890408104008a901e00540000e00c1c1c0784c030a40303807400789000249000c000c03042d5100ca4840f0003409146001030390b071401d80060640c0c1e0400042507540d82070200742500c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 863127140 1250 863125890 863125897
    0x902070b06103504080c060a06030816050307080d1d0d080601030b0105090301050f06120102120403030b060d0207050a02150724020c010f06170d080f040609081206040f060605030606070302010e03 86
    0x2081e1036541c400c00324a14521f040005480410018548001000030840720401c0d5104a1001c45100b000e49031581001403460194100107022004000f5107450042c20701c0d03005024804002e880c604080c03110098440c1c640940c51030040209001c10001a8150710903032100c40d95000c14100340e410180d0700c2001c682140c208446aa44001c1c80f0310038002d180ca403003501010001c01000095141109480b00c070140014083c00050615441e20032841481d034616040d600d100d540c109045480340c0c0c0b41e0030110358407216180185d01502c0c0c480c1c8100c2015807030744115420160005196101c2c107000410840b2420440d64035082003540c213100c4111421020300452880c4801504013151013070078002065064502044a800c0c55400449031075403140d00304001c1e543c0200c0303207a071074161641d41e82030520260035914001070503840000f55100660804a9030700e4016082541c003041000340c4d00d0096000c4640760301815010400901c0052607500d04a001006440c0c440e01c004161140d841580c10715681 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 863128390 1250 863127140 863127143
    0x60e10121a090d09050f0a030b0a1d0c041406030616032c060618160302070b0103031706030d02071214010501030f05120405061902160902070b06103504 67
    0x40149a0b9803c0d000d5001d0701080140100702e429504c2813150348002150341980340b000400282110002034000d10042d07204100c0303c0704503180e03404050541d0400e81d84401e075107180288182d01c2c0c05c501d03074442d890a181c024440d00e0064014021074540301114074840320810780e090205903c40d400c0a050b6503803240c2010102c0f1080101a1100504480e007a0401200509031400380120b44101251605030320807081c5c01003140701143c03400b42000d00088001e032084c60070182005c07202c1d1000000300340d0301c5802d080b080c00c25201250056141c4404050b240e140120415006030702c01d240c14001000906244c842141c400d08180c12a1003429132034909441c1e00341e00982d0300e0386900b218641444404d1000d20704d0840d07000c107001c0c03806003003c0003d00070f401641210006101d400c0b0748038100c0c80c001c000361200480b0480c1960030030399403412503c0c003a50002c0402c0725180c1c40d01011520500740b03c0d4000c9a00f05036601c9200080b000c4100e448844031105202c680c004900034580e003402c1c146040c0207030085 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 863129496 1106 863128390 863128393
    0x1c02061807030b040c0503061b092205040305570106090b01030b0103050c0d09080f03010305030703082410090e0910060e10121a09 58
    0x408079801c018440041c2c1010f000a0083d091004400c44004408444450b520100100ca40e80c140042d00c41603d102403190402c5440c3c6412820107200c1c50700031045100410401c010103680080c2c40030b801261000a10306148550706c01214420071903035008120368503d40c0c2040f44c2034810408000030792102644010f0f11040c40c084004980f02d013440003805001e45a1032500000c0441c01d48040c0481d1a0400c05045035001c4d02400c3e1140340340144490800c1e540d144040087c11410100b1900808100945441e948440340036601841c0940300641c1c54620b03c1c50040c002050140c520155155921825080b400c50307000700205c07142c07040e218080011490001540c4d6807640f40c02894000501c0c10030001c04880001d0b2292595149180900c426503030b9209501842400f9903058003041c00e0048188900d011030070820086901c1000c1c900041d4825207a5844a6501510014800d = true := by decide +kernel

theorem cover : BRFrame.Cov 862949640 863129496 := by
  have h0 := BRFrame.cov_init 862949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 862949640 ≤ n) (h2 : n < 863129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
