-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:47:19.578986+00:00
-- url     : https://prove2.me/submissions/56276923-816b-4af3-9099-14d7b4726beb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 919244604 ≤ n < 919424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 919245854 1250 919244604 919244617
    0x90606090402071a071b0503040509040507080d0e040f05091e030c150a05010614040302190e0a050a05010b04140d05070b0d090b060418030c030212040f0302040c02010513170f 77
    0x5007500400d05000f0750091a1b950b4005800415600e04408080402d00010035201214003c50340196942c0d01c600d0410304000c20b0341d0240406104205154200c181c0021a20725a040141d4041286018290141060380e40981d4149a6034101c03021440d09121301911110045130740d101240e10349200005001e240440c0303400703400d034040d02d01401c0c86020342d094016640140703254540304d00e201c0310400308030190b881944402403043c0740c240762242c030002c003c441c80c0f00180380d908849855483c20040090103070100300c40b44540c00e03141034004140c1031040c00a8070259040b2458106405280f5821311656141e00401506c45208501c00041d8030380c8401c0091800801c10384000c695007400c1d01d041542c0c900f015060078130880c14003000004989003202030075a8250103140a4082c0d201c0c41c1130a07801c011009480c1c03d0803040000c5c020818024603891442140e03c0be84041000d8840381031f04901b00c1b402642d00900c200041081d8401042030041c520404c403140e030301d04914003c00451071410307603404034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 919247104 1250 919245854 919245893
    0x16030e010519050c060601050306011d0a030b010b0307020705060f07021909180b01091103040204150801021803070b07030e241911120a11010b1008061302070209060609040207 77
    0x130f003000007840500542d5041682828054103504100c0c0000c0c08550451003c1400745840c4035000d80e45546204c036000003550003070500f6105503180e041040c80c1390b00441d10000980325040d0300040e24200403007292904503e0892450a082481e82084108241900c5845400c2d40103c030100b030b1819903200351041d09a40081859050f4981c1c6080400410141d2215180e185001c106142c06160002120782c025812a00081d548214030788100003071001d41c0009056620200311040d0a00d2080e004208079101242107074007507035840402c4600c62194038001000210741c080040250b00303015000d80400921032402c03203c000b01002607040c25411205489a07410b81c000408400303a41c100008880d946074102c081e02903d0031111580b03c0510900c6a024100283c3c0103c0b2051032100f98041081400010300080f60b00010341001400c1003010fa60452007600000303403408141116100700c07441254040c7c4041c849070354450401c5001d03048000d0a540050b0204104400920107115091021114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 919248354 1250 919247104 919247107
    0x3030a0b0112020f0a03020a0314010f2909151e030411012c040b0d0c150c0f062c060a0e1f0504080c0a0b1b16030e01051905 55
    0x4001000d41c0d82d411049900144100b25560240c0c90450842d5200301a505001d41d44100c06501180103180c00044140c034802200000308060b071a03031812008072088000312045440c440081f270440c0751041031041e9044401003101036540d05003c6a0020030b9012544954103001e14071000402e401250346c038010840360000100820022070380000c2e40f81071030a207030511122603d064407035164002c2c0500c1100c07190004078140c26680d2190480c8601007030207404541800c00038604060601d106000307004503103c05212585d143c500c502030b00c440f511307080202d0703450002254507039070f004000943e400001a02805184a16668800018601051460000c020505d0070200b06800c5a0007003088000c1d5807c880032882081c2c101710840d00214010850003d403903150b600e40380c0c005104080b00f010b0300e400303682c00f9901406400b94009105181c0c08458050440b0380c00400d402e07920a00d6162640745c2e0101051101282c42041032400c20041818010316003c5003525100741d042d82c509a500c0080d80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 919249604 1250 919248354 919248371
    0x1c020a03091a03040f060b18160c12030509010b0a03080a02010b270903070506190b030d080403030e120408030406020705090c09010f0509090709030b07111b030f03030a 74
    0x107000c10303110018203041c1031005420090300848032581c40090000303003819120098403030034003086500c0b031600c0c0301d0010641030b05a066114551403124041f101303940907010107c0c01008031402041c60a0695a220041c580d01506055041d0f0003020044e00c042910b41d610200005203480381c40030440614003c20255071030380106030000342554a81e000050184929803000000c00c5d02803480b4840b06504581200141e13650740c5d11440ca94003e1300c00c090040d108030303014805944500540c0080b00c280391841406019980d60034595a0f200484c41000000c0c1207c2c00500403e109520250f01c8074400303800d03251242d071004400301082d007154000c0c404580000804200c0b164040012000a00081e1007207a41d0b8036205241d00402e00076101410305100e00102c60b805103038850300840383d0445c401045109942031100004141840e540000caa00391070390000300324054000d1504c0da10070201c0b00010101c0ba0720b0007010f012402c0d4180c1420f60140301c0d00c00c2d103000c041c100788059403098561800c00140e001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 919250854 1250 919249604 919249607
    0x23151e0909011505040b011e051b030306010509011b0c170d02160303030b0604090203040516051f11150103060b03011512170702030a11030d030b0f121c020a03 70
    0x54000c0c05a00242e8075010003c1d4910035210300010071101d0444000038101d10420058450036003030a07810703443d403155140d0071103500d8001010b051108021845030030700c800c24121459492005641960200d88280400d08007988101e0814040b4802c030181d641c80d83d14032740d0346c401c29450746404c40c1010b64645094050782d580c041002a462002c0d51000303101d8880c1d80c0e4510720201145002c0501055154103410000d40c8402044400a0210000c11542ca1409003060754035140d250843c48280c98155400089610303003810a12510700c00c030140c0302418140c0b03100580b03840707440b00425446406010b490030248844582c0060003140100d0300800c40c031890300c0030503007120b500e500120310310060b110007442159003607078030b074500c6580c0403007212554400142010118012000003d40c0751007001c010300d0402403040d4010f40c00d410164120f401214542601b5400ea030180788000303401580d00d49001040b0310f0f1031004c198a051440c403d540e00503652030102c000c80c030b01055184016a0240070200c0c1050f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 919252104 1250 919250854 919250869
    0x21270504051e0601020705060f0f0c030309030406020d033b0f0a060605090403090611010207081b06010f080c130b030312181f0b030c04020a0905120123151e 69
    0x10300c3c241301501045090900062050040440d2524054804034503d500520148202e61401c0c80310000c40c0d89074034100803601d07940e600c54007801c001400b83c10b0300a00f05a01901882f507620401014880b1820103d038210300940c0941140b02a18100c00242d203d4041400d0180c22480b240c2503001d0094031592303040000c10f030b8072298089801851104100404280d00c040031000340e981ca854003924010014521501a020f0000c3c0600682d1001036218130042c0c1c01402201840a041e090b15101d81e039400d41148200040c1c800c804040e000101341304080d250400b12880401c00300d00380059003194100c042840d580180304140040b0131078900344150b41c0f41d00391040f400d8420b0fa0300101081c10b01101c200c0340c07004100c1d80103a80182c0b50005e841d00c598060100911481001e0b10864a40c4020b175401032a50142c0c0c4a80380c002c00c441c0c03101c0d001a203411300680c004084401c18181d1004c52003109518818001000c1c0c2d00e03040200691004140c0c0c5040315070411003940b441c03d0b11340004103001c00410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 919253354 1250 919252104 919252111
    0xf121b0b04051806010e0d171207121e020703091707080717030a08070c0614071202040b07080a09031a01030611090d02060f0708030901050421270504051e 68
    0xc140f02d03c0401056a80c80040740390f1401c0291160340c800318841c68440c845021b8800c01c4030300c842d000b00301002c1403070b01c5c068a2881040c3c585e944800174003288424004a4101c50508140f0b003208029202020080f5001462160b110b4035142e4501ea5460180881541c0940c9981c030280c0c000190812078074200308004005481850011211007e0452800342e50340b14066069060104034000900c030640603000c0e9a05a82d0000400c0c004850829400c511894044030301501040d00c49100202103011403094500f52441112001d10700030300781d280c6404a402000d01402046441040400040c15444605908000c42103200e0b41a50440c0b50810070303960343c12880d074800300d0b003807003040c50941c0c03001c40c0030a01640640b00b0641d580001c40003c84144034201d00035001c03d100005101844030150300003846180621502c888603407601411101c866600185d0ba03001890801108000800030b0298040300b01d41d402d808003445a0b158081810384108445010040b5400724050710f03420301d41c0c481140d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 919254604 1250 919253354 919253389
    0x1409014103120a09090c03020d0e01050708071103270a091b0c05100908160f0c0614040612090b07031d070f090504060636060f121b0b0405 61
    0x200030508000502d006198400c0c03c80540d203400301804070034020b504840b0b42427140c20040c00380e0310b000501d80c0d021b0441510361100140c1e05900003900f051044403160030343c5100303402071407070801407299801714442c50f81401c2d00010000c003080d42007039076000ca1583c010308600a0200c0c01e03802810102e4242d108800141d07091103803000e05200021340200300001568000e4030005200107150030190400d00030300c46a0380c458121220007005100c00107404a11031440b5265001340c090305e4000484084203541264242081c06100078009a4000e80c440c0207600160040000d49030750584a40222500c2501c4902c0407a035118046299592640801c091072103212000b0603d051411038901d440e00c1080c0b1413580c8c5596a0300103d070400c4206d8000d100100b0b6001c82d1101c1d8070302190703460991130110410452031707203602e810b01d0034001a8500400c0b040b00c07004041425014502650510b2400071a00211143e0750b504100181c1082c0c2c41001401070807190100300d071500d040c03005005062070228160301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 919255854 1250 919254604 919254607
    0xc0111071e06270302010341060d05060105121219020f010b1315260f010509070509040302030c060a020309010b0a030203190507080105090102030402010801140901410312 75
    0x1e10b204281c0f160501140e60a20740000c00c504008001c207050740f5204000c00341c8100410307003194546042c00000c030328403401350341d00d101030f85071103040265604e1301000c01841078005070010450f82c5400d100148042845e034042d1082c100c049412800d8540c85100c440620311030049071004115410002c00684060110007000b886038403a00040d1200703580c1d07010847c0c80c1d440e030358102c1c806540340c1012001010006080e61201000b80c45604081800700c0c41c00c00380e4400c02c1070400750004140502c81c0181c03124406000254142400d100980c3c10003001a0b080d0700c803c0203800d14030002045000d114068071000107032281000c2c40b0480c2514420200300e4841c252904090026950100d070b8202c5002c0222050f620282103441e10034207090281c0c0c01035202d540391000b0040d0002040d00114440c40c400da031605c5882c1e80312150140003400c80880c1d01d401c00c2921006100000c0d889500300342c100425042003003005247c0c003008200d13020807440e0048100d00c050b403c99190404000103240c0c09081030066 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 919257104 1250 919255854 919255907
    0x22404030b0a320f060103020405031605010f08040807110117090d090602030403031b02190303081f0b1c0204050d14120903030f0a0909051e06090601020c0111071e06 73
    0x2052952406445540f5a0802c000070448681c01f917130440d001041c0240035601a038025000382104400f45115050101d03100e102101203141c030480c2400e10440d401008070307092040c1504c60505030418108858144010001d0841e42c0c02640b001c030510a40c070280c0100520b84110200601c2190554401025548248820300001c1d800410200c9888004d41344280c510380c890002643c84000746202034400301000d2008414503500900480c80340400c82e44a80000496156000701c21200c0e214104a0200501ca002030700c2c030a0f441c182a14072480301c4054205a250000104101c12800d0101c41c2080d502010001c808818441c07010001241040d007402c054081e000701c1c1e224410303006401030001000500400481c0202d02d000040c4c0b4040c0020426854080003405810381e0aa18951070000d1a0000800714585503002c1d510401041c1c3c09882c00001c00c400650320350504415074001c6004041000c13506090b101030030b0103c03800406034061410b180400180c0b01c1c81482c0003c250f1441702d4400c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 919258354 1250 919257104 919257191
    0xb210d050306030c010c11090c0a02070b130e0a09152003070c0f03020f1006080f0a0302120c0a061109010f020d0519030f0603061d0703022404030b0a 66
    0xc4c3c4800309420b08040700c0b2003a06141c890107900c00e01c4407050f4059240f20038441e10100d0180034280c40700ca507030201d030403441e1140c000c204540151000c26192001c007000034803c0b4243d44800030b8000c2e2880710003045240300703940c41c01d0120005441600c0069903540005d83d411824103450041c034403a00e2100303480c41c20300b84802014400010409849074148074070880030580700300700b01c0c3c070700043c1d0b0030907144007020079200c580203081340b44511200d0b440b903800d480b0441900400d0f0100d1080e07040d0020580100d5030087d14121f0b4002c44842c11035406801c28050124809000d418071101c0c02e40c01507542e546042001401503604c81c0d000b80c0840d0310503a99500607036003040458a1594a6003051001081c2e0580b04602802c0c4100c4a140303494109680081044036942020f0241021110100680c816008500e9540d1703510f0710010394000c5460300140c58083e00c603071101901d030008001a9151030740b01e8031140c0100d0300c01e40c0c605200554600020b036483e9000e10629070106900e510380490010080130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 919259604 1250 919258354 919258363
    0xc0a140c011215060f1206080607090b03190b150f0a08010803031b072a050102071d1f0f031419030206180715050304050c0607031e030b210d05030603 66
    0xf00c0050040d08080740406030300a90406c0703809050080b05001c0c1d640c0340c0c40a9900d64000fa110103000c02c9048402140382c084a4040e02e01c00c0e0f28040e0b40040d01d00b0711001c40c0b1301908401040316041000240001c240e1b00c030f03200007058030706804d0310b5041e540e00703511600401c584d005070301000042d082030051164050010b044a070032209400c4080d501d0741100e0030542c1d60401986c00a00b821461150031400c034000b043c0c003a03002c840d0243c00360391000e0b40e140828030700c191400c1e203520b05d2b0900b40c07070000c2c0034010401c90441a8803000d600450081d0b0300c407021904078640680040e1160754040260710701c8500c081290b000c01049500f1305024060003660003a60f0751402401840d042500008100900001003292074024003080c480c504d04140d02d1400584a0790041c0d80c152064004d02a00110a04000f0211003229034903503100106042c0703000f1004140310b9a064480101038a0311310f00e44180d80e84017042c81030882c00808003010b008060f80e011349000e03412100f400a01806104001040c1e5000c036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 919260854 1250 919259604 919259609
    0x619021c091203030b060d0c0c0215040f05060c010e0115180204120201050c0a02040f0b03100c0e130f020a0f180303120e070b030702061806010513020c0a140c011215 73
    0x6004c50078810510000b001b42c0075108800c0790312850b10403000b0b02150b200404101c5507000380d95180c5e600e03888044580542c80350b07000b140c4912030b440070100250b0134074100402d0182241d00001403040d600d0105642903ca02e05811020034504c2c00c0d041c802d002400c44480e0094148880842c030741440c0c018103025030144140060305018002c00d0706880500184280c900d4558010010000206400c45403070050042d045846e009200e01c04002c10b440394244a103d10b00c0840351102d207101702c030902c108103240070603a003a800d60030303140c0024554004050001d81500000c503125041d2081124000400c1c2c040000d00f105c1000c42d068a0401c042500441400c0b0300405415011a010790003c80461401403194006844003d00204002000d036002c41c890b8040c480d000c5a040b805650351501658a4100707010306e48e8000b0048000741000c0304168014001815a503054601e131038910f0b00d5486400e4000090b0b44501d070803001c0c40c0c25080da0702009205020035100343c104445080c40741c00707901112250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 919262104 1250 919260854 919260857
    0xc1701091e020102190302060703360f050a24050601080103200a03060204030501050c18010815220513050a0b0408040b0c0a060609020918060619021c091203 69
    0xa9540c010b592003840349401141700d9026050082100c2c0c40c000b503596800321030207000039251004c0120100412801c401100c002c10b410303441001d844070f40c2c02c0c1211128000c1110185524541e01c4001b420038442d0440c440c0c007030090b03409000c80d44078000740340300030707115a00440c54603001c10010307e6a0002c18203810b40f5002841c0d10550024a000c8010a00d00300c180d040c1c0c0221088000402c00000e50014010350384244d0083c0b0060326451044841c0e401222580c0c0007800c044084403d00b94802c621040c0e001402e98108488510b998003c22140360006e2541807104843c60706a10303404403103025140c1c2081c3c2d0070314822100c140760740f20f2a80340d03058808000d000b0b215050119061101030419200605860303e215540d81e034201e04096940c0c40c442404603882420b04100086002542c400d90b031141001801265041007000d83c0719488440081c25994002e0041c0030307031030380100100103000c200320a603001060601400740d442d5121110400c1400100000c5038400e2143c000307601c09409206030705 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 919263354 1250 919262104 919262153
    0x3061602250f1e0906081902040b040c0f03060f08073c03030305090c0a030206091206150405011e030816050a0b0a141006050a1b0c170109 61
    0x89494020344807515031140e15152282c00300403580302c20402103070b50315849000c0000b40b02ca03a01e0b20404203545051042c2c10030f6420540b510000c0d150052001c44880344002d000052816a220005d82107440002404000a000107907454401c2e402d44200e80c05400d0320410130003104c1c034007540b040c0e8807405405241405c80c5494441c2c480c0840c000310060b210702040f481c0d5000b43c019540c00508407003051106800081c105070201314122030100d1048101200a00550041ca00755000e01071281d120116040d08519105010300003070b50184078103801842000d04040400c8500000c02055407010f8000b22030342c050310010100c5115000d100402125445041d6548074801c442d000007400e500790301d000c2c0250041540308010851f94038480b900c290403900c02000900c0908801c1030a010044450100c22107981d00248503990050007c0c10012060349440f0bc8000141c080e40441c0a048003402c441a20300314109001581c0740503201c2000c0b640a00081003803035607a0712805c00b12081c039800280741001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 919264604 1250 919263354 919263403
    0xf060b1f1b0b0103030203030f070f05190c020406060306140603401208010b0901020a02060d0b12030901021c09090b0d080c16050f01050d02030a06030b07020c03061602 74
    0x70000300c1c142568100035855001d40e513908000e0745a0b4000caa0124050500c000000c41540c0141c0507045444200d94842c0c0c1000c03060422008031500003d0010140b21071072100342d0060340e984c000c45004d80850b903004a020752034041001003042c05c2009092040c80240108074448002503a100901003203c40c0c080003c140741c1403000782500010301003800300406400c8040a01c1842e101d458900c41c4c607540c0d140c150340c3e40c404c40310300d07107010340d01d000350050300242101400b5140000140160301da00140004a025410001808544100c8100c8845400200d004a895078040c011840c0c010032403000742c1083d80741c041c001080e401e0b06001d02100307103685110b9002070743c03241d240300c030203003944012010354a069120000e5560040d28880c40d4240d40c0d500800f02c1c0f80c3c100000002070b400410b840b22402c16040d0792652000e50002000c121945948100020214150300d03a0240100240e802a241198151040c1410020000e010303042e8a2080211510047e50001c1c01660481c858107010070440d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 919265854 1250 919264604 919264637
    0x5090603040206090a03061a010815090c0c03040609083d09150209120309010c080c0a05120406080601080c0f091807090e1303020d1d0a030f060b1f 65
    0xa4039030300398201d2001702000c02004103075401052031201e0041e094840010440c01107400c0f240c221486841c1c030941e030000d00785500304081d8041d000003204110034180441a4041c40c51900140e21840c002241e02e04100f0880405202e080c1c0c181c040900d02d120000f40c000140d0001050241001c28207007001b2803848041d0710940e2240e016130f41d110b5088414501040c000c03c019400510803503101d90030f101d15054401d03100104440f80010103845181ca80c1c1c695483e0416242c0150960340120f0050302010030020f0824042030108442d0703440e61076219410080300805004009040c0343c1030048401c14050380f01c20b140b047c0d50108d9400f4421036911001e02000c03507201d01c0303c8003030201c0455080b4184018190000899001c1c1e03011124544c000780d5503d400c42003080d070340040190142c1c202c8070000441d1446038602030f807140540840e91002040d154080b8100380c00d0b0380d1090300d038411320b001441d0800446000705500344108403465203581044040071800e0400000000051207428540c120340c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 919267104 1250 919265854 919265857
    0x325082b030b0d0807020f01020d1b0c03082101090603080714011d030c0d0e060304110a03081206091f1e08120415020715120603120210061505090603040206 69
    0x2407030080c0020b184214680b13440010b41e00100e804030f00c211a2843d0200581d440050700403040f0400307585a540c2c2180c01c02610400c5207000e103041e101004c00403000300102e6183c030024112180400044154040301030719501c502541030308810000c030f080400c2007010800c41d03800e540300b0b035400c41a4544101c03a520240e44c01411345001c6000a840d26651300410303098048042d140b40e10701c0000303640c40000c102c1c1040b00d00c41541401c840c0d00a4007400030401040181041d04458203019040118a030b1b180e45840066070400c4c281062003110003010021a41006038080e500310b4510448400b1503404a0300740311007684070380181c0000d561810398a05501b05e903805104001d0800c07005554082046114404144c3d106002c0c844120003d8100b01da001c610003c2e0000c101c1e010245011054a0410304c12220102c442002c5428140c458102001099064401070440314154006010201d208011681565821340c00f441c10407501d03a1021850740e4110301240e01002e0f0440b4200e90300d54451001032520b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 919268354 1250 919267104 919267121
    0x10f0b0d0612050d0e040b01170a0905100c0207140315100906090b0301110405061602040b0405070201050f01242003070302060a060b04050604091a0325082b03 70
    0x500d08507502110601c41c000c1082c0903414096070382c5d0803404800e1020b01c0261806440100d001030000112040b15144c80c20b1070542101e03664002242c50307000b50721401e1034521800c0d52040c1c0d669031160184c0200d1b404000b500000d0103045c0c5402e50b10f44020000907102e5003185006a00c2186002c001407207580111005005450804000c0000743e031100040e900502c181c010b1b041c041d41c60302103208440d5100c0f00a84048841c0200080e10b000d40a40c10b612040b5036282d0120780054803440b200c0e070a6500c0e0700403584a05c0d078139400040e9030b14001100c551807210683c0500f0303072581c070310810f446401440404104401002d06000c080c0d00d020319102500c2400844402149000c0401c40c00c0c2090b502042d9280110342c0101d041c44280c2c2c56566030600c900ca207125981c0e0002c0c0803c0104000700481d04403503400916040d40210808410000c24100032401c540718692200d00c4c15440d80904c012583d09002d00070305002080700c0c69062002c8034580c0024500e132019000c003096003207202c2c3d2094010409 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 919269604 1250 919268354 919268369
    0x112180c06020a031b0f150b15030f1807120c0b0a0818071d06012c12010902100c08190816050a02070e0c1b100b0306010f0b0d06 57
    0x100e035510000251a04080141100002c0c1d419060854070141c480e01010025045083e076203800c1e0140e81c5501d40c500f000b0140d21080d80c0c8900e0540e40c150342e05c030444081c0205181150740d40349051200541e003502c0c0103044403446c14442002e6500410005500000da481103040c829811403941005901448541c2c08884a0000000d407280d4996020455a018291501c1b42d90180205011074175150095030044072000940011251050342001c2d0415030090810f04242da1101d5000070742d444c07a0242402c24210718030345d2218954003418100d86400c19050140000c200d0030303055900049550892900038810081c284114100b844450011500c0d804000c840b540710480c17040300081c0918104640c0c0a24185d10b0442c00421140100c086500d95051540649041414001020300498029101009003881413224010741c0c0003070800c0c51042d0640500074141e09030503050480903110707034030b90340c174080d0700100010451415100001070582c0c540700e10a50700c444060080c00d000309220350150700d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 919270854 1250 919269604 919269623
    0x9010509091504150e1f124706010e130b10320c0312040b010b0901020d2604080a121104170c030d170f0105011218 51
    0xc04042da512590410b260295420700c104803240c968500890600e1042c1c00c1d140b0808800558001a665200c01c0d1200811054109a58541014044180c071b03001044a4200e213014192035401c008141e610180a0254500e40001c80d00d4486d10500c881390340c541000141d055808500141c0c05541c2d0441c82c0c00d03002c0d0020340441031501e0008040c140f55050305014440303003070803110010b100d09070703655134403030b11054801045031003100c0b5101c05188008a180007040521162201540038030003000b4074804141114110708142c1000d0140200607400744032150700c100450743c05c40e60041030180c280318880c1070520f0084505c100d1003c20700450741c07903c1e10400461081104000a810207401001b100790ba03900d007018041d111500468000c1580c04246680c00e104c00c206103505e02030500d4100f01c0400507107500502450202c1d1400008a802d040402c41c442c400c081d0078114660510341c04403003e1040c0d02154036000003c0d2801190060250702c6a4481c8401c030800c108440094044650001688 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 919272104 1250 919270854 919270861
    0x11a01110322061103131707090e160506040509010501050318100e0c010f0e0f0409050303090601151b0f05010221190e0606060309070902040303030207030f230901050909 75
    0x9242c00c0d002070183c640421850125580b00400c000240c9101520301499281e40d5800d080d240c3c24400c0b03c0c2c281d02c05070f030301c41c41c2804245105140200c40c81400c3d400010100a42001c02a0130000c400350840d502038002400100101d60b6104006170443c0d0081c24a0b070b80e282c0303506085024085515a2940b91482045180c81c0c054031140d20002c51403541e40255030138024030000469002031007480c041c0000394500c0c2e000a5601d8000700081e108040100300280c101c009546e05d60440d0002c4550b90107981002004010f081702030075502030045c40074503005641020071a40c108000e00618400703840d204003448003004000003541111a03603000c94917030482c0b8030030604240000745001c03942d40200c5c540300004290780c2c1810703001e40500440034901600f001e581e003600b8000300345c200600c0d00055202e00400000c210300720b40b0042010b940a42e4015a4400850402504401900e40100c04000480c803070b07a00e03800d05034610304480c5e844880c40581e4072810640103c070b140c02215036082e0711142d400d050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 919273354 1250 919272104 919272157
    0x50601060e010c121701090212040303020c01020903071401200d0806010c021306050f220903020715050a1707210e0102040605040305010e07120b090703141b03011a011103 75
    0x403104600ba165161758260380724400c02081c3d0203641d0008042480641c0840d00003030103500540721000001c80014104003a55000174030b0031080790700032902d014503a4802641c2d541d0080c0340c02c44500142903490074007030100100c1c030360751400c14400108000d034480110744160b00c0b070761901c2c2100d50001c20191009400408640040441e03110343c1d40310781c0390044080b0ba541814466a100d04081000b2099a040048030710005008000782c102c007103026551010403800c0d2809000990000950344082c1c940813083c00150040f90f0844541c0880640541013121644c0d000841d01c1c7e61780c0e0300044000c04010081c02d2880500000403408150b03500120700070640e10390185c007810440340200000e0022044580c55992100800d018032078481500b01740c0000440c60396003c032904500903000f00c444150b030b682c54416008081d420405015003040030515500c4122425104151358100c000f04116185c0f07014046500041c549002e05000042c11460090b950920035904105d201846040364600071280 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 919274604 1250 919273354 919273367
    0x18150c0105060406051002070e040206040803040f08010c0c0c1701111c0614011403130609290f1f0504020a0507140a08030123030a060b031207050601060e010c12 71
    0x18a0b0380101d1500c0c800082a103001d142008000c0110340140142c40d003050203004031020002e1099030050010000018403010400c000d0004100030758041c50340c541848042800d650302f02d8075500410008005000102d02d6421205040f58900200491391f00700002d04140549070802c020a082040460820000c0d5500c8006040d80e200b00c1d00108200c0f81c40d07441c03140785c004c50000d0317040c0094080a01510400b60400c0110f400040021480100b1040c40d03a803502603070f400342c408544100c41200056210458545442c054428105501c0403614205400c0d600e0f403180100300070b640003102c07000040d02c0d89100c111140600809401551703100c220040c0540940c0c0b0000c01141c03003400140c846c208810303009c561441e031207620902c0c05146910b0400d8003035004001002c101080038041885034030640d410000404c3d0184600340c0410910440d0081500b050307044101e1744101e43c81000741c200040c5000c103940341075a13414200050300700324550040714200f6038840c008050f141484081c41c4031617001039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 919275854 1250 919274604 919274611
    0x312101a18180712020309060c0307170a020a1b03020c010e0d200306181b0406090f060510020a030c0b070c050303180706090b1e0d1a18090318150c0105 67
    0x320b46009030184240790713104905c4112201c0c40150055004900722520100003150484454034100c04003421007009000012010741e08064070950010700e0000c0150402c0070500140840b501d80c81d240710f1035840181d10fa030000c3c1030860412001c400054040d941e9054804113071608078016180110b040504024128402e216151292084500140c2c0c207107084d0100b90540c0220401400780600d08000240000d0261071b000303a4040d07107c15010500c00c6035482000c288190110021550314036110a0180040300005000219080400c44102181c0c01840d0420440e0340a12000596035403920212031840c2903c200802d9800000140240441c2415240001a40320020b41d06815940c10007658044882d100b00551003c0600c0752840c1121100118441c0e4451040c1c007500e04088284e400c42210400c61500b51060085604842c07141051404190000050100740406041c034140095a0340101e504420a212404c1c0c85810561118855005200204000e40e42c440c0000d86029002e00340c100c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 919277104 1250 919275854 919275857
    0x305040816030c1401020304020a0608190c0c020f1203070b04021804031d1e091f270b010e10090801020d0e0115050a09110c0f0312101a181807 63
    0x50080c0182813818401c680c0600d80c024404a0b415151a40960b41820f004151101841d0700c661440c81007070346402240d00c041030070340d103a00d040c05040c41001074810180c140903009060054405000e5040042290f0107560006241e464540d9144000340070805010222400c040d110024030080540000501041e10380b865000ba81400c40c4905014100c200410810008980080c00d00303020704001c0c0e02c2503040420030015001114001c172210305420510351040480030118800c10030480e03a0b0340c1e91548180d403030710003d122103481280002d01000e1100e400703504c84d103000510392003000e005040b0640104000c400940d180c0102c1450000203260600d4505115403c0640440a00300c09030b250030300b41d890043c00351281c90b08281110303000f0b00c3e4988802086200420401d000382c1420821601440c001c00000c5a0340d0f0b40241401a074403502800e40c0300410081c550a000c0741d21440c9a40c1002d0000401058482c1000c04e940404207503c00f900c1908124aa09800c0d030030100441150b01c2103009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 919278354 1250 919277104 919277123
    0x6050108010e04030206060603151f09080f06060402250f150504030807051b0601080a350d0605130c0e010c1121031908010b070b0402010305040816030c 67
    0x3039000b12a54850300711402001600554001a010304d07281e40516003000301c96501081d02150740001c41e2180000300f04040c29800b20501c0210070607400041d20002e00345107006031803425080128190b5940002d4040c40c8a0394000c42c00c03600d13400d0102010071580c1000d04c64050541280d082061102e615142e00741c1b041c10607d42101d0313692807140200d500943d4507a071504000d03600d42c0303402c031899085100894015121b00b990310141113010001503001c0d00d6160041c02d174603091307440c0c14070004001c1d0072156150001010b42401d00c605214491196036040601c069450030483c0300d0b02c00410107130300010703804900ca81e2412080035003a0310804994125441744c0c1c0c4020302560040d1000000e01100401c003491003032100320b003802c003c1c01c92807500105210a1001c00e02e0004001d09640200316604515910a0b005031070003944540c0b15030042c030301604103614010080e10340303a1400380000c201a060580320740100d0100000d01c0102c3e04000b0000c2d0305030944030550b240051007820b90040641c0c0000030f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 919279604 1250 919278354 919278359
    0xc03060905060607030e040f140f07030908071403130617090c0d060b03070b0a0c211202090a090c0315050f0319050c03030d0608060a090309090f06030206070302010605010801 77
    0x258800e26002d004000d0290b401c0030302c2680e0444040f4135080035a9000380d2076400308201c1a10300d008001031740d036552404c803650303280a111118040100a00c41c500309424007038902c011807c884201c2d40f240390412250003400a280082d00c0c076602c03854940001020201d500013890540c0a103074101c401d64541c41040d003688a41000ca5641d0040e0008190310024070501100021060341c00a40e4400300078007542d441950b29140481290007560440700820054514a03040003c05007d17058100140e2181a5041c2c01200f002403100d02004031340300c201175000803008106d030b07907801d80b500c001c0c070741c110042c41098407a8000401500078500c130040700780103241000c1000d01e400007540c0166080a07005100d15242c160b1160040702040205030342a0080000c00403243c0c50030300080404410007200460709902e41100503140410041c03a800070070b80303040ea04000003680142018100c91718600e003c5400d0000e001c0400c010082c540c4003c0d8005000140401010b406406c2181125002d8881c1d5009a0313 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 919280854 1250 919279604 919279619
    0x607051902010b011b0606051809060c03040506070804020f13020414030f03250f2d0507050f060c1e0d1d06030a060b07062c07050d240c0306 62
    0x65401c0d010700d0200d0000301154245d06410211008424058540454071950722004180c032040e4814040005d61442c034208125840200891a082040d00c0ada841c42d504d4951903d540f10702015020000300300400020a06644d524405070300c61440040c150782d04c035240184014029407241c80b4030300007000440f568001c1882c022a2114035414404007841c548800b0701c902c030141220b0302542840507007142c4004c0000c1224000640070a03449404085401907a621003548a40310800b8060703404860203e1000001d0b5011070108100c4500340e80b5128044048800245240a18510a4030901c140c10044080107141d00c483c8624405000581e40e40301c40e00c40c400c68411802c0703e41006805480b600d00317850760138505c0045511141d80c42000640c6612950207020f6580003040a880b200d46501101c201d000707840624403442c0d07a50030540741c109000d10350381607103c032918841c00703100d84030b0740708001c0a00400005200e402c000e942c490818201c0b180184d40000e00b040450300300000d141000204642e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 919282104 1250 919280854 919280861
    0xc031615140f18071e0f35013e0f0d0b0a06020115170c04050a090506010e1501080408030c03040f170d0e061302010f02010b03060705190201 62
    0x1580744802200c41e40d5940c4507000414405030001c0f909401011068101410a000c1c0c1c5000e480043c81c265051481450300254002942d00201844441810100811a08011101120301d07540176865021003441d140c0c5071900c94812095442c5508101c4440e0315600001d03156090719003140310000b10090b0f1051102808240d40d4144e40a500d0204003403a000c9001c4005001000c00110002c10000f4814020560107030035a4044400350391165140c2035032891130324046001e0315119104101e01c0c1106400b1a580d400400b5a140c081c990307400c0800d103404016000007042c00c0d0401d04503800c1c0d50755421440726068045a01c213500501a0740c00c000690301c5000746c0790045400040c40c9085890341e46d980c0324194400703002110340843d00c00540c000150041d81c2d040c030385100984c016448401c000d0030841507400101c62141241c00441c100301119500800310302e040d81d028a0b010f101c4404074182a401025900e0b803880d418401c80f010042207a030b00034014060600d07900c49000420340d8000302030703099 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 919283354 1250 919282104 919282121
    0x3311010c0c0c1d0c1e07080c010b04050411061c1506080108060f15030f01050703020406030b04093903060501151b120306030c0905010303180602190204020c031615 72
    0xc501c040c034081200c0000d641c000e0300098401703aa01d2112440000c85181980c0d10644088862950201e0a54031a90082c0f040003807200b000d0310103200d07600d8182d5402c15400b80e04131a183c440c20004c660900d5420b071030540c2d60318800e602c41c01041105101300300ca881c0c01c40e186c0300d040002142080017098280c4046162401070090260b808001d0b2121400d01c080c3c05100d14500380c01d44203c0c2000101312000740240d0340110402d071001030760707076086c00350003000e540311070160328041c5080c110400001440f03d001128415484d40500c0c5100310303446999050041911410721030302119250110034080b03181d01c600e040b1214030346240c8204000740d4044d40c0302c1034280342c03040d807619203910b815020444d070611508624140c6e15001400b80e80302c1d95506040580ca0300401c0220b45d8a4006108058001500308619159902c0707860301585040002903071046041003441c2c2c8150b142c201e003011500c4903010740340c41d165010166501e0b5402550341036801e19070801e068900d1401c0840f0138003a4207007807007030000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 919284604 1250 919283354 919283399
    0x11070f06110f0708070201030b041805070f050307030b0702121201050907030e0c041e0c180605190f1701120c050405090d18030f0311073311010c0c0c 66
    0x30309440d62180102c9405c404400e0781850b48403500340c601651103102d2000f000e00441c401c400c91600c0c1d82030841c0340100766004504500011007040c04903075400a007140c1140c1d4005200c160581c0c41c024200d0038012024031051440c800428481030784110030200a0507500191000c0310036a03a01c3c0c41c11000d54803015103030b50280d0440a000002401c0c640c10880380410f0182c1e03249208409003440d07008a030810281a4001800120b10444524016a480d8000d10311441c21508001914840f20f5440d40c80000c000140480b00c90408200740c0a0601c3e00031101000c1c2d9030100a42e59550380138188106070301c00301c50031110200041480d240074400c0b58060721184000380080c0040e8402174580c00301345241400d04000400307001000074040d8800194142c4a65104a248082101018a0205190000a001512a04001e42c0d4001035400810a20500341d41ca54040880700030950f44100c1c0c110401001c0d50a0a0422591030303040640032003624030641d80440e144c0e81d42c0d4000300300070b400c0500004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 919285854 1250 919284604 919284607
    0xe09040206040303031802090901091119050108041103010903030c2c01120b0303040303021509010c0e0d1a07030b01170c040b0c030d0e0d0806011d060a020111070f06110f 75
    0x464443c1c0d11a110070f00c2207031a8200b104c00b0030b40000701192400c40b92764100c1c1c3c2d1200f01081c100500034101d41d4050034144c3d02c140a6250b44060910528194042c15041001c100002010b12011000c85803d8107000380c0200320901203401e004000d44403c900190115550004940e5502c1c40704915040350200e900100407000c42d10401120070000501c0144c05090f22407812001304e5600303200a1008500c00e80040c18001d151590800c42818010403507400f9914001c8415001078009161005c540e03c102e45000fa10791980c43d088104056011b16a2203280c802020400803580540c41000c025000340c89822103020405102d801d00c00c1300312650007080400380020002040048042e1440f900b05d03000352820031482055940484460313010400d000c0e4065a001303001140c0299100c0d41004081ca000c04400c03040c018020100100240c0250184000140c048000b40c800c0d440407114603042202c15981d80440e082c91204103614141c1500c095207014014001860030804030b5a50000c0380400d507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 919287104 1250 919285854 919285859
    0x60c07060815031204150c0c0306180f03110634030e0a11010e09160e01110a030509040e031207030b0312031f09110f0c0a0b090604030e0904020604 65
    0x2158145400340a024010b20044100c4803155070a0000300715500342c5004450304e82c1e01d1b0111603100c5101c0340034030700705001040820b00e001c6444c0103a4441541d07008200440c4090007040c035880d10b034000c00d0018103001c030154221020141d100e00000c0d0000d80780b1080350880d0303c8010400b840341c6915402c4800c11040e80d040d140c00540c8154141c402085035090004000c40312080d00c0d420150a02011a452805038806c2d540c6580c11902c402002c200070345600ca10313441e2402c00d590100b80a1681c190600c0784460124089a10940038960707090204400d5802c0d40400746000382c8603410203452284144d040119802555000105964269127071089910164076a00703030503402030507050641d54150050006510403040039000943c000c0b03901c83e000c0383c800074191003001a00340c0350b900a43c00940c04d0820b070a5140c0c040d84195504030004540d045c2e81c030010403040c145030810035a001000140004100300f995003003c901c0c0c41c400d82c000c1d02c441070201e011004010b82946d007250b00960100e403d0105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 919288354 1250 919287104 919287107
    0x1206070f080c0f0415030509030702010e0d060f062c04020d021002010f051801242312012408060a0e1515030706020a020607170d15090b060c0706 64
    0x11a8000c4070b11010781e440c00700380141e8030308143e001d508800844140310141441c2280d140c4903135503120300080d01450405540784d00081504c2d0552004600c03e400d0840c0e081e042c081c80da80f10141c40e4101c040f0401c1b42c0343c1e5402a5040a6540034400c070500c002c1000e5440c900129100d98a2140303a0060212881c04160b50030880d41c060300142200031507594100d0000002854800c480c080d102c60901d404001c07101c1a801400d40d20b500340803141c412441d02034121000c81c8419060b06803540c0001314000c0b00d448022034000044000030300ca40c000b403041c50800c40c40c101940300001010700701c0c0e180750030346084c0d80c83e040d0407280a204010b050f5020313500240382580c3c9584601c0b05c0c0300020054031050001c08061804000056036002101c940303201d0701e482c85240800281d00244018006000688803d03000280c4500640c031003d400c5001c01d40680d0560b000c9141201c61401c2c8220040244601c030941c00d400708000307406040901490b001400901d407238035009880500d20850020a60181032400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 919289604 1250 919288354 919288367
    0xe030c0406030b061c0f2d03080105010813050102030f0f06120a0204270506090601090b031b0103060f060e1003050402030309130615020a0c06050307050a1b0812061206070f 76
    0x880405000d45245d280000c0d0905181c4001e0a00519055150071540c11226501c041501c0b01c0715611300c641d240340000250000c0404d811100c2c242480300003580d0307a9064a501032400c100081a5505c000200038000d0b0240d00414091008144044161b9840d60140308003c003000c42141c80c0c0354002004000145019000306424180b50945800e240c55107904452010811400480d150781150081000950003000042e00410b1841e0041c440b01201201194844618110b005081d010380c602c51074003a4040c1c0c10050082061800c440d005545d40d801c01032807075444886542c407400803513000c10309441c030038016180180d4000380614034003e0404108500590800c0b00a003c958aa01000a0800030000ca0081900301c1360080e0040e04460700e80302d801004150000c5061000510501051951001c00d8844100c41401c2c00d41e012004195200c42208041174002c0c0071400004040030070866061025004903003c0c1c4103510341c100602c0c400c2d1784909089030414001040300c0181300d00c0610420307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 919290854 1250 919289604 919289629
    0x3160312170f060103050603033108060c0304060b01081501050706141f0e04080a180503550305040312020f06160815041b0e030c0406030b06 62
    0x421500d140c02140315a0307803400d822076040b850b203000842044020350305401042d510010031409075181000000c807604d0b00740c1c0c0d1030061003540003000b42e40100383d2009014006c0030f04410b10880e6014a8400c0c03240c2c2d03040d80100d50449805040c8140c44120b1750184d414503000d40c2445150310209805032004581c940c0181d2400e403103c6884841d40060816070f0368145024180e80d07401b948581000d81030702815204290301800003892918200000f0981c42001d032002c920aa10f0300316030800da010800001c0e43d034103801070b680c14011041c151403604045c102e10740700c070b1500c0d00e103003454040c15a818014210f40c1080160307a2414074140480914450000d400001303210b41411070a154480c0c441034401440d41d100b03140503a0054401302c500c4142085003683c482200b0b543d0700c01d4442c00c840000c19034000641444040170b84401740b82c0059071160802c4402000507900384061090b00b0900a210302d0b24942041d02034000c1c10041034031400c1c00d02503042a00d400141074500da4845070305220a03c050710 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 919292104 1250 919290854 919290857
    0x242203050706022a1c020a033f030c0203120f0105280302060c010905102c0d0c020a171b04090203070e13080403060e28110312072003160312 62
    0x40b40e20170016035130814484040c5000728001a15015480030007450b4448141040403012321071680700400820401c440360883d029480c0120721000d031204180d245002d800d0040c0f9504007180d04202000b5039905010b8101c86c03084516419208140d88816007113154244010b0000511450900c09400c0c100c00a0980c01010000000ca05040391226410541e45c011100d21007078440280401501c2071010a07050420251020000d030012102c02684d65004d0085110a01050154290655640260340c0008003840000c0500a140c01c046403601c0c2c400c2900c0c0240f50001c401100ea2007410540304c2c01035440e902500400900c2c0c2000c410110142c0b00400604464580106104c005060303200a000203521504010a41020200ca42424452039000389a079134072040d14240d040f01085009900919006031200960f1045070010908100700b45070130888440c1c00003500400c114454003030b440c9a145809480310441000b1080640b143e0075401000078541e84a5410b0000c140c48104c8007440300e246 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 919293354 1250 919292104 919292149
    0x30a030c05031c0b04060f06171e0403050a020607020609030403060504060f2301050405130818150409050c04030305070b070c05100b040b242203050706022a 69
    0x1508403041070040754034400004a444d0322204415092034040c4001034008a6507420750181402030041c0105104070202c0c0d01c3d80403200204480c1148003040104c00e600c03400f404c0540e4134050502903c1d59010180120040c0300e44000500d03540e1020407040d0081c10004003841c501841c41e2200c5025200182081e212a81c0c0d8207000302200e0b0181c4610403000030074495504034002d03102c0448190f600144d00c036600071418402006081d0024031040120340d03500c10442c1c0d0303c0740c82c40c01c0740081212420044541140d80b45a4003840c0000f580003030412522582c178188400d0782c40761210001801350b071100501044082c000a40000c440744003169022400346031002d4200002e071900c2c0d181c00081c0880ca2412541e6001100c114100b5004a144600c001e81e10b81c05041c48000c2012845183c030207130400260004628050545608510720742211001c1000442d600e440c3d04003e61521641d1041d1030240c402c0b8240e40241210356142c60b088141101182d510240780c0d14140a1810074071410640d80100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 919294604 1250 919293354 919293367
    0x10b03150108070e0903040b2506021b0705030a06023403031b0921021f2d0c02060403060c02010617120313080c1c0201050c0405030a030c0503 63
    0x60030003403181000d510403414140303945400410307070030660950040c0301582914420810400c02c0041100d0441d110017003840da841602c1118400041d002c0390340d204d170000e1541240d02c1031142caa0090050300c0c140020441e501c2406860940d81c030b0402d44a2140c1681085512070040340880e406000c41c51100f8004082000c01444411408469111101a0107000000010902da454811059080c10442040c0d00340c001603a806405962980300d00c0642000301d0842140030410b4503045455079602910303d220346c420139100c04030120780080381031001a03180e0a01020762403900170060000c1e144007102c8104941d0804048070308000c1c00790140c0e00518100030010000d5014820035403c00303525400040d50703500f003040600603003003081a0400f1550000140c81101442042282d80103640440f0303140102103035142002c641c2c001c0c40040007a60140d00c10052100da503002200480c110346900070412681c580440d28090300071806542c1e0540d00c2030a000d00001e000390344ea45c506a0007001224204103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 919295854 1250 919294604 919294609
    0x4110f030703020a0e09150d050c060a0203040911030106081801091a0406050702030406091809021008010e10141002010b04051e0a0e03030f190906020403030e240c010b 74
    0x5005903a600c0000fa4002030440c15507501c01900c0010302ca00311690310082c00d10a4485030047c904c1561a4816592031644104110b001c0025600019010300002d40355500010081d4480d0020310541c41a54100321400b203446500c00210390507642103884880558950b01e07450441d1243d0030402d25419941d9804000c0420311f0010b040010600282454078a840c00340752203c244c1e02c0180ca0003055505c03e01041c050160000c1149082d24440180000300201c80481080a40701188000e5084403400b1805034400d540305c480307030b07060704c9055103241d609859224084821812a200f0103502c080ba0b640c507240607140908664010f86918400807528401e2400054100e0703405481d4074080103042c05a0300081c54801c420281d0100740903008010000d685c8294039100d100040a096003130500c403001441c035800e094220380c01c1002c45c0c0000c0002c401140b800e003000b036109001c29000301c1e56604480000d131030004600100d14041e06031508035041e5460040d0721541003030070412500d54a4206000300342c3c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 919297104 1250 919295854 919295857
    0x170412081620190e0613110a03060e13021f031508030408150c090d020a03050a1b05040b0d150905010509010516110601050603040312021210060c02030c04110f 70
    0x102c0451502150311041c20300b0400702c8201d642031401458030202c81001007012000d0002c0c0d00800036248542d00340c002c0045a0018840345060121030480800c103075099941c0345c0e1000c0269451796144840503180c40d600c6419903d18210001d5102208110300241c0c502481000e14068040c1e0a020401d0105400103090050700ca0f0007001260340081810085040100b0600300225a035000016550604c00c4250200d40b00346070641d4003c00c1e6045084085445020040e401140c0180550300e0744001032034440d02c0300031003041c003406e40141d8040c0841d851170140310b04003042c0e00050508a1070041991003440003a0145002c0c0e440994681d07042c000300704280907072849088600000141881c10654420744084280c1c50001040b03000005030070b44400000342c0505503030017140d050b42ca23540c0e07074a030440380c0d280c001024459090021503825802c451004403540619030310b00382180f02c16241e80c41181c20030081d041c081d44c56403000903500001d090a52200c500031180c1110b25107044082d401c0783d4200d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 919298354 1250 919297104 919297133
    0x120d02070c0503060411130c09120201020a0807050106050301050c0910080c160f0b0c030c2d04090b01020601082d1c170a020304030e010305090c04181704120816 71
    0x300300c0002541c0345428020407207d0003801104201c00c25030010300900541e071900902015003900c800b944c0c1968000c000012045074000140b541d03800c000e203231080c0a000301e0b1284ca400b13503003041c0106654803035000a41d0f204100c044d1404807802203a50b0111aa2580a411003800e0541007145244444881c40ca017848940954070380d0100018a1420514800004011200e0a841802880ba1000d07901c401c6500041d03010805848015240b4001c03486001c0c506100000c9013800100080ca02070b464001c1d2402400907025140c651381d0303070000e058079146103003c000c0031108860441c06c0111512050003010851000c215004006500a00303c44041107071943c0000c1313001c4481002c00c0804800515a10001203102542141440e540c080c0040d03100b440014180740e1580e0000d0040b060421004c1c44041c0002d000b8000010740c0e81902c50b00b240003035010750350707500c100d01d0041e10312200c0401c031411607000d42c07603010301c0e0349003030b25440c5081e003100740480f00c4001c0c854014000700307416810f030b40710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 919299604 1250 919298354 919298363
    0x50f01020a1403011d190203011203030b030a050c04090f171306030b0306040f0305090d0c17060f04170d020f0d0b0d0201020601032009040b060a08120d02070c05030604 74
    0x9940c0300c51000945450050805003001401c100010710a900d00401a4400705e82d020410484035180d880c0c007a128800d408200c1130005101000010b100071103448030f08502406a142000000300c00800c1c1526803854550182607075004244c041220f0419600c42000e00f8003401c1002c6540360183d0313558100018a009039140040c01256900641c00051a180000c040d035080801001c000d5402003901c1c0c0e20018000ba01386d0300190011402c0c035029008a41d515400240b6070b2481c8071152a0020000321a4050003c14552200300c0d002d840e2800074100380164258140441160340c1c6590b400100030011146260340710051000550007030080c005040403d002c946031984035806801c80d6012201c607413000501c1801c130040d0704000350b600032512030305403504114004805003a1040c4541140c0010f4841500440c544082100f40300c0d40d00482c03070041304201c1d84286a6980e46d00f605503152003202c0b45d00c3c0210030070070035016440749603130091030040e22031278200c1800c594901c002401c1403c200c40698 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 919300854 1250 919299604 919299607
    0x3040f02122505120d120c09030f05010509120c0a0b220f0b060a031a180703050c0f0904082b06060203130f140f0d02061b12030c121003050f0102 64
    0x2c245851303140c00518042440c000e010490102e10000c2641e419081d4104030190344402120b9007610484040340510741002030003201140da0715010b4002d0000b29a403002500900340c00c0449022102e04a40746040a0401403803012002d40342c0c40c1030703540007a154010242c1190702a50f264002c407800110114051440050500c0203401d0040040f10010034003845807012200038000103011110030032007110000e020a800c0c0e500c0c8614100e88180e007101c030103550305c40c4401c000200800059010781d401c80680b90308594440a605110709250251001006030700180100702005054a02601c4070f1003182c80003501400c80440041e044412a420900c0140c00000c7c10710201100000300000a1000c2402c5107419071908406422001010aa0034810061280c8800b01640c0d040711450500341c000f01050303a500e40d1001c40c3d1803084c40140f03002c000350049856120f510803810080d24800c28694030180c1c60036a642c45400888a0000d0a00c645808181001301c0070910402481038520348040006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 919302104 1250 919300854 919300859
    0x91c0b04051b040b0a060e01110f030c0f070e0c0a0c0b010e2203140d0912180603020304020109050f040e010f05240d0b27100e0303040f021225 63
    0x2105031102c008030b00c0c015403c22000101c15216401c0b90401c40b0340514100342c81030500c00040390514620440740e0a90b202e00e001980001d403001c070040403100d034802d08684010a500c04181c0c0c0b900440d114a101140c1c110340000c807054000f00041001205034a05924144040c0d52500300c001c83c00e0300012034001d515010000c50443c25035182c000d84803403948403400e25520f5170703000b03044640002d2a00c03014500810706c805580e045400c48058035500c0252030552300c0243ca8003c143e0381500d50503174245a520315001400d80e000c0d108880c05941c060352200400c608000c1400110088801d2040d00981d840c00389620b0304030b085c41b484075800c420010200d202d00389540c0000403694051500c00900207100e0078640030f59603e4204003546036104601030400c0d5203180c0d400000001900070030f6a040c07030021201c00b0380c2d0008a40d0880840c15070108100800c1045145956400300701e4004080c3c0d01c0d8101484094509a21132580388030388581240c500d40c0fa03203207080b401c0c1000c12140c1c40d20317200d01c103406 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 919303354 1250 919302104 919302133
    0x903170106030b030c10110a050c030705060a08010509071103030a09030e04060803040e0907030b042405060108040f02063105060703050d180206031303080108030a05091c0b0405 78
    0x2240103000e2440c09101d4005908002030301c4000140391103206a141c0988040030500400507503560040d81c0056950302942420000d1321840445c6809102e801b0f0940049240d00d07080043d503002250958407840603030308000500c040d103500984640140900200c003050551004c0000f10f1251043c0b0501140a400500e005420008090b03545446142004001d1021010000981d0211840840c150307a143d00e50920b02400d2050399000174000d8980f00c1c042009100e00d84410860980c01003484a0303c101c48a6400d404861090b50030303600082c0058082008034501c09d00c00e03c0c1d09070004014924003147c010417413640801c242411000a845000740d0200c291440f282a00240000d03a03413286040119500101180700380d517018280140c0c1c400020600c20207036040501c10039070140c0495600d040c00c45403003481d200c070200c0480c009410040003080400c0080203075040c442c895210142407003010f40400ca01041c0c10108180d40c68801201c000109510745a100e0281d4003da019040c01c0608008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 919304604 1250 919303354 919303397
    0x240e010b0307151b020a0323060603070f032405090106030203100e0303070518130509010c0905010f2105150109060f200c1009081908031807090903 65
    0x5081940f401c41500002a41104024901c00a602c02d558407503e2144001800c100b00c6400103007151007000101101c07003038034000c45a82e00110b081101c1c0c842d0380e0041095500d00460050058050050400300300003000a20146440c1c0010f00304806c8107403400c20010129034003180c2c0d03400103a4641c4020010350078284562044051484014005a44070b0400c0c540d136880050500d000b0040c001034003500340385030305442120745a00102510780b411040309440c1c010700420b682c01455940707843d118a10032405001c02000700c0301e06840c0c800c45850940301c1941c8244458064480c0419058040340380c1801c6445217900c64500c440c561026031904500042c00080c4941040341807000303c000c4c115010740c020980790513a4100801402d01640404030311030402c483d450302250000442000041e40f9a08400c210041e22420b000300c0d420180100412444083e032280094125841000031852101c00b500180500c1c0010781c0480d4442076072038290740d089074801c10302a000141c8004012189203807020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 919305854 1250 919304604 919304609
    0x1202160b0301030804151709011e020304150209030a020a0b04030308010e0c030a09210c02040c02120702042003040b0907090b030d030938070219240e010b0307 70
    0x205041d04640c11507583d0b04640c41a40101034400b05d8503140f81148610a080307403118101220b807100c0c0b0303a04005003d60f0180c4620312107020710101d2038a4003004c551a600c01c0c0d0740300304d8000850141c01c501036540c60b0003e520000400390503000300300361180075803281070841e401801d0340107a441d515440e5080c0104600c01c1a0010850303040a041400f0b0206918070a413904441c04420000c0c03400b07180d18107556120141c0783d025000811048076102241e400c001d10b000d03454000c0c6c0d424403074a4000701040781c540d40c1d50320010100d01000d1042c0005420700760306c0101c04105000440d07540300b10850303024580c0d40046400319603400d002001c10081d01304c14042030005040b480400d10290300510b0010703854040c0704208604040c0da80300c201c0300744500c018190850048030324104044010f4000290304500018400740038100b006400714000350701c00503241465036109075054802028550b20000c0c1c83d0341c2d035120701c0605105400a01e0644a0f94420080203c240c0000007400c400340d8010701d0304110955 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 919307104 1250 919305854 919305869
    0xe060708041418180106230109090c140306181609090902010e06071a1807140a05190510090303110601180213080f0a0c12150f0207120216 61
    0x1200100100e03480035526074100f108052034240b200d585600d9117004000903407007400000c5c40114540b41e81c0c00d81c02e001c9081c03000280d0f20110341c1341d162910001616400034080c0005411142048001240310000e1900b005000f081c8640b0351406150582c0080c4007034824010245200d2821102c19410104d070100500000100f4060701280782c001034910703200e4890160141d030000403800200060f0b20a002c04039030b800c54031040b260510031106441c07204030881c0b502c2c81f44a0f4400c007090403881e00120445101008050111580c24801400f0400f103603001480f41c042015000803d155482580c1040e62940e0342d0340d4100190b01e541001080806104105100e41c1c0095005021807100f244202418083e191b1001d641c400c410480300301010f44551200d4250300036140700255130280420140c14503402014400109911102540721900590b80b0041a0ba83c03920700c1141081e2098010604030010072000504162080c0c95400b1420109106000103801001044081d110030700017040161120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 919308354 1250 919307104 919307119
    0x5060618040203150a02071a07140f031b040801020a0804061107050a02100e1203180108011202010e0f12060703060617010905100807081501151b030e0607080414 71
    0x7640100741c4503034540c00320406a81e94400040c02180b0740703404640300c881d4010b80c403580ca000c84c0c03200841454410754000000407542c44091004c0100078003644d2050142c1e42ca010f1850303d580f071801d860036854040c02202c580041c007000600705400c1c4050415002c10b0340707525000b4502840e02000300e807402156130289620a0094101281000415140c0c0940c181c1e0192180640d000c01034442c9410514419400048011014012030000c8042c0001c003a000380f030b8560b000c42540054600c14024080c412002c041801c220001d50b102c7d2000d000c2c1000c000e0300c007a00b041880c02c08581030580b150407585059019400748100390758188290741c0240b0151505030700b20f5550795984504d000040c403030904150345030700106030f038440302110078001401504100c50560303941d10040c2d52680d1410922070780d50b0350000c1c000944151002c50384c500c000c0259a4213003800100c024200300d05c0e00784100c11340411240c48481078890b00c0e45002031414900450741c4540311072601c11419542c01c5403200c07140c0564031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 919309604 1250 919308354 919308361
    0x13020a0206040620211308030a1e020a270b0708070c05060304050f0d140712090807140306060f1f180e071803031d03030d050405060618 60
    0x38085400740e041640014085090401d04a103a42d0440101061000d580000201d0b91280c581ca144070701c06041301800352100980d00c51032140480c000000001c2e10010003000040c2d1105400d5004042110300d81400c400032850031010003040341c02801892010070313802c61180340c0c4814007001e20700d1103030301c14180c0e105002e04003100b00f2154020903100801c2549e001c5a5a400c22a0380d24031000501005084039880e80b41a00744107988d180094140561170055007e0400c199216896030380084011502e491310b401150758a03035403114101c208440401c18109004a034a2405002c150700411050084180342181107040508018010309284c6c400c400b030071481203190311544440c400d003c03480307261560525004802514400705402c00c010380151030640c04030300c50703c1c0380b0308040c0510001d0b40c944170031080414912241c13501a000290214841d211080c4560295102099407400058152400c3c0703540044014240c54042c1c0f0100c4464101d0340421210741442010028035030702c108a034110504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 919310854 1250 919309604 919309607
    0x602150705041e030501050705130b0304030c02131b02070602070902070c0324091b0602010e06010e18060109020a14040609060c03110f060603010c0c020f0d03111002070213020a 78
    0x42944501441c3c00d1000341c04214148034501040000c42e0032030000d110174a00540020280d0344030007400d02c0d040e8070f481c4010030411f244009030ba10681e41a1640c0315103103043d4081002c05640e10805c607126070346400183c000c03155940c420380150f0040d03800800c0101e0074107034040e0401c00c10790003011441d03206100110105261a41150407660410100c5030f0740788200c20420741400d140241c10740c03c0d608207441ca4041100c084245030b101d04041900031003654a64030700301d090300d03100701560b9000e60150006100100c0e0400c100c2d504030305e05000640036441100b60940c141076099100c00005540852503181035a0004030082010000280503031619080900241c41d00c18240103031000c008000660030201806680c6207000030100008407036098009180e401d50f03036042155560f000b5424070769403060f000d01450180e590182e00429034600102074a06001c4074802441041c0c0400c080e0b029649020002071010340c030346491000c4056030b10b1049006101d4000c600c50703521120a4410401243d000b07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 919312104 1250 919310854 919310857
    0x1b01020d270206041e08160305060c07030c20130b040b0f06030708090c0d0f06061a070204020702030307060c020a050d090b030604150308040605041a04030203071701020d0606090602150705 83
    0xd1303450328407400f24205640d0503a05e0803155038200d00080c2c8901845154088032081c04002180d00c540d085600b55510780784542c0703d6001d00400100490f05131403002c8001200c041d0090841c4410842150301c036900da00001d8065030507480383c102081d58580000c0c00500303141c092803410140030b440b8014000600c17404183e06100040500080154000100d071031040280310b40104000001d0240c408568241000c540413010700b0783c00c40c0d40ea0b20f40800010720700f851001e4010719058800900d41440a90f800b480040d50046400f20b906020401a0100184107441802c005203d580d0040840182a162241c644000e00c8c4100c000e00031900c1c0100601c82c1b000040740e90056081d00c010880940380a426035104c4000d8100820344000400c0115070103a100010b04120390000c140c1000703074845216841303514811804082d4041e0025503082c080c01011084800550f0801d400040c501000900042e0440c0d5075900180c000402085040101d55410003540d4001c055102c1d04000300d041002c0007034801e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 919313354 1250 919312104 919312109
    0x403020105070f05010e0327150406030c0504051201020c0f12041202010e03120d06060905030a0201030207080d0903050d05091501140a26010c05070c0303051b01020d27020604 77
    0x500b40803070103d1040100070b4201450301912071040741c0d21030054982c04111003c200003408001c24002c145c2c0146803406201c0040b1406a90312100c1c40d1900f82030b422005010340c04a002e0601c001000002010b0305c440c21200400c035440750005854003883c0d51100d04201032028403040c140c0c0481d02d50982c2448800031541111005c200000341078a0350f00c0165039000941150551500404001e101c420201100400528011120030002d241c2c07207450a03103075482c040c01081e4040d804904c8a000550090f401040c409004a10407403d24240d6070b510801d403480300d04200c0c001900820340070308114150060f26081080c0002034039030010602241200018148039041d0816510440800c00743c85200308440030b03041d802c0c03518a011701d507588803139042c03801070500225542ca03050980703000911600980c0c000d598003e5461903d039140d43c8084400d42c104003040060740b840c0480040d1842d0092005043c4400c0c1c0d0440825940c41502e1030700c1801c212049085000b840c1c1302c801c0030043c0d560034111800d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 919314604 1250 919313354 919313363
    0x30105060904060e0709050108071103030a020f040308070f021e0906130b0618100315170738040b04180e0f0303100801020a0e120a0605070905031002040302010507 72
    0x1c6510900d00014041c01a41e4400c850306000754081c40740c00d076400f90f04c8109980c0207032211a1503440d05513049a001000c00140d4400c0d410074004541011000d0300240720b540d03c403004580c2030a449444021b03869111080407282c095107034401e141142054009840403000222000b00000b0701000420405180140024420340042d01d0000f4218042c0d48900c000d40c0000c3c01c115150351161241452044000b41c945124041c0105d1610a40e0700c207005500300302d99102e14160306140341c0f56412179013076460454002140906003021946404091183e94003541c8024046c28070501301c80c6c1200245103243c85084016400c220038411042c1d041c080f1412501d202c1c43d80c03401070f0034440e03009001305a400c0320319046010352100280042000405180680304c1c1040e9050819540c0482c10300301d00c1520000004555000c00820b028a40903042d4014042e9500541e00341c01216910041126000c403050307004540c80310400d012070305040000700320a030401401180b40c10300f5500007801074010514001c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 919315854 1250 919314604 919314607
    0x110402030a09150e0c060a0207060f12090308151915050c0703050a050609030310170109230f0118020f180c0901260a020f2205040b060f03010506 64
    0x4010303216650018a116401400801c03941d0802d40d0503c2c00b03030a44076500c1007a4410f0070b040342d1282c03402000f12082c150960300180405403802c1c40c25245031024281d400c0500094011880880000340102d584052195890b4012840c0c0011180d0f940207020310101d00807005200f000d20495a80041c00d0300341d58490f00c0c6131000030300042041303c05210300040d003809802084800010000c00240e070401c42c92050041d94001d82d1640e03030075980e80c00f0840754400103102c060310400c00304421106c1501e411043d440041441da400d51506504529070100a43d48070140b2021841c0c4240203001da0034010b60321600a000c40b000b031503032805403c043d001c80a489440b82401d01d2030169101601141800102104084180b803c00c5081c00c10f90071124516011940042c11030701c540030345150040700300009410b1500039482d009030540c02900301007034148114900700300301d060f22040780c840c5c1440e150780300c0d0340c60407443c2c100300c148004d40348400f81c81802014184100e01089400c6025203054400544a06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 919317104 1250 919315854 919315861
    0x11090a1a090303130e0606070b070e060d02180f01020109051e010b0a0e0103031211120a1d0304051008012d15030e0d210e0a0803010612110711040203 66
    0x1400c092294a0200b0341c10b100010300c0820328024450580c040300d043d002040d02540e03541090050074890b051004058184a2000542e030a02401021300c072454003038000c42c1054040f040c154120ba02040c0c001109100050981295107010107070640b40080030f20080c0303d800c0c00755540a0340c8020b10381d0f5803480c0211080310b01c0c00020b02544150b0019400070701022446035148451a2609400c0c08190001031205005c144210458010301c104440c55107070103883c2401c40413580076010707405810003842a4440015101c0030881007800128004a000a15500c0303141c94204807142c0306c41240c0c00c00303000614004000301803181da01030000048500f51881c1414022100000a44460b00a070491f0006a040710004c03d502d0340c04a49804102c108949017040ca43c90255410421802000d64016910203a0040440c03a500038000500d518011120105c0d010780c2c0e0700700140c200345c22440c0099290600d41480845034002c140341c1c9032060841d1480d00d9425250901e1026290105c18003917600040030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 919318354 1250 919317104 919317149
    0x18040b0a0e060d06090804092307080a1e0e1e0d110703060c0c060c0810060c1a07020c180103050723090405010b01090f0e04020405040212060f0a11090a 67
    0x1918043c0d0203c8200030079031051034880501c0e0040e004001d1802d2038000122585127003103645414440c540c2d40031903410380e2400011542981d0040a481c030480d111a010144041c0382c41c01c5114601e0000b00104441403550070701031400c49040803a02500236603e184030209840480d000305040700c0d51400780ba0040b00d450300b03c5c2c82c182131a4002400b051a0418940b80300c2e80c008400c11100344601800d000740c1c081708604070b80300c00c0d0940c1e0600a100b0f0880f82000154000c0c0454003d07035115484000d46038000c0300079607880701001c888002c00368012040d030b142d551420f4020244107000c644404800f9504503298507607948003d00030f941011413104d000180c0300b10441c10482c0540c00081004060780760900d81035000e05554000540451403904001c81c9480301c004100c4161091920302c110309941d20340800c07002d0080504142d80007103203c40e0001d40d40a0910803248601c00520760411142007103d81c14045a50000ca900a403000611211036542e44c4e5520701822200c11444400e40503000104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 919319604 1250 919318354 919318369
    0x115050306220501030b060915010e03070f0b03040605090a050a02090402130e1c021911180a02130909020d0609032f0705060c030a030e2118040b0a0e06 67
    0xa00380c8150b80c0d080051118499800807410303a40301d180951683d446010902104d408161208400b07400c50b218034180c0340d449041441c01800c0000d00f201c110340d13a6000080c2404c096030700311070300c014400800c110601a003405102c0d04513107954018046030b552921115290380ca11480288201d10150200307043d551a040145a5551038100c104241400d1114880e07842d149000c030b0281103240110b130075040c00e001150350545040e0030141840b4008003591841c100c0c08800003ea070b40001550345500c04d601903241030502c00c2030031101c016622448104119a5960523030300908106060450008c0141c684200a041a0383c0c4590081400c404514003035a400705000e032171100310b450005070000398601c0309016000300080d003025202025207420910640f40309035100030315030f6030080100c0d440380c0c0e200e0341c4280302d5101c2580c2030b11600030701d848206111100c04500814074180c0480e0900c8000f09504510034004011182000b0700004500812055035540c81000c040c041c4c00000145e26486268 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 919320854 1250 919319604 919319629
    0x60a061d011a070212010903120e120708040b03190b061e030a063b04020f120309030706090e1302220e0a080406081003020d0b0a0f09050102210115050306 68
    0x10b01904001712004003040c001c207103055040d000034450a0030340c1161030480c4201214031007204060b002091803090000401e9004001c01c42c0c101c0310800002400c1c280e00d1010b54040d08140b0441c805010704d000d030850a40f0044d904552251380104040742092440907400005510340618440d100e41d40c3c1c6000c0390080c01503a101d030101200075400740c0345051070003a03020703019101d03842d1075183c0701c8441c031702195180c0040354000c0d002038071207094107010310342101152402c0b10850102c07803415800d48042410500a948814003013482080e0920401460b100c40341d078000407110307002031180001d400048142c10215440448031003010307903035400c1d0010754010408050300002103401e01203035442c01080030780c802d00c80e110028a080011a82500000782c0c000112500104000084031a584481c440c01d0805030200c4960395544006114250044c020001d02c81e018000042e11138a581b040600e24440302202072131b280c01020010301502c42d85440b641c80804444ca4000d440b5035038400030038403204922 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 919322104 1250 919320854 919320859
    0x60f120a05030a1d090f060a030c0303050703080718030204021c020301121109013b130c1a04030b04110d06021e0703020a03181205060a061d011a0702 66
    0xe414044000010240c100696031072070001c03003510504e00710744107414400d2a44140044040740c4180101103140f600414020094200683e4982d1990b1000055510440200d030340032a03640c0c1899001000540d002180c2c0c1800002d07800c007d141d11903501050f000083c41550301044000d817500212041c1031041003462411541c0e561160001450014081780441d680409000d4981890070710803607844c1241da040e4a440d03008090605000380c0e9402008400300c0c444c80e031070030200680d0b080000e10781c0210091040e06208418a080035211030078150418003110441c80b4842c20048401d004071000c99400107031540781c0d62a10b140034a107415007072590a070300c038148401c4201032190075401425440801009070016001c01007118049008052001c1d0150b080405402b01003401043c0400005210100c101207031030701c807400500c61440c01003041d0341c2a40403070200101c0c6c00040c8981c0340501a070f01c030200b034400700c51485d017411804e05019141c44c500e000f0fa02c1e41c0d550f2114005070b81c2c145900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 919323354 1250 919322104 919322113
    0x80609011401080c2511030d05030103060207022709150702120711100918060f090504020a0b0c0a0c050d12050a14181804081608070501020d150803040806060f12 71
    0x50304080c140d40701c0441c2a9124103104403554128900020170ba013288c040c0d134a950f8103581c60743d00c405009410600003640c0103190a0706a1280c04038810022060082c0c1d080d03000b01074241074074601d28160401000c00e2007003002c1e04c140100c280d000a0510822031600342d070941d41e801d05280c8064481c1c0d800c00c1c626040071300c00f2010600c042d0840400015600300400402c0e4038440c82000c001900c03501c1c4200b110701e4172500c0c0c05021703620098201903807150010b020000d4a580c0c0b41d0b5400fa640d4885170002e501e6800401d4000108511002210010041111001c401d445d42e51108612115903203000001c2c0f080009042c90071500602d1901c522161000d01140c0380d020359900c03001131148007481e1a00c1006400030790007070011012962401907800204007414002440c2d05a064041140c20075202c0c120140020b0b40024824001003050b4a000c1340e01089a080306100c080001c0095000000c11b0b804c1408213006800300043c0c3d065000404071507a800543c81d410218413009001000d8a045000c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 919324604 1250 919323354 919323397
    0x30510052b14030702010215130f060b3c030c0405090a05060709180c020a030e0409060608150108030a0509040b01120e0d140901050702041508100507080609011401080c 74
    0x100c09002442c5c000e070266064406100d007443c1c900002281c10458030544c0d92200808918404a203001c0a0b20034040060344481c000000b4046003008660b2883c6130000403500c41c020452814142040d5400c0d504030300e6a82850800079890300d0007001c0d0305025541c0d4000090242c0d40420203100c1d000d4000003920b546041c5810001d103240c2c1c4c24004c0c0707440703409510002c44170080710340b081c0e001641c495400303043c403030b446550b048522072101c1004c0e6902588440c45180070031100e12271940201040801084400c10440704c031540014140d0146070190001d128114065802100700c0b40440421900041c0c01c9140d400180c0d841900c0054007082c0b070385014030458210000056a0304046042e440c0d11890640c040b503108058480c0600701030008070f0a01155005040c140c20141440718003214a0240540351101c2c07500e40841050325400e01c079180c4040c4900183c1014240c2d401034002e580c00d00b03081d0304003401035400d107000026884c101306241000910000007401138440000b01155030412020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 919325854 1250 919324604 919324643
    0x1e0a031202010b0a060804031817030415031e050c0708030c180f0a090b121501030b131e0614010f1a120f1e0a0507030510052b 56
    0x180d1003100d400156103012914122454040645011584203903540503c07580c41c1d9408551265aa04003030151040620b0045070706401200002e03445845c5200868980f450071700035400c031203c5000000240b41c94050041003222a000614450059064020a0649504280102911490310050801800401030114000c0c811000741841103400c0f04400d58080c244007000704050b00c0803181a400b4246c044200980f00d03c070b400850552400500942404641d03000d10780c02c29964805007c40402800c0040c0100118402800e0b0030a030b003400f011845010554644141015030860b8105450b0031503226810010301c0d07003044600310782105026000c4e5a44040150680009011307000b42ca8101915906151304404241c0d400504206000714072612a16001c1c0c03d600e0010340603124503ca40800388014501402c64107004051100002910b80340410340101280c0b006000c3d860100c1c40e1404c10000d1395140360341c10b8a24110b920141c3c031450f18400c3c1440404041e20401017101005240c80407102 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 919327104 1250 919325854 919325873
    0x5160b07140307121101050601021f0e0c0604120c06050c0d0e03160f060e0d1220030316030e0c01020c15090a0e0702060f09210f0313030216141e0a03 66
    0x10101d04024003454940c0230040e80c44c0c03810f1001046184803954107284440c0c8290300450b03282103896041d100c60404160105450b80d00c150803064002d0303840c4400c0d108215006101400070442c1d49001c0c0d040899100f01705442e1809460712030100154400945050f03503050210840400d01e500164205644d2940120102806441403001280c1000710b00603013070829080d0a0040b96100020100c03038061348206943c400e4052040800c9000e140b900e600c80d20104200071070003180c07030f1030312150b5550300043c009054030041c03a00d00c901900440410410303a40c0002c0c0481c254501100c031116800904440c2d030001d030140d1000180e0162100400055010408180074024446582615131669035500c0003650818251509403050b0310882041c085c0c02c00381c0740e071041e41d0b080c1024014640442e40949181c0c0307820030f0311070a88101c0080030720070070582c04110103140c803040c0c000386030090343ca404404103090035180406030081c100303401714070503400203203081c0900c1c0f10000b40280c41741d03912070408007038a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 919328354 1250 919327104 919327127
    0x50108130f11041a03060702070501140a030b06070302011a0a0605122203030e12030910090314041412070b09040504021314010f0f0b03060418061805160b0714030712 73
    0x1c2c1c006d12012860740b0344089000816030b030041e102c0072140903003900c60000641c88a0341c54000c040d07403144400b880b56201c100a200e4140a0b030b00204190780124010301c80001044001482107549844c00c105040e004026515844c1606440080b19599540d507901c00068408020a80f6003482341c001d001c154240d448000d81115a108540030700105c0b14000b5501c0c402078482c044140d01080c0c50640d21074244c0c00c0022450301c2032420031505a8401c0092410f41c105402c4210442c43e094070f1560182404148034003400d04034801031075907900e00069141c05206088400d4000d03925203001a0540d19101d03040e03105014240e80030808010646118042e000080c06144105921002c0014261070039010201c00d0b01d40707140080c1e02c0c60302c44008000c001d003200c2c3c0d01c2d82d4001900d18001c001041c824403840c0d0300c4000c3c0705c0c448040f40e1124030704182072006a10038003034140312000047c4007030a0180b0640d960b10f9444074011408556222240d0703d540100e4500401701a584e403c081403c0d540400d05151 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 919329604 1250 919328354 919328359
    0x628090e0a0203100506130308040f050103051b041505070c0311100f020d052802010e10060e0c0325031e0504020108060112020f0c030310050108130f11041a 69
    0x280e9118000d44000303a00c410350f01262a11840002030065281c80b20003811a520036058420066640b0390341d169446d00f19502000100d2400c0900b0441942c1502a40c0e80c4000c10303c1ca4101c0c250404980c000d114003440c056200c103c19070a2400140c140220100c030a5147c101d4900e1003000c0d07481c902050030900c40381c0d049008840c0e85080c46201d9010f590304165450590300a0510302c1204a411213081d040b2a400080800d4054040340c42c01041003041090301c041c079030010414120200809242c144035400c2498500d140134410824201401107507038002240003030082d620345036158298500e81107143e1900180c4c480030490150550141c5c8000718404140c00180700c0ca050842c90f503022654112030180c086000030700010010341c403c100c178989040003000700600b864a0042002c1583c0c011515108890740700005004043c1e601517203a4005000910b0300110504c1c11404601c1510b040d00802014401107281001c2000b02c0303020f806440e6000540704019810407011400000c140c003044103030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 919330854 1250 919329604 919329629
    0x2304180608010e0303090303040605071407030c1106130513140106020a0b06100f03050402120708060a0e0a030903060c020709230a060503070501120e010c1205130b06062809 76
    0x101003d40481502c0c42011004041d42c2540e64a48601d805414024070300c00030405400c5e10a80c0074a09103014040b802c2c001d684d1940300440300d1a14128906ca0101c42502c10780081c04549400c0103104446010307510140c0368080090105030420025050300051480d410000e04004141d41c2d50018420380c0c81e80c003501c08250941c50718420300841c242c090003150f0000d28500405041140283c000d282c100c2d20103406525400d10b944c0e042800d065158000e03803450340014040c8445007a1a005443c0c01e000e122010b8240300e40f1544d006800c110042c07200501c1680c031076250320042402484117600400c2040d205210740401c0c090000349900d40503404001e50031026021a0480340c05210f440140d81d000b400030120b9605040040d0380d50000c110020a109880e4444410b44c401c003030080c440c52144a031903040b50788401c01d0307400301524001496084020650300210300400c0180080c5904078000b61101a610001c82641a90440c0c0442c0b0300200080c1803040040c206034050b14030021034200c200c006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 919332104 1250 919330854 919330871
    0x303020d38010c0309050108090a050706051e0c07031b03050d0e01021b011b2301020306010f03020306060909130c0b09010909060b0f03190e010b01120c230418060801 73
    0x107550303e01c0c500e0380181c00103101039401d11181d4043c1004942040b0b032041180d0b0094074643e182407410340705400031800920301040c4808102401154000f840001d034035200d051140303415425955164600c0068039034841800351590b4100c403410b004e806190001c0c26a2080382c000c0001901c5c25200421007401031040c90420300411081302c10002c200f0105039902e82d51181d080704c1c4529a18103c0340180ca11844510700201c0d403580c55032040d02c41843d440009601c038a00360001400c46006000c1c96001d140c0100200481565510b0403142003d6040707900c03401686451300c1e6002c2980304410001c042200b224404610040203030701a00d05103070240d99140d10107840d08601d100b5030314a03100701020f5440c1401400c204506007009198040302c400c0c50117203000002c107001c200782c50f08120180420303552000080420350380003505e00341003c4294400e10a0b008540d50007044082185003007a960f014043c100708007030103008210350080c1540c98001543c20000b42210000349414420782220b0342c68647ea5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 919333354 1250 919332104 919332107
    0x8190b070c0f0b06010219050106051c03120c0e060c1501050303160204180c06050304050123070309060b060703201504030f09030821070206130303020d3801 69
    0x508070381640141c01c0400b00b00315540381c07920030340c000d03003040c0c194060340491002c900140701c0321020103801600049100d501d89014003540314509042501441d03519a20800402e030000c00042500741c40440010f0000ca07128400c407900b21021400c03540c000000030342c1c8d0303a81400000700410304503141e2450b80360a0360794804040d80d900c22840021404031903d00074201514050f802450000f4100107201a602510754070740ca1602040c0d00440c0115074003009010030300c42d091044005800b000c507548035450040c4940103106d40c20040c1751104043d220b052480030404507410440520a0142032039440340000c1c5006000d040d464000b040c56020302d50f001d655000b80004a031070208018010b0350450b9222034404503203520b007900d42c05080c0150078030000005200b4000504843c140d03180f102e6079505441c00307441042040a0f00300701c1194407a80034003918a814151900c00e5980c54100180d4401002d080b400140202d68404050324094601b070404d0311640ca41c0c400c03807800c0c4400c81c1e500070300c0c0070000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 919334604 1250 919333354 919333367
    0x6040306150918150b030114010602010f02090901031113020d0b1309110607050703020306040f020f03010b0105220f0914070f050906160501050705090f060405060a140408190b07 78
    0x8400421424610220224076504c3c50300301c425503840f20200760110783c440803d081d51000042c6a4103080501e0040120950a01c1140b10822180205510b42100440010010801030101505108108104c10a286d60700c047c541c0d41c1d844d075941c0554a40210b03001402c02801009240b0707018124408900c49440030074400e4051580d48401140d003240e080d001440740e6500031140444092040110200150303400f005110711452160000ea03441020b41c1c03040c0500c8100c1c000c0001c1c007136030603c4203c103c160703045000e55850302c0b09c0050b11807200c0400013800c40240030590010b5000e0801a01c0490b50801d281c1105074411030000000006449904044132014600c0d0030140000f00c0c1804406071a107000e0000b0104c0308a030380e40b03c400301621502d59608441c026136a010100f04001940c41c0302d410101e05c40d059000c803ca90050502d031400020034500e00c00c249240e010810810350000810721110180c9001d0109041210210240c2c07060300c3c804009051410340c3d0745402140005c101922504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 919335854 1250 919334604 919334621
    0x70e06040317190f0e032802010504031509060f140a02210f0f100602030f1315170106050705030304260703050307092414160c1d24030c060403061509 66
    0xe610103805d91441f1054900820500c4049040281c1084000007080d803159040f40c4540610b000020a5025407819504541c00200500c41d000c2c1130a0b841c110b1217144144150780b040034002c0160780d80c444903c4000c189848841c111140342141024001100701c0e06480030301c01c0100e0800c1034100d0300c40a6181e11220703502e00c1024010b80c42003061102004480c400b4290340c1e20031070305140800e901c0703040001c0c0c4040140c10400024046851030441301031000700d01c900420003414454039120315911090340f80d120040002c3c00b81541414415000b0502200d030003031181020221a84840e1640f5001340164800d032402000251201e801240340051800814150f040e5100041c1000a00c6003003910710790b186020485645400740300d501807019801403140d00683c031914200a80b24140300080f52a84200d2010302c10412025080040000354070700108940a101e00c1c81e094030f0910400040c2ca094040080182c002501003000000c202c01c41e00031183c1c0c03504825852480310b40b60b0341000300715075010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 919337104 1250 919335854 919335883
    0x13020706020405120601120327090b030d0503011a0702031002040b0703090503012a020709020c010902040608060106051b4b030d020c1212010e070e06040317190f0e03 73
    0x107c0c20f000000e00030440361440426100d41c0a031030000042071021540081e500038908141c407555200300d2494140b1907642e071841d807420920b046505068440540d40182058182070f8840018842d040d0351b81040303d18030003811550155503c0740c44800c0c079907140e08405400c802140e05540301003520300d418019a084022141c00480300c0390118540c1851805200440509600a48601040014060004284e40c50f81a0000300700e4885030300c140411201658802c1d425900000010300542e03500000b2500e10b09402140801110f802c00541410300303100311134071300c00d0345400b106590609030b04a21140b03110741e4602e22140034200821100014200040284400d604100308081c0712044941c05021070410a10450b54500480030303c40c92254088218000001014401004034002003241d890740000c4a01c0c1c4105024070003000b0034000d016a01000b40800d500103141c540c5a40c6108c2581c17041c4070382c90212883c0802c80b90014014040c5148142e0000e10903c04040711418001407204251050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 919338354 1250 919337104 919337129
    0x170c0406060c02130b0d02040209040213080c1302040b0d0c02031c060311011d1903021314010f150e1305180d110a11060c0a120f1e080613020706020405120601 70
    0x31b03642008000d502503180c07a64000c3e03007440f1588441076014040405003e003c8010320030303003900302c0070000580c1c510600c1446a0f401000300b4044020740b00d0985020b076212040100c0d00c0508a0340c10782c10740c003803522604c8900c4600301e55240300b00c5040c8c00c83c0c0102c0c1c1c00b4400528603100c2400c011190030241c0c0300409090341c0f0414003a00c00e0b05112225810909001000d8030781d098903580000c2595003004540306070f031500e4030303004214840b56030515801030580380509d1440c0761034071408200d40c03083d240c0e03ca0b0038000d0100350702030192079600c0c0c50139841360481f208108516000e09010400d21580342411200d100d01c02c4d2100c40c0900030b130707401516162100010030459407560b540350040b00c46082800d8101c0b00602199201c42c40c02c00030444e41d1845400021941c501c1508014001d0800003140c104100241010607001c0c42000c144840403a841d04e0f2454040c0d880c180414840540365041c0440700c0d00c005052014032410303038007800640d08200c50f9822928401540d8640d9102c0a01403540354100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 919339604 1250 919338354 919338379
    0x3020c0c0f0418050a02130605030a06090c0b030106020f0d08071202090a1d0109050f01051518060d0c0e190e220605090c100801170c0406060c02130b 66
    0xd2010300c200c110a07004102151507002030701c02c1e0940e207036920710031142d5505c01002c090071460545d000d10b940040d1190100903140c0b8160029a0701e0868100180920f40d032402c2140500c51450003038170140c5600d501b00e41e46c9503074440000759156601006004140104496188070071b02c2181080d00a004958403030706c1c2030710740c00b42c448025488140010351203081c8420000c0c4181903518654143c1d1102040310800d0343c5044a40d00955200410325030720b800380c10f401408150b80d04d803903a024106034013903d6500c4a02062646154402c41c031f00705a8010004114904082e00d19005010f0701c030340c5c56944040d1801c0c1c400c240040003914200703019080c000c020b81402114901e5036456030105043c4c104c00401304007809030320a00c6803075800079900c15850741d0400c990035600308800002d0000503285641091080c100080100b40107014a101e0840c4030300d4807100ea1401000310710f03c5c030400100108600c80e40c80c40301814940401e44202d01403444083d455080503010b201c0d440100c01e0282c80040402c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 919340854 1250 919339604 919339609
    0x1106070827010f140412030b060d3317240903210604051609030303200414040e0a03090b1b0a1401051005011709120d0606030c03020c0c 60
    0x1050316015610030340d40d80110000800840c0129580d48040350b9588441e401e290422a1b10b0741d2241802d201490300708050600c040e01e4020450716150440c0c0000150030100c43c0c2c0f0039007078103510701000f4116400001c00c8030f041c040c030000070021a0642c807640d1110b62001102d43d46c036050414518511440c60b50030740700d000c002d500c000a6000c0303094000d41c1c2c50103080000c0c2c1c2104e000c0c07401c44840191840000c101060909100300c40d044101500300d4182d47c021500010010740b00341c00010704058071365010641e44c2c01d020141d0854002001c500c5901c80b5210511030000050060656200303074100740201406a1021074014505034140d611800c14030304154424105901503480d080400ec0c3c904c00d019500390050160740b042500c1101500c5012204603449800d540b0041c0c0086900060030303134104003981c0c01001e00ba404840381110300a60b9980c550000d070511184c500794800e040c0000880d80042e0055500c103505403207040d1003c112000c0c441004408031f00074082072040741e40c480c10b0082c1103071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 919342104 1250 919340854 919340911
    0x1b06092b080c0f12090f0c0406180b060c0109060207060c0503060901030318050a06020312010b0309032703030309070f0f0b0a030504061d160e07050a050a0504050a0611060708 77
    0x101607001c12140b5103a8071388034007110350034201c90000454000003070064884505100c0d0920741902280c1c1031020342d04200c614102c2ca0030b02c4e0610740325140d5801200003103464043c01d0754122006d05008102c803031480e042001c0a5403105104664103841c1154890b1520b02070019a4003c00c0060290302ca01e0f800d695041c0c030312031509400740a00420700400099541d80c1d040b01200a0280b9501075038170385007200340910780b0300c0c1c06820032502542c0900030800805400000d9510320903428154901d40d203c0d036030801468805040c18581c00d40400000c000c1d225000203806400c4401158507040802d0b520003004000760140e004065002400f003041402e654880e40206401501804000a00305031101001116200d11061820542c101e1100300036030b404449042c43c007c0c00750040a0490f0705d007080000705203204090b194001e2050205107400c0b514031507810b072005002c01030306d5041225110500a0402c84c1071000301103042c45010001400b080c420074000703000b40311513405503000c0c1c2d015440305040d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 919343354 1250 919342104 919342117
    0x1203021e0f0319111603110109020f0609060d1401050a15020c040b060c300415032406092309011412011d0706020a11061b06092b080c 59
    0x50394484e521800507000c6600144104840100195416030080c680900400d00d1440740006903450701c0c00060150700c680c0603100c031203034044a9460f0380d1000403001070164052107040d020002c2c6010011076002c2c1c408840c0f58140c56080710b018020341e548820314000319070401c0b10000160440305130340c4990b041c03e800600b090100200741c0350518005200c15481c0c05c200b04910014a9041240301c200c42500c42d5190560301da141c80c10901d040e00f0300540ca28006103076803d0740e0425658041d0203950403880281c0000c03403c91100754000c030036560200140b50002c54045c1c000311020380d0304420419130302c9000c650b03c606805070a4441c0b580c0391400c0505145035075001c070354200e500c010070160030200038860500d8403003031145800300c070b8a1301c0c6c00c00c54540717407c64200c01c040d0352001400c030021483d022200249480101d13a40e0b540e074030140040d00243c20314003554451f41e00c2003005010034182d0124003070094504071682c2d50904100c41030100c64180c070541e03291021401c41004a094240342c0801041c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 919344604 1250 919343354 919343401
    0x6071d04020913090c06020a030c080309030c0d2f0a030e0f04060e1b040315020307050706020304030f2a03050f04080d0c05160e0105010c0f1203021e0f03 68
    0x2e1010079800300340d003803044444058121340c1d1402d80703504020400c9078020252640d4801800c81d00c8040e900135083ca41352100290070400b0200000d8140002001200c101108020540304a080040e42c0903011540c1012564075070003c41d4078403d031014082800e02c40f200b0031080140440541a20305032609012441c989400ca440c0340156040d036201d5000303080c000c1000e440f41e00c10910b0840390340000444c407000790201c0c1c1d08040008001007030300017200403c82c0034140710050f031b00c1c0c5a05909a41038400e198000b0929400802080245600520408a0b00f0700035103560301110781591070100c0841c400d1202445200e444200302c00444d1150016000746034913448900d10346a180c44086241c800d8200300a4005010f1005a5041000a01100095a000000600310310780ae14410320f01c20081402a1410401e51001110500c0802d4005405442d007043c00f190382040d803804010003a50140300411254020080507441c17010400b8100c0f46070302102080542151030720b000001c0c104102850000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 919345854 1250 919344604 919344607
    0x12a0903061e140f0f090c09070923150f0c0118021903030206070f05122e03050c010c05120a0201020306010806010806130509150a0b011106071d0402 66
    0x240d192040000c1a2800c1c001d4101c0400440c05034019580d5007007040d0706518000060101030001104c02e2900040040b91309a95981c91903051443c1c481782d40099a03105038010300f4401119001058041910f210a00510498071400082103010300442c40c401c0d044051031404098000c1c50384060000900c40611161038a481c400c1c19030b01351017018401c0030610050110303200440c40d108441042d0b6035502c2c5100e41584d8a1610040d4842c07900509000a011501d1119180903129108603256004d00420515903801c110030020030700c2d80d80408031440040044031024420805840c48401c407035003d00107008000105004580104606100300d07039600c030312001c164080030848013909a915250380010386a18180e000140415800742c80c80d410300440e281030101341d031181e68940120404160000c41c05480b101e08891501401041440c100c0920000b481950049a0413170009540700740d03141045401c002d5581070301c034801521000003042014003103c03c00c0c0c072051061009440000c2005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 919347104 1250 919345854 919345859
    0x6090522240e070f08090604020d0807080d09110d0510020f040305070e060a1208030714040801060e04020a15020a0f0303151715160503060a1a1b012a09 67
    0x1189480e500419a114000b078100b0003041e0788840c6000340400c3c2c034601300069040001c801901c03050080e0000c2c0c05042d500d44014103224811007210512075003c1c2d0f03200c0d41d03002c8150300701c0020100a101210001c0c1e0361646c100e098a00808007048a58102003e80000511290488000d40c044c0719181008002400000040340d4248040d500610074111840f4162a041c420030a0000f5260805d400c100840742d0300c1004a81840700f40c035444942410003040f050504034110702c0c20b001d6544101c444d582400004a04020070045190007903100791030035540030f5103070344c45204410f0f03030040740744011fa100c900c012010803074800c0c2140c4014081c1c140041c0d071100c1ca400b0f50042c2100e940000481100f04c842c039030281d02d0100301448001e900381c038101d00b50381841007004002d0002d03940941c040040c040082905a56204005802000c03c00c1d142c4100d0134200608035560b4101b050b80000c400c02c2c0302c0326a00c4140c0180600c80f11003000340301c6c80b0780b480b5400d410310b06100d032100206800c0100c2040007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 919348354 1250 919347104 919347161
    0x90a0501050f1621110c01022a0127030b15010804030c1401060e2203050d1d0706020609070e09060c0a110105071101061a03060918120406090522 64
    0x10f000c6130001c1d40e030f444401d50308080300c06243c2038581841c40e0441d030008241c51120b1864101c031440c6c0c203506010905448010320012208514540303440c4030307402d41b20340c0b42c00c401412000412080b00d02c905203e4500f076543c00501f019000384420402e020900000000340042d10841c02c9124007441492255041d100d03007c2494210307680303034002d031014411060900ca5500304100e548070701c0a56003c0d0494140003141c0c0c005103240207110000c2c520540369002001d04883c134503003122003520920100c8040c980c0d10b480080d911242a183c0380d08038025001c000c551541c046c1c1c11503125182010042031151103444503000990301100c1c2000401140741c030910b8100310280290350286281c2c0d60f429030140141c640450131142c49900c860617180c001120601003221020680e40d101d0001c881e40b418a541d16100e04203503000c00c02002c0d0301170007000d0641050015103409001910081d5846098050300d4809200100c940c3c060ba10402c400b039081c0c40c007810340b5203800980340d02d945030400c8603030542c02814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 919349604 1250 919348354 919348403
    0x307230309010902010e1e09060a0509090c18010303050a140903014d0c010e161a040b0d090302120f0c010c0804021804170f090a0501050f16 62
    0x24603124070b9446000850540d80d01c840e450440920444640d564405020580410807244070045030258003840000b44141e601c004101c4001c000144c50102c5c1c91070188041601c4035803001900c1d2088500070124007070f40741b20000440c1a613500d030300c62510b0080207210a807010807e901402c05419800c10201015850078010588025416400c00c00c50441001c590302855260303440d003000d4a08a02e100c001c0c0281e004224240320b117810b003903055a90114259040c01760092000d500028400c50b00c612400e201210150003c031803a44529000694698140d07050364450751040040c0c0c42000e1184802ca44020707403002ca19107100c0c2c01102d40350540315050420303d411005100c2d1801001251420300e0110a001e0710410980e5840d04408a1505030300061740c200ca50700600407650122400241080800307040c007220840d0743d41c0b42c15114181303d944034695034040302d6150301802072100002890b50080c81030318000c00d074450300300307050503035800740c03c210601c1b40341c42a40d03001d0a40d54501600440c004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 919350854 1250 919349604 919349611
    0x302040f020901021c0f0c0f050f0304090e07030201140c070e1e01150c2306010b0c0f06010f1701061706090d17070e0f030f0c150403020603072303 65
    0x603000350325108200c001a0604200c0712070600f6020480300324240903070b03024801421400003401c00c0100c105075424032030b01d40801c040c8010228410403042c0d4080d860300002070710440d4200760040c0f1420f9480e41c02241c0303418041c0f100901045034640d07a04000c60840e006002005508002c41e00d4066030341c8180080c1c84020707280000000700301ea503800b440c41c003051042c1c2d001d440d441042c0042a56003980040032420000c402070201e110950203000103c00c020b1096a03805110303c216405c1e941c650141044503401034070783c000288111800c03c2c0d459040070410b24100c0c1c8e05030803c1380245140010000c003912032404500c446550b10f820225050702c840c2c46203000d0b03c41140042c5030038a4600d0304d4500d0701003d070f030380b900600c0100202e24101c0f4107100d00c050f07401400761800094201320640811324003047c050b15141e06024004814080207000035001540b950100d602d0000c107141c407090700d240d0744580c2c0030281d0881d03001c00010b1291401113000501ca010034420712100007201c4490449a0b070401d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 919352104 1250 919350854 919350881
    0x6030a0b070f0311040b040306050402011818060608090d050d0e070e041106180d060e1504030e10050403080705031b071d0f0f1b1308060a020403021c0804030204 71
    0x440302c940c40e5a51504c2103100d0207880352411864070341400c0c00303072515000d24400144040c0d211000141103910449643c12440c065070803405c1c2168484514003248282084a00c400b98600000042e50503c1204218001c5281c180503040348811844100d88542c0a1902c1c1140d2079202d00f01c400040701c04225550080188203015407150500d481c02e503400c0421003131605d00c564002d1040101e505183c58813190404011200e021504060b86410009040499a41c002a0080d810442d40d500480395100e485644039540d81d2407210403400401290b117015603001070008200340014400200164000c0c81700502907400c5901b00f203848141d031b07440b10b141400302c004039420940c01044010601d05403156441c8015006803101d1611002c40d282c10311000340652041000c400104900854507000c6e50884020380c4401035403020900c05880310f10800388904c0f0001c0c800c220006528a403e0b10a4509403540100038502e07140003107421030000341f00050281d40340c0c1000c0100000507a08d91180396584407c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 919353354 1250 919352104 919352117
    0x20a0b131802030105180405150406050a050906090304030b0c131206061d0c030414030a020c09010e07080412030b04140708180c0d080d020d140a1b0806030a0b07 71
    0x5004558200d092400350701d00ea40d42c014030050055030340b07401a60807441665200c1500650750380c2052860209120368240300250650144000c1c443d058110fa841a40c0c81d07a003e01194440400c01c0703545000c21035012026400501c42031000600545400d0b42100341403d0382c070b0138110358000160303000603a07502c05a0000c100c00407040820910b0f0091a004084020b4080c120b451000e49034000b12100819001200400000080c01c000003010150140315402044a45480f06080d001e9a6890352201d0356124001d4980002407004040c450b0600c58040340d42c0c1e052486c0c9a9998034613881c0d5090112000345a1580f020320b43d152924420304800350340c112310303c0441e0300344844003601908002e40562400c01d100b041c110112040007074070300b000010682d03002042d00068104080f9500828814103030050002030940c640500ca50007004941d0b16183c1d403940191100f030201c60883d0f9803010306540c290041150708041c18062032003150321440180036140459616a1268000c1f1401c84062010400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 919354604 1250 919353354 919353359
    0x618021201060e040210110d0e2119021c0501140703051b031009180605011508160909050a0c0e0f1503070302070503070303061503090f0f020a0b13 65
    0x340542000c4140440e00d00800c10307203080c081d8000d148140108068081c40384220840740d00c5118542c40b400c54025030090701c50040a44800802000c1c840507002c0c41010341e44410801418000005241d80400c00000e020990341142800c000c1841d00800340d80c840d244c2004034001d03900e400303089400a4414800012490b074a2080c0240c030f180c001e0000007c2501d40b034100603c214840304541100d10500d00b6583e220b54680000c0c14049561346c001200c003508145084010b008000310300fa1003030740700301c00a11549c1e0721085141e0980080302131090008600390003007004c0801c05400800c001c1120325100d16825200c194403000d84606845400841c1c3d0b90307405004056034400a5101100c00c2125202c19150394040040e1240f0000c5581100b0030600101082030907010358110b40c0000d5100b82520b407034036824100540101201d00c81e29012001f00c08104801c1d910074403880c60f240e0340c4110a511a058903403912028400790450807a0807034518540443c205d00c00c0c43c050180030f501f001c801c6207001d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 919355854 1250 919354604 919354609
    0xf020408060c070506240d06020c030d02090f06030f0c030907050d0f0b070504060903110406151809230411031e0708062217070b06042d18061802 64
    0xc8004083d6a48402c139504090141e600c4086104d090440495244a201d1f259080141c0244584804030082d8440050380d00321440803600a8840c3d000216404581d840e40d803000c0c000d0300e1000f02e80b070f0021540743c0c400080e04061814017854228114404548846840d000400d040d040b032014251900c401e820480c02c02c01650700240b944c400d03460714107541840d00e030000c090000480d0b400014071403603101c400300e101074990b640020010110004034890a6003001d00140012500600780807100303000101c0030824084900900c502d0300c21010b20554200e4109500c0001e004024104a605418100e43d10503907680400c4200344801d512081040c003810a40724a511f40310307980d4000c0b0030740d80207002000201443e00c00708204001ca1038254404840682c81e060746491008a941c0a00c100b0100e40d9106200c540e2060714800e02e42540c04010340c3da120003500b80229180807452180052600f8480d80308241504504111001a035403980048507680d01c407402d0b103c81040e0a003681241014034019071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 919357104 1250 919355854 919355863
    0xa020d0602031f052b0c030c0e09011104060e030115090f06080f0a060b0604090204060203031902070b01180e010e03030417190f05040803031003140705030309040f020408060c0705 79
    0x7080460b400811030301d03210200c1c0c2c48007054040440f40b01c0e40011001030305042c200b51112090780c400c400080341920303450200236020307440c05001c000c1407106d80041c004010520400108198443c02c15041034030b445021119440c4906900703406549440c1611744030000802800040d10840901040102e8904030003400c403034455101d061203500c0001c1c08a00d090307003c0380d802d031241d420890114109610601203845442540d01c10040e16200150025030b05a0220203140540a2120420105060140d4038005d80c0a6010b01905044240b80104005560329120840c02c254030b010103d981c1036482800c41c2151540c4e80d60f2205604000b0401c010090f070040842401040700240351704000401e061001c1e0401968041001d100d03c101078003490a0044040d20000c20003c8112a92071919020312016841e880c801112000480c452401544001196000a80e14042d0003117081c90300b080304100c003034440c090f0002c04456081201096100c001e0203580e10551215004c5a501d10443c9040b5180c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 919358354 1250 919357104 919357141
    0xf0e0c0105071707020d0213090c0b0f03150102010633050c07090507020309131b02010c0f0311070204020a0203040e06180117070f0f030c090b01200a020d060203 71
    0x100001004580b00240e54000d00b1071101404030541601e4800510204500f00f54100d806580240403402950050a0300e4010031100ca20a40050440703130340c0c541201e110b5000d0728064100c0340c04180001040c0d08207031704c03140d0b10700305051001103240e550726188030540c5840080c69558203203103c100d02c101c00701043c1c03100c50180850700d015864851122001e88c0c49011902807406007a80354000b0600c01d61007001034a5102c400100841d01090303540000f00014614081c6502d03030150140c0000c00f00b14011301c01e440070981d513a20344480001a0344001c4000301011100c0b528425001c0c000d4a015131a68070141003180f049400a5949604283da00300c4c2080000b42441d1081c0248054074801403016001141191030b05051180e0307800c2c004410300e0414000d03410081c1c1e094446000010019150b08038034085034050501c0c450003507100c07100c0b03a040c0e9040410303c0340414001d481140c03010600a0321400383d00003030301c01e4842040ca103500007150044407580640b00c10b40c010044c081c580d190064441304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 919359604 1250 919358354 919358357
    0x723150c1b1c0c0620190c0506060d02011b032a02031209010e040e07051002010b0d0f0503120a05070e010302090a0e0603030706181e080910050c010f0e0c01 69
    0x82c000750714980e80ca096582100c04000c00c007071504050b08000042c1c20050079034001c0b180b0781c0800c00d40076018082a4201040034950040d0b1000722944190007011801a0a0781041c0900b101d0355680b81880340070000040c049040100b030840c41c42c141440d413140c04d00043d21039900e84100c03000701c1c001d20080c0c40d031480e0b9107400c50b0303c2c0ca040340740180e1380010f4081e48003151342d032840d84808264006031200c60081032881d400600b014161002007902045420a9031800c540b0b400210b40160001c81c200c50245203407039044060401c03d5030104807007103844034205100e05c084924120a12030004014402650040d041649507400d11003182e40007030400384100006e2808500380300f4404000b4143e440300d0312aa00e501d041030400320344951002e0049490703280d04030030280582c030144800c4607c8881980c0f0309940250344c0e00c4100a2425800324202d20060b0841020780c03e1001d14010880080e940544007000d020042000e409070034000e0091035a04040940700003074852200d4603450521445070360741030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 919360854 1250 919359604 919359613
    0xb010503150c07030f031b0210060f030503030f09030f040806010612050408032806081f0204030c031506030b0411010f02010e0709020f13290723150c1b 67
    0x80060700d4041520400c613010701d4980c03c0503803004015070043c8154080c004503042a11005021142c001402c0301145a41c0c1400b041b038140d0360301d1321400c10070880c003004096800800104e014440c407030003002d820690401c1640e240c2503003444202083d5201d40c0c0403074100c1d00004010001550003080005440086138818449481c20f603072580b11034840103040b42c214074092014540c1c104c003060900740e0325194200e020017106455032541940d9045140303c00000007441d240d1548602e58500075a0200c90b4001e0310005110300310b988150310082080d403039000303042d40c4800000200c1c10324a11035000d68021a94500081c03807680c00145010084c82e601019a8180702c805404194009054011038600000051702c401c003515422000f8416081c0f1050103c1c2c40620101c0e00003112154428200380300f28800b04400e5865440f081a40180807000c0c211422203a4116003540700071124680307003182e91007518200c203c1540c80920050003a03884400403500030a46140803900a10f9034140f0780c40c80d60050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 919362104 1250 919360854 919360861
    0x806010b193e0c0307051f030e19020f040c08010b1c020f13060f0804141c030b030c030105040b0a09150e0d0305010b120115020a050a0b01050315 64
    0x605050000012404001c0d6804150110040c02e0469071620414040000510000c0926080e4840601e035400101c60158043c1403182d450005204801ca4801402d40300c80740350001046441b410041c1440d0043c552070300340403840000705024105921000b90142105692a8014060456800c81281e4040c0f454500d600b1407441e00202d02030f0456204010701995288d60a000000921032400d5862030f0344d001180e00760502d4a80e2000d450701d83c0703003c900b46c2a1603554510494004034080a19408900000d0101f008031b8803181410301c443d50300382c080b512051900c6500c0d182c4852100e000d20000fa41e80c0004d10341c28502030080c90000c500807402030002c0c0c149500c0c0c1c00c46165000d05100300a031f43d00ca40b02030820204007000d42074211500401c0240c1c02d011070070592031710b00301080c00000924000010601e5003070207080d40c180c4c40c11149001c10f80c0e800c012000100615220000040d80701d021142c50000e4420088120524400c002a0305107514220506240c40300c3d04100491080d54041027 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 919363354 1250 919362104 919362127
    0x30c170a020313080c06010e13030e04021615052203021f140709060f110a0f08091e040f11070f03030b0a0e040308010801020f0d02090402040f030b010806010b 70
    0x4298204a100400594a468408800500d40001c2800400f10310b03000c90000c01455011034460b048410801081c42550b80b510895034401489a00007008608480184195801d041c1d020f40000441c0b0007503480e07101616111415401074826045001c1c503120020881280200c00c7c140045660002c400d924062031a40c0c06500d4043c80300101121501860040791700c0074054000c0140c0c1450f443c06180142030410005059800c0c3d4003070700c03011038030060301108040d105410b24040204000081c040c1070003503940c0e060300300c245e6080550b0800c10503c880182a0b880b0380c405c0c0c0c9000d25210155000340d60398000c1c0400d9440081491aa40b850516141d0049441004031500143d1010081c0c4a0121070318050b40141200c0404c1a001504144049011464081e0342e80c0958040e858a0741603070790b03684038107090780b0403e011008410700c24801c0c4204224140c010f84510700c0d00402c09401c160700c44503070f4280c5803601c2d8015075046034420010460301a0600c090783c058005070040718a4000541030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 919364604 1250 919363354 919363397
    0xf021b1209010e04060e04050d080f01030b01050108040212070603020d0609050405070b0d0e01050a05070201050f160f020c030f01020712080c07020906130908090109050f150a0917060403030c 84
    0xd000c1d0500158101020f4640d59581c0b00740064401600d4004040c00d00341062a41d0306102e046d00c902042051022620307a0080780d2150f41220350101c50085140e09001c01102e000d0400380c01282c00c181850580c4104c07841c18080f02010300701658005031200c401d00014410340c0d02641c08410070303910b0a0141310200c1c1c1c0104e0403d043e10f42001c00356036540300c424007420050000306c1f235522141d481d101c14044c000700540c00c000c2c0901c400c0c0c4d0090200e600d031503001080080c02520000d41e040b400001e031080090050b03007148074003002070041e240712001c6017010030b0030528071016200c10b503503001845004200395004803a241c0c000e1172410340c24601c2c00300032190051180c0701c0c002c2d204543d90701c0001c2c116901c0c808541001c0c06450400d1010318014600103100d43c00202c1118003141f00900089000e042403d2a24604400140580d0300200100700120039035000750122030400504040104055401c01014920700c1107810040c4400e142504005080b01c00c140d403100100302c8054170300c104404c610f40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 919365854 1250 919364604 919364617
    0x1218130e1027021903060c12020316030c050903060408030106021629072a0b0a05090904050a1212110f1923031501080907090b030703060f021b12 64
    0x4040c8440480d500000702d008074502111038072019104004410042c043d0000348414100340c640104131512341c5909001c1c0d00007158161110300580f80e540d50414400d0300710089642e0141405072804507240042800c0c80000c44058a80701c10000c010408164100500301600d200e0a40103030344241040c10100701c1c10141890100d00741e051480851072121510200da01103075002030000e110111801c42824060340d280e005224004400b40000760004107001140d109800560781c40380341026200810800071030150050391540b08020006000030501e0460b40350710f400b0303600c0d81104c120008018005070307403180440c500ca15030144082280500050252060344412703842000044409100c111011201e2120444004004405421292009400460150905541b11902005d09600654400006580c5000264004030007004400c01c903070f0140941d001d009003510102952a1034642c161104580001031743c0354002094080c10040c800c1c10040e034098900680000003059098040d03500810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 919367104 1250 919365854 919365911
    0x51b1219020a3e0c120303070c021c08071a0610121d0303130506060301022d19031d06040203101806060306020a0206010608091218130e10 61
    0x1d40020300c1411030b503141d94141c80da00e80c1041e40c21980203d4450380e111074aa1429000e8003c020455110306404000c4902c079880c140c0310865011210341c00c0c0004a200c4080c0c900c0c610003220f551a0018008000510006020707510b2100100741d03c0d00203904143e4040e040b184a80c140000304602140c110054099031810410006484103618980d524010007000e110482030000100b0840c10590640b06100e000c2d0160b030444180e651041d091608134070602c2c1c403412204242d0b00c0310803000e5048080d0542402d03010402c850500101800a20355043c5684010021075120801c2180a038880c80365640c0702039100c40241000d040c5030f00840c0c0c90320741c0d82d68074409403904c071903408248548044064030219482102000780329500d0510b00029000390316101c0050207100d0000540da4450300c0040d0080e8429006002100340c038000307540c07055101c2c0d016100c2100000310354a200ba8ad51110403603802014041c04200c0c0d07025070000b2400d041c01d0318a09040d851070000b040681081ea10011041c2c040c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 919368354 1250 919367104 919367147
    0x210a0206180c12031e0f0d1d0613021008060d02010e01021504080301080715120506010c0212160b0f03040f0212030a02030c0105070306080a06051b1219020a 69
    0x4007000c581000e11080c0c07116080600340d040e803400800b00000074115000ba0010944038442c1c840142a01d5128104244441e080c00f40082801c554031507210784146e40e6412011200c1d01004100a814400219020302a1380fa041000006506100c00108103001903031620104501e0b1420000c1d8014480b4003001c1d041140840c00040b00741d0080001107240000c0411140341403400b031130540d485500c240210703583c9000d0a000003510223a00d610001b91402140c403160f42c02890742210000a00000b0501c030304001c000c1c03421101603160440e2000030200c4c041c0143c0410300d03006480203803007616039004403140c1c001000018010101c0c40252500030380d0041c07101d030701d00540e800000d803002c0700740707455a0050000080e540c01d076540000c0208100c214041c020310555895503000e9085036854801c00d201c6070011281c902c00241290302407507210b0074801c02900e201c1802400c0384066001101010658241d8500b400341480069214190b6646a49002e500d460854040244821885040700c41e01810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 919369604 1250 919368354 919368391
    0xa2001031b08041511041e0e040f0f0519060209040b0603060f0f030f0d020d09060c0c09200c0d09091b0507080d0212040210030608060601050a0203040e09210a0206 72
    0x130103401064000340f0f5110000d84036038a0b40900640c000044000d0134000c07511601c0003404030b074441450f910803070308070184039440c1c0c24a4603401341024000c0c0045806006020407003d010602034140150103022305070040c1c40352039003c288011101d8920312644664000c0c400c10400d82e5a01e26101c0c06060255000c1e0040b03000741c2d0100b854030341d42c650174104c180264124100065400980080b94011542e1182251507681400b628501050700c006852010842420b00604035207801402c3c0900b50200044801c9401603444082070300251a610495000503400203a103541c4102d648020b04a02c2504220036070300041180683d4440d600740c40c040c03010220b90030302400400000e035000c203044400306640d25844011102c034822400c0350100d225040403031110789428030a01c10a02641c56400050074262100703801503030f00d604a20244011071100300408070310641e808074040e018885401c0103100301281110050f0480008454503a600c07182408002c0b1180c4d40000d4032034200b10104000e420901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 919370854 1250 919369604 919369643
    0x6010902090103090c1e0f03392303030301120f17070b041a10050f0d0c0e0126030904090204020906030f010317090f060307020a2001031b0804 63
    0x261694000c1d00d86045e41000003000d84401c000031610941c0f05403800049a2144c04140d041c924500010b030070041542c01800380042c00030800b00011503100f42d60004040c500c101c06040035866000701c8032021951030b41094600b0a0b0341000c200c06403c030041c50556040c00d48040c20602100000b03000f81483c4642d42c42030040c0c03056080308035100c1c401d215542d002e280c10450b4400a041c0d90490300e103030018070f040040490140b01d0714040d1944c42d02c1e00c1c03101c500e0041009264101c66400561008030140d801d0002807078105120000c04d4070040b00340300796150641c8a2400080d13034580b012128800803c024081c0310200469100c0d25044800241552070742c00460000d00a00c0d028640002000052007a40d00080b0500c07070480348507140344005814514451005030080821983c3c006240800860103403a100010399031200c058412122148090340b00c2002a100d1403070300c0003141d03a201b407100b181d40d649801a01c40c840d02803003d080d01e030404400010704000700200044c2107001c01ca4140c21100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 919372104 1250 919370854 919370861
    0x603031e05040e040507050f0d03080a0b040615031d03040302010f030f09080a020303040c0f080a150b090f0115080103110607020103090b1603140103080723010c050a08100806010902090103 83
    0x201529400445645003e1404070b580f100140206841044070fa8a465598071740704907082e10a0303030b040d2f03190703001621500c01d484080e1000d490010750254950101040b000f00307981000801e10120b9a0100e6152080da8081000801d002c848a620b03402c00c00c170600161340c1090032281c0c0848079140014007d200180104010301d007542c07000b00744407070002d4140e50040c0d0010103507010b180146605000141e82e0514030341c0c4840188142d22460b0040d404c1c03480400e22054246000d00d0b82d2041c04a451103202002450809044500e00707010000d150040c00100700345143c440c004115410100120750560321240c2090030300f4035549102e0403000070700c00d08591282d04000c2505038400d0182d13040b4180207456042c01c0b4102d080d03400000385485c400101e5040c50703500b00d6048a8029504600d00480341d1134459103002c0940103003450610404080f2307130103407007449000321004599036819140d140404004041040c0980005600c55000000303101d418000314403141141c0e01d0041c010f9549404a0040c4e018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 919373354 1250 919372104 919372109
    0x60f040f0c0f0306050a0c0909090501110304050d080718050d03020a17030a0c02071d0709150e0405181c020a06020318010b031902011b0f03020a0203060108010603031e0504 76
    0x48101c008400900381d50301008400503a485400c05020075a102d0380c0180c121898092180001234000c80e08201c1809142c0c400d109242c02034001151a0084550980082e40180c6084465a002011110781590300c00c1c981c0e600300340280351006c10b10000c0742240400c840c3d1805294407891100322500e04160081251802e02c41d072112074942050b01241c2c0c2400d0381d400c11990b01060300d06010004c5405803020610b00c01303440b136591200040a8244004042941000706080c007407211001012540c4645c3e00c0712106040c40e5a502c0110010681c41031100b40c45018000716002b10041e0701810a03e0300100e00d10f6048030b8507038074000081400d070350100c0c80c0c4918150060000d51001007800482004030007039070200030100c0020f00401c0150020705980c0d919412543c401d003240194080b00540c4500310301c00044640d20301a10f2500140e4560700040b50f842c003030440240e400a59080c003182410311043c1d0041c60701c44001c01c0624a141c030080d0403d214188149440440c90f440209400c0c0075a0640c1c02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 919374604 1250 919373354 919373363
    0x10b03251b0f1b05010504090c03110c0a11040908191803050703020315010e0a0b010315090b1905010f0e040905071205010f110d0b04060e0c0405091305060f040f 71
    0x5030301c2504100c600350003120429929040e03c0d10b0740031452000d40c0e80c0b01c1c080310010303941e82c0c1ca024a400351000c0100404030310318003050b45800380c1d541000da8203000740c0080d03105000500750782181890b004196510203c5580e002d507042004181c08507030528283c40d29058100854000440041401c44004903441c1200c07480d43d0b403a400110a0001c000b40329020340f40b0035011544a0400741a804201001c00d101e001c0300321b00f010f000183c0402d402d070401d441003c2d0605021600e403018241c0004c24481c141c000102541d91080600503918010f00b1040080b0380304c14105e4074150070180001c2250f29103140b42801e1103000342680425803a6035100a04040d0000d0a840036540c60300c0002400d1519520705580d55802c03c0b01e0b0042c40d102522400d801c058107262110310300111609800050006000001e9020340d480b4400a03542d0302c0c80000038031032040c05252645d9a070502c01040010003019100303007444424500407000184c00003928540040407800c82d01400d41d03035442c0c500c5c10040d01250082 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 919375854 1250 919374604 919374647
    0x50f0321090a1b060e0a380c0a1406090304060f05041d1f05060301060309021302030f0601080c0a0f0e040e01110a1b0503041a070515150f2d1f08010b0325 68
    0x1407223540003284413643e0758801c00c420072114268400555642070180c1d0014100e4208020800c000d80c0104810951001e040c02c2c041d0510340d40d1000c040b14034000484842070011014100500c010303041680741805120b01d6240100c00d810200890341c00d0205015031070030f0640c1c4001013015544c402d103001c00300d100c000d2425540c0b40342070668442e2458040d10880c0c0070504079000702e40d10158201c282da002240301c1d80c0f00414503a45413421107000b564400a26006980c81008060704c1100b03024411a40160f044040d5880d120114000e0000030050456000d590016203210700003074010040340c0448030001c030010ba44592400e1040680d00c075000c00100720f40300341082010f20b138120080c0c69100e0780466090030060030420041c07020343302007905c00c0d592042450440003040200005111800c210481c4503c91086a99003c200615481c52000070a9000608000c14550f40300a030703d405070201c00c802d00e0450a1002004540c1944040840031044901c0080c0411510480c154001c5090400640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 919377104 1250 919375854 919375867
    0x61204151d07050a0501090e07050304110904050c100215011a0c0d080a0f0902010e0d0c1d0f010801110f090103180f050f0321090a1b060e0a38 63
    0x140da4030b109901c181805041440c42c009015030141803c8811101074100d03010840d610340c50100d0341503000500c2201d500403d51061381064542c402c009118500c00c00044c20106850380030081d03500180000c04086501c007498121a1906100845045900f40000c0103240e4501c10b1416800c1d00500380c00c034405220300340d0305d03c00303059100e03080300e01a0801030020484291980400302c287c1e0518100a030100c3d0080140700e11034101301880200d020f015240002401e62200b01940000040d003802c0c04020f0720010600a00c1108808024010110311000f00701c000c40a480c0c003400d60242e0420b2100c2c0040204200c2101d90194008691001e42c11f03440e15280a01442c0181220540c1d034400e9505108004081d11500000400c48804500c100300f101d2010030861340c1c01d01180001452307412540200030141000030000003500c4850310140f0100308103103041ca000146030b01a04400e19200d03100706901009031112140c4903009041d0700d40c0c000011505540c4401c0c0020131010300c011241300313002806 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 919378354 1250 919377104 919377161
    0x60d0905030a1115010e0406060308043b1f0306060902042306040b1818090d020a0308070503070509120c01090807050a0b0715110a090506120415 64
    0x2030901890700d444102e518414204000e580b900034091316806451840b0041c001c07113295200059000e40b18000c0443c0d481d880e82c2d00c01260760820751221454042074a595050812000508041c00d00c00d484203401c0450f914001e0914004d000d4155243c4418115500c018070b00d425000d40c02450f003025060100f2541d40300b680c0001d500620810300d0000000b14240000c00748100d1318800100000c2002c0c2c100380c208510f402d0316a01c0032440c0d540b414403100581009807a411007554420501d40003604091030070b01500da00b44107040303074281c0440d0400e43c00340c1d0001c2e0304140702d140c0180c40703490115282da0707078a141a80c0902c20300b041d10382cbc0090b0030700022012680000f1403e03140c010a991b41079180c0d603540d0300b4559400e401d001c0d403603000051010900102424401406100340292803008641201041c40d1003111610038091007061340008030700d2200368000a1000c01002c2c152a503d10b080d000c102c03441d4190b0310152000f4031500c0492440c81100b00039411640f0030581078481020b807465003201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 919379604 1250 919378354 919378357
    0xa05101202180a0509070e040b0a1206050703051f0e0414011a12030906030a0f11120916030f0201030c030e030f0c061f090b1305090f120a0203040311060d090503 71
    0x41c40c1c4585500720f00403c0e2801d20a1a0303500404403502c9242404a0380d02c10000681803010410b81c00410341d0000060f4801203400071040503000390740014240c104018001d05072100145541032040301c01c000c00c1c41a44106001c0380c22680e1246985034142c5413480c1115002c420040480140d41c00e01c040344c03c140111a1080e5900d2004452060840b07031074034212a101d01420107955405a01030000036003500140d084404510341e001c0d800102c250401d000e600241d0410510140603204030020060b104e0b500b001070814800c0707400301d180da805103143d8a131510700d031507003600a040644030401030001901036007008443c4454542583d4941a1803038682d003031900b052a5102046c400d840c0455154003010a504480c2c100d42c0810251990510b954640074004061203503400031441c0341140110942d512545009408150280c10140d0360b1410319072500311103a808010180003003140280d280e80010485040704d50020800c01900c08000000320345004d5031010000e018104212042004400310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 919380854 1250 919379604 919379647
    0x109050d030f06030c2c0915040c03051510060215070e030106031502090103140c0714031210080d2c030106030b18060f1003060b030c15040f12020a05101202 69
    0x281c40c0c00800b086803a2015034080c1e964034040d230011074032450045142252030340d004d4014084c6121059890ba9a54600450380d415854004c0080060084601c60415404014840c502c014003105a10700c00f40500041301034400c800303001e90b2002000b00d90b10290040c04c000e541214401c81080002550b0b00040d610810314180042c2c90f00348a4881c0030307000040355008007450200541841d06c55541e800d44c032000d4208a00081c0310600c5030703200b019140090b03248103010071102ca240c25460300a0491a09542030000424407541601d80036400704080e54400c8072842c0d43c10b00304408640e180c003203801008140c1001e030040c2110400c018030001255200b030b8191640204881d00c03a030b50b1461100108909507001c03a03c00d4184c031030400110b000d075040200da4034030080a0342c9001328054005181480d80340d54201e00c07100d003c5010401c040015840d130005258401c21030460103c16400100303180154041e5a21030345405059034040c83c410040c21000e8190201c0855844017034030f02d40058418140c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 919382104 1250 919380854 919380899
    0x4030203031b040f0302010309020109090603050706030606021b133e0313082113140d1b0602042102030105060f030316030216030c09060501020109050d030f06030c 72
    0x2c42800c03105520441110110796810f0300100c100c03400c60f4011005009210710070380c1044036401c4007003100751b11486100c0c000d40c401d13401494500d280030806010380e0381030790107001590000c28055848480d40035284c050900300310382000c480344201000c04010004520500400c1a44080c241d4440c0c00b00d0080b40c0c0031885140d041c1102d410500341c2600244400c1740c412075050508800000000d9154002c0d0050002800d0280f10b0003c0504003a140141e0440d0600600340303590240300305005103480c152a201020700003901c44a8925100a070101d80303034280e83c4960320000c13900c04003813200c1f0340d05607400b51845c0c1c042c00d0008140c0300130040f580c4028800c00d034425481c0c4000305400b8645400c40614012025018604019036042412074620001030b082c0e09600980050044442034182220081c40c4954030305200380b07080010680031a904c40d044907040da89046d0184001c141c00040203141000c062138080303100004d030304000e0050a1141d100403c5803010700400304c2c41c0d038030440da40c4943c80c031103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 919383354 1250 919382104 919382131
    0x140301051e0a0b0d270f1707120804060e0c012f01020a200115030210020a0b0c0705060f040b010e100315090203060a15050f280e07081b070303140403020303 69
    0x42100b400240001e0000086c000b60728030740713031000096014030381d805d45800c00c039400b0781800160348408100300a008548030004840508000401000340710710f01040c020300300180002503a40c00003800c840c501a50000d00c054036681014107030042d100114802400b107500a5403502d0180342c7c0a00307a07104804d03000d5031101e18522085c0404d80c052044600b2942d10080010820345182c0074001440207030815002140038070fa03180710108000c010000d00034100c48802d030303541c3c0495090080c10500041c0c02c2c0040f4038520801c1c8000300d80c6c0b0701d20860650300c0b146180b000d1903c0c2c082589105903960351008100d60400c07030291542c0b40a991110f0699402541955200d03500e81c0e0b940700444421030b07610f00d254040074000b4005401e00c0c0300505000c01000c2d091213403d50b510021903403940c01e405e881070440080310340140440742c10b50440c00e410101904080425080c940451400c83c52100c44c7e401c60410045480340030b240c801c1d0801003501002c4c0303c1a10300740c04c2900f002522035000701c1c0c030003203003108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 919384604 1250 919383354 919383401
    0x1203200c0f1908300906220b0309070614031512060c181c11031501031202011d03040320091006020d020a0305031308090604090c140301051e0a0b0d 65
    0x1400132a540c0c106a0340759250314103903409080000c5c98004140102d10351076440e5134042090321300a40500038000c14021035441c3e02c3c00150503894880c070b6400c040d040190015440f0042100e4005580c0c000c400c02b0041401c80c1840b030040342c1c4100e88000940400d10a4109010100e40504010031040e00080600080030b050340042c002a943e10040c002028009514250b000c9408031010109035000181990600a880b0442c50007000d000c0c0c10555030200601e200680003034091041c4c0f840c050b0101d482001c560506411144c41c0c3c012840041d06040518012516200007001c0c418580000149600c0070b40c109400a40341e2803c1c14041c6101620803c544401c110b40000b482d132010b00d03490395400b0b107180e5660715034401c11201117404070b03102c800c240141c42c4c1d9590303002e02500150507010800189280c2264005026145200b140603591000300014421611842e10750880700c02c5c0326510b10003501540d004500d042205900200c403109010801901d95003440e00034000c80f000c120030507052401c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 919385854 1250 919384604 919384663
    0x6100309050d0f0504080a050f06150108010b030c0d1a01090e09071e0f0810050f060f2101050703200c030418020c071203200c0f1908 59
    0x14016000a4203a510580b4080b0010384508980c1c001c800803071520504245c0c2e07032080d03603150030101f0408480c140c002c000c0c1a500c91030200844c03644202403000310050560b505001801d0718006002da0802c40d04d000001034031000782032081300d5070351404110402c00c0300b15600c0c054204800024005000840c1c0d600d00290f101d0703c0170469800707000c078480606616841e18600c450040005007000c00351038900c100004450702001c2d100e600a0a01001074010403103001c45820880304002e0940316280c8006007840025100c000d0b80c500550421760300c0d80e222440210410805020550401c0751035802d05042012282e80364200c503021664181c0c000070250780b2031070811100c0c055000ca0000030f6006200821a00000706003a480c001c948500051400e04641ca409003007054580001d0440c1103005401c108156000d05590018044145110960280784080c5900c400740c034040d5521406081c4070030030955648043ea850100140040b0390301c4565240011a00ca1000f6194600394090005510a000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 919387104 1250 919385854 919385861
    0x50601090810090309150f02070e100303050708091504180203060d0303051b131802164d060304030906180b032a1608030903130e061003 60
    0xc80311030002c0e01d19031400800d0000146400001079003003080150340010754400b4800299044281c5965060226070800c0010b841c111056120010740300340340c0c1c10803200410864440d001d40b03901d45032503035403107011b424981a140a005c014541c003200d00c1e00c40c2140020200018022240c0008562038400e03e40001102240000c4454a070480e42000000c00000c2c400c1c1e109951248040c4241000c030120781000c42c1d0517802400300340d00c80c0b401031041400076012191500202942c070036030951038045502400080039003005d0f001011080b10f000da00520405030100e440d07104040c1c024280d9200d03c0c3c210940198104805140c0460b45242c40004242c1448400c40e403080c0d0305034607002011450301c241241c541e5155803100f21050800070b80400d01407030040055020f200180c418050107050070362018010400d20f4035658032039800f080400304051a030404075800541244400d07840742c1c0c03100009402c40c03141e0102801085981c510202e20282d41d0030300c05025580c00c0d41c030200c4038450300e40150f040317 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 919388354 1250 919387104 919387109
    0x306090c090f0803040b0909040512030f011a03061e011202280908060f060d0803160e0910060c11060a090306060e1e0604060e070e0411090609010c0c0e04110405060109 74
    0x450200300210759160404040c8650024826030445010018185012f10709400030707101c0134000c40d60b0100400c034506014986808410412144c6031450406500040c4107091804607a41d50b1100342c050500c2503806407820003164001038509640e500035010320550310160f00e07104013006150401d41d00aa15106102600640b40224001d0140707440d840011121108000c003ca54000e1001607040b00107007201000e54003c5028188040314141c40b900060100000c070850580101c7c00c000402400000b1012803604903030450414400b41d0314207040804080303e104010b160080c40000f1a040c00c0c5500c500d0520031240910810803140f9190b0143c1c89100c3c0c4191061143c403014604109401c5d4990340396950041e10042001030407a82e5a0408103c10904444950120303054282800a500b42030040c01401c04485410310b00c1c18519400044190203140c180d82d0410503054840420000720344a1840940089203100c0a00c4c03410f072030076600442c100da0540c0d014904100101e8441d5000c1c00d40c0070107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 919389604 1250 919388354 919388369
    0xa27020405150c0102070c030b01050117060303220306090809030709090203030304020f0f040608010222080703140f0f031b01090f02041a090c0a030b0108071e0306090c090f080304 79
    0x40e2500066052401a04500075003141558201b00c0900040d00c1c124443c2c0086204400c048030641c948000500381159000e900d120f154060000c00c28695404000c0742c005000c030341d4903041c10140b80d0300c001d00e0381e0380c1caa003005240314a000407020511000d540a0030190700d040701182d18480d207540100c010b0740c52002d0002d4155000b4004100103240c810b01d81410848003030000400803c0c103c3c0003030181c0d6060b070b001d074171541d60006008a844442210001801c0c8011034011441483c00f2030403940ca51081c48040c08840240004540d01c42042c84001d46520302c0c0001c0f80d01419071162101d07103e0b4020354035140320600d00ca003070b40008071040c01b40081e15030300500300c521504096024800980240b810360400c00380700d510403446540e24217600502800040c903520346c44000e05203015048568143c1281c4c1071195880802c481c41c1e502c54070340082035101005146600d4441c100680c054080754010b01812810000b941515580c0002043c5c101d900b0700c0d540f00d60303040d40d5045a1780c4902ca1030041e0312 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 919390854 1250 919389604 919389619
    0x102160315020712110601050d050709090302190b070206010e010e071d03071d150d031b1a09060106030606143001080d030605010503060409060b0a27020405 69
    0x8120074801c01180c080301c1000142c50000e90f95601d000c0c1c031103002d405402103140850071541c8032004200340b901400c0700303172004201c120325915499602c1005200b100012512821228201442803140e901e019265140d4822400c08601d803260210000301d46039401841104000110083c2c0d65203604e0485040180a9005450300e9200f00c501080b04208494007040a040c038800740c0e242081078400601e000b00c3d24003080c2c0300c05046403543c207034060700070718400c850800281c2d4141d0310000202c0200b03078541802c914509094025942e08007614401a0010011480400c0f1001c911703e502485a41c1c80e40958025a889010560890f802400340c0c80010b00c04508000c40c22003800010710380300ea801c0103106d071400c1d010700c020a810754005c10851140140c10780100321110007000070001b00c501e141001d10074581010002045130000506041c41161200040001c0c0b01d210f902c80c103580a4041c246400c0940c45070b00e1501d200f41c41d03020003c0e4007005000b10210b0380100b80b0079035013079510041002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 919392104 1250 919390854 919390859
    0x3020411032a22050a0f170a080f03100506030408030f0915130f1b080f122a010c02010222080c0108040311030c0a0b091501091d160f05010216 63
    0x10900720f0290314420302c0c021100c1010a199032201e499000810320300300c021801c14241004038016410035040042c80360300109494000444c80380a03940c03240b04030b2017806c1c2c0b40e5403008480a0441c1e0140d1200e40c20080010031301c0140042c1d07000442c41403202d40c002c10380c55110100840c0e40c804403142280c034400300040208840302c510000c148495401660310000d090b016846240d44060f110610008082c031401081244040a01081000850190240440d0403074440b820000c0c0c8680c48140c0d103410b814001e0004c4003005d5426041011000100804c108040301c08084d001350700505105543c0081141200042600400c091080c2d9440380050190303030000b1b80c01900c02c0c038000391007141401042c0c01c80f00170300c06041028000c0c1d002c0d020300410410200e801c3c4011003d4010381002615000808800000a00044480e04450300c0035400a200c4a2111000201c0b00d1808084d20071809100851407188400f1188074042d10969425400010307030f10001a40e441c45001c810307680b082c0200408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 919393354 1250 919392104 919392127
    0x50a2703020420030114031e430509100b19021c0221030114011d0303041d0a0c0c0b0901090212060a110a05040e1003020411032a 57
    0x11050355041c800350702907200416000b0f507a640c100340c1003401140103000740800a441e0400003014852120700801c0c4041580a22003070b00c5144190044540005082e160b400039810013a5071100030101c0025802d91a0b40320a0f05200019144115882240080d022613511003520121130300300d0740c00503049032418010541c031801e0f03e5016000c0c1e20a5000c0e20200407600110414003010b12915580034219088143c035107807440d91842c0300141030f541414001404000c401180c1544125800d003031105a401484244241058080c0c0c03241c3e40500011034001030307421003030b1801c070001d08904400b215503940c0c9880020407900c5030009540082d000f0409180450704840d65103170001e08801c004180f603490381d004180e035244098070300306840d4002d104101d0340c080705124840d180c408a40020307140c094000d0b00245240258040e1a242c100b4010105048203140d04a180040d030f030180050054003040400d1070400e400c110341c0e01001c00449511400580f00740c00b62004c03040d85500720f441c1000040c000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 919394604 1250 919393354 919393361
    0xa030f0b0a1a160f140c090103020d0c0b0a0302071509120818060c030a0c0e030c01050f0c0a0c0e09070303210f1e0e070315050c0403060606050a27030204 68
    0x60074200208004814411041c8503200d09103500031007400041042501e000d4101708812202d08445800c180b004185035565071080301c0c116901200c090403205018204607003c2e00c401e0f48420f04030400001c80c0541507405801400c08580528400741c0030300c00412194090741d0407400011702001881140074101030241361102c1d0000420340101d960303404090364051806109850742c028003c4040100010781589005000d1525641c0c5445164001c01501082e42c41c1000c20441c3d062001c045801d1500301203c03000e898442010303000312903512006050140c0140c820780102601d203200f000003d0f0801400103185030450f0b0b030642c3d0344684120b00d022920014604034003995405603c1d03444607800e12070240940040460740320f82084400c00e1030030210089440d202c5c10150305410403141080031402002d80c501414060b600c020070035586440d500d11052140c0d420081442c0d02d0060301049044e4000043d1a41091070384403030405038504841a80c0004482d02d42c4101b0b002480b800f440117090030b40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 919395854 1250 919394604 919394639
    0x1603020f0f16080406020105180f0601060503150d08030612030c250b0d0b101b060c03060e0c03090601062a02011b060b0f0d0c1208090402070303020a030f0b0a 70
    0x58800c0b441d810b0340c3c1d42c04140d81c041d0b403180c40181e444d0f00a2200c00c100c1d100308908408400c400070008107207540c000b0798489205110384018010080000f41164001081c415007400380101703010030840f182d24110700c3da41c0040c1d5119000d05050343c4048901c0d54000100c607102900743e4014011015100d00c1e01c514401c103880c070458190058400040c00c01d801c1c00140624005640d40410740110f05018030243c1843c2c404500c0c1003202480c5200040c16124800000264000c1c01c041041c0c12a03000a07400f4005c198401c5030040026003c02510f90960806507004000d0300060715416641c03035500b00c4103400c2d40040c002d042c81c2030500d071896030760a005521000c0c07481810014620640e524030307101001071002d81510b0700c075241d00802c841d528040147c805e850b001100c12074071909168817616022466130042c500701d0070304c0000c2c03801408050800d442100f440140305540c2d43c4a40c0c81c3c018040d40014118802090400c560354501d0205401144d1207141c0c0034040e04030203031900c44220000017000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 919397104 1250 919395854 919395877
    0x7180b01080103261c021c0b10110309090117060702010b0a090518060c070b090d0e06030408071506080c0a03030206190b040e01021e0403020d030e010e030609061603020f0f 76
    0x10081145e8411a440c8507140c05141c0a00060b140c0104030b100d207035849510104000442d2400c8a400741c1aa01c40c030380548440c00794549200704070303004503802e49144100d08101d03070b01203c08000003a120b003181615040160002098030704c83c1d11103100c140c1c240e401980c41141d2095a04c001440f04224681c0005c1c1e1022550185041240441c0445414414103840c502c2c40a40002401c03010b1045501c00c05070044000c00040030340080c51075008007030340c042c1c03d10544240350010110701803180480544588a4201c2c1c1903614004100070340300000c0c0f00e18444c11310140900c8808540918001c440901101c0e01500501030603540c1c50801c80c003010240340002007080c2e07248510411502c83d4465206101815000166900484400b01020500d404080c0c0780c4007004200c20700050300c03200100524030b585420080c04042c4178400584414108240300383e0107125000400101e41c0c40003814034010302116004145409016104606900c0fa00740b0700b0b203003031200b08000707a001c4440d14028641c4003142d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 919398354 1250 919397104 919397107
    0x15030907031119060203040527011401050c030409050f010801020703080c0d060f0e0a05090d02150c300c091e010e0d0b070e0a150804020406050307180b0108010326 72
    0x80c1c00112080d907150b9080b044c01688046018070880c10120040103031a80c80080d032614a03207005d0116003c0c00c205011355142003c016410b02446e9006000b6110440560b05c1034035113541c0c4070040c0b80014002181e405000e00c415070000900d142c010700c2200c42d401c1d056965500103545040ca58615940440c0d5252344003542c9040c001603a0160a07031901c00307050058100c1250b8106165803a081c3d420207484241c140e0001c400b0b90341c1160300066080810b02c8400d079481010f5031600b807428100d0081c544060303042140e141141305969400450b404581040c42c000316100d40340c040c41150940907003c09550410025003103401545c018105031404000145008500724a610001c120154201c00003100d2a0050b0001d004446070843d000407890b04040c1e4041031218a820712900820300302500d014140b110904c003050554942d40c03c140c001d008040e003103c8480c0c1d984d07010101e030b40030070300d103600040c504d0000380d00c1643d80302c0c0c55030078122600f084240100d4112800d4030304c800018200d2901c43c4460 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 919399604 1250 919398354 919398379
    0x90708010c020a060609050601080406200a05190815090405120c060f0705030c0d150b130e060406030f080c03091807110706120e100f0b150309070311 66
    0x4003406540d5001c02190301500c8404098a00301c1c01350ba0498001e000c1e803034140420400b040c1d13440185590b01c15004000415000319440443c2102201e400f45e01135900341c0000d1141000e500700e0014101c0c0d4020000d0795406481040003110140e4088d42da112429845100b00082442c2c44025581c006004400752004243c48005103005580112604d0540390008010481804007641d040c517400a10340c00d000785545412251880240309200031910710a41d1903400100a400340314005001d03004000c410713996400f01c0c3d040c080c105030030b601c1050b051150050005025040a0040900300c0e50300011003005600580d9448840d038100d25601c0c000e074841802080340310394602c0804800c045452032070202904100c04000e00c030b508400c0c41d40140b548640c804103c41d40d84114055104101000c00281c203000b1024441d003000094021151058101100c030304035030b0001d910544044004480c140041070b400701c110a40d6010440300c181c901c0e00451030400226640c41c0000d2280e0790020040c1780c6021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 919400854 1250 919399604 919399619
    0x103020c160f08060705030c030c0c0f06270705030c09090a080d200a1d01090b030108060907080724090e04030c0b07030204030c0528090c03140606120907 68
    0x1d40eaa20038401c0d80c0d0215810000e80070140600c6401034104c0c9055447c5103421038030700c8114400a0600100024002242103242c0800d012400070b82260310140d0b206420f01d0301154050b15100000d40d2030034011f550f110811103600040c994110f503c040c000e40441c0c9840c20800009010051a83c1654021080620001072500005110501004500003034107070039000b058402100c40210300e494200c2c10001040303007503001000c904003400c503030040c2e04900c01548012034400308142d0241c0d507000f40110000c9404100412410712a01e111000c0b90101daa6410040d5503c503810b204148070101e204480c0c2c0802501d18007007410004040c104400c0040e95841c41514254084074154001219145004200100e078102c540d08848540b4084d0300305810740c4c035010030444040c403508c1d00c078184c2047c60502004100c040c0c592811034000d40d40c8080d41c1d64011440c00340041000c0e420001e450300110414400350007845600230351001d80001e051519441040611800c050f0031700f1068428090005500d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 919402104 1250 919400854 919400893
    0xe100b030c190504140f010908030c0c031b010807120207020d030f020d1d01030e010b0406030f0506060907050909190e0a060b06070b040b070e0a030804030212060c03060103020c 78
    0xc032442107074903903600c4802121181106603540d4000400108001c200401d03209003100070b450304000c940541d04500391070010703110300000d030b030001141d1702011448020340c0c0c40200f410507060000f075098540700c1011820520000c007230586680c3c04950500b002c02e10a82c13050340005002d080041c0300502d80105a0001490341c0e20b9444114006228261000c522035414404030b040d10f5001d04143c09206805550b00910840504c10141099520701101030358039400d42040804130409401004025101d050109001040b40e406a909200342c401040890401640c400e100382c0042d0345080c1030408640c100010804007030315008004403440c040c0c5400c42c0c0a44070f42008040d4070300c000c0400800516125065640190303c1d14400d5400740030410100d0611085560f100d5844001c0202035681e0074810380d044d41e065030840790841324169011003003090400040c3700f5640204c0340300141d6000e1051055407403c1c1184d01a0b035060051010580950094004d0500c0e17006800c1503824194030b03810102c050703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 919403354 1250 919402104 919402111
    0x100c03180506030a020c150405120c0a0b180f190f02060c0d030e070504090506070305040317010303054f08010e010204050a0b03010602030f07060e01050f0708061206010e100b03 78
    0x13019030026010112820820902c20b5000c480404a541d40c94180c907103e40300c8441d0000b600c0d00385400120860b0501042c0000078009070320102241580c1072850010b19200ca030300b0b071003010503ca9004035046802c4001030342c23420b00600724030030140a8003e44d51f102c241e60503400100e801800601042801c5c000038003400d4040c000310b640c002102e035980d0316140d1800e4041d621540c000ca140000c0d02c0c0100c1d40c0800c0c8594444114100480c80303807528582203c0c031801000c0c0e0039032031340f090720000b004040e4000c0041c00009094201080d0f000c030501420f4a681d610703400c0341e03100003103c408501444181c1484d80c03006c5c10001074030f21200030340c0c6200365800d4a0f24500c1448059500040078020362034600018800f0b00040c025044c00d560501d00041e41c1d920403c1a1814100004103900d41040003603001204110b4214000744a0303810300d80b0b10b800304e020003030f2010000314600b1800101a400d01078110b000080e00b0303070004d2481e6482c00c01c0364a8598005002c40c02c000341c40c1100400d01d6a40b10008500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 919404604 1250 919403354 919403371
    0x604090f060c11010510030b04061a1306080c060f03070e1c0501090b0711030f0309010204050a03030f030b030c01020a020909160303050309070608060105040303111005071d100c0318050603 83
    0x303450401c1c1c4000b130f0840d94000c01c42d8071500c40c3e0071783c2031022410003106542e0296014400140c140c1c4c0043c0714400d00300106064a0744203182450f40f1217600000e400000403100b43c00304440c6400d00d02820002c00713008108001041d11020700004440c03521400c0852070445015040180c26003a450328034902c101e03210000d54041e13464491603010458031620007984048a4175060801c42e051181a9803244240d04198989400200104800c608290704540060030000c00303102c0216902e00e8050900030200c000100480d1820350030010354100881ca108001c28164003402c141d11a5608000e143c403000342035000f46104030700d400e2410883c0010180c001d503001b070b25040e0b00c91a00070361203031904820b81c00c0f00081119107010300205981040942d407c0e04d80c1030412031b1220034840d03205440d090820420340d442c82d0608042c0580c180d00030ba03981841e40d01c0410f03c12420ba402c6014404036002c4003104800241c440c22601001c0b0303204050742055030110720690b201496031a00020855041a01d0110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 919405854 1250 919404604 919404617
    0xc09051b0915270415060809030c1e21090402130b070503041703090901061b2f09091e0a0f121706240c071205010b090f0604090f060c 59
    0xe40100d80700c500b015070f1003080f5002d000390b000300d0703c140c00d00f044240f0940060115590114003084420b00a50f000406910704460600d91825801c0700369015051390303a4035a0250025141d0700c2d102144c2082c42c1544071403151864008040248402580252024000c014504401247c10b01c0341200400d242030182c4001c585581c2041c091104203640040080515031040103040441e0301c601d1340141c1110a1070414145400d51a4142504c0800c40e09000b00713186040003240c0c4840c0102c0312a03040c82c4410f114080c2c2031840140c180007007440141c1e800707207256200420340d00b44c80b44050a80c80786001c12405540d4407642682d11600010f44410302114010526000309481c1c56100421410780b2135030107240e1074a414144003144e400403103c010355454500c911450003002d5003050850310840d407070304100c9a0b450340c0c41d449026046c0b10020200e4a6500704101e0049038a411005076000d4048071a600da2240c07030f544200402047c000c0e400b1124400050f07d09000720725944110103020903241c50740c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 919407104 1250 919405854 919405897
    0x5030405042409020702011b03030501080d030603170703181d060414151f0e1201110406110c1c020a0905310b130c09051b0915 56
    0x2515400180082000c002d601699240e1460048401c11240300030350040e550842400120307040c0300e001d00036804194001094004040c0d05502241c101d5050b0008d9914548003003004400303440e00c600c006050700c0b031a600c040e80c00d10100d50041202d0341c401d043c8580c2c0070b42d0a40180c41d0b824410352100401a01d208209500762550311102a8092421501001818107007070303c51644602c0649103600e180c4d07004140d8416078907050040c11842c910340c21082581a10318000400724401d01d09814064088001d1559806d20140621140c3d2481c2d00b210505107030410030101e48007001120280e00612510050256035110900b0700c02418442407180a101c1042d8014810041e40e9944802003013480c2000300b000d111a0f503c408030080411040801c2c458003203a0401c442140b04401c06040719058000f40180c01550a1211031858840c600c44200c4642e504486000c88404076200c07800c42c61030720b4a00c0005641c00c0007c000c0e00ba0010480200c4520700721410489800800080e00d41c200032a440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 919408354 1250 919407104 919407109
    0x1c0b10060216030305090d05060c04031421030705130909110901030305090f0a091d0d0908030f071505010303050d0b041a090702190f03081503070308090102070b0705030405 76
    0x1080040c01060008105101c030010380c25402c1019440f0140810201207440083c035924280c2030070106030418112040c908080e1144100ca45c0103100c1221031020724500c42e000c03800c010402220640c265100c6048003a50303641c00050341e43c0014081802c00004024502607a003010200001620700c4c4003000881030020701e04040803000014951b48030b5854a00100000380d0b100b03044408020050301c2400d038002d01000494000800d94010001507400d101501150511292104613428604030440303200703c403548403d580010b10741c040d40030250000c100305a00011584000c00d00d0610480181c2c50b02c0c0252486031044500c2071b001200087c0f8002070281a507580d5014100074402c00716001c220361112040f19105515466000070b0203110000c0005000324000c0c009001c2010348507151502800d02454100038861f482d0b036080b404120b00c04041000d20850240900c8401c0703000d001486042e00b96100c1444542000b19613034110f1080500c0030030800c5404004e4090680302d03030000c50710740382000704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 919409604 1250 919408354 919408381
    0xf0915011106160f05130501050c0f1203040b01050a080a06092a0602010f0209060319020702131515050d0f1803082a04030b0a112b0c120b1c0b 63
    0x21360740c0c01c2203c1407080224a041d4200410b08954007400e25640d688481c0899604060400c0640f003154041c1f908a00001d0005000651140b17104080a0116a03200e20070400c00070041d0041c624650b010907800300c005840d81c0c1c81040c1081c01103620030392032001c41500d2580710300005012404080910810003005809003d01345409080c0c13030040d41801c40c558040342e4207010040038026802401c8080019200f00e40d0f04443c90710783c003e042c00f07404d00d90f00940030000e0558100c408490000240c00080d50001c60781c2e0382100b0042503a9441d203040c5000b040c140c085c043e1280c82d011680c0c1d130307503440203c85a60003516600c1c940c46174541d65030918000c0003200c004242c0e1010801004080c174228624803c01004950669900142141c92038990b200b12000420b22003901e2151002d00040a003c80c041000101403501041c50580191218007003401060f10314036280540801d0180362107450311211030b001401c3c240d40180101c03007800303506440d6043c0307001010010f807001c2074480d0600000c102c0400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 919410854 1250 919409604 919409627
    0xd0807060c0924021605030c01050d0e12040f060e0607030305092d1603120c05010b0d110405070309151a03010203040807051c0f050a1206080601050307050f091501110616 75
    0x76911441440c01000c82d0700c0b031150b01000d07810008001030300e600c0c1040714cc0c03184d44c0403000c44c0d045802a1210918900c0e0642c0580039600d0010342404002800c14071500d940f4043e400040d04080c1090416601270b0301a1078080d002201c40d001e540d81050034400c040c45010160700c0000c65138010f2506100c40c5900b000500716100726805401c400600101c2d800f01d440c80d10b40344044c0382488914110b400e02c07a00410350011042d40c09030700c40600e85d00b80400803484200014040381c08200c0d5440f64401a4111018068014290b00200c0410700c9403291551046041c510511a5400200c101000107170072640215000c4800f13131070103c2d400c800d00c10200100218031100b080f03080b5940192500250400401304c1c3d11104001c5c00003007404107d845200803e050f00982d0310706000c01916410400c1c2c40e0304c024080c03580244203028001409181c40a00009800c1c0040d120782c6468640a04070a0600c81c16100207061140030b145940801201700407075440703900048228588403003a1813000340401c3c0a10b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 919412104 1250 919410854 919410883
    0x30c050d180803030c22080d0804170306150a02010207020324061e1c0f0b0421140a02070512030a082503200c06150d0807060c092402 59
    0x34010000551908400c4480310780e400004100b1038646c80c00108400c3c90f0070740003030700b29000b1130000b541c5c099003191040380143d04c076840013068a04820081c8425003c209d078196880f0340d003005424068035610004100210152002514052441c0c0200c0e181800e20300f840d111074094441958107002e40070308507a0704003c2c12280f40450301076249606010760750b400d13a003920803421a001d0310001d82520041800031507001d0301d800c015074070380c2c00e1844486a0850301030f90303586081c452200c031074190040f400380041100d88941c40150380103500400c031a00b00030080000d42c41642c0c00410150b540c003060300301c60541000216510780c0c01c6c030401014440050824a00c25100c0343d0300001048a80e001030707691650501d40014400c14003050180182448200b845c15000001018922641c1c04100148102001c1d000d02840103844018400c1c5c8042c20400a81180400d100784400106e454021450341e4a0380d180106055880e05001401c2d20404614880c1b000c08488049403442e4040c41001c0204806 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 919413354 1250 919412104 919412107
    0x714040b1801050a1202030a2d051b04030f080d061e050901030f0f050a240e030f030403080901020403020a090b0405070305061302160b070c031709030412030c050d180803 75
    0x4a01610391174100300f1041c1d1a54003c80003e8070808240e004c0741c807000c003070781440d12012045001700c1304c00b035080d00c03081c4841c0b414030000881007a4612840d501040c088290b00e03140615581f15034800c210725080460b07034420100002d010f4403081c5d00866002e04544461a64100780b0aa00300b00024500d6005070b019410100040000c10591410b050b500360700b255603a0700355505803030b045050a185c0389004152841e0904808030703903410080c1c1c504c02d4190300c0c4002c0020b80c0a094140b5030f030740942e09a06074200800c00000300040c0c071810003250000000b40015003480d813aa40054500240d503001882e00741d43c0d0b007801825034642801084d4000215003001c110b07605018000c107806250030120002419000251101821001140e603490140c2000c240955414203103c01810621700c404207400081c1030000c03200501858101e0240a0610040210b180c54540310003951000040f050580a0101c2101410007061092041d880604c1040d42c552500600228001550000035080b03202950700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 919414604 1250 919413354 919413367
    0x220204050c0334050903030d0501090203100906081b03190609170304051c05120a0e120a0503010e040f060e0c0109080a02030619200703350714040b180105 68
    0x10010001c1140310204c2c5015941d900402022038614032902480c903009a142200000c0e42c003460341d0195000396400da00d0020080d80d00c074412030940e207690056442c250041c49400c004031f0f0201609400000020302502d11455078000001030001d14a5020f440b415110044182044100c40341900500581030305107003941015180c065850b074000349628480481100c0091280d8001d00903502d8030340884118852500d44803a400f00079021808030010188611407143c83c602c0d05c24403c1c0d5152486650b51581107a28000741544841310241040c0c40c5014841d100c14003140c558040d400b010303510040100b1000100c8400182140301c16031101010360016030a100059070702103002c03134114502c4250002880c0c400a1240024103023449070400c54094455003140c000104006081807900075161101040d2401c680d007000c005807200310024680118400d0140b50300940e003900c2e00b0a60b5171814100c1b10901c5040150a80e000f03403c000c040a04c0400e1000381c2d81200244401d00309000c0c0b03021401e010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 919415854 1250 919414604 919414681
    0x6120213230414070e010c031404032001020a081801030b10030e070f080706051812060403090e010b0708030a1b0c15060303082701090c0905090a0b220204050c03 71
    0x92205d440743c1000125101d1b14103045c49050400700e54010058403541d10fa41e2480c0c44021030080d1458400c80160814031104558000310380105050b4002042c103140c28019903d049051060364505418582c1d141406001d0342c888445003080503026403000a0220650001246444207e40c010301c184440d288080c0720122012641d581190210b0600c5ca40b10b050f43c0c0380319405180882c00d2981c0000c0c054407003260140c0c2c00145c00340618020b844030b00502c0d4442e594000000000d008103184110b0401c29800002c4602c00110b43c007000561000421012900024000d0314070140e011000a4481c4102010b11000d0707038402400041800d802c110320387c07031030b54003034100e4400808070000320711904149049802d50b10412080039511074000c2008002915103444c4589550083c5121580740c00c00042000500181a640b0640c002c40c00310880c4d5190010811465964564076001c091400440c1c4016111030003084c0c000c400c01c140b12916460100100000c10b00305411110000c540301c2100161034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 919417104 1250 919415854 919415867
    0x1a0c04140306190f090b420108070c0212010501053f0a05030a031508010b1f0c0b1303030c081b0307030e0f1b0402040612021323041407 60
    0x3c04428102041840506450000a0001c05409031600030700900700450000710482d0544600903541e0211204800d425901c4105500c04024140410300707040304100303030740c01400038079485245031408012001d4198081100c12422200c614103581d15200140950328241c8010401c0c80e004540140482d08121401d2420050600710600309110041304841c00b0300d414045803a9007508039045070b80d5590242d50003801032103203000704103510701c15500210300c025040c020b803170754408014002c2c40107140d2411450310700c009580420b03044c42000807006000850f101d8122384111441200090004818107015060ba038403e1402020041c25104100c0d80d401c145a400c140e8078805400d46440e699200e40640c020f0a04512040180c451042d04d6602c00100040c003100380b14440d030a2203410b94125050109902035402200c0c0490b0403060950fa1416150340940105071002c0c960a420329524441526a4914000c0f1802040c0500350300403240e003003c0c0180152030042c042241d0f85c9241064004055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 919418354 1250 919417104 919417141
    0x503060a09030e040b03012405010806010509030d181806032603011202031e01200c120705011d161d0403080402010905090106050901020709271a0c04140306 69
    0x940d94135114445c0d29102503101416076080381c5500c00301d4a4005070300750a070800303070f10406001030a2072001402a5209100765204e04001500401401440d080c0c182c8401c120f911b202c20f4035002128000031100c00700186010f01c48a0b520b40041c00c0d60031420410401f16201c0c08041c007c03d03800d849000ca11005038101ca046802c0207614040340c805500c0002d0505580303c0c850320b0002d242080c00c10800c81d065106a2003100060007019510301712021004040c010410b1007003050f00089000f480d0503040d1001003404070300c544000280401c540c3c60290402c5021610085254044802d0884240170f1000582c00f61980040d40c420307100d030440c81c4c0d41c1280d6000b40014100170f1080b001c9811a401180c204002c0c00005003280e00a60310f03000014030036002240458014818040001a01c0740c607441032004181107804d901040e16114018401c002104100c102c9084906400c4010030401101c42180105510121036039200c0c604900e43c440c0b6900e00300081e110350015014002c00d080341290103030b003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 919419604 1250 919418354 919418359
    0x1605060c0a05190201060f03121e0207051e030307030512011212050f0c010617010c18031113060f050a051801140a03060f1d07080d05071e0c0503060a09030e 69
    0x140325003c030342240980749982c003c2035681080c05001c0704110191418081d0403029039940d0b0007080e409201030290004803414040903070805030090113181001103001c0e03010350000d481c03000e0004ea44400310349582d00410044d00018400b10304000c207817949030384182c0104198602084200340c59110401c40c0e81e26a0003041c1070110000354900c0c014568000d4480300c0e9419030003086240d40d18820640e5001d000c1c6560b083c0d5500e0580d0199150303010b04c0c2820603035040203514075402400c640d82c48848050035401c00354003178003083c0d12400d440010f002d00405481006c070141d920f0303450701c01406001c41d144d4000a104085202d40500001510110241140c441a007a801281070346000b2900038011600013408140c2403240c0310f84040003d8005a0400c421000114041450182500e496104a004003420347d0440d42104045030304c2035024008160198000350300b208081c1c10141181d2055150803201086180010812468140540780e84096400d01c280100760480e98014002081003500c45e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 919420854 1250 919419604 919419637
    0x31e032206091e030f1101090b040308030c030916140a0e041208060a09020d270803010605090303090a08150f0c0729040b04060507090e0601030203070309081605060c0a05 75
    0x1040f40009a4076100640d0000403554400f00b55041c0b020340704511042140c007091912000040c44c1e060001210700312900001404d0540d00d40d140e03030351403560000d04001514851422070345608042c1c812601c0040c09200100035544a0000c10704c52038000543c0004c0b0301001070010080410a50100081c2c2c0d481c1a260060f890380e1074800260200b800e40e0040c0900d00c1c4042010100805c1d1540700d060800c0d140029440302ca030401c500c2d0003166001c0d4000810225061004000d0300d0b0281c000740c10701c144002d0a072810801c103c400728607080b415078015a6250320032032010070342003050280705400c039204980a030140e21305445d400d4070900c160710008005c0da0b8402029451110118401007034154480040c0c4d0305828541409100148280d500703507506841d0101003901640a0500001118412a0303a4459607a032400150700a40000349410140341e10b4904840c0041d045100800c01d40010343d41070760300883c0d182011894188000c0c400400480200108001140c2080503603080000640045 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 919422104 1250 919420854 919420889
    0x61203030b0117070c150c02070501202806050a020a18050a061803140606031005040b0c0d0e010e1c11060402150d0c1205092a031e03220609 62
    0x1802a02c0c00040b18801f07207403115044880f503021407810115542642c803000620345130242e41320103008040030620690b11a601c96005001c5411400c0348500c10111003920200890b02c2e8142611300c00c6406000c101d03400a04954505e030090464552400c208282900c0d060a00340854441441c0b4022602403210a404160321000d824150030061584889000c695481e101c101580d80d0f48152080340c840d0007011000120700c0f24a02c80c55120721f810180121694884140c40c2815511030b41640388121386520b54080f654000b400307801e0030807003c1801003401d81d4141d03900c500058a00080e040c1002910403003000d250500003402ca130001c4c0c044805081544000c0d034100b50606c104e005c2e422920381081c10040056421500801520304959000e00040ea0790006c51a2120b54609000c0c84103035046650000c03040040045200d4401e019084480c84006e101b0540d80600c211120203425900c0020442000000700c410303001c200345a040c40b2440300b07051074005084c010181c002c11402079622141d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 919423354 1250 919422104 919422113
    0x13060e010b031e06280f0e0a030f031b050714030705120d050115020a0f03020708100209030d02030a0804032f0607090807050f1909061203030b0117070c 67
    0x10004107500101250424036030503501144010309030422000c00c0c000e440c0061844a111111081c914010421a0307550140e80607210000300811004032034115662111009560310410011811038069151061007500c130900c010300382e440f640b1800940c0e1072941e00c0d10782e0854010341601e2203e0b40c440380c040204041d0b00c0c02a031842c01001405000d43c401c01e01ca001200c4045001010340054510f0306006980c2c0302c143c4113145940302c00c2d5450042c1d0003080e003403011407030030882120040d209205481d1040e41c0c80c0701c85851300d400c3c80d40c2c8000f0076034002000c070402e240030002840d10560300d00165007003004c08500076090000040c00501800b07002c00c0100a00003144c0e9a0500788480091900a40034080c0303a420b50700c5d20122804d8010403d03000d4003040c0c04800144e103c0031601c000b800c41034000b0b01c040a00032444130b519081c0000350020380000c54460214003a0b00060328030308240f4100041c860600800f41d813490003006040c8480c1803056584051044078066001c1c00504007030304980c801e07180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 919424460 1106 919423354 919423361
    0x606030d140306041e0b0a0e0f061203040503031b01050603071401030c030209040e011b080c1b030d050c03070311030621250906060813060e01 63
    0x260050107501900115030000340904040f400c0c540440400b15065090104840070a485020040b45400c1c14458400244107071a0241c038a8144080d8030001c0d2140034088030700071882164203a0a20908008580051034083e0441e50744401000c00d030000600540089291035091030081050307071800140900c00d643d11900d10139080c2480c1c60066000b00390026007007090540902c48107000342d59030304c9000c4040c1543e800116101280f5041102c0e0400700081c450305100d043d0040c882e0b54101002039980034400c1003110780002a04c441e64614500601e4500705440341800b0411801000d00000b86001e0038030b58800348499401d80d003600c041c07030008480781900004c0061103110001c1401240101d07003490b20f816140168041205280e6540040c21803a1202050030700811501419114000080c401c0c0d1400408900309801d5500740030384074000140030242c03035400c2410140301c20341c0b = true := by decide +kernel

theorem cover : BRFrame.Cov 919244604 919424460 := by
  have h0 := BRFrame.cov_init 919244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 919244604 ≤ n) (h2 : n < 919424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
