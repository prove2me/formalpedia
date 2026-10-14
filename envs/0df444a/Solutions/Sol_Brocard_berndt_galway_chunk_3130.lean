-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3130
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:02.956109+00:00
-- url     : https://prove2.me/submissions/d4efebb6-01aa-4750-a03f-95d82bb44332

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 562769784 ≤ n < 562949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 562771034 1250 562769784 562769807
    0x9050405090d020d0e010c050a080726030c0a05160b060a0801020c0c1923091e16051318060f240c0c0603020705060c03190e120307 58
    0x140d0820001a050680100364020180c50320780040500101a0100340e0380e89001950680c10000c0b952641e001141007007000354111805407841a40d0703140d03a8100802100ca407100d4911469004600c03d80b554542c000880e076020b4041c0c00c01a85078100f00744200e40603c01d1007030901c1588101c000e4030043c050880c8000c1e011341d0f0100d40da4000079039502c400390300340e000e107000d0605c3c1c6400500b10340c0020300b0002039000c400f4400301e4103004650745030211402500a5041c11034501000c000b0b000b01c550a000190503040706481d507901c120700c02806a000f41c01341c0002c0181102c0c400051f024001c0c0345c01982075802502c0e082e112540141c0d1240c0251034840881c1100314829030030084009028034081c802502510305d03007a00340310b100701d400d03841d00501c43c50310141c0c02c20014545000804200d4407601035000e000d9681c1e003d640c542d02402c0482c9000d802a160800a94040051100509412110398400002c100022448560060806080203132030301e2880c3c0c0c20302001003004080ca5014001003503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 562772284 1250 562771034 562771039
    0x80706060806090105090c102d050a0201050129130801050108010c12270f060510050f03070501020309010e0402070c3317040519030504141e0409140d0905 68
    0x40d6603104016589001d203170b50f07060708041680c1455142380d11515104072110042600081c01501182c030071003107031203d031450400041d0b01040c198400c55080c0109401082040c1900071941884900095601e21040d403900304a100001c4810b60410102c000c48028240240200450f40c0c2d80c4480764040d0501c1c1880800203500b203070f00144220050700c00d160364010701306000e50303940e40c400c9010b440307101403440e00f07951024109480b100021143e0068030300c6107461810148100e49480d050245c20b91401d40c0301403090b08820010300040e41c3c00000d691404c2d20901e05944140c6140b80850000e1103000d0303004e040000c4400740071800c81080d152484481d55880d603000d4407000d000400b01c600810701c10070742c00014011000041008080c0c1203aa0304039010f5030a844c500c00040c202010031102815044010820110b003c100032074a40001031310191096801e10791401c0c6042c0e80340703900710305000300b0307072085030307110b042c030090102140d65545030040020443d08031a068180c003074200202481001e2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 562773534 1250 562772284 562772291
    0x10207051c112e0e1e1e0615010c050307030c122c01030b090408070c0b0301080d0302072a0312031802040e0309030706030f0f092f1c170a020709090807060608060901 73
    0x501383c24105469004e4941b900010b03000c151107003008402d0348036003020a24100095100940c2c00700350180000c0c1045403003034842004200062800304a0059800312500a200c1e00c421440c0c40e007803090340b098480d025150b60031080d10b00408016002080050b8000380c01c051a0010441048030090041c64510b001e2a4400030b034540c2c0780c112118500c006d0007803244d103810016403084854041d40142c45160b104004140b40c1000b07500c0285504081408140a1786022950400920075600e2544004009030300c1c05002281d50451100c08082110384001c1c0100c0e621001c02c154003800380260b620800c00242a50313139050350307090300274040c0480314514000686401210b24450400e44990326415910951001e280304240200300c6103040d1100c08544408012410b48020356640088068581c00c4084140d45041040c01c240c2010540c4a004241808007044980d078801e400041d035004890b0313946400b00344416a444d01e04014003445e1001080c0a0501201188910300400e41e01e200b64003540c001c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 562774784 1250 562773534 562773553
    0x60a0506040905150c0f0705100e2d100e030a020d03050f0f0a151e090c091a040f06090e060a26010207051c112e0e1e 52
    0x2108031502144000c0c4140e2000010004e604546038042e58816001000a81002508085415140e000e44011601d41c0c000408815080d101882044400e078800d0f4010400052001d40d03168038500c22248465500745240f0714014a820304100413503118000103014010341c244031810b25565000641c1c0100940104440710055511038407c80b03102e02c2c12034140004d152203c1010000c40400500b10808464032078610800444200410000030400c103504040301243c0c006030b240701c41200750441c01c880c9040c400190b0449920400b1402907031070b4526000584641c00d044c1e010144682e42c0f2602e55480e1000000540a03084144c110072207068000c03901c090354442c020020610b1070703409031402c1c0000c6a084001c8141c00c558960b4800110340c0f00042c039090090f120706280c100300560520761000311046500c0d0362070307108409188403d0f82000802f4415500302000429404100103615500c040c1c00118000c84401d4110140c42d41100c1c043c3c0b248982d66061420b640d9034503030f60000d141c1c400d44210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 562776034 1250 562774784 562774789
    0x20303160b2e0b030a09060606023009120a050f0c0109090c0f03110c12031506040b030a1503020909060420030a02040b03031b01022709150312040305060a0506 70
    0x6201e0364410340001070706982c00e03c1d099094542001d03111400c01d50740e40b84144001080c3c0d101e101c0103040b0a4000b0310541005002d00c10a0a00802c40f02c0f03640403000010010b0a607011054400ca07001c00c40d2608400d484900c50b991901003c07010103019403162482203066030402207203000d070800080c2c0c1c13115115030f00c80044506803211440580c4c006002001004140c1c0d2003948100b0007503140c1c048003442d00342c003005480c0c500400c00034502103403580041403040917402e10003010150074056a40e03a042520341414030105000091074184040d071204440d51281135200340c481c0c003969008241c012207007407004032a9690b100840301116081c0c07515284070000350700000a0380c13032910f0060040c14101116428040a070852207040b03905441b050111740e1003402c1c40101c3d0340540c200342c0001621862034a45010000740444030040f03981d034880c4d9420503d07495191409a220130741c0a2031003408017400001c00c0c0f81150342c3d4000301082c240444c0100400c0408200d10340034490320341051000d0f44500c800c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 562777284 1250 562776034 562776091
    0x4030e060909071206090c050414040e060403080606070f0506040c06030e07051201020d060b130e1b180310090c051804170f07060603020316150c020303160b 69
    0x60307a5403052114000400d8a40b04241c0e110000c2071060010801c10350b1004103206076031580580c0300c003044011a0500410a0310818003003070240c100c40510062143c20021525000c0140002d000c1003c80710014125854150441c0c140c1d42e03000f20101282c07469420400c0c1c441d0001d540448480181d0783c0001261480f030701460482c0311403803001d0440246840d0400450b40481e4180316140c0d502800f000d405411781d480380300018610310140c9580c0b51501c2000903c0c042841e08690558801c900a0000132850300c01c079129011420384070030741e540800603810312044486407041641032240d8410314030503407a6900302061151141d0707050300096880742c00b00702c010600024040e421068a40001740030503402c914a10030101a100720620b00f181c0b48400b815180c0c0303c00c0301030394103603218201041142030070003899103801d407104480e034506420300105141c4c040403c1249002c0203030302400b100a40d0b03828000c0b6282d0940e5a552075484100c00c0c600601c0105c4200ca25840304064842e14882e0003c3c00c80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 562778534 1250 562777284 562777297
    0x302010e0a180b040e1504120306080303040204020901031503110a17060c0304021503092803140a200703050c09150108070c06051008010606090e1515030f04030e06 72
    0x10b029140c140002000200900c1c0c1c0340303602540943c4540b828142e844090050a8090400762030b02c20092415081c401342d940b8500c258841018034106c001c200c039a40c00310540f038105034101e81c0960703a24002001200034117010a0107001c900200c510000402c28902c03030a0b01d0002c1e096440b02d500350f80c4da04220850650b184502c00080c0c10a100091b08170f00e03032034003c6a025200400500341c10405100d5018150021140c0d0032160f17004950450b840340d11004400d52040132042840603d41d407640d40182002d050209007a401e210101c1c58030006405852001e824041d80c42400442c1c0700d1481d425a0f031030303809200c1070f01e481c00707280700b0594142042402c103840381a1050207010108418001140e402c1c00c0240090104501d4141c07801c0007410b1401854001c00750081041000350400340b01508480340b55201d40248140316400f003050f41002c0f000c0942c80721208004407854810386011903220546080c0701a100c06000042001c05680518903a024074081d070759200640c0500400c1c0300c0e0b031f4840c0c0f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 562779784 1250 562778534 562778549
    0x31902010c031a120712080c010501140f0d0302031b010b090906010303140d1b030e070b1c051003291b0706051509010f03031e090b1b06100302010e0a 66
    0x101e060b002c1ca00304441e242e9a52502c83c011545c0c0e2039034500058418a24022040700d80600015200b00071100074040e4a000d401c5a0030310000310301d003030b02c00102e0942c02200c905000d0901d020003035051600034402e84103200c1d48110300e02500310030010418000d00b100300c0c41522a01441000c01e0001ca80056128140c95142c4c94100c140e80c1803100c404150307005010904800750311140c2e04a800d85042e454102d00d41000d45012a80a80310b904550414805401c075001c10300e42440996141c0e65007958003200d15004007800500fa407a00040303444900d46540000d007504180008031010307500340110700500c030140407811840c541c492503000070304251035680300243c80205201020100340e0580c0000d0304035000d04948403a9504140200b122550f00345d1080560780c824490400030f054004690790780c4c03581480b20848220304800809810a50310b8010b1880c0e403080490000d00094401c0800c8658403141d00454950380703005c46840100049500040740083c0030101d100c0b44c00c1c01e009001d142514101c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 562781034 1250 562779784 562779821
    0xf100c020c01120929130b0a020c01110f12090105010503420105180f1602150c1b030909011e0e0103060501030b060d32031902010c03 59
    0x1c400044a503050034072092043e669039504054001040310f10100d241c000522150200c0c142443d0280507512801880d00801280c3e81403060001440d11200c103a000a40550058807070045850b110300425650080300d516910000b8866801000c0c000604005030300a000145255101c820450076141c0a03c00c140d0541d21a17840030615516107041d1180c0803401400352482000100d0b101001c0280c1120b28504450101006200a0410050300c0207030700ba01d15581c0996040c81c080d0603c46030001400c035941107030603400d2010b5142c400d0000f4000040702e03000c4040361303007002c0e886018990b102c00031340704456000c00c00300709003810048180ca204a000414400c000d03868020700c4141449110f4041d401d4035852400400c114031806100c60185005510001e020344c150b2074803138022031001c1c1c0154810085e4500302000501402e848a48203400c039030752000010320302803140040241e05091102e450201081c800741c1240c0801403003e40c02c17002d0b8024007004042071820b40440d08400082d0b08107810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 562782284 1250 562781034 562781053
    0x70605090907031404061b0f0e060901030b0306040308010f05090705071101020712050106090c0306030215280206101a040b0702130603030f03200a0c11040e0f100c02 73
    0x100aa01d031a8010054140402c0503055080302c414000021142103410660300e07803200018529100720108004c0060134080c003e0255000e02900040c0d49004903031250303000040082085c0d201360451505140040c0484889041918000d0f00150b07003401692000d4040c200001a1840c12005032409900503071100e0786441c2e1036807101c10f60120b000740c1e507a041d442150030002e83c0507201c1c80841816400f56000003142801e1050310425600c01d51042030030981000000d1002d681da101c147c1080c503009007030107551100344200601c00180710011100c12038a43c008660790582c0c02046807485813005107007030300b0920b84071882c501107001c0602c109052032105120901108900d0001044080c1c001880405075400118103541940e01c0c58001b1800034040da603a404905030140104420304866501d40444443c980c080c0c20001c0c066088100c0420850740030002c00c0c0050340800701c007a020040d01c180308603030400f9580b55880e0903d1034101401e100b113a04103110900c941c03050040381ea84503030141c8034018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 562783534 1250 562782284 562782289
    0x1080d020a111e090106050d0f020301051c0c0902070803010e0601080f0714070807060c090909020105090d0f0213020912010501031106071406010906170105060a030b100918050f07060509 82
    0x43ca66082d55082c001c0c8201c40c2070706591134503000c40c02069580d49280e542c0080712400c0c0251013850860b003040e24014801441266075070241328070040455184150841c105040036426516141d0152042c4c510016401052051000085058402e0440300000703030f0f01c0d050011030350300078101d548211200441c400300301e8840c8078991406106600400c402d060144a032207604165001d10300440380701d0303503410458504541000d0030707800400e19804104440805900040c015202d500c00c801d100303820403490501080fa468018000030f6402070409107461880c001e13020000d5001143c8184111428418013000c2030050150605172a4450800035000310000184021a00416006c881c0104c458400d82c551101c1002054003c00010801140302440c240c0c804010140350310045000da41000304101c0192681c0030b5080c200c076400101d0a100c2d50300e982207501110025003002e42280c0c10264180c45400b5281540b0700914056416184141c12034003290b996001e113441202d01044040c03080d0040b61 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 562784784 1250 562783534 562783549
    0xd0c0206040231150f0e0f041106072103050a06210201050f03090a0c0b04060f0c02030c15180d0b04030e040b0405041209090c0917032101080d020a11 66
    0x2900e9460409810041c607070f00d2038050303490103148002c400113208001c001c2e22005e6100c210090a84440e129194240f030040400c41c41c01c01403001d0f00c40722402c06030284945402c0c084949454001003000f80c25101402044015580c411052000a0030100420301c0c81074184104012900a80382d85aa00f004a90000076102c01e00c0d030040e418020240300a42c08589400c00851040c24000080d1410324424640384140e0b805540215101e050180814002240c2010400c0c440719090b04000542c0d015503c006864001c49495460b0480004131130104480d400340041c04500000031622900001e5080500038109100714000d0400c000941c0031402007406903070000c6c481800504040b407203141e1040803801b42d4409880840d038070260a19406c105a0b8009400c41c06032080b02010b0101c610416030040010750306014170b914012040643e0a00c80c8002c000301c1300001c404404c001c10900c0b5491090064000074450030001d40074480c5030421980c0302213203001c191035000b00113000d480018400d0181c113 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 562786034 1250 562784784 562784839
    0x10050114040332030901200f0102180f030a1e0606030218041a0601090b0a09090e1c0f0801030b06180c0903010c080408031b0d020c030d0c02060402 65
    0x210070400800858140103003040c9000c40b180c80e265901100150b0310500c8a44503d032088260001c3c040041c25a034000303400307072000c1442010360308940301d014042410046c0380a00d0000e1588001401c0050f80c1c04680c0d160386250040f5000f025140d40c80060513261040b0b07010040910466600c0c2621000c5806c03591868039003e8000090401c1d01d0760302155421148410303030030080c5403c00404c020003172110001c14561024a40d00c2219051510018006012a01070303044024008030301400d40341d1007114060000d01c40300d9414401001242903045c3c84100841354210b4418216004001c214064440c100019140d541d03080718682c1b954441807503814002c5d29803541b04031445414102c000d00c40b80098000c680032a02a659a000c10303080508641d03012840d40c01380506102008007080c1385406407075006000300d094564880444900700e5641c4074002c00c50b40581d00c08107258a5552000000e00000c91941c50304000c02041100142d0380c2d8081114020750285103408429241c03440c182c1950325 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 562787284 1250 562786034 562786067
    0xc06180d0e09010911070515060901050d050709110708130806010b2106061b011401120f021c020a0e040203011518090305130b03150405090303130c050a06110f06100501 74
    0x43c06d016590f260308101d000346d01e020300103000d00e051004a01e0308000c0345005003c221740c10034446d221950b50649a4400d0f00c81c140401d5a14180c0f1014183c0e00030894003c5a0701900c1e0550300d1240c2c06ca0083d86210a00404020f8441c600010490380200c00491307030403410030b2804510071108412546000d41001340300ca500305c502401403100301042c546e0701c403000030a01800442e501d040e01c5800c0e00b405a0507030040402129038100e900214800c40c1a20461a40548262403543c68030007100c04011014100250081c55000c800030340c446060301702d9070083d4401c80c003d210001c2d0101c0300002d46c00c11400380700840c04070240a041240d07210b81c806500d552007406e069040001d02c2c0400f01e404985a80401070742200001002070202030f03142c40c0c040a92007190200500e0800962199032404001d080313250044003204520180038a011070b05004210003041201015114100107200f9139041c03042814a201c1c800346d150030f501012861611944480c2c0d51048100e107003000441e11079403d0300701340d0b2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 562788534 1250 562787284 562787287
    0x70c110d06050a02190f1710080601060221041a0a12020f0d230420061903050a0603080a1206080a0c030201082412030c06180d0e09010911 61
    0x200001c0060150310301c600720071200141c450301c000030310709013040c0e0b001d46480410903003201d06c40740b541c0c10005482c8241184608140070780e490780d181080b841e0180d0022040b500c41d410001603400c0d40000d80c1c02d400c00d520004040100f01c65030140c80140500d0044000700401058526131480e42c0001a00c604039085c60510100c0150b1405101242d00c01151002300c1d8a00040784484003c41e4014400110304c0110f4900c88180c01d0803048425090261009000d21564004401c3d9404024102186031100030300c42c0350344041e41c10b2840000c02d03100b1030703083c0030038140b10000d9505000d611801703080360b40180318140b030314440381422244210403107568910107a07078401c041084042040034051640c8181c03000c0500c0d41c218000542841001000820b421000b2281403620007481800c12400080a83c1c43e01a900880c00000d42140612030303204945204800c1007200242003903041c840e20111282c26589185030100c0708654803402d0b43c040a80140c00e16004000c8010300b9445507004056004a09 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 562789784 1250 562788534 562788559
    0xc031b0a0b07030507020c0102030301030c0b0c0a060f020406030506030c0f101101090b091e100c0306030501020d090213060324090b0403210b0330070812090105070c11 74
    0x1003a01103400c2e900180001d542d2402c104076079404200c1c1c414005001d0000713600315031466441740d0a500c41c034000d4000960001c16100a075005c10000251101c0d131084051083c0603c4a100308000e4020380300741030001e410301000c6541800e02080c80711901034040c09803050040315200740802e00c020480c0007000c02103c1206a400ca8101384902c0c0d0307040307220f003254a1150400788401454040f04001c8100c06100101a54040100005031200c59904041d80441c40b02c914100c103600400083e88040d006500011380442c488115902c01110148210f0300641c4403010f044550044444a010042042d00c0c8010b80c1349144030441c4500c4d100008641c0c0114101e40d4917030314050b920009490440200344210141a40d0384070208401004040c0003400f08100d00314100003d64035182059450b000c520311049003c903030380d0480d1305845100b02c1c0c00381803507580700070f4500034a06030300140c1c003180c8564104004c41e1000e0018010140111107956602103a103119484d8091801c007242c20783e5504c220f411201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 562791034 1250 562789784 562789793
    0x18040b060d020c071406090a030b090a082a0c010c06020d2003090c030a1110030608060c0a0201050108061b0a12140f060a15050d090609110a0603020c031b0a 69
    0x40c0341150f8490040c0091500d82201134404200e072006031340c810441032201446070f4640107189021682c2110b402c0750310ba1143c00005051140710003000d4409000007940c0502c504803410349182c5c2031902000c01149604011000342c4800c1c904000b140007a000418420100304590046c1a410440382800a19018075042000752041e0341091080740c501c002c010410145005d010785410300c50254007400801280b0350b11300c144040d80c032000e14440d44c5804641d440c40ca200380e02200c007800d400f0040b60701c14101442101150340040802d440190300344030002c02c61190100d21035000e0341c8010909800c1340c1d264002c106454101103030001c100080440304c0442002d040c0100d1400c0750380c00000f460781d0f003040e040904000c6401808140200d016070004c002e95445410309034486840740c580b058449494100c124050000f0034005031041d03081203a410b080c03207098050064440b1086504d0b400280e52400240c0c01d0f80a507206c0008503070801e02c01e10200300740c520f680034100b4032140152031408210ba0745 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 562792284 1250 562791034 562791037
    0x40b16021f05060a090902010e04091a18010c1e140f07030c0b0a091713170d08070c0302030a03181e0302071d0a0b01050705102018040b060d02 63
    0x10011590360b210018004941132001c40c000c094261031800303220080c0c068001818401001c03000c14041d507501c0b588034040c406035000182542d401ca003103030022424a907403450145016a120040c80c0c2d440c3c003045107075a038001c01d0311a03903042c558803181203402e201060540301c001010008454000d0100010501e81c90702d4402055081c0c030a40303840110860710f0510300c1e0070020082c80025210b240405040115158108051040e20303081b541c640c0c1ca41442d540c1c01c0a40002e54480d00c09501c50150442c490200407070002e425060b16031f40c2c0481c95035555422200303140c0382000503015801c208110b25803c0e00c0ba40000303113401c0192101e50002a6560703508003804000314240000c006011180004065051000314000d10949040c1100e88000800d810000c01d4003625200300944c1d81c68280070300c0d0b4002c1003514401a00700080e902d006c0031340c68000000e00f03007a01a94080b03003107a81c00680c29101c04801e0b01d004074400c5c5201c00e103401e11176050200070182d04075481e80c041c1082c8141c1e41525950300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 562793534 1250 562792284 562792333
    0x9040206130605040f06050a200c0d0f02040c3b100203090306060a050112050603011413030f1b08090d0503040b04050415030b0c0d020d0c030c110105040b1602 70
    0x10783c2c050740ca0740703003411640390203d0075002102002410400c00d400d841d40100c24080e030300860904210703400d903284101d0307107410014404c41e5048002d918550b803e0000050401c00202c1c02520306100c01d02401e001150320144000006568901e030001e0354884529056061503800b4040b421070018044c1000024210b412013014030700164000100485681018840f280e00400140e410a400500705000a0701d10030b24010b5408a940d65640050070554094101d003a102c030a010b07100c0c07103c5c02c02c0288200c454410b000f0940c080360701c1f44408441c2c00d12640d462000002c9035240008815916510320546902004400d9803015828407901d001c40c8041c8001c0004015281038290380700d10b44000d100540d0300c0c0b41c5140311030015600701040480c0179600c5c50303640001341122061355500030810f072070001e00035842c1c0e4210841c6080704402106d5090b601a840c0c204154442240f00c0000f00b0070b0320b023030302c0d0101d800518400b50f000c04218000400c50001011a01d02d0060b200441420b403203400c141807248 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 562794784 1250 562793534 562793537
    0x712020a061a18190903050412030c0b0124030e1501080607020d0206090a06020c030f12010501110a0309030308070e06180906010504080a030503180102070b01031104060311090402061306 82
    0x201d14510143c81c2a958103400c1e03508020081c000b03407401114808090009600b5044296103a40c0214201485001100c3c0901069584044c2c008818103008025031040c01c0d04a40c40c408240000c0360a0300c0c201c1d00c00c8240f10151084210011079071000318064400c0f01041c000a10410a40e444103036000b41a45004c1e0030b100300140443d10f04080300074a00070341c6200fa00e0a541140e03003403102406000c100001140e0700960096550340e81c4d403c0b001d146100f6161000f00c515000700700e5444410030b100c18141201c000343d8401079400013030191390f51540480e090080c00300700160030070070002c0d000c0c0e40000e52000890810b081103941c1d036408500d01c0d91185105c9415103582042ca0318580c07600d0b441242d0000b2081c44c106040c1810001da441d0764001903980601400310200018100c0010080d82c9040804904001d5403501043c0c03814081c03002d002e001c102c914a42500804116003094440d0344201c1c0d421050110503100004180200038901403c181d8100d401042411402c1907143c7d6010018a0b15 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 562796034 1250 562794784 562794821
    0x20d050403110106140109260a03180609050916090914011e08070e0c090406030f0b010506032716080d0f050406050d230108070609080102030c0712020a06 68
    0xa541d44a00319504ca80008002503c039244048450364401d41c00c0d0241d546201c0c074003034001d0001d1030540c0c25000c03490005c1898070480c6005030404da0700c10709400d114580313000400329440e203421017500d408015024140d00560b103800064400c2e0020300307449180340140e040045c815a01c487c600400e032680402c0d4501c0c2180424010040306002030095240020342c0481c1c609a00d050003440350300d0380700c0c52044c01251141e80300400c1410203800100c0b034031424010020800e059903071a0895211910810a6902c116034070700000c0c8604200045034450307020300c2d0416902d0803c005014030410020506143d003407044034206000202c114050001414400004020500c03900c000100b810266800311410094248070401c1100d4001c01a256148020302e001b19001d20341e440c401c02d000020b183c10140b1080d400d0000546200d020076402c00781c6000d075a6184149032200001400d0b171105a40100c0311000800a030760102d080b030000c0045a51a92059031002500d07500e4140a5030305285c01002130540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 562797284 1250 562796034 562796057
    0xa0b041404022b0e030d270507060302071a040c080f010b010e0f03031923040e0105091905160e0f0d12020a050708010501050f150702010c06020d050403 67
    0x1816011810464088600b035142000300003d01035050408041420140d0041e180404070304030903041584001c4a0b4012030341c56403440c042240c040c0120a038410320701c1c0d80011140510030b0354058000b000301d070050010201c1e2490400201c0080d80328000960700600c58034461342c1070002d04410180506c0c050344e001683d0318100299a030503c000c0e41403403c1140c0c50900340e080030380d800411922078580304403200e00700d000c01800030078114400c015120030315844044407500200d4100e0001040c00c0100f500b508690720410702d11040c6445280501003101044500401180ca00382c03030f090354000100d82c03501c0b1140e0307003c801050540b04190703016590354548400c04500213600051052142004075030fa1044039030782c000480e898490a40c800b80600c00e0b0100e901080c203000b0040d00f203440da032050840718040d5540001074020072003030141b40d01c10045200340700701610303141c100c0d04000c030701340254a45000c10070f0780151188441a4404c40e0915000c1c4501c483c0a103107407040a205030300a07100c4002c101c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 562798534 1250 562797284 562797299
    0x11d0a090903030b180a09020105070b07020d020c1c061503020604080c010206070305271c08090d0c150b04062301080c0a021203040501060e0414150f0402060703030b0a0b04 76
    0x1906031413641c0c09010f11402c92008011000032840c0c101a140f00002842902400100c40d90b00c20840c02525400b940c0b8280b120700341d400212414201c00c55400d40344080310000c20054104264071000101c15464507440300480c9880e80070b49296039500d001d05c20f4146d66640412440d40043e48440916040042140050758041c002ca60f0310001500e001c020a142c1089000b80340030700e000d40466040c8464405003540300d0100008402c0b03442c2034801c0b0908020503000140300d41d40c01c403074511b02400380411101d40c00303010740d8407819429441078040d86c503c034150b800503000f0920007403640e0307000c4d480304400110b05110031a18204880b8010450105845580015005810107010645034450402050311041d501040240740c04031008000369403500d450800c28090b0807241c0000f01d445041d10240400c000c804001c0a0764040d800064410056400c1810f041c0000c1c21070f1003102c500b0400000400518120b401000868401c1c01d0000346903c045020401240c01900010040c9400080500220 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 562799784 1250 562798534 562798541
    0x16032f03010e0c0f040b07050106090501080d021c020c0d0312052e050f06070204020c03030106080103050d08040b0c0304063309090233030a0504030806030f0c011d0a09090303 77
    0x7088010843d440d028001c3c1c0b55000601c664170905030000c8000c9441c4081010070341040d4010200a0001e01135543c45640c1c40d0345511032040000007620071b2802980c20580c0c0d4151206210b010b9030050005117500d0001e002000e4442c0000320100804902c810700d00009910440d8021002644408002002124001071300720003103560305150105243c04002a0f40c52234074500e43c1110599646071180114800310300030b809480d180c10f03028007000c000410302c1a4000c0b003560490b0700500840e50056038400c400c4c0c81095064070b0142c540c54607440081c140010403070045410a01c94240020b0f00307508aa28070000c8901a0000304540b200800c0c01a01c03036084098010103404416000c01140d0344a0b030004111016084090b14140c0240505481a8024080d03d000c0c0000c000d02480d074a1900240c0d00000781800c84041303000c038117441c000c1111801c002034045815802c00340200f00c44e0103078100640b40b4a4401c002c08900102c1460201c0d0f80ba10344450b103900510040d9070110b0208218503025081c4c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 562801034 1250 562799784 562799791
    0x60a02120c0c06010b0903191104140408030a05040f0807120831080412060c03050a05011508040c1706010906090b150a030212040812010e16032f03010e 67
    0x78060248004482d40e00003040c5507046404006545a40d000901d0201c1e0620310301c100b5001d10101402c440d1424003101c0b0581d0600858121410001c40400d000e2480d100c00c1d041d00c01402015060000541840d01c690050b40c00502640c010941465590789221485d8401c050407200c0740703440740328004240d8100c802d06410000c6504081400d60640d100000001c1c0700d4000000c0d030300010081031061001a104450241800c12b80703110101e40309003031080180400000306000280b401001500b5400c1da4410541030780c40d07411001181541d8103400302c03160040503100341c82c480341c0400c00240c840000b11901d4040da13510b002511266140070b00100888074103074840c2d07580900306a1860b60590f28405640c964254002805482e08034080046000740618080026900c202c0e00070702003400f82d140007800c1d4100c02c141ea04829030382c0f01c50025881c860190f4000101e10000b2481801086c0a03030405210210001d500c00071500104d0b4584030b40ca10780900c820b0f02028004014001c041c0c0c164210b660 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 562802284 1250 562801034 562801051
    0x41401030e010c1b020d060c3c180503160503010b0603090a1b090c030f0f0b061c0e030a171509040209071101060b09040609060f091d060a0212 63
    0xc0100643c000d0081c50790a03498051085851007500111760f20031014000e82c980041003003200b5454840d026000c50540519070b20000c070541c84140c00b40f000607804220703908440208007418138004105890703c012801c44110300400808003c01d80c0c2d00c1c1000b07908800a01031400000740740c680000c0c1030844240ca400e4900030042001000240c000c00039130b2903081d5511a41c88503401c7c00c150310050000035075400411480b82000c141440c2d43e42d1540103e21045074095082081c0d480e04020501100c068492080e0004070034804142000d041c00703c04038040611410208924440090460455101d000c6081c0070440301540b4200c9102d00500d1503a2080a54018400356903500000071001a8002c01c02031080c015400000e10784d034071985000040b03100b240000d02215850340c2c0d03038071041d4003c09209030003140b41c40000541904980200000c5900311200f151010b41040440d0b8041d084a0b01d0300c01c01c44020318115058401c08010700b5218100000340181c40e20024201c1c50b00c0d480000d0500c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 562803534 1250 562802284 562802291
    0x3180a0b01051c05030306010c050a120215010905070e04020a02150a050f09030408031204230c03010c0311090d020126010519240e0a06021e030c030f090411041401030e01 75
    0xf03000980004c101c035007044007401c1c8000c1c0840070b89400c0c1e10b4007008480042c0b00010890041e10750366000500410080001d41c0140c40a03a01d4030064807c07950308564a400052025000400074109a4000e0203540c0f164415560301580c1003290f44c641100c140c800c4510b442d520801c000404440d0390340c0d02c0c2c008030f905020750716084c030301100143d0728003606404811a126010100c0c0400ca0801c60051456038403943d01d1406410040c100341d160908507001354025400c100c803820401384244216007018a8001c21603043c050750b441488022541624120f042c045c030080c2161070100c04050f02c41c1418083c2c012548190305010a009847e03003a00c0380c4110719000c420060140c0e01e20300140c9201118100060081851030b034004480c002240e0002c04d820058903100030900c1a40480e181040d40d10f187c0b0320428140070b00603441d60324801d40c400c1d240b5a800c03d000d242c100e1100d0704010322080340018004146e032451a00c400c1e034203500c554044004590502c1c1c4050b41540c041c025205d1660a450080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 562804784 1250 562803534 562803589
    0x105010f0302060d022b1d0705010c0311032a100513080309160801020a03050117070312020f010c120e010c050313080706091b0f0f030803180a0b0105 66
    0x40d690b01510902c10601600415481c4202d01c0c1040059031b10495902400000450124000b0042440c001d0040e01640c041100c5500b40354000342c004101d8006a450401120203520101c0d0740e0801c0c008034105c50301040200007000c40c1400d00c04140c120b40901c654100c0e46904ca0410301e030105020044021900781010080b40210144000541c03e412104159495a40300030250400850420510782d0780300c3c00801250011f030560103030501101a840400403640c030307542007031000150308003030090301e0b030003001300340001100f00c9440c0c40030040c640122a10f0740c260814082c25113a0005030703000040c04075003219030070356411702070308000d0038160000700441c01044200503c03505c002000c031402030f900024000200311000701214911500064100080280c503d06540440b41030007120344910305881000c1040d0100a130300360304075040e60b0341e086400f0307107507a40e00001078200506000d410310700c034008100c0040c410701407044c06a00c00c0351200c140c0c0d070500c000c200390f10800011813144402e82d035004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 562806034 1250 562804784 562804789
    0x6121006020d0806010e040b09190b030a050c01050c030d3b07030201031508060a060905061e040b04060506070f0312020a020a0602090d14070317070f1b09020703050c0105010f0302 79
    0x5080e080142880e240b6840046d010200d005072440455007900048980e00b0031a100c1481e41c200034900341d1021050004407440e10405680707206160014026801ca182c1c03501e8690301070070080c00b48a1142040c0d0382001c1d403001803d8101c420300c2c2c40380b101040c01c21444034984950505040f480f2841d219508c0b4410740c0d9900540c1d075035116400300a040c940d49090010103001c50100c910300074030200c0111090703403a10701d042030003030401407040140c01c0d420400407031101d203401541040c08010803010306920120f600b0401015240368410307203800079a10407003c20640c4030301c0d0003424680d020308005140300c44e40e40b80c01480b07448020744040c0894410b0003403241003940801c2c0c2c4008203401c480096140c1050500059940c4043c900040981403400b41d11011510086003242c1228010070f250a400d41103500b00041910801e44010047c45094244c5c40010300400707420354031284461000f1040035103a501d210102e07404020b09a0106102191008840717109020f0680503003120b0200448241c80d540c00b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 562807284 1250 562806034 562806047
    0x40e06120f030c010e1912051c020304060b092223010203040c0614282102120907080715030b2d0a080c060c030906121006020d 56
    0x50340310380815598020202420464921980300403020b40e580e951401c80400c0c000c0440116452450203403a4100340c54840019100c80f1543c0c110780611901e00f0740d610122000d5121134070b2180440344003c00a0162122803010714441ca1043c4800183c0c035000004003c80c074040100b0300041c800020440480d44081e22000300c0300503174010b502c010f41184d5844402600805c00c60f500049610100401051140d0011032000303c030300c00c0d1100308200c020249840c00b80d00c201d000000c3c03226401e0003c0e40c03d03001e40345c04811612802c0d24000c0c180d000d4181000b81030304000c481c0f814410707401003081c0e201400341c00c1005070001801e02c002d281440c40d01c201f05403580740f41e106400c240d0061560b070904d510b000e60001c0034100c80082403081c0321031001300000d00c510011102010036241c1501c403030406041c250446800d9a251030b000b0020150007800700300140d405060f07040c00e2400148000c8507161103c0c030181242002c001c1c80102c540c98201515030300130300c4c641c0c800d20440d800003407490206508240c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 562808534 1250 562807284 562807291
    0x50c0d0e1804020a120c0305242211011101090818060306130b030f15010303030608010c170714120405010c17270f15090703030503010e04020f0a180b06040e 69
    0x10004600d4070381381e003820002e8440541c0702034964080d031440c20305040309c1a1000ca042070000c0880440546404e02c0304890440d0103200008030341103100c0d00d8000b0400101c0d002001c84070502d1311070f14240301e140004c0d00b540c04800c0215518640441c81c0d00000b05081810580004140c401c1411031030f002c0c0004204d6181e0b040783d04549582d840c0c10700d58a40b802e1050011804603e802c03154071038081c035140000507a0074801900000c0c070300b207000300d882030042c0180c091660700c0361345d055000e115046480360020320144c004024088004c89040c0041c0300300010b0030b80d801c00c404c2c0399a8030380f4160524a003540da082c07c01008012000c0d05e00440d0800c6030380e00b02c0d042504018401140101c0c051060078a031f0001d0789102c040c0c030500c070b240c241100000070140c52040d02d0201d00341c8a9144c041110390f039038621340001000f01c0d00a00c01130180000fa120003d6000d0f00041ca0243c540c0109800318241101039044140c0d070314440f44542e42602c070540940c4405000a42e0030514181c03412248200007500507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 562809784 1250 562808534 562808549
    0x607030e09090c0604060e010f0c0f03081503011e0506240703120e010f0c0e01050a0813080a17010b090a050105030405010f0c020a0203070e100b0307050c0d0e1804020a 74
    0x307001061103800100b0210710500805440590b40369144c10020341011821413500d03001480e4120f00303c0c5010b102ea1507007070040307a110341080030b8005c0b155001d0300c8414001308213040300c007245038100351182d509010390700c1850a580c0720440000782c0e01c2000d0054079801000d0a005800081902444080c0e03442c00e18109214140d82c4c03500c0d4550317440e0131205e465104518081041c00e05088500380c0106600a030000840c6038800c11407103040c4402991300301c54901ca40342c003084080c0301c6284c0b45400394280c00d070702505101403003028500c20f582d42c0915401a00b0880002032545c4642014440c00010780c178050400c0141d92400d0600040000b004418140102810083c020000c501045000d41142002068404041c0800008080d0080da107240700d02041c1d100c1d114000700010981c0712405000c0c020200155200f0b0b405007081c01c86c54452780003819030010490104030080d150030041c07110b8802613000e6a02d81540c0c0d880241000403000c0700c2c0342c01440d00c40c012801d110041e518119910110380b40c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 562811034 1250 562809784 562809799
    0x3120c2f070612060509010308090f010c02060a030b0118062c100c0302010b09010308180d080d05100314070e18150a18060b03010e06090703170f12060f0607030e 71
    0x150f40d40e0010708901d038445070300700602c00000b104000f2020040d0043e400103441d1170106280c00e0b0b00444558808540c040d400c2003041000e001c40c00d10a4000044441c3c040c105a4041d10303010340098000c29031544000002540401c0d04000b8403111400d4904015001c0a4500c80d10302d0300000888c1c60500f458042c1c01d00c00380c00140300c200b5000390044070741d68400a2500c590b40d030352400c1007101c513880050703244400c842c42041c1d1501450015606503469030014501820a40340c040c0c2c0c40010000549071101c141b020303080000008204030107105042d401040507049840c07500d00780e5602c127000607254001c05100741c0c40c030041d01e500c001209400020700b02c0743c0c418142c59030034250f0024a014002c80c034592b00c01060340028031280383c100d08080301e0305038001c02130844040242900e07540d0503104105c030b90300600703400c002080105406651000388016405e02e018102036488000340d004624200150041c04104941464810900c0403403c50544d030340c40c5032000543d0024480c0000f8441644114170 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 562812284 1250 562811034 562811057
    0x51206070815090717010b0a2c090a0212070f020d0311040f0e100b07021c05011d0a020f10091e0306090812100e01030f03120c2f0706 59
    0x100000b911400d103001d4007801e16410080001000c100c801d1010405440900000041e8143c81ca4100d402040c02e558030000700c0d0b0544821030880d81c2403c0003452561981c1300303003c01d480d6156100d60303005030404d5a0060b0342e023983c050150380c2204020b00901c10b100780c0800e1020002d401142841c2e4014162a0000340048004032401041c001e031380101c1c030f41460703c01000c15865481c06025002d62440c0c0310302c000c01c1d0b0741d4910070300480c07040030310080d007000b12084101c0d120a98841846c4100348210000300707061000400880542c05d0f10003480c03215900c000d1b24a0b0550410000740032280c5015503609070714134640a4050f150000c103100e01c2c0c924014420680d01062011650340300590f605c46814020004142001c1c041e941120105a0301d03404400c2c08203001d110150303c11003c45440c852451000c0c0c1c03964071410290500d2140545c14010400590818642e5078803480c820485952544106150180c00c02c2184050115004040020b88440710307600e80c00000b24102114824a4040304800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 562813534 1250 562812284 562812301
    0x112050414070b0a02010e0a05030f03130b0f0601031a0303161103030f040608130507090207020607061104320f01090b0a02030301090e01090c170106030206071b0512060708 76
    0x242070300100c0307038081d40d00c011034501c880d040107040e00304407603000303229902d20100696222454030703c0080669008000c1d001c001e410b6003014503404003510051092480f4262281e03850b07103c080341c2c214043c2030420100007856030140f00307000c1e040c1204413094442c01100000300c1da4a200d518210130442025166003410000709005041040c003020f02602d4403518900301d0030103181c001e4098000446c00c80c400184490b00100c01e03003c40300b80c00c24020080c035480c000c1801c00030b41c000c1d1001e0b41c1040c01080310201182e158006c00501c1c09400280c0d556a0703280107060090070300c2d12604036079009640d205d41c8004100320302000c105050704403030300d20200d44202c0c010b0f00d0142055010b200d02c10341c0801e0100100c0d4000c0b018504030340c6814003e1001080c41304d1007130308070740f00003400512602c1e50820500c141003d02c0721b0218031420310000060884c0c4c480c0c00142c559000303c00200c845071060302d0700c410040c9002d90240d00500d41501d80300812030440d007003070352151710003800300041120300e000003146d90 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 562814784 1250 562813534 562813553
    0x5010902130e060f2709030c1f0b10021f06050f0f040e060a06051011030d050403030b0a0305010501090b040c0f080604020409090b0a0e0705030a080c0c03151f0501120504 75
    0x61100400010944c025806040c4c48500300c1c486216503981c600c5c0018503454004421500034450010141a1240302c903170704103140f4800310a000030705d03941c0d50f00c1c2d90a00d501d82800c80c00d5518403e0300105040e0070800900000038844100603540f1a00b814010041511b800307101e807848a404036020f071208140140810003c201500e08202d8a209450511028014a500803400c0d40c0c0e043d241c0c0d180100c038400c0709a841d6170348240d0391002e0780d01c100240c40c50a840b690000c1e41082c420300d00814440e080b000003900710011a001590319954139001001410300c584682d019a1106680c2440007518156002e0b0020400203221424001c1103000103103a41d5450303045401500c1280c1c0e04000385491130030a4800031000311900c1c1001d0340703000710004520000207400c200301d0324010010007901c80c1b180d48440058100c142403541504c2100c601c0034243c2c1d018040e00c4000c0d008411900311615148900c940c8590b5849400c1d01c0d224840c06040c865070741c0c0030088045e0001039100c04074258440d07140c04203a2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 562816034 1250 562814784 562814809
    0xa0204021c11040303020607170f060d08031905130812040f08032701150b2101080a1a10050622140a140604351005010902130e06 57
    0x92406040c880d00c000300b5809401564060f43c2214615521803405a8000f0001540b09000b0310074580082e024080410107154016005040d8000d40d000c10b55820300b007a0019241c4010015111002104800062041c503602850702c0042c0c10505060f07032102040340c0f00f0001c0825000422500050900000c031802e542070540c0540130303c3c0d41c0c1c501451040d4a01d501e210740740c1840e03d003001e240001c0c2c2e80140500d41c5180d8203c41c0c000b450515200d0034441d42d500400d180d00c840944421411024140b1029040c020100000a05440d0f4101d20f00f6604070b080100010314000002e00a0012203250a6144400d4030426502103644052910042000502c903400300741004070340180204000040d145082c0c40088181c48100310b440d105c441c0c10100c5040c4040c3e254022209100400c402d03400b40304c00c10300c049183c0c941d0400d00c0d50340c000150740b06880e12030b00d00031a60102c0b0070410041e1091103440d00510b80350600b1820103014002d20f64003400a446907080902000011075030540d2203244a20a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 562817284 1250 562816034 562816087
    0x5090d080d09060c171501110f01050103170a050d091a070905090603070b090d03090f030812071704060e0c0613150203030c03040f05070b12040b180a020402 69
    0xc50740c9403001c8003005010b00da1000c68225081c0481c01c1052030048180251050866844603650795811070710310803840100d0030b014100202c000002c2024034051281e0303400418100004a019810740c200a40040880300f401d0607090820030502004d1b680c0a000d0b1041c21120b81000314450000d1b040001f4040c800c841c110032121000c1741070010303441e0058407a80442c3c209131000d00540c0d0316007082540b0381b601407007110b0b580b480030448200e1030300d00f8481e8900701c00d110741890a440c580300e010f00711100e00d60b500107c82960700000e8005002c46070025140e0312070100d1400c01019502452220f8215a0280004100340c1e110300302086205014000b4100c4039802030a01031b1119500d1126100f90b40241c8904600c1d451070b0801840340078030100480b44074110115074549181c9482c0c0c1e402581c10044401540d45015011010801c100d44000030106043c0d220800045400c1c00d081007051074001130850401c41c14600007100000c140400c410140c0b64040b207005841702c11588030b08000a032402103541 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 562818534 1250 562817284 562817287
    0x906060a0f0f022b0e04060f05040207140706120b040605010f0c060906022a0d050307050d060f060302070506072d020709060602012a0c0609060e010507020d17041205090d08 76
    0x4a041d02003406203c0d94075203651340c07030403005902d8080c00120f42180c0520219800108c100f0301c1982015002055003610402d070091050721200c1105041c407030290020800203034609d650150920990260b0b49506404039010041c41c1d00d444001303401c3c6c00140060805015242d04c40e041070000541c07142c00002c0d080076055568002e540c088562414607a885140c980044031070400c0c101c00300040c402c05050407034a03220f281d80c44124095619030030510104024039195071011803224084c2c4484c070000c115a480140e00c805aa18096090510062a5204002d41482d403a000b100b4020f42e001003850359008101b20580c00444200d0601c81c5540040d03006038148080020210f03415408a144114642680c0100d0146111b00c2c04800c10710711040c00015000908002c081002540148000b500c03c103c001402403074081c029003074850407a224005030b0001180100410b803c14000c015202c280e4070910883c3c40c0030ba5883e0014103c4203416003c20001003000881601c0d00018420314035044018075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 562819784 1250 562818534 562818583
    0xe0903040315020d0914070608190e0a0c080d090b12070302030c09030a0b07020d170a15030605130b0702030901021506030f030c10060e06030a0b151503060906060a0f0f02 75
    0x40d02030040c044641c0d01b58410034200050441c420307040b20340038440d0810f00303800c003000b054403010203803183c40245242d9020302249000003c40001c0c12100070f100700e001a1010400701e07400540104c04076400351030800420000a6007129105e04070710b86c0003106080050311380d00c4054280c00d59000d0300740199051702c100413103a401c0c44503e031343c194030601c082d0b821900c2290040b003040700d440108543c92941a5500c0011802d0001d040d00004048583d08409102680d500d4842c0d0b0f055880903254a04030f580c407440c202c8184441a40c086a111849000862400c0340f0800000d5607072415100c1c14400d4a8000042030240c0e905201c001101e00c0d580045070780740c2e4100d6085a4132201611140c503151032400c940044c0b40648041d080e8880d00008019182c00b9113036807140031111500601001c003000301d8400500356a591070f200c0c841e80e2051075032095200d10381101401929070003c1c0031580f0804082c032400055540c4240806405009403038010100071002109a10344200040c0d59a8100310180c0074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 562821034 1250 562819784 562819793
    0x507030b1915091a0a030920011e14030a0603060c02061e01050108060d0606082d0a021f052b14240a0504060f060206010e0903040315020d09 62
    0x50a03034909216200780c10800c010140c0e007101c1030b8404c03007929074818000d00140041103c00b50a40440f641800301300003100d5550351042c84255100e00e990041c00d0450301900d540d00c8210000b01c0d030000080246030300e49109010388620030103911503001c108000000341200c0e800707400410066500c62810310102c030b20400065100d0001b2500c101078120ba816a00d50790700004c1d2000c1c0d040300c0041e101c090380c0d40c5070041401284415030754207550864550b803002540f1001040b40d144909000290904100c1d90b5600c000003071202041078410591045030742c840540d03144d001c0d4115808151002034201c0041d12003c0d5128041c00300710312072914140c000d0701814594a44e0b40d00c05040c40410420210000ba20103480d83c100075100c204200802c02003080280880004003100e07444000c109c094016030300d40000d010b68242d6000021440400041003010b6038040103214050606401058628a0300905117550307805188405000d81d00310502540b411202075048030001d00450038213200b000040d050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 562822284 1250 562821034 562821079
    0x120301030201081518040201051b160915061b05120304020f030628090b041a0907030302030a050d09081b0606010f0e0d14030301230f0d02040507030b 66
    0xe82c041a0302000260010894510f0070b140b0200c010300e90011284890845440c4c100000e0040b41800010404036990450b1142000090340c9428010240306012800034200c0e160a9408042d101c0d0901c0302c29440014911b0204041d500d0500e0081820910003d42c0000074201071000340c41c9005514481000f0302c015401103100300c0c02070b11101603007203141c1d085c1030782c4001c00c60b005c040600c02450520301a540c0030200c000400300410020030048150b40f41e41d05006404c6d50708444501d0046d5955855012800307041c1d51000020015040071441c585000e0b44a1059204010802000007003d800400150340051a2550440074550312800c1414941d41c015622000b009441e2146800140c925803084100c41c0c07019040390744014508032907800744419030806040c2210076036100300d81c5159085007000074600070403403a9008851009008460801400c013040940c1c02490300f8a0410110745403041c01c88542d96040c0c500180641c0e0f640002c0f8010700343c02c803440d80d222203402240c2116402010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 562823534 1250 562822284 562822289
    0x3050f040e010f0f06051c230405060108070b0a080a0f06030f0b0105090c07140102070203190b06090402062d220f21080c06042a030b011202030f120301 67
    0x2210200f0880d107a6101c40e0300d11005100b04000190204a5480d101101002507140380340d1048000c11400080304e501c0300b03400f58410711902c481071404100402d119042080900505070a00603024a908041d4050a00d101e50703031403601409100310119104180c1e0398010100311250b00c2d0308004a54403458080d002c0b0620b40026a1200020b030b0000c900c03031801c0b00080c1c0c007841d00052114605441c0d03589880c0b0182690100310501e550900040015880c02e00c150303070303000c4c0000c445000b0301151860004d640c0000948118018140c02c001c0100607280c03001110410405030040101c0da501c042c0c02000c10002c0300c2e8110007844000324110805111107040a0f80d00c1041000340001e041d140d1904510502092140525030031482c43d0110014182c0f107500340c0b40c5409101380d42c0c50400c0b418419840d00f031098034101d6000d4821a02c200310010742907080c81140010b00351107040e580c03464455452545060080b50400341c0c0c1640d0440440d0384c20040030503112003010a4504c0140300d6004041c080d0404d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 562824784 1250 562823534 562823549
    0x90c04080106030b060414070509040e100609020415020c01021207061803030f18020a030803190e06060406050d021f0e09161103070321180f021203121303050f040e01 73
    0xc80d0003854600311001f00c61141a25555460504001c00100710141074621402c2a207806000405c2c0511401e40c01030320081c151080025035a14504207100e80302d00d40420a080440d0007800c0d150501e41e1380415400c4070a41c030440e01c83d403501c1e030700c0c02c02100815420383d00b80742200038014517034101605a04100e04104004800b0000c1c0300d0348201c194050600312800951049444200b440061410300c040d6401054075070081c0f40c1c98545149140880300720381222409a440b210800500d45060f0050202a050a694010b07120550354080351a29044001c00000c1401c9a8107104000344240c06101c1c41c0740c0010400e6405040c058029061001c9564549000924074120110352040c008200c4252961507507501f0180e550503103070b810700241d542c04184056a1200484d64020303541c8080c0d80c2c0311500031724540003c5c4804d40304000c410211584e01481681089c4090000c2245500380640e112010b10f40440c2210002d00c3c04444511808407091410600071501165075003000840e941a0340c0030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 562826034 1250 562824784 562824791
    0x3040218070f091e1502010e060112060612032c041a1f091a07020a08030307030c08060a030f050a02061b0708030f0409230c090a0f05010509090c04080106030b0604 72
    0x2184604e01402c1d08058a03c010301c407590204100c440c07010160a54591501d100004040b0030307032600e0504165080e406210030b81140144003060100610510000708081890922045066075000d805017010000408005030503402c4914a031000c400c1c0c00e070142c01c0050080241c980e0741c060813680208101011130041c0340c100c80581081c0d0041001e0340801030700ba145c0c0868140b629001c811070312032040602c141004203225400040e200c480458002d040d8000185403a4039080302c00408a4002d04880800c00c800311040c44186d0b1076201180701542e801c1030003d200101e440c107089240c151660002504001c0000340c118a0f0000481c5e0408811944000d03a041e9035600c090690792401600940304594100700410041060b40f03901c8000c640320a00040003030103071200b494118a9104a1740301c0348624002030040100e00e401c0503886c001d001d95005070b050076818100000c0c02ca000d48440503000c1c2e101200401c4100310064191401010142c009010300790301d0389042c0c0e890580543d60580114103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 562827284 1250 562826034 562826039
    0x190509010e0f040b130f2f071a0c030103110328080f13030c0b0906040e06120d122007291023030c090c0c0712140a1703040218070f09 59
    0x1062a0400540d4510745d281c0340b1034048008482001c3d230040b4001c85100040c08154607100404480d41881100c4000009031290b01d14100360401d00501e4138030704d100b81c103c84203100f0301032880d141c6040c03d446000d522001e08400392501d03203030a03c14080c4600c4420300c0800c02c0d11201041c0e209100035a4840c40c0d0007815036076160100910381c01000c52042e44400288000c0c0031510344180441e074000302c003c000c0c000d0700f001c1c20000390a0003410b041d1600061b0070b18a49200d8600d1a000b54442d200e02d07602007a2840e40c090100c82e110307010710003000302b0654488103860903800c0c4400e904400c8010800340c60000e0700300b28542a801d00d440d441094403014245819003241031300c00f40e4081504101501811a0703040c50001c01c0404c80d07000704030f00440441405950300c0c01008011450203081d100c2401d10304514035017088e20343d00c0f00312085200300b039218111200c001420315580d5031015080112564803500d031440000c0100d80c4804000c4990b49c00301c0308224000b580545050913654103516144e00f030a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 562828534 1250 562827284 562827311
    0xc0b0a150810020405120a0b010902030406060b030403031415010507060506121005011802070809010e150703020a0203072c070306090515120303070e09130605010b190509010e0f040b130f 82
    0x75220000502300c8041034004000d030445913001150310600ca12400503026031610f11070007007500191420360004c2c2d521603140c1000e07480708181e650807103102110303143c4030080140002c2c00351060740c50090000380c03181c003c1045900c60704030445800d419241a5810407041842c41d800606003445144011048180122115a118400c6559068001c42001c3c900044031005451074a006015250031040890690b0100d29000f00504100e512a074090000101c00d80105450528203400c208125280d5000c4442c480100c0910402100e0b081c4034417050729510008198020f01071640300d41103542c10401040b65512803000802e4600c01e0450300b62100001a5082c40e58a0004440d5540860600350000d0003524045003085e60012406040701c0c48404e01e0341d11181074805c03e0788040240c0d1000b0400d00003081e91200b05d0500032070685002418600c070640001c11040c08000704502400401c240c60410783c0301c80d0400c0000302005065031079070148003048040102650b20305100700620b408241ca03c0107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 562829784 1250 562828534 562828543
    0x706050304030903120e0a2c1003230a03270302010504060e0609060c0a120516020111151008010c03051e101518060c0b0a15081002040512 61
    0x101e40542c0d50540f00c60540e501c1c0700d140c3c0c0303c2503241d0040c0211201c4200c803030707590100c10b030020703002d21500c0d841c0f4002c08100d0943c07054196469824522075034802c00000140c1c0e4070104080320740020900300000c0140d56940841d5400c00c030310350294010703806000c05040c0c1000346950b400078490000034100c685120117070070754045da00000b4001b4804102c10000a40f140304003c2c1000c100401040c5801300000000707003590f10490002c56107410881e20101440008002c1080c8411107003481850315190a801c26402640414000d040c812100d024500741c160400481e0030005481003013400744c2c24154207543e1143c003284207a84440d0b00f000480021a4883d028440c021100180c20480500c03140c80ea4402031a4020082c004182c00b0b031300000b809040c4405804403910b02a110440c2e19048081e001901c084036400050900418107a808001503184800d00e070710000c144400a4401000c00031080925201c0d0311220741e81c442e050030f085034441c50358014800c0359011101c40f00724030541d40400362207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 562831034 1250 562829784 562829791
    0x509010e120d0e060409090f170f0915070501050718050a0311100c0f08030714070209070309020303131403010608061b070305090a090f0b120d050706110a1107060503 73
    0x580d00700b42c507071a410034018210420300d08401811075080c42d8682c00d490086032854031081e100d504c0340d40100c2e814429079106a6003114000e90000c4c2c5042c0c060b00c03251080f8031510b0b03820f50180c61410603460344040c00400313840c400d0768000000e00c0541828400100380c0200b40428031113148030b080d030000d900d15010325130500b280d03030111081c0303600c088920800040079820340c9a00103115103041d080b00021f00c41c07142c40c52158070401c4801e4683c00c0160008140e081c20702c84401d240d0004100940140c0d80b0103108a43c400442e160204e001d044503c00703e8114012a0502d00f0a80070305003011070308185d18600b004807a078040d8003c014159842c001c40740d13a251b06942d508100041400e5684051030380c038005140752802801d21302e01d4414000046030603814107038402030203581d5441d0007180b405200d0040680e2003800719841403406103504005601d8580c1603100d401881000101034042080d650040d61004151581c8152183c2c0c1218014000d0f078001008000180915080801c0b0304e0f0048040d20300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 562832284 1250 562831034 562831069
    0x60e06040e040b0f010816140a090603080c060105031209130b0303040b042310050304080705070b03060127261009030f090b27100f02010c021f090f0803070509010e 72
    0x400238a011050141000d421103215013020807a000422203031a140194401984200c0c0e901d43c0c0c0c0d6000d062840d00f000010303007019201e80c01254440604025200944141c1d800031a080e0f41d21340007040103240240103402c2c0d115058003001c500000c01c0140c1d07501400c210b8004540e01c1000c030071500e040f450000e01b504049940000380765113010030365200b00081c40c1e05c58451410301c1d1a001b030755125a840d000640d44042e6807040c000040150799603004110007200c0d4910415000c151144170b4600c0a1104e02d4000d030804040452102c0302d000036028a84110400c000003982d07030f082408040c060141c02810f0080d4085450740100545607480f5803290811210b21340300d042c2c20000b04030007600c5180c100a614200501e240400136415503a40480101a00e01d01d40300c0c2c0ba0390b807038424030103429205026808419500311180141d000b00748403070300c008001202c400009080c0181c0c901103e014240c48805032107541d000c410482155045002001400380c2602c07880c1482d4a49010803107004c0b001c02da03200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 562833534 1250 562832284 562832323
    0x7260309180a0f090f0b06060c0a1b06020f150c0d06090504032714010c02040e0c031605011b0303021e0306090109062123030315010810060e06040e040b0f0108 70
    0x1008200b01000e82a00030000511091030140c028070150b280c00c0071582c042d9451030940c1e2240c0c2088554000200090000740094043ca01c09000705a03100c4074070f51040c103f505a2071000802e0382855200700ea220203980c1c001003000e01c0c0c440810030f0082c030b030490b412400310350850b00e101054180c800001c540004030b070140d40e21490a00b4900c90012000d2114141070050071000f541c01030741c40b809194103c3c42104000c0c0141d03002032040610300b28420b0004068608800010703c410b0b42c0c0030788a0104c245030403864008006141c0b800b10024450b44082854403007000a0015401d45003000950050f0002c80315031050381d807610410001c652652181e189107409004190800c00281d1403440c6266018541860310700d240d01841e020800b142c00c01d84825a0000000c01c0400340541c1003500a9500c00e18094800e89400745403c405403046000d0501480340004000d00c155480b00700700c40c042c00e8140c80d0a5400d080500d0101d0603c5c6054920303582488101d800402c4058002800b880940c08441130b0a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 562834784 1250 562833534 562833563
    0x3030c0102090a0914133305180c0d0c0e090d1706060301060e040906020a1115130209041511070308090a080418020f0a0c021207260309180a0f09 64
    0x5d46082d4a02900301d41029006541244a00c1d160881c10700f4240064411100402c40e40301d02c00c08c0700c1d0020442c044e00380042c0c072500058800014201ca044505542c11584a43c150030088043d2845510152400032084100801c2420205034241800e096890300401c061507404034112240c401c50f00c10b60045003d10041100511450300d007000400c000c0c100003180b80382c03500d41b4000ea80c04002d0440100d40403080141c0300c18420481d000e241d003d0075043c48498100303452084003480d52888080c1c404c806200214090203001e42ca00035014501120820007898a0744000c12990031241c410380c007041e4124002010380002180c5274401702c0e480f50840346070500f0448001407240482904c0b010403603007400b43c0001c3e8003d0500900202516850707040309482542304025955882c11100c20461300701d002d04200300081c0240c0131032000c10480700440300e8540100c20514501446e400207501c0a43c002c560b0040b42c24100300603010b00c00010090010001401004d4240c88010300c009000307114071801d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 562836034 1250 562834784 562834801
    0x2705100e090a080f0904022106011101150506090a0801060303020a03080a0c0e0105300108070b190815030a120318020f060307090b07050c0a06030c0e090408040503030c0102090a0914 80
    0x144601310b0700030001814240d00030a10100d23141148070b821804550072003400317100d6801200d051408481000203210742c0010034010000d000fa148103080c0100b2002c103104405940c1d1980305c0c0c01600040d0020840305d690780c28000c0d610811401d0580c0400d8000010a4004c000f5000e80c5140440644504481c1413420004507210342c081c60310341d011a41007140c10007420080800080c82a40312074407a01003941080001410490380d6030026010500800840c0500d070b2070710f0135030104804142040d1004e95240d00b0600e10100c0e600000650502a91104004110308054450100c3c103103075030b04000b11010140010050550a50081e52001074040041c900303141000043d0391200c1039150042616a455502d003203d5000b02004885613085090050342500707001d0341030380c010401c0d8503050140e2101e25901030b14201c07020300d00138000c403c0c290000d014405507004560003481c0240c200c95a840300444c007d8001e40003070050314420108a400044c82c5072142c09019000201043d8580c0c8a8944040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 562837284 1250 562836034 562836037
    0xf110301061b23070503070e0f0106030b03010f110c10060b070807050f0303090304030302060f25031118040e030301051810050415140414012705100e090a080f 70
    0x201141d18503401c0100d0085015104205401240c400c0c000700042404d00c82010704050454204000238500c401c01c0241c2034021381480c50440b15242000107110a101021901401303000c09010038482c100b0201c44000041e482c003c0c01d00518a0040e520100c50f1280c001d01034804501c103089520000b8400d5001013800e00c4002e0060034400c1c8211823501d0404a05141990411105000c10f9040420108141030301801503581c004903402008001d490842d80000003a000009207a1840c622455190001070095110090f01c20b408a40e41d40c60346e00b0701110554802e10b100c0f200d80907d05101058204640020689050f514003e2039070524080c401a41558420000c00c00c00d200c03010004002001d4a0350300c9956030002034800c07401c416030308003890700342d0f40c2e00000d06880c0124540440c0041003124150540d05441001c00f010f00203c24001540b00724100403407401c1501c81c40d00085c48059411580c0300001c860ba1243d0310300c01c07603680c50130048d140c900f8414043c1c1500403c02039058104401c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 562838534 1250 562837284 562837337
    0x303040b0a03020405030a03090812030c04181401180b0f0f0423100e06011d010e04020d110c0d0203070c030323032a042904180f11030106 61
    0x40c2c01424070360755800003031501c18002c1003607020400441050000714010b1080d00492800f00c2e000c04c2c594144546079070264405d601c03e5005c104005032191a910b41203030060f0300b0351440d5442840341c2c0d50f1502c40700d12085600c50180c4000a26002140010b4101f990030380d10440380040c00810041041402e010190294600640340811080c201080c0410b054100501504c65041712010760350414401e450704041c00380c0b405040c80034008e2030307900322801c41c0340c000c521460a00e80409003092500108000e400b406007013040e4903080c03501007101440c4103805000186810b20490303144548454081e84c0f02d100b080805800341103000c10038008603004001c80d0b58011115a01110305441c80e803441d8000f50420b88005681200f00d008a00300204404941c03030302c17400441c130008d10f002c2c0f030001d200c00784201c40c0300d1a03110101042d40c001101040a400c0d90020015200254a10030501104000410444032903039101850003041c0c3d003071209400152810783e0030945810354009500a0703114003450480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 562839784 1250 562838534 562838537
    0x41d030f030408090a060807080f01030b0a2715050717011e0e0406020c0724120603020d0c0f0906030c06080a0e0102041403060112030905010c06111204060b03010b0303040b0a 77
    0x10031540c4d500391620b1000c00010310169943e00700c02c4c1801c0c0002840081c01416440703807010039000510120340300c02c1c12240c210a42800001d040d0303c2c0c03002d4900d200890b401099041011080345002404020240f20000340514174041119503a00c00c1c0680c1c001c5400d845101751603424400522600001284c003cad41540507020040d011950780522000c84070b011242100c590b9000f0803180012401084000c0240c942a250b0b01140315907540100585200c452200040009410082c40c0203c0d07640d1003240515000f0301000500c00103411b000c001e54101d403140c1c49421410030b03400160200c09200307420549500000a090443c0341c10021689024094091540e0710780c0d807840300c81501000d10092006108030302034211030784243c800301420f202e0140d0090f20205c603d4038414000a60242807201602d1003400d0500040125080000040403804d00141d081080000c0700018403002c0140305100c1d0f0300c01d031010b001f204400014142a02c0310103581c0c40d01603000f80300521014996001411b11040c19 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 562841034 1250 562839784 562839787
    0x801060f080d0f121d0c0a210c031a040302060106020a02034902010c0e0a0e09030d0c2c03100b1519030b0901031101050a09180b041d030f030408 64
    0x441480130101d800b540303110b2050f0b0000896080869505210080c803821007222606101e0703203004030080c0701348032034800002e110716500119020401600c40d548c0203103030443c6c128480078003407000c280c0d03060800366003e5001d44283c200014826100150083e82744d0b41c00b07000343c41010300021101410a03400e402d006c02d404c07a0b10740b41d854070803031580c0403841520000306251001200703e0303400f0b401c56080c04107002c2003180f514940300c91611039006880807110021b0070040359903240913140381140180c040c1e00090030b0800c2d100788a0541d01c0650315840f8103249a0201550384d0504050680326090000b8a81541180362054a4100d1540c0600c1305000c0180811455412105400b0810750011902032200d02960300e15801c055818803840ca03040c60141c50200c81c40d415919025407041080d9030780c43c100035000803c4020b0034803a1304040300420020340b2200308a2404030080c0701a1145449141c0114074001038074206122551415900c802c48402440c40c18281c00c0c9145141e034801001a1441c0310b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 562842284 1250 562841034 562841057
    0x60506043909180f050921091c0503090411040602060f070e04020a090801060b03010b1902010212010330050d0f14071715091810050705040801060f080d0f 68
    0x4500300c0c03a84200e070f902c0001920040ca1111041220400303400c07034059a10518503030180d4049240100305a950300c0040b01d031265484030010780c03206400707a400c08840703080c803055104026000001d00341d803400484084c041e0103600c1040400e03d0043c0e01c1608010390001001c0381d01c0031004c15815801402919100d55900460000306099a002c414030f8400180700354000c111045080c4140c001408030443d10034515490003446420394080c4044424205444490481065001354110b55003401120700481e480e69607824200310340c10510419a840b156500080e20142d0f400441800501041c0c1d02c03868140f030200d5603480c005212031a06466910340c2c45040709804a10306148500c6a4501e9661441d5000b0811102c659101c001e03000640d583e035014400d40060307403040e038000e521a0900c24101012100c1c80349141c9040d60304400c4d1841d441c81c10007449912503200c4018030565000a009000303c40d03032000748402100c0380d03101d96689500801568072010744601865008041d6510b0302d13450244 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 562843534 1250 562842284 562842299
    0xf0507080a021f11120403060e01020a051b0313030b0a0509011b0e060915041703070206040302090c12040c050f030703021806030f0303070c1203052806080604060506043909 76
    0x940481708605405804902003080060074003c03051a064218025406c0c02400f8801820070700415851542d88003a41d000b0b0302c0c00c41020000e803484000d00c626648220f582da0700f40700101e080262402c00100d801c1000040300744d4014016070348900e1030f0100c11803049400790030031920741c10070051705c5920000410001035590f0301c03030701582144241005825036035031070702d115004005007002103c51030ba0001d100090160f920030050324101c0340c040d20601801e54960034942a24070901c1d443c02244942d000030701c001c3c4821102d8400540b01d0a40b14480c2c140e480004066481829200003907002240c4038440c10000c0c02c100300c1030342011018084030038200001250605540088410070001041e030030100b0148022300c0300402014442d800c04000394144594841e06040540001c2450640e241c140d2000c1814250300820090035208103a821609081c90700d41302528042d81d2451280d0b0601400340c032920301c2c04000308000e501e0790840c01d42e2400d8580385118003078080b0b41c0400500401c100c0018944 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 562844784 1250 562843534 562843543
    0x207060203040809010314010b03160c0f030e0405011d040f02030a020a060807020601090923030405060a03020306090a02040609090e010209090c070506070203090a03110d020d0f0507080a021f11 85
    0x103e10880f00c00d501d9103c908001011a0003030105001d054505c4130042001a1040703040380d030001030100e40320784130400704079043c7c0d07400602800041c407141c29500130102b819070111440001140845080c00b09990b80d17405412104a044e8005403151034810200300001c0d074110005003010f2010f0103844103071506800041c00207820350700ca8804282d1840c200003c455061141078050302e41c1b10804c10124015032244c0075051f4800c00c940ca00603111050140e2003002c100103907001050300503c40b6503544100d100c01406034205940c1c5602800001002c40d0135000c0500980d810303540150b440903070300351804045101900a000500c0741c00c2d5400c2004185944500801c144240c4295400c55510402407900516000008082904642003404055507941e92101ca02c1c081301e4000b2100707881c420001d0001540788100b000025407211619008601b044003100380058118043c85c15201400e80c0c59005030307240c5001e200000c0d4040390000c41c02c0ca00072441c02da29014078001d1714003801403141d400096850b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 562846034 1250 562844784 562844791
    0x904030c0c180504120809120315092a070305030103020904051218030c0a06020a0206160516060f030507090611010e06010f0602120711010311130e06310e0f010f1a061303150207060203 81
    0x1c0030030518330703100000d00d8030040190114448912890410251401000f60006000c000c2c401c0107031070003003400e04c0b00400480b100d1078a540051030303490002c258101c12105000b4500d50290003070f0300d901d8a031031800b05040000c503041c54001c3c02e0140950b40c00c0103005e6001c5d00112400450f82e584407804598100250311602410a030751458182c01d0450103050b026140c10140105410001080480f9074480701e2101114030341d0030500754070b05000440c01e024250b000c15241c60b61040000016035200c0c0300442c1001c81c0c1e00c0381c00780e400c45c2055500060307551082c02c80180140b00c0018100c00c26500c41d91150042144085085041c0090803c0c04042402c107a07000383d051000507018050146480d0084000400e94010401050408146801c04a02d8802e00d00d414403580c0768160000300030188420740711104034034003c1044480380d0000c0c200030310b0303c00e50391280c500e032600044445007410011940c0e040c1000b40410740c0b07689143c0c2c4035400e54494840717200d003068003070283c003001915a0014500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 562847284 1250 562846034 562846051
    0xd08061f0309022d04052e152303100915170705090402040f140c0406090b040b0d0c020304120b01030b070c020904030c0c18050412080912031509 64
    0x680940c1d500400031038048600c40b0019090302011300c40584c2404216401e1460f1303041d030300410540e540452040c60384e0305004d20340e1a1803000505908546401c00b400005a8209182102e00d101c00300d182140c90040300fa64151b460304442082d0200c0e04000b1001d16401840050340300540764132030040b0801c0d90300c03a40008450200090303062002460b2000b0300038058008a00901c4074500d44000200080030260029008541e10400d02c2040d80d02900000602110041040b640d402c0001c540c421540c0540710b51000a2100400491403c0039070044404030750f02112020b00b060a031403441070081111010680652108000c0042c1c441c413040110132a840c0641205005585542455041c1000040c05401081031070240480180d41d400c840d1900150180f410900413030080c03031700380d07030110b102d41080449030821650204503c070190041440345102c2c0f1480000407000c0b040a40e44890140c410085c0c1744c1111810b9800e030f2102c0c0d4040c0da4404207903115800d03211000340125880b0041541c3e40803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 562848534 1250 562847284 562847291
    0xc050613111f020d030c020c0118030506070807020c090f011e080f01022701020d05071407030b150103091101050f0d151703070c0306230f06011407050d08061f03 71
    0x9400e10f8062080c020380301081e00b0b0034003000440410081d103c41c01d6455503414842c01c81d000e00003801c3c02da81040d015681c0700c01100c03030a05090301d010740000c900701c8200c0014414020603d8035810068038450140000d80000d401c242d003410100310301041c842e05651455180708000145004081024064282c0480c00060359110f00705c04d0999a2a010184507a1082503000014081c7e40d0008100c00c0007407862800e00e403a0012441c01d0386130300c0617030100c0084c3c5108003800403051280c0f000c1d4142c004d64400ca03511506000c02d00064003941e140b6507015202c83d009650046207940524010011818061212032034400040310840c212107008156041182200b035061010305c1c0110401120440054015800c01c3d034543c1c1c2c1c240d00c060480c00b0040a01d40c0f0344504160480384600001c00141ca8070620251600e00501181504c100840b011400903e40035010f1201402d00c200f00c410164102020f400d007500c08100c20707941a08058040c40d004007200b81503070040c2d14545440c59a016283e40c1c0403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 562849784 1250 562848534 562848589
    0x6031a0f190e161805012a06050a0e061003110136060513030206090d0b070815010f0203161a1905010501031b1817060402100c05061311 60
    0x2c5584403081c03d4a1028001552908019000c100c000301c01100d400f460b0508012602112040e40c210a911103001c00740444a51803007040125040f152040d4051a020401500e15034012a9074840543d840c1c42c00c401e05920030b00115268041540304000117041c19125100c0030201010450501c1d994220b803450403811428180500b0440b000082c101072078264240740c6160b80600201c1d041c1d10009205040000d40d010785c41d103c00b08440b0240d60008890040d03841d1502001c0e1281001310f56400411802d90040750296008445000184026500450070089007031200681c0700c1d1744540541c0c00f8801c2a0a035042081007200c0c2a101c3d108603659107403a81503070300c4a101640d4040e0031143c141414400c0342203c1d010100038010440001e03281650300d48580f81d002142c0070250390054001c01e400801e02c010a50400507c0e10b0003640f09546c40300c541303240362008031100d01e00017400604903005100031805801002c030300c00709072034040c0980c060f44444000024810221410500040d5020118103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 562851034 1250 562849784 562849801
    0x9100c060209120606120304051008040213020d02131505040e0a15080a12020105010614180a0f1d0f180705060d090506100509160201020f040803090a06031a0f190e 72
    0x7246c01c00c11042005504181c2090001150540204000810060310307000040640d80d0f00300a4440030901c00404541d200f045114200c081e50084d0348518010701c081e0030005803a000480c083d0349025460f03842c1418a8144901c1c0b244112000c0e08001070b49031035021000a216813220000020803803c001030001200390310302000344485035420710040d079141800410001d9085141c00554001304038134940e8a0011041020041c20b203c2c002c150407103412407000c14800c010103080002e0f2121102030b2030b42c604100d218151f01400480b00c1401400c030074404581303004d0b0300c45d000303180300d1907440c0a0b6450a43c13035402084540c5c00810490800070f8a95400d00184001804ad180c0c00024001c2d44403149400c120102d04400350181c000d00142028441c184a094400e505507100700344401d608569550352060a030340d4980095034032a201d8807004400040c0c060081c4541003249030683c0c4020581080750080080490240704000d421404180cac018080d200c0caa034240018004000c401180360900021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 562852284 1250 562851034 562851049
    0xb060102060f040308070f0e3c0306181c05130902311a03040c0605090d122109050d0801060215060109030f05060411030a150902060c060c03091209100c060209120606 73
    0x440321510600001122707940300030036820792000a1318081d0540591a07041c039440d00c2d0140102d4607a200090030b841003026400300081c4030007900c09140368a6592148030701000ca10810070b13034100202d040c3d820580b50601c51900c2c11000b040d8002c4030b4038269502c07261002203042040d10440c400000100b04005c00c07040c0103024000d04030303d2501c1070614000c9004140d000700e038110043c1008146d158003410080c03140c1d00d441803051032000480b07400117054070310341c0162924a600b01c4140c002d041685201b81d114039661412640281d009050312005409081c072501ea0141c02181000603048001c004680c054070301e0594079200744001d188501d01420a0741240300d81c032940c036100c0d412031720180c0c0115007000441c410a21040c000010030031900c3c4000750b024828849500a14050030081000002044029510030140d180c142c41512550b6542842c85108100503542e0200b0200c03c400072a81c8114030001203e84118401481c0002400000d0780c403030818030320500c1e01e03408002080f166081088 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 562853534 1250 562852284 562852369
    0xc07140a030216080d110106050402070827011b030203090409051f11041418130308010609060909050601120e0a051608070b0c0a0206070b060102060f040308070f0e 72
    0x84070a40341342001409500c4038241c4020104000c071904240f92a40e0080d030080b4000c140c020000c42d0b95900b2840c1000e1207070080700f00020300c00c54440c401d040000702e144040180d00d030140d680040e01a5000c0b08490580e401031826400c510060050941035240d0f4452311030010300031401006045802c0140d140f01100c5030030800030550401003101d8002d02c4060648054411121560000c1101c050126803e0390758120954040911034090000034891000320f006002d00035920480503a807038400580e006501d40c428000055503a000400c00143c10340d00003030308908145856100f140252160006640148951b8881600891610410001e080003101c0400d0801801c5400152502080382d417a42c0d2517110385182c440c800918020440400c2c028a00d0300d03039000f008661030310070505210f00601c0703084944a01601c503030004103642c0d82024085500c00c42d4150b40c2c0640c1075a42da0b608071402200d0120350000d1001c12007081c1e4141c3d07142c0307290784128041088018000ba0841c81c107000c00c4c05540d07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 562854784 1250 562853534 562853563
    0xc12030b210f010203011e0e071e0224010602010e0105060f010320040b03010f120b160e1806010212070c05010806060d020c0f0607031a090c07140a0302 67
    0xe01a69103611031034034208903110203407024600004682003660601c40c0300c00440b80103510000000c9000c1c1c02d440c190191f901e040000180116885100070240030b6030a84500c030104140ca1b1401500307203141900d41b86507004900c1660407003022035080d450200104032407000010075070401840b14a60911652201d900c4240003800b06060081c0854281c20108540f035041584a0401d1002c50b10300c43d503192803038404000d41940e07072559043c444d50560028000d95102c4103101500081d035408507108400c1711600a401c07180291501894824150300c040c0c0c1050500071044605000c0740d8030000c1c0481a412031042c0011a071421130002410b00c080803402c00181d100600038100456405104030007684d2080c00c020b205030b2030fa100001d1090003084541c4503803038000244051440c0010861007240c068101c221405511412030a0342900d2488a4203114540c1302c5e1250100c901e0890304454004041c44640e034a0b0020740d40392031403d14100303102c0602d20f40c0030100c01c400b0182e04004010000509 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 562856034 1250 562854784 562854791
    0x60c06040b1006082a032809020112151a0408010e0a0b0103060b010309060f0b09010501140d1d0105011203080916090902220911180f090f0a030c1203 66
    0x500001805100c2d020f02950170042100102c8660414000d01a844058018000726220702e07040c41c104820014580c408100e0852001416641e49a14001c0c1c1000703903816141d0031101c01e00d40e1040002042981e010b0b40c0c42120328040020901e8410105e51035040710501c002d540c6905028419080d160790340d05188041d404030245001040f04205054107595000300049420882030004030701074a030b8040040c1035140384c0410400720500c50390124840660690b400001c50b80d07514015244003040320840c20f00b041007003250000700c401c4c560041c04041050f044a9185841042c142c5003190001d801550301170004a03550001e140c0c0011405900180c00c1e0001c00300c508d01512001d0610616104079071919443d030300003004554500118001c564006802d800030100c6043c2d141d8060a09080c00b84c5c1d013900c03540303050151810850580c44041142075204900b54a0b107010300010400000e00e0114140a45c2c190704004d11414400a04014040d58030000c001d8140e0412448440304400c2c4007003410318 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 562857284 1250 562856034 562856039
    0x20f0907051b0a230109050706090617070f0e0307090216021806010c0f051c020d1206050303090d030903060608100b1c021c06050c0a0207050613120809060c06040b10 73
    0x4130101c803c071111001000c1d14401a68000ea45002d80b4002d00c00802c030340900c0c1800308546500c4460f540407540d4030750b203504500118581001c0300400554400000840e500c29940301940506d00c0c1c010310b00e2002d411603034000e41c1c80441070100c1e000484440030400c1c2070560181549409005100c148100c0000e0342001e050050018014a40f01000100003200861044050000c1805008a00c100d8041c2c0c2c1500103034040d0009460f448422040c2340031400440c0429161001849000c00351360028000b07520305043c0c0010028084c01691048040005000d030220000d401c80c02960010610b040082a0b40c000c1040701c0c00039035a0000b903036405040b600914140403240007003030f90041d6406440001000160160301030754801c43c000c02512503810f2400b40078240840d90010300309204680c1c20f6801c1e03642c64508110040c402c4402d424100b44801e0340c140702c241c407050941ca030a5481541032510b49091400402d0707040d0004280d00045030080390030007050103513003849190302c0700104c90030000160 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 562858534 1250 562857284 562857293
    0x501020d17070e060a030f05070207180b060405060a05070c0501080411090714210f010b040e0c091c060b030708030d0b0f09040507090c0503160309020f0907051b0a 72
    0x740d180215000d94608804194400c0c041c0701681003864010f41150b94943c1c44e104064017034142106903038030079460000081e140a01c007040f80c0044e10040440c450b08840030000e01d074003804c20409800d45c000f80400000941e41d0310100140024811625031036280d6142d070802600c90030b003d80c000c5061201c0f00c0200800591250003100d00c0980840382c082242d02d8411007210505204011802034560000310311120720300420f03050504107001d41000385260381d02c10122078200c0b820321035000320340c0007071000707004014120b415035034010f07090203409041040700c000185602e2001c40f020301007494070724059030a228950080d06016041030f00100500c0e440c2c214050703070301d21034004803500300c0d42d403108000c0350340da540313940502c50041c001e105001504041c07c1007a12001c840c80b441011924105c07080402c903028505484c031510104403441c80c941c00c5000c06502802d142d900403640140e094211701640d42c3c0d00d8410034011302040d51001d44800b0700152428001403200640c036000c2e032100d0035440004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 562859784 1250 562858534 562858547
    0x807120507090b040b09090a0b1c0f02090a1e090222020415080f0901150608040206070b101a0f0307050c071710051e0106030c02280b010501020d 64
    0x9014490006080d64501008440d00c0403203802462802c1400100050180c0e071240c00fa1a40410480e100030094454075000700071103845070050b03600004c4c541c02c8110101600c103404010a030007007451134640070440c0d00013810228101d812441d219a543c02c20700500650444a40180030204003c2204001c01d4001030040c035940c5040403607800008440e0ba40007405a01681c000748581c20710380352481542d00d00941610003c40303907103004003020400511950014081c0a0843c00500c2e00107207501e080a404648040c0020300c01d81e000401001140b0000340003003203c034490301d01a07004201c2103060151440ca00843c0e44d0031501408010f124404480c0c2c48403044030b801046909010707035901c41c940c0056040034110ba01500001c2504125600c8240020918500721425401b0420003136032008109195501c0d28240964010317451070050150741e0203680020000590381c01254040049150080c038041103818580d9031040a5044072802c000340c55a8250140c03e00f40080c200402c15940014440c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 562861034 1250 562859784 562859807
    0xf0f1202073b1b0f09010e01180504020d181109070306061409310b04020315040b011107170d08091c0e04020714060c030105011d310c0807 61
    0xba820800c000c581051820a614101906403e0009486008070102080e032500180603a81c04510712242105c4039602c103481c803048440c02c40d196030b4243c508101c00d0000035008491160800c40e0360750302c13030804000c20040340c0c00c0082c07090a442254102c15814400c03102e101400c981d09060406009000c801e8220780003441700c00080940070f403203c900c403000580740640d20b509000b016040b12603294103c2c1d01142c600d09004071290b01403010303000d803400740b004034803040720355003010340c482e160700d0300146055001540c084005141c00d184480d0400281d07824290242d200300480b036a00140703107501a030248004051440c4d5410071140b203107015007140b41c41c3d4022403032540802c0100340d401e05006001d40089035001c84050002c64680200b45014a03a100003010031b9141071051100007243c072003031001101d040e0762069442c0800c404040c1e0020042c0311842002d50360014040316000e40071b006070815882c3c81c09184200c80e800d02c6483d0600b000f190800c014002c01c21000d042040340c1d40ea04694040b64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 562862284 1250 562861034 562861139
    0x21b0609030a0c1110021501051807030b0a1a0406020f0105160507030210140603010b0d03021f0e0102070f0312060608010e0a0b0406240203160f0f120207 68
    0xf854a003901d4000b4801d00f100310a2980200c01400590415600183c8402e102c0350b040102c5a1a907281e004110a47d2580d8075582c0c00c00c01c10b84001204a071081d08100c00071480507105080c2c00c2d40340c0012184071411f969490f21408030114003003050640c1086802050b07a0414000c1045040040304031001030107421056081c1310000801204151080003042c0c3c6001c3c803583c2c00c03c00c0b0360754100d48686a400540d410b034425800d0001104051502c1080800d01660640040000d640750360316020200b00c100700781480443e0f4074102010500c1d8207000514485105040081d00d544c21072401410f444034020300111818508402407105580140d070003410b40ba6150329040481e07030b9071410f4001a2084201c419042803c050b00054201c103c4c541a28102c2c0c08103044000300c1c0d008032022603581c01a648141500b094225141001c10060001403440500590a0140703a4189890b0407604400f1414000010385c0161000c0001c09c4600d00c1a80311032515a40c0702c1c42421010f400c41041c01c215202616 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 562863534 1250 562862284 562862297
    0x3040f02010c060204090c2d080c13030506071e080403030906020c1b12030a0507110307030c060c0b0c0901050a0809010b0d03090e090616050f09060301030501021b0609030a 76
    0x2825603005070010403000b644400195074036a03ca2030004050300e82d4003581404103d0030882003200d0b0f0781c41840c0300c1507011150101746c0100e0321007078210b40881c0701400948026000700059186080550400c8020354020710060000d8140300c0c00082c004e842154a40b410300c442100002102544803d901ea0000e81525000c00e81c6c240f1410000c0007031056008020603407248180e440032040044605410002c000c0307a40c090a2041c071141c5e0f648034814540c0550014108022440001c0e8004400a841e140060b08440d82140c403940d410315840c0035500090089429038401e5030030800452010b0358000c1118016504185030b900001c1c126004040c001818420210002044860258072150b1040b000170300b1101415036604010309802241d00400b808000700100045410030300084450240c41d4040920b138007106e044000b1139440d0450b00002c05030b0b0310100318905a41d580c0b0009035020310300800005a9500107100c200c1d25656440c07014004a421102c100011144080f0561f1448042806d040c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 562864784 1250 562863534 562863563
    0x4060609090c1e020a03030c020f1f111c06051f0e040906021b07080601121205121815061f031d030c0d050c060103030f03090c080c0406090b060304 65
    0xa48101518100c0321004030303010f400000b001a0300003081c9800c680a501c08102001066000701d0715400c0303800740c0c800940d10141060803d4031101034070710240f00051000061403500340c049a450781d80242108140d124035050b040308800024850300300208401c682220f128054208450707401d044003580c650a0101290108600f5150345e0442c2c06050340c40181159030381802c46130030848201408481c0c0c110b10801501103000c0d0300c0041d00074184d80c03038200e240309840e003540e551040c0d0070010b0b40700c0400c001c0705100201c500c511006c3d00902880d0604100fa4202040450040c500006201807070620030104c003e020b2607440b60900c07864000380315502052408442d00d019030240c556104071940000d45da915070310380304c0c0001c006032002121903000c0d00c800c4a10074000711401e02038a285403a05412290041000074001c01c0b0b560390160603030802055141d00c98486601c10301d0161300640090f00300031055151481c05126050180038103142c20031403152502d0200d44103001c01400200700200744070b0316 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 562866034 1250 562864784 562864787
    0x10030501141002011e06170724091e1502011a060c01020f180306161e0e0303070f030905062508071704050a3213090308010e0604060609090c 62
    0x45a100005c01c48649418074030754903040002c20f42803066140800d0441c452900d10180412400b0803036015841a40c40c041c048803070540b011010180e004140306046200207640152505511401c01041046a0030706185c6110040c40c2101c80d444070085901d0000611010110745d904500c60040c1529820344603032040095a00901c01c1d005003040051012441d1074242d624603400b03504540c1d007503003904c1d22900d030302040d02d040c008881010307408510040400700d202c03280400c2a00ca40c2c07605103003100341d80c110480801e0655010150035200c0400c024004018075400c291040700902056402038a42120796407001e0300310884210110074415035400000c140485802a1140070390060503010004a000401c400b040e4414031469009010342c2c0c00008056960900c261406510b40e05000c0140c0300000c680d800c115002c81c820303980511b000c4101c0076150898880c2010032480b80c0c6840bd00e650401540705072503000141002c1c450b9080a0051100980c00421841100c88a0700082342920b61202c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 562867284 1250 562866034 562866041
    0xc02032518050a0e010917091c030c0201091e060c0c0509100305010c030225060f0e0c090f2707030203100c030c090e1611030c0601051003050114100201 67
    0x46034203009100c1d4403078800c800c1190702c01c6000d5024060200720201c001c0000a00b40c8900080c081c01030388030b0800341d510400c03842c0010840204014070201d55490200020b4030103c1310386000303600203018001d09104558101c82c540014100c00701c04c40501242c45e0145491000c4c141c000d0108011406030301d8801c11281e44607840107040020441e58980c43e045050040442c0c580c4030980e6190700300280840064001e10807034000c0d0140038845403041c5412031180240307280c0300c582228079582d05c0640c404a0500c91140080551012018004607280c40c010842d01c4140035010089071880344c0d00b8050480c07002200741c19032410110580b562441000501414444030345e101030b42502880020a030001120750102514002503102088002c10002c0b040720062494010000002c5010f0049480c62021071018600521a460805d40e007100c10707403803181580c00010b41860540d1204005001c14504910340090a0080340b40c10003071903242c191051284140414111f0151413041c9103024118801e41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 562868534 1250 562867284 562867289
    0x1050409081e03070f030e1b011704030305150301060b0d0b0d0b0c0307080a020901020a080c0709060b031510050301030f14010903020708061e0408090402090910150c020325 76
    0x4140d032484203416070042e0240e10840310781c3e002409102d51032004c00c1c042c2c0301c1c82541501000082c10b0201c0081d00e400c1100c0900c1c0881c074184004004103100e80c020b0700c0c540030b102d60310941c2c0200d9503080001400c2503514a01e422584aa41800001d000c5c05000c801a60402000918045440e415810200e41240d44481d0060700b0000c0b1482040102c04003034000394090021a03030b519401d5615032079082d00328001d02a2260068001d0280c80010400d10009042480100410303511040d80d6074682c4070858500743e114050300c1d00044104450003d0103030146250240039202d5900076201000d00504600c0140001041c04018003650024042aa446080061000002003000201606005c0d5440c940380c4101c0d0350a00c24500014210301140b4880350708001c862807030035215112a521106603030440318943c2d0f0086d9007448100305070b035542103600f40500255051a140301d07080c10036941d0030303190111148051011401c0d0140042e100051301100e0143c00d076445444500600e629401c0d02e03012503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 562869784 1250 562868534 562868557
    0x30812041a07020604020915030a0318080102130503010f0c080f04030306032306010501021204090e0a080f040603060f1a070320011410060207120614040b0a0b0306040b0105040908 79
    0x1401040b0300d90f0380002d42c16002d14002c030358150300e07641c56100c1c0c1814401c442181079010b0304600001000607000700010040b03107040805040304036850341c22841c226008030030b41e218803082e440e40c1008141801c3c030540044c0c240a0b4018841901c0c2014042e0400001511401510202e100010203040c4a84e02070300145030300500080d0480d01176070700c41107620b1180c140004103006103800004c0311f42c00012101c149100c00c0d5409030805191a801c2d000800580329902c0c60360140f0403034000041c1011004100c1c1080c1100d8040d00d8078140340d0700070300f1228150004802001d0100d0b0a00c9030202303420128a0048407403241c550741c4c3c4190724003214040c2c1107185180d0f644104060704603203848107410035402c019514000c180c29650f9802c064003c0382c2c5900c40c5c400075030402d540520052900f012240d200500a8801183c10460600035038603d6400711002d1318205022024031245d1344107406010340d1301030700301c1c010038140c2842d49540000d04410310032244120f41d2400c0c4078003084026400c0c0c0350441e108 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 562871034 1250 562869784 562869833
    0x130c05100306080f0601150c060e0a06091407030c030b060d0f12030b0609060307030c020304082e091709010e03070e070f090303020d050f071b0306060501050403081204 74
    0x8140000d0060306042c01a50f280b0300604a8000d0b0140c3e0010307640d8100ea4070ba842d15060401c25000945a040346202d09a41071501c84514070099074040000c0350b0507a200b6100050005c0c13041c14440c20001d404085155150407105040004c20b00415881081c1d07500152449415103075140003030041b004611000300012281940c1c0700600040b0718840c46c549001d51024000c12001d2010000184100b03030711243d0041003400802c5840388a40c3c042034000c28280100c0c0d1619841c1ea4481e483e00b07105c01000c2c11940290104a03900408600c8081130031242041d042c420301c0320035600c91004120100c00070104141c0400c0240c07041e0311410f080302d07030800040c00b07542d015a20303528075041c42041221394101041c1031482c05d50495109240103c12aa0035034003800c5003010205007210749a109400f07040034034000340010030108500c00c4040c07891000d81c403a051100c40c9180b40001c1550310355403195050203001d010800208400e81d040304c8102681c2e5484110642e05e500e840112111031413455840b1129 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 562872284 1250 562871034 562871059
    0x60807030203330102160b030103140703050f0609011d0a03110304050d0b090d0c0515040f140105060a06020d020c0906120f0a1b051003020a0306080111130f0509130c05 74
    0xf0300d0103c0406100c01e0307007074840139104114490710000c260b125006244000300010404184030000800410444c074060f02e201c561307207880b01d903c1c02e1080d0196500c0b6811400074450244000d12901c08d01c0070b487c00c000c7d5645403001c2c40b001d498042d103200c06028010400c0000801c03000500440b00130300001080d110112005042115011804503010a80e5105003848160410302851007030034010750000050882003584040e290f15080040d00c12900c040c540034984001408055003d070750814400000601440c3c1802001700008103907200d4819500326408030b070f5255a01180c218106601910610400d0303e500b80800c6d529007007d9500a1070380141100f4082101006c144101c03107502807079100c1d808a221808450540708030788074081e400044134a0703c08403903019401400c045034103400d0015041d907680013500d083d500201c0034181e141400080c1e055060548441d28005000030801c00701c0014280004902d9910014100015000707141d40207504200305140c2c280098440a8400c0030600e9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 562873534 1250 562872284 562872361
    0xc0d020f0a0503061003150203060a06140702040f020a030b09040507050f0f03030a03151505030420030a030201270b0c0913060f05010f02030901020c040e1e0d020f07060807030203 79
    0x445d40d010072940d444200303881352518195402600e008032402031052070241e2601c80c081d200c4c0169055500c850320740512081016940d50300c20b0f464071403848072015139141c03981d00c0003c2c03c44814100d424032500e0b5180c18000481e10020b1035800b0769106584000710000039a0000d5451407140e481d540d898480000c0020300203901d900010040034440e0780416a95480780e2804006521826050340080d0060000030045604e50310044c1185003015544c160001d05000801c3c00c02800030415001342c1c1d101d61903080d810b00c00601e03003860803d0010710803a0408003960384412400000e444941140004a2810041c0d55030200d11100c00c000c50100304280707907170f50b02c0c00094921144212404161020490324100d0b00200c00ca4900200c168060035001901608020086c108001e02c0841846080c10001c10031000d990204d481c081070f04014007107586ea1300b50007850300149800240705500f004401704081d68012134021382080301c0c0c1c1005a12592030000146014107006440300c20040b134940380d900c144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 562874784 1250 562873534 562873561
    0xf0f2a040905010b03010803030f18030c010b190b0405240301060216060306140904060e0304080309040617122d0703030e030313080705010204030503030103150606020c0d020f0a050306 81
    0x4a181e6201400746a07a1803220002c00c0c0002d1107031410303035042000043c84000c082c0c20341960201c4c071641501c2c0c404000e503017540e1850300100d0503946107a40d6070208101910f088188030609036070070482558164109000c071a441d0180d4801c6a0007100d2060344070b40d1042c1ca00412030144481c68047c5a2650794546c0e00075550611055416040303500c881020400511a000300010707600c1d44c140105419010106015101c600180103071740d002d54414841c4080e8405200030001414400700a6440b03190301300410084803665400710741a0225050140d0314120003003080302c07140b0741311450113840d00d15003101c208454840791202078100b05280042c204903034024015020300d50003a82c04110702c554500e41142e49100030307120b00c089150851100c42c0020341e0580104403080c4201d00240c14150350781d41d12403440d0801c2e08200c404241d5080c1c6034000d1035980c0b20f00401032035903100911210750b07000c001c01c0c0c20024600340039004144540c0c0d1000303581c9991600000507c070140c101d0f81c540c50081001c690b0b0307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 562876034 1250 562874784 562874789
    0x60609040908070611030630011b0e0f010c0b07030908040306020301030506090604210c0b010e070f03022a190503090307141f140a030b1201050f0f2a04 67
    0x515190205c8030307030b00c0c0d41944150781c070071000a40311110380d1411031008c081103420b485514690000100719000294400e006d115840d400c0c2d0b4184001d12444400d0260401e40547e20460181c150b600e5602c406a83c064100981710307400c2401c501580e240d080b07044015240a80010f0300152000030000700300205603000710704176070107402551125110052710b103441e184c003540d002d050b5461002c981c001c03040e513a503880c08000d000346c107150040c8030a665034001c07a144241d204a00c09400c28040210b020340064011002c0c00b09442d0840c41e05903074401c0620103401d074801e0f08041d20b54110100c2e80c0c480040040248103204100103110003141841c1407582d0f5400b009610303008c0d010314040000c031003010521107030303894a0040c03c20240c44502105114070815103900c4008028121000c229240c01680040640404940d4040740002454052082000c5000c401c000c050389000101b101130010406942d40050030030340c49030b9881d100d11140000e44076030415081c0d0503080b40ca5150201c1c1c1302800040c000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 562877284 1250 562876034 562876043
    0x2d0602041d130b0406020f090913030216150e0d080c010b2103041401180b090405010b030106081302060903100f0b09070c03032f030a0e0c0d030806060904090807 71
    0x341c0e0b54060180b000200d00e410020a994206004540090480c0c0c02500704500302c0c070003c2c1d003032003100000909005030035101200c40010300400c1000f031503030520504282c00a11004030101c5458501049410400030b4120020030072412040202070781c8103442940d11076008035060fa2600e1000c1c40460090050035100382c49106209544074222048007040804080400051420070f854001050704c00041141002d041003100c015038032424009182035406002c803100000c0d1100c80c20707000e000c2241c1041c5c1048108402c18001000f4207039002038401d51000907107000300100c0c2200d2012548602500900703d52502480c0390403035480002e980060071410a6030414003c000030301e0180080c4600c196050000501009120400711307020b600300500081120340354240c2c0380d20720516000d0311070f80b900804030303060000800e03c0220215406031107101801c1d0409041410200c0340014030f181e40b0040000c09224000002946c1030b07440c0c0c0151680240094810300c0310815603e064409a88030000496 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 562878534 1250 562877284 562877339
    0x30302030909150d0219030516090506091005010c050a05100e070f0e07050313080d0203041407060e150f0304112809111b0d1103072d060204 62
    0x18542c5900e5801460f000030007400d9652083e486809001c1d01d42481200c031440000c445100100160041143c82d8003040e0303038101038845a042028100030340300042d2009204101c031b00c1c2401169214001d81e9011541c00342070281b0b4003500da08c0c109040500b1980060407070f0080300010005607150741c0103100000070920581c0c5505032545000100713280a03018003940301c90a5000989207500503030007150002c4d1000841da514040716682c000340c0b60320450814203065004421303c010003640e01c44110510007200d0262100c00d042c05002000503a00d2105103200300682045911704543c0c1204680c400450a201039a903850701e1b05003840c1140c0c50705451030144000a400488648012039440e848640c030b68036405030781d860580da50740a48502c540801c1c10720000c009945440d0b1025009100b0264000041e000746128448058042109130070144042c0d04100041070000d180c51502d0328000d074041d118440101244c159030246100e54001c001c042a1001401041c01d40c8a0a01034520052075017040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 562879784 1250 562878534 562878541
    0x1501121b14030c0405060708190207060809061509060d02030f0a020306160806040b0a080d0c0204150b1b0f07030c080c04020406020c011202160f0b0702010c1e0513030302030909 78
    0x55100444a5444008003441306201900d040001080d403d0f00076400213003014100e5030140d0402020805c41c00141e442980100107250704650722030384c008100382c041d00051801c00400c1d00701e01c4490002612403644440000c05555844070101d000b5034024007203801d40001d0040740c45d80c46d1400d907410b038801d20078400011f5000c80e001740340d01101e0400360703100012600d400051101400716107405d02e03800f4840540114222500f0400c200c1003107140d98403082c054149005000803100130640650040e50001e100f4004800714108884204035181c4c02c40c1c09041409085078240749248104034a10301503104000240704c01000c0090a4440c04001e5404901c065000c200480c80f99200d0203025800005114005601403011002d600c05001e201501c0e0400f0b80020f4450744004810448880042c4da581509201038800415485002400200003003002000301500e81c3d114000c0501034012118080c3d5500e521810640f100790700f200f040040e009483e031030041c5d03c0b5002000380c580203203d0704000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 562881034 1250 562879784 562879817
    0x40602061509090d0f09091e0b0103060506092206152705040504052e18020a05150d0203040812090c090c0a14040e220b1501121b 57
    0x12503000f40c1e140d50051001840028044c0d034200e6140624100b0310404410003d510a4a4020403a00d840f50a1614141c81c1119014030121002880b0700b81c1014a0010240b00070740b41d0000b25010361508803142003140910032850071540c060003101160450030703e03500090418418200ca040001e082c0c0320300310a00f0a505000146140c040758101d082d55820004218905140d400b440c0c1190052003aa80c1046044010051460400703402d0350b46401d011242440301c000d9440703a07044400d420001e00b004040f50350009038454030b0501403035100c2c614000b0102c90407070540c42100d2602400d04000d64885c502401c00240582166103003110f080365920000341441d0340410705c108880300040030b607041342e290b2070b4180301039400c0300d4082418004140d040070380c1c40309102c0140c0300400c00c00d0b0032601d141c40c00c2500d5461580c810a418132a4032409000341d00060f4516440c546e0042e03d1400030110300b1a1400100c5090401d00b5031a12000d2a20441e1074a1900d428502d0100045940b688103682e11070149 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 562882284 1250 562881034 562881049
    0x6040905011d0304531b01121107020105090d0b01060504030b07050705060c03060a030510023705130306020c010e0c010203070201020307020f01140f0c12040e19060b0406020615 78
    0x15282c03ca0b0451044440d041036003a03c061800300300550a0fa4417120403e25051500782515582215640c3c2500402d00c0f03513078402a10408010b1080e01031003070703509149100109000d0040024140040404c81d0074040d1142102c2e4480c454224810803035075603494001820943c40b0780019194000e1701c1000503180c130302800880b0320443d484801080d542d66030ba6050700c5550000f60195620202500c1d00002040b0b081090040da640400d00069540010355588001c450b0310944001c188140e00986d501d60015aa00c5880644240d0800c1544d0b00500380711003040c120907030402060f0320710214520702c007504158401c035038a02d41c0b54211403802c038120f0010790303980c0200703100203005a0041100800500f40303100141c070340c00303018108100c3d140701003096611709401c840100c50b0490070203e044004a5010003004203005a480c0d2814505401c11300303602c40c141002032501c006c403444100036107103402055200800070890091201e0301e40c3e884481c000c0d1203010a441c0050001c031085031a600a240020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 562883534 1250 562882284 562882349
    0x32a08040f02060c46170d380319150c020321060a0b070203120705030307020c10050409051003140c0102010b0901080a0b070c0203010c03091a01080606040905011d0304 74
    0x24a00107850304ca5480c01a1a40c04c1c441c0350100c030009000c640c030b29164a02a500b4120b00e000b07000c8a0723450f10540a0079000007015080002c400719260350013002d403401714151000418181d0a0325200e40745090800e400c8031070b001000611413420030f41d040c1c0e4a9011026140e51000d0100c5000410285210a01c01c2030742510b4441e4405075043c001c02180144900a1060a202406480c000090a485c000070380d005110207035842c2d0000001c000040340d040c0160140341c1021107550190300e0b40c01c48020b0042c00740303000e80c0341180d80d1000480c01d404103044e242002554400c108040e4266036561030354071005403118690240d800c1c003203070505074944610319a040c0c1c2c494000500c2440d009444010407100c025113540b0521200e501c10b4400b50718203000b25071056002d600d000c40c900c039813480c01d41c50307201200518220144210005212030744022a1158000d9030440f00441d030701c840e40c141640101802901c0310280304060504480400020001d4012580c81e4110109008c018074030f00d400b00340b03d80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 562884784 1250 562883534 562883653
    0x10f0c0203040501050c010917130b0c060a05090c0d05030a1404080c04090c0b0d020310061e0f050412050d0305010f0e0610120507032a08040f02060c 66
    0xb80014440307540f00d4009031645072403100c00401c0903262621030b22070b42e5008202903e108600040c10f0300401c40c415050a00030460742060501d0a00b25104540c3c81c0d40f0090300011845484030b0104104d088204490720799200d0040904085940c0c5241080d660340c054160440407582e86070145900128a006840450324201d003e05420418503003040700821606900300d0384040481c5000c1008400400a005010718520005a480c03c124201492860040d0301000130421031398040c020740d503001000010490f59a00b81041e01502c00d003001d0f6224000c80d0050707180340642407030b0304041c0300f40020895441c5606450802480c0d80303030390f003256400003a4010300c0b0030300304424003190311810003401c1810381500514221152200c0804204241c3d482924044000381c0c94006500714100552402d0611710002008104941040d40015150000040c0090604621780780d010003035444040880b00600500010b83d03400003d4402e201010501a00c00c0004410300c080300c80c03003419084c000c4114444000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 562886034 1250 562884784 562884787
    0x302010f090f061112010306090302060132060c0307290603071413020a0201050a0f0510051e06040602071e0f050f03070b0406031e051b070c03020904080309010f0c0203 74
    0xa0341c607550084d04400c0c041d01810001003007194902c098905255020310312420020031024030740d0030024548003041e0044640c0d01482c4848807411099401542d40b4907181300d100d801c5070071080c4001501b500440c01c1c1d1079114040050b0a41c1080383c941104240b905181c1d10b0b0903860f41c0701104018030000101e40040d003640c0300312018000c03141b02d40701d0b051943e6801408113224200002a900580e0802d03103010025030744030400d000d110107040c005c074060f81c44a0041046680f034240400e150241007846814080c803003200c4060200404400c100c24032010250005a49a54418000390303140000e106d80420161440050460020002d01d40c4080340c1110040426040c203001c00c001d070004460210079814410b8550010701c10310f122001d0002000da5450010302c142154a1102c041240030f0318806050386050200011400c101c40b0544172100d0114010382c880c82c56251880c408401900040d41c030601d030707004220420041c100107600c03e0010030002d10000012000800648102481e150b015820 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 562887284 1250 562886034 562886063
    0x30c0c01062c220614070305071407020102010204050a0e010f060507080702042408030903070b090901120f05070e040303180b04140102041e09060b04030503040b03040812130302010f09 81
    0x140d00c0d400b6604404100b0b1a4101d6843c441903d0081d103810000c1280c003282c54120f040c0c101010481801e0b0b008031541003d000794034140344010a406459030522424030000300306030b400c1da4800d45c147c8006e020044c000c403c20070307180d94900b61104800d1003041501e03d0001004980c05120300242e03480aa1301441007418030700180d00b0040580041c001429209420040b01800703022002d013000c00800704075000e19503a5182800b49420180550808a0184000c010341c5c041078035240ca131141154032031000310074403034101e1801120494540201420601c11000045403007001e110030980241d11a4508000c00c080844480c8500c000669005c0c0440400c3c50009021030003508059600003201030005141c0f90315030130442400d14102c1c040705130240300900709010103415480f541002c1c0c08101c4010f41800d2841e9205070b680d1140b07000c1d0942080000c0301080030080e0560554a080c00c02080d00b482d180717005403100d0710582a100083d0010340c21b240300c01c040b554192060085803078002e1328800c4140c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 562888534 1250 562887284 562887359
    0x130308010b0702130218100203280318030905010306120f03110c040f0911030a15151802130b1c1a03060c040e0a0b0906010c03030b0303030c0c0106 65
    0x81008000344d8008546021140244620f4801020f000e02032420b880d404800d03090900c410b0381411110081913500400c04040c0000d81031008450401e846040c0280e002012941200503204208001c407100702002011810960449042e10a440003079800b0002260380ea822107906400800b0050201c0c140b282000380070038490780c2400c4e0a0034000044078112100c00300403404a54950107299240e6a8400b1060200071102c2038515005400b10000e2507807020a407501600760b1841546401c1c2950341c0c107000510107081180c80d07801030202446541401e03484030207460181d4410300a00c0f010039210071003c034144181406030380340c1911503c51910480c41c0c08130fa0301d00504400b88a18406a010f9100c08865901040510703c00d2105141864a8916220800140c2000940706000240c00d055010000b5200c200106501c00000d1030541d40c1041a42000e400904842c04030b1a00f6010010402c000b0326040c078010b1488840c0d1900811400f0394403100030050300042d20f10000ba10740324525011601 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 562889784 1250 562888534 562888537
    0x3070605040608041b0b09030f0309061b07050a090c0f09060e0103110d0e0706020d0912080702060d0f021c0e0307060207050f01090b0601030501060e090601050a03150b0c06130308010b 81
    0x2072144000d48140351030642c00105c2c803038055105c1842d450380020700e1000390800348807065503c1d0203440150700304002c020008540c0c6c0514001041c4078082c00b4007410100004101c204010031003d080d200c0d40a0f280c1d01c814014022310b004100c041008840300c644aa841035859508945441d510282903a0f1004d00440c045c0102c1360f840035070b5000c02d03c084120000d0608ca0036110454501c01405214546180030741170010081e615801e110990b1010414001c440100c0002c4c3c40c0d100c1075081e985c80c414400907481d805403009000c031144c41c1a800c0441c103a50703540209104028421b200300d41c005000c0002003030305e558090b000d00c250030034010680043c26070b40190041c40d105805032840c45500300348890071550b1040042c1e50240c4401d0a104280d60144100c9024240e9490b19481803103110021802480020302214108000000e0071420a84240d0008585020390072449490344c0c0d8403220316855410804400c0170354016003001c90b558402c2c400c001501c1c03d61684034444245c1c68102084d02c107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 562891034 1250 562889784 562889791
    0x1021308030910031d100204152a020418030c0c0b210702010b150403060b0f0607030c2603041704050d03050d0209300c060d0905070f08060403020c03070605040608 72
    0x80501701c0e83d1810311480500c4a143c4400c0724640042c0c0316132603d00b42207141e0001e02000003e12000105540350708020030400d02c400d400144628230002c2052020800401015440740c548a00b40030592042640c0411404529802108960200c075280d0107414407074401d400e000845003041c10b0140208016501441d40d025a003070000013827146d00b05001c0341400407070010035007841c40c1c00501441003200600c81d583d0880d0b000d490741c01c0c0b0380b1015404901c4070703c550180501480310036001001000307003c10a94003040544c1c12100d5403010000d580710a150002c0d035081320f10b0503100070318a0b614450f04041d90102c0f500182800c20303c3c64191002e5a5a90020b101030603101e07020846661103803611a00700386050070410040005000c4000d0f070840b142c008a9a46109800410501400da9503801c2a16a03651120400044d440c004c1d00c0e0086c9080e21660000180c0c50700030400289000d00802c21500c034074000d400341d0300481c01c03034010941c45e014240a60b5010400c10b0000b88586846510850f61 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 562892284 1250 562891034 562891061
    0x15050d020a080601150f05070b0c07240605120606090606070602040b16051005041101031a1509010f0804030903030c061e0204060908010207080405040509031b0102130803091003 78
    0x1901a11034942d9400e00030240c03c0003082e0140090252509a481020620180024640103050011035030341e0520300701c07019081e070505110103e09d400920142111004005c0072098503008520b85501c1c401001e041144207691045598400d03410342c607400424906e1060304003c15504496503500300700861604890401d0b80c80c56070070721010503c0c402503001402900c050b602c004010f80307040d203000d52800303020410705200700e8200411f00c00003d00d0035100403a802024203000c151220642c02c42c80524444c521010b80c000b44500d803001c02010385c10010b00d100c0c8000c0c2da500032010f0031200d041da518882960024002a41c046040010078450f030040d0b1580c0c1d01c0b40b840401c5200c03c01105d0b510b4984510003151046500040401c101a00481030b10010080c40c00250304102d0759803039010b000d0041e482164061a282c0c000580540003c0c01110310550b40c90302003401201030b20074030342d000390000c05c3d0703100303812400d0180403400500000c103841a414000304811000444001d0031000303000e401001c2e02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 562893534 1250 562892284 562892299
    0x30412030c0507140a151a0603070225141509060315040e1e010b0906190305060c04050a0905090a0f0201110706080f0105010c020303040e15130c0f0315050d02 70
    0x20006010207804031400c0b41013100034400401681003145500e03400140a0803a10301d00001c041041101c0b10b142e0fa4002411138107107031030f9a40d2000c02e904002464040301080006400c5d0041e8035030018074814103030303a522081d6003800b480550038080f2401030750580c201d056070184100301031850100003c5501010400c0e1000741816140c004c0f500382e500f81e006451094000c0c6012002a0150740010f9107440c01d00d20080c0708614240d00460145540940785034081d0003122a000146034040b910b001c001e42d031003011241c0c40c2c50f1030100c0e038249070800d0040f14800c0c100c4000014170000d583c05010700548002c405480032002603681c443c001207100380128144040f45074a2222683c1c00c0c440440100500d4860040c58902410800203960341600309505200d0515120000351710b0010a940556a4000049405491f1030300024a000000c1e0413071a030002c407080c42e8610500450b04242811451501c415003031015202d026010b850683c81c80740070311050b1000400203842c103d1a2203080500251201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 562894784 1250 562893534 562893547
    0x90d020312042102100e070f03030c0819020a0311030406080708090f0706020c030f1c120b10030903020c0901140f1c11180f040b09100e16050402030412030c05 70
    0x4003e00300440c18040b0268214442c484108802c9014250840900201820044e0308200145000c1ca005000c0602040041d42402003004140e90417520445030942080c48000034045000703544142600080340050500490701c00740c24400400d032800d807036264035050032580c5da0440450301c0c000010000c1880748100262200c01c1002440000d001c0c2a07180d000d0032460714448241890200204142240c1d54440c500c1c40e0041e800302c81c50401e911041d441d09503c2c208034003080701c0150880310b5800c0c3c0d114a40110800e81e4a4140c2c1c0300210f50780c46a0240e45a010141c010030022603030034403990a40980700780209200d49408180f0b28602280240110710408402c804000041c003080d030200c48410100103600410f00c4c0c50f82e5005030184411146811a00e030030b805942d9029005400109060009408903c100d401803142541b0081e01c2d2004001041d580181d807a61344100e032800501c03150324448082541d0400380200d82c8125086840c802c00002003407002c400800612070004100b00f8180503c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 562896034 1250 562894784 562894823
    0x14030c0d0509060604151211120601060e090a0c09031106070b0c130806070e01030f23071409150904021e0304060f0209010c1b090606050c06090d02031204 68
    0x403140542c1014008001c5071070303c40709210440300c5441142c4c044691003a402c0103140e00324080307030f014a0351100480030810032180225a9101c103103070729510140244400440d490f507220105051182c0211810070140e203aa0750b450342210840e2030f845002421004040c8046440c151990b92517031805010a071914280c0c0c3c41da58003001d815100100700390400142d040445a00d1500c11026000c030704040c203003d041211000d4100780005080d20706058484030062100c400e154002d10305150060411028540c0721403030844040011520840424080c1140081c1800c8a10a8486000003c0d00000e00110300641804103504090b80040c1c1c4030303070200803540350451820140100032201b00d07031160b100d04091903c1c0080d6045040151440c030703c10b00091030540e900124217104c003504403402e240b00341d2290721400307400e204a400503030050b0700708040010301a5100000b016081011000d84645480f409000d94030f807550801c01c140164000d010100c4640d20141c81c3c1c80d082481009418a0408031012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 562897284 1250 562896034 562896041
    0xd02010c11150f1b030901050a0305090703020d0602070614220c05040c09030303050708071d180c04140a0602060f0a0609230f04050d140913090c0902070314030c0d 72
    0x10740b00c3c80001041140c0c030304103003400034481e84000c2c201035801e0060038400208603010780c1d0059801c040c0c65101082d140c00088c44440003079900a06031210605240c207000019600400f02100c03014603010201030312603201040d01d030140f800e1041c200c1440741c40820207c006a08100141d80c4845c1860000070603503164402c2c1c404041050f00c0d0441040d14604001d022143c000b050707e4203000003c0101310725160b2040e40c601c61001194908041d05800d600030408000000300703400c0c075051315041440640c281c0307040a0300803140c032404160f10301c90640c4144a0241410706c2900301682c02071000c10482d2007200c40c3c066000c10705410000c0d59940d1101d02030244d0703043d8485220924041d00300c48582d03904c54018241d104140b40b068644504156498030b5035004601003440400c103020300c9403a260400142150f4000703074010120703504011aa0808402810702c91001c41d2951101d820024506400e4000da814140c1c01d901c07440046881c819041c40383da4802028511400d83c10000c6841a031200d01c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 562898534 1250 562897284 562897297
    0xd0509160609141c020d0303020c0d020a0503030606031b0406210516080c0906070507050f0d0804060c031103030709090b03211305030a050c0108060d02010c1115 71
    0x1000380038158030002801240c15250300030300304014291106001960740b48508490038030b82507034802400c50ba211800030301d902c000709000303511100d50781d01c0c2000e1603416000f81c406190060203a40071a018a01c060743e844801d9100240150001d01c000b030101c1c90a100030350380c0440c2840701a820600c2e500c115254a42c042d80104d8089500040907481d04c060010240c9400c0101c00c004101e0b40c2003030141d40004d0410100d0320402c029020000034000000d51040d6010b07604003804880d1103032254500b117074031190b40303000b0b00307014455002985000c0e20b002c20341010240e4000b080b4514080c281001113031503142420703044c3c05001e0700c14140c1181800070002144100c03403da4626528504000788203040e1144104080d1007030b0310968404981c0380409520704414005d13000050342e02d00180c2c10558860750030b544455854044c1c401d61506022002c101065040c001742e940181a50390700d010040206091000640020701c69035440000460069130154400070040018000b0071001c03448901a91044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 562899784 1250 562898534 562898551
    0x10605030a0605091504051b1b0f0601031a281b091a091c080304030e0108010b0d0203090c0301050112031107062109050105041112070510140d05 64
    0x2048a8560240b250401526048405055a042ca419910604060410074520960703481c0c1c08100b218800c036512440b20308112003100c3e26080c52551880301001c455130105a240943c0e00c401074001004950141600e40c4606032825620742e02c4a600000f4000404010100c0188080804511409440c40400f21603404004c1380d40884031005440302038084400c03005111b4241020b2042a007410a06810b0161220046868a80341c50010302daa074003602036401d40a101180007014405036100552045e4044e4943c14403a0b003a10004403100d800034030a00c048400c05000c1640051002e0f0005d42e08141c41d90107c849242c482000642121030030784c000c1803195415400002056003103070000401d8600d50001e409414902440501456044007450303030218410310b20544000b80c4d681c0820995600800202711501d010b141084480e041c04800603c01c10580a80c0b00d00a000052004140d810241243d00000c940d54420f0300d521584040c03010032541c05002000b81022648501803150418 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 562901034 1250 562899784 562899787
    0x6050c010e0a0c08160608060d0201020c09040c29090f04090611030709052d030307120e0f03010902010c0209060402040e0a0b0103050c130b03180313050a050d0309030602090604080303010605 84
    0xc00c407480345010a10001d0556200c0c45c40d004121660b04868042e920031001c3e5801240b6030310910040f8140507045003101d6005810030144414807195680090603260f1242c600f1109966546110b000054140f504260002080004c90101e081c080d80070000014080c2c03000c2101e8000303030b9070101510382800c40212031490110411141c5a40b083c1284c005080644005c4180300800d44451a1455984511041d6070010091201d042d00e0420440e000b081d004141c0c1d8485e002c00150091074a4050750050748250304000c80394a552506220f003aa02a505844a101805140e42844812200100034a511a90070b210005050000c2c0d0500b03846441c600000040e0680704034000740c200c44c030141501080a20500c50f08005183e03440800e415070743d001030b81945a030ba40170b141400900b80604103c2c3c56000104203030000001d140d85c403000b0707107904840824078182c58005029251584902c040c0000d40034200400c0455820307030040008640145c03e0b20301d8140c445040ca851070f8405e03803001c40040c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 562902284 1250 562901034 562901039
    0xc0d20030a1a010309110402090105070212010501060207060e1f1202161703010f030f0501020f0409091520030603030f070c06080a020f0a0e121608010e030c0706050c010e0a0c 77
    0x1000c0041e070341c0c40b04003402e04000d01400c03900c60040c860064091140600e600040d00740050b80030f0750603112400d44c020041680c00015516560190a0a10520016218909010450038002c411120380030102800f100880204032401441c043c2040307151006000744480032020760744041c00200440d12088440401e64201482c0c600d0041b014401d1120204206000511002140e542c80d80102c0b40c02084107003400d406d42c2003250080c42400000c80060200007800900c40b4110b40042104500401d4071945540303042c2e04103403e50b810411402c05180007445800c0f400c14910014541240010342200d00b000700c2d40e2601401c0368401501a50745584401003000070550010f075403680702c07000450550400058141e140814041c4121000610000301405151a20b5030704400c0f607151034500440b05a82d2840320000c84602e040e004150155086c0000520303052800011113205403542070040c13074030303c2c5000b10480e010340001100c0f075181d5413260300d100a01c0c50308004a220407070203080485003940c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 562903534 1250 562902284 562902311
    0x1514010e0402100c050309180f1501050415050903060a15060201021e0703030f0504030e0102150103110906130218010915080a0f090f0b0a0605090c0d20030a 69
    0x5016448403028280342010803006898000304840040124101550f1211640c6040da00394041e00c840c40b504030300124030b205003100c031541c00180a0302540280e040c90761507410440c1d54000c528002d50740400c20401c0700300b06001400c050899414901d1411504150487c00002c2c18080c081c1d0f4200b80c0b040c0c484905081e94071450700d1038001800ca0740021482c1c2044a0b41c1080300c5c0c88103200c00404990045a0310302814040e800c03070001440070380000c002c54076180c41c0140c0a080d80b0000300d40103104e14489680c0031304196003054181c030b4003c103c004001d280c0354104280301400401598200f0304031115801080c42e140041d1240c0d013142c19002500b01000c1c000100600030f103510a802c1c5071220a403080115402950084d04404400c401145403203078048000081c00c24040020b194071402d18442e414081910056400783c2403201c01486943d60307520404c08941e07000e89070a102c1c01c004105003048010380d0740c8042540600559080c2501084809a4442c0e4000f00c458411403600c40c3c0b00f035202c01d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 562904784 1250 562903534 562903571
    0x607060506031903120c030f020c0709240506030912300106080f0a1b030f050108010516030504021f0e011116090905120a05040f0801231315 62
    0x4a0b500260a441c0e0a0b080d1002850105c480c1d201440c02940c4d40200c101c62803003508034020107202040c0c255030310300000b41119a5000d00d881400754031480c0141441c8805801030800150041549020032040d0a06081114550016002d03690324480c0c4410389034895a100c6c041c1491004403000c444d4031000101d00030b000418013440c0300450b2405c0d60014840d1503000507540e03800ca030a000c41d900c0e190740ca02d4040341c010805945824140c0c0108048101c1075503050700031544421105006108a03681e5000342c500781c8809503007149006956034180d50090b4402d5000c1c42e44540000c0100b5a8004c0034044144210014141a07001400c448213000c000c0d42c20039038a162200031200203100d81c8070000501401c800181c064280d4640c0c8800e40101070000400c03a88030711030385025001c0d40e43e16070b040000c0e00c5684244640301c00803012102c0041c5140c07040c80b43c0854005602c1918841c0c039004c440324003c4040040642410786100c0c00100d0103d1070207400580340002c0040000b0b0301151604604501 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 562906034 1250 562904784 562904803
    0x20904110c0615010c03030903020c120d140406090614070206030a050405010b0307081f0f02120402010f0e030303061302120a0f0e0c060406050a0908160314011a09090c060706050603 80
    0x100c40b0b94050f9010942d9024041c0100a601841e0000e1280b900307241c00c0307040c0311984070380f1a40050400c2e003003d01d60101103000c440c558039513182e00c038001d6013a0f40070401da4043d42c401c6c58041010544c041154500901c2c524141d1050040620700d80316255002841c160070540d84004803070f50350700411041110900c64002000c1d821401865100c4c60072100560316480711260074a907440011102c801c4100580000000c20b00051047d5102c44101c20200710342c3c80200c13002c1e070020311407003c0820700c68000c0284881d0404060061461a07560078180300340e0400c240c0444070032950802020711500b8100241034040d146811000c01e0f0010401015800da5508000c50364031600041118006962543c046504640b040d00304252034507080c1005a48140a43c0c0c801001030286207039282c006044005020282c1e84a00b543e40d40d140c00f024004d9003280c1342c82e20704100d071000302080301d030b042c1c58091030407a8415400c1041300c4001c070380c000226059800c07480b07040f145c140d200d070107028080c80e0602c0321001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 562907284 1250 562906034 562906051
    0x91f0501090f360618050c0109030c06051813150b040e04020910030b010b09040c05030c031314070617090d122307210b10030f020904110c06 62
    0x407031000c0162120040324100b0208002101c0d01150f01241d040b0480c1c0b96115401a0080110488404104084000f0100c089450b405804d049101640c0075002d04d00590b50840b0049108030301704101a80c0b00da01c0b403901798013040a2101d0b040501e82e10030b4418181107103082c40c0448c03203807000350294902103140c1d04a980764450a010070301139050f55008541e03000d90100c601c400d83d602e690301d00c410081d0494002502c190200310000c64451319404c010705608030107580c10030504804900446040c01300741c54200361b01204001144c84545100707120007000d070260100445104180d0341c031a1510116a0051001c40d2811044d81d101d0040180c850340e00951a002809942c0c88150004260b29441c080800308a40c0c1e87d59030207450900107406a48d030140118030500ad50422140203030a16180c0d450420800003e10384031480850680a603441e101c0024001315900da104c404160080d000301011689116400e0100782c00c9542d690280050080b200302c607003551008010b00c56424a01e00821610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 562908534 1250 562907284 562907291
    0x20c030102090f06090604030501290f0d02130f05010603240302010813150204030f02091b041206151401140703080411060c0618010e0a0507060503091f0501090f 71
    0x2402501c601d103003d0310220f0110f8810303686070100e90008809000340e0304090100c0d842c01504d550032140c607010880740030b00b22880d50b0303030f4445149041080d000c03130348103110b50089424044a001401c0035041c0d87c1d80108121030114240009000d42c0c0d007181c2c026800030001907192240890007007a9107010000031011030f500802d010f42550006045a10050f0a074400c40c03640448886c10f1000d8000c4100d280259aa03065540e02e0340d03400d20301c0300d0b002a580240d10030241280401e46a07420304040080c0c141c0980c11180c00c2c181f42072140c0655000440003903070b9a64a99900061001640a148005d048598500d6071043c01c0400014501d00d140040244007950400c450008a9000000158440c0d0b101d10074511340f1244c5008a0014000c941d2442000c2c82060140b003120302444000442c0b504002000300040c0111460859803450500c03009801900100340601c59140700380011a40a20000112820920400c0c0240c8a0f160000b1b900c150041ea50b40040c405100103001c2c041c0120b080880c1803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 562909784 1250 562908534 562908547
    0x40216020d21090b030606280509041b170606070b010e041416120c0308030a09120c1e03170405010c02100605180702070515131a0d05040201020304150f020c030102 72
    0x5600c0d01c0081d001c42d218103000300d0401e1000700d80d014403000d4412311555440d0b07003865142c40a44242c0240342510704c120304201110705d0041543e0b41d42c005c00f0078547e441e0b003c0c02e01d0b4002d00c1000044050171550b00220108040d03408070340040b401c54020a00192402c100d8030781424030642003882c07584244095085100c0759003604480c1c0124800f51443c803442492480c20a1401042c1482c0c2540018076142010081116011103903202850183c001d00803885169868042102c201000304001480300c0360255120505000e00a80089114400d003030000017040c3c002c411241d007240468086925139118250ba41c511903040c014204880e100080902c461130500f00010b8840543d000e180d40e040458030006524544200950f00044c1406450810194484006005540c0c0201000d03202c17071840610004069804401e0f01c6481d8005001c0a8180340c0c59120040c003528010b4410707411032009000101d050045921440b20b00086a260303180140c0000e40c0290810640e00b10b003a100f44d1050015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 562911034 1250 562909784 562909799
    0x20a08011a0d0f05040c090c0207090e0a080408030712030504030804020405041a1e1608060907030e03120a140123030f010606050705060f0411040216020d2109 70
    0x806040d40e45a852090507095441c1924500340103803081c00850506001c4120000c40c815801980201e00610b5141c2000f074032141c040f816074910b01d80140040e4010340c02001610400e601c4031445400d040140c4409070180d88800d4a20b0700503412011554000051520400000301604000302800c2d040c127000a2415440203084040024006406180c80d0000641003126a0f071070020400140125040b540c10461018084500754500d0400d43c80c0728680412191150040582c4032046140c4d03030b456041c0e44080c04d2141d4000c0c0603100006064507140d404503441c2e41800580070050500d801840c0703d1a0035241081030383d01011807580303161550401440705081d80303240c0181c94022014611189082e000100e40ba00441042c10105540381030808115107070322400a01109000710300701e030200e86030301c50320490307c6005940040a90741c0441824080d818030f50041c1100c1440c18040400c00849030700070618508000c13504072503401e103828a21100c601d5900d8444402942c42ca0420b10340e50a1104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 562912284 1250 562911034 562911047
    0xf050a0e0105100804021207030c081005090d030222060302030a050c391507030b01052d16050a1e0c050d2301051b120708070504051002031b01020a 65
    0x1143c410030200d440001d0641d15448007640d5100c840c001110342072035030fa0030400503034491760007151004d01074243c4c0d116074510103008207802000d80c2006040309103007010003a40203500058103441860b130403036076124152083d031040b03a0090000d03032005682c900e0700502e8a0704031b81c0c008180c0c102100f0140b05010142d0300700c0312421078009148010f0140b00030040501030041440a01c041810301c280641b80d10118101c075203950045009807024000e016614005403881e0007106502040c0300580a1400c0718115003914920080c00d00e04001c40c40e111121540c292001c1110b1030507103c40d0f105200800401500d89001c52040c0c1a84442c141c64590300d0341e400816121138400d951003450260b03072107001c0c00700d090350000000d50140c607880e00da0382036510580d0207410120340c860481c03c07265510b10000003c420494042c0c40d41d511405c3c9082d9a0780ca0140d844241c00781c5070604101050102280b0358661512113106d0703070303810307001191184101441100b90009a40c1d4003003607a401804118a40f40d041031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 562913534 1250 562912284 562912309
    0x10b04090503120606130303031a040603020114030406060e010303020f06010b1606020903010612051606021906151502011a18040b0a1407091401020610120212070f050a0e0105 77
    0x100c2e015162180051705500401c01c14001d00e00f0800c100004068055118200254081400709030719010a001c0004a9800344170282c0400d924248026020886a0056a015111b92000a81700352240c5d80383c810050260404c034050f90113104100c00031403007002450b005260f00104a440c021a031454040c808019541c010281900851f81390b4040d54203410590141c0108443c400b0780100d54100603a0343c0c100c0da1030760440341c44800004135489101240303a401c48840040080c2a5141c0d583d9240c000f095102400700c040c800060700403502c031030020304844001181768008214000307030a032160144504500c005101e0540350355a56030701e8010a008030751068201125141070381d030f070a4081010f000c81d51640f4140ca0007038810030481c1c40d041105201511300804084004028480040e03070b45d1107060700d21801c0d0701c020000c02c004200c0d000503100c0e8840c1c40501400c0905044601c4186002140d801002c1e540700d2807101880070b8100111403c005005584200b03400f949048003080a4030310700d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 562914784 1250 562913534 562913557
    0x351e100605070f0501050a02040e0a050601020c1c0215180d150509070b070605010e0105030604050604110a1d0609060d080904091109041208070203120c0c120f0705010b04090503 78
    0x2c00c980d42400000030010001c9a04013000f84114645080c0300f1000354020f008d810810540135001c07548003549407040c58441c89040c0c00400c0c03408641c1c405c01a030001c2070718a02203038510b520174400060311181012803202215041042d25901c4250083c56400040b00d07070075010320510295540401c0b2055100c40e070001c51140d00041c1601c0c1c1c80402410800c0365008040120000181d000401015500480c101d44011070707100c0c01030342c0398800c140d00c4041c00d40e00038006a0105000c9000714000300d200310a03036080101400141a41c03140d459100799111340300c03003010070069420801b240c00d22005c02e6500c032100302ea2302e81d1601010359400c89280110b8100c14095541c0e03080d5082046014050304501a40040c1090080e2402d031403d00620020100c287d00090141da0118000c18000410380e2083ca0700f450901a5968800300840100d40003101c070440c0394459003040383c044a403030b034008100d601c80082000d90b0b140c0031420143c0c251240d44000c00e0040c0c0c81e15800a012a001105450110402d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 562916034 1250 562914784 562914787
    0x4030f0503040503060c0904150b0315040e0f06041106070c0308180a030f0303141006030905030d02070b180d090b09180112060b0301020712351e100605 67
    0x24100645140541e07040f00f509171003194188800b041d000d0000e0940e50000701c4080c4a103198100a9181d841c1d811321030211900d0084c00409d08019a04180450f00b100242001031245200021036183c6110b0b121900b6864020714280020b00241075205415101c095503981d15208166032150708070710039440080c210010119134041d90581e81e4403280400000100100c03241a268280301600e54513000003100070901e49100c142d0007500f140b41003407048880782d4a0412035413070140142e02403c03d5401c00c4800380020002042e41c1c0307419102401d40c460107164000e815140c051102c20811110302542c1c041d84d40a134007602c0350340780c5c480c1c10601a60066190182c441c406803000c14691000e481603003840300340314400403520001c5200850710203401075401340320423483c1c90b061600705d104040010789000310500c4424144d901413451182d95000146200c0d580c40714401d00000c601c00d00d8000500d019214030244010641c403000b2102501208800d000750340d0070814280c03030410f2101d02c611020f0100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 562917284 1250 562916034 562916063
    0x4080912070b030a020a110a0203101112090319020f0304090c11010c020f0106061106060402130b0f0a0e330c0709022206020a02010c0c180c08130203030403 69
    0x105000100041101010756503d9040c03418981000c1e400505121001030898445815090000140003020740d4018018004030383c01e0042200c090020020301e4035140c0d80400544040e0030a05072658829000700b000355880c0c079070559004a42c0120b001c40482190311540240c041107001008580c1255404040068121840d44050380d081c01000a1000c07554030b000785280c207440d000f06054121002c0346008001c0b9540b21582511004451a001c84075540712400051942c1011741c024002c0c01b0802c40c843c10f2559031284a100c10b0f034090300a1803507108011400705007840c1c015400041072241158444480c18100741c4d4a8050881450403403003c1c040380391800410750b02c10341180d200d212000e00340d940068807084058007a610242e800c1b07202080d069000c803a001150b02c40b450a0310b41580c040d1510352030503001152070600d030742e00c00c1d207044045e02400141542c40c5500790b24500c03200c041c0480c08050440014200450050003006010020000c001c0165004000c07107090304e902081d086412003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 562918534 1250 562917284 562917319
    0x10b01140304150f0b041b08100b1e160f1509020603040f1502040f050909010608030f0a0201020d0f05041a0714131d1f050a0b0a020109080d0f05090303040809 70
    0x42846900b501300340b034800000300c0c1c11908908940310b081f0729210090700e41c0300d100c14000f859203140300c1c0c0700f060750b0705001414003506a98150b030451002000d07024100390202070001d1405409203001c9070606da020083c5000c00101c0003950301c00840401d030800510300590045a0688002400140020040c103d00f800b00005c1e808030481044985608540307460700c48201404040c420f02826202d881c3d1080001c3d4101014003a61056982c4c500285082820f16200c509003a0031052200701595003c0c00a2501781d40c00348540001089403420114040c186414840401200b910315035803481080001c0094850304101d1a19910440020240c0e0701c40c5200320201002c5402d420a41e20300c0800090940d1516140411a001d00e5400c2d1441e0310061090041143c420b01034810709801011381d0300100006c4038010040c1c19407045a00020890300c2d9247d45800d0103600c122a0640f20725a20300f25010b020300c0074840d183e40300010350011071850170580c4901d103840c0108050710344507000d06c00039020410b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 562919784 1250 562918534 562918541
    0x6010e13061809020f04050402030730080a1d100f2f0d0c03020d12020c060106080a060f0f140a090c031a010206070906030f0e0609010b01140304150f 66
    0x500301c1c40202c1c41c01e24101201e640103404500001c0c0c2c413640300848108043d2030301e4422940203641c014000e082140c542242e00740c00308241560b1400c40003030480c2d45010a0303102d2008140c007903ca00c244036511043c6580191034403000d156115100c44041895003015111f44100b81e030051564244101200f014280884070200415202d05007a00c41e00c0e24400c07580113256516140135010020f0f03600f10841810b045451410002002e80103a0210940852082c02100c06079000a00a20050310303003c110b002d20f601c1d003102a400342001425103420025040382030300c039080181021800e0ba2290030f10b8002c103030003407074050b020301c0142e00d00440e54048203940e0703103007680010200d001d4148031581500002030000d0188044516a25503494a420602c0d84003003402442030400d5210fa141d140e0500740d046000b480c980040c4034004e030360b4080f100224542084454455040000045801c1c01d0a6000500000300b8500c40c07900e80c10240b003070000150310780103400c403030a58024000070f404c2442e40c40900035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 562921034 1250 562919784 562919789
    0x306180a0804030b1e130201050912010905150705040320041b050a090f050105120403200f011b1b0c0b0f0304210c030c020307030b0f0f010e06010e1306 67
    0x400740001000410401410085485840108520040d41080b202501050390048035044551681100780000660050b00a00315109000e4030347d1481c20148861503003103421040090343c90b68859050409020348200d603a50340300d0b01da451b06508103880c41e500c0803410100c0f03e45021805440310266283d60726070307501003880d280350582418010003075444041c14584c04040c8420002d14400702c0840c4540c0350480140c01c0346e9042e52024540310340b10140640081e4040c10071410402507104a0700e4034032002514060480140000c0c002090907002502c0c2120380103104890700062101003052441d40001c0325a112001d1650078400d5014503150144541d0081e41110b0b1110101041d0841c072904004042e500c51807041c0659440b00d851203054184411104140700000382001644100080c466084040510b00c007904503107089407603642c0d1914891040b11030b1000c03031818000700301e400307221070f90890700424109058401c4c03400d1244c002000c0c42e60070f1001c1400740b640c4003407401c0100000d900c40b000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 562922284 1250 562921034 562921043
    0x2109030702060301180b0409080a0c02010903080a0f030b0405041101270b07020f090906150f04050f160e0f1002031c061415071b0e0c030a050f060306180a 68
    0x43d40c4d0f845058000c0c540c05415002c0c0b59075441d11100c04220b0030a8070800c03d250790460203081c1014146501220b540d401030800320f040200c03003800007002521510251130305111640300d29156000095005045400c5202e15510481c00c180500010440030480e84c1402071081c40c008001c4000c07050342d840c4d0340d030346140786680e00c5110000000b44900e00d5000b8000152080318000280d04001c000c008c0003450503510341c0102d030040400b10301d030309400039000403078001c000c1c01118042810100103030490b0b10442340315030816108010001d0106070030440940800c5a424074581e203161070303008583d44048210605001d4040c1c60700d015003060081095900044812070b0b061054890403e00b403000c3c0046200d014078000e81842d0003460b038a0b00e1b4081e070a40c004000200d40c100211038541c028003d00144400181d499820070215000800f521128880c6801183c03a0365070341401d228200c01c40d4002008500550300e40c1c0140542c640d80810860741120400e4440399801000c5007419007400740e42500180b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 562923534 1250 562922284 562922287
    0x1201060206040c080102070b01060f0c0206070c050f030307050c0f010e031c020d05160602130b07030804050c0f0906040b1c0303060f06091212031d0102130b210903070206 75
    0x400039400900544a0707449000b10110041c0d41c0c480c0d01d4240d0040e0040100740001e41d40051103624031907040303441c20303c426241078403036032102c0e80100d54213a00c412000c0c0d8024006200c2401107003461120703c3e0001205500541c86c01140d502d403162555511031506104007a540c00ba00e903641c2c41400d240380e695900400303444a03c002451665211640b55000402501600f0601d01301c071801842070310b00d4501c03034180c10b21110703410355140d40c0298880d041403504d6190700d01c0c020400c841d190028040c01d46c8a034459180c0d5003800c1c101145402c0300381010074031550341a402200309481e241034040d000b45c81644e010803580981c2000900381043d404610510140b003842800925a00d908000100c410b10b0364004903064440c10100c51a0309070307000d180010b0b029401002c0c0005c1c481d41c40e5091107920391400080c02c0001c44514940d030071812540007210386d00484c5030b6141402c2c400155000300280e4008914101058089409880210380410940d01c030700b4000501d800710900c1150300c0542d0080041d0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 562924784 1250 562923534 562923539
    0x60f2703090405060109080a02090a0603050d1119020a0506030402040902030d02030901031a0306010b0d1503080d0b03010510120507030f0b011a0301060c150e0f062e030809061201 79
    0x1035035a820403a00340c1d21680c2070001044540d40a00c00f41010f641650014052030f10307543e02486201c200241c0000b0445944250010109006205080700c1c0c00c8541d481c0410b0b01c0c4d0311034400f4541044050851603000a00c0d0442e4010b0303403210742800403940b00ba6115610b954850000400a0480740707000f1707406001e401c50381400294040010f091001e000d0300c0800c10649483c85181c10a1035100745980c00d0751052005014951040000c0c0030000c3d080c0e2400315080401c41e5180b10164844d6101701c8002d900030030584441c400c0d90007200d24041058000b04000d24101380e21410700c8c00a482820130b604140c800c446c00744801485018042e50b04840d03004a0244540780c100c4074030209116010016420248944024185004890413526580c1d1940003041954031001100c060740010041c1e0140d07070740004034207d1002d02110b009510f170b034000f46c0402c1c540010320550714400404100c26000011800584003109482540d05680d080854a171701c070005080442c07104e202e030882e0b01c284542d203130000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 562926034 1250 562924784 562924861
    0x8010b04060e060d020103020f21100e10050f0406080111030f0601021209040b010903050f07090b030c0604030f2a03060c170f0702100222140102060f 66
    0x124a04401654200115035841d9480d640603142618102c1e80800000071150240d0320940141000d5010a0b071a146010709403100c1111940c1034603c0114800390700e40800400c1024115140010154880e401c01a0302c0e000c001f103003051295004980c4500c0000d0007401c000c0d207442d800341d0054000040208280342420502018581013102d54024003001000014110b510120306400c540d606250490306164891003088084c001104099040090035200000817560030440a8010729800c0080c0101c20704002103c415030740d451038290702a0340a165000100d484920442d000c4a8006078040c0c00c042c030074a8122818170f10524a222040c00300040c138054240c2041d1032404903881400d04114940c0c004500303541c464002c101d903e2009540300005118a000342c1c0c16160b00901510580b11340001cbd0000200403600880c41001014403092440c41c9054000c110090107045c00348050f00e01003080e41d000075a911302c0200740707985028011001c034070000200110202c50388002005100040c1d002201f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 562927284 1250 562926034 562926041
    0x212391801090303090605280507110f0604030f06060801020307050c070e1b09040905010c020a051506030303070f020a150507080703090c090903050f070f02032506030f0b0405010801 80
    0x1030044040300000300d40c036510342c09806402c007120381c103484100302d40d490a030b400d40c1c0e02c2d00040201c0d601c14128440d10f039035074161100c00050001c0d0f5a1111900c40180b0704201e40b44441202103540907070441c1801c03094540d0b4003c265001c880c0e000c41106d528003401c1c5051809013600758070261166001000f070000d0140c20a02a0008405403002c840c062642c0f4011403107000d5085c0d607088261520f02650310010400030300105a06200540041250b001d950340c2c250854020042031801600a08210401c004003400503001450f041000610030341801c1e000240c8922000d0540700900c030321000504500c900078011224860740140b802000030b9540e0700140060041102c00400040034103000444003402446000240c0d6040b0000c03a50b850b042c82054002844440c90030b506001d814049081c20b06500002008260722400c03031400340c0c07211032041c1071410203803010178103c11a8400601c03a0501c84001d01804481c40c1d4900800c0351400c03030840f6030061103400f001e01c1c0c000b8200000401c0300e03501500b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 562928534 1250 562927284 562927297
    0x10602060901050c030a180c03031d041a0f01021c0807030608190b10050d081b06070c02150c010510050a0504090507052b030f02060703021239 63
    0x2000c0e40c000d5079965882600701c07002142e012100c1030303003800410188420355200038504010307066101b450b05031940b6010080101c03648110002008005941402c440820710a4031042094a081c0200c6030071149048030400e003000701f54080c1540d02800c41c016842004150722141e1050112844282041001400742c0002c0f5480300c0401c2c20142c0c0007400e140e000801c1c01e5508045041c0d000303601015039a1100d041f4028101d64001c00c03607050041207d513610030075021010b00c036803540c6540301000d0745511460140c103404449039402803030800c041c0b540c020040e010316960441c1c4c800d4204500b0040c0000a01a0405a460703a6103004200421054011180801c0d54802c45290004ca40e4400800c0300ba18482c15008126402102c010402810000f4a03508002901c590030700c4c0488081d000e130b11026001300d406400080c140380f05e4441181d014060150492000e10303095180c1400c0713003154500f816002d400801032000100c1c3c43c10750f8414140c0400900790480c418001e800303c01088590706038010b070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 562929784 1250 562928534 562928537
    0x41a0603180606010c12080424020c06010806060d060e030f12060f060913152117070b070c050c090702010b1305010e0f090c19140f0915040905010c02060106 69
    0xb040070409560061036183c4469501200200303440e00f13035480403101c0c100041c00459030359030754a0303249082d1100114141c024100542c00141c5400c001e0b50b1a5140c000183d000e000d280d005942030041c19168072401e2035103280c10103030100350307009086405480c44c800c25040264074800861100780c11702d00d000d2020b0250804035001504408503c04108181c0701c1d16041da64800c103003400c80001660190031110814802400c4d151030290b0f15028100c00e080c0018015000e10000c0c60250100704101c0c40c1c2070285242480c10030300f8488540e560010309a8094081c6007400554418441001420812103090610207040707980c031424400f602a001e01041e20703803a480f968807007090021910081c41030340c0c121001840c04141c59107a44c0900c100c1003001810b07038015802207103011040398850a20210900360b24100240f1824138042c4000451826040031500c070700c04241c880c000c103680e80b0009030341201003041c0a1003d03100840000e4020200da1038001c00d90350038000c620020f60340101e4828100d0350746 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 562931034 1250 562929784 562929793
    0x40509011a040b12072904030201020a0807240c0212090a050d1406041a060d210c020a0b090102060f010e040b0c040e0a0605030106090e0c041a060318 66
    0x916184038280e60191031680341c02441c1034480069850140c120101415002d0302100142c00104002400c141e180c1d007000c010174000604840d4207650000e1040c07000640004054109410350f40000c1d180d1030a040c0280c6003a07800310344603081c05004240c0c160854088480f850179032010361088800b801c5061552000f5000e1040c8804a03c008001102c0005000a200030b075254105410000d10600e864801d803026540114416040320080142e40c4c01030b07000b00360044501e120784041c41c030014802440346019030600324801d00014007203464184003100800da68807411403682e00032030300800304290180d80090520400540303100050014101d403a801e900740e80c116601d101040c54200f00230310542900700d031074034001804106c081400540040400e9001450705580c0c040c131301f0350314405944880306165501c0e801c0045240134840c0d14001e1142080901c183c42c801010b55403a1141e01041e103008607103412001503444060704800705051801402903849040c0620340c03c17520340442c00384031680d00c039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 562932284 1250 562931034 562931041
    0x20d020c07140a050117072c0a1502030a030506120106030b0603060a02040305031801020c0d0b0702060f0702030a0806040f020c06040311070308030c0d060512030904201b0304031208060405 83
    0x3441c0a01c50f050307440684035281034114640c4607071200da000030700c210100f04500f5461740d8402801c1030188450104800c1240540c1d024408114111000340e0101c0710012a0004016906401000303440c2031215500b03002400c2c1e0344d020302052007920002c60080c0654601580401041203894006001351026012078010f551840c000c0000c9201e1800050704a41c0148602c1c44566800503450701c03c0c0c401032040d1a540d000f14008184c8002d01c1000841c0d4203a102003c010409030b0401a0b15881003403d504684941060803010b0b4403403086a5151040003800000101a0780b9030f504021205507080004560762060800c0d069110402034804034005501c0c500783d4174402d000000c6660989400510003032071901ca40f4120501c0307034801c1c8040000c030340e00c64a00252a507280d8142c01821241607014603618032205040204640c0c0f0200100000e88000c840031400c100324505940c4454441444c1d00204008207502501d180640d40c40200003240c20110300310030940c8104024000c1100303850902c100e44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 562933534 1250 562932284 562932289
    0xc15140a0209060f130f150201050916090b1f0809070f0303091401030b13020d0b091e19020d0209040b04020c06040303051f170c010c15050a020d020c0714 68
    0x850030709090f50201081c40482c14a01c115030082194100c040a200c14696490805207910a40340c3c0c0801c1c0d0114058003600c1d6280d40a0058646c02021140034100c010350700c80c02a00300d0880c0e405054241a40c501c1441502e0b1603a4160045448244a54201c48424010000c01440048462203480d0003120030010b1007403601030045e82500d6140c1c4506184605203800349410080d001801d50401d6101c3c400744c1c0e010b441d410030b030080b500344c0042c000d60f80342c04481590342510545410140038500000c1001680c580701e0006004c8410014400c04032501c07150408070032030503040d60441c901c6100040300117401c440d9034014003400400380c13400d001941191040204038040d9030301140c1c0c0c0d6040703074000a00180c4680c1c001d95000003482d1840030701e2a00681c0744400b111b81c41e04076810002154003070141031007040000e0312030600700b4a004030140318160b0741c41e26000300c0b00324201045c070340712030104442e41ca060b0196408882c1120b0115165040c1500d45c60b96003403d4411030041661041390f007030050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 562934784 1250 562933534 562933537
    0x60f160f090905373204080f04080606091602030d0c110d05070c12050a060b210a020a0602010501120201051602060721091a0a0c15140a02 61
    0x4120549401c0d090500d014614005440018249156011065204041d00b2104d803a0301545130420000d10b4400300c3c00c0300c20002140c031800f038441406107600c40c80341d4641a2500018105603000d00c440f0081c0d0f01c4900e04042d00d8000d981400390502d501050200d003e20001a070280b18400481d400c5030039403551a1014071604810010300d0040c0c1080047da0720384e07075240e0802c140c080c42a05e0040302d05a41d600f00141070200006420740000d070f0002d0640144410b0301c0301e071405000b1071119070400c603205644495651958180090030140c0340d1200d40029629410b8200300d0518200c450800701c10300e015080d4170f80b000b0b01c000300d02c0f8100344200860700d54414800c00c6d058402c0b03141450711b4901c0f560010340b45a00840303800400d04503d0384c5c0e80001a103490000d0004175108540b803c045130703c0f170804403105450407121176041082c803003003c20480794a07145407a070400c0c00014a61359040e01d03550450b0201400803010b00f807110400c880c050317441d000d640400312481c01c0807030100d01501d0b000500c805a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 562936034 1250 562934784 562934807
    0x1b070209040b1906060e01091502250f0608090d0e0907270b09031b060711060d1e0f06051f1803060b040c020607080c0901050c060f16 59
    0x2094400300050005441c503a24a41c101c2059240319030341c500001c0c0007200741d41a9801c0013001442d441031040e6156000342c0c0140207000d840e41503c90100b00d450b0020369407200c05000e8142c55105400328030308410103040040c00b034248103d41c1141e0035180c41d406014407106075500c1c4642e04c100c49030907080d40e10500d402c3c440044020103c5489803140700c002c0340c56409240700000d4010711a500e00340c0b0351842d8071640005004803000951a605201e08044c02c18030b401a81c545000303001d14098405aa0324012503814960212150300140c0711000400c0d042d000704440650b040d0328100d414072240303440328044149140e41c801c090180e017028006074410380c0d001c0d12449400841c83d81d04800042884088001c5440c0c1901c1c003221518840c91103615134001590003036940b20790381e250303240d06801c044c000d5983c99078a5000030400c505285070000c00d586002054480e20140104080702142e2161381225a109030b10402c07602c090a05007510000c004055030880101d07000119211f13015801050407000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 562937284 1250 562936034 562936039
    0x4081b13020c0a0311030f030a0c0f0809030f0d020705011503021504050f040506040b0d0308010501030c0e010c240207031205090d08040f02010905060a02060717010f140f15031b0702 80
    0xf5440240c1e90903900c940200040b00c5540c04148003148034040250040c5100305114000414200e09049001d0700c5a04035241c0803041155000400501040000481e40282140d00205507035520829410340240284000101a5400e0064925200d0110080c1c10141ca0007102e04010780500040c04003010301c0380e071041c182c11080302594000340b490707d41c0c805542301d94080c2010038180ca001c000106190040074086020450400040c001c5507414401e0700800000c0d03062202ca00342103200081d080c4003a4110040110490f40d603240004800020b0407440e0202c2d1000c1075488125a1034050030070311312804404581441c1c030300043d807210b0707000071f824401d00c0072074a07565080d840742d07200e040e0700c181e02e0070043e414410001c1000846231200c00080c52000c1d0194080e2a590400c170800034a0001c001503503400710380074640107001c6a01c0c0d00511078202c070b8a1003011079000100c030300810002000201a079911090401028590518050046115155100e103030a59204404100c8010b1300800d04080e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 562938534 1250 562937284 562937293
    0x603010b010210050a0b181905010f05241305040f0603020609060d060803040b07031e0206060d030320070c06020d0e131803030605030d0e0607030f0504081b13020c 72
    0x5071038105136000301e422115100c004140b80d02c0c3e40c0003103050501b6050140780c3c24000042001b0650340e0103507844060755000c600501c5107524141d84805903180902515201785103400500720030010000d00c0c500e50400b8804031a0700c52081005502200f004c612031240181c2c28041030240c114118400c900540303500508080c148070002c1d050080a40100c034031081c801d60350700d1010076030410030406800101400180981e81301c4c014540100104d042c0d4044810700700b407400b500342e00203401249444c2e10a1003074a6861507514a420128082c2c654201144004100c030b0b0702040c603030180000240b6099009588a06499031750301401c907583c200b000f08690003e00055400b00745417070700e101c81a4002c81003200c081040b001c0c50150703c40c03480002500700d0200e5031760001000755040070311880c5100c0d4554180800c04240820101d0070502c101c2800070b0804c9208442c1d00b010034018026039001d02512812510300c00208e11411a13100c0301c02903850711441c060a407180089046008481c1d034042058090b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 562939784 1250 562938534 562938553
    0x14040504170c030c010509060103031e020a150f05010308090405100e01050f0a0801180506070e0622030b0405100b0d030509092802030612010902030a111801030510050603010b0102 79
    0x418194201012080d0b09020412260300c1600d024003c1d05c2c0a1803600e0f000d0403d55166103000f400d040d006021009140c402088030b00302c02c0790042840c41c80d0303580003444101070008400d01c040080c007221214540c007528080011060021190152042c21004e4400300001e86805250000280440c420800d1000e0640010f00050800da100001c170404080d24881c081500d402e42d09007520848140038652829100b5290140642080a1030f0010308a08111100710301841c0440c4003445150721100711028280c90441400029501d03400066400c981c0781902800c0528203192220a403810031902c6900707142e24260b00e46800015848095451b44405290030750460070710817104001030070582c80441d1400740c903070011048290f807040720200070b0006a90b8a003000070000c0e8003030209100084ae07890068000300684000541c540900e400500655074010b401c00040c02085c04120b01641e6600ca81c0300000c10810001104a10f0300c0d94a007050100c1d90f900300030300d4204c4031200d64190044e401050030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 562941034 1250 562939784 562939823
    0xc05030f070c050715180603050903070f23060a140601120e0111030c0405031009080412060e030f04060206090a02031c0201200403031209150b13090c14040504 70
    0x3841c2c0101c2c421801d9a203141e6441d031440e005800414130000c04540340f42c00700d1414030085000c03000944001e0404010030704100810035070324021854014814054101d01c02d0134004600030004a00c0c00e4066515a801c0404448039254070041c2c4955200c00c0c2803a0000000ca14080607461140303406a440c1d04160f070682d00c8007005822095000709103550b0310342c40000680100001148503000070f582d0a50390b246071405043ca0102800c404200452422800400040741c090460f41103a8890519038544105410440028503080b200c2c00282c0c440007455280007070405000c0d004940560b000d841d8540d48030355140d41c40c1d6180050080d07043e0455140d080070002040301852440c01c46100010708490520b075900000400b4507104154404041010420140d000041c0c801d9810000c0f001d1081540e1556402585402064072005ca40d4852402d03100e039440341c1c9045155411f0754841071103003407100d081c52090514075015014480054000241d100e0400f4002d45002c0c5601c80041e00d4440050340380d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 562942284 1250 562941034 562941047
    0x60f14010206071b050a030e0a0801020306060d090c2d06020a02090c03150a18051008150a02120411040605030c010c17130801141302060304030c03200609010c05030f07 74
    0x281c00058408040540010805c1002081d161301d01ca1b03200d071030354032a4007403c01c0a18111640f0403040d983c0104104010f940382c00040e00c50900c41c101d030118484946180c1502c00790059007018400809010040c840030b2080c1f240103401c02c01d000b00501c00f0030380750441241c5462a40c100079401202e514007003000c01348034400850744420340e00030400540440c0c030005600c15000e03604c0400e140d4218044021600203a10841d0741281514540d450705600e1301c14001c0d00e41803d1611001b1340881c01000400004580d0111043c66407070400810b210303c1c01e441c04000c03401201503103501861800302c003c115401c00103944211210161280d0340d0b4900d09030f5844a1034100304100c0b115248007480b41c1c03900b0080350100a80944100400410344402d60320640d8090040200111a410ac1d0f6045c0c00002d41c8541e022280c00c43d4040c0350400d40451a0304050b5040750720081c102d005121408107250b00302c1c0300407407801d0103413040d0030003404031802910341110107010503a407814a40d003100c008207143c01d00945 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 562943534 1250 562942284 562942307
    0x30a23120411061b060907060c06050717010b0a0e1905040e03070b090f01050c1905030601110f0c030606090c1c0e0321060405010b0409180602030a060f1401020607 72
    0xe50394610542075001180302d54000510b42ca000300c0345680051030781c4c40c007407100b6035000f03140d00010a009460540002c0c000f200141000c0c1c4066078480108080c00e1150315090741002601540b000996920b0200303481070341c08050400001030070306a46044c18540741401c13011000010b0084900d45042c00100002030003640924101840200202d000040c00c4c6508140304207400005080702081020506082d290001d10651000f00c041114242000040050b8480c0001d9454031907120b55840c00140c03444400d010401a00344948140d540070100300060031a41c0d82425001c0c2c8555032280c0c41800000d5070152101d40d038040e410310145858220b4103070060703188100044042030102080c3d071b14034190760229004a061214070b000e0349007642141611550041ca09440030080c0d0740c5450a001102e00860054ad0400b90304c0e141520088614450b00a1060350001d1046659003842c107544002031025100e031103844503000c3ca0008038465201c0300320b5001d1506070090f04507551560000c0b140c091000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 562944784 1250 562943534 562943543
    0xc05101b030b030c030a06020c1209090a0b040e1c0f02061009090503270406060e1e0102070b03010e180304060c0b180d02010507180305120c0f0f030a231204 69
    0x1c08011404e9503042101c16001d9015040069440d41d003035a4003420701c080c10004050ad010100500709558075822100ea910504c140e0700001c00132013080004001c2c10701080a0390181c421625608455600c91000451041007601e07a40007814218405a031200001c44204c04030f00c003141800c02c014101b6030040741c0f0482c490002d4904e0710303200d0b1203101000c94001d01441d86409402000512a080c60301c01ca034068207207070400c681d0a0703100c840005d402c81804250661003e0a074014100540d008000c0329000c0c00103c1459612580c54001001207090b00301d88030b251802e4a0130002403040c0000c41220180c1e401952841003180d036030b071581614407002805e40891910f9401307080300e2068003400207000f02407669001140a040190008181880c0003540c1c070255406401c0400c0041c0d400a00030360800c28192465468034640200b0178100189004086114026601c40592181010005117405901030b120b64040f00c1000700101001000c0303080700781c80c081c81000b100101034100d800c0f255106225 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 562946034 1250 562944784 562944793
    0x10f03170d0b1f0f09140f010306120501020706110a0203250f030302070203010b010503010f05090a0f1d0d1d1908070f060806060307080402100306090c0c05101b030b03 74
    0x290010403100001ea0f0801d80808840c03144485090b03500920024040e4400d18190fa0b0050130403680100c0c070080b40045034410b003e0701c030101c10035034003e40184c0014a502170b030802403081c8500344030f130103540501d501f1100c1601c4c0c0410341401281c0c07001695000f2180c6e031f0041d8144500d07a8000341009203601179140902c880244064001101510740543c001e100b550301607203440c52407043c9400d40d00c2c490b80b2581440000d0006001c0d00c80000070140c11500110351146072911401130aa000700a903c40002c0702a0402003100c007400d04098816900e0f50013141180c205006007003080765240310882000c2c2003076032480d00103002071a0040500183d11006001114115030728880e00b440c1503080c2e8000e80e0f05070200481041090382045a89a05c0700094030391500c1c524161000519400300100003d21400120881c1d88640380300c3d40c01000a0106000100158114090040c0c106040c2200440f07031445906000302d20714000340940c6076180102c006e00a1480b00c00b800a5014180d01d0304d00c2d0350540704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 562947284 1250 562946034 562946051
    0x101401080f1c14040f210305090409022b0c09020a0905091906030c1e0b030402061c0504061a010f09150311040f0512070602060402010804080c03030a14010f03170d 72
    0x11140020f10040012204a00d03206141540182d00109161b090110440c0684098804641c00508943c418002290000b400f0004e901c00149010074002d05502d03004c2c1402c41c2c4610403460000d032900d01500907416180c0c11a0b41c1d80e116001d92044840f42c000003811000100540d0402c90452a08810340c80008407820b01041c06020440d10182d00540301c0740007607441007101725024a0058900c10290000440032810260a00958031000e00000c0c052040062071402258428a501c0c0c0312188100c014482ca0074a428010050100c83c04c00f5125500400310216156014900c4646803002d5900c4101007a40b42c0103001c1d1801600800c40c006260b00c0c0c00079500000106401003000d094821904062039040c102030240c2d6004041d14144a940008070901400380c0000d0f10b26849542440c0050700e43d92549420501ea0048481d070000350b10011090000615032078200c81c140002c9414800041ea0ba81c116141031403600344000340c414000302c0c040c0d407481c40808000740701041306036201103891034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 562948534 1250 562947284 562947317
    0x9032402030f150d0305070b0703021c0204060e0904200102010209040f0917030f0c030402030a080403030807110c0a0b0d021204140d0f0e010c03090503101401080f1c 73
    0x74802c540382102c4074606402c00c5440501c681890060340410f0390503075054012584d000d4410b00c02c81300701514004509000520703403407003a0112414201002d000b460043c4c001801070000c0c0d0450b0142602080e203510901c052820300001c1140300d0307500f20a00d640d83d004151282c406071281900700300c8c1195000c0151020a803140d0107590698005010009444100c80c1415500000410605104682c0410070311080c1d078194581950841c0224440603526119032001900d0320290f201c0080011102080c0002419040044140b06541d10b8171003402d8400c0441d40c82d6141c450715401e040d8890a051801c0c400d0229100281954094215005103400b0251003913101680d001c82d81141c0400500d151744102e030f4030500c07030340c02240d51a08204030302006c03004e800340815202074a25410018140c0d240828184a0508100108030140664080403a02c2250b0700c0604007200ea03450415078048000112a4000280d040341a090f000c0a402c07482186110544250a0540000e0400904c020000120b1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 562949640 1106 562948534 562948537
    0x2211507050702040515030613122006011415120c0a0309060e0102040f050f06030c070c0e0c1b0f15180f1005130309032402 55
    0xa64403803000315550302403407002941c000c1c144024450600b034060034100c0c4d18801038044d50328a42c2d410030a8400380c1c80c0711074004c00240d03a505103030080500c43c0710f200d1020000b4003d5498103c2400c0c5d4050702c2c206080e000300c0201800c503011034109203441c0440b4a22040369503c501c4c204055850318010707402005042c84280c4500050030303c4600c2c403961058003071790340c44141040305112003944207000b900f1500070100140f991502c00f044601e8818201c02503288000c04051441c2d0302c1f5640103543da005000101c6090706644d402051404a400070940701c4c1007aa0709943e1190821043c0750302c0c05c81000402c00443c3c00694004c850210f020030341d0340710307c208001540580d865420310b00b040c9000104a440003805081015011100f02042c2c012085480200501040e1030b0840c01340ea030350412031402400700740c14039410000200440d45000840090707200c0742901c0f0038842c81c6002079 = true := by decide +kernel

theorem cover : BRFrame.Cov 562769784 562949640 := by
  have h0 := BRFrame.cov_init 562769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 562769784 ≤ n) (h2 : n < 562949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
