-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:33:54.436386+00:00
-- url     : https://prove2.me/submissions/72bd9c81-a143-4710-9a5a-8720516f048c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 907194244 ≤ n < 907374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 907195494 1250 907194244 907194251
    0x602030a0c060e030a08010306060b090a0b07050c040e07090501080d0c02131e0509150103120509010207030b0103052802010207170115080f0c030a020a030201030c262215 75
    0x70820200e500300540043d808030403651201549800100880c90a102c1554024542000410016115011100d20000242c84ca0591a01d00482a0060381c04207c042d10030b0700400b9520000742c0c0e01c6e4058851a1b0075841f0041010074146092807003281c1041c2c0c804e559680c00a4201159141c2040c082081542c04442400b0400d180000321000350071401444a851403e20b541051070320b8440d4062030084500b01d04545000114210048401c402804003408242540d0303151250584031300001c2409003410f01c10b45c1c000540d69664080030b48801e800860345074205510001030003914100c03842c00800c40909510303001c10180c0020307480d500c00c1e004941300c01c01031a980c00311000003500555001184080054091a039039078105840390315980f4411018001c566111100b40340000c1e01c5030100780c0040c60b0f8011589158015802841c02c007982100b800801e40c2c10043d03210009200c01031280c101698450726141511030b0100d90501c1180d4607081040d52001d041c086912000e40c502d51205020000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 907196744 1250 907195494 907195517
    0x230102010b151308121309290604030203120307031b1209060612060b010f03060b0409020705011e0207030206060907120b1c060b0306010608040f151103010e070809070602030a 77
    0x1d800d0f100103030001801362041c0d400604200524000512800400324100a8019210110f07101074801041c1860141209182d101080c4000d01c0c50000580f600207003090300d0f1507982e5000c681006501c5124080907100841009034044c0c03d4082d140781345580342d04540080588001c0030b40007012074000040c003c0e41d0b500b9064100000b981c01030000c0e01407041a0701d2895034910b0090041d01c0070742001c1e800140001382c0c03117550314024080c08081d5160300d2502c80c10b150a00020400a4101d60070a603200c0d92103200d600d08129207950804044124240090303030354041414081e2030003001812060080c062041000342d01c5a0007688202080b10200c0080761170f140340d00000d86140a80d42442d50700019840a0404102041d03004218901d804d41c1640d0186c0c1c0c0e13500303003982e0114088401a00c1c0303080ea8007010002440280400d103002c0310030080000c10940c0d44540c1c091a070006d801800071f1682d450207020200c1d8000c09020350140200009046040c10460300175240c2c002c0950400074407010700b80701e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 907197994 1250 907196744 907196767
    0x40b03071707260706090b04030201180306020f030a15050105221e060305010b0c0c060c010f060e0601030b0d051c0c05120307120e0601120813230102010b15 69
    0x7914020801200640d610f4040b1403034114400c84900624070795882442400035050f401800d0350070840d06d00f040725500b0546550019030f82c41246c22443d4246040510020000030200d1000e0000900c09500c03282c1c59103010840c49023204d03080c03803180c0c10800b819002006660381c41001c41d4481400080c420605001301601e00c40d02075040d030050b4101010388540d0700f8019291240d0282241d0440da000c1c80701e81d0342c0d510018000e00c074414841e500341e08003002000c81420144000c0644006040001483c410070150140884c0c406401c00d050560400781881a2584d060090300240380f0f044841240701007841d0394540e5036481c01d41250b01c60907200700d140440f041c000c00c24240c10542041c140c485030064840c0020840e807084844a0201e100c401000b0300b0800644240080459148014a0280d08100c800842a910002d080313030784007000c10071946182c0c002103940e0020440000106045801c161042c801150b0241e103040c1168540501d040d2107580301404010002100405c1c1980c4403a80c988 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 907199244 1250 907197994 907198003
    0x20f070807020f13050a0b010806180912131d0f040b0c0f1b070b071709040e100903020105070c0506060409050c0306090a0b07091503050c1c0b0f040b030717 69
    0x140c89500138480c6400d24400070480d04200e20400314810f00308681b403100d01c01901c00240540f105a0006c90105401040c8840c100046811101707900c200c81b1020704140c4203003515800400030070380c484403164080221004514207102140c5001c90800c9061408240e04400780f2802440070f845802c9503004120421120400c0f10102031928100e035075140e894140800646000c024010700602c80e2700c400050510824060340c22007588419519404040d1040c0e0140c2030704908039450740a0303a510001170450500700a038604202e1100303c0030030b0907600303420701908488000b0540c1041c8917003151240001000030842692103002100c001a40b0390081c03c066203001d1b42c1041842d014231440050003c3d0341c50015192250340e110381801d01c007039500e070701c1c1c103c609103140d1165070316601c440300e518201c55000340c0015a0020010804909205080d50300100300d042849401000741d585a00721106410007040e48a0f0003c7d0540e414008000c2c40e1001c06c2d5242e520303114007507070082c1c211100542d8102c141f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 907200494 1250 907199244 907199269
    0x12050f01150b2d2109010b10080405161211060313031202071b080712030c0303051801020d0609050a0b0a030b0c0906030709060f080105090115050c030c1f020f07080702 74
    0x650464981d01540700c440007410444c41d0f00c010381c824640000d26540014012001003080150002e101c06c000e4003000d85030300e07038050001c0300c039401102d0315192050072104a450041c4040d8101c0303101500c3c1c50520303103560602544030502802c410810060400500298001034540c540352110540705646a9a030084c09000e00c003c154a10141c084202540d80403c3c0c00152200b200076100030b582e8400180b00702c0d00300c018004000c62002c5002402082c0283d004035403003c201c40c003484604c4010742540382240e008914010009958000a21140050784503c2e60302000304d007002c011800500c000680044e0091000030701402e40303000040c4210307403520192815004050300c8a9142c1c00c0c8806c02814020140c090140058415912112000d2096422504a680260111340b540e4248401d040c4d6266041d018041171040c03c10114202003401c00042155115500140501d01944001c0c01c5190603001d0141c040180184148010042d988048800495205909a17919030031031012441840841c4d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 907201744 1250 907200494 907200577
    0x50112060f061e050a14280305160c0b160207120c0302101b12110307050106210309050f0f040513020a090c0c0809010912050f01150b 59
    0x1200c0010441c0d004812945040030090303034483c0142111008030340c00d008081c0000005054404226054002032000307140d62401c1601408840400a003c111102600c3e000380c400240c0d50030030840119001044000554070f0740c50500c10702035581d2508104842d01520b52102072006081041c41d80e40200205401042060780e0101c1ca54035034100082540d84501c42030340510151010f902c0e0142c0301e28681c6504036050b44040c2000211519000302c0205448008000d0102d00d003030020911504001914004e0f114100110b40c840c10415240b000d10014404e40302d0203042034010b5400a41c103c410407054980a0350102c2c882d06080c0c000a0107600e9196a0307580003403820b828000d14904920300e13001844d0003900d41c1c001b0f0607074584881c1c044454800c69a40000c14156002000904410080003003540515002c14600c0d212007410039054040c2c8411145544044009184180c080c05405802512445030010b424500416a0080e120f031003c0250074003065010710726900301c242120207030144407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 907202994 1250 907201744 907201769
    0x307110307050904031d040c02030a08060102030418050412030203060307061119030e190614090409060c020a050c09061c0c08070b1e1801110703120804151505011206 73
    0x1400d0240607010803680420b0801b681c140039410b0b0f81020300440019002d541d0013036180c0180d2250488441c0e42c09411907045020400c000511840003c0c040280d09444181c005140d041501e0081036030041240c011051600500420600355800300340c4104a41c02070403c3e03001d005401140c2c1d170520200c900091b103170307050002c031120505070b204c5900c50308900166425850710300c3e040301e030302c4041d1200d108020010b10000d0308942c4600e880d50280682a4000c0d0000c152824143d85840985205040315001603101c000390000340101000b1511130b000054400c01142d04100001c01c45d015403c1405800c500f503981015070420400c0241d500040040f0700541d003407552660030350241030748407038074000340301ca881031030982848c080900301c4504c24058241e0507010100c500056442020b847d2034401e40380124030001000c198012240309001000e0b6a48a14078a02458040c81d08811a0ba0350007203503140030b0700c00a421100390203100a8400900b424104988440c6010001c4c100a41000c2190400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 907204244 1250 907202994 907203001
    0xa231c0b0418030e03070e0c0c0f07080c030d03050606030f0c120a1a09091c051902060f0c07030f1107050d0b40030504050301150519060203071103070509 68
    0x60880304441c018802c1c2d5411201c12951800c1580d6401d003405503141c00740409003c25109006100140304a04c01c03070045cac40d00b03100c407140d0007401c1c40a0b80c3d00503003071a000591550708501d428070a0800781c10207410b0411550a105001c40c03210f0100408000c07560340f0080c040340c4115601401d80d8403001c12207110391403a2514040440213004441c0c20b00081805420f224181445e1440710148103c2d04600102042031a00c1e12030844440151015000d200042001035500d58031501445000e01d00340d00240342c1b03808c08440300c40ca6820300402e18140510280011400240d01c40d900003007010452401c20620750690303202e107050125030382c44940c0c00000c0f012044100140c180c64180f003001e0050040306e9a07180301640303a10310301d42d118140a07825030f285640b10344101d400d02048a020300030f150050400f9200e10100742101c86a80c030419001103445000c105519100c00342c251941144180c40d47c2d010310b0118060743d02d0198a5004001c0840141c0400807500c0400181c2d0003407800410f10020ba06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 907205494 1250 907204244 907204271
    0x31a070c0615060f11250509040803090c1203030f06060f07200a0303091205070e010e0610030b030309040209060c0618010c030b210f0609030a231c0b04 67
    0x18454860b1030b020840741c08003004420b0181710803d00d4448141e000e84241d000d60340365180840e03203144107190b00e101481d601050035210500b00b284203920130181d00f603990a054440524001c034110026200310b1005040ba02d120754044143c0c1d030460700348070800403244c49400001d0300900400c994024000c1003c1040018028118254103a0070094042410390f01c4040080c0040f44074140806004500480c2081002c880343c000e800700f0490103841580c443e20b4503030004998a050030fa10a005d0046080180720561901c004184e400c400706040400065242c680400d440e4011800c40c0d521642d40894618101c0d02c7d224101c3d10318811f8901a41c20928050758815082e0200c1a900c1c1225864103c003441a03034060700c20090f19160040150314044042604642c0036202c1d8440f0131400e010300c440c080144d0310200300c1030340592045005192200c0d204d41c0001c000550310403000704020f00c0034100d200030320f4104007142d480b8003040c4403811407064881c3d1a10081c001030a5101e80042c50711450f010b0340c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 907206744 1250 907205494 907205531
    0x12010e01031221021303061a300706080117010e0c040209010509030d0507170406020a240504121103030f01090902011b0f0b0a05060f09060a12151401031a070c06 71
    0x507803003211f0410452051070002c0d000c401408012580100601d032080d030900301c164002e00c4a1003d4202c0c82d0340e90b007116030300303060400328240e02050110740074100604c0f107940405103001c6995a8080200101ca121900780c03680c5004240d4514010740d400121041c0592265040703a0406030081c3c2100c140460320140100310b40d1100c0b80c107403004038858140c41d5400300310781c00b00c4003200c80c298020300b901c0d40951212101c050303010064035005420400c0d008005000c1d8083c040c46503004200121989050302c0c0b01800107104881c05440c2500100b0801903014081d00740d00d41904c00442c03001442110764801a940001c15404003260014041080750400c00409410f02c861403042044003025150702c2c070071409403030042e101198808010303c01c00c0c010303042a41e086a400b07a0b004202001440c1c0ea60810300b41403606903000d9070106030302c2c441e41c0130031078150203000006034219519440700d41c59502d4004683d901d00c603151008200c808041a6418420301380000300c5601700500300521000788502e00100b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 907207994 1250 907206744 907206749
    0xd02040614210309060904060321030e150112061d10060527090705220c020604020a0312230c01060501081905042612010e010312210213 60
    0x40e102c0c016034900700c0000c001142ca070300742c07644004508200900041100c950042c04185400c02c1d6100c40000c0070507165090042607417804800c4039030803180c43c58006c050302c2d070b00350007010302c2c3c2d000e4030580c404030015441c1c55045035800300c01c00540d0f1629140c1100941008000c00591010440080e0769415001c41d0194050f5000c00082000d5070352242804107070440050883c2000c445442c104034010381081c1d4660303200184d01c05592a483c4c46000086400728200f280e03204880348251541441c3c4414400d03141110031034001007131240741c83d50000312040b000c0c1c00f0051100c00b0041d402c2c1d20481c0110340a000c0781106014021001d191301c044041c081c0c10408018a0030f40c00c1a01c00100d41d405041014091403414141303240824120200c1400760902500032280b444807890f0500045502c0d920000c0c801103040307916952440071180328900c024068010316104400080100001a00030204075041c01c0d050500c0d076030b800b8441c0c0003400307402032506410707000c1800002d00401e503050030f0050360103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 907209244 1250 907207994 907207999
    0x904061515080a060b1204020a0f060f111506060d06090504080c06070e010503070e01110a0b180c06031603091a16091503020924120916140d02040614 66
    0x560f03540d40c85400950f0b1581c0718410704000c1c00c02824180742c00070f41c50a54001d0004e0145403645a0b2805680803040c810340c86032000444500340e0198503541324003050024030846000b0620b14040102500707145d240648600c4c818000041d1006554615400c600d00800d5124800c20503440c4c1400d212a496021000e0400103000790340c002408103000e0707101c0a5603410181c0d10a420341d910240c0070388030038060040c02414002c440e012002800c070100f1249010303500c00c42d980e04050a00c590080e04100b0f202000107400e40200c103948080d030f1510410f80742e1200786100704107172041011800764024080340c0005440c100094511004541c000d0983e00d020f4121034071a42090150210122407080c140e00801e6500803d0188400c41c961007030f000b81210b6030000f002e0140801c0e0411011003200c2040e0401c14036010085082034210300a100104c0d0b100e128003020301004d20650014880240241c004c40d0000b21203910708500076118200b500307a21a40c00760007000040e82b51183c01040880107480c061 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 907210494 1250 907209244 907209257
    0x15020a122607020120031302060f1c0e0c12120f07020612060a1409131a04030f02010b010c030c0b04030909020a08060a1403060408090301150303030b2d0904061515 72
    0x15500d03160720704480c4580900041f40507200225800c20200341e00c0550754202000c401c2c842d8201001540c807540794030610711400000c0c03c20309107508500748034020020500c01c0700111100354903481c011880c10101c01e07600d03d03410382e13400c04035203c840c140c090200c010350004400b050201c611201c1e0102103015203000c64810591a0341c504140704048910364600307402c01c600b8008220500c0319580c0c281500c4c0d01c289804041510403041490001808032426400290320040700c07104946c081c410010100300170b11b0800c184079950b80340601f4101106200070b05034001000003400349880f50301d062001d069003082c19503462a1000006140d88005c2c1e0f54548526400b07500026600e440d5000c050032520064090003450740d40741c460b58100d07007048040b81c1e059502d507021124944111070b03518018503c41d032800035805000505110b200e100c0501070b1a441c2484003908142c1441d805108010100100c1d1040050b95440c41c1c0301c07002e000f014480f6040900c50303103004901e907201041c0901022419540780c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 907211744 1250 907210494 907210541
    0x150103050a0e0307230a03050a03110405090c13180e0705032b230c0d020106081e070e01091b020111040311010c0507060915020a1226070201 62
    0x82194090301e12031942d94010420500000c0d0401e80360a010410441c005036034241180c02241005440e01c002c80c0010b8000a113448107079054030540001800c441080e90800e401e00740840c0740c0b0103016204034020000415402140d0b100b031802600900600350507500c94039004c02c9004041d0040303080c0f10310107010305103001c11142400108007142094141c6680742c030040700c498400020943e072000500b00000500b4409101038074030501c036601003000d100c1035601d84003200614100b140e100074180440e410316004101d80100060070b50304048442e41b84100d40d140e0040b19a01d0a80f1503400300e0041c20341c810000a400c0c42c80d074130543c00041c0215101803e14207104d001c0b800c03079001000640000c61300b0300091002c80e009246c0c5060021040c18800045d41943c2c8405e4584010b41c1e01c60b0001a000304030910207072150301304a03206403040e400240780805045c0d07203042240d0100c1500408100e0351000380c1084000302143c000428000c0d0750589010b04200c00001e028000da0142242d00e005402d03103c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 907212994 1250 907211744 907211761
    0x1b030c0709021201060e060d02041206060801140c030c0d0f0b090c03010308030406020d0f02070605011a04050121090c1205160b0a140f04090e0d09030c0603020705010204090515010305 81
    0x2c0f1890340608000241d61a13007070000c1550120b040600342500000103208081c5d54100340c1c401840030f003420304a0380302d0082213031400e5019520550002c8800f641415102c503c2000c9001c50150004600e500e031036101da0b03607940811003902807034a1805000c0d080c040314007030b018040e6001c00040d4005483c80003c942d1800100e0b2410b04c000e20005200e0101000050003044440e4058991183d0654010840701c450380c00c10700036600075070420f0311030740da4400042107011004804c3c2920000c0302c0141c10308042c070704000600542098404060180340c06954000004003da108182486e40041540152610380b210102451000c1d0802c031554450206902c0c0c12129460120040702c0d54070040390300d401954603007140d9402c4444103079040345900780300c0c01c2c21000008011704043c1c1124a00021483c014880c80b9103440b1000c100e05003840591201400440c0070f038180c000684005050160351850703249000c900901c51071780051042c40c0341c1018000400500c1ea2880e440f0741003641c0600c50344d200c4402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 907214244 1250 907212994 907212997
    0x301231812160201050d1a120609101d030f0a0810051e030723040f0b030616050c030a050a200706030c090b12011a0405180c1b030c070902 61
    0x2000707031011030034002180c03071030007001034001c010348107152041c20105d507844000152907480303440c19000800381c03065070254240050f040040404040c010302c4941013aa03446500c0b09a00d0915808850312104400c070454551941c00b81c4045c8030b20100d030759410800740060070940014230900c002514460218003450f9240c9044003d41c4c800520404c4000c00c410701c480d0060503140881a094050844001502070541a9080402c44041441008a600d5100f044100c0d100c15501009003031500c0b1145d41e13942ca000403450380c0600e800c10808040044207030203844a008e849000b084900c4002070f143c42c8180d001014002c009800c2e00c900c41800040300704070f045800c0080f07041005074802001005550301c641c00c920782c61483d500b03052201580b0f40c0c60144040d8480001100e0302d4910000402c00c003c0c1c800619002c00c880c051044d81800d0519000034280c07580a0750340445884508081241250b4020403601c900300003150160441c000481c6d8161a90001d404c980c3e22401400000200e0140790300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 907215494 1250 907214244 907214263
    0x15050105100f0e0d030f11150423030f0a0e0d0525091803140310060c080d180c06020706020c3a0b18190203012318 51
    0x1440980c0032072803440122022425922070038200075820078503800d142c40d224019000780740695180039103002e040c5e0b0040d09510402440c07003000c3c0d01480e6221501d040c03041c51140c0195004101d40c0d483e01c05400a400128074036000441c142c0000a1015400c00c12000100b1202c030144e04c550188000c01401c01a0049440340080d0050708100c050020f180c203189080f030032100c40c1d00504140240c80e03508207001c40b04038600b6051501d902d1220001859040440c004449c032555012515510300503061313170790101d5148035442c01d00031a40307140c01c10041c4450540740042044002040080f42071800c2140c40801814252202c004000c070209407244082129019258243c00070140e40c1110014481881d40307e00300d0708170103018860b15003e246207101503044400c0c40c582e903100d0b0120183c00d040b400903501074021902d00211050107000c0002c085281014681c80495400040c02075002103030241485001050400c1021054003d0314240340a40e01d006206802038510270b50200e412180ea50441003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 907216744 1250 907215494 907215499
    0x4090f11091c02120d0207030b010b04150503220803041511120c04030f0b09010b030705010c0204050415020f1b0312270304060e01120c090515070b010e0415050105 72
    0x24140c01c0d502000301400100a10161000c1c4e0200c5101c1002403c050304a41c0c8540140c1040301c041092091204a55016010705402030385010320b00002c0038a107030b80c601c2d909001e116010000551f10300c0c00509845690008a051804151086c50107543c142c0c001c45084030300c02c01c0d070005c8040c680c80300d03c05c01c81e168107680d03011440c1542c1071003030800b590b40050828840d21002c00c80031000a108600d0111070a104940080076420148000e50035074103c0c0c90620700962080f0800c000c944c2e4000e1100c002190140c1e00005c031a111360030940c0300f03030070460b4030b518a4500020300440e2814080004000c10460b081e45a00d805c04a00788407901d80c442c500b20f00d00c42d10468008110b854031352070300b03a540d800070080c03810b08146482e510103419600907502610101d0f504c0ca201c05420358200c2000c0b101d415205108001c420303050100501000140e003e12406060750403038120248041c1003ca81d280f071f822245d5071182d0341c1d4a11154036803050444003204c0140041d02c151a00303141038044c942c16900d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 907217994 1250 907216744 907216759
    0x2091515040306141b07050c060d05540a0b01060f09030c0b09190f060f050309060a0c03090506010e0a18030c030c080904150306060b090d060c020309030304090f1109 73
    0x40c108402e0241c20801c803c0e681f074000d10f600d01e102551010000d00c01d042010388089038914120f01c00034401414180c04990100000f0040d442d8100031825101c0c81c075008816042601400a90030000001c0484803120319105003d829010700041c1042c0504a50b0a42d50701c4415258a01c02120001075500c00100b070300b00d601c0c406101c1c0c4402c04000d04043c03072016102c00b0404030001c540c0d60b8a04002e034000e50318091020380c01d02603640d000c2c1440e43300c0c003d241040e52860501c15082c654031a0000c1900380c0c515076030170f501d50b05284280c101102c0150014125070f05561580030f13481d007d803025900101d080703107070030845083c2c04241082e0030a890380649078807101c1407090300c003a51551030030807084820000802c038000780c030f0b99203210701c40d03044031404280100642076241c142d0403204241c00c41401442c050011050a566408071208503a80c0003c002c90281c1194005900c0c0d4010032180c0c40e071500006c035020071210071030342c004500001c2c084418013540c0a03c3e5004081c1d885018111034100c501c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 907219244 1250 907217994 907218031
    0x30f0e030c15070e031c03091b0f171b010e0a0807080717070608072309040c02010e0c061c02040608071b1218050402190206010807050d0209151504030614 68
    0x100080fa184156101e41000300d540d4426981d4581c030702c072107c00d0b01c40d01860703080010311035012038203162400740c07182402d259507034403600d49cbc501c4e0369007560450380406c0070b1141e07215031513a40319016111410801038018810070384c4500e0001e4640f2110701a5000c1c5104540000a0707550700c0003081019000c1d0000942119410107004462002009245100b4021114030740421640d081248400954444052548420100b000c000c00c6e00c100c01d2003401160304204420036107410101d207000100504540c0241d6a00c14807a52601d41381d0095a030701050f03407010030000b40c155042224a8403489095596a400c803520005070060035544030005446801c2c820400710010340130720340c060341c00c00c001b4400d9582d507a0784100250980c0d2080500c403800208502c0d056103050b40410020703000d04400c201405107942050302103000407551200284c455040c0c000441c84000031f0550854035401c0143c003600302c100c089030340000c0310f501500c000c54030030b854a012860607043c1780c0801c80c0640051021030070b1444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 907220494 1250 907219244 907219273
    0x3050f0c0a050c010621020306060d020f0f1206010306050421050307120b0a03050705010e060705250306062c060a090b13091b06020307030f030f0e030c15070e03 71
    0x1003009000d0200d44d9603c800100c1c40b43c2203c540580900c04460760340301d455002d841418100710f03001e45074502600401c42001c0c01a520f100c0c852410010950304e600859220200041300b041d41c0d0303200a4801d0045030000300c02c0c8001c81d0003244c450b03400f60b100711070024140741d03000d400581410503000c0007480034000b280d0860310498a60b02c0007491000301107000070f1550006101000c0651080352030f41e110000801c00e0313503049211038106c1c04c01160018103128076611015103071424480103049554449241c1105610320909036005503420820402c80c6549a84a0408a945101046100307a00d220541500d5280031301d0903520541e030203420541200d01d0082c010000c2d041181495034404007a505e5103c141250784500500b032400340000c0741c1c0b496299000c12104e444550480c82c00c54004104a0300420303001180350885401c680343c0001c04c100948940c4000386a20003a11701d0602000905442c202c000080d500c1e640071a40f00f501c4c5243e103d0500543d0505030520342c180e09a0032500d031b40103001c3c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 907221744 1250 907220494 907220497
    0x807080702061501170907061112041e080312010819051c12020a0302130f120803060a050d030302071b061b0c0b03130b010503010b0a180f020f070303050f0c0a05 71
    0x6074041c14101008038a00c0d8114942e0181110340c080e460b400010f003000130300ea10201c49c0d46c010001c0005803d401d8542c1c0d11a002d00c3c1314501913003c5020030030340e44412914120b21418020550041680d40300e051108000c40d41020030702c03501c1c21902c24280c2c8020703500d5102902e441d609500c28005c5c84c01a540c0590100c50400c0e0054503c2805410483c1006000c1a80024070400d002548d00680c0c1d0b441d40101a003446e40c594008030f050f20b241e00c505002a94440c1c1e40c44440c0c0790444102d545a90f06c0c00002110461541c01440c1c000790f841f2445020141c0580140181600c0b07003002101c025080980900021550b1040d2000200d01c50860603048503004415091140a2009001c0250300e50a054501d0340c815203000ac1c440c07205801507004e010a41c218540507040440003400400030050020302103180600505035808140c2d0b51009100360300764040d82003030824210a540741c00b580d44a2100c00c0d0001007040d0f01003410000040d00042c0c02c40c03400c1d0300c00d903501110142066040ca404861a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 907222994 1250 907221744 907221781
    0xf09070807020a080d2a09050d110a030308062e030209010e030607020c031e0a032105180f0c0d110a0308073012020307020709050412080708070206 65
    0x20b601603400c03030b407010804490041207103100884005c6455541ea00041d04030840b124901101c010110500c2c2c8016680701c1c8983d02100d100b10352181c007102d0507080c40721500040280c1e0540c0071214141c004101504190500c1c403d400484000c107902e020a4215494210b200e80003040c074082d50604140c43c1800fa9000d000700d0707441032408100c0303080848082854044251403400c0540d00c00860101039103420410605070600c88036802d84c81c410080400c5984240d12140201400494442c0301042d41c481c50741030102005040b400e00103420982228400e038442042c401d140e40c001c1d515a070b0009000010b10007414440600ba01e03242c0c0d40203486100108a4030075050f0385c018a81103000000c1048423001c0c01080340031303076080d8280c002682c6003020f0540c060302d108100502040041c0740005d0b041202010110312041e40503070f4954a003041242420a03a4002d0b003521031421051000344030400801c2d88110140d41c07900040b5031658038040e204072500b00d94007001a4040d100044030711070701c554400e01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 907224244 1250 907222994 907222997
    0xf24080115090806010b030402120d0e01050d020d020d050103140304080703060209060708071217040f060c020f0703060b040b010822110d08090f1c06020309070b0c0601140f09070807 80
    0x20b00300d4031440010704080d82a8405111100040140400c0d440d2449595000c0030440d001400341c2c10000d84080c03c01690f48504d141400001b244420b0860040d80441f40354041c840801c550f520716024004000f4142030105607420606552006844d0600004175001d840212009280f96480c6070780d0710010b50310800016402c0f40080c400403001408000140031624801c824001080030014001401d4100f0040c3c0c3c0d80382d07944074106000210707024805903201c968210f9001306080c0d035200d006906d8044001030420481c8a18000041441515404141102800c0b00d06002e50900d110044902c40d10075600302026285508006805056044a1420031131250482d01104080800002d44804035504142c800034000030f00741e10580f078440960007540500301c0c3c03050494110502c0950506040c0840141801d0780040461440c0a0811024004201e100c4c081d964035480349006989521084c452070689002c9612101b2803880c0134100c0980ca40b001428129060341c8a8030100e0f100c40c13004d000d203070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 907225494 1250 907224244 907224257
    0xe1909110408070609061101060302090703090606030c1413050609131b0603051f0b032a030406060f120f06020a0c0f0c0f0e060306150102160f24080115 67
    0x2d04020910081c8020040d6407211009107140810240841140381030046842c0d15000c424001651103403116a0010064500066900690300d80100240b54540010304800c087d1200010000385800c0b091800b140144c5810954880c04d80440301518404c0e42c0c040d80c03190451001030080702c0d01e002c10045440c0600c11036420741c0c625074281076020329990404000a901d1b01c0802c29980004035481c103d5070541d01d4a900c1842ca0302800011a0001030690380b881c01403080f0107403000700c1c2d0106408120b4408003c1c0d07952400c00b40f0b403110042005201d00c2400c0c1d03d41a000203400c2c484210240c60b0240c200d059890b65240541d90703c0c0080d44901c64010a00440303401010100d84054082101a0f11419010341d5441c100f5101c4480a1040d0707101070107140c400810005d1588000c0354054000c01d07902c0381c0f801c5c1386000c000141c0c03c100e01070074291148040d00400249424840c0510001c446525039072180c29649056014030803403009205d0b101044494004100030f08444910301074040c83c516080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 907226744 1250 907225494 907225499
    0x60f03110303070b130204060b090102070620010608062e0504051b2101050a14040b040e030d0b0120030318010b1002010207060c08060315340e19091104 67
    0x24440080d5059285d035400c514800c01182042e22038a4094245042041e00300310407040001c3d50362120303005100411500100030007400601041c08a0080480d0000740010349e103072680310396101c4048800d56888042e00c80503441c003080b40c00c131020f030405c8425503e032245d50401e420301c00a404050524910310303079001210410080c401000c0c1400c0c4072498140090f20200da450722141c00e20680090f489004c04800c2081409034513441c840e45200256400b242e03204901d4006030080901040401c014000017a80340e022010030350102d800404240c035000141042c1503107000c1075121503003203842c00382e10410200320407a480004840310b02c02c0513030011642070b031004081814840e0300c03041200540c2d00403030802c00300800350082850305c818a02d0550800d24020700041c0d641e40314101d091207070001d42d20100c1c0305002210307401c849016121301c04180320f40c0000d00d2010850303415582900000d401400350764040c40d00d540109070052450490103405800d10703000200400c20a50019840310703040000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 907227994 1250 907226744 907226753
    0x120b15160c0e0f07230913020405041e0f1a1e10120b09040309030212010b0a0b0309060a09020907201e100903020d0813061b030f060f0311030307 64
    0x1440d200e081c2d007070202c00c26418990b00140003954820300c114417400c0c10380d0494980e119110180c0b03014a070211076003000e030140b07981c50800074880c0c1c0d0400c54016041034080380d8200f1741610700317820740d002d059401c000d40d180410031042200d01929601070701c005d510b116032419141010b041204001c03468040580760114500082003c6905544840400c858801c0c181c4003501034812a00c454070161621600c514081c0e900505800e21400000c0c0319078a500e6440050f24425440000c00c0000503000d440b20381c2d2a4002800513400c1100c0c00c049901c43c1d0030004034001c8183c0144101c2076405083d04101d81c441103001e0703507054644281c80c6800302e1100a016403150007001540403001140d20103154400c440400c1a00b41075800040c5596281081f4080002030b0740001c0e00d001e01e0340d00b86000c12484c0c440e282c43e00300e503040000c0042c0c40e00c0d06003600034031007041403800011010415103080040c4c00d2542c08440a4071090300c50f200d02d43c0d0345280300704082400350350300520132a40202601d1414079166074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 907229244 1250 907227994 907228019
    0xf0c0d05070818060408040b0f1308070504062111040209090c03070e060a020d180b0c0f0123151c0c06090504091e0507050d03120b15160c 61
    0x148080000d080da41440f001e0726401840b1001c0e0340001024000602d010385070f00082d4455446280070300c07880000d8a100403181402654005100390382d2603040b040c0d64944081d625506805280e01c0360b49000c0c2d0008108460074204010410001201c0700d094801e42c461a0341d8840150582d50407a400300954001c960f41d18005a11980720001915124200b880009114114031444140140e13001c0125103041500018a03010020076460141c003e1482d958040c003c00703e481d0300810a80c88003051418a80740085852029200240020800740b002c665103424107443b22800314844601d4640420f00c90001d840b4880040400585840c200c4051810080003405071008152580b00002006000c120340c040768031402400c1c111414401c04419841d07681d45100f6052a02e00c8644003861003508121040c40301c0c0009040c000c1a4503c0705005003009000b444030300140141071403401c0b5107072103185031240c3c1400544281e01849401c1200b207400403009950740300da003502d030080b40703400008038040348a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 907230494 1250 907229244 907229251
    0x90a0e1504060518040614010b030a05070e0d02010e041d07080d0e09010905060109090e030909130b04030f111609050f042d080a0305060a1d0f0c0d05 66
    0x91004040d10304000c400e45400d4440c00e26500c56414102e0820265858401c24441402c00d030394081c000307840360b01c0e0501c000c2c48290f0400e080d440d880d40000490640d000041c500c9404141c000384002d6842070360884026036400a500e0784501c1d480c20450142d40b1440700055810009040000c0b0550907030164940d49000c4c0751803031810360080805100c8104280036408400c40c90b0306006200401020014480c41414080c0c20003082d0f84200003052070b8400c9030008020031000700200640d0300100050780c1c603548901d2140303004840c01c40100300c5c400401c0f104140074980000c180609500c07661703001c541c01006000010100701a81d01040d4060f9024010402948a00203089200b94074045441c02503803001003074450102d1200d010000401c03400410307809001c50880c040c11440101105c92a00c8010782d8002404884d0b0114141105035099842980506003c803405004155210902c02c804d445118005000c58400340100c0c008030640f145080e0001000110907040c210205000003c03100300700c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 907231744 1250 907230494 907230509
    0x250b04090219030c0903060e0309090a1b0206041a1816050a0605070c1403161511070303021011070b04050a020114070b0402090406021b0604060c081515090a 69
    0xc1c40e00b220506803a07240010762003400c050010482060000d40840441d00c4041c0415841d0002d26001500c144111100c600b402030001145081100b851001071800070a1200083c03070341c9030540c51090000400314415075015000c90301060001404210b02a4043c01c43c0ca1181d42d030a030a41c0d01003205201030b05640030300c0d4040c45030751454a02000014421540901c0500004105081c041207080d5010700c29648419070102242c3c0030500801e150000b40000d04a50600c040c601150322071400101d00300000b1f165507012811802950a9a118941480b0003000b503400b88925903990302d540e03000319116081885c40c0c1400d0802c1c0741c485d50586041124100c40319045000c0310811580c02045151100d0b0040343c406050200c150340d440c0003081d018002912403076200e80002c0c1000f2103a0101d80c040649107410140b5450800b1005566000603a01113907032901f4107245903035192282c04d00d54030412416001c0c40641c2d240ea000c2c01500c854095441054840030000d004042e15009002001003168 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 907232994 1250 907231744 907231747
    0x2150316020601090b03032d040b1b0105060307120305070c080606090a0e0307061a1903290118061a0703030e07050108010303080a09020d2001080405250b040902 71
    0xd454000b0b08151050300021402850003d821301e0640380001078038004540403140307120303529020007a0121010504001c0e40d003c100098049500f40f240c3c0d000c4c003c2150f002e40d6032509041c6580b581400c0e254110f030110f4056110283c00c1280780d040c454280e9032640682440340c5401840d84a00c01504074a42100600f42e21071001d004aa0520360f0712960702c00ba0007101000000d0340e542010b600c034070a54101401d00360b11075465401700e84c918602c181c1c00b80700003030101c030003414000b18206080c5403d00c416a0b0f05500d1540e800208220818582c0f079914036009280d5040e820440000f03800c1020300195525155904004940c04884d01e04e801c0101508908503902d6603010b150082c295103642441d019142c0014004000c145d130088031071415680e142c201a01e1507078034008240300074480180c010f58004905c076101010312400d1590404161281c150440c0a00002c0c0019555101c0544004003540d020710214421190540082c800e00ca190200ea039207255590f501c2c94260b40c009da006001c40ba40d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 907234244 1250 907232994 907233031
    0xa0b100305220309141906020607020d090b04051309020d06060515040b03181504030f08090a0507090c021009080c0601150804060c11010203040c0f0906050913021503 73
    0x742901007081c4002400c0000e6800ba429960080038a6450b10800300c0004d0458088010340d90b818907620b0b52003c0841c0e43c4590903943d588000e584840c01e561060141c0607401c044180d1a11965510054516451555240c107181c01d003407100d1136008074000800313290740c0d03108100140c1c2c0b04030450341d155020313041c0403c9803810b113001c205010002091002c07034403600300020003070311401300103580d808809400320318070500e03c800400342402e464072014400c00101c0b100708810540c100c032446c860030040c0d0380da0280681e6150032165860b0200360028025901a4904028101554104841844091064900d407100000b1360100741c6110040c00c544581b0f0104900c4c4071400100040c0d401498400c1c0600d04a2401540250140d0030260019012580302d04e50010340c04e01401e4665416011800215901c0c5080d06000b10a100d403405204020b000505001a144000d80100410f4030801000141107444140070810300030b02c102400c80e0003d400c00c08001651807488040e5100d000f40d050807640394031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 907235494 1250 907234244 907234261
    0x20d0b0907030c0506070b0a0e0a050d0215060103020918040201030b031006090e1c080601020307200a05101409130203091615210b0619030e010203070806090a0b100305 74
    0x100f0b40e0015401071206206240102c0c0c1e6891642c1d800070f11407040051b4034030351512207034103089002c00040c1c51482421861072031241d000030003003040141c01509668070385482c0c00450591040400300765001b168201c0140c1075500385081681c110340305041c0001c1da1000400400e05041d000c04011039034a41d106810001c4c903500d0302800e80c1028625000e44004640c5070403014130038103684800410010510000f0b511a40200101e400294105a40b2443c10450100940040c0d942c44511800340002000010703440c100107540e0f9a46111036200c40a91f032140b2402414241c00224000f80c1c8403c5840e000701c1c410300948011405400d80001500300d4115030400c048407160141d00001320940300024051680364040314005071b000000140030140ca02150481c005081c290410b10341c07001000030210602c4a20808050006216840034465401c40d480c0c128200d000403250400842d10301c80018000c1d00e40b8000c0d4582c0905170040010b903408103400411303500303044402c051003c685d40d8414800d03a05e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 907236744 1250 907235494 907235513
    0x81b070603020904054005010f1e050403210b0d050604140307020303030f090f0f0d0207062f120708040f12020d02040b0a0b031003030f2604020d0b090703 68
    0x3c44002c250003c444903240a0903150122001d421306e400d10700c245a0511130001c00202503150008001d00c044507800381010018130380c401d100098604c143d240708009420034012907200d80d8060300c829000c04070b1041401880c1103014060b411065854102070032503590900e420000300d01407402080985440d03e4280c160b0384110003400407a90040c0050030041e54000210703540035100410f900c44503210b00c0500b0f4540140009124242d0040380e0301d024001c4400500c1004000036a402c40e02280d84c0c0344011748210780c00600050500d0350100c004602ea29441542e00c10221502088032501c6000500c00d05058005a00841e84080005030822200b01d40186510103040b21049061400741c81d640022800d60301030000034007407611741d40000190f5031450100d81c014440d8000b02a41c914010600c0301c4021050702080700480e8103001e481d00c3c0644980690b0602c0414200c05821200041d0550010960000c0c403c0368402107070010400042c6000700505c2c080d010f00c0006065031802c5151a0445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 907237994 1250 907236744 907236751
    0x3051909050d0e06040f0501050d091401090b1806041e12020f0d1b020f0301060f0305101a0904030302030903040f0b0c15060127030203010504030503010f051804081b07060302090405 80
    0x84c0606110510046410036945000c0301c00909026039104490b403440000b4100b500005002c0c1c0e0442d000e06000b4082c10b40088c11030b20b00c90022048141d0f61501e00640200e0013800701e1509901c1000000c002540031035410182c02a51281d244d00b0325455a1b9140c0d0411b40e82d1901c10050b003050f00d03a2601c4410401000d901d43d600d5080000128226258203040d042c0c0c02c0801a20030320240d030000865171402c0d4401c4000e0246403035070b6910700f6200e0501c03698070020426048015481c001c0c81141d1942c0b2800c051000780c00013044420303a0341b501e4508030082e410282c00c00d841c9020803c80029400c10500d201c0004210740402581c403a584d45050300c0c1030407c03082443c41c901d6a0071041000d181c0e4001c1000c28999030407014980401a4002c0c24400039031790341c0000b0341643c6424144010315400c00043c5040f00c00f440c010070400d0b500e660510245143c01035050802c44207000200b00040e1218010300040c10003621031020098900e5422450240071b03610000200e9400240a0364505090044507407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 907239244 1250 907237994 907237999
    0xd0f080604022104020d02040203160810050303070206030c12040c0312030527030705060106030603020907020118020405060d1211010b040603080906070201090f0806071b020f0103051909050d0e 85
    0x3d0804410b02442c5150004069119040070100003e00310b54402501502168000d04215213a141003a4001d01d460129580c00012524010018a42d519991160010f507103019002d1810201c05900303014807a0400313051244103060910020300054004495544158041c141c0e00ca8540d155080c02c0c4110403c0500c450101410982000302d00810400d000d142c2001c8203600c0040e80952200f00350071030140c2c1900074410302444c00002501395041e08014150b0780201c919030180c1c1c0b11110240e08903110682b6501200c034140300d00001511705a4041540a03c014000349545030a41e07544000e0107004a0980000c80d17103074000502c164400740b107401c10f0b01105480800c1802c0c11078988401038050500260321504000030180d046910581d0004024114007281d2442d05848048460320b0300c0040f40c20000160710407048400d1304490500081d00c175038014204414034010399004401070000100300303d4090352000e509a07402c50f494802d0891003070040b0040d0054915050005002d10541d0340d4551 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 907240494 1250 907239244 907239247
    0xc370803340308160302040801021801030606051206130b032d0111031b1218100603080904110415020304050f1f0e011b0506040312020c03090d080c0d0f08060402 71
    0xd000030b811002003600300381c42d51004c8202c0225a40100c01034801d92304110001d5002160408007801c980d92a800c880500341c034280003c90311140121000e0240c00040305110b0103001c0484c00310b041400f0642540c0c0340302840030403a0ba2543c00401d1805c1c29018400c501c1c40c0610440e010345036402003452041c42000340081c80844142642a6481d0001a1403111081030041c1b03681d9032202d40000301c60800d900070400541c2468040c0411000d441c0c03540f0f040300305014000d6410080c088a01ca01000d40b40e2205e03000341050182000d100080c04141c40044601c00100310104520040c04501342c800e000e40e50046a8440c204428003030310030701141c402c4d40903459000d07030000b09552038054080f869800c1d24000c5115000400100c2e040c489000301d070380103540c01c0c0b00d281050040c0464170302d01c0b80340a504e175940c0341500c0c003811404901c1500603060680e0020b0000090910700100c41c9140180501119803c01040340320702130400303a031a0302e02e202050004c024050041c4c2c00c62400d5500c00c0c01104e045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 907241744 1250 907240494 907240597
    0x18090910061e0504050a02120c070b0109020f03010b0c1006090b030c1c0b070c170a0e2202090a05040e030306030601080a08041a0d060303020f0c370803 67
    0x100d102c15142d001d018031854803030740080c1c100c4100398142e034415000302c484030010b030400184a0702d1580c050641510800103220020424205500845100401041c0384501e943c0c42e203004c03020035801038007041c0b0260060b001207a45c400c5550081c0d001074121500c0004250200300b00b01842c005200d00100e000d06e441280c24040111034440c0c0300c81301c0d500130524103860f40e60100120f0f605401d900004140070312080300c919111190300c024282805854441000302c00d0300b41d08011410041d942082c0004050620f6503000d110f040e0090060b41ca006440811030503203070000103059030090408440e03035520200821000c0c0c039040102e1801041c2a078064604040c0903102c02d5428420380c000c5900c0b6142c007c45041c89509041d0031107800c0380d8008402c005041c0c0b00d02d00291500d40030204d490f800d101d0181c281c1708a01d8001520601024a1000030300c410008200c481c0404d09282042204d03050345040018034004144003d1100078032042c82e61004050b00c140501550030f8208015180100e042d83c00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 907242994 1250 907241744 907241789
    0x8030901030e0f0c0111030d0e030703090603090f12031e090b101d1801020c0c040e12190e030a0507080105011d04020904080c010932030f1809091006 66
    0x41d44c082c00000e1806506407100c901410b461446a080c540102c03602d000f50340e5041c14004000781814521175500d1210302565a60100c080d00c2550f04003810640c0c030310614900060460030078482e03501c528203020548090746075514803d4000000c11a03c583c0d1100c1d212002c1025a80c0210380c000300c1034503005c10b854100401c10201c180001e880711800e4440c2c03004610800c440162400c0410707000f900955959001106003a107074440042000e0140b400e246072503486071000b182c503040074904034100030704003e10301c00840f0600200d402c3c29024007040c92101c944a460503c200410300340200010810186020b84890856405a1203409904164004580c0400b08040038580054044451500d1600c2d42c0c100303080d047c45035074100b0301070390b04e007082d00c0041140c170074280c21b003006c041c01d90b06410044445580c03940400065a200300c0c0e401c01c01440d0403440741381000d440e010301500c0703a00400110806c0402e102a0013616200d1a0354014440076445003c43c0c003519018007000100c4050f0250b00300039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 907244244 1250 907242994 907243003
    0x150305060f180706110309090403120c080105101d0303040303080144070b030109091a040209160c050304030c090b0d24020f040f06021212040308071808030901030e0f 73
    0xa00c4c41041140002c050791408200240c035081480140243c480341054540540a4080c460340020380c5824440211301d114050514a4120b846c080c00301038095030326110460300c041011125500f40190059450699182040948051407081d210002a0b50400d20309401c80c0d02e46040c120b8201049025444288218030014001c140d50110301c03c04c0e107544401010b09203206a081582020408400014201c00e607800c8822901d01441070000e944c4000144100d05200071240603410810306000725044034483c000b0f42210b1030103440c120010807a15900c65086502c283e00948504a250100748426003c230b11411815000403107501e103a48042d0380d280c1c01030b001800030404182480070b400e00d0300710903650121108511030780300d42641d4507100e40ec1008461000d0241e8001840350919512203448080225082d86900c0710641095540e44da50071100180000c00c0001003040c10381020610f06005603241c005031508102a50716031a039040010200c84400005400f594071018003410b100d0380114 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 907245494 1250 907244244 907244249
    0x140610121401020d09030e1203070c210f08070209090303060916180305010504030801171c05091f020606220b0402090604060e1c02060a030c03150305060f1807 70
    0x601c5400c140030080d15940240245426050054280341c0050201a4030032803079011410f007150b5002c081800d040e1a160340b800307515002842c200142c4414801662810365140100d402d00ca075214a59915688480140050a408440292740030a4210442c07818000c11f80d804141c001c01141140340800026034109405811b914184a04100c40c0052a00c40c4019200180c0a5041040310503500c2c6000c03402008220380540c00070718141e0002c20780d1074130341050b56911001900104200e0785440c10146069400b20021000d00c18204050aa40d440c6c8001d5000c45400c44485039035a0004000068100304004080701d106032443d846100c801d400b002d001d10072403000c02000284035190080850002d1040c1714002d94066008540041c06981c00b464190800a0544103a0800c400c00080d180000780d0565000790320000c14025010303200d101e41c0c848040c00c4040d140100f0341c08041d540000080009800c162800d8000c0d00c10404005402015107802101d9942c6a28824101c0006103031148030780d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 907246744 1250 907245494 907245503
    0x504050f0904030f1d0a0f0e070f020709020904091a1e131b0305010e06090f0a0c0e0613020f0a02010e0303090604032019060c030c120207060e0102030414061012 71
    0x10711702c40403500407003004602d02c0440030b4086491591180e2014260a0031880f689412440307400c00260040d1060001c95105070f00c5230010101207041c60030700006034220407104c540161342d43c0003000100b5111030400d0403d42c200e81c4120140d0a00b2355180c0c5040d407070800d002e1b510404d0242800010078240304400d10b01500114121000350352090b11050200455201410560815000c0c20b0a000f000c10498007611242c03080303800d69928005201e4441a6a0b007002e01b4415001104011460201e00c682c1c0d48404000c4c040c0c08000c1501c210700e004c98109888000f0766140100d410120142c091041d0a1083c1210b401582035203824842c0d43d90311030004000404104003035170b10982410144a0200c141b84079281622002c0f0151282004201c09040041d1940c038104410500058042d2084880d4510030740d0343c240c400a40c1c41d03007803000707588402d00449649645115000c821242840a14022441804000120740402d80f02d14a0954007401007114160010803c0200251405d60103240a83c070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 907247994 1250 907246744 907246757
    0x60f0e0c0f0f04090b0c1306110307060203090a0c0f05130501081b0310050901051006110616200d031d060f060607051b040c090522020f04060504050f0904030f 70
    0x690b003c50f0252500190040001503043c0070302c0441000540a002d4a40d040300111008035038510089030b40103500351006240b60420032480c000300e019a0001d541c450320700700448045000c4c69a54000f407142940c40301070f140800c3e07041484249440a03210010f40650402844294145200e090702e40c001c4103905045410340401c040513a03103083c003801d14400ca010340c0400452a0940149000c2c003800c80c1c1075441800f204401051050280043e40c020010740c00082c02c1c10f80e03605401014640090b460700c41840064120403411142c1c10600c1c0304560340300030140000d1120508043c4c00e031001451805200c21032100402c203880b01c005007580e4002d991a100d64016110038003c50020b01c03500c0b40143c581d010b1a052107030041085103141d900c2820640c5c04209516007010f086030355124501845600000c0c440e004850113a03146180c160000205200626018010480b41d40541c0700c0d50080c1c01050001c5030030130040c50100c0070000401400d607441d1415150694005115001850380501800704 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 907249244 1250 907247994 907248019
    0x1505012609010b090a0614040e031b16030302010b040b060a080a0908090904050d110c0a0302210106081c1409040518060c09120c0307060c0503090d060f0e0c0f 70
    0x802d40054210f05800f604001c211300f0181498400b0b08124000d5442c0f01b49140800381e0035007458803902e008043c0c500069411702c0c0300c41c0b015404009130481551075510071000e18150390504030312102c004512030b03000024070252080034001503807407030350b41184190014021080d1042d000740401d03620102c20000080c403040246000d2846010b441c40da1604940d001040008200b40041c600080c282980c550345d02c1d042074482960b5485094140050704030010140c104010b00b001e0701c084040021000980304007518580415086a13119440503440f035110011002c6160000201031070b6141d95498912549206540700c2510751040f807a02d24000c0d656000040d40081c4401c900000801c003040c145c072010b01b070001c441c503402c3e0840039580d403103415007030741c000030f080300002c0c06051452020b030240400b035141000030f03948001c001c0f4003500c1ca0f000821100089549081d00419400d02c00c20000503818282c031000301c2140c1d015005403050340e110038403910843d505c08a021010341422510030030b4903034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 907250494 1250 907249244 907249261
    0x7050a050f0a0e090a050316060506041a01031e0906051e01030809060702030f070816080609060a330906140a03060f091b1a120c09010c050307050115050126 69
    0x11017040c1c016041d0300010034003804034150003c8d10030149011303103400d1059444001c1000200d4120b411542c52001110307000324031a5003c0d4004c100c500701140840030030401e04241036001d5655040c0c085940303a503a001049050303545984080f154201c1c154003900c0d5581940e4411885101e4226990b11803003001c25807004541d01080b100b03505000200030b4420507945c03050001e544c1c0c0104c0311090102490454085802c00300003985503c101306040c0109200c7d07d410b0343c031800030204181c5c1d0588820040841da03482c11003280c0c0000701050327140e11082c003103480c02510408552007900208016070321040742c0102175880344200016280c00140c0000c910300004101c4009014100004044410b41e00f0841c2c0c1224400840c20100d5166103115548801516400422880350b40c17281c42688050b2408282c0310114030b0042c1c039119606052107a10344165450306480e41d00502d03030880d4240e46808403140106610038401006000a09000202c203962460140c07a61458503144012100c603000040d8044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 907251744 1250 907250494 907250503
    0x4080403021c0c30060b01091a07120c120c02091303202e0b06070c09050604090605090102030a0624050304060b0603011d1609050907030605030d0207050a050f0a0e09 73
    0x500260345501c030038138101d181440150241ea00342c0c0380031032142c6c400020b4040b0f201c007900421140400c03a051604d00c1c030340e4419210040d40010402003080c04101c4d070700041c054690801421115440e082c4140c00644104203100c2c0c1300610610441262800000c00240c0080e400a0036400a50340400d0003110444200d1030480700c520352421910800120079100642444000c000b024100001c0c0900304c0d6810a000452042e40c00040141c0c19800c81085035903030940c041da170800001840031800e04e075152600400d03070300180c41400d00b0b6540001441481391051042c600105078840d440f41080c0f10086401520320003c8810106101c4004001000c0003030a80c014002a1402054076450396140e2040c07002c2c0b0b40c00c1100c41c200d00040c40c40840c0b032134014080310762001c02203540c90002990501040c840c2e000c5000e0321803c10700d510b64101013182c4d42c040c0507650802000d0350090044529010030000351103400d5020034020807072410031444d251120020802030f5068004900d00d02c1d01c0b601300c01c41c9003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 907252994 1250 907251744 907251809
    0x11b0b04021f0906080c07030504120c0b0d020d0b0d12030908091009030201020d0509091305010b03010f1a150909060120030d0608010218090c04030b04080403021c0c 73
    0x203074010582103502d2500a42a0b078241c40650780d400c0002c2e035031801d9180e82881030480c00b90104009000c1042615001070030f0704000c9124201d280c40c03280c1e44184859054110044d000d912a8010030601d400018512504545030411030325050117075a10f40b0ad0841190b10b91400000b0540c9551b400414070250408488a500000e4850340300ba107040034006101d100740f03001c100c0c010700442550844807813168081d2000c3c00d00081c05508191109501c811080e901c0b07840480380d41d52122071612040c2d80038441c0380e41c0a4001c07480400e46141d03407051005500030302c10301c1c10f10401d011a035064182860340103442c1081c20640d40810345840d9040181d0343c0f04140d503c60120581204a00d0b611034078040003610310022a20350034459286c0b81c00c04c0a00747c1c050108540706a101140d9107268030302c0c10030921500501150f1040f85060b4a94680c900302042c116000d495641002500300114141070300039040d09403040c034081d80c402c041943c40e005a00710b14070681001030180d007516410304802c5000c0240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 907254244 1250 907252994 907253029
    0x1141509090109200d020304050d050406021c110105070e01020705030708060c070c050d150c090303020607030908040911070b0a050c030424090311010c1107170708010606051206011b0b0402 83
    0x1103645c4402405c0b4041d600490302154180100300b8414101e602410696064070032980140601c4030042207078003900018811301c1810000c4600c1c02610150b000e11034140296150356640d54403002c0d030000685400b00d0707a400035020754400c14040040a00100e0001d401002e08480d480e03650400d410402d80100480e040203034000c5001c3d00c04030030020400074540c0103c00658052101d00c0c1c8454041c1c6224126102c00340250300000002041c043c481e03400340c40f03801d215000085c1000d031151654801c6821a508200c410480011218180700345003016a503c14282c1d201408203260003003091920707000c0584010150807412403005900101480a415082000c1c0d5040008140760b040040030080d6150724000994a0903e9285020340b288020154405455009048051504151080014405508210a00500c02c0208190100707009030320060000e0f940301c0e900c2c1d120f030701c4000700145005410141480074034280300d05100400c0081042a3383c01c1210300030566654008a40c0d9817120488441 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 907255494 1250 907254244 907254247
    0x6210b0f0a0e0106031803050a08100e07020c03100e0a02240a09140d110f0324040c0b16080702030c040e0102030121050a0b0702070b030114150909010920 68
    0x518500302c1040c0c6041341c2031980c050041e0542c0c3c08200c6011410100050000b820402c001940b4038004c4d83d80c66001549400c0320000c0c035a540506090300c0c003054628100580044c10b040d107403850200300c949160580343c40c08001d040300703024901d0f42c0c4104c0000000e00800c500070084009803800d0162044201185414640c0e600382e1000042c20100240200c15803040710144002c00b07410100741c404000c41e4407003e800c02c1040c1500400c070800c21501c031003030b6051041001c40799000028100b82c1180c0c0820f201b8100340f80c1041c0c5000c0826518980159001071418032149400c00704280d951008150804c03410b95842d0b036140046400c00403101000c7d5041404c09200d0001d144056004504803502503100740c81c0300441a4243e01d19001040006d081e591140440c0e10100d08500d000c1c41d04241b00303004a5143c1039440c1d00304c0000345c009038449a040b8045640800c0d0900b0108880e0f0303070303203545c1901480c139042007030000035904070041c0213501c0c40301d0f0303075600d25400c20b110704005600000d00701c50101e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 907256744 1250 907255494 907255499
    0x180510141c0605120609060f0a061d0414150106030203150603190c050a0509040f02120c030a050114010f0f05090315040c1d04031d040204080a050706210b0f0a 70
    0x107070250803188903207400b48a040c4909074000c500400c1482c01091510003900e9107407101100e40080c50005011000e1302039a80c20002981c071012407840206015003c07c0400511341400c0012940081c44100b140c59040b00c5200444d1020820300d40c1d0648680d0300f40103883c0c0d1500f1050303091501c02210080c3d0452000418020114207039400e500101c07121180c2030003204c8002904443d44e018941d89100454030074420103405e46000c0d0088031140c903028000500382208008c2c0c0b00119442600d001402d1600001481102c58280c0a541e000d014046450407901140500092982200d0b00c0c15408014440380300641092040d0300301c842c600710040440b03007644205c14031070018030404c4c1c5086034041103140c0d0015210049035400258001c106051800e15540d0f40c9040c0c6220440c12210301444110300741d00705032070b40c0da40b01030805051307504010480429245011480c10315903801010034045003110340c880d611008255602185465880412600f01010120303050260000a0550011005001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 907257994 1250 907256744 907256797
    0x90702060405070f05030a0f0f020d2a06120e012a0e03010905121324030f090203061815010e1b04061b020607021f18051014 55
    0x50364015400344041d52005981c41e880805404190700c500782e0550440c034090008288640344402200340114810b00e801c170b03000d50008070802503003c0c048481e07002c0c0c010400f50790301107465031054014500c0040a41503080c040082e01041c10800d0000840da15181d09400d00350f801e41140070400345200c009040300d0041a000220241e214410600280008409002525050087d10921608440540004040090b0b110000c1e404030354510a408400303480020607580c4d1900c8102c20321019010240c202e441241d00030103444400e0740140c04282041210700c007681d40490341c540c00404400e480c102003035106a03458146035508000070002803040c1c00001d0b9000009554034414400b080c03031180254031321244901c0314007540c040e090006200e050700100c0402304940e101c00060000340003d0601d13840d50b001902d00003405c0009407c203014000c1c501402d47d002040441d0031079a49141c1000c003400c0101007445004242049808c002c180712004000601700b1080b60081006810300050540b81d0f41d06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 907259244 1250 907257994 907258003
    0x90e0c0c0a03081e101517011d0604140f0907171005070f05070312020f0a030b0a060908150718080604050d080c031801020415080f090601032f090702 66
    0x108148400e0f803880c0900340c100e881c1314605119004150340c000800e03045c41007204e0329180c658098028400d0364007500f502c0c84003020b400d9008000c60800810441124142c00e8107003040a0b0009021f18146410b41d14101d085009480d03001019407d440c40954a1220b40c916005040d0b1049154450074032100d003003c80007040c034400c08602808203226645900401311591880d100040000030414001480028031402c200041400000b0025007012121104000fa65200410f560046660f40e06d1044050400241d150010f00309800c05003203a92500e011030751100c061a0617140c0040f030000000b01500d025045040c000b4000d0140300e800c0d0b50f02c48005a83d07550041e101034496100e11001c10402c1ca10442c00fa52140300050205410b60311061019000f0020aa540c082d0030354003030002061500518951400c0c220480c0e40b84403280c18001d007880c42c075290241441800740c00450062001c01d079041401c0700d24007160081032004200c2507403940380d481c0c050f602c510b0303000c4800c0080c04200d550004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 907260494 1250 907259244 907259251
    0x1c0b0306090705060a080901151d01361d100b0910030f051203070504170d0c20030607050a02011b020d0c021f0f11030307090e0c0c0a0308 61
    0x4003261840c0d291012920340d607401a100b400d502c42400c00c542c0c1402d0b4032405005412810b5000040b800c0300c00700c1c144644c0407029800c003100c80d21078801415526080017030300c035006100100c6905d10070250f00240c88a20071803240e01c5030413071080304000345546119a00104601401403101ca801d80d800b8101962103940c60035104034254107080c2101120b14120034264001c0c00010b90448045245582d00340c40d41403114415107107801130f4400c080a807580304000b540706440e550364803a0341d1420a01b6400b50321042410407140d0740e00818240c051550008060709105401c40117400600300c68601c141c0000d04803507801c64042c0164000d00c48a03903000750140100030080d4009100c40821020003a20307542e040310940c0c00503032000c0c1e292100300e4011845d88403040d001403c501c8882041444c44200d10000380803420008106c0c09246c0591a40031111024850384d02014510350700b030480340100840d43c0f40c0580018016801c000c10b034280760f001d0440da419a695015642c0910050401800d610000c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 907261744 1250 907260494 907260499
    0x110408100b0f100318030807020f0f250f03150b010e1516020a0e0906010b07080307030510030b0f06010e030c010504090e2404050706030e030901141c0b 67
    0xc204030020046801020190300024015000101c1482d04125100d11002c07114000d02d550340701c3e03000c805481035991415890107610303100b03102d007407202c4000e1900e03911003220444c60b00302210b800e02140020802a0442c04d0031a81840c0c0c803c0000e2400c100001035134011546940510340c00020131120422944211006400800c101c81c03002c80107580803119401c440c0e903c2044440801e11040310700e4007419a402c408101e051003122070360f010806180c1c45410101d2804001e2042203c1e1142c2081b500d401f4000004185040600c0c5a407804501d02010700030750b05064541c00021010303850300850100550300300d0503402c883d0400020019800c40c040c2c499a0005e03a00708075190041c10000380380b02001c041a500c403860940b400c6100c1c00180886084001b140c040c450b00d4150110b0800100425403202446201c014203040c50b145180001a40c820800e150402ca048484480003000783c0d40348403400e090001c1c080e81e0380300e02003c00b032103042580c85600d5141c2c17240e009010017581c8901081c600c00d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 907262994 1250 907261744 907261753
    0x1060315050f01080702030d020f04170d08130f02090a0209120706090302010305130c080d2c091008192006030c0c010b04050c0705100506130c020c04110408 69
    0x4080010000c1400c60254982004241071400c07082d51141010380d03032103406803050300d040c0f000b844c030400f0036a0711421040c1c00c2c1010110341402255409089203900c841d0703d0005055040f80040043d21040c0000c10030142c0344082c1e81010207010792103000d2464103030700030000c0170b00c0c2c58072581c140d0003500b1008006001e045c0303540010140348000100203090b20a55101c0d1000546541d00440180c00010503400440d41c0550450700052440c241503805040920080d0000a1070240001c00b03142140703901d900e811804141c80d60603180c00c11410300c0c840b441902c9021555607112100c800c44445680702100324851000c0c0c1f50792a03581e840d01801c0c01c0e407040c1600b8081d03651900d0584c980c8a1111100c0d82d01c0b103c100701092805442a00030105145040004101900d8600000c0c0854074200c17018055800006002410080c091201e840800c080303107000c01c03d9081400c0405c405003d00c890030144540c3d5000900c00c400e00030800b00b40c0701d5000610034040d40340c1c00ca0100240f50824810344003280719 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 907264244 1250 907262994 907263011
    0xc041514011121041502061b0414040c110609010b12010e062d090a0309090c020c040b03152e080309040c1b030306080d17060402030402012105010603 66
    0x400c0c1040300268a24800502d07004078084031600c2100e940003400c114103401003100260000c1c5c5078410203a044030503005810346e8a020701c1d104489041d0a522010324807003c1005104e030310f54041960490702c0040d280003501c10980d19090714840c2c0c40000c0c105051041904200305032805400102c12414292400d01044000710b0b0000d003a118040040546c5400c400002004c4040e0207038204503004e00c40900c0c1d802c101580c075040243c5074054031103084030f41066038400c05143e0004070041c020080080100584446080000e444104a45205110702d896588000c100e54003004400140d00c00ca1900d5035481c00d0800202c90f2001680402501d129801d4020643c80c5402e2014102100e419501071444c0a101c0b038204401007800818507000c1c03003c40c0c0a4840e015910621295030640f094a001410608015801e031034407281c1c000a50420251302290f030840d018805000fa0001801d6a000d81c994450344010b07500380440c0c1c000c0c00c1c180700010211194000c031581115048403010b4a01b0403103000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 907265494 1250 907264244 907264247
    0x7020d060e0c1507050c15040f0303080906132001110d03230103020a03110d150c11010c0e040f0f180618030507020108040c18090611071707050c04151401 68
    0x250040180c071719048071280031424184600791054546084460b54603290300e840703105030f010310140c10503000124140704102c00c000081090036080000c54800400d00d5101da0303122003410000e41c602542c1d9206400030b08510b40d0240030702e42e40c018020303c180c480850800704005c3c000d042c19505013000040040f041c0101c1240082204d05032500940340a80040c15515080e5440b10030100c242d0304405401080030102c1d003980400c4403880c24258021542e02100b80000f080440000d200000992410510421094014950340701028040d5400308080d00c0c2604100000c0860310351501452b03060160740b809403084040000d0301588549020081802d254070b0f41d860075602c020006011840401000e00998040d08a15500c07511800e10034001d642ca9808952104c0c80362031041c40103d840308402010400c1034060205500d82d451401e50512850707403140f00d00c0658518550b201e030403002400c3c006100c003e010411140c08040d00078000c010080ca041a1010843c1c8a0f031007091001003400716056 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 907266744 1250 907265494 907265497
    0x50c10060801150b190c050c1305191514010306080a03030603140115090506120109290c0702060708120c07230a08030601031e14100f03030507020d060e0c15 69
    0x480d03007184600b400645c642054a959005c1a020b5406205000519140d5030722070010310280c2c0e00c0800081500d04000c00f103085241c80186030708420798144220000c02408515003402290004a04000b90066031801a8000e201d10f030843d04141c0649203074001816015007215007228842d00562041e119082805422100c11421010321105202e00070030612942e40c01158020000030702619411821240840c211100d13a0002c0380e0080003542100a540d00c0c0406040c1c0c02500354030004040d141501d9148054030542e28000d108070300108699003400315000a6441c0700041019402c11400c03c4010b000700380d0031590048540301411280c802c004c144200c44881c20402000c01810200d0083e43c074001d0b580c000418080c10181d60b10300c0c0215030000f0b48917078500220360340d20000d800e00100701908503a103001403603444083c0003030808228654014003814212900341c500b207074031020a40f0015a0101d00d0500c0031340789030b0903c5c00c03200c103000d0b0204421148000440b220302c8000140102641103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 907267994 1250 907266744 907266757
    0x90720120a0e01020d0e24131509050a0512070b0a021609020c10050a020f040b18040605090f0709150e0103240522050f0915010510050c10060801150b 66
    0x10400b603d01d44e4141015106500b10f8a0b0066441c4500403400012820641003140c07101451041c0008c20082450004034800111406141500420303007008003180c18150980309150168004059442100364240046405891102101c980d07031100074000940d540d200801d54000130403035110014119820b407003201c0c98481442c003d4203034034900718801c07001001c2c010520a803507602004090001d140c0a001000640ac0b2035190316103d01d507043c1c0c0c4210048a01003000c3c01140b40070300a010968401200039407022a1140101d000c2c0c0d20718900b2100001540c0c80b0030098030514158420003600187d0311100c030103080c4d80810500ba100c1416005030880d400d1100b60052040405220f14200074612100120401c4415456400300b40302031811034004031107068030714290314140500c0d42d40c04e2120801d140c0302d040100c1229418000001d2110020b0700641c01070007000291498100d10a004a1400450880040010039a0360300c03024041c100d074100c00b03500c100344d4090200304480f00000b0b5589 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 907269244 1250 907267994 907267997
    0x60611073029070806040b0406030b0a09110402030408070f030c02030628060e1518070e0a0902070b22020901030506070f051908070c0618060e0c090720120a0e01020d 73
    0x22030b19140248001014001d811f5508035860f0700c03012000c03c01c01c0707c84e40d01850314001c0c000785102a0381020089811940ba169108a004000740404550703000141c80409420800d002c642c0082c1e4a01500c642c0d0100c5002500f50040804000b40310004034401c0070031074508401c0001c111503c920440868905015508280441c000400c044e04444070b440c81c1070350300c080d18250540400e205002c41c10001140c0d400c0001751080f841000e2801c2c0703845010018030450310190f0408515070b45007070701704200410343c0c40003c01840c001012140108d0116098640140841d0700658403402c00d10b0700c0303400803120314010403061a0511001e51144c3c003121022404c5060032811260302d100102c96604002d01910200141c009080011840790310407059a84c10b0044034a803551030620700801500c0745c21120320780a0300920101050340c0c54003040f160f0321412074a41030791071482d8400c2504200525011441140c41290f0401303c000010314001c01c0b0385c00035030f21a15030b070070601e03001241e90b150410580710 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 907270494 1250 907269244 907269257
    0x51303050a090b120105010e0d0c0501051818100503072909060a02030d0c140d05180d090302040b101d13020a050d06061107302907 58
    0x4010038400c4015000140452600e8920075a80720301d0300c20707141c110079030074040c2d01840030042000d5030300701224090f034a00a80f11401104855210300c00c0c80c4a00d0710515040c8540054800f0340e4040c1001110240d0760024401040039a014a52107801c1c40c0884640201403562640030400785000110f0f001213514050b0744800e44021180d49920300360001043c040c010b076040c8418003c690303612014084c0441250300960f00c4000700d0742d001064514100c01c0c50207010002600385661800b51085034050782e0542c0010410b5102c4806e1500040383c85000103600380140d0552002284d03106400c1c4040324000c0358280511107100d403c00540d4140c0118000101d08030380c510034040740901d01d0b1000c108800030300b40c91004001150060070b0303078440c1006000003800007a08489148482c882d140151145144c4440c0b00341440320000c0d1759000d40d02030145481c0c0c804550030585260001c2c03030508103000303844000b9038907100e141c402c0e542d2900e01c00703211400b44007246091083c1c100203402c03071142d030682c0d5460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 907271744 1250 907270494 907270531
    0x21e030a060f0e0708030a120506090621062701050606031906120f1401050402060d020d020d15050a090e03070605040f0f0507060f0c0f03050a0c0507060e090a05 71
    0x40200b1104030a1410342e0b454000c005400c0b00c06000500003400c040000e1030f03543d00c090000900030001c40764003608103480c00d010301100740c0340d801c0b640794409400d0303130031000040400703044212000ca80c1c0440c014034821401003028981907404100840d062811030395460382070900c4018281e4200300c0d4410740003041800060355030008541e010305001d0304010002202078940c40307a06140381021304142d402d003009000850400c030100c82d040b190500042c2c003c005034200b82d80060040d104c1d4101c014903c0d80c0205100721240c0856044034074100801c00100400d9038103c80000139040c0750b01c82c251003010480000581e204050080390f28042c84040a1898403c5950342c1c400241400303030003035840800030341500700051407100203220b8240c058001071034034a03c0d0600050491880d0100e000401c01c4010760f2600060025400301422581401c00340e03100c482c120403c80d42c400456402411034803406c000060802d0b0032400145070380074180e030345400036a503000c0c5100c02d80d0030581c1c25011442003032010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 907272994 1250 907271744 907271753
    0x1306090320120330060a091a030a11030d050a05090d080702040f0b041b09030b0a1e0212060a030206091e2805090106051909050616021e030a 62
    0x1001204600820b07001141c21418091843c40e000581d80381d000403c08051110781c4038407100d0100410720890f01024031441c003500880c00071203052044100a07038454658600492002c0e0441c005108080c0440d554070040f8100906016882c0f6003141c02070065140c1800028811b0301140c060140e55112a032900e4001014044c850324030319030540e401c0d41309112120050b41e40b4003179845694444000450040b04581c100b0080310f112a80c0f0189240100050b45181e941055541007101d4002044440a03964800a4009091107008548407410407400700e100d80300184e406400c000903241a82c0700c4582e0340b1001c0c0540400a030001035482030041c0409401494400d172801d4101020303a808003410018440880da2070708500c520240c64007501c1d140451189104007901e0700a04c000ca404c0c103559490504090030a10504690404902c81140c071440c186001d581c81000502c0301402a654807440044840d04921403070004911403154807201082000800c06040e1070304200401424405000e941e9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 907274244 1250 907272994 907273043
    0x1f0905040c0329010318030c060b09090c0d022709070506180d02150d0f0f05040224040b0f0901030f0c08130212011b081008071206150b13060903 64
    0x2e040c10035885250758410f840a01c6c900c01c0e00300d4401d448000529001d80b03820001d443c04031078494000c0e00c00b02c0800000344ac0000e08100e19003010b0f034172103038000043e002081d012280d0303461386843d51800700002210305100381c0040e4801c82802c3c0c00ea514154481003004958450b1501ca94450740f905030070107041d4942081011000c4e8401003c0070b54650b508191080143c0000c4078412a03142d4613016089041d0050007207811034803804d9020130203407826078009001c5884100010410101e0200c02c0c9800525640841c0c014004182c045500d5040d00b214071401c1303511600210340028248254a481407d150258500550070b5407610700140d55250104000381508880c10baa0000c12041800d007401d50a100b01c0582085900080c1d400500d4101d0140c2145006802c4160181d45403404200d400030101c0e00070156840e800c0c800320b01c111a41001c0000d410301c5559000c0240d40c004000a00c12403203002000c0128000da138800c0c8884d960b6000761030409041c030014010128080304034110140086c23 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 907275494 1250 907274244 907274321
    0x9060c0b06041116052a090f07091a0a110610210213020301060905012604030c120c11040e120c01020c060709050a090e15061f0905040c03 61
    0x2002c1c1c02c24580224003501054226000e076440e4001110400f01a4001e400c00b8110400c2405000c102c022000003183c00107000412300411401d0039004500c04074842c00070000104403c285411611002c07500c1d400040e0701c00d0a080700802c1e082824000740110109074107101d083c2070720300100440e20b07000c0042c103150802078842100700031404600006958400106103280610b00340140c581d0b04084c5c028148220b42e4003c07074184007000c451036581c041040400c20841c4a110220b030f5041d111880c0c103a8407403103a40750041c402100c602d203019096500c50800ca08150045544a1a0b11600c40134082181d03c042c0e4400400e4000b010004070f0303114180700a000710002071000500d0b14400d2a10b10b410800c2c16100310001800039902007140d0315085d1a4040600b2107280c0403c00100760340b035581d81e500000c01c1c420014039440000106e0f40c1d602c480d0300c4003601c0140c7c1c90300350031941c20003001802d404d042d000d158403641c64241942010340c428840d040c0714449044e020080e0b50000007041e041d0b810b411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 907276744 1250 907275494 907275521
    0x1211060c18101b05161e0533070b0103050a02010801090b0a03031d030106030c0e1006080a051905180610051809010e07090203181f020f1e0a09060c0b0604 68
    0x3c1c6140c40c0c40200320003807500200b004001b034803894101c0159182c8032140e6503200e140700303610007100000340508080c2d1164424403440e207451540308200c4a062482d0203503034070181110303816200020501c500452191091352007681c42c0c0f04030b0380e00d45041008442001b2200b54118441c48024070010340942d5540c02030301024461217000c211550002802c1d00c4103500100c504055150081009007000c118054105a40924044445041c240300800c00c1d03100901421041362101d002c1184204400f641c000d0070700103244180011318040d80b9130114160b6401220403a803181500049d90301126144480503600f0003032403c1030b18020030918840c2d0040103000e205c9255a144091003030001c0c100304000051210240250b01d178502040b919130b0709498101c49035131640005124540c80c02241034007102111002000588032100e8441400180c0220344444140300f50805c0c11502d011425005060020101c0d44c80341c05194450804407082d003044900204800070780e402003110380c40c02e0f410242c40142117 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 907277994 1250 907276744 907276753
    0x61b1803030708180109170325061a130213090b120a050a0c0605280e130f0b06040f0b03040303090f111207080601031211060c18101b05 60
    0x643c1c032145070300d601500480e00200e01e4080b4420039960416448001000130b0f8080b69480c0101030700c501e403244107690007601c50f4440da0949e0f141c4010b41e541204076103a0070440070801e28003075000100050058413800f43c82013403011684160f40410b03000304e0b0072041010050a807007600c0e0452140181c2320b46503003294004080828400c166030100202d0040d035000c1c00c001c1c1044483e03030a01c6400b812071500300904000c0c04001da640c82605c05540c0540c800d029104941195503a410200c4001856004036076200880170303000c1d0365110f40350700f005241030500da000b0485003240004205d5113126601c280c508601111104210201005000d1030740701c0c6c06800d02180b428100c0d9992000000c8041d000c8410340108410182d079428031350500d4090b0604140100502c6082061056445405100040c80f0380c41114944003000e100f02d206c3c0c00340082007c112221800e0a9950640f1a080000c00000d01c01c0304000541491420300081590983d881e211440710b01005212075401d40d008103000e8429218 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 907279244 1250 907277994 907278007
    0x1120c2703031715010f050c070e27120f0f0301181506140d020708040e0109140403210905060915060d080412150204030303020408061b180303 63
    0x301003100258003500032a04080303041d8074001d0070120000f01c6001070051010208425242d101860007042402402e2a003500c0508410864031441000c0000035a80034495000821203070b4030344058080c0c8000344400b180441340d20034000840b0702c3d010340c64107164018400c40c08414294402861943c10b0001002e10305004800400707043c0d030080e0f100341102500d04c00f161010442034440c20302c541c0d146400c0e080c88146860801460711992003034070005403800041e40c290107a03e95048880840d070040c840343d180c0341e8400541d44030300030074400d4207003290178071107a0450304100c2c6410910981c0c1c540c0350060f0302e0308803403440051a4803a22211180c180e8480b52030b40070034800c00801341304488440003800302c440c0300c60740660038034005800c032030040700202c42c6140002d8083d000c2e9802d6400051160a4400050230402424520701a61100c0d040c8000740100500d035158008005a441000403203449880d410440e030010b00c0e102c0c004104c007034000c2c86521034051404040c4460749200500b200c0c00c210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 907280494 1250 907279244 907279277
    0x1808040b031504060308030105031528240503161505090616050c0a090b060301121a130b010605120106030b0d05060a0605090709060c0b13050a0b070801120201120c 72
    0x2409908191200900800100001d1400700300140990070030344100592421b003e0001d4400c00050103078335400d509030f51401c1c400c0460744c1e44401042c841685410800e107550010560494400d401014064056400c5001c10810810801e03421141180701d0882c078441ea0841c200d8840d00685000d5034040e60030403107848000740307020820031801c0c0514094541c04804404002500e212503102d0305103142411030002c0141d83c1c103c2940c0c11a290704000304040c85103490032526040741d504619000381c0051045c031020700446041040c03400d100d00392002580e603c0300030643e064002e01c040c80d5031241c00d41c401070000f94420781112003814009401c41e040301302142c0d034440c1450001c540c006407142d81c0e41d10401140c645991419045882c6d800c001394403d04156000340342101b12003001c0e2011a840000c81c0c0c005115030502101103401ca0305807080c020131840c5c41d10444a0580b6008000782040b800442c202c044803000382030a0303034161034841540c0100500305002d0080035812a050107806030b00d2003c1c0c0c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 907281744 1250 907280494 907280501
    0x70e07020c040f0c022b03090201090b0315010e010e0603010308090103090c030b011409060915131e2f0c0c04020d1d0706020d081506030705120108060f0109022802101808040b031504 80
    0xa031030060459035440b0ed03620004150000c001c40300c0741044103030343c418442d0303807101021281501e40100781d00d0395540742c003001640584400f95008240800d0003000000317112048442605032500c1201000034440c00c070080014440c4250b92480e03020243e2404a00301c600055500520004041c0805039101e00c04130640702190116a401d4103c442c5440040749019468801e05c0365581c04103c41a0814510b4004204c0a00030300c0d5041c4145800003a060742c04140c200591150440018015541c0c0c6030502428006031940030326244012000c00b004021048011460a0640f00b03a98000c00071040d110b40c0c00c0386e1a04000d041800c03840c0e000030280c0d50544441c0011f5218202c0c030380300c541c1e85a20390750b0b407100385802c141e1050038190040d5051040038550724910a0450706005d0b80540c4400c0b840e000c040a03c000300001a81d9540a0752400c901d02d40c01007051707840303100b10a0040058400c0c00034407210086010800410540f0100400e004200c1054007954100001d0307100c0042c1e0010300000300e0b048 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 907282994 1250 907281744 907281751
    0x1090605090d021603080909190f06090f0e0c01140d0e060103051002090310020f120f061219030c1b0603140603030a02070e07020c040f0c022b03090201090b03 70
    0x202e0b00000846007449404101c095840d01c030140c842a009451501c840515000d0500007500c106854004500c401205070912001d441541904204080700d00c41c0d0080100414414401d455041080c617240010071032203002c22852102000d0401150501c1c0110b07402c50b0801a1415154000d020f9030031f100d1618030503c0300d140c41c03031070007045154110708182e4508003412840b04d01003030040007105a29240402d2180910405600150326001221400c0d002405640e4699490700c00d444100b12803010011811801000d080c0ca030b0040101030090340548070070220462000409056941c0400a4412a04407000718000c54540c04040c2180c0f00100c131000f0b02e40d10200000c1d443e101c0000b03102084c0380c210b03900480d04500562a01008040280d02c503c418400c907240616000c0016081c140207005440314018010810007000d41c0c1140704000401904032053700510645502581d10a10040600d03840d41e215042244d0f58450068210064500c4060882c1040341c0044001110400080511701 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 907284244 1250 907282994 907283011
    0x8030d06050f10020c060a050c100b01030b030703080414190602010905061e0f220606140306130f0f1502070b0f0613020c070305120d1503110607020301090605 70
    0x203840d0320304000c11102c84000d4119501c80d501456070a122180c000810050f50038003030303410301e81b1070201007804da8007805414034880503409811020200c3c0299603001c62410b05007600c04025410703405043c1031351000315000040030360301d040006020101550389402c0c0401e0006100c50344c40d00034645880202069903002c4400750391110090300c00c00800b800b206a11890701224000b180202410701c070f0700b2150250925242c804004046a40f031141d0380c06c02c103000c0c03800c0086140f44d00c42070b1801c10700034030305807242541c1d02001d0740d4103184620300418001c0c050f24440040290811498690b8540100c2002049401440c03000c1c004000800c0c00c2840303002c21940d0013006881e501c10342801041e41c10001c201085000e0003d08110350b594402c04492030742a80c0000040e164185c04000d5403810006030000f500a00c40e40d1142680040e046000309903421035a00d043c800b050032038074440300c0071100d8080284010200b925404441c04c0050241c074000c2d00080020840000580340c00c01292019540800c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 907285494 1250 907284244 907284251
    0x60603120819110301030b0901060306060b1c0b0a15030b1e0306070e1003150812070507080304050f040c0302090d05160605070218070c0501060e0a05160806060d0608030d 75
    0x4015542c0444440d4490101000b84840f40301d9540d007105602c014013004101d80306990104040325400d512680207542e0113482080540c4d11202072410540118510101c440080080c0a00801c45030050003010203019001c5a0441d060142d0f2a810b0080c1c10184006c044e03a035200345c0000c1e9143c2807094280a9030289112107405100141400c0050080801060065002c3c049901da103ca90320106155500d10300016800919800c0441c1140170358018541407103280444002c0c094200002c0c08803d00c540c0803112070941d2066481c0d01c2c1c0c0600d2180329484080b000046210782010340041c480c811003032500618258080c1c000500c000190041911035521141d80117140f80c00f0030078904090131041c00c10f141005200d6002a510000c0119002c041c803120b04081174402e401156070b003001590043c000e1080e9600c9021045017164101c0744800b040342040d000ca410007040303031081104c503011946c0f42c007a40d5482c1e805014140e40088008250240d07144800240d5200510140c80492072141021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 907286744 1250 907285494 907285501
    0x50c010e0d0c0e0a1d070b0903010605061b011b092c10060f0c0c0918020907050c150f0411010210060e01030c0e0c0a0e040f18210e010c0606031208 65
    0x360304950010f01800701200c41003118942d4260001140700c00c8a84c003038101f075511055400070038050b060f158003140d000500421004d1400d4403944004c0c44c000750b580c0c000c00c4a10404001546000175082702d9401141c3d40c0c1c5e00c00d000030f014280e42c1d400c2e01044815407030541c480c50000100014001c840c602d027001c02c000d0303081c80103540c0100c010102940a00e07040010b9041034445d500a801503120784894903684500f648051155082a4000581c0041848045103008503028219500843c0d2a035054003c0004600d40040c040c1016802844200004109642c8998480e06040b07450742541d815441869514000030060b40181c001900540d202c0708110b52542c60131110a03206034100f090300788004820008044901c0060700c030b001c000d625100c008000c002011400030507403164900704003801d0900c00c4070001c0361500590310141c898408448407610706c00000d0380c200310200b80500080e03e00724000e111507200390308001442c0e004d40c0002500940e203558050045607841c1025001c9640705081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 907287994 1250 907286744 907286761
    0xa020907020d0810180e0a05030708041d22050a140304080f0706050a08041b030b15120709110c060106090501021b0906010309060207151b0309050c010e0d0c0e 70
    0x284c0100480c0082c0510174240035100c1a10214003108000040e80c1d01400d094070f01003000786914064100d01070300da039610f084c00c00100c154024054982000e4003000b441d69283c50583d07080e44903c200c104201707101083c107844480d00207454882a030780d0380f140760700130b4000c0741e9101810002000c2030401555228036200e42c1c02e062043d10680c901158000c0c1508110003904501101c0500c00b02c2d00d0062665030b501d19080c00010040403800038a80b0f41400c0200402044144060280c8441041442070f0080401085001404540703820360036041000208001c80c401d402540c0041400721856040c042d5800043e850401c00368820400601030600400c00d650301030001400b03415000c000c10a40da0011008a142d02d4005031206040581c1ca09040301800b486605881c229603101e1400fa0351850410703c4c1c0c0010f0700f01020614541450030380146441d0f4080c0c80343e450500d0344000038200c0541a040195090200c807403119410400000e401d10000b0300a91020000d0204034038500b0090a010a5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 907289244 1250 907287994 907288007
    0xc0d03050709080f0c010c0c2411030304020a170c0402030415050915011e050d0c030308010902070510090f0803012904031e02012a0b3102030a020907020d 68
    0x8500880d402440040300d00e02404151000345d030a0a007080ba416074014505241c0c440015030185061030f400901f8040c4403040083d040c0030000d0103039a024520f0030350070079440d00c900c03042d140254000c0b51100c0030061b4800313a81884214421003800c0d034004500d0b40c40850b041c0d0b48120b4086a810459424843c00304d8850710409400c542e840c40240041d0302c803032080207094041802143d84e401014183c3c408107a600c03104c1007014100140c0801d20030300062404503400c0c18580012400b0901034000803401c45d54502c20344080d20b0700a001040310f104656540780c004d000e01c500545098814800a0000c501c5000081d4000c02c0100161141400c44c243d03180d242c1e00201d062214418410003041010403c580102c60143c08200380041d5150080c1c40165001c203c1e11049603c0103440c03500569450040000241c2054041c00b481040c0e69204405000144c001035001800c440e0000c5580c850384028401c1c1565562001d8120b6100d0b420b01e1700000c407038050440d04540140c1c014220204240d0b40041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 907290494 1250 907289244 907289249
    0x4170118030518042309210708030a090602030f22030509041802030f07080f030f0f18031b041503031407150501080601061b021509060c0d03050709 65
    0x803500c1801502654005002e0320030401000780700414044580364a03520b99010040102c03074444e01c1000210300c0130b480d214000301214681901c0c014040e90340901640c0c00125848064102c643ca4a050402d550300c1402d90409003642c0346140c0d0b540000703000141c00d480158002d44602014030120701c0e03c003488178484070800c0d005035980505190a00002a080070a5034081c800807a030105200600d1a46a010301d0384204001e0741c540b003800c3c0e4400c90400040360a00588181da0b0654990744900006140d0f64411a612849590780c10003003010100c011034043c010340b540030394450029142d4200040d1510031110b000f6405000b151030030399040e1500f4861018049000c65400d1070003865502c001d801d030007150000411000d0005070300d0017005015650041d01c2c800100c2c0401c4036584404406545010900031180400c11491004186000200300307202c000d0350050882070300000c0b900004d482c3e500320090075500548103001d00310414006020343c8c1d003610079070740c0c0008991a02000003040b00c107056 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 907291744 1250 907290494 907290521
    0x50a0c0e03063c1f060c020108040204020318010c0509031b0604090e0f120a0e1f140c0a0c0302090c040308031b0f031e13020d02040b0307030c12020108010905010e151302041701 78
    0x1b404100140d03040b1200540c420b4045400603143e6880288070f085035085403442da242540303040802c0280c1500038000c3c0010000580864a100851400e4802c01001c04807205a0003241440100904c500c15080a002008a08180c990b8035080c145100d107461540e420a034045c00010403070030000e56100e4400c5e407203214101c03440f82810030a0040e0221801c0340320f030740e6400c11003089408100c620140d030480f0b80d6038818400325088003e10381040380780e42c40c0601040b03103e50032410210340880702c11425281980e4012146510b183c544030b820b0f501400010840e8100040c05110780d02502c0c140b0780180d8890b5000e0802e5042c01a000300c0d4205001d280107041d00fa001d010300030040090384994031f60350046a41034500207041860000060f25010a641c0000d207a000c40d10400b140b0181e800c0400b00d4141e100ba2100361131031740c8401c4604140c510234000c50200e0381814001850940c0d0855005840036809441f0210208030048008166401038009503a015044886140f504200b40f0076206004500b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 907292994 1250 907291744 907291757
    0x7060b010507150e03130905040605090f421009020c070302060711030a0f03020d0302040e0408090409050f07050a1202100c060609050a0c0e03063c1f06 67
    0x30790f1840c10345240100303680070701592020031130f00c1103030300b04215a00403101d10790001c8019640d903a45005402c0448040701e0f181d0400001c5044060000b5008110010440c0074001c00c0313404401280079040040e40890399001c0b11440c0c0b0384002d420318042c0501c503502e00b03120046480c00a0004850f03064503400508014030401c801712040c04040b8102d01a01e42c1110201c0e9220007904190315800ca44450b4660306000d0000d92904010f078158400d40410303c260280c0e8004004910160102d000d079100f0b241c880c0446400080c00100124001c0c8041c1e00003d01c00074800f007058039202d00e41000100c103450703660b111002c2400706150084000300108407425102003251031b990f020a18011003014107800b07004018101034100203d642041001d002d49000401142c98107402c060050504a560040814487d20110070b503400c1c04902c040c0f10751001d44540e042000c62266880440d4126072a003c004091500d952840e003034413310320f900507007146840000600c200c2c00220032902050313203c0010f0000c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 907294244 1250 907292994 907293007
    0x20d020303070f0504051002030c16080604030f0c051e07171207050a050d020a0c090b18060d061104060212130b1308030a080906010918080c0f0a060207060b0105 71
    0x1800401c480e4012118a80201c1050700080144c2d9680103540220740d03c80000d9031781803030031036000018240d078845050440391460a120800a03000c40140107600151b0081000500440d020f525500762480e03003442c151f441284a0340b90300d401c24140c9081d00100c2e118203044450842c0c400c100e23550241071202d40d04e00284140f1245182d884107041d202e201200004140e1070140f02091203003201c926040402d60f01c51211400b0700039203c08030703900225000d82c1344200109140c00644201300343c008000c4c0141e4540380b41d000401d0591400201204d40c040c1c0d002c01c10030001401400350251001c0c00c4e078001038881d0b08052000e07042c5404051160000749090051034552000101c000e402c40b400360021580da1003000d40039503072a061903004000240b000164802d1901e5019a20b144101c04480560300380d030362101c3c00f444c240e9014250b10003101c42c40b60305103004104110700510b030702d01410b403c5407101c5c40c20609041c14030071400d1044c1c81d41640400d80c80188140c5000b000d916000c03d10b01103117040c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 907295494 1250 907294244 907294247
    0x10617031206220501260c0915030a030c02031005060a030305030a020f16050106080601060c1106040f080a0312050408072406170106151403070903080721020d 70
    0x42014007000303003100d580400c550f9111040d610640424018840e41e04401800888000d0039013071107101000c0c0074401000e8440100301c00b505581c9407a03100502146802c800c200328071001d0180c4010010280c4580f61215503504002d80d188042c4a03840300215a03645004040c14101020002c2c0c1d109401c003010065541c0c0c030204c01c081569810304000f600e0f900c50600f103034024050940c071682c5e01c1000160b2010403000d1046117151a0388244002c4c40302030b80320541c040d03c075842840760402051044900500003654144040d07400c2102034a51405d060380c903503085120501640c0a410302d03422904440c801c0c1030380449101000895504240b0250809076503140107842a942c001c0c2241a0300d1064807504a0400201c43c00500070410502c803941e04e860240041c016143e9000640350300e085000180020302c403011042c95000c0b07031100c0c08440b031041c0d50045645c3c001841001000092413000c40000c1c0040040c0000c1c0d0300810001c498012050039069220005801a0b000e5512141c04410307001d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 907296744 1250 907295494 907295497
    0x90602120f1b0f0a0c15020d0806100e030111040e180d0804030c051203061e030c0d02010516110a06020319050d140a0c0e060c1002070f15060801061703 67
    0x42803240c0c0341c802903541d01c2c08103801c000840003080072134095081214280b222454200c1c1c2070712408034180080d440d8103103041e6580c02d211590f107008600c0c2d000c005401c03407800c43d56a007026102d5040c80d01600603038100107821035030104041e01c1d40c0030b0081002d1104800380507610360310149c80c1240c0f4640d050400c00190f03036148884000c0c02005400c500040030140b14080040030658000300b240c0200e1445600014550008c86126018180c0056041c400700e2110401d02170801010300644800d50500045c804040390412080e030512104005c0c0c428640952580040d0f454007680da40d01182d560041006550102a03000000f154414043daa108100903010083c890147e410f103141d859000800101c0035015015901030f03401010410811010815040001c464526554468003074450204100b074a00a403442848598440c15010a520322158000c00c0c006015080000c25819a035903442c3c5c1c85284480f03905400da480d40d00410050b071007401150043c0c40401604115002c84580e465600e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 907297994 1250 907296744 907296757
    0x2b12030524100306030f05010b1306140d021f030207060612030203121b07110909070608040b0403020c1e09010e06011407020f0d12180b04090c09090c090602120f 71
    0x5600b181e442505024020340c4000011a400401480441287e040041c02080c8031440180680748003034400000480c18400d0f5000c0d258000007401120060754203200c3c101c0c1c0200e90898102c1800604441c201d214000c08221564603541c01603502c07502494481d056807242e80c45012880a4441c0309000603070017000703440c5c0060f800900300d9425511030341d00040d45640c0c1185542000c000290306014014140044190307904143e4406815880f460201c81e41c0302c4643c82030b0800038040c1d1002c02c000888104c50690400d010344111a80c00d15403400082d00301c0c4061007480402c0c24403021700d50075824008140b90041203000ca15603c0d502d407241c006814160062030000002500068000c11982c61481003925800c02900d20b0585070840d00d055000c480342d0b0842000403a480c844030742c2d54510701c04041d406035410500180c2c00c0c03500c2c00c14080c02806080240e502444480000860300000c0b500c65000e00750000c0da100c190301441d2540113818540b0340d01c0a030440000130000c1c8458441c0150031120f2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 907299244 1250 907297994 907297999
    0x4020f071209080616110c060d0c0912020312030907091d160503120a0c0c0906030507080118080c0c103617070f0f09111303022b12030524 61
    0x5d04403e04130506e070402c002a124654010401302d9540414841940410555411030322090b01141c1c403aa0400f0036209030f450b0003541540921342940d00014400055a0045100b400306c40d0103030b480c1d006100645481c002520940031109440000c0d0500400c0f0348000341d00105482d1850a05282c040307070f103420002d4408211280c0000341e90340d0b650b1003211540d649a030424403ca03002c2d81c03507a2016018140718801510644181c3c00d0200e480c04040c40350302a40041403484806030b4a0b00e503515080361300f042c1c02e084001e0107152940307a120b496402d400f1b48000e403141c1e941d14440214240d8001d005100303100b034014095920325100710000f40e03c0041d90a441d00c00f1078a013018031021115a00d41540ca40040200c85140c40c07000030f0a40101202e08155070621005004400692200304440d000d04507107034444038190f41d81000503003400700c2c4060f480000c1c514141030101e5103c020b0b103e24902030301c04561145030703011420b120300d84c140b02c4c03c1e0b08108614104030801c00c4102e032080c21140d100200a1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 907300494 1250 907299244 907299257
    0x10c0509040f020316050f0705060906181207020f0f0301020711040f090c091518140a0b011e110a0c03050d02030412030e0402190e040f0608071404020f071209080616 73
    0x45540c880900341d1b0583d89c0e018044406500d45484c9058541d00261400e450105010751681034585011454600d112100c0c040d15041803859004c001c0d10007049881c0d40c0c0c010b0070012198000d510f080c001450a07074010310b07006400040c20002e200c01c4a0044400c14080d918115860000030800a0a90116a11105c0101d000c030104442c0071a904c4040e44900004600e8103007444810740c49400c007204c2c0070203108107000e255940d101800c0556910b1310f11140001ca44110301c040410340340705c0314a0450411720740482500ca5492800d0b18081c030702d00050383c1140d0300503001c0040110400007002d10b000b0b030b4805142801c1c50000c20310441100c00b0802400d001200703c805819843c0c60b0305854400200320840d5001001c072400107008419100300d070314041c0d8280501140c2c1c80b03001c0e00407042110100c400400e01c852610150195242101840c103501640820041c0540e040b4040a44222805181c170400d01450b80b42c40070380030604c150b001d00360907000320f41003108965000e00d0559042d1520309012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 907301744 1250 907300494 907300507
    0x405010603560405040b09070f0e010306020c0723130b010503042303300105280b070b0105030f0c060a0e1804060f1a030c100908010c0509040f02031605 67
    0x503400d00079070b9400540003460b1000308018400c000f1b1a15001b0b2440d502901e070040e1b141c0b05503814038035040c0100c01101c0710403001000019990350040080c40b00c001c0236950141c1d11590344100c0c80903000d103c0249608450490411454146103240192049040070426007045400117401400024405412221140c6034529070b4140701031030588042001c2d060302c0e0748142032481000c8010356044845411407840005a51711000e8a10080c1603500040190208100e0b40e42180b642115182d640ca03500b00d0b00000000300c3c0c001c1c2c00c014001c110710541d224840341d07050200f45498103030b07005a828856481448501c40300c3c0c0301e600444a001105c4d10388641c45801c90004500c540f03100c000580060001c40c000c000c20f200c441d6001d01041c0c2d000e54024405000086845048106000d0352503506030015885000e00340780480151001800c14242001c0039075880d1802821140c111031060081400081c051480d80740c0b5110b9501119841c0c0800c6086040010280080e912800f00840c140140025174 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 907302994 1250 907301744 907301891
    0x901030b040c240f0f0e04150f0f09050f07140a05040803070605162606031f050402150f030a0b01021e011b02070312050a05090405010603 61
    0x40c10042e20702e10f40e105650215040d03003009042103016580c4002848800b0400c034682c4138604000400c8200d0703503101e1a904100c010800204040031030890074058030580010031004002640c00289180722404961500d0514044180e0f140100003c1403107940c0c2c1c0400c180960044084c40001d051242c1c100d8490051031015201031040f03400c142120310000c903c8104011b070603045141304004103000c2d4044a00d5010042e504e1450018aa01004025400c8507245800110800e680881c0c0182120700e144075440040c012940e00d0b44583d80705d55201c074200f00c19420007101a80c03800d43c02d6000107180c51160740308124030380409800c050005444800c00d000aa1082001801503840b50100019044084540c640244501900d0f01024071403078006da502640003258000c126900010601285003154004444940c05040c60409118050140802a44072485814060a1562000110505a1441c0c0c2d26440352a8445044007a1039080c090044181c184d040f04401280400205c9160001c07100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 907304244 1250 907302994 907303013
    0x3020c1911040501031b05030d211d03030a110301050609040903030f06080d110c01020307020d0f060501090c020606030a15090602090d1a090307050613031808030c0d020c0901030b04 80
    0x31082c0e40181010004814001d04680302e0042e91030440c030b10051146e8580516032901100c0048201041400c1200c03403e04905002d846030035540307148002010b00301c3d0358115503865a800b4540816a0001c020002800c01912900d60750310b0000210604540c0b44c98000307244c901c02c00103458040ca481c2c0030b031202094003e07040b10111400c201e4003404156150007071a907840e00240c42c01c07400507002240c0101c4c0c10b031001c981d1004041d030680c06503103058919000d0040b03039400550201c40700d001480804001c10680d1149601800080101189140400b1002890900c000e44014401e4006518900000d00300d4000c0700c8612082c514007084801e01030030500000d000e0418026000094004140c003000702c03040016100b0304d0f040034498140d407212426a582c0340980107006015500030710101d00c41048000081a0f198404c1c940700048906495409500707900342d0f44001880c0e40045842c061651040c801c01141c0300c07183c4000c1414500c0301e0300040159106100241020101501050a1011106 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 907305494 1250 907304244 907304273
    0x80a0e210c120d14010e0a0510150905010305070f02100e030f190906080f01090902061603111009030e0402180303070c0501170f150f0411031603020c19 67
    0x3901e9007021403003103000b62940b0260b444112903140101000c0b44008001e001d80c1640c1c4218401081c540d02d071031140300100805410f00030b01e40c01c08400000c0c1c01c0310103c2c1c055610300c456652070301d125140900260640f5005006c081c140070300e80142080700c070741c005420f4040440c2c000000c981c40012440c3c090a51003009210b10314088006001d003460191a820a03502c00c00640d0303503a8005561302000c640c400c0b030540700c82e02d2001c43c0704010000c51006820102800d40010b110500c0c0c0001c404c1007003d44500b00b40d08a0105100e805207103460a018000c1d5019060745400900c520656550000c02c20b8290080503849950301241c4000d005404031800c01c64088098201e90f0340300071310b05010380b1310b50180c443c003070000d542810b03240c1c0f12301107952249000e4020701900d0b183e5525035542c04154041c20b94001c030b8110010880c0030045030360301d000e07a9460450499810380c1c4c0e030030100c984101d240064941d0001749401001900340a89000514031070100714010500640d02407482d10383c4800e030700f10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 907306744 1250 907305494 907305517
    0x50d0e2d0d0602120108060c162915011805120705030703140c010e0109060309022e0e0a03171c141e070f0c0203010b030a03020c01080a0e21 62
    0x4680d010802510f5401004d00240c00d0140340010b0380e0307801036141c0d100022901e04001190502200312208128149251064400d001c19582c805201004000201d0706186110907625240e0500c034607100c41701e8071045a0102032030f040801c90901c0c00329110020840c8681800b0749554170244c4d440c14030500c45d0b0380284c0002421395410540c0e83c14100c00282c0b091040c0c800d10b0181d614201c5096010f50f145401044045c1c4600d030b50f4602d0b100d015402452264010b80e00100c0444c071040c03040341c95070b0210300c440802021089a4880c1c0c00030041c07240c1030200c3c0d00c5004d009442c0c02480480c90002034180d942010405003075030703129010b001d920f078001e02c06802c640142c280071240030b04640b040b80840c130541d44103a9254503104541d104140540c000d0341c2a1010030105003545002074801e2036141e000d14006070000c101d0200c4903010034a0110200401c1c0d0058210000c0030300300d5030b400b00030650000c1400c40207205040d483c2548548035500d0104001250141030b03600e251081a41040c0c0d074060307002c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 907307994 1250 907306744 907306759
    0xa050405040f03110606220e010f1a040203010e0c070f050102030709061b11010e01020a0f081b0609030a18030b07020d03150b16030306031707050d0e2d 67
    0x580b030404188100e0703610840116540000f480300d014030004900784240c40081000e03840c03071020000c05031280c4509080e800c1aa0301ca00c81070681c0c080902540071101f40400e00090500c5d50451a180030350400d000051043e80100b0042100e044000ca0280e040703880c0719901540c80b41c00d4a4030810b12580141c00900550021007004510340c0c00c030741e84000304c5400b070f00d50511000401012000e054a6010004d1124010030a2420194030904001c0c40724a07040c011074400c4003050b2a4903600100c140390444100e440001c05140702d000c040801a1240f000f031006154604040c030082e074070b80c0a10b41d060fa04019071300300d43c8100880d03100700072001135400c0180b004640c10a0200251502e2031540e1800109040c1a00400c400862122180485c0d00e11005030307041051843c00d9142c05001c0c0c0105130105501e5201c080049208035014485000030000121f5a400c0507152550078046030b00b8440d01805080780e01c031321440d01d85421403d02c40400140600c141906229402803080c03030001e21503040800c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 907309244 1250 907307994 907308001
    0x206043006020a03060605030f0a0c020339010603031b1e03022b021e1606020a050c04110306010804140607121506050f0705010e061015031512020a050405 68
    0x89540100550001c9513028032885071951403da030b243c4420344411142e4021391000404201440e4807807901c0c0166841030700d15060b1541c81405c06e128095280c800c980c076850380001c0c0d01d2802c05a00e207800c1c0c00b00400138400c052850710007410030703126074000507440d0041110203000c00c10b10501d241590b98000d60040e602e503005003002540d0f16442043c1c003d540ca4500e027001d80510030900a00710000c0030354010314040c4040f030743e5807110100804803485188110075881e0000000000b5030b001500d400c0c0e005002c1e1b4603480c2000d5103032004071507400d0b00031442c086118082162001c00c80398483c1c03003030801a050740ca42d0314000d642e041700c5501c41160340c09402c0500101a41c81521400705081c00c040c148840194441c0303090641d402440f070480400c2c0204440c0141c00c0c5000007805c0441d001d540000360030751102c0015800d0080885000503100c0505405200800c00c3c1c0b491042e09140500c0e0400c03070080f070444c104100c2d9441c2d000307001a580f5051452002c550b1885420009404c0c0a0803c3c0030508 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 907310494 1250 907309244 907309253
    0x32070f0519110d0801030c09020903010902060406261902090d020307030308010609051203030a090212070f030204541406130308040b1806090601030506090a02060430 73
    0x901c5420054000c3c024404125105441003240f281a0398106070340701949454807c08000a41c85181d00c00d8055480e4820900980d51312009000104810340341d40e0035400040a80c103c400d420150440352240036001882000c0c0b01c010751003406400520001a503403640704002820580303509100a5152003100c8000c810075600c5100b80c3d0481c0c10070303114500c1c2107460b442040900c100c0261011040e6000b400004c00d00559500120b6295001406039840122000125400c1c1800c6800140c8003480c004010404c46c00c00b403095120031003841d44040c1909010003180005c80814040200490070080c03680d01c011b81a03101e101143c80d02d07200c50030101442624090702d61000255400081d8050384000403030448c1c85020345000035505950b107c085658554410b0032409000e010403a20b42c01c00925689110001c21040d030241174440010301e40d9600d9403800a2605030001c0000c1819046032a5100050f114141a64199044116400d90f8130070420214022000d04952401002112260800600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 907311744 1250 907310494 907310507
    0x3030403020f0d030b06090d0f020a060f1209030206040209060619031e0501180207110a120b09010e2a0307120b09010c0e0f0112020d32070f0519 64
    0x2d14282529618145803400b0340440f5450100c2c1c9800000401150400780f030820700d54000184074442da400d610207540c010800b6800c207600020701141d0309030f03503400955801080010304400900300911000115503802034442030081c0c00213020305070290200e000d42da1090244d030107484425440f441501c0300e0600003400360801443c1044071084a000040c080319550259038180c401c0203005a0300180034020150095020751020b0707070740f200c043e01410707100e59500b0741c3c020007482101e01d9601510001c0c01c1c16040400c0140c8140c2c001d82c9481a1028242c00104015070342c81c0216035074640c90840c45a09198660f4035401a80d4540600000070500040603481d61480c0d038041e081c1040640d46540c0064220f488208008c40450103014640c840c83c60002d080030741480041c90845605090014000266008003051104040c1c541604440c0c055030030744000000720845074204283c18030b042858a1480016010300c08010024086072800c80c001ca0484d00c00f0703c140c81c484140c0c80002e88005051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 907312994 1250 907311744 907311763
    0xf0201081315150504150b18030a080301050f030a0b0c07030e030a050a20310c05040911070b0403051b06130c0501031a090a1401171c08040605040f050303040302 71
    0x1030b0b0440c503070003140c1d50401d813141c2804d00018a008807001400c02c7c2c50f58800b03400014840701d80001c003c0e1441a03d0310180018010300b80f20303010044c3c907541444200101d41159144607806580048e4600020501004180d03030008201c0c00700c142e40d0451401d089503c05d01115020780c240c41071182250030018000ba04030040c80c0600b440036441e0003003003000d00c0c039140c401088a500c81c84044200320b84c0c14040d02c2034072651521a040485861420300414203841e80c24804501141d808074081161060500031001e1120000f074041d8900155079440e98008a00540003800708100843c03200750104010390980c140000b10811240c0d5440c04122002d540d110340f40f411a002c000044002445500a00031964808011a02c69030b440008400b0710a6010005040306c0525880e113903c481702c40002d08100d40a40300240302103000c681c40c82c0c0c1c440e290050840b000c19030203000c1942c541e90254030a11040d0407640c00203000c6401c0d155410040096a0400c001816902000007032104041d0000351401c1d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 907314244 1250 907312994 907313021
    0x212090a030807020303040308070e06040905070c0c050307031a13051906060509090303071d190f0e2205071508060a0b0c100f1d0f06060604030f0201081315 69
    0x2150f0780d03e0b0002c90301d0f03000a50340100494a01d1020a406500039600011400c9014000c207007030643d0f695450064580540d8501c0120344003118a406200a004884002c1d0000b40c00409a04c0d1a640d80d201c1d55800440c0c154601507502c00214054059045400c00d0b001d410000f15139440300d82055010401e9601d500c121a083c0c40c0213000203a1341003800c007a51041103080301950031651120701c10307640900b4030f03401428009402440d8001d2513444025540d0303178100d0b900d2610001d42c10b11618064402c030036000585072480c404200602100c01610064150307400020b001e00820b620f1500742d14084d910f8001c50500c0c02040000d4500079070000070244510001c903400384801c0e80d9810582d0341442204404442e54014a82d0078481148035041140e201c8441c03080000d28004041c07440c00a030350741100391251034000c100b010303101c40e0040000d039401440458480f0b150924642d03580c0319902c84800024140680741d80000c04641010300840d5003940c005009054804c3c550309540024078850752820f2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 907315494 1250 907314244 907314257
    0x111e04180605010c02280617010b09090c0c0a240b0a0305030d02090111030409020301170724171f081c0c050703052422060f0212090a03 60
    0x100820501c1c0119812107906031110750340d240554083c00307203c2103a503038611401400c50070004100b0040c090382d000200111fa46007900f00c1c412031110b02c0b41e408103a01c01c1c02e0390041400201c64955911407541d0708030110b4a8002c0e0388082111445091000d01d4601604001c403282c01c030701161000100700d07110712082480070005206000200a17459445010191003940203009820b038880300d0360300500103420141003106904034526501031840d4056000410350503008001084041103042c00300644c40d4800b4050131016080030f007504401609485014045e20300c007800c4004080c040e0f4101485a4007103000c0c0d034551714014004110951030908a00501d401c0c140000807504800315a10340d105810303484414038024089822554461000e50540d1203024180d4000700280c010411696200741500c004d1000a03110000714110348002400e10041c0e1400f040d002c0700c00000b10070f4502c0e4050303100000080340c812801d0300c1d0b0020b000d02146078440131410001e021403144005802d0010520a54070355 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 907316744 1250 907315494 907315529
    0x261207020406080307050a080f090402042309040b040303020a032a14070b04020909030c1b010e270c04091409010605040207150b010302190804020f031c03111e04 71
    0x2c3c4c0e983c8074603000908660003030301c0c0040000c0c1440c8014070f6410402d6140c9030511100c4c030001000c0303a00079403061350748540c010f0612100d00d281110810a440c400c0720850503a20706500e0f0221321441c02003000b820103074001040c16520340643e000201c001001e25803140c2000c50b01039407580c405c8580007540c010480d10f951021542205030f04480c4841e604c41082c00d6685c8456080c8043c01401a14a0000780030901c0584010501042400c000c0ea4a01401c500100000b40c009442a002e01007514000c2c0c84c2094065081845d980002f210622481400c050a0341ca5031005031b50f034059a00700030000c0d818411b40480c0312803c440814024420354008002407a6103004000480c41254001004400220b01000c1c80c249181d000c00920352041c10003501d0b000701490401010304207600c2400100314820188015802c000c1c44140c0c1c9804103400621805405405912524404514440c209a1603151003c2603a410b81d080d2074004034010541080780d1020040401700ea005401085268840354106 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 907317994 1250 907316744 907316759
    0x303050c03060102030a0302090a03050d09140402042103090506031006021b030c0d06090803040c060305060121110712030507020613020907050a050c1e0f16261207020406 75
    0x1142d014200c1600154642075590105501940004160581c065200180000800c40034825005c1013451039031aa01d865052801d0540c0751906202c061303000328414031040c05000b020811082101e140030440b071000042c1440e003150805c113140c000035001103011050200b10141500442d00b1b907405602900c2040c0b42124001901000490200b9455130014041aa040c10a905004042800390b00007250704d10964841000c0c0750f100351000ca82000c80c3c07440c104070503035140c0b0543c0c7c0c0101c400d02c2e12015030745056a18503118407141a1101345030780d80e0105620346000b00802c03100919442040303a1803100704004043c00030308040324850054041e0500141020413011081131144e0750060005120381c5580d10104d410750032082181d01030000c208071304840c0400c20000c2d203c181c8540004c00341c040d012440d55506003800044040d4581d03206507409246515803c45100a60704540103629070103203401041034035201d5a0a41014501414407000741841d095070040540d580240c030140100c03980e40c0035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 907319244 1250 907317994 907317997
    0x10305190c02011a1e06210408070b0c07150203070e1201020c070e010e1f09020c0607030c031811010c0f062c210c030a090311030102030f0f191103040303050c 70
    0x40d00002c030285d0f410741300a1900700040c14580682c1c0a40700401d21444011200c06807041d5800e0354210804078400c42042280c186136980605080b41880c244003e50b40e03002ca110107103103520310340243c001c8002114948101040000a4401400790b081004d200c41c2d0396000f07620180700f400d054080c10f04013180c2201000d000d02c1c125501c070f10140c003485d42c9110f40384401c04854030440c800c00c01d030305100003641c0400e070002d4912554110701805290030003840c090105d840040002d07040c90b061840050044450b142c00940355608080140801c00c0d1260040b990b9640424009242c0e40785075187c2c20500c00c0940c02400810120703075407072141e003800302401d6410501400c403410a941c0205201410b5070740260994401901c0046254103041c0040416030854214004030307000254006420828450a004141d41c1440140d000310b1442c1080c490448200380010004c0c004003a040c00030502a40c44528030204600b11503504100504e00b82040d1040e950043d207054000070304000104000110250 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 907320494 1250 907319244 907319269
    0x311030d0f180305180114040b0d0c02072702070215030103050c0d200a0801060803090301050c0a051210090c0305180723030a14010605130207020f010305190c02011a 73
    0x444c0c46051082c00c1010700140312144164504018800006110034005800588090003108400544480c0c10542078011a9001442c010840d40320381d40400c452103a280b83c41d5031110100010b925230402c1050020080d01c40c03944025003182d1000c04900a545c80e0a000d541600d1240094402c085586000c01c286400342400140141c24007260910070038000d440110204040035001e4024681c0ea18481421144640d106030525000040c902e0b2040c54207204e0594040d5150301c0b00da041c0300c811034008101b80111001443c810b43c0000100d5486090030242d00b0003465810800d01004031250401005000e0540c0d2140d00924040541801403001041c1d0320181e4031981140041d1910742001400d0440b05440130300c0e05409195071240c0800e205543c51042202e80c4000400e04600c0d00d0705000380e4240104400c203110b07205000b5080141d0b00e968100005850918001c036a0342c45008000d400d110b0b02151105e1b070b1500d0140303e00d52264043d00b2220340840d568241d00800c0280c1c0d02840b02904002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 907321744 1250 907320494 907320497
    0x5010e060603091f05010914040b04030f181203030c08151c14010506090709030b0114040b03011803080105060a050409021b060f010329070c0311030d0f1803 69
    0x2901400c201c0301441d030100f01c0314216040f81e801c0d07070010081401d000b10921080c944031070040c0044040d5008055500d440171080b190b0b031f1300d0b0640701c984881002070001403c00c4004c410724500c1d01e12411043c8055100301000024a07a6280d11000a160400b401200868100484240300c5405080a2480b400004c49072490032010300c02001039203903521110006129482c80b15101060b8040c12040404007841c0000845050000c10090b01e81d000a01034070812a80f0007051000403490911039044907210001410b540500400050241c0344404055400d980381c2000d05202d0600d080e80044150300030346030032000d640c81d5018026a803040e900d000300400d004100c2040410071a5004100ca10007101c41c01c07650080c2143d1140c20304505440c03440240c00300310014400e00a041004101035007180c15900300c200c400012807842444000c02404c18030401035582000c1c540030b18000444010a1702c103030b07a92254942e5040c402000c0d040c1200c0c51091506a40b0203d003407801c02c03080c010a405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 907322994 1250 907321744 907321769
    0xc080711030711061c0b0f04090201020a0f020a051002100b0618010c080d09080d0e06041110020a0b180f21070c09050406020307021b0112090809060703050a020708010501 75
    0x41d43c0b80d81c12015424840c19422400400c4500c900e41c82e903484805204207000700c04640c07260300f80c007007268800103801c11a110b640352a601d640180e0300068004602580010303106400c020714000545c01846650045410081c46030510350b42035408203540005024480d010080691081c06004043c05100c00c00c02d8551050440341595600480040a14612903114149030156083d030303d0080d41c10948080794031840c0880c1d1034120300c10b140201190100c0c040c0c014015440c0035150b080c4c007242d0046009000301548000104410f200b4881450b540d5006241c180060500c0d00c480f620038800c075480360b00c2d1b40c0241c410f40203c4038804220f80031a90740c804c5d001d968005080148000300e034800708084468000d00c12000440d06550f001d0b0501c81c0340603890060722441c28100c040d09040b10040007a4100720142c21407121680c10020048100c050f0040006143e04240f606071150700c40e588502e84e100c90046a10310415920000a0a541900d9802c1e501c04903500c0c40e2080c244c50003802041c50401d44c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 907324244 1250 907322994 907323007
    0x80105091e1b0408010204030807030f030b030c040b0303090a14030d081e09031b150a050601082e0321080c161518020f0f030c0d05120406030c08071103 67
    0x110301d000002c2c0684140001c5140654500c099801c90b485a03004171601a804030343e18041c1500722180304007804507414140001c1c058900006c0d01c130003501d002280314594480d504041ea407410000da54001c0d00250140c4a1035403a0300421025540d00344a4a00c1b9200d03502d4544181440b4030303201030062101e44401c2074141c02d04120650b14010003040c1003000e10060060000000074804511800c0705004050039040d007149460411107400281248e060a00701428881c1c00d90303000074041e0784050210800c070b508140b504511200100324001c0c91480244d400008000e006000c107100c441d89405103a1078907121491602030ba0420f078101d42203000848140500040e030440c3c54460303000103220380c4403011200c1d0700380e40c05421140140d004039100086240c24400318103003001d44503866641104d41840009900e400030b6550729007145c8150080e220a1000c0b020820108102024101458003a40d11340e601c40c0c5004006002d141c2d0030600103109507020400b19401000c541128180b400043e43c507111 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 907325494 1250 907324244 907324261
    0x10050f12181606020601060338220b0904020d1202120a120b010302090d03030b2e0801090b0a0504020703020c131508030a052512080105091e 62
    0x30008065403840044074020a45400050010b400b0300710b000c1500b80502d508290000b407810368140c00220a2502c0d006452000c088041000745c81e00018001d98245121030b00300e001c2407043d08038455601704440000300640c1410300c180b0740c41e009114010800002c500c50040001d000025680650090850013509000c603145000743c507074030a014011128803104000c408969503211a290800040034001400e40c0800305025407089507409107030550420340800c00041c038200b0900002014169614507451040d12640380203001354600b9680400c40a401382d26404c90896041d042d580080c8030342e000803c00c0c4825200d81c040410014120b00200c508260500000b035100d81d40c2034041d4800c403500307451180c9d1201841c58281107200340100701040c0c1190707a002000d1158102e918160400d01c00381d610b56500c68141d07a4901e00300304203030320304a58a010b003c03c0c4202c0f402c006007000c600c0c20342c42280e598003c40814100c1c0d4003551440445d030740792036600c80b40c4100241910b5540030705101260303111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 907326744 1250 907325494 907325527
    0xf1605070609120905010e0411030c0d1b0905120f0d030e01020702040c0e03011406030a110109030605071713030c030e04060f1806050a0833040c0510050f 68
    0x1a104840000341c00486844a8100f0342070320440038005220701074107025650340b081e1075491180c402d0703405005a055140c128911800300070000fa0b28031601140c4d80d03028520702e81048006110120000e00c940540d2035008201841c540603d60141d1300711145803201c40000103503811040030300d03030160002e1001c1c01d504402400c040410451999001c0c42300e030380540d03242e11a844400e81d050b2100c000007884070040c10709584034010720058150b4400104803007a1008600440c103150312811803503403041c0300001a1440d41c41a00302400040c9000104250f01341c0000e848000d02c81d850404103040d0f40e0726009641c1960403000001e0001344803155844c0000d0040030b445003100e40081c004201980c03260848a03040c030382e60744440040c504401c10305107170701058490403010300f0083d90403444840c00e01c40340c10b0762640452014018a104001405c5155840391a11000c0302c226482100131400d1078100268007890030301441c0c1c45400450a40200740d401f800c200e9407a03400c104221070030b01e03444c0100c1000d0b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 907327994 1250 907326744 907326757
    0x10507110312130b0703141515090604030c0e010302031203090a030c060e0a03020a020a0611150703110d0b010315180218030d02070602060c041206021804180501050f1605 75
    0x10f09030000c09002400c00701c03500c3d200f0396844d540020424150802d000d0300d001c0180c0220302c48051110401c1207a1203140c240e101003610140c0e040e540e2504a00420b81502c2503078001340c940c1c2e0340040c011a01011410f500c0d4103d030b0084007180c10000c03401460048a01c402d80706032066510450000000030f004103144003040303000700c1000582d0895810a54181000018100c00580040780c12408600d0014030070f0300503000e0341c6024004950008840d5994039010592810072000400004000c0b0b40b2030f40003410741c241584542a202d84522a00401034804484610702003403c00425018045525200d0422100030788142c42d400030341d841c0c0c264000d5010440d1134000340e128102c10070558808000f804c5032890a540103200d518508240282072407000741010181c01c804000803c400c40007400d055010079040780c80140c0d0340c1c01c020040034508041c0d070407458104e418101b8000e40623070045003140c403c9028100a00c003d690700903004002d0700b000c40d03400d8401000f04a00304040c0c0d00c604080c212 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 907329244 1250 907327994 907328011
    0x12040303060302120705040612050c12030403020415051f140c03070506011d0a0c0e040b0102010e0f030a09080f0703030305060105040909150608011e0b0f06030405010608010507110312 81
    0x141c01d40c594011401c0d540181e440039035154840502007045050030310400e4010000901100402d07402c42e81c038691110210045030740b15a0035110401e60000060048070003d5034001c20800440b4481c0544001a0300c59110b0b041c850380380628526500c1c10740303469004d0b600f0015a602c1d0008502c002842089030040b802c01350451005000080010303204001d500d001c2d00004100b940303011030800c400301c0741c403100503c4080c0041c1800e00d540a0280c1004540c5401ca00440f808522480d0120040740141410700c95000311340700d130340011740207254007200410030705125945461003e40c0b105000f40d6141c0d039000d51129036500615080002c00d119511107034000805141036450f156803400014143c455102003928002c44d2032024070404800d9100c0d6070300070081e50380284000005400303c110068440d90b152007000f40c8030110303e09143c1c0c40d508210511180284040d4881c1814240140204514011541558600004100c0140c010400d030f61072188100300951a03c46c103000d0004031003001901501c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 907330494 1250 907329244 907329251
    0x3050f04030f050409061415180402030c2701080a0c0801181508010e0d140702090a0e10020301090c0e100e030a02060c060f0c18010804020312160b1b12040303 70
    0x64496480c006c4000502c80030b94614000328a1000b008a150b620181e8410b42100c20400301c601e8010030740480700f40c42c80840b8016182d40d02d08600c1c48891181140020a0340111800c40c800303c888585440d01c14242030740c882c10f455540741030318000c40d0032400207d00072414140040120710205a07019144045006000c42c80c610841c5080681600b240c101092594640c980d0490045040003070284c0038070245007413005241c843c0f02d1800c1074852164044e001d112800009485d818482d041088000b9070503023224071000a13000b20300000d410070300034514098140030300d000c41540b040c04d03a140041070003000b88c001c4d0300386d000050700c0c98040900c0701743c0c150084503000c00143c1da890000d01607555458002d030120f480c10005002c0d503000d00602c0d910405e1814059040744a420300e56001c41d01100382015038140e02e0350300000c0e1403c402c850710340c0b0b00103200003800031100010100c842816481003c00c2080390300c0c0e6841000310741001e00000b03803070301c1c02c00d010200c81c41050790420b42d0010301904001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 907331744 1250 907330494 907330499
    0x101412030702040c050a1205070c03110f190204060b070b06011b02060301030609141f090507051504030c08150a0c50030a05060109170705010305060103050f04030f0504 74
    0x14040e01d004200304c10100320041082c56130550805108a04074266250400c140d2070203000250500c50b040c00e002c2d0401070b0b0a4100c041d5900104034141003114190120350fa1014a8500a03c2c410f548681c101d0046080210000c5c5c0481c8083c260751090354080304109140c2c0d24080111362400c0ea40d030036503100c940303461b4402c000340c5c03680ca0046004c1c5000b14004108030413541000c4c0c052419208942c0502c0d4441c0040c0c2101e500000280038203a0b4036014042110050341c00d10b14600002c81d0400c80d0701a14984c0c4d070381800c029490080080b281328802c3c1d10f00b4a0360741d0704400e840300d031490310903902c141d0b8a00014a14000543c03108020b64000e080001c0440c0c244005440c0203411014450200840541e083e448200c915541c0b042001d580145150b1810701d1426625441c00702405004886403910b0228156078084c403044c20280c00340703c0000c100b00102008065541c0701e01e120300c03404207241c0008618694803a0090314405e40301d581d014120740d151980c04560262124841100300302c0c003030001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 907332994 1250 907331744 907331749
    0x1a090f040510020a0e0405060306090a260d02040801060f03110409081909060e0f060d0b010309051605010314061c030e0301180c091e050406060e0a0203070305101412030702 76
    0xa000d49541e01c5d40c40c4034000c0784220500044a030098001c40c402d501040c200100884006503484e903a030349c03009040d00c0d0a040d10130720382506c003400706180c4160f02d40413907064000f890340d50181044680d0680240030344c81d038070969015035414500000d040b40c0109620850f1504180d000244c00d80d10500001d46001814a1030f281180b0307040004600048040404008039a0301c4201302c90490710480300f1400c01a03a80000612034822a120340c0c0d24140c441c0c0310240c090380240c0c00103220f142c00509441100300e040054070001c09644c028640802d01c0d00c0d40092164404d00c1c1c1040c803400c1d02500004040d207041d40d800402c1406040d0440402c030804011540320b490030701401c1c012501c0e081c4002d002514919080000880399080700705c4030380c40c215041c40c0c10340d0200781320703180781041e42c03800282038031613003040000307040f00c0c6e00580e14840141c414440610300c941e0003188200c0d81c80d81c1c00c10040d1103820340d20780f40701e48510a103130700a004050748600070303e082c45190940440c817070216460074810750701 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 907334244 1250 907332994 907332997
    0x901020c0a2301020607020a030c210c03080907050d1b0b0d02040306060816060f02150705040509100e160903390302010813050a05100209041a090f04051002 69
    0x40004010314003090360110241101a92002d2102400900403e2074100070003903603800010805000c10060340354032410712242c0140001146030680e01d030500c1d15000100544031514403d011800a001140002c989200200e030044c2031f00c40040007030451400f140c4683c842102a8504802220726a2000045480c40c2c20000c04045410402c0961100c0c61404d10008440c0c0f41d500201c00c907001405590607a00c440104401a04c00d2814800b120ac550740c3e13400c03840c0c4032107004060240c0c0051000d020740d050704000600700729034013141c05000d03941d107444100e0340034030391032240300e01e045000c6020070301031181f641d0121a40c881f1450041c01007981e0351503c095480c80c081e44480180141c162400145062207185290400c411489021151659000924162002704100c00c4e4004804034101080001c1c031032004079a811a0454500452109500000358031032031203144600d20b00103ca041d0414441d5000c1d040340002800d043c030940d035501e200c41e5034cc00020070485960181410322104a4032520 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 907335494 1250 907334244 907334249
    0x80912010c0f02010b090f18100209040c020d0909021e123108031801020a080603060106090311090405031b030d11191413171203060d03050901020c0a 66
    0x401c0304400e5030809041101404205402c5905102c9505e5564507400310064000200890010003599889040000c80c941d44144200d02e0062040303031282d40c6100d801030315a4240403a070401601b106030405a0f44c0d280380480002c0480c446c12004c214540d000e5001d1700d42000d485001c1004007000d00e248400951003112040055010701e003c1c0246a40c43c60060112032032116032050045016501c0289907180c008001030050000200140e0900c0b51181101100c8048030002c1d52900d0403564040d00a080441c0c080d4040e100c0c0030b00000700d652180e5601401c9a0304406032244c41900001404511003004006403054442003002800a030380072002d00c009030700800061525a0f29110f2444285e540da4010a4203441c000d00135540c00081c2060780c2040d11007981803445448001204840003409403800e810041d10002500168950a514131140426030702d500703a0b054004c50700300814a81c002075038469049804002d00500080c041e030000e12401e8014011070b801c00c9031042c009002e10f00d603074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 907336744 1250 907335494 907335529
    0x219051914010509010923070905010306020a02010f050c2d0708040f060504060909051503032a0714120a0507140f04050402060a0302070f020603070f18030506010504090809 76
    0x180c1d401d54007003000e100f55500030507240020720910016840b00318400c6080d01c81d9a441c10440146948001c000300b0682008000c0d221042c01740e03681d00e00381f240007904a58840d50142d42807609444010b030191256611692050780c0325030502240134000f800c021014001d49078404c190703000c0c007841e0302140000307092a030780700c2c40a841e607031030411442d00c1200300c01d9401002440720a000520803030380c1005000d001d84d4050000054580d41d07000082c810441c0344088160140030009032602e000392140e8506504c0510a286408400b2266881c550317640d44c1e500c10446a140310852118062400001c0311030400480e10480d440c451071601c0b1582132107096031020b070341c1500088a100c10381c1405044034028144c05c840420080c034254021500d00e12407101d0250416500182c01d400304148c0e16100494107030040c141540360302d003e09000c2d100e074410b007501a010902d030350300518040790503d072100e040d030358080050310450f4608414800036000c994007c0310304a40501120301b05440304c103c103116804a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 907337994 1250 907336744 907336763
    0x3030c04061103030c120a0b33030f0f0405100c030903080705032e0f031112030c210c010c02060f10050108040f0201180e04020405070e0102190519 65
    0x70240c0103054005400700000e15a0024401c001c0d0000884060316210108103001c00c2d105c1d641c601c0960001c1c8400d141056001d59519aa070014a1083c01e40444911120741401d060f100c2c008240388260000316201038030505403074001440c1c000c081800e40e0704140314034120381160b10781d981140c090380c0a10100e480003d42c2d5915000a265001407000e41007141d40c2001e610714280b4048000030004001240e80048030b078441400209201f80402a000340b48005001044980b245403200350b160b0b95001c101d110380684015004d580b9400700484800700e80307600c01400102d040d00c07880545003d800905c105c0070b180c280700c9040b0441c400e004041c0c0c40340b80c5a001d01039034a40300410180c80d070303000380c07514002c006000002d100698100c01c0d40ea40082d00105202d6881549d840104d4101d000b2610401c080f2181c20790000302100c2461078540281d01c00c5805002e01d030b451205c01c40e0442e42a002650040c2c1c03081d8007001c402000a030001ba07445028606450700500400c0418040d9016900c0c22922180c0c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 907339244 1250 907337994 907337999
    0xb060301290307050a0810050d1b050303040b030f100f1212031b0537030606050a0807080a060e0705120603010c020705090c0c0106030c0302180f13020301020c03030c04 74
    0x6814819800c248141c80c6060300b14148030500504c00e004203158441800102d00c04520034800c1d1401c080020130009003000c11510491800c2614050316400b40151401c61000102e45454044280d40644104820743c81c19544c1d6114007a80a42015212146505905c0c01c0420300001c0ba107440d0020b001c0600c00e01c00d552580d8905204a00318001394201050b20300b6030050400c1045400701e000d1400245400707612469882425500c000f010042c80240c09022501200d401d0030582c8900b80d10410740d00c04005481d030310a4140c8007842a10a408005a04400003d08807809040496001f41e40a580020392a8481401c220089403e0b95141c002c0340c400705002820f41d46401e216a0700c039200760003d100c0c0f0a94079002943d20ba0766401503510850042c8000b0700c90481300410345106046c482300901085650b070a00c000040c455001c1640a45551200c17580d44032181d01e43c1500034944120103808640d00d543d02c0000202c080714040b41c3c19502042000100c8030200060350040400c0c282c0c040c0c0d00c51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 907340494 1250 907339244 907339289
    0x706050603060f0c0d020a121b0809010504080a12140c13050312090d080d41190f062d060f030b04110d060f0503120403020f040b060301 60
    0x1c024059460642002c040200301c0303104009507081c5d0a0a01c1000d600c1d4800d1042c180c40c0c0340c502040c1500301030b10349203170307514000281c241caa0115009510740c1080d84e211342c1d41e220b085c1c500c01c40d0007903d01007081100820161081c80c0c4110252041c550018122042c00003221845005603001d0342046408604804500c0a403c0e6080040400320001c00094a000307541074102e0041300c4905210b541103090b4a000d00800804450783d45d481ea2070108550403007201c14107110381c6a041480f203403ca000c09504030070f80b401400c600703c580c00e10f400c49446a55020704502808156190040f0a94481c4002c00644803d8055200941081d0031400070a40d02d024151780d0401030b42c441c000e19011840780405c1010703044100c050100c1c505140100f10089590b0101e00a8158a00382c01ca10000020301d030341e1500b10070760054055558084269082640c0d883c101960344412250302c65440104020810040c0b40c41689240c1940d0b000d440840e541c06c1000020703080f5082640804040850450310840300c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 907341744 1250 907340494 907340503
    0x19050f01110607020124120f170712021204140909100e0303060f37180e010f060f092310030606210b060307080d030c021615050d0e030706050603 64
    0x400d00d485017141f407900142c01d01c01031078410007030000383c000310122091085c5884100f4040c1f080c3d0303840c03540e00c080a2a00704025101c2d01282001401009200311294000008890844031444011288143d000c1d04001569401400c184c8040c40307041a003001a154502a8240000100018540340d16107031062111440c807486000344501c0780d003a03000058a4181084040503890886009064ad201466401e0341e65a285c020036070450400d29490507848482d044549200d459400910250045641c402c050356094000e420750200d2481d801d020300701c1c0340e42c05a82c424804a001c041140b041824442c5500010f55154100b8030303c0000610038080e2502640c00108240c82ca00c0c0745895007041000f180303824585004040301100e10111b41d807070b501082000090b2110105650100c2540e0038092f0013001d00f0f0107560054040e10000e900c450241c2c2d4040c6080718541c1c141c81c0c10000350408229103550042ca406201580c2c1d40480302c06812040002c0c1040c1d40c0324400020700b60403e203040501c1d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 907342994 1250 907341744 907341791
    0x270a090221060115020109150204060e09160f0207031a010e0702060907030231060512010b0618011e09170c010207030605070203040b030a020d0b19050f011106070201 73
    0x4841d865079210007400350008805045070801c2e019000461a4944124050004900b024000c08c400801c00c40c03400030071b60700030301c200d801710784400c040c2440306418400d004c041112010300714800c1d00080c1c42c00500031400703950590030340d1054559031364903a5507102e01c1640c403052101c0d0003140280144450187c000e4007079000003441c001070825207080301a40e561000c4070300000b8060002e110fa803224036071684200007035103902c40d003290101e19105416080108054070509120b500d00d40c0301c4000403103040c46070070076400380038103e14030342081c03500d4449520201001160401100000a0502504800709100644202e58803001d20900d00400403501007101445040701350011658114180c1c0c0005032401142c1d8004c0011130300750354060341a41540102e0380022180c200c00400c011190090f83c0c0100081600c66200300081494082489213411551600c5c0c840b149590b1010f200d42c5c41c1c44071000c40313a0b6405241105a80300000880c81c1016000d850550240c2e440c2c103440754002215440540c1e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 907344244 1250 907342994 907343029
    0x902030f060f01031e05030c0c13020703080f060307080609010e0d0801061e0315081501060801050a120206070807060b0307050108061021141b07020609270a0902 71
    0x440b401c10b54504100210306100c000c000802460a564001d5400d082040040340c01405680d2200082c44c5515100d07516400c0503480340342412150708001c4494403d4540550705a604c00070340340d4134100301b1032181c180907104580c50300c203010303000400319410480d9922985500c00042034002407050b401c1e260034000140b40c01484840300060011960010f07540720740d0351240c8006529550103220a0f402400c06160035031407105043c0c404210700380c00180e0303807541c0501841c10749060780e62500b084400f00001c0c050340b035002d036020808000c811044007200380000e0009200500d07004855880341c089501503401128039640311000400039140600450001b01002c0c01c046103546004400500040c0d146509d03030382400035511074890000c500e55088854094580b5040043c28080c040071011221b0880f5000c449410901000013a8860300041d1102507070301510807410181a0001c010a04010125402c81d070480b000204060050081c9840d008072459103002802403801e0042c40400000c81c502c098 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 907345494 1250 907344244 907344253
    0x30c1021050618071e0f140c121e1209100903080c071403220f15050306060d06090c02010f050402032517030d0501050d0512090a0e01090902030f 64
    0x609844560201c40c0f440c0c036103441160780395a000c1c2c00780e940b603001091401c5d00c42a8031641618858200b0102442e81d03026840303018040c4041c00381400300c1d22071b0304403040d2140c10070595988403510300d00180081d008091006002018000c045802c0e58200780c142c813010412103001e008031908180030a09401c20fa0340d80170300c101c103034a1310003800c0410003030140f010000300001c4403c18009170380003040403d82400c2c242c0c0e80e01c0c59080c1c0d80011240c01035441c260322504008001072210305801d113060440e1050111b0307a04d408905d000c207603640d400081003190000002c00c01f0040940f03241c461107014002545001030102840c0400a0031111003c41f841d0b5000d14000c103110140c0d4000590000030b02c0e82c0d0300c29800d51000700740311680700040c2c0d0b0f10403581c0030b450b0781c0d000c42940f00c040050030780c00282100400c4140e81e624100848000d0500c4094160b40150071500d81c2d01051000904068201504445d0060780d683d5009003031102c264480030080d642c031034480f003c6240078005030300e0b45080c842c01807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 907346744 1250 907345494 907345501
    0x311010b031b030111030124091505390708010902060d05090307020904062306090a1a060c0f160e160201110301031407080607120506030c102105 64
    0xc0d9035010000d500110018122007128090360f09400c00640b140c00ca503c110780b44e5a40e0340001940c0103026a040c081e10341d20701407682c2040e110b078032003104030b0314a0503040c220720010740c01c20780f4294030280001a000348048200d4041041413080018601d100070051322003030702450105410010690072246480c0d042c070301c808016a4541090724518400040700041544494600c5859840740c01d00013508224000204010701c6069030248606648001010700300800309501c08103004c008440742c0343d10807141c0020030103800203a40011044039646590b0010f00f04144005038a0b600281c2a0042c25030281d40d0003541c2840a008910520f59030031908801c079820003071030030701d40200107001505804031000210726040c030075081101d20396141401280e503540c507420a4000c440f09801451054400c0c12070014059200281c094440c1c2203642e210b2035004071881c0341001900001c3c01d455458450720081740703103540e10f1000e406e03007011090311031124a280d580d02d00340c0001c1e095040c848200c1e02d02002c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 907347994 1250 907346744 907346749
    0x110c0901080a0501061a2512170108010605130b0f06030903070c120519050304050a030c06080f0402010914130f020909010602010e0a151d03090f091005010818190311010b 75
    0x141c074106818242100da0b82505982c0d240305182c50b00a010340152380ba0302840940da500a81c1401c1100001250003c00781c0c0c03104100c6013a12140d1242d140c100c45444118064124540d104100a090040c1060104406500002d5481d081a030f00c00156800004040c0f0801c580b40a4000050840c2103600f4204c1d18035841d0aa150592112103080c03010540c1061420018280100c801401c8001c201034005da40341e08003148418140c1c0a02804254510040703103e28925528481c0700d180c0c16522590403509210040d1203d8500b40c0d00301d030f0013003c0304002091a0306035009246115a9100e40142c403611800c0400840c543e0603446030003903900d041c411111048011590403407150b0458101000c81844c050000028500c810003468041e612459515503118040020001c40808a0303034903da0320141001c00c01328803405e40e40000d0690b001602085103500038000300d54007000710498031030a0b00301301a8003070901e2802044a03040f80e403070724560360415401c11058001031085000030840414200003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 907349244 1250 907347994 907347997
    0x309010e07080c120c0f0d17270418060c030209030307080c0c011b060203060f030d030f200301090c140c010c0f0f1d060c0d0503180a02030706110c0901080a0501061a 73
    0x2101e40c084c00d01080020705105e024a0f122682c07508c0110305644d90f1201710340003c0911440030040d0305c03280904c2c9a241481c23400d03000d4401401d40d108500c0fa6806251358400c0004e020b040d210006164090002015aa906001600c186c2d4040c0c04010380e986c0140c40c6950074a00310032125818808441142d5822998610406072281c0e4840c0005036243c503200300047e000c02e240107071240c1c54800e940800204582c90341001442113801501813104a00c1132140c0c40300201a01c110200f4844107000401803002c1035040760500010b03074201040049003c4410722280d45c0082c004024030380d15284d002c20680e5201c41c01580c904c11910381240f003400031440c01850301099056401b440800da41c52052507640d2407007200c864200400888504040d9642e0141141d08122040e601d40109518401d906110100d4011422079000307003e003010904040040d1561620500f0004040c030540f1a03051403a00c0300784070745010309200b500a000002080c07a01500b0760b1001d0300035443c0740601c0c440100c81d42e6403100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 907350494 1250 907349244 907349269
    0x10020303070f0c0f0503130806011508060a030605010f0608060303030c0702010c1103010f0c03150f0302090a09020d140d02150c16080a0e01090603020306150309010e07080c120c 78
    0x29142c9088201128103c908540c0042c0140c031a501011311401001000401402c0b01300350f40341a00b01d007607900c02c161521303990244034044201c410aa06001d14078030070244a03600010041090080c151243c0312a42101d400360840036060800300350500c200741c1c02c1618260b000204400461540c6405020ba165230301404074020b05020b140b40b07050041150804040c500d017100500200a40e0f4100300c0b805028000e003810310000b181c03071302240202d284032552030102500e004400195580c0c0c555400d0100c04600203020004d0f02d5944d90590005a880b51415400c10340954144ca40008401224504141500c1c2c4642c081d0346c08a40c0040110f0390300403040c0d0744000c1da070507111744070080d02c91803800b40c50108000a01e00f00000402101c920b40120300418a00420fa070b401c40400d488020030340403031001760ba98980c4940281080b8524800d06002564081080e00002c500c3d0300d940c000c2e240c5000329640000c56075400440b106000390411101c0134900403071150003448050310101c00320741c0030750203034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 907351744 1250 907350494 907350497
    0x501060903060e03090d050105011a04030b0f1b0706060518090d1101091b030b0c0309300d0f050a06050d0f031707181401020309040b0a150908010b1002030307 70
    0x840e8800c2680f01d0a10a4900100001d001940407103440d2504900801d0b09010796200821030821f080500080c031011f460640e035100c007015250307403200002e44441c0000180800811004461100c0310845060b0107019200c0c4119030200b80941007408103c055040c4003403503c00283c61204000722244000b4204d0f1aa10060034071040c10ba29004001e80074003603541d0040d02d0071308003c0c0c980f018408002c0001e0112802089505001d4072a003110301e43e00d01c0195a0301800707610550682504000300080480ca0540d00d502520321190204a501c07096000003059100c002d0759a0301110644145024540d84280000c00c100851800c01d000106c6180c0c4615000c3c0c50b03800008421420580a074060080c81c054100c000421890308480050441e84142c00740400040c854000150740f1200c001980118203050300070f9814842c410b010320008002007901160b0086503110001880c0c05180100003c0c10038650360524054101400203007903521400d8014003e15042c40700580c0241c2c040184c9811030010f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 907352994 1250 907351744 907351751
    0x31305101e02030f040e04060605040b03030d18020a09020a1e021b0a0e1003060b1801030f170301141903030c0b0c09040f020306010807021b042403030f080a050106090306 75
    0x4140d040f4651301542c080321641000029000c1000c0005d444881d219034810fa00500000d40c036901804181c0c0c1003070a01d15010380c0f09020a802c1070758560411031855801d009100b1601e64260005001c08020741d100e42902c0781d00041651039558080404210310008824941000c82e4203d402580d82d10925801c407005680b140c4500300660392419076900a1128181003802828180802c0c0306a420380d1100f246c82030f1612400d810682400105056078a200b0510500325a185031122101d05403c002c0849140078a540703032103e0071148601550182648003056080b01021106001d200c0071050720800784c5929000e800c000113030740316080e4119940d000280ea0001d0310f403800e80b00f01d03900070724022076130040c03d0440c207049a42c00750380a98491402641d600f140d41d225030f40180c0c2c4030740281c00509116450000c1e200ca05007041e0b00007205c085100c8510140107072102c4c408040440c01c41c2c000303e000801d0701131740b10220b0707920a507600e400402e5000e042115515020001e801080c623032200910aa48 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 907354244 1250 907352994 907353047
    0x20c010507140418020415111006030809100e0d03081b040e06150d060803180603150402090310050f042f01031d03031302040c0c05060f060307031403130510 69
    0x507203406a40041c0100d1445245280940030042d00040c55800c4c26a110b110b80240030b40d81d49c40d00e000d41000c59421280c100d140920000501c00e0400e84440e100003480487d80482c21140c649984c890441e50081d540c04400d07040a4083c00703403031024000320b001001c505000c07e1000340c0c1c00540b101d401210407102c4403c10003004450280f54010b041d41041054949070000544000100c020900c100070740c0d1082c4c1000c005030301003100b1404252104061100400080a040e08040e40102000031000b0112401060a8401c080903920100d91055904610105009c104a40f40945400c00c01c401402a0b145ca003161464070380140c146843c0c1303410582c841030250b605d98114100071030a41c41110a580d07481c982100ca00041100c408002c038020f51619019070040c0b8840e0b080740110a51003809048140c585218030240004041d1805505001d410800800252403000c03504590105501440e00c51031018420700c0d03100c010350b01140c001c00741004140000c0d50702680202c00681c10040741ca00340031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 907355494 1250 907354244 907354289
    0x2072307031221110d0b060d0c0201020912010e1f11181201060b04060509060c06010608040c14010c0b07140a022b091203020a1203020c0105071404 65
    0x10107580068004210488000d60960303200010000c0003040092105800100d012007108680484003070340b00740035081c0003003000e00700710360011058084018121410710000c1c0c0701e00011116641545c9000d40e50001b00041c0b40c3c103208005c0c4c001c8400100c002c1100c64031301071055455800000104120401e41c803a20036000601d0350100109440c8003c1c502c2d101c4800105d2024070407510160140f06010112103902c500005006131429500602c4585040134500101a034490300118180c0d5480007040c000000c196008004d04c034000c18041c0d03902441c908042c10901c2a00d0f40541010340d030008051301c030100300e9811040b801300c60b6074002c0b0510300310350b20740760222040c900319068501c14034000501d1015450b07000504004c00e003500b1000203488040028007801c1151a994650003045280d1010056030785810403100302c240c028016281d03012004d039140e84010101c000140301080d03001c04c0b4011071a50074070405d03501960300d0070041701d00001d0450001d46401107114204012044005071038200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 907356744 1250 907355494 907355503
    0x50f070606170f121c02040518071b050703030e0d02030601030b0105100914100207091404120c020f1e0a08061b030408040e04030c140c0a060201020723 67
    0x2640000007045601e8407029115002c10703440814040310700c21a800071a5108001c15003011841c2180c1da030340d10317104100041c000901140008119056806d1000183c2ca40325480e4200d0740c0000e4048030291482c11000150880c0e02c900440d00f44100c00031a07810000f03000080301810390743c1504003043e0503000ea5000500b12502450700075058050708000008114100301014160b40d03003114010101c1100d0142126400324178882c1c507100740e005501c40c00603800c22442c4013850740098410780b9416600d82400314160b500c52102c0f281003219200810007840000c0801c002c04030103501d8030f007820550f50380008441c5600105034620905d45480c035a241031944605440c040707407025010900342a43c071081c543d1261000c0f2000150380641445050341048458103da10513540311506c1d47c00c1c1810046201c1c400390000b0411400d0081070701c4d15101265261000d0420401400014420040702e0010b120002c01c1d16803100381560b00602401e40001c2010710410220b100a143d2450300001208109241 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 907357994 1250 907356744 907356757
    0x30305070221011d0a03080402060304060e1507170105180a0f140f0117030307030e070b181002011e0207111f03111204062a12050c03010510050f 64
    0x800340000c000300d0454064102951044180c040d0340210313a10290b40c41d40703840c3c26000040c001501d0b540010011300e03004e8065a0818026407000034601c0103a0f504a181c100c0c00042c1401c4107100504201d80b0b11340c408c0c01c00304a80340141c1d0503003442d45450040360074841c0d414010071110ba4600c00180030090703254421030800340302040900a903220403210b2420b0501c1904c070300d00312039088070010900d0081740038045080e000c000015032542d52501021002000e2000485043c0d000b0b1100019105111801418980701d4288044440b100702c0320420101c00200e008640c02d590408082110102c0324404001040d80380c190302580c1d4408516045a0309410f50071910390221780040e40724041c000c40078944541c0c102e291410423600006000c0000d6500511540d88065038400d00001c000810b6070700050307600034100c03040c1e103891448140d0801600800f44c4500002031103091200a81c85400d014954008401100c218519414007020400002d07024400388140580001d02c151520042c0b07085445 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 907359244 1250 907357994 907358029
    0x7170d0915030e2a1c03050a020f150136110702040501091d0a0819021903020d09050904080901080910090602041d061e010909020c0c091602070303050702 68
    0x1c441d0f03051100e864520142120005201c010b5895020071342c108540000c0032401c12210004500c450f540c0c04554903403041c1182c1c0114001c0701390410740d681e01000000e0b0078600011601da015810003c2c421a00c000310b40c0f8411091021803000000009031004841d800060082d004c9096002c18071012102c1c410460000e40040c0340000000348092683d1061140c40c180a111003012a41c20144586da0080750001070001003081010b55610201740e150a000c07501075005a510b01800c15121030710650b5209000e6015070000b01191865541c048a8039026001c00c9800030b40c42e09040e01c1d28159405243c0d0741c0b6060104880c0421454413040080c160501130700c90341030040703803080d240050207504035100d0a442120402d5400349158580468503205010150070407020103220034400ea5180d0803182d50034180300b038034a00400c26900d9030006000c0159800d000300320200400051107003400c070040404840c0400c980d141d1200b170354007007080384c1200d41624100d511445d45000090809000e18404c55 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 907360494 1250 907359244 907359253
    0xd020a08090c100e06270424050d020a05040504050109020a090c0210020309010209090a09120c0213090204200c161d09120a0f0e010518061c060807170d0915030e 71
    0x340d403000124910b01b0000a840502c00c90840c01c4001c5204600c0d007140d107040c142124000c1c051030402c40c80305903140c0c0c002807030110029034960204040300c1050743e0984441c0d46440341081982804014640100b071b0006040001d142c1c1102d00a44407803814030905460703230300080032400d0284250156141c1f02001050280141410a29003000340a8144100c2c2c1e100c500c41c090f14040e0b030003101c402d92595009000103c0182540c1c4540780105a0036400703c3c0e016030b880d0818020000000c1c000c4600c0001803003100e075030300ba61510395442d1014804442030800304181050040d9841210503541c140452024017520741c0f0742204032828105450b014849060011a481100d6603001c091021003020031b446201c3c0f9170107a4001107416103c0c1100500c00000800c03e1540c1c0c2d410280003c2030004e110103180c1c0007150001e000744055981035400700d0923a81c4600c2e002e0140c50b05a040704009090340310f00030724001d03188034006000300d1494130800c0f80c2880344643d1603120718003a070003a001c0101c500090701d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 907361744 1250 907360494 907360537
    0x3091008010609060302040f0302010f170c09041d0a0f1a0c1810021e0304050d111201020702030c15090d230c060d020a090801020d020a08090c100e06 66
    0x42030200248216000a0702c00c0f42d0000799203020b48201c50542e81101076041d950760550300103407110341003600d0410410004400850000c0c079100003660182000840b042c0c2e1750034041c0100029100d0400642043c0510b064022214100009451501c4c80d070000d8842c2030311140d0b0500d030640d140d18111403c0b002c60a50100010140c41000030004550b0200780500c070081e0040911078021800c00b040e02c05a40002ea0f0780a40540c0f4410689040e02d20500326413411340c1316008504a0403034500200c0d40304a100008036207505c0c11100088141180c0b000841c201007554000039540d07074505030303942c0c0a14151221881c004042c10100c0e00d0450010300100c5442a0a02d009140b0300b052481003d652800c9030380c8040c0c1614041000301100c20020085414814613600200c02075103c103d40d0414050b0782040017481c00403c1c000303421410804480140c82d8103041c1c00191950400504003440e5801c00943e103020340d41c919150040950903858061b01c04540080802c415100f8680004d04580c00361846 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 907362994 1250 907361744 907361747
    0x1318080409140f1315020d0e01140912031501120e06010801151a030c07020a031a07091211061c06241b05010f060e0a05100f030b040203030910 63
    0x80d00208980b9114450365008030ba1000c0090a454540c4142c0c000c00129002c03400840c60301205203000c1c80010b180003040355003001101c000e85604803050351190000080c00d00d40710502c1b80d10000040184c00700104080c0c18216900c001030020a2665040080d84a2039100c0d5081c1c21038070b8001d007010400c0d8040310804a0f6a0343c0309109654241d07091022506250b00b10100c020100c44078011960f00110f03011210503141d0f00300500b0424000410b200d400c2c090b9a0307074041200114000c0c10400000400281442d018101c0108032005001c041d40c000c00600114000140000d504204d00d058485c2c0c003500001c0302441101840c001910801c5288082880706601a03011a4943d802420715881071002019040c403103045240049003001d8409a04c01c0d24124906074401c0c40340000043c00803130400c0042c12622a40c20003003d00b11000e080120010203031051540003004803042c062014a040c026a034270043d80c3c0002004001f081001c181152003c00a860b800e14009009003080d070103c400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 907364244 1250 907362994 907363001
    0x1802041d0601060306230f030307082502100305060f0406080d021c1b0f0209010e06030625050702060f040311091311010804080d05010605041a03061318080409 70
    0x600d1089009003000080c5040c00f901c40c0d04100c83c0100c10340007036500000c044d15200144d9003e02d94022000b51424001d50340c0500040006511810402d07450707030301c401d15402d00780148101c40c124224a88040c0c50240c1d451001024075210107140100325581c441c80891901c1c0f124044194005051003004556000007061041018103103074210759100d4640c3c0345541c015290b144a540104103d000368065900110907065102e1f4091213180d49001210340c00310315929001d03440590700c0b845900c18412546414424076810000c400c41542d0003034000350424203440b40c500800c0c02448000125003003152a0801928401c0c1d8500a406803501d40e1b0781400c080b5815a20041c51040640740b0010303030b01d001400040d000c01c58000e840000242005801560708200103007060341d840d441844480c068801500810340031b001c695680544403032400c40c010009003880ea10f01d00c0740c40c03c20b00410080e612400020b0780c081c0d40c2d103080480c001500c0601c80c100414103400103006d0210020700030601820942 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 907365494 1250 907364244 907364291
    0xa033905010e0d09180b18102309011217090102101d063412090f050c040e10020708190206040b0a06061d0402090a080604021003021c180204 62
    0x3003040142d000417506401180d010810f059441803e4514844a41503550700c160390015640041c40b01030360300d1305410705050320540e80c00e15511040d40203d07031060411208043c014041e0104026144800303644007141c8020380480e041c100400821080030503803007048441414000020100f0000da01c030565448000d0520304800d071548295400314003402c107417000960780d14003460401411403402080d903580e501d4100e10b086040001c402ca031041d8210140c400c10300c0e00c074030032403c5a40403c0ca030f113442400c1142c9803400c03a20031440e1046450050002140c1c044a4550000340141d640520b4a0b04c00c0c03c9001d0f00462407000c5803100200c819407a00006c8040c01075028044810740355a91612a400383c440704d02070800007400d030383ca0300c90000c2d181982c50120f005d8010400b50800340030b5400b08000894940c402e1509920000500c4158100100c04130070320f80c0c180c40c0039490030287e1507007084001403400c80c80c4081c5030344141c04000040c2c0442005c406079402802441800c44401c580040e407001c52 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 907366744 1250 907365494 907365509
    0x20d02031c030f06060806010c0305090102032106150310050904081b03031f0308040303050306010e130c08090a0c171005010f140f090a1119020a033905010e0d09 71
    0x48020807a9801604800c7c40303038030144d40c0d0300c048290503501100c1c3c6810110106042d803005001004184e40800402144080f511048003903d262400030082d840c44621451095601c0800510580c00c203054510f1007902d400b560b5902d031036140c1e03243c010085d200f24054180384880f0100305400c1031401100071801f80071200b1001810300d611a0300710181c00a00c1c071000744540810802000040d00850145d41d00200506090401540020101d0b00301060102c98841c001c2d5100070400009821021b000c0c0c0000188e0014010300c0305668900556000d90300410b49100d61003484120098001c120704554081406400c1c40556504c0305c80300c2d400c4001e40105c034105214504e074440d5506001401100ca8a0018960901c03515003500701802080102c0001c056243c0410a505940301c2d800b043c098074010940c02000310070203500b0f0041014203d2011001071460100512003810070a00c1c5003c3c02e01076850103000c0402651410900400c02904141d910b0302680402c0b101c21b40e00500c0090071950700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 907367994 1250 907366744 907366751
    0x4050601050a0b04061d0303130e0709090213091107050d0c0b0637030f050a020a0503030a2c1816020f030403121412040203070b0313020d02031c030f 66
    0x40700f6031240c0c2400b4a0160100140e070140c40103c0303420040ca540301d1017803005402e8a151114002d01d0f010128000c2c2c00c01074802401800303020806a100f03035003000426280744110f00f06101c031010005101001c1c4078058040c0d440f4807450869403c05002c9402c996841000c507522041110300c06802c1c4585c01e8030645648d403d1f071001449500381001c0c000140c1d034103000d02a010f0100c40c0d0002d509564080d2070103501c8140c222001c00080c848800000740103002c2c00007411800c0301e600c1080b250132031a40120380260805e00013222043d0300301d60701e03841d40d1844080b0030020368007898000c3c1035204000d042c2c0303038015034010300d40d6426101d0b4840e060203001500400000030244034000daa0720281101c2040c0907078010042003000c80d0500341c6500d000c0300e81d490203040c42c890541180a0740e8001c010b0504030510030105020861504018082c0245040c01115045141280300c01c6915001841c2c0640900c0264420b0800c41d42c05020400501d070b070201110300d40c03c621a038006c008143c03485c1d11228070303072a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 907369244 1250 907367994 907367999
    0x4230f070f020c0405180109150513021309060902090c09090a0203010f03030c0c0924050a030b460b03010e070612060503120a18320904050601050a 65
    0x105044188a080701c940041603c9006001400000c10700200280e0500c50003a4007558451002e0207815101406520003c070305201d0811003000f120720250881e0703980b47d5400400ca00580b1007008000d40c003403011000140d00ca0480c02c049015111002000390302c649088104551840c0d8a000b400b18074105888440d925510340a50b40128031081c007034029240b400300f00c04c000083c070030501c540c074080c864032000c6481a603544117503085d944661469244a240031a0038540d04542000c0800106400c440003a10140355481d0702641c110042c103e40c81404098841d404068181e200c500420300845042e11071603d8982d00c6c00d4004403104c00c000c0e02e0f0600b4521607035413518050041d075071002032020150030614580078040c0d0742047c11a00c001c140584517600054207079028003401c000c5082400c84150340740c424070f90060007a450002685c0104003100003c0c000300c3c580409100304102c0c1e01e001c00000d00802d4659003002040c0020711035000c0442c07403c00041200105501c3c0c1218003d40c3e40b01000303034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 907370494 1250 907369244 907369247
    0x40311010b0612090d0950030f1605060d02120106020d0e0328050a1712180a080a1205010f1502070b090d29011509030503071104230f07 60
    0xc00314410280007028040d141ea41400e10807e611011601e52443d002d42e4268a44c0580b0320303c80c6100000700c00d48294240a0710310700b000e01c120f210a40143c00980311654055800c40580315003402564010b07240410604d444010035030450780c2d01015480420225a075a003002907031b0311050003001000507582c400500032400c00013095120380308154916940385210401c02480c80461710410707075241c0b1460710340340045410810081c0c3c00e01756210480e80c0c3e0300c040301288494003501502c03a49400440946650b0700400c0800c00703814003544203492a41d42d80b03200c501241d00e0410f0f081c4030291103240000009a041c500d050450848802c8545285e0315100300c00e06030b0703c400301440742c0c4c0358140c01008608501d2420003901e05180d0b101c3c0e11035100c158000c002c01c400d503030101d6194040f91a820001480003400c00d00089d4001859880d0081c00c490540c1c3c0c803075440b030003008401490310548800d1507030180d49a030400503c048a10100407001c440c980000441c030102a076104807a54100ca02050416 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 907371744 1250 907370494 907370507
    0x4150b0f06032a04030f0210050313030c021311040305070f0501091703070605040303050a0f060b0d0509070503030310060809010203130f050c061b0c0d030206040311010b0612090d 79
    0x2003800800c100d0460340d400031007200d601480c00c0d15001c45035000b00110b800d1030b100b00c0038202035401160210b18205a0340305103e03014101c1c40d02801800014810400c6503030f410782c031400f82d85038103150802548002e40f01044000c1c00300107107000042c0c00c3c040d010380c0700076100c0040c10449020750304903440255208201e92001c8c4003130007102e00044041d031050000b540400100c03440845540201c030702d4400d00d525030501720792064400310000381e20b13a810b0009982150151140c030741e060300d0080006500d0811211124440e200c400380c112134803a00000c0d1044001c2c0401c42c0100710140580360340707150171081c004049101d030041d040410030344000304018110520a40b071250410b610550005082912080c60100b104002111244a5104201d0f1103885441c0540201c040041b10303494a01000f034070300b40c02d040e01c800426001d21166160074022942c005045a0055014101903241d2483d00e940c05014080d0348135802d41100c00059442d030b00841b4071a02c1403107840307004c1c140c0d10310301c1202c04101d030354 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 907372994 1250 907371744 907371769
    0x6030b0a051801170708010c0f0e04050708070f020a0f08030912090f06070503190503100806152b0b0a060e091b0d0f0b07020123161704150b 62
    0x11404100602807100064a100302d418139140c1100c07465a5030b45201c909554416200e04006019030080002c0c058000e07540344011201182c00344114600840000c22640340285410300b048020b010394050315009001020203036811a9080e01c6600e6242803c0d45c1c180e01c180c8034480c43d445808203002c1180c1c2d007001a035a040314000c00c00c50070300c40a001000425000003100ba00c4601041040c003404003c0d4ac00300d0966442036489043e203e18010141901d003c50300d40c0011707040e0300800100071240d86000301100c5010800c40381c071401014459041d040c22401c4005205142a42c11401c0c030600040d2901a07106a41d8114184003164544002c48400b4909441148581d0b00035406086408203030303c1101c04440d00a8178026820750315454451500300106000d5807085103400502a400764280691100c0c240c6030500c10300302c8640790306210a94240242030541c014407102075010b80c00e00c1800c9040b40c440011881118505140c14405501511520544042c1d4070341116902c0905041215000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 907374100 1106 907372994 907373029
    0x181b060310151d01020a03050403080d060b0a120528090809030102040303030905070905061810031208250c08090a080111030405010b0609130207020f060406030b0a05 73
    0x70711490110703071811504100e0300344003c01d808c40c04441c1140c0d40141100d0342d848220031110700030311854201c00ea218000103101d9481544c80204480620b80d80e940810058640c4110340d420359615020081c040041c40990a01e0611958040b60b441801000000d15003500d910020342241d1054001b00e000c2a502c01094050060400250300130f410440d401f0450741c104140050740b084100380850640701045030005090105101d01c4800844d84070070211654081c40c00054a040d0007141d042030b00500c2006d051710300c2c681a101400d0f8000c400d440b02c0c00009800d403a4180b80d5880442002e03001262010002410072091140c0034209191041c415240c4c10030f440e1650130f50340c944c0c040502c40c4406101b00ca00b507036030360ba00381540c0c4507643c1e8006995035554404510840404008e403a8803403408500060300d5a0550018031000b18101c1d07103980101d80310000c1000b90000c0095114 = true := by decide +kernel

theorem cover : BRFrame.Cov 907194244 907374100 := by
  have h0 := BRFrame.cov_init 907194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 907194244 ≤ n) (h2 : n < 907374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
