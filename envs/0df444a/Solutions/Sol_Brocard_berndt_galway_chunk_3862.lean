-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3862
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:53:33.987802+00:00
-- url     : https://prove2.me/submissions/97bd949f-84aa-41a1-961c-63cd916d8173

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 694424460 ≤ n < 694604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 694425710 1250 694424460 694424477
    0x2103030c0c010b0406050907140c010501090e01051003020a0b09030c0603070203031812040b09041815180c060c1b0e060906030303190203130b160329011d0907 70
    0x40c1c50b42510340708542e16000d5883c2000c10002030340c1d01d492080d0002c01905007400040045000b58085e885034100e201f8070b96080030000280030600c0d40c410084000c2c2070008001e140c94020881c0344210051201139805489401c00f40184007150000302900e0300010111100c1200c20404078aa9402c00c45041001d60008403c01c0f0500d484078483d80446120003000e00180c4850b401a603429000340d00603010450004140c22400d912254803e0701200003c80003500074801a2034011000c1420032404500c00d0708041c034011900341c46150389951540d2104c041710f0802d090200480b000710300c008041e1085610200c0d041c8042134000b91460113005a40304607220b23480c103401440400303c4080e144034003d40c01001084130180102c03200d150f201000c0b800c05681d0307454441c45564032018841000d0180340000007840b046418981200202c0710030780d03d0030b00c100005208a003074090450b002607055591404400001c0390700c249801c102c0c5d503a425034011030340320450000c80d400c0481100e1400110384a03a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 694426960 1250 694425710 694425727
    0x8030109050106020613060902011443060b04020906070b0a0c050a0203120402010e1003020405030f07050105030411130501030818030d020a02090a02070b0f0403090801050f062103030c 81
    0x7805400d0141409000400142c10800d035107001b200c0314a440901156680d441100c1168818041e4150906242d200e16032a10100d56001c9600342c9071506040311002144400c9102c4261034032460384964a040d2013100089694039000058281220125442642013084034a156100009442107501520002945150180304a0222265581c0d0307501400303020322905c404141e00204503481c604241600c21440e440301e100603150302e107a10b01c8660341b10b0307000f100004000741c0c140e0240007291001c80444a902840c0f46400d03485081d1170040a00003041040041c021801c0c80714007000c00e031409400e202e0460206078191007151001e8200729548140002d803001e40c003070401e4808461110403005000d411a018070013130342e62110110001e005200c1400054040000e6a0540e40300381c0e0040941c1c6000c1c030340101c1d00151110308660490100701c40b85804102c80105105181c803800541125810136210304c003c003c004204201000400070103125114142a001c0c80654028101c0104968640820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 694428210 1250 694426960 694426979
    0x60b03040f061116020f030a02040507020102071a010510080702030c10050105040507030b0f0d060902030a050f0708070b03011202060705100507120e0c010e011e050702011205070c12030216080301 86
    0x41c031038421500f00c06100315110b0024203504c2c40c412590413a90700003104100400310b400c046501c0c5000e90711625141c108a469501034008000880c85009258180460b040c02c843c0781050a00503150412440d41303521016a0060000c190085054012207080460b80814549003800411282949584600040205081a0049541081c0c0904050048020410200e8160041c00c1c07001842591001d18840600c00036501c107100441d009003c5d41c01c00c941e242010b569039040b00024118601c00d803880003950b49808500030b016034084000342032031a481c05101d040c0480b9084401c1ea40701004001d8400041c03001c0004084001d5200c00114191610400280c5024843c4c0f00480a01c0e0904a040b03280b5200440d01c555126004d0804071300b400700e1000121010519141c07134603002580044842e808507008006882c10920036aa240e000a0100c80c51034107454090b035409012030200b403054000a0030354041000250b40c1850010f0030300490000c1052200d10418068950000020060205001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 694429460 1250 694428210 694428221
    0x9090b0604200d09080301030b01050906150306010e060f0d15080102183003030f0a020a022d07060503011a04050307172407021b01051c060b03040f06 66
    0x14111010403849100340c000b07001901c070078018070035920000102e035038000000e540510010341d0010b0615484e90386925141107110001c1c02078600c51911800051030a04e02001038102c10b5840080c103a0442e1108001941c2c1c0e04000ca0240c0d030700c80410b110000c3c106030000068281400d000340b012135512030401da8600e0441050b00302d103071181d004000e08a180503020150011110301075a80072140904030105001c1c0989001c401104030165040c9048070040010245004031455070100d10142c40e4000000200c0c4141d0702e034034025030000300000041440028003034075281c1c04130314102d81441d0156042e038104000c503007000c804580040018010b0300c0c8200340c03481510455000180c541070524000075600c0301244200146641e03400d0b40088500d0301403040c2c200722160405224803062254004614606046440b180184a51200c00c030300c2c00503010070305440b80e0044e190310749866450341001c0303880441410001001ea80303440d00002e00c1c0303042d4002507105034010180d1402070300c264909981034a5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 694430710 1250 694429460 694429471
    0x140f07050c120f04090204060c031407020d0303020304020112060611070504060605160c0b0a0306050414041515120305120a11090607020301150902031807031505071809090b 76
    0x510141c100d4030341c00640401100341030220142c83c0c800c02811400c0381c1c032032600704464103400401c0c0044c503560080241031543e0321036180e80c4c0c0c466031403507000003441c062200082e601021807414000801d0080e8000c503041801031521601030b0442640210651700c0300d51007400014091400c80c0f040f08414000c5002034541118203000d418a0504000c000f80a4400e00750344007030040301e8501c10000030450703000003808a17900b0703d520346a003d40041c00400c064800c00d4000c9080140f036a0641c202101424881d50384040204048506440300d038000301451070075021b44101c42500416206100200a0368031482030f91800da0300d06042c40d41030011503015004050b16414118640302045500054410b030364801e4560b0390f01c6071014000207015000b140c01110240c6481c600208103001039070011482502901a00d102c40414001140e69540c1544030240c4084000c4071200d00c6980581c0103a0b030014039500d402841c903020441210340d00011540031030400c59480c61040708210302229840d5003c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 694431960 1250 694430710 694430717
    0x90207051b0105120405100b040207210c050f0607030c0513180609051302010207061103070807230d0207050a050603130c1203020c13110403060504080d140f07 70
    0x90903949007940c034482920300459150459079070852603440b403000c0e00d11380072000100245500305410010344843c0072404c0a0420703801c009400c071244c2050300880e400203034000281441c90038010010841410740108143c10403030884601d0005c680d0410180e0305510707050014010600306094081c00b112040d041e0700f401c0c00002e2000281003038102c9103800c1210a042c2290048040040e4a50000c0040d90029864540f900c005d10482683d07090031842082e10030303022600540e840e0300050703400c007010701e484540c139030320402c13043e0300040d100005000d20910994400c0d00254162042000c031044140701105194884002000d400780d0421640b030050801341d890b4003c081c107203030110704070344801000f00c0000860608800300300802e496041000b80807030b0038241c0700d415241c1b500940750300000003c00e00c2400c140a51b00c0303000780544111090390301251940c0d4585491035440c0f40c00b41c82c006000b0b40381074006022480f02d201050007040c03880c6a00c91040d942134505460000100343c3c002d40200c081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 694433210 1250 694431960 694431967
    0x5011a0103140c091c0609020a06020615040b152d030606040b1b070602101103150d0f150e0607022a1c0c031208070f05070501200d060902 61
    0x400101001d016005100d00014560350707080040403c1703804040c4c040005840700a040d410050100301e910100c000382c401c544d1290707090741d5000e049a80b440103450a250302412030210201520b426407100140c580050407000035101c01d00c042c0003c1c0e03013040308000c2e03191907401c01e80800c04201d2009030b41801d10303800701541107050007404590f980c0218095071080000c0001c0301c84182c0c1c0352440d800c892040318400c9400c0ca40c3c507584000d49501c4a107e140040a06040318580a403d8003000c1e03e1240d13080a13141100404840b082100c0e40405000c140ca180c0321940207240805c8500511a4004007400c070003003411044143e007a07240c1000240b00c0030454226002d14005c40450004ca8421001545210001c50410500080054500708140a8043d403003206402c2007109410078407040300d0294405d010f00044a00b001d4601c04002c480400024095040f141d0619008034043c2c0a80c6001c0c40000414058407503451103520461004405000707408a0340700400045402104050444800203604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 694434460 1250 694433210 694433231
    0x5032206051201030f030c051f0b0618010f1202040e0103020109080303090d0806130204090504030305090d0509040c210b09010602012309030915030912160b100f0305011a0103 77
    0x240b4403041c003008020703001c0d0000c1c060074144503c160160b010b4001c03040d640080c441a00e1f070b2400c0441c84192003000c900b01b8045411501d440000c3d105801e2000f1841001040820011541c0e010900450400d0202c04170300350407040094800342c030143c41183c130901f6813541140000b51915021350b108820580c4208200064081c0110302e61009500b14100821aa00c0d85000650b0142460850034803052000c0383c0006c540390150040d40c0550300945041020341c07031700140039031154002d0b0304d9040440c0c400c003c032041604080d40106011a100d1504041e00d4210744800340e842074800d1a954000394030381c0c10f555141c0c0362032502c0d54011305260000f00003401c1283d0304102030641c040c030785000c1030070701e0400a001164180115010000010030350780c003800102d10940e1a580041d20803540a01c9031001c0c81420a40210480d0480c1d8100001161414840c0d43c8541200400400340c400442d01c165001030002c002070a100040c51040002007000c1004040d01142044102045410141401813652 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 694435710 1250 694434460 694434487
    0x504020f060307050a120e0111030a0608150f0408041d25020709020d0605180a060603060308090f041113230d021c080d0e010b0f0109060c0f0503220605 67
    0x3007410b011820071b58108142a070420005002c0c40501c14200e500b4022441220003450000f180b0071035001d40700f0055251510b024503a1280004a00103100c1e00d039801081c0c4040b1741c0d205c22130b4407904c038505182c034140e102e501d14101c44000c000c00c1c05041004105114150300c1c000b01e0501020b80c0c0324448900c0e04550003009540720714501c42c9440c080e9000030340f1441e980310380c0c000380041c0c00e014006501c1d200c00b280040700000000c03103002c07040905d03080b000300e6624440d0048800b129084041d00b409e1128030010002121150002642e205030ba40c1840e0511000c4140034041c80c42c5808203c9a405160850402c1480158001c06c58220482000c0460942d0ba0381d20001c821501130741e000e544412042a4080c0c500130000e8003406801020480103400285900150a18003040009110080c003090910240704007040509020900800090011902c5080010440d50140310880450b4110380c8440b0300716401840c0584003040d0042c01a4551740c6141d268000406582c0f80c07842ca401041c2c891007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 694436960 1250 694435710 694435717
    0x1f02010f150611031308030310120f03052a03180102070806040609080d06080c0406051c021203070807060204060212070c0311010c121701051c080912030a030504020f06030705 77
    0x10024800c20755030206500e04204107a175004000c6400d4800500d440e15000ca035a9001124500b52030030700440c01092480d1001c8400c034000d94051071040740c030307403260b642078a0680044401901002005110300c0300c01016541002c0052038007c0a959103a00c1c804800340e400280e07588190541d4442c0b0b40410001c800028101d91080d0003c20000b140440c0380f03131030f11951080b14072440c504c6041c00c1c40802e4400d40401c10003c600c3c021903082014680d02c105102810046244ca00d10b03240107112410017500707203c0394681303580800b0f02c1520300d4602c0c03a0b6200845a080810191046540800e080c041d41e03404024511280406845450618610390381d51a41094240030040c40c0c101807482c2d2642c0b076409158082d40482c0d00403020314002e0364008005001e2070200d01c06a000109140c000a100e00f407806086c141d103004982c50b00c0000751151284440e56105d80c00c0380ea00603802004188694000340090000d0944c2680c02155508043c01000641d0f80041300c0c01348507410800c00d0005190304074046 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 694438210 1250 694436960 694436969
    0x11150c100f020c06010303080f3306090a09020405041d0d0c02041e020c0115050f0105070510180501060902090108011514040602150108011b08151f02010f15 69
    0x1141207440c074900c11010b406030701644401482104004000c2541012401303100d16448041000b4580d1480c6140e0540d147d240e80e858080484036085d84554410580240307a8034101408052405680c400451480f0205a0040355000d5000c1001e00440c6800d0040b40d83e1080703040c88200d800382e04a00060748a1002000c03042c103200c0c41c03050300c20464859400018280e139030341d500324800c82e0812071341e4000b07540200d140403020b51802c000000c1010b414001802039580141c01d0300a40b50f030480c01582da40e0320240040e215403003510001060801140160310034400c1c80c00ca00c2201d09018941182500d0564100c1030140c2e00502c00b01d40c0b10f90744150300604603036110104e50107540704c00c5c40c192124a100315495444010014020a65903000501c265440703205016810150703980d00402422a600304201845c4440c00d120030129480c492030b643c0d0780040030300208070301a61168000401502d038034540354101a480282c40f0714056020320030000c040b031070403009000c0b462a42103407982c202500e014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 694439460 1250 694438210 694438243
    0xf2603030403052d181f08011214010c0504210201081306091a2406180a150201050109060501110601090e010221090f03040e0c0304110303030411150c 66
    0x802c40081c00c0602994450b5031342c0124120769070100985181c81e0410420455800f807114004151700c41030500a001022101d141e6031000c080c1d00740315044025024001c401e60b80d00c001588000c0d000042032181413182c01090f102e0341d42d00c0f440c0c0b07500120251011a0f02c9186c4125550101d40580d801100d260382c0075251041554040900d40350060050241800113011a0500c9201003d600c544c0c2408502a1051114918000184150081b650401400700541001d03090190141c0001229000c01070000000c042d00001038851020840d02e8a46d54034142c010b03910b4000400800110740b240c0000390000b0b2070311101c806400320780309654240601c1400c0d0441c3d9203800c0c205c1400c01c00e40c142c0e4420201f2001030480c281d0446c000d11700300e072801e4aa0310700300e0281a00640f44800c1c008104c400321803800e2200e0006507034510b8401100d420051080e920348042c4489080d981d54217100231840b072032003240803000310400c0205001002d0489448028207a00410400160382000651008900300416 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 694440710 1250 694439460 694439497
    0x60106090b160b0f0103050c0609060d1a090705040918020d020f040f090807140f0a03210204090e120901050706050c040302060a021e1504020108040204060f260303040305 75
    0x103404040000c1d8845000c0c10f0225114144031341e112000c03c055040700d024904658006040070100b04161146114269104000f0805440030380c000e90040a0380c1100281060f200754102000304540a0045680c480020800501400f010144c1e105e400714004013101e21a000d01c0c11035001c2130901d5000c01300039100385006500e0708855076440c0c01020700602210340a12960000d41342400f120742100c90100c0f501821340c2c1141e080440006068030700220316000414604440d030320280c4d005618501012a104409085601c642c12140000d200a02545070001174a8001245031070802d050184e0340d0051f10303020004000707160307885010341d15899007204002400346c80700000c2040603c41c46c1d0000b50044000300d51071000980210b8603015581d960280c0346c08801d03241140c075898203014203020702c4c2e150798140030401552140401e580d1052003c1e0002440d60349544043e030210b0b01c1a8003201c40001c0d012048101111720344040040725185200850650030300b50360140c4a4064145c040b1030100641 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 694441960 1250 694440710 694440727
    0x9061005091503190b090d05040e090304120f0b16020d0f050c0d0c171303061112042d0507050d020d0609050c040b10080105120f011814060106090b 65
    0x1002d1111030000080840d40c05004140c2c0d402e000501058040d01ca80a0b9800040c29955000c602c026000e03141d40d40b820302e0181842e80300100c804c5c0181c00c1e01914032092101080281409180003402d9000e910210726840240c54a803100340402440e509004605484415080c2c0e0001b88081c1e4048050070f0034801040403810848040c0108503200c409440740281c4005081c1d041003543c0c0c0554000c60250640b000201d50125113407043c00111114204247d404101059a0707521210151240b0ba083c40e1904828194040610f18191001c0e03540c035840c445900349485a4014840345060190801c0007110300503280c01d07032100400c1c80b9050040c070b07400300b80d01c04561b6503003d0170080720707402030f020400b0b6089810903d50b20031406140a002c0d85c6012414080c80c5010b00310603021004903a9440300c3c0b0307802c060a00a010300ca0116103082c500c1403000c140c88000080c000c81610280a18040a10202c2c0741012144003100340d54004040e00f1640c01407141e164001c1e4031600f5034070740d689001e40d1100c55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 694443210 1250 694441960 694441981
    0x2010c0c1203230a0c0c050c0d031b0c05030d02121e0c0d050a08100806063604020f0a1203050703122c030a09120512071203050906100509 61
    0x12010441c0b66150f00f0340091040501640c0c810700034050200200105191a6000e840c0c0030350b00a4090550b41c09440e00340b01d50300d00640d1000f1481c1c80f91038003146c280740003d480c030032403580000304440c200e0080c0d000f0b0107241400c0080c40514a8144000c0103407541050341c4501074420580008480b0f90303a250a0723140b4030001030840f025580070b00215080138040b440c000b03085400002400d0700080303044001c200d416514803c40b90944080324050031a03074844004200800c0d8550101c46e054030720803840c41c400130340c0150743e8801c408008246e55816107840d05c108035003440d19211243c422400f2400910464180c00100c400243d8581001a82c5882a0900351440d058600800400303600704180d0b00f0f064001e03201c01500e41c0d0444002c40c8280300010082c10340b0b90142040580004184410401c521820b101403090b00c24010002d660755061412007040b5907910080c07003070f00c0180c0060b60403941c1690500c9a03581c441c141d040030300080e003080d452582040315607104a620582103000032074244040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 694444460 1250 694443210 694443221
    0x70b060402180f0d080a090305011401030b0708060316060c03140f0a05070807060504030e09090703080d0b120706090501081f180b10080901230112050313090b0a0602010c0c1203 78
    0x8002000c142c40e02d0000e01c1c007d001903018041200c403035080c24032607008142d030250164180c90384071051055954402e00111000c9000401c125454400c3c884404840d07030390078588401604103035880c3e10a1221904001c2c0000ca000c41c0e0b0341c0c503030f048100105080d00c42658152480b100113850401e030f44040d542007044032801070207000307819180391206200405030800e500d908414010b41d08142d8036520464040d4807200300e48000781800900308070051289040b03901403502c05200410b50b90440640c84051854580590807907004502c0d100740510071076801072074445c0c2c8407002960044a0001c690f041c10041780d154491907001c5a884500c83c0f0248169820001c0b099a01621050301d516203040001c090501c1540e501c0c0c103035442c15168000d0480040d80795040f940c4800d20200040c3d1074203000090b2003d03903803020b9400740414011080c2c950a130081401c020012560041380f0324100c8010402d5a1015600150541e85000210320146812141c96025140c110320b41032641000b00e54207901510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 694445710 1250 694444460 694444463
    0xb06011413260607200a11010915050f07031103180f0303070209010b07170a03020702041104120f02040b0a0803030a060503060f010b071115070b060402180f0d 70
    0xc0c0081044610141114011801c8900303075010a001400d851085800c40030900074035140c0c40c0c01034070015640038015450240e00001c440540c05080a4400202c1d090600c414412076004920400416480d030384050810090140104081c11564016901900328407031141c0c451620030000c00c0d03000c00c2c50300820060800c1c415080607280e071109220064400d000654810341e04c9803041c900072501c9420008156020903502903c081c20716400c0011055990300311507422a01070a409050b51500f4918401610442e07595440c0561190440d02c10401a0303040072801020000040c0070030419003d103480103d0030701e030f0003400300c02e41c502c128000304000d032448914294004c040214001070503240000114450544810204141c644070741c101034032094107807180d2150010910060140740d4007080204203182c4210600c07500e0540c01e5022441006440d06900c008040100d818002d014198103071561104044404500e00452030590070b00490900d03d0f110f00442c1d40e25007105c2d407a242c0125002da1f1a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 694446960 1250 694445710 694445747
    0x1080c1c0603241103060312070f020307030b070e01030504150f060503030426070605030f09030702090103031709120d02090415030b180303040f06092603090d1b0b0601 74
    0x2402d04494003201c03c2450400f01441e00d2030400114609207000c42503d00901006010746a0400f80301c6169503c0c1e046200181d030805409040c00d001030380c0030485400114030800c483c051038070b0444406003214410300b501d90305142c102002c0100141c41c0b03030020b5680d10721101c800104800701036410340040505400142d054400081d001c190300c0940080700c0344078004082843ea20300540307e101511070b5250710901022802c1440403c8012040b05042030740106a2011a03050800035000181c0f840703020b90003500420f00380010304051084c42d98149a00403a014004c0400c10140c0d50401c200703111300c4500c20180742d4040b0381c0e905503071f031950041d81141015904600c00d40e61179080c05600d519040ea24000344064040340c280031444007006503031041d50031401c030400c82d08864844070b02801001208481f4001d01c0c0509080d407188154a000d02e499807400c0301a22803501c40b04162a00351000e079090b0034040f0801008451082d12b00b80c4200300303903010080400f503440710001611403000850822912 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 694448210 1250 694446960 694446983
    0x709060f200a0c03030221160308040201140f030a050702030c1203070c050601090f1d100504020f060309010903080601110705040e0106180912030b0f0d020f060a0e090601080c1c0603 80
    0x41c19400200c100f050700c03200c0341c40c0315820321104c481e20709823084069005904072440c00610100c0e0140b400594840d0041c1444400d02504c805502015480001680c51150003c008d0002d202c080c1c1c0701e002d40c0811240025481d01e801000f00300e03035840516229400c08540080040d202d94880e25030800041c2d8003004403056075071181c03031440140858080c5144450701d003040c0e248118004002c41d9000828803405000722104070200312000d040700401c2640c1092259081900c030b41c503410003c600c10510311000090180341864000c1c0f551501400c49810010754a600c2449040f01040d0307207046034000c40f00041d615006c0440303a40034010350b0b481700b1450108004041000d854540010038a60300c140403103a0701c98680b50058046070540f610b01c0d42c01c0340c3c000310202c04a082038040c0542d468002001d4042c5a900340001900640c84156100001000303503c0904c19800d150404903005902400c0c40e0400d89000c66200d10300340681c10840e42030b9503c0100b058250358266001c0005540c010022040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 694449460 1250 694448210 694448213
    0x40f09050c03010c09060f0201021b03180406050604050603041109040f050607052b09022205060f01020a02011b080f0403110307030203030f131d0709060f200a0c03 72
    0x602010605856501515201414510301807140302e5074010340d43c03101c0d40142d0400c0000c6804200c058081410b6660811000300c421601c2617000704058001c00045584a003100c0c40d00390184803841c1c45d60702136401c1c0f45040c030442d501c180a98083d01c2041d10266102c1c2d40b9410805444403160000303e422000c06000d10082c0420426444440c40c0110202e0b9041d80301c1074011120392240241d40030071030914000f144a54203000c5070710020b40c0f0194101140c070744641c0e00041c0040c0c0d00c040601104180c51150b43c90303451040c1c014a44d0040084644144401442001075100c54403064008c0c1040b0003055290350407282c009480c0140c0e40c00042e02c0340c4502e442140f00c038113507000e40426a031142c0c61902c4a421440c0004d61007080e40d9014028504042007112040b9050300304a0b1803514900e248000858041243c4080414582c1c064440c1d217103a041040c0094400c85168204c42c0030004680705042c096904100003e6088503002c0d0b0312211071940b0080316090820340300c0d0003041045041030000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 694450710 1250 694449460 694449491
    0x120c030c0b0909070c020d0201140705061f1715091606020c011709121e070c061103120112030e030307030e0406060f0c060b04020405120102030a0f020c03030a1a04 72
    0x2d10064255604040c1ea10340c01000e940380040f00c503000354001402203844005503c11445031001e03004100c112800c0c50143c1da40d440c01c201080360210710a11050840507200c8107540c1008005040c410100560f000b0104801c0d80c941080d110030003d000303e45408110500720410000403a14482040c1d030495a49401c80292699150b00145001407030310255500c80074400c50304d40f8014013482c001018485007060700780486800540347d22240c0055010341011541c0000300070030501d4401c10b44950038a08280000e050000c2d1180d24000c59401800149122030000e00700d0fa066072051158191440c80c030303140440341c4441003214603030140008130342d082c101500542c0d03540034008210b0b000d2000c1500d4860403200141007803c0c650000b44490750b814041112580300d01018180580090314044d140c0001c1440359000c04000d000d9a0341c00001c0180c03001c06031007824201c3c0382c02a41949402039146943e44c0d00d010203840b02c0303400ca5440346a56030010006150b800c2c000030240050040e20f41d000700a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 694451960 1250 694450710 694450717
    0x504060c081b0909072007031a240301020c070e0f0a0b090114030309060409050405010b030f0a080714070305031c05010b1b07170709500421021204120c030c0b 70
    0x700d070080300701e414140242c811a4089c0c2d02c200200e40a0000b6500442624003003203007028000c40d0555401c000140a60704180b110101400c1084da20743c0301800d0080d0510807240c0000c061542c12880c0c13040c01e40d0a0382d5924007050441d81d203640010340c2c020300080004d0441c0304807002c49a00070300008001606440c160032040c8030704d01500003000103601c0f11040c03503196030b10000694051340041c103e0700002070964001e4004640649283c01d040e01d024540d0b28070b0702485810541e460392020074000c02141c0e00201c10301040200000a01481d40741107000c20711802880a28220700e07680e0b860f40020000104804070003802d04421440e96407420500791030300c03481c0c2e600501da060350a1040c180c1c418810740c142d210b481400020b4081c00150110b103d41c445121002c0d102e0215602d041e20b0420901c40703445820b01950040d101e0458202d0070200e488030220002038440d095410030210000503070501001e480449a0300103626490101515010001380c000381c00c000c03c01c4403104000b20303030640e108014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 694453210 1250 694451960 694451963
    0x140c03030a06061d01081f0f090923070e04111f0f090f1e030b09070e0106021504030e120304141804050d030209040b040504060c081b090907200703 65
    0x7504010b8007070309500800c41d0703043c001381408643c202d40481d803006c00e03040340e010030703c021421032080f119142c4a19552014070741e0321880c03400380c40d100e2038800d006c052296183c1118101c1e803140c120040a031011034031200240b06078240d0645410010b001c0c411200c0f803401c0d10241c018031400216210701c001400c010b910a040b0310016442030302d62070300d071401180282c041e41d25500403420998034005007412002503c6160b48210701580000100090003029100d0040c6101409440c4072030406010007290300e4140c2c000070031940141c0641d00c00200e10710030190001d8041c5440c000002c0710401180110680d0208203003a4400045c00049042a100345804000b008561060324503102011080142000b668040c1094000c5407010743c0310b6000380e000b04544c010150001c80c090302c80a000900f01c490446080d00c0181d101c0007038000c100d13800704032164001c9454050408a1a01c640c04043c07038010121030038021041c99010a5009020b0a8074119160120000045020034030004a89800c1c05200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 694454460 1250 694453210 694453217
    0x308220506180615090c130e0c0d050606121503010e03040b040e0703020a0504061206090e0c03011b270530030403020127030c29071101140c03030a0606 67
    0x411804801310129885142e00100304007120348904909025951124050702c15100326105c0000713100d00350041781c520a020f00c14280b134403521691108030580f08000c118910441041250300084807000b141c0301d8101d08020240901c0808480100e4010200322642c0d00d2588000303c1d00003452103090004000343d81e025905001c00c5d480b078641c01d405a014500c9004040342050100b480010302c61000d500c5a044e4001c0c011826030b50740d01120f01156031a2001c20603682103010035501c0b9040034080c00c4c49403102d410703200d0140c1424160050100d52910941c491402c0b0030320040e440020340358042030203040000c2c01e180807101240204507594a08040c04803421240400c1082e0307001e804816107003282c2d01a190000308002011001c903407030700105441c20400d81c16881c04804a19603408040140404c0c1001c2c5d800d00301a0f03000c20400200340c001041a100040081000154580103444244c05081c00d01b2001d26407480300c841c030740d4000c22034900d14920012042041022068201c441200c9450301c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 694455710 1250 694454460 694454473
    0x120b040f092006161704060f021c081305010f0203150102210712120c08010810050c090108040203030c1504150e0606060d06090e061b0403030822050618 67
    0x1020442d100c03519000268010000d00a804624202e46a207660451188540c406210004038036001e145e0015080f400008060011504032290100324982a22202c1107861010f1840040d0040605000401c00780030492515121401c10a0940001d06842650101592246412074100c48040702c00b0355010700610400d003d60071140d4000042c91740c8103410007849032425000d500c613a094034152010341c004220000582070703021420b44c402c0c085c4003001d07556504640d502d032084562500c220300d4800504949041c0601c03600d105140121031062000382411442541c8500001c0c0c21030280c240d00c03489500915503502d1481c0586503440388540d1150100a04942d0301103c810125240c01c178014183c2d61111001c1242c5141c41006071060070000b0101150380340d00c400080d001e440c0c0c502d1030f1021742d51048092142406020307440c1c5050001003140d40341804c0c40c50324000c00e144c00242c614900c44501858103202c0d0100c0080394445940c12000310758040c00c14560010340b012001d00c0c0e05e070680c092003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 694456960 1250 694455710 694455743
    0x1a16202b08010e0708070e18040c050604080a0611090603130b130b130c080d09080105070c02090f040c0308161a011d06060705070e190209010906120b040f09 69
    0x240c0708181650103490100005035100340b025204080003400040c1031054024042020781d982282d0050ba290781d800c641d02c520709003890603030707450081034000600c100740910040c4070b1b1b0500080d040b14401c0d00210080f803401a07014138018179100724054a608140c0010400ca5003030308103651007041507c6603034508400d540f60000f12a05680c0c41c64010041c0c51048081070761500c0c01c0d040416414001e007004008a581d0b648a5450400070210344004111804010005140f0a00c602580803031682004485841d450740041c4600720001c00780c0422036200b102140901a40b001c1c01d01c0907546c44110203548a031011010030380c074000c81e841158407240c8400d47d0300d103004400c40010f040301d51080907203583c07540c03910064801c000000c00c403941200d000d02100001c80c00404c0410700030841e1400e03145103030600b107c071004110072041c0100b80d0b03117004001e46030051742c1c030068840868440f85091108000ca0308044d40250a515150690040c104010070301c2d8140ea550059211a02c02c500c2c116059004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 694458210 1250 694456960 694456967
    0xf071407030c090b030f10060806090d0903170d060e010509070e0609060d02090307090507120207080f0a030f0c030b0f09040b0103120c0f08071a16202b 67
    0x1d000c014120030501408010075001d6810900c460b43e0000d050b545000d80440310b603031800c4c0603000000c14880d1600003c00114505100d01ea401034010406402e42c0940190041d080680e0f6110003442c9040440340c901403507450300d091b10400700c0c1000f03003441440c2c7e0320740e106141c4c82000e000c5c05204001040100d450540104161050f440f4040c2200d0700b411805410080580c0100030041c4880d81c0030040c46d452558203209100c00380c22140800541410455030041000f6021402c40401510403c41c05000c80d10400548080c40c2d0380c400d01d01c2d5a50750100782100a46031918800c07131218285000c060710181c25030488511003001340c03800d00c5218412010484441c006a50140c009003060006101143c460300d0240201d010b05d040208403d10030381e8500300340320754400041d01e40d00d6010683d9010456003400884804c0c102041540c0c0720305044000f1308200d003076404c203481802000000c2000562029030b4200511000300284c5644a0744900766090705801c0c88000c80c2044042280398001034007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 694459460 1250 694458210 694458223
    0xa021608060603100c0e09040b0a0b03030c0304030210200705010e0a0303080402090406020f0a05041a0403021804021f1107050919020c0304050406120302100c0507030c170f0714 78
    0xc0100200056000e010404000f000c8417070100003002081c211075480c1c0e031615260716000350300c200444446440c156101c4004c07070f048144058800d400401c0b01c0003202d1000402c0e2425a50104d42400088070000310603182e0b00030340d011800104d000107112401800002c40d40c01d04462003a01c904ca920b0b03140d00c2c20407002141c14013004010550400c080b801500701090b406a005100ea14010303e043d1b070084200036030740c201841845c00a200001c3c14004001c43c100c0080700707080580951401c050940d400100341020460108901d0400d140c0000c0a55840440751132010b00c01d00c001da00540ea40b81e40c000d06290b90b604000b01c941c0708a080024003410089591440fa41c85d10304280301552046100001a5110307c08402a620091101060300d0f03585101d01f0000708001c100300311141c007240c6006400d21540c01d80c0800c42520b000d40c8060195004001c40f8400355262030083c8230780d0f9061504116071072000c1d640c40180340e00032030007601001141e4020f02c006400341084104204040d50303456038810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 694460710 1250 694459460 694459471
    0x4050d0306080616050c03070206041707140603040204090f1514011a0913150b031549030c021e0a090c0e03100b0f0a0e0708090f030a02160806 63
    0x70340134881d5040301d8818800b4003015884001943c2ca820321039000216aa0040d400001248000060030040c0c80b0040094000410000080d03000d84180000020f40d203000082c07002c0c0c015501d82e2a000e0800060004400c041c0b5070140e9000f0f16070011203d000c00400c030a00c4100000e00c10300d80046281404610311001e00e1044041d43c0d46011042d505001010b09089481b018544e205e1801d060303580c8031914813802074101c6500d240d0b00c925200040f50040d80c0e000548034003943d502d9a401820043d18910310109020030102c845003195420510400c1e20084c0b4800a0f00a26250080342010341c440c1c00016a5402202c00c0312040780ea1845030f8031408404102581d03c41c201300b4080211103026041b000341c680c02410248400c08468000c641018141104007606a0f5555000d038100d1911102154900400790f0300c4100c41420481c0701c0d8018172000d8408000e20401c040003845117801000f00301004a240400d80b0744443c0300c64000707980d0361000c0344c520001c542c04080210b50003134005a000c0c07044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 694461960 1250 694460710 694460731
    0x923031b061504091104090c0b0309030307030c031404111210090b1806010e0c040e0a0b040606030603110402031003020607060c090603051e091c0e0a051c2904050d03060806 76
    0x305d0311108100c020640880c08032031342041e2040c00201c211003800550b10411039100916520f140c085002400c0710100b04071903060500c2d09041e407001d004c48181442e88168020309490300c420740d03000019489000e95194500912801071200c6520445801c003500003449845041c0040c0c072403803500c8451800c0040104240d40c840c000402030f14210f21f09031900f10b00e803629041e00d05900d8000349201444100d07a1082126101d0000c034060b170905100790300082c480f0389010000c40341595100c1e8643d90040300018412500807011820329045040b46000559004002a949401c24503006001d0020042c05101242d1580d80000e04940039001d0140318000e02c1c40f41ca44001400100818003a01c05001c03c002442a5540044800707080085072003003800300e803a07070794420440c0010001204010340010380a03c0b0704180344005100481c240d840d0720f5030301c0040307250303501180010b040603041c01c03c2d0200851385500b814001404000703e1098403180d020b6078107002094541500d641c1e00c2070242c1d0320b00c200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 694463210 1250 694461960 694461983
    0x5010e030a080901030b0d05150105010519031e0606170a05060a150e0a060905030714010206160c0f0822050108071b230601090923031b06150409 64
    0xd50710401807003840f0050400046400d440c20109800380421401200c02d90f02c01d0100c400201400021070f0b0040c02c09182091900d4402240081d01c00c2e8108903007c02c1c1600c0d02c0f0710a010390304240d424642410340c01e800300040d5035100401000e02010b0607070302e00c900c80243c0114045801324010144114800360440c10728034500821003445e586c5a159550030006184022001a640d41c05004001c00440d51034043c0f00d8140000c0504150641c4c0c41144041c205407443e074241d0341c01088003a444084403c00f00c04241d1800d0003034442c0d0b2480d5a001f805101e40307148040400199101903c5004401c0640b1a8111078424440800c986180070705800300d18980005124640708240c444000303190101c520301c6800050740e90580c2d400f0320419201103070402d41200b51001c07104000c11801407100000c140400c8041e501c41e841078040d60107024100e02e50000300b18100b82070070400c45160758581d510b450841c061b41340000c0d4841e0401e0712640c243ea072084540f00e80c11700d02402107091003504214070814 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 694464460 1250 694463210 694463213
    0x102040302090402220c050309010c0306030521120c1c090f080c01060b030c0d0c0207030c09021b0d031b05040501091206060b07060c02010c140d0507020c10120605010e030a 76
    0x4030040707008010a17030500d09001e1481c812020b0068010300102c0da11440d4a80c18014012401d5859806841e410140b0708038080001c02d40008440380c2c050300c2c9144e007501101c00c1c03640e50401446510800107400c2c042600f84842e2295441c01011001c10022121402c004e82d050b503102a1032141c10041c003240c2c11500100d011580f501c00410076440490000101107603a041700381d1194204440501d002000132401c00d054404502416038034510328800352051074115a55151010b21074003803c45002c0d4041028203080052f04080c140352401034040326200c0c204440010040c104880440c0440100d040c0d1202d6418094000d40e425560141c540c0d94005003803028204441141d084283c5010f6110000041c259800c64000c00f0954061800420341000c0030340040d003510a68100c00081090b08041c040e201401e080c1524111201e050300820582c032401412858075250701300c0541e008101a001d0107480746c2240383c8401054000009000039030351900150b8031030400309016a0540c0107226010f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 694465710 1250 694464460 694464469
    0x20309040506190807230a090509030d0914010e01021303140709020f041409010e0403080a141e06041107030c2901061d1f020a02061206120102040302090402 69
    0x40e8000005440c4400c0c0110509143e4080545903000c8540b03a00081e8060005c0c030250360641903005444012241402d00725408201107900d64032882100956030307404100e81070030900848141140f001b03024400e183c014241080c2040d2855140e0701c056107044003e074400101802651003030b861001062418030f1075600c0e199604160b2007000724480c0038544010403c0034052001d441c4100c5800c4083e503c3d2170510842010b0741111258052084a0020040000042c00e100b2558031070f5241c900700701c4a07210444050b025107645200d0050000a480422420800241d021060030050041003100c0c1e89640042c4012240e00c00805080100d04202c0c00340424000c07c10209144d10424036644c003051030104500307004503404a20310040100c42c0041100301d603c1703034500e88603141c0c007400d000e03000e01c88500084d2480582210303c2c5851841104a000250007482280f4090782c0150105599054103100c04d6100b1404980e40c900c01c0d4204507202c6503084051080d141035980c00b81840005031125004c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 694466960 1250 694465710 694465721
    0x50a051003020706020414031e070b09060702030d08220b0f09030c070303030207060e060601090e0c0904020c060103051504202b03120b060405061b0d0906080f0702030904 75
    0x1034203041d020080b010000360b1510080c00140001c046610141800008241c10300300c403084030f100400c0c98840d450700c091801148030b000f1031328044107071503880c4115004140360f030082d801701a5060140c2d5a5050b121600302084510940c03000903000300403c5030604903c02e54280e4103001d841381c203924000842c03104083c0c0220350424014030440c1e0501103038042803850010242c0084000940114808041046500400c1d055030034500240c94285040350000782030900d64442c112000803858085030010300306034100c940c0000e0280c410755941c00803181103176075060288800c44031032141000d014041411980040d000d01c0c0c0c03001410080c950b50700384804032151003040860b48913403000f40f00a0625140f03000700c20712480014544c8075800b003505016284c581da070f20100c0b0b9950300b015400307201541d8920886e000d0f180200c0d01c0e103495621641d900c01000c580d0350510303403017442002860ba581c1d81d0001c282c4001c8070040c0ea568484c0303036144504504041c01c00d40700a800f60b4030500005140b0310303068002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 694468210 1250 694466960 694466989
    0x50f0d1e02030316170405160605030112390f0806190e12071406060405090c060f0403020a0b03101d13150213180c09030b070306050409060c0f09050a05 67
    0x3582c00c040c5555a6101502007910210b1f0251f000051881e10000d03036185e004010325041c2007240c159072604003c0e504488040a0013400c40210b0050750500e03442c24038251400201c0300c0540308070354014a600425146142c065100d41554400c400035210000290551082c41d10384c56801042c1544041900501150080c48109010b50440c924800c01600003420626001390000c5514003040719985090901c00340c1928012414001006091140040c030b41513041c03002d459240c0c1d00c1c01039001c0c51301c0c0307402107800080d8014031079100040c0d9001040d000d540aa85141d086283c0f650f03a520880300d00200590441c082d0075a940300150719490b22403e98901c450140043e41e184c41c001c120150101d03404090030f00061401c3d104140814055074000440c42c1100380000c00402d01030250240c5500c0c2035101c01008400300c000042d0030580b29400c00001400040c0c814020740c00c581c0b41485c0035100b1280f81800140004012881803403080695604580003e049020300074146020f018060000d0030700d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 694469460 1250 694468210 694468217
    0xe03130b0c0f120d050f070807050a0219080405030f01050f0a0203130b07020d0906090806010e071b08250b0a02160c09050108060601081603090f050f0d1e02030316 72
    0x800c400e209050103100742c950303c0034032465942c22a662060040b00d030003500c0000303200922010405001e8100100541004450514580b10810b01c10300700d151400c0411a5a075201d00c1019102c10071010101030020750300b080b025208804002d80c3d2442c221b5074101e990900c82d89403400441c0508003507038000e6412000c041c2d40303100580040c1d240e00620100540ea10001680003c00060080b98000242000b030452450509211883c00801641da01018003414240c500c421011480705401426424404600081100801080b504101403d90090841a22040311006996940403040c01c900c41c943c6901080090041e19a40101c02c004c0d04085101407441c2aa5204013020076640308402005001c4c2c04c0e00454a9810001078600303240016242d04e05005a10301440340c03138010001403010500340e0f890001120101402e00105031310990301c000e00b680c0200011881a00e1011901146400030340c1c41f000031945d68034041f4182c07203500400000060b0801d1002c549116045646d001206490b0f1030f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 694470710 1250 694469460 694469473
    0x30324090b060f1c0515030c120705090103030528020316020118091a0301051030110a060e150f0415020618190f06090c08030901030e03130b0c 63
    0x243c030070555510070114034a07680522131880d42c2410160150f41d5010310500b804100462016010990f207061486c8100d119140800c0f052580c0740d4100f03d620010034004108030400d50303580c1006031072070703002e40c14840310700c50b84a614403600c080070203064000740c240c1c0e8005c600e405509040d104409079071410890412580e0300d5100003501c00c2c000c0c0746015159000c40000c15221410305d10b40302e8240001490301a0f4140410000c25840c1920040c08480384070280c0040b04c00c04a5101305041e411000e40c4c01d0b02d1112152003070030310121110242d030a24066480756042c68072880c00f40c40c450384c0002c02942c4861340c0140d00900036403e8014210544003800a142400d440b0710035200c1101d1355070381031001070707002204014202c1012910441002041e101501000c0341c07003000102194100c0802508d004640c4035010b08002c80fa0340040089078004801013141034849140c20f45075884410060b00107804c103000c2c4c2a12110110854400f50b00728583d060741189040d104d0346c070a0b0000342d41c5a04070300503034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 694471960 1250 694470710 694470727
    0x150e09060a0c1403101a04050414070917240a05090703050304091512050d17060f060c0f0d0806010207170c010305060a090504080304200904080c0f010612030324090b06 74
    0x36503458100f40d0281031b032030300c480c1002c09001c110f41035290f007001207212200500c0b01c82900140c810b8283e03810f01038000c80014010681c0d6160103007041130b6004605240c1a02c032000440702104601139407c400c7c080c425507d601e2103072903948416010241140c0c10801c003c00c00504150f01066090840243d201d5a1175500c00811842c000842170559041d0401c0c119003200071350040960203050b11200404016090540c04290301c00d4148034660b005410000d61850300e00400c10201055800410480328a81031f5028010a41d200903038140f809445540c0c800b26941c01ca46070144252108207000701130b86446a0011000b81c007001d8030081e00b041410305c0c042050b280700d0203010710881c090b650b02070f542c0c2064a031501c80108005105803138166880180c01c0540d98402a0f140c03c560020700c00764440307002c00903040c206041005505512f6103043c1303002603500c9032001c0880c0a14025201044980c5071941116030841444205c10403602802c10117000700c441d29800b80c1003d1401600003420800761 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 694473210 1250 694471960 694471979
    0x10e040b0f060d02120a031103130e0606041211030613081204020105090d1a070f0c062c0105093a05070c06051c06120f06150e09060a0c140310 63
    0xd00c95900466040b486a006c02d05130010024507501c3d100d10000d615207003154521580070000c5000d00c4d4059500135010400303035940e440a9401800501c01c20f0860b003455480c124401c40c2601a009000303005100000b6440d1421242c0e040281781c11182c064500f031139403000a0348950008104a06028052201c1c1d4180e494203003000220724032a0007101000c510890151540390300c010501010449441524044503921840c0658040e83c050004240c0061158840c1c1c00c41403100c65000604140200c44070001c40150003550058098105803007640440d10fa00b2126131040c46411080110285862000f000c0a441c180d807601c5042c0c40d149042c4001ca41d031740701ca4000140c2c000d0340002c2020807040400f241f41c0a100140c204c0e422820000d4600d09030307110351400020300c406815141c0b03101d460810b10032135420421040f144071100c418404d40b00c6002c00410007059074180a80e210301d5000811416262007805a0b40302031751641c240c01c00c901c5100314420341c0000c0030b0201705603040800042d034540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 694474460 1250 694473210 694473229
    0x203070e2713060b03120a0810080d0302090f0402030c0702060d0e0102070c24020d050a0903290f04030c0206030a0f05010f0501141806070311070b03040209010e040b0f060d02 77
    0xa5030485010b032251141007540135155000e400313610a403c41c888801025412400311000c2c0c0c0e4039070074080340c959074115034042960b1269100c116640940049148516499801441e4100e0304440040c207102041c410b0004901040303a418981440410005001d807800300058400c8007070708040440d0014102c00c4040c01d907006401c0c103c40f00c0e403403280c0c14000038444e10510b5107504900c0710021000064500004d540b2403440440c00148000044c524445900c6108804069900701407104c03a19089959941c0c40388415210300c2401caa60340740461089554020407078000e40c1c042c1d5400c0031403000c0c0e400300001c0340e002078641581141c2d90b1703103140102d46841c0545c5000304801070000e42e1192030300300090003c003500700011748101010400c248481010365000b130840e00c01500d40319282ca10034602600d0178000482d2005003803140d8140000c2c0070b21000c0080d8441c03403096a000c0a140d907a0000c0e0001e81c101620010000084e0b0000a00c00d250261245680220010801c00030705038940c010404904 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 694475710 1250 694474460 694474471
    0x91e07120f110603090a031107090e0f0d02030f0702010f2c0310020408060f04061e09051006030503030609040629031c0c1221140702010203070e27 65
    0x65201414090041d2800c0084060000f918060f01d50b103404c0c0340180d110604050020280300c0aa800851126010801a0040c180d408030130420f90700c4c0d0051103540c4009800242810340719201030000107038404012b940059141844860428846a00545103031403d50901420007100e840f42030340c807403150b0059602c034441500f1000304014914003418204032205506500301801040308010400e0000781d2154045d404010f460700c1d07502c89d442c0450140042c0d080003125060034103400708001c0781540c04044030030300c2042240c002c0401c0c02c0c080c10907039800e0720004e850f50b00280001452410305914403030381719205110004500300d82480802042803c4000d901c03a12402c0034000c1c1d81410100f11140c00740003481c8101c610940320a4000b81a6800884010420704d82070124401440c02909000203800020a0342215001d112403603400400254044007285d10082010901c000c0c0180308480c014070341c2d40d07a42c030f0704031609109026881f51010040c110484c050304603144201d11b20300100c0e000b030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 694476960 1250 694475710 694475723
    0x200607150b061312060c05090d03120905060f150a0e0c0c070b0a0e0f0a081e03040302090c0702010206070807050d020c07030b0a140a0c080f071707110d0206091e0712 73
    0x5801350800000b00c640c4200110140320b01000120f45e5581d443d0b5000f4000b943c94541041503440d000700480c050b1400100003400392103141e0510840c0400504807520a010108820641c0c51a030010811440c1d094802c3c162180b248201003562014202d00400c503201c0c031481254506039075030040044070f900c807160070700004140405c0c180f294580883d45a2400030121503552040307040c041810344420b413550f2070030b03589007220a40c0ea41782e5009006840c01143c008102d2062440c0c604403088644d405400c1c201d006000d50000507441038014010f0f94019640360f0303030341400c1c041003161010080d40142d83c010054491118008000b8200241440c0b0501003c50080343d880d4122464440100300544801c01007801e20070140c00c3d01c0c1e4810600c03a031110902c50340a8254681c80c0c401d448050a0b10032141c18241c0d40010420504d41003a4881e09580034202140c4160951080403600d400040c1c4031b40310541c2000d140c003001700c401350681e10040098101a2183c0365074480c4c0c649107a030440642201e14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 694478210 1250 694476960 694476989
    0x92001051b010b12010b0f0d1403030f0103031403042a03051b1005040e0601030b04020706050a09050714130905010b031905010f0212061011010207200607150b0613 72
    0x10381c10048980721041c00c0040003032020b4050180042e15141c817903104c807401004660a030750144032000e400003078051901c09c16a036590410302420650094240001c0e40411503d401500100140004a0384a540c0015032041840e8004104003036003000d0700d030f80c040380031000d56001c8089001400311803508064601240d41c103810301e1040c070004881c5100010244030081c0000c002000040a0390341d0b03c00802d04c0c00081d0000c1d61b10004000340210540075000c5407a000401c0741c0811a540101078050040044808056035000b11201901e10180401c1c1c0080004100d092012515004440b2984c414070000c14582c10000110746000141e25006407410030a80850080c48000c0c071448021070b1074000250302c0e10303102004440741058040c0045019181003d50304002d944550800f80d0721a00c85070003035560305075600f0450003005945420740b10359641040c0100b00780c68200103c8072601e40c800341c0c103007078041c1021442d80209088100c2a400c140d040010300900c01848c408540904106881b0004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 694479460 1250 694478210 694478231
    0x33f0c1005160903030207141f18050a1802030907080f0607080c03070e100215130b010b0901020a0b040f240b040b03070504020d02220602060a092001051b01 69
    0x400e00304071041c2c5400e212070300c83c00b4000b00b9408169034054034080c540f4442e9400703522001c034404401042541d406040341c919240000b541c8000100360402149524400850700c034010806d101359a0303c11140c056001e80800c0c94004626001f45074040b1551055800e031940c0c1d5820182004c003288000c2e11103402c0740c0304004540343c0160800341c0045c032002d1054114a80a10040d04544180c0f158603c140c241000500c841403081080b041c03200220700071044541010152200c0f12021528100d070800c2201b0b00100d07220003440300341c2d00d59990590062107601e4440d21265184030740a001921f0a001c03001041022500d00c04401c0440400e80080100012010800600f01d0b020720389114466410f044201c4003990380084c403d4140c51040f9070050b514002c082403400248a2190035040d405910380024410080080c1200c0072525980c090710b0a0b17907280c031107842c11180800001490200300c0c0941c1210754402541207601d2100c1814a40e143c05203000b003851700321001d41c003c04003680d1a01880035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 694480710 1250 694479460 694479481
    0x70c030c05100306080d050327100b0303091309021206090c0901150e01030203191b090806040f08070305040e1305010b060408120306041b0c02033f0c1005 68
    0x40310500386004c0090905142119840d9002c00f001a02080000300216003040b4a41c0c030130306042d2aa1002020008800426507a183c0001c44003182407176242c40f641012505011045803c0701c44011300881d011091920154020580300c0003c4c1d820045112034154521020488940959a0300c0e00401c503284a02c2d003080030543c2c0c140c014604400c54075882d000c9454004400d42d08041c0f0908002d81c0300c3d51840d5202884c5001100d888040c071381040500320303214101074110602444599030305035000d2789612a141d940e07001900d0050400702101001000704400c04090038242d0b201e0300c0d085151a40c0c0b0300b10b600054030143e03441c0009031410140d050030803109100344404070605540c4603041901d400c070003540f00d080c0102003050f40c000000000b1416615a80107904070035500400080d507182c2c0320001055014148401c074002d210b6100303100c405800040900305105c20003095510440b085501c2a418cd40c1d043d202c0290300a820300c50392040031028010b51040d241e03e10800509440e0082491 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 694481960 1250 694480710 694480729
    0x3030408030d1b080a11090a0f0e0a0e0303070c0c0506030f091b060a0e0301180305031f14010c050a021509010905100f230307030b03010e0d020709090206070c030c05 73
    0x4007015a00da403403280b4035812a60895100070056400651203070060340580d01b40c464175144e00c1e48540c03049004500c151a003002c20080c1c0300f205410048554032840803508941004d0540b42e156170007440003170200c1c0c0c401c80890300b09a10a07444001142e69030004507007150019901032a40c03401d680c007041440c80003044400d410781c1c0c004440901144400000c500c1904c1910602000c0010f5140c07d5032081d2001d410602010312490b040c40a00f0381c0908005159401c15925820413880400321981154107280c274000903203122043e0001550881c0005603110080d04008548034043d00d6104400360f940c01c1112042808070040181d82c59002d440010500c00355030700954810740103070f03c6002d1030301e902441406030401a1b0038002c060302001a0840e4000e13152070b4030190600d00003c100880f00358035400140307000398150002c1c482c1c1d011250b402c60720b902300c915100c0010790011404202e51005e640240100354005485e807403034050991610b25150074180c20545282c6405c2401700702c242040281d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 694483210 1250 694481960 694481981
    0x30b0103060605040b09150d020a090e010303021e010e060c1c0204240915020706030c08130b13020a090203041e08040b0319020705160b071e030e03030408030d 70
    0x4000703550500e18050524056030107802800c140208102246454080401800c40300c3e41c80c01e141c80303a00110407800613600c252061030020302801030005441e0100c600842c1a02d5040d0040e095801040c0d024224444401e801c03d14959254140c64006c0e03c41440078600420841040d65558401380101500c0300c00d81250110f0300d144100070800c800150301c140385e502500094050440894204c2d41200e40500680081c1200c00b6171114180b16240c0001d00041252066101440641084141901d20800c00c5420111501b0900d01c3d40000984078000709078003e51502040581410ba03801041c040422034014804072940002032000388804e40301240802c40c1d111503103240e01d0206a40baa4040d0155205034000e544000c004200790f0111484094100c10b2a180115190721850610b195185503200c10382078102005480862154800e804540c40d40790080c21528054060f0040d00c040d030203050070705074100507180c403454810755070900c0184000c0c04d00f10015906c840f000c2240000b113440c80c0b0003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 694484460 1250 694483210 694483217
    0x2010507051804201204060b0d020112150b161e170d02070213090c0837020301020a02070e0705120c16020a09090308060607020f06070c030605010b030106030b01 71
    0x864100d081451011012070041a200403418139204604800c60750840b03000281c00720700c08682c50105403030115590b841180140014409058000d0520540040c000b1010340040c03404020701c03040e01d00030740143d50001603102040904076603a22020001d500f00380c1c0c1000d6081208601c071800d01480a0030401c640e1740c01484001c0380307015a5036203400b04211007404507100c50301040e00d408415880c1d0550380b00b03c1c2c0141551071001d03250308003440249510320003110130500206010600d42e80020325000003ca026259002002c00c1c03111200c00e40c4103548001c2030101d403003500000140c0b0700307001502c20003541390020610a420b1603101c035200280202020100308042c04a103410800c0f1000184e08071840313010747e40d55011003121001c848215180040d400000900c000941c0250b0350b032010f00c4e1140280c3e51220140c0341c0b0350030811248581c10000c6d41c0019007510b04a468034103c401844070790300c01d40740f40185590329540e01043e51426404003110600c04401017291a070540900c4250110910307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 694485710 1250 694484460 694484467
    0x61205070e060603010e0a0e1903030c030b09130507120b060a08030f0a0302091f020d0207170705040e030706091208070203030f19020d09060c110d0f05070602090d0b070201050705 79
    0xc0481d03e0707800140300314104482440040380030f03070a81c0d0f80a10b105401a20039211424009a589588801c1c400300441c0001d00c1c0c0641e900c4510710030b00c01d104c00e1140052102955840f05030030040d41010880c829200c9000710b5400040c070455450340d103803c1910590300302c003003803030850104802520300d0341c02050b140d0810403071502c50940b10012517184000c98200107071100d040c0400319034400d8403130002e080c0c0301480d0304004043c280c0000c0c80390b0142816a08175107009464070b00e290003481c0381d1561440d00743d101003070030b000500e02030304220700003050a0700b12810700c209926004103a0f1394849080d120416040d2114030300303d0b40281c1d00ea1f484601400250b156003804c80a81c11076400042c00c2c144002c0c00c1810040f404030150301118041075800505001408250401c20010b000c4982c41801141380ca624041e20103101044005003030030140c86201010140220581d65035001c0700c1c04849141d803c01922020703070b03609800c0b220072074000d204030491842c00300c0003c0c0c00c42c2d1000e001031040c80000d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 694486960 1250 694485710 694485721
    0x50a0b04050f0705070f0c0314161e032d06060501090e0601080a09020310150e060d02060d0b0a350c100e13060611010b06030408040b1606061205070e 66
    0x150444176500c0d4840c038010325911440c20040b03d4100e4a400080428080c6581004100000160710724940905070018070b02e19581c15060011400595503144940c4015100700013141c0d0f013940085a00e8001290340c03950010550745840c504000403404c88542e99204014840c03940e00006500151160f00c0e03e00005027455000a000078400412034860742d03403a642d131581103450900048040d00041c0e002030011189000505600c24241c0c020100c4410046001904074034050b600080000d8016042d1440c1450800213100502440c9801c90b400c40d00c040d00c00074458001d0b800e14003159190065007a804503003101c1e50040a584100d0b126119445000e00030500c2c0c0c2d4004070040c54401a00307043d005885150302141030b0031599a05003031000c1c40c1010004000da003103040040c1c01d8046a0003042a000e200c0c003004903d0000780c5020300409028041444420003040080082203c150441074803850542e50780c400703070b40d0103802603041c840c1c00719000010081e040240700094500c42c969242d261504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 694488210 1250 694486960 694486967
    0x16020709060e16030b120706020606030a080a050c010608031206040c0305190218090a050f131e0305090d080d180b070302070219061e03020c06012304050a0b04050f07 73
    0x43e055000040503d0016160940a5444102c3e00d40d0064a0202103060345038196444400c54800c0d10054003030040003442628001c0b03040b41d0f100d54002042d5050080c01c280440d0340b0380210264812540d0703503000c0800d400d2010009007805070a00003403050f0303600c0e200b07043c0000c0d92880d07030302c400034541031a00380116421a010319800d41100341c040180c943c43d607038030b452083e0075018040c1070300142c2c030005010b400708058104a01c503860f4050303146013680310688030309041d203100480504a51806509180002c50740d4103c12074042c02882e000e030411482200007a81404021130071509000c0000c1c050f4642583e80c002d8041c5040040d010000d540c0f819126184440e2001341030604040e80051a00115540d403a1000079000140e50522100340d191480a04156851100206c4211054111400781f80c4030740221a01680200d0280205074a081260803088100c420341201011024010624030f40350351042e140b1401c02d40c2d0300402c00c82141001d01084400241c031000c0d214a00c1010400e03440c1c3c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 694489460 1250 694488210 694488239
    0xf110903100b01030209150a020c10050d11040302044d09120f0705040f062105100c18050d030f080c040b03040506060901092708121602070906 63
    0x1180c0c0070119030703114a6401240240f00d0310100e50b80c400b80e400750300c040d61400b80c03016002c512581c0d004c036095030a8400030000d001c0318040070100055010800d150341c2c0981c0303400117050101460703801401c041e1a41c1c0081c0690700c4000c00700790303a14603600080040602c120545c010103014480040c0e80c13200301713103501184007014250701c1a00e040d000410b0300654440001c0e5400c01b83c0054244d4040c075040c400000d466407801d10445104a0600102d00ca60260300e202d01c000315540004030b6010000d41c41007030a403040125000ba540d80c014001024201d40080c0103000900149580b1001d46807a09584824840101c1e0800380c02001e84180b03210010780c0003000c04d550300d001804e10706240d0b41c0e010f286000900c01c0f5000031403c01c5010050100300240003c0f024080e00c011620f402041e0380305c050080840e016141c0301c141c80c4044100e140c041e00b400f0036006900794040c041c172920b0704004403d9441e032a64240d0300c2e190386c0303040c0d50408250a039040c04103074041c002640c3d0600c007036464030000b8040d40703c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 694490710 1250 694489460 694489483
    0xc0a06050606161e050a03021c0e0f09090c100c02010801150f08100308040902031512060601050903030903060c0702090c19050a0c06060b0c070602031216020a0803010305010f110903 80
    0x11079602c1410b04859034130031480c0455500604980c0f0350341507460000c0d11a400104208004000000308146403405039940c070303000d40c4000d401c1d44045025a401c20610302006010800240100701c03400d010380d02c039501484070b00146901c3e6003040d05410307c00107220400503480b0b0901040110062040075502050300c103c001e01e80c0ca04842162144a180b1040c200941d2009144030f50000700018600c0c010340241d0304c10040c110042401c80440c0040c40105403d1000600d45a000380d00002c007691b010750058003407894003404590800c0c0003400440e141c5501900c2d19038442d0b0002c9841c0302103141980031103520124420303800e030905040c2c0e541018030482c1111a0000c2c04404aa00b603142c0317204810000c04a500244c06001007580c1c0c801c00303004c0350303c0202030b10001d01507003038086000750002040f2035150070043c04500c00c0d9a40c043d04800100b195517100b60841c0141254400424414806035000e180980f00001350781724148020005c8600c003249001c49000280b105400036a00800c00005c0c00e03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 694491960 1250 694490710 694490723
    0x40f110105040e0114090603011b030c0e0307090e0105090d08010b0d0f0c2c0a0e0603070e09060619060c02040e0c04020d02040305060f10090b0d080c0a0605060616 72
    0x49200200503901030050741c200c503aa40d03180300000100074060382c001c41c1c50440306445100080d104d84092500743e030f0514884029a0b60b40c078001e030510b40d11a03804103a6500da10300e024031840b101d100000382820038580c44680c0d81511981562100702c420300c14180c1118251004001c158040c600250440205107d201c880c0b80b80840c0c98804000740d50468000917411301d20420503d20f046a01500390804204020b1031401d030320030314503101000a80903c0030344000400c4d078000a850990700a440301c00091941c0c1c0c02d4001c08400250625151407103500528500c00a000c03945090001e00c50300304440d1070400c042080d0030340100000c58000c02364021154050700c02041a43d40707480a14985803000180540142c80040d81260150b03296001d0000d803840b0380b050342e240c0e45501030f16140d1007400703480007018024681820005210f083d408074904400140c80780c403c040441d11642000d07044401458116008443c07201c041003030901c1a076a001c1d90850722075061810003003003626484c45980000305031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 694493210 1250 694491960 694491983
    0x2310608100b03041b030318080d171e010308070614040b0109050711060907030309080102041511070e01030c2610020a03110f070311010e0c091306092306040f 70
    0x40c0716614491050180300e01c00c2c145e59640d520702d801004990b0840244058054900700810640710204944003008695030b0348089112545002615107070b0060580d080407484d200b208604d91501145141c001d50160721000c0d29103140c0d080a00076a00545210900300071507000b00800584000c03103450648801400010f0255100701c801e4410a00c410000c402902c00c01040041d9098002442416684207a8550041039036416040e800d07401607005048001340c03480b080501042c0718100d004502c4a4150850345504e07595081c049020b003003a04191030608001801b408050390019005828200000c0d00441d120311507103c4031345603000401c02090302900001e6000360030388290810240c405031084c0490352080800b8900c0d406520103841140414405074100040202c1031186145c24103000d4042d01e0000f0202040200604c4020002241d501c001050030020440700c1c070800410380d1040005110034045841c2203801c0781003607401d072405640182c0030080010252908100c20940c0458103903003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 694494460 1250 694493210 694493213
    0x100302130c0c05010f0209030d051201060e130e0120071223040e09061b07020105030a0e010905010c180317030c270f0a0e07080a02310608100b0304 65
    0x10b1480000c034002d800da40c00c00303240f81c1c0508259801000385080c12000c451455814400540e400d0040341e100f5144032001c42d00401c0518000c203c0c0d030315082030061450120015201c0d0810843d6400c1060840e02c1c0e40d00d0000b0500d407000c00740c400c1180746e003c1407401d00b0048550f540d04005941590740364100401c1c0e03000c02518403106101818071a410b11491510740d510b03030f002c0301840312040b2185ca1503442340c200801c4406200d0039840308640804803480340b40c11016001582c0541c0082d014240c0e8680d01c0407407400940007841040d400d2441280041120188201c2c01060b5021111100b20103403a071510420000e1324032480e00c0309031911001300326100e40d600c0c146a243c5004403030403c4045209825650b40c241c1c02c0c00d0141e00000004ca0743e04094442000920101e1030a5000d03000d01c110070f002c049500180525202d40d03006007111005450f01d080c00007025005840c1c3e0307011041c050f8010740148070500740702c07400c44060062481c00c04030341e10700a208942d801d65980700d6581d0f1214000046070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 694495710 1250 694494460 694494467
    0x20a0f181b031d0f0a33150504050c0a090e060a06030e0a0506190e010b0108060405060d170d1415121011090315070905120307060c030c08100302130c 66
    0x10b000d8000d04207071454902e099510039203c01244604840300203900c4042c03058510046d0030400c080721080021031401103800c50100c024a80d145442c681040f0405000515a1703460040622032100303182919140c92050401414155481d003081d0b039080011802c11403144c803206d8406044404914001c02c80d18000d000880c14100441c90191090144504029038083e543c205c2440d0019480b04c00c01070a00c0c00740e43e142c00c0701c807074559060000d072481d004113204d80740c6500100d4220500a0105924140c950b0301c50b2400603801003d02203000000c1400e074904c02d024898101d0800b171000c0381204d07030300d084004401c400c59070106145c410034500741c27600c10120007003010104140404138104811081d42c01c030408203820101880d80702e440b6504800900d80c4100c0322890096482d502d40c890801e06090402000c0902101e50039003503c01400307840c0110b200c50048034404985a02c00044003181d00703000800c2d40304003c007003603025071110718100016290403c1400c607400740e8000c0002c00b00b4070440e085 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 694496960 1250 694495710 694495751
    0x9030201020c0f1201020c2103072c03060a05070e0d0804290301090b1e1807020c031207060b0108040818040207150b040b01090807170307020a0f181b03 67
    0x85241d58404180e0380250800080e9010440d10740c0707210609441303103445030048c1c0751000300d0b40440080e10410614001c001c1030b51500e80c99080f480c42c07006c0600d010301d010900d4800100e440483c12915242401004c80d004016070a03655010790380d90341d01c0307419074070b94180ca8812442125100011203038070003030310741502c020941c0f545441d000c0281d407543d4a0340207074045c0c48041c038518850003000302504025015100071100020001c6e2000c008030200500e60300c1c0b44800104144154000c0c480300a2843d40c040c07000440c2810a880c41d00d840d14110704100c01260480c03130a29062040800501000c112081c2c140d800ca400325107000f0000301e003c440810080d0240d008011700b4011540342405c1d0a0003290070844030400f06407010040b900c0c0c040c0c011151648076200e210602c0e0000103081c400040901410792420310780c0000c591602e82d081d40840c500c0100d5900c03009103e020300382c0074042d000076164598103030400c20702c0070b00a00da41e00400c107110400801e13008041c99503038800c2d111364505075040d2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 694498210 1250 694496960 694496989
    0x170402010c0c080708010510060e010f0e150301080c030303130f0317070201021c0c1215050d0b190b01050301050906011106010b0c061e13080c0102040b120709030201020c0f 76
    0x10300b01036500c0c4682d55445a860040021550034035000490b403490600b521021a010395661420485208006594007c1100550003c06c01407102d150b600b334a07201491414402d9403a901c0b83e5070f6140c00480c40c280620410b120384207800c10814482a0084103214003100c9800c80d1080c0010303400343c60142c450362a400603800f00e2001641c20000c075a038041d400b418142600203021151040c094000c5402c4030940d4401e04040b13486540d0031144504543d00100c1d103001e1004846010381d40f15400600c55070642c600898526642604003c40c0980c410390808a040481c141880264483c000217065400305000e028010000c0f48000342031030380f02d0004c10398100900f000342c880658413200d00c4035082c2c0c46070703010425900c0341c80041000f4842c40b124070283c642000480400949804460f440240900784056a00e08400d00480507000c0003840240003c142d29105a83d44031407001c000540320000070300740c0044c032109000402c0940d03000305a4501c03800f030450780e2104103504440020504601c0c0d490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 694499460 1250 694498210 694498223
    0x2060c0304090609020d0e06040b070c151508160e130501290109060504050a03060222180b09040c0306050603160306061707061d0402090927070303170402010c 70
    0x80024031304925801040319103221101441405400c0500c0f0f981d429050f18010310b013120100009065610820801548030b100c4c10404242c852a003c640b8203940c00060b00007a140220b060421065804200004821645040408002d40380814182508100500683c902803400e0401f604112003940301c4010340240382851201d00c458000b81d42c10b0201c1025000e030104816420100e1880e00603020340b401c9440041461050380e040d0b5990034040d40009500f04c02030342d0300c19495800118942041005032402c070f03088400e01140d0191800c16641c070251090b006003480c00c1440003041e00d592000090341d030060703404105500c442c00407034a071141d1112140f040480c032140100c20401e264028408403008029078030800603c0034283d645803001d900c140c9012580d0700003c1c0c103104880002e00000184000c10041c24280e03800003046002008a60142000e0a4101083c00782c0da43d03200c0364580e032248030700200001421954003502c400501c05c14400058049030001c1d08680c8146481c4000aa2094 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 694500710 1250 694499460 694499471
    0xf06200a0f020a0b1204020d03030e060115090905040f1b17030d0606141905040b040305160801060b0f03040c0302030a030c050d0813030e04091b090b10020303010302060c030409 78
    0x182500c40d12481101248203e5181c4000501030101c481611201c14250101201c1c54580d42c2c20440e004211400031030074141c6031aa0804008000d1000d1802400c880c2c810010440030b1480050281c0c01c1604404000d6207840c0a0202050360550b160704030a501a4072086440140c20004c010094554051840510125080d034158000071001d400c08100001c818801d064503500240c03a04100000d10341c8403808144448900300c80303d078140c502c40105900f0010301d82520b605840c02c0580c4950810313075442e0b2203400302c148824a80d8181d603009103141c0e4020821b05041407001030f1540302c3d41072401c6080801002103010b001c603041c0840011a07004003140c1100b001850080c02c50f180c1001d0646440c0035120070040b81502a0140381e20422100d2042c0c0f0450103035540558a1010b59280603400503503980d000e00024440401442d110074890400075411844c003500c42c020b403108641150b004135a035040300c512054000003a0381c15241d04031001600c43d25131175900c1d4a540601d900200b081424403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 694501960 1250 694500710 694500713
    0x70509010f0801141302060703050702030d110f0619020d0b030f0a031412010b03090f1509121207080912070803040c170a0b0603010608160501020f070f06200a 70
    0x5032025040700d212100034002c03840203480080f420344c4200c4801d03004044001e8548018a8503070002c10b0300c00d01c40c4c11329900b0700d075598020a151030748a45c5a500414501c1e900103d80b0b45042040c861109042c1e0010031191034100f011080c0c0d4050390590744030302c0c0d4002c1451401c0501c0c6401402046d5006822100b901141e1460f05039a0545102d00340d010504c0621502c00c4980e41e40208d40545e101440c06c25a50703464220004c0084d032004040c50800c2c00ba6462913030003000207002c0508543e1110001d40003a08010200d541004458030440640c1d400070402c4181451303603140e9181d4004842d051071241941c4640e01682445103442950354003507000100d410400680d000614000e0340a000950b0481c0d07290301103001c2c0c4140400203000c00c0c0d48034000020024080003581e6511590140001c02d0700707940d41031060701e80350030000440d00315000030f4401c2c003855034100401c0c0c1030100c18000403c0030710318200740e1941519186c05208100482101c8004880c5920014080d00300300c0c080403070786041e805 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 694503210 1250 694501960 694501979
    0xa020c010810031e120203030c07020f150d05040c060f0c060b030703050607090810020403051f0204090603060f0b0118030305070309031218140102120c0c030304060c0308061e040e07050901 83
    0x100604036640c0c0d0b021882d107170fa003502c000207807403003a800d51213030070718240a40c0c0030068403006541031554080c02103170400c0c45d0250380d1800350905e800c6412010601d41858078010b0303480c1040381c22000030010401d01e030400c1e00d41e02500b01075002e40c00810001d4103140b4040880c1c10700c0190b81000d002c41c8910002c0c008210360123081642110580d2003a2500701c0c001e180c4000691140d44000b502d1a80000b10f0300a00640d414500740300c0902c41000185490390354007045095500562007900d506580e00400710b54040c09008132031401d4000d01c0c0042d29400d446401134a0b58a141c00f002c0c00700100824054100340c014207015000e10782100c40b0b0303004024410f000628903100e03642c0c81c0c1a00141044001400038985164640980301600504038202c0c40408101d80e580011009605600c00c4622184594905000500143c00b640ea00c8549540c1981006813410001030007450292201020280260003406114031858100312030201d0b01d440a0300c5018a00110f58103c158003101010002800b030b2003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 694504460 1250 694503210 694503263
    0x40b0703021b0319060b0d060c090518090d0c05010209091503100e07150e060304030215100f03061d060114010f180605070c0e1f05060a020c01081003 66
    0x590816460940d01031800e00d41c88401c44203025650400b04c0c80030a001510a40116500b01400b134904400006c59844501c241e6890509280201d070200c03c0600c11402c261103400b00d0b20401c450643c2d0306007071009025644607108099070f0100300360301d207061003048070a404032129000c0050038040716040ca1502e540b40080324000b11031191041e2420260000620302640104440643c094031980d8600301980c03003001c0c8208030100c1045030b031001c1a4071954445010b076000c1c0703009034020203000b01112000c14803000040d00000c45000703c19001c01c40340081518020540740c0c00b43c400700b442004810840c0e183c003c2100071400714020303c8004200310105000b98039101c2001d0340c61152864200b4001e4506d00ca10806901150351018018010706000c0d000800705140304000d50042240d5a03411114030401c01e4070303160103c0c03504201e010440918600300300c0240908452607498404ea980000c0d590391542c1d088141070010500003e081c2c03082704881e560046412040405180504c1001c0d80e211a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 694505710 1250 694504460 694504483
    0x11d0f010c0c03390303030533090c0418090807150c1e090510051b063c0411040906021209060105010206010627090f0f111b03040b070302 61
    0x13203001105000b406114071080d92a880480b180341c10b02c0781107032000c8002d04030090400d02440d46060996807502c40304d20040b540a1002d10002082050340410840d0340c88001d880b418030030304c0c02d001c02c8c0001441c0c1d10a03800441c0c00000d00181c0c65060f4a8407031490701070389401070140384049952414040160300376060701c03e41c2e40d441140c0200d4078058801d030655a842c210340081c0f4040c10901013030804944070000c1c01c0c51400c0c0035080c17801c000c0179a5048041c0d2070002c96542c0041050003418842c504088402d500c003107200280b05104185100c940066000780c103070f10440038401140900c051243c000c504558064014440420316051102c069842200903a00400d0f8030303030021700072a1000c6006410303114160302030b18159291003030445845501c0c801c92004058284580101070ba2050ba0003801800714100109201c50f5540003281220100c0340b1a00c0301c0ca04000b205004505604100c0300c3c20300c3e284100a811000c00e4024900e14000e5403c03c1005110014055086c103800086004010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 694506960 1250 694505710 694505753
    0x609010606050301180504080c0304080a1a070e0d151b120b010903021306120c05031e0303010b0a12060308091504050d030f110601091505011d0f010c0c03 68
    0x2169191811901c0380700905c150140715090b2603c0d80381d520311640182c1c1d0054091801c10342001441d892403800e41d0312036031003130200c0e52240d20014200210100c50a1342c0f80e6a0301d013a545180b601c0140608032103051004148940244640102009802c10f6402000910b82e101001074240c41c0c580d06d040100911078840115004c107040840040c03c1d402100002401a543c00c81c0f407501c1c41c3e092003081002480205c0039542c8628000c10328400d0403000350f9140340169004000c4601d0314043c5401c10150410040c2c0300b01c80b1081d201000f00000007100d0445481415103940d4502030304089404000d1070100d0042281000800402c1c4020f5038042d002c0c0c11411154100f12180203594016188100d204841c0c02501005110380070030f0041c01c030045a5140e9007032903044054402c5906050020036000811895520052800c07969180c03254040901400c0c20550110318920350400400c00c5042d05183c81242069500640340c0d105840107400107a2141c0641c88050b200c0c41d01c015100c212107402400d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 694508210 1250 694506960 694506971
    0x11202130c0905031e0c0103020f040909050d08061008150301061a070215030714030c09060a0f02060a0b09010b071106030108010207120503070804150e03070308060a141008190e060901 81
    0x80f03154001700e0b00d103400a050000c010b080c410200540c06504091400e00810f00d05005c0080c2c01a194001d281b0381714801c001500400c90103071006000000701800140c002c1c030813000101c0c0a50741010f1380700c0e0004c2c40040122031240207400003d014009035040f2894104d42040c4421180140c54041e000181c421104010300c000c101c54900f660b80001c8501d80000b4105d00342ea40c0d4591142402103070400711588200d441e0010801c003061003540070908000004141074614244145c0c140f140d190044864113091100b030020b00300040f050001030050342c1440000140c604200700181c0f00d410314040000e1721a0b07841e981d407290392900039042508240c82462640c02c0b148143c6109034110381c440c0c00144c44103041ea4903180c80300c005009000e06035004250341c40c0c80d0808150130420141c2101d074401da0b40c4055614041080c0310720b440e002d601038260004011030342c070319a640c1ea0301020700f1141c2d9494070401c0c556502140d007000300c1601ea0030000e2540b905c40994111a070204d5081e100d80c8009009100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 694509460 1250 694508210 694508233
    0x9210d0203120109020f04030618020a0b03070e0f04020c010c020d0906050328111309110712081510050a0e010c0312022a03030412080f011202130c090503 68
    0x2100e104200d0384004802c0c40c5001480040221390240c08129000401d0b103007419140d5803100e044030840508007501121070300c0c3e01011480d101c0400030103402c0000095007103040085001d00041448a0500d1045074030380860411512190305882c1d05090300b6000b0300829102c01c0f006502d620507040f034003000820541c0d003c94107900500032207015544103095800394072554141c104d098545011112000b41e121054140041d041a0241001404d03400d05485030303a261080090440320414581d542c2401d051044c6000320340000c614198056190405107055507039030f55102017500111404990090302c0410300248981d028004e0300f658507440e100c2c12003584a050055483d0610b0600080000b03201e100c0c04502000d158024040102400780d00780d40311260300f42032090101c4410814111036002008002c2407100c0420011001c5c000c81c10000300e28100300581c003034001c00500610411001d442000d00c11901c0740c400743c860480c805102003080c41806480107020450310705c2100c2c441d10440c13030b80c580b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 694510710 1250 694509460 694509463
    0x40323010606090b0307023d0e0c0609031f0c03050105090402091b1e0a02010b0a030c031b0504020d09020f060f04090b0f03030406020a030801060302190305040809210d02 75
    0x1025241d45494036002c2d40d00c0e100c4c40310203e03071006003000c08501890301c101c8140c444071610881e21010000c0100c03034901498450907448043c0c6208945214100745030300401e060003068100f452001507a800ba40c481c4041c0c04603207000b11888035100b86400c0c0c0d0004600581469010307450480e01c075501072100c0d03683c3d002044032814003908c019600c4030140022810a2403810105000c181c12100c0c05410180b038403240c240e0902007240c4690b0f441d00b00141074080ba40e030a10400380030701000ca40810101d41552101814400c0502004019080e00d032240008210300c094654005d00703006006541e00c014420185001d000d6100c0c0480c00340c450928100d01074030305403042c3c41c01034031044c3c25a810035103420000405020f40301e01858001c510f82c2000c001c6620203000500142000340c004201114041c9801000071a05a02040c10544144804100602032007058200700c41a132401041503100c40c2440001441165400d5500004d04140f480685220f83c0b02c4590307920540b010754117034011680c01a03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 694511960 1250 694510710 694510721
    0xe011a04080d120f06030308090106091107060b0301020706020a1e0806010c060f11130f050f061611040e1e12070f0f12030506040b0d03080c0a03020f04032301 70
    0x1807150040e0500040883c4034180402c0e18419601c03000c2108004441c50750111001038105400103180d40007003125152090280f90000c1c13200040800082c14a00200c2d031150240b500e0041c14280c40e0028401d1580d006d4042e04c5903150440400c568a401c40000a41f055080c0003c049204081180b000d030f00500425625215000607160b51031940555520000205070050359800910b40d42c00300320795102c0001c006000d110484109104138207040c264020702007160f590000d882070781c2c0252404843e0302c400d0180c44450609007155070606200e4502070454003819009950058907005c0c004407848000540c03002602907118459440305074100c030f669241c0321401a440700c054010010034002514084062030541d0141c0002c003040a03da41c3e810780d5108501a04500080e290018031005181603c107400581c03d0458210011202c16940a0900d05004200152900b80481c1064281c4d009404450300d480e810b8020300c7c0e9a13600c1c2c0c6020003040e040941c006a0309107101000c142d5071941440384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 694513210 1250 694511960 694511969
    0x131a0702040c0807080c0708070b0703090c08120d05090f010c030c0f0e06070f02060d09060b0103050708060a260a080309060609040809090402012a02031c2a0b010e011a04 75
    0x7241d805d5038400080d10010f86c0021350485580c0350821518001c280c40c0b00d00380c1e01070b020540d00410031349018101001210ec494210841d41d4020701d188100d4208108101d400d620700f6060042060390303d0705840c5080940c2c0725401945c5500b003107000034102e641a8480c0d00c41505945840c0e20000c420324089420070070005100d038000c40304211600100c4e805030103c0034050301c010046442c124a120392407040e510110300c2120b040351200480c00541d030701805210f9000489190801e018504000003c0600003641b0400c02d401c0040a04e40100a440464600700304984208480781d40d1024038000e1200c1e88115511400c1d4000c91000c1491407a180c81003a0080380c0016110741040c031007100300802c2d0301c40580200c3c144811030030f81c5c07910302600901c0001c2054000c4640c80c885007090052500701030780325030200c42f16400d400d11009083c0d042160540281480e401300b49850303140404004003a241d0720700151003070012000004a10849480e0241641c0c01c06400c0c7e0300710500d66003044a140603e000c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 694514460 1250 694513210 694513217
    0x1a01060216180204180e010b04090305030a0c20032701020a11010e0a03060207060b06090a0909080c15010626040605040201170c0408161505131a0702040c0807 70
    0x4000c90319042034150b950081e100001403400340d030303180e0200c1090408040d8101107078a90144002c986000c0c0b107840090002a5070034080107080c0d5078018841d1000802140c5160340d54050f0900142c418681d44038030080c10150101151000d000180d07403038000b21186001088403680b035003001020400d69400e02d10060700102a03000050b43d8840f0007001105100e03040025260701d40e072150b900c1100602c000c5004440050380d41c05242045400c0c0c40c00c855025026203420001d0144c1c80d03c3e2400140120380050074002920703180c6241c004010f201e04083c400329445000256a051038002240c00e04072080784c0c40c0c1c486014101304c04004400c0ea0190306034904d001c00000580810442e40045521501c14500710b009500718200403c13446009071802d81d1080404501400070080c1004540140c011507801901401e10f040240c0d4060603005907401c041040100c3c88122403008074050300064407032040d03551034450340e42a550481c0e400601090344034074103240020740d4450043e01c08500540203680c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 694515710 1250 694514460 694514503
    0xe0316030302211c0b0102010c0206040804050d050a0b0f010e090a02030703141006031103100b06040510020f0a0614060d03020c0402090a0803040b0406180b091c02030a1a010602 78
    0x14860707001c19a000310810003074071040000d4004044c45084031445000c0c803000000720300b0040b400080c21282c1c000d04403429035004c81d0a120110707541c0c13016107040321401c84584e50604003d11307145050800900008000d100350070140000c0f443d50100f400e0584400300c043c03e04a90f592075800f07660340b40c0440003a40582203900c00380085042001a400c03080c45c18001ca50317035a119401c016088510b55481030798000ba1102e00317030710306280038441101601c400840030b002d60200b0700d0006007640308512400748111228046040c10074004d00c4005022030480050b1040302d6405e092450160815107903510034800f851002540a2400384560790090b0742580c01440007c03400c1c03003404000e500c0092500e50202100d200019100d10801c01840036020b40c00003551980d291400142140441e04c58081c014030707060200340450f01d62070040c0c8035462030031603140030003800d1102c0540740d410168001039014080e80810342c0500049201484621503480c200001310380e6140022078039513414001c204904200ca1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 694516960 1250 694515710 694515733
    0x110d090c0314062e050909160504230702010b060c1b06180103050405120a0e040c05070206180a352103191d15011a03250e0316030302 59
    0x45031101034480480c202e1340c00080c1c90f140000c21110088444806607800310714080e2610109203200802850306513410300c0f440508000b0075036286098000001c0c181c4c5600300040701d040c030035000b8840f030100c0602001c2d0350b044c1030049161240500301100d80c0d09201007000a103903040100c210b941a0302c1c408a4285020310350740044000d41000350041d5102d104400c1003800114201c40140128142a10b5440d00050000300340001e40758156010030a000701400380101503101d1200b201c010004084034842052948000521040144c1e0000713030402e11112428024488280e01e170b4422461540c00500611140342da0140e40d510080113003070903403019005018150721055004c0c581000c18505200344e14114031038007000b29000105001c01d1070000c00c0c1301180181003808401001c0500030070024503503050816404c010411040309032000c0b840080058030894508100700c94001007407000c0e94400c1d030308c40303c01031081e8000c80c5028424041c2400e410001e52035240e5080449505401519404408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 694518210 1250 694516960 694517011
    0x219020a140d050d050904051302032e0903080103020f0d05030f070809030114070f0201020a0806010509030c031b01030e030c0c0f18070f090801020a0909110d090c031406 75
    0xc0d40c0d441c0d0002201800b00d80050410b102e0820b4840f1103640310754882c800306041000340c07007020b41000c0c1c000c07251890380000350310041580c416402da212f90300c9442c94001c480b507100c0703003281100603d002483c02c1a01002c2581c0300031541d0403680210b50402485e41c0e013100f00002e1003000d220081c165482003246e06400c48511001c0d01c0030602030040c05041030381a80220f0300392500c841d5008400c2440c07801304642d41d5008110510100224402141000c0681401a00e0014040c2070103061140120b940541c030b07501040107240d0340c4005025a003c54400881001d126400204000c0c04a410006009103c010010981c2c520014410041c200c8420050500c40d02b171038806801500501c0c181c507030504010203601180d0144035140d45001d041010310f40020403e102e6904043d0b8141d00401058a820b070340031400d2000d6a2801e10000b42c6030340c2d01c01d2000580d2040103410b122040c10241c482d818010b40072020300460340581c01c25040c114400d0307641034075850100d038500d04080a481614800700071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 694519460 1250 694518210 694518239
    0x19090c0203090a0315110a020309040b060403060f06060320040905040c0b0c07180603020d0b06010302130e100905010807030605091905030310060801050d0201050309030d06060f0219020a 82
    0x900d0059a16201c161030100302c1c40009500b065810b01d0500001c8070303180050744030b000321010081c1c0d042030070301c0190307000251248034540103580b14503141e09032001980c2d40d401c00c0b24021544108104950b550b500c0215015101c54854100480e2400b1b08406400718103407140e020302103603085180c0c07030503040180d03500040002074004d564481c54410301060001c0958014146141904014000145414030580c0031015600d111501241810340c03c0005803074180402e01c01e154065040286d6550b1400101c0c0207000b0b030018001d24801424000955480031130050b03000e000d002084070480c0e5190030082c41954001e20502d116a44005030070000b10b101507020940181c0203109a618120902d85000c001c0212a0005e407040d8100000384408155001c10100c01010346003043c07251585440001024914179000190500c04008001440c184060045481e1944d403c18100109522500c0041482c414206180d02601c200090301c2d0b60081484080141554002c0803101101e0800d280c83c107180300d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 694520710 1250 694519460 694519481
    0x6070203120c1b0a0b150609060d2c0f01140c0c120a08180d0e010509060405040c0f0f18060e0301021306120b09160f020f0708010c0e1909 61
    0x41403100700182000d41c5035507101d0341800300044c10f1a1140d401d104641e0070003c0c3c80e40d0802100f0607004401c540f0f9a03002d86951080484215458a41c0c440c82035002e814140700d0347c4581c5e01c41c3e01200704809110189800c240c00a0740444014035002140c15007203032105007110105421910000321600e4040c80113020710aa4201641d000c50344100c1006040c1d000040f03044041101c800810142c3c00003064864109440000200325089003210013416407056140340c039042040c002070200d9140c842104550041c04040c1c0104004a82c100c0000c01602c40c156000c4000303000c00315800503151040f81c18031120901044845400b5160650903184141845441501075400348840051182c1068655008018a031900749080ca54070307031404216440c00d140244980ca0201c184096400c81d40c030803201003511404c2041c4c1104ca000001e91504d0f00841c0380c00320341c0c4100792000c511294190030511100c980c80e04d56449010036481044024102941d13a5400d0140c2041d042100480c00d400080404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 694521960 1250 694520710 694520731
    0x306011a0d110d051302013e0607110a0b13020d05190309051002070b07140d021b010311160804050616020f03010c141e27030607020312 60
    0x2581c002601070a903018409201c00144020a250320f0400c11405007560080507096114035020a40d40041e0419681d903100301030410484000d0441103500003120250038100d1301c40d401081c0703000350a00340da13050708035142000190351308034050901c030700015050b04050344100c5149155030b0300d0100c25010320b2940d00c1070f0380c01206c504850012400a00040404086000c03294081109904021745403c01681c000783c0030f0b660456807500306507808280c0c1b07030330344001612090395011141041d43e503014800d800c5030003034080c1020000d00150001680007180300102c1140c403420280c900150211b45546071041c2c51310904200c00910320041c0b450304080c080c40341c80000d040030b8903000840c20070741200c003099884c168008030740e005600d041070040c03040080032002480301152103540188170b10b4001900b60040c3c28085240400d140d484000da40c03001c004008080d0b110314007030201c0002c021101a40090386001100c60110604012039014494841900110302d481c000c00081401c3d002c0003840c85002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 694523210 1250 694521960 694521967
    0x9100504030509091303180f091a04240b0a08060103020a0c0b07021e0708190c03020612010e06030a20010306030b1015081b0c3f090306011a 62
    0x80380e03a94041e00380102542641044000c410b0304e00a4080505211081c0d61061f82d04800c00402c200741c1ca0580a07200410004550b092441c100910322224140380705a02ca810250701c44203900780042e6810441a01400890308031740c0d00e401ca00e032184901000000040c0c42c0c2000212031754002d80007001003101301d241010444103182c80d003400c078000a80e46040181c0214809609805035543c24080034490b07030020b416030a00d0200160354600c400e1040d40340311203d1044200a02000b050070340019900503140360b40c2e171071401c1c00303070640c005c0c0074000d0707004000310000031610905000070040d403d60380c080c0c15611020042255011590380d0501005c1c10940c0301c1038040001039521035405e010b00454002070421505044d00700c0402444c0520500402c1468420010740403140050300e100000c0c0d001903a6590304013903d80d282040e41c03e42c4280091001003039400c5040e885051445215580d000c3e140d8900316550104600c00d2085080c401d07450707442100140034151181c411101036440450b0035518 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 694524460 1250 694523210 694523227
    0x30c0a0507050d08011d150d0302070902030a060f12023a08071101180e0414030307020c09060609150315220b010c0201051e040f08010f0c0503091005040305 69
    0x50003c011518400140080004001040110000c42c841030134200503410503180450314107100891080000d44101c01007000c023414140248148006000c0842080d9030700e2402284bca80501014401c0c1520b041040d880016004c1030410f603500700c10b600034841211300c49544007291014010088554031545250010b0340380340800c40411000c944188801c0c0d0701c809c00c5080510414a10a80c41c0341030064003200d800341d00c03900ca202c030019036400c0c1c2030100d00380c1c8450a00c102400c290300f40b1340b42244000130a001010303030000f07110804981c088694050300e590340e5041c41818003800013556040f958441e0401400e0100c140a994050010f003005082400720307200184040001d0302141c004640b607a0f032024114403950092101c804401c0c00c10110030881c5a000070407134417421901940c0c26403c440111b00400311f0354122030013010f42003c1f45400d5515052014001e00c0c0201c409001c0c1c03494006400d504501600540744038815000c0a0405407107481c0110000d0034000300218100705e01040100c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 694525710 1250 694524460 694524463
    0xb0a050604060206010306060f06050f300f070e03031602040b09010605070507080622020a050325050307062a1b1502120307030e03160602090108010609060203030c0a050705 76
    0xb026994000c2145500d0341c20000100c8005402030a210410110207001c201d400c078046440690400103030580e02e956400c01d060780c403194880b06000c070b00b203034000d07040160310f0108030940a120700280811003030700ca40100307540c00e42c5466043d80e056007092000124000b0b0101d01e00350000d001034004103008400e01e00064614409030030103c081034011502400f4010300b04415000b51034024001c0c050f44c10403240c519078402400840d8035070030f00c01d02010000c40d01c4119a5000514014007203402c4007101142190308048000703041101c000503042c0c0001c6510f070001e1141c0032035480c0d890391303811030160598410180e40040040c49042041d155072b60002840400b850807070030b16011041d0002c5090002d00406480342c80f106c0d800b190702c003800003c01ca500c00d030201c03900b20026040004400700140d00190541c041c8022300170040600c01904018811590010480780700d00b662103a046a80b241d6050310301540c28080c190050b8010701c00a00d81045620090200300414145903040c61155a50a03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 694526960 1250 694525710 694525717
    0x6020d0f20030301030507120b0a02070609050a0503211e1f090f0b010302031e060a091107060506090408180a230901050a030b0a020a1704050c090a05190b0a0506 71
    0x50035142e100000400520100b403140d68060002900122440c54160300c80d120b4618001c1d180300e010300d81c0095140100051039002000c2c5540c440d00b03645144030541000b0303450b50040c0188440c00f60b0302c00c000544e58810b030320545100e0a01c0c068400e0400c01d620b0090492818000c041c0141d403c900207441c00c4482c0902c0d400341c014400c1c1d807008599032010007150790076140400d0302c25050500600900200d21280407000d0401c20400d00c642c0c0f2590303144c100062041c05c00741d0000203514500000c0e64140c801c040018503690340244002d00480d11204140320181408035009040d0310414003450761074590036500700b109400001c6c1510311094450210402402c1c0807502d00140881111320001207042c08414a03004003001c03124411594130319120104400001028020003ea0000c0d140d42142e01546072219a020501c0c1c00f200c06150900d005a0b071100d80303030321862148803000300088c030305407442c01540c1c480c0661921078884a1841d01411010f840c42d0403e49a101580e036202041c01d440c0c10015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 694528210 1250 694526960 694527017
    0x90302160e04020406062d0e060a0c0605060324060a0312030912030203152b140f06061e010918291c08070c14120706020d0f 55
    0x90a620b0800b4410041203a241c3c1e4040c0c030030322501c05040300001c0004141d450080c41100d2441e0b4034106040e100f100d204280080c0719500800210380c565400b07a1000c1d1040348140301e420104120307102c06040507981e0001080e80301203404042c40c90855482c4140205810010190841d50050b8607503540301f110740a030054400009550325506404d2105280c2d40345009100b5042c11451402d242d00070080181c074000026001e0381e6a04000d10f825807500d034001c2c00b2200f10741059440c2c0c6400c1c1c5008965020952880729492040d08600c08034004007280842c00b45100601661070790050207508203403a40c3d01d030300c410b05014004400140d50303448021079000b103400e003076000a4400302000e040c80981840d48038041e4440c42c200000300f03503602c5108042031200381411804007100c1040c5010340a034841c100005042041c4000700042940303091300304641905007210a01174050680e0580c0d40e1b240403900c81d4000681c461802c40c5a450300844071500d04a0440ca0144910042000d0840b400d8001462 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 694529460 1250 694528210 694528229
    0x415090605010e0601020606041406101701031b0e0c070f03030209100302040f0605040e180a1202160603020702130b010e060412230303011e051206010302090a0603080d09030216 78
    0x1000b001c0d61b4180400c9901a604903020091010030440e084036842c1c006004a01171002c1080c10f024880c0184039440b208100c20f480c1541c290f8480c641908404014000803c01c244400310104141aa403150b10b8807451000351154146881d44e02e840e01e100701a800c0030341c10300d07500b000488003680b00c0840c0032044075410340300540e07164540401407410048a9228800b00a0300307000c280090b10040401d03580188801c14540d10031040044002c2c200380c90420000c4c2524005954458580c0e00456200385414000210405103695918142c080c0d22950380002d50088526903c011079440707d074444040b0020614060289048403004103100364043d401102100440e070b0441e0081110303013032084806d40700c16082d2105203010070a68a42d0313404180503070100d54104400000c03050326800b01c44e90041a004103002000b00380040c60980b01c81d801c1c01b051b401916000300040003109036018110031241c0c0300105610f4105045240401402200ea0460440c003884080c1b90b0a0220312410f60054074080c0f5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 694530710 1250 694529460 694529489
    0xb060c01090b011707030f0807030207080a06050a18030c060905120d05010e0108031207032007081206030d020c010c020f0a062c152a01090203101103041509060501 72
    0x11402c3c554510101341e0b81e0301d01e9020781c400b4070001d0060404810815440f111051b242c3e0000d280503418110a50450b41c01c41c0309a04522081c010300350840c44c003950540c042089414102071080e4449041a44d000d00441c02400c0131500083e400e40c0305a070158021030588002e0103480602c3c0c2c00c1341c1c5c003007840c0045e09500c2c0e00040c00a1a0040b4030749004003a19030080d0b2800d00c9645646040260090184041c166120281080f0340341c940a41c00c10780302122401580e0b00741920f0700081c07940085540c6c054810740c5400180e4103040000c0c01515100341340d001401080000c0c0300450310f44100c20f5003260080e41e01658044c1c50345071010f00b10041c0810b44c80f02102c003011405d5001c103000030307844c0c0030410314421101001c0e0743e214807601c1800c103080200666074480030a42d103e16140150001800b03104500d02c030015520034194000ca4500788220295400c1b5017502002c201a00c58401c40070812017003c002180018540c0c01e00e19034000100540070519850944901003141c209030701804910200c407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 694531960 1250 694530710 694530719
    0x216020411070b061c02090408030f090f0319090306061203080a061d040218090d020c06070b010510021c0509151614010603140a03090e090606040b060c01090b01 71
    0x280581c001d50398624030240e06160381c645408085880103042103008039000c143c0641c002c2d039010040d20b811034014041c0221070601e450f0051781540308460119407448000007140c02040086403503c62541e600006604003a018180c00003610140c3c0c00190034403546400000001d417050107004010010901502c01d44070705420040d0081d20003e0003850704901c0e24009010480100d00c3c01a0400d6414111420340c0d0707140e00c00b151010070000c3c0d0658910003000c04201040800095604010010ba403c0d5204003000d041403150358010b0000040903d0310010051286050050600388111502e10450b65501881c10080c0d00c20a003e1680d200050300c0059120000d0a01c3c452101810b5103001804e440c000e414440c200000c151643d0003000c49604001c2e404202d542504107102841d0000002d208008258900380e40d202084003085022840c015000a501c1c00c5079840325200d2800d25014240f40d9072a1400c0000602001f0710b403a5000800348001c2408040901c41c29100c01d204440300030341541030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 694533210 1250 694531960 694531969
    0x70509103c0305090a12141b0f07060c05070302091005060310090501060c080a082e090c030501050102062e0603020c0714060f070606080105090303070306090917030910021602 77
    0x1001030038135130711150080000400400410340c040700149807180c610f800808540e400c601c0362441140d950f901c0104034411030711002ca080c40d2008022021220110359504040d2001c0321550301c0078142d504100b0003040581440703807401d0f501100006090b0243c0d520f50000905036002543d00e00d20408002d60180121800b9205040c05001d49003030404000310183d486190500c514a241d40130403052001080482c07080103c0070440c500c03803201800220000f8100070340036030194403c905103942402c1001554030302a20803070303058880c10ba001c5c0102c1d558440d103001803110719122200d5100d40110011004202044040c0c010704119540540e80c0c0540c200214640021034008010182d15030141d0f10a40d0707130300703012a000c00e0b66a00b000c0c2e49450440c10500300419403540400740950030401005a0144040000c505c2030420307450400c03100e41c45804200c02c4500080300240080410390202400ca006031300a1980a02d1030380c11034005140350000441681c10001c2e003aa480a038807405002185007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 694534460 1250 694533210 694533221
    0xb0406052112220e0f04061a030102181c120c1e11271303050c10020417120906031f0b0a090801050c04140a0807030b01030209070509103c03 62
    0x30140e070030343d070317007465030a00b2a50000500014011b07641c1c1c0b03e24080b00910310b0402c4080e454000c2c02191203018904400a40034103100c001403045540c41e81e102280c4030a1825241c0168000c0680d2020551049094034140101c241c1995182d100c10070011400c0c585070081c0c8089031041030b900b582070310060140089401e4040050070102c42001c034400d500343c6280a015880a106603404550000d2400e0940f6244507440c01031a4600913544001205040b13034004000720381d030301c4100c04c20800314500b6444e1110f00246c074141c5001c004001c4a2044d00d4010095a0031000c52624591708505640750000d080075103600c0700990300c01c085900240280c200c24078400078000304009111516003219801d42e47e200b180a900349419a4174101025921001c0c501d4000d0304000b01150003240c0c5030304001000003001d1104a104540c000c1c0029045807095003521840b8001501e20340180321306007030646181710f200601c181c0c02e2034007020051804050101c860845404880803130001502302000500307654 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 694535710 1250 694534460 694534469
    0x807090b03010221070e0306100e0603210a110a05010518210a0908030406020102190905030a1104200918010509040b0a020409020417010b040605211222 67
    0x34814400c980c00c58120707441100361182c4c5410700100c242d403100015a201501d00302c50540621079202005190680c0b0a0f016042c0d5151060041d82d65071190105640c0b5886261605a600e0440240011300a140b40151511480a003000362030500382c800e0709440c01c0ca039002c0c01d0311660f4440040c40b03914030005240108100d0701c0c0002d0309600000940e0201250900a08000c41c0070f00042c0a8580600c84c0030714802170040340054995450b41daa80080c040e4109405010052200c10000d1000038096099001154000380250048440d0b0380c650b04080d14149141d071b81c01a03241c0100007110040c5000c100780c66040c060006444405040600481140d06400e80618503000c40c01880b2640d10a03000390780c020792100c01422940d5802120300064040c03070344180c20391400450b001c83c803400b0b00841d04988420380c4008011010f0382030100415941c0d20b114003600800c5082c0d200000c00d861220f03100e100240a01164213031a084400000780303520101140c10300d200c10f02d28001203035080055070030040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 694536960 1250 694535710 694535713
    0x914190605030a0201080a18051b100822060f14010e060d080309011b080103050d0929040807060305102909040b09090102180411120705130807090b03 66
    0x35090002082d600c0444200213414446e0b0f07100001c024100a0704280021080410281c2818066142c0680d480860b04078165452131007051081150078203030910b1303000c2c945680da9004651a412035002c2030048511460402104151400000c60786c40d000342000480c1c1e2420000390505580042000080181c0140c0112003000040c0041a0784d031000d24144e4640042030305a0302e0702c4801d0414010060340d00c0912400c0d421110002c4041c1c0c1000e901c5040742d00070001c1d00c45024044000b110300750102c1c0103003c004615100c0d24141c0304018028a41170850300f03058035242c0b980b200c0d960b07860000544e010b100041d44030000c20100c0c00f0207040389030003403140d030741c1c0c004680c00f122000015115164503503592164000c60464525542c981010f5144c90026028600c24104161918045c3d485040300101042044455044c182081e200b0600480820300c0308a06240440c41c0a0701c603140f0103441082000760510100ca1420803082e0f03900c00401803080244407c520b0100d0355420381d002c403139007980b09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 694538210 1250 694536960 694536971
    0x10b03070815060d0506040b0106140304030c080d0e060c0301080c10020705010e151b0f070302030a080309010209030f01020904060f03031b0213180c081f0c09091419 73
    0x180e040c00611201c0350410b56003a05040e54502d80407560032013214101030040e20508060000b40445030083c241a00e510b6558041c00c241d040001926601c020f490050004e0420f4803204040382000016058511030102c0c04100340c101c640e071062401e00242c03000902100000010416640304001541c084842a6000c4242081111003c0e4035009030348206d03814001030101c03140c40d903601d034210002009d00388580365496600184242d40480c61382c0000c000288519030b41c0020fa81400900c240460354002c009141919080d62480100e0300041e02c24103440d9000d00010480c2c0c0d40c04d1150080c2404803000040cac450858a00700b0060710703440d60042d01c00d160404428404a270f8010003110381c0f680c1c045030b0454078403500d201140500e6242000d0303986581c940407919141c00c14100c13240139254000c10f28a6111138031128890f0300c8000c0281e100c0c036441c0020401709841d0115420680d44030003641403200c2541e50b43e140e18004c2e900e062200300e0089807000100700c02c00d5034492510320701206400d004c004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 694539460 1250 694538210 694538219
    0xc0f151d0615041e090f06060603231006050708120403050d2307031808031315020c060612150f160201090c1403011d0f0615030d0f05090409030f02010b0307 69
    0x75080540030a1040d442e02e409402046c01240c1903480300da40ea02c204108441a9a2031000f00200706004120504a0112164000483c000704049006050b209101160580303004025543c0d0b510010f4119804e0078140030040d0084c2c000c0c2e103a94812800703030300c6080da50b6055254100450b10842804c45400058050404008001408990340801c80341000a20b0070742da03901d041890fa0000a00612041c80001042031410f851480c41c03030460f120b0780034000441c00150001042c1d00405a8911540c2d003c82c00007801443c0c021145007480000d04242e9000c4402d1a0001c82540d9007122034601149112060004007010785203d0054101a031000f0440341350541c1c3c89840d807140760311440010701c0c061185080c05580a510040e03507404901c40041038805d14800c1c4586481702c840310000e042c05031100107920b01c0e0304010307005103400c0b005020f030041281032042070701d070740c05990b00c0341003001001c1c0002d44564946d0300c10380d003076980030f52682e211031440484d0090a40b50410500c601a400c10b40c030400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 694540710 1250 694539460 694539491
    0xd050403050c2e230c06040204091704090203041401090c0623040801090c150512100902030901090507050607030c110d0807060e0d0c0f151d061504 65
    0xc02e02040319042c0c00c9400600d525950b98441c264002c903641084075840c2c1d0142e80064800714010782d54000f0641200d040c00c000d109602580b00d0050980c1c0004002600600e03080d404131051522440b126280c042800d00c008540b500030340c01c5a00301ca5070010512040c4008000b1078011088060002e1064800350f69074030960129920802d02840784403551074541800c500580198141a090041d13180e5964007443d50180c1008a01960070781d000f41e0000c90b0340b01c400c00201c8074014140d203035507140690b510003641c2d0030200248040f01e401440e84001c81c2814040c0002c50240a0880005c1841c81440c02c00f42d080c0350f42030344800d118500c10041000002e400251068034190419250210340070759a01103048100da101c001480d80c00000340300d0302040718a50051120075001411221801d041400c1030b075001c080300c0c8020340100b0048000c0c10000d0000c603c840c0d0200c110600128000803803d480301080341402c0303085a003d402520070404d40c401c0008500065100c215000d00a190340184280c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 694541960 1250 694540710 694540723
    0x26061503060d170c19060c0e0306190612060b0301060b031504020d06030203070e0106020c19090c030b0a080c0411090a05100c08030f06030c150f0d0905010204080a0201020d05040305 80
    0x81c0804200c0345a0031601003440305484048044505445c000201000601109585407404071440d51070080321101c0c01c0e201d41c000c0d5051101c0074000307040548031280484d2400d0504001d2503519070300c418000ca1004902c194602c01e0701d1198a001c51014401030170103080d00c58980107040403003010700c100210300d80840445845200c003500c2c01691106255801009425280c0029400d4030958000040102c03402117160304072051035080d03031502d01d00c66082112076020203540740c0c100d0703a5010050000c00c02607403105c440c0f2250350a002400500b08004034002003c180e1000751540c000001040d90b5042c03500034401d01a5a071226a842c0146042c006060300301da81c01001d00801c4000e03007c24540b4068180a511039400c119095142d00d0b02e40c01600c0002e2048490b01e01a01582c0d18203c0d9505020b000298070020048005044c40490700300c0d101030b900400c0c241150a80c80d01c0d603810100b0700030f20003040940000000350114402a00000e8589514151400d0070000100410000b168012420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 694543210 1250 694541960 694541963
    0x304061e0e01081311030f0f07060801050d06020315151c05010e010902250803040314070201022503170a080c03090601051003090623010506040e0109050726061503060d 74
    0x703648242c4d00301e0170407602d04680e030004a80c2621442011040d040c00014480c0114009042198402501c400c41211403140c28410740b030300441201100c1c000280d40740c001d1548504582d0550ba0300400f041d0004e4154002144a041007510003e041c6141965240c0303000c0382c801c0d4408007444154501301d42d03100348c04014410f00780e00d240d010926848270401c8052601d0580d03030011480c2100900b50800b455640e100380c80841c0820301d0600a44241c1e0041000e81d060b981d0141c0140240400b6105603030140c030701888442c402148042404400210b01040b019800010300c2c3c0381a844681342c0d000a01203030f0015181800103401481008010000001c2d03840c1034034401d81d1001c0c2d0303242035400d003900500640c482c020700ca642800029a2203c80c02d0303082041000804480900e0340e40c0c0e80707051084612031800742c10403100000c001441040d229400c41030b0090524a00481840c90385146541203a010000d0281e40801034400e001d07a0740b0301041100304001d42c0028075851030510000050054510400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 694544460 1250 694543210 694543231
    0x1c031118100309051006180612120e0a081f0b210705120d030501060f0509240a02070806010f050d02010e01030912020c1801050907140c0304061e0e0108 67
    0x200760010703200390491142aa4414215014402c4811012000c1d1004d07000e00c0f00c070110703071b038500511000031030082200b26820154035601c0241142c444909003542078801c207040c40200c00d0203610035114144407000411780344016240358800b0707a0900185c48926829165130500300040e6049079507500f1801c1c040c0e5000d541415911040c000c2d02641000d2581c0e210030b5010200601200c5800760201da5a449544c0b03554007045039030380760340341601d60105c00c1d11742c840000d030184038034541030505600e90700c0c44802502d000001d0000d204a0f6007401da001110504c01a00725040810811604004083c050940200030100d454100008034424400d1003402a04000d124000088180d020303a0041c0d0b0000d0f001031120b04d02500c4c4010280d070310303c0c52111180c0a105000180003204d000801c1441c141c0300d00404070310240d140c0840840300d240c12412a00300980d002c0205080242c0c3c2040140000c20140e210f120300708038024120f08001c1071005840060010000f158a0140e03440600d03594020041308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 694545710 1250 694544460 694544479
    0x6130b0f07030e060703020705150c03060f0103020f0d021b0f121b1e19080f071703010608040b0105010203031005061b0615040e0318010c020609031c031118 69
    0x3100034000b5640f202d0a41d0140a003403048050b4150024a501c50003042102c0324aa00508a0001e10b0301c11541c0240072001071011a44904d001c00b07504904880c14074001d81084542941886150f10011034039082a900041d61001907400c0e038622b403940b1040002409510101c001c11540b20401d0040306414184002040070400507101100c1c0d0024840204480380d40a00e081da4020302c9060464502003442180220030f0900c0c0000e10952400d0f510143c80c504045420510075035580002e075048400c0c40320011205c220804403c0a103008040503900c40b40b09090078144202d840700c044e00000d0440d0010070812048601a14000c01242c20980e00c07075a940056112510b100d2a064202403001e000305800d100515034140b00f50003401508032800c020a5450301c041070799a105040d2000c602e40b00c4240301542d030358015103c140070ba6002801c0680f4000a03130000900b025555184065505401c3c2d20030703505141d141c460398244070404520075140800016a0310b00000d18405880e11420248 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 694546960 1250 694545710 694545721
    0xc0619111e071e1209090e070509060103110309062a1911030c0606030709060315020a09120b0702065707140105040807020607170a1106130b0f 63
    0x907440020035800f0441c104150702c40c1850010504030003682c40600141c640b00002c1191029440350b44403860800b802000079511300b0b0300f40060464018240d905060785d4150100c1d50049030002907201300c40b940041e10342c034a03046400c408549001d02c1001141000c8181c202c90b6041c44204845a03c684030141e003810040d4544201c55030b010035404011140004952600c05500000c2d102c0c0c09600304500b600d00311a00c070680b10b0211201780c80080d0441103100b50220240300c80743d0050482c090710313107443d16100d0b440d40d0000503902044001161284250740400130990b905002c010f80158100030483c0d09106040350b15807141285041c540c501041c01100e130b140f221110300080c0380b50302c0b12500716071604206140e5500e140c0c020b1001501d1122264610220190381803050344d1181d64050016400c143d240c0d024469250001c1d1002c89002000c0e401d8880780c140e007400a4465440c3d10380d07a040340280b9044595043c2400549500c3c40e5041c66402c20000682c0d21040d070358002c5140004c1e0741c42c0d6462 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 694548210 1250 694546960 694546973
    0x5040b040905100b010201060e250c0206040b0d1508060c090f09010306060806070507030f2a05060106030b1804061116051606021507030b01050c0619111e07 69
    0x10002c00a01c02c4002d18083c1e0083c5800051300c44600341c0007080065074414890060840c100c41c80c3d151800107100a0701c0c00300c2007148035003004075603240040e20014954082015540141c01001130284045590000c40f10305e4080c0a01c4015451070064400e8502002030fa551480a0b00c1001010300101c1d0710942925403549505800900800d00c82455030343e41046c01c020017190150030f146002e01c0d000240c1090040080301c0c80664160f44200c40c80030030308c60490f1b070346444040191080c0c00c0c02909040301c000944504800c2070242c5c0c0904880d51514202038221401c01c001d540c0645030400050003440900030005901c503030485004038622000c41d544080d40c0c4240c01a00114001c10300c0d0b000240310000030030307100c0000318102100ba260345682060ba0340c0c0210701d25403083c550031000007850940c484d0708004507580040c1011070800302220016420301d082122052a008074a40f42540018424003e812031411070701d02d0645007954000948040703c01108407180e04200020320071080042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 694549460 1250 694548210 694548221
    0x30621070b03040c091e0c0314160e010f231b010f05011a070206090a05060a26010521010e19061107021c05100f02090103050612071e050d050717031305040b04 70
    0x100014081d40030714000c212001003010300d00e10000041c0030302025540303650143700e1100c41401191151885440c079450401c0c01c51000101440002d203041c031881c4580d0b540012512880e9600708008200401d01d0782070300c02283c805038080c89540da00d41c1d1501d00340b404c1316800c0f1000c1980542e16256a8150400800e5025600303900031740e00030720b0010707001c160250b103c2c0c00c06041d4040d40458400100300d0113820804d00e0000c1c0503d503848505006200d004044c1410b8410511100c07100110f119000038842504025411014044401106600c64100101882941d9481c1e41e070794140ea08109190300480c01500889c1c610b9100e80184000c61818050200008480008021000d002090900e64490081e402c4803407102d010905060204d446854842001040c640c48a0001c00d41c0a207424041d1020060b035003440b110464814501280944464440e51042e03030185c001000090314254400c04042021203107401c050300288203110044034005101e80480d02c00b01e41c0800e01d4600307200060000c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 694550710 1250 694549460 694549481
    0x6121008031b060703050c1b0c0301150501090801152d06121505150a120905030a021501050108160512190e0a0206030621070b03040c091e0c03 63
    0x4404500c07400396036100e0b200303004100c0c42034050710f4440e00c0d050b0090307090f03a4042d1181004110309100e10400307040d0100b00700100410060448815071030701400f107400c40d07004001361164050203900500081d600f1009450007031642c03000030043c000701d200303a99000c800d207801150813038064440342100844035036407001078161200303841243c0385a623041c0151010f03001c0c140d628000345c140040300d520590103141080c00c0710005403100701c4200c030302620b07a0384581c080c0c00003034144040d005201e00c000740288100f4140c1803282e4011680e4016284001e45048000807100c46150072100060246907840b030041504017880784442c14141d4040c6005403000e004100558940c3d04216081014030b48400e210030540b00e4401400b002030303c610800f25911803940c01000394210204102007030440c100400510880c000c4200c10828561007020840d062a64581c005200001d02003340020b0000e40c00c0701e42c005102403001001443e1015888201100c20010708111140d40e0b201800c04460190b0805001c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 694551960 1250 694550710 694550713
    0x402030d03050714030c0d11120f1b030a0203040b0c031003021009321203090603180d080403030c080f0a15050d080403060c03150b03060315040b060f090606121008 72
    0x2e143c92500b011094100b21090110b035401e01c0031540708c0140c910304503101d152808035149a2962941d2030000300c1400079044038184560b041e40ca64206c14080061401203c00c1000581e490810b8189849482406000f0841b8050104180100384046004c180300700c942c15501c100c1d1482550308103481c101c40b16800481c041200031194421511510012010041050031020810001031300340001081034510400032070f40100440000340c600b80028607448041080715155140441c5011400c1601070681180480e00000c28401016054012103900c00d0203854078110701d01c1c0c00b2150b14110000a010103440039651030305410707a600910345903005030902400160440c200380c904640c0d964441d200541d6443d01d0205074500240c441e0007100102d6412007045000035091408c00302c1544d101801c12036061041c4201000c00340400343c4890310660180050b0051490400184041c0030801a44140b003142d8210802c0700507611401511200c0c641070327050082075070711507000305c61003c142e420102c1e85 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 694553210 1250 694551960 694551967
    0x316110f0c211c12140612010615030b041508070e060301091211010605090907030b0a02031003030f0509030a030c060b10141b100c2307020105070222060512060402030d03050714 78
    0x4025100804c2c040c0009031090180c1f00000c02d5164200c6a05001d1503c034150104405d00c1d125110fa002102e003034000610000345101c202c1c605035003c12541d44416641c0e08441401c100250951303c0c2140d003e10290003c2c4400025986c40a00b40c40d5940100f03014012002558000010250b110102400003c2c03c40300b400d04044a200355210024401100d141e124540000c1c4140400c0c002d4900070341c2e00304071070010681141c1d0213580940d011100340080150521064141e03640801449480d103001e46c80b54622203581382800015114200c8001340250710b010001c1c041c803640201c8029000200c83d2625880e103071000c03501e00822820451224240c880c03007441c45000740e900c2e4410130300000f29807900f60420703056045a00c0c0b40c19020780340c1940c0060500058003d94015001030952030b01c02480b0041824000c2c1104444070070000941c0c81c1142e548070140128200080003042c4282c0d030350300408070f9241070b80c0065501c0342a09200341c100b58a03400410003107402115200e6880905591540d203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 694554460 1250 694553210 694553231
    0x16110d02031801020a05070b030601050c011802100c0c0303141606141b090607060f0504140f03090f0607030c0f050105091c02030316110f0c211c12 65
    0x50301c2d000036000d100154011a02216a0740c00080c0844556600401404005160044100301c9403c010a9241800130800601c990304200380302c0c04000101403210414030426900501504100c0316130a130003480550425500480c07140c124000c200da40c180340040041c0c20680000031540900e40c0031000b1070042461040c104065900a00383c003a0441c1c10100c180d03503a6407400094201401c02103541354030304201301012414110018407909015482c0400c0c450700c02d603032050841d0030441d015900d010303c2d4054040d810000380b00750a4160901001542441030000020340503809800c3c1c0d032032113448001561410140030301020300340c180d0800e80b0f4460081c1e0500b880ca010700011520010640104824641248030002040c22540c0c17180e402182140d5551b2404074180011743e58400501941031b80c140c50500c800c200400702ca1454401919110020b1030501c55210b20095040c8120801842070f803003c0c14001072840980da102e4130703130a21007003c0c2c0d540a1321b00b01c0c3c40542801d041400d207402c028 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 694555710 1250 694554460 694554463
    0x20d0501090b040902012c0a03141b0109051215100806010f030b04020409020411040b041e0b090d110d0b040b060108060906040915060608090d0f02030316110d02 71
    0x14101c072003444040c01a89102810041210b50f1084003d0200e000101003202460241c400d07a00d1072850f1b0002d078088490410b001922580c000d51013121491540b40060452000622030b20005181030042065003c0da4140068881141401040c6c0602d03e41000ca14400030100003140541054031400b00050404030424500d001c0a0700a4013154410900002042c4441501e480300300c0f07411404c0e68115451300c2e030800002d000171600030382e44280c441e91610782a0545070300910040c118500c0c034940e10742c40c201d0550000b00c24040354090b510501c2004001c2050703130508541044c0c23011183c40d0120903040c906903000e016900210b0b9000b1100d20f250710304021004100c14003890241148100a40d60302004580102c0c040b60b42a400440070004640c02e424036030415000188943c0d01110300400280414044900990018001038500814000130100c1441a6042504c139843c09082403540070310069503074070004d402051101403860400469510a02c042d048801c200c071306507540e1a16804009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 694556960 1250 694555710 694555721
    0x11e0f0e1605070503030601050d390c080301060309080c0d0302070b1311120c0607050312060d080717071b030c06110a1e1401050106021504110f011101020d 69
    0x10302140039980c25501c01a00070016540781583c49801545103541e02c1c0011103080d0042c2618160f841c1e00d9440c0b401e194030403190621080a600c14035244905a128201401c201c00341d03108009000c1d1041140300813444107011281503800c503080200c4c05603542e252045071846440311043c0380b0301411034035032401c66060700101079160080300140504e81383d100142d16a980609001800d00c0302c0c0309880100d904100c603d0344001c2440c802074410480040000c5891544404401c944e01d80000076420441803c7d248402d402c0b4000f81d80308030040000d0b40d15412030348122440605120741c2083c0550103513160104840c0c840d40c4c402140101d0000d81c4628425540d142e0000710754094102c8400314100d8421031081d12034885940c000e0480c4443e503260044040c40c50800080f406080b4944800424008000c0d03103403040f402c01c0005140d41c50241c000b41849040ca0440490410340008d020204009124416200c0011070b10f000040c0502c00068030421100303695900c0300e500100da404c21011041d80f05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 694558210 1250 694556960 694556971
    0x130b070302070603060b071112010606080103020913031409150a05070b0a0203101202060d020705030c151312020c0307090e07050d020307181e1d0114011e0f0e 70
    0x80710745a0783c8605060b8280d03204c500411064510034060000403940b034180c0c1c4d0003540d602414080302c02c449082058203403900c0c1d0308007102254008004200f1400c044050799448008040e00940c480a00d50f4010176140c02c032004c4504c0381401185221007550340c0c015114007500c080240da0780d501101e8034080e01c0354001c51000c0c1d413103010400024540000700e008403807042150741c1c0004020b504110340d03000f00c2100300009076000a8144801d030b0643d02d07240700070881355000d14000c54644070446006232400c80f0107405103021041724800c1c000001c3d0070501c902449907110920100d0a000320301c0407481d22001c20754003545445800ca000801c030080e50b00c01c00c0810241c00958080c50f4580d4144402c40321503103c004e40550240c00108441201041e111240794000c50000c10900e11100340039401841044011003070390ba450400001c4032615448031032500c5032280c024821003041220030129468140309040301c0c040008804202e0407024841c10000c0c040300400c0303003082c40c0c0760b04030104211021582c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 694559460 1250 694558210 694558213
    0x52205031005180a170f0408010c05071407120b15030a0b070f18060e1c0b0106030501120b01151b1b06180b091f0210051303081803130b070302 63
    0x100c2161200f01040741040541c12034445c0781c403000054480352442e4403c0d071b808180780302c05001c045074640d003e015800a04400743c2c5c0e0303140c48040302e0801a01110660b402e4070441e42c00503d0030000d00c1c880b0713100e032452542c1080c01c2500599a480301618400b031034040207940b600a4000300400c000c01013070440d020343d440b5511030302003191441c41034803c41030030342d0281901b1850a1081141a00c03404580c0040e001c00b8141d8180590011003281c5021440d40080b00c0d840c900d0401031018550600c1401c2c01484c42582210307000545454201802c2810f0160b0040100340812070440320b4041c81c1d40380401c3c007614070828180c0c0c03c14240990031110030b008810040031002000281da03840b40814a120a0b1401c548080d0249000743d0442e10354400b0080f6030704040340074000c00c03d0001000c1181d01c08541c0790050b11460003504001011904c00500490400050780f0309032001c203600144295004a42d111080b49044051581c9860740c0149600100c400c810b10340b0105031185800d0181568520940 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 694560710 1250 694559460 694559491
    0x6050609010e041d03030403120c0819200d0b040b040b060d0b030a0c1707270f090b0405070303030b06032503060e0705210601052205031005 62
    0x40015510951214900003065500c541c03072245002d5024009250800c60520340f40d00400c130300e05080d504201c400350007182d035080b035030508044079001e0711120712032910300003486262844540c1c40007030745d41c2c040b81c942d50755031603007140205d185010340c9041c500500c00380c9403208445080a00500620700101c1d00441c00d1010070f042e0303800c25026003503032014001c000324200b60078070301108020040c490f000355040c8107455803030011485a00c01e1001603c0c0307064a14126141800e19145890195070043d04540f4a01c13440340e12448544804c1e0000400b03041c8003040800c3d5000726240505200d0350003134001e0035584288401c00500007000c00071288030b610240701e071420400c100300035800110b0b800c8007842e14a0940050725014100c45080e8040c25080010ba107603203c83c0c00801010003140c05c1c401242000505140070710503034021011008006180703c0d254504500001c1140c0038004c02089100303060300c0d07085c4194800c1410203024190103001c8822b60843d4180d040064242a580001400b0102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 694561960 1250 694560710 694560719
    0x207080105090a1110050f0d020409021207110c0a1a070602120108070e06180612010914210f0a09090c180806040b0c0a090906080d020d0f0c0602070c050d0c0906 71
    0x89103c5da807a40e4a88600e4245001c46042480a52107080c1c450345603a401c00000c9168140c82c03001d4a00c1584080c005180c6280011014015500c600c00b5900d16174401e14080005030703200c0c0c1843c0141c58041e143c11249148044003424180503103000181900d00225006503209804d032800e50480b44584100d52282d80d070381801c20f24402d829a1440e400c0500101160243d4100703501290700080054074524418040003001400c403a0f03401c5d0221032003504160b18510b40d14003002f01c80d417085184105007642640c040c40c40050351082822a120f062000700b06404c00e41d0041000100a1090f0341302408100003070fa0000b0920342c02014a1100c403501200c001c00c907a000090030303620a03030f40826071100d652075480294000f500520591002c0007440100401c0c04201d600809006000c0b02000341030410f50400086d091100080d680e0007080740c1018400600d540c07202600001681041d001a0b4500880c1090281d209090704429082078406000f401004485040c110484481c0c12040010300e40301c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 694563210 1250 694561960 694561969
    0x200a12080f0912070c031407081b010e040510031203020405210d12110f03090105061206040803040615080c1513050402030a1803080711120403080a0207080105090a11 73
    0xe0b19203016541c01203c0081d04002080d0040074014082c6501e075203010b54903550020884410403220059800c100e5081120420820a041c10003400e0078482c020040500b00081030302e102c0002e01c038411511000801c21445c1d0350444100655006014901441e004000140103544a072081e0f82c02034011484a40c441c44007415a443c5000040c4080c0400500c0080300300c4410b80d5420400c1107242d91a5039000c0c02030030720b0b401043c200d880150752540b2403603e0b20701c80b821200010071880c05044200111105c4d20345c00f080081e40141d100031810b2710b94403a0704104009201504864840010b14030011444220004104111040450b10001006100c58101845005501004000705a00101441036151580255500c4217089600045a170480c0030b080c00000c08009055000c6141c4509100e1103ea01c88445035054022000601d02008e00034404485032280d03200140c485240400c108500c41d02c2440010008d180e104000d1140341002c141c9191150a400383c01c03243d070300e4900500307005410b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 694564460 1250 694563210 694563241
    0x40b16090b2703070f08011a0303090108090f06070908060a06180207030219230102030c04030201140d050708011d060307091112040b060f0904020d0201200a1208 71
    0x80080c2060818106110042900440e407160b084100c041c0410800d49071001c0240030018101803149440c06450010401d00311030090b1440d10030003688103204003c0e502c0c00811a42424001c2ca019202960344000031414075a41c520607a90328000e038001e11961542c400300c901d083e1078400090300d056440c0d0956000888203079200c1c064a40d5035482c0785ca18060103a0380071f05003843c000d00541c1d0480030360a480c42100314000d40d0032a0038805240e0054115600320040380680c40c9180003c501d5410102c0c040800781c062840001d04004034010400008403030b00085e40c80340c1d0036081050206080c8a500507042d003400740225540409500711480300c2c40b4441312240d01404001e4042d280e15801c241b00744002c1d1022140060310300200700b18500c114034100c01c1492145000c0c40c4d07402d519003000c400300301c0c80c1e4500c3c54129110f02e2002c0c091201681d1780003000f003036143c0c2c2400c01c00326428603d8818602c00c18141400b00031802081508400d2040050041110b84c4140c0d5400806656941da85800500f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 694565710 1250 694564460 694564469
    0x3090906040213090b0a0503060115030e07030c05190902160302241902190305060a060f0f08040213090302011a010c05060c0f0405040504050c04050903160b060d0803040b1609 77
    0x505a00c3d080001d9826644000e410305000381001070380640300c2c0040f03407402c9400e174400911703001e000804041196240c0f05030500c0c0482c200180041618644911841c01841d000383e61280b1414440841c10940d4441071000820300d1501c02c1d0b40b503016281c80d03c0014180070328250b001d80580303420352407400c8240141070700f413072030b4540b054a460310b070801c00250140c0c0400d0310703aa606908000240c611300c40000100c4d25101c82d5a0046160b103080001d100e88189254000300600603a1450310281603040342c0e035001200d0052034074440582c3d07540000381c035289603903a01042c6030785008480420305d64190020809482c0c060301c1110701000110046411702d2600e90003506542264020030725a00203207000b0440300230382c0d20b443e07400c0540320000901114001c3d40e04a4141d4030a500f9150182054001e06031300c25013900103142080d01b00082000c40b0b125100000740590400c800146841d03540640505640380c105076800d450789040e141c60103140d0002d0b1000942c80d2020204800744a1092ba0350700c0c00c1d81c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 694566960 1250 694565710 694565737
    0x40b0f0a17010e010510030c061716171302090606030f01030209040f0c060e01020f1b0d05120406180b0301060f0c02010c0b0702060109060f030210180b0c030909060402 74
    0x501d4840780118490241e0038500455407907140c9401400001d0003081d00407114204200d211034079514162455650310391250091100c940c3c0c3c03840000c240d8089950780b00c03501c080340741c0304c02c011504115409104022800c4204030018180954150300520301c0c00d80a100381e8505001c1d85803401007015a00007210001c0300800c1060051005080850450f500180310f000716441460103952525191900e41c3c1040000030700224042045680c10845103c0c0c4452801c0500004d04400540ba00c40b0410301500c0740c02100c6c580710718070401408110025204486c1026551655210b500050441060301440500f0000c4188041500250803080701d048039603503101c285500340011002c4c0c610704100308084c0d0600040305940b2020400310f148052140b10903501034015907050601c0e4800b1100590404070300040074540c02e00041e01c8141031090107801605200c41c48c1c18005554132101401d54002003d0941e0102e030420b00200000041c0001000c00c60f080c865541e91801031208034040d004208000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 694568210 1250 694566960 694566979
    0x9060602122b05010608040605161d01120608030405010207060906020d1407120206040c2102090c22051512040609060f020a0203040305010606050306090f06030a021806040b0f 77
    0x4908a101c848040807985004254841d1002c142003107078400d80c403190211314488100401c001c070702d220355544110f01541d03c91000805200044c0340d500310618080e41d010046103007440f141e000300100c15400041510901605490b806004c0d140e80051003101e000d403180c48004038003580929604010355425a0041c03542d80b5000030100d6400d031441443c0700c1c0909080040201087c48250100300fa418141c004041d03a081c2450429441604d90f8048580400006000c03070b1178040c90902e9019180d012154680c548d122041c00c590144640079100c0f0840741206126100751050742100d0341110001c0710504449800e501c1e010007548644120324070521001d400041c0054016406036040a02495000503280c0c00107040b2009c0340e21108565005da8004607007002009000d00440c80501406c0c03502904509200c40819045078015040a4015903c900022480e40341041100c40d85a001401c0e0900458108440481680c0690701c3d1030203241400f22010550401c40c0c2101c01c080d00c040c00310111b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 694569460 1250 694568210 694568227
    0x3062805070e0a03080909010b0c03040915081f11090f01032d09151a1c0819022505150904020c0303101208300403030203010906060212 60
    0x80c4002450310003070252010122460303860307140c6000e0283d407094603510303603c0001d0000c1017a031190590180780b001900308800920b041020040e6811182e44a00c0442e02d0b03c0400b0848208281540014046110761400801c4074491000070702000440e58100300052002807940941e20305c903010340e25811882140c040c486035442a0b0001030046420341109514603840041d10032004c3c81c104600240d513403522052814800940200444290100c0082094059107080d0040c1800c803103103c24490030300007041a58a031410000741c01d040c0d610040d04c03a6201180343c1b500d0514414004100e006100f003140c40c031014400c407140403150034154541c0c41020361411003017142d4500031701350300103001d58207004090702916039001402c059912840030f540c59242030b00d024241403402d5404010340000402154000c40d00440840d2400b846500c0f0315010300001c9006103001c20039500c4d81c4845041e820080005042e459406981641d00d000d20a0103170f81ea840c0c07400c0341e840c401c4003011286440d0420070300d00b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 694570710 1250 694569460 694569541
    0x72706090302150c0615031e0c0f130608030d0b030f06041403040509100e07051201030813081603030905061c0b03071509030201020c09090a03200a110306 68
    0x25040e00e16610540c0c540100d68500d10b0a00c0800d580c2e1460310128400d052010341f40c14006000c0102c0320042907605080001c80490b541d5014110a9000d080741200e0100543c0304c0701c0000b940411100024014296601442a80c2e030748030200b1820070b50701c0c1503192081882c0100b00507808042ca80020421900c60391a4102030400d015000e00e001d10080100040ba41c845c1d8a00c684250102070816811929100000214840040c101010020704010b505481c182d82100f543c152900521403c0e220200110001482c0d90181c000342d00d107102c0da448162100e14040d24080940f03100b965a44641e503940d005000e401d02400310100c082085600340e03060002300300e03489400c1c00b100080c2100c1056a4035100c1140030045858880c0001c0ca00700014800d41d40c0411000c034030110141ca04480b1441c2ca51034141e240c0c0d8400e1401010020402d02440c0030a41d0100d1801100402c0740179240001050325101c062101c1c541c404901a008803400155001e92055280094903403030220300044141c44078003031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 694571960 1250 694570710 694570729
    0x6050706051b0a032403030203091302030c0304110d080f0d0c020111090625030903060c050a2111031e060603060102030712020316080d15080d0c0c090203072706090302 74
    0x2c00580b82c4103480041701035898011000194001d40146550350b2120707003403000c1120304266868096004006119050308800222a401b90700181d4500000c80000c0005203448116203000c1c00c022404a201507140801d080148411100a80e08210058088400f64284c50300902e070307401300c01d01c140300400c03080c01c03d00000c1c05822004111a034084036049500302d0281c0e043ca5041c6d00154800b282402044198031508000758414146281407480b0003034010230100c4122581f400045034801410a4026140c00c426011038007005802d841e85407031036003200c0440c01d01142260744040d05010407801d042c000b00f1680a45c0c41079000d0b40c076182064036240c401c4400d181302802144020000d41c41039019031260502c10500c81e280039661018014810000d80e2082c0e020030480800001c400c114000d03000031501c9004100341015009814103003860058581d241d030043c0841d60000082048090788039028071411001d9010440c2130b8081300b00300f000e070b00d4014040c2101290b0403070001d20251900e107018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 694573210 1250 694571960 694571981
    0xe0607060b120102030702060f0112060c03150305010e1204120b04020310050901023106111f0501091d070501050d1d07051c0506060904031806050706051b0a03 70
    0xc104850701c040420400c542c2c0400039040c0d81d40c0441440042035042c09840c0d003000010301e18103c1941070070141d2804501c0b000c0002c14507075545104446141c0240c0103440085462521903185550780d00308540038140c0c802206070b0902030040c0e0240311394071410a460980e101c094200101042c544d5401002c103c000c0c00030799052180c0210103242c0b51407070040728892021030f400540c032201c4028101e03951521b081c50801802c80145803144c000c5510410003011260940703020110f1004d2a40c0d440d040082e0302141200c4251103c000481c19256608414101c034819a0100300c02d43c40a034420301c9c15603c007204d02c008c40c1c10500040286622030000307040d180c100c442c1c1c000340722030810701c403032201003044440300d42190010302080203c0c0c80c01841d05615800110700c40900c000f0603640d80c54a07280e0080000b40f04002d6240032909151194601603061404002a00313440b9440b00d1024080c0d800551040b61603a0410000500e65032840343c2e4412400704140300b0600b030030b8680b0f20990190600401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 694574460 1250 694573210 694573223
    0x5090d0302030c24070306030b0708151302120601110d03020f0409020408010906050105040b360f010e0601020a0b0103020d03181715010f0302010804150510060f0c030e0607 76
    0x4901900c205220000c1ea011310301034010815940d9044044c881c0c100140700d14203042c5484d004102203075120101e84d0388074016107410f10b000c0da901e014091006850b03021450700003004441105002e9140d13401003203030110b8201041c0d040d035038910045802c5007800428080c1c7e600060811a0b01c18029000b0f080c5a1510681860920340c50350906030403600203a01c1280c0a80d12544880c090000341c1c45003030f02400c02600e050103000c1c00c400c080384e14150307141e45c0c0c80040c88040c50700381100700991a030000001c000321994000750401c0c040d4052046030a0054646440706d03400415015800080c10200c07903940720160320f086a1958003048080700d02c4900a4050018400314421101810041d443c050408444d000102c07041c1214064035001d519160408406a042d005100400600d22402c0440e80d0900c6d00705180d41d503500d004503140b443c002d0106071041c1008140620402032080c03400c00d4524aa0320210104021502141d800b034201c0d0002d00401e00e0340c1c0250b002403e240f40100b0f103281c0507a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 694575710 1250 694574460 694574467
    0x30a0204090504150b01090302010e0f0d020d03200601062c0a0e0a0c0e0603010b03041a01060903290601030e1e06040b0f19050604091e03081605090d030203 69
    0x1e6144003510021102280d00c0604d00340401e400581510845511180c2843d115840328115400601121442e0b08041d01c10548841080c07201d030790b03800c03905100c554090290384074444145006000c01e8a0a403503500804c00d01d2800c40020100003c072a4121032440c1e88000c62140c2e101c80c80317600504441c2d40300b0600c032014507001e0a0303a115000f0369001400348094940644c03911082901c21a81c885100d0010402442006c00e0f103582c41c5002d40c2c0c15034122404a694a49407813902c403841078042e0f8444641c4803049000003c0c40d40d0071940724000c8a004528507000068851480c3e103100c4100442c1c054042e031301a011403090b520a5115008003000002100c449400d00d00d00852000385542c1c08001d5540302c80c0400080003030080500b50803040c601c881d11a41d040800700d00e106040003900c22001d0540e80c500081c01641c85070420660b423504000d529480d18103540002054510400003600401c501d0400300700c60030240024500080e48503511140cc00201108100507021548402d40c02c42c807007030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 694576960 1250 694575710 694575719
    0x19050a030e030a080907050607020a091a120f07090b06030a05040302120c03041a07050303040f0c03020a060c05010b0303160803090307170c16120305090a030b090c1810050105030a0204 81
    0x1000100b00d03c10090b100c00c21186017880440c0e00e02039035500f0440c001c02c401e211980045e01e400d03ca80c000d903514848042040304018403a60340d170403000c0141035480405100c504040302c00c046241d218004502003642c01c440d40b11459801542d82e44c0c42c6407900424104006400c8aa65600c46c0ea0050300c80c0c4140d400c3d00051030114040b0781c002805d4401d407900001010006903a944c02d10505400c60b1810030717803c045142d00c03103684900004001800c01100f9100140c20040c080d0524005564010003a080b03071501c50000901c0383c2840d00c4111900e42c030b840060445841c00100350780c400204203408200c1503c003541d030003030250405030140303941d4401880080d0014200c0c1074007140c204c0320f8116007034a450015403006d140902e0251040030003042103106100550001c0000b0641c6909428041d95804c03072034002c922502019400078282880c0c00c014800030308800700341c031241c5c410121003d00c0b15941000310103442d003c064860f003103107100008040109500035406180c2c0907455000040c10075545 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 694578210 1250 694576960 694576963
    0x9060a0302090c0405091005010f050f1e0406080f06060a110102120a0c021009050d03020306130c02160b04080a0f0326040b0a020a08011703090a030b090f0319050a030e 74
    0x3925900b83d2000301040500580c00c0801240d42d201c1045014402c65030328084c00a082c00b03080031040400c021000039641141001d0504403207004d0301040941c00d6101c0e210f00061080d800501079031002600800218119a040500c00d0740902d070018440351500b09200c0d4155052a0f0809590368195001d226802910008818083c41003140b00710100e0800300420000382801c80322941c0c881280d01d80b07140e5001080d000030341410348108034140141d4940350440000c0f264a02848940441750420a03614013442e4040341c8807010700250040d500c80c0946542e19000c09000fa80603042c4158080710610b808560b01d145400c500a001c0d0901c0c00480c440001310b295006240d07030030301d080f1901c020144030401880305241a4402065001141809455400184010010311070001d2034803180d0340c81c044078032007403048503080c08009100d100440c0d92442c000b0082101217a41a8080c01188032400fa089000300c1294600c2401c00d800d21038440d448441070f1040c1e000f9a01003410159210b01c44a0718900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 694579460 1250 694578210 694578229
    0x70c091a060c191a0f0c0316120e012703080c070201090b04080102091005030f190e10090203010c03091e060204090c0e10181226040810140609060a0302 67
    0x2842040c1100c0e803141c4ca83c010101c1c8098541e0321a0071069041010300b0710301030140c82e002038200134410341d0035000507011250038000e0102150001c2c0750030131940d04840e056003c41d8074214582015000c40600040c0040b000c002c00001402190624000580d100301d040c005200591050402d801c080b91207810026035902b054001100a0394006915522031825410040c1c030f814071883c2036895031501c2c5401d0000301c14040e29000354031024100400500d071150708290b108104200860300e00b1a660110360b0080d250900b4282d0103540303821411081207200e07000d0005110b0300810024011446500422031002807182d064482c2642400003113a80d814501800401d0b081e207541da211840b100e0404c00044c030080c07008840c10b0020043c000d145003010000440c08540740803011b071010400d242003a40c0090800d0a00380289403004010f5280c0c0e60010b40a80150350503a412105107110394040354003100c5e103840f1440c0d0a50f042d000001c1540ca41807051591100c00039081048a6549a000c1502c0c800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 694580710 1250 694579460 694579463
    0x203090109050a240b0a050907020f030d1a1008070809030909010b0901030513110d0f290906010e040204090f06110301170a08093003070c091a060c19 66
    0x10300045544d0b003408007a185903032805204e82c003c00034601940001341d40940300d445a240660584000600700354003d0200b15034802c6410244d95594090309480f01c01800c40c0790f02000103080300399071200d9a00380501810000103054030388003c0d60b07c0c0c3d00c0c030584500a0050007003503540310401000c0f1a0b0b4450352007480c0200016000e080c0c6035000f100014056440081071085810445e40422001c034402560381c42c880a41500c9500e02244d40b403d001420038400704000e0100d000528150354030f480381205510f5550034210b121400c030317101c0300912071f22080280310380c1d01c070119114042000362410f61300000341d02c0d102e540440d1105ca040c1d500d480548504100341d8480e0400440104107420191120f000000441006014895015076034110316001e4442c0c3c10740a411340d8654125180404440c0c00c408040842044101c0344052980c3c50766940700b4481114418805040014070891600421041030048001c941c058007180c0180708064020a0300411244189100e04540010000b40c203458203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 694581960 1250 694580710 694580723
    0xf05030d02060f18120a20010903020a06021305030a0b06040c021c1224150906050409051503060a020a020712080901081f0b0c0f12071b0e0a200c0a03030203090109050a 74
    0x2401988489441c0e91a0b007c81d00c40b2170307410b2070040000a54080360880d4002c0d885040143c90707035000307044411120900e0700501d416128002c407800c180007c080b121446030300110340911103d030044a0403600c85c4849010403410000d4041d0040c071032030180c1c2c070441e540f0809650000364841d41d0040d07540c500c801700042c1030400d1113580b020b004480c00ca203000d840e00c0032103040141c000c0d458500e000307040d40309520841e61610f9644010402c603030203400700800c140000508603031304cc0c24048440717402503000300e0030480584903c0d00300003000300ca02801552415000ac18682c1068122030055030b04000050403820303080841190040c866103006907080c0644255901640c4411a500c0c4080c45c0c581002c00b2a070181d40b0100410f0001140c0340c1c200c0350440e5120380460305029005998910702c07181600700b001151100c000300300046440d9400f40c1301c40700307501134003009184a002007181984a540b0000c0a540c12000015010034000c0c0c0003950840248800010078500d2070b104d4074180114191304030380f034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 694583210 1250 694581960 694581977
    0x3010b090a05040c06051c020f0f03010e15030615040b04060806070c1713030f030519050c100920031609050912040602280c0f05030d02060f18120a 65
    0x140002405201302821240c28040d24045805070180b8002c400d5060032078045400007150f05013040d10b801500c000c000c2c00c60302c2c1074032540c4620f402c0a04403c1203844152004002800424902c0d00240450040f20413a032429401e030b49050a1001800b038917034005802c65114100080c82910030800b4502c03038111690345184442d441e140c01240d000d80c1743c03008600c50006015040d02c40c015080800110781d8441d041c40840e015500e401c1c3c54074040c1a400350708807828182ca00d41040e4200c40241045180041603800c40755505480314102d500d000e41c094000504420364030101400101280744c15103008040b00c0c0c5060192030040d09144050700102100da48810900150003410007070b0308801056090781c98201401e103c4001d58891318568400b80e0100444c0004895482650b20800d0464110721a2050345459083c0c01591507520711855009105018038840e20324800b050581c000c4034410700c020380d035465500c0e026100350a03c3c0c3d2102668007820030082c601d641904000c203904a0f0a40341c48a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 694584460 1250 694583210 694583213
    0x7060e031b060a090e0a0207020111010e0a020405180f0a0501060f060c0305030403050f070c06120c08040b0702010b0303160c0e1608190e0f100b0a03030e03010b090a0504 75
    0x19911454210900aa120500141032406444450108000c00340c6040c0d80b90109107408503250034030342d070081c01680103080c1440400030f166001403003c14005c4e200c82540403a107600c02400c0311548800d840f40341c5c200a80150061800703800254008665000704c500c10409910700d1414240ca009407a41d4907031000000000b08402805402e000302400440303504501d00c0c08001404820071070800904107d0004001405c042c080e00540d0302e800c404083d000d44810507440d0480300f49140d80500000304d80c0400211580d0012401110343e20b01c03259440a4aa880303941c1c07124111074001d064081036540f101c48401c281d403400c0000e4a07100106401000300b01c0307400c0c24810100c0b90340307800c90140c0010583c10040b0121502803072104029061401105030350350350318036050681d40748003d01c42c503e0601417001c00c4000c0c0010001049004c00b0191080d01074800c1500d0221510b0b4108150800030b80079082010a014a1002c0300198001d8000304282c104c40d0300044030441300b101c0c0c40b075080342e40e03005100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 694585710 1250 694584460 694584467
    0x1e0909112109030f0d15140108090d020a021903020d1b0602010902210c130f05010506040609050d0c0302060d060e061504170a0206030a0204060f142a0a050706 70
    0x10900080c12201000909040c29a43d40f64801d583c041c98912100054100c2ca00d001c641c001200b05e182c1d52000350006440751031181542900e11426400201580d020924150000c0f9404202c1c414640061440741200c0d42444a4102d48281104051036100c00020240c2c80d9881511100341c4158006101c00034400305016070740c2c0e000d8105a003168034110301440140c0794501e40d6018248040c81c9444000020b038038440c504548010f1154000800e00c0e0011003481d02078010402001100b4014000c5a072108140010340c019481241c00050381e004041102d4108166511070040c02429000c455070f44940103d4410390200b161515580e650300d030104084000c0c800840c1e00540d003240c0121403034820f41c4445070640078500908401200300511f034038440d181080001d1905501402c500e840c1e241050303d030340007500540b107424080341030142d20204051003840301c11721640a0b000c01c542094840b04c04d5070b00407c96a00d00145840108000311b00c2c1c14000c104000140d485000104421420a08001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 694586960 1250 694585710 694585747
    0x718020309120307090b0d09140606040f1404021002100603030507200a03060506061b16050a03050a06110409090c08010c03180f050a0c060806180103031e090911 71
    0x10b0032002401d20034882100c2e80006000304940300c1e61a8980c460503000e0061005080c12000184103132001605840803000114080d072140104941c200448000c028103401074650b80020198913203424800200146840280c20f00038001034412210070344010400b06d001c03148645c0081c0e0200303501144902c204100d03480440c405003401c940d1888882c8105001c1401c80c81c0c02d000043c00140c4a20006903162120f50a64940b07a41042200b0710150f101c8a0440e140c4415505160303042c0c0c080c200c04030f69820444049400c6980c04401070041c044141c441c600107100715500c80380b40740d1080100045408141c05010034941c00307a06548016481d00010a0031141a80c4500c07040c142030642c0c0b450020503868941080c5604075000d0900c01d001890407904122060200600c114448203020a140c0d500c0024240309040658188405860344c08222078620300034031000b00003d41e120b15040c848404400440400b01003401c0002c02c1a1301c802c000c1d01503400051031135190000c080384d00300c00347c401e01810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 694588210 1250 694586960 694586983
    0x5040f031b1406072a06080a1406060d02070303060e01170c0a120f0812010b070c0b0315011d12011e0212010b0708040918110306071d030718020309 65
    0xd48503070391101c40108143e40214030001e44845c5040503a000701300c0c0d400b0704141010018450001140d07441d110080e11105082d0f5004409500e40740021410302810381d000380c05108010201070a2241c01d0350042c001c0c0d80171041c110704040d12841c1c00600070301ca40e40000e01800d075403c0c245002d024416003452600041c0d0500ca40304a00c090b0081007040c0f10702664101c050380040c4241007440b100c0c103045001c0d220300e84041d80d154050000004001e44404054080304d440fa058034001c1ca59100a50603031f5002c141c0e07846081e840300d4114460345601942010038a0010310f4101c90406011a0000301d8801c0400d0510600f0f94550008403402e4484040045d002c9180d44000c60a0002c4490b1614140005004102c0a042c00088172014805908140c4000744110311080c0440d01c580b201c80760410020300720403106481d81c5c40d00c5011038900810fa06103d030100c0c0c0d49a400002c4d081196484880f960250190180a074ac5004a17404580c08000c0c080b10104900140c0d50781405070103940b401404660 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 694589460 1250 694588210 694588229
    0x3100e1303180e160302040e01030606030519080415020c031b0f010c170310030c0b09090606070b071409060301081e0604050327060a2a11090705040f031b 68
    0xa20068003c000820303000810103003156010f01c903041c4240e0080c840c0b40c000105620b0f14800000811085810000950b440b840c00d865081a000c1038a203003784907900d0003070101d070050100344104001c154041c1106001031049401c0d800380080440e00780109000c803520300410383d008071509810310743c0402441da01d00f868152280c6000f9110381022101ea602c02004002000010543d0042c820510034055a001000d0040c03103680d501007950182d112401043c011070070140012411700c1c08038151801203400c190103002ca0307035503003e04864124076488101c14821043c046900d01d5142d800140d800382400c0001002e00c280c1820214020f44107164640100d9804503003004000356000c03099038800d607a50201900c1407014030380c000c1004542d1583c0a03400080100301004d0550340103088040d115600006210540c002e605940d0072110080d00150482e80d14201000c02c07400c3c00070180380e0010304e62501c20704098840170f9a0102001c50783c41507a400d28142c010b040800514070821004104682c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 694590710 1250 694589460 694589507
    0x1206010f031b0908120c33070207090c03060513270b0901050a0b0a090b010c0b0a0203101e0e0408071202060f0a020a08010302010f02010e01020310061d0105040b03100e1303 76
    0x948440e9100c9801c203060b07c194041d1040d4040d10705202215060404442020150b98548200300a580e1102d520640c4081d9044c4614070310050701078403d05040d00d2018010b25a448600c403004001782240d00900391f86601580c090300294007080e4035007910188510340e19140c1e8240250382d01d0035581c2c05498000c20360b1812045130120b6a514030004212010700c8400314003c1044c80040c2d07680c5281c490040d188555081c100190403800b035005521a50381fa0b01c0c1100e02a0300c50b400d03002c0c5030240e000e10383d04280e020b01052118195002c0a60f030302038400c0705040e18046040e695035008900324126100940d0140d01030200d9208004a040d510000c207000860401132843c100405d00c00041c4406410311011a0606000070720030f40040c00c0d0b6540810082d507403820546000c0080001d144a22030006071849400283d00e520099a041c21507016580da0f0300b41030512201308010343c80603200a00d640e06030700000494154040c1868810801e52603010700301e41203400d000e000c0442087c14214481d4095 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 694591960 1250 694590710 694590727
    0x507021f09140c0906130603150e061e010b0c0c0604080c0307170d0818070320040203010b09010e19030309090b09090d08180106031104111206010f031b090812 70
    0x40c844e5a034800d03000c0360100d20000355551410300811482d0409040164051403001080020743c00c0082141500c1d03045800301d95840904042e20107038811400075081491004010081d041d00c0645604a10502a02e0300a625000007605642c0b040d841f414084e0040502c40b400f40c502804400002c181c058030400001d1603880e011500d810010300c0342000c1c44030601c04030f1281c4110078085402d43e4241002c861030b00341c590070021101c444084c0c2200c1b0047c035402212240d0300b03240c000e690407258a00856400c0169400040d1207003900a100c0365004620496800d0380c0c403c2820800d401580642c4680748000c0c2803141d000d05503282404614000c505000034412911000928000038150b50304e019150b03601e400401c400d0780c0f18092200310b03081d030802e040030051048100c4803000c68202124200a41c0c130710780080030b4039409030f00308140308900741a0001d0072650080071080600e44051030b0000b844060039004502d525450550180006c40701041440074080c10007008085a400d09101403c1c03c518 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 694593210 1250 694591960 694591969
    0x3060e071a04060c0c050414090c1c020f010c051501061b020907030504060609090c090c0201050105030d0f14030a020a0905030304180207081306021506220507021f09140c 75
    0x241d10501007007100c60b141340b40c14450840400380141c4070041c014001400d0038105001c0260043e650030416018001080f1543d1400404569203499036810f000186a80e076000c01c1005031200748090306102560f8240c0000440600105001012242d901c910319414139600810342102c0e011200803294034155001d016035501c42175190b00c6403640c6404211641c0341c1c80c00801502d6603522081c0c1050828008070304018114407400203a0f01c00030400c200d080300200c001ca00b40e0700c0030f100362900340c0c0081204542092003a08034020041160510513039022044003040300c1d6900032210349403210b601103851444250f0168030f0100400f012001075091605100c02144c03000500d1105444d0380f540064100d040244030f8007030301c08041030f400c0c045041d180c2d6402e000c3c0d00e850000e01c3c2203141000220008100d860079801c08030b400c2482c00d0000380e0000d11900b408004040207000070081d482185034040400c240c40030404500481c016021071401014640035004048459091100d80c02064418005854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 694594460 1250 694593210 694593217
    0x3010308030c09030109080a02150f0f040818090a0606021c0212091309050115090c020601060e0319111e1c1704060905090f07080f07020c0a03060e071a 67
    0x10b0301800c03503a0760401c04000a0040034020740003000c0807008201c240c0900c1e0041070141e00e0041440c0b4049e04c87e51103502080380d00c1400c44a804402c12000041004110b40d500540420003108084419801500d400111031020841d0410032403920750700e00b44201541846907121528203010b00c400f0000780180081c0d2551245120840c00100125120032542e6400000f61520300604a0421172200e032800e10901810303a019161030f5100c1c20080c00101d160306846201110342042d030152006134200001110300840b901d40203603240c800d903020001c1d002e40004041101520940307000003800c440398180840d1200180441003042714400e2030801c0f5440e4030710701d0a070481021100142c580810b1070009440100791840303110000011901103542900601c0c1c26044d19001c8030109029610140100e0074002c0403102440003408800c04158880801038180c2c5d000701c0c25005440c01409914003080702800c46072300544070700341c81d83c0714100c03a00c40920004002d401540c1502c0d014810040c1000200e10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 694595710 1250 694594460 694594471
    0x61106131e081201050f0a15050306060d02030a0606030e211b0f0d031802030c01110309150d0f0606024803010b01090609090b1201020a120b03030301030803 69
    0x203240720031000d900a218000d2401c0e2950103000241ca600a400c250300e882c400900549000c3c0c1103a08008040e8603180040c20304554100b424411085440002100d00d80c00140c0010340080003448070407040c80250010310b1041d040010001110b510b00702e0300409461a402c2d00e207601d40c02415010780b8001103079289142c10603840c000a640c0f50161403a80040c41c420b48035444041c000c182c0c5454204001041602010760a56414400711540503902015402d44c550002c4d45a8054120681d40b54040c1c0f0751101c0d02c1c009641924103104090010804580307900300418820400050500581c0d1094454403401f2101201d0400c20031b414008069628a0b0b081481c0c001a44084c00311000c0d030400408191080040b00e40d090022007002c402e02c0d8441d0401042c5511a50034060101e406502c00c00501007120046e030b4888850078601001e03007005001c80080c0c6500080300c1c0c1c0300351417100000d00003040924010b555150784c402c59022280e045503a14000b86100c0c1d00208010404030b603c000c00c0c0da8204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 694596960 1250 694595710 694595723
    0x10e1302090c070203030a090e07090e150310060b120109090f241404120819150b030103030504030203070b040e041101030905060c0307030b0102120d0213031a0106110613 75
    0x42e00c1d2551200040e02840380c000b54148800600719034540e50090301d840c215070400c5220324441d150000266004040e500032100340e00c041500280000031201c092105104000c1e05442c0c004843c02d0404043d0b50468020b10300744100000d00306e42032540c1054031070041c4040103007040b20407680d13590461115400d0802401950b664216aa07041440040d444071059200748100180a0000d00c03035104584200c0b41620300342c0304034011088503070003419590701c80c40c1012403400748011074000280040141054400c074600000001240e003c2e00ca10095001c1d5002c2e4071480d807154176501c101498080260440c1c0d8001030240020805aa00d80c0141508254400c02100001d800744004134010004804c0c0074056100c0c0c1c1c0309002d50000110010f40c00350102d80e40600400480f00016640d90704070091500c01c0c2041045800400c1000394080e201c7e0b500101c00590082e6500d0315504a0030f00c040d980e0001c0c580303012004014198215130210724800d84080680a01d00c0d25544ea83c40b020303e034a10180c2007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 694598210 1250 694596960 694596979
    0x10b0a120f0f1e03030603020117100605130b0f0c010617030327010c080604052206020f090a06020d02010507030b0f04320916030215160c0b03090105010e1302 70
    0x10003c54405003041c009181081040c21400e90400601821451201340d012030381c410320f0010031541b00e82605119040400d11808001c0ca080d4040707509510980b80060f2004c020700c8003003180324400004001032100c0010580e104d840581e540360851f0b00075072046644c44420104041780e08004002d8940c8181c1e200841000b4541c1444901707100e1141c010360802c4c42d441e007011000826045a2128040e220030b58041049503900c40070481d9400079083c80302501e040711503214000811a0300100248003903c884a4240400030f808154991110f800c4000560002180b1000c456030900c1070517070040013460140a21402c0d100840c09040303840c4030041c019602d030300c0e0a090700d41002000f542d1418101081c4178131400341d02400c2c1403144058584410034083c182210f01e12581c80143d80d015250000c0c10940b00d0144907404254075400900c0c00e00200313820f40e0081c4045140d45002100410b00c85014603503901d0500b03080c5007181c1d0140c00680d0034248002c2444880b0b101190250001a41078600a04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 694599460 1250 694598210 694598213
    0xf191403030d020309060a0f0c020c0427050a12021f020717130315050f0c070501060b0a030c0e040908090609031204170f06190c050912010b0a120f0f 66
    0x65100b88070164072050b0001043c8481d800300021400d1140300c6801040250b2100c015080081d140300340030841c0160b000600300308003131801d64000282010214100f414240c100c031050703040001c1000041e5030b2034100185030024070000010200d250300d00c4c0e101801030402c1e041501c004e11407a10f10386c050107503404580b00303041014007468031040e240c100400944441d04803601c0e201d038143c0c501080319128400040403a40455902500d4014041c00004084560b2075122203000c640110006817100d640b10b4000007007100029005100c000ca00d91340c003240505401c0e00141c440c9a800c0c1c446406540362942101c08910b0303107030541d440c00c882114826500c40400b00028603042015082c080d400788000741c001a07110004503103c20f00ca10801c19034641314002c8614076102d407011a170303a00c6502c1d00404608125402c03540840b11085503410000d052032a5039010070300a00070700c0400300305032f0366541e00c601403031819500800c001c3c100445102071204c0596a09a074102580707000510001400398040d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 694600710 1250 694599460 694599463
    0x19020a0b160507090608071d04060509030706090b0703062301120b0307150f0c170304020a0305010515010219170c0715050712051602090903090a08010b0f191403 71
    0x1000c0c1c010b4110340003240c81d0b20b041d200070945072159000e58400c807000080c400a1180c2440d40d2540101c80e042e006545070707145d680290000408038012400704118020024400e1f219000405000e5840c1550070314081e00003070304a800302d0300071800c04034001c5000d10034114460350b001c201203802e107060b23050700c10345030850001707003412020ba9941130040001c0400e11521011a001c8010503d940e55007150500310410389405900c104003900c2480e842d4034207a1003424403401580c1240c4041c1080b0f030701540d245c03920b5003141c2d002e4415000b01c060a03042c02d2943d6074100015421180003450b10070300726030f20787ea810b4101ca200d04451b0030200d201280058100c0401c0c441030004281d0008521402c0b5070240c8000c103d036000c850704030744404d4103039a050074892040c1c095079000c2000030364203130315030450703408200e103003030005012103403500c41040801c07800c2c3c449000d0705006110400001c902510084200500c0f108002e003443d0180c89070302103200c0c52520b0501110121280c0b018000511682d03200030a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 694601960 1250 694600710 694600747
    0x406120513061515020c0a0b090a0909150f05060301050109052404061511010e16062f01020403032c01080c04260c0109030b0105060912010507030203040519020a0b 72
    0x10028100c402c4110244e0740204140e10388100c100d96618846440d1003100d00340e0700031644004d8101c0ca0b1040d09201c44a040c0d0300440409004800444091100080031000d0302c0782840400a45074442090150070708090145d80d01408805900303202a00c0d211140300100c1d0418203d500c0034034000f40d11032100c0c1c1c481c2c0d8444000307082001d0140c04c0d12400600040c22a0161800c2070056620b444c495441c0e1400c08a500c00e409a0042c030fa003060545004800c40d00c0c01911416404c000e00c901100c3c4590450552451281e4504500050b80322071560a010b00244002120752240701808007803070603411406128035481100900784803807a0380f14000c5440c9a03003da500080341103440440f001180e40708561040c040d0807031290442d100b4038070100c011203410300584030040400c0440b4005005501d41071000d041c15500140c54080501c03000c1c0308a0742954010707203420021940c00018441030003014030000300341e4012002006543c10550303000c511800d00c1c41c414a00013610220700441c0703492002014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 694603210 1250 694601960 694601969
    0x8040302060301031a0708100303110c130f150e06210303040503040e1806010905181b0a0506030f010905040809060d0b12010e3d0204061205130615 65
    0x90703626503031603260a100c0e8000d01003030009190045000a9001403080340201c1c45650140d40c00c021251459405941003130300041e860b0b01c240500d100b102607945a00100440d02c0c540c4240c00b1403020000c29101c0202c1d032107605008010b600100040c003500440d8203104e900f024050b111080500703000d00551540a50100300b034001c40c0000000d02007401800030144c01079607040e8480b0700701c03030f00c0e2113114100040034015032074225001040100440d81c3c0340d510007948101540340a40d5a41682c902883c201002210050f000507080c0318105441d040002d400005800280c0b0618a10708000c0350000c16241c05205001074551a0320018080104d010141c8819139005040c045d111800c10401c2c40c0948030400026000d00381002c00800740d40d0701405481c042d580d0f00c401400d00c008003030b1984445c113140ca0800d5078061440440f004a995000185050b1320b0201d2200180ca8a003071160050001202d04813544040c0d00f0a41030102d04200c4420079105180d0000c0000340319080c20202408521442c0d11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 694604316 1106 694603210 694603219
    0x60103090201360602060907051c0f060b06040b0c100b06090108101502060a0c020106031a060109080d0903050111040f052101051003110f03061308040302 68
    0x10032240f010700da1043c003aa24650300a06009006940020010f0340000c00b007007a90718040c402c0c800030f407000b20340d200c4000d00c0a41c60075030040800f040151040210745c0780b40c2c0c20003045901161001c04041c1290740c445645030280320311034000400c007032103600500380c0784501026107100e0382c07560680084c002e908204c079640c011030352410001c0101e8000050031801003414011100545e00790b60455005111902c0c10100300740c00c0d140c440c035481d410341e8101001400001d80044a850000c101002030702810b5a41500481d103029190b400705489000d401e0007220384660008811040d6401007000348410580145822610f00c0707584038500030f28244400601c021714120b0302001e0076a0300c000d08080e81c8201982c66500b1514242d480031040d09502004100f00101c030301e4180c412100c01c03144421990f01c0d070342c007083c4c58007002031405520050a42e0440e0801200c403055802840d005071 = true := by decide +kernel

theorem cover : BRFrame.Cov 694424460 694604316 := by
  have h0 := BRFrame.cov_init 694424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 694424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 694424460 ≤ n) (h2 : n < 694604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
