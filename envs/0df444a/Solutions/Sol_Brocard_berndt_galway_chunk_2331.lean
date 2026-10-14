-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2331
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:23:21.812859+00:00
-- url     : https://prove2.me/submissions/f498fa28-ab41-421f-8cac-e96b53a43626

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 419064748 ≤ n < 419244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 419065998 1250 419064748 419064781
    0x8210f040815010302040b0402070f030315050a0e01030c082a0f0402120402030f0309060f03040c030503071b090908160503040f0e04050c040902060d0b030c041a1e01020d08 76
    0x70940c86520704002e01c0c4851030705440d048030300a84041000548007003d1105921614101409001841c002100024403c0c2d0020840f5050348816a011940310000903005071084c1e07100c0700e0000032240061040c8480c4020780c030f0003014500003c0c104801c80103184202590094903070062500d8000701c845440d16245d2070b0115600004008540d948100c100041c01e0200c04d54099010740f190210b15005214000200d4201d0840248800c0c00c24040c80c1900c1c0f121f070f00050003180e60103c9200d0000024030100084c102c4a40314034554102080d040044000342a815481701401e1820a110500442d140c031003210300c2c06195103c002500040c5007402d600e14456527214085000286500103041601c1d0b0200b43d01907442802900d0311803011808000c1a031b00d040f80083d60046041000d0601001036a0090040030780c054145c942c400850400501140c0400303819803d41c28000080f00340070b02c0c10f5180444050071a510003805d0310b04040000f5500c8040303800d1001480029408904034011805060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 419067248 1250 419065998 419066009
    0xf0a0c0605031b03070c050c03063102060309030a030e0d140a030e101a090f06090a090b0f010302040b03150a0b01051309091a1303080606070f0b01080708210f04 71
    0x50398a040c010310046c51000305000650b9140210b001c1c1c0b103094900420018080c2c2814001c05520b118a8000e00142440c1c403c0b40c040602280302d4880c005031900300295102d0740c19240074607181c9611002c00b40503103203140207090329a0441010041d086407c41a0300c090700c4c14040c803031a10340c0031250050f0001e2005108041e514440d550a1109400198014400701500c007210000161230360000e001c41502c0545043c0d03409407181c0300207450390600c0c1c4503460b400054941c01048408050b15509448103040d911920010b84100c01402503081c6401040781c007074402c0d401020041991a0300b40c5008001420b003012658541442c0e440c3d0380e00c01c805442c1c03400c9041d030198010980e24240d0f00005c6c58840f40407246e0203400a04180c6070302000718441e00c1035156103050103129600703950444a00c440200400e0b4811400d07c1103d0100d42c0c8503250010007807090105107005e50408050324941055580603d11a5000000d080c0d065640189030030300d0801d036501c00c04d844002810300d49041303002d40d4101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 419068498 1250 419067248 419067301
    0x1b07080d060e0117160501110715030b0a06020a0b0a0203070c0b090a0b0708010f050609060409020c0619020918040201091205100b060f190311070503030103050f0a0c060503 76
    0x4a000a6007010b210b0484920703a02c50001110225800d80d110140e1032a41c0340000038143c0d0411403940180c3e0311140c400305e21025600042d460395051a4182c000311070001c0001da6135500040241051003040001d88284d00042015030f20070b544960381220003c2c0000d00568001c404100c2d114081e0015200c20396110380d80d041189040c581e048c0d580d90000710165414801e0314045a000c5c0e01130304080341660345960a03448082c2c2480b050058550191070a02c0c0c104404100005902d601880a419200e45800c0035200a0400c8160002078071035400b840303410548108a01403c9a031645441c2190701c129415842003a940d500050f100003c0661281c84800ba514007140c00b017081c040b070204160900c00e0010086440f0728800d100e624090031020f0540e81008102c0101c46502240e00348144a00d58a00400c0541c401201c90300a0740084504941aa1000c030041c0304000060000c1611044030400a01211242d92150199075149200c1c000502500002007042018403071141d0018002c031044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 419069748 1250 419068498 419068511
    0x23010e12031b03040f091a1909021309050103030e0f031902041508010203070f0311090d11150a0f1d090f041547040b0d0209130b0f1b07080d 62
    0x1001b01404a12135480648868180d5000903444c095905451003030210b42d651034441d0801b080c02e402548802594001d1900708030f00084c50078000e02270103010710f209070394660710400e800007400692a60121094071079008050714040103900c030212444040d40403900400c103000d901403c00d100404c0e9800114007540000104202d01d034101c080083d802c42d8540c1c00b00703c0f010403144003415a0044000c01944460b8010420700421001c203000186117000410800c0300e4440d0343c0011809034800540c801c0421107010070240840c2c0c0111100000c1c1e10707103a003034900010280c0001441301030700800c24980310b669080800c00f40700d52402034060700701e0b000c44d0030040301c03d00c80c10101d2009020003041300d543c840407411079078204901d03450039181030050203900e0600e01c803003013001301921400c07030001d800c680144c0304800541c3c2e449008500414900125603144405400c0010f0481e000612801c070240425003400034085105140802941c060700045441f80c1d19842c2a41c50740c0b02d41c03000c00c002c090030000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 419070998 1250 419069748 419069759
    0x90423040f0c0b090609100216060809010f05041a090a060203010b030604050a0b010f210518010c0c0c060804030e040504060e0d0c11060307020723010e12031b03040f 73
    0x205441070382401901441d030940c0c0d944014a22a01c0388211140d0019000c0c010900e40c0d003019512075049031140c0c0141e5600c907070304542c0e1892103d1507a0201000034061800d000c0c20b81028824082c0f00044100f06100524054171007290201544e07041e0700010404c80002903000a0501400a50541c40134041d0360700e5a607000c0e0200b541e0000d807040780c03180b8549000300d640d02d40702c3d03c40c030610280c068603a14800da010b0b00080e101a074a811090340220101540044000f4003413080d940304082050503503120b04a60b018035400c5405a000c104180110080c080d0040381c0001c902c2000c80d040352500386103544e82c624003110100480781200f0b8100341800140300401c801500400040a00c2d601103400d0001010000c41380301c02e00c4a00940b4101c0030400c05c01e403900b0b007880119800301d4180111910f8554940d12500740d00d40c04140c074941c1401240880c0410f42e845100c125011800302c82c481c1003008218091522846001c50400c1c2c004c0c0000c00c2d100d69401c0920550303004010600c0408056a03841 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 419072248 1250 419070998 419071013
    0x81803100b011b0b040f210302030a11120411010c1e200a060503060d0b091506091009050901090204020a0504061b170c0f0105070c051e0309042304 65
    0x307150208010008002c24541d00b10307145030f0225000b10381e0070b145442d1501e0b911240d002c201010b031070201603024050b02e0148103d4440a01c002103940051f940c2c81d100c0c04c22000c491031014140010709080007600d2030f8103042898690495000803000000e411050b005030f501e90218a0000d21400042c0312407143c007290742401a43c414010b0044000c000c0060307030540c1d1403c2d0400d5110398000d5108209001880c03240f80a9540320001070803a0400e403c5640724000c0703650b4201e0790075401d0b0307001c18000504071081400c076582151301650000020300b0043c0d90080311884a000e401042555080000c02d40442504818101e1b900030b80115958202d0030002170140c0c0c4036000341c00104484003840c0c4141e6840c80e0040313200d1500f02802d440e07415440030300988113621202c50300109200b60010018100c0080c4a40342c0110091789035180c110a00385029402c210303810958100401c02c181501e840014040700312111810110340010b01262801244140c4001101006420050701c42c204410031040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 419073498 1250 419072248 419072261
    0x90109020a021506150702030123011a031e07050d0501061112090d0609140d03020d05090a0b04030f030e1203060102011103070c03050304171210050301090b010308180310 75
    0xb942520401608400100f0030740106039507840d00725142d54031340b41071243d040300a0034420780300130000301d0981c8840d082982c82c0c2c415801c1c1103d041f4409030040100c035026004150141001039407840c11883d000b224100c41d1030890341e4000c0841c6400f40001c1082d40b00e10221920b54030540801c200c1d650b100e000c000d1062a100e40110406d2259204450f0096644002d94451800040040c0c0d05070301c00d591950080d06010340c00b122080103c2c01600041c01003400400d0814219a5006884280e0440300c40d0135942d0217032400485803c40a120300203d081182000e40c4145c050406250b10202510224000c00407004017070940d02905603038444803131164008502a61090b402404018401010b42c411840306884807008517228122010009000e440038640c014081c400c0ca803411542d10340c0380041a1700c00484904450640300420810000080f06980035220980c020400c200456488408204040c080a02804004a614110602d610900034403121001d01503451440078100440f014200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 419074748 1250 419073498 419073517
    0xf16090806090f07050607051c030b060c0607030605040504080306090403020313031b083405040618050f07050901030b03101517060621010e0313030b01050904020d080c0c09010902 79
    0x203130b0a800602071900340d051b55070042e00718000d0f02d07070101c401c031083c007a0380c0421507107406043d11400041c40a80d01c0d40302505400d080c18000d0403039454880001400c4900a4004031310035403500090002041030304054a5001005039402c034035944603810140c1c40c0d401114159680307080191404020441c84803c640141d983c4c0f40000048179071030304a05038a5a18555041d400c8400004d0780c61200140d060041000914541c5503c82e09500c0b0b80110341a242d268015005020482c08043c60503283c510405500c100d46c181ca5444c1d60a0007880100184038140240f810103803212100f0752a0f030b40502281e60222003803601005652040b0290b105101e00503c40c05170500d848904050280d02c001c00c0147c8235210043c82c1c513140048154011031540ca206161000c80e641ea500c461030300c20020001041c0b503e92683c540c00055182d441c008001d56016040680034108440a000050f241c0070a012140c943c0090055110801c0359152031409540c075181d0f6500c40f00d600000207100440f42c0c0240420704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 419075998 1250 419074748 419074753
    0x91401060e0c03040506070813150204170705060d02071509030c0302060705070308010303120e0d02010519230c0d060b070209070f020703030f0509042a080f16090806090f 75
    0x41e1442e210703000714041200c01030029000280094400c0341304113441540561000d42e40c059003511602c549541c106522402c0060b1b5600250912a0058511a51402d2818140146001c9040c680403442c507004000201507040e401040c4d407010040d0111802c00300300303101c9408000c2424170b810000c1c2aa40300355025000341c041c1c41c002c207280ba4420000ca81c031481e0140c56000843c0d107103a5040f80c10048203106a151250360f54008402c1071004d2110318441070b442e80c0003250a00b4050b2680001d4030b004608031120515046152103a5001101055407030079140120140c0c1e9550242c4580e018482c05ca615a180c500c0d103000415400002d801800e80c15009031100c00c010799800505aa0900c9214540070140e07002036010800240304d4504d5142c0700841e413030041d040c05c4003400802d06440800c8840d408078110030840b180317441d17007000c00441041404d01e001030aa0800804860041da40600940c1c01c40e411404074103c5540500c002d18018600e1204455452604684d80d83d00ea1503521000100d50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 419077248 1250 419075998 419076001
    0x140d090204181a07200a14070612050912041814190b032d0f030306100e030c09011202040e03030108330403020d030e0d05070206090103091401060e 65
    0x990800c0c2282d000c85600600d2404211986540fa2211943c000c11103400c00060101c60380d11690b908200040354850a0700900c0c203c150b6141181c03084484c50320b00c00c2c0f1980b10480c2003148960000d90000c4251000d4400152911218105403c00c042c7c00d00b42070212400140000d17012110a014030000d10000208100d0400c00c01c5803100320030025a5103000350004112015850800c0c0d900140031140001e080381e610040382d03200c0740410386404c45201003906000d00440c60090080c0403003c401500304c0091451454035000141080c914050100100200540c0030342203070b1801c00c901e070079404005149104640c0d61701c50034220840d00f500128041c50406505013286000042030b80d0603580100040d1014040e41141c450002ca0309130303c400c12088222030038860030300102000d28015400391340030303140200c40080702806554900250182035442010301100c1075902c08269244154122200c079030b0741000b100100d015040082c00a00700d4403161050411a000542c400012204290000b044a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 419078498 1250 419077248 419077271
    0x30c0301240c120309060f02090405061008010e04031202030c0d0b010201051b0c070509070806010f0c020f01080405011508011505180121050312150613090c140d090204 74
    0x91001c0a1500c0100c1c64410b8464001540d481d03810f82c820402e0710740010244519103a442c00c0c0c90034084c0003600d141d030008400f0703001d003040c0c0075a80e071240d0161100c03180302c91090b000070704500051003518111480b440104d004c06200f900c1a0701c140e400403100b52b4503810888100300c0700d58031a6171072517190340c03400e106d0346544e500600505100b82000319038905100044540f00080b60300c0030b410708032203014112001c03070280d98042e003060142c04182d940040c00c0c03422400141900d003081440c2820700c4003407044036005984581120318030050030300e00040252154034015001d4406070006080c0c40c20a14004907000c60150700c800b400146000d40601117558403001e200185100e8003905805070041c03801800f130344841000c0b03040200501c001984140712103032540c90640d0407020501c0500300450083c003550102d1240078695445003220500e2030885d407915030807440c05551150603c1203071105060a100c0b40108080c0c0d03c188150490907603103684a402c220000d110004040f88543d2510000c08203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 419079748 1250 419078498 419078549
    0xd2f09130b060603060a080f060403031103100311060c1b100f14070f12170115050d0507020f0a061401090b0d03120204030c0b190e1008040c0506030c0301 68
    0xc80326005910081251101d10a002031680001d003143e03040820321800040300705082018040c20104400070f050582000d1400400780c40d080c0c0314000c040e1106205100c208140000c024045070390140200420b1005d901c0880d040e4005c0c481c44503410b0040c20b2417806101c02ca00085003118004480c040400c0e903c1c01c4040d1600030300f10400310000f4200b0394003510035041907402020303518011401c500e644826075036103c41d410b0310781d070304240001c0901c0c01c0a0f134520a0000d0490250801d00890807400064001c000c0c200d0090592800109032071300d020840c058000c0c450003103000c2141081d580c5018660030108060310802015000100351903000261800a901c00d506a0300401032601d4501140d07500d00710345c46501c10301032a021650070080040041c240c14401002002c0035111203403a40d18000200820b9900d200000d410b118411400f44c150385c0e69040ca0390754206c0c540c20504041c1c1c981b800d0000030442d4075040250444000400d00c480c00039010040c50483d904515100340b55114243d0051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 419080998 1250 419079748 419079781
    0x1203030b0a123011010b03070e07030203040219151d0102150903090303030106090302010e100516030201020c1209090c13030b06010519180f030b0103020d2f09 70
    0x6004111030164400510024400900210303a4101c44200f500e2030103003c018800355040c88404602d0341140708400c2c1c0c40071702407910850f4040b805801021b203002c05401030120000c042c0c50070158008006011950b50a85010180c0c0404968401d650384500200884104404180340030590160310705010b5100c003180241c941c20103178080d240d48040216460103201c005015a0060700040c0665400c13074504101030740c002c00c120f544520710145180005000c01d0140503c481c005d0392224140300c1d5a03034120048401000324910710080c9403c07941012802801022480d10240c020380f184524010030b540c000c4c150a56007103550b44002c1d210740320440752510908200840286080c48104080781c0c01039603ca901c05010f040141c5000c01c01c503400d0900000134004200132901d0901f800d190300c0181c2032800040c1c81008000450341e4119200c076100040c0501c0000d100e2440c1e0080007081280c003d00c2c1d10b081e01248040d80c41130301114503c100d500602a226940240712250025401000000414 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 419082248 1250 419080998 419081009
    0x2604050414130305090621060a080c15090301140a0f1d0c04020d0e030c28020105091003140c0a03290405070e06070510050105041e0b0411041203030b0a 67
    0x7a000c41c000e43d0f0503a104e4010340c500d15030185060081d074500d2224010b410450110301c10215007649401410006203c60760340101d200c41d4000600300761940c6a11000052a140e20130450751a1203032a4002400b4100c034055400d0040604411f004007580140c20001c050b03132002606020140b441e501c0c0000000e41d884240c80507512540c21541b160030968002c3c0ba112000c907901243c0c41209030315051559000241e000e480d68070546524403115803144400342c0100c0301052050044059800080941c014220298810551070220362912340c000c1e030040500002400010f425460f01144014807a000070540c103020038101940c00803000c511880740010404c15100310011105000c0c03d01c0b005001c02804c010500c030b0700b41400002c5651762400352100030310070310080c45000f400c2c590440c10340740103a0209000307a040a401d150415110400c0d0380da03001554200003850492034000030050550010300345002100040c0c00701d29502d080c000c18034860300a4406000310f82003981485034810091045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 419083498 1250 419082248 419082271
    0x26041a0c070e2a0f310b0706050a0b0a080703060f14040b04050f1b0f0f0303040b0f04030c0611010515030c01030b040f0609090302060a050c162604050414 68
    0x34415022070f10582542162498212810449554003c00040d803021600303036050540103481400400c00381c1440315200c6172014018001d1880e1004030641c9000710b44000784216140c0001030a80c3e6080c0c0d008030103900c4000d240602a0b5507408141380c41c0d08150009880c2d55050030051803655882e400354039248400c0b0246548075076502c0e103800e000d40c00003400494103401001a4030b880aa41003240c40c0502c520320859203071084241e0100141d8a801c06c2030785004100355810005565400f10035a401ca079800003546964585180340c0503414811500010139240d1100c00111307805511946109240c40c0c000001c11490302c07560b80d95a01d101520320400d6065000080c040c041354403a4206000b007100c06400480d001e103c0500c410203558030341d000f101203903603a0ba5060050590402489410a0380e40c8010801e40c180304148000d035101c2c07044900101d41c00305805004002c200d0309071421503501c40f140111074003003202454804c0e500620405100740d081c00c03400041030103540d05250144107000131 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 419084748 1250 419083498 419083531
    0x130602030301150c02040207020a170c0306090307030810080a03050a080c03061f0306091d0715050d0c09050d1101080106110c19030b010f08100926041a0c070e 70
    0x20101d40d241d030a000c4c126040341d024040300c0016200c0ca021100944071010700044412142c00d40a46412405020a0320a81c800000c1c8000203c0100464440d0358151400705030958a01c3c0010013020b00c5540720122601c240c1c05020240b43d070010141c0701000c80750f078810340f8030b84820811002d58001520f006520010410220022254908805c0040d10f42810041040c41d0744075414421900c001e2400a800c6080a00141008000344240c4018090304003044001890414005200d0b010b0b4455498407180c0d1040d818a14a0040740040010107004007003200c5807104d80780c8103104106c2d64034501d000c58a01400031810501030201410f07943c3d05078000f04483d504407002c1000050700c103514a42c4104c0c500c5004030108240c2401d19020700001110070140d40e192090941c58000840b0140c0840c515145414000907614202001006c1080f0f600303c4006131594030352402c038461540070500c3e207402c551326450103045000c00b501c01d0081d06001d56054503510a070403580d442044620707100c810038611 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 419085998 1250 419084748 419084789
    0x210f150406050102100c2001200703050712030902090a14150102030a0503100504021b12180f150307111911010c14010501060923090a0b01050c0a08130602030301 71
    0x34000d04403a0460714014081f84498544140401803000300014542d4481c5a50000031010404564183c03034041d181501d0f004d45a01d0050490040d190001c3c5010300c4031421500c1030740729800c0280c03d5a0002c01403516400c110b100b401c003d00f49003509995080c410701c00180e00140380100030203100342c180c02540c60502d401c90b08888a40c0002d00340c2458400c084800b25039619144080c01d4000040b2101c0000c0b44440030b045440c0500190705020149070030029001030300100c00c00c00283c03090a07100e03005045903c10000340c49006911068054040110030460155801208958680910303419545600d40307501c0c420868641680c03000c1c01383d0001828821055105510580c03620303001c0c08101e400007514660309829140c0a070302c4100051141d103000e000041d030246030014a000a0f10821b040070300d9030700103d096004000c00340b0304000e03900c000c503000a034064011140d0001c00141550001011450402d003076800c040c00c030241c001e81c41c0002242071400041224107035001480c2c000701c440c0c3e480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 419087248 1250 419085998 419086001
    0x105030c04020d18031106090f070303030506030309090f01050103140402181b04062001140a0c09082b0207120f020402120a0504150903050906210f15040605010210 72
    0x145660f600d40e035a582444690201074400b405080e4403036a204c4607100ca80742c08140c940100904051500c3e08a00340d1002e1000000422400312541400c01141036610040000d0a5000e400400c0ba0403002035420040090200c2d58002d0690380241c804020600400307800c045004000c0350025000038540d5003076000300c2e13100340d07030107a101e02460000c00c402c21107034103826803e421a40c07100c1e000c2040b1981000045944070108800941c0000c020403580c070280d500e82c503840d04041c00d0002d40076900c00c00c4c485c0161091102d40054540c11013110000404000103800000a014004d8003040317007044540c4801344042541e03002c0740c2000b4001045000c0d61388803040c0b042c001c0798040740d125900b003054002c3c1d03000062070b241c0f0420b540c2000240c503143ca4241418260070706520603040f00d1600e13030000300081e042001d650b02606c00790b43c85901c0d03160701480c1c0c01e45282240220362640d2a00010400b02c03141901e1024441e4042c0321070f0700410340c010300c18031040d84d6139405030341d02582218800c0401c68825 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 419088498 1250 419087248 419087257
    0xc03060614070503091201090b281a06160b010b092202160b07080a0203012306090604080a0c090c080705091f020f06011d070c03030204080303070815090105030c0402 73
    0x88059900d03040c44030b4001b4038006d200790100e0a080e51144070160034840481c8144c0d0b03001d08100710b48044c1c03040b445540c1040d91007200e20322a001c1c3d41e4010818001760741c00044810780c5c0000d000c0c1603980d10340c1210450420401481121001441c4001245400590b070a07a50081805050080d03d1150f900b0f144101c0c03a8000120300e4401c1e400e0043c0080340c0d422100e5009614000c54003501c4500304240300030100c07400140380c208510b00420041110170b410042540c00e40785020b00d42c50a84a0190002e0071620500340180e510040c00300e004034003007001261400d2660b200b4440b0000342a41c9005003001d8445010150780416441030000d001d841c0550f00900c14070b54018155480005000c103000428010100a080141d0000c0b00c1050842410098640905052502c28406a20a6034a0300780d441c0001c140780b0400c500c43c01100209802038064134042c10903042501c1c0c480c5080e4100070104a003c030341811503402c40e55510300303190401102c002d050703c40c003402401558100b5802d11010350722 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 419089748 1250 419088498 419088503
    0xc0607080f1e03010611151605040b0a0809100605030706260c030a0f05010305071707090c0e18060901051c0602040b030907150918060509190c0306061407 68
    0x1c10840d180d200c0c0c0c02d40c0e01c01210403a0a840503516541000d500402480c6c1070803001c1015800381801100400f01c141140741e0001408090016031844104101c900713001d01d60080c024007201180c80c0c0440f42d001072215104100080441e140314411646034408c0e00c42502c00c241d01038000c2001484030070300c201c580311150034002d0314020308640c81144588011000312103e90080c0f0010060140c4903006016540d41c5801140c41802603505544609450300782074030820500d5550907500c052080e00500c4040001d0108074804c00c080015040081e00006a0b4416603100d00c44c14440112150440d001c0b0500503000138040e041541e007410300713016151940140c20070341c01c06a5081800051020b00007480a080a0559a0f40302e080401880e40f9040d2290000003840234400503d102c07060f07002d11082d0407940c041002e1500c904102c0103640c0109004e800c1150010507a0042124031407500305100350818001d102004404112a411402c58006000d65000903101d10388240e16810018050001c00e030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 419090998 1250 419089748 419089777
    0x114040c08390130060b0715021b06041a100806070804050c0a08100f0b01050f0a05091804120207150c15050f04110105030c1b070f0602010905010e0c060708 69
    0x42c40c9503821040c2d0043c0c1d480703030303103090403000e804d031180e1612030042100038001d9441c403506002c883d0b07a07000400a92a0041501e540d40461218050800056440700c0d010303000b000e550316030030141880c0340b40d003442618000c4031070501d0003c030320700d015202c295004586488010700314a80343c20008844001001d041614280300b104c0d0001000d5850303c00b0600181901c4006258403c4d90844081c1590412900c000c5418548408041c681e6001021520b10100455170569511600842910140941900d09402c0350b0754062a030241c50b00b103c08070b8000c0d8040d0750046841102070302c3c00c0341d4440c1c03140961010300c14000c41c0300391003502a140144c0614490034048040710b41c61a02c8804662040300c800c44641c0360242403100b03200b9070002c58110741a0a18095203140707462115a012132048150a52602a20040d40088410b051000714050400381c4a103650040e51500028040c201d543d605841d1940783c0011a2001c000010320039840d00c0b00680f0550915203151503802c82904008136800c03890 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 419092248 1250 419090998 419091017
    0xa1a0712150b0a090801050612031909030501060306061d04120c0606080f06040c06050a021b0301091406060307080a0c0504020708120106031401060302120a0b030114040c083901 78
    0xc0b0840e4000d8032001c031099440c801001d00d85104142910400340805009900c1c4000c64803100c0f00c04001c480310a11800b001c40409120144200c81c22000d1341e10292440d4a0100080204140f80d0455400c40302c40c960343c5071a1641108940a6025041e94000d280900e5000b0704e00c11300c0d000d102100e0105000320800180590b1300d11600d4180740041a100060350020400c010800041544140c00350000c0d2030403d0a001c507461000e56149a084013002c0018000d14451105070313425004501455030111a4941a8520020955039501d065030210310034096210042441d0b580040c000b0842c80e08105520303c0b0514050910009500001c4d003030350404002c000a800d01030f07031411001d0003056203070b0303000607001c45208075403580e8001a00325200b0540108441003050990a40c01c58201070b20700701c001094003020000a005043e956000600c4c4500e8000300b20a0080e00050681210104010340f2101b1590034904100101500e0010401e07400c15140b81c0e05450259a40010340001030500c80543c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 419093498 1250 419092248 419092259
    0x100e041d2506050a0e0409080c1b1903061d0a03080103020a0e0c1e130303030204050907090e150103180f050708030a171003020d050a1a071215 63
    0x10301101918040c0300e900903a44898201e9412558102400744011400005810448020400d10034074843c0760400a00e03070f401001c160b03a160700c0300d40000d5008600968804110344030644649207146441400448061301e1456030034203003210b02030340041c51707080d40e40241590b41e8070780200149101c40210003040c05548c507070a08208441c84090740a51145c0c2965031443c81001b61034038194010341184030140c010f01c680110341c5403d45104040d1003801d0190507025030503c403e18020011446480310812030300109141d0194000d005451040c0e500402d41d5503200c0e0191003114061040301090610b0000207160100c05107410704407041c051501241943e400a0940c2040c070309198161a1102c5003c031003010084200404002006180091410401d69000107480303000c150407121003010b41140090100e00359060351002035030380107003205000c62280c00d050303540b400084004c40d0711509070301d00c1040180c00406113a101d90f004e42d0350341c540219682d15480280241e01403520380d19000d8076002c942c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 419094748 1250 419093498 419093531
    0x32d020403080313050d0507020f010f11030a030204081b03120f131d064203010801092a090c210b03011107470114010806100e04 57
    0x15100c468600303912135020741426800c00c920380040c0c800b4080c04000c00030050301c5d61401816090310901f0200380801651605440d00003a080768600103000c00585103400a405501a20988510104a5102d0902807085585031103c030001070340d055000c4e8501040500d0384c000142201c942503e0902d050500d522450f5514520f260860f81e503201d40700d19181980700382207803803541c02a81103454a040d805903000f400d8501c00f0071580000020342428082c5441c0c4240c2d08c24908900c0070b007207142d81c0d0b9a0750b5140580200003c40084442440d55116996104a0358482c1000009107180c60300c540c0d031408120714000c1140b103060a0500100c180342e00b084140f00308207030000428101002c2814804482058211a40117030ac002e031188060000e40c0104039105c1c4030099410220800c20011004e00b6010424a01c00a056541000203144401d11400030b45031480c1c1222298406164001054401580d280000312852900584500c0d41c46411a00c10070401c8000703040501b00180000c0c00102890 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 419095998 1250 419094748 419094751
    0x60d0605330f090a091a25020d03180b0423070b0306040c030914030c0c011d010e06040b0d0b03060106020316060c1809140601032d0204030803 63
    0x100c41005586901c0001d4080c88030340401d6107402050714030720354803140000d41c42c0c1c01d141100c1802024007000260382e8880c1ea41c040034105410689070020909807190f02c1c5144001200d20681090712100004501f980300c609152003808942c020703100280713103004120300034000380e1040c03402005280d0b802408510f0352880d283c00f031030282c0070b4510121010408101245038400311910a5881214100100004003050b250080022500851003071a030090480140614000c05006050640280143c005000004000c030802c0d42c3c087d50f030b0010980005550071000c40400300300005201640088541c4214020480d545000b041241050780780c01c6c0c1084a6040080744031800760742c540340c02c903403803404020310f0380107060383c0c401145025000045203100341d0001400a09040c4c80d80354641405008460f03c0c10704590b00c4002ea118643e80c1c00140003c0c0001c0e10440640c141b0150100d440c6510a01a849130321840c42c40c11450300040c0c4800f12400c2070b42d01c501544c029030900c40400059030110040d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 419097248 1250 419095998 419096011
    0x60c03190c020a03020d080c040302040b0402070b07050c0c011403040204150f0b0a1701030317040807051614010e060426161d0103020907050a020c0907020d0e0301110909060d0605 79
    0x2c0582c80309030700e0060700e4110800801014007120008008c10a1400b00480341034079410740e070110320380034424080b0f00640141000100300184200c100141780d03a0210140141440c180121134001d51800010f6441c030000ca1140034a1603070400004015050039000100001e0005100140180da602c00040c032040b40e50b04034446a035000280c60382c040d0390168501102c0000501c440110354035640d00034004511300c4040c0716403c00da0384c0c001070a215402003980c070110f030401c0588951006689a1009000103400f07242075003400703010503100d03c0d44180000003071444081d110503e09418280b101030166212100c500000c00e010201c10218481030005035041d4046aa2550001e81080010343c82086692170034000083c0d00320040001d69604401540c0000c0e09007070695440e46041c1c1d00300c0c2001e600910343e40d001114402444042680050724008500d9595980e00c0d03800c081c3e00030103080e00c0d604001410b5100b0240306850b0140760407800303242c104500502c0a510700b440d507034a04040d160202d80340e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 419098498 1250 419097248 419097253
    0x250605010807170c1c0302150106030605100503070c08030603010608070b0706050108030a09031b0b0304050709111c052d0a200304060510050411070203010e0609060c03190c02 77
    0x2040300c2c4a41030002001e6060300030280104c40e2a541c04106001904501069130000154106003898001d04c0007007000701e00b05031802c10710b40c1c41d440058042d100521500d4040d5002c08128a041881541030340d0060403a6550390001d00320a07100d22981e0b0304050440c81d41556203210005c0d00d0791040002da00101805024691500c4060420ba0100d400580c044002a04104580049c003640800d4030070940342d00010002e5500c03440035602070584440d40016583c44000014042800800100c80c0704a5909000905c5000400c9000045902500c40c0510141c640d5100c520003401c107540103994002601c000c141f005c00205002100994000c6500c02c1007000b80100f80800b00416004c5c9101900381d61110924501c00001c040d591844003d2015005036510004a500304d00c0410483c002028024020300002003902d0300304c86079500c8072208038070035860000e5642c491100816101d1080d1587d00180842e0354a016040030182d01c0208203940e0304000003502d40e6115014440c6928040c0a0f500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 419099748 1250 419098498 419098513
    0xf0e210a060b0109050a1e05040e0f010f110405120a06020703090611060402060a03020c01091b050a090e1e0a0206040f06080702060c03010612090503070302011e05010b2506050108 79
    0x40140845082c2040c1c54104030002000b8001612001046000ca074000c0c0008001c103803007220214091403158200c158030034101040d5015080d80018903102d000004002005080202000c7c0700c12281d01400c50b05007408140020013031803030043d000c4080020040c0c25181b0810550707071150206d900900c0101d010814411061000c07075802220412903400782c0c401000701e418035400240c458095003640004164000039003142d210300c01c0d0006c03682150b120207100c0907070b8485486105a4099400361a0052564040000e41f0700c0550250382c104850030406400b401612610f005d1680c0c00e030540402d818801d100340e010068840c0b000500003890135100003044103040450081004c3c102505280031507002a051003422038041003201e0441d00c550501760035460f8070b030100c80003030420500d000c0c0440c0000314078441415019000041003000c0700d004020081c1600302010104d407800e0180c080c1107101404420020213581c05502080100448400e282406642e241000d948098000000c1504880d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 419100998 1250 419099748 419099753
    0xa030504080f070815091e01020d0b030118020906191401030e0c0307060807181e1a0307030902060c0f0a061a0913020a0e0a061809030f0e210a 63
    0x1c01110b1020000010300701440c90300c3e01c00c3c0c1c2d84804001c1c2e01d84007054000b02041444404000b40d06500200e101e01c2c000141104021500031b4000056204040d030420000d10094076041c8145448034032940410001c0407215028400303040401001560802d00e400c51414000640300850b00081c00607405400150781050001404c2ea50741441c07205050f40540318081d1107680208030f11068030f03c1443d0800785581c42034002c82d01d4003113164444c114440304c01c40122b8625000081c0200140c000c3b882080003c3c1d41d0140d241c1e1041d601440442070b14018804940d18038800d4200100c02d80c0010801801e000300700e680e050500c0c142c600031303001c5030340061005400c11590b4001c130300b060b4881c21007082d0452407a40100d005014020003450018030000a008119030326500e01402600c0e0032552440140741c81e4407007400500c403600640c2040200103070580111511809011902c40d850ba480d80760040401c00d050b14030b01516000e072039002410b58122500321001700d022044c003d8450000382900b40450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 419102248 1250 419100998 419101003
    0xd0609050106051c0f1112010608070b031618030213050702010f02250503070f030c1e03050a080a0b03100603020414010e0f1e0f04020306151f050c0a03050408 70
    0x591003e0300828804400a104d44800c1032510b035000d4110300b4101641c0d000d4501441d40604441c0348503403058204a0341d82c14248158888410748215004844070310307071902c1c40c465007400200c40100e4002c0d186d103002d10307101788100182214a20f26580c014440344d01d80e40000c016040c0951588050341d610410020401c0e42409031240f40751580030210311b45175240f006c0b8406000d600c04c11804403088540c1300c40801c4401c0080b80c07000c40d000412103c4902d5980b400600700f070090b40c0140ca840c0b45260f81d1901047c02e020401d4800b5515032203241c50b041e84160203642c00980101642c007400d5442120b00040d4805106c0c903500f20280c1b4400154190851041000f11802880c500100d01c000500501c1016050301c00c840d000030402c0d100d14016030342c0100c1020480321100d140490000004140403521040c6660180030700c0c800c4007030701c0d050380e680d00c01421001034420a0541c007601c2070f2490100f005951041d07445e0300d0101d10b0001d14200c02e0486103881e140007641d04030b0002d1400a07041100c844207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 419103498 1250 419102248 419102261
    0xe06100c020a0e1f06050f0a180b09010f020d020703061109041a100201060b03011215090b010e0906070c08030a020705061504200304030e04140f09010e1513030306050d06090501 78
    0x1189600c03108900381940202140204140046120000a01041c2c1c580c081c101c00342c2e1800301c0727041e0809200c1d124040085c0c40d4206505141c00306111068144520780041241d00068070147e004140c072a1440c2c44a0014111107859441a0602049240d00f141c9445c000c3d0780000001650b140c1d03841c142001440500e807102c2c2c81010441e450944180001180c039402c13030741101c4004041c426654104d081400c07000c400144200e1102e071800350b442042100807601c0a04903410880201c4286e61544003081d00c81c10111124000107500700e88203000601c441c80615006002d10800500f4825203503105450120291400792a8011100c2525441d1920303000d05010307070010030b14140c400180307142103104901003e40f0007414000015211540d907101c942c0007000b504003d104031201c1c0e04002400110250055981e40f9040d404d00392200311020000405038500c90804203030340b100303556080e01d0403c4006186030071000c2545404001070503a0740e058a03117911a008000c00070710b00e011071801c0c41c02c40c0e82 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 419104748 1250 419103498 419103541
    0xc150b100306060e0f130b0316030b010801050a02070f030c051f090b09030403050d0c02040f020d0c0e1203040b220b0408060708010f12020f0301050a0605190e06100c020a0e 76
    0xd02c0254003e041d10f58600b0b11b1944410240041441c000d0f100002e07040480603500348458040d071410000c180056502414103d03280e4000030810307038175144881020382c802c0d40c0001d0a80621000e208000900c10100c4040e024000c500b40c42c1d4154071409044410142071400441d11501c4152990500c90f4110140d604050008000d6103024995030b2082c0e00c84a284500100344185142c0030010340d19075030015022032248100c115900e44500118070010041917400400165000070001c40c1c50410403220b030017660344c0b64015030411f4503082030030361960b100389180f01d521400382c0506409034050980142c0601000045151500c1c1482c3c4a589881001440d00d010824404010070000b0442a108419203402d2680b00d0f061603e2030011481514075441220380541c070341020082401d5550740a44180d42c2c0864030071011007858030040c0039684590244842d400043c8020606610b082c910018949445052080501c1941d8002a40c9071038541d00006000b80e10743c04000e107140d181000306030f1420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 419105998 1250 419104748 419104759
    0x10605040f1d0d020a02150c011e0e010e0c0d020a0503030a09030b071e0c140d0206161103030c09031903080a06061e05030c040f0f0312020703030c150b100306060e 72
    0x805500a54926074000b0203070003100b60030f018400301541030080f01c0100c01341900074000c40602b0310b081ca14520031850070b500360b58a0070f4441d00764881c0600829051031290001001024410020003c01001e45407040b40c1c45800603078005210f131000c1c8050130b900e501c0c9403a103242092135400e05402c030a000600c2e16003040328944070700c403800c4115210322803907031070b0b42c60548407244081c50120b2503903a01d0203c00750700744101c0e0342207103150380c3c00541035100340003c0380e0419060003881c00c1502c0c5103802c541404031940090001807000d03032000d0003400c11480020300702c0c5d200307481403000c00318124442c0d1001e40008440c0300810081e00054021200102030700d1030310927000c1401407a821200d280d000c2e408010402d00201250b81a0300070019100604240807030304910075951864451088602d200481c0c42d0f0418451010f02036001040c0c58080303d03059203540c0c1d036801656075940301c451503950790a88061754407525594651030f0500d00504001d500c0e00d00107095410000064a900c17505000544101c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 419107248 1250 419105998 419106013
    0xf1406061203070b06040e16050a080123070201270b220609110a0807080d02070f091107080f1201050301050105030a060b21030a0f05070320010605040f1d 68
    0x30701c1c00000c83e0025600b240460003a80c4500002801a0000d51020980c074440d41d13100300100005a000703001112801c8038000c946aa4a040c2c0d00e0a84414416070f100c03104008449468030002001810383c00b26051000090901a290001c1c4441c00e40c4906400c801302e9010441c0c0812809000c1c442c2c000b540700700845440a110000c402032450450750080003191280d0380c400c00c20a60540031480030b10018840d01e1201c0d128007440f40e1710040742c0301e00c00040c800c8100c0c0b4480c140c000714404056507004100503081a08044040001d000100483d208001003080700c04003291041c405803268400c1d0492199a0780c900c031241f4443c00780c0c180c106610030392510300100005c0d980000c828105030b80c0900003180051001c5c00003202d040c04e15506c850300e80d140043c2e00c03a14100c084020710040109407603441914550b40d40413100d07030154000c024082404210b040d00e402904181d00100c10800300008140c1d1a11030001c40c09883d000161252120b480b06c203076654000500605407640c1c41440001e0410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 419108498 1250 419107248 419107279
    0x90c1a03090c010c0f110f1c1b060e010f02030415030609240515041214060901110301090f181412090906100c17090a05030607091a070f140606 63
    0x14540305c610003400791010400000554640708400b1628100c0104140204810510040f42c0c20207510000c4415100203080c1180c40400558604d00f59000c640d04c80100c45104801034502440031482d040a5100034000010311240115205400c01d80340d0ba800b0a22a141001c1c80302500c4460f0218202600b04484c1403440900480610045400445034071100b14401441482d0700c0c455900111022003c2141800610210340360442d1440c07c80740403243d40b50390700040c007030803284100e8040c6c404900410041007002069000130502a01007080018000000c001070486042d02c0c5204907420344515404490620060100b040c2c08008015031030318110741c1e00000744e5803010044c055481803c4804400e01c1080c4601c4039101d9155110010311009030600301c0d0420780b03030040f540440c45440ca603e030109036402e0214074940101d04d96210307045102d0030503181c0c07138168400b4842600740100911001010603441c01c4116100d60080003080082500c10403e5030030031000900045c090031121440000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 419109748 1250 419108498 419108513
    0x3010f14012c06090901080105010f0b0a05042705041202010609140a23100f050a050612040201270906090203090a060902010212040308090108150a09090c1a03090c010c 74
    0x224504005500800d140105001030420b00401c031303255030841189800401c10007415440706050f220084e0f14040d400303a4075840c100c0140b050703052000c00a0ba040c08100500302006001e0300c000c8c54058550700b0565006d0800030200c4404407020b640d204800d812a0310010f17028030861010b0504180c00380400441414050075072500945000001903540e255a2102041107109150040d10000104007900380403450a2850220f0b010b8481e02c4400c841000607249003c4000c4011a20050451400e07d074015410802000d0001d0060741402004a55449020360300102c6a2000f00747c903580620745828510f03010122032090300704817074140c030410901020000006040080c030b50f22103030100b6000080e20040341030a005040c5091700d00d4020401008012020300a401c21410a90f500b40007903071030070701ca031017121844000c0907001001158240003941d41c640190030094000e5104141e0b0584c3c0d0031031313030708030841c1d010250f03000210100920a90340c0302449605032010092030402c400c200303140c64201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 419110998 1250 419109748 419109797
    0xc1810020a030e0301020c0f1b100f081f090c090f0308070b0910110d0516120207030e0d0303020702120d0206160c050d08061507150c1403010f1401 65
    0x2d050084003982d00c1e8490b9425012100d4880b50300b82902c4c051002e0b80070b2a42e464202a50310b0340c0003100c4072051080740c100705500c00601d2a1a0f90741240d0b251003e007054900502c080d03e800001b010000154041070f03130003848000285030342c503800164400000b200130214121030f0003981003180e0944040002c1030030101a1903e8a401c0081000503443d0803000ca8500860181c0140e122420090980ca5039036164000e440e1038400c8840500c050390311058051000140c004070342002c542c1c0c4140e07001803c202035000d068498841c2c10b10f101030003103100009926041285045000030f400040940450174010244940c0d194400c0c0100003203000180c01a40740c3c2002490800140c10341d503424038141303100b0003242c040b094000c03084e0341d0b41c129511001440140c4c1100e44500070411180781402101112080318042500100c800e0700400302c0b507490f10050040ca200e5070081122840e60a4920500a00194001e0901c0035010030010700d801ca0b41c10040c1d08140120381840200c021201c0803a00040104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 419112248 1250 419110998 419111003
    0x1a0405060a030b1207080d03060806101505070204020d0501031415040b04030306030f0b010e01061404050d050304030b13050d0f17100b131403010227060d050c1810020a 74
    0xc6001c460140101302c44018000041d4600e00c20306500150002000c90b49420983d481d1f5001d000c03164890411aa4490b0143c426100400702954100000101440c0b100b0003010180350886c0382503825000135060f6008103183c0c3c5111507542d401003040180e13030f141024078008000b016050381400352114405074007000300003400144411001500b01846940000061580107800503000402c0c1e040000d0f40c44001d0081c00c1407c13410000200b903d50180c00300d056490540b1102c7c51825043c03806200c603c51101c0421070b4144424403000c00005c0e00c1026141c40307070740864010005a507072814094035189001c0c00390382c14002d06420200705294044c1105e0b0303203c4c0502c5100c400545480550200c0a01540d2200c2c524030070100304e00510f41c403420a11012a0350f040c0100b94554445801c05080b441040c229100f02d07900c0803803002a00e14540c0117004a51401441c00f424540c44200d800140d807022207840f024400d00040c0c61204404002c0700100d8a08190390580482c0d08004000e0f64442044201 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 419113498 1250 419112248 419112251
    0x70e0a0c0c03080a110f0f030a0605090112232a04050606040302270709030303050903090d120210090c081509060114031f05040320030d02030903130f1a0405060a03 72
    0x360710f0000030340102c515100039006e0076562803c41c200180d2007500300b40d0705108414102000000c1c03500e480804941a00c074882c1d803c80007002255981d44500d6007814591209010603004805070841c00d1000040d01da1140207600d039003480010400d000101c0c80804c0600c160700d817400b4022641c44c0c0100791030550781d0684010038000b1a0031030316241031024510091009400504224141c1c1c1c0c080703075101c2100d100b900c0c1030203a6100d004000380c5134040c00c00401d030030911859a0f90085640502c0d2004200260300554807102c550042c07602c02e94100101c00e4074501c041d14030030061044108240ca044429603400410b0381e040500c0059241e90041c410f41c01343c81c00f00000849682c0e014007030a01540101804444e2103080c614455000d041c003100c2c00c1e03000c91034001040000c8118441024820703d11f41d006145003010861512000b5000a844502203100c140700c4c451503180d01c43d0031940500a154008a8400d25020076440740003043c524902d0280b5050204002c80d840320420394014504a040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 419114748 1250 419113498 419113511
    0x100f080403030e21090a09060311010806011e0903301404170f061b040501080712090302060a0606090503030f030c09060307030e010b01050c19050708070e0a0c0c03080a 74
    0x800707244c0301910341211044241c2c05101e407400ca00c02c4005101c6000300341c4d59825003660b2182282d0880d071082c4130140c030719038000120111542c840e8111030390104050400c6202c0794408980f4148400d80c0c105000c02044034170b04280140202220050404100340041c002c085124000c09150202e001800800317100c003404290b071120b440502554003034400202050502406000202e503600f21040540b038003400f480010800c2d0082040240c83c01600d04202240b4080c03500c001102c08010040600c020013160704e6920203116110b0080e01e41030790007a0300070451410400440012901d0580c845800d104004070208455240802640e8a0701b4031410843d440342c0e1009210320962040030b80c144c1c1d01080c00020000d2094056110200303115500f00200131140c0010300650741441234519041181d401550100804040ca14404440607c10b10a41c2e40503542c0d680e445180080941200341110646410043c942c20280b10300801d60034035162a00741c080c6241c03405089150080c0107035400d1601d51130b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 419115998 1250 419114748 419114771
    0x904150c0e041505090f0c071103031c0b011404051011030c010e030c12090603130201020a06150e0a0203010303080105011d19060e12030418140c0306100f08040303 72
    0x28591881d100a03000344000e11120a91024050460083d60b126004100c0413401405907951128464081c10800784d01e400c42d280c642031401081502025810700c000c0040000e0500f0000d420300c4808010403010540414640025041c803006032031442000b4000e100c200b05c9aa20400000c007024440d041511250084000c40c5003144140300c03c15806600740101c8490f4858000002c1001d4201001030341d64801d80c0090301c500070301c03a121595600001c284007041c0719003200c02505040c148140102e988561032580c81c0310660303c00011200daa1060b000e07041004000d0301c0c49103070340089950421850f541c1540d034007034030083d07040c000d150400040c540b6222403049002e400b150344210080c9014900030903074181103821a01400740b040000c0d40c8940b400f0140c1050040b040007400100051800d090604c034050b000c0c1c0d0884102c403045030340c8a103075a00c800401c000425000302e1000d041556240b514009100400f0b40c03160161040002d62416995031540c80074045070415450710303002c20344200e4003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 419117248 1250 419115998 419116007
    0x5070806040905191a0f06180603160b041703132706080d1d0a030201080606120f180a0c030b060607080c070801110c0303010909051f1a0904150c 64
    0x301c2c5020000e01808000b1002c0c00070303212603102e040324071032052607846e43c0740071009410030415034505800842c1440b195092049240d000e684c401e90180860b07010b248030b4030400f0080a10765200500d401c0c40010305002400506d000300b2a81c4107610b0056261544203840d40f0f4030030301c00e4418110810822642c7d41d00030906408882c548010241d001e1000503102e841c03080d22000103000007400702c1c0480709420010002010300c02c030420030042c0f40820741803845e001940ca06100501055014030100850415a524070701c2032070140788560540c900510b444000120140b4046550b2400e0b684503418032000a90407503c5602500d521003c00c01c0b04c0e4032200302041c201e001d241801454076201048044d214840010349400310341114000744590030400d0182c01d42481590200301140d0801c100501000406802000520f80b181c400ca6090780300811000d0403824403c400f1940790368648407004541c0f0382c1440c611004d40001c1f10b0081d814185590b03105c81d048980f48811015a840c0d8041d0032001c0e014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 419118498 1250 419117248 419117263
    0xb010311150f0901261915060e130504050703031b060603140610080d050313020a030c0614090f09070207030c0b0a23030402060f040305120c0c030105070806040905 72
    0xa090584074680c03550140d6098000b9078043d0300180d0004054016642401c1044034250825400ca040381d4454851403800f4042d45c80ca020b5a140d2900904040c50480140d0300700140f0403681c0e04003624400c0020828044408503c03401600c2c10282400003150000c9400c3d003c0f0390307050034524811030950aa10031421482500604020714240c80003051182e07080c50700d444030101105a85440d90f03444074424129003140650240355000486005426001d04015030300001010003103c5481400e0340064500c402c1030304200d9984501c1d25003000b03c00d42242d07850351842c6d84659000e0034203290f10082401905465243c0d8842e10301d210202d850f0f64001d1280c034014540000420404546600a907000c5a002128040c00151402c400c000003151810a90400001420b101840c5841b40d800b0072901d90060304914007610070403c03001000803005c10011a000c041040c5241e190a0800e50b4103007881c920f2011320f8000d034100420070403071507803000010707a2201080b40d002841800c0c0e4103005140184 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 419119748 1250 419118498 419118529
    0x405011b0309030c0e0604200301060c050a050604030e0a08030708120601031e051f05090609091203101706060a29040803030f06010906020d0c03050c060406060e06030a0b010311 78
    0x44e00000c01e035281c1004201d071103000c0039501030110241005510a03030030f1030017100e136980240c2403005100a600c255000c000d80d60241003218034212a61b1070700d074181a0f00703541c220081199805c000e00b1038240b41807440010700c4500050b5081c0005038881002603ca0741100103240c020240018806038000d0780301e15036400d01c4082c40c0207103106041c001e8009050560b5040e541c50980d2000d21a2507010040c0380e405ea410161809040b0780700c240900c100500d025041e0201c500420801000051900340650301c220301e0700c0c0c509503909181c040c00c186a01c000e810075402c540c08c4801007000b80e440c0c1d4a000d204071800c099082050401502049859400c240510994032100040024100000202031405101c82c000310540d16281c1100549803055684641409600941e2545130154055000360928600909103940b526500d00c000e941004400c030b8044174000d640d4807042c003d14420315401a442403054009080d90354442e1035031035a0103014400240802c03000c500e640044c0c0c8840115001440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 419120998 1250 419119748 419119763
    0x21506011b0c0801060504060b090402071718012615010201020c01140103021306060212130302040c11011d1914120d140c0a0f031401090e010e030405011b030903 71
    0x2881072800350070101040c82103c085609004010130903240501c5410111208010036514000d401c01c1030001a42000340151020131000c204046001d401c000140320300399061001c1c0104080200c00541100c178105404c80000020082440c0504040700b0394580105031801011642e01304480100e01a01c107413290418554201040740ca0701c9241c5220305c1e410f13039100b160740c0018422007400319000c03611144540001a8010300040c501c2000b045c00034a28226581104024031ba104e40205050760320400f1080000751003018459079418082c8540131007021010074441c222040c00c0807440e55100c80c228114101d1403645006810041803580321010ba00303014043c0d40828005516440850308108600220386081201c800b861501000300c00e80300c4c140841440b41880f480388011a400300750350790a1000d040e5500c07044a0410230041070b80c0c1c000c001c8208041803094994445033700351200c0d000c024416510070b0005001aa82003800301c41802060f610742c201c46410740c28202c981a0300d551001e460103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 419122248 1250 419120998 419121047
    0x3070f09020405150a02030702060d0902040c050304020415081f060806010e01170604020604030b0405011401080f070f050607020402030712050a0605100206100b09013b06030702150601 81
    0x112280e4002e001103070021900e103900308000c2182070324944281c0e400d100058108000d2030f801450910050003803c0c20100c0b0000318403000d80c0c086002c481c048080040428000700c108421880c0c50b02800b0f4005203140d44405009150071255982c8403113640c03d000c204000c48031101c120440342d0b440b0500a2503072034221484e55940d2120005203500a008914261202c09601740d06c81a0019580f0b0150790b002d4031007881c3c941766072500b64840b0300c050012141c03035484e503680340c100100e2054454003806088000d48803445940059514100c0654800222008070400401c801c1e40c41506a4a1041c1c068502517503e50300d080040368640c50755a0400350041c40e00c0d00f4040314200c25805042a2038040c0c0b00c095171900d903404182d0303403a1011200c27030b401c0e08070001e024405500d9481c040c1c50008818105400c0f0141d004203140f4071910700c2c110024036408855610316680c914800011051030065540d18690300f82254001e46038481c03120404800042007000c102140d100307500300540c04140d0984131400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 419123498 1250 419122248 419122259
    0xf02090d06090507060819110910020105071e0905151204211d010c0303020c070905160903020907111501030302030307020105010503010213120807080f040806010608150f03070f 78
    0xc0918035070540b0513229008010400c1800307012058041c03402400300e240c146440242c188040c00c96940b54600d20170041c020307a9120340b10710500d20700c201d580350008141461300050042c1140c200702c406210716044083c00e01c2003542c004000c00143c03401503c40c03064503902072855401d180308401e0039001303c4150700c0400c000d0224010079807840318240a540b00210400c014102c9900d40d03086c016201041030644200040d41c000c804d40d6102d14440d04002d81080c4801d0b500d1030600140d42c2c0900312490302c400400034552034012140c00e41325614100070b00c1071b0f0700319004a551080001c000809014140c002041c100c1c000300b0026005400100c031030580d07982c403450001e44075081511480f000d50300303200010505190600035140c09648140c100d008003807420000c034116101c86001989c1b103040811200000c11b003000f004020300741185032803036030741c0e490096054a05101603001c0070800c0001014400e40c028030514980c00654203c03000031410b2510000a801e2400d0303684131440d0500f594100060 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 419124748 1250 419123498 419123501
    0x50d020406121a0a0b01080c03040c03080d0204030201020c18010e1005060412022719060512010219020d140a0e031f14040c0603050705040b070506010905071d01030f02090d06 77
    0x560095019064026460303c004403004c0d00e804851880c0407907c400c001030280101c0c2e0300510360040c02104100041e0303690b901c89a00a60081003903005070780d0001000d0003035580411844c00100d1055504c203075206850060844080342c18000e076003850f00701030046001098034044480240030010a5140d0b603d64524812010b40025441280181c55090b50030200000c1d4620b480b40c95540440e480406540c0d6000101b40c8040d802c80354001c1c1d0f0303500d600c00b10f041e45400281c0c0900118520006968804940390940440082109402150300583c1d40940050388550150107680451544940322104800309490032000360220340c0d05845041400064240903441c18080320012040030400080682d00e0500103180894001e810540c003a502000ba040c80780e0711060344002245016070829469070740c41002c41d404050243e40a6104030014040800a0b10800d50011343d981480310b402e003480030400d480c0351019403119040c166a02200d400c101c55640445040e0100200041c1d9540d9644c6800d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 419125998 1250 419124748 419124773
    0x1021e031308030c100203061309050601051242100e1602060c09030a0503040801020712091d0a1e0f0b04020703020304090b06070f031e09050a050d02040612 69
    0x409201c03070181c00080444001c0704440d0401e1134480036018800c2c295260030041d520243c10309030408102ca441d8601c8441d10701c41d03010218821005041c3c01c0d4500f00400842c041c04040e2003031250049841e8180210b403450340d080400ea000d00610395400b40e038802c0024003803859110340406800da20104603010610300d80084c20317120075590408658448503083d186100c3c0c42e11518001d81d026101080b2881381200c00342000c6000102142d100b100281e40c0c1e5070075500668445da03002d039000f146240c108481500918a030031340901d0004485850001605004030000481e05541c1341074030b011500f28131864120b8007401000d01402c002c03040c000441d803001825030000c120003030351529024446e0b40c5024001c482d00d094159004608041c00c1881200c000e168051905500950804c04440000c1d140220b955025009888000c1000485813180d105200840105010800b200006100c99500c003600303802034072001d50f50181003843c2880420000c0405812030521403201410207020003c503451101e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 419127248 1250 419125998 419126017
    0x150c020607151e020c0714130204151205060d06050a0e0607022a0607120c0227100510050f040906080a0c0e01050d020603070c0b04110a0b040e1501021e03 68
    0x81c10364160402c07032804c9005644446400782c01c030300410840a00c05000720402224024a48035800b03148092031f000700d0307000c0d0703002102c101144030400715540c0d0404500c180021100d1014816840d041c00000e0756800310b81c6009000c66a00d1010a0860442c1d030f001d102840a288200e8049007840c1001941e16118500c01036a20384a444001e05150401d4258020746080a13103924100511680c8148004c02d00a81017010480d08030740e01000f6a4682516598802070024008640090420100c04402c2c000707000c030051050000e020030094680e00d0b04c00034000700c617103006515400500240881c5204980c04039011504003100450b02d044082031075181c20f807140c2000b4285c6942c441e0f1171480c0303480134407942d40d115118894132805400e0481c0110350180076840d040c070011089a03503114030b00b101901c00b80c80c0402012140d082c1810111910f4024000c04100300e81841e140a110341400c0030001c000094030b03407606980e50b5683e4000c01140005262030000e108201c2650b11307100c1e81e80e41003070101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 419128498 1250 419127248 419127281
    0xc03010903080a110909040f260d0501050306090604061a131a030a0c0b03070921030f0e06070f020d02030a1209050402041518180203090606010306150c02060715 71
    0x9159440e003020119802c03400e010704085450343d0340303844480c4059803140b01940c000351011072700254600b03c94801580710302d074040066202d00c0c1901d0341008440c016080340d4041e602c01d9013030128002001514a900c15030000010a000d40d80c0c0c81495058507144801981182016201e46113034015074200ba07452602ea11410641b418800c001c055440f602c15030003403c0940d443c6c006001743c000030801540d00c025203007004008640d0b030381504e0701c890030004003e14600d101060b00b20101a4440c6801c114003c07540340411000d2a0500010254400c0c1d2100400256003114180e045480b28045200010b40003019904d0f4400141024030200c1c56103c00d450006600302c4010078145400e209072400d40d110b0301c0200000903000c2c10141c070140058060700c154001d01035400207005010011032a040c030310864016850341012040342c4c1c035055000d040e2905041c1000c01c1400360300001c44048600403024035003a905814a80003055892145440160a40e201c001005400c41626004101460b000086 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 419129748 1250 419128498 419128511
    0x5060405010b0904170d02040506040312020601060203180603060d061401031b060f030b130f0b091b09010f050c0a2103060303022505040204030308012c16020c03010903080a 76
    0x108071400100302c6000f4032000560720340c0f405d00703140900a030800c103c10b40c0d00149044d03105c90000c0c4980d00700d40d1084415600e0b00a1502019506001450051480b40021f509200703810800034440c00800355100d0080c0b80c04070001c0c00c540d42d0030041150303298110000704030b082c43c0c20416003141c090900098841400b1504581c5c0c4001c0040191070031510f2a0f40c0e14170040030301440c01c4001c0c0c031000080950111480d08200d1020f1020300c50b12809962101c400a6801e6406c0140a8140c10091400007201444418010040c510744101c80c80b422007468800300d5600007680c16515070154000103001c61060800000401c18141149200019581e24115005200240031415621680402801608a81d020142c0400544a1603c0d84240301d000602c01c01d0701d07840031500b00c0e04254001c2d000961a00010040150144140703c2c103030030100032800220340f0440070014030f6000601071403214460000c1c4500c40510034042d503424144010b00902c1421454180200180320940e5150b1340c01d841c152 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 419130998 1250 419129748 419129771
    0x5041206061a220501050901030914060f10060306051008040804121208250e0d2405090f03090f0f0405040f030e0a030c140103060b0307050705010b060301050d02040f0213030506040501 81
    0x8290303c080742c038142e5a051034524684011006807203804001c842000d90480b41d180786070070620842c0e120361092040c0d04900e00d480c0384043c142070b203554080420b00d8034202c01030200d42c40e005421058500c0324100f070302181e01c891814202500c11540000002d0861b60400c0c8200310917103c0e28054000380c0c3c0e80d007200e80e4942d1024000c100143d41c04c1c00044641d101c411400c0307640100c14865585000800c0540c4000541c0c44188040e040c0a040028000c1003801500650041d442034540100d404001004808031110240c0d175a03108801c6da1602c1521601031240e003a135598444240b0104000c0d20034441030410749850003400e48140b000302c000c1603600380c1860303441c20510602400c40360054503d041e507920700741c41e201c000103031540306c039040588901000c0b80054048008601500c0b0356951180ea40207142012030841e5006e5200d00d1080800708010400780c2c0d280c0011541c040d404580c00913001060800c640000c2c81042e90050007540e04220000078480003181e0240b090740100b009000c02c0c000b04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 419132248 1250 419130998 419131057
    0xc1502030c07151d0c0406152a08040305060a050f19021c0203160908030a090b0d0e0106080a1104060b0316050403020312042405041206061a 62
    0x1114256001c01c0280a9a80890207404040750001c0700c8801c0000c1e018902c21190301c0f14070a40b54842c9140c0d01c45494000381d82004e00c0b030a002891040390307406000c04000401403d1121844270020006400c0317444481c0717146000d410b81c2400d07034400d0186130b03959601c1c0307000354030b03403008039070b41c011700e520b05000141c00b603400200d13180c030800c402d602c0340c40715001186546000b900010007400544a0382001ca00f80110244002c40c000c0c41e1114032030020050552004100c0111a004402c0c1a081031141c52a1580c00890385410b5401c1e50321500e86502e013016500c0c0081000c2140014a5802d04200040c400e6003c0303100044079008140d032080b40d170100300074042a90018820546041710420010b0840c0d801c450140010196034507115150907661b1300068a00001e01220103c00e2000240820041c0401045400800500162200795891440001c0c1c0240554890b52082e02149820716040102c6903200c4030190800344045801c1c102010060082500310f60701c4101114801041400c024540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 419133498 1250 419132248 419132251
    0x70501020705011b08030103060603020307090b010801090b0f100e130608061b0c06090601090b010f0e13060320030d30060e0708040213060308041a16030c150203 71
    0x603001409240e2411004546511054103007407200201d0003a40d10001d5a0400114002e50248102203070301410342c01054200a415800385901520348280a541d90742c0003100e050441d061420000b4840110401052803001c40c000748030760055503021402d0380b1a81001504070381420940c0c54440481103070040004860040c01007047c10fa0115000074801c00c514603424440080071025203003410ba03400d20f80b030b19000040d1004100ca030000001400480c6e070511980050120034078ac0b00c03501501c20600504070b50300c00214140948103a40c01c0d040040542c0e0403032002035a1040d131050060401c281c0c5084c0c114030b0001964880d02030410500c2c0994400e000740c54800c42c00d0f00d062003180c801c00980c01407160040e032075141b105031250720004d1510b1a40c0c107920322403400d40d2070b8020b49240500c100300c00e02c0b0400138407640807403826509002081107241928250b8429000f801c6c00482e1580b520121070140b0302e000300c0100840000c0e1001c05600c90a1030080d18480c405210445503c0c40c184400e0303000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 419134748 1250 419133498 419133509
    0x3190905030f0319050405100203030f070924030e19050d020f19050106030204020a02030d0e06070f0e3001140c07020402090f03061e0a020705030714010b030d08070305070207 77
    0x10322014860b01c41d0844c040f0300a140394209140741c555103c2c0840c1015802d0b100d600c0c003580011042006813075810801c41d40c013201c680382c00e644007414510348201400004a209041c44941c501d1201418060790050351030210540803a101c1d102542d10b00410b5400b250304c2240c290140c0d8880c11021030000420341da02c0d24075580a041c1e80e87e81d510404016901c4400181ca2035034881c2000405a140e510040007158101c0c1d000d0741c0c1d00e1000b0702a07101075400c101c2c00c078044c40e030048003045a0b49a000d01171000907102481d054041203465070020b81c01c420b0b8001d001e01c40d244110390701c1c004081c03000001280400e1040c0240016095010700071580070701160f048600d04420003402c001898a5802403a406c24000d0901c5081051100400c4c50450100d444010780c1400c0c440c0f0401039210000e005074062000305e02945407003021327580d0903281d02440100400801058840c0c00420600307400c04103808001500b201c0c0320284c40c2c10000c044074019510040403d10f800089440c41c0c2c40850407100752507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 419135998 1250 419134748 419134753
    0x1401020c0d0f2901060801150c050d030c090f0b0301060f0507110f011112031f120b130f110a09050f0c03100f14010306271d03190905030f 61
    0x424a40390608040703400340c0c8840b81c007240f03807511610440214a019010300180d65503400158101540c204002e040c8495100501c4205240000003c20004009400d9090307850b0200f522080e096007524004c0c5590018020b0000a6102041c410803100203181210441d40e624000c02c1c03800d44040c0c48a2140b41130181c00300c0703040520354451741000681c0810807141854441056040700152504001000100a02e01000082480039a01c003001c20b40d8060040012000f040910f0b1403244104100c607200d00038416141d4100080b01e840814107882645500305072a4083d00006280c00c030407000b00d00310420322401c0a803602040040071840303214441e4466000c01d05c0191185805c0222940005201c401824028403020480c801000031100085c10060136521000400c0350000d0b00ba2843d540154603414204a9440d4042034100d040502ca125841030010789510f015911650500b50b09400c1e0043d840006104060300d901010700c00305010065a983c030310b0302d49a2017050b4444400440d5001e940d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 419137248 1250 419135998 419136023
    0x4150807050108070e06030403020105040b060a081b0d08041d0a05071710092a031e090816030c0210051e1614071701060f090209191401020c0d 63
    0xa500894405401ca02182000756032404c8510029400e1f030300845007203006035100d5040c4010040d40703d420b150019411140c800701181003030040351342c44580494050300170f0b689000307201c180d49407082202c0645801620f0656290b0700d0300341025180c1241c2d00001001403450700003c0701c01d01c0b2071103982e000b00d80654074500c46004c030160030458020083c1100b1602000030b04009520400f0303224103a42c3c2006244584560310700794810403032515150b105102458184403c46400800c5800003070111404d0f05000a20300480c5c1c1040e00b05d600402a16041075030601840c42c0a150300446a0303044688202c808181038050350100b195680900010f680602c11078010031107818640d0300190000402a080074001041c00f0b807200b4440e103111234641796254014000030302c8070f4203200c4000355050482c540240000d038600143c00d10b00e0603ca1243d8041a6800b040d000104d60310f1080d803500e079100d00303022210940d4a1b2502903500c01c0410a880707015200b9000d00321950300381101790310b04150704081d105282c13 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 419138498 1250 419137248 419137259
    0x14040509060607031206090b01110d080408071a01170c0301110315040b031b090a060f0608090c040c030b03010e071802030c071401050a0b09190b01030e031804150807 73
    0xb1030300400011400e00c541e40c1e4118a5803c0a84280c200070030380604007142501401001414400700740c081c201c15900321030030442d401900502c4042d001540013550966480f49030501e0080c1400c44020030f4400000c1600006403800d170b0a202c0d0420701c280c4001d9454404800c0201802c076691803a581c030b03504a0a10010b403402e0341d01000c010500e0300240020403c00c0c00000002e08003c503070700600c0c01c100072102c10084581440700040d5030001107480304111550401c1c0c2c04c40341c140204c1c4511010000c02000260402034203000d110a101da0180091005401540d4003602524101e9802c40c0607610b007005d81001d00d100021108100c81440d0410304d101420342c070120002c2c1d131004101c0d405c010020003406d0000388140c81240145806000001820b01b045400041520320040c07445200b000400103000a8100b0700101070081c80c40310b980068115100c1005801a02501c01864031501021450100764141a50607603001007049500304040c00b585110b2040f86180c0b13004503a001d0348150f8042c0700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 419139748 1250 419138498 419138509
    0x7031505121906050f16020c130e1f0f181b08061510030c17060a0510032307020a0b1306020c0a11090c0927040803071404050906 57
    0x1002500c1c1d0140c881c580010050b20007000c080c640100c80007541c0f40e081120b446040a011504030b680f4807a0403010340440d500003551400c0440740c0520131307907078007202d980400c4090b4040b00302c12020078207880310744811380d004088540b003040d02912003d05042e040c1d600c0325444c1c0b041400c1c81950b610f40d55840d001c0354685c00400c540300c0da5807502500c1301304808101d10320104500351003003001d400b0050034540c0340e105101c0c4031410101000285800c050010340031a41211811f600c540c29052400c4e100c0e130320f001c005018200c0e154442e580100754400250105a41904031900458814021110300d0744000128510a04101c840d0801600032200410000700000c83e02500424014401c3c4400700098a80034100d911400e8000e0307099204c03034420800c1044490300e855040c1812100f50755185030204038200340e4440e04800505c5107100c1c02e151100304034900501c4401490380a07444000c0c1c601032500c600d030b030f5001351007810201e51030b901c4001104201c40d00f03d5056500190000107503440f02c0081c0079 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 419140998 1250 419139748 419139769
    0xf0f09071707080712060b030102180d02040f020a0f180501140309010f021801080618130203120f07051204230105190203031e0609071b0813030b07031505 68
    0xd0040c0807000402070000c004c2d01026041400c40800c800005107444011100d015100500130390060003004100407090740c0d044035203402a01c00840e0004c4510000b0003d2061040c030b14405d03480490104038581d800300c0c2d60840b42a407511440040001c01818030b00d1009940304250018611a4803001d078801a58080d5800000e248004140311180c6800c440036a000124808600101d58043c0300003982d100e0320294000600361243d100d8a42c00112051141c04001c001c40000c240c0882200115201040322000c1249000d0355680c40301e0350540b0700001135020484c280c07a40c1c03252194540d40c3e0a450007c440442d640b11034410820f5818541c05040d041c481e0080ca414480280702c0b115505040030313070750744004c00103501440d92403810503440400814440d90851019002200b001480d841d07400e15503070040024103195616100403a56091401c81034007000b8258840803980980c410f0000f02d80c201581c0c03060968001554403400101c007140d46191500620700c0303d410b000c014908049a95a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 419142248 1250 419140998 419141039
    0x120d1706150a1b030c03030f1a0f030f010504060203010f0602071520150a0c020304031e0c051801080c01080c0304020d030e030d110f07050d0803070306030213050f0f0907 75
    0x30100c50050800c1d10301c4903586a030f0150f0108005204440400d075061250703074a04403004408000c54444a20380d85040403800c5022801150300c074202002d00d680c100b01800716081d6640003401507160174901138019400070302c035400440300782040100da104c0c004284001640d10001d00003105c2c4030322503030450355814070441e01c00c007611800310714a807130105c1401107410400800b00e540d58603042981ca000d00711410400d4071421034100380014400187c049482e10707503240344c07980d1001d0348035140d00f080308100340030b1703400240d00506115003010500d004a28447c1284c1000c000c0d030b9000c0720b00e0401550555012106552440c40400014005140540000f0b4805000c3d00c0c040c002d0980402c0172920f4800c4003001c3e6008954a0010301081c3d41c401c115890a8950705009000e003145420302050a2110356032008224a502200040d51a84250b101d02d0085400610f07219801100446260040c02c01f80c0300e1820080c44e81c000102035210701c070880c40c020040c40c0000c0550078500090000a2915821030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 419143498 1250 419142248 419142257
    0x23f0415050a0f140d051509060103060f06230c0d020d0801031106131e0e011e2d0b120f090d0c0302010e100b0907080c03010b0d0b120d1706150a 64
    0x1082151100c92191912a02c07a50f1f000382001c0003840b007041200034005001c039041500341801844800c00700401082100c2d4107080402104420402c10740020030081d030200b4041d24003254030095610700144800e0410060780a0302d0b80380f224081c0880341e03414240800ba0000840b9940a900f0342000401410611111101c00841603117404441b50b81e50908001c841c1004c3d11600c0c01d008042f507215180c4d006125407401e104090b00d0f030464002034203aa03807150601e200001d2100140b0950f020505052880403262a00449502c802450f002504804041c400304480000061011914680c0c5940240d4161004041c0150f030b09908841e2010214000c078115502c980d125080d50100300b02c100042d100b500070114100344800b040c000600001050501040031100c24040341c8040711044906580244c000c107a03488101008900181005c090b040390032248549500c00d0610006ca0008082021580d41d6101c0c01c8281d82250304840d4140c50803940702c00c10070800141785100c0f600504146269041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 419144748 1250 419143498 419143507
    0x3030103200a060806130905102406030c110c0d120e040207050303061f08060d420c1403070e03030a0909150303023f0415050a0f14 58
    0x12901c2c04115921003000300318a1010b2061a2806a4054503c41c0e1045401c000d0500240c60700c5540d41301c0740111420036a581c5000040980095242c43c0e18916a28540d00c450b1343d0b620350041c0106500040c8000203928920f204d600180c02241a13500d2140080c040c1450900c140c549861b981a00350955052240c5048500550746a038006002e41c80d010b400910b40ba403030004188025110204407210f440d400031403070811034642001d042c603084001070303c0c5d50381003803594605040448485544c43e03a0031074080c031582080401c80d1900290151016050940350400364810b00240c401c000a008040341c0343d1700440c500415100082c55012640d49071189a0a060101180c1540d105d03020010010340d4103101400700b00e115001d504d5014043c3d0490140e400d1441c1c40080d180c9510600000e004c40c0c400642503240d0550408201c00c00000f0b110a40d80c0f14240310018645078000d00c01c0040d407c802c1c50b0b844682c03501500030746120000c0ea84429000e4490700f00221130000180c40d640c3c400741418403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 419145998 1250 419144748 419144813
    0x15050f0f18010608030903010b0303030705040e0a0216050f0d02030301051e0604091104060305130c0603020901020c040e1b09070509090a2003011806030c090b04021b1509010506010203030103 84
    0xd07030f00007030070040003841e500c2418005140c25550341e02c9040d40254010400e01151940c0001160104c404d2410082815111481540c0c068418580d0150503002d4105a440500c9000709180784041070780d404603000b140300c086003603860303000034880d0350f03402140d0400c107401025001c4413003810300400a0049252585902c4104115503078070404101c3c644021406010070741c0c1510580da0000103030412101c7c0c15640f0381c5d5103103200300c090045800f055000f2a00d02c0c0079900030400034071400d600401c107001c1c07201c6202102d80d8448409420701c90b070400f0001629041d0410b024158050039040d55207a1820004109000500c00060071020105507100b02041501000007054003400b0707102040150341c0d51520f00013071380d542401a94040344601c1e2900030800925011200743c00c0f43d034590b6002c2103070240000018001e005a070308070500c28070500e440c152282d00c0405d10107801c0d4202d903002100c90310350400c29400ca920448009001d40d00c10030050000c180c2981e020b4541004003032a40c4411440f04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 419147248 1250 419145998 419146001
    0x50a05070c08060a0522050a080c031201090b011202070f03030b15071a16020606090a09050303040605011a03041212020f0c0c0a090c08040209130b0c0715050f0f1801 73
    0x1160142a0165179005006980300010300c000250900c0b084040200c030720903120561200d610b40c03c010700c0402c00180b03066841d40c0501c01d5885046160581c030a4a42e55802c0f00b1018041c10001c480c0000c0005c1d4030300116012034800d4582c801d400490481c0d0400c511b075000d500402d030042d03107203a2001141d88000b1031000048001c00e4a130340f103000c2c0151104a030a4098915480c0940442030b8044c001c800003001513070016165034441000c5910001e0b40d100c80c92402c0052401101c05032003400700001f000b0910840c0d4214904030341d0b0034060300500150110b220f840074002910000c01c0950005103140d1828410540a0f0484040b44001071a0080d800142400765018108811190b00400458801486c080901200401c840719043c00f1b12503807100700600060000700001c1c070550124000c100c40c1980150852840c0303a00c91310b080ba407802d102d0007a00c0c0a41003100c08a603e08508a081d0581c680d81c0e0060382d0003000c1c0c91a844809480b11082c454611034020310311003000041d0480800c0f0107209 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 419148498 1250 419147248 419147251
    0x902090f100f080f01080d080c0c070e011a09130c0e0d0303090b01080303090c01080a020906070f0605011508040f0614010f06090b130611070f0b09030f010c050a05070c0806 76
    0x60b8894901d41c0200800181c441c41e0300030480840e126040004220741e02000c51101c0d09800d0302d24043d40203a03503483d81103036507010395003500070644910040070a05000c0310003198144d07a80c1583c0712100c5420300403050070034801c500c2031580210541c2e5488440c501a504022205105400e0540101c111400469000b80b2240002d030f00203a10381404506208075a0700043c09000320030095855447e15007041540c13210758920782410230a69100248a0394281d03415517895060081001b940d40156052000740c540c0c0d00441a2902841c040c00000c540c560a1900a280b0036540c8940540313565030344800da03003148280d900b44c9500e0380761504040c0c080e8810000601038120f14224514076410000e00030030007403480d0001200b0410030068640619100d0b540b10b03080b61038600e040c42400341381e02c407041e0030070180f603010240641440f07401141c1c4071050b0001e800401c5054040303070007001e00401100d081c0ca81803207094003c118100182340310a031140c0000c02c84140034000d1840300710769922846190200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 419149748 1250 419148498 419148529
    0x30e01240b0a142a1b21010504030302030106140408150a14040b07030b0103050f0606070309031e032c1203130e041a07050415090503010c0201150602160902090f 71
    0x3021403204c1d80c1103d45040b103080803003d0100800610301d41c0c2c030065111801c071480c0140310f002e20b0742980c101049441d10004000c11b00342c00030302c25401c01c0d00c0e000e4040d40081c01500d0100b606070455122040d40e040a840480300c0386030061a24030802407103010038850142061a8182d00c900b0740420b480c5032000310a00451188139400942d150101d80181116a599110360415007040203100614400f84c2402d504040304440256544503145016105008180d10041001e0f0710300805107a00410024120601406510307640d0400011010800c40c1c9a10320b01c0f0601e521540004030086400d145035003070786551032541102c8c9423501c01d03090202e101216500161134801c55100b004100a01c0c00000d500442c001503c07180c55040510001c0e0070f5000703500550742d8000240f411490201d1045024400030113014000300104240341400901900b00c019400b082841c00c0c500002e1094030010b00c56691202c02c1514070009800c6c6466034020354807108201b40e1020505400701440d030b560000c801241e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 419150998 1250 419149748 419149777
    0xd111305030c040623030c1906080a1e090606050a030602041701021201140402070b090c030d0e01020a020d0203030717030a0b01050a0516030c080307030e01240b0a14 73
    0x525003001c141c9441d4800002c01d00035420a42e0420038509180c84415074007080c0840351800c148036202103881c1041c80c900d0154815081d07020a08180c4002d182074065030b44960760402c0a56920041c01d00f81c4000003130186901400341d4241e2441c52181d8081c1003a144110000b00e04e05985400286018816400683c0c1240e0300050402a0110030708210b854614904029070500c11490303420200e02e241482041c11040d0184021070803a5170b242e04807994150301c1016104141403034030a0304d58640e0700c01036550091041108501940c0d000f20340750440400140c1c014814070009030b017400524030407040704a805100602c2440d000940c0071817010003441080d014179840e4a041c0101d0000e8a15180c10503051000401000624640c044110360740992070208100c1640003502d42220010480d41010b071840d007002c8180842c0a0307154100d052a012180000e0141d02202182d0034030008030504d254803000881c12040013405c60385806442d604c240780c284542095103003d10040954400c0c1012110302 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 419152248 1250 419150998 419151037
    0x30e0f04020f18180610140403110f12120f070c0621020903030406030506060c01140a1a0604090c12050106050a08090a020a0b030c210601090b031009020d11 69
    0x30280d0341100c03c01c0e5038044542050700c1040c4100706010060181220340100710500c100c1d200d0324002c0c7c0c03811110725140704040340e6540d43c030f040c6161034040805540d4844c09038a1101c044c6498840040f0015280c010042c0c41c1410741024842c1c3c503584040381c0e800e0000d10504c101c00c007042e403e0407440c00420361500c1c0d8002d4107240c1a14180c804000f0308410b29680d105028040e2161400001c2d039041e0740042c180013965444c2c09000841500a500500c2c00d55800c212940e4114410b0800d018000c202004003480102c007410100c40c000e0351146000c41c0c001d14140010401c107001508128614031407420b0951080007a160100141c03202608054041600050070b00c4580307600401f915032004091014181100b05540000c403155400e208000640c14080301182800303000c01c08039001034003801400f044131105100d105101c03410440c0e8442c0400c40303030b03a07000410072200300071a0b20914500303980528150400c40b404009401206012101070b60707594043c18210428401000201c00d56140203050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 419153498 1250 419152248 419152267
    0xe071407050f06010f45090201260c250503090118050619050d02130e0c07050604060e3a090f0326031e06040216030e0f04020f 56
    0x40078410781c441801811828410001c4480940c4000b0070703c10b5820101c0f0984484401d41c1d1400002e46c0c1c0c83d0344141800c440f03002c40c070b04200d92145810070b200307807100403099845090740041082921026501440c03900001003005001c00000c00071107840c501403010407041c0e00b900c0080b0f6850303100100c950340c0c40000c0c00846581c00032511198400082c0d00e0750186414040401c3ca0790149102548209019080c241da00398003420544401288842045441c1e00142c0f800b50748001092040501c12800140070030200203003903040303c6803680c0001c020280f5484699854000303205407081070b001405005a945586010a0000c503d48a00c03038540754a10055940b408280d84074011450381800481e2504001c80c4252060001c00c994100a8102c0b010000503801055601c0c00b5901c4400c0020020811555040c0e4282c19031409100c480656000c2e0313200400d02040b0b115a414081050107018182d100180c801d109400e45610040c011210345088600820241d0708220b003080303400d000120b212540e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 419154748 1250 419153498 419153503
    0x2802180708041703070c020d26090f03070e0c1c050c0703080f0601021e010204090504050a0b100f030210110a030e03150103082d0a0201050a0b0105130e071407050f 72
    0xc408000f0604185541883c0001400201a05000901950805086a06100d031981c80c0259110f000d80030303803140300341c10010f0b54001d41c000081c5510403d51040a40444d04001070701c04150b5500000411058940c01c004440c0d64010700f440100c180440710207403200185500401e4051158031031400d0f00c7d6000c2c0d2802070541c400003080081c10042103010802a41c0e400283c007410000444056118150284626406441181c101c01d40803410300b020300c01000000103400f01001e018000740340d1640c0b110800c07032181d05421310aa50b048906001c1c14405460240880101e07582541011030410420329200741c101040400d040c1c0225001c001c80c46100d007001d110000004038400c40079840c6605664600c0021301030b251a40344492448100410010920501d200c0030b1468641110f4440100d150000d01a00781164015205070500c2c060580c90350041c001d0364000c079502101c002109080208510700441c000b04035104005000f107648045400a07001072030b40da8060170140103074800c3c01001c0761 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 419155998 1250 419154748 419154773
    0x50106090806041110050d050f0a0e06010e040809010c0605040f02030c010504050117041419031e1706060f0706200310120215030106050d0e280218070804 68
    0x1400782c00c081d08000004845041c2e2016051089519944001817007108031800d002c0e403800307214501c0c41c1030140008141800c150f648201108003091060f011441d07051a11441d00f886180d01d0f0300043c02c00310380051440000b6041c0220306242c802900c0d103240e21604191032052f9030a807240d08201c1c1202065040a00043c02126001c3c20203030719251910340001d20b00b51004c2c03081090751000f080418200110074000c1c0c041d07443d1200480d20444260035600c0ca49524020044010864440300e06888080041c1e11802001c2d180d140c400343d08101110006003641d004101c141d1080d420011031007902a1000509419030181c000010f001c0c41c0f43c4526441c1030f012030503a044401050040084010b5441125420b0f1030319130015014071180d40c03010901d000e1455511865144cc04000892a942e2041c042d08034407100f810305001305d1014880064039143c2000491403031740010500140482070f0310003801c00d40ca2001c1c1010b1000d81d84000810f04584007924407130000703181d0f5001d10060102688540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 419157248 1250 419155998 419156009
    0x30604060501090f031e0f140105010e070504050d031404060e0103180231020a080a0c11060115020c04110705062805090c090f01170102030412050c07150305010609 72
    0x1c031545414146180300c104901d00c0001c082e41030591201070011811080341040f0b9900004e01e0803510488c0c80c041000d915003424404996280100005244044a1920b4000c400ba902c405203003c1c244020310a0301c21820806805200d00c4a003d0311b450700c1550010002005255220449a0082000101a20480782088042c84010392070000961703203103043c1d0011203d00c0d1103500c02a2100000d100d03850b01c00c034a81e0440561021540c231a040d038000c0c02c81c500c140700480c02003103450002c0c1030989104103044141803080d1702500041c4581184001d9180d10034513030703004840200403280c0020b0103440d150032a040841101040c04010403100300710301d1b42c10030380300804540303000c010040d00329492650701002c4003c0d5843d007001c5454404107200c07021603481c02070030244013490078940707000402c0403c1c8520001100612954801101d040c0700752401154006100b02d1069020362b800c0324281c1240781040300340d001d1104005091640070b0400e00c49200540c40201c1d043d850808041c0070300100c0da000d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 419158498 1250 419157248 419157257
    0x60908010608160b0702180f10120b070e1504081e0307051203130615051005070503040e1506040602010b130b030d120216030201050114030d021209010c1205030604060501 75
    0x650b0102c0e04081e000f20156040c00f861991140542d0000480740b440091031000d4020540c03041c801c00025248401380f00700c550303401186445646000e101145a4010f001a0101e03081e8004112800e00c1004100701c1b1000040c100c94040040b01c107440401d50050340220000c3e0700072408801e40c1e05600c80421105050300c4042c500344034040d124540c8449940da400322a0590000025010a80c0d40706507440442d00035004010b0300d20b0038031507003200b9503041c02018424180e02002d00350b6684500221141280c3c0040690700303007480c00d0282e1161060140850b6420021246074007800d072a994007510041c00264000f06070243c00b14244443e00840c5100350807642c0c201a0b4440303042c0c5002904c8a0202940e18108540c0001070740c800000340590040e220a80310361440d03070402d140d415084203050302c51a040034000d08800c40101a621b5800440b0720003d80c0200741c501b0b10403001c1a01810441e10181445000001310303580e507041d0000403216240210f1301c00300a02c5602d0405100d0400640300a081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 419159748 1250 419158498 419158513
    0x21060e1f030f141f02070506010f0b091e031f0501080a02060f0a0207090e03040f1d01030f14032a010504080301050d02010c0203070b031803040f0504050718060908010608 75
    0xc42003141c01d82d820014015401c440a88942c2d04401c000400701800c68403540480d03091500000c00281d801854265111301c030702c07030010800001010f0210221010011300c0e0b0702d05840300c410303c000c88868801e000c7d000d00341c0744c0e416000d68405100036102c407603070b0860b106801203103680c40e1340c00c441040c0c00004031a44241c0a000068490808545168000c009080e440304a0203000b00c0c6002c0d43e6400c9003880504281100505000000282c0187c41d000c100c112071880d04e80341500c40c41d04140c440c40100c00311400040011594041c11410010b008502028041c0082d01455245602c032001d640006071402c24502c40c42d03c201c40307101903a620501d00074045410940c5a54506003c180500f520441d0014000011603000d0060b404550754054151102950355401903001c541040b02c0714000e046000c60030241e40540070044505070781c3c842161b0a03c041c108400c0c403008060040c886018041c28160000180c851007481d800140101c1d50799000260070043c07900e0035200141c0c0145030030f510218 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 419160998 1250 419159748 419159753
    0xd0b1f02030a110a14030c1504050a0807020102030d090503030106090902030403020a02010e0d050a11090705161b03020301021902011a01090b0c160f0504140702030a21060e1f03 78
    0x411681402e00900c0c2951806155529090602e0035090004041c0711100b000d140d04031601101500d10304a0141c2601c12540c019604c800c0b0034035003224004c100789c1114031042c000440c50009000c21a00600c11241026011103000d0704844c1001c0c015207442e030000c0010004258007450b940042d14440c00c0550550401e950040e5a41d8000280281440742810715407440740c4511040140041d003010486a001806080034544841c0042505000d00c030046d00052000f4001c8003203d03884a2140018100d030003140d12000c502c10072189164440d08511035000015903000d0021307001e080c5641c80c840c01640110b10010342110200d90301580180d05000c680303140c176a0020540c000b26450700c803140b075480310070103540d40c01c011103028100c42d1000d00328404103d00c4403280a0718262041540d081094005414812307c690804490b07140069004101c06981c45200d113102181d1380600b0f80d0040c0d190448505c00c84c05565140d081a416501181d003000783c02c4045101c0c4008854422154500c92421038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 419162248 1250 419160998 419161003
    0x60f09020423010c02241b0106050d03021b0112061403060109112502040219080604060f0915080d02100b0d0308040201080405031e0403021306050603070e0d080d0b1f02 74
    0x554043d20410b003030102c40c1406c2061040010202001e420150350f100d07000640c40241e5088401003032034a40c80c0100c04501801c0195825041503007580050440c442a074000b400e0300e25503103480034100403a140c48800d520324a40a1500a899120501d6411005e0300051615000b0140e0200400c1e6040c9408100c800e00c0c0e6804035030910208100ca448504115a040c07410800000c20080d0020b1002a003a440d41e6820040700110b0f00d1035603200c16481d01c0d03e02c20002500c0c1c55000303018038414826420080b00c0066030110303024a000d1070700442d20326524043c15082c40c00c3c0840110140e00403560000d90103003d03104454814404807006010002551401410100c00500c002d051082c0100800e050240404c1601c054020000ba03401d0340c400c0040c1d490700d0a8100b8841240641c924508004806095000d44019180b014150a0650351403c0003250406e42c5847d60580004480303003240045204040182071910750341301e021030710207550000d00124074a450192020300e820b83c0c0f555024141d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 419163498 1250 419162248 419162267
    0x10b0a020d090b0a0c051504081e03190b030a060e0601150203070506010302150715060608240907030f1113050102160306050408300601020a0b06040c0201060f0902042301 75
    0xc0740352101c000c4001d450b2640c5421554010118158001f00400040203145002048418104424204030400c81c04800407103000c140d500180c1d16407121510303e0302c020254001e8030402d000500302c8901c000180c4603c03084a25580c1c070612903800440040c0b1100f1804a1070b44041c1040344025441d02c0307800d8503040d44441c01800001d114100b40800d10a07100d142c441076608080c2c01c08d1409200036201780343c04000384160320907903001c0b914200010720310400404034603504c1c51b44146640b0304508224104a000d080040c008000c0c1aa10850000320040e40d104c2c0c005000c00c1c61201c1c0d41d55900400d03d00041c40e10f42e6011504640c0001042d80128900214103821640d0200b00410951601e2405402601402e20580d91000b8500b40c2d0690362040d050118001000d442e1598110f0380b9003c004903214400c003140601486054004560182400e500c202810900381c40006a081d403100c00c02848852154030540c000c1d07401080034031040b000000600c2541403103203403c00241550368006400400b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 419164748 1250 419163498 419163517
    0x62206050c04030507140306010e131104020f18090f090706031e0911090a0204050d11030705040c080f0906070806040902010c0503040b0c070909020616050c0306010b0a020d090b 78
    0x22500081441c642038002681c001c3d503400020f075980c05031a13981d4180044210f000360751003407280d80000181d5210b2101d070ba601900c0501c05500c01034465031514030807401000e0fa26a0095401c0149006454103240640141e11034100c10480c090103850400207078002c05400030030198000030912100c00c01c006804c408072441c5040100b0240d000596a0341c11111401e810380a1a0a000300c8504008219010320102d0740d049800fa12240c45016202040340078a0180d290804441c0c0c1c200c101040490428150082000f41210001912030001c102650100702c01da1000c44e03000f0090188040c03000304166404500701c03001702050301c0e0200c0000c021001c0504801d005a503522041e00a591103590324110041e000000c0300da403603a841d0004203140d8400f5442c60503c0c01103000200d981e1640b8040c0e00c4205400070000c81c100705051046000d914221002100d952049403019002038038103000090003440d40c2e4000079110008050060300b48403901111608115440e0800d029038450328056450248 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 419165998 1250 419164748 419164751
    0x160c030c0302030715020903011d07140f0d0326130f060905070b1b060408040b0913090506060a061716020f0a05032104030c06020304021c050708062206 67
    0x3035641c1420b0b0300314410400b02402d521459400145408a20b80040c090346400741c0082280b40301c0c128001015203020b10030f4400542007614100090307990944411040e890080007003829840b03110002d41d038240c02c3c0c00c0460110f40f000605192001c140c0507504490318081c0d2444404c2d1500c03841200e86036400e840010716100c010721801c001c0c0700d969480505a50740c09422103100e1900c2d1100c624641c3c01251181e41d903030740710009000c008200459103601665122014500b400d0030810707104a41c2c0c001c9450503070452078403a203001c0d003d904d131f0040c2038045000d007019080c90b0a20006010f0b050440350840002d20600704824101c1e82d41c4980a00c0c0e1210400d420b01d0862030600e07004070b00381504d9043c18541d074070901c1004418894040020400003000f020404400d014040818040c140b048401601240d51484040c0204039103800460340144010000d11030020300d9004401c6030040c2d00025282c50b070045c2014401e5140c10010750b6008601c024039480480048422402030308000340c0000c0119 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 419167248 1250 419165998 419166017
    0x1206152405030c090d03110c030d080c09190f030b060607050a06110d1104090f0501060818150705130906141c230d1b0308060d0b090106030506160c03 66
    0x601c808191303840240b00612070005541c40d810024400114140c0035006409a035068003080c2c03a001800340405a050388840303800d90f0780c1c440c00380e501e0f4200c0d41540d0340100b0b10700c8008000700006440b04001e0403d510091807914114146081000401444240528030400103040070440000d0b4900c4a143d21001c0483d1002c03c5059801c2540600041001440c1c01c14000a036050905c1e000351080e18410041042040c03034820b02841640c90070300c01c0601180c2118042000d40d0914060211040383c180210b941801b030840110440210441d081000610045198501440302e450030b03030300601c803409061183e40c1c24a40540c0304030807803003200c42c412111800340d130840d441010400d135070750b5822070028aa0b0341c5642051640d0a907201da00404079004400c0d1a114003805056943c2c0030110554100c10281410b03a0103540600025100681c407043c0c0690460018009080041c13107403c0303c60011030854a9850514a00b800c0a070100100d1125580303144a15036001c50003400858040c6007130f0208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 419168498 1250 419167248 419167261
    0x501120218040f0e010b0402070308041407150c11090f060d020a170a051e060613020904090501020d0f060515070c0b0705030910020c01090915120615240503 69
    0x28030008144954000f42400c03001124144070340d00024003410b01c00000c2c00f59000c1402004100e01c161a8001c002c6612270780410049550500d03050245401b0000311400b42c0d49510401c10050403c5584d41d0001d0303036200181c810003c0034042110141d00c00d4546070641c3c01c00c400b03000b264680090096000c0c9402003003140565480540000041c402c5e4080100c0c00c80e20b04071126142c200400060f03445102d6000100c650251442140d90110b0303004011300b070543c41340010808009020050102c40301c1d000c0c4a002c407030387d80e54819500e29910580006076140031240d4091b00b0f0f03070b041d80100000207140060400c43c1e611550a44191121503c2070030b591070502e441c120041d82c115402200640d20081201803c1020000040c40e10a20458101400ca240404100e030b540c400c041402e40002d0040d0410007541311580c00c00d41c00e40b48403201003100b0700e4076000c448a0040c01d4481c2500d420352104600d00581403480140d4019102000011120a140440e010700d43c8052803a140200031001000940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 419169748 1250 419168498 419168527
    0xc0c300c10180f110906190302190302031603030f05090f060c01180b100e090d3203011d0c07030807020115030b0402030c030d1704110d080c120405011202 68
    0x9440c3c2c84154800c01000743c2c100884800c01002d8035900841051010441920340300b03840541d80a28007014890041c03d5509210b00341442100c0b490401c0030540e40800103a070148800003c2148820384142c8603440d6080003040807400e41041d0301442401c1158686030b4071a03910060002109448266403001c065002a006008842c800c8600086d9200d0900821501c20750080c02410702d01c0c104007911303448160b030500700340c0c058503d8041c6a00c04040503800b1801985055899201c0c203020001c4080101004290940c007810800040d460000051000301292010050f014902e8040d4031f0442c03814940b41000b9105011010701030062040000700d5091003504500e001c500c0c0007100806582d92803400f0b4107120410740d000c900c42d00038000c000101d410300003114442100c0c1c49c1d8418403030002c102c4182c02d0902d4050310540d400007078140c8901858a4125a42103510f20508205546000542c605c03820401c10080c20801400e040008100c0ba82e44403001c100003058503007006075a04995009001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 419170998 1250 419169748 419169791
    0x1050a030f0218130303110a080708090a05061302130e060f04080c100b0111150a0906020904020c2506050d0c1b05010f06170d080c0c300c10 62
    0x30f8050002a00f08075980c1d1074481c1480006100303460900c11109007c08440141c00307212010710009900c040090042c602c24142e0640000314001966003da0a40c1c82d49403c1a10032155410f5a0101c2820076086040c00c200740040190100c1c0b003000000d41300352100781c0b298400742020300e41962100200b4180000041241c40c050a064102c0d104829404c0c0d11101600d00386031124085008400c0e612658440413601c180b0780c00c20900e158556a6070048108001c000541094440d0b40d070034030400f511511644000c10b25580300400500801c007200c081d10201005030551158080003901041010f0754110040c0c8242d6a0b910074042600351101790215051982d44a504600010304d56800041c003506510107102c201c0803400a0088a0b207a00c0387e113880303509450303245c0300e1a4030821040301038030703c12005541c022000c80213a5140850740701c6038503e0094428010440c0e405166450507488104004003a00d22105058a500780710800084640790550100c1c188103a030344030100c0002c01d600c0f060000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 419172248 1250 419170998 419171029
    0x3050a090e0717090c01082a040f050306010b120f0a110a0f09080705060403060f090c08010b0a090b0112090819120c0905150d060306020406020609060f01050a030f02 73
    0x689061600b40d42c014010580c45291000004004002c600101400b242c401d0707040f80d040c2c41c0d12003191185100500103664a000d96958030080c2c64100c80843e68020041005044503e8024826400c1074201418a941070748440c1c05004200458030803141e9101c1c0c2e81d507209040b1001e101c41644d8015021015081e03030040551000000244c8800b62038001c108108a001e2603510000c0c15515000c040d070751040140a044e42c0311005000400001c7c1c202d402c1100c2c500f078a0400030518102950b69410804840e810000199449200c07070741c20307401c0c141c1c3c1c1c80c4010803141905002d2540c140002905031f00006001444250301d07041e8041c103202c5001c08444201c1e00e104050480210070700c00080684107241c07440100c070340c02c0001c1c1981c07581c8120241c070160740005041d5081420003041c0441107900000d2024000381d01c5000c0003000c030361603101401c01000300345c01509081c609901c04600306031005059844560042005200c2c1e03480d80314910f429a03900500c0138040d402e542c000a500b064891905 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 419173498 1250 419172248 419172269
    0xd051612050a0f080702210405100c0302010b150301150e1909050115090b0c07091b0e12071802070203011a012c090408090a150e03060c040303050a09 66
    0x140d034001540a0010000d600260341c07074903400e400302c03402220310b000c0507115a030040c1c3c4000b0140c50404403111a9031104071413046860701c1c007035403000402c401c4800e484440f03011441c8070402c9000d041c0c081c0505c814142c0d045988984103181c19034454620300040c000c4040350300754400112051401b40042000b4044c000b0141564000883d41c8a12002c131580511594582440d00004484d41400074403084040c00b900e038208004d080280c004080d422007496840140308421002504040700e2188810440682c0a540c0084e51a281d001e008075400c000c01078000c14094101c008007100c042564015500404500748500120b40c41480181c00b400c40065859481c0ca0030707801c010440d84103080f030ba208080e00c442120350140003050f80603038000c001d071989005401500315240d03e8143d451540c424401c00c41c05040c0040a00401c0720409981c100207205090207010945264012302d55000720001100200300500c2c001403250454015444010103021020814183e220b000d80c0442d80981412000e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 419174748 1250 419173498 419173523
    0x1507020f0715030905060a0b130207020f1c0b07030903030b031b040203090c04021314031b0d08040b0d0b04050a0c09031e080a030614100c020f0303190809100b030d0516 74
    0x46c80f170003c1c0b61182c6024840e603c4009c2e41d40f2030452500a40c0d4520b43c004210b20703014044103003800380b8017203503100126900030340b144000000f592161406000b0300d4203036000a520085441c0140450fa0000c4100f880307507124102180d0900f050840710100d01c8010340300580c9030f031581101240741c80d00040b09198801c3c00412042400d03148a60850115102c040d1509504100d140500d070b200c845a840c031804104a404105545040403514100414841c051076850295201000a031540061081e80803441d1515103051452170540620350300146603010400070010b944002600304074051100410b82640d01e60003c041510054a130b03481c0580001c62030395a2100d5000c010010304035030155551802c050700b106031075810302034a80310410403562101140c003840c5400300f02c00340685908165052000b0000201d498840c0444880c4c2d813060b42c2c903155014200700c074042e0b0400041c3c99802e54003030310304120705042d0b03500020000105009414241d644d0300005c40030f9480304016503405440c0c201f4410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 419175998 1250 419174748 419174761
    0x91b1303050a0b06060a09140105070204050405030d0c02030313170904090b07091a0a08090a12021608060c04050d03050706060308071b08030301090e0c09091507020f071503090506 79
    0x50607002c1c50b4414040d20300c45503102e0080214034010303440c01c2000654007240502c01c1c90210050303001005414105075003040040c0d400142a600101c0b41284c4607080454040c0f1340307030981c0c022400d40e006140050740c210714002400038541c0c1a03036080a4084c203a1a03060950050394241101e10303601c0301510a0000d1074041c1041074140005480541c00130b6403c0303500040100e4082c80390192311b0b8101240c1c80c0340034004801103440c0580030340151a18001c421580d00003800c240240c4008140540241c9064100380c1850712504419078812699030304440100030300c21002d00b04842c15106c2c102c9030543c510000c1d003012a4680100d800003480145084008000d102c0c4000250584601c903121101e121b03000184081448040707441104015481480140000141034000c1841752240004980a00c030b012400204210710988200415406c0303c861180c0290141c880c0035480f51090008010401c5003903542980e609142c8550030f54080c0482145200510030340090a410750094102c1d929030500c203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 419177248 1250 419175998 419176003
    0x1009061e05010312020708030f030a180c090c0503090304090504050304030f1a180a020402031513060e090f0c0f150d1a030a020d06090812010303020a02091005091b130305 75
    0xa0100b0342d02c1004d60300e01c404e90b07248000307010b20558100001950a01032540209082500080e080b02a01c54444004100100c904015441210b000d000e480302c1080c0f400743c2d00012074105094010420000700100306405800000b110100e07400208001441c0e03959081c0541540030720703000100f043c03a200c0f40480c203215942403050b4400c80401d00b50001c030b03140c01d0301803c1c1101c2504820f482c40d4001c0034034000035103415809560b00c0034501030a4110030550000042c2d03107120007801404d034142d40345003d0114500403200c0b40c1e4094401c80062a5049044810079502d05030f920400d486214071900880700b40c0c03a2110300349486102c1080c42034513031551080c1f03a800f0b42114482c0260582d4400040c441524000031a100c44503005041c0142201315500c8407000b5081140d825580c00302c0401003001c108000ca0600d40c02103000b0742c0a00030154480c81041803a03800a05074003401d404482042c0074a5540c400b00740d8001d0006803e40000440051840328503010315070450031080c1c0303501d1000043c000007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 419178498 1250 419177248 419177251
    0x1805041a092509080d0801080d2007081005060103060e16050d05010e330111030f070803010311060319181e03080a0204080606060c1006091b0e01021009061e05 70
    0x6074402e81c2e04d00f01702d4200460f00c0440034401c1000640c441901c1500450080c4100340d581002511400d442411103075000b49454007076031100038984e100311462040000f29115054100e41c00f441d05100140c0b070400802440c1002610304032010042d0b001440c06940036800b2034209001c03041c8180103542e500c1200542c615001c8800c41c000565100200e0b0b038841c06100c2442c3d250184042c0c990744200c0050044400c001c1c60030500365940300400002e070303142c543d04001d40007803481100003540d07139070440c58549500f130110411903004070401d1050000c11000310034081c0e050200647c0001700c1e601614070803c40540000c40103030025441c2058440d50712112100c42400d0b034000d85510f4402c1e1281d182410492059210704c0030180c01c02808520b1503d00140142201448041141c002c0ba002d07010240031035829a101821270b59981401c21620603940f03c43d081c01321401d00b40400d49240000020f500c80b0b04603000c2e800510360301d00d502e404000aa034415400e01c05407a0f02502011012180e480c0113080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 419179748 1250 419178498 419178509
    0x4030b0c0307020705101728050f0a0908040816060f02070b04050108280b01030b01050301030c120213020f13090209030717070306090501020a08011509091a060a1805041a092509 78
    0xb4080101c0651510324000c1c18000cac031020340b40c81c000e5601d181d505402030804803c201e5a40104000010341108100034050204400c100c002d040032303162060150448031000401d00954101e14002c202c080f906e04181ca08942003800c200000c1e80e1030340c0c0c401102010b4003140581000710840c4444544103a41d00800381d190307003a2001c020f80c1400340c00541c2c0074002480014003280314980c1c00d104032031164682e51203040c40505101c5100078000d40400c180e0b00800344044c074902010840220800e6081103030801000000780852400f20011701203034940c182c0e801624484c0480007400ea911003000c02c4034000868000d80104468030440c6000c8d4043d50050b501240099081000400d00e414402914480351242d501c1d0386000c030b85006c0040b80038100c01e81103081c0c89101e1501d0b15045466517001409170310000c2c0ea4000400409036051820200c2e01e40080d401035203807541c4850301c0c003051074620300944000c0b11071001981ea61507441a02810403000c1e50391890444100045194001030010151074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 419180998 1250 419179748 419179801
    0x51905070609260f03120907050117131401020f090405010f08070303260115080108030a020307080f0412080c06151c030e0a0b04030b0c03070207051017 67
    0x1d076604011500701c1e5242c0a82604202800c00904141000005141100d294482900e245805008105085412142c1c08480c400290800c04c10050018030070400500400d017003044031200ca444028544400007440440d8100484003480b003806080e00d03000a0103040a4025541c1d00180c2d549440240c120260940c0128189000440c00407000940c1100b81d030914002800407a1440d10210344503000039800c02c00c41e00d00414050354625885200d92b010b002d50071885d100714590408000c0130900141c0c002c6105401c240070000d040342e170110484484a801c912103680f5882d10b60601c681c68882c0b94840030040f9105d0b00c20804102440d00a04828244801650405d80e03c03901c0c00501100c5e9008165408242610303030101d202800341043c0c5d650345c042d00c0c048ce42c0030300c18004200795203025004030307001d00c4011904004204040d09a540d000703075500840d608609115801079030303410050184501c00c0c06021040c1c2840f5204140c03140d03054150724400d280904040900040c5d403840c1e4602e1103d1032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 419182248 1250 419180998 419181013
    0xf1f050109110a05180901090506011e02070b07031e081b0c0a0803130221010c090b030601080403140301061701151403060102010605040213140102070f03030516051905 74
    0x1d0700140710380c44807076141804140c603100b51010708031100d601003800b200c2e04808030340429030703103071540c0381050f011b0041e140000849003070140c0007401e00c100c90321584a900008001c0d101401d031b40425402e0465801c401000d0725020236203400c1e40c914941c120f140c19000e00380c286083c02c10317074400c40c12400780c0c0b1200140307201070119190807040d601c40e0921007078040d4404006c010002e459400210b6005c045103410180b1244a030380010f00340006109100c078400401425401103907001c0c404e0260b010b41e40d051080c025898071808114900000b064035050014200000e0245401000c00e80d4007507108091541d07403076865060280445811082e015152031b0204008148009621003203c4201410b80b2220702c1810105900c2c100b035440141458115500d8420000d03003912103001070300009800345000c2654600340f803140080058402c1e102d40c1103602c0882c0802c10340c1d007240b200800f982c0d00342c40d00701d075210011103030f4281d84072624000a14074851081c0074804c2030b801511074810f01d4403881c2031301ea65 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 419183498 1250 419182248 419182259
    0x2010b130c0e060a080c0f0910020d08010503010c080a0e0f0f030403050717031605190309031a070804140c06040905070306140f0105160b16080f0c0406110f1f0501 72
    0x15000f101000b8000c00d01d9500410130a0941b44040c00c850011030082501c1c040b4200080751001007111803290259100c01140c101c02500000b5a5024140030740081041700c00884c0b006100c0d00000d011800525958420b14060040500c51b507640420660202c0d011055401a99035681d44207204c16109401411404500f451102e005060904200c40040d8103014455080e404800007414080b2218828002e0001e9010a074400802c1c4140c0070346c4920308800c0c91400c3c06081140340c00301e040b0b02d0b00351502c01c0103002c50300414400e82060b0041e803284408803c101039240351640c1c018015a0254000c01c0015950030190004c0e481403041790780038030880e65200f51b070010140c005810b4a52001801c1c413035444a520940c00360807501004000c140c11401c0544621002841c15101d5014841d10031008024aa42159010b608812807400895091030401c20203002c6000324020b540401100e034840b180d08800400010030400031200c00d0712089608800d118030340d0401801280703140d034146400010b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 419184748 1250 419183498 419183509
    0xf03070f0c020108041b092c030c0a14030d020304060902030d11120a0e060c0307140601051c050c030607021606020a020a06210212040309230f0102010b130c0e 70
    0xca5640c10f84031000e46459981d03074a8488608540324804801d0000c00000d500603030f0b4081c200c0400000343c1424094040c43c521140ca14203235000682d5564000c001d00c81c90340100107001c0c20400c0d000112000e6001c41020000e003540700e002e94018885001000b0700040c4400b6512584106200f1003c441242d01c0321502234a110f032207810310704003503003000c6c428816802035103008080001c4286403a03400f08501ea8005606900844915861070707001044200030006c0f07278000d648141412000400c4550f02d0a000160404603030001098024803a0f6004802c10404000c045034040d4000c0940d4a149040a002503658810300c03200003d0900c0b8200c00160240040741e04294140c000e025a00040e09101064030402c4010ba4040c80841c01416440c0c081c11181c4003420610045508215107801c3c01d003401007600b400342e0001511889440700201140311401c411007801c038004c2d033701c183c1c0c1200c034480140c0c01031404800b0246c010301051240c400c0c440244e441910f644100362030b990144403240e014001d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 419185998 1250 419184748 419184767
    0x30f060d051f0b09010308031f14010e010c02031f180b060d0c080a1a07050a02100f150e0915060108180709090506060406052b02040f020f03070f 64
    0x40c0542c201d10b5000c4584600300c84904040302c001c2e20086111004400031506810099109031446a4080203001a40d0341510007005d0043c01e100b10760103260b06007a45000c0e032449015885041c41281000c01c541039004000040c1441d40050a46005418441c100d000c0d42100e003940040903450500e0038a51403001038004405642c0080c040c0c0e00356590302007840441c00101005480c0c14136104c45c0002c0c070110400040c3d907818480c1007035080300016458060701600c0040c2c01130060100501404001590010710300540342102c04000c2081100d1450f080c00900800c00c813031900c1400e0f0030001c11040900341c80fa90240c02c540c41103407a240803109a1354500c00c0d0035900e090005040e0004a400e280702400c080c0b40560405050f45c00c00c95680307203c1c0c01100c07404242101c4a0f0050020030100313103846c2c4140401410b06446050148080703440d01d00115140e143c40e41c3c1098003605440c400e64880b075000400d0010701c550210754405481d550020f0039001107503c480041d4001e07010030800c1d4071a5241c030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 419187248 1250 419185998 419186003
    0x30f06051c03050304080408010507020a050c0907141b070602010b010809031204020d030516110108071e031a0a0b0c16120809030a0b0a0510051807030b011202040b030f060d 76
    0x19032070310000d6408840a42c0040c0040d58402e80910000c00c508800384201c43c081c0c0c48a40040c18035008502d801401e00d541d400c8028403c80d079410400071030981210141104d00d0105041e5691000d83c1c541c0c649040d01241050b01c018440c280b004201d1a030158040303421800c0989a0000a5480800c1c1075500d1250080801140010350042401800c2114a0305001442414841e050a9426201c0c02c03c0500d40103040e01c5c90852101000d0227075800a8503950001c00d43e14054454900008101154000d01c20040003019511440300031074203410780101c044a0b200800c500c0e24140d5410700071190f9001901c0d10301441c01020341c8014145030588145084a41d04523000d0a98903a42d1904051900105e250980600490008100103282200300ea03129141d507910010311400c0c0101101045072107a00a40d001da40800311a02040b0700101c501a8403180c43c1c070300801c0500b1240d004888109404081d030784200d00104011441c81c48a50140d4410240462080e6450341c0e248200302c1e0064049002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 419188498 1250 419187248 419187289
    0x1b0c080f0f1b0d05101a06122413050a0b090103051906020405040516030b060c060f04110303072105090108070c0219090b0f0f030712060f0c030f0605 66
    0x5440c0c1c0c80014500e00c1815441c018460410f00d2225219076081111004902509669034082c0201004078039201c03001c0c0010a442683c10030303010101c1040c030200060130f032050a00d61401c0c43d45050043d134100c0381c20984050001c0812061018114004c4c103401d96040f85002d081054000e00c504000030850304030b035004402440011402600c0f0404d0455500c000c2e200e00e60204000305017178540d030203514011120074214802d8201038010041c03c644841603628171481b003c10058640b00400602203411124201e0060884d49607403400b07040005100e0003242d01070002103280342c144560100d41204007040f1101e240c003004e400541c22100c6204045400740494103102c0814501446200341c01c046c648064074540d455201a08600514402603002c200995240c040f8620300e0b003010008505c80741400e46410280d000500000303030302e03004a4020208602c44411040307040c451b43d500066100f90603080f08000e03800d50f1020003400703090132000784020a801c014001450f81000d40115010501c0e4062 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 419189748 1250 419188498 419188513
    0x1718090112021807050f04150206160909020d0209031516090f030b0a090507080c0307140306070813021c051501030c050d080d020c0a031403040206040509071b0c080f0f 74
    0x581c034200001910b1070003084000e111a0408980740b1b8003c00103044000c007541440101d100c002407500e407009140c0310601048444201100d40c01692010036604418400342c2c0311511014240700034010b88900036410b208000f00c4a08103a003401c5464002d0710900e00303c14140e0506c040c01d8030780003d46c0c8103015102c6032030002000460100031103550450119400891100310030b480f81c5190101a070410a000c0d006806020840d02d010000300e0001c0c4600041d100c0000f154100080d2282001043c600c14058103d00040c00400914010741d50150b00800e000d4405002001115500644040441d518810b600044040110100030241225404844501400c2c01c0005100781d40b1207012045820315006c0c4030b202c3e9020260300203080400c00100040181c400e890230024031543c5001c0e0006c4000100300b0500000da2a2102290140c40341501d100d003646e10741400450340504405c1c0307202500c803242c0783e0040c1048415000001201c40c803204a400d043c403480c185513196242030380c040700a50700049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 419190998 1250 419189748 419189779
    0x80a050a0f1a0414010c0306080a0209060102030d09151a0a05120c060708090108011211010305060a090213030204320403051b061b07110d171809011202 67
    0x2a040800701c0c070641d94044805105120451451400c0d14121007202d44180c680100000901c02c114950703480d842c052110520786090241c66100b030f2140039000e50b907008000790b941d90003002112004281442d00300410480c42c00c02021a09128007040c3c9107904184010031180700001c041d019449000340700040c100d1600f4200018075828203030b0500300740a00c2030103178590340d23411020f402c803a400780710307040c0d6100b54007000144401c030140c200e0b41d075a40c0300d0070942000c54122206044051420300700061035031103820004450049550001d21881d0000a44803480082c0c40b241d0000c4030320985080c01010910349200701d002a48a42c0310404550030303c1b03443c0404020b0403117941c00a009003080c91a0401c891502441081c0b10391481110360b02c03080500045001100c0c482c0e101c8042d80350b0050508016a950700c40c40b0316540310300e6114074003810350002031095401203140001d41d00c00c00e003507036010f45070500101c07681000241c41c45407810800004840b4103000398008900d80c0284958035445007803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 419192248 1250 419190998 419191013
    0x5010f2a0c051206060301050f190f020f04080102070b0a1802010e06070206161b0315050901061e0f050414071b020901061e02010c05030703090501020c0d0315080a050a 74
    0x29030141d40e540c0c02a507000485031100d007180320b620001c5201421507458000d0a260958101811540c5442541420880c0d034085004203180c4000b0049004a003020811301c0b00c10290080100c03c540d540d000003000514803d056000704052403061149602c25a41d03420940100c1c0d0b03030f0141c10580721010b020303460b00540c41800941d0140100510217030a00384590041207070354001050107283e00811704100401c0c03002c81d0b10641101068413061032a85401d42e070302c0404200c880c90316014815159404900b49135000e400110242c108081c0a201c0b170803e4560155580c903181c403a01444d1001c100d40840d840c10030b4000c038400c4440b1000300102079160048204c6502c40210150450450403c2810380103a5032442c006000301840e0741c8a500c01020244030740811646440540c0643e0300d0860000c04207074200c002d0302c0c0d201d0003070705001800c41d0003824200d0280c440c00c2c0c1071500034069220907101d100e0b01a4004202c2c802c0145040321213603100e05c80c440d0384501000002c0c1c490341c0a0400200090000b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 419193498 1250 419192248 419192327
    0x206071d0303120c030414030702100f051902010204050a0501031a06091201050c03060405060d030905061308060c0406021501060503130c0504020714060a060303080a051f0f05010f 79
    0x1e0100c0f031408100a0340c007103a02d4000e89103a416203400100b80000d1010310f1140d8251003051078040c40c50b1101c1e59001441a5036090000d0f000e000034007800e034400c4c43c021410303a0b101500301c04881c1585000c09500074004e62190162070300c9502640c2d030108035540300b44500380b003045004001301895000b030310400070300703400031881254090a0300407080302c0c1400030700030300d409401c034a08590f03260306201c02000240e500003404039001d00007000c580c2000c43d90001c142c608603402510707040d940b40c0c1d240910b00509542c6420400c4c00d07205101c07d01ca01c0c42035620050044a0b1640c0c217603076403018508000c0da2900428803860b40001e070107001040e1410280c04da50a1200c0c4214450800c4c0d9030b455000c101030b0703000391005070348148140d8000400b40200384060b036070004010500b00882c0d4110b950140810202401c0140c1d11951140050011000800c01062070560251142e144664030b0390390ba148600d840c05076500180c041c111510b4424000e46c036000680650b0910206108100c9102d940710601 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 419194748 1250 419193498 419193557
    0x7061d0f0a030303090218040f0b2d10050103020403081909170a030806030705010c0602030c070c27060e06010507020a1a0c01060b040303020a12090518010e07020607 73
    0x125104049841d9907001c0184019072183d10041400c144034010400c1d47c036142d01401c003030740c1c00710020000054040c082c011613140e80a201070515481d5014404490307950362102941160540164134030300103824980f540720741950b00380a000503848800440590296100083c5800d03401e0104c0002501010b02c42d40200a0514143c0c1250f81d40301d010104030401810101200c1d0031244041007072560000135990301c02d1007036000701a054a0480002d00700c3e140300e41c003e0142c0e54003101141001c001c0c403080301e4030f10303800c448102c040c162036050801448445455800c05101c00c0540e100000c501030190904582d08541600308554501e0019100c80d03000038803c903800085400302088100031100c10407505002618403546803920b10603d142114420340244860583c28401000001e6001443c10b00c02580302843c200e8400400c0e9090300ca10f69681c018030391001003059020214686d0034646412161300518008082e2900c1009a848240542d08000001d07982d0b02c541c522100b0002c8410312000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 419195998 1250 419194748 419194759
    0x20f070f111305060111010b150d0f0c0207080613030c0b0901020d1a01030f0b15090307030c061d0d020907140d05100e0c03010b0405040b0d0210030e010e07061d 71
    0x1d1440c0010b01e00c0360450004102e41c6540b502070141c5940d00a0034405403900b064000c101c5511842c4c00941c455104c0d01c610062034000040e20401c0d0806600710458018003410107104001c454600a516031202c1d000e600a50300c80d440001c1d40c40754a180240480540517241c2c0010b84960341c5171450700c624000d2809030559000c0003210188a01c47c4074011070140f4071401080800c1c8100001010b5075090221410f00504021081d40c0c9640c9001816450210036042c61b0f590f1850035010a040010036400900781914182000601030340044400d41c7d4070b4061120701d0640c2520b0000c03c1910b02c04282c000e508401c141000564013400742402840f420080c03c2d4080c1411030f503905010070b40e4801c803005000c1080e0503d00b0003400e01016207240d000300075451058150743c1060f1412a950040d40709952045844045070000354407034440650240350083e1807103c0c02c1c084071002502410158940e2611036180c01c1c4110459400491094140d480701d5880f0740d511032400300806002c0300b03c944000c2c1e209 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 419197248 1250 419195998 419196023
    0x50f0301210b09060601180f0509040c0510081b04060e0405060a12051f0507121e021813060503120c0c0a0303110d020102130303080702120d091104020f070f 69
    0xe0600b401244900700c0240100002e01e0954001040c800c0241d100f00450078208005000d440d500b060242c2c2540e4080d100c04d000c5a507607050526001070b15600480c0c04c001443d0381c00380816400a900d074411070015017503041c3d040c80003101c20214442e40c8254000190041030301a01c502d01604856041880180040c2c00e841d25180035902c01c0c2506d100490f455440029480c1c044a840b585149121008050400c8a071800d907401a0465140d400719024403a5604040540c80d90000c81002d08114182e00031034484d4041c2280e030382e02d00340d10503a00d40300d4880c2448619072080c0c2c901642c82655809406003c02500c910415034094204003541c03641401003081050094440d012104011802545c1d9408070034010711005040080d038850582c01c40e4010071070400c0c0d020840782d02404480c0c1c18035141e40d59580c0c00034103d090219482d80f16008003000150107011701e8164000c04c170031038003d104400e10789500004100803441541c807404c658400a114107800301d01d071b10300805007850040b581e04108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 419198498 1250 419197248 419197253
    0xf0b040f05030d0f1d19031107060305040303140402030c130f05250207061e0509030d02030d0606020304030c0e0c0d0f09060506030c0a17010b03030706090b07050f030121 75
    0xd54001c1c03520302d0201c590302e113000490b80c42c2a01884032100301d04100500000315000596032200c8040d95880510040382e2040020180f0801c4003e803a60421010343c0d1701107441342c030001c1c0900410f032826030001c0c1c20300f0b030201480c801a9200601440c0e006005000c0d0582076030904c40308080030760600700c0250352010740381701c501124000d0303521a202c2e2a901c88981b00100d01c41c00c01e00302000510704219032040200307014068100b8141421021102c2c900c2e510b0b4034402504580c244540707241c007070301400b5149103074051a8000015002c40d4040020a1001c1c58580200300d80da8007a80c403000d40040042c113020031580c1d00d9040742c03941181c0560901071a10f0420340e589001e40da103001124200d02c1c0d4400f1400e080c0800d500c26260413540440180103440340580009445c4041c5003e446400c0c442028071032a0608251300400031070001134192503d401650a005005242d0f00030141c440d05107110003d0405171081044645030102040c100741940d01b0440600031402c610708c1c9140c020302d84941d00801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 419199748 1250 419198498 419198503
    0x6122a030b040603110a080f07031104061e05041d1018053412030806241201090c020a030c0602280f030c020c0904020303071b0f080304030f0b040f05 66
    0x14601600102000707203030040134442d03201c0c5264031914440c1c0023400c01581035600454403104803a00700400c2c60034008031600207001020715520100c5811074844401c1000c109811100c012100c0c102c4081010610f21a81a00b42c0420703644d50140c1174000d560312142c0b00c2c030594881c14150a070a9680300f40a099030b91003c0c40d1021440c48040d1b9001070174250481246941c0b0501c00f260110f4294030151841e24611102007552900b0042c20b00a00c100002c0068031490643c3d141c1c82c0c0081159200b204030f00101c01001d0b4490251007001d55016030020030401500c1c020b031210040107a00411018940b506e04443e402c003404070072107183e03808100041c45204e419150b100000880700706151103002e0303c4000341a40200d108075600303240c00c05100c45020b42d00800d8901c140201510700b00c030310356610f1000a0031031081900042990701c4600c5050120544100c0102c183c8801c1c0114080c419151510181c0d00c0c0130b5440700800203141c00c0152070004040742506900140705030140400794402d952400d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 419200998 1250 419199748 419199761
    0x405010906021b070f06050d090f0c1701050a0b090c03090705130f05070c02090114150a1115040b160e04060e09120405100c03050d0f0606122a030b04 66
    0x10b200250750303001c1c004003c005104100090101c4d0a03661820741c0b03020409840c5020701081800c17074640d1a44180c050111942186008a40c4569064282c54440e0722900d00446840112402c035840c0500150212050340b0924160301002810100c0342d40e03425060401c0f0707a100800c0e0303904a0080038400503481c1c8030070022150820342c40d070011603c10500c50074a01116402810081080f0b280312085016850384110a81941e0901e202ea80c40c030b40048003c190441c03105c00320292072441c005000700c1c050384d0001e504010240c44006132241542c014880302242c640684024260054041c08605101d818440ea189800b007a400c05215450380680060304858042d40003a8040d14860304014403504140140748241103081c8004d03003054244404a100c007902030490005000031fa1240318141070040068904142c401e00702884510805000d0b40c02600503485820045004407250a11501242c09100b41e50314481c1409a020069140c086a000f0f0000315202c0038503555400510030746e2990301459 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 419202248 1250 419200998 419201017
    0x120f0b0f010e0a140403030209030325020405180d121418010c020327040204120c03050d110c0409031115010806060105090a090207170d05091002130e040501090602 72
    0x2105614141c02c00c0740e0528000d000341d10491800b01d01003c060f05603080650400e415150050316940d640c00400d02c1c520545487e0200f80050109000c0c5d50340f01e288041c2d4400d4030a0f142800039482d16683c2c201084080c0203068800c4c2c000c6880c00c69001e100d034001c100b480564440200c2d1128042d4620503044074181c0b001d5448042c0d00c5a00c00340c4c01024004c5c00010380552006519002c5184030303d842c03011400205c04001110500110b82c10390350307601958007800859001c80c607040d12900e00120f00c86039501c801c4480b401080314000c04180030b05c14250441d0a000050213013010020108002019521030890502400c03290703a010440b400c000307004501008540d260340650400d50f8851400d04001d1440341000310804c000d0009484214002c0c0448802d00320141c0c642800e80340a4040111822280c1032694001c900403c244080741c001c41d0007200c2d041c1c190360321060040001d0040e486090007140105081c00410040b4165411019900c44e028500008094455566560582e4010040e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 419203498 1250 419202248 419202271
    0x1230a0504020a2312121b010605030d11010c0f0e060912030a02070501020c0f030706080c041a040e070c0203031c090507030605040309080d120908090a0621090c120f0b 74
    0x440340c082c02d1590a00c000d1312480e200601c10b10101000500440c840c07411411f0703014003401c3d82d50784d000000350001c1c00544401002e541e1446400400104031400010303040001d982845110950a4060010401e91105940e20940d09000c414144491a801461041d0f0444982940031038921002d0005d850700707075195400341500602d0000028a009206040a0b1083c1240c001014090b90700044101c04c42d2090f08196816988418200ca0907018651100d506c0240130007026010521410042c0140c600c030300d07140c6005031581c54003103078500c50b8001c00940540c400c10260300714494070811240e01400b07032000421100360b2561504d04280c055401160400d40710004d101c201a080a01003000d8580d4800401a043c4005401410100003151130030704c0e10380d50042c4c1d005109e0032004983c0146000303042132200b030b90307036a130010321080c0d80282040d040d031110210803080c484140035500000e0b40121841411034184001d0200f1018022400c40755000e0b00070400c00001c8851000d5440341104409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 419204748 1250 419203498 419203559
    0x2210309011a06030406090f050304060818010c020a020103020f090a1d2820030717060d110f12150106081e04030806061b07030501230a0504020a 64
    0x3040d82500d20540200504290b000c0c41c8812580703412081c2c3e5482030b001140440c1c1e411035030814460410400c04080d1290200040104031203800c4121b29010b040f07030304000d13003d84c81060401030803103a1404c42180140c00110244001d90f105c0e4026103e034002d210985840c14040400050000116070300481e40105a130000c0d01c000604035101d0b641c040017440b0f0040c0314503aa10100900024072847e0745240329a0b80c4034000f054500a0003c5403d8082c0a1340c05030349060105c4043c0041e4002e0007000381004802c03001950f242840100040643d034000e901114801e24001005200e0229400c6941c11070401503040078090802c122038490082c40511030411941456401001781200412443c1c5043c003c0302030300302c5030a038080d81507403140d014034109203a0b0300c4030800a81180700b41041c0d0803410000511000080304c0c0481ca49040700c2c880d000070440000103020101f40e031005009a0300d16000001c001800d003000031380042e40d00c548000d0420031301c50b80321858405000000640c0300d001140001d0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 419205998 1250 419204748 419204761
    0x4022218060b01020601121b0306050702010912180308031b072105031605180333070504060807030603050a0b06040b12031b10050c12010b031312022103 67
    0x45400b18100080c8054241981461581000b10507012401810121001100c40143c45601482006180d00c80002c1c0000d01303010324002d000c3c0c5140c00007501d50701d41d1070001902c070f140038076402c01c000c0e1519504041641e1841d2100c00c50303038200030400d082002002414001166001c40202500d038400d20011001041c0841c82c40200d110440b8040e0521808201384900d100d82802100b04042d900d15006a46105000d4030308051010301c0f2060b40c00d8815100c00c0700031301043d8011201c81d50103c4107015107017061041280449801a10300e440803401c100001c1c40118400d000c0b4503440344260801040b400d96030340d2454a03204071940e0030303a00d041040d410700c4614581805204502e0364121011291111414440390301d901c1000010a0214520340d0f08501c0070001744100e04c0400c5220404105914154141002c1d03544103040b040b500c82540000421306849500a9a02404101d084041e0043c4581d0346d10034500300300d51241c0d05511801400501c070088240004403203862103041c0030303200d04180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 419207248 1250 419205998 419206001
    0x20091c15090c0314160e070c080c030919050126010608061801140a05010e01021b130e03030a0c0906080f070311160203010605030106180911060408010510060e06030402221806 77
    0x6d170001d46110900310180984c160380310180d0718801c3e4014025964801e46600070703520390f12030b08032410b8000c07a40490b200c100020001c44c0401701e0310300380c8480a204205200c8680d081890909000c030940011005004051181102d194090303400350440e25110307a115454004c0e090300341d010184010741070b080d2003c54180240610003c4c1001c3c20480c0c11440ca001c0080d4413003a0f031001458580d89240c5200e84160f560401042880340400e40400c100c041d0083c919840f80e2046400d0001541070042007804640b19140a000300c812a0f502c1400544442d6200006450013403d0344003095100d01042303002c0803230240145004210740c2a00758001e001c0d8818142500c40d00d6000e14807a91400000304000c91480411904100440c0e100280e085e065140c03001c198070080072101c0d0420300114010070307500d005501c464041d01c08200340380400365036640700f19000c07903a1030302160b04a0340500204005040403014009903103c000703000c0528205803102c0c442100d1480c050403011480f10b1b803c039004d00203933 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 419208498 1250 419207248 419207293
    0x10201021e040f06321c0213050a030c150e1e01180f090e03040806040b0f150d0b0a06051509040e0304060801030201050c0120091c15090c0314 63
    0x29810850b1042c4540881e0600e02c882200360004070041c0703012030a80024004041301c60b40c034254003036406c03040310031030074034000b5009402030041b0500c400f48042018540040d404044a038001c0c540d01ca10350500c4500410f60494038178200c04c1c0a90100c03c50382c6a80e803d81d01c00113040c51000700342882807040000409080c130f04000202c80d58034001d42031229601042422080c0d4520b81c102150040002d04e58520710b00c2903611000c0f55000300e00c01e01c000c00082c0c19035180a2204002d00c2c01454403070122201680c1048074082d80d10504169134000050800d007003241d440f00b000340b40020700350351310b1010942d455000444007044dc07c0c001442e005501e4180708100f50040350100840c00c0504105000c1c2481206002c06070511101289150010704250828072003001c2c0051585040f81c8044c4002d101c0d904100000d0f40301310782030a510b081c80d408080403015042e402c04441000c42c1c074000b0156000f4816000203484c14007603c0404400b0503c1e052202208003001001458030f80c4519000d84041c040c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 419209748 1250 419208498 419208509
    0x1205190c03060204030b04060b1e011103040312020706260406180b090607021608061305100204150905060901090603020d14090d022812030227010201060902040b1602010201021e040f 80
    0xc078140242e081102c9003201002010003800d080004cd50f08400d41851402658401445201800380c0a00500d502103950780c100e90098440b2909140280c407915075004200c801144c1c809110b00000300403030200d8202c3d46842200414485404159445081984500322001f20b40342d8898010310051560400c981c44501034101c4401d40340170305003240552201c070090302000ca00c4469491110600600b80003480d41d00c009140210341d19030f507440c020120310303c8100d4240d0204000c0c610000e00c50820b00f044035840c0c6016910580341a00f000000d40094206552298010350351700e00748007401c0920303454140505008030040c2401a0309140080c80c2034012440301c900c507100300001c250138044252803c9030b03080d4400d0026155441c103003001c41c02030041c445041e00000c0d00340c240780c00040011003040003c8030283d00a1007201c2d100c00003030090703100717500c100e90000700c0c01c207d00307545003e103551000850380c0b05100141c82c003e604225a140c15845141c1c072805030b40005001c000b5540840101d00c003e11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 419210998 1250 419209748 419209759
    0xb07180305030a090e01061b060b06131e050105041d040303020c0a03030617030c19110916080702060606040b1308030f0301090606020c060f0d0615020a0b011205190c03060204030b04060b 82
    0x9216407140e000d81609923400400607500d130a0f14010300d6031048140c8481b09949038944060355a64000b002900052001000500007402004196540700d4401c4800740c8514083d0401c0d4201101c6551101c43c000a00a4040503401c0c40208851042840390307140440c001d64010075001d04051300c80758035407140211075030799520030080ca000d05036021aa425110858403140700ca02c59560030300c2c10040b00d10840c0d09502500c1082005000241110010804000c5070340754011070b40c40340000e9aa4100640c0c0e0903074404400c0c4000c00c030380c05000004060054032882540e030311965819100d4a99001a41c50300d025030000300060100b49401c2c801d0b003008003001c0c8018020100004049070751031040101d900022500000c1e09440705415421080080050408070350350b0102065000f03441e07107202d80007280c081c0030080c00014200c002440c13500d4030a402c04003400c41450019030b400740e142c01103c0200c468120111000020034440e1010b00b000710301405001c1018030b0a854180122800a000d05116a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 419212248 1250 419210998 419211017
    0x9010903021504080c0d0804031e1d030102120a06030510150509250f031805070512072103080606070308010905101a090901060c0b07180305030a090e0106 68
    0x1a6002481c40341c02c0a00c00c0881c0c10710b07201c42c109209a4440c0c000c5140702c2e8441c80314104400c56020b501648605c1c02545c44840c021108400004440140086d400000f04005140d80d24524085112800108010300062900340c5c11001c20032110301c00ca0700500305d1950b40b501007040c070505008c100c07100a00c02004000000b00503003000d01c4000103004040c0611000d900040076586e0346c5c100b1503818032040e80d5212040780c0c4030f08010b1081c41890586000642070140014030302a0950465429a62010103845a01d040200340118840c864540084911a100c0c0c0012a01d00082800002c468600340034a500c03851814090204100070b0f00c41402558108441800300364026074039410b644161201043d030b5215002440491035a42e004024001d00c890050300158080c80020081b8140c103030760700c6945da030780d840d0103592540d981c0801811071011680010480c42c407400310310050a196001409045d6100c0d1202455034210800e44404a132100314280709200e42e40c28082e0041c42c40d0310b00074601 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 419213498 1250 419212248 419212253
    0x907090b030f060f03100501031b0315090f0b0108070603140108030910030f0f063008090301061703071a280605063609070c0203101104060305090109 66
    0x51000410b88002c0546000204096907130705203299180d442c00504a0317200010689035100101828030046030b416800329030b51600c101400159204072034000224110000e0300021020291a400c40215009102c94000e54001280510280d018284030300050034403504200e00501282c00403811201c45c28100341c01004268000022600c0c2440e05030342542c0d210000340010b4014158000c0c94a400d24182002c0c1c1201410550100040318004445007418840e1600f412002500310751001260300350320b0f04200c3c04184424020304052034043c0000998540d50010017160940840744100701c0e800006000c418030101c0840c1940500082903c0c4000e824070136a0000d0007500321044442003182c111010101c0d00360750b4400c200800001d044140e940071070f01801151100c02c6140711203001c4210f011031655201d4840c00100c1440054201c1c002610b40d040d041e034064202e40812641403050100c006218032a41c0904410050048070b003540762800d208018007a9880106102013603171404440f68003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 419214748 1250 419213498 419213519
    0x50703110f21010f05010b09012a3819051510090f170709050705070f0222020904060803120f100f0806040204180c0b030702100614090709 61
    0x48401c403064007141c400000b820042c0900380c8000e031440400c0c034000c000a10700d80b040d4000c100d45003090382d40c0018003160490602e0f8000740a40034101c03868500b4981c0000821801e502e49000207103804020144455600c0c00d984a01040d0840802c1c031045e2050110700c00c0245000c048090303006d00c0500151400070707a903070545c1d8052080e452040700b00b5103040340614040c81140d1302900c84030150240e102c0c1c41d11100d04814011984a0302d072845125800522640d1600c1054002d00d11541c40700c1c9000ea182d203c40031122207506099921000d541c030070311150401085854021120020090381b81c0c1070701d0b800c100403030781140e200c0300080c0c108000c0c4a610303018032010141e0040710300c0035600315612004100c9481c111150400d55821084680104000000082c0c1c61b2085100b141c007131203404800560340582c00503c981c024650110078005021429181014641c01500c40c41140c02d403070b42215500003071324070680c0450340c403080802000142d4101983c1e102c3c0c0c4281c00d403c04901c0149030040184 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 419215998 1250 419214748 419214769
    0xb0402010e0415030803180303090c0d240b03060c1c09030e0603010f03201c020102102918040f050307060501091b210209060904020304050703110f 65
    0x2810400c201d0a0807195030784907880b07841c20f9402c2d4181c00d801680c403840c0103070f000d0b48261181c0c442210850f142035400031000040783c0c41522044081c0c0380b01c0e05081d0074001c2040042d5000c443c120a8900580443d07803242410800d49174a00c0c101140b01f1840d103051504103c4003514501440301d0800c0562114a00b81d140b500c005504620300050454050900300c9552400c0041185d0001d80003000082ea41c1007548100d00750390080414103c00070f45031003d81584964211410303003103202c0d0303501d000b945080907006c0003040c0c0c018010307101c80c1884000684112030300e000c100d01d80c01d03a0034500c540d4038450307818000340c00c10010740b406802941c20894000358403500800042c0101034a03c015020044d0038030984020580c0020b052042d56155000030740a0301980880710030340101801e040d201a407040241095910300703070240744569550400d204019600489074190000340030003200029403500c1c4001c41c03240d40100050680b243c1140707402e8030004034141d02035205240c1c0c1ca441200640d10b1a8458 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 419217248 1250 419215998 419216003
    0x6150210060b0a02070e1f080d020c03010b0d02041a03030d2901080412050c030f070b09060705041a041203031e02090a05060d140a1a0414070807021606030b040b030102070b04 77
    0x124281d036965070220810303650f481e10100d1f001d81180c00000e901e00700144000740c40480f502502e050101102c2410700301c030b241801c01075224026004100242c24560b210b4100042d81c10412050340b10a140403a00d1036000c0c039651200342c1d0703440d00c642604e950218030080d000c0e02c4a12600b07400a07407960000b011104080d00150003012420780803d000f50003107048030110170600055076103036a42501035101383e4005a000307844c030a017000005441c541d00420110320a072595200c0f1810541880c00403694000c0c015088030300308a0400c000b180c0b01c00048aa40d0850303200ba5800300d140c0c520010300c04013000004907540456401400b41600a41d2151000030a4400907900c41348c41c3e00c08506401c015082041031901c0e40c50034031061110418440e00050310b404209614280000008000c1c8411651882d02c410301001210010500d1188106030380c42d0885050f20407560300145c04486060300e0310041d8020b40119030303560104011030070700780240c0b840000102d00850405400d501e0b420040700004100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 419218498 1250 419217248 419217269
    0x15030305160b040b010e0705091005130e0c03041e03020d0507060b04050a0b0f10020c0f031c0302030907090b100f180612050901020903150a06150210060b0a0207 71
    0x80c032003008590181d00a1075034210005030b2143c10141003810310b5003028001c808035221001c000136030301400390084511400380a4100d180400a0400459041d080306008680351061a440054900b002c40b504c00c1c001c1419143d01c0703959041074906942a030001340e842880101038074000c00701081d004607114494039501e041c0103540e02a245000001401c0c00d1640590051406003800020307400d030b511884030030200f55294821040b803c4204210410021200c1c1d00591240030503104030705182009590010300036045425050000c4511148106070308440000a503010081204d907040c104403500c01010391460400c080854200811242c5528406c0001400340341000e11500310700c1417220707114208014804403c455107541000742010044071280740c0740c60903c40440c0409506200b01c80313102e00001e0090100c008000712142a2000c02000380c8040741c2c1d10040010009819139420002041990260008030b580000f4402120300c1c0da04072142645050064003141900010b000c81569070041c1d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 419219748 1250 419218498 419218507
    0x2101406010c0f0c0f09090204051b07060902061e0d050c04030804092c0a05060606030112030f12020409090b091b0d0f02042c0a110409110301050403050a110115030305 74
    0x100080420f40c0d940c04201c501c1131840c0009480442940310718401482180c0500c10b603110280c9132f00c0d05030490122008850020800100060b01c964801c51642d880504810700304012900a400c15105800a80c40800e0000030381c54070300c100d030384038490380070f80030034103103400c0074110b8507118030a00a5000310400c156655000d0b040d5900004c1c070b01e40400102110000c1d121a40401107929508a588200e80d10b20642c4003051a2b0b1910b441903034162000d5800044042d90316880440b8681c00c40d12031102404030481c0085000d03101c90008002500ea0f07480045054503d9103000410940d0081610300507401c0b81410951f055000103082c3c80302c441c01c6a5500d0301c140e580c200141030801c1c441c0d00030340c06850200884c203041000301c2c554040014054524056050380054551511400080103001d04100305000249242c03603030029500ca0f01401c2c40d50100704000c40440d00319032040d2001e8003c0703400800d100c110164400c078800301d14915134009024000806810a80440c5503001c0241441170209 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 419220998 1250 419219748 419219753
    0x30d11070f230d0b1602100618110d060803090f060a020a1407080709060e09031213030c0501020310030506070c020108011a0c0d050703030605040e030d0b0a090204030302101406010c0f 81
    0x956030f0740c6090b044403613500d690404151189141e03a5401e10803015004140c841900b4140f103200b09011500c5602c215144039200c200410001c0c100d60071030030f1500806029580758025180304140251441600655550300714804004103d00070b520700c584681403c0007082d40856001c186e0b80c145585c0450301002c0300b1400c2c03c030310b800d05107031350054030041c03007010000501c6003296000a0200c07403000440c0e0309292211070089850f8070628412960a6524001144c030b0300c42a039107200032450103490b15102112140d5995402e99100f03807824155148602d90030b10a1000901602e5007004041c1016000642c0607030011788107840520484042c602000001c4004131042c5003140c40d80b07a211803d90300c1d110070021707000d800d0f40c02400040c5c1c000fa2030044080b82d0782c200f03845072880158440c1c1c000c5003482100e80260000d07212004055400c8050344030300045001d454005000650711940240101c810384408101c101c880c400c0c0d082c110080c000f814480310340d0b0000829001203030812007280d0b00c0c03030650 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 419222248 1250 419220998 419221009
    0xf070509060913120e13061706061e0d02060414010909020c0c060306060705030309071809080d020d0609050114040b040b090c0a020114100602011d120a090302030d11070f23 76
    0x2c0d43e00c3e600b14000c203210791b0309402554000c0007034070300403d601c004041402201965a0344c00b2509180c0010102354022280941d00c0030210310450b008200703480ca4181da80c0440d909410950240106105110010f8003039a0400320036400742441030821070800c45202c1441d90b03600d0441001e9800f49070004040781d259111007007100e02d0513412900320380e0b880c200100025a1013245d4841c036035600042c030b00d03003011440582c02091280d41d088900f0380c2c1050000d080d420000c3d84400700004046643e0040060504428000c190007010b00140c0c0f00c462003c07042c18001a00d04888a0511aa1400c071910a16581e5020419044441840a50740fa0000240d003640141b04958640c19440035000411200b185003003034070750070b9450950081c000a03d16200700c00b020040d42a0090054216201c481c001301e030a4005040c01c03884a11b441442a907903500800c0c24215400b031250001000c050034080310210801420000340540e004c10361005290021080c042544a10094a844400500c0c803015a9a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 419223498 1250 419222248 419222267
    0x20309041107030206010602030a050301063c020f0c24070812070e0301090f08130b0d0c02010c0203160b0406020f0a020d030b0f010c0210020f0f07050906091312 71
    0x10344200700d070211180d41d0250700d0700500c0c800c90041c0302d110000f0903500c0c03020040e0b58030240281c40741c50942c1d003029004c0e03445040383c0301140301a40074084010340c50a0340803109845c03207801610b40b034480000d9074402810804c0044c2000c266a010603045800e5403150030b500440340088460003104154400601c0e0b4651080d24405007206c5004240d071110f070303445243e61030b0046401780c0300c0138100024001414280c605440b006404000400500d0b80807510440080912810710f040800c442500da1311007901c1034018844414101c0d50740d100c3c100c1c00c103409224030451440c4a00055040400e4000c200c004142113100041007211981c0104041180c940c050f56490980302501c60f4903108154402551380b042c8070320000c002420005030000508213104141c980b1103040c2d48144060304035400f03001c41d21300200d24480451280c0301307410110035028001d00010b61030f00400307040485c2c0b9003410041441000f4040a10032010501401001b0703004e0140020381c0f40d481001c0841100070000b091725103050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 419224748 1250 419223498 419223517
    0x1203060406170c13050c16030302270f030f190f020d11011707050708071509050a06060b03010e0622110705070902072d021003051602010504150b010203 67
    0x40881c2c0114403440c00304100002d44019221021800441a0701400b03859041d030f41d055113403004000b80341c525820002c540306980d00905001d441d00300c941c2d66045064040002c0c0055a0040703c5401c115403501410f02c09a20340100c0050030014138030031003251100005565034251070348a07074144041044440100034000d4000300190840b40031420a1000d90b0750713045215001480348000e10040d400c000c10300c140181c446a49403400d000b100c0c2d41d04249980b0a103010396541d540440c3e100d40b4540070303004290704188140042d040d2482e0602e040020307610743d60000a00c1050a00052140842e08000140d0040c011202000c80359180200c00120480c1415031100340f03400d10042141c8060f40c04002c0c00b41501c500c0c1100e03410ba41c2c070f0034010704074041e86c40000c00221088001c00102c85944c0c4030742441e4501c00101700510b058990004480c510144110004070341c41d4010010710f00c00c0c05200164104080c00207102d18940750703848200318400201c0c225032050b034400014030503034401c02c00d40340c02d0381 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 419225998 1250 419224748 419224769
    0x2d0703020d0c0608061504140f0a03050a050d020703050c0126010623120406020c0304090509060f0601020a0f02090c0909010308130b0f0405130f140105010201060b09031203060406 79
    0x242141410324a5000c0340c01603e020071013450125115090540c1414038010756000350b142014244420f030b0068128140d01c49600001c814108000c6035150031200e4011440382c030082050310882c0c5001402c141c01c0030141d00542d001418200042900402d50b01103181003446c1008883c0e400c0280340903981c40003000350450070804000401c0755500903035026001206071400300f10691140360041c07124800e41030328440703a05a080c04503000400c00d0b009804d0340c410b003c047d282819216029401143e030100e801070055405042440340085c9044ea40304e401c01c8080c400340000b00b070251110a505d14a0b0100203015100b6100054803401680007a120042002002c1102650b564148045140c10410090641207212003002458070002011900450607a04096003050f00c3c0000b004040d0340b507031803442181030729100b10070640c0109115042140f07540c58214400c550404c0002821039510340c05c00700c65518108116605135070000703800c80f090540b800e00d083d43c0740c2d102c07800709000d004164420b02162 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 419227248 1250 419225998 419226019
    0x10905060d140607020709090c09150e090124080303041b120f06060e0f0106030c0203090604030b18061302041d030301240e0d060b01140d020d0506032d070302 70
    0x100410403038000e00e84c6500b15010b250311040f041d011110410001050068450b004221000854001c020701115041c40113004c0f90307880e900d00c0001c0c0e40841c0e41024595454181c004610045c140c808490520350007040030341d504050005a42e440060409032a6442e10482c01d40001000005074020304a03021901e18a403c1510f0041d00b204070001c0120384080c10210702040c454104032825100745c1d4600c0c106102c9918081040c0d0080c00d180081c0383c11800100b20303a09030780d00c60500400c0103500c0390140410740d2800d40c5c07028040c001842c2c0da4802d25080342e418040500c000c0c2c0c0060041c1d43d0120b400182482c5440024102e001600d541299540000701c0005213850350010100e1900e10503e42c00d946504003050200e07484035058035220b5000b00251b4484010501903031000031206e406040c0006088256215810640c008031003c080c1d840d0000750316a400c000e035000b0585c000c00d040e0300400500f16400710488200c140c00c00c00e030f030030800e0700304424070722401c1040108002d6401500c0401c19 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 419228498 1250 419227248 419227283
    0x304080c0310181e170a031b080114130c03020913060501050a030f0f050c04230d1106040e0c0a03051e07050903070302041805010501120506010905060d 67
    0x1554030a000080c0319001d501d01c2c140304103a640c056114800d800e503100c202003c500d5562950381e50705000c038100020b14424268400039031402513540765051030501c007075101c20a0f2000201611401007042c240c80c6110f1550149141e001400c29040d604088035001c0f404090328040b9245080c2c0d1910100410704005210040c1c64059008019000060310f8083c80d0040030300b05036049d200f2501c03c40380056810001040a24881e604c00744120b140c06002240341c02c4003160303c1054907016200c2040000d40020200414500c04180010f5000c04600309544201407400084001442e040d000d402c10310036412961300c0e540c81104640c085c1c900054100c065090030140008950400100c480103c0d1500c0003051402d024840381d40072120890b03024650307903610744008507400d030030064401d40c06106041e00400140c0d02c0f401f035050310a20b280740e0349508200703c0c2005801c0d503406900a407a41e2a07003034445404504007040e0641501c491090108580d1211360100700c2c4440d070340001a04500660b90342202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 419229748 1250 419228498 419228503
    0xd27111c060f0603020a0b1305090703020415020618070b181f0903110109030203060402240f1801050a0c110d080c1b0108060117090a06020c060912040f09090c08030408 74
    0x13a2030081d21281c200c5c0c0e4480c01d080d0018810500301700704090311000108040c2c6400c4540681c050034a180150600d6074452001030940c0804030401c1c0075800c1207007041806c005828070480c400a51100400e901442d00d07240c00001e00c03a00c040105c04241d08565a4400d0711006210b41c034090710305d2040b84450f14030440c010041c52030307404214ac418042902e2041c2c0f40d0720400400c403d07690000c01909164030b445d0700700301a0100c010640c900c42070302143c5414200d450b402c09050064403c1e401c0958403125061090301c0040f20701c58107814000c0038012a906140d100440920450740107401c1c034032900300301c40007c001414000740182811000110700003a004040380440c4a03522955012401c2e020441c0151403036681218414005100c0180c0310115a80302a1019041a1413206481d0449400e40b6040240d901c900d640d00d00c00d0740030f00309210300c4400800c010380035410303180c4a550405080100b030f60809c40c0c01e4480c148051f40c07960144024403601c1c0d0035010013402d140040302c0e80c595603620983e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 419230998 1250 419229748 419229761
    0x70e060c0313240212030f0a090501020a050a020601120506160311040f0e09060f0a09061107030c2010111014070e0405011202060309030f0d27111c060f 67
    0x84042585846490400b400024031540800d020b00007181980c2d205296001e540d000204180906512760390940e0101d00b080c030040501c80e0041d40c1d003551320747c464940607241c46410b07404140c01d02020181d080c0451004564a908605018081180423222001c1240a03003440d11248010440004000507070105c5031485c0f408843c0400e05641d010780c0c8103000f082d100c940488180307051080507000500e080a5607402481118450780c00010381d2024031074242126004184220081000320f403255050105002c4415034a0900b402c0e04040d902d800808079105020240090091142c0c0c040740225442041c42601c0f01c91042500030003020541c80d850030301120056648038003199070300000e24810b0525000e0b9905035008000c0c071504a020f07a0303090100742c3c0d00c01801c040b01800248009180c01640c44028800d280800b0404102c07c2814100c202d40c3c00d5001c000d02c1c585a0411040701d000500340c0003407a070409811107802c9050891460204a018003100d001049107290408402a20010b03a1004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 419232248 1250 419230998 419231039
    0x304020a0605120a0c11010f0f061a090613080a0501090303061e030807111201020706060e070e04090c050301060807090c0c0803151909091208070e060c0313 69
    0x1040da0781d9010150703150320908103030480080c803034000101290b0480c2c00c49a00981d0a10b40f2540e820b030400121401c599002c1140c005013903c542c00d107243d8580758040e201c05005250a80007a81c040d60011003041d205401391203005010100314240700005e098880002020380c24141c441040540c40d0890003483c2600c400c4012a1030002d010079801103050100f044580c41401c1c003c00b583c1562a801d01c203030080300044501c0c0082c03c0500c2c0703254070f6540c0701d01c480c0c008031400541c58042c0d5241140a640071900014003c034865010098090382c8041142d005c11000c4c2c0d00003a5900840c1040142c03560781390022a0190708154002400140000c1e401c001c6030342d045801c0151044110044075400d4840310003410880081c8049180d800d371146003401036000017021001140c9c0c2e02c0c105040e0401c020342c80400280c0c1e580f80329106005841103c2d0300c88034103600d0000f0a6103440b40b40903101a1200f445640a42d0006ca000100c01108000716a108114606034044840e0b030f6042000c8100102101d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 419233498 1250 419232248 419232259
    0x12020102060f06030703080d0b060a02211206040b0d05120a021e28050a0b0403120501030510090215070c03020a08071d06042003101706010504020c03040e010b030402 73
    0x30b629040d001280c0c0c1c0101d80007000f038043c0b50b180d51100601e6810011013175062690b14070402030b903652400d0007803075101015005030011012040040350402650140c0008041c002c100c084c0446420011503640603504440020b450860302d404504110811000142284a41d403950b442070303480800034281f100415402c58000019419400415900ea2801d454446d40300216682c05105c0704140d602240d01d180d0070210901003d40c03213961370320590320000d0b500c0034542028001850703809100009800c50816080c051545540c0d07807141c1e00c8000b412806a60359468081d0404c40d9900c13480b2155143d055044c0c030741c40d0b03046420408400860351200720300c5000c03402c4c40010000b2000c41e0220445408180000c640e01301c05240c0344200b0002004290b0190380d0381c039412428245010701e401100c65403a074a0f601da01e44910b50708004002c580059440b402400c4604103081c4e400900d45055590070748015840e5204012800e14501454102d802c00802e0000040380c00516100a184124021070b00b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 419234748 1250 419233498 419233501
    0xf06090b040e1c0216060804110904020f091018020414030616080c07050d0e04060f081009031b0b0f13051b030708010204060818010501050a060e03010f02041202010206 74
    0x402040310201d005040d415040100300f0819000c0341c00710382c465000c240c010b81d00e20781d802c442103040c1907074190000301c00710704e82c00144400d00c61491102c1824000a40d2140c440e424281c002030b60b00f0f080300329050300c18074103c030000314160202c040440c01005924115807250910882c80303800fa400a0045c840760040300300b0503180300c0c500055258040c18a01d1800f807c41a18032031300f2144000020a40403100d141001524001503007000403016a503240d1760f41c648114807040c00c10040c3c41d800d031f0020306075840ea6807080c0040da0010401c842c25a00c007140c0003c000c10030b0b2405a44007490344e0b030380c184019111910102403107090b51801b803080c0c861b40d1254030140c0d03a0107042e600448441401070800d03401780c0002c040c481007100d000000101c00401300c5031080e6a8800c901d007660b2040e000b8400040c0110140800803403a41b41015404160300020301503581404040f40c0a88501e00c90541009410202d03550241c070290f0060540b142c40354019541c81d0341b41c40d80c6100c1c01408040480c0148940310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 419235998 1250 419234748 419234771
    0x102090f03120d091106031302040b150d021b070b0d0c030213060e0f0603150901051806102105190501050a09020706140412020f0102040e061201020d0f0609 69
    0x15000004000c480b410609103a00d1901c0b58000380a03107003044074483c402620050603580e880b00507621640907081b1007440c40e4440d20510080d1000700800c0f40c002e214500221307170306152407426259030044280c0010385520b44980c22104000700c00605840900850102007826080c05000b8429803084103808e02004101c01400c9049104518803200012010034080c040e041c441c0d42c0c0400c500304004c122542968810000401030352055071a00060140031052410341e0810030802ca0041c581101c20400c1c0002402c03035a191120300074140d520a042c1c64070507850f868040d509800da0200f9101c1d400d4035402c4401d003000000c0100741c0d180d80d14017070401050750000310603005142c140c81c0058512101c5529142c8802c010303400803541200c6c485d03269200720f10031640208030b040c8958001e0800b6a614011000081d041600c0990310344a1640104800d2202e040004c1c2195000401610025100c10780315404500902851001840540c100011382400081d1604010b05441952004120100c1d000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 419237248 1250 419235998 419236003
    0x27120403030512101a220816050306160818120306011b02012712050c0913260c010f0c030b04020405030a0605060a03021c2303030f10090903020102090f03 68
    0x280305081102c8249070300564100c03110b10103082c0001c1b58401207450781408505038040306025402c0f104c8594840c030a803200c94200d1052500c02030206070094040c0703050190f040c5103058042154441030241020100b03046c0684020340b404c0010701c0d50243c940300000819038082a034070944401d40000c9414913055801e1000141901031a07a05844030b0003464944140e0310358200301264580c0c40d100303207004c000603a02c040001304c01015120350041c106a65156040041c440030182c03c08100003043c096043c0040c030440340b4403000300076650303801203c0302d8075910000e07143c498281800b0300c075428032038020030010080d00004081e44250700c007448001d4203001404224043c0d40318095066000c00c401e14041074031944590341180e000b43c4206815602c94012940983c0c0c80c951401c2c03120354400340c103030a000c0a0541031302d100e40b48000403280485641c04080d9a4040a40f40c0000e1109040110b11585a400503401c0181162507085c07081840c01e0034040d0003904038102e014004c0460f001d0041d21031402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 419238498 1250 419237248 419237281
    0x3070f170f07031805150304020405150303030106030905160e091c120b130e060106030605061602010806010201061703090901080319050c010e031612030527120403030512 75
    0x32050141800302c99242100d20000c20910800c86000d00c038004038068a4100796105000a07001a10f682e0b400c0520500c01207600040541c1c00d040741040811480382c0d4040304807411102c40f454046541c0f081810a40d080c010190302040743c0b004511800140400d80036107040c81104000141c80000c000c210106400c944800e0004000510b07614400c03620016550000503c0c002c00b030300e509200c01d55a00c010341203032035009845407994841001002050f9160107203501410042d60180c1c1450060000c1c2c44003c011750100a05010210000401c1030340300354440c20080803440f2034165100d960307400c3d098480e444024407a0080c26124000718200200004480f1710009070b810340d54010101c1a4200c40300c0d085501c00828039500ca010714259032804102038140c030701d4030240c5000b01c401c8524149e030498152002003001c2c142000208500c0902140700341e4250400841e903000c403d01883c80180c20524290340c1644451004100030040c5644440a0407551503041004183c42d2520154441c0040a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 419239748 1250 419238498 419238517
    0x3050f16060315030f0c05031605060a20060406021801050405150306010c0c090b01031a0904080915040801090201091725050d140c0d030909051803070f17 68
    0x4092500300401880b90344660300e280c281442c160400340d00ca82e20b00454002d0102c05a40c0c80d82401c5082c446481d06206106090801140d0380e410780380b804000c02c005028040d051414032901461081480340d00d610003c2c461f25440007036510b246000d00d07100000b074004100700d5400e202403580c590102d500541c1145c013903440003031a8056000300c108990303055903c010120360401400241c000000b461000480000e066000e1000c20210080e900040480300c620729880701f602020800301d030003501d5203501145c005800091150381d642d945008106030600c40001c7c919000c80008000445070740661007000d2042c800d90384c0c403552076915000e0a990100351145440c09812051601c80855921014209908110441c040f0075942c2c40000030401498070320140c40c650a003120414151000340f141c04145282114680da080b00710f40c600520001c468000c00c100f4030756900200c1c0c00d030440102403c221a0001c4100c903070700c80b56403500d1040500c2c4000f0858004a29028440c242c038004001e6070312050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 419240998 1250 419239748 419239783
    0xc0102071d070339140f2503030501080c060712031d120315030a0c09090f140d080c18040906020405040606110c04091a1003140706020f030901020a080c01020d05040c03050f 76
    0x82e0351070030301d88190301c500d85480200e4001f02141c010039003042d00e9285414081c0d1000138042d894003010b4ae04000c40c0c1030031240b0650007007018100080c412003000d11043d000b032030b0000f1400590305103001c4000c0c4441058000381700304048184e01ca164400110721502d800704510399800803e0702416540c0302041c6006010b1180d204052280f40034651000207103600444040044035030030340305c08942c20700019020b1840d030411400ca040e041d4202030410381113001e280b426480d02ca00000c0344160400e100200d00d00c11034580d100c6a044c001550152000303448001c00800c0029a1010060445031501c43c4410300c50140ea01c501891f46028480d009005410510038149603031000f50b203100220008151180201254601001062103080e51180040441000b021210304040c1d020346040c0400f03070064103983c4204100781141e41e000c24510300003030f4880364054960706510310040c003a02615010803d6030303180c00d08000c24000c24101303040c1228040c409843c004545000c0442d12000c1d107036030103030106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 419242248 1250 419240998 419241007
    0x60309010b010e150a0507060204030204110d05090a0221010f0f0b1507240f050903130816030b100b0313020909150115110604080a020c0102071d07033914 68
    0x40c0c0103a001f407403403601c1500c00524040c4c4950000301210082c0400d508041130101d80d40841c620319210700c6802035058030003807031600250b0740012000b842008a03c0c10000510f20a9003005600b5000303a0394940380c00310240a41c495045028008048a00d00544186c4054050200443c1c003142218103da40220480000280b403450341e0343c3c100000c0d140340e008540e40754500d000491442c4200e90107110702030081d543d03e11400084c441200c1040d000304017990403440c1d205004c00c48443e102e2003100d0b40040704409942c2d50b00600c103541e07400c0741d108481c502800010006210155072030a103442d80b0031540d4802e5610307011030705940e070b002010090a503090100c0050040c50690203c1842888403441e10100300c40c5c4c1401003034201103082d9000c03552214042045e4002c3d540601988861070300a20052096602d01200c9800120004200000841611000c240424030075000f030300001e820100e840300180300d100080e03403180d604c10b1b41034600c1b0a00305043c2c0e1940c40c8569040c0042ea004604502e050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 419243498 1250 419242248 419242267
    0xb030604110f0c0a0204050a0e07051003022a070905060607020f06091008041e05060406050a090b0403020d0801150c11041805240c030a1505060309010b010e15 70
    0x1080c03140c5000c040a41e060144001c4030098100030655440c03554064003022442d8030510003a14030141c0040c40207030403c2084030700c424002682c00100c82c004c440d00070405805070020340007849802000f500e805490803d44261031207c40c1e504140060041c106c6480070350344e2072020300b01c960640b5074551007e41042010b015180040255070a000c00401c00d1340b600c3c40b150009190350300e030515003030040f0b034501c41000103101c1c81107682804460804100020100d480d0b8842d51200c40080c0014143c0c0c2c0e542000ca000d640c20340c9d100c1408158000800c00e243d00341810003940d40d600203075164001030502d02c000b094802c10080041484c0f00a41ca400e450b481d0281d03284c2e030300180c0005503681c0003503544030403d030025544078420703000c14000d03005000c0601050203905c1151481c02407508140c20180b0034401901122022243c0c0001c15800009c2c15410200c41d24503051080e82c0459440900801400354000041d031110002c0d00307098071948100301c00f030400e0091000c003c1030b13103a094142c14000302c020b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 419244604 1106 419243498 419243501
    0xe01090317040c08010207081c0c0e0618030a080406140306180702150403020f15060607080a02160902070213050f01060e01050c06012d0b030604 64
    0x5600900e480291056610144984a614114000506018481c44204054000d000081d540d44074507040c280c204d81c01120310031050542e118911011404e06105813100300d1142e0300e940c0f044802c04130410850303800c50310144c01c509485d003d26140301e980c14440118100d20a5500d280c17140e040075001814030316614489206e100c000c100b40401a6a4009501e203441e0108002c0010356481c00405c038140302c0352440c26003011400300140000c060300030603a10502800881150386000510403101641007080d1041074221070b00b08210004a07d62200400d88c40074030f030044491030724560040b5428122250300400013141d010410318210318102e042240304480c85103042c1310380d081c420401d01c450f52042c4a480c052260300c1308013044990054080d2400516134405559241d80d4610f540d05440f00618484080c4480000307400d0150b50428a02c21705a4107800c1d0494155542c407020b100 = true := by decide +kernel

theorem cover : BRFrame.Cov 419064748 419244604 := by
  have h0 := BRFrame.cov_init 419064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 419064748 ≤ n) (h2 : n < 419244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
