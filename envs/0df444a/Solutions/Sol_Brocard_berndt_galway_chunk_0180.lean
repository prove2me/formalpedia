-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0180
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:18:03.15668+00:00
-- url     : https://prove2.me/submissions/51308386-5ae8-43e1-88aa-a466672b815a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 32194250 ≤ n < 32374106 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 32195500 1250 32194250 32194259
    0x90309170304180209010203070606090504050c09010b0d02070501020f070b09070b1305090910050a02250f0b0c0d05010e160306060e041d030a0305060a0e01322206 72
    0x101d0340a240b1440d4100b800041c40800300c4050794001c3d050700302041c41100d0034040c0365151002910943d45c000700045d0b5030b0b00306100920409000c107060800381542c00800a500d80092164070f1311480d09000300c9140d01043e502c081060a40442c1c005c0f0100c025455107914860804540c40142910685550f00c15510009101e82042091f42c04084003031826004880c0360806121219500030140c812a029185402160303684a1161a00034001d0010042c0c85005400c0034413100c0c00c6071851144001d18258081c00007403405500116895484070840c21031707448200c06e1901901950354592107141c141000840c4c0100c0003030703a1a10580443e083e020002e0328142082c1d04880d00d81c021140054030702800f801c03050416401502e1005100140c0101002c4031038006811900f103492a40300098480c0705000a0340740100603d03016002240d00c135811035140c001d1010408450b07044600074445410100381c0803c109005640076a10068020b26990041362501507203030994484007503015250100204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 32196750 1250 32195500 32195503
    0xa0206030a1e09030801060f0c0c0603020307180f0302010c0c0b0708030708070804020f01051c02030a02090102010e0f0a150209060d0509070603090c05132c0106060e0d0209060a080109030917 84
    0x200f0302905070b143c041c042c1c0d08080341210440c800400500034018002401000504404c0081c0010021560b0043e264181410002d14054400d200c00c0c0030120304903400d100d40700c03070401d030384044036070900f0b1005a8500901d0a0850703404140d2210040c4c01000c603001c0280480a1700840c820307102d565896403140c0da04007007601c11032411359002c0c0d040311120028003030030350140e00180303501f080c1080740c400952041500d800984e401140c0100790160003054400065070240503141c15180b4020207081898031a4a40e1590750202c000b0140403280c40001c0908013003410350450b001c014001e01104da076034a09410010140000343c0d000356441c45101c03400540b0314424400c0200840d403105908024900c1d2100b002085014040543c4400b542e40f07506025040c01d03c0c090403100e511211030b00e400d1045160003942111043c2d80004144141102e81940a035203549107640f2a0794105c5507030940d0b07194800420042c404079080141c0039031800d4490020306810005407022640898086001e2001e200c030004d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 32198000 1250 32196750 32196761
    0x1605090a060803090d02011b20040c05030f07090b030906060108100b1b0c0a151107050105040504021605010c0c021905061c09020303070309060809010504031b050a0206030a1e 77
    0x94642d90000e2240d60250f14040407407085050051504806162804105202c00c51044104841e0038403032066010070f803c10071a2a0312403001c2110201f180c101b03100d00190443c403004000c4806500c980340010aa40d004508050282040d0201144c0780d24110340010b65561058407568041400c00c8002402208a03841e101c080d96000d40d150340c1806081181540d04c4204d550b44901503004e2250480300c03d403203400854008292095081602c3c614001c00500a42e1112248494940041c10248620790304541243c04503401580c0042e0b03506681c0882c01d0394550044401040c035401c0581c0c040340250300c60003103602c440c0200c1d80203215030071000080b111402c05108917500004107002d503084000944103030320b070f0310320511070040f622603010350001e4103513480180b048003c00d00020303003841100c0c0c1c0b11880c19072001e02c0000800450030907441c0a0218403102d00704071145c1c01004110001c201c0144080e43c80341da40500746589074140403484102134055000f001640c20b000380281c02502d40d0a0055 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 32199250 1250 32198000 32198009
    0x81501020705150906030c030103020114130303050304050a060509070609050405060a03020904020d08070807060c030c080103060e03040f03210f0c0b0417030a0501051002030403150c111605090a06 86
    0x1c0c4409403900e0144030aa5403a1100842e01032420f100c00d4042d601c0e041d00841c400c106107080e150740c0e98154400541181c0f103000f1a0703e1200070600c10000400e07003101d0101c0c140e94060806603241d9980e40740881c586200e08000412030b034280707001d015541c84002114030541d0026240c004406403610140412180110344242c0d0061480740e040000d410920326a81d080340c0040c003003580401c0305441c0c81070719521161040740c1c00c0704001094000c0c05614030461030f50042604e42848925070304100105030304410302020304955620380c0361110f8404c081040354004c0451000071350419540b814039035103045010300c100c0c4c41380c0c4840c00700b0168103119403111054807440340c0340c01c2c01c2004161105020700d10000c05c1150312070488000010f02c0d95044002e14071070310301c45034003203040e40c10902402000310181480c030302598403d010520002d420310b500582490700c11000007540701d10b00303181111030310203d140d902000d000c0d2400044818099604080603100152503003913085c0c40303d40888007155410720030b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 32200500 1250 32199250 32199253
    0x10e0409051f0b1203090a0504020c1c02160608091e030a0c0203011107080d060b16020d0507211403030601050d0b040b0909070303020c030105060a03020d080715020a08150102 77
    0x9a079400341200100500c0c414000450005010003203a0111364495000380040c1d0080d400402c0d042502d180c01201e5002901040d03c066051807050f0b8000d44d5110703461569500c841cad6401c2481c0752024030030880d440c0040041c8140741d086580d900710150003040240d034504014020141072001c0c0c4403201000000050b5050000c41c9441d02d1171400f211200c038400340c1241e05540360013540092008003006401c441d8001d101c4590748020000035401240c02580c0400109842440784040082c201d00b00c2444c02d075015100d03240515030f5032402ea42000110f82140015110400c1c02001c0e04c1c034010403001c1c2d81c41c41403441c0c540d40c0e1206500583d90340006c0b03503c1030005108008075030001511741c100100e0002c018001090110000c0c000418101c401c503030b03160075603026140400a15604228550403014103070020000360501402044107a14203001c064080e06981209200304040882101d0380d0075040104043c1e1a030f070211110000c0e5010002d90000542c10780c001c40c204000d01122a00070020580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 32201750 1250 32200500 32200513
    0x150a090e0a0b030c01050f040803030a06080d0c020109090b0406030b251103030703020f1603020c0103060e010e0f0403020708030d090308070206060a1809020a0b070c06090e0703052d0402010e040905 87
    0x10045440787c0c85010a410703580e006210005034603400704044c60203044401c40c04101c07103040c08802803900113280c110004204404410030b0160740c02c10482c0d010f0340c5035010003084005010011070040d140660004000010040c03c00002d50260481c03407100a00c202940c098180c2c1c904000c940e458400e110024541d0420004103050034020343c02040c6000440c0c4065003018091451420b03a004608001d4002d60854030f20000c413580c0c1842400060903d450b40200f035075040002e000d9078101e00038215044400e000000c82d040c14000c02c55200100450340450b580c5516504010000d0402400200d0101c2c5007040462004c5002148240c45160f0151848206a103041140c0c0001c400d004c03903940809650710038800c05178a81013a40d60140103100c898640e0346249141926924801e5444402080101d0006018800c05045c0640c0c0000b05840c6c040341c244c80301d000707501001208045140000031455904441d03814064078461140d4002d803181114115044140030507030341807401c0103003241c0092 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 32203000 1250 32201750 32201773
    0x30c070b030406090b100807061b020d08040e01121208060d110f030d030204080c0301150b0304020103060909060f050108010e0d1809060602060a0b040204051e150a090e0a0b03 77
    0x2540603662007805000c004c98042c8042e261912096800e9402c06012a90100306100880d010411030f40200228070340280100302640c03100031504071401d8024030a02c221140f010034804e807007041e00e010741041c4409103201d50303480c1800c80983e8880381d022506014440c048942c69405803014a00c149405440e10755220160703a2040211089240001e511001800c02c405094a003001009040d04c1c00b528010780c0d0720700f800f28043c03030b01c5100c10700d02c0d100b60b04100108290103522520982200c0001610980742e4440784010b0300541040d07004500c0e028a40003501c3c0c103101c010341151011000341074041189036240d07501c1900f07031591002100c00c550321000415074030314414014040320385a546482e00c941030300e031500d6005545c0d540d0b10020050f403045082c801c4941c0702c1d00c00d05407003420840702180340510344408110410a41444402c1d01e6180b1800c1291a403280551450300c0785d0101c201540d00e20304620041e15031200e600891180090050000b801c422092041c0e6400800050090a0225a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 32204250 1250 32203000 32203019
    0x902090604150801020a0e040501290d020d02030c0d2004170106091404120504080a0b0601050d1e1404020609100507050a05010c0e030312011703040503070305010f0e030c07 76
    0x401c0c040795850800002c0001c00450a10140035158000ea86046030700040c9000c01041c5c44d010b801881d07803402403454070a56141000c044164021000944923141c00360303d00100c009008422030300c540c031800007040180c0c1c1c040007001020300c0088248200035090400c20a8050285010381425801100700310030f00c07640701d24280d00700c5100540d500108903181c40c0c0310a40281c0e482a4100707030202217140240310800c043c00c41440b00ca20310600e0001d04082c607004025a1b54034060901424112100e00401c115910810482d9180c1040d00000e000341404515881510040440c1243c0c5040c540140e00443d680c190a111b401150010031440c1860b0340078040111328450340c0442420322500704140000a0414802c42c0c0642d4007a034000182c10a5013000503004c80079900026211b80c1080080c50324828442d1000b9041d00d2601c5646c01c2e13a41c0955148611710b00c103d400480d418801c1400000401005421a08001181420500c140300f0f803003510300e95078040c6410710030b83c5801400c0705024203400b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 32205500 1250 32204250 32204261
    0xe061306020d090204110301030c050d120f0912030f230d020a0c0c03110f0904050d11030903100204290415030f0501060e10080108070302130207120807030e010902090604 75
    0x490000000e142642139002400710340e044640403048400c00b000400c14030090009810040009440e00c5454501c683e461240000d9401071030b5040c08003000c10070254504c9040003401901000f10103151980850070058180340340c03a046040000c409c010032010910088141c0300070118005900703800c0010201101000c1e4102102032810040100d40100104445140c03107001903000e40c801c50060b01d500c0d418449400c4c803012095010340d00800500002800005980303038400107614060b000030402d00c0c0124118412540741340c0d4944100d04403900c05d824a80c0c018401c0394a1092900e209000c60040166104010392204010404c03c1c4000c02c0041800312058210141c02c0c03900181000030100d400084481c2a00003c00085912902d007200d0304118021100035111424184019031600c0c400c030740d8400d203a0000038090f1001c0c1108040008080d010340b08442e5122500008480308151f005181c20422254a00060300f8a5103c3d5401481840381d031000715005080c02038103640354000e00c0017820 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 32206750 1250 32205500 32205517
    0xf0c06020f1201120309060203030f01050405040204060929090601020a14070f151b02090705070201020c0306040506060a09020304031b020628260105010e01170403050a030e06130602 80
    0x1c1003005089035194164460302030007840c07805001a42d65410020311b5090150480c0080d941304000b4450516000380582e4110b840c00c803070124184d0389034030124000d4a1503611080b45107051152041d0201081e40e040380d240d8031904e50300309001030590700b000101102030310540c0c05070300800e1034140403c91555007603001003017000c00c8891465075001e007a006c3d02d400780d21044221b20f0644810209940c40780401180649002c60015016140e400040341d00d580a0180401d2200c00110501164004d101000d10f54000805070b488a290034204241c450104581d8503220f6540d8442c017240b031f1043c80c400d80f4000c5070540c0e00d050344260741d48003400c0c60822020059078401014040c426400d1602002c0700e441ea010700890700309903940380d01c025001c45466456000809510042601120b00301d02d00300381121003d00e02040741403032400c0180d412201204600e40f800c94a0400c000603d9004001001200901da40030000044210105a29040107039903264819001801c06000724416801500026 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 32208000 1250 32206750 32206777
    0xb09150603100e070c03030b0103090302070b1806040314010506090411010f120f060608070905060708090f0a0e010303080c04050d120908010e010e07051807031e020d02090a060f0c0602 81
    0x1030b83c903200082c542c16021141200098486040641017550500030540c5c002c2d000c3c20706105075500c0760740c0651142d10501403003c000c0360120341112425003200d0112548400900644c5e5901e031682001401d00142c070807658095824180460024240110302c144910b13046480d16210742c800d05c004407014550000c0790410070859055007102c0c0c00c694442e955009a11400c0040c1161402c900a0802003000700310500b4440c08d01c1d000c000350344840040f40c0320345d940a50215940d005890001342c003219402c01d078640200c205a80400c031001c408400c00e068900030344464415646480010b803042c40369010390758100200044080025004044115145072542800c00c049030b103c0e0b01a40c01c4a05c03842d8801296911503610140f811018001080503100030359010b0b616181c11003650032030381e4002d010a070405907288403170242c56800c003e1000c2000c00742c00c429540c81e03035840e40a03406904440e042ca4850384011400240c10b9005141410443e100d82e111511462031a03183c000003500070000701c0001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 32209250 1250 32208000 32208031
    0xc030c0405130c0807020706050a0302220f03050610050d02040203180d030c08130b0105130902060304030306090b0a0501140a0c0f0503030115021501031103160b0d0b09150603 77
    0xc0365640c10302c1d1007a4141501c80002c0700c1c910400001e090302c60141201081d90172180060014543c8881202e070301c0f10707490401590320300110740000c5020020b40b569000240085001240b0007a0031a00b103812280100c1c1260f079142c9803940d2222604c25588640d84e4414100c504801c01807e0035000f6690000440c810301c0868008a54030b54140014a8031120000b0795510240c183c2c1d40c1c00c004440e400a1445100b05000c1c145a511038040a506000311032140e1551090300d00c140b11075800c00c900346d540c007400341078603800d00d4a03004e400317411a400303059182420051059034904001240e2402c03030304e0595a9101100d41d0b0441900c140d071018078002d00300015401100c011803000745078111050b2268008554940c900301200c401402c00080c61021900000314452810000034002c90540c3d0700000d1100801d0710310f070000707071a01300e085003011101c0c0040340340040c0107072020300030b40041004028140840b810400c10800e40c0002200c0110880c0d400c00c00c2030b096814014041c60b40701d20010100b290 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 32210500 1250 32209250 32209259
    0x2c060303091302090a0602030909040b09070308040e0a050901020903100506060403020405010e150a0f062d03050405190201020601140d05030f0c1c120e01180501020909060a0e0c030c04 81
    0x1200701150000b522020340000700000300c0e08100780403400800c614405141008650b10010300500005000a062002c846020540103403051000394015a171290800e56a140d440c80d561001c1c21040320029451803526000410001041c003c03207410010003409002000c0c1510701980081c00003900158210344c06010201c01601c4610070240606888610000a0f15100440305a0140c14007041130144031051010010191205d00c0d150554a0f9401c05100580e9808c580605d113241080c403541030801880c114008968040e4080c60160b8003907410f982d031514903203614a40000400f8802030069101c58010022341454140003505800001d01c8401f4401c2c468454a2545d01310043c2c444041000080807910904104252400c1001d9103030540355020001d203001d40140d44520082c0c0c0f20304d40b2484007865015084d4007802c6e07098076a0002c41c6283c03130740f4100b56000b9000040c1141c0600c181c50046249868840f02e1842102d04131380103408169203866420280da04003400102d400c501c248000b09 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 32211750 1250 32210500 32210509
    0x3090a0b180f1006060e060403081602132a0504050103111306050a09050306011a0318070b090a0b09030307080d0608011d0d0e010e040e070e10030c2c06030309 70
    0x82d06155110061022400c003d4160b800c0380c45a51046081c0f00060002003e5070321201d0640301201d80007640700d903c0345a05032004850802114000798819580144000e0032081c6900c413100c800c81c07c1e0100940de1412002c0704001004086201011620500c0204411362082c3c020058000169010074241401032042c000d100140b030b004840403c602140008035981e02c107240340020002100140360039450001c00720082c483d50719840c0c4c113400000002502c040e41d501c0c0c0303c6815009400c1112a16035550f450540540c00c103c2065226084450300010700c80501030595282200060142d0301c0e04199580f21070150303000402840501d07450b000d002070030000a10a50251508429203801400d00b80c99003103007804410b543c82014070620401000301a40d200199441401094800041c04502002c0251401205070702c441603103450101001a101c10a01011044900c900f401641c019269001003c3e44001d1200b410925200e0b6201e2220810800302c100d80c00280140a8920700700003200481c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 32213000 1250 32211750 32211763
    0xa0b010c080f04050102060a060b0a0302030c120406020903100902030c09060d060c0804060b01171906030b0405010b03060106080c0703030f021c06030b0709060c110406051f02060c03090a0b18 84
    0x802c0000081000c21055070188007880e8800c201e00402c004050030136150602e240140840002099800300000340810454011642c0404c11031754007080621341850808003952140c1c00c498000c0c00303503111000101c1100d018074102542e0003000f628018058000348009103500804050b801000301c100c120110b0703403610a41640341400d568008040c41c0c40e003092801d5072070321840c4a0412105800015080408003101c42e04080b410313203800d102c0c8505100610280009410190080c40901c040c0010010150701801d0380c28829000e9800581c2d07201401c3c0c030200c00807100030394615070812901c40000c0c82035002210040002d40018207104490f40b0781504007090300840d42109540b101b003407082c001105451a07000f8080c0c58074184203420460024a020700c032040060421515101a074500d40c1c0c3d80c9c016401a00b00901408030816a1520300418036814003203120241c003902000c2041c00310b020003280c0c440c1c64014020502c1caa1103545102c82c0e4071000b81240458501d00040c4400c980e0b060012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 32214250 1250 32213000 32213017
    0x615070f0b0708181902030f010c0504030606090b030a290405060403021203150f0a080a03080115020106030314030711060a0903021b0117070203130e0403021011030a0b010c08 77
    0x881c814600366202030304000e005069928a011180d10200c5003140000d03030707009840c030700d94445900070106102003071a02105c20194000d80d400d00144110a903409400f40c011070780988010b2110b5551982d502d012540001c0d0401c0d05500030300001c03000b041d000055060b2420300d00700b1106031104030090344c02050400307590031521900300200781f00c10315a0400402100e04401000300c0d2460400c002d42003016407160b0482e600030103406e01022080d540e83c0b8203030801410f0120580310003c20324640203103024001d000e800d94a103007003410101514414812350081d0317a490b4440014401d400d288015003600028145001c020703100300c20100301e140c1405514010b42c500113000c00c10f14664500607040c40110b18500180015185d24a42c00d44e0340045500c040f188886a040c100703458036101241584902107181428515208000800098080c0310921590013035090b100300080c0180720909403901e85002c800c0d401000e0000c01e0444070075500c030300603100e41418000310482c155558240c20360001c426 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 32215500 1250 32214250 32214263
    0xb0f0910031506180506011b02030a0c080616020a0c0b180a030501020307121406010513080d0203070c0506090f0402030a02040306050c030103030801080604080409020d06082505040e060615070f 85
    0x7003101200e07040c4d08002200c0c1489040c4442d183c10000200b26442901c1c100c410307510050301c041c080d500c041c02180801c3e50406480160389443e101000c0da12242030718080f4115507411420410701b88089450400d00798402070300e4412a1508825807034580008a9081d692b8500018045d461f65445c8401802144100d00150b201e20301400c01412100244450b072000e5400c244481c10250f484400c8241d000009080141d106c105802d407107070440010307800044952090a200703113140340e00000540146482440b420699513298405e002c00d40c0918000c40c0e070020710b0031340905084c0c50030703402441d80039400010043c1072a0b40c03901c8a405580c01903034400e098440000041c000c1c10f0f070180403540500000e200a046a0500d0740d110f05092082d881540340329070340403d500060300904e4014a00a00d007c508651000015031661b00c4080390140031544a011507100000390380c28140512590650060041c0c501503460030188895010071888082251104010f404c0c0001d510050079034640d8007882307 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 32216750 1250 32215500 32215511
    0x20f0d060f080c09010e070201021918060908030d09110d0c050906030c06121b0a020d0f03060501020c01030b0a12050303010602070608040b0402010c030c0b1e06040b0f09100315 78
    0x1080740001c8051904506082c0d00225640301d0651107002d0003030f0445002d0201d2100325a201032049009008070250440d03840700800c0b000d001254482404001a000301400f001c8480d5641c0003690134540c01d12514416800502c020181c448895105c040d80314010200c240341035004030005840c60407500421644a000c032001817019040c110700650b8050400c0c0d000700016000c9200160090003035850f100d4809460350001000103095103000301000640104294035030342c2d83d0344003a40b20744100b5031040015140c40107003a8054840d000d071508030364043c0c000d840d200710007000440182c08620f500541041803408002244900c050bc159051401980690345035410841c009052034034544c40201001505020b010108010707062403500198242864a00540342d850103980040b040c44003d810721a8020401c035100807144c00104043e02c80c0c2903804101d607503200070801141d000818403a0044082100c5140354200f4208083d048030b142503000240e00c0e0340356203140385482e0801e85030101c540c544 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 32218000 1250 32216750 32216759
    0x406020a050106050303030f010513020c030a050706140408091504080703060b030d14041503091a0108070b0c0d0f02031608090103270204020904020d050405010905120703080601080604020f0d06 85
    0x20f208640c060441103014610350309210840d0240c40c3c1040c0201d520600341d00b19075100d190342a60446160404140640f5111041c0140250241c2c00c001003d0303d80c0c504200020707110300d240400c4140b00b260310907865400c1c42c00581c14041202603081040d42075003400c01001c54184403c000e10001103106020210704a221001850b00303203424218441d090004c1442c042400401c0705050710191042d4201800078144100340840c043c14040340701a1801c0328201615010340e01c40c22225069810075411901c03804d0b0b0368244201188601360310110a40c02042003504040d00c240200c81d600e4151340304503070902d804900955590700c10070004850440d00024004015601400744030b41c00007404142c001952103644c80500240388032704009110316400101d000e042d680310b038140c3c0c2c02002c00c00d038100101d1600d0f1624900030711542c8401e0701c1030b01c02e500e9034501c051040e01c11a42460703410317920b42001352a44001585c034100007400d2076a205400b2b0100985240022001d0710081c2070300d410216580d07141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 32219250 1250 32218000 32218003
    0x1080304031b0b0d02090406180b0a14060304020f040b03060a020705100b0d0f030311040b090a051017040c050d11040617120706141e0c070f0f0302070305030406020a05 74
    0x90301c0b600c0303100e61461004100310038080040d41c028181d6588056070352807005d070002c1d00500c055007140c0415000307a00d070014802c400c0e60000d07070341e400d040d54440402500ea00803000c0002582c005168040420000100142000150782c04003040c0a0004180360b030036000000d0801c842112180d10055000c151401071003001c100070005100c000b2030800c9408000008110342207000c0078003608002e40081a48101442640f082031300c0e8040600081e00c903500c0304007140c0e40e90321488800d0b109076279554021500e031800d000c105036102444d80311550341c400b695900748404000140117880c40310266400241c02c1d1221143d02000c40d105030704000c2041844410402190b2007500040220255102400c1c03036400c0001f030801e096400000d48a80703c074828070700000941110f003201c018416002051113050240c00c3c100c8119090100f103400030729910112000181d004203130000c4c1060050512400100d9070740d4000860f4580644142c034401ea442e80c03a12895030b13101d9845000141d02485069061200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 32220500 1250 32219250 32219273
    0x304060206070e010c02010f0c110901090c030608060105091b070203031206190b180307090e030a12050c0a0e0d02100206060307050111100c050712020c0f03010507080f060d0b0108030403 82
    0x90900786200100000c2e00020858940b00b8002c8c400d014440084070107000d1246039a280c40300000741040142d60711120300344003400007000d11202007170034410702103958180803618605a54003d0304480245c1d0707074141385030307459079a14800b84602c01c0c0030000345000da20280018031000b100d1101c03000640c00d1030700c10b02c610440c00c03420141ca03541062809204032800707c011211024000721352500c0b48030540c0002030500e07500e86e0119243c2031502c21041c0e00502301001a10780140c80b61a5500b0f21000c5a040d181078500882d601c2080601c100454664240250841e0500344000340c445080c01040f9808904918000550b600160b40410b0400c490742c50f04000003000390a0a2030802461218180c1c0c85035a040b00d010b0306080940c40f18000e6400c10b1040d010b4035038040e040325008034020320400c0083d44404400d00c0c458014520603c003031a050405001c0c0a02501140c0e03035120082d9150700c0c3d2181c0002020346403d41c09400e2a034403502007403640b0f007964081d02c924404ad65849203580f0b4a00070900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 32221750 1250 32220500 32220527
    0x20906030f0a080a110601090603060c0504140d080f0c1018020a05040506030f06010612150501080403080a0e0a05010506090a0e070303050309030d020d0b010210020306100c050f030406020607 84
    0xd108181c8090507600100e0781d070095980c44850180c85410544041c3c2e00000340290b491024400d040002032401c0142d00140c0031603024000030051407003e850229003034403480c06138204081c002039006200d400c180d0303e02521035008840304c609101548034245c89a0740480c10520075584584de4820b62003405100303021920000700210342d88420640e001c01c1c081c1400b803094901c10b0380e803040001e8007503d042c4040c4140072a460300f5110250384a0402a10300c900c103824440c509480c2286030900c0310640c0c0340d40c00650302c050b180d00c00155119902150180001065480010344401c855003014004005001c81d0620880001c65a45003400a02082103002010a5042410074405c0038640790b02250071002c0e25014606203550781c1d03407409090310f14030403031142c0b04c0718510025400c02e05081c998409410408264240c4102d03212154106080c0d00090720580c0e0321510845402104601403459010468400d4003a5180203020340ca03a1415500150f00500150300a001000700035580520b40703d0b9002e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 32223000 1250 32221750 32221753
    0x4030c0c05030105010f030b040501090b100812070c030b190c0509090c03040f140f03070308160206041509031404090c090b0406050f1b0a030504080709051b090118090902090603 78
    0x158501100b400e41b0604500c00070f49180404800700b014880203410428506400414041050905100014980401d403140500c00d02548481001d030303442140c2124540c50300a4062030915055803141c030131181014000c1814000c003605214180c140901403070302405000d845403a1038035414001d011584400500020103a0070400810000407800211400e04c0c0760400d0750148101420303101540b0b4210104060461440040b60b00010140e0021016215400141c0c0b0043c0d15641d40f081665140c6041e600182039482544070388004545551100c074101c0c0c02803805e4a540c0c40200184142944182c000d481070315142c00303138162030791b410201807401066503545003441d16103003400082c041d01806840081c0074030000780d00900d505040140380d18220103038055448226851130094078540c00b900c6040514010500000341c0340700c03c1d204444c4126440d061103c6e080b000c849542c81d00ba800095030a0511004980050815202003078440107041d407007500144854542c010000d07415001070103d40320303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 32224250 1250 32223000 32223011
    0x6020d0b0a18051b040e0114030c0f0f01050f03151c0f1b0302040e0a05060601050c12220906231e2710060905310504030c0c050301 58
    0x8108260b16000b00300869100007800d901e0b20000000442102e040221060001140c046590100a8000c9040703960102c8102d1240820700c0500d51038051000c00c4e541e00c040d401d02426130b1802c3c510120b07481c0c5e07041490281c0c90424111110120303500195650b40000c3c6a40313140000034200f6000402103580e140f0700130382d4100103d55032114414a4400010050400001003103090010000d500010790b9005105120b1215841022660b4070a003103404d0b909403050001044443d409041110a100c0c20f020144c041c40520a0b9107110a51110f120115580300e0729981d42001e600500445002d003a002c0360100c2d01368605500d54640342e40c06400c2800034681d180310b01c1819511810f003400d2000d1036020b0207614032442c1000480003c181e03088110300d5105124800002c01c2000c0c141481512103c01c1c0d8017209171240000c40385a0207900816800c045c05141e01d000911006401d01186a80302e90500305a803003403040c440c1541c1e0107640841c0030a101441c440e00300b00c040c15100e40684020b4000300b15 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 32225500 1250 32224250 32224259
    0x1c20030105180f0a150b0f0901080703021326010e0a050d140409050a0f020a0302042d060503040f05010603080406021005090723030313050a170c01050c0f070306020d0b0a 75
    0x4001c9405000d807144d440e92668a040361981c8203951310010964141000d850340800e5130360a040340d105050590008480000203080c0600034803e0340c0c0c04402d80a020b043d25420106800003a840000c2c5481915151264500c881c4109005015455089001801c080d0805251641c5049180d00755003040c0070510307110851000000c01600c0c12601035040100e510b03107071103406074000c2c800320f01c18600300790001918001d03840e0190000c0007101e1007500e02c5101041e4109525083d00060100e041217107040300c00810805104001542e04140510864480d5414a40c0c4030782c21140d030b0340d00c1203c4261000c68100702850b0140b201800140341c0910030301042c500101c03c65140c85803809082070450b80c140300d40c00103000e40700001807610b0014085981c0ca2074014a400d07040c01d40751041d18401e04d800000440e0b01c3d04120000460714210b4401001d49855150054a59070807a000c81780051165442007078448804000780c4004600440c00142e0f070380b8040103054203031188041c40c0c90040c0540f030030800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 32226750 1250 32225500 32225521
    0x7030503060f1315050f010c050601120201050d15050f10020a14010e1204081e0a030c020d080a030c0201050a0902090a020a05040506030403111506061c2003010518 72
    0x990140d01107038040c2003205000002000c10540c2d0843c0b111070b070724044c940c4a09904034500401524011100b20300417190040046400e040100c0000b0043d800c07001c010011011031040010156105050880c10084520a43c0c0d0481e0142c0c4624240000b030800c0400080c20000440c40d118101a00c0c03200301c1c203050050182d070700c2c00c0c075400c000c3c01d201101041381e020507002e5000c4520400351405071201311280030030005560b001401101d0940c01681802402c403010082d10b5024081860064810a081501d064032039801d4140c0903600410414281c0d40000d0b1080c008103c1452107403000600d038503101100900b1904d00400c01c00001c0d1030304c0e010070090381d10030542a4ac08015100d000d40e80b0134511204452500541d808190069400300038401059048007400d40c6178450342c0300b151408080700c0c3c0c002c2c0c29520142c4245412072010085283d01071259069010760340b0707290303102203003000c4c030f440300d2042c180101256030005d10b0012006100c1454800c140d140003851944d10b090b124100b255148 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 32228000 1250 32226750 32226757
    0x905060f0903190801030c05010206010f27050a09060b03030a0c02130b030727050c0403030c06090203031c06080706050f0309070f0b0d1b0516060609020309030403120302070305 78
    0xa480d4800820005403103040200704940d440d00318420503040302900c2e00d80103010f415084c00104c44d03035445080c1c04105c5520000320f4a040701c1010742c60310b00c190b02c2c003000d02640e1003400124030031500070500158103500c16030048501907640e207680022408101d040c1320007181c42c00040035120740c00c1013003240d901541c0038518a0702c2540403108102d44400c100c0c0190b00030601c08030481c2d0103000c0c02e500010361004103510101588002203103240d0682c2d9010004003140c07404c07503820403148410700080c0046031007542c2480d2441d11903800003401401640000780785800000d9445240c4020314038502d4810094001c0500907c546801080d803a820500c01030b010703000d14161146206404000208045000c101004c0203105000002084503100c011005055001d600170068040c1084c0000c2031003000c81d21200b13090b001e181d46250030706440400d02c0301401a5050240c0d1520b469080100700a0846c0c8000c40c061101e03c80110350355840c61510440c0140e036205070300141441440980c01180d0440300720b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 32229250 1250 32228000 32228011
    0x2010f060303082205011d0d0804020d03050f1c06150201050603060705131703070b07020f070314030c120403020f06070f1203090b041a01050f030a060c05041509030201080604090506 80
    0x51402000c00b44c05110007010f001d180980658202000c5130f0001080b00c00c0314900691110036a4500d04801c03405607a90402a80e0080d003000700c082c19000841e00c20300180100c42a1041018905200201000c0c1c4440c5000c01d907143c0f0541d60042040340c103003000140c407030a22190009000c14500440080d8440800500300414403800045148400c1601b44800b0043e00c542c2500940030300c0c816041e035a80b500040f00c201c48500c03503c0d01141c031440c00003400f151422a0a402405180d04594070543c4080081d074091206100a011a0344840300600c498101d4900c0220a00e448074514010013920000f2194440c0c0503a20800004001c03038032004c0d60212045d04000711581e502c841e00720171801013641c03da014100054060070701c000c01445501011070001d00380b41101d400d98a50301009031039000c201490354542c0c0481540d00000d03030240c01c000c0303e420950074041c0c101540c176402c4000d02054141c2c0d80002482150042c0210b42c0c100400c103401050a40c0c0410100e6000e948441d600c032005040b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 32230500 1250 32229250 32229271
    0x70902030411060c06060906040e0c0f040f0c0e0901090605030307030f050f0d0906050604020301060e0111010605030a050706030c08131b050622080c03250306090b01050102010f06030308 82
    0x41c1440108419101c1074180034209030b075200844511a520b41400b910395900c82c15040300030548034601401900f4550468101500c0291400e01c2040a540845100a90481d4851480d451100941d100360f42c1c01c0303540b0741c890f8107024000740308120000034140c001d14070546c074018040c0241d880000595081c1a45410040078610320302d14280c07140c0c0100b410281c4000400140051003030780c990030a5000c45d2090100b449030303480304002c0105901003400343c8030001d0600084414258400e41c1100a20501d4100006a0f1a1200f010074240484404141c40340e0340a5001000059407505c0707005100a050320701a0024284944524080c4200d210050905003050011103201040b00400a00a1400414155a503001c000c1c07103e08140c240d4100010b511a0000c00080901340817481100000b4001c001d030121111415280010030700303484640300c010040360030200000e0281d12601443c28040c21165041d0362500d4002401c0d82c44032145110350b6818010b0400000f40c121002540007003032500b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 32231750 1250 32230500 32230507
    0x5011e0f050c01141008010f0504050c010e0607020603040b061003050103020105090105030405010b12160f03170a021c02030414030309010f0f030e0a06050108060705030c04030204020702280e07020f070902 90
    0x901d80d0241191100c0200d15a4140d13080c04124504140050100c491410003440311078901a05034040340e1040328041c081c0d40003e000a4044e42c410700780b5116400006001c00d062598940101e8059041154221b4410003c081402001e10b400551035047d60305078903040c0b1035581943c0c00204540115082c85d414014044040b4003000420f4202d01d010020240005200350300c031500300d59952901c042d107510300303003000c190125203c2a8510401b0940ea00090b804070b42804000031210740d54841003195003140103000c1d500b203a164250610003650701065005640381c0303050004003480407a041c28030611170741c400c1220610036600306c8480d0808180c90b003045580200d940c0300560141c8035a0030524111300440076114100080c580c00342d030681e00c820040b210300740e4170100d0641c0c45220581d0f4892000e039050004000525058008004640c07015202200300c5900c06d000030000400b0b110310031005180102c00707000c0d04a6540c8070b55402103a501c014006407001c0d8031415116a428010084c0c42900013 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 32233000 1250 32231750 32231767
    0x10f110a1506050901230f0405150109060f02120d09020306010f030b01050f0906010e0f0a0815010e042d08030f07020c0616020d050c03060702070905070201090209070302090406030206030c0405011e0f05 89
    0x88800d1f0700e640018106106903d40407078100c005250180c005804245103040c08a402e0344620320180700360400d500202004040448803c0a0350070407118424400c0e100e20325500140c405001d40d5000b012008012070a41c0d04500d0214101041600070318044c40b44250000c007540d0302c070390000c0d0700586c0c03e0070014158441040810807243e1005100750304411000d400044110001403400030ba2f0320a52154070407644c84008850f410001600c0c041d040010f2100a90700510110381c20250740d1500d0488406501c002e5038406211303401c201c40b0b00b61076040d547c081000c070f40e405101c0c81b0340303541c42219000d20344440c0e91010285150302a8010b4000e0040c01d07820020088204828541c00308000c0c12590b01d40792100f802999814540140c003403050400011406041c01401482c504039401070000c0c04c0d55881000480094102e200d101d98000e480d00000405070b100d00c8011406044034503034055940e0300b000c00160544030f4019152541c000d1141c11064280d0b8058250700c001c9642c3c0c0392941d59040700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 32234250 1250 32233000 32233009
    0x70b0105011110050c09040b0909030304140c0904110906030d08010b0c0106080a060207122303070c02040e03031b0c030a030203070c0503280309030e010f110a150605090123 76
    0x64109000c020b41c41e240170710268031028405001d02e6282240c0a101c1d00500d0802d002d41d0140a40300c1c0d29460740148081000203440c1c0d0f00d01003070781c130302074003198003243c2c5080001c1d400711404c1d00c041d95800100c8046810380c0c1481a06039078851016001000d4041c2103000c001e01d286e505218404890401145690322102c00790006401005108101c82e10b103042418540b00960180030304681050004a1116045000380e21500011440d52007528200c09400c0c00a4040c5d800100400c08000d1aa481640141e655118a421021004000716240e10386040c00c02000701c410728040500000911500708100c0340001182d4002c00ba501d0702507120b0b110b0500680304071a2004005085001c0407070804008100043c05410207050700510802c0070103002d4054045a4000d440600011803141c014101e0794000c49004201c25481d142080042900104035824102d2004d41101c9400c0b0407641303d10910510302414002d818101e40090b0194904807440c0b1031800c68032214507440054030140b803119500d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 32235500 1250 32234250 32234263
    0x1c02030903031b010c020d05070303090f05030313050d020c03030904090c0b18040b060c0c0906030c040903030e010617070e0c16050a020108240f120d0809070605070b01050111 77
    0x40941103d0b165035500d9045662802c0302d40000d0269031800f50360b0b4075030317503c00241c00a030f400440c2c032000d04e0842e4a0f182180600704c201300075203074521268101e900080080008511030120f44c44584040d00151510606204003241100115848200b42030180d95000c4120782d01d8000c12600055034030035a103006011003001d50310004e0045004500c07072040c0e00e901200f42d4000001150100103400500041103458000e0180f0300346160f002d40303450007107401c4c08640203410030001030444003d0840140014150745070890100c001945a83c0c1d80d0600d01c50900401d0042d202104840340742c000308007403641e0364075042e101e040c080d03c840d100400c2c07015000d80101d4486c186004c91000b82c08100b800d0556607140c40403412400210340700c00207400401c100b00ca182a000403440480040d018010401014492454450b0b41c80303000c403001000c213008200a1031000300f0070f64032110705a10b042000c181c00e0140540c002000d01000f0010030000940e00820300e0f054075400d0915502100725616030914220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 32236750 1250 32235500 32235517
    0x1090509070e04110607050307030207050307060c0b06010c1202030706060e04030f05030711030f0c060f0c09150903030c01060f06091401050c01090b0702070f0503010204030503070f02010519050405040e0f1c0203 93
    0x300c0024260b411f102c00400144091400782d002c59019581c3d0700d090541da06000c0c41090006240000340100081c40c5888003600800145802d00204640fa15580c8140300c01002050142e40001400030400030035011380e000501c171068520b501440c01d030b140948010306056000007000b40000001d10001d002d10000f0614100b0a000c581d10340880c1c68003012540d0215588281b14410000004c0d500d0044080c41482031046500f00790901c803500051080f0aa800441041c200d441480724001e503840400290104010359000481d110749000b40070100c00145400c181e04010340c07502d050003020200741c90400300c40c6c0d007860015070313800010007841e0044c01c98030b00040c551507410060040d1140d000941130161181c4268408081e0755810401d0300303e02c40c0c0e2100420940050103078001140700d0b626100c0803680181059403a0000d03449503c0d9002c15401105004141d000c60309000e9424244260000440f40c54000c1905914480b4a41c1d510301e12240d03c00c100000c402c076503100c05413080c42501e4024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 32238000 1250 32236750 32236759
    0x90307030c0602010501031110020c06090105040509040605010303030c082a09120f0f0312010b090a0305030309011e0603030e0f010306080d05210c03040605040f020a03050c030601090509070e0411 86
    0xc1e0384948000340070301000c0c4401d45c0c00502e00d84540046107400004c1d05171441540d001000002d50040600009ea00407100b02414070409200004503034a60004080c40346104101c00030302c0350304511703001d02226403c7e00003804005101042001400105008080d94014400420301185c4400d100007000d100c0d5984503a00001d91219141c402c0900083d48089a605030090356112101d884000da0b480c0111350512200160300340040281514182c000d0441c0c80019012a210540300e44a181c40c59005640013044c2e03039035503d40c480000b03942004101400c030f19000c0602c81b040c91034400902c0d41940c130300c4952041450051070500f680c0240c0c0300c4030050044900b41d41a018042001610541001c1c03d40d403a0401c0152441c180703400c1d60403480744500c041e50181c900715203954031108010440100300700c5070f044140f455200980d54900381340d0b00440c8684002d0003c4824072003410300f0083c040e400303405d6003410031041c44643d040104450301a604282c00b495480d0ba12400c0555141c07640920349c0e60031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 32239250 1250 32238000 32238023
    0x30417070f0807120e0a2702070c08010b06031009020c011b0906021905120a11010203040b0105120c03070510020106120503040509150901030609050102090a0609090e030316030209030703 82
    0x1000312440c00fa100e034071300400d00080601d400c681c040d1100c0e48081445540684590824000c24801d82d41c6a54985003c034044502c80368a0882c55080341d002450030341d012629a4010403031480709006010050105450080c214100066900488034042c022800c115801062500500c1e000350300900c60f00700d84005a444000c40c1040160141a26004800c010f001c1c182200d48610540032103101d820364041d0041000100921040085401841ca824200001ca42401e911903000740059809a0300401c4407c00759450705040001c0c070003010f9901d00d404e07001011070070f24030fa40c045091011160181c42d0495811105801203004001c07603042454032050b14034004060080010190080d030300142c07042d0542e6141c1d02c0b42e40d1400c054a5410a80c07011001c0d00600000340280c011080d803520440015090000e0400003c4481c605070b0408400a103a103402040014920300556122400b910003a51542c01c01e14020707494555070000e50000c1c16000200c0c084d45c0e031010404600196001002800d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 32240500 1250 32239250 32239253
    0x309050c0405151c080405210a0302010203070807020a0b04020f0d0c180b01090305120a140a08040c0504020a05030408090d020603040602030609100506070204110409020a020a1509020105030417070f 87
    0x8080039060b007090140c020340300070181c2855403000100e13032a07800030402418245400c0801400901001c0f68030464410409201001c00c020400d00c02e1035480394001588a103442d0100401c8208000d124004541c00340d00c0c454042080c207401a070304280c059968051003100c170740c0443e0424501c09170050040050a10003d0448a0383c081724000e00c249540501075001c80b1001119840d2160102412a42001f101c20350002d80c031000500f03100c005070800b02050007101703001c106650400341400b800301d600e01c001c00c030401c05040000c0000e404200c42c110300f0f09103071420040c41401f000340000c0c1001740016140445070303603516003001c5141e070092a90b0358034a0645000406900259011806840c0000c00700b4400d103001c04944c0266280600803030305082190f020000542000e00c06040511809c0101140e030501a0008144400141d001804010000d20700143d950b08074955000c1c5851400000d0390042c2c0e0721004894106400448001c1c2202103c80002c40c10b03c10240011321420b58800b4000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 32241750 1250 32240500 32240521
    0x120f0e0d0b01030b010b120c07020d0c091401060206010807050d020f0409080d0b0301060302011b0c0306180b01091407111002041d090601050f01110703050307080705120901020d0309050c0405 84
    0x5040e030f481003196130016680c0310981556401f1340000711540303004844c0044c000d46503980180c05000e00050600c800d40c5015110042048103a401071920151075423504ca00360142c100e10395005101c07034802850030b50300d0101c0aa0325001d060007458841d8900f14480000d558130210100448075004104100c1001e040c80d0003a80b90b4802900c0070016820b00200c402c40b0f26041c0700300740882c0d4040c2c440c001c1c010345900d0705558000d84101c044850b0301100c0004004511180301c1d0040e64001410001014509400c20800381c8a050f4084202c2a04102c0f01b01c0c503010305894441c0c0c02c481181014030304020070075151400c09401048120f2407510100b070005110045212180b000c40140c5500d0710755403110140d040d1200401d00130309030040805038810b0f285500c54040b80b01d20b0008402568003060f101e0740c44900b0f640c012402510006404900082130210512400d07200840c401201403801c110000040d44039016000c0300024190b860300300388140142400a444900360051041145150800181 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 32243000 1250 32241750 32241773
    0xe031219020706030204050d030807030e0d0509010311030919020a0312050403060b06030f150406032001030506030a0c03020409080903010f06030302010c0c080f070201051c0c020c090103120f0e0d 86
    0x40c0300600c950440040c01c540244200c0b400d50707a020b0004a000091514251442480503242004241d07859070b039061911000c1c801050451210303602d15607108080320004007075608100c28495011402c03c04c1c0702002c1000103644186480c0302045403c50103a0b40002025591190300180c0300040200003403141036413050041080da0b20562040140c070064106110590004a945188141c10040031a40142222610300e4a065006102052598580d030369840320038540c01a100d041c0c50564080003003507815000e5286e000d0740a400820300341a0a4480041c000785910010b0b004a6580001c1000d200d264004c803019490064024402c01c0c4031550004000d003d10321042c1c00551a10228a800390300c9880610ba029402210312402c00c4c90001c01030145520444c8200d040c80010000480881c024130700301142810700620000340805d0902000c3c1c01c0101c4154902d1041c601c01c80140006070038808000840031040c0b6041c40c140d08014420b03140d0050300c01156602003484000700c0200054000507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 32244250 1250 32243000 32243047
    0xb07031103071e030908030f0613020c030904060806070c0308190603050307030306090203010602031e070c06050301031101090513021e03012702040501020a02011101060b0d0603140f0705010e0312 86
    0x74040f4409004000724126400204020301b403440400100321409507460a0503000f000c000d100300600c401203510081282d1040c0a81c0d00c2035000032581c0c0c410352400f1f01c58000101a400d02a11252420131002440300b065824001c0902c60300402040704400c00f45812099007000711010042c0684900b4655625008064228006402d00d1800329501e0680d0003a2030403039440341c00940c10a082602c408000c122421360007042150240104404038541010270401000b03240c6509a89504500b00010018002000c680c113000f00b00500700226103901d801d20018071561007006845144820040148100c22035140300341c080d01100200e100c0100f422044640608544010038241e00403900c08180d00640c4103450258011071074040165000c1c2584108581d0040000203a0347d4868040c1e00058120020203400e40395900814800c001380a9800c0c016101c022000344a60100f5440b0b580d5101c07058003900d4100056000003806546040115000090f030051105450f1031110085d80348104060a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 32245500 1250 32244250 32244287
    0x150709180f1505090115030207080f040519050f06030603011503030302090406050102060412030c02150901020403030e0303032e120f0302010c09031a06060714071806120b0703110307 80
    0x1e007221186250110b2812154054403641d0260301e410b40c61502d50a40348000401d2680801410b400605941d0041150100fa000381c81d03290f604001c2402020b01d81c09203094010441048280f056560310020041d01e02d0003100e0345540da5540c0f03c08a0301419841382d255600003900900031040507019005042d0b01042a58100155035540004a9690a041d20098017007190007004525181c407035040400c0e000a9401150341c0303a01c80c071811228040e0200d40c080001d0358049001d00403d42d02c40090740442c00100c0080d815030600c510244140c20030816542d842c007024050003c1441a031042c000001c00e001c000f4101c21400d1414550161510b0800c01c4005520f0103a800031681e02821a080989400200706100c0e5000d0340b540c50041c00001d400c2da41d100e10140700f050002911aa54424640014005445018584bd115102100503644100c03881401c2c158180030709491403440750051600600c2d0884181c64034402500208001a0054070ba1039000081060300c5401c0320301c0d034189165030403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 32246750 1250 32245500 32245511
    0xe0405090a06050a0b22060f0806090d052701030f020d0e0f010203040b0c090f1c03020f070b07060908040b04030c06020c030303071d0f091501020618150709180f 71
    0x121600105c0d803102d03921613804161820201c80b28410081030304c003954220740740003840d03640702c28101d088440c2d2039000c0c0f000c0750301103000c110307118006028010040b812800d003203061107828506800890f80c4110141a2406418003040781d40e80310307420440312a051742001b10344d1640300301d540002400c0302c140d910400784131359110a9a01001442128460754014001c1c4c40107885004039003015501c95100c156101c007c800c20040e007039031000c402c1c1020048030103548522004a1070042e040482c03000c486841034000d0340e420070820f28020100e4400702c0c1d11200008801c41070b0714000c0c58038001c5400100000d0700c0424003104025402d01107174141c410a030200d90080d845901015942c1c40119407031000600106001541c000c40f07814000006036004150107503202416000c20710b55081126060000051003017807603c1940c0500082da044004410b42d140c4088000540c15511000311036007041e400c000400003134100340304074001c00241c0342000d20100c071105040014000b42c8004021440c43c189082c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 32248000 1250 32246750 32246761
    0x30204080f061b0d14150405060a030c0612020c0102040303030b0307090209060909090109120815060909150a080d090311090402030c060c010207020415060f02060c0d0504030e0405090a0605 83
    0x1441d5106801e940c0890f402280c1141514a8981061002003503d50312081604050403900b61300b2807040002c2155038480c0d0609030200800e0700d0740035000a024400203103052021030742c0c1c40d00c00e4043e21050b00700030b1124180f42d400b25000b4418001d07500c45e41c2d4804580841050740c150480703803071407004904030750b010340d243c2c0c0051040348100c46145074401d00405c0707050303d03a05088182c960300521204c000030301e552081d12a00c3e0b41e1400c0329201000900c003802000b014058420345402d184d441079500d50709102d031482c0030070340c0703080d000d00805c1411400c10014405941c442110030302800304101500c02c041c0c4120005000078801b03010803100d1080b002c94400060400a40040c402c640003002020300300404410311880d40d000e82090f0081c0e5408001d180056203a034007a5013400d0a00b032404840e05454100010109200503ca6400b15004081406000220f810a480444404040010302501e95250545220a01c5a00da07a04142050b081184040b408035172285180e00880c0c0522055488 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 32249250 1250 32248000 32248003
    0x50d0c17070f090b0a0510080a0c050403031d040b060706050106091203120504230714010804080703080c1306030c081503030d0203040f080301030507090e01090f02060c010615030204080f 82
    0x1d6000382d00c0c1201d40d01e01d04016001c1180c104941030b40f005030595151075140d80101d1f1060104c4580180030800d0501400000700340340c403c44a07080706a16002d8101400c60381d00420504000d291101c030140070003604d001d2035440e58410340c0e8614004103042e036901d605281200c0600b1007403041c40701060031000009140e50707180340d0041d981a81556481804d80500c8102401045c01400c00d9802c2d02c0d900000ca05e214050807142d0283c00d1011000302a6945019810040d02c0403035280981000b10900c1800700041c03090068482e00c1354142082c0708203640340a002c00050060070011680000d112600003403403905075000030072100490b40c40c0401a0b84030409805082502d02e45c25825620401c04c1b4802c85003a6400b1f15006881031405036a100844e448585240d0000c1c4c10944254101850070085c1602c0751244070149a80500203121512540c0c40301c203201c012254000c2c0c010700c03000642400d400c03001c0d48290080d0148a43d48040162903400040084d082405001c40c284580519408200300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 32250500 1250 32249250 32249263
    0xd0204180b0d0b0c07060b120106230108041401140a09050c0d05060a18050a08090102060109060b030402012105040c050f0303031009110c0307060903120504050a1704050d0c17 77
    0x20002c401e02a07540f544c0840c4400c1c0d80c464503041e2102c0fa51001c0402d070940d02c10071211801003070f2400200c0c0d442d00704101c4017071081840c211520085d0006030300e00c0559030440c08036a030050b0080c8101c400e50171125000d5015200501d01540d0509100701081608e0f101944101c2c070203400341040b1002080e0310070511001d51100d0f80302800540c400d00c0050341502243e081060340000091041c0081e48423952a1031a003d601c5608803080f050114200e04d641d42c4c100100c5004012044c003d02c2010b00c0e20040e0400c81c44084d0000c2d042105000f60140c01d052013440c04442100426820000391a260600605910381030190034070030310304480900603038503000050300e00070103e455025425514140314200100b0140410240001e014400700c1d480b000d0903c0038044807405100003044821151400501d000e5140000c0e4003403c0c5444c0074080440c000040c07035100e960f803000441201156007218088903000702c0c0d102950000d50038490404001451031900e0445c1c891900e211050702076034064070b480d001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 32251750 1250 32250500 32250503
    0x7120803180123060102010e0304030b1501021b010315051207030204050604020901120506030f0604060509060106141204020a09020c010e010b09072715020303061005030601090909080d0204180b0d 86
    0x641c080c07843d1030340d20031441d8400d801c01014000012110000e002a5046402c19881910700a42c280704001c036401691034445425042480503081156013000500031400c0c003001e482d8105039540c2600041850140514000b903d40188481c1e55401c4c4500220740d50384603804224060382c100340108510341818002d030340651005031102d401e14942030503208001c14000700116454442c00d074040820110a124050050340290004503440c50155079552400380c044e03001a040007224112204507060b18010b89091450101c03d03004c440e2554000a2201c840c60340000c100d103840010030b05110001544240d840100650080c042040490100007689000700c03202008a004981079910310290022020500000888602a443d131503002501709121080c5420f00564000814826946071282c80c0c1c01000a2a00d0314503d1441c050000a001d4403840c030071880c107946ca81d9482820007001320140c0d0341203883c0380811526143d48996103481101402c03141000e05141005400490800c45004241c80c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 32253000 1250 32251750 32251781
    0x2010f050c070f0503040905100608010e0106120b0310020d09030306120c26010612020111010515011d0d0803060a0f0b0702122d0f150c0c071208031801 67
    0x50700c542c0f101c009000c0b2400085459000c02c00c40400c46100741d106250007080303401354181c2c000c0d0810501400c0b074107060300300110180500004108580c0e21123140d0306001240907010688201c2800840d1510b991103e800101900100308000f801034541d10450006019980c2070014507564140e48181c000710307100107404420031480510440c080c160f0401c1c0a03010051345070048000543c019821100c0503009000c222012030f800c1000d560b400b0004181038560080204484e080120f03002c282c0c0e01040081c54180007103200e250b1121240283e070103601c1c4034060101d0b282c5c0d400e85d141800e070590045980ca4400d01c03e1030000304500d0740d0300700404143d5403c516600c0ca02862a020800d1054aaa03180040c47c490030454008024200308010848045018035111410480b45c01c24108043c42c0c8810b10168000c003541c00c205404da250a42c3c20046038100141c1e20b000701818a410201d403900001c5401b10070501003c09c000303130340004510441e1070700d424513240741048188909036240d142a80f60315 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 32254250 1250 32253000 32253007
    0x6180a06020f0d03090507090c051e0702010806220b01090e040602030703050c120406020d020c10060e06030a02010806101106070903030f050304020d0605270a05010e0f030f03040302070e090d02010f050c 89
    0x180400340c1c03040780c1c091464101581031034bc13420b4004a1154003a240110000c1c40407a0600855810102e2144c0041089070104030314516520781a400c2c60404000e02c9c400c6c0d490b05440c00d0564000c000c90301c0500071510342c0f007425240500305800603500c00e48035500001d20f0200050300d00c0c2c1e01d40b0151030707901c01201c010403601d440b40d4076554042c2d0050b01601450a900b041702015581c01005480f07031010501002256162400801039807881004014900a800083c50755005031ba2081203140c1c01841160041100160701408030b8501042040041d410b100785000e000595820420060840748265600264140308420455183c0015100290409004c40405001616642200d9401072900324241d06904900180c2c40542c204844035080030b40041c0c0a1505000081c0a541560f90005004041944100800c07070341c0d030302c1910b0b0303051004034000c0045020548207101c0140100420208024a401c00604483d01c0f01c80b41c00d500d0000d5803805008422001842c000c561280d90b40580d0701d8203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 32255500 1250 32254250 32254259
    0x2100e01120e0705040207050109050d030b1005162f0a0f09050901090501020307230a050f07030201140c0309010c030c0207060f0201060b0f030f09010203040506040206180a06020f0d03090507 84
    0xb81541d0503140c441e6014034680030609403501c3c80038101f003602a400101c1da047e02070802500303041d100e4160004042c242040a1466142d10103c0e00c0d00c411782d40348c150303a02c9180302e540100504c410307500100005401028007404003440b0b1403004007618880b500169141e1503104114500340310307102d00c2d000300014035010051440c1941c0020341c000000c10000c0341c00c50050f41d6941c2203038070441e2114040750081441c0b00751400705882000f00c3c1c400301b50310245480a04103021384140038000001002000000304c3c07104240c401e4100104000c255090541b1601b40003e19503420340085801d143c0e19842c1240f4042d03094800d00814000305084e40203400f41030304001c012140328080402000a643d00d91100051007010040100111180104181d13182e00300303e42c1440310721001801005907a8014030902000c940d002c102d03150030aa04940541d40d9840030400c07410343d000b600200700d0f40228400e100050007500030561907070480c542005c1e0b50707107882d102e18260308403015a60080d00070340c000030043c032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 32256750 1250 32255500 32255537
    0x60609010603230103031d0d021e0d0602030705040311040506010f0809031e0901030605010504031203020d0906050711060603070605070b100506040303050c190b04110111150402100e01 81
    0x440701e84040503040c985802d036081c01e10b003d4000ea2049000480e609007800554031507a4203121045070403111001640740c9a00010100c0300840c40d44800209400280c20050341e5510311160110340c400c00964803460407034000b030000d0f041407005441031498040b04102034a030610945200381016180da0350748c1c5a5071001110119030040c5601d9462000f00702800010013108d80c1002d000403690f0885645a0a0070001000d6401c0340c1e00040c184203060000340000f0f8501c42c0301e1540d09105250045c0c4aa4400c003c25000d480c4855001d1315191408061100c3c85501020402842400c0801c079500c588612061642e1281107128000010b0700c24442d203c002005115255049018224050841c6490704005030150340b080cde00442c08141c00282d542000501807044008900c002c1000716021110ad445c6c0d911000d0f00104000e0034045680c5800440341c2c020080d1a558008660840c0d569105442c1c1d10710803103030155001d920510224408580f201d02c1240075204114042c0d55130645289500c00f0b02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 32258000 1250 32256750 32256761
    0x15061602121506030c0405010609090207060209090403020c090105030d020a03140c06090d2a081c02030a0f050109020712080403020106080a030f0813080405060d0609020d06031202060609010603 85
    0xc036030080618501000180c0100b200712440041d00100d5201c9003080d0007018504125145054003650034031004000903504564840d04540c00b00c02d02603500da10700e142010003803092440e110360100c428010701c4207042c1e00140e4518803041c00d949070302e07aa07601d88003059655a50300840e0030040c0e03c03502c200c50000348540c1701d29400b031a940c191541440c0208000a0800f10304846d1450b140d48150740703001c0101d44c00303001c201c000140a10003162444410244170f56448103031030068010040000d004c004511480d00d1095210100d400440d203030f040c105003d0f0301400c0d151151480081c1132800210303004045200701c403511a84a9907005cac2c0c1d209201001c2d201040018010303405d40d5030364034000960030000c0c001051050310a035100d18a810034100d000e025544041c18110240c401081d4900000d000402100c007074400480f1910748400064103160041c1c505500f0a030301080c004181c500302400103400c11000e50703101d00c6001003240300e41601240c6d07070132046a0075540001e070100104885400fa6015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 32259250 1250 32258000 32258003
    0x1a0703090306060e1e01030b010b070f060e0304080129010e030708030a0503040308070e01090605030a1118030c1008010b0f090612060102060903040e0103080d0905100207020405150616 81
    0x500c160340e2516080300300d480c0b5911480c54210300740c0130040034254803269882104c10140e40e019640d4119150a000d400050140070641e140005d034910510901c0001d0140640d070082e424440c003c801c40406440381c00a11603401151309040c080641496030250100144c52400700c5140b00c12406001100c190401c0e4024a07018040c1d10b4003c038040c0f000b80b00524200b155900e80e076070750341400d1500a204210040c001d100b000410040300260b60ba00490643c1103881c10703e0401d4498407003201c040000d12501841c5606030600103018003802702503001c85190b00740c00300c042c1d5034039a1031601400303455680007a103000080c00d9440180724114076280580300c0300c101d418105041c001c0f0f48021070b003c4c2d403114200d1f1500d8030308242040041d60f410041d035a0302c0b045e03060242d4200780c03a00c0e480002c08241030000421490000c181c228806005900000710607410004990b600f64020110100039481b03140264055401d15001030f0510351448401310740c00070080c100a140c03c01450f0710106501c0180d10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 32260500 1250 32259250 32259257
    0x503010905060f15151c052203030605030d08040203010c140a0302070f021e1f02030714161508071b0f030c06020c0708211207020a02030102040603050105010e0a1a0703 74
    0x40c1c00c1580e455485503061a1208000e11a40e10048004d044e06c000c507405402d80c9032581031a00b04241c015403440749031607446d0191034040c00b032442c134135080d00580910f0300401d4040c41203140c1d541301c1c60b80c030103012030180d8002e6000700300349600c90308121240c4005111140d4145010040d020026206c5c2d401043e465009840c030b904400300d00d60010700064100c011903080915800e894a003949000710002100250800e1107055404140001035202d01070110042c24400d00d04600c24034002c0305000c241c80540c503060f0148001510381400c881a166110134020003d02c950000034611070080003510b11065041c000b10401950079540c158003a924210304a00b045404043e0400041d102e001500140b032090b0b002e0000e0f2400c102d8500c3c0b07480c1d005055403c5221036008410b00c5040400b0445100544022522625a90b040000e91902c81140ca00a4166100140002d0001d906134480c50595000340d8458802c000d4070020050045910301512102400c0100c120602520400090617070a12a00303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 32261750 1250 32260500 32260531
    0x11a011b0308060112061d16080f010b0714030a0224040201090510200705030f011103151206040b0402090601051207030f0914010504050705060c0604061a060c0c01090503010905060f 80
    0xf419183d0808080c260f04500920280a2504503150103008448d256262800c502d16110100c4100c03000f061007a13000d0a40002545020700ca69410070b554542c01c400c1c1102d940741c0b50428002c0d5200026900f008031810b02d80152502150651049070065070160b42e546680e500301001c120811401100e40d1007070020a0303c440c0d06c03901d0011410f02c141c17646c46000d040d0301803030581030605180700303143d0038403079645002c1c3c0c140900c8590b0825030390800003580482d00e00030360010100c1d06240c940030f15143c80b881440208420426424100b81c4114400d0b1244240342d21803070015940750050000e01d02a100e158000200f40724440d52014803882c80c4404003080400c2d00791034803039090300400d05171111079448004200a0090800c040001803c0c251881490907803c001601c1c0c40b420b0103400204202c3d01d404003001e405000c59160440040c005210550310221103480640e21403803071104a011921030100099280340c18401ca81f500e5800c1005001543c2e243c0d5202401100014140710401c560007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 32263000 1250 32261750 32261759
    0x170f0307200a0507050a0602030c0a0f03020c15031e01030201020a0201030902041d100b0f130509070f0803031e061810030803040c0e130201050403060c0c05011a011b030806011206 79
    0x2c1002e002c945001c0c2010300703800c60921062120050160f0010300179540200126941010005802000c1a8001c4c3e00018007003da45800ca00b04000c204000307921056010001c2c81d1030145000079400385c4100d60051681c4d10a2100c8036100308000d20000c2e001d604418440c42c0903500a8105c100d650784000c03c00248190f80c802a1208002100c90202ea2541322500040d918030552003001e42100044407100c0e00010f0303200000300c4050300f20402141c00b40d00c88010588030f42080004202904441962340318181c3c94010181d5290811508030240341c03144105110b0b010759000c840d50141101800c031117225100ca8280c1480f464020300740060f2400c450030008041618400910301075403141a0f11681c1a2a22072103a00b55000504a8012022428403810060703810208403411030794003030008100454402d005903808068000b02500729400d2010602c0180c4801040741c10409090721407420741c550001502003100d481c50780007004540b410000c21070940c0503040c010100b0b00c03054404140107455 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 32264250 1250 32263000 32263003
    0x504020a182c07050306010e061201110d020a02010f0b060f0901200607080106110714030a020d110a0e09030a051b070306230403021b031006030503030103170f030720 73
    0x80b09900010224110042c0001c1d101400000b0081074128020041941006004081c42030050500341c0705031441030f090181440207400161182c00502d800c940c691940c4440e110181d4894040c1c00015403a180d0001c0315000300b480f486100c50409000c0303a041c2103681222407441d40c00504054144070302080401c04000a00c01000214689040a00218206003c0147c41c020f0306030001400e0080c007842071304920000290460440f8502000c00021075000b00109041030310710f913800fa400c500428201402d211418464540c08007007950201880303a6615506e03945030006940041030794200300400104617200b44c010341185031400c014461040e043d1131100d8541602d5510841d0b145841c2d9a81e40c11102d203c0c00030544511006000f00c84503e01698029111000040041e00c1450350700d481d100a61070800800b04101c9109100b0022162030781000b0351f1b2034000b4401103414140070039901400d2035203141504e040d661410200307411501d82c0d020684100d501011940c4001501e081c50b940032840 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 32265500 1250 32264250 32264291
    0x1030906050a0e0106080304080309010507020406030f050f12040b120a150909020102010609110307081923060103020c0d0302070f021c0b0907050a0311030a05011104090c030504020a18 81
    0x185000001801800c03c0241400e640b030700e910284050f081440100030800010080341c000c120241707001960b80d6918030014000340340b03d40000c1c042100c004450420014002200447d5442c5401110010560b1400c40d284511031400384039450f51092041d40c052125052449802a41c1c025000c1034415108030022002d45160740003034500b036250072000c01036507020305c20701000d000f9490050141e0701c80c580038600c2c0c9210241040c804c111103100060004100e018031030603900c2030754206200140c004034080001d052050600309034020548007280d8030b58041c0c402c8654424040018007803c0689500c20340003500900340554071386030310f094881c00681c4e411040051102098803c040a604181041030703032840024000803140d4040703a414485c0303680d10300101c01200c5e0f101a1009580c400310021a0400c560664010510340c2002044088600a00c2c00341090700c11200e0304000004028030114103450f8141c0c0c0c080c0d00541240d030213002030991701019074a01c11781d034000804c641c0c000d02680c06500380d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 32266750 1250 32265500 32265511
    0xc05070605060a060914030a05160501021221100807060f080709030519060b04050717090a03050f0307020f07060206011d040c060507020a09110403061b0903030302090103090605 78
    0x11000215442041540d1041c1c81e0007402c00c1e40c0341c1c0e051904240019185451034001d00c030340b0360a0100d0645007650108013488a5942c84000d841100f040a08500c0c110341040c040c090150140e5043c44500080650603203d0003204400d10110300040d51001c86018031028022810002c02443d0105617a0810000c1100400b6141d0b5902014041280020180003010304035400b0000482402c002264000422110014504810f0558000b941c58428003c00750a00c0d525001400d0000700038146070402c2412424803002940d44035a6a1601c1404e604c40c0390034800100490414807440c50442440005984d0189160040b6030b4801d81d8240c915241060542c04500180e200900521281c1c03841030810f2141e8040101c00a41c50030030380d44881e0814540e006070010084c1c00b00d8400c080d545c51101e403400529008030704104644c1c2440f001c038001e600c0742c002035a0003410603c8428882c00442660080a1482d654101d682425607408030080d49c010165039040507180d184002c085040303481441e0180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 32268000 1250 32266750 32266757
    0x303120a0b0a170d0f0c0f021c021f02010509150403080601050f0304060e01060512120f040302130504060c0c030c0209090f01020d09050106060f0207061115010305010f060e1003030c11040c 83
    0x1044c3d41100801640d50446088200000c48a4600c001100141c1c40c00c59a82e04450000300904005007082c00c0080200e4080e6202605064040030008003414040c103e03905540240055520502456030b03440d40107a440c640c5a0300c0d1400100030030706c5030481e03135002081450000e181224240c4074807500c0e04141c0d000c0d5811795440525200e980f07400d03c940401040f080e00c4030550342c0300e50b54003103480b4106260320329185030740096480e0164900314122005558010590410440e10740000c1c2d00406c421035089030902d180c81116403d4601818043e4820740e49a87c8045902405500b40204404060305002c04c40c4500e80703840d12810404e001405000c0c5c0003510001e105480c80c1006c2d829a90a5840745050091070391100502c1680490704800760382c22400d2505c40904400c4043d071030041035281d68007210010000200410106401042c90404002c500340300d00740e1070345aa07800110080d5440401c482c5800010000203009501520030340340a040c80c000003510f00c9000c6010344600e4138046002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 32269250 1250 32268000 32268013
    0x406180506041a0109060509041b050a030f0504021e0102011b0f090b0f041e0902030403050403062901030c0513060804030f020705030309060d0e07030b060f0303120a0b0a17 76
    0x241e00703140c4500807880d000000350b000c0c4010f840001800c50a06802004c3c00c01800140f94006500c0340d410012008486010210200e4102030780200a5040003640400080c00c208544d0984080f601400b400340f07400030542580d2200c044100242810080c2e481410740d52150103444102c048000d00c0e0802c410992111500c04140580041c1030710003540290f004420203004041c40107041c401624127a4065210300007a501b0416020f5407100140d60055201500000c20041010751040250088a03c41c2c80180402e00102e1400b1404520f8007c0120303060a4604140c0034940c46908030307210840301c9080061902031511f8441800c0819a0880400300d10881c00f8402011f5110b018058054604c0c40501801410f040010f5120704c210003045124074000b003020b00c1855070304c1d8401ca40480307204007100d0005681e8600003941300750446109124022180310709000341404811141d942842c14403070302c0c560f580c0b0b9030f00d00300a01901c2d610940050810310003043c0380c21042c0d0300c948044040001004d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 32270500 1250 32269250 32269261
    0x510090b01060207050118120203030d020c0d03060902120c0d0e030d06050102250e060a090507030501060e100504052b2409020102031219020f04030b09070303091404061805 76
    0x30f000500ea05c440e0422680c0c142442180c100601c40300d041d00c0400c52080c0205046000003481c0d80501c601c1d20000520000d894103580d100001c3c002c00c040c0b40394030700744603581d030b1100140700f2806a41c1e05210760524040000e03440016000041103000040707400011400d00000140780385400c4424607516003035889005102943c4c040011085050024201d2918118011201d512007841407041a800d0403000003c2a141d83d10001d02c0c3c806085c0c500030820403450b0a00c80180a010300784030314030114a071004e952145081510502106413401d444241c505072070881440011180440804140e0300d004140d17284041050f404040d01500510990381da049a411070a81c0c00c41010051880031441c03c0303020300050340c010065a015014800300d0309042d0b41d4a903145003030003520142d00c1c40311070300c0000c0310345400d4603400281c415a03014001e00c820b156030350401c0e10350701c200c5400050046080003004101d0f255020524068084019201280c2070341c0d070710b00205101066095600e00203454008101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 32271750 1250 32270500 32270503
    0x4170303010f170a030e04020904022205030d050a080a0902060a0c11180604050709030b07020304030b0108060105010206160509100e03010b01170a0b010318060204030b071d010c0510090b010602 85
    0xc0c25105803c9203004044010340780c0d944a2040c03000303060018031001e034406691181d065031622400680b040d541c401d040340d004030711401210030064100d1402103000c20103050001d5642c224094039204e60340b600141150560704c812000744010303405a1181d0b080801a101c65024000110854803405505d091901e8412829a05101c006000d0301500c04440000305a0190007a0400019200010140c82d10310086964000715040a8424007107042070040540d400001002102d008034042032050340c032060015140c403030070310a0b03600507801540411000740c15141450f8041c034171820810b1600b170381c0d040442d500118099801c004250801c0c800c0e070b0387c0c5c282070007081c001c03500901e001b1102403006403540400c0400075000c1c840c00e81e619020650240d000394440c000040000c02a03400b20001898160043e501c540021540d0100d10390103e1040c50145d82003660f943d148080c003038002c000c100c004440c82580031300d0a4909100ba06952024919244a420719550080300c0040c01d940c10001c019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 32273000 1250 32271750 32271779
    0x30c01141309051614030103030302090103390806030703030503180f07051201020306030d0815040e01020a030c14030406020307050f07050a0203011503020616030302090612060a0f0605031801020417030301 90
    0x20701840607145c1c140038556100811203040d6641401c00603102c2605500480c02800442c4011001083c03c0d07948101021a41c401200c0ba09040201c10040645d003610454441d6025a00f00360140e118000910000f8090030146d03521080e44852000700c3d600c0c0000c2c441c0390003910460f200c40c0d604041c506202c18148520003050361422400207510303504122000ca60344540f000a03010030401e0b26008600740d08400f6018540000380104107112404c079504c8258000d51100c0480d40c080780c94420310701c6d407043c05181c0d881c000e664503624081c00d56940b929050080d5200600b183c003000b8080050400500d0f1160241c207050f80510000c00c8060304500c1030500715a0b1a0100c011246c03c02d010030001a03480c0811107048030990f9410300c4002a030fa26064001c0e00030f0f0003401c0d40c0100c3c04248081c900e04141101c6200d2802262940e50150b910340060384c400416000c0ca00008030100700191401c1d64410148030600c031038000062400f961603d40c82e5084442c500c002c0d240344c2001004001e00207840007030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 32274250 1250 32273000 32273041
    0x1002010e1006080c0904030f0c030509060403080306090f01030b010608060d0b010e07020105010b090a0303030b06040503030a050d060501140306040506210304091103010803040302010c0c030b01090f05090a02030c0114130905 98
    0x1704081c185a10060000d100d00c1c8602d070b080281032241401014030032010394081c00400760070503803502d449241a00c4141c01c201c035801e00901500c0c000414018141c10401d048075003100c81000a039007031400c00c030390051001741804c1d00030101808490005503651240d034028038075000e5a40c2c0d075083c6000000d00b544d4042e449100c401005101c440c0c0c056607015958400c40e5490708000960010203004101240600e900083e8107000c0458903a071002c1d0403200410082400c104100215900c89005403480a031002c4034004100303040c00060a1420b20350f01090700480d00611008500014840f60403c3c0300032641040901e0308045410460340303c2a0017050560103071929542d05641c14100c00c91b035240203d20019040001351301541c414030100a036007402441d00580b040d00950384030200c442c050b05040c144c080740ca62610001410a0300080358104800d0390003006404d0480080c0011664411042c1c84084014001c01007004001500c02c0e41000a20520102242e185442c544081d00c0c81c61283c003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 32275500 1250 32274250 32274259
    0x607020a05120c010906050901090218090703020607020f0a060f0e0d0b04170c010e0c0a06030209210708010207050f010506010801080703031407080c0c0306060f030c1002010e1006080c 81
    0x10010000300c000c140e030100140b200382d555803a018407020041c090410548090001890401405041c61064004816190094404161000181064004d001030403107555800c0d422400007440140351000050001e40c1c001007800f203000c1c66003070005080788020f40c41400414040040f007001c0d0740c0c010b8805c6001074400c840749024030320035890703820901000500003040e404542d030191030340e40c0c800d42c00e85800e58000c4008015020000171402d584181c180d0010b403084594200c001035030b40c842c0c0211030300c8610251801d060013101c410341140d64001c03140d0408480c001c142d40892a02c2c030074400350030000c5c0210b00404549458001c42821207102900780340c1088840001802480000200501201c1d071500c1c059400003000c4501850a0041150003800700784005440000c1000c0010040c0c5441422010303208191038403020000048200d03c00590150840142c06005181030803c6500c00100780c00042100365445061500740200c08101d440040d5440f5400e001c43c450400a4042c000c0301903e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 32276750 1250 32275500 32275513
    0x1406040506070206030915040309031a0919080d2f0a140d06030b010303020102031e090a11040f24060309021309030c0c08030405041b0f0c08070203030f0c060702 71
    0x10200c1d610788200308001c0d000703050020115003a03c00420000000c0c07480300c804e85446042c02c2c500100406928401610203810310441c0d0841075a400d100d0a01540c0c1000007446c030482d01e4086501d41c3d140981c41030340c20307283c2400440d400e5041c90144040c1030710701c000300e0880c1a0140341c038812124032032400058804418809403041c260040c582d0442c00d0160a07155440d40da070101c10b940680708941005040c01c1d0510000001c01d1740540166008191401004d0f5030740c4040d120101d40c040045a050751180c1c010903d101c08160551401803403102c0103000498494007882000040c2c2d00d03488030f00d001424500654440c110b0300642814050305241c9028084a03010b034000414036030301c044024480b035950301c0c003010406000348c0041000d0f5500440f1450007669801d001c03503e0741c0187c840c880c003940c01c01d00e003100c007003040c2098400850100e0700c070b80340c0d02641c0003001c861001c0c008038203e500c01020051900940d5081001d001d0802c10440b0351a910b20201c00c84504225010f40818155071154 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 32278000 1250 32276750 32276759
    0x80106180f170f0102160308090304050d0303020711030c0120010b0603070f02060106020d08010506090409060507020705011103090603010627080102071112060a0e0a200102060c040e06010819020309010501140604 93
    0x1e21b684c1c040c054041c50b1103481902d6203031507103003103110f254821035100c0907503000f040c20540c040d0040c200c003034099007400c00441041e105142d114081e500701580054030b1600005071003c440707146000c99240c442c1c00064046881d41c0866080e0340300b17031045404a1300080d1203008180c2d04108440c0581824405030102d1203100341e01400c03128040c02464402c55020036040d03c039840d1907000f1b074407880e00320328184180d08001030042d448442e9802003900240708402c0080c0744110000485284590140190b0b01c1c50303203400000c48030480304150070341c16610708403c62101da80807440428007600000c000140d65000c81d01d021200020414100d901a141803003084009000200b040da81c0011040300c04078011221030120341c100140414028003c01c6104203440d00c14000386020300d401e280a0f000c40f02152a0b280010100f80203510030f601d0703c4601c080000d8165407144200070b030400080d50303008415800504426080c2e03082202c440041c1c0e9940d000400c0f00f9142101007096680c0291070796441c05080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 32279250 1250 32278000 32278027
    0x15150a2a0605070801080c0a120609020f0303031609061b0204200d060305070501080c030106030b0d1a0a0b150708031302060c101407080106180f170f0102 68
    0x219014585440008003051280c421900c0d003001403503074400c03410811442e2440300603040704420f000d00d11940c4030b10504c0054a00300f12507940c0540c0e21240c0801040490b60350b07020301400031198104c0e00700d1101101510107071400c10155020350111b10f42c582c07004001c404024075208843d8844401c010700d2030030f01404105100d220041280c1c0581e80418492030703003a81c81e4907403ca032008078480320000003000d40c040142603004d801940e100f00709540c0c10381d650360011642c1e03550660394002c0e014020401045150301960116a54100181864014031041c1c0c0301c0c219060740b0030900140c040050010886480910300c10014010011101c80f0544520550040c04500031007100605444002010130703900298214400c40403503006140c0b40e40c0c1c940792515103031a11a100c058802003030512940b5110188c54110a0f07210300c1d816522a10107038681541140c0749443d900341c0b0240d4610721540400c0c4103142511403405804055068801c1d144500803462408004128a6180d644180801e03400b00a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 32280500 1250 32279250 32279267
    0x81b1f0c021507030504050c0a150909060528150302030f0702150a0c020708010204080102040e070305061807050d05040303060618080c010c210309020405130f0204020d06030203010515150a 83
    0x103524001505c2d030f690780340a528000f94000c04a521140c0e0902c00141960b5441c50031444920740c0c0d03512a003646d038030b80459007551500d01603640c2c03101c01d01d844a0b00052500030306034070080e80c95407205950b554401c1711944143c1e5072101140040d80000801c65240c0c80000b00540200082c030080c1095456801c080003144805015144216120f1546c90b002c02c0c420000c2d0300180507010021551555a80001c41c000d50192107501103250007400022040340c01b0748605481000041e0a400c1c0031100940320900300b0350018154424000140204409440140b180c4c51241b84280c50020b011400c1c075a002d07100d502c00e440000349011082105122040010904010b00c00c42070910304009105850440e084410b503078944294080200c07034602039594586c21200d007890090358100034a483c3e07886900d0703549094600250005005246a60060805500800346550180310000f900c03512030380000e094880c00d072a44004410140108001443d007600400d5164400800d0745150030806c0001506800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 32281750 1250 32280500 32280511
    0x30c06051201150c08090f030f060a060501020a03020d03020a030f02070b06030105090c03073c05040b060702031b010318080d0b0a0501140a210e07061b081b1f0c0215 73
    0x1c081035100040d21070071f0318080303c44030040a460f0303680340d880380a60f958041110000221800d1007400107013075002080620049400da0301402c4401f148520560295118920000400d43d50ba5403290400460f44098160948548100401414176600705030a40b840074015818036004241c682085640026215040b65000c4501a40050385001c1c101602c49084120b2504210030015810030111009101c1d015140204d03000c212070715100e000c3c000e86004030f86000350107034000c80074689074009207030f00c1c000000d00515020074500c0d00390440494102c060f1804560111000c40c2d82417017000da03400349500a420030349215100c58a00760000744031540540d1200c40c2d5003400241080e0741d40c4260780f41560034501c6004601d400050362480001040c180d440b08000340582140400e1042c465503801e1a0034903050700b02c001007540c0e51200d0006070302901c54995140d0f014120343c10400000d000c00b0b43d40c4280044001c1580c80320038250800d4498803190781e003c54100721964140d42c09144034603034108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 32283000 1250 32281750 32281763
    0x402040306021b0c0a0e1801020309060901061a04060809121804060b0304050c09071103030f070e030601080303011e090f020307080901060f0603050408120c0301050a09060509070509030304030c06051201150c 91
    0xa456072001f50001030411a40000345500010401c0608040020124041c450070402003080075628190003182a540102801160740100400c00c0294070501d41c00e50802200425280440e41c1244100391a1f403105803083c4480c01c24407902401407405101d0301d40140202d42c0e1241ca10300d41551510f840c0c0d019180030390700c90300086011804080c0b14101100384a126001265920b003460030000403201c008070382d1800018460509682c050401180c3e45040358200ac0c003c6003035074200045050034803440300d40460f035103480b5080041c05100c40d0042d40c100b104180c3c030040e6a4100003200520540c0010322107a40303a814040b04200103054003044004480f4140b800107140d460742c1c6004e14141c8503030400c04800707040c0c0c0c0c42401081040513004504803201124080d000c03c4c2d80340c001e0360580380c3d144211580304410f440022122400340c0020004032400809980c03420341c0b250b64100001f00d107a04408009440402d1034200c114424124030b0160861040c402400131100c600244244544000101903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 32284250 1250 32283000 32283029
    0x11d01020f1b0a0b040605011a072609090f220f02060a140a0f0e100206040b0406020f0a020a0204150302030d120b03010218040c0306030506040305180402040306021b0c0a 75
    0x1442c0180186007180341c3c0409409864149810080041d000c280034400e140940091120003050800341124542580543d1503040f03401c40b0b03500c0c403001c41840c41079060381c400d0420000d4415910969058455400085801601c0c0ac20303c2d07000540b00320504101c0c000d0003080c0900c0020440d8002c0c0b1480441e4112141a55121071a1045400b0b02803100c4903401e07041c005c00c84980c0d1607004003031240e40e500a81d4516810181030810407908105030f03280200075070045400716000c03600701d078482c950003401441c0262910700b1003000e1421a43c890004040143c000b02c94510031403400e4005d42c003500c9602e45070f1102032070454000a841e13400d040c10040034806c64481d000c4440005030000c080c040c1c0010000c648440f018180f401009005103482c1d0300c510f242000c0030b800b140c0607120301000d90390400018150390740c4641c3e0648066011001c60700665485540f6082c030f641e200d000601c00386d8403d0001585a122600304580308030400800003001c1c2c0c201200c10300c80c0c3c0e05c0d201c94050840d0710183e00340c2c80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 32285500 1250 32284250 32284297
    0x120a0809010e10030b01020d080c040e15030601030c080f0d05160f020a090f0b0301020414100509030106030f0506150913080c01091b090506010c0b07030b0a030302011d01020f 77
    0x10501400b801c0d50741c00440292418400640550080b203000200707800351a881900518120b843c01c070110f80c00b0003124000e1100307100f034515441d069507018014690707803080041300e2400680350040c00d80c003c80300f81c1001c18043c0200c50040c0510020200620020309035081e2000c1c0284c15800b4042d0710509880140310500240000c0e2441d0229507600504400c24641c0c44550000103024808514036003507007016614081c030304051007240c00300c4d041900da602040d00040300f000061046084500c08016044c0111007065500b03206002c01103104120500712445c0320710780282400b500500544032851241300c510407607141c90044682c41002602c8c0007054103014a0810910b01500c031100d44a58a02006901008081c1c4001030454500b0301c1034200346640c4206100c1541c90460320117002550111090700050010501140c015903503040c00b168082000b008909600400c0d441900142e4540c00495071070000d441388680504d01c160000d5103004181c91020a1511036401580141080c0500541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 32286750 1250 32285500 32285507
    0xa0801140d020409030206090c01050705060a05060a08010c0f030e030c1e010204030c1412031603080a0902031b040606030603020901120302030f03090d08060405070c0611040503030a0309050c120a080901 89
    0x341d0140d4018810000600d05040080d9031300000c649100d094030070b00180586541c0210142d403100e1781c1c003100030541c1350b650412000c041e00d0701a115136000002441d002c540d10000380108010f00c43c0f1552001c1d80f0074a0460000d007600c0c0044c01c421807580042044014400000c581507086c58003400348616403d07503d4a1150091040380c0c00a001c032440d4803030108079403103400c2c1c82c5500707440c007200c016041003010b000150f00c0348294a0442d9202c4040190b203c00a40034842c41d9900401100000031120f540b038010070708001034040c003031604880d4034003100b903e03142038071462018140d54541001124150f9021804948041c001c1d00025a100150042018820400c0347d482440719842c164036800d095555039501c03801c014008000c115400001442d6041510803548034100a5403a400a10349948038a8018140c0f404e02d080c18440421001c6002c6d2401c000070a245c2019540010342d0981c242840750510f80c152000328851001111002102c0c0c00c001221801240c00440640d5942e1140c00180e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 32288000 1250 32286750 32286769
    0xb01050c030d090b07030e06150607020d060506120d02030f0306040204030f1b090c0507020111010e0618100c0c140c0a0e0405010b0f03070b1804050f0711030a080114 73
    0x39580e8031002601c07403014680e94100700da245225028540441c0c596060a8040d100324050460b1150f10400c009012041070800261020030060040c1d80b8002107a00454600c00f14440e09484050315801408030fa800c2c11710002d11000c0610340906540241200000e403071380305015581c0d22000000c00414440d66469040f2401540d2210351070201041b24684400c00d4982200c0f0b214501d43c40240001da405428000d2008102c255565140340220f20350040da14100c0b140507483c0b0941d81c440052407440400c00c40359001c0e20040414041200745420105d01d00707003c000082e000c660410000000b09034000c4040c400c003e900505807000001e000925910381600d180030705078012010400000c503d10703122912401180160020711416006400388105540c2e026042509135015940030001d150f164005000000f0803200c5101501030f1820008007a01c1040d240540314424020030301c100103030405107509400c5581070183d4100b17000307007401800b01401441030381c1028540400c0701c0031030f0342c0c2c10901 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 32289250 1250 32288000 32288017
    0x50306040f020d0207060506030f070e1603020d0e0313061b1106070b04030e1804030c140f01020304060606020c01090f0e07050903060a050414030702130e0c030706181d0402040b0105 80
    0x2191240305a00b41540034003008c3da080c41c0a800b83c9091400352480101e00c04064401c141903541c2c142d22485031400c0d09030300454004007019428080580401c5007800340f01201c1c50140010358507000b4070480b420b002d0f4030917841a03042c0882c50f558241c0b0b20500320725500405402009109511120001041181c410410000c0a000c0b50324100010560051001d07100b400c03050301c044422003402c0c01c00c842110b20079903000d40451420b50344140010509404c0513840a07400042d1030303446041003407007420380c1c005a034103c8800d40c503460184112507040210001011091078002c00311445d000c003512201d12640180b01901e0003140000b440d0600034000c5450b0054041d044030002e10b020903100005240035602102ca81c0c0100c00042d05404000003035810150700204062039060b040480d03100181082a40c200a82c0110100c1e154569001c1c0b101c02c0c0281155140c4070003181d01409254050030b19600a43e07071020101e180c02065a01c030080c002e5201c0d5042d035000030a1212400140d4440c0070780d0b0071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 32290500 1250 32289250 32289277
    0x501050108100903230c030f042306071103100e03030a050705030106080a0207060902060d021801050901022517060a0e030f16020102010f060f0e06030a02030307020d08090307171903050306040f02 86
    0x114591100101340041007110742c26009142005006a00c0c40341c4c071586985e2b1a9441842802400e010a51600a1001c94680101161143c8000151410644002c0459000a070300084100030f5203078074074000c3c140d2141d031900c0c000e4034640c180391014002140113000103148903800316002040114540c00401c504c1e800600954460f80c1c401a0b0902a42c045120108541d0001040c420f480d401841945c03100a0141c01901e100c844009200001140045d00300e0a8110743c18400078074141c2c400d00144c889a0300300042d2030300740340c403114000658400d80e0449501c0e90042110402001e40c120a840e402c4564400d4074020210600040b40585102c9075105580791030588000380001044000504a690032070406c90243d54860826858000290000c0d4264104001604c01403401c483c45500b13292207450320604100ca05004a89040070540112064a28982041c3c3c20b009003000346010301c40303640c00c1c8001340203060b540042007400301a1089002e292540c0c031144c204606501a03a081030280308 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 32291750 1250 32290500 32290507
    0x12120609020901030b030a0809011803020a0303052101030302030d020c030d05010f05040c020105010b0d0207050a080a0903030825030203070522050a0608010806070f1106040501050108100903230c03 87
    0x2203400d00a5001c29100c9001c01e1410016030740508002c2030844049800481150406113000c0040d50301d40300703400ca013405114502c00048010b0741d458480d000998000c0d940d440d05d07648142c0d46002c5003000200504d000101141c01000001e0380003040710800c050101026840340314125040d403542c040c003451a4821420304002142001c86095450129801110184068010000164200d0b5400c3c003955402d00c00c1004448141d0106400a20000b8032440481c1c0702c08000f0f403181c00b02034000c0c0803d20001003d21008006040c0c0c8000042d0300a24103e0703039162160b10040042007a40704d8000e0030410b154000c0f000611080c000e9007550303072101040c1084000c450304000744000c0744256004180c46803000311800702e074031413060a01e2416180c000c80240701c0c544031031405031041c4049000181c108807055014501c0044280329203400390b0b04c54000404e09504000205041c055524114200149840454008281d220490035104225030a011402190100004645101d465a007580921001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 32293000 1250 32291750 32291759
    0x204020405120a0b07090f150c0206030403090302030c01080112030804210302040306050109020a09060e150d0507120513020d0c0302061c20040306050612010507020307030e0d0f121206 81
    0x3083c041140c5105007080b200b5580d454000307039a00e080700e014880c10b8689100081c02441d200e80396040400c5281d0608040f444450b5001804650044408070001440007100b0021410100501c2d141d504090030070080d192706005044200402040c40541003018a20116040c004d61149640301006e40d22a900c40b05061500007902035070051208640740c40c1b41000015190005100380c4003a00321654440c0c90040c9040801ca61480d0241000c6a1110b41038034032461a031240002445158000e1700e02094520b801400505040304102c03071003002504240c1007221803010341d1004411161304459401c0403004031300340302c501820581c100075040f184c00240640c0c04480c1490301144990200c1086c003a10480c0c0c86509110700c0c0303c0c802060300081c184400d000042a580100f0341c4584040e10303034110780f290603508500355003061b290500507030000281c0308249640545401c0f25000f00b0740d109100402d140d62100d54102944401414601d2880c8156a10f144140a00300170921039003010310035107485 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 32294250 1250 32293000 32293003
    0x1b130b040f1d0c1c02010807090f060f03050702060402060322080309030702190305101a030709020c0118020307050d0f0606080c09010909050c06180301050405030307090b04030b0a09020402040512 86
    0x203001620b00710700c180c60b520842840e007488034015241c100c112a6500780074a50054402a0780a407c09040c014000e10104560100e40d41445c010105ea50380d41030010300c541000380844201400803c1150010b00c10840980c41d41000c40741c100721424400c06c6076034803a034880215801d1941004046032000000c0c003035001c0340000a400c40e5802200c1c0d06051380985150311583c1521880020607070340050b00c0d01142c139020b95102260b412a0014140b604801c9480000e040506036001b464660360301207440307410030109200c0d92070106c5102d01d0380b200c0f40705a50002665400d075403140d10701c03130341005014404100303901602a80c99a4000e005104068841140d80d0300d482d454501c0501403040800005035000b5107001c1c17884590b402c80050455020824103000030380c0d2041500903811072600818440c107450912034680306500500c0036540b2030521707100c01031442c0074603444112150782c28401031000c200310655440d000018003000144a2001e440454080d00481e0301142d40640c0d50540c03041103020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 32295500 1250 32294250 32294291
    0x30f0614030105061e040b010e100309110a03020a0b030a150f060318030c03080c040807060302030105030d020c0a0b0306040612050607030f020a0e0f03010204080f0703051b130b040f 80
    0x481c000c0c00340b03980740c1c1e060000712480f80b1007a60013010781d03a4240525007019840500891811314100014840400114250318442250040040c4d40d4100350b10501c006920901d4030300f442260b800c01e42515540000e035544107113004e9071003941000808907110300601e6000c6810120500031070409195140d410204410403482001d001c281406954584680008050451698180c44410f500701c619201100c0d00d08004000c44140103013088085011401001814014a859500582d42e981400203040c18022011041d0f000e40d40700c8299054555204d05101040d5494894616140e948210000c2c01904581c0d11041d496448116554188400400c0007071207203159483c00d1011090500b0904100d1090b00e8500c03001644070195080b6524003400d1201a8450040c0054149511603200c4c41c02d102880c905020590302021041081203000c0c130048003520750b800c0200c0902d02d209008030752a0302507a41180e0f60284d1395200d820569660303a001c003041000b040c100300056081501203a4841d00f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 32296750 1250 32295500 32295539
    0x9010212160e04060303050304110a090e01090309050901030305030103031b020402130501081008070504110c030a0e01090b030c031302012106140d0503090105030403020312070c0605090102031510030f06 89
    0x1c20b014091000ca080500640048a40c10350b591440c650b200d4440c5004205825100c991103500100f0008181c2100c5c000da4400c40d024600000b4284101d15028014080340d6000a024101c070000400100b5004025241140c1d01401c011a042645180c0d45805903020724000b9441840412260303220700c003105844054a1080c2c07100d451741c0d203401401613401001c80c801c500460748400400c0c0160304064000483c0e0024000350030742059504202c10341142c0001410f0310000c0c0c41000795001940e80140703010000c0178a09685071940c1804800c0d520780d0310008286180c42e40031800c818086900c00c1e0521614100d01c100b0410025142000a10161a4901c05d030307200c203544004507461510707000d040f0302a0140d2100080d4600f400001c010b5809400c02001503096010510101048044e4014a14810847c0e035035103d00c09141c0d0700d0003404070394010740104d0041e03105000300b01c025168900381c0e0743c5c2c0c050f0886032014044807a41044018024032010002000c0c14039500003815544e07041820140b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 32298000 1250 32296750 32296757
    0xa110604120e030c0d12020709060b18061306031a030102030f060103050c0a0801030f060b0d140607050c15040215120412020d1b0602070f03020c03070e01050105070b0901021216 78
    0x541480b03040650724011034051542c400c800e98075550001b8442c0c1981040321032a1300584018a0f03950390b41c403044400560100d03a079814001450f146000701402c05050050086510500300710540341000401144c6026020034907980e810952031461410040c11920000140290342d680b40901c0d02020b0311006a84e80b0340802c0c200700100b617000a00e00165010701d12140c3d039002c00d50b0f1860320303000b2220201003016903007155079003500c80164403614040c0b110345e4055824110380350b24072001203190010017000078003000700602c60b07003210820120b101d00201441070910b00054581f800001c0003484451104070340180700040070048000140f140500c910301591a500c01142c60340d80598580803444030a00002c1d405815281d80319102c00303500e02c1e016002e10401410105545ea45103d80c00c0f0014095001d64003112080748185030400001000c3c24004210503001e52504c00007801c0b40c09031450040c0010316040018454032400d50641d080c554407075a0403c0e81c0d0a01900340208403001c5421503001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 32299250 1250 32298000 32298017
    0x10311030601020a06050a150b0307140909150102011508010905070f0605031810020f03010915150f0203070b010609080d030c08060d020303070f060204050a090902030a02060a11060412 81
    0x12584000640c0c1c49080180c0213000c109150384d40d51401840f0040010001e01c0c0c1d6080480c50305a460003450b000350900d100d900b607507802d00030400f51602e0344200030384203c450100043c83c41c40d03d890b5079040d01300100381d02f0411400202401070380901880b0701103034414410100c00040d9001d0540049128034040c03010b5403005511038141156200541c041d420214000304081802c0c00d0366800c01e070307104c00d0800e4280e503810040025540300b0303640283d07118880500048014401c4c5c04072032042886240703100e00e04003045442c003c103049110001c46144003e03c204060006000340c002d104a540503640104180c1c01580c48220181070382d8002e0217030743d40500c200e4482841e240d02904c14500c60350816196a0060340d036203003c1150044030000d0417030701030200780718100015030025011003070386220f0100075031624102003e100f1460705643c40b00c00c225003420880b0000d0384010407007030702003078040d03400baa5184051401035548a9404501d80e0452184034204024041c190420950000040c0da85e40c05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 32300500 1250 32299250 32299271
    0x9010209090928050d0f020a06020d0501051c050705061303020307080102030103060b030304030506190204090c03050105010210140a09020411030405010f0501090e030316090513060e0604180b0603030d18020103 92
    0x2ca580c003200d00401c4ca0b40400011612240944a040f07180c054030b10460b90490350550302c00003a0303006a0300002466403507800500a514114120700031039505400c4000c15913031181c90b0565181034078411540542400907002c0c404141c0c00050b000034580217405c681c910741c0e031140d589000791300905c010f6540d103103031010502403898003008950480c4e8010004115079214440040c4c8104160b5030084001c40d820400090603031030b613000e040d01c3e01c41c0d551000203103503160000180c1010310359040200c0803460188030702c0074800c0e140c002c00d420511000300014241c45078808203000f0b120707030098440ba19002004101c200441504110380c41114000c06001ca66625410041aa1030f440e80240302900300b8000101e41802c0746030030803420000391a0440c5159913841c0807442402559a5490105460314000c0c0445050900c9154110301d007a10108555041c0d051040c950001c003a5004000390103100c0810803a079410000d42d9454801031408010310403034401e104840c180c51410490110313042c0b022091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 32301750 1250 32300500 32300563
    0xb07030503061e0d12031e0b0307080607021b04021204050a0615030b060907090509010f090e0d0206070f020705040f050f060102071a0a09030516031b060215090102090909 75
    0x208000906440407907551680c0d84e41e00c0c40580000340d005c26079181814040c3c000500c00b00145c3c7c00b0203500014200403950285820031000382c000600c182e1106d001c2c04419035001030440c0386000d080d050f030040e0b0b05844000038064400d0841d40c0035015000f5080c001805804200b0108503842210f00300244402608214201012440064622210391002550a05040d8621036015000c0e14060303140946800c00101c5086c002e0300001c281b0700891034140142d02c3c151040c8540d5585810007000441d1a0b00c0c002035a81da0000c1100d0100058460b212484d58020081c0c007015020091091110301c458500d01002854215504a05160514085041c0b54004030740031050714501c45180c0c0703c000400358030045907804030000008000e10b0100020104400340301e03583d07114100318405841c4510314202403404990099a10400001c008803c0014940000308007074049010b9901001c0769403940e102d14024012110159000170a00007040650f40300812641c6a0040411203041415000066031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 32303000 1250 32301750 32301799
    0x307051006061b0302030a0806060c060a06051815060a09090e0115050609150f120405030c2103040b0408040b0703020f010c03060e04020607020a080a0308040201020c010806060a14040b0703050306 86
    0x1501503002001803070040c130701c40d01140b5886040032b032205142292229100746070100c221180301050345c0d40c02062041d46800c0304a0b4541c075042d01c104070040e0a0035000a07102e8416401c605218800002d0b001c0d04040c052280d0200501d05850104013480c03086880c24086c0c40c1c100c41101541d491507001240c0c034a40380c0146c500745d0202030b281ca2490011030b152803100354010080c12600380c0060103901080d6085600242c413991042c400b664942500201903441c25120440c0540c008103400c210a600720800c400781c0e0f074070907003107450441551114140400c0512460700001400000003a4402c18542c0001b4000f1803124450020429080b103d50102c0480305e450144084002918001c00e0251401d200904508c6000804000c01155900d1489240100c110800c60100381001e003080150f43c2c052240104091086c00c010328980f030325100165003445520502d8052044003081191942500c02c00e444c00760a0351008030b0303501c182c50f003000f80641c0c01c110b0b02d641c401c2600ca81149240c0341454400b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 32304250 1250 32303000 32303003
    0x70c05072c090c011116120209060303040308030a050a150b030412030b10030902030705060a1205070c0b04031d03030f04080f01020c0a02011409040f0902030c0316090e0307051006061b 81
    0x1801c0040e030360b43c0044461900d002c80c40700c0301c0d2090b9030190f17005c0b04000700719500803e80d034001c2c20160310b0310b417041c007042c014000c020030710a400500c4100089441d0a04a82e8004007550000407256038510791400240001682450b8800030010081f03902440e8000450182d80240c50060345481910f008405840b02500042c2d08000b0101c1c1c041c0580c2e000360020302c2c1981c401016100501c3d01c0d5004500d180c1c205000c01c400103000200340d00d038000c41e180300b0f050f04840700e8507185900070001c0c1c031900c52b20200500010104a001c60740d00232501c0440c5009408801c00a080da541c1d104010055802a040342c01b07001541c2c002c0d07500c402070502052003180d0b1400c1100000c0c00802d0055001550b200703c9040a000d0f4030740c003c00456070313a5074481c0b0448804810702030b03000500700d9241c0107151505c1045e1140300d0096028811494000c00d40c2d029481c116141c900002c521405a0a201819401101401821442100c0c0529000d030300c6a0000020303181d06556140000d040a4a610b5040034020f60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 32305500 1250 32304250 32304253
    0x60a0504020f0d060207060c050304020109060c080301060503090102070c08160602070312051c090503250308060609010c0b041a070f081f08030d0b0307060311030a05070c05072c09 79
    0x181003106043c0380c000110001e0260000500f421700b11303241c2a040d585400c4c0504001000001004119a08070001c0c01c042c0129160446014507159280c1c1500e20060040c241840400300000745000380035012119040d5014041130b508664814189507203a0b090710f080d04514014410100d042c0c1e00c0003960400f100c1d003240b04004140142d0340143d40ea9444802c905414052040120a003100240991389059204800a50b5165401210800e154000c490110300d08d412a01d6540301181e4403940503900700404481403541c3c1c02d07160005071003880309080020032049400f1b003003000b03008400c041003d244104546200190391028003c503000c0510411000105080c01c010800203028040760803c4141859480d010113a00c4070003440c510b030414062000d207203845820241c554181405030000500703c80c1028007901107190f414104500008110b40900b035a1a40001c40880c818400084040c1c0c00c030003a01c004686889072460f00036109501e01d40042d05900310f806a1a030b100310070b28400e440100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 32306750 1250 32305500 32305519
    0x90906151409040b090109050f070806070318030f12180606120201020a120219061a0603011508060409020d080315060306060423060a0306260604082104080903060a050402 75
    0x26900c1305103071405810400b1a650f034000283c0024030800000d603560300301030000d0907418500124280742c094000d114504050500e80c1480c2c05091680746441c480c2e900d8148200490f8080400700c83d10300710510300c8243c0c1410480074403042c4000c0c0d0900382034580030311000e10400b03460380348801105001c2c140c000d0059010100c500041440401c5d41300d060007092040c0c55642140040300341c0941c000ba403095034029a030301410a800c0104900034600c0e104140e40b50703415503140c0043e0b02e01d01080c5200d107800f8010803400081aa507920350180c1003443d40140001c025030b03001e00f41841d054200300c8100c080e40701c211459010a02d400d83c1540d20900e8005e041e20302e000e09040c2c0c2456001c1e003080078250b1400001d0041d10b03080d034514001e005080e24075a00006e0881c03034815461804808040104214411554400c40061011600c82c0d07200760000d2505a90b440b10b400707034058058034404c0150306042d2010611080010010040020440881c100d484a0b11491041d030704441066500960103403201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 32308000 1250 32306750 32306753
    0x90506030c0301051c0804181508030306040207050c09090c100201060b07020f010c020315060a0501051303060b0111010204090c08060105030906071d03100c09080304030c090203040c09090615140904 87
    0x2846026510084c4140b00c004072106d82c1d5045480c3c01a802080903884800f100001402040c420004583c00c01d03002d0310780040c80c00044079181e06c40540014026074001a040050210800c00b02104160103856140310b031624009094440c080c04400e6446441000c040c20000c034414010354095032845c0c0040e511b40342565003001040206030064038140700200002e003000da6428401c1154540000d881505145001020888009880e811031410f00800788400f400c5072440c0340080055036400301001034180320403001030f41d2a0303c041500030040d600000c0c1c0810710003402e4100d2004035016450f000f074143c444000560f03882c001100d0200340e59000300005680644140100180c00304144084d11601e400e500200741066440500d288403e51200c42c40c02c1c0e540d6002c501c4500070404400038500b4141581d071101000741b124418002400c0d0044081002d2001c6280540c00404049004001403030306468814007810f6841f0b0910508005402c0000e40d20300c03e500388000741c0e280284480401c0c3d0742c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 32309250 1250 32308000 32308009
    0x90b030f01060c030c0b130209060315061207050a061106010b07020f04050a1104090605031b01080106140d0504030e09010501050c0712060f09080d0c0c0215030a091e0201090506030c030105 83
    0xd0b03000380c0c1000003102400f170100e0b400c4c0c000301d4051f80c2041404010800180140515203501410060080d071008000081b40c5042c480225000300c4202c62000603842c40034111454804a5080300c0d03404001f054001401d41d0b0840d2a80704203807200310a440090ba6500c0c400c0780f480c0620000a07402c003901801c0305d501032420358815503000300d901500080a03041548032440f030b9001a0480c0d40c440f9920740d020311542c90b0802200d0685203000c481c644511101c400003c210303041c10302c510400c0c0080c201e21141c50000a1042d101811140380c010441d515003410010901c203410010540a03400000000c19294071075000c42c0c1c03a50b08190000d0614600e0641e010110400034201034408550301d13075050f045494180078000100e03010b00d0300c19440d40c006081c907a0894603100c91800c02c2c0818002110010b072100340c010501825881130960f01c941e103002c4208080c04203404002e1101c40c0d0040003181c44000c506411021500030307a581c0440c02c0e10b80041c0072803484242d4400e607080d802032004000340d280 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 32310500 1250 32309250 32309267
    0x5060405040e16080a03020609213105040b030607090b0a0203040510110706050403020a06050306031e24040c0b0f130305030d0f0903080408090607021e01090b030f0106 74
    0xb1030401c648a07441e0380c1074070b03a442d03015942101e58150460760304082455070420406400c100b49502030b1116200d108220504100307200442c105055021400e045886048000c01039900221103180e180900d007170080c007002c50b041e405040c0c0308074502818080c10341000145903201b0101034491004890402d00b105116411034030600c021480100302c0881c02d034450b1080c03c07084401f1500d40b9202c0c41034400c000d50618045400403030801c0300501c403c00260365912200411a85241441c03a07480c2c48900202e4184085070180f28060001ca00c201c0343e52000010780310102000c40120802c0e40000c0d107140860380302060310003500c0880c000c0010305c6500da60301c000303004c40842103100d240740450404140c0c64100442d4030036201600041200e20141d8264081e50520307141c16481000b8405a943e009001d140014001034035818001c01c0001130f5468034412101c580d9002041030960b14042c0003024203d14500001c90300040341c081c00050000304040549002e5801c50000a001c0d82c206901154101c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 32311750 1250 32310500 32310521
    0xf020112060f0905220c18020405040e0f01060b0918070e0a030308010801150e24130204150c0b070c020102070b0412050f0601060e090405100c08040b010504060506040504 75
    0x2a9114400904601c2d42c60802004052003100440c0e1494058007015286480d00d0880b104407807040c004200054205100710150781c2032040300303645420008000c8000780541d4000c00d4010345001082c1c4184000014900b000e021404024008982c80b5045040280500d144480c0c20200901e01c07007420351500c6501a500211600c2c14003002400c10f4000f43c0c80094036031080d004a1051001030111071740a000d080f45490820340d000c455545003003a1441c2c4048020840c0c182d00c10451818185c0da4403101b020b000c02c81c4000c0c4440b503441100a00b0780000d40c03003481351641c0c0d600c004039822403203805008440c400d40d41040d000344860b0b0301d820781030390049a0200228118020306002140745d0400e8001307040039008010404d0312180e400e2400c3c0780381c050401d000c5c1c00303140c1c0b060004102e0700e54000725804000e001034440c040a42c8170741c47d00d00d00c0d050303010380400e01160422450082540d4803032000b034421402900e200304141d9803841403100b210790034081e141e00540204810b0009040c603030046001e00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 32313000 1250 32311750 32311787
    0x90b130b04021e0a030b0102030f040603180203100b03060a0e1e0a02101116180b030102120c03040201080112020d06180f0809040f05010b04060c0206070c0905061008040f0201 77
    0xe050038a910400b41c050658010844400b04600074800d625100b00c00e46c040080c0002d5203003400e450a00c81c041d0245100c0c54081584807c000041d200a850b19429016400780480c0c0e4841e00c0100004081e0000010032030003480b0f00350014425001c68010400842001e5005c0c00800080312101c14945041d0700000a40b44150850700c00181c440c441c903c00c0f440590351b500c8850040300d80c0b01d241400e042d07095070480990600001d01c102000081c40109419441400282242c2d2800c00310340603009142503000307024608000c00c02c0541000740110320444c800d0782c07203e00303981c0c030b4800e07600c078000e90b0013130194002c84d200080c00c001503c01e40c09014103e60000c01c4080d140d01c0c07591626880f8800c5030b0f0031a0071080109035128182010300618008c1c030503d80043c0219030600010320a68090f40c440c4004025034140d500065440380011501c6954120801e400c98580b100c021801030201a1000c0340543c9444415000350f61084e0181d030701031a40070b265110059401d400441d20391940b4603045501c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 32314250 1250 32313000 32313007
    0xd02010b1e01051b0c0108010b07021e03070302130f060605040b0f03070e03030705010906110903120703030e0601060e01090501110d0c0804050301020705060402030d020607230f160c090b130b0402 86
    0xc40c6a0811340b01c2e4440c56420040148918a000040440f10103a02418049505100c1400141d60701d400b02550520101e03004541c511034200060724120306a403010b90403144044441400c44030300d801044816804040500002c3d0760b445003114140303c0c0340711340d0074100002e1005014071003003c0002d540065403803520b002c14032004000642990720100d0202c9140c0c0d0340d00c480100b085514020055a0b007101c040103410404c8003404a500d41c542c00d968190707514400103508007050300991040c404441e170030080700c08a40c3c40d110080c0c03a54854600300c1d804240b141000050320f41c41481081d0900341003101410001395410303003c1e40d281002c04011a800c0c0414000818691403d02c054005280207000409e03190034140141410300148603018000c40d0054030400c009203410000e14602c10101079050500c404820407291024041d1806e0303418501000100c844c5581d00100070503199a00130161002400e0f602c0c18040219040100101d801054050210b01e042e43c941d8050b414034a0058009403a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 32315500 1250 32314250 32314267
    0x20303160c02130e06070e0d080d0e01020423030105040804091a0301050c070309080c0f1e0319050f0105071d030c04020304060203190504020904080901170c03090d02010b1e0105 78
    0x25000300ca02c2e450311a03071300c00300030741065000c0120f640c1103001420a075614500705400301d442e03003448040c09820038200045004403c0e015601c45642052014000c5481766210400401e0707040e070807134900c0d05442e1070741d201c80035529061184d54022a4440e00f16480c0500c0d20000c5000b9042c4088205071041c0000b540c80c4864400b0300420f4071510301e06807616996480c0746030140a440ca103412881c0030354004a84882c20f6100d0b2185c004a258040710302c04494160a0b0000781c040340121040c0740c142c020524441100d50340035000c1c0b50080e101d101a540300b81c2c440e1070414205d0b10102c4150b0001103204102c13200c1031116800c455801c1d18040c0c2a16690841c02011400383d90007134504449240c1c2c008100f0000840001e610300c4040d01041e03042c0401d04054000500301e02010f00090f10943c000944044c550380100403951002d032017220b084603685010300342040c0603001107031016840d0152001140d5024418400c1202c000c5005000602c0c4550824505603007400c40b0600c141030010400c071084 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 32316750 1250 32315500 32315509
    0x80312061c020d080c0f070308040306180501090c060f020d02060117030c010501080d0f02070807030204050a020405131b0306050303031602210403030e090c03040f080405060d0207020312030403020303160c02 91
    0x2c0c0001d000b00d8401e0740e1078617460803951034060310140012542c0c000710f07014800a80c030102103400b03d036001384010491400071807030102c001c0e10ba10710041c615840c00411004204040701601d08840942c0c45002020541000c26078a0301c4c42c0302e080d000160003000050002980d603c2c140450f2140c80c2c800c503400c005429900608660081c0c200e60342d551310444e161070560750300c4491505c0056941c400b42c6055403401d44080c0d030341c5400e4040288140c2c0c036040007852a102c20f030f0586008120044c5083c20040c1c914100000503c5a082480c10740700c4124260480940030703001c0d43341110000b9008514690350fa045030302d034900b62103800c402103000309005a1800e1001030040904aa000c3c41010756a91951401919044035504001c1c006e5411208200400b00d1050035664003540121840d00604601d2410351107a00c6180c10556100d0004501c0384520110b6a0180003220310036400c90300d0032002c0c4c40d0040c1080c002210010b0041e4402c00000d003001c10b1130340340c94490f40118148514a03d40315030019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 32318000 1250 32316750 32316769
    0x60e01060603051801140a0b06190e0906040b0307060c060605040c0906031a0607030507020406031e0b090606061902010b0d08070308060f13091a0f040507080312061c02 74
    0x1400039032200180000041c03c41d8002d061410a403001b04144480e4038100c0803204001086100025500c480483c01500c03208101c9070a028166050000f070464000050b00e04201981d40340d006001c43e0000561034180340c81000242c06004008060359481e10200711034001c030b54242192441e4070381e9000140e80c0c8071713409110000101600d0b110560781c101000101103500419214071009019404c0050079160a0104d4003043e805181c0380f84c0d0381c816400400c01400040d400100b4950400030010181182028801c007020712441c4a02c006490b460081591141c0541d40117074819020880b00c1d100c1d0800000310002213100380004580c5241e4180083c8030a03011f00c02c150703900b007000101101016440341c2c409038400c1c000c031550810000584041940d1441c42440900c000365501004001c3c00100600c0040742c1c4650903080c1c41c40c1c0b819500c00021501d080ea01203515109001c6e000c00c6000002c002c0d40c2c421400382e081c5280036a2211b0030040034001017184400c11801e4903511901688441504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 32319250 1250 32318000 32318009
    0x3030406030608100504021c03020a0c0801021e0c06070804140601090903030c020d02070519090f090201030b010804080f0304030c050604031d0f21010b0a15030606050909070c060e0106 81
    0x90303010b1400540900b0445504d80800005161004000042c0d88070004c4070089513051500a242c0265031400781d01d004440580500303216034001000541202c150002d2401e200070218801d03040741200324103c098028908081c0042d00503400181446218401d15a8014000c00a042d00c0c0034070b9008541c1010801e800c2019080d032184c0d84002815010b0041c00b40d00c2d021440144a1610f418100a480d0442070040501c9000460500d14544848201c0300d000361614180400858000030080c100501d02007034100d02190800310075064641c040c1324030612840e00261030700d10b03100e001d84101840342c0c0001c0088003403200d0040c0310300105404111451040f8400c3d140c1c1c051561401d540c107211204a100d4251080f40b41043c9401941c45550002c1946800d4400c815441942801628090800e000a860700404240300c00990202c84208007000b03079120352003c11205da1111030454861007a1070045402001d410080b484182c420212101100d0240c1400911580b25504047c01c0d2a5140d21 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 32320500 1250 32319250 32319257
    0xa15020f16110a050d020f090901150e01091103010608041203061a120109020301080309040911090f070305060102010501060c0b090705120a030201050c1911030d020703030516030902010e0f0a0503030406 89
    0x40d03182d014248141c401010348011a622142813505074001500d10b1f006121003801a984a0041004600250810901201040703914450a5180c0c0d60044480c4000d120b12210b440c24800700c3c00210444a0449041e1400b0380d492016036903a5807039201d40503c1e404108000c15a4410740004d07805d41e087da1000028600e01003455880c107800070454800d01068100207981c52040004000445d0004100e40824005840100e2004814140002c558030b052150540041070740040042c1000703e9011a0702c0780c03841e520f0411494507810012801c0303440034061100410080c03841800410820104141c0c40341040e81250981038540010501d03802011042031102c2c0d1180010030b00f003540a006075903004d860350b0407550421031081510303181070b0710030b105413002e00403030040041d21030506100b282c041c01c00c0c3c00010f540d1f0b80082c0c680100140001c4072620607207100807040c5024544280910000680c05030364010170003038410308000b800d00b01c242c07555610030f01d040000103080d02c0500140004003003945 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 32321750 1250 32320500 32320523
    0x6020a03050a020a0c140f0415050d0809060301080f0709051006080a0b0d05070f0801020f0412080c0a0818030309090708060a0f0e0f010e041505040f02180105120a15020f16 76
    0x1014000114015540984103278100b2081030b80b07106030020414121081120350100b650164141702c4ca1600c43c10006503000080000081000c0c000012030413042c04034441118540780c0c0d2841ca504c201d4009175200c542eaa032440004000f86840345031080d801464810002480b004e148001130001301044400f242c1a03049048208804c2c1c80221030480100300d0100294903011185e80303000d100d4400c0e070140c5030000d601c5040340030902903041d00307660919500707070222a440d0b03405081c06006504021000000b0240c42c8140d00110308010040da100741c3c102510720010703503c9203602925084402404a41c02c03c0406800040024a0060300300043c94440c2240802e030910341114400808141c00c400b070344000e00030038400094a408440d14624080d6403000980d500c81b4600325400300c03900480650301c010040d100c1c082002c44440024101c82c4101c507101c0c42c0050340090107807540341500e400380c4104442d5a00a54804c2c290f00107000c582c074098070280c0380041004824030201513045043d40c5110580 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 32323000 1250 32321750 32321789
    0xe100c1b0e0405250501020a06091b03031d041a01030509010b0d14010606110a08090102010f0204080d03060806090a0f0212010e0d030e0a0c090c110613020f060406020a03050a020a0c 80
    0x44009a040131202c401d01101824070380041c0d6079032144d0307600421240d1380d44000410300040d506181c03030076041c106610070415581c1c10b000744250f0314500d490740b0784a1003440c0f110107441d00e48900007a6200c0840940ca403038240c4401035009180060903010555201d107949689540c3c7d0b01c0b003808140c2e00c501141c0841210005c01c03503084030307000d410100500618802c011050000010f410706c15540c403003011590f070f100c80d500403030162512400c03050340c40e0300201c0d000ca0050404260b0484001a0360780030441c0c580c0e200c400c0c943e22182510500d1960300b1086401c030200754a5400707802c4150000d00303503c440000000721582141c44040c047c4126820083d00c040c01203616004007548921210014401264140c45a2403100390900c926200140c4c0c40c40d1200406000da034030340a61080920503113405150034150900706400d4200102c1c456420740f060000309243c2041a070f4181e904a50040034640340c0e594084e01e081d40a00504000d512511030348100192012604e0360142012451005884642 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 32324250 1250 32323000 32323033
    0x17041d0105030109030905090702070b070303020403032c0d050111031003021e010f0302090120070602250317120405070314030304050c0103051e0901050402010e100c1b0e0405 77
    0x1a0071140c400c1e4109000780000c258840c0112054a4044035100ba0710345480307900740e10b1b19038103500441400802156107414150907034081d1007100d00a407900e0010600c1794509414100715503151861507468006810318034140003c845006d54800c1c000001c40b5040d40482d0115a082207079544801c411800c0207104504100c0d84441450900c080103005503040240042c154822690101d010580c1c04184400c6c4d0381c0c40340000940500898410040310520750003101c0d1141300030700074030002d44507105402d1a101149945400f09624a0a0144c240c80c11070780c503aa0000c0da401c0c0c2e105002d000600520410040c49043c1c02c4c0144d00c105c0041c560540345190012850451110350f0840781c0050040002003480402c80380e184600c24a0700050316503940030104002c40d40519440f8410511004001c2d041105500c0680124001d03282c403628440309030100048c0030111844000010490700703910000030710310f000d070a868594061801e0fa100380c449004060741c1c0002c4400741c0305a0311086078012611036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 32325500 1250 32324250 32324309
    0x30f022802190b310303050c0a020c04020903010207170a08070f0f0f0504150302090f0d020607110a0e0c1206030105060d08030a02040e09070303030606080403080f041704 75
    0x5090000c0e00301e0103401035408400300310380030024000820040c002101403802070441d2001050a20394015500c203c0740000e5481354501d807080307010074503080119925428007026900070b005182c0c01000f032107040301c051002940207040c1d03450301590280102c82c005500a01880304210505a616880e071086210040c40380e4005006c070b0040c07104000d24041400d5100340060700c0110541820282041940c1c0216541d1046134800280c104030300888080d82c640c59002444810001c13a0101102c0c041c000801803a110644002580464204000c1c03001501608040c28808001011541a00e60700d0b495001c1001040f100107201c240d0020b060014030709120301c4160061815002040589405000300c0c0318441078003005400b45001100141084905070102c1c0e000c1c180002c0850702504294100302c0d503510303007400b08501180c28144003240703c1340303e000d45074802c58041e40c810072035880340c8001c0c080e50180500256402d02d403610f07402c40000d00c598003c000921140d003080700a02d80b10b0105801040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 32326750 1250 32325500 32325577
    0xc11101d040b010816111006060e09010b040e0a091a010509070905060f07050a021201060f090504110d0f0203010504240204050306040602030c0c0d0818030a0207060f030f02 76
    0x5140c2421442c0b140da0055440d50b00c0454882c40c611001850b941c10b582040c0c200703030320051500c41c041e01c181d152034040d08039008881c1c1645031264040640300820003660007d0160011061040c0000c000507000000c420ba040200c100000602841940703440020b0300401841614140c244c000410003400c1201510b0b50100c2c1a141c04260942030100003112031180340f004c1c3c0b900d401e000c42c040c0180101880080c0c0000c1e4010302e1780f0040c4d010300a49038082c09281c0b25229403191001740c00101c942081c00303064811030b80161019900702c00c050400c0109075200805039240210031181c0d4006842c2480795a01945c028020354541500702c804442d40508a42c50001c243c2e80140400c0220341c400156840c3c0080c0c0c080009a103942d9040c854140ca030003a1907848a8a103d0840444411500485d549001e42c8221100302103185009142666030712400410000592101804100701c900c90b00c4003420b4002e0318600810800000007024080e038000c0504d0080000c1c85440741000c407400d40c6101143e89 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 32328000 1250 32326750 32326759
    0xb0903070210030507090915030b0105010c080a08151002011b021603150207050601030303060503281b0f060905040b010215011a0405040507030903020105090f07060c11101d 76
    0x11000e50301146a28400c04060002d0584032030100e6030f01400750041c2e03405055469010030050410758458942d44c0c9041c40240c41e036481d4940049641e51088100c5401103420032840c5140126a417421107920704001d1070711513034003a08400000c1d070350388005a240f6a0030f4154000319090090541020042850401c003006650000b0580b10b090000851110704503500110002e0310341c4c1c250f0326950080d202d90300004045004441c004001c26800d0303071020041d213105504480c11200f00001580103280c00700c2d41620500c0142c11503000040d0000c03019040d0106c02c20220b80b40310340d01d5000030084840c9410403408501c00c0303003090019003868490400c01e45000d200070402e40d5114140190b02c04c60600445080e500011586500b41c3c1c0c030031044070020100a0010071640c038052000400924551104070019420500410100c0c2ea00180480714114280060308480b03281c61004d03290640040030440c0c0d03a600c3c004801685d90361300c0070320b03851603d000d84908510101040500c42c842443c0c00449102c2d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 32329250 1250 32328000 32328007
    0x403090e01080d11010f06030807051002040302220f06090b0f060f0a0f0507080d020a12050c04050f03010605030607020319030203150f010c0c030602090a060305010803070816080301060801030b0903 87
    0x481d40300040321200740d42c0e41d044c405403000301c2c0e0b0001c1c0d0140c1004510604c02d1410000001308200c0600700801000f401001070711911200c08410005078891841702a501501503a030006c041d810b101410f00c400e000030500040c0c03003200b12885405071000b0f90f015845843d031f03c898051550400001003024004d040764607619014041044a80e80e000710392403031080080090403426020302520407189810f8002d00000e80f15034101c1c0e80e0102950198090341e0000f07000311801c2444143e42e02619006105800065060030705007400c3c03103280700c503989441d94159203070400094103032018441203025040716401b0710390366021281090380301c0d64103954083c1018410810402921940e000c00221580d08990322019000000b004860001a015024051000440e40041040301650003895481c005452010150341c3e19141581203410074862102550010000c0070000b40c0131100909a01203003003450b44c4a403046446001160304240c110b04080740c4100014800c4c0003a06141d00e13440501440194074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 32330500 1250 32329250 32329259
    0x30a0209090619020c150c0409060308040501030605030c010207050603060402070c080d02150403080610140d0e250e0612030a05130e04020102032b0e100b030303100e0604020f03040302060403090e01 87
    0x65402c002d80a111b43e00f10b1440200b201000c00c51308030340007003c1d46034003408280c0cac50317017051000c552051007010302003850700000090070b080114003e0445070b816000740c580c0628040a00c0095070000b0161584103508105030400207101d03ca00d07001915484004040300d405c02640607141070130905462201080717203c10080081e80c41400f040d4003c00c241c8541250410000c0d0590f0103480c0d21454101c0c0c8030f0b010075100e601013407541c84042c106a107101110402c81107025010744a000b11407080400400855040c0a00c00780768080c940c20482c082d005418500b80c10a0700d50454100c80c010500103840061061400421000b44c43c01030081000004514281070b80042d5a07072061003d000000e0010f10039010200340032142c0c8114855800006000c8040311201f032586030756109405003061494941d13140c01c181400410b480c4600c1500040629a60404822820950004054650103178080010300545841000618007031403203a00205150b0405250103400d282c0307030303030009101802c00800410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 32331750 1250 32330500 32330503
    0x111203030a020c0a0b0a050712020a051204020a0305030406180f180b01091710110a080712090c030c0311100e040b0a03050703050601061806050703030b030a0209090619020c 76
    0xa0308401e0146006960f401c2040480c3e04280d030b2184040c1421003400100541c07000b0301d401962255034150340d1016050304a06c1080200d01400303400d078001440a00c405003103c00c48081c00da4225000408070011190b0301c2e42c4652071544241c02100014220051411096028a82000c081e000341d07001d00c2815410320800000307100344a44402e1007142c540901080a9000e41e98607400381010f40000080107034000101a44c4000000407110510705e0081c6c000d01801c614015a403098006a8946105885c1d000307044850707071503061000351901e41e151000b030001140962004c008500c10102d503401c039403550601d01600c902145005004664000520400c0b40e07202102c09041c1504540026260004c0008505081c910307403c028560300c02c0310b1011060040002c0c1607412140315a81d01c0c045000d40d03552502000314148034240c0414000c0c05050b0010b8000d03000001042009003c550740c0268035000920210000e41d2108000c0e00004103200760160b100759a00340d44419480d00707514080c0181840b6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 32333000 1250 32331750 32331757
    0x171e03030a02030703090b01090209030d0503010302100804080f16030e040504020d150603020604120b060d0546030f0203040e0109090f0f060204091409030a1d03030a0507111203 78
    0x30007486600000260080e40a40c0c404140c50340c00c11241416503844080142c0250300000d801d81c400e105500b02c500c0c6c164401c03003c1701e059a9014100000c14044c06105849030503002d04100e0318440140300004607001c0a402405002c014400300c4200b41d40d45003005404d08800c0800301340a103051604002c05a150103a13203602da42e0b8040000c2040c00700e211036040050031079400081d8480000a000240c80804070120b1230801d0003410044159103c60b020804600b2218100a1075500421540c03c80181180032a91415098080058038030300032020780120b01c0702c009541d0b4200d40c0d07024410002e0560224042190402c01e0006514040c281406007045040500c540004c1c240c070380e10710300208081d1074480040283d114141e840501c00500e0440041d4002c0d000b024202d030f00d008030b00031841009a80300b501400b04007010714034040058801300c448900060a008450543d00141110b9480810040084900c281c0d41c503505c03450a4508050240440c0701914400e14030020787d078001200c0032044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 32334250 1250 32333000 32333011
    0x3120606051813060305100e06010f06050904020d050106180b0a051806070501020a0c1511030406020d110c070305010501120812070306050409111002010c0e0f0a080106171e0303 78
    0x800303a84203101d4000f030a401241441d503031441e0b00b044400010014000382050b01c45c904020148840c030320741251303955034560902c1010907070108044104007950184009111446010303201516061020004400b902d00a9002c00009643c41c4001d5908a00404413580a0900c4001540ca403042e8004018417500842083c090130003c0c60351550125644c1134100c032203159001c4025922882202c80c0a42002003441083d500712400c0d044040443d50700d403040340107500811101600303541f680d44858000390001d01000c0b150781d40c1d80b424845804120005030428100c100b00800302d840c15490000c0c252001a4072462115240c1e03404900007800c07480580f640c0d00c4150405500c0e507134a41804a003c0c00c81d56000c1c6d07800a203060811000e0101a01400c0d108101c1520b82c4441100700550890817181440080300c002401c91240405610f801d40c0340040220700209481e800310b0300c49044508440850b44401e07540c00d4100b14980f29898148002c1001c103a81070b070244038650404140c42d4030392200808 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 32335500 1250 32334250 32334277
    0x40506010614071502040302031203090307060b0303120114040c0c0b01030b041505070c0308060306040c0e0613020c01020903010c02030310030b071b030f020c040204050a05040b0301021908040312060605 89
    0x20401c09110b015400e4580b01c41e00020110092095141600000d41c00390100ba0300030700030040c054070940d030490100c90240e04180011480c0180c19291440203000c203592056060004011691860013125074590180c001c45181004100a500c1080121911107135041d00380101d001c0004040390201c12950f04680d0001c034618100e9441c3c0c81e02410404414190240152414040c05420303540020707001101c134803d0f2500b282580761202099695042218002c09200d90340c0e805000c4507041000c2190042d4000d4000b0800500c03100b800001c0c3e802004144c03500c1d070b601050120b00340c90709006018074455140099450b600708202c07001d0400340703180406028991008046406503120315000c103540c818600303d64910412518004002d018102da034000103118002280d070091030584203e0b0120362004205000443c42d10b814400030307101c080c7c821641550300b801350408081c6160440f4a002e110b1b941d4040c42d51404d0b15000d08030780e00716040c03800e04503d041014003d8613005000c403004080d8458 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 32336750 1250 32335500 32335517
    0xa1e030b04050f06010305030304150e030730050903120403020907030903020a0c03050d030b030c010f1d06070b0a0509060609040201030921090e060409050a021302041208030f0604050405060106 85
    0x3046480e00c400051100c01c6840344c1d030000802d2050101c0694040d43c8213030800c50080c41448480780941e002d2035014002c0b908108522000030b00c4a900d184011507081000301d01c485031104100390000070400da1400850000102c41c8514038092001d4102000998071540c2050304603000b20f80000030041550003490f94501400b01414000c000714640642c0c0191003040a80e02d9103005603d0b60325443d1244c01080c180040da802c2c41c81e01041c3c90440c1c10781079407a55445c250345402151500b090109031410381003981121400e40d21468000c00c0124000c2503d50504c2c28248002c00803980010b0400000d0740205050140315543c01d88141d402580900c1c002c41c041c2c20908048462038440051071500300c0925000e6885640c11000f03480440c2c2c452925503036242d5886050006131216500c00814540080070000018a0201e0880700041c030112001400c0c9502c1e02070403015123080c950b05540d005004410013107a1080e00485030390092083ea000e11041c01c1039601c3e030307540d010306000780d9041c4903600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 32338000 1250 32336750 32336753
    0x20607080405030307060209030d030c02030a030908041a09030f150a020c0c090a050702010e0c0607060519020a0201062309070302090112020d05010510050c1005040f02031005060a1e030b04 83
    0x2031003901c0140c840141540e41c2c45549240640003584000030050081c0101804142000c1c000c0c403581d01a0021138019600c0d2041e4001d0860040914101c00c80d007000c0b003404081030400d54100c0900c1c0d210b0340b0840503680c0d01101401c0520781081c2403110301c01580281054140680e0124030325411400d4900007503126100012001d060200c41200d4a41080240d01008a41242900b0442c001c5200b50001c00c42e1a90350701d0075a44a160800c89140c20030020018100044c0865004680c04641c1d16190401d5400c8004000180d1b0b0203d00c145006070346400d4180002002c0090109034891244030381c42c154007802000c00c890510007003014081c0350340813440d16030f580d004410080c002401000c04640d2040c400d000c407402040300703028107130013416050717015200e071402107040b108400d6042c0000c0c61001c03010044c00c805400000d0003124030108050044005880411205d82c043d540780350003040138a0440d040c028080c486510a20909a0980d106075116030180c5540054980104400c45a40d50b01e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 32339250 1250 32338000 32338013
    0x60807320118050d0b0117030c0a080306040603020306070216060e0112050402030304051c06061401050d090302070510120c050421170a081e1509041b0b09030c100903020607 76
    0x958005908092008694810090220201c0e0f05035056a211000d001c901c0601041e500c1c044e0349c054a0913079000d000d0b4100030504d0f160166038480801040030800c162203034003281c240802174900d1000340e03210101c54102600e50b03030070300300280c51107143c081030038003481d00028044d0640d40f0501030f0f4155501b002c28155202402101c000d800094101d80039075540c0d41c403000c0c1c0c01905807010ba440c40e00d0030340d000c500c052030101c1607100204140d4405041c0460803102d4801041440d4046055114a01000803e80c072602d00180c044000c94940c0100040c55540344800d0b03882c030307050390030400404003c103010301c0064030089064032054601c0c2071101c0105207070034421014040380d2040c032458042340b48210998092201d6200d507a0350381900721280c8a140410580610a0310b010781c801001d0311203140c9504081b407090754400e0098401403001c680704030140a845050350008403102100103006406801c00b044034a83c441c0050307070740d447c0d240c48000c001428104030b408002d10036038001a204092126 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 32340500 1250 32339250 32339297
    0x5090705031e060108010603080423030604060c03050603070f0b0a0e0333010b030703020d1508071401020f060a021c05011d01080102030405060c0a0507060608073201 73
    0x1000750440750212032a602d41c10040c60014040701d4140b00d076000201300000306029000859512420050410b070a00c2d80b0300560840020001c0c07180d4440122600c107564042202d80d0040d03015103070008401680440c020b007507440c001c00032402540300c888108806449900780f50210741481e2505a1640001902280e411440d441d61903131511500740c2441c0600182110007020309115260302c41940501c3c0c0321130314241c0091044800c1004240005000075019400070400400b25040000d50158622003034800d504d013a401030780070b5a010420a0013900042014034112900c240010309180000c002d00300e5550000070030a400351a00846c0b540319504804540604001c80441d0502c40d81d0b84800701c10010b10101c0086940207090368000083c1140103100712400740790481c0c0900f2032039a812402500716401002480c04021040010350046052485800040c0103124041e1038441d00d043c418003012140000040b603400d007202d101c099600c2207424040002c010a0a0128201c5150100d6112021 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 32341750 1250 32340500 32340509
    0x25020c0303030405070e1f05060a0e061b0601050418021504030b070201020d0c0c050a0201030506060d09050601140a060906080603030418020304050d021209040209122a010311040306050907 83
    0x44040207000410130045403100580c1c0b25003100d00350a64628080e82070b200a0029103008400c0403800500290502d0801801c00d40c10703c0c10320006104e880008504560f01c6042c0c841d41d0501143e4047c2030356a81845994014507044805000e00c946031500588068800c00001780b043c6500310a84a0f42c0080f8425140150303003118a041d0140303080c2102034044c1d0700c0020203c8450789001640c502c414040c0118040d225001001407244d03051643c01580145030103070201d5813005d0b050200b080201800d010b8404c201e0f200f0380140140703504d801c4c07040f0010038082d000c8502c0b8a052031002d110003a408960314044a01902e800e503120b488440109003903101715003100c10441710412480f031035075200380c004502403880345046403801d1014075012615039100c40103058440000301700700500c0e0304c0c0c141c002c0c182a800c01401c14464520802502e0b190000e0203495032440c000f1018444298a08a001100030410030b00f410300c01c0c400d00c01c2d0641e2403031084d0301005001558a0700490402c910070031049002e003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 32343000 1250 32341750 32341753
    0x50a050d0203010908130806010515030a0b03011e021305040e0a0807060b030109030c12030509030318011d070e0f0709170a060c0908010c0e030d0c03050c03070308150925020c03 78
    0x86c1c240f906d0f5020702e1038403405100542e21622000040c00d0030041a94480c032103100b0041411910f82c2c2c140407000d84200070300154190340720803801c0324030f00c000c0c45103038070144502900607a12224503280e110711071240c3d07016030300c03a5141030140b03401d01070040b035074991403a84000c95a43d1030000703261150081140c00200340d010743c680503054080540050391010502e00500d1107400c0d04224040817010350703034101c0394031503241c00600118161403d803400c29044c03d00c00b00000310741c6140c0321040e0520550307821400300ba40e034041501000800040c0342c0b056000601c03071045a01500d0400c0c0c0180c1500744034891411032041801c04180040300c203121902403180d03c41c20500039020501002029280680100d080079403a0030050244607015014000080c0b03c003401500301009083c0052320710b080701410990030721408100554248000340300814049101c0e031540007050030808a00d041c031000d19a1071034003c00100043c410000101300b90014031001211500c4007408403030004a0914030400c100d60707010b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 32344250 1250 32343000 32343007
    0xd020f030103060f0513140a02030a08090405010f0e01060c150e010b010f020c03060402190312050d060e01062709020f0c0d03061203050a02031312021801050a050d0203010908 77
    0x102011800a40c12680540024414400d100480d04d00b00d0b6000d480304a8140344404c1e8100004190080c007a4102c880c09003650108049600464244500c2030411030b0100c0b40094100610318041c42083d02401800034a0034007941880d0101ca031211040c05040144009a00008100411070519071003c1040e0541440005450a0858042d05841540b00e000c07820290360702180d10b100051815440e440100140925191078003030000076030400d0920480f40c2036000303010011442103410180000810303910142d03074070f140c00c1c280b0040320002c0d0000034562100034010805164803140c205054000e1080f0f800780241d040018610b2500940d120480f40d5001140380605131030007101070503103045c0386010f48400c00c0350070104408803501c500805403043e030a84c0b000004079104201070444403605004903450001e0f0340c94503401c40000c60307110642d1043d072140c1c40b074210300b4881f101c44000d16150080700219414040040c05807686409418000c02e0b1810441081d950250001812150058805a134 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 32345500 1250 32344250 32344267
    0x30c090b04060906060807021b030d0503180106030c030512030c0a050a0903020a08030a030f15060804080c120306010216150318020a03060608120703080c0d09140d0e0405040804030f03050d02 84
    0x601b0b18125061030250203884c0300c00407920304181341c240c2840f20060240c40010040201661320f42c0005d0424401000b00b0449448000c070240708040c081e500501021154515514115140800118120403028014824011100700e03ea0170345202c4449030800c292244c1c040c1004448805481e440a9401070408000103801d19002c40180101001980d090140e404501710040c02d94003003a2092018070289401005524030941c0d4071a0800d224100103840c1565444105107061111000998403560010138481c2c15a01000700d02005d014000750440c1891034180d8504000202c840d1a10515440c1d04048001100f16103614280d164010000b036a16522424000c008019a0240300c0c89481001c100d503141740c0c07465040e00d04141c0e043d03031915a40e90300c12050480c00e8200d1500d03070503815107e604140000d0550904008c10f00d810320b00602e0030f403401e40001080a081241c11a000c1d44ca03020600c808500d03613400700d8064a2704801c0c10050311003580f400301c40c00c7c0b1681030703612801480440d1040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 32346750 1250 32345500 32345507
    0x31c020a09050301020408030a0302090d0813060f030b01020c010f2006040201030e0a0b0408160204020705011406100c12090b03011202040b010516060911060706020403021504030c090b0406090606 86
    0x4000c551540d40d0940c1c15140c4080c18200d2040b40500c98290b4418801c050b1418402d800a040040000d8107409403131405560b07500c4207030170425024440c8181d03894103001880d44084002e0071030b0100d1400b40f00c081600c1001035140d50007400c0c410704000140010100175800b8004013030700c508100300c040c0341c5421000080e54449105071008c90000b404d00514141c104000903001c08240d810003402c0800c0d407501d9446250551101070388102d0034654501040159840d0710103008018040c40c00481e114078288289985d150006240c18032446400e41da034410f05600070440050150302c6142e80e8017800910b18103642e0052a80d00407001240e0010021420032111076018150f20710940e0280f00880510b4010340c3c80d0302480350440d580c0c0d11086c4608001c150366400c01240c40b80514050718044603000040703031841d03015003401da505980024042045013400d103c18440c402c8407105041c102415aa50302c4007040c07140c071440e10055103030700d034102035517071903510003801052601d00030031180d82d4801c8040d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 32348000 1250 32346750 32346757
    0x30e150906060a0b030703021309020a05070b0609090d1b020d031701061719060305060a0b0f030a0f0210031401030b090c04051009020a0210060305070f171e031c02 72
    0x422241c001c050100346503042404104054642d00040141075aa911a00302c000390042482000640e1030341100040c8001c08c0c2c4001c120034081551155034500b40b038200702e809118098030040c0106550b50810501c0350300420071040a00c3d070b03403501c104c030480c000c504400c000b11481d8010750700800b444840d4040640065450075031300091110106160b9840c0c00c261100d2200c8100d00300354403460750004030000e11030600040800000c5a0009219440345c50340d80c40c0c10320032100c0109056031440c11200518004000300c004100480003021190035960302c0101c030302607041c8000c1c00b45090347c84c0c25040e1130198100300c3c641002850400225070b5242449a10900c003a20a01c50704d00030240c11102504080c01b806108035691803913500c031945071200c07910017503021689140845c050302d5101400e0200b503005050042d4000c0009201d1141020400c031401d0645501007071020800d107028500c0e0b1080800c2c81880c010f40000e03824420150b140e02d080c20352150910307051041000166000c51100240d016 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 32349250 1250 32348000 32348011
    0x40906051201020a021b060d0e0303180a120302030c19030b010905030105040309030b1504020c0304030b01060815060315030a03020703110d0203211c020706050705090f10030e15 78
    0x24000748000088240b402c0f446844d90f507030700580003120300003d0300380030741d0040c0f1010078080c0965240801e580060402c8860b29500c460383e5801c000207002c1101142003440b8150300c03803080504102c62643d5250490020f18240c400306040d0007100103803410075024190382c0c8081c03201843c3c51788500509802401811880e0035103012890740c42d000704403400d0500c01c0303501c5079a06444180d40203007035031180200101c00502c4c004070b80c6500c62091205e501ea40c0040c042c0e655903000210303203460a500d0000390340c0310140c00c0b040410524004104951040303414500c51300105803100c0b0781d05d4407010450500641301d004a250948030b0748050a04065001400c01c048902504005082c850000200900ca0352400c0019605038010001d03c00c0c07911a0300846181f07100c081403414074001d9038412a1181ca00d191300c4c030031300055000c103454043c001c090107050727488281382c0b82441c03070a034145001a1803030901c80b00e010700800202116001d8076001e58000c0d00140c10030800c450309007900e00d29182a6075800c550 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 32350500 1250 32349250 32349259
    0xc0909010b091008040507090e030d0501060e06041502010f060b0c010e07050f090a18080309010501050301020301051008040c0302060d0b0f030c0102030301171f0507021c050406030f1104090605 85
    0x1681c4803800003039031003010009040f00d0740002c0300f074400c0b00c000001810645650180c1580003c0300c541504c20020040510005191030b41541101d000c120f5a0503400032050080d40d11004c06070341c2e104422181a107500200c1e00c080079186200403401030500225026a548ca0b000011605a040601400c01d42603000000d010b130260a480306500d070051403040907000341c0d01e403c40c01224903002901da03030300540d901d20004112000d1200c41c40304030900041599040030000900c4541da40a01919001d0003080d80250314551503c40031a01440d90700c40d80d001000028008142006424a1400c0007982c00400075038840142c00c50303140060024000700740c8070310b5a400c1c0c510100d041c041102400050140c0140d41103a18200a5000240001952046030300890701201030b2002043e04410700360b00b0001000540340b4154201910f000c00150490f030042c055050308154143c2e0120848003074514915000c50300c9110280f040000e420300360380c00030726540080b40120b42079803290300880450705c040741c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 32351750 1250 32350500 32350519
    0x1020d0c0e030f07030201020615180c0705071a04050607030318030513050d02060708031312121d0703080c010f091506050603010b04150c05010203070309120f08010e040c0e0c09 78
    0x6440c44d036911400d21009000d40c201d100003600d00200b41c04120395801000e490800511540c04000103240800c864089840c1c0e8085a02000e000741000341d1b40103031440600080074580000400c2c0124055480742c0c920456002070803408052294204030302d49002c440e080841c4c503c030b5103400b4000750070441c0d0b0020362603410f501c0000d0720b1900e184510007654018007264138210650711907441c180c0c802000558509a0a500040091101d241d045030300101c940c2c032000607900545042d415640700000168641301044009400e4480100d402c2044a91100c0096580c20b40b501c9428050842d050241902e246040c02000c18441501c00012940c043c9000030050b0980351010011039000038003504400720414442807250b5072a0406001c486071039814513010304d00ca40d03521103099a00869002c0c00103600c41084004200103080111254100b42c14010703040350169070001d00325101481080711082c841b0000c1001e004070543c1d000c0261070b42e041010028604201241416880062010301651105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 32353000 1250 32351750 32351773
    0x1502070516030203010f1e020708090d060b0405060d080910110d020304080609070807030b1e04260a0c060911030a081801091409040c0f150201050606160f0501020d0c0e03 75
    0x42c4213408103001f00d111420208004607240740d00030742145c20100c0d0072000400c20540d196440075856401d181c4034a030041a000c1d000e0050000b81d602c05440305004138810065200041c0c503070701c15119070200541d400307240c80b806451b045810032841c0802c07403a00e0080304001e440c602d6020000340191010072044401548813030484544c0c880c201d200320001a04032450500000c0c0d58152940d421032001514461a00325000d0b890401110540d0100c62030501000c42103c44240c1703101000100035111842410300f80707030071300140544c4004600101640c1c1c0d14000c4c4c904002d20404420000707000a001c43c1c000260078a88036181d41e000540c50340c1d59030200000f80940b5803040003001d0995034800d03840b07244020700005021080c000500101d40c601100080482c10f045a000240004d211407040c01100480000002c0d00b107a401404282c0104c0e410000017801010300c075400711603941c2c810600d44800350182040e500900801c3c0c0080c45407814038400c003015030781c000c0b10f51540103000c0f002d0750a418100c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 32354250 1250 32353000 32353031
    0x60b03090a06060e100b0703030b04062c010608060f0604030f0b1008030412120507050f030a0311030402090414030c010f0c0f0c0507090b040902040203010f0608160c150207051603020301 82
    0x4075117520044001c010148044024031004d4490f452082c1400b050058480c4000740a03180c05811408400b14480040b040c1012181001c0101442c10034006c5241c1d41462401804404000c0c19240250007207034600101d522108215401183c000035541100704162400140c00f0f10260b50004030010303120008030b5010b0b008070441c1c0446070110324682c1c0740c07502640d0705d42d04000083c45031002c0c004184250710200d40c0c14000000c03c000070001542d65002c003600042d04403185800c521000c113500380b0402c00180c03145003d10b500560440264031481030703240d8615140d440364004410007542020b422601e202e0f03150b004000040550745844601d1400100222425001c81c00082d04a51000d0010450002194401c455803c005080030420000c90380108044c0d83c001c2c0d000b8030912001240030051140d00102180c1c1042e01c43c090076594442401004028a00399000a0302c1c03c045d2160010300f20303e06a0449400c03d81c440b003502c0c0000601c0018851141c030605c4181c1c025424106100602c806 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 32355500 1250 32354250 32354279
    0x40305010c05041202010c061107030305010801051008030403020402030606130305060712050702030313020604050a0602070e0606070c030303050a15090209040e01020a0912060f020f03100b0913020904060b03090a0606 95
    0x1540644c1c0313140010fa00112120641c466040e940305641c0d140d0240508010001010814001c1c0c4001c6060f52520010b603003101c5004040600c203184018003444514400b20071182100d40484000d0707125144d0b8000108a4424010550303070a0100340000420032070301154940c401d001c0b43e118842c2c01c41d2604100002d850040710504010782003000081c7c9a0841c04103210030540c00588607506054580000c1360b010b1845400030702c0541d006d8074041206003400e440040e40494203032501130401e925580c545000c5400c03800000e00703142e00c2d40c0002e1042c08843e88102e0441c142c0642002801e543d070404070b40250300c014030441c0603c0c14140007041d48101402180e4162660340e0351014085c0c0b924443e0300070801c8030700044450540b10b007002d41e21004c036800a410043d281c090110b60302d00b843c0261008041d0140d10024502d4130078445807005903500c80c1c0c0450700044484002d660f80c822140043c00901b4542c005154054000c0144000021700203200501e840c81004100209601c0da00070310003140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 32356750 1250 32355500 32355509
    0xf06050105030d050f0304030c0b1003020f060903060708090f0715030f060b040513110301080606120a050c040903210203100503010b0d020613031a0403080a1406060a23040305010c0504 81
    0xc1c1c0030172150915900420085500900924007841c55000903030742e00301d510600b42e42c442c0718800081e030240207501c4c04c60140454083c085170310300c0c600160400483d8603001c0042841051001880018010102c02c0c80005400010b21040d20003083e101c0c4011020a40c1e10110440001c1c502901102d2503401d9200d01e0080ea0b80d0b414465041603d004108518010b041030340810f640d46174403050040c24100c030041c601801d008806801e02d8603200d400d0222101342c10068407041c0d40902c40c03602c0071035000b052001400d00250303070205085a02d410103980310f04140900001c003454109204041940303650140d4090410100e520181c5540c441c00c05080c2d40c114011998000d00c814100001490228000d04180c030f451404142d0043c1e4a407904408603059840008180080400308010180d00c01021036000e4600c0504005454041d0342040349050004d100b01c2c00307203000080c0d036452075009002030302c2c41e0f01f074603840071900e4100143c0790189600075100803107140d03003881200b8003494001e1007a01d0685 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 32358000 1250 32356750 32356757
    0x91917390c0f01050d05010f030302010c020303070503070311070b0403020705030f03040e0c090109050307080604170a0c1104061e0801060e0402030d0c060603020d0f1202070f05062101030f06050105030d 89
    0x140c400104200c1046042c88215050120401504074403d1090180a00806250440a030b4082c614180a425240800c40440071034004001300700c00e542d08001503d4000105180001c0c024400e4440ca001c148140c40002d0314505558017008101351303001440c04269a4203030b040c1c40c400c07245030200b16628060b502031400c0781c004500000780081c84000c0070b00f820010515040071070320307501d801003070412600782c202c1a00c40e00300c0801c01082c06483c81189941a088040041c07a0030b503100c00c000c2102458100050420005400d00201903031250020000780640b040d0640c2c521070f500c4450114803c0ca072090750455401c046000800000740800c4500c515009409020700c15012007003100c00162172481250120703034802012000da2034190310b214100e4441c10402d8140b44041c00d0010144072080119030031940a10401d001001241d00e04008895040c0c45407521341c048060240e044600038a602040340c41140000421300051580490506d0300455040046980303c80900d0b445960088020021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 32359250 1250 32358000 32358013
    0x604051c05040902030c070c03050709230f040510020c010c0801080d0807080705070f0c140f031b010e04050f0105100f0203070f02040e0601030b0105150309191739 72
    0x401000384c0003154800324090445180000c250340e03031510080250000d0b20154040c44092051030b0161154612841c4601004011403a0300500d80c0068540142443c040584517000704040003000c000303585458004007415901d8402c1c262219008100e03582410001450038400007411810100c0c0030401e204903a0b03604906a03492503025941a2005001c40c1c00300728082180c4400724800c2213900da9401d12502000502c140741a500d10401c8150401441c8160011144c11201e55400a5031103400d02c0c2c107107010003400c803407080142c4400704030b01d8143e50418105030800204007601c0801a040c2d540840e448030310340410f0002100e250900c1082040560f00c1001001d01280410580b0100948014404940e1500000f041402c00100383d02c120748032200c0c034005208504e404624900040e00d03061142c3c0c2180303025403050f070343c800989581060204042c1161800e1000c0207174a02c15001e1401202c65841e0a006100d024107011003400b03540d18a65a8030b001561600c600740c51401e80200e9008050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 32360500 1250 32359250 32359259
    0x100302010e030a060606020304061419080c09030a050601030b07050c06071404180f0e03070804090b03030c060708060f1e040c0e04090c08070b0304031b0c0b0c0604051c0504 76
    0x4001070207040300d56241c0b140500c900002406401448007804c03407a80070303549903442c00740003074840ca04016940c400f010b03043c04680c202640d451800640300d012854644e50307540350047c0d9a8010b01c02d551140780c0500030a0384c050140140010424100d238403800e01346400e5540e00b0808c4541d80110305581a00e42c00420204265900c5200c1550310003141e080749900d82a5100041e016000d602c41503c8409070b141e4480a456106a1041d041298000701c05175190460b256900c1005100394010b138088243d40d014159040d46041060707410380a481c204483c40c1d030070519030281c4240c4048450030f02c07900c0a80c050a1440c14480d003180c0014072121000c13000f0390f03110402c00002c0c100c4250502d080109200540305169554002e54042c0390046144a04090402440350704210858000044644040042c8400654002d820a508560a0301030440c0399042d894a64503004855001112803100030900c11054076011036060f00451159040364000e80480f10ad102004945920035004a60180300400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 32361750 1250 32360500 32360507
    0x90a0f0803300426030108031e040f03050304140303181e0306070c030809010c02060606070503040305070902030a05060103090b191b020105040c12020f010e13050903030709060810030201 82
    0x1c1010310b19110110901c1c803004030203074000304202d400340c9014480740800c40000d03c001510b50b02100d03111304000d10315810080c05660b0b902c43c2800501442c50040310903240c0207126010764014000440011051036601c0c204951b4903003190280c810300060031f0107240018500081151340032a00c5030500c801c0101440e0030081c242940400b40f42290007a80e00d1410155010b11540340700d0400c54561450410190030003c0007940c0050803e40d0b182c2c584200506034540015080da03128a080b40c00f90f590b00194030f0145d042d806107030b000900900c10802c01150910494010f03502c10a540c040c20041699103600440548903030100140c1900000004a80202e28883c1c0b5180c2c00d480100011802e2303032600c803000001e45041d80f040d4006075540d0050004000c01e84c1401030081c030617200c40c1c4400b052036400084504010904490520040300c0c140c094580f1004009600303102d84000c100000e11b00020703002d8580c0d01c200c4000001902d00500400e00c02d008008075402a0600350b00300035100e04550054 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 32363000 1250 32361750 32361787
    0xd08040f030c1a070f0207120f0309150305240f010315030f0b0403020723090a0f020304030c020a06030603030c02040902010e030a050f010605010819050c09060708090a0f0803 77
    0x1d40402c0642c00d129070100700f0441c24010155200c02e220101490300d80401000741070781010001c21900f1800c010484c100d18544c0b12901160840d2061020300e0032480c0c151411402a4062104086000c1c1166951501071384494400c81d04c00d04c5404424110a0301100500221043c0d264070860b5068005950b5109a10040500703440c10320405805442c1d880360503a139000c4180860310351242c60104020580e040c401030300144081c2c030b159800b50f8000d25555410310201c005860003060841c0005d541d803601ca4004194401e6910b604661740c0c01c10342070083c845400c1d83d4041c1e02907483e015001500d180300388101c80482e038056031400202000d82e401c00010300390b82d42046c3d0400840d0038071100305540520900c1d642a20403001000040d060324003a6080d40c009a104906010350b20080050340800012080041d5001000000b0955600f006032403286c003032515884c1d00004081400400c02171007400800c1c80b648116554100a90f41e4400d0380303001516400b6078071503031301309021030400101c90300c018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 32364250 1250 32363000 32363003
    0x703050411030f070302120307050a0308090a0210020a0201030c050301050a0306020c010204081e060108010507050304060c03090b0a090b090a0c0b0703020304050414010e07020a0201021c020a0f030801170d08040f 93
    0x30452030100d070000a180002d0307803119000c542c0010100300304601d8811194000d200e0f40b000558180b000700c0e2600368490703550001c0a414495079000117a0090303000c0c0700b40850076600070501d01108110b202c0007580ca0300c403203100300d0129103020f0020186a0080045c0c03412508014038140e082829507454401941200344a041199001e00002c00c18410600c50401e01841a1804019030102184031601e001c04c180d006000c184d2424050004066106044980c0f25800c06404515050114000c8004105858000e06008640010b00c9200199a0481c40c0344a0180d0700c080701580300c0c00b0005444500d50f038401050085640410405814100c000c0d20005019005803418640d403030000c40c042d41e040c42c008036811148000184808001d0f041c0641d045003103403000302500c00c241d50001c0d40e034050030b8118200d80c031004107003500100d100304410b0140e940c2c13101080c8000052440c005c2c000341d00c03e00903a00b14001400c14503030100d4001503144203140803541c030703c1d0207134880c1c0d210310f020b80b000c4020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 32365500 1250 32364250 32364263
    0x30908060f06091602030c0102030c130b0f3c030a060806060d2303030c040504110a0801050405090c1c05070b0f0a03050a11210c070b06040e011401120506011203020607030504 77
    0x41da10300c094082c4007852060040442f81c5644441804040b00040b0f007541081762084002d20540c4509510003041da40c0040b07802d071000328010004c41141c18080c0080c61040f5840384c01d2400071000744000c5010b9805a4000c038402d0014945500d00f2545511048421a8014503e0340800c0702107480c44240e20000c0f03588010344403840d072490200a003154402c5074101c1850400040c1000300d0b044c503104a10540c504503035a01c3c107200c100100203104850620070f103481740d0380b03480226224900c2030003907072000c2400400b40e40030030000b480084469200d1100a4035217000d10000020006089012505600740c0f02da88a45003099000382a03006001c00f5080d1507406a803a081a5071203113a050040000d015040401d414407101c0303c20360310741e00500824414074000b0511442000a41a10710160410001ca40200700500709132882401050306441d10b011106e240e20000640040011410700060f0143c01a1545681c860200c100e113405110002001a8007000000e54003d10a83c4074980040c4110f2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 32366750 1250 32365500 32365507
    0xc0609011704030509180708040204150909060905010c2102030709030b072c010203040b0f0702061201080606010c0b010306051009020f04050306060f0d0b070507060603030908060f0609160203 84
    0x1c0305001141d04440c02c40203d01e0000d0440640c1c68541c0c4400481c6110b0341604080d4603100000800700d41c005017009014a0b200c2c082c8134817802442c01600003609842d201000086070390301b090005082c0c42001500c0e45d503c1c115840181c0e501c80e2400003003100d00f000c010800d01602c100303404000c0d0700040008081003400540400000c0581c590701d401120540e80f07800380c10708080d0b20801072402c0400c079280305160600304483c00d41d070007100f610121030180c805103440d0780040c98015a20b102e40c0e1802136005400040000c1c108c3c0c402140d65041c1c0702660101d603001e568600040d40c600541480140071102032070010400905150020769000b0f282e001200e441581e60f40e4100b05a80007502da5400480010806000c5805e08101441c0d201c4400c41e004804904024045802a90410005031007842c0e43d800107020399000b0412181041c0d0320080400120750340342401021916035000e043701c03c0c0101d0012981c1b605104c180140290001031005010341c40b52914910349034442503202d002e500013407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 32368000 1250 32366750 32366777
    0x2010c0c03080301090f0c0903020306011e08010e0106080607031e0902010e040c0207060311040f0e070903050307050703020406120c05040209010311070f0201080601140913021603032403050c060901 87
    0x6000c0e600800a0501c08185c07181b10116a03c01c2d10a03072001c50041244141c1d0400142e90f0000fa05130441e408801260b020620811402920b01200c3c4c210140a6080c180c070781403d02c40540c00348d001c90301200e0603510f0300d4035034190803410b444460700380d05180d002c441e100074000c4a6991220071440e10506040000540b464040f40580f0350301b20504015030444201044002c3e0140505da9010f407a541200380f406082104000c0344070003c1c0a451102945100010030607401411140055038200c0d04894540c00700b8074041b960740807640022801541454000580000c16000b84444141c1c4a600880c42c0750410701844001d410042490f8100754076610401d080300c40d49001010781600880759400207004030f00000d003414201030400d50400203445d00ca08100c2d13200b1400d941030f1142c103c694440c001410004c071006401072288440512415915031400c154040e0300a10002182100e021540350003d40000b80145d818800503040780c2107c88410201e00e404e100425080005041000559080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 32369250 1250 32368000 32368013
    0xa050405040c030501081e0316061d0105011e030302032b09060506040501080c061e07080307020f0f0304050f150409060b0a030509010c0c14010f05092407020a02010c0c03 75
    0x503000c000404c0d690801130141e02400d01032080e1000e084c80342520001945074055903640701e03810b04110742100c0344da58402000b101d900700806d502072000c0100000140c90600074000c2c5400e102d20380d5034000c185083c00000d00c24070040d000302ea806401650400210b42112101c1d40c4c1c190300030300042c000d0350b6071b006145404d9203c0c00103050b01030280000d107898450188401c0f0340c1e040c0c2000000343c1c0701031455041d55841604481311070040c0b00340d58100103403080c0b2440680c040c0040c010040c44001c41000070710380d80000c105041c403003524121540d000505003441e803280b01d035002d080d4015084200d2030046043c131441c040c45451401100707904e025a130300c4c0c80d5011100c103034021143d030400c0000c00403c42136040c0259504036003440f00800191180e4076000d0844074003004010881160841540c01d40403080d4001021502d5400c801e00c00740c51f244c59604c0d06ea540030300080002155100c0380c0317003030301088140f40c1e44202c0d03040c2c00402400c0d100780c005580d1403803000c4003122200c1022a012001810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 32370500 1250 32369250 32369261
    0x3080712050a091a011202060c030d1a010206060a0b1b0307020a0801020a020607090e0609060f0301050f2e0b03041707030509010914030d030e0f01050c03160f0c020103020a05040504 80
    0x2c1051000903000d260f071070810141480f120030324100103100780c0140a040880210040c07203c0c4d0485041e651858250141c40c254052000120200c07461b007040300c0408803003080300c0304400c60264203583d000e640340740810850301d005000310706006900340040001ca0000f142c40344610580341c0c00306d80c00d05455500198030b00c0003035000f203007103a500402c0fa031100701e03010051550004ca05040920b0201c5c1800c00001424000034080c51180c2d03103000116540745c41e01c0e9400d4921a001070300a2000c0c2c50b12180200c1c824000340d64020001e05c0c2104841000c103001c03919085549281014400950300d0485010301c140c10240041e81d42e036114078540e050603480741009011aa1207a12542c2e1100411301c009003a811031b41d4041c400a0704515200213050ba03000c900814000c0c400d041c00210301808111184c504050703c2d607100d800750f103090244499030b0301c1034002d5403184d01840c1c025008849402c00c1180c000c10007603038000100300d854100c00300540c0a60040d202d44802441c1c600e080903600c100040c103680 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 32371750 1250 32370500 32370511
    0x6010807060e0306070c15020f160b070203120103020d030e0607050606090a0204051807050d0c0c0506060307080601031202010912030c020705010503090c04050a1401032316030308071205 82
    0x340900c608220542e00005018012401100034150616010303102508103120607600400b08104600f01d00b8002440740c1c140c03003d940d141902c25880d03d00580b10201c40514039207050301d0110004000900c054800011500e4040f62039451000740c0e46964280802a00c034600100c2c1480791012040c801511604042d00480d03014900030152801c161051048140014000204150040000740081c2e11410216207801e101800c0d032034100e03600c0d5501212035002d890045150b150400201e0304c00c06511112040300c4500500c25550705860b00300406956000701d10900c3c0c4a904103000410200701400c0e031402540125000101d0300070b406035244c450000c0e0010f200404030b580c841c16000e03081c0d8100710540c050079080c00c0140c998200320402d981e540020081c0240308030b4603140005c0c0b0002443d0030541500b100410025940c0d40c4074944400c80a02400c030f1a00b072020007403003803c00098002020714194060943c072100d100e0842d00d080741c0d2804000c003c0400c0c4002c01d500c00d000c1c19184e100d07040c800d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 32373000 1250 32371750 32371753
    0x3071d0106110706050315010306081b0f040513081602030304030b07020d0c050c12071a120c0708030609060607020d03050a120605090c0a02070e0c0426101508060108 73
    0x9604200d00580b003940341001c10441c56010344810300c11990000b0403a80c100340c00c9210302080d0341c2001d004070098540c54001284a004130046000e190070406c9184440d071208551b9120154082030600044407801c640740403105000e0450b8401050400005000042840740111040002900071a01d5680241e0044446644090400c90704035818080745504d00310381c0c5040d2210710301a444159881c9035080c070451103482078180300031600d0030402c405c9000304140d096600e0b034007001c0c40c03014003070ba00030190002c0035100342400100c281c2900c8048a04059002076000c1c25501e13040207100309001c00904583c0c00a00030001000540d42e244140c0902921981c1c0f8143c3d074806507100280280d440b81c04c90f040381414183c050144d1f648045a01d0f6104590f00f0349951201c0c000c1004a02e230101c213030321041d042c0c40088140305807240b1940080042d603162800c020b80e03200c0b603108202650900f01d070100c2000e0b000000034000000141e008003202d13036601c00100c6440e540f9000b40350f040140031792190006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 32374106 1106 32373000 32373059
    0xf0703060b030708070b0405040606020f06130807150b030f01020901090308030714040f0603140408070609080d06080102030a050f04030504030609170d0b04050a020a09140307 77
    0xd0207401c0882d178015030354541d08515680680100f83c041ca00b444400305280740000341c10403144010000424641c0e403402941c8107000f030015002c0f1282c6408012100216585c0040c051044181000010b00c80c1c1d1980e0030075117000e500d070750800f4459005100c841000d030b8001101c4002c40b07070480349955880d50b40540c100d0f200c07240750302002d2803a28003090202d21820281c0c15281a1a201d032010400d545170301440400f800d40480b4002d2245404024560009030f40d81c121940c154070a48989090031074040a000a07650b5903000320019039800700c10054001c100d030003050307000415100c0082943c102031701c00900e0f500c11070102902c0c0d41e0721480001d00304000400007815039056030310381e1900c90681070072101c05001071458070b510450400001ca1121440d030300c2200c2c80040b00c1e845141c125450881d0641c0c040700081181c5906008450707000801003031460036070b03112002d1518001403 = true := by decide +kernel

theorem cover : BRFrame.Cov 32194250 32374106 := by
  have h0 := BRFrame.cov_init 32194250
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32194250 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 32194250 ≤ n) (h2 : n < 32374106) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
