-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2954
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:14:30.574566+00:00
-- url     : https://prove2.me/submissions/80b2788a-1bf5-4730-a63f-62f2ab337fc5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 531115107 ≤ n < 531294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 531116357 1250 531115107 531115133
    0x70b1518480f0a020c0a0504060b0415030f29120c010302090d051204080f0724120222080a0305030435180904080901030213030b010b0a020613050307 66
    0x3141000030042c10030401d90040080140d9000b980c050300b81700002108000100d591070340311500c0383e0b0500c42c0520110703541600b21811507203040541101d0441c83c200a1300500702c281d0004412a00c0d20092100b10080d6124001942542d4641040710074400c10800100228800c0b110003240e0110954035500c1d406603008003a080e0b801420200703c01003d60740c56241200c1603488425611022808001c94242044004400c0c0c920720094105a81010601e0030313910890994901c1000d01d200035854814014118149800b0300300344107543d52440203940c4a041c1290291000c130301c40003082c00196450010858660b04c50741607460700c2c0766848503152038046105120b401e00c85030301201800032012406d5400712065060320038109845603810107105d8144240e200e00c1d0b5001e02010b800308400a0b040904a0314049403d01b001a00d42c52641814501e080c01d0f6000140314940080c000b046907242c940281803510f01507400c40c2c845d40c3d0b4840c3c18600d4241c580000501c540c1c401d00001c000210000300d840c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 531117607 1250 531116357 531116491
    0x210b0109030c030602091c050a080d0e01060e33010806120a0f150c080a020a020c120a170f03060402030411040f0b0f030c010203070b1518 61
    0x1500c494403601c0e8901801c0700342d80112041d0345d0002d215503481c10130740c03902c5058480a0f880ca040500203070f140c030703919140d40801c001d0020b0000650307080c103110305900c00c4400c1e02c00f48008128040d25169400c6e2601c07800d42e20401c07440c071140b82d00606a019040f107150504042d00304100c0402d0b0f00c4005550505015000d1f50344144610344442c200041007180c62005801040041c000540a080a80340c002d4810503040d41c1c5410b09096400c43c03a0800d0807a90403c0b5821001642c5800c3c9030b0301282881c480031803003030740301003524100d80d500600002c4968000b801002412024a81681840e0f07503442945091a22110207200145540c94960b01440c0e00c41d0203552113450810140300010212400400d880c1c000560b14007000402d8105420640416101617004203004a06080003035500c6c000d40a0003400f10034208001550091080d0300b4048a04c005010308007800460018209510011074400003c10610304800c4051112100c40a803003050342020501d02005002e0000b2428250700040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 531118857 1250 531117607 531117617
    0x2e0b030c04031703071209020607030f05090d050c130b010f030e120d150602010c02151503030c060103140102030112060f060e130b15090f181b10210b01 67
    0x10070b01d440304424141084060322541da142600003c6c040300c04012055952034a070010520040e101c94040381c01c3e858040c04c04044d0b580302100121428400d911415401512400b204003c1000000702101c50309004c5a13840d821020741034403481110300b000900d60000e64501c48a0310040c1c040c0c0e0114040100b2b036010313280078040c4800912b10039031025154900c1250344442443c4403085c10300100c0050a2603200a1240d80744500c0c00968581c000340000d00380f40072840121b51849105207480c801c0e0746020703080e00d44407006000b040303031151001d1105841c1045400c83c845940caa06202b100d050724a41ca19030b004030101510b50f00010201002090700142c1d480401207003c000b06109644111401c0c40c240b1320361501b51030520942038001c1c0911224818444c00740781650340d8198040da00410b0032075400c90310790b5a22400804407240c00024032560182c0e020404001c00c0c5014440700c80a001e440d2050302140f0344074211000418003481c60300390828503070090a000156041000c0c030040500d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 531120107 1250 531118857 531118859
    0x20913081201150e01080727030b0402120a0201050301270603060608100209092a0c0106050a06110d0e0a090e060405070b1c020901140705062e0b030c04 67
    0x11002254096200120070500d003900403c051a081c1054203015012854124201c00455002800401d0098803240c184500034600e60040011442a40e4202c1441da10180d503031540c07810114a0420250740680c05800e0604101e040500001401454190706a41d11840c5a107000c03103800d00d1030f006003818000200c0f03514042812491a00820020354002c180c0012281d181034407151500180940c03071034640d4014808401580d0340c03050510b03801580703510704044248280a102104000b452201d1100c5c4001060401080c0c5055002000380d44041d10450102034503004180e400c000d9810040f01540d2110040488881c0f140c040f0006400dc05032001900325111003980d401d81d420325408000c198494400c02c01401020410304000781b020f0030a0b54a44540e10090407114150390001c0940150001413001c1d169200b1100010400740b5512040c0e1280f880d031922580316801a00d00c01d0403038003601ca4081038a00c0a54208007981d0300564000301291400e201c1448542004051400103002400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 531121357 1250 531120107 531120113
    0x80313030b0c090915040c36050303070b1504020405060a03090203070503100e15040302070b0c0a2102010e0d0c020918030a0f0201050109180320160302150307020a020913 75
    0x404203025041e10b05298110109840600c0126910746807c0070411120045180141514602085a000750707401800310380b828811a5103107070301e182e920990700752000058060600075140d110a00030180710b500e406e0700c2d22844042100340e000d14050684d101108001d020304d103074041d074800d0001c03e04c00f5007030368140707035940703000170706142e08480501d1205454500c184a40041030000034241c482c148000040c904007620029528091402100c07500d403000610340c0d00d0003404120b504040c03940006180d004d410701c04202c1c0b003006240d020380b10240d8207058400c2c0b6440700201314100d818650303035100003420b0a285c08001c5c034688094070b803504a4000e0b0901c251907200510041201c1040760301d03154056985502c00a0071190305a1085600c10301d801ca080c100701c05852107000c080b681603e8030003100c0d540d4403000d000b03008070406001414807070b001c2e913042140003a0300ca403c1140d000700e800d000001001e50069840f88411511100180c00c040100b400503d080b003821030304030503a040d041300b02c00340d140d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 531122607 1250 531121357 531121369
    0x4082506050a09211b140615011d1c1e0501020a09080304050a0620151905010503030d1d10091104091205180913020a080313030b0c09 59
    0xe11401d21840d1220a40c209014003030580104d6005085640052040f50713081c0240002c030540450001d407880001c4800500144000020032a0441000e44a007030501c07002080040c0c185160310740c0800d9951800c014540b01130828004000e03000fa0144074805056880c0345401820800c0c2224070032001400910000c0c82d00c0107015070a44107000060340c0360400c2901070804402640a120940c1c4100814030264541510b01000c580041c10301807910107074040458804410580f0401043c802c2035001e650b01c1c5009000b042c0a115104102d141100c0c000b0300300d03415558240103280c0c066008200c031160710b040c60b5000c0e01a070f20407400380400892010040c9030501000c6104460100d841c2c512110600080c8014200b0300034080b9420030000d4030131ba50300c4284c880441210018003501003100d900b00c4ad190003824030760703090090542d0114508a40c01320f44d030034603e500a901441e084807000c40c508400000300c82d8111038800303401099030300d159180e00c40507500030300c00e9400c0716041c4454410741c3c1b10b030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 531123857 1250 531122607 531122611
    0x30c070b0403060e1207060203060a030210020601090608010207020f13060b0403050604020f090402090708060a051002010e0d03060f14060706020d0b010f0201200d1d16050105030408250605 83
    0x80240e0703510740c5141400303000d56a942480d80001d8000d038242c0000d2100410403504800d5216101503100c0e550341001607240d01040c1c0c03002c0e41044001c0c9410030000d5001c9003190590381501410001a52640e07401b5080f4004c401340290003504010690780b281c030701082e59018039001e112004c10800c0d11018081090f403c1380d17008660b203a0042d01800114034103d1207485410304240c80205031880c00340c00140d55080c0180c1070500380400c40010542c50344480c144840a1322001c1c0100103032003181c5400078024046010581d81c50b008046a210403d40300c0d0140c1030841c0d682c0325001c0d2056080c0240c4a80c040c5885038500d900c10002c22555001802c0f900140600c41216000000c18200080001d025400300071202c0c021279150040040c1d0840c42d04c05100101c801d110450b81e102c910201e41e0030000c1c421360042d4040d8600d108001c0401c0c0d03400140604101209400c0c2e543c0841d170781c400640e501d01051b5001001c8810501c5090010410301c00b50f5081c1e820341101d0642d400c0382e1074881030111441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 531125107 1250 531123857 531123869
    0xb1c09050f06160903150b030303070c050c0d03050a0f090801060f0510030b060a110f1005060307060c110103050a1d0706110a0c0306151707050109150f0e03030c07 72
    0x30403481d00820041c01d0041540c029502109065003401a031001000b0b01c0590100601c0303400d070b402c1611800c000a07409401504c0000e400ca03903481c01c00c841c0c090300c41c11034003400301c0c0c1c03c1c80741100074095802c18070316072001e0a031b240d12414181082c60b02e0558007100012144003c1101000c400a09a2030901030f170801401d8501c024000300781060305000302a41401c1446050604000002801d42c5581088401d208514139046264205c00303203400341440128810b4100c0c80c07090041c8241100c1840e0f0103580110300031821038440b181d80380e03020340c3e80d030101c15409400d82d40700c0240c3d581d16500a0f0891036001c0e4842400103408111820800e0f04031440c481703241c01030f501980c800e0044940081c0c03800c16540101004100da43d03500d40d00e80b6120481c9000003000a6112182c0145d02d05840b20071002804c0103034680e5211607400a038095403000e0034480c050004049220000d07400c410400a1000e00000e582c0d4002d0300d409030403003030b200680c03400e20352034161104102059034484184504005440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 531126357 1250 531125107 531125113
    0xe0d05030316080c03061e010c02041b0f0f08060904170309070504050108010218130209090a020d0b0901050f0f061c020d0b0102060f2406030a02031017070b1c0905 72
    0x180200c801091590002c00041300e4003c1081070040f0355668074801d4981c1400301003040203076040c2400496402c40c0c3c580c0025005400e10b116100700359108181c1500c14030440e51032051041d0b001c2802c440c50107462002030081280310700880c03014240140300b41c0e8058041d0302c00d07000e2541582443c1402d42e20454180d0b03115000b070102403085181900625005040040080d030514100814031745208a0345580d0764460031110300c0d46013035866a50141c1c2c010703080042c52001a0319017115a50040c0d801046007410031850101003004915090981506840020f0310003050346070341205008418030800e0724241d100c0001d000d84074020755512120441c00c17201190142c2ca1360505004402910686030342c40341035420032030030060a00e140d4103002e9482172040c611a0f604c01c41055040f1030390210220a160040400020040788007030715002503001d6000f40c40044c04260b60340b1145000c007568000b1521031600039441c2040422600e80161460051070070b0355071405515000c07142d0450f2491201200d20390 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 531127607 1250 531126357 531126391
    0x2130207050105090303090d2708030309010c1704240626030733050a0614040b010503011e120f051005011214010905070f08070801060e06010e0d050303 67
    0x6001c3c041d007034224150030011400c50070b2a00010ba01c402c103050500c000c00140e050403010040d000c6190920110200c0d5401044030b032a5000710751a40d00c00c403465401d641c04c00040a601030310490403040c1140c00303079403580026165541c4e4440124014000c018103c0101c188680c1d07140d106206103001402202c07407511038049144085021941d80e07034486101074009001c3c0e500458440c00d0b410002c01c0700e04261007401c001c500308154010783d4080840755800d00d05010072604c0c81407a40301c002038421000100c0c5200d6000410130007130768420003100f80007900038801040508031940c01050300801c85003090b030120f43c54205c00305442c400404266800b40503a001c24090000520801d4402d0580301400d108031741c108080c0550072005180c00170b040f14800415801e40620039881480020761040965070120703034403468500c4240b9140141040360140504c0000c1940d414030a0108a82c04410b14081d40c0d51200d006507160724142d40505d80092a181c0810006102440210f20038400003800394800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 531128857 1250 531127607 531127613
    0xc0f2303040f0501021b27010605280914121609050f0907060e280f0b04050f041508030a03050901060f0608060909012408060f0c030114060702130207 66
    0x14a142d82e2045066412004861030f8510a1007400b006410080d5004448078400742c0300c0f440c071008819861111858550000718031164000300410a141d041c1032004002d410100d883c400680760a1001e8000ca0261041005043c060044e010341075480100b9101507810609142810011030a46204903a0072401d401d001003030303a501c142500304420740e1140c10350385031025909980302c1d1b145c000c400c00d00440004402242da11940e070307101c00c403801298170802050881d030700c1000c540703050040c004042010100480c80f1640781c8162000c40d08010a40050801c0c1d00082c00b00400303407120101c000072509503000c142c19004000416840005540015561400180003821100a900003030303020340c18030004004095003e6162900715204450407411038545181841c010301c403030603882408582d0403501c3c0325138208080c036080c129007141b41603881c3c90307413007412034440703450b04540080311104244014881a008001c440041c0c000280406d440c0210302e400050b05502070b1144240d1907500000c2103010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 531130107 1250 531128857 531128879
    0x4231314011a0903150a1508011e05240a05030304180f06050f33040302090f0108030f130503060103061a0301050c0a1215092003070c0f230304 63
    0x1600b000148440c2c1868004000070380c866080440b00c0d0b00f00e2060601040c004a0742d42e01003e00709110229440c2d01c1e13655241640c0c0600007120320010071034146205e82c800d88a050040324424545002c025880e80300307007a0004202505040070607001121050080340300d4500f040207001078035009204140d03040c04000307138006035403e04820390117807410301004010780d858104415240c004211030b281840505000f1035402d01038041141403110024801c04108120440c0c01041074074001d442510182e6581d220b0a88107407402c0c8076240c829403040020396500290300e006806850b16a9080103035a0307a0b1000040d1274a01c080e0400c5c0d40003680c410203405d6a0750900319404140c1c00540083c4858038155602c0003450103203502200602040500368140321086a0124a02c070152000c4481d1650300c941c0060300501034030350264400600380c1c0c882c48032041d0400c2940c0c468003c80c1e8800079414650b07030312a40c1482c0300701c00449101031a42007103001d0800320001c00d130390448410000d42d121803038860300b515 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 531131357 1250 531130107 531130139
    0x2030c0708010b100309030e03010c2703110907170f0a0c181a04030f0803040303272405070e0f01030605010e0409020f03060a060f0b0423131401 64
    0x4507507803500c14460103a46510140c0d0002485500f0000f81e80c040794181a1881170b01907500c00e03815441c0c87c482c108180d810410405110300b56652403c0b0a042c1007844200f1800c043c00003400450501c0c1c0d03a40b095190124060380e20480c5440c200f0085039000d01c8444a55205827a01ca0000800804114608040b403088114685161030001c1c0c08072081c01d1490300300700c1680205130403060303140d00014858041404407002035602c07411810680c0e03118141041c0940043d60f088002a040041c03901552000c1c01c01075492480750076403018110010355030301c58108242d01c403105280d01c1c0d800310030411140324401e044c8070b00c005072121000e02118000304801d40c401c03490304c181494035007013081c0520f9138008000d03c04081c0039100004c0d004280c0c000540d082d00d4000b9200d078503106035410400100a180c201d5411501c049103107090464a4003e03031142070149010f181c13a80104a580c40c1c0288541d070001301d00108010701225988007421000c00302755188403100c0390702e41000d480100215541000400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 531132607 1250 531131357 531131369
    0x30e010503010b12180a0305040302090a060510030b0d0f1401050a0c05070f020609030304030c14010f17040c0f0b130b130e04050709020d0b03010b030a051009050c060a02030c07 78
    0x1d2540d818600221480d008900d07603400c4a0003da4002100c400c081c5101040301c0c1100821200034000c1890018065405404128020642c002c0403515446260140c001a036400519081180c02000011402004c003000d0301e69020851103510000b0480c0c060740818030600501c0b04551782c2d0850120f05007960406070a04038010305c1c0054603c03c95038007605507410980d1203a01d002070900b2a0001409500131003104641c540000903000082200e0108170500b11a803080c4c0102c40c170b032030071001507510740c1c1c0c40e10103400820108080161303000f2680420310750040c41462110740311611010480501c0c80d03281c1011140100c005800c001960403102d06500a101d28007003a0714180c8040594482c4007101c0c1f0030107061515443c0820100303c802e00c00a40540b0380e0160442d101d4154000c50340c05000385843c03490083d46828450550350a0106075400c01e41c0d040001001116070351062203004000d4150192114058409540c8240d07030f8880c0144041303441d070f900443d211100079001509040059200b8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 531133857 1250 531132607 531132617
    0x80d050603061e2805070915031103041e1a0703140103050a12051c0b0a060c0201210603080c0c010314071d15070b0114120703150912080103030e01 65
    0xa00380d42104800a50f030110700854000100040e030500701141c0c00006070341d60f0700517040c20100034210ba84030b0000300c00c43d0200041341c1040060400d040d0201d5000d00043d440f00c1c6410800540840d04400d485c80641000c4680076513015855258086a14408030040c0b180d50008010b002941d0340c18010442c0c0c41c008002038120552541d92001da90300850413008055030028412600e04500600035101181520171210b10020790b05c03070b9280c1c000c0044004852096810030804203401b071040000080e4203606840364208258505000c54032640310720310b5020043d442c0e007008800188000c001d0101041448001c0c0100c082410016054a40254039280740020101c1007041d0198071402080c0c0c0d11940303c500c0341c0d1415074000424902203207550602c441c0003000903410200045507a03003a04980d561110360030380c05907040820410b1a03000404004075071001d801400800c0313240c0c00326049480c400c8800140d200340d9a03034110a60181750b0244010990000040041c150040b034041d003004000d00e49 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 531135107 1250 531133857 531133891
    0x6050108030a0c060c0309020d0c0501080114210c15030f25030c090312050c15071205060a0f03150501090b0901030b060112050a0b0a0906030c0506070f080d05060306 73
    0x30041143e07401c001d020b07035031556403001c402c41c042e90100005540281083c914402d4505103168488078910950340005c1c0b269000182030784a40100d002d0200b0f004000103404500400c0c100c4845992440300303900f43c0140e0b514081e00d5560520300b4003140e1109000710f43c50780307004885c140490700300405802001c0746108414640400c14205440380c0e24241c1000101150003030011224040290401401008405040204280c0100c0035083d000420011202c1800d4500d1841040740c00a07034000d0003003103242c3c240320341c207030940d400156124030050020413445039600c080c1c500900c5264816500340c50886130250b184000380c000d860241140d91000e010314000903010801d100014403025010042d0f03240841c038160300c03428a18000d00e2142c2c2d030601190400c0300090380100011580c0324800d1303200080010301d0150714001c07201101d800c901325005503031415050203503592024408039486480103000200065036840509290000560001030b185020410f02d4506500035006241e41000134107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 531136357 1250 531135107 531135127
    0x90a0f0f0638071a13050d090e18010f0c031407020a0b010506072105090f03070515030709080321060d0b0402130e101b1d090c0903010e01090605010803 67
    0x2011107000061070720b0b580c0e903082203081c15806440381c00482d98030103c41c0803d0080c52038813a4401281c0030300403029251408956101504d1a10181c032034a00ca6051900001c1c150b0a1400384546000d800032001048081424034480122a03030b0491601c0441d981c1c65148504c50b0915580c1c60b40001c8a000500181c3e5040e1108038814034144100c0b03100e10800580c590810004003018040103108090451002e10b1b001e40150142e0001c00d0128010782080300d24807900c0ca4000788075002c445014080120104182800f41d18541c00100540e00303004002d580001d070701c0300820041c08030080b001d07011140080c405001038101c84001d8091446441c0c00601d07200814001203010b070b0060b5040b5001850030341003a204a014040c82e5071069400e01a10b0050700100607540c210304421982c50301d0108030f00d500000305a0f402c014142e200340040344004081596818601d001c56000714070074100e01d0900d0202d0700000d0030345400e03180207602a5142e0700354008002460148a0140022034091402c0c484444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 531137607 1250 531136357 531136439
    0x1090c170f19020d020607081c23130c1a03090d0302042402010605040207240c020a240603080c011506020c01050d0e030a020601060f05040e06090a0f0f06 68
    0x40684940c04d1038011074115900e0b00110ba4a05500c17031000740c0c0351084603180d0030102c2c2003180c1c0c2801640c103242106038441c0c07035100000f42d5102105001c3d112600c803200d0031006100401002c44000c2001500814182c401d090300c0c514180c0d040c55a50303900e00d003140c0c9a6041078841880541410f0050005000d81000080004024a4928211000c400280900300e001d05183c2d40314503005031000424505001c804e00e800e11815848889001c0d400030100070a000b01d880f4654a0001038000008200c0010a40e005841740020392113400c0c075402e60a440c2c2642201e045a00449034400009403089503c01e082c065044501c80c000445607000385801c1000e9110403c528469040040001c0c600d88805401d070f00038449040c1c504100c1e91201c080d201c0c040d550380b100b0f00030740c0d0200d0a1480030740c00480c03140c0c08407015540e4035a4540e40580b10780003440064400a403e4006481d10b07106250049141c0e40b0505044240c1e103480401c00a103000d4190f00c141000c2d40c1400030445803050400c890913412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 531138857 1250 531137607 531137653
    0x1605010b0a180e10050711010e07050a05150f1324050f1c09030f08011707150509102610060c05070b03011401080105030109111201090c170f 62
    0x1010b01040003803400742541d050004096844d1101450181404086d0ba8411084070000340100020066204002c4486541c4c03c201e11803da8041c0c52841c0a10450401400b24841c50682f030402c6403c02900c1d01e510025504042c0c070107001046050400c00c2500040c941090320701ca40007045d8680c030702d14108014580d210b43c0000e030f0819180059251600580001c41a449990903141080038000520f0020301140e45c50281000040100d0000310340314560030903643c4160003020040c5880c901e40040701c000800024403180601c0070610603400d00f6190b1520b000382070b260b203564641c1100c8132004607010685129502848100280003002001c500503a003190075500d01e814000d5400c0d2a6152891410080380c001d60220315001c0000212000e1400300740c4401c620980700c00c0c0041e0780b90780030b041c22540d0031407026001003417040784524a03041440d103104008480c1b4001091204007916038030260030701076101a6410340b2480080205550510106880000c0e0101403c401c0a000301010200408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 531140107 1250 531138857 531138899
    0x6050f061507020f040b0f0d05060f010806070905011805061204120507022d030d02010608060a02090f1e1c05100c020601062d0c03020d020d050a0e0d081605010b0a 72
    0x1a4122100195845911180b000341004005142c00044c278642192075010a84810f100b42052034004a2622001b107106446070b1090364a0f41e60f0300c5e203424011991100304124092918152030004560b40d00d0b1100203010541036011031038581d09007843c1116003031900d40c5004c03042200500200e00103a964045400214800e21070044150005101c100048040c40d92690360510880d04080d410070307019040032040320341e0201a542107554160f0880c080c2e10031031807036a038054800c0c9510b0300581f40001c090403081c0c0340e040145801420007404641c40c1c04019018169908981e1210f004011040101e851420880b04c02401140031003d0040d44d1800113006030002d200403c2100e01416190080d01e00d650701084500d42d40c54000d4050191540c09180d406400500410b44500484e500001d50801440c00d00d41c0d0b00c1d4a8031000341021255041c0c428050740e4028480760a040108001c04040c245c1018602040450303041d1916100e03007102c04099400e030280303285000820032010a520703000da030021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 531141357 1250 531140107 531140111
    0x60903041a0f0d15030c050307050d03030c0e1012180b0c0a020a0f210906052505010203040503030613060f090513060e0606040f0203270a06050f061507020f04 70
    0x250b49482c81d0341c1c06595103810940b441c1c0416120306442c1c54541e00200d074040d041c4105440d40f140300f07241d03d802082c0551500a03419481402c0040c0c13203035022002c14860380c0f82c1040000318040c0011400225200c0010004400d0200c0340c2c0842d100b40f2501030070b5107481c0e05070041e03081c041c8c0d0303001d586180090034007500c00804540807800302e00a001140b4400d46c4800140714a0380c051034581d1018440d100d06000e41c1601c03100c000381850082c560302096507443c1d201c075800c1050b4144d1906040c14448a0785240007000d815410000380240050f60199100300d0156450307107131050500064503050381900200500b01a02009049900d04c0c00d02c2c1695443c85022440d41d944290000c41c0c5462074800078100c91410400c28144000410407600450044409000c0540d0780c480460030f9000a81d0001d18103158410000c003406091080e010501045101b5103401c8205519124115901241c12001c109070410410460380780c182c119010600e4094241810180b090700070604990744200172501440d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 531142607 1250 531141357 531141367
    0x5010305040c0906120b160e040b03210c010c0207060c0213022203150606080121080a090303020106050612060108040c080f1c0e060d0f0b04020a0201020903060903041a 74
    0xc100e000561020f00385504042c0072290f80c80c0400c5c0c10015841d50140d4001a0040200d0b500c4581c9030321290918038145d032980102c000318000c100003001c19442065040c81b400111444c0502156000b490a580341a40707035450b04c40b004046c070300b5500c10304030290864125400502289070003100e00310105805841c01c52942030002d1110009220300703507000c200411410184c200c1e9800400000e002d80344180241c4600000034844c05c2d003030780d030b49000352804207032158014011450240303540c9a48407052a60090940d2443c2c0314540242e00843c845d000041c20540140141a0240240d10040c4020759443d40b905901d080504030444025084074108141d03034000c03c05202d013440d2190082c2c1150400e940581100d80401560380e024110014411184825460303602809900c1c18a1059400f0304142c1c60711006081800041072070400003211340b551800340d03540c2e17600d603440540641d4150f90001607032009618105840c0440080442542c4d40c0108814030860280c1e0000002c050750300e240c829268 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 531143857 1250 531142607 531142613
    0x5030c010909150f1401120b06180625030806030a0c090e010b030d0f1b112b080703111b1201090506040c0f0603020a05030f0a0b030a051f05040c0501030504 69
    0x8415135004544004c2860400301c1d20321032502c0c01d0b030320300e40e42601d5000742c900c90900c0900941312000f20540d0300082c01e12241c103000d41d03007401d002da0102c402000c1902e84411301202d001f07520008071010701564501c2462408040e000074000d504101c0450082c0704d000c8c40c65a90300703010300003405101c844c141c03284203031840c0c0c1c9000d42002c010060010250340781a002a00c005110f0010f0b54000d00000d080d4142481c0010240c5ca0b50b040d0381c42d00304000e48040e510203c1401307038644000d1074203d0342401c604103c508006d081d82507980d8452140416035078505403814020880000c04030700460381d400c169010b10f006078081d114003401d0901079850344c00030303000140100c0c014014070a0252950040000300410440500d50b000c050312581c181001e141c83d01c49500b10704074040e040c2da18010460401c04038680200b6003505591104903c0e5000c540c592110020030f061042c45001103c083d88841104a00040e0400340c642c2006042001002a40303803a449402c80f42480340701d428141641c40f00450300b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 531145107 1250 531143857 531143891
    0x90c0403050f0319031a370311150c030403030302040608060108070905091b0f0910140a030902150c010c020106091103010e180601140103060b2110080a080c0705030c010909 76
    0x1001e07000b4107c80e0390690001002003a07034491a1400400107292181d0034180380e001e8a014103072a04081164010039181e000c1c411040505808044070800030300425260b02c0b8100014400356110b42d40140c0c4441c07400801804491004d000e5034107021499080240301544200d6500440d082100c2000503600d07406211030080000d00d01902c40e50f0000544d4246003565031008000c03205041e00e80d40c440300d45805007101c0c400ca00f004411411601009070048180c4250046015076000904005080c1101c2c4010040790b4070a0000503c140d4442e201455004e80a1040c40000c0034402ca0078058615800da80c2581d40c801401580340b09407644002c140641402e070b40000520251204071452542c446c07031800d80240110a14a0000303007460004107103450100182c5071071803001e03c3d98001d40003090005171640d403001810358480480184e800100e801c4104076000e60345028841456236242084030b26428800746070000d502035406038a2100e0180d034820034076401c84c3c61000700085c0d41c828a40302445 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 531146357 1250 531145107 531145151
    0x1a090c0a03050a020c1905070b03090d0c0819180503060705040506030901140f0f0c090d0807060f060603060302130506010e13150306020d0506010201060b1602060405090c0403050f031903 82
    0x300b148070381b0f2103d070340c0c0d15003003904000024000c40031500060758605459002d488111a0300c406500304041c0e29924034052005501d91901c540121401d16802041c82404400400c119000080c034801c91641400658524140507000a8010303040c0c0d454500b802070a00d204a01c6035070700845001002803000305080d84440424407064040b0107040c289201c4405445500380c0e0310980010740000414524401c0d1740440340105d1003d4095002c1410a888941d8250400d940c190790280e1940c9400070102c00324813910020b81120b40340003c0480c00e5005000c144081150301c421024503001c00d00c000e580e0031610488400c442202c040390074900004c81c050141031841410505c1292840d07012003001180d4000e0600c0030740031001040b40340e0ba504012400d984851290115801c0200001003200c9440c0d2510100741e800944658a010b41c1d490120300c90800885a4031446000480e05000b0014240228031660000320011420a0703903003540002c8d010b12049201050581d9103410b00c1c02444044080700f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 531147607 1250 531146357 531146377
    0x20a150c0503040e0405160f060c0302010e15011805060612130c08010b100206040b010302040c030e190606052b02010306080a060c0801050d0f120915031a090c0a03050a02 75
    0x9459594484c42c00b02c06900650b0304031443e0203007400c04101d4522101100040304c1c00034500481242c03800c4d000f51428401001c066045540f00c0c0142d08901008000c2100e501624100c5200c0640c0740070b44540c01d800e00c14045031364150400080c040e03140d49040907503100f940320b0403e040e8181c072000300921000e03103210802402d480e1611000106c800e410b60105488000c150345c004c1d01156504400c0740c482d0b01c1240c004040086140060025040590003080c80c0a03140c10000b402581301d80280d0710741007000c1e21564402e02c2420681080040d030780140001032506441c4040b10f45000c0074086040a108011907400c060f140c807010082d68400d07041800105003800c1a1804403025003410380207031103180d5505001c20564400000d1904091600703031a80fa400c481b050034060368550f210a441d0140380311590820560007400305031606600c1c0e101c0348000340e0341c0740080c81c005c03000c0110392401c00428500340f2610b40c40701081a48103a0f0421070300c1e41c0280340341c001065969141c0e0000240104075500b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 531148857 1250 531147607 531147613
    0xc0506010303030621080d2c030405030f03090d1428120e010e010509030f0d02060108011802010905040e070f090e06310f052407020a020a150c05 64
    0x1c2072540590240d01a507150020b025224170140082c00c1d00d82119190050500c4410050808824400c0d88481c200c54503100300ba80c401d800d0418451990341c1880d074600c13042c2d00002010085071400b0401621a041c0f40760107941031900c900006030509006160140200801d1110a80700c001c0912200c6c035014500e80c03000103218030403203a4440d000c446440403241a82580c074050b40c198090402c511003070105946500703c0f070801c3c070011182a004048070750b4140c4030351021150340da0401d0102190044070b0303038000c021541c508200c042c01d6410031030341407200020300301e040030141c2d80c043d81100940e001079601181080044000c0c9140440e164004145030b262141d011074504059040813400d200400100c51917600e54020b00d91080403003040062800542c0c40c6a6030b000c001c030b001540c0c0c0d050702a001000103111a6100c80342480e40c201101000f00c2102c00428101620005080780c02640c40c0c4001c01541c1c001703a011859405141c00b4003020703010807015607408030781329560f00c20741303184d0000c19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 531150107 1250 531148857 531148859
    0x80606010c0f0818120610061407080a020c0310090c03080f270109210f020a0902070b2d0c030916030506010e1308040603050a0209040c092405090906010c050601 71
    0x403420b110010801c5051050720021028504800002810380c0950861404189410300d083d101b60342119803030340e00f25200d5270140851000301381c860003c0c0c0440140394000d010740c05003e404041c144505680345001062030701000344041f441c0324a030201520ba00c50401503035030705208026025800303000e14050250110400c452100c00aa486941c4030b0442070f21880c480a4981500501c0481403455951903d02c0090480780411350a42c004004240041c1200c101d160325118800c050342e01c011001d4030f102e2040c005214001000e807000d11100109481221407140041050b041d00140c0540b454004010202c081400d240041c8443c030365071490a0700c581d408958a00d851a04d503c0c09124a0303040320b04c82d0380021080c0000d00f24414500360b22060544c07034103082c00010350081038007402400f0407541c01d102c02c407183e840d18860582c0d03004280d01c130500540d140803001c2003d440c10b1894020301e000c000c81c4140039030b03802900340d9201080c112034900d0700b50303035440040310900a84403000e0064403c40d80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 531151357 1250 531150107 531150127
    0x40e0705180d0f051e06150d12030902130608060a091e050a050708030a170a060302090a050f0919060e2113060c03050304030c020409020907170907080606010c0f08 72
    0x70f0508460700c103405071070144400c5006082c540200c1461000035030440c00000b180c070084002da000c01040b000301405410001c9403201d0300b41c141b8a001030800720350344402d0380081d440d001217481c030401001c0d0410300c1014144103d0390341304c00780905424641601c40450104014100000150032080840c4400c54200345080241d03880c82010415111801410804180e03410044104c44554a144d11281c001d050b100d2100244030070024248445196112004801131752103400040c05080f100d2004901d50500e2411041c2054018100c05100da00800b80c03414010070071103c88000c640c000307000140307000401c401c203418109040003850b12aa1a00e00c5246600240350240058140680850000e9500c840301075034400690303003000d404510140f001038001f0748220080380100d84050404146109940d000c2a2100025200303030780460220b07440d076040120323f00c050680c00b00f0408000c2440070701c0c1c14041611407201814040c100000902d0100600511398801d00d180c651110b101c603a21140b000f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 531152607 1250 531151357 531151373
    0x1e03082a01020a0f1205070804120905090a23060f06090d0f2102030c030f0c010f060305030301061206030c09090305070b070804020906061e130f080d1103040e0705180d 74
    0x5411813012074000700d0008007070180c0b84121442042c02c0e4882c9000b5443d41e4440304801080c080079841080358901c0f01113041d80b502040b960107400e15071401701d4000300c405030400721041c130540c00150144682e001c0000641c0c400140e002c0400042c0c0d48240e43e0154800032461b080241013024190f00d4021500a0800070321003044083c040d51841c500c3d054007081001280c680c400d00c22340c0f20b401d40c028018921140500300c020002d0f0b807400310000a03103c400c0680c9101b550200e41c0103036059000403004110f816040580500c2468210f04200852401c540d00c005800340c150090103a50382d50303080c480b0205802003003101e202ca60002a00c10700c41c680248020202d1000b102d0890140310440042003050811030143d40400041481e0031240003658080112070341c0040950403030b044045840010401d5004640102501020f400341040b050030b5600540503010040030084158400c02c01002000506842b49810200c0c600c2c006680d250100198240056082ca41e15803040c020070903401006022 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 531153857 1250 531152607 531152627
    0xc020a170d0b060c101802102718020a090302090a09050c060c0d110c0a0f050907091802092b0308090d020a0201081e010e011e03082a01020a 62
    0x107400248441d1801c00c00703101040c0a10243c0c014513601000c0e8400d02c02901341c1220340b1003007481c101c1421600403a00001c0000a00c031185801084075444041e02035100303429814884402e036400e42034a5031a0990f15540c0401d405800d8040941c0403500c100780394840e170f076075500950700140112106e0a200703402c18001d000c0040b0480f180d2188500c0c4005508100c01034410400700742000e003400200240341a50180755041c050045806102c0c0590322583e12500700380e010300002441051114102002d002a603500a402d0300d0038450300e040200304811000044040c8080e010350050784031081300001c01c0741d54a107281441007c80b00045030700c40c40e10880c448a40c1450295a9140d804c1c1c03900c4840946410030903c2c06401a000030114402550140c2c51168024805180c10f81e482851030b40708103d80d1600303070441c801c10b00e07051004104c0d100f1502075401c1c0070a020500004147e01d1682d58015603c5294000200140d01c0e81310400c0c90800701e900704c5901d0001c1c6c4025580c1c2c4e8039000005101d0418 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 531155107 1250 531153857 531153877
    0x10b0a080709061707030902150a0201060503032803020d11070201021614010507030c06061e080114060906060c010f02040911030c0301060c0503130b03041719030c020a17 75
    0x4550001401c86100b280188120340c82d6854102001031451480301c01164003c0401080c55281c00307c0100603201d1003c09101128071190181d150a8814802070a45d4610b600041c400e0340700303001e0000c4181000007a40b510b00b07224033310b5180040080c201540607000e00311200105915141c810010303807000314028500307603100341c2c00d4481c51401403410744221407413402222294180489000080c4d409440144140c0c0c2c020704000307620010f01d40ea441c1c16506140c010703000711083c6506c0c0445a1418880d001c01801d42e103002808003a180740504100074030020045803081c0c3c05480031854507140d040c22980000c0b0054001d10000c204415401c02a6110307208049005d0310f081e01001d1012400026240a066441d000615507440d141088541d40e11001003a5a42e000411105642c45a0710103103034018840002c610b521ba281c54100140c2d0710a408034418040c0f0020071900c10348041d91075001c0020491400d000031102d10205003246048040b01004192100c81d01c00e03003c00a160b9405400d21641c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 531156357 1250 531155107 531155117
    0x102040617190f0207061a03154605060f060a0206040f020f09070906030b0105070f0b0c0d0204060c1506320d0b100504050601230c0303010b0a 63
    0xc2032a00070a100d080c110740301c50a0354a500310020301c91071182c03c01260407000c90300260601c4100c0e12550300326071101090001d0006102000c1c100340c1014000c01074801c120000384074862804500080d05e0318080150020040001502440000800d581d4144142d024141a4090540141c2c1c942c4c0101403d884051003020204074401c41803030480103c1d00b006030980e01a28664855503140039242800b2401242e21400745409642d01da1a086c203210303c1001680e45907148145054400303811600c0303074100141080340410400003c220409c08071440740786d0001c200307203842da16030003090348a0140800302c0d00180d0000400043d0641d0003103007409000e024045840741620540210411170b01d580c800d201d070312191040c11303203103030b074034060001c84003d52600300105400e00400014084581e0030004803412041441407010403a091508c0d040909400d031010000c42c1040300002e40703110f200103814500150303001d07004030750400164241c5181520903400ca988a58540f203180301a0741002c03000700c000070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 531157607 1250 531156357 531156377
    0x20703020c1c0b0604060b07120f08100e041b1d090d2003040e0a090605090c0f060a090302040c05030f070e0d02041a0907050d0b120c061e070501020406 67
    0x3140c4001c00e011500b00094000d035866500740d80b0241c1011005040a80c040d5580d00005800391000d8000c1140a200f031281050004020a0181c0f8899401c103d00d42001a868200100710082003400007d58007080039402c501c2d42c8034501726180060101d004500d00d0001140000ca450707010350003006200008508256079a03c040c50250b07200c201c0f00f040b40000d2514400b03540c40d00c503000c010202040c600b40559141c2509e43e032012040e42404d941001c006581d650071001440040c0c480c29030070200403000b40020030000700020300500400309007176104031000201c0b80100c60081c40c0a10080d0b5014005000520035010f016000c0d03001254401341940440c0001550340d8800c8513002001840100310840c0420b01d50240401400000300c0c52004000f641e850030740d540e43d4144010311503500c6070340b0556a9508501000241e900703055041e805002d030170b020504140e01c08140c100e80c0303507004d5407203035103401118442c1c40314004000c107001d40000740081c00c00140041900104291807943e02c84800607 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 531158857 1250 531157607 531157609
    0x12020d0f05061911030112020a030f0503030708091506220e01050601020c0901030f330609060b131a16050d090609180f110c0a110105070206041a0715020703020c 71
    0x2e2a1201c8921103e80e10801c0107121200901050031f050f00d0010701450005038984ea2640b848407505c90060314140c0c00031007000b100590121101d94411b03003100282481d030154000001c504900503046034405c03550003000440805030b183c1025845a0113510503c200d10100703034018000c003015141e00d401405903c041800c40d084c44075510f4100c951080581c0185000c54035401d050300009141301144050050903a20010345807200d800416040840c0040c950b8a08042c450849105074020b04117100c1c14004030080c0c0000c1044101211008d500803070b0701003850800d04029106282c007906119603048191030070b1180000c4d9800c11014180c5448900544442d001c0e44c0d01c2e00c0d039101d07950220416040d00741e0858016005100d0003000080045500b8201e606201c28a400203c141c101c1503100c5101c00307042c403040c02a1416046001e00b007403071400c81c0c1c1e1f40200301b00307204074002c0d0082d08440c0180c440500c0440030071242415084080111680f822889040282d404000103400620904220000e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 531160107 1250 531158857 531158861
    0x6040f1e1d1b040b2805032a04020403061518020316030911030607020a02090a1a1e040c090503010e0f0c01030b18090610080d02030412020d0f050619 66
    0x1070700012030040030504501c060072000c44180c50321058020341c0343c1062002603201d003408014541035901071190f090212100004241c07010351700c42c1e8820b510080c4122403000d44990080f81d000c81c08a43d90700004018000308010b0b10466000800e0980303800c229500d19010302202c102904d0090312680740d4001c4d0500c00e9000d900069520094880b00c032266000064041d0344142c89141c824010f5a91002802001030b0038000129003560158220f60960340440c034040d40156401100f02c80300f04070100440050040799841d01407803a020781458603119800d9400c0c105501c418041c01441486131510012000f0205d099911960703000b03600b400d010792152403002c03c0c04414000c0844c0100034003d85507004401500305000c4050304101e0507500c00520b0345103081e0184c800d81c61403004041380d0610740704482e224411580103e815411280407a21300301d501004540c100c41c0c010f00c505206c01c12900008900d50b22600380202000412941901040f8000c6400c500c68504000d0b018001d201852941007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 531161357 1250 531160107 531160151
    0x60c0b06060a11010c030204090b030f0a020f01050d0e010b010e01030203060310050a0e0601030f0302160e011e0b0304060e070812040b03041406070c0b01050609011706040f1e 77
    0x800520a40005015400c00e03002600032403040d490701d4003a151001210354212201442d402d00060780000c0c0500ca5104d190007212003a110540003080200e19090a4648070749800400a200b0030340c8540c10404d40c0e2042050302e11900004404010f180c0d410101c0900a20021b18114049199885152001d600900c02c2e603108250103806840c842d00444c00c4103005290042040584a594882c100c40080b41044070310b010f0361043c0028944101c00d405d020b8542002d01031031500c0c001d150541400740e04200c0a0550440b0302c034a86220140b0140c01c0404080c640607044411006d00220421062107001e0304010852801c54094480543c0c4510307600e03072903200d228001132050004000820951001b00003d50740b11b400b0b0303102c010b841d102d003044290401e10240e410f000001c001c8940102801003050301180102804c0343c01c6881c0c03002c800006040501e640700c0d0300b58040c0ca0320000808c5615542c006101078180742c0d8042040d044010400c0600d50072128560b440107140040f1221064031400e030000f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 531162607 1250 531161357 531161363
    0x70c060e011b11090c040b040b27010c0308060d060e100c0207080d0c140a032003030708160908060a02041806050f0d2d0203060604050402090a0c0504170115060c 71
    0x20245881c3c06041c070980c01e501610b40140f07003008200010b01280117101400151a201954076130392000e03002c4100d505414482c3c40e5020000d000d201d01e450303030380100006050035414288004c8541d6200300080c80341041c40000390409081c900c0c00da003400e43c0030034002d40f000e001c1c003002c00c01d56044c0364003240e0326002c0c0c0c00740e60259409480c504460038025020305070b01a04c590300c2c00098401e0548441d080096144044001c25411469004011004003c49046600c0c1c40002d43c21442c1ca488002d1500340d01804004510071094402c40d466407041e003002c0090821241100e4040c281342210b0700c001d501c58402c407288034116013008200ca18050081004071480202240c00a1640c030702084103a40b1011801c5070000ca50301c01845100c40480441c00d0b502c08000e186004540c11801894180724008110761b200e107141c6020400165141300c01103070803045450000a504c481890140d815100d180c0110384203507000315408041701b105401c840300c454241298a04015524101994030820000d401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 531163857 1250 531162607 531162623
    0x11150d050a0b24040f060305091c021002030408160302031b070302102012121609030b06061b07091508070306050a02160f02040b0607051e0102070c060e011b 69
    0xc44110070f2004100c0c20441512002c00349030580d02e45c880200c01910358400c40c0400e172684204411518140280702d070504104e4228411100d0780300c4000c3d190306448030802d00d483e60100115041c042c0c540c05503242c0100004410703240311440d0034060340e00d4000c1802507100142882c20317180e404001003a848102da40c05003002041c106c201c5401d68003410407000202000541d40000100103004101c2148180c80c6201040e54900b07142c0c0c2c410298490050030203044d1103644082041a43d8041c400303e00b20b035040f01e0075a420b52100300000d400340c400c0ca400f440700000c1480c8500d110900214120080310800d0508001d446018601c07110100c460384a444101e41082ca8100081040c503008198407a000480051528099002543c070315401203209131250f045041030801181024401d0460300b560840d00b07a41042c82958030141e80d180c40c2d450140180d01c0d01404400107090035019515003980c06101c00d51003948402c40101264282c0403010b000550091084d482c91401c031494251003500140d00e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 531165107 1250 531163857 531163879
    0x9031507031419140c0313030504051302040e0702070803030f040203010b0904030804032307081c2f090913020109030b1f1703041211150d050a0b 64
    0x2540004210061012090588605403101c807000e00301070310303842040000100706490841d03149003003c131510700030f0024040030000148803d800504c3e00381c951081107075181c607225240c0c0303140848560049034485508590780c02c0040c28204803d40242c41919109078400d289507444020890340d444007841138001e50b400400c0400c40c00c1440c000c415520bd40058000f00359446200007041c89640e00310b5050300040e002d603062004041c0d1200300d160f096903441103100800b40240d43c050300b0a20ae01c0e03000404100c4001100005e0903492004002ea110700f04400308a45640c4200803002940199180080441c1d1000b40c1e0904000400a49003000d0016040d03602540d540c2402440320840b00d0380030307030501103200000000102d07101007040c4201c0c0c1800c5098030f500035800c203500d180b6445810200039400c0060b00d001c0c074840008140da00320b4880044c2811042a04e05100184074903049580350006c41d540c000c0800308411500505032042c045900700300c141d030b6514001040b241000354442d8006600c0f85 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 531166357 1250 531165107 531165133
    0x603030807110304180903110705101d1216060c0c0b03070203121f0602030c060705090d17030f07031e05070e0d0501060515030408090d082115060903 66
    0xb111a19800b140c0040b00d1803d0707100d450000079080000fa403600b00c2c1740c070f421890301003603804075084a400c46801c0040c00360900b45400586a40004a107080130881500440c1e113607005070f40c846145102003e085044800154460561590400c501601d011a10200c00040c1a4072404880740f803503402409141605003031840c0c01b807459002402c0302c030845c8030502c800c600b1512000421400380c40c40341d4001c6c41001c0403560480d0410015403007581990400e0103080310000010801070390121140c649199544400400034210b1016050302410398402a00c0ea41d414000c55002540904200c141c031800300d6a07400000c8003034466450000704602202100b5002030612504007540290050811400b466007580114000251603030094800b07a440386020419420245070309103081c41010207061942c40c0549824500744680b5141e240512600e03804082400307c12000c0c1c1f01d4031700c00c01034141c030344400d451001094201c050310b200b04040d140046481e52842c0c600112442140e010f0050400508004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 531167607 1250 531166357 531166367
    0x1a03070507020f1305040507120818011107030308010918020f010804020f0d08040326030f04032006070f020102180f060c01090b0a0c030b0f12150a09020111010603030807 75
    0x10300100d0308081c940c00040700c9136562078600c01201240c060300042e10310701820300c10300d4111968002051104c500e003c00b000b080c100d0088401d108491005813040c803040b000100c90204150301001081d0003015408400c05603c000514121842050306000c04000c01c2400075907040034000080d8030290704000014654005d0741c00d030740c0c0140000c20316410004142d0100d0400c640442c0103d8444800240510401402c003225100690203941948114002044140c5540c40080c0541c44c90a803000002005c2520440600c00c03140420340000c2050f4581c6202559600c60540d030200120340c50603e02002070380f0520a4520412000025140c20880c550610142d246540c04139900b080c0f08101c407000315202401410101403240100d13152034905500307060201e42110780810201410142d00e100651381d030340c6a0702c5d01d001c4100c48406044c2c40207280301d85400508480c006101c040c140070010541c28030303400745a2490003a01c0340d19805104032605402c8405501005000c500140b0110744840c1c0f10b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 531168857 1250 531167607 531167617
    0x40302070806090703030206010f1d10050303070606061d10050903010905030c060907090605060405010818150108100905070b25060614060a350f101a030705 69
    0x90054616007a2a108001d08000c0304640302141d962081d0340030010103a0420000380181076010201000380d0401e003210072042400040b01800f0f6010001048070052142807950041c00000d0850359580030b42e142c00005007800d8410742c4d01082030b02d8598070428a010345240c042d0000100f5220140451004c10303a12a0807209030306416641e61100680042e4040004004180100004100c20326051040da464414281c00aa80180c1083e00800064450360141c0d802e56800f424281c03d142d540600c0f864a541c0480d842224910660002c1c288110720105402d060380c1403482512903241003000204191403290f000113106074440030301004801a0000580800c80300b410820700705001007001e401c04132010703e2095941d40c2c1d40e00e07000c00c8600d101e03000748801c50300169502414001004c0b00502901994005024042001d00302d5032902c2c4d100c0a4403010106020f42c8a0345203040c905800708200c0d6088581003c4a1301700740e40410b040d6503414901c21840c0c00d44441c5443c52f500c84c002280d081e040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 531170107 1250 531168857 531168863
    0x5090d060f150306050414031303060c0302160f11191e1d0108060a0902010e040903210617010203010321090f0801090c0b0f0409051504090f03030c08160804 69
    0x1940440c8028000204032000083d40a81000314003810306042a00f100c040d400514010b5a00c200040c1c000c0c80701903020001100e0308858000f400350113607042540039124a560100e42c0443c20b182500c10030190010141465000e800341c1a645203100c001d200c1c0143c1c0d5a0a1103140142e034101c100203210f010620212003901c150200904255240c001006100c80300081d206500d003890014070802c40b0400c505607010345500d400303000610680c0c0002c0c0200814400c454001da499100d0001418000e20940e9400851449007480040a14004d800105024050310b00110052040c0403081401402540c3c1625002010111100c0d40c88581194050503640e006050003e01140001c54481e00d8000c41e0040c000c1a00100300703200b0b51b01c0d0214000010ba00f02c0d80400300140012200c49109030143d605442d403c02000909403250881d030003440100c4000a0791040c02d103440001006601d0070003058041c0719443c03c0c046503015800a940311113040702c1d84414009031800c0001c1c038503c586007250704180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 531171357 1250 531170107 531170111
    0x4031103030c0a0308090c090402011403060111120702210d050705120d050610090602071205010e010e010b01110705060307030903030e0106080c010f081b090315070c0605060105090d060f 82
    0x100e0401c9a0381030103080301c1c3c03e601080c40341080094003802032140480d18841118880038034609540041e0003071031404e082d100c68120108c002910360740150041052000884115401100e64403040d80042d070010310200c0c02602848080c0303032110645003141c507010690002411a004400c1c3c400c03609500700d842c0954061103445441f102d0305540d44c0c01020348281450010405140550901401d00d00b611011020010011400c00070690301141c0b00003980e19038072203405072403050708065016080d044102c18855103030040e07181041c01e055200c02d0318942c00380c84070401c80800c902003646030390091190f960090020000200da00c1c2c03083e4000680c60f40b0030300f030000b20b217282a030f03015084502c00d8002c0c540325840703c8003940d100e68000d01044941029072078003580038a05004204c0702c1d41381c00c6640001003074000c2072482141d40c6c00c1c01561401240900010014a071104005008c5c811508042d20381c9454100407810b035520404c116011501c01529400780640990303500b0009008074248812501d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 531172607 1250 531171357 531171367
    0x51008062401140c060a0614210a0203030c060121080d09030908031801030e0c0d0f0201050714010213090204080c09060402191107050102070f03030f02121b061005060403110303 78
    0x4600142810324a01c44c002e16051606142d813108a60007a0042d6484848583c85403200c0e6641000071403030803040f82415204581c181112500e044140072009506000c04240708010038030009015048501010b400b020303401c002030031190740005100025201d010104007410a80003150412816184245010818240c0e07a5503070905542002a441d80442c1c041900700041d0741e4140103440882420790040c00000c0743ca000000e02e400b421b40e00003403440581c200318000b0b5a005a05442d9055000020700c180840e98400382c50007944490345d030580040c131a80340070810381594070030385040c5c4030400001c1c10081100010004001d80c000d2a04d035116800300076a12400c4503200900107807060310307140c100083d100680010704000c00c7d50411811503101e030000b001031b41500f0345581d04032078040c2808500742003d080c04908250032941c003082100b0000130056490080b115003e00509442020b4030140c1d11010b6164680320000e2082da90f1004042c8020300200d001c030071002411060080072a4505 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 531173857 1250 531172607 531172637
    0x302130f0b0a14090d03110a0c0e0106021c141c0f1e050c07080c03090406030f05060a0509030a11010b0a0e061e010c1203090213051008062401 63
    0x40351a001912000008a100095070360803035a05200c2d83c41a4107218285001500402d140012004010341008415540001e07603c070244103040702c15401060780911a5124009010f28030b4083c800c1000505c00c4414460701080248517201d8081202d03a01c8070200a200f0261031010b8000270700d400703d1030443c1408844998418030610100d88a403200110b110b0200803590390350310000c0095080e13014241700030481d40c200032400300e9508640c88117480b41c031150820001c030b00c1c60280c04505074105251010100900c001485e52040040c800ea045803010358a9404400545509032184405030f0b2080c0443e060b0680907a00e40f40d0fa03400700348000500003042d0343c0000d01401c0c0702e90007500110400c1092200030700f005a0323940300c0d8140c035010b1402c1d80300e0b4040008003041403040c806001190480c060340d88080c440d400c00d001c1d154000700b000b071070442e02601850003418243d541840c1c1100f4204006412003020070a03c1c03054000c040003409200100e070721031052648048880b8108800d60320320030300c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 531175107 1250 531173857 531173879
    0x60b0111101b02011503060510082409010c17070309050601090209010f05030c09040510120b1f0501023c0a05071409190e0a05010f1103070f030213 65
    0x21541c40c10003088440c0800360044998840c1d018490459040880c01103a40c1030320700620045a03441200004c6d81e56445400101d00e0007035420a0b0214010190b4070940c01113041d5110320304c600c04c40e50700d501a440318150142200e101c41c8040000c142d0040740c5600841c44445800d074401c1d114240031441110756500c9078100751090f000100300a44c003040d01c0405581c8000c038280f88403100e0a10610f54100384040050502403000c0d110b10880d15440018844114009050018401540b030060309465510f00309402e04c2e02203c40e641c4902d40304004004040c5141100f00c12110103030003030100511204401915881d024244c1000107061071174505c50401003850040f2018142c0c2c1c084c14101d000c5240c0f807420704206501a0003035200c40740042e40d00d560384c1215030313401a4243e0700e143d16520402d045038018149a8090710140d00441c80714409000f13040d0003196001a42c5401017040704101121240d02c0d0000361221000210680940840360340642d0042500218070038545074000c1e40c032000c02c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 531176357 1250 531175107 531175123
    0x10c15090b2e0e041b0e07030e0318090a02070507031407081c05090a09050a0603170c0303130c030203191e2013050901050702150c0403060b0111 64
    0x15000032000200150010010302d40080e6a4504100d4081c02da0280b054040302c290b24020907120f008007902060400115140341e5030300a9840541c107040c1c641d1007408000800003210000c011900b0180404000c0d00088102c80da401d800c041a8008000030006004c075500c001412191056820041280030460802c64600218401e208072071044003410216424140e4039031012210f0b600181007404040c001c1c02c45120145040e00e056a1a045410001641c0e05140d600180b0307141e14040601c0700440355500b200c1c05880c01100f01d1704803841e01c22410b660034800c4103200c01c1c45400500200f4442840c01210b00c0c0d2043c05000000c090350b4480e00000d081559001c1ca20b04d96501c5100f11104100403c1b403025290082560080311802043d200e00d00c00861800001c080c4294800030404141e0700c2110703137102c175058140200403914007041c0c068005e01c0242c0c2c03140054822114140ea64421074002c140c07042c50284035190500307103142e0b5450040c1c8140e00c2e6150500c040981441807180003000140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 531177607 1250 531176357 531176363
    0xf0f060d0c09020a031e06080f0703030806010e060d050903090f01050f0301061413060c020a09231801020c0d170403091a04050405190b011107030b070203040f090e070b1602010c1509 80
    0x80c07403823030146407e00e4100110703064881c1382c01c00002080801c0d002040e065001c0c2003802d1545462011000259052007422498035142c3c0c03800042c00a0960000041e060000c001c0d24080b182c442c29038010740e080e016071182c00e200ca210070001440003070f01c1410413410700354050390014102800102c56100034140c44d000400060143d1080c1c206500c0c040d0700e0240148038000003004982074605c40700080e01c840201038000315082c100422003c1c100c003034201030500d0100d8000c544503050f00501139143c500302a501400505041c842903c44001030300401c0c0100c0d0325848001c00986442c1d02003151303440760390309020f480105010000d010b4442d40903c5102d140f200c4a1f58000000c2004514100d41c0306030300d218104004444120342c2c8640019401e416a034001000072800e80d02c18108902c1e501c0b958102c1840034484000020f103600c01600450000000d0300c1c107507030185482c0c1220031a240101081840d208114110f00d80255002e056881541405007400034207017035210881d5000e54810850072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 531178857 1250 531177607 531177611
    0x610180926030712020711010f02031b0f0d020102090a060f020313260303070e09101e080c0105180d02041d0705090c030f0123090f0f060d0c09020a031e 67
    0x10303c482c0e00811605500181c1c800450801c86d1503140c0580170702a0321025070510042556011070b02d4020419154440c3c10014a91656031006400704c1d01c030550b500c0030b103001e8840c40450010140c018020b4464030100940160341c540c0c42e1001c102c4061500700b0000c801c0d0700081220219101110280c0c41c0500501e4240580d00440301405800c0d00b00705d8098104550030a00c00c0c020a654440c0c0c8188480320120b0b049181a212156005803130b81d202e40c09840c0d03103c1940c002807a00d00080958000f2160103c00b40d03858a0320900055540d03100780050b41469029101480b503003032420b141d00004250024000107080e500301445800c0c411300460807080b040d440741404020b54a800441158442e01810410341907051240003907040034018001c108440c20380030078407490b0b0030704a031a2000d4444c1c0100850311900303050010100c50b040945400c40d8035840480014414100b20309015120307540318400c0101645000c1c540c0c4000c0d0410b10f00364003015161100394848510340006045001e00b44400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 531180107 1250 531178857 531178861
    0x60d020d0f061b1e08010302090c0d0f090b060307060305010e0402040507030b0a090e011815020a0527090603150a020903070f0b03010501030605181303140c0d02061018092603 77
    0x35141d1348041d48000320041005017801880180c680c4086160044c59100030f0035140c1c401909150301604100b80304c1d00300d007803414080d074060101070b090080c02040c09900b5102c0d16520350700d046040d01c4c024080c1c6104880340d6004607005003025841103038000001c1c6800103a8072408000181d01e20841c0d4030115819840b4021079090550078410701c031000860011400010181d9640c0b5003884d0040c00365031201d5a8003142e00140940101c013100e03000e144070400550710f64540c0164807014907030b002046015803032200019125060008406c036410160f075800d014580e440c0100f07007000e0341c1320300000c64160042c1c45002400c540e010040b04094039183c09078940382d40c10071000500315003155218901c03c400d60100103001002118150350056800c50b51004208403e081c1034640c10000c0750240007100c0001600118840040b0712000310243e1942074590036140e10b10b2412886440c0e00a182d80a01507102e516640109a44103a10041c492807000700181141101000000c2e15040600100640042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 531181357 1250 531180107 531180137
    0xd080706240902040e04080d110d1a1203191110060914010f090b06091c032c0423070906021c080a021608031e060d020d0f061b 56
    0x9101c040d0888800031402e1910380300340b8406504e8080c0c0b01500c514030000e4401003942ea10341040220b4100603568a40d1034403040b404e500141255008200a55021000c451440c904030810781260301c0e80400079800c2400040080f2802290613400c4401e01450b0b85221801e0142030007521000020401c001a00d14508200c1c001500c01d1141d0f898400030b2640014005024400c0ea2101682c40404001840f85030050110302c040c45420000750b40304500d0030320568541d03403a030a1181000e11036501d0329200400e11164446d0310569000c01c8003860452000c0465a040540c8001c1e0b44841200440c0c00d501822080152248015190240020008030f414400b0b42c0c0c0400001800b1a440e42c0c450000042c103600003050000080c000c05007040c0c0000725001040b488800d002c8502c1d4004006941e2800c00304110b44000c00040c102e00c0e810360000d000151285017100d00a02c00c1d54014048025207089a6280480d02c1c0c41030000300e5400703641c0d26041c0541c402402c0c80501b11000c6455210500810340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 531182607 1250 531181357 531181421
    0x115090905100e0a140a0b030c0f091803040b0c0d080106050405010804060b0d0c1509050f030c040c020a08030f040311030c1203060a090212072c0d080706 68
    0x18000c0c0c0340590800d001d10040380040011502191014841440183c90f2410050064000b110700742003200911018441c0740d03145a4014140c2120440c00c8038003003441c17207003841140a5604886a40b002024001070380d00d00440d01303404681c01c030300301c152490319440d480302a03456002088401c0c032940c403603180c0c1030849402802041c0509180d040c454106490040002c2620500800080005417205068515a11142c40140c1416440441068056150b0360307101640c4001c0c405100003c0c08110b80003a0f14180a0302c00c0441400140c041d000309054082170102801000811100310310840d0340c44800300e042e040145024500981c00240d450416040092103040b0310048603195800c100401194020001070419030040c0901580d5160f03610380e0002550100598007540310b20740005030182207035800035101ca10420007a1103036100003100710200072f01c10f04400d80201507800c1302d1100c0d520303074541086014030300c0303124500c0c00d882d1000b42d982e40b000f40c1e403083d070301030028814a0451108030100c40b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 531183857 1250 531182607 531182609
    0x3011a030d080420010c0206030a0c14040320030a15290102030304021e0402040303020f0111090102030d0f1d030d05160c03050906040902030907090b030705010807120605030105011509 81
    0x285442e51550500d6110010f42121840c0c090840c4000000c13805a26401041c4e02e00d80d06400818280e02c81c1b9081da00c1030040d10704019002c001407094000700c0c500b91480c00544059982240408810080344420100c461109100055061040d00314040000c2d4480e003500c0c22444184002150b4803569040710016411540c08d02c106071000e10070441d40b5640d0000c2a2644103404941074000c0c20041001c0b45071806090880c1ca0f0040d00000700882419000169980b4204a100081019100103144444680140074086005030020843c2034000461500481d85c50040c20710001000ca50003020341070318482101400c42141c0020070400310300b8600340b0589600220301c030103015069054440c001e1052045100003003c2c0035020442c0301312911988143d9028154500086640f414504605583c405451240d0410941819208016814045000c0c82100c03410f031200c1071151102c4070107917101c0010030300c1c00c250b860351684000b80c5540c1c00d01031070b4020900d0449105112504110042c020703801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 531185107 1250 531183857 531183883
    0x405030711240d0b040e0c01021209180907050406150206100f05061c060f260309040209030a020409060f15031505091c02070f0602010e0c130b03011a03 67
    0x2040c030702c0780600381c140c0d02d00d121000c041e00d140036a5603054900b1080101a001003207a04545010b400c0307805004001402c5180c42001d80880f544500020841d45030b07440707808080f64211224030500122980042100741d0002c070004180c85400f0380b250085021107844e42c1c011800c084c2c0a00011510307036010703c05290010303d451079480950703040c03c0c024101c074001072181502501c00010200b81c09402003400d801800310405d414851070340c2d60098103411103047c0c000c10031034081c1803a18900340c090a62050000840e103074091800e0aa8041c2000000e41180e0b10850305070003114007aa006a03640d1188022141c41201c00292600000103d007040300c0f185c2c984000b0700301400302d060000c6801d5a030042d01c1e0642c045004100c0703039502c00c905420900300c40e50242c403440c0c0308012815100e4001c02d809050b18401490342c0c02c8580d482c54124260380031446c04d52400d03003205101d4409410074007600c420f142c102d81c0000c1001d000640109084032a040301103211140c80710703c0115140340c00d000151880003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 531186357 1250 531185107 531185119
    0x12010506090a03030e060f030c0703031d060a0902010507060e1c03060302240c07170606061204030f210f0b0405040206030703020309070504050f0405010e0d0e0d1a0405030711 77
    0x78401284220055000c090300344248640051140d81e200c204440340301c500300034031644074100101c00700700e01c0d00810003c0f070100741403e5018514908500d044404004c0503802001903484800d0307550000c0c0118242079041150400440012503950300641d90072003203c900400c0d1a00f105000918401071189880d020103092450800140e61441914945c075404803405400c2c018030800100c00354803844910b0034041c025410006451655029508140c69204069039004d80d80c580800002d0300c5107090543c0c000b100d00c004900864401d90742c4460003a1a818034101c2c03c0081b000f80380452076207000205070b040c0c40e645c803030b000582e450080307045220050301c09000c142015800114075000080200d010154080700107087e0f50b0341000b0740001480003a00801441c00c1400c03412281603000c40d8152803d6007004100305541c500000c2038101001560303200d4440612840030011608900034080d124003202c00703031200c0c140e00c3c440e59060080384034000840e900c9250340b41c0301116403016810303180720300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 531187607 1250 531186357 531186367
    0x3040317070207172104030c0b0415030207110303040f061e020309090a150e0a0e060c1905040302031603031805090106050c01091a060f06070816030207081212010506 73
    0x50b00019000c0503628a13540e91481144071451031440c01045121051400c4e0312249404001150b0720300400580780144800c0f41400c0e201c0c00080b000d84141d1007211907079070000d00f0303815204c0c5c8280d0103806c07280d200e40004040c07a0407100029195401070b802c0700d800f480c594481001b01c40d4100c003010000001002d017102002c5c1f460000a501d9000d0b105415000f0210440068015521036024094850300b1108002045403180040f03156007000310360480c0018903001080b40004400515180300703e100301314a502d0408284080005004400741c840c2c1803041c103010200042e03400303200424404c2201c803684040d451650070014112500ca803d144410191a4000d0109071940340d0344a0542d1030605220355910070001c0e0b0300d80106603115000c4c203039840d500058069200c04a000500807181180c0000c5421031180c00c1200b2841100f40c01032074910100400003010b0b040a4004544a00a005447c03045a0b20099607040c00c8511100a803900c2001420003086001c122a5502408041d95018109 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 531188857 1250 531187607 531187621
    0x5040203070e061c03080703380d020402070503032d01260d0207050a060f08041e1205120703060506070b0405160b090922060e03070f0803040317 64
    0x1c4403180035009807442080700181c90307030300c032040b1500c208141c480070201c00c4000f50800611016042d40c440300000d041c19940c1c54026200000d64005125409101c1103540004d9a001084604003d000c0c0c1c000341070f074201c100940d8a03803000e03040e02c81c028805981e03245070001c1094403101c1c40300410905450030745642d10354420104455415a41c564070440420344072070030145803e140c2e0607007201d03c0d482091f20084040350302040410846009a42d1420000d0b2522810b40b142c4428408210005a52100041c0410212030200c04030008032280308074150007030744900d04002008000000842c400049640040481c282055031040e80c62a0410540b81001d000440f5807181c554007074450403800011405000007402080710b038a4500c4901c402440c1e030b507404d52004d60030549d41280b045202da000695041a55802000780300c190390b04854400d240c665503000200303a1010608a5444103209501c00510b0021381550400c1c010500f80303807280b0b030030307e4001c003003d46111903650220048002d00502c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 531190107 1250 531188857 531188863
    0x6090f0b030408180303120a090b071d0105161e0c0503010501050609010c060e010c0e180603031c060308040611010e07080613020312040608090601080102070302030702100324090c0305040203 84
    0x3000c8138080d42d4060030080000041d14602507180030401121014003070242241e4a0340c081c03114a4420401c09070f10765120b040c1914040b001150410055030b40071003568141d071140008000032100142008800e04503134542041c580024201942c3c0f240070902c4134004c0c084c0d503c024000411081b002031086604200c089101d900690749084e041c0710451140c00c0400034141c20440801c2d00c0301008000700b0940910003401000d0407500c2c1406086174101880c44200b50603038491107400060000e615000500c1d000803402c0a4580784013088903038500340800003c0d00000184014040c90342c4c0c1000c0b5800072030200e821920340e80c002e03c035943e1000d2401c010b900804152a903104202c00c8002446000301e001081c107058225041c2d2049c2480002c0c040380058010341103d0107001c2d01c5d000c80710780b0380e01c402c034080c01c0b0320402e0301c05000740e802402002c0051815450818103803590349400b10f829280c00d2038074907000040011160046d854814140802443d902c1562a08000307032805100c01d00b81500030a072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 531191357 1250 531190107 531190117
    0x90501060206180a122607120b101803060f0207151406060903030d09061d07081c120c030b010e010201140112020a0b030a0605010e10081f050a06090f0b030408 70
    0x4009511591481040c500920200c11b952010706561103910006200252613102c0c1120f2100c0450386501514080813024451200c20680241001e040c246141d0019500144030144d001039a10500c1d50100006800d0b0003141c29030400042d0142c0c450005203030001040312072058042440c0c0c40e105000e03845d601e0080b451364022806880281d602c0410781c000c82d003503200300820b9a211a051480f14000c006940e803041c05850007610f41ca5030302140941c0e069880c0c070a00e100d01e42c0b44d58011910710102420aa8a0720580410342c04d1021034145101e900000740d40041b841400402daa0311000c401135600412403441d003880920003000383e600d0103c085e000a00c018028100f60381442141c1504644441d6a5100600492145140c0341c1c078240c84000c1c017078011402000d0000d0004010001300c3c3c02c1010000c002618251681c092507603840c04651119105901c12180402803030500080356114100150301070180c9941c1e1034503060070111101c04c40741e515804000f45c010b0410030080450300038170980f1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 531192607 1250 531191357 531191363
    0xf0112120e04020409060e060f030c060a030209042c15071b0218040c030c05042d060312021e06091c0c020406090516031b030b0613090501060206180a 66
    0x5110700d0351070000b10b80240a0707900490541ea103000008191403510f22500c2e44500e0048071b800d04440900020b150b00d0720300040c08160418000d10024141c540a500685103c40010b81300148914013011308201740982d11000c1d9880c00920074082c81c8040e014032001c1520440200101501d0624040040c184c040008000798410494001e4a08540d502c000d540c4681d54107030050113013418203040c070100783c1c0ca191000f00c502290704080098241002e00030102c0901019a00c06000703000200c03a10b60408011242d900760035590100400095950440c014808405500501803c95280300182001d61440c000ca20b455214500b08400c40301c0000300c0250080e04925580b00044110b0b20646400d260518003d43c440d0030070030301240c450303903940c0000d100d001c0342000d600101072814010340840b100801ca410a02a4203110314042d40c0c02508080311505014102c1407810003008020000380c4890b1b00504441604d81004100d0320740d040058940001c3c420340070421851810a2141d0b0700d5101000007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 531193857 1250 531192607 531192617
    0xc030f0f0e0d0804030b181009020310020f0d06080309040b011409010521010602030a030b0405102702070605010503070e1905220c030b07090806010e2203080f011212 73
    0x70410003104405840080d94007034201b04050a00c41105440311905180403541032003282d1340480314800b24041c03000380b5070300640680304922001000c00081e50001040d80c9500300d08001c650140304035803013184020595000507545a410100400007510002c0541604001c0c221b0500070400c1c01040450300c14030f009080c51903170350141d4600b818464501c400c82d210011490400082c1c40c0c0d070040024280c8408943c1c0801c40c3d0314405d020001240c8050b1011f01d22084203003018041090403601c12041000d44001c07401d018623111145000f680e2140c0710442e000d5443e2801001903041c01c0080201401e0200604041ca00c4d00c82075100842042c0d4403e000c0786030301c078804030700c1a000b00400c02c4641c100b01009032440c5005070a011640e5422803000f1540400030000103086903124400700001d0364078810203018030340d103041c4501c440004094040f1080c1c442c00844840f0030b86c0103900100d8201e21a03280d80c0954039180f03908100f255416844031440b2519582480001445d841003c140002d460401f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 531195107 1250 531193857 531193879
    0x1914150f090403050703031506080402011211040306060e0114030607050a0c0c03030c051006050a05011103090a260a03050403140a0804080f07122d020901060c030f0f0e 74
    0x11004840d060016030040d40c0282840181544500181961030094500b842608010710600e1001d041c64410080010312020115005600c1403c42c070b82d0301d80003502d02094420082480e6205a80b082d07104440a560b294020800f12412120b118014004d60860241c0103d1000100f40c80310801400001003080c001840880c29010320452550b05410086040880d03880346009040c010080c0001d6460784a190b12840342d02007a802007500740d65016060f01c0c81d4501c3c020041d07904400b802071017840383c0018001d030940c94030f51410010081c100c910410300440c1e200a0030140b1108400076040543d001041d404000c01d4104003150100c0ba80121084842e42d110314181e800c1510941c0000c1207584000340014950000003003406c140b03446803040d83c29540d61501101c2c50ba540e4004000d04030070b0342d0f240040c400c11310307030510942c0300c141000070650010850340000d03002c0000360001000700780000080f02c1850342c4410b006070324840904007411480d070a441e001d030070880701d07818841c400e009205e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 531196357 1250 531195107 531195109
    0x1603020c15250506040b090606040c020706180e071e050a05040312030b10020c030d05040807032a300f081b010e0c12070b0f130806040506191415 64
    0x280c042c16168105055034054101464001c1080030251080c05241c856180483c000b8502881000200c0304a0f40081010b145000c0741510703001c206c00b00350000b82c0003142c0c000550031948440c2e9480f480d40d0f03035905618901b05041004210303244040300c0c405c100c014007140400c1e942003c1141d09613600180b00582d920f20001045020308080d00d01250400440743c034000b5281c0e00098117a140080803800d4031101011040100e515011300d1081001941c09410108080f039000b0902c0d211300941440c50034600c072804134048507041000c0c0e01c000740403260403281650400c0c030410744002c1107a4080316519400c0c4603031501488200b403808040d280d03100014540090b041081881c10188a0080c024005001001c84a07500d41707034510034190144e0609000ca40d1924404650344082d1103656040c9800d1070a800c61a86080d00080419140e131400510081800c0c442080380611607803054000300305d10f2410310740c0c0c04801032401d4a01010141020004040003140500d210b5004000b01c080c0c070190101d50b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 531197607 1250 531196357 531196417
    0x9010b12130222050a180803060d03092c01052d0301150b130e040302030714160806150f010207030b0a0615051801020303100302120708031603020c15 66
    0x1c00307100c120b41080403c003404803504030501c00d280c0000200403e070305058649401e41308007400180741d86003c00010310345140c402c0740307004640d0080c9040042581c07503050017920410020340c1004c8410000007007429001c155044240508001c0d82e00c15450700c81d1883c1c1d0000482024441c4d0b1520342260802c0c0f140703441c04d40c402060805540591504150780b140c05a110b41e1142101e0004001070a101068170311800c0030b428000c541c1540250700d480c2054644582c140001d8540304014021211810300701c144c001c00e46405440180041c00460070540f0b400300d02c1e802414000ba000c0c5002c00150382150ba000710307603a41140d40081c580d400075561105203400600098101814141c0c0c45512050940e900001400c41c4079608018442c0c0b00c1c2c0c0c07040c0160b999010480d2800c00c54060050148018185080c100c1a104441c00440d50140e840f00c1c042800c0d034001402d0007140c003030082d0280060582c10400c1c03081c590403d80700c010303045041c4245101e05110303c000d0030111400c260041c104441d810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 531198857 1250 531197607 531197629
    0x3030906110f12070b090111123c1312051b030d0506010f090e0a0e0c030a11030706030203010b0910051603120e010c08072f03030609010b121302 64
    0x50016503ca108a826002819820403001921201c1e0807000040e01d5980520175481c0301c0308000855410459003101051000500500d020300003002072503000001c40c2c00f009011104140003500d07000300740c0c1d601d240304400d100c01020109000444c552220119400103101003141c2603d00d0650703620354002003800c002c442c10f81070b036007418400005c103c10717120240d512031801030400741e9600d40d42d01d907201d00c110345107c990300802e8800c460320030220b040f000d8a580300d60000110282034800001100300041e0030119100c206888501e6900c0c241c8603107280c14484d8002802c0903050442c295410401ca6220034040d0054050092018405140000c0d02881c10384402c002e001144410742c55031403030020120f0074603514040d0f085041000b515624107041c091480c82d0031a60341c0ba1411b81e179501108231160200b40c0d0012484c0701c2000e40d200c825003034008103c2c61400b0894011641d81c01c0c450184140708005034070048001c4414407003a40071113a020032240c2c104000190050001c2c01a00000f036000c021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 531200107 1250 531198857 531198883
    0x8090a0c03080a03050f091b01141306020d2604080c070303121a01120b0f030706110c0306060a12030201020f2719030318030206040e04060f060303090611 68
    0x110400001c00c102c103400040511030001d64041c402521010aa244080380590b21403070b5a070804038443c040840e0807460000301c543c0500d080004ca80341c07070000e1040c03a070001c25652012003d04605100d000e4041150080c00186072502ca10340440c1c81a0070f040349070a0680080b95100b40d20b012605102a0300141c90b601c0f0030308025146040c1d5645800f5081d001c4407411500310608007a03c900d54447c01842c0c2d4408410181c64044c8402c03102004080100b0404d699194054021480070078a82c40402c000d0019281588800e0148240c804009207011000034815100f070317000e08200300142d181c98062030200c0300d00d00d40c40527410002c0e24050340640608800030104d00030106a41c100303080b40042020044550080380c1c0201545181800201040392441c0c0c984070f415000c040001901c5520b031140300d5034001c503500040544a41c001550303075101e0b600c014400300b540f60500040c048036124410520345620000c0288504d1a0780141c940700c042e2080750b0600500d0046100501030503c5041c402c108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 531201357 1250 531200107 531200123
    0x50d0b0604061d0901050709030f260a0c05011103060604060809010902040911090609040302030a0c0512030a06030b09030319090302150106090801060801020306030705042304030503220209040308090a 88
    0x950f040c503c2d10f000210741c12801582444003142405004043d1101620703088501e030150704540b80c0741e21020002140a00701ca90769040d82d1000c00314900400b802ca034080030380d0745038000d0559041c10b9003501ca00d9003488244000400600500c2e60302c0f081101c04541460410510696a030102580180843d0101a4201c0d081015607010484d91082c40c0403050001c46000c00c45803110b8081c8881103a084800501580c03041250002d401d019a091010561054003110038042881c2c0300f00f0340541050395802481e40d140c500c1482000704480056a100c26110011411498002d03011501800805841500285c0e181c010301c0c01c1c50f2090011856a00e00308258000650351484010800300483c4600740c010751900801145184060080300d007c2c01004000782003032420001000010315000e528500c1080440086511095040150601c603501907180c1645030324060100c804000044026038403c003501038401c2005a0320300c6800b0790401d0309858000c020b940c883d41c095241046040c006040c40c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 531202607 1250 531201357 531201389
    0x612150501030c180e0a060803070b0105040b0a090608060108120708030406090809060a020a02010206150a0314150112120f020d110304171015032a0e010b090910050d0b060406 77
    0x80070005d4580c061410710000300040e80c1d80700c24003500e0b0b02465400a0403884120010070041c54507070071414429800406181115a49040c0502214103960015501e80c000d007004104010040c801d030f80e01003480d2114545060701560b100340241c07000030070042c041580c0d030b060081800001d80c29140c22040181c0351650300c000f2030390081e50320030b612002240144904400a1a4501c00186172f1080c0030f000b400c480001400c43d43e404140c6080715a04500750322a00201000481c100e4907180c1c000c001d0520044489446420701a4090050800f00014010340035814608650b000441c4130002c420b81c5082c1d51107100c44a0040d00750721481c0c0c80400180c42c1c0c0b00c2080d103c0c0717030040380e181000c10303c6640400007180b00c00e8000204440030b00c809840c07034040c940c002c103801410180315031041c0061001041e069031a0310440640e088280c01410390300034007040a00d075900b8414825504000030707242c6520000d20345000107241070701d0302c00000d049004071000304000745c45503008403000d088002d8041801d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 531203857 1250 531202607 531202619
    0x151e020f0c010e03100f02090a061115071704020a030506010f060813020906060c010e06010b03010303030e0f101d06010b07050601060509010804031d0a0801060612150501030c18 78
    0x14020380c10304121940141d0400200c80c2d80104400000108080c02500c0c4401985216500910402c0c011040d441d808202030b60080e903903003203480c024100c240c640064007035003071403d41d02d004e80d12158000c1b031140032020b0143c1a80c00040d1003c10b01d62182040400c0da8a9201051580c1d43c06e900050151054100100b030107020041400c00341c0f4a1580c030b0040079524034060301140188401c02a400c03817010004a144c0d810304100901e41d610010002080302100368401e03170b2a1100c240c0c04010f0140340400144101903050140d02040d0f4141030062940608000801c0d840e407c1030052141560365400d0309030060b1003038406244845c204001640d0035580d46854640e00e41c0d000103001c4645015620004c21000e000c6c409403503203001d06a40e400100d41d10b80d5402c1d1682d901c040301c1000e21049c001d10111041d42c5a050310f030080d199030000400c04d03c1c9095009400c242e040744030000351070704041c06900440f401001d168100c43d02403070049095800303d60b05541051030202c0b0007035a100d4041d030100c0c2c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 531205107 1250 531203857 531203863
    0x308130f150f18080a081308030403020123450607020c01020d0e011404030204051303110708060402040507230a090b0403080921150103061802010504151e02 69
    0x1500c0c04030b031400c0c41005900ca003140071140c80d0100041c13812100b841449462440703004100c0c3d01c40c0c60124140c40904190b19201c000740c00888080b0010b039102d210038200c00440c04180000600315801c244008d050501161117082d0240050340300c0280c0d4024203460343d0440c2c41c0c908600500801c81d4000c0e000b000d0714600c0e01c81908a444e0300140c400c44000c0c01442d480040e0b003442d01e002d035a4a989045451030b004440451a280010b408014140004005a82c035481001e00400b501e491a4034402800c0c500501344030351124582040f078108600402403540b0119503294080d50407140000d69646010003651240c008070001c1c4040e808408100e1203c064001c014902354503036480740c0aa00356600c66404852042d4000102402d02c03d000001041c203000380600240c092054000e8820114170900074030348045614283c001d00040001042800603500c6080c0c02804803212484209560350006090380c41b50344071b03840340f1018450440381c91502c80e1000790418281e80042d410400712487c00296 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 531206357 1250 531205107 531205121
    0x18060619020609071a040905090a0c06030b0405091f0b12070b03040b0a020a1407051507050d200702060c0708100608060907210201030209040203090105090601060c0308130f15 77
    0x594800d500d404940601e0f83c52003085e0380807402940d40e1800e41011040c1029100c09429200d80f8402e4048030380001d290036401401034811070340d000614011810400c4180c07603019241c901c180d0440c0804002808400c0800149048010070210341f01400001080b00c6080c09042204030740905c446c0410301d0010040217601890054001514039290f510035002240720ba00010004107051240c030040312003e242c09048520300a00070360761b615154144035000d101c0304171172083c0010000181081c0340d03d010310070b800c50501d428101c00e4294000c005a458940704152010340301e00360118210940c544100020000342c0050b00548100d100c07206000707005481701d07019601c01800f039000055070802d0005610710482e40c2d10801546c4c1d103071420705d440707807a468010000da040540070050345d11f0030f4545000031801000d59000005440c0b410100242c10020306070840700802200d2501c0d180800d0f40555030a80041103000498031040c070a14015020903041d800061090001c002d003c25030360b006620001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 531207607 1250 531206357 531206371
    0x9020a1215031a010509010303080702150708091207050d11030f1801030606020f1c030b0613170d090e06010302091801060306050a08070e0c0408100203060f060702180606190206 78
    0x21200e0300416110f079140240106074000c00d02c6030040000c0b0344595281c40c1c004142e40143c8290304085024401f500ca01100d044000c50000018032601150070882e40e543c2200400145080580320b50b01c0d69122040c101005041011075000c4180103201170007241c0e001038a188240c0d40d554140480d0840b0000c3e611003a0340420300d07000d000074902e8004180c2e0040160450090091240185000918000340c14564001c1540c3c1c4d9100f4980b607202c81c0010256243c9465141282074a0405a46001034800c00000c0790740d0000005104600d802041040654100c2504000607603a40c2004900034001d00e0603035a40305481d01c0415101500f441110390581c0e181d035909005c501d450300f0074002003641500c60245154001c040810090804112081d004000405210300e825640c01c42c683c90803442d40c1218003029800811701a282c03418000b80010304000703542c01420140d284e000540c4a04180350000019954440080c42c550340f2a0202c824180105580f00f1107042000c40095950350211160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 531208857 1250 531207607 531207623
    0x20c07030b16050f0a090512060f06100f18050a0e0a0606020c06040303051e070809040c051e2109030307090e040c0909030215090304030209060303070b1602070906090506090a0e0709020a121503 85
    0x1c0bd505040c02da40465a107022034885001014150078101c1d56030440480442201a0050b00402d66075546401c600050007041c8034034405042c490b00407000c0340d480b580320905541c01a20010000d40798202640d08130f07501070030016110795580e0301d003a40c403c00302e25941c0341000002501c107041110101c068990060195401c104502065000303440500c120210601c0344484d02c10040c0745c0c0c2629800401c0004071a801410b40c800c1154a07205045000340d59416264002008000070f19601043d0b0100034401c200d00c4240d141825110f4025a080a0048100d001d403242200c0d428180200600904000030113000040d03817a0603015543c9035005401300720310610100300881c405142c00416158650303006416500701742c8401c0404480084000b100e0015400344103800201c43c03c880c0305202c01000001000b0407945000d00800100e004000e00208002d4500302500c44240e0000030340205842080c03100580d99076030600160780041c00b2414101c0300e181058140400c585101c20b4441c1142d1041c00e40d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 531210107 1250 531208857 531208861
    0xc210328080f062e05120f04030c080a0e0d030207050307080105010e010e06011205070504241d030a021c030824090613020c07030b16050f0a090512060f 67
    0x1c450003442514405405501a008200d061400120740e680b2410603018140d040c001c0070142052590420750060b0126030042070b6510741c14440340945600480044400d003403480c05079000340c406121190046d010950100313031240181c0c09420100d0000d540140027140214031b5241c003e5a800c0b8078028a8024001d8001c0003a4980341402218140c41c0640e4141c941e0340e08114116140d1540144014100810307820224000b00c01441510300825480d90340f15551130421110200b05840c002040c80841c0310000c0441e00240c0c41120008001d40100009514000b0640040e1400520141c043d43c8900554400e1042404403109184d840e03100340c5454507590341d100d441d07030082c40ea040c10031300959403504041d0001c1d06e00300e040d86500c50401840c215100c44000c0074031040780c00640301031115507c8400305100b0300041d41c004030b070700371100d40410020b803148031001400f030b0203501e6150098880124500040c1c6019040600241c0000744c000001d915000210390340e1044280c43c060090461000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 531211357 1250 531210107 531210187
    0xb041406090a021306050114070305040e011206050105060f0a080402150d09060608031c021614160927020d140d0e030a02091501030603120e0906040c020c2103 70
    0x1e0101103400586407851044210703109142c0680c071803270b401c504012081001180a01a0b6048030740604110018440e981d2085e01d0100c04a480680101e44201d0007070105a104101c010f044a10100d020304d0880010b44552001c42c80d00644266102d2000c0008a28030000c41080c2d0310402160b40520410b00c0b10b956182101501c82c4a85994030081400803440c0c080c1a44031900100701700a00741c00481c91401564a035480c00407560300d0b0404083e0046002105503203600090300020f04070001082151546004000f41451083c1403a81c01740d00249d40210b007590798100740c00107030507041010700b100e80000c403503003070b032a504040044c20105450100b004902c0c100000c440c000c1c9a4098020039880d242c9800c0c3c1e030300301e030303036480074141015120600070002170302000c003800c3e43d403101d519242c0300040c0c03000801543c0703100101303000c1c02145056450000b45500040781c17000350344151082c00d00c50b4440311640c206c5005e1000030301080d101c005240c901d00c2c80015071242103803840b00394464014900780 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 531212607 1250 531211357 531211361
    0x20613050601030f080408010513050d0906120906060902030c19050a0906271502070512192919020316051309060f090b03190b041406090a0213 63
    0x9500500140c1c06a801400010b400d03880110520380512a4103007000d5a64100303609441c000c843c540500d18075281d00d0b400b0400c042040485c681d4240c1003c08040b41004001080f08540c0d03214111a41c1d201c3c815101440030340d60052015255080e025981c91800c14840395040d88950344250310021891a104840380c894010f4a04c006003d691300051a403038403808940170a040010300d01c6983c0d6401c40c02100c00030300c0c04000d0081c035034005800c0c81039107103e9020b82480c2e1154019405196883c0342d00002138004201c0700103c0b003400504100b00402410100e1034001545d41054480d0311088040105900e5565450300c6442c007000781c0d107012124010b80105074081510b5111006070b02810580d003031800f450203040c3d81c580c200c1c4070400890b5610240c1055884903800402400036050090020003100c0c00f51480088065000349581c014409810020802c03d10002d4a0102d00341c0110701088994030000c85003084800840300141840c0c5007090725054206400c911400080c502d03200904040c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 531213857 1250 531212607 531212641
    0x150307080d050a0e030604050a0308090307022209080c030301092304030c0203030f0f09030c010c0804030f080d061403101506050309011413030e0406181d0102030a020a0206 76
    0xa4005081d5030007003510140c0d41a00010000301c140100740004e24040e807402c10103144214041c00042c03203100a103043c0038025034000b410004268208005480140e15204a0130040c201c440c2403080b02100b441014070010800114000c00b035600010344208070510000207141a6081c488003001000500c901d803102c403402504111000448990003e030219000e2910310407080d0024061703918244844984003810b0748000b1024000c0003007c510002c460400300401c0d00d140f03c0a007894402d040c01074030745103200c0c0950b1100518540140d44400100903594003661501000c401701401844d440e03000c502910090303024203070b0086c840c2510424080d0081c0c002c2001c0c40070404d034528040343c100030084900340d00042002040303648440320349030321022150004ac0301d1002c940100051103203900c0e00804201c14038010a02c01c2e800d1507030a003e044034002000145e5046070304001960b459088004c04001056a082c4200e540b020007000b014654640040a54003003da007a1a5213a17105040c41e4014a01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 531215107 1250 531213857 531213869
    0xb091201270b0a020913051504020c0304061b0302120c01110d0905011a0a051507121701090218040b0102010b1320040803040905040503222606041106090405040605150307 75
    0x441d001d0b5110b1450070303034401504264042230078064045900b01203020b82c0d003c5624001c140c1d00c0098100301035980894070a00094001400e1541003009840003966210040d80d030240300300d00013460b124428025400294500181000b85480d415010400070003401c55400a032003d500304400d02c4c9044890461044400d0001040c00d2103150504080c0455072003004c0c0c0440010a0400100012072411002d511651802c0e6444414010001d4010bd400440c107900055075140180114a141c0c205408500310001c01500c3c000f814550703540040340034110b1034071a1a0000f03440115102d8500e980c1c2c224140030340c2411940e0040c00180302c1104024030a40c03003890f0941c0c01c01d0009011403500c54200ca9003260140e0304a130300301890301510b0041c214003040c20003a241c1c11003104101c1c1e8002c644240201d090740605821540d54600c1400b43c680b00f0052000b0115036541c19000c3d020354401e0192860b82c0c001070400c00003480c1c10320700400100415070700c500781c020810303100403400d03e000100c0f078003034a030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 531216357 1250 531215107 531215119
    0x250912032f100b2d03070e180705100203091c0605040c230105090603040201050f0a0201050604051302030a0308040c1a131e0e19050405030a030e06010b091201270b0a0209 75
    0x132a0301c0035500003052041c005600d40543d4200003282c0c183d90388103a000707039409042180e9091100359158501501c9a00c2903004601007a540d0130020380100a03141200003e0710b00f15240205900f003001401401c0800501040c508001c2c07106125030002d01e81c050340d0741080084105480c1031007800c08003c9003a11030740000c000700003d4060342031541c040c0d0b41081c818100710f030030001c24070310744101904105001c000503999041045120f2a0a000b0140c10058a012140d40880560082078480c3d070b144001074184000343d030114040011400019004058105141c1c40c038202c0a00c21010382e500c8600420346010402001103428188901440c08004041140203411031501300405844500142002c4642c0400c1c030894024080c0c0f4002d02e0720851240d4040d541e6410400400b4040b074820000b04082548080c0c01840035407401400c0380c4c429002201c924600055055086014000c58460340e40d170505910409216001c4010f0440c00d01d601c681000c04540d500c1c221080100e0049401e0a6031043c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 531217607 1250 531216357 531216409
    0xf021603060e0705030319091a070803040215030a090c0509151c06020d090b0f06010906120605030d0c0201111906020f0909250912032f100b 62
    0x900d2507000c00007204071241900c81d001c0ea220000f13030030b40e04111317070001f032a8255028031070000c0ea101003010301a100340c500c0f000c61404a515410000c1c0915100100341903000008a015035a03420703808010030b100c0c00d80c49552441c0c400b0f9100701400300d030760040710040f52828001c2010b18000b15800c1c41108640f5180110340455800c20035040040c4a050b81e0a0407021090000b04400703000030242e81030040740c003161070f116610340010220f50050065140b403920701c06020081e139000d0320b140112421407411400e40040240100c004114030f5000710303498401c2c1315080f40440e412111210445000342c8070703200c2103002110000e0326008141c0599a25020550b4020001403555021b040355600310006141000b4541000c42c0e441c20003620b2040502c0480c58120a5030411030074149031100c683d02e088141c081c58410480b00c810341c1540c0c0102484501003480c4182c800f0f00c059a51841031060005506a4035405400e07200d40c495a220128541840c41070071702c605001402d81c21100074600502420303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 531218857 1250 531217607 531217613
    0x51e03030624160b0601091203080a050a06080712022707051b010f060807080a0803010302120312070e01020606040b06092209080d0b0123030405030f0711010f021603 73
    0x12162240103090498050202c00b259145600d075881c000780c4a02c84c0c88065041280016100d05803075840025003220022070080003c3c0d001c00a15004040010041890703140e8455600141840e41c102c0b8010744a0f09400180c0c00788400700f180e0b4454005e450f1f0382035030200c00d0180c103100801c0604070310030085002d001c161080e00c244000e0200000c18018032100c07442c0184d06500b0f460101016030100b60301ca020502089800b070080400070422440109100d507a0341d502d00d1020b00051001a1189401c902520184071090045641440e4602e00e40c1019180500c4003510300e41e40001218010701c10140007908508142c132034000390005c01040706007004511801c110031506c80c11581001240348607501d8101441d24011070480302d100305145503c6a070f100c1c00c031408448542503d01c4c10030100700c4946245203030100304c40840d11001880c482d0340b03540710f082252a41c8a8070071003282000d0f00141a03010f006000100c0f80c00301200b641e4882d501c02842c01c1c00c0343ea60340b011181701d0840c000c0c54400c00c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 531220107 1250 531218857 531218899
    0x1a010309020d1401090c060c1704060207050f040207080703021b0a03031b0f020a0b09090c0a141602131d0606030c0f040e060103030f090803180907030207060603051e030306 76
    0x110b901680012034000f03046e07035800b00e02804036031100002c1050101c3c000c003080647c4220085070351154007c0c0d1308291908600941e60a0140304045c040d01d80d80d6400d111507160f6404039004aa08071103c1c40d52800f00d80f41c001c0d030307a0446042c030b10040c0701c0d8441e03074007240d1512812540c2140e03010707500c2001d80c200791401302c50f40e105060300445000481a10100068664411034030050a6600129071030360004001d11900c0c400003030010841c172804100301034110b600141601032030241750078941d485411402e480030340e05d000300c2c030080c0d44043c0b00304000c0c03c6c5602c5034206039210303150220f544480d04034a90b01d15695100a480b003581c10780041c148070100d41004801c009191000400104403075644c212141e06201c005c3c0c00541c00154401c03d000c1016821283d40300042c4068402146001c1a03030000716010660000071038130484680001c00d44641c480e03015a104550030440400030300b41d9900c0d00382c0d5158030501100e11089448146100401030100540307102d1040589000701d64010480700c008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 531221357 1250 531220107 531220133
    0x3030c0318050d02151b090a09022209020c0703030e0a0905010801090201030b0907080109050a0b030f1005130312050601030618021806040815090c040f1a010309020d 73
    0x309903541c080c40c40c0007668401c0c0d1103401c60003540600000f0111510090a1181202e10720821540307000521020300002d503442c5c11a2900c0300101c545840e10000054141a1301d50b004550700f60011455800c0c07440c03505102000100d40312000300301c02d0358540650040c4d000b44d2001500c1508603240400100c0d0289008031103500c001000c24000036190002801119000c3e08401d246a654036260421941c040c0314800c010704040784c1c42c031100e1801c01001050071505028680307400e40c4480109143c40055000a1a400d9004041d917101c80c0020100070b13907030f070308403c0c0301c042d110b05010100e10380d0340703011880808864241d554200141c40d401c1000d400f03418003403c05030405558400c0052070880c1c40c040d1031000311029502583d160354054030038030b12462030310480b4811101000108506400040d480300001c001c180098003560354846513504100301c0003080c079042401c007011450040311320760101580409504807901d8095104c00110101ca210100c02504085080d0810021a0031098541 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 531222607 1250 531221357 531221381
    0x91a040c030e010e031806090603070f03060f03080c070f050123041e030c14131808030c040914010609030f05073b060a170c030105151009120303 64
    0xb25402001142c624210348980e010081130380c00c0460440c0c001c0240518076510400c0413901c1038149400c120024a00d4480a4080006d0001148105080b1070294102c02c0c000d21030300c00300c0141c0c66564144044594481ca140100901600001045c040d02042114042e120185d58144090140040b094221030010314000c00a01041c03000141440310102c424000801801041c01d1071880c500c0d00000e03203140c1d608112a5404540d0364184c098540c410050361000b45110003280b2035282880307650102d00314480181c82d07080e00000b04000021000011b204942c43c05030100a0501044d403206040300d0280544000104055420404100d424152124050151055a03c4550348110101110740b0102e0301c900300940c100000c0316800e06a80103c40101c1d01c2e81005d441900c0c0190000d03504d00498026096402c5002c8198505d0100401859103840300240c005c002c1d500b0582c010001c40d00c0396908451103501d44042c0284554495200041220f182c042d4500480340b9036542a000b40c13014051107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 531223857 1250 531222607 531222611
    0x1401060e1005040f080717070810090f120e0a14090a1508030304030c030806040506010806041a09040606090513080a080c0706150801050c09091503010908120907091a040c03 76
    0x1090264448404c0d1005017040d000422442e49450784002444884031090300b13943e08648002c211360b4401094a9190303442c0d600c000950b034115440d1038138030100c280c8006022495590b0304185440c2d0004004080180210395010740103590f250240c0380c40310000001d03030700080014003040701e450b12a044090f840c140c00e090050072030b032505ca0b083d01e503400895042d0000f5031121100f0080c10782043d103c54200e0400e039003e2240740342120000c0c0240c1c0d070190002c1e00450780c0b415000301d0150035112403824001c004016007014142400c0c4000a000c071030040c15812481c0c40d000c11420031080c0d0300da00c40c943d805810036081c41c0f5400c0e0161b0310300400410700c0b980044100301d4100000d81c1441200e22036142d000031410480d0610000343d0841e0340080011011078800c000502c460760f03e0380741c1750742c0c00000c090420200005010102c1d01400c04035500410551011440e012214003020280b44a05541d2040703882c11a51005000700740d40d11844c2000e0840350f804403000340ea04141c0c000c02d000d00118200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 531225107 1250 531223857 531223859
    0x302011b020c0a0608131205040b0d0f050702011b0516120503040b01080d0c08030c04122f1c02030a120e130b060319060305030a050d1401060e100504 66
    0x4006880d40061221030016085000c10190514042c0388036400b80c41c2e41e01d4400d038a4030b05010b180403450400c2c04080d0811503114942d03c61503101e1001c03a00602449030480b0780310300180b00e03200301501003140b5850700542080c00080e000c0c1c3c41403181c00f80c4088d4140341c0e002d9100040c40180c1ea01d0307108902c142d2030984004018808a40e50481e40b41c5c040f01d8654400d5560701d01400c009603a480b040c3c10907012034102c03010100c45c1030740c8989412403650304040c0f0361341d90707803180c40040341c042c441c4d47c0c41071040206031881d40040c022003034008600e25611b42c240c20f242d6044045000700e0615002c02707066120038003210181e1030030342d41040c16684034405001c840000ca0b440e103074515126860468040020300301240c00302c540c20725079100350300351a61100a01c2018a5800000c013180001031034440d0000030510142c0c42e18449402101c003c41e084407d0301e940d80e034031170340062460f80030350042103203079040c4107145001756601c00610303040319440d9540380011446030ac01c020038211540b500c4020024180f00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 531226357 1250 531225107 531225131
    0x51005010b07020102100b0906150c01090f05070603050c030f07230315060301032109030c031a01120b040204020d0902040e01090c080601080d0309030c0b090a020a05061e07030201 79
    0x124a034040d0060040e240d03154003181c4002450300400e00ca022003c1c41c01c00c1d80c456280c0c0c0f07403010f10b9a04103000f200c98000640d0040755980c040d000b14042c0d8442ca60800c0d206405110b4444e0b15291010700500940d10032549403042942a104251407140d01d66408000151000c15103410a0780c015005261441500f06885a003c050041c2c0419035119074000200707010110512507444c0d81c80800c152841c40c110362658440d00c018640d50121070190012210200f06194480d40005003c3c5601001c4841e10a490b4200501d40094901c50003a80d8520b000003c00c0ba00c6800c9902c1d602d0030b40c4040d45602640c1d8035030071b20000e50001584107184503118058000180e940b406042004055a030000410b2a0281010902c560103640b000543d50002d03001842060008910403480e04143e06000c191148146002c8602c82c1c02e000000d0684920001032210340c003004035941c41942e000304c49900c1350176290b40c1004054890400e00440460120910500031403201c0f020b828014000e00000498070359001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 531227607 1250 531226357 531226361
    0xe0f060904021809010f081009140a0b15060412060b041d01050405060a0b0a03060b0a09110306030601061412100302040603050307060c1d0111070314030903100b090f040510 76
    0x1e00c03003143c880c80c2e400c007800c0c0b541041403c5a00500003000800c400900d01124981c40d4a03584c2c0c08001c1c2192990380080520100307030400071154041d20100c43d03100c55141440c0d0340c1c2c50400da440c02d03c01440c840d01c0e00c5881c60300360259030070703a1146c1c00c050110781d180d0340e80c03000101400110507030000d032500c00c06031a07000001034180c4100d6601002243c80d150601e440307814a2001040680d61320b01c0c080707080b02e0030f40b1400c4550341540d603c0080010703c5040c420000d2282c2005a0100301f81e41d081600000701c800c0039401660188100344c00700d07209a42c0718070051f14a10529000d20f5000c007001d00000041c2c01c1c14130212600701c2c1401d801000c4a9840340c0105080d265507030426521903000043c607604000107449044c1e64100289040c58241f0036040954501460b0b00e0b1605041144441e200d94200c071062214034002c41d40040000341094158a0040d240e8005904c0b1714464040e0240010361014580903078030441600815004803907560b1007120071281c0c0080c1090b5081d10958aa8407c446501c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 531228857 1250 531227607 531227617
    0x6031a030102131e0f05060706090807150c0e03030a0516080c0609120f03010608060f04051f0902030910020304080c030c0703021f0c0b0712060b0901020f0d0e0f06090402 75
    0x40e034400c080113080140d030b1070818148018010681c0d000e44010001c020f00d8a100c8010380b50211041c81d40c0e50581e0402c0c001800072102d016103a1540003c0301400c10041071161803001130343c41030a21a801010340142c4180450164150305500b080050b40b05a0b84101d001301440350180c030a44140042d03a13103600c55140c06c116480d0100c1c0c0d211405000e005002000a80180200145800d10703090410316034921718041071044400303011103200410b12a0b9141280324161140160041015151891803d12a09400f0f0900700030080703d01000304070b81e8001d000302c03446108941e0040060710b08003900b01700250310061003aa801c900c14004111907280a000501c444007040c40249203443c02d50040084940d400030441e1030003038a01d241c5049154100c585110304c140c00481d801c000e5a03c3d0311080d1299410350204500481c40c02102182040c489006405031010070381c00c8561900d001858240e4401c661000c40d004640c1d904490000b51030102004d0503128400f030801400e0042c960b010070280d03041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 531230107 1250 531228857 531228877
    0x30a020406021204060516020409020d060906180206041208090307090b0f27040c1703041404060806040f060609050f1b0406050a0509040b030708030c0105070c0c06031a030102 77
    0x1001c10003554100249102043c154010928191030a08040c2c1035225891401034164044c0c03110000307560f125884081203d8000c4c149686515103450b007a07004060480003128454684024110007408000d848480300703034098000c40c030f03060400e0035081841c1c085042c119003103901003041002a40b400e1010b403004100100000c60142155000c001c50050b4001099009072a400d00081c41c4240e41c0004c8550701c0c001d01402203503a103407414581c402c1030305078024107104014142028540140000140104e40180328034214074502d9400b000f00fa82c1041c46001565071008000c00e0100d075513000c240403214803800001400f1a50f40d0500c505543c03080700d015824003c00701c00c02200ca050706034640b2304120b807640f05901e051b040507005403046c051040c0e40000c010001c1744032070321910b840d404040c042c80000c0840300e0b410750310303480c2070b640c1d51141c29201065400c080100d440382d8000e15100700e4a5500c01106000141882c008078024240303911001e00c4010200d0201029807020f10080c80d50721a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 531231357 1250 531230107 531230111
    0x23010e0610050609060703051c060b1c05100b1b06010306060302030d210e100207081b0f0318030a0605010b03101e120f08030708160305040215090411030a 68
    0x6001408603508000070b82c441801001c00b0002c140d2203075603d03421500802d0345401c0c00d644942c400340300070981803014615600c086141c00310205001003040054000d99140c0c05116501b8104160408159041a06c549a5110007a8024031000760400045e01483e00170884a1034803203070102c03199240540a90080d02c9403035a0701018070540c10140421000c044540c14244919400c0200320040206040622905c26a41c2c01424400c0303c800d01c03510801541c4c0110540d12850740b0305200c6000d82c410b5103080030856071640c0003007400a0106400c20080300c004080c6051900307a0a00c410701b81c1103814a5541800b4190746100064842d00c02d0038041c181510455440e072400085404c244802c907002034031100c3c04010300c00124a00a860b250580c0c0c05654203400743d6030117250100c0006c3d41258000c00003107000c001c00810301c2d8018003491084c42c0c0c0640c0c3d519090400344d01a01100d00c180c50203504186070b940901410340c8400b000305101f200c0600005420410b2000c2d0748843e82007524107544050f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 531232607 1250 531231357 531231361
    0x20612010b13080303041a090c04020f0a02011d030304060b04060503010c0f02011a1e04020c06151305071b05070807031a0105030706090306050a140c0a09060203031323010e06 77
    0x20b206202d001030240200158a141031540b1980068016941404180e401c41e0001981c1260f0504c26030220b514041c00030354035504c11095001154228007014001586481460b0742c0d280543c803401998125524055881c645035600e400000c0c060150000360040cae26941c3c0003c1e6900c003489021a0380403150b50b4607200b4500908000d09403001414600400741c2c028011141c107548902c0c200380106604c048050b400c07814140400d019000e41c00580c0b5540c020340c81082280d0403002000b0740000e00403a451200700c2c80a103085022210165013100000c0c1c080841000e86c103110b5980304060074041c0e01103500d003603554007034140340c400b40360000c580b151403640000300f51203149800ca80c05440e048024000c10b0342003410040464910b07103c09080303551144007280310221035a11041080011441d249400d1401490f1001c00740c0c42120080b0020f8541e1600044d49480030003070381c0c0141040600700715010456210354034113414074118940c4800c046603e0382d21340c68091040585540280c800740c0302038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 531233857 1250 531232607 531232627
    0x3030b01211b1d0103020c190b011a03040804050904020102070504020a0201151401210222171b0d05010b0a030c15050a142a1b041116020612010b 64
    0x440e42600300052003000782c81d1070280d0f15003600e41c0209520a05e00180c0703501240302501e00d0030680c58400091150055050018014000a580d0580340401c55148420038041191410303880304480c00b83c410b440031301c070510030761402c101c0e0300d500035005104030742040b42c075080000e04030382c82900c1900260b9512014500980c030044803080041c0070300201501c00c090040006061000d00038070065403003d01c0d01d606400308100d07070b040d20600e08100e0400075013500289818048215103009560022114102441880c2c4000074400c1d5403054008801c103400c0c0011003800703250a1100c1e0111515526094100d465031104143c04004500178100b45034540e15007a03031000c211005110302d000f008000c002007144030780c00001070b01d4503028269403241e9480c844840c0038401c564400400d41ca542c461313480180700000c0064881880700420300708036401c18205c000c0000305e5011003085588031409010850a0b03070701d070060350f404003030000e85540e1a10710003141914015800343c02101c00701c100880c2a5142d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 531235107 1250 531233857 531233891
    0x5042d05090d051201050d15060e041406100302191d010306150b040b0304080c0a0b190b13020f160819050403030c30020102090907080106080403030b0121 68
    0x10302c900b0b824103d2a040c005a1107a040110502904d8020a01151070100704120009041401070042400300f0a0a031075401c0e443e003cae882524280c98a103100e20320854002000700da403500a00c1501c01c8040460b2550742807010700814a00e4400508222400008140200841c148202003034054a1420340d03055240100c2268480b80240b0702c128650b11003071000004e600121415264202a2280c8079a034610300f040880c420307520401c240b07014500019040280156040380164103215070000c1c210234008000c0100c0d480d01e80026031065140d0b0030070300000481c0c3d0080c440c1600c0c0844981c980f0078002d2840f85444000d2600316800703200026071100c01c0c1c00341c0e40061503252a1b85441441d151850f100100301c806541c0f03002d400c0001d04084440c450765800021052410258640c0c41c0506454030b01034000e400c903445003801800ca400c0050511481403482074141d03446600c0300c4599485580301140103010402d42103051180c1c810361180e074030041cad090856411203091408640480d1480c640b000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 531236357 1250 531235107 531235123
    0xa06090210090612021e0a02030304171602130e150106030f06050d0206220b04050a0806010503120304030c1b061b1e08040306020f0406110309060405042d0509 70
    0x8004504000b840b0f0f042d0700860001c012400e456003d030316038a049200100000c04800e6004c030405000885103904c90300840070354481e81c01098003036801ca0602d41c00d07160520821042601c0c0e03500b038100c910018589183d009101021504e40012401b19a00c2032914200891144540844890004000c201c2e818010700c9240d5002c01004d0140038030b41404204100e480340030003032282c40c001c6070084140d106d04070311001c0c201500d0464404a55900c46200706584a4000d09000741142040400c40001c0007480904131800034000b462050080701c0c0c03210715600040d00c12800c100d40400c881c000720300c400071805e2001b030620020300a004e240100c003500f1542401c087c41000841413040030041100c2d03118641c540b10960411a55003109071400810741c1c45983c0005100300d1000c541d0031000111f20001d003051392416211166041b54030007005a8070701402262a9200c84100424481c0341026040031900c400386442140580710760121400c0c00d582c0074a0074032a02540ea104000382c8004c1003221341 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 531237607 1250 531236357 531236389
    0x30304022b0305030c120718090608060705030606130303080f0106031401030201111504050c0a0f0b18040209060a030504050c010906090b0a1b0302070906060503270f0a060902 77
    0x7000d1542581400040d4030308003500501400700100c00241011a030780704070f03941d012441170031046903d001407000d80014400da600c0c5d60b106d10741a001140385415441000107407500d200040ca032a030b44110782110f00e40c2c0002c040c540c03c800d05214604490b07150781ca5800145200c2d480300b004a1070f000100480c10a01680718004060070f004c14100d10081c00040141500c1d028030700751040120190040b46025203400030003240007541d00c100402e100001c80c0ca50003029080b04c6152843c1d682e031503c0c240011140c06101c0c0000000c000664007a1800e03142190f2a0f0400361016080042000000d482a0040220f560120707890794200010440c05202d800c09607102401c021140f68104130000380520f081c1c2c001d030480090000380200d280ca00845440d1130f0111401200260502c0300e1a00035100e807594071495100d94104500841d0079805034040d00c1c402d480f80c03000c0c2c2c8580a0100c41145641d00190baa000b41401441032240460030140140c0d41102e01a030300104d2800305038410300c1203181c07001c0c5a41c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 531238857 1250 531237607 531237649
    0xb190908070311211e121303020a0204180b0603120702060304210c11010f1d0a09051e09011103011a090402030708010510030605010522030f030203030402 68
    0x10002985590030790719059050f10f01104140000401d091034002d000c000d428444405803000010f400c2036600030300003450203800c050415455003a54000501400c1c90149031282d030a00000e25248800c04511090340c081c1c812103924200d250045400c40f5003914030761030306004d40c104080c00d0201d1013640c25004041035004100e8081d11180000381d900600800903c1014000003080074403515403900040c1900c01910440c449400c09005401450704550441c0c5116150301d20b2952580550f08400d60001c1d44d440d84050004900c1903080080c800c0507100750700c90040d44010401000c0d42c429a440b9051888680348901004803041d054070b68002c0280c41941e04101b240322200b2445410340e41144c4000c4403d158400d1040050312282c000d00400c5a0014808820440d03169030050565040764001d42d820300304103c15403002c5058844c1070003440e005c01c50030421120106103804203028003049080300104080e807650789001018442207c290010b9001100b0b0105500d85a1035504940300c808000b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 531240107 1250 531238857 531238871
    0x81b13050f090c030718030623010f0e371e0207020a030210170a1401081507080702070503010e01020406080c120c09041e06080c1206060d0206070c030b19 68
    0x2e40300042c84000d104004100354000c000102c08980382411b4043c590045060004c00c000380c1d2500240c84031103800b000255120800007444d00c050100d96020f69030a0300715074501d075540c0150380c80c00d2038500c00c4111001c521640610341a107842d404921045640071400300328140c5a982100360050505180140648100131500050b5141c819103000c43e6815a480340030100c1203802135684000d0310461050b94461a0200600b900c59a402500103955011480280e82d0300c43c1401561900c160003165003c903003010200301c140307008240d1554000443c2c41140c0300340b41c6440c042820b40302120340c000300390703900030600b4000581c004968981c40301590b0100b500309001e00c8900d500b1041c0141c02c1c4502e58500282c0450b01c0e446a0b000303c0c1c5a00310354907144001c10140d40c042c200800c0c881c841e8014500511446842c80d01d4101036071400c4442c8070300106010b4071000700300010804484000c03640302c00304000b0200050302031042c1900441c0219015091850002d045001202959140c0281c580c03034005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 531241357 1250 531240107 531240121
    0x1006061409040b030a0b010e01050315270c100513090b150d060f03050607120507090311180702100c05040b03011401090b0417010e030c0607081b13050f09 68
    0x50320301c00c0c1e00407100407419a03610b0340807a0a01030405000790a206072000041034040c65004118100c94041c2c04698404499181001c28407906880d02c20040d20b5400c110610610f40104002600d5842c2042d80d045034085000a11503103001c0f046c07200800d0307010886a40c10040d11410100818030f0000a000815080300041e41c0409204020302e0800c0021400d03d4803207000e6071080c0040c0c43c0b01422001c00a44030706100395100c008503200c100080e4000780c1503070719041d24015280105626102e20380d2203811643c070340c030000d0640b244141d004801413000908482401c2141400b40010360040c2041c0f5100304044402c0c1e90101c0340d03100a0000030002080b0441130142201e04592242d091101c443c0d5211004880c480441d4ac0203031403c03071011a0110f4006100800e100101e07403804000c00002c0f00f544d080545902501211803500d030840d6000641041c042d4150940c044d41102020002000c101c13007a01664004c3c1807820a084103c40b000e00050906441008c16020300300c82502e02854145 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 531242607 1250 531241357 531241397
    0x80f070509040809091e06100915020f01090803010e010b0903060403030b04020d0c09140915150c03070309060801080a0b1f182c030304060203060a030212100606 71
    0xc864240a000040009000d00c265642a1544001d00170a50456420729010000e0b01481c07030030030003c800745d014001c1185441c060f41c540784043d140f0b131070340d0360901e16268880f800da28030a010b00080d805180422034484000b846140d014912074500f0396203d5040241d11a499141600a4040404200001e860640d0001046070780964035250201e0f40941c0100810081e000c0c041039005018100007802c200960413100150585004481540c403003030000c010041201419901e04c0030600074490740c0c0009017441c41d052030000c84429485032501100c1a0001d166030f100e48400e50015040704002d000e650b80c00140d0a00404030300004111100030380e1200f1307608440140c0410139102c82c06802948100314100740c03c2c01800c442420034801200d01c410030b0081c000021941c0440070100030104d10400c0d02d011f0841c410801100110f045540300e80d07401c0300a51000d041356501c0b040355100003005a031561600903181560501611400c01400e0f20402076a250350800b006003c04a44d802143d81480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 531243857 1250 531242607 531242609
    0x10206011805070e19090b041806050907030f260721140406020105010e09030f07032d0f020c030f0a03120603051c02120a080a0b0a0803030a0c0801080f07 68
    0x1403400030b91600d4815007a204070603281c10498001158140c168071591000c0f0240b0212100c0709414014141c1c00400c000c212074000e21180070001e4000707904000b0540303c0c0e00050b1702503010000c84010076203030f13220209000c002b000200c940e203252103040a40d68100e42c0080c11421144c6a0060811800b40e40b41d0b460040c9203000c209070b02035203280c2400c0140c0701e10180d0208128410f070f1117565076240c1000901a0409001c0d100c0308032685000300325208000002c40f6140351020401e0343c1800b04580d411200484881400807002070010788580300f6401001e005841c58240f5104c0090006601d1030180c10280c5101189120360055079803090114004520003d0650b403500d00568191040ca8448000784116080a041c07840ba181079462a0f0f009150342a00c000710315000c56100c081e200b00360400d035104042d040c1d00080c40f0f100210780e07409a03503000b014944070b006182c41c000d59240c0502d286103030021142440f145031240504c8000700e0300030b81014050034002000d000c40d202054103c50f0f0743d00e49 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 531245107 1250 531243857 531243899
    0x7080402090a0f1806151d0c0c010204060804030807030504080306010311071203060f0b0301080709111b01050703060b0f04060e01200a2109210501060308041401020601 74
    0x10360001d00854550361000490321080003040041c1101c16601040c00d14035004112207007440d040b02d02051b421440600021038a0040c40020600032090f0f2a40c01381101918404814030305000688280f4000c2c0040c2001e44419520380500b45130600380200482c001401400a061906041c803011880362005c0f294821340c21b09010511056082401c07070b052081080240c41c400c104507401c854a0f40c90b4116404840112a05500c925200c908510040c4428400e41415a0000104100c8080b90350482d0441e8038219400b603040c010036030050048550403056010940c0d65403010001d21941500c142005051b40071900760502c1d129034082900c0d071040d4003650092100a820103912a03101d00454250348a4400042c1200e52903800d003640d940d010f012007100c1c2c1c09403200440383d004030400301d80510350855035216180545080413070039a5a200c2a00d0320a000400801c0034082402401000001c0d032150498640d5140340901207a80c02d1a512802c90443d0007070001044401000401c1456000c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 531246357 1250 531245107 531245119
    0x1021c1e0c020c0a1203020606030d0203040918050607031b09031e080f0d0c0305070c0506130501020c12030a060506120c090303040314010e0c030f03070609050c04060312140307080402 81
    0x180650603403400702000e00950380100602808505c1014002c3e001c9001c4e8401d40072503000d6141e8034100f540703c24141c821180143d04c10f010400201c2440d4000c0c082e6410003404100d02210161142030410070126608000701e61602c08244018409803200010441d4525100d040d45003981c2e201c038606000710320350501c09882d1008600c14003000e6002c60341c01c00302d260001c642e640007000d054006410a5034540c00402e190400151847c0d01074020400801c0c2d0010103010140c0d16800588041020b4040075545907600744010341c6484010440154440c00f05030005890340f4240d200070084d94056044140105001c0c49007860007003090a200c0e4100060425071a05c07842024082807660046034400f421884802c41c840c00c0c2072106602001520260303c0070340301d03042d0807807003803541e501010b0301c03c400e041d803040011070b000c0780682e40540002ca1088040e0740c1100f000c1e500007819104c1980003900e03200100030904485980140a19489011501302c40342189401d0328040c195003401407019008103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 531247607 1250 531246357 531246371
    0xd0e0603010501020a2d0b09010c090506030f1b03092b0e21070905071b02090a0b060405040e0d0807110703060903020c040906020301090b04140a0c0c05070801021c1e 73
    0x25120301004d803200d0b5102d00f1046d0f0700c5c0c1034134282041080b80580304910b181d443c2a041c13a000718851651041030b1000600440c0c0386868840401401c450020602c01642c400c1c1c8445a205641987c01140129000d500030110f6039075004d80d042c80306821400c0c601e89030034000c640341d01950700a80381d00c81c1b103002252012840d486151604d0000ca001c0040345040740a0624007149142141d88154001c0d101c0365074656070440211030441c0c05840110010703610040c1d010002e0f0600e4001d4010120300e210107002d0600f4103a03160003042c195a00c0181014a40d080454481e200550252005600842a1500200311688a842d4640740d000f40e00020700080e480e0046281418000c0103c1d102c400070203070003088245501c0c14a88020f400a0003000740e02e80c00d000c5131a07028178040c0030741c6085903c2031078500b14540b100d58070000148402d003080d50900000e10004800b041c014000503000b00101e400140e0f407900300700da8280c0c11641a031605d030a00e52800703261003901340c01e04000915040450100042c49 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 531248857 1250 531247607 531247643
    0x603030c07060305070305150a05040203060a0302092401050703140a0504081009150b01050d0f110c030711010f05070f08040b0a090e07030605011d0a170d0e0603010501020a 76
    0x512031010805014495450006a801e603d640414440c1d40d09560800080d10f804003850185200c0ca10001d600c2001000706024500d0503500864002c64014216401c250b07899010846140044032145a40000488140503000c28a481c6801224091806a00d002c00d9994040c10130300d00c60a01d001c480e81c1c04200c80005d58000c1046070040c3c0400c00c2141d54034107148054102400d1115001c89001c05c90f046401640c500e14054046e80b071070141c442d1800c0621000d80c810050180c249100d410540b50b46004500c684c410000f4902c1021041c041c540c1d900b1103040c9a6006003244109904002c10780044001045e1b0250540f1a03442d801300700f0760410503035822b00540901458010b104046000500c03001107a4100c1d45c2c503400c0b01c0703c03e2090952a03541030700c158201c0b001c51080314003281c24000c8990965112421010656000400410070030380c640d20200b140f074400c8002a103003540300d84120341150350044140f01d5520b0044902c1c914660400340000e4440c541d42e00b0007400c0c150801003103010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 531250107 1250 531248857 531248863
    0x5060301020d0207061d1c0c0204110a08071b111e0a060c03022a10030204180e010b0901080d030c20070608010e0103080a08040219032103090f0b0603 66
    0x5005502c056460b150181812070043c400d1561341d01002200f081c400c03c441c08041003071011402a404505c0383e80c0103042c0c0581d0300c1070b10a0000c03a17005688a00300380181c00c03140c0c05440121079503aa041640e180a0302c01514001c180000400070f640300b0350385080080c8042e03112800825040e20b04c854203c103082045d004224a100c40036038881a21040450100c0c0d0110035101280d00079400c1f5501074400030700c9000e007030310700d0b6262060303d0048100851441c18418031400c40854586001840c0a41d601c03990b0702141042c9d82400c0c50180ca45581601e000400d003c1ea201240c01110309400741d5140071491582e0f0395107500700805242e21500c058500034000c0c1140800303064800307400c0204901c1030312801e80320080c0c0d000e914049844040042003115041c0c211505036548004d0103460040071031401d07181110020b2080f41c0c06200c4141c404850800d440700c40c4000e41c0305000c1042c2410325040045124103030034140d0000c052030007005c90003150020100e034104a40040040c80d41c1d44403280880d00f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 531251357 1250 531250107 531250117
    0x70c0c030816170306010e0f1c0305040906060207051f0207180204031e030908071206021b03070f02040c0e1c020303190c0c060f050d050a06091a090a0b030607030506030102 76
    0x448802031520100c03442d0f84000c51084030241d07600380710810104200300807158235000ca10b8208a0807022954000ba001990170502c0c1d019080403428580da48104100b0742e0482c0d0820f90040c0c210140410603820200003056690a05190801e01c10080d010b00960f03460903441046440000c1d001184540708c000d904036406035802030f8658221079003256000c86100c0446d00c08400140740c11800003070381c6901141c1041500d120040103103040d8002d440e020085e410500314203007080d1228840040c803590810041204034811804407202c001c1500422040310045180e031818440313074505801c06645d032440c500034048845803180080005900200b450350190030640340d40c024981c12100c850a030414079031003986100b21040f11040342c41c0d000460b4041c0007101400c01190040c03054900800c0c190300a80c0e0301001d007110001c0e549668507803a0781038507008034003080080d40b007d0b440c01c26030a00702c0c00d03150300c41c90b00c0d01b0901c07140da68040400e0740d070040104490708150b0740f200071801035502034040784c0d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 531252607 1250 531251357 531251363
    0x20405030d0203030f0c0c1e0c0a181b09031511030403170c1e0a020f0316031710050904050c04140a14090c040e0c0310060e070c0c030816 61
    0x201c05151100c0069035070303401900d44914071a4542c1c000740c140c0a0000480b004009120064100029550710314180b511a00c004401a4060b08007108a55180d83c3d001000801c601c0c2c2d445054902d01d284c0c86c2044500c1e2544000346540803445613a409a00300030900c0403241d01410035880c586640c00108000d01d54403200c0c000c034140010a000500da888010f04c80b00c4800c000f00104540c0381c41140c1e46041c401d0003000f070901007005c4814142c0b01c1c001c1010f13003025000380c0140c80004c11610403080c2103620030a160780041481c0c1c0c2213002459441280b140ba454810104280c5a09020107002c1c107203149448ce5138440c0f03000800140810205204c240803000c0003a10502090300c5000480ca03240700100c0e1401d40b442d2030011010070036903814408a0003058010f025008481400c8107100191030000c6482440c0e108285043c40d803614200120140410441d0f40003d5042c10310082c03900b6810003030844410801c810078540046020f4201d07040480743c1c410b1843c0e136182030541801c20710300d200720406 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 531253857 1250 531252607 531252613
    0x516111509032a0c0603090f0f1b190b07030203040f140913030c110301090f0b010608070507030f12181a07050c0a080c0f030408070e06040204030317070302040503 72
    0x400540000040608803800c0c41e0300c0d1443c2d221500481d800c100d0f05071118100366591015002c00ea031418100001c5401c03c074103400380c0311410840c81c07825113050000031030101e007075001168007220460001070b181c14401045a1503441c00904440155404207075008507402603900107034400405001700200c4005040401d203460340150741d1414000304100c1a00b40b02d008064031400161000c2c03025503c0d400315036158a840c50070500c207444a86018a5285c0419090342d030711030b00840490780e000c2d02c2501c03181c4190181201503051050017840c81201a05c090f041c4001800440c001a80010030601e00030118580301c16000444c130781b02005482c07049410084419010004800d0002e007a000801010903c40030504940f00d1b500129002d20070b003528120103400900360f0070006030142c001440d045241d1800c441e298046124411300b958031540c0400c400798440b490400001300c00c0305400e0f920880441e004c50419146032000b500d04407440d80c125000c222164005200d0602035410785014013000b40407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 531255107 1250 531253857 531253861
    0x618120a050d031125061514100f050f0a2a0c0503071a070c032f0102060c070b041a0c04050111030c030a050d0207080f041401020105161115 62
    0x8801d0b22007945001c02c10010f03040510045148a0520845001112021070014120b0301075040f01842c5401c50811581c458507028044564500e0814900150003000701c100c1a0b91107000411049040d4400300343c09024403040c03e8021240c2140c141e5130720002c402c01d100d40e11520000c00f00c0ea1500354980060203000b00d540380c500075403580500c0814640c0b155428401140d2036104055603107866108804000003140614040c400c2c0b81d40203803421610a10485081d0b58407940c41400c400210b29043c03022600104031003020341c4204000c40d450610a0018203500c7c24407280c996030501c940c07a009131441d0102c1d00814100200760300300e505c0880541802481724140054591040e40c000d100d042e0008801842007041110701008440c402c2548a005529003105c0c1141078600b500300c60b180f030b080356a09010748400b00d080e4030021300351a1124035800d66220306004092440c40c0041c1000c5046a241c8010007200c105c03003d184112803000c1d03042c2199403901520000f80380406030f10000c01d0011080d01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 531256357 1250 531255107 531255113
    0x90a02090a1226030a0903110a140d14030432100b060301120b1909050c010305010902180622030605040218090d0503180d120b0607020618120a 63
    0x80d0910030544540f580500030710b0710100c4061400c01c249030241540c0401c0004c507164445c1c80d031118007160b200c0e04000701c640103000140ca090424000040c2d03880810801c5c420348000c410b000b02c01c1c501d034950900d201038040691245181d0700005000501900003600101c00e81e580300c52175881a0304281410a403070140c0c01d84000e4684d65070400441e44141018001d00070741c544001542d05880e5151452462030009031a1b1030a04040501381d8080c48102d107000c0c2c24640c00e21300941038114010030003040b4403034a60000404881059210545141c414010b907404118180d0200742c41103404c4905913142d0030b42a8030b0702050640c80c030340743d82094610900001040340c1e035001230340300718001c484409008030790000c85414130304122030305200f981148000d01d40f40743c002c4025503040864000002048048036030b6a518118000415001142008002c2c03900383c00780340500d1070080c1080e65a01d041416a50104105000d00743e19134000c01022540c00c2c01d039484101000d9007550902080b20407151440c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 531257607 1250 531256357 531256379
    0x915030603050706050c03070b1305030c06013303111b010e0c010f08160915020c0307150203090621100e07020c0a0b07061e0f0b09060f090a02090a 65
    0x84821650ba0180b544001000ca0090066450061400c0041d40ca4a00d0b280d0740c1480c0c016009010161200e440d51441c40400d204202070444001d071140103041d2541001e01c540060030101c041500403000200026095044004004401c0b40c2c6034100880c0c080c2c9225024612805400f000c1010040d000034264019001508101c89881c401801c2c0c880703a040c0d070401140d006032240200c0001c11501c4012403003401020113409042c011300d103021b074801e54840c0f09082c4180c1003100710400582c007480240d00d040c60140200002411824188031121000c0400603460340140c0d1407862040501040500700c040d06d0400908504000000c03000c0c441c45d00c2c60700d090320054140125481240e440c0000398020b0300016004260880c020003820300c8600e0444045200d50190700f08890042c1c4030105d1711010340303801c4003000d090f003680756010075000d40f070000391001c484c4601c070007501c04d680340400c1c0b110303686030641c2410400718240d80544941d40d5210b1000081c2c8220007405400900c0400009034500200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 531258857 1250 531257607 531257609
    0x709050405090a2d080322060204050306090d02060c0a020703050a141002070804090f1506030e0c030303010f09020708070c1412010902030c09180a080706050912030a020a09150306 79
    0xd407a203036090b40c580840198158104c9010004c1054003400000045a031142c059648003003171800451007541c01c4002e50086020904003201e62640200341031142c0d2505002560b880811403000301106006284002d54814002d001000b074030400261500c0c80500c24840034000d181c010741280c0190102c2c0c5808030940080003410321981c000c40c0d0181c50070308282e008075a1403d40000c82e2506007418100b44c1c20040c030040360b0300b07c0c0655640041d00d0010584d40020b0700107107000c2e01c2c000381030910165141d0502c030789042c0740781c0329420400040c0410080f0300e0130501910580600140c81d11281e203054600c3c0e2041e12009003041b0441d01c000524180d41404811548e44255221944c10309440c0b089800d0300e041040007035064121001c0e803229400d016555940c001000030400c81b85400e030010242c10110700078010b49541a00040100030b001e05070064a800021040003000020340403100650580405040c1d038064a8002076a8a260b038403035070910028001c10551220104070701d260187c02441c60b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 531260107 1250 531258857 531258863
    0xc1e02070b0f180904030c0b07051b0d08090109021c1106070c0503010f0e060714160c08010b0913140a06060b0a020708030c0a1b080618070e07090506030709050405090a 74
    0x149943c1200d81e424030800e05406191b00d901e900d140300d00f843d0b0720f8103480b03500186160b0402400f48092107125445564a060840d01a0040c107202510003500818023640181000004c0c1e04207189078005880d05500202d40802900c14083d0310081340c41c105000110f085052a8021404100c000c01e00c11201036960071600d046008110020368040d690080d41c041c0380e000d0055070070140c0007681140c095100c010380b00080821030340c0342000c1050340d13014000200711305940c03819414400b80204d071400d1240002010040741c00c440f07140f800103542140070030120001000c3c2d03000b00307201d280c4603301004500c110b5a44208144910343d00e444d14046990082c4188a0051203409000110400c0120031146200d16410190a124140e520340c050400c0f01e0303c00b0b00e0120301d0800b800045282c01408414003070804d84080c03240b10310010703049501c1d1011541000030f000c603840d0300b4003c0e4123030002c0c3c80004858040d2121a2640e0350000103403040e41469010f950002e00302810820140800f00b10041c40c2c0744 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 531261357 1250 531260107 531260137
    0xa08031e060d0210232b02040305070510050904230a0e07170703050a06090308160507110315092a0904081b101e0c1e02070b0f 56
    0x20300c074410064050340c0c2d0700c80650020003507000590054461003041c51200149010300b80982001440c40096038040d0010810a20395054a00c05a81c503045080c0711a5014100560420b8203603181e07191904824840d082c8036190000c20038242500030429180b2003000100104244060744003814032a1450300345424650340a440011f5a4240c54400c8c411510203020042c580ba80c1410742c4201c0d15040d2444c0843d0794410b42200100281042120710801807103960f012403107083d03a02d0080c041d000c000c8c10381c010000541e0340e4041010381c003200b5a0780ea541c22240c400c0081144e503001c00d00303000321911442c0703c408840c410000c202c4030000d0001d00307241100012110002c403420311402489000300040d0b6000d1038490110703010940c0000a4991791003080c440c896400e0490f40f145180c0a00310524881c0f854641070000c12154446044040100200905201c405583e4000500724440180e810f04011490300d101107001c0d2082100d80301411500b810b00b42e4802c0c0500010380560065a48800c1102c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 531262607 1250 531261357 531261361
    0x4061b0b090a1e030801060f0c050f0102090301111603180e0a0b10020d020c060d0e031b0c04060e040f060b0406030f06060501030e190501020f030106110f010b1503090a08031e 77
    0x2504011288403c01e801d642c1e118400e034288001265803240c4210301c1300070031112100c202c01044052002c0740604841c03070700059031a04004107050942314000c0c094020b1800074000040007a8141041114155161405030052200038014481c00c4445422242401c21044c0412090003c960710042c00c109084411591003809220100c2c8c0c1d4000c503c0d4a1030068018034212905070812901a0165810b0808007040701c002d4120780380c3c42c64011000c28180d4902d900d4058080000521001042d18030582d8180005410044448202d0701c01030002402c192400c015003050082a40c0582101e6034008c000348080c0303580b07040411592401d0700c401e486661130040002220341c0a031003900c6821814402500c0c1282e4542a1051022081303030781a121550200a02402c0c05a200029800380116890300c840050841000e00d2030311080d000450341e60307031400980d003e09681c0c4074400082e0f000b21a100959a95800000038109854854014807400002c800c1c020ba5049245c0440e091042c0d07191043d030a6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 531263857 1250 531262607 531262643
    0x70b04030e06041202041109030d020d0f020703030e280b0a14210c0d0c0c060e0601060801091a030607050c0f010203040206031504140c1b1204061b0b090a 68
    0x94403a0340720703045139003d80c4801400141800d0304401002e1080c80c0791141005a424040782c100300e501c51000c00184c2100060f011465081720000c80910f0b40c500c0100075050640e94040d0100460103503803807240e83c000b40107286007030100e2101da00c20840c0059420705540d035605010020740001c125400403625140240c01403901107000d940402400c0540f00d0202c145280040c0180c000250500f034003c08200221101800240241a480c08441e604d544000700700342030003011208600303d0391141d44c02503c010048241c1c810000e505552403484000b955468902c5c1c0003040f0000c00d0142a0140290300401c00d840d6000000303042540281000c0d40c9611356070f00700040c201c3c842218020360096060010540102c90010a6205104c0c0904001661302c103a041d00055400106c1d800e441013040001c43e040c01101c041c141105140350000188040e494404000030b241c0141d02541040205c4442007155041380e04128140007904140204c905080c020040c0d600c072210f0200030b41d540d00305101b802d02c0c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 531265107 1250 531263857 531263869
    0x30b010602071238040c1502010912050a0c05010f050411010207030807110f0d05011a0a0506160611071202070b03060d140f0f0c0a0e0906040b06040f02070b04030e 72
    0x89554881304840b00c04c0040104002001440004034421401c01800240329404014140e4040c9004020020155150202c180c0900108400050840e410180b81800081e01400100844210382c00e00c1c03510307040302c102e007200c14114416000c1c089600701040158103054660040c0d000e02d01806414960b007041c4d40045ea6261614417004241103030820544010605e02e07420555070100080c105507040d881c0100196001105030760540c0c080c1d544098a13003005500c0b44030440c44001c01d440f148412450200004c1a500408107100c0180a411a40c2000c00c4110707072004c1e42c006613814031551a4081e50500046140349450b426025114078200800c50181010a491180100810110111800303603200341c1c810000220a86162044248030f101015080c4030300344000c40707000b00a1684056210802c600100c1d141c0c0441c00140c1c00d04c041c049803000c00300703d0f07a500c43d410881c01d01d0305441e1000828001d040b20881140741606c0130900108010800400d40c0c05203000e6920b14100845040c00c00c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 531266357 1250 531265107 531265139
    0xa091e1a1605040e060303040b0f1803010606090b0c1c1206061d04090f20130603020907050a020c09010306020d05090c030c0f0d081b07061106220606030b01060207 72
    0x702281080c001040440c800700f4585900103409025641841d039030307020814147c3c111144605d01c8074800724044450348940c803986c000c4100128000d0261510f0b103d00075007503032558040d501030461b0000b406201c0040c20800a00000c4110403040c220307440c2108018803080150408400960030078000241c01071040e0b8081204200c003100c89807401c41503108002c0200250034049071044542c84000010500d4264400e01c241c00c10326031004001601400c000c0100c0c1500c082141140c13501100b4000360700e0f00720301070f40d00814504280d941d414003000203a18000b480d00d1101d40c803075041400841000301940140c414841086010712554580e82075440e1141881c1079569010340c000d16401c0051302d0645101c1811210140415070300210a032600411a070104408400e128a165801c0d656202c00f01711400040105251070801c0a048513040380d15854003030319014000c10403648100c20340158a0021100540c032081c02c11960390b407480d01c1000c2100900c1200051b0003185000039140b10b050403240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 531267607 1250 531266357 531266401
    0xe0f0618013e03090319060e01240501030203090a062307050702040b220f0b0622050607080d0b01120c170c04030b0109050907030c080a0b0705120a091e1a 68
    0xc240002d00c0031070300088080c0c005c03081c7d64142c0c65008102c031400c0288680c1c1044c446030881c2201c4014130032010364212015501c028105481041000503441d004154804440d6000201061041004882144461050074450404c03000b10f03050001040e000002000424400ea0341449803050038020042284220076001101c0858009444c03034402003540220a6160030000000c6c50307105440210346035401c0645c04130303081c10690b284590030800c42d411a200405085409900d88a869500d070348141c0030b00b102c60040d19449500f9605542e000351302010075880081001c10200c40e958800034944070303480703d29862004014004c02c000928410844060740d80280c8000c40d20f07440c040d1144010f0400401d180c1c241d00400c40c002c03001805100c8a40010541a40103000210007401d02c0700010f28040d0500c814013034104248011940300c03020207648503010410018080042c1d0411030841d440b0403034940c2d1401c0341c204001c0c0c20400780c22520b01c5101c0105414a000d5640c9190300b03100400304521071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 531268857 1250 531267607 531267613
    0x6161e180509011410030608070f050310021c0b061204260a14130509010807090c0503070c03030c12050a0f0b0607020d020d05070807060f0e0f0618013e030903 70
    0x46001170038030940200440354249400681196100711882c00c0808503000403295803c103078020400e038542001000d00c0c41e000300c0000c528110503456043c1840481a146010282d1100308840c2243d0300c8106840511505c410100900c0c80c5c149407036010840c9101020158444148401c50000c02d90002c1d00d400c004191a0f61503404202c5051042c40d0300107903606902d0365000b00b4045025100c3e042c100b4000c200c4c030f2005200303180c14485100d003500e2102504030b0401c5400c0c07040020700c940c41807404440e035401d810001402040c82000b29400c40d03000c5000406c4034208818081150b40326401000d02c3c4505440402c0180e05440800640d0311030004046d600030440d07640d0f080546001607501611912940031140c40b1603036030760781505010f41e03540078801180d0a80c4004c154240c1001c0640500001150707031558052420001034070900a0070a080d14099011a40d102c00d40d010304640421000c00300d100040391050402142d8031001900e5415844200400e040e2100081c0041640d8032000c000b000707 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 531270107 1250 531268857 531268889
    0xc21021b032509020d0b01120b01080402011202390705130509071208030406141b03060102010b040e0303010f0608010b0306220c180501020d0206161e18050901 70
    0x80d00107400070061450b2000e03464a000003160f803194401031241e8106070b031020403c03d8500b4005030954480707014418165051a546442603a4401d0810303510a0342400c12180c5000c0d201e00c1100280a207154110010380506025003a941d40101407160350070540300c1c2400c000c00d080044036140c0c001881401d800c04084690036402c0030b055042035512810368006c9800d0144d907419502e06203162040b0646003464000107200034000d0501a45220070500c1c07500031100d04204603a8002c82c004a03000c4042c4e5000440807500c0e0b03038400c0d00141c2c86020001c7c401c1c0915031604107100c0e1643d00a20803800c641121710000620140950300e2103040764011030440d81566621401e1110510184200504c80442e20701c0e481140c105070f01c140c01c0c440d8016a503244006211050001c00045650805810741d8052040000c800f5400514143e1007004503481d44084030940c2d009650380c80c190400c11004c401544c2c0d5804a60345d202c9420544402e1394900d402c0f01d107555605001c0349120a0003400e01c900c0700c0c070321 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 531271357 1250 531270107 531270133
    0x10617120a020a0b010e04050714060921070e0a18080a03051b1c0501060e100e03162702090a060c210309020f1806010f0c21021b03 58
    0x4003820035503419006907483e08469684086070328009030072880c0100c03105410311092100c10001c0c1002340a0001c6c0c00074030601c9910024965029900038a0700c92440c101a40d2203c2000c507241124a1100c03208845200780c441d0b56030754802c03074110b502c1603070301d07250400344001041c0807402e06004a0700800543e14103664000f04402074000240928003a4840d01c0018444125800003081c0721082d01c10303055106440502c1c0c1070242c0c0d01c1a40080304000200c1d42ca40c0c2280d8640c0c3c49042582c0c4203061060450f148840400e0410741040da0160500c00703080f400090f08003034070980381d00103410820600803008075201410f00301d000340184140c0000c8040e505001b4180a20500d40009009690803027029600013681c20110180d010202d0000391130307100c10402c40c02c0c82c0440c040609812200f000d0981c00080201e14094001040b0604004031601e40302c03110742c043c0340903028480e0841d440c0013042040c117201044100310180c0c603c3c014410416a041c2d460f10080f80648240d00c020058511585012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 531272607 1250 531271357 531271393
    0x170c07080a050913020a110604020a27090f1406070f0f03091709010f0c050a02060f0714160501171f0503011e0e0303190903030204081e010617 63
    0x3001041c01d1103002c001100455840c0081c0c0101d1200c13800b000750351150034040017869140ca00481e04c4031580329805000040e0368905030f81007a41d9440390b0b82c03039815114410100c01a6502055241c40302e02d0294154280302e0400c1c0c00c515903c3c01004408031289003910010350f03d01003190044001180f0203131003100c891051040c2444000289030108400d1422303101d18032410303518030702d071500c02c0000110402e075940c02c06400541c3d040c81e400c110300c07401115242d82c0e8451100c103000038441d600c00116130343c1c5e014480c02620246508189010a424078250450f5680d9500c440490b0b04501100d00001e030940c856078003581020300c0070341d080000d51203410a9070b60310000601d5200d000c8400c1000401c0540b824403864485d90000c20440e1040804049808101c503030a0541c80c80300e410810803c0281035282040d00c4192000b41d07400075603404681000c90090007290069600ba000320390103c504031a6450b2214081020103008200c129511210300c1e10714882c0c080d00391840d0308200510b12000003c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 531273857 1250 531272607 531272617
    0x303020c0d030c02130507030f0b060d02030406020f030c04090501051c11010909020c011b110a0b04060b06030c180109120b100f0e0901140114091f120201170c0708 72
    0x707003001c603800140c9a001a258401c0c020420317091a94a5003045442e035414018041c02d10201c0904000a10102e000302c5d01d54030907150790a0f006a0004003060401c4410350460728a10b05002480d42c80341880c61840000d81d01a103e486582410540041585d140841d008040d0018003c0d0706240003505603116018007000000481c144031064500080d54011070004001c104580000002c500810300100c0201080000c0118100814240341440080b0700282c40c020b880d8001c80f03c0c04c02030b42e0304c2c503203100a03010b40d04203560040e0010040c444414245005070031030721002066640d940c001d6800454400c44144203c1c41c0c19001000c1d88004611080492900072a04100545020351a2940e500c4c0c000d40d95445040300b611590100920303c50284a1000301004a6120000d01e500d0300f01850302030010004914811071040c00803440b00300400d9100000341ca5110103400a190303480741c50700300c00c0b40c1200003680450012400e110041c640b00703038014850101c01ba0b205040407055290007550342c01c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 531275107 1250 531273857 531273863
    0x108011505041d01050702070302011e020303041b180c020d030b0603061e03030412020108090120030718060e15120103030c140a080301051f140904020412110a08070303020c0d 77
    0x410781d143c0003000c020700815224440c96001815194510b100040c0603a21600e54000001450f654420b0181d81c00b2040701d0300315420800c208020161400e481e40841c8056111000869030703602c0561000d42e464200c0c418011107502581c2d0000d401c0e030030a400355041610740c40c0d03112500f00001846454840f4a1490900e444140c18802d1018440070038510340c41500041020500401e00310700b150790080716940c0c0310284000070300c03001c7e800403106100b00782103401c4100b27402c00100c00194031030f125181000281050030740c901c6c0d96550b075100c00b41c602d103080680e103400387c050544070840c2030020000700c50080d0005018011540e1840e00c040365004c0d0482c0c1c0459400c80c0f00c41c5d82046410040110038504c60240303940704d40c0d03545404100b0002913a9103155095098815184102e003d80010342000100042c3d82aa43c2d95810603000074000d01c1190041b05031500c05003520320034410003907000a0310742000d803140404a0380740c00003155624024440200107a0010501c40c141c2d08080754a08130480c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 531276357 1250 531275107 531275141
    0x290d080d06030f0503090406060f0e04051e040c061409090a050a020f0c0f0d0305040203150622062d03140304052205280908041e030605010801150504 66
    0x2403683d48001c0322018003001901c1c1070b84041220080c918092007030000401085c10803140110f03040348050400184003506e54440d0350b841c40098004030300421400ba0418041040d540140f42078548000e12040c64042c10340018807003403030101d804282d00100d5107048402010b0308465030b146280f0708080c020042040a0a9070280102c3d075401c98040058618400b0340d502a1409441981e00d80f0720306000081d4450401d030401c0c0510000d40c0f0040349001c01010400ac1040f00c1d030341c42c5404100c0c66040500684205120303586022243c16055024500350381c00449040500146505d15645441c0552529584131543d0001000005d10402c41c840c1c2c241c11000070b480c2032503a900002441c01414017551030102a0100c5224404002031055582c8101c5c2c00e60100a11170092941d12800440c1100c40d100195031171040c0750602001c0401c0d2001481d1a080105031000c0242d811543c060365444115a034604003000420500c0c418000e040505030500c0315003140d14a800200070142c481c4403a08540d5031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 531277607 1250 531276357 531276359
    0x8160605010e1003170c0a080a0206070801030f030522060f021606080613060509070f0e0409030f11010e0106080a0b0a0501140f0105070b04030306081005090d0806011e03290d080d06 80
    0x180a0208020050048d01038039260411441d010f41020300041259042120031001400010551814943c0030b51f094a060342c0c03103408040075a603900d1a01c12600b000841e12000004003164013071780300c1070190b482e90300742c9410519504c100707040c158040c0a100007240405002940301c0c00e05048010645600f0322011400c199941d000c070342e006409481e90b600080941c041099200c2e08030f0b1111084072003e0701c04204070b58054800504081140240008000e4140c81462052509400115411201e113008000e0300341d540611a90f500300080f0210382c1e400d0307a9000101402302920400d4122484440c0b11451400310000700000720720042ca400d818044180180b6003c40c02c0c5008043c0f046202e900c00046276400d0000c6249805502044080818240420054500c0d00810541220703071460a05a40340d8a45030016150503000607180c0c4a00c0c18902007011100798143c00410124240d50020000f8600c03014034500c03811510325403190000705008544001540800003042d042c42d00d590001842c1e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 531278857 1250 531277607 531277627
    0x60b0a1d09160c0b040803182a0105040302090c0414030304060f0e01031407030509010b0d111507050604030c020f0a060f11010608070902070b0c0310090509010908160605010e100317 80
    0x25415030301a250000c000c02040300e460410a8aa0400d4a0708d2008004012810000d130036550002414402c175003801f0084c940316a4040c00544d009994014903502851401c3c0210041c2504548662070810380304001000c1d4a06000c81140d00b0384850356140c0a10190241060350390b1104c0030a0305040564421250a000500c6c04906003e0000360b030703002c0303054117080c10f00c0c500350b500300c04000d0703c00c151020079540001c1701c0390f0550380017100c15603500075004404041e0004030700448002900c81e024030410007042503402421004200c1c401c89400303802070130110134046010518065000403c05004078038100c54000e4180e5845880100004295551142c1d00c050501c035081d444407c19580114150080141c122021588003101c0440c903811482c2030001c03102c3c00381262042a02440d03940f004110300c908203402c0000d4490300010031980e1900c28444900030654540e00c00d0b50302601d480b0002c0351014401c641c40e4000c1c4c0c52284642400360a584840300c9604180f11aa182184200704840388 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 531280107 1250 531278857 531278873
    0x1020c060712140f090f030109080f070308010f030c05061810121d0717160608041e051015030c0f210210051c060b0a1d09160c 56
    0x2244294042204070030242c8019100300c00301c2500d1485140240844c4482a0100007612a0740b602103510619060022002c030b801800080b002400320000015810b00c80704116005086441c869a41c00701c440c1e07a110a6124121140d01005000240d06078040006280000250402607100003180751a028a10f0025407010303c04d101e04008500d000f19070f112500300e5841408101d0034840d6000c00700c0c00d030926485407180f00b00c1c003402d1482c0d00301a1000421640400100722074111610400c6841c68070b4040181440b801150100c0d00014009030b00502e509528522812441d0f22038014410f1a41c0c0d100072401070b0202c06200c2ca01d02c2040c043c008081b4400a1596006159242d0240d80ea541803900c19044483c0798450058207071410702d66180143c9a00c03c0c01401a24a89405500c465075001d868560b50014a6181c0180741007050118200360000010442c0241d01d41392125a18505030000414947d54084150b01011300c40000750916404005012000b1007460101c02c0140750742e9a0302d0b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 531281357 1250 531280107 531280117
    0x1201060e040b12070617040b04081608041e05121513020306010b032205251e0503011b0c0b060604030b100e0609010b03070e1c08190305060303071101020c06 69
    0xc1e01d07601031300080000c15042161801c00554009142403a450a034a4503424408080c2c0300820008000034814030540c0d03a1700040801e60340c080c941a50700e503a145070202c1d000900c00c0b05014442c00c1d004001a261822a02e6034011001c0304015001c3c0c141c1c918080400c1140041ca881d0301c07500c003111004010394046c0900d5028000c0c00880715244c0c1402d419040340d84610703502c00c003401c102410300d00c3c000c00e00000b0b0b0702c49451440041c18100642044030380022840683c0000e076004100400b00788000185110f180030b640055008008448100030980c141c500c1c1c0440480c0072503561002100030845280a50750700c80710250120345004d03943e41c2c8070099504122010a8400c1002005210360301e04514a95001401140c1195865040804040c80341c4406000201030000ac03101c0e00b2525291080c40101c80e940c41207803050720145078104010280e010b5401c84400840c0750001c3c0801c14080e10409015940180080d8200b4171150742c0e15812070b422007007060540c0700d400815500c0d685d031500102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 531282607 1250 531281357 531281389
    0x1207182d060e011808011103010e01080a03050301090c091706040203210409150e010b04140306070503070c2102010603060612050c010f02011e0c110a03020d2703140607051201060e040b 81
    0xb03660350315000f1030301c10002cac043e00041c0c2990400354081000c241d01a06036410f407101014009103d07000040c05440c0044181c0c0580042d083d11544001c0a45000c45c0c0c1c10b00c59402a070a440f000e44c810030300c40484d031501e8030804000044c24007090240801700e41c001c0c002d0034268040340c040591900e0a51861070000d9118800716440040d00b8024031019080c01030781e00c04107030f00410260414900103071007070100420b04800c028070401c01d1303002d101000d035412a5071250400c1a58040d121604020301801040c00b081d034215082c00c4001928022003041c00b205240c200c400b900000e44c442c0d004451041c01e10450404546d00e48102048110040c41003400b80c107000c400008403200e00002c0608415404c01402443e600400700030350209401284100b850f044600d0131038026406419070b0382d00c004402c030200c0c61043c0100700100800440340182c2d410700e0968002c854066072001c10440f4030348140218924170400c203000401c0980e000d4400f501d1294002007002c070b031411804c00426000b503500b12180d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 531283857 1250 531282607 531282641
    0x71406010806090709090213092301270c03080738010b031e130b090102030403090e07050a140405040e0604020103110f1207182d060e01180801 63
    0x40210300000708445002001700c400e0500013003045070000707402020403004003c0090703280c40f41c0d2800c0240041d8180c2c140500d100d6107000403200000024024190340c0b10ba044070444c20b1200300e0b26580c612100660442d44924840d0031700c1c0c00d65580c104560800e4038112400304401158000e80c1d038141840f0340342501c00c42c040035201d000801828000140c10391120003000c2c030800910103800c0741c10340b403030558600504082e420340e10f800c88a8038107600800c00144c9400055000d1001024042d0010f50240d4020380c0d41949140e1a01100000321000b560120085003080100f1039602d405400f00b01e0501d102d1004113402d050765500420150b5180c5d160305201900325200304011584c041c458800d440560720100c2e07052480c0e400c59050a4462180050302c00f80d01d01002503141485484182c41c441a1011012189991101e010490b2680712400b03000313840158038041c2c600ca0040c00980111040740d652000c4403042c0c00015200040c21605030381c107240b024000070420680c240140e4848200b00c14103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 531285107 1250 531283857 531283861
    0x15140d05150c220e060f01021903030209040b0a061e09030f0b0f07110d0503041118040303050708060a060c020315010f0504060803091503190504030c03081317071406010806 76
    0x103c040c103540300c041d410909500c410511050a2081e1104e0303000c4025603040440c1000e40300140d107030407400e801c1c01c550680419082400c042e4950040d0020410130b840521800702c0305010010001c1c000c1c052440007440421190502d007008903c02d40861100c0d04011400700d4494480c1c15001c1407100c025290801110280540d588038444815402002860300c0300b9000040c0c2c81c1c00e521210010751038001c2210100100e07040c00301d0106014a2140c00621441c54510300c02848503051100310703801d4000c6450b1500007041a0f02400209208280c0181040006410040251081c500d0540c041e41c0601caa054101d10000c0c0000c03181e406080c3c910b10030003142e0300d000304100c141d40c0207400c5117001d504144500012500d03003101005002100082294881d990011440c80b000ba221010b100480d04100600003030603000006482c1c441c0c06691021056958043c0c06e8420081c000d0380100501403800c4010540c01c5e604010384629803040f4131042000c0b0800701d40b103203001d4013a0000803a41d003007001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 531286357 1250 531285107 531285127
    0x906030c04090f270201090b07030210020d0903120b01051c18140705120303011a0c120d050708091509030c070e07021e0d0c0c0503030d0c0315140d05150c 68
    0x82911000303d01009020180b81c5070300007005843c1c2c7c3d12500300318030008685a01054000d020039802c40746c07140c000710b44400c8002d070041d011b0004840c040d80400c0c10b0041d068102c440b2409800b804110613141c0c680b6240c5400c5a0400103004c040e40b5003003850366907d61034a541001640074100600481d11074440b00c08104d140d40c1024425804580710381c01c14490040c00544c0402528119410300c2d40c400b40c07034280c051480590f80f00b85e0303840200750300411001c05040b4881c040502091b00d40880304106036030b5207803001e59a40720140c40400941d40022401c00d540000011144d902c00040f4055034100704400c44058a000c031513401c802c02e040c030400200103025504100d20b5021505610741d40014003442d180d4543c44401d40f040106c10451014440010301c000f030740d0510000c00002d002c8a94610440450000826200c050040040c1c1401c030424a038030440360301403083d901202542c1071140070050410980280d41c0104440e0b601504501c0c0086205a04180740b06e0616400712030307540e40c5544 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 531287607 1250 531286357 531286391
    0x903030605030c03011e09020f090c0301080d0311192304180b100c1b181121060d02030111070611031012030309060e030a03060b0901050906030c04090f 67
    0x803d40c00d02070780c50700d64600c0c480a01c50981b0f15000c50311040010b6640184e0011070504640518a203400c41c8503d000d0003081a00300f0000c504070b901e581d0a03100d04648141e42103090301c43d285d84d00454450306006040210040a202411036240c2e030404a500425212155060050b5402c25a0911101007410001c0e1f0402c00d100f080c005800030400c001c03950a1a001910f103100540c114410080f01c00414000c020400000c8480c009202604052550780e41c05801000b81c04869003640746070500c8940305840210105a50201c0c00400800300303113550b200c106680b4410010610342e8424850401040981c400f0310840c44000902d51155607030305010704005094444114808103010b01c20410013285182048204090701c844221002c0905410f04045000c5d060000c0e01030500c501d402e044da4141c000000003015000410b450910000d55104443e121600401088501140d010407200384a89040001183d11101c03c0041c10705068440c248401243da8400d001130300c0c1c554036403034844050207803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 531288857 1250 531287607 531287623
    0x210060603150504050105012c04090c03030e09010609140303160803100e0c04030b07020f100e0d031b0305060d050d02010203150603040201142512080106021203010b0d0f090303060503 81
    0xd13901405907514250000300701c032210500a4000110706151803510380d40d2460043c5aa03203000700207100454a0303080403c0894043e100880129100da4000003050410764450350403500c1070307115003c805d85030080801016031001c2801d03601d4002004008a6100b0781051110458001c40e0302e1a202d10704100100c1c2800c1c4a90000e0201800038010445040c004c40115400c0e20f038040c9604045031602101079181c11422429080a4058540c04204020055025000c100301900843c0c003412808903003907040f5042c80e42c510380350080c6034103201e1106019805c200e411182c05443c03485849816140c29062511040d00000144d4002090040b03002042003192400c8100b112128910304007540080c1120086e0354240d034096402081c0c01c0072b40c504240e80c085440301203441680704040306103800c244600c40e1080359008178080070008242e451002808121540e04100450300e1642490500700d115000300720384541d160345940080000308501d0040028440c443d46002c21070a06160400d4140020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 531290107 1250 531288857 531288859
    0x1303172208120f0909090c010806040902010c06090201020309060c01150f24090b0f09041104080a0803040203100c020a060b10120e01020424030b030a0b0f0702100606031505 76
    0x3500c80600441a0204804050140c06101181e43d001d00040d4641070740545415103900001820420602100c0441c0880c842d0030241e9034409580d480c00304000440310203020180c00540404281800a02140c0c4540521401401120704201c0d44100094946d489500c0c031075103594691a000c1c2810b0707840200320000e0107032148092900390401c4401e418404800000c1110b004c000046801024051003a072809084260b8106540f82c0701c0c2000ca0040b5030000c0c850a0180e480c10480d040c2d401c09000c240c07826200c1410152043e0343d065150141d66070000381c0181d90502031640000f00255a610820300b68003001e4016118502e035a0420340200c42d0601041400380c010426000c2001d507120000402501098900180d00c2c400c5208035030081c01980c0045140800412a142c8403c1c0041c480d20301003a0107603414000d05403030906040c0c80300d481c5030000b054100c060000c1402d50310384402ea190320401a00c102e82c1000e02e500c071080c086e529182e1000000c81d50350107058003000301345404035003d090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 531291357 1250 531290107 531290167
    0xf03021e0411180117040308071416020102300a12090303060e1807091e020301030620040303090b18181807141009180b1e100302130317 60
    0x911409035290602c0d00600050400c8620b48c006103003240660080d1054418101b10a03456400022a40d038880c10031410a90140c46824142040c2c00403020602022000d1118594840d5513140e42e0441503400900407a0701703216040c1d00a4464003420b10540071448d000360340c0480c0702407500c00d940850107030160090b6125280c03400e0078204918005000b204491541e000040c1d001250503c0e251010034070076815079207a0000000000388420341d005810098170701c4d52002c0800c000e01031440410301ca144401004501860740c1000211811000b40004403030244660151742001c2d0000340c00c20310600c0340c40f06080082c1080c412440001e45580385442404401403444905150f008104800361001e018850507800f100c006400e40f18400c54030007051080c1c40800325070343c40900c41d806092460b055601505119001e81e45103588017808001c00b40d806044079044100b260011006988145480003c1c1d01c1110b10010001c0c045141c211b042845040e076013071304c0c0c01074a10110b01d002201c0083c2c24040e8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 531292607 1250 531291357 531291377
    0x100b16150b1509030705011103040b1207030c050406020a0b060406120b07020d050405010e131b050421020d020d1e0b0604050f0403090b03103206040f03021e04111801 73
    0x11300d000130200d066850900740b0800031011500e8242c55889a90004400028041030110351842500718031802501c407a103060284030384800080300c0745c2c002d51013444016231144800d040840d80040065400040250000c50382c7c41c0c44051071004202100001c80e039001d0000c0c1000b212690501c18a820405280341c82c2d89018034006c0020445288000124454048440369691080141c1c3c0720580003460810100a03185c608030000d4003d80151003149100705550035001c11340729151a003070314820340c002c000e40800032442c0c0a00c418403440003c01c0b180455000b6420201c0440c0c0103101040341d08c210302081c0d481c646242804280e600280450030021b07034401c1840002500710103900300b03560408940d2501e0b40e40d508580103002c5019880b010540104150a044804484400b80004402501d100b0700940c0c4500510405211364441e03400007020000302800140b920402520740507051007200690781c150480043e0480e0745e00c0245643d4400300041650b03000440d806150000c0c00c0909041e01c2032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 531293857 1250 531292607 531292609
    0x6060e06040501082205060f0f011a03130803090307031701080c0d0807060501060903120f1d010e090a0204080d1b02010f170108030c0f06100b16150b1509 68
    0x900079802801e051120000005415540c3da2082c481e10380806a0010303840c07152814084c3d02c800090b14001030b500304240010b0000d20010344c1c00f174122050004c10111088400038118140c1c1c1000d0501000403a0050003580410180c20140d401071900030090741e0350754003502d0003804c40302a0b1196074540220325001084605404142021103032415240c0340e045035407504d04404241b20700d110041189140c14008107421354808112402c3d60b2080040c915444160342c010340b149600910310800140305140c0500081c814001c1c00319014206041242d040f4401c0c000054011600b2550611019804982084403081c1003110507800d0f5154103101301201f89a071500c8031540242540079042c07296000c12025030754864000550303001354500c00743c08696159110191280d01440040340e45200d0300c816030604d4080441d40c54012000780d43c030741c011145440901c150603044519650346602202611070003050182c111048140c80100000400c58100b10800c0700d401040c401d440c01c20341041c00500b01c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 531294964 1107 531293857 531293869
    0x1c02030340030b13050a0201140f0408030a02070f12020d0f0501091410110324030604030f02190b060906041e1a0102060f01090f110708070606060e 65
    0x42546a610060a224483c130704090619001008110b0041d030280c20404100001700c0c030650b081100c02000c1c40c1c1c450b0450b038008080340d00b00180c1d003410640d041c4010405451a4403c4144290412800941c11000b155000b8040c440301d01c008400c0c0b00b01d00c1100c40d08554014024070101c275151514041990508110701082c0c410105c8160800940f4007480012800c4c2c04001825035503042c2005000012504070002c40d5640f0010381c60598505000c11442a40680c4aa604811295100900d4041c48140302c010700205e50b07062800040103144c4054021030101c5d01d19a0648403080000d0080c800c1302c403000703203200c0701c285c182e514860340f90040310350f007940c0900c5041c0c0340701c052005a0701c0f444100c3c1c110785c0e4107040304010321441d980da9000701d91140d01c100c400180c11460088400c0d03590320494050710b0340200450190104103041c06003201902d502e14007458941843e6002c604 = true := by decide +kernel

theorem cover : BRFrame.Cov 531115107 531294964 := by
  have h0 := BRFrame.cov_init 531115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 531115107 ≤ n) (h2 : n < 531294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
