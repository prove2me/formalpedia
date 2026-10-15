-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3996
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:17:12.676979+00:00
-- url     : https://prove2.me/submissions/86814ca3-5bd9-48ea-a719-423aef3f2ea5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 718525179 ≤ n < 718705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 718526429 1250 718525179 718525189
    0xf0b0a02010f02040602031804050601210608060f100501170f070e0301060f1802030c07021203162f010f050d11190212040803030402010809240601090609030c0b09 72
    0x400e08020381155145c3c1d540401a6423a0320a004e00480640d2072000355255150038801c0c03501c540300c1a1100c211360b14051070171100215a441840c0c02d000d5444201040b603071030800c80244200242c402d40c82e0170341080852540c8580da0b641c022410884104508000400c0c40302c4043d411149050006284e0340754418142d0703503249840b20b0340307402d503203001800550b445018100500b1503c14240e45a400d000d180c090741c0c16880116004601840f08000800060514020000ca0500c540341030768108000442d500b402c038401e003003081c0c82c0b50715903001911146c81c15200700c0c1d00504050074600301002d503900002c3c054039070710724010040c0940880c0048110009401605107001e1004a1039564445000c00140d501d80c0300a861006214002c000800c10a08800b16000d135441d9200540c00c5981c0c076401150801e5005041180701e000b405101030440c001c0400140c040c4804401c500003520340a40010701e06822580b2580070898061002c0020511241c202419503400303040300c0c0d50b15190240860 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 718527679 1250 718526429 718526441
    0x3030f0c060e0309182418041505061f0e030a0b01030503070b010501020307080f0a03060b2a12070204090f12020705090c0910120608010e0f010f02040f0b0a0201 71
    0x9011942000c0c082007840c040440104007581c1d04440044000001003082c0244104c221091440d00d910400d0300714011074494201d15006100a121f2511082500d21904118000b5a01120102c0c0340e281620b417004410b004060340b20b030003074808243c100001e6010218910040303900006101c00c000711000592401c0c00340d04c0d40303030b40c0001000846580d40c0c0303410383d541e9200310019a0b851b4400e000204896101000321403400d0f8101c0c41305030401000340a0f1030182e40c8000202c4092642c2e07103100141c40d008103c00b0b4100d00d480754020741e0741c01200421113039981400708640e0010b030b040b07030244031480c8046078140d41510303405850024081d411864000d8080c661045c2c0036050034007601c19a100c0e598000b8941080c0d44041d01c0c03502c0c0c541c803081c01c0c10146001380e00c903095001480b01c00c1c11850500c240814410604540c2010985c103a070303252101d08485084202c0d400d0341c0c10491100740184030034003030341d0004043c1c038904626041c40c0c4104a584040c0d03502807000d14510001e50880703140d10035002a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 718528929 1250 718527679 718527683
    0x1509080d0c0e0310090b0109020d0b090a0f0c05040605070f02031e060106030e060705040b1e0f070201020613050a02090c12070804030f020f0d03090215070605180303010b0403030f0c 80
    0x4101007120000040c100344641241d0380e2003885100d018604041c82c5006030303089164000b51102050342400031400194000281c0c0b20141aa290f104a11983c0c6000c04a801900050300025003119000604800c2d03480701e9400c0001d200c0d04020802101e6400011210741c6900025603020701082403000074200b0901c565078075041c4030f01d01081a42a6404503042d8100c82c89610200b003c204403070702d40341d2642c400300c5514020480c24042040003e0810008120102890814140d4040d6080040700650884400b17010070384400715510086507010010300b50400180640340140c8032940d91255035038402c0007002030280c88200c000c1644901c8000030746410f00040c0c1600802071501034002803100303004403025000110700181c01c1c010540042035401000415401505090303141030b03070a4000d84007010040360005446540400d41140c3c100240110078422030b800709180c103100540494200a01c844500643c100700010000361032620211011207a01d8104104901c07594101035882020000c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 718530179 1250 718528929 718528931
    0x2190302010207021305090d02060402010206220b090f1e1b150c0102090f1221040b130f060207210215072103061a1612031b0302071509080d 62
    0x1407080208590b80001c7c4c810300c0000c080351280320f041a4100e945400580380a130140c3c209801040b2643d4020307061030091010700e84000d007941e003940ea90195a603022959030240750400c41300120035480a2000401d00428102862035003105c11840c0b40e226040c0c1d450404901e007d0001c0941161130b8481c0c03007000403810911103611114522066070107944618001c0f407049000710b9000503689804c0740307058140f05000700141111800e01c4041ca0019a88000e240c0c05010240000910000d41c03030018030b5a005401549045a490007241b9094441d0360381203e8107540000c1001d1209010b007401c9194800d2184c15030101010460000c40c1c0a00d241035a000024030000404030244500031220104101c1c02c5505860300c08140c1c007044089510342e0041e00702c9009005c0c50a2860191710cc06810201c0400c4c08a6005403032a5480103c0300c01030800070f0300801c4c0c89100604080740450084040503c00c0d040661801c1059529020b49501406106044070707903800112086c08401d205035100b10b11781c200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 718531429 1250 718530179 718530199
    0x16030303060303020c060403081801090801110c010e06070507241b0f050306030304051215091b0a06080a020c010f020307051201120b0c07050c150d05160219030201020702 75
    0x140200075040c01e0005a002d44145803010306503040104c00c440807039401011030ba040100007003141c00340303640e0b085015040000860700407800340401e2103041c2c00c0c09003400e00e0301e90710000034140509485c0c828011400c103410a40c1086a01908035084070718103984001c105082d102001c0c0d045404143e240142074046191100d040c01002e0302900f100380174840c07500c9a140701c0004074000c682c0d61008540054241d0002c9c0010011410001489054686c4100c203446c003000c2d82e80c0c0102e0400d235045070711410942c002c01d400c041d9400b81e20f4904540c0d4100750b0f580221641091000f5040c010054104819103a001071210070000080d07226049074415810195078a0511040080180d001601d08a00c1602181e0001500d0040c594209440c07a9206070410810b42d00e00140360203030307007201d90142c445020f1800b109c441c0d941c4024903100300640c5800503544980b007030446c034012640700030300b800c252410406a588a60b5000100c101680028003400b00c410740552034100c0c068016030381c00941084e0700031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 718532679 1250 718531429 718531433
    0x4030c29010b04090b0a210807021302071a040203071a070203100e0c01020120031f0e01060f03090b0f0907031b1a030106090509270a0c171005091603 66
    0x4001312124002c040c00103c03844420080c8103a0544940c0751141c216a4108040c42130b11180c1051090041d1a824249080e58000c98082d52819558603a1680d000411408020340f10100300540c1c4c1c802248070111b443c1640c0802c0e55804180101120303400901400d010340076419085501040e0701a041d1407031b0307103070528029000c1c05403500410300383d001b00301c4c1d10b05031944144988448044025401e0b03a03183c81c0c0040410340d9900180250302c051402003007808200461a51101c010514825920001e40c50014011302c05241d54041500b0582000c2c070480100f90f61030b211320b40210220402000c0c2e80c807440034051802c041540020290025240f82e12030050000800e0811940e01c0c0e111081002030312188248284000d0040c400403a030750203c1403100c1e051203200c9680c04151202c41c2d090307102e041da03110901c45529001160065101c64401000c008040001030014010b200c0b000f505004890100342d01d8881003e4400c440c2ca941e0700002c0e038030150800050550744485881515095128 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 718533929 1250 718532679 718532699
    0x3080a02060a1b09170f0d050301051e091501031806050f102108040b0c03030613060f09090804030c080a0b0c250309092c0604030c2901 60
    0x1101c907100030343d2500c1030720034280030302580c0400c1120300c640d202c04010741424046402c001048030040340340e02c5250304d026854001001000c0440c401500d9a0f42c8941c500300400400340500c00032103608000e0803c0d1060280c41d07042140c2d0b00300034000da0202e0002d182200403001000c076600d0720090043c1d1025500c0620019500090140c00800d100d04080d96036005003005054540c0718800d00c074403120081240d0020a4040716840302e00c42c008540c6081d86e5088014150381181440344c503950400018809645060402c148010000800901c1000d2501911000c1c0100603c1461416034807648000204241c00c021100039503404401000c030580c0f5484416590401d0749003c0703913003101940c04034aa0410040c1030b03030303242000444005010803d442440000f4040e0500c210184143c0b4880402e101201d4000c220041040e000c4a84901001c0400001c6100c0c0c090880c0081e40c01100038040426406034107140382c20780140c003243e5015080c060030184c035078841310740c5111000208004201070300c071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 718535179 1250 718533929 718533931
    0xf060f03061d0a02010f0507020307090f2405040b04091e051014220b01081c1407080f13090213140a05090709080102070f030809070e01120c03080a0206 67
    0x24942006488004035800c1c140100c04030006800741c3c400410301c0019031145013451040c000ea0314010341414502e5011900d030041c00d400458225807902900f04c048680e510801200c83c08103001504070700f03915490f20b04c60443c1401640d00444d11101c904c1d401d9182c0360000b284142e44005403042d9480e1100708122080101041190580034151454902003041e010340d841c001551070f4610100e0700c03500030207481088010030911524046550303a8010900c200e204c02e00034501c44e000760011405041e040100d602420228009202c0d04c02d0781204000203034010748902035840000c490340c40a40b861440903902600442c2ca07000030088601180d00b02c541c4e005440402c0729280142d104030341740c10b086000c0d51590004d158002c140d2043c10845481c04120050b08521a070500020258440c1203403801da900c054400d507a1810108030450130140d10401c05c540c80341c0c0d0500500350050504604844507074041c0b040345e0240c2442c680d01b40038800ca1345d0b5070200643d80205a29602c50070210007a4031144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 718536429 1250 718535179 718535183
    0xc03050304030c17060106120b030609060403021905030d09020d210e0901230a050a060e030709060f0308071a0f0402030d050c030f030a0e0303190e0102040f05010c05010f060f03 78
    0x2098080c00141c4c070f520000015902c50b84800030b001241c0c24084200c441021101502400f162a00130307050164070217000f090300403640400601500e00d02418044d01c2e18940c0d4004c0b10501c0c1c521000c000c04640e000c03044d00c2e4000e20844000c200040c450002811080f0358010107041a081d80b0401501e12041080f24904811151290f84103860807100300146918240b250300ba101886060300400c1d0b0384100b040319181c100c004c1075000e006450790003107040301d18150800008210403582c0c04600d0310b41081000d00a200105080c0901418903030551004421480b0042420300086400e108001c070504c1c0c491040202c0c000510541d18145400200c0c00106603410b074003a0144130b01c1c0e6071405100307408444420b02d07944011864007100000d0340c0100c0e4801483c1822042e0f490821a40300312040c00214010108500042c07855220b82d4100c504468560580054070b80c4100300400c00350f442010308400301c41c1c0900700342c58028802d041c00780c058014849030b403402c4e500d0b1540c0130541202135890007082c0c0e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 718537679 1250 718536429 718536443
    0x28060b060c16170c090f18010501120b0f060a0b0a0c0515070f11190212070602010902010807080f04061a10110f070b0d0e21040302010e0603040209160c0c0305030403 73
    0x30080f0003180c1c0316022441001e4005129500007000c0780802d00700c0c25000710001194690000c0f02905207400c5480c02e0f040840509041443c0a09001da0041000e070002c94240d40080507080150002e007a06442e40304281911308042100702446016000404019411805030b440300e0709071280c8064503400850356900071440c1041100e4504d88900256a41d00780602c0c01000c40a0b40c072100d42c1040415545c2c102d82c045d8a00c2c0142040440901209000b0b012980000c61101150300c009800c1c450002c03c01010403007800100501d400d45c2e950a9900250049000100d200d007180d0301907150902058920742100603603040364006a445901551400c00f0740040d50ba103200000c040a0319001648121100540c0c28001d0180c4905994001c0314403a8401d001c850b440e03080c04400462801d80d0014480128001280402c00d40d42c00400c1c401d90b400084607142e143d841c283d80010f140000c017030071540403c40300ca2040240c140c011a10b00702c180b038005200a010564900e0b00c65601ea20a0000311015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 718538929 1250 718537679 718537709
    0x30903120216020a17070b03062706012007090b1201150f090c200f070f05090c03010305100e07051801140402090d140a02061204020328060b060c16 65
    0x20f1080040d8003102c0500d80006d0402286030600003492130b000544026030009040f0150380c0c1d10214008200803170b81e0403201c2034001e4500400050005400c0580070542c0c000c0991044007210404507200c07058902803807000420400d040b0101d80c0403404030310340c141c0a41c42c007401c2c1c08064410000307407000c82d071032240e141045d1511100c5c0441601c01420061010507242c070b01d00c901042e11048480700380c04156080355480300c8012001403500300e665120443c00740001c14188054140714004c961311140c410055880d6514582e2465a544c40415000348140e030f45400c910754005003441007000910000704880442e006200d804d035080a028400d01262a070809810070a5081c140250f43c5044c0c0000e090f1480310400b41c03103070f080e4403010400c2480c1c40e000311101540140e0302c0c0d03005000c81e07100415a04040d0b24243c0b052500e006120600c0c140310800c1643d03542825984151545c4a480d4030842c0803c0703611900000c21a94041c01c900a811402003d0218029002d0070544e501107500c44070300c0a00c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 718540179 1250 718538929 718538939
    0x91502210f04150204080d050f0d0204240206151c061e050609010803191b0c0e06040b0f060c0c0d050c1f0801090e1617120910030903120216020a 64
    0x491280d80b04410451f007058403401d011500440c040c0040900607030382c40c1e140901d1207046100303d07405074105180c030204810802c07084980b04000642c542290340010708103401c0c500300c026016040d031040240300e01c0c6011003080c13110741000002c0e01c201d60b01403001d00c00490181494144058001d0070724990504c0c1c0400143c80e440c3c14540b1904841c2d13408069884c0560b12076540d4111800751003040c0906c044100500c50498051004a17810ba005401d54840c1d079091607a840c0002001130850307803286007820100c01d2180e0310350320b000300c042e03004440c01540d4022000007e8209188840020703841515002ca4000344080400d01301e0b4590001c0b54090034031600c01f0503c12510340b099002e0300008002c2d10042c8190b1400707500c139020804c0c04804950b500031a003514516540040d801544c401849201c40d113180300802c12038440c032000784000c4107050507001404110305c245402c001c0f104064683c81c1081c1810300556001151124030714041d5540c2c00c404403031280340051000c0403800343d40d2071200040c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 718541429 1250 718540179 718540181
    0x1e090723070b040210091205070509011733010e041e0305070f02011b060e06070201020408190611030408091f0c0204050c091905040e01091502210f0415 67
    0x607155a2018107000075032115001c0c4001e11040b444520180b0403081e20208111071058142c0440c0d501c0f6800800d103035400c04041c041a0304c0182c1c044411800b49524074202c121002c00c1c0480c5d0f2100001c6080d41e0790342c64151020301d110804c480306620b0f400c5440041500ca5028041920441c007a404921217200003c0400040030b10003440640083c1c41842040009440545000000d500500d0800359104443c421000c1c0c0d800c1c1900100e520680c2c910102c0c0b00040c05000403a4840c07800d000071402e2a14080005440d400c00c10f04410502c0707160b103000b0040080a520003001b600221409940360303e0b00d89031140084d402141200d205031070880020f10b100107000c0040801c918a5501c0038410b10b41d48d800d02000d0000613000c4005a4414007079002c1135111032300d8a13a070620700c5a0b981041e8900c0e2a0a010440d124410056000c1c0d05012a4201180b4400988442594103110050751900307030048410161000100c0c2022020f83d06003409107200c80780d8007003030080c0e0040c081d2168460203030031154 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 718542679 1250 718541429 718541437
    0x111131d0f0103030e04090611090901050301050c1c0e0d090801060b0310030f15180c0503030415050c120a050405010e0a0e01121110030e0d08040c051e090723 70
    0x4140e03001c210018000070f44660301c000da40072000b0f0008580d000b85661007005880703000c80c81d0562020081031201092404103489401442c00b64000c10003418004d0b40410184070b080e10f00d0072500c0003104084200701180e130085506000060940d00c1c2d4200d0715100070710003580c602c03401e6410340c01c0c040042400700c59202202d00403400301ba2918400b41c610354401004c030140410a0b500c4002804042d030b44104240100c8856400c00d26044040da1070b1440c040e8803e07242c40c0c0180d8084d62040c8004c1c010104403c00001c2011402c1c02c080b526500e00170b2182d85009007022a000340031102045c9030f150030740c000300a0b000b40d880c2600d0b01c0d40140456028010403140902c1030103130080010004004001b00c03000003a41e40e40c02000000000c2c0b1440700402c60b512112200345001968a101100b130700c207024440d22680848030300d040102d03800e0546a2041900c1c15000d228416a050140c1d01200d072805407010201c1180a051415079140c40000a004100700045204619214a03840000000c2101c110703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 718543929 1250 718542679 718542691
    0x91e030f0c0913030203070c0f090e01020403050a030c140a15050a020a09090c0c1a0a050f0c0301060e0a0810052403030f07030504051507060b120a0f02030111131d 72
    0x80d038450ba64890f0044101d10400342c15410b40c0420400b01000c14090382e1940c2c090100f4480801703002e450603180d04111030410082446ca81d00c14401480010408604501003d40510b4414501e081c1418038500e41405e000e0424154031941c0c0350381c070811004000d1403078403000d012001c1005941d042d00f031005902c50703484403c00254a030034040c0901c50742a4000044200b041c54480b80e100502da40e07810070169807009560824500004004603848a4010603501c400c8004140900e420301803181c0013a0f00060280c2c1c001e0212250f000400340d1203195102e0001c00304a4220b4404140d10510700000f0308040d03c4e04140e0242c0402140e000e00c1305000d5888218201a00440c84c08072800030324100c0303420540c7d040b02000800c100002d2296a00e0804070802c400760306040c1c0e5207058a240c0002264807440c81c03140100560820180758000210342e01c1c54482e08034200c00d4820351548000b90044c08061030800b0821000f04030140c0540141c4180400d4a14400303101044164202036646005011902 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 718545179 1250 718543929 718543939
    0x12091c1707110c150c07060216090b240a08060118090e0307020312180405040f11030f010f0605121507050c1603060b041503020f04090206091e030f0c 66
    0x4100322a115007070b1081c0911500c002d8600703181d452000615400804507070310103072000200701040302c80310070300502c4000d1000c1d000403c1f0700c0b641000d003040e2800c0c60384624034656035284030016030390300d804404240700941c88410039610b019100000c40170740c103e2480d600000c2c0ea104001003240d409000c1c00740070422404110b041c0c442c07030001240b015101d64085400c06002c2400918010385082100702c8400004c524903580b28102034003522030840212801314441ea040405110120b5002006d401c68503400c500c0c1032040400b80004280781041d509d20703210301d80d0300e00070b4140d4034003030540d014400b178039001c580554507408284035465880c44400c0302c4842820a22001ca600280140010200ca0528100f551045054030f003410700a0455a8015284141c070f49010a03c4da140500c00c04d06142c14054000c2c12150031500825054906c0648103800745546500d4801595100f00a0f01d025904c010009003000c8d0500140c040801a46424940a8810030b03045650956020403010040321014203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 718546429 1250 718545179 718545181
    0x1527091a0f22020a12030f08070e0a0b0304030c0f0b01060f0825090b07050705010305061804032f030406140a0c020d080f0d0c021e060a020c0312091c17 67
    0x5201c210282d05080101d0b0b1140d0300020000e541c01d0110200c140700f6010340c8403041d84084000002d040b85000502c10707001c0080711207600b07039613030f88482500055800201c400c0d0788030303503841c0b506840521440c0c20180181a6400d1180200000960482d041c3d80746595221542d03000b182d019281c000090380c4605484054603a4103a0303904801c2049048503d1504c1c1c04030055a40760605182680300303100546c0d0903000361000f48055605800344c2600200140e4419211600941c0101c407400b0f000b9000a0070031941c0900d850070014806c03107442c90b4a16404682e5104240b00704240d690340e000d0b204040c080b9604100107440e00c400c04054035039002168458402c0310b47d01d9420040c20703021192040314416000c0c01000c0202c140c81c0040d0489061801000500c8010240c010340303425850314403030300e21a4041c0f00c403101d09500410782c1500000180000b5032240c04440519046004041d01e02c10860203103410880e070032200086142451400e903161150f004c10b0020120340e070f0841c4e60401108400004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 718547679 1250 718546429 718546471
    0x1002010c1b0602040b03041b1502031b070b0c0c0312070f0b0a02070c0806040317071b0c0e070f140906180f150705060a1527091a0f 58
    0x81d1401503403500c41d660040ca40368407288118116002504d09035000c1444100b03805072000303070408280140048804803440400c56000003541d174841e04250400d415008640ea001140c4100b280901805d0100001c030745071122910f14907501c4d0381d81d0800e24440e10600410300b4500f1420070455132030315088040d0110b00701c401e440712040d403600a405c3e18a2180d00300000000b0400440d9010b024107200c074007618160409080c02450211501e151001c416904000c2c00031594014559200c0b081c4e01d088403c110303034510704052580c1005c690103030321140f207103408001820398040940c1c44e8141c12500d428102002e0640807010500401185581240003000342d081007c00311014140903180c000d101c5901c0c0c41e00030010442010206c42c2030108014013040c038600b004000d00c006580060100420401501d030580c3d4881c2c0a804d82c440e1087c2034240e034503180c1c0d0040b074484c40c07a801340c5651308040c002e968491814010901c06020501c0c0e07155079103800704541c1043c140f1510b0080130002d0080302250490 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 718548929 1250 718547679 718547717
    0x1509010c05150a020301030b31150c0906090602070501020d03050a0219030203061011060c0304080403140a17030412140702120d02010e07030305031303030f020c010b1002010c 77
    0x98082640d00d845590300d41c035074070000c2d4400c0501c10f5111010240c2c90303503d075141c59901a003002c0c1071070742c05041414041514110300d4040341148490450700c081c0c420131600b000701194aa4a0b4181003090070410065a80d42d001082c1008840003a5124002c803a5502d1003243c440120340181030041e0030a02c81ca1042c0ca00c607400242d080042d0788401860900c0c20203420520161900800001c0b80d008070800c05949045440e81c0710001450a01d4004c611100c0d6825807150001402049580008030200301031000c1d41007940c000c0d5603c42c84c0051001c1303486468660f01d04a4003412a40741700300300c200140b00341048003070341e025643c0840400c00d03e846034031041d04c00c01048071300390300c0d1288240101800740e84e40c9200141d003c0e49903070151011405170704000342954500881550540d211420400c0081d42c00001c4a500400710500f40b2014480c0d03140842c05031601900c410070712400454218909a410b40c4148043c120445020314280a24078060342610901c40c0c03e00c0c04502d20207024880c00c20780c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 718550179 1250 718548929 718548947
    0xb0c0706030c0e040903030b030601050a05090f04080c070306090c1a03070c0303150e010f080105160c0206040f060e1008010f051311030408220323011e020711150901 73
    0x1443c00c1c071940c9820380030301107021110f030380700141c1c0000c1d2a041d140203903060511465000d4081980c10076161070505c004140c0c00c040c041c0001d001220f401c0f00117030a200801c015070301c4410605080c0c50403683d1706c0c2003000141114650a40d005103c013103000441c1e00401d4a80201c83c2c160035442419581c8408003550b050130030b21030960034135843c0c98800c0441411101650054046a1545060b80d414000800c8104050b6008050340b0382c90030007481f80400303000010f107440e4421460441c0c4004024030119805000701d070301000c41c00c07500000105046400c083c1804140707100350340541c074404140c0d40880d405c5000303100d11200080640b1041c040ca06162140351000450b401d00400c6100104403c4c100035031044030306a49408001c50030600d0005a096418031350041c038010a0916070031070b210a405600c180c0c3c1e884191190140d10b010102000713400c4540c075003042200002110b45400143c0303019520030343d411200c1810b880789040c45440d017503030790701c07070a00440c04010b0600c1038900c0191100300da = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 718551429 1250 718550179 718550201
    0x1080f0a030906081b0a0f020c0f091303030603050a0b090f0c0a05060a02010e06070f0f080603030d0e010f1103101e05041e0501080d08090309091f051e0a0b0c070603 73
    0x203040401c074100030851710010304107824156500c00b505421040000c0c00c020303c41c5001449904404404101d6554400c0c00c04c2c0c0154610605110070a0315190030740040c04c066000910328040c00e5090418004941000c51003851480c065910840c1c80d5000c06840340d070090043ca0b404026000c0c240454100a0060409103403107000002d000050100c081d40381403030071900c7c08001000341c0384011541e94480340c0042c40310000d060002c0349090010001c0c0e200d0080d40c0c544c440a03aa2480459910202500615102211003d00b0488841694103c03041c91b8000c035614040b980304003100007402040407002a064401c9890450105410074003084080c02d580110044005495035914800b1045032007054000e000000007080154110903001c0c1500c50010030070034a9170002e114402c0d441c7c942d2585190b0045510791341c50004044801844000f034655000107800044500d20030702603c5806075190303a505400c94000e0116541c031000c8803900c0c4242c000c1c003021074124038020030802c0c1c0290460807000b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 718552679 1250 718551429 718551451
    0x20306131a06070c1a07030504150c12120506120a0b04052a090a0b0607150e12030609090c06270907180905070c02090a09080408030301080f0a03090608 67
    0x81401c50005031030307402c10001503a0100d01030804100c59000100b603550001c1000300e105041c0b035403684026019000c2d070710800c08820800c0c03841160a6105101500c8803030b603c00510150405149001032202549115981c400e61514010401610f00030b883c0f003681508a90080a483c6060b0340c403d01007260240c07017100c261048140c0b00c00520014500035104c158185040c2d0346000c400010400818009005141d02c82d05d40007442c0341e80c0d12880111a1600c0e0880c10120501c42030395005801018185002c4d03815000d001e1507141c454040000442c05035404650610b0f030703034544a1580c2e0f201c0800c014101d0f072180b000c0020a81d250105070701c40950b14040d424003035401c03525401055900c10202d910f0400115400c074240ea02218100c1e46070061310004c007081105243c582d030b0140c290700a2401c0680b10310b40141c00034101c490190011601d1607407114000351036640d91882c45540f03800c2800307201414011540e04218621700000c01c0404a40c041d40e4404110f03203003800a440c03030a0080c03e240961 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 718553929 1250 718552679 718552721
    0x1d280804080303180c0603060d1101090803040623030f04031d100c050d0804080417010e070312020d02010915020c032107020d02150a020c0307060e1f02030613 70
    0x1e80c1c02440a14450744915400d0000c000c0340c2c0040d02c3c2403484400c130182c41820103206110043c1c48410f503908640341e00603a4501c40e08401401030b180400c00354000d054500c4000307008a941039102070a01c04942040c031954801440d0f1450341d801c5400115801000301c1051400500030070b1043c21406050f20312410181018020a408502c117280b40005a9011607003900c8113008100c020050107000040e9031901f0704940c201650799440600c5548915280741d02100c001300300b1032070290701007a03091542ca8101c2c1c61403603076031801012541003000303000c000d40151034582400358018020180d0390313948411a00396803800c01da003550094100742c2d0102444d04c001e1001410500c07100c2c00c68a07064007103030902042c501c0d04072030007850b201181c005442103400880c001d14000101ea25002d07001060a24096150004642c02901d50302405c207014080c0c0d418918103010340080031504003001c0c00012980210340c0c0c001c00e806816448143c80304c07500103a003d92646600d490b070340e00810075403818111113801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 718555179 1250 718553929 718553939
    0xe06011809090305040e1317180a080f0d0503010609360f0b060a080606070627060b15090d060f1e050a0b030a0f02130507031d280804 59
    0x11540000d00450214000185c1800410b1441000c03c0c2e214485031440e202c0080103940d0030102d120100810308541401003040c2e6000c1a5004200c0040c00024024000c0750b56145406950342a5044811819000e05081482001c0c814030880e0f05845194480004491070301c0b40303030080e8114912441d0680386a42c410f000b40c15200d4a03100e1444c10030100049155240000c02c5c10071031382840100ba101c0c0c907081002180e4030307411210099005104a9103a07880f01c02504004010307041494000c00303092140144810200c0c09101c00181d001d02a0904100c803042c04020b01c8040c8a9500c1000c0c03105406010501c11454a41d10041c2c807076200d42c43c003003013540000040d00d040e41c844071840052002c0070010646d29007a00e03c07034154402040442805030800442c0440d4a0381d00e01d6402a201c0d071001d45c801015510703034000446641607aa03904000629010302300030024001080071550140c88007048942040c0c00007804800314010b03c620010b0029543e6080010321101c0204461349001800000703a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 718556429 1250 718555179 718555181
    0x230102120316031a37080a2d140c190305060907120213141305240c0c0a0804080c090117030f0a03090203070602250e06011809 56
    0x10040c2c1c2d1844884001e4081450041d09542600b100c2c244240b10402c80710016940303d0703902480035411410185c0c4071413581c400e6280c2c14100241c08880050030710100040c41d500c001007400429004d03032400041c4545210742c60400c4070303441008407959961010305101080d031030844684014000780440c1c01140032000410701ca00351031a041c00420b28040b80800074010b040c410340758010210409800e03203030b00702030601e00c04010320f143c040e02841440490a01181c3c0903845400b0030013042c43c200d070342403420246440e01c800c0440d004070382030b000d0b031b0008550180c02540700c0180c000040015560580d00d000a83c1a160444659180740348915003071240071404800c010b00c044d144140117046140b41c030340180700d040981a481600c20a0440300804100320000c0150707030a2000b4192960307510004804101d0240c200702030060b61500038003030700113203940e00010004000190509a814010302c001002c002010040c40b03a03104440001c40010400e601c100c0d8217104420840d840340c1c9a045d1101c440308 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 718557679 1250 718556429 718556431
    0x1314030705150c070e0a060605030609070c24020301050a120b070509012a0308010b0406020d0f0527030714060318070305060a0c02120702031b0609030d02070509060105042301021203 80
    0x2017206026906214511080b402407101410881c10035a1071070800102041c607070304c0300600304820085082008810040c110b511400c106000454103204580d4060411000b58001e02c2124410030f00d1090000704601d44600000c00541c01000c4103000b661000000d0300d00742e0203403c0f05410404e4a1010781c140c0d0b00d10b010241ca28400c1071190700005400c62070042c10885040c2c12181e50508148001c0140e07a074001190f07000103820380740c400715000301224261858021841b0309007928010854640340c80d0400708940d036190704110100d80343c01340c0e103200c0c0d40f040c008ae42407a980c1110040000814400c000a60070360058071720003c5a035001d40e40e4407882d091240542c1c443c0c1900d9101e0180d40e401c03070343c10082c0b118620b010b00341440ca8100d40d0340c00603542d82801c0002000c82400e004124290341d94240030740b015070401600b507070f5001140c000005e448105a0103001e104640820205015500c1401038400b602c5a9040c00d0000384020280c1c82241c0340031340c42e600d04510801d61540b0240c406000070b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 718558929 1250 718557679 718557689
    0x8030a0f1b0203030405010c030501050a030602071a04060f060b03010b070f051519060609050109031b0b040f06031a1c06020c010c0f020606030d050a050f0903121314030705150c07 79
    0xf95849041074a00030342550103010340384d401c050514005005075698226844110f07a442100140e0307410342c5103041c0c8184049500f402c0c4520540f03034200028400c01c4d411200c46491002d01c00c2140302d480b910300e100540400e00503e240241e091040340006010801c0001189000e60700b115840300800310040c13400941162105a40c0d601001610a0788400e8054a00500041d00305408150300b0000020080c030101d10015191143c2c1040082000d401c40c5407410240030510011a50f4580703c1c9040700c3c0c019041d10401001a00c2e01300d8200d00e1121100c070a503030000c401841800f880603a408815803041c02d503001950441c4d030800c8645100c4400344140d00c219481e941b6030700c010018568010307040c8800100a0b074000d803c5082e103040f9403a481400c072046551141083ca8860581c2924890240148110260107108211580c4000c8907000060500100d150514080300e03130b102c0c0400c10000126645c1d841e05036005020602c5140380c419030710152400342041c4181450442e5840c680381207055408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 718560179 1250 718558929 718558933
    0x20c03030c040e0c0c0c01200f0d170402060706021e0705010b090109050f04200901090605190308040b1e0310030b09011404080a0309050601080607020c010c08030a0f1b02 75
    0x400c02c1a0f240c1c1480300c0e80d1180070008614240301c02030a07120703124100320005c2c030304000e05a80700e4107244a10045200c01c011101c0c040351184469003140079901c4072000d920101246201650062011004020303078491580030b0082814013815a8a5030040d401068289206544694400364101d00d004003500b14640101c0c00401e402d10040c0c140700041c0d0040e00160713030250605081009505003c0300c104e40055014501c2c406a0344085210005480100c2e00a42d10104c8000001814841500180107503602254070080c440c0c00418203600031103461100401002d0700344410010803069070301600300914030040110442c1040d8005e05030a50040b10b0801450450120510600400007007641d40501000c0c000c1040703200c01202010000380c01480200707541e40c00250403804034440c1d008260000d502504540c01540c4800e0501c1c0c0343d400840d1520014440c4d011111550340c1300350301c07000e90b09410120305440c64a410040c0c0307000d044081003980d0000e848a9261341c44028900030a051410b207540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 718561429 1250 718560179 718560187
    0x2131d010221010e15030718090c060c03081503102a090b0412020312041d0703110a120902030d0201060509011d010608070c0f150e01110f0d020c03030c 67
    0x4006010022200000b403088000000144a88544294000e42010102d1030807400d40042c000042d02e0004030382c001544445020000309214801038020700700d00e40c42020b03464103068071b07000d0480c0d004013190000350002d5040030101d000006144d80c21010b10308080d09540028074a1100d200c15510b51400c0b4400780c180301ca0001091020100c189403504410340360206d0303505c1c41c3c5144010301e800f903401a011040c003025001411035400300f2881e14020341040080d80c07926038400328905003e907042d020140040c05000050051032082c860400405100100c2d20b041c00000c1804540304001801000307226590f48460300c000d41c0d000c00540c1c0b00002254000701c1c0f541d0404052000d501030681c000f0070400244c034010b01480815075078041c1910942e207001062641c9884044507510110203000d0001115010481e0500a603501302003040d02c0d00100901c000040800c445080316070030741c00076041c24002c2c041440903a0b900002040340c1100440c000d4200803660049a0456005590480710702e04001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 718562679 1250 718561429 718561447
    0xf0a0924020d030908090f030a14030918070815060d090b0702250e0615120f0f0603071401090e0117010e0304080601050d06111b0712020102030702131d0102 69
    0x1240d001c0e044514a0f0501542241d82e45554260080b10041449620842c100300e00c0354804200200481d500400c160130310040c1221a59160392003d89094001c3c800100e50821a80704c10710100d00601003992070b10190754810204140d5440700b802d42a521903420002c0c50300903485800f0701c00340280940701c1500182000e110113442c103400750725401031400851000d000005460407154081396001c01d210055030f5038200c005604a0b00c000c141c030358161000314640e841600c1c5541c45612800c07045040c83c4107a2941d07020000110f008540c903036455408950f0611552140428680400d11b041c1410010079441c0d19440190000036000300c541840c002110f0746941800340201200c524602024501e81403c120200d900c4d0f84050003400e0144c51031102e040200406644420300c03600c4032103070041d140c1c0c030740810001c65034050005400091148150104410f0020009100b9035079058004500d01031140d424080d040303495020034030000e5036420401c3c040f40b18001000c0c00c940c060000060341c2c1d404034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 718563929 1250 718562679 718562683
    0x5010e07090501140c160e0618090c01121107031809050c0a0f020307150c1e27090c0c1b06050904090c1806081b03030f0a092402 57
    0x10640c80402200d14000c01050f40c102ea804060591804481580d8001c00030000303252200360351180d540401400130010391104102401409050102e070b160005032030203104608103440c181c52109050f040030944030160340c09001a0141d901500001203485c141c4001c94108030340000d0001e03008030b0700c500e00b42d0880c0c40c0075a8110000d040c11940400103400c2c460341ea00554001c031084034062054000c035801d4000d00801c00c0d240542d600c20711050b004010744c0c0f4418003405041401c400442d511900002601500c030484200d8150280da40c20b800600380466807a10f84890a01030655000c1d58401003107900660065840011146c0c480c2e241854075072900d2494000c0c1c5284602c400c40091005020082e07000040300c00710202183c01080342802030814a5007152241e20050500740d14415651003545243c0000003252903690548003100c081844600700c0030030680320709515810400120b007101c003000340604821001c614000800b1a12410302480e100c4400002c0781060303042170142c3c1e40355030f41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 718565179 1250 718563929 718563931
    0xa110318010b0d050d08090307051f0b0307051e12070605071704060e13020c010c0e030705040213120510050106030209040b01020d020d05251203060e040b0c03040606081005010e 78
    0x410b40380b820794641c643e04c505845014000038403040000c8203012400e0480108280c07070701d80e6040703819100d41c0c12180c10941d80b80c0300a4070034040c106080c14011005882c0205104040720409000b07180d40907105d0a0482e86c0012404231075038420548084116140420041280940110380f20316580d00020308084101c0340c10f1010202c0e0042c420482804401e900c1100300c1034a080503100b03c0042c88403242c400b400784c060031807404caa0750b00c0e080100c1c64450b40700c3c0e00f0028a400c00e4003654a165125020b120a921800702030361400c0580510411000c49021540d66105014106880300c16101c0e5003d50141c1c1c4084e401940000d4010410b10054540741c0b16403600b2000900041c8442801d030b200181d1101400c910031000c0c03040110302030109054103071036151040c44148485441d2040e80c070b803116041040c0180000028507100c802714000440680c12405960080880380035581d80064190256000410417205031703445400008071460304010440341c00c05919000300d100d42c10010b0b602c1100030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 718566429 1250 718565179 718565201
    0x7140f16050717070902030c0c0f160617010b03070341130b040201050c0d09090e12040b0904290f010302031b16050703030f020f0d0e01080a11031801 66
    0x1144040810f100900064000484641080c05a240d070b5801aa44d13803e03004070013940480d4003a000c1e15415031540818011840054142d8070000d0300d448040c12141c4040c00c000001002e4040001030001503500c1c0041c60f8010901d00c1c012640c0c1401d5680b90a081203101c0300038a5480d025109900f0a420741c50401003807030f0b014214018145030001d4000e8024140100142402045d8008238040d6440390080340d1060171090f044402100c401d6800400340f40403032207002000e61402c60702d81164100810524000040341580c3c6080500b02740724120980e00509005a20590343d10f900f40200010b1a1048801c155001a064101141c181880100308111010f281010300c1001040740b20601000c0034200400b0540341c580d00c0c1d94034050701d8120345030043d101420f00d01c100c0000008045e4041c4001c0900a031560035540d50980e411002941d03030034503405a0000c80d20103080782c226540306a61840d0f01c000000808907048500c0000c0c0740032a030081c0d411003c001000241450809801d000c0d4180380d0f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 718567679 1250 718566429 718566449
    0x50309121612080a05074107260106080607120b0306071b06150e09161404050c13061101060503070b0403080a09030506190b060307020607140f160507 66
    0x144060781c3d030304210f114860b003513000e2003004900482404100d91001100842c50041e20080c00c155210110401c10350100c0413249103210407011100a10118110b01101c0d50503150008150400170501c9050030000410031070b0750740e03030310740010140c80030010035004108944a4080301040d403039a80e4291a81c10700c1d481d000340d010304103001d0050382c054803240b5070213800020114004110714058024110008001d01301e41130001c80030407103000906501c1c0c003c1c080b880c04c0301c0b0310004810420386000098401d8501e50107030b0307800803101414503402c501d50000d603149031585050388044005149000701e404c828009030440c41382c2680d04c10244180c030041c14080300103040042c9405003242c2c1c01c2c421404000d00010010613141c802c54060860007002d140d100041e210249040c0f094401c81032034124a0f5241c031400d01c0060216405c0c5441203a024848680c09421950780f5010150f03840d0300140081c1c100040204003003c01010100042c1208101c0d101003a800c10b012800c0240c43c5c10315941080c4910 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 718568929 1250 718567679 718567709
    0xf06010c0c0303031b1805090a060503010603080306090f130312090219060809070e0114152206050315041d03070b1b092d040216020901060305090a0f0503091216 71
    0x5906c855801c2040360300c116041c100c1c42da500010080a841d881e880585c00d5801c0c80004410440c5d0000a5442400d00b03661944040d6202c6203c0d03018990180e50346040b04a031403101402081c8a0020102c100500c0003001c56280701036070128030182d0070300140d41e034000c041e40340900c500c0d644030b880c06420490324001085c256007804007087e42c2d9041841a0618450040c0c98919252101d0410400e03440108100c0d80d168542c60700e03048078442038064a40c0c4600b06100c40071500500a2080c2d9002c0e0101d80c825908008403241804000c000b00c548081911140d018080101c020130001803d10740c3c494602950300e4140f2400d035049a2040c0c003440342240e40140f20261003625150710605003280c0840f02e8000322004564403403d09e4681f403400d10f800900000303d041203103e0500c06081c2243c42074801c1944c903131703079100100e04a540548111000f508a401d0740c40118200440b40c485090040094924120881c40050b415081d4441e105a064109602c1d2480040021940c0070003030207100d680d0000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 718570179 1250 718568929 718568957
    0x8010209120705010e010507020d120f140f040905130503030106030911090403022e02030103060b031005060108150f030a05060601080f0402010206010612180b150f06030f06010c0c0303031b 83
    0x40607200a17840303810032001090075019940c4c0c6c0a005400e094114202041148041c10010f00741034100c1890f10103d0302c00381030380320243d0520b012142d0f041c0d1003500290511b41080f1000001e0704000c1c4c46640400c140304030400114005000842c0201096180099100c820b4504500c2491015400301c1c42902c0c01420040425004561041c8030101d800580030079841d84042c0344406058515401845440440048100280e42e404842e00d45004c800700c401e01c42d41c0300c441806403801210843d00140d4100040740083c03018054406d030501d4010901021503900202207458550440c0043d42c2c1c50340700341e080c0205c41d6000041143c0100006101e18880e15240d00003030750303515040c4942403c1260445040c10758546503444000c4105c91a1083e040714101070811244100c000d0b0f030100000300c22007681046c02e180000b0704101400e005400141140d5450240c2503141100425807810320401c1f00020000030694000180914030a032130000b0341c1c600c03280c041c000040c1841118018800c81550b0316403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 718571429 1250 718570179 718570187
    0xa020d0f02040b041e1d0a0e0c0f0609010504030b0a050a05060a060c080315190303030c020d0215060312030405010509060f0c1911031b1915050c070c0801020912070501 74
    0x1043d642d0300c548605840b0361781d50000c210070030698000149101400000600c3d80318481c6c0b018011014100140b00c500100c8040a072500e20700991564001d00c0000b0035010707401e02c400544400041410400c0c1004d661f40c55045041404440c0301501d66074920800504902c0381c841e4581040d81a14641207260608001900030000250040c154400100025aa244603004d100800d00c0c00501480c04103283c541e09816001c0007800101d020905044034040c040c1d10000781c0b0740e1420111340c002c01102440900300002808080c18880c1c05025010300e5982d0840480000d50046204000004040c942496401d042c42c0c000303060502100c8074103052000588910080c1d44a03001e0400c0c2454040800c0c3c0001d490131070148000b090036010200340c18169000b0f4408000a40d442142600c0c101180075416a81c9400701a0f0300030181220554088814906a44600d600c1000410a10315100503070302d6a1240038120f50281807641c4d00000e40200c542032100b01d050f0b05400d903500800c4550f00f40800a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 718572679 1250 718571429 718571437
    0x2190212030c28050a031a062a01020c030a0e030703020d02090a0b030609012f03041403070203030d06231c0302010b04050a060e100305031614060a020d0f02040b 71
    0x14418a03400f2502202241054003410b4a007103014803001e401c445602c10203407144e00144901c00c0405d2509100f81d031240b60f261400d4040400040c03401c1c0c17400d00003900707064800444010b6284000a5024031481c2880309200a04030400d030900155100d401840c40100042d403503603c224007d8000c07d0301000140c4950804100550341210341c111165140d940d40030060030860007070744e8144606418000005410f520602035058100c883c00808102681403828090026032005000002000041c002c140c482c82444422680041660320740106600000c0c41c0d6001802e4981c64640c0d6280108100c01d05d40001851700e0a500c0701c21203000c050100000c03030600226806030b5440d03024003242001c241c400c1d440070f0310529006000300828108542e8000013007516014030b204040d0042c1c0032510000d01400701c04100ca911000031850520600449101810007440c12110403c44609a1180300d00901c240c902c102d052441c010303210041d114003001992000e500304001684100802c0c0140e4050740125 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 718573929 1250 718572679 718572691
    0xb15090a09020f0307031802040c0518031b0d1704030b010f061d0103110f1308070828110405190f0c1d0111060408120f280e010c030219021203 63
    0x40e034082e40c004403601103501f0000207600c20729122218248035040780142c0500301c10181104845641e01041c07650ba025030411a0110901c0e218440e4483d02d40315050a000300d03c51f0340244010323410b4080760000d0b500144c104a03400c0c101c0c00d00510281c214502804014a0103140c11603030340b04488020800702030020b0480e0304243d1a8081ca002c2c1801400840d8412005440190754542518402d03840184441c0109500d41c0500c980005003034100082c88880480c4000b42225101e03803c200c2410501c600c1501224521801030540986603224404d4510480209290020070460030b50b28404071404030b003000c0321892520f4820501c0560024901d041e00b40c1c00703a0402d400f41440801030301c507440d101d548240140f15041c200b104100146028010b9001c8241094506031240c1c0590b031109982192425126040544410624511411260400005220005415900c1c6c1201c182500c1c420b0384a14003182d0005034000001118180016040b1510700c00b03400480c0110f03103241000e12020700300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 718575179 1250 718573929 718573931
    0x21b0405041e05160b0415050306130209010905120607110607020a0813151e05040312033317030307093b0601120515060d0b15090a09020f030703 64
    0x80030030403c0800516800341000c005130103019540f0f20b44808a90b00a015100b00c500f004804441b001d401032050301d02441c0003d0411001c84140c42000000350004010075040045468000810351585620b201d164289100600300b68a490500648542c1071800f24a8681d4002c074100054a640460340a840941c020301da03e580c1c070b06805110740c4441903a0409415401044101401c01e82c010281201529111320624020b054200007510f2f02e024911001d0003114504502c002110b100b85d00c5000c00c0c0741c400200c10800c1c15420106698a00c60800c44803040030008800d000c0000105099040307200d0f550021071461500120051070380806100b0000745000c5a440ca4901030962110340c00307104030403400320854000d072012641d0400070503190030b07000c00d0043ca421001c04685000355441030201d40404214803415a050007100da000d03080c0989066a54801c10790181e0f1504091282072180307245480c0c483c1515801c00000b258680e00000340d8500c10400401001c043c0000d49911161900b8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 718576429 1250 718575179 718575233
    0x3060f01061d0d080a02150a18060f090b0a0203060a0e10060309211206051807050a0c0206030a0504030e0904030e1c060509060405010c0e0a090b0a080d021b040504 72
    0x108880343c0c503000d4010f041a4002c05c20760703a90396001030b500d010f120144c00c0541191701e440d21110f00322807601443c0c403200a4980e03001004a01d66804c070b00030710300700d1850001c4c4004940d2141d502140c410b03540d05001035000010701c031040c988401c03030f00090402c1c50b00c08003650410b082603910681c01886600245034841048200380703e051860849002c0111443c0002ca0700401070082800d8501d0f001c0c0206c181c50480c002c500c2d81003403610001310514185102600e51110340d000e5900790090100e603400c0025880c0301400584403600911b000e081c00c02c1e0045140d05003890003400001c15045920302940c443d108210110364840d09a040c0303c0710540741c94402c0d48146c2002260004400c0e4050145820581070000342c1400241c90b911450165008000b90b00355604212411581c000001d984031051420030300040c80961b0100f003404d04018410744131a562000f00718105500541c58a01680107a254645240e408491140285d503085034100503510700340d82c400311139186081d858450a40035030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 718577679 1250 718576429 718576487
    0xc03050f18042904110f07030e031c0f18180917130b031b03040f03020c040e0c01031d070608150906010503190608060c040f0b04050906060c03070c060e03060f0106 72
    0xa0119082020042d86e020303902c0e003040c01c01424910005905034042d11845000e00404a1405034080c40300c0100d0741c4403141c1b9068224215019000e0316140654881d6400300082d09804108400040b60303600c2002041040090600450000c003820425210f0700d020001202c401091030900000d82e4140b422050b1680c482c1d40c14a000c50f006458246602e4000006010a20400120a000c040d100381e007103d5141000400784401c0d11585003140044c1c1d800181c940000e903010b03030001442c820106080442500c181c094440c58001103901c1200400c2800701844028850711946410400d000d542151050616500003015444010100480384004000e07900d240c95040c6c101800901e482d00c2141c10908000c50f5920302503201d03101d555195040d8840c00562003042d001500d00f160381c0142404260b40e11341d0203101c81540034401210311400108001c030f00054020143c60301501d80c40d580c00941e4005082450300e021000760440003841c480000410906a120b0001000c803100e9542410796060300c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 718578929 1250 718577679 718577711
    0x24010302030721152906090d031b030f08150901060e010c0c03200102010b0a1707091401050a0503010515061c06090b04051003120c03050f18042904 65
    0x80040180b034070092900000c2c00c107070290000e40e122409400700d014428000200e040011208170180360f0402c0307040c404910b00380740c8403004120450003400d00c000c942c4c07810300e6200038600420600710080f40300c800440d0085680b041801e030b8130a410703008000411003040d0001e00c10600c14460788007004610300c0079000c142d1140c01c1c03901400d6401800c907020740ea2a840c16100e0000800c810100e4840b0a4000a0403584140a58a905071003d0505240d141c200158058100d488001d080400d106a10001610301036038841c02c03040f83d411003403960f403039410f04040200702e1205030f000a01c20b82c1000180300440401e50300b8504c40315800c84030f0a50341c2040c0c0b5440c012007080b180380b207040d461030541d00051035003203900503510481d000c0710200803d82e40d19000c2c0d10688054000603180211942c0360105503402150780c0080d1074041c0c14000e04000640d0000c004541c44100c44032508035039040303210010705041c0500131208001100203107140141c020b18400342d240c4880014821500c2d07000d00d411400032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 718580179 1250 718578929 718578989
    0x10306110405030a0b0f100b0f0306040e030a08090705102c0a0b04050f0a0807060c080409060303050d05220204020f070837200c060a02240103020307 66
    0x7018066a03071360015802c24100200d011141425a1510b1200003003800d94510761401c00e0700c03003a1781070728203190700c0d4084200503420090185030800c0c0e503003051000741700041015011101d000d590f002c031f8510300803103040d090000e554460b5014140da0010858440d800075852648400c0410710304c00c5080c141d903c03110804a60350401c0d03030010044140401c1281440c0010425500181d40000420b05130707909000c01d000312441402d01c1a00164030901143d44610403540e52035000340906800d103078481200c00d085076015403048021032000510f14020001c54090784d90710400ea8a040010400c1890f00b000d6207500c2c10400a20944e0300140440400c0c0d41e010965040030380221100d52100c90340b884282c0c0806403504004054080c5603440c28001c1c14003030140713451010595130003c25959200e440c00030070100c64807200d00341c00342c4480b8040da1f48036100504044803a59000300790074907141110074905c443d40d1010f1510344109000510140c0c40c002801001c9400003000b050024070210f0071110f85501e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 718581429 1250 718580179 718580189
    0x60506011814030118030e010c0807151a0111060c0c0f010606020607020f03030115030504060912050a0909090c0501080903040b04030f1505070c0b060111160e07080405060103061104 80
    0x4030301000c264603088504000b00440181d00030003180701c0900300075050211880005001600c01d0003215059449440c82e660800d01c106500390819901c4e83c0d9000b0440408410300000565035611002c559003c14100b2003405000e003402244941005096515950002c1c082c0441142c006503d1003500010000703003080200c4040200322450300e8200094980e003054407000010700c00c40340000c2c104180482140c0c100c854001c002c00c0b150111180a8002e010000c0056a52558580c0400d012031404550044021500e51b220750752016540320143c0b07003082c16040301101c00e00e8203036104000303040e603100c610999109090a14160f40c030403550a145202d1a0004020014041000802c100800c8000d03840c0500c01c00c40501d64030000d0108000f245c0007240c406000504c2c1c600c8260120344000700325504020b06142c42c9804003850300d0305a2915100f000c0e07140c20080c102400308070075084124441c0d00701456150005c8107007400d4850799078030181030102806141c0d50f841c8240b2254105412180102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 718582679 1250 718581429 718581467
    0x501050c0a03110c120604121e0f1e022a0d0809061905130605270613060e04050717160c020d060e07080309060a0509040204090608030307170f0406050601 68
    0x314041c81e040342c489109450460300b4213000001743c8800e174010000840c115803046887d2781602c21801044134004805080b400500800b0300205038072031000d21003c502d9003035980007044070050594010148070350700022074099029074962180c01d9079841c0158502c95170004901ca40710508540060210720940d081c5a8511100a4440c030304190000c000d444150701121000307040a0f554101614a445000700b07201801c9010b9016001c402114003007a2203a00c2c0180c0264101960303900d060300d0110140c2c1111001c9485802060801d24080c02900d078032050918203800700d4400c00c0454500d40c50003400070b000e11610054003118082c4103e025181054000f001510491440d0500c24018142e000f1100618055000e000c6521036000080380e0708440054145843c0c079401c81012152a000003074000e80c040e400304070004028056000703007400313492204065541e07400d00c440d01511000d0040c9513002c044a200c0200802c42ea49000c205170320580019010404d551414012285090082500f820700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 718583929 1250 718582679 718582699
    0x4020909130b06040b090612100507270f0b0c0f0a060504050105090f0c060d0e0a03020d0f031e090305070515100803040506031512010f050a060501050c0a03110c 71
    0xc4000c1415500d550b000b104190a10b85880e0107000c2036600015509030096240404501c55041242d852001d2a80c000c06490120800c004000c09551054490b003000601c0115a149249800d100c400310a02010041c00b0419190008007500c24216100f803100d140c0010401048040c000e112043c1124101c4084d40c0c008486450305400510082d40d0030784a9601c2c100018420101c001804114000310300c0081100700c19120400002e580a03281c42e2003501c0d283c1c3d41c0c02e2600ca408110400c02c0b18483e8003d8074100d05900b400030800d00050007c0d800301824a110312203015001c0da0301141d510f9800d60042805101810b040d40c03a071107180c1c4020054407805290018050b00607030300c180268070082058201d20b03510031000782d0f02d00944c040e40358800020404904144071130b1100310410304010b040e402665211641072800c55682100c1c0100581c0c480003040584001440740c0301c003800c02400e1041c103107000050040e59802400e1002018064402c0d64046810b05c00c000340d04004034014040082 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 718585179 1250 718583929 718583941
    0x7030203250605150f0906040b1c14153103080114030d020316111f0f110a0b0928061b0804060c2c030d09050d02090604020909 56
    0xe64000707400c06075222490a404518002c081341c5409558003801000c04494008440412410540c06044503078415a100c0c14401c141c0c40345059202c40350303421620303040d0700c100c94104100103044c501c004210541142c21420080700d0a12802034008100d214900c10078646040d421445101c21040d181100200600210070954089413450580e4404450009030180d640c0906079200020600d01015070818440014100034100030b2800f030b6401002c40c8c2c0741c103001c204041904502400506010040401407026006400124581c5030300d9941c40e00e004100200040c250715440f10842c01842420000003203294100100102294540000c1c1c6400a40d04103282c00450641c41540c110394850030305440c41801d140c2e004590520390025202c3e0320466895541d901c0060003440d040b00d0902032900000980540103044500c0000e0340259250445036086d8201881c1151036a40d940c10000521010302440e155803815105241e4161411456a00c0e442c00140190103030480a0350003904010070445 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 718586429 1250 718585179 718585237
    0x120403081e0c0d06080c010c02061c060b0a020606030703030e0d03030e1603110306010b04030b04050a0b15040b0f06041505041805060a09020708040e040201050c012c0703110607030203 81
    0x40855400e030010000d081c5c3e1049006d8440003103c0206001c00c951112190240c1031903c01000819049074103a4120006046244125117982c4c001c10060180412880c0f501c0f901000903a8114404070004c201951075994001c181c0d0803240c86003402180741080f40800c00d4000c7d040110304106002c1030751110303c5040d20b012103d280b0740c4016a101101c00d00f031606203041c00703c2c0c0c590680d40748082c0702d0b2403e411030310742851401000e04226031038451040d0050110f0000d00300c03140503245544c421456030643c0000c210030f071494000f005e4401d04031541c40c99401c0d41d0301c0f411101200c01001000c1003490701750f04252924000c6a10070580c0b0003454056007034480e6203a225030700c02e000855030790700c100c0d444032a1440ac074010018010040d43c41080103000101001c505640d00cd0320500d00b06107411100b2440c2403d4403144200c094881802240c0f81105a11070520048130b20340301801001c0070380c519203400d244000746401d264040c500c00528902418402c0c012150320f407442c00c507842a00d03202e60074a08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 718587679 1250 718586429 718586437
    0xa0b1f020f07061701030f051618060e091e0f03040e0a050f10030201080a06050d0f0501051501081b0403120906032306041a0301110403020f06120403081e0c 69
    0x41a4000d607840441d83c3c03030040c0c44803440c0c403400001c664166030031a981d00c66141d2021800341c80b24404c03c0410301044042241c41000303041d11032040013180003c1c06001d4199141e43d0441c00310310b03e07140304002007401c0004005214044c21800748002100c04401c0d5400e000e4281440c04150100180200b00500217151013402060b10700300800090761380035030a10400b101542c4090b51041d003810100050342c482d9100303680043d04406c0000d20a59900d0009a10380c44450b000c85001404030303004024072000703204281c0d110518090f5130002e240104002800c2140c0140584004008242070f818148172080503034001c0d40d80840340300c0d408101808081c241240301d11803d4006070410903100c403130f402d0b204010000c0f102660888240c1d6150002040068131081e0700c0d04444080042c4411040e0340c0034002c054503040180d811a517075034210b0062104012840c0003007030060004102d02c0d0007090083c580da070b6100e50189012a420740b14010820400101104e29040941041d400d1103481e488140c010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 718588929 1250 718587679 718587703
    0x9140a060207020306150d0308071803060c0e03071a07140607050d0e2a01230904050c070503040509131b140d0804050402090a05060406050901260a0b1f02 68
    0xa4020740e541c00349030b06c0d2800980c40455002244c100d004c4000a0082034107a81000290038981c07040880008900c01511040d80b0a030b40081c2c560301c603000b009030026929007000c08140c025151840c20262a681d11303414403501e02165000000b400030501800100c06054402540191060350030303c1da90040460308080e101802d810318114107141c034414001001001442c9031188241408110048030300d1030074035034540074103010851024401c482ca504140c4141018618412501c410f150000c0c84201d506c001d0184d403c421003000064042100001030300d0460b002202d4083e8166205412000450326652000307040c0c2c07909030000418054125181d80039078034040c41c0c41513034101072420811031403800c04020342084400c110a0081d41051740090014440103024503040a9a603008141c6560090b40080006200440c4000d21907034045107505010205101c44d1a0350001c841c8030704007152010300708030b910bea0ba07904100301365228042c0100c40d01a4024414452080d4002e001e9101d042405007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 718590179 1250 718588929 718588933
    0xb190c1a0f090a050a140c0a0306020315010507080d0903090306060f1a03060906150c0a060b0102120705070b090a0816030203060723070503070b0a0c0906050a1209140a0602070203 79
    0x140b26840000303803456410703000030040c4100113298072112180051070300c0c03c07a142c0c02030742407a81042e200c50116000542c820000143e4a24240030700002602c1142103490401908100100c0800c103070700156018003044220015452145103000e60784007601e036000078946824840000340c112901400b890850f0349603040381d0089842041003142522088076140e0b072101c2c070310012072414206000400030f01b00d54142e846260150352541e0b145040510042202e036107407202e01210040d60b051010200d1444900700d401e023040c03135030703074a03251540c00b240126043c0302008035829090760380b0107181900912826094442003000c9400c0810071000f00c0c0403c0e8000c2c450607011480251003000b03e201a01107071400c031f005070289400300c0b0409900085c425142c510050048101007884c0700180307409103d001500240c40c1541d06006403400400b030744a403007440b90502c03210700c0c2c0f5078005a01140000d442140091009801d151801040300200401561441540300460400889034000c00d20b8900840c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 718591429 1250 718590179 718590181
    0x91f08030c12070f120516060b1c150e01021309090506100f2606010f060215070801060e04090611120a06030f02132405040e01060b190c1a0f 62
    0x7648501911521000501000426a21341c000c02c03061011142030b00110710304a4034010402c68a108010903a0005441c1d8903034541c1c18070703641d1505014005250b0000c4d010041a13403186d40b0340000303c02e0080e0742e10b01401d440c0e01603045501420340c100d802e001c00041c160040d998540020000811020008450600c10000400d50307280b403c1408030200e4140c0d01181c001c05041101914004508480800c1c3c80445040a80380c030210501015002e05001c0311519001ea15110b002450300c1a41188460032421820600074038560010110703054400300d0800c0d000101e120000f04009107111400030b00710f140b400c0300c17085030a81260000d2040c0388049041e40c0b00f44e100c803494181107841d94400100b12060981500300141082d041f100501030200b0301c0003d440b025101c0c04a1000e2201c40298040074440f2018052460944280c406084007100204200d03401c100b0001110720607854160301d00e401c40162140716a1140f450146802da00c107040040641110284c490f15110035a000c920303200303000e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 718592679 1250 718591429 718591453
    0x103140c010e0a210b010909030914030a03030b01050912033423070b030613090209010506030604060801060b041715040308130204090302060a0f09080405091f08030c 73
    0x904941282ca600800a40d00c0303e240a004840b0701d0303034086012042102c003910002c0490b0f04a5003072402400b0ba07002c007203123038202480c001b07080b0a815040180841f02400501d091624005600d0350803a500d03080000b402010100180d80302c2c001c540a9503404400106141ca642a02001500c0c0c0c81040c5000c4000c20302e1050304000000c04a2902698524030b4026042c2c04281200e100317107403c90642184a415002641009082c1003c42e00301c02007600300081400a035091841e4051a10b01c4600c40400900c0242e40c001441d130341041c49607610880012000c074086d942c0e41d42c0010003c0117554002c0119030750301c92894034250040e1240030903488800b030302044050360209500c040c3c030300c100142103010342d10761703800391074461300a0110f19600300c1d091749031030058039180700c1c1c500150300a070004e0420786081c5d105101910700040006000301c1c14104060001900303442510280e070411544024603a1b81c6d81c1c0c1411521010b040716088600264900041c4040003000410784102c1d45002e9801c8000d0300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 718593929 1250 718592679 718592687
    0x5060705060c180a0308180a1410051b060103170a0210020a3e0d0903020103050604020d150e010605040b0901200624030c010512070e090103140c01 65
    0x1460080c00a03004280000c02842c01c00b0000c041403007003418948084070304031021540c09101c940081b21412400100c50310030702451600a08841d208a8103440e046007000b2070011100c80c0c03854428020760300003403410109801a020303510409207041c1424210580c540015548901c284020350394940020103611000181d0300c1150304102c02a0020185e1031061528807000b9400401d90a040040c45000d41d080143d1000c2036038542c220801501400d0000410703061940c065821070f9481d59071046c0d4851100079003042d200011280c0900300080d06596000128000c1c0c40340ca444100c1c0b19103020201031444000b441c1100c11740e8605001000c0e0b42e80c9802055520340715a008440759a0402d2140c0c03150703503210344c00d0301402074860b41c0300d1400b904070b4078001441c0010541d000900d02c01c3c481440c1100c148501d00302ca564402c120300803d950580000040d100713124500800d10000d0301800006c0310203010304ad0030415400c01401c21012582c0d00e050480c1d40e00d0340d40480010b42d000d100d007803e18540c85 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 718595179 1250 718593929 718593937
    0x60e06031e0c0d0c030c0f09050a090b1801030506090f010b011e020a0b101d0606091216030b191a060c0709091109070f35040c0602070506 61
    0x10011803440a01d440000c1c29100000091440450440070000c66030b8481d000d00402c0b108000e1501c01080c000d402c060041d004d607000203218010030001403020800c5a480d1503d21046a248a100042011042001c1006000018100c5e208208243c0000081000c00103095114041610075950b401e07003400c3c105426140210706c01400100d0214403000c004070018a08128086540100c951030407582c0d40b00d0107840822100040d641c1034a0f00d00300070030300940003d000f0000c42ca00f0b2807181c0d4500307800054004d01030303202c0b4640200500e049a010545040100c004c03602c45003080c84c96290b42d41d107010500c503d01100e000d0410030082091a00d041054007030140c080e2172180c070300b62216035100305000d110b8120540055244c8030b88040050741807801c1c401c1c02c0c155030080302e0140403100c5160a000d0347c1e440c0504201c0400091545030489207038480c0700207502014100f024140109411110403200d1000c00900000041d0001403004009030250440308070703001c0340c090310021f5503a10200249405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 718596429 1250 718595179 718595191
    0x5150409200604081f14040f0c0914010b030403020a0b010b212203020102190503040605100e2202040c0c0606080d1d0a080d0801030b06090c04140102070504050a06060e0603 76
    0x21101602040119508a0803017105000000020b2a6400e400703145801310341c00d6405681200f000c00001d024408560540c20241040480038840074401c1c124010080c40144200d2084400200128041520900c2110f6419400010080e000d5840e241180e00329800008504040351181481015900040740030174440d8148440900766001d46440e40090b801d010041101155400c101002d05127409414000704803000d681c1d200e4882c6400d05d404400c481018000030341c0d842a14800304401e2015001e0303581e0200c12148082803148483d030725108004040c6000030361007406d01d640210070036484406141103a00841d01808003e41d0350b10200d454420b903c9828002a0103885880003881c001c000a610021002e0549921265a10481d070f060028814030803000448040c010002e010101d0080380d04042c00711403103002800c01c0c03134881b990f52003a4403568040c4080d008500c401d9170700a00c8102c0007080c0103042032050386403035207410000b4202401900045103200c0e40e41c0c03806090080a5902c80e076 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 718597679 1250 718596429 718596433
    0x106080f011d04080a120501090e01140f2e0b0702010f03050934031b0f080c0d1103060c13090519050c07051014060f10030515040920060408 62
    0xc1ca0725140e0011980c13002600b4010300070961b008a00f505080c0c0b01c0c0e24000c1030307104000100311070510100e500396000d9482c0c0200d020300c0c0c00d090000401040d844c2d5600800f200c44007041500c8090f4102200c0c2401620080348074101820010302080e0803001440114400d03a111420a1940882941100e00903111500254884003007024103028110358128a40e0f001c4a10000c048901198140c07022419001255062010b0504203040d401800409001e40440c5101c0c50350241400f42c8255a5810400c0d818499070110034181e060006100020403080700c041c081e01c1103480d12102c8d114580e1301101c42584904210140043e1000482c1b240b10701900b02000320114103504580d407003001d072401074040c0000010030060003002500820040300d00428031600400d50306880401c03005603240080040740510304003011400c0642d54106254410103060a0024180d2100545541d0441440400d580c001307140c40780000c1844100000f040c46448e0303140944c500c0c8407004051044da4000c034800c00f2119 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 718598929 1250 718597679 718597681
    0x807021c0e060c0105090a021f080c0d06050d05071518050411040f0e0103110904050a0b1f230a03020d0605040f0f1101031410030b04050705090106080f011d 69
    0x103a0700c2040d00040840c0c0c014000ca0030a0381c0402a1401c540040e640904542d0168105600f141040c03a10705102480884800c000b184000744080d00c1024010204c0b8106140000d0303600c0000c10310360040c00940720240482c030100c104d500e041c036612413680c002c2503482c1003501480784005110300f9803110507543c15402e0314001807604040c000030b446240d1b802001900d0901000c91310403000b45001e4010b04110510020341d51460034101c0f9240c7c0400b03c0180160107a40400000c41c80010f4120910b80d44800300b0074050303480d642c2d8000c0042204116008088520200045100c0040310300c46584a40708000040124502c0c1044920003041c031000750080c2840e841840400ca640c0e00c02075105000f480350617042925541c4120b60891200c90840d00d19111020711090307940e040c030401c11801c095034000b60450a008210949800c4c0303a2200424035a04500003030204907050005000400703000d82070141c0380d45c5841700036043c130004403010720850280d4030000914444a0080d10b40412401a014982d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 718600179 1250 718598929 718598983
    0xd02120601030524010528020a0314160f020a0f14030105090c010806010807090509010f030302060a050403050414041b0203070515040f0b1302030a030e010201200d2c010507080702 79
    0xa19007114600d4547d021803101240c00c030100c40004100000c20f998090000c0180c01d29028003920114203280030f000e001401410550b62900307000a0a468000c03210032645840781c40007900c1c00e080b5401c410403600740241c000510141d40303510314949400450090140c0c2c2d80d2424265034542584800c03d00050750000420019406540841d40102061030b2404000e030310740000c80c55031402039004140c1070041c4542042850750500c8030981000c4070380c0040c0b00c5400d007501c1c028164003c0d8003902c2700c0080703924000c6013a0b542e142e220840d440e816220b1034120602d8520b000c0d44030341000d60300381c9250256410010070081d403038503a82d00c55a03100c4800180c000762900c41001c0319100078006d03820448070b45200350140e6030801110400380d2280d80d0b00d00c00101e841c3c000909446100b444146143c6501d445c58000c400d10400f0750311030180f80d07030000031580095101d41c0c841c0c8815241900c950070380300d8906982004103412080c40f901160302c3e8001c141d00e94440480e80e5001c071140b4040711244409540718 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 718601429 1250 718600179 718600187
    0xc0f01180e0114120316060b0118090b150a14071419060e07030807021302041806150e0f120705030708160f060c0b0c0d0212060103052401 61
    0x303030840354038091030082900c9034005054080c0c00e0300034000c1d03014900d411804500c2d100300f0344148408001c01071410314100807441c820004015800a0070251905c9110311640d1150200b002920b9015894980041d03660002e08010300302d82124501036103001d42c0a089400421003100c40300c201d01d698941c00b86031402c4c51400b0540150404a81040404411400348a41045901c50020007a181c1c22003050051602c20221601000503440300c0e008a40104082680342059980203078054403440c2c08a038407009804000d1040c0d0700043e04001700119200300180440e400b00042d5200d4008000c003510b10540192100504450615400300700040300c02034500b0b013295240c413501d01b6541182c51054482c40000e0800e00d05401c52229a0b001c01da0350319240c820031303003d6001000000040d010290400e00300610b076012456025103080341640115240d80141f00407140480ca01d40c008645075446842c45150701e0800b030343d86500180c10100450780b03c41c440005001c1c07595540400701d00b6072070100b0040d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 718602679 1250 718601429 718601447
    0x105090a02070f20010906031e112206030b010201020306090408090a03170d05061903031b3009081c020f0304080f1603080a052d13080c0f01 62
    0xe641001c40c40000c000112032400300b01c00841e1190641c508142c2610004000c0e01b183d42c01502050306106851042100c50030071691480c520b5600420f0005400044c1e110f544142010340001e030120321713940300c1051341da100000c00713442a550742400705060030341c0120300340d020554101d0352190144c00481c0028a00340018a000d1002410703417528240e403501c2d50102c40d0320128101c1c13448507000409400340d1a4174421203500c104d003124400d982c0800c107510310001125034080201801941034503840d100c4081082e1200481d8001c00501904080e840c10b4100c00220140c0b1030000708801d49140e400e640550000810b4070124002800090011583c1501004194096405501030520b41c0c1c400800280000e002400c041c2000b4041500008001440c100e2440c440080304c420085060002a0f24441100d04940480c900303e6100d602c015180d0005002405804040c0d4a05c25920304a0342040f0b4080d10122046020880301c0c01d507944119500e0b40c0d048071110340d100861540c1201d803503000f25019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 718603929 1250 718602679 718602683
    0xc0907030e010e10050105040f050103050c0108091e1005160c1101030207020604080f06010803070809041e050414300d1506030204031b060206070c0201230c0c090105090a0207 77
    0xc182e08051642050074840c004c002e016440d40c03200010300090510b4003500e40e0340c050740d81d0104030541c5580c80381911450b080610078104000702c2e001c110206020003e181c070440060b404000740d8041d03010303800e648554250481d41502e05201c0014001d2031000352400200d240307038445410005180c0c0c1c59407010a4031440041c18150b0070b0113050050b0700d459020348040c2001d040180031803a4481001c42c54032105a0080e44150700070040d0800042c1d0301002d032141641c060b2002724070102c448050b0054915501000e000c0d151900302080103100005c000900e03800b10400a0b0340030500c404101c5800002c88502c0c00ca013044500501e031038207400400040031101b1020000150911041c036031401040c05941c001e0001070340228092050291200c981c07107101244c510f03040107882c90217501a403240c800034141e00a11414903402829640111692100d880d04007030107144803c6a02d103850004d81004001d26801e104030354800303150782085070350141030700c00084c503c4e8151394506a01c200079611103401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 718605179 1250 718603929 718603931
    0x71404080106030812130206160c0510030203100509010f0b0313020402070b190915021c0e0d020c030102041d04050c04020f1b010606200c09010b04080706020c0907030e01 75
    0x400038542034207204210207140b04485265980c0e040c115440c9444001802180c505000e80c803090006a075074104aa030b40700491a03184114070290300b005000c48030359602480d04040032400100a41e545a0700071031090511421012003580c941c41806403d06003401003c1000c0154001440020404070140d64040e01d9010340c0300e050031380703039010400b60f0700414800c40381f2032907100510150f0710141160b5048051200020480101aa12100821091251001c00f5240e0020389045c0e10380c07056048030014056150280041c000782800242d580f840c20801900500a50031150b1051a0600894044500b00c502e003882c43c0d80090000d1400700d41c0500308803214800c4005510700c1c1d45a50000d041c4621900882030380710b200c2c0550900e442d1540501d40c503c00c0c1d00d0000144449a0040c0050031600c45c0c03415854036003e50030100303926203484144d4159024070b44100001e00d508a0b20014001d4910030020303102d54960702c55080c0eaa070084241301c1640070301078900264032030b03100b075102442c1c400007580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 718606429 1250 718605179 718605187
    0xf06090c091507050f0f0d050904050601020c1f0e041415010c06060b030f061f230705030a031b09031b0902030709241713080c010212070c030203030714 67
    0xb401029445414101e903140c000d0020100460402d101e410b0031916094081d01451545842c01040303481120101c0e841381c1c3d500c601140140e48200442100c0040c041c0c00d1f102020031060a05130021300179620800000c1d040c64400d490b038101402440030b200d05140204015807a15040c1c03148500980c0724050401103802503030004184c1e00e002e51002440c04110171a0780741040032100340042001040d40d4018081c512482c01804c0c4980311070481c0c51128500202c232001c00480d440c40e021480e040e880500710b00458034a00380100400100286c0031241c40810080000340714082d00112294100c1d000f1032000c1d00200041082d50084494a070081003040d00da440c1c680e049602280c205440503000104606418001035400711010740b0003050344640304045c00480c941c000c294151030a8511036520003000030603800510032a0000c60964042d48050b103440300c07002124000c2d003142e6244100c032040c400c085040e050140c0340c50740c0f0b220f0301a8059450b598400c0f80c25140140151380c1610f111500708 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 718607679 1250 718606429 718606459
    0x4020a051207051207140a18050301090b06040c0c05030d0c0c080a0c050f01021e0c1204030f0b060603150603310203010614010c030f090e0f0604050f06090c09 70
    0x2181c498800e40160b240c9035110403003141c4098000000401020610810301d600d108501d10500c195283d2100901d0003040442c1c18640c013072480100e40e4071407500766007014100c2c4100603030051690310401c021b42c0d0401c0b0104054108458540300c0103005011500108101d640303006d510b4001d946c03001024104000b5220090703031045200e42c8151191000a070728030580703000300442480b094030380104c000300039410148401c0784078950380d0181600340001078001650000d03480060001c80c0f12504c00c2444541c4a0341e40b401c0485040070300b064100d5104048a0000d1124900541524000c44030fa02c070201d407078102441804080d41c07019000c1c1c1c0e01d03080d94004506c2582e600000e408030341582d0000711040207805105040c00d6a280707412809003400604503a40042e64426440c14420340c041c079040e6110070b42100d040d02e2007051034000c006d001d40001d0401c0222840041c9040c0034590580c0d04002d00d551f80c80341903024a10a4030305a90110107800420420044d0002400c00300c40003d0800b60503407911 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 718608929 1250 718607679 718607707
    0x170703020a090209090a092109030b07081f060503060108061f021014130b0606071b0314010912080c0c0703050c0109060212160c0801240801110904020a05 68
    0xd54440740915800041c035200d1428060046600654102d0047c420100c2c0c560303401078444026111b44030b03090311900b540312400c0d111721940002550041c03144017580c2447d803c01402100111480451000c081c02c0140a0350b1124a19008644469407250300f140c85034001111042806808640d200e181c01c00200003031410361080d0785240c02c1d030782c00419031102c00b00c000380143c82d00000d0640d084a0914200012055100c84d10141c1c0c580c092810f82090b541c41000581c180240200508421340440c040151460103005800a0b41e000c1c0010302c94410208100c03d080e00c04d031750340043c07020b001002d503504500c1c010415641c01014800385141040f107890308441c902089030f40191003d071b01c100c40032143c65070003a00840103003800e840030306680524803d00701d4181c80b070100c00403082c02c16488640180407d5080100240081000a00045403030007980308441307161616055819450b11000904160140300c3d41ca90303e281e200401f400c040301c40c0700300b2000b900915044014400104a1940307040c0c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 718610179 1250 718608929 718608949
    0xf2004020a08012606060d060915060509010506040b1605030903030a08010e010506030c0a0e01020c0d150c02032502040204050d081228020d1d0f16060917070302 71
    0x6603507100e11580b421441e036004d40741c0f2080d03218800440d40e0030a50404404622594080000e994420300c1d10a01d1408600030420007401034810340c529a0b050440d0521504040c086481c219206032840e44c0700c00810500f8843c5200700000300304100003043e10007d203007020500c403a000e00b003643c0c203016007040803a00b5541b154420034001191480140080b400d061075850149c08203031219425480e00607208440f5208030342c1d00c41c0a01041d4001141e03d07130302c00c200764940340b4005400103211801c14035010049400c03605031a0700440c180200000311610000036258245800c00a0200503002040400c520310b50340002643c000c0d4007000302080320784580c0d10034020288251740a590310940030445803400c2c20301405907070802d0140305640c006030007504804845104580380c0180c0d518007400e04100144401c005007454000d4002c0141c204400c003141c04150481c0c91020b0354004800c0404440c00090a0302074000490051001401006803041340c0742c0140d600341c1c0c100e8818507180e800040080341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 718611429 1250 718610179 718610197
    0x5030c070e0a02072604180e010f09020a05010e042301032d0b1512010e010c0e0306010b03100b0d1b080f0415020f070b01080d0c0f200402 61
    0x101a40d020480c10150302000e41e03000c014040214104441542c40b40b140220300c421000040000342942c0c07000300e54030300484006285403101200e00700003880104000d031003400b03280784455213070003903180c1400c009000c0c4202a6500801c86023040b41050300548921080340350154003d40cce181412031140c8807203d04010380007420444420310303614600d0305540320b003c1c4540003c140000040b4034840404003011141c81d0075402400078000f681c44011248281100603009541f003504006024000da0040d80700041c00c0c000381c0001e105195004c00c00752603404450b50410782640c002c4004000181e4104051908400320203095601250390b1246105290058800075000b25510202901000300d55031280c00160500c1c00e0940062401811203160703080b000300f0152461110a880e610401202d40c111080560b00d6000349864504030304001c50101030034000c00310284503a035085e0010501450702c0b0740c41154400060341070142141c5d43d41480e801505156000c40d104009907140c2a0703154000360036410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 718612679 1250 718611429 718611433
    0x20a0b0c030f16020a0807060e04020d1b171308030f0604200d05070305090319032d050105030703051b040b120f160602030a030e071e06020105070311180d05030c 71
    0x3e5528010814402039540c081c1185074040d907001c0100c40c1d08803440000c412002c4400507145e45d55054402c0181420302000e0380e4401800519a103480e0f017091000301d9042028201003003603a05c0c6640b0607c0660b0102d4050086001400015000002410641c0d8031400203440440c0c0c95455031090a00e40c0384403c14004600304c01700b24003039643d00d00c1c858294058214907083c8080e00f032001d480d50f1a8800c0b40e0300b04441e0001c00701d4400344103009400001e0400d203a013204825200e448411942d98015a0702c2c440003a500344800010b483c500082d01805594101340070340540645117400c959070400b104004de8100b9262000211a076035018200d4441c10110000740a49004c81440682400c8000380000c01c0000b82c41800d0081c558000180c3d400031f20315090015a030f61807480f41c1460032095a03c4100d00c400c038a801984a0400c802c9140d044a4031600240116141e8200550650310b00855150f8011018400f20b541882e04441d461340e0408068003070704210450b0b07120241103901c0031000400039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 718613929 1250 718612679 718612717
    0x904020a09111806070201090b090a150903031704031b140303040305070b0901140c0d0608010c030b091006050f160b0a0501050f030c0307060819091b0909020a0b0c030f 74
    0x400c003c2c0c0074000d290803040f1561881c003103003a800600340144a00404c81e51840200f003003105a150001e90308050919480000d03002c0e8141d00b0020901c0c40769000480016080c40712007030260001d0110503026641c140caa85542d015055007464000c0c1c800c0b5025108070b42400301c9010407400500003140118001c0d65844d0f520b9a1500303100500c01805030600400313a14040441b148860454000c40e0000da4041401d42d0726511540a00081d084a82101500d03510b0304241000181c3c04d540500243c070003d0320b03840781c160f5500c1c03845540964144140300209008214008410300013100600c00308007446081264120340d03803514600303c2422201403c1d00c5a44000600070743c0792001c00c84a080d03004400900340b030b00180000c00d0b101c80151081a003841007000100e80841c5602c8800300d1418a81d00040201c140760307003000320115030303d00700344141c825650300003040e10451030140c204816000740030074040c146440c49004040d07104019689140c002444210110188103009040d0300d041c1d90b690a081c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 718615179 1250 718613929 718613947
    0xa0c08070308012c0c0c030403020a0b0406090807060c03031d01020307030504060b030714100e0d0f0b06040b06070312111606050603010506090109090c05060a20010209030a020904020a0911 83
    0xf8482c0901907045020746010032184d07048044040b01780e100000c0c1c10559110300c00046000d180d40200c1c1c1000b9440202c01c04003003496243e02d0003134011500c45580705c0e5252030340c074484035444000ca401800f0020b14500d1003000428000d800003411241c5c0034003101039405901c4020341c01c9801c04d8944500090302c43c8140414030600380036101c0800310840c09001500e1401c081400d00c000e01194803801121088101c0801c0c0d805000c2c503081420001d0840d400507001441c09000c0040e071500119208901d002c041460703400c040c883c0b11200700b8042e0181b860300c0029101601c02c50b014004820801d9158128000791800f00d8014244050800d0034840140400d807920009554002b0182030081c1c4c5400200480c1c1d580d1151240d0442d039a50400080001c3c1d942040040440150441a00000000344d03070301ca1558441891070544030b100a600040c0c1d54805009802c2c0d02c100d41409905922001d903030341c054506601c0090704588001c100c55246c5947c0d42e41541560000b89012118a00116107111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 718616429 1250 718615179 718615199
    0x12050a06110a091e051c06240e060a0501030509070b040609030501050c070b010b0a0c1a0105090708251209082a032505010e010615050408120a0c0807030801 69
    0x2015290288140440e0810b80e0440d143c8040140305d07061048140054460303141c0000802c06104036040001844500000b82480495188518407034004012060001885114841c04a4000d00c402007082080038500f40046000e41800382c400b020b43d000b14034000851241d108010310042c0350a8481c458030343d140d428080e085904c000c0480d503812004108100010b4808454241900c5144882075140c1c18030107000c4687c110341d01c0c00181014507207100c1d003101008000300507040320402c032003401d865510414102d507000c009580103400843c9250760018040f101104615000b1114a0641a01e1000303452030000d0341d41000d000e031a00e03400004e100380340c510304155608170b14646121401d030500d01c0005082c1e80c1d200d5001d402c1000c10316441d055000c03002130703000300c810580c00c20001d002c00c00054110364020040d503c030705000c401501d1a0317500050b02030301c103035012900000080d06402402005c0c000e80c950280c40345008100c40b140e44040000e011078060701d913250080d5a801d22560410700902 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 718617679 1250 718616429 718616447
    0xf0218040b01170309030d0f110304090609050601030b0310050a0b06030c04060207120f17090d2003010b09010e0907050a080c0415150e011e21060303020712050a06110a 74
    0x3d5000d800030408440691000504110342c0c206034904040142c0340503504440c81003200a0312403c90000041c005550001a0840380940b0480300d400c100e41d8944030010340844018030b010907015040640709401000a0394001580010f400d080450450442c00018946134411250303009000f001042c140880d42e4100030b6500039206000030110b1007202a1501d07002d07600041030040183e50400d00304082c16003500c082d00c3d403030700e0050080c1030000c019291003180c042d420410240c05905000c031040e4035240500500701d030f0b000c0141c03d001140e4201894442404c0c2c0080c4416000e1003145000262600e910480d0b6000308941405007641e0480a420402510220b000202d1410000ba1040c4101c2204054448501003541000c6c546070360013a005861303003d00d03100001460720048107a10101608000702c040001c1008419201c6081c1072614182180c070b0502026005074461001404050ba5044984038418050000c580200c0d4280d0b40d17410a90f030320b072a0a40e0108101185030f0f4000c3c2d401480f20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 718618929 1250 718617679 718617719
    0x2d01021b0d020703020a290c0c18070e1201230708130c06120e030c0d0801050405090606101407030906020f010911060901050c01051f0b0405010503040f0218040b01 72
    0x600310540c030b1500001e113400c0f00d42c0601c020001004920f1507104d0301000c00e087c00c107101c5450140d01d407054a0017040d05c800381e01100d20b00558080000b40700450340302603114401c81d40c9845000d030208000080c040c0544080d441c900c4190750304d128180c5000aa10001a40ca84d0300c0e1485641500d4440f5000b442040080c0035241c44102d02441300c800503c0b2200c1c1d050644810303290656001c10403604d900040d04140d06000180d000001b03503018118401300b00b00555281d5601c501c01c3c1a6600c0b0148822a6002c403920703d801d8001c0c00128030140307016040c4032000410f0b890043e20386440b0104094ce1a0700112003200440c1c14500d0410030f494046c0f19180e50794402c403000b00b0880b00640c4803000c030481041b136420301c1980c0000d900c03030b990b0b8050000d07512a018000020801441c061008005455045490500f100868900050080f40000490f0309a44041c0d68850440e11144e50b041c132040941c100072a0300c41d03c07086820350f0302e07200102020710407402246c083c1d100794504504800d200311115a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 718620179 1250 718618929 718618933
    0x150412050a0509091e07020f010e0a120302031306020412110d020d030f140d02030f010b0705250e07090e0c0a020715020114010608040203010c080103052d01021b0d02 73
    0x100c0c803a03142c1201c150780d860001901c01c3c2c052580c0d0b0405607203507180420341c030001e40c082640522010740e40c0010004c0c94002a14002c000c5544080c2e80c165079103407480e0300200031494103601c011580384282c0240d80c00c17080340201036044141c260381f8030301030340c001b9003000c0c2009000301c40c00c1041c802c003440080300d021403c2d1012030500b280754000ca88482c0400c2c0c40542413001d03e0179044a0030f4400c40d0b0f8001c00c3c04400114584401e03410481901951003920a070300a03151040021594032400c104403101d69500c107000f8224012000300b00150504040219401d01c14801d0000800714811803607e4800c041640c3d07101d040750b051611504440d8000b8004500d80c40060105070540c5400041001c06d690780d0454032084015a054101d0240c031141e0380040100d41c401000003141c5400c182041c0c0150b00c200c0090001d2803506030100e81c2c0800074030000d0265400b05544140038517010000780c020440c1200041450901900010b003aa8021010781c00400c4c04110300d80b0102a050101c01000166840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 718621429 1250 718620179 718620187
    0x105070305130b040c050d1b0b09180702010204120b060a0b040f0b0d1b0c0c0509071704050109020423150d021306230120060a0e0f15041205 62
    0x7002059000c2c40960080a10075600049003d10085403115802000010240070b407421b21460800703001700615010150101c12200003140540001041d20201d46c000b50800c1003802020000000100c8060000400d556003040b01003104201c0160350203c3c2405000243c0560030204107001c03845115510906041105000500201c00e4003d621001c031244a0300030b684455203211003000030700502c0900142004d07004c1401c181150000254601d01d4000c150258081e075983d4188040c512003200e03a40e00155407261502190340500000681060241e0000106500d280c1c1c0410100c4c0c84c000707179075180800c143c003904a1446900079516400049000c440718052020400b06840405c0315400a104010f0486001c950301a2035000000420a03022a20703446e400b1180d15101207000360303410f1b0f400a4104101c480032211800d8000081c980a1401000e080d510b285180d40100001d05507a01c00740108e001140c0d03020010410003007109007007026040a81400c0c0f40c240f0040c0042c01d0240c05014083c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 718622679 1250 718621429 718621441
    0x80a0e030601082a04090b1e1e2a092110110f0d0b040b040e1f020d061e051008070c02060f030a0f06050a030c0b0a020304050907110105070305 63
    0x7045000300500b40008130080d40110442495a07514198803068000e854030500c5400d006041055074001c09054496880c5519100d41110180404442c04101d034841703580505410010000314584c040c101d845410f0580c05024140e0501d892a0581ea84911902162001240c0b40000c0d0007041c0d014155150084034510600d902d4030b40000c4d00c45005515a68400800c842c02e44030112545c80b0310104246a540b021604081c0040101441145c0a1440c001004615081c10310804030300170882030041c420b6403000500c880798005698200310724650288010848901075002d408081c02d400940303014100000b0034040401d451651040c4e02c610a90455405800d40010746950001c00e43c3c0b9155208000a00220f0300d1486404023810703002d0000000c0040002c1c20342c1c80042c0b028a0300c401070108540c0c40040040130003660101401d0302040d014204110190140180107424650040e00e06180d600c500094428034100c6000c400b19200c440c603d25441d4080c41070b15030005680c10100a00d003814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 718623929 1250 718622679 718622683
    0x40201031d06010e07020a140709050a05060306040b090313031a0604060b0307050c160303031a0901050102070905090a0203010903090e070f09032303031008061006021f06080604080a0e03060108 85
    0x113200d10350a400748a00400c020341c0c403d01001c034040d07401400c078610000c1c083c3d400d03d940b98a09d11134000a04e10705004100d8901040c0921802490b0080c020140b03900c0b140c50744d40442d9400b40880469101c10005800061185156a402103019286400300b01d00c55400c1580007050062086104a19000c0b081c0419403114042e01c1c4c200c01c061030a40d4541e4190382050346060803100303844000e0708001400008055240d0017681c0c4d501c1c141d822440d5600301c0442880410a0203000300d5016812210007171012109551146902282c10001c480c410511900800c0c219100c2c1c03007007076000914450061244120515034103411044ca032500d8000f0402c09800102005c4071400004d1100c09039080c3d00301142070240545141070103410640782d9a08200c0c0740340e03280c1100742c883c58025000300000036041282c80b0804030b00301d0305150040c2c0005000d4a005442d065007552a8200c0c096503100041000c42040000c14850340c81074010665820f04039002622100f44090b907684a5031120005000c10100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 718625179 1250 718623929 718623931
    0x705010e060c04120312021305040b01031b0c0602070c091d1b01080910050c19020f07050d1e1203180302370501060e010b130b0f040b0a0206040201031d06 68
    0x3c1c01900480640e491901b20b03000d100c521941c2d07500c280042404107003800002140400c462040300d0070404520528015020765194101c200c002511030303003250300600d00407210020042c4c460b010052601e0342d10381c0d50001c0500c850f0040a100c694500c001f03224034502c200c2840d0740807424130050250a154500b8042680c444c1d03900c0504010701c21011448840007004000c00003545050240541d18242c80040c01c5904045a02424001481c0d1050ba0150011841007081c00159028204a6081805101d80800f030380c081184c0741c4280d2403c00810400c03141d803820440348078000a49541f10801c0c0b00900b6140540342c605842c0100004803c0060f40002d41800390b1300560200d013001c03c000311503000d0303da04051001500800c10510368000c020b0198049000c1d280714001c3e84103940d880fa04d01180500821400c80c040192028051140c0c050391000f504c907840e103540c011803500392141f0045110360810200007001d42d0084080c4001c540c0c05006a4802000e03184600740050881c0380440e5440380 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 718626429 1250 718625179 718625189
    0x8040e1003050a02011b050a0f0b0a0603200f1002010f150501080a050a1506090806070509010804110604031502210702030702280b0c010b06030c0d151a0705010e060c04 74
    0xca18119046e400001800d850134180e0401c05441c1c0529040c24550403130440500c04594404800d800030310051582e108040a41e5000322841c00c00007945880b08210202103524541d120303000d070403160300940d99000100062141e41c0c0c00480c002450300c00319015544000703c0080f464200a40a2016983c032100041e4021201d05000c00c6540360300c1001c01c014a021240c040a4220b00d05004c41c2c85038214080400b03c0f90f0650803a400c83da68440d08490307502030940e0300d0f0700188901002c540424040360103501050001048203241c91380e80d540e400c80355013403071040d079020580109504030407218040490003040348141d000b10107442e181c0c60003174980c03003032081c000d01c40c4140e03040b0405030980441d4150780d07240f03541541100d1507403107406000c030540007012208502e600f0031001030018103004041d280101e1040c8200d030309010322044c0004c0a08124500d003400c0140c80d2600103094205404280300d012274260405554811505189080d1004041c41c1c0c4c40d182e201f038050080800d000f1084900303c2d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 718627679 1250 718626429 718626437
    0x10e0a0b0411010e1005040611060f0105010c031205010f03020f1504181b03051602010b0d141c0929040506090a0e040501060f15080f06150708040e1003050a0201 71
    0x680c10001a210a01404113003a00402014407180c415030b0848001c00c2031380c0c4140c94591501081d1101207030344003001c503240c110071400c1100400c6070794050024a00010312070304103c41c22045901c00c02d000c40388260b02000000301e0702d880400541c208035400c20903200080d103200c407110f040e0140002d014480c92145410020700718074100c0c541e11142d030010240781c403450220407440820030740060142405445080700d9403840d0f524445102e005104501819201400500788012540c440740d4005540c0e60010003180505421a0007441d016245280090026187d03c80000e04284800c8040f103e0300000001301c042941c4500f554180ea441680d04039101100c006603504240b10109814440c154018040c0c004060240410010107400820507211040b032000300c21359690f40344981c51803a40d44414046a030b200c000c80d80701244841d11a501c40006016607003840802204070030030741c0c0003060541d080c00c4040b9052005a0f03101c191070f0340200d101c000014000d4250b0b03d50a03280c841c2c41e00003e040c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 718628929 1250 718627679 718627703
    0x51b070c06120209040519060807030c030303020904020705012a02010209030601140307030b0709050301110f0a0c02040e0a08070b0610050a031a0a090b10110a140a12020f010e0a0b04 80
    0xb12000d6011154135a1020b0400d104900744405002c000009510501405c541012030220390064005480e604a03070300302c44c644558a1468034107400070341c401c04070340e904603400700402c1c404107a090048150103070030000038800b070344401c070b48403003c2811100d40c0604590042041095a07a00020203505460030950152440c824040002c3d190010075800180003810800400902d213801140c40000c444e4203900070f02c8100440c5207080500d01c00e041003442d02c2e03082840100300c031358031035820b000c1c415101900c0000c28035550710f526840c000c601b283c00c5895510005200d020440f48140158000d003090303403155002134542c04050214042d460009003007503554415442c1d54a55015040f029a4000d02001d80254480c0d2104000c3c00009880900503a8086000340d1045d1058070b108505441e0f03c00504030010b0300355a00141480007821aa0141c811101c01d03c010503141540d0b4100d0200d42c1d002480013844440701d66007074984d50b1182c03c00c180c022507400fa010660544016510580c40000c42d000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 718630179 1250 718628929 718628957
    0x9010e0115080118020d0b04110303030127050108060c0a0519030b120c06030a1109120f0d0804022b0c0b1e090a090b010c0503030a051b070c06 63
    0x405864040440a40c2407901001c4070000d0303514520180ca00c46030091041448080030382407a400c070490003d401a03030720f180803c042001000d9980d0030503c00e1041560b903e5540c2d0010345190020782000200d100303c486a0100b590080d11a02c6035020250740500c02ca41c90942d60380e4030354400410322545040c00254908090b440340040710881145104249aa250b05602c0100204030100d111806a407042d5001042400001804a40600006d080d0380c6156551100e4101610040708100c400394030a0001110a94603000c0103507201c5c3c030000003416001c48061966140110852042090201500501016880d00000180988420702c11845401010000e25011003051000a040803c4035030022665241100c000c102540c3c0101c503800d0081c0c02c4030b444010602c50344a603035500045180c2e003000380c2c0c0d0031034009040e1140e050610021201e9144c4610b815640708903000001c00303a8800c104203a80c1c42640051608011408045041a0f07031583d582c00190194000c5c0c0301440304903080010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 718631429 1250 718630179 718630181
    0x910031421040e221209080a140d090b07080901090314060718060909090807080301171b0f012001090804080c01030c1b020112020c0c13020306180901 66
    0x41c2001051445001501c00d40707410710304540090250303100d900c071800042580b4041060804e48104440400e6100301025a42c82030011260107540e4400e01040d254005595001442100d44450140c2c1c044c1d5000e03113820070b44900700b00c0b100c080d020512407141c3c01840780020301e006450a8990040c1602d03592150301d80140c840340c1041d070004000041c03900201050900100e4424003d80c15a240c0518988001162a040714114040c42c1c0004008050402c80c1c5241a00a11a1240a4525075143c8000f94039118081e41c0242c00001c00e000c52503003225007120302007050088207100d480125581d0351044000441d10103012054504007c6000d03d070008000b4a01c204154041c03569008011002c55407038016034640080c420206980508040c284d4294000d00130030240c40031a0303664140c91000c0041940014902c00e00a90400c00f0550b5180c03250072007480202004c10498004081d088024410044004000c40440c00c00c2401030061010b80d03124000c01d020044220b0170450040c0c1e595044682c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 718632679 1250 718631429 718631443
    0x1b02030304150c0506070e18040c120f03020609190609020f27010506040e040308070203041d06040507031e0b0f041407020601061103090925051809100314 68
    0xc0c05614481c400d0780103031504411006200ca115900f5607100b42d546c0001a164901070081851304142c81c02c819194510102d114070707502c035200c4c0c80001c4c0100c1d2521b59241c6010002d60702210701c160403410800905804200e0035034442d85040c010410429180002c01d0718070018140148013030f4584c441a01107540780300002e00007481c051702082a04941a465000c54002c42000b800032101180001c40c842c1004d900b19815501d4015012903282c58076034017110441e9006054504601040c1f00104250940641c43c0488940d22001811181003500802c01110f0001d40030b1020f1520b454601e1b51608103080207c00940d030054400546240070201040342c140070b1048999000345014400c641908204600c60b01900c03150342100e409a8a4007000e407001c49105054009990080c402c00c42585041c0e41a00d034003142005d0100d004241e600510510000c00081c50307008288046400d0303200d0104000f46a00c048011600c4804604015088080d515414040500301e0000080e620054940c2003100d0f27 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 718633929 1250 718632679 718632689
    0x302091005091306030209070503070c0b07021509010c020c0609041808070308010b0307090915030609050619140f0a0b030f03040602120c0d0804051e011505010503071b02030304 78
    0x62036080c0118540104158060320380184034200940d61081c1d81c0700c0611806003502d502a01207850394030382141c1074a0315003000b048441008420b00d0070398001b44401c8200c82c000c0300c10381c0061080360041d400c07480b14200e00509040c2c4e660314101ca0810f016500284c40c034070360301050342c80c560350b2050880030602401c99568110100d40710b9010755000c020244c002050014000d81d11088266260041d9010320310080e510b00d000144041814400d03440c2d03c0c0c0c01548040c09980006035001d03525500c0400b0b0302c91700c0d1019105a08004100603a079284040e000503100d0048204025000c0341c0c08a240b80d800000c0c04225048103d20300090303c12442d9409030940f140f000341151011400e1000007035076540f081c010a130042c00f52421444034000080203450b03400d09118007806a560044a0884185800038011782c1c540c403400c0b18010243d007070802c048880110030070001c1000c0d031044c500d901e0b103210386030300803410050308200300007034039030f01540c0101c5c038440d0303610010781c50034450002174590302554110b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 718635179 1250 718633929 718633939
    0x90c1413150f1701050c0406080a0506031f050405070e06010c140703140303010305070f0e0601030903211a1f1103130b07020f030a11061b0d1110050115030b01030209 73
    0x80780c070030500c24070f804081d10050700038803660303580d00c0c4104814050b503c12000440c0340c07040820320061140d0030403540000094100d03808600b0101100b104102070345003084205503200d090205005042c409140501600c2d42714800c03d0400c00300003002c86648613009040250a040440080b54060041c0402140c00c946007040d00d81c0b44481280d2281d0003844121030500c9070381000900641204501c0080340c020807071308140c65852000640192080f00422000c100ca4036001030701154120b498810b49500114002a12449001604000199140c0058812043c02e001d10400101d00d030794051310a5010320341a403a41000c0d2940502d9402100100c40000244200100300041814041c0000f507000b2114020411304240a250b181c001d2200050301d480088410560380e810b06a00400c078440d5038049001611860540280c10415044801c1c2c0014041010908000e1002c10a029003070400309001c20282d4908103c203c48105040014005d144c0c850a000c17910307070f000f54180e400503070010380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 718636429 1250 718635179 718635209
    0xe0306180106080f011d012a020102130e2a030604090c0b0705060a0b120601060e0105040306062615070804080f1b010c14160222090c141315 62
    0x3080e01824400c2017014000c0c1b40d00c0604280403a0502840c2c42003008045c20303800303040c0c412555081c444403900c285019590204144000404c03225051001011031400101c030f1414901001d0b802444601c4142500c24100304055400d000100b00701c981107041140c00081d054035500e41000e8000c42a8028111400045070b06024040042069840740781038090401a003da040100301f0000101d12094005500ca05c00600005014025020401c1ca0504040b400c25039250386120680d100b0f5000ba01d001c1d00040452103500c00646507240c4981c4481c00941503002e61842c1c00c0c2c1c1d0003840105113004025001c8041810f02a0900c04c0743c0b45a40400a850b5982c680d0780303001c220864500174415007541c0b80950190070507110b180d412114000302c204282c50b1280b00c88642903520715101781a6848100002c4120400402c5201543d80d0444900d011500042c103041100b110303c05c03680311601c030f050f05450f04800e507594503140c600310040325040040c200d208000340c0302d011660b40d0407400240082d05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 718637679 1250 718636429 718636453
    0x1111b0708030d06061e02030d0c0207051507020906040905281208090709150627030f110a030305310605130b191211040e010e070e030618010608 64
    0x140010b02035405c5a1605130042d414081030041d030b86005500e000c01a0400d00151012100c1074000c1c0d0440300040c030496004079160800909014880c5e00c0e9080650400a40700007141080407042d64000e6084608009486250321066100c3c040c11103031030304c001c4c4104114565502c0090b4000300f02900130102441d68121500054004a0b003039a481425101e40600060041c1c1c041c05010030048201d000403129611b030a60030f43d0240000c5019442501902522200031703409860004003c50081c002c0d00c40048242c2020840f200254a0003406011180418000301e900302017110705130348106155100341c06c0391182c07000b4041c00c4070a2000d0640b0310a180001c08982c0080a0404250038151f03014400d40d0300d803c4210244900748507252442d0802c1c40340140207000d0190924001100c400210381c10001c40408202a441500410700c2c1d203c0c3c001c0103002e4003840c1d8070b00960003a03481c200941111000000680d0b101001800800b002c00140009011085c00390032400c001d1000c03c00729100b1510031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 718638929 1250 718637679 718637681
    0x10c150f06090b19050d0302070e07020105160509100c060e0f0708100516051e0f03040309080102070309030611091201050619030f170f0a09080f01111b0708030d 71
    0x20300c0b90080140c00e00356000460b141c45099021180b900300044040c0e03910704018072002201e803480c02e800b075000302c50700080c8a40d01c0500c101d1185c07849500000c2d0381c0c582241000200c005148000d000c014091064030600d0b1105400c8c0700905101d400c00c1449941e40d842c0040240016003c200503d00501404a80d40e40c400903244055070a0380040d11035141c0201403140c00c80e28200c420380107221030700c011160182c2c0075400401c645070728101841e119500750052150194420079004282c281d000003000140f66004070081c1c0900003010080d40f4200300f0781c400030a1199107000c040c182d540d03182d0642200000c05030445e030b0b00d65405014081318607025031009000b00b2086030014000c2203c2c912180f081081d2890f640c0545e60b002c0304120304420320f071301c1e0310942094601902d004010704204010020310400090052a206a51200c0216040c20300b00e6003000201e0b80107001c02da062880c9001c00030722071019a0020301c0860380741f01d030440003100c0c40c61070200e00d5440301420f40400500240c99182d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 718640179 1250 718638929 718638941
    0x1020c1e0706213b030714011104121e0b070f260117010b0d0b0601030b0d121709030703110703020904140601060503070f1206080d02100b0303031302010c150f 70
    0x900080c44c03c84501c4604030305081d0401034903070081600101324000c002054070461410080590000041038124007841001c070b85d0280d00040341c0b2181003204842004410b514110020700450049148a08140e0b40c024030280003601020600090882d00c4030002e1049200401984001c1e2408140102880d00000c00350020300802c21071541e146500104c0800500a0321500200500041c00844040d148c02c0781210000e8080c1d0304168070f800700302100351740e1034140d00b0145000c2c03032014610300200b24000d0803402d40c0c44c50f00d030313031001210040141d08100030041c0c0780180d4250030b200342c00840090000782801d2a9400003584914203d0a0005021541ca1b50352002ca034040e0803030780ea50741c0f206001e176454041141e03650000f0700704881199450340301e03000e00c035107000301d641000c20581e4441ca0480d0611000389108801030b4000180000d5000c060701680008a9054014500e0341c00c040300da406800f074500102a0503c580c101c4154200700340f80402195070180070078208004440c010300440a005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 718641429 1250 718640179 718640231
    0x907030e120f0a121b1b080310061107061e02070b0c0102030916030803130f0c240c0209060607170304050c101803110f040e01020c1e070621 62
    0x1e01201d40f0144501d0f94171503240c0800c140340c15801d0b0070070400811942109055501a1000724032a08480001d001030040c42c020007030800e210300ca003400c10100a20030b905080c2c421145501c140c80400c00f0355000001c10801c0c08200d04007012010241d8802d034600040d0380c1c0681e407062400602c8001035003040d8041d43c000d0b414002943c44058075281d400312003500500001d000410f0420120b2112a17203500d088201d18031034038085a4180c0340c8c2e01c490619004950001c10040a9440004408140c0c45075141d94000e00d810604145883d640100e0700520009181c1406410001001420f102e001d01c1942c0c05c040c08a00c2241e6a450140f615036220561648001d01595605058845190083c60354140c0e203102d40305c291101c140b0390340b22440401122040d01d0b8110700440321609480e1981d0080107047c10061002507605e01c09019894509541454240d08082c50b2044004110740f0100710f5004460251030300c0d90320b0114801241c00d0307070103c1ca0f00301340d034443c5016500301800880b0145030300141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 718642679 1250 718641429 718641437
    0x9050f011a030f0303061309060906050a0b040204060e040905032503090b180d150207060e06102402011b03140603031c09050c120f010e0102090907030e120f0a 70
    0x1407800300b855039940340c49889080350b0304140001400d5007058001c1e0321008030040e10204954140d40c03900011140340c0541039900c40d03210002c000168450f8050040c00c03010030b8408603c5c00f483c280d4000d0000c900c0700d00043c400c64403000c4a40070300104000360b4590762951101c2c1060104048141070443c0044071088010480d0420001045648a402e070b498a00d248280058146a00d01c00c02408003404807085442000c01c1d00d89450705a114400340c84040e108440018a190f11051268079040d001000d501c80c54100720018003850020a2151502e0480400010041c643c0f140c401c2e07026080c1d2113040140c00740210900411968550030441600004859880d0103865803414136861340324280d1180c0071140d500040302c1101c0050b500604540c0c2c0100151566841c01c0c40000d915241c0850000040780d001d068200902c440a110b0030f550644000e0007140b03000d0042003c60500d1034000e040c442416134500c1000c48500b002d01100040503100d002040e504c840c450758005e480d401c8050250006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 718643929 1250 718642679 718642721
    0x1090b0103060f050d0507030b010f06030b09091207080f12040b0718061d030708030c060106030501050a090f2301090c02031204060b0d120f0f08060a06030c020109050f01 75
    0x40d500900c201025280e0008640144500f03010501038050b08007801111144114100000070940d4a0303102806400c510307032044002850f10f50000c00b0b480d14171015034800c40142d01031100705000000d044a400031102e09250311800c02d801c1003051750049518601d102c00002481d140c000a81900746807095100c2d1408810540303580d50f044030240050320800d150300100f91410b000703160088081c0d00c03214144900c405098120840442d080c407950b44d0043c0382540c00030070780361800c0009122250244c041403170200055890000010b51442c00d83c8070b6803035071641d40e40e040c26070400c8580007800041041010314040f4101d0f164030a10101007480349611540c60071540c484071510100444000b00500e001ea01000d4550b61603c1d1300600207035995a41c4107500090040000d8003411400e0450300554440c01e03444081c0d441d025024003c250741000412001c4003c00001b503a07a102d0070004c1d103610703240014203c40006016801411422009026881880040261413030305400c0b40c003ea4111103098108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 718645179 1250 718643929 718643951
    0x40e070806041107020102060612010f14040203010501060f0203030c0a09150804020a050d110405070c0507030b0910050408070303051504020d0b130b06122512050106020c06040902180a0b030109 85
    0x454020000c000b40140c004002007400360ad80050181030034541100002810070149800008880040d4140215100380c88200030561900b80320380c42c0141011308100e04150081d078002501c0381f10041442d07101450101c1d010f920144240c1614018000d03618030404000410b00300945400400c0350200c1c8a0805004085418200030b0301d0b040301d0a5120201203000014902008050640201480c0c2046540f00401020030001c01c1720382c000718010902290303a4180316800e1030a280621354942049414281030000165910003124074668040c6800686d0f611500410398580601c6516158401e0000c5051146c1080b5130f804111492030807500300301c68216427581030040d14100a0b45a90120301800f50010b440410000c05070b00c00700302030804041031034418000c800c502964840500182c6003c02c11010b80c2d00380d20070103015044500046c00b20030010b0002440302e100b49e004003200c440c2c0101300140f0302030040784003908420004102002c102c1d103030b0f0b29400c1c1e141c200b403041d5500d55040c4032803091 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 718646429 1250 718645179 718645211
    0xf0706051303032003120a1b090302041e060b090906030604030e090408120705090102060717010b0f0d0204060c0314070807080a020f070f140105030f130305040e07080604 75
    0x190710341800060500032451a203083c0c0d01d900180302070402c2e14900310f6050b500c40b1800d000400c40c0343c10603d4104650306103c209481280c121108031551362041c42c421403c0281c0001103142226030407140880c0c0307051011824080136000b0301c045000982008804146880300304054034683d502901e08801a40d00e0800b050741c0d61805a0f0081c0200700f0888090307406080030b200559000340120380f054a0a00c0400c00143c0140c02107900d000050800b24030310040d0340e414402a60000d07103078940026000c0c21600c02080c003038030601c518070700c1150002c2c0c40300c0b54958890540d2442220100219100d036681c45018182c80340c0c03c00120001512021841c5020141c101070724689504a80f40c1410158640e4414045034014a40c1205611810f080c900c00680200244800f0b00209045901c45920708401600605000001c0a05015052041154000e848280b90380e20201e018849002e84901c0d00f01074030729102c1d540200007244060010480744a410280a0740643c030252070401114160400040b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 718647679 1250 718646429 718646437
    0x60f021006230604120308010f09090b0612010b030a0c0305012703080a02040e1006080604020a05030a110408070915050604030503090427030908150105150a0c080a020f070605 77
    0x3078140e81c0d40c40c1040b41840c0751148044111000340a0502d056180d08101c04c3d11001600214001201000140700705000303030b180d0200400601009020020342d0369038a0744074440c000c00c0d1900842c800611414010307001d4000c0c03038640c00041e0580d02454014101100822040d0006488641c00d28035001500160509000041c00b02040e0200800100360342c04c40e0145005003507402905c2c0c0911010621703440311341c8a540200c50200d000f01a0900d003160141241000404042c030035807041c8102641c05400204681d8050040040001c802d04041e0304000c00d401a5000b8441c9840b80c600c0102d4000c1c0e10751300903a5003441c0080070300e42603540c1f00c0c108900c901c1a400010040c0c3c000b402820050304181e0410b038003043e00202401001d0f43c1c200c140d8202505080c009030002042c03c00c04000707251040c050300207080b000c100300c500503605120103c2c4191070540e000150a040008201010750b11444080700c4003517018044513034401000300025a20607410003028040d002d051400680540a90221 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 718648929 1250 718647679 718647689
    0xf0d020f03030c0703021e0114060906060403080d061a13050f01122a0f201e010207051005040b06180a020d060b2a060108120304050109020a060f021006 67
    0xe500c1e5943d03042d00708400c0e130003950301101540f0405a00380d1012103000815984c503851180000b4030a08040083c43d40c10f00041c00140c000c010220070300c40252600b0003140c05698108845a40d20551031140340700903c4140d2140c0c0881c0c03070300207010503454010001030101c80c00b440b44d42201240c84501b0800c600a0030078941c1e001c140b00100215190f2025040810b0440c80d950440c2580d42e80c940044003d40c1d495610007001403100c401606a1030707000044482c2001e102c0100b84891aa8880746540d03500c0c00d007101710802c051711110260303c0b0800350102c611590340075050350204114000b490b0003600f0151030468114245c100007610301d0428a03c3e001004020800d17004450700d074020001c00940c00f4103261a16541c90b101c0228100c070383e0030b0003070100c0d8400701c3e21075594030300300502024411400d42142c62203411220040040400005409100c180505816540ca86031031030b0a6004041c8100d00030342110ba640400680d2640005090383c00542c42c2d000c1d6000f106c0c4100380c003001c84003d0300403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 718650179 1250 718648929 718648933
    0x1c0c080d05040803030f06010c02030a15110405030a060b030a0c032004050f070809030c0a0803060913050706030209040e19050d022406270613020f0901031e020c0f0d020f 75
    0x180407154242525071f04401c060400c17907001811500400c0c1460b079098010b0343c0a80840c07007807400f14840d40c41054070624060072100c2c14203044c02c000940b01c40d80c84030003070b000c1600c80c5880080ea540602200a0003584003000204603075072880c00460412146820404118909101c541070381490301a0a1298826400c00c141e603075078441c403c0d251000b0151a08000d40300038055004503000801c000c400e0300d400b800181c0d0312460518104019244d0003424901e078070360602190000540000b8101d025225030b4240961100c0040e400f00f0300a00c0314003162040c0d0307c03805d9665180050785881c4400458060410b81d841502004000c1eaa2800344003011440b0140072060030040c004030100e000c0e000000288007014003c814a03010075250101c01c01c5110743e040440500c20300d49400c80154203906051030040d8280070000600340d8060040003a168107054460b031049844081c0b030411403800c082000e070704544030350002d102c00e80e485c441c00c6041559840f61000c1941902e00000e0051040345003040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 718651429 1250 718650179 718650181
    0x90c0703021e07150507030e101407031206060c0f171306030b010e010e0312180402030103121b11040c030609060f0315020c19210824060301060c021c0c080d0504080303 74
    0x2040c0300d15001140306160800400200315540ad408560081a609001c0d9450100803030194176a0012500258803940900c5440c204000000d150f0034107402039203801805000c4151503240e00c87d8520f11803403010300940140e090010540a17090b40c031070003030400280c2c0c4103034901401b1030056964284609000354107074801d5070502c000c0481400107080c03c034943c49075000c50500c041c1c0400d003a80c1003a0801c84052074401c0071180c0c25980302402c00091000c480c0210a14541500c0d88554107081c028003c0c080c9031100000c0c90894000d4110000505403100100314282e075505038814021598001160024041c01c12628404101c0c02643d20082003200a444106142144841e04408441301120b049001c40444182c408464400f12000701d080d8443d0300c11898288584480750a801c50480940c00c0015528149038a07a91f00340d81c10b440180c10700360343c00c03d121700009861a0300300c06642902c6405005210810096416240842e0710150448178882404d05040e00c00b8002c4e809140d01940c4240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 718652679 1250 718651429 718651457
    0x60b030c130b2b02101701060c080c070b0c0c010509030304061b080705010915021204030f0c0b160f0219080d020702031e060604060302090c0703021e0715050703 71
    0xa0701110200000601a02980800054404a1160080383c0002d006026882c403000d41c04d14081c007644564180c9400030348010404450400290180100010003907441c40000070880150308071080041048107d9126981c0d07038110a01c0c42d4003ca6507880140641c05006250b0350240341594100e2800802460610b42401c82c100d840070308014000b010144c000305403001003058480144800c600520010035000040d080201c20800800d200310031072841040300807205100d02c03070700d260030641c50b00e4204100c450582003110201c20300e10010b0502c2c4441014480344001418215081c41456100d406035070449190503a15140c1d84c0c6095800c0e0207003580d817040042d501d140203210740079561400509000c1e40740c01103480d00b040d00c0380c120352140518a00c211100d0003000440d511003001c80d8180010fa0669001c644000806000b04031500c00c0422207404250003409250260800582038080b40242002001d5440b9594443c0c00ea6003480341c0c0a90315518404c1040302c0d50346406403a548820701600c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 718653929 1250 718652679 718652681
    0x90e04060b010e10090911120703090311030a020c030f01061a09011b06090309140102030409150909031e08010b04061116090204050a120b13060e19060b030c13 70
    0x84029810414081001c042c195990741c40703a0040e000c5a03441240450030000310a00701e55140b1706410a0701422300000e1300100000403060b03030004051401040c070510b645403c3d00d00202420032120980070114840300c0d01680011001090202101180e03220300290000608843c0b550040249030100100301080030207006c0b00401020006240c020580205414a80c1c00d500350007400303c1c3c3c81038485020340180755000500314040d003a56950704880100d444c001079981d103c0c3e881010325091f00c80380e6141c41e610340c1c502d1440041c0454003092250f0f45151034004c0c07418902c4c10100f1a417203500c1000044007880790036500d050710b0400c611549058180a019030b420b424609200c08603100304500c0c07240ca03514007450380c40100000ca0b00540c4440c28001004803540103034000b14640d070b100d80f01c1d80c00800c40c003205d03068110400d0070101c03184855501700b035800f4042c4908410182d01c641c0ba600d0010070007030b4044044040c06820300300101242d180415803134014104140c1d80c40f000c0c1c03c044132100e90403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 718655179 1250 718653929 718653941
    0xe0705010819020406090905070207051f0903050f03070311030c070b070206070501140a0b010302091c14061f05091306020a11190c0b03010b03150f130606030606090e0406 75
    0x710855a502400035414030b034180c0e4050f0708444005254450104501d80907030080e2074000359a17001501100781840c001c0f600850012720200042100960161096400384000d80051a089015030300c50144000c0710395502d0384500390442c00540302d51010381f04444080152411010568042c066a51030b10300b6004440d0070090041c1da1002c000c01c55000040c100348601d15083c000322280141c2c1b840d1410403032089415070314075203041c0341c010004140b03039950380044038041c1c469000c2540b60f0005c1d03904007158208603031442d018686c032a00043c06100002d560100c181003460200c6107213516280c4003070000441d4107440384503e001c4c818180c20000b404640180049225510740342da840c003035404519241030103005085604c445500c8010092043d80c02905c00500344241c1d00d24a154980075031907005200040046280e95684001d4550701e5490007880c00c40210000d001c03104002e0690318102c001c08251003078102292602800084090107584108115182446103820710f5403140c1b034000c09400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 718656429 1250 718655179 718655191
    0x70b0712020f1b06101809030e03100b04050a06080604060c050c0a0c0513020309060103030e061e0c16060f0305091903090f080a0c0b07230a060b040e07050108 70
    0x40c090103482c289640e208054030102000051032400003010412144c2885000b03001c43c801121000020b00105956006c000413200c2a11000120464142011101c0303203415050b40340c1c140940032000c040d07081143c01c0000d00d0344040310104415103a0a161a00b120340501c0340c142c20b908030600007030104000f6401110f2800441c100fa501e0101c86100d402e0500c84060011526850920030034490750070403020b03030140c24036940c50031807640c10902801036460005100c0241080200349403204281c80d120190740c1001487e00c03200c40001c1204010030407641064480031450300c0391138098030b42c541050000604079003040d03c540070032002084045000d018010030040f098464080c601e0071501c005c81288024074001d0741c0d03400e00d05003410fa8641c4520b4003544550025841040e1000105502501000c21036000100180d034918240c54072402080d0550125103034a45080e4103106241c0c40450343d2000141300301c07020064091884200310848220135010b00c0a94400c040c00d002950041d184190040c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 718657679 1250 718656429 718656431
    0xe0a1503180503030106030c0e03010501080a0f05010e03120603100b090a111917090c03070b0705150103050d3c050c0105070e040b010f120f020c070305010504030e0105070b0712 78
    0x2915454030341c03844d4001c0e0301080000356500312080c0f1950b400419640441c0b0118003c0c4444e5140010103540e40007102800741c40400743c1c0c0f1603103007041000d51105059031303200c1054940700c4021008a0f100484200c0380d090081c003a0203030101034001c1601c542c01031504020412211a1125403e501c002c001d0400001a010020010f24402c4d0074980c0c61041d0445480c0e4030340441c40d004444001026101038500314640d40241c815003066500410b00c07000355a22220100e8070390840b400c115103815424030309220014189400441448000310b40840001c00c2030b19100103400e0f440100e0031031200e01a09420780309a94a1403d00c41c104003c00c101d00350800c0345482820f10940205e881e084680a540c014081380f10151919801c1c1858041c6509108003424094181c50900d04054900400310301382001c066581e02c00721061021580c1551004a050803c40b080700ea202d10f8414000d15080d00c3c1940440c506180c0b9806640c17107401142d0b0790076407182030340c035440d03c1c0c08038155111402808001403403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 718658929 1250 718657679 718657721
    0x8130b0720030310140603010e060105160204240b0a020304030206090d120c1109060f0d0615030c08010608010204061b0821060f010509011706190e01060e0a1503 71
    0x4044108080d502601148030442c1d0384505d030075405402c6441c0c201140d03000b18030500041103084240020240d200c60282003556851003410702c141c58035010108020340c014600448030740341c40d40c52003885618400d070000400259440c0c4051640b140980700145005074020402400141000005400701000c0030b00b406805594035541c00091007000000301000071002c1c001c120a0024541510301840b0040e512501c19041000100e0089800d0010a90180c51000803110400456030700c0011240490060810070343c2c1c07a45040c0d00001c4452086215960030300b40c0121b2503040c180b0031201250405d0310f562910722504a003500c81050b030321106940c010418400302c0d0303040205550749502c0c40902c124000851820408100e044004094007a04000060140c84556608210f019403600c4036400c040825030380750300004118040c03031400c0f1521044c00b03a5000511000250015058800380d8481d081e9003040f4000b030000d200d40c140300d00c000c6140403040d00d56016009600507040300d540c0751064504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 718660179 1250 718658929 718658987
    0xb031f0e01050f040c060806151602060a0c06050906060d030807180f05030f06271014010501081b0a0509040f0c0504050f12100c120f0b0108130b07 65
    0x2c49408607103200c441c1c42c03018100400c125a5011074006400c81c2e041c040410305003200442c58040c402c9104401074400024807008004003c1c06101060382e0060285580e1081c4980013000c0c7c0c00741407000c0395140e013401d0104143c1d40c0042100c612414000c2e0400100c1d600540f4102e4580700080c041ca0107100c100c0c07040c54242028041d041c0c3c0681584107044240e640b8000c280f503e0004035200c5a82d0703035003002042c0200703e0f0f0b0402800401000c0a15030400341001400603609001204c0c0c2003080e102d19140c12a1244810400258125002601d07002000d98801600c070454000c104011490813030200035040d00503000b83c014001031000030300002801d076042c410090482d41400c95507800302d00c003c0303010019842c200080b00302412042c5ca006520126214040350354020485084403540d8650300c1e8a072050744280140c20031908008818072000280034a01070040140c07a20b030300c4c0050780c0348001450284040d1034070003911790300c40780b9041c081c0d5400c1c2045440ca0744a12422202410540580304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 718661429 1250 718660179 718660181
    0x3041713080705011116050f04020d050a150806070f08070c0203030d0e06010b0906190e090114090a0209010c030e01020c030d1e180b090402120103081c0b031f0e01 72
    0x161860a00400320b1030b0800001600303055029034003440c0c42d80110141d00e00305640301e4000c401c881c01594003201030911070001070040d00450001b41c80181c94481004409141c540004407001990005100441d803a40320f83c544440b01101c0703410110355507843c003d200900c0f500314242e00c00d4052074450442c2c459680080e06641c440c45945a01d01d403600c00e200c401a405121250060154641142c9401c2c1e419000c034406025840b111440c91442c00e42d8a21075600542100c0501c603401040d04800c0d603114044001c0b000c0d2200102d601401c172420000341031003064400c40e400114140c4850744601c10f265800c5418035180001d0504500501030011040d0f2070402000381e0400168071070495651014090594038006561802d040112000e01003201c900301035400c200351032013100d10316503d40d064001b040c040d200340400040700c140301c4000041031141720000b40025003a030745ea1049013080c0c04d0b19094286c07820600300c107605400103080c0680800312626040300080c0c2d098004211a100345103418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 718662679 1250 718661429 718661467
    0x1210f060305060402030d021b04020c0c03030a1805041e021c05072c06041e0312030b01021509100c0e03010504030c120201152c07052706030417 64
    0x42d89540b048060004500d002e200340e0801100a00c010110800c242000c2c2416140260f0310754002e03640003c2c02045032505101e040034402d00642280d903240e1546400a0603441402c11a418022043c1000720304b13890b01d4045d03d003c0340707010f10340302d503030380700540300d004000d600c05210080300e00400c400820592610f405650700ca0601d58848400101c0e1071aa00c1491a09058100f88240313990001660b99544903010744041c0c039007000f042c80080c8039000032518640e00c0b80d000581041c4503c0da10f00b403840e03031640060009010a9003511076880308152041e90504003911443c500360030040c0380e46180d01ea15400309840040741d00d06440000395100100e400c468054805400040c407014280051003c8001030049078070452008000411881e0745104004616015078000c0001d00d401180d000a1802c440e004041c022024500083c2440700010b0100d40c4001034003d80c41c902a04ca078820310308840302074000144058602e91441d80c890792400e041d4942480c400d48416410300c90340c00d4031904c0304445 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 718663929 1250 718662679 718662683
    0x81f02210a02030114030a02030d05133f11060d0b040513021503041a0c0f1b0106090c020c1009031505071b1e0624091a01210f0603 58
    0x42c0c1d04d50401900000f11001003030f00f13502030340c4045980d500603200001d100052030720354904152100410071042080350803541c800380c401000d5142d1000d45030741081d00000602000b2030002c1c0368100d5800040c485980707150002c1c0c0101d222401d800d0782810054020300d40000d016100040030b0107203000040c2228029a402d162800310308104908605145590100450090308a136007145841d40c2c1c0c4154080400d9aa0000320040002284844080c1d0055548041903400210784490348a4007008525241420b0810380303608200d40040e03040154031640200c0038099019069801c4040148400182000416000c124503541d0000202d0701028501c030001151030800306542c202942d00030030200b11100d9840d2015186c04a45000a040384902404406a031139513883c214100e0600c0001000c10380c2d8042c804030203004441b0b000c417012a00c000c05948a080c41000614510007004814060201901d030100340c42ea01002c1c16041d180300c4002c1c0605440078003280c0106003402d400203a0b0300650007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 718665179 1250 718663929 718663931
    0x106120501050c040e0c0c0c04020c0a020a0501050c0d03020927040b0c030f0711010912090519030503040501050706020f04141f08130f020a06020601030c081f02210a 73
    0x488010010203005003508011541103d44c281403e0074010b4044040142680c910201d0004d80043d50f00814043c080f4200d00061045403560307040b5031369680f5140308407401c0744207002602001c030b500c2d8060402e640521114100420161041841c03e41c000c0d801085c0c42684403103034104005c00d60110040b000c82003840503031422002c0c00c0618102e00305141c0508080d082807024810042e0b41c002118450754008400e00d810354500c80317a0341003507004004c04040500305001003100c1d90112a0000a5641200d00548014020011034007401002c042c980c000103145401c10171040081e5881a00a0508180500401850700e11420841c00e82130b4041d60260f955011075404c15150740c034180c000744100c07003071040100350021004440180702c40b400070405200c00c0000348004052190039211070a4060b4068103c40d02541c0701d0f4000b940d202400d20044541084200003c0b9005001003001a103039429005042d0b8480d01c0d51071180017941161619011145840440040c40ca400040700c078018524228 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 718666429 1250 718665179 718665209
    0xc01020a120b0607020f0d0c0312090e060306060f150a0206010e060103020c0715030f230c120f0402131803030608030a0c02040b0f060c0102090f042a0905030106 71
    0xa00034040c250440e00e00c44441e450480221100d803241002ca40e10950304582c1c120b80e09110030002008080c004201900d01040b4a40201c01c00002001c0c1d080304039070759254035808a41d41c05588480001c200c40442d00341c4c01200c003041070b0713050214100744401c400410498103540320320102c0c0f07490340143e0348410050344085c004004244160880030f070000402e00e0198031f070041c481030003692800b00f88200c07450908201400800d0381e1180c1e10040000d900842c05001c0e483c3c800d000c264000b0f075844480ea011031042c902158004038003c0840e00112018020308141e95520b030041d44d4280c5004105030303000f207815491500d09400b58819222051082c503820112070445e03050040444496030000c0c400c91388100000e01003140c00c150344034074032641150085640380049020400808510704580d4200300080f4a5031607000064024101405007a260440da00c2c0c6084c0c108825100c007601d0b0080118010301e0501c005103002c2e400f400c2011100d0822010300c60740c5801290849829a11034001401c0040d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 718667679 1250 718666429 718666447
    0xc0309031906050f0708040b060a150503040209060d120c05011d15010527061306060c0317060d06020a03091707030329060a090305070303051c11030a02130b0c0102 72
    0xc0302c3d90340c10100c00d5030200103602e080328001d0490308020384040c0c4a20700c2c00000500c1640c0b1071240e00050a14058000080c0c030010502802d035410a5030100d228590301000161035081a400811106420a056a01d40d00045a040d10428984c0c002540c070b83d522280c0c2c11018081040041481d0390043d4024503061105813003c03c2e4880c0180c00ac41d11510120b1845004007007101d03080407051100c0005100d443d26031130300084405070000160342c0e8031410407100103071442c2c0200e80252a24000d44898100d409642c6818140c404100c8401c1d0784403640c06040c10114031a030340601590901d500380015041030303d44804151480317a103010143c1000c001806003c145d03042c05a00c10f00c00380245c03400c074024040d400c088140301c64544903600407003012503031060b035a100d206c12000654000054035106e41e200d08000380340e580070381c1e111291000143c0c608594010103110780302d42a0820042942503442d1342320810065485203c0c1da41055001c044040303000040344004040c2d4080a200040e5900144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 718668929 1250 718667679 718667681
    0xf290c030603010b011e1110060305030a1101090308040305090103090609060204061803050d140f0d060f050d020d060f09050616080609090303060603042102101a0d080c0309031906 79
    0x81c504c154100b00010600310102a403442e018410a092400d0000700304691b1044a0f2404880d18105e50390142040c0e00041804001710080941424542e2030f07405403540741407414207036450040001c0001d030000002401091041d005001640014580400d02c4060341d2201703c10342d00402c4050325080d900190400c45280c00414000010310081f09141e4081c5c03558031002d445880d0384080d10148103400e1411240040350754110359100801d03030703100758440305565043e02c010010340c080c110b4a0040c0004c003203032900c0c24400310200345034000c02808803144e03240c0e11000500302c150981e507855919443c9060008038203000052180e40400000019600d80d4031008001810261426004040e4403050000c1c400000c0226640104103540e0790307603a62202c4c03900102c0d0101500300d0b11a980c02c0300cac15165005901003203000000000600030700c481c4140170035102c032841c0c1082d18140d11010719904040050082c1000c0c0c10342101ea44150381c00c2c1403610b000b1034142036074441201c25051020b0314a000300942 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 718670179 1250 718668929 718668941
    0x24050712081609030f02130b0a1413060e190f020403030e18040203060103060b0102100e25080a0215090303040e1803030c070f170d02070b090a0f290c03060301 70
    0x89450b0602403140313151220781c0c4540c94044080e00440740e124160000360000d0700000b201307440c040c011020040e41c5405103d00c54400499280c400c0c0b582103a07024410141d401140142c9500750390700203240e01c40300300da080d103141010074801c9256160b103070f00c000318103c92010300000c600a4a8503842c07050180c00b0070424501e45508082108100720601c0003588000551605481c0c0c4002c0000d0700902000050346802564007186000c64145150004002c0d0040741d1480b070318001c1c920408090154641101c040c00b0a801020759690080442c1005841c000e41309140b45108030003040d2a10904101280c00d6502c01d41010500002e000c0c00d118581c054a5801e034031417102c00000d581103092500700210341d8801c088000d000d0f0812b50310b4002c103218008284518180410841c13507640e2001110b82c0b0080e42054500f5a568840c0303400150480c100402c090b1030031a880b142152065415660300030428a0030340c00d2010105241c1000000800001074090013408915800c9071207103892810103003582c0d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 718671429 1250 718670179 718670221
    0xa030519020a1718120a0c020d0609110102010506011d040608010c030b15090303041214060f090f0a0f06200313021203090f040c23040e010b042405071208 68
    0x44d841078807040408000c100c80d00030700c0c0901040b99884001c0507003100d41e911103070384c003a61050b104520702e000c120659206000c820721814015806110761001a030885000702d846074041000008503603054100c880c074000d050340000b0400194151941c04003821510586074200100350340b100411610b260408000303441144141b0303114075008414020903102c2c0102d00c248803000e042d1202c1203041240e0f40e1400e0062018903000c40740c0302d241c11400082020000c2e0f583c50f07014000d00c0c0c1130170400400480e5100041c1d402541d424060803480c1d5903500205041c6900003000c1066108031419a404c600081d40a07068070050008001c07010300400c202c54414000d480c0480d0310801003250103403030702101503003a541d00300c90025654205d40b80c10346522800c110300143c01d17110113006000f80c1c1e03040c501510035541c0341d546c110300c240c0e01c44107004403a110b24040c0c100c247c502406200c02e001c50000ca0000310030207c6c9440c5003041603991700d400b043c1c0115107101c0080345500c01007084512100c600780b211a2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 718672679 1250 718671429 718671451
    0xb0c0115141f05250827030a030504180b0d0309090c0e0d020d1b030b01090f0c02060406230702010203070e060f04060804050106260d080c0a030519020a17 68
    0x580340b060003601d40c0c07007200000028580d6440e00c0d040c60f0345505440009440d080707a0380698903079101d5640249006400d10b00b006030807a0300c0381c0890604000030349500007513041d00c90b140343c28248803a1640441d0090401c009840e00c1c0d45040705c0a0701c409000451091080e2501c2c0da9050404240100362103004510001b041740410180c0c80a6580d4800511000d4041c0c440346000b030a981444848446844007001e04016034003000001c01c1549428076040b1011180108080846c0481c1c0c0c400352903020300800d005030301c6280481e02051166010200c0744c0c280d0300000fa44040003070048035180c0c00484445015035404400c10510540203002c64220b540116910b92402c0000c241d48400750003030380982da003040f8a41002408102c02540518040d006c1c440d00002d0110004207a00c0716100c1c1d1103030581c19030041822000c100c1e0300503285140195500c002980c1021104501100208002440004400b4000180e210540340c184010601f0050781d40c0c40301040d070b9100710184806003000e409030f1b40c02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 718673929 1250 718672679 718672729
    0x60c0609060e1c02253f03031a0a0e10050a1d0a06082e020c0c130b0922020411030907061106150607060f02042d0b0c011514 55
    0x6840010544070503107140742080100c2c449821101c6ca5040750301120180032003a641c2240040e02e4504009100103071103a03400340321080c0d03c0c41500032682c030060000c90300051080e60a029004540c42069441419981c2e4804899620000100341a4241c2e00c41014420b1f8401710f10b0b4207416101038542e008450040900516203003c8105a5450301800304100080c00020103550b090407030440c02c80082030561056440300458001d090302c03110340c2c0204510649030b030001e2a8640550340141440407070001c250480036a11700456940d80c55010b0340d542d642510201e5800010795913407080c012a807003100c4142d5107034078281c00c1c118a8100103402c50000e12401d0507001101400004541f40d000c4015449000c65044900104e49280140c01005244d5824440104440b0520368058008c84030410840c82000303840c41d2500d02940301442c1e0a0903100540d4105002d88440c0300018207006049200006400441c04800c948886a5401c002440340540342540c003145008401c1031090390503031910b4000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 718675179 1250 718673929 718673983
    0x1d280b1e0a03031202120907080f0708030307030c05040503060708181203040204020706150308070c060806030307060b0112090c08010515030a060b180c030708090106060c0609060e1c02 81
    0x1501c00c49100043c2004403480112080c1c1d02250182c03040045014940069401c00c10001c41c0c89036098081d4800310b20803507072a81c0021600003401411038814602651440d160200b0072005844804206030502a0801001516890421071988290140d664140003803d1a414030000f0b0700c0201d005080560004148c0c154001d860802c0300d400c036504650041c1d54225500d0001c0141000c060b421101404018000041c00848401400020f100343c1030000e015032501d0065410f4001541d00c945c250b402804500c000801a0f400360f00c070441d050510440070702c450361020040d5142480100c0d1044082901000401070901406400100242c0e00125191180340443c0e55010381c0d10001c2e148070784038821a141a111141c2044400291f80360b51003080c42c2a00849000c0c9d801030f1954800500f5020004005030410311400054620969944446860607107692000d000450405c2d28040c0d42e072a0340c4020b02d00100410400c000002c110801a0205403601a04180690044d840d015400d4801261 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 718676429 1250 718675179 718675189
    0x30106030c0f0206160c0c05030616080901052203030f0f1e0603020121020702060a1e1e120f140712050606160317070201051009061d280b1e 62
    0x82c4000c0918085c520f0b1640c0d4104411f000d40303658020b41e05801182c0502c0a1030003001e4080d402d07040705444070841511030700702281c01c803042100c0c1c2d045030b481603180c0300d11114421011000e005002c3e10380460301000030603806048641f080c0714080d540703031790b28055243c031501000e10b506420340800040042610795000070741500c4e40e0002e506403102e1003c803504c0011406070f040d240c8454014200580b90040c60700080c114a190b41098a4681c05800105000511400348007858940c40c102514101d060040d055500700c04104899081940301c0b0b000b0301c00404a03208404080b00d040c0060300d241d003040714028103051100d0758507400c002d060204200e441c0d210030044980b0038200541c0704504602038201140e100c80200500e50141c0710000511284644c150002030180145000b441511507840c904c1c001101c0f0584580c40070411110300603031410b0b05044503540d000c0c2040c040701d0403407240c02c074450449203102141c0c0740b49d02d6601d8441d2141c1d030428003001e080304c800040e11010440d0860300056 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 718677679 1250 718676429 718676461
    0x9031011040b1e070c03060e011b0f2304260c01180e0a0903021e0c15070c0b0408160b03190f0c020303090d09030f12020111030106030c0f0206 63
    0xe100000c1c0e0707030b080b01a02030203c03407420720560112600c440301407600e9a0305a002c0d1209071130306800c100040c00c072520107200750380c0100310544180c060740380024002d03903218683c02c2a15081c1300c8210298038115800090850104181c5101c5d21742d10b5040c40c025522103aa030140c0303400410001c2c0c2140c2c5030600001101c684101c000d090801604000b121024039428440d007100c0d854103210800c0c0b20112005d5000821000d10035002e170f42c4031000030900028034884441d40c990b46640320110403140ba08100581034042242d6045203460034605840b085414001a130195109101c0018200022071040c450120004155104021031a1a10603007400c7c82c04084c1421850102003103491200000030b9105010401c1c20f420107004031450010b000c3d45907081105d06a02a00821210591640c802c1200c10140c0381d00080440d902c81c51501c950407000858200314065641c0da1052071680300302c10000c3c500802d0184c3d00400c030113220007001082c2e140072607202820355208005014000c88220405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 718678929 1250 718677679 718677689
    0x30207061206170d1418130b030f100605010f0c031d030d030606030b0f1804150204030b071b0309050f012001060e01151e0509150903101104 62
    0xc11064611031903450080c4003c0d40603210035485180c0c1044000000319000b00d02d08942e84a051540a002d01d42c400301e8440d04072000d4441c1e400c0d0409100c2e9260680c490355102e0b02d081300c0024445915004a482d0240e100511b905550190f890280d2000c00c900456014000a00c0d007400c104012487c082c150003c038000040a219110b08101c20f0003030400400c403444c620040c00c0f2800f2002c4004041c004102c1070140200103400d2000c15a0301d0b003410651000086009080180d03004460f10b41d042403050041c2044030304010548c80c0c11000c07811800036001443c028440720074941003420024003c1c00d0510001801c1000c56010000400e40107a201800c881050f180030881c02031440040320404000802c24141c608080001d0032000c1055104109842025458032110b90725081400301c9010f50b130342e105000640f042400d2804c0049810007003500b107003505095061400d0b24000640b290b0b8844128403000c5408a882e1403d403508002d00c10700e4080310007080107c2443c1c01c010345074601c074502807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 718680179 1250 718678929 718678937
    0x20a270b0f150307030c03050603070303230301090b13090b0406110403080f0904061d0705070c05040c0206060405060a0e0c070c0e1302181302042a0804050d0305010303020706 77
    0xd804456203415800d1080440d0003410b4040d00038110b10280038a0b00140e444100081ca0843d08411441c06031080501668000b4000d1075542d00e140c0c3d040707c4029088154049500a5103c5225580d10f120055030180c80c4002d40811b03588000c1c0148800828090505400c1505041810000c46d60840c00c5540141d080740c4040354002481414001520855200500c16040022700358070700c403012405004003c45c11101800080d80d50043c02c1d8400b07400d943c1c00201007904101040c0e4041c00b4200a041d100c1c4901a110340e81d56581001400305d50103401c484015070050402c202d00d6103050710555a006008850207142142410319503109007000403e040c40b8888009028010f006900581d5402401c00200c4c4810305d1400c0c03050b001301020401780c201d0143c0312041003411100c00d9418510302c58030300302c03500b9510410b6680070000504100368801c0174606010440081003880104036503070100707094450300d4460510380743c40e625284110090300201482c08c0c0044c00002d42c042012001c49080b03240c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 718681429 1250 718680179 718680191
    0xd0308060f1513140d02060a051e070f030807110703030e130501080d0212040b0a051303060c050a0e0607030c0b100f0e010302120105010509010b070c030b01090207020a27 75
    0x408181c4580d4180b6944080d070601003a0400032050400310f81096038041c150303000e80a280403003408264440c0f844000d501103001d0018103145442100a0243c072800901d14500700da0240740506500d40c0098800e48900f400400c4e503c0a140c0c12500543e04052545011008419260310098450149000050070014541c1d1101416991607000c0c11040944820030805965200b40003a9100070400a80001d030081003102c2100000344c0c4180c8045604902c10540b80c04504181150f003a44051584d2658110765100030020913080d108642045049848c2c1d5591440c0303001c030150541c00c21400746841440f00f080140006580641c60340482903100d5006100c944070055144840c00f0b180e0090042001c081e080050381008000350b00c1d049900980307602c01e506070120101d5081e64024018250401000303c01000829451001880701c00d0141c0c000181150701c3e5543c81c64120b1080c0e000d41141c503008185201540343c01f85055000780080b1101401d411800c140003401d80f9140701c1e030744010300ea50790 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 718682679 1250 718681429 718681459
    0xe07020a020f040209060f0c010204260d030c020f0a030509030106050607051002070f0506090a060f0203100b0d021c061406070c031106160b090c0d02030726060a0b09060d030806 78
    0x95540c0b41c0c1f001d240440c1c403598401c404034002d400920075500200da1a001c072451002c114804603101440e1000074042c0d882c540c000030350180a01310b1001781184649500018420014400b40610910a550380c958075942c4508241c01c1d21003170f030400d500c901010070040740046c400180d90314070a0302041c009a02c40c14581801c9004c02104040030302103000301c80800041c0100458512038140c0716810170448280d003a5254012404211002c1a1001c03a20b00c080c8510a40e140151031460344016000d8a0003c880c8418400307014610050648a03481d50024000c90000340d00d81c0c4400c5605540c06070600c1016203482e0405071a0303101c0589000d12107902c203841078650004883c5945201d10035190302d4100d40c82c02c074110040448079000c03e4001e410801c0180e00d08069130004c0650002c0041440320304001c85024180c0d40b000b044440c142c3c95a0002d4805001480690f1046000180024626107030a007801828100104102e01c1800403580b1500003c6c2c04c0002d0903081070b81664004081c070640 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 718683929 1250 718682679 718682689
    0x1035706120f020f040e0405100623120106080c090a0903051207030f1b11010203090a021c050604080c0f0309130f111602041103040807020907020a1505010e07020a020f040209 77
    0x142918490611000802003101c03200c21080da80594421303070490751030100c441c950f101250388901804c801e02f61401010350110310a61004000803000900d450345143d004070700242191181c0d032000f8150b0308150720301800c80c6450980710b0791144c4500c40030b111402e01950002e2107449004d11030112141200301107643d10744254031129aa01021604200c3d80500c586061048080d0b8060403002030b1700340211940c0e800060080d44c1c0a800e01303030010601041294204004150350240c3c1954200300e4000a0001c140c0030403920b030042d80214003240d070342c00c0f035025400d0509031040300e000c50b91b03481002001000c3c1c9513a82d4601119100c450001500d50340c03003200da009072241030072030b9000c210007080078000144909080c46c02c0f203208880402007801c882c1d1418095000444019054030380500c100005401d02d1541c4651103082c80c81961001c004582e5104180c400d401403c1c074501c3d5940c001400684c884480d00ca8100308540020300144190303600161041c003c0d1300809000b590007040045441e21a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 718685179 1250 718683929 718683937
    0xd020d14130b0c0f0a050706050f220302011209110603040212011b021911010e1306091d012c010b150702030706090b0301035706120f02 60
    0x4200e002400c07103982c8581182064000c200c04603041c1c003d00c00c030344125410015946100960103030242c00c24a19006042da002e81159241e240565020002e030352096010000c0401880700d08a00c22501c1c0d421400014500403c00c0506501e49203007080320808078101039481003880400700c0d142a0380c0d82c4c8910104041c588881d003064600e40c02c000100d032212892030828110302400303500300c64040c640040801454005594003811044100f0821041540325500c2c0c100132450141c00c002825101d403000108644030307a801b017070840e55030700d004002c80a1030341c203e1500b84c0f40b002d00038410b41804a040c1c1c1c45060011140c9c2500304011031141c240c0a000b0b410104041d800103003804c0301240140080c26203036120413402ca00c6801008c8000c03440c280140c00f04c0041c2c4000700e070050300356070035569803040b01c00040c001141c2510511414810301c401540e00b0000100101c0c08406005007140c003104940d8004403074010b03041010000900025500c922000341c206801903010a1103800c0c1e910403402440317 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 718686429 1250 718685179 718685197
    0x606170705221d1b4006080d0206041a0603191509241e0c020a0b13020f01030506010c1e080a020a051209010e060d0605040510030507080d020d14 64
    0x1030340d44807000c241c0031500d001c01e80c800103903011901c80d50409003544101c001d803c030b5040705c032900c0380b00c8500d0320401d801d404442c4102031000007082e179150400e0900d050480154000140c1c405c1c400c1208100002c410481910007010960889061a0b070010b601c606080881c0900b031101048000d05002c045250308025a8148404020310310580c01c050071103100c1c0c003a002015150520749003c1d251070310300c507442200b80342071600301e10380300440c0806000d420b40795150801c51040e00892004184a038410501a00007005044042074891040c0082c07196400c50b00c1d07041c540b400007000182d9030452004071409510103014000001e080c060011128847c0f81d0240c5030700d40c00b041821020360001a02e0701000e001c2d0040b02c4034080701181885031032280155a90010b1488000002a803c10030080c1c0000d071580c2c080800d001d51103002213021110100c0718400c103074900c03203002c00034820b080c031464028080410250508400c0103c002c0e43ea2188000d40c04104019840302900e00c0c080e1409940981ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 718687679 1250 718686429 718686433
    0x10203040528090f0c020c0a120b040302150f0618040503041809060c200105070504030b070239010e180c160f030e030607080c03090a0606170705221d 66
    0x44080c01d001e000410f20300c1c00c1c11703000d0702c6070700078200091501040034000c6406008228130030188a60354a0302041001d00224298892541052400c40c003482d640380c0304442001c02c154032482d003401008044000c04c1071280c2c81010301814080480c4021044a080c0c4401c4568010301042e001c52074401000200800740c01c45140000c00304a85a1146040d0344804c54448444a0b220b09540018201c074029034414002c03840410041000030412202168810020300540f40084034140b2240c844481c440301014880044140c2101800c8041145198004082c80c1480c1003035444030110700300301b1001f502000508a0000000c0080c0030800440741c024844c0b4800c2091000c0514002c42c5140c007940048010079038140503480399090006101d031203100e43e5503500b03001e03440b000f2240b82c003a8000740051031703680038170310b4a800821058060540244020743d1004546400c0c03a80035400c0403400e40103280f14450b4001005171180825071052400e00421100156100c3c04200054089807207208240040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 718688929 1250 718687679 718687691
    0x6080c040e0f07140a3005130302010606051206060702040b0d06050105030615010e1e03030f1c020403150c0512010e0a0f0c0f141605030309070501020304052809 71
    0x48500c021015010342c1042c4c03248402c11032041941401030140b110201c00103420a03004100100d81084540034400c0032500113641503144071b401c40f050b01c1c42119010b00c800c0060001d00700b01942485820020a5149841410003d0f101d108200000e4064100b0744911004603200c020b40d074817580844c081410081881250011500d8136502a103824032440d48240541c0c00081e420014240e031340354a07454165503200111080d0410481003500c0c681c040b22030084019040d90082c0c9080000b01003810540308443d0f294440e011a0003104c140d08001420540d0041c8820030000b04c080b903094006850a11010030310704170303400007200c150080902d030003c9a401d04000007150012440b91500450b40b40e00d040c4000710388030354108152030024140c600040c0880342c01c0104a486103071002c2d8102070140b010340c90802845a0040e440c2100b10040c2d449810000601040846c00c02a84004000030b002031410146132900240d40013104a2101288400c1c00c0072101600401542d550060503540c0b8041080e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 718690179 1250 718688929 718688941
    0x1a0c06010e090705041a09150406090b040501080f06010b180411071401060b2b020a091706040203031813061806050619050a110d080f070302120106080c040e 69
    0x111030003501e202e1018002c2d00c0010801d414140500d140d1211540303090380b800803070041030120f0020020f00111204c1000c940000c00d80d50366010302002003400079004030700c0c1034091040004551040c1c0c0000141e6000f2401041c0c00321000c60410f04451040c040c0b15103504100c512485002d1000c540c581d803061922003041c0c403402c090009800c1032800b6100240d11a250300c62400c1c00c0340c000b802071000300c010034009001b012141c060314501c20b8035108828918807402d0442c40c41681c00282464000c65030984043c00a003081e1824000482c400d40c00502c25420175401080c0c4030320400d0010b00307010040c1d65007622a500c03244071903503005c0c0704210b04102d0030341c1d1840100c41855030310078052000e40c248103001401d450200c040d03e03981e0300720421022121940d2442550181e100010a00511401000d54180014107201d5506d62221584600095160461002d60351800080114040c544180001c0801e4100b00810303d06403429410309006584a018125180d40030315480201003821071420040c2c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 718691429 1250 718690179 718690199
    0x30c08060a0615140a030609090b0609060a0338070c120f1d04180605010602010c0507051c180602010e0f01020c03070609020406050904050604030e0909071a0c0601 72
    0x200c90159000c007000060307190040e05003c1030054503c0d0380060100c2c0c0da890a00a0854018054250141030009002e5035501800042d200e07840000da0f0f6802a40c000c101d11414809006680a0300440d2103072000c40c250760701c1c01d072880c010b105140b080c50342100346800e00300400b0100011104d49000240d0040c544908000c0101e18064001c403050310b00d203071200c2c100d48d01414400000c500f994840700704c1c0b4090300c0b450598400a0000701540652608a044501c50b1101c2c2507900e07090081c000401d2640c145000a07083d101d801d030300803003004070070044000406c0c4041904c515009039200c40c03001c1811103071000c4032480112a07402203100c1040c08005240340d01540f1041070744c0c9101050303070803040204111034204d024900e00034a0f0340d04100002000200d01d5480b6010710b07031004100180103a00c0d0320106120160888048485501c0b01080c84180340d08003d0044400d00201d4240c000e9141c80e80503030751500a00c0c8200d1081601e1080c5c951030070004003007a2000c00d6001030071550a981c0d40da503096 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 718692679 1250 718691429 718691431
    0x30f030c04240906030c0e040e101118030606010504030b04060b060a020d020606060301030201020d121e06090f050c041a0712020c01140c03120c12090c01110106150e0a030c0806 78
    0x20116070f0701200000c41d14080c5c01340c00c2c1402d142c0e40350004040155003d01c0040c00c400400313100c441c0508401607411001710b00c6414040318000703070a10303112541079482010701400d555900b44a648800100202d513a401421078007903030f034040304102090325145404400b400c64450034540c854400b10303003051910341c00a0141240b00d85a42150100c0c2c407500c041c00f1a510080c000a40160800000003034040d0196400e0b0081550840d000070705c400f244d00e010112000a00c00404420391288001c120710703607560082c148842100720007086142824000190584100d216a19005c1040d00d0b0380002c450001081d513400d01c4d040391404003207054001e03009480710010078000780420030010303000804c11100d4090b241c1524403d0000c500c0c0900c1e103080600b0810004000d911480400c00803424004032030b04016000300f40450003003000c40c40e4000003602029a09030b000001e170b8074142040064103192542000e044615050115a0406400200f40309180343c5d00058051040c1940001d04003c00103415 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 718693929 1250 718692679 718692749
    0x61009230d0f150c1706090403091d041a0601020d181a0d05090636010e010c030b0d0b0a0b1215091006140906030106260705040b0102030f030c04 64
    0x1001000001d1600345c404014807048824007070012000907089080a031500364000740030741004015165141c90b40e0717082e5211443c1c81c4405844420a10003001a0f481075850101c030420040c10143c90030701c00003540c2d0300c13019004c7c208001985c0f03500f126101035194030030080c05910340030303030b00c00301d400801c003001a48585054183c0916000002d94061004941c0b035000703000e5000e1082c19a01d071010b140611000442561407103500c00311036015104024440c513400b0240c944000b16180440720342c00f0303088610b180b02031406085220030080001d9a4000555404602e030000010840c4240380030136200000d16010444506c1a0034110307900220003000c282c0300329519401c90b22018803100c211420742d4034a100e600c40428140644458500d00300251039404040507000140b00e40e40c3e482d2010107540b5207c41c88480c51080101964000b5050201e400908403e80d014007512500d800008d50382d1080d071144d41c1001c0c4000c00400c564101c1081201c0003420410305440007039543e030003e813515190140b12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 718695179 1250 718693929 718693931
    0x1f03081c05040804031103120d0e060601050a020d050d020c01020a05070b0717041118070306140604060207051c0f03031e06050307060e1207030b061009230d0f15 71
    0x21288054503a4012103204a0740070080c80c0c01e0619542d03402400c803910400c0181d01d4018180661101450039015101c150041007020504007204c0ca552824450040c0510f030420008105d030800c0645c002561491010091400135500c1319114840d900034001c900c018440d55000007203298803e540f10010b040b103640244000205504d4000058544101c280381a18090280c2030008021600401900d81e100303001400f5203c860015000221880c1c10484484022a030740300e000b8070024503a05511b0001007015910305107040d06008010750b40e82d4a62140600c101c035400e0001000b055180c0480440c254004060a020646032602601600d40740d500801402c000e0058030441c40c445004000c00c458000c4d014042850070814101d83c6184079010564200c503454003500298030303040180b180118002c40c0841c5076410728a00700320034100c0c1d4208480800000900601c2500c0781d4116000c00745182c290407611094910011840495030a0303c042c000c40c428500f000140300a00c0188840300c100d07000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 718696429 1250 718695179 718695217
    0x14010303030c090609260c0901080f07060305040b0f04050313030809090a09020f28170d020714130f0c03051f030308131e11030c0a120b1f0308 63
    0x404440e4264944901408107a440b280130314a00c410146101b0101d40da001960040116480400d20f8a0001c2e4082641d9910007011352040100501010000e84864034017800f9509140e1912010301d8809803803440041428808101000400c204035001c08510304000700b85203640742001a0140c11001d1480d0155603e070300010b40d507038140c2c41090801d5034020031200310141d240090204550b10124408407000c4040e101000d03942d1381c41103280003070000700348542050900d042402d0400c001207480c401035520031082442101100050108183d0003a901f40468801c02c120502c083c040407040c91001d14540340c0e102410340c3c0d044d00614480d03d21500303801a900c440007003101500c43da910010300024035603030100c4e004104000502944078012104120111b088400350013002c0b00c0f5541c101c1311101c0030b002d000000d04003446415040803045030700e078280c01e1625012803200f80710890000c0040f0b10314400201c40d8074803810002c810458600c00b130203c3c2d03030300d91900f40c40c0d0341c0c403d809158603621401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 718697679 1250 718696429 718696439
    0x70302032406090c0d0b0a080717011d100905011b0e0f0909120d151d0f10051903410304150e030a0f0b090106030809060d14010303030c09 61
    0x1000b4280210b018401c654505420120b00c0c6000b406c03c2c0440b00c1c1d008500420000d0075507000c001d210f010745003201860007035400b4048541e0851f40038014804400503010340c610f0480030003080d403000e6803000e07050119501d4214940680148400c00306003844040d000c901110740d40e480401502c82035401d81c0c00708030498510741004003584049413023802c90340c04030006449020b60100603100640c000040443c0c110000303d01900c08419507007044071018224002012440d4940003001d8012845003941a281c1c10840348a0501c04a0785c082c032806588664030040c44041c4040443c0c0082d42c00c02d1608880c1d40d515140048103035055090000c034000042c0d0515428207034001698001d4440d003009525151402806844420030314040405016500e088281e00e0340b814000100014031440b500010a0500d20b0040315810300a8000300c100e07032410a00b400000c10400848400c204101e41d015200c8132044014000b0f882940b650141c0e001c66a4000401c05816802c060310552558603001092a228 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 718698929 1250 718697679 718697689
    0x41e05130803070c050703020a0e0f18030909040f1202070501030f181e052e0b01090303050d020409230609040c05040f02090619080a021317070302032406 68
    0x40e0350140055004101207090b4902440b843c1c0355252148055860b01c65494001a1070713070b07007240d1108009001820800c40c514805034240e542c0000580303038090030a42003060701c44d500d010f4071041c580501c20030400700b0306000224120702c070040d0b80402c0580302c1e841801d50080d201d020394490140071a0419000542540d03050183d444210000350034503407821640d440b4503400d00c2125443e041401c1102c40420045107050000340c400c0b680401e2942c0c10440c5c04001500071200300103085c01d210b49852503046242e0b034001814411640c00d850702030f0310380d400c01c00054024481c541c4001c5a0b6413a01d480d8590f4212082e29610400c448000d90040300d544140a000c906501140c00921f0800c0d8600f0a02451a140d44103810360301c0b500030018100410100401e030b80358000000c00d4124604900ad0858065000b17466130f074000c00465055050201e01c02940703047c800e5038081d02c490a113a04550011200003002004000d50300242102c0d8207070842c5000d00010810500b4aa803984442000603840d810a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 718700179 1250 718698929 718698961
    0x90506030a05060d120906200d08150303160606050405061507050c040c05070c170c042003010608010f0f0e130302010b030708030c16050a0e0a0605041e05 68
    0xa01494610364034070014400804004000551080d81e40c910540851800021100c10386000d8581d02041030070088042c1001c6900c403021034030319072011802c01603400b001c00d00d505484010b0a00e40b076140c1300d00740103020310821050000c0e003601c0082001040f880100c0001c4805034000c00e0100f0829450300c00348819078030100d500a41110400c1c6102200c000c1010003024071074056070694864640d141c001070300303507400c2009600028001241c210103002079900100f000300741142440e01d01c400210406a101c0e071762421034174070903a40d4940c007103080c2440204921030300941c296810f65940c0c45082c0a01250f00a006800070800000d002089417082c01c400541a91800700756080c0c3c0e5034070304940c003450342c5000600300c0842d52500118403e0ba10100f006038090b00d403010140d5143c0854110344c2e4903042c04150300006881110404000a443d440a220700366072402e03004402a81e00c0c52199030240680b030340b007650054503069111901d244090314000280480500c1404180c039170450590314211 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 718701429 1250 718700179 718700189
    0xc08090307170a031404150f0e06131b0e01031406041104050c090904080a030e01090b071107080a0609061419020a210e0708030f03010e1314011b09 65
    0x480308514890082500b0b028042c82800b510300807800c00000744082d00d82c2d1320140c900301c1e0314001e92151003000c1005801484808540b01800700700b1084010030f115503c030701c05000d1880140380044550b0502448030401013114054820003205242d544c0d890220206003440280d402c03084403590052600c0700071889500403900072040030600700c0404200b00c010400500781441441e010006405c01e5200d00340c005106074042c03031806848010800c1c0240603140400541c81d4141d240c8481200043c140b5501260461a14500740e078030b80701901c0989151030303210f0700400c00e144541d04908081100b01e0704840342062284e501407180300c00e0881003440010068402c00a002503017000f10030028000d40c058264005940f4140c6542606002e0b04012a10184080c082d410784402005004400c1000164010308130030700210310b004100c480c00b00741d50006010300340c100d1601d80041440c020700088070080072038108805401e48240403154500924203001c2c61845280706042d4a6441381c040c10000003160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 718702679 1250 718701429 718701443
    0x218060438090f01090503010c020a03090803040b0d05060a0e040f170f0d0b03070f0b04030501050c0a170a1d030c0715020d080901020f120405060609100e0414100c08090307 76
    0x101035034040240f255480e440369070401c641c0304400a4140c1d000d000b1064600c225402610100700e0a050042180784560030241081d48100003c20061039410f0482d59505801c007070004054540e0000100c3c41c020980c407040b202901d207418081400083c0510030401413142210302c401c000803030212202070242000b00040080240b01c0307848100c10071f4000308401c48004003070f41e1440d0b1300c2d0710032400c4003481038100203811400800c05208001d001d11031a50010041040309080c8116071400901c0e0040100c40c40555540000218000750200c0c2c0082d41c50291785a06404c40a40981419549410a2031100400d200708140080c1102281149444c030058079409401c0c16410301000762048540504840c581c2e40d820045001c18010b00405414440b1428160058508040c04c00a00d05900517103a03910401b64101030104000303140034524210340d101c445034100e50341c480c200100c0381d030080c411101c06409030034071058104100380c1c48081a248561a00c1c10280c5235420303003d03503a00030f1560080c140303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 718703929 1250 718702679 718702687
    0xd0e030a0c290f07140109080301061101060f06170708060102060a020708040510020f0d17060f0301020d110415050c030403030819060f0e0f0f0106030218060438 71
    0xc1c00040102c0b91008a144150b0500007100345070041d41c81e442040855030343d000104100d0204241ca0303c0340740001c002c4000904c042c03074554481d420305201c18460070b014052014800d4964500a40012000701499090300e00195518040504070b4840c01119042c0448680300090010f8050310342e4a00441040c0d00400b081d0b6078015440000b94064003060b12620b0090000003010703a00d080c0662001c00c40c2e0380c050150b04a80747e8200d40b403c1c00c1220608144070710b9209160130300510340001c0da88100100e8003259100d001c54086030080c0302e0034400341d015600307000c4a010700300600d01c000c00484064081d448501c14002d2412180e9000b084031008c440e400820041000c01d10943c00d00350000002d02e41c075441d83c000c05400d4400c85405a01ca072600c031520303020400c440350555010b13030b60012109210101d030703150103c400c518a4405000c2d910078154041a1217140c1c035401c0c9041c0b0548a00a0701c0980e5075030712840222001c0c000710900d20440a42d070701d103018200c17180f03010000c042094a0402810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 718705035 1106 718703929 718703939
    0x615020708030307020d0f0e04090f0c050604030302060c090414090607030c0302030126070b0c0703110105270f091501090f0b041a0f04080d0e030a0c 66
    0x582c1d0814010020019000f1a0b080720700351980c60641d20030300c0c9004064032001540c0151940081c50460300701c04100041c44141d00c1c0b41d01070080c501c001c0e45c0d10003c101180c400c41c0001401a004a40031401c500e08400c0946000c1c0c1008001080d59101c450000807903030400c8500321a41e900043c140000281c01d44030340000300380301c0d00d029481d645c10840c20814174200c40101040f0445102c4140120001c14819880940191402d041c3c1d1230b80101c1c036450744c40c130aa0000341c0f40b0b83c4c28034a440e181580180c048411010101400301e500d101081d4842d403812420700452500801e40300000006a541c1c040054800e01403c9107a0030b035086e00200040c801c2d07545412030005061240014031540a100d000d5400325111010b83c40d111040e2005000d00c24011258800c200035400725000c40c40107000b0481304100710b02c65881c3e0078190701c004100341e5650398620000d44004681042809 = true := by decide +kernel

theorem cover : BRFrame.Cov 718525179 718705035 := by
  have h0 := BRFrame.cov_init 718525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 718525179 ≤ n) (h2 : n < 718705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
