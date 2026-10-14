-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2947
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:13:08.23593+00:00
-- url     : https://prove2.me/submissions/952abf71-7d02-409f-9d4c-b942f9ea383a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 529856115 ≤ n < 530035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 529857365 1250 529856115 529856141
    0x5070314091903020a08120f0703020c210f030c0d0518120f010b030c0d0605060a05190f170d08070909090b0f090f0706030f0605040f0e0f0d1d04 64
    0x55031110b51410100182280c00200c0c0030b1034a803240000d00f1240003c64406c26aa446021801d01200305078080b115084038505400710710071072709a6503150f281c0301c19112890b414462100c01c84440e010a1601c0c04542070020460396100f003001c0100800c0110729080412880e25001d0354848050a03400000c1c00b680c00c2c1c1c0c0c2d40c840002403040c81d0950300011006000145280284244400703041099110780801e10707000d420401014038080000c0c065805568014401042c031400540c03654045500841001c03a0481c00078807041c0b09021403001e01400c00e00070401107640c010f1103418400201e88a500050181d403d020000c4081065240665054009000c0f840000c1002401504001581e10016203404100d280800d021801d00032000c14080386400a1710010821285401d804070b0003810740041e0715140a0760748030041516031341ea0180c0c900040b050080401e0500c02e53786820b0802c00011000f035203135403040c40741c14034080c2c00182c04807440c1c03015480c6d4411540840081000340402d203102d10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 529858615 1250 529857365 529857379
    0x1d061305030d1b091401080403050f121006090b1602040213032103050705071a09030c010f05150109030f0b04060b191401050406091403030f07030c11040b010507031409 74
    0x801e12000e03d920100c214042c0365120410142e480041030a0358903e4580306002640d80302c002130219000e00d00038050380a203881541e2515100c24400358042c401a1051008402004808c0111941c44104440a0300d0007580c4c00740761110600690301c1d0f000b04c4042c000c0c002c980100b40203140c00c1d03417200c00e0300c019908400002d0f0042c0c00460b24502100480f200c28001c28a0100400c5440d0f10a10954850135032018580201ca01204001c1321000001042c41c0c40c248810862240018000c2c06032280d0300320b03441302c04907a504000c4ca00c40030f500c0c00f10790020304020210504001245c03881a1900340706412076400103090b11030b401c061000d400074000fa03503001001d00910050b641d0040501800700c49010044101d1494004011a030078850342c811030001034400074050214484881110f8030204000707003280d240001e43d0803e50019089501d0a401007008100510240104807015124402044408000d90026000043c21a0050b46000b404010072258070500390023116044450640f4011300c19 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 529859865 1250 529858615 529858631
    0x1b060d0b060f0a03020903010f0b0d0308090f0a05060115030b0307060f020a0b0f0a0b010f0c060e0a052b0302040e040b0415050c0a032f1c02030c030a1d061305030d 72
    0x9130180d0b1140380b11074081e40c80d0000408010100d80300f84102884014841c0700e036111240c50440301d184001c2c000c115680586000210107000402228203100c0c0305e0303c0a00215032400c1e41001d8155191100030091608203881c282c482e031343c04031300384080d103c9509162000c4412070b00100e150501d051401040c01d1030801c1844405000442c1c010303c112a02601409035050315170044600702c080441280c003080b0300c003c41000003051904440203555100c01154264001600e031540b0b03100c080c05030085406010390710b10341915414914180c80d007205080075460300e8a0040c403640041d1000344003801c0c44c000e041c0030a041040a1040001d55104140184128200300050501543c403151300c0702c2c0460310707082041c01e00c0c02c0e00c21000340d50014070742c001c60031188011090315480e03481000405d03c0c2c180c01014646500b106880a140030740d5003800e409480740361039250201115802d65400e200c04140c01e0919001c00d0000400c564000e80040d1581c521558505c0e08074954040c0d1042151402e04003604 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 529861115 1250 529859865 529859867
    0xc03062d01090f0b041a06070326010518010515031518010f0e0405060414120309063301050f070602040e040201031409060402040b0d02030a141b060d0b060f0a 70
    0x205410400c0d020b0f0400a07a000802040116683d0000d041c418040051111300d4520f02440601007403402428054a901c1c0d0ba0140a441c1142103040c0c080861150401401181031500d041007041c6003180d0703148115410080042c071011801c5014002000e4004002400c55940c032001e1400c00c8405021100c0d4005400c482c009100d40900803540380042c035103c001440b10f81d9400890003150040b01a2410781c403603440300f00c0001c4040f5032034041845015510707241e0001e441c00079407007084400003403c0c0300e04080c800c8000014402c98800c20324040355188420803500d44000c40022642401c29503998034482120030350324090204040c10031803012400203210341050036a03600c00c9100f41c0e000c005070b80c14101e200e1848101034034a00f405e035000f80005401818668018408114000c10701550f07407080d68006458840c9071001202c0d00003030140b981c10f807601e041007440c1c40986102c9c010102224510007040c0203000b1140c07415915030b220107288000e502c40a04607508590100111540c3c0c1442da64 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 529862365 1250 529861115 529861121
    0x51002030a09050d0f1404050f12151918050607030c09050307080c0406050303070b070507080f030c0a11030301050d151d0304080c030615211c0e030c03062d0109 71
    0x41034045002c00c0c0d16006c0490b41c06c821202501c40003401800e061944106222084c04410510541b07403041210a000403110428140e10030040056038940e800c04024040e01030350071280800c010241c00ca540500042c00104015500007003030724001902075140b080440d5020019800140c1501131404017050750040410107405c00442542c05000c0d103590303182810b6907446100c0300503051207803e01c04160002c0c4520014400c03180030b450000c3c04c040074500d0100075a0320584414203100c0c0300050040c0c440790084401e40488120300003650a640c54000030801e559504540108200805003a21410340081d5026084404c000449004c204012071803143d170340e41c03041c0110034003807241038040c13203c1e4540081e4640c40713002c640408600703064002c418084502e4624810303030b95002015200038242d100411048105441c4c0100b40c180400700c200c009454400c0c0c1ea900c2ea8001d0300314203480768a40d20009600d0307400150701145400007000d25040e441807058050160885051200c000040c4040301d50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 529863615 1250 529862365 529862387
    0x120d0903090e180c0f22110f0a12060e06040e031920010501080d05070510240b04030206040b0903100c090f080f072603070b0a050112051002030a09050d 67
    0x60103d5411368000000c00101100c040d003041c0e400040c09401d070f205448050501c01c60303504c2c5481c3c0412844080356209040f60007441c000c81e08101e0208044001030f5002c150030540300121802040314030706140009284180060201d4015500d9210886500d0800c00c00c4402030800380c0a094204403490700c00901d40011225404000700b00400e0920343c811041c0b05041c101e5021500820003064070345010345942e00907100540707280c0903e69003039100c0d1b070700703030180c0c0300c002c40320814100d0b2109a0360501000075461b60025414803030184001c1c0010f07100c2d2021242515000003200d520f5046c4e84000901d04910000129442d0703040c001600c40c6c03940c0120700d07101924030408883e1000c03615420341b43d940c2c07a400070070300c0b01a6011240410090001d400b00310304403552014401c0f2070360480300f0018515406a001290242520005c00032a40264030030603000d0804030401601d61403503501c41503a503102c00801d150035180e00102289114101c0d5010b90080c83d4800d0607942d00003a4040c015000d09018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 529864865 1250 529863615 529863661
    0x1050906120c070507083f0a080601140c060c0304060e030a08041a04031d040e07080a1101020706080f060f04140708060901051309060605150d06050102120d0903090e 73
    0x10441c081116040802c070401c03c42d030441848689031083c05004040300481800345004007c8098481e8032800310000200051100e42c2c03038000b650706080000405109031802c052036982c078240301060f2214404140690821015003400791203448504202e0010724801d4281d10540c800065240c8690340c02068144c4514051103845c119040c4e1070402540380601180d000f000039111905881c040340d0000b8865040801c0984000313903400100000038a080440c1d005104a03520130941441003210304000440c00071001e1002d00340003072030414007a0428402920288075201008005140e548800c4102e05280e58001c2c420302c81702c0a0007900030a07440060703c00740000341055001499509040030070b1030485038007500780070092418041032801419502c40403038405880d61400100ea50b81c46d508104400c21b101c4016a40c1daa03625a0881164166031015066402260f035444c0c441040d5016108401e0b41200f022602034a28603049498440360b4122188145c1e40ca001e01c00b001e4012544070300c03500e20f2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 529866115 1250 529864865 529864873
    0x7030f1509020307210902030c04061410020c04020a0c1112030a0315030209010308190305160f020312013005030d15080327010804020f01050906120c0705 68
    0x4464801503440103028108501121401000102099401550710084a140410301244811213104680b40980b503111045601c030140d001c113520341441802111881141c040000600c4d11000864441140748102d10417142e03d40240507860081c8441402000000c00440d0f9800a61401a0807244060002e580b85d24604100c800c0f0303030400c00b154803004100f00e00103506010180c0e400310302501c50011009050001c820300000103031640c0c51000d000c2c51107580d041c1c1c0c68190310000300c10b02043d54940e00013094104801d0182c1c080101c200301504a42616008070340c0122628180d00d94825a07106100c20b030361240c000500c40e81040d444080d040900e50070304480040d0900703041d141800d003000280c9103801c104828452225150b00040050140c402c840e810941d94524546c159006541e03e500400c007403902980c412008044001c1c4160001d0929804509064010618008200314214103014000641d219103540354801d03100d0045501803540c01d03e1a1055140803070341c00040702210030340303e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 529867365 1250 529866115 529866131
    0xb0310060309021324080d1e111b040e070e0606032d01050a14150c07030c0306051e0103030813080408010903050c0d03141303051b0309010f0f0c031d0d0b0703 70
    0x10100704800c610400340e9801d003000d044890716201f580b2307100c800d1906002880340105807480c0240a0a8169421402d2001840302c4103414002600c0a48002d000700c0c0e0042c807810301c20000e16581c00c940040d41038031b030152030707586d00c0e03095002c001c2920218042214610090320107200c0d03c10b0000b4181c0308151a6100101c0c1d0360942e0207002120201d600f035000b41d48a0311554404d03802c0002d001c00c141c0050449010b00d07541c1c2ca84c9a01e44400d5002550a1500d0f4410403c00416152029a0f0341c030b20030800420540c95910004c00c0c040b00508002144007880101c1810b104c000c60a5170040d0140a0007000300d000c29150291a0740d111003644d214900403d54801090b0b8040d100324401146000d100c0c0f0300c250b6030039200c205404884507003103042c841c0901c030003080c15094800305840403012100456581d8940ba00242c01100f000d0f01c084108060f114940700c195034411010309079283c0c582031122503d90305400030075041c0d0041c003003150004603034180c686c10b001408003c2c501408681d2020803c2c80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 529868615 1250 529867365 529867379
    0x60a080c070b090105041b080304060e031c022a0612090c1e0310051005010c03030f05010303080f0603061605130506070803042a060e0315090c0a0b0310060309021324 73
    0x82c45511422048c1d8000340001c010f0903008114150141c0c0c001416144038141d151220f00c0c9071408a004003005a10141c40316140c252005108664080c1d420b03590043c0c1800303140007402d00d00c5140200c010a01201010a9160008102002250320011b0145002c1b00c169400c000b140c1c81ca0000180c071910544551649006061151034010b00069004083d8141043c1c01554004a2a84124201503a0b044483d00c0c051191140d42e010354440e9071941c1160030010034000303400002411003032180d00940b090102c0c1d611544406803210f03141e8108242c88410402e04010700209136440716400c184005010310401550380f009500c1144941441024148070785400b00e0700c007140320126401040702d80f0003449058010311401c050b241d0014201c0300c0300b11a2034840085800c0968541c1510360040440007031030310300b4070b090034003819401d0905410352030040b800d0003510b0010310910b0285a82c0706000e0b000e5484554006011124850007800080303400b0400c07107400701c0b080341c1000701c0c0e0601080100d001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 529869865 1250 529868615 529868663
    0x102010f05040f0f0201021501080109020a05010f27080303090c01030c08070e04110c0a050a02100c020d0f0302010e160521060a0f0f0e06040b01050f060a080c070b09010504 76
    0x8a8000302d40e401c0d10141c0396a5191381e0f02c10810103038154030038005400e858078165100740d0b0203040f143d000480c0b10341c020300c140040d200060708110705210b030034840c200c5a1a404240d9030b1000b105040b806c0c50040c0d444040d01c046036020b42040500f80400010410640400101007000710020781e004c00c103101c0c070200d00700e40f5240d05880c04000030303036214074040c0c3c1881c0070740200ca80d1a84100e01d951900f42244022841c107209250100da40e0f0b0070030580740302503182010741400c0e0300c05181012420620103034001400d02c20381f008010622950100d0355010705200b580b203001c0202210b000c541d00c01504199181420b5500d204a6100d4100090164812510340307000c01540ba56800c003c04a07922002c68110180591480101c222945e6510740e810710617003809107120001c40300010700918102824041009001600b0150060020306107400503910f0b01c504440c45413140746025101c540303580060440d80c0c03040b09000b0704101c00c82000c0c00814130042d80050300692181242c060821032844141e0f901c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 529871115 1250 529869865 529869871
    0x207020a0909020105090a0e0f0a18080c0a050d05030108011b0e0420031009051303091a07080d05011d070f180506181e090604111605010b0102010f05 66
    0xca0014041008640716070b4010394076280c4141010790400c1a040d0115040c00e6050f4461045856a44140f0042c00c0403000503541254803890288060703803142614015803441105d004145680000e0380003003641060103500c0071154007400b0384a660840c0c0100800c80c0d0400c2c09022025440e00600354064404010071400082c107544a8612507045d403401c100080c20303001c3e05114181092288019115001002540300e4003075241082c6903542014030309021280700421402c0e040030540154008280c00c40641c0045500c82c20416000d10140c0e180340c0c001d4010240c00400c41c14000c40d210b0310005984d048941030b109034058910080d20b540a641d5a0100141ea04102096501e00602c01c0c00b03211b138615100d0104810050740748290340354045116948540396812013142c2e442500350301450f2180c1d130781c9281c0d000303144904c400003600000199a040e0180a0502c01d55440c1c0300391100038400001d65009041d4100c4d08603481d602810036601a0105801560041d480c1c02000440c444140c410140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 529872365 1250 529871115 529871119
    0x1b1009030e040b0d0506040b09012d0c090e041a0906100e090109140d0e01050f040608060a081009120c0c030602070302150726090c13110705150901020702 68
    0x14800145010b00000300398103010b15070080c140c008100f020520401c075940c080d82c8a603610710b1461800701c0e00182122405107801c0e905500340f020312020b00e400311200a241960110707000902e4001904182c3e642e9041e6448408218040001c00c01031010b40b0b20441c154542c00c0709802440d656000074292107080856501d2120b4066000502c042800902c41983c0012000000a44108a5250380799081030380304000d0803562064540f2000342c1d034030815500c03141400b803c1440c20301c440440d090200d80101c0c0100800c01c0f081500007240e13980e406044000a21144060300d001803620f00820015001106064500250380e803081c66001e44900440700e402900070540c03510103401c66032050040e47c4501408c0d003c501c030349200c0c410741c4180903003070b0f9000d07906980b540301c486501214050030201c003500c410321540b40600108401032101243c0e02c1c603881e404940203e41c06416070442d0000f00064a00c921814202041c031008200c0c0014500c04a4100e0080743c141680d11480c04900380e101c1c00308025 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 529873615 1250 529872365 529872377
    0x10b0a0804150f110d06120201020d0c02010201090209040609060605010203041208070813080303090d030b1c1704060e011223070302040302040504240912120e031b100903 75
    0x500880c0103055944044102c400010482000e0208240295130742c8a240d00111940000c1e0740d052807001c3c0c41804020500343d14444880d140c5500081c3d21050b04411410921040829443c210381c030070b43c06125403580c024a00c128a00f000c2c28050000d15000ca422502d03207240c040041032540c00081a1001c03035100f5001300c0038400d115500c1c900c1e0703034001450413a9108001d0018001002d00c441c140e10240010702c00650312441d08401480c80d0039140601c8105145c07921680c1b21880d1240000d0300d14141444110000346101440c20410301c2180e002404001c2c0c10101e404654954080807804015000340c1c1e89403115a003000711013040300c400c00f022801003139901c03e40004100c0d00b400c0042d802400d9003401401c183d030366004141581c00440d021071715180820040100c0c100400641003800d05626000c10090409954104882c01c01e00d41250a00c031082504200303248440e00500e04145600c01960384480810110004020500f0380340040d03401446401c01c1959154400c50300140c5c3c155403a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 529874865 1250 529873615 529873621
    0x9020409091a04051c050f0406020c151c0e1e01050a060b13091824050a0504200303070c030507060e01021605040c201501050a0609032a031a010b0a08 66
    0x1700040c02800e070004103100301480040108203400002d400103007204d4001d03000400035501001144044540702a80039034040c0a180191211038243c1181540c8510000490f0064600e03002d240801c2401c1c100c005010040b4101072510040d0440b9004004900041c0714050f01c40c2060110b40c028481843c051700c0010404201c2d11903c2d40000e0314101c01141e400c0320741081915420b159840b1162034803241000c1018540311500d080c85840c0c0e12181c45001081607003059640c0c1d0041010300303c011400751b14010710389090703030745c05004441a0703507840185000441d96a00e86aa16000c0601c00d581c08200d1f049074000700c550011406800b2110210300e0280500e01b08800c010040c4080c000f40300420140004100000d1014001c0800700320b00c00004001144840d0920300020034160005400340720b40e190200410b81c5c1100405064a074400400b5110300c00180c168a44000c2e0300070005c880200341c4400205214040c0440c10440201c440464481d0703072030380c1880c0c8441c442c000410000400103000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 529876115 1250 529874865 529874893
    0x151a0d17070c05090f04120f020309010f0909022802150f330306100623120403090303032304021212180102010b090115110709020409091a0405 63
    0x70704101d0b1040c1607010b056034440f0040345001c01d084890b0080340b0751540034802480741940303110741075007010301e4402c2800c1c0c84a04001d44074002d0031015030520000d0140015494040c00d0840042d00c40300d5011034a400110448103034801003098011f00010382c00c404ca0313a0304ca00c04100500d40321503240e0038030f640f42c40300c0c5929006944010032200581a40c441350050103c00c00ca18064030414507850441ca4008440c201b6080c400054211022301d58241010006150040d1030011041000c0d04415008090722110745803074400c0003000411882e8020800080682000c0b094050301e00a513000c000000740c080c26240e105903540781d040880070b000000100146068900a90350254079030a03185401101d0300000481d4100c04c0300c1c4200c0c0140041e240755036503130910810303c0240013210303503c3c055403414071000e4071584200d8040b800c00140102c0ca15117850b007045000c000b0f200b41d202c00c55a0320381d200724100040030700c04012511070440c04003804645500c1c01c4100c6c00780d90044050400c503140e03040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 529877365 1250 529876115 529876117
    0x605011709010e01050705040e0f0f07051303020a0801060609061107031e02030607030b0102150f0c22030503070c0902031605030a0e010e030706050f1308090d151a0d17 74
    0x481c840656403912181c000608080c0205801407046403185a112410140b500000c801c0c010000d0a10714600310410010a40001d220760f002441805c107140d4848200840251400440d0070180d00007000031400240c0c26270540c000c0046900d980d03a9070741100e484403421070b6229500c0c800fa03100d80d40081814404100b00038100f410803104501c8600d5041c086901181c140541182c000010a42d51803001d00c265070140110590400d40203117005803403410000440011502030106843c41c0b101103910044e02982100944841d420b4600d03808055035030385030187d6258010b000407104100300d00b200080098950082d00d0181c01e100901c3d000c0305104130b404a40c4c6400050101e1013030364650b001014001070038403502c108902d005010710795403080350804c1001c8d038801422841103192101d0402401030b0284000f005c40170742c0003200c541c0d141c22200020f49104021840580304007501d011f0203101c143c840d40110034540d14420707074035031401102e003c011021080c0000a0200003e1100c1d051020040c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 529878615 1250 529877365 529877371
    0x3060b0f0d0c200604020405011d01090b01050c120a021911090a020f180f180c0f0403121e03060b0f0903031b0307030210060303050702061b030a0302091306050117 72
    0x4034000d040c4a00d80102c90b0804290303810300d0000c0d500704e5402d00080d801c1502855014003141503180e04007a00c000c4213007009180503c03c2c3c5180c0c075920400704c5071036841402112840c0d1500001c94aa403100404241c4881c0d10040240015218074840400c0032120304038110111904108804083c04054003405145180242420380541d0308006894100401038050702803000d100c0c048140c00b510201c140f00c410364800e4a45441081c0d801704d40c031b0f14007403054925640004003961058450b59600304046043c080c070b800040c104805082c44200841e40200e105006000350900b048c44410048020b604a6551780507682e050401006440049007130b40008055240c406411640f52520b142044c2001008000421800380c2000070700300141a410866035030b03c54031300002000340d82e1555030090254400c8000c001d001d12000700303444840f4000d00b04000c29a04484050f40ea80e8079802c10001c0c0250702c03030000144213400c80507440d02764940522803402610410b85565000410b100901c014a59000b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 529879865 1250 529878615 529878617
    0x7050a02120408070f0b031003120c060c0f0f0c0c090b150a0801051509030303010510020a0c0f060917070b2b060e0a020c12030718031203060b0f0d0c 66
    0xc0d00d11008248003010082c0000c00b11000501030301d071300302039040070819001c1d0321490078040c0600910402105058442003100da0103207070010881d0306e0100503202c8041a0401500d4203140c004d1002d41c10350032980341e1504800c540e030f0b030440d80b80708400141e070202c0c1c5501015001404880f828042c006803940729004121000301580d00402c0c03009c444d661254008450b2000080c040030041041741820440d60348880c00c00c1111b039050105001c00304c3e550380014440d1620a4200341c414803003803402070000030759454021110804683c2c643c0c101048414031031040340000340c2e103c172000070034000c90210600b00304000c0015051103450690300880603003003020011103e000b419058040c0000741a0343e45003801c0741640102e100362802c444005c8404000b00300f44030030760040008690b485808248250b0000740d039011503842e87c403100c0c41151100c800c4030f80001c070001c40e01004001d1110000c000c2c4007200b06076405004064a6103040e61550144c2d10b641c1008840a211581a000b02908666000502 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 529881115 1250 529879865 529879873
    0x141f0e0708030c01060e011d040605180f07151b020d0c0b030a0c020115060507020108090f01021813060f030b1f090905010c02060705040504110c030319051e07050a02 73
    0x103944119003582d1041d812402c0a82d51170b1800c01a0021040105004050707006442010380344500c800c0c0e0004400801c01444c095441000807002c0a0030540d4043c9100300c6801c85062000095203580e84aa00b401403101c40400700e5140c0030503501c0b0392400c000c1c1c00d0404030b40c20006c4045609001e01c1c0c990b4020103e9a280038440c2c040350600d6901d014500c070308000ca801107907217004408043d08403244400759200103200f040d82400465000000c0315003240d42842c1c04005e44c1e60300c03080301c0e08003042c907181043e040d40002600305402071501c1022000c0b00044644001c1003081a50b03030402c0b41c809102c1e550701c0c6c001c2d0308020400319a40c0c0311501e62164032910951340e0461000701609101645802c0f0200241c0c0d0f8030200d401380301d024841c16001c8595800108040d02b413495019215000314860107125649641c501c0e030313503640e050041d640010b1040c0301302c81d224141458080141d40511045150080c03502c0c2c00074041030208000c010b00122004484071540c1c56110089420b0741c000006407041d441 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 529882365 1250 529881115 529881119
    0x1120906020307080415021e03100806010b0405120708070612090506070c05060a050c190210020d0506090f010308030606030916031202010e0c060d2409020403141f0e07 74
    0x2481d000440c072030601a598030801e0300e003501c0e2141108070314200440407107206216a0759640707140010802c050181c00040c1c0d8590f503849002c4036022400d50070040550095400011f030400f082d801034819154100c0d500323103240c942054050b0b41c0d61400d20400030f4991056038100300e11070240c412200d010041e4940810010402e03150342c2d1401000361202030024582c0a03641042c40018409a80c0041e004082440f0314240600110350300d025000040c0c1d0007040a5170340c502d446001f00f1082c030804101000564813401c03180b20450080000312140c5004420300350004801045a82101e13060b00c0e4004520345c195210b403020b01a039030300005d255407510311400103020010440c049203c002103200301d848100b034103003190000307095850b401002c122981c0000034031602651550180c441c1c0c030305171030400131741c511818201d00381009005200440c0e0305201c20000c1150070403034004100b0342c0d008034500d02642140b042c555955035122900700e400c042c5503094104010700e058102480c4640c0100444507015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 529883615 1250 529882365 529882373
    0xc010e090604050403090324140402010e0927030703110f030d0f06050619030b030c030a0609110d150b06031e10470703030209010323071409030a02011209 68
    0x401c0c8d00f00d808020140303030101c01c4072402ca004500302100900461926402e00b40d001030a2290603548080c480e0ba2684001100c6126110b2010380200c41101103043c40c00c1e040300d205450b40d00c18242900025180100150320060000d44d901c041c1851000640c81c007902205507100402840d82c100c0005a125000011a50348241c0030780380d1020202c1d4160005000504090701300e80303902c600540a0740141c10104007903074000c1588490740e6041007010032090605c0c030f89040c450000880144c5c1c4800c0c40301520050000d040c040780810420210200030020150040000e00c2c00100d6030444181080d001003520146072900c2e043d084010300e5201001e035511191858085000c01c1e031140400c0303140715018488895500307070b0380c041c0c2d195010020215190a2030301c610184964580601410b80004060200d03910030361160100c14507080f52492428041c45a2198107030041d00e40310000740c1110300015581c140c000855402c8400200244444195580103448420220290309241c0340d4a803c003002003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 529884865 1250 529883615 529883633
    0x60a051b030a150503120a03150e07050301030308240f010903021c15050c07140708070e090d020c01270b030108010c171009111b0106080c010e0906040504030903 71
    0xc09502d0004581ca6403100f800c07400860881d40054480d07440b040492480c460340004841070030300145404a980d000400e5a020031410550000681480443c2001403642c0c1c044081c505983c843e0741c41540036290444420800019602c101c004103084509405080c80c102d04003030810b5606040403e802607503600060040c8003815040c8080304c043c50440030130040030400413103c000b28084200030a007011003000c0c0d00760007200c800030450420740440700c0c0321381400c111100040810a0480303011580700d2034804810030058403c500030340f11307001e130b20002e80e400031624185903030f0183e64844070300401a20303c10880401070510340c085000b8460104490004500450180801d200003141040324024018040302c6401002510520700c1ca041c4030302c522602091000b100c0992401180001c020880042e0510424045800c10710201c2c811032140782040d00300000f110340c8041514031031002d03070700190b034203030505590035611082000004000d80b8103a800250068000c0c5054a00b00d501c0b40e13075030911 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 529886115 1250 529884865 529884871
    0x1e0d0e04150906140411160206040f09020d141e15060706150602241e0406090c050a060c0b071e0e0f010507050c011409030a0b091e060a051b03 63
    0xc0c54481200b480701031019602130707800301400c2d10300301308003140c228582d8010300a003070640425100c09425001996900d2050340c02030401003402d4550310341d407980140025880040c61080c054184800c8682440c2c03c0440280704410340f40322000c030030300700c03070f6844d180804000c02040c4000d0801d04c00e0391413500c41c54080d10320144a1400010a05ca15000c00c00d000304140e8030880031988a401640c4101d1640c00368021a203080160081198842d0b10404158043c1c1d0100c003c440e4040004000071b000a42d002101d196008032a40c001840e00da00500030b552a03580640300205500e0b0b0140390008411143e21a8000039602c2c25501d210038040e14070001e0b084219269000403a810040c00c0300d803070b00c02c0101c50300c07100c2400c001d0316240c0103580761621203208400c00750612800b00c420381040d032402c2d8219005408010255061b8880328500941440c1040d00d02c010070b8403d0b00c1c010000180710018020350008014010718881c2e450104c3d00c40601001003001c800708107e1148221100505400703580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 529887365 1250 529886115 529886129
    0x18030c0f1509111801081903090306020a180e0915090c09130606060503100303031806020409020714061512030903060403091404090215090418050a03021e0d0e0415 72
    0x4400b01c000404c112400440e040c0c200d05a0700c59400400000c4000140b40514001c444000c3c0080712042c1816035244101d60b04c06411540009100240340e03030f02102e458045840064440105a1074000c1c0c441101000c80da01e01159000c0ca88a00030b101c2ca04402c01d602c0b48c40d030b00803039100800c1c4c90701184403450166810013203815600d10241c104440c1d40185405045685001400c52a01000c01aa40c2c0075620000d018143c1d0b130540080a98002030319070342c409800c40019907031103684200501c0250702801095503191100034240070001c101007103440c0211800800c1c05a06507569042048003503c0c07800104191004101c9140d6030744080c401684580e01a0321910044c51401da5418204014103134a584207038500922040113907101400c64880301458030b551522124a8000304006201100131048002c40f06214003081010005484d01c00a20a0742600d50241c40429000b249007000c41c5400041d400800583e1040c6100340488080664003c101044840ea0f2603101c610140e2035030000a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 529888615 1250 529887365 529887383
    0xf07210f020307080f040f021e040e0f01060504020702150901120509060f0601020c0109030b102105070b070f0204050a0b04150f080d170414030c0604020418030c0f1509 74
    0x88242130f001404143e1004001d40401c0541c9006d5480b020400030b0600000e1080c0e24240031341800d241c016552820070302024204203d0201c0c488000d9a0380c818500d440440c03582010804a52406c1c9402581c0d80141c0c02f40c80b1000718901141c1558040c0c00c02940b070390410600d540b0000c182c43c110b00549020f08000c1700606500e0505580d0416a04801002e0906560148100c0b8440341d034440360b00380c00c0b40c0d00000c2a6580c1d80351a440d044044900340c3c0300061440056504502c580c900c90285000e440c402c40840321359540d1982d81a00500922002030202c1c0c0483c1c1018016040030307008543d01c136800d0840058004942c000040813105030041d610401000b90009103c0c0d04c0c086048100a810900003d02d80c042d040c0d140142200701c50000003540d0984000400c00f003011584080304070203507030f20603640c03104540c0f09225607420003120142d20036418200f840100a0201d1104100c09415980311500c51f400c0f500d41c0c48034402e5108080355241c0207030b10208034600f85803050800082c8250560 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 529889865 1250 529888615 529888621
    0x15110607050d1505090a09020a051206010e0108061006050310050915040f0e031e0d0615090506120606070f0507080a0203010f0213031205040812090301140f07210f0203 74
    0x1440443c0c0d0310a0580415182d83d20050000f903841c0c01c0c503180d0004a41c080814514894400b0490610007075200c0382c1c20101c000c040040c10351010548038141c8508001d0003030503a80c0c0f150b010759240c00c240d8000030940f012000a0004510500065522425100d00b0040072951400030034a41807085441c2028400b00c509100000e181034022211600300308442400781003159075025480713220b44107000c04860700d80d6840f00100300c00c4105072107201c014464100f00c00c1e566070b00c0b1132030321144612080c000200741c0a00803415141200c15240b54803003840d08802c4695410b0240305480c0c0c084c0c5002d0f02c040d8a92130710200011400c0281001402881d8083c11000c54280305050a50f406040740e0700300b0303500511443d040d41006600840480740c1110b8602402650340e00c00340c4151050f90048101401030348000070340e0800d050f0040050b070900380c0c000c00400740784410440ea10034054400320742581103900441c0007580318041c030ba07800c0c0b460320500712400e505001d800e108885484111003495038003c410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 529891115 1250 529889865 529889887
    0x5130b040b0d0201141c0903050a02070b0c07061b060e0c0102011109131e0f09030801061719060905010e0f0f072a020d0b04120e03071511060705 64
    0x207940014070182e50086400ca2280d0010340074a41c02c04501d40c501001203061061000780d0b00213000c28880b2400100705055123801e004160741d004201c0c0c03401512404800041c0785000748121010202c01101505509080040441d54079034602c154030708070380c488024600451214418075419600420041403038445000003e401d558039102d00c401200ea00b84500c50350303a1107060f4460009500900d00145070000d604151a441e2940c40c08017003858603100f150002c2c8505940025543c500035150031000742e9a554044800c0403107100f00507844841d900214000e0311030b13011034000041ca100404600309880d5924035089510990005220812140511000d84d804a2116810016000d401c0c820752904403006440a40314030b020a00791142890300200c03407200c0701c0c4802c106030340c0109036001260f030074245198003400503541542ca01c0c05011112902ca4051a5103100d444008dd005d81070413071070301000c101d144101c0f0200a0174014004074180102c201401218843c14480e21003075103480040030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 529892365 1250 529891115 529891121
    0xf0e180a15030c2c0a0b1e010c0303200c060a050105120a080d1107060b010f0e1c021201150f0b0a0806060c1e0d0215010b090d03030605130b04 63
    0x8940702074000c0040034000304031110301800c20b88011141000d9890701a07505156030000c42c80c50462400b60020034403007540c905030000301ca02c00c011940c0d034041030310500800306280450010303507002c40e190070700680010f03000f0742105800824400f5400c3c2d5901c1001d040e911550300804800165412100801408507090704c9818054001038407030300a0140410000c590b1000117650142002401092a4640d4800c640021201000d425945a1a007401e46840c40141100d60007a41c04100d03100301c01d43c0c006200f40780b140e08203c3c2c010070700800310380b17030388001006104103c205a800c080701c1807140e110728009014286080c842c04c1000c000b014a010407511000c8038603000341c03031050010081006080c0c0d0014155412007400c5079000e986a004004e020316010a10741004e01e183d50380071001e01e0340900481c8070a00b205144d003e541207420701c03e501a00036007090140c0003c001c1c081c8040c01c550b091128140c042c461003800c0c0020040e40700c00000e00e0846003078180342540c40d100c10a00e5103a04040c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 529893615 1250 529892365 529892381
    0xc03060c040b07170f0a030605040b01140a1119051e0a080d020a1107180b040612141618060e160e0103020f0d1410060806010f0e180a 59
    0x14040c41e041c2418040503a016200b5520050502c001c01500c0031544c0004004031010101e401c1d812a58842c02c00304060090285845001e224501d0b11802da034095000d040e03521080c844e140f0459142c61003d10080d910807440d004104458812408507080904144120b4944d0b107008100900c014000790002280d080299829101d094011401c0c0b40c002a642805907080300c24842409a00c4030160007040300c0c0042c41844070700d0203102d4220002107204075400e000d62005140c441c184141007044044c002614220f00c40d03040162a0500304a0124100308440c084a42c0400103855041403140e26020f07010f0915041000701d03e03001300820f00a00e01600c5410000c00d407040c9500359520b4000411110340f1030580c1c00405210048a008038103a100e0350440d00d001c0c010410301030b2030b180d0494240c0c00030b0003045004181c40e00041c0101d064a0b01200041003240d00340d035600b854a948403001101c108400070000010320000c151940d40740d41e039505601810020040e41c04034240780c07802409007950041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 529894865 1250 529893615 529893631
    0x11030d050c0613021305180c0402070803060f040212041101020c010305040210080703060f06020a30030e0102040e040b04020a050109050a05061b120a030c0215061002100c020c0306 79
    0x4000c009003150010400981c8408022a50701c0002c841d4004117a045800400085801c1d01d044100a01400803c0500b5560340b6503404031a40e0b0410705003400102c0c0720703080f00a054040b003400007580c545024404050301e4507000c0d00160030f0100070b2030b04076011101603600316001c810382100d143c02c5582c10807110803410703006d190600c0542096000f0450314050300082108000128002a00550080d0406c030018124a845018096171b1840001d4554100c518100d130b10280e1141d044401e03045c0148000b1000124111258001000100940042001d13030600312070b0795000e0000080d10400080050301c500e0140720b801085107814410410114040d400040c18000c2e40101809261110000f10003960001c0e100956101c240318098a81411507116210481c41480821856081d15201402d400c008580382481100050320050b030f2100c030180e0000842c800c0080000d0114546910340c86010065401502c607000c0f1100d034240305550302100c807580541c1c0462400036150030100000d035806050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 529896115 1250 529894865 529894867
    0x810050c040b070201030507030b061b0c090103050705091f0324050106021002070606380901050910260105100305040206034c0b0337050411030d05 65
    0x400800381c00c0c034043e0040c00fa04140d42c0342d0008080d94002e81c04003440e604010456902c034010700313102a001424405201030b96001da0303206106581001020141a250720401408100b410324080c854003641c01420b0390300702c604200d003200308103c0007040d41e80030b140100d810002c0840346840c0800c8a48480c0302c0c04111a14210041152690100e14407524002c803400c0035a48040fa400d0803400340802d034100707034000e1489828030309a203044c030300c08003140454120002210a40c80524052113006195146021031810081084186007000560288182508290954040440715043da83c4525603a00c2e95134050240180800e00c1c041014020b140018a018001e51401e507000c28440d00000d0811341d107041200c03507401e03010681103c40404900302006c1d001d292400c42e80c040c2d640c0d143d482541e0b207c408140c8a000c28030244104c211303031107040c40c1e07592028411401c00c0b15900c4201c4000342070500018200c401c280441c1c00b40111405580106802030050610303104050602c074803840f0f002e05100c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 529897365 1250 529896115 529896119
    0x605250506070f051c0b01080907030506010e280b0109140a540c05070210050f04061707030501030f0b04050709020a020109110102030301060c23070810050c04 70
    0x400003280d82d801140c501e415440043c003048113aa80d402082091001c440e80324985081109490b4040c00c4038007070981c0d5000050b151104442d03110039013404081d00300d80024005000b408003180c43d00390440c040e22244401d0b0308050010300c1c4030b900c00800c109640340e2030700e1990526603800b00e14800505044a040805000e00c0e80c00a040424244983e100700c8416490746045420801c41c6106003030000566500b8009100011668010718a501c41e01004002103141e4403104440c45803954805013a00c070b50785002c900303400304001e20340d240303103480b00b004010003d03007890441d1a0003402c0280402d850321103540404100319004504010494420180383c14010000300b41c0c0007482c007001765000015092030340c44a040c1346041c5210703500402c00f014000a424403030309905501203d90303103010b041c000f2102d54901d0012601c0344400e1058100040101002c40080758620703130541c0000c0c0034050290901107082d89c0719804c9c000180d0100f4000c0d0071a031417078001c40d81c00d8068103038070824104245240c03034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 529898615 1250 529897365 529897373
    0x6060e01030b03162c160804020a0302100c02030f0c030616030b0303070b150d050c10020a0203060403080405161d0717010e01050a0b120402010c08040f060525 70
    0x6880560100e04050311180c103402151018800c3c076445000b80c0403000401c54035544540c004004180b422000500000f01130301c80004140400c50050f0740c1091800305500650f401181c00d90000781c02079078021003100e070000050f035a006c40642000c015807920b50a8460a004142c144881951019280d03040075402080719503011800c260300064a10300c00408814004e8214000c1c40f45501c5540c241c48009591030a00104801d840d104914040c12071043d10400030900c02c10001c0000f0051041c5c3c0010f07130f010030a02d417070140c07105c4452441c8100c40c00840f5a400003450850300303442c2600850080000d1000303012050050650720b1088901508100303103484102001c150b060441144031013250f002080c0418030401c044940024000765501007940c68801c00b500304682031250324400c0042c3c0da0009000440300301554403459006982600c0ca07500c80e001521940641c1808803400401044049100c60f01c21020801401940d6109034460119903080015107803041d041c540c1602246103e60002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 529899865 1250 529898615 529898627
    0x1030210081e0c030a0614090408160609080d05011d0a0504031215050f190b0c0304050d050c040b0109180c02030c0102040603050f06040b031903051204240606 70
    0x240d4030914000d900741da10049101d918698555005024034824828000300d81220780140d030240c4018441000a60782e41d482c407022500c0241d600640101e02e076400640816105c1028040d480c0341a2020f00300c1c9006a070781c3c1e5048400300001110081d2002c2001c18855500b4840c0602606069140703c9601100310145610001d00900d1003520503224000541018403400c002001c5920800c07080c003540110002004401030036014190007866000d461201034030f0003003a5409003514200e4054406c80c10711002e80700903404141a8605071000f00300000d8180c4401e8404101c29020320040c1140d1001c010800040d650074504803810010401d0080c00b18205200740740c85021448900000c410381c089609074114040c5043c51b130120352011500080031a05500041c2c41040b0180300780d00d095680e8002c200454007d01e03910364150f4003050250181810241041690711b0003801c1550a0440810103070035440e0048800715152400708450010f075045200c0074000c0c101c0c45e42c506105481c1021401050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 529901115 1250 529899865 529899889
    0x2070606080316150b100507062d09061407110c0f0906040b04110f040f09060605160609020a0311100309150b151206031b0609063a0c020303010302 65
    0xb0107503655444039007006960019a9412006d080b500c8240000107010306260041e038003d9908908103138094141c02c109502e01c14101091700f5000c2c403070000d400380743c40044c2281c24003207401c00d98030034041c130071510304252440c0714400c140e660b901c4034541e000f44582003140c1c841080780603445c4406070742459540c0b0114140e00a0081e81e0000b00c07911514001005003400315030503907110302c00046070310040d06614000c000341d40b007100d5034411140c2e031500540121a014031460b00045e0701070241c441c03071420820b80c01000c2405070f41e000c50b500354103030005048030a9550049070809035a03c6009203034203010912045080c03450900308100d04098446c0f003002d2104980045c0a00e44d00d01811159540d00030794041135a44548e20203482d00625880b105800c00140d031f03040d20134418440a994024003007400500d0801c4054042070402940c101440440d401030782048010305e00c441510308295074142400c1903d1242249090082c4107074070a81e800700c844007402102150802c00040c0f015132034403000c03260 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 529902365 1250 529901115 529901123
    0x10e0606010309060b12030c0d0809070510090f090f0e0a030801140a170c0a0f0b0d0b0a080d020c150c0c1507080a020d020c0103020304031b080f0d02070606080316 72
    0x2030a982a14002009002e1014161b40c0306600d240c14854511700040a0f01c40d102d602c008a41d49000039907000d49440508603100030300c1d6401020b0501681c104031044801c04595400d00200e40b03925850f40034198040c070f80250b070b400c0790380d0900812400203d00503040c9480660b0043c111942c084c0d20b004040020500581c0901002c2100301c81303c1c0c0c4c6500c103400000300b000b20005010210b0035501c507030300c88044010f1036108042c40f01001c1a0340e031049407002c04075509520618504406424104042c00c0c00f42c0e4003a43c03000b0310040c00126442c1c1442190150305a56000e040c40e404202e08000010f58140040b940a803c148821a00e00e580083c50b00b404107021145180490540d03c1c5009a0307200d4882c000742242400b03d406940c090700048c0d41c0202b040035400f41d40712040048011000c902003190701a000441c015140e220140a42c180d824802d40104030181c607044030a8900c0c42641d21041c00e0205440e4009070314414085da0b8424072010300912001380d49402d401403c201054060100082c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 529903615 1250 529902365 529902371
    0x20a0507030c171803120c0a0605071403040b0a201602130e030d1811120a0506010f08010e120f030c09090103060b010e0a050307170111120117010e06060103 69
    0x81070140000b03030001681d49184010790ba1303070507141d0244092601410082d01034807440000350340040303068040c0d4111900c600c0040401c06100d44032000600703405061603082c004803406030340d0078030002c6006500c1680507008145003400d0071841c24040f140d1082c61060802d81486484032841c62002c1240d040441954520351008183d000182c01c010104020040300e0b441c00c1085229054080050403055101240c10021000069180d2820082c2c5050040500b851600b0b0407801c0e140c40b0814082c03150024003240c0c80780e00d031542c1345464481d00382c01c80d0140461440e02008180342c24041c4150080090000e4640c8605011070354104d8040c0f0f000e028500c82d800300c00a902141c00740c0c00c0d5012040c1c014410000c1d56542e0414000500740344041900140d50400404810308201c09880d0407603d028004180491030319405040c0041c040314038150035502c5001c1c05840028030406019226980c03140da40440d403614a00848841c06500c1020b042d074100707015800780306800710b091030344550300382004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 529904865 1250 529903615 529903637
    0x21009031707050c12071e0506090d060912020610050a030804060f110a06050f0a0221060102010b04020310080d09080706030506040e0610031e020f040207050a0b040f020112020a050703 81
    0x2032030801c00359100d0305401178030030401c3d01017200b0b00084d00d004543d030b0403488014079607880100c2e800303030032050064035001a81000b0a0009080588000141c14060b8030300181144040d5200254804611280c00041e40810b060001031640030103220b006040c102e840903505403440e900c103101c60017148249001d000c030b0000c040420501800b50300500c8400a0184ea9440a09180c6100140000e07208810040741d1200054500c0d0014403c91b2001148407401c21554101d00c4000042418001c0c07065045548905500b0380680355030016500460a42075000c04c1c003414010302d61314021048910f141044040e0f80b081043c00e00c0403641d20300380d421034500414660307110404074002c0d00d0400d00305240c51083c4810002412000103d05080e01c1c442d60107a4841ca01d001e4000141c1c030403054010f5804a0395200300c855515085e0700408101b840742c0c041da0042412511042c1a0882c100c9041d200c1d1070881c1c1064003150fa11a00091000c202948c00f10b042038034617080100f0a002d0031100030300b0f000c070f00000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 529906115 1250 529904865 529904873
    0x31b031a0609280c03060b0c0a03080115120504050c270a02070b04031416030e010f0201060503070e0402120f2b0c1e050f01021c0e0619020903030307050304021009031707 75
    0x100c1d4024081040d5060b42e03a00c4c04c9148c3e41e5940c0390148050340059000380000c5100c115201811f000d000032035565520041c0d80804110003840050300880f21841000301c08a116240c04c80724043c0c203a0700500284072803405208017032803008018080d10380c0900c100704050020700e00d8140160404d41528248003404204135200324903208001001d85c0c00300c20703109a0341c201544859025400002a0707900546558960001c2c0d098850034041c0c1580358104000a004000008009d1035001d40001c0c0030703019408100200703030308002d1000a090b11641000c2201c8080c01480b0340507020410f50290b00d03182c1802074010040150041440061000e01c02c44008403000390701082d030108260300a0241c56024155040c074038000e5000c0d034000c1080420715800030101486a2283d40600302082010780310642e1544050360400a00229201e98190300340044411510204040d512920740b540341d03203540741014010000b42c44041d080b0300003007098401c010300014411040182599114070941502c50f080c900d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 529907365 1250 529906115 529906121
    0xf0402060f07060906090b150a081b010306090606020303010518010e192c0c090c0a110307120306050f03030316030b030c0d08030628031b031a0609280c03 68
    0x4080c5c8000c0c1006010818481c403a098980070303842c0c07844544040100b600a005d100d0301c2c80d204008081d0800750303800c0c2d082e42c686000a0185501494001202500d803602001207611a4021000507400480180100e08020b1112000d01d010561018041c0d85018201111540003c1418150199074249400c981420fa048510200c003c2d0280c00030011034a50340c1e1400602d10703900840305115810b030080c250300b02510820700032aa1400c255103044c000b42805c1d9101c078070120a0826503c4100584000b24020884111140159643c041201403809003003007030a1042c4254070388650800c00c188070061800301c0700540c0d418294140460750b0301c0107100181c1000c8030140304903000111000e99100b000304808c000d40c440c2d8012112486000b145103104a044040748400e071642c0305200790f091000c80c034151413210b0f42e0711103041c0c048011900c0781e0318064040002ca007004030305c000340800d0000610b8100403565109154a0501d2400c01e0021030003504000250020008c0556540c2c003103040f18400c0d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 529908615 1250 529907365 529907381
    0xb0d0915020c0f242a0d020315120a021915021c08101202031c030c09061103040501050d090204020313050706020c1f02010605090a06060201050f0402060f0706 70
    0xc4045488040b151611038491410901d00d514500a01401e00100048819000301c10308000070020950f980c0d000c8880d05400f50744c9001151217480d0070260b001c078855200200045904280d0258503410140400c41d43c0c4042d03069004d01c034449130540c900f030112001890740d441c90740403181c100d4492800e550380081c0c41c10070f030005802c0b00b84807410420320301d40018500f401051900c0d0a010b2a80010310110b41c40c42c000e0320b0a401c1a00c3c0340c60100080900c21140d180d03c9400182542d01d9020740307800428601c2c45005d1b0010100341c46000c1611000c0c4c00c001c0b25001020036040103049901814103c54992050303015690510801045160207918207502180005a010700115981c1c107181490040c5110401c0c4121841e1142410203d000380c4042030014400c000035140e1079400c1001a907041540d4100d20211045658071200040e0310f9807135080583c055a01100b0004082d0306221000f420f691b0000c18800240e00e2180600c00103898480c200d42c0005550201e039034981d01c1901c0e180e07018041c20 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 529909865 1250 529908615 529908653
    0x10080c06040b030c18120a0c091107020105030c12070905010e0414070507080403020604060c15020705060f0a0b0406030308240a0b070c030b07031406030c0f0f1503010e010602160b0d09 81
    0x1000001c081805c0007c0d41881103030083e800414820745c0c0d000c4217010394041050f0b07032500c80c509003c038400650260b005960000b4409000c036060201e100340440d10204100c030280c000404c078080400480d60003c1c1e6110b00100240c50600030303000c0b110710003440c51030301802d50030030440c1c0040d0700824855541309850146500a00036a40c81d5680d940080c0141c141101c103a42c0704040845180d0130142c64402c4450041d800000b826195807076400d884c2c1003d10091181e11020740360703000b84003159114403444010314400d03103d400d828102034050100e038035401c00b0048041d004042e0f0620841d658620800b0449a0710000207644500900d00326801c3e142d641e0004107510584e10a0200c1c0d290142c202c084400d02e1038a5450300c40d554001010765943c480c40725150020050102e04219060a10908410007000f4044114284026200c801264000d90041c460314400703800600034540d0601460096140100d11142d4082c02c1040d0390805104880c00304088a96445103031040240c1c0810300e0303c441042c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 529911115 1250 529909865 529909879
    0x702070302180604050610090506070201110303100801240b07240209041b08061e0a08010509010e06070f0c0c051017010e1014061210080c06040b030c18 67
    0x144000c80300310107090303c0c000d21840c10040002e59138144034030400b400c501c4a40c0c4500d442480c00c0103212595110f188281e04010300400c6218071038800b003001710300a20109020002e0746192074244d500312a1400d400d800e006131071940f1044440c0f0403c240000740c86452510980d40d600d6480e0025005041d07103e00010b0b45000009a1034030507003913029050707184003580e00b4000c40c00d12411805403c04400300f408003240c01c20000c40c40703034148000001550030a00007040e40c104207500000b9100d00c1c080c0e0007449269110327020058104420700540701144407080080c842d0342032102c80a000008609102c10400840710b1841d0144044400b00c0340040102034403070300c128200703548000c01c0004551090380242d2285000012200004015640f09981003482c21071140d060540034011700880c80d0f100c0354002003d010052012440d54615402014803400c5003a86030715001c003180c00c0401c030740410380c0700d034074280410882124810112507002c41960050f039600c05107590041c40940c2041072880d04200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 529912365 1250 529911115 529911139
    0x604151d150d0308090c0d0c060809010b040e0705011403010506120c0d050c030117060106020d14070218040c08010606080f25110115140f010504170a02090915040b0702070302 77
    0x134100341020b00491069040d03500d85860a018480741001040d001000040c22140c2008014030034032080d07400c240e02500104813044800c4c0007805840307160700707401c100f600400c10800c82980c10032221810965a048010300310362401c8000b820301d014003100d5822404003039000403001003070f200450b1265100b40d1b07810052802c0c40c0d20115101d80090003006400901c2200c9503103c09000101e140c1242c1c0d65600400c0c4800c2125000c841a001d8819030761843c400a0000100513a00c0ca10b180020700441e6252110718907183c00c0c0795030440c94079031110640c0d915102080c04600d900080e0f05602020300c400c5551a500ca00003021545100041080101107000101d0150103074450744455003c06000000e204003401000c03d20613140c040d100d000c1c0300d113642c10492506414003802140c003802c414100a810140c0d2012401c5410010f0b8140c0c1d0010b82000155804524001500035005800b0400034041c040802c0c042d000b0780d98001d00003911030303006c090000310202c0c0700700000d034040d543c00743c96042001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 529913615 1250 529912365 529912367
    0x20109170a02091806040222020c030c0d050c06040b060d0b25031802040f02090603010602011b0e130f0608010e01050105040606020c01050324040908030604151d150d03 74
    0x200940e03000700d12403201d020214030580e51040a20134030554010181c5260b0300d0390b03400c100442d2000d42c105116101c02c2c104407034000200d4806403400d601c8000240d5601c1034455011802e02d400d01440200348030b000e10156201840000c1c51603401507003c1104602c94072044009480082c1c03054009004153703100400c0150100c0c2003404440b640110703402890a0700c400e20030b82c150f92100150302c000c41080c0f0012409403415810103250042d21020040c58410541c1c0424a40d900c242c10007c003503174540085003034000e4003142001701d010b52860000b00201c1d82c080080c2907202040c203032106180e07d502218a09248660003480140075400003000450b034408001030180c9003d00c41c452085140ca4000200c442c00030441c803202d40700580d10306113191750f07820492a501000300301402c10019119503941c1503448174800c000b0841d01860b003160722880d18508001c1600c030b2a034400185490007110802c00c0c45000c3d20110401c0c030101c200086181d86124888040d000a03040c001c1e03020044840007800c0c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 529914865 1250 529913615 529913623
    0x60a0e100b0f091e01080309010531080a03080c030f0103060902041e0905100b150a030b0d0c090c0c0203100207030525031d06030112020d0c060e10091404020702010917 74
    0x32602c02c4c40101840d80e6580800c2e80c423400340f4010140416020440c005940e004141180c3d41c40340103054115040c4803500340d014588502d40c01c0200d8680c000401c5c503080c150043c20065110b80c00101507465441c101e141020b80d42c00c180310061166071951094000c56907590042844441c4408032409401c2c0800003420180c8056401074900d8001d2565012103948030707008031070302c0000161002064401101c070418180c0d10004a1804255171207281c3c105030703580e0740c0034041418000c0481d188624102095031040b1030481d1088014083c1c5181e6450068a02190304c034401017040c800182c0701d2115080c1038807148141040c090016200f05400f01c45400c1d101903551005000703507103641031030500207014400344466091941e800b81c801d100402ca100c0380f900075228094401303809408400000d03565000340c6001900f1100105440f4400e110f03050a28860712a01e8070010f207070402850f45450142c076640320b0b4075103019001340e400081290035640241c00303103030007003101c95210900c12100803041030711 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 529916115 1250 529914865 529914901
    0x6030f0d2106030237060206041e05060f0705040504020712090e010b07081b0f0a1b0308030a0c1e02060709090b030c040b0102120c060108060a0e100b0f09 68
    0x140d104403001d2407480c2058030603502602d0703000e0402c01a40c861701d0b030400c8045032007401100b5020101500d034914800340c407400380000d02080e00203007102e003058984040b01c417401000080c41855a4a00007010035000036031301d42c10602c5d0000340183c60b00d400e0411141403041d0741109030818000180035003040520009035046202940da20707441151a614200000c160038414242e04103010b00850020540440040803880c1d429076400684081b00914142480c40a040721a8103400400455083c00b0200f8507515041007003d40310182d1908650312803103140400703801c0f40c10403035464280160301409601b161420343c400c12180c2ea141046040029a41d400498013003000600c8054002000d9009029000c0151802030180c41c200200c2c4007440000c25616030000c2c114444c3c3c1d21482d081d40c0c41c43e402051503c081310080e240130360625004602e01400501440007030b0b031030b042d4007015030500440c4115003541049004079200e0f5101c0300089140700705008240c3d018803040f003884001000c45420080d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 529917365 1250 529916115 529916147
    0x13090203070f0305030d050106030608060727260c010c03080406150f140f0604030b0601200d02071203080708040c0e01060504181b2003070b0609090c0a03080306030f0d 74
    0x7ca540e0b2518400c40c180c80c11489516125400a800300d10014000e0000e41c074083c08041c184405d541c980090040c00d00030302d61010880090b060b00c0b82c800001f18100300761a4071114001011402c03080301c0000c21031190250041e08000358071021504005042d0001d080c84440ea18003010455200c402c4c2103070003c0035200f010302840040710b54542500305107a04903001200186082c0c182031568940300c0c100311005080f90b0400c40703035400b802031014402d214401300b810241c00801401d864075001924104945c1c000035a0001540360440009070b00c2224154080c01780e15002d0754580303c40c80e007419103d60603001010070700d841400105207568440e020b0f004860040c030300461500390701000d0704100c4850b1402400854100b002a442c1c4600814800031581100300000480165440016055400158088501c00703203c6044c00640e14001c600310b07400c190140040c1008201c410001015648188001000c540010001403999501480043d0078082c001e01540c0c0c240c07035403c1e802003504001c41c50303001d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 529918615 1250 529917365 529917371
    0x819030b010210090c03030c03051e0a02070801050c220b0d0b0a0b090108180c0303070602030108371518172511030f010c081513090203070f0305030d 66
    0x10881080c019004d009420900d111410380c00d5403003ca03102c54510380d040e001d0003810000180c031070048422411100700d00c0c0100c00e0302d8284191000741454055840200141c0c142000e0116014006046030200d003145220b107600001c80e907030800c00590880c2d02803000b10001103a24a540049600501c01000c02111151012503c0325907080c03030350042802c0180001c03140000940c5104904240d400105003000c129040000b91000092469214040880741b441d0040010030207600d00300401ca96803800080d9184a541400c0c400e824008a400030006006103503100050621010f12030b01e4400740c42c5250244107031048801c03d40d400f280015411211004d00714090f880ea40c002c0e40540f000d010300352000c1c0300f54143c0541c0d104915021142c003501d0410140c0c0c0c2070145507030100b00d9440f809091400201d05041d58160280a01000130a48010052580c0c4100d00d40d079900d400d0814a02c00103440012500d0840c00401d00d4560a03401000300105058008000c0c03120000251a0303030400b01401b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 529919865 1250 529918615 529918633
    0xe01060903050d08090f07081c0813122607021002130504050903040b0408071503090201050d050a0b03030409022203030207050105160510050103060b09040203030a0c0819030b0102 79
    0x11103400d091448003409580100344048259407146420315040441c2d1411210044040980c0c0e40c24000c296116444c1984546505445280c8040c980e00d8600b82c0340c10800300381d2600300d021080c2080514801020b41740e0394100506080d000e5101644c4070014044c000c145240a00c81803030745d01d50300352030800240c46007101100c00c412980c000c0f50014040c10f0000e1120528010501000c1c0402034100144c0c5c9c00280f101042000c54400500f00a1280f84018000f139490610241e904c40c5507a076280041501700300398800503036045030444814034003016001555549c2c071404c480040c00d0f03010800c0d5250000160001b0b0b4012103401411907002c1c242840d0020880001000031440480d11000b400f41c1c0104404105946c003074006031040c09401440c1c424120160b6903180d0404100340c00b0464003655440051060000c18810b400e84248c050315910143c0c10305400099890003040c2d07800b4104009282c100e000c020f034035400d4a218044003403e598112099400140240c603098401078018440e440e50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 529921115 1250 529919865 529919867
    0x4030201140114041803140f0c12130608012303210406020c040612021507080406030603030f0309030233090a110a030c060302030a020705390609061e0a08010e0106 72
    0x5032030002a4076441f041c0ca8480301c95a0a5415080150500301072070052000c04100380c402e104080d0b008004081d107668070b8591a26502401e6400d8220b00108220100140051000740c8060300144100003040000200c0440010b403520032480c5500f01c140220034400100e26085102400584900760203544000e1034a00911048403146d2140c44660302030b42c2c0c10310025040000c5400c0400d000000f01600d4102d0340e4a80017050f81c013030350045002039a141000c00905602500302901007000d45014401881c2c3e50b00c0003951403002c182c40035046206042e4560100600132031803459a40c2150302c00c06146809800103450700080d4030240c445626001141080f46040300c1441c0585c2e62080c10b4500d50750070140308030001d41009260641031942007240a0212301c08010000048000b008110441c107200b040210030246054043d1400b40d00308008104140c2e42d030302c00d4a1155005031060f0341c031101229942e801594640c16030f010a08030006500003019407083e00c66059803100941030075241d90b9110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 529922365 1250 529921115 529921151
    0x20616050f070f02012006041709090420121608030a02120904090209180c06031b1c02030f070e060a09061808030309010b0a080d0f080403020114011404 67
    0x180d140d40c1c1110070803812001035060101201418010316000396072a00910105003140d041001c42292507100808010820120749490440050b0b009142405e004002d004542c8811303002d00010100245030705400301100f490b000d0762a032100f0040c480c0d907280d65240001c0e42c84500d44940410f5100c041403001c0b80c032240000071154480442e60051555280040c00c0c000313680c0029540d19170094807403e86030f000daa0ba0140300b9004218102000d40b5190203022824034100180b916140210814003c010f040d0190080c001d217601207035040783c0d64900198405420b0031540541c4514024070102c140304102c544040080c0c451112038a610701c03071001c84010000c460081b0002400040c8404134248403d41c4607641c10b0000d800c50004d25114540c0b10255941540c2081341d804131541c0d518090900d0a20304100c0c1000140030786000750a5841e001000145484224040481809810800b050816100354051900011416060420395844250140e85422480e040511550900a110206030380310b034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 529923615 1250 529922365 529922377
    0x312031321020d110f1b1305040503030c07050109060612020102060106020114010b0a0e0a060509040605090405060f180111091002030a082215090b090a080313060605060a02061605 79
    0x24008150940075840d045a01d802c0074134070711203103020701e07004400410340030451940ba8211410807100d100b1205014040c00410040100c0001c505001c14440401d50100440e0340086c0c901d2820780e9118014140603000d4410300c40c00920300c07032030300000040407078680600d011031034400d03801d885059036115802c9080e00e21950005440c2060800104505e8550700006c1090b02018100002600c600c10005600421039903c043e001c100001035a1000d40b815108040c0038200807030f5891440d00b801d0b21a02d684000040a0b0501c2d20041d102003003007140d0103003d5001c107400420091044c01110064100c8980041480c2c82c0500a45407070306440d58004415152135849503030310414a81d81d40c5240c0c1100c0b410184040c0300d401702e80d01a020100b0f101d02045d80f0794078000304022501e10110300c0d0900c0a90001882c0c010350b5000840c41c0350000300d803101100d0b041110b841201d5280c40c52800c150008010540c0481e900c858009003684045801242461046580c203800324841c20121800f03440c00d2180b5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 529924865 1250 529923615 529923617
    0xc13240e070801240c030e0306090f0c18060d0c03020a030302010606180e04020d022202190203042303030405040207030201050402010e0f01020d210e1605010c020f0f0312031321 78
    0x141110303d44e0f551160400681c254040d180c03481e10b01c003a86000c05c1c102402a9600d40782c54009032512820b03042e04012000001905960514000652030800c0c0304181000e0080f80c481c58500b485070041c84140074118000d190000c0280c03c126a492402a0003044180b14440101ba9401a440d0741c0180310102c0f070049410308121070460f17660350741c02c1108036008954100d0b40048100c00b9010781c0d005013000e41d240c855001400591300c003001d5000e0b100000402042c0011903000304403d00c40002c5e44095900300420203440060b0800545001a0944c01039400a43d041880894907106240d815042103000390b001380ca0380c0c2c4008900005000395007070302d9042507025034040c0d41c06404440c840e010040e107064400d860b1604c2001010064400d58540c0809501d6a60214450380c1d000e4003580f440c20020b190908007000070300500d5000c82c240400d0403002c1ca210b002d2081100c0c3c2316840c188101510b80b98144c3c0742070385c2c07803400e006d03589820014100161131440291240840c1580c1c050b000101039405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 529926115 1250 529924865 529924919
    0xe0c040302060d0b130501090917070c051e0405040807061404020a0b090a0305010908130b0316030b040209090414011109030a0f03020a1a0114030c13240e070801 71
    0x5004030f00000e40400e812682d0031202602c0d605101d007141d407017010b000e46007103000818600d0403418010526000d0710208185040100a030b9000a00c0000150003113a500341c5800804c1c100c1c860b0034000d1845036162460b042800e000c200010490000000e100c01d40c41000200001c0c99980c03a00601890100c1c0c001f03410007000b10b001d2103410003485c043c1c445800001c0000190721b8481c0da41c40d0a40d400814112100c00f80458881c040500104220300948094440c8a0452602411481c00d4a14048405091568540d08200e0649031601201c0010300050021280350519280040103c110180581e0307080d440c00400d0201b03904108201c69078400002c0080024040c3d80c0c039444a4840510002c9096110340e43d0041d0004003450f110710003200d41500810160740c54440810020f6544402d45442a004140340692a82c1c0306654850380d4004402c0c00240001003001400c1842e0000d00401c030b0203e50b03000e002130003036151240203125902c6a5210b50b0341da681d490920610b10a20914200d803a0f103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 529927365 1250 529926115 529926127
    0x3061003140402090c040f08030c1203090606060a050f0a0e030d0201090209010b0d06030c0612140105010503270f25030323160503030702071710052a040e0c04030206 73
    0x6802013042d500410901c0782c8071b00d416501c004412036100183d101e4502c580001c030b4034140c2400140920600610003010b15455460000c0c10661100c6c40108010320030080031a40c0004d4602c65001d81324421040f070100c1e03a550384008009000f2489045400c0c1c401d01c035003076540c000c262040c090007480c5d07540604000050b908102c0300c030700d00d0f0b0000700c0c0d4413404a558400020200b69a1840e14000b0007031600c44d600a1040d01d000107042c0c034011900c0c01d580c0905000100200c1e6844001c0325802030082016440702420341000c2d2100c440306001080080c45a1107010902c400c000c1001105501407400004040801d0034107810400c80a00c4081d010034512500071400c6030b010011409c0c002660741d4003a2400340b07500f00101d2601544e00cc10380e6294400b004101100d40c0402003507000d001c100d800c00e00b4204080c8102d82c0e40b020740b0008a030900d41c699001c074001e20411811345514540a04c0701c5143c903062400c0b00c2c421500507204001c0c1e0016108081076400e80010700302c4081e2600030780002e203041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 529928615 1250 529927365 529927369
    0x30d0f1b181a0f2116080105100f0807200c0a08010510150c081209010b1f0509030c0904060e0d0509150c0c04090b06030c1512130f030503061003140402 67
    0x1d00080040ca0101d0f0140b04844080b03a0136085251141c20f83c80e40d00e801a41c840f8000402003601608079902400c04018000061030b000781c443c90a81c1c10524040740035980c0ca40b02194207000c4105450400c1d4681000c481c800d541c0410640151102070303601d509020b039650030450072381d40240d81c0840c04500d030b08000c3c0600c0708000c41502d1902014100540a5442642c0d4480d11b548110040002c4040d80c0044c048a45020300440641d1031040310350001091070b82c0e24450032040030305840c0084c03050000d2a40240d4806212400b80c45800a00c0316000386003501342800540b005079102c4410717000b0307061111103581c007900540b50200700c082c0505022000c030f140c81c40c15030380c0008024941c62180084401007036690f4011003180a114102400041c01c01c6014145800c00031454035218054180301d1203191a0201c080d2540340000b00d20100c0e883e201c5810729050407401442c09000038004600742801d142c1c001c0021070041505807482c100d0805180c004508031402064015161072181c40814054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 529929865 1250 529928615 529928617
    0x12060123090705090d05100903030c0c0309091508030c0f07051503040b0c2206020705010203120609041e1a06150318030903100626030d0f1b181a0f 65
    0x4e03a40500384c1c1d1512052a19118500f40709810580350312504e5213039407005c156060068068605460501d500408403d82d80a450440340e0f000301c040300c07a903407401444080310b2026203500500005080d01d0b9540d0060300c100e0344a52040b03510000034481d40b4000a010b042541c0c1003c1b1400001907654219210355a92064107507001d007100d0416402881800071403d0f210309040700140105412003031081c9458000703410494980d000321b05541040c040c0031081d0080c28541030b8441c60031100c10710300740d44a207440c4001800c60b400d012290701240c1c1419003000030440740d00e907198030701540f00a03442d5155401c1122a40da12880d558034410f0510201e0901c50400301c1c2403456000340c2c015a410801d000b0080380c84c05002940c0b00000549407801040008420800300c0303513062000304000b40c9002d00c540019900d21604071240d451950b20032031301107610700541c0110101020540f8080005542c4134000300000242d28001980240414002a018010030255031a0110072150242444040130000179a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 529931115 1250 529929865 529929877
    0xd05030109020a201f0e120f07050a0c030c0f0b0a0807021f061d0103020120010b150a1205040c09090201051201030b070f090501120c050912060123090705 68
    0x24860b60080f590040c0340d94082550690b000800200070304e94914181c0400790102c02c0c040c01e521803604241606d82c3ca000f0840307205800d0003825866580360200100e2030399100d000c00c058030700d0103111155420084400c20203000c0341d003e0040c2200c00c40d207a0b051100d8038111440341e410340400400403080040e01981c0c0803580507a080c0140e0740c0301c610740c40356503642d0000b244403440f40c10307030720342080c45420000034460303e10741d1001031000010341c19980082d024000f2401201481c45540100f182d051009402003001042c0140185d482c0035120342210700c0e1504040700c04808240340f2052650300300b00601c5010710490b04614446422440c1c646220000c21070540c0503410410108850304558074248080d5008502c540d140c00c07200c0c41c0040b4001c0114045005085c2004203040c01040700d80c0c1e0103c1c5c0b0314404060f61100041c0e2654a5400759203510880d500690400c02c0c0700f015203843d04021494504071111400d0513581d501c0351485601e0b041440803d03c40e4840f40d0315001c41da280d4030640c003404c0c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 529932365 1250 529931115 529931117
    0x1209062c011407020a060302090a0f0305030702190915030b0f041a09151602010b090f0406110409140106030b0402130311010e09090c1c0803060111031b0a140d05030109020a 76
    0x880c1890356004114080446c0c1c001c1e0000c070780c0018200741ca84c203005a5410040003100150070b1514113550701c0c02d8481c401d50704040e12401505079101c1c0c03041d242549850003412a039070101b081281c42d01c4241c540c00c0151000381d0340021500c0c001000c480c20b142d051440b541e441aa0300401240c1c803003c40c0c44501020705065994880d6032445140c419011001c18016a002d4080c0482040c01070b00003070030b40307800450140c0503840c4101444910041c0d00007060b00140e000e0404074520041012154040c020340e0b0241c00d01170700740013400600c1e00102c00c100741600d07074984c0d05000000b128401d11007688100b000521012540e0794003040850084400040426414500303007500b18400e90000c0c2c4020f0080d140b0070340710f400108181c507a0b80740800a07039100f0350741f4240d20900d0b42481e4a500209000040c1614180f0580708106501d181050040f9208800389048220b00e0001541030142c0e40d03080c0d00401c40300006072050040c0c5c111070000d80d80b034072030b141965aa0f00c1d507801c020984001e034006030703042c030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 529933615 1250 529932365 529932367
    0x70e1b03160f020c0d031d010c08030a05130b0c0d0b010201020f070f1502130e09010b0942040b0301111905040e0c0705011a010f05070f1209062c0114 66
    0xd1550350b640c3c1c440000715402551002250103c0b002c2c112071f41c074403000310303981480b01c012524000200f46005407940640d600c900000c582e40c3c2d01d076a40f43e512000a1000300543c50100802ca042881c2001505d41000450001c224814000c001a4200c2c031880840751000a801e01070f100001d0318000c050489144030360040c0181032114110501683c10002c94403080c55041f0030309100b000d407001d00e1160b101404a00a00c401d02c00f20300454801e4500ad482580c426810b000a119004000d401c1400d0400130001c91071200e00c407002d80078034440300e1401e10700c3c8035904090501e00646014000e002e0511502d50820b403400c0315140c016079042d107182c0200c000340f11083c000015905480701150707110300b00f00da00f505e41c0c0c1c001d2450100d085800301020f0362400c154620500d15030b40d900c04400d00e509900781c24003c1e980c0c4042c0c180b408070000c0064000b401c4084052180001c0c0354030181c4041162119100d8641c40e01c3c55a254540c00c0794003240c2c2003007140c202d030501c0b0f50941c428811518129110001c207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 529934865 1250 529933615 529933633
    0xe0922061407090602061302060706021b0d03020306011107080318010207090222060305100e0a0e0708150112030206060d020409140105070905120c09100503070e1b03160f02 76
    0x90780003030508550300d0b0301103510644100500d90301072000d030b5070020b030100d10200f50071030650014045015000300a4986076000c241c012500782a2400803000010000850f075490b06580402006507000705e40141c005006110180038480c00050074406450304e42c00950b081c41150043c1e00c010501e42068241144511000060910500d10007052080c4810140140e4070081c060740b050070050551109041502e04030400502d448400b0700441a41c901c0180c0010540b9410a00006080046042d81d443d01606400080e10b0b1000107422a0310442c19232400402daa071000074a24001e800d48001e405600800300054141c03400200700280c4e01c1c8014400a1140d000c0d44441c281740e2807401c1414101d039914000d2051417508000d440005290444d02040344068a2031a5a111519500d1760350048070907101007000c2c9008503000e400948809070441e4141071b650f940718034444105071801d2800d21402008036841d0003009003242d200d05071080d050009560f0203901100e00280c141c4450381180103000715 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 529936115 1250 529934865 529934891
    0x1b0f12020a0311040f0e07050304031b1104020f04300b0402010512040302030c0115140f040e010c050301031a04021c140f100f02040609230310020a0e092206 69
    0x240c8098184000c0d450455810051400310707400b006081f001c03c1c0f2034103104100010391f1040704482c4c00707a51600c0e080b803000001d142c1181c800c1e420070003c1e035215001003aa40980c130561005081141d0840c0d0310402072621401c00c00800725610280c10b100301c1e9200f02d81d207000c251100080c0d6040ce2061401a161a15a0101007940c0009803412001070b04000b60741c00d14000b007402244c120700519404c10150b14901490f003504601074803202809814a00881d44060303513540c1c48028401480e800a00c403e228515006103035900c01d0008895005040c00c2100b602c00c0c11034045441590b001d05a0140f2003041c00819440301140360b070844101d0342c4080780900e06402804a0b8000c05102c030000c01c5102481c424503810f5800808404051070320502040015940c030484186c100c982c51f10310300710280710300300104d424a69001c617101d40510030581e80c0034a00f4025402090b40c0c50695603400c18504445040001000e400d5901c12902410104124003440c5154030401c0281e1080e1000903201804140f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 529937365 1250 529936115 529936117
    0xe0618030109120216050a090c0c020402070b101202060f0309031b06011805091c020a0803011e0503060f1801090f0f02010212030f190e010f1b0f12020a0311 69
    0x1203c40340d50a90300707030f141d95404000344407540101001d4000e400f81010041100310740f0358419250041d0300e031002040301a0040314107240c02078001d401556600c00500700900104002c3d00d2041600310025400540000020100100079174014141031408144205100d100d80015040710030b64002008620001c500312910451b1302c1003041c024107002d45c03421046c07000d60b074106488011194204030401004540120313060b500704903090350421804d41010703012407424074203840c000c185c5034001001158000c06442480d8070180c0c40e880400240d5114014107880b04001e854030a0000081c0011400c003201d540c0b0160b4403040d0800002072044010b460340301c02e9001070702c42502da1846104000303066503810302042c032040e044c08100c2032030350511080800b180040142841c01c804402905201d80260940100b5801511403000b4041001d0385241d4400510040812280382c000d000c1481e1002070044440204100d01601c0d29903580907036040c014060750000e13240c0b004042d55203401140d280c04c204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 529938615 1250 529937365 529937381
    0xb0d1e17210c2b0e010b0d0615050603010f140103020702131d0a03030209030f01050108123603100c0f050f0c150703050a05041110020120280e06180301 67
    0x15260f451480400002404507101c842201010384d04290024100391076078a0001c11f0786074003040000303503a0f0101207105a20210743d001580d0040001000142840b483d005caa4181c589103913000d5607900d078250046d8100d1240440094200e80e2400000e402105c0551210910103002946031883c813001c04a840e08201c10500f00f2008250b0114036513050781020884540c89070440c070000c04c43ca5040c142d483e683c40c85009507508c1c4014001030039071244c134244000ca020344d001c45807110f030200c01402c40c500868180807501c580284200900b21000740d5081c01000c64101940d1540ca1403102010f90446040d031200031404207840b010407000d48220340170015a42000f01c0c511a91800d400c0c40440101034a5000e40003440c4107042c1030500c030106103009035045050070100c407035424134400c0c0002a4090195610b0402c03240c101256102c04194040c2c00403c0da40c8001806e51004d03007a100ca852040c50703501001d40c4005544008190150b040540090040440031034508500d00c1a0200203401e540c920 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 529939865 1250 529938615 529938667
    0x9041b0807150206060a0f030b04050115090504022707050a0314070c0b0c070302101d060408030610020712021507080f0d060902120a0b0d1e17210c 65
    0x2040c044002d241d418890700b50090001c442c82500245083c09003498158580030280002024501180070094250700c00c00701c4640713002c41d032418669265a10002080c5c116400d9015032035022401510340b013402d0000303452801a00e403030f83c41511544803c44007500950480f0060540c1c52003124030b14070b2a44091407080041d03545005042201d890301004403e406007440c0d210950038440c007000030307030045140040a41c14100c000792500b80002c1440e407840c4c0c2600b02560702c0c0201410300c401d1040c00002548114070a55941d070b20005046e00490b61074002d841008150402d0221420051404020a94000d1803c1034414240364564503461056400b048402e070b404000024494414011402108003e2580740300450820b014180030a8046130010010500305a5641117410340ea510459541c007481d4012124410500311606e024500c0c000150003034074060003001c646000e0010043c01c40f012000700880606121455141d0005400d0b006400140a224180017a862890070340540d440c4050007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 529941115 1250 529939865 529939889
    0xb09070809100905010f0b060c0a081614010608190b1b0417100b0d0302030a03050402030106090207050109020f15190e04020307120b06090a050f0f04053309041b0807 73
    0x20b51b1011107610904071805040306001607a400712000c1410004d140c0c003c1c580c40d648400040c1009135040ca4601e000f00b01151045105031084e0301580800c0540e0220000c5812820301c0011b80d40c000b03010848024081d03051140080c0da0f03142e0701981e2a40c000c5900e1001c2e41415151150803c0400c02c04001c882150b00160b100d031070b524045d000c2d2940d104016a01c03c017006800f620025201d200c0c0c103021005042d2280003040854500b58000001005001c43c11911043c06142440c06882c002d84280d2060761605181015441c0c00711110207040404001146000e600100c20000088100d07481f90510410032000317041c548682c00110b1050761999a80342d402482c140c401d8089515007070a45020383d20903c4084855190291120180c1d80216520381f0611803a10000e0756601c20040515001800d100c203100711140d0342403040c100e00d1905002084406038000c02d417140300c3c18844082c0d510200c0c00001c903000c40c0304945410040350941105045140d00c230003965107030010b158001302c1d4a003c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 529942365 1250 529941115 529941131
    0x70b1e09060d020705060f0c03100b0a0908011e0e15010501120f0501030b180d0518060d14040b07081510020a2a0b04050604030803191b0807030b0907080910090501 72
    0x42c5455126500008c020060781c154101070001c948580c07114005c88480030800504031112a000f0001c2c40c000313100b940c0007880328440c62061010301d130318000c155100031410111403040c0c0c620013003000c54464900404505150b03107017000450746042d6410b0060525a42c0d0003200109490a0140a001e940103401b80111800c1c43d803002e0010250f4041120b2503a00005008801180d11408030340031000004c402400c001e0074003001a03030b81d21918140030380091034100c204100ba880c3d0000720303100c1d5008003900401652464000c3d50200c504a0b0f810000c0d80d01d15610f00c000349025126a80c07256243d104495446401ba43c800d078800d030065461880e10129101c1d00701c19003d060102201400c04000c090b42010300d06400703e1010b00850000a040000203c001030906440c0c4081c072409d600c801009200e034400c4605268191040e10003131500048100000440443c060f000e050b4070310001510340d80f581c0d519108110340c1c280001d040c44e07105001d105440c061050141c05081079280c051400003d100e2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 529943615 1250 529942365 529942381
    0x1b0f03091401081b1e1303060b09090307060225150506010c030c0b090c0a030309060306060305011805070201110a030b03150103020918121605070b1e09060d02070506 73
    0x34407035414680c10003690000704907011034401c8248250301c514194594a41c00501210030907100030203410740200c0d40214031902040750415521044074000c01040010811800a103c80e0600403103100c0f40c84c2e031041002c1030014206500a010003040070b0b0740c10b0349440020f601c58010000e6040c0a0310341a00000075140f020300d940c41216000340013400d19002c80e0206580c090000f44000d14054405844c0c80c2c00141c0640050100080725040104420655034980c034000c0d00c190030f82d024880c0020310341003010624902922941d4140c600890b8848203107181c404803400500320061011085540300c0c4143d003807031484039010386807840c01a1130224401c80400180340c41c04016582d07513890000107400410260b02c40d079598540120102502c565100700c0071105070310b0b042e101c64810564040c0001c0e50440310001da00c807450518400c005441c4400d94038100c0050314055040d1003408032082d1081240407085aa0080020700c0d809088e090404100a28810498124400640d09034000c1000c1083d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 529944865 1250 529943615 529943639
    0x206030108061915050d0f0203190b090105010e0c16080d061d0408030606070f02062b061820040e010e1f06140706060b0a02010b060909071b0f0309 65
    0x5940502d0b0200004440003401041000c850700c5000d02811b84e0b250b9820178803001240075046030750040c084075400c2410100c080c42e603483c9190141d0392000202d0103d0044941801160f0481e210714040d00c02a03150030000740c5156112540c45d00b1320354903142c0400000381010016004a40e550040003502d58500301e9a04d21180c03120a45003800b909a600f00000907940e17106507508035100347e43c26500d0f07a070340386060071400101e0100039500500201c6c4a150060070300c01c0f5480d6620205650b048441c08182d5004184c460758003a840c02800111452001c0001e240e00504c0a1090040c140c0b000c5525500710b4010350384950008017840005d613006100d01103034003d01c02c1d00081710b00e80441100c56160049003100c2c02034001e010402c10180c05801d070303000800c410b0712a801d800a0040258541c0d0742401102584810380d444095401c0080402051800c0c40980c0d601303c601414100d02903031010001c44030205100e02c69070100400e81703580c40104c2c13014841000c03103070710949030711001030704044600b401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 529946115 1250 529944865 529944901
    0xe010503100908070305031902190906020f0606091e130501180809061806120f0105100206011a1c0b010215010b0712050c030a090302131b110a020603010806 69
    0x1007402c0c810060001400d07881250a03403500751500700d40f207459007055003011202c00714194002d00e00100e4002000040c0c00c2d54100300c240700e43c5401c0e070391a81d02c040980e00d40325409160041500aa0001411801c0c4120b2036584011106928402c1c50017030f0305020070507441500c11002d050146050740d41000424890b1038000c004040c0d030098260801d603140c000f03030310030030b0f648034081c00000c44c005c0550030301e07080646180c500c01401140c40304e50303078000c09140c10412602c000c0c2c4c1e400701d4070000805040000d13036a424802c09034060a126820501c00e1280d0040820b0081c2e0719403810410020800c545441d5a0591104000080b8548001c40002890020030f8101028003105050042100007848000c440c1883e034842c800c180c0b112805c410580325409051080070160000040c0340514a90040400e42500d00c222070a070401143c4070b1000007100e003a0a106103140c3e080c5942030b035010340900300000315080400119000e03e001a80810403913013080e8030a4880344e0110090102c3c0e24190072110070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 529947365 1250 529946115 529946143
    0x5011d24090a0f0503160b04050c04020f0924071a0f012301030603080315150703020a140a0f12120902030d0309060b06070308061c0f02090703150e010503 68
    0x21401c098500c2900d4114840d401409004a000024100241401a10300850358076041d103000d0021420442440314080307404072814002c503c981080c61601d4400c0c0c079441e0604180c3c0608000b000014800301c011010403000c5015400100301010040007001810124802c0d0301000c0c0c80d04074000e05507401c49010701001c030030309081d070300500219000313401c01031002c3ea1004100700b0208620b40181e0003800d20f500007070030300a1300004201d4084400203c600032140169801d80181201c0d03082d03044c90340540b0200500580090b0f03100000324100c924440c0c280c46080c800d0707500c204016a51400024400801200c11511900780414540c0d044910201007010701c00081c00a918182e00090710307410080d00160a140c1d4804d9660305200c41c503400700c072040c5006002c80c0d644491754100134000c00b00466865110f90240d100540381008464508800d103603116214040580719a8200139011a00409560030036030780300a1240d044074070340b04001c000e240d41004d4002c294140024542400394001c0840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 529948615 1250 529947365 529947433
    0x801022104030206040f111e010f0309080f03191a0901061b0b0a09050a05100b060c060a0c170f0114010c03200c06040906050406050915010c05011d 65
    0x100210f80c02084840d0702680c0580c50a0742c6100606e040b101d240d440e8021640c002c020b84c1000c0c4110038580304040c0002909886410006100d03800440c00c2d503040007801085004140f040241d55205040510303000780c1c2410780c802c40300500811840880d1084d0310490340101a0b05031221842c2001c070500e0340540110710f0304100314000e64900600601d6505c0c40184003040d00ca0004021100c194814581c0d5a031001c10b444800425080c0950703101941c0b241e84003c2d92420f450100c00d45020070880d8800c44003080075180b00d03600c1c0c1ca172010050020f10041c100b03004541142191250112500a10582c025244184254104402240581cbe01c606100e81032021024601010903041038250b542d040054200903015029101c405003450107a281d0701e07410141c0800d02068401c101d42002d026100b0507601040b5040c0d41304200034100005a4801041008140300070126511581009201500400012400001e9203401c080404104900586c440e0442d03d4401e5100031424031414044c66220300c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 529949865 1250 529948615 529948621
    0x10b1503152e020120030901050f04020d1e0c0306021308060705070b1807170f0c0f04180b070f0e0301150e1305120a020d1d01031e050108010221 64
    0x4180240c01c00002c00c85a840c2d621480d100c058800d401400500400603903505032429003503807402d003540096440036003a5081c080054502c0000d265018850394004100395030103040c0b0784400d043e1418590041800005441ca080045801d40040c20011803007000016610304c2c425205000c01d102541194540b0380050003804107245e40041644c480940001c40300c08213444840c0c403005105c0c26200e40703a07071078081d518000403c400c03904203080489815074181ca014940d407d00068448500203202340d4440304082c50070105040070b51045d03280b99030069034aa5034400644507030010000032580080041c0031090020496a4003080f02d00c0440303404d50090200040c400010801010a030040024408500000500844266205064182e0454190381180341200300c117103010360290040c04054404d2a09a603280c2d442845d0315920700b4002919800804100001140503000302520ba450740d1808151a1a520f421f40c41054028803840c000180d95201d60070300c00705880410100c46a681003e8410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 529951115 1250 529949865 529949899
    0x15060b0d1b1e0c05010e01020a08070206060307032003160f05090f04140a0c060e1807080c0c07080303010f030c080307050303070302030601030216030f080114030c06070203010b150315 81
    0x305442003074400c849280c2e01c40c0b901803c641121503807101804030360030514501c0014a042d030040141c080c081e80c1d0440517641d1020140d9642d0303004c1c1e5609805622114041002c94404050804c03d819a5002207005420b0500040e1070020382d03400700549840d00c07400402007000c00241798030050105035a555098504203000c08101e800013800500384646010340142c001c0402d200890395603510409020b002e580b1001c004180c90580400c003401010b0904200b8803122600070228441d140503650b160860380d84a42581e2180c015142203551840348140100d811003062000d18080c04211800c600c1c103a00c0c504100f5a2580d207580061204d40040000b4004100c000c4200e81c0d211841c2d0402699a0300c1d4840101c00a10942d04442c501e903586501080406da888035035050b11110a43e80c0c042c0a0362140c0d0300c180f01e48441310000750300d540001c0d0350024604054028041e0f040c00103000254032125480414030541900000a00504000041040c585452101505000e50542d0603485442032020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 529952365 1250 529951115 529951127
    0x8070207120b060609060403050a12110c1e030a03030f1503020904080a0c0b0a0f0510050315060604092406050a050f03041401180309090b060f0715060b0d1b 69
    0x20b02501e0803540011101e0f1910000c595030210301500701c3c1d0342c55541e0b040c030544490202800310769000d5072400807512288960606210501d00d44040c11155040004201d400c5010040410000c581104100d001d603400780700c1e201c0010b00a85021511007103440c0340030200c400b191a10414156490f0003400545c80703000815601075800b1403100d5541da40b407942581c20000405004018030180c3c2d0400400d40b929400c07108060742204403d11068403281e090010282980c0921a0154040341050001f00c2e100c0410b2504098082c02407458241c0300d200c544266051550841002080203c07201030706444081600c00914403454290300f000402a401441441014160f21030854040701060501040408101d8902c007100003c2000b02d00c0c010301103881a5402d90182c001c12503051000400a0440c02050701c2c0300401080541742031180003541b0801c0d0003600003910707050100c1c07000d4000d20109100b04c9016003494036602d911800000b0480702540c980f00c10f002c4202450b840c80070758031a0819 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 529953615 1250 529952365 529952399
    0xe01090b0f2d1303021e10050f090a030f0c080604030f080402060910030605040e0609100e0304150801050907051204020f030102070813030507120b0a05060103110a020d08070207 78
    0xc00c0d080b003a41e0408401501078000c422611140b01d0000b4048a40c1c105104488040702c1c403d40300621080e11520402880c02480300005400c2008402c41c4045a0310810003450074040400c030712414206014081a41a4665001102c0c80000840c60200344117042da081c000400e4030700001c00c528503141c0d2f0000c050105400c944424081d80401040031580d40000380c4212040190001c481c1e200c8600009000e41a5882124000c502c1e15212503034801000c615113200780c16045c0280030082102213084000d210541c04410140030600c4049030122540509031888269607603484003950500d81000010303e8040c00032400c1c05000c01c00840908034000e00036500540440714280307164044000f080c0681705182c4002d104150018040324020800081030307040da80600211a085a2100f5803664840c121490142100b0389020005035081c0d055008036600c800b0600d408520a800980503800d13a401480c00362001d600840500f6440b0f541c491340007a44002c1e00d2004007001380c80c00b180c1c0d00b0351510320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 529954865 1250 529953615 529953637
    0xb03070c030f050403020d060615051215010e0310020406080a090302060414030d0f0e0d080603030d020d09020607030e191a250c09060504020a050904020a0e100e01090b0f 75
    0xa0b00580381e280240280e800a54010784110608040d628054000744020302450031703021203240c94480b8952265054440344a0280380080c8140c4480008a004002070399407103040110100581840d03032410310510f03003040c1d1506070151f2603500703141c0007a04110004150480c22450320a4000200354009a40b54005400001c07418001710b4180c401411f41c440d8403031140300c40d41441c4204240d21f0740d0358482039120341c050060f912400d101c40c40c11110301106440003649580140603103001c699442c0c1c0141150403261a00040500b030750b6003c52869004060180c0105043d2411020203040c40c4140403254500080e4040c3c0043c10012038420f0300443c044450420140403559561203010b44802d40d6040503d00d4a07442c4910040c81d0103480c0150718000c04004500b00100007032181068000e031040000c0b16142c00d8140701c50030040c40020741100c440182046929804049641c44070100d04c11000c880380e9138a41c110484000240c21140d55600074041d0081c1004034540c40c0070914150348a500350 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 529956115 1250 529954865 529954877
    0x305010506300a0c0f0302030610081c0318080d1a1e0307032a06090501050414031c08060f060301031a040f050d0c0c080a03020c0411130b0a02070b03070c03 69
    0x280002540380100220f80248a120b400301e02103146448241600122803003242214800e540e0702d42c011003146d2180c0b184c84080d605c03842e00503a0020b0544070282e058017040c5070006d21130306298040c0740095000e20081c1c5050b0303000100c4441d1a003546c0205c02a40b440540400d0100400f04007080041c1401c111500d014a66070303809002580c2c091094200035038001e50f4040f0511481030010034000340008291811001c3c00e071001400d0750144200c5011541d058440c242454a0409840d64002d0444443c6526028500c00104880d04004054580d0b403020340e51840e82d07281c4201805007000104100344e114080600041000030308100003072180800c1683c102d24107440b5845e101d081442440703001050b600400c0503407a0206e03030004d0174101685c05034064800c11a80c411700340e51030714044800500180c11160b04203a00f07091a8000302c504000d110f00d8145880c0a80900d02c41040954102e0665004001401c0c1c001c01da042045202520740380305c3c418a1410840c1001c0c024941c0c602c402014484 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 529957365 1250 529956115 529956199
    0x70b061c0201020c151317010507020f150402060f0a0c1101020c0f0409050307020622050d0b0a4701170a0510030f0605070f050f1206040906150305010506 68
    0x9144001d840069003c180c0d0411b0443c1c60b04061068606480d109046d17542c40c5ca000609024400100d00c031203492103c0103000000e00d0500024076210000307005980042007040b40c1d860700003292008219400d1940e035001f43c1c011a51800c2e8004501103140c0d0350455024550f490400d40d510700e410349000008440c0050095140d103010703402c5d8016050040d501c9100801c0b5085c1110441c01c00358000038049141d00c22a507214000c0058580c0c5400024011903500c60009480820300d41c032544820f94950f903502c0110001d1a117130f50295510035401c0c0c03945420001030f0345465a4555a5141c101c0003401c01e40f02442c181e110b2010b803c1402440c02d01d150780c075000418041b426104014000d141c001d081c035001100c41e814071401414060701c0080010b00d40e501c82e0070420b4400d0040e20099141407424602e00307104880c03c5c2280d680c0103001b213540960748030900d5000980500c90503000310602018806c000d499820080e00316040206500d015468180d0f2000389240040d10301c400409031400d241c2d1b0212 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 529958615 1250 529957365 529957399
    0x9070909140d020d080906040b1504060e15040f020c030f070602040b030708041e08090f15030a090302070605040506191b05030c0d020c060d050402060f070b061c0201020c 75
    0x1032405070004540600708118101d1036004c50340004890840e104e01d050780d01c41d6290507960307010448029000c200a2400328008446000300b45401013001003008c280780d500c45020314030b2040240c400344c2103003100070342c402d88a0074240205124031480e140b00b1801d200c003c003001522881000c5040480540000c1d40004100195041d40e01400d00403d80c65201d113401c1d10007400820302582c054a40303030b0a1160070311100c1c4041c04925180c0e40d0040c1c034641403103030300028000b6642c42c24207115844649041c0520b4412002c1c40a07622440c01c1c41004a540a032038180681400110f030800c0f030800c1810001403215444500440e100000500c0d00f00c8481448810100c4050740408519494840b03158091805e00c00000040d009c0074001000751000078034003442c207076038070b0184054203604400c0903c9070941112a907449a40d006001030f040d245030040d000c0401071180d2121900311486c1c84550103200c5e03075040154442c5011103e00140e0110615180c0002c4d554030120303107840e44070f05a0076203c4c0f1804 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 529959865 1250 529958615 529958633
    0x150411091b03010b03250906030b220c0f0807080412030b03100605090133170705040806010b03060d0b180102070503030a0507052104030e0913030e0909070909 70
    0x1d6405000c680c807961a00400c0c54180e0090301c00d1190180304854400c1603e10030444040d945241da113515110740d1420f041a0301070001c10070280e91010001d0700300c85034080c0c117201000c6000003602000078040c024240180140d400060900100300c0104100100d10303400015190304030390042c480c50014400404100c016201019005416001340f449082280d0159000344080d2181181c01500300c0ea00c0707160368108280700311010036000c1c0404d03040d815405120310440380c009049180400b6012070f080111070180c0d40a56108002850000d01048454410311401c0e024141c2d11820034a5400d10100144012217840409882c114078140030482040c1036041c296511076005000b55110060b500705503803650421500051450300b0000060a0184160100c401c2419140c0d40e01c0500c0c4400c00d480240190020012070500c428190400b0141c3d40711468a8030400101d45010002c10003850000c2c06254aa150140524158410711110942c00f14162042e01d0000500046070000b5007001080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 529961115 1250 529959865 529959901
    0x10c081308130e1b090109090e011401030804080f0309100509030106080f0a030e030706021e01090204020f04050f0306101202150a0302190c050c1507120201050915041109 75
    0x40b41503494000500320a400034410311403407581c41201c01c40c0c1c40600e1154500c3c07180d81c01e41e90010364030300700a100844281d4481c600c489002400000c840c2400d400c1201020404c0c4c0042d030f211600828200200c0c00308211203071042030004061820002c1e12000300b56030b4900344460f00207100740461080c00c41e8509600a00080c0b61103030443e900c56407507451194031840510415000210351100b032080d681000503402044410369402413204007508a80c0c3c4074207888240e540344055407602d000c8400b680d03d500180042035501941199038500c0d000402240c0c0480c90f05090280e00503078104109600b01c1c903142400c40d0f05041e142e1904050610008441141c081000c08207c903020030440400755059016001400110641c51041151180c1c10303160003801040051140d0700c42e8020035041d00300151400d02403e070b400380f000c1c204021550382c00d0340e809181c8038000050395a4000c0200c0844200074055040c1030300015014142416151195a21450b2207440d00a240e07070030110b401c0e00314044900b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 529962365 1250 529961115 529961137
    0x20c0d080d0504150605040905060720060115030f09030824040e060f0106090b2703011b0207060903020d02040e1f150902040e06010e0a05040c020a060509010c081308 73
    0x5107140c54903000c06084011388006092038a803420210f0b007814a0301c90703203208a4100000f003d00743d9401400702c0385209654460782c0f100c030344140c503400c8002e0100822070280c200001003144c144a0480001d003120f4102d102421854105220200880d4018403010341140c00401e8880200103e10241403ea14000052680140ca8400c030011200380c00f050f418014220a80401c0700c41e680c420341200c444040f4061101240350030890704514107a540000e2603507a51103451308604040c9a0002400c4480c0914103100448200e82e080440903818459000030f054a0300b0000c02050450700817502565032500001e0003039954070400d441d59807003003280d400c212603c200d00c00c5001c02c0c090210005003800480341d403e00b4040c3c4001160480b07480c001c0d64285c4240c1c4112a059a66202c0116401241701400c035400610017100411581c070b541c01101c14119141d0010400102e40f07181c6401111402010141140d01d4500590210742d03010007d00c1c4c01c400d14a4185403c503806003000c4510f4800c0d030944e00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 529963615 1250 529962365 529962371
    0xc0a1409130509012d320412090b04060513030b010f03050c010837020f18040e07030f03050c07030309051206012114070603051f06020c0d080d 63
    0x4030101c10315001140b04288500003400b400085041c034034601540c10701c1103036041d2903107406440e00e841071750b028220504d000c1103204513889084100349040304a00300301d1080880b10a040209010983c07032418441c0e202e51900310002841c140041e10389000350b00070001000b800107400c8881c07403803100c40c05c1c0246810850001803941d4490803c480000c10b80700031a070b13502815207222195800381075058400c0d012441c188900100001040d51200c001c0c060340503141d84000303098000c003002c51000d000441000402d2a564001e0710b5051542d1000c0d07580c04910603420120303a4100000e001c5600012a0b62120032100d803403615103015903107802500d08031000d0740300340e00d40081030540c0316600c082140c40540b00b0420702c070401000c040d1078501c00d01443d000001200040914404040e805a070403c1c020040030240c071495009141c1806502da024000180e150420710050040407119449070001010500541c030f8a04440651106140940d16108858007143d40b01402044400c644940396840030030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 529964865 1250 529963615 529963639
    0x50f1302092806090f0b0c25140f030312060303040b0d090204060603091122020d0e06060102030a120216050607020d230f0304030c02191505030c0a1409 67
    0x180c00d2903105110640921000340070016003d8020038142081d00c10b1144290380d11400c0c029015825404440361034094480c00101c8601ea41d421070001e012020030400d84801245428466000060111140c0348110401e0280201e240c1d80041180d42c45081c1c00b040707043e01d1fa500000281140169485450418400180300d0030b0000250702c0406881e10071502000354546800c1d01320112552640000d201d40c110401e404100d150042d00d40c031080c0146500b69010a0b002001c600507600725460300e141480e00c0712040c0b0030b244014009203903c040f0130f100441c180280c182d03000f402c0d50802c280312001e880d03000500c8071600728143c65040c00c26800000320b4045081501c0000c0d0343d400041c0034080080c10140d204200440b0183c03809440651091190b0705100b0044044081540042c1c0104c00303010440d2f16174001600d4104064041d012072440900042d440c08911548281d080c65005080002c200f00f000002140f030301c1510000e00082c54424a4003514002410252080304411640500b0840304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 529966115 1250 529964865 529964899
    0x140307030e0d0f120b190f080106150504090536060109020a12020d0b030a0b0f1302011b06110309030c1504050a03080a180b0601030c0801050f130209 66
    0x200d811800352048400c049910001142c0018900190300d00003040341180e8800030f0100c0e044290303804801400c1001401004465012201895020800007d6101010480d00700c080c414a03000300740e0224007410740c4a005a000b486480340f400341c410029641d202080305500a0302c0c0010003015609004142020040d02c841004a41a00c45440d10b2003190008910390301c0c1402a20314400607030f22203040000403440324001a4000c40380b640c180c03560f42c010514003a5002c0101c402101d00030b0403081164108044201c10405004040c06e40c05020311a4180041c5d91000c8000015440203000b007040e000180380c40405804a40360381d00c91083c02105000f848034010004240c0c14003800101c0d400c2071a840349103908803004481c06001508080712410100f40a50f029a40c0018900710001d14004141400700c04ac1462600960b1a0501c00c03081155950b01407003020400d1040d41043e181360741c94800052400040c0c44186801000081c0003e4214001501a1007024400400d100050103401003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 529967365 1250 529966115 529966121
    0xc0504090602070b16080a2a0503070f03090206030105040b03030720100207150509011202030708010501080105031f1505040e0f0106210f0317040605010f0b0c150714030703 76
    0x40d040e0307070071140500443c8200b0f401c00c070701e1203041015450b1481c0b907030340d40e510013002804412380348440c0703420710310906c0e880c3c3c441c120400440100f617403107094403420244001441851071200e0130b020f051401c0941713000b40c2c1e40c000c26a411503104680c00f0640d071600c81d000c00d0540c01012070060401d508814024a2440e028603900d039510010b541c000f00e5a218801c00b244da841c5a4071401814030512074801d0b0704144100d00428030320700f040c10718401142140e00204100d80c421126980050503840051100e50f80c031044490051100700c0040c14690002060fa482841350341c26189e0200d595003138008208540e4030740da900140700051003003021030b8204a61907210254004490215464400c010946989031000b80c226407204000002c01d003805580d41e02e101a0700d100c400e409000c802460810782010b40c49909100e64800d0740042240d500d8600100000c47e0a83c0000c02401c1080c00018005440000d02100d04004010114843d0b16604402d641102c03043c0e20001c1400000000c101c1e01a0301a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 529968615 1250 529967365 529967377
    0xe131a01030308130803180a0b0103050c1f08240a0801092d0312110423013605060a02030307020706020601060c0b180105161806080f040c0504090602 66
    0x20310307500c3c240e40c0c407070440c802000340c0e0383c4008106060903c08601d016070307004071100d5031603c1c10080300c1c4440810349400721000c0c3c0c00d0f8403c039230700d6005059081c1c40e801c10001020301a010b180100111404440c409400000c005040c007140840213000706040c1c21554540100c50304000e0101c0c0c141c29224000ca501814442030261141c45084120441c4081450500103c4060040013006850810341c2c017107441d0910210f900d036440d51202c0b400c00d181c0c070100d8000e10080a81c00ca214165600304010303503216041040740541480805480c00700c18030004c51f61080d018100b2024005020040301c0c0071b03550b400090300195040700b03011803642c0720701d90004021401403140f034084a4400da51800304030798480e0240142400182d02c0d81c40440011401c3e0440ca4218030108210000705400460640c21540103c81c25001c0c0301d042443c0c1e80c0c1c3e40e5046101004510034010020000c4c6052450207080c4a20140105c0c0c000c4d82d5030000141407100c2d54005030040c100040040c000e45c0f0250034130b07501a41002d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 529969865 1250 529968615 529968617
    0x20406020106140609011b020418020f0306010e06040903030e0303040516090b06040521010510170c031c170c0d0c0806090a0e071703120606030405070e131a010303 72
    0x880868034100e411004002c00c6001800c5501d000494401110903881c440000070441f45880c0210005903034030f01400d400910b44015400b1652194010403a10507100c911450003a00f2520062242103041c1046c41c1d400300055601213019001844c0840041101c00d00c0b00710540030100901041010204401002d9580303003680000300c2d0346840914045410041c2030f6540308408020030425401c24015400d800c694414040c46a090444291400c0d20011540d003409400c401d0390a0020490b015000584c5013114402010090100c07030109640e482441800f6103030101d1182c0ca0300416104410b00d1908100c410303e86d04a50130b003c171090354240c2094541c03003609418858280609445559034510903140245104415220b98200400502144010010350b00440714046040d9440e00f40c01c40c0302c40001d600965941c2d9008a10f80350505020304481c2c030550b010000e00012070b03000039480042d070f22420038900083d12101480089000d1380c00000300141e4510b000d8088007062007100604990003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 529971115 1250 529969865 529969871
    0xa0803091e190204050c0c0307030206010911120609090f071502010f23091c1110090b0403030f18050a0309140a0e0a06030203120309070b07171602040f0204060201 72
    0xd88005910740788089a02c4000210b240da04001610f000c2d017140b60400f42e003005447c5040b008810090555001c0c2c6c3d01507016034000d03001042111842e00c10f10802691703659100d82040800000850f03c4c0d103029140d140704075458800704404180500c1880e0300201d80d8012180410795803216400040031f88000355016520b040710010255505000764000d210340003002451160410844059540b00030300030326420300c01c1060390000d6030480185040803400d140c0f03030f40c0b090722030310948640340400b5040386080090400801c2c4000409600c0c8040d00f040d8181800310305480c08050110051501d00300019983d83c12413440e0062010206181d43c61a00039a506010503848101008103144c1e1000791580190b41c0341c1c4204004400302c060950000d00c03072080495560340e80d400092030075020034080c070104040003040c0322003040300300324101c020910a40403a00b488c14540f2028103010148280340444c84001407038901032001c508441d051940d000300704008451207134911900940060042c81d01540c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 529972365 1250 529971115 529971163
    0x81306202101060f0905100c05030307021509011119050d150810050601050a030e010b0607060e0f0c061603020a050d030606030b01020105060307060f1b080a080c070c090b01020a080309 81
    0x44508072904d60348615880d020802403804081c0441405051020420000301c00040000039a0034002903019a40640c0200700352040a0b0140310126005040c401040c0e00d4211140760408010742510f928000060500000020f81c8005460034031502220740c0d116807030103641d000450b0a0040c150300b500c102800300c80800f280c148801084400964925003c94400d00800800501c01e0300300340480100c04001088134201400070980359002000216505a100c1440c15030742c0104000300340c5080480c0008204d00003008010405502c250005089100040038013001030500030421f0840c610383c028100e890141114200400401150040100003400d089410b602036205001c1c007401004000d001e4121685005c100384c0c2d0440c0524651010320039600c1c040c8400e10030700b00c03030f50a07000d024041d01e1f6950103202000602c03001d0000c101c0d0030010f90511014001c61610100102500c002800000d0070f910748000603446d1048001005011b200d0000070042440320200c3c1080003240140c40b0500c042e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 529973615 1250 529972365 529972367
    0x3190c08040b06062d120c0c15011421030d0e0606030127140319030612030e09040606050d08070512091005090402090a090b010f08130620210106 64
    0x4800c01104001150408141000d071042d07072800c2401740213120112910b4800e544508802900080b10f0901c03d0380d0f40072a03241d072440001e22403a070000d070392141404400d40c10712042c079200240c0e02e800b03280034030f50300d10098a400c0f400340425010f150906080744d84840043c825580a403e60681c0c1e8400e42c0102c0001c101141014018061141e14146055400031321141d00e068121410403001d4030914448a40c00858600a0004040c4041c04903039907400f05041d21001f4042c0c0b00240e01041c100304013512500c02203036208048100310141110a400d040cac89509102000e002943c0000383c0c4109240c61801c204020040140311091203041928850100092840702e1400743c01003140d0084101022000303c94410801488255401040103041001040100341074018a81044190715a03078118401c840d030304000d207055004114941380c1d8891401581100c4195407000b401480d0b02c2d1138405001d19503550080401030100c19000440d02c5170726816003d000302940b51401200798051000120304a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 529974865 1250 529973615 529973617
    0xb1203041404051e0106050307080f0c030c07170412140109030c12020f0601091a040b1516020603040b010e0a0b100807201c0e0a060503190c08040b0606 67
    0x218000103410078004040300611001d808000c02880440c0048400c20b044140010b4038140030b00314a40d903840e240c0c58416005456520081c1c44500c030084a002003000c0400d074007003142d43c02420610342079111707034151400070201205c000c5094141345003c5808910000000d04061090340140400311103e0443c080b502d08a410b00d4030302800040d10115060b001c1001c50006042c02d00f0944101c030030340007604540c070b070502c04203030481c010140d103c2c002c44500781e000c00c00c2101a542c00311010011000008000780780345030902c0480881034404a2190402c0092210050880d40c000e400c141d524038044c0741480c4c440e0401d014100319281174001040004441d07100f0700e40503d0340940302c01c04030590850141e405001c000d01038403c11044045191100690403580405c181e400380090514074071500c569074a40540d4901d2008000e4902080030701c82c1d846240391320803188541001580da44400304960101c07207072010905000c90400e10740400150b484400036104500800c0e9107441511481d04100113 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 529976115 1250 529974865 529974869
    0xb1003060b0f0c0f060106020d030b0f0a03060e0f01051905010608010315020304060207140f010c0f02030d0e0a021c021c0f0b0604020c010c080103050c0a031515180b120304 76
    0x203560402d00c4031196241203400289001c850b0341040320001110b12078203074a048000d030403c000507000000c510607a0b40d09030080b004442c600300c580181c0f540080e404600c00e01e0380c0c0d11014244584807100761420040600c05203140300100070080c00310340703410082540403c0769440070505051903e400015414071a48025040c0d951083c540640d034441400c80c140607403c09002507514503800c2084000141150030260031019402020700440554000b03201d084409035036244086c02082d43c1000700803076007c400c441d812107500d200052650000f4a20364901108410700940183d04079000425803507070741e0207411141d44210f520401260340090b100307181d0105041c008080011403082d01d80040c03202e4408903800100580014200095104514295004900355a000c00c01c00c2e40184103100381406022204481075a119020a00d9550303072840c4042070300703142044182c0d0b84640141d001c5424643ca0000c20440d02030b20307004401c1800d00d1000f000b5084230300303114400c82142c042803020013106482c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 529977365 1250 529976115 529976129
    0x807031b050105040b07150614100801061205090c100519050703090e0703140a0b01030b0409020307050d030e190513060503100f0603020a080607020f0727020c100b100306 75
    0x20130f2528240c00b000c80e0b50051a8100c800c401001d454464400d6607101e41002010b0211200805444541c28020500002c0642d1801c011340040180051a00200112510340903040c000521750754003265a42042c81e8185141e91022002e250240c2440d4004081c3c09800032500d80002c0144900a050b00d140c40380030300003808590704c24420480c00d103810980e16401502030501140e00c1c1800703007901d22103207011503200108582e9480c1080c600e590510500b024604180c81c00c00141507150000f0f640d5883e03d101d9588607407041100c50301054401c2c3d8518030300b10000b070a0460102c51401c10a10900e056000325401160446903030f400c11401e03401500100d034400390140002050311200480641003807244a000b01e91a14000001030b243c4c0050b117001400c801000e00f0726801e2555000f81451000e80c010080c540c041c8100b0b000c000388000c01e070b00ca500c11074500d000490035029a440040e000d13201920049020303201d18000a655141c0210900fa4000c844124641c06820380a40442c0c500740240300c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 529978615 1250 529977365 529977367
    0x1215030f21090621090c140d0c03060b1309030206010905090a0c09050c091203040501081803300411030d05180418200906061822060807031b050105 65
    0x34181c00750842103c02c1030152400c4e075000c1041100e4800b0707104108000c903511501d80408001c0c074142c1c0840c4040d680011070345102800626280c03507412100720302020340306560303580c0e00740229a00da64986028001406044c010303c1c00e40e0602030344a840034410b8200c6d16040c0000201c412801043c4407000580c48003a0340b403600c0c00c1c084004010300d8000d00c041004002000b4445440e501e800301d07200c0200070300c00115950f80c04d14000400b400c50143c0741404113401d90038a00c20200000c41581d00e6041055020150103045002d001d0400889588400300e002a10080c8018009203c4003041c1c4000300b90115a544c002e140c3c0212a81d03ca0015800118051403d03420740030714280e00400003c1206030549510b48403103842d014800540300249001120a0407c05645814034884542d80301c00100c500c01e041180b0740c203207808900031a01126124541900c141c3c9041c0d500032003101519002c403d800c00820380c840320b0309a03030781c0d0170b41c00b040d01d481106800d41c60080ca0b01d0440e110a554060b9105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 529979865 1250 529978615 529978619
    0x317030c0703030c020f03070b0a0c1b0f0204060b0c0109051213050f0a0510020d08070e0913020a0f0b0418050601170a060b190e1801061215030f2109 66
    0x200e0003000da09480e9130440c007860249010b0748000300090480e4500a0070403813400c0c1401e1800310112251000182e00b0f21140491700d1200f00c4940c2141c40f5a1900801078641010462002800030106038002c082100300203c1da5031508001540081d052510402c110f509620092611035101d00550b00710f2542070b020401c0a00180c100308220903586100a0f200926142c4c4070310003e8016078038001d1007401a4030044000c0d01c01a4410402070300301d505410082d4010280f40042a44d01c5001040e1f10b40380c8890340b044404640320400c0b2600100350a220104001e51200305101c0701340c0c0203100e10900500c040520300c41c0360031144500c40c01101c0c161182c90320340314001100400d40900501c0f1051543e91082e000590315136010092442604801d80581115941c070700242c220303002241c0b040d0058586403207035a28102030442046c15503006051000c4d02e20041880301024104c68100540e40750840b031400002c1003150120891500d201c0d8489a11440e409031929801e54051000507001034040ca0341 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 529981115 1250 529979865 529979867
    0x1060b030a0b15071b0f030f060216050703050309030c01050c0606040e101a0a09053d08030909090a050601270c0801081b010e13090506100317030c0703 67
    0x1400c003081001e09090320240c800d40481c0f001d40c000d10000e0390103da4464081c0b00075100503401c0c3c0701801241c07000d035848078159242c0324001c0c0b030000401042c1d6070f80003c0702e500441d200302403003104983c400c040fa030201d612840c000c0d8883e042400083e0003840380d8400c080642d8001c0081c2c07003403481c140004002c40c0d070300c034000c0102500415185005a0080e206904600f030014040c540c0716070814080486402c08940900210380d54503400140c20074a0403003070018040e8503e000a182c4d40c650ba20f400119210003400150101d9070b03071120940c03d280312030001041080400601440f170302c125010304461303560b43c0d030320303500c0701c83c8400e00521036040306005001c840c9020400c5400c10050340da0031144010340700003000407170b01016880e5001c52406001082010401c000e101100100400b921403580e502d080042c1c0880071309030ba080d00c034040f5002400c010110940c07014540b9504031044a0450801c0d1610460211450100340d0b500d40b180f050300364070307050324000b107a0003090140e80715807500d021030318 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 529982365 1250 529981115 529981121
    0x2a060903051c02030f06011419090909030306150f08070302031302040501030b180c0f0d080c120307090b16030809070e01150806040b06073c021201060b030a 69
    0xc0382441424880700c0015640d00c0d00d50500c25800d240c0040e13407428a101152126040141401d04000d00d881741000c5080c20f0b04251101c00148480e0141c152400003401e407030f01144e0f0f030070045a07a403410a4041c1030603070680088007100c18011321801011000c3e00211401c5540f0403d000114101d500440c0f081351280d40110342c000000000256031017403503800141078030020391003603070401c80c00d00601c08010751514001d0f40188000e0020301050700720740040b800a88203481c246205d0b0382c1a46192080c011383d202150340d071459080c02e40e82d4031042030741c0018042e00300391900000a03a4483d40400d103000440200c40c0315400003180000742e0ba0b11075404484a80d801080310f03545003d00000000d10714400000c039406072140d45010012806001c1006200410007061140700354100003210030305032101c00c216241c564000e0588c600031900d01c4242c3c1d5200c1c4c0144107100c400743c482420708601901c0a1241c000c114421100d84140034443c548880c03c1e652540070b038541b030341000c0001c510b545d5050782c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 529983615 1250 529982365 529982381
    0x906060f160606030c050f0406150f02190b072303011502251706040209060405060303071a07030c02010b091501020106030204050a0f0506060c1203070908030c0d2a06 73
    0x48070500d0095100d54800c429220164002ca818030590f035010320aa1500b6601e40d10a84410382c0c2c20802e151a1298542c0e2100036140e805040c03043d0106548012803080c01980c01c0086040842a0324010600e8000c000900031290714001494800741c28200c065900010047e0014041b034850443c0d0078002890107011003171543c08190700c00c0c5240311a030240d10241000a50590b9074088030061b140034441c00c07038400107066660a60b0400420840143d03a2120401d40010702500c001400daa03a010200e40366108060010f090001d403d84000303101c10341107101504c030f00d040e03a505100c00103a84200382e007030317074821040700703501800d42c3e070029100c018940c01e40790442c90148000306155a9a0b0003041c02c5500a6070070064180c4c95411051002d07006004454002900742e0f4200d107000c8038002d54a40b20340c800525113925103c00000324403524070441202c00900b0380041601e580c1c0018914165a84c07041c458440045098100901d00040984c03050310003148191415181014055503640000c00c811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 529984865 1250 529983615 529983637
    0x403140403020d1a060607020307031203110c0303041b03030c1104061706040c0e010803070b0603070b040803030a0e01050601021e120a0c0b060303090121060305010c0203180906060f 80
    0x103200020141c2d480d101009007007030182c003828019850145100d071808034014071860003014204003c100503140000c01108480d00030716404c240110401c02203000d003101542c0031b41c201070003088404265001000441c0582d124640900300b00c800d0111a02040806100140100f151440d007040407480d091300405122100920010b80340b6100c208040780003246a4a4105551200c01000b04003c031050350303400600380d046503100745580340803400c950341d109032100142100c2d1f500022403181c1e04e0401554000c1c01d81c002e50252100d4555505c65a02e81044940111503401d000d2204540700042c41040d0040b8810b84c003070803250460500b290b029030218020340a680c481c2d03030300c44180000c101c4040d0080000503030342c10b60480e02e070b418001407100c0d014100c68800c1d082040041c6113070fa000007081d400741622152415a25101b80e820700c00622641e84090419401c0006800c1c21b168080018140151184141808004007000b8403c800303900b01c0350355030040e0040091042180144001c0e05140c441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 529986115 1250 529984865 529984867
    0x10b0910092004060f02150405120a0203040305030f0702010305240f01171305070b090d030e130f020405030f120d0e12070510060918060b13050114040b090708040314 73
    0x80342c808070401d42c025800000024481c4030a0429598140540c82903070489107010081c0c1e04258075015158000c000c50304405000000f0003507515402801510001d40e00141500d0301c401828401070700303a0b0720072402240042d10303080c0000c1a114620484c01c8003000b0041c450b0641500f80c02c18840342c44d01d4240d80034180040130a074103081e200d1101c13800d440b9240000a885041042c3d243c06843c10b0b206401c00700c0252030a01010046445610760380005036054680450100303a590f01141007403804012001440341441001654030301039800a104032042601200e40710385050f9805a05c90041210070301c03108100f004030422512003034008a804880c0ca40c155070412801c2c81c2804c0d0664801c031011540c5400c00d0341c0c50450910144140e100400d00c45405114280d0080100c1d0300b401052140105010f0f0303100e8407400280c440482101c0d45a80f41c040070407581d610f440788252240d104003001880f940c01c00240c034a0a01b82029004e02520450700c2d8401540c80300d41c0c080c1c4006503240d916000e4610 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 529987365 1250 529986115 529986161
    0xb041a04020a111903261b1909051309020603060d020616050c01080601030e0616030e0d091505090a17030f07110102010e062a0415020f010b091009 65
    0x5404c2c86000340488141c191900d40c0c9102d03141c00f421044943c100b490881d01c070320b1001344e401c00300d4841103039002000082d108009030b0034804a0185008018840240d1a6051240180160400260410349204981d40c1c0026207600507500c080d18800040250800014008500e04d414083c442c4009540700a12440c2003000d02103021010307031810a016104d0f41c0c07004000ca009035070003040543d04078900b0b18090011020a071341d41c50741c98030058580700b0b05c50903d40c20b54100783e11940c09a4201000d040a541040c90b0074074000f0075103910b5008440112903d4404181528042ca0440d8018480940b0441d4803e2410707030b0407501c0d0700b21070000c4c0b0b600380001c000000c86081780c41c00070a03c1070b10a1307140c94039140c2c410740020300b101c0d070807d0794601c2c0d903010609000c145414115a1048054095010080b003607184203410098006c40e40000b440000b03592000f41074640209110101c040c01030300802441c60280d040080000702a1004901c01000300300c00d10070fa18140e002108154209400c1c0c4003691 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 529988615 1250 529987365 529987397
    0x5061303120807080a0c0e09100312020307020301050115020c1309050d03021206090403121505090a2013050402030624040f06080606090f0a030503070501050a0b041a04020a 76
    0x201d081101503000550180400c5032040e0070141040d0402000d01c000c200381101701074040c20440b0242083c070f100300c00b441c000800304141e4021040240d688410800002094418065940c0c1c00800e0201c7c825402c1c1030021170003044000c0d09001030244c80e401040104034080c144102e8966460900108a40b25954000272810421402c8018030099a00607980c04401e0500300b111170010301040d01c20840c3d003041c0300220381d100141d54000204081c000512441d4011030f02c996040b25407005070030043c0c00382000114151a40404403d200c1040c400b00035610074544502d60740710350b051150709035100100c01e1000e800d00e903000e942d0001b4041c02540201c0041002d901342c0d4500031650310142e0000150034030120315607512034070091446050226250030310900107041805a0414903014031070030484540d403a942c00389a6001107801a00307813035542c0a503090942c081d000c2103a49180550902c9090040f1b8107281c030070740c000c1c0c5664841c40d1420b0902241000003030f50024004100700010b03401c14074030007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 529989865 1250 529988615 529988633
    0x90a140307020f04140a0510080609010903020f1c0c111f0f020a0215032e050117190c110d0c0b0f04020a330c14060c0405061303 57
    0x4180200011610381d4418410400101c40c5100c50710701a50501030392a03480200d030b030350080e003004440714042031b02d5948407414030041a0b290700202c4a4895502400031a11040d84a1480c49001c0e40c240c031301243c0d0850000783e0b2018054642882d002c00341d0400b080070b40c81020004049071040c035090841c84840d000141544d51401c411444080100191030f520540117040d42c850000c60b4009020300810f580c0004a0307e33498989018a00c0c0c1001002540700c2c5000c2c01c04186080100501441d80740001d100741140d9a424092035000c036018581c00d00201e0800c0b03044174800c4002ca02101c000e0780ca100c4c3c440c000b0389020f48030300c0184103010008090306001841541585101c942e501d0b00101654104a042e0100107030458030602c03c600302740000358441d000e601042d9003807290b030b030540384170405125451510b50010720340d603c0c08226201140c1c80d90201c44da92880b405128524108821003c001e41c62750404d598100038008100400c1007142411b1011304a958801466040c00742c1d52a22200301c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 529991115 1250 529989865 529989893
    0x9020307050a2f030903010c0e061e0f04030312061415070c0b03160318050307030807020304120c173c0304060302191b03080621010617160e090a 64
    0x101303800c0440c01c2c0d40582005d100d5a1405440d40c0b400c100c210320b120000c030310503215000300301a940105500181307000c00c401046512243c400107115607503643d60304000f0b18070044c1450301100c0da4240f28001404086220100100700401445507401102468010006600501d011030301420b03031180005040181c3c4000d03512465078220900855101c1c08170043c126681184080c159a40500850011400001c1940e440c60b0341030420031100d444d4072005a14501980e07010516116009400c04108a4454507003030032100c03040c010b41441c0300000c0e05251101e018003180c1955100001800c00741c05210120074845000220000030201042010039045070300070341190002c07075000241c1301032488900c1c4102054440ca8903083c0c140440c1c4a0300c0e0310b00516450005002c2090107030200740f03283e5880d14102c2c003240410003101d1106070b5850015020340440c0c482c4540b03d01c001c600041c0c25060200c0c1c00116032900482140945042c8059038180e0600504a0986482820001c000095000401080b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 529992365 1250 529991115 529991207
    0x40c02100b120c0d0311070303261302040209060403150c18080d051b0d1d011805040f0b06040e010503070501031a10031e060504050109020307050a 65
    0x540504900040c0568010909541c0100003840720201000300208443d41e07402400c443c3d04510a10a060071208145804a80c0c075890054500010415402403e4400603002c0e15600505403104c8048001000d002151201105400504410300601e0582e0040010307010060400b810aa1280c543c840740403c00641d8440d010764412040c0483d54102e100c0140300100d0907000c6c01042d0030305140d41e44509500c0ea91005000c808544070300e100402d560b19501051074001220b072040105007000303040d201c510300700000703440c003c0640103040e5201d40c60107a081c2d04c1100280003124503003c14840208060301901804603581c82c280300084d503c02000300000e0525000c203111039418903082508015481d44018141072038400c1d114030500030a00c0b9031030f68100856032081c920310030900030f4001e0984856040f82091500d02110703c98800c683c000e4058420a40b0f04020b1a070700c03a111070040384415035041c4040b54060102001461203840c9024840d070a900a1025000707070000341010820302011500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 529993615 1250 529992365 529992373
    0x30e1509010b0d0215070c050d05030a09050a0f1e0e011e0909030e0409051002030a020a0908010c091211060f03010510021b06070602070503030a270b06010c0f02040c02 74
    0x805092401d01560740d59402c201c0d4001030b0b10301280c2c0000c03240046801c541001020109070345d01401100b40c0300400400020b403400500300a60301e001e5480c0da10040003034020072484100811141040700203041900c00c2c1442405940342065105001035a2641c0b0f1146900780e4050041603c3d080e42903d64020b10440b44013040d41001050b1078000b00c2c0e180e42142c8650307498031a0381004070b5031051b4408101038003600e00044514260500604042e140025103a94034000014041046100c4e802002182400e80d907002d260343d1107488503400d0325403130f00d03183c2d000901c10802406000340f05801140141d00c241100da4450800402107071007a040300c4015000300001200410590500c0d49070664290010b1024046419241c01c9640f50101c25841c0d05000c1d09020403480c0400c04076504032280d1b5600141125180c1c42c0081c3c108018001480642c1030311880300825141d00c020401c203c00e41c05500503100e0406a0381c402c01123640c1120303080b041e00c6190160070f621f800758603203100e0314000702d002e58050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 529994865 1250 529993615 529993621
    0xf0d0f020a020d2303090f0d081e06030a080a1b05010207061a090c18030304030f02010e010206040b070309080412060c09120308060f06040f0b030a0c0306051c03030e15 74
    0x10782003102441c00035062264102110200c1d59107a02c00008162505130780c5a1a5168000040d00d0021440d440407010301c02d0903100c2042c0d5401c481c2c0760307125005440803141e1111880307072000407018054036080d816601110070b5030001240c8001070000a0b01514045080c1c1180d40c201008405081c1000d032101d9500059202c2400709034060104c0c010390101c9480310380c00c1e10341c000c00c00d41d42c402040c13805800e1010400c08002c1501c213a00310300305e2000904507602c0315200d0901c42c0d18041c045d00d0890208400480541c031550000c80d2481c0300d40c2e0081030205060b0398051082e0040e20784541c045407040401c000119080c540c1184000e2554021540001c41c500070603401340c01e00b01e40360807558103400c800c0c01000000f039100c04c00c142e00c03450503901007190f2051040441c0c00c40c040ca4105031500d460108021440c82c00340400b46120304482c010901004a0000c0250125002c81c041c1c0750308556150b848082d000e6000c41908800c1d4800d140018040200980b1642000002c4d800801d0403000c900c24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 529996115 1250 529994865 529994867
    0x2190306021305041a040b010207170f0f0a0c06031512060509060603160b07081b0f010c0e0d240c0306230105030106110f070303080402030d090b030c0f0d0f020a 71
    0x816005000700313460070481c15180566a015605c4c510014500c00ca4803604100c030b20303034400d101741030003010400c00e070300030b00007144404580744c00051038408002e20581ca04441500000142c01000707a4108280c8a481418445c0c1200079020f89164095551074210000440000802c40600c0050042c100064903041901d035039802c044000c1d050b103100e40d2012607980344003001084001d00321044501013035070300c0299241803070300c60160307481e12007000745c0304050305a200c88003254242c0c2001c44803000308500c8038094010b5a9000b0721554041e00708101001510000e010740518451590400811080c2045200004015a803d0b408804006922240108140d02d50150f69843c40320118407064621410480024a513000522035881089030420015000000c24082c1305288188207041d51801030302c07802c0160407010b0031b80b000c0b4003030304c42d20b511240802e12480040060318085c0084500e1078071585040c1910350001c00f25103c004008200b20120003e03240308480613600b803140d01584a0361003400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 529997365 1250 529996115 529996147
    0x10b03060c0c0d090609090e07170a0c170703030c03020a060e160605041d07090b040e15030c0d03050901020f071d0723070c0902180307060c1e0219030602 68
    0x43c09014080c0c9020b05000064001400c00c05a40130b40100180c6e0000d0403090351301d4000154403811070000030248158104402140d01c2041c14000c40300f41e400301e5682d40c0c1c1c3e0201c07420700d2a50f040003a00030f8801480082e11840d4107080a500a20444003810005c0c1c90b074804403800d07142c00312226841200501c40c00c6910b651004010091414024142864904c80b004049040910038460404450001d1880c45c0a40c070104041c01c40384404a444a843e04000001100242e50703004945101000d000d440749030000d5a50745115019080d41100b203002c1d0340586141d002440094154001c03400c620f8580c0c14100503210081200d031100c986214451a5502641a00034248008200314105c603103101e141e441402188802020141a030313551000d05044500046640007504014000168070505000c0500c0a4010440840659031a0340c1e54190980b01d81c014000c00411903036410001000400c2c40c80516480f25002800080c0c020002c034814040600b4150401c0780c0056010a0210412072824 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 529998615 1250 529997365 529997383
    0x306050613081e060f060d0507030c0e1303270b0a050711010503060a03110a0f080a0212030306010e0d0602120f040b0a0b2d0a080a140106050d14010b03060c0c 70
    0x4098030880e01c070100040c4c0e1500d20050040c0c550104040100c0d8803911030202046900760043c09440040e41c6074a0030741c0020f60944601d00b810aa4040821480807011040b000c2455041d117603000d041026030402c0c140f00c2c01d9403101280c003a1090b00b000810780c175008024281d5031025039411303950f07a489140205042031224a1107040003400d10400c25183c0745c03181c0d40816690029120300000000c44001506401503400c241a0400703038080005403004000341028150f842221002c0406111102c069030341e010407200980020b440340d100041c1424a080381414041c0240b1000d40742100a0342c140303c1051043e00e078014130300751420400082c010072803003142d040310768230405110307000c559000560a0038002e07101414880c44100000b900c8484045070341c120301f0001d402d00902e80c0d034600c40c65450b41e2040800b41c40410103076240441a40040c85001c0503903000415a04080010b5100e0050003c0340f0041c1484943d07940f0005000340c2ea080103130600c00c00100d05c06594030025000d20600b080458 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 529999865 1250 529998615 529998643
    0x60f040306050a1b0c29070503041103070303080106021504080a030e070503162d030201031a120d121404060905070b030f15040b01021b0a0f1707080a03020c0f01030605061308 77
    0x68008180c01141b41e9001e1604041c0d00e2600c00d8580d203603800c01c04144004041d00d90b50503c40d0a000104240c0c000351014101e4840d5000da0301083c500e40e01c440d20075074044400802100c0c0401c4002142800f0381e00080c044002801214001501da502180ca010209043c06115580c4030ba41040380c1c00c0800c008000c000155490144003a0003030640b02001c201c3c5000c024107150321266005020031200b454080070700c07401400029803840f8480680d03140c07680703c554600010902c01c10380c6180710890043c00400c450380c8071091001d64071621030710300511100000b224240110080011041e0300e44010310f00a184000350714103e41411500c1d40c03401c9107001607a9000301d0520b0b1303440070310b43e07008181c10038810051340ca00c8244940304c0740010340090094120f8130751141c40b8840495100b03130003001c42f0a0fa07011801201d032683c0d2641100340d0f54001c41030380100180d01042203002e55040116100d2040d5034103041c00b040e02d50b1a40c0004103160003070842c9015034001d4420800031010104400c450038180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 530001115 1250 529999865 529999913
    0xa08030a06050916020703240f0c08070504120b0c04030b0901020426030a0804020a081e0706031803050d0b0a06020a050606150405240f1206060f040306050a1b0c 71
    0x4d0b001030744590305444041c000700314400c88a140b80001c15a00498410074040c20004144010000320082820780c250300c001580030783c0000d220a0040e811581941c021000d54011085160350f0200c0c4500000d00220482d4801e0100000041c0b601036050f00400030440051b850f00d0900c0522b2440014610041c00700503280c2811101d402004402c039802e18125282940306959940041001306d442a40030726401e02c034803040211001d01118500303484000c400701b9102c60554030001102602e031284a03220b06803c0780f00b051400039000d031008001c138042e1a03001150035007a0100103043c0d980d182c0c1c08840036070018a04c0e04100300041c0006544910101c07403103d5648083d08400845005500600e4022104000d092840e048607000406400306500742d410390f100c200894100c1280c02103e000d0313042c102c050000c0b0b0b485252080a44448490002030341c1c0c1054a952501000381c031000c0d01c0b4100d801d994403405040e40c100003400d0308466000741c540b07032602001c2d890140312880f80c2c05100742813400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 530002365 1250 530001115 530001151
    0x8070e0a0b0405040b03010e0303091501090b0303160c050a030b090618030307050d090605040602091c031d180412020f0601030206090d03050412050606010f020303090a140a08030a060509 82
    0x207400068409454003074030005604d0214002183c0100360701c0515848612000c400c00c06a0300d0000f40398800c1100c64100c1800507644c500c424400e0b6112000710591540003030001c0e00038220011145a0094040c06100780c0e0141d03200c3c080740c4119100e41040d0b0304a0440340811402c46800c1001c02d0f0024000003003084039a0380b040301c981d00c9000103000c40b001c1007c00102c0b184c2c004010342200054941010040102e420320b841d02c04003d501ca024894001c0000c604200d03599010540e502940c1360701364489030342c00c150040100a030168101000d9500c00308803548142c11901c0501c00d0f6106030302c5100703d000c0e200706000010f0325000350000602456800038005000517151401078600d114002d03544e1005541d800c0c80d00307441c0e500440e00602d03c46488800c000c020311000051031409150280c0380e8500300b01c8100c4c03040b40c0300d1208881074100c50340031408a01c005426001d00d4484160200d0a641c4411840d540d202031a50050b01d00c040c14a440d42c100340300503e00540702c240c014901c07942100443c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 530003615 1250 530002365 530002379
    0x7031d0114031f0e072a080304021c030309200a0306090305040b1c0605010f080f04030905130e0d0804050706031a0604030303090615081b03030d060608070e0a 70
    0x1d2010582802112404404584000c2d16958040040e01d001240796145a032207465180400700126401c00c006140e440140f8100100e4000211085144da400c07204080b000740c0710240240d20140c003ca0300038801400c080002c18075211640880c9110b42c1d8017080302c00060070441901821408a0b6484441c0b10000c5001d0740d03180d501c91421a984203002260b102128141503070913000315400314681c00c3c070000d14a90740140d503808402100300c0040741040715984507001101c03280480441140400e01e22800b160382800040329080d40075129181c4900c1e45511178010500c4190981d900071a441d45450201000a10a02149003d4021854800c4140c80c0503103800765079650921039802170541c1c44025840f40006e02048060749030000d071403103a07607560703d1400800800c0189001d850407494a5a2003001d4540350000408a80540c40104150800800c0760307417001c03a2148000d5850b102c1002024481442e50103030400424403034076021f03160b03c1c20450141081d084504050720038481000c0034410f403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 530004865 1250 530003615 530003627
    0x506010c030c08040f08060f10050a030609020a0803040b0d060e07050912070e0403050d051308090f031e07051002010c0512070c02030a05010506100512150a030804030807031d01 78
    0x15078251605a802108038204001c0c0c52191350011000e024808501003030f141070007d041c2d80102c2e04103aa14186684840c1c0c0040e4400c1513014480c0c2c0264040c2080010500c2074008061a60008002c0d8000e030399545400c610715489903010104424012034043d000b8900352003210013316803054010a2031401c100300401034070600c2d0413984144880c004d07003056000104240c50241c00c06100030201402c203070902820f560842c101540c44a42020002203411445414104c46990302054481c00e03c481c0318100800b01c81c0c0792030003a41521551a8000c1e1210340d0b00446030211540502410301c8034148414040d400700c40031183d038150384c1041e40704800310b94004111182140500391100c056221840221240201070b64040d41c5407081000c510240003040d84240d02405080340c02106a45401d181030314070380980d03445031081d11402d81c001001c0c1c280100d5070a62085005040000e096160740d242081038229400a40d8035200c041040713010503403c0070043e882190480c1c82074040e420204002480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 530006115 1250 530004865 530004887
    0x300203060103170d0504060506131b03020a02030c030f09030d0f12020f0d0903030f061e031202071505071109040b15040b12011a040504080406110a06020a0c02040f050601 75
    0x500f07403103014100100c14403101a00c1d0000104e440c2405607003030600702003002d01001d5828174801d0800e41c034101c4802034107102d03840104061500030020441210000e50081d000a400300003940000c1240c1c0f0003000c021b100802a0750501d031003140e100c94140c03040c1840c1c4400c0c0d4480e507051016050101c4c030407a400035118858104180c10140e52090441682c0066025140c0b03244007541c03e15140d0810150190012599029446001c000b199624242c0751004801d12800b0320404c842e030130341400032810307007009140c45034182e0046030403899550590b241e01c0c81d5068a07040003d000840d0100402c00010317a2180e412004842c96000e40c02c05850b491120a4068040c0007195040340c0300a0490702d4603000b000e4107c2c8004c01c121100080c2c00076660107440c6151700c01701000110b14008100b85403601c20725004a400c0f40c1110b080c181042401d85010450354211812845031a08000000b50b0b14001003441525695030028402120310600069400355005014011306060030441180d1f40002c0741d1003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 530007365 1250 530006115 530006123
    0xa032102270102070306050a0b03010f061401230a02030307090503211602062205031c140903070603020c010e010c021b0f040501080303010e0919141501300203060103 73
    0x101110007070050740b8215a0b5840200700300d042104000e91440305922103584003000740c00a12a690640038010b08640c554059120001f00c0305a28034000d521850803008400402540d10950030108920246a03070084d94002005030306c00403c111000758024500c000801c0241d0043c00396910707000c2e8120b10800c0854040d16074150100c1c60340305550f003892000b078081c0e40203010b66958001480021964036400710000700c4014104400080609000483c8901081c0051400040750307110b0301c085600740c1d85142c0c0001c12030002d00a00700650f070140f25a40c0204200c1d200181c0d580e429074415030070b4581991290320b95901d44206c80405603004519035041e2000c100070740001d101c010300002c03c1510440c0c2c1c203c1e00140b605001040010340000114181c88504800b8589640c80d800d225039039140011044c0340e9041c0c420605000074a841c00d000c402e00296000b0381c2d83e440c214000e04054a007099200390315010002c151154410303001c094980c01c800320001c1c10304a207546034001c683c1c2d40070f0603c4010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 530008615 1250 530007365 530007427
    0x92303040605031905010b0d06050306040f0609020d06020310050a1e06050a0926070506031303081302040203070c020f0301020408060c0c0304031212060509070206040b0601020f0a032102 82
    0x3125004813507181a0076000303640082105503110b41c41c030034040d08080c0c2d1046840385840c801003043d02c4d0000b8920310de03e502c410b03804c900e0480c9654103000382c10741c000e040344c2020201c0c0c1008005145800179500c140440006841024680010000403480a41c8190b1320305208208901c03000240107a901c0c10b0320404e0408643d101254041200d82001e81c2d07100d0800b01402c4515200c40b004480b00b5480ca45d580d9904580e5190741320420082d6034402030760041c8080c140d24000000090040405c00da200104525604420146801090680e84102c45000005107100f140b0400c40ca4808185442c501080c0c00071420300b4144240c0386d070b4403400a03080c0110703440301090007401100d040003250091580301009102c601300c00301c000303412401e110030307603000440c200340011400c0e04220040030311402c181d500a0080b40c440f070303c49101e034200c0079104904500884d0f50f01004120100007400501c1c0c481d13901c07280c0492a8810b441d0752000540000c440460040100c484424481c1582d1003070714040003c98 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 530009865 1250 530008615 530008621
    0x1b0403080d0b1504090603110307060f03050a061a030603060708060d1b0b040806090d0309020603060105090a0b1305030f1b3105061c0201141806040909230304060503 73
    0x9500b000b2440f400b0701090304000b802240c10260703a003020003180e200710221486000d81008041d10744203140982c50008411060b1014454820b030081500200b00070000179405440f041100744807002d00549000d041d00c00424401a81010807000b58840c00300d1406114a04000c000220303204150303038014021204842c410a041d40c000140c0400803e44010318580e25030741d410100343c4030502200c038000b2501030180706c00d00e0140130b40103180e8416030051400c1e14540d035110041d00c0b5608614002e6801500c2000d010603111040e00c010003608028402a40b2001d02c0c0c94101494000c900c8040d28440e005100300e0903000c4106100070100441c12160040345560220004403000d4082507803144110441008449a1400b6405180581d4082e5503420102c0d494014055807020100c0c1e009001540d811500c0e00000e600d84041c081001c0c6500c0035180050f00080040c109030016008540500e6444000310200015006218440d02e10f11102c4124038800c60410f6440f070190744981e40505c4000800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 530011115 1250 530009865 530009869
    0x90b070212030307020f120909160203070f030801090605010504031e020112140f0105060a0207210803100e10030f02130209030a050a020405070318080901090e0a051b0403080d0b 78
    0x20507181c40300100403281c4918185100a40d144944103082c0482d0051418220340b1290344400c0301c40040d00540000d000351500c0c0600403104203040860011800103000c0c4030000b03a00c07040070f44082d501a984511243d410030891400311030003540f245050100c10001000015040c101121008401034504070302c00d26240010303074400d1115441903003842d14007410600081005180580101c0320541d2010a41c0e0300c560600085202e00c0c180342016074000030041240b180d403030402c00f0749034242c04016804142946d680da003454000740c548040c4280c002c0d506004103e003080c0c580c0d43c00099036004084d8180385d40c894100301c0301c43d80c0010307010720704203950000c148159404a03402108080c0403151f00c0c0e05141803854032041900802c070700c907500b09000710b00880e12a014020410b0104211a061524590b640c84082d0340901d403040e042c800d00f400005040007904014612512428802103094900541c00820140800c003c004c2d610340144010320104003c2c400780e44e03030756540303403000a0041d1103440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 530012365 1250 530011115 530011129
    0x607030e0904060207060b060a05120408040f06090810060b1905040f03200405011430030a26040201030506041d0102180f030c0d0606120609051b01090b0702 69
    0x884150401415020b0208010556000701941800f94500b000554541c0e030420035284a22202000015001e00220391001e018168045d0058801c110f81440c05584082c0203040340c44652025005c140f03607010400c450754091086400b01800c0d20010081e150901c1c1c04100c05000754084203081004090783c800340f4074002d00271a0b01801017010071071519941c0b480e140c0d80312103070307011035050f00362280040c850b1071309090050300d040c0d85404042143c5000001d040c08a10401d9540d10002001c801d50140c804000f50504c0c1c907071114200d800303190381e0800d146026010388440e443d03c03003100002040a02d002802006840d810a030f0910700410642c031500c0c001009000d400c1c040314889042c4002128130024158000c00e20403208200071140c942103102000303206440e003400c5503010740202c0c2e550b003070034502401511a0315108020004407107455184240501803c2402150000c1d07950703600d84103004040288035035400b5444008183ea6180c1c20000f01481c00764811200c0c04000802c3c4c100071555140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 530013615 1250 530012365 530012387
    0x130807320409060207120806060a05070503120106030606140a0207050603090a0b090d111518190c0e0a021813140c091903050606010e01090503030a080907090e0a02060703 75
    0xd01c01d01890100d42054002584030302d000303c44078181800f100c01c80030b014416007032007081e00034109400d1500b10301d400d850950107510111058081013010861400565036907070b0181c42c00f80d40008038581410300103040b174030248442000c04001031144c151440d60008050702500d80c02d4510315103a456182c80f040c50304043c441d000b460002114108802c49900203400d0803200801e40d110400505d8048090b40c5500000c140004c1d1080c1010000d51442846402d0544501840c4111040c03c82c105840880441b984035080b910034820b45d13030801010035030704a216040040c2c9081186000c0c030a0380c150f050040d44d00c8036140550200401c2d001800e2990380062004030f0210450700d010300d0f108804d900700340d10000e1303201d100d84500c1190010280344003240d401a00e605c80b00038a5107403101c0005681014582170b92a04000c15048045420785090002d07004115540d11403c0c0d107410400030b4a0304090058002406052425481d075100302d0b000501c03000760a8041d90389980d00c0c019800c007100d101040c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 530014865 1250 530013615 530013619
    0x607020f2d1b0405011502060c03040305040e07030b040506010f080f04172d030403020709020702040209120604061407022d010203130506010806190c09081213080732 73
    0x1ca001d81202c4001e02609544600301214200440c0c0c1c3c85240e4021109032404100005912900010314490020030040d80c1044c0242041c5003410b90f2103440b4003030ba4004840350300c0000c0d1148103000d0315082501500b40c2000c0d0900323190704010750245004102c1e08000b0302d241008840180894103010212903641c06a0ba47d400560b43d95200c0c03070002000002c02400c5940340904106410722110602d40e06403801280e160340035180c02d615151614019401c9034400380d030322903401c01c0480388580e1050003074130002c9065000352009203082e050200850324200b9850207061031441c20480256070100d509100401c03000182c0400184c9204010ba03d030303c0c0c0d0144400d0713a601c000180b1001040c481480141a4440c2085030240d030f80b514078140e01c2d9102540d10403c80f16800e4007600d07140401ea04030241300f203d05d180c440c4001e0f54402d007080c0b8024050b2250076600310006051501c80c10614048005000110000c0181038688207003500440040107544e01c0307001241d0380c0c03c0a00200e914549005806c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 530016115 1250 530014865 530014873
    0xf0406110a0e0f0303030717150612061c02090619030f050303180304080604080703020c0406030b01170106150f110d1d0d110103050703180506090607020f2d 69
    0x81c01c0809440c03034400c100c500c1d2084100b00b100214901e40041182e00c1900b040e682ca00b00c22a8600c00c65540a101070b10310842d184080901294544882001e0700d005a404994401241002c1c014048002580b0710000c400d04000101030780503840360900b1039000341069600780808541d00c000f124011009820041516040c424004107000000004d58000d90414010b10b03040305910709900d94a10880c401e11000d5045900010046034060b4060300380701d4040e00564000c420928001412128150400c0300c00b1100b070390050041c0b060750b038042100010440020850181071481856a9841e20070140b003c21160700030301442d040c03140c22201482d42003c0200d940785004040007505040948440d074540c43d2182c080c21142c0e10307040340d901120765001040d22040e030508000460192000404490a06031140c1c00e061110802c4a404101140508064605800c1c2104100d0070300f6006001c030400c66028810340501140c0101d035030ba4078800c0b80d90301d6500305051254400f511020142c83e25190b402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 530017365 1250 530016115 530016127
    0x4020c1203070f110706210e0a050c0f06071106130801020706180b06210a0524010506030a0c090504020c011401052416230d0503010e0f040611 63
    0x40d00201860080071251150340340421581d004890014504291203500e07440f805081040034002c865211440070301185164070341d40b09880c00c2080c1c03854144960f00315481002c8000602406102034000742d041252000f00e404100340004145008140c0060728450100a1036055941c07100b04603041034000703603034140082d603a80450303074000e4200d140c0a0740c48500b041c6080558054103410145815842000141a500c48405200b0380c10151201a8181c039078040058950000070002004400e20070001400b941c0d1282c104c510580da5081108211900200b0044c461962201c0035260b002c00040070001381000044400c8035202c0c0c0707981c820750700544009600ca00d050310640001c2942c0021502c07034040e40e40d0700c0041c4041c9602c400e1001ca0900f22a42031328a00415843c001c01400380300e0a150604054141c950102c0c00c0900c07061111103075a5a0141030740e8079818852291160514100103041d0340c5800715548401200514078282e07002d131003002804000d4942c2c0102c0601c02c049042680340c0e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 530018615 1250 530017365 530017393
    0x6030102040e041524030b100806010f0f08010e1f11030103030c140c03120a14032503020306030304050609010219081b1b010305330405060303070c060e04020c 70
    0xa0345014140b4103a0300303002d0178005055070701801c04007180760340c540320520916544540300f803050041c01041c607000c2103200003e4051010801e050103070080c0703841402d48070720740080c8102e4819aa400241c49074100319180d82122008590241c0c0e02c00702d070400112501603203e40740c008008040400120410220021091591180309024400e100789a4010980078804080d545c0e000c0b001503c1e1340c507522038140074880059490240011080a088c00c0c030101c1048a802000754004a07854000c0900710004100c1243c070b400712100d20300c0d0460074114510709080001c0794480c8294000c00340240702c005400c0c6960703442003200495959036010b5515030703c001450072a445511824850304144814085840070441c0820704200381d00041c42d031341807038a030110010b4000d041c1c002c1c203c1c120702040240c0a84140d4880c2100c0300041080504a8944a441000c00044034006001070340071343c2c0107109050003e415414000181d84503424130480c5880240c001501a20842c05007415600801d1580e080a0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 530019865 1250 530018615 530018633
    0xf0312010515031611010e0105090609070e040b060603040c050907020d0e04021315030603020919060608040203030714010e0109080405040609090c0b0903010b060a0f0806030f070e06030102040e04 86
    0x3a4504070398091210190034905401030005403042c40280c070340304c2c4680c1d0300180614007040000d80c0000002c01c1007884498960700312042150340c1c0f12580c01080400c1245c45050040401904a5020520441c109034540b5000540020078160007401e00002240c140703d0b10102031401403c00800b0f512061900d408000e4440e40c014500202040c040c80201101e86418001c5e64904d405202400080500d00032900c0c8604100381d52103414155640d10200140c1c4418800910660110310207914080101c131070001102c149900c040104441c4006100040e46c000c0101e50105402c1503d1202c58426500101c3c0100300b141c2048a0b59032815030700340100414907000e030040ba003084400300880e603918800c21003541d0410900410140e002d550170b020362a40017015001e10140a0000503803a5811004100640c0c09400e000000c1020250b1500040360302c0700180d0780c010800c3d00a000071803841000300f039403544540100c03810320007c440020301e6910250b0548000301000048502d050070136060000c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 530021115 1250 530019865 530019869
    0x90501150b09011e051602040906060e040c080105010b07060c021c0f080f010803250c0b070b15090a1e11030115030c0503010e040204090507080f1006031208090f031201 74
    0x442e0010900f60940744400301510302c03420b0503485e881c0c80c2080a24005120484812003283d0240c0e40710782100100d6185d11450028011024a8072190700b45401d00b181894400d03400110b0580c14400180a03003682502a00c00e40c0754044c0b0b01140c02180084d0a078240440342e882021101902c040407013807281e008944210928507904c9038190303a10380c42c1180794030070780074064101264801c00200f41c40d14085000503400c040c9148a141c250303000e5540e0303601c020500f82e1015004030300c0860100c05001280e00c0250f0003041d58981c036820a200740003c520409402040e01000030390b0fa5645041800d5494101c1300b06135814041046002e40406401c0c0e0346800038002d009120000c8503010300070313502900c10320a0283c2c2c50744491b400d580c03814024003800c1000503c100c0e0007035121451000042d10400080e03001e44200405481e0020300c1504072032a02c0303260401c06201c030382441000c0010420b840d021030f031502d560749011099076480d49102481d00751500e00201c2a8400000c020380c11a81c0e403c442c80c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 530022365 1250 530021115 530021117
    0x6090313091103060d080408030706020403140a0c23060f040314030a08010b0a03090203030d0e060a150b1b060103030341040c0b0f04170a0b0a090501150b0901 70
    0x1849844034541012150510314104060000f040440d905140682210028620801c8420b1030240c45070320090035600301e008200c49164003c1824070804c4010920307420801000c070b004000803482ca40341c9403141051489901344c0c4c5c00c084582440c10003d032240f904840507003d05095590034141d4002c650340c3c3d11921041e00c2600707804203d48a40c12004c41250b000320031981d07410790070780d081505400842e40001d400c10240b541e140000401038a061021305000b0098180016400349034800441c1490401000300060626010800f5002c8040183e490b0503206442c0c812a1906200c00d01c2d550018038066807542c440c07103000d000108240c0c0c075802290044561075148440000014281c40c510384052901f02100440350302c29403401603a84060a034060b000d45807c01d200c690b0386c145047c0c594007000310b00303088807000207052001e807024030301c98108000d0703540040840c0b0305241c47e040c0c514030b0058007116100ba200c203420700070302c0000d4000080034000240d09919480e500c1c5c0c80114182c2c82400c42c030b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 530023615 1250 530022365 530022397
    0x2090d0c0e010605090d0b060f0909030a030e06010b120406090212030307030b150403020409020a0b0a020d09080304060e06070305040803181008011a0a0201021309020a120e070308160203060903 85
    0xc1902807043e0240c0d440554060100f40f019411582c47e41242c080003030100d900b01015030f00d480003d0742c0d298040f030701820004001d5035640d80c014800034203035541071903101141e80c082c2c801089800110130480d00c403800042e440441540743d9241182c06002c000101a600194100d158149140040002e5002d00350300d48081103101c140f1070512450f00e403400f0003640001410f01c4204094145508180c90440c4006c2480600648503480c0f031440350417100b502401030f0b11400c0090880c1d40c05c80101030140508a00030340c24546094802040000d005020b54001d680100700141058001c801303581c0507120480c01d0b251141519000b0700341e6483c11001c92031181241d10701807280c060140311042e0580741c035660f1101083c0440c82c040380c83d40d400040c0d4442150341c01c000c52441e48480c0c246420280441d4980543c0d9378410200c010a40c0701007a000d00003a5192140c01d070703e542800901d610460750301c104056201c61071215030350300c104a51100650075024140070050700c000044014000c0ea82940070203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 530024865 1250 530023615 530023619
    0x30c08070207030f0f03020f0d031a0d02060301090b01021018020f01030515060906070c0f03050f030f0a08040804090519050a0b1305060406032009070f0e0f0402090d0c0e01 76
    0x40741d072040b140c403019000c0c090940360000400c4000d2101240305000b0f004586900c952007001c10310f490700c03c0312003c000076501d521951042d88000e046080b0703894100c505000d4281640c0000da1144818491074001c80d035180b214500c1079000340710004524610800030006000006441e031089100b101c0d08921500c17a0823504081c0d50300170301c00c0e40d02418801c014501842071920034000390382d00912481d6400b82c028812070000420b000441400b034051110000078852961400340c1c50892682484400c5400a10000c01c90f0600f64054904000b030621381201c0c60344807810040c2c0307244900d8000c01c0b071303050500042000317045a0318412035051106800400440d659038000c201110140c42000307a1001c592a040741d441c01300ba802c100d800ca5401040060043d541c0ea866000c0c0c0a5080074289804500010324030f540d241454071b60345c0c0000c060800d03413555140844020191841c2c105090303c19011201b488469031260307410f540c40d449025120300809940b50400103105a01c034854a00c07404481000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 530026115 1250 530024865 530024867
    0x1d071a03091c030204050406080f100c0f08041502030a2c0304050105180306190b0f0d08031b03070207080c060f04030f0f0c14030c0103050108070501140c030307030c0807 75
    0x3124412108038014024501c2502e61401600354250711081c1050b03028400402c590b56036114900c000d0805170002c044510000d52128105039590201848082c030f004c2c01c1c4074065401a00620807031000c0c0ca00025070b035445203885060b4010b1804480380c464030100030050408501d0b031020174850041200b900c0020980c413960b00500c00c50074004021500148001c110315401a030140c41003071023072413000215001c4503010a06d010b07001ca841072000e000e1021500ae40400c2d62041e0301003440199245c4e104c60340458042108070701c03d0310008200b06000000a1103a0004c134241b9504150407010140d81c0e81010341c0020f55504560003617000c140107140541180d4a445021030356550607440c0c0d000d08061454490110805ca00c110a48118030540f00c0c40000030744c040600000740404150000d20383d08a41e090505e48000380e00399074181450a4014090250002102000c540092802041005004240b2143c0c0d015021114006120100500000c690540c002e041440030702e035611015a607503c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 530027365 1250 530026115 530026117
    0x207230705010f05130519051008040f030f030e060906010812130512070810021804050907030209181b010f020303010b0f0a170723180d02041d071a 65
    0x1c162800326030b03228040e2508500642c082d020381944014050003c83daa400412124140f55001c00e0701c0b42407000c410710140c86e0802d902001008545820702d00ca02d010390360310340502c544c00406070601c50060010744448e8400d0708120300c0e00c01131005a0350700b0b0501a4559540f140207000354101c2d4020002240c0d4080301100a8a8003207a80d5003000c44030340d15220a220128044904000d50b0317005d0b210020607000303803c00c901521a8056400181d450010721011000400b00c026030510079030408050019a0000051071816260111803038181c5840e685900042660440fa800e0305070301840d03000f10700a2910341c0d0403020401e4203894150080d0648070702241c40388001d01a89440c680140f00260301c0b00c22940252988040c94103000015900540c07501554001c200e0b042c90000b05001c0c0c4031507111444000030000c43c40c103a6100d41c02e200c020780b03040078000304144000e07018850036158101503643e181c00080302030f2468440c0c4090351401407d0180c1307031411760089240d0100c000c506d0001c4007140720 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 530028615 1250 530027365 530027369
    0x111c11070507030b07090b0a0801082b0f1e0207090b0402131403030f0c030c12031e13060501120302011a0a03020108090c1002160812071506080102072307 68
    0x340c090040d050070f69603038108404010706040f00f000122000400c503082100d00401d80005540c842e0f03003030396240030f00c03031032030181d86000c070b0321070411001d00c03404402120f840081120007003414660409594041d0807903c50004011003d14007403c0c20310410116004902001580d00548042c006241510103001c281d105003a541100d50141c1c0f40c0401c0360391440d0358545401040141a00c0c0b51a030086200345d840d402c034102c02d42c11078000003044000d0300c00400100c10501c0303481d10054198906007540c40d0552070340d1010080c4003484e90002460011041801c0213805034001001c0120396183c03a41606440d61481302100958078048020010495030703c070005000c0c03002054011401d085074011900800d01030702c90030191050507500c510640d5042842d00c103143d416801030034515810307000321100740c03180d034809100d9030013040c0c0b4030300c49180700c50460b890250440700032540c0181d00910000104040c1d4080429948049200c0041000320198000301c542164401c0c0c480e00001c0d1182c544413007840c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 530029865 1250 530028615 530028623
    0xa0f022b0e0c0d030e09010905060111011b0e0609040e01090b01080601051e010c06141b12070309020d060504061a01021c030f0b0603090709052503050406111c1107 72
    0x1030b01c05649030303d82050f5035802c8034803914014804901010102d2002d540a030418003240f03440c1c804018041d6844006103030180b82c01802404030442c1a0328123001c10040400c0c1100b00010364000703140b161a2132040b6511b950000c4c0080003080081c0c8191030003041114401c4541000d08000068000400143c0c1030527210001c1584c003101e2000d4121000c40480a8007142c1807110b1350b0480390100304d491082c031190198500c06031080f80b40c02d00e1804813121002c5090603e0640500101070050800c1591581c010018200040d207807050380005800129a070030024400da0824040104219003504160300c03d14101078035402c686110b1006a84502810128920641d405159403100d1440780e0081c2c0202d00c15004000780134103260011070f4080c0e00032a14101c099200304010080d41d03003d841b62070707031080b1212b52030088000d03084600d0b84420000918542090b84500114040c03090b80e034001804000d6070040d06035200541d504680c440b130b00142c50800603034034160703580070048003400803101d0071a44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 530031115 1250 530029865 530029873
    0x7121b03090905070c2906030f120702030a0c090e12270a0503010c170f011d1e040302010c03060b030c040b07060209030a0302031801050703050a080a0f022b0e 70
    0x10103000c00300803e0000d00c1ca100300320032081e00740d02180440d0803101d0500d01104131140304195550080320807a402411041c000c1d1710542c02c040c02c0304008298852a407100b8403186a07070b08803e000003860300b8030f41c000c043d1505084002c00036010105074014045419445c09642a604410f45d00700c155000d171030090702080310308490701d06006100d000050103811009100d80200c0781c41d41d0101e82101d8284903100c020400440d030820b2100000b40c1e90301c5e400b4046452030090ba41c1003140491046650b5030320803800c9450940804c403c50340100500c44081106400e09540746046d040007800790811890703030800701c2d25102011800c0720449088074410460041c045141c540740600040c600c0e40710f0001900c50a83c01d000c50340c0c07540d40038001042094001d500070f41c6c480c0407420302d030100c0001080055040c040e08010840c0000e4105c0255420001181030038a9030342c1c0c50300e8550b405080c1c008000b0703225620010340c03000542550300c0462481d402c2c20307020f075810300d0a0950322800c48082080044060344 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 530032365 1250 530031115 530031119
    0xd0b16020c0306041a341106040804180f0504080d0c0f0e1201020f030a1e0204030314070f02030a0c0f0501050c120702010513090b011d091f0b07121b0309 68
    0x5d01c150741d1900540c1180034850100380c00056400584046081c0320440007403000d21a80d1554400003890301c810301c00000d0155400d0550ba0b40c000c5100d14850101c0700a441c2d4400c1d4103501c51540b01d00c0d41414280001c0c0036924046ca0080310741e17403100c40c40309911850302034100300045c0304040c0f221458280740c0740c148290b94118200300c0c840b2440c00b1184a5903400300701c104141b07111000598003511350b43e01c0208040c403444c0000070740049410111142e00f48103010400100741d0051454903411164665183c2d0f4030030034101101540009900a5014881c1801d02c07002c01c81030300950021166140880b00515407180011a4640b250781c881030510352100c846617101d25075540042070f03890b2050401a02c0c00304580d030070003590180c81e800001078540c0d50320356414658001800d134504e21914407659800d01d0712100065404800680000980700c2d20003400c40484105130450400780030000211a2100e000d403a2414402d407400d191000061690050708148250800600140c50ba040d100c1e000c0d803c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 530033615 1250 530032365 530032403
    0x2010221040305010e0d090e072708030c0c100918020d0b13020c0d03060e16050f131505090a030323040303020109021e130504020d0b16020c030604 65
    0x19000c440d1185020010480040003d1007445651919000000641800c1d0000d03140504844541c0c3d00c0105054000000c0050a40d80840031070103a80540c0180805481c00400d40b0b8000034090300403c1c46440000344200c00074100040520200d541110b88280c8030003022403c940c02c40c01031041c03500e60381c00031584500342d9400c1e40182204400980000030031180e81e40000c1c0fa250015007020600070380c0020f2210500d8004d001d0401040300c00d0405000c018030b4410312540070900141081c14046075040c0000076a4450f50803501201d080d583c6071501e6100146000c00302e48400d1003450341803d1401000c0307541346d0186040d5141410000c2c1500285403841e10240d581c1100c02098214041d400c1040d00400c0d10100068406035010743d0002a03842450720600c0140442d1005440100411262031043d03a55007410101112562041c08101d588451000c24480b0915080007825104a481080102d50004a8103c040c0d10142e0841e0700c1c1381c0f5141c06154a905040d90041d2000c485942201041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 530034865 1250 530033615 530033653
    0x2a030702060c0102090d0308071107061d010207030c06090f21080a09030507060302070614010b0a0c0c0f0905090d080c040302101b1101020709150e0705041a190309020102 75
    0x250002c0c0d000075190490407400924010300b0101c0031408903013000f0900911580c0141801ea2006112008124031414400e000d40003240c1342092102c6d6100760005901183d00c00d02207840103640c0007030a42c0841b515040c0150209006000300c00c01500c1d041c500055000d11081d546000c2d03036410f841058400302546401c071455128000c1101480f9405000000040c81009010020b0035155401a00c4400c0703454440c0640701c0d51860184a01c68120060080d101141c080360751035091800d118510180500e004082050785500c895104621802e0006000c5403940000d0b20840c0c41c0c5007640d550440d844425074440034142d4504080420601c400e00c01414505244400701d0140d060442442488100001c54801200d400700e580c0d42210200b0100703540c0401ca031030082c100c00c0e58148251556083c16680c0864540304a080c842d8807032020400441c0a0b000b103a02900c0c25000c58807035101c2130362030b0320500e6212030a0322544160030000c04a0341c0b0721034400c60601c075034164050074004a80d81008403030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 530035971 1106 530034865 530034877
    0x171c080a0c110d081f0f050909030418050c0c030307020f07050a05150d1104030818040227010212130503070b0307090e0709030b0106052a03070206 65
    0xd501020440c1c00640d2a10300d81000643d5540e2080300901c00b074040300c2c0400325002180890a034a106d410070302514070550300c03c280e90322544d0421307980340b040d449803010b01001c0d2454100d00e0680c58010a8000000e5464181440480700c80b0a040d9802035072100003603413000d41c1c016000030050000030000e200884502c03404914042c007144448003040174100515400103100380e840000d55102860b07015a8000e5540c46e140c80e071070a0004c0f0343c082c1821454452818a1205451800c2d000721a100350003e017080e1411002981e0840b0214100c0390b4160550003000e6107202498000b0003c0d210442100070030050003490003007410308000454106c0c051000b010001c0044090300461100c04850f52255003809a6603954012a241c507030340c0d08000c2280e8010800041c1c5d185d8050b001d041c0c45105404420103c16081101905000704240e100e5400c2d001800301d00050715042001e029 = true := by decide +kernel

theorem cover : BRFrame.Cov 529856115 530035971 := by
  have h0 := BRFrame.cov_init 529856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 529856115 ≤ n) (h2 : n < 530035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
