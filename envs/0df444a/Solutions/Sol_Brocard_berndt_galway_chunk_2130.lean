-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2130
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:11.495347+00:00
-- url     : https://prove2.me/submissions/3d0cb6c2-0207-4a34-abec-9e112d4a2c5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 382913669 ≤ n < 383093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 382914919 1250 382913669 382913693
    0x6051506091012020d0e060106020a030f0c03180306020c01140c04030b090a0c0e060909030702400c090501050a080f04030e1c11010f09050d05070b0a050403030e040e0a0f 75
    0x20f015800803410244d26002a0131044403d011082a02d03000da0301c0780000ca03550ba900f6800500010904020841800d0042222944041c002c0c6440c402d982e00b8070038102221103d0750301c11603500d6030014440350845001c0c4030300603007031540346100300250a00802c0d815050240340405006800740201044c214841044400354196004400c5c68a05940341c040800c2c0303400c00c803252806420303068009446a1804800c840e20603500409004041d21103c4014922039880e0304d80080c00e500c2261241c01042200c2034903814003150800200741141c0894008002e0348866008034103005040c000302e00c080307811003c2d5540c40342d082c9854034147c0e60789090844181a90003201c2d60440c603040c4200744d1300070201510701d071141e000e0010302140c24940c40044403800c0b50314000c03038002000da940c00c0c0b0081c0703443c80d0080c00703450041d0111004a912038003080702c60b51000c02e86801060002400b082056002010f42043c02d80c1101c04200c00460795030a0354513081100001001c2c00c0701c100d805820010803201c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 382916169 1250 382914919 382914947
    0x513080d1113030309081612060f060503030f0d060605030103030c140a1707020f2403060f0613170d0e120a0b1513050402030d0809100c0c060515060910 67
    0x42e0900a9882c2000b4050503038038014502c0901590940104c580b102ca40c1074002c45008400740d0182c0c00c410b48030700e00240ba0703a4002c84007290720b80780e00103120760741040580624402400903543d00e00950a840b01100c0d40d962001051003024001000403c1d04080741d05e041c5e035040fa098001000d0b0301051a401c007219004010311014056882200a036060000b61550314820b449042106521100b000300300070707450880018120101c0c0c00031040c18410006190040c0b0040c05d00001d210361003000481d07640041802000340100c0300c1c001c1104800305940e0030342060000014080c103451500006190b0f600d0f08107020b0140c4250090405d00c217000300100e60ba81500720f1220403490074031a854030400d034040216644115040c0c0312545400f4101c0c81254011507000b4010a00d0030248031040e29404401012003c07a409031310795102020a09026000f0101e40e41d030358002103814585070410455002a1018514a044080d29030881e1203480c1203441c0e014040f00c0a58941c183c114007114010030118030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 382917419 1250 382916169 382916197
    0x11010b031207030e01080c0a050c0109061a01080112110111100e0105011811121008030a02010b040507030504120503090a0519051203072307050a0b0a0513080d11 71
    0x42044070100901a1810b5403090b56049400d22a80c001150500c000380c0d406240c00ba41040100c2955008900816005081e8000030501103140d4440804171000700900610000c824800021030350f81c070160440c05040101c0903018009501c0c0c0b01c41024044084025060144001c2d0104440c3c0c0104160900340d000b12400b4400c15400d94800c6010308800e03c9840221010b0140c40303880d50300240644804146610344640c100010300048082e9000e0148c0008031540303071004041400c010620081020350308980003c1420f4201c0c01c00d002c1200c000806410405107481c05200010315640c400740c0b0318185c14a803054494507907111540c200525400d0080c507078441c0d4001001e110a82c42c2503000c40e10f0141050744d804c1d105007000c89429100803175140c00050082042881c5407010b180601e8610f1820580d0381d402d143c0c0d1070b600c0b503203010b50920040e02c2c42d092090402c0303808219805101d6202d180c20740b02c00707100c200d07550b01c60f801030140740b01070500d4a48814801c0c1c080c0040905079444540a520 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 382918669 1250 382917419 382917433
    0xf09050601170c16080307020a03030501141f0323090717030d0b030c03010c020c03100c0f0c0602040f260106050a0501050702181f060503010b0403060c14040b04090608070b0a11010b03 81
    0x1f006951443c5065044011a080c03400009081d00301c0303015081c801c500500150003499500722001b030403154203000a0240760343c40044000590000b00300710b0100058002c5d446450030040c1c62140781260721b80c05400310f07016a428803a4420790200955654800b003220104003403c0e540002418688040a220b07055840c01c400840c001e540050700c0040740c20141c0554082c00c1030424000f00342c1d540c0383c800901280e8844543ca070818411404240180d011381401403e1680b00c2d9855007080e192940501008a0281003c100644191483c65582c4003510001c01c0520f191034003080d0300e2a120b106240c18000e020481c1015516508800360800068280490051404140003c041c8400001c080b1600b50300c0c00307010a805008104407416101c0c95100c042c01c29181da5518800742c03100c10a10300400a146017038050360048400034001602c0811001520346042190080403144581e000c5183d903031080d101008000084012200040d02c18a40504e504440340f92143c054225141030307079090302c0f59079 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 382919919 1250 382918669 382918681
    0xd02090f060c01060e0f070c0209040c080303010f21020109050d02041805030c06090f280c0e01170c0603070c0212030a050d06080d092d0f09050601170c160803 70
    0x252209040e05c01580080c0031302d480c1d00c2500740700315408860b0500480d07402c0026401600d45000d159600c180b1400001816984908825085070400c2e80f280070072400d00308052242000300e1074080c0d800c00d1040160f46021880b03400082909031300d441858010130b030856004c015512190491010b0a0f0b2000b00c00301904400d241003592a032041162580c1d1780034a8000c00c0e103c1c1c02c0440c11049444006004141400b0001002c101840c84580d8218010281c1c00d007280c001404444040001c0101b0f0a24410540c0b516a050f06003100c100b02c0b588198100400104090780c030344061320b0b0040070b00c2ca8107a9107000181701242e000c02003140c0050705884040b42105106034010001c2c03200326500c1e1001c0c44655504c5155a54824060303101c100810b91400052052031b030189880003a0801400c0c651843e503524801800b140321140e0049101502d03450014020304545004007500311800303103070543c2d81c0880c2e5403020441c2e210141503140190300005100c01e84c000c020343c0400200380c008c0003803640c0382058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 382921169 1250 382919919 382919921
    0x204140106021501180c03020918070207080d02030f030402060906180f040504200a090606080a1406091303020a06110705010507090b0a08180706050d0b03120d02090f060c01 76
    0xd10400c0300520544030443c06a14244005a04075189640f00f40030924201e01d441010f000d445200c1000c05900380700e000d2040e0b481003241c40c00e01c48003600441c12410400d4000b82000441d0f0000b82d85a8400e204030000d240d030010454150298990342280c490700d491000800f54411140103950280022800c665516842034000c070b10340d0811a0039a00b11a4207400384020740340c0c100e03400362a0403001800e003035481d0800c002d46903101c00020b02c0b080e0340e0354641c00007000711a000d4000c140091440030030805a65864421484101e8110012450a1806030700140684c1c0c0000c010348460300d07441401400305402040000c28466008000380115080310080c0002c40e000580142e8080d800c003408112880d01a5115000b5142c0c1c10380705515040c000c40090758001700141400d80340c0c1f6070b00288a00d0b561401e0100f50054529540c40a0365082c040f40928280c13400d01011038032036084061407542c101c12440848004100c101b0300940c6596a28002440000000d0f00c807581003100010f69500880d01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 382922419 1250 382921169 382921171
    0x70201030911040615021c050d021315030e01151a0a0c0501020a2d080c07080904090602190e01092d0303180f030c0b03041707060504020108070507020306040b13020414 74
    0x15407c40c0c512481d00b004049071807810040010100c0d40030071049803401129001031450616440d1240100d0b0f070345801c0c2c0d10b00d00d0001d1002000003952006460f0400400f030040300d41500c00780c4c0801c3d900c0c500300b00c14071500040d041000a030303e00b00010800c032014050190081d1840d0003100071034a80040380b4000c1c00091920401c0c41404001c02c20150304080741110740107050100d030b52003180c80c2d5580302e580c4401c2e83c0000004d0301c1080c401c1c080c1c10000d9031a07000e4031300c0561040c5009a284c003484402c101d0101407615034130041c0400d0301001c400d1070b42d200105404860000c5004c00350042c108580401d0b10901000007194504003610110515420108445148075810208003526070781e1002d42400c0e0400c0d0100034020310300c4920070051840d8000246030440d000340d03030442c0340070032010440c8809e0f44a92400c50b1820344840400c001d641e00920703c0ea1303120300141000c40c0f4102081d0b00082d11080001c2006000e01001700101d613203000e06048804041d03a0243c030820851098030780c40041a20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 382923669 1250 382922419 382922459
    0x1e020403050a02280b0d02070c0305010b09160e041a1917070501020a0f03020c06030a060503060c0408420108010f15061d130c0210050c0702010309110406 68
    0x7415000842c80345a1040f04c22180c0d18400c8000704072030306207524a02d45500c40c41d8210003d1f5001d0010070040b808403004180294440e20001401e0140d40040c008819801000302e000843c00a0f00c1c1019a41c00420482d110307542264009140c105400d980ba040701103262445800c59150300c4018060248485014265003450a98901030303a041071441f0350f9628240240d50058110004110004401440c07030b5481611a0050b14a0b01000700017003000c0e0b8008030f45400c60903845410400443c00d007842800e40102c800900c240c030307140c2480800d999403003201131b0a40811441c0012030300c0d40b070303107010038044846c90fa5144428500f01e1710700450030a500c28001c0c071400d07520385142c0703021018191090b113802c4028680074601c802d180c11030980708140184008804244500c0911865503189108114015036000000aa05504900003450041d5005c8a0f401e047d14000c01e2000b1054010140c400c190780c2413a001c6903503101448d0186284110031009078100341441d602063340300e500e94410600e10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 382924919 1250 382923669 382923679
    0x220b04121205010825080d051306020d05040605031e011d1006080726011d060a0303052d030f04120512010e0603010b130209190506040501031e020403050a02 69
    0xc205007064800c940081c403802e04954802407004002462400e09001204140c80c031181e0713000c1e41c458000b42810301700010a00003a10000340154000c0000424a0140215200030403074800d10300d902074290302c0b45010780004d000b4084009441124104502070410165400700381d080e5a503100c01100c1c510791070300d06148841e196400918520982c2600000700c0d070080c0d88600054944c14815680600d140500124140c08400043c07020342c4449070180c028039108030200e4064510010007107400030301a040a01c1404040ba0420101c0e90140c1554071000381015020551340400300c0c5141c0c0c0302e045400d103003081840481000144415090500e20890142c1130301022a552404201c40c0f40c0f18806003003803035070070b100c005015040c7c0040312941e101d0030180000820380050000500e0702100e003800b0740010f039000a00d0802c181085e000c003080b10381d02090565011420680001d0041c043c0d4040e944c10940e0320926a6140e01c422401c02c220034514103800c541d0b6a449080c046c1e00e5640e680c00c164090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 382926169 1250 382924919 382924937
    0x1d01090b06010320041a070b0106020625140c0a0b04061b0203070f030e041d0a03120603150905071a09030c091501030e030903070617011d220b0412 65
    0x4080700c0e90070804d01e4042d1001003450107007803200f55001030000c40d0000800240c140a080005120001c459002e40f20341e03001003c0f18504441501082520f40121022540f0250002550f0680181400c01d030030000c0d00d580c903203800750050315a02c1d0064007280944107030111824003040c0503080d44800c09410422505035102489100140e980e4480c40c0001080140c80c1011040070900c10900401322040052005c1066000381d03040702000b15060101c0242034011a001c24100740c0c100b0101c002041c000d40c2d040c130810f4030f140c5504424100b00d21841e04603e8481e691a0100501409002c010f041e1410180c100c9000d4144680c0321508a6586ea6009106400603020760f80ba042800c3c503c0f8501494080f030b0350310340840c0110040d002c20001044c0507c42400010415175082c410700002d80a680c0d03034181e0603105800c00e0b485040c4180d022003045c0a4440304510000000ca02455100e200802c00e05010700c0ba0b1078401582414080c805800105900140070801503081100e40c20705480c2c0c0d95800031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 382927419 1250 382926169 382926191
    0x31b031f1a0d0209040308090c0a06030e0c10020d0c0c050916030515060f130503010c110105060f0d1b05030d090303021608100c18030c0501091a04091d01090b060103 73
    0xa96101c2c001c010707600418600000340020b1007605859030010111041d2941002034001040b84400f0641000003c251034102401d800d0800b00503c0141010440740c066041d8170728500607440d06d4508500301c0412640402080c140040070003400001c3c04083e021030390301d00d000c03008440407850440f24400003070304003000f045002083d400c0c1d56a0391034004040d58a00300b81c0b4268000554800790012001c490307101d000003201d85c0c003031045840000450f26407180c0804a01c146900b191001032205100e0654449440401d8648410305c004959000c544061040004c0d2082041d400456001d9980f51203448951024554800810b8040f01d100f03400300c4103081002050081e500003075014140d440d51000c19205c0f280282a0442400703d000c60405509003005641a85403464031600141c50440012904111550348550f400009040c06c185070000c001c1948120401e41c031440c40b80c403540c240c556074548814038901603c1120809a28000c005d1b410140c903141ca41c0b80c4c3c08803030460200e490000740f140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 382928669 1250 382927419 382927429
    0x209011d01080106080c10020109021e120a05031602010c0b0a0606092c07090b030f070f050c0c0f121005060f0a0605030103080a05040e070c0605060f031b031f1a 71
    0x1c281d039100d001500500c1251b03001c1c80b030070b8408105c0d600300310740d00d5102010244c0c40d000503c0c4c01d2568041002000030451606200a0b03400701b1f840e030511a400b040d4003801140011058801011242020840004c10b43c00100e400b60f001c00000340032020b9201c00e000b184503450307006104035445602c44d00100d0381d58007000b0b0780d41c3d01e0312450f010040200c9400c00e6503181c4e94581c1d099000c64181041c000b500e446210003401c540007203aa11461003415410f0003c0349812100b0f102c943c003142e282c03007841c1ca90403a01b055200d00000c881640180403a9420031407540e2001c1c00d101d00103401c030080321054511080040080e02041e0307803660007480c00382c42ea601c072400e010032000240e60490f11290b180d64078541d40e6984681c014880b51701001002d00010400c03100d80c0c1c003a140650101c0d914501d00400d0341c00c001040380d0003d44842e201e410340080f181150740f408240b030700502c50140300644048005402190901c80c00034141c00301700c40082c00e140c00001e1254081061031440b06108680c00e85004144130b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 382929919 1250 382928669 382928681
    0xb040b03120c1b0f0909120c030403021201050106090909020d021002010b01030e0c0303070b09071a0a14090d080a020114070917010504051c0c02040609050604051b0f160209011d010801 81
    0x50300031040005412035410314a18003034106c1c0c2c2000c00c40c3c84442c002e2032020440c2c1c2051f081c0040c240c100150401c150300e40701d03030b0322503080c1a544001c0203a5454000d02a000c2c0401d032040000c8151035500031410345d031f6940041c0612076000b42c0031107404418998001e008040c42c0041c2404070b86000400d0041c3e24001540c2c6e403424074058004d52800c91507441d41e200c9210000c0600341d207841b80c010080b4081001081c8041042c4085499075218510440d01502d1400310590041e00d1040c1409a1042c0382e0710b40c0d0310a0390135900709800302d545074081041240500b0f54000360619034a0350206120f4039660140790b1104440c103040076030907280d502c00109420f03030f00150703800f6011750b06c60b40c0c0d2259100c0c3c51005600841000d8207099440203c1d0707602240580e00c1c03641c8100c018564480802c444c0d800c2500880d41d0044509051401d51109070b86400c0f60f50003501ea005085400108510125000f0f503800c048a1580060824050350f0351100c04100d03c0102e0368120303000d43d07a04000015034030b0f014002c0f8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 382931169 1250 382929919 382929973
    0x20c0f0604030f0e030c03120a08010e0402030d03090201170c18010e060a080601051b1c030b090a0c260402041b090501210507020f0d020a0c090b040b03120c 69
    0x4601c80d00446200301e0310050030750300c0182d15020f1b2240003401c82d58200320700902400e101c0d01850b02c07151413140107080d50b00160301030707050581401c0030400103940100c0c0320f02e05c2c0c86640c10300242030180b6000407510f680348070b002d80e9640a240000e000b81c8002d2071014280c02c0c01030414403581243c0350700045544050700d0140a8200c203041c00505070060080c040e45500c4001854201e080c0800030b801d4401400c1150034401041d0055802c031401c004000034018095105824207005032403002d03002c82c84110f40141038010080d664412641090b200d21819164204014001220070202e01d00c095100c11050383d04070311592401000200c50400da421162065180e611b40c0305045103400c006498191441885184012100b210502a105503108440c00b5aa00c1c0d4020801d031041d82909515254001541d2419580214841c40004041104980a503031a80341c021540f8030b4a071011801a110316515143d1501441d06a003421900c0c80000c2e103403460580f01250a4034582d003035a03100b025096007c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 382932419 1250 382931169 382931177
    0x90604050d0f21021203040819020708010905030316080105030a0b041a0a0b0a05091506070606080106030302060a0b0607030e0603270c2713030203040801020d020c0f060403 76
    0x801161400c0022222040e004400840d00c00d2501d940e42c1d0b80f0081c408803240444112200c01c41d4680394100154603540f1000004a41395091a40b9038950074003c5407242c6500149181c03004005610034440340c402000800d0007400701d41960301d0425202d400c01c44075680380350744c0c02403082e924920440c0001e0407141c025003e009000055241c450038150020000d5518050030003d034850107040d2406548160051440011039409900030031000c0d200303540c003a500c101a0300c07044c04006401c00c0245444050308455143da208018036140000e819503a00007006546840740000a01d078000c80d4607841207c190070100101064407040068034010101c019002441522900d0541c1c1400300040d50000391020b030440301c080709038001c0c0320f6480e503480303015401c0e4111520118250409003100700304c403540c410b5841d40910b2410300d50f0001450044c012226500c8600040050500134011600501001c0009640e542d80f82c00d0316038080c2d440b003080c5207518820380c9400440320f007010035454040c0d40e00d951 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 382933669 1250 382932419 382932427
    0x1404020a06120212310b011e0f03080405030d11060c0919090e0f07080c0904020d060f1a0117010e06060409021803070f0b09042d140703020906 63
    0x14080b1002c0c0b8200b5402c0c0609035007008884102c881004480d44181c1c80300302c0908001d42c044143c540086100c4030080c03c0d40f04410070550010b055180040e040d6603c110040102000b803131440640340340d10703130b221a401e4003084001009002215004200341e0794154119006031000420455044401200c0002c2c42c1d0404004540003580300360040c1300d4007100402e0100d1422091080c142408d016520100f01c0035911300d2500b08500e01400f42c655032a81c00400791180a2402500d15120082503800504c9401d544000504544c4d4000c1d235204581d822002c10044d01460000013002460001780b20b090310912a0160801984140032410540035000c400003030513481c4c281030061158029000302e5200c50140b0000c030b03187da42c80c8080c001c400008030f000d4155905c640245030421210360003041000d00c005005100300c01c1c20104440e0b11003002c3d0703400113269080c01410710700542040d0003c2c06034a04840300d011028bd40b9044144680101114040c042d212020700358102d100d01d01d0b0f0a0342080043c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 382934919 1250 382933669 382933679
    0x10803040f14150a020d080601030b0315060d1221091505040606090f14061914010302070f0302060601120b010f051e0a0513050102030703120207171c1404020a 70
    0x80b10a1000400c00b41c16440000101072080300780d82c000c1e00da8030006070300c004000c0e22011381c00903103942c12040c04c1c00c0c204040c2841c0b01c003207a00c8214240d036244032803200401103017071902c58400404074245c11a51050b92030380403c40040c2000d904421204406810004800380f186540c410303100d4056000d00d006148285900109014000082082d641c440d1b8a000000d0100d40780d01031505004d100942c0040d511000c8110700130341d4040901400e01034a60f01b0308840741804261541415164280d005000748490400120003a01c200e4000400700340581e1024400c054001803010300a01c4244c84070000e14082a200404480310381030140e0000c0e03000c2641c4003150380100002d00c000f20025042da41ca1f00204d43c0b070718505900c080d1410700054000070340407140c60344070301e00200034202c01d2010354036007852900d0040c00b03181c0c00049081c4440e030000341001003026000d00c15040380ca00035103c07900c442c01031030204101c49007405900c6204d4200041d071258542e882d0b0075079104076402400220050300301 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 382936169 1250 382934919 382934939
    0x9120801060e0f0d021315051f0203030423120309010c030e0d18080d08070912030801091a030a0506060102070e040203100c02070b041e0e130809060d020310030209010803040f 77
    0x1144040c3d1b0010709418921410503424020440c800546240c00c0150b5031801c81404a00c14205420b4101e02a0301c80c010856a0342c04002c4980040e000502100c0072864050124016905440001c00714803d8254080c0300703402040146124081c060000c1000c403010781c030190160303005c2d90321441c502e130070000070350301d0286c060039504510200d2180740e00c1e105030b03c40c0d40483c51304000c01e80c608040b440c001e040080cac05500c000c0c003001a14520042040301041581c016220400600460340b140e074850a11050143d91080c1d400600113000b003c540a03c0c01d1424401c3d1600c80c190b070b80c03034014056030741c0c0030801c51050414640246c1c1c3c0a00244a6070340d5a1404200400e9060300804c2103000340c0d10b00240204541d0080c0001d401c180c0190a5081203810629800f210a54011441526108100130380c2505194040039160b030040300040c0d8900440b400112244514900405110b1012003400001904110b698055a00c20f845124107641c070307004001d9407070080d4428000c20100c0054244681c1c008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 382937419 1250 382936169 382936189
    0xe0f01051e0d09020306130b010e0703022203030813080d050702240109060f060507030e010e04061202090a0e0a14070b03090a03080c090a0e0c0d09120801060e0f 71
    0xa920701c41412010000348100030380c80140c40c0302a5584a041c0b0301c007546024401c1681040384021110145a0b00b9a1200b2a140051240904503007404001450103802501228520402c42148c562103145a920207005404240401e8001410400c000703038500400c8081061026009090f0608050a84a1601c05010000d01d004114052840340451380342c003070051050b0b10207249924006030b40c1414a0881156040e1b030015800c40c0014001700b1080b9007040c200e540481d01840c007502011142c200581d12540780c103502c66040343c1380160014000d82d003403000c07450080c4212000c0c00e00d9100d1408102c00e80d000e001850000c0e41008030503100180141c15840802c65584054440c002c0d074482500e49550002c4031020000d4011040280c20035a015045039406130307003510700c28240b15001c000301d044403080e0f02403002c000524401140518464409599509a01a00600007030799540f81c920200458442c510780130403801000400c0280c000c1c901c400418401608150b5403c0500c8208004529 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 382938669 1250 382937419 382937437
    0x20d030209010e190819031806140d1d07061e0509130f0524040603080910031811011202120408070609050d200303091c110304030b1005010e0f0105 65
    0x48040e01c00103604109100076003180c0f901b1b0792408030494032810054000f070740314803a110080c07002e80f40a01503240c20101c20f54002c03590500060710b4281664902c0020f20b20350000c140c406003035458000002d40000380740e2081da6880d45c2c42c02210307494003108000c15040c0118000124505018600e00c81c04c0040c03078541400480c002c082040e40021442c00120341c42900c0300908030841c10140240111441682ea0b49450207803010001c0c0da02d56119610540150241c052040980d1581d5a0300700e8406c4d000441c1c000400910303440940f43c2803804403000341035840c40340e000c61000380200020840707c2c400e03038000b401c084108482d10353b1181e488240f2907200d03c03000c942d4540c0c0c880c80c01004c44d00c10414202400c030311762074080d05e40b01407070341c03030218480b00503852103c942c0b081003000103a500106030301e501d4a101c4401c8180354464a4030556804246800c401083d10000c00c0000034860302001c1c860142611031040c01e205e503244c00c0111036003451140c03002d401621364202010340f540b0074401401012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 382939919 1250 382938669 382938709
    0x504060e010b0c071805240d02090604090c0b070c0e0c030a18050a0309090e0d0c0f0c051c03030506270712060b0c0c03010207051c021219020d030209010e 68
    0x58171380c8905122140307118904030416540c2c1003040750300e082141648030300c0008070038040c8110309a40c00240b1200c43c00c010080c05000c80c14081299621260451b102c003590041d2141c2c0003584450080f0210f800402c015507662180000c0061508904a219801200058a114995501da08200c0041c002000040d0140130506200401040041c418007081038031955a0141d42e034074100000c0c0c15a4a1183d04c0302c002d4100c625036401c0c039504090300d0710295a1042e0280034080c050309110704045115400150400d010102102d44c00c100c9040031080103100b91401c1090361582e03c1800540081c04070021030748800e049040810a0040e0016a4808a54a0104403801d000c2c0045c10a46102d5408041030007000300b02400028800c0c0001524a20180c0085041000c180c50b20351b40c80340395841818a0401130310039002c88610030301425401d80220804d4075a40c0d0042220804200c01c50382b000720050007020b0402c000c2d5407084c021501100380594444201c40355101c01c00c0b40d070002900e8503000700307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 382941169 1250 382939919 382939933
    0x30c1005070c05071418010e1e060303090d02150703050a090f14060304050f19051002090a0b030c0403020409110102010b1909110d0c170f01030b0c070501020d09060c090504060e010b0c 81
    0x1d5846c813615000e400c4000c0307803505600b4038084940108200d4024403400680384030401480c0d460000558000420031119021240100d00201d40a4040d8000c0c84040d8000000e00e034041c0b640080040c020809170707a4422050f5070307541c004022500e201c0d00840c1107440074142025228500440074580090242c1d066038190ba650021641c580a010640b000b07803000060240800c0c803a050007296600185860150303e044a0100010300d50012030241c02820f00b03011000c02c5411214105640246501400400801c500303800c0c1940c2c40a05414410700640c240442d03c489810030503200604c007030010381a445030901b0004074402811001c1d084405020007401994020480350049940003c405c0e21382d203410039014a480c8075148401130104141d104620010000034010365006079000388035102c055103616041c80c0c058003920030101a0030000b8188203114040c80021b40c820240c0c5001d40d15440001587d40c030074041614518440c8414140341040108426460540113001c02003440c01950a2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 382942419 1250 382941169 382941199
    0x50c0406080c0919171b31020310061b060f270c0f080a020906220c0905040e0a0f021c2105120720030c1005070c050714 53
    0x650312a80c0729849807882285040080d682d106188450444020001e4141c02c00038186142c5492102403406004083c1d003100d000c0f0034141004561000c04480100e447e0300c6005912010180d001030350074140c403419100002904a000380c500c01241da20b01108400c01c5040742d1503040003884558031301c3e41001c0d2502c02e411700c082540140c00c00a03125080d00d100d03101d0818141a06940d1054103c00c002540c402c86c2481800d00014110181d240d0488aaa49682c3c82001051400340203418811319880c0742000c004400460382c0080c9210780f0159240b0201c0e990300c504010036503522035a41d2004d42c0160701c44002090324201c1041b401800908904800b602c01d40d004200060043c000340d0300081229020542c024950f644056401e00074a03120b410210102d510f45070f0f54074040c042d0410701c18114007091207035070f1041400191019000549854070300200c481e40d00c542801d41c88040040c500400204200d002307828200e00710381c0180007009094108005c0b51802e0800000c1c0590107251040c00e004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 382943669 1250 382942419 382942429
    0x40203091009080f0c1f111909150201020a0807020120030c070f0b01081207080406030c0212040602031e041212110109030e090601020a031209020d02030106030501051009050c0406080c09 82
    0xb0017200088014401d054449150002400c511005006000c0c10106142c2e441c4a862041d104251404907400701c25032820281641e803c88580e010304810340c142050224415010340c05408441580e03201c50169a581c80e00803800c880482d01800d030b1b5400d040d12041d8400c4854030203964442a260718583c50210755899051201222400807a826035142e00103001646080c4044022400d140000c07a040444680e034041d41070140e402002c0c10181d80b035144104c1c461003000f11401807400d03d200143d666480d820002e490381e210341c0c9080e0003407080b040851021200401110110790920601d4010703215940e031030415200a840c88142007015902450382100420701c41c01900038440e445001e07040380c401c03080c00806d040c010710302d034195080401107030042a04800504c0401d00e07810000100c0c4039076480014204260000040c2d01580b038110040108031055110b20700540c03100907921140b994840300903080c0c070003c6a4103001c0080c24001041843c0c080c6640075005088800298102541100421 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 382944919 1250 382943669 382943677
    0xc120b0a050604030605092112041a0703050a06060e0d3201050114100e150d0906023105010c060e0307150c030e0604230f01060302040b040203091009080f 68
    0x80c5d00184d6842c18400348100070070a4074520400000348603207851f24005900894001c41e51a101810403040026003088030f060807145c0c215582d100c0c841c001e0706042c3c074010300404046a066001906c1d0000104855014850490105074010020350110100d0382d1a4401c0103d80d09a1404904d101010074440c02d0fa03181e00f0001d81c04010700001465072515002039046008111003900a64002e4000c1c0d400940c003e91034905c8070410741e4540200100340c4039010441c8901c06c0400441850300700e024003080030f01e4009015800c06e4004851111011084404a01c940b62503502c2c074201ea43c2008000c6540911321100400c4c2c020031001602e84050f550060a41e40701d140c044442200c4c41c0c1c65420302180b01d00c02d0a00c0540c245c03a042011b80d83c0400925a10500030300050700c0c0071320500055448807c5072400384d0b01c4500242c10341e000b0440f25408140a400d00740822403049081144e551114101482602c1c8668101c80080101d590211640b0707005081421003035403c280f040220030b80b4444004024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 382946169 1250 382944919 382944923
    0x3010b13170c040f020711041a060c06010e0603060105030a0312090f0501020706050a020301121509080a08100902031e100e0702031209010b030c010f020102190509010f030c120b0a05060403 83
    0xd010382c02140000c00040f41d1081aa80e000c072803040c84090301094502c50304200c0d110080e50002900c082c1c0700400c0c071040890191143c0d000310300103171400700c201000c00e40342d040340c00180d032070740841d1540c80806841d11004d026072901640000604400301c0d104440070140001c0f1312000268080140d1540359141c1d0309400c050b20142c0d0002003038010000781b40304060b403290a20804605650600040f0f40241d18108070143c2800d0700b06604040c054025404441c0455028200039030ba56030069014141107000c443c04140262400d00010743c0c40030b1802228841c80e0504810b40c100610748a07030094501000d0400c00380002d00141c0410400b00507a446070240d0066001152900c00a2003003141e00d810081c8102c82a0b41030034074001e1141c40004c0c62000000003420603040c0c080e90480201c1c028000e610311003103140c3c44110f0b1012641c0d0000d00502d1800320a90700d01c041c115442900b64142c555881c1c0b418001440d0b110700b0301222030700307601460000c1001002021103e9480000806540042c0c00c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 382947419 1250 382946169 382946173
    0x90f03080c0d08010312050c15011d01060e01020a0314070b01060e1201060807050105090105130f0e070507020901151106180106080a03050708071a0f0f090a020603010b1317 76
    0x94a000c4410041002c04142601d4502025070450b99130800341c80c0500c440c142808808104041202030601001d86040d50601181e0803c1d031f95040c0340c40c4400c03181e020240c00030914070004030795940300d0103818684010680081000030f0460380d04590846441004655250041c00030780000740c06c203042c0c14000c00e01c3d0758450340351901c403604000c500203002e1795004e0540e140203010482d0350320101d542c4081718030900342141c84054620042e902803185101c01460710344e13420350220b8007940b040c0e4000709803554001d1804255032052000d846603c100400070f5884440380e4010400d0320b00290801c6036400452030300c81e400040c210b0308145001802e8541e003000240c41403844042c140244181001800040020000d5099a44004e0038601c503140b80a044540000b490009205a40b15041014140c00105003103614102401c1181c4000c20780350305e14180007240104500b40000603980112503001016189564646212070003a944261480346500d8008040001c9060491303103144d02c480a01d02c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 382948669 1250 382947419 382947427
    0x20309101a130c020f0304170c04020708030f04050c03030d06031205040f0e0c09060408061005030c13051518041a010e180a1e0605010b0304050319090f0308 69
    0x103100c8040d541818040035054620701c1a1068070303a81c800e9010320390982e44000080c544078a0034100d041c000002044c0c2d09502c40010f0020302841c641840740183c48080c4142e0b0511039801c81080264810501c1c003a01a0340b013400070a0216504141454000348504202c03410413508001203811904448620f50003030f40d0b01d0400b0400c0c05141c04940082c101c0342c0c50403a20b082c0c03d0a14084809825000b200c4c600d808090002c0c00e1401120200e401c3c0c900014407da859aa60708001e81d41e41c41e0490f07110084190107000013540c1c0c00e00055155030030300024003603625031000c03034200402060000c28005402c038401198288940f652180c918000040c42003610701071420b4141310030000d1528600c0018440040010800320488544180d081003040320281034882101085a1402071480005404802c2100e03000c02d04c090380403a60720303465106150600050381d884201c1001400f04540180250f00200444814040400c03842c10b24441c1340e050201703006071514000381440001d43c20403298400d00103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 382949919 1250 382948669 382948693
    0x902010206011401020721020405010b0405040c0c0507051c020904120f0e150309010212010b03061804020310090515010e07030b03010c0210050702010f09061a01020304033201020309 80
    0x44807041c090b2442d18602840d4607030340e40000395505058424a070744820100c041c1592180504850000560014010b00107944c4401583c0400e500c40d21500c0c2c410b618140c00c0001e654028005141d40c25004406012400c0c51320b0180f01c00840b402c500000c114a040142100580d074440c981070146000301089500000f005c107000d0402003c1d01c2c6e03d03406111801d80071002a0750303984402c00f4240c1d0a201c88644075200c03400d01601a00806101034040f140202c004104080c142002c1e40c450803080755140c11b948c01e0800007680000003070718081e402d500004900180c11415410042241c2d100b03400716403241544c800c0807144d2203802e8200c604c4c001c01480030322580d86da043c05840a1381500710000c2004007980c405c0a17540b1410309991002c11601c0318009060a4000c0d0712141007054081402d05c2000e0b030328038000b402000101c07c0040003011914581e9582d510004c00d03181a01c3c0c3c081c0d24901105000341035690441c0885845141d00340340d540c4009804d890a00255000e40707458802841d40302e01d10303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 382951169 1250 382949919 382949923
    0x1090b04181128061d0306070309021302040e1816030602120105060f1812010e030304050f061902070203010f1a030106141309060902030607020303071101020f0a180906080109020102 80
    0x400c00e600844080c108003407000080801c00d01080702c6580c05e00b0700f81101c0c103400c13407211101c1c0a11145d5060281c001003100498140e008403c54910845001b40651010180c1c0402c80c055405003511001900000581d030800001ca400b40c1d6a011204403801d0184007401d0702d061103680d4208a82c15900418200150302c1028000b80c05000308480d60360410903020034606480c001c4489085c1000c10750001740c00c940c0c42e200c03c03a05001908030001d11507400030301c820564a90040d60100d50700e200e1402040c446c1100450018005c8041c07039820190321101e4051100179403c0b032402a6459560340b0511101c42c1e80900c40c10300f01143c07600d034660b09541244101800c507003280d486911089807a03000100b10f0b0340c3d00d8844842c0303c1c00d20b46002035a25403a04120005002102c3c000b90107104100c14002c003240c001029501c00c280d6640d414440d90800c14074242030340140302094050500074001c03c48182d002d00c1e000c1c0b6100c000c85074151001590350848070309030b51540d1701400240c2d40d904416011341d641 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 382952419 1250 382951169 382951189
    0x127240504030f020d02070b0d021803010f090314030609010611011514120105061c17030a140106090b070201030905030c01090c061106010509010302040b011e020d110a030801090b041811 82
    0x1ea0010741301c400d02e03084801d24107104480005212710b50016114070841601c2c10180000071000c1c000700a0340b00c00f4180d01d8001c04a0244c00c0e40442e00342100500d411038003508a80c0b04c1c08000d0720448050346401010f80301203c040e49080070f02d54031906034102448081044100414030041403000700244c000521080d00f82e0110101c0240e414807040242c40c0d02c41d00b10281c0c0d541d460640b800860030783c6040031000ba507042074803412028800420300410907529000310707415000c0494080401e0341da4074402d40b10389803944203442807954240303d29400b641c040c2d845011304a0240050b00d2918040d24501404c48059440c00c940c840f801e03101c11310000da8014035038480080600010700165060000040042c003051200074403450300d5108034003440c5d00c07500140708c0a07000c0c07104141c414032465034041d44540d01d8210040001c1c2c003442c40c46030b01c1240020121083d940603122a00180d0030000200c000d41800e03012580c020380c4940901c2064015041c07116981c031300490110b8007038001a402c003d80c1d111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 382953669 1250 382952419 382952443
    0x1305160f0f0206012102030106030609110604030308010510111606020d0306050a1505090613031a0103020f041a0d290405190215040b0c0127240504030f02 68
    0x201c0d01286165800081d828191204148210341c80041480c501100390b02281009405508204001040111a400036a1f0b854401c10403040c00741c445070280000d45c0036038030021740052501070042106040c803a0315002854040d261034000a14100203540c03420407140c4400144a218010800c109981440034000c0d03c6503d03d028441c051600d00059209540740c00b0b800080d600a42c20700b0f594500640484005a4001c2c0141d80c4810304009002d030300b81d855110603115911031000100c01c03660749480c1c0c84d060301e60042c98240400300c0181800b00418141480308480e20079940e00768019540d4850400c4124442e903107000080c6c130308101c2c102120f00c01da08410004e0301900c00740800903001203191141040034484002d10002c881c0002032810485611034000c01c40700003404a10004240c0081c00198010002401071068031802c2401d43c01d01c0c8481c00c04809a900d02190001d001780402a402c10004da011800140d03900104d003044900c1138030120042108040604c0880f41c0500468034800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 382954919 1250 382953669 382953677
    0x603010b041a0f03010e0d02030712050a0804030c0c090609021c09030905010c08120a0b3313180c020f06011206050c070f030305060f06030103020607060b1305160f 72
    0x844886140120041480d0b0b203680300e0078048580c556151425400362101c4003d0804592a200305500e010707440f80e05c881c1c01074900300c0f0b00c0d040c620117460081c4226000407041d50f81c0c000742e80d541c80e20111707501e000800045801e2496000c000660f00d28500a1801905a071400140d80700e040c21481e00c1d110f40c1440060f01d0355030400b807840c00440c0d0049440821100e007800e00350501c0310540b40110300c0d0320660741c10310100340d80d140c14010200c00e164401000400181d680a000501d408026500703003c0300300303509205820510504054401c3c0001800d1030310240e408403c103050300e400b044200d0a441c1c85107458081e680d070084000381e542c10401e088540e04440080d01042d4180002d450f001c288000000c0c1c12141c580d0040b074a0b0105d17100032141c0032504260010204030062074014040c10b01178415070722452200c64000340524101040ba8100c0358003d026038500152966080060000103459580c460045100b502c010030b12406041e11514081c54074105501c0142e001034030145002e01448204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 382956169 1250 382954919 382954931
    0x30106030b030c0a030201210516141804021806030a021305090f0705130b03160e0301020a0e1201060b040f090f020c19020f030d110606120a12260603010b04 69
    0x140c55504141085d25028a002c000301501da40880788013606028440481510b410104209416100c103400d088401c1580c540994a0f00000c0c0040a4011080b194201c03060181501c50146010b6005140400310840600505a107023000a1501d410844510f1082c07600040c0041c11a01a1400c42024080032100389045043c141b48240040b0001031603d02400700c005100c0400844400c1ca140050000e1365609a4a180403a001c410300b90500042e500415012403c803a21071078113009882d014104c03660b03801030601c2d6010800100c000d490384502e005542e00c8501040d11080071006001904500e105815840c1c0782000280072680001742018038a481401000300c10749000c500940540600e04850040745854000240c2240c05002419070520030903040002c51900f00000841310040e00080d924240d40e280244501182c0036025003a140c2c01c80b03405200051000c040007a07070711a40f1300d0031090700003010010741da2040c26800c0030606060034130f04201c0c80b883c0074002c13a0301d0404d059406000d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 382957419 1250 382956169 382956193
    0x6051002061306140a1b02010e0c010c141e07080a0206070204020901030f0e011a03030424050702100905030c1f120b0a150f0824030109020a060302030106030b03 71
    0x158040600700020307a150740a442d00c00e21940b50003c0c0d481c0070310041c44948078100300f000400100306003075505400c2c01803c0007442c03140d8018840d00391035101c56030241c405908000c00440c0c0c1d03080d00c1e5400300c1e100f4544036100440020100040c0420b09103580c042c02284650f11005860001168000c4540d80d00145100006803240c0d01603684490381520096240c002540040c0c010f000403210851040c0d103458203162149805402c51200c02071501202416003100d081810f89070701c41c1e07006a95a5070a00f85402c038205904401e24240b0710f035189080c600300601035000030b5491030100000c00004003080d10a001514082c0041415010704903040050782800c032070400c0191703400010b03c8080c04030450755007482d03111907004111074010007080035107015290030a404241600e0081480010000b01c9204070b800d0040100300c5c0240c3c2e2000440d16410721505100704c24801d03241a5580554840319402c0068440004010182c01e160b00c0142c1c5030360424800904407901680701a1290340900c0c09060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 382958669 1250 382957419 382957423
    0x31507020a0609080702040527031801050c0f03070b0411060705120a0e130c030c0228080904090605010501020c0105120402331206040c0e09040615060206040606051002 74
    0x2003030507400003001c40c3d903e45074141143d5902500e0070294111f400e1004006030351842c0c140707043c0d0908495079010841140f04c501650f4038020091110f6640d000542d9a0701d403980284044c241000d6100115200200f04861560954005103022114002c0b1b039824041040008840745104280594005082090036290150f5810400c00207941d4500c0005404a0703051198a020006c60000303800e0f00c02c80350040e040f21004000d50802c03000080d1604d0606051940b0100c1c04a092a64040c11456901803446250090300c1c40780344211442041000b440da41c036110303805014031640c0100070000d21503242c0310019081241e41840c081c104a0700700803400a1400710356900d42c05c15015101805518450544004a00d0001504802040d51004008048580b6400500703041003040c0d04017140da11840c00380310588aa072544d523030101d41621091112820b0000f4400c0d40503000d0040425644ca42003400020301120741c0005006821104c20031050000d140140c0008000c25100c1050b1f06400c040000c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 382959919 1250 382958669 382958683
    0x27140f07030c030b030d051e030c040905090304031a0f06151806040519150305010f0b0313080a090302030f03030403051213050601060807030e070602120a0315060c0203150702 77
    0x5140d514070002d01014403c0d030290804450240c01c0f00c0c0c0700816004003074001d03049010006860304030603000c0418918404143ca0240240807512400d00b8108001c20300580380052401140344802c0c440003010452514410040500c03002d442182030400d0004c08600c7c0380d00410160041500280c401040380b1345000703d0b1844114000e40b07c80396071140c40001d0080c451940416442030103140d0345005003002280c0b042c2207440c00c0c180401240c01405058080c0c61003441a00c00c0240e03504400c008074050f28004545c85004101142581060707584c4140031504a0815900020a003100c1401141005c2140c42c0385440b030280214118500340d0f40040c010b2180441c00d1010100c01c401154060700500005007070305034030400f0b864956846240c01420a807003191040002414070703801c8909110f02040d03910542d1529400f401c000484500d202407142c4c030a41410040540c1c66650000c540b000342042d2000d0034031703595010004003031401010311b0405c080c510704100c01a0b01d01030202e89500000c0708 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 382961169 1250 382959919 382959931
    0x16090e070f020705030f01060e0106030902130b010c0f11100c05030301050121020403050318040b1806060c0102190314091c12050f010303031a030a0204051027140f 72
    0x60140000041e000300e04110075a80013507014031420b940e03200700360019080b04080d15403142c4a000981e0b40c0c0c2400310280c070b00441010750003a440803403259400240740c0203a0480e01c410304011540302c85550700e81181003198503086e242150341003d03400c03561030106500358050220340b804101c64840c3d80ca0381ca4480c4018450b881c1030042481306518142c80c107140011041410400440d202c9580f8200b06499034006001e00d0b8000c0500c014110243c074283c4544480c0c003001a1058411343e1b800e01c0c0400ca80724002e0007150348154180300031a8110340c24002000041e80b12850300300702c0c4980900240030b4401c801c0201c40c0380072a10082200d088000030740d00301d602c00e1480c810808412420030560f8824000c0a029003094108400c200a101c0011a540d0480e4806d41c2c0806c804a034280180400030940302c03102d58160401d0030342e100076242070f40001d07401c0b1542150f0442c1d1140e851196030024800c00c0c09009903212440d030904100c034118070035081441000302a008242c40c254203800c140b250f0062407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 382962419 1250 382961169 382961177
    0x9100303120b0f090a0b01180e0f06030102090a2304090b0a1a06070501050618070e06070c0e1009050a0209010906112a040f150b1605070b0316090e07 66
    0x50706201d41d9410303000d10300305040545604c1040c144241e00da006070a01020342c41c045445280e04034200440220440d00319a07003d403a070f600903221082030b4070341090081c0000740d242d034091244003a55076926880c1002000c400c0c0010b01da5005d00300b40c0c041e501440c0c0c1302c994070480c40c00c6071110209080f00d0030345a118000050028490746005c40c201d100d8103800c001c25400440101340002000070562100740101011214980e41440d440c0c0741e0b20111800312a203e00040b81c0340c922549a0502c04003401c2c125108083c812076042d205c58000c400c44204403101403061100031820049000b1078810f40340c100c681218254a040c0c503040018100880520a1800b009423104109a245c40c09000840d802c50b81ca0051805010750322a00400d4503d0552801c0c1c4628500b45401218500c5882004c124186902140d24141c2c90320f5200311049d0800c0b101c0882d041c941d9150b50000a101f400020064482010619107a0500c120403041e110020850724003441030181060003941d404440c42ca0740b01009240c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 382963669 1250 382962419 382962431
    0x7090e0a0b1308070b0a05061504050d020102070314010203160203071a04021c0b070e030a0218040503120901061a03270f030414101404090f021c0b0910030312 70
    0x4008802d03501603002400605002c91808100061403400900074041843e050089840d450b0420040d100040c2003c40301d0517040104000509000a40c1c010050050040d10405070380c1b80c82e14401036a0702900c50406075030004c1000941110015060800e82840c4002c42c107080050391003002c40c0d51f4005c0c114030103044c0c102c0000c04556408803c141804040c0b03c6418000503c0d00d070558010203343c0d00c0c100411051414119141400121000f5441d0024040060900c0c003c103420310300e050142081c0c032140000c00401c648002c20414080c010400100009952407500000c240f8480841c004081d41ca0750030414002041303603035082140384180200b14100d41c06c583d601c22600d40f8041c5150200d071800301140024402c2c62030890144118400c0d110300322400681349084035000c02400351030b20007640c00d10003031250101035400002d2407440d0500051401181c07880b00118040010640700c01c242d00d402101074541440030341d40f600515043c00d03003a101d606682e00a49007142d0740c010810701d59a40d203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 382964919 1250 382963669 382963681
    0x1b03050d0f1508060112051e010212090708060f190b040612051e0304030305030408090f0916030c0f0507080717031015050f0d02070606081c0207090e0a0b 68
    0x150190000c01c6580008000c50040031141c181000324603c103c800034003800c00000f6118001d070364075280881d40000504008a0b805a15402a00d40080301c08003640d401c2c00046460792030b0424940c099400c05c8024407a9601d00b100082c07a09400a0864160071072040900c10080804840f403400160b2247d0041070380300329200414010800d030391080d02c44c41e01d80000303a401c0c41804201c0031072002082e1206009841940743d000d40e20f00c2603100041c000b4030208001400b06c2c54810241c00718190080100c07034030840e10303c0015035170707401918407003c82704003400745504039500b41c810485a001300d410810070003120340e50081c065010f03008003c4e20052002400d03100b00b1603002d04500030321200600c21a128286030b5010080145240a42464035003034100d03031017980e4003800c10745103180f94031444186403090055529010f500300c4030301150819120f85020508007002d0006200c030b440e031004185066520b00b20024a04143c0342d00c01001d0fa0b01d00b060141c0b00c0e14000ca40803044541140e0981c0c10794a81c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 382966169 1250 382964919 382964921
    0x3010c0f0305130c150809010b0d08070c050a0906080c01090f271503020a080a0807030e0d0203010c0e01090905010b040e09031201030f060e03130504050606040515070506071b03050d 80
    0x40c1030028002280c00001113208205c0713840041011001c0d507543c0225940d14800d15080355900c0c0340c030b607902400307a081d032100050044000785549482043c2a24600e6a00c1000c185081c10640118411584812092000d00401c00510580723110902e00340b000c09140022604072407410703001d060600858694108280d10310800b103803900b45683c402c01c00000911509200c0d148025010417445421203200c0020300e080c00007031141c40c01e504460712501d8603800d9078040d2020041c0b420820f4110480a0001006d40d03400e10550409545a0719a00410140e51000508004054001c0c020241c9081e0060240e9417002080d1800d503603803541c800c0c4458271940c1d1802e10f54096104002d00810352000040200010302504003511441070005000c40c440c00c0040903100d0088035010103001c00050420031043c030f86a04002e400074000b6040529140e2100042010309030544420040040d000800f00300b000303000c00115900c4111840c01005220b41141c09002c101c060f10f0001e001c029011413070241400e51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 382967419 1250 382966169 382966201
    0x1120911120c190f0806010602101503061806060b0c100c0207030b100905010e070206150609100917060408191b050d030510080d082e03060b03010c0f0305 68
    0x20040510480b01140d600350340c200c0f00e8030300130411140100c807000110828002101410381d140b6030040e0180c1c0d00c03002c0351800106111604d0311041301800c0c0002010801c10705c02c69296028a404c003007400310a609000d01626903507800445545003c000c401d41d22003001c41c00f00d0b161080b610012880b141c42100480c030b0400c03141c0001c1d202480c01ca0038400e0800a02c0a004220b5520301230500241c0e0b42d4501e14000c4680c2204c000300941c000c0000103255081d80500c2840d000e500501180c03c0400d81c0c0081085c40c8031129410307010400d94034040c4100070030705041c95000d1444034000c7c001e81c50f00d0b6649003600c0c060f681080003407004200d5021030f0079014071218001c2400c40c420040005049007400d9946d8031200b5032200109150001103500c00784003200300c10035244c0b2003004000344041c082c0102c41c0c0b44801402004484070301248034a10070703880b10405030100a480c80e0704208500354200b810450f000320403294483c2e0315290703580c800603805c400c1c01900b03804541000191a601c00401180c4100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 382968669 1250 382967419 382967443
    0x40204050405070c050613020a0501050901020a0818130606020703140106030501290d021c030e0409050304050a0603020306010905100c0f03081f1a030c0d0207030e0112091112 77
    0x410b060812000c03a500551001641c2d0080044075030540760200981c60485003c080030390807054600f0140201d50140f070042c124504107104450454829481d0080c198108108204031a10980d07003404451a20410081c04200c501c3c0040005038648600a03654203018880180ba241303c01071761700c5180c01f00717522080045411030024004210380c50850000c42d85603980741322140b030701d07144031404a0a1074080d0205071540a071103c0109810f40c2400c00303c00340e10b503800318104a8088402042521140605a0f8141c414070080d41c945041804114008140341c0084082500c1441040703442d070307803244068046900c144d4096107514141c1c5400c8804c0b0f426500041c011520580742c101c101030384455080e00c1038035000003403680c200d1103400c403003182da440d407140c694071030380c0050141180c4484030000c54114078861a8240740c1004078801e1010381c1c101e0141640829484007841071256042100511000c2481c1010000e802c400e03501c07080f044d5440508039002ea415000f40c3c64454204200202c1150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 382969919 1250 382968669 382968671
    0x10e130804080f0c0a080a15112b0c050f0405040b041103040b04060c020304050d0206160515010e0f04021f090f08030c1e0a0f0309030f032f0c06090402040504 70
    0x80d810140b42d580c4c806682e04034000c4455400005141c880454481c1d100c07a03110607141002e0040c2e0200e00017130705e0300c0f031303941d0002040c10130004036005590760701240c260520300e001c0c0000d090401d004801725103213408428140602044080321007900c2c41c045505031403041300d001864103400c20200340280008505843c25103400020700c800d110700c000c00d01b0710a42c410788d0288184101140d0403a1240078900c1201c0c1c02802c0e030503100f0010300d03241000d400a00081c0d5015131181c0c1035511014034040228190801341d80d51706006100310110114401d61007a081103d1480f00e08066011a617140707442d00301c60461046088840c5c0707203607225001142c020142d00203078084440d100c4091940301c0e4410403c00c841c5224030980399a105034018012031084110001510629025485003110407100850403010030104030000f000089040c042540818025920213409603c3e6041102a10b0741345e0790420305000f0240d140c0e52140c3c00c001880310381000c05651302e0b5169407100d40490301078056030b0411a803007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 382971169 1250 382969919 382969933
    0x40f23060d210306090f021801020f101a0612040308011508041401110c0705010801151b0305070b0a0e010c171f08010207050a03080718060e010c0605240603010e13080408 75
    0x121b4103402070004503000010005902c0358907801640e0703d500307800d100c000d07907000010503c1c0a1080d42d4070035600b4036000c500e4a502215a800090901c1d449441d003640d880000c3c10600c0705265101594502500d031260a060045850001c003400c100300040c0000d050030240c0c031501400510070b41164880c05200e01e5803c0e240c001c158081034407501c0901030b0600040186000040324041c07825044008605e640f81c00418000003070780d61a01c041415001c0d02400f00401c415000200640081d5205003502c403000103403000c003289924292800603c6407801c0110400180e464144001c00e1107820000501034210401c00441c4031100109080c3d200d111203510200c2c14805016001c540761701c1481c4296030b2001d80f81e07213240c4151410040420b000120040c1d00109100040c0541518420b4041c141450b040011031b5a883e81c1c10390b0000c664028030040c00720002444500703aa1007102d1102400c4504604543c1003102c22541040c00412030805030300040d6101050050035411030340a40071100568400f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 382972419 1250 382971169 382971191
    0xe01182301031101120b091f0312120b01110d050912070f03030207061103040303030f0902060d14011508040204051003141f0b030c0f040f23060d21030609 68
    0xd18403d502a0502007a01c030343c01540e010f02c0a01c2070908a5030b0044c822450368030740c040507140c510807224804000007101d08001c000b00304100d2400000c05607556445007503031703080103072003054aaaa2100506200010040d0164480c01044560b6907130b0080ca841a1aa92808002403058486922a00320b5018000c1d0200e05d02c4000380310441568020703000c59403202c0c1e562100315003800300f03581010400e8201740000c1c00081d20a0b08040c4c88846142e402052070f42c13058002440039405004403003002541c981d10508614159001c0d207004000e4103841d844041e0120303001401c0940014070007403046681e080064059100c201c80d500c0034503080b003058594801000c60707442d99a00005140740c150740300721030f045c0c600702d03198010f0700e0050001902800f41c24884000340300c6002c00750740c4c01d164069298610012440c00d18403ca17042061078058400031540c000e0100c10316494080c0481c0c0c000c14000d40002c000c1010000075009070010342040c0d00c488191000c0403401402960040c40e0303124100084401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 382973669 1250 382972419 382972433
    0x504060615021501050114121e0106030c030b090c041703040312170609040f030f09170c040b0901150f052811060708011208040f0e01030c0e0118230103 67
    0x2042e0616490b00c0043e590301e9000550368520b400d2060050300404000c1000051103120280d40c2000301c0781d51696080107030726828907141b40241c21100000e0755170051402247d905015550b4a0f00b4151007221341402c0c1a0f11200c4d49210f80e005482c4501030f007204006842404104850096070004c80c2d080e542d007092680180441c4420207240030604180b004600740d4a0302c010b400e0b000e180c0c007002012050301c240e64190740460f01c140161b0280092003500040d90035080120040e1780b40884007038603001141d10204000c03541d03c0485980107005200c0184001d2030607552040d150711080c00e00c011a90300e040d100301e03094031907060755441075080c5511001164070395403410300322500325807103907904c84414042a940d43c14085400000051106004111502d584900c0c07171105070052011524180d123900744510010314941c84850b180c5440801002071142c1309441c640a010340d98201842c0354035200e0074541e800a1010401c0c42642e031410503006902544001400e0072201103d044819a96030400308 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 382974919 1250 382973669 382973683
    0x80c0a09090903200f1c0e0a090606090603110d050c040b040803030a0e0d020d1803080f12070906120b010512130b0604090c032303030a020705070905011503050406061502 75
    0x4454600c0044416030361601140c01ca950307402c601d0040000b0007606c074688010140322041001400a610468906900c90032980c0c0083d14a200e0042911484d00743e00410300c803103551001c0105450400740954609200d022140e2180b00440302240a8440c030070348601a00c590b90050103080f10004000a42100100146214410858081125002083d1415220168006410016009061100407441c010100c054078200103000308035607a40c0300e6445021039848400c4a00002c1d4000c00c2c4035652401242c5002ea1020040c984045e030517140c40009031405c6100801500890b0300c4112014080e4820000d807040701302c5058400403281130a10820000300010582901e2280f02c90700066030790f090900641d050282d1281c0300940c010300d1a100e110140d00c0c0d02483c0d03590100205034030740443c4d10400285002c0c1c0d119030b00060761080d00b458010300e054440d9010480c554149001003120564045803c501030165003800706182d5240e2411000078422500154401080a0807201c0321503030002d000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 382976169 1250 382974919 382974947
    0x140703110d0c0b040b072307061b091404110d02030702060c040b040504050604020d050405060f0a1104050d02010905040606051809060d120201060e190f0b01080c0a09090903 76
    0x1450300c020101d01c0880d4030202d21400542206002d402140009400f4071400e68000b58502c0d10070039050080d4400170100e460350580b1104c3e034801155020074400a4800c003c0300d44010410100780754034404003d08100014420710302c0044910480204603159504072000744201a50030307030380e560004042103009400640e0084010301c10708001503100401c007000c0b1030580340c1e59040340303081a240c141008080d08000f0f200c2900183c0178420030384a10040d000700c2d030003148114091700b0035141c0620b840c1d40c00ca0004141c00805414880010030f940c2e900c3c012a400e464003641d8903c1c203083c1d580016101040254413542c0c0180ca443d80005025a000000c2c021640c5c1214113102c404e01c0009c00c200c00600306a542c258095200c130002c00008a00107520520865240000708015560704400290014101c50f60304405044c0a00854a43d210348a10804164200c070100b02032100302c5c0c0000c042010007001461380b45000160480351320700a20030080201091070043c0716085c00c0745401000b0b41149088 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 382977419 1250 382976169 382976173
    0xa030c0605070306080309190e092a2d190f0503010b031207031e050a030b04020a0c0201110708011d07230105090d05060403020109050f0c09041214070311 68
    0x714054520070f002d02c1041703c5141000310f0420481408101c0c01d44d020040d80d622407a20307030400190f003030301c5001d40c10311070019030001d0015010240040b800c5c072481c2c03c0200411110f03540c0c04040e10b58400c030a0500703003007a034054103e01d10780341d08034040d8054032206920341c8480c4d13242d180444400840c6030401550010340002001076034403c2818280c490901110f41e26411881e41080341400d50070280c170256000740b034480302462006440f020141d402040801c00220000390703d05020f6014055490f440314140d0b41145014040e5000134410b403803940000f4100001c40c400024440070802890001d032400074000c104a80040b1031210024010015031000c40c00380210000c1c4035400e03135002c0c0108160880615240d0721950004483c0c9a000d00a2aa4444102d00b841c60100758200301e05c0f03204501c640c000240c03141c82030428514004803064441819072049456648680356140c102c0c3e000369101407035003140880d481d81600ca101e41c08941d840c2100000c02c04400b4168000a216076110218007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 382978669 1250 382977419 382977421
    0x20d060503011b0507110406050a0b0a080709080c2404172b050c0a0f050d0801050306130f060b031204031506060c08070204141017070509060904140a030c0605 70
    0x3d0b03540c01c0078908045403400f0030018072591022646ca06001c0440400081c070001c2c00a03100c0c000510540d65030b40100d01400000310f010588903801c81d00c00c0e40c00014905104400c01c3c40d054130030381d4440c0d405400701c0c09201d02070000a1210040000703000036540c1e10304420744490700c510996200c9034918052810301d210380581c1d41841a14044210404c07021880d111103c0e150501c8240c540c0d03845011181d4143c411b480790400840d0040e60240515031241c0c1c0a011740e1401c42000602104060700071500c80e401060034840ca8405429410149070350007202d80081115030f042c0700000b4403500142503014020036844804600c6901d00420580c1d10601c2c400407401514141c41d41112101d015000105850b2051103011401c0304028009032480200013060b01907910000410511056859000405d600d8505110f4100465980e0710340c1000d0800602c0e04a1500c0b000814800014010307500854011010a0a0040301c40700b1103440c0c0d030844115418094240b40042001c82001d01c01c0e1401d928142c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 382979919 1250 382978669 382978691
    0xb0117120a0e1903020d0804090c090806070f120504081209030c0714031f0b03070603021e03100e070810080c011e11010609020414180112021201020d06050301 70
    0x8410344030301c80aa996428400b42812040c0008044400e030301c100340d2440c45400000581d95500181030061044001075151454000000c00361071120b0903580a100c000d00e0140011100012083e60211081c03a100c4084049404103450213049000700304034044c1060200410b00c00454010b10030008c500c594800d06569000d0b543da00d90144803003030001904080000c003c040e4030401e41e0303826001d00038291159a031001c04c0c1e02c007410103003404690085840350f0050009180c2407040300028840d80c2801d62411900c844080001103050081000032100030003c1010320110500580140c20ba0408940650900000141121404440591041261b2003011a0508020510b4181a007041e1103030340c2030700492943d440441c3c0d600b0110a08001c0324100d11801c4900c03d001d01c400512841c84010303620f5040c10042d40010114a00f094014511020b9000d0040c0c0348a495030304444072883d003040c034900148002961498604034080c0b41d58000f00c3c5d215404185980120111034084008001c071107044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 382981169 1250 382979919 382979953
    0x1b08071518080309040914032b090503160615080a02090109061508151e130b030d230307030b0315090c061b060718060203180f0103090b0117 62
    0x54000c4802c540c10500c20b450071803d00340c00184000303118001006000542c1d8030501c0c5150031940321250b000000e00d421203005904011460942441c03c1d1781802050306646a0035541c2c42100203101c00401061050070904c0120b40c400003110701d41e01c0f0020320b041c2e9036500842e07440d02c081d1002e81c42001c0d01400007074130100c144504022600f448681113443c0e46094001d9034042001805610b81c1c201c98100c0b000d80c0e640b41c10f0016210880018030031020600c0e107052080041002c0051082285085010340069030000fa0700480d4a91501c2e00300f10120041d005201d40b2482075040c00703c01754010060180b01505500300940c100026400c60741e00c3d88001019452101c0250341c0c02c5500d0f00300001415460070f0180040440049000803405010402400c1a18184044030300f98000f400055400340303010704003486480201258802035040421404c445401142c03299880c610507103400700e031424a80d0003500314140c2c5a40003000d000e01980d540484c1c0700c4084200012240f540184005200a4100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 382982419 1250 382981169 382981217
    0x606090302100507020f040203190e0120030a06090c08090d08010e060f1207270b0f01030509011508070504060806040f060902011101150e06010203161b080715 70
    0x40c55800c040b60850700550310b0380d20042061741c200e1103030b400c0812240c4443c0001c6004560040c91102d80e01d04200b0300c1022100300340f4081c0066414540d01c1c40380e0b071321100f0820003144044c191260f5291240b00c0c50400030302075513010f180361500f00b10180e011281c014680601c218088020f4400700210b00c007080b64070b81001d004400300400c0150100d40a414444a100000600501078290141c8070400d840c1c0b8210880d4010080070ba0040041428198450381c04440d00c040e0381800d00c05913141d07500085201901007001c5041682e6a000140002c1c425009210070440a0742950384440d00c42e0383d444c2c2c82d10150f0145070f01850402c20b00041c01c0400180d001c0c4180d410441e65851100e0503901c078000f030180060280d0400800030001c50201c0700070b1181101d0780e0f4003c840c5401d0ba0f4944011302c04880710041185040d5041404102480c40342c0003840303071016910405c00d980e040d8149449541d07225851304070740b806214400001c40c4001e038101c01780000055070317241c0d003020404c0c100d1549a40c1e18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 382983669 1250 382982419 382982423
    0xb0115080708060d0803130201090e1b37091710090305251a0708130219031a150d060209040609090b071707021b0a05030d0801080106060903 62
    0x30080c0000c00e07481c030940b5030307580101e002000705032481025110b009140c1c20a8a601d1180f9100200c00b400715a0082c0d0703a00002c2c801c0c50ba001140745440d02c05242f501e501407041100c1c1c03010000c0ca0040e09881003603a411035103e040070066a038003c2409021024622000201c003040d040c034408181c14586500c0c00108001ea0030050281c4901224840041e04411204400784101405034002207410b01080a105480d440340040400075242042000420002c4250441002c1e400a2061081c0d102801c82e40c00015a060106ca80380c540c8003042285190704070030305821200050100c10480368032582c0840300140315803510962100103411080039501c1e045194819a48019100010102d0300a0804207000030b00020301c05035a00a25001d4031041e200482e84d0300300c070380700300044e150b040001da0b45502c20845145106240502d0003030b40c0e460f08060345131284100380914681d183c1e50351000070050320380a81698030300100c5203409031560200307006d1410103508001c8086011403085c0d1401088a03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 382984919 1250 382983669 382983677
    0xb0c04090f05161b082d0a03060b04060e09310b011a09010f020705030d030606030e01060f091a0d1b08030304031e03020d1103010503011401181e0e06040b0115 70
    0x440141d0722001582d008841c00c2e48252806c1561041408540001e0b03800702400c0c0200340da4820701010020300710780c2d55400c103040c462000d00c0140000da510a140c900d4450f42500d88030100d0b2207251000186644400e8030180e45060303002c4000c054003891300580c40c014482c201e81d10b2240d07206c9003104010808051108a141414800b06207658406c943d03803a072050440c01690f0b04141c40702c0100c0e0400100750805c4011079202c0d0303404c00025600d4420041540c44907402081503505080400545107280e120f102d04031602c4404442c40101c000001c10b0400000801c10107908182d85466985146101d441401241c07007268009109003000c81143c0c8a60f42c9569081001c24a01070090402c0d1500e81c1c910040507420310407105100c00c0c51080d100c03001c0250546586944c0b400080600351040d0700711482e1002c00e4040100100b400603944000036807107050001c00c001d42e004006401146a07002d803203054070309040812907500f0000c074103980901d01944002e40340b1b0303894001106c100c4100d43c540030002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 382986169 1250 382984919 382984967
    0xb04060606201002091c03050909010b16080912011d071706130618050f0606030c010c02040b0f0a09020406030614030303070c05160303050309011d0a0b0c04090f0516 73
    0x120310390003803100d00401003004034074601c151246e140c41c0040e10012008500d00181d14002031034412004c174010304650400c07924011701d1034585010000003100c001c1c01c1010100d0847d440383d0314100b040c00c03007906180082107030b60550b00008000090300120304001d8061304401040c41407030f80341c585038800002c05c02450562100680c2080070600f148040d00c5496803100c4e401c8030348d009903603005000760051780240281140452281c0c10a1806000303c2e10170f500580042c1d0442c2d030481440000d0b40d80407580040e050000b4008030341c4a40ca0071000540c04541104089601d48407075024205646140d6020401c82e034844409003820314103218010340c1640306200050107503100e0011501c0d0701d8401c03070603200701d00800c010400890b90a41c00031070204802008000c9610000d02c17603050150418000030350501d884024070360b220581c0c4c1101070440c44415000030645e01c0708204940050041200400880d0361140d2001c00504059544041600c01e040c050148648a062000c3c08148000b940c0010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 382987419 1250 382986169 382986193
    0x90e06090a080708190512010e06030706110c042306060403150b0d080a02150f0403140f160825020303040b09180708010302032a13090b0406060620 65
    0xd03c0e04049412038070090200560f010020061004902c824442e0b00d41503145c001100f08200b0b05e020503007200d1680030f00c940c200016560000350707200c100d079214100302900a11090380141040e21030b2085580060505020818480344107500c2e5403550012841a41a078540c4c4040022510075844080c2c4401411944a00020451307071090b0b8110a0080401e10001c1b803590f56408560000328500d00542c00808040100d01702400105512a120368800701e0355203001c2c0e0340500240c20f118030410911002140d8668402685001c40300521640500d04005421500d080e54159004584007138100101480782c00c1c1c00e0342c140c68000741c050b500401079070605007040c2400030306411021410340c0c4401254280c1e100041214005c1d130144c400da64034000c0e01c3d8103600501d4070b090441c0240407004001c040d1000d08110070403170380c1c0c81c0100e001c03110b10341c0c503a0342d02c0c0710400940075441c7d0217018106101e00740b004100b0641d0050084442ca81c4030788800d8103031200c0e4440d081303803a900c001c81d06400480204003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 382988669 1250 382987419 382987433
    0x100c050a050d09022e02060103020607080a0c0c0905070f0201090c030308070306030204050405070e07020f03090409140d0f020d03060605030c0304140a11130209100f02121201090e06090a 82
    0xc2c00c0c16078030710015455140d500001d08410b001c2c076489586205583c00e420700c12540c83c20040040665000414555145902150261140410107890303030700045030b44040f403845600b07401315441d0001c1d02608820384840400e0010002030390100d010804a80444841900601a04c8100c0b900090818070311840c2d5101500c0d0381d10300030540020155a100007000503071700e0740b040c64001c50103640202844c070b04051100b001c5000203040c4030150350010550003082d840000407181c40038002d440110300d41d4824544030250798029400042c46000b40d425a00d0125400558607602d813035540d0031164540e0103030f0340a908444060083c0340015400b0400540c15541030030095030800d11031400c88800361018409030703080c050016012100e41c18030031602000b07494584411358004027a00421440c000c810f10002e980708545481d0718090161290740141d0b0b030350081c455100305001070100309030346010900040c01c000314240a100c080c81e283c01c20a03400c01000050303c0748100036582c014101d040b040d49440c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 382989919 1250 382988669 382988677
    0x30f09070b04090209090106030908030a11070204020307030207060c0513171908130e010b0910030e0d020d02060906010308032e0609170c030c040903031d060108100c050a05 76
    0x1825881103800004100e00040000c00c0100300740080141c503014810100809010182d00020815041015020218803850b0481b600100c4640d400100c2c180d85910780a850f00400c3c40182d4000c0c8003004115000c2d030141c00510500e171084008000b12601034900782d0f59802a2000822140d0505406100510192031295807242e4070303400b2195044a5a00c2d8044800072003081181c03c03400101c1d03000d07030034a07040200350094a4187c5601c00b40350b0414000d003440b8010502060b11424200707080f446414001d600c40e11400c01300030251078600c0d00300759010b035880c503900c64001c00520416000540395800820b00c0c80c16284d00440b0b903071950700c608602500110801e8590b0504c0314024080703086040340414a50f0007404117807220207c091071302c5c0c02c0341419005080d00c01600d410011030300405038ce01150500c0349100442e000038103000e0f81d007022002069202502d40030401c0401d01400d038000c1c0010451f048960040448064090042d41d60094601c08509000840c170700f403003044c141c09d0045000e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 382991169 1250 382989919 382989931
    0x605190c1d03070506160302060702010615031a040f0203070908031c27060605041107030e061e0c010219020d02152809021e060313050a0c030305121b030f 68
    0x703d980c991039800185480d0701c10080c44030740d072480710300341420541c0500c540c540c04015030008104480c9003a0b000c0d41d2603101000188201656003031a10304880700c9003403105c4410344c081c0080003c041c16003020740017980180e51400104000c40d40010380e0140000458200040d00355107140840d819195101c0540b015441a03500141c4da0000441005000d81e03100d04e0070382c0200008210325107802d00b40000c84103140c0c01c502034040704019240100c1d4002d400e4034030300780003600c19959861541181c60041203c040200101002c00900ba6181c2d0405401820f17119140c400a880c40c007059460580e92021401284405a04549080c0400c00320504c140741e8400d810410286840740801d502c2c0c40440c03042c42401751260340e105501001e40c10450140040c051010f0074041417604007d00049003400002c03c0d0b20f050b01e104030b046108000041c003000c140c259114981c10412500e918001c0c0003608005400c410300740807040001c1d12a5902040d91082d04280d002003440c68483c03c50702c201902005200c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 382992419 1250 382991169 382991173
    0x20a081615020f150105041b1e02071206061a04030c060c11122b09050d05100507020703031202030c1c150b04090e01020f160314070605190c1d03 64
    0x1d11501240601400d400c548003d032001d10b1307a40c1080701300000c40d02c5682216000503410440424004d4201249144003460044890058242d09204926203c140c0d00080401b017070880041c0e0410006811a800351102c0fa14040d141c1e42d164032818006009078400030342540508002040050b019200c501c0c00c0030b0050382c44000500081010401003d1144100d00e0345604c20241660745002a144000c2e0540c401d46246030405d0100d072004004c80e215000c1c243c031070310740300e40a2001c20504000d80036842d21049400c1c840d034500078001075100d0503c1c0c88181c4c00304201d0501e5000e18862442142d06c540120a0030604200580003064070108111003058217a0740d5401250007450f903000745113401004c11001443d903e1381010350440c2640d040c0c1071400341c56030060103552004040c60040c0d0b00300c2d203ca80540703007001710f927070030121400f000c5020589208400020f401c82031201c03980100341301c3c40a80348588007402c035101c0c403201190207401e4500006030089208811001c0503108588100c0c000500f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 382993669 1250 382992419 382992433
    0xa120c0905040c03030f02010e210715050708090d120903051204050708010b0105030402030d05030408041a0316021b01050c01090218040210021603081309020313020a08161502 77
    0x802012a1010b031000d031408000500d080080640c04541904140807a00c000d1020021560041da511100c24072099200c0c10b0800e0000100f0300703140d096a01a980010b4001c00b2000948440380007444140e1b5104c000400300350024031048000243c0c66041c0080303070749510201c81e4224a02008080320401101080702c100040350481071000c141900541c0500f000d07107011403501180c1401c40302d441481d039062040501c01c02c4090390700032825820344800350402a640e40c0d141d20f0300502c4e030320543e007090b40044409141c0c1ca403407081500145201c0c909280d107001da124000f40c0244d07030320700c0d943e0300744011103a500c000342525521078006881906034402c0013092024032503000076050014a841d50900010703070740401c003d5250412009804098a001034250b206940c07203103a8000c0090302014290f400000303080315803d40c0c40802c1c103004084510085440e405c000400120340b810b0344605070310031a05200041064800800c2c01081110340c3d240d0f03141454604500750000c4409032841e2415030080300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 382994919 1250 382993669 382993679
    0x29030606070f051029060706020f03040309030b0a05041212020f0a08240a0b030c07171b0304050a0512030c01060e040611041203030e0a150603140a020a120c 69
    0x80b14501e0707a03d00c41d4000c0c2149052070311814049035010380b01e0f0a078400c680c075401c1881c0600402d01480c0400c09840340ca550348900c0c18070030701a118503e2402d00c10380c000000c010904d9440381c7c0038030659106544c0c070101ca44819607100c05030b80090b107024240c0e0a80c0074064086900650303c036074550004180140c00c011076600352110302d4000611041c00b0400f220100026019804005101015215142d0554400d507001003060321113035000d010414a000000b096110420781c0a403551564490742103200d8104420810401d50800d41724501c420b00101450301c4c402c440030044c0d40035590043c144881040c0340c481080000070b607000c2d2040103404104040c1203000000c1c0904009441030f003503140c01c6030400b441c20078201c1e00790721184006c0c03003000e110520190080940710641070781c16182c003150b04910b001c191360a000a11400502d0341c2e00401a56030406030a802050480e80030f10049140a42110030fa61744510070b1100096001c1000704040c48030a01e41e1b58098005400340840c404030548032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 382996169 1250 382994919 382994933
    0x305030f180f16050604060203030601082a041e080615040f0219090605040608040303090524090f060402330a02010b0a050303070f060203060102010b03060a0605030105012903060607 80
    0x481030304203554201d01c10b8200f01e1440b9224000082c034054071300515251034210000c0d180e02015008a040009040108000d806003540540076401d060300305d42003400d00b00d0201c22090f07025101d403030f88040017440c16200b05080220004111000f0f40b0250900345c1d148440c0340307040c4852889496020b42e407024200b0000da0b5520150819203503402c803888507003030512030252520300241d0240003004002c120074000030f50f000ca4807680082c0d050402103a554842d28181c1d0801c4004d00001180d0180c4184d4190714030b0f15029145e00030b00c85c040c10f95a105040301807403906c1c0c080480d4040d4000284a0b40401048001034080e69002e0780c2d1091451000e0008441500071342c40060001d0050b034440c0c002d034244e494806002002418110011881d215076680e03440e04040c100c0c440608166400300014050b64000e40100d241d458000341a12550318044041130014882ca014560283d864000081000e410408180140300320948204046c803501ba407085c4403a600080007a030b00218280076041c00940c42e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 382997419 1250 382996169 382996183
    0x10c0c030b060118060504062604050d0801050d0f0b070201020c06011205100e0d230d050108060a020a0203030f15101707030506010c14011104081b010c0305030f18 72
    0x4246015121801d000000405221801342c81d041242600300d0f0030031000313400000702ca080f903040d410442007003010b005800b1284e02003032202d02c016107844020002000741c00725003502184500d8403400060790304d404c240210080c400c10018a21910a91282c021442135410158003121510002d890a4120740059042c40000e90000800d60b28070003c0d141046000e0240c88641d00e160302007041002d032041c04956a5050403503045c024000c7c1c014002c1c01d0007071400c06001a548800710704603178401c03e5503262030040c01d092040030941c2c007a00f400b00d21488114004c56198680c1680154207640307402210140d56600030301030143d14426100c18404507110082e50b01c10900090b03c1e10003542c003c814500700501d070010b2120041514201c1080ba07560303001407400081a4008200400c4100c0046000e401010005440600140301180016002c03400140342c1650350303a83c1e401c544921840f0401915101d105010040100e03409000107900d900070964090350104203282840401140c0401c0c150414403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 382998669 1250 382997419 382997423
    0x61805070611011415010903050304060e12010b06030c2214130b130c02070f03050a03140a1209060902150301080c090606030106050c120c030a0801091802010806010c0c03 75
    0x452020401d454115000319541d4481c41d000380054241c440f80c1020303141d4014508003090914022411660f44a01e03519030203035910004482e501c90700c4802c050801d00c0c4103030216100f1040c0714001008c0d001c0600418024400280610303055481d2285003d426810991725608440c0d000c150301e5060149518580e00146480c10f400101d00c0c81920510050848842c0c1c07404815007442c50068040c0c0302c07074061140c0c07640742000014070004c2d00d560881c249005a48000302040c020764001c01445008109840300390f11940b2a038413034080c90f50806c280e5004500480c00850210050040c0071134694000b81915482103100051540040d40000c003000400d03014040c80d0500800103011581d02004103d404001c00c4842d40802c1ca4010001030092005002c1c003070401101080514601d402008030145010441ca113181e261550102d85540d01d80240d110000040d00c07910001414141c1c1e8030645002982008441c2c401c8034540d0015074030307100c0140c07170241003080e03011a05001c0381b030082101c00514 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 382999919 1250 382998669 382998673
    0x5120703052107080a0209011205040b01063c05190801031202120f0c0c130f0b0a05100f02071a070b0106020c0a0312020309060c0d1d1507061805 64
    0x388009080110001401c160301c46100c0e81ca00070f2208050300032042541c041801c07000542d4581c10500100c441c001c0c040c40c0d18034418140801d04c41007002d400c5001c1d058038925034034078046412804070754520030b0340380d8451042101c000d00ea5080300a42213445480d0041d660330100e10303015811210780020111800d41d0000508000e0050003008030764519120014100e10041c9203120014030800e05c0741c0b01c0c0075110070f15048000703507584c0100002e000100309200012f1080b5101036141501001508107038104510361b038589442aa0249004040342c1c060310300144c4211685c03460707600146c4210200340103c80c154071032800001043e03400400071450031020200840d0315442c0a00e400220b109060f0002400d6402540c810804c6840e0309400d6021640c00c00d4840d040c07490403410503402d51140c2c00d005600100005007030f03406a080040c1200009050703a8a1001303210b441c420b80c2241640f0500ba42da40070300d001c0e5102c0d5880c40604080d1a0082c000d9500044144c0c40c604010925480d039441180c1c15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 383001169 1250 382999919 382999927
    0x30f110a080414100801140108041110080a0e011a0103021e180a0504090305030c030a022205090f0c0f0f040f03210302130504050405192307031205070512070305 71
    0x113410100c00b2080a4042820000b00550421903081c01290300d0b01c944a040203481b90000d414400d102c02101078107040900148406540c54800134800c000071030f8100280c50900042c007540010511598041002503045c0076000c0ca000c60044001e584a40b81803508580d0840c02d003030300503003603100a22004950303800120800400906102929071765601c080d02c50743c901031520004c0394021007100d5000580640203503481c1d60303500c0041c009010b1101981c0500582c100c10003480c0307005c20866403e84004440501c1540d0b6001c80c141e5210800329210342e0388410a006c52203e440e10b003000f510212a03407802d00e504091710744500120041e130380c0c1c0c4140d070041420b6030745190316200694612400c98003490103619184045c5010040f5004a00c500b60040e95204001003e12009009a8264200c850111000c2071a1401c0c1225006803010204100020103400c001203080c000403180b089a600445030100340504160a0b00c041c2c1013440213481c0c9000d480400d04050401c1030007800d40da44a62174254803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 383002419 1250 383001169 383001209
    0x1104080f0705060904110705120403020a05041b030e0a05060a0f051b0f070201050f071406130c090b0303040f080d020d111b040f0204080309090a02030103030f110a0804 74
    0x604101600101101e810000041c03069490304800c50307804000540e03000c2038103c9103400c41d00081c80f90b914090080d004a01200c0c40d044503401c01032048074000c6818041044d144e03410401100c40203c88810162521440d00b178901340a0b82200000002407000c2d107413001507644820742096403c407a0b10021517901c1121840a071410b12455800c20b1010702c00006988003142040d40e03922490584070703082000803a4070011a840390080b155a00c2860000e142c41d0182c40c5401e042e00c10250110300800d015081c00078000449422107100100e4002d038070341d022a032a00c0500c2d0000c06e0203409141d00b6010410001c91a08400c030f0003071000b001311a00401d12180d18100003401c02e000704850404000c10a4041c80800c0400a8200f2146240f2031001001c2e09460000400510507084540c040d40d0020800094030640880074100d103d0050310b885086648401c1080704030320090000030041000500780e01140703442518906201c1d1035000481e011480d40d92500c0c00543c01039801507503202882004108 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 383003669 1250 383002419 383002423
    0x3070302060a140c070803091903020a06050105090c041802042d06080402100f0903020301180317040203030a080403020313090c0e0d11062206171302090402091306110408 75
    0x148465603062071200f0340c10300c4c525000c00c80c400c0d000080c01858011010400303600050105c80152400c484240425030110310b0040c2d152010284162420b334a080000030b120705060b00000e01c01d042c50003886160a0800c0988121343c071054072900c425660910011481c4224600c80f0001c1e031500704071030010000180344240196065400c198200042e80040c40016200c0f407030340c1c500880950a018290340c240321411200c03005182e1000e94150b00303041118902c450761460070b941c614044e50740e4030004000000d480015510a4400a400d94010803003400300304c1c803071203800b600107100b84103481c90a1203c00c4c00c000d0641d036541100c004103a940707007694011500300c100481000c00641b0b03940b43c66007841d02c800f03900c0700144540500804002070790104844140000d04002540003031081103003512480c004140c0a041711005410742107400201d0344400f0041c0500358002e5000388442d504d5510340c0c0c05d2208241c0c0180080700c21a4007244541c3c0018014000c2c41914540452182d807110b02c0c211742c00d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 383004919 1250 383003669 383003681
    0x10b070302162d12030503130f031d0102030309190503040306090803010e0601030509070302190302040614090606070b060f0a1203020d1d010206150d140105040c0b0301050607030e1203070302060a 86
    0x108941d101d013000414052240ca801d11a014100f598503903980c8001d540e008a01810000c00c440520311850003003540000010b40241000400f1040340224280166524402034451042c1c0f584621804010180c030130340c5400c0583c0c41070b8140da041550f00d507547d000b0740700414000c079101c91000c4014440d901e0608050703540a6002d10381840f03242000100d950700c03104280406806051542c07110015824035100940c010340d4080d1040240568400694866141005105100b01000800b1500f1460a4800d450600381c0100545809844080801102600c01880301d0782000c0602800540c1c0400e1040f1044030b2790080d000b40c011400304040042801c1c14900d20501c00000d6100d4900441c0d90016000d980507114061422000c516480010285050043e000700390320380d110242d104c403641c1900054000e030700c50401464415200d0610b030485010900400740c00980c01c0c010350010901c507655100d41624082d00d2410000045081c4c1360841c3d1107841d0541c003591041081c445416458884d0b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 383006169 1250 383004919 383004989
    0xc12070303150e060d02010201270c06050301030b010b0a02190303020702010206010b0f040e0901090b070c0506070f0f030506150310060e060301150807090e1e1e010b07030216 77
    0x403007100c2c2402800f540c01400508694059500b08020600310b9001350b0240079512a034204410300120300001e440340f1200b541d4130443d40200494030010350240114241da0590754003425400c6640e00740031381c0c21400d0704404589001c40c42003443c0100014140b1841d00c850078001e030b0340541e90b03030050300002e4501103041c0c0c015264400c0400000102d4940d0038162001d031299141b420bd00ca4482038885805072800d50006005140c2c0007040c090031a070030458103901240b2840603251176550304102900c6c04080c4500b5180491201d02c0440c0c0d1580c402d511980d0701550040020b81c50104000030219507130002c17601000c2448014001307101142d0020940b403040c040440d011880c0d981080820750040803810080414001c031040403540444c081d440038000313403000c00480b0046107820080d0a00c11022402d242d064656030720003189200d401c0d803802d036400000e005189140c903481c2445026041d0300c01c0b9410790450190030035076504c52007103850000060160f85c01c40c21219511945640c121850070b484 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 383007419 1250 383006169 383006201
    0x90c09070c0c032d081603020304031406180d08060918010f0c020705061e0714060924101503060e0f09010606170c0d090f0f03030c0c020102100e030c12070303 70
    0x2000010380f480c00b22510a10360400d8101011b40305c1c501a032850086420003000d03c0c0c41032244155402c00014840d21030b4015440e6104c8030460824001d4440d940f11100b1030009146500282c020705001e0f1100e504182c2d0040e100b060304600490711800c4072800841c440045844d6200d184049038100540000b40070120f40c4e0500d4508020100d40c18103013481c0003c00d5203040401c03a28103001381c192411001a44001c1992190324180261545920301603404500303812141da9500c2004c201c6280962141350200b01400b0300c40e083c01d04182c0844c50a5181c4810183c89400100308044030704803c60154508407500d25850501252580c256400350700003008200280c00b10f02c401c7c20100034220782110610309171703d550b9102e41d40584081d000101015105000b8100d0b500b08001c1c041c0590b5a481d80130740d80400400030b00c25401c561b0460000d10207801648100100091122a640b21810b03441450040324036000c1031038903003400c140a08600110044020550205158040c040c1c2840c15402041d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 383008669 1250 383007419 383007503
    0x9010e0d050d021e060f09010b0607030201050619180b040e01020d1b021f0c180e1807053601080d110309060304080904290a0509090c09070c0c03 64
    0x406985e8070f440c0105501141140324000c100352080a51150b0076449010300f019584490600b03002e4040c5c0029140c25000c4c0c6904440341c0d070b501c04101d0801007650319039241015410804040c1d200a0042c0d48040c41c3e100355102c01c00c80c1c61080c2440101303002c0500b07100126109480ca0694082c0f41021801d007003c0d90801d54680b100c5080602c011100020340c0c41c40024190409142142e02400b0300c210f40706244250000400d102c0c4800000a10801c0494020f0817029454502140c86248600c20140c00290800307035259402106e01490180740025100010521120061156803140c2a40f01d40c3e20364015402c00e407507003a48007454000040d98580118a050003203000700d0000e200042c00548030600204825000d80c0d0b903a0400c5c1070040074030004066100c2c0d00304000b5038611403000558440c0701c600c07070f00040c10b0800031140c5202c0d80001f800b80480b511b241c4140010094000c021000300b00e851080240003c0b03400c000d1001840c09448164040b007074001060880d864082105c3d4226a1102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 383009919 1250 383008669 383008723
    0x1401081209150403050706030212063a05010f090203060c070c030b19061e1e0314070e010e07171b0d0e01051504140114040209010e0d050d02 62
    0x340403a48015400d440d410900c8085040c04409800b81d9000207000d40600400010300c0b9903d0740262089166144130488541c039080d00300050340400d18901d80e840c12041c1c11529015206040040703010056034a010042d1004d50303202c03801c440884a400c5555a6101c41d03040c298101080100d601c80e1800984900d400e00503100e000f80ba00d034070310004285051b41400204901603107034003840700b40440841071000c02d488601e0940c40159503003180305040012040014003803480c0040c6849156030080c0300040340d0660b200e03c13200d6410314080400e148101080040d80d44060100d5900130001e08064950600740758800921132400300f450b500d810381c030a03400d00128480f0031010341c166244d0340d10070540e2510f44030341c000017412100f10b40302003039482c12040203c0c50030710032041b0031203800c100c40800a0218850070b42440401c01e018001c07171403080764001d0415040550081070640c0050501640c008142e00004400c00c40c140d40865494100021000207282c040182c9100410301c840b001104145607 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 383011169 1250 383009919 383009953
    0x51e01080606040203130203160e0714160c08060411090f0601050a110c040c051e0a0206190f050a021902010b15160203030f030405120a053a140108 65
    0xb4059602c00c07503001000c40d40d0000c2844040245a0303018042d00c0302e0200c1c1c10070340d00c101651446400841410720000443c800d10a520098280d00e81501090401d0040d002503021103070310740800c4880650041004ca5100400c00c4150b108070b2081244e4a894103100b402d1194104019001402c00141e05061013110b0380c1207000d44d442100b06240400744e8540110107286851b074140c6410f0f8000d07180041d002d0042d17901500400510307103e40c1e28003030011710314004450b9034450040014011b8220001094076a00a01c0d0083c4000030010008540f5041855141044804c25a42e0b8402d90703600142c40203078030039111300d5080c00410900003048401c031001d02090501540360102c94514900086558203046084480c0c0503a07034000d01100c1e22a0705410040d00d450b4400c0e5000e45861083c104070084030032482e411103403c0c2c4070595500b420841e80145244c9000e2520311044241421440051038444000344803002c003240c0c0c0b00000c00c0b0380803004c9035032803542c1060f00f12580b40e40050f5100071a8000c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 383012419 1250 383011169 383011171
    0x3100b0702100e0109051f02061f030f050f01050708091c050d0e0708032b150e07110d0e010e010e09040803090a17030f0601020a02010c06020d150306051e010806 71
    0x40c1e0f041c0142441d0301ea000484948074290030031a4030a5090740d0340250740c910410b1280325250b054088034007a4480d12612640d08c54070300b0700c01d10180c414000500000c1e0801c1414a0030758070580c01c940041034150000341c203582c0c040310755000094485080000034041040b1803010442d22240100046400300401811485030b803016000458540c030070341c1101807080080500800f54101a20f885d0020650101444010b205555030450760040004e044245240300e0f40c210408038049495850785080a1151160802410001401417066020700040300a000203441649680c0d00c0e0f074003030040d0800150105c0110714a150420500e840d0386001501e4100c800c81e08260894011612641d45009040c640201184001c20400308803000b00100c0c1204400385000c2c401c0000315802c0da64400d0012641c844d680040a800922a6481040466443c4d401848406211341c00410340038501c1103030300e420001540c82244ca082e5907004003e0440144040d605d404000d22250101652404010b10780e1000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 383013669 1250 383012419 383012449
    0x6300605280c080f100306050406060905010b0316030902010c1a1006020705010206010513020408030a050409110f03040323220e06150a0302070b04050105040c05030613030c0f050a0803100b0702 85
    0x54501c04101003905007080c1c1d000447d1b200340244035a160510740740001c0d001d648900c0d2a200c1c103080000c511880d84605072481007a8214403840d031207005000441c050b1120880c181d040c40b001c00701e80804102041c6104564002406506005040040072005406020350182003190800c0d4800c0c003040e0703404285581141d008854010401d05105d00d060001d02c51540424528400010b0700c0c0e07480c68001019004580c0a01400c200c030854440c54040e961240f00803d241c0a0f80030000034000a01a0b00740ca0218601c013060003506c525100070400c155480747e042100c00d598440c10b051400c18030705509001401c20b040441046040100c0800c0c0d80fa80144942e41200c4c0c0c01044d035111181c42581034a0225400c03182201d52801c2904059000745025502601c008220500200d0103040000e041c2e4000c4d8400d0301204600b40d0b09490440780055201030803141e44a0801c46540402d2040180b600c5181c01810010394900300440131524101d0707550302495122005200c00c4015988130140b2490000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 383014919 1250 383013669 383013691
    0x20304080703140322031e0201080403110f061e011e0513020c0102040f0e07020601260c0301050a0b01020f0a0305030114040207050f0c0f0406300605280c08 69
    0x1c07241000d950645c0105150a640096000c060b0080c110554650100702c0e0300400b0107075048090103003036044100903191b02a01081140c80480e00191050f03940850380054681500c068610400841e41043d00541d0401f6079119100d6605400180b1034558034014032030202c0c0f00c00062030180d480e8075540350f103100b914821400c04040840090079a01250540401a4000c660315500c407042c022000c2803a000300c0b0010000d003000200d180d400060001e0580306200342c0403501e030555525501e14180411100c0170075000c0c030100b43c1d4540e1003d020b09400340e5107405001c148802c07040002454059414450485540035055082c0800d40140031a410b507585080b400408040c01c0c1c0c00b00b80a03100b000001400e51081c040030355106080403901c0501030a04407009201c0d00e01000400042c0ea250380904402081a0090804030403400900300610358104542c24000055540340e050840d44111401c4600a4602490074100c40907054490800e840b100001c00a020f0b00300c1d0014249000108040544 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 383016169 1250 383014919 383014943
    0xf03050a020304031e03090e1003020402090105040e0c091002030a1205070c020d030809010612110d0201091a09090c12060f0a0503010e071806030b0a0504020f06070609020907020304080703 83
    0x124030a1040f02c0182d900f015031500e0308001c006207601c0008205070f003a000525400b1012810402c40c511481c003580b680c4024030016130568082200a600803144036043c0441003000046a50050a00911404000d040c1c2a1a1641c182c10300421019002d2182c0440d0810041080c034103070000c500c1c0c01440c1000c0e070000341c00d81c1d42d1502a2461030045101943c080410400c0000305580404005d11548001c0002d00565035100b00a0b01d03503140b1090014103101c400030b078482e218104280c0000341280149000c02c429130b42c6074038010187c03030402e005120b00080003c0180745804d10060072a00701c0c070321650543c54542e10f030b0003103600c0d48005803400d48205d940c3c1c0100d000c103540d1380c00301801800005000f0445d2440d842e1400350b0700d40c054850382110460000030f00c181050644200d0007280d401c030340304042d5076032656548030040a004000302d90150412060606940b1000b000e081c0440c0303c0c0000040721540303030040216400d4000c00480465000700010300009401064000450743d02c42c44100384 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 383017419 1250 383016169 383016187
    0x40602031b01020904020c0a0c05040501050f0d110a080a03180302090c0904060e0c130509070f140d0c090501080f090d050706140421030608120d0b030a030e040f090f0305 75
    0x6489250311043e1701c240041620040700707001103590b0200610603444112142e85c0c6e00d007032000f580c03030900c24940d01041980300d01045080901712020028814210604044c07100300003d10340310f2803031700302d00b80c00d038427440e188010141c02c0b211074214001c5203e000c0c0d0503a80346500041c610f1800610040c00c02001040b8007509450707503080302020308400d0440e9111031070181c00c4e04800750048124100158461400004c175400c1003e512030280c2c0096541d005561402c0c9015100645200100201c1010405ca50039a442131440f40c000c8030681360341e40701403552901000500600c0c01500c00b05500c5608014014a40342c0050148102892418004d490b28140c0c2085401800207001204034006084204810000010101c00514218110a27480b81801203011011a02d40740170380c9a4903030104086200140000c005041c00310850340c0c001c6469115400440d080c50101e0f041100460002c0c0310358841c03442c0c140182030380001c04d10010040110942c6a50105521544018013030010019001f51 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 383018669 1250 383017419 383017421
    0x8150d02270406020306030705010c020f010503181504031e0207091104051203090301230105041104120b220f110d142a1810080f0309030c06040602031b01 68
    0x80030001088403624502d81418181d01943c8212403680c443d004520000c0303100d41c0110000d10b0800e8014100201d04c580d604015101d42d800a0041000004265400da803141020800c00c0c5040c2c44d0800002501d0509240282413000b00c0703180e51519814880040411507030009200044480c3d072200401c070080303401045603480c07049070081c0b03402101c2c0c2d1042d042600d40000c01031111250075802008801c00c00400400c0d880b070385501c1d070010305291000402c450f140070b8221800426251701440d20305a54bc40d0810500710080fa81107642c1c0c0781744802c1048001c00c0d01170f042043c1c03503440030300180803280340e5509c00005100c040052240c8030103000d891a0342c96500c1124409a031240054821032400e0041c02d1b41d60558454030052140c4280c036016458003a42d00206c0c400d0009404000010485030741c0341141c01000b40210705002d440500002c0d03042e010090940600b03030300e402031680e90100b20141803d00c0d60b62440740c1c1c0500c2041004000300c80c1e0000454144400180c0c403007565400790f0210034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 383019919 1250 383018669 383018719
    0x120504030e12010b0a050301180609021302031e0c0a02030a03050c041a0c07060504030c0b070203010b034206010f11030a09090b1008130f020a0605070308150d02 71
    0x15045030181c02042e4462205500ca401d0118007124500328840c0c5e200b04260903100f01c1c0d440d0019955081c80b2020000d40350f60044405607100038000400d01e041400d94104036002100c90000320300c07810000c007018030080d501e01900508080103941c5002c080703400280d40c0e1f114148040f0201641d1381d0028024003142025a400b50440840200081607844101d200130340011403504a030f4000c444000030021700900803501180d91000e44d200019140041c48443d0350082c0000740d8140d520b0301c2c1003148076682441503039804810b1001c4080300e45110294100c01548003514481d02007006400286191040340d41940d202c54241b07400d410303000b0100011900440c10300b080340014800450f40b80c00682d0024080002d40b020050100000b104060410103405036004490011032580c40214a07460a86811010410f010fa440c19442c45415030100d02c03404c403031740c2c08840051360200b004003c05034410052078101c002c0040a4074082e0200340050401c0c038104000074480c1c2d500c1d0030684154072507c0e040b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 383021169 1250 383019919 383019947
    0x30c10110d020304030c12170d152303011a0907020a0f150b0612150f0303040905011401110c01202b170406091a0c0a170712050403 58
    0x788441e80425040030b0356a4001e8007080b1044c000000020600081d8561204040c5410100c4034500c104190341348400c660001d900d2000c051b40b030356000d844010755280b03101e0051465000c1c41d6009c1503c6e071000003865401d412283d2099041003129040185180c85040d00300c042140c020160752122032040c0c0c40c015042100614000e0101410010b02c00d03070071444040107410340720502c1500d117000d0800150340f0541411148602d20100402d80c80c2c510006421800c05c405050700c1010311200c8002031841e0041d500140d10180c807000107200001c03004d0b031102100103080c00c080c407000070030581a58456002c0c02030903041140d8080322824608200820072500c803180720588280600c41c01540940d2403414000c604410f0803240b900e58100d20420b000207041880d14010031154030303140d540101501c1c9002003500c6025110f242e2529090881162500800e4607907009551002c0720301c00a0a4101e411103645008040c0c10100300109401110841c0682045d181c005019078443c501520382904c00d6400e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 383022419 1250 383021169 383021173
    0x606041401030b060a0e15150304080304060e030f0d0e1b1003111201060206100501080106050909060a0e01060206190204030f030c06090c080f070b03060d0f060e010504060506120705030c1011 84
    0x40c84104401f04003081302101045d115204140013112512403a0310090703030000c200c64420800a03010524503440310f000c5c103448105480c07a02c580d07040c12600d9504101103400b140c9581d8a6080415101017040114194495107102c140c5184080080c1146280303601c030798249a103600942000b009050101d9207101c00c1078201d50b0349941c40300002540c0d504101c4494007a901c0090001c284d030340c003440c0610304903480b550320140307454a0036003406880310700039107017070780159500c04081000d9115100140c00303091154024030302450a01d1008012035480c040e024281c0c0d1040205001154a40000b006c0c903980600744000d64001503e4070320b0040803541c5000d0001c4100781c81c045094000820703043c50350000349007100c0416072030318580c860a1205440403035000d0300010544c030009003162303c2840c500b0b00030350000800c2c07035021410509540e0203c40c100c94050340e81c000c0003c00d2410a4000a9004a1000405850f0f05240102c1d030f894000140192062040b0101c42034420312910ba0704401e08031280c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 383023669 1250 383022419 383022421
    0x160f060216020907080c300f07120b0d0f0201110d030b011202271206130c06051c1802061804051b190516140606041401030b060a0e 58
    0x810702907403415003080703100f034070a0004030b0885485040c0150142d580d0100003442c0004e4515030104009529102c6200d008588000600301039a070920680b141490300f0303003146940350440000b080d40c1032444e0080d105a281062050a41d01d90325000f003032060780032800140e01341050005071000c41071084903843da1702c5810780191001d80d140c0c00c4140c24100a80320481010556a900c0c2c0582c025450401d03606805400721240b495103140425000c800007401114003904101d8299081c0101250070100300d41d56050301c03004004000107200024019864081d081c544030301d159012451010406601c02503c803801501c01311401640c00b055158003d2115030b4500d0402034140c00000e07400c0c1c44512070b619020015040e04904d0710613a5003e9009041c244c58050700c03a0420508040318a444010081c0a001404020f01711444c2c2044050080e1940b1548882041c019031510900809140c041e9041c030f541d100e03c01450011203410340791b10151240403561460046000d600c8603034400e80180b03000324 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 383024919 1250 383023669 383023687
    0x103110d0902010801090908070f081c0501080705152209090b040c050d1502030c090d0b0a0f0b03100b190b0d140f040f05011409030d060e010b160f0602 67
    0x141c02100942d10030389030190300740e9840307421030221001e82c0310103005501c08100c80c100140c401800309120a00c034020460501c0c03c694081094803034100b45624400780d43d200140404801048194001d28007251035010380c540100c90000540190141d0f44480601642c404500315100c80c518000342103240350400844009e81404542c3e0783d03058500359007140d00b81c00d0204642c10480041d80005070802e1100795124074041d804c40003540001d1509100d21014885030350a1340e40d4008006515010b00424981810f010708040d003101c100d0285c2214070740c80c00c1600784480d00d010814007568191084001030102c04240419002c461025100b0302c803a80030307680400c030180b5181c003030400c480a000e0100b110348041003500300c110380c1c1030702d0f044110b00007103000800050503020034811582c480c100200d0701c0c01801220f1007113807400341c3c0c140081f5000402d580901c5400d51080da401086540070240b040d5151070070000c490b01c0b522200c1100501e01c200c048007400015109412200d0740b054085544592417 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 383026169 1250 383024919 383024921
    0x20f01030c0e03010f1505040c02070b030c040503010615022b18030b07020d09080307150b0409050601032102150f040311060a091104021e13050916090b070b010608060103110d 77
    0x20707251185402802c10710214990805200d034032740041c550b400030030806080c000740020f03a400040c411850300074100804201c0341c80070b01401005014070300580101e2012840c010b42450504c6c22449501284c9003005103c443c0d601310040d52201031420468041034655a141920903901d400141001c40501d0602141d00e5002a20008030317425aa0361024590311244c8081c0c8902ca40903003c4d2200d03804c1120005140d0060b4048242248002e200088441890780c2c1c00d804c2c04400d0740243c6500c840d4200281c48150b0401c0450183c2090b403001e80b20019240200743c5c82d90380050440f003564815035000138101802020941040310b40c0404840041c0703072a83c2240d002c0c02c010801250940c5030781001c6031f0300d81040c0c0240d42c0c61b60142404140a0701002038008040d4022175070103600010010400555070301d0312458070713000e1401405a0141715030160406054101142c0c0710640e082401c0000c03c021840300c0580130705445482c03404074583c2c2c50b4000120701601c0b0a1088203800c03030340004c3c2c810100c03000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 383027419 1250 383026169 383026181
    0x3020f0c1507020f030f0f09130f050a0608190206220821070f0c090c030b090105101b1a011205010506030303090c01050d02070b090a0b010e04020f01030c0e03010f 72
    0x410703201003007680c0d09001241c4885a80007180d03c036503c1801080c01a02201000d80044890f0030781c600d00b44580e407400501d000314024150303802640c0d110340000c1440c000d806080c1c0c4c0b04030301c48024489949071050041e680c62144004080c0c1328071981040701103548a2044803000040c0485c40c00e00f551500c1d0502d4508070080c40307503840521a048840fa0b031500c00c241901d1460000402c00350420b550741d205c4c807884051a13001180e042404103004a00d00354284102007800310a5038000031800000401c0c4940c400068100901c00e02405130a0b40c48280d000c840c501c21319a8514200d440d98140d071420f00700582400000380c1454500d01300201e040c14007200103110050049000340700340d460380c00515491388402d680a03015604401621030309540100c000300760080112000503e800c013180c9130340c00010800d48001c0c00d00c1d04800c0c900c509200740c10380c401d0702410340c0c0f108902c0381d82000d5000036104850720b07200c241803607180d41d81c48010700c2c040c002e044091780d0050300a0000302030769450f9200900c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 383028669 1250 383027419 383027443
    0x120c01140d020f040914070e010e01020f0d020a1109062d06030f2502030a0f12020c1c09060c060902040f052d10090e1f02191805090703020f0c 63
    0x22a00a4500d4041c25080c00c01f07005074000d485030002c00500c100110341e002c0b905034109055118040c111b202d5420108030103082ca03000c66000e880098a180382c070861124001e013040c0e100e0300d9104103002d55607446c01031640c1c103207404808801c0d80f6003446c0c5080542428800505502841c003008100101d007a4404481c402d415115510030040c0307410100b20780c01d07541600c02c1070058ac414840c0c0d444042c000d20a108543c441420600310083c05015442d060740d010084050b100d8008a234006003101c1c140440003503540c06420500410303400c145006000c85518107019040d241c6404410095407141d6101c0009195154000d00007841c1007960081c11a60b03800c606807604501c6103040a02c1402c2d0400c040c010350910025491592030700c1c01450242a0b0f86482d00518080c0400c00300341810081e11030003103c102504d0240c5c541d031150851032101c41c5180c0a420501c103c21406004410189100000303480045440c008240c50b8030501700c0c02401181407420400a0001302c0c1034031070600280106581c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 383029919 1250 383028669 383028671
    0x5060c0a02100e1b0402030f1b0403020d05070302120708030f091206070e0906040c05032d010906061806020a02120102130e010314011104060c0f02040203150a05120c01140d020f0409 80
    0x2200c0e00c4c0a01c400c07403004982031017038094a42c0c040b901c80701d003076038842074001e00124100d420603460380c0019005901d407240031a655407049504000b103052922034480c5440141002e084030500d4659110340b03d204801d0034030507400000840161035070b61782c8032001b0788010f004100c4a03903141005014000b0070070f41028a2007044a00d0001e0300a1601e4007403c08060350740c3c0d442c0c50841e00d03541c0220404440c1000780d00b01648003043c0b802082403000300315500a004503140802d600d442d2400143c000303400038028003a2022107503c2840100d40004000c500f455069640c4030056604d2000580280070301207800c641ca400380070000480b0030007468000d050b01c0c055449102c0800c07000050340d00302c0b201561055100a000c2c0030411201d4007458a0009050240c1541044480d06500040032644121160880741c44800c55209681c144080340001412065607091040c90214107655034030500044428100000310036843c5c5c0007500141039441c00369000d18195111003449442d0b03442c0307800c0750090948035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 383031169 1250 383029919 383029963
    0x201060806070c020915060f0a0e010311040e0709090e010b12010203061f090e070807110c03030d0c11011109091b0702040b0105133005060c0a02100e 66
    0x22400100c0c0c018040d0700c00791503c0d0844640c580c20f015031503000820202007001c074aa150791150b11744500400d03412070922840b40c0d503115540340190203001d0680140d810146400a048030700c0080e80225410795245180e5034080c3e40e5014402c40344203000c0e401074a8518100240c15040384415000404080340484d1100310080c4c204402500301e00088801d25400f2007030b00130308400304003901c034006038001f01482d044602c6a1960032a0010400503240400043c51650403c0f001c00d5204e40d180f0041105540a40051448140084d6403409081040b0480d2035903034801d82905405080d00c4240410440020b2280c2c0c3d410110b00302c005d81200d04080c1c00b80d89420b0000304400a0a0130005484071007144050a00f403e0b45c09010003024400c01c2541400010010700842e04803200000340246291402040490302d2800340303003c19110306a0710600310783e450f030210f0005100405e2450b0302c0211051807584030041c0c5d007022482c0c0303014022000d0607540b45c4600b180d1994800b04852040c6003240c1c0d094890307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 383032419 1250 383031169 383031179
    0x21f0c030516050d050904111c020a0c0503040303090e181203060301140a02070b0c0a1202070606050d0609050f0c130c140a0f020c060f030718090e0307020f01020609071502070f08010c020106 84
    0x18034464007082c027550300840382c0170300d800e1440790303028100e889194034005c1c000446c0340d518540707190f1094000340c010840c80003040103141c86401d08954040812031061407541401c40365155070320401c0c5240c00d5071180c04000280b46c0d450035408000da01c40313003c105160a003000c0f00290000d50001000340c90540c2c0042c0000c42c14510b0400b120010f4600d9903030321400004041c071500c025040010f003154002c0c0c0380c0600103541c2c1d550800000500c0c1c000c03040040e642c6034903d00f00e441d02c00b01880c03440e8150081041e5030710b1503232610492452542017000c0880c0c071004410080f2110030740001c400e02400130105048001544c02003240704140707a00e13001c49001451400401007207008401808010070743c100001442c0501c14181982d094415034107800700c450720358040c1c0e41543c018201c800320550002c1101c006500d80039815451608081c0040c1c8280d060800545440d00d0a174000c031050190520307400ba07859442000140000c00070001c0020001d922040b84501030000340113694015030034048040744d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 383033669 1250 383032419 383032451
    0xd0e0a08070f0b030c0d06080d1710030605040501020912100b01090308040938090609010803040303110a08040603090201020606100f030b01090e07020307021f0c030516050d050904 79
    0x42a55402c02841c0061890a00d01810702d0380001c0c05d9501002050003d070342d00003801c0c01800e02824060015102d588030105009161502c0c800c0710185810814003030200420400040c4070a4903000300001c28140d540f0306202d070192080041031074000220414000e40302401240c9500d4015030260113100200d4081c00454611800e8080030f88004000c000401c4030001c01c1e842040d0444207803007403008440303c00e8040c0f030f082020607900c1c08048002d011162100d140055040c0c0d44207208441c0742001d0350400351295038900072800000c0074420000400c51030b00204120fa5441b141d80000d80703a0b5240e40700d0302d0050280c520f0b540128054829034000c18a246000c0100c85550380c00c65171000200241114210094800d044040303062045a000100b9015940c1e00585d100342c10940007566105100e106111500602c180fa99805142100070040c8540d400f4141c814240e415240c81501e44580030701c0a0035440702018014080d10030f060503000b0994105020b0401d13044200d0f800c003d9000f100025070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 383034919 1250 383033669 383033683
    0x5040f120215030601080a0902120729030103110d05030f18090105010509030c041a040f020a020706050a050a050307090e040507030506090a0209130602130e060a0b09061b0f0d0e0a08 80
    0x260206044600090b20031587d03a100c8050580002d00f07000f102d440020340c46003441d00ca03801c10603000d40854420400c3d007400e004e460400c2102c05540e5441c541c07450701c80508008011100e280315040e0000100144030702001954031900661000664071050044468524500c9003034490240c0c012500000e4658015001e44445d190040c000c1c001000421b010003000b0841d1100b0010001c15041001c2c11507104c5118054284104000c016a030b0500a4006890706003154032480402104001914034a94090155080060fa0b810441e84035117070b0605c140c407000900d421818014450340204002e10030002200803c40e40514160746107500c0710044262515620340c00650008000404a0a84507148017039410503030140314014140060f04071030412482e0142d0040e816411a5418021949042648400148002c1541601d03044051001c1b034901c7c092003140140b0300348009240318024400788100180c030351405040c1d0328003014840700034001c001c0d1240040e0080f085e034600403800710000107103c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 383036169 1250 383034919 383034931
    0xf13080d0906050910120c020109061b0507080c010b12032101080718110304050a03080105010906120f11040b0703030e060601021510031b0513050609130305040f12021503 75
    0x10311300380841d824800d400c001a07141c0c404200302c081402001d0400d500c07c22003406548d90002c1440c0b5911709002041c1c0b881c108007074004820b0b0000c00c04a6a40000840714015070146203c1d490b25105d0700100d0050110004046d0894030128865000c043d010004066483c000880c00043d400d150700160820301090003080410350082a05200c0e40c814107038203a0000560070004180b49021031208000c54005840444480e84415000400c0507040380071036001d40000e281c40a05140341c00c2000b440c241c11644c0b5420141e58400080704170030159040740721418840b800300d0b41c2e59652003d25542c00d5001400c1500000d01d09280c0c82c04a5001142090051005900510440d00c10301e944101000340640034404080302c14200000007089102c0304200c16100603d0704080714030f40814450710b24126115240b115140a04010540e5180000250000b001528544c540b980c1c03071505580e60b1049030003241d80780c841c0c220300281607500c01c100407144500c00d5491098407075107900f002c91300e4081941e0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 383037419 1250 383036169 383036177
    0x20a120324090501050a081b0d0f1202030c010b04230c07060e06060103050a0903021b01051e0a020d0207140f0409080313020406120510020f0f13080d0906 68
    0x9201254401e03045035510034101014080322007602911103107035018a034031420050340c076480108032501d0b184103420300400b44100540299542910801056035640f140c051051000c241c581041c001142450072202d40d100160064039107403100080e41d00c1c0c100220810341c540c28907a2050442c200390207005611101174034000115103c0c0c561320301402034010001514410144034090104600f030080181c6035100c14007802c21030915000040507101c1c01405a20041d08003004240003d80c0065880700e424041011041d00088000040302c0c1c1e03110f0076a6010307100070b010548004008081e401855800140e4086407171030380183c402aa11900340b480307050001203205d40d5103c01428080541042020300400020320f20000e41d0300d0049a40081d00c10700700d0365925210b03500440c205441032802800d24052280d80c00e4812f540e403250750740f00c80510341040d6070700811850f41400c0d076030341680c1001e062042e513103840d451400c6040340c540c0301314819041d41e4441c5504004859012781e803d03c0558050f070303036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 383038669 1250 383037419 383037443
    0x703023d020c01020c03040f15050306100c060b120106080607080405100e0c040e0604150219050f04050306070c0501050f01060503041e020306070905090108030307171503030a03020408010c020a 85
    0x1041000039009514140382c03554081010040c03c800520082c0060302d148100c0801031414104c2e40c4001d642c00f0b4916000380300c0c3c104140201507580301482103980c55a440c1420003603400e80f034043c0142c0300c84107210750040320080240c9405a41074000c9070a880c140801c035516650b804004850703080d030075600a0110780000003603404030354a941050300b82c02c0b0104101c900c84004a400700b0122241d0500307400c81c0750000c1d4140401c114240807443c5401c81d040c1410342c205100e541e45102c005d58001e850314144000062211894000c49e011b03a0300404005003030704e0862500c11000b0b00b6400358088102c1d0030b075107050b00060241c00d11070360035410380d5496070b206401c558807540e800748005c60aa4807002500e505924580041e0380c100a220310030982503580070305441c42c207414440c1502043e00640d00703c2d001401000380710b81d80403031856a20804800c01c071005445081c9483ca0349620f0250310790301404005601030155415400800840d81d84070300030400c40c102c000e0220385613141c85a0040c0059001c00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 383039919 1250 383038669 383038783
    0x3040215040b0a1b3909050619052b0803040c05090a060e060603072c1504050f062d190c05060103080d060e0a060812070c230303070302 60
    0x84c0b00c0a09035803000b400b100700b170816070140d43c15181e241d000c000d050703440f40204044d03410300c00c40c05456100203d400c81911410040010410f140024200b2001060000b98142004402e8400d2000d1134010401d181c2c1c03400d00d428440c4925169004640c05201100e001c9001ca1074070b8170904003103503040c00c42c3c124136807620810807207158000b400f02000c2028001d04158100803048454651001814403111400b41031028841030310400310b80c90804041c03d01c4104002d848400301c0802c900c00855805684000d520030300280e90800b01448503a00b0360810081c0700103141d0030b0080c80142d203190b071071103000451260101c0c1c1c02d95039803c006140c0e80213840100700180340b0101406004d400c041c004a0781d40c1c1ca61a14048040088441c28403c6407a0503041003210f0741800403003281c0c0c80c58540c09240c41880c5c0c50341c82d9050018411000365260501e007141c00000c44c0d60401c4480c540007820741b40d640c8480e0500964594000070300d07032407252511011328100c0d03511542101c1c11504114042c002684c1407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 383041169 1250 383039919 383039963
    0x9360b010e1012210f12090503040b0f1c060e1501020c15160b1902040b040b0d0b0a0326042619030807020d0305010b0f03040215040b0a1b 61
    0xc008100d0340481603604100e884c141081c6041884051555a090764880c88903005210032520502c20303016910f00302c601408150b001c42242d060342c0660300140e58072803512941b03e4003480750100c106060500f54032a000000c500e50019004c5a46c0343c40003441d5a1644030f40320390b503101190925405680000034401003820030782096000e011303452a41038105030350110b0006c0c1d9200b5812040b100401c4e40e0040084584c0d6101d0140c0710412003940840c01d06082c004003481d0303481540104003402001040d620f00b601e83d103400c0b40404003070240c4840c228039542e00c0c005600314403a4101030720690581000c640301411600942c1c088030002440c90180381c0c503c8407441880216070700000900e000703074818040c03224812a180c02c0054440c3d950f000061500360350081c1441c003042c003c1400c0605100c01007100040b1501a9080c0842030b1541c15525207840c130000d02c2c840c590b082400c0036402c0114001545166850240130000070035100d00c2a014001044003420b04400b550060503160490342d81c500103859 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 383042419 1250 383041169 383041199
    0xf030f0909040f170a031d0a02060309070915090f0e0c1201090c1508090d0905010305071e0905030705010327020307080f033109360b010e10 62
    0x900390f0b4081c01c0990b80c03611505806640c6140c000311000169843c8a035038180310b101c8408007503282c14000c0881c41c0781030341e032100d0b0b140601078458103011011905505082c0882002044c07070242c200034494441920400b1618144600e13004c0d1413030400f601504000601070f00c445d403440c02014004602c0300100704054201d203000550891f41d0b9a40021001800f040030070030162120b9800410354104c00a0002c01c82d2130014401c005a400001d11411183c1c1c0001c03916050ba60242408600d95898142c100d4408400546200540d58070700000714069401080000070340d0b105500b52481c890301c40300154142c1e201c0031079070303403d03000d900d120101e10030301c091546103440307200030181c03402c5981c0c0b4103035907143c0003100003102d030345030000900c0d00c480c000c0c880d03102107110f541d80086c02201c01e2240015800c08181d0721034400b660f915049654031882100e40302d4452002c01c04d02400404090002c03102d10b240307003000c1c2203600178030000001c110740c0e04080302c0510810001c0c5850b00340d1800c008651481050f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 383043669 1250 383042419 383042423
    0x103021c0212010906050604080a030e18070c03110106080c0d050120040e06090603100e010605060f031008010612031b0f1406060609011d0a09060609080f030f090904 73
    0x50840501100310038980018042c2210407503110a50f035050101ea08100c40643e0300c000e2181d001004104581200483c01c0800c140d098100518148001004200039400c954150300c000c451042c1001040d9401a519420301c03030103544c070807141c4031124007005d08a03061801105041e601901410b445803070001c000c0700c00d00b482640041214840300e0a80412044444a520203003c2e010a003030000400034800940d1001e400c40303c00143e410b040010030b4035468281c810500907a11040c440c07801000941200300148805000c0580d2400060441e1a0942041c0c41032540c208024000003408181401417009464008511910048443da42650b008541c0740c110b260b0242000410000300303443e00f4a184010340508515030701074004216950900c0c0002309010b110350001e1110224690780402d030222803059440d4010400d510000c0003804440582c0d00c8914542d08009020070710540c17082c022001c9408100482d6550010960119224011451074410402c800c0c813502076940b50640866401038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 383044919 1250 383043669 383043697
    0x6030309153103140a110607060603080a030207031107060e0904140303010b1801080103260909070c170307142802032104150504052a120615010302 65
    0x32800c08802041c05010240030b4014004500100300741306080d0070380107419401c0340107400d080c01d081e80d03070141c0b040d00d500c0c80501482011a40ba0100702555000707101840d00902d6050700c410030110000d010350701a560480000b2151400d208004100042840c15100355440b03600b400680c0006100460305c005109503502c51401c1c800c407408403014002180a000c3c6400c0c001e603140c1c6040018008124480030860411040f0340040000c640032481c000352080c001d10445071005003c2d00c4a00071801522140d07030b40041d034501808901608514140322282c420703c0c2042210150300b2021200c3d0000701d0320740000c580060481c90764041c0180042c001c1551010f844041c4103640c00380f00350742032011140070000d6400041c410368000c00e020300c4850240480c05180c4d44610b000d0361274110384030030f0903c3e529000744c0f1400170600300301050020b4440501e0400d0380c800a42c81c140c03007011801c41a0281c11380140000580d00ca4003c0c40494024400d00756500400449aa0b410045000b5400480000008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 383046169 1250 383044919 383044957
    0x90f060905100c021b040c0306081b0a0503030a0e040504060e03031006080108010c1d0303121906051005090108061512010e060f0a03151103010b120603030915 70
    0x2096481000200c9010303000411000b1038644006007295059440c00781590700103214040100c502c200141c04240083d85c3c0417031650044001540503005580116815014051140c0080103201003c0d602010007202c501100c20f40d0f40e0241600c03482554038507000208001c900110b941000d41100381c1092045100040d980341c112881810340d0406d603041d05c845038000a04100c0594000d180501510011340200040007070500007401d48198010020048021000600a259000e000361110494a078406405074989070480b00c501440d08510003c503686000c102040508040702606505286511901c1c900000c99006580c00380c0014481741d44410701c2000f50785010a80005007820440220484070b8a50411414065040c4002d0030b00d4050391480b00c5101040d42c1e00700148040b07070741000303011181d03007003c40350382c13001d88401d40d400941000000f000040c801c0042d4014444114103c524043e262202000c054480c0f064039042b03a030141540c02203002381514840200034141c1020147c4c000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 383047419 1250 383046169 383046173
    0x2130513080705031e030402090702010b01170c0904020f0a0f3e010f0606110a052508030406111005090601050609010318050f0d020604080f180301050c09190506070204090f 76
    0x31044591741c03170704038410210601003107041400100d03410080e5800240130000701d00d0002021910555a0010001d0000001c240c0701c072444030403a03551403005401907503610001d1036201040d0380001c080d0400611025020351410b84551020303002c0b0b82844044480242c0502e400c544010700b02c01360450313070540c100500303d81d182c1e00b403080d14100141e640c008a04185050000340c042e04904228414030b0300801041c000044010441d07480e455800c1001e1206d40403443c4191901c00c0c60b580142c1c003144030000d00410942c2d01300100c192036041410441d0640302a10107480144c0b10103032442e009551082e40180103a2a140c405483d203846d0602d0300040c11140702113803c0c2c049920b0300c2c00780e405801c0401d04060001c01401748200203580390004200c6401c180c5d6130a0318500c600088003d08246c0400c007600500c0f614200940a1580200244084e05081013072641940c0031403c8244150039403078207005000c0810039140c0440d80000c08860030303c9119002c1c00050001420125890b45a142070000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 383048669 1250 383047419 383047447
    0x301150306060510050f12130816120509010e0402030903070b04060b03011b1209020a0b07050f16060212090f0306010303050703020c0f0d1101020f0d0503040213051308070503 77
    0x40254000c290214803680f40c48240141c4045018660b4100b1070100f00160002c1d00710000c80780c810094034200e98241c0d8600500c482c40c074500c0c90307000b8013409002410401d00d80c2c010f40e440c1240e034003559000740110729501e8150748900c0b40034807260128401c094180c1c210329040c0e010710391000c508001c0d00d00d00380c0907640e001d20510f411170301160199990000048a428248510022410341c2c030111200c1c0070300303031001819905045004440c01d07510b42408908540b90b8501c188024607060813081d4075034106203040b5442d08480741c410300080c0304011104010f0b001d4000d43e00121a115005031000300d1024110403055803201201503044869500c0c008030540301000828000c41c003a0b0740300c6448106a01d002420514840b00071032240d400090b9403022640c90292150020781d10003815a06100c00000507420310348081d90f446458042d0f5440000070a8020b001035203e20304c00c590501e4865158038207001202c0303060700c14001182c0324026038000180c404000700712040c0150101c0b42000b10503d0081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 383049919 1250 383048669 383048711
    0x140106030311010609020703080a05070c0b07080601020c0a06050a18050604171009020f010c110402030901060509010504060b0a0c0303110301121a0c16020a05090f0f070e100e0301 79
    0x1c001400152110b00c40c0c0b0002c0c4210b5028080000e42035141102d1034030700a01c0310741e001d4000e44199985a01207800140a00348048850358441c140c0c4240d841c200704050300742c200c1151482e025000d91046c0807107a152900040781550760741c1d114281400c1401d001290100c4d0200021fa8044d450800080750716690080a44020008003031107103000c050f08610b0034285016455000c50150810f411000160355880742100c19010a29048403030119900741070503951140180345800910000511042d4441900954207640065545034000d9076075505100840b04148036045500300b05222009986100301030900100d070107854041107514060840050755482071744040c415443ea168071404100d040340341c000d01100c640040ec0c00074905081d140045100303040c0c043d0440b00107401c0403021542e4a41012018043c040c05036045440c000c085625851001e4500102481464000400d0148207030080e075004034000c0c0100900024082c410707170341040d918410a60554079031a08002d2203250900300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 383051169 1250 383049919 383049923
    0x80c1803120c0f0303042001050d11041401140304032d0203180d030801090c14041418040c0302010503041419060609020a1413080f10061d0f0414010603 67
    0x6a0788500014200b071504464220400c1d00360800c1c006c03c004201201d03c000803201c05482409984110000100d540b449964150680306240c0344000d10755030494400b0700166040d0042c01140307c11039000641d04108911740d074041e40d410030000600000d214121010720320841403c61161214020b1000d24181035200480e00160b0002c2402261800e01c108502e920340008e07151544046004c0c0c400500140050003000303c010b0320f0f21402d50307031a4403900780064404140f80d40a0389a43e2140d0324244541c0a403508544070b03000c0c12014800d06000a07070098044c603400382c1c407514818555070054603150030040c410340d032503402000a4948648140244440304800d031b074000103685108c1c0780040c00c581d403d401c805817481c0f05020032a45941c21a40c8000301443c031555564950350148180303202003034140c0020f065030046a15491139500001003140d19106000424803010307845042444240035a030211491046030f00005c10498030409070460341260207280c0c040703102034a8504903402d4504991003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 383052419 1250 383051169 383051203
    0x206030a02120f040218061504080a0b1e0703050603010b060d09030207060815090c04050a0f090e030f040b0c0f0115050a0b0325030f060e190606080c1803 68
    0x3451010310300e0408000e50043e000d05041c2031074249900422020f00c015003102c1c88540500e0045040703507075180d0301c5805542c00310b1152640c980d100c0e9665901c401001004840e00459130ac04a512450014000705102241047c601400c0ea2070000442c05041c010707100caa0103541c0c44500c03840d90f0700c804004041010f5074480201707400f40d2510380240b41004551000e002c02c51060b0a11962035008070f400c494554040b540756515454100c01c400f454403d0340d0080e07030700c4030403480000360709214080c19900301c0d1450038042015008003410147c4901c0f4032500c0752842c0c20304000502542840c0e002070040c081e200c900701d5000d102160221070071202000070400f0308690311601001580350160218014040424a16045040c00c1014500300e0080c294046954003e110509400d544260700c0080302904000b000e020059880e402d484003041c040e190294020070041d402000c020b01801480100c1e00c0c0c660310400d547da1002c1e0100c041d50000741a15424032092030340e0001656040140074040e148840d6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 383053669 1250 383052419 383052427
    0xc023c01170402031911030703110108011509330e12010e061303020f120403060b010815040506030a0512030a2d360c060302070b01031407030206030a02 67
    0x14124820000c14088075115120030040180c8000c2a00042e1802d5071440c1d41c2880244c0c075200d44103102c58250290140301c1c403a0008140407461403000019042070f21000ca80b030340c88522641c0c120440c040c854012482101c4200110500700500d00310255a92001d031984020482040c2d912001f0684410300140d00c8500405081c9083c40004281c0380f02d480c0200001241e809066482c0c1d40000c00c00c0d459050443c02c0c050500d4001d101e000f0655084005032424000d00c000050303c9604a070005895003407403d000d00040d54003400442e4014054404c842c00c40c55202400c01c00508002000150540203e07100e0000047c8204441104000c082250903101d02e84940c1c0719044402080401407000007000f4280c541e60a840081070380c03181c4040d004104d42c00000d038088100820340001500301c2c082e120300c04100011141c61003913003d20401c141031540d40c0e85c0c4021001d03030042c50809801120003100400000302403000044149010000351031803150349400154064004446000240750005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 383054919 1250 383053669 383053789
    0x3010c0f1202120a090512070501140109090b0610051920010203040314090415060807030e070501051c090f0c14041e02030402010c170d18030c02 64
    0x400c0941070110014000c5050615403540e01c010004090590307502c0320b680b4102813043c001d00740b00c40303001404403092069440103180b91141c02000d100c0140031425440400204542d4690301582c0c004640040e20442e0700c0e22044200310a110056410105110b020032840040710314402c1c120f80c810415458541c18201c45009440500610605074202d0740d2041041000003600301c00c400511035203860314141c652403010080b6000b001e02c0c1000015156040100080c0ca580c0007540e5072080c10703aa501484140700c001001035442180380101c0c3d012540621081e0100c2089170f0360a512141d0400002c10f00300307940d84a101f040000081e003621545010346041c080e00c400f07504011100403094400f0801c91840640b404042040c0103003804c0c0054000012a0035603204a200c0d003403282d04407070300c02c0413000400280d040503132010310396a011302c1c1020300d0300250061070040c424100f50140c40303a051552241d805c000243e43c2250340d142480044000401d2030860141a041c0050145900c05441034088 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 383056169 1250 383054919 383054927
    0x9050a08011a0a03030c0318030b0a0f0e072709150204060f090f181b030f0f0e0a02060f040e040f0b01050d020a51090303080708060f03010c0f 63
    0x40307040b690051603458410000643d00c0b00c00c8a402c55050b203421240d00d52884500003813110103500140504409000f0301136260b038590b00118900084000802014151460054030744c070b050703c10396a8004c07608040510310102c4400a841c0070b584000700169100d40c070341e91102d031b03003a040e0191004154041414080113070040c4403100d00c2d0002c0e02300a0f080d40e24100c501401000d042c0280b12202c640c01100800300466904080488200103613400300701c801d0080d005005080f0701640300c0e1006c4c10003010f8192240c440c8951481144070340d014001e8440550280314032580582c00101e070b0f4241c01c0000007860104c85284ea80111701c521101ca2040c10715003864201c15106801091080728450400001039944460070b408807040d5030310400c684005243d1203403110000d000243c0011606002402e021010b4007084025941c400303031030f83d004402d000f804407091074440c000180030850810105000a0059182543c840401031146404803541000701c0e00390380301c0d038045401041c0740302e0f100e11000fa00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 383057419 1250 383056169 383056211
    0x3060c030124030b031506011e0503040209040c0302090c1c05191e0f02030405190305121b0c1506040c0e010521131a13021009050a0801 60
    0x1088500500355410240c0414a4104888038082600d9103019540041e41c002c0d00f1a02d140314008064a8200d00d2580c41e1041c5000201d40c0e103800101c041c8185000c0c0c03140040f9004e02e0350030710740d00c003400c45c0c2e251341c00d0290107a40a4020303591030b061580004016a2404005031140d5540b55038140c640008580f0300f04080c0002c41c11900440c00d00c020400513075581c6c00840740032101d10801083c01c00010011383c000030554440038103031604104e1540040381264000314001c6e03224000300c4100c0d19220110071418103110500a00040c0c041052014141490403801d4120210744980f012030230120703500c0c814030350115040b0b006a03004100701d1583c0070300004020f03a101c44140e0301844400c0c4901d0004003443d0361402283e0600c10081004c07038804080c81c28010380b0450046004902d410000c0e00c0c1c015030444600100e071010300744103c9910030321000504038001c40788047c241c0d402c2d000a908003c01580002020000c10002310000940c41e52070007060310052101e20f0000401c010070002488650503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 383058669 1250 383057419 383057431
    0xa030e0a030c03051b030406020f0708060403050f030406060503010207030c0302060703050f182d19020901090504060f0504121803020607030f21050708010e09070b030a0e03180306 79
    0xc2036803000c01094001d00044509039151a045a49511404145144032440b1407000748906c000b00e000300b074442c7c001a0280948001201300c0d51115a1205c0c0d1a56620040701c00800240040c031a04100503c054051a00b00c2e214400c00304200d5201c0c80800c1c226000b5100c10343c00503c10550b4041456018801c01e07800100c9840c003801140b03071516201c0d444520143c04050010350070018003012510900c40d48942000716042e921340c031580441c492080015a01c41910030b4081c0300c2e0f41440c5101000800d04050b580a8810b0600f61704c0d04445400406c1c00500a80b40303c0c0d2600c1c2e005101e60020311130284076038460310483e0070303480c0039400c020111002a003400224103c035400030720260b91031105840b916581850a242c80c8041d180c0206c504400742c02c400168010700744d0b1404460085600014850082c0303907612203450381e071039044090481080d10002c82c940c00006041c00028422402154415202e002c0440c406500d001d084d40307558041700740110300b80341c041d180b42e10518080c007001c0d81000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 383059919 1250 383058669 383058673
    0x603060601080712241707210f0f240207021e040905060108030c0d051c0c051b06010801060b030712090c050603190b120d03050606041502030a030e 65
    0x100d8420006884400050083c406124148074442071150064004a09180c40056288450b11030b1012001040010303002d025401c000c00480302294800019801046402c40d860341d01d100900201041a45d034079070304040c0c404601040c01c00e00400e80704520308088502c01e2030800b109540b00c4100060f50300c00140e200e090b0b00c2c0100030000c056651507000000314443c480d00c40c164612000000723002041e09400007003c90180c84000219520084090318581094000f42d600845981104440c2c920802003010125401302c4807243c1000040d90011280a103181407161074240d50a84007075031505001110740d10341c0d220f00014413a400007070150318003c00b040d0100d1415403c024002804000300b240d110149aa03031400e0701018090084071010040001400c00d0380e4a003080b03079001c0c0080741055450510a42403144210b05810300410103030100e02214064440c04924503400c4014110107030409500210038080400c103001100c07462580b981740c68000350752320000d40b44054142d480c0310560301215 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 383061169 1250 383059919 383059921
    0x12070e0102010b0d0b09010212010e04050d090b03070507060b0405011e0806040308040b04050c300a05120901180e0615040503100e0a0b040b090f01061d0601050d021908060306 77
    0x948403003004c4100e441d0b01c5015000190307a15040729009004040035416216040380000540c080b60000160046014100703581001d1f40404041c2c4915055100d55280c0310300810015820314490409041c44030700c10341c0003140e4030b5180000101070300c500382c008135000c14214001e10300002008500c80010050340d40034180a11b0191006072000b640140068046501e40340001c04000052282c0250240018201c105e05c6114082c4c0d441e4440e4820107d4144841400c085510300000080640040b17034414002d11210000001018043c3c0103c011907062240384112112210804e001c4100504101c48020b02546030140030081100364811040c0c2071a10200310900081d140420005c1c00b18165603400300d0004041c405c5149041d86032000a00600301075000c0c40304000084100502816047d02111010404481c00500301d890314426404a654074000034146100603203a1203622000505000d400c2030824900502681d1000a1031001c1082030302c007400d00749d9001046190407139000d500500003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 383062419 1250 383061169 383061191
    0xc15080c07060c050d091a0c0903060411030c030708031305100e040908040302130902030c06120411010e091021050d08040c15050c010b0f030d080c070812070e010201 73
    0x1940315030700020344925114801501c1e010b001e60b048803c0d061004e24200710641141c01d0103074046107210082c0c0d202414000200e0003140c8104242e62481e00000d014001580701c940d50700005810418a003501400f81f843c0320b0803603a50500801000305030210240d9541c00010b07803982c00007000745d00407500c075840956982c000c45a10008241c5114030990300040c00850301d04041d42140a41e60000794001007a880c0342c480c040e20380c0c000f024080d01c01c1d403c070b038a088848402c014107030044e04555040310b2440800600403076199100e8042002c41030400058407107a07000800c0d42000d0845000303906081003002006070500341d183c0900503180442c45100010319a43c1d4803500e406080540380d08000c0303088089414000e6001902e0010480c140604000022030040600a5004181c6101b004c0d444c080c801045814480c844200201000300a07200405564805840310100500040c0700d050050100c0d60000b05803030300801c0ca40d0302207801c1d07003110b28207848010a0103010240380780c11a410881d203000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 383063669 1250 383062419 383062441
    0x8030403150c031808030411060c0319030c0c060b150c0d0e0901030b040615080d0201060e0105040510032604120506090d050406030207030203120a060303110c0d06020703030f05040c1508 82
    0x3004a9002812a60707e803070701d00b0017003802210100700070303801280001c0004106000000400096211020310382c00719110040079000c990103a0f00300c5002c9400c0d801c2c1c034800600380f9485000811402003010200d80c03040428003040c0e0300824041c6130030f903200c2da50b903444081c0c00c04c0118000c1d84d002c40d2080503175811959942e14040c00a00010320460303c820940c60800660750180d4003514048003112585c2c0c10404000340a010303244a03100c1081c0420001040905140c05a02e01c02d0010350028001d81e03265555030100052325244a044400c6100c403210925583d48000344001c1c5250600001e40c0c00703403428001e0500d100070341400143d41c412800300c268107030400709031800c0b0703021410010f07120001d504050341035104002c41ca60706130010360708200049806901c01c10031380e4003030b548140c86a109903841c40d50301e403451086c240c0d01600c04100e82c0000343c80c1d0340040107010701c0380c540418540d40c0c04140d00140e0701c05480403600c2114140d001d0084c216804081c0d1405049450804210b040501d0429 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 383064919 1250 383063669 383063711
    0xb0a0b0f040209240a1803020d12021006030f0b0106081302091f03080409060602070b04150c0501091112150c0a050715091a0402032508030403150c03 66
    0x1034011500031418024980c1c0380c0208014244c07000c09140c840200c001c1c0ca80d61154003180000c00842d020800fa03c40041540b1182d00540e07502908000484031181c03500c0108552030f610180443c0304a00700d42c0156501c074050000214481e0b040c01c402258076240143c0d1414050304594204a200f4007040000110341c0d41c0d9003803268069805040c0c0b600c0b074000084226400c01c808140b0b0743d8140c00004104040700004108442403020104899501e40c40c0403030301c07080244120880301e4030620050000071070030503074082e0688103804c1c09290001e407650340078259440140141da03080e00c0d113450003080f401d007100f94070300c02011203000e441b41c4030540c00300514052015240300d2a101c5e002c034407440d10038040e004807050315401c58821009802c1e0a80d028014114075039080f15840c42214455a15241d14040c2c14002c42e03004015203820380c8004995041e80181074a080210700062600080940d03084c8000c00256008080046000303002d1080c2c441541c0f001d17180a8205807401000040d500441322005e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 383066169 1250 383064919 383064949
    0x7110316060f05090f0907090b1204050105101d0604060f03060506150922090605010f03050f0607091806050a0b0702120307111507020a060c02040c0f020c0105160f0f0b0a0b 76
    0x90b10b481d451f01c071000c1750040e41075045048103040c00a0444160b142110306c01c2d01ca81d105100a00007682c130b16002c5a100481c030f200c0d50800040000002d007110041c8403800350300810282c000036080b07075640074411000d40c0a9105880c0650344205000081c18803408200e4001c1707260803858901810301010420055213141a03400c0c41c1c4905604040da19841c0c0c10034030142c2e070000c205120b0340d40c45083d0740250031218401140c040c0702e40b8004283d0b0705c0012030306900c10f8000b510380e03983d0a49000911001c16000300505004550340d03580200343d40d078505c454100640700c5000071a803918074600c1400700c002e506000c0390080e40d000b80f01d2080001e80d10710803001544010740c0c0c0c0c480f4203d20040001c05078010350308000e600801c007601c00310344a940030503e0fa5115008640a100c0507507501d206692a0404403d81c4005810403081061716500a40040c0341e040d13003642c02807081410380e8480d401c0002070708204444140e03130200750380c0500100000980d0454010242000858106000079a1a2408102c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 383067419 1250 383066169 383066179
    0x10e280b13231c0504090213050a150c0609051603060506040b0418030c15140a0c03050f0f07090b0f03010501020f16030f020a0e071206060e06040b07110316060f05090f 74
    0x10030342c2404c2c480e0f0207072001030a0f032040c255201c0c400e104420407070718000d010356409580b12100c000b0f078851281042560b203170321030340b40c180426040342c42d00ea019000c41d92003907803944a00580f200420041c5452107000754082c0d400010241040ca04010580714555401403044e42850001181c4103040c0c1302d521405989030420f9581d0510714907080c0d03045080c83c0c002040302490030040c0ca400b256100810361040c0c1fa5030008211080c40300005804881003039584020b07a610117000221181c201400803500003c403410700c54201552402e02095540c011242e80303001c4a40400100020358041040100ca00d850700041d2144a2461101c0b0000c048140700203003401710030000100941d160b080c0100040e14000900d17034054a800321028048084c010035400390986480300000340700d441040303050703100e01000340a241340501d002680311040d002010306032034421000300104034568003044104000c0c004c501001180b28030341103000d40303200d0306a00010240082044160300b80d030384402c00850625022a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 383068669 1250 383067419 383067463
    0x803030a0f0612050c0306100b0a0e04110a0e09060a03030f05030601030f0f050613020405010c020906030102041e061e140d1103190b03010e280b1323 66
    0x200200540156440041c141d43d691540314140100400c44d200c54a006034101c030100d4450089100425483d0300c5043c10552051180242183c824050750404600050010072800901c1d046400e03964403406440700820700023000c01c40c00f1700305038500960202040703980002c0186540c40c09483d0701c0924030380c1c8007007103000400994580e00952211603e40c05118081001260108054000b402c042e10761500c1010f140c00c04407041c03056402100d00303680041e960000296400c1c1c1c03c0c003003110b80162110f40c2c50b5401f40004204680030300c40041007507080000164529103020400b80c143c0c10604452400030046002a0b040d950300288035003070701e01c01d040015a0340e44031750000b04010884ca0b51541c4003210300100303010f180c030303030105058800c103000c90f1003045000d40d03440c2010700301c03206c1d18441380b00c1345c105a074540c00c190050004e490007603011100507011400d043e51001c2515034122201d40354a01c503c40c0c00720900511203159025041e00f002c40e41078514040b80c41c5035948400503c6001c1031b121b110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 383069919 1250 383068669 383068691
    0xf1a010906110f07170f011109100306050612011806080a0b0405011e1a03030301030c0e09190305131508160e031c02060f101401270602160803030a 65
    0x40f814020300d2072002a1540d0540307500c41c0c4904d240748007000701c03844d10640c10000303200c0c20184183c41c00c00391201c081c54a0180800207120f80c40203080769080600d96a0380000426864000c020f0510054007510803084dd810980e110f1850000030003041c0380310b85084024004508000389291000750032000b4400c0598443c64030300d01500051880602c2805841460041ea11b0710b40c01081e000e1460070029107aa10303034082815600d0109210203400050344100800c542c1c82c14985064010805905448051564508000c45d807500c584003100003038400241c004507882011030f11805041a170034661500490b101000700b01c14009041c8a100200c0e1619078001c0900501c5007001110015044c0d4480e118070340c040340040b121100d03008015024401c00194026040d01d5441e12403a81215588601424810303114401403295010074144110f00c4903c90010400c034465140c00c803145d007103200e1200c1c24110002e04100c00183c41c44c034004906501071041803004403e50758014a075583c001034510b202 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 383071169 1250 383069919 383069923
    0x7090f0317030a09052b18090905031608030f0a050408032707031a090c061803030904050c0c0f010b030a0f020d02061201030b0c0319020705120d0f1a01090611 70
    0x200400174254450511070341803c1e034107010140c0c01a06018902405468200340580d0030750b00300303403d250001da00054180001591a4486501103001c0c404031382c02c117107410501624070503024800b40c81214000c0200700c0072491201c425680001c00d242e0502c264189581d500c49075001c058411540d010011110054031a20a44031083e6030038441c04560000c1c1d602c1c10042040e0084624007000c0c03899407000507100c0d0380700043d4100b03005400303050760340341078040318910403500e10900d07140b60b141c001003000300e040d680c403409504e00440d0b51681c1a1b40d11000200040e1400f030341c002441c2000d9060a00c1c03180341341d50102c1d1307182105804c5a10549664400d2001a000c1040860300a500410103c0c502d000101c01000c000d0589228046c05509500e81002c8041e0a0004440c0c0040803512a00c80416051598000c0c209030f0303210b40100d40c0c11014400c03807540c454001c8080c0c0c0d50070071350365610200803602d02c1c01049020100d20101a90855824000074005c02680c020b220038040d000b012989000c000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 383072419 1250 383071169 383071181
    0x3130308041703132c0a021b031317070b0d0617010b060a1214040602030727180b0306180706140d0207020307090507020105060405160807200a080307090f0317030a 72
    0x20500d007128130b240050840000b034008c281c00000c40c51480401071500c400000c100d5030b8068144010b00c002500d040d12101d005880042c58100c91b015072500054000102e4010b00b81c40100f044000c50781500b4900032050f2051a202c1c108442e038100b52808069840301c204660000c0c9280c50107414103001054a0005840b01204100c4110403e0040006002d001d601031800f4694079500c200c55914120044c8444e0b02d0315540c90307082101004001c002c030b00c0080c01a11220741030840c0128000204c40e0010f400d1100448409842a44005041804040c02c0c40818064034460070200542482e1425a800c03078094105041c401270341c0054514190754040060390700800144006100074034100340000d02030039080e14024091400d200c042000e1650b0001c80c01103580c66070341c4508641d030303460108076200c8a20380409100b0800401ca000c55030001400b6135001940030fa1800e655030700300000020984252a4400c020010408009100243c100400e00e407075140c444c21081c0d00c903142c5509a034020a4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 383073669 1250 383072419 383072489
    0x1051002031b15010b0408070b030a1803020f060117030304020f1903030513060e0f0405040c0515071428020609040f05060123070b090313030804170313 67
    0x4001402c1c1c140394000001c09410700c0d402540030410b01c1c0d0740c07070214404034011405004e910303403c030301c03410301280c170402c030155074000410313000480c0b005a148440000154504030507030068100a0031501603000c10001035004113507030500c450b00400e490510989038000a030000303104030710441084010f070760340c65000854003078045122040d0560702d20340940184d00008104816840390000012031300d0081390300c1c100e4410007070040f1b085a2807860401000b414020021540807094005c003144ccc98644101c410301072114410381c0c41e80c0d5801c0341055a1007102003e044c80da16844003070400c02101c0d44e0181620b00c99400048001c14040070301c00500c0303501500d480341d0341152030100e11100c024a80c0d000f580c05802d0a0701c0b00b000958100d9550a0641c1e00c00140d0260504200822000a888041100d80c007a4413501641e050200841c0b4422000342c280c1d00580701c0781c034007080c103214405c0c108510b8440c400581c0021440d041400450f082c000b006445010902d601185045410041d5401d0400c0908 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 383074919 1250 383073669 383073697
    0xf032e060c02042007030f03060303050708090d061d1b150f270f090c1603140c010c141309020c100e061501111513050114180102120105100203 63
    0x21411307851011458004032401d60004501c0a00c0592031402481a1801c1c0c0c0e0f019034800740340529540390285c09a21501d003030303034000944000700c0300881c9251103210314144001602c01505c0f005030a9440c80d11200440c1c0c108005481c0c00c60a04a580e070740100070101c260013a48940303d0600c40c80c184c055002d0081c4080422000310303101c600b4000381c200c0c0030703a880e0411916008407148800034032560700c1d000c4811040c2c6200c100801c00c9010221092110560300ca071030034411440b4528140c1c0d5194008901e441800c0c1c0d1100038040003e50000c154450184400b5101c40c01c0c46041441004d10b154584180c0c48415400034849104000c02d1242401c0400c2c20352003803194044200ca043d940c1c1d101103a00b10461010b9101c0d00d4000c0d8810314401c5088855940204030b010600c0c0840e91a40341c014024154001d5010b0f03c290000f8000e01424401c0c426002540e0428501181111111a0340c0900d0500b0fa901c104800141428801a03150544505403a00b030b0403400103200c103a207140b00e11a081070500e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 383076169 1250 383074919 383074961
    0x30807200604120302031303050c0f07090504051203041502090427050d03020a0507020f031f090c1202030607030b0a170c030c0604080304090506150f032e060c0204 72
    0x30000010403502691062032a291680682d10088080380010f4a0b0303140384100b4098010080391240001d0002d0070300590680f4655190340b0085850106180e11400f2070580f56030400c800d0003c14060030042c5544605000c0c9503140c603a543d602e24074441c050b51048140d010500e4891500c2c1d0350301040958401000000100715000000804c0c070426030421170b510f00c10072031181d00c0d5520074000d5900c001c0c1591100e03400c0400c59400c1042004601415a030588207050416400344101100c050b500d40b60101e000581903418100510355610540101269100e21184032005880006072070f54040040d00d00014401e071103000151090016611240c03400c01000c211a1115001140780c8200d140110102c0f106103003603805100c00b6000358401c0d00060342082c04204a80100307900210b80c42903000388411211400031881d041c04ac2c00070b01d0001403040c0c005c410400705010049940c101042241220714000803489410040a00d05010390400c04c8101404d140c11501e403a0401d0041c1c0c507408001d1054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 383077419 1250 383076169 383076227
    0xe01020c07050a0f03170f0a1d0114030a09061d010e06090f0607050c0c0301180203010f1b0327050a0506010e012103020a02030609061e0112030807 65
    0x103504100d402024a0003001800251450300d015000d00f01e07200f40800000c104d2858980d21100824902644807091040083d245400d500d50000c3c0340c621455120180320401b81c40e214085e1442007510b05040c0010110007100f4007007a4000c0e030750700030820000400d40300c0c0a0701d8000b016280c881160654504925454255040190050f042c210b00b81800c481c0f561342d40003040c0382d03580305e090300f070f030249422860100303100302d01c00c4000304040751082d0304403840d021041c1d0110b400c40310600300410f104c0c464188110110f1034280610030510340601818000d80d030080303080c500304216088008003890742e03402030907040304850010503d055040c0f64901285800900701f0589414400c0f9007112140106000030924008140081d03059414080c4450207946074950300c0031016100c900198254031403800983c0050307404000d5144560a12805006c26042c0240403845030007100032001040010309005010f800003101d60380345810f0309807034411003584611405a40d49440c241c00d121681c0b41423007810b41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 383078669 1250 383077419 383077421
    0x12050c0a29060d030f14070303021c02090f04181703040309080a120318020d0507090b0103060513090602040f0305030715092103063305030606160c090e01 68
    0x1d1405021040c584600340c0e054410031200c4221a01580072210015590100b0702c0f80b5480800c20405042460702c245084100004641000c07204400080c0c00160602e40d02202c09039800841c400880b09500f424402000507020000385a152030095a0341d0286000314105092402401500105484002c00002c03256200c5075008841c241c02065111b80b0000f9003600028900300c0701034111000c0b030440f400c1003000f200900700610884280784034101c20000907a4407a0704012140b441503004004240c6072494500681d500c0b0611035042c1841c02c1010000b94507503054103070040c401404006003007043e07442c2143c000e02031a0070801c050401c03407501004000000004112140c092081e03504078844400103032041d9181060018911238005250708d1404c15480071601c4004c10501b004164a40c546030b400b07581498585105031491185000c07c0c6082070581c01c0c0c150001c107940380c01861031600c0004184540f15956003000c03d0500007810b00f0601454081c41009401904030a02480e000c86181b64 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 383079919 1250 383078669 383078693
    0x130609030507050303090603011415180301060605030c040b131509090f02040b0f07050a080c0c0a050d05060f0c0f0d021206030d020d030c020a02040c051309020909010312050c0a 78
    0x201d103846000d02c0400c0c14500001580c030040d60080c02c4902c0c3d40c1c20003214014030742240c200d07150070454408140407039225040c00f50001743c2e800004034801d008241c0801d400c3d40d84030781c4803006000b4108144500c2c00c1c070b801e040300c05070307400c202841c2c3e07640d85100021415480a40d005510300800403001119a40d8000859030407140a10f600703020307410740086035008900c6284140c1080c020104508024540103a016060303450042c001c0e607014590796150031180798003a1301c541e90160002103000015250260800000d0070043c0c03400303040d071181ca03070f40d1a5884802406d8102514503440014803440d00002c1298010200c119603951907032203045a03030001c0d402100c50790f506201d102001a80e1410f000a00401911465005040030121204143c000f095202c0720341c030460107216050005038071103011f208422291690b92940d520010054219105000d80100c80024010003e400c10ba5503003151160541c0c0d00140d000c0400031860b142903880d0b01c91014150001d004031816441404000c3c0c60316 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 383081169 1250 383079919 383079923
    0x3150d1203020424021e01140a15090203060d03030b0d200a060e090403050d0212040f1e050a0305281206080c0a030b0604020f03090609011404020f0d0813060903 71
    0x1a809001c1c0d00c107544c40c54084910300590112041110b10030102400500da1415100001801e215090290b21943c0d02144c600c100e80752500550560040034035011001881c01010846c1107003000000508015860307100038041544513840076089913503080c0d0582100c2e910002c00031003101c0291a02068100d0688a02d1040207041c81c00100f182c0541c4481209220003011810159103a0390f060358075400601007041c034a6424001500340e184503403851030103980030751000c4640c4c2d00f480c507110010b030300c00075841c0120851b918040c1000900004454401d103a060511070b032291850740e26445141d010052648581e000c2141b207500141e000b405c0c10141620301c0606004064541c01c01c076544890002c0141d0304200100000c102007444480550b406c110b0060000d0300e0601030203815411900701380c408864130b40010060001240c02403040780c200e00e4203c03c0720680b900e00b035000030704584803d1010030300401000e0f5040042107051000c8404660306207800c644816102e07400100b481c200c86c041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 383082419 1250 383081169 383081189
    0x5061201050f1807081f0b040806181b01120513020a06050a020705040911030a0b0711010501030308060d150e0c091e180c040519050a090803150d12030204 68
    0x10b115541000c03800354041c841c0b80d1844000036210030710102e9092900500c1602005046903900410000f50482c0f1710007071410001c0d1039202c500b89107409041c2000a812640300000d541d2160304808030128039806907511000000310035124420051b29425807003c9185052460039040000038980804101d596500a4582d42c0c00300c1d855043c00c2d90148600043c60001d40d000c030204014902d443e80004060750720070500c19944005260211b4030f00a0032072001c5929500640400c0b854503032140840284850b114020300503035141d61030103048031002504550080c034210a290303080c02141000303100c040e100300600700300401895041c0d680b51624141d002d4456208940810744440c000344407541d411002c113450f00207644651501d540c00380065201d000d942e0207104401a1283e42d140f0517640710b040320b900034000101c5003203100c03000c0794402820115894903152144010800000035260310207484043c0a0381480b090001400c90440d40c000186040100d0050050055054016004071081c04032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 383083669 1250 383082419 383082439
    0x17040324200a111515030c0909250609090507050c071404180b0606130305070807061205190e031611012307030f050f030a291c0602040506120105 64
    0x540c1341c4901000303031080101c0070a0300c0800c2a00500e1449106010f60003012200c000d044d110100303068a0040b2500c08090300315803126241c00040c20000c1810302c020791540e00c110740c00d0880251280081c0e01074810850742d00e40000d0b51040c060401c070b6100765248021501e8840e544c01042051502d01c0351668051420b001c21454104d00310110030508a034003002d8500c483e507441d018402c01d90054a80103088603013041c0e001000c01c0c1c00f482b180d405040d0401c040c0c001d941c00d01c94003134451305241c2c80b54650b0519110410900c80c1ea04001c0c0c41c40900b00d0b04010411001100c4082d00e180900f060060b41c000728400041704014940015003603e44007038030f031801e03904842c9030141d0306120602c220710303200c0104008110010713105140c56500c82c1018100385040200c1603003601c4160b0021102085500c0d075860311000810300b00c0025400082509408003140b416080100d00720501e180b4802c0064804110440200041c035010307240030b814007801071600c0d215503040b000d04070482882032034041d080600b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 383084919 1250 383083669 383083697
    0x151309030f050418020c0a12021615050307030509010b060c0a02090c190e2b0501060806100303110705030303040f0b09030703050306010e032817040324200a 69
    0x903054801303c5150902c40340c180b00e4000ea00401940c0311034112800d83c003c0d0315012000840404000c508840c1940c020500c0100d2440f103690302444e903810410710f00d00d0750101c804c002a0704c84100c9a20410900c0e010600e40c6884071414054041c04803602e622250218a140a420000540004440c000c0324101c0281d110440352342441d1040c1035070307444c1101014442da6009030017003001080040000d0a4030400020342050300d10000308084150004520b031860740001d200f42401034601500200d8043c0003182030004103c40543e1f050700c0000e0900c1b00c000c85040d2000c50034001c050050078041c01781e03135a910389403801c590030380e00520040710360b4588000032400c111340000039600c11a5154903298659191603005590441c040a0410f03030606c10f0101c0201524038903070b901c07030502c0c40030154000005140d1a20b000210813110b010740381e401c03040c00708101040c0c45943d0500411000070101400900c0c0d004804054094174844401e2102d517135080c844503010b41d600800e5008031590350551703040600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 383086169 1250 383084919 383084927
    0xd0e0709090503030c1c18020f0f011d060403320604020607151b0503060f010c0503090d1b03080a14210c090405090a1202030f03070503151309030f 65
    0x1400c0a0710b543e2040c000940f410401400500391059080300c00d0800f40184905403054a03940f00003101d40b40c540c1c0c038100086007403185a1405040d401c817a521050000703603000a08450012142c80480d41c161080407216417198000c440143d0741000495050646404c500c00307200000700380c0d41c981d003008001c958504890101d0950301031079004101500d42146902d40340c18035954a01046292540c0e24030007166034001d8800c044118445880f000d40368a8440204484142c420360214107005a8680d64400070354088121469402d085909906090103030402054488551600d41100100791501000b40101000602188000b0380d440d00e000041107048032101e0f010307100d80d002c004100c215404145404406803035030302034445021942810b030783d03078002001e0342d078151454812034002041034820300000c1919414040000d0000f54503220701d5002900c41488001c141c0b000f0440080041482549980d54070030300c442005000c450a000c0c0310074080000d145c0700318214040b84200c02445070090203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 383087419 1250 383086169 383086181
    0xd020603040c150804080910110f060708100608010b0307030e1e1c1b0206090a0608090105010b04060203160318030311060603010c12020d0b091006020106051509100908030d0e0709 79
    0x4006602d80c106104881404082100c803c01c803070a00617510703032149c502c0104006038521616103400810040c14200000745c045c500180c074101442c03040130f04c24030140d5080a045030444140c0200182d513a0b942c00021001052005c00d8003866001e24510390516071b000e0480c0d0a040441002a0f0350318032418080c010000c49036600704030100d2401da01d0400308403401c041d0050b4860000d001d0f0b0740b800382d290700020b030208483d8000c60045405c003418040c0c001e0f001d2056601406809100503d480d040100c043d549001e83c042c50044405500449e40802d480307200e880000300d108105494100752039141c05019111030b00d58800940c460034000448a1405010700e0901c0038842e102c1d03010740311429a5001c041e501a210044d14a901c41c545900d85480d0000c0305445a40d500440c840301c14201607000f800d4941580c8035510500051600c10100500034040f202854412240c0d003010110700b40e400e0310700007a40e84c0200c641c0e020225000f6880c200caa00503000300e007081420b403002d00342c175030b030f01d074011600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 383088669 1250 383087419 383087423
    0x406020c03010524220234020d05010e01140a0c0f0e0120030a03060509090105010f0e0919050120030906011401090f060905042a05090d020603040c150804 68
    0x604d0540c941c3c020001018401c0f40e03442c015041d8008820703a14003056007000c2842c1c1c2d0712682940000d15090f500e4030b495841c00c00c00c041210070301c90020021805200310800b031101a10543c5460701400c10003c0075442500000c0b900d0000340701b261801c95030b1948000c0708841c1100001e0401c1982500e8502c600c02402d0b1140c1c1d281c8807a598092610f00444078080414040090b035a04420440c00c0c0d0001000500408101c565001c1a290300304800d010000801804480080c0e06060041c403081d900c100b000c41c203a692072007081c803e070f54070351030302ea4a007800e1010580d0b921240c0118072001d102042d00000c022008110909070640d0928000700b065100840c2d403130072a5003020740140074a004140302c840c41c043d01490014802034442091065084060f07001c040410306c1d000040009007800d0140111000d00009104400040307144006820a525100e250400100007121413455032450201441301e600a018182c980c0341c81d140c0740c10701070658006d4240f41000e403203040400c54494001188074035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 383089919 1250 383088669 383088691
    0x40e010e100e03040801050c07030215070804030c02060d020a11070f030213090c050303030712060906030320014703070e0c120703050a0b04060b1e041a0406020c030105 74
    0xaa071110300108202d25801490b0702007044009000e0500f401594000c618200c0d1181c4d44160380c2c600030f85840d07101d030007440103440303c6020031003050b0308081c09903401600350402c22054015840020f405120740030b03041e0300f400c2c400b1803000303040c9a000c1c00c10203014070060101e80466881d800700351020581448000d60140c120030100d00714881035085110120b10962503100020389a00000313045400858004c0000340342003000904145003401008003d10426004000d01400c61320010017075000840101c1c14580b80400c2c98141e41400d51081c0c41c0c2c451b034440c808601364400840b94116800707130303500700b10195907210381d41890109104804180d0007004005060b01c91503c0c1c1400c145110051032042003010610950b9400c2c000c00403120b1081455a800260300d29020004030f0031a00304810840c003c5141500c18000c50380d5400440d00310101c07040c3c0c007008035404c1c3c6440307200c103110301d82026444040c11140710015001141c06801900c40726000d4511408100d0103045c00c0f0307401154010009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 383091169 1250 383089919 383089933
    0x50f0702041107060207080a020c0108060a0b03100905070314091603140307051204030302060f0103080a050903160b0a090608090c010311130806061002060103050717031215040e010e 80
    0x5107441d920001850001c03489040c00c1c20a02d88840702240c200100035240e0180c00100b03e9200d40c3d051001145075030090802c1c07842400c050f004112058982d000769641c03004000007040c64299035240981c004c108400050199242c211030040207021540113902140c45803c010070704148000c0381e9840680718540c12500c0103442d54464030020811440d4802450000300b21840215900b8415215a560a0b140781c0796030380e18524000345025070061030503030720129601c01800001c6100301210b81405641c5000e40d16031040750002070601a03030a6a02e0002c247d0b031440003500e540f420001d03001184c03032921030305440c43e0741b4517060311121412102d030200e5030400030f0400c40940c000d43c4803c4000440900b0f0034100114441004210103544e082030041d5400701c420008207140207a00380e80c038001d072440a4082c652450343c03000d991b06101d00a150070f048100036240c0074600104203880d00808030128000c2a800d111400007011082c10a400d0b01130790800302c41041007507050140c0340380901800014965 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 383092419 1250 383091169 383091173
    0x203090c060f0705061014010509130b01021f0903080f0c09011d040f050901063f050a0602030a150b190306080a030e030c120a1502121305010c050f07 66
    0x3a62200220b090540720074002540850002c01c07855101c0c0c540d0141e4000c20340c2c10841d41030101d0703118640c81e504105040082c10580e44a4012030305802240c1c80740451038000020042c4d040001d84820400100c8500e07444603181e0b6920341141015034001c0e240d00d50107456808209146101c100e40e07081c00030700c08001c10044c1d940b007426100e00d1420b01407624004280d40f80005026503441940c072180550711401400720190089c41030300000c00c15403288400b003078071424200e02d050040702d0144810b100788203021065880c800800340cbd11a507101c03098607000f001c1031070842c3c001e400558083ca103013850031520552600203e40c2c018150765080d4a0b050500c4504c0d60518030207540080c1c101c0805880c0c01002a008001b00200b2240c40e100f82c5078880e05820305010f1500e44515500040e101c4d14801100c90324086003c50f841100036003000110031440079100a041c0680301c4c1e01c026100141b40318003045072880d0b000304c2003c0c1071032040000340b103207403034140c1d04503818003c140b440034900c03c0800c038202c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 383093525 1106 383092419 383092429
    0xb0711011b02130f050907080f0607091701090c060201020d050c090f0d03020a0c030309082506051305040203010825080312040201051612120203090c 66
    0x903900e5003282070001c0103801018003a01455031500e0a100660305504810360210a00d80140414142862455039403850340c8034005003030080ea504065404008103501e070080c182940c0307040c0e5590030121a2070424003440d1001803659646c0400100081c141a0240014601c5800058a540040303c2030029118002d04100203c0d208200c0d050f00c0340e03140f2a890440303010607104140124038514050385041c80229003d042c0245030f0b01700004250380310710414107494000c0b099541904c00c1d0300041c20801d405c000301043c1d01011140a014581c480c00103005c10a06028010100325900c0f00458100c0c0e2003a0800003054000380c12407003030003d420f441407032103441140107809000c0c0750441700346e241e014040c044084506081c0c04038044d07a2141c400c0c2c401400c03e4100c80f9011500500e004080310200c09525400b161038060000e02c1e0701010b1080e648162180000707000a4040001002 = true := by decide +kernel

theorem cover : BRFrame.Cov 382913669 383093525 := by
  have h0 := BRFrame.cov_init 382913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 382913669 ≤ n) (h2 : n < 383093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
