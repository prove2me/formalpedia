-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4755
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:37:38.454386+00:00
-- url     : https://prove2.me/submissions/6540a546-fc2b-4478-8293-e964c6b5e23d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 855035971 ≤ n < 855215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 855037221 1250 855035971 855035983
    0xc0c140303070f0507050309090106030c17150405100e0a020901030609180b100305030310030c120807030503060d140f06010b0c100e010b03030c070e0c0a02191b090b040b03 76
    0xb65100c0000140d074000302210746404c0b4007400c41d9144003c003d000310541d00c42c40c01c24000c011030307074000c580c0354215030000709440c0c03001440c16100d00a61092299482c0e080200301c020040079640014190b84c0c650240c90101010f601612640390314030140013603484150020301862100b85ca09005040d0354400400890b8800724104280f001c140841d4000102070510765908181da0007800d4052a031241c0365a4250392050b100042d041241410130410010b4441e0040001d000c120003208050200380c54008080c42039090050800c200003000820640c1c51616000840760012603500c03901d030174400d42a680c0c04c8504103075600c520824000060612101c012a459071b020301d400f4000c041c0c4008141006441da03481503a54070f54a40c040705c0010b40f010030180411911000c02000901d00d00400d100e16894003a04c8018418401c204012505800040c10b0410000070020b0032102d111905020041200410110362340700d95855000468112a4100c1103104000721030406c490a074040405640d44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 855038471 1250 855037221 855037231
    0xd0f02091503031615020d150501021207030c052d07081207080306030106050603130303200927070207170a050d05030a090f15141005060a030e010c0c140303 69
    0x1a0041144506030a0076940c804e5070a40705c2c0000c20082c0a07014400e2040c0d030820429030720b40702e0340c4401541b4014429110100142130a002805000d11030501307400051040b05c074054140139241e400101081410000600c02c08444803650004950302c0007a00b200311a16082c04943d442100c0c00442c05880c0410380310752101190b4009460040c207580c0d21030303031070f00b0082c4881d506550f00c07040065191070b820021031144583d8142c02054008d585400b8080380c03102d01160702841c0300c900c8590b50707403141030003160340004c0102d601081e8620803030078800201d00c0001d521401207828405101106400050b00d6007030f2400c0700154005168151115580c440b023050010388107038003035403840c0511805400110b40000c5001c101150b03615140d1200c00712a46201d10850700004001d0f01c4114001d00d0b0700c14070398071050360308100d00c640c1410042091200d1480c090f9511a0100044e0000c02c20b0095004041580b14003001780108641d1000192200d22515029a80587c544101202101c400b0080300d20407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 855039721 1250 855038471 855038473
    0x1b110106051f120c0c0201090b070201050f160f0804080111070203070e1003050703080a090b120708150418020a060203030f3c0711070b04050d110d0f02091503 70
    0x2c101c2900340b04004580651880c1c042c8120100c00d112a0540c60003020300d0f22110340c5032414100101c0c0300052103038015074420090545d0502c00030b401030f80e100c8200c80303003420701c0c120940c1c50300421092181000380c04100100031031401060b400820140001401c100c42c03d01008000c802c1840b1200d81151142400013036150300b02c0c1500707006085200c0c59164100312030cc844000318a407290741e02c5142030b841d500140c842c80d4010407001405540001d950700588440d500d40d506080c90200307128910035002d0164014441c5800010701c490a0401e0350400119000300240314460401500310031003c0070701e01c180d0180d100201c02145e820b000008880c090b1803002140d240aa6a42003110444612a401c0303c00b83d10b00d000c520132040840d21500d6000900600c4c0102050070b03c044040c045545004800146401c41c240410000c46890306660866206982105003c05245407125158165604603584900240702c0c540a2050292809901c1e17032080d20078210035140e00120741c1461140305400c40d41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 855040971 1250 855039721 855039739
    0xa0e0a0803130501090f060515040e03070330050610030b2b0b01081509010c0903150e07030515060d120f03111c1a180405030c011b11010605 62
    0x2288000320342050024090000002c51203084c1e40c5911b443d620185050303981a4a40742480f603220307002c0b428800311441c2290100464040342c154140c890041c15009800e100c1030030071011000700c40007408004982900700c0c10054101e100c014100400c1c06035000d500404c0503062289000b4000d224a01d0000002003081c8220000c406072480c82d000000284207402d01c00004902c000341c07660003101d0281801c10050200e048071070703c0881d60a500200342c26513503810030791020a03a54000341c4180680ba00040c2900140104c142608064180581200602c0c464480c0c004280000070824541c03d4900d106840c819403160400c0005002044030044c224104014190810328080e0280180481003824007143c1c1322011030a801d5143c000460030048513890726400c2076003030b070302c0e115903030150000714010100710302840c02180603031040c04408a41440c4a0020809002041065503703405000c1c00074007194010031340300b81d085625845264080740d00e50064100419040c0100000c1d200c000d042005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 855042221 1250 855040971 855040981
    0x5040507080103170f030a0e0d020a12033305030d09080d3605010f110c060703020703050a060b09060405150f0a1e030212030301060e04320a0e0a0803 66
    0x351303d90304240d03a404140040200d000c1900e2190051480b03480196030002da03140404695038280540c0290650454010040031000100e081000440c2039100f8500006c6158441030105201c9a05480c0140301c0c0c040070414490030005040540203449040e03060b04d4002541d01030981d0106240d0254400a402040165944920640040305900030080404440d001d10f03005400382c81a65541038445542046802d018550300f081e404802650a403600c220840041442d10740c841d40400d120501c40c92000850100f0305108000101c091074015060b17910441e5130785001002041c10250b501e00507012900000c1040c5080d03c1402d10816400345a512816040c03410401e0442005400036440132a0318400710b071503070913140b900c001c140025002c416124114010004000e90181c00c0c83d125900402c014890320780d011b070700d4424200e01610085010b0301d0248950344642e480d200082c18481d0344401c10310201000306000c1c0c1c090ba244107c00c00003c2c0384030641c1500c40b1050b60019245c0f10081020038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 855043471 1250 855042221 855042233
    0x151d0114090d060e120c071502120309010506100c051c03061701021b0115151403070e010f05160b04080409060803071209050f100e030d09060905040507080103 70
    0x241414184003006180924880020300c055507414000d403445a03a4441c40303600340004000b001e0f824900a9013081c28018000e0740075907142000c2c054013546031020039410350424000c02045020803c040c602980340e14105022074000e00b82268514402c240c00d0f44098038140c060141c1002e42c90300100a0010360a42914010200f003d5201d15820940da981c80010000e518901c8401c840c1d04c0c0e00000740ea1070491804404000d5031407602400c03e0703403500100c000d44188032560b03041190304c021125002d076a134214041d6002e41c10241c5288010b680003081110315940b00041d1003050300c090b01c80700348450640c40211014052038001d600c196a100c154031021444140410303501c10312035101d40d40f500740c0715021364050b18856400641640c5c4041400410021043c1004440381a5880c00c1c0c0c00051811000640c0c280c000b2984c140a8400e103503118556520444140184200203003c0b5000e000c02d20000404621140c491040013aa05100106103072402d801100c0c01123455956940700c5900b144c40b26 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 855044721 1250 855043471 855043487
    0x206090111041a0318030a020c13360c060c1a0f0a1505040903030209091806010302040534090911030714121315090b04150b090a0501151d01 62
    0x10001c5c40310b40d81c0102c524214100002d00401c0180d601814481c203030708051040d180700c0e181030799051504004444164404920000103100b0040d40d900342480e002021201500750512005404402c0109010070080e03003080a101826100f00040b08268a4003046040992800c2c0c036042c440c5400706002c280720080c02d07007110f0395001c10809e088072487d95410000d01100d024000860100360040340661043c5400d1411036481001d0704d126582882d0012080c2d502c68005000091140b50740d03202144480b0234040e03043c4e85c95441840038038884958080c0c41441c001100107100009501041d022404100034020000c6110643d41c60500b0b584a451007918402d6102020700040081408040440c2d04842485c174000c4d411503da00240b26443d0500444208414904040d4582000d60000c0001c000700d1200c2d0f40a07030080c0e042c500182501ca44800900954104281d004c101c02007404040812503000e641219901d45100030784000300c04098841d0340400440440100842e0b1220020394094011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 855045971 1250 855044721 855044731
    0x30c19051305100909050109270f0201080c0909090c041107050a08070204150b180604270b0307031a06010311041502100f0903020f07050d0215190206090111041a03 72
    0x500da460762104544d0741101c000f40e0044010355105c27000d0000d030524050f00c500210000c02c0100d04052450344031320a40302d0361820002d04101003600051203c1075282c080c0e0f04c81100c02868004241000d60340c95a075084072034100c80c80b480c5070001120b107064004007102da09540c000042c01e5412596101d28240340c11415003070f82c1140d1108082c00001c00300c164440b000d0300403910030b10b488201d081c44856000c1031080d801801113600304030502c20750b201c2d551303050105200c800c0744017440090044c6c202c2c01b8041e0001d02c16010302c2859004001c00040094030006d422500d401c4801c2a80c1e02030046040e21920710300981c1184007044284009241c0600c44401c01e0312030300442c0c005007a02184802100e03e8035202e29281c035640e8010000301176040c030082c80d00390058402006801c1c244400100b003601c6045000740300b403d1442103c003008613040b066075004030101c50803038010707240312402130348822045036618055442d00320701c5040d0101c44000e803020794010f0403490142e031410b04600e072090381c00070741 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 855047221 1250 855045971 855045977
    0x3020112150e101d0a02030709051f080a05070e19050901060507050f010b090c09040603050102070813060503070f032708130501110a020d17030c1905130510 69
    0x11004492103900030003001800c1d4403582e04264506120080c0010820b81c01400c00c0448807092101407041e01c440140d00655001d00050b0759840d80e0360b095481d8140d95000b50f4204074980200441540c00f034991424008a035100c054942d0350300481c1c2d80440b0b07000c4601c000410003404064015080801c0400768044061910426003602e030300008401110907840b034400142e002441008106080c002070a0f15541c0d03000034403680600000088d08000002c0c4403000100d004601c065440d561500140d000f107410000840d960030180c2090384182c0c0c800110b9080c0c81c0000c4174001441032181e000c99104149035982d5610324050403000703c0107401c11039514110325580ca074900c4a400d0086aa220180d403158030701540e00c1640c04940b561040d19680240d040c4005004208035900d804288a4101a8111000e600ca410701e8030f07000b010b241d50350b4800100204040304012081d000d030801406106904000c2c030711401c4011508607001e2040c0303a5020b0110041d8901000b180c1058064a0000d9500341 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 855048471 1250 855047221 855047231
    0x31b170901201c170c071208060a030b0603030f04080c0312070b0f04141c1209031e050c06130302162102130c230a02070e0601090b040e092503020112 66
    0x700104ca0800069401120602d80060120100b15070340d902e00c9400961402c1c01c0c1000d03d06070000590040407840301908210381c030300009080390350038402c481c28800020803194407661902e4100c0c1e1340d0344800e2001d07130091040c00c2c0300124074100c0409807800981d2041103000705566141c0017484e00c23580130b8002c03115541d8151303150340707231003002c0c0011403206a000d0740fa041034038103804005090607c1c50f00380b0403a607440c0400c0d400c0400d6100041101c004c46188400452407030301c0d0000c82d6507110300d00d120f9031580252000d0080429403c00c1032400709000780c0c00c4070355541c1c3c0318100c0c410701e0300184142c2d140c3c02d00a494807110003204605000100e8001441442002c19000b09401620051440301001800c03528903603807400c14265104609600e0b1490180c01d03c0329400010f996000b00303004181c4400764030000200c681e84258000c50151820f49071068540382c0e60400440e00c40c0086d122131189000c2e0301150311110814803c541740c000c0484282c007440c0303803450b0015680001407182c040c100719110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 855049721 1250 855048471 855048497
    0x90d050a030216050604020f100f200607210b130c0903050610090f02040509072010020c0d020610120f1407180e030304031b170901201c 60
    0x400350203116240240c0250803030f031900d44104035120301c1c05008c0d01d01c40c08115950090860b40f1107240c9412680904000c400301002104004820ba0100741c820301074800e04003003164643c1c2c04449540c1c01203400000391140e001c4080750314196041c285526820641d000140d28801e04581c00c06041d0b180c06041c0316041c00d4698a40608020040300c0e80080c04542304810801c1c1000f900c581c188901101c60114185814040003070b02c2410080e0413941001400400711586c9a22504000d842c1c004aa04940f059000c0100380700c007a4000d5100d40c2e041c0c0c084d16440c04105400820124480c0d2640421060724504108490780d41c503100c48400c3d103a942c0410440c4000802c00305001c00c50911040003006a04d280008400c0802107135100c8000007801d022170a55240e4002040e00c0d00140c4c141801140070308176a0700303144146902400923014900508441605184070801442116001e82e10b4056140700098210401010810403030102c0c0d11583c18661721202088510081540d01d140402d442448 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 855050971 1250 855049721 855049747
    0x14e0c0e010e0901050a03060b1302040311101706060309010b03010501030c0e010b0a050403021c080304030804330c0504051005040603141512010f0218030606010305090d050a0302 79
    0x811040140811440c45035403500303682201440081e08070485034070780c0b150b041001040c40740c441071000600e1903481d08440441c1e9a03994603d000003950140e000c41d00d1396580e04048054900100701c6501458004185406441c401c1c0400010000c8600c0d06100c2c0ba00c550042c0446644000d00418942d503991b24800c496640038041c1600a50041e24400c0003103080001840303418006920071700c55404100501241103400c9800d6800302ca8048404580c1032500c01e003801003100850710002e101d140300104010070160031a501600583c011032000750080d800084242d01c6c03d9100e0032501c0030441500c607035141e114441d04180ca42c03001503d07286d41050703511800318900010800d120004640d0103c0c05000b0300b40c0c18850088100c40dc10302218050030008807151885106050440c002c580c0c071b4800c003a03600303025003100f0b520741c0355000c0c00c56517800c03005400c05018100600542c0301c0d01564001c40c0c1d4540c400c0c01440e0080c0d9103d005045104170160050710580d202c0300480307060580901c02e4010b2600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 855052221 1250 855050971 855050981
    0x10e01090813241809061e05030601230f0603070c03020f010203071b020f060c01090203210405010c4101060303051c29014e 55
    0x1214440710740d1503492180000218500d02e070890840d00400744001400e03840c61078180155908141451041800c4580810105140030b4006601c00350a0101c005505180109648400d50304000403148040d11401019100e440a00c500c0d4003501020802c00d03507040442c0c080c02c0020034000c15103040801903201007035040d001151428007154620001c0401e00d13405010485668001000841c60f62600f000e029000300c10f22424080701d4502e0045083c110f454604c00d40039203000040c1119181d42c45021a2406817403017a508038000c0c0102c0c40c0c001c80d2030082d04609807102c800040710300d007842e05000045400894041003900e0240c0d90f0007038640c1440c000002d84544040c00011110094038400d042c07066a00401000515070789490b1040010950100540c1d40c0c83c1e1080ca01180700c03490340c62441c0050880c000304031082c0d401400e81002c00c0000e80c00c0500c202d10003a20740060341c0325440751024141029610b0801003030102150543c180070100c0c2c0119488055048000c1402c01c0b5020510441e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 855053471 1250 855052221 855052223
    0x110a0b070215090a050a0b0c13030c15020c0607020d03090b0f0d05070503040c061101060504110301031713140112051014101b02011e020a0201090b2703010e0109 71
    0x40c200380d800342d040c6800806036640c030800b554024488214942e850341d545985003000030b0700c25155980458140900d400840d046c2e1840d030120031282c04e44904101a54043d07501c101042c06c115941151411800071400204c3c40380024070813030038247d290f0203110010702d913000100e0070403103900b0b03001c11941c030900302030034070f21001001c0719444601c03400210084074005040307441030020500401c0006410401c4050030b9500707a01d0045a8a20854421800351109800599005017041408000020500007450403a0301980c0ca4240c100c40400940707099100b5504110100c0701441828480501d04501c0381c80c0150040c50300002500c0e01d0941e41c403c0b0b8500b9600c01852881114041005402c040720b801030311081107840c81c0b40c0c5002e04d02c001d458407071440c2c405c004022802d00d212095a009480311802c00c012884910b5000102c1e0f9070003516081c0c450700c1240407441503040400c00c0c851000507034061220044903030300b040c115207851119030300040801030707855903e81d9005644104207000d658001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 855054721 1250 855053471 855053473
    0x607151e0509070f050d060f0e10021c090201020318011407150522022b0302060121080301030305030430080f041703070302070b010e180d0e01110a0b0702 68
    0x1070070103001090501042d0b50144e4a4052000014407055031036424580d880d950000c00054110a200380d40c601030440c00058071180d010300c59007401090b295400902e602903041d5403403903601e803000500c18102d412900c80a40145e109101300e101940007291029132162050600003002c1e11240700e6a0709c59070044d48211480704001c3c1854059003a14002c0d6500a044440c1250200300001c09a02e1400b00d44500640b01e1002c92030b03000315403002c0c0440e4400001c40c2e26004420003403d070501a50360311081c81502d07540ca08100702041000041c01c800d03418164400e01071461a4a0b684040301c0d10741025205032085003038001788441d00310040103110020f214401c500d0507004070f00c0d94040e2100b00c000381000c948002031010000003800540d500b841400b0081e040385d40740d40f2440c5080313009000b00c05001f045162045c0012503000d0508130114418030000b021911303d4151440001d4841800607144000306280c0042c06030298003e1030181c201100403800c03150100829103810b0444541943c2c0c20001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 855055971 1250 855054721 855054731
    0x3070306030201080703050c0313150504060902090c071203020901120903030b1503040f0807080c01050103050c0a12030807030c030b1305100b13060806060904090b060907030b0607151e 81
    0x11944c004804590140007820304009910341880e41400a120041540e10b01d40041c41c51034041281e03a101c02c640300041070004024034586817034504014010356005a20034030481c80080c0ca40b043d2030045800ca95071000000004100500d400d501a4000c107945ca8103200541240300009447d600c00c81055074065503001c03888960060501c041d03840f005400c146681c03001c00401002c201a520260300081d48000720590303911b03083c10844081d021381c4000b480d55500b0b0400000900000051084590104540c0d10b0121a6640640b00011689620090124066000050199010b41d11901c0500c6050501042002c28040081d140b0749a0001040fa0315a5500a00c4890341c412800d85000d0b0032036201140c03034980040850404031103d0300c80c0e0000c001001c0f000a40300d07102d6009442c0208005070050144247d10303d04483c1f08201154054003424200d400184854030a0154255880300609a0b0380b0b860038544a501d83d44000024907403400f03071148410b2461141403425254148601100000c1d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 855057221 1250 855055971 855055973
    0xe09010603170a050f180a0f14010512040f08040b0c070f05010e280902030c07120801060c15020c0f030403060b0a0e0f190f0b040f05010609060804030509060307030603 74
    0xc2c0d14560301807400e000e92024425010034a8200c01280c84890300039400d507848800402085c007014040fa24840e81001d0840d1001524900d2040080c054413181e104924402d00307241c0045425001d0050785c100300d0480c1002082c04a44858042ea100764020403845241c25142c03000b80c000349d4070003014000980d11102c0304101d485010f00844002d00000d00c0d050f5085003920001400207407400c61210203100c001c286554805044c54504c2e00100660941035441c0e01d0818555002d0782c00c01c0c0341c25101c08148241c0300c0300c00381c030420b5010305032042074132482a40303155030725070b40f0781e1302180301440354426801c010040e07080707d080180900310402c1030025a9138500f1890b0600c01d85030580141030052080410a21020300110321240d8401ca4000500c000c6960b01c001c043d05100b8180f40201d81640381840207010342140e40c01000622000703a50a0065452004861049a80034411a400034000c01c17024001140f007180c1c0c11783c005003e45002030414030240d00240711980152024804613964450400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 855058471 1250 855057221 855057233
    0x8010509100b0f0a270903050703080601141e13080a12020a05100c0e181023011b060e03030711030a09031e050601090e12030114040f060e09010603 65
    0x180c0302c00d00c10b40b000c1101c518508081004921640140c2d068500b920905215440199010307481e0003204105c00d1042011909003d8481c0e4041e900c1500081d00c0d00001484950050403000509a1a45130f020300e045054403050125034284142c0002c004000c110ba00f0116031070160110140a45070058807044109183c541c0e444c84084692200759008040580d0118001258280c1500717040720f0041100001c10104071000d1109050f00e03039004840740700010400844d0040c4503c2a40c280da40b9189540e1151003071540c01007013141c1051701d586004241a804d51292aa8450b41440e40a0025601d00266146015181f0000c0403401c903520101c2002215039111380d52551112116010b54913292200307000500310303505408082c080c620244460321005c2c03001543c41d9041c64000c401d9031019611070003d9009406110034040c4240710324002100c01e20141c0d800c5070704a418540702d6541d40b0004400303201c098040c1580c00354020780d4481c03000910082e88000244200345070000010200e017103141003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 855059721 1250 855058471 855058481
    0x61e280e071d070f0e100207090c0507080f0a050408060a0e010f09020d0209040c0812090a05010504080601060c23010e0714060a03020304060b1c0506010506070c0b130801050910 78
    0x60056910b020318081e0200e2550056086146072030440d0503d015001d007520050803009126821035016824490740c554003290741c00c25100004010700c03080c1071840d0202e07200c3c003602c140601035440c20090510703040d8110004004602030f03810714038105555030016074244001100c000102c5522040744554a5030203110b00e82c010311460000300100c210680200b03a00b0865440024060303154031000c2800c2c02404c408400040c002c45041b03c2004030304010503a195000001264012005a1000314003580641c0c165001d1301ca1403401090284e2030008210380c02c80c141002510f20300f40d034460780300c0d05030414001c110408207000c3c00440c0080403654820310f0252290700c01d82d0030f000042a204c000d5510032044600c250720514000d0307165140c0707040c09001060004021607024240d0035002c48099041124040a00c1c0103409031961a070340e030400d010b180c1c424000c0060804000c3c03e0103200005500c3c024000039a040c00e0480c6686488517182800c6400c103851001c09948041c42c540000410744c00340c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 855060971 1250 855059721 855059729
    0xe1002211c0204060c1b030b0103020f150408010b01021033091a190305030f1c05090d1202040f0306020f0702040617010c051827040606060e0102061e280e07 69
    0x211b02400c2c0c0355464091039220103000c0244500c0550300da45039159100302c125000302e41841d2040d9a5a40c0d1031501c14020304000c407916000d4003800404002c0d604a03841095001c0c0311400482c01c070f1031b002d1600e0082c0c01c03480038456008074015440124422410b8482c44d0701c0e05010a1024404001c0303c400c20136908001c501804a130f146611081c03001960110694107100302001d0310304e4543d4529010f00c15411004940c00d00c07000e00d45010005216400100e03074208030815102c207030074010390b00541c0c001d9100300d0150802c50002c1d058100005903031039004010400040c0885403c0100c66400103050341d80c181c2c841008590001c140d2000010284039a05d8012035a0920925008000840c1c3c141c092a0410003485074070100c1074400b2076102c0c1c808000d01000c0c5441480c00b03c1c0361502e0103a00070b106502a400019001003403841c84ca500008907140a04007809860b400c920070040f0100441c44010542000d4080c207405a200b0402641941820a01c402c0b0380811401500400c0c1e07440c05800e0340c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 855062221 1250 855060971 855061013
    0x2090f060a020703021507170403020906010c0b0705090d0b150406060e010206042604090c201f02130f09050a090807080f0f0a0e1002211c0204060c 65
    0x300c14041150000342500c204c03a0b040c1d801d1119844ca00c02610a40c0c012079101600c4420000b0480c0d80b6180520024404da03842203030400e2241c1c886000440e403104200074000d2000d071400001c5058640110090000c002c80103161580f1891291395000401200b40c50f442e5a03007030481002d80a40c9043c0c001e1030b024082601d8032200c9041c101000071f584030310141c07000d0305908050903921440c0744910705a64441c08071a110f259116950082c10004040c60046000000d50100c00c0b00d00c0074404845500300c0146a400504040c1f007181d01c0b0039a04e4400074450180642d00300b050600300d0860485a0f002080840e842003c0c551800c40d241090358801004100c2e118030b0729903a0800555000c06131040181c0000c4001d441d401c4540789075241d4419202d005600303100120b0002082d075804040e60b500704000f502c1c0541104104442039964030700803003d0106841482d074445140711141d801800d62b04043c020b103084c446882c002d166080b80d000d50008000074070b03c40c047d5070520904104403140107140807 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 855063471 1250 855062221 855062227
    0xb21061006020610180603060905031b0304051008060102010e0f0d030509150720010f020712030b0135010f030b01080706170a02120a0e0c0d0803040b0403120e0102090f06 75
    0x441080382044e1640244007188a20b440011900c21050740b010380a0341c0d000d4070411880c5810b04001c0e6498004900c014100d05082c052000c1202c404010398080b902d000e050a100034844150a40b17588400070041411990b884844000d9080c0030028a0303844100309019180000e034403000101035640080444100c0c1d8007140d84031112031004210a40c0c03007421840d0032a2020f11642c03518a0114117880003002a41c280180142c0381d1107154000d010141c440c0541914505201c00254150340342c8401d00c1e4085001008400c1e0700008940c203d42c00030f84036070802091030520441c000000782007a000100403402c0c026090003042a400541c07405442040000c056103490008001c2046102c1105039411141c440c010a40d29481a015184002900d401440741403403c240041b0051070058100401c620030944204528108070b0000024150041c0e20285140c2e6551900c40e00340101410803401c20420001b2840c3c469100c1c8101048250444000350307840e06a88104980f81c44032036003c6104141c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 855064721 1250 855063471 855063481
    0x6091a16240e03180f030a080a03020306011205040b06040b0607241508030d09030905030a03170105010306140f03070812031f050603150310142d0103060b210610060206 74
    0x10600411385811201500980c40e0440481d09180348a01d00610703010001c9a18410513030141c000d984200c0b000c0c1d803100005c1ca10b0300c22101c241c800588010b80311a8148002c98058189a0094102200003805903841c0c1441540d54000484642201c01e802c3c0317245621440c0c16114034010002c0700007503401c080c0102410500000c6d241d20606030101d03565a6500105801c00d80150100d5000b000c0c001d091714040001742c00c0203441810558600c4542400d0b003400032403558042e100c1c500a6038820106142c0e400c0000081c090701c6200414107076490701c00c402c0006142c000070440c0102000401d4201030f200d06010b1085401482016164801c10404e440c0034081034451005885e030100001e000c000c5d40350034080101b818010b18841c000b40c01030501008061001004401600564941064509900b2164203407003003c0511058010301c0481d0384010804150203070030041140704000c00702c0e0503000d803030784200d0b0240015072196402604248100300500b40b44442c035000520700c03030010b0007183c507003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 855065971 1250 855064721 855064747
    0x6030105060421170a0f0801080d0327030c050c060f0f090f0a0803070b09010c140f130905180d05160f0506070203040f06091a16240e03 60
    0x240d020740d07400091003940511001040c03564000e12140c12582101a1405115410b0142c0c0d00000c1140082002c07080c0c52540c55201e00701523070407a4001d04c05003034501820401140985007220342c289207001c164600514081600c02c1e120750492007526070400d42035003450701c45c0c203200410315610303c584002d00805150480490850719140c18a020956542c001c00e40000c071440000c1000e203800100d1945d020840d4039000005007112070007119440015a41c40d00c02501340c41c29404204005141d101d840c40c01084402c000e40040c074205a0a542030bc0a1401d541c5d8442d00305500090005855000307005600c0c0000060901940c02280904007181c12500c0103420303885020b04d17241c5d8240c0214401c80034440e13004c0f0030004ca01c1e4800281d408030704294000030750380e0b0170134000c003121007002200000764070b802041500112414240d080ca034404082c00144415001110711016028981103241d00165900000d02c25005010b18000f02d01c944181c1d950f001c0b06d52400312a6600d034400c1010140d1640 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 855067221 1250 855065971 855065977
    0x7080a0506061309050a050d110705060405100210090305120f100b0d060803070c03031704030906141c090b2d1b0a03050f070f0806043809060603010506 67
    0x7000f6107800007a60380c40d88180700103103140840036103240940d82c0450304010307010510081204082d9130b184400c101c07048459880c4c18943c45419444007040104018034281512090f220f88444c1c0182c0e000c0b43c00a000c05015104015021000107000049101d05880101940780c0c005208150449407407500107007903080e074403603405400c4001c0008a044813000015810003409004c0c214196900c440542c43c15440c0c80c01c01d40804c40204200e00300c3c940c4800031550b28a0310540d0980c0d100f0300750914100c0180d03606903242c007007642e88100404c20118010728041007098101c0c15540000b8480415040000d020034028180f04001c0346610150000031064600801408940c807110030780703035100c0700a0000901a4540401d81030100856403107641d9030194003140c81141c2841e164503a0781d4800c07008481c500030302d500301d801081448022403000c1c2440d130310607103407462103004171034010440699040700080501c0d50300445950110762068603007410341080e0341040c02610031a01f0342d41807000043d0940 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 855068471 1250 855067221 855067231
    0x18200312190e040e070e060a060c0b0f0a0902060406021b0109050d150b0409151b092102041109040e0106030b04080f0f19030b011d060a050f0d050907080a0506 70
    0x2003074584000790243c0c0c6a51004200f83e504500f195000c550300e00707203002c4808080794505d214042c403c80008032180035200b90210580c0c011600e560541d18140c0c80302e207003440130700070029040d5515034000050f00c5140040001d8050340c1c00500b48944490000e0403019105c0386100d040014504040140c0d449540400760515440301140ca1a041110b85a030003d0030329a03406507006042550840500c002c0c0c01400d550300e64070039818800400500d40c5c42911100c21a0381c0700c0011201d00c0104001d14000c074012800c86855015080c02c0022900060140c4500e0401401c5070803001a100f03455241901c40c08546620030002889a5450340d2140380711a00c00400250040e27100182c0d00d41c1e80b403004401c40e0007803401100c5107a181c045616070708840030201c46a2001003854440c240303c4541c003443c1d20b0202900c1051410b0b294203040c0051110a402c1200280140401481032a042c95a004c0140c05000c82c5200c0000d058540302120030315110305940146065000320003640003040d00400c01d0741d880 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 855069721 1250 855068471 855068477
    0xb16120c1127041407091503020d0816051612080f09060c070e19020c060105011407061d0712080301141315140a05090103061820031219 60
    0x40c100204000340d460808a02c10380b07400840300800041121455000c07501d6000300d012500e9594a030841c00044a008031340c40380300c1c41c039520310400041c603103400c00050091154613000d0900013144204910b6103240c08007101c040d00603110f180c4100c01402c4070000105032030009041c80b103003a0303103030504184202c034a1402111000100040c1680b507010072522000c1c1c1460440e05643c1d46c030a95001c207442c0540f0210301303030313212083c150601c40308a000740da01e5000300c4400f4100c1646008015510114044c441c2082c020090002e54013142461140c4010201000003180350081d04520060920906400014003461025034860220f06e185064034192802d02e403080c4030501e02a40014100c480707030320381c240c51541415200c5c501c1c0100386401c20125000806c0d04107030110020704210901c80c07180203840d001844c1a00400c0401c259400014850300e032005001e0070001d20b40c4401314903c045220b000062441e000d14401c80b82010080c5e40460300307082500034148804070b20141142460a1403100c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 855070971 1250 855069721 855069739
    0x20a0201140a11060906090d0804200102100e010b030c040e0703141002040b09040506060c0a060f0b0a150e060702010819060b0412050f0c210102040b16120c11 70
    0x2d09014800c41d10710846942c08840440c034100e180c0c40c0d5220800c0380c09581e1400341c00300144c80180102d210038012540842400078201703620200c4480741c000c06000c0c17411403003000e40c0030390311388960306c100d90708100b8603030011441d10348140038103241a402c05509805140b80200c0b1810524010401c0f4003581d80c0a0440c840c0790758640c11a80c64455078012200b10507100080000b60102c848c4002e108440c0300351401d008543e100800c0002c2405901907000e03440d00200030503000a040703580090300215032500b00040c2c0d070a80300c0c0030450280c890740280c01c0c40e000303c03141100520f0308122440516078085650914041e0180d0000340b240201400c03128064003001001c0c0f076005c0c401d42043e405414821245a25650384038030071030380c0d035880440642e2180168810841c03c8c0c0e80c0810001d5201d0406881004020040141c181501e42801c05141e240d560901006c1507a0070000c0080100480700140d4069190f05030030800c00600c950b10080c01403000300080d04c000150783d1818480100307412145115 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 855072221 1250 855070971 855070987
    0x130206070309080d08060907081b09040207150203010602072903070e0306160e04020408122a0717010b1521131205040b07020607020d0b19050601020a020114 69
    0xc2c03561030507080080d5034000c1c28650305000da801100c10b84900400c90303d46003662544032040e1818082074075a030028140165401d9880210740c0003e20b5a00c101078001032410400e0307168044000b01c01070f84d003804c4035000001080156810400040601210308030074181e100c4210110350020401000241101004000102481d0198105c40c15403940034081e075082d40703040009000d1209001c00e0741000f05044015008090400c0d1007074406994094005003144020070a5090240d0060909500c1c8108110100340003103002041620407410408020000d4a0810405031060b4018a280e505070381c1c50138500f032055941340d20311422860102c0101a9484c240c00d080b4125440341c0014291500013082d060100740d1910b851440740b07a9004641b008400c22410a04540303038401d81c0315100c09a0740c24043d1802618100c001025901e20003400440620f0031943c9101086000315000904520038002034842c41180d0f0142581c0400c0910160050009990029080305282103050120f440301041c0c0e41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 855073471 1250 855072221 855072227
    0x90e0a061701050901110a091a0f070606140f0108130305090a06080103050f0f0607050a2109021005090303040608040507050409051c09061e030f181a1302060703 71
    0x140160040c6811100d8400789a6030031806418240c90030301281d03103005d0060704070904403026102040d020fa660800320314030704468042103590203e40d00c0a0380400b0450703400d044c01a1341c024040b40d4402e040220341549840305502c0f4207906040c841d40106091a1302e5501c0760382c09902c041d0310404e51070b008200001141001ca5142c012040013a8120011000100f101d581000d1842d04892042c000c03a10740300c19040304152501c10644190410f41c3c068000b040b1403038002c0d005809511480d2070300119408044041940e510956000d270385031180e54071101010350a06156454200304c050818924062040c030210342c1d07078807541c417404080001780390126040010500c45071005100081c42845042c0e070608003a80c841c44202118a41080020500e00595000d001050115100c41c0c880c003c00d100c00c42c51170808420650302d000201540c03044044010729a610a4021083d10700c0c0809880c3c001030310789089000d100002d0540740c0d0014400f00f1440c003044214141d1800d41c181e800325183c074101e140035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 855074721 1250 855073471 855073481
    0x161404052110020d0b091008070303110309041503050d031b0f02030c030703050a090801060e010905150d390303030b01050403050d031a040c0c0b060d020612090606010807090e0a 78
    0x1c6600ba000281601d0311307401c16040420a40d4046803210700c41d07152154110307801103491080400c4c6400461040003c640030b5544d0f417207009003030415607280c003842500083c01c60300000f86030300340c5280c0c1d81d00c24801d000003084942c9803081c95040801c80300740b13586042414142c1c2c1c000c4013800c000340c0d15005043c1d24801c0c410355800c81c1c83c61080b07948030201441c1c0a0516009003800c01c001913007409002600341c40500504041316840e00c070b002d1042c2d0070b00d1034020103030030010b2805d10000055164001540c4505507600d401c140914107010002205580d040d541500c603c0c0440041c0e6043c45550400005802c0141e0450b0352500b00001c11810320001a41d0a024581c40540103000e00c0305001c004940580110708401101104407146589002c204011034107680409000035046516103030004400300b45042c0c00c004000c2c01010b64945a50008489a0054900010341e0b08000300b40500c0380d07806c01c2a01d42240003400c3c441c45900d0a03450050407004c8500c90300c0f280d021a04003082c00d40710190f001c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 855075971 1250 855074721 855074743
    0x30a020606120f0115050319120c020a0815040b1614090a0b0f0a02070b030408122a09040c0305040b1f26070f05061611091614040521 59
    0x81c4410301c1e1703011018800003028420f0a002e4000c1c0c40c4003101c0c000c02c0101d003080b401d6110135442c1061090850881f91186074500881c1c0140100001103990401002075441007828135440d50464509803a003070000040240900c3e041e030409684940340780360402c4c60740640080401c01c1d19140c4840c0000034050000b1580003201c52600002e42080e0f044143c0002c02000c840c036021903070076550310f042050076031204650152007180e081c8000d0311214000700328140c00c0412128114031000b440c8007645282820710002c01046c0400280301126824180558200b201d4141400c00035031074540c440f8038041034000c1944490030000b0111541143c0c07540e0014014145072030108400c201410255072400c401050480d6152050380b01c00a280401014480b0640310054407040c00d04222540013441200b50081c12985070700c003000c62101c241c45a2204900c1400b002d501d485401d541018017130b000156503501019445820407043c48180c548107030214100301500c0071684071480c1c840c00103040110790380c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 855077221 1250 855075971 855075973
    0x904090804060801080c060315091905070f090509161202072001111b040b010909020a05130603090b0402060c1509100f020319050603031e0a080603030a020606120f 72
    0x79002c07811940c0090501d06803000c420403648003442000400045010031990080d403000701e044a04014180460403503042602d400640344004002c034440303800d441085980d400090500c211800c1d90b40c0c2c2c44800c9100511007510032544504001710b00c0042d00914038003480074011110813020310f1201c254110f9403000e4200400c0f0940c84184202e0441c0150600e60050020b000340400000e000400304407000c07600d5442c071740744440d004032900703100140640d19070060502402103c001003044590000342491281ea0707844c00d503548102071601006480c1500301a00b0145002a000c001600d03007031000f038105404031483c6850f840c08125107072504c007e50310082c1240b00620180290351400280580c005c0c808400b00380241e200402d8018228001250148108104248075100c0d5035001d501840d00402c000d0f040d60700c1c0551a03070813504410062a144920107400140068000390300492040c0c21400c1140034601d00002e041009680ea84040c2c080c500c00c5030700010100650070300b0001d2034000f0040308 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 855078471 1250 855077221 855077227
    0x30605070207051002060906040b07050c060f0601200a021917060a0606020f0303010e0403050f0f04030501050f0112020910120606030b01050a0f03030810031a060f040509100209040908 81
    0x900c009480b8401403040a005401c0c0410007000507002040c0b00d8400c11040000700f0745591140c4802d200c2403006007058041c018104004104072200744652841503010000c601c40300c0c03c20a00040080d02500d6803982c00b0420200a400b511030042442c490840c0c04580001c1031540b008103410400038164811035040720b2191024141d50004070708075108180921081001564803441640c440440e14603640458000304010302c02801d0720b8404a801c60300030710b007842c24840076501c0344d0388a5100110343d241040c00400c0810402200b4050b165200c050800030310419403600d0b805140c034180c0080000d06c242c026000117148044c01d0070f10400203000030b02c0710310354001c06801c1000090007240025030300e45a2120000ca02402c0c86502d94040302e0324508480c0846107180c03400c8400820240940489182c040000400300740d100c0c3c000640c0644440700461241400020407403d0b541221541e409582080204048200c004c01d030b0303900d590410300c805691034003500000380c000e02c081c48000b08800c07404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 855079721 1250 855078471 855078481
    0x1090515030d020a15020c0a05060103200108070302161509021c022b020a030b09160b16030e0a030b0906092b0509040504060b030c0109181104030605 66
    0x1542116005410041526100389005014151248550411040540d10803441e40c80003848140350030300d121240b281c0c0107041c40030b120b681a08010300c0390811750300b40c0c3c040401401032242c01c0d015034a00443c00f01480c2003a11007040060300c442c2000f03104602f85a170102d8180348006404895204d09540501040f4000c803803802c082c0001d0295490682c0108444409030714105403a00c0c07042d400741d03001040d1198103001340700c0c40c00703201580b0752007442c04d1150403403000b00684a8104040c00796200d26040695481e14052503881c080e0b80310b00704010700b000782400300501851481110540d41e246124444d1050b042e040941d4511202600c054004841000000a010100d8a0117002c0c1100703c1c260b54694940c1c0c1e0b002d0703030788100344030f40b00014440c10070603141d1015620003003440300703115400c22501304100326001404952044070103136100390302c51a40240314034050104114644003400d012000380d0030b19018a070850846410103106582c2d1340d005d00d18054069003520011503011100780303c68980 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 855080971 1250 855079721 855079739
    0x105100c1b06020706030c11030304060506060705030711040c03051315200a08010e042409123f0b010c020a080102040501120e15040305221a070302120f0405040501 72
    0x1e54410600068600340010f00344a01c501e048042108c40c0200540c01c46e03e958596600900f0b024000c503501ca081004090b001400c14005000c0b82406041010714000d40e12051005488441d01d010080601e40000c1118080c2401a8940c6554200301d50424040c03202003110000c06680c0c500303038030180070f00c5050f00803035a004000b4406012503655684407642d0f2503c5035040319500f6600100b41240d03090f4002c01e0a803c1c84843c00203e0507128000c64142926128048074600394002c1500041c0003080036000741c0240c00d071807410071102408080320883d560480502030207080740360b034510585aa004000e10382c070529000c0f00c4650014038800c01155103000c036a0003540103200e140d0204004481c12544044284200b003115801503000c4c100c08900800714118151000700101d007448424442c03030214200e00961401801c5c8811494503c1c00d0410243c030342401541c264282c8154000c21140c00040d90101c1c0e0342c107428895020701505c40303011481c000814041c0d5040150032a140100005590b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 855082221 1250 855080971 855080983
    0x7110103020d090c030c0e09031e0f0a0c0c06050c1902190e01060f080c09060a02070306060906030b0a05150114090d03120e0c03210705070f080f060105100c1b0602 72
    0x4421a00c0d04085580c4000d170880c4604110740781c956a030000e001c104c500d10703880c1008a04040c0d40d0ac0b6082d00d00000307402e08215a801070511540007a11540c084000c1101800040001e81240d00340b403818140460001540c40c4484424040c2055a0810381000c6443e4100000300c403422451492800704e8a644d00c0440c074490904ca4800068000f800307400802d8064108240200404071101c0d1a0000c3c2c2c1c014400180d000b01c20000840c454460f00002080349841400702404c145180440c80920b1800c1070005400d01070071403c0c00512b0142889a0240d2000c1e0951000c40b081c2007000880d898202086414041c6c515a19007122841c0021410998001c0c550b2244042414080119003c80400d1564400182e0800c80e09a071110030402403a00e0700c1c040040c5101e030070004440c0b412810b035036950f0406035580d000a1085d1031140c0c06010042c400e0040c04c10f140000310081a856250000280c06501c09200d04404e0200c40400c41041c42404001242c03a1000c41001c0c0c0502c40c1d8806000b59030700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 855083471 1250 855082221 855082223
    0x53702120628110403020607110d030203090310231017010b0108011e090f021c05040b010e040f08070206120f0f0a0606140c151f050607030507110103020d090c03 71
    0x502c10a40311002030480d115005a01d18403808081c2824150703400d1007400d5103c0e04096400112903040b01580303644245600302d0240c825800b0f15101c001e04010701d03241c1060b01504586081c01c0c0038142c10820f41140246100410910900c000798885040407178140d15a500b2482c662101c03d10b200300c60100541003625034441c00e80c0c81e00e0550ba65a00c00d548400c0c0c007107038840a10a205901004000c885400044640f0f0003840018903004145411080b0b41d460305035a204095100c1040105110540085a00400350803401d98214540740c2d07510981c01c07100000041844c200402c05c5415034882c4c0c02a582914081041c0b0070450134031810600e4800002c44070038480040100015a81d15070302e0098204844a40c0c8407040c6c09850124100b281d50011083c0c00261302c100e10501414030700d810b030101d00079950b1403c0c006a0f0107401790305140d003200316080207005202c10020000003962100485056540000481041403002401200a44a1fa54000060905180b400700074400301588100440b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 855084721 1250 855083471 855083521
    0x22080a060b0a050423100b13030605072102070f0602071b0501181202030f070b0d0501080c0114091818010e07051005070f120504030537021206 63
    0x740e6680d04110a941019903e0602a070040ca518141d40300110000d46d085101016480522038680c19245840d400040b0341100820100404000f80072513841002d400001600c0e00040350082c2030420310800d0501d01d240003050754006045028018602520108140c0c002e1041d950381a81e4103200b00d0b00c2e0f281c040355640c6201c42090003d417660054140100c480c201810f6144020b281150308558a5088071080c2d07014020200c84901c140c6c8180540000351032801105a1581d001140350022203c0581100310340e64450304021036560b0300045404103e0410040c1e141d50b03001c14501094203850300c807181001400d02c03031003403043e034420000c080106201c0f4140204800c165203041c00340c0d10180d82c420b854007c048800301e0f10a452044000b0580c260164804614007505607851809072041c6004441c00100701117014003c00105001a41f05c10550307a1210201041d50059203540402403140610b85c448210802d50454903601448424000000191400c41c07520445940d42030054003000e403c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 855085971 1250 855084721 855084739
    0x3080d0b04050135010c0f0207080a05031b010f09200103111819080106170f0c060c151603050c04030b0a050705090d030c0302010c020f0322080a060b 66
    0xd0350500e4440d9034100d031303411590001301c2c007a900300034950107030003078241802c8000f00c2540d195000001d000b00c41c07070102240da45400c51348500c80c0c002d003816010380241020703400c038500c2000441e000001351141c1c440070039280300345a1415046d481c01400728401e0381005904008504041c4821510070303c9260300000c0d590701c60100100011001c5400341a0300c7d1181b10380900ca80c1a50b0042c14200d030b030184001074405040c8003107050310700c1075004083c0e101e040316030344604050044100d45008804103403a0302c1d004240b180d1000e0010360711a1b080d169668000d000210307011003071520400c10300424502d83d803051450f500f02441003d080700301c1c031680d5201090400020901e501c002c0c4007240d003206c0d00904600040c1c0c840c0750030310300a41000f41804003080070500522810ba6100320300c0c1001c152080d200c80c1d440322001d190190940f1855000030040d500b2050f0001903149012089440c1c0000d03d20762015807101c600042c410710100d5402208141c0b0902c260b00c1e040018680c400c20300c1503422910504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 855087221 1250 855085971 855085991
    0xf0609120a12020703020712060207020f0d200616060f0501080a1a1f06050309100b01090303080402210304080c040b010909231509101a13050a03080d 66
    0x5a1141003141c0002070082c4100d002020040d5015100d294401e10640310b0181d5600e2007006480d40080e01558825030002d80a030440c984101101580c1c03500b82c81c0c2450303203c0d26031078840c458000e10170301c10a0003000c00100080c40c0d80e400110f40210215001c0c828040280341000001400c01070800780409140000200d168000005c051107a16400015000c0da2110020707144120400500382004500f50080340c03103000002e410259010f00380e41e941d41d50302c91030250402460020308201c10341406217820001001030368042000000daa0301400c0c000c10540b031f14070100b594004032182c00790840d94242e81950b05050040020003c641c0c0800031030300ea10f065641088211003001e41b086022401c14035040003001101d802c04ca03900c803107004585d95501e40206c10711034a003504507050400c09143c80441000f40c5840d454035a0070442040c0c1c091541800c01504030081c00044503042503512010400d005441c104001340340c003424028020860880d941d1502404503004031030f0041480341440c11040d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 855088471 1250 855087221 855087253
    0xd02010b15030103081b0118030f11100b011b03090e160e01030506040f050c031008030f0723250e24190315141902030a0e0f0609 57
    0x1800700e10141c44100d15692841d074801105900400c07801310340180c0c1e0390301d51107550028400e803510303041141e02040e100106460300400c241c0150080600b440844081001c19503800102550000a4280001b071284214001a07a06119016000d20015602080c910403d544504040e045031582400000b658030b4900c1138010860070b1001c03440c0011201070104c0c3c1316604c07a4020907041140079000207400e020607010300703050f120202d0303948919100010038000364001b0010b0640040002201031400c4c517500300490754040c89208005041c8000f200c1a514070040076080f000f110f03400c9030045608400b034800c070303078041000d0311301842c00750311f0034900002047c0e5000102030b803180c4007001e10b044801c01c2c18210480d544016080448c1c200e01116044030071000303004401c81c0a50301072000c241503c00c0c800455016989c1c0351130310031000c5808500380600d241c1012040003800460900250710390ba039100c0010024802c040d190700052080210028440c0c1c03003c1036040c060745159054880380b240c0500c101d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 855089721 1250 855088471 855088489
    0x90b09090f1507090b0a0e271306060e0405061603091211010f0e0601090c0201021603110309150703090e07090b0714120d0f060f090c110303090d02010b 67
    0x280366074200341a80b01e107065030150705583c002e0f09400d0040c2640c1c0c4804805503039070070104000011401e1401205c1c9146450100c54110b040e460040098148465414084101d0040e2000040121003040d050030000c003a000034014002030240081e140c907107820566510300d800e841006144c0c800c010030303004461003030150420041d04070070207158802050008480e044c801c0c9c0842c03d0740d55038540390044030358850f00130000040d180800403c295410600e03648104d844c5807000e06c00b960700c100301401e0300032891564020040d8150400030001c2c01e00c89941c0b4158855024072580c09000c80540410020030b1a001e0140c090080e83c1d40c40c280340d15010500000e03007007520080c0224004440c10460a0311000040035068450f00d041d610000d0142020b40c64880d50868181c040400420b058030070403018400c48036042401c40c810f02200380b801607071a54a48060194011041c0c480d08201015801034951b505813003620000c40b9a60f140c15202c00380c890000c282d0b90030040d42410030000740b0f840c0146030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 855090971 1250 855089721 855089743
    0x16181a1903061112010e06030a020310140a09030801120c0807090203190c08220209070f02120406050d11071209141f0c03020f03040308120a230a0f0204090b0909 71
    0x10b107019a401c0c40280031b1084001052250f052040164510041e1418881000c5003c202800881c10940c6140c500c01468802010141304520384080c1d1790109600c504601d04503000d00004290b90740c40ba0909510000d46500f101c5410722812400042002d000c2d40254070620b444000300300505844408030055a90040d403040000c4d80040c0440e0f00c1c0d10400b1140100b045600c11103800c440704540c00309010640403210700300400c080d0b1b4814110720ba01032010010741c50000071a246041e0404002404a00802042c5106a85d880e4801c0400303410250072503003095003102010070406030002d0010300c3c100740c600401074800183c1021000605040c007140300c0701da038100da80950441c070725881104c0c540710446c02901140f00c0c40496207031401c402c1c0018005540100f80e515a2070310100411300f24102c01a001c00f05052825800754001c800f04450030240005200034a00c5a89a40d0140e40103001c41c18150340c507041c0300050000310000c04c0c0c3c8c02036200c06020b55070103800e9035681d0205621481e500744 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 855092221 1250 855090971 855090997
    0x23030601090c0e12030301061106010317030414010203191a060414030304120303050402011e052a07060909060605070f170f03130516181a19030611 65
    0x6010341001508407051480351071415980d040005000615030081c20a00c5040640002006000c41ca501c004034881c3d84401c070b8002c02b42075140d0340e2a65003207000d00107852020400400400c00700071960900e10341c29691a0001d64a900b840d0b0007010000180c20030303c00c030191405030304040c0d81364429032249041d4401803180e800e040c40e0088171401035416604140d0b05d400b0400000c81c1d0010b44000c500111030007641c0005080ca4648005005107d0b0003140f22101d01c2242e00802c11a0380c42001c54000c01c0030340001c444040303030300c9110f03280b06980602510300074004c040380400c019a10401c410200c1d00381900034030866540e03c0058a080c4284d22000e0f040050440304540415004140036a007004641201450035560908100c925002540d1010841c088006910b080c44020072042c810303800d5203110f0044992030000724160030071800d100c598510b42c0307034103e21080500401c0011f401c41e002410300c1003085007629030001c40f0102408200c48541c5001e1801c1c7e0340c610384406940c84290300712 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 855093471 1250 855092221 855092233
    0x928061d0904080c0136020d110a21051203090a0210090302030d0305160f0f1107050303040806011a0a05070b09010b130f060b0c0c010c0203030c070b042303 69
    0x442800075260380108242c0701d0701d00800070400d41841c00d203e05268000b0700105d0803a960b500c0c2d0014080c2201e14179010700080b110011103000340e5500e940002c1e40d10780c803622504509020001007202c200041e4000f1860990b407403207103070b204401508801d02d414846c0e0140c2d4181d00300c502c858401400240c4805015910019080f401411b040711408440c071418200090710a07070340c0c1e0000349001070b9840700301d0000743c4070001c1c012180d0094100b108006501e0070600d8040401020040c03030307508012108010080d144e00e21a4241100780034000c0a081d0242c15265501d840e104025900c2c20700b271041c50443c1420601d038221020386038040e03849510169035683c0c41c081003a01d400d6502030029041c8100340d543e40187c08029990149115002c15a03c500400c034041c62014081c102c0d1b00c0c40d4820449080d081004030754286c0e0200340302c0c01c43c4009090600c845251400400c0c65030240c0c00c50003805110b40400450304203064000f0b4000c90703c10180141c000c4250200f10510b00801c940d0b03668141d4864 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 855094721 1250 855093471 855093527
    0x20d050717030702160605070c0909111c08190e010c030c061a030f011e02090f090a0b120729030a0f150e0108150f0a11092806 56
    0x10301d00440d00200e061048442e104a0700d4400c90b104419680040301044001448004200c3c0c030142c840014501940204026409030f11350710001070480004602c244c6d890918858241e443c94221030109801104542e21050602c9021400000c5021041c0114404081c0440704d98482c002c25030200d685a41e070700c0e10015043d600c900c042e0003074480c43c1d115a2007203d2803401740d883c20044019145948000403d9040100208182840031100344404c05801045068102d403211145803003051415610141c0c0f45d039592031303001c004100c0c41d201c040c1c0c000d4001e6580b142240c80040c1c841c040d200c40c4014240d6210011104070748860406010203000001840001c18201050b802000d102da599075002c10429003031801e01d41c07001d800350046a0140750040050040700c404110403259895040080d14403402c01c8000c14006403c0101045074854981d4420111742484005540585c64003410030790103080001c0c01060141240c0c12000801d02d1000000201607103d81e90a0700b1809505600040000c0702d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 855095971 1250 855094721 855094763
    0x409060915030c231f0801080c1c08041e031403070f020f030c03070603060806010b0309070b030714070c170d050301061407150204061d0f091504110307020d0507 71
    0x1180e40b4a9201c0e0091004c1c40d507454036840b0000003001910070031070b030340a100400040c040c0c032411b0300300e108180d000c2d030f88401a81c3c44d280c0c40701d0035a8040b6500c5605200e01890f041640344120f030000040a480780a0507070700c50459502c0801581e201300e4207003d03141c5411489aaaa020341c080141808031000e41c08009418400c103400c41d0b00b84081c080e034007051245404207140130110341c40840025651201008208401d00000c0c1c0034190b0780b941d481c950704102240301d55480d41d50084520501c0008049601240141e2408010407010303002c3c10345640306410b048139200b01300c0c0305500010390700c2080901a01000701d412459003c10b902c030607007180d09001084605405083e50f0b8251068108500404078800b6003500008121019001d0383d100e0410710010109400e604443e100740c0b0071b15294202a41d04d40e80003640802c42075070000c545580c1c0100c800c0109000e001d4140d040707858900d41c100e0265001004502c20b100b55000c4802d180d801160480c1ca41c410403070050008560744c6955540000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 855097221 1250 855095971 855095999
    0x10510092c10050103031d0a030c091512061d0a031409010c06090602031e13110109031a07020c0a051804080f0c0a0203061b030a0c11030409060915030c 67
    0x1640d400b00d0741c260014240000842e0030a0300700f07902250500b14051500304140054946814043e15600d0b400f0b0715540d510101c401c1c85024a080598850295003c01c0c001c0e5080d4800400840700f4a4600d1b03002820f00800402c1189500320014084108820707912800240c409021035041d0703950300e080da403011618031003500842c00351410010b60b48400390203d2440d00a1115403401940010b0f0782c0c1c00e2013480a2a2044e040341c1400d00510040c04224003038260103000116507402c0aa07161000f02c042c40100d40892954000608840c0d000c8810703599581c4143c00340f407090305141c0884a101c1807a00c100302c0c00d02c0071841003035480413920328032040c03d485604105800c60711507001f0a0900c801105071360001d402110841080c2c1d0320400500c001c0d480e00700089504111481c24107150002d0f0038010746c400e440010884c000e000c2d280c4030540c14040c071036405000c00d038501c80c0c2a80d8465864241600280c00ba0744503c241084c200a00381441c00300c0c0f9544441107e51020240741c48a1800c2c080200f401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 855098471 1250 855097221 855097301
    0x20c0d02040e0706050d05070801050d0b0703140f2e060309050309120f01180b0610020c041a030c0a0b0a12110a0c0203011b08150406031401051009 65
    0x58a420324070b060140c04001c41000b0300303c00c0e19000c2d125040804001c0c00c6131401411a006c01c41c5400041102d81c5900602040668004540f01601d41d0382000a501900c01e00041e100c8049000d0b08115866010581543c080e0007825810311044d4000c0348886081405a00c4000e00c000c407950307040003014041d92043c1801071048003601e0400580c07500150042440400f80319417034000d0326001040910a20402c0012103030580074181e51810b5448504400710000c1c9824001c3c02d00d50006883c030b40c000c107c1c0809078440240184021643c00103603103000b002404a950081c801c0c2d2000d0101803400010746410f45072520301460a02809520440715410b505400300c1042356603211505818103e4801000c109440d03444a800019280c4180b40c01c450680b00b00c150006041c2c04c404520550024021b50000c0038580d5241c90621a40f0005000300020341c4001e01400840c14440701c1d101041d0403a911844d0704040781c8221030768551030b1005480342c40c081c0715404041c1383c0d03085120081c003800091080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 855099721 1250 855098471 855098479
    0x105090c010f0c03120609140c1305151b1b0f060304030f09031401050f0708100b090102031213050d020727060806070c0618110d0819090302090c030601020c0d02 71
    0x421703840c00d840d404640b416000360386003a8a4084200403002c0d80940141c020740c43d6201c45103004c8014040188560860154510819081801c00400110002618503800007030000040c18518103c00582c0c0c1c142c2d034107280740c140301e100102100310326050b5920f41c10101c014210741d1030740c0d0712a5021206640030b022007005000095001201140150314140c0c4903000c00000007034542800c00d8403400800e402040403007001490070802c1b4450725850200d0080f11161a10307140c41d071742d504005034194040d08150000c1c4400131010071041c44000c4070140c2c1e0700c40c0980d082d1840e100300104c00320786440d038074010035954044610000100c0d81d800c0c800802c1e501182000002c0040d255040c460074180203883c940000b0780b130f081410342031100b05e00c56000d0300c5410b001050b05c12401d6544210b03035415080c001c0c0f03114007844c2c45030000f84204602100c0c007540d0301420000100380c51100c0907100480c03c2c001a070155602030b00040e0403c0b042012a400f94a0580040103428012020852511022070080b81c01c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 855100971 1250 855099721 855099737
    0xa120f14010b0406080114010c0b061c080d1b0504030b07020c0d03020d020105070e0f0108060a0905160f03050609010e10030c06090611160515090306010312020105090c010f0c03 78
    0x3640440800380c601905034221800d42c0c40703180c008014100c0038182c001c2c060400300c1c02ea10454a80e0032803001c00485038004448e040958910002648207100c0c6184001c00c2c100302c8841404000300c1c07030020604640d4060082114066800002500311401c0b1840000318804000c01d00200b0b8030700765516030004041c81140c1d00180200040703005400611412400359110b6416a200c143d02030240c40c3d1300a003140313030660002d805180045d0b02440c5103640c15040c040080302081c519103524000c240a8541010107100c1c40c101710010300c2e0946689460880020718081500d542103110307024440c000c21006140450690034078070f102003241000342c145d5040120b00880003002a2502075140d00811032030311140c110074503220000d0035549180150001c5608921084040b501da91440f0700107441c015a4288006d4010625202c10382c8182c13400e507a45441480000002c10003a504401c1c018080e5034024826504d44004181e07440400200007804079014a60202950b0702c500400c5500500a14140503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 855102221 1250 855100971 855100991
    0x5010b031501210c1707120b0123101b0c230312030a2c0d12020c0c011404030f1415090c1314070309120201020a120f 52
    0x101d0080340ca000000a40c082030010001c1e0807921038444651508901e2481c8000000d99032100148105d000e20100b01410802d107a002c02000c00510000c0d03c0d2003a1154920046810000d005680901c5064030608900c503048080300140c15641244040103083c018006c1003007003007950301149141010408507080034100d07011403038848200d002403450000043e800115001c0c81903050420880c80750080e480000d24044000c0b4560449500101134500003450b6288120407d00c1c6c44002c604007640b901d104101a00c0710342001c12090300d050403e4990b04602400790220300c059000b610140d05158004207028420765018035015260b0000c40341b03c10380b0f000e0700c0f990f41f00301c030764184403040e1b417509446074481c0800d09003040341d10185048204c6d055440d00d8140001560b43e640c0c2560f0300c0c080c50450406400e0303034203176403c1110040c440040e0030300d581c5009103004004000d83d40b001e80e84602d851542c114024010700c01c6035840801640e070140b0741c1040759203400c00f03003444000e4052050780d5017107495 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 855103471 1250 855102221 855102223
    0x117070b160623011403010e060a110705060a0203010e0a0c020604060b04060504020c1e010902030d120912050a020706090518061f0f08010807050d0609171602090a2705010b03 77
    0x303d20295048080d580d54106100c100c81c00c54a090044d0082e8580300115014030f400084d60303503100e2486000411840c01000001850f401544802060703403080310148400c01007140c010398141c1c9e003174440001c000d9695111a0080d20030b6400c0c0000546c00180115000c280300c1e0304210207083c8003504c0481d8032640e8101060880c0e1100d031011701207809c0000303422219110314224803040035401d0001d002c2c41100d600000c3d120f101c0340b10b9010038091000307034160144035035400a6809640244800001d0110003001a00ca584240d104000502640e0070202e5054010500c40c4290703440542a501400c40501040400200281140341d004070078030183c4034242010840101075842603640e00c290001201409001010103811a58840d00100810711031a210f08400c0c004554100b00041042c159a0426826a804006410701c03000c0000412000c0c7c2288440c810038954403c0d5002031496172200c0c1e82030122641400c440030702c00741c821900000b107001d04454484190284c400040c11000f17000001e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 855104721 1250 855103471 855103511
    0x307050c1c03020d15080717190309050306250e181e100302060f0a0c050d0906021e0d0509010908030a08061002030a08040b070c08030f0117070b1606 66
    0x7403070000303400050945a40c9500e0040241c984c0b611104071076450b0414107a90340341d240078003c00449030014080f0500000082022014002418040400380c280b9814000c1030401c4c5070041c54081d202e920003190032081038100c0d19004105941d0540e0500010030021281d055220002a034004400748c9034445001005202e24099849203044035245007000040d0010795000404110301c81d0805081040035031120001c4807501582c15140555542c401c1009a03611140b8040140640c0b0a0888000c00e190b0890404005e5900c035808030b80d00840d9002c8003c03280a0705e82442c081540241d42040f80c0a0b000ba000703481c0070b00050410b010303641e454203801407864101c180b0170340000d0034820501ca641c0c1820014682c100c0c0f00340c805140f60003010480070300410b4014100070074818030307100002c00d1039114486501d0302680c0800000d40c1c03070512200343c2070914000c0c000d900c001071040c42c41d64000440050082c2c2140c243e030082e2400c1100d094048040b034040402e040c2d4a598495880d12002c407080750f81d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 855105971 1250 855104721 855104773
    0x5060408010605091308070602030408120f0103021912021002121909050a03050a0b091c05071b060f05030901060b0d1b050f0d1a03120403110a0b0307050c 68
    0x1500b10b2814040120390310340135109002e84201c81c031011010a0080b02140d001e940c00040140e0ba0762281e00c1c2c600350f584120542400000030400c00d0014459035006140d04883c022034a0038100e44c00603207500c202512521900c2040d100543c038141c01404c140c400034000c1c040b00e005881ba41506014a141e00343c2c040c0200c52600c0030f5201001c0542d9800491010103000280c1c0c440c0403060840d0307281d5645108466015025a080d140016444c00c0d00b000105086640c071a068010010001d0000c6c1058000060440d17a2801d11080613812111400743c0384102d540696540008060b0548280c40b140c3c4040c00c08482c3d07540b142c0d00896000300c18030080c8040e107034a02c40000c3c80740c10507000c418141035809840041250400500300001030002c01e54610104941000400c6034242840440e481092020725405018400f40d0980070340048014001301da001d89000079828010b101003000c0c01c4200e00070345030b1500d41130001c112214030031400b0f80550240c2004560321080559004004142c803144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 855107221 1250 855105971 855105973
    0x2090f1e04020c06100905070f0c050c0a14130902030607051803011803080a0c08010504020c1c0c12020105070c060b030a240e2a060f0c0703031106130b0c0405060408 73
    0x600c054480052190350051141e10007c21481c2070100e8014106900c000034141040610301c0303401c05100b01405100d017144401400b03410807a540351480c0d41c0801191010074440e60440c40d0a08407800e20b400382d24480d1354000d01502c45517882400035103407904100a01c01003450b1058156025803424400c0c0301e504c101c001130029a40d4076074034005085590007807a10070039034144001160020f0b0401b420380d041d60411078001d0f0300c078003002104524203200070807900b00e900130b0b01c01112825078025000413000d42c011401a51540301340442a801e986080d941d407000a0015130104002c124598414003803410018140c03136403050705848402d000d0840c0d211300018004c40c058903582c503041a00c1118540705d501d00140c5041d0f001c0d0364601e0540c0c907041e401808005445120100c50b580c4010031182103204880c11765440d1100b50030300c16928821800100d0100d402210800000040010114820558110600035031609680d40114204020300108050001404040351603a81c40c00038101a0903154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 855108471 1250 855107221 855107233
    0x1202071505120103080313062a02161e2301120e0604021003020f0a030b10050301120f0212030a05030901050f06031b0a0909051f02090f1e04020c 64
    0x903800058060400d001081481410880030320300b100d505108604407508803440071388940e110444a205251150700c020f20f01403603d112650b62010790401d148000707012405141e0f070540703c410140d03511159041c2500c1461040c001c02c1203840450308040c03c2500031100c103400c106a0310780c1c8089010030b007a0007a0898a07404803c01c1215680003011482030288108140080584851080c0d03c40300080d002900681d504c541d18101c1038000d03012151013a40200c00f095a03070340f0700e40009004003003a20405105007060300075085502d104a003502d059801d06940650042da15a441c0e2301d0001d00c0030001c907000200c00031407000d1100240094003200c802c5459040e500e20b880349205003104d80041141c034113034007444244052900d00151200d1030f002840007408403042c0002c0099200d100b540e1001301907908203a51282044400707d07146503151113138200e10a1880300003016009038061161641e811180e204104030300c51414500c04006981710060071100b142c40c1e00041401c1e82c1c4950000e0746240d100c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 855109721 1250 855108471 855108479
    0x30106030c08060411250c061701360605060a05040e090715051b03190f0f0e04111b0604050601080309010503010302040b0303160606080705030f030f1303120207 71
    0x401e005983c0031004650400c0200705502c0ca440480c0281600107900ea142840c1d80542441c1012683c0f4903a50400501030403e0b0b900e190003000092042c0040c07401c00420000000c1100300700201112229502c5050a00402c0d280a038035100100c643c0c1600034681ca81000040c5905c0c0d0034010031141103a95100da607207509095508500b0032018064415503808644104450303040d80140306100199480c0141d50b50003c0000c84071180400e107007050860000240c0e14071440d0806c18001d9051800f500c941c1e4404000c1d5030300340d60359144202004041603070391001d804a441c040e8881042001c2808007a0f080204607805034505100e110455261540190240400d000c0c0411170240140542001540f801141c480020014003040c40001d01458403400e45103047d541c188141d82166180400c441040c00c0f043c18039001412641c41200340c1c0c0e0080e6800401d05080106504482e00311a5005514044140e0140d044541c410245107031072106505010002509101d02c0ca4040c0485900500e9903d00f8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 855110971 1250 855109721 855109727
    0x302060402060c0a0b0f18030702030304050603041419020a06080f07030e01020c1606320912010527030f0423060d050115091d071103130f05030105041502090f0402030106030c 77
    0x4047e00c000010b42c8140f08180042e64000105c50584200b0744245403070352503038038000c030408942000d0015540075402c00903906035880c1104102a034021203019032407a54403401a81d61110a41da40300f0415440000a13044034060380090039040e000f0000103140a00110410b410012721030714008000020b12800c10201d0360148400c7d0303c13506120b52500780e41c10b80502000d01d02c0341c00d2151001042010810415654984101c1000160210000d0005103001c0791000c0310118003c0361017904d50400e148000640c80d00109658188219091052806041c40e200503003001c01000d404100c10402d0340f2143c1c042d10340300d0143c1016007521201158550402943c04c441c080b255840780c00b00138013802e041019044407083c6100c035204c5071007143c40e1915000303000c03030742180745c1000015148800130328141c0c11014201c0850031914501d40180c1d40e9034881042500340e5205840103000fa4564400c000954111607008186210008020000c82c0d0842008141640c100364014000f0076902c100c02242030390 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 855112221 1250 855110971 855111001
    0xc021006080c180123240309060c03090a0f0203190b040302060a020a052506060b070b010503010506060a180509010e0f18100b0f0405040606210302060402060c0a0b0f 73
    0x5210001100f166050500200c202d10032151010740c001e03491458070f1441d0b22540c42d50100a1400704601c1b910f6804a5030f61545540117589810051050b40c00284100d13020740b00b641d01070041c0c000034102c4a015510b81d103c4005203100282d034180190360700b545844041e05504003659110b03560407105480d02e41000b905000e0010040700c00c00b4010400c800102c0d0340401114841800340c1c101c0941c000b4100181c990700c5035401c60081801e403506030040742c00314040015103206e500c41d45411140c0da88804c141401d81d0029619a074100f001808800c031018024502c080d6400e450342c40700c280c015912000581111420391100c003c400c5100d05000c05039000f920040ea0282c1120441000c01252500c0300e6078400c4007043c218940780d41c2e01580001c40da1580e0600800e41d01c0104244100c0c181402e288008041c03511030610a0f5480110028448846504035003003290150058200f41d80d4940074044140e00130881141d01d8010b800454000500014030745001d2030500c60002c041d0b2800340d4820b0524a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 855113471 1250 855112221 855112249
    0x2070b06030f060f0610030e1006080f0712080c0a0b04030801210506040308090703020402120f0f090c220e010501031b0e13051c020309040f0605060307030c021006080c 74
    0x3e0050400c101c00c0a84404110740c001d03400f40c4011440d00d4401134114014195900034210a0081440d6030300c111000d50480b200751042c10090b10704008841c0c802c41e5840b0118444c4d041d1480000c100240410055005044203680880c00d4403400003007566601c06414003242c04801280c0c0c0400144128490103075011141801400d02c22510b01c880e4403003039030302d54000f440102040070b07803c0003079a0404180020401140d01a1003036440300f042c4503500320005001c50b1200c3e55814a41c000441d180303250f040b810700400301075010302000b03440a4103001c14085006880d281040d03510b014409519114800c01c1c065a2180c000080c45504525288491900c0801d64141c500d010280600140c0b809520302030b04a00b03400500c000c1030001c0d16065003803894246158050b43c107100382101820340c000c801001c1307050301110108040c011340c03180001202c0503400b885400100c24000503401ca400b070744c000c612041c0e540c0100c035074207010180302c20b05442060f0003d40240c1c00000250311641041410745c1600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 855114721 1250 855113471 855113473
    0x60727030209061002070f120b07020c06040e0604060e09010f0f1a04180803041b060306030b06211b210c010c0c240e0109032004020d02070b06030f 65
    0x41480d54001501c01d400190140344252010f00f00c1080e001e000f00440c0c001031083e40c1801443c00e07564219890a40005082541d00e124114005140c3c10302c04038000c0f0a13900010103031800c25050030b00c0c40c011018000c1500ea0083e41d00c1c0c1c0d010440c5104603540034414103901c0c0001c100c00c1c00700002d07601030755280e024000342c10b400c0c08140800804101c0a080b003290059400044581c4244090103924622010140107800000140001d00082e0101521907054031000c40303180300d039554011070803500141300182040e659040400c1e89881c2400310110428291144407000a00a90800e400e001001c1100040012007443c82042410715264030340b6480402c400b650000d0403030500c00340c0c0319070960010504015801a1400c10000b4604800000d0300800c41c25400381c0c01040e02600c11584548401d00208102c072170920580c1d88111100001d6070b501104c1801103590035580c0c01142da4214007501d902903000d00c03106004144910103840d11501650030441d850038400145404d0186502600800d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 855115971 1250 855114721 855114797
    0x20c03070c210b0c090a050607030807020712080301140f150a1206080601060c1707050604150e0c0f0103060918020a1e0b1b011d0d1d10020705030607 66
    0x40340c0c1c0c0048450b8401d200e00e5131296181c094200141c2a00b03429003109512600c04240e01050560241482c1e1152600c7d4089a4105403030b20400d039030307d6030b1441c0000d019100400041c0442d441014031031050b0341e000303849159494044000160210540700304c80b50102c002084c4800c9940e0b100d040404242c0340d944040200e02d09002c0029228007050096106000e0030f0b420740c80c2003110742c464080301f400510185544a200501e04107488800940b4241d84120161048a020700182d2082d0843e1880007401001160003250521660300d00c900d40043c107050382c41400044248150040c02c41c0030300390110204100555204119000c1c950741c1005070351403010000405000300007000340c4103a0304020315480d01c03440c1c06000680c5061110890512070350800d0b2211502d20190b03124840c542c2c40e003005071000f60401c1030003142c001a040240c3c521907006840da100c0f060918a4401000400d248141c0392143e4580d00401e19041c000d58152001808502c40c6c80350804e00400700d82c0b130600a2440c0400c4d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 855117221 1250 855115971 855115973
    0x5040507050a03150b01020c06131a0f0726040306020c0609030a0507060207020a050a180b01030c02070308031008032209020717091801060f0305090f120706020c03070c21 75
    0x101d40700700310044e010a0340d0754007411030b61a0700820610f0880b070402080d565690408603191861200b02c1c1c8a2480d002c00d0703502284c1d201c2c0550344c2c02c3d82c00c0559100f1038242400840c0d1240f218919100160300c007011150032158882480620042002e18007404c80540d40d102201e40e50703031405000a10201040c0c00c02d00c0801c0344581d00804441600750041009600c0d040c0d0b0340000303926210b1903401580d0254030100d00043c805008510404070b101c1e041c6c01000501443c0c401541500c0d40c0220090040e00050001d01c00200b51401543e000340588400d80403058071540c81d00d01d183d010b01e610740c65110181807594070011403041000094a80c510041d4180049541e802125080341c00620160f500045040056a1201000c2e6105050310300c103030032401c2d41e490201130024070716000c1101c00039040c6400070742c0c8801c0005c0c110301c465a01d14002c0034064141190480982c01031541211155000c1044911000c010806040c1e000d02034020280c3c902d103800e500007200e8445a5281114603850400c4030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 855118471 1250 855117221 855117233
    0x31b030905070f030201210209030d0f0206130803270f010b091018050a022206030f02030114190f0b040e070e0306160909140a0b010203032e030b090105040507050a03 73
    0x4d01e800c0521040703030b04003d904021f6000382c0608403000360148112034bc1e9148031a07104241505900c0550280d40703c075240c60092210941040380c01030005001007010600c0701c2c828803804511400c10f55050001280300d80559420561134180c214510303074451304040c03c1813400e03020b0150070902d1820000e64940c07034030b0880c0d0a644c0050b82d900000f569200c0000b200d00700c2c03540489004144c984502040501c0c00a142003420056010b200d00091038040c1c290000b1000e842128103903088442096411048203040002d104000c40101ca8148841040029100032041c2550003801501140d1503e441c03c000c1e00040410000701540c00b0001200440b1801d62004103100d90030104c1d0b052080c905070201c0c4401c0c1c480846991003442200e16001d08a81c2c0b8002200d416801040005000e0019007201c1c801266a40401e452000d10740030702103201d0072040110440082030030074000c03004405666903101d0008412044a10744a036945601c1084108841807050303102810301140c26401035404c50300e0341 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 855119721 1250 855118471 855118487
    0xc071e1203050d02031e01050402090a1406090d0b16030c4509181a0907050402030103050609010b0102010e2e091a0f0103150b01031b030905070f030201 67
    0x10100410480308040180761140c022182c080c070659905542d83c0c01c14809040c0161442c40c0255162400c1000120f81850f10703008031400e10000500d000c883c1400c120010416622030300300694408030400180b85a516082400c60703505018a07108030451400c02e080032200407002c001001010b28050a40388000e4000030104101c0000315070024085800c804451890701d104108045000301a404800068420034106800d1700c1e54408207004640c058030315081e5031400c01400038441d00c80d020f4090302241c03001802c154003001d90701c1114440750b41c030800300f400c81e4800c1e00260748640010302081301d5034000b401211480b84d4203100802240111038203032900c40c00fa0b8081102c10707480714030b5000f10013102c0701c4c103a4404c201c95000411800d174032440e099280d6891042c081604401e48000102071403d030748041c2e4104ca800c44c90000c24a030324000341000600074030704c1b40345c1410380d10202e030740f450b44a444c505120401e203502c00081045d0103090151a19003e54403402c40340c0c01d044000d000503640310300c0c2c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 855120971 1250 855119721 855119729
    0x290609070c1704150207151e021908180f030d0c0f050f0a051006180f02070b07080a0e0609030d0b011e0f0305060303031b130e010b0c071e 61
    0x3100c45140c801e031801d42c1100e54140d2a0011842001c03601150380206403815924481d5079400b00e4209a0f40e40108051010100c540c5901189008841c10f002c48034a101c0014044010700c141c0703000030519003030010b51200810050301c4501020902c4020706203881030101045108640408001c51404002950382084401b11070801030716040701c00400c00d00240041c44564000d0550340001e10300380c12903a071010826410780301071040703c8902085c0e24040c0301e080c090b0340c44260340e10f840350018600d4401801c800745410011a6007000000041a00500300d5400742e403803a546c01209042099100060311044c2c1c0f00c403c802c2d040300f400e01201103130000c1110740419802001084081300c80b801650a5001d240700c40c100c0d40c040141c03002d0810340c07120005070031062641f02080313141c0f100c1003815a2070104955541d94400c100502e42c0c800c220b03140162031007404a1a450754080c1e194002d20a0310303030003030f404000f94240101d00360720401c0d42800244040d240c030240a136070400050404200041c05489 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 855122221 1250 855120971 855120977
    0x2409010906021527151e010e010302061318050702074b09090303050714030a05100506130312180b0f090409050a05120a2304090929060907 61
    0x44c0b000e116513141c01103000441801d031500082d4a2011680c0b2041c21181103c1d004840202da80e0310041e0403210710306a4500d800c050111385c0c215401d0000552104500c000b030341c400c502e4001402900c0b0454407000000312070011440d414481d1001e80744c040c1c290456600041c91506d1103040044a020001d02c10101c104500054200e2140001552110119030724440400240219002920342c02404605d403090303808100540e1400d10854020758440140c01c20030800b0800303e0310049217a080943c100c50200805108a03940d0f000050841c0d01217903443c1c01c003081683c020428004500385501e14a00c150030035001064070f0f207814130901e40c850700402e82c1d074541c00306000c100d0301c10361801d0b1079004402403c20401d0503040d050469072040c840748101d48900c5007800c2c00100c0000c240590b401c40010f030304c07040c0741000c3c0359003842810105e5030704010800b002800001041065401810a501c0c014200c8050765203030b5000644441d81c26010348002045600d00313002c0240c503240501540404a46 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 855123471 1250 855122221 855122251
    0x1020717101e181703041e020f1c0506011508160203070f060603050c030f03030a09020315070809060a110403021e151309090210030b24090109060215 66
    0x45480d540b810030400d400000e585403c55058101a400f52420811401503020056019440b43c0603203540c40200ea008280c032500ca4040103031f100034500f034070303040b903200920b11401d2a1039030003c00c800401d8038403114007a0301a40c4c098400d100050202a015102c0c0008400003128100c0018120100181051465500d0420741d0500a4401e209903400745a02a18a22008100b800d15001400d0349003c162002d000740000c0350341c1881d0000d00d0420061000c400b45045a90396001c3c04000c3c18082026a010b006403d0000c0d010f020150115200341d506849001c440d040c81140c062a10303e006229a03040c0740740c0103181c0e056880300b105503130450b64100e48620380c0803504416501c81d451403142c40b5130022907020209200c130804102400ac0c0c0c074125007000710703c1551003440800b40d43d0300c4c440194111080c01c1404030518440c0d08441042c500c003030201ea004861030010450b03c0c040000032800208004500b101d140d69000017601c0007000544001d10351108500c050b604c038031002070084282c032800e079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 855124721 1250 855123471 855123491
    0x408060c07170d05070e0303030f07111005090303041b121704230114120103020f011b05010b0a060809061f1508060a06080c070303020c0c0901090b0102071710 70
    0x600c42d4080d00707400d54a40d03103440c1d03940e6032441d00280400356882c80104420a84008043c24000141e80c803581d0f2517800c9003016150000300382c400c2480e001680f034450280315083c0300320350300601610723000f80d04100c01550b9918150038401800e004440500c1284140d81c04104440091840804851030f0080360408081e84001c03414122485142c0c03040d21a0343e2009011070b00e0003150354103014074003403c5c1c85181444102d0f1a03180807074854000c00b420f58044090040c009410800d540a0b1814410b050503074841c9108030143c0c00f00c0c0044881103030305079103d042100071803c100303070b01900400700b908104c0c0241c20304010003922600018030501803e5103494015001c0c903038446105000b000e408513800410b06001d003005203501812a8081d004800c070307460010f0b015104080c40d0303100b400c2103004941801d22a580c110082e61100a0441ca5480b40040d400d80c25a038903c003050090070b50100005000c40f038100060304000c100e03407058021025803071800d041d02d01c020407030f00d400700742d40c1500254038015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 855125971 1250 855124721 855124733
    0x311120d020a0303151212121e0b060906040b030a0c0327111002010212010b04080a080304150513051902060d150b040e1906060906080c07120909110408060c07 70
    0x3040d0702200c0d06c00c10003101541880082030280402c11030959528400d4040301c142c920507103400e070030b0f81f04144081c101c0841c44c440640c1e000c1a9012402030101e488c6c90700c0d0100041d41500960010701c8001310000502049002c20310070389904c50000d04007404010126a01124a080c40c124041000ca02d5414000104043c000c40c0058500c0f00400500d01080f9035100207000303401401c00c013800681d481e000400d048441d001941c080303a50410050039680f10907030f039034416070b00040c10446002d584e01070030642c40344150140912030740d4207040349041c03036a40707083c00e038a03200c5821760044000703242070764080140c2c0b196001c03251309031903000c0c000c00c205003402542d0b2220b1006510440300e50b000880c02186184c0044800d1303004e4468802c0242e20010806d2843c8111203980c0b150313002103802414100326145c000c4500b158801c5000f2400d03414a0340a031901100c5121800415002030400c4109120941040c80f541d40000410040c940c101400c00c0d440a955510181041c41c0a46e4007251600800031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 855127221 1250 855125971 855126011
    0x6070507150903031e060503030a05130801090f020108010501052109030c0f0102093c1201020c010c081b120c0c1c082415130311120d020a0303 63
    0x1040c030020041c42e030103420010010100041004800c0740704401e08801a040c0d805030400303070b48000380034612b0240300d08020380300d540c05140180c6000780c805070001903940080c4503d100d070034003408031205c1d8608940f0004103441c405801850521501744410500306286004401840360b0070140c1c4207d9071510780b209071441c060020942524407621205030940f00c41900a03100307004050b0b944040f03000c400e000500300802e4001c40d070b02100c5200315400e00003044444200079482406009071010a1101c2d1070a030036a804034000d280c1e80d80d168500030b020981c2c0103544661100e4510002311311100b200c0382540d100d12030122840208011003003c01c0862641c1c00c12901e06036403502c111408201c85000c100782c0140912100d40110b06885c00085448054000c2200e59035200d03943d14481801034010802c490941d100e03060b841180500c00102d007800c1c003260707401c00356002c0d110007400c7c200c50f0001c000d10782d00440182021074105810481a10343c0008090b01c025505041c041265004a011528000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 855128471 1250 855127221 855127253
    0x806180705041a0f10050a030b011b080712020601060e0409050304090615020105070c03080f040c1a090f060c0706050a0c061a031c020d0f090b030a05180f06070507 72
    0x1c0c944111440f2040d001c8511499444050303d042400410305030030000550120601000030900c01c02181401c244280d01034006510705041440d910380701c02801c070a403180c86c02021104160009038107030a00940007514202d06010348000c084031341c18290000d000c1420013155502954445c48070400700b220a000380c40c064809080200030580e5200103016212061030120000740d40381c0320109104070321400c080041d29404d0b0302c1e83c0b80540c030303850400680350300c0003401654032804642d408500a80015a41c12843d4078104086072509600310400166a0760012030501c1080c0c01c2040ea000d0050104840d0202c4a030780c24000e403100c0025106690704119100c0041072145042c50302508010b14130645a404c4400b50103d03210020b1880162914846220b4131001580c0581c1c03da00d10b4034400c00c10910948031a1030903140d40d9542d100807a0a40c0c009a03503d12089464030108007403510342010600d0920f09a10003059014a0f00b59101e03210710b4042e001d01e04205002414005124041d4010b400b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 855129721 1250 855128471 855128479
    0x7121a2e03022203110f010219050106050307060c0f0305090d051501030c050f0a0306050a0902210f0604110613031401150b070201080a32040c0b040806180705 70
    0x245006400030025070004000e1110803401d4488103d07048010240241540c0d886140100280180d408219400980a50550440c0303d039180191180c00b00d19115481c50f03118100118100d4102403c240c204039150b00210200081d064166004c0743d85034000c0c0340c201d50181401c0d5545d012503008034011180d071200203402ca10500c0e5882070002d0800e03150a04990283d100508015210f80410003607001045400d6404684400f0030720200e103141c0c0c0401d4001c0c07203406002a01c070301c5030703404a8005401d6a0002d4030310304d48880f0000050100b442000c0407142070310083c090915081d500e43c5001b61840000303030302904d008200c0303035000024000d000c4080c58220b1b0089003111084114580601040e00d01c104c3c07801c010040000300c2d40880401e03078110316816101ea01c01e80c2da4040740c640c02001c0e80d49843d602e540303010f1402e8590500c903c0c40f00c2d010440c041100070700780c80c25080201804ea003580c46618402070403c01000740c0e52000c41e509402040c0078100580e01c440455485240050079006aa40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 855130971 1250 855129721 855129799
    0x51b0316020c120706140f180307090614041a0a1202010e0a080d18050f240408033103020d0203011b091a070b0f0903071a07121a 57
    0x2c1e42c3c2d0000381c00045500a540c1d032800d10010000050710350180180e00d4030714210900110b040c0301d140450b840320429001d02254249075480b82842c1c2607400b1a0302000022803560f0346c5412506003405603080522200501c1100e18006001150052a032446071011443c0007200150031680b250765003402008005104001c05a1035510260300c0c0c60100c415580400c08203200000f1103000c5048100c200c0d6001088650f0b003424010078481e080482881400191502d0b04031000700e0481000540041c083c1d00c0c00440d11014001c038100c08506170080c05c41000c4000c003001300b022840c400300d064180c1e075040e507400700140c030188046405801c0d0400b0396206184042c42c2c0132903180e8020103000840c1c4130103169103900141030f9603c040301d03c500040900340354090000111041ca80707175030b1143c0104450040f81d1511080781c8421412105403540007140d241d504040c040c0f160387c04991a806060f40e0681040003000c2030030340d21100c55011200c03900413848444000103100040646800d140100125092 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 855132221 1250 855130971 855130999
    0x60904020a0e0c0f0a0e0f030d050409020c010f020f0901140405090a1107050a110a050105121501200102181c02010e0303090d0c050102010c110a0f08070204090c0801051b0316020c 79
    0x1024181880e0114007d8001841c140c1580c82c001a1f4911050300c0354540c07920302030502d9400c4c006940400429030341ca41d05c03003012903138094440c07009200c00303c1841c01840d21800070a0005100fa51415030a4241072002d0006001c559500c04005410245211000400608408441c001400b800700040c2c2140901c0005c0c0d01441003081c03100300700a008840941800351103000544107406a030b0401c1c1c0141503000d001442d034a01504c90340c0b2000105050244c462070b564115400084000c7c05145090303500480c01c24051003003001d110004000851b00031703940003602d0340f18030010045c0800207410003441400203600d0307480a00480d2181107010f001c041802241b41800c1031940b40d40e00c2141d005605e80fa5a066440341b14076140c41e40c80d031040024003a00c00349610340000c04000140191180e450401c2804010307551842400c0800e0b2185600c1424149044041801c440c00140303042e151203a203038070081d408082401206d51241c105038184c0000c510908081f807508150130401d40d0440d002d0703141c0724 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 855133471 1250 855132221 855132227
    0xf06090b181204140f0d03090503010605040204050d0b0622090b06010c05150603011b02100c0905010207030206030907080102120a15061715090717060904020a0e0c0f0a 74
    0x144150100201c807411800340400d0165a000c0c26180c07040c9000b000d110602c102860000311040c540402000ca220307140b03217003001030f5060002000071004604000002c01003410280106d80040a00702d07000c5041900d48008501e002c1c0401000401035044580014490783c0c07107504444410900400c0d5640c1c42030703088600c1004100c1360310300341c40f42011407001841c25841880120201c0da030080103054005402c0450500b01100a800c59925540351007102143d03107000c2c0c0310b01f581032065034014000180c0d0707045a0700440f0040f1000e1020821440130a0086076000124003044a03410389920307a0f250760785020141003840d5608004615400058203507800e00e400da8106014040c8031004001c42400d080d4070003619121807040a011641107510700e200400d014070680e6000405100780d51a0005800024000c0f4004440c94400728150011804094814051140c0c1c05103050b00c0321100c0e4245500007981602040c441d01c4441000c150004941039000000d486001300003405081d180d0382003000c09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 855134721 1250 855133471 855133493
    0x6080a0611030c07080708070b040b01051305040b0c130302030d050a12020c0a030f171006031406150a021606032304150c1110050406060f1406070f0609 67
    0x903100103040c074648114240100c0c04580c061480c59041c0741c644100c540e61341026420020060351203060a10204011403035641c01540301701d1107030725250740c2036040c0340030050078500c2c207483c3e19240c9150204002c0042d203482040e90304410f1600b10306807107940e24150100d800c08980c00094160013050707504c0a0494104c409040480416281c90281201c0108098200d01881e014880d46c0e501081c04a00402c0c050700501c10301c800780e072030403402010303061000c860500300956503020142114501041841c1d8580701c8e91000c0004003120a40c0e1b800c2000015450307280c280140c42d001d060004208050302d0003000f0081d003484191078034440a50380e518004c3d0041044a42c3e01c4d4000c07090074061032552440c95103180c0700d40e41c4a294213403801c2404009000400b0b40e04112401d000c41081e086015043c2007000c001780180d0800e0203e1079142c14601417061300d281d80e0101c26100c48416080c45441040a0014020320055603841d0702c4050b2810031480311801030714060185da203094031003410300c1510640 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 855135971 1250 855134721 855134723
    0x303040b031015080c03100b12040212030901090e130c0f08010b060712031104050a08060414010504050304060309031202030a23190f0f050f1503240a0e0106080a 71
    0x503820025915424046141d1079220070f00300090001c0300185400343c0c0540139607000104120469800d580320741c0c40e5581e0398840e14207044030880700d004110444ca070010500d00c451500070003031410071031b15030b00203050b02c242c0380101c00302c9544600004441407c0d03095100592504008440100e0340d69092100c0d41e04154001c0c0c41c19942060304180c503a0030144200e50030345501174081f01080345a00b00440c0282410011382c030405c0300400c8001181c1e503a10058001511003000039006506051070b20911050403030030300501c1039061104100100d9008011380d4122035050901140c07000c49440e04948280d000020640350508c04028003618125030703440303001408000340c5040300c0481c0c41040502005021103140702d0f401c0c03070705035203404140142c0c2101d84100c44445001c10505100f03404a8290341d411508805001da0240401c1440b0705075105103007840505038051301b406440356440b18445410400c00d00d84942a94001c070381d140341d02e1351000c06000003030402000380c580c031041010b843d1420a04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 855137221 1250 855135971 855135991
    0x5071401060e010f0b03071e09030b10140f0306060d0c0e1303020d0207150e0105040e0c0309070f0b0d02071e05030309010c08010f1502070902040803040e01080a0b0f0907050303040b03 81
    0x901080344800b17641103030b004409613105c585c1d951080201610401d000304000c24100304007010b0010000315600d802c0e0340550002d040c00c65041d030510209400014032800e9041c4540c00300b110141c031a840110740c80d90854010399503040340c0c4110f800c00c040b0702000c69001642e41901c16040040c94440140c04c1c1d40c07514801c0c0c1c01e481401000030012640d807006806012101200b001c00840e003240a41a4901e160794103041290405544580d64402d0703201c201c41040c00098000f0030080000e0090003108080c22220107629100d03402c0c0314290308980500208858403030f500007031601c12311406000e21548032203c0e226011100c086407a2681d16600b094070b05035015820b10f1f08200206000b9502a41a2036081001000c01440c01148142c41001c1e101500d05501035100c000c1801c100a000810281c18540c006607542c40c0341140405040e20f05030700000c40c54100d0501c5c40c00082446421a80140503143c03100340c0c98403040062400c120700f69010b04e52610001900264444051020354411400c40f2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 855138471 1250 855137221 855137249
    0x3020106060e0f0a0521060c0901030608030a17040602160609060c0e010e0409030e030703030315300809061602030d02060f0f07030207020406122f0105071401060e01 73
    0x180a512400b801c4819030001101e40b0a006a082018244100210910114138000d1074031103e1b5007400010381e640e00035003200003103014041d41c042c06208010b0078060029458101d89500042c00c0203241c0740c070510380b42030500105040c0f013196016291002490000ba9a10403001e24104000703082c11013044440e181004a031038205401085c330055107003c1a101d00e40f1458002d07007044000d101c030410880130f2000000d410386403928100064800b46109032000220020350441142c45105940e00c00170008482205520b80d121540d444001a16403c2581c465407a0300c51900b40303814000d0f20401500300c040482c0c00d03001c0410844104603050b000703409071900c1c2c000d890b40807030301d80c2030031070714405482e203040081440c000c41001344aa0002b41c030b260050400c446079000030b050721210b9000384041e00308000a00c043c000072075603954000d0001c0301502c1402d031201c4d07400c030b66103402003e03180d05120010401c0401c0c0009130f22203912031503004008101c4c050301c0e405002c45021003070207141d00c20b403001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 855139721 1250 855138471 855138497
    0x3090615090b090f011a0318011409061b1c0e0d0e0406080d020c09040f050304030803070314061c030203120405071a09091519080d140708040e06060f03040302010606 73
    0x10100181030700d10150404403001100c1c0d4801c103131071f8030242119080103241e1480c0b10710100e081c0b1401c61505094039140390300341424601d203494404003038480c0e422020700300c1706424102c2c0c4c04412210141c0c0391a4540e4100b01203116001c00502503c03000340264000d140b5000c24542c0e10005104415030116010031038582c07a0004242d03a183c11590540c007591021440302242c0ca00b01000030b0380f29102d151240150201170317a500d030554020707030300460f44003074040140180c4a41600484820300c144105100c12454503800294103095450915001d01e48e160380f00701c06251007401103038094001031424900500341441c00954801152003982d012642800c80401c0c0c5068075000c45a00003030060a240c0c440d101e14195864035111055503e610070444190950071602500240001340345803c0030b000e4160001d04d01415035200c1500b032280c540003c01c00300d8002051442650305907078000045084070754850011030320a2040e144402000031022040100700742e81504000c080d1503c40d50f49004213200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 855140971 1250 855139721 855139741
    0x130f14061314011a042d08160312090e090c12060708010e060414040c080106061803060c03060305070806061903050c1324080c010c050d03090615090b09 67
    0x42c940c2601d50582d45840108180400151186590540c01021501c0c166076002000c3c11035140400c07001c0c407141103400101442c02c121180303200a18001000c0c04200e0780d0b001682c0c3c110040c03408000c2a4595000010340018400c1070140081c100b554010f80403814007140207035607001d010040d1031190842d4044035000840c0407801e180158000e8680038481e07401c18501181d0b03e80014000e5820554030002c1c400da40c9903019445014500030508202e010f410640c1c49800e491454002c801402100e0308807480303421100340c40e54200d13508131200084403058150b08400be0000c940c0050102d118485d008900394401050f05405203404842d02c043c1040141140704a00c0318510001d020354014000d00c07911803c2c00d1070040950241000300003038500b0b0382c5908074100c0d034a60b00d02040c0e2014503001480510020841d205850200b42000789598200da03a8070703903499000014890405485e0070090b820032103503030012001144500c000180030380c0c45840072401840d4069030103204e184c0c0040842c2401e18 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 855142221 1250 855140971 855140981
    0x2280620070f1211060a03020d0e061611120304140f07150e0a260c09040f120504030803190b2b0809060406090e0906010f05130f140613 60
    0x103031846074210380c2d61901d00071034802031440d40c041d81c0e001e1008005001c0383d501c90004040006903600c0050325401022000e41c01c50f050b4403039000c8298414001c3c0f003030924000318448146840d40c9031080042e21000301890034400385000030710f00c2000100a02080008898082406044010840ea0703400c4030842042e9407802c1e288225880103010b110380c92804c0388a41d2101400c2580980440009641c03040740d040281c0c0c01080071125110900f4074109038400a010160007d0422641000c05042ca80c940f02c01081e02100003c1c45089829211044c42d8007a5080e00c0045400101144d02c900c0c0410000c2d003441e003c200d034203074150301d401c5010b0200c0c0b41500d00700320321a110007400a0018081c02c06800b40c11b040310020b40d0803060034003509000750f0300e0400400c0a003421b60f0b00c00340400d00d000384950903428007500141042d00043c00501491101c0d0100e00c00312507048030750840c0ca0008034a074000030844407001000031810014201c00c20040b505229020301c0c0151034070385408280f40c0c22401107234 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 855143471 1250 855142221 855142229
    0x70f0b19090c030201030e01021b0313090b0618150a0806040e030307020a080f0c071206061a120c09040509060708060a0320010207080307061e02090d0228062007 71
    0x40b2007a141030002d540f10f03a10140d50054410300051400e5010191a180f000c9412081845944000b641c4041043c41c1116500102950101488002600400201d06020752849000e24003400120f842107941c81e0848625080320301c009a59a8241001c4000c280d00c0c021280eaa026038200085101000c070000f003128442c2000b81e01070601781c1e14543c2c0c0d4130100c1d80881c4000c030381318106000c044d00c805007d0004000800c4400000302c2c0c440040d14101040e01c160703034001450300b41c400c3d12000c11031303072075000f01c4000700e03c40325004180e42c0d0703440044c2115020310081240c200d07140c08100301d10b1060005820f4003c418641351105140d940c5410020011001d0000401010540050520101c9100c1d0021100785050044c0c03021a92904011803454210440560700d07592100a0220726103000d5082c404c5504056070700354034000c9004d0100e80b8659a0000080c010394040100860700c000a4201c50240101181c04904095a580303004111030212030100f684404c0f03861022a2355040052004129 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 855144721 1250 855143471 855143483
    0x60901020a0b040302011e06170d0f0309020a0314011401270e030d050403120e0c090606092e081f1503110307090303020d0c2006070f0b1909 62
    0xa20a5841c0b20b18104040d00840640d074856009812401072140381009000450300c002520f80d10f880481c01d11f144201c0325411864000e645200140b5501081c240c0880001d42400706440300d162000c25590095988041c161551082c10410b40d0700042d0000b050860110417171459998030b400b4107007461759508005130b03c8040342d0100700000041f2030300415000325440c401e036410400b030b0031410420b851003243c0440010380d031502100108087d900c140415019401c0080100d010410b0214500e40b501411442c86000d02090581b00e83e40c9100740401c0e401d5101d403230078110031102c0320000070462031000600003041d450000224101c46179510140d203850210811100c0a29140284c2034200300c0702c03040300405458580c0f10f1020102900118010b683c80d95403a41190301e182002801d26840500704420043c00f10174060108000050082c0102d0b04a5054170740700142d8000500c0600c00c9020060502c41c01081d845d0038400c0c9840164801c0d03a00401c5400c0440100d4615001c45842080003007035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 855145971 1250 855144721 855144733
    0x506010201060b031b07210f0801031a13150b0f011d061e07050d0809060702070b0c031611040516090308030a0608060f0a0e070602070902130506040e09010b06090102 73
    0x5c02003c0c002c0f03010030203625404649032403682d0f02d13041a041003841402c044450400413085080e0381c400910b003504955440c3c80c181c954115030b502000c02a001c080019069030402c007040c1074589002d000c002665114401c80a401c890441280107401c2c0211514400e0340240c00c0054554080c60100f00c00d13407200b070000c00101c880c0320100031141d00710381440401e10a00003003422055002d00001c1c158180240f0081245032081200281901002000280e09802050a0121a940008584007510400910180c0b94007801c0c1095295006110810f0504800c41c644001444400400c15007813440a0300d0030307c0140d441407030301641100b1110308100001c10f403003020008100e4845c09103030032202d04070012924541e5001c050b4540306080c4ca001c4401c042c1c00080c03220ba80a14402c60490030030351009000424a49500a034840c2c003035103e103800340d540029620304496810361004001d03040081040b900d6a440f104240440c850031101402650b203880601400340c0f90400664441c44016402400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 855147221 1250 855145971 855145981
    0xc030519020d1b0509090c240304061e1418030702010504180f09060b040c020105060a0b09040207051e070501030501030b0112050705040c020d0e09250e060f0a030506010201060b03 79
    0xd04075214009420344030444090120321176403105402070040b4010030081000e02c09402c01c10040320a003a03103603a4044a80d0521180b802c3c00b6105603640300d17420150018400030001725205000c00b560980c866090700c3d0064a10b020b90400b40d901e80284490051b100880c1d0303080f44c0c22640e070702c603941d0043d0204009000409c14140248580200b02e926444041500c0c08003088050a03a00d18040848901c1d4a0302559107841c20310f40b0601390038058910083c052802c11002185000c0b00902a210b168400020469455140e80d01120181d80e44001100c0185048004a10418140c2c4042d01c50902907014001820b46c42805040e05880d0003204202c0964a448811802104140da04907564010700030009500c2d80d852040381000d40d0b16401420181c014400000c050003101c20a40f40301c1e1118a09000b04441004072030414094001c254024400c641c05050b1440da150300c50140c0d2256001550f080c0425400001d8008108203032000e00490b107520005a0985213903000310702e802101403002031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 855148471 1250 855147221 855147233
    0x170a0b15060d0b03060709050a050f040e070e0702060a0c1e0309050a06020915070506010504021b0703030c1205030910020f0f0301090203010302030c0d0305030c21040c030519020d 79
    0x80e040985400360410000a000114010b9000101c0c50180d0350343d100c10003809410b0a000b559070201040c0740c402850b80c14840010b0302102c4034019140100140702d01c3d10a2500e403584403403201c2d04400210b40e07c00d80e503070110001c1090112030110060252201080c41c0212a004011500c03601303480c0e000280030103e01001da8040c11840b00c004050f02c41c04030001180040c881014818040c01025940311001d506020b0400491b092007210300c0010030a03000803e00110b2110b06680c6c0481d0f01594500c4c0e240f0200ca040c141d40c0b000310086000d5100e00004040c1c1040038025041d120b6149018030031111001690140021141038484d034120120303c440280c0b4540c001c1840c0f414044032582030030101d040f81d000c01c2e0000d1308041042540040180300707603e0300700081c45c40000d0849000c2c921414030f6038010000d010180c01032260300c13008241080310000d00d9904200358038070005d02d40c405144c10708000303059200900c015120383c040c0b00b207080c074016050b00b02d9280e11034018001d0800600c0a6a0344 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 855149721 1250 855148471 855148493
    0x6100c15051b0c070501031506211b03020c0607081317040b0a0503100801061a03150607060903110118030c050312041b080d0c080304030e03031909170a 67
    0x212405203040d4540e0a40c01c44400064821450010004e107500c0d41001c00150483d09000d00c3c0c50312001002c3c0b81044010b034022410252849951014081c1c42d0203010044003801300d0081c02c600a21099044200301a8076902038030030340c400312003160480d031940303901601e1460082c0c902d807100805150700381001c40e510800141000709140d00b6940b519039136030502881c5e43c01c40c0c038103900014400014483d030381d003e08034044c018180384d00c0200006c1380b13842c24000c00400e0103902441155404000150340380390b854001180c004001d40b0007551011185058402014000804c40118540d6409940c2480c1c0c14030516a0405504440360f10511054500385c070342e030a89840440e11403100301301c20742a451441d0a02800340b8030036140d551440704c160607100d9140c0d080350401403490340808809643c0e40d070b110740303041003458020003069500e1302c0c1d0f81808c0320360b01c220958854152200180505440c1185017a122041a950307482c1d021841d140c501240501c420300c400b01031a0345c0000006008114480d4030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 855150971 1250 855149721 855149731
    0x90b0904060203070c2906121504081606091a190e0c030d0f0801080606100507150603110f0a1d0601110d0503070e030f120a0306030b0c0306100c1505 66
    0x80c5d03810a4960f501100c800c01c040358420444608408441031040541606401000c00c4690030381042101007215a14004440d00d42c1ca10800d1001160501851800b1600080c1840ba22010b1100d440d041c0710b805003010039000c6038401c40500c0c02400062031048468014940000c02c5881201665092005000d10900c4043c00c2d001d90b500034511580c0400401208810742c0d1560f00b03000b082e466000c0d10004050b80300590982080c010401c0c90343d184540088500d21605040340c440759503003814060b025003841c01008a0703250020200c09c0c01a804129018014202e403c074903150319030300c14400b24084c14030405590180f61001003280c88180302c441c580c000c00600d440e0407040485101c0515040c0e071703422101c02107000081401516035000855590155003030340107100ba10003c040031039480f400485071703031141c0c00d001c950644002e01c40d4105000454200c02462050304215500443c01c0d842690b42c180324074801040c00141c4c502615500b2012074201e00c5509192248074400d13405030000800c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 855152221 1250 855150971 855150977
    0xa1202090615220e1003050715050c03130504240506180d03120f09021c0512070c080715050301030f150f02070302060612120904091a090106090b090406020307 70
    0x22003924064000e00c2c1c0400450f10380c1c8140382e69450100005040540641840c40108511505101041e40011481e0842e441003800b80003041c584e40302240c003801000c2030807035140400121104120b43c024441e07c20f44404940c00c01600220000a510802c92088140301601440c1c0d410050391411001034402d0040540c4480950400c1c800028294125007204802142040440382c6214095104d0303500c8030190040704000c0e819aa40001e080b000380b03918524215040c07480d0180c01c1120500c030310b01c011608016200d80780c000c6840d1074190211280205030310b40c8078401c80040ca0b032070501d186503408001c685032503281d0f90a588828802017240c034402e51707048400c01100c0d42a0005445485035100c0198001030b1641140c2c0f40082c145030000d0a0248140714500d490f846e00c2802003800405014807842641d55400c40b03802142c05031690a402500040c0c1008805001131840d541480c46402d1820081144c246c4950b9000100c50061240075001568400000c00042e401d038019038029209007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 855153471 1250 855152221 855152227
    0x122f010c0f1b0609080102070b06060705010e0f0705040f02040b0a0f110d08010801143c090303180a080703050d022208010e010203090307030f1e030501050a1202090615 74
    0x916031041064505121a09084480d81c0801c07a282d0b01803a2840170b804103074001c1d8644030140d228441080c0e00a07000340d00c034042c00207940c42001000d6111a03072604401d03041c1d4110301548400143c070b441e45071050314050740c140301241e41407218078801c850a590040c1c0502e4140360940d031f000c03078800710a1008241809400d1441c0d902400c01000001c1118034075580d81c200c150304000726542500c07008841428083c11f21424451020131504258178640c001d914039401c0c07040c0c00084030b0040052701046d2042d2034851b038144423550b40044021803041040e0025000e200b010308441d00c3e40c1c3c02030804051700344d5409000140c00284100011b00f00c00005481c003606100307000498860032002d46480d0000c941e8101002c04c0141401c0c000e005041005100840c214a0140d0070680c0303a1003100d400504024420303645080b01406046030646045818822924080300710b440039000744828081d0903c16905100006061608103c80350111035001d0000c003003d40b1280207001102a07100f8094003401418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 855154721 1250 855153471 855153473
    0x2030403021819060e160e1323040501020703080603070b0d1a04020c0a11040204060801030f02182d0c190201060503030c15010603092004021201122f010c0f 69
    0x501440c0041d09516106094034200b04052401b0030300d24440340020b00c901040d07005e0031566460100200ea001242003c5403a00003050070582c0745c10040382d642e0341c40d0b407200d080c007060020550103050305031712940359000c40e40c40f09010140d480111348100352429004000c0141c142581d82c0080c3e0440c54100c403041190b42c000c1c0000b4051780c11000d052025a40b080d0034001c10301c040bd1604016114086d03c0c11803410342000001001003030305001c00b502ca16000c1c144d030021911039080f00c0880708107008440da445d041c00b0107450034034005000c00c144c0c1e0705035004029007500085820b00303002d42d0341550100d1070081c440041d90312502000210409556039070a000500e9142407005061016140010308401482c03140b83c103000c1041a04408101890300850400064450141c042c0d00340003a5000901880c25000140c0030b4031a100780c03481484048000002d0118403e000c40c251a4801d200030b410303000945d81006034030b4000900c3c10982610400700b202c03195008490011649000701c40d00303141c210203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 855155971 1250 855154721 855154771
    0x80901020703290a1806020f0d060314010c030605010c0f0507081608011d0c150d0f0903030f0515011409030f1f060806010303141201081b01020304030218 68
    0x43e0282d40c0d0348494410111a02d20244041d07002c3e84070744d661030104001d59000b044464851000344004025940c0000c1500c81c00045e60306503051800d02c0401071041640700c0c40e060805440b201c00310701040d030074410710151090003401520f080d1035041c0c2d102020009240c82d4044100291102511030340115000403581030400c5c00300310214601180040442880c06a54a003110f84481203200542c4e0644e01c000c44031f10000c20000214030084640c02e403442628600340c0c525100300c03604508101d01d40204042564901d411094000b8000d460070009500006e140201780c1b041110201090700d200405414158080c1c030700e101c00000085061418900e40c0404203140c0408442e010791958001141c0402c1413030180e0010500e0542803600f445020b2424001ca641d51006000041c00d020b0308004010075480b413001038441d03450031200108101d580d907008140d240c42d4005140ba6a58460742003100c001d500000460b000ca03a07000d403034541a083d0910490084110180061100e18545c0100340100c00c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 855157221 1250 855155971 855155993
    0xa0b0a180b060f031f0509160f06031404020f040e0c09250c05030a050a0e0310050a0c03110301090b030c03030309010c022a01030c140a0914060c030403080901020703 73
    0x88140708005490401c2030070041c0d4001c02c0c4114a110f41d200380d40d20f01d0208005900c2480c0c880042102084940b10040c0040c202200c40c0c058450100b00000001011900c14188004030b85294404100904000c5e035110a803500449020350410036030b640c008003d00f400d0740040084c03142c5805541506082c040080c50703c07002a1a4501c0f00c4110303000425141003445050b140340c2c80c803801e00310240207980d42d0301516800f408040d04180440800e130002e019018004d21108400014191511880c0b45000c0c040140016212405280d282588680b4094068480c1390002a240c510241c11607107018980d001501d106506a034046c021805403280c152420005507000b01440400411100e0341c084e0001e244c881c1d0350140402d00d9510f0360849400c40070645100f18080003e2034040359182c0e03485010b8503800302c00e120203040300000043c0c1c82c42c007550000329041601e040c841443d0507414280b003041080e014001c11040341d40c0007000204001018071005105482c01030043e941595079035100c0a000340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 855158471 1250 855157221 855157223
    0xa0303051504020a02060c0c01090807200f130513060e0714030606010c02010305100503060c13090213051309021905041404030206070507020d061d100e0a0b0a18 71
    0x203844400780241150a41d407218a941c605980450030400b140b0802550303048040c141107209400001e01152230002900001c000b40e41110b00c5a50f00e0045103801d94280d003405000c54212005807032042103d10301032409040505000307020001441c2400c80030300092030b006e0008100c0210000744040094814080d1b400c900d0303491f070081d10322a49003002403501042041c010510030b03000301c000c04c01282e030000d040d110410b4082c0ba00003401c1e07480c9401600c10b222150400340d13045c824542044040d803104030003450305040041130300600301ea8400c0120168000d00e082822041c4a0075024802800c00704030303e0003001045000484c4140990300420041c00c00c0062012002108020505c514109030060b0200aa20600e6422080c54039450003034440d1006040c083c1081800160081036585181216402c503801c02e004200786130300014040e4003c0c5200c2c0007403516000381c0703582c0d9840b00c54502c60981020f16910190048450603a02c880340c0303034001014420200d680300140120300200103280c104407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 855159721 1250 855158471 855158477
    0x6010b21010b0c0d080f04080315120d02190209010311010909151a0702130b190906051512010902030c0f0c160801020a1416121e03050f130809030a03 66
    0x142e506040c1040c00c0528044014081c0281e0201b03000c0c074000d0502c0c0c959400383d00410041d0f03d984400c03400c1440711074915400ca60040c081c0080e407404041c08661510001c4903502240e00140002c81c008405c84003111010794099800030040000c10342c80c1552600c076650515010034440d890381d00f084100c940030704040c0d6803041c0502080c02460292400030501400e5800214241f00c2c0c04e0f400076003074040325880a0320154440000030000c0d100c610214118613002500480c00c1c035100c00e1101d000b402c252017580c0c49180d100c00b80030049174080040380d2008640c5e040ea952540e08004201c00a50310107400701c041600c00b0060f0071001040701c000b90031010107410151105046003424901a0025500416641e0b4810040009030f944c100d040da641c4040360820481e1141031001004118075082d40d005003649203100140b50100c1d038040e4202804000781c0600176000101100102c04440b0105d030080c400300007180214090600c50740c07641001c2440380311751900c1d01c18994082030034003801090841c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 855160971 1250 855159721 855159727
    0xf2a02030613050d03050408090409060f020c33070c0c1203050a0f110d2a050709050c031017070305010e0d02212a1e060603060906010b21010b 63
    0x1000000d00c81c4c00c140c200310b841c0034030480c1030544a03002644607400441e44956a5a411801040216040319039001e1003c078085496400350100d154445000510b60482c030840200d0311111200c11851030504034541c500c440340f0641e0b130700b0800d90713070301d00c3c00e500a569170801c240f030001e41c2c014085006015540300340c1c0d0740c5480741d401d980c0141030042804600024490001601e600c11100083c03032900742800e502d840c0124600001001c2c24240420480d04030359480803480d50140311001412204907402e4202c00c120b01d0341d440155103407a00050f0341d2405024085c402c10070800d000d05503070000b44120142030780d294070f0fa00d40d50340e0308444c40000320402c542c1240c4003070b8040503014450a030314164003103602c011805c220f08191485108610350100d000c1528154800002d220050150980811a046074520f14a1780d900003100c45110207003140c1d520441c1c000a80905012032402d010b6810348004102507404c09500012680241070a00c81070035401110800366039040e000140240040440244e07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 855162221 1250 855160971 855160973
    0x4050c060706061d0405030d0b0609100c150203090d0503093d1505010f0519031d0c0f011103070c14100f0e010c020a0816050a060f2a02030613 63
    0x4181c18003d400051601284c1c0421022501c00300c02c80e160303103d040000150b620240f000042e2240640480c1e2a0003050031041484440c1c3c0003000b00c0d00c2a801000c8210389000351801c58026031008441d01d042c5900040d01c14200036002d10051030b0004500c00940300d555100010126119030650749022500180524246078844031403040090020002c3c0d090001180d80c2044000c606007030720849040010720304550810f98446d5054410700c6212081407079101c1a211802800751a5008403d10791941c0d0001101030f00d00c000071026050200606078480200c1b285005580480844d052807000303001c2005410001713a80140380b07001400303d0b020409075445c0702c02d0034450754000b210811410f00a03900200403400341c110301440300c009001d280100e01b0b201d261010890002955203c84036600c41c045100c44090300d5035501d0706c1619002d0710301040041e9035900444d50038070a00d441c03501240f0910241d20500c0301000f190f40341012141015100720809a02080c600f1100b1940801200c0464549078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 855163471 1250 855162221 855162239
    0x31b0c0304060305062e0e0415050d02120a03110705060a120b0604080a060e2527050a0207150c170603070f06020a1a1009051503070f0e0901020304170304050c06070606 74
    0x100e007d800035a0b0400c011076641241030160212030240900c01d5200301c2201c800c6559140e244400100000c060b40c51010381850058101c1c103511584840034000e0410100d12800c00005441501c0d6990303452401102076522900b008004c4614a01d030000b00401011620082c20010901920300c51400020040e485c903001605010b038101ca154071005c00d03040040450b0712443c0b5041b080d2981c1a04503a8903510b5240b1108900321200d4a806489050808000000300994050f24101d80903107070741b030b00369400100343e481261003a83e100b40100f4410902407108103580b0164991000001e0100d0305015298a24007240420070b500000040c3c0c04071071103c0800070b0360720701300c8203046100420445500b020b202703c108200382d5014240c04a0398400004400d04c5010030608016800036007903910442d2248104040d81030030b0f00a00a5030b2140d1004116003103c144200c03485541c1281e5080140c202d2441308007180e900151081da42441030027040c9103035a0b81c0c10010107419124201c00584245840366003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 855164721 1250 855163471 855163487
    0x7030c230a1d0a0b2104061a01030c0207121a0405010c09090209091b160b07030e1b040c02210d0506030309030d120e060c031b0c0304060305062e 64
    0x418820034524002c071255115a0703c441c007034402c4d0490480d20381440042e607840c200380c40c44107400b0301d0b402102071100f442081e6011103100a9000d01500303034080e80c0c00064050f9001c0c50301c1c86005901000d0104042d100204031222030b544038020100c01c1040070902d0b4402c07500c090300c1c1900c240e59070303008035841e0361303041028503004007087c2806608000740b01001821900c401040c035070305040105200480d958046040320b00100802c1c109600c018081d04210500d03d00489444000c07a2400c02c028818072400100c400f80b29201444824502e81c069040c08054070340d05241c0380a51240d0034100d14502d0015251124000c42280c242c4d40315018000300e01c0a5030b03005068207000390010070a880c516180800e540f0307040001800e00155090300e080c1154014089032040150f42d0040600344410360100000442c0100e503454003152812081c1c902851941c801ca10a40c0c070240c2c82044200401c40c0240c00c01c650155000304150080c40100380c002c0c00d0f055916406904c140800000e40b40b0aa13000332107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 855165971 1250 855164721 855164747
    0x12060c1201050a0b0403030807030608100f05060406031112160605070201020c0103090f02090c040510020114070212040e0c040b0a0224071709070b12240907030c230a 73
    0x8020401c0d40b130311101111500c10385c0000b4040008010016a00354002d400002c01824405c0c01c4400000044090740c00500300301060b019114144000300b615458680a05000c3e40c3d0019a24000404100d08008030b02c540c0c084400382c10f0041910070b0781e0220380d0b0035622000b0000c0d5220305a43c2e0145100081c00c100304910725505052034000150080341009c0174a8440c1503054030889a00e44179040701034981e0040d0748c040395010301214209001c06606401240c0c00710500289545d0941307035500c1c01d0362107641d0544480716110f424001002848aa103c00b903800101e2804118034064860040803102d62104016a016a2081742c2d0b02a0040002d0312011348031140015894003424040030040c003c1080101100c0c01d03400c40300100d800c1c0c003003e00c50710009003000708405580f0001c20104030003e1204480031100103801c0d1801c1d0769000501c1c00400c3c0030980c024942009940c51200c1074004240402c502e000f00004591b8071402612000c0d842e10007461012002c5450300b401c100000c000c0490100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 855167221 1250 855165971 855165979
    0x108010903091e0515040f0f050607201f0f03060e130302010216111c08070b07030b0312030907050409020604050d170310050f100f080612060c120105 66
    0xc0c0000100782c0c8542c0d4101960100110358203c21000c1c651003120024030340106030303c0004910b0707412404c940d05000300203c4101c2c08240405035618041007003409100d1082c1500a041040744100003640d54450503500d40c015400000100c648a010866510405515801c44848201d11a201c26000021010011410300d0305001c100d04081000200d100054415900521003003000010507000b034046e90389280307211500018200031400c14248101d007204070340c0d01801b41c01030718500c1c0c662442d0401003259040074070146080807581d074205440348000d046e2410181c0c1e420182c11259424054011001c1d01115016241c0c24074650301820420384d64400351190349011308440c01071b2141416a01215411101640003c02500b8240881441700c58540c02e9024000700300051503000000540c00e0710415240c00c10401803c7d0300f440008401500c5003408107440d65030300400e091040c0c491590145001d06010703880380f0b01800d41c2e03251110a546070001d105010170b9280c40000b81107100380c01030800312 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 855168471 1250 855167221 855167231
    0x703110609010f0503090106080114060a0b1206060d060b0a0c1104060f030f030516052404020913111c05010b010c020904060c091a120a1116050111030f010806010801 73
    0x407001034400140308805505000003c000103444000030740c410300040000c10000d03c4010080c1310041540c15003240d426200300d0030401c010801e0740107481903800440003036a0346551912000100540754101a04540845031982030100b4032050007005407a4a801c10b0300e0b005120107140c606068502015080c0d9800349140150400034210030b00082000c694115070411907070350321800e084402e8800c20042140d2810340040100401000181801503803502c1c3d245608048040e85212040d2003007610003070350100300e010110700030b1030300c801400c070303003544102d1401851415441c0840d0001e00e01400e0001c07086055000b0b00c080c44020301403c404108240f0701000108025400200c0715000908058007296079440c219848a000722031102c081d081c4000b1a103002d00c01000c0d60f4090fa80001c214045c1403031200041541400280105d041590014003024144192030f00300741d034202c00c2c2071410380701036481c0c44005d01038070001b030300075800750441c952400540c4d810410201c0c40e007a41072b4001e44140e8502 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 855169721 1250 855168471 855168487
    0x20d06080c150c0a060c05030a140105060f090a0f061d06031e070207031509111210020c1006080d110a030e300105070f020a050312040c030b070207031106 68
    0x39500c00c9880c121140210743c5500000101d80d140013074040b4000c0c9994505607113044400d4201010354800d0f226210240b040700702c1915884d505800038800c064100d0411b0141d0b1a031030207a200034099880001c1c00003c40155190300e0400075200c1a071110010822400c0030111b401e560307100580c140c2400340d41e201c0c95030400326a1304601a00e0030301000215140c60002c41c0010b4401c1c00442c0c021038000c600d1107031a00141c080c60008000c079243c21284031041400316400b50400711304070401202020080d0007407034160b2030300002952081d1720000c2580200900030003071107510b205401c085c1c07803880000d0022000a14000d4282076200d0740001c2c06a00076440600041d074050301c2c2203002d200589259102484241d00c401904540304054080c44040100e008481c060551055100348110fa8544440440c1c02c901a40c41e180f100502501c01d1b0810040d00d403800a034146003542281c8200846c01c9195500e4032031401065041c0c83c00001a04111410014407880c0420310480440454030750740b5003114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 855170971 1250 855169721 855169729
    0x605010b1c061a13091e0b010309030f0f03020405120f0106120c03200409031706181b090d060c02060601031a1e0d0f0c24030509070506070303020d06080c 68
    0x500a28843c01607000a080380204010320260001040280010b008004a00b81c2c1c099a0410a600040b0003a280400d1882190301c0f07401026a1182c0549480703104121300807089914840c19a44101030523000c12000420f903c80754142801c504c041005000301e40c9002a6850a46105510036442d01202408640c0450102d030000412a580030070450701e81080581600c001da0b0150440c0365000e0301e00348552040c11340182080c030010303003060000001552403000b004541c03041248441c41c4130290100064105443d400003020881001c01140d090510103400154282e01100c0200c81050b100d8010303030602c03a0100038543d0800300c24242442042e515130412180c1e910240c0c1c6591041040001004032020710321250380143c58007800c1c0401240d000d0400380c00038881b0900172a00b8041248000440ca030f4800b00b0f1440c2e100740d01003030b00740c0f00c49241811005400041e00c80340817401071784000074117603079160001c0c09014400e80303002d40c5403a13004007000121002d990202e40390b038024400e03a64040e61 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 855172221 1250 855170971 855170999
    0xd09050a150f0c030309080708090301050f010614090d05030c0f010c05091806012c1c0305070b15030105100503010e0724030204050d1103060901090b040b0c070605010b1c06 76
    0x710a240c40001c3c0c41d02800c0490103400b0b41d60b400307000390a00244850900071290000c1c42c0011050b030080c0a07507114020700000c2951b00740b0400d0f0004640d200400c80e0501468001c1050440061940003982101e407181030465101c9214005203510040e00d072103195400f80202611160242016424241c00c44c01040303007010a40e10000541e065800000d801360f00804100c001c0b5601150440a10302101000c0d22100c050300289034860000c0390110499641441d00c100e6089605030740c0e080c2000304940d10320b5603aa60191134a00009410740c0003a039603440901c5007a210f5084401500c01e15454002490700711070111140c01c03407941041304d042c0441200700d80e42c4285480c4072444a9412506507104800a004540101d82c0c4032a01c0c6414609102c0c8002020300d81c1078049042e24003e444501c0c44d6800c8030440b850003800031550800140204003207020090788806960101460484d51340c1e10041100c100b40c0211003034000c04100c0c151800d031000074180c6003540e014000c0048506021643c50641 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 855173471 1250 855172221 855172247
    0x212061e030a140114010303020708010b0913023106050a0b030402011d040b0301090b0702010510080703060209060d090609050d0c05060a0513020a0312031a060306090601030e0d09050a15 82
    0x680c1c010040c114001d50180b100d84030300c0500417080b941c582c41c1c0251500114850b0391055030908942c8d0300f0626010034014050701c0380113047d12442b4010b030700303005d19481954080c3c4010144542220018035841c1034405001c5039250300002c24038100010040200455003101092010a02c100300c0141d80010190504a544e441070501260b00e850010b00608800188240c05500f4680d804040015403005140150416002800581d40350380d000300b00815184183c2806a01000041001c100c45500402f0802c1001e0710725490320035041c0580c03055500c02101244c0065803095843d090080500400791646880e250072015415151500b6a0f10758001d0202c0c40d0702c0f9682c03030200302c150989805200d0050b0b400381881c2070250b507030f0510007202851245903030f002c6410925501d0700c03c0b201c0d0714000700305000144401e0850f191a0181700f22110000d10060501d55a0550111021401c00c10412a030500d6510000314038241000d114180005a2200d81c041541c45042c01c0d026401c07402c5444a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 855174721 1250 855173471 855173483
    0x506250f05122205061504050408040b0c07031a1b0f04170a060e0f0601060318030e010c0b2a040806010605030403030204180516110c12100212061e030a 67
    0x36441d10707228403042040003440750560f201101d01d1a01000008140503202c0c4c150901005c05905a620900040d40c500300e80051100c1ca08210500412001101074a91040b1080440c0d03075a980380e6407103e00c8011310310031441c0c14080c86420400e0480c5888081e142c3d1030b0f44542c1ea18103181904150ac0d01d180900e00940c0031a0300d2080390384403601e108020481a040e003140c4284400035106020701d803100e19202017000c0e1030140e82d00125070103002e40141d8204003540d800054031054252001c503101c00101003590b04225880b2140030109041084140c01114016003c296241100c00100c00b0060040000c403600d50082c042000f014a010500a0446246040c0329030341c0d070340304d1504a00a1045401280c03600d107040300c100f812140c442d4403952003130a0401e2221082c1314242c00541d00c44e2030250181e00241d00c440d105582e1818100c5519103080d4010381140c80d068505c4580d00142e07000900090746401c4400100300e03035458030102e0389a07803031910100042c469550b1000b003a01c40102050207000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 855175971 1250 855174721 855174757
    0xf010b0f060f07080a0e120c01090306020a1e030f0605040b03030403080a14070c0f0816051e03010204030b0f1b0403060504020109080d0807020106090e1e07030506250f05 75
    0x1d41d146078040f41c1420341c0c0280203c1d95602c4c8414042d0002c6c0809064a00410341d0b4801c003103071450300041c500100e100c140c485a41d030f1480c55680034065880311031003604100c410000c030100010b113103030300495028143d1400708100c1d01c1d4680701310880300c41c0c2e40550720a45c248140b840840c1c50200803103007901c1d0428652a984d039008041919030345174800030844185000241d030010302803484200d400790303842c8221030407040c0c1d514840710799503011100500c0100c0807540e00400086c58404284004400d0000440c00388000c10740c00242281c10542c025103000c822281080164982480f407a90700980a2184401004035843c03061458040c500000f0449075541c2c000c1429680031354504030062064400700e4061041041006007241c1c425070350403000d582010000306082c003031401601080d580b030000512040341480e509480c00b9069098000d1b842c000c0d48008000719506000c03245c421000d107015152010035000c2c3c0202c10b8450607030840100314088010845083e441400c0b900d1031001c500180032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 855177221 1250 855175971 855175987
    0xb090a0506030f010e01050d1208090f010c0207090b1002061302131e05102306040b0406081005011e051c050a0c1701030b010b0706021e09030f010b0f06 67
    0x545503a00840d900a0011040000310148041118140c600d00440d14010341d82c0c403410b102510140103070040c010000c0c07041c844031a83c07291412a1b40001048120f40c0d1041c00b032200c1500311080002723040d005800c13a403401d0000d000c240c0290311140c0341c281c1d984840d1984102009440d12005030844407400340d0603140205555904014000e0b810510508100000c007050741010348286c1c40d0305000419080c103000861100d641b0154008594203410700105402c0c003401040c1c001004d2280b66940400b040c4000710303003480318070082c2c005050780d80ca501c452030030b0514803842c4c00846540414104070390003000c07c21280d01c2030090021107001d0309080d0384907005040030030702c2a81205145d217031440c80c10b001c1041c13000c226000120440010f80301d44c1300154041c042c03844a5482408003410100e0f640c00104030308a490001000218019034005080c404142411f0400700705015400100c002c0104010120b803405000c05440303914414000c1198520003070210b0518900030b12003611584000c42d20413 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 855178471 1250 855177221 855177229
    0xc050f0706080f3c0f0f0c1c051302090f0c090f0102010902300105090a0b040302030c0d020a0303050a2904020c12040e0106091a070303180c091803090b09 68
    0x1115410304041404c4510745555001090a000301201c00b0386424010007240710010f4031410280502d070351070465078840c0d8440c0c0603c949a4000201d06041100b4404600103180840c454980220043c00f4141c028003024010080d0720b0801800440319140d45205110340380400c0c00880305420f90507a004440a0039140050b801410265000380d00710b04074441801c088201002017030614030000c40c0290000f2201114203007251011219001d803640002d600c0c601090807070916641c442d20070300c12a46030014180840c6d0402410000c00009030b405400700e1030030550540201c9510082580c8100301a0311142924900302003094904481e28200468040da00e44458045603d55001e860031100d03a2106440d600030310358001e10460313450f40315100002c1502441164030008490007813081d481043c20114210140354040389040741450f81d034681c24442d111100d0364a14501d4003c640840041d840d00429205446200d94a15008805003808000113a00b20354000141e50345054040c1d21504518082 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 855179721 1250 855178471 855178501
    0xf07140708030415050a113106050903060f0f1503160806060a05100c08032a0c0d090b0a1d0d0f050106080703020f0f1f0c050f0706080f 60
    0xa081100c1c0002003005000e030110f5a42e81e04410038804020568516604508640f41d00c00451303100c150401031110407001e80c070001c8541c52802c54041c120b4440d403c10900d41502a540205c0220f00045996911450b051003400d502802c00d02014000323141904007181c2090740100042c5440c0f17030b04030b440c2c0c4e900c0e14204450407001e00350b0403540941c40e0f05d51b84003580d240821100c09125001c024000301e0281402d00103e20000483e4031003218070380302c955515200c3e4200030030031018002c0f1030008401090400034a24042c1898945460380c0d40403488603103041801655042080c018000000c000d4807100004030f4000003520300d0310045400d004546188000b514502c55075020404801f65814001c5900881403928810402008250355032802151a82001c0c0710184d80710450340300100050030145d443d042d03002c0c0000e00900c1c40c28101140e0a034000b240d01c13001c800041c0c01041d8039007000000c10070b480f02409250300501181c1e1030101d0040c0614801055a10300401c02c102246541e0180185 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 855180971 1250 855179721 855179723
    0x70f05100501180c17090a140d0f0507051006120b10031212060801050f06100e0f0f031c1110060311040b0d0819030b0402130e10030f08030702010c02060f071407 71
    0x281e20014201ba848041d0b5895011700195908596501c0026a6072030000e140d1210150a444511003071141c0b010998070354010700000c0d111402064100580b9405a205e00c00140522480304500c0400c242041524018010620746a042c808941803000c60a9009881c40110a610b404910b0f4895411f086015001c5540310a126600b07203001d010802e4500c84550388146420744141c141b02c030784d01c201124100c1c494844907400025a41500c1180d0070400e0040614050181c1140c5201240c200c0e6080300100c1c4080d040001506d112103046000e20610199040240c1d010051150ba425911901c41c281170103042c2c607102d241c0c0d031400d09003a601c4404d0312002c1c1503080465a034840030340000d42c0c80c0300400a243c0c0d070002441d042c00081e50b89020b20940c1c08082c21014003010f41030500110b10320566020701909080550340740000005400f11514415980c0300b042455101d05011b04081e00f51224404d5680c01e540084040103032918448031240d500809601d4001100205045401c10520a042c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 855182221 1250 855180971 855181007
    0x6031b020a26070c141c0b01060f0302211506040605220e13030306050108090a12020f011508010606020c01080a0b0117090d11070b0a120b0402070f05100501180c 71
    0x130009004240400000400070107907054844410103180e65540100031120040110102c4001842401e00c00c050709103c0d1401c1c1d0400611f08034461005040602044100741c0041c6070100030041c0b80300107014040300c2c842d400d9640d00d0078a410540040c04901030000c80c1b50540134000008400b211610071884010405903e91207240d062210201c410902100c034190042801d100b00010305c0c2d403044100f035126038400d0014102d1a4070555420042c2d0072100242c00441c4500000785103031000078481c01c4030030014540c003078400340d20701f1100c242594a1a40010151b4004000008050360040340c0b8070381c400408500040e000101178010303100101441c0c49094034041810821124400c0001d0840b82065140c403404541124901d0070b5580d0107090060030001d02c418020b2220203070140840b1132030480c0241020440c0ca2110000c581240c02044d030a42c0c9008845860f0b8051280900c6a2001495041030038012503040c01c9503440000034601c14100881d076104014550704e4480c58003840500420700c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 855183471 1250 855182221 855182243
    0x70f0503060a0504110301030b06030c060f0c0106090e210a05041e09090b041505061302071e06060e0c0a051605010b1201020c070b13050d150606031b020a2607 70
    0x1117074090590001d0104580c1d44a405e40803580d0b034078001440c03c41000c0001c00340b51a02d12003980b1819250490245059203640300c05001c5013629032409481010f40c8440c00030214802104641480f0714000a407102c1d005808101d9140c8030782e403240c2200c043c0c80c3c50a4100f4010000001e051400b066290f115503440d034544903100041003910811540100d00038070565002d0f06440802004032581a90020342c01340802c449042c0350b2803541c010708101c41c0a03e14180d5500341c500807000c5240c0d0124000c035445550b40005001e00700b00101c4107a0005400300d242401c1051100780601b9a207c1d020801c42450b42c0c3c0305140d01001003d400c0026400e5014000895200031410440c1c00703500801c10039041c902030098003081440c0460261034001c0c80d030310300e140c3c5003034601401d0101c0c8aa219005564103504103404513071540060045600928031540c0000b0408148003940f050320340c95120303e000315040070040c080850300f07244510142102d80b11640100f5812000b8a0101e0720413850001d000b45641 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 855184721 1250 855183471 855183491
    0x12030c0408030a230c06190b0607060b0420160606080a0f170a090e0705040b130801061418070e0a030503090f0d020d0605040302010207021c1703070f0503060a0504 72
    0x2000c0188030440001484800807611811464145d000b8280710702901c2d4003030b10009146070180009403c5140c00b0340700002d80080c008010400ca81c0c040c400c141c8920b619a5a040140d0074544100098a035051000100311003000d45050124800d030000c5020b240c006a18031801d014844e889076004103403140449641070414030f4001260149000b080e03450398031502c0e012400c2454902211424100c80c0e13500c15000f401c107032850f0f485080240c0705c0010072409210204500341601d004120301d41401d20907031103141c40d00001134255146600705a1691000b5958408140c49034403508019058417110141e40795184030007100d0700c0303003a960070b2a44241581c4001080c00300220040480300b409450f01c071010520700b414030198051000c0c000350081c0d20380d0351000100754194070076900a1320903c00540740512940005103441404460a03085803140c1140c103040102e5044d50403d540811544203045107000b03800a8035480c04c0c0c42244040c020000b0026420b039440d82c02c600301801e03000b041008a1412 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 855185971 1250 855184721 855184727
    0x1091b120b0411030c091603060f08210c03070305040311010c0209161404121a0112020108070309080f030708160906140714011d3903011b120204050312030c0408030a 73
    0x402e1503881c010925208000c1200101c219000d000d03202f64800800d4181e04180c440807448440f01c082540b950018841c18462000a10080040c14000e0380d501d901c0e1829803e124a0b403100ca80801d50500a04040c0e40c0016117504000650269505103e680d16078524401501c00d4418030803c0311020500080100e400080805440307561800f54901c400074804950665851620a01540b80c0106684612900562040c50a26802091403038049102c8010f07a56030800d81d0800a0b12895420001c01084000c80d88040f400d503000c588040419004044500050b0a41040380140341c10004c5c070044402e28004648200c0718100d6220700d1104065201c0140e450007801503100030303c000300745000400c0d840140062040c1c02085000f00406072443e61413001001e682100845c0e02180e04084240d40107a41e003849410b8072001e2030b080a0204400310b80d0700070301c100f50000421508520610081c0601d440015600003000b004e03141c000d981c2e880b600031403502030103035034000c0529100000302c02c014158 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 855187221 1250 855185971 855186001
    0xc030c0203161e060c0519140f0a0605090a0f26070f0605090d1413081b0f0114090d081209011509060e0601080a0e01091b120b0411030c09 61
    0x3c0c40702c0101a500e8039040c0450721403100c20f2024040b0781c843c6e6900100e041001c03004009451044030030003840801c200301039043c40f101c80b1200380c25410a594403000e004050042c1640031512102404404c00c440d5200d080300444108007808147d40d004550b4100102d4500c06201403070302a2403552075a00c039142800c4c0303000c50102c1c200da842c0e06050104522040000b0a00200e0015455a0111001c44030b500d280c0c0d9082940c0700710b08020906000180c10318140100414148001552050b07a400a810711900041c515405810005180c0c80742100400d08020b8855810080752209200034007401d0035121800740c541c800341c00d1031043c400e110103080c056000c409a42c0c030b0701503568100d6617600f004a01300c814500c00c040d80c442c0e404000440943c801c0c010168003254100d00004c2d0032540051003030844111b500100e81a8040042960200700000500401005444c4010301031581642e00c519810601900040c007010100112480b2950305202c071010b0900041d00e64800c40c5800f13203030044245 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 855188471 1250 855187221 855187259
    0xd0501050a06170a1802120d081b040e0903070b010f03050706021506091b0d0209040f0b01020c130608060403080402090f0702071221020d0216060c030c020316 70
    0x240c0201d0005203107024031112990994a1142203c1030760341c220407007002e440503e000c940901c1882e00300308010f903940e170140711352444440002e1514401c801d02c058103034800035108102e4480c01440e603810107181c0804442c2580c41c1c4000d50a003603150010f03120b25601481030010500e5500340004500d8003c08201e0f90200c3e4051412a155a0341e41d00040ea22207000981c032021083c0d035940003c0c01d60408001258002d224480441c862220815842c81c264220743c100c41041a00001d0303070801c0d0301e02400742c844e038109446003c01240d510a0000303503645603d401840e00070200c0c102e8007200300c00e903940418014560081500c4052605240c01005d10008580c228410b680b6440403c0c0d2440c0d5400c40980b0441035a0014005a81002501d03241040104801c964202c10480c9480107100c280300c03048003104540d00100002c000320f400290503e107a500705100f01b1283c00600b000529070102d500800e45406040ca00443d51050001c6400d00000740402d4010003065007000a250032000c81c060500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 855189721 1250 855188471 855188479
    0xe1501091b031103060603060f093303062206020a09051005031b0d02071e02101409150720011103070c031203060509010807030b010f0e13050f030d050105 68
    0xe00a491002c1d000c031803e65121400d80402800010218101600115040403008000548041251000602031003040701c1c04145101c503c01c0d031568001355102000325201602d1031000d00c252141012a5a8007070052010788010403400344060800404594145101d8001a0644d9120032120020307000c1c1046d03100701401108040140f0f0388051044055038015011091114160065085c282800e50031803003c2d13081440d401c2041e140001c80701e81544101c010300100041c81001c542c010400700f916040c03c000d06026204515100c0782044504030354022004a8400c1c041c41802281c100450003160402000c40381480190100010010300f080d803013400c00da95801c041d58140c4515500c07401546801850014035410902c0001d607140c2c565400080f01d0700c0c0000300c242da2140040e21408007079100c00c03500c0d084020140300380000d500250707016090780c40390201517619014011079501f0300109100005060a00780c1800c1001c180a614003d030f140340c048945400c10903040c1030081c8020300c20707584a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 855190971 1250 855189721 855189761
    0xd0506040c0b0f09010c08040906300503030f1005180f060f0f010813230c0105040608040201050d060b03270a02011b110301020d02220302090a0e150109 67
    0x80b40104403c9899240424a185080c15402801581c107428140c1045542d01d0043c04041800c030b5861107000c0c000c1c1000c203140d400c0f400342e06030062102c41c01c01c0c619451f0040407289075000b10380000100c075041441090070a20603940e410400511a011b500501e50102c0030315000b88050380d101d6042d5000d20107012529016440c5c01f01004100003c4100454020b200d0840c004015801540501d41c045a0311800601000581c0e68440f844150316a507000c111911a040000c081010805200725003020309049107002d06241002e4100140104024100701c0c00249002e83d490446c1c11450050940c00c003429140d08001402c51003015081003c10b40810800c503124003e0030000451080803a01a145c503402050541d01c001c0344516050019100c41c5007222003030305291800d2006000b81da151510051711641c00f40d400000c0c0305007074202d10300c0c3c040c2c0b052401c2c000360b40d96922180c3c00920a460001d03248104486440c2001c4a048085d0a0011050000540c03003101d600209131000054440050f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 855192221 1250 855190971 855190979
    0x90c05030108010b0d0203060106030f090f2a0b03040213021b2518050405030c030a0905010e0402190f0c0c030b0129160c0e1302041d0a200d0506040c 66
    0x50345c41302c002006549680031200401030b45010f0fa00800b0070f9003029034040b49900990701d4500080e21008030403504d03a4528600203006290711065485090200e40540e0309461410400900e94000940041d12079051061505a007038087e43c1114143c0c8030105150002d00044803881e0b0b02e0382d0940f41a22078464140640d002128020b05402061301d01c186546410b05c600d10031548001c020080040390315200c00c00032281140b0f000c0000e00066120b540e1ba004503103051400040100d402c6004040c052401403020b0b824003050744629030034410141c036160480d80c3ea01d00c003c465100d0060005006031304807400200c14010001004c0e130684010001c06036040e4440041100b000f007400c802404c1c40d05003805042d000364036400844402d580500881032a0035140c58000d000d50303000381c131201e4403001d44041540c21401c050207060fa41204103d140220100c1c980c21280d2a00383ca03130001806105e040ba588400c5d6654103081c603001079805002001258010310f0200e5981005aa065890f0000350798002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 855193471 1250 855192221 855192229
    0x7020f0d200310090510050405120c0d0323040b101d040b0c1303080f040b0301180b0103020301080d0305130f1202430504050c040911032707090c05030108010b 70
    0x40c184550140c020400200313490b1b050402401c2c064422200d90048403026003180510002070400100c0f02c00243c840b000600e98003808a811580b14100070120b00320382e580f0780d03444d950543c580c03081d0071505002081d82c0704c202d00d961031402c0b41c00caa036408080d6601c601c10700f46859000e80c4a148200104c0381d41e80c84030604089240034486403240d080e01005c01c02d000107441c001c01341c0729002c0e540c0c00310303820a40c81e030441c1111900260825081c106065110403038030043c034058260004000e003021469541081c000b1b64a800510314003000345a1580040b40151800c19281c0051075081134000074491360711f03c0c194441d200407000700c000520442c2c0780f02103802c0f078000801c540041d524250039058822030000071961a4085500c1c0381c0c99641c0303000003615031101e0148902c1403107d0007007181d54a007800c0309172007180e03107034004422001070620400c4807001e218050215607410740081c1494201c585d40400c1d00c4c10a16030000100d4038201141022401d412001450598003110021304c003504580c8180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 855194721 1250 855193471 855193481
    0x13030b1503120714070303210507050d020c031b1e16090b0607061a03100203010806060d02060d06030b0f1302150a020f0a050a0b100b07020f0d200310 66
    0x21641c5600400300c00044004020010441a03101e41c410240035101c0c5800705040200a510640c0491120005600030f2007003800c1800041e0200241004903092a0304d00401c14061a0300c9075100da07a0018401004070713410803d40c0c100c050801e40e90301b0b85284002c7c16548500c014440030709081c403901c98100d4101800726041c02e44550108030180498070f0848100e0240c141100178076009070007008200301091460007040f0980c0a02405c0520030a0104c05261034070342058a2451003030303c1400140003000c17001c0341c41d40c1c00190032201e05d035040d001030000031841e120301d040c84000e251030b04000004001044000c0c500c02c10341d0001d000d000e503070785002030f408442084400075030102000440b000c0072050a006032070001103c2c030407904114102e81c500c038581405020183d619501400e00c1030108800003011940c0601c200c02e41d80b00e007520b030000e01d000341c0c003a00400900ca8190702c110484903071183c0040018281d00054024204410345420f8031100c4081c00019010703001d96911000300c0040750141d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 855195971 1250 855194721 855194761
    0xd1410050601020a0b041707021f180e041101030221010f0902191d03100f0501140d08070303020f1602040c020c0d110a080114090142050613030b 64
    0x1703d02c481e55440e681c4101ca10b001103510600d000c01400b002d0056120090301e2903c0e0a000103241d103003035003890005001c40c000c12201c030354500921030050003102c006100c400d1704554000ca228891032140340c0160040d008030481c43c20805072041c22250086040a5a541219040306a0078042074940b09210141e1141d080c03821212000200015a903038071903605000d00002001c0c4100d400001000045d040c10804006c16031400d481b4140d41c0103120070b500c200790051650380c807016007910788080410810303c0155070182c607403a03000c203c0c20309040c0a0b4040b200001080c52902d5912004481444401c01c07603800f00340d0040f0f1030205046e015a0001801c0b013807a80c00104902c1c211520350703981c800d4942c0712207205608482040c0c000034130410300b401104044a48078074100134503e40081001e0031101d04407000c40c000000d00b04150301302e4411941c40842d4940384042545c902c41d904101e8040700f80f0f5640066049100020500b046c42c41000f64001078038402c40f402042070710381c03403040e40311166a268 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 855197221 1250 855195971 855195983
    0x22b1a0a05010f0b0d0e06100905010b040f17030903070f06030507080c090d0507080709091a01030b0a050411090a023a0203040c0b0309030a0905040c020c0108060d1410050601020a 79
    0x70601c40481c210020700700d0751171000f4010500400261a080c100442951a900105080e04092000f50311902915014240c1c07908068149442c1010394400e4112600c50743c0045140c141d900701d03068409004480001101400b00e9214503554a507500100c40c092040100091800c0003046100f032055000c2801441d40701c7d581400d2850740c01c00c12030385454899003200c65119140b0000341c0700e035080c806400100040d50700000c040c105810029072103240a50341c4406000310000510000c0d80c0240500c1c0c0043c814080013407107540b0740c44c003000800c080c0075030540d100c0015810002ca921458006050a04c804136000c841e040110f01800d50100c1c3c04403041d205080507600000f07100c0c0c4140c0c040c40d03110740180701420f65180ea5086900e4185e000f07850401c8036410014401104a401c908070200600054804210448089800a40310307211409140e0400c10418042003080c1e60b0318141400041c0c00080180403101da071a9925510002842481c151904001c00110765600101c2c660080c141c000d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 855198471 1250 855197221 855197249
    0x3030e010e01030b1f022b09060f0c031209060f15150519031803030603121b0f0c15030504021c050a06050a06090f05090705041107022b1a0a0501 64
    0x100080e00312000b160351754001c40c42500525a40d2204045940c01108010030044d00b007039032400c10082c41940070b03400002c00d1000a0182400040d0b120501a44117505803410f500300c5100a64140c015000c0740c04046c150a040c50091000c01c0c030355501c42104441480140e00090b80d07600440c00400c00c450710708001042c010710800002141100100c601d8002a280024812694500311112514512810380010390340e003c0a104104e910111001c03d070384641442000311245c2c080d080030410008500912540c24114800104912281c814014040740c002000b04c600102c03000600603c0100c6069200d07241c040140412861030080c400b4885d0340000c0640040350a584808000e010701400f80038050340d56400028203529148100046d8071242000413171181802a44146807113031039040b10744101d1030003418901d44007010782250001c80d4151414446d4646184007064001c031b801004400f00c401115115007001040407598500d03a54550660500fa115204071008940007401980f440d11900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 855199721 1250 855198471 855198499
    0x506031b09040501140103150c092303070f06050705010b1516050705090703020712020610050f060f0304060903020607021f0e24060f030309030319090f03030e010e01030b 75
    0x6103100c00c0c1c0c014083d90010407254000010310b42120800d074015990341400e108826000d11450240c00d070f0809292810449103800c00541040000203040180c141401d14010036501d51002e204060052115071505074000d60313030342c001070100e5012403000c88a5502c0d080003010300e807a06040c012446485100100d082a0203141b00c061641c0c10b507041a1020f200b607100028081d95070309000c0d40308010550307000d0703200c980d00d240445800303800c07090103070564114004001070074040d40400340880e50103c58400a1100d0f030004140b207842224100b444031b85c0c0020810040c0a000d40144403110720950031100300c0d03034460348226260000007510030540540d160b02c150840c1215088000c4100c151001c0d1003080102c1a00d46540d5404880b80600f00e01d498070401c291072034020001e0041e110250061450001847e0019031288549070550384101103085207441c400344910302041c0a00484a80c0c00041c64407820040c28206400e01d100380069001c06d007034117070742d44a07004001c0d081c40080c0140c0e02007109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 855200971 1250 855199721 855199729
    0x110105030603030409020a0c030e0f030a030f0509060408010632130f05040501050610020d0822050d0c02040606090803090f01110a0f0203101103010b0d020415120506031b 75
    0x4041d004036030610003444003040346000752004094403111512070320101d9205250241c00c0490f52084944620600340b0487c1e45620007269600d0813551626100001d1401d07031400f660b07a401984030346500075002081c041101581540500c1c10741e81d101c961401004441582003c4081c0c80d10801181100352076084015070070581550035008a030f506010903015902d151400c2141d02c112070a403202c0e0345400502641d81072040c00d44990304041d1001c0c2a4501c0e806a0103846000042d108550140450341d46170704030071058a000040c2e0354010207503400e02aa802c4010a00703200c0c210140d11581c500500012842c0c05914044122010030024508188580c0100404148004401030500181c0c3d06080000c24041c014903513a54030403071121040301030900615281142450458840c10f14205143c982205c03500242c90440e106400340b166200c440d010000068040c560001400b10001840076202c9034010b102c203c10114180745c100400d940c0c0b6000c1682c0d072100d03000c50303106250903181c0580305420 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 855202221 1250 855200971 855200977
    0x307080f071403011e2c03121f0602100b0609010905010c030309140106030501050604151a070818040b031b060a0912030c12030903020607123b0a110105 67
    0xd00140000745c060002000c4480243c141610202441c0c2c0d01c030481c1c54800030402841c02c00030401094001180c680b241110b550748540040050701c4585140054084040740c40319141a080b1320305100009030f51450060758490f4030001c600341340c505001081e61a41072081c1a98010f190513920702c05a0751901e4015250040c50300c0050b4101511a88110702103a01022142007507407004c03000141c1f0034610708106007141d40c041c0203079215a040811380c80d004c04442d44282c050351001d950742e803000040b503c25600035201d00c120041220001041d0b515248400c07070042d0000540c10346091021201e40d4042540310b01c5400a440c1009543c2074090400d400c0c608054a10300f9820b080001405454850213030807519600c1d41140020504e0040030108042c9900c9890504d00780d050a001c9401565030283d15a40018004010400040c20203291205030f0b40222464080c00e88007a4007030704d000981d003040181c0c4030350201142c0e80c259900201c0e42500040404945401103810440b420301c1e6070046a50364 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 855203471 1250 855202221 855202259
    0x71401080f1905090d090801050408071103030c0a0803011d090d0e0f0a120c0b04030503030f042301050402010f1805060306010302070b011d1e13030306150e0307080f07 74
    0x1e00642e0101e400401184222405080c0380d40003004041400c51008100724001d41148165904190038440081c603400183d5103000d601c400d0004070712006501091560091560031205403041c80d01c1c42e400d00880100450503100503201040b5003540c000311b030901098003035460304850703803003500071140e11481407069500903038008040c0201090071900251034546c0540044400824007847c0c002005085042040140030302c10040c0e080c0b5145448081e180c1c0801400019043e041c1000201002502c01c7c05220311038250500140455010b10300600a0804440c2240483c6c0000d0600b42c04034041c0090110711440c3c144002d65540c2800140801038101802c003605043d000c0c4034031000900e21014107400b03041c8041d07010a440c00071800f5002c03000c4025100b8503034110b03420801085401c40d0100c0703590100704003500f2400320a145c0340c110300405540d40280310b08041004444076142e4420081008114100c00321032401c0d441d016015102c0403900008a4668271a401c10044000da80544507110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 855204721 1250 855203471 855203491
    0xa052202130906110a050409050601021f0b0a0e040b070f14040504270305120709031106090d05062805060f091315050a0c020c0307050f1203040314071401080f 70
    0x70070b5521160702075034101c5881741000c600049814019995244280ea6024600744000e2001107200c207031801c3c0101e41d14601500c8942c903a162400076803900c803070240040c0034045003819240303010b04003428018001d4403c0300008180d244100740b010f00c5582c62005c80590052100c2c40c05140c6010000180104084c889030700d01c0b450191010004007040c00031149010f030f01d6803a0340e111007224090f0f240f0401400c503000e000c1c040205101160000e4034803400d03000261070321075a5019034000200340703448001004040e44a03900401c103248111640092a20700c1760180c6001e001000b444000955104032038a80d0801525602a811841c00344065504080d0022000e1141d40107904c8544241640341000706086464505114440c1418880c5003090507070ba00c09014004030241c00285c0780c0015200f014400d580d00f81d020074042e6580b003254455050510116540c80f0380c0da240401110710000c004251500800100203540001c240240b41c2ca818141c0d29008580e0b1030a14068148101600078090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 855205971 1250 855204721 855204731
    0x50a050f18010e0307060617120417010b0d030906030c140702280806010f050d110f011803050105011707062f01090c0801050106021f0b03150a052202130906 69
    0x2c07486042c0005c10455000d00008228142480d03280809041d10b1040711140e948008591040068a00c0030380b019140c003800100100d215404c2114094071041d0407903540f280d1801440740801d40c000710484100c1d40c0c0340e01e0500185030088000c0c0c4d480300c50982c4480400104018480c010f2501c42040a0503213029031101c1d0340e040590036030107024200760308110301d190300820041c041449100b0b5400002c01044031f110081206a03075451580441d5084818001c00002c0d6100245038010780e801c10368000c01800c0059241c1e40c90500f940039050038815845101400f8407016079011021a4408c03c1d83d00f10f440782c084041419210040e881c00840751a100d45040c9100c0e05080d050030701a208903140184201146075050400c82c0f4215001a44801c00350741c0180c0d0801c04400c9031038003445200406c2040084c4e04c81d40c40300864104040e906613041d42003e0f0008001c40c2620700e520003400381d43c1d00c041b9801d8241c601da040300310241e20400301944c0401d03085060094182d1641100700342030b11504000c61 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 855207221 1250 855205971 855205991
    0xa1e1a04020a090f032402030403170c1b071707030b04031809020f030609070504060f05070602120903030a0e0a030c020d0c05090c0703020610031205180307090b010201050a050f1801 80
    0x40d400d421500220780f46e401900500544040d41d01c01c9106400300003000f1499418140d802130030100c048080b20350340825036400500c00c4a068801d070351407410152484015400c171032820b80d0700c445040c0204400c40c1c00c50704945109070400120041034950011510b95a0340fa551020340c0c1807134644900c0e00c0170319a204804900e00071540081c0541c10b031204000b5469050010030800d034014020040010418240401c0204660201721400d04254504096980d01120f00f4014040d118020584480b041c2d030344180110140c00000035403217207216000400400d0b015860300741d15240710000c0580000c0400c581c01025180007611703001450b00c50f0030740405095540010402c4804119005e11500d203004c00c012042c1a018400154094183c01201c0b00c603a065070340b1288109117026508080080114a485911040d14101d0b0382c0b180f8020101c3c1c11076503994282c400901190000f15005500708000f00b00c10120500696004070300c0090700110654401c20b070042c060140d011600301c150340360200701d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 855208471 1250 855207221 855207239
    0x7051b07030c1401020d0e15071703070915031103010b030a0e013e0f0a0504030f05101b020601061101020405060d050618040317040c05090a1e1a04020a09 68
    0x1400503d207101510852030049800a810218800700074001d12810005884265642065000d1040e45150480342c03a00c4850400c050040c00400c03400000f4240001441803907a08400b850046440966554030346843d19041141520b11411110004e8441400103020f4560040055030b400301c4007100c00100450840d2559094030654926509103015103c41c140060019a0b542c00c44000510224035040c000140104440e108001521407207150220311210510f01c00c600300c800454010902c81c40360245800c00c01c0e11585401c6144c0085494031103180003407070301100401c0612031142c01401c4180e29142d0180c07008113213030710a00e456541c2000080703444e6640d1000b80030420743c1c58100145500e401000e01904005007543c01c0f4070600300742d0070400082c0e03224544440c07842c3c0741403442d1801d4aa510b00415441300c9034001c5603101d50401c0410030801802e60145164a0100090614072140009540d04030b8401c8030207046030500c4001e643c24a42810b4000707105046072442c1c008101d60340d40c2810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 855209721 1250 855208471 855208493
    0xc0611060a090807080d0b0f0105090a0e0c04050307080c010219020108060d02030102040b1602040612081e16031101050f091515030718150e0123190e010b0307051b0703 74
    0x6c0600582c0d904680d01032402c08032451404440b0a0811a29040d80708002603461405441020002c2e00210b00194001d10901e00b610024440a412100c440d0340315403031640c0705c1452400c5140188151459682d43e80b00713800300d40000c0d98041c0c65140554031400c0500108580c424030583c0c05640800c4002554456000207103051030464002c8403401c0502c2c41000b094032015407001d503184642070300040208014000b03e40b04480b0b143d1194034404050031070743c559401030a44880c580b409940320a0203064119080030103e59840008000c95a5104c4103012074040c20b0b03900e08803583c00550f00701043c0b00c4402d41e0503082140b11420910407903c0000181c03519032560400010f044500c0d02c003018448842c0142c0400d283d40c0141d0310449420203407594803080d014801e042d4080300c0394401c0c1c0e10703242909607880d064040107014049070340d0074100c0c00040c0d80c6481c400c0091580172400001106060181070b24026406540c44c113240c04614007200040080f0280c80d4a441c9c01041c4000001500611035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 855210971 1250 855209721 855209737
    0x210150527130203120304210c020406030825050c011101021201080a020117070c030c080d092006030609060105211e0a09030c2009130c0611060a09080708 68
    0x240b080707001007441418101001d070f44c4c0c0d01040040500074007002503c852024500c164044101141041000c003048942d106c842d10081c3d04245000030100520003170700001c0411000c0d009a0507201c58010800d042444c20002c0090308940041128140340c0d032240b0440c0d82070000340740015007003d201207800071400400f0382c80203660f41c2c001421882113507000080e80f541407000400206d01072a1000c8003405c07150140300700070100310362181da0104005076001540c10341068242e0030010000d00380f80911501452080120381044c0e164000000c034600303a02240e1040501500008070394641600549542d0010320480b51b5114404500000d40e0040d0311110748180e5803412400b82925801d4000d044611020303042c5e40900c0c2c100f85417100481e0f0040507018109512000100c0382c401c005035221b02190340111082d62103034010080c05a20340c03125075840b4410b4000c481d0010300300d40d1484155010016500c50482ca40c100d60001041d2140da90300840705640100300482c0351484503600c1c07080c640c0c44844 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 855212221 1250 855210971 855210991
    0x70c0213061a0313020d0c170a200f1311070b190903171b160c06080f0f100302090903070c0e0c071401020d0603050d0210150527 57
    0x908102e0b1a205441040358208042c40700c52440c102412440721125000c0000390183c42410042c404100d031011450004114400c0810340c1c0111217400c040d11103003050000d48000c0707d030076050a5402070348a680c0030300e83e000a03c0381388050551414090445126000008410b0b942c1c69040701030a0908010103846224541903125071410807030b0500f00b080f1081001109915004540000940114444400c4e41c26003100814039075410943d800319160780b03a600224000d000c030b8881083d8406003840702c41184100342601d80d00d522044101d5580034101c481c0620010b91340049101c01500102241c3c04c6401c0c18401c0300070540f01e40100f02d9031101603590141c1c40e1b20000c2c840040c06068040c07075000c1c1041c1c1009402c9420300090000d080c1c06078601c00b4140245045881c4e24064003503049a1014004400902143c1c0c0d403803d10a0300c5041140b8030f0710141c05a40540c40c10320055101d28040e001c803807820304150508000a00600040420b5000b60711034060f001c00c00160010591188105002d41d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 855213471 1250 855212221 855212231
    0xa0e070801061101050103111909240911032419031a0c09010f030b0901090603050d0807140c240a06140a030b040515040804050423040308070c0213 65
    0x1c4001040b4200e500c0c2c03100c8461745480e0040c40050000c140850001e0001c0382d02c1c0d40d410b8420300e0050382000d841d0b4860180d2038644044001321011a030340d148081c20008502c80e1005980c2d03201031054030203924a0b05000724081000489000c0c241c40b4200c0c1e00710302c02c024071000d8184440810702d225039010380c82d95101d036019010010440b90845203848042410326890041c2000120000d1602175104d280d41403202c40c0d0000450103100340e02000103254002c094580c1d6580d1000c201d00242001c1c00141d9090107001041e0a0705401025000e0149a103036440545e200300801c05051076811916000c2c0d024000c10441c184040300c079a0410f444e100c00c0d118801d40c1810705006010072114564400040c4100503035280320540d032820811030403a82c102440803107666540c03421500b0a8240d0140f08a03001e2900180010b000c10900a4416580c040d1002c0004601c07079000a03900070095014a01040c03c0c0d00001030010b40318040c2c07240c0210751400e00310790709502a40026004028220f01c1041c40c1d544e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 855214721 1250 855213471 855213479
    0x150203010510050c0615180a0207030e10080423030304050c0f0102010b130905150403050a02010c0903050a030e220b040b040b0913081207031a041104060305060a0e070801 75
    0x30682042c203005038204580390048400b1820345a4170001d020b005004403066603288103441d0405003050455201c1a2a5142c3c03402240d80802500310340070039000142200c407a10b402c0d08280a03d013040b103060303441d0300b04142d40d40d036548684409180c80d08035000503122102d00c00c0b4442000030b140103d214401070b266161001e41070120301c011003840541103a040c07605041c1e05454460310b02d010440e801c00c001c07a07415900e0401030f281902500034230104011003c104000d056100016000a00444d402800403198002080b074090000d4000500240c20041c58100000e005000300304c400345000c0c040c1c01070341940034600c0b1011a07101411001440e200c08a41406203414840c1020003201120100003c012400208021520003441c0240413a01104002d040c8205d4200386e5410302901e038400c01c007619002c01c008000d0110034038400030780c4095404048443ca02405080c40e00d9110002c81c1d41098503148048001d080054001d54005c00002e0b40400d20348030035001c1c80d08c0799200d83c55280340340d450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 855215827 1106 855214721 855214729
    0x20312090a050d0206130f0f050409030e010f18171e0d1409041a0111122a01060b03090607021c08040318180c08010302031c05071502030105 62
    0x30240001e90159071111070800e5440d41d8200ca01c803149c0e104184025036018040045c04110302070103009065214945080a610b2146417610590003d03050018481907150041400040686520b0100c07240411250f01190045080005228800d0b04100c0d2a0541d41c186042000030441c44034400b81090000c4c1c500c040402001041007c00c6000b00303d20a000b050122404590104c0306010311400c003240301d09502c007a81500c285031a00c030032584103401d5810444440310001c1140d060b0207886c1c01740300c0d00d000303041c01390301d0542c0c0d038104105c08034a009001000c0c80708540c44a41e1103011007071594021b002c0b0143d079040403078242d20b4034076050318000c2a00030380070200da000c100c00142c1030703650302100b100c1103003110410400b001d0005070889000109001c080c0d00b55020b81400045410b01a0100c646c820651600d14248507882e6140d8012072200c4215841c7c00c0d40100041c021850 = true := by decide +kernel

theorem cover : BRFrame.Cov 855035971 855215827 := by
  have h0 := BRFrame.cov_init 855035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 855035971 ≤ n) (h2 : n < 855215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
