-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2685
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:59.445851+00:00
-- url     : https://prove2.me/submissions/207a868b-66b2-42be-b53d-ad3f1763578f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 482733812 ≤ n < 482913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 482735062 1250 482733812 482733833
    0xc1603020c03010623030d050306100302040e040b06490b133305091501080601090b030109050705010c051612031b020f1005040b030f06030c1206010b07 67
    0x6002c0e00801c051517407217415424030b41050380c1251207211303400c94903400c81c24045024540c4c007880d40c03130310f51541d21542d050049501449481404040c1d09010101300c1110003903a240c05103000f004640000c1c101181006145a0380080d101c0a80000340d41e0503041410002d10155041d990030800c2e5501c3d00c003807109480c003202d01c840003418a0810810043d110030500d5404a80c00e002c0c0c07020500d001c142101d25085042d6442141c3d485804c0c03052080c42e41031207030b0003030b50340004001c06440708002d00c004100710b100d1080e08410010741000005110000a5110781107290f8070803402448840261f80750b10340c80b20514094241040094030070403003401020004902c0c0c1811001c0340c0c444081e42c0e0711901c1e681c000704000c21000280709079682c0d00d0342d01400407001c00c56500101011590b2117100e0400201603001d90101d4103100c01408001010007400000d103201c0c41314511180740e5031070030b041050308003040d001c4541c0c4100000251020703048000215641590404040c107661500541400341101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 482736312 1250 482735062 482735083
    0x1e0a020109141605030a15150909060b0102190c0e100f03030504150c03052a0307030509030d090308030a180611070b0105040b0d0303091a07020d11060c160302 70
    0xe001003202d1010700341c0004642852065410b0031100ba0b41d1070710109034440d070140c1c81c040c0007200282200900c4103016880308014a213030f100d9200c40705950310300e0704080e103104d400140c0ba0070780c1e502400c00b04ad58040c845108015585c0702145049903142e80c5020200b2031500a116000070b100b4006803150440250030006070021210b1300070515580e00c2c0c000c026038401d00507604509800301c5076001c0c0074000d00c416140c41d03a058903014140550095007c19014030320462404c50070622031030511a010a200421145000e56940d07a0346420a1741810700e07044000e0461010002626800c202007800401580e8000c4000180450003490041c0e0f40c003221080f4030400f07803d141c504080050b0a00030040180585c600c900321800503aa642c00402c412101002003c1e07401c00c01c92230300c0d000040cac400e60200700c003603205880540c2d01580f45c1c042415500c0f0b0483d03201001d40d1000c050013421a400c00181825060544010308191818000f880100e01070342202c4a00e0140415a003001c060080c170050710720 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 482737562 1250 482736312 482736323
    0xd1407022b021b0406091104090609050609010504020a030902131d0c100c0507050307170607030921142b0903020a110111010c03150518070c021f03061a1e0a020109 72
    0xb6025947c002c0c500c550b1182c0324000b035940c90000c00040d4041c090155500c903040c0109129000ea02c0c0600b030101944c01820039004040c3e4075030a4200581e91010700715000100000001010038170400d11840d0300d8590580d507510340d402200305020a90314240c2e0b201c2c107101c0c01d04c0c08420000c150315140d841d00c4c005400883d450b01400c800892280800105641c44800c04000c94506468041c015012a1303184c8038090301d203000700103201c000b00c0204442c08422400520b0546034010300b40a074101f558101c40380e20300707401032500c5001001c840c41020502507100c0304c400030858440d0f141d40c0690340795101c1a0003885d045064010b070781d55030701400b00c00811040c040c00070301c100b1040300c0340240200354845180a10b0103c400780401c240c10324006481d0300d140d83c030402066a803682e04003620141c0040c203003268025000030322141000c42c40e0803d9040e110480e1400300b02c9038244840c1c0021228241d00141d400c200c20f21030201004000e00031b4140103a0905406030f80d4030254503040b40500b01c0e00302e02410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 482738812 1250 482737562 482737571
    0x100b061b10020d0f0c08090607051803010f0905070b0a0c060b220606020d0e21030c240106080f1303020f160f060201020f0d020d1407022b021b040609 66
    0x43d43e003400d4004c42a411000300f0b0400070344803803c1050b01c10300d0080c1e803242a181e0241d00029012801407009040388520510400c50400c2d40600081c20740e50059030350740b0810b45030030901e420003030b04200f848040c056558882d4141401c1400003000c0103407055020f00700c04d84942c42c910702e40d140c441400440b100062001f01c0310580410040c0c01914a911508006105503001440c55521801c01780e0303001031000b0000100801902c0311020075090403808281140010440243c04550402100d0f00c00f01100721804000d45864210510544059201a040c4030200081107210201d849181c3e80c800e400d45440c1611140c1800c2c00c81c83c001d0307c80c00e242c601c0d00c9407241050044084007141000c540c41c8452811030651249400ca090340140340041d04048002d200301c400341c058a8020700b009004500c40098401900d46403007001d104141c4403040980c0060b085900c00c202c08201c11654000e603e03825290585134044001e64805d4802d0a070030010103281e00c6400c8a503550b400810003494000030501 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 482740062 1250 482738812 482738827
    0x1030b0a0b030402180601170411060c07031407060c0206160b0a0e10020f1209100504060f0b0d05060a0c0c050d0f17060a06050705010906060e0603100b061b1002 71
    0x10010380c0156004e0b880355401034640b40303100c10031482c007030320564040e91040014084980c3c04072900e2400703081103504080a480001140c0c0703501018180f1030310090020028285103081c07881e07400b004100250080c0c2c00100c01480034940042c10303040d000b541038070825030701e01d1411080031402c42907400c0101850070341010b1000d00351880d00503241400b804405c0e22920000c1d9152401207124002c0700c40340a00e801d0005104510328003c1c404c4e03000008000b980da0b02c0e103084004100711002250b0840d4115544e81b1281e058040300d1041d40910700040d10004a10341254880c1c65a8940080c508104d46807111560b403a020302c01d0003194809980b201c205c502a4400040181009030042c29001c0013030020301205580c9860001c03042c0c0a00009009114003d080010441e002d9222020981d815900d40d1032080000308903101b0030004001280404884d07051041c205814007802080180015082c40a80e844982d10803040b15042d061000c0b440c0000800e09607503a0802c1072408001e00164400324000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 482741312 1250 482740062 482740079
    0x81b0913060602010f1a1903080304080409050f0417030c09060c0a03081f14120f060103030210020705100b0a08160609170a14010b280605041503090201030b0a 70
    0x14042e12103e4000b40034504498100b101200d1424144a1031130103070407050a89400d0402c280324425101800c2c00580a449480d00c4030550300c140c40031620817000042c20042034501d4032503030f03400c611303051801c68044c1065103940e0b80c60b02d40d41c500e912001c0c0000000c01c1e942c0159008031348401c0c00180095481c2d4070200300454513100a1407054002c98001e50010748200d88280c546140154842101c000031810045400040d2a135600d800303800c59501441600c100108001c200d00740c09080340108030560461500178141680d0380c0344040510300500c980c40c00202d02042011011400843c00035000b00317410006a40c10a00d0745c0304090328040c00e00d4003003005411203401000e40d019031f16050981035440301c1d80f04405030030b04290314040e080b225402c0000382c100100d00071a01c0c0540d00200d0403009035400225908500401c81159107143c0300009414101118103000401c880e00f461802e00d880c25000a0300340030080300c24010150746450600031a8040d500035400c803000613043d035103100d4540303041303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 482742562 1250 482741312 482741321
    0x1206050a0b0d050c0313061a0406030524070c0201110a0609081806040b0d0f110406090302010e0306010501020c0907020709050c18090103030e0d06090b0c0702010f0906081b0913 78
    0x610103c1c02c0c0b07000501d103401c4c1c0b40210b901510030b00300180c0055200e91240130040421100b070390051800509031446a40e158040c0c0f2000c2c1d4040c3c2c01030111380042c608088041220443c40d20380703c0c1c1e9144c3c10805d203142c0200034041525020308001030300351904a0b00d6414005a20802003400b45098540d9050003240b2000d4800802c01b4550789000c0c210581c10007007680114418240a00b40400c1903425980d0190000084641a0600810b10150a100c8069140c10030b402c54000201c1d042410030556078070001c60708d00200d00341d020b040103505101c0000c1d203c10b1030b4503081d4000c4071180c001c1100e51b442004103800a182c0040104a941030481e00400f6540c0108030301404156458586e03085440e050f000c49040360f6141d1103035020000c00b0400d000c05210f803c0342c16240d20b9a40c0d1283d00102c2e920030700080c4200c01e0702c4840c50f41d50fa854030014244080e85000181007141c02c080502c011500002034580140c1da02400070080300030b00441840c14880c116200b5040000a1a841c14001043c0c02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 482743812 1250 482742562 482742577
    0x30c050d062009090f04230a0c080d090e0105060409090f050d020705130e060a0e0c0306090d08180303060103090c03021009060f11062e031a010f0b07031206050a0b 72
    0x184244151264504000c4c01101900c01425140a034003088600c0003002015501f11480c1e103041e00d41103003036a1545400c003d00d0341e10160b51500880b0410400740e81c00303c0c3c944003922500c50299125410000400c2c414051030007800c900c11743d40d002c3c80060100090113603500d298488211041c80c5980310009480710994868980030301e0079405050000084c07070103104c8225031803100504259035928601e10241009144c514040c3c0a49000741c0450344003070045510031a1414010306a81c8820140145018002007620102038400341a0022042c0d022080341c0e001002440c0109060303489041510500d44143c1c8000d6210301c010441041441d005890391040703030300e02c2e00c8a141c514402882a181260f1040104005800960000d01d52401380c4080c4c41a1500035241c0c2e00e0500b007041c10700781c0f40718040c0c0c2069481841c0c00d955644070302040c00b0018090b151100e40100c08510300911080940901c02d0003c1c28081c640d001c07050104000e0340b020006010050030a142c4641e99000002180c1c007460 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 482745062 1250 482743812 482743819
    0x2030703170a03051302010f0c140d02010203010e10031203090809040c030504060f05060d0b0415020301260d050a080a0e07170601090c02060601301a0406030c050d062009 75
    0xa00c41d800103805c03401c1d0346070180c42c5c003070980955a900b110340076003840003240c040c8007010001d4105071007000172a0020086400050f81d80d41000c1d5240020b82d0001d1914044012040f01800042c00c10f504442d0b25000c01d003804601c29040e49080d00c0b2a01410004a0700145401001e16580340e054000398016401204201700b108440e80890b4259107003140e006400618400d9500001402410351070741c01402001c038006c0741c000d80d41c0d9a80c00d0740e00c00c0c2c0c018002d0b889a5454102c05e43c0d03000d0583c0381c50580d140c0050030680000503000d0011f000741c42200050180300360005100c108243c104d018980e201500f5601e40903101e01201e1080203007181081e4451082c9000450a4801d511400f0102c2110341c00034201ca6881c0401101c0b40d80c151151000100d1190b0510700c0b08100b08038084030040d540b40380c00b05103080d0803a043d00a040d0b80c0b00c0c0380781c400c07400e04c2c10800205000581c004151041501d60030303004056030602d4000303130080d10b6440c0c43c101d03210064030107001c1550f40503101c031101c100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 482746312 1250 482745062 482745071
    0x316180e10050114010e0306070e010c1b030c1d010e0903090405010b040f09020301120210091208092d1302160c09061d130303090807050f120a0c02040902030703170a03 74
    0x1000461b030ba403041040541d0180e02010104085501454100b040c1071014034280198902c15642c0030820380104000c0c08042c0c040403024001c002c2005110000750580c50314001251070042c0081290180610512603101c09010124449820030300c101c949050028200b4002540c1d20800b50350035a00c60b10600e540b00c02d244c84007107201d103c0d0b40201c0c0d048408244041d40005155001c001b07080c2034544450342031260720100050210400940d2503d45c41c060000103441c1c0702c0c0c0f4410300c0004200131945070780324207078024101e84008401691031013a030420b4030404694000c1d01807550092252500144402c508102c070002005000002503050741c440103404e0103140c0c0e40d50654140c00302d03060074126291541380300040d2030b814155160380080c0d0107841c001c0b03a617039813030380b220495584901e401744c45039080a102480c2c201e608010158550f01d108441601d09002090000c0400c03ca140000340301c0c50720391100205554040004d580590342000071815800321000590010307600150403240883d042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 482747562 1250 482746312 482746349
    0x515010e06040501050405100e030a0609120e1c1b0f090e0109120507020409080409020a110706020c011d3003040303051209120c011401050316180e100501 68
    0x980700303070750440310183c5460703040038284010442d00c18000c20351079041020690601001da94200b0005038001e0084500060303207111801c10800d600500d0048a080c414480c1c255001038441140140c0c0074501e940100010305100d103400e082e00b0800c504613031601d4824039000700d2015401400c00c01100c0c0040e1081142c800e00141c510b00345c5420500241c8007038070245451400300d00603801014a648001d00c0050300c08000c0d52286599000754121000d003641c04524500b106070007900701026482400c006048903881c00034000c0d51544207602d010b04009182c01114168901c10344010f400d030794020f026040020f07446044c05e41d41d2139042444000c1ea8101400e1002e014400300407602502d4160f510185450203035a0f03e2a00440041c0c2510f14610072681d007900d0158421004c0c0180034140da0000c01c1060307110300200700403401a002030f0321a40140060b0b0b41d20001c003040c440103d0390000c040d5000481446880030040104090700380081c080c035031a11302c3c868640c0c1d0215040c1c07000345040180c213600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 482748812 1250 482747562 482747569
    0xf0115020a02030106472b09020906030a08041802071a070914030a06110c0105281e0b1c0302010f0c0e0a0608090c0a0905010e0106020a0503070f02130515010e 70
    0x303c3c4840c9000c08000511411102c0c040381b401000040102d44520450440824800b00d030040ba85500c01030321070b601e492103421407130815062030300701d04c013100103200120081c1c80780c0c0f0091081e0b01c954050b401a9078005402e1400d2601610441900001b0810a00b00c1800b01d82146440c1250380340001240014081160001449250206e80016005095540e45503480c1d034010510715041c4160502e091150444a4009020301072040c4418283d45107440a00c10304503021541c0809030b07801321820015031441e48400400310381c50050150402046044102001c616002c803032010244c00d10307114602074800e068054010406050b541e26081150202d030b004101ca50301c1c41d14258541c07102034880c00b000b0191081d880136401001030000c1d550340c203496a00140d00e05410b580300c81c40c3d480d103410040024015012050740102124000380c0342d2000c039980e94030303100d00c80c441c80107044802205c1050159220a011031007201503103242081141130110540d01d2481c4000c818500160400315a2343c1c0604 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 482750062 1250 482748812 482748899
    0x10050c040e06010f110d0f020706030b010507110a1802030609070801060c020d1704060e040f050609040b1b0703030203100b0c070b09130c05130603050f0115020a02030106 75
    0x195005840c1c071064646600444030b01c03110100c1c000401060300c40504a4640c18040f004084006440d0700c130324084442d1029007030140a0f030156040c035150810040035a45c00c9000c840003a540701040400002041000801c86c4820350400180d00c4507410000c4000200703a4011030040714203d981c0482a5120042294403500034064400040c800c08610801070030188003010303005105034030201000b10150f00184081e00f0a60181c17001030818080f11089050501c100206040b240c1400e21085c9801d00c041212404040c00090103000030200141c008035001400040c10110315a4035a541c003814100140030b5023054036121729882c00d5007400510700e80c10f40c0459074010110406011030341d140c81c3c1c01d5411a0082c00078642c0000030042c800e00c69000501c034907003130868907446117512220b02c2c0032000200101c40c3c200005062030402809001c207102c940c10340c1181c801041900700b1490340c920481c02c0c1240382000039015070901601142e944014010b1200581081e000c9441008002c100340781c001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 482751312 1250 482750062 482750069
    0x18110a09230612130215090415080c1002031909031101020f0c010c020d12020601061106100b030a201b060408180d0f0c0e0601050c06010b030a1d10050c04 68
    0x110401003030035003083d8a840c2c81c0d4030a00540c00d07106041e141d03802180141d20303c1c0c100050010400210714a03c0c0c5803502c6901c0b901880a0740518500b8185290b450352080003000d96031144540d1100225102d00c00c03c1107075611203a200303020520400b002c80183c122440c0c3d010860711103800c3c41c0c400000754800600400708100c410000e001c4540e2140054640c0042c4030300990f001101e1800c0d0401156545050901003d890760003080316600d0843c0043c06905140e1351040c6139006030050048851404440d5030903101000100b0f80d032912641e40c075100038100441240c01241100c0068001142000d01814000c4442104180c420051906141d10b81c00d045400621070304c000e10080e0f0007007040414445102002034981003d4400c192039134a58011000400c0300e0304a0b03481c2090001b0300351042d5164014100b82002c40c1030840003400d0507103900d01401000d800400c040700083d180c0f0071a40248200244112052120409008056484003107009692000034184004107400082c00c100700c5048 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 482752562 1250 482751312 482751319
    0x60503060415020f04030b09060438100509040f0b010501050f19020106030212010516090605120604020d181205030603030f0c0a151b020102040f18110a0923 69
    0x40d105210b0000d42054400c50007407031060001000065440c0c080b0307406003c65100401151809140540c14141d98003140d1307c4400c40000c0c2008164041c00029000400f0301140c80340d10740d0307040c007003440184c0e059100c1a4000b0750340051105024a42200044040c0101c02505450b80c84100640da54845d0420707210881104114101481100c4030150803403008034030000c11000c0d5a42c00180040130407201c60440d507551030060011007404405500e62031b0717820b8140114104e14080016049000d400321a0032a452070000040745075807164129110048000001c104c0e5100c00030580f900390b03008040417a034550300c0441800e100340c0200b01752881881c00800540c03500124607001c000b182c205220002c0280320300c0010078001180c0a020804840e11000c00081090600071500e184001c04000700d0196441044140320340074a01c804074040e80c045000040f062041903026a005103500911130201010216201c001c8a521603500021103c50740d541d030f0390716005204100c000b1414503020b10390 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 482753812 1250 482752562 482752583
    0xe01140408250b07030503010e06040b060a2715020c0307030819053a1a0d0f020306010e070909140f04020d0506180f01060e0c0f04270605030604 64
    0x158200640b8500c022000d600860398546540c50111605a800850045000c12000b00050000c82e007803828039507100c41c00300c405012401416010640038030542141504100c0c0d070300c0c0414446003070010074840300c5240080f00c1182d1951a070200301a90000d850880040c01034804103542c515000542c00d054980181e80301746440765540043c03425400464802052150a1107041614107002d0420808a00400000c80d070a6001c021040031a001488030f5061b018070785051100c1c1c0c01c66200c0940121281a1040c103503038403d500305088071101c8070400035898840d0400104134100c41d0301d0f0395070041456854000245455000d49402c0c4c440702ea086c156103a00b00000101202d0145151942003400a02030b41040c0b00184c40d81c5041942c1202d008120400205140a580400700003003102011020000c1101b0f0341440312407038454101034108404602c0204144140840c054116401040e10701214204a40c420070880d400d0355428601010440c44e003000003406d03042c003181403813107503502440e400c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 482755062 1250 482753812 482753833
    0xc030303011e15120501051c0b06030a0611070b09070b07121e020c0307051e1201020c071202090c040b030a15050a120605130308010303030203070c020405070e01140408 74
    0x200c141c442d01c1d00c20351558100d4a000240c208580a81c000464282c0e5901c00705914600151015a407042e842030f806080c048929200c144510b55100a415604c00302d04140e688400780000d15050204202400f620b00d0100100c04101c4110020044d9a100c0c01c40e440c0c1640c1c580f10348907141d0a292040f001e000804000c1c4400086540a0f120103170200b40c05c00c0080710900084151050038040300500240c1d015031848407035407904011174401420121580101c04281c0c41407035205e500b00c00115402403540010522064a00390103880c504084481211001560780300f6188510b00c40c0c900c20b9024110f82c80105414a032540100c3d4181e590008070540740d901c54542490041a99000728041d0900c0c40c1400b085c0c43d522044100014007500ea4009100c910904264080303510240c000a1090828192a800a0b411003d094112a05810b00580340e65504da41916400c02107030000307502910740302c20015402c1c3c00100000310910281e0760810103900d00c1510901501c1240103540d610380c00004c841 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 482756312 1250 482755062 482755079
    0x320c150c07060b21060a0b060a0e010518120d090902030606032403063112140d02030a09030305150321070605090c10170f04060e0a0303021306020c03030301 69
    0x82440060243c6011090b02c04c040c002d0070307298020076841d00d0542140d814402c0c1040070340150f00002d2000c8030f101b840c050f21010042c01101d60795601030306000c80802e010981d100e040205082c066000b900070150200c83c10f60a43e1990000344852012454440d80815908058800d40c0d100e03d030081c1c04640742d42c03074900c1246a00300445102c084107501480b100c0300d250b1400d1121501809240c0e00b9042c40071b001340005407181d0400c401c02568a01003281c4000031511520600e5280e0506082481910407114028234080c8142040e5000503400003080c006480e00507400052480c0c040e45e004c002688a00751040da41d200081400d40d4158448091000303400d0070842000c140034a4400315514000150380c0c1d034000c0d10000c48a000482d04002c01d1b02040e81804441880c10300002e01d8403c269101c0740920354251070020303064011480220001508010f2264801003071501401c0440e21034000c02c0c50010040d41c4408510700e54a1944e2500248441c00060303a0a00a5001400745041d80e080050f039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 482757562 1250 482756312 482756321
    0xa021606120b03032214030a02060f0306030a080c103219050f040c15120207170d050103020a0f03020307090c02011d030409061d040201320c150c0706 66
    0x5107906001c20420384140700ea0344150150718030f0840703405c082c1c214604800d45082d0024080400e01a8201454030401651480100d0b034282210178080354032a11030b4001b1a14122024100404464000030340c007454540006040d0300c0e0074030440307003844003400130800c0e40800039128a188a80f41f2211064150030b90b907060810360320014051a036110070480130b0125040d2842a130310440d40300c24180500003809003000c0c2c40e2014040015545109891203c00104031181440710715555a0780030a21904100628a000d020444421030454580f0b65000c042d000800c420701c4101c0c03040d0442c0740001214184041200101ca40003405400010314280c900c902501c07503200220219542d03030030840c0620040050094039034981000840c0c0740c9081c14007010848505411220740c050404d485604940411110554442e07030a10b820003d0300840603180410f5540926000200c1801c1201e40c200582c1c10006442085940c1c1e08440d10b582c100315842c0100c900031341e1149510304081100b0f41c01308032141c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 482758812 1250 482757562 482757581
    0xb0f09070e0d0f11090c07031103040e0405010b040506040c0914040207050d0807141603050913050106030f0b090f07081308030103060504021806010e040c0915050a02160612 76
    0x14007034504155030000a44042c2911011103101210700c16440034424803541104004e8025100e0002038108901003002c0b9016a6070700a0410504418500d000d000038815280100400d0a0034034242c14649030040c00380050f10440e9007d01d15081c000380080c41c15028002c1d41d020b40382c0741d814100381804c03544801d00100104017504681c00300304e4040001e078200a40302c242001542c40e41e5545c00d0920340103104205100c41b0a680402c1804004070b0740314502003003000d483d8142403007959221801c005c00d02410301480a1125a0300d000000a0f50302d030950011642d402031440f04003c2c40e428402040b4424006868401c4017406800000780024000e10819400842c0840300300d611086a650300030703150707000b6001151610345079805e1000318105100440c030b040060845c00900d920344180020060711500c1c0025208640b80d000b02d4405500860054010740000303011881d00d8506c4000240c02e5034400095000144100e440482c2407801c0554050261545980c9000c1d070300078400c8140c07000d40360401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 482760062 1250 482758812 482758817
    0xd0501330e0f100810140a0924150f03021903110714030403020f040b0f010e0111010e1c1704020d08120703050412030204140909010902090a05090607030b0f0907 71
    0x40700d419483d40d58203c240407003c2c40b0380c0e50149600d008411250a000b1a620880035003403510700d04951542d8882c0036a06445507103c0009104018040c03107103810102c01441d001c0000f00c204081101026038020b0941d008458031030b81600585500103c04911030030516810030240d910b04002c195200760080400d91420401a9007807800320703125800c1000618502a41c507a200045c00c00c118102504400d02410040f201000400324000200c0d00703603400c0526107810041d4140602086030302403204400442c014200030001c0300204031005070740300d00380c0760880820410481c03002d00d480c3c4150401007503082c4009992038952a0760b820300941e100c564504a401c2c1070b0600c4000450440491074900c2502c0645e0046000e042a05040c1c0c0506161525442003500401040c08841d060126200000b1000e6900060709d60710803050500418040c28001d510a000c5401d0100300640754111f68003c96240081e43c03559260300005030f049030600d0703080582004020030000c5442c500400055480f00c00c60 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 482761312 1250 482760062 482760079
    0x30f051c0305060307050103021c05041b03030801170a030f0e0619080712111c020d0606050a08070c0309030b150a0611060a1a060304080c030d0501330e 67
    0x4039051042103042045001980d00d00800201c0d1904010a400071700083c2411071411502206050a15182c4103c1000142c0c481000c24200034403076440502c49038441812465580d16443c000348000000c2c4a030100c00c1c0002c405100c1038620120b032002d8116815105d42e0401709020f941641c50003554104980c1c00007062240d488280d000c13500c40c89400b2800d568030511464194400740c201e4001c03500d450007080c508004c80039010310310000ca6024a0301440401c406100403140b150281c400d19280340309840c24190300041e50f64100010700281c40507a03c0b00c8803942c0d03811804642901051902600140302e40c4000c101003401c0303805d4290030500408070194801119400300304030041c41d038030450000e1500e03007242072051000e0082c42d4000321503040038440745401c5920341c111880c0ca03198a038860310b8000081070400600c46c0490301004c0c65942565100e0000d0132401c1c0c0180007d2003110b8042801c40d81051a030400500f6600c003030340d603400010b0000d60b2145411659410080b10f0990841e026 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 482762562 1250 482761312 482761333
    0x705010203100510140f0f070510060e09030a02060f0403021615020708030903030406050a121104140405060d110a08060405030c070e01030f0807020d081c05150109030f05 75
    0x80c00203512600109038800d049a00c2c1000703103e8540030760b40d01030041005003501908000d28440884001c401c5140f06a51900040301d80c6a049105d01d010003052842000d65120600d01c05801442c2102c81c07008128290b541c0340400c0c1a26032164101a500580100b4002440c120365602c8442c1c01c68081c5c4115002404105100d100ea030000c0c0d04114520380d001e08825441c03a904020110107044440061420a110007010030394900840c0074000c1408008561030580d14401e02800044048480060110845c10b03502040aa40311707014460058641d0034826089061500516000da20f001d0003403084071070f00b81c840305e180301d0000c000e507580300303204031000035a9410801480d40503034020760103941d8a80c541e03004145403150030790090400f240c4420040020459100e1440c1043d600003074447ea642d0035600c0020084004280c0081101d0070220341080c48034070752040788114000c400f80801503a114101802c4410141070b1807107000541c0c1000a000180c1200c444a1040e88280b049503902d101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 482763812 1250 482762562 482762573
    0x8070503030702011d0316150e060a1a04050f190f062402060106090905070314040f0209010806130206070f0501020c0a0c0f05060a0e012f06011707061407 68
    0x70540c1d5010041c1c0d1240702c00c000200103210b1440301c40e00c80000a41c6050b010181504580181441c0a40003e10342e85180005a0a603000214881c0a900540d00340f4a0000c142d00020301000c920810b801030b20b10351000590516100f09400303400c0c0b91341e54900f140d4403490100c0794641881c00c05d000d41d5881d003040300030481c1c0324014a8064085002c0d40c40c2c40c030615440c02c2c0d0b8442810381d010310840d40311500402825400c075481c0c60035150800f90200b03c913a1003040643c0541511400e0410340e00061041105104041c2410160a07108030b0344688241d0780d40000c0c50781c482d41980e24140d50340e41d01002400602d407410003070a9042c4110f4840100988546405007240c1010941e1909074211102403800c20214407580c40240071020302e510080750134100030400d94024056103d00384a0b029410f9000e5a02800c042005400440240d591410020040c007602c020781130710200ba54031074000085180d40e802c1c0b01200d6624100001064403500e010390032101200e09a04414a8400803c08200803a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 482765062 1250 482763812 482763817
    0x180f09020907050901170106050f0a0203090d0b06310209010915080f07112a1002071a0f1e0409050f010f05030d35180712031b08070503 60
    0x40443e200d49465540a0001402048010019000035001000140410303078112041e0340d803003602d0110346034460080c2c48003a451803085c000d20300d5120881e03000c50030400c901441c00512401007a5040907040001d0031030707511121281e0030000440304580451240c81089540a440520014500784002c02d540c0c00d4a0103040004051290007d0006410043c0342c1c038180d2140340d00318143d03251000c28103007500d40e811703202c0001c0458a10806c041500b405030801400084039180d50000703240c102d554142e840042d5680d00c803482500013540e4a5620690380344504000e031400200d003070012a1520b212a2030030a000c0070702c1b203040300f00104180400314402c400303482814403e80008484010b55410002180c82140c641e600491190307102c00c103c42006c5a0054030f0300507120001c0c1e81c40244009128210109184c0403580484201d00b81c010005414441c00e50241e80d810000240d900f05c548900e5903401c480c0180300098040b4104075100c41d40424070706101e101043c0100d02d200d0804155588040c1540e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 482766312 1250 482765062 482765071
    0xa02211213030f050a02060604050c0f160606120b0f0405010213080109060f02090d12020106080f010b090601050a0207060f02010609020703080a1a030703020d022e080709180f090209 80
    0x181c0070040000101034200f4000b203030700f4405040c46814203c0c1c0b030400a56800d00140070368010703034803032010901120a034401d49a81200340e049441d1030303816160910710007214090042e64104d0a0810025034607032540000502541c0015003000e2a545218004425000191040700d03079641c01c100c3e10f41500361929070a000b6041007000824241d0150034064190748990154002c094810040c0c40f00b942d032103030408640390b41d00040e0300c01e00c0c0c040c0000c2039004102c640c2c06000726003d070400811840c401984800c418450403500081c691301d806004440c0d900404040304050b80c172001c2d0a00c0030724005c0748d003100340902c03610021405507243d100000a90300030304c41c2200414460801d01403900c90f180a10700d5a041d0b1100c0103142c3c03000300400a030341c860003884041c1c051340c600d40d8018159100d135074811803a01c041c45040e10392602d04403145070140761240702e076600044c0040086510944651202000c55103005190f0500d05121040c0c50000c0c00f4205070041040d59480005005072039014131940326 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 482767562 1250 482766312 482766331
    0xa06021b210f1203131202010e0313050a080303070507020d060605130f05060103050606220b030f01060f031a0108070219080318030408060f1e010b19050a022112 71
    0x2550400400b041c644800c07551400310f18501402008182ca00403007106030500d40011310b03101b80340310320002640104000065800729001c0000d55614100711000d140741110400d48041e40e81c03558a8221075201c0c0001d544140014a04011036005450b190300080c5c0c1150042000090130303a501c4002400606004428002c0da54540700e8440300b00b00213101d443d51108003800e0502040c5072800000b184da02c2100d00c4659000c205890500d0101d50078108403019000304005690341e130900300f0501c0c81d16002481500d00280d0840246e6540902c00c4c094400c0c0c0c410f0b0f1640000400c0c41c0e510042d0b0382a100100740350110312509407000101c00100026120070380c040c8080503079a090441c0c1c03640e8041014180c0349159882040100220900021315a81c42030f004040c041c01a00d80d040d11410405151600f101d0444140780046040c010000042c84502865810741c044940c1c0c2e02d40a0710702e4010700e2800303c00744e0000e120307184551688420301c804005d600d180c0390707107411340c207081c807000c001c009881c403003003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 482768812 1250 482767562 482767573
    0x30708011b110c09010302060a050c0601120b060d08070807020d0614040201080112031706061314100309150902041b021b04060f141504030503090f0a06021b21 70
    0x881d6600041c2c4a030b41d07903001a02901c40f070709800c00030511491040c0300007405600001401d80081e40f1400036104c2c1d00003039030203940003075079103100c4140002500c080c142e5213214104041440c501e4403a4850a5050380145250304006a40d101d0030100e8001b6401643c00100810030380000401c103200300303011200404201003890230980001405500b058001038543d200c00010803001c0382d00700041e044171010300c02d1181d01a82d542000300702e2600403010352041c0b10b5502c280105007919822041e1a0754601038a6400700c20745144412070aa50a160020708440c81404002520360025000851110b0001d0700201e1403100711013255401d0010b09088400581011104084c103140744c0714001d42c0c2000c2210144800c905200c41c01d201a003a030702c40d0044104951a1041580c1c81e8000301e20383701d100481115454035541c1c10f005481380c0c020004580300f143c1c060788140d40c0b45028070b8041c0030b0303440b03d03070090a003000d90340c40080c0c00d11000d916080e80600d5200c051401806802c0003200d822443c00007424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 482770062 1250 482768812 482768861
    0xf0405131409070b09040b0d210f0801150804030c1707170708041205070308031017010608070b0714030403052413021c0c0609060e0103020309030406050903070801 72
    0x203103a040007402c5004580c100180421110400c401130310000141100c0c000b0b00140d0000000b46090601200181031681e40b02c18001240094100c802d581071046d110440c1090342003d04031012402400385450900c0c81100d02c0b030381184641001340d4403920a0030044080581074071249054420b100303c001603180d00040140c10404822480f00c1c00724600d10038142031106a81d50710742c880c0254001c0402075522603d10b0001e02104000400c01560441d40311641c9050414030303020078100c28001d89550084046000c034101c0814805c80c0d08030342052028018403030503c40c001c04150f00000040d100c0202481d100420300c202400140000c502c02d100030880381c012600d6100000c038007005151100d894038820410040700d0b91070b0300700200d94115902e00c00c1d8031202000c002c4079215a00d000d40071540014001c110380e900860075000b47e030000d40325035080c0c1d2885c000441c207a210440781c030425504180020407030280100060030448000500782d0361b0325521240d00c0c6085074000e25400100001c1c0b0902d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 482771312 1250 482770062 482770091
    0x8030f2a0a0e01020a0822031b03061410150e03030f130e0c0316200a11030f070b0d02071704050a0f03051509030c15011802030712020f040513 63
    0x20b10361054280003406515030181c40c1e0b00440d0003403020304904803403920702c3d800c06d00c090201c0810103150700040c1078140300c6604640d103504281a0000b21042d074030f407800d40c54101e05e142052910452522518881c054108217820481c412942d605d0340500281c107148a40c01c0e81d00f400a030030950600c2c440682c84401c06040788540708015803048170752400607014456040c11a0040700e0b44060f501c2c9000340c0c0c01d40ca00c0c408450003098060300c5850b0368110517030440400008100080d44501510180c0f507580b103000304043e1600700d030241040ca203901410040100c01e01100251003148103010b00103090542c1c50301c4090744a20701020710302800000084c148840c0c5840e4090742c000d000d00d6841041098113568a4a40c4e03100004420390050341d401c800111204420000c81c0c00c5030300c11100f83e5080604440d0008840d41c030a0044441d40c003290a400141003500c3d10a41e0b12039101035458072078403101100300030300a41c0f05120200c002d620070403004c00e81e6190311840c2080c08150030130002d12245680c542c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 482772562 1250 482771312 482771327
    0x30315090e1209011b02010504050604031101030615090302041a04050f0108070801021206090414010e030705060f1b03091006060e011107060509040e0c040c020a0201080a0908030f2a0a 81
    0x580702c0d200103014080c20359074032400d1040490001804601662854001600c0f14003603548043d500c09000600801040b803107400180302c110081c0c800340011078035000d40d01e0b5400c2c40d44a1003000110003402c1000586046d82001e44110082c0a186000c0c0c035030800400e00343d90707049600c0b030790341c15404004004012042241c107000308280c80085051104540310a00c2d10b00020f0103c0d0300c24011940403e00b4021640e00040202d45c1c1c4000030000c04a42440c4182c494102d000283c8850003400001951002c60089040c07007207080503007a4445040c41801c0c903c07286c0024007000300718401c000020070035560300d100f02c40141210b41c580d0f82e4102c1031071000411404680700e44e813241e504400c10030000c0320380210a84500c0c20741118040740341c0351031000c031a18004100c43c4a661042c1401d010811564011912500540c001e90341c540c05561200005816500ca0040080200740700300001080c203280082c01582141c0e0020361690400220382c1620082400b03885008020040002c130b050314103401842 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 482773812 1250 482772562 482772583
    0x9040230060312040518190e0c040c0905030a0620030708040c0602030c0606100311070606090b031501271a01030e0f120c15040b0a060504090519030315090e 69
    0x143c8500d02030600d0045200500d10040f84404101e0400200e02c0700941700484e6540c00340800810010380352001da035240d4404084c20001d009070f1800a207030140030702c98001301096134401340060903100c40f6a59040c00401e4010800c44d640b000c3d10041110403202c400c0210b025002c80c5c0c0d50b100250420b4141420700c805140d1120f400c1d5402080307456240c1e40d0100f03000c0d5112000712414000341080351020b4000d0b2080c104503561100700020780e00d04101095000005896406800308600d100c0382040c1035507030120944515050740003600411011648001a00c00001c80303070b1906198005807420f0405441c01d08003e0504502c4449500740c0c00e5926100c0d0310307a542181002408030000d090111900c5a0749100c1c1a41e02000005403240007100030071811004082c8101c0000c503510b010704110040b907005407400701c0300c1d13401c050002a49103024081c42202c0c2c0d03000703c00f402c8141014041e4400c003002280e0120289a2180c00002d0340f0310405080900404250301c010030380c1e0726000301003030801c0381524 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 482775062 1250 482773812 482773843
    0x9020405130506070e03101424011b03030923010c03051506031f180e011a01120e03031e06100512190c0c05010c08010b090402300603 59
    0xa4500803400000c0d000d50004c0a90410101c6443c0d80c0f00801d003064005003450151740e040a62040c0c000c00070402040c440c0303100541c42c0c200042034003000410880d0511016000234010b41c601c008040c9004c81a46a00740309040000710300007140e545101d004a81c100941c0b802421036861032024400f801004c882855030b00d401c1102e454981d507408030410361000401e02681e804000180022650850046602e04003203e0307900e002e0f510b00307401c00d00101c85040140d00301d0514174590422681400b5515290350300c41c401e030035068826801101e1040c40f418841000700c0e00c030003098500c4107042c0010340c0103100030590104c840368032580d0401d6800b00500300e54081c0300d4600c3d483e540c1c15800b20640f00c02c1803d0351804e5106072145202000384003104200703e0540d61500c00c40400103600021400c100706e01c40d0009009050744000256602c4400b480385001d0742400300080c1415141c01c0d401401040c4815025007848098030181500810502d8001c01400240000b0311a0516080107140051802c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 482776312 1250 482775062 482775091
    0xa0807050405100c051e071502190c03020102190305160503090904050c0a2103110321040308010e070c172b0501210b0403111020070816080403020d0609020405 70
    0x381a507c0d6114000d03c41e046c90725411400c6464014400e100040401006502c0d869a2803582d08240c3c000c65503a01c422805482504514a000030003008d16070849901501e03403500b0400140c9107921030b62007100c011507607808100004403090769409030140c0181d0046004002c041c0c0500e09006c00000036030050346488280f04601c0762803181410a41821030783c98540104076075169401c09265005402c80035002490042c00302200d9203400088074800da010b40d40700c0945076170318507140824003420b40c5c0c50000a000103801d0400b00b40d07503c41c00e040c16003c688000d858111600304010408902c0c4c14607036200ba23104051643c01c11854019a409800c02c58002d2019683d80e61000211950a4500800e150201d10004041c580546100142400054261803110341d141c51244000d0007140d0001d480c1b041c5005030070341341d03510700000da400c055400200e0b1840d14804801d90202152144000c84c2e0741c031070410000c00181c4800c20f07403c0e1120710907000441d004100b48100020340701c00408110021051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 482777562 1250 482776312 482776363
    0xe010216050a0b0f041a07030f030c0e150c0708010f230112050307150e011406030a030c0507052715090a1508030c0c03060c030c0a0807050405100c05 66
    0x2c0c290603404590001c000e560f611104644650054000c03944603034100c1c500000c5c07107140052900010111503100f44c0ea4050840780c25002a011a00d07080800070002e48d20092902d010306081e44030890444540160740c0c00c00c8941d81c0001c0c0f418410f41c008040c0d9035100c0515120b0322160b4010705140d0b0091030944e040040840c1c4812094040500c21140345030042d6481400703115090045804140d008500241031410844c4c3c4040070700414405600c19603e424100860100c00c4580c01d402101c00070080d1861280e140c402301c50010681d0020b4409000780000003a0541c2c4072041002c008040020200072450040160310000a006120840d018080010b010095443c529125130000c608100002c4211a14159404030b80c59034124001500c0009000180b0071000244d1807007103601202100c0007070b82d504250604500003030f0b640c00c4985105108200703141d80103000e100e0b8000028904541446d80d03c4c0001500c0608090020002c04d0012820105210083c012402540c1214254900742d0b0701 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 482778812 1250 482777562 482777569
    0x906080c1806090411060a080601231911010501030506430507020405040b0105041a0607060903110601060f17100612060e090c040b3a05010c0e01021605 67
    0x80c002d00c864482c0f003c0c1c0b40003e0400c4070290b613444d4022400740440b078445442c481c020b0b00e2401c0603106680401d140c40000354201d010265001c040b0881c20b04100d040c140103070741c5c028201407011030503400d20881d181c00008544007441114000c40c0200300402141c105900540800007003d4101264040010070b0401c11003502552012840ca52403518642c442590a040b42c0c18000c05c0350082d0f2240c00c14050005200600407034030306a0781d044030304020103034002c0201c1841c040307075400254100b0818401940815440c1d481194010301a0411440001c3c0c841341481c02e08400f40c10240200d40304c04419001158070501d4280c556200c4070840f496403c0c5144003595042e0700340b0030001002081d5a6008020940380c00c2800140003070a000603440c2403110306140c50315401860140294a010036a9629190842a400d0310001d0012400380740b5680d40c1040d04400132503150000b1070a9405900030020790240302c0c040036458150307290039004111000090074468498991b074200390001c5001d00c140d94 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 482780062 1250 482778812 482778859
    0x20c0f0304050f03301908191509021605030d02120a06030201210b040c1d010206060109031220010504140303010501050406081f06050307090e13060e10060906080c 72
    0xb101070040b6450220b1780c050b45001d200b02c0d000c4c4005034100d51012490140c00c402858010580400c03401d00e85020802c15008440c241032026144041d03e650811600d86c95a0090880d0305000c07100d0114001d59841d818034540c001e030304009405030300164801245000481c0941c101c034246000b0b103d240d1554000070300320110604610105075160355400b1910350a42d00c6140c2d26234028005100d50400d0100190018032151415005084903503c4410550300c0070a5461080d4016198100f0003421512524207030a940d401a0062101c0d841d614250914040208007806403280004104c6144c2854007071990031400034405801e43c02400184100e80e0840b0645040d5229450100c00a65444202d00d0300c041200c07070400d9900c1054940070402d543c0c00402140300310401d4036140d40d1180d03180f003510b0102c43d0407155407030390b207881c40640350014210780c000e25000315a403022940c030110280f0700307482101ca040d4881052517a44100070412a9002e00c500204450200c0d00407242c9000e00040740100d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 482781312 1250 482780062 482780113
    0x3050d11010b2b0615050a0b041a070c03170403021206040302060a150b070b011d040f08090f040f0509010e06130b070507080c070603270b0703020c0f0304050f03 71
    0x900c143e0800ca8050110000706900c2c41c0c014006110300c0ca98001c1c0819410b800340030b014002d08401001080c485810011981100d4540c03000803102c442083d0040400e810200303003140c610a191a000000c03603c41800224505003a0341e586599514501c100144403008207031840301a0400410032011030703004945030f58040302040020514143c0b103010503c6550740e5812003251410041841c5060140c0c40c0620390584680d0101c01e9107100d1031810300d6402c000d0403640100513100c056628000201020013520307a1130400b03007040350541c0340c2800017400d039030b05008031009041da41d8041140070f460034002c007420f840e00d000c060100c0303051003440038049160741500179000100c40340c040303403410b8030410840b941550040d8090361102040da0506460301028418000000c0c249281541c04100650903110454440080c0e20100c03285503503446000c0b40000d1210003403540c01d0020965029013400014510240c01024503517841c140010040c91030001000c450080e400741c2c03205c01c3c00340d20300c0303071081d40c00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 482782562 1250 482781312 482781349
    0x40b040201140c060c0d0b030f121e0705011406060f0717070b09010203041101090608160201061e15050310030b15120d02070905091207020411030103050d11010b 71
    0x4003048411400b9661083c000070305900d03c605400c100740c0c181d480c0040c14075003c05810601404002008040e83d6000b01071904005070042c0c0c4542c40f00e911482c00074007441c110034202c2201c0101c64100c4d43d0703803a001030b00c040d21b65944031700100d1068114401001d60164045425906004030b0300c201481c280100c100007041c0450000311250f134540803105a84802e6440901a5414038190400300e020750020780c0c2c1210100d401c00c100c2c490030360003140130000351030032542c40681541e520306222a101070301d00c400e0001e5551300c510100306d10210b8020b80c02904850040c107685a440e10b040550340c410000d0350f04041040c144240203a03124030128150403242c12100c01040c036140d41075183d40451304e02e1022a070011520038907446003007022690300c0b0b8805154094440d07240c0d40e4240d00059420850b08500705401400041c20700c084004084c054140c00500000f80310740440034500899030080e0000c0d107440e8454030340d1100c0152301081245070002c0410013482110f4241010808090382c0c0440b0500c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 482783812 1250 482782562 482782577
    0xf0405040b0303040902031312030c080c0304061b021f0203090a150b1f0806030c10230a030501080f0a0f03030c0309120e19051c020a0f0e010f0e040b040201 69
    0x81d80c0410a0342c0c05407656145c110b42d03900708042018061240003000f1207440c0f2603000400c0c1a45d0007442245428001da850f402159900c81490a40a9100910886800369200b80c0500340031000d41a416000c0c16540051000564180c0854081e034410031428480e903004004101c940c803000310380c4c0d001c1e465000101c8001405aa16200050a800001c2036001040c01000359a007a4140c407103128070310966200c26036183c840c02c00b45500c80e071801d00c1d45604080c600e184071764a14401c06510544405c581d5000e403d00015030102940c1c3d44c024500440000d498000501c5550000d00018140219820081440148a60381c681c4040d041240c050285940c8005281c0c40c2406078014184503940590744030300c042204100504075114182d407240c0103c2c904001c03200b81c410f5071802042925070081803a011804032015004511045500480c2c03c406038900025800c9400d260b450054406038460280700e41c1000f016030504170540d4003a800e600d000e01c06120100d240312803050b070072940a29102d079 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 482785062 1250 482783812 482783831
    0x1012020f010c140307030507060e0c2404030f12030e030406080703020f09120601060f1106060402160213050f103c090510092a020a0f03050304020310020f040504 71
    0x9525070f0311101400001e0000007140420168443c0041402c01c2c80751008220041c43d04c0200c03a41c0f000c503112850303007214000358003085004013192800f030060030701e108851070b054685e40c40502c644110340c011501100d446140e070b04465018014500f45011003002981880c0c1360250040c0205009090201803681c005600740b0401100012108500fa000d041c038071091080c0c2c040a56070302403d114134000681c0381040250702c01c0c458420a800e4030104c10082c003181c1c5821003040000d41c0030240c41100f43c44941e03d04401a225034070b983d00340104203034000809107040049040340031001002e50751152803140040c04182c000121a08003100700d00c00040c0e0382580e203415500441c52420001d50355051070381000910520b140c00c45403141c2500100c2c8a07070300361b450b602c0c0d05c1601c5910051807564a01c1034649a44d800f1208040b0004105604c101c42c008000f5859148260701928410b40004000000300400e41c1020444041d0044104004601e04007a00040380101d00442c050a44120f48030700106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 482786312 1250 482785062 482785073
    0xf060209030d1d0d080d2408060406110307020304030b130204050906010815060a120c030b010b04060e120d1206030b0703050627070c060608060114100906050906070602070c030602031012020f010c 86
    0x1f00f401c03410207a44600c800d442c0c4030804e0355600101c82c125002c50410840001c628a207209a901421240e0002c5040c2400e641c0c1d02842904c006004580340380094401a02617501c60085a01a40414024014550400c0240c1e0306018507146170f8808080c1c544144600341d21411046812681e21101c0f01da23400f8200e01c0c1c080f40c504540d0744050b0410400000109001e00c1400c01403044a105446607005032290006004012420944c00c000913001428000551401402d00c0001e000d40d54400188103512982c03400a024000d42d03072080000d0303a4a04019070303400e2a400d002d1002d02d01c210441c1401304059020b021b00140204404200503100c3c44810030000a81c00c500c0103800e240081e030f4030380d41c1c4500c007104000d0241941c16114409080c000c05d101e600a0070201b0170b9441c1941e60710b160a0030071042c04000c1d07201140844030151f08000c0700c40811032101204001d11b12451002d0b0ba41d0a0014241f5101c40b01a00004003200303c0c0180240165249041c1d900314a50078200041c07a4010340c01c05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 482787562 1250 482786312 482786351
    0xf0c030f04080c1204050a0e1e06240a0807030228110a0f02030c09041205031b0a08040b0a11070b09070510050403060c08070c0f060209030d1d0d080d 66
    0x102585100d8001c8125540c0361340409002600c50540c1c103046000e584034000140d1007021345040000d004c01075140465000b40100b00e80e400000949040c0200000f6132090600d0340d028024103403100740100d580307902c290b4045445504009180303070035400c1c00b54201c0391640704081c0d4030100c0821085410201825402030f042c505580300c1820684254036864101250724442144089209000e450904151483c01d46da41d0f5014941010001182d4994144240c81031342c4050300301701c0c90a42e201c00718200369101c3e074014850301d0459601c841e00703400c0500c1c01c0d03040c00201400300c40c662820200b9021000c4004c4041c2c40006d43c000c403110405886045240303040480340c0d0030094109114607000d200450f00000144100ca01c40c20f402c00c11f000d4105c07030481d1200e001352080c20019924106240105035440d408100342d0380035200c0145045541030000c0d1411440c2c00f601c0380407560420401b005885402c4004820314001d0310984500305481d42c5607812032003003914050b144d41da100070020071210400f25 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 482788812 1250 482787562 482787577
    0x6060e10031e020c0f120703021e070f0305030a08071b1704030f050303190506090606030901060b03102102060307082206051510050406030f020d02041d0f0c030f0408 73
    0x3011540c03413241c000c52640390a440c01921030188070380040300528445520864440d80d03010b038080c03c010604004103009194a0000080f000c1c854860049040b541000b181c100441c41040150b0303407104c3e000b0000d0100d14008101406004400c0c04000401c000d660105207203130390003c1c0807810700450f00c14907015401150009400c210046c0e0000e410001d00000860044402c048a11400d8005c1d820704026544100c03200c03500003400740c010034000d050000c051034102d0700000c0007007442e1f62034094146030b41c0c104450410140d0440d181c20040702d10040c41e120007031610301c64030001980720354000c0f0300b45110242c038010800c100a8009205400d50712480384503200300300c40c034036160f100c2ca003400c001404095510085000b80080b02d11040c0ca4aa5035810301000e00f074480f18109440e1681c2030f0002c245c440a5403407116001c0003079414002e094402000a0300c1400c0c440341c0c00c0e18152200b040468401000000008124002d11401112510a59a201d800a0b2103030915603100c0c071b490825030281f6034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 482790062 1250 482788812 482788871
    0x4090501060e07140f0703030902011e031509051b03062209020103050c0c06010b03130c0e0106021c050d0b01030618060806091504020f030a080304060e0106060e1003 73
    0x10440c80d01441080740288a140c0d00d10030112132040c08080603211704000740c0c000e50400c0082074000b901940061003040d005040099803c6802138055507080c0b00d0000070b60000355200b1a41248042d503240c1040981510b00c0c0800c190f140418125154004102c2070420f84200440000d00030b644800d9981c01d080810213440b0b02240b05680b41c880070700400d03c42240441d04110000300c24124440c02d030349402d048000182241d900c1c1203000345445d4800b03800400da003a0031075010070104100e2000d17400100b10745030401030785614003480203060542880440803021869082c14400a41c400150740c5036002c09138001544928940c01a0b00a00f40ca61050040c1d43c02e101c69141c1c815a140e000200300c07807901060707828503aa600c90041d1501f00341904003034400303104008540542803078402e442c0b050b40c000d03084038400c09480e15000da8981013220103c0342c9070b881e18103c02c9464401c0c0108401418203040c8000d6100d4010005017008030100c2d0b03100c0400d0381d40e0700c10b0807405640400d038842d4282b102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 482791312 1250 482790062 482790071
    0xd020d08040603060e0112021003110405031207060b010816050307090e01060c140708030706200c0d030605090403082d010f030605100303170c250302010b030601080d0e04090501 78
    0x400b07000d0701804c160721070f411180040030000204040007800041440d940140f0942041e004c0c60800d9004060f200700c0380e4102c480c103100224454a040105910489001d441d05031552464502030b81500d02a400d03c0741008041402d2011104140c1c0d5540306e2001d150402c9900c9503201201194011a030b94003e801d074000d10300c000204550030410300f01200d40918000d1491841170740010360303034914600c1000100d62040082401048199101d940320f150880d028042e42c542d07120010b01307207410454503250340341c0044508e1000d90ba05886803070020302c020341e000300762752800e603d01078044c0350020b10604413501d820b0380c1515100210014040e180c2c00740300c0c032007405503100c0c8101000c2010714042207400601e080d01003002001e06800b604120b952565440a04070300c168041d0018000207054052107180600c54000c8035481c02280c506805103229500c00817000034100242503405040d0341c09e02a810400041c082c0c00808118468942c20710304003c42c100240001040c01400444d4000e4220b52a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 482792562 1250 482791312 482791319
    0x120e0a030309260303060105180d05010b011106040302030412140a12030f060806011a0d060b03102c090a051207120203180f040b0402030a140a11090d020d0804 70
    0xc42903007010f681d01031800728240101c021144040f51028000071a10364810310000d2103a42c0b20700002e01d20100b1148030924405004000f0075040c10903082e08a4069441e21000e41a03541c0c8074062014442c039401c01070000381042e403006502d920a1f4010b5110845117485488103004521a03042091810803003200c08034113a0341400c000e0381102c1c443c07020010b0300b002915180107440303001d0401910300c0d07640a011079900e4031100890404100d00012030214040c802d00a001000d882000b000b0505410840c2d502d2801d080752400080c91034000808c04550501030602a2801100307040c3d000070400802d02107602c4088845140440006004225110704640c00111054010140148078810b400d0407901d511180400c3e40c81340240c1c4c07000c80900079010340849180c81c2034400c52010207000ba2001546081c06c0022a007664012034050036034a480e40c02c00c0150781402c4240b41e900003400c2c2d40420000e10b034a01d0080b070a100c3c1e5602c440c03048040203c008159541d420051100c1340d8002c690b1595a5034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 482793812 1250 482792562 482792567
    0xb090f040210020f070506030702010e1218060a0f08190903021020030a270302010212060102030a0e060304080d05070c0605070f090e07090317040816050607120e0a0303 74
    0x104aa040740030300c00710315602021034000a40142c4e2102402c001c1c000740c5043c50f040c0415500004c00c0c100c1103648546510a41c1134080c407030138480f514042c0504c0d60ba044c607a94901400742c3c080038414040d11003000400300a5034860b03c4c5500042e00b40c50190b100b600c0c2c0305000c4412030454555107501e00d00c0c0208480405400107924116400105800c2c03046840301c228118100b400149c1412008404100040c0d40c110198001080601c440d65007180904a00c02d4050b105c000035041140075030342c00225a43c003000c2c103903405541b01c4801d100442c5001072580c4000c19a03a04d0040d0b2900075107020000c0303000c00c170117070b01a0746860140403c104903d14001e480181080c11140042d0f0350b03e8940008501a14455a4590040c00c5680c170350070090340c5800000480240d00400e0603007001400c44020001a03e4882010104010b00c5a843c1d00c99050580c0725080c40e9150030404903034038108000304071545624040e5000c05402c1038451540021100c401c2d40c00d00f10200c0b0603644040041d070301204054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 482795062 1250 482793812 482793841
    0xc1b0f10020d06050603010f03081303050607090816080d030b010c0f2402030f0f270f07060e030d0e030321190203040b0f0c0904020318281101030b09 66
    0x40d4410018801544d44000380600c2d4403007030003040b003040040d800500219a481004018110241c403405800b90394a0b100c49061490a861820000c3d0300300d041001400343c104809482406144030085525182c11505661940341c0c0c0740c00014107448141c045416801406440c11164110031958120b80c06440e09803000352160100c0071030446000f040d907104185074400d0703a21940c0300406629083e207880c0c1d4000c0d1004001045402510f0344043c140035000c2044078513811184280c070080600854950240c0d0415407181c1002003000710113205805c0c180d900140c070b1611103d142c2001c1008061180200e1300b03520840c0c0c04620707941e00c1c0d140148115100c850741c1600c1030340d1001c3c000c1850a00c41c0c0710710040e07110035500a00350107185004070381102c0905002035003240040100344c1c9405800c90228090741c104440d4680940031501e01c1c0b0001c080700740800903589521900304c0d04841d850020076041d03880500c401a04140c0440c6183c54140d0180d031000100c41c200130321a56440c50505946050348 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 482796312 1250 482795062 482795077
    0x30409020318120d050c09031b040f0b13020304030912050c1008010501050304110a12030e0916051e07020409050d0f0504081509100501030c06090b030c1b0f1002 71
    0xc4494001e1103003000e02c00b14544001034158020549040f102e041c00c0c001411018106601240007000500c0346507404115032800c150525042c5455111745c1c1c02000119400150b9030b10005080c035010410696410f6a03011841050160050b100d03140c43c202115040780c40d42044480b8040f603141103080c050001080ca115107000c50722280101c060407400c9414150a1040501051060011a0010701500c10782c150717414002e81070700d220540c0c1d00744111800d84050015000319140704c00c444000d0030a19034403540844d4100d00d545901c5d02c1080010918410920112807109a80c409907a00c180c1d00811545a550010070503c09949a070526a490702103410064000ca003407030468075034050042041d03404a41d1518080d02050a601440143c00c190092129009004103007041100c0e4100744516030186020303007800d02005051480180c00302c441c41e005620320b0b140c01e0081010001c80d800c11540801201c140002a41c401d03e114a8070302000340d01407440e10300800002c090b01c101507038040c1c07000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 482797562 1250 482796312 482796331
    0xf010914060a0606351806060a080606090a0b0a1d0a1b030902010309020604030f050d0201110301060f050c070303020c2805220603060207142e020c0304090203 70
    0x11501d40e03441da02c1c101c070401d10581010030b2003801c51542c507054402c03000380e036501c4d105140d40500048103403d8000d41720844000710314542409010b100076804111950740300e81c042d21107544950070034031150b0340c03954020070185c41031301c021000840315000da8200c502400c070041d02d018a255100d202010482c0b480003043e11100e80d80000240e1049494081e221040c404400c80203415008a00110064148400140d062640b16000030700180c5503480104011030051901e400c2c851800d113015800d1041640c0c50300116810100c540c00800c80702c1e82200d0441d0841d0030400c418402da401c06841038014900311000c4c901031980000309061700880e5142d0b01400482c1c050210308442e10003a070f00b1654480f00c0140c820b404940c10300403414880c41800d0b0b21495a0042c480e023104010165081e01c55680003110300540203da80030402096040e001203200080010b043d201008120a4508080c840d200058042c149003c03506c10004642c100c408800c140426281d030350f0f40f519103a2000c1e5009403000800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 482798812 1250 482797562 482797573
    0x60108101d0724020d0807050315120309090105010503010e16110d0c0c0807030f1101050405061303020f040501150804150c090f060203040e07050309011b0e01030e06060f120f010914 80
    0x441d00c0070505c1014084c00b1344900682d62204007040711142c100a00e23802d12600e044103000099910b007003c5c15039490700c010055548001003014403101c02c5042e4422810f0100500040c080307807046d140341550150410040104522400d00100c07a1120506581c008034015500c12a40c610b81c8550500300d0103025101481c8583d43d5458820b40d9126a4400640300000310118840024000d00328520b034004140351a0341069241e000142c0030b507200100719008010206410000c500304604400c403025802c0300c00b0400340d0b14119135281061500039165081080000c0002d0401005580c004488060f44504000e2042c1e002c80c00303030a030003940c0521314442c000180c0010740244004103c41c147c0d00451114510354550002c00d503034980019111742d815540300c0101601a01410a00100044590b90b80e074203455070000025044800f041001450b5030858000c2096585480040134090f1505584035a03d80704d6030000281041ca07910f2482403a5400c0c03100d000240152902e40c8950308144000362203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 482800062 1250 482798812 482798879
    0x40b03090706090522270b07031112062103121f0303110c10090905090c0a05010c02040f06032303030103030e100c0b090105090f060108101d07 63
    0x6590380014880e043d8001800c40301c43c1103a05e0500e0401c02c03016513404c004a603040200003040d0003000d07a6100101e4140242d0b40c031105005000c1c0c5003030b03080003980c24208500b030b001c0c00b910b4840d44100440003030072072009800300740c05484003000300104280c118110226444091031290312580320900c1700c5500001c8101088041d6460003880e442b03c90000786101c8154503650703041d590b00ca106422040940119450101c140c0c45403c07e03c0c0310118a66982a24103003004076400c1121005025003005501485101c0c04e00e4603180205000e9031024204101540140c1c03001901416075503200d4a042420b10303c002040001c03412081d41044410044154000503014030b042e6a80001d11019001404404100e5441d0904006000541c2d515245c0500d001d003080d140c1540c1040c0c25038034002a40c2d915800c02c0b044020030700c484104004040d0241c2095403401c0e1007184c0d500101242c4105aa60300d000482a4688a09180e8019107052055a0b00d160382d0300d9407000c4d500c4c2036800c80a5140c80c80c20210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 482801312 1250 482800062 482800067
    0xc0501091a04050d02120d030c0318030903080f090a030b01030209010e1311060c06040f0c050303072001030b030a0c140d05030a141605031b0d0c060b030c0402040b03090706 76
    0x2071064410015060700745407904041000c6588a40d40a0f03801200300071440c161518240815008140c840e10081100b440d8114000c00712101a100d50995400c0f10f00564000703544100c405040302e41100c416a00c800d480c01e200382e240c1c4036480b01141d12030300e900000410007903107095050407240200c800b01450313a690110303200b2107403084500c800c074800308101400024140d1880103440f401c004d424a403d0031745a01c1c0a510345503058400b51025220349400000308110300350b20074003a26094002d54184801607035030300d034803000c80ae00d120f0314904c0ca07519038040350340300e540312108500006040b908050004e0400c0c5d01001114000c0c00200321078058021982c0c1401c0f0405503401e68003400861400e00034690440d10a1080c074803241c6090810485003030030143d440d1800b084940203034041c655034803020114003080c50004903590300c680c000d10b40c03101c80d56410080d8406501c0e0481070100b010100e0100103414150034030301e51a171117440800c0224505030351102451140600008a925554030340e5410b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 482802562 1250 482801312 482801339
    0x405010b0306091906090f05030309070902092b0506010e01060305060303181c05030307021b0a0501080115090e0a02030403200709090c05030303070e090f070f0c050f07030c050109 79
    0x1001580c0b044d802c0003038824114081c10307915401054005141882c581e100e17180b415608a050300c07141d102000303111046100307100000050898101c218540780b400004594dc1085941072000c003642c0c405088151400720046040b9150352000540303415603101c0444004403c020f0180340c000038501400160103003030000840f002000f280c80900100700d80c100c01c111980002c3c140b54840100114040d000080007040610b000303840d40d4000d0310740c00d0049820506400144d940140c4a852246c004205076608a01c0b82419255482020016101e5898098411620a60101c040307000b0b148200000000640d0103980280d00c0307580e800c05800444200110b080da0708510480301e40c1c0000b4020080340c01140d00600c1c00d00e02c204032100140740d9590000f0f04542045031404049810319800b1f104a1a05050040d070000201524030198140f00b02c004000a2403c1300d180207001294500304284101000ba003c0c540000c003007102c828545924240d4070984044c46214049800480c000c294407416820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 482803812 1250 482802562 482802571
    0x705090a050403170f01090209031f061a0f07080c03120103030906110114010e190f06210308010509100509090f12091507140d030b0a050a1805071b03080405010b0306 73
    0x29064601d03400c04102c44000d5010722000f0f642b512032000800c0b10b200c0b4050604d10781640352800012402d01e81380c0e0b00c0300b000310203000d108107949042152541105181d000d45103d80d81141841e9203408541c256246144210308101c06041e02240c000000c05502c641b00e8010b58500d43c3d03441c41d469901d40d00d4182a50074802e10f000304450104018080b0072801001c165200c4500d807070841c2c2040c01680840111035602807083c0346035442c0c0e04144100c1900060080b140c0e184480100c03074001c0350391401007850006000305e5104840000105104580c0400c2e0b403000341c00020a194800c1c14050741d4640d81e00820840107000307002c0d00080c1006000340205488100304003601c040361248021140e003001e640461402c0350050340000c8101034541042214210a9180744c500007602040c14041006c0301000c4d91091740b1485010400f400003a1240050801400c0320090104293b2203070031050343d10354415071042d01160304400e41081415440140d80c0e019900800081141009032024551030707590447c1e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 482805062 1250 482803812 482803831
    0x4061208090f040507020d08040201140a0e0909030f0708090d02041803020f072904150c1703060a03020f150d150f030305030f0c09040908040e0603010c0806120705090a05040317 78
    0xa03818030303808d004122250340944149091050130001103201b1000d5009210100300017801c2200703c0340a42411404540c010b03101000540c100401000c0f00c40340c600c601c441c02040040f01003000710b071070f4440890a10302d5030381c010310901003900303044a90407440c1c59051007070b001480703034502c0107503030710b8010a292003511b0780b884004816203143d818411200b004072440c41c0300c0160412002a40640701501c3c000044819511a009000182850030803800a035400301c0700c034101041030010b656604010803040342d0381940c61504510001002480c003040d4011800810000026400079140e580e030f11514500300015150b400240d04c9110786601e0101a02004011030005c0000c83d00c1e4001e51a04a41d0207590f050b2100e00e0303ca04980414240c4006910032240120045014824940d010003025401203040e0001c00c20329251034402410003c0103414980503120380030940098150a00c2440040d2001808d07056460900c83c40d0800245400c640aa001400490142c43d803105c460314954020840403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 482806312 1250 482805062 482805073
    0xa0c0c03030302071b18200d0b10020313051324091805060601050f0c0703081b01020a020601090b0102070306141015021f090b040b090f03090d1104061208090f04050702 74
    0x201b042c40000c0090480c8801031425080c5450b02000901000b0080000a804081a810f80304000d00c050f0794007080191f8199002400702e0a41840d200780b20204452085a000c0701d550807002e4201c000f45005034102e0182c605115101810b020b95030382c548211604490104103e02c0c07d02c0751515000300b585402001d5401000c040303902d0390b101d400504810502c40401628040521410700d18014095104440440c0045052801c0000c1d01848140c80540c50000394949400300c1d41c001c4d11440f0501070035207550b6580841c4003c5902c00c00544029590244003080b444115440b001c40d00c13041102d000000d8040e4075404200c101c1ca90075200300005154000f0209802c0c0307c041c4070302214040d2202464188e8844e04080850580c00049008134000c01d076543c042d00700134801d9810881c1c4044080c006e60b03c100841c00d400d46135210039040450b0050b015a40d41980100090050815507020690b200c1a1800140510140e00c00410840c00c003119100c81c0b2880e002d00780801e54004407041805030300074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 482807562 1250 482806312 482806349
    0x140c0304140604150306060e04020304020d0f060f060b090f030309030604031b0c0b0703080703060b0a030509030903030f04090501060c1a06010e120705090f011a0a0c0c03030302071b 80
    0x207010340c4200c03001030445003031075200d084201000c02d0340b2441e80002904ea00040204540001c583c0d02d40c0c00c001d40d000c0d8038526182c0c002c00c60013440518010210480e000d020002c4c828035510a0120300d00d072480a1054960300c0e4180b100640042c1402c070701c14a11054684a149070000440300180b001801420301390352181c4068a05070991403502c0c420f198454008030005828a24200c09030400003007641c0c031000b0505000b0802d8200801e500180761418a05103c016004401da40c40c4441e1840e002c15030b941e54242c018154010302c0c0006d509440f020076074036140344910000e03005551401c0c404008070f80e60303160115400c64898202501c000c10562580c40800d1200d0180f41e8410010304000002100350030114401c03171000085400e00c0d0f00201e01c248191728005100a07001100c40c250f41115504045000e849103010780288040090f0000300060540d000d11a061012904098407032051a038030300300540070398041c0504903500410000c0840308420041032032010b540201140c07400c041c16 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 482808812 1250 482807562 482807579
    0xb031b03090f010203010f0603051f090c0908060f01080d0f0e040207030302120106030e151b2a01090b0105120d0e2103090a150e0f0d020607060606140c0304 69
    0x2070800c041500508058000c04042400114000d00d4139600c00c0e07100c2c0d440d2010040031244090448070710300030142c518910b8103011341040b10541701a66000113806051000c1564080e920ba80500c000d0301840d03003000320010741d0710b2415040364070242c150b65881c1c1e0701c80d000700e1320949940f40d210f0106e070030314214503903608196020f070034480c0c403d04005160030000031801c51002d00c241c2c82800003a0716000c0e50040d86100b07001c0100748541300c0c1c0c85040e140c204000307a00700026070035003403000300704012500003d00c3c101034071191191a515000308105c10403c040d03c50103422200425a041d460b4400005035a0416004068507019a41c001e000c0034050740302d08552551008040720303803007841c2d000d05081d0030320901e41d4082d0030b0300340350004c50741c6000c54800e000200e41d0b1580140d00080391004600b001e2070f0499030300311202c002103034080010352442c000142c00e101ca45601942015000c1008030400942d80d003d036054a030f40303480d1400c41030382010382044c091080c8468640550000d00c001c0040c403d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 482810062 1250 482808812 482808817
    0x70602070e0a090501020c060a0e0705010e040207020a03020a120303230601081b0a0e0301270602030417030c070218090307061503050d050315062701121506090b031b 73
    0x4080b40002c1584201034941509a810082c4688680e402c5403040c05003001c0e035803055600c201c030014040d00004d0702d01800600100c000400312030185800140310300455641d00717a01405983d00030030704102c190300c0310000c55610303c03844070840120b840d00b0001c3c2c4400d00f04481c02c0c00c0342c074505900001596140d00045030f8921010f0070b8003049030060b4000d0440404000050810321280d6a504010100020b00701420344030005004e86200010b44641c80602e041202c21802851304a0300c096502e460328a01450790030203140d00d00c0c1294034084140300c9641c2c3c0400c000d2403001c0c000c480301e00320410a105151249502911450515802081300400180440e0060003d4241800c0142962580e1752900342c2028000d10b039680018000000b004408104081c8045142c20b096030a5814001500e0781416105688221400e00e90001c050505142e8482c0240100d02c00907440f05114040c100719441007015107500601000c9000c4180126240311104140c0784a18050004040185040e240200669 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 482811312 1250 482810062 482810071
    0x1030f0c1e050d02130c0203090918070b2b0905100b100e5a06030a02071b05010f02061303080618091f0209010210020d0e15010611070602070e 63
    0x220030005d1118241e052845504000e50b095000f441d640e1000c001002140358000702500c05500e501d0000e4a0041c10010720b50094690800b81c0c10350f24018034250070700c90881b02d440301c0ea03811070541800079481d013039410003402c2c203114000310b500d400c020420f07220541c0d8241d03014035000880110151754441c85041640469a0301403e080341080f1402c4020f489c2403807000c0c0161000d0150020640541c10080282c0341003d50510b06000d01440488124038501118164030301c11030011010540c441041c4d41220420b9520409500c142c10b007810302c440c0703034003107510405002c5602c0300100642d050000c03072254410100c0440c918105680d13580c0c00d0308c00c81d20151040350010084c0c1c9031041d07046c2c07000004c80e018841c0742c0000c0c00f40c01e2180300c0d8410508121108032100a0040c0810321260360001428600c00089030b20240e1144000681c4200510039060100c142d4400e280719403064a0801c001c1d54141c030350036070360031442d16802148030b6a214070301d2140c1c80069004013020421408500e03015a0030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 482812562 1250 482811312 482811319
    0x1308011e020c0c0f040b04020d090317190504030908010207030201060623030a0f020c0f0f120a020d140d0603061b0806150304082a0d09060e04051801020301030f0c1e050d02 76
    0x280d1a55001247c204d81044030f011120664400c0c04006140d0400902088190030003031108991410718100d40c0014003003d00c0f901c2d49500ca1010800b00f40c010030b07100c0c004e080500000c54540039a03080c024080e0425109680105141c10f0b00c601c0c0d44e00c02ca0000511b09004243d510b413541c0c441c42d02c408003c00d10000300041e490743c02c0c0309042c1c01a40522030300c2140010040145190001c82000500b000031084194090103001c03c00700011503000310f400302d805c04281c14001d804014603200c2c00c00910498910300c83c028034020313021080042d01e90049504040f904029008030078082025904420243c0314190b111003041c2c12101c400180400a503030140c480d10802e41800d500e00d07000b0342c3c00d003600f981c121180b0700c181e103403661381800030044210760341e400303140a4110a10f440000340c0103185c280c1000380207036100d00006101000c050f0a0b21000d1100320000c40d683c3d0ba40b8240169440e0043c07008441a1080c00f40014181c0c01c03001017010014a0031505948840c501410000b150b45000b0080b80c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 482813812 1250 482812562 482812571
    0x6030503070c08101a1908030a170a090203030702190306060b041502010c09210f03090807090608060613090b0a20030f15061308011e020c0c0f04 64
    0x2a81480503081a911a80d0b4554046041841d81828610130240c030002d02d915210441e0090750303295080e103080301800d440710500e20300c4040300e8840112075138006030709920001810640c201e50044c8003110072007c03500301007440d0300c6070b048590a8803010803010358075501c14401c0c40d0141c071f020882243c0c042d40340103841034195602c0d998001590703e1a44004c41030f020209040022180200d00178510150510081000d0400c0e900054440300c82030203007801c000025045403140b0b4005243c924100f6400011a403001c1d400c2e45002030000d4418003900f03400f03011b0400c2c0080d40c00500e00540b0280c41c140409480f0700e40c0c1d086c0500041a07012000440c1898440402d2404607074000400ea00440c031204001c1880e4132403981201d070319202010b10000c0c00c001001004030b80e500c4035091039080083d03000c500b8525070032040028501c0c058203c4032400f04030500000034040340154041c1507910302c69a40d20304e92400d01450700c02280182050703190140c20040b0310310381d24641808003050440c002000003a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 482815062 1250 482813812 482813819
    0x10e1f1e020106030314070c170c030115150c050318060403140c04051f1403010b0603010e040209060409031e050f0a0c14060c180d0b090319050f07021306 68
    0x4065610600e0a03400740c2d5407210103005055110790901d1094400c80178092030112135507610350030f01c1e005100340b242414840070f01c81c10100051080a2480e84018020b100d1400c946620100e5202203106107440100c205d510340b411603014480400c007080c0c1090185041200c55080d40550103520026540c3c007100410012000408141d0320b480000f002a00400c41c1542c0002800b080300c0e400b81c40c0300009410b000701c2c1060182d116240301d0a03600715085c01d81901d06003c02203030240c008582c0750ba9016202100204042400209140c456030007242c08e20340a0b110b0005000c00c440d1484005000120f18803000012182c9801420031170300c01c1407401520300303810f084480c485c80c0c218001c4140000c80b5150a4818000b1290079007402c0101c0001400040c24072076105c03040b6110301e85d050140245034000c420320613a14000743c12555504080a04420300c2e10101c00d6842c2e81c00340120820207a402850750394180c0c8240203072080c0c0840821040d00e407c14507001c01c070031075140720741e0641000d4880c203012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 482816312 1250 482815062 482815097
    0xf080c010c0615050636060a0c1e081c0209062205270903040605030f040305090901030b040b180607180f14030f0606100c15050106020c0f010e1f 64
    0x4101e4034024060302c00031b00c032001c440002c2103201e400384403210601052209003250f41ba40300b100c4800045045c14030b141c00003841e14504ea050084c20480c2082a071910080c14040c0c0d10b802826104440080c240050304c2081c14407040707019580b2002e40020041c016a101c14206102c4001c61010070032840c9009035650300001c0c19400c10480078a6507041034a40350528640310f107503441c3c1111034034000c0d60915090110042070f500004064038080d800e000003040515014804842008001401038940c5684904060211140c02e40e0100c1c2c51040d60f04c0040d1002d0540c94007101110100e1000e40381d15207601c001250008044207032022400c40ca1500081d002c1d403980151030042c581c01b000c05130107a0052040500b40040910bc000103900883c1c10000b483d52258046215900030b42040c0711413201c0e5051140c03400c0c7c2590280c1c503007a0f14240000c01d542e600020712110f07411044072407003102c100c0ba50045a6811104103400c1c1c200c40000c640c4480d00120041103c1100c8091800704c19036043c50444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 482817562 1250 482816312 482816317
    0xb09040c0e190f0605090306041b030c1e320103320112031e12090f021c02010210090f12050310090b03030717041a040f080c010c06150506 61
    0x1030880c5840e40300040003d250b61643e840000c14060a1250408103c0c4001c03e480f0000104014109e00c000089030070f0903007190784041302a50b00940c4d041581e5880d02080c102c01076800030bd00c6000107200304000340403200700d080402d5103038061001034000000400410340104801100d80c0c103154860000b05032504103e645411074244040f0803203462403003030000101800c01038010145170000a40c0c4640440c0d0086505401402807042144009a00d008102d82c00c58280440c1e001150a01d00390740b0910035001415241c15001300c480032141c0c0c0000c0701051801125400081c096041903607661082d003450b6105c0301d40c441c051000303100c800d0f0482c0d680c42c0b1100c900030504c1d00450400700c00e00200c003d50304060005842c840c001008118014400280d5a008403000200003290100300c00207513440c0700050310300034900244141d61006030140000714581241c0620343c1248000500016201e900055220f507101041e118030302d040005882d040d024004800c0902c0d1415070f607a500281c0c0e522620700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 482818812 1250 482817562 482817589
    0xc01030e01022104060e0d020d0f140304060e011104060c0b1f03201903140f071202031b010903030503100b0307030c020105070c050d180f09060611070b09040c0e 71
    0xba2020f901d02860010100c484062944030503a0040c41c1c5180c0b2076400041e40c807240742141c00d051803e6084628207c450b2110040f0000d0014004801d0108100c600c0d0072841900200b600240281c007191011030240f03000d5442004000380f43e1400c1e01c008103800121440e0000c01b42c42880300e00a00c0700e04000c00002c43da5108403600070f0307200c0040c40900056060f0300c40020040b610014250a10200450f10150300e0001400700b40c111020344d040c81008000880c07003c1821415102225650f03000f020045032081c100341d00901505405000c19454540d200c40c0f20f00c016102c00700d00f00e0440e201219150001481081803100c401c0307011807290301c1040030314425801a81c010036110281c2000030b01b91a00500150140000166080d0014801141c00e0143c100c2130306c1c041a240418121507032407010154464004400d460300007040c41c03003a90704801c0540340592101385c810b454005081d40d0310704440c4902d10800b08140261101c80c9410380003141c9001052404c000845401d00c009a0700d1103c449 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 482820062 1250 482818812 482818867
    0x403020405070c030f030b0609030f151e07140c0f061618120212060a0b0f03060f0a0b040204090e0703060c050301060813080c1f0501061b08030901090803010905010303081302030c01030e0102 84
    0x83c0144445044cc08034154044903014150344050640f4000748001031024103560b050201000341c050071301141d0800c0d5590488400c04a0300000e4140032120b07103640060721400c2d021003009201e406014041c042c847c014a96030303515002400d145c0701404070000c00c681d1049a0140f6058203c915503003040061138061038510f0000100f000c1c5210130080301e080c14680f01400780d040b801c02c01c0040c001e8003040c2540b02641040110f214a15040054000c1c0715035004107041c14034000c0d10040c01d14000440c1010341e44184020008c0c1c00080a05840e076020074880c450000f040d620024100804800c038503541ba03840340c00743e40d0501084801c039a080c41d4041d08503034404804000e43c9200b400440c0203441c010102814160b00440365110f0030003000407000c0303003c0c02201001001c50001082580b0810380d550300500d01903180d507103c6845101900003884298005a80301c401719505600302c40e07030340840035401002090880300800041d0050050400c1a80c42e0b55828049041f04402c80c0301c10040001c2c011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 482821312 1250 482820062 482820073
    0xc021c110c0a060507150f09030201020306150c06010b0901020a0b151003021e090a0905010b0d14070c061a0301060602010603050f0307020a0e130f080403020405070c030f030b0609030f 81
    0x3164aa19119500e100c203445212504070400c8038680013821200900e4116881d4519008030350f8520303000d04000e03100c0500040c0f4042480082c0740e419030295018140840c2d05414004604100050600a001c11030005400800c010000d601d01900100300903941070042e10066440b54030f507080001812102928014403c0828100718541010340d205800980e040c1141030420749900c141140d1122240b8001901001814101c250f84440c84c03000180744601084c08150703141c3ca40720b0000d420104030284680d051009020501108542062007005140c0e14110078070101e480d484c001e42849240250204842d01440741140c500f8007071180500321036000450201d1661500714030b084246412210305d07400c24015035006035a407440107030440780321040d0000c80703885483c015034900030768190082403002554088020040e06c400504100c80c003c0b80c0030800e40da148001610300200034000200041c054868050341039010364080406500302811762410048204040791400003264031402055200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 482822562 1250 482821312 482821337
    0x110d0b09100917070203010f0203100e010b040510080601120c02070810020405060a270306060f050102150c0c0705120a170f1c1116020109060f090302040c021c 70
    0x8005000d03200750000400c000218040c0ca8031802c8404007a00c1800d03444000810405640c0d0135048680001002c01045680703091441782180c00b82a03600c0b599103840c295034000612140914242c9007250070281c00b407220901c181c079084901c810010170160500c81c10494001184040d0b118540001030035400401c461030a040106240500050f40c140781d0300d00401080c0f0580d1254801d07903801c0c4800d4286480d00010519403031046401c50080c90011110a074000424042660010310860f600c2d03080320380e803c03a2528012071700c2d0091900c43d40c0c2c01440074804280405070f51401802c0c00a542300980e8060b03920303640002c8854030040c40300403459008200c49011b1040700070000e42912200d05502d031078600b0441c01c91907030b03024120382ca20b40740c03d41d08161a0b851950750064414045003206003075035103071480c81041c4100c1c095941030b030000740c10103404034406001c0c0c60062354401554440c0e001461666003000042c088044900b411030140724500c4202456401800d1f1101000752940c58402c02d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 482823812 1250 482822562 482822581
    0x1120c09090f1707020f0f0a0305120a14070206090f13060605070c051206070f03020d021603030501050a1a070807051204030620040b160c170105150306060607110d0b 73
    0x20040c201e0200001002014016074440b08914080d9100f85c0f03400007e60390110005203406a40c1d0f00c00740c114004c111101078030705040002441c003005240c0320100d459000014000881c001d00c4c0009402c40c10400a00000e803808226030703450340c00001d0042040490155925042c1d4196a001c20046003000c0359203030411000c01ea641c00a040e00340c443c9959011070800281d501c17030020700380c0014040d03191400b013002807081d01228040f6070700007401e6598682040800c0b041441840c81580002d241000115440c80d12070101c0003100d00c00000c40c2c036181406a00c11410f54002d41017103541030010406032002580c180720321601c00c403001c0705e040d4845296042240507120f25041c7c1031041940c4d50914500e0440100544013640d036042c1d44203455020a004e86481b8200a030000341640d001c3d0100041d50741a00d80c0b401c0c50004c0101c0c0280603a440d0811076403070041d945000694142c10000001e0745504091000e4820180120801b0920160b040081762a0346023000d030507142e0328518400c1103203400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 482825062 1250 482823812 482823833
    0xf0a090503010207020a03080a3f0c0206310f1703060d230703050102040810091106031306020403080307140c06161413080c01020f0601120c09090f 65
    0x14140c0c001d525001c0285d000501880751030000a02800340410811051842980d00503240440300c03d8102001c4809001c83c0561124104402d5081a41a00d81a500c000500610520b010150000d04185e200c00484c03003030000e0038603a80150106100040c1e817085c41c4070038006444d640141041408050242031182001961480702074034203c0800c1404020b0b110111140e0400e60004072000c80e20a540306d01c44940040010880a1071041c404007005001c01075005008691071007088420f400042001d840c15601800800340408600100c51103050804400031a4400c0608100305100c0d0701a9940c1c0f8200e030800d80040d10300c00408410800d00c0c03604810000120140703d50b240f0300b0202342c030b0559562480c00500d0300d08402500c400800307401d401020205030005181040302c0d1034080816903200c0c00c880d10700c500b511610840f5407a0300154000b0542803103109019014115981c02c2401c0c500140750340c2740049420184501000507103881c00c0c8107024610744240305002c41c0d107825042914900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 482826312 1250 482825062 482825069
    0x316120c0b13020f1c02040b1f0e01080601020a03050f0c010e0d0201020a08010f180c020c040f0203060a140907030b030703060c020a0201080708090d0c080c07030b091c05090d02150f0a09 82
    0x1504001c07400705041d21740e2199500c5003a4100d03000318180c00e000002c9480c08200380201c20041c03043e2a1120300d05504105c415112107000ea130b80035610364030040120703603c103250710018020900400c1410740a03420302008040d14038440001103903c000c200c00c81890f01440d800030300c0047c2d40c04035580340b0f0150700110741e03401000b8407a442c407417150521001d242100d25581e03a1007021541c444410300720a000780800424890f00034410055a10300d40c04000296000710343c624894000d001010841251000440c1031009010301008601ea81e00c04066004252016a10b58184030b0382c14000b0010b40f060091295024840d8017801040c1035510000d084214060010000d07c400c001c02c006071a0400a4500711030161031a028444911a00b410b07801403144603107116150103072031000700074003074505412402844243c088800840768881d042550111b0252501c0005104000b40b41d00e518005916054050000b0b012054050303204400100960000154010760400450310040058104030f080c0c005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 482827562 1250 482826312 482826319
    0x2120a0c061d1e030322090c02030a0c03020c03030f190806060f070305120a020403050601080303040c1412100506040e0f0a170f2107020316120c0b13020f 68
    0xb5200d02d8071032844010225800c03802203007000c8001441e1a858001c00f018080083d00380c940d546040c0ba14040c19001d00d49200b0210fa501900004001141348522800c2003a01d134050341c105040c8080496440c0c03000c95040d000c5214003d01181030743d8051009101407059400415660f410400014000c0c0500d24140b605104502c0c007080481d8445d0801c843c810b40c5080d001070fa446100745400e68050150800000d02120314000b0880c104006500400076a4012012100c0503131313032120040d07a42d00c41203134000e252a01c111400c100001c11711a01c2070b05003600422004400307211400081c0380c403420901840303034140c50310705006031414144180c2071842500f101500008030704d1031400755142c0d0003403001030401c1c1008580d149110344810030b4510003078541a049588680f201102441c480c100900510407105c28000f04001c1400081201c4604100c00c1000c000c120b201c0d160f4082c0c604540f11a01c0c18040944003540003d00a07500340c07445025a5950221200594014041c003901a488031501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 482828812 1250 482827562 482827577
    0xb0405061003050c040f0909050c03030a09030611040e041112370f0501020408010f1802010e03030d020d0e07060311120a140a09020f0306130f0f02120a0c06 69
    0xa4a4907060070005400016080100d42a2100344040c0c80c1d510980e40035040c0302c80049804940c0b4070050b04100c1540340070b6400c071100c1c90064030406440b44a90b841c80d001142200c00100005805034100c14030010660300c1c401d0030039694a10360340c2c18100807107080f1844400350592903403030f10309040000c1d51003060700008c08034101c8001640949690320290300150924040301509007054801c0202c4100c0d0307109074000c14551440c03820a02070b410a001e0b60600f0b50034400700c0001d006091242d407081c0c076259144034100d804076400641d8200e0180d01016014002004008a41d007003c1c00103180c0745081d204000780781d59900990500301152608005e04040c01c1030b007034030003168503141075503100390004100c4009030300da2503101d0004040c0440c9201d04850004200465a409a800507407203038029241c1d60039070501001010303200e0304201c82600c14800c82d5164600480c02c0052146103082c0300710304c0e0224424507a000280c5400c0d840d01c880901c0c0d40304241240030030541c1c500303200c010509400d1240707 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 482830062 1250 482828812 482828821
    0x1060c05010e240a0e0708060901050601020607090306090303201e0901021507110d110105060d0b011202010c1406041b031e05030d0c02030a0315080c0603100801050f06040b0405 78
    0x74060221603d000c81d40007600c804140c0d040c29903840035400d9280402210b1016a9a404107601d0382d804854000703843d445c14000403025400414050b01c1900580c0d00d0050041c1183e40b807a008001005e0181d04255a590b0700440d1409184001d03440c283c425041107032203400c0360005040040c0c88440b180c1440200340444040c59800085d01911b42c1c480090b078802c542d580724030841d0480001c01180c1c0103480b4120481d07086030b0300003410610383c2000c1c500a01842d03a07000103104840c20994002013580c41840300410603114042e100ca01480e1051425411100c3c098880c2c07000024049040304aa400410a0104100400d030f4940c10001c0c0729079505140780e1568503440306200c0b107108452100680d02c00c06201b00802071044600300581c0300000c000302c16102100035a00c0e0018400c8034046854404105244a080c454a40481c1d8468005000400301c03c0d09001b03d40e00f014000d10314818102c1e50101e80c040c42805140c2c4121007407034104803180340c0541000107071040d284480b07004d0b516020611 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 482831312 1250 482830062 482830093
    0x904060f1113050402070c05040504080717030103060606050703120c0207050a0b12010f031a0402010e0301140103030801051e04090611273304120c0314060c0a0e041401060c05010e 79
    0x7d0407510120340000d02c1e075072a030818030300510030224000d04200c50402130503003165844016506170790041c94100002a214007050f1003d02c00d540c800740c00715200101505420040d03130085038041c1e005106035000c0c4c039510401b2a801200b175402100c0101804180b02c900503c0e0401c1150062010f1028818003d145803150301c0b039191050180c0390903103001e10001d015640501949462401c024008209a0071200300707008900500380001c40025411784000a0903107080c0b0701d1030441070013103402e00b020f1340380c008100001007011040842c0c0307164031040c8200c41c9201c208054008001c1103104560400c60a0b10803855002103203801e1886060869200c0142c01454074407880250070300c295079140e0307210407c0c4064043c060740d8412100300242445640400c803051080a045034407681c40462200d2803a0000342d00c840080b510303800c0d40c40d82802100c0781c4611448010341d4440700a080081c000b0b04103c41d0944000d03098000300d0104400c42c41d40820080e00b44200d00c0000184c0c0e0150030b8020840080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 482832562 1250 482831312 482831333
    0xf05040314210f09060906071d24040e0a0c0504030813321f080c07060c05190309030801050607050c0a06020c090a060807050904060f111305040207 65
    0x15810000858481c4003074145000c1201c03002d065400c0c9056034a00010403001060381110701410034000c100208056a800040c1ea9001d058640c4501030104039850110301c01a01c28000309600c010400f80d600c02036543c60103e240940d01500199641c0c60400c0040d1324242d202900714851503103030a100c18051a409801c0d501038960016100e07648985030b0050000e007030007a030484a1a10141074030030614036a01c0502100c039500000c0d014030030940c05c0c0208040450f00300300c0480c1903010204000e441c7c0c0d10030301e034030703580444410001e60030300c01d0a03141d0300c0403201d65042e039402140000521014036003500c000601c010400d490b090140e07090390ba400816603101132007668024200800c0e080c003002f60900c203c40c030056001d0100c000c1d065992000035600d2a035851f2050003950f80fa4003090807690349000300701c1500c0200d0b00800059140c10280701003103800400c181c88183d50342c021000701d403202d0701801015507034010603d504e03640c80819450302c003000c55112600c528410450340300050b148002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 482833812 1250 482832562 482832587
    0x70507060c0f030f050d0e07080c01030513060c1e030b0a0909150c050c01050f100503030414090c0d1d01050709060e040b2205190c0c2a0e04060f050403 67
    0xc0c03440c02480980c20545e110300813916034502c0707541440e01d9030040c07440014000044800c000101c91600d00200b0040d03044413425500d550b4096940b240d00000710f203550700030740c0076500d4502d00041d4106040419081152229911000103511601038030003611f4041051409002004d2003044403032220b603503601031841060044807580c0c2c0c42d900400d6840780280d01380c80c28107484038001e200f1440d02510f03283c4900c5085480354110040f04c00d01296034100001540c0030355541024034091200c000d410451403100c010009104418100000f00e19840c95001c0d16501c5081080d800345012003808a0340c0c04e440d0300070004020003280e10810400c10390302c407803100300781182542e000800d004407101194980165600c101d45003014200004050115035020522980c40c401c5a0142044c00b00c64440039190070551410001d00082c1e01000811103408007010b940e19050507040c03a082003004e80000c1c450007580101c0010400e1030810040c420305005594008100410401881c9803654010748200c6000c2c0e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 482835062 1250 482833812 482833817
    0x140c043b2a030705070209040c0518061c0215090d060606030207061b021f0603080c0601090b040c080402060c0c09190609060303050426072c010b030115050f03070302070507060c0f03 80
    0x104052050509600020b01000751501c20343c814a400c2c610303103cbc40d054420b180a015149601014407420745103005010b9802000d010300311825a500c00000d8000c20308443d8040c0b00c907004140040d00510484000380003545000d0303214005400d05004413405000201c0c80c0c089001d04580a2942c04109a2040112445440300e076003640c40311640104465040200f6110300042c1000440c40300007449812108403000038081030640d44244002e50b0301c01e1904501003105603020a00600c0c0c190003611200304010200c440c1c95050343c00140d40d6020903500e50b0b4600c0300789040d0103e00d1100340282c1024210264091040900c2d596004140740700310b100320303800c0b0141110207040481691201a00e01800c1c00c003180d05190b00c0d902008008d0b0046912407070761545240e80c41c803d100010a019040b21000840503095070f1800c0000946200c2112001040180401801e00c0d04201031025602511680c0d900680b16000c62401d02e2403d809900318006201186c1d0082c2c0015a00d00c101c6400540e061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 482836312 1250 482835062 482835079
    0x1d0907050d0f020a020a021c03050a08070e130b0f04060308030619090e060604290114040e040605040218090d0c0f0803070201140c043b2a0307050702 66
    0x7580a1002012000342d0a5441400000d504003526400195451381e07a0088400d000e030850103240d0b007805c4041c1a0001000f2074010301c400351019018bd021030358047c016050a0b5058030352000024071083c010040540c506540b040d050203207060000740420345c528141da0030045a03007141c079103203080d001c024407075440b5030050b442c3c0340411161701d103a01000308010239050081e043c0c0c034001d69031611b0301114a03d005601e4001a1445c243c4000f111312520786500001c22040401030004658111f0242e2003d40c05503810040017070380b103014000702c500c80c42c003402c030020705824280304210054006842c56442c43d1800000e00564001c04642c000c03881c0c1c100d06200c00c0c010a1881c02030105400c28a001d021484003200b000043c0750113402c110220414209000790759074592024040e81d004a02480001003a0041480507030700c1c0400003d5007500030b900300a01000b680c00c81c0ca00a1843c00c0302c0450540024108050703120380d400c2d0401d008000c40c00609415454503920003449405803400c00391290424 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 482837562 1250 482836312 482836327
    0x30c1815030b0607050a0b10030b15040621050d0302030702070b090a050d06050703060e2e1e0303020105130f0b0601090e07021501080328020c030307060504031d090705 74
    0x9601550303080801403c020348404143c20803507251a20400191604801540010154020000208290f81e0300c203101101071744034440c160f056500940007041d0410f580384000715900c0c000840307441e00900303400e443d40300190881c60440d0505a101c0e405405042c01881030104207038001c0717101d500359004001255106c01d00d41e000140c2e07104840c6c3c40713190021745280181085c0b003810f8100c07500c61425518284070007a61000e448100001c201e6022058906040d001324203651402d20488481d55903070071000b54640c844001d02c41106015601010840d0310110400c01c040c1c0a01401d58015202c01410540c079100e84c4031254110040c0e60010f00c82c41c500c3c000035046a0203840b001c0092714505021561915246001a60354525410039070b442000e42c0000041d410300002c00c49a000030011880f01d45a503507410001e5010b00107031303154410760152450340621910100040e021441c010080480c6604207414040c2c10a0415004a0036042159480c2c0030542c550100b4160020b0151070150350f00ea00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 482838812 1250 482837562 482837567
    0x1e0e0c040b070c15090905090a1e02030a120f0f0f050426120333040e070308030f190e0c15090607060f05090f071211120706030c1815 59
    0x50f40d0030141c0d604086003060701d5115801603000d0181c0b010b030801040f40da03c890104075990f140c840802007003d22100044000b035041d4a213418103142c405021200c0c0342c2c0e0b00c0e581c0c03090326040d00750f030003000200c10b0010919516031021080030b9140050410b041100c9034108018900e1250b402805100d607144025060080f4103407404001030a0510155000007240f0540c101c807030740c41a0341c081139190b040c00c0304038400800c002d2109039000f81171140b0030900e8586c905100c0640114403181901d40100d00300000031411040c011361240481440d0b45180b490030b2601c018048081150041c1d8091600c2c070308100e010400640c0381c03071051041300e0700c9000e40d00c1c241c0c500005219001e681d981000700812a41708010031741e0025110420440014089542c4404404c0e64515014403130910690101d5800c2111002203546044814000c0403680d09189492022400c01e1a00003024403440d0b01420041242c00d51500c16220404082d1070803400c007042c0c01a00340055402c500a4100450448040d54006030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 482840062 1250 482838812 482838833
    0x114040b16120e0a03020f030f0d11130603090c060f050a0c110a0311030c220b040605100c020301050c0f0406031e06060824090a0f0e0303011e0e0c040b07 68
    0x2c1c00558140846145600090303104e0403400700481c00352044030720b0340c22021004402c6e103d5160b1040310305070801e603c4800a4001e814040c0594900090030030249140a4500100758080d04041d100071512482900e4030809a0103580c0c0401e00700300c60300e80000192580301c0e04031a10310b00c0d03514045800c0407441c106001502c9422081543c0010100c41c000704003c4402c03641a6003d1044050702c0f41c40980c034050150402c040c0e45150000e104130400e42c0300501b0550b200d40c5d00007a000d00006426515480860f0a40740c404c605800484d8001003144114502401400d50000c03550790070301d080143c40d403510740719409240142010300d40c454130590740070b6030b0684180180c0c3c000c80700148449030391a0f80240c140c10007910600141c01c2156032108079182d0310300c1c640c4402080508801c0280d612042d10900500c107074003079801d80c161110400d5038886420400b07507010700310881410681400415000c01010702c69400604122094400c1000900314001594201c034404a055940e0b10081e10b090861131 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 482841312 1250 482840062 482840087
    0x5100c05010e06090d090f060504150c1b05100e100302180901120c090c050a080c090d111305040503090d050f1b12010b131125050114040b16 62
    0x503c07409040003180c6900182050180c1c805482d44010541c0f140f000f21802c450340d01130180841c90402c800c0001a5524820075040074180c50301c5601c81c801a9941c80e20412039202ca80145002800184010714002c0d900c00c6600401d0f00f0240351840300b15010a0841402400240c14540e0104048980241908003000108030003401040c4640e1101c02513170051204c040c09031983d0078100000326518603288120107034400d954590500b400705c8204111440e2000a101e1200400b0030f0003c061107840354110002030b28814811441c19130189070a0020881581c42d070741043c42c3c1014180408120048229904050b00707031000011540c0908045281c0000c40000c001c0310f22640c04002c0c9500c8805042c9504c442040300d83c484c200c4040c1c0800707400d030751201780520352051090a00c082d00d00e0250b44588801181c0310135141c14480600801001c41035030314550751005108260b40400c01c14203110300101c0c1c200c415500700c658246916000c070100782c018044501c0490400f4032002140c000c001c0c0c0481d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 482842562 1250 482841312 482841341
    0x5090c0d0b040b070c0b01030b041104050403030b1002010b010c0206030901060305030a03050702190b241c1b0e01090c1403090a021305162102030c0406090f05100c0501 74
    0x4020180c074241c20103030812a0140c4400360024045040346106000c42c4000c03607001605000281d09584810014240c06042103c030072408511074445a00c4070b00403a803085001ea00c0c0041c892108405225a01c01c0c181c40010441e4906a0100740c280e800c2501e502c907007901603421719142e80d0348801f45801001150006000c80c4404981100000e9041d046a803180c060345d400d035021015149090880310209079402056101e40000280e50307901c0300c15000c8000a42c040011902c0200040880c4905100d5101c400c00000c14600c107109102004130a03810101c400c1802e910200e291218038070800301c045c001c1c04141c1d500c0344101c01c44a4070480d52070032212110102259203040c00e90301c81d070740c446070f0000490040e0010314140d60701c19664410b1912a00f4070704003c45060486d0300c4100da00403001261100b004201030078840300441035201071403103000480e00340d41e5200d0420401425920b02a400520350a246881c01d200030b85450200c0000d4078154106091001c03000c0c501745004d440d100c141c02d842c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 482843812 1250 482842562 482842579
    0x3321c0e30011a10080717070507030e0f0f010809012705061807170f06010b091504080c010525110f010c050604020f0607050106060e010908150a05090c 67
    0x40145030340407510501d020030340003005184602e5016180b04550b80e501103a120321004a09944e181c090300d0002d520090b281b034103002001d440512158007010a980b4180000d002017849003c041c1c01c0a680c50381d6042c01ca540c8441494140001150010062016410007a1003000306090900035000510800005900d4000d480798141545001da501880180d03034911070348001c01c015229440c0d41494281c01107000d00700c40c60600d41c11541003041c0c2c2800540a00c43c08455004034202440400d001c3d0842c40c01c4a41d0b556411410454040f0300e100c900c88199008000c1000100800100b80002035020300b00186c035115484c0c082d8000d00041c0c5411480c0012510841c81082110042401000c0d030032100c1009107442070004443c00c020804009003558040004140949000222080700c2c400081600e880e00480b03603141e60130364401e940020003046031801090100c2d80c2150205010b481c40000401c4586244103c2d540416009810f44070156500d0001c284070000901c80c0501c100c001905060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 482845062 1250 482843812 482843869
    0x20d0c08010e0d0306050103020313021905040212011401020d020d21021306031508100905190606050108061f0c1407060c020a0b0a120b030703321c0e 66
    0xd0b240c43c01c100c00e07800024502540890030758001c3c0f0980707000780d180030141104529a80d091000410103d25111800c40d50518000f469645030700007040c411418a600308825490014100000d14040356000d040d9000000721a801913800140b01b00710301010f01d0308030000008001142c00304e4030061441c6607003a000155100c500002640308504440f2982d40411640ca00305114807170507007403401a10707001d40004030580020790860300464003441c000c405546001207494224201040041c0c01101d0207508c84100304015030700300600070b5116102780c48651081858503144400c240c2c4603442d110030300105034040c1d81030205d107100f02c0c0003007881002210340890319088041c2c403000071411304078402c3d0725400000c1000041302d000c3c1c0e0a80413454403845140c0360102c12030005800c0300e42074030790140314000001001c0340044240034801e021383c2083d01c0c06110070805483d6400300104c80740005070f01104600c1d903182e50030314000c44004228500b10081003500400181041c13082000310704102c020200c2c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 482846312 1250 482845062 482845091
    0x190305010912090b071b09051801050c1306200f033105010804030e10031a033c030f091806060d0908070b010b1b07050607020d0c0801 59
    0x50700c0c0c2902400c07140c9500410508100d401c00380e607016003441080b091000d88002480c080f8021a0f0041d560b0034800816140c2070300c10304603503044400c003000000c1301c54603100130f101c00e03c2141d40001c203503c2000c2c034105408440b100501694071905081081e21030309602c848405000d00401400004242c07207a090075075002565a0700446594420700791482c0c580a0071211000580b0303002d1140d224490602da1801e001035404050080c001e030103020400c0b0000c4000c0c1c0d60200440884819902d00040c035048410500301d90303106205c1c0c0f0f00d0190b400320006c16010500e9241c4000750700104820140e000c645192080e4050f00c000e076903411184804541000c075048944060b20420300161460440b14501a011312480001601c00c45c0c0c201c6020042d0000c00c0c80d864202c801310501599a00307240410f21707078426400d03040903440350f07401240c00f02e40d0340c0e4600c5144c01075003841c16502000381302d41420000043c4c030034400c9035030003403254140c0d801350801c100c0d8002c8030000414080008100114161004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 482847562 1250 482846312 482846321
    0xd03020c1302130e010f062106030609111c0b0604090507141c11090c1b0d03050105150d09030e0a141008090c0d0c090906060f0b0703020a1119030501 66
    0x203003e018501e4a4049107094180603040d0407030b03640f000c40315050b41ca800c02c191952017007030310140501618401115a031618034051400203520600c00024001820308190402c11503181c104e42c40340c0c8441c02240d1403100011881010140c002441d20190b499190003c2c000301801200107040e4000d00c07500107007a5540700001c2c0d982c4d00341a6002803035041688900d00420060721740c020050046602c5202540c101b0744521076100207514559450304448284070304020700e88140d400040e0384003142138182ca903454020303e4010b10b0281d48156201e408100a01d5036801025200384140fa911503035401411b00c64020b40391f4000c1c4c040d100c1120162030b140300e882a01c142c660405e0045844613491085c080c440c40725144103a10300c02c09442d010080208020f030791001143c040c4c88041d03401e8404581c00150b0712078a4815482043c0000b00301e8500101420f140d00f0650124511250074082100429004515120416403000c1819a0800f444002a02201032a003101c1120071500e03038080208901581f1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 482848812 1250 482847562 482847577
    0x1a1e041107020a08061603090503070c030803070306090c0507021e090106020a030206223c050106090605090f0907030f1a09070503030f1321140a0305090d03020c1302 73
    0x100f031420540c8031503141e81d8580c41514041a43c2100100f20001244281c0c44542198070038015285404119140d110b0201125007054401100000920101c95054400c5030010880300b00140007410700240c000c1c1560144000290244822200c213042040155031840b00e10b180050a01c0440c0d61502c000a550f078905c4038044016104110200c0c06102c55008130203141d07080c43c102003500040765965031150084c2d10031481d00e0300f4109021650003461821350241031071514800700e4030845480c200340342510041c0d8482c15826283c0301e4248040c1e2035110b030895110312240c01c44044c945840c41d25a183c06600c0d4800381004038000031b4203041260030010803030385840306107001c42651155a170841c1c40d540b0f54801c0591590081086004e1524070001500828001f04d60034405181e0350481044503a500010f01e50401c01e40300040001c00a410380c40050800509000740403480f01e50382c0c0500980b2030306543c1c91240c10a01c0007a41054402c10245550010103001c0c81c90426074002d040c0040d401c0902c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 482850062 1250 482848812 482848819
    0x403030228050607050a030f0c0f020706081501050f0c010501030c1805060d0308060f090c0d110c0d0e0a0312110d03090b040f03030b0d1b0501031a1e04110702 70
    0x10050039410401e1a50410441d800c2009402a41c83e8900c0a66071684813114004c2495110b03007070070001d11540c0c81507069030b0209443d5030b130401685110007070400d107450b04a00e05001c040820701c440341007035511405103164203080280d038078018800c040069025510340c180c00c0e582454004020040243c40d400c00302e400721a20711005100181e61070094600440303185401003441802c5002003880340c0300c5d041d041840501201d1030703503121201262550008440c403169001e4001804407a1403014410544072200507000c05052007003000781107403286d450060100401c20704101c200e240342d64540e1f80900455002e00407144e40d00e6681005001c0d40d151906000081c06801046849680603020b40450268008045200c0755650342d180c80041070600801d80415650b55001021601c0d8212100c3c0d210f8020b0590100119980149606240c0310780c11441c109070401c00c001d80e44d02c0e40015020340e0117104032040e0310b115040e604601054a02c0b8141154441c2c00c0458050038880c04100500c103250081d03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 482851312 1250 482850062 482850103
    0xa06051506130e130206030f040303020c03040f14010201020c0a0305030703060b0319151d04140619050a0605010e090703151203030608010c0e090c0705011a040c020d09090e0109060204030302 84
    0x2004c4080c1c0070503242d00007a4105000b000000c205951100c0d425074054841d040050030031030380946640c5103400603049a2040c41200206104c40080b01a040884440c240300a42c548070805d54060744444c0150401030a005010012450050003034204601130914400010344031300c1c0c0900c0d040e140ca03d49406c0120006d152202c840719903101250002c080c0c501202020804682c1c400036014403a0004000f0f842840003030383c482c030741411f05200c030600801c500a8400800c21f0b001600380104d500c0600910340e880e1601c0010083c0b41d80003901d16091a40482d012021030b52100f00c03e402a2a42c0e000100c0c40070b144040102e507040002040300d00705402079408000c8240c07110140c508a50001500f1000310b41e050460b501117280800c0c2c0640d000d1013000909080001c1503458900752903d1001040e5200e008041d07078501e0782458814102c041c00c3c2480203003070180c10400040d014590501807621110380b18840c040a00d082500f0140306603500400455885990b410021340307540c0b0140d4a00c1200651 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 482852562 1250 482851312 482851321
    0x2d0102270904030e12011104030507051507020d02010503060409020a03121409030307061e14040b070c02091623180d1703071418030c120a06051506130e 67
    0x500200c0c03046506071078002130445407a04102c0343e104034440043c0c00b50340b180ca40401d481c2d00c24000d0030095220394005c0911508003010818408460380d50507808580c2030106101607078400d0b0001c0e004540a0a01547c3c0b03485445c00300740a0100340001075080f00f1441400803c0001d01165019070b80181e994006803900445c094480074490a021103034035900170f02260313000c200301d948041d210040f014940c0945969600f09042a10311783d5940c1d02e28101c60804000900940d00c0d05070358019014603103203c0d000030580c00103458110150841d1090640c400d43c15101c0c1e03009004d41103c0c0c80f01a15114281d1554903410384203540105c0020f0303000c000b00e0000b0b45030b500b0580013000820790b110000c864407500c0e05c1181211608010309050820190350a608480c640440c01040000f60a811281c04d0740c10328400d061514200d440ba0038041c154203006590003200100e04d8181030355001802141e243c960400540e0104440c000280c0d05c144001070341c0040c42c280424110803540b8042e0001c80b030356038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 482853812 1250 482852562 482852569
    0x90a050d0317070207080a17041805190c020604032a060227010f0810090c1206140d020402070807081c0510030f03050a2f07090e2d010227 61
    0x1762485088a00d5100540143c000303500700f0803035281c00030701440c1581010b82d50151001240c1c11000303140032280e99103007888820a1030703010050701d03024465400d110071551000c0c002d54a000050000c1c0420000d00c0c2d0085009411120f82000ca520008404080d02c0060504100960210002c000306e014007000850341600c2240704014880c81c142c580b440a828076103025100000010201580e50408c0100480c2c2c080c050300c504221550300b560346501541400c50280e0844a49400500c02015600d40b280e0302c0ba070f40c611008032000e070306403005a1034052614240400d4045e40200528500700881c0d04845011800144180301c0d001c520180055240e80d24440501203880c08042d000301070b2000d03004080b030f00520040207a0380f000c1c980042c00080004815120448608019481401b04024106500b0301080031101030201d69004018007130344507085699a1403920304c000301c3c81c3c607100205000010544240302d12021518025036940c8a4182d0008130540584065a0700c1c07145404110700a0a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 482855062 1250 482853812 482853823
    0x7060302090a080c10180519150305190902010e0a120b0a06080a030f0e0a03060e2b0c02011803080d05010b130501180305010e0d02060601050c070b090a050d03170702 73
    0x7134060055031059012100444039030048082c0302d2144202e4800c001b1b201c1c1c0303072036070495811107800111904560403c1c3d420008000110800c004041c188018007404001c4034a8030b030aa25aa1100020185c0c0035200607207071040b0740c107000c40d40200c6d0303804005000702060f0361005a040c840e01038481e40307a807501c940c0710440e07800740180721442e8042e41d511030001e4080c0a00203003401650030503c05407064100010341d40151a04111360003620340e007440c074100c00f0410001c041407009060502c143d610180f00d401c580e01c14401c8a42c100480c4c64030502c2964001c29002c48144501608144225202c0c00e051303d0baa40801c0001c25810307d80f07400042c240c0005400c1da4050006562500c0f181807504004503903405941c01903480d00f804449002000071000d21560300c03140707105c0c03000c1c20441100e40340180c104030b8010301090500000700003044000c0300102d0001c0568040e0603503152250031043c0410b030f21031202d4004035002440760965005060308a10380040044001e51410f0b41da40e1200c07030482e19078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 482856312 1250 482855062 482855083
    0xe0a0302030f0d0209090702010c09080a02010509060f0f0412050c0406050108130804080f060f06010503040803180a060609151406041412061006020607170f09010e07060302090a08 79
    0x50704140124194000c2c0180104a9800340100140c00d100c21400002c1e801e00c01a100000547c1d03550200c0c064003500550a03000178920000a84001849034002030503e00c40c40401601c14000042d08511000f081026202194801c441c166100e940310a082962411800820340d0300e4032500083c0380343d610302800b41c44151107040c0d450407001c1c0c90301c1c200c400114040b840c003201e80c82020b100220b10380360700b00003d1800c4c0c0219001030080b030501d45448001c031f18024100504005c010400c00000ca0001e608a07a040b50507d0340382803000a41d1000c10703003051900700340200700505004c0009070360707096078200d540c41c4128005100205a03640c2c05400400309c1d10307550150080010301c801c0250001c01d207110280030b94007905202e110341c0600c00312810300b002190031a84c140d1085000707001d0594100440e40d40300509003000c9040d44107030744049450303000003000e1106c80d01c3d21800003041ca400a410464900b00c0403012600c1c61511440301602a4201049403805400c03540c0000a00c800005802c0214 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 482857562 1250 482856312 482856317
    0x30e06150d0f0501050c1c06030f080c0a081308100605011e05070602040e3c130209040c091503080a200f07210c050105090307091406040e0a03 63
    0x80d9040001d02850601d0900c0644000c030711416202c000c501d081c000d0921403181c0b10b034183e0303442c1041e011901503040904e14012507203250480030700c0001c01c02400d1444058000300101d484400325845107142c0f20114a00034039079a000309030b44a61903400c01c0e0501c2500d80070000c1c0c40b4000b001da64000200c03000b512079180010b00520301002c100302c00d4801c40c11a031003e40f92140c908600b0b5100c1205907030041c1d0200902c503204604111000707252504400044c0c1031600381441102c010000e031a4622a1404610640740d00030010420090040e00443c40e002d5014010846619003420038140390f4a044c41007221035410500e280844d194003c0c4081c040e00c1d03201c1d0b1298245145101d048a04004852404203240e13000400d40950480c200003000c60503040c07400a280107400d00c3c40030b400180c0341c11541811070250000610004e0003007642041603510030728085880b000d203400064034000d500e1340245a120319280401d68110354061500e4400c074015a01403040d00c2942c840c103950b030f41000001400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 482858812 1250 482857562 482857591
    0x20103020d022511270a06120b0402040e030c1b012a33050a150602010902100206040c06030b031e0a110f0d1b081c030e06 54
    0x5601950203009031205240300103003001032018400003800b56000008030a2a164500b000c20400e01300e030751041020007911102075150301c201075040d001e581c00003241c0d840c20f405000181c1c00ca4199100000400d10708440411383c01c0d0a0a184858040a0b60144e001d1800c0103141441550004121408483c084004040c0d8414400c501107060356105622030400c40b4601108410801d1302e41600d000016011000d44902c6032803816003c4c04144050f17112010340c0240441041c540b804800a0000c200303450082456a6400d4180000f4000e002c51342100c0c18180e8404075900f5415401207004610a0303540d00c0c46c460049406076030303425040fa0020038013107070311a090083c0c9200340c000300a5410060105c540c122600d60014000702d00d1100d142403203038000c401c3c610901900204143c2066001d84040062400c20008a0382c0191001006043d10f40110500c1141080540c6213400609400d416a00e40c00030780c404111841043e01c0c0c003180006c5c140030144100c10f2000c96694082c03d1140018503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 482860062 1250 482858812 482858819
    0x20c01151a0d060509011d060a2d091b12020726090d030f0206160509010309080c07121502090102060402150c010c020601061101050606070f05030412050c0f01020c0a 73
    0x8203a540314801032003015845400019090701c070441540d028009040c1c4290360000340402e907a85101f0008c000314410040c0800c10042906124240c544940072001107200c801005a50061226010b600c040451840c02040d100510242d05081420103529a60500d040c940a040b000a074000c060000e0140b00344840002e6480031051000150300c6c004c80001030900d500840050521000761030144d0208030081c2d0512040d5a0600441e6400792040c0ca8280809040582c01031850043d002c604d4140741e0380ea00c411003404204010b0301c1e041c1003c807084914560b101c5158000c0742c0070050f4100c4651490074100205000a030007900ca1000c01a030045c01155915020054151342061210340184001c004080e4140d4080c040c4244100103a001810594502440141181c240342d2400700564505002c0c0641540c80408603407056401898181081000d8100715007140b095174000700450b5103000055040010220301200c294204070303003031031091562500681e01c071f4010507100c50b4000660300d001e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 482861312 1250 482860062 482860109
    0x10020d170f16020709090807020a17070e070203040f08030c0c01050301032411030f0702060106020a0302060a0c110a0c0617041509030306050a080304090c050c070b07060f0906020c0115 81
    0x41482c0d407580e10407541d48599805c443c2013141d1203101c00396002c0d0300001c2c00a05500340144030600030078504604a910310f21842001d0b07195107050065810f0f410078107020583c25031007042600c000e041c6003a10200b405580380c1900350303a54044058a000317030051a0344020700c1d6000700150b9040340d0b084458a098a000c9442d68541005140d00818006694624403003e50304c240000d540300d1113680038070b01040d08202e21b029103480c01c168850001c5511580300c00380003d40c00701d56685c02640c404e10200c1c84900c882415203141031521074400070352241e04809024802d40b08103041c12901079440310f82807800c003420840c5050304101c038090101c286404040d19140019070100b80e0315406840c00007059610b900005400d0990f0703034080c0302f0a6001050500204035580b2851802d83c5040c149036162607070450703815440d55094071640503900004103154081c8421500002c610f0f42000d1400c00030300c1d083d071501100035042080c6441035586801d1000c140312600c5100c100507a0f2420f880100c030f201402c803c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 482862562 1250 482861312 482861341
    0x1f15050607140307060509030a140c070e09030906130f05010f1d12070906090b03010b09070503130b0708090c0d02150d0f050109020a111f02031510020d170f 69
    0x3490251008100309004108175110f01800b80001c00041d55070707141d902e200185040003180b40c5021940c02044004401d00303001942c0f00c11140001140501543c58954542c254000c2e01034860f0081d400041c5c0b01000002c0040300e000f9103921008180754103884c1c81c01140c1110000d0b4a14003c00c002c150b849240c042c89880058220304003c00c04070300400f014400070b0a08045034040c0e550503403940e41c10300c01d010a90040616080096008000700c20200001400c442400b9095005202d00040801c0190034103071a51012960000f044141c0c03814034801c01088240111a0038100d03000d0004401d6041c035020040140180e0001c0c10000c680444000000b250741c04110500d02950380c175150b111a80c4241e00072240200190400140c86034155071000d4a03410045640c000c060b081254011b401d407051050a84200c3e003801c1c00103850340c1d1400c0e0b0800c84c1c0c1e000548856072200ca2006503204040e800140109044190f6954001078141c19540203400001a100c12816641d0744c000a030018150003032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 482863812 1250 482862562 482862593
    0x171506040e0d020313060e0904080a02190b0709120302060606090a0801060b04030201031508071a09090f161b020d050309150304020a120b07030c0306081f15050607 72
    0x400586585481001c0b4901156600600b0150f0004108140b644560462080090005d800e0a02e040300240002549005d0000c000a04058010a450003001d1003006403c002040300300c800d47c400c603000c0c28040e280a4049541000044017041c003c91149004801c0b02c2d8400c0e07040c1c004003201d403186001c0020a40040e210356070410303134070400047e100ca000d01461001709140c0c503407223990703a007140001400d844500c00019607050740e880c0d00b00304504000540310101c803090032030025404035001c020b02040c883c40342010340c009805002d0008a14412250b40c0c0107402c0055500202c42002030242d5005032803159000700740d01600c0604015007044801091101e220b5415203103000d000b40001160f1482c1030114130800039021080004500749045e103c00946030b0320b10b040010381c03126076035803800c00b10042c4034408041c0c4aa0004017144d000b40c20a1002c0d0282d07100340d175030342d010000c0598140603100c1010a070075800d0002c000200010074403480b05403a40644400d2500704941c80701d0f01c05650640c1b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 482865062 1250 482863812 482863819
    0x9010632030f07030b091006051806220f141b0304050a0b070c05100203010b0405010c05100c02150a09020916090b0403080405100807091509050402030a02030f01171506 74
    0x406095500040c40f03c04055480b850304200203081000c50305141c800008031685020f440e00c501407015907111440f07404000340450500760350395117810200b103e40403c1c1c5803050740d641e10f542480025090540011030b864100340317810000c030402264241d907550400e031006002c002800b10204801d1000300029070f4800e01690858004420b29581c010b1004400c88003580001e031540300304400c00c9024807a80000003400c903c15419035040c0110041c0d03a20641c4210380c10f02c83d10603000001c020040c400e00c03103079071410017040115194146000e5140c100d080e80318208840d0002c0010001040c2d4030030303c620160058100142c076550f204003400101c600d40401c100b030040e40c200010b00e2003a02c00c02000030754460010b0705e8031903180000740007551041c04884c000788060082000080d5a1251001c412a0b82c1450503001c1d42134440025101024142c00464100b4000420810306a40e260015800b0b46100116498503030713070310a42d811183d11400030704442c54004800f200c18080000304040e400c184000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 482866312 1250 482865062 482865073
    0x102010902030d020106170607021005071b2303040305060f04020105221502030a1e0c0b010f0f06080906070315050d0321200f1b03030901063203 64
    0x1070300040c0c0707800e020300c1ea8600142e455400900c110f03000b5485109800800d078005040318248aa40a034544440030300c110849541d0b0340000e07080034031030002d10141805404083c01101707940e0912440845018a002800c004000c400758259003002084508481d000400b80126844440c001d040d9001c0c0604142c0c104582409070002461225461a00310b40c00b080620b00c04e189444144034a03080200401c1017950402e01c0140c1c1d41c540c018000041c071000100100400141d1158155042c4054050162000c0000c1c1e0002c074268220440800a461200c13080c00315240c0e460f1021208503104450b411000e40100003c611000e010340c0004002441e494119446581c0345d90120700089941902500042d524110080c482c80400c500d4820b08201200180081d2038011301030101c00c1c04411088001d03c000140030500d080b404419601050301010f19009081400d01d05a6a290815510700300b86500e019800500c41c520200000220520056400d0f080f40303204040c04411428844400c1e05030080c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 482867562 1250 482866312 482866331
    0xa03080301090b0907110a110a180e0f030c071205120703020309010e030115030b100b030910110453070f050603160306050406030602041401031506050702010201 71
    0x4502a40c040d100b06a00055510ba103202000702080c2d025000d0010b1208518510039001004104521010b0300100c24014040c0c00d50049881c15150b90720131040c00141072810800b48055400104201000601300c5900c3c050010b03c503900c034418002c400050fa48014810048540403060001e04140500140c0780c44165106482f88681d00c0000c04500507000003d44219130741e00b00001c006098000d800800450000000c420402000340c003006d0176058424001039038000140000748094040960016100d0900541082d9141e480c000304461840c18070361020ba4481000d800d46086400503944040800f141d0b01501d05254000c0c0342501c0b44002090f414200142103404a4600650010078400008818030989003494540d40154250018440c3d0410042e51a90b090b02d41248040200e040310142d69082500181021380c0459005800c003a4000b0a0240d071b58080c01c11111070111203035000054000440440c3c118a08034425105402000d1141d9071040e005460b110344103000004401d240d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 482868812 1250 482867562 482867573
    0x21040b040902032706010b090d0c060804020a0806060a050d110301090c090c0804110103021614010501240c1502070c23010f080601030507170702061f060e0f0a03 71
    0xa0700101c00940c0c002080c401100e03146056148410300c4038034a0030000751140030302074640806124021070418040352011043d5a540c00741da036190303400003010000b1a41c450300a0140705045800b6403007051241d00009500300081502841100c0c0207140445e05400c1004000b036084c440402602c054095000e040940d850900c82d04c603150307010300352034210740d45041820800c0e104183d1000e01000580d40c2172000007074400d241e00403145d10034200540c41d607410f806800845c11004101515149090003801c030183d1040d4000d50685000305942c40c0504505401c03411350001d00380c0100d002801044020011030034500c5049a011003c40000d890301c1101e07100c01003186107540200d240b161201c892030407005101c080c400e03501182802e000e48088001800038101c500c0061815060680700c000145000e40f052105010140d403c0050a61a04080000a54a01d011100e0092403510144110700306550500c05004640750781e13907020100348400007030004002c2e0b13001c03419420003a80003000c0000352 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 482870062 1250 482868812 482868817
    0x1204080c19180b040b0609060405060f090303040b0d050f0f07110f03070804090b0420030a140a1a15040303050f1b0a0312050417072f0f030d0221040b 66
    0x2240b00c240860400403d000300404c540c2c007011118400c03201041a4041511784009550860342e0803204035881c1c010400d0707842000e220f00030715280d143c0030014000c10010302410107004512644031003001240d81c1d52201c14140d14090301c0c8104a44581c1001500040c0f190320a020140c00c41b0080e1864802e090407554070f0f64001c208215403940012406020203030070f07442084014581240c0034040c492803841110414081124204200200000052840d4600c0e0b04410802c0c10180b003000103a1400a02d103000500c1e24801c14807550001d0070402003580750038807000c0d108454843c150352415180d590b05a41c50340c000419032402c1c090a00224244030058803d40300403050030405007401c5204d900d40101030740003205040901626200038800031891070038201400e000c0a00c03400f507a0f1051070404042c6400f41003000700d0f0a40720340100c0f84010280c0d0707420b40022401511850500300d4041d08054440d0780d12241180141e20816074210329a000800902c143c03070078241c001e8074094807800d0310412075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 482871312 1250 482870062 482870099
    0xb0a080d05071b240302070506041a0f07320a051e030103051209030115140a06020c1c0c0b0d060609120b011a2a1204080c19 55
    0x10360701040503030502002048850b140c142d024072a40b8602d080000c00000c0202d1480104815807000c000080c245001380c1c102c400e000c0d04001115280d18051804264400d814418814500107600115504464014240740286810b8544d030880c200491010441c040004140c035108212145c5102c2c24299000e004000c65529566000c3e80c8490f404405c4101c54401c45035800400003c000400c003103103020a00304100f40c05501026075580c0c0700000070780500349580c250340d113210b864180054640c21039016403140782016241d103000c0c00d40c0c0315000d0303840e40c03002942c40750481c4510340c0c411800b04844410340442031140e0301c200e4100d5114402242c01d40c00041000703261075900c180c140020744c0c10590b040000c180103c5e0f240c410058030364804501070070612030010783d2403a4290030b07800448100706031044405030040200e040703110325071040301950984400d059070340240d90241c0b948041c4c4000300e030241c9520b0002011504403803000e00015001240340300664409540d40801c9090145840c001d10703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 482872562 1250 482871312 482871317
    0x2131a0706020f070b180a0f06060803180301060501170f040f17041a0403080a080a02092d011e0e06120a0e0c040615030b04020403020a0602060f0c0f07060b0a080d 72
    0x3140c12501e0044409000070b0202001841d071b420134001140400144490080e5001a1740b0014119526154024003caa042400300d40808108402d240310014002601254202c0091000c5075440005542101030449841c81100000002603200d5100000968106100d136441040e00001520303441d8440140d0340514850010014080040c4a40b000080104608038042030380f5240c039695500c42284a000301803810302c540d4100245501149a05071840e0035005446071034484100d04483c4101003c0b40c1c410301c2000b4042e03000c030440e5407007611020a1940811030790b007040014500e060702c21141c003601c1241d0128041102c20001c0b020244194059151481c0104084400348038050a04a44038022030240349050320811010103981151048140702c0e044c002848c40450300424040d21a03600080d4000301514000180d0a83c001543c92207601d582c022024940c41e81c4624159a01c507419171b480f202441481340c00b0208080c1e5110508050b8010011416155606141030038243c500350048003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 482873812 1250 482872562 482872567
    0x70b0304050c064f03061b020c0111121204050607080903090f03070305010207050304150302070c030b070c1502211312050c06010909020a0902131a0706020f 69
    0x41080400100698501c200d40ba0b41c00c06013002401054494945402160184414041030b030b221010030082c01c003000415404010200d400641c3d440010b658030003101d0b02403501100a4001075482580514061030345d018010104000d001124042c04182988101c2d0054020343d04942c14584001c00c0554980d040c01040d920740f600704036040850051a000a0014400c00c02045031004400c89981d05070841d442e00600c40680c0201e031421006400c0100150301c0000c0c0d00050100c000042d10880302d200d100c00c00c5c03c00503079004409030300820000800f80b07018000148000356140d1503c40c3d0118407441c000c110110700d500d550748600a20404501c90a0340060074004410048c071056503180c0c08400c0c10782e030608140c41207091102000e10080d120419445140f034903c0d10603021941003010380d004070b45103941c5580f52003000780040042240f14030300310503000603004d0306030080d14082003601181d2400d071468124001c1030000d078600380014220302001808001446440903060703421401040c4d98 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 482875062 1250 482873812 482873821
    0x14030d0e0a02010809010c080f070203071505011707080307030e0607080a271a030402030109020910060f2a020103061203050904111c15090501120312020c030d0e0a05070b03 76
    0x1007011302c000d0000010359040c1403814502c84d8003c055140c00803194070081620341d031224812401e60051520042602000d0440d281c03d4841d5070b000541a1420752510003a108800c2c03001e1a070398010307481144d210760014001c0c0008280281c0301c4140c5e06002030052440c210041e921a0300b00d80c04007840102003180346005106c001e466910b0342c00141c038480c0382e4420f00d0742404105003c08031002030340144c1c00c100100080071501d081d003020802c9076007d030135020542015210210300c2d01c06070154000188000d11150f490910071800424402e0300d0213429240ea25400d0000c9614403882c000c03c0e4145038480030001510001241107816182c0079507580c44d100d1500100304010348034060b907880c1000c0d0007802100c1d2079400c0380c18660b038104030300343d80080e6124145e03040441c01d020a6101a495519000000800c140c00c0d41011341d4980c030aa66118020b018030344010100c0c001d900f02c10381d00340e00601c144074071500e1507030184480380e1842049450800040d80d900c2e1500000c0d4000a4907000c0c0407040c003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 482876312 1250 482875062 482875067
    0x1060b0a0c050c03030a02100209180c070311120403030309112701050a1a0a0c0b04140c0307030b01050f1f180602030301150c020607020307230a03050a14030d0e0a0201 74
    0xd0341010f40481c09585007002a41c00203640d1071421800112855000a41c0b0a0741d649403501c000204d4148031a06001d403502c20304021058120450580c04100d0103030001e07004280104809004c0c019070030b900d03070404e030071a00c04800800046100321500d142d01001c81603a90f4543e010f1942003600c4620b4007200c03070000e0f001202c00490603072182d0b00581340700d18180b160856152051034045100c10341181c48403003c00d4101c0d44030303481c40c0740900050705c42028803050010b40f500712216020074108842501c2000c0051690354201440040c05010f10340300140450329080380400e0740c5c40d00040c840c0f00042c0000201c2d846c141c01545540010503000844500003020354a03601c1d00411140c005981036602d00b070381c2000640020003035081004030488a0004550390b9400765907940760058111600d0549400320201100400701100e00341a003150b140580900c2c0003100101543e03800340c090a000702e220f554159000c403070700700340c1c0b0010301041c4a03040c2c20700124490791070752003040d8000746048080350001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 482877562 1250 482876312 482876323
    0xd020106050a053a0b0a050c120c030901090b0114120a0b010504150b1c060b070c05041a090403080103060c08090a0f020303190e0306060406150f0201060b0a0c05 71
    0x22802544601d0040200d9039a0b611054003a030084450300d00c00d0304044801d92200030442406030055680c295130380c801d1108041900d4404c2516100401103a1221440015203028035200b0000742402400052880000b0b032000c0c58124003004004a410340707859440c2c1c4682c1009030001c040a4031511244032035803071700c901008a44501003000e0302d01c07075019451f081c181440500507217000700e403074110310400c071101181114014a503c0c6076150b2203400d0030080f0b06100800e80ca0501d442c03814240080342140341c40c01100c92a50748501544421131410342803001a100c1c111200182400807803228500b038564030043e902c624480d5549001030360462608400312826844503008002010080003602c0c4d20004408404139040003083e003003484648000382c40c5104140700c05110b08090400f802c0c0c11a08203041c0f10000504805840d905e943c0e04040c003089840a21590a003250704080280c003180c080d14203910051640e1002040281d00c0c1d40c000c1006500c000054030001d08464494014840305018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 482878812 1250 482877562 482877569
    0x80d1119061b0c0c0608040c03020612060405010503070506070605100f06090617040f0311010f0c03020c070909050d050c0a06022802070501050913140903071415280e0d020106 77
    0x2072201c3c158415803a00c202c5a03945000d1a8140203043d004542406084e03840c5000455005040c1c543e60307070551803081000d040550300580a2030501c4000700d0645804a00c03c41a1000600001d0600c03280b6100d2a002e400c018140504440034414003081d0780e5504c0e50528068440340d22480c503030600d000b900400d620320b000490100303e4491014000014006140d00e07078900d400d8a480213a9000e0b00b050140103128440e009c900c0340d4600b6000c02d003000e0300341c2c0250000c03180600503074000c0d03a52000240180c954240004200f80c208414140c0954028401345c01401c0c0c011046410107074159032103204980c8040c240c904540b02142020415540301076071030440030001d1000c2d08000d0321b04400601103000380301c00b580c46075150051100d9413520315401902c05008101040e6428140301c40059100ea0021409035880d2b441e072441d10741e031403000003004003402c0c0c0822040030842c2d8500285586a00c0d120b030780c3d07404010071b88001c0d81c1618851301801d140458540041e0085500611000e82110595403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 482880062 1250 482878812 482878817
    0x7021207180b1e01110601081b03031309020c0a1205071e170a030b18090d080106020c010e0d020301050703060f050d0209061011030c030a0807030501080d1119061b 72
    0x121542c64848141e84100c1a001e03014200c0c0d000e0548005803002c4c2c0c1000341d41281c0d449042d0001503003100003d05000c0c181d020076103070b108040820040c140c0703921550710341d0000d0401c1034004120885d829030080006406100590345904580d030303117800040d04490801c100040b00455030506020f00d80e000240d40d1000d002010302d40701011760384c4024010940d811f01c103c5080100d54840c034103010385c006012111008001010120350b0b5164881d9100b01610111154440c00d407403070030524010314059042c1c84280d0000c146168100c401114800c000c0c04603240c0100c28508844010380b800d00525001c0c01490314080780150406c0c12410f525040e80d030005106814000c080d10260b1202003003e604004181c5503401540c4d1607281c02d42d20416840c0d0000d0451000141da151501404400b81c12000346541c1d5900590301c075114100d0660300c00780154002a0051100800c0b020302600003001140002c3e01540c520082803080b9078800c0c548101c05540140e260b41034070700000103c544800c021070340b50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 482881312 1250 482880062 482880071
    0x50603011a1c020415080303011d250203040b0a0203190e1c02030705060418060509040c2304050a02041a1341030d020604260702120718 60
    0x8100040601998041000306646640e03001815929136401c07101c065007000182e0b00103240d4070444141e40c3c8c1d000b4403409964003041855091007207110582c11340500402a5403280f900c10882c0c5005004a64107050000c2d44001c01c40062007020f10320161844481c0c640246480e40b803440d0502031a040042540c5040000345810802150b96000d031000070280c074a031000c00700c5081d03880400c0ca0501e050b00920761024010500044114083d5182052440c04610502540f6540c0e401d1056441d07040d07070300620b0f010031483c00380a0314124108401e101001d0038118000e00101102150860794240c1d4081e6109030005410310600e620395851fa440001c0c02c02101303191019010b0020203038580307805409016214001e20240d00b90040300d0103030024a1810042d04140c0010703000a00b000312070080a03010b80a4002c050030300341c2c000704800d4030454002ca02920008203101003112900210801801884014480c0300d026072540300c14600c071001480010050b06062401c1000c001d00d500428603189802c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 482882562 1250 482881312 482881361
    0x1c1505010806070c0804350a050615031606020606040c0207050312160803070305060907022a01140301120b0f07051c09080d1d0d05030103020906180a05060301 70
    0x41c142d03600c050903180c5240201d41038906848540700d654480781c1e07064520343c86901040203008000d080c100000c00c0f46a0f4000d6902c80c40b80d110542c00c0806800342c0c000c80e0004501c2044d80d070b001250814020141c41c010f0380c05040e81240e10650382c228500692000c020042a82000d02c550040200640010b004c65450140040d03540e240c15452080301000104002c429507003458000c04074694407001c59900d0345802c1000600510b411503000344036101c0d82e00070500283c004a010604447c1c001c8446079903541c820010000c0a4010031003604015180070f81001c0a8100b50143d400b80540c81504d417500503007070a040c03120328030280126046100b1402440401034005040764400800c1c43c2508840070f0340481194000c10880e107014100309000104454281078a030b20000001040b103c1011880c04c0300340385c0d00c0e40c680d504410403022400070001880540741c1521041d0303202c20024940c1e0005520700c9030007055104282d6500780303d26290030a0007941d20f403e025200341c26224012030003a5010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 482883812 1250 482882562 482882579
    0x203070b011404140a0213141003050c0903070e060306010503120307120b06030106050a080a0c21200315010507020a06030c0c140a030201050f0c040b0313021c150501 73
    0x101841068036010329000980d0850321250040c2540e00b59900720003413186010320007400030b503100b00d003404055010000045260804d13450240e152480c060400c01032000207200c00d138000d1001421018811400340003110417660700700100c401030035200204034524208081418603084060f00818403d801c40e18001c0d032641080015282c1c070900610b803004c000d41c603020f280c500030721021a0a54211200200219000d6001401090340c5001c558134404079586050f1804119414011001c000a94a0706400704002085800a207075044d511030001e03c0c002c1c0d4504011508446110754143d1101c04010888200e51503060301241c03400a0904501c0e000d019400a008008030303000e40810706580e9030400e03940c24498540803180607070009000c0810501e02400701d58507620b141c0e0032001582003c00040c801034000350702900034080102004e00b41418914007400384d800081402040fa0f986d0350700d010260b07440540310790900325a0300300c0541100050038420802008100c400e41d400c1c0c18200100703c0b502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 482885062 1250 482883812 482883833
    0xa050906040209192a1d040207080903070e160c030f1d1002060108070807030f080c151003150903081605070b0f07080709080c150702030a050106030b0601020307 71
    0x15811a810991544c50440c01820142284210300c1c0300e070714000c07a0412210304140c0f109082c00b024281c1c0455001c0c2c010701200e4004555140860001e850666100d0509090f0081d011940c810100b481c1880c98050111346052000c0d40000c83c00b00300d150522a85016085005803492024038000d9003000e110b0f00c02a0500601c50b0102080040c1c04096058120321404e0307444081380001d251070500520190000d55941e400c0c01007544034021240c00050190380040c0c00e1044075440001270100d40560740303401c217264024032042c00207400740942044071032490034655440387c1c40c0d10381c09031482404c505003656920311444c0180740d054a450510408a40c2100000e50b010002a03d850a00d01c0400c070210b40c54001c41c41f0060110030101706011462444e6004640305a1240c1d651911941c0c412200b1500e941c5a44503000664120030074081050078858203c245d406280384d01586005420b074086881c000f507448050300d440c0d541e10001c0c8100070086400c1a0030031001d1008500b09045620307140d0005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 482886312 1250 482885062 482885071
    0x303060f062d07050d0e0406091503020603152d1c02040506060f0c01020c01270308090a150902101805010c02031005041406010b0a0e13060308040f0e0a050906 70
    0x4550100c2100d4080ca0408462072507a200055614428007643c002e4045690700641031f1180d0304000d0301058032200751107040c454028620305207525a00c0c5400744811640003610903c02c201c0d60010590550301c4071f119440840d40f503003160380381c041e0b84038040c4500b041c0901c0c950761083d0803451070104c0004110b01074820803601144e0010300c41d254400021560311804200d400c803800041078038419140190301810070085514020b005002143c624420700f103a0703811804007848083c1c480d41c800f080c4200c0344198444804411a02981010741319452801e2410360401145910b0360312076000c5040142d81c242300d40c01d107400c002d000403900c0d0784041c8850700c0a0113010704111442e040c10040d542e0402c0500702500500404000358201818009200300c006560052203204d07080c000155a8424422500ba0b4515986c0300e990410244041000c000c400c0c0c0c904c48003554480f04044082000c240081c0020000a01d0000600c0d281c2000491240001031042030400c0c0340208002c0914004282035522 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 482887562 1250 482886312 482886367
    0x3030e06191a040c050903060c030c07081605030f070303142401021905011401080307080313052509111e0702011218021c0f02010f1403090303060f06 66
    0x468885160305034002d001c0320039402400c2152128420350048003c1c00743c4481034065420350380e28a80705680c2e51005803014001c011080040c1c070007280c0183c000c0c00410302d40c03044007154030700c90741c41e240d240da082501c07a280d90200c0000c000c4101a0103124166541b860800440c0c140c0c9013880000e9a031613428031440801135050fa1055119030f10230303c0382800075031303840c1c000000502190600b24003c02081d940040849042400130402c0440002502d140b194465060740c51340d035034010581d100c01035070202182c551040d2514002d00490401441d40600b0501160140c1c403894221044c0544810b40c03940020014200503001c48510000340740c00107800c007101c0c09540c405403840106e48994000f000c181c40300d40b900340d80a4440c5000361050541030700071130b091032404c1c0c218400621081c415180081c68120046510350065019408140d0034021906090781d07100c0d041c0c40400301960085502c1d0110780c00000401540b031500b4110310503400b80580b00c403810140240c1f0380c141107070b000072041d004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 482888812 1250 482887562 482887571
    0x6060e0109170114010f060906050f16031101022101120b010317090a06030b01031109060a0f0e030313030209070306032d0807060b04050105040c021f06081903030e0619 74
    0xb0b201d1025005400d1031100b0340e41500d0f056070b441104e4100003980b40900301c00510801d600062241c07159007540c240d46603c107501450f0420824107001c401c03950520480c2400005419454421000e101400c2003084c44410b0907064901c0d100003500c0d03560141c111000443c1048a030201040318000d206055031f03800300d95440b0301041c00040c141140aa101e04030b9024448c03070700105020f9855003080400034820b0b20b062081c100019851032441c040e101100e504080244080d02c00d0302c0c4a810b0605005004d03080210f504800000400e085070302a0003541c145040d400d00410440c00c2c50b800f916030118251508000103030a583d10455591540540043c40b0703099081664290302031050354840305130b40800345554030540d41c60140b000e891a10702c103030b2049281200000e400d0900f4025800306510b19409401c00450780b0012070700a01c0c001c02c1c00c0c50560b45d500c002003a0007404000c007014403c0580c0500000d11803614000301503e004084414294200000b0305c040a0100a444000102405070108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 482890062 1250 482888812 482888849
    0x70801080d120b0603090d1d0f010c0204091e050c03030304030804330b040b12030a03090c0b0c061f06020c2116080d030e03070b0c0f0a1206060e0109 66
    0x1400b140c81c40e0f598844800828860600380026096142c01030540707403180c50901c040f5011120a074a5805030360894030861582c9001c0d8450280c0d440110310003080000c04151680341c10310107207103030b00030000400880316004080c00410408804411030444c0158910710701540c00401e110000341c0020012180b80d500742181141c1e0309240d40710b004002d00003901903c620589540604150030000380124507054801e406401d04480e030b01e5040951400451400304040710407002420305100075078000c0042c41006c103100f0781080080c80d40c80c4000e4000e2006003807221000a4401c4080266580880441070811006401003210044854203c2da40c412034014002d015100c1d18004482042d60302959050210060000c0c911200395180d0000f101d0010464003405d800712130718005100c600d0317030062104000054840720b48030780c040c0c4049001820400c02000140007038003c01200004201001c035050380041d42841001c0c010301151401142484140d000a80001140d001d40040380b1003404111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 482891312 1250 482890062 482890097
    0x90a091e0e120309100e030c07060f030e010906060501080f0103171b030a02070e010f0e0f060f0907091d0f04020d020402041509050909030a0504060c03091517070801080d 75
    0x20740c0800382c540200e82d21303d800d4a9290301d54150f000252074071413911111900700000041620440e800030340041c541903003403031b41c2035404040709903072001016203819442c2040c4034203000700c1aa083c803d04020410504110015001036030091244080c031100600400c04203070b1001e05102011028200a40e541d0b168500603c2c50324490002d0303009504c4000341c0a400154005043c1c012650006130301c0303030282d032110154141480b107441800f09400e01d10020948a0f90303100c03a1650050380090052840f00340f5238011032905070040b02c14401245214038108054103504001c40030388540e00710480801e01c0c1520314000c006401810190150041a2100007151160341c1290041c3c802401d000840414180008140f0141400717560f0013200010003140303400c40c000040d203621078090341310b060509040c844219000c030500328098003040140000003c840c11148000a62040c3c0e5594509198000302c50080d40100e019044e50f0410441d540100550640410442c5030f916251030034108500c28803050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 482892562 1250 482891312 482891323
    0xc01030b150c0309220605060a121104050301060602030c0106120f0803100503010e0307032006010302090a020f16120221070804090e0a0308090604020d1211060c090a091e0e 76
    0x31305410004080c1002046451503a904600c41c0f6414414090b1b00d403503030180b119a01481d0140000700c2c454030510b1801c00c030503800140449003aa40c1e443d04060b6203030002400d46e00154042d074007581002880c91261740080c0900c0000e004050400308100416a40e02c81d8200745100303018124540101c045200c1814501000000385801802070111182511040d912544100c81c201c0218403000740791291101c0c0701d81418181c0d100140a07000903840e58090000c0707894010f00142c0b11319420011110141010383c045c042a4040e4081620805410b10307111603507118000e9080f003035600804107140c13400451407035500001c0407a1000c0352200401d1a00142034003850b0000d03000c0ca8204402841034900c0041d04120190080da140754241c0c0322400d05c02e4441d0000c0e54040e42051904510760085a1102e0600400c1012480e104101588003412541002d1044d56804034000d40000c1c4a403040c9007001d06a00507143d0094100940c41554840102d00c48d01c028041c00501c2c0c440d03c00130381c1c48109000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 482893812 1250 482892562 482892577
    0x50714030c0a05010606180509010303050913020a0c2a0605090d02122506020c060f070b07021e0d0815041803081b0a020d0e12070b0c0c01030b150c03 66
    0x2103400b900302c0740c60510b020309240d0146200092020410b029401c10070301e800411039602924030011070f405c1d600c0464003640140e003040d810003c8400000510b29451005112100c2d103583d5120401d440e5181030101d92140303841d4403599605c900c8151419200c1001034000300c03a164107285030364040c0140841c60246003001d01030340c8000302d810051a403840201d24410012110105080c0710107000045284001c01800b440d00180e0202100d4140e5007000740050054526482c0d00f0303030403c50680e030350021040c000c488040042c3c101c0d00a00c2502100811485000e6291038050f05c28508907000c020701d4040000c0040e462142c0d800100c2505444076441905020035040c14581d102140c0d05025016050580d80c0481000c1202c1e00414440b4800040e40c1080707555034080e1540c441c503640d084030008140c090390303039200d030481400d074484e10760401c0741c04028042d0201182c0c6400400d20205e0918558000c4c8505060808a41d52115582c214400c041e0400c4404195201d001c00c1003074600c1c500481d030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 482895062 1250 482893812 482893837
    0x11404031a0a0c02030301031704181b09150810030b07020708070e0f0f09100507030e060115020604030f02010e0a21020a02061803030f030f0912090105071403 70
    0x2004024000302080108020004020340911500c403452050100c42c2005042c90058106100501c0041c5a600196051443c00c02c1d02c40d00381900c0d40c1d290750303038205468840340c0c205035917004600282400300c003a0001c0d602c150134003116040c941603410020303030303910200d1604107d2110b002690324180c5800e0714014540000e0309403128a40344038060350790002405040c1c101d200c1c444c0c0000306603002501d014811140015038015507100c1c2c8110150105e40585042d0440c02100051592224a4400c9620412080d40d020030200500c1c80120304042040e0000941100350500100c40c498000030440d03000b076450b18100441c42e0401404a005240f400c1300c40c04103000d40891074051022420b040d15040000d2040000405d40c040016661040c001c40029009001070200c03540152040001c3c0840d03500142c266460070a0110346001c4641c0102c0d251040300c103000042c0030041c10200940c1d607000540c0d951191600b400c040001c0c0c242e004603c00203104160102c0c822404a80510654500c0c040d1503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 482896312 1250 482895062 482895067
    0x70e120d0f09120309090203060d0203390a0506130f0305030d060b09090c0d0f050103140622120306030b31020604090926090f100516020114 62
    0x1540105510751410070070000803850a03001c611002c0a040792000b07140c0c5615004030040c500340c8280003940008010f203511880c01040200942c41c1484030a6141d8014040040d038600e10b03202d41c5081003401c951050084031801800840b075220b4840318415a04103c858545a0000281880087e0400d402241980491354000001c1203400070103099901340e108002c0c801a034503070f0a807050074050180b00945c04000000404c28000d02d0000500491032018000300b41c05501c82d181000303845013079008465034061202d108072211001e122490708902a0b2800700080385903401250400b0000c03034000380c200b00c80d185e035100e2080c1c0668000d8000f5544010351846514181c151024040441140048401e0000704800301545d0805048841c9660003420f25052034107002d0035000134445400c0c200e405c0e000d8030810303031104450b004064130294085150729036191100400d01070642c81024030036002d100034810000403540c0000a44000003822455001e4482e81400101c0b058a030310481d802401400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 482897562 1250 482896312 482896333
    0xe01150503040209220803061503060f09040201090801022805030118020c100501450510050a080706020d05040e01150c021f080907030c0303081003020411030a0b0a03050303070e12 79
    0x300c00914031a00d4101c4e03241d1000c0482449c80d8065100840312150700c420003240104591900902c0387c3e0300300740113141141501e91a200c1075422a4031800921603001c800a103402e540e00c42907560ba61002c0114602f00e41035515048407114814483c1d4144c0e5540794001c44c001c04281402c020703c0f402c10000c0c42d02405a540e45003a0350105211940e00c00484485030703600e004c80000d0115466620030300300e6011440c00c40305800b80c04018200030700b00034100d240d0600c00003501d50713a0001c07075009070441c0c0700644001032030b205e0045d207815a5000100c05203c0d090000f08440408125100d04407031510000001407165410200c40745640740400950201c0c20054070003038a5000d88031f100860406460744000d50b110f05105c1e03541c038199407000811424289600740006840358010a4000c000100c6a10807a91654009000c0d9400546050300640700403003040f00a14260182c48094481602c1e0700c540b09041da1030312512444014048030620212030580030700d9841e440d090300c8000c1940c60a41d48040781 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 482898812 1250 482897562 482897573
    0xa0c05121b060402090601030c02010906060e01050109080105070e010e010302130f14010306080c0f0a120f06060e1302010f020c09100303020105160c0f030c0206130e0115050304020922 81
    0x1c00e0003044540c2940e02110101d00d03000090031400b598004080c17440550300c68004501601c00305440c003045540301c4080d500068194001c000c06010144152100c0750304000004245d80c1c0241d00105081e81850240300055400810700c0402c14400e1030807080b110036400c0140c02034450486000350301110000000303041510110620266030b000041500f02d2164040110156400d5024071041c64114410810461624204040300e4101c007900d8080b00984c1c5403074400c030f6040405429a1540805d141020801056100f900043c0103c0e15a0703190a09007607036480800100600c0080c10b01c4005055100c400d402001600d0f218207004000709040d10f0000114a141081c0d480102c01660070007002c240c010350464a601d13040680c03603440b002410080c0d04c0340749595007404010742c10300444441c0301c009a110b03200142014402d064100700c0c0240f40504044003060141d005940040f206a030200c41d140e840b2048940094040702c01003525220a000948405944036620711803402100f2104100b24 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 482900062 1250 482898812 482898817
    0xf08060d1b08190b010506030a060f080102030f0604060b030a11090d0807020414040f08030402130207061506020d050f0921101104031a150406082b090b0a0c0512 71
    0x20402c0c02601c1102c00c000140440d80000c440c001001d48500b140180041c1c10700304061a031003802c402000c2812580c1d08440c0c80302e10071540101c07400781d400108110f14605c84003003203a004030041d00c0404c4020700e4040d50840a0101901608006840c1c050500d003e000e030400303540208000420040d0002e46500d400e0400b40c1c03080344101c5c040c0e0b0500450211907512003034510711036504103001012044685e03603040c1c0c6950000b042241e10040e0002c01c42058403d62025120151061400149090522440c0d80b040c9100317611290442d4405081400d11907031001c1600d07400350060941c1903c40600324002603250102c2c41249808080c01620500d900800280640000901450401441f41e001c0124007062040b808080c145510b26a030601c0101d02405c0c0c4e00c1c1d4804400121040e04541c000d00040903581a5030040c005d540c40900000c101d00c1d4032507501a0031000c00304100c500c0700c1d1445d501030452001c03031240044801003c2002d0305598084d8144048156202060342c0c800b422520340c801454 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 482901312 1250 482900062 482900069
    0x21140a05100b0108190e160e0609040201050f0901090b070302070e100f0509040312050a06050f061908061201021210150c0204230c040302120307030f08060d1b 70
    0xa100300003003605840c01ca84500621910181d40701c080c2d50b603d040180d812441c0080c2c41d20000c0e903698524040e007030014410312400115210f058290f192400038442e001000c0546480e100344007400038800140c1e003110494180210805000751200003050040e944038200798454005e1020000e40c1c84c1c2019030101d12a015030301c1003440d144041c0c88140d030900710b42d242805000180d0801600500c0b0a00d40001c45550161091800d1041403c03a190182d0503a981660004d920700c5d142c038020700071841c1200400308000d406030b4819080120301c17840b00c02c41544802040090105039804542691a000005a5803130321043c025961050f100815980d1200200c461164129804a01064907010070200200c9402c0c1c954131040059510b40800c40100000000f100d0450a18110b12000e1030710054012720400b011151907440b0391a5005001c9020190302c421580d68004000100c00282c010210154084084c5040c070381ca42d17a0240842d4100180302e10191140070800e000704820b500d082e1003001607 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 482902562 1250 482901312 482901323
    0x130b0909010e07060207030b0a021309021b01050a0c0e09040302011404080d060605090d03030b031f060305010507080105030604030c031b0b0711060c040b0304110603190b0303040b0421140a 83
    0x2a641d80c0f8005c07a1030710401c0c000206841c2c1d9400200c1c003807540750780140644000000303070a40c590303582c0c0618000300c0e4000070203070780680030019141041c05428483d1b2584a01041030601001c81f503140c00800c03507081034984a10480c05080401e00f814030035030085198490081250740c0070b00300750521040a8201e0440c142c0418201503000c2a894402c1c4203440c0c8031880a884080d00c6502650241c01a02b0540603590300f601c20500e4030a19241c4291132010305440003100012040d00310300700079094480040c15603041c081207000401481d1000200254001e4040c54800d8203042503150403907207010100d0780d080003141364028500c117024002200500034140c5840740c90b558660a001285c544e442154905d18024091004100d0f0480440066511a01c0384081c15a095a00c00001e082500142c5001c000110399140f4989500d065100c0e501842001306c0045043c01e240c040e0b00c4140748100d00402804075240b810100115030742456004145038040e103401d442d162030358403140d0740342032440d0140e0b01c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 482903812 1250 482902562 482902573
    0x30c250501111801090605090f0d151d0a03051c0204030602130806090a020108061207090e0304081e060103030309110a0311010314090604020d0c08030c06270a02130b0909010e 77
    0x342507005416580807100346d519a20304181c1903004001d40a0307000a40590000c0b00d00002c1000600d9421040202c40440d0500040601d104c3c1520361000c0c0c8544816501640040403040220b600602a01c0c0d20150020f10242100428001d0b50301038060b07544000d0619001141c0d20081402c4401024281d8043c50304492081d0340340000b09940342e80c07002019002c10352000100d0401c0c24441c02c0c582d2429501030888040c1580c034164071040300c10040500030f8941010500b8800c038002445a0a8584110f0f120400c14080700d00202e6155107062000138241541c903c80402003103000c840a00c10b151008050400550762800d0504280070030100c0140040d2421000560b0b81032100d0407035018408200041820769600c0c0c2c2800000d85404005031814601c1780702c0050010000c00040000744c1e880b001030a030609108140f5030401c000c0004442511012050030720300c0c05c13400201102000c0c0c04440f000340c041c030914100b07401042492407040c0c122107000100302800005400c102d45e50700340d5004658 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 482905062 1250 482903812 482903857
    0x1030203070818010231062c010e031f0f0612060b061204030e011704050c040f020d020c0106030b0c0f0a18170c1005030c25050111 58
    0x10124401250304402081588011075401c43d000030f03800300e02000c0c0c1c01c001440d000c0007000c8910f00d1155401401d148040c030b030300510131000700144000010900c03807e03c034404865190707070024008100220800801a00800f902c12030788940c010100c0c2103009070a0f03075045d42c0c0f1008489841c50100808520380b40c00d006841c13445c00c9961280e8000c0300d0400b40a41c1a02a00790354030f801078501c001c800b5a02a80a10800d84400940c088440c02680b090b216207030f01010a800140400c200d4103403c1694114240c204000324002040d5086020b004490008440e8040f40c2c0d44402801590500780000e4804030742c2c028131840560004081d24000c00305041030b9600c0d000305030351502c00e4440c48a81a81c051100c0c0e44001c0c00388100c050003885428600c1d440c103868a403240b0381002c030385407490240c0e80700481c61045401c0048030a910054145040ca14610f0444200c481030b00c41d09103001390004504520b80809071801c1d6040501d654041300a114942404440b0001c5410004400d50034404140300e19 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 482906312 1250 482905062 482905067
    0xa090509010f030f0206070b18010c03020702300304080c1536090a050103030305070816050a03020d0204060f020f010b0906010c05010e0a06150501030504020a030f1e03020c0f01 78
    0xd41c100e0700310b01d00418000d410b541d103800c0c414800740001c03a080202480107a0000f11481002031282c4400b52659606120300c441c440d0039610f0040d415801c1c90b104008610268407421070311080428009000c0d1442d0140c0c01c003220300c5070032050166499000101e0007262483c40410030a14541d03048a14811a441d5107100700340d60b00c150201900303e105d011640c01c0700c0e040700108902402c5829558a900c40300d40c8400300c0c011483c203c0301d580c810750f62503005008060b09849615040600c42c680300c00f003440e21440440c000e4544181d0342040c00000b14070310118500ca034040318803203240144155291999850060034000d10020320302e004d80989003014185140503c108030b01c0d2507004088180584860b80113540b200c0075060191501d54035030002d00a130000801c0000d00844c4244d46c00641c2d9406402e0204550245404c01c030b0415040c58107100141ea0f800100f4000d0320382005060b543c06066180c9070005a1100314602d2100e0f0702d200050081c541c0110300da848021090b03c20408a000c6c00004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 482907562 1250 482906312 482906329
    0x60a08060c031501020a1e02010f170601031a04090c171203061005160f141f020307020a050601060c0c0e130f03020c0402040e1006030903051902010b10050a0905 71
    0x8141000180002031142d0b62103c00080030600600685810340c0e01c9031961000d454000c050820a81310322042082103583c0460030046e40b64183ca0604904a16003080c001202c00241c0038034100758a46100d241e4642140204451828004208018104c158a40052003960b50311519503500d880300e1041c1c0c64040b0128107424809030f10743c00903140d0759a010800012260044001040040c203101e00c010400a5110401195002d86881403641c00316142c180e460014006002c10283c12034240003444200700c00e814140321a0701c2d0001340c0c4941c0c4600e0103e107011801a00a00b0601c00c103000000c1031900901e0352066580582d0800e990681ca0b0f850ba16143d079800d89006403100106d4482d28089041140c200407418032904c1560001e81c0c21400042c1640c001c0e400c6a410b0401d0b0350305001c0c114103070007040300080005d41010311122a60b9207014010313000d51592100c20360540c007068810b5902c03e50102c0802040200f42400340828500c0c002d00e25000240d500f804542401c00114940c13030700c05007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 482908812 1250 482907562 482907571
    0x509060618011211210f01020c151f15020c091501050901030f1e0f110a080a1503080702120a11040207060209090108010c120c12020f0d090605060a0806 67
    0x154409164a44600b0b078210310f50862050b14070030b00000c840c0741180e07904c10307484040c1c480d80001c601007160020310090529507242ca10609607031041203031a5403c04046001c000ca50f00b0100c034030406035070391801801802e40344051341640440d0010301060300d149403444296203e0550342100d2418a4034030078040c10443c140d6001c0182038004070309501c1c0750f10034401419803003418580800e801782880384220585162200d80b400400c201c2c606000540060302c1940d0401c1d0100106010351b5004040c40d048510482021004020034440021b038220505d40210113070031108812000119a6170800700601e03048418100e20800c21002e41d0395107000c0000e4100b12554209413005040020001044000d42c03140c50200c601c240c0a2241c4002c40d03540d4181c450092403402e0001c0303a44190350340024460740041c80180c3d0081d190024503941550700c1712116102c0d09000100581c0d94010011400860140b02244214a41007650700030400400d5000980a1b88056900400031070700c4402c01c540350081180c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 482910062 1250 482908812 482908849
    0x23040306060e100e1e07030e0a03020f0f0303041109040309031b060e240a020703061e0c05120601050901090b0d291302070303091406040b1003031706040b040f05090606 74
    0x78400305015801d000c6901b18056050021318011840e081c54141500c50000b507015070000c00c4030040d890b5044c000044560b421038003451070b41c0b5250b9034449000b0311a0a001d03029481e04000141014024010b4a02868004003206040c0700c00840c0c07489500402e0080c080042e028a007281c0f17040c14a0b00c8201c0010086444a42c520700325130402c466190000b407907003801c510440c0d00000c007003841d5202d0380302c00d81061415850f40568244480041e1041414110200202004416440b070301d0361401c00e8201409103040e41d91130710000700403070b01900140c1103a44040c1002a007110b58881c6036002c104a18500c0c03070082e48415242d002054070b41400b020b01500702c40e004d120b030001142640d004020451003406d0001c0c840480340c60385841c00020840405c903950058042c0001e003d039800d0401d6006444c403600d06600c60a568000789000d44902303620422444a101158480d5160f41007820281c00240080080d2000c0b0184030024050544110020340104c0c00490218104200500000401c86 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 482911312 1250 482910062 482910091
    0x702090a0f021920060108150408070b010602010f0b1207030f06110705030a09091a13062102090112020f09090703080a031a0901030323040306060e100e 67
    0x694400c0c0180100050084119908020200c0f9510607405070b070440a1442e9901045113903a0544900752842c4449036a0b40355014400400039110000369209084c82c0581040c0c5050700c4074680f1010314080d4902c02004400d0160011034040d9056100300c1b030304042c3d5002802038541c0e003811303c02000e441182e41002d80c1c00294003031000c101c460008011962007602c00082d8401105803030311550b041700400311443d800020700d880d0700980c0701c07914201600e684141049412045244030111030811503c81d4003c0300ca01040d06105095980118018401c1105200c6c4400c00c0307072401f6030325881c0d460f4124450320410300007103030412190212400165002d010031141c84140420402e4849006103024507a10a9420100010f03a0310b401400500290782c401140081c40e444c5596004071484103d103000d40d10000040011039130000385c2e4110948980111880100c46a0195207144110340020380705a04004000629461800079a4440e00404840f8020340d508c81d6510944000250355140094035034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 482912562 1250 482911312 482911321
    0x40c05041a0415030203060909070b0301050d1104051513140408130b0a0c0204110c060403050c0a0209010b04171606032c01050402040606020a0f0b1b0c011a0402070209 74
    0x801c04041c1c5070303810262450510b65a0410003180780c2c0f00c085030a0000b90040207003c5036061260b802904011024060902e80381015000c80c554081423140354400d008100d401c1c41840300ba0080c9030307500d8002810610607850b0011050604000c02d021603070050b83c880c4092a0340803098420b5441d120503065400701c00741c90341e840b0380050381c100c000703880440d040350840000c048206034000d04450000c1c8e124400c082c04280100404c8500c10010000b00c840100101c480c10100890b059501582c1800c02d551980e07071010302c461a12000382c0000790050810400481c0284d8040007400450b0300805000d07600c070f4041c1c170342c241d100d04242e800c0e9540b50b00303800c3d010f005c0503000f500030100c03001f4504d03904110b0700040000d0f001005a00c01c142c4c0d42d581d40d542c0c240429400c00c2d006180182116000030032103000d582d51600010b8242c4c120241c050b584020108041d2003007030a8070282c450b01d24107440e440e005081c05041c0203260b1820440c403840c0f0410483d8505003840e000351480b00f40c0080c401a95940d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 482913669 1107 482912562 482912579
    0x50a0b0601270645050409030818010606050d021c050a0e010b1020010908030412020601050315040602180307080106051806030c0111010f021b0c040c0504 68
    0x1c40104541888103444000c02a940100d860042591404040000016080b500199440b5091482c910309049c2d0200344140140f04c1045100408120b411200f803c8424501c15200452002c1c0300c006050600da034003800310425021030f00321050035240d640c4021500121041510746580d0402c8028000091269100422041d18500d000035071900f0b000d40303c0c0641c071709405030004070900b819500c40800c1d0480c600c00caa00a05160b00c1c2c1c1464a0324445841c41850b0502c0103100c0c1200000d40c61600250065018002c03c180c18855100d5072604000380d80031510802132180c5080e44602d040d241040a140200803038400044d455080008020000070800d001b10881c441300c0c014052559404030b8409111502400e02d0884c1d8080008100c3c0504040e10390b00c0c1640f840816580f00f800c036400341b0301440138803100a84242c0b0071714604000898800b420070b400010020300007409000e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 482733812 482913669 := by
  have h0 := BRFrame.cov_init 482733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 482733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 482733812 ≤ n) (h2 : n < 482913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
