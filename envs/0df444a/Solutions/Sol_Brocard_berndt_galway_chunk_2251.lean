-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2251
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:08:02.335772+00:00
-- url     : https://prove2.me/submissions/11b4e8ee-0771-426c-a268-1203bbb11bc7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 404676258 ≤ n < 404856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 404677508 1250 404676258 404676271
    0x120307020127060807110714010c02012c13020906030a020f0d050106020c03010e07050a030f2105120705070c030b190207080301090c020f061b160b0901150806040602090111030d090b07030203 84
    0x8e441d042488594094205130b011603105060100700618100142d00303001607010030f180c0740d840c1401e105555900308224201040007038460290310346410080031030498400a0480140c40c0c1c0d0004000c02600340d00020b880040003824001d100d03a50790780e0f0b00290b039104001e26040c401e51804112000501e40054013000b15070000d4030192055280da16406034450341220155910001d85031404a10104801c20090700103541d111141c90341d2601c80125101c220082501c1c0511000700115004285041d2190302205d60041d04103181c0d5030b9040c41c0e1030701c1d6000e81034407607006800400c600040102e80c2c03010714142e90000504124286d4000f83c00c81e0344003800b0348a50119000400852040001d00c41d203514040c04120120385010b039031925140c0c80c03194034001518590601c00620058401c2801100c681d000018034002d00c25040c41d40142e101e10001d0001007580d640000c140450b079008800050102c0d07032601c00e580d100c04540030960081c04880d402201e24010100024455900900c00e80e4000c0c0d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 404678758 1250 404677508 404677529
    0x303020906070b0a1d0703080f092e09080c12011b080103061b080c030402030c0a0303021c050a14090a03060504050d0e061c0b13291203070201270608071107 69
    0x11f296031551151a404034001111074041008200d00395150410314040d010404002030950700000104110049541c1d031915007000a01c6404002c1e50100041800c0702e45802c440c00c84040d4007021300140101031511000190203016061044c019070041e80290484e8003500d018811241d00d50340030340240b850811790001103583c22003c01d400b180040003540d44284090219148820760000041d001c41003075004030010b90018160201c0803024038107021026031030b400c1842c14101c0d60340016059110307003161204100030215030202c043c0c1d80c40b40c9034801150001300401640c20503080c190b8940e00ba080304080401c8a400000d105406e00d401218910f248a101d1ba4640403103903804072010f044c1c28006c00f0780c40b03166800c000c035019020384a01c4071401301d0000d146002c130300003910f8841ca21701400c0b5054810f0440c495940001140401190f00060f424a0328401e950902e680d0030004c51040da18440d050101ca00012405580114000e402080d08ae110400aa0109249250b840c440c1f0b00503d034510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 404680008 1250 404678758 404678773
    0xc0b0a021507170907080726010c140c030405090109090317070909180605070306050102070518040303020c16080106090b0619111203150f03030c06010b070303020906070b0a1d 77
    0x540110000c80c0d08071074010143d03220740d61b450021500c0e258058104040000c9410089040035044411a003c2c1c2182d0000900883c4820303030700549134030032004038605109000100b01054103800d0084034090030009251200550f150b43c02341c0c000340b03401f04044021032441c40d1003c1c400184071040078414101e0395540300ba0f503410038100c0c4010b055864820503034601860a0700001030751601030705104090694001460030715140009261541c6a4046801b490b22186820f02c140c911031510f0340e10640504026a95030034507151a07140c00d1101040800c0c0d814205000302c0c100034103400036821030398400001d00000303980c80104051846030148007440b000c42c42c0e640c00c03003460192800d0001800950103031980e2002140c0810b40301e900880b01ca507003141221015050710314010300703456007034182580210300b8813a100c0d422655602c0306018034400110301007480c40c05c01d4480c1d01242c03400d03400503144030f0700e9a10701e2501d0407a101050b00c003054250b060002c100c0c500c0107000c4400030100c0c0214000d003480d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 404681258 1250 404680008 404680037
    0x1309021308031611010e030307082a0f07060801050d0b09030d0f0e060c07030807081306021803070503030f09040b0a050303130602010e0115210c0b0a021507 69
    0xa60040025200c000501480011009424805002061820040e04520500600d0000b05000940b54100d06100000a1014498500105403407072984d10441da10383d94810704041c098401d0003002d801c1c8400002040890050030080307248100880100c00302c500c0340381c41349801e40700710300240980c3c0c2d0071050078540d81020407030383c50850b5001000d030015a45040002040d92050760301008020b07404941b40c0e4000d4540355001c0102c0b981c08104119203d042403056038009201000240c030440420030124007040510b9a1907031740c2070b02e181d848101155a01c05075903c69100055030706846119014100c800280c034140401294140c8903944840c0d0f1030241790900300002032410101c01c0f90003008100300410951801c100408071088410700d1410302c0c45c60302d1402030a55107814450b0032140d0401481c594980344500340c0a0075100c7c0918502e801c00000e240070351040003601d20203440d22158200005a46051900605145000b03a00f40c8105017110800082d9644098418800041302646480758 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 404682508 1250 404681258 404681261
    0x150804030305070e1009050109050616080a120c1d0102060106020d050f09030d0903020316030b06060f130303030c0e030307080f0c070315020405040b0f010e0111210c01111309 77
    0x52044281c2407411308660780c40081041c902d007602c4c4800c04038a444600b4403041d0b030404042e000420003140c4c2c0c680b400c2c1001040380040585504014603a010205440c0c13000c3c1e00403a00118004600d103010030482c0c442420081042c000383c101900b050342010902e01c240e503c00b182c0e031416501320750000c0c200052102c40c100c0d240da00000210402d00d0301403114141c180d07014030a85000e001e0782d0340d07088411400c600425041030080d01c03295180311300c1d030282040051354440f0003651206003103034030729203450200910502e00d00c0b0b803007200328040d448681e0100070176416921070a2001e5860341e601482003009800e05640b8401d891707020f44141c00034081840c0c401010f074024010b136180c0505032070360150391ba6180560b0001100070310105a401003000d01040c1003d22405a4400c2c003201e28103070800008001070074008215618604001e8043c0b01810303114802c01a513407106185018a603024443c09059110346c1c0c01c40c0001032055424041ca07084254142d40581c0e0070000540d009529803440d1203a01c50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 404683758 1250 404682508 404682511
    0x4081c2c0f120a0206090a2018040605010f08010908160206120109060e10140f041806020414010201050f0c07051e0d03060506030925032406150804030305 68
    0x4140d8441c00110765008042071051a9982a0031070016483e28181440641000001080d50280381e12140340c001c00f242010110408090420041c0e0290868040100d0800382c0000c440c4101030301d41c0000d120030072145a221604032901d12580040382d075190b0f020b26082c1c41e80d541c03025094403c10321000c048105640390001005200034107080c030380240c0e09600141d01000b41e10500b10780c0d0362141c040210031550350000da4810407001f01c0800d980e08048002403100c402294150040080701e0b40d0004903181c0e940041c1040d074402189110b11076031458400701030350003800703690000540000c1c0110b1550050061a00910700320484070a2540c51000001c09508103100681d03091051031107984401c0c0c90745602d58800f02000024100040040001905440c2c19607c0307280107400170402c00101c80404550700d076025002d81c000364600f07142448982c80400eaa5040907141000c90105900c070028190a1020001001c06040c00102d590707040d10302c07254401e6007010340407a031800000f80000f4482d41c46a03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 404685008 1250 404683758 404683841
    0x1611090708100b0d1b08092422050709090519020a150c06050403093609060204050907030c1704051c18080303060307230f0109090504081c 61
    0xc20810017022201d40d4a001240300c030108030a901803203c1c031241846919174507141c800301c10240c180845400414903400404d0340082c0e9001001500440149000300c10b00d90340c20004503800e00d6201c1244000a040c4c0c000111824414100c10030000f003050b060306d00c6000d80040c80da0106514011121058000c80070070101005010300d221400070300c480c0300d1070340224029500ca101c52414031000e03141c001859440500410300640b480502c0b03007112061108020031503100402c00503980d150943c00390061344c110030742c04228001086689607159000001c40c05c050340e1407540e0280c00408900800c4d00554010340f02d50015081e016502084d034a00c281c0040543c038080000040d982c9005018100355003001d45075400c00020302865140400c501405081002ca1241c0b49081041c01c41030300c481c03036070f481d540070703001da10030450942c1e000b0801c0f03a001300308081c0c0a05c80d42c03130a860090f0169000c4104005c02ea981d180f440c020031141403241e041c074031256045203000099003a105c09203c22101c0c159 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 404686258 1250 404685008 404685011
    0x70314030f0d0603061103090a020f030a0c090b091006020a0f02061908090c010207060c1511030c041806060f0c0c1a09180906010b0f1611090708100b0d 67
    0x5104802120014600c510442030b001440c5801d600e400002d0b200c1651124480b00014414868000da003c160592940d80c12075010b1181c95441000ca41042d4030003802515009108100051050342d640003641c01c032030125034461007650b4580c004d8003584000e0190200580c4440c0010000a415854000d000350005020700d003041c0750710b0340c01c1c11440340d208482000180c46c41d06101c80300c50208a078042c824000d00181c2459402e01100410462030040054000c0200e407000c580c4069803580a50600e00390410090780c5d07460000311900302070b84036200d100200ca080c120950070300e40d881d1241005980f040c0d0b070303120302410038007c0456000211300c6007510940b2401d80001428030100300940b81c1900392610041c1c9600030074007002644104070f4085a10291a00204400c01e500842e5183c150742d02508400e40fa2419041940309074040d002d400e022180060310008248400b264a0f8959220129207240140d614180100c46110040c0e4072001c45d200004800c0c441e8200003400350803040d03600c240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 404687508 1250 404686258 404686267
    0xf0706111b0c03210a031d0703031d0922020117010f030303050105060301050604050d0f0b0c0403200f0409030c080a08160309080a050903011e0f0f0e07031403 70
    0xa501c44a00e0700803003181154001041285582014800d514104210300c00000440810742c514514610600665004055a80c11180c1c0d0450500d20444006214401203d000c40e03107914000d84801c03011104a00613600411150707440d03280c000714207485500525400c1c600b464800d40f00704902203421100b00c1c14000d40307200350220143c1054642d8000c21030700140c5000d0500d981006000c541c0103820443c02044d0400052003c1c0d01c5100803901107810a1340c0b0410102a241410700141040c0000144005400b030144520070b07640c0c0c1c0145c02035070b01860003400e42c04200401d0314040340100b54810741000e0107405444481c40d1030b40c401c0c01854001d0500c00317411340d00d42d07a58403025840302078818041007003c028026054816244c0923807205150500304904061341e00c40344064000d8860360307000c0180000b5681a00d031001e40240285900210000d005a00c0001d82c1d01d003c0d00905d960f10300700390b140584003a054043c030f0103203d85044e0008050042641141c41700701040c1188039209000b80b10401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 404688758 1250 404687508 404687527
    0xb180904050a0512190203070f171908041103010e120c030c19031b03080c030c04090e0c04270b070e1302090102120921070801110c0105010501050f070611 68
    0x1001042400401e007800c1c0d507030207118900240c02c5100489000441d8024400b00d0001460410140002a0491540a094020ac040c400f20304c1c4a100741c44045440012100b2195581100245000783d103e1217840401e2503000b0b090508035109000031884607030000031030b0080d112140c002081030160050641c1d01d014a404001440e0040e5040f241c2e085602c4250071009040e40020b90348204001421b907102040e54644000740301c004050200030f0b03c540c000020610350301c100c40c201c0e4010320703c0001c14419010304044054541540190701030049050800102d4034503018901c801d43c0084a45281c1004182c80c4c0b18843d00c104005c000c20240060380c51005c0081d40e40e00d207801c0000042c040d01699880d2203400080c180701842d00c0600380210180100ca1455480e1241c0050440010501620341c05842001a16000300c40d40004095440d102e180902c80325640c0060283d900108001e00c6a80da0703d02c011030310361086c2c061002d00c1c440180180c50000700b0b2500200308510381040d2840c10224040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 404690008 1250 404688758 404688763
    0x10e0303070f050c01170106030509030909041a1501050a080a020c0a0f030f030203060f01390209060a15050c0a080a0f030e0a020a150320090a0b180904050a05 70
    0x4815150b0710411451001001020003101055910a10384038000400e00311404400748010f015540605444a0005006100c20000d80d01d002c0402032079142c4d01d05150400c54000031022002c0d010221401c000229074480c5405103204100042c0d481928207840c885049822850241001c107025408001c905220241045a4005980509024103c400c86460058102e1504004030401d050040c01003082c00d9541051a4081404c20f0905500c1c61701c0d919590507864100c2c201165035010182000c080000901401c241c0481c030a880e0100c0d15124282000481e0005105044400c010501100d10140c82a4041c0450900080c111022a546582e0317241c0c16800411040380002c2c0400c2c0c2c4500341a507d0300901202410080c060681e00d60190041103483c0f110b40502c403024040e0055021286102c1e81c02003000501d0410f0103041c40c1d840e40392031085c0360b0000c4411841901c1c0400003042110f6031100300d92540240003a00415031b45003c083c003141e240014001ea5003030042818603400f15009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 404691258 1250 404690008 404690017
    0x18030609010209090a051e0601050c070603050121020a290a0e090114130509030904051303030b01080c090d06110309010504050d05040815061f02030403020f01030902030a060b010e0303 81
    0x100e10002d03845202c00401d0000c03007200180207601580c1031105021258189440b240355171150030403811041e58a510046c1ca0501c42d074040c02800707114500300082c40c0ca9040d0b20443c142c1c1c550500390303100c5018402c840381145402001c040c2d4401403115040081050240c20844c402030f404c3c4010b091a90ac4130b4104a00c5e412912808010940200e01c8612500d043c00c0c00c940500001914495010512070108058544e801450109140c4e0740000c80c0f03500c0e404000703a58183c20024005d009078074000b414144004201070341180030900b0185400035660003102c0d043e11880720b43c00f145003000341850420424807400d02e01511540d035a111054403420300c0800030b520401c103030340001c9041e0030140703415850302c2c25030000d000c01c00605000a11442001240c00c0c6c504040b008079840c0280c80d41c00010321480c451000e044120a01402c01c201c1030342c0c022010344200c0c0d00071200806130000d26030040d01910720a08009605800104c500c80c0001e0304c5034007042c0700c1e44041c9404280ea10242012a113150300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 404692508 1250 404691258 404691271
    0xb16080c0702120d08100b0c0d14040906180f0e12070c030b0a0203160905060909180316120915120b090a090b13030c02101b0309060f0e0105040b180306 67
    0x74410021001050410180103100e403030f204032324089100c40703401c4d150382c2000034140800c05142d000700c06021964060318003606040c54100262a0f89030203410032041e0503082d000c185420559003500198540c4140b0802034059000b400350540d10324103a0301541c4c01410201c1c7d000d00c5449010000c11400c082e028451200588016640c3c20107610001c00b44104d810f283c01040401c850600c03a41c1caa2000360f50718001d041d00c0302c034460b8840d1100860181758440c1c0c0354032688400b15580342d9030a0004c00d01c880c1c075801400c044003a030012041c11a4019a10b009100c50303580501d41c0746061074802e0007241000b000310707800007032084840c00c0010a0400c0548081e400251140440700038805850000758001045080d0043c4011140d5070142c030030620031602078800d6600d54803091b001c4c0d00a00185a0804103494603e02107013040c82c01034134103c498010380c07000440c8042c581681d18042c4140031105034051312224142460050303094490b030b00800c8180440b41040101d24070984040040501400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 404693758 1250 404692508 404692517
    0x306050726010f05061803030c0a1211060f070e21010b01030203101a21070801140d0b07030213030b070f05030f061c050a0f0b16080c0702120d 63
    0x114800282000c94032840114218800480104001403d00300b9074012210b040d00e501d41c80c0c0340e41c00a080340340313096200303019014007000600000313051010555002840c070403440288800310f40c1c14101c60801c2a419100056400400803c010443e140304042c0e000c0030324505030b0002943c0201040b000b030400001d0046020800100c005048420b018010395a00d0a182c00c504510b085040a22100198031801a10300014500c144e0b014003594121000c56070b29020700c01a03c40001d07910740c80442d04070780f050300041c80709001040300e82154042c80c0724044000d081641e9949561210781032100701a102e102410b5081200703030300140142800800440c0281f402c21071a140402c0003500c0649095800e00811004100300300383c452907181c080e0b07040300d0107840302c01e0781d0b0348030401c10802c0e580681d5000e031403403040d51002400c01c1000040440180d00c14149404c2c661107802d4002d030124a07543c038110100d8101c0c0d00088503101481e000d4400310340000e10000d440d062000c2480c1c203110b454582c107400203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 404695008 1250 404693758 404693777
    0x2306010504060b0a1b11060301060e090c0708030a05250305010f15200a0b0c070c05030d0507110303130b041703090a051309050304060309030315050306070804030903060507 76
    0xc0c40d01c1d1003004010310445503420319100601500a010181e660300322542140b6240b00030341446210210800c48500c041c00c2144d40e940c640c4c80182805141c16101485002e612000070307295402c1074260b030065540310000f03034115200c450305003025110003410901070b40400b242d0380a11a0000e510100b90005644000400e07504016987c0340c0707141c1c2500418280100c2d4802a00704603400355111807070401001a44828091550075503041c07120039070700a80074074444414003a05010000c000c12440d480f03032203501c01890b661020b258645490342c010350040b440034821100031420000b4200c18084000703041c0ca151017950004096800316035045a561200040760a204100d0040f0948002d02c0d200001035003000158000104500d4903400703100d01402070010188804810b5804c1082429400801d4a4517140c4440c0010000e1040f1041540083d0901c455481c544d056403400707200f510b5000d000740c83c02d07549030380c1c00703903260803000e0f000f02c3c06c0121000001000c03840902c1004d028070031607503840804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 404696258 1250 404695008 404695019
    0x2030a14060306060603040f06110409020901030c0206010308031501170405060610020313230d08130b040506030c090112050405011a030f060f220614010f06080105010c230601 77
    0x40c0200100040c2c001e912802c02d00c400c996a4805481d1300ca03034452500d8070004070301c2c13600034041d044900f040c05020f440440c0220f981840c0b40c025180c206001e0b81d0810940c1c030013841c1280d4458080c4000b6044420410200e006a0100690541c1241042c148000300405083c8000a0030004841c10b80700c03a0002d0040c82042e240580301d100c2d0b00c096510085040c440c0711036030b4400004040c462010351300d0014001c00544a066000c064801c44010041210304102d41042c1d1400d0b40580c008085401602d203020cd00c540c0c0701820f41d0b0580f40003a002c076045a440401c20a00741d4403250950341444240904880000750500500d40f10340d01c6a00003050100c01d03622481d2440780201809071294000da480418441400954240d108803c41201107460303c94001f4084400c00d030700004004116942d20410a0007050342107141c10701d03807503180c41d0340076039035050001c0030600613004010010f5407450041050350300c07400340b402c1098002d035490000c000e400807180144c0750802d03140c1d2007207401c1039004001c1e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 404697508 1250 404696258 404696291
    0x40b0409060602070b09010c2d050d0903050c0402030c0412050a11010302030708040f1b030311060106020a0213020a0905040c0806040507110a170c01060611010b0303070209060f120102030a 83
    0xb80000d0004100e0b01c0d00304140500e80f03000d1805014100400d0b21154418001036079004604d881200310011851003100351210200942c010f402e842c03912802142c3d0007020b01c00c880050840c5d8000e400707410425120300800000c0e601c081c0c583c1c0420601480041810207401403402c406c503110300010400086149003030010740901c03420b807505040c8180708100d8240e40080340503611907802030a40c2031030b00301c43c6040303800901c6d03821101c078041d1551400807042507088402d3f0480c0c0d00b03112045501c9a80e90b104100d9880240040003500810000e00c011100342040c4c0140803406850f0402110881d15600410b0440d0700c01e00000d07000500c000207124850425100b5140c00181c00d1070000c03045018803034015940c41000c5d10007810aa1302407510030309824098141c40708420442d0081c001ca95a40ca002400480d90ba4100860b5504e410076410013490004100d42d1011360141c0805156691003082044505154100b981c01c031241660801c03410400b0301c01144606880203002400790102c403600074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 404698758 1250 404697508 404697521
    0x12070602030406021939060c21020417120703050307090b1623030930061006050415030f02070204151e0317030403050c0f1e0c0f060d060803040b0409 66
    0x121105001e0111b91505000380303081011190441e07408607106e107c03803004894006407400b0310024400001000139280c4041c4d00100111040c0107411a00001401c0d40c2d0f5440b88180242c40441840400c041000a8012005941c0c890814142021507d03035981d44480c2691200e0301c010246000501407500304400c40b00e05000544203640130740032800e14400307030036541e11509852904c1a42c00c0111910418088100030301003000150900d0b24590b409060355035270782c03800c1c1da0030510340c07a04003404164248214185c80c11a0f100141140024800340c0c01540203010100c908000d6036000c01c000380240e1258001c003d401c1c40d503083c034500748a1815030315071010f400c44c2000084402d060310080004c030b484c02d000300341c800e11683e248035500c2e10346241c1130303401e07104418010001d8000c0491056000002003004003032a0852400e40e002081426001901c46d08840f44459010113480089622402e081014080f0644030000c0064640d03212100c683c6190080d602030901d02e200040c0c2401002076a00420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 404700008 1250 404698758 404698817
    0xb0301090e0a0210080a02070f0c0503071a090d0201050c0f060a060b040614091f030501080d090620340f08070303111203090d0908120706020304060219 67
    0x300b503540c0d400c0d8006246921403050380b104128400002c41c0d400d0382c2ca07604541540358003900031044e030320b05031a0200c0c44003041d1283da03203e0700034808006040944160024401400264454505042042001000c074021b12080c3e0400000b4840e0b101113510070090035080941400c000c008030b203007212018040c1d407282d40110300000828000ac006c440c2c0c1000c0c0300c0d04546007030923400361500301d0f450219803000130200c52103802101c004074003020b454040d484103060300c4104056030000620000251442c115600c120310016850071070901c404001c41e100640c80354482c03c00c2ea040a01144140d00c8504a440000081001d01da641c51042000040050b001000040c07810035000d840c00200b103494404a1001405002d0141a5042e07031403014804030204440c00104503880342007900d20a990f0f25111a40d040100350940350104151000007400c044000d0707400e940c0ca28000071642c400001e5000030f8001c807109038081c8100e0100381d410300000c4c080044144d032500e81402030300c1c001012500408110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 404701258 1250 404700008 404700013
    0x102090a0f0f03030e0301150b0705010510030803010311120f150105030625020312010b0a03050a1e020a17132a03020409080d14060f01020f100b0a0e010b0301090e 72
    0x1000b404440d11107680489406083c0303002018030304004a80900a1044000c1600c0794501021603a244640003912419000300300800681d60380301110b42403440d00e4000035200d00302c20310041001569881d40c61201100141111a40310340c04403e031464140c10003114000c1b034014811004c03002e0b65410701103004007011401030959081c081e245400c0c41c1d005502d0340c0c40c0e00007a200032201e07440c003c0080714040d01801c404040290794031005618550070404000001906040125690b60800c0c01641100c00d620b0751245842e00c11070080300002c0d030110403850140468030380e01e40941308902c074105106100611018100140a15002c02024044541c041205100301000c3c24019188020038050382d50640740081c41c080c50b801c00c106180a84144000c0c541d0a04005104a0b40e4014003e80189001d88501c10510341d09401a43c650210307001c0c070f040c0e80d807080003a0b0f041c802298122030780410000d407500080c2616440e941c0c4218101b40c01546c0e25001c000010040164948140103000700341a01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 404702508 1250 404701258 404701289
    0x90c01140702040506010c1212050109020a17180f03090306090a21121b1404050913110a0b03071805012c030109140f06011a030901110c0102090a 64
    0x40805008080001c1c3c0070f141d803103000941c0340e4000c0000455079038101901c56018012400c006043c2c5000c2400c00b98107501b003034000a03644174070f4000c0e18282601d030780791096032109000049848402c010b000c8000b10003d42503100162030284a591a910700f00c0e4091035980d4003400a0514284001d001201681d000381c040d0000b00f00d0b0742c4400c44800c88010040484a10000022140e810fa00d503070443c0c41510701803250402d003440c816552208400768a0340031010514000811007409507204507034000d4101c10015050100e001c03291800f19210703d4400f00702d0b0400c0000703d0805540c03038019880c248000414000b04a41002c4240410040b401036000030300d081c140000c1c1100c403c4010407480e60070787c000f11002c0720f42122001e01c43c1d24024001b0486070b41c8504014104249100280c42a03006240ca008050007010610310305980c207420501d4841041841d04080644c8001d11111440d541c818400b4003401090006041c0d904c402800981c035084c069040000b49682a0300644041000300c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 404703758 1250 404702508 404702537
    0x5010905060d020309011b08040c0f0f05010c050a0803040b040b1003020a0504020d0e0f03040609090c020304061103160b19050403140c070b0f03090d0c020d0204050a2003090c01 78
    0x3044450b6516107040160700c94685a40c180c0c05060408035060007612019400b5448991050a803445140a00071410959541d04900903000f03407213000c2c05801c010b2041060119500034051b42c91240c4c420300458440e42074640f2445400e4000341c4084602c5842c810a21041c80082070600d07401055090645440c1c42c51640001c1d0240e1852161078061500841e82120103c1503030b000780c1040842a043c0c0d08208201c0b0312941c2caa078064000d07540862580c0001244844440c413070180d01c007145c2e40081d031400e41481402e0f50080d601452001403448104141a642001003011401c10b920441c3d4510b5142041070381d10880d80324400661010754606410803000c00d62009224010b5025500300e10382d218503100c3c1040c20700100b038011b000b04c028000b03030209100d502000254440c090300707002c0d02d01c2c682d0640303412162800c14400107940084803480c00300c05071400740d002942210307c0c0040050090014009291000c070b07000c05000c59680c01000b04101040103000ac504444000d10b82440384200d500d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 404705008 1250 404703758 404703769
    0x20909160c02030f1f060e070e03030f0a05030403110d0804030e030304210209060d05060126010920180a05060a0b1b011107050a060f11070b0a0605010905 68
    0x610114a014030500034402850051469002840d005400d6854110b01c00042c0e994035103030340942808140c114240d400c440c1030070b4031400c41603502c0380c15401680d4841020031125920710b00d003000e41c94001003082d00031141c1d4040080a0014160700c03802d40300d00d40b1741405406100d11401405041d004840741190b8168042e491540c89a494144cc1140080340800720b403540c01582c100d81000d402545181e41d03a4104080300c02103151084401c101c190340d03081e061140c65018080001c050703070300800c014001e20104484404904011010315848203110081c80c1e420740e410050181c1780403100c00324621404800e08480c10103680281d44004036402c0c1d400e0f02400c0c500c4000d25400716259035038003061a60b515284410000c01401c41b41680300c044101c48030604004803605407415601c1c000c250345001203000156501c0f01d0f0404082c00c031942d00c80d250311010f4440390358080b940c0c1c3d070303502d25559281c44420050701455000d001a6049440d00c201e0600c1224090f420450602c10903078400c0040da5180c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 404706258 1250 404705008 404705011
    0x60403090b040b1e0d020c01020301170d02072c011701050a0203190e0106030b0705130f060f120902130f06050901050f060d060b07200915120f0a0809011101020909 72
    0x20008205961030501881c549005c2c4800c000840e5000184900c40c0010540241d4140c4030380c400241e44034140c241d02d01740d070f07050780a4800002d42c120a0080000380c19001c00a454034a080003140020540c0603040c1c10513200c01d0f0001020200c240c14031043c000001d2149a034061340b0078500f1031650800d440701141e00b07108001143d110340d40311600c06840a0003074002070000c6600c454000c5a07810b101c0790141c0281c000c0c22018020031414100011404072040c1040c088900d1900d800440704030504048070810745240c11850121f0702d51903140b00507129a801d4802000106400180c0d811040a80f10103444096100d140319040d044c0050005542d002c600700e001440c11190143d071105510300a0b4068107181d031141b910664003145032400c3c030040c1201a05558000b034010352a4121070001c00402c6003043e15401803d2403140c501084905208a915000c840188110303a803407040e5071900d502c1e2140506080740d4507030010520b1703c840c3d40c000380944521405400203504107003011000c620710000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 404707508 1250 404706258 404706277
    0x170d0e09160302040b04090b011209080a0323010801020d06081507031d1f11180907050705100f05070c17031302041b0e0114070b0a1805060403090b040b 67
    0x1546100301c0001ea0282e4103e9004201ca480c0c000c0e225983d400400c001403480c983c0d079501160b081e5002680004040c40b60507002d0303900a001c0c5080129070001180101081103070490a444543c405220101640d00754500074580b800000d0790b110940100c0b01c0039074190343d000e4400e40e4002c03401201110344d07000c5010b520203007906d80001c004031911070050781100078210800300d6009054264541e62809450075800421011b42400b0303001e20b012601e0441e100f020755500001c05151104016840c040001c1030f005140c07480c21a06101403502c0f038078100003c0b000c03500785944e43e48220f031003041c0c164020903510a0381e40c01c00540d244401d46810312038250070400300c9481d00c8004001405080612459021240c01920410448907288030020789002c49002c007601040b450b400d49501503102d90032200340440307506196800c0c00c0c89941d4450400d440900741a800d50380714114800c0700c050130300ca45100a0b014800400150401c0e080180087c0c040381c109441020003040240300c1c040c0a00c044411603007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 404708758 1250 404707508 404707531
    0x6020c0d0e0f0312220f08060f0601020a141011040e090102250302070e01081608060610030902060f070f0b0c0f030403080702070902030115030518150c13170d0e09 72
    0x500c000170785803c800200301910801d201090001c40d492820004107421f80798001d04880841d103514a9118200317004440c2a80182c1c045001071000039003ca141c455812803610482d0300036401015040c040c0c0302d0180c00390302ca000020400708400d541225000307401030222402145003604842042004824020180681e245040c07031080c10180308000b210024000c200344042d00c0e5845071030254803000c0c2d0101c2800008074000c4041540707080402c05602403d00140482c0700100001c1c02a005000700c103805a0384141e05202c5003491178803a20003401c4062050751208602d280da13142108143c070010300310505a040c02d0010040b1140401c00f125001601820010119500c00f101285403200642010000ca4004000004c4142d25500034410380955030724140032581c1c0e442007890000303000f5508845980c0c414683d01600ba01001829900440e4404600d40b0b0315081d00d244e03100d82005540010400c14000780301c43c1d1090b1060000b0004410700349000080c100c08100020101c04014000d44180c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 404710008 1250 404708758 404708767
    0xf14040b0a08150919060509100e0303060111011410030b090601122003010e030408010b01052113061b0f03090b0c09370501050715110706020c0d0e0f0312 68
    0x30340041000916001082100e170355254010315260b4040c0900f55038400d218421890050302c030500342e00851110308403280c0158195520040111201d940b4801160017030356076041105824548a10003a21440840c0240036501e07185107804070701c405c4000d2490f0b03e0b0350000b10040c000c89844124212280350003000c822000c1201f04584498424004030055040d0303c0e01f00c0309007511074088058411548907200800001c000d04006561030310410042d603c103103000d41c0b0391248030b1400c0104c66802c202d00c190362407082c5210f03594400c1250412404035290002e001007040006510012207031300e62429290910095140e559050744241010301a100b410802103201300d02521581400e482c50741912803808610030060309000c041010b482459299600d4001e00030605502030b07403c580c1c00c0303a80034030062110500e074195840148144815140420401c100d444c01049250000d0111035628402612001c10180009000120103001c3c541c00340511400107250307030707030049030405d68001445052a502d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 404711258 1250 404710008 404710021
    0xf081509150118060e0a0605040615080a0c020a020a0303180f140d061e0911030312070f0203090901090c030f06140402090a0b130303030b010513030212070f14040b0a0815 75
    0x15007070581107080ca001700e42081000c2040d09070800000c4480540c2c08001190300c0d1099008540c1c04200e000c0c0204001e40e000c103540c40c0c1164800f20070340b002407050320b000d0100d540c005840150268819400144104080010640600c5000300201070700701d810054546448034610700e0381c80342d1304a24490000044508148000341d00b207050345680180002d41c1600b1110381860050a48403800d4644840d21440c4035040e06002003160f40000701ca9a00300c0c0c0c10740d1043d808507180410080d000046001c140212132882d01c40c2200b250181c075034080040740200b96001c00600300d43c01c051703007000040d0602508010404000103002900300e4140e030007582c0c8445000200d4510f80b020b500030b41c01050002100f1030380038080d44840307080d40d10030354092103c03949201c0111218000d051442106442c100030401c014540110740c035010700b031483c043d034200720f50358550781c0b40c01c08580e44490340b01d052410724480c0d1860f1074403500102000884554040c40d041801c81c6682d020090513102074240c203440840c05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 404712508 1250 404711258 404711261
    0x10801030b070e030f030a171005060f04050d0308012301050d0b040b0a03061e060b0301090b01031e0c02190b0604090302070909050c040501091a01050a090f081509150118 75
    0x381c1c4000b40c1180c48034044100404d41d81d6101004850002313000014201c141c141e07a80c1c866000e50949007a40b0756060038032042081c2a40305c3c0a004140740c0d070411001800791240c43c2c0144400d4080c0e20b512403503602d000d24210302801c03030089240e00b141403403a0451240c0e1308981994904404030b030002500c0b180c0703040400c00520000722030590201d1135020000030442c41d0340200041d80091070038406800804501c51007078642900410030700400c1400140101754480d071122041000c14940810560100b4680004100e40c8030324041030341c1d031180310b403480c03d44d010402e184021084040411b440d400360b0300c1c0d03608000c9015088520440d252105c40b82494801c21a030380c041c2009140c200320301c02051920550b10002062514011400d0600000301040b803071140d862103103541405d01351894080707801103d05a0002c1d100c0c00c00e04c081520302007082c244080c2c00d107000c3c0000070014803401060203605d0a03282c000401c081507a6001c041c6048070007403c889600d04403a80d18000390b0034000303403014040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 404713758 1250 404712508 404712527
    0x30c0b0709170304090b010c05070b0d0906090f0311030a0206161e031a0f03060a09020a09020a080a1104060c0b0405120a021f05070e090402030a050d120b010806010801030b07 77
    0x481020b1141d0664500400200215809008208005031050005490700000c0140141881e000103408104080c40e140c0100010175004e0800900c1003c039603120b4046803040c102c00d0b83c0c00004044c00c40304254110034004071040c001c100441c2065210b842c025a6240004c0c20400041d0161103140c1619001e404075150406020648080344510301c071b0300800403c04091258100e842c1d4595055031814901e04105800d00b001d4081c0070381d60791b2190300001818071602d040b6081113002c02c0000e01c0b1903e40c40900701d0002c00744e54000050800a82920035241c03a9a4180d0300008104401c21900c1d0b0030000ca00d0010b60f00030100091607540d818154204284420b140200070800542d42c0040396000c030782070440141025400c1c25050140a13040e080b00c108880c10f0001c92503d014005440c030b00411710a5126100400320b99507280c0a60310641001c00c254603c1002c030340c030f410310441c840c1258016204410390030719281c00c2500c1d107100000c25244041c44058408e050300804150450320414620 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 404715008 1250 404713758 404713769
    0x1b0a210803090d090f05010504090e0f071701061706042004150305060708010b0f07020402130e07090e040317040503070215091912030e2205040204050a0207030c0b0709 74
    0xa948a142c089a03068540031402a0900000e11912001c1034061203050103600381c41c03043e0347c0c81d030803d070a01032074800a003045d4548400703d01c01d2000b540ca0001c01085114080c240004c400049800030b180c0302d6080d101180c003e442034604140c0d44240c510742c00110940c2c03103070304401000e290300c0b1b87d05500004c2c03459810360541c102e42807514001701902540c1c61070046038030410841c2c840d99a1004110354808081c00340000c103850400400c000c1015020141041e903000801c01403401402d01040b190003600c41e40b02010560108041228041e00319101800400c4420200700341c51900d554001c00075144a01e0240b9042c030a0000b180c1404000c000707645c01c19078060690f0300310703c0c103083e220b40054000d20105403240c1100c581d004110680c1ca50244104c0d0007013040d54485070030550701a02d0003da0842c40d030b40c0001d60341581e031801c143c2c6481c20640d0780710607100000d403505160042c0400e9410041000c21a1801009a40e0009030b01070030680202d030304007100300c8003074480e0201180c501645a010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 404716258 1250 404715008 404715023
    0x30c0121290102031303060506060d021206281505071b0510110619150e0703060605040308030a0e0f030d05181f0e0102040b0c0a02031b0a21 62
    0x1d071000c185602a200d6203014101d000d4528074040c84004a940384500d840c02d00b200322022008100207100303500502d070170050090980e401e12140c01c000074202d030444525000d410016409000d01410b01400e207180b1a0b00b00045044080441c3c5c0c2e10300c00480e030314803c0f0300000da5180b01c14140c02d44280e044d2950580c0c0526500b51701030070318040e0380c003040c0303903024a40c40f0303051811181b42e01c00e02819807807015420900290030156118640510340f1128800c061304095200c045107150141006c0614014121018024801d414600001002c94080c0d410010522104020502c0401c040e4003d50741e00c030b20200c4010460a11004002d130411f030a0082501b00703444081000d806035511070308494454801d800e215502007481c03081c02655078600088050340001c20144005000c0c10b241c0005090002090000d40741655440c02e90311340d83e00440c92203506030444201c400840c82c1c00c0c0421510340100d070040c45070000c20100042c00c4415a8030600f5079003015600d8064485900c108001c0540703411401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 404717508 1250 404716258 404716271
    0xc11040f110703030606090807170f241006120902031204270204030c0e0c041505091806010e0607050a0b0c12070305190207020d0c0603150f05030c0121 67
    0x980c40290b048504203c001c0380c00c1460101d903a612502104007100c07501e400402d02a0310b0800d11560320698000c1d040a5402800440c0c0500c400800142c0740c1d4589000850301050802040d0703d900004c0030300030240c1c10760080320800032641d100c101e00210404c9501d002560100f1840000e241402c6414118640f10000c00c000915a00d666440b00a0b24010b21842c6c2642d810b0b41d250404a12450000a00c5030416850a001080450048070b6101c0795880c80c07180b520303440740f10340780020013440c00708000100300080d02880d07402d00716007c14620a9000c0b00441c1c0381001c000203801c120707000c00c03003c2c00381001084071014003504000100c003440c0c00800e81040c0e800d00c0365207103130359500808804031689207120200d420030f446841528480c43ca40c603001e45000d4000b29154000e5806410140d0f4400d03c498450703c0820203c8048000414054500107185200c11960316102c560b1680202410703100703014108130603100840c0e00a440c80007447d0039051005640a613460400342c00c900d83d8043c0e0f20f06034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 404718758 1250 404717508 404717531
    0x52203050a1409090a0203190515120624040228030e061003080f09030102030a140112170c0f030c0c18041110030e0f160e070c11040f 59
    0x400400e180c40c0d4580d11280d80312444072080c0348522950055a80200c0300b44006617000c0d2050b8003841d00841008440c030b103281007400e03011b0183c0700d00355038481070340c010038001a0a40c90184e01e84007076a0307082009020310f0300d040b80b500311220300240c01e050802c200c0c00f0723a0503140703030741c0c40c3c2c1141c184040391240030800d40e8068071400e0300f200e10100c100c40480d24201e02c0001c45000061018800c00c440e0303200c1c25003c2c2c19591030b072100c0d810080d90300801c00e8007481070f0303651075078203001030351042a0b10f600000e2222a056101811381c103060b40104000303505400540c0110f2030901030580e801000005c0305540303503c4415214030b00b20200f800298076000c0803502900f54180450b028401d01401c490f003151000500c0390400d040c480980d401414103d0b56100380025081c005031004201c1e08604000500d00400555541085181500c10301d064022440035554401c003108000080c11001403407060501c0d2140001d0084090042c2c081d04500108186803640e5a0325044003842885a40041c803881c01000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 404720008 1250 404718758 404718767
    0xb06011107240228030306090204031b050f060f07020f0a03050a030908011e0c02010b0411040e011401050901050c0f0703061b0305070e100309060e07030314070c030204052203 77
    0x8903900e141c007641465000c00c0f4400200030850200c000364101c080001c00e005000710701c90f409421806c1c10b80390180050302c1c1515201410042d8003c203502040e09500d0440c01a00c10302c141c00051043c00d400307107441c071103486034810b030340041140d0090942e6510181c00003522085d50383c5c507074a6100001000101c100b20f80807d15804280c03090300e992001944a90481e800e882c402e600701203986d00c1e14908035400642030b401401500f540f0740000103c050008004c90151924000d0002ca4404000381c100003202c0700c7c02d20240144504003090b4840c00510000a090344218190681002000300701001040340501030380c02c01c500c00c1408c60704081c0e0385c1e1a140d00606048640300b282602c0900e00166401c3c06801041d00c20300d00c0b90348981440a89104002101c1c140d620013a08140e551503d4100080b074511844043c3c0308000d009000843c550303c0c0040031840030448d50281d4400c140006000654000840026a80c6c1203030f0208096880c02c20502286d5140750421048003282070b40300d010705800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 404721258 1250 404720008 404720039
    0x60b06031003021e0d0f03200c010f05030903030f06060c0d1214070e0105031b03041b050a06140912100b011b2a080f030408190f0b06011107 62
    0x80d04c00001c1807064071130551403407140900903038011482e00809000a0110f03002d90440034801d040a0b00d05080100702849800d02100310002240d10021000c0039643c0c2002d000005e4000a2510038918500306c1d030030503101d00000d00744000207d40070300892510b075191070555811410036000c07103220501d40500244110f09035640c41c81390602d08541c000c480b0041480c424411a8170b40c13580038050007540c004480c0c90344020607034003d508401000344501c10f140f0000b1401180038a0740064161200c02101c0c01a00d2250300043c861491034504000c010b4114851001c4a41d2104215807100b40d943c000c1070080a030700e4800756041c024600c800c0010292984556245502a80c48030380e140d0000405404174166480d000d820441c10213005050f080b04050145507066098101c07114251b40d40307406504c0c2c079407040700c140e15030b4001103000e20250300100215203000d0303000c41c442c040442550300d41d003e41c20303680f10003d0b00540200c00000d1032a40600107548010300310701d085034804e9558020000c2800413 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 404722508 1250 404721258 404721263
    0x1b08220308030901021c1a0d0309050d030909050a06240201090b0403050c07142803050a0c150201180b0a1413030207080d020c010f02100203070305070e1008070507060b06031003 78
    0x1008000c95520105500c03070040007a2182d00c0c0701941400340c404001307141780221009c40800c0004a0007094076141c0c040c001c84240e1091b114803610a082c0690b40094440c01030002d404546814810003416100c020007148000d244042c0c90340e03c0c144020700300d006d404d203a00d01400215502060008155102c4014044901700c0000d40b8001603c0d07a407040006c43d01a8043c3d0f42c442009a02a01d5a03214180a040780002c0381440c038804a58990b00c03c0c1c2000c51300c000942d40c10b07040b00c0341082081500002c01052402ca44000c01c10440116007842401c448944058000c1e0305100000342010300c2d40d8491208100c501092010030301d8040785007800c0711007101c004c400600a1103000074044200007180e20f6020100d801410070f42072404011140d1001c2803151404510454010883c680c03030728802140100300301d584c00b1545242016001c0d00304154818102d0007100c9000c2c1e4038101d02d900007100781e004141c5150440c1d54070440e0400ba00984000001c0d280e22680001c103210070400c42aa401c42200c1c0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 404723758 1250 404722508 404722537
    0x30f1501090b031902090a15180e01060507050c0405041b0f0b03040f0213050a0f062c1803192a0f08070b15011b0822030803090102 58
    0x5002500444401049108101c802c02c4103101240d6455881028407640304043c1c4001420000504005241d580d2194400d11404403994046411207600c850f0804020a808008620701890500b00d03034041001445150304100700811010104001803187d80d402d907030018001d00072820181040b110b5044506000041410045070015880618141c80011508010511401c560781c0e51561200494240e1080b82c1c003005c101503030b9240071700c548107882c003e003002240050148100c0c0510001c4403000c4c0c10003258401601401200c035200c041d00148080090f0001c0f6020741c03642d100c51590000c0030360b1074400070300000c1501940865002d00144010f10550703a02044c21600344c858560300c0f041e11400d01c2c02c25050501000220f070000400c4080144120343c410b240c0081d54650601852041e183e0201c1c1c109440c5040c0615a40507107120b0440500d80300c8403486541d1907070b4010081c81102ca06c04d0b1140c45205411405101100045e0000c540255200b90307a444c00f4400c09000798841000c264000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 404725008 1250 404723758 404723791
    0x305120f10080f100207061b090e0f04241e0e0d050c0d320705060c0903070303030e03090a08070806150d1509080c0a0201120b09040308100902030f 65
    0x1c0001505000e40e96600014000b496114a4420007a504c8030800380c452580f51500940c0b04c0d00b182c030109014000340d60360852943d080c00c84404130000040d00382f40000c901007041c48041a0401c2414a02c0c03e221a80051014010006071000d40355200381d0019141c0d40602c00401c00c4940d82142c12024030303007801c0d2814414106000d50722802a041a40402e41c48260315841e45402402c00d01070b0109049502e8502d55030b180f201070003525010001050783c400c08103032141008010000503402545810b00c090400380c014010980c0d0b6050303840040c04160300c0c1c01c040c07036809206000319803400c0e0000c1d01e8400a03d0311140581d60380c41c464882d180c5503106540004118035007110082d5000c2d24001c1c000620740074a40c482494a030300564200520559991201c4001082400100b48440035000504111007481c0005031400c00d40700c01b42d8040904100c240a116a180f40c04643d016a240c05d010085803101405846454800d422800126100006000b211440140307081d11698192104050a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 404726258 1250 404725008 404725019
    0xe070902160c0f060503010303050714120403060f0501180b0604090f05090f0307050703030f0e030708100b0901050603040803072a2109090b030f06040804051f02190305120f10 77
    0x1c3d8001031082c1c0000450a00050001a200790f000b00012409008072a40030301c06512242d09140381441e00d07440d0180f0024040040084600410004911503003080107a580350000200307805c489007182910b295960384801c05039503500400d540140c030101104028008a64510000400098600c182c4a01c119180e44242c5000003084800e510b13032000281c203005180d42e42c05d4525096075020310080c8042c528002019407020040d500040c003030343e001441c0140d8002c0c0718404aa0400e4181806980c108006101035202c520460380c0240d400b00c1c82030b80e25507800600310345200e00c40381c06070040c0310f41060041c400c2081e141c0d64034140340540c083c147e1100d41c840594500d186a1010000440d100200030080050715038400300d10a040a0300781da0002c2103000b038181c14800112011520ba540114082c0f0150501044501c42001c1d49d01700306195a2007144082e5540f59048114605541200b800001305849001503400e100e40c1c448480d001d83c01d0008451a451204a5488001600c8404005803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 404727508 1250 404726258 404726279
    0x20a06050a0218090c070204020a090b0d091110140906071403040f0b07030e010e011407081b010902030303010e0a0b09070309171801050c01110c1b03011a040e070902160c 75
    0x545c840b50125460420b4543c2800084d402031105031050003a0800d0000318180d00e1001040384403035480c2e00190f1071a0514000040170308181c45540214400c041608142e0b4120341600314040d90800b01940300c15038400000c61511510341d004000036a140405055034000101501c10b44800d692a03905458454010304181d001d281e5010300042c1e88030300001c240c1e50003942011804d40061511540c13003034580c0b103051516840288101c4800ea800113006200110000b455a03034012903c00030b11070942c49400203640c0e4041805000624030118012510450140c0e10088114a000c0c280343ca0910b0111300290041c61001c0b02503031514842d02e00310b455040440119120341010050701600042800011140c03034214411901e420b642e42e0540d00208a9000e000c0d0901d031404030014401c50034041c2c801c1400d40e0307451800d24060780c101051001101104241c010324884180c4000410505201445142186d9940004462440016111540c990150406221a0107100203000c07a030359620300c501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 404728758 1250 404727508 404727511
    0x409020f0906030106090507050d1d0d140c0106030c06020105060f0a12150f062c060405040206070b0103060606110a0c0306050907030b0f040c06181401020a06050a021809 75
    0x2540049100550324162401e06201e5800400107000060425140d04203441281c2041d04c10034085035012888409030300b0320b405000c4141c40408895406403a081e000c1c0b030b5035036440c45003a5050120035a141e01140c07100a00fa1400800003800a2201c5a035071b007003083d185080740c05848019401c020003d40b180c01c00341c84c000c1c2851800740841c4180341c9001d03d00c2c07031000c403141c00c102c451140740f00c0d0405a140d183c3c02655000d0001f08400980c45113494004007400407500202d0360041030f0054145442c142660140342c0c00142650080313000d5a45100140c041d1003501740040504c00c4001c008030a00885600c50007c1c0e88003a00c40c1000b546903849050b640d0350b400d0000034004c6054000c1800042d032160849508403200e042200d5655441e0380e01e41810240c04c89122201140c81d400700400d2121510595000300f460341042c0000c220403a0070103008403a54061652070f400300b00f901610316403007000f8280038103400c85010013082c10008254806076001608800782100c11012a20062410610a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 404730008 1250 404728758 404728763
    0x60b030601050a021c3b060a0c080414090601080408221701060602010509031312030509030a05030705011104050306070810180b0f010f0c1e1e0312051b130801020a1d0409 75
    0xc4400e80c0546e030030011140e1200220604008181e1104000a070641000d800030b0005201e0700d292508001d01849420000100034a0400c5450014080031490074002caa90020900e1a07a1881c820003120303221260780145c1c49080c80c0c0314032520f180540c04c010f50008007a1480340e8001e20241e19200d03080359aa000b21442601d041c48035500812100b000d01405a84440c800d081c06818880000d0000381000c41902d41520640c000084500800100788030780420603405000c410f080900b414042603440380b0081a10b400e000840b40460540407140170380000410306c0300844000701545500403400313400403600385406030510f144c0d00251580607e5181c2d50b590b11680d241045d001d0107490b0b813914007072940c9201d003a0104d04249403000c03492400c0030302c2884000c0111042d02d030402d0314000746000d20030041d65481524240c180006030013010041c00c403c5601452613038540500140004500106030300034081076200080107614250010031800d201185030301500c03140d40888017400191407084000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 404731258 1250 404730008 404730107
    0xa030e2506050915220f03081b0c120109110603042a030b0a020909090a0c141807080f0a0b060304080d150b09040e01060b030601050a021c 61
    0x5101c440d1040000c0d10030f8000040010103c4451940a04285c0d400300083c42c004a84640c64120011481701340d0b8070052410800f107848440ca16144c00c0307401d0250035801c68400b00142d0300328500701801c10101e280d84500134038841038402c08943d154002c007800c00f0101c8620038594007480e840d26080054921440c0c000c03d415107103c00c3c240e4850f0411844140c040b4075003060980c0030010404d00c192662040540060040e900e0529a00b042007214001302000500d07801110201d000800303c0000710216011004d64400b000348a9000486900045101e0206042c8120401200940c045030342801030806906a41c500d03183d855858060300c140011180c0c200c1401c1002c0380004140320020306030100c5000700040e0b00e810448186030031240562080c084801c1c00310380750b601440d00744034401d80c0c044900d008001c0c603032230700200c03410f64000200441d0601401140c1002e4940c001e20002d11420b42d0500c000c0343d06a1121406020000449140c0c0d056400319040442f02c0c1c0e040301071401030380400300c0340d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 404732508 1250 404731258 404731333
    0x106120c1202010203040e0c03150d0f0213020904020c0d110303070c12050c0d08040501060f05010c0609060b0312070c05151209070f030f14031c0e0703080a030e 71
    0x100c0300751541910100d04501c010400000d1180d5048886801703480542089640c0e170603c2c07520314142c8000b41750224481e10307981c2072200024001c121032402095044d00d907449052a040000b40090060103e440d4005000040d015200c3d000426020828281a1640380a10b5060025203a8a00048890354003091541c07a41e40042aa0750725000f0134040580707040ba140402a1242c182400312030031030304c0e003c6102c8109002c01c103e004c0c05845c01900100000c1e1034014908000282080484c1102500481d42c40d06002c05211581d0401254244060102c07050030195101640312076000304820f81e5100c84020000c01c0c0d034506005608001290080d410341409451803041650040c0a04403801034420740b400002c201c805030610100560240341d01c42c00300f1a060620040034181c100b4103001c160401c00a0380d011806486211700c0708608008009000203100c81c4c0680340103010b40010f0039000d00031500c101010380c5078021841d01c04000b0700b81c401020242005120001d00000b0703c042902d040034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 404733758 1250 404732508 404732519
    0x3010f020c150a0b04060e090606060f1b01091704030303060e070f0f02010b09070f140a0f0c05070806040b090c0f0619021c0315060f120203041b0f05030106120c 71
    0x3002500300f429420001402941400003130222441503006c03014045546041101504084c801658020b40a450041c6000101910542d061140c50490300080c2000e1002840a4400b58031842000740c2c01012000341c24951141240039800500c000c41c0000e00304003001c6421090011070600400d003d498100111100e0101540c01001e006414801c41d1368543c2d828020341d5882603d980581c1c0340d91184442c101a018004107800c1748014038000c041810061075040e91f9010a40c04444071007403030102e01c01120741c0340107800c0015a0384004014030405040c0706c240710030010b00c18043c49158044480c4829000d09010124056244883e44410180101d00c00c10442101c0d0b818250b46920694040221401100c030200d10a8009000003d507242070180108900c202c01002910150505440310100b02e8401031108c8002c80c2646074054010022a04001204500c280c1800008035440d881589444815080c410240300745c074401d41c2841c1c000100003100080c10501a034101030680030aa0030321 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 404735008 1250 404733758 404733793
    0x3030601080606070609110f1806060a020a050f2a030c0105030a0204092a0c1203150b03180105100608130507082401170a1104022703010f020c 63
    0x2e00300b0350420400c101103030004040d88904482e440c807540d0000107030a0141c040c0604072155030281c500500100300c0c01c08014442e42411a8060030171181c6569603030207800c089040c1452420010074501c915034401d035440101056442c5201045001a80c02241001c08a040e00074941e4031580c05070003c02420865502c0740c80110b40c0500211005460f20f9620301d03400c0222044009107060020b400744003900c90303400c0b002c50701800d11050328102503411036a8684500560100107071005240d40c0d03000028041c9130b0111a5070040098118a50300c07031404000c5818218400981d00009528040c002105050100b0008003560640e039204491030341d500e00d00048881d41c5460540c0c2c98451241c0c001542641000711014003a8044041c1820070b00441c0c51402c41310b0180c202d4105d8200c9042e100c0744c514800203100a0284e00042100c11460707206020170001d20660700b200700001e142010941403990030100d040c100440a900801c204051580010102e001e25042072a8980121041800220b04c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 404736258 1250 404735008 404735011
    0x7031406100b1603091d0109060b0a020d030b0f0d0f0c09020c0703150605040501180510150f031e020a080a090c0302010809070f090902100c050c2704050f100207050303060108 77
    0x41d0030a064219114030b00001e8a1706c49850a0703042c81d40c1d44c80103000b51403060003140000c001d4141d54505040400c034000c0e4441814005c1801010307a10b9154107500e9807004402c41c004000581041d10700c80e6681001d003d403815540040d940c030540807030001030f240036a100b00c0f07a090b50345c84041c1903401c0c00d5658070b00156500c004100d40071625044c0101785039645104540c0209040708114400d5a59541da240985000400e501080e0b0074444c410480d285403810700030302c0c0034418074000c1d03031491179141c0c240c1c01841c40ca045d220303804000510707101c13800c03000b0b40c01000c1e4045035803a02c011583d10b42d039044050700c0400400600076000198200019409490030b107402c0129003041c3d0300300d40e490300e8020410001941c80700d041e190b01c90303401c9400d50600880c2c8120501c041d01e8160050f0321a0344485a45040807a04a40540e182c0100c1040b2a00c00c182d01e4007003100c110324044e815042509102d5a641c200c1000101580260900402c1050302031003200c000c180c5c000c01940c1550340f5040150341c10b060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 404737508 1250 404736258 404736263
    0x260703051e0103020f0d03090314070302030d0206100b030a0e0d0206060415080c0904050f0f0c01030b04200901050903010e031b2a0d02030109030f030501090207020307031707020307031406100b16 86
    0x121000c000c030024003840b0241d2b5180140c100101005891401014035040d000d20994065400040030f03c0540010750030000300340d4801d03200103681d82d01c801090b5401801758042081d0b19016800c50000c051b507001c1206801080c1c11602440700c075000f0300203c0c0301c1780700b103200d607006035400485541e2050900d1800c07294010b0180060300c0d000000c1900160030011482c10440c0c070b42d0420f050440721980c151140d184048030076101005040a14800c0e002c05078a8500c2c0081d406001080c03450f4103038460402c0f00d0409202900912101984c4001c25581390440301c1e84155078406103900360752443e0001075000c411124486a12403800410032040c4145105003600780e0007481098060f009624240a0100c009100303649000990844800040c00c640301a0000c10f42e050042000b0b00150703030001088800d81c1d0700305800c01c4100050146150308e521440100030b4060054510001c01c0c070120f020044441e0b00c902c41522900d030345068406121000d14050b030341d06c4a406100c1c024801d11400200f081c03451 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 404738758 1250 404737508 404737517
    0xa06120f0f0b0c0304060c0503091b04060504020409091e02221404050d20070b03060303310909020105041e0512010605120304030308040201260703051e0103020f0d03 73
    0x9191610b00581e40d040742c044581480000500080100d184181c0c007400d0300c5881e01505504007003a01c0e5881d0504400c000c010761440a10102d015a00d56000400601c8001d01c00c5540b583c1d80e0f10743e00045c1498401c20b540c01420b401061074201e90701030b40901c14580c01000d001d00040b00b03584280c15100f202d0708110b4510782d00c0822509015201074010b0240c1d01480c01170a0b800b40c0540014100c00c0c40b40d0b0962900b191000120044003400154407056a44100c40903440e6511000464518040c0d1103172a05154451415048510382103078007082040100310801401d80e80b0b421985054410640c0000d0016800b0401080845503d4039070f035450700c04103281c07014019900c0700058070800c058071422a45075910a000c108070701d0700000070020680305d00046c43c2440e10b951405841180020006418040c820b0faa4a60408006401c8603801560184002d0340d42003104008005120450710540100c01c0c0302040411043e2070707042e260480303500030410300402d0311120500c07041c8807900f00100c2c18032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 404740008 1250 404738758 404738783
    0x30408040605031312030b12010608101d030d0902120a02010e060904090506070305100509190e19031d011106190b0603091b0604031109180a0f06050a06120f 69
    0x15009641380c00c44a49680d5000c10f2505442d0308002e04482c04040c8003230282e15098007041010700110b442006001c41c0600003485200500b1400210754103c0024002030100003040f00f0b110242da40b11000d124001d4814000740c9104071440daa8840710404080e022803154940b14040d464080f000741400079003d403000ca0704021a07604d1a03d4200161000400b10ba01d410400c1900c6814414020003807508a640250354240711a4082000c0d25400706960034036160311580c83c2005003003020600e95031000e00701c0d840c2140b80d410001e004544078842001d011004500d0015550f11030450319083c01b083c07a0261600b6150460384462202a0f65814010540c41c1c4072030200940e150006507106040300c070040c00800d0450050f4800911101e050a440703040140824000714095500700449250142d031100440d89450f1450300f846071040002c8505481081c1004d030410105518404113544100b20a0210340c070b0f0004180c0a40d1a240183c40640d4549104100800c8403030b1024a42c240c024100d46901 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 404741258 1250 404740008 404740013
    0x31903060b120a1107020f09340905120c040e100213050405070203031303030c120f0209010311090303310f0815040b011206110a090f0b0304080406050313 68
    0x9070000002c542201c5102070030000c0c059810b01a68004185034400c4a00e420780769400104014141e05946018056000c00601c109440c03000441140032642d254580c034130501c00260b140301040914210000d90080c03c00200340c2007882c07102e1010704260000c3c254030a02003040c080188402c03005000c02e84924440d00c0c4185c00d5070b1005110f0120304140100f0b0b05410902884140c503005882030045500030030802100700c5c1c1c441000c0d04201d0307141c600450a030b1981d8904580041924601c4181c4500e054070400034240d40754000e200c2d09500f80c030107000e0403200c2030507809180200140c0d650160410046125a402206e00700982034008a903459190342900d089201040c1c4a50400502e40c403c00000f03001928040110866887c4890048252441d20f55504071003000e0622950310500b041028540070010ba5812000071140502c889540356080c0ba00c0040090320b90f0300c01c00140144100e00032034072041c01070407248125004066940b03000d2038484116841d500052100b451081c03a00e00c241d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 404742508 1250 404741258 404741279
    0x40b0c03100f080f010b030a03140f041503020304050c1206070e04110d090209010f030c1a07150b010e040e1c0216060206040c0b0a020c040b04060e01030b070f0203040803190306 78
    0x10f01040300082590040c0803042034210b900700503005109510440d89540040d41c003040c038150100b1007c4505486199101002161740165000f1f0208400c856442c552501d5256000c1c52040d801a0f007260100b144900c148000d102c46851151425003003080000e82050003404009010034025000149074001c0b18000f5420741c100c6c0c022007107119200d68001007949402d180e4103000d8040a800f640010785142d54060310401640310310005135070a03240c00e42c00c00041105841d515900448081c03030081500e1802c41c001e08030504428081119a01c8103001810603104185130b00c09504002d00401c0030523081a603510403502d00c400704521030000c100c0340c664540350200c0e0050041c2c2d0010026030509141c62503101d24036800000581c601800765880d86540011040c0749080142d90000f503954110300410003618003500600c081c0140d0703e00000800840081c000d12075195503882071094030491200302d071a0321480c89001a80d0f4014080c04008800300102101c1f00c1c02e80d8100020810b079100c2c800c0c40c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 404743758 1250 404742508 404742539
    0x70b0114010c0b06240304060c0504180908090909010b04050912070b060d1b05030c040c02030d1e021c05070e0a060f0210050a02070303110406020d080c09091f0e040b0c0310 76
    0xc45c118070210602c002c212480c00760a460b1b5526080030341c1000c1c10103a41d41d010082c40541d100c002e81e1580d8800091040c030400b12100c110000d00200498980442400d001e0141d800c8010b00580c54480018a04503002c2801006404404200c62501c0c2c001c0d20754404068024005031380c01400c1c8a035070000145032540300554826006200c12045180504150801c00391405482c003540c2024400390305a64080704481c404411501c3c0040c1b540c00340c11040038000403442c0b1000c6480d00c0081c0c0d002c0408a551041e403207000214205011a030f039001e004803103c0840b10140b40c1c11102c128001d1112501034081010110f02d81d20403100780c40000403c500030ba0300d0581c1d10442c03603940000c502051581c50b000d90003440c0a0762640f249810f290500003551110f80c1daa0a074100103140000c00c100002160884051550092900150382001c10500035804460703c01c000b014144500000f403005402c5c95a1440360350009503007401135076070302900c0b00690300c010308029001d02c044502040b410407610081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 404745008 1250 404743758 404743819
    0x1509150304030809010c02030702011e020c040c02030d0b04020c150c090405011203020d03060f0b070c0b07080a08090a03050d09080c010e0c1005032208040317070b0114010c0b06 78
    0x603045084c212599800c5075032070240103085402c20400d40740541d0f0043d02e00f0601c11881d03548465060000c420480c140245030410030341c040d082c000c01484651b400030150100c600322103000c101e8800c001d4108412441581b8152406030050429640680015803e0075440426440c1c0b26242a0440c0300280464009800ca9040c81080740d041d141419410410200740c51220704040000904180940b0f050b5101031084002c2e903207002071820b04101c101380001c0010448101e12985844040c41d1201168000081441c0065040d1002640251001034030304c4180e40c040c5c0350103140881503100b40c000b40400e07800c25102500204007143c20300d0300910581044001078409000e101c4181000c0000e0002d040c2060b004010090003400301d144000701000c05415240c080b005e1580703489262002c5503000e164000740c0b8001003001000d0603070f50040b0003091540d12903030099000d40c1e00c40c1118074244d00b03c502002d0000761301c0410a00001d00f00c80d400350b000300c1c00070108901d680305040b240f02101042c41e01c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 404746258 1250 404745008 404745017
    0x50d0e1221130b040201051b150a150e0c041701050108010b010f0509150705060406091403090a2d0f140a1203030b04200702030c010906050708030403170406020c060105010e150915030403 82
    0x610095074074040b505170095040c80e014003a6a0b022f41030b110300352041e1300485d0000c841d5903000c1184c00310300744200c07402010400881d960741010108111300812091103544d46da5402c21001d840151b21a0360501c06000503030702c03010b050100c00c00c18000f42100c042c203407203601c100800c0050086203041000750311641c45100046000d140503c0e10780c94111111901d6681d503401807189514031364440c03c072801682c1d01050509401c0882c034110002d040c2c420100003ca0750461040800c1d213400040328681a5219007481c84000f0400b1018040e400e0403d10a440303160f081c2c00c10600002e440394121a9624600a001086200c40181403104402248a0218196600203044011420309000da030607440b10900304000d4080c80d01c40050150700c00e0b00d40003407850710300200040070140128901804400c961224405030b03d03107840c101d0000c0d4800c1003180018071900e000001e242d031050405184055003d403100800c001049403059180d040002140d0740000c00c04501145459000c019610945c0207a48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 404747508 1250 404746258 404746273
    0xf0d20030304050a08160902040b0403031209060c020601030317040c0b0903070305010c031d0303091905190c0504051b0d0e0f0a06020301031502041401050d0e1221130b040201051b 79
    0x1d0380e440070071a9440301440c0b5005100c02c0084ad9041c02c25201240d070142050768881031f01d021043d004048211004041c1450907080306941303580061041e041c0c900c40e44500c80c10744441c6040b02e456217400c880c0180b840703100741000c2c0012076500d00035250707100c0f010741103035121074885d681e42e42910441000340c0c000940c1c5400f60148484450202c007240701d03004019601e541002c0031081e80702d00031040b4807081d00d540070030b0b4101082005c10140c82002990704010350303240749514240c1304603c039520400e44200d0900b008030310004600c00700d00340280480a0b12071701d405100b00c1500f0190070f0322480380c49540180c2900b51402d0409000401200340b048a005907290304514251303041e10218820805d0300c03441440140880d0304400c0c4860301c0c0d80780900740145c4400d5050107401c081d200126995543d4010300020f503030200c00e61000340400484c1d802e40d0b4070344003480c601070903a00305080703400b003044040403100040410345403041e19401034018940300d490001150608140c2c0514401b400001d42c0c0700ca030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 404748758 1250 404747508 404747533
    0x6090607140301051e1527090103030507020d0501050c09120c010906081017010203070908120304061a1002160510080f0a1401030305272404050d060b0f0d20030304050a08 75
    0x141104040c4a070680419074000347c0c1000b080d0528414040101480746c002000300540d55410ad005251680c400c000384460320b045e010300c1209402c010000c900600c00f00c82040d000890201d12250800e1040c0d4034143c03054548101120180c4d000341111819a204e20742c0402d0500c0d2100c040321002c52048000f50f581d05003188010940c9070307554003503e00b80c2c00c103803c4148464010421241c005820940201c2d07400112a10a07250072841442541d003d100017944003e100d801043d020780503000d000a14404030f99900c1032124921482c2e91100018440d100040c2c9903000700c600c6290010341c2c1002c001821600c10044401614081e00b064012400125000039007180301415003c401074103410fa5036040314a840894148691025520400030080074801251000001980d0081c40020040708171128141000c4004020030445213010710042010310505052418017143c04e154803032412040403980440d540d1101040c101c00b158140420040082c0ea0756980321100003500d6464090a040b50880 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 404750008 1250 404748758 404748787
    0xd0e21070806010f3209010e0a0b06040f05190312080a0e030f03010302010c021201050709031b050139030906022b141201030506090607140301051e15 66
    0x1640803150110703c821081c00400b45450301d0000a15404c0c4041010008245c0301e0458145001c48054020410000029940c0d54400e10303d07010b01035081c030070840781e000002444114491401555104091030004110342d00703114060307048040c0c2c40361440c07024649980c2d0b80e10141054404085c0011410000c2c800300111030710a8150035061303100210301c3d060000b60401d00300d010521010703042c490010340c0501075440d8442030700540e19140000b00607034501040007030701e056810300003517511080616003120250301c80c5241c0803c3e41ea0503140c0c001d40c0c00d1003000d0b5550724455140a00000c08030121019a6a8102000c07001014130a440fa5201541005002880c04482001c903c00c2c400700720001200c00ba50040b030701c1d2035040e86880c00715503044c60f1f407194103214490005403503414890140000240800428003901884040f400c1c2d4400d074840400c1141c0c070035140d031950400300e0001c00c010006841d1010805641b150050100310b00301c0003c00010305030007207008420b421200300007541308100809 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 404751258 1250 404750008 404750011
    0x1060e090304050108010b0c0109052b050304050a170f0a1214060d03140c1e150c0f1602091e1303021c050405060a03090501060e090d0e21070806 64
    0x40100075070505180c100001c0ca440410b11a05c034080c500042c0008481c9420b41143c4149078004c000c07224068204411941d40907040a43e60007601e10089080000511030b2040340d01490704a001010303509420b84a45c0c0d0140040701c01e40d8541c0d41c0400004180d4219580602001140c58a0751010008802c2c0c00e01c050354040c00712a60f02080010402120340e480c0c6494800e00c681520304407169607582c9121000710310403c2440006842200b45080d09410050581c042000601059a2000c0e80f00d070f213280c884103000e6130005d002500500000d81d5102c80b01c0007a00e0000c942c00c0c1c1003000d00c060340e004030b003104800340c41012100410703200003d01e00d10a44041900201c410501c600500c5503620020340368505038264034079403039918150221885c850010307207014080007440302c2e5440c071f40780c8806402010580002c036000d5017040350000f0101e034003082b050300c41e80d040e00c0600480c400703403142200d207801180001980a40c0f401c00c2e0808881c841c02c1d8070a42010f0b1003004085081c1804a0700d40f41000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 404752508 1250 404751258 404751271
    0x150114010e09060102031b03040815040c0906050105030106120f0515041407051204020f2206060f0e04020d090b01090209010905040e070e0702030d0903051c0603020108190207020307030501060e 85
    0x2c4030703424000d107641d0001c12914281420706c1400030200c03e50090b1402d600c610313406200a486003043c100c10b40703000200e0b40c50003036101d901800d182c03d50744d04921094608500c41c5901159040c0010426940100150a1040162078002400311000b034440b00c21101c0c00c2e14070800842e8003030090b95080c00c181c8602d1034035100b084010201c2d494440401031083c420012044408601000400d0454861504554880130024581071280050740c000c5140e075014103001050440c00c100c40001c50a0003003c0c40f400000c916076404d90120291418030010790701c00d1590740501c65650a824020411081c6154060034213070344003503903400d1481c4c001850039600e81c014500c0786103466102a11181c1c00283c0404440d91429028540c1d940d001c0140d0440c041c08817110f40c0d145c2001c4c414810158401c0085c000e0301010156190038a91460810007100c0582c003000340421140c6011400b90a40e07840c042e8084031090f14098500856580802d0422203941d0003143c460391a0a8180130481c62a00540d03031001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 404753758 1250 404752508 404752519
    0x1116050c010201110405010e0609060a020a03021e0c01050307110d020c0a0905010e010302040b030f0307030f1704050a0816061401030b0619030825120806010518090603150114010e 79
    0xb40c130603c0d40c1c040f80c4280c0c407400f0f050200000b00c83d2116103a540c03c0d80e0140000400958540c501c040000e919480429000c0300103008030442401c2ca03020581039031140f41d20400007000b80701c1040f0300540c0d943e40b010b04990103028940c00ca00030024020464070341d0410080c0d010f0310544c6100000e00c0f40c50039041d005000c1090404006204c0340000907101811650100d401003840306122012900f8055030403a401c02601000031098207040e00030b0000048140703079a413080c0c03010801000489402c50b003550700030410b8211056401c0403404410150800149504d207101d00070341c0741d541c0c030000c46129421072080c0e20701500042051003400341100d580540c0c1030702c0ca02c3c1c099652402d064203c0041d40002406000b02064031550764100326507034060003100d044a00c80c40416810310352080f070800b01420002841c07100005000c3c2d44a042a11a052285c0010381c4c0d145205404010780c9103001070803e50140700710800c1166845480800500924070031030084d0406c00d40c4800103000301d84c00e10740513000d131 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 404755008 1250 404753758 404753771
    0x90e0106020c0d23062d070816031d060108010c02010207080a030507090b0c100b120a0209040f23012003010b091503090708060a091a0a1116050c010201 67
    0x141c884404000c6032907400b0303001c1540d146018520003040c0080b041004101e20852003000f000308800141c06c4542d95038210440760204035218643c51494040301d521001030441070100354850f160240031f40b03110105060102c2c52081e00103d417821554004ca01c11101c0c0d12038801001b0003502072140c100940f502d07100a52134130003d0348900c44a03115120b280410140d82c1d0300040c0c401c070710500310b20b0040c15401d10b001e950b50340503456407540c0b08011900c1e0a5490b140c10102d403040e151002007143d03251644400380c103040b40179408106072181d00a0007510303008500044080001c0e00ca501d001c60740b428803003c1342001c0148880240c21610081c01c00600d07000b45090702e8501c0c944450942e811034403e50022592002140086060768245954561042c40040280002d610b004568181070b41d09100031540155100900801a41d2036031101030302c641c06d603038401580800b01c4209070b03a1080c1003440200303442c07844101d07804aa070300c0310084001020005191208000040c0304240d0f01050920003806203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 404756258 1250 404755008 404755033
    0x30608070308030c0a03020d0603030f26011404091a0108070b07020105030a1a0406030507050324010608040218010801051608040c09021b01061418010f180905060403090e010602 78
    0x180f002414020300d4220102d03103464021b02c00d4044410282c1d58042c00d1214996902d4054240e85041400001040c0500031498440e6203d01400c943d00e50380c2d00c004003243e4030b4a500c1040c29101500f40c0783e0444e85598a200c0400c24110b506482d082c00f88020081c00e40c54a980b81c1d041c51400c2e0001a15440c04004900c0540e034808196030b0441d00d1031400186080e03200240e06a844065030000f0b802900b058000000d011000c07c0781d07001c9a8058095a0030725404140001008001d503140c00c600c804c5d0303203006002c410302c500305aa0780544050072100a6454603246400305e20000da001c25543da460314200b00c00703400043c0704280203401e00c0c20b140344942080da48101007001c1e1400303105082c95001c1481041c4010703000d0403400c11461030700200b01c2c1c0d544541200380180f419814250080d0030503860040104907803840e150496401c1e01c40074404a0400c2074502a820030080290790312510f43c1080804154107001c0a40035030f20903100e8800143c6003030585614080140d00000642d004011071509 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 404757508 1250 404756258 404756273
    0x70f0f2903040201031d0a030c15110f0901020c06071202072102220204030b09060606040621150905090c010f0e0906030721060e0109031209020310050a0b010306080703 74
    0x2c0265090030003080e03640c0c40c00688003c5035a00001103202e48200c00c980400c0c03503000340e845004d26000b520504240000100a101552003803c5c02031300c8510100840e5010146030030107040c101c2c0c0148191841c6450f40000125a038000c4642902c51b010213862410701160104200001400d402e006040010800c3e83c02500240c0c0b00070001e4003d101c0154500c6180c01c4030f4510f100c02004201e400c640f210b88900308034034071800403076044103144100c030003085040c6051025101100c3d141d6680d084580c2628800d82110000c0c400302c07420580e25840c0309074030f0400140084c0c0203000e8507a00011079151028480d89440d5005402c0d5050103a00142580d5096018090b4244c040c01515594070549401c8082841c108481e44940c0c440f00c0c1c18042c242c0800030170b100110303c260241400307000201303021480300d08a851412001b00440e07841e030f0310388413904c82540241c000305000074141e80d0280c0c0780743c40c1c407400d5900c111000d9074241d9031600701580da503070548180806000640e0040c440e6900750394031443d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 404758758 1250 404757508 404757511
    0x12240108060f09040c081b040510050d15020c030d0c080a1b0e0312131805010f140d02090403020601180510031121210a0909020a02070f0f2903 63
    0x740142c80782c00004c0d00780320480d011500140350070340442d110b03903031b009040201ca180c1d00380c020b91040d410034012888840d40c8601150554000030a81444a003807942c85801c65886d1202d507080840d000d100d0400c0e03100091010b440721140c100400705034940d503070741d006007828401482950030514000c2c00070282d0610640e500039000c0703039080079401010355400280c0340241400a005034043d0024120b1030340b0100242440440701006007003a515103541040c00e065234000d00401541c240c0510081205401000310342404840c060f101e0145090160017044041e0021201907001d0384c0110010400d00c11419265010010f51207000c100b54180f2404159003070050344000f40c50b44899800752250755540004074007203201c0841c3d00c8200c7c3c220400d4030f140c48807444d840b01c0c1103009603411000103c41401c011160482803e0350741540035400d140303d00000f50009101030003140703d0f02c9404940b01d60309001c190301a120141d030305941585040c12000c5060220035401244844417818420201070703890a4a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 404760008 1250 404758758 404758789
    0x30c07031502090a08030d180f02040b0a0305150f07031103061011100504021f0e09040516090e0d050703170a140a020903010e07180504081224010806 66
    0x129840e620641e10301019001c1d24004a5111804e03c1002a40e610008010404131070a1902070010b505a000d03102d600046003a000381054444c01840d40040c03400e40e06c0440302d001c0c000c000c4000790ba101d45860340781048060305505e0030304511040c04020341c196031323400f640101d1600c1c00f800010342c6000c0c0c00d030b410b000140c409800743da0b00014450100b4018801100e040000108442814443d80810000b40100ba13078168001e1504403e010001d4410321186c03040980c1b80c0d260103003074441c61402d01c804100024005e46044c0a04444042c0c02000b0011301001800b05840102e00c090349851403500f40a80300e00c40e0800d02c001003002c07400098011541811401ba101c103030364840d688441080000e4071a00e00c0c02d00b040c0120900700f208614903035000d80035400098008212000e59018055650490f5001d01043c840030300c0120013488040303402440c0c0c003038458604075003000d91180500d0203041040e60514103030f0301117034615a00000600307401014440d0900c1c040000f07003404004107444a4104030785 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 404761258 1250 404760008 404760023
    0xb150414030c181006030b1c210e0a0b2a030d14070809160b0a030209040516110c0604090c0216141201200a1727030c0703 54
    0x41403400d503000e000e88150458007408004a1000300c042441c82000202c03130b10307420b040d10910085071031482882030120705071000c3c10031145424294803031684c0700c10009044034080b690b0f8246c0400c4811a0b4981031f1030380002d8403a18a400504020807034012070b070790084801010244500c06d000140700141440720241000281030f0f400b0760025060461041041005459080c884c0c00c2010805001400f4816600da5440461945400b80c00c1601c0c1c001200f05024201282101441804120300081c4050445800d00500c0c1450440205081e0340084850202035001400c0c00c21080c0e401c54001c1d0b00c210241806000c10b49900d0f000105540140d001c3e00a0b010303500e400b407a141034000c100c2c100c03640340a008401c8056607101c2c401015030702c149040d9800382c18542d9201d0700645050040480707410230b02210000c00d401d030501e0700a981d00203d40c00c60800055800c90035a81e11003c0000303001c1e6981508130030031040d4061480c0506c9107900c40382d41072a4020840e403500c1700000700f1400152a4400d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 404762508 1250 404761258 404761289
    0xc03090f011404060905120a0b0714091f030b09040b0708040f0614041110090512120a022503031e020c040c0504090605010903080301090b01021504060f0b1504 70
    0x4884021808074031102d02e800000700860340a0300703c0c00c0c000c01c40b0b004454024034010140b0310a038450380001c000405240c040800b00340f440b40a01003d00902da0303039520541c2807940000c005480c0c1100340442c50340c0801000c801d998100e6060180600c4008250b556007800e05180d5100b001d0100010000010020000c0c0480c04000014080ca640c1d035800c00c400303100600e18090080516032081c0c030129110825401d074a03026003805580140340c4001504c40300700300c84c50007007840300d49000d0240308500c42c0200c051f100105110080546804071459000f8100180000c40d07041100281d40b030007074420a5441030801c00640e0100350401c80a035003a21380e1121204030b84082c4e15001c00441c40e00da101c0d08007504040c1c031550150207001110349511b000e01909a685c40103484c1b14135980000b50480700104010b2201001e1500400032078038040c81129a95400383d00c51000071442518211040307038542c508840e0300e146034052800d421b6001c4920640132400d50940c1d20030791145104040c0204460407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 404763758 1250 404762508 404762539
    0x3030203090a0b151306080309010309050102070b1e01091406281202031005070f1110060f0320010806010f1b12090807272307020708030c0309 63
    0x801400c10358002400f4889040c0690030f01c01464443d103009000b0007040000010810080c0030b4882103941d000041c62914030400011000707404015025143d43d90200200d1000900c1c3e83ca88074481c1d13800ca211550001c0714807100524070703201030f44014501d504003500416003072600074040303401c090200c0d580846070030000d40740100018071824a075045100c1190000c0d00c10b601c08240d4104070320803000d0703882d2440c03880c03116412690140c84100024400a51464050b402100365240500d032000840e2943c00b0b080d440f08069564039000000b511004420070401c000007a03503040c101d50b101140556446009900080c0b4800300244050704110103100c0c10030002e8010002c0a250062038600e200b00120203003400340c0f0003003d5540b408005813141c040012f50101c080b07441c4054845400710903000d445003102180c1d0942074030340007a5602d03035910341d6002005d14240034001411144411040300d850041006401e0080541c03041103070750001c00941044001c0841241c07003182c1d00301c0e5003118a0342801c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 404765008 1250 404763758 404763763
    0x181e0711191a0403020c03010f0227060c030c070f091406041104030206071a010e1306020304080c0105070207050405130b01261902090610050d0c050c0a03030209040c08040f0303020309 81
    0x1101c2c0d64a0890b10701c080c0300526a000c206113003000d00030380007444041c04107000b1200303e104a0302c80c8031195410540319100703c210010040d1200c000100418280303c201c0c4803690440d8400648007185074000e24081044020089811005220301481003042c0032046541c0210701e04010015032140769078078035000b0403400c00360540c1e000c3c41d00500b100340c841d5924a0420700110b8094081d04030240c807680002071040c400c05465101c1c100c5000e00165280b682d60b201e00194002a10803203c91a09100d4458803140034031030389100d6410342c1e00030b012051501d01400202e1707601501203035804e5400b000a401142c00003d40314111582002c18444904100d00d400c20742155041504220b401006020f40c08a50000d0003100220300803500002c964640c0410002c2c114080403200307010690074005100e006640f9071101c980031110f03045c080d207000344244034071341040148681200440d501180d9410355040520607001103006078104218540bd054680d0504085416030050806400200041910009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 404766258 1250 404765008 404765033
    0x1509010609090f1b0f0b0d1404050c12120a14040302040507170703140609060d141b0607080f0a021011030a0c020d120b181e071119 58
    0x106401004250b180303140039911600240c0066a40c49856030b02048a4980082c40800721643c0c4402800d45524140903075260390042e4a0031000155502030b400e142c40d00007a0101e200e68400d1000c0e00342d2001030410400d03c0d401851040b02c1551000d5001c01440701020f007183d400111a00703044005029100d001881446140c000942050a03c3e00f440f5442e074200d4180bc642c04501c203003040c2c03a9070f601c0750100c0807552403986020800151001050182c141502d060390840406090404030b01c509485d0861203c86625049500360f11000700d0802800d0b221000c2d01c01d8000841b0b186140c030a07103485070043d40c0a0a00c4130aa10f40001402c0d03c8046d001700884041300c1c0020344144507046d483c080402c41d81c2c004440e148541b5051044110040b1700c0031034011640645512001052034560500304000c04c43d1800c456045521120502c0802459841052043d1040e000d440c0d40f518049450519a600142251090010680150f481880c003c2040d028000c05c0d125040d4800089040c00c484a114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 404767508 1250 404766258 404766269
    0x3080601050d1d03130801020a050304080906070507083301030209100f06020a0b01090c1d1512060a050a0b251209140607050705060c030909010807062015090106 71
    0x4458100241c01d41d002c4080c01c65146000c940300c40301ca0f1b450003c0342c00d07485081000800540f0170400200059448000f81544803400382c41d642c10b000140d0b6a15207421405e0b000100d007984a000d81c05250b5098250021812690001c80164580d140704490707045001808020b00c90016407001421a02000ea0b03038070010444801c1030a0025a1001c000e5180c41d0381c0c0c08142d40c5420203100100306400c04e03004035040d8196564504101009180040301c90711018080c070ba5002d102e6104440f50304c2c8008001d010b03d5600a400320040742483c8007040301c200d500d6441310740a41c0c01d142040041c04c5c40f82c03055410034001080310b140d02d402038080302c081d180f03031440d402402c490f860302010742000d501112203010f84e4015060348129070052010403245018032100180103510480051145003001300c050410000200308a900f0402140001003404909030403a180c664001c0000300091984000e00c2190000d80d950800d900c0a03820542d039895601c02e8041d05101076283c40130482d0740c00c096000714000e05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 404768758 1250 404767508 404767541
    0x605070e0d0c0806010f180c020c0a0b120f01050303180d150f0605060f04060e0f0a0e040c0501080610080415060f0f170601060c06020c010204091d0a03080601050d 72
    0x82061901184102a5000d280503038410360002184a01820f614803081d1100d80c010401707050040000c1c1f4018000c105e00000460180380918801c0b40c403410601c0c000b80c0440c884407621506100142d07914480028020400c0034001c0c801013040f6240881180e021fa040500b100090a0455000c0345912403000c40080940081c4041c3c9a0340450341d600c0082e8560500304103214455450041000601400c1c0300c1740c510300ca0401041281901442203603583c54006400f5400300d049680c001803071884642e00003d40700f04031300304101c108840014030324003500e000d080c40038080c107014000c03c42440a4401131424132503008042002d005d0200f914100d40d4001c00028451386480c2c031104c007803000a86c410341449001a1a001c00d0f0348101003000d820030070282c40103000980c03a001c411128014160000d80c1c003035500308010b4203100c60a00041018102071000842d402c401f000405810407418080340c3d80980000c44200c00183d8045801074000320700b440c110381c8810002401900501500c0300129500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 404770008 1250 404768758 404768779
    0x606030c0308030a0507020601241103030103030c0201020d05120606030402040b030f1c050c060a0c1101060f050a230609030c090a050708011707090c050c062a04050604030605070e 79
    0x402150b0066100e13207180903050050b0307103503c0000d903501c0d80c4c2030041000d00b01d10016240165641c01c9a108001a094980b4044009400d054581550310070380041d030001d00c0350100001996010006800140114a0480e02c1c0c4116084c10b200d9a4101070004c0d88288000408501036680390f40011920780e00003400e940300e10321080655a980c601440c01e0b41000f14100c40d10804043c01030040c0c610483d11307007015200980c9e4a56002004080e00e01c0d03404148034001950542181c0c00340300b8580600303098000e00c2011400c03d003c00c1403041d0142d01c0414200c10208000035800034015210b0090401071310303404d860b4604d502c0043e0400710501c64203a00402e6003c10440d41c5066030300058021003081d103804440d40d80b15401d1400c203007140e1040c06920751191104002692445c1d01219519040c2d1030858180b07111400220300340345e81501d80708a0b403c0400c1c280c3c3e008102c098803a0550884846200d4030b0117140c8404181035004911001e04000d690324005071849014081c6c0442d64840140304800c1d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 404771258 1250 404770008 404770013
    0x120a050402030c1503060402090301060b131d01030f060e03091c060b0301050906040314040302100f0801090618050c0408010e0604050c091b0903070e07030e0c0409030801120606030c03 81
    0x2440111001d911074414001543c44606201c1c40300d1000221100c5407030300d160358036002c2c000607601061802d03805640e506c000040640c1c644015182510b8080c401507200307427420380340c0f000502604040b00c082c98010001040010100100381040f03c3d03202c080031070b5100c45208a20700303500401300702c66000001c85003039100d401035504403508050300c1020204a0250b861041c98225030302200c529a01354840c1020034003080c010340000000618021046161585030340c007042d18251400f000002003858000d81c1c104094101c05440e0251040440c2008500d02d01a4084100c07050385598201196980c004a2010a03100d0100c40150104c1402400076001d500d070065070385c080888090307070b0901a10002c080940313003900702140100c4000d80c111944c1c5030655803c80d000d81c4101c83c0075616228a00340020103a111090440c860340d01c48c2c0380082d00c4032104001e5802c00c4481d41c0c4a5201b40d1400d46114002500202202c2c15104400d00d007450f8102c1c903161040c0100410740014014041d0100c0000c02c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 404772508 1250 404771258 404771261
    0x6110c1c0309080105040b011e180621020303040b180607051c030e060109020a051b0105090d0309390b040314030703092c010308130f12080a05120a 65
    0x154144030b90786080342180d5030070f030b19030807280d050f81d008090402c2000104114040024004c80340000e440900304629540e400303031a410345111000070350fa5600d45104000708401c21140020b079400c1d01100b903107205207590000b81c0700d104601405403040d80c0410049101046e682c1c0441c3e2401c400388c000e035600e008900340540d407017580131610b0112440321380c180b460141c070038094108081142001420640d00780004c502c040d411074840c482c10088184081c03800f0114684d00704030281f03802c4c400010ba40c02c100808a05001456610300300b4181031000300c4000920150381200b00008007030125800c150f01d00c2c0a04603038440144540301c04040840003040d000c280c85c0080040b28460b104000c201c078200b282241e164000c68038040c000c14410f00c0b0130489080c1c5141d09040c05501e504185003d03581c1000c9500403040280c01c15940b060011410f03150f040d1515014901030280340d0359040b142441c040095210b01101c7d00d004080c81f001042020005018005640107031800941d42030351490050354800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 404773758 1250 404772508 404772559
    0x3030537051003030504050f01030f1d07060e06160203070f060815010f050d0914010e06010302031006030c122303031e070c0206030907030212060a06050406050a06110c 74
    0x36a49403070700022810122442c05110112541074076400e040134600ba040007151494070b4000da0505480d0ba00e00200d294482c8121b00300110b0030310020711008209464140762510541240d400c1c004954204136240c1d945400380c0d481c0d404030189143d01d0321024404a420302140727501240c40d000343c42c0b0021605a0b00070384410300c00c1249030440303c18585800011100604070110f40d401048003004414002005c6400481c11540112415100905541c1c1190b085410070700810326241c101000600461406024202c3d4602004101744042c0741161076114400c0c0441c03007400103ca00e02415041003001c031444640c3e46416050f018107055003403548031030f10ba602c11124603140b031544510b03d071000450400094000e60f103a0743e8028101c059035007800815030009d00131510341e12590700b0000060f40c414042d80004c9072602d001c0e12060501346000c20642e40c0c41d4100e0303403080b81084018000e54444824000071a00149042e03c01e14003031840c00c60600014035000d42d001001e0f80344030400844240c4441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 404775008 1250 404773758 404773861
    0x10122607030e03060105010c060f1e0204060306121e2d031106161b06150302090906070e131401060207060f05040b0906090121050f06040c020a030305 66
    0xc0b25500a008040d01c403407090098030b0110340f18540480c0400c0e081e038840e146024185000040340c0341c409001400d41d005402091f078000f80c0029090094a503d07000d010011710700c0d21405442c0c112203a84042e41d0800301c07929a5220300000840109110004c00b207805030b20386507841e55140d01018039050100c54840350041d00412401d05c0d40056103000000d482e0300c43c41100b10450080030004004030358007440c1d0020041010280c3c2151004114a481031b40306003454007491125103850342c0b062000300900200b1a40f5590040340030000c50307a0f005483c003640342e80116401e00b443c50116a01ca402002c91500c992011103401001007072042d00050003200381c03840354440310082da074903d4007241c00780700314041e6418a10050015804e5410030300064020b135101410101542000750b01540e50b9030149810490a05890740140b20001c1980421144c01100a407420f100010000d00f01170342e554015240281015a540006100c1c0559007401c01010025848250140c9002019451000d1200d0604 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 404776258 1250 404775008 404775017
    0x9060109050606090d060b03030d110316020d0206010e06040e03030f0702011d071e1a070c06050918060f10030e010b18070c08310e1012260703 63
    0x2c640740d480c0c1031090340c0e01c42d00001c040040e00c40b407541d6084090b01e0451003064051000b4041e08080003030701e0040810130220125607607100d02c2c1c0020482800c0284002503805c1d90440b9015002d50f50f408035285054902240d101c214689904001c01c0081521700342c0c01070307980804014000030f076400d00c11950090b02c40c1c1d40217110382d021400c80c50040700c0c0030aa0321850755010201c208115400401e41c04805000024003070700341951407408200c062a1020300710103041c40010480104404104490b000c1c05d80c900c0c03d02d0030b00e030040010622804000700f0740f401044101d00055403903a01c5800c4c1d04440c6030081d00c0c00b803050101c084081c1c0640070340c9110001035404c18214090324109018200f441500c1c20102080d6a1a40719060724040a43c100a0321942d10810201103030410300c60130303c0c40b031115a1500c0100d1181050031545842c101e40c220102c2284075205000660b110201c496003900d401c48084100c407845032070b151828800b41640416400740141e8240f00003892400904202c0b030181d243c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 404777508 1250 404776258 404776261
    0x2506052a071e0605010e040c090507090e090a05011529040303080a1b0e120105060609040b12070603060f150807080405010e0618010c03020f0a0f0203120906010905 72
    0x10a50500d4603610395808015410300544000c240101d18141d1040c014154520b80341032140c4078007041c1c5009812480b0541c600c0c00510080044e990b1040000740422841007201c0c0c140b5500042114599104080c00d2032100e102044104106022815149034800c000300f00701a0341100414890041d407207011010356010070164902e1991900011010440b0884a4034042c1540d03820f0f100e130705029141014455985140c4000061288550304101c0010345404000c06030340000c0003134a4031845044401c590400f81070040540f03486050740c80e483e0040740c01060000050022540145d413144079030303880744203289000840982581c084020b60f14104501191180c075240e801c4820054500c0b10000208000e002507142413054070803d8120f4840c5002080e101060700966140140648420003020340740d80322a00740d08000d2140300642d0009007801c0d41401c400b0210f11109000d04480780042c0070114420342d0703899200b0700c02c8812035164402c40d803005003007601e5960313500c81d801d02a1b401d42920300b20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 404778758 1250 404777508 404777551
    0x3030618090507050402070804080312040204051e1b1c0209030c1c08030408040b0a0806030d02010e03190519030212070e0d1115270a0302090705250605 67
    0x90901e40d00c0e0414010000701e0700c0c10302440025404003900b540c0c0b5290510001c944c254050004020f1014403e080c1e1201d41030600410048990183c29100e0008102d4005080c07807401820f015481152040103080054107c0480b8900d8070035440d55502c16007010b041c01d0210070441e800f401411000354115102c1c04509400d010001c80e0b0782480c1c81c0300c2c104240c0c104002a05400c029503202d8403494081c0d00701a40c420032050240c0213100403c010540110030002c050404110407246c890799803009100000703241007110f03101c2c807a01d00110350500200241400700380c0200c0449500c4101d9080b184070401078030400900940044000804680f07050011960651081000c00340381d0800401036a00f04410f030781d806d101c52000c0c004403170300482d1175000d6020014412000d081200f04150284002031141c403181040520800c0e0b00038850024000180090b0303c494881a41c000814100966554180081d030003100c90503030582140142501414020400c0c941c000324003824034554000044940003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 404780008 1250 404778758 404778761
    0xf02010209210618150712050a0207032c04110922051513090302100f0e0601050d17160209070f1d031f060b0408150901050601020a020904020303120403030618 70
    0xf00c1c103054603170059071180d0b24401609140398114500e41030004505103141c08643c15220b0444074110f07842c1d8081a100c0902d5007000311021050703881c1c00f0340c1c070b0a50400301c0351050701c0210000d45030040d5074414002d00c407411500207d41c50410300038000c2070038034801a04515203119504425000fa0b007400085101d20310381c60200e00c01c446004004111047c0c1140c1e07c01c008001861050703046204a00384607100342028402d40d90b41034102103006c0f039604605002d4a00c0c00c103041e80700500031501000301c0310204000302804901c0c445400c890039680c08040402039100b00805d00040d42c481c3d100414442096081600f90081500584450b6900a0b03c407075194141d207441001c075500344c0c00100c2c1c131002e920480000c0205403101d402002522544500d5411120780182d04013100c1d5500942403d1070f2605044641540180300d14020300c40b9203081e100007500d0341406140203004002d4840030404550b07040c41070344c00c80d0000012a10803454241801809401075100750b0310038900000c801c42640416 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 404781258 1250 404780008 404780041
    0xc03160201060501170a0f0c05030115140a0507140102031f06031505062d0c0f061e04150911010810050a03120912060506010215040209070f020102092106 68
    0x50711030a000c03000810b26503016040c01020707102c041d65114800281f004261003158007107502540c0e00c54a0303606000401c5103405014009005201c2041030b0903150201680860b07407080d110703240540d200c0c60185816a00a4404075450541c1d500110402800401c0f000300c030075032005d01080415185175102429000c0f155044c0740e200345048084014406810050001c00e190800c2c00e0390840d406005e0401081d01203c01150001d4440c4009240090f4001c200400d03d00b50000001074410f43c20400c5041030419900c4441c56442d1413400000750612a0408086001039000359062040100d5480c010b2408071190007546d01080c02000070403503400c83c101820b01a40e1b40a0000c200003030560301c0e0300111100c0540c6000030019544008503c441101d40346400503841880c01080398108040007908084071000265a0000380340300b000090b0b5500a456030700452141002049440c4651080b80607103c0e0414403074000c0103400e1107022440d0014500d09030240c502c010b45240361220724940703500b20340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 404782508 1250 404781258 404781269
    0x506070506070f11120408060708070f0f02030906030f04173c0406050c21190c0606080a05010b0904081e04080d0519020a020102030f0d060506030c0316020106 70
    0x4888000380341e1034040d551802842030326042c03151a108500811318503040702008000142800840d082110000030006150000800e0514591074580403a00510039075242d440700c0204103188107040001c600a0003201c03080e00e009030040d583c0340382c102e00c00d640b801c10548048403210003c0415243d122000340a4440204140c842503804112003001200310940880e2048080d0b1003442009134000d412034010401003115440d09622800d803d03450605000028117904600a1240b00601c05482108226180300b070490205420900340301c1012103c54811300c4000700100c1c0342080c0413403900030001d00305a07018869002804514615824040c084a06030703001840355105012a00d220003140c0700032146103980800d1541081e41e034501440c603220003c3c1d8004007091000440040205c8030620611011035140000c01700d0a0a5a0000f5075034481c2600f801214980441c10452014183e0000c400806009003c543c9034100760800461030360041d02d01100c5016210b240009090040c02804120745 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 404783758 1250 404782508 404782513
    0x9170708030a0c0c051c0302190b0c030916081b1c0215071719020a0203100f060513060e13080307080c070f0501060e07210e0109020d0501140105060705 67
    0x105805010b4481d1140f4120880c0c03900b9400078042029162860143d0000c007400032140c0e804055030802070704050004904956480304040010042100340f211070ba04170140500741d40c2d4035664146211f081100c52528205d204403c02e000080000d8000340e0325220a145a40100c4441d40d68000c01c606900c1444844001e05501080c0c0400b46c600b01c2c510130000d6140e540170501e00101c0e6522140f00390b110400e0b01a00000c0070604020401e1040c1d81c640c01035205000a1200c0c3c8a20380010f42d8030304010624102c01c03500c07100f0158000c207903a003001e4010003001e40355030401d0034045d041d800503108901888002d0401e07480003a2042e00325411000240340c2002c0304a146846014048a00c0d4500501d00c0048100402105001844006006c0605800740000064080c141200034202c600040c0a52040102c140545961b044800301c14003088411014009482e1050300e01c1e10b405050541000f940c0301080d600614280714064202200c1058024883c1000380c0e01d800070403030280645003000c0e040d076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 404785008 1250 404783758 404783767
    0x21c11041b1407291609030201020307020f01031803110606010c0317040201050702090a020d0b150a0c14010203070207090e01020f090f0103110307050702030616140a030e0d0917070803 81
    0x500420050107840d01551081c0e80004407031402e01000314031001499a071307080620410410b004440110b0342402e034140781252890b4078640000390380780101e11010b0300c078003c410f10028540c1c0c005d40c0464140c04d0002001d01405446082c0500788042c0580d010803240034030400181c0661043c4010b03507080d5456292003140110b00303048000b1000000384206d0500604111800241e40c40148803482101d01c40c201503914500f54403c1410750b210540a40d002d4141d0400c00360719004420b0a0b20380c040400d1a14038803102d00c0b1304010101221035200b03103029500c000b00f44040603602180102c20340c4c00782c401c103226144c4103482c883d080b840f071b060010078148070900403c841c0340303401518500ca07003a05140c04550401c03030000c40c880c1503000380e9000d0301180700095001d046040900140d6848200c00107081c110074042e807009071455080c640759506a0200089040c03500e4080d600541e0150300080485004181d40c60002c0c04400e0503004040152184403441110040c002488030141d50b050750146051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 404786258 1250 404785008 404785037
    0x106150507030f1b060e0c01030c0e0d060b21061015050d020d0c110c0d050d0509061909030308010821090d0206130302040605060c0712021c11041b 65
    0x341038001d603d91041010820740a4461400540e224034603a00441000a800b41404000d6141005c43c0320103d041c07500303158154104540000d4030201e8a081135510400b03448070391600d24014100326091981c8a003206000c042c03910340903c81e46030035074042001c03240c281d1146540501082c00e284107250145040c0340440c41c0151292015008041482c0c002505028000c114001034407242a000c07000100a8184c0710b04400e010400d60300c0082050300c281101e05001c0c1c862585400c07495490070300f8800c000070050b0701915420110b030307400c1c0484541c0c0100009100c000800c2012a80f00a9000452400000c101c002c00400e80b0f140850b441046011809550080c2a9460b004a500c40b940508007900042c096140d010040100003010b50070746c0501429441000221420b9070407440c054a02440011010700300002c46500781c2d22403000c29441d00c40c141c800601e50042402a106210030100326134800c00c854000a0043e0a904540502c4402030340325192010b203000c03d102c9030005a450000701c91 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 404787508 1250 404786258 404786267
    0x18060506181f050d120219020a05040c02070b0c03041a160b0417040b0d0e0c030d1d06040902120604020a09031403071403040312030213140a090f0b03010615050703 72
    0x802d0300c000c44000780e00c42e680c40014404100050301501d035001d1015811400c150b05001d0411080301e1104200c0c40c54481d40c000c91b41c00e101c640103060245a458911a552600800503200109080152030742c0e02c140d00140d20b07803a41c0041c410344ca00c403840243d1400d0080f110b24266a03004d030314003500842c5050161030303000c89610050310a540d42c035401400d020301d41c102e642c01080901031388146255104606d10201040303e10000c0f003803a00703410203058942d240d030b0003144d4110300700010716041500c4070320125840b1490101ca0030940d800705000400080040e040d4015100d02c00c03048a0001e4955070700c200713002c10380c424644540005003c0c00403c0c00041c41c0d02030055064607440049a05102d0a0754582041100ca034011045541c004034080003003144034040d1202c01d8045207030643c14026003031013680c0103400e540600580302c0c03d440714030420340d181d2986c0e101c01030400c80b806021100c400081c4000034114813450074025401d01002007800c0b024a19000301d503d5640d690b01d4a071031025102281c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 404788758 1250 404787508 404787541
    0x503060405040c0302040e1e0f1213120b0601030b1504170a15140a06030506060609060d0606050d0f050405060417040305070e01090507030b0a03031805041806050618 73
    0x30b412043c00c9802001507100da100754426500c3c48402000d11150b405000100d082c0841c2c480129980111451650304a010503104102c10102010f85d031589a81050036096555030303000703004000901107025007800764070001c0ba4003400007a242041010148403d010302824041c6046d9035043c020403080041454249410200c0c10911007a9500741e2065683c00c02441d01a4041d680041d44803030304400f5640794200c4054000c030030301c903080011914564a0980f191401010140300700c2f000b00b0303103c0c80b644800003101c1c00d545884408110080e15042d000c2c29a41121a00c401c0691410003100c0c01e118561150718004c41d0004020080d55840f5510400303028402103646401c2e1301c0c18000040020410000d1001501c1c4140815510b50b04255201c02203410044c405420103092010f10140754039640707030392400e41ea054038010f50074180e0004140c00ca0180c55201070b40040c500b0b06211019101c140005200d9803007003c00713201c1c5d522000c040110f02e906503600181180c0d03881002c00c03a4500d0b0768a048 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 404790008 1250 404788758 404788763
    0x1e0e0a06050d0f0b09160e133002031804090c08030301030c060f0905010e0d0c0815010305010e061006031a0603040f02010305060a0614030a060b040303020a030e040c050306040504 79
    0x120348140c40380d0204030840d007003120840741d10051032482e5042100041004d94072800742001081488039020f81c5030030801e964450f003111500c080f004104e07404407000282c00c055800030750703540030f08655840040001c100308840310a00c800c20314030401024800f01c211a1040c103100c2540304248407180070040100a4404225045c8588a40005100e5001d00c040c1d0700841c083d100460855240140290007480c10003600e00070880e070280705212507138000111307000303004050703540b91001801444c24a804200c50b4000035403a22544001102e145510250a810b803441140203000481f90241c00b80d0303440d0b0342901e9186165940c030342c1c2401428865808424184081102d420703101d40520b0100e07005a2084d10203641440d0b46e01246025540c05000341d0350812815904441d04515002000300030011692103500c9101c0000045000d0020079000030026101800c1c00703503551030752803402a55600c0e440c0d03c204c001c92000810f20740c952030a4800c55411103040e40f9890b01c1e60f034501d01004001c00c03009004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 404791258 1250 404790008 404790011
    0xc0f1812010c0809060109050105091909020310090312090804051e04020313020415080c100201091b06080c03010b0301050d0f0c060305150901030203030a0e01170403080708011e0e0a 80
    0x1440da062009009001000500740c81d43c08150034020780007070400c00d050300310f100c41707604060040060b40c680c1400d050b032014640c2414460703c0030a400f080041c00103450069450b105031511142e802c0360700d42c4a105d00505c646c03243c594900340e1603150001c2d5450b10301c0140a44070140310400503400d2100320320110500703d054a001c40c00903280007034203d8000350f0300c5100e034458403407054085051512070000a0002488040103c5180c010141c0e6621003c0440900804403881a00c0c0c08030700075013001d035540e80e0100276180e1810b400001d031700005100b8032958000a6108021416808040040f6810f8540b020605032442e82130409002d01a180c41130200d60002c102c4034554007141140c0788c050041c190a5030007040504150300c0307240304840c003100d000380300d0b040d500010001a0b8001080390164111401c002049100300d800580704e81c0880c4c40c1000c036071240d010400040641c0001d56034843c05441e29921880d0740c0703c01340c00c1805e0042c00c0b80f800c0048080601401410401080c040c3d201905450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 404792508 1250 404791258 404791279
    0x1d0d0b06031009030801090506120a0602180909010906241217030f040201020c030c03071a13090209010f08130b100f0b0909060609180a1d06060301050c0f18 69
    0xd902c0c01c0700c1e40c2d140150009081c110051056445d80d00946030007203001c0f11105200390450912035164001440c00030801903000500450901c021104410b16550040244a4500d0035408090203407020b0352003102c20611f0300140710903400302480c170704134074241400e000110a0708212205488000540341039441d404520050400591003400951040201004500311801c2c1880007a1900e00d500f0380c864425005134a0ba000c181e14002121411110a06292032403881035803981d0713000d80720780102c0030000b8010440114080c11580c000f0304a8003c280c3e5018401c0301600001c865003902564032003844200c441c1400003141c5240d64164100c2c05050743c00d2400382d80d40c000070301d4104450340b00100c00c1e90080f0751030302c080c680445410b42c040d2081d142a85050504c00009091112000d54881316040640100d00f14607042d81c002e0000740358540001e001c28105032941560340100f128518402e40c24540018081000001681d03c1040550844c604100d0f0005841c440c030320005154a40000c0d4841 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 404793758 1250 404792508 404792533
    0xc020c060a031b03110a030f0e0304060203040326180406050306010609050a150e100c020402030a020c1903141e03070908060708040f3f1d0d0b0603 65
    0xc028162521a5100001c184850581c581819403101d1141d905242c82e0010300e41c52401900100c4902c0d000c00e281c00100100d54001c078034002c100603035144a4a10020038040303412500040208103a90103016020b02070038034001441503c618000c03413254250010b0140c050f509014110144035010024800b00f02c40c0c1c1c84002003840c06200360300c1100002c4401508016504003112440060b103040b000318005441080d0001d4014011410034a016415121000711000e1140200308201d41d0b004009650340d084c01d016a40c060f40000618100a01864070100c0c4c841c0c242c410f01442030381c0d058440380c61502c80c0301e84143d1160401a00c6100c91300c05e4403065035101510300000d610940321600c9107000341d801d0488080c58014018940814085500d05100201e0300f54066040525402500c86003080c1d801e9a010600d01040301c94850407103080c4042841c88128008088074502d031031340d039031a0350351007400c10fa0903c1d80d00304903443d4219602120103000f1594040b0125845900a41100d1030f00d02c048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 404795008 1250 404793758 404793769
    0x100f08030d23040809120613030c0f2a0602010519270615120b01050409060f0507120b0f01080a0b042904140103030503150102100f0912110304090c020c 67
    0x21101181e4104c0c0001e089800c03071901a454508003032030103000300301e00c0c98144010b443d412401c007005410321030f500c102c2c80100682840d1403c050307035001d1890859600405c02c40034444100f6038008105900c1103401107103107441441054801c9042c2c91459000c20305102d09000104100010b81400c4541070306000000d8a038046c1406290b40300b0b903800100017005034240d4503200705542102c0702000743d240c00c01c0d0210716240206819107900f16400034140303080e8905000200410701d10301406a052a00300f1a400313400c108040103000c60030b841807102444100030814000c0440101070301207202c050110310000c003950712540380c0d5000580001150030171005040b68018800c03500d000c41d040c02028014403404d00f40111414941033200c9901c2a50550303170080d0150000801e024145001e40000501681c800c0000c8507002d2030a003410050344000c0d104180103003940c4002580e18086800200d035403a407150f0090501c0c0a0b01d503018504180c10000c40300c000e4550f51641400714496502180065070345c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 404796258 1250 404795008 404795011
    0x51204060215060a0303080c0c07120b0a0621081305220c0507021e03280605010b04080c060a0201021c0c0e0d121103070c0806100f08030d23 62
    0x240e030000e004080900b6068981a0b5005000078001e014106040001039040201c40e030f0030180704580a6150000145500c0c0342c0102540101c89100b6100b80d89811b0050886103d0701802c1d401c1d10038403043d030301c07840f08854810841005454440400f510300d804501300c14064080186c6180310f03003074507994800000300c0b581c0d18120500c0c0980312003111060100040e00c108102007209060450409040e41c0000d0141c0c510007901e406240032884203180655014032040b204142210800200080d440c031000d0160620b48000301c42c2e1a01d0a40046800781c055015503040b140558000d200d00020041441019003020503440c095640900c214210360300c400c4035481100d032519000255441801c8801080b0b0100040200e01400c1030741c600101099009001c9100004c1d07904003010b015016098051540c854103001a140e500001c02c08a41c055012603114000e01d0360710401c0c0c141980f03901031100d400c0168425140715030300030003414420749200c1d0040104400b58113204503245a980140b070031180700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 404797508 1250 404796258 404796269
    0x912080403060e25151110140907050405060303220e0c0a120507090b09062106090105032406010905040c080901060909020a050d05011b1d1813051204 66
    0x22007148011510750641200301d1070040c012006241a1511171003c1204002280760010046540c015200c00721041204201090301004100240203010703400c03104016065403611058000c070a4001101e16140c05440d000d18001405546003507030f000090010f90b45403031003020000c816540000344c2e0448120503170b4812001022003a507a4001d01e200108484040c0d0030181c0c1141c504818407280c0b540c40b801c0c0d041a50049060150745d56003070300002e40d0742e018000500c2400c04024118104415000500600501d410748807414241d889100309511282c100f45c040041c0110045501141521042d5060b04440181400d400c0203841d9408582660010880b650218a00105000043d0801d22451006003501c41d8204843c41c095030000b00c0c000b059220390307886030400103919001d0250130340c41031090700000410825402c2c42c0b16005070101008184018080310075002c034410600b490750001040c500b16598241a03603903040030301340d0035401020055899206502c40d06880e004c7c00b0300103102804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 404798758 1250 404797508 404797513
    0x30915080f04020d1e0605010e070507120905030a0615060c0503031f0b04170c031902040b0f040e07060905041b081305030a05040801110408120f0706060e150102010506010912080403060e 82
    0x104d0b400c101c01a1281a400127240b18407035001c1103c180e5100d03007503980c4690721900c408100d24040b84119006d59140e0002c82e89801200d02d50400c01000f42e00134001006070100c4441c01c1541c400007a18101100f5002030308903002040010381c20030501da140f09401504000814116803a81e01100203034110342c1020481494024a40070544c030104154005043c040300145484041c03040c641c0c90010034480e0090040d511540c4207040ca40c2d412000e880094000f600402035190300d0000c072940c4480f02d10075100460301520700440c0c1410b00d03014505040550302c440ca280300b10016000c45200400510382c50800c0403d51544001803828401840c84090f966921501d640c20600d040d802c40c5e08550041c4e10305402003004000c1200045080400b12081c110340c4c2c1d40310301d80c20f500c800d10741c41040302c010000c0d81b414401040988002c41c00c18090b02c0d1144554501e035104034016400c88000703480840c0030400e101d00400c0602d080796145480c8501c5448500d00741030b942e5962409990b101800a010f130b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 404800008 1250 404798758 404798813
    0xc0f1e03030f0e1b0103110c0d021e0106050f0913060f020901020c010c05150709090f1406010503190b060d140603060c070b0a0f020f0703020a030915080f04020d 71
    0x103070881c0a503154503036031140903042054040ca03420031201314140009042c07517220030740c03161002d0950003901e030110703049030949503404080c00c0f001351038031490b02c04003070a100007a20707001e010300051107141c060790780241c49007011f03440406c100201034000601c00a1051411904000011814003443c40c1c440140103025072a00c0c880d40000e420a07001e03811690400000e56110b001280e000030b01c8aa03118040030700000e10752564882291101d00c0c0c0d800195070f440c20086003245440860703210340b02c0c1c550201160400b9032100c9004403414030090700d070044030154404034100076280c903602c075070352800b001072104e441d06601903190010380d0030080381514aa2007807010031002d030a0034480183d120310301c804401d2405449a1312054102030240400300e0980d501d02d0708000c985166412a28032042c038001c5151200381911f0002c1d52661098012030003d402c2c1c8800007002280707131510703000c0b80009480d01705159694030f0000352200c6c2d0040040e8ec0c0001c201507032001040484815003000700e002c0d022040b01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 404801258 1250 404800008 404800031
    0xb04091b060f080a021305030d080703050c0a0e012111040314010b030303011202010507020d05030901090b09150f0f0301060903050d080f0705090a09061404060e0105010c0f1e0303 79
    0x2104294089024045a00840c08202e40c0c0140c200e580012001d100580f02c004101d04062050f030300d500081d4161056400301000660000020f922072407003654141f01903600c0d02d04240072401503a00000100c0e9007a490782d0099806420907402c5552003031000f045854611281c5401d845500c00300840c100400182481841071100942e115204132000a00004045002003035417803005201d480b0302030344414047c00c110ba1041e41124040f40e0010a0301c1c036007030028109203440340d01180360203020400309080001e138580a002a200750800042c048408100d490200c1407241c0d202c0d140c0440e03440c0c010072400103844905000b0390b028002035601c455140f41507181c02407030302c9046480c42c800d0050080800040801103840154132210700c0c50540d440e00804008620181055003000d00c525090000121340080711100e8100081c104803000e1004560301e442c0030a040c0e0b000e01829000611350400200820301c1d021032030480038031401030151403e801002a5003000015107003240044e0712000400706 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 404802508 1250 404801258 404801303
    0x405090a060509010302100e1305061e150a0207031401140a06030c1401120903110c0a030503090405130b0405010518060f0609070509180421050d020d0b0409 69
    0x1032110080808100107401e0400041c840310051100901c01c502e07010000c002c1e940314100d0303034901c464090b0080d4a20307e03481407244040c00003121054041e081e400100c4030600480107440350700c0d003406010301800350640d640d0025603500c920320351400e40c030440800200017507800100840742c1c00e0031400002d0034500044040740c00803014040940b91824100c050000c140e1030545a821200f201c401a10520348071001a034445a00501000846203051000c00600d034212003115109003030141699440680c41d400c01c40041e25902015000307074402e002a0030310341081d50000780c2080c0e00c40c030340d40d040c50840c3d9074006c100002250203c4259444000b4040d480301c1c1402c6003025004024050141032070000200b40700c058001344038612a083c0e020108140c00c0c0a01d04072007091001801601062054031820000d1502c01d0310115801c00c070900ea80949015030918240352107200e075490a292a0394030002c003000e50040c00e43d5602240c0e0700c506040c0035a0307951250745500b51281156078074590720300750700f90fa = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 404803758 1250 404802508 404802511
    0x7030c023d09150f051c1e05131e020f0a0602010209040f0207083a0501080c0303030112033c020c040501151b06050f101d0103080a1103030a02040509 66
    0x281e00001e0307400d030070b086a007004c440550a10710b880c04c1910b6100283c29120281c940c6549130100b82d10301000e001d00e07101c0000c6920446815441c003804a5155040314810000900340081d15034040514407030034003c0c010320744914044c0000d00e1100c481c030b950800182c007100c03039038002400340c0c1d0f000588921900b410b015004460503003490440c204a000e44560807a032181c10340382d0390400e038941030100c100900783c0c0074040091500d10b0640b20310302e0404441c0300104000c2c000c082242c82190031f600324034940001280c0c183c519203036100c5541406031350196000c1d5003a1900f401c004c1c2054003901142c09050402e41d0505060141c4607031b2040c0c8040003e8140164020864000d40c180401030141807658807070000c0407070076442c002005801c401004100c0d6001c0c2000102106c2c00c000911070044001c5801a0144c0c00160f58104941d42d1941f040c2c40c080383e010340c840300800000e40104041003000700038001d03082c8241840c4050040c000d21241c1103038812600d24503103943c00f20b0140803034242440358a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 404805008 1250 404803758 404803769
    0x3010e0607090e011805090f0f0d09090203091c0201090218011502070807180f0c0503040b1e07210608030a0201060902090d0f17070f12020307030c023d09 68
    0x242103941050354400c405685c14140c00921500c030070119556a404102c031090184e201070994030102000301e0681d032a08d205010f00000075690740b40204d89140b0038800c13a4084c4030030300d004101c1600b00c2540c0b005801c2d000300d925001d6560f241120009a1a000b0b05a02d80051841c504011581414482c144c65001540760070111343c0440d506001190b0001b0f40c40f400d440707120443d00b09019203203615a020740350b81706521803c039040074040c906064101c0040e50060707208009480056546107a0040d41072011042041d180e0651004a104035020340100c550303401422005890b180700d401400307010340b4190351103031585d94400609910700541c28801e14000c1c181540055141c86041400609009040000980801c20000600c1c0400502031400240e6404101a00342c0f0b401c0c0f2420500b4800880c01d6094410030100132441c890188080211503a59a264a80c4842c1207555028090030000c095241c030100f40300c1401210300600d4034100050360200058141c101940b00180c0104100c085030b101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 404806258 1250 404805008 404805029
    0xa05011409040201081009110301170a030e09150d0b01090b0a1202060a0201020712030f110403020303070b040c0803301306230a020d06060509060f0d060503010e060709 74
    0x90740d80752041e4582050b02407038444072a4541a42546002c5c80b945c0c03041031b07032510382403183c04110394510145040b6103824040121211409440c1a02e4121034800140040c001c0240d6490510302200d0042d0015200306401ca0182c43d4031011034501d488401c0255020040c26004100808160250b0a0050000d0781e02c150710a1402d4020205400300b00c1d4020302c0f0b00c4020034010754140c401d60540e06290740018008151100d0380201800402507116000400c0f410b100c0130940118175501211b040b86d5015009610300000b82d02e800c808254081c1040300d001e5a00d01c0002110001000680f00c00140e1144084c0d102030a110080000c4404410190300c481d1020100304101c903982000f00708081c0c00032070220305003a005480106510703900c0d841c40d055a4a40d0184540420154098020304464040400c40d140d280c11068445000d007a10546d07004104000c103840d5642c100b0090002c1c101c1a00000c1a156212070001e42560080c481c85034241d441881000f40305a4084407003070081c03004500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 404807508 1250 404806258 404806289
    0x60506011119021912051005040c060c060605060a05040e15210a020a0b0403050f0111090f1203040b2a0307020d030e0927030301050a03140a0602030f0a0501 69
    0x20740d15048503802d010b62884030380d8030180035900c50760b00070508201c0094a540d0415200c89454172040700b03908040d103003849000c00b04002e00703c039442802c0c0102d401101260303405240c00c40440711034410b1141196501e803079260024481e1107040260101c0080c6032201a101d504201d0107082511000b0078903074000c0398a14007040561204c10602d412030154404010040784150401071500d0b5107140f000b500031802d00000510030b00441302810a40f07214400341c0b02d1041034403800350b09a458551005050300410401c080e0245000b400000c001e07034000d0030f01e5250714180e240c124116041540315500c076502c0081c0c0c6104140414005800d58500c0455001903480d401c40d841c1d41c1c07030042d07410081c0070713405404c0b075141071501629a4039500d11000706200120315000c400040c40c1001d2680300b020002028200d09280c2c1d0000c001d407030507a039000d06034405c098656140c00e41010700840485d003503070191051410104503140011032040c0300b441c240090782c0c1014901002154016030044100d088a940b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 404808758 1250 404807508 404807537
    0x3030e0418020f041d16090b01031a06030709090f02130b0f0307050f0903011b02010e12071b1e0303021908030f19090c05090702061902030c090d0f06050601 69
    0x20482c40c0c0f010790035680000c0c1a040d82013540e102c02c641c0011141e943c170640b050380450048031124081903940fa180c05001d14810280150b003519000310306001e100c07101540d19805400e003d006164050800c3c540300b10304a03517908444086445041d400031080d9000681c800701c00c01c00c041c0b01e20041c2040100c2c40d01c1c210717047c5071802c2d582c04080c000750300304040055180d190399008004e58100c01c03070080c000c1108000b80d881302a120002490700c0300c003550800443e0800c208021852110b40744406400c10700d040c3d00341d60b491f80f021450401c0b140782078040010104040c62003600fa240c48a80c403030115a5a1821410080d14165606030348d0700119000720403e400003001030043d41c0d0001c0580c800c81c0c0542c1c03680c90161880f07844200d041c24075907150951560a000c201910801194402c0d43d00e18001c0d11460000c81e1101c40441d9800001e8084001820018003140e0041da40034032003402071410704c0300c2c0d2400121000c0841400b9108440c0d08440f142c1400007602c14075030407000c2424a56007510100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 404810008 1250 404808758 404808769
    0x51c0f0203040b2805030a15060905061605010e06090f060c0403060209010908031c0b0a030201020a03201c0f030605011b0f0b0f0f0705070812071803030e041802 71
    0xd00409030703c2c20021881c1d1000480f21140040e2044c40e1180c80981800510380040940d04105c4100d140c8a041480109801540d185044181c40050780d0340701019003040d05100751030780411070090120074600c0483c1c000c5403080c80f4011020031403602074611410034100392482c20b0720130f04180071035401c000e0601211519203400c1300d04070303944810096110a129001030303502881d01d0340442c0b040d00000401007020a150944020341d01599001046006112001c0c4a14160076000c0203025070f100c82c0c1d00002081c05407a0044030f1482001c0b10020342c03c0242d92042c28003e101103840702400b03070788103282100d5401c002000900001031074100310403407900000030803c0032407842d0724040d92485c1601c88144071000b0880d02c40280c000b00150700d1070500f01c2c1c45940c4003004803043d528040582011131200fa10070421603898907001a0040e041108814002e800c0703040c01b41001050007000e403000482400d815030005e008500903181c080c00e0b0b000f540305120a684983c03101b510181120800200180d844 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 404811258 1250 404810008 404810017
    0xd080f13030201020c100b01020d0e0a0e1306090f06050609090a1514010803090a0b120604050a02070203060901050103020306060a030807060e0a050312011508010305060708071b051c0f0203 83
    0x2880d2488400e006142401da0080c4901201c03d00e03e40070300500c4400e40c42580d0800d041d00d40e0203a0884220b03809204040f01c00e040d10b0030b00781780d002984003410814030a9405009070041103500d011080300301655143c00c103da4800104551180300d1203002c0c402d2000741c1c454560b000009951004040c0f40000f50713541c0310511a10024101030208181d0b161994a5501c04100b0020034400203400f561150402039480d0030000340c00d0301c01c4541e6900441c0c00710703030f4505860b02d0300031500a80c15140c86100400018000043c081c0308030716070030301050700541c0d8200041c50090008000004c0d080d4118010b240c1440c0008004038044c120f000301c10000034003503104903061660072000014184400010550030320b16200d44c00b4144d407001155001c2c8400c4400c50f014120354140d40783d564480c103810401c0d03401210134400a007103a00b01c100080c1e0824026020035900030410307c1c0c201501a0688401914140000c1c03040e62942d00c50891182e9080e40d100070120f4140c200d00788200d21010042d002550fa104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 404812508 1250 404811258 404811271
    0x1a010f0602151f030809041b02061326070b0105150d020904060803070516060f0e040b040b06030c040614070816030c020603040809030c24130e04080a020d080f 70
    0x90000000c25281038544145035402118944641c4140c0d6130030405c07030541060061b03501c1945841503d1903480c41c0002c00041846980c0c01400003036940c81802c0c01c030090250400c1d10a84460248070214407801160300075440521a00c003502c0d0511800e19000c03e2405030401c03401880c0c201400300040e2400b600780c402d401145000981d0b10322a02010074060f04031603000720080e1002081c42820002d010444c00002c00840c40c4800d44070340d0f40c1c0c01c220b13041c0c2c0002c0c0c1c4078004504c1d410301c114640c2c10943c2110054201c054000300d1040005400b042d0f842d40110f4000503051008207091282e1a80024801003032440d04ad150343c10040300e5100d91040c0d200320411840b60701d018940e01d10805004190003440e15030000d051640382e00e02410704a0380d542c0302c4040b244c07103405811071003440740c42e010711900302e01c40c1e00e0715a1422060912507488c0d4903501c0064900948080d001c40021501c3c6031014040c0310781d02c0390341c4050322080319200182c0741101c503604890903c0040d004200920011502c01a030012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 404813758 1250 404812508 404812543
    0x10050c04090b03030405030601150807030510051e0a0602030d2405040b150304030302040617090a141002210f010e060108130f03170108030a02060c0901031104031a010f0602 76
    0xb0300e07a50000b0300d58425584030b00d030140036440c000149150b048103000030100c0b40343c407120740c2030365800030803411a0000c4030001c028841c8054140210f05003140038048020103a011030704c0302c070440c10005070580415404280181c2c80010800708040c041d0003007480d12071801741c4d05034015421010664915145000b4580150baa034001c6c1d41e0140e45000030200f6032942e81100c1a602d082908000b00030398850300030350011481075512910b00720060002180b00710130000c0681034014069640c51171200901401420a100708520303a1000361a0344010125061800c41070f00700b5600302300207031503207443c020310704070018804100400c07041c0c401e0400d09600c4002464200501d0f44e40f11421030500c140600054001c99200400b1410140c21443e000764503000300001c8021681e13111401541c030b104000c010401a00305002180e01c07221399102030001c5040c14140400d1300d0031501e260280c680c00581c000d490750b10b06420b01c0801c0d0011141402c2c098044910f448100c1424494081e43da80d9000304d6801b0070a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 404815008 1250 404813758 404813771
    0x280f05040506032a040b0d0b0105091807030b030f07180203060d0b0c040308070b06030f0c0d02040b12060f1006020c010c02061602040f1e0203040b060603040302160b03010810050c0409 81
    0x1138041410741090140e8200903603031155252510400940c0181190200981c03514105004541c040c40031b941003080024891b02030b01091000f4410400000380084060540b2034524000d150340510a60700c461100c04000e20715180b07803525030710140d1000048244114410410f00c2040d88800ca070140040d50458000e40e000d4803007000300450f0348219400509450400700b10042001008424032307000e48412011642c0f41042072818684503003031701790310b15030042036568488010308080d0030500310130708001e01c1e68003c0044202102d0900e5000c44402d0b801c0c08110b0100b0891003013040c8114054040352005000b5280040006044440e607000d000c0c1c8181c00218480800c91900380c034a22100350b000d4002c0c40803146a85210014180b0007281d2981c0021100c46181d00503058070a40f440f6581022183e032850300c0d41800e220450f4409002502140106100c0d1307940c090342d420034a07005000d1070510590740c0d03142c152010300b42900b1160b40000541040180a180491841034609941c4000d0000458 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 404816258 1250 404815008 404815051
    0x70e07020c0d0320010b010509102a02100807050f03150307030b0702010f05190c35010b0703080a0e03071502030a0b0306011d040602280f0504050603 66
    0x802580840041d4420451801e4600309071340140089004115078101401c805200c40960b42640c070183c4200780043c4092080108918010103032120705413140c1001c1c3c0341945c2180741d4120036800c41229846400104840d030b0114200318103072545100c964500070180c2d0500c8030004116104031946003449c48004000f18075140c60a103900000b200d0300070201da204560300c1c0350003840c0c010110703030300c030095440d1641880c400c13883c1d406914441da00322074200f642d1010041049006080c1d4849210400851650405940c5101601204201240d080c0c001e01c00c10b0000c1092601003050b080100040810300020300025007100300d260300900100d0001c0b5000c04681161803540c041c881010345508403e4442454042e460f9000f1406000e44813810320900a0000502d03640301d00a20a110f00f081d8641d5000c1c0304004c00e20384241d0001d201d9000035180c51046481e80074080320540405800e40e590748040d8101580110340c0b0044500142025410720b03180100080742408000e1492800380180d0611020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 404817508 1250 404816258 404816263
    0x30c0901110a050a0b090a08040b03040c1208041a090918100f0509010501090209060403030503070c0f0302030c25050609040f0c08100e01120206070507030204060b0d1d070e0702 78
    0x7084111072003110120b01e928180300d565140c076041c043c1d4000c0c4100c400718800d80404281104059000381769540f4207803802c458199142d1005100f03999000b40e854000c104903642d401070000082c01501040d4850b03080004443c42144011560400c0350b400700125a89a00d40341b1105902c040301c00d403981030380b0003241c80d0340741002040a008000503151001c16019a0100e502044c0200108070082050f03a8031048100100d115141030645c4c001014001000020700c500021503000300300e4038040f4840ea00c1c03982d50035000314070b0080480168001003030414441c4420401e4009244038014400e00113400001c45414041e418000c4601070f401c0052420525100e40d0014020041d00580030406000e4a000087c000c40d400d03031310303024031400d070034400241445c41886c8103042e01d0000e07010104d80e11580e800c1100c140e0142508540900583d403001015030b982c2e11030b4000515110b80503523928500815241c044a0202400c0440d0302e0f48280c0744140000002507003400e442405508000c1515124000d13032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 404818758 1250 404817508 404817527
    0x510030b06030a060f08030309060c0a030b0d0f111906110f1504032c060c19060c0320070210022112010e060d060b040902090a050624030c0901 63
    0x540140700003060010740349030b0307500c20000c4400c0300c508186010340740c0f1303201e43e143d00c0240c403850155401580420000c5401c04c00030011114903040000309440040c0100760700c100c0240c400c3d5055220000c0704824080c00c00c1c0c01c0c8400010880c1c034003d02d03607521030520280740302c06d000c3c2d01e00700103c9402001124070108004031210030b02004485240024540340d94120504030382c01c600141c4580480040359091621071000529140741000200181c8001d10a65400005d1606014810341c483c240e203a0b1002c40341c21b4103050140300003040520007a0b801a0960307401102c00580e2110210360500e0300751090003640c80250781112076101c0040c802c80e0480c50072684c00300d22002020b4040d021400341d12094000c050840000082c4405a0f0369080601503559040780c0d082d8100402a400e5000a5210f50040c000264002d1001880429940200c0c0485008540c49020340d50b0f07410910800f85488052255802c141d414a140640491450940180400391501000c40800315590020380e0092043c3c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 404820008 1250 404818758 404818781
    0x1f0b1819140a09021801090e0c041203090302060d0b04150302010c060b0f0a08030301062d0c06060f06050d1a180c090d0f140f030f0705010b030f0a060b0303070c051003 74
    0x44d500c45101a10060f0120b8034403403a00e001c1803c1d054002804603104c00568804c1c040d0b07603c02400c007840c0a03104008144651030171401c010080d00b0110060f03941d0000f50818441032480000c01d811482c06000840d500003840c098031008080e006c02c0180c0c0c0c0030414054256100b400414030302440b001043c00c0200412130319a00100034140820444c100201641c1260420340e203405c0e00012550f41c0e51001041e0488480901040c0c0d002c0c80e00041c0140c0813216213920a4000080d62507640ea51440c059400b5085000013400c0041c0390110031503036015034410100b2031803440301850110000100364480850080240310083e10010321080c0039501a1003914101803e218012005071800600650245c242201d040f411580300c02c6945200065000035a4403050040d4601003040410a03080e400000c0120f41e00d42d295000030303a8644080c0030710407007a81c05600401e01d0f16114500740d401d9812841c1d402c0d000380e2043c00003a002c1401d19040e041103600c10f440041140a9000c02140980742c80c0303031038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 404821258 1250 404820008 404820011
    0x1306080105220e0316051203060607030e030c060a170c250f0b04081b01050103020906041109040c080f070216140111060c04050f030a0203060f1f0b1819140a09 70
    0x20031702c051038090400005903114805449a1140200c10b4405a000a403002074011406100a2340001d000e034501400c40c0305c00070100c42640f19500d0004259510000a503000244103031500e4030640c10030100c0f182c1250032901c80718140713013a4001c000c0940301103c07503030090b0420300b0341403c05000301c1d0000318080a40240e503485043c90281444052603021b800017070240f03c2103a040c00715030350042c030960307050300d50041820046444007030400000c2c2028168041105804002c01c1c1c006985a1140c0444071402c0d0300c90042600c1c18000341100d0941c02840d80d01550400039000b01e1440308035481e80150b804140c0308100c4080340400480b91704a94101e0742c1c4c01c0c0d118441c20b1220085c0c20001400440340215000704281c1d9005003419103e92076a01c0c000e4055010754045903081c0c00504c2080d5001c4a000c0c1c0100b07030882d4070f10780140e44080641c054007030803a000506046000301e514841d412460181c0e501245240750b010000d00c2144284a0340700d10034131424203201d155480000038401815000300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 404822508 1250 404821258 404821267
    0x90b04060305011a18130b0915010807110a120302040e090c0f0103360b130507051f0f050c01020403060b03010b01020109150b03030412030201021306080105220e03 72
    0x501800529082c007401d0440100d9001308800b032100701e811940b13100714441d00303944245603c5061004007162460240400307511400f00000d146c0b00e80229070321030f180c1d105101d0301004041c00007401e55131010340444100441c2040c00306000c1030004004042681c070820940c03000c550030400320002d020f00e80200969112920600110002c0003400c0020350748200c1303100c1d42e40e401001c019400c0f140843c2c0300c1c418441ca1184d040a03080d030b0700780400366454426a80007800c440a0390b610142c04074220b0740c502024030304006080a01c0410810b60003d041c040d1a0262031940700480841e11a90040c003540c100500351108910307440c031030800d81c0c212030820002035440d16140d20f00380c3c000c1c1a08002246c00f0303610701200060950720501403280b4807a00721801c803d180007944034523006024000100c1e900342c44108800070b004014010a042d58600a600050300d50443c50205510b21039140d0114041000c0e070307401401140d42d20f80040c40413405c100c45114500782c0300b0310600050292040403d450303000229 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 404823758 1250 404822508 404822519
    0xd0f021504062601140103050c040f03080a0306090903090b180a060203120901020306010903151506050c0f011109040207140a030c0c060c050a061107020d0c050a0b070f060903090b04 80
    0x12400e826115420888030f1004580c2c1d4042000e03d20902c100910070782c11040d049029402640806d80208107048800d00d416154a1603e4000c1840d0344201c51a41d00025500e0b00d80e90702d807188401501809400344964510303a14000d02202c018041c0304680c41c00040c0e8490104291804280b039400060f000c0c03500d46940e140082d4490f000b501e000340003030401d080000d0a80006100b00d91103540142c462903200c50a60302e0b41c8410300c0440b034410200641e9006000102c0f0740301420100101800c0d0340340c940e41e03d101503c0d181080800072500310160f0425111131140e0800d241980c071042001d0701c00684801c1c0b03a09041c00c0c160034a20140e01039000c1c4c068070401703040d030200b00040018010200b80d03140c26079a120450300a448480c0241c02e64018118080009890760007005201c14245034050400c84684c0000340440c103010000c9a50f40954041003142d82080104a00244030f50004a4113100d026200c1c002c411a4060b00100b040fa580e40301502058010352004020b4150110029159521071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 404825008 1250 404823758 404823767
    0xe120601060f080912091503010f030c090c0e060c07030807050c0405130308010905100e0a06030b090a17090d120201050603010b0d2003030c010c080103020913020d0f02150406 77
    0x20700840340002c5402d00d818005900a01545000c0d040000c000c3c01514175400380c8403000d410048140d90b1107421071032109600c3d945800030318080c1c16030041d10101c1515600d400032800312980d00c0b104c54281402c21014504c0d400c03100142d203070751003038800d6036440004044450030181e1540005010fa00045041014800e0024038031005000135102000a9100c1d001c1d4a18030344c2228200800082004005001c0d6820700d8001c40c0d00040468010b941c42a1120015004c281e8200d03004590700c7c0d6503031020402d11100201c01a0000c4d000006404008490b40307131705080381c5075403082c0030300ca400000c3c4250307083c0c607603031018281260801d941100c1a4107052000740a444250391580c132945c00c00902003a41d1604d40c2702ea40c60f85600c900d06142d050042080d0f041c15242c1e5852190385030100340140540c2e01000e004403003040940340d0301d40c034080d8103501c1000b035444c4004d40040310101480e00d10300300507116443e0540840ba0401c00c032401c840800d2001811101b151642c0541c480c07408100043c010307401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 404826258 1250 404825008 404825011
    0x804080312010323030f0d09061107050709020c030a200303040b1803031e150a0602010606020f070501020a030525060c030c020606010210090206270102100b0f0603070e1206 76
    0x4002d0900c1c4c542c0883e442c49102c0d820018004a244c00410800c40654080310082180b0b5024510114045049841d600c080b11200080c4d4064800001802410040103100320340203016040800c600709900418480e640b40121545501440b403107809161102c01ca218104240030804400c5030340d00d00d17013481c03c8000c40000780c642442c0c1c050000f4550045803804010349104007080c2c0e15490340c48485000100703444a015103034241800c5102c520b0070840e00d4400b6044007404842e000800d201c2c0c640b40c1e00a1070244058407068441d0440da00500c580d0380d01241c650182d81d010310b041c039140d036141000e11040c204c4101040a41c081d0301c03c010420001681c1001541c1e1650b600e04001030030f41941d0a0740c480d0001c5803c0c3c0d0060700441c90310300c03005c0002e0b4440c0080310f00190030745082904007032040307600074054025800380607440d079a6200f071581c1c10824001d0301e241d0300c0350502040c0e8904011500341da11400e20544101004000584600d208210203001c0507802040c80765501c1413030724629100c240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 404827508 1250 404826258 404826263
    0xd0902011e02060a050a020702040c0815150405010c1b06020c09010801050f1f05042903030a0207260d08150a0311060f0f121009060305030a0c08040803120103 70
    0x1c0000d048854501841110307495070708580203031070300c1c2e40c0d000e074410020500140413100d807503800d20880d00075072154441e408501c2015240d1401601704083d01c190b020302c40785c000600c103419030083c80385400404c4081c1c0f421540203091400e51181d4a00d407020340a0421713000c041c00005401d10000c4e040d036000541015a5805880c01300240e600c074454582610700031a01c5107920003001010410b541c0001d020906603c4114091201c0c1ca03480b50001402c0d21100307001d40c40182c007000400c1c0c84180c103582c2d0188404004900031450241c2440c0040c0d21010a4412500040302c00481c00740c9500301c41d071070007a0b10342824003030390920384d015400a006844155814000706c6400d600742c00703186c1040d5000c24280c2c1c0c1c01c50030349050b0788244401c021050340080c4440f8100c40c0705001c0380d401403111401900304048150300c446107615181103000e070042d01d076502210119042c400c0410100f08048112003070303d503003441c0040507280300703045c80c0e0514800c9502a90003840700140340c2c10408803c10303005060300c2c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 404828758 1250 404827508 404827517
    0xd1a060907050a1b0302010e011d070b031e040201181d102105190b18030708040909020a0807080102040602060a0b01082202210d17070f0c05030d090201 67
    0x21070314181158a809020142c0d40412121881071300050f84410904950600c80c0c03002040c3c4494400c0b429094032858407124281042104003010685d50500c508000f8000401b2110305501d490071882001e0790500204610340d0341140d010509691007551a00400c0300090f542d000490f80d2950f0220703010400a054001c03042130b04000c101c49040c0c0c136802c04c049a078256400b002c001c1c09044031905441c0d80000071541845980c00e030201d0300039500c2c007204605004030400481d80c907040900303010041075021481c2c0940c004007c000300113800d00040d01c003911031581c000503000c0c1c0740d4404548403806035006841188510100014040c80540003007007541c4883d401d407074003600d41c1c900344010348500c41c201501282c070b61000111541c40701810190002d074015281d02d000541a000705840041640c0034146007901d4030045405542c0412141c250079225241034107169442c0d011445c01020090100300401c11421001c0030801e1003040c1c41c401592700002900d580f0322404c0702040042c128480101e0124 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 404830008 1250 404828758 404828761
    0x30f070806011e200a050c1504030201140a0e03010e25050a14031c08071d0a0308030a020c010f0c020f0610060f1b050a021507020a03060b0d1a0609 65
    0x9512402583c4221054600900070541500e00709544404440c0035518600f0243c2064583c0c6007400c012004403140220b01820b042c12211040c04800f400a1a401a50100401c010070050340d01c071100c031883c0741c9815026601e480d000001110347c846580f0300143c0c158281480d0242e07191012840309000c40035070741014129681e081511114a000d4450241d100a1010041180b030494003410220200001c05590054612007801002054800d803800000358180c420052103541204200c0c07202c02d00b60b01d00306407007284000020072401070b0b030000401a0704c001c00414080c036000d4040c1d40140d510320009200001108440c840240000031008005200c1ca41c040c40c0280008114140241c0d000141028000c1c2403900235206400032403203610400030580714110b480b01348800c00d9021244107030003810300c0054a00402581c0c428001c04045418005c10400740181e685001c0501169400000072543c100034000050121018100140000c2d52601c80c8469003c805200706104031070464413018103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 404831258 1250 404830008 404830021
    0x218180a0c03090305030f0601020a0b070206010608060405040221010f0f140705091c0807061a0109090b01020a0b10080304060c0506130b15040906060b07030306050d1212060308030f0708 82
    0x16a07843c03070300c0a0b020600c10030220741003407a2111074a0344000c040c0102d980c16501e41e611680301c40022140000160000c100500c0351a5102c91003d411500464051001d07060540016000b400000c2100d909070501d10b80c03401691400f900f00f100a002c01d95001c1142041603583d40000c0c0c206400342910b89800540002c40c4180a40195179800f40f01030482030180c4030900703c20710b1035074000d002511400d006100c910000b0f80c0318011b111810490611561203494520005005007405030000d8841c203080c001c4150713241c0d0780003400c90302580c4c01520302801a1103407060703503850a2440e08484000d0100141c080741c141c0e080398070603803045c0c0700e03a04460056546036050401d680030050000c0500004034041240e0100242d00050680070050000400209a65503041103917036690104a40c0d61010400c2020300d9010f102c5e0000501003529541e004040c60340d54080848245c0d0410405d024224010300f41020180d80080d01a50344652029035a0604c4e416000300ea080445480001035003050002d2103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 404832508 1250 404831258 404831261
    0x1b053d0203130807050c031c180302060f0a09170105072a08090111100507110307151d010e010609050a0c080c09010e0a0f0e070207180218180a0c03 65
    0x1c121140e4180c00c4180d84940c0d1003480d40e0780812020703202ea111b540201156a030b01401420300754444001402c80040407041d015084106448180503910140c42041000d41c030b81508645805c541111040d03550724001e0005d846035540b5400c240e00d82c544854001030441c00542c080b50181105480b6100c200750005003142020144000711040f0804a100c0c410000b0080c9000c0c02d04c251050600981044252011a20b091b0451a1010080762580305006000fa08800e01000c413049000241d803501005444910480001103848031149030364800c403110700314039000c50400c00c0550000174000e903940920301074043c000c540502ca159510780808545290064071610b00c0c01d00342c944440100359141d140d19000707900002d24041c1441107501d0140301d150340301e4550034041c3c00551304019455040500d000c42606001303240c4415944144001d000109a21404100406c41c8a4015948014003074074107101809040c500358000303c61800d001041c090544e5228030401402c1030030040745820300b10030ac0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 404833758 1250 404832508 404832511
    0x8030a0e1f0623060a1403190e010c020a0b060d02030708061b0a020a0318052211030f1f18020a02010f0b0a05010305040507080d020f0f010c1b053d0203 67
    0x440b0103030803098000040c140356000c5c04000d141070805000c034103510030740368820398070131605240e001285015603d019030701d5200d2000d04100c804000c105070444500081d54440704500c2c094200403d02000078210303920320b82c1c420a041d50140c01c5d510300d940d803403994907503807034040c1c8081e010780481d00c1000d40c2d0500300000f640e01c5900f040d070082c9041d80c2580c8042d1038000340c1030307401840311070303502d00c041207607210300c0258a030078a007031100340b542d6442224400b02215004080b00007048420010b11040c000d800d4040b82c2c00c001c02d046000c0040c1101c10790301c40012a140e0280e0011100d2040d00003405080d580641240c5060350020702034410740798125000c4448950f000c82c2d202c0380140d0b081c00554406d07403003194050310800131204d5980d1551030092034121041c031101c0c0140d0041e02c908a490505014004102ca1a40f0007805244054070000d02400c4e400101d50084801c401c90305424024104014040c3c0c07007000c0242900c550064150b03220341100181a5858003401b50b807081600720440c801c1382d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 404835008 1250 404833758 404833799
    0xf03070b0c030c03010b09041506090e011d070809030d050a09031b0302071206020c07031b0b040803030c070302013b06011a160b010915080a030c08030a0e1f06 70
    0x1d0f14580c04d014040d2450b41000610b20342082d89d841c0d0501d152a10080c2140240c075503603ea003214945000c44440b8042d605070450110130078014543c140391685026a550000c2c03550809a50300c0c4e554008561850142284800710141000140404200d06510a80f071140c020381e98030764441c0d9603640700005035107000c0c001001648800400c005109401c03e01e00e0906200e040d01600c1c21001000030b03850200c1580040c0c6030484520b203d00e4808009069000040044640c5141082e1030301d03a41507200d00004084000207800095a101014402e52050505002c3c1c49519006070380c590400b0a07040341004150140c0e440303404a8000b40c244001201d03412511520100304490a8001c141545a000842b080718203034660600d100024140045290207411846000180340c0080003503106240b48942c002e18040d0040d9041d280441c1d449501c01d01490307080001150380380c903401858001070035002c2c48022540512181c00030400d80301c00705400c1e21202a0820b1021684a240c880c40442000000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 404836258 1250 404835008 404835031
    0x1050f04060506030c031507030e120d1508100606080c25081201080a02011409030a030804080d020c06090c040c0f030903120905030a0324030b04050703050f03070b0c03 74
    0xe800100c0681085a001c8009420799500700d1342d00b0040380c0b0700f000881140d10b41100302c10420440c1030f4107100e1564401d940b82e0003400f580007030040c2c0c003060344a0400001d200d152900e0141451010520440c2c3c010300c403035021205191401c000356001090a03000d040002620100498100a481015901c0e011040490311800109440314900003880e2280202d8065009000e1140c504d809203c101d0b000381000c4019112064661000609030211000003045246051202d0a03030794030002444074405a040c2800d003c540c407941041c100c2800780e140030b04902400001e0181107944c0224180e409100c15000320303813142001c0405c110540c2c1203100ba000015040f402e8201105200c1d808c901c20302402400c00044488001700090280d0b01104420b0340c0a60001401c01c08445d4948560443c41c80c0c0c0c40304181c0f0b40c0ca000181c90656407240d20003d4103032202c21002c0360601c54280b02003002560302c0307402c40310349401412001d5100d070440102914045000c1001030000903041d1700326841146000740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 404837508 1250 404836258 404836261
    0xb01030b0a14040216020604060c170a090e0a15060c140d050a0f032424120f11040e09070e06010206040b070e181512070303030216200f010201050f 65
    0x340f1009400c5141e0941d20072004081c131704056140e650041c0080c001b0340d56142c0d13400f03019041c5100b5003402c0801001c08410200301d0050500d6204074044203a07984140201a030b07480f0200000c0c09050310612800c44560321010010303c00380c01c210706180b07851089070f403442003d50b25800701e40c4406403966101c000c079104100181c601032003240c062121200368200002c03020141d054140c2d80004203140000d2a2003100818008000c940480104415141c42c00e803011035901c8100610491081d80340c800d9072511592002d4003071945070031610000d803c11407015100d9647e0784002903108029100e114481c02900701c00303c0c480308000d031a5031041006030010005a21513a0301c9556281c0000d00034010845c00c3c0c07800c00041e035900b0104000f02801c204c00b0380102d050124090400281281090b84555080400b02c1c0c1c44060100342001180d4144c100161110060101c0544d0b181c29008018001540c0b80c6881100c1c034850344621061410a40d12800900f0303225005a003200c4007902c1c4005003401100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 404838758 1250 404837508 404837549
    0xc16030b0714070c1401080c0c07170a1704090b06391009021905010c1407051c0615030f15020d0e0624010f080a0b130b01030b0a 57
    0xc40c02495541030300d0b18619211154075030000c031141e960080c010062090304900250b41c3c2c03040405070080d401041c4a443d2003504000195035650500c9802480c400490051340640000c0c4003143e4050742001c02c480d601e40050011090036840781c000c01002920304504102103003001410350340c2d12001300800000c2d496601162a68112800c100c0b04440e20301c440070031a14450511844401e9000b542e0045a070b290284100113800a20108841c01942d10010030040b03030703a021112405103034110044259940c00711079101d085c0712051b004560001d860101001090a82c1d50f03000310658050745080100d41924120004141c00070310001d00f804610b0400c450104c0c0c070500b0702d419a00404407005180100442e04001512070b165400d040f550400c8040109902825889001070800d840385000040070450010b001e07481c03080b2041080040003800560700c0000e5500081241c40028049140005031700c800704041c203503a5040030300013414040321034154180404804192840500400d1030b003407044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 404840008 1250 404838758 404838767
    0xc03011710110d050c0307050f030408090904050f07060f0509100c1506091a1011010612060c022e020f0904020d0507080c161113110c16030b07 63
    0x40c81020300c0380510074039140045040c0c890304864100340c803581d5494403881c0c10b401c001c81d4001401714210b114200100802035078003d00321087c10206002003512502c490410a4113030244400c3c0580140d0f2640c00d110500100182da0542e110141d012135240030346411044426070b044003004800300304140f2120f55180780070070b103101d01e401240c60407090350b00b21919110503101c0c1c2447c80960180e5204014040003000780610b00c64401c0304040c00319402d40c01da01160349201a424818204152060803845d0a4400c0d001100104800c0c0c83ca458540880d060440080040d5020140580720740c082c3d029040020300c0e0480f041d07048070f003440d80141c201070502c0d0003e58424001c0c00381c29403040014800d244c0d03881c4081c0181d61400000001d19160809000d042110003918000301038105104d074030003100206d421500981c0d031000d0a04807210b160400704600c5c50304010b82618131802c00ba45150340d01003000103016207252a07401c40360140600c0107410100032941c0400380000a01000080109014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 404841258 1250 404840008 404840039
    0x903081b0d051602090414430e1012051c0305040b0a0507050c070b0703080121080702042a032712020a0c0f030308010504021204260c0c03060c030c0301 67
    0x240d150140c501c02d05091f4900f0f00310500318031f404000800c0c0740355000c07034003800755448444c8079008109941c44d03914030240f0140091f4400c0e64252484403000561450340356090100400100064002400b01864003986844600c031280c0328000389a40c0510140748240900c5004603008071800b0401c1c1c03200e0303044901074403006010701e080c000c0800451903205001c02070301c0000c0403501c08650b1a5021843c004200780b00c107a001d124107422a4200820001c20100c004038070340d5010706547ea42e0581341c404030740a80808130450701c0520342151481510240210075585a114a98040040d11440c0c01c0e11001409484003c1000d400304040c01000621481c1c08400c15a110780101c0301005059510b696a00c0101d030000030268074141c2c020030416800c0040b00d800750900719402e50916011250284100358010405804900c400001c403440140c1891010348001003207104541c3c0c0c100111146030740d96102260240a1300c80ca0b00012109010031b0b084e64010f94070401c0c5a0701d164a00f01401024052 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 404842508 1250 404841258 404841263
    0x1e0e041502041505040315060e0c070302160e060906010207080d1121040806060105070f030509010903060203010b1309091101110f0102030109050a0c0f08070309030903081b0d0516020904 82
    0x90800c808502c040c5280b20051580c10f00d0354034079a42d6819454480520351200400310901070038041c0034491054001c0c6401d50101c9154600e03071300d501da41d0030120b1501440c0854136040c1000c403180030482c411b1b0100f80d544210f5003039444400903100c50004a039940b13158402c2c03840c10341245c814648114440c82011710702070a035204480f00c03000800814681889581c40f89080064001020000c000045c0111a8082070900f80581031283c03644a0490b406803580004003000303400101075040ea03024040b408051600a02d00315200d41e1208881619a440180d03500e00603c0c3d02c4a0025014015000d00052940d000c400030b05941c0c26500151203009200c000d680c4240076099070fa00b0101000d20103107008048003200492241017000c41c8008940441641d401040741e5521640482c64100300070680000403898000350440181c141100c000d0300780c1d08000c00b202000260000c050641e074140f0b002048411007034900e444e81f03d650903070b102e111ba03101c00654201903142d01c1001d442c00d0040594002e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 404843758 1250 404842508 404842511
    0x209031c0519120c02060403050307230c03070210031a0103090501020d090501060f080102040506160206040e070c03030b0603060a1a090a17070b07050c0103050402060d050438010509180d03061e0e0415 88
    0xc3315110b41b15034000300c0d0500040d038004203510040d854a0604105514010306007041600060210310810f40040c9038220305041e10f410030b071800c1190941c1101c6100d0f00b035040400018213075140c03950181000c3e00c40d105100004130808110114188200d404940000f05074501e843c042400700201c0201940c02661f001d5400e1000040050484400310320800f12a51040c504040d145006000c96005410107400381009204020440d00c0f00e000d141d080d240b860403840314210f1714200540300d62050002a9030080c050003000250000b01d90f40c3c49040c0d82c0d0301d0040d104100d407a035044000ba402441d4010300154090140038005500a510a6800c14005041c1a20748001d01c410003090356015070f000c545003505460454151440b402010f202420842d910f1500c040300440c040c43d1240060190f2403180c24020046035802101101d04050450014203550540a039001c1c058002c2c2000e20451740f488083c803181e25900c18041003450f040d01d80002e0100348640311511000c01d1a500f548001042c0b5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 404845008 1250 404843758 404843807
    0x304060b1807030b030105011a071b1502160614160c0b04030b0901060602060907090e0a0b07050a08010515270301150501030e010209031c0519120c02060403050307 72
    0x1800400400b0312400351a03e010403a1190441410b08440c0e050b030040341c03a02d02072000301c1d504403d0310045602a680002c1c0303956800002e942d4425042206034000c039004c2c040b101135640ca080c2c003c07640d60451143e41e440030301210f50f504400e507200c0052011440d6442401c000c0c4002030031141d00d104050602800da1112640e4840c003468907194440d80051310030b400b658041091516003402018060802480908900d0500003407046d40d4488500070800519120050003401d2042003240580032604100071a41604000c1c001070241e074484030502001801c0c040002c9018240440d5200080c42c111803030b14648024811820f9885800003001c3c89a070a1498100019541c24001d01d010451800240862580b0701030001d41143c85010190710207900510840c41c03107980206540e04a00c0c114501c82d654007040600495041c401c1401004045460b03d902010721544007035040699100301e8403c001140240100341d942d14011140207002480070000141054403500b1040b80360782c642403d000c00f4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 404846258 1250 404845008 404845039
    0x1812081f06030902120c0108220210050901020d081312112a01082a2203020907020f06010b0a1202160b060d08030402010302030c04030618260304060b 66
    0x100d000d240c1c0010000383d00c50b0003203429442c0c0041382e403001c0c031032000081002c1106480082c0813a10b0040c5002450003c00c0c0301c03500c2c5411075500301000321782c2c000c1007250008003d07800a4900d0300070345210360052180343c1c0c50080d40c9002d1180540151100901286045070030358507440c038050001803490800c82501d0f040100d0003810040f480c140002e0190005104614002c0620506a040840f41c1044407110a0044c074410f210304c0c142d01e52001c82d00d440030500034501801e6462092106000c0c2850144840001d04035000900c107040d079108460281c0240c84804040fa603501004110903d80c1d08114010001040d1050051401d103003103007800c1c50300307403c0e41814804a80165990f05041e13030340c4021200800009003512030388030804440d186510100394803484034070300000300024107042d40000805c04110155094400a640c446414403050b4012160041c010300041001c866100d50700000400c2d007038610704148180e009401ca46815984d5545404000d0010502126001f02200ca40c1e800b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 404847508 1250 404846258 404846311
    0x606030206121902070206120604180807121707080601110703140f070f0b0d0603120c030e09070e0114251e030507030804110a08010c03181208 63
    0x20000b180c0c41030018603240c0303400c54100c9003030101c0c400318410380b04011030030059494034190b80391514400c2400c440d655030180030034010411002c0350040406646170060800c9101ca0041649501c0717140015411401c1c1c0d4025140c2c0e04401700050855a50400010801481003101c9580018149021921442c25580c886d003011140e40059a00c58510500103000003070800c903008095007808014941c65180c8420b200c2c1c824618001d0324904207002400000c3c51805401c498055034028400d00200f07001040094061284903034101d0200b94080940e80c201d02d0a5518a0310800c92a01c07030789c0140000b24011100b0b54608110082420300501c9a2582c900d442820448440c42003000d480c80343c074240c14000c0000903901d15400d900e00010910100080d4810250f800d01503260900356016111858500c1c00c01040301c903420303000032102c8000140c9000c1508000381d4840c0c59202041352142c1c1061300c0041b40c0b00800060841d2709131030480750b031446c0304d00b81e0740394440c40d84141c0c1c001e4202d100c00c2410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 404848758 1250 404847508 404847517
    0x19051c0b1306050f06091b0d020430050d0c050a1203050714041d040f02120105011a03060a050607031106010308090a06170604020a050408030301260304210606030206 73
    0x14030181e1000c8a2010424203120359070300010240304582440c50401c0c006808460028840c14601c2000b1426480e800200f60640780d210f01d0902d0f055454540344e0308256401c64503600f00049407040c07401d0140804040c103a092005940000207400041c841d042e0650328005543c10454551240300607900c00304100300d0b00c1c100d28500503a004a00380c104510300400b11186d000480c1d00005040008000401625440090703a4050020034140307a6294108003012200d07a0764042d400c026503140c17148080e41c041d8417480c141c3e0b0502151101448504040c415940021104d694100799220341c148105d1401c40c02030320842c2d201e4036210401200c010340c4075050103020b0307000f21503140000c91a42c00c145040151003000c0c240030b25260b440a00003c4e4240c9820002800580c0503541c000352210405214108403409000d40c02c0c00c40b0765070b503920000c1071400da01404001d64120003c4010010126005c0115411258954503140c90210356180048a0202026044502603995000000140c45040c00303007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 404850008 1250 404848758 404848771
    0xc0c200303130f03020a1721121915030809190302030304030b060913110907050c0d051e07030f031503061b0216050a03240509031819051c0b 62
    0x55815030710318411b004601ca40d5810000d40c60213001c80303880a250000404424031001010003000e141166005007140e0310032105003903480c44c5240b0410041c0b84070170300000d4140110000030030a01d022003200f945200e0307080c08024100701080003403845a01d04030020600c5040c5010905c0403541d96640000e1455025500c215000e80c0f0000c1000003924001180c00d0f0300150a018040b0814005d5840743c0a404e0300c05d05040c131802005010580300e03881a0160350400c0b1300c01c0100e0303401c070b281c0f03007c0034000e0b40041c40310070394410b10a0742e80d000140c404000d40f2103103039140c0c48218030040c00540503406000d1110754440918042d07100000442c1507030290510405020400c0b104080d041d500080c03d02c611448041d04241540100300000d455000e00f100c1100d821422100300700c01c1d0464600038038440d98140150150070710050090422002c801000741c401103a00e040803140c2c40d101800718140f804d42d85c1c4688003080d010200080d00703082c0c031003007085d002420a1210f400090f40d2450390151050315031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 404851258 1250 404850008 404850029
    0xf0a171501080601090803341a070903020a0303050c0c03060a090c1e05090a0f020a05090103051008030a0c080c0106060e13050708270610090e03030621070e0c0a030c0c20030313 78
    0x8402700c0f00c202c00c00c5a00300d400380c545041e4090440c1c020545500c280c0c031004040160025a11000d110b060007d007a0406004007900c85034180a444040604020b4000342c0d0240284040080c8170f06d0202d510705d80c400c90410004402d035182c03e0801c200722100400f964a52910380c1d05403894011700b131005066105503a12000d13110100b8074001000c40304010411020840015014003060f4000001c0d41c540201b1443c121120320424078042020380200f9540e14590340c201030380800e465410656440907110306446408038902c0c19540041540d005030742c614081400359010034100090050b05160755000f003500c006104000541c07075891f0900440301d508690014000038405a080703400740c0030642d0300d000021821810300a00064544500c124050501c0a900c000301403c1041400b610000346442c400000b801c0c075001c03250002d558460200c1c0000689400f0300505498020a51040013680042c1c403400d444181d0304020707a244450607a0b69a06200034485180b0a168003544003018000c014003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 404852508 1250 404851258 404851283
    0x120603031d010e0102060402040c030b060f03010519031e031707030605030f0c0102030f07061e02070203070504050408120c0f131503050c0f0a17150108060109080334 73
    0x2004010751607950300d10304101100c80b8040040ea40080c0c0aa0170940484000030780d85407258081e4018121352807101e8100c0b002040700d492400404000d18121401642c0e0a42d45000c0e0901c0349501900d0350200401070b07240c1102502001594000c281880c42c42410300c0c0245001400141c0d441c1e1000319200c0000070f865403418007140c01c080c0541c4200c104244024441030195800107503ea0045142d2284280c1d004135243d0709202403904a4801034951209145180b032007039040788040c4d030081e03c2c241d01a121740d0900107030038101403003164401c1d0703000000c0ca4203140c61503c0b00072840e9409840301d246202c0520400003020001001030140049140741155050b142401202d107404900c81c800040c545800100301040314a0801c0b00c2c03030802080d81075a580c5443d40000e3b5501e440300c000c06100c1380e40a4041000c010181e105100c80c460003600c0d02c010320354640e001120302c014603024610301c3d0340042c00740610441141c0082c144803d801c12201c43c503c091301017030b0442e5402c80c80c0c050b2581000b044d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 404853758 1250 404852508 404852537
    0x60b191d040624090f050906040b1008010e060603010f061d10020a0b0f0c090607080d020d091a0702030906090f1002060118060b070308040213090c090c05120103110112060303 77
    0x401810310124103040a0302d0345000d0f1a41000303000791043d640641c1720140008c03c0350760b4540c04090320040050010b5500d01240000804855007401110110b60308000402c01629018054074129815648072204c11820200d003100c4219820711500c0d040c502e9980b10b81d00543e1130040c804d1544900780c2c0103000d51a59400e000d05071a6003e01494007211904040c059040900d10449034450000d0300ca995850050740f815034058400c85070312500087c40880e144d540c10350302c2e800402c9518003036445200703c110562058112400c2c103440d058090703441000320f01003e040c0303000540800c1c00c0c0141840702504c0039102098101c1c100c88401801038001d0001808801001000090048000b0b07600b0400e841c14840e08116900c41d0f07410180c24800c40d4000103045540311650b10040e2a040d480a02c1540e100d0300e00b0801c1c000c0349004d03040080d4100faa0703503080d051140b0266441e4900b10000710b90b00da440d640b100625021100c40690402060302c08454490980703005000056100c1d5480c1c1d06a1b41001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 404855008 1250 404853758 404853809
    0x606010f08130b040c1802040f05031902040e01150b2203030804030818030d06140409020d0b06040b19051906051c021b010b0301060b191d0406 63
    0x40d0545040c07015880600c20814040503092112a501005002054603503041c0300c40c1400f1103601000c0702c2117801c824102d240d03030550080c004603243c021002650036100c408042d261021034000c0c03411880c0c0b900410b000340c5841e8000c40010b046030b400000d5509107400005050852a4001c0d01e0384407400600005400c03c113036215484e84c1040c4050b46d42c00ca0031035074001e244850161010382042010030202d0065004090782083e1814541c0489503501500e42004d4043d14443c0300b079600711070340c22000c405542054081d02c62110b41c000c0c40400411041e81c0c0b1030078070010140100d070300b00d5903440c036040060300c4d13a44c43c40326407920702c4007201d41c05846e040030011030541d1110b8501042004403000c00400783c100040e5940568021100c54400845001510007802100e42040201340224000c010680065216802118044c0e00a200740c0361980fa00301081c0c440c510303011380c892102d400704200040c41000c500d511511040721100c003410700c03400090255601a017021040c03109003424141c000c00d44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 404856115 1107 404855008 404855027
    0x180b031903020a0c080105060a171501030b0406050c4902040806011a090d0f08040b190e0f0d030c0506092811101107030302060601 58
    0x34508000f03655942c443d805541003404007070301258048040c091a8450720018041524031880c0c400f562120101400e030724000c1d40589001102401d050390b800c54000c50203010a40740320305040c00c214045440150030341000035001c02c12a00c10648428002481c1500305c1c28032882d05104401000400c8503401610000300c1c03004070b003400c0049480c0d01034001e44011000f03d4001d681c031110100500d016002011007400400c1c41907080524014412080701c0f4824100e0f00d100440030394a40d0000d8102e5086040316000c0400d00301480d904144d07507040b03a442e00d80b078004010462200032424146903040c68500034000d84885400b072600620101c81c44030303441030132201c4510f80310801c141ca9051000c00210b0840d14441070454910395107166034505a000501c18550000060400030120403561015003072000d50910100449004d00158005602a8016001900e415030006140305803 = true := by decide +kernel

theorem cover : BRFrame.Cov 404676258 404856115 := by
  have h0 := BRFrame.cov_init 404676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 404676258 ≤ n) (h2 : n < 404856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
