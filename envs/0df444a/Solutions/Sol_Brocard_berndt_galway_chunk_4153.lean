-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4153
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:43:42.284361+00:00
-- url     : https://prove2.me/submissions/81738591-b78a-477b-a259-5355e1167e62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 746762589 ≤ n < 746942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 746763839 1250 746762589 746762609
    0x1e0e0106030b0c070b0a11180316031401060b091005130905160e060903190c0503060a02040e060d02090c0912160528060804150e1e03070f03080c04 65
    0x840d15103c1500c3d0355000003001c807008004200032a41c034203840d1240500c129101080310340342c41203940051a40404000b4403946c03611a0f0310401480905401c948402584114000c00980c01042d00746400e48440ba045401007540a1040f07099650341e108807000d8020860405d240d940d090303c11524004040c0740c00c500700d03031420304007030050b030030f020307681c80d1540403a103644100103441d1400802060b4814001da00740c1c0340d8003040f001d46103607607121101035011388203680b8a5081590388000ca802c2840c11112202c8c00b0707034081810040e40e540c46900903444042101c0040e0300c41c1880e40003400181c0080e00c620040e070170200c1c801106861304510313614081c3e010700464280d103845088140c410145405031a02404a0041103820030720a41e254001b00130400b81005506824600210f4042c407004105545d40343e04800440303e00d0020384601d401d01d14540f005000d11000400082061004d044e48980840d070080009401141c0700020302401c1035410304d4652010345031402480c0d514055038100310028 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 746765089 1250 746763839 746763841
    0x60f1215091b0604030807120908060405010b04110a12050726060102240412030207021c03110d09090911060408010c031a0603041101021e03040f091e0e0106030b 71
    0x59100091080604290b11101c0c0c050b000c0180c140320042c01a488020407100041c8040000502c8003260621091b0051520300512a0744600840c50940299400d4a2a075900c10782e035003040c01d0600410b00d490524102c1d09203848148907001300500c68407103d088010b582c45001c1043c8910810040c1c5422082031951580080384075154081c80106a030202c4c05441655003500780d03640c03408010300819010300002007007a07859403680c031070300500883c1034010142d0030041a001a9280190046401d90100c04544005030b24078000e4114142c0c90030b6072000e0b502a18003548103981c0710f0350090a840300c1130070101e0002241d04e0045080071101081d242d2140d0082800f0460400541c404d6000e1009a5028043c1071004c0d2115980c0900100c18680c2040d001c05c00603021600c02c8010084640d410310445480c18404610b04010240c0d2040043c11500000350030420241c3d414040c01c082c0422050130400c441d1880810300e141e0310301104611040340c5811030020003000c294401c1d0020f58200b51102d1036 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 746766339 1250 746765089 746765101
    0x50603060d06181b08060c07080703090f170d05090f010e0609090717061f03180503030901091103010605010807081008061008011812030905010e01061e0608060f1215 73
    0xc008094003e13650070b01400c040000d4007500000e4590041480c1d42c4510300e440b5072a01c40704055440600103600344000722400148201906684c1d200a04080308002d00107400086814103016902d00b66108008040c4440580f6548072000e94080e40000d00b40254040280303000319840c0d0041ca1196036000d11000200801c45402030100480d001d1130020088443da1500d080100c07010b4030381d9803001c00c802c900c4201c1c1c050500aa0110620400c1d2000c80500c24280b503403010325580c8102c91442099440d00103c50800a0100391031034501411002405102e0400300000e00e4414000c0c400f02c01c104140010854203c030500e1441d0140800314250756407840d192460044640c114454580e440d80381000601c82061214213080c0c81c036900130014060707071300700550440141624032030a480ca95038400c90140b11030300c00d104000050880c042d8195102140e140b280d031000801e580000c0a0181d03a41c00c1001a1b543e0440e28608540304a584032481c0b1106800e5914001c400202c2e07800c1300c0050402d000c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 746767589 1250 746766339 746766353
    0x60b04090e2d0618070b2b23010810180c08010b0114070c14040b030a06050105010e030607020304030803100512070e07110a080904140a050f0c04050603060d0618 71
    0x44540340412100f56882e51202000b1003000080050041d800044c4240300003200c0300c00801484104186440e0b68804245410b9034500154140312140c0355654a44402000c030f407074031440e102008100c203a003298035141040e61541e2401d0100414559240c0d401c0c040b03d411020b114004a8100c102005510b4075038000500034040141c00501003489818222a40300e802c0040303c0c86107901c4050540b1103490116007602010400c101140c4c05501d8001c0c6120a48080203115202c5008501c040384951401d03001600c281c800502c058000c2d040202000051600041120300b22640f1009941c1d41743d0340c8840c803d00710f241c1a004139a000140841c00d5616940c0018802d05403412003114284a480c0c4c000c0c15101000304c450800f000382c0040302e440000c1640342001d0400040003801c0807924068100f4a0000c604040b9110581c0070b50b290309000c100e180d15480075900041041880d49800e0030200011041d000c020f0415215038a0440c0f984200300703540d040f0000c2220781000c41c03018120a840d02003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 746768839 1250 746767589 746767663
    0x201140c0c1c05120711010207030210110a08010324020c0d0311090a0605070501020c12180f1e0a0305060903090405100605041203050c030a0f0f03060b04090e 70
    0x80d440c81081c21030460b002090044070305128071910345070714010748000324041c40c0500410f060705214921890f4800020203000a0049900c02d81c068480040d056500b5021a10f9102070043c0054003400b026085640000420381540e0700079200b511a41140c80b0002e061210310343c0c400d82098000300301d4451112000555418400c540d0702c01f4010030505140502e01d170b0140c0401c1aa2100d01040308100150150005116103401a0000f616000c000d002c024034201440c9214540a000081c030701c22524059461320f00c8006080780d50100e101c1840d00019142d400c0600381d08444407034070500c3c6201e076640c80b18503c01035501c581610a60701d0f000501d1516034200600c01805a03003010300084243c0c00e010140000d5400070380360a8142424008002c0000806040c228244030342042a0001850104050702e5008419511141c10955120005040e0703600c1c420600141818100103001941120040c3d40a5540280340001c00390000070101d0b00c0c0114401c0c1c18101c0c140b00309089a10404552410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 746770089 1250 746768839 746768857
    0xc0c020f09041e3810030c0608060d06050702010c030b030a0f063305041d25180e0f0d08040b151801081c05070b0402010201140c 57
    0x101640c290301404010107003103030700410f0940d01c025040030038201d92000d4201c0758010101c14000384100300c2806002121400c40340018202d00110040740540703981030b00e5000e43c40e1400d0803107651541d50345410540240c0120018400000300041840e103c1e10100703114941c20035070501c5181040070001e8001c10004110600103420030386180154100019a80580c41e4403540400051859445620003030400491407007000b030b0581d0782200b541e04000c0c51249292540c47c201c0b803003145001d080000715001c45114540c4e800f03034111107104003030001c5404054016a80c05100c221702c5d024001d100c0a00f8190030480031507900c4081d1044d401641e1b0b00c00e000062002048444411047d060156501841e21000002645c0403000070005003050032683d80144103038001403aa1442c13080081c0c0c01500c0322030b4041c910000c031001005500000c001903000f1200f00841041c06891b1100010f046200d10312000d420100381c02d01060859100b541308038078074a032801c9080340307500307000790050301c10382c4601c0913 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 746771339 1250 746770089 746770099
    0xb0f10030c0806010207120f031e090e1e1504020c03040902040f0803120a09020a0b0a03151e030b150301060b0403050f0106050f040c030b040c05070203070803040e19020c010c0c02 79
    0x3c2e039694000240c03c01660650196201c403c00c2ca591414862041440100d00f001204007064048101c1a03a550854074880e48071058a6424070001030b21342c42009100f030040c0040321262070101e104240c86c85400941100c02d01c9240500c1101240c081d20039144a1851884009800121881c103980036106135a4490b05844400e592004119501c0c003c003542c2a501a038030a000c2064410260f1103002400e2014101280b0551340e00c405005039000320840401182c0c81d0300c400320203140c0b001d111002400301c90108510450325220750000c0000c050000400c952514000308070a420081c04034107e00800400a0180300c2e118111015513402502c400c45d001e00c20f0100100c41d250040c000d81040c8c41020304009041e1041a0030007000e80001410102855505d000c60481601e582c02581501a02511815980c00350f074818945820b400c0d40c000350790740d00140010300c0013040c1c1c1d41281d500154201e00c9042c4441d005030103c4000e2040082003100356103050101400e00342c00128040442e402118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 746772589 1250 746771339 746771341
    0x40906031106070c06111501062f0d05070c0f030809010906051206060a230c0c010507080f071b1818030c0b090102070609060209120d0806040b0f10030c08 68
    0xe000302c0c1d020301c80e001008000130480600c1414490700b100540802c42038201d500000c01014000c444050a030000d500040c0305248040c90005400d5043d04003880100d44903084e50b02d40b004954a91014244900810100045d5103042c415110f03000409070091410007018245c1d00d16050b544c545c407141c451404110b118400241c46030058040c1c074000d40030301c81c0307890665568004208440d030003800c10b0800d0201006004d29500f002100c81380c01d0241280040c1e80d203070081c10049140400c09080181003060030049180014505400c3e5510b9140e44414691a0409132402d0f61079000450400401c10341c0d01000022089200e148081040b10403076000c11003000040324010195400080107030118440300d41000c0040c14030410325a00040b500c00041c10076549030303505025115102410307101d00c1d1b000308500d561440c141e11a840001407140080c03c01c1d03030700740c85e01800100c4010280c030310456407a0411415902d405442d0503003032030000c0c201c0414580040c0054014402084900009800c9134 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 746773839 1250 746772589 746772623
    0x10f0e0c0301030308061011100f0b0a0620030705030a080a0c03050c07120e04111b01050714070203010906020714010606020d0212030c04120803011409010506070803060f0604090603 80
    0x10101c034107898041ea030b0788500d0fa440105211452085001102c10040884404000380d4824403004440080c050008503000080f1040341c010744140e030400920a455184003008820703082600841070340c200c102c64040800a0301d034018114011100045c10790f000008800f5222079000080500ca690680c00c1041407440c4c001c0101c044030402c5941400403c400c0061002003800c40041c0c2e10b00c0300c1d140c94a111000005008039050f9129602e04170044c3c180031581c54600a540c0742003075a0400c40034020410741c138003100700500701b02411144808440380081c001080d51000e4015a0011390400d03400e640e0344030140f07040d42a200340d6075140420742d484d284020410320710106844903218290b6004180001054090401c660f0018041c2e00b6544400c000000d500c80d140740301c001c400c9028003080360712903240000c07020643c101018250300c6105c02800500041d03079281c040c0d80c5115000f14010303450b40d0741c842c0810780714500403042d41d0b401200480c3c001204810340d0805002c0d0781c4500100182000c0c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 746775089 1250 746773839 746773861
    0x3090406081f0b061b010b030f1006080d0203041a070f0f02120601052d09040c03050f0f0d1d090f100b070f03030b010c0605010b1b0c0a030b060a0e010f0e 68
    0x802c8440744d202ca800c0001c0303003000380001e05010300c644000000203001000180001e1a0813038a004c0c07210150081d00d0b448410f8289031017910003c2990902401c440b04000800948030303c55401082d070728501e1113201603450300c0c1c80300c1514500c80d401008503006818500b408002c00e01c140f24100e00c205031801d84102d00540210342a03049800240c0103075840c4c1384103401941c0c1500e040303500d0070f1201820045a02c040c0e4a00c00024025401240216046d5040d801c0c241e0034000001d0704d01d452039020341c0740e8503a8010005500c03c2500043d2800740150119aa1f04d519444441c81440da0300100500a01c100c0700c0c0780316440c0740160000d0441c0d0201a580b0740c0005441c0c01400c2028110100c06a00b95010a020b070300681240341c0140351442c0000c426a42d881b085410030303004034168000100b80031030001d030460080480045020000c141c1e401c1c404000400901c03c90000820b0442c0a41c0030a4030760b16610304c24005000c0041d81000250b850b0311034029807005c94810310340e000410f003000c00d05407044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 746776339 1250 746775089 746775101
    0x3110d020a0b0c151503010b2e030608010515030607090501080105061b1c0305010b16331e050103051216020402030f0601020f030f0a030e03090406081f 67
    0x4050000c5004614003050031416400c40480c0d9001c50250149004c0380a030032000c514850410043c800c011121312000340b5003103c0e411701d0070700e000e583d880680c001e42a0541080302c0a4a00c14012840c140c5076144003280a4041ca51204040d982841c05224003106000c40c4c00e0300c40c181c00d0302150031654403207074221001c0c540c504c52a270210b0349680c014025414458001d02c00a09010901111007d00600042c50614102080303800c00030f0711410a0346440d858046d02d40107000b2481d107241020007043e0017048d207804c41e03c4010034085500d6100f56000d034010f1309004041c00e03c5409065580580210a009000002800c07004070020021510141c1420b200319270589400034014200d0807a0094410740d554400740b4001103541c202c619a000503512400210b1103150440d509800c1030604c00300281c50f0a201051b2070000e50018009a1140f01000c000d603400c484640c0b40c0418006100c90030142540300d04503100f0b41107828070038007080f206000200c0e1000100c0142b6080a4018131654601c11256 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 746777589 1250 746776339 746776343
    0x203010b0f0d02040b07080c0d020c0f040504050a02090106020f0c10050703050a020304030c090207020103180506060f0f0d1a0c091005030622061a04030b010605130308030f0103110d 80
    0x106001c1c00311101c5014000c1d041880980c41d0042c5426111440c0728160340117410100c48681000030041000b0000b40030707000072a42c1c00c0c0000c0c03100070700c06c400003680700c5070090907a070086540320005814000304121000700c803500039040d541e031035841c0c1c04001e44030040da07102d0718400d102c0d502e2529000d08280c10002400d1480d0750b116800e0840c555011501913005100b46000c62205000c0807000c102d0941c0d001004099094005030348220906c005002e540c5c2e04070129030002d00815181001c00c80c046190355000c01c0031299424030b20440310000e40e02800f40030400d608819044084030401c080c0e80d1203010050080f60301c40c89650340351160b1a00622400640c0c13600044100000302384a030092000e190402401440f501070705076000000b82031005122101111030b0346031103040011120580300b000001c00c01e020a14a000e085440380c0c20041810722480c010840002035040750701c0c900d96a41030207568000e00d05507030b03400c05410040f003c54082c04145c46400d42c9901c0c070310040c40c09616801c1620327 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 746778839 1250 746777589 746777609
    0x5161e080c030c09100801020f070c060e0112020a030204080f160b0c0d200a060510061803122706170f07110708070815010801020c1b01020a060516080a020301 70
    0xf895440a003c101d160103030980c9400148800c010070340fa84280060103020155042a0303456141030f04000d40314074030552001c4180103006890a1199a0003e032014001e180c000b005a503850070001708030020f01c103075442440d460181004c2c2034848030001c10b480d0381e82c20903a803406040c00c0e11070084002c980315105994805501514280700c0032400f56926030b140345005c440c50901d10342501204c0b41017400c06c190488045980304108034121080c68840c00c090000c505c0c00d18044206020307410503201403808050424900300c81c0030500c45102d14200e1a0042e103413004000c010f22480c0c4805421141800f440011170340525414982c00c03403135020f55106a4407050114440e032901f00040d02c050000700b01025a6000310180800c1c5000200504801414072900604c0d2002581d544102c0801301a08030b1030b103d90041005100e5220300184204021240d0001c1c10444601000181c0c600b400300540284441c3c02d1008010a14450401c40c0c505070b01c02d078603003030820361703034480398200300d100034040c9401e00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 746780089 1250 746778839 746778853
    0x111b0309030604140a1202060906010e060105070204050619030b150103090f020405130c06020304090e01140708070c0f240c02071401090e10061d0f010c05161e080c03 73
    0x1003446282c9008079201104c054501c00c29141d120f54064000242681e4051f074868002e101150500f00141030040801071060182d50a002c40000c0091042d100042d12654450f0080382c10341d9644000940c81200101c0c0e034019040da01d286c00c0040ba041291b629030324040000000d0043c0d4081e002d400300e802d9001400540d4500a1343c02c000003031201820003140b0344101511038002604001d20140036180b280c0045464178540784001041c2d1b00c07444d5444040d80d04101100c0c5449018803030280d0001514107140c8800e0381c860000300ca88115145010304650624003194081c4140c0c583c1c491055000c00c1170840c04020000f800d0b4080c0c9100e5030788a801039018100c200706115460180401d1540149002d402095842c1d006109100c0240d6201d802c01d10b20010410805800c0024101c200459180e03028290310703010005114510301082450602407150000f0f030800030140000106032007520b00c0d00d9520760315401284141208010300c1024001610008100030100081041141c0f000400410107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 746781339 1250 746780089 746780093
    0x3150102210301031203020706050a0b030c0f03150712020a0504031106121503010b0303030a1d060c09060a030f0207060c08060303070506041709090106120c080702210409111b0309030604 82
    0xba21075109176540826901303111001c0066018010b46008005440c2e000c1003200a034010582446411013a4a04c603422800d4504480d4502181c6401c0300191050102840d546905040d102000ca10000c14505c42c0300081c020b050a41240240041c0c034010a5031548010b550710078009a40701c0c0c80092034542c042e400004404ca880508103c903a2000900003003042c00409000c0391845e001550003072203264507100c03840d03000e10b4020601c00c101007212006084a040c22441219a4801d900205000d9000014030080071402508041e019400154017155200a542044002400104003540000e4148004a01213142c00415210526040360203400c05860320759624007a03140703135840f105202c0f1040c4110b50180e500e18110034000c0407103441d8400740400781180d00c0215003a0501001c14001ca500510a060b40c0c00520110245060300c5610214400c0c01200c0001d4050f550040a5070b9061030f008524840c2194007500c4611906900a65491100030100fa00d078060070705155016032101d400600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 746782589 1250 746781339 746781353
    0x90903022e0905010f020c0601053c2101020904050615042903010e01031109010e040f170f040503070e0408090d110409061b08060907050a050f0315010221030103 71
    0x100d18410f5000064181c00b050401c1e080e42c0216400450a0304464010000c504102c1a100340000b000d0380455602c010f0503020401628240d0300c1c82c0c1c8401c00000110415440e00300a24070480c102922160b242e003a01c0724124042d50049103030320301072810100818900c1c20001000e600c4100754903901801c1030704004481000c0c0400030f000c2e4a8980d25580024442107000c0011400390940c604407041a40c10b60501c0031740e20905002881c0628100d40c010040c405142032165081680220300441c006150f04015010000c0c4881440d104180000d9650218081c13400900482d802601074865040d6030b08402c8101742400c40b0041e005900c100690145803400c0035035820750300d118821789480e000880010404591482404540c4282c0da203c2240340d098904030a020f20603031031315002d44e26280c0380c030100e0b4113100090422814080041200560701d4002d400303980c21114400320480d01ca1600b000040c04074984000c0a40c007601031403401c108410380040700340840a00c0303006031750700c1c5910f15a04c002e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 746783839 1250 746782589 746782601
    0x10609060318080c0d1805030606040203180708061501080f06040c09030c03061e0c120506030c1f080c0a0e06070201120f1508030a020606060a030b0604090903022e 72
    0x1084451120046400541c0c400040d01d055101c0740020032904840d17031300240c24074140340c603070107105003650000b08081c0e640000c0c0d2580c403800a44001d81c0340d4484219030350115103078010400e4140940f0001045065000a0052040010840030550110000010344800d40c0658208107289204e4000460504041c0c1015005003520325040c0001342d40c030b403111882142c19400c110341c3c8584503551206080b480c0e00140d00c00116400007005600c81d184005012440000c4c01a503d03561940e0000300a690248150145045c024003030101800c12102500d8001c4030034030380c403000f02d2a1030380403460612201c81076950008140d107501c1c4580301c04804100e01a04800e900301e04002c0b0194945100c04014000e10402440510010a00b02000302401200101c00c1c0c10020f52a441070217101149980020001d801c09416588169180b0344144110b0242404144880c1c00c604005070000c0c0705c402c25881215910b01a40c2a5242c50403288040034031141000c62a0045184101e0001c280d41500c0e4070203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 746785089 1250 746783839 746783861
    0x36040b03190f02060a02010f0518061b09060d050a0c081b031015030504030e0102030307020d030e0a080c0d03180b040b100503010c0f022103010b0a111e150106090603 73
    0x1c1c07034040002e64002140c660101e580c20005035151658491204441d0007500c0c0c11940040f410301c07404001d80b00440d0f4070b0314024000c4020110b80f80000040300c100700b0489611480241c031481e80c035041c12481d1006450b043e036500d070040340f13031244201030f10b0b2148909038000c2c41010b1449000066007400c0840d10703080038100102202c01900d001030741c4820081d00c00380d43c00c25610042603614013418064050980100d03858155001001040032190380403030703200701060541c100015540301c1840003518102007408002e000d00d200080c0414403050004410480600981c3c040c0400e6040070860780000108180090126800c5800b040000c0d0070500c480b0341c02603040800c02a06559040040d00f912500c0b21142c3c0480c0001443d0444c0c2c40d8107104500c5180c00c600e100e128888450110581c907480148039441404a010400340381c6a032080504003840c001030003c4a000c4807258514421000b000004c500d03440c81340044440c0c4203083d051505040380c210351683c9103032a180030002d4015140028070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 746786339 1250 746785089 746785103
    0xf16060e01060311010f1409040e03040902040e250e060c0313031b09020c1e150703050114100c0210110303040501020a180f050f010536040b0319 64
    0x80401002d100d81e40055000c0d104c07800741c143c064000980100d018600d1071040009502215000c41c00010440d20004410742c2e000400b111030580e803c0c11801540c204450306400020006031903a020030100d13000c6c10021610b03005803454503d0035203001104600b0600410412580b202852071f0040142c00703005044000ea03450110304802c440c440000d15002282c401e0918143c2000f82005036540c0d0001d0700006004500d4280140c0c40555034031040c0303105d484002422003a090700404103001a481e141d0b4842c0340040b1a04000401901a007001d02031a00600e034a810012001d1a000382070107450041c507128041081003503000c4c000c4100035282400c080c001c0b00c00c2d103041c49a00800c0110702c01c03405140016190007141034010300202d0303114400c40c03221200510501517003401100c4a02204c030110b62404423040b2540040e1a0717402a4079040c81ca030480303004140c840d5070058003080b00c4aa001d503c00760f040046a01000125404000107582542c00540f05022140700c19512103044c2d401040c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 746787589 1250 746786339 746786351
    0x9030507150c051507080a020703080f041b0b04050418030f030b060f07141b03100c031b2d17040f02150417060c0307180f140102120f1606 61
    0x4445184c0031503040d802c070f412400c1d43d04100085900c8210190070030785109041d45445003e480007801e0070405130040154100d1100814104002103081410440d51041b0305852185c0e2031850740000d0300140708060050741082c08296400b40801082250f442c1e158841d44401048690110014107110280b070390000410000708a6244064015016603842041442010120120b485040030012400e0030f4281e6420540001c07a5a0042824506580542c40028a0300c41e1808101c0143c0301420100300980e40e411402c070845a481031403811a6940554182050481111580903400311905d0910005410406005883e100745c81d4080c0c000c2d020300c1030800100c556030002080245221040200c2c2d5800083c00c004d100362402107601c0c0508c040c2c0c00780c6800c0c80e2400c50b884491100420250404c03401c25101604140d0b80d0b50481c0c0646003a0848020035600c40044044a80e0789140740ca015110741115150011000c1c2d049481444014043d5402c0c0822850340208100181d40101c542c140c40361 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 746788839 1250 746787589 746787593
    0x2104030206092a01020f01020c0109020a080304120b09010b18010303082401050a030e161e03080a0323070f03060b09031018080c0a020109050402070b1f0f081b0109030507150c 77
    0x100240402000c1c1c0d27000020f5001c1d007441000001041a4000440d039001880100010303114000b06500a0f60413640d000315559070049224010b01e0714480266029440818013034200c0ca501810a040e00d01c2902d401c0b540303403290310807811001c0992600c546560f18400c00035000d5481040a0011154107080c04901c10000388121800c20202c2041c1006001030704104100340d844680b00c0d0f01c500c1d14010314055200d4159103c0421512810004000345529900ca03440c44046000041910748285154000c460a00c5800100280400148a80001e050a82c04100485007404030340800000030010842a05d801c1100005481034020304140c001102d00d443c008544604018020020a4409050480820720001d4039509a41c2c015500551050003814001441c4441d104e4000b0f0010310391021901c1041034121481c00316070009080240e546100080340364000580b038400366007085000400380300788001199240c5881c4400740c03c550101000300301c0300d20860100c0750100c62a251003031000e0825 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 746790089 1250 746788839 746788841
    0x103030509030f062d0903030606030c12091f0c17040305122e0501120515060c150702060606071b05060c15070801050f040f022104030206092a01020f01 67
    0x171900b2a0112461090060072074201c802e0180701c0d1444281c8907801420b0a041059603400003c5c041802000000003040050f02904161201181c0f240711403c002c0c54000c1d0380e00d0b100c0c04281d40c0c1c0d04c106518120026241c4c0e4030360140443c181c5207507459104d84012034001c040072001c050700079801e0100400440d40050110800f075441140105030618451210b016039401e5200c107802c01070560002c4031420310041e80d1004200804800050010655031251350404203507a80c280c00482c1d200c1030001d01c9040f10750000c43d16071a5000c0c21001c03100300d60b0711004140c0e00c401c411255181e01480401200f400203516600100c03030503100c00c030046500b50b114800300f019944020890606130384000556814001521203582e8010500c0c5000714141d4580340c0807504e20f0031410f444910882e100d1265a050000d035034182d034036420b649460041c214072103201209000c5004c0e6002d9005000300b1001486020300043c1d58000404c420410b0300b0144011144940c0030303004802464110f0080c0d81c5500002142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 746791339 1250 746790089 746790091
    0x31302092505120121030309020f03061005130b03120d060f060c21050405041820011b05070303030902061b0105060310090b0a0506010c0506070f030f050f0103030509030f06 76
    0x154403001d0f900c908120700c24402c004140e00c04e00254004200502c02c00804040342d56180d0f626050100d080300180c80050105000e21200c60303050322a1030100122171000403440401c40e0000c0e1800b0351035440070184281550007214005415601415102070b110100c1343c0206401040700600091441d1940501440003903968000d1002a82d00c8002c1c506000000242d03200040585000c1e80b0003041c141c0c005403240c0100d226443c403841d511f0301a0f20540000d540c0c400c0f0340c075074040d8601c2c01d220b46540078942d00c44151104180003400c4004540c0c00000101081d400040e080760044c4480307869554110701610784141c04980000d8240040d45207050580c01580d01d1402c17207030001c04c580c40c0c0402454a0545460000d80f40d6a04004008003c50814120716030484801080803d507941c400e80107032a00131240b4401001d9104440800c101340f54008220341201045d542e0901906000c55035100548209543c44d1310301c00486401040000c0c06840103242d0080060103407065180295400d60070884 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 746792589 1250 746791339 746791411
    0xe1e09060f13020a060302031905040807060b150414040207020306090a0203391c080403050c04111b1002070b01050a080610150c0f230303130209 64
    0x408182800916a003540d1a554000b2202200803941d220302e800107080e01030380c1c1c40b401052580c008007041180443d100454010808030806000c1c0f8141407402d6401980441d4065071482d02c0c045041d111450720400812030b418142a00c0f41c00d02d81401106c1c150101032000055001c0c0e130811201e001a00d0521049220344206030103010000c0d941e0040c5802c150b03c4500c0146c000c0d2280b2890114a440303601104254180070b4400c2c4030034845000481c40142000e401520602008081902003040000c001c0040e24070910999030a6401c910900068070910100410311409c20310045407168007204102d0322014000381160030141400e845d00c03040f03030301010050340e4139002d43c070043c081c0b4140700d61710300020000360004003041d291980200364105114001c8900651100e001000110b00c51401101682d4000c00c282941c00310b00d11740014032100a00784503202105240703881070001004001d5074403400710030000c000c88181c03136420040440c0c070007850f0306140c0221031111001c9103250051b41641d14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 746793839 1250 746792589 746792593
    0x310170c040926090d110d0b09030304060b0312040b160b1f1e05120309041104060f0c050d030c0903060e1e070f060509030321011706040c0e1e09 64
    0x2203050005040c8040780200f0700b140941c42006440159107402c4044900140c012101c841003101ea40005080c40c00e03001e1000d0088035429060005826000c0010340c001e612400c0b040110b04210720a05403103e4012940103406d2106020820407080a080140381a4100280c0103025440d281d9031841103600c240c6603a4402515461a2080000116060400350910070707845d554114540c4c1606002d0105c50180900401c2e485402d26060392003081a1152504001c0c018031003112403074002483d86d04607200711400200c50040926040d405840391014103600480039042001c2c40d03a07000d42c080d01e070015010023088205080040418150311901c14200c400001500030782035264140c0d600d8880d001340c0e4401d00c1e0080101042440c0d50820100c0c1201c1c11821320070f840760100c0b4006070550003000391150b010b00d5074090020700d004401100905071481d051071a10f40d400c861142c0c2d595050b04070380040501c50f4124043c00800c00c0d0041b8560b1201820101c1e5403100c104214101080a042e92101d0082e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 746795089 1250 746793839 746793863
    0x3140d05100504150b16140a05030d06060804050714120709020403060507110712080702060c01060f1505030105060306030115120c12110904020f0406080a0b0c0310170c0409 76
    0x50302d020300071424400c05900d032014845061203170000c4684290050080d2076000c445003103040000304166003916217820001d40c1d40004090500503280c2c0e00a20703116003101d02d00b5001203900d038094200380d40101d800030000e18580d81004a0a85265020100c207544a000c02c410f41d003405c00100820f50150a006401607211403451405106451015005d1b0040c4810a040d0707842928000508400315007021540000c6400c003800d103588a031181680c040e411000000c2c642000c4401504090b040326504211200415034807003030b120019503003080c0300300014410401040b01e403410501964100c20300400014040c0301100d0120082e00f01584401c552000c185120300501c0102c03603111000380f022101947e05400199103422440d194007190760303c9102400041030039900d842c0b519a55958000d042000071540300d9025a81c1c61035282c004039840d480050000b1154850181502d001d9000414074a031018100700444288451100c2914102e10500c48040c2050744c0d1405100b400500030b80004d240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 746796339 1250 746795089 746795099
    0x1b02150601090602190c05120105040c050402190809150709080c0a12030c030306030c0807180b0102071203020a061104170d0e0409020406050303030c03062b03140d0510 74
    0x8049005141a05020092604120307644d000b083e2103181242c1d05158600a059514000304e140f1510380001c3d4002c0101040c4400d1a06c0550210780170701d00900b0241c00e6595200100300c1a80700c0c0354081c50301d203100b2801640b169406000483e40101c40c032003c1e00e00c00d00c005c084015070004200c55036000500041000c001a0105001507220781205407004051a800c0042680021401060003000c0103210500001454401c1d40280c010719844030030360b10160356480000da5201e2107400b5884059010704c0641c103aa40e00c80c428605102d0045e00682040351a000200400340070b02807040c0e042d070083c4851745002030024411310314805400d1000d25201d078184466a0000004d90092891944c80079018604441c1c002d01007118000301110081020300030392020602a04c031707035804150144804814040d143e15140099403081009503400b0903a00f00e07600000801c80c00d00030820045601c40d0614401007403190b1100001d200d040c00c0c0c81c600d4400c1c0315440104580088800c0300720b07441520000c0c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 746797589 1250 746796339 746796373
    0xd0b030312040303021e07030f1d100302090a061b300206160305040302120f040b03010806010311030607050f13030b071716120c0905060310090b010c0f0609061b02 72
    0x84446140c0c07d08010f1203a07009400121015950024030044109500c0490342c0d500c0c0c03d90040e54050581200a40e12040c00b5002e1341000307800314070401c02000302050340d9101d01840c0080342c0c02d41f030341d07a1380b400c249844207003c5018100c69000012240c41d0309000e1103040d4840d0342240c1c0c07040c0d80209520718044611410300c40314149a801018184010b0002203540050400380c01540c1c507200d5544d071440ca60200b5054422580102d2001c240800005000040421401c1c1228061030503004d494007840300301503e815040f2a6600400c10500c95040c0c51003050015118411070941d0035510310ba160748609400c004116110400150011105000ea41280c030041e0740240e410900c09a4980841c4005414038007100f0403900c100c0e60355549440f81078841d4605000404000d480117549013404014422403c1c00c9014220180307003072801c171030a41c1d40304890701d6041c03d40100c1d10004034080d940d1401c015107a100350655056407100b003070981c2108100c1c698070341003c0380c0c1c0041c101800321810060f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 746798839 1250 746797589 746797627
    0x40302060705031e2d06120c010c0b0703020f07081b01020a020c120304031208070e0108010501090b070c0504020a170105040605030a15060801050a02120f0c0d0b03031204030302 78
    0x1c00c00000744144002131008001442c40e0940c2000b09120b25645e10725036003540d600030f800401c0c07102d6075040c8141000c0319140d0240d001d25400d86409003070b0300b1441d8075181e840741d03281a910700250501c05c0b4040490204030a079034000145140c098607003400b1840c2450160451841a00d00c00310020300d000541d001000b040103588286402542050a1080065250b034540842030340034801d60388192541950a008440296921010211400c3c2c0d00200c024078602040319080041284e0100003102c2c0c1d0f000707154182c103c1c1c00507992520f0703030f81c100b00342444550410030b0100d4250000082c042a1966540054441d101003640c0e03503140140051065500e1650603880348ac0140e14245080c0000e0700c01060854401d0740040d0a04440040242c200d001804550300c8a0b40d03030352908090019004a0707800800c000c2440c011034952035211140d100d00c05150944004560801c05c100b00c640880d19600011028040241503d007402014412030f41c00410407202280000d83c001115461145141622 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 746800089 1250 746798839 746798851
    0x702010f060f05130e0c040c170a06062303060409080c0109080d060e0609010b1b0f0705120d090611030918011d160e0f060a030e0f0c0d08070804170604030206 70
    0x501640c410348141a40b2510046c0100303024a4981d040a054180241d008188086008030740d4040b40c034105000708024100790095600003805d205080441c50100f050a640700041100d10b00c1c6142c4038041080018040c0040488030714030140080c9070000360a104140c0e5190091104c4c80c0c0e0b81c042c0f00c800204859071504055400ba5a0005200058072520700407810345034100c0095a9552102c5c000980070700501540007194410b4414485103802c0100c0c8100031a00203840143c80c4010704c0c102c45440b000b81680b0720000502c54042001000d208400205607615054280c918050b50440403170000902c400c0c4880300b59504400420080d02c803003541d034004043c15400d01c001404c0210101c0c544110003030007801000210b50401e0349503985c81e9616010b8010080c00b0300c1d610068440e018000d0451103003212040d01500602e008201004145022080002400540040419907d000687d0015030007601d10302000d10005c00c00c0154103c2d031034048100762004000c2840c003807500900d440801405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 746801339 1250 746800089 746800091
    0x8061e010614040b0307090f08010209090f040210080403180816120506010b070510020c0a0b07020c010c02040f02040807061d041401050d03030b150a0e03030703170702010f060f0513 80
    0x400d104400b0320006682c299000340868642d0303616188802c54104110707400904810002110014042c00b055000b0a03100d036044d21002c081e0340c1c4440d05624400400c450294110079003080810f107036441441c055501500c6030414241155083c08602c441c284940c12131882c9520061480b200b001004807070400030400e0381101c0707a04940307a580381500c1e503c06100d1640b51400c0071a24808106051199003800c60654408540b9560403880a13541d40404440c2034402c816610b010944841c80403401080c0440c040c0c4032050040250741c2404001d062000801c82c016609020100f241402880098001d041a0f42c2d1020185010000c1302000a815101244190720b4072030349034a144020255541181c50071105001d00e2881c90405801400f220504290300c07950902c9440440d0b030080c00034007500c10540c0d661502098000c0140744c1da9205610016002c0340f080024024403040201c401ca500035078502c00413600030b1690b1410419101690018a5255800102804641010034603e00b0300624070718 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 746802589 1250 746801339 746801357
    0x901020307140c012301140a050a0501200a0f140313050f060c0114090d0c0503090603090f07030c030b06061602091b070b160c0b061908061e0106 64
    0x600580b0101c040310319205140c8000c280f403c2d500c8029402100c40c108404107012440d141e98003c2660200309008011503002c083c640c080302030074050101c1003500c00280003820030701d0501c801505d49081c00001c21003c0b070700782484408014414044410320030f01c201c2900d10354510700d00d898068828140340f0603640340c0c000e004030702c0310801800d03540c02150029202c0e039440340c541c003010403500e04c5414540c0b9141d60800958035002e00b41840e010f4450f005100c140d5020082e6118100c8a02c1d40364440603015a1052241031a1807411100540c7c004006500f125800001d04040c2402d01603503a00603600711012a000708180540c80301419403046007101c001d80340038607541c080102034a611a0103030140c0c400c5d10000c2c000d51612000000c41520715440580c80c2c49091030400c2020104941c41c4460320709600c0003000d4940241c031805410383d40900c1e8410030340c3d250002e0245a0309512480c030050076001c000000c24450a0118170300a0001b40c98000f440491031181004880703069105504100303040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 746803839 1250 746802589 746802601
    0x1d0405061e2701050f01051009050a091104081525081f0819020f030703150209063603031e0d151205060606030f04110103140106031409010203 63
    0x400d9a079100c02d1900320b001100004042c4a050303030003600c00c400410340c03800341170010030b040104020303040b1241294a440e91002c0920b00300c0b92128144106904100e2a62051040750042d03044a80035515803075400c1c0c102a92250070524114580c4c032072030800000001448101140c020130f4103c44c86c1c40c42c0110030b03607014041c0014030309400204280b50110624081079a072900c600041e83c01481050100c1c1c820b44c02c0c0c22001110a00125400c0348a8040310103500d00303d003008030f80c0004498009403400e03010542607090f04041d41c0220721603a23000d8000c000c40a50742101c002c0314840c100540d8501610a5240d184035001c0c500c060005520a620a114510790660328200d04400411450303029034603401885800340280018811070b01501041100114144407404041e410507402241118103645031042804202e200a40c0d030004515540c1c800500404d085044510001d1010b1500280d003d203140302c0103103160400c0e040000042d8881c800407815030015030001b81c002c00e00d58021850342c2402c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 746805089 1250 746803839 746803891
    0x40203010b061210122409120f081f05060c03070204060306060905150609010e040b03060f07020d09080d0e01020a170d2004051c0609060501050a0b1c05101d040506 72
    0x40b00f882c0c01003244121b01041d01c007034102090347c960000c0500030308800184c01030020251031544100140700400012040b2040c00d515504545000c202e508586041c0b80c2807119607840300d01c4684e40342c4010488600141c6481c4241e800440c0030710800545542040c1080b0141c65000d40b00025076442001801816030b5040120b0710204004d08250443c2c04c0380c0c50218003c0c00080036129810700489040041280c04801200d100d00701c40e034242c0704200307085202030740e4142040c0034191080e03014980c0703031000600800c20740848190500450344588410395131118144502c98201d205020701250104600c09240105580e41d074110481c1001041d5400c8880e4a602407031058030300c82d0101402c8901104240c054015106810a0060141c03500c5400d04002508080c41198020700100788005000c0552505903810740780c8410003400c04003040d144c032501401d005042c5560003024004002541103000c040001c00030b081050000b200e1500b81004c904082005040c1d4040e0b0941c000c00740003007406 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 746806339 1250 746805089 746805113
    0x9020102060a1806060b0702010e030a170a030e0d0c0210050a0c062705070302190b0703080604020906040303020c0a0608040510023016020f0d08040203010b06121012 73
    0xc45040001d0302408150200301c84440f40c2c001425240c908071001c02d02220b41c10040807017a00032389542410b411114245580c0e4104980081c056648890301c00110b43d6141d00182020b980914000c918000e10304a07080c02c144070200f00744041041f840e03030f000450a0610b08952446014100107080c0540468081d0014092941c018155682c1741d5941680d12401071a40741c1c0b1085c004031031101d03031102d0320345281d440741107000076442086400440703c1403180c00c080c05426a00000e001c03a040140c0341c1e909488100f40a4240c6611540030300c0908155250721025000541c0661300a00b81d03c0000d030207004410303d4a0704482e040001d0700e020071002c60300000300e400780280510801661141003e412080c001c0100800290b4014050482a029048000c07154059555404035200c00c003c0427600340d9a6034082504044150005101101f605000303450055010380050000300750303059114000f4040c0e0b0b006990301c0303071114114401d1000c10714904040c580982001a140450000e103074485882c0b03050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 746807589 1250 746806339 746806351
    0x102130902070606031a0108070e070e04150b030a1a0d050703030f091d0403021b0108070e030c040c021c020a02060409020304151104052b1e1506180902010206 70
    0x10300010b0703800400100d81e2000c0000c1d9001881280410754201c45030204504c28400c6c1c0016109481c8040b9001351403403038090145d0f90903190750b007040c0c0c00b00303003440054031165000100042000d180000d0901e1240700561154850000005100300804034180c0e0103110010500e00820070340080c4070000c2d000092a1042d65003609162925444220741103862101d00e030040c1d0301c075098402c82c400c2e000355502501c3e80102e11a809442c6002015070f0203d0014100c140e0b0180011000c0b0080b801032806072645104071403002e02594511100d2002080039600243c110b58010b03481000f07541c903842c400b110082c3d56049540f020f444000e400c3e40000d40280918043c54068541c0000444c003044441101515070243d641c60502c01104078504020b4941c1040c1700700c0c0e0180080c49010f0300117044410780607400d0f00c080a03c5c2c2c071a050507034448040303030350302000b128107030500c00300c00342e004900601144010440565400700d0300c1401d001e80f14803480c603503000c10b45001d030806599000503a000b085107075000c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 746808839 1250 746807589 746807591
    0x1101050c040302010c051009080405040501120c14041d060f160206071404080d030608010c0c15050604140a05010503070f210510140f0c071a0a060e0903130801021309 73
    0xb2214201b16040c50300b00030040d0303103407441c1141c15400c0003590009070080311807c80d4200f21a80c6d07240c5c407a58110b00140f0000b0455203141d0b000b48600c0e44078000103404c0d01009800001d01400428000d01084c9802040200b903520110801100c205102d4100303600c014000745d40407192450f41d00c042d42d140e90107406402403200c402c90442841da41d12080d85e00030102c0104580c40722601c0c5102400419442c0140502035090030740d41c103011806054408110380e404000500c3c158a00c5400c180280800b40503d540641c44540e9031201101e0707590010300801200f040010300794500420546030004a600ca10020480d0303c80070006403021060720848284000c100010b150124604281004a100c00760b6094602d0b00881d511400a000f844030f1065001b5443c00080d62281580a0224060323500c0050001034000b04111001d0140100311390407401040300407450513100e04298481c4601100c4c804001d13440460041c1081c8001e03642c4e040201100002140f80010061032a51000007a0050802e15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 746810089 1250 746808839 746808857
    0x260304050612070c0b0708040b010e070504030813050d08040e070c020f10020c090109020421050604030f170c070b0609010509180307051005040201090f0b03181f0b011101050c04030201 81
    0x350103800008141540300d10002010301d006d54001c0c00c801410703102a9224519480080340d0741285c10307801c5000d040c01d900c88504052440d41d88100f264040e04006503000b800800c0000d081e261112001c481500c04c8006580380ca0401107054050340f0020001420444205c0036200903031203140a02e02c2c0c010090b10358544902a000050785441d406200c11508820454000100440d8540c0a881030b501ea5144a901e07604111600c4c600c80712060102400d01c1c0c028030f020a002078054004180d0684a90a140004656080112202030f104032010b4403039520001e054020040400d00c15903000000f01c554002a50500000ca00740d910010b10441d001810354030b5400c070218041003540c0c9030590100889511299041414002d484150340c200e001c035403500004900004c2030034010045d124002c0c11035040d6a1241c03155080c174011310080c44031900650081e09210198a103000994400e0340001040c42e6050a000411424401c0e0303d0034841d91405050091804544040380e0480760246860311071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 746811339 1250 746810089 746810101
    0xd12180f030c021f09080321091606020a03080105091b0d0b0306011d011703031b121e0c0406020703020909071d04062d0c020313260304050612 63
    0x40c0c004444044c4d4071410015080c03084d02d00a042c0c8121a01140e80d4070f030708481d95521035980c0c0303001d9045200704070742c0b0b044031402315080f484044580c8100034500725002c0c03c0c280d111004001d585d40d04080e0060304150440d6040c55008440c450041006580f1060240703810f10060f1124101c540c004445540009081c4680c13070ba094100a0254000506544903940d465440c000750340d040080303400c0ca4402c104000100202c1c056981c02d500000d441c00f070340c40e555501c0494041c4a415903500600aa424843c40b01108820781c040c170700c40c51680041d424407417040ca410b1000c0341c0c03006011400014040100740252170b40440d6842c100c1e581500c0b09906626030b0342440e818a83c2c1d642201c0d00500c09864000c000322400d0042a0165010b81c10070000f40d680f817101c40380f164484810042c00032001c641855001ca0366a0700c900219a000c1c03050f070f0f04100d105104803410b0104d42e840f130525a510483e132040d00e480d1103204032401e030794540000d525003031620020526501801c2e6419882014030400198 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 746812589 1250 746811339 746811347
    0xe04120e0f120f15060108072703060e06060a0f0504021b0a05031b06060d08030a0914070504060e1b03102705090601060818010612050d12180f03 64
    0x181c41c08005003100c01c00c08800c24003c1e961140144205980d20410404040d03034251081d104c0c0c000c40c03042c0c0d0b075105685e90308101a14020243c03403c0408010792034141c80c1060500d140c051014520540d070200d606000084d005281ca00090602e42c400c01c1d500404000b00400c422149040350f0080d1000b6031250030050301c1e140e15000301c10607a00b8a00802c40d00e4420800048011f020404510100e100f603a424800d105a4a56040b10110b400003100c0c40e0640205590001950344900703011404103041e60700d030741c0c3c010342a44410440c0d03036142d00011040c003030740c0b0789800707010060181c0e0900f5503040c2c50070800d03210440d2560319256403071000c0003000c1040c40c01c0003141980901024950903010320415101100e59038100326841d07003060720700404200c0341c101c08544a81214010354403042d8a07240c449450f80c0c409100720a4801965071840c1c0050440074422001c02194090400f4184000b8800005031415107242588030400f81307845d84144030007541d40d0340180025000f41e6400c00035900b17450255 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 746813839 1250 746812589 746812609
    0x70c030506390408120c06010b030f4210051201260a0803040308010b03040c03023601030b01060219110f060d090c0f2126030a05010e04120e 62
    0x102802172400c0c1c900f004400c4030040246211800c03c84030f440e070740d88240041c1404117035111303020641c01c1c00114421045042ca000d08032207505038079180c108603003066580f5140e90f281c1d1602840d0700000c201c0c807040c90400301180f0400c880341070092070328040075584070054174140501202000c202e11032140320b04002d040010440481003c07148200f2807030602e940141c004440071000203200000100d001c0e9440d100b920300407907202403607c021074190f5003041b441d1140b049000c400c01200c1510310200c8080f180c0c4c00c1241c0b004860b0308100715419810710301c0301c40700140c1110b8203543c02041d94060440107155044083c40d00560007907118110100018601090385404c59848580400c8880300142d40d82d0102c2ca130148504051514035a0b14a03188655002c00c2c8502d000c03110080360010000d40694240b203421912401c41c0c7e4a18200500500d458080410304c0034921340c1d0b0203c00c010042c0b4107841303400c1c09802c2c4c0300303440d42c0c451602d561443c0040d03442c0104c10f000c000042c0c0304017031103031101041c42e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 746815089 1250 746813839 746813849
    0x20105032703030c0c07090c02100914010c09090b030d08010e0a060b04180c11030a0806040204030605010b180d12110709050903070303051b090d05070308070c0305063904 75
    0x1032030381c03401c1c01900070b801604886980c0c5e40720f00940031b0004403903c0500c5240750260550700a803190f1090140550010040c0c45000d03101000e8003c09884032403007e100d08101c08805803030743c1c00c0190800091104841d0b20201da43c0c080d46c44580341c59034454201041a04560f298164400607650304a0031401074115544140c0240c2004200800c40341c003408617110740541076400c10052020004022030f03081d604030b60020f01c6900700f0448031f0342c9a4071454000c0e61000303000e400980703000d40c0c1e5035a4404454003603125101c0541c001c5003000c41d85100d00002d024581c02202d546541c02c419072503603410003103404401c4082c0141c002c401c54402d10140001ca005021707003a010021407814201544c0c036a4410281100002d1511000a448250010021281f60420344c03059052614810500600d102e4214081d2094419801c00000003103068008003e071500c543c0c00b40c00e02902c0c610b130103441e05101801010700e102650704d00c0d48a207140500c3c00c003500340b408103052141d03038140d00264003e4825a004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 746816339 1250 746815089 746815093
    0x51303031e090308043003030519110307050304111801060f050c10021b060103290402031c030908070605010e100305151506070c0807060201090201050327 68
    0x10915811103000c1007601a000160101d6076144075048801d010b20b4003009250b5001031005100c0c42d0030110703039244240389103000d4040b030350019074420641103c200e100310000394560042240c0840b596030100c103801c28268050148203a101400016800001c001c01c08114001c00082c090020f860345101140c81e001e4420030362214a0b405151800c1030900480c001305081c00d02550490344683c080360030400c8442d0180c801b642100354558060740c007000c408200d5402404040c1000007003441800d00841c8140107540388030380845215100c014103021310030780c141d0030a400c010150f2030100b2104008005400505040018180160010214003002034030802e0045401c408000c1c00d80c1c01203060701c002c0c10004002d640c402e032a02d0140001c60200500d59080086c008400c03940b050041e80c1c0141c0200c02c1e0000b541d00780c8021031200e8000c21001c2d45c0a691852080003170030b606210003800780110b84028000848d003030b000607015100182ca05000589400f2a02d0b0700150408002800d464802c41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 746817589 1250 746816339 746816377
    0x3030f040807210e0303070b010513091212140915041b0909060f1b08070207150e0a060201051b0306060904020a0206040b0601020730052e0902090606070305 69
    0xa15850542c21030f50b001da010a05449100041d85000000d8a0500d81d102071080b109a007444207101090b4012440803104607214400f240002e2031a59001c0d40c0442c45da5a58a41c2018008541c81600ea28020040c903002070081400b01c584004212141643ca52080a00d1143c80300e240140901c2410780c1c032940c861400070340104140b0305942003140c03a503004550a102414511504108485442d40303040c1a20301b401d42c082e1081400b80299a503c038050740147e0385207075503803000c1454600c103030114840041c502c0f40f410007040c9400a5050007404440c4000c00c02c51a0490800350f4000b940c40c2113201d12040440060340719554402224070042000c1c00c1503444840c50303c4082c1d924002a10f040715444d503a080054929440011004102c640400b80f10000046810003541d0494000002c0e4100740e140d4039103040402c0d000c00c01c50b1134134408400e6800080204107040b0405030048207840d020b0508044d0803c02580d0340180c000d41184045500755036422152034259a01e100e0590001c01540440c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 746818839 1250 746817589 746817623
    0xe0c04062702120105010f030e011407020d020705090c0d090804090204081902060901030e19080c0708010902150906070b091f0902010801380a0e011103030f040807 72
    0xa1940620003075910307480e4480214814040c090340950030682a501c908140104982e40c40ba81031407501d900c003030400042c2c1a40d1031807010309441401d0f528006c0c44032a14140403c035603040041e095121000d01c05461600d00f4000003c4034100f001e8079014800e0340c0840c241030f01451960110944030340c02039507540c1d100c1d907859880d0f020703402c5482415028014032504010110308059583c2505d5401071801e0f1078940c103c00150024009100c001035644104058841060125941c0d45400c6010b101440d8840b91070f0700c400792401c6a13035040030000340d040c000043d0060311880079120325144500b144a440c1e44254000c6040750007400005845040440c1c2442500180801c0c07411120700070300540408a0048641c00d016240b00d560024002101d9030010465070103141e4010043c580c1e0160310b148200030414180341c1a600300d41305001c4201000800c03042c0281c0003209107280daa400c3c2842880034003d50900ca8503408000c01c42415140da007000941044044011036200562000035000056051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 746820089 1250 746818839 746818859
    0x60f07050d050f101e09090c08250603090f02090403270503100c0e1e04020a080a0501140d14011b03020702130501052d0603010806041b0f090e0c0406 66
    0x7611600403903411380c9000b2460825210440714808005000502d0540c0b030064014014180310100b50381c1032071010804200300704240300d00d9540c1c0c425400c606861030800602120840e99139800001414038103010580094030b80244101c40c16011502200c0c070b581c860500703840614100800003c40103464520b010b08522030407509050f505d054080f1410b010896007010100c3762000c48450204000080035506841c0c043d0301c005001d8410600d0010f0300034000c020a080c4c3e0010700700c280100b0114401c0021650080c4100c07401410040ca5408440c104400440c944200031302c00078000301e0a4030381020010000350091000000300d0701000010007401c0303a001b0029008914100d200e02d804804040141000d070160301d05030780d402020700c0c100d4913040750120031140c00c0c54040207100d072107682c002c00c2c0c13a83c2d0b000246000b481544041c142928013403a01070a500a070795140a02e03107012000074084080c01c0000304c41075800c2054009040c2c64521001d900d80b4001041c00c80d8046e00302031001c12001e00d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 746821339 1250 746820089 746820091
    0x80d020706030c021609090203070308180405130b040f1b0306090605060405071d010e191a21060609090a1b02030708180a0b030c07140a0203060f07050d050f 69
    0x20030b68081055002d518412030b1a51400a0242c0c1d842039a218240589041503001d8004284000e00321064696030b5540e1000304d40110700010f04000980601d94550304103030240c0c0798020240c9070000362a483c00d90711076014540240001d08222204010301c0c00b00492101d40c03800002013038900c0085203039645041d00140240d0b00c0121101424600803401d14141030045074001e0784942c8a640c6800709041804448548608005042004514a114550300c03000041c0d010f040d0202c2c00c00e2034984c10520181001140120140e1110701c0402c03e040115050f1b80100700e03081141c05102c804d0741c0381c200000b0800c2c02a010190b5225001405100200344039034000e40c0e018880d0000c0d00107403174104405a0700e07409068406007030000f0800c80110040c840180030784040c440204011a4a919030240403042d4000f203c1c42a4416000600441401406280788080c40d0800c001800042c00076804039443e02009400d200300e0203040800b2030f0b40e8500900070784149541c43c0c03134100128076091443e0040f540c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 746822589 1250 746821339 746821349
    0x30f15020f090a140d03030c090b03010f0806010b21060a030605130b1006122007080306150301050612180115030c170d14120a051b0903120c07080d0207 67
    0x20721080000e0340c0c3e0b186030080ca0b90260091565000e1742441e1400d50141425030307014000c200c1046400309030929002c02850180c0080c11121020500b4086214542003040c1c2001600c0c04041c44222006001c85807000085a004645210103807500000704170003806580004241c1d40c20001005000710b00300c245c0c110f41d9030084801c1c02c2e02c0e485800c03008401c06828000d03940020b15000c10109544450707000030442c04880725444585241040486132545c0107148115541a4000180816840c040c85000075103000d54030741900d503500d010001400703481503035180c0a05400781d00020710410104030480c1d0502105034000d00c07113100881c6620030301c0b510502003240d03160b1001c00007180750304081400380c1481c10440002d1075140c800301070680d0803102d415010600c109040001c00400c00c0204062801141195004102400c160141400d078005039007005221039001c0c4445112a40c000540e1b010004441d8402c076640d80410004609200c050b4002e854180701d41007031500290b50000e15482151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 746823839 1250 746822589 746822599
    0x150c051210060c02041d0607021b0a050d0212100f0e0f010207030903021509131b02010b0604120f14070806150d030e06120c1b011104030f15020f09 65
    0x241e00c81d807450300c80e00e45502802e4005075030740f02c0c0d05005042540c440002000c08000202c598070394000801e150400c01c40f003400061308105103030922007020584d8070902c0e01c0100d034100391302d9090030003055043c074040c030001e807041070b140884103130464003800485080d0020000900800300307503844402c090064680048031510880980d00551203044c82aa00000c1d0315603181c17046e01e46141c0802c000b002010401c001c1c1c3d9502008104003554078203407603402140d2400f801055034040240c9101d40f90742c04085081c103590401003034004540c0e440d41111700350385c0f2211002580b50068182090600c0d15803400030150102c083c3c09990400c0b0004940086131311001c00c0340ca85580c4e0300040b2242207034015180341c0141c000010403002030b004400d032610003800903105130700b081d0012010003008901500c00d51074280002070001d40300b0340226028008039500b0702c02844810308129000941c0c0c843d500c8040c02e5610106540003c00c000d130a019041031080c1903081d512641c102d243e4500c60b91010007098414 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 746825089 1250 746823839 746823841
    0xf07032d150f0b0304060207081b06040c050306130b130818040b011d010302030601121506020d050f1c06171b09040302060a0f02041214120c0706030207150c0512 71
    0x81c8030202200c2d01a03a0b43c0c402654216110b40e5214806504102d00c2292190024416140000400c0340e80d886611100c000511190400303040811503140182c000d039009400c10400c02c20a1481851042042a40300e0030030000e44e91090401e51101d82107401c010712000c40080da16995841a072112444c11104031001c1040004410054600e1401026540b10a800c7d080c21072043c0d41c060360103181d002c00306040c4001e40c0d2a1803406942100c0c91108100800f0075041424050a80d040001401082c0c91b4141300d85401c08840c140c08071070046146041a0001000308060050001e420450003011800c0005405255542b0f60740e456072180c030503420b0f02d0344511401c60014030700829864060364164000e0215502e0700c040308005001c02003816800141c080200003202d5152007903401c03805003c0d480020547d03010201142c20040c0400c41d00310011824014007891200104000c0f04841c481d090041c0c3d0703131026140801c1c03c805100e02012400d8508074030480301c603811030010402805035420000c16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 746826339 1250 746825089 746825099
    0x50103062421020c010c0318021c0b07080f1005010c0b06040e0f0c090a0e1c11070627060921020303210f0f07032d15 52
    0x12210544504194042680260707005031486018071081240c551a1415030b0b80c40c29020401400101080000916400643c010510b2000c0c0b0640124030070324038050011181c100b61144041c180c0d05c2c000381c402c01100c50400c601403101140514626880204018946003c80740900040c0045410040e03034818140019903c041105040d016500140c5401c20340c0049611104c6168400900494210380d03104420150000e08001c840f442c24004401000000c0800707050004000025200d00c003458201a101c1d0342940d804225a9011080a000310181e40074100301116080c08070810032050303000781480804c00960141da41c01c0300c16003812007001d1003400780b4448105003082c7d11a0000003412000103100040c02e1818203100400300012804242d401c1e500024190b902c4107c680020158000a40380710240000190f07a2004407115141c02e540b601409017101414010710610801d41e403901c030f929426058400030050744484004c107504d0074501003910f000910000041c2d04400b0904000011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 746827589 1250 746826339 746826341
    0x71422150804030813030c0b061311130b040f05150f03160e0904200102070302130605040e0a050a030c08220504050a0b03030708070c0302090c03160504030302030901080601031d03070507050103 85
    0x12403603151f61002c80b601100d803150070302554043c20490740081888000300569405011700800702c118520b06039600c50b10388490000001c0950b0005d8480355081c0801c110340d40701e42202c0d608071042a6a400e06500580c4001c50491150030b070304a180c11004030901410b40304042c40365003004943d85440140c194403800b0031407041d104890003000b00440b24200e112050502407059140e00041c0110740400f40c583d0f0000c2e00e0708001c03907d040f059a039255020046450140545815044010064812000141c5400d1b446150104010b403c1c800826981000c000302d0300304558140c21b400101401c0240d6185109c4140c40c03040c420a44243e007814003040c201300c00b40c81042202c0d20000c00951a0070000d99600000c1c1d00007002c190355030141c600380000540c985e280207600c5800c001c06010b43d82d00d01440c2c040ba6090030540204100300c800d010900000790004102c60f844082401c1c049101c0e500c0340012070282650051102007801001c242100140b13001000c0c251080c803880a0300c10041e280c0300110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 746828839 1250 746827589 746827621
    0x1d070921020114090a090510050609100e130501060f020d050a1d281e121112010c020d030e1c08070306050306070e01080714221508040308 61
    0x199226203509a100542c00b981ca58620044941e1040b030800f107802e0006200d0500300e6000c4c0400d9034460041140c03500441000d4005000201e8081e070401e5103c4012812176405045132409100300915000010381d110031804181a80d441414405503031100801070a8101c4511044003600c0b070b16403104680d90080040e250b9291161740c490201240740c00310407001a4884009540000403440c0d05080c400e860000407001c40b804816001c101442c2404030ac101d00e501c00988100d80c0d07204d001c00d00c100060403041e4807102e40c11125407061150a4000158000c682810901180d8039084100380c00a401003441c0c9000012a201040006605103805417511920f00da8030700c4500b010b94400d03042c02d00580869070805070710b00e00055800d0f2610007180c5042019190100425006001d000c00784d80c1c03281c1d8440e800b858600d000f281e407151500301000c1030f00038483c007258101401031403000c2c80c1d0a4280c40304000d0031070003074901c18039403600c001602000e82980c0c1a03000500c081c1c002116149019000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 746830089 1250 746828839 746828879
    0x60f02160308190c140105070f031413050c13061d0402090f090f0a0507050a0b130501050c120d0e01050f0906040204051302091f05032d071d0709 64
    0xd1854950f9804071800c200c0814000441448050310a200c040303000200d14588210240000284c1410000c0e8041d014109200c0d5800400d82480d1084c841c5104010710560001080c01d29603038010880d10f4907905001e074020303a40e0307000950f10740d40d031441c2c1c540e6030031010031560540e015095451403008440d40014003250080d40108462001c2030b40000c0d001c000c981d01c0581d48090b500c1c070904041405040404808080e541948148004d2120f460300004401c004c2407000c00070f40c582106500040b070311100a101d082e06110003c1000503294809002004800324002a0303103540e4810440c40200410700c80444000c103610f0400090002ca100a104038041e5500b000107050540e140d81c03c00c0301a101c000c0c2141030820b41d2004c49070040e283c003040e050003041846400c030b030f410b040908240c0c2d1422150340000e11903440f5544069a402844440e034007140c07040884c0321178445854602500d0810198071251983da02c0d106519804102c0d024035030300804860391541216941d405540010032680e11350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 746831339 1250 746830089 746830103
    0x80316020d02011407060506100c03020d0806030304180203100b0a120b03010b1002010507230915090613060f0507080d0207050a0b0a090506060d0c1806050a060f021603 74
    0x1180054036001c80e00d00c110520500d0008880d04101d0703440c0519404c025800c03034509032a40c00b84082e80c43c1071018010304842a03e091040044142c500940d60603c005c1108180040e00c000b1401a4600784202c40180400c00160010715020800c1000254400c031101d1911180c04407003c20501c01507012194030700007a54505000305441d20460000b04190010a50b066507611400106038403012680701000007203400004d4a45414400a8903081c244100741c4c0c1d01026104440d000040002c040e00c54054064440700c0c40900020320448003071041451040c0d21220226605071060900d20502013560900d60300d818203042820410358003406024001011142c0074403980d14140c07030720781c00b400c03415015504845400d07110b503c070200e90440544044200c2c1d51102c1c8840e0502408101e842d8005501380c504031070804680e01d030344030103200030b015a07084a00f228441214000300c6402c5100906401040a0001962000041d007401c025101034000f50140c0d4510f642c0c0d9001040042003201c2d0442d01d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 746832589 1250 746831339 746831377
    0x203010303020d1b0b010f06031505011b06060305060408030115020c100c05011e051e150909210a08070e03120904060e090d140a05071b0b1804060803 66
    0x144c602444402c0c080540e0600d028104000c07520a0790501c1c001c00582c1c2d8074008050400c45c0082c141c6003041c800248503008501e007000f241c1d074000c0c1fa00042200d10900e40c11010034500c5d06070007400d581d030300c00b41052181200380402d01003948021030480c0c658040440181107585400c0c2d840e0061054031990215904840c10f0602d80102d11800e0260b00c0f82c800002c031540021105800f00300384c40f1413002c91582e254108070881448200c10041000c400401c05800e04e00210006c8d0481140b150041c003a14100300800c040d09030800400307030342410005000140c80d400d0401101d4582100790400009201d083c0441c2d4194054a040d610106014010305440c444426418220717600140c80c158100d40d40d0100040c00c20b030341c00307021406000e510f00070340082040007000419a1010b02c1d44094a200208807601c0300c15041001c5070702c0345610012303540d00410740d01902003054119602c1040c10010016070012210541510580c0241044408205a03601d41c1040c559a0085000404150200031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 746833839 1250 746832589 746832613
    0x815010512060f0f0a2d0b0103020702030705040b0402130801021c0501031101030504050f0a0f05060f0f131a0c0a03060824060d0602070807032309062118070504020301030302 77
    0x400079917400204e140740803406048010ba1003103040c0b051240203409010880040c58031720300030f01401c1500c0c4024601541080c41540000b03454484610825103e01d03a06e4108031041e46454040e035421020a120810310540e0315420300d8081c0d80b06002c0403502101e918805107020300c003031080d541030382d402038110481a804540150001c00010f070090b10130744605140084100001c006c8003900034800c0341c84c40c5010989142140c9000005420700203403512007020860540104000c090f440007214900f02d44524035403e006003802c03855800580c01c01b000d0410030440c0c25201004040020069a042280c1680c0c0c6016507161016505588050398560400d40207211000028a8000000400144c2c40100710b640e454103e80c0004400c95120801040171014190803042c2d00400071520745552212502d40d603584521ba01c40c03030761000d00c22440802d07410800034a590034000c1c01800c405050340c150400b074200d0f083c0140540c14816541c401c00501080742e04190003074a0489074150014004c0900340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 746835089 1250 746833839 746833861
    0x63b0105010b041205280b15090408130503060705030f3103170703090b090c0d14011d0304171c03050c1c1e0207030f050a05040815010512060f 63
    0x160700c00c0d00c9a214000031800800000b5032404141241903501d41b15100f031710b107813004a060000b0008000310221091703a080e240c48840800d0344c07140c4d100c0005a5908000b034035103605200c00c1e0700442e8042c1304101c10850720b26040001140141041148404286c0e15540044600b001200c07080740320b03c500f42038058160040d10340004c9a24440d04044d1030111504071000c8140310b045400f800065141e280e142c0901c8680c1c0540f941169115002d051407003400c9000c55025442038400030f06100c03800d01c9411103c802903000c0c805c90360b1b072420300400c00c610a4403c51741e070390070034003030385043d0786403003808490b08040012002006450b00f0103140b45c90f4114001a801880000c0505503104010050711032183c5010580700500706143c1c10004501c0c2124009130a07075444449a019002d20400811001c81d4022590442200c8607180c1165101250700d0b084a8502075a0300c0ba542920901540440548900360103a041ea202654240ca106e152000b0f15039489406030394010300342e807105021416003480 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 746836339 1250 746835089 746835119
    0xa060f0903021b0409140607110d051c0e030a0e01120b0906040207110607050709150620010f0606020f150402061b120703020114010902040f12063b0105010b04 70
    0xc000d03c009417040d00360b10b554400100303200300c020341d6822580030052100c2e0032141e044000900c0e400104800b1340039002c0500a445030703064418480f0440c50104600d81c0558100342248103154040e03c2d02c0d10281c030405001c480400344c20b0340c04034a003220031101001481c070030059031550080500c0000d48507001480001d40c406441621030a69035005000e40f0384510f00240001441000140300701c0d882c2013030320f004581044048041030300400e8401c01503650f2014030054819aa41c0c14640c50011025516004150749844180c90b2400c002c07000a2850700862044d20110414065405202c5484542080210102d80095206800313105002c52548a501040c2c04030032440c0850360038044000c0d64510f19006800c044006030344401c010302155024502c42070040011100c25410320b800d04442c3c2541804900a40e24460061a6208103001583d0400103884c040c05034020707810051145400e10002c4802000710a00010301011403502c0814441d0074101c0314811200c034282820200b42c0710203070344 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 746837589 1250 746836339 746836393
    0x6020a140d0c0611070c0e0a2f0309011506030906241505040b040b0c0c090415090503131d0c0a02030f0703050702090702030405040c03060302180907090e0a060f090302 74
    0x14052010000041c2030319070304006489004048845460110918002d0b51040c900c084004d41900070b110b03a015048581d44080c6500d644502901c2f82e4070402800c0c010b103400da4010140c6182c06d4000144070360113510050706580a04014455103120881016402c01c441c10450700c8201e42900c1000002241c00d2118400300003880c14600d07040d40d914a102c1c0136000794100c00e5080c100011013465602081000d0150b0700000da5040c00c40d0b28050320344241101c0e0b82c1d50351002c03460300c5a10a40801806000f20340a6104000e07010f40004d80703074810790b00a21000828a2010a6076038082014503100c00182d800042c9154011498207000c508d00842030341200000f181401810b00c20b5070016600c05811700c0c491403865001391f844615100800041d680c4e2003100d003040c5482c20f6414805a1290590700c0d0201003960303900119074880c40c205500c0c0080f50351018000c940340c8080c12101201c04201603a81c00d0207580c05006880703480d14040210b031000340700100964402c41c6402d003600401d921030081c1718 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 746838839 1250 746837589 746837621
    0x41103160b04091d03192709020f21010501020d05160809010e0d062c0304090e0f0604050105060312041503051b0c01021c02040302010507200a06020a140d0c06 70
    0x1c144c112441e1179508204160030b00c000c0a4000380d890107610115403000311b00b2089456504c82000e6180000348455405160441c84d00001c03043e41041142040742c4a4034440d000e2080c10740d00c45078140d0aa00028010540140120b0100c3d422207032007102662600c0341d01e440c0318040c0798041c0d5030301110b170392100c0b01c068103000cbd0f42031800659954124885120600410000c5942c0c01c02400d80c403d420380052540120140c4d050701244001c200006860540c0da040f035000907098a000d030840d2600020a00d81c60151140408000c10050b041d00180e002d5401075048950307500c119160030800b1301030743c058111111201245a03e00b94030030381009803c07070ba540b264040c2c0060860100c00b80c5a0218000c600c4076900025010860301490070000c0701d10b0380c1c081c421804d19040d82d0000b0258030030136001030b00c610601c1000000e00c410000c00031080c2880104800e420660b03c1501039100e2030700007002d941d0f010390305004005035040452101902065560303560306424055590300018040b00200038502d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 746840089 1250 746838839 746838881
    0x1e1c09030b04080a021608190606120c090c140327070f06080603010e03120406060503011a0405091605060a050d0213170a0b1b0909041103160b0409 65
    0x1042100e6001070050f40203111550342d8500a00300a40b6000c0302180d12814240070503402c10040c030340403032120b840a2030221500e03501c503402c1c180302010704569040702c0b9803401114500010030180c44085411134101c0c4005200070410743d4002d582d180c1d0700000c031909002040001400c0c0000480c200c01802070100122120000c403400700c1c0b841d080780743d0002074407102140000d2040a402c084440d41c0100700320028012030600341d0107036031280111034101c1d0001d070301c4501260403c8159007115002d00300140003004005841d000c56030b203100160300c1150140e80b600001c500c400a0100b2406801036070a209405403500d8142448007980c00585107108125003030100304e010043d00d000030300a1119104400f80c50a0901200c1003a2034401503810325207500410102d000620240b003060350211650200081411141650220620564100c154020180020070040040134800c0c40d010503001e40071216107030800d070891001441c3d00d0091f08006172060008111504041d0041e08002d2548003801d040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 746841339 1250 746840089 746840093
    0x40302120f1e07080f0a1b03120305160e090f1e10050906030d0206060f06040e0a091b050a03021903050d0c0b070e060313020301060b0403060204081e1c0903 69
    0x51505075440ba100301d680003044081654010042040940300c078801820060244207409560782030350100003000b0034130b401c0c0c64181044207041c1900c001d5400c81140404003c20b241c00034010324045560785055501e030382d0402c4030113115491607440c002c0040c040301415200c90a0160102c0750081c200015034102c08000504c0c06540c44203140104100d1803c1c8161078102001c010518038002c042a0103640003502e5803001c10340c00100f094000200380d0307a00340c40202e91008a4168030441e0045030b180381e0040b05105c50310190b580040103850003041c01c40358240c120140720800010314031480e41e000456070303003d0000d4902130702d02105120400c03040390380341d5680740d5840c0c2c2403104810308000400c40401d107031801c0c048129200c0cad60080313180ca00076800f0000d05000444c00e00029003c10003084040700c0c450701315102580130310301812080b08107503100c941e81d10f40320b4080e5006001b0b0301c070a8051445940c128035075100300001c40710700f442c006e40f40c000c030700c00750010f80c0032492500c201c10003055a02c0080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 746842589 1250 746841339 746841343
    0x309031e1e0c0d02030702180c1b030903060105031c030b0d0b07020d0318030c0308060109030818150c0a1403090406410112110c15011208040302120f 66
    0x1181109045101c0c1c0700e00c42152070a0401040d08086004c0d90010089480182d503015841040d14140798585002d90302d070209040050f00600f038061029100c4144ca90003403440020281000080172412112540e80b107005168440035a004000d1342c9103d900051484103000380c001484d0504003410050750541c0c01d032500040d10f00142c4500340942c01c081c0000c3c20080d85801610190465076103520800b580a540080a6045540c0c001d070400138030341c02040c0e05a104000000c0215000b0712103589a400d40c449034000b40340207050091103076150081864200702c607042a1a881105c01c0040c1814403000e41f5841d6081d031385141240c035503000400204840e960b55124400103410003045105041c4281c3d072250260040c02d141c2c2c140e00903840f047c1c4030300e2046d10b0401407034500707070a180940d0b215092150340b402400031025805226500410140080d07074001443c0713070a032054025902841d076030b1000d0500d0036081510015042c00020801440541080c000003080c1400c0d404c11640301450100041d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 746843839 1250 746842589 746842627
    0x121b010f020910090e06010e010201090f050f0c0306100e18070f090617072106110903160e040809130f0f050c040605090f03150705070b0c0309031e 65
    0x14400650204800704981002000301c0c0050651381448491581000b804032401040180b1290402c00c02c0c01c04088283d100703421483d041c40e801003004000880030720386130751504810406c0c0701081c0b01d51580040c1a25001404134044d400441281c2070a60400301d500c0c4862200400360a020401640c425503031020821850000700500301c41080d070103007005000c07001d8880ca07a0020490090681030440c510f01c0100e404e02c00c848600b1a101401304183e5030b5429100d002e01c40c05005986016820b154a910035001402030b2102241038031040f0104815565811409014141c040a030680000340080d40440041501c0704006040c141c0d10f031814040903003540c0e800101d881c40c0548801c0c80c2007006220f4050f0f10b0708544c04010b0181004d01b0800001d001d0701808103241d2081806104e403039213a403410b01490400343c0034040345080d035142c48040609280d202c031204403007080740c030000a410340c5898030a1340c0c01504804061071400c281100354034000b01c4848201d0441610401407060001c1ca02c2102c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 746845089 1250 746843839 746843861
    0x2151303050903150a0501090605061207091503020301090f0e12090a0e09011a04020c030a031107020402190e010903020609091b1908060307211104020315041b02121b01 74
    0x440142c07408034815000c2d0340041c0d1008d0981401c2c000c040c031140d9a40c109603110440e011071540307901d80d901c070b40c215504c6406612500c00d20580751400204030b5495002035041c0d54009009220111020000400316210100b01c0c400d1030b00500502044007010301c006040d00007008200403c1c650b111138100400e80420303140652140c4d0744d81d90031100480301c0450401d00c0d00044030114284544e201c4540e80301d104020010041580e17818070348465603041ca00360381140303070054811034071000c456007032100d041d8003401010003050030806481e605600c030b0600e0700281c0b6400307030070141464202828042c0c5030308084d00000d0070740d0410543c101649018405080210070b45070225200d0101040090560b070400303046203020f5003000c2d0040c05681c0c4031545910303101008c071499a046050034188503160040c03801c0703402d9200303000005002101c4820070340d0301074100e011282007068070388a1000100f8980e500c0b00701d03409a00640f030125a00d0742c03464007030201c0c0d80400f4440e0203404140304d1001d003190004002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 746846339 1250 746845089 746845123
    0xb0117270a0602030a050f0a060311010c031b05280c031419080a12020f04121704061e0507051b01180306020a090b030c0715021b0106140102151303050903 68
    0x400034200b0b82c40900f96000742c8c02c0c40040103a40c0c00c60b118070f585910140b0703903a410307c03841072012000c06201d11140040c80143c00c070000d104a12030304c0c220b0b03101c0700824000c81804020165404489000306807003c1c2507a480100c40c440f4500d03540d59a040c3d10103078030070200980201c10000080341c0a881124000c944142c0100d903450000e030300050002ca1a18003030b103420034810b20260200241c40d804882c1a541d139101c031551000003a2800495080d00301d2a1615615000300c0c0010b403150b04080801c1800030342504820241d4030102c8211854010b4620103441503100d01c4452042c202082c00100181c3c0c0107141000880804130f040101180003580116002580007503214070319035002d80510b015007000480103166040c5081405110302030804080c20700c24020310503014040b265412a0b00c42c01a02e0140403481c025000360500034610b602c0382230404a6502c08a40266102007803440c080f01c44011540c41c951074804010255060a0101310300780041080f810000759030801000d030b000045104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 746847589 1250 746846339 746846341
    0xf110d1202041d0118091112030f28030c020d0809010612080702090a0c05270406080f0114062404211a0708040602090a0b0408010b0117270a0602030a05 67
    0x800210741e01482038070171000c1c3d803401d010b41d000503079040c1e0780da0f43c0a0422900304d000302c180c1d400014114410483d4490b15080001000b40315030071000042550a902e0140071620364980c6d2100f80c0548076034003080303401600017811048190740100d20a07a00480c1e0640005503040c3c68a8000f8020230302810b040c0d60307200000c90b4200440c41c0078102583d000c0d500013002d008440707540d4000f07003d500664040b1460804055202c0b0001201000e001c902844010420701c121a0b5407a20719482d103c61081e098001d500f007072035a4984245540b56140984000340945440b150003141030324070241d200d03010704914141080001401d4402002184001a03800c8103e0400c580519104540d071404011040082c1c190200300143ca035001880c10764003641018001d603503121550300040d0354400da900103d02c020b03404103010601000560042d00c07001d4003a00c0e222041d0459820030201ca800850f00510205900f04800c2d8509006c0c2950300c80780301141c01160314182c0ea55881d8800e0f60002c50340310358000d40d180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 746848839 1250 746847589 746847599
    0x717150901080a05070506070501091209182a0306150314180a060b011806021014100605090d060207050d0e0414180a06020c0705010f110d1202041d01 66
    0x2038100340182a0140180152121607581c0c0e62101c038640f19140c810280411200e051000a41017050000e500040c00102c103084070b900034180490300d0058440345031040c0710310342e0038980612480300181c90b07440f80a0b0800038007e55001a04103020a98003c064840c040018805030403000d80c0414805520080380007000803e50103c00d02004150941c0d2680c840d0940080410208102001d650070450126800301d0b140c1c01070314042e8100050004031015150005415540070482c1d09a0040d01e035404c0c0120010b0b00074114026405a829600080c2c000008203c1c1070300602c0203201d001c002900b188240d0141c0e4481c20220307000404166000d4010504500760a07030300c03001140e0580d00c211802c01803c010091103c0f4032400042c84010601e001c00848031080000708a40a80c05501c000d00399a10400c20307400545510091040c24041100540e038813540e50700560400307029140180003000355035170503e4101d4466080100d180c5480e5800c11010501107090741108265030021240c0040a501d08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 746850089 1250 746848839 746848849
    0x13090b010b1b06101214060f070e0a050315221103010612210e04021809010f060c08030703090c080a0506070302031605030c0d0501120506060a03031205071715 70
    0xc800ca40702c29801c80700c2040b03c10203081640f00d0540c0c3d101c00701100c404c0c015142c0031980f8008420f103815a44a06800c203c1000840030302940314510f90364848074a002c400d070a000580707446001e40759042c0c00914040f682940030440c4983e021120001951792150300c40340545200c00d5040055600e120151031102c82e505003401607800a01144042100084480d02c1c0c0740032800c0c59a100e000741440d030302401788406210b80c04200000a004208540c0c2d2a41400000e0b1320052030181540201c940c0c0000096802c0c8804418040310466201e03418140f240340d03282401d07580001e00d59000d00d5514008100807540d191030b1840074120041c0242a44011800e082e032a00300000c00c075400b0140104200107103100160214030000e109401c00302c2e242d48600c50b1580c0309019410b03100036118a00b0000050f818a2600589100c1d40644144c481c0c5441d4239082c0700a0f0900c1d40006008038141c0314058015840c0c6a00c40b50340401245400744094a149105403494a01500c103206c3c008146004006507280c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 746851339 1250 746850089 746850127
    0x2609040b0a1e08160f050424171e120c070806010906210c051002190501090b160e15070204090323090a0e1803030903180303120613090b010b 62
    0xf510030f40752001c3d845c20f40c00c140c0720403290144502454880c4495810004081c40143ca10208042488030868895261040c24001401c5645251180060001500034110501e15503980b031100a03140540b1035885150080d03014031881d0800380b248140004400c0800e020f814041c0103c80000300362241b52410b0852402500f040c029043c41019060070002041c0703c984004440c01171303419050404014805a080000140c0d10b030020260185071181081410b40c4000c1c2441e1003104480c0c0c4079160410900c01084410b41144040761014403084914504000c00b21860801d1a005500e00000c0d03902250950b801400201e012401401d440040404442c1030500f50600b0360300e209042544110014624820910030aa51113080b500498030600c400c040c050703022801c0208407940c0307041240495580b948001e0034101c00c44280c9041500c9440e0100448044c2a044c1050288984075441000183e40028601c094855959082c0500090350580e5842c000c1c81c0c0e00302810740701c04040000e5805241 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 746852589 1250 746851339 746851363
    0x1330050304020a14030703060c031805010609050c1312021c050a031b0b1f0506070f0c060302030903180f041a10030c021e16122609040b0a1e08 63
    0x604240c4c14102c0d860005981c000c503604414045622102c0440641c0201035072074000380e641081d400100148801500114101d500414041203e940d03001c480080b140a903158401c1440084801007104107601c810381150742e40000d20544503541c00254a40811402c0a421220b80e00310384040b009040d00245901448540341820300e0b81c4807119614200308142c000c0c560402c56402201c0c2c1c1b480ba50000315108094079018000303541e641c0141c200700740500b0324072000315510300c6c4492021820700d01ca4002e4900032030303500d0000c50609000440c61102c682d0b12038500b58200d180554090342c141d8490081d040342000b0b044944c40e14000ca070040c4030748544c69541c52030071f050070120038114483d8001040e040c108a4840110182c0d034101c03d00c0d50401e030490300f200c80b810503010000b0440e24142540005094400c1079a03100340c40010f8145084032000d42200030300032800744002030b02414560046104150020301d40081192608014404c060042800046503034207081c09000c403c108000c200a155 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 746853839 1250 746852589 746852609
    0x91e060103020f0f0313080c070f0b090d02010c060f02030109020406120b060a0f05070506042001110d030911130902090a1803050f19031a091330050304020a 69
    0x143d069400d250b051103030500a100400c4000002451581a4040040441d900030030150b1384189000b0700d55540c51260103820343d014607000b00081c41900031001c490201601a042c0b0070013101980040d2014500b451007a0303040ca0311800742c030390403030041d10080d4081d10b40c0540050f215818450018130034404540b425004903d0849070001075a00c2205480e40c0d04030600d00300010350a6200116014064414010001d216600c107010812090b10004105064807110784a40c11030100c00440e040400d038602e4052941013522201d000754800c0d0002d4015901075400c007a04849060b020840182ca5000c1465a43d03036512101000c62a194480030b810090402d42400700c1d80c40429400d6120780074200c02000d102c0d00207850f50752990080243c8038245001825800044079550b40940a0500c08040c071080c140f00f000800c4540c54070304080e9000f641d44001110400d502035a602022500340251200b01070b15000351180c4980c3c40a1340b8509440700e0381d44064030b03030805d8418489800c1190700100104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 746855089 1250 746853839 746853847
    0x260c2206060c0b0f190f0902011e0f05090102071d0103170304050d030f0b0402070308071206030506010e0601090302120c01030b04060303120b12011814010b060d020f09091e06010302 80
    0x201e54071180690308014505208041d58448240e2100b85d2450021103107000fa0074440310703080b40d501c640e202c0c890f518002c1c4c0340d640402030121006080580200c5400c0c02040c107c64030628624420005010f40c02c0040c01241c084c5521804008280b03003404100f411043c00080040c420003442041c3d20b450003010342003050a50402d50344031901c60b008100b02d4410180c1e510031040b010440c0390488070050001070310466036180d01e418000c211a4003180d46202040c0d03600440c00b640c041910808040b250400040d0070300b079080005101c1548405001d2904124410303c0110142e0380d10f4080343e4503003004d000204a6207000a002405541600100900c514509401003021a1704031042e0b2036003610300c4000040d883c144a00007512070002c41800352256107000740c00c04101c0b0840d81c0b24064030f8001e0582411075480404d0441c01c0c0d90302400c480f0342204041c403040003090056000303030207a5841072000c0303420000800082140c1107000c0301c1501282e01403502c030700d200070003004400382c20010a1a0035807038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 746856339 1250 746855089 746855093
    0x90f06100e060a050405010909030305070203030c0702010e03030f0f0c0106060207050112050a090510020702091003120f021c080106031b270504090b0906070801260c2206060c 77
    0x1844414071a0404041c24480050615980d046102010b0b000c0108108440e50710745000f1b50040c12840c2003200440e1514001c151070600000035684241d2011001a03d0204c10354011030b810184404040d405110500008985034000c1c03001c0c0c202c1d0660808196201d42d409a801825290703540c0c01213040d900188400d01890341d01035034003001d10508550110f129110310000800504820384081c10720b01078003074800186c60854009140303444c000c40303a05c18180ca90244c403c1454030180b00050075190070300354020f4804d0180168038a491903d0060b121012078600751826084070400102c1c0c000365880c80180012601485902c06e2440d000c1e00781d55070340c2c205072005460104590010400001c194542260644001c04110003601c1c0203001072107111014580380c4005401034800c0f091742e019110020714003034881d4007038504071002c180404820445072410300500701041703103105449008942901e00207849000070008030858102d42c04c940f18100c00118001c0f80c0d60794108008000c90340144d100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 746857589 1250 746856339 746856361
    0xf0f02030d110d09050610140306070807110304030c151107181d0a03030b030a080304020f010302120702061603020c1e010b030a0f0506060111101508070905090f06 72
    0x101c0500c4100041c0d407944400c00c410140c05030480002c169410300540f28100700700450214012060190161440c03900d070a0803105001007a120030350954040000182d50301d2049006640103100c0342003070381100141030042c5055600035001500e400c403030340404020140007240580c0080c5013501e0030140d02c7c0040441aa2144080e2048410300c02044001d04001e0080358400303142d41800064603205c81c2c443d9074086440301070403041036000c41d10b0b0a580700c83e18100815030504c0580e0029a09280d07aa50341d007040f0302e8542c0c41040c9410145e003400310304409900d55000e207001e104181c00501c5649820388000050000807118501014010b0198542880e00040d034810b0058000798021420060308810300d0044c80700c04095603140c07181c08114000d1104220181d04d00601a40540d03285030b50383c4e00103640c2d10340c803001c5040c1c04c0d0f03000410fa0007159410f54040709448100405020344290703500501c601e08a1307a5041881519030710424005a0f0004100c3d40300009007000c05010f0038545051204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 746858839 1250 746857589 746857597
    0x11090d06021e16141e1608010b060d0c12020301090207200a030f050f15040606050103060b0301061d0307090c1107050108190b100c050606010c020603011a0405040203160f0f0203 78
    0x8001c19513040b0449120130b803d00200c43c0340040580148007500a0703410456486054444c0500c1c660140031000c18a80b0045c020242001400f500f42450b14903001c50000040022185880410001c0d0200307070560b200c140021030080ca072441740980c07221610300340b207040d1304500321004182d0415102d08214689a44403400100c80c2c00c407116600003203103030620501384095035038200301170302582c040d00d940c2c0100071014601071b50149408204407600c420054044812038010468168401e000420100b0f1090103100d038100002c550060101c0c8041010921707040c2c154000d0030cc40d81c3c940e040103006a41c03002980c2102c480340c000074800c41c1c0c900000a407180078081e00c54009110b600007007400040454021441c1c0075000381c2946100c40203e0402410440d0740202201c41c2d015000100e6029849901c91007130994005001c9413442c2d10300101280ea00c0b81032002c031550b006080c040001d0b103907586d1010318420401e050000710340007840c65005003403501c62468541440f5241300c680051070b900000b40d0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 746860089 1250 746858839 746858843
    0x3060c0c0c12010603050706140f0c0c09151c0f0602220311100f202406041107110d2d0b010602011e11090d06021e16 52
    0x99038440340d609209003001c0807820002c1c1c0004000e000c510102c2015844031080380d0003002680c0c0180c2c0c88910461f0f109190208602d07c403102808071800514042d00200700498120040354008854600070480039081290043c101031030380040307a140c90034000b10b0142c900a80300c1c07016150002954aa00d8100c121050180c440c5034041612200c82a2400340b43d840042e91901c0041e0083c1c0c0c030324041d045000c030300e442c1501448000081005040c050208040c02298589582c2000350340000a9004401d160020086078032480d0f40070308001c82c07401559200d40007000d900d00181c5c80c2030010b100c160380c084012000c0d022000c00c40440070401059401862007130440b140448540030b803c001d150540940e03000d40907451000e55081000b1640741c0151040c51186003140321aaa881c08145e08a070b00300c0100d0380048407110180d112441d05a80a000ea9000407441030b8140111314001c10a0310700850401c40303034282d0001c0c0c68840700c0c00700040c0002c1002c00341105d900c0c1100b002c2c1c1c020842200c50b400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 746861339 1250 746860089 746860111
    0x105060a020a0b040f140723030d0c0516082401050114030a1e02071a01080a0305072a091b0504030b070e04020c0d08090a0c1a0706020a0906020c0f0306 67
    0x12a0402900300b0005101a8000c80b1b04406400c20344c0c0d00907180d5003144140c2400f031401100d0846036000c1c00403842d1442c031008001e0a0350300c410340ca090702c006558100c202e440340070f206030120b292260f107407003107014006110040130940188034024140f0358441d11003141441c01280100070503a40141c01400c003100b0301400f0360300c90f240e07021410044d04602180c40700f902c007214030003901c603040e65001d403003014020040b00c01d00c458180303420075804800303004001b00c43d00007a10100c08a40a4402010140d10030013401e0680e001661a2582c42d658400417107103a0307a4403803001c01c0b0f82402c070702070300c0c840f6800701030a021010006900503203184203920008140e0b0340c000000034401c1340030702032450000c40080c0c4150340e180c088500c0e5648a20901c0c031090007007204580130810038a0001010341210f6440422405001e0404c0c1c0c001e001c0c0c44034031030703030144070b036001c11500000803600d002500d1900c466480380b510890034802c0203820680305100071030162100d203403210040d41d400520315801c1840541d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 746862589 1250 746861339 746861341
    0x1060e011a090d2105070b0f0105090622050c03040b011e140315040809120106030209070e03190302010519050601020d0e0406030f08040503190302060f18010c080f0105060a020a0b 79
    0x1404180e5000004d2410700f120341010f0048411942003801040c2a902c2518040c5e11a6524141c1c402d1a0b1000c1c082c0982080d10080007070820308045040b64130684000c0000c4c015894540140c00076698211495420000c0205c1840300b00000a84d58078050300702164101161b0000d181f041440324040d00c925010140300c111021610386050185400b0103c659441d816146040c0c200394441d80c1c00402d0841c098800f101d03003124102018841c0100380c0c2d500411700882c41c0c0f0350a408aa440960391081a49070141010743d89980900383c054041d901d12940012407280744c502210001c510148100710040c1e42000200410703681d0206440f04102c96505240c0040c600c40d01c04640280150340000382040c0b0110100000d01008801800849200300e044404034501400e01d206000b15440c401000b6a002901150091718030b0030b12035502c02c40f00000b21094184184a05081d2000c0f0200880800c2e961010311100030000d100c202c4c050401612403e00e01803001d40d000307640340c01401015008100c4c2c54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 746863839 1250 746862589 746862593
    0x806060d020117091c110601120215030f0601091d0604050702070f03031e0507230111030a0c08011e060324170714130e010e0f01060e011a090d 63
    0x3d0b842d00000d1460101c030b000c600e00002020f0752000d117503400c00303803e064560b000039607540b14014030446c1a0b4188090f010726483d09410f15400010350b041207a0051030201b403070b0800000d401c05944901152454211a800c0202c00541b210650350071131080c80c0c040550540040800150703882e00003606440029069455503001ca061012a4200410b8040c185038004181640a0254518070056600c00701110000c08c4003030b1800d2041e410b008003d00000400840242000c81000711003544c000700100c0c6242d402c400070040c0d54001ca45c4207080e241d5a1044a444030303402100c203409000d805900903d16040081452644c0e0040d124690400d521401c402c0600020158881d413080301d0b00c0346241045898040b4240c4840c80607800039075074410b68600080320b030800030390701c2520346000d0312090703409c038200042c040600044000c0407855904c80150406a1030308200c00315691a80b03c0002490780e04001d402046404103910400c40c1041e807501540c00809a1012115a644200c6800c942da2100b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 746865089 1250 746863839 746863847
    0x1208100503011109090a0612080f0d06030605012402120c01180c0317161403070c08010623091302180a02030f160207051504051302071109010806060d0201 68
    0x168104540650818110340280e110f81ea0281a80c0c110845217140942c1d0307090105000c840303881c440c3c280b401c002c40c0c902a02240707000c0c0003008a80403990f149481e0595a4585806030f50b4554402c460b21a036940041212200c0c40001c40c52404202940b030028143e2100000d40d62400a42c092000800000c0c01c00c000400c254842a00102c0040750001d00d550300d41050341500440e8401034444650035040001c40b8884041164895408d01c4401b034900d01c0140c54189204003005207040c0c0034031007000f0030350200da0084c05550041052000210781e0504001200c000010303601c07000e101c41e502c1201441c07410b0307a924848503801141161101c03850601800001c0c18080c100c08480000d0b07c0d440309001480006400070f40c0b0890000c000b00100e0785401c3d04510300c056942491100682142c2010f20032031402039070054200141552480c2826242c000284441001d400d101e484254006029410012144084035004000f1a110100c6624000c2c510341c41e0310f40101074174810262005107500b1a801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 746866339 1250 746865089 746865121
    0x5010e0d02150a0915050a050315130b0f01020705090c030606250221030715020f180f0406030b01060804020102010f090b06150a020c063a0e0601031208 67
    0x108440000c041100c901d80c880d500114043c1d0000d60205004038041d1303d401408a600e0005686031031070714050100840700c6800203420650a0645000704c80c0b560707507403041c4000c8202d4101000180704c1039010308000b611000800602c0c10f542009008000c07664035840380031703400201048803a43c0d0f5682c0800041091040303c00303420401c079440d02c0100e5019012824180384070310a4424040001450340050200c001d5040c001480c3c4d4800c00030940015004d03600d2044180340c009002d414840001082140c0790450910550620407820031400c075440c054038410700002056a00708003482c1103485128101105000c2e0106201140012900b10391003580304084804005908001e4204540390420822a0070390b01180314030420455001000d4558046a003032041e25001071640549480a1040d075410a21398012086500c0350a185d07100c4909040714000f9501c1303040d4608200044c43e4030401c4812074910012507900050042c00003906031046410328050300c0c1070621050b038602c8084011030103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 746867589 1250 746866339 746866343
    0x2060702152703040e0c03100501170c0c1e0d0306050a050a0b070512211e01120507121406090a050703200d0602040617041a0c1201180f090b0105010e0d 67
    0x417a050400002d1001c02c8041c40c0100c1c23a42c0b00744030103d6514801124a01003140e80c0e1800c440101307000c01d107140822401003038581040803c0d1003c2c003084400e512451300c1a90182d68550b00038480e039500301c5900d41700700c0014201c1252170509150030000420000c00881c0103c05e20b82d0785c000303400350030b000080002d00c00070000d450b031a5071740385c0740c01c00b9440303144c692800c141c0102d15292010031291712880b0902c40180d290710740d2621580e0728000300c1201100c640c410540c3d42d03026a90f00030644c0701c0410305903900180220040f15102218804051608400502918564000740701e03a100181d000b207001022030743c101030701740329503102002000131a98801c004140e1200300b41b0120003c0040c1500074104888268584400307c1c94400c490b140120070459009095041920802404c036908174040c6802c0354400c00520b0806a8620075108808800e8018041c09101000581c8228005e0300503254441da030340ca41804680e103a6910046000d0060181505200e03902c0700d91505622012041d0940d15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 746868839 1250 746867589 746867609
    0x1f090b04181109091c030c08130f150612050604111c0809061c0c0221040e3d05010f080a0504051204031104060e06090703020901021005070206070215270304 69
    0x1d20f400090010260011007c01213041400015402c0200c024034121543d008001021100750640c0c441003251410a40c08241d1503035030300040303103880e0801c007100ca9aa102e00b0040c042d1381040d040c054040078501d120a445048c540c4003844141c80c0c00e011030a200c0d0b40c070241c580c3d1104403000019502d4065849d056800d000c42101039011700905400400030303050580c0a0320b078580c0c00d084c001d403800786d108410080510740408c030400400c03e081c01a1580f1440d80030721a04920380400c1c001210001511085001c9039102e44a140c3d07009062107004024142420940e250301c8185101400b500ca00400e01030f2070a0740c460005090040a00602c40d0035810855003540d1075859161840700c1031454244030740500d190001c0403446003130000c9541d0140790000d1000302c0e1560358803411000780d44650303101ea04500860381000c0d5035900fa800f51a004558035009000d86260080e4000c0c6005620f40d0120880324409050050300302140400d00010f840f0f44e1051140c02c1103202c550b5107144540c0d808100c0c22 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 746870089 1250 746868839 746868883
    0x1819060f0e18041a15240f0403050304080c0301090c06030e100507121116021302220e151f0908150103050d180501081f090b0418110909 60
    0x20000104240c81c050813035000c20001c0c3c50b008030000707601000300e00702d0340c0180c03440380b0070862000350403650740b840d5203841441407618a45044030009600305a0040341c0582c40442c1c10b01003142d050020803100f00041d4020040f5520b140c440402100d0701e4450301051654625000e004104140152042d4030380b01c141c14072590900074001004c0142a1920a10503403400355090001d5154000302d4178642104a4900410b0001c0d4082040d01084841450381c859800c1201003440d87c45034024910584d00341008864240c5080641808540000c20001d0402041708003002d0503998141000700c0a2020b09178114040c24400007075814929507045051036124001003991041600a84103059074850410340f8510404044141c4e0005070420721800e05004c2880f0502c0294400d102181d48160a170942c10000d0310150403ca08000c81c40d00300060f0315032556042c9001c3d0400e80a8058030707900c03406005003d1220758942145c10301000204921508480000c038510050402c200c24501b250300e4606005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 746871339 1250 746870089 746870093
    0x20d0c0807140405130b01020a150603120516140a05010207050a11060a021b1c060c110c030c04093315150e0301020f1819060f0e1804 59
    0x20200c0845050000900e8100150000000785095404a8030060103580c0810004040c400142c00e5081480d41144150001100406c0034090711501100101074000b99150443c14001e080138000d541c0392007401030802107105001c4d940602102141d40140300700d40400148a0410300b00394034818003070f06960011400500340600031501d4051288113094440031039802400307011440c01840901409600075842a039034900c0041104086c0c224010094500950042070044601008180a540007940e07814200041070304019031100c149a508001c210240440c000656035042d048800340c000d90300d8828070003c11140521402d00464918166030f0000201041b40030300da0720f58211040104d0038030340c86800300c0801200400c103440e40c2c002d58038414a411102901d034091440032080e0150b40c200401d82c401803c2d04058a00e441607a6000240d14a946e01081038a040c0011090a038015000341044610380003000081240f03010700b03060a03007508006c0010b01c42d01c172018840d801c0c0c030781503010042 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 746872589 1250 746871339 746871347
    0x80c210a141c05010e01091e0b1305040b06120f2d010203040f03030b010e09220b1003060e0c03151e130b1b030711010e01020403120f05070f06090204020d0c 69
    0x4180d4801c100409661b83e03a54811100756242141380c0ca824800404503d00001142d8024100c03040300682514003464403812032104880701240c0030346000200200380406458403e0310f4042288001008000c207411509005440341102c03003005040d0a510203101340305c24100c40e05010340c0c2028200031912480d05050009600301d134004c003140003d1414040509940c010349072028240750142446c0201d944801295a59051110900005008845074000011a51b0507100d208080203105d2104c060b1462810406503a002d40c9413040542040100d4540c3d5180094803075140c408400d01c5030340076255084550025441030f81848900c4521904124044040f91081d15006201d015506881e5a41241c12203501403003603c9a0040c0c081040401e256600ca1b80d403160341030b29881d000050071010114490f089901540c4201c401c41321100700c00520582103028542120781c503040145c5042c60999814682042030301c00202640e0303960817144c0070364560742c0c1078980c15807070464204200d1141c1c0300064 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 746873839 1250 746872589 746872591
    0x90209210f0d0503010312050904020712030e070b071101030519060902131e0e1806090a0201030c1107053a02100201090b0c0a0c0c03080c210a141c05 66
    0xa100b4401c070700a5055007440b56080702d04807604000624203091030706c6000c41c0d460384402e1060b41c0c40340e000d1025202140f03a0301d0001c5a503c42a0b1030014443d442d5186080c141800d9601215103241c0600011010541c0400c2c1c410081000b407800040c140c0e80c0c18044855203a221102e500300a03c3d2006c080b9240500d47e0003820001a00b40c2443d80490b80d881440340c0d80154040200c0026039158410002c00100f00d6905402c0b070410300c80186610b90f41c2e502985007000454000724240e214000740c4081d0b50305413140505401c11480e00007814103001c0169a80d4000c2d41c0302d22409821683d01400300c0c80f00c101300c0c1c241c03443e0020013800d4030b4440340000302462036004142a84150620703035111100500520803040e109511203d030740c4050381c2e40e00303802c05c4070781005010750b00b03222103952004000f580e86c4c03400c0c00144d44150301c0d8035100c4201070146403078418072180b284c0d2040c101c455400300d40c442501c15601d03105464900f01c049509a08541c1c841d41c0241c030740500c40200380b80400744050314603410039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 746875089 1250 746873839 746873863
    0xc090204060e0406030201121509020c030d0f0606080412120c020c1003180206030a0216080a0906020d050d0e0c1f020c0402070305160609120503060f09060a09020921 73
    0x5220340c4402e030400c0100320780d13861000901007640106152a0074100303800c51603010700c08841c210001d60b500c5c104403003a0782c015415600d450700002400203500115105000c103620b81e07250208641424a040600030341c00291014280031090a070400f0040d1065000111200410405100c26010444040c3d40c0f0210b652100780302d00382c4034188120040c483c0c414000958404522407a40113656004d20003103034400340000354225002c000350404803400c140b00d003059a200d07001583d5074001106d4020002411908094115008000002d60140e070000079a40150107420300080c240100c0d000c86498641041110b5070404040003501c0c1488022043c0c0c0c030140e00d020f4090318407400c0c0b104100b004030f10a98000402040b8240911818151100008042581b05240c0090850910341310055020801c5580d1400140000104002030600d61505241c40600741c80295841c100000011160316260103003030515a808184a5070640c0c50340203490344042c000000c103c02c49000c0d5460fa4540f4401069 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 746876339 1250 746875089 746875097
    0x12020f1513061e020607080109020702030f07030503130e040203030a26011415160f0203241506030603061911190311040f0e04080409020c0706090b09012007030c09020406 75
    0x3d100241c84c0042041881a44165030f0f45100780e090604c084000e40010320140e80511501c500c0000c0d5030000c201400c06140140000c50300c41e01100c21450314400103804c5030010070f140c0c105010060f2000800d4a0403902d10b4204031080c1ea1a0326482c07081000417100d48110803695000010b9808030350103194900440a4520005941400903a910316124841c1d080c03a0004400e4205c501149110015802c0c2070710040a40700342e14041da102014054120381e00c1d04d001e80e00041446030100c45801c1060320201d0503a1440c0c1149000000640c132120000c000c141c00b19140e402540c0401c0495004040315054100382c01d032243c2e083c0305000012014244c003800443d14004041c02484a000d023034404a440031120140528140304d82c81c1405071014104440c856400e020200300d0842ea40054412209114001c100d1645445002000c2c5c4480358800314030750710200007944142c0d031700c07130003d801c1c2650805050504c141c1e100c5c6880c0c50440c80c5d0707001501050707070700601188400c810780040088415940e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 746877589 1250 746876339 746876387
    0x307031a0409050a02090601020f15070f090501020c041a0d0b0609100b160602040b190206012306031e07021c0f09210204060603090c12020f151306 65
    0x10074401120541c00001c1c0081d48869001401450b041c01c00c1c41e4000c0303042c03040d9030303488005040a03890284e80030030504c0541000d90400080311303480082610203d10500c0c18451040c5490000303912881440802c1d400703075031181240401080000c03814107052001400b49070307440401c2e0a28004c010700651f0311501c0348808002182c0041d00c02103620080d0b4210004c5d542c42c1c001200000803101c000c0210840e4880c4d02400009260321240e0302031318030b000c0a00c610080d034004e482307002414010160413072100d030341150a1400100c3c28070080030030892030540d6561754940302c182d5240d030308000f040c1800026400043c104502e80d5404a200c0c0684560b18011622100708104191603900340003150000160a8007810010310b1808004c18003403d0349030000d0510819140c0219003606c1c06900b000020a403200818000c0150602c5500000e10034034015103100700003640098409500d003449540700751041d140d0302d060f20340b03c2811030b0328603803044540c542c20b0340d0744100180051645039061b001080c40c0d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 746878839 1250 746877589 746877641
    0x3210519171e100b0f0715050c040e07030e070618050613080f010b0328050a051c0201150501080601051c0f050108010b1f021f052a0a050306060f030703 67
    0x4241042513a4800719451304000310000c0390305040c1c201c8502991403504a00c01c03102c943e00700c3d104140c0a8448030ba1160f41c4d0f5030a001c0d040c000004050181001c15142942030f8042200c0814494140d5000d407503e240718400c80214540c07040325035001281d0105001803041c0700c030482540060101c078542d1050300c45401030081114201d800700031070a80c154100701a610900c2c0680040100039040b18081c88001a105d03446640c6046440c8100719502d07030080e0388100d090b104600c01424042c80c6d900c0288801040f078a002c3c0551985440703071505002117100403401e40e078010401c1d580000d0050f0850810744890b07010460240c034803c2e0b12082c0d45403030800082030086060184612900b000b4248186400300200480b5040310300b09000002c500071159070b01c0723105202c8003410001c0c2c0741c541400f0640b4140a4400c60325040400d00d014010304099503080c059400c1d4109969110b9402c0c14a2504c907a41e510206980b031181980b82e03041d02d000002000315042e010740c4030083c90034130060340414080b204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 746880089 1250 746878839 746878861
    0x10b0d03080a020d060b19091e0302040e01110f04050f011403040f0302010e0d09080d020c090411031c0f02010b0105210415060f03210519171e 63
    0x1400080c00140c0c41000156a01d02640c0082518581c41c80c800680c103683d403d146078040e040300d03540c200d07000038000903d40a150305c442841c014007024044603404451106010840380f0b040d100c02806243c40d82d1404130b90030b1007984000341c10201100303819520300792140000b41e15809805181d01c40d081c0d113210044154030402240310300c82d428122003031a60b00d4503140c0d90220340e08404d04504540d201c2254060200d0144204848282c03180c071a03980c00c60811040c00d04005c0264220401c544c08046098110b42c1d07640402ca03001178000511034546207129010908100300b40317003280240004842c0c03010f103040d0301210300b00204820343c2c0204188441c035070045540348200c1210b18441c00703c68100800c0c03101c139a60116001813080da03c509518400421900c00d4601d142d0003000c64040d03043c420410b0001807051008120344000309202a07203203030311b0064082d010302c1c1001c03c400f50140094418281c094844111040d40040d030003030b901d2500c20b032041006503408164983c28813a40340820000101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 746881339 1250 746880089 746880109
    0x1a0f0703050f161101110a090f081c05030417040605030103030e030c2214010803090a0b19080c07140f070b0c030d0b0a1d04020f120a0206090a03140a05010b 69
    0x960301c448401e8609043c04031810007442a000546550392266145140c104500a01600c038031912580c1015190407140c501c4c466860f44040b000380c01070380090b4200342a02c240c14a9022060410301c0e01c94a031070511410290b003805099020090010b13002c80e0032034001c0040c50403603110743c0c2e40840c4580c0400505480d07100d110701e6550090000c11003155500d001240c1e00300d00d008000c80003d0109076081540c140345c072082e4080e6625400014000c400d9040421043d00034009000d20b0901c3c6c180b0105480c03050b8450301000104010420000c111024041005c0b0f8011070340000c200081c403400c0728003107070b00c0341c8004070b09140604c200b8400242c0c003200d01d42030311051601e0350040c5040c030011a00b8140944840340300c135503100301a80008514810101d881d80c03141001c681c0c40f402c4c00d18151041c400c1c52941d2802c4648100e9180d03820039400003001810b92817245d03040d221503485905440105400700303019000244500e0400507009603041f80000c5032031400c0e004200034014a40303000140a0b407004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 746882589 1250 746881339 746881351
    0x1006080a02090c031503120406090f060e0906040e011b0e030703030815060c070e0702010605090606160501110a0c020a090e0d050306030705040203090d031a01050a08041a0f0703050f 80
    0x4810b10010700c2c00c020650240d5800101105100300319601040001d003060424242c150520f4400b107014481c503540901d200e0090000d201c1c12518550030038101400c41c0000c880c80038866482a40003800703e8407103030002c0703500c4a801c000901c08a0321038101c000650380e40c51112800900040245012403500044541c2226015142c443d501e85030302c13102ca50385992440c5c1c0c040d00042c0412401c2c0f403114040041c6c20040018840a00030b030b080201009003510026803069105800789000e0010ba41e54040c2181c0c2c142d6410b10b2107000c01e6a0760300d081409011100781c032800410000c00e031002c07500d8204c26001c01c014800c4a03106111500d540d02501200c401811618481c3cac4402c0000136154000c0005581040340101110b0326907551314001016070b84101c3d01801143c00c50703424071614507054010300344034480c41c6000e0405845030000080581c000d40010108000c0d03202c0c041014080324003481030310041c0302c14a5401502d841d8600d1a164034081e210790000034030b000d0000f401001704512a41c0540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 746883839 1250 746882589 746882599
    0x30106050702010305251d01030213170703081602010206011505030f090703020607080910090302011d04060b030c0301050907030e0a03051c05010e180f19140304081006080a02 77
    0x30465030011802003000900715520842c1d0700d100d8002c000040c0d81b244011407142c1e5a1138800219400c1d045004062030b10f025070500d4010700c0b0001150b8180c0c41650140e83d240740d50b080c00000501616460502030790310192020000144800076030326000349614070107000381c00b1255a40d99900803450041104101c076400281c0c1400400c5082141c2c0614179007040301c0703008980b60300b91030343c002451990161104455001c400201c1030b440342044000f102c080e0a16082441000b0300c1c1d0740010b004196110500b814907101d620101e2001d645960144014001c50800180c4a2070070b4402c0e101e4940c02801550302c02c459081c00a500307548030b40101d00307207821441d026210070700407540d042da0b9a070802c03c0c18002040d0520f00100b80c940a5108042c005c16100742078a025040c4280000b0540b00c603811165083d40000c103051181000014030032070b43d01031404088094080328205800c44c0300548030a00c40764040010000345182c4001002124000048410451155aa10b05540c0c1d01c400141c001d4000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 746885089 1250 746883839 746883847
    0x2010e030f030114061c050609010e0601020a06050702030d1d0c0a08120d0e010e0616090303090b03181009021503070f0e0a090944070c0302130203040203100203010605 74
    0x72152070410303d0740611002e81100d0601b1141420585102c141107545a03990780d403a41003105d2882c000841900400031407010f13004600709500001d4807084000005410f498440c80030902e5244208200d881002e122101003100ca50300b02c1902c400c0455a014054851189a0440a040c902803441030120789980c80101040d000c03684034002e4035003061a604045907070320019220311403030a0146c514140c11740c001402c06480c200e06404581820700b0010300c10060000c20600000c4d400600480941c3c12140c3e002e620ba070f650031083e41c59031b0315201a820031070082c000401c000652a800c844074162088a40700c800249d2034010220342d0008981e2100007503250500040064065030960201210150100c106280c0382d80e50141544c00883c3e04944ac0f950b81102c040001e4000e540d2942e00304858402e500c03000146c07402d030305400e182e500d16182d12070900240200800c19070b410f408000b03603406803405500481400c0c1100003504111001c0c0c0c041c2c001c0c0003888003111400c2c402c40f4142c42c02ca03144c035810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 746886339 1250 746885089 746885099
    0x906050409051306020c03190e010203122a13050315061c0506101d040302070512010e060109021801080c16050a05250e040209340e0102010e030f0301 66
    0xe040080c2c01025001008524000469213034002001c80e000d24000035642c03200540e143c41d00491040b8900350401144031620f480310fa80c04012100c50043d4000c044074903484080d6241d0001841100c0d010a6075148081d00311100202005031642c0d410310386a062090b070750b0300c051548030a006062500a030340c0f0500050b2003440c040c4204140c0d04c5404104500901d02652034601d417034815109040f880d414004100300d9a404c2401c02c0250450840e514003c0341402c1e0381c0039649002500034640b04d40b03040005241201400d5000c07010303080000040328001e50b074030501c0c0002503002003007890183c0000840c644441d40905140303030150300d0901c2401e1420071806040180300e0341c030420498050041c10010404030324100442c071038520303201c602140f49408004502051031441c0c1c1c880d042c0700703400500f00300c0582d49034908140c3c0203800800c0600d10207038603009085c026030220a9468075464500455490a60040c9445051802a0001c20511a003100d030f0329544d000710500215800310402c01800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 746887589 1250 746886339 746886341
    0x1e020c03011a3f0f010921030b03031b030d06091a040e10150306020f0a1b031b02130509071802040f0b09040e100209090a141303091508040606060906050409 69
    0x20302c140400c420b41e01342c3c40003480c0c2035003510b58254007651014174905a45110503075110a05000740c1c642d0804000002c0818040798990060490346410700d070040c04030320700c03034001401242c40c0c00c001d100041205030b480316100c07401481d404411000032410034032280c00e01d0416114001c100d40703040000303040d200000302249014000e00f990094a0751645600000007a0785400500400207100b603035035842d0786c07400700300a05407505503441e440d0b5009114070040129800c8110914a0a07503c6007481c1088072074000b0440784c14565030900c56992400f070400c40e03500390110350041940c5030680c011441c0240313988140103038095030050b1030340302505440030001e1004c500300178074040b2400b03040490003a00c00305800303082c096401038000100c4d0b00040d200b1000c1c9450300750180d00441c0040100a0340c400700304010802d00c0d000b0000c0804040d154151400d040c0a020b910004204201208002045560000345402c0b405d0328201c5d001410140b01046107401601c040d41920440d40d1100d0405150a080304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 746888839 1250 746887589 746887699
    0x14010e18040809212401030b070302130602060f07050309070b0d060b1c0b010201020712030203090f010615030e060402012f07060f1e1e020c03011a 65
    0x3200c55004003c0b00005031220521a844048000c03c0d82001e000c1254000d410004070500e01c1001c0ca840348440d0320300143d1850014103413504080810650f81d14020305400030f10030011403501e0081070403c0010541d6000484a200d9050b901c2240469140c070241034600f400b05a9003ea1541c001c540d0034440d03001241c001c1d0207004046040811410340c4c03100d4540c6258451010300500c0d584504601070b0b40100e502440c001d11a0a00c021071074410603031248284988080300713804c00c05030000301040c01580204800b922450300c00008101280d6540020116061220030300400302e418680e007902c07001d002040e110704ca0b0341c042c0c503501e580034015405618a0102c44c40b1081220302c848100c84851131007008030501900098889000301e20907000c01074aa203910f03525124905075460b02a011141d804095199129403820164030031003400e4100b0381c00c0025124100f50198a04400740c0501189200c4a01e442d5400351017000201034400314032001c001441060544940b03450084c0e9048200c150014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 746890089 1250 746888839 746888843
    0x60f0a02160306052512050c07170307110102040509010b16061509060803160611071b03020414010e0c13170601080c2b030c0206031014010e1804 64
    0x1491032031441d056001d00018450304103491144c0d8500030090840e20011441e481600c201e000c40d181c06003201e030000c02418098288616040d114404034070b060601c0d038207850266501400300d688861380300c050028203800480708000018034800307040c00c0381c0c80180708a0703058400c007808007039081c5e00b001400d90103a40400701454000440c05681404102d41d032285070341512002200b610b1079464841c507901960b1342500041d405400c104140c51160a04d4010494070b164040320104400340d441c00d1040017070090765000b4101003880c41e92681d0700e030300c083c50034802d591085130200020401700c0d1010400210900554203031000381000f1907058110320015190709802c54010f60719003030b1500c41041200c03040041400c0c041c6c0c4800018809540c041c00035035698801901d4015001c1c2d0100c03400390600008202091000321180b0f07101084c1442078001d06507494020301620b980c0d0404000480380364181e1700c0750007600310344c0324540f00056100740382800c40908002c2c000c1d00c0d00b2070b003482d254800c02006081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 746891339 1250 746890089 746890093
    0x20a1b03050903102003130201084803090316050307080703020c04050a1107060e010f091209080c090103080306012703061109180705040504060e07020d0c02060f0a02 73
    0x202c120250382c10080c0c03010401d802180424000ca0f14100c0d1025a41c5024061700807440901c1000541070b48440b0304100d090702442c250410f178503100e880c158800c450b0b07240200401140145403040d00d0b1100c010060782ea624240f9215281150150880140021b035200034140d041004160030006050500b00d145074050320540e442c0400c2a603a407515540903040c01c80158004140c0100c8a00e800d201d680d0340700d83d001c001848018601e003215051842908801001d0b65680d03a40c40d07000300d03400d5020300045403031700d0420051030203d03080c00e0010f030b00d5507100c113000158802008201c0123004225500748c000082c0c2540201d900315a100b4074581c100403c03050401170005504020600e02c06806014190120001100030b070950900d001566003103102441d040b0341c208020f52681e214540c0d441a0355a2007105140c480d10358507c1211144555440203612604004020401d0028002018040c07801130f000c4038160052620169100204001d0195003c003092001044035000702e00106958801c41c81 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 746892589 1250 746891339 746891347
    0x3080909101d06090f04210201060503160e09010e0a1101030e101b050306030a08031312030501170d0e010f032a140705060601261501020709020a1b0305 67
    0x4018846240d000a0001440c80b074903040c0301540c1032420f5816044104842c00204a18280e1586810700e50020885004000d41280b00b504040c03003984480d016000c010b013925842c0e43c0320508407048504038003034000542034440104807414014814424003003000005031294040640781d955643c01b00c841c3d41814140c8440c1c1c1444001010301007020001c807440320000d034503400c01c0396040800405003886000d100c420000d00c01c42daa00018854035883d07000d1842c55403a40c0b00014003650343d00c40c0300c000745103c1402092600c5d00b901a04007034103941545401c0c3e4200001d1000701650784014505040100b000c603000814954811034018040200d00e00f80420340c1c1c90307010140100d00802840c4503000601c1c035080041b425074041c00f45846050900c0c2e000d03040040300d4803020f865038001740440d4140400300c00030110710228040700007500024405082c0300d03460042c240c04810040c0300c1e042401402412400300c0c0d208454420344411440780d03991142294060240b030800b40018800035414450148 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 746893839 1250 746892589 746892599
    0x50c0a14131b021f0621170705010e0c040603020f040f150803040f05060301180e010b0607080a09050306091e010f15030b100b0315040b040219090f0308090910 70
    0x74104240b00a03a5600801c601e030840031240000e200700600b45050035080c90700800c52202411454581d83ea00d2050401092501d4640703d40c506041d48100261440c0104084003800810350001d00c8005412080e5100040c08000b004212010ba000c000c0d4003190b4201003d0303583c1055804260390343c580c0600014030212203146900c2c500d100d903000e40d0b410382c00082c091080508507900c02d0020070701a1000381c159410148201c80c03800e00305110402d1150f90f0016802c00d00b40c25000944541d10103012195511801d080c80034440e84414250700110b001e800d800119400d0004110f032007220034902600c02d02180c424034607400c0504240180c080d640710344040c11301d01214400c032207100c0c0051003040070141c80c0d403a068428210040900d800d6100d5031004000c41002082241c1d84408040400f110030007a900019000f00203501d000c5422501c049840000340c101540140d2460019840c0d40484c1c60381d802483c40c1d82499030200400c141c00501c4000741c50305103030502d182c010142491540c0015121 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 746895089 1250 746893839 746893871
    0xd0c080a0c05121b160303140706060603060306150315230106050415030207120c0f0c08010e010e010905070510120e0c0120060610110a050109050c0a1413 68
    0xf4032000c448080083d420030108000034514030035007010070103400a0b8003400c802c0500300700c0a00c009014008030201414500700744070100e541c016070020301000307440c1d21944c0c0240202260b01048404624000c2d92031003809480760154100d9038041030303413008001c031200c2c0381001d0000032102c460b0a400400e0703800203024181400b6400380031550f441e203441d207181030b400c025070040081c404014144100f0107034010400101d8049006034981c20f020400d00c1c150300c0c19000e080518000601000e0341e813032001c20000410742240c0d4820080b00028005262441c08030b9088442922000348558001c0c1000c00070342c04c0c8803010041c040c0f1941400d0000e40022f01c10601610840e038a2400031750801c1200d06070f95a000482e1680000183c015204d603603142c408503550303c40018000c54424a0503c001589080c0b2803500c0c007404d90000c40a403140d16000e85041c42c081c0c074081c0d1003203e81d40a1107045000340e0509141c00d10444488034800d8002d84064024020716500d2402085051519240144100100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 746896339 1250 746895089 746895103
    0xf06031b13030c090f05060d0c05150405040e01090c14090105090a1b020d02070609060f08100503190605060d050307030c171611010203030c04090b0a12030504170d0c080a0c05 77
    0x40c000e000c40c170b102c610b2201500305c0741c004000074410381c06085120041200c050050058560503100c2075412080401c103180305004590101c0e42c01420050849040392043d0000c410f442e1007240c2d560042078403038000e441201c811075841900010f08a00401030b600d0500101604442c45510004006a80307806d02010b410901e070800e4007580c0410050910340ea81003010700000c4c086890700410540c142000280782c4840c602c0d071401000000004120302d210ba241d1241d0003010010110f40031122038204401c0030603070700d6009507400351500c4000f415904100d09074075040c0b41d100c40a540707001c819650030340b0710300c4d40400180d41290005465008461490b8014511045c1818900120010601c1d10030002c0e480c07095500c1c110340040c418071051385c004400362419249176000101d05180300c0700105006815943c044066080c05200410a05030840020402d07a01d2096502d2840c0b861124145e03991401c2403070401c005200e40c0c0e10380303000c16241c40c0a800c7c2c0c80403620340a010300c0802c0e01c80c0e5291400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 746897589 1250 746896339 746896349
    0x301020a1106100b2a1c08010b030402010c0209040f0b0a0b09130206030a110d0c0807020f0a0506071b021009180603050a0f0302121201050f06031b13030c 68
    0x1c032840140000c004108000c96000900d1101070740c1c3c0c181480000a40c602a00c51402c40c44010044409080c2d4907841d40388061070340303004c12601c2030960900001085543c46d1404004034907588004a12040c68504403842103070107858a80c09800e1503401e000340c004000340151104c0303203401090750005400851042c09100c020001241e0f051030f400400c10200390203007440f4190620030f03803031b400180c403040281c950000580400240304500894150000e21500b02c401039181e1600290b2010240c10841c1079024031801d07800c8660841c01308141d07640d0740040a01c084c000e54013a01c0004d900d144900e0f40810103080da0b004a140100032640411518251068000080f4000c0c0740306201802040041c08034601c50008240201071a41d112252548000c0b8800b40c00181501300300f00c1854000c01c182014940b030f0748840350b6151000340100e0b4955201707000d458842d10f20341e0303000107062500a0641c0e010320341b0721340c00410349112907103c0e4100307030710140302c0c0c58000303000040000100c1c44860040000f44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 746898839 1250 746897589 746897597
    0x1092112050d050a0603140a030903060e0c0d050a03030506092412010f050a110f07020603061801081507090806180106120305030f28020307020319110607020609030d1a0301020a 78
    0x11b00394078000101c010ba0307120000700b550001e840d900c0429404115541166044400003e01450000d100340c240f40046401903003240c540400ea02c100100050031444030380c002e550030807264858608009145009884007038800b965000c0140c89800141819101e00714000c04d12090b08940e80515401d441c1045034080e100c50b504c1080010446007405180725003000103071030516101c48d44038918658010100301900940c0c000c000608203442d919100d0701d020b0308403c01c11f001c969443e0056a40c50301d04d43e5046510819080204096030f014260001c241c0302850003804103079452800407114924211414500c1c0c1d9241c200000380398503155208914907020340e80741540c034500982d44201416010b0a4128642540842030031b000d191040100c1040252380c4000da52034550b000100d00d1400307040810440820034110f030b40360f180d400004104090340210b0030348600c1d0350381d14010b03a10342c201121801c03442e820801c1800c20180b4107500c401003460807070301d030b581282c444580400e007241c1208071400042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 746900089 1250 746898839 746898851
    0xd08130503030901020a110310021b100c0807030c09091509180b0c0f04210201122d09080c010b0a0e04030914030a1a0601092112050d050a 61
    0x1455592814040c0105400840c6001c50380700000356036404c40e52001d442141414004940c654081c0480d103c0050154000c1d9101e4620400c81c082d50021415500d0b01846103490a84181c99580074a603060241c0740c41c1c1c1c5910750b83d4000305801412031742107003004001341c600c0041141a142c1c850140a61070848600380d4403414a114902102e9502c00405100741d103003042c49000900e6120701c141d000c0c0e860000039071900c2107000d400c1c0b6a4016074002d6030f40362030070b0243c00390200d801892525086000343c1e191151800c034100940100d41c2c008403400140070031a03040700681d060030040180c00d0070b416600040c01c3c58a80e210010103410051900d07280365101d080340c50491402006e004003170404046030b500142041e540181c00404075120310070a200300c01220100c1e995080c08a20341e1540c120141e111030b250702c400e08401c45001214140d01152a13094085121480d0424103c4c0002c2d041b0400c60b060b944070b07201d80d20b0655043c4050320130007008009403076208025004d454041c400524000c549 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 746901339 1250 746900089 746900107
    0x203070b250e030d0f0519020309040b0f0d0201031a0306010e180d0f08070903140a0611180f0609180103020a0b0a020c100203041d15030118110f0d08 66
    0x40306059160074000c00101c0c02030200c8542e0045180c01c04074480e42031545961000420136076075070080300f0558048504003181040c6040d000b00007080c20000c11501002181d0981c0100111010781482d07030f41d04002c6440c0640c0043d4045e40c00006142c1584034035044010684000a217040b82c26082036941d45650000d010020328140b010031203604054000d000306900d1030000609442145d03400c003080140040102e0880b50240c0312010185030043d8044084184640415644561304603013100c1ca1440d0610a40075119003201b65079400600e103c820565445103002c01a8400c24400c1301a07100700200109030b026501d0094216100d081d0042c10f881540c514010421132001540c80400020010401c5c1c1d2130150b4089031110901c103003201c82802c0403950810480c51806950840c0f01444140741c003803400c0010b841111885903070364092203081c2200c64000d05007070b03901c8810300083c10340e4102c50040000f04ea407003e4500c0c01314080c0000d001d658010000810010402e40162604a400030315054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 746902589 1250 746901339 746901391
    0x9130f0608010b012304050d060c1d0a0e0c090418030e031b0904150f0906110414150c0a0b18010c0807032304110109080106030317070203070b 63
    0x8200c1c5400030040d6180c04030010305084c80c80d145010303120009495031500000b061060310060701c40500302d030344150058a00a001044074111050120f0001d41d004a00030f207000c005801e01c014094104442c45150081c1e01a0881000c2c006052902090100380b0141c0c6461140e030180d00500210207004904a040c003624840e1020f0941e4040e8100c07481040c441d5206141d0b119034054152000780003903a6a080c10840f075044a0701e40c001c024100b181032159122a82c01540e009401903d08011243d200743d40c10041740300d140326440c1080c41c090040c203102d1902c4180b00c11001c80741003a051502421500c1c8a09142c05800c0c01ca40c070300030306414094000600540e03000750452410003004904c980640241103520020101703c1010740f91850707001c00342c0e210305031400c880031094140c202900b850b290214040110501d298005006107000041c0640140612021280c154031482e0a01c3c0c0240d10544030000018800b000394841000402c000403e002d038111300c142d03503050328081c158141c110400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 746903839 1250 746902589 746902601
    0x828170405130203010e07050307110109060606090501050301030c0501050702030a051c14090d0b061201140f1f06030c03141504050601050f120919032a11100509130f 73
    0x15910610510046c040c1c2c012003c94680c0028003800d00302e490340e0340c8540413100000f5140c0d48034550b50806440784108940d9802c540161407145c1c0303590540646820045500d804248000391a41c0e8410108004950042e002021041d0020702510450300b01503c4051410100218400f0a00c20b6000070807035881d800040301c00b80c403c200380c08601e41050480090030b00c05800c04054221042c8a000c0b6180c0c0c1d40c1c6064007104a08000001c0c090f0801c500524140072038100d8031001c0d8202c404000548006541c454030081c00a00d00f21600e0a03428030034200e00134803a8880c0c103002e00da580c0c1003402041c54441c4080344900411041a0040b80ca81c0041c003060714009040079044c000207204682810b21000e0136110b030901400c11403003480e40c0310740a0074601046100015282010340c41001e05041d8009209402040d00d2440141d0881110004c10303100f04068101401031144040c2d40d104601c9d10f03614400d009001490100e040c07003510780000b14a142e650550a923500d41d600c0502c068090140214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 746905089 1250 746903839 746903869
    0x305040e0c160201200111030105090a060e0c07080d110309100c09030b10032316030f150e07140f03060106050403292e0828170405 58
    0x1c90300381110502d0980e00e600d04010028107100b0207195020503030443e84a0441d20501000090000d1030320031100304802e50080c002d07035004006040000f5207401c0d0ba0b0262a003220b203407040c124a26950740c1ca4010395034014440840e02d02c032003040b40312000c111a00440188130484d0104d15600c0c240030081514101310b88040402550401071303031115290300b204242084a80080b11854280d43d4a41c903c1d410840580004001c040042c0d011100c407140001c0303000078484020121042d1a004c011804c2c103e4207a444000c0400e07000401a50018800703040515001303065844c04241c09022100860a105480d00a007804220391416803e140c17a02114101420000f600a45521750600000402c00d105500000e040381c5450315942204482d082c0e41071890000320707544246035060007101c00c00f01e0100c000d00260524170b099200d0701d110340500086021294000c0040c020314200050390060000142d5101a01c150588100720101d070340c49a0440d0f04144050016030b40d942000c0c04c0060701254800a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 746906339 1250 746905089 746905111
    0x60e07030509030f0702010e03010207060207150605150901050c06041b0605030126030c0a1a0114010f12090f08190c05030a030b0616060b01083108070209040305040e 73
    0x50140104000c000c482406219541c1380d9a20061400180c5501100e640104c0d019840001c04005216055002d400e15520503248252064440e0007620152a8203008070380d4445150012248400242d200410350780310107050007801c11540070f50007414200b084400303695001c683c45002485580307003441000941000d045c00f600319410135142c1312200125840e001020440d101c0324410011042041d1440194071100320b603460031440c549a2220000800c50208003401440040bd0584c80d0402c0c003030002206944140d00050314160441e507134803504c049400b4683d03840e9100300c0824407418201c0170060041034540d070745904440b00080c00c11605004581040f003107220840000702c0101c00c945000031030b0300c0c001c07070710300c44510000c0c3c41131144865810036100c080c8000320030030040e03400c19603a00380300340c0b91030f2116a280c041e444040d0400681c10b03881c20722100d403c02c181511a807500782c2418020907a8a05110050380807508450003514141d000c15004101002114101018183d00505441d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 746907589 1250 746906339 746906341
    0x3030501030227402d06050c1303050c0f0d020d1502191d0301051e0405070e09100e0c09010b0d1104090b01020c0f090f28060e070305 59
    0x700c2c2d030100c0c1c0b0010300900c045220954491810041d07001c50130074001c501c41041000484088800d156125207900220755600344000b81e5440d005000d081103004549005509403400d665984242c002d20000300741140303004090083e095030000c2c1c00340450242d482940184000340050007000302c0310342c14010461081d08401351900060300d46002c012001503101001103960502024510007078050030160b980c4d0110810814010b650344114414941c40c141043d1151444002d410b040c2680c0c0700300c1c2c40d50400c11600320015422451450060703402070048081d07400e0661142c2c40d00c071642c44140d450784803a510401015802540c2c91081c60041c1441400809040300381c20003040c00108140700e40c11500b078000c51454800d03415a0041c205800041203044d5546d80c80d14a4103000303150380c65030180144510802001c2c281003940003d024650000d102c9505c6944a80603c811600020300a040306050380c648501b141b40005182c2c40c0303448042c0c00108506081c42c04840c68800f0007003101c801c040c2880 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 746908839 1250 746907589 746907649
    0x10f1101050c0d0e601e01050f04181b0819290103060f0c030b03030d0207050a080d29090f1005090f100f080715110a030305010302 58
    0xc4003c008011220b89451103400c01614042d201c00701d005030001032001159942c541080e21700301c0c102c81000074040c4126035142d05c0032418030740003107085030040d10740d01c030005001510b486012402c80f002c005201040b8486000020450290007040c02c0302d00c403025454112881c407002c10413502500d0514010265964401c0d020740c2c01c400301e0200548000a212034486c92011140164080080040841c90055039286401801020b6160071590607034507000b8180129882400b40e140b030100020010341c1800003030000da1000303501114044071144162440280019100005818500c03110360002072088201c0c40000e000f104a025102c0b00c2c41d5030400461203966849031119009241d28a01020640e01da0010507200103813500076940c0020701b6020041c1140d44450f9140c03003080000c0a0980c159600c81c03071030b04a0074090140d0300d0290031410051000340c0784456507103034401e0103190801c041e04918202d0f50505003900e4060b00001d03102c800501c1507041051094800300c24045401c4110701c1c2c01c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 746910089 1250 746908839 746908873
    0x150b0a050409020711031504060b01030c140a0e0d030e0f0405130615050d06020910020a051b0616030e0a0519030b0c09030304061d01090e06010f1101050c0d0e 70
    0x9020302540c05034082584010b01200b121000c40721742003d0212078480036030055024521800b02c40440d000c50500141c00340300d501c43d02840c500c01c1d051391a8038510078900000d840d0705030040245102007100d2194900750b80d50310448071030030244c00ba440726103d0094440520400c1d504011200b4010f030b04000601820b8140d4140c441c20460708800005250702000a003903501c981d03540d10241d4803e041c54111002d000c8070350b00500d401901100d10b801c1103041c0403010b80e1500d04000d005406500135a06c103800c1008600d40e406e460090042c4500d1070412883c8002108030740214044d00020108401415242481c0e0006d9000c0d00c1c1c1103541c903007001c04045003560045800c2c00020030a48403000072401d800240d40039a00d070901d0003403d0340d44841d22540024510f0903038000209100c81340000c0c3d80299402402000d042d02d0312010443c81950301d90f001076401400c001034820070012155140840d0031001e00c0b409014001c000c000990302c0090f135245200f501d03030f044d40c07a05aa0b0080a2080400100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 746911339 1250 746910089 746910097
    0x5010b0c0f0d0c021009030611090a120b16230d1802030d0309020609041803081501020a23010c0f0207082a01110f070e0702030c151b0409150b0a05 65
    0x81103172074401800d00845c04841c1c1c40901d40c401414141814000420300003648040e081840060ba003050f01242d8501d0944e441c03007071803000030f40130781c01480103c1d403521283e949074007002610f030400e001000141b40900c0e0b0051b13030403a01d0440c0484080740d41480d688150140215410340000c2a01244034140c000a440311a00c2c0c0401e000e0558900070340c0115185e55058440b00d280c0140104101600d42c2c03000409904011000c40020355a20300040a106051004011440060f03005005440a642d5503007110b540010104c840d44c0350981d242940f0031001d0145e00f003580041c0c0d9640444e009181d00c0640380c1702194101c128282c01402c814543c1401541503001803005003171048103145d07405d01c0142d0302c0c0c5c10000030003078040c098900601200c490019000d0101c034010740c0c54120035919a40c3c100d840b8020032240c510141c10160f003400c801c01c04000c070030f90800701d10f0450409042410344880001d0f0702640c000c08a07540c4230000c0d207201c0251540003c0040c070300c658106240403034406c002012886 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 746912589 1250 746911339 746911343
    0x3008070b0411010305040b270f2b0c06200d0c022812030e07080f0705010c1104090212030c010921050d0c03090807060203100f05031506120105010b0c0f0d0c 69
    0x1c0002201d029402302041c1584001d01d041c00d44981202101801c5c4c0c851840180c20084020a00c1854140c00d44408000f00d002d4040e03600c06e480502c0315643c1502405c0f640c070011004c6446410b642034130080140041805071400a800a003103c91600301904050750130850540e015100b102400318651004015054a44e015210280c90002c99001740d0003401600003044407403240e500040364807400000c00c1040c4a0803801101c040c030b5903400045841754100070307008049100c0030205000505058025149861000744403d404d48000c2188038650f400644c92458540e450f105120140600140e1006810781001c04e1a080c0040d40c0c00d0280051103590329030040c8940d601304401c85280700e94003064a140c0d00500a6903510228102003001e0341080c1e889540400c03600d00001889804007030300e03c0c101c0c0d60180c0542514140051010071b507281c024051500310032801d200e10001a0f0a21074580600041d8509a450b03600c44080945480820f0440e44065480b07000c1907082c0700d420000642280c0d17 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 746913839 1250 746912589 746912611
    0x10b04051b1e040b0c070b16060f1d0c090906070e10020a020402070305091903153b0d090f0302060714070603020409153008070b0411010305040b 64
    0x90b01030301900038482646803034940c05060118000c20040f030b84d103004012030b0002c00c0840d0051900e440c4107100d0341c8503001001c070113042d01c0c14072440051219004201c20112440380050001005045140d0449849031441d11980058032441454900281e2440c0c110711034400078907440ca080c54002c1c000e03003e5243c0051292118800b092980c1784200000c8400a5000c2c20542d21070030300303142c05009908100400c904c81c8031101c001c2040f9003440c91615044130b0308400030301880740c08000004001d03c11070a83c0040700d81031800510480413883c08080410011452011414041c0a0740d5820211b030148680700700156000e0070070030140c040b41c0c0d03a000e0b2501215141d03a94041d40c9444185140590f40c908220b02a0140c001030154042c1c0c060001c681e848202409400ea4803182400444002c1c021b088081c0c40b00f40032210300c035114180345442d03407801c40311004001d4441d031144003164212190445002c80c0c2102004201304800f03030506135000d820309081c407050030160744200c48600c2c002c009503440 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 746915089 1250 746913839 746913847
    0x4170705090402061b030a0302030711030c07150c0507030b10121110031b08040312020c2d030c03090103061401020a0f030201150816080718091a0c0c010b04051b 71
    0x11581d60b58207800d08581c145c1140d50b10f018038440600070790007c880e6900410f943c09403059010601104450028190001a04489052601d82d40182c990500140104a50241301d580002c0003000600099405070100c1d611a05c1c00c3c000d290001c0101e03800420502000d181c84600007407024654029400c022240700a40d08048402203008026520500038940320460b4201819a041440540124000c0e514040c00401d96041d40d0242d10403d00c0e1550117071f200d5445419200001d240c0c2901c2000086128588480d001a40c540742d50071455050006420001d2054403a41e094031881e001011085c0741d80c8002044030b00041d4a90f60420b00141c05901c49031444001c1520030341c80f942500b12504503e0106a45640e4401e90312500e03800c0d00000c03840421004949100c1c0000c445049596a5451039201d100314854600075041c003030012150f1803400c1e0140100444002d0301c0522500c85061610f48a05ea58460716003900c0d080d00f080c60080e480c05042c000741140607640b2441050351541d0956031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 746916339 1250 746915089 746915107
    0x9051207020607034e050903090103091a010e090609070302090604020327012012041b150503061f050301120807050708030306030615010519120c050417070509040206 73
    0x454030399081000042c8080150f445e0703a0803002c81d0703410320810382a084140c101c1d1410040400c80310706480e400c0040d40709214017145907119401540401c2d12803401c9400c0030030382c141540c41060b82038104088103010807042103c0381d0010844141c0c0800500002d00b0755134915004184c049401a007014003e40d00000000c2104485800745179410795240d2401c0a00b80240581c64000d1000a0500c200e180c881407044c490000b845060f10300b5081080039000c2203031600d5031548400c1a80c070030031940210264100242e00b00c07250308102c04004640e1229036a918008041007140c03500001d209074884114010009180d5200301501e040d5018070400c10b001c43e81908000a44d03001e5594010041c0c4190203000c6404d40f03020000e98000d180540807a102601e50000c2c000003d10002c0c41140002e000b400a90200300d80d1102e480113134510b6040420b0110654903128058550010101d004200005030421801142040070828800110f02500b802400c0c40001540e240b00500040d202e010701140780c0344 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 746917589 1250 746916339 746916377
    0x20f0918091612171e0405100908030d051b0403060902010f2111160c060908062206060815190605030c1003060f0303090504060e04030e1e0d060905120702060703 71
    0x6452641500540c10f0191810090744568494020a4001c0340b66420044648d40980d52440980e10381c24051401c200c0707964813040c02010024561241c0400c1c82c4002003e8041200040001d18010400465000100d000242211204110030010011990394400c0c91150012214040a0301400040380240340c03410802d2160244402491480884540c550b003000441124441180c8851701c40b09032071540e4440d41500ea800c1168003120800b0320516811481801c540140c503500e12400c400500e694603800040e01d044c0c2140b05192920a4031002c0c803900350800c00c002884000700040c11b209803810400460b450702801001c1c14000c40c5180c2261444070b00075007081000d003c7c0e01c1202040d2995038100101442014400c55002da8500708011071003554a80d000b91049800d07445842c00100c9031414000b00c0a0340c10302040c0c8100d110041101141c3d1281a106011401744001250301e05a5045c41c3e420000e0101201c61042d04c00c0100344010b1319488195249075425040c81c0410302c0c68101003503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 746918839 1250 746917589 746917597
    0x50a0309170a020c030712021e131802130c0903110a03120c0303060603021e0304050c0301060b0705010515010806010513090609020d050f010612020f091809161217 72
    0x142a034801048090340150f00054030130600301e0440440385010354a41040c46140004000690084034215503c1020b030040c00040c0340f1403038098103162505411681103011100048040c56001c072406c07000c44194544181d02e09a1540c2c0c400040002d03113082240034203a01b080b4400141b641d5045811a5001d5854450300d6000b5034201d101100380144036080103118041b0120110302180c0342440c082440c9100303100741d03161003a5058000216001d214400d03031851b00020000c948910400c24180000d032000e014400040040541c0103482d501580342c40c509640004028030041c410780e0100c01181d0381d10025241c1c00900c282003e40c0d448032041307604000048190048081750781071010001d003100c0c0d40ea00404081c21215001c1156840f020489201d0110038030544001a900782004003481e0022b5000b1b05e80c900104d0310301850005100c02142c1a800461810400b11014804010b02e00d0410311501d000c0c115400e6030148418203180350250850388203034000d41101042007034604c040318120115 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 746920089 1250 746918839 746918873
    0x30c0111100903120509070e090706050d05091606080601030609050c03040807020d0b090a03080c030f01051c06051305010507050c030d022a01060830030408130b07021f050a0309 78
    0x45c030961500703c6401c0d42d11001480b40c3c503e1010640001400b012313001c0b525600343c1d11039030348091400400c40e1300c08000d0700029042c210f5038068459002001c2c0e0180615000410294540c0b841620b020030016003183c01075031082d88800e04100c00c01141c01c407503600302e030342c0b242d80861500c0c1c4416550010035101e81c400f900c0108440c1420301400184140000c001c2256072080d40c80301040d541e41038140105010541c2c007030050490f4100107001c140707420340010a05490103a17a116440d600e40c1c0381c5e84140c60007030710b0b00085008a18940c00500000380034082c4c1c862114140f55240030902030740c1503035038414480828142d48e40405d6110f000501070348810301c1c01c0b14054040001d04180b8103000c0c02801c0d10f1085480500c0750007035200d05052488640841c010381050100302c0926541c00003441648000c0080b10344041c04c001000d141c240020b180805421641841502c540d094814090007101e0243c400c0d020708080d0020414450b0b0102c1114295a018640424005558905458010406215 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 746921339 1250 746920089 746920091
    0x11040503060a0f15180f0b180702010e1504020a0806090601030602030405071511010516050a051e03070c0312020721020a0512070516080307080f040b0711030c011110090312 76
    0xc0001c0c0c201881c01152500d20311700c0401c000132149245d1300000c5562103800c1a40004007100201c2204840355846a8486050b0002044200075130b10b4641c185080c01580810700f02c07a9a082c4015428400c0034140501a250020046030401301d00b026542e00c0144001004903400200103030400c681031241d1030080040d00c89020030031018550107008180c0c2c00120390035943ca400d00188600070306809840c1c800100f82c441c41d00d001c82d07240d421241644140902c2c00300089109040801050b01c5000b9440b0b01003c6e610403185502ca0b00d00200044030240c2078128490060100201080510080d640741c80035400c480c0300914416202a8100440d1303100240c5240101392080040c0300c421001480a00d00c21004e45840240d58944000d40518600031916a50b0041c000080051041d4004281c40d015400001d82003542d1085040840e03032004004a9080009446072091402c0421411f00e1181c0242041d80c10f00c0311400c0d01503038580c1d540e66040219031712a0384070b030b080c5030007484078141102600b10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 746922589 1250 746921339 746921381
    0xf010f0522020f030a051f05130b030d081009050f13150f020904060504060b030c0318060c071e030f08071205100f050105270f0d060f11040503060a0f 66
    0x101d40c041c6904100c600b0f8400500701000140c0c0c40e4074848001e6441710a9952194200d412304042c8a000d480100300740217040e03030b41c0018001554003000491440d280d0795480080078600718800301d01ca06640c0c0c0c0484a101d0626080c000003c40040004d03500007009031b14510005009d00b020040700015148021780b240ca8007000c1940346c2c2d480d4000f86040501a0741c280700640c2c1d29802c0c0011038016220381c0d0010142030011a21140300000215084200d03a903100216096601403d401c01c4410b403000c242079100002c4a43c1041110040708580c0d080204602901804984010b00024010740c8404100029240091003d0b4000c19210400e8011618100560f2130410280300441c1e80078054081031142200c4005001d610883c22144281c0064504010304001208080c5241d560b078005554088a030285e41181c90700d5110203845500e00178a004151000080d24000c00c4409501c0004d00c003810402c81407103191800250650002000580000c18924440343c00005203140711028500c402c420b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 746923839 1250 746922589 746922607
    0x20f1209060d0e0d09060914270c0703021b09040b180d051804020310031202030405041b0f080106090b030a11040605072a261e060f010f052202 63
    0x10b041440d6a4454460700b00c407a4075000162603044041c4a40f00482d400744a82004904100030744000b954881e02c0309d081d035144204952140340600300c55055a04002103060350038180d04010140c1c183c550811500e00079201100894440343d00200083c0090300e8030070100b900d0342a82c88203146166a0341c010794903500010040103181c1e41c01208148a4490410788010070340c50144200c9001e00c6228101c650701501d987e40d900c000181501400f0207600040c480010306486900858800c80c00c2c08005100303c000104010f840788000c06070810410110380c00521400f50000101400e513204d150b0005c0d113a0342c43c1d42c0040302918029500e0003d01e40040b43c00960355800c074003d854124803484004410740040502000604910b0346420700100380c1d5103041140b84404804c061109003240320031102c0f83c14145001c2d1070036210310b210b0051001d503000d01e00c58140c403d004080c0c101392503800d00840b81d45000c0d40602445250b001e002e1140c88a00311504a10740c1c4070041441500c00c0c800d0541d1034030092 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 746925089 1250 746923839 746923843
    0xa151a180312070327030f0c030512070b16020c120106030f06020417190f0302012004050f030f0a0b100f03030806040b040b090114010306080a150c020f1209060d0e 72
    0x4940201d005c1800e20030200040300600b10090002d440030003800049519640355a903945503881e20990b821700f2890800700c0800c00600c0012100003c01c1c4400d41d8541d003924080b070a00f04024222107509080341c00181d00e09601254180c401c0400f201ca0001d042c03041c8100c5d9004248176400200b0818048a1600410142d50080c02c216940d000100c2c0903018050b05181d00c070000440304041001c0041c640c10005803144000d84111030207480002416071032040f450201801040081c00e9980c07001c40c0410403803605a4407100c2c026030541c043c0071441103c01169030341e418481c070f00038650780880300014501019503030504003d01c2030035074102410313542c1e0a015040c1030303061310624050f904102042c3c150f402e0500070560594800382c0245020703864440300c1d815108800b04403d0400d52502c2c000100840c0400c001016240500c17001442d007506a031132042119000303010201590818100c013807548001103010320b0104100580c09980c0c41003140000e807030740710340133110b5211803512020f140e0390100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 746926339 1250 746925089 746925097
    0x30d050601081e060411040e040f0c12080d09140d11010c090608150307080a0503030f06010e031002030615160201020f0136020411030a151a180312 65
    0x2030300c4031401e94075082c9004614a0703954104425550a582c04201e03d42815444808402c46c00d24890303003095141c0b400885401401d0301e0640d103005050002006200c5140c010310020320f0443d1a04a0740820350340c0b17085c030b140075070100c0143d09039580e066407003440003816142c50398040c42c00c1030312003200c0340a5001e0084801505564510340c60f11146041490185207030409031240da0b143c09481c0e41c2e4144000000c3ca141c21070f07668041c080c1840000d40002c0400c500b5410520035405551a0300c0e010140c00101c5900800301810030111000d085401d4070041683c800d810414400075a41e87c2e03810011804c4040d0101c40c2d501425000142c0391b005460170310b041c14110f0300c00da0030703108270031102000c980c2a01c0141080c00d00303040d0341256030340050311407240401040324500d0903000c05001035000a41162148401640e0f02e20000003040b400c15200c2c444c4241e40180458070000c0f490a0101e04550142c07800012142c0f00800182d44928071001c01407100c003240010202d502100d4501e0b038000460b04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 746927589 1250 746926339 746926351
    0x8030907090603031409040e030f0a141318110d1e09020109090b2206060f0306060203120402060702040509070519050d0206130e0c0406090b12150a08030d05 69
    0x8031200411000554060001140c1d0940c1d5074450500500ea010042c540c415108950b00565800b80d55045103000d2001d000a00c8132a01d0454035110411700103420840c00200c0810b00f040204015000301d005007001da81035800301d842c0d954485c201d00a07144000c082e82e000f410310301900480d6802c150f07002a080240301110902c410810901d01b00d00e00010748850401c003c0c080ba8a000003030055070403d0340680041100103006600d11291800d048200068101a400b5516120b1b03409010f0f29030450540c070720b1412070303203400c0007500d1403c2d000940380e018080c0d40c0d4080840d094049401d564801055481e00c0c4d8000304101b0080c289100d240e50381c3c0d03003d4840d890041c07070111480f1a10101004103d030841d1005040c01e1210361096080001d180c1c008414803d030307218065000721307404014101b61032068060764109540c031030134180040d00d00703011a8004803419000f0803c000d042054203c200e904076011011184002d01c80700e000803500866a0011a1540f002140800015400d42c02c003500500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 746928839 1250 746927589 746927593
    0x80912180a06170a05060a0b030a020301090507050f0307052a0105040521042c090106030515090d030f24090e0304210614010e09011b0207050418050a080309 69
    0x2a50701d60064030460050148502c4065110f0700290807940a80c0000d64010001020350304825140d80c00c41e02107400a50707581c0d00d504d0b400b000510460a203442980d4002c00d0707500700581803400d050740310b80309888001c000e801045030104820400c1101d601c8885011a00b00c0006481c51010101c424001c0604880030307a8203201e001d0700e8170100402c03541c9210400004107020f6160904006031300c1134012082d4034055100007400b030f2000c038900340d955409000d401031302d002282c4030b4a1420414900a001c1e04804901e85458051000f03d2600007450711207803000e81000f050701c100109040d0002c0000132000d00d1032036001200c55504600c403140000075a04048400c0180c070882541d4030769a13014074004c031800e1000104500091401c901e00c0c44181d0f40c42040c01190280420001c550140001e1344401506110300003070040b800701c28068011030404079001c9550240e201e200c002d54407025886070900403980e415078042a408180354540c419030b002011518160890300c0d00a007554801c5654800f18 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 746930089 1250 746928839 746928859
    0xa0b090a0303051f0b0903070906030803041202060705120714040915231e03030a03020a0f0e0a14211f0207020d020402030a021c0f0b0a0509010608091218 68
    0xf0000404d4803050700016081210000c030b04000f05100c413a4132842150ba4103110344c200000d4810035a020f98000b4510a07030005490707007442c1c94403800726aa1042c0b248159040714040010056000b000d070f803150025160310342c440b521072004c00d071b8101080d0f000300f0341580b400181c0131600c504907400c010103480010444140303480c0e488a120096003240004002070100c26248841c0d00d01d401d907240052400c0d010b42008045419400092841d482038803401c001c03e4000c2401c080c0c160b00301c1002e800c1d03040c0c0340c00c3c540349005002e00021801c1c94980594008400050561410b50f00c688100700c80d04076050101d042c035030400109055484d0040c484020f0345d240210440b03c44918140203440f20746601600c4e0004881e00c07070303003008040d401c02401840f40070780c01d20076003020014202142c080700d0300c00c00c030019041c0f00c4001c0348000e607100600020300404015804012a880303000e02c190440f111403a1845c415254110154142031744140b1070440313482c000c1012254400d0b075560480704214229980006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 746931339 1250 746930089 746930101
    0xc0f030207230306010330120605040203130201120f05011e05030d08010605030c21010603051b0405120102041d010f0e090c010c0206090a0e0901051003050a03110a0b090a030305 78
    0x1c201d4242c40d003240c0540100c4010800120b00c5e002140050a03140d0740b002e1415044901c600ca0b044030300300844005105102945114841403107503e01525007541e013036185251150035070f8a4046400c6000f810090540c4c9a06501d8115620404504074006024055540c1d20719000383d1310b01c030f540055505c2282d030700390018891800043d101401c580c02d45038820380341c0c40c1080c11384540c1c0000b0500700082c2001c0101855405403051074141100c2e6440701c10501e5414003a0080c1103d00082201c4003d01c04400c00c0c2d5000c032250001d45003221011a010a2031000102c401d5019004950103490010f07080c81c521000c0082514840f4143c48502c80c0811b040d603034075240c0e0034400e401600c4c00786c040e8200d1044490395500c03e00807007e6050014040f01d2070221031501042e18101e041d0701003032030b1103504024050451400c2c02103640001c80c020001408500710b40760162900c503001c40080500c6141015044007400610140c1c0404e84c014240c030026141449410352a101e000c141100024903080001d40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 746932589 1250 746931339 746931389
    0x9091918050c0d2310060e150102010b1e0a050603040f120201021e070203070b0f041e21050703080a050d0b0a150c030201060e10031209050105190c0f030207 69
    0x82055008003404440c0400d40644111440e000035120307044d0702482c0758441000403103000d914010406841d2004035481d12492403002d084c450b8030a18116414060312078040ea4503203014a221422010140484600000009117810503580c491031300501c0210411040c041024408680d8032700482c2e42d84540101504201d08074030920025181d51b950310840300c40c011a5903000740104d140302508039011640c80320f60028071070304040c1c0301d0495000d00203024858880c07070b079041c1c0301c11508610300c8a031500c0c140103c1002c60404c886161b200e10044881070300500804020410045070450318803503a5824812008085a009151828a1a044c002c0745041c0d41001c9a0351070071624045414a800000050b003120000113842090302117640301d0002040103000001e081d8040d140c0190310070400b5241d403401c1c003180031901d2141014405001c504012a90300201281c48030040800040c0e80174401c541c068550403010762000d40320880c1c50412400301600020a50245c840c4d003a080d03c0100d01200c1028 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 746933839 1250 746932589 746932609
    0xe03150408030403141b06010f0b07080f0f04030c06091d070806040b01050c011103060a151e030e0a24061202120c06270a080309091918050c 62
    0x41101d1810000200480d01c140b4038102d0550f103075000d251601a000207011075801c854144e1000c3c2d90844401000b4190b403c80d0040010107011540d1410104507480d45a100c2c040c109030131107500c00010f0b0301d00d80300740c24004a4020315400b039881c41440307494500c01005440705000c0e80c140203200c800307882c4030340310f0070803400b807064a0b1030755200350540d108002d000c00382009080150502c03d09002c04c2980302d1083c000d00a04200e6602900d850f481c10004000d9040001d6011601814540140412680c0c0c081030fa0f040d6901c4a02c0480000080004120005c0407410b054070b0bc14007034580c502c0c0030040d298006140a02070304201c990390000c56410300c0c0407607240744580c01800c1e008482e07150060802046e40804032a045040d03071002da1408010651942c414501600480d103114140e00998030305069010380b4407001d588541d001801e040c14240d80340319503c4440c1c80f94445200144440044000506120034079034804e02a40402d002103d09245848000704c03900d01400c01040c0c21420480e03654 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 746935089 1250 746933839 746933843
    0x6130612051005031903050405030d030e010b0105030402180613050705030405160b07150b030a030804060623130e0f0d020106150e06160f080a0807020f060c0906190e031504 76
    0x130348411030000c2108000081799080407410301c0000e000000e800e640921024038181a07544022600300c0d06a8009800c4440e072041c17407414480306005020151700c4105802403c4010704501c400ca81d240c91001641d83c540c00c2c210040b003e42000b040203281c0e0ba001e80a1401240b1580488410201203c61a40c407404140221144004c090000c00041003901440f5031407c01d20000020301c540050011901f0640b0801c01600440e07000010712040141e180310340310040c00d81070380303581000b14080b00b00900c0c401000052817240070010341014038845a43d01500180705944101c0b81041d2008940781e03101c00004c0c220030095468000c0010711009520b024030700550540d6a8a0a01e103d05810841150041c091521006201000c20000030705203d0805010034007550309980c0710114024001c0074000010440d13000c54100a0000307c14500014006401020900c107c584428440021840c07c1c0181c01101088600c205800c00c0c160307810004118044c00d0a80030b4454040c458442d141102c20140c1d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 746936339 1250 746935089 746935093
    0x406060e1306180b01050f04080a1a010b0417010b040606080711060603060a0c17040803010f0801021912091a0708010e130609020a1d01051002010905070509060613061205100503 78
    0x568002900f15440b1542c1500141443d03030a0400740410864103822917005041c0580c42030341c00c0024041600e03680101c5004c0000b00031040d606000072a5024000d47c8030301908168a000e00049020382900070410440b0094401c0059554841c00203141d440182d039004085480d00402d00c000f038030042041849444040d0050016031107440417940100b40000c40c903010804000303591000284600c0f0854061b038000c000b402d40765414555404100c5801d940030140683c81004040482d05040c00003100b0b0241c80e0805035500107c018400c4068419020010300031041c59004400c1942d03000b460310701904041d9210540b136a22080407281000040d01c1415469180d0111103000a0b1160401c1200720320103420000748660b501500e06031118440d051003030f4540c0d104018055410b10202611b481207461000f401001059104d0b552151014001c0c540681c880c60000354454490034102e547c20074840c0c06a050701a80e0700b01c003c118a000b21046407285003400041000b10482d01086000e0b910000c1c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 746937589 1250 746936339 746936369
    0x50a020421350f1314040b090601020a03230403030507060b0a030b0a24030503090310060b09040e010912090e011a1c0617160b030f060607110406060e1306 68
    0x3401c404507402101c0100307400c0e00704104410000c0d41c1e8a181500510041171a1400401c1420070841078580c9100c2e41ea0281115100304a120b03a030000b1040c01068041c10301140c11240c86100306072100780c2c0d01c001d00c200200040e0000805601500502c003160242104001d0350072140304200d416002c0d403201420079050080814480c0f01ea551001c010007440001000c0b550400020341c4100424643c015078640c1c04c0401c907840282018405194901441e9900f044090309084080615000700381c1c0c07407030042da40c44804104145095001d01506a0040501c7d01c507034546d00e4005100c010305028415002f48080c0000800ca000c2980780c42003003050f510f480782054141404002c1c05d5210000c821a82e03501c135000010110841030300c00d80a0003115000e051419010700032500c89c001290b11140e03c05000704104000386101e150f0003a00004129030450781d400032418811603141c40e1040155000e850703c2c0c800180d064002941c1080040c00f6a0f0f40654825421074041c00c03200d152140140e1400590 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 746938839 1250 746937589 746937683
    0x9060504090819050705012c0c060f07020102120711030f010c08040807062a02011104080c060702011205160f050a0e040c0c06050411121f050a020421 66
    0x180106069401e14216040c000652141e5080d25008d0381455008920484007942c41d8410903e08044041840001d06e44440c0503c040b034218841c08003031030b031900c03c0843d41d0811a0310034030001c011050f48040c410303140e1145d07041042003d602c0c581c0c02c601c01d220316005640e100e001800f4521240314651249001039071503403111225503004030021203084d03985500c40b800d5556000140100b01c40d00200718240715206d507801030700310340080b0380383c0c00f90030010f100030070103010000740020a0080a0b10502e8640c10548010f0f582e4944d40450443d803607080c01c08018217111003250080c0a1029075403900910012041c054941c1d200d202c466000050b840c0c0d4500d0840c1c03c2940003d02d46e8000c9282c14810780d0360716103c0c20304884d81580c00b11020784494084080701d18002074258074001e480d2000d0a4600101d0300c401ca1070b006881a204130298a9400103941c008960341510010408000445d1a0303003410448106d00700300c209000c46040b40002031808140c0c41d030280304100e900c0c840c21a5142c0034054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 746940089 1250 746938839 746938867
    0x1030e06071409120609010f060621090c08030301030303020c10020901080f040c0506070302070504051006020604030f0c061103040312020c070b0d091b0f0501080f0105010e130213090605040908 85
    0x602d200039080446903201c0000940d0400c041d034440c81b104800002e081c81212458019030b41103910010801035103100d01c44043c3d101c0940e50805d60341d05240020720318214900704588229039800318205010100c0004141a00754009090701c003c00380071f60300c50480307007010b8004038010186050700007a0301c0f00010f1184416000080d40003800740c503c0199a42c1d4500020794a6440309508400607084a00c0c1048281024010035410030150b460b032008a90405c4d200a5071070304020b002900f04030f0543c8103000514000c02006048542240041c440710200e0415141103038400d5a04030700040c124210148100c01c68801c0d29807208071712028008441c600080703200c44c1c3d040320030b030786074010781d0f800012000440503d002e5034600c414207205a01d96242491000201405502c401d0512002d10100003c2820b4900414155507003401c02403064240f0b000401c0108110708400300542d440014115480040003040000700c41c02f800e42030000a4650052106880c80550010308801c02130002482036850 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 746941339 1250 746940089 746940097
    0x19030b03010b0a06050d050f2e0503340807050126090f0d0c120f262d040308040f05010c0e09060904030f0f050714070501030e060714 59
    0x1000440c12502010001c1c60190f01c603800f02000c035a00140310041021180556035111240203001411460070705030010305803418070762007940b00c088841d1622001d20001002c00107070102070101c0d11405100980442103a461881441110103225051403a00c000c4903010801d451000f005041d40d9464100191440344802c04209009641843d080f41c1d5110445455441a66180d00504c0d40c00c5000201c9070404683c01d56680c00c00140340040f001081180c40801cac9061068505000c10701480c0c0700441d00d4020580f45000740e40041c441e00040c443c80044102c1c040c0c103080c00c4400c00c030855000c0d10001190700e821500443c00b41400000c01283c06030020a500c54064110411248056640c0ea400c60b4072603944070011074030304401c4a04504100244540c4400141c0b40c083c03090900391000ba00c4042c0c1004041d0401000c0b05405a80c14850402d90342441d03446500480c110b086540310a480352500d000d00350000f4588032a0840140000410b28080c2d07103162618040c2c0001c414034100036500c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 746942446 1107 746941339 746941361
    0x80f2107080304080d14040302070608070905031c03090507030f03081b18040e100504050c031614010212040303021e0309100c06181a09031903 63
    0x11a8075040741d8010350040c01241e01c41200f40f2000c13000e084100b0070109200c1d413460a000406400090003030950741c070790b1940c0307079141c1e21076004a80e00061882aa43e0590003012500100da001c0344400c00d007d5554680481c034941035482b160300d040b801d507104880c9400001d40321414141e00c1200c46802400420680f0ba080ea061007520000e4081c2c203500842510080007407803032a5a8540c800150403003060280c403002c0c40c0203220b8000401084a0a941502440c40c0c02211450040350001000010084855120341040060f42c0ea041003007034294150301c03403550460140070b4003102501c01584254000c18000c0c235480154400c840c0030601080050b0b106020003403480e0b4402e4011602100750740381088a00c800740c02d00c2d101500c0448094004108107520142c10301401003d044021388540c51480c902e619112182d5036684500b40c4410741001d905215000c140b4404c0e0400741c2040 = true := by decide +kernel

theorem cover : BRFrame.Cov 746762589 746942446 := by
  have h0 := BRFrame.cov_init 746762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 746762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 746762589 ≤ n) (h2 : n < 746942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
