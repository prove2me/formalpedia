-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0928
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:00:57.592131+00:00
-- url     : https://prove2.me/submissions/ce59a46f-d340-4780-9823-7ae5fed81089

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 166726618 ≤ n < 166906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 166727868 1250 166726618 166726661
    0x50403050601080703030207060807020c01030902150a0e120d0f080a0b1e010905010e0a0b03130f0b09010506030703020a03110411210a060308070b07020c040f06080c0103050115050c01 81
    0x5291341d5040b00303110840140c011400700103003190050020070300c076140b180c004e41030030b80402c00110020076400300d04992041d50f1344032086a42000801074002c100a5032152110400e082080011800304d0b4041c4584990228401d43c0781c1c3e50b4040c001c04104c0301181040401034070384082c86e401508030368612540210103030040c40200c8400200007205203800380c03154400b1644030401141c0103110801d900d9040752001b41c04018042004c0c1c01907601640c40005912030f0a8941d0300c501c140c1800402c03c0c0d0390501d4110611042c48020b220b0f40e42c01c0113045008103410fa1850b8081110b00c80b0610005d440e822110b00e40c0d510b40d46640c1c0181c0c00d00c16148004650703032113079030040c0c4202c900f0310414800300702001c0c8002a00d440203840f0b400242c3c0d070006541c03403d0002c285e885110740400146000c003140100030441d901c0303803528005e0043c507413034248010403450f0078481c0c41032030b0030316401c03090381010306000c0104101018043c1450139082c1521b40f065640d500542d40d00d01510101c60180d00c203c003c1e54 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 166729118 1250 166727868 166727879
    0xf03090911090112060501051b030d061d01080304050108070e180405060a0b032b091e0905070e0d060b0f060d0507080c07050d0e0d0b150f040c0c08070201050403050601 74
    0x7401030036a03071000d88500021960644284040303034210700420740840c00411050081c81c1c0c1c400046181401076400b201c1c40c0512204424043d60001d0380030301c400304c0e40325111100b681100030b051809402d015000b141040d02d040b0008040280242514051001100040b042a107540301a003142e00604484010103041624009549d5141120650310540c90100300ca9030170310300440d42c500207007054174003410500c00c04840c2c0035503c001c5115083c01c0c0030741c00e40c00045240b4850684a0440ca503110007920140c6080301c12410b031384000b0030481c208003079809400095503d050740090b01b01c0e0840c80000328000148003050754414040c06441c1c0c011b0011030180c1d060030720358102f03603c10005569800042d80360951140720900030ba9000030701c10b801038030f0702c0c3c84003e10800e4404c501e0040280541456402c81e141c56400510980d251a020f602c004038030341031800e00c6036020040c000107031410400100c0b050360041c10303c00984402030100b40001025000d581c072407006d035809960007000740d031450f5035039a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 166730368 1250 166729118 166729151
    0x1505060a090e0a030305060d0f02190f09020406090b090d06050702030c0102070b01080c0a0f0608090a0204020705010e01062106050a1506021e01050121020102070f06170a0203090a0f030909 83
    0xf00c000718002410400001e071141441100181c031560301101c2c0b240c10314080c0e801c02c00300e40200061401d14441c1e0b488001045c0410007074650040c01e00e92801030362203003480c00041c84c0038003607003000d110013208010045a5840340200c40b200c00390400c10009254642d840103d00710700c42d08004c3d0240391b0020401406200c06012041e04075610001150744500052043c0b201c5140148910940c5501c840c4d070801c0100d004000350b691000b6020155035042d09154006000c036000120184c845a5480b8150509400b0910a00d009408102500c0c482c260003152403080460380814024001500c860100340c6200054002120543d04030990491064580700001e40d41d010180700d0030403a0040b2480500400030620400341600c18145401107090f6401401440100d001c0404074110305c40c43c000040c00000f07410b402000b4080c035640300f030b48107035407455180c20300100503155461031841001403021200e03001455480c019805502401c40012608050303540c0d480030361050440718205201448272a070b54 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 166731618 1250 166730368 166730383
    0xa0b04050405220f0515070f030524060c010209090a0b03061b0d0c20010c0f020f0d0807050f070602070311190b06120717010b0d1505060a090e 63
    0x60754104071940d1050300302d80d0342d00c203186005450012a51450004980150510000f4a006004550224120b0703d66440020004c80340d6100040c9a6000000c4046e41409070315004035152001e14a0f244075180b6481d02c2800d40d500c203500c112400540c0c640f10020a406440904c00010074801840ca40704107078001820384400f510707210b4001d44000400030807404484904140031071170034a0038000d0840d41c01000308444481e8405012000704a20250300392001d0032074100c00c5503000031405501402001e0403a01400200310300355000401042011503000901c00c0403a403c42c80c1040c1c0f241c403612000d0f01e281c403400d400b4031320780b4100080300402e00117a90024030003e0311a0b0745d2185001e010006003522080203d40c42105c5184050100e80072402c0c1212082e000080104460b4803c189103513440c0c9058801e074450b450042920001800030038080c411300d0f4070003d05880080d0349880a07590000503405128504800c03e0b60b07000840c1c1c00d61259107190000d4070300500100100d8010809181d0750310308 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 166732868 1250 166731618 166731629
    0x215090c2112070c12150c0c0303110a02030f181216120f020904080d140103120f0906050a020a021201021308240c0d090b1602071401110c0a0b04 64
    0x291000d02c0d40d2400340c1200b00c50f10320307400400c55802c1c582000001070b0f80c1d4160000c00e8800e002603081c24000d102051140c44118a142e44078151480c203245009810b03906904044070040d03505100001c49a5004030880d02170103d103d2446030358450b071003055040c4c03001d0b91041e1078020040c01c0e00c42c0c642d5640082d03848d0380c1c0c0d1441500d04825036520000c8140000c2144002800120304400d4580141070074204c00d9002032041c114641840302e0540c8600840e101d00c005100c0260b02180100140f12181c10100c100c0351880c944646d4020502c600541940110f01c12681044000503c03424610b2086c052600340c5039006168980c0740e800500110f020f50030018218500b880340940010780340400240426440d60760308441070811070440e1072a180d0b1180102401503007141049481c8828034144164042c041c82050414554200144103000311040000703e40159801204d0600c180d4001c0a12007a8012091070301c500d5800840d94628204032103141510341117507c030344000c140583c07c10301900641c2d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 166734118 1250 166732868 166732873
    0x313030b01150c03030c090911040315020306010f300209040b0f0102100209010c1b03051501080a15020c0717010b06040f090b061e0a030c020d0215090c21 68
    0xd80380d401182000b11000b880d01d02140c981c81004002034069044030820301042c0c10204e1040741d882038041c00303481c006074007401024400074046c82041a1980050340d5039200c254118118034051001030b1100b8091601c2c8014044101511075400a02e080000d1b0f5030900320150518410500402002139007240c109a4440c5080c00443d41160910880c8042044030590052a20081c400b0b46030000390301c181141810081032408010100d00001101c021850700d000216004a2031410181e007850100000c2c400c003c1d14481c0108031201000410002060b00151030059072025216400024403508e001a1030f0390245040000c0d04014150040c070302c40010b10300a00c112710564041010a214a0140320450320400300c0600c0100042d5100b5100120080d00007442c1c02440c61210032040000b40c616081b8640c00280b05404990502a00b8443c0c240d500041800d19480340d400707902e5407040d204c0300c000c00320080002000e08000700900b030300d60f80000d00784200b102625080c503203903488134140606652 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 166735368 1250 166734118 166734121
    0x190606140f0a0303031a060705030a020606090c030a18021c03091203051b0111032e03030203071506090603030c02031203060a0314120406030504140318040f0603050313030b 76
    0x181001000301e200c50310014510711880d41036a8082e00100400701d00001a9003030b605104060fa01da403402882601d0240c002551220309071a00289410310051010340550321010600100c0c0240c2c005403904980c41c404049610058800d940b021061062406580200a90940e2040d070301d00040d003069442c00303651519506503d0f4000411080800707000140041e000704141e006000c42202d07902c0d501100d58001064021221aa00b400da40080c1c520f90007009006c1000f0030b40981409107200300b0f0440611800c161031954902030340301d00034054042e010035400282e0a41b4050103900050180c41c1d101403c000481e1a410010286c1c150100d04038080d10a91024111050010b000d41c1d00c075807001461248180d066645d092100004044914003a05c11203002800311840781018001400895070001628581401c0c80c40009559410b61269074000300725410112507031058a0f40107104c25600440c04400121400c0c0c0200300682c0054110300011072852041c2c24000c600000302c1e409034089030000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 166736618 1250 166735368 166735409
    0x4050114041b0906081506040e090d0e06030c130306020c0d031a0a051302040801110702011d0609011d0604090507090801050105010c20030d050a110c0d0204090203190606 75
    0x144207006141c000f140242c502089007900c124126940070215128010303411041d0307408119a42c029805c14441810b03410304108030198204204940640c6c1ca10b0150441200200464032501c0058001000402d0004984c0b0507500000c1e0080002c0d81d20000c02c5641c2c0c60348400135900d6a41603041500028240321034910460303c26440519031040081c0f807855030518010410504081c9a10f200030204d80911001540c25003c1c0700c0c00c81800c0701e441c2c1d5155602d4103403000520141c80ba00024014404544d0f101c9272646540042e103600413400c0c00d02c41303e03c403070305090510b00c0303003950003800c0d4003420011380441c400000390003060050a542e19001513180d02c401006003650380900038280040c014100d400080f8116541c00080f080e500130300e038085210203501280c104803c00b110240410760000366000b8a99210201c0380c0304c00c900d0030181100a1030000090311003280004040d215035100d840c09020b565090084040c5105040e010200040180c0b03000e201130710403449480000b14000004821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 166737868 1250 166736618 166736651
    0x5070e0118061a0c0f010f140703020a170709080105011815081b06070219060809070f03021027080d080408030a0905070b1c0605040207030504090b0303090405011404 73
    0x42c0d43d002c0340310030ba10340c10500e91004290000740c0310b42040c0c450b800320081c0f40582132081400c9070306c1040c0c0210303038007150a00d020fa000d04060b1006042520402181d200d1030780c0640700b68081070b80790410070440d45400f582181c1e40c40164200755029460003000081e0042ca5800c1c1c2c0a044d05850800e000c100100546c2c840042110302c6442c0d01504101400c0a00044480c0c1c00c074010100202090309007010717500404c14840704076201c0001c0d035041d0a01800036a030841001e540c080d00c440000c050301d81c00c101d0001c0d100d860900c40203000e101c801c0b0030a10414003a421300c615029103d0441030090a00354642e040010962203410000e024190980240324400c07070b0400c4c8a00e030045c68091840d2a0789680e80c0080c000200300b99102d024080700421209284001083d54100411040c00030f42500314104046452503441544101c0c41041500d002a4001d07040e28111000000300103100800c4401090642c8142104164401d190100120b0952049424240c4983d0155000c2002d011990403004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 166739118 1250 166737868 166737881
    0x705121509010b090429190f1a150721170112110411031504050105040e0d050f0405060409090302010e060103020f101b0b070f0e010807051605070e0118 67
    0xb03400c21300480000d40415140c51003a40f545043e0000d0103002c0c140c0300c403069100e8100f130f10303402074607000744194000c1e0b00c0d002c1c01011540400000108a550301c18004001811003c1c3c545500810301886030f4035000c1c4218046e21055500302c2c10584524503807900c008524025081288042414110901607807050144180d05075043c5100305036003501d41d521000d0400418440450f070041c1c492440011840c1000c0141d40265403108045440103514801c00054480507000f841c069464604440b21451001070400d0092100e03003005d65845110f422049101c1c4206d0b00101d81004001400007a00b400c0c0d030b4802d00f0041d000390b000300854894030f480e03031752114002c0c03101039440540888500d505140008000c15601581c2c1480d8030510f90f2400484404030700044c0036546030848070100001e5540022514031412100d1034003100c05641100080e00c202400391207102004804504144000351401c281c0b041c00c1e40060846500d02da5403400c0119a00090141580e200b10808104400c04051f02070708 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 166740368 1250 166739118 166739141
    0xa060801050a060c03051e0d0e03040504240605030402190605030f09060f040210030b030a0804080d08190518062401052d130e1e07051b070512150901 66
    0x1c1740f5043c6e00340d5407603100c8060100c4030300c44041f04001098005400384603080098410a01454441e40342c4004c01049030800e02c0403551a8400070541c040c0d000c8401e02c07486c1542c5031402e040e40c5980305d9001091b0081103004009450700029000401c5298019001d0b510884e40480400300035a1400790081c2c80c0c0909941a0f510f0361360743c01c0402c00610741300300000c3e02c9010710f281c0010000c194100107413030700f5903040055404400000303090080d000288440006e0400c00c2c01c0c1182c4908041800441e14081c411001180c0d5075140c02113402a10b400c1c0340d01407488141d00071a50702d420600b0428804030741103211141c6e07064003505502078950094094a141c404c3d0071010031012500034882031101401125405482e20042010149a41a00034100094080e501c140303900c40c6054125280445c50790f03118982400b0200f800c0040e000e511008a4507980f00c0411406d1520503525005403800070590805517020078105614500c004001840c99140c101c4d4041c0707080f140d01e915031280c1c202c40741140301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 166741618 1250 166740368 166740377
    0xc020102061b0f1b0f16030f02150703020c0a0509100506030c12010b0703030c09052107210302061f0303050a090b13080c01080c0a0c030c020a060801050a060c03 71
    0x40d1008240030302102c4410915a0028580101580d070205950302c000714a81c031049660181c2c2101041c204490f55031820404000c00c18004403180400800303803544002440c0701c241c5c0c4249421504c1c0c03103101e8000300e4140e07420789844941c145006134841c03021804460107000c01810004052504c044268014209a41c08a540505240510000b5840107290007101c0c1d07010486200d03400c20060300343c0e0081614800c250703180d004500d0b009040e01e075a0700c9940104603215005001554408150619080c5011000e403282a001e146c06810b10806038416420600d400440040d80d0170309107070070280540309034295a0a680e0754041410b08041c1c080050000c070f01403500510000c1d000307600030908141582000b002c01580ca802c81d00043d0700000043c00c1341019610200200382003008211007996007400c1a0b000391601c1c10544001e40140f61110f0200b04600c2c6950007450301454814a215401234412300311181c80f074001070020130080c40344a0054580180000b01c20b84150300d050840d80d4141d69 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 166742868 1250 166741618 166741621
    0x6120612150c0f071b0303091e0510030f050a05090c010201090807110d0507030f03080a051902090105070804030b09060c0a02030712091e060905031603020907030e0a03020c100c02010206 82
    0x1140740c0d10f9003003040010091003041041c980410b0280c0383c0e040c0001001d80011400c20f0030761800070820300785640520340c2542410b01c21800359100c540e0303200c1540c03820382d5010800903031083d0850151000c0841c1041e118500310500c0851400b41d004240314000e40c40448001c0e4100c3c0300124200c03520030602038400c0600b070048000255021010303202090004090030042c0c3c5a81d103d140c10f01007180d1044030f03a0510318040d201010740004400746d2211010808100502d041c0e8210314002c4a002501400341c2d0703002074040000da0054040d40c01158100b040151519143e1500c50ba001d4016100c1e06941d105250000d42d581082c070044901d0310550313030f000d94240070055888524200d400344264082c0206004003117020b070701200800700241488400c51600600d0306501070100703581501b01760300a401072450560070b1f0407001030314412030f03034180c03010b007680c0d91317600300440007030001c40c841c0607040c0102e0360000306041e4000740050f00e81c0000c071032880580b4440700041c0c038600040200240541c00030030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 166744118 1250 166742868 166742881
    0x604020702030715050d1401030b04030810090609200406142104060f06050306010501051806190f030c05031009050a0b12070e0a060305150a06050612061215 69
    0x401428803540301030202c407225074480d0341360b80b0070f001e00d100c0c80000140007240701029070445e40118400c0a02d010030082c00703941580c0f0340c0b95811b84014005414060b0600109004a0014154000030452680200907403031702c4507000f801074076403692141c14103d000344110202604130011038044594640710b0110156032222801d0b500d410004101240d05a0080303813114115481410621803445588001002000780740200d08031040c0380c20041c00b0303070b000600500207030340c0001c05c890410104002604030100700c070b00018958403d4500c4c0051040300c09000401c2e2541140c44030200303962944047c0881c0b100315130100c40030301040782c4000e090520900300f00012145c65005640103501c92401281808400d00803c412601615407880309501040007088100e404850b903030340005c1124000d000e41031031516003698508141010820560901000c954140c9041d40084000c0001820490701c0f070b03c1c40300c0c4022101201f1260342d80540c0ca540b00b8030901260104030040ea0035180451480b86854a1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 166745368 1250 166744118 166744121
    0x1a100f0b030c2205030706031d0c010e010309060e0307060c120203060a030303180c03050d2601172e0b060c0a06050a020f07060207060e07030b010b0313060f0e0f0706080604 76
    0xd0f09080781c221403581000c130b03c544041c00030704080d1540e07450102c2c10070321904080329440740e466081d0410307400c0410301c806a40e80c02600488c02850910740802c0268150a102c401130001c0070301d40d4441d02c8000f490303800f040b080da00070541849542d10303481080d2a02c2a00c0c070702680300840303d981c1c0c4600c1004003440000d000b070b1f00100d0501480d205c0e101244105a84400c1e5038a1140c0059926a0002040340d5986900221040c055032400300d0407908044180c0e0b420b01e60410600450f40d0412442ea44054282c03020084d016941030b021050b02c640c0c1d90071520805131f440e09078a401a03c64104441040c06003814030403260f815440100174400c01d102a16110b000f000003400b000d800d50f13002c20002200d0800d42000c2c288032805004010b9440007a4680300341103449070410394030560001601000403e06070500103044490300c003106070313881e136400f400c030b2248440044005118525004484a20b554264890046515413404a460508112100565420303ca02c65200000d2441300018000e080c40e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 166746618 1250 166745368 166745407
    0x9091b060703090803070c140303090d021003020c1905010c052a030c0d0215060901030506041202010f0203041112030c0712060b27010e06010503010306091a100f0b030c 74
    0x10f850044509500c031031070181181d01039001607900301c441040130701000b2040c000002c03c80c08110020b43c9800d0010340428042c980000010303109110b5800c00403095400303901181c040d800240c059915440141c0d80e40400c1d0b000005007078610b586004003110354140502700300c4803030103840411080e07000c0680a554101c200b020750951418002848907542d80a000c0044614203c0b094024202e0f540d402081c2041c24a401403503580f182004c58010800f2640100e4031581054204900de00540b4603807070141c1c05004201d502c0c2d10702d82d200104000030b0110008203c010544211441c0e81d82c400020b401e1a903074044d84500c5541c0340c00c00c0404000c002401e9021080041c864240400e03548816000a034212a100c80e00340038450410401415098803486a43d0151450501d660840c1c102000000d0060105003c01450180d03101124024058500205000d80b0100420030207a40360521a800038224284580d4100600e841004141c1c090104184c1e4891010403004d0760800906a03620540840c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 166747868 1250 166746618 166746623
    0x50f030604021b0709060303020c09130821010906180e0601170f0d03021b0a0c0b0a0c0506251b020d0c0f0803071e02150c10061409091b0607 62
    0xb901080700e0f01030082c00903000a0000c03201c00071b070161460802031700b0200c3c2c802c50684100e002d541040122803035501c00c17000281d0041191070300d0716006500c10682104003400180c5806c038101c000240c020039030f0003c90589a2034440d80101c842080501015101030240c0c0c40c00c0754210400501c040d149440d01480b100d10303d00d040303a0070300360b40c2e02c0351600b000003494290f0b000039000180d0b245040a071550012a07010658010281040d06845400030303c1c1b01c50052a0041c040040c001d100d283c03203040d854100750341001c103607034060400e1500003102c42c100c81042e170303100096128481281c90103910315030a50302c41c0000c01000450700c0e030308001d0942d03400c0c1c1048820008004011a42909a15500c0c0290003420010b42e030300c808d03a041c424100e10441003450180720410700b00100589a100050425039400322401d619210450704050400c2c6541403900000e620b003c00009261140040c01000003009440745440c949483c030006448020301082500c100061020601403401c2a07402800b1250 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 166749118 1250 166747868 166747897
    0x10504030e0405130807080904181203021b0d08010305061e0a230a05010f15051c02040b13050909030307080f0910060b0a020d03020c07060c0507030f1a0601050f03060402 75
    0x10400d6641e85c03901d0b0400201518030f00400b00d071004132401c1c03620540100080d141c1e11a00012100d66910f101c0f149180020410160089251069440b001284800c40520181564681051044010400c0500b40310aa800b071280c2d41c00b280410035000301510541c01e406100d208030342d8652065602030b01139441c400829411a45e2100005681d80f0384150040c0b1000c600407949516120101094001e076400180340c620900020b014070f6034110048811502202c00e494200f0302d55080400c000340116440804144030001d2080ca09640010041c4140c034011192083c1540350031841e660759000844400c0701150000000c41c1040e070510364103e5201c0154801c039025007940c0d0000c4015147d007940403620555001c1042d03031415805000030100c2c1a101c4c5002c508200031682030543d240414440d031030500c196404010306008040c007030000030750340240304030070460458039101c00920000d11641003c120350307130003140c1290311810494200004030b483d540d0640c2c5400d0304110096000007107404040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 166750368 1250 166749118 166749151
    0x5041802041b0201050c090d0605040203070504060801020a110304060c0305180a0608150405150d1a0f06031203010503060a0f020d0603150b0f0a09020304032d11010504030e0405 78
    0x1070303031103010705458819940c810310144401d00501a0035503c0241ca5a03403000c0c010321090b02c0a494100c081e20354550082000309003034485001281c01c1c05240c1d001603420038100040402c190707105400038150450a9920030754104407421382c994503402540900340000d000c41e041c8801091081c0081c00c440511140c0d1184558043c00c00100c0302401c561244010a8251007046149001d40340c0c4d00d40c00042c10345041c000f13450f1484040c51403010218105220307180080e81d901c14082d03400408040e4510701c01a0b06100d0400035848a028501142d0f468420700c20010f99101c22105041a68100d400c00f80040c40b540c1c4a1401c5400034120782180c1400483e4240006990600309005040007140594442c141400b44414140142c070903807841c0341e005000207400054152a0b5440200c11108000001a02d035115850210b84080b0310300c1c0e004088850340c041400514000b02c0100b684000319464507010f0a00840401e400e071903040720f0240206074812131022013410a034002507407090381000b526004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 166751618 1250 166750368 166750373
    0x9040314040f080c040b060c0a0303050903070602070b1006020d02070b0304030302190819020403051f0605120706090f0b1c0f020a170109050f0c070c1503020c1015050418 75
    0x10401250f0003054240d01c1500403580ca403d1511952a11940c144c1e14207280407154405180d80342e000c4070004003050341e5440000d44040c070034803d40e026076912450941d580c1c981c9042c54400c6850540d004046152808000180d45000181d01d940d10001a0041c5c840d0914240e07802d500303a0001041500bc0c90340802c01c0000030001c4803100c4405c05c9803034803200c909090180c801e41d00c03500d42110644001e80b04100a1010074000140004c08411410386040c12140c84000b40b00030f401c83e9032116800c5001e40c0c21100c07903114042a01c109883c0302e683c84070b41e82c40d40d510b038100000c1e403030f4805d0480d040c0e420044030140e1800d041c1000e00281e511400410301c04100890441240e1180380c2640000724042e000184280c040e804c41801041400c0c400d0041c0d08011090750159480645008410302002940c3c00030408074140f01401041c0c5010200010000b500d000f802a5200001409040c05100b5007003641c905030307101e8070074000000402020f403582000148401020300c03940e08440d00bc1e1100d1803500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 166752868 1250 166751618 166751639
    0x1205040506040e070914010e1e0910080d020307030905010e01110d0207031a04050c0913020301060e040b100e01060c03020102090d03030b0102060109051b0304020f040e010605030c030304050904031404 88
    0xd140305400c2611a00d01641e00800485c070710f801020011001c1c00200350b040e030b44214140d520750422910303081c01c00b03a904090300d1306150b49411590041c003007401304526802510701036801c1700c0c049020fa4020215040f41241c4a12031144010080780810b0790234442ca511a46c20111500018140345200a5444449918101c040040d103001a070042800b4020408540036400000100031007600b0507040ca5a112501c070711120803011b0043c10712000007041000c010014911094026000b0080395845100000c1e200340105c9081c0ca400c10780001294041c02c8802d9940211003103016190410303402c0c001c04992800d407200040e0210b640910050f89165103060a0544851203600d0000309080484006424400140e001e106014548020041280354905d00c540c10b070151403103019500d80d25480000c03241950700d240550090300d400031107008000e0560002065420440032500380c220007030201940c0b80f19500a5540020403d03000c00c0c000ba001c2e80c502c070150719058424a05041e1940070144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 166754118 1250 166752868 166752877
    0xb04230f01030510020711120f12030c0a0f020a171305060307120507030906230106050f030103060c050c061311040209130905010608030d02030a05070c0f0b060f06041d0603010b0a031205040506 85
    0x40260480001c403003259108201c0702c550ac0c001c00610718210b20f4410303011501400703000007007000d00c6012402c6040c1d45109011a03e40258401001800313610844d000d6680c60300455043c01c0702800004001c43c071031030400180c030302c910783d19078a101c844404400300300007402003d00001c0505032a0070b28900015201e0007409054660302c584030b90307400024010344141003010391064090100400121030910340300021241901c0d04083c01243d8000b03251000ca1315031052092102c690301801301403184904521304205442c502a4070807600008070368040108030320071100c07525489006446000051080c2c4d4104404403401900001707030180d5a90f032120f05580c88480d480707550700d500204210160480f0302c80c0c0e13600f00011346004610000f45d955a901c2c0030505d0b81000d401c0c44ca1100001c2c1255494200024107401e0103448035803680c2e07030b41800d050400c0a440076000c0b02c0038181c0015080c2e050500c17500f1380c0208001d04400449165460300310840c54041e5204080100404c404501c4d03440c2c107030040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 166755368 1250 166754118 166754149
    0xc0f1119080c0d021f0b0307060c05160b09190f0302010e060415050304050d0905010828020c0f100c080103020d1103010c080a0c080403020d11010b04230f01030510020711 75
    0x149002e0a204203075901070f0026004064001b8600b8000d500d4940300003507c84180c910a0a00d41080c07401e43c01d0903482c01c40541d201940c8002c85000114940e00c41c80d001c1c00d400502682c002c19408104c51105010f0710b850b01442e4080e140e0312074104095849441e00004481014291924154540c0400e00c12000240c9048c07010607000000d03c01081020044c080702c01e00c0900c1c1190003a81800d00007000180003034031080c100440d49002031540000f0700d4141810441d4131604541d2081c070000d12940350307000c24030f102034540030705182c82c0c0c5101c4003070081118594070f07a55034090580c250b071b0810000d07840940c0305403a01c1e480e2500620480c2c80921446505a20603190340f650f03490082c100c0e00070344000300280420410b102050100007900000d040079061a24142080d041c2c02c4070400d02d00400312041225841814203c1c94000710781c8151402d40300f581c0c040f400403201c1d0781e002200b086107034084c88020b05982c40101c035400d81002e168081c00b1424854200009985d6050740003842c249020140c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 166756618 1250 166755368 166755373
    0x60108010c0809010b01020601090209010e09041412090310020c12030f010f080c10050c0f1212070206040c210b0406060f1d180703080406030c0f1119080c0d02 70
    0x10780304181d00700c800c0c0d5903c0390240c8001c2c003010a003000000c2d1544010320452401d0743d004240216076078000e40c800300100201401107a03843c50306042c20b4030302e00d0b461404041030307001d03103041d03034103224007a108840d401c400180080c14029408940d501c001d5000c0300d61114240034101140d03001c0003800000b10b004c0c0300498000304c140d504201000820041c0356000010940c00020300911a44500c5000700704003c240c1425601c50f00581c03081d80c1000c2c245d8064030712600400078050703004e040c1500501b0880701108400489a50340d58403d03a41c0b000c040e20050034149615034204000ba1188141e800c0750706012107941e420300519903e1458a420070340342150050346450045c4105207105a1090051a83d882e4030224084042500401e910006d46101640448460f06124407042045641c000756809409580e80b55a5140001d00400a0502c400c001602038051031031344600c0345072281210b4540d2400f034182e0031500300c407a004801c61941d08450855043c840300155070300074443c09000b134145401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 166757868 1250 166756618 166756631
    0x1080606030d030b01022505221406030712080409020301080d030b01020c180402121203010f0b07030906050901140a1106060a240e0d0606030506061806010c0c0806010801 75
    0x8050030001150b01c4401014035010030240207a90000718000200940a0052043c4001ca4140d208001864200940044e1601c01c0750b4041a0350240c102c6484990042c20000c0071404040382c441c0b01800d0f40e070168183e0014406207c5005800c01c0001a1407161100600c2e05039900300791400c0e60026404010660001031074a5400c5400d4003804030b101c5800d1002c7d0403021020350000f18010010100291040c031401d001500715158501c05011400c40d600440c0c1101807182240f0703040e40d00c2405541203903401c00c400043c8010b944410303940c8035580f40d2100c425050801800700e4003600040300f00d604004003080c03240c0c0741700000001082d03503080940d03034441c12034580c940d050701e0b00d0030217041107001b040001020001d41d1603002c00c996410701901142c0240001d070000446d580c0e0040e0544035031103890041c098041180e207511240440f803050007074030000c3c1c0d1004d08000740c1740040c0313080040c040d480c180022002c0d03100f20007040b051407041d036891103296119038650303141071426000882260f55031174 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 166759118 1250 166757868 166757881
    0x1141203090f120c030d0f020d03060e150111160314010c1407110d030921050714010c06050907031208090a030305060a0f0e0906240d02060909090d14070f0209130b010806 75
    0x1c40049c501006080502015281c5200c056030344400801e0780c0400056855240f02d160321031403084010321188021510700008a2200403070b0050361b8842200c0041c034202501d0401401030060204849150311021500380c0ba80446100035800304008480d01113620300c05840c1d50740c0f20318113100c81798040c1d904c90060382d042c074880a0480e4200c07031a4408030852030b0081ca002410004100b400c1c2e0301d600102c5403000a4510045c0c03030ba650381203002405d42d8208010010359100000320502140c2c002c040044c0e10490a69040d90b650740141c5000d0742c583c11104004020038040e420003a000f14010740b80d020b003150303079051046002201c3c0d00840035040d5140188024810208550340d080f10420300340d000091038002c035540b4496402c099060040c0342480c00c3c4001d65a03104c050750000500540642c3ca1454889206504c4e0001000ac80021038820785042007900c2030081a111001e03801110000001c0f420307001c01880e0080280300a000c98038a04105000414251105008191040090040b802d061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 166760368 1250 166759118 166759123
    0x30206090d03060f090903050912010c02010f290102030408150402030c061c0b0303131d0106080907090506060c0d021b0102030703080106030911040501141203090f120c030d0f02 78
    0x507030241d4109400e0031400e022020215032140215201c000000880d14007502d416101805a680c50a40c009100092585190702c1074101c0542e0020690081180500d1948102c040f19483c42d540c0410741d400515a18842489032440b81841505004403130401d6070303550b501c51a00c107100c41203030070750a08003090000310b04007002042900801116014180300641c540030044000654204c0e40d00382e01c1d151800f629480502c200c56405010500741a20703551030707034a504a1503400010184142c2d0368207000081c12407080a0050258901c440601000b615002803440034200140010354000e00400009910180800404031400b4041c2c02400d4842c0c2d03010580d5241e96035585c1f0803415900100012000603510003117140c159417040c18002520720349410103108480007441000d403c5482c1600210b05020107492020020f50304036050310400070b00d284407580b130f8000c081c40302c0c0e0421841245050180f8228120041c540021070488480c80100b4001900d403c40010040010070720f4000d03100703a4590705 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 166761618 1250 166760368 166760383
    0x1005040503150105030a080d0603081204110d0305090420040806011a07031211120f0603010b01020705060f071a010b04050103050a05100b0c01060f08010e0d08070c020d060605060703020609 83
    0x1001c0c10b8115807400c40840d4840280c24001403010703000045000c000422684400090358004c65955203820080c0e0125542c1041074500742c41d0300346100ca50142603d4180c880c40e007441d038540d461904021801c8288005054482c4810418494100ba000e41050201010b00003e0548100622503545411003204601008861003858100c3c02c00103080800d40046500000c40069100001c4100c04108403920b9805541e4040011607441c0080c400c1d802c004042450242d101100200002011305006a80d07a807001d10a42d0380102c000e10006c0b00c00c1849030701510041c2d0098800104100e2444107020200030260001c03c05114080703014004c65a240c829071b640801202002c025904101c00c3d0700320a034060303220300a06914001690503500030b013904000c00810b4519114480c2a0701c400221b8068001442e09803220300c82d884003034403140e1107003503503600031172042d141d83c2c18861aa80034040040079185054600540f030703103c0060396441d80030040101a0181d40a00700c2800c000d10b038075042482 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 166762868 1250 166761618 166761643
    0xa030f2c06130219150806090105060a020a110604051819021804050603031312021f0f0305060d080313030e0a062007080106030308040c060513030210020109021005040503 75
    0x4258100a071140304806805080c40e0100c42c40c15401351060001d4252160384e400007030000da03441c1e00c141d80c601e0304140814019082103900340c0345a030720341040c440f0500500104000507440640d1800200d1048903111714480d5010f0301070351a280d05d03034011840358041c2210040c2840080010401d41d98001d0001c40700c3c0d145403200039840c20803114802d9018200c542c8236148101e950360702103140c550f000c00c200c580711030a410501000603039400180c0e41c2440f0003007041e4003c48a240580d500c50744031508018507000c0c2c58a400c0084600780c1011401010000c040719000b45451003c2c00100708500c02941c45001d0baa012840d0350341c208d107030080c8100254800f06001d407024030020300580b900008605c10107051841d080507070304280c0b419a49031113520b603c880c030329510301f00d40401495480303462180300c3d078011030802e89103595821741103030607210700b81d441c0360206180b00c000c0c0018075186001040c0300525200116030046590009900342da04113130300c540800e5000804100c9420f062080401090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 166764118 1250 166762868 166762873
    0x40e01090209180607091412010f0f0c03050112210e0402040b040501020c041401121a0108010c0822020906060c0d050301060e01020304050a060c081902151302150a030f2c 75
    0x902c0c19150b02011f030765114640340300d1072440d144901c1944095010342c3c0f681602e14020701c8a60b41e5200100020610362400078002402c140c00401c1c40c0102200c0d01140580c800b4100b6070b2803900d09903510b1010050001c0d00100054895240210740d100d00140016044041480c4d94807403030f2000180c98a411450000d000d02d040200e03543c0d07070407518420345044a0007a640c14100800038501881042e85a10296800b6955203001285006055012040168a43d00c1d500c845848602461000d00004c18502d10305201c020820001418460062074000340041d10041c01c01105540450404000001c2c010000d40080010804140d101c000400c3c0d208080c009140703014200804034080048a02030b800c01d104081002c51704108910703003203911129010305221203841140e180203444140d1a03800c64140c0503000c01080e09922102079101c2c48030341c002e0400c1410100d0300c0c03001c9060307041801c1e010241a62030150f031800307454600590500484800010110f0107403203000280c08a04ca105a00039035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 166765368 1250 166764118 166764137
    0xc090f040510050709050301021306271206110a0806010206060d031d0d02060406050d1b0503060d110406030813060f020619090c0b090a0b0a0e040e01090209180607 72
    0x41d41c0818041150300031032402140982d902e50b400d0f0f0b0b02c100c0e99809a03815610008503103c5400ca80d401e12401c0e10f101c0d60341c1c401d28500e811100c50302042240f2480b1941c1c002c0701000c0010a5040c50070125040c407035a80071401d20060030110809420a4000f0800306405604002241d0703814000c17541d12500442d01c92103203130341c00e071002031901e450a007440d640c0300036640c20b4a08a41d42d01d0b42905601c2d0740281011703501c50f151000107080b40c01010701c80c80c40074100888114000031080b000b038040f428030b540301070642d0354200801141100b9a02c054401100c00c03407a600d59521103003d410090350251034a940d480803140705940c06805a03520050401000c3e50010302c0859011504a030021103071411300d03034440f1070034800c0801400840f40003031814034070580015030b525004014007108a000c598181d181d40c1e0b50304502c2541d10500c400000040c4040743c00301854076207a0b100306084203480300006203480c090340c00300b01804000d80b042e0b1004e5901010403c20f00808001c2c080d800701d131610340074692 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 166766618 1250 166765368 166765373
    0x2030d020624030a08030106090816050f090a09080a09080c0604060906142b0e0c0603060d0813141f0207030b07030e010f020c0c09040b011401090806090c090f04 71
    0x900341c64510760607038920003003040e82d400da408016034240e054220182c140c0d02c0d40d5510001d4a0302c10070b4071a400c0c80b4001e6490548110074109001c008440d00500480c1e50b09a01d00c017040003198006083da07115542c6e440c0c1000205140342c02a00c0100100d89910104904001200b4a00031002030801c0c4940b0042006010f8140e01046410890f0518180521004480030075840d2600855504001c2c9a4400c4106903412042e414072241106000008010f0310800841c11030b242e00080300c020350095400c0020440a05081c607800d500580541c2644e4140400c90801e10600300c400d612076440c2c003403844100c44d100e10707155500027180c585555910a030600420406911040b80d8800900540710040020b20a01c3c042c3d00061901d0704100020000c00d0354006801c0d000750040c0400f074041c1d201b110007a0700541032054840d8001c03500b0200c440141c3e840c1c42030456041030740490703103410441009000a114a01001550f01804080000d465095040b0040c08064000140620014243c50062001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 166767868 1250 166766618 166766641
    0x20913020313060c12050901050f0703092f040e0c01090e0f0105040b01030b0d12080109020c061f0305030a0e090a0207200a150507061409030d020703180306020702030d0206 76
    0x94050b0f001c0382c0840e401c3e90a0728159502c5004403407441441d41803008100500f00190710036441101d0045180226444008088040701c4800760300a003114041c0030300c8680c0d1a1605038501070f240122a1540e00d00301281b0105081d00c42e06601000d507a44011300b10319207580c0024100707014000f2440d82040c0d43c60300d00320f08034041d071040c4580c50080b41c0c1c0d441122205d9219420842d4441c501801c0d03c8040d1451b0710300300c03110050390302008000840d95000496480c500e40200c0305158180c400801721a1945030030200f003448040ca02c402e45441c0c694000000500c01d002800c48030084da111041da0541107428014100c100401680149104101401c00103260781c04500e031081c86078494101c10032100020400c4412142c00a281d0303007182004030030800d48d02400508816110762001d03c64468420360030b41102a06654591460300248424a004806035014002c81e500070f240c04003900e4010404007404940c80c1d00280c580740e40008541e02581030401541342c0e805040d03c0140b10600d0310f10074001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 166769118 1250 166767868 166767901
    0x11403120a05161103010c0306050a0e09070915090612021e040f05010b270607120e060301090204150e011b080904110c120906030c0d021c0209130203 66
    0x12880c00c40441e002030420320510646003014280c48540d01c10b4881d9007003026205804011540c4a507082c0094501c01602c640520710803254041c16001005013080c1c81c0c500012402884142c0038401c190700042d414100f4018003401408164200d84a1740c14150807100707580c4590000c58a07000440740000060300d0707030860807000140c0301500790200b07903046001401a100340d03501c0c40011406d010000ca10703401c0f9003005029401c41002104900021300c40182544050394400d558064010f00c0b022011034001a09240bc1c02031a24010756005070a5000490079002030308000b425541c01315040c00600c200b0704200c1100b1540f8203010900035028000200610b04803032100e000005440344603000c000d10a0180c5031140e400038010321500d80c0c800200c1000e41c0010b4181c0e43c407445034501044101c0311940490310000c0380500f11519594580251740032903070103884a0192240e08000011444600010070280742c02c1c12a405130340c85a01c4410054010300034007a4207481031040060106500300350340c118 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 166770368 1250 166769118 166769143
    0x501030b010314040606170a0203060a09050a17040f0803120703020a09120605090705060a020a0b04021f020d031109010c0b0429040302101802220e070806011403 71
    0x4a4001403600040b07003c0e10340403440300d0030705071a40d09010070007041b40c020a00352803211501501f80c03441001d0050382c405c014040607415400080c04900c58a0326a001100d195019004850a800c1c3e203698100c586010902d000c2040a0003260074081d0802c480c1c0c40e03000030446400114200a085140c08500940c060100020f0590018010900d240102c14000091502241e41a200251400d024022306000c40c0d080ba00c9015640011030701c1e181010039079200c1099503000b8100303d03869036500440c0d000083e1007aa8441122403041c2c541e2281090298580381c5c3c5640a4003116000080190070342d944840f0f020302c120b00c20f01c031519160f40d00030541c078401600416040403a44036420a402205d5844001e4500c004034443c41180c3c0d1505558554000c81c880d508642c000503203010301c03030101c8036210705100e402d2a011500c0005803600641d030001c103c82d06014110131440304c8030f46000b250290300703004020745c00100080018110920902d40140054004c4034903e0f010180000e44492032214075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 166771618 1250 166770368 166770371
    0x2030403033e0106180605180f010324021911070b07033c1101020f03040f1424060907080718030c0303110d110705060c0a0206040603050103051207030504050103 71
    0x1200b4402009420940003010340f216203004910040001c0d00c064075550044a000d5401c0c3c241843d944121264a03d1050001c040c0d40410f90b42107941c0e903a0b080c04104406010400404070f504851103240c0b00411003e0908007074608007803024100602070340c0d03000c0304a0142e42c100c2c0e4410880c251580088868190381460039000c1d956103420a207054212441c0401004c201e941100a2181d558100b41f0030100a291908e40000c00fa0110b6142031f44560903074064445410b1010034002402562520076891045141c01546545249841c6c81d0085000c507111440c0c03d011410b0190b003c4106030960024000d0361214480d1801d80000341010340094910b0303003004000c0b9004680000c82410910141d540000011501540c0f42401001896560343e17400041c021411840d82c1640555909607000003410301411140349800d04202a81e0880da001c102e86020b00d0610303000503a01e03480100060030031030320009030a50460030034620f04a591107001001c0c000802180000c01e03040019101190b4003440c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 166772868 1250 166771618 166771727
    0x120305241f0c05070803070506100f0303050918330906010c0212032b090c05010503070c0b0a09030e0105180f0a0504050702010b1207031a040602070f030203040303 72
    0xc02c507040c0040100141c014020b041c800308504030b01000030250640a2011101c10351200148032811007034500c104502c42c4200d41e0200700080c00750028103003040c8010600120a548240304800d030400c1200d1900900108a40501071807100c141624102c488032a510340801c00c050f408203d82d1000500b60324180851100c5d180704540d1141c4180d070540c2041d806803601c50030040b90704026290142c2e00307080d1424407c90001c0d49601a4401d03000416007111100e0005482e2100542d8550b2001d413011007000341440380803000c141041e811a014050034180002d280d601820010030b81c03a80540920b041202c100810102030f5014600f40440300d03c11140c400154207901c000404d04001d80d4400c80c0c000c0d044c04100302020307806500c03031803e041082da100c00740000c0702201d0548401503801300403c507074104103180c050081d0080082d9406482103400524104641c1ca4201c841424500101d0042e8000078040c4200365001182040d40c40d4810544924812a51850011105059400304a0090f0a003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 166774118 1250 166772868 166772929
    0x30c1b0b0c0f07080a0503040605060f060703030903090b04030c090c1b081818041a010b040e0603010207050a05070306060902040b070b06030c0a0f080606030f0619020712030524 78
    0x4680200da40044c0d4a5510852000b01800c690421a81654201c0c90000016441e05141c6c904402c0003000800c1c50385040100c0e03800360010710b1030741020360400c0702500000c103965103404010401b440c042d150f102410ba00d0020f207181685c10081d12201008407410200d98400380c00644150f8090b80090507c3c1c03140c3ca8030501d120702213981108580c2c0101c0059055541004000d82c15001e1405000c0080c59100d151840c808014801c0c482c40300701002c1084100700200d50740c0100d036081000140054030701115916524030301507154800303454940140307070100108400392084c0710082c0003400d0103604041c0b03000c05920f154040c00d0005407000841000048540e0390620645408141c01000902410345810300030071503ca642c014020355100c1d04006c61102c0c640020008100b40f800740c010421a82c490601c1c02403100440a500e240c00d03000e20120001420102e284101c8103a80d503000181d46c40e2000a00b413000c400d1002c2801c0781e40718032070200041d40750f8103641d189010a05501e602c0005441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 166775368 1250 166774118 166774147
    0x801051210060f05180606030c0a02011e05010f0608010803090d080d06080615090903090f0d0b091f0e15100e04080c06100807060f090e07030c1b0b0c 66
    0x1d080650058903107140030403204140e40158050301c2c41618403501c0740c500300074902e01380b000079180740754800c005000290468000100074030a030040d501c0003013000c1007030308407000101e03440c031180b90035040c1c4800040c480c081c004814407001705024a8004d44551406451a88910904100d41d020303092100120b01844000e0303084480000e00c5607000c0262076940d82c03009803a0103090795009202c11441c3c0840a0a00d0f04c840102d0003000d111000e5494124000d04008031b1888c5612403642182422456101041807042281d01c00c40703c1c0800303040b0201040383e08209002245401c640000d01d8480f000410f00d10000300524809682403072958192500e80d041540704025500200d029500e140803c010450800d010300243c2521100b103a4858030303031549000b0014401c0c0150580342e80021400c2041e01d1142001015410315820046040b80e11905c109a606508885040c01b082c0c40300604901140e00c001c40c20000c2ca0240e1405140c81115a904441e0460181c02c0714901c182c013040480801424 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 166776618 1250 166775368 166775383
    0x807120b06130303080901020f030604052503020c06130302030d05060102030d060308090a1205060c0703051207030b1f050a08090c040e160902030f01090207210504030c140108010512 80
    0x107004a4503003038501a601101c00c46030004400280909000c81d061401c14000d0f03444462040b03078807a003103607514024800205401000d0660f08520075042c851075184195528018546540e00941d95038292500c85240107009040070904403845071101c80401c0e804019038001c948155404030b000c1d194200102d00e94052003101e43c0c0a00e107050000802c00c4042d0004142400d000d6904900d40d599844035024803002c0c036440034000c0d03000304001851040003080200356140c882e0401a045c2031520f03441290700407084445c440400d41d54405d0100c0c1d0303d004c91000c00c250703d00858540030140c1c10303e00141a030180000a070309014030740004c100c5200050203102d8440c030b00030b40f0800030210b540c038480b0740d580014612514007004040b004100c80e07409000302ca1041c3c43c2000700e20107603442c2c02e1560009500c0200141c4070792102c41218911000314010140030b580c8541e40d01501c99096040114202065501a00f20641213900c601d1082c1d8101500904481007107030400224400045050b091801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 166777868 1250 166776618 166776641
    0x10b0a18200d0c110111090108100b0d0605031506010e040c090b030405060106140a090302060f090a0306020c010f02030103120c030207030501020d0207111002060a111c14090a03080712 81
    0x1008a120800c00e0201e07407110510000715620644004c40200c6a5400c852080501120103c1c0170030694226500920383d0359042015000c1a00b00a5030303c14080c50340350070901c5c50440d00758071020108001c1c0390400c80906251a000340300411400c2000010741079800c0e02071100c0c0501d80300c64004414500454882c0002c005002c0407580d80c0c03416281881c2c0701c107030901402d80840ca14a810002407007200c0113403415580790b600d540018a0854003041345640010500c0407901c1d000b004207041c1a00d811000034011480750070007523252580030f0101800e6603050a02510854410f01c01000400c000101c10150f254417401c0000c50b0000c60305089040407002d8101410960000808030000d06c80d0341d0003040c40c03a00a030000340404d8510070821000ca4804070f603400060380100082204c0d80d145900c8488080d11386080340e4500144524850f00c48441c0c50078400c1050390b01d91404814a1030413008aa00c0001503016180760744250394040e22060010380244108800c8244180c4500f4190344032280904 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 166779118 1250 166777868 166777931
    0x9061903021e1c080421061424030a0f050307140d0813030203030711071716090204050102030414030a201005040503030a110102070209010f08010b0a18 67
    0x4002031001000b412401c0d0315000303020100c411007288103044181031950f58080c0010b40740c140b60011440d40c010f440e58030346044505403940d03c0001003a500c54107582091440d0311f03049903d07060300242c0e078102151090204082200740800c040b5580400c94810041e0300485c3c0e032080440b181081031543c0100c200c02000220a501c00d060031603000070344088500515079601940d9545c107001000d100b0584217004016034001c1c000700d020309004004200d0902c2d030882c111851581e43d085a0070742600300001e00366854104001c947c242c000780d08800e802038080404154546803078440001e640e4881c9100d003007085040400100f8181d40c0038030407a1145500701d8813515007a54004184c4841c1400c03160003038810032240c03400b1400c05003d1000e40c0c0880740d008003d581003894020702600d603020200e01e40340e015542082002c0069407942d020038083c10090750440c1e03042e824010284d08480c100b5401c03e1250544c128100004004029008801d451000d0007140200c2482c80380e16841c1d4041c114202c049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 166780368 1250 166779118 166779139
    0x302010606110a080310120b0a0c030c171e0c09041a031c050d230601020105071b020402041e03020a0e040506010303030b040207020a060302130e160c1401050403170601030b0906190302 81
    0x4411234507198000c003040c0300e040007905000b09007541110003e5900002242c031083c49580c2d40480041420361000301c00301007407440030000d40480380a01040781c4e14840c5400c00f041082c2c503401c0503c600c4082c240c440184824403a10f08000a0381d5030b4120b041e50796941000101202c0491191082c0c0e0303000448960203000c1001d51042000d502c100d105445031102e011f8800044003584140251801030300151180c5281a0152400c801ca5074907031071050340c22580802c000941d1040742c1c1d00980b01c2d00c82280c01c4040503815403040001540803540290f030f20b002e03000305000c041140031402e1030460b03505040019004a600c80030a0290240e01000385d840140000c0018141e80c043d00100f078007848480542111a4945d0040484918261000804a074a2140c404450341c0034904000b0140e0080154130170203030326552411300b03441c000c803412400502e00701c500503400243c0700d20180d0040424241442116507000218418001c02403d00f4825401d90042c900700900489608014580140442620 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 166781618 1250 166780368 166780373
    0x1020c010b01030b1f050306030307050f0a02030705060c0c060a0309120f0306120f06020a0e0d080a080709052d0301060b07050f0106050603070c170a08040302010606110a08031012 79
    0x2071408850090209081c140d41071042c2c038150104c4800341081c0a00c04d0158211302c5011107003a0001444507030503110801c4644e000c04d100700605c85020940600801002c08280b0605040980c581c0c00240110021301030310011410108009403400d005035402500d50f07407090400c4001d0b00c505c05020740004140350034130688680c40500e400d6204003a8405200d099a2542d01c0c11081c0030f070030302c00341038144180412000204a60010301c0310150902c2c00100b0840400c00183d101341103960f00700d880600c00504641c1d2590806030321940021141000c150080c03802000c01c1950841500020456070803240b006484d50b03002d8800d200710030000d07000308011612581c0a210940c4500d0741600c440c8210046003602c52014000d040c06c3d0388014000e0340c25901c0d1180250340205107004c080f1414540900d421207a545000042d101e0550543e481c0d02090030603040c003a003102c0c1c0580000d8100034540c0304d1203d4101000030039001c19644890035a0340e03584d0b15440c407004085150401ca5110201201c0c5406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 166782868 1250 166781618 166781621
    0x1903020a080307120e0706140d02090405070903060c091d04050f01050c0c07050907020a1b050405160f03050601022e05070507051506013507091409060307090c1101020c01 75
    0x108030035658040008481d4088521b585407000c0c4100380000b01c900b03401c41218401c1c90017500084c86016000360804001200003400e681040755104001000c6402c00c00a10a0602400d80903900a0411b1851507041c4400c10b10010080c08482c00404000d174041020031000f0040f003480104000c00801030380c20100c8001200703610100030400300d481905e13000f00d40b0b0700c0e211107924040d90103134000b040c130740d0b500381d50740203008441c86413800c1e00940184000503191128001d4510490413104101c4400c0227624000e81860821105881014500400c1250590300001c90a100000f8807048a0110b01c20b031028a00040b2008620b50487d0306180c02c1c4492240c1080180903294030940940d16040302e50030646008401c11560240003e4581030708100c0000c2218907581d0301c03030340c40e4400e680040410300f0072060001e09807244000600d094501300111994082c910100890032101d60203542460800240d8030900e03800303105100e030740d510544881280504036918040300c80f4002507454450703c440860 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 166784118 1250 166782868 166782887
    0x52a01090603020c030405040509031e030708090a020112270b010602061e070e0a0803070c030c17030304021e0d05070f0f06051b01060506040806010f0e06031903020a080307 76
    0x140480c01004000c6403190007402a5104d4220500045003014039140802014002c081c0265006002c2082200200000c00a50803103910300c40f401036950f41401c100c0200b2852006003144802d411680c1c2400c010b03230384880462038569092030042071194a40403012000b007141e0b89041ca0100c0e5041244081013843d1640c14100d034019000d9400580c1c8a4001d160a400c400c1c0c0d41031600e800f0500020f40e050300481c1251050703240034012402913900c991b40d59165601400c000e403400324901c3d004000300316207c3c284801a10b522465101540b00070303240b01f55030740800f4000074451720034940c4600c0708050000b500c8481550007004440a003500d0305240d9180e10250140b0b41e440c00c200c0002103010310f959007101c400c4039031560300c081c0307469107610480708440c01d0004400010354a40d500050103603581da0151025000700070180c00b003945080c0c038400305030b101588036043c0f0a004500700702c156903002c0303030302c030303807441104241000744c1010340340803170500311a428001c040c00000f1090051a580c40395952 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 166785368 1250 166784118 166784203
    0x70506040203010f022b020d0608010b0a14010c11120d080a05010602060402090c0a02101109040b090106093c0602061503060c0d020903070b0903150c0f030405 70
    0x4c00402c2201c080b01c800782d1141c414603221000020203511440d030b944044224001c07195110050408450245610a850f01a07204000c2c6a45031501103111345449401000200301031104c44507421040d000281050300303041d0b406401006030461441c00f9403100305503003203403c0c004001d44030340d001000301c082c040800603640521003c0c5010000b0138900d000281050213550004d080d48081c0c0d03102240d003a8540c0c806907200007103008800c8580c20707000b514002e0200c101820a182512520b903901400100c5d4406104180300e408001d00420405d50020003950546204072011004104455241c0c2c5104002d40b0300071402890304c0004240126103640b42000384c0f02940d0a031401c5440c1c141d41d4545004140c4051541a0001ca02084518241d98018004900b1358035001d0308003d41000041d040940c0e43d417200c0d403007100018101301180740c1841200c1141c50720b024001e1050a01548030b2000f8082c0c030030790342c0d40918008041810301c0410000c0320001c2c0070402840d00000d50703011440403501d0048001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 166786618 1250 166785368 166785371
    0x203130f030c0b07110405070e030111090a05040b060412030c060f0e060f0a0b06040312020d090311010c06020d09050106030c0515031f0b030705040e10080312040c0b07050604020301 80
    0x41190304400c410312044035000001100b51a05025000e24550f01180089860000b000315900c0d503034a590050601c03400041e1100c82c81c1900309028107007500d00808011400f40810031008406a8903a102c850540700c042d0350009443d40c504001c140e0030300c00c0d0b42107400e040c404407000504241d0700114039003032036115040c140404ea04140c8600305460100c003100e1065007003a800140c50407a208581903012100351030110354849803030302054071030344030390420303903050840008005000380c040080c4200d0442e28685145220b00c2c54403561684012698682c1c100845c29881e1001c1c05259016190341ea000c00c1400c0052900a20f0124000c00186c48100c541e0510300000181a282c0309200500b2184104440e610359507480074185a45011065249281d4040440c049020100311000d50b114214940700c6550b2182410014088a403000741049031102d541d00e4140220800441a140d050b81051010501900d0310f02d0569a50b1205800c28201c540b00854002c0030b2001c000f03005030199000703600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 166787868 1250 166786618 166786657
    0x30c1f030212092a0f090604110d0b030c030a030206070c051c0c02010210020301050109120f08030702071703040f0b0c01060b0d090c1217071401020301060c050c01090e1b04030f030203 81
    0x12001240c10b01448001e030700c00c2c200103e174042c0b4100485040e81c0464000c100007902021a4900c3c40309800170311806000036074419035100c19050401079000030300d00c100d00800340c182c4190b4009680b24401418201000344000364003041000c100030300e004400c0c488842c042642c4c290381008140307174540d03c4144c0c0184144164121a0401d42c802c8038182c0e041a541d51144a081096841c030417101c0380c604641c6c139281c52020f1004602150040c50054580740d000c1c25000c0d103000725030448800302d0722603140c564004110802141d01c0c40f960840495000420350364036002c00000490042a46502403032007000f000440c20120307203c2e68428020036101c2e00c1d500d0040b035101e03800c3c0b040303100700100001d0121a0075582da480c2d03040b10304050f0903150310403585003074001b030310000c443e0a98200381d0006001c20100440c100400c1414802204890028680241e29500c1d040710300a00060142c60071300903480c1122420034940c034400c200d4001e5504130b03440701500c1645240003540c913030200c103018100400186 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 166789118 1250 166787868 166787923
    0x4060b030f150102101a09040807021201020408063402030c0f060105060406030b15130e0c070c0501031e06030804060201180c0303052104050105060f030c1f03021209 73
    0x1a0402074118061340100007000c030366a0380d4002050061440007070703c0b030481303a815482d5030341e01075403449075105510b025110b40c1c02d031041c8507516030b03c2440c00358280d0061005000c1c1d09800a2803c3d072081e80600d2500340302d80d403030455001d000d100e00d03001240d0b52003a02401c03001d03e400000a05c8682d100c07030110751400a02100301e07a1a000e0a00030075a109000300f004000759403103600705130b400c0c880c02049403503051242e80c003200075548207a40d044042521a40d04118804000b103000da8004a680c005520300801662520281c05aa020b124103165540042c0040000d28620882640645c01010030400c1e4490601c2c1103103030490300c5044010f42c2001800748981110842c4270641035070080100d15480d065541c15222078214061b40081540c4940e00405030520384d8030824000d078000e000000380c41c02d00200340301c10420007643e824001c0e03214007500040b503140c07404c03074410348100e505080044410b0600210080e00ca002c0340361032250224802c0c017210400c041040740020104058a20800c034019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 166790368 1250 166789118 166789141
    0xb2401030b03030706150b0a09060201110301050f09180109050303180705180712020d0203100608010b2a0a0308070e01091401050a11070b040f080303060a2304060b030f 74
    0x1d9081c54058200340207884c000b4000e50421890040c22441602c0072a4035a645400540c0000e20014006006128104481c9230284103091039070321f9040c02c4030f14643c144170101e02600c9000e10302c240541c032040d000a1008442250460302e404151009000c02c0c481401c0155480e0400c3c0e45864041035030302a08032500c44001045401c652010301400c5040c140c600041213405c200410280501c500d9660222110040348000c010101c0301c20340c0180c90b4200141c0e180300803a42ea800070b80a0081110060042007918800e80f181038130000d00c007040140b4045510502010442000080d92203000108402c1540101c1114407510f103541c0e40228018000f001113038190f040e403081c8c091001011905047e1540f28000512528a40d82022803c040a0010b0b4074603000c83c0d6803060f1203085021405110000c2c41c1094040200040d400850075410b00c1000680c02d01e285125400110b100b07041c51044c6082082105070071500c0c024000c000550341c0d004008440d5004a07119040d00303222800248580106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 166791618 1250 166790368 166790381
    0x1a04050a0201050c0109020a06090603180c050d030203160c0e090607050d0c020a0506070e030d0302120112020a0f06020c01030c030e150a15170d390b240103 69
    0x1080042100d59159001950107034403c44044016540395220080562140c403104002041b140e030340c9046c0e0524048006044800b59682c0c0c20546051681c04404500340300035035003c0e11030465580344907d445180a1b4614891280c2c0e0b03049502c007403484401030000d40d1080d00c00f15204520162655601c0d00c0760703079488040c11541200400c1042c84840380c00011640016180845401103c442e0801030b19010b1400340100d0703521000840d401e0390356210b414140a0641070080904081d81880c1c00040c140050160501490741510f00d40e0b1840e2041d555841c11407002000840d001c84965070302c0749002500c550421100ba4082410804a4250340f84640704030b600c5040820040c200d004400c00c1c051041d100054140031f10591240a020700b4004011240d100400c80702001c6d1301c5000e5040c0083d82010480500482840040b290055803010250500f2382d485005002c0c10001007041c0340c20040040d40d0400203041c1c4500e00080181014116110081c80054480304c4400d804500c4011070680b1103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 166792868 1250 166791618 166791623
    0x501050703050d0b06040519140d02130b0604120b090705010806030606130e030c1501080f1002070309030c03150e0c010909050901060e0c0a0807020c06041715010b071a04 75
    0x40802c10b0362080790f89a400b0044558000700101d00d07140c1e8500000304c9040c08181c103000c1103081404204940e04260b1204118400141c0300501413403160f030001001210300a41541c1d0842d29800c403001a650754030211000303013084140001041e585810b1600b070700c100071034000c480d6108400002c2895030181142e1481980c1c02001810903580c0c490a0103210b9408400e0b00382007607220202e84182d20710030b01c0505904890100104401c02e240c100540780302e581a880804103030003820403c0c80d10040850b43d5005c801100c0070250b550156468210350351102540050f0168046079004020461100b02a02d20640d01c1d500c10320000d0340b1400e02da82c0f60180381c0e0481c1c0c0440c190b0f507410801d00901c0c0d002180c0c4003149100001d4120364a415921000504440941c40590009501001d0039000014543c01c420306100800245860101144e20b0740304a009000c0c035000828440d030031060307081080c40303400e0034040c108110a594074841407003560002401202c0c500c030300381000042d400c1100d460038400da8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 166794118 1250 166792868 166792877
    0x11030907030308131203020703020c0405010902180907020309010c1403030403090501021c02030a0c02041d0d1b030c171e0c070503010207050309090c0c0114070305060f090f0a141905010501050703 86
    0x17110040a400a601c442d5040b025402403008005869442e0703c2000d00811181c040035903249050401e00041d11049800c2510440380007080c402201e5000060713400b680002c0c200700e502039103241013541c0c10044401d0082e0311803100004020030940e00c50091000c0f59400e13000c90721414119411400c5201d071305002d140043e8018400d20180a205158a40d190b0780040c10005030550501191020076079840d03080280d591081d80c40450141c3c2c800c101203511040c0e199161401d40e00d9039070007060121400c03000707002e0340c45c1c2140d0854522100ca0858500812980e034003020403000c101c1115240d0406070f59a20580141c0c0381c0091030342410f0084500241d07009000d1450605e600080200340440605842c54041d0203100000110f00c0900c40c1c062400308480303450150f45071404008060342c40c014031050160848500c004402e448810701d10360450484076681c071441e95210030300700040c510341000040035118001488402c05012030398040d00f800c0c07a030080c0400c0e0f80711001941d03144644600100043c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 166795368 1250 166794118 166794143
    0x20316030f0e13091a01031a04170a03050405060903070809060c031c0501090f0911010311190905030f070803071104020702090c0c28151103090703030813 68
    0x1c0c407421190029100504000c03958003100004100240e001926881c0966969400030050003219001070351101c01644042d84d10b03605698a20302c0c0382d0143c40500c403d00030941e02190801120141000c88c98411481c0d058941d1040c0034018040e01d0142d03001e46032800b80c0c1001c00e45090001c421600c005402005103460284060240710240d4400e003800007075404180400c21000303030711014070b0031034040d040e0000c2015410640c07403500b10b85000b40c420182a24201c410400100300003000c0400f0a42401c1c00146002e001c0403c400ca1306c0b13080300364409484a0205924019001051700382642c0702038048070903441c9039458940d60761001e8010035035140c0c0141300c0040083c642d00420492000090005800d25019501140c0c883c18140c5002107004001304207a40c16400803c041000404078003800f03c1c044801a001c140140481c40c0c1c0034054402400810300321a1158001c40360384c11035060080d5682c0703083d148554840741e45000403030004084c18045069480b1485855400ad900802c208501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 166796618 1250 166795368 166795373
    0xd0f020901020a1b0b1306080a1a012d030e060c0a080f0a2301060219080915120112030206100b03070807030e0a0302070f0503030f040509041401020a0f0f020316 71
    0x1844e01304480d002400b5001e44020a1341014000608400801255014400742c180744001c0c0000c84001d003500c030424641080e9407581c1d04100c0c1e16814042003820074013a540c10070410124001000d44542c0b40080c410107000800e00d90503801490380c1d100d804c0640e81c003500d90180da170051340300302c295050000c0c41c00008584c140212074900e60304044411000550014401c680901e1640700c0f45400c444128032100421005405001e00c0701301c040701e510f00c10800b1840b5620031110b03000350802580203400c0c2e94030780b000288510080300c4c041903449a040c2180d60791384400c001141b80c00c10342200140108408512b0b482c801d203440d241a40c0e10781c0c00c50b074255a961074045070b0a020040c0800d00305916540466226030040c011072958500139400b501d5454180340b0301020a44440d40901d000364070401104801201540a0f98181d4074102ca49032440d84850501140d1002c900804000951000600d084065000080c1c00c40c0304041c0d0300c4d1380010200245080e600c902030500d190b221807181c0c2200d0b800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 166797868 1250 166796618 166796633
    0xc050310210b09030705070608061809060c180d0b0103060605090106050a03051015020c0102010c0e0303040302100e06120901050c07021309032a060b040504080a03110f0c030d0f020901020a 83
    0x500c01e4a034003c44e810044580c0f1180d14003d05940a5030114011909102035030034004000c07500c1d40100c0d02503000c6030030700000c0305983c2d80c4020f0020305440004a503121080040c06c1906003281402403440100030f0700c1c4c3c2083d52096034280302c1244e9003890484001040c0c20180f9034181240d06035180c80341000340019065014000003009015000000000032840501040104140900d00c0e0300922900c4042800642103801c0c54000d54144031000001484a942c0001206c0c2541e506680c0c1c2c070b032488080c0c2c1c0300f0f82c4c00c000c2c1031440c0ea900c03c0d004240701d103441702d010b940700d88911082c000901c2562640100010144540b00e00030390000f411800b5144480440e40042c1583c40c400c2ca00002d26a0b403000600021007ca952910744410410481400b030055070700401c0f00d1070304200c03000c100358209691001494422210b4401c03d05d5142c183d000042d48000f025980b1f0000806501681c40c211040400c1c0c481d4041001d03040050b00c1c1c1444440707882021f03c00d884240070181c005294440003611441c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 166799118 1250 166797868 166797871
    0x6050304030e13090506062409030708030301062c09150d06020a0c020406150801030f060f09060906050a0606050d020f091806010807020303061503060f040c050310210b 74
    0x20180080302c00b0750030141d11070842070800d014031001d001520b104540b0f4030714203110001e80314511405046da103041c0070001c0c0d40002c088040c2003045056a50180c0000f01c3d040c007585034410807041c040403000044403500864091030b003c2d540c0d401c02d070010b0180900100301c40a41980c041e040720701540000c03101e42e51480c40d0700c08480018034030442d582c140e980707400a86c0c3c08084900d0010728040701000c00c60500b8016200038188513004c001102c03900385001882004148000740595044907000c005104082c4d20070381c0d169041c0e2206014400c3e09007000d1000d00401d0700704031540d0b450180080c04240c1d46100c0c800603642030360b483c0c9180a03008504040030b900003000c1c01c00f909800708101d0b80b50b46d0340d86185900342048042200c03400d1415800161400c03400600c00300540d0410010043d00b0765034200c1c103034142064400000e40300e80764800031880174514240f04580161074045c0c40ca1881c0d070088080c51180014280c160301958441641400d01041c020200003044420040d4400007450b089070103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 166800368 1250 166799118 166799123
    0xa050301051e030a080406090b07150c0c0609110901081506060c0c0319050f060103080d09060902090907140103060503070b0d02070b0103060b0a060503090604140c0d03021005090a02060406050304 86
    0x78000b100400002d00b4401c0094040307171100c000280401156401c0361200c4020511080c0ca10f0505140707441d003544a0940710004070849640340c0d17009015034000c131101146150404010084030326146400c03c002651140e203948070f140d4035000040e480b6400108905d45220b0300e0540440c50303c8160511020b43c000c070381c3c00f0340940160707454154079440030042880000c0148e2000015034001d800c01d24245200403401403101d40200300140042900681203884401c9e0a420024000c030316401d0050003010a410000c1d4860720020900200400c000344401c01d072080c030700d044c5500600354401901194103d104494040d04140001c10a2100240240440c15040240585132a003a90b561a0b40490240c00c203d0b4256a43e41102d1418200441c02e60050401d0381041e80c40d506080790070683e04d250050008040f018180c058036809181401200c07151701018100a4214545103006501d40000454090401c0c0c600b00009907403100c00200c03612159000b402283c50b060814004894a40c0000d20a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 166801618 1250 166800368 166800409
    0x703030f0e300c0c0f0d030f1b080403081209070f03060509160f15050a0c080702030a150617030a080f1f03080a020613081c0b0d0308070909020a05030105 68
    0x104a41c1d04100024511000f00c140945032412044003081007015992510501860103034001030000307500107441e10400340040c00d0101d00c84040b1070000005417503107239004284a602150000c2041652406000180342c4403d5032000d03540c483c4e444954412052040c060b4081c0498020800b041d201c0d0f010a41042400c0251581103101452407800d24801d64009100b00014034020031210023440700030060400d0b00d141c0380785444050400141852001100038000741d000181080455800f004040080d6901140103900540100503034802040c141c41442d141000608030307400000c101004503120710040752940d200c10740b644070840d800100c00400744005401c40b03882c4d560603a4010503952000b1849030585507620000c1c4c1e44001d041582c0a01601c45111550101500090301e05098034417081810301c2d080c20200500700818058401241d0301500004017541900074554011241842010240c485564107980c1d0805001284202032402001820600c014801441c24113580300354440a0f055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 166802868 1250 166801618 166801693
    0x90c09030309101701061e030e0109020424060c0f0b100b13031406090d03050c0d060f06020606030613020405070908030d0c03051803041406041502030703030f0e 71
    0x400c0740d440d05200c1e01008079130300d410082c1290075207101c898050300d880e142032002c7c000700039041d04088502c100050185038982103900c5910b002507219808150300200140980900c88a4503440072811a008070410705800e80041582d40c0124264003c05030312034a0300c0e01010003501e55002c4a94042c00c90703120b00d1004e030030005000310b034103018011101030740045040e16032442c40c140f05a80541164074402d5004881044003421022808103144107850401180c0c56403030742c03001034441c4100f85541088503d0410302207001050050003006840c008d400b207484548601d8200755440c00115464004c1c204d045856200606141e00003581149590070702042294036041440e0031a004803040142c219a034022080703002d641805066005291407220b002d40d015010341854503071243e8090030300041c4604a070240c5a8603580125402401c010781d94503c0c04210010003512980201c01c280c1c000380c100b00d42c040c4070708141d110703408007413013240d00034090562682e6840e21016035480c500321142c2410390 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 166804118 1250 166802868 166802887
    0x60c0306060e09040804032406050a060e010305091c050d05070512130c03020d06050f07080115210213080c06121302040e030307020706140403050606060304050115030809090a0b090c090303 83
    0x1512466800c5060301c060b000c07003234401000d9089500e5940302d5880b50055403810001c1e140c1000c8460012042840d0101d059600d8100035454094001312080c0d007103190441d0806000d5014000e0810000d031480188065165a4011105400340161001e6610701c09404111250014031200307095900c00c030201a80c0540d82d80006080ca4007440d025118142c0780d104000f041c00424103003c0c2d0103034103820000902e50600c0301d0380007461a02c1c9420380a01066001181c5100702240e110842440c1044041d03541d400b4803040e502080301c035849840c2c1a40703d222406416843c008041d5408004000c2c1d915055546002c0014124a030028050342c11690383e0101101158003400110b1144d54550018450145840c1d8010b2a240201e00700994000d4140800e00c0014004640750740c10002c00ca07651610b07a212400e007280100a014081d6600a50b000000810031140501400c580d0f0400c449030400e581e11941c0c01803e40e01c0d407040b62548011443d0005500152180140c0001e42020301168200168071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 166805368 1250 166804118 166804133
    0xc050a0606170d0305010311040f11040303050a0f031a0114070b0109060f0501032318010207110901090207020a0302060a050d020301080102032508040b041a070804060c0306060e0904080403 83
    0x2500316400300300000b440006500000c000711407448545181c02c001540c5141c4440648120701c0f40340a110315200c0c40e001d00410806d8000600c4035107000710190f919552480c0140250f40621200d00102d10528104e0840500a120b4583d1108007044a00060721144004540710a20187c0041c10104140070f40d40128504030740b8140602021500001d4149c2010303604510108240e111504060512004510340b60001d6030a0084156800c920440d50312007089510b4082c000c103040881c03c0d03101080000030700c01d07658007100c02000c0c151400381e40d90340c0f141e802d5016841100d101940025480b00d0030001400c01030000c08071040c2c10b00d84903060071461340035042668800c1e4401125a0740100910101120840004440f0500024103038600f0804440241558a0040020b004880003c0009003031002480400415031158031407075109107003100001d000f1003800e4805490091412500d032052501911628065910607210000070303031a44020008141e40050048400d440c1c24440000000c080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 166806618 1250 166805368 166805381
    0x150c0d0204090e070303020f01110414010e03060403020a0c17030703120605030312150105090a030305030402030c0d0b040c050915120309060301260105240109031e020406090204150c050a06 83
    0x10f0300c05802a1491410000e00d40300e1140465002649002d050810341c1644000310340880e400030309606003c3c4807900050b500448105003140e0180101c60800c405c166000c9900600c5d603100e40c1003080c850352039101142c0940704002042149620070410301c0003007409100c40e005040d60444011540540340e0010a045070040d58040561603803040a2103d400500f01581c84090001e18100e410000c400000800100d07540c0f001600f8080300101040c25501d081c03010051042025119243c4070b9900c0c40c00c40140b20301120256504523140c100421946040c03100c00740034601e40c030340c5049004a050308101c00084500040c0703070136200c1004580d071340b030715480040c500070200083c040402100041b10030300c4203901c084883d034542e413400c8100b2801c2507043c2c1d00018030600c2100380b83d0410b00f610700141c5010901c0c0d00090824244052520380d070004c50440810f400303200361028403a681e50703690a0000c0e0300581c01121804a2001115880c2c0c070701c81c1d00880740c203038010002c8800032500c0d525960215240b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 166807868 1250 166806618 166806641
    0x5220807080102070b09300f120711010c0503071107090606050c0d0e09040609020105090d06051905150114040f06020105150117070e03010b13020904060503150c0d020409 75
    0x100491004144100f000300f082c0c5c80880c00021f405400711302d01150b081c144440903284d01d0001c0e5048505122038444040d91044424a600b4540e6000c0d07c00b41c411080e842110420006400000402d4080b20103001c0c1c684044030766100d0504546402000341c4480079051022420743c400c140001440c100743d805050001c20f295107815a581040c40744035405c1050140140c818010a50000034890712003403002680603800c0040019201590300c0102d50f01c0c410031101c50b0788451340460100c188101c40d8010340c00340720700706c55201c25107041c0006482514011140e0540c400d110b0200701800d540502c04a4000380c0442940318036054440650880e400b00e03903004003006070740d500100400700d44c696050105001003406c10340000354500d2002e205020005021008100042c00310740e0b800d1300c0940005040101c01410345507500f04c0000060029089400d21605c60350502c40002210700300801c81480046a0900b86040c0d561400224030701d1754002c84800900c941d0070400003035442d030b4501c03d13081d0400c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 166809118 1250 166807868 166807871
    0xd0308010b091c140c18070302160f0c061b170903150a061406072301110a0302030f13030c0f031e0e0a1e030312060e100810060303052208070801 64
    0x12150003104d440d2072450301d065801145290b0702000c0003840312009641c040044d2030003603650844c1010110403000700501c001d0040c0030748160341040042e07125450302078030659955054412100010040e0342c12507040c020b44007891880c5d1030201c8480c04002024102c001404480c81d111801171241c1c440031080301c88083c003944e80c0d502444001d44d01000c0c00c808820071941d0038100103e94445000b03c0308110b058000801c0c44412200b080002904500b1003407a000001d40d8880b250f01a0160182d031003121094000490743d400680088907102241c1da0240d015580c00707001c41e9180d55241d29030880050309030f00388214610f004000200e0340b02c201510300000d643d1007060003c0c95050000c0c2c0b4016802c0410584451000440701e03107014540c00040380d41500c1c055460f04060400100102001c1e00a501e03141c804008004400700e41ca09801d044810100c22a429070010b48400411540a07010090018204000040785a500462907130701111a079501559400d5980c0c00b02450300c14242c2c045c06159 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 166810368 1250 166809118 166809143
    0x6070504302001032a02070308041d100b04060c0606030b0406090b06010206040b27120903100506030d03050603011407181706070c05030c1f0b0d0308010b091c 70
    0x560400000311580c078013820240800003461250090014100c1c2c0611101d0b0071020b000c106a40c4200205001035070046001507641c1d031220641000001b20900c600402c140000204070507080e14031805048072008206a800c15061400445142c2c900da001590002d4650790f010011031311009006010380d104601c0003500c1441843c008880076002440c00f4150341000d000c00003c10501041580c0c0111800e466090080c0441020b0340300140c40020129280b190500c40c498510384c923002843c9142040381100c040c401280031450554100300c408580641103a905088024041c0c2c00c130716040900100049000c0d24944822103011500315244070010369440710701c4411244107107514000d020209201e140b005902c1c21120396605024100c60104003070070f6130490a101c005d0050710704000452042c4d40c00c014104078000d01076200060844005890600001181d01e040c842018480b80d060304c0c5c250180c0c0c038011044074070350005502d640c1c001c010160600c4400c1440e46c81c882c2454070542c0c54001c10f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 166811618 1250 166810368 166810403
    0x4170606010f050705070e0a090b0103050c0f090c0d0f02070503070b100b0c0c27041b090509101508010609091506061e1e02010903030e0607050430 65
    0x80000142d800000c1c02400c0240c034020440204050096400101c1486550303200d5148480003031405010240078880c1e10740020040210100c1d285c288000111844800c403c200b904000c1e682e01c1c25075080030710860400148006060350b800007080700c081d2040050230320b8400d48400f81107610821089510b2070000080042000c80902d4500c0034140c442c41030b40c00c01d5403154000d0ba0708c043c07401107a031041c600d4402221480640201d040e00d0039140304140c001300d007001d140c10b011043c00c201551000586036200420804054801c8030b01c2030039400014203c0c84424500030380249034840740d82214411a02000c244a202401444001c1c01c4050340040c4103069404e00c009010080384410072010300780042085800d42c003203101ca900000084100080c032070000b40940325120101444c3e803a070420002130b0000580c040d4405001c0302e00a8406111044000325800d840342021242c0c10702080c0706200600c440301e0310a00710340041c80002c484080450300c00c0001c040f40390705d0000844900940c2421b0155 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 166812868 1250 166811618 166811627
    0x21c0f0e04050408130906120303020708040504090507081504030804030f200a020418050d0513030213020a08090c01020616020304080303100816030308010510120c120605060702060f0901050417060601 88
    0x43c030041d8030812142c8e080909085103400150700213403c150b00880c0c0390040c440480d04840062000601c00c00c03040007a85844c64035803600d445200203034094556001c40c005090000b840c03040354036681e001d07600c1e074507a50182d405104049640003000176000c00c101c0104d60540c0d200702890f0788000140700721146441007009a4421074440111800340360801000540c00003119403500c09a800c00580f02c1403600e00d80c4c1101600c0c0c3d48003a43c00f0403404d00d03102c0c0269403980141f4425070203175169122540c0d0480440d0351149440810780c01a40700340006420b80b818200030001c100624030540e0300d041e81d40c6065500c0c58106896100403410300c83c0f002c0045e928108500101a540f48011040062035518064580081486494010505581c030f01d80c016100d41512100d0000c01c20080280300050303003004103100030401042055500d0030802080d02c0c640f83e404e588605a00509903440c04807032028000c180d4100360100d505016007440003090400741d110031798074140220801003000c0e14100c0001070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 166814118 1250 166812868 166812907
    0x50a0e10020c0d031e0c0309110906030c040506040e1b181b0702010c1e0c05010e090c0c01140106120501090203041115041e09050106021c0f0e04050408 67
    0x1100c10300c10042100c054001292200f40044039040000c2c500034403040c40466030803030000210700f5900c1e0103500c00c44203030141c0c0304420403405000c1610300004100140280c40030140e0300d00e94907074010343c2540030501c0c0035002250310040107400420041c204075089840d0181c17014400c130300030200f00420346450900c0b02d000c0444088903800420030f07060280c52903094100003440f0034940a4002603120659005440100b0b07015030060506011001010081000c203074094000c6841102510f4000380a6102d0541a0074a5030000d224640c55100c0d5602d0710784942c001001d425881d502c0e40d8000d801060b0300e26020b4000c104a46030303507802c11140312440003100d9050704040a010320520501000ca9100c1c0c0020440c800c06899404403001c00d41c445891900881d80140380d517081c0280d5a2040c1804800c8000c22103500203810f000a90b260002030341c031768088001000c0c1c98030160801c0714895204441e50007034480c1e80e040c82001101c1400100b01582d4040300d0994021100040b99040580314070740c0791 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 166815368 1250 166814118 166814143
    0x2030c06090901030b06032b09060f090501050304050f030c0a030206010503060c0435010605011107030314130506070c0311090403050a0e0118030c050910030f060c12050a0e 76
    0x120320340011840010b0491406000141082d0103000010300e4a4404201c5803501082c03064040500f400d848030741c020400f00c074000d03040001b1007181000480b20b002c0d0440303d448001c1a11103240d51420030004480541001300705840740d01c500301038031050310800d00081003203454150150203a02030305c1c100a4541038060b44028003d0b0f0152080240201002e400e9905807400d01120203010343d122519103101d440c0300080014816401c0d603401222220540c0a442110404c0e01c0e107292027101454515101c180c0e0f40300250215407401182c1001c269500300403c184000c80000c0140203071204041130301c0d174201c0f01044808030090340c414020700c415800304c00d240610440c4c14203958945540c00a2950040000d01c07001d0094401c0c0e02901c9a0055008002c0d5000c041c150b004a139030390742840032502e040341c843c003801341400a0100300741c181491000d200340c039000700280f620418150340f0000100384500100c0c042110300100c0d0341311508076000300c60241d01907220218124050440440c00e10007000ca81 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 166816618 1250 166815368 166815379
    0x801050a0b120c07080d110c2b2d030212090105090c010503070e09090307060b0a030c050d020a09050a050604050112030914030f15010e13020f0d17040b0702030c 71
    0xc00c40e90840e803003015502ca260f50342140d88401c814a8064500c0c084c105502d950242850310751100b47c00c808025210f4942c0c00400c40c0c1141c1c0f140501c05000c9204245c1880000d00d0b9074107111480c90080d00031020700c00341000320b003028114140100d1031000900400d100042c1d000240c55141c0c0c0d040012040e08551118004c0049080261950b41c3e41c0d610742c0703181c4c0d050041c080000345010303004890040f0803800290044007a0f180041d000c0c2d4403070380106000c403241c2d4500011029281840d070a680d090782e920003524010b50703080908110142c08a03640481c0d024000000100e003802e10790040c14010200c0d00000718180c02d10404000640d40145c001d58808400408151b000c207600c92003100031101100c00d20b02c800c142c1c0c18007003420800c0e07070385020180b84540080340441505200e01300341201d42c1d0041c80021604e440c101403a00700b1216a0180d481901c0000b140b1203464012010450700b441140d06849810030700500c46034a802c2648007007803e12010401e00150f08050010504403401120b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 166817868 1250 166816618 166816627
    0x80f07030317010506180f040606080412090e0f100b160302010614060f0702040906090807061b08010312030e0f0d0206060409020a06140c010615201009150c0801050a0b 74
    0x101c0d5580c090b00d092070080841c90b1034034122688400c0340c80121f00e64081c20511465440f03a20103420b00c0c5042c0c030207c51301200c804115102c1c0d4401c518100588102007424411504d0b00d10b5a0000300c0b4010b82800f00300e000c1ea01c000110141c9141c01045044000b0b600110303255072038100a802c44542d41e001c1403021303000c1c802c038184994910040300c40301240e403140503032030303030342c1ba0001c600104a101c030003c0ca41c6103041801000e02c4003980243c030315030348550740034810000300c00c003590580c0300008010000f04544a00501c00110001144da052102da4500001c0c80820303552060702d420040c0c0354140c0250030040820031035550502c0704540c04007040c2e4007071020300c89503404a401040140305100070444001c04d507500420f042c8080b5070324010100e0003448001d495503425030b02d94284080940201f860b0760956001101c00c4106c0049201400c0082c04002450f14050390140007518400c0f5541d5981144a02030154207101c1c41e0031205903507aa140156041c5014000780c0700168100b0310760b01c2010701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 166819118 1250 166817868 166817879
    0xe01080f0606190201020909040804030c0609050f04020a0c1b060f0809150619030506060a08010e07030b06060408060f060a050312090625030e151213020a080f0703031701 75
    0x400703c03032040351a0f00318105815180780342240240505038030b0300e602c4241802840284446000507001b0b0301d008102140c21155284400c0d40c119101c0e110f126080f5040d10120380d0039292581c00345c1159003003810038480c1c2c11021741c1c80b90b80140f004400c1e900b05a420180c10b00c030955006034203030038120250a04048900300540a256035010040548601040600000b17005442d8035403035122003400c00c3c092304c0041c0e85a16006031940e80440d0241c2c0904030b940000100d00c03605000c0d100040340d62001400100e41107403a9005030900040c45240c0100c010400040d840c030040007030520400a401ca092054244132041010761101e56110f14400e07848802c82c00f0700000b10700104c840c3c291040383e4a942d6280001c1035540486040340c110100311003041d41c41d070700b815005101803030019000c0762483c0c0103500d03100c07038000075000700d03644032a003444078000090b0b00c40c016a800000c02c5000400c0c010580f5501c041c2107140290702e060342a0181c101823000c004040e00300301d211020303400f490180100b560510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 166820368 1250 166819118 166819129
    0x5070f021906050a11070f02090c0403020d02090c0f070803010503060105191e120602070c051903020f0f090907060f02070605030705070c0905010807180c05040612020c010c0e01080f06 81
    0x3107102a05640d6210040340d98001da581c845034072000424002a1030721124200700e0151412a28241e004076040c0000481422a035011135003aa5401000102024040c0c1c00340002c044008080ca03c3c0701408001c42400c0c00240800382080910604400c1c2d03596040600b450704060f010b900280c065404840c030211840404509007090f1080c075014001c81070380e1814040700e00b406640c003041600100c0e9840005111081e001040554010307a03803244070507900c02c140000032442a071404402c1c2c2c0b400000b032006207442d0100c64100702000301198820061080010b0071030600761120101c651040c0341c00c00c4820781084140740000300e0740c00079002c1d041c5820005001440300420308010041c0024000080043ca0344000000d042c90010402070366841d03000f01c580e10301d910301038120082d0219061003020003c41c080c080c1004002c1c0d6641c1c0c10a442c2c0b080c15070f40b00c00801c103a03180c510307000e10600c0c6044409100360b5a082243d0364540f5500101c2d900050a0000058410000840c0e200100562901c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 166821618 1250 166820368 166820413
    0x5012007080a020703080d09230d120603060608160b030c030f07120c03020a03061e0e0c0f032502010c1409031204080109020406080a050c01031e02070605070f02 71
    0x8224410794451118408904080302c4d80c10042441d02d000c80c4646070303406c003a4002502507126070001d008010300c030103501d00e401d11100486100c5501449204201c10b2240180d0040c1c040440c00c04a0000d850f540c5480c281c80700f40c1c0001e040c562188101010803007260140304000c03d48440428607500b02070350001818072009102e401c0a10140000c10001c901c961030910402001d1041000708505003200200654005d850340c0340000e0500c0b8020810881c0481400d1002a00040c040101e601e801e0306080500c1d00102000300c81c0740c0520083e4046038040c0001d521566000400d003000c440c010084030203803050b4200740421a854035040703182c1503801900c821180c813954502d1944032140c50001170b281c940b1500c0c603008404000300d00090300707000540002c065940f08a409000443d100c0700d0f8140d50b10540d0300060200c3d4000e517002d10042d4001c0e8404020b100c60f5807140020000b0303204403c0140d1b070054008540f610754171010000c2e02c0341d204a61035190300c0715102915070324040c42c410710311400c3e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 166822868 1250 166821618 166821623
    0x406020901030b012d17090705120c0904060b0402041d0402100c0f020112110a020c030601080d0203040b03090c061c15120b19050103030903051501050907050a03060e100305012007 79
    0x201782e000d0451030041c0003460004502d011592a81e02d000300100e40c507140c0700d00ca0203004421240c06502c1c01c20000c55024940c800181c2005420b94403900c40300050b00d0080e003800e40080c0d00b0007002c50600e0303085800b0038902080420f0309809090601c18401c3d0080590080e001300240500c3c0c0500050313840a550302c2881c2c0900c7c1c4158109c1150240c3d0008000c9568071a40c050000a51203c0040d00407509264201044050b103042da83d0398003034103858842c0c0d040e10300010b8208000612040f1211400346810aa045013286c3c04141c804001c154160b100a500d06801004a07603001400b034200d00490646120543c284880e141c0b80001040030440d031000000d042118039800035815031310b10903011180c04034140741800b03156901d003170141680c4082d0000351180e0040501c010140c54a0001040c100d0340050b104152941da611011521500400d50713050030561107410004914030b407082c0c8180201140f02312040b50628614180f070031541d003807040702c0c030341818055144074220b071300c0d0143d4035980d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 166824118 1250 166822868 166822937
    0x3050f0309011d0406050406090c0201060b18091e01090b0909070302090106050d0207061b080c040e06010c1b0b19091d1312020102030f2406210406020901030b01 71
    0x1403d1800040103403149030052a001840c01500058081c0d041e000a40c0400141d00208182c94840190301c07500d00c51400380020984c41c0902c030900b10b0074000c007140d90045880c03040c07858900080d100032030000001ea00c50b22456403188507d106610b00502841e812005020040c01090b29507070101e15402c038140715100502501050440400e9155011100c607254044410031070030200d050204400c2d5044004000000d41c13100000d103104945000b140d066030501d0b0700c4070400b659141c00444001512010480d43c0000081d40c401d19914080c84030001b03040c40b500c1c030f9030303c407d1310074400880301c1104c0f0118010441106400c00861281c4a50712100c0700405114401a95403088406002c482c11080107006c00912000d03c0051075066002d1030240065400101b05601d60040341c006d26103107042c50340c109000d020000103042c03400700f00400c0f124040c00340030000700110b00048013684c502210f080e204590001000c1c103407980d1503c51480244002d080c2071041082140c09000c4480c00c1050039031485 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 166825368 1250 166824118 166824167
    0x5180118020705010e0a030f26070e030f150a020703090b0703020f06010e010f0e04120c140d02060f18060a0b0a0b030a0e0c040c020a0627030903050f030901 69
    0x80640381c0460b90481d0b08540217019400c0b462810075502c0820a805500080344082c2040380300f4801c0b24000d044103125200403024058825442d003040502070500024040301c0e464043ca591800d110204882010501034040b01c04c042540011142c00100400841c62041200c400041e0f00003449a00b507a5030301c05256114015860240d15040f01f81d003003003560748524000011a180f0248005050b0303808915a004c0040c2c0e15000e107040f28a007520300401407107426104186092060070300e410218082c02110100111640c40c407401d258080204000581110042006041d2140e55640d0411084000e0f042e0301c0404400f40c13612801c015001844141e12041106c5495440c0d030f601001400d070b40c098842c0d890400f61a21401401218440c200d540900b1035080d50381e1070140300d0314185502607009014907044030f684140c020101000449444510115003603840180230042ca07008901c02e41f5071040d25400d42c1002e81c41c0c45100c1c0c0080d5034560040040065503603014402103c181c00300101c1c1c000b071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 166826618 1250 166825368 166825409
    0x304210f0309050a0f081902030703210906050c040302121605060c07180504230607180803210f07050412060b1002030a03111201030b04020a080a0309030c051801 71
    0x11300071180c4000d003130314250340c400c0800d200a0070300a00c01024907624040c1c24411101007a61240100040600440e411005d41080011f8580304400d51109282c000a1240301a5031144100d44055490031445400407a045c0118141028204040604000144084040c004081040041501071903001d00030110303800c44462410080340020f0b03c034642d0b00c4400c0f0800360031550b005100c00c44050340c0342030010342400b0504035400c0d0040e030803c1d154005040740e5500c100059941261040d0070701e0070900ba02000044111050026001d40b2001e0642542d6078456113418200030320b070143c680e0b0b5030400d0160910640c950018211011a5203041102c41101c68905103a0014040080d682c0d0704224404004001c0301c0d80030000700511800d940b0100002c09105070041203e006040c4079806110f0000014000328519808180d8424030081107294202c2e1038080d00303810844005012008100181002d0081120404082c0041c15050700c8184152022095404010a042c426603403000c44020a4811 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 166827868 1250 166826618 166826623
    0xe1f02030c1b01080c07230307020306150a0b1809100915050102010623040b04090813030c05060304020609092a0705010c0516030e0102100e030304210f030905 70
    0xa5118480700396039082c01101050007504110a0500340001c983d140000d1240120354296512150003010442d62030211044030b038072142c004c0000400a2005002880c01690f040084601c90301884046080950410090000500494102580d910000d010b041d46050421009140c2c410007290070081c641c451000040010003d41c120031070450801319102c5240507031390b107400b00303c030030a074001c01c201656809059010002104240005404803c00006524198116005003100200009030916030350359141119440704180b6507800900b42001c100348481084100000d0400313640b458503526069001801610507482c03c03501c07030307a000d00204c4e026602d95201e800c01051662501002d0028074110b403c0c2c1d9800208023115a5820030200c23502c1c07648107400743e420000c07080c182c1102040380d640c2c0c1910030604006c002c50461290b42003101025901e4003034082280c481d68003035a600d04045c200406d01d00740102c051884000c656109107045c0d070380484162803504043ca800224100daa19100c0d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 166829118 1250 166827868 166827877
    0x321220b040222020306010e01090503070b03090708011b03060906150507140708011a031615050913020d050601020a0309050f1c030e0907020703020d080306030a0c0b190e1f0203 78
    0x25643e003410a002d0844000c0350303000314042c80b402d0301c50400b0600d403000111003c400d240100b5806130400c0c5800c0001000c00310140d0b800004200c20380e140c007500d80302050701f10f032800600c4c1001d20400217504080c035501841480b0251030310003c203101d01c03418154121030754200c031000c0004001000030b030801440b410b5408170b00d080b990340c42911856640c6421035800b900082c0d80712400d00d8030f800c0b4803465a24000520141000c542c42d2452216480c050310000000700074002c071418800d04111010103a030703e5500070941c003401740d84010780391392602003240100d80c40205014190341c00400c440000c00c0d001800f990440e030040340d17036941a0040c400450481d0030111000c038485054103819100301900107846120350602a10303001d060b40c0d02d0401c12644c0f00788900c0f0280d00060074211480100b00c1240056510032005022070301d458620756070714040780c60903a000e424100700c0800d03100e03250350501c50001401200c80c5410007004888400007002022030310640304070503110900d0721165031f00900588 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 166830368 1250 166829118 166829149
    0xb03190e010605040e0705130209030a0f050a061d06010308161509110306041203020a0c02060307021006050103200307031d1c03090816050f0321220b0402 68
    0x61000440103880c040c080d04403809807a1045080c058280c01302c50000680c14102c80b4024282c5c0d42074144107510038001e5104241c2c0075094007500d2402e101280d1980c05404115120383c00500038103a1608103e4101d0340484c0b1040c5050054820b00c0b00c0b01140040c2d0981500c1c1c12404031681d8a01e01d001100c00c05000d450010aa2046986501484000d41c0c0c402d13000c1a01a181003800968154101520382e00100c8009000c007048880181d2017510a5000d0614280503041c140c070702000c99000141160001ca0715540160b00c002d00101d80d0b07600501811000f084207003010700140c041200c0da00b1041c801c8903059040d00b6404000182c4140c804d800100d080c4c409a47c0c1007100c10501580980c55140c03099040162906000c0a105464440e21078200400d4010030b032a0708114030000c030403040c103245813415a40e40c440c100700743c054520144000c0c0700c0d440c2892045401401100400788c15404c00801c0c00c500490203a20501d8500d05269401c40185d40c4091010074642d0780f440058401e40b80810b22 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 166831618 1250 166830368 166830371
    0x406080709060f05100c03050306210a230712080904110d0506061614010627060b04030f080d1e0203090c0f060f0d020f0a020706120908040b0319 64
    0x2a18410541c015000c3e50100f0240068880d25a03040c030440350780035013a2100140c0c8144103a80841c0c03042c0302640d04100000c0404884001504403140000c40d050220001030b0031140384081040408281418a80602225501c50342e1416842d42d03107843c160302c9083c000c213401d5642017080011a0040758010400100100240d81d800302004a0580040c00030003201c3d441c0c0808207036a4036000082d03501080820340c00000c1400c0550b148256440782c02c09400c059900d500700451120340da14408a40033ba400f01201484000e4060703c04250780c1180d01c41600b100b801c00c03013800411020030700030f10141c0d0028072503030b80d07441c80400000040400d200c1005682c00202c10a40e02c0d1081c68004502486134a0102c58040308070340d0800c41303c1d280d00100075902007010800d050b41c001c3c07444007808030141503000040c10812803d201c1c40c0ca07580810400340068200e80410300880760020300c003180d030420090f810408a00340750313500a028401d501035a5104200800021070201c0c8030186800500c446010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 166832868 1250 166831618 166831633
    0x309050406030b04021509090114010e04050a0509071406030606070c080316030824090a0b09010801020301030606150c1b030501020c100617060f04020406080a11090f04020d030e040608 81
    0xc0100b0b0894058804a224800c102c000544206c3c02d41c06496448200410368906640f03480501d0103160800d41500e41407095800c0c4502180d5581d00c14184207000906001c6600d290441d103090030316100340c1003401102c140704118862912010182c95010b02d0030b4a80343da0b9022a4144203120609640c01a07840e07200010306175030002283e000300e55105101ea2a0000191103100c0d044510240c40070100b0420311482541520030314205154607040700c154900051107005503004200009026040398996a400200400c01c000451060500425a80c25000342010090000603d0402c0c1444007822111800320002201d661800a2034011a8800021541d0f05018607078241c40d10401810195004d180c400300045009100c600200780740e00110140526540383c0c103c20040280244c402e0b070b046075480a001c41d0a2800704400c080e01ca0107071b4550000c41e002c080420100001c01810b80500620600c00d100051302e504101c0a401503045c00e00d00c59050446020900600441c2d029000900c00c0c3d94 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 166834118 1250 166832868 166832873
    0x140604030c03142b020114010e071d0a06020109120f0c17040504020304031e020d120203090f01180506010504060f050103050a14130c050603011a0d060902181e0913030905040603 78
    0x3040c40c41d540107580c0003488010240446494a07036002d10038003613640c0f201d100160303542d032040202001d44c0c0103c48000cbe5000003d107021404442c1590850b0700581e549007210b00500402c1114004c5403422458002e01c00e0384800c400506100d90b604000301461707200462000ca041081040c0c40c007030400644215180c0c07402d4100200700e00013403522900e540078602100381d84d8610104049102e41c01c0c41d2150016089000c0a04000390b00080207110107015000044280c0442801141100300d0502014900300400e818114285581030307003c28170a61a04c0001c10488511400160464409081c00211590b030006141d0203000d0361440d91494588100c2000070124005180e0034070b1030301139004145030079210350501c10144000e0040e400c0d943e10403650754036801400c500600c0300c0c0740d450501007900c130b0f501d01588050f60007200b00c114031045144011101d40c10200520280144424503000d44d05c604080032440c002e41c05004410646a02c403010800c1c54040c4599a000b000090010804a0b50705d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 166835368 1250 166834118 166834183
    0x305010c03020414010306050609010f0216120308090304050307170115171e030904180b0c0a0f0309200609060c0a060e0d1b0f0b0709140604030c0314 66
    0x1030052030650f406510b55113403154841e1055800342c4030040c010310b107003c0040c0010358400500c1c001e0a4114801c0390340e2810b901c4110780380c10009041a65071b2401c2a40305150140015100a100c130300d4540c801d2000700265940007400108031030001c2208855510540b69440c0940450b550140b00c00070300d0310001480d0840010f0300505420031400340e80103004585c008694440e0540410180b81e40280003110891070954012894400c80e40724250070515559070303200e18024201c6070403403800320100d0104441a0840810300903036050340741c204a0741d1415500c0d00020b07412054080203103940a08602c1d02c1da01c0c1d06007140c80d00600184410340300e9604482495890340c465104881c460b04051504e044411300054130300e036000458460303c00010700d054904040780c00d031030401c0d200c107083c031602d180100b149800c50501a0010b82c0d101000e09080104c4840c40108003114280a40400c000c00c0021506050a410030340b0341c0710351040c803110243c26130303146020300500c0d4440428034000285000040c46 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 166836618 1250 166835368 166835377
    0x18010905070626161b11040b01210c1107030b09010c0302030c030112030c020a120506010503070b0906030a09140a03080a02091c02030a060e0d0206090f071e0305010c0302 75
    0x1607a100e1844803c00d00042c164596080881c1510400c0940031943e4650f15212064104206141c5414040e40c070744032241c400808040c00f5291031409541c15811030415001d801c00c110001e00308941080414074a042e180003030300c58031083d11541c0301ca0700c040c06442041c0518050000034100d40c915500c2c3d0400c17130a0000159440e039465803800e000d640c8140d001e802528890306948122608680c23802c02282407602c03030804110700700000c03000300b000160b03030781200c1c44041c02e034800d01e02140300644c0c580186000b2060300a030340b0950004000f00842031a2800700e817188002074400d140c503500c419203142c014111600b0020300400310b4182c0089450710025903148124060b544000c0c0030380302c08141d04102d1003034000d06500184400304a14a180ca4441004409880a0304803248055141c482500301c0f0501d56500700607410024015040e5076042051603003200714030300138084d440c0304039401070b96400e01807149105943c1580d522003550a0041710301002903800400034410341213000c034002c0c020b511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 166837868 1250 166836618 166836629
    0xc0b180f101b0e09070306050d150c02060903030115020c03010e0d021605031504081e09010e0103020921030403060e0606120607020a0213020403060603080d0617060f1801090507 78
    0x1c0c0040004840e1074844044042d0b0446480310001c4000082c14841203460082c140b2051603282c000009094540c1c17031850740c200780aa000c4000c3c02001c20400400e40d0202040710007190310181c280101c510307000c0f084a044429064030000d411590807800d1741425840c0c0c282641c1540382040b00c0850020110744000900c0f199401c1e950103154091800041d4540d40c000e80340c00d980044544000071600140c010f41040c0602801e900349070714822030b60300f03c80140d02503018003a0045400350031560000072061407070340e0900b01542480481800308200ca4104521940505101c0c0821001d0440c1481103030091504400203001c0b0290302600d41d0758503001658068002c2485401d00062098007184980c00f6041b42e078040c4c00c0c0c1e61707401d800b0408807545004034810410381c01c00c40040082c845115083c021840740804c1c40c0c5400b040310b907600c101d400503803004070040c0d02c0e201041c0c580350002c64080e0384100c28040e21400364841c83e070321b1030240170f4180481ca600e40c0703000300c06820703c07000084a004584 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 166839118 1250 166837868 166837871
    0x20d05010905060a03150c0504170c0f010302040315050a091b03050d09150804031407050709110307020303040f030512070c021201021306140918040501050c03010302010c0b180f10 79
    0x200c480c428800d900201d40300152009800004c000c071416107d4104411381c10591811505058983e0600c5035114002c10a1020f10760000b000d05400c0c4c2403c4600c00341d03a00f4242801c6080038a181c445006c100c2c04041c0300b2409540c1c41000500c091102d43c0040b8805421070706500786018072466071215040980070507030720f80c0304181910340d0180c8030f0340050064807040a4805000c0110000507190005d0182040b0f0a00c43c02103218002c0b01400406404010300810041c030580c1e1420702244111400380f418802500010020071009607000403ca80d041944642608002511401c0440d401e0103054411103d03206001c0500400030b90002c0c0000400f4006c9445001b60b00724420103508038800d01403020804440300d2402c000d142c0c007590340805141402d0380094500300c95a80001c2c407403014046584c13100c0394070034144030070700c4003d20802e51b01407500300c00c0900e15411a00040c3c011001c074103000f000c0e04622030004125500404001c8000c101c007100706c0740c83c2c1c50b4901c1c4541d04c60fa0640071428801c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 166840368 1250 166839118 166839121
    0x705030301180b0d110f030f0115080f190615090c02010e0d0e0f0a08060f090f0304030b060409080d0c02061f050603040605040c0b1c110702010806040c02010b0301020d05010905 78
    0x50003480350f050b85800043c180c0d41c550081c1e40e81d1a64200e000b0f40c0031580445542120342c1140c41c140100402c040310700000154408588a000030704504076001400310768042240c00c00101c4000a20302a107052810040030456558a0030001800403c8c0c0103124055249000241400094018140002c260340081c0300360620000350a43c1c61681000d840002034180c1d080358020b003400e14407100b403440058003c0c030b035890b202c49a003441c0c5130054420700074007a0781c4010400c86440c203000c0181804107403005075113840d2458503414910400a405a84a0b0f40e4032400700c03003003003040b00884400c80f400907000d108a682000c4043d4903500229039204020600b45202274490806507910342c207503280140351074110340711500d602c401000002c0c801c40d00d0110600c4040745440c0c4001c0900540611000c1400508821524440c140c03038400000f0030321008144a01c000603070304000300b550f0001056a0008500c00c00d00c0040b0301405880c40400d8155200143c1e40030b0090b0b05412850503590251402e0016 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 166841618 1250 166840368 166840409
    0xb040b030606131203031a031b03100203040c030b010b0a0504090209060c0109110a05120a0b09031b030d110309060411040204091112092409120301060f0e04050606160203030f0705030301 82
    0x81c020001f00ca581904800060701d101140c0095a00d4080c1000d0201c1e003503290941d41c2c1000307e80c030968043d1581040214200b040040201d641c41c0900348000019080c5984200003401c217024074003840554940114242080384c441c0e0b001e407000c074041c040007070080031580d00b44110800401080d5038041c071030000d00812613086c080d854085100d03d000080c803031010380351038134a1041c1c400380c901c1c1900d00007004031484600300107070803001000c90381010f135030b8404407011650204c0d242c26103031510845090040040098000c266654003030f0700b00309282904400d480c0082d0080c0f10755000014164540b0381004000411000134066211540c8642d0341d0984412280725035034548140b0080021803c800c038a00c140c00e483c0300036608a200c20003100c0f92207110f4411864550000d0b0415000034100d03c20304003640f030b4030654661000300251010046414904041049882201440208200e03034003803190442d2004c1003110b0303607500101080c42d11400a40381031500c0394000c3c498504000798034900300d40c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 166842868 1250 166841618 166841651
    0x90606090d030c080d05090304180501061e0314090f0c06120105060c07080607030905010507080702070b0a090e090106031511120702010f090602031f0b040b03060613120303 76
    0x100004014400c0c40500d01e00c0c0c1c0c00300d910780d4241004072101c1c20140000066064107016107030165030f00ba4055900c0300d0a02601d140181030110315944100d0606004000254100c4205400c0d80b0405401c21419039035400140e0103051949004c4401002a60410040080104641c08900140d1041c1c07546101c1c1042007020078001e21003000400d0070302600400c440d00c0c050f402020740410f054161640c15503282141c50801500703c0d054070110392113841c0101001000c1c03103800d030700c00600d0402c040079041c010300007952550b950141c2c40760910001540c184860188a0384801010403c3c4c1840341031404490407400307004640b20031a0303060780f1062040c01303000450180802e03130f04441d165542802c00031101c815803818060f240c841595690b1f4012100f07403e03a13010786501e0a0040201582d00e0170401280c01a10200024040d00c0c0c006000c020700207803e04000312011201e80180c0c0e1500c039100e0b680068400c0c80b1b03003040c401c107800c0c05450000b25401c1480d03050780c80500a07101002404201142c250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 166844118 1250 166842868 166842877
    0x2203020d0f0c0b070305130c0905040b1f0504022d0d1b1d12100e0d020a030c2303040f0f0603020a2316050c1521042609090606 56
    0x1050804800c0c00500c01303505c44c0c0d000c107a0007040f441803e0002011501c4000c1800070a4100090454541003007000b488174078903449400a2928485c81d076400341c0200c1100301c40f19203009191003a0340004450100740f82c07407c101414034502c4e41d8104020075680c1d14840250340141464100385003001403024601e034080071044402581901e03a482041c5460b030305520010361080703585500c042c000d40202d911040070800e814014040c1e4600103070444011000034a07018010300d0205c03c43d4440354502d00084e40c0b010b0302c030500d582c1c420800202644440c0c44803290300c86c0b42400100a200118000480030800c00340d4500f141d001d9040b403200541c0380c0008405a03ca0200300c0300120b414001061680302d01001c0c1c00424170060340c501c0d41020780101400d90707626071030740d01941c9541c44500300c148540b901d401c0801d45d00c0c81e80306400d880c100044100c9415a1102d0030a1203000400310b0004050000d181064070003c224000b031050034212009482c01503820080c8014090800c64002404c1410b20340d00310f8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 166845368 1250 166844118 166844123
    0x40f14010c0c110405070215100f14210c060306030a02030f1b04180201080405070503070603090c0b0a0c0807052103011706010b030c0906040b07030804121403040b2203020d0f0c 78
    0x510315080c455023424074250024102c26058012818001211407030012420f01510a10f9030104044115108204142c0c551940c042089506500e6402c100d0b00c000488003d42501991640c0c0c4903a6040002814800002030294150251030841e4000321008030b682034421040d6041d0b004038902030014401168000001c2c7c41200080d07150600266000348100c036400380c441c500321a01c0c19200c0c0040ba0400344985d111801007038480340c42c0810003800e103502401a1900b06200c81c10b012a00500600039a240b07000548002c10000715001030110500c69203d040300c03c03800c1d001c2c1d0728002c1c100c85043c40d4824070039004400c10002d1600c9501c0c0000c03401c40d04850121100703600b07640329503540c40d8039503000201459020b101048005000300c1d58070003a0102c103001ea00d55a55030300e46410a481d078000840301c110100b21801607065110382c03a00f01601d400580016a0a8907540e480343c03410440c10b0200d18405040c031600c1405130070194000f0f544046050381e580c540c6400140b1035819200080c0c4000e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 166846618 1250 166845368 166845373
    0xb0c28050604030309052406040e12090d0c0807060503010906050d11010305090c0d21050c0a2d0609030e01020c033018042003040f14010c0c1104050702 67
    0x216000c2032298000e0158980200195400f400c03804401e1041c4d444003d20001f0f000410100b00292031500c8e100c1c40658a01d24400352042e5100c2520006003482410b01c028880c0400b083d0141c00c0c07110200340d0390301900840c800c403400c0c40e450714400340c040d070400d04c662a441d0382405000724060420030b444c00136990f80301c2c980310801015040154040d02d0010211140c174455805203100940e00d02c443c00d0711640c000c082a203007500c101d80480c039103606034003421002d2050400140180800000f13401040680044a01d098a8124540e0a480341d442c228100c900c501d0083c41c0e001844819804014000e00c2615911041e0100c1c0c401a40c64620707000d00710354190060421043c0718214100c0955100064071a5100c4440070441e5404003034000b00c2c0712051504110b088211141070501c41c0c946804020030090f50040d030f515011545a10004100905c01044010f5003030802031a100c403c0d110450303803802400038180040c002000f17606000740c25240303039172405010080341c04d01c0d1180d02e00455141d0301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 166847868 1250 166846618 166846621
    0x70b09031b060c01060b120105040c08010905040c051203121f05040911040c1701060203040509010311030a0507181109090402090c160f030e0a14040e0102040b0c280506 74
    0x2603101c022003401e0640d401250030040c1140c4000207103d110040c6c802c0d08521529247d82c04104088039205800240c012860500c155a007990040c80e1503045030319100d8040ba1035641e52510207034240c115407040c1e4004408030100003110700c0c0480508684800b2a080d000c050f03440c2514106124007103242c02104101615017030000e41000c3e00942238881c0203800d030980e055000f01c00304046481034480500018010a8524403103040a2501801018188010340c2407608000001d5020172041c03000802c561483d002c1c0d0042a20284400c0300c1c00c540100c1503460007a51012081580c3d0080c80e00b00800e035151060105134a00700105640103250058503164a41c1d440b98240310b4400c4014004089509040c0950652142c42001c1081078921500b0000022701c418034015200c6000742039040e11813803007504284a08a401c450f040798080b030807903001c0f843c24105290386009211780e0300b10f00500e040024a10030601400100510360ba50707290291508200107507082641c141ca410780003021038001c5030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 166849118 1250 166847868 166847893
    0x1110f070311031b0f0c130f18080307030e0616050306010c060e03040f0b071101030b1507302709140a050a090506010b0f040b040f030203070b0903 65
    0x3514495100c1d080c00c40b100780750101030b035141d6000005003040c0c5150305101c111201c4c07418490340025404000c014001c41110000140710001050034603071003030703079502d0071210160fa03144c1000100103541c9511070894030720f900f0b1118030750f40308440c190301181c140f9104801c10320001a0081c85060352074076040e0700c40c645a100316030135400038141030b0401844040003400700348107118020b1558180740c019035540e031a008080e013210352a50701c40111042c0a10240d00890342e404080d005940b024a0b00080d81980000000c40b103d9140450700300e0712901150400400509221041494100d403513001d06d5041240b401041c99a01c09800c0d0300080ca1003c8400d008000081044103080702e8920003050258940905408030f0301d030042d400400340001d4083c005400128801d00d074204000800500210350591a040d580d01c05c1842030441306000090070300c006004e0801581c001d418410032a0b130343c40b6610601c91904048500003a0301c41e01505900140b0400400205c0f4400d850140280000e40c060070f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 166850368 1250 166849118 166849147
    0x5071215060915140a020a060501090606200f0f07032003070902090103020403120315050a120f05010e060702070303020723010c02041d010207030806090609010b030903040e040b0a0c020111 83
    0x700c042c20921001e610300d1500c04c0c42c003401503c402541640241002009030500c40252030781a4030072244149001001e0000c60b901101504034051030f203207181c000c0350382d610206140c00500300c139200c0d1398010700d14000c49294001c1010000c0341d002e00c1c10014000d2102c904845121201d65289616511100080118426580140c005071005050040c18035689031161409804200c0703108000903520110004140740c0004d005014000075140e040c0710a0604100041081d403400029000c2c0030b5042c0d06104012003500140741c1c1d19080350607a0414201710034065070302c010601048001d80202c0c3c0e0041340481c2081000c941c501d006280342d450b4008420010b403200c4183c084107030782098035070501d2880d01c084000c0c1e445000004100050f503075102420000e00700e5002402070743c8201802c2c030071300426a427180d460304c0c10356285810403a504c1c5c940c05d080c640f40d40700e26801202c44004542c1000180101c2c0b0400a105160b84001441040304144040b42210104400e140c04030005000007051011071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 166851618 1250 166850368 166850399
    0x92a05070b0a1406091b070c0e160e040e0109060e0a05070801050601021005130f1104061a030f10030c06081603090209010e060a080114100614070222050712150609 72
    0x71b108034010f2800c46800c058a00307038001e002c1900c01031050441081403440174004142d20003004845400000c845e00c0c0010030341c50208042c01c0c0f02d582c41c2c072414010070707100703604c03d480c1c155228908210003102d11142940b40e070050001650319000d6a9000550800c060003100d1190340d05038042c06031241038a4190006200251500040b00c07146c4080600144c0400008401a0701039500800c030032440b8420001911000c2e0401050b0090300101d24550001e4241541d8009007024140d800c1d035a42c0c4046903050030200e80c40030300440d002c0d40f40019203d4108403c40c1c0104070602c4041442000400107405440343c0d01d0f0002e4008011400400c000107441702c400740c01000040c083d41a0981c2c6001d030a00b56403140a035007085d0282c402c20f10480e00c050202400082c8607030f0411031700d40d85012420707440720700903450007a000d0142c69400504005440d81166042139480c0340402c0f040c00c0c8a40300401d0641c1c1c1c0141d081c00a4030f080794583c08180383c1c4803070104030b80740c59035080c104904200c8003400700c500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 166852868 1250 166851618 166851631
    0x14100c0807061b0908010b0f060403140a0f030503010608010902190c060b030102040e01150f090b090d0812101a0a0e03010b12060702071509092a05070b0a140609 71
    0x1529103080300c00960700811041030f458569076110115080c0000c0c00c0c02c603441c0c40c010b0791040c8050703048103415031070b0042954205c0b5040000c600034801f00640540c200007024000030304028414a9840c201900f000c041d50513250161713500300d0039a81725a5410101d10505207003200076200ac2141c80d015910403031040c003500d0311400340800c1a4410f60042030980e0001d80003444200803610043c06070564003140c0c20522074151904c0702030244402c40c003502c6900103000340904080001003000140d02c0c0c01d02c8070035150b644042002d6171b600d2009106100d00c03405031206407004250b584001a540c080c05661030441348440c1d030031403801c07042203800e82d10107601d42d103c59010b541342c3e001800c03140d079464600c1c44a1030740d41c405460203140010009092540c0b5410035203c0034000d860031011541e01c511480d003a60240c02001540d0000440c1c01c02c2590503400402d60030b01032480040020551210281482910903030882030341da150300e0004020b030380c0b841126001c061071500c00031f0321518020b484143c0149 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 166854118 1250 166852868 166852871
    0x40203130b090f010b030c0f01080717070503091c0f0302090f09010f05150313080702030f1606030b0a03081204020a080105150a0501080906040215040b07060614100c080706 76
    0x100e4555503141c01807421100351100d60440310b141d44020b00300380900e811071402200a40244000c3c103000840d10449a030100d8108907500000409942c007a000300191900d041a6200306031410a00082a07603004880c1e62116002c0c411018140d11441a519171000f0404d44401c5c2c503200003048203d00039088082c18a9000c1d0345084400c500342c540c24416806400e40d45c215018140c2400700f445114012030038100c407100400c02c10041e64024141c00f40d02d41c00d50001c1c3c0541d40700310b01d0000034075016416840200e035011300c48850200b81004080c4608440c0c00e074405100140656080152000e514880078124000400c60360351007101050760603a0051008024040c0e8039140c02c8210300b1290211010700b003003c04d190301c9200600d41303600d04030300407c0d0074a0700601500d801c0070071035141d40340680000d00a1740c0f0500c4425200329440e040d240541000f59000340c40b003210b8200100903100c1c5100300890f82e074840302b8488560a2144920602c92010303241c1e060414502d81e03440016030311004040e503429 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 166855368 1250 166854118 166854151
    0x3100519050103051305190611031006120e060109022109030306011823030c181009050c0304031805180f16020d0503092410060c11040203 61
    0x180d69420300e0150800c0604121100c0500381400501240e41c0541030100c00d12211324207100040c000200d40011242442d0489104010303454404080c214240301901404008404c00c228941a2440b540403a5907650706d5150080314055007400f10b03600c401c0780d241290000342c014802c29015070020721402c3e061206205e03040981ca287d199a4900c01c0e100011319030400011b01c0b03201e40e4001a00711b0000025000101c10500d040941c0c0f444517480c03c240d00c0f01c107010603000080380d074051180380e4090320007030080e40e4401c06181c038003100f9990403107421a40039821500822030522030f1145521405050318103501d182ca480e1010b840c1e11100910283e000e000030036000c646a00c07010f801d403605076200c60618219041c007040c8000140001003039220304a0344980380d012440d41c0010a0484040c890030904c1d5661119614141000e1480500c1c07072059103204801000700c1c0403004141d21400943ca00d000c1125242c5104590015010b50007518503804400e00000600d015401941c000414110400c2c11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 166856618 1250 166855368 166855379
    0xb09030d060f06120b0105030103060c030b1009030308090f0c061b010f06030201021b060405120f0a05030c160303080105040221010602280c090504050f03070804060e030607140310 79
    0x160307141034000e500c2441402c441005190b40120182c00780010340542072001403281c500090040c00140f001505480d1103600110019010740d01003854040b001d80718080316121404080d06080c0e051200b01c00180511001500c40b030008564204041080d0006e080f10303407480f00c100301803130300200c50a461498488880041441092142c40b048214003c00132800c0b62035800064108580301140214403c2e0006d04507105607102011039080c0c035400c8a42c3c034404100b6078809440c04210a503c0e501d240f00c1c04040409101c0c000025254041d03035842142c0d45180ba041c4502901c510b5803100401207803003031005020300c1c5001d4001e80121105a1503aa038228070102500c05a284203034800009a04108000e0b01600c101200840780c0b070080700d541c220603540907a5421088410b03849000940c5070b80318081b4041207014881003d80031481c000710303a01d0b41d840d818002c4107540030b4803034240401c074000d0060301a41030220b406440b8850365102d040b5003001ca01e62100084d480105100050341010f000454ac = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 166857868 1250 166856618 166856621
    0x30604080702031e1c0503070207090c03020412060204140a0f0b030703180b010f0f05030309040c03020c060c03011e0605030604200d021201080102032404110f130902090a030b09030d 80
    0x800d10034a400811007075100a03081420b14696403c1001005007c008004411341c0000740307501201c00c0100002010303010035600314020701981d003018030355080302202042408126009003041e80d405070b901d5150308103000c0410280c0c03030305841112a60082c0c64070410568140d8070103150311024904021980312400400d440506407041c2c0c013111908075040062181110385440d09000d00a00b50702101079600b4400069680d0180f014180e20503502d5080f02000144243c040da52040308500484034203040440690015070024042c620900081c6010941c2441003145204201d41c070544440385180c4800e414400545040505896054401803001c0001c0d2481001000c1c01c802d0f0b03042c0184c8030200e84044c1100380700b043e0f018401ca0303030040c0244401c185441020701d80381d061400d03031412540c01ca1404900a0150085110740c8108003041000741d401c0507000421545049121100325186c851030f4270401c134050160041e4002410b0b0071309000090708541400d4000302c005080320308060600c2241c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 166859118 1250 166857868 166857913
    0x507080d0c0f081308160b190b04150308070203150a0b0a050d05030912011b03090201080702010504080301051e0405070203070b010e091209040f0606081f0503060408070203 76
    0x242280d44169016181d5030050190040c445145000200c50814074842e085015910304044d10309000001d00b0109402480c0300d912000380d1100070310306940b07009000b882c0c3c1411040c0d00ca00c21903042520700c103410314042c4102c0342810151100700e90800d055440d4001d5503004240106c0c0c25102d0106039084002c6540681803249480d5103010070040082e00500c007600042c1d83c00306000320410110b401c0026804400d640708040b0a40b040e603000b00514450601504c1c03480c150001000003041d040c0c01c01030741a08043d052a000f0303260300c2c0d02a151200100d0803610200c40c090060746d000c7c00140040e2030b103405c0084180811851281c000c000d1400001c040701c10035500500542d0000900100f001b6140c01c041c2d00611101d0040441807500c0b00400e6114000c00056040000b0002604075841c0c1d44c0e40c0c0104d036039150305081000341644038a006090b01c0c4069410403049920072039103058411240780020103956019000d00300c0d546569a40500b0754022450072a894010000001200c2c02d40360b0504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 166860368 1250 166859118 166859137
    0x607090f03031b24020d1103060d031b0c181112041101050405090f0f1602030d09030306120f0302071202010507060b0109120b0609150f0f061b07090b041e050403050708 74
    0x60303450701c1c0324162108961411f10f0840001000340200034995a500042410154050800e440c4440540440034910000050020301001c000e040108860710640b210180701c0001102c20040d003458000c801074940502c111b8013601c05660400907001a00c1b0701c12075103a00b0018100f182c2040d4680e000214824001c80b0050340081518007009070f00300e051251590801442e01008510301810349009489210300c101500c0b03c56102d107500c03810180301e6070081c4001d0210300c2030580c12955915001075001d51030300058005205265010401110070340c685051245c4c140c66107403811100360341c0c01014012000200f41804181c440c0003429000b0350440001191007103000c0b68240c5070070b004000e8444c50190409502e0007201244000b10b881e003600c00b4070344000813140640e2070b50b5030000083c441c1c4586000c80b5035820f0015241c524244001a0302803c2e901d015406019074111070302800122030248024000e40d180c4542a0880301301030760700540d04280249042840e00f1003a449814441d444441c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 166861618 1250 166860368 166860371
    0x10e040201140c1e070b040509010e06030705100509041d3a02100e1f0905010f1a011b0506040b1003061b031d030307050903031b0607090f03031b24 65
    0x346013a4070148058005000b001400c182440e00303010111f60300c20700c1400380304500080300e4045941c80e542080a9801810020200584c4040b001c40042094002d15a0325000c1c030700f00042001c0318404a02041c808003007513801484a0404002009144502e0a8a541415000d16545100d500054400060b0480740b42c0041031b4481c120b036a054100c034000003040a0603000040c1c0380b00c0b500c814556081001e0904a4041030040781802c14a004046055550f4032441c80d0102d003a0015908400c0104009000d0702c42c1e00c03855480407008685890b400c5001001604000f00003800104c0e500100e42d00002c4c2a015001941d45969442c4215040e0004610071100d5a804590b4065458041e540c04c0d4a0141644a4000803441c90540daa00015080303c0a2041c085441c821540303007003041d100102c50002608480b10444040d040d180d02040d200880004c1403840042030344070140002008481d41350352040900185078030280148807031140f0850b90100310302514030241c182c00a0400944040400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 166862868 1250 166861618 166861663
    0xc1107030c030314030f040204020702040b030709050604060f0b030c0309071203080114010c051b04090606090b0a050d0f03260a0b09070306080a081303050706050c011103010e040201140c 82
    0x50141840052122031000d0131420030420007120315860900c0e402507410340700980c45210310320010740a040c5040c4040e4061140c41400a03101d0541e030400d900aa0b0251020000700340c9134003a500b09060140295001514108041504c1026000007943e12030351741d1050ba15202d482c0c140e811840c000310401540080c540b90014800001040070003074510b40d09080c0345001c040603070f8030252151300841d001950103840c101c1c402c8050301c03607030007020f0001d52100301005413a4407a030141d0010b044008055010301c20040c00400c0600f04046ca04038100e4001108100340c4000e65130440d1410440048400920901c803100e01d80054500b034540d001c1d0001c002e000c2100c008610500c641400014011800c0600b41030b001c00074142c0104280441071703044020255541c4650249106040b9203a00082440c0b1940000003070460340800501249a20342d00203010401c4440c2d1103200d140402e008110030a900c55022400640c041c0c105030b51201c00402ca240d040c844102d0382b440c00d11025100c03913407456102d41c2c0d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 166864118 1250 166862868 166862873
    0x9050a0501090b1c0302030f13080c0a0b160303020d0c020a030806060307051e0415180506090f01030b031f0b01080603010e070510051306050702011806120c1107030c03 74
    0x5401d0150003518020000c0000081c00107031181c1c2907681c6030410700d40d03509404007410b1080c400c031415120801c512942e42c48400d40100c284500700e2107046024040ca01860400c0d16040742d101c0102d076164044e40d4103003201c21100e100b074075482c100201c0a042c2d00b0012010f03e0076050092074a80307143c0341c0280071000b0450801030803241700144202c2c40340a0400812950b2a00a03090301d0404001d0840300804c2d01e00d400b41c0d04030320710403031300b110382e006100c0d0720303d000000d130f004011051031a00040b02000c100d40d218180a4940a10301d030740755200601d10b4121180354400e9010304000703030004080704e04491050400c84003011600761210141901da4600c2002540c02c01100c0742c0000e42a8001c10241000c04819911170780180540c07803081c08a11800100103101b182598103214600d44060541942c1d0100500700791301901c003c07404103401e5600a5080c2c0440707600c0c0070849400e9102e1011130070240e40721000030483c124001d0140301c1424070050860608103c1c00c006107124000c481c01031030960 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 166865368 1250 166864118 166864121
    0xf030e040c030b1011010917041805060307050d1b03080c1e060112080f040e0105041d12030c040902030103050708120414010f030f0e1b060f09150f0409050a 69
    0x101ca03040249410b1150f54640740c0c880c8600c0d4040c601862030010380f0f00303a0000180f405040301c0d1001030100d400700c100039510302e01010000e2040701e544411200c6400300504182c02500c508076001640740d0084802000181400307034908606902c1400032260100c2102803815002500d50400d80390080045041103440c1400c00c0300d55a65050900702d0842e00c207003680010b90310b00c0140115903240346825881c1c2e0030011060180c5003070708003080d0000e031540c3d154102c588108400348180d0f44524144900c49070039800125140d280351a8120291130301c01d801f15105141ca0b44054540a42083c00f004000340c0c2001c51b2000d140070398854405014400c1c030344010180b50201d808a0340103d60030400007044130b00e81e01e1070800c400a00a0030200d020403048003047d00288030494074030715454105042112410004580c0c2021000c2d04c041040c0507014900a120050158a48c4a200000208005181c901d400030030010f800400980c550b01e81036030000180c4482e00300b5407201d0316007910b070010700c03d100f2580e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 166866618 1250 166865368 166865381
    0xc02010f0608150408090145030b07210c030f06050909030d0b011205040308060102060703020406120213091407030501120c0e061f0903140c03070b0d090f030e04 71
    0xc42c0000c000d05501c100c104004110050001481210300081e80901030340605581940d142010840650151561303403901e04181c80c1c3c3c07440780c0542c44100e880500c1803407000e00d52001d6903049007041e0f040e5a40e47c01c040d502402c003c2405010501950010208003030f05000d50750141015a8020500c00c00c40e00000c410340310503400152180c1c400c00100401d4210020940f00c118411b000046040f00c40d00c00141da40000d425000c0500c141842c0c200b100703160300000c0c014042c41c001c0c1d0031510140e0340c41004404a006a005040c0011003500c031040210500c0e07005000b1a032000307104962415035a1520f0b0040302e072407e51903035041104d181000051a01441307514010100500c08950901c6903658100e04d900050243d8811051000b0114815031903181c2d495803d20a44030110f44080d4000001600802d1144001c981e080c17890035403460088800309810b0040c043c06801045a5070038002000c40a07000150380e04480c80e6070385004008101c0c3d044055030054040d440d0350750355a60a5091009a83d603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 166867868 1250 166866618 166866629
    0x14031009060f1a1c05010b07031205040206030114030c03011a01020d1e140c010c020c131b23120712020702130f0e120309010b120a08030a0209040c02010f06 69
    0x305001c2c2000f100031814500c80d80111682185030f9a80d4450b450940034441040300c000c1c407989000000f0801e204c0260040040d14044e4882c440c0c01041402402c007610700c02c64000b03400400c18001045403980040703e08408440081c25a000381580720042421503000401d1052a00b0b1003409010b0a03580622900c0507440c4217140034043c0502000c0c83c403003c0f090010f000e03400c112005c18804003600e075590640d403140940380003d00001c1001c60000356120400d02c1d01c20720455404603001c042d4411886a2030101000c90456001c0c0c001c0e2501c191000c0c17004030f4141254040302d050400860749030a009104000c851131221005042a103c020220143c100c11a00303070a10401440000da42c0340d20700d01500c0ea81180000c240c10348079000c10b00160a042807900c040340300c0c2e07151103180031700c0301400741d407240618034000c00c21845d0741c6003044004074010000203c642c0001c28002c02103284407000715805035801d2005840c1c04540008141204d02041d94480183d541728480051210b660090100910 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 166869118 1250 166867868 166867889
    0x405060103140a0803150f0d11040f0213030f0204020c06041a10081c020c060706200a091404060e0103080304140303060f0d060f02210106030204060503070309031403100906 76
    0x4260340d5980320548400340c91b503078080500c8a402d05450382c2d04400111445005402d2204e80c11003032030b06450100d804401e440c851410441c61150201540c800d0702c09069412103a000d20520b90385603504803400081d07090b03800940800841d004c0003020055a8052803054a14086900d8107544000c420000540359a810300c044460800c084c0344001001c00408059048454240702190740603491f14500f80c8856400150100e0440103019096001d890207480c800001d101d0007120030a06403640c403446400c03001050440109000d8403080020796000a40080d000064440d101d08503400002d909a00071640d00c0400010401048a112040007400f4050340055041d4280311001480d689804506540142d09050301e102c184103041d00550306001d42d21b20111342d030341c0c9000020b81440c440482c051001d02804000010054800e03c2110304940d00c41e5070b600e09640f03070200e04038082c212198095080081c044d00084506c61200c0045008102000180d040d55103040314800640d10960b00004488 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 166870368 1250 166869118 166869133
    0x60603070c02011d030105090c03010518073f111e1c0816051e030d020306030f0706020c031b18100b07030e0a0b090d1415040506010314 60
    0x2141c0210740c100c0303840d60900b411420303001300303200009146000c00d009551660804051040c40c16010031a00018801903009010f00d0756292541c1089941d800540f0100f039214540400025540381d0643c4042c142d410005641d5041102800c0b41c603e010050040c2610072401d40b078420441c10441c180d8010310b0a440c1c00f5040c0305013001c0d0201c0c0014681586010341b41d01c921901801070201c0c4030620f0a68840c0340f668641c01400046104412003004c12103a9108a80c65107088816010680d003045841c04003c518100044448001a401c050030543e054800da8030707401d4030441c090051a002d400b055004105640c00101014a41503414010981c02906a00c4082c21368031211800001d50341d403040b09400b02d441e05c80902d9001400e0750b1110404210103e0000b04065011035405114502180c0800da081e071100920070702881a41c820540c4003000e05946400a000e013800c4518904075001542c000590240da0702c640e012048604440a03000700c40140100403071030a802c45140070040041158 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 166871618 1250 166870368 166870381
    0x9060309170a031103130b100f060518030d1d120c0f030c1c0b010e090309040e030c0a030504090f05130f060b0604080a060609050c0f03130c030c0e060603 68
    0x101c00d8018031a407941c1030000b58411050f4040d41120003815500c543d035994034070b40b42030310000c5519500d4049505500440201d8150748045544c58181c4250428106485240c40c60a40b002c0d801074a61406080b20080400102c0d038041c020101c8142c09a2124940c4520f0402e00b4000202d864515a03c00e40e40740c590f400b50003800140d55516204255540704601b50380d0f100280c50709411844103a800b8180c01c60300c00344034021003010043c0310701c1421001e03810f90b22003d15400c80c0d01d04070351030245540700380f040d094149815008041c214450009a82c5030901e4010007a0611001c4142600420b4000a00f04072036080b0f0702c0382c2d8001c3c40210400308003500f806500e6014011100d080a40700e00104030420041c001540e20060b4004002405150703120758602c6d04a44602c4a0702003582c5585c40c080c40041c440c64203002d01485000b422507407030302d405580000c42c00543c202800300b22001c04110241070010b0300402940d4061070003171680580301450803400c804081c4000b0112070040d1000e0080c480d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 166872868 1250 166871618 166871633
    0xc020105060f1918090f03092408161e0c05070e0c03011e0807030311010e0109020f010c110405130c060207050a03020607030c1506080c010903020303040603182109060309 75
    0x44c2c4640c041045624038140b40000007600754034001074500c01c08410044101034009500e407086400c107041d08070000240000d00018113040a07000000305108800040e0001412540840c000340326080c03840d06c4035028400320000300d11500c0c001d008120042c80c814207210302001442c0080c94881000308151508400a41040c0810320600c8114068001000b03010558007521707401400070401100c401607540c0c1001056034515594288140d4038243d010224090113021300b0118540190110004030b010b100116010786d10310500391401911031840c007000381d4850003031a00401c80b0401d003002030300003400c041484051951100f030543d44640707010031154079030301c81880880b42c04841c00c0307465200504064660300c0c440d140c010040b401007604d990300c0c842c0d1603000e1001e81d0b03800c40c110341800340f13460b005486400603404065170542c000c1c0300401445129410038080c15a00c201e40650813150355403543c149041d403000303407820450f10240c44400958454000c0d8010f100602c0e0500014065885104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 166874118 1250 166872868 166872919
    0x15021e1f02030c18120607081503060601020a020f0609151902030a020a03030207030302120f10050a050612060406080f01060305010b0402070807111903150c020102031023040c020105060f 82
    0x344c2d0042440700408981d0300c0078030485802040105071180c61420300d0004080040c1107454050745c0c4012507013010142400180b0510a100680040468018036020816001c0d21a040340707902480c20081d044550300e4880460000c01c10170113085495101054024a04803420402e03002194002d0110101d51b950002e000c4006a13090f0500603910005420101c02038840d2600c12043d0004031814408250103000c40d0307500c1035582105002c28039403210100300508907107114407a0300520a2004150f2415031042c000d800100040002070101d58840216080030314085054150303940d2058208188035003800781c102c1105040b03800b1898450242da0301080d5004412002d85641015202e02c40251241150b14802c0c01c0c0c01d0f803030100324039501c0c80e12500c4140c0c001b040780382031410041140782c040d0050007540c2c02944d01340d8110b040c060a007085409007808000040782642500000d5240d16210f5104545007054594004140e030306c1c140050104810000c0c0b440d0b8010030f14030740505031900c1242d4910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 166875368 1250 166874118 166874137
    0x150c080f090312070e030f0106060c060e0a02040e03070b01080a0305030103231f0f140f091c0503010905090a23070f06030e070e1015021e1f02030c 65
    0x2429a100d20034540c1c910302a483c0c1d0044505414402c2c0302882d50810681c0b00040d07800c80840d200d03080c500c09400d007694214825403000c51511400c02e800a50290803000d40c44045100b01c2d0440c3d851500090160382404a010b241600005200014060704c80100d078098800b400013825449101e503001030242c481440080d19400090002c54813011480340c10300c07841c0d5000002c03150408c404000c40110401854001140f00b1701e403404190194116018680e0a0780d080c1c09940c145075a0350000440e01d0b1001044800d460080000036494800400c1502c2a5810241d03519a180d6042407801e00c11680040c1c0558007980c8507000c1100082c400340080142d02c20412141e001814400323045518200898018541c000b41c0900041895a4168802813896030008215070010740d0b40c400c42c3c6080030342590300308122181d04009020100c2d45a40c10345805102e8411184107400d0704400c400302c04039042061850303030804000e01e43c001c0800240510b8401100404610314141035580040910602e03220 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 166876618 1250 166875368 166875391
    0x503010303110d0f0e0f09010e0106031a0604030201200327040e0d03020a090b07050f060f0709120f02042d02090105030610020a020a060f1d060d09080408030d0207150c08 75
    0x849001b5110340040081c180b4000e0484551961981c1c040d8441981c2400f80d00c1c0040e14010009505003040d49220710301c80c41c0036200902d010b00b9a001184c003061414455607000c02410340e40c16950100b040104a840310618440403680084080751000700f01207200c140c1702d07074108440700b076010b40003090704916030465080050380c600c807101d019282c0f000790354825040b5910200c0d00348240140130512640c014442d1064446950721201d418540203002d0320030b2800120411010700002520580c0d180c03000b400384140860f152965400501a11903c1d03d066284080f02804001e5080c4400303007014008803440000e40c00d10b401007000030702601000b00003521802c018102a01003d0081c80294521a000381c030500c20580c6600300903001c2006400300c000026008807904c8038200040b04c0383d9181c820f0040c20302303182c10884d1709030790301415441d201540e03181c504000000f100027003000200a03518004101503151a800c0c14a442e164604104400076075003800810703180d05600c82002548032007000d00c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 166877868 1250 166876618 166876637
    0x4110f0a1d030312220309030b09010f020d0209030d0201020a050711040b032a0d0c0e0601110f070305250302090c07080706050105120a0507050f12010c0503010303110d0f 75
    0x54245030119850000740c041c000040c04c1010344c80d00403041441000f11a00064104103100d030008007001e0394100140002c0d820400500024501111254200f840d200c00824106003c9104800302d91152040b0105c0b00d038002842151070030107000c43d40740100d081c0000c500301020144041c24510400e80c0c020480c1e8060907540916544035030200e021103d0190444840304003c9400c0120048445141901c3d16000102c042d01d40c6845d000c810301b159889840b00d0105172900c0d215402095000e02403e040c8241120850b903000810040c8042c2801e2034801055400d00e142130550800c40794020307c141c1d20180001c46aa0541d010002e441143d40c140c505502642c2c60050900d100d01468000800002d4001420001c4c02401e40220f41612021110780c0182030801c0782103640c0300c1c0f480e1f00041c595084060200035514158481c03450022000d040f0115030702c41c50000a003114502d0020f00e010610100050050691003801041d40811910061403c008410b17030140c840e121182109040040d41c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 166879118 1250 166877868 166877897
    0x6090d03052101031719111905060114030105010b1e0409050a0501060e010e090a1e050a02030702060c04080c0f0d05151603021303080d1409010b04110f0a 68
    0x807506250410b002d001c01c40076160049120020007884242d4a448941100d00030b18203121040301d034103012944081d00b218101c00415113203000c01d144030749020300910554080d1841390000c0c210f21a446070000e0130f529810203610b02c2d01580c1c01041180a07a1610b401400940c1819044420000c41260a002001004c104011035031140c0d8200541440c20901400240142500024140d81594450305401819000115261500c402c03900d50300c6440c071004242440c00551019510381141005c3c61080300c8290101c0303050b18000c2d20103a80003540001007020607a418003540d41c02180d020701861030b080c54421840da5074103046040910620445420341100c1d03942e010f484904a03884400c1c2e0354071032200c00c0b1210b1808400c480503003a2440c0810300d410154402d20850300070b031005000511480d41503445a100d141c0191070201c41c615aa41c07001815100800c2c10148215a40c2001161741c08461050009403012103180560ba80b1040c000c803608041c0490a403640c00500f40782c0600c135516040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 166880368 1250 166879118 166879127
    0x18050303180705030d0905030c010c030c0b0a111c06080f030a0e0d0c0b0a0207090605030d050c0307020d0516050a14010305070c06020c031b060417130305011a180606090d03 76
    0x30340c00280d00d0301c05d0b00d1210b00c041e6003010011044546c01c40c142e6451007100c03401541c15282c1d02e00c00a002485c040d0603080043c0c036030310209400c0900b010002070b9079094890000541e80c1b0810080005c0401000b130080d060210b0301500e0040d106000290403034584490f8500c1c0c0e00d0003200700f58410f2004031280821191184400c0106042d0052021242030340e039904409034a5100d800203038014042e8500c007003080800ba004007411039101500074605102c5000003110103401a5610207140e02041001201690341c6c0c02c8020361081c0500d014040d8280d01146075101c1ea0f84580c8403078082c1031503607070130403501c0425443c0d4444c441e001c3c20f02084d180c0e16507070300b01d501c0301c074010008007000d2002c0390450400e030001020b01420f0300700a20a210440ca03030351056554030400c95000b85528020001032012030b120002a000044410b142140e50300c0c0c0703a42c6d0712800e541150317515000584501d9200e00300303860055050020703005240b00a01d40d6041c00e030f012030748074450510501c0c01140024410000c16109 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 166881618 1250 166880368 166880383
    0x5100f050d21020c1906200304090c14070605070807081009050601050706061707060504030507090903050c030d0c0f0507020307050609060d110703090803270a080318041805030318 79
    0x404607644241c80f0b917079014007041ca40c020080041e40e62140d86a801e186c000140340d2401501000b18282031030304c00d00c88050a05054401c1c20422988907260407000c100e0040c00400d4444c010220700c501e0581c100070301c071034801443c5c10108164403082c00390078070004034504140d0300c11540c04521542c0e6000187c07aa4450300000419503440d017100001d2070380121582e00e0b50017400744203440c1810b0f5110b00850350343c041c2e80006445600030400402c9120178561014a0700c83c03007410b00908201101c00c440c0c0c02d5411010300c12414a413103092a02c007031070740480c40d0303002c0010b103042c0f0a0808015801182d82e800c4940210340c01ba4200241e10416130780c800c8140d43c00a0510001032048030707120314a161044d0007040c011804100985008103441c1d0b40881500c0170342200e410a60300c4809207171701d85a048050031100d6904604a4080442c0f00e440038001440c414449510741000d190b8004144811220b0b10811400d2107102940c1d2480080c5002c4103d075000381c0c0c4440f01c403802035130103c8a9801c1225 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 166882868 1250 166881618 166881643
    0x3150902100e0108010503150a02030711100f140c160302010b04150302090601030204030302120a030f05240a06050403060b040e0f0d03050a06050907030f09020405100f050d2102 78
    0x1c2200504041d0b409400444004800c0c1e0740e550350f990f03a400625076030381441c1c002c0301850924400003c05019240d400f5581c85251460020a25001206040c0c2080d000000c3d20300d07400e031034014481c80c0c2580d41c0140c3c980d241210705441d02515002062142c035004500940800f00c0352100c42d5024540300350049012030200520400c101e00c0e2242044041c54480e00c0202d001e0030048c4006602580648291000c80343c041e0003a008001a41c0e41c000301c036074055941041899600c16a10501760000e00c02c151040501d1070503604070003140e003030001c800300450944030301c6244503400c14441994402c00741c8045941c018400b2590300701c09000a0098030881e00e80760014458241026400d010005130f80740d800085032800c02503501c600000c80180c41282c000c540d005110040810b503154031907440b080000242d400000341480c05540040c0c00e03114240ca074282c00490b040420300400703610b04c3d0000028001100c41c601c605802d541c80c0e48490454410315070640741c641b445280ca0a000348843c0e0400702 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 166884118 1250 166882868 166882879
    0x80a051804061203020f1203040b040c082d0a0201050d09020402041a03070807020705090429180c031f0213030b280b010917010b030601080709050f010f03150902 71
    0x29100c03420000c910f5286038050380180b0803802c0340c0c03072850404500d0818400d2100c00300307840c2d5035403502c99102c4d1900241c0110b44005a490700002e0210040c07220518040d00031044c000080d4286071126a48011002c0c4030810340c00903424180107070303080001c0302c48841c032800c00451301f60b80500008009009962041031a200301003103190740d090418008500c42c2900713448a0a464448403022690b40e40a0700405801041e8640030802046418440100c80c03070700410040c0048080224019545500ba9802070b42110720b410703025412203050203a040c890405400812007420482080300c1d040d290481c0c0750b442e442e4002004ca034400b81562400b4081c5130003210700d61650800041c4441400c21101241e880b103005e8448804a100360390090304003e0805075105a01a414046034103034406c00c480c3c1c0c3c42030543d80d030401541d03581c8007805220300a02d404c0001e00709080c90100d10000303035040240a2503080311b440c0014004407480c480301c0f4080c0c0ba04004012580511005a0703030040c451043c0107036024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 166885368 1250 166884118 166884131
    0x717070317070918110f040602070e09030301030201032712020d02012702040914060618060d0213021908040203120306151309061806050307080c060d1803020d030b0d080a051804 78
    0x241b06d404000d03c21602903600b215103c9661b080c15022041d002d40d201030140d0030410040001d517109030000c0001d00da241c500310510300c84c406040b40600000c4802201d9003551420000500c0760140801d160000d51070000b445403a413840c07125014140e80e07103003e50780b840d2441c0c4503500f95105c0d42e0241c480f0503440440c2e40320111406d8855031340c3d284100e41040c4940b042e8011b2501c21481e4152045c003610300030303042c600307850180d500300441d40f9102401d022803181d00344103500152803901e41d201c1c0c1c1085191075800c8682818018141030051031a265444a81d04100384030254035003c5404021040c3c1601007a111280d00503d60340c10308481d4040b40394281032201c04284d69416a00080c14001905020041940d81d0070030306890300340d5442101400d405c10301c2d12403828241940200310f0810800000944400d00d1300c03400c2070324943c0c00000d40059210f85d8050012940510071000512804c0f103414008540503540c20b90a841641c618004000c40030618240043c00300d86a158420401030003407081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 166886618 1250 166885368 166885387
    0x60c050310060207031205030601140a030915050403091503150f1508043804110910030b06012a061a01170c070305071707031707091811 60
    0x1140c20585403540031181c40440010300c9400041d1840407264065003440c43c1c000c600d0010b03182030300010000c90500c4910b50510400c0c030072080060500b51b980740c1307000a040300700c2e003464442500180012514103141c8070902010a1b08440004221410b04170500c80c41080e1039000c40140c9210b950480b0010070901d40803c003000c20403d4070040d01d0305080c04081c2c60b40d0004048507e5074003590701401c480a04485520581a40d035840200c1007100c0d84800d8554450001e40c10300c0c020b0840d410760340c1e05409400700420303240c180b05645d0803003482440c050b14030b400d684402094003c064116414007460010703007a0850712001d400200d913200c090101da202003941c20300030040c0a031802c3c40c034211024a0003079201c540c09640d840c01003011286c20b0b4103041d5a480070a03806680081016020b20006014150000e0000121114255810300c01141c96054914000c0c02070390104400f821003441d15002c010100360300c820204208c0310b58004a0380058044003c0301c0082c01c0d0b85120440081001680c17102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 166887868 1250 166886618 166886627
    0xf0d0c0312350603160e10240c02011106040f03120c0503010b070602090a0914070e180601110a06051e040210030207030207120605060f060f040905040f060c 69
    0x8410803a48400045000720720842c00100a201c0c00003110b4110070100d03400000000c0c044070303444103000c2c1c101c500c0902c0070200008000199402400403d00706020020140c8100c40c072507000304002144007000f007080785622160701c0705000c5060204110042508196840340c10200140170380e08041d2551414a82491410510700c60401c0d004540d84803200380b403240300c40c0704d112000d01c415590030707003507900344807071103c5c01d40c0700300000e84800780c080c400c0280716078900c500340d002007109610000c1c0280411a86020181c0c0040403941401018a4024459220b1401441c1000c0100201c148242d540c04016203406039914060f022503c29200308008100b0280c5c0003d000d81c1c000c08403d0818101400c00010083e0101c500a4000c4606030324622900d000341c014000c11b510070300507140115165544c00c031010120072010740d08180c644043c480b050814007903802000a0a55409140591102514049104920504805659560009080c03000c0e07818014645640200140400e98400360002c0c07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 166889118 1250 166887868 166887893
    0x20d0603080c0a0b070801140904150c0503100801090209010b030402120106060c02030c04050c0a14091306060806030a172503050903120a09060302030a0e0a080406140304050604020f0d0c03 83
    0x104c0b00304004001c600130354000c0143d24101d407106494000c090a0001c00d00c40111005401100c940303040c080030501c0c80c580782c083c820001600e907640a0b00ca1400089078003d01210350301c0300c80715904d0a030704400943c50f080030b05410348009000c19a40d90b25a07201240c510300c0341d408070718030b95440e200020404e030740c0c0401d003080d009008030700b10384500303e00d0001c00040300c2c4140d034100000346d030401005d0250ba00400990000d029a03180e2242400c503500c01140c1c0b001503107420700051366518203003840003503040284950001d00c20b0b00103208808090382c900508501c8001d103a5007041002c624001c0310000c080c00d258403100313141c405aa44280c14074000c2c2c020740000903050302c6402003003d03241a1128013001c1c0c802070f0410342d41d1810b10914060044d4001e607c042c012250003910341d41e024030954420001000c000748138800302940ca0749001e8004050058100901c3c0e000300c010028040407620000b04242c0080c0c0441e0040c0504030311000280ba04440f5080040412006040000500071100c1059 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 166890368 1250 166889118 166889123
    0xf1204031805190302010c02030f0106030302030910020c030705060c07030f060506031e10200a0f0207080f10050705070b0f0106020c0906130504050c121605010f09030303020d0603080c0a 82
    0x10301d055158000c00a0410600c0800b20080c951040c0c100090340c80b0308514200540050151340c5401c030704c1001c241c2034070015082a00582e0000070011030701d0505e0840f09072400170790301c003030040901c4c8180020307288c00c158803c152040902007240e0000000602031500299400901003000700c10510b0140013501c401c440b01e034842d001c0e00804000f1041c41c900c84c5107800c004440901a01c00748070144400402400a8401c0390196034010118019200c4006009000c003a031030781031105001d018000c1c641203064108541641200d1160050072a000a400b0000d00b80440c0218042d038440d4004c8506000380c00c00908a001d0300018404609801114203040c1c1d04030303070300f55094010341005000702854151003441d0001c170a600c0b0200382d004c9950200f60403901c140107842101d85840b000900e080c003c4014481c00380c1003c2ca07102602900b03029190000e180a0030011030304451200e0150101069110140a25800043c8cc900b0365040d9032040b000b0b180e02128654850401290241e034500c11788008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 166891618 1250 166890368 166890407
    0x606030e0f0d09030b040f0206040b030f10060c0204020d0f090305131a0313050c04051608130c032d0803042303040513020d0203070206060a0f1401050f120403 70
    0x1615811004244841e00781080d0300d92903585461a40ca400c5c40700e00051050311700343d41c41101d01006a80b410000d100070f21112045039220300742013045001d01d03400034083c40083c0c034404004102c0a900181403012080d012500141c98140c1501a64081c000b01002d0a002d545009a00010580c02c100540700c181e001c0300c07800824980300d0001912000c0601da298100c000140001000001c12035081c0803114807030320075034118007240340201d801e4450640315011481c50541e40210101d41c05180554803805000540d0007848040d2135500c45080340d804050181030f03e507aa460454810100c4038007002e0100c1d0011800e9040030301304000c90f40c01c00d48089600c0b0f049440300e401810000021442006a071402031864035150404116001a0310040306403c44d800740039135841c0e00c40501c060341c85224140c000d401c19203003403400c005040150760050403d110b140d100038040f0746002100200360004c2130800c260703507031490341208210340280009291010a080f0421080640c490f40c000c02c030302c148440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 166892868 1250 166891618 166891633
    0xb13060306180207110a2306030c16050a0b0c07060b09251218030908030a02030304120e060c010e0f0f060606130509041113020a0e1003020d0606030e 66
    0x45060312001e21902c5112295014080c001209550080c440036200344038110004880d85c000c10360311080c981c01096030b907161801ca40303c0c0c1003250b01720400b03044003203034107030b186280c00c000e880202c4c084c2c6110320a202e550340441c001006020001c502c04241c1001c2e100201d8a02550000040d600000c7c0803035203a81040b840d6a024181540306501440b8030310345500340034400c00f10300e80034a160201c2c04001c01550520041000180b80f00780d069012810f032035040daa0170f03207080282c000320b8950302c616041c4d40308100700100154084281c0743c01c650322001c2800a01a09607045405c3c03c441780e803080c0d101d0000101c1c0b81c5003500550042490700300f94800d07035070b03136442264055884989241c80804142c00c11800502d9500e4000000d100140c0402c58274442c10781c03140042240707060201d404071004c182c0c01c00c55000d2843c2410458882036001714040d803900729810390003040341d00950b800038041c0c6109030811810501940507500c2c98015400300b0400316598600080c0548400510340495016400c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 166894118 1250 166892868 166892879
    0xe0907090b130e0304170f0c01080402091302030705130c020708030408030703180b160c0e0c0d0902010c05060a090c090525050d0c120b0d1e0c0f0b13 66
    0x90300300c1484005102007500b260201070b94025241c00c0800c850b05000400021601c00c100d41e000100341d0341140001c2114405200343c3d24945141c0701708050620403400e080200507500c90303d105070300405070940403800511170f20100f46002c0540e040302e0380c403c0b12110b4105490f00140d1000541000e15800c5600f02565a03800c0f2b6124440c81c003074001e03a0740040180c90086802041ca50100e543c40c200724401a0b555010800402d40040c0c0780c0200d02d08110710301c0818402c1850b1a90090a0509001c6803542020381000d425440342040000340c45858003060019a8098114020b219800c5801c1d200d9034074241101100900000e00200e50315000b20b540804c411002c2c1c0305540c450b21000200c2d0315060480b000e940700c8804807020f1b03081041001c020a4800c5406401402c0300510a52100469006000d000f40e0560342c0701581e8501510300141200041000d0308401559890f5442215090003041d00b0030301164104c0d600961041c480d000760018511008070010003103070a410f4082d059294807072 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 166895368 1250 166894118 166894121
    0x2070b07200f100e030c03070305070f0f0501021504060924140c160503070507060201020a08010519050402130509010e0106020606030a0b0708250f02010f020a08040b1b03010e090709 80
    0x92080f0f40211606084102d240e00405500507030072401002c4840707002010740060314002050300300300d4060f008007904201410074807004101802c2240d83d0560040c2c20000001c4d580c0c2c502d41c2151185a14003000b04007407100a03030100c042c982c0c01c001001180c0c01d1400096800e001d20003a401c40da503180c580010300c00b000007405580030714100f00c9401d1070084130111000007001c01e40c0d402d40355804204418000150200203860050240f6000941c0700c03101420040c0c14224140d210038041c68060a000616032506c01505064a000b02e4005807144010a003011070030315117400403508104004004100c100505580504a40b0b8a40c200c549030365542c01819260200c0050080c003851520b0301083c802401181d81a901107034502160302144511141240e02402e2010b10300041100c02c1c840014040d8280036141a60383d000348150714190303134180014803401e0001c0c80681030018940118480d9031030802c40d0302c084080644030b0394a03540c64422044041d842601c0d01c014a10a400c6d000513141c41a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 166896618 1250 166895368 166895389
    0x70e12010c120923010522020102060403030c0e031e0c0d0503040317090603040f030f05030108030d0504081201030c14040c200a051e060c18060a02070b0720 69
    0x15a61180d405854100c02c0e10701a1021030350854081108460000300c0500f03030a0052054150140042031a0401c1d415840185034030180090360620504e42e41000340c0d0b00040c4042d001030307040c64001880c103007244080b00d1000105002680c5405000780030315030000502c00510843e0701039801d442000c0c0c42d40c010001c040031800401003c6410500003000400c2d142082c4011001c0c00f440036611b0036002600207140c541c01120304031022a403a0094009141e030000490018020f0f0781805403a55040640e21a528001c14112083d1941c6a100081c200b0005101383e440e54000003100036802e585034502030150201500810324040700b00002220315203400d002c0e2901c541402d440700da8480c2c040d1003454005200c6408015864032445038014005841005074074151601c00000540b0200d1103402241841000f907d10100e032201403000711400d00006008001800c000c85250303549004451045e4144580c540c4084003e210200e00e85040c048290840a424144580c680c164040c002e400c200ca6240c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 166897868 1250 166896618 166896641
    0x1104060906050a0507081215030c0901120804050402040905090d17070e040e0609010506010311040e0c0a091d07030e0303150f0604180c110f0d050f090603070e1201 72
    0x14003420851035000718010a0707109034501c0c1c400d1030303c40180c4409502d40d02c05421013925200803020484041c507007004004030030400f100548462022070f8001012100103004001e10325024907410010007000d4001c031002800003510039501d030365403100e103400100f0048448400c140a000a6010071038454485821614207948500c0c50136100c0b18002c86140c24801030142d00560b40d2181011101c1c9d04000c014421000e4100108262401000042c00d95900f803c6845c0a00800d02c024009990104032055000b1100c408040d120b01c2e0381c5800700e4000241d070f17200b0050407403020b00c800307814803194101d18071a61003900d003441100c030040c9146549200468000302c8800920700845818074005012102d4130f580144544e0402e6100c201c902e403480c0800001110300c6583e08240079146030849001c20400040401801c6100d103503404940c2c844490182801c100000041c1082030040c444082e2951203901030181c0e0b444e4500f03090701a00c00000228018420281c0c01c3d488140c440e0140200c011014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 166899118 1250 166897868 166897877
    0x8211509060303070b0f13020319110a0302060409020309010b0603090f070605031501030c02030d020c010207020f0301050106052203060c020609060109111605030d180b0604020405010509091e19110406 88
    0x5450252120450303101a054407209081217071510b0140c0c0e810003056210101138000311030ad0820038035104040802c1086d03150f002d0300510703e0030805691510280c40071a80012005a5a0313910030302e0306401041060344482c0e02420100500c00c1c440c00014030081400a400110b42034030b83c0b99003003600c1d1400308071401180c00d00256006041c07544603812040c40c400d003500440f030410f40c0303036116035017681c2140350703c00480d81d030100b10304044d0314103600002d1400906800803c019414800020403602c112078400c03c1600444041d000d0507840c08400c4002076810044c1013082c3c00240100a403189001c0c1c698000b01e1140000104000ca018400c2030901c000c041344041c6410340d81d900d0b409107040c5500c000d84031030205000301500d910b0903018031801580000010701798940745107448000c3c0d43e00600380500840c410302c01400166004001c9401000c07040703911803030325980c5003c07a10103a10300142110300511900280038608018081040750703100e0b005824050800c402c3e0780321010b40a0740c0b18801c00107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 166900368 1250 166899118 166899121
    0x7060e0409110423011503110909040813090908040519150c060e0601080a050d0e010906120207051518010b0609060309151005090915010308211509060303070b 70
    0x5141a0340003220511201000191041c282c41c203200c13000c68264452508110283c0c030b10142240d0511481074a607400c00031880c18100340d580402d40001000303200401c018000101c60300843d1911b014080100880da0003402002810b16020110f500148109401011550100380c41c500b07000c1440b038150351100421300c070b103907400000c11624200d2840b41a9845035940f0300908102e9010301440d8042c000540080468003c02d14140b4078240c1207140000c00c0018040c1060700c00e07a4454101001c4402e43e00e8094030b043c442c126070500901c19003600501500c203803000002641d40c2c40d604980b265400c20492002600d02c400b607182070b1443c2402c01607114004103d0782885181c460081e5411140c0303202101c1c24901c810600840b411010340c0c40d0300c407845482c0f80420451034081c0e41d55030f0040c42203014200002c0c0301c01400901c40818040203103c40700c0820880303a080b81c075104040c1c0000002414001c1e0b810200c41a42409208101c8640140d424100144441c03c00000300e802c2141e00c0801101035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 166901618 1250 166900368 166900403
    0x1b010507120e15040e090c01020f03090402130e0f0118060302010203220f0b07050607030c0e1e0604030c0509090303040506160905060f0a08180a0f02060702040e07060e0409 76
    0x514940b428450f03100100d900c0840c9075483d12000341018001203d880f42443c03c00e011110302d000d0000b1f180c181154020703581007440600c080162020903070241c901684414154920498084107504103002c00d030200d50405c614948c3e400b08081c100c2c0e03a0b0403a00641340195460603004d440b410301019015034001c0024003079140c2c178034880d00304020014100e020042d4980400780c09001c81c66105000710300020a4101c06e102c02031103c0b0740c004500e42810010300c6401c410203058898020783d018416040c0020080c07041400700c0b1008002e404c010b04241d0744540301c1c0b4189990900b01c0c0166802558101c000914418000007140e00903038118001304000d0b50740c2000c1421480c0030394400d130b040000d5100005080d0f19000c002d01710f00c003030044003951252110040100450002800f03600320740e00b82003584841d580c0c04146001266000008010646480d0012800314859180003e4110b454034400c0d040070500450070710300b9a5180ea98010300310207082c041009984807031780c020702150080c10340c1001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 166902868 1250 166901618 166901627
    0x3110a050d020403080415081e0115030e030409020d0f060803070803090c0402040608181b2403040c0503070906030312020903241e1b0306120f1b01050712 68
    0x410001c1c0300c002518054480c0d50700b00d82c9403c10b92200f07405c813a1400810309529048240140c4c01007032600c1e800c1c003603645001003000030710f0103200e0945c1600104a240d01458030a411484e00201d42d64116582d59668040000007035105100040860b4601080340301440003901030841181c4044c40154141201a1540209544058500d003410310134100d401c190b07611580081c20062085490b204900e14010341da000e1083c1c117901010724541c000314910045184000c401c0e0746461003d48912854010346080740c0302254000d14202070021010080000300300481010006071001942035800300f950b0f4182e14010396400d4000180071580596007181e6205440c2c1c0a0607000c0402011204942c1c00c03c01c10b845010303444c02e1916020480001000310392443c65690740c100c55110b5542403d940f51044004d43c800c600d2a4110701540000004901d41d5075959030082000c0c80344000b99a03864124811070303695110406030740040c404055520107019030240042d0f60b5210340000d101e40d141c8600d0001200d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 166904118 1250 166902868 166902877
    0x8040504020f040801060311040e0a03121a0a0e040309170d0c0c12150608031204120201060506030702030a1b110904080d150e0a0506060711010c080a0203090a050103110a05 76
    0xc0ca0b810030302c000100b0f02d10034054840218015281a62508441002c1c00300303484411507200f0b0a6400607180c0070019502018100d10000d001100150100c01c0042c5030752401c0b0707484c07256940240740403408248a1b100c03030070250145102c2d840e0251010b0380d0f1010748204091b454091030640c2c002c043c03408041c602403032200c5541482824200e501a444104802d0041c0c030300c03030307056074503130343d40d110400b41e001d414401e940c090b10f0703000015810034a40c6054000c1c5040d0060000300081624400d222115000750845009810018680f44d01ca1414031802590b070341002c20b01000013148240710303050000c440d00314a915103411141c5003400720040c4003032000c03d110141c4100d494400800000026582038841e01c4000030030b0440416205191801c41e50140c0030142040300203510b0030060018031f41c0c90038221604203a01c14001500d50517003000584082d0a102000313400d14400007480d1600c0d03980400240201c201c101d400141351500e4100440c1110408440c2d0b04590004000e80b6247c0c40c011405403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 166905368 1250 166904118 166904137
    0x10c090e06031509031e0414010c02210303070201051617191a01081f1203050d02070b09061602060a02090a03020a060305060306010b0c070302060c2a0f030a0804050402 74
    0x540d207401c00540d203d140380f4004c58201000d60004506c403a500c004221800e14410028044141030500b00007641c81403502c90450746062001041d110300454942d081d40300d01a48000308c022810018030075180d41c4950048407070000551030000010315114044002080401065035503036110143c00e050325049000182164005810304103202c40c1e03030b6015000348490030540110740c610000754000050305200d0301901e6414048000b0001910000548114200300c3c0ea00d507104411000e050300b810b95682c4107080c80c40d81c3c8580000741c0c24061024500c0f01d240181024803c41e0015903a24491520440c0120b042c1401a08004041024050550040c202d02d4400521124030f482e43d83c0d001880d00465a40100701107078845080215900d800e0000320300502c404010710780b5011444040c180ca424a034000248155008540c1c880f00b1803041052400b071803004404000010241d4000804107290668a2440b0f007501480075900c0d404c01207411001264044081824181410104000b83d003104020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 166906474 1106 166905368 166905373
    0x105090411010c0c0e101205060f07090e0a090512031605030709180525091203050705060403030203070206060f01050a030c1101062402010c090e0603 66
    0x440e4419400140c1040028480005a0b030384103044038040c15507010b600012901e01d426141c00c3e8010400081885d81103981c95880700d0000100e00c500500316000b030004102501811000c858000d103240c01c100101c40d4442c45d00c035044240440e505d81c4040d0321140c0190174032000b885140008074005111031310310301d010181454500800000c210400100100003498a032045844070003400d009041e0456110340014075001401c0c4c2a14014030000c03508613015505c0d0b0581050082500e59601c1d8000f445190404403e880160000301b901404400c210b0980024001d0080e6441107100c3e480050700d03070402401c000e00e0044014002ca0280c486070384084c801c0da030094182d84045c8224070b4042030f046060360f011603e5194079000c00e140c030341c2000f501180d10000440b055104807910540c03600807081c4420203d00361041d5000c0080030400360300c8140030b003610140090351300407006800c = true := by decide +kernel

theorem cover : BRFrame.Cov 166726618 166906474 := by
  have h0 := BRFrame.cov_init 166726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 166726618 ≤ n) (h2 : n < 166906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
