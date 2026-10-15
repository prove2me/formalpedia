-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4468
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:42:54.428771+00:00
-- url     : https://prove2.me/submissions/8f3aa317-1707-43d9-9b4f-d51b24810cc9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 803417266 ≤ n < 803597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 803418516 1250 803417266 803417273
    0x70b06060703120f0e0f120a080c070b042001030b090613060b03041113060609050405220b0a0c0905031b01050d0c17150306190b030106260a150207 65
    0x34500300c2a903d10780412801900e80403100007000c2e0681d064401e1700034201915084580890410303450188800460329209241408445448004040c1e0308003007010322007540851082880c15204030301c54110317501d505002080c90b20301244c81c003c144d410542008803050071a181c554805030060030594035864200300d55210301c1d02501e010740240500c0301c0044100418041220741003104d0710020f03598140c040d8140c00b00c01003640c03010700500000c103407107000400443c01c1541c044c03a80980c861f4040405150700260081c0c1100a031901030300e00c18410000c0c854004014030030f50034000b2141c24030000d29407502e4046070b25048036040c00c0b0703100d96a50183d94404d03402201154204030001e1030800511031411000b030560001e0003201d45440c094607000600c14240e6101c410302d100002001032101c0da070fa11240e030800180206184040548890140d003998909001d4400606060b055400c1141e07a411032808810034402d1031034005900c50f9030444080340d50412012080d054036140581d40d6561030a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 803419766 1250 803418516 803418527
    0x30c07050108061c0c0312020d05030415090f200607020310050417030109020309070906030f20130b100f170402063006060f04090f090c030f031103070b06060703 71
    0xd1080f201400c0c1000c060081001c22160310307046e42c1c410384181e241098004402c996038030110f94480080f036410000305021444400c40d01803030350b001c01400b044900441d0f4400503916101c40c0120f65038200000c0c42425184440c02403440c112080d558607040104030340009640d5048003908452040d9110003041c2401440c9290141080a0310721711513403560340f854444c00962040702c0c2982a4000d141010600d039841307020348011a50000881d03000790b40380c2e4130f805119002c008511401200001645181d50300e450300140c140710366181002a50001c0308080c81071000e441100c0408200429140304a006d401ca480c1d0460f20040580300d900a50342c5102089041c800d024108522450410411185402101c0360031907401007034201301500c0c0c0342c034000e00c8528041c290001c90a28410701040c0212400d540c840d4510b40c4181e007010824510940352180905e140307401c240e4590800c509a4028160016120380d10b09140b03400031441e00c0416200c0c10200d0002402c854803d42000601506052199 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 803421016 1250 803419766 803419789
    0x140a02070620070e070905010c0305030109020a111b01031a01050313080d1505010f390204060902031e011202040f151e0e22240605090108030c0705010806 68
    0x2d0304540d00542c49444084901d90121138000010b0040b90700400d95503c5988200b5601d0390549803641143d082c42005400b03034001024030010030090100008041d6010440d2043d0526100403599802d4030b2200014250388400d6070940d4000d1003820030100b6640d20400720b035400215200407803500b40703652410805611549401015a07400d00c190101c0807a03c4141d10b10403100e007602c03044c0a4100120381a50150700d0711090000c490380c1c0710041a8900c14100b071014840e40c05001c1c0c0f4421543c503038002412540150451407402d036000c42006110034201407102c003008401d0030171900742e40c901031a60b55003030b20000f40203025a0301e40c13610340c40780e11060f004103d01c9a80c031203140c0812600d072680031040e419940f8103a1048007041e080054042d141c0743d0b40c5802200e0303140394100c450801032840180442410001c5a640c1d12410014821030b040f840d01401d40d0030510400300d5001d161508102c002841078000c1c24407a0404c00000803141d40000b195021290f00703003403c0ca090b541c0c0c0000910003c01c031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 803422266 1250 803421016 803421077
    0x7020f01090b070804090606110607030507020705150a140304050a0f02060412110102010b0d020609041508070906260c0d08040503070303050c01050a0c0f0c02031e0607140a020706 79
    0x49001010000312130054810f9440c942004c0203450707035450089680040302282e10b0080e800000107c2e410034803d40006a0103d980d004481255036a01c01050312030b0100d4407001180a008039500060a501c81004031400d00100402811410301d915242d859440d070703031002014000c29030306520071901c0d10410f43c0c0051000495003400c1d038055003002c1d001c0300f46191205005500e0920510010715003030b150001200c6e005045241000340140070311001304100980c0c98800000d80c3c500040c518420040c2c000540005034000c20b50a281440220960500250b0400c0c80e180d580d02c0c0c1e103205400003c3e010300d04881180d203112403121500707001ea0750f0710803500b00303030303014000c0d8030000c401d042e00000109006030000000f0070503a0345503040107086850343c2e0000c900003103581c01917840040c0f04036840890344d4001426150103a01898683e440318003180551540391f0440b40c204200319401c000b50503000c03404402c80e1454443d50f10002901c0c0c00d014000c0d02c00740841c021502540c9030804080300d0180c0301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 803423516 1250 803422266 803422289
    0x5060412211e0503010b04050d020a05030f100e070e07030f060f090b090c0f040e04140102030a09050d090b0418021201260f1b0316030308240607020f0109 68
    0x41589008029442d010010252240c41040c03400c8034a01c9201141d04032400540e620b0304007800c020410003d20017400040e81d00c41c0b081400441c1540c5d003446008030f104c00c0c5400034040282c8295000c001c4d00d02d00ca805c04031035045003408104044000e8040d680c030108514000660b01c0420848200030451a000f2100b0418080408a00440380c0c0d400380c401d050088941c00c900f0b0352402e141803620300c40e8102c00b10b20100240420011440d80c41c2e41503030041e110b080840d955603600380c4c00e85c1c2213070012035a1007103254441200b01c0c1409402d20102c604400b00c0e182c07020440e401d01343c024881e0300c04d91040d02034800e28024102400c4c1820b5060320540105003403e2000781d60760716031140c11400441000709088030b16014910400da0006086040c205009001d07010502e8101e01213102001c030360160a806010304006151614500c400070305c0614803d8690a90508000c2c1c00c03a580320105840b0600c80306079000c1145666501c140945080070340c100e804a039800e0403980102d84003101544070460748030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 803424766 1250 803423516 803423573
    0x809121501090f050603030a081e09030915121f09060305030306010318030f03110c0f0604050d030b030a02060c0307050601080c011202030f13050c0a08012405060412 73
    0xd000d5895604070b03000c40a09204403140e5001107001c40354107948469059000f0804211103d005043e00b0b0743c00080e161485101c20f00703440c500031a80f82d04844054860f040015443e8040c5003e500b00042810301e41400d0f81881c0d041c645071100170b04050711444840c1d007000d49200703c00c41c901e07170a080648a4400140b0070709503207140c100d589800c1031f00d0640c042820002000b200c148032601c14a40da41d00f696404041e582652070540c001c126100c2165442c610030003450340480401c0140490410045000384074518050a03c01d0910000d03030480400c0604003005400b0a60f40082c03000b0300c3c240c0443e591940d030740542034068039610960344020190300540c0000200303c0c0c2d010840034043d031400c0e281c1003c5482000701d20070132440205c800e054500007403004514080b50038048500468450001c81e9480303c04440015500113840d4440d0401e6911480c0f40b0800d112003190301121401252009803600e424a4000785e0b050086001361484c02a8904a0344e05000720801541100382420314100d100f0b9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 803426016 1250 803424766 803424793
    0x150a030204050901140a03060b19060c020a0b04080a08090d020a0f0602250611070b030a0b0a0f030512220f1d0f162a210804080912 58
    0x750802e21a080c4200c81a1000007109046040728445440004061500e6981550b8441d00102810340703030550054040c00c083c182540c1d00c0106003001c0c0c07220b5200c005406145104100f8040c030740c1e0700700403048a41032004000c400c50002c0c9001801d544080703c10b4031102d0280208074044000c050103584014100c1001800074a620b04180a42d15a0340c26600301c98010a0b042c1007101000342210512190400c0c10440d0307521451075a50303400903800a0304c0209a0740c081290043d00165040c3d8821a070701c0f0218046440e0103c3c0ac0c9004000104c0504040c0b4a15115107417520ba03d402d01d80f55075000010309030b0703046409a0011b11055654120f80d03c1c9281c41d0207000c3c40103442400780c4041d040450f40c05200b0501510202803181c0b440c08800703200d075070f142045481d210725150500c0c401d00c40a506541c40000c42e200004201500340b03076440490785501d052004c0100c5029503806000234064242543c80341e0300415050f8000e4008081c10fa550100c80041040900c0300780c0b941c1140e020f401141c1c10714 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 803427266 1250 803426016 803426021
    0x41a060d1110022d0607080402010203030414030904240f0e150a0306020c0106140f0d140127030215040312051308070b0f100b19110703080408070b0412060902150a03 73
    0x80c020360f0101c89a9586d1007105a403900d40545019015a00520004000804213400460140e100034140d0382003404080205041e240c8003401012842441215a04c42d00d14980c0c070b140041082c0000468034900e080c6802c51031103006800c000343c60a440c1c042040ba921031a09600043d0b03406002159120b150180c580d00034480d43c01403401c503864115003600c0030300d8401d09180c90150b0040841036603407403070766641640da0540f00342d41c0f006540724410f100c1e00711605040200c401180800e0300c1440c400c2443e000b820204009251100701e0b1071002840082035124001071a0038490075070005181d155010544180e00081c040244841c200140ea4810080306e41d03480c03402080a070b454004542c5880143c40d0040c541e5005401c80e15009100c171050745d8540c0b50303071041040074a00340521401100d052082c10194180c00589040000007410080e58104100f401c005001c000007040c10700d42843c12104120000401c003400f02c0d038407625000e05640e5030120840184004602130303030303a90b140b464000d0003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 803428516 1250 803427266 803427343
    0xb04030c0306051503030d0f0f0606030e0f07062a0c0801020a111f0f021201270c08012918040b0301020307051b0a0803041a060d111002 60
    0x1509410f280109100c0ea0340500c90300c02141d4000e0203581002d0200b9508001450405642500da1f52121400103004400b0300c100d0000d04416130b00841c603230308030140b41840c1c1003008060600a51101004001640d1700c262140c0014042203080100700f68a0b0b00e884504441c40c2a000d021030241d842c00089002055004282d00107660311a842c40b5075801c0825901c43e407144020050340040e080f00c038200070000341e110003503150f02908010b0078058805c50140071048260010b001c48074a1505040f05028216100c4d00d003842c3ca244103101c510101c400041083c0c4c010301c07684451140b0484a034100e51b014054008040e0480802591a08003103003030100b540c000b40039500d014034a4040752525606042c0212840380020f51119403030001c803200031141104440161008600404281c04006114480298001c6020305074890000b500031003803840e040c002505243c0705480c010801400134410510240c1c0f0703c0c4088840c0c1480d081004000c4c2e0500c101100d100c448a58000900c05064111041044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 803429766 1250 803428516 803428523
    0x40302100c110d021b10050706021809091603030c05031c0c032304080322032c01090b0c030904060f06090503030a0e0609042301150f0801090c0201060b04030c03 71
    0x40344607060700f009a8846054601c800c0c1422103003000706400c1c1c100344100101820f0300f441c03c0c40c0f0300300301922a10100d03001028001800208080300b1200c41c5001d0106640082e0705c04c0162000442141d044d140e0240c15202c01030a0044900006040c400180b0a9a086039103494100c0c0d018030716120000d00501c9603102c3d0001081ca03102e20110009a07095409240e40f8004c014480140c03200c1d15905100c4d08000c0181c54082c0410806000e003201e48042d1b4200c0c0d51003a02c0c1c00c41c4002e4401084c21119882154616045154049840c01ca0780c0c0320700d20f8000c442685d40e00d9541d40580686150070741c45130086413a0440c0c1004400a050084900c221045500540e01c9104003500c1d407082644074807821f808540010b00002c1d002e021403500000074560101d0007000000c4440408003075010b21302020a14015044c1d024004100c0000b1442a4407201e030203a20302241d91040400000d0085807060146134001c1d0307070710414080d40c1c6000350311050140c20f90403d034036102c40c0c1ea4500244401d40c640401c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 803431016 1250 803429766 803429773
    0x209040201050d1b14043014060f01050906010c020411160b0a050f1006030e0726010c020c060f07050106050319030e0303090a0e04030e06130302040501050d02010e09040302100c11 79
    0x390003420f0560140d0781503440f219902c3c04a15000b104803d078010711f100a07440010790040d03c840c00a41c0000e500c108024040300901200e2400e00038030304005105078007583c0903185110800c050f80c0c4c0c0c440040540035904460002d888494080390207018051074240b42d117074001d101d84023408d001b405060700748125001d00043c44a41c0da6003e54007545242030b01e045801048540081c050940a6005400d070100c10b1802c84400d01c1e81e4090034083c4820b50f207144c0401782141d00080c50f13200c6c428001c21035100c655000030001035851401162140c815003110b500304076070218040003000707003e402140050500500311510700e100c11082d1190305524100c2100464004074004105003408401d031640d40d00e000b001864000e15020300c1da803125400800450400585e8100c4a02541c0e07440090410001c40d00f4a00c882c2505602c180000c450040c3c12452291200c0b000b8040184c0c0d00c07460b0440c0e5100103444540903619a0319083e0300d0540920300d4841e0650510605050b1654000c2618085000c02c034202d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 803432266 1250 803431016 803431037
    0xa05033105160e01030320030a0503060f01030b06090d0501090204091109090f0304052b080a031a060d020714031204020a0509040b0a0509070807081501210209040201050d1b 76
    0x904000c000301c3c815540d00900c0316004001107809407030007003040040340c50200c1324403100e0005d0764110ba0190300c40344041900802031055074104090b208031480002e00307040100c0d84506001034100e004504085100b4030100c041013080050a400500d40c103540034109000001d0076140ca47d807645072a44640e40286480c0c80000e000f100c00144020903002d02901451800b410401441003000e0f10180f0f0954141c01c190200c4080c808403120802001d000d008056140c101c50100242590f901000300316211119410805040c0e071448119401c10303d1207000140c3d58100c1340b5212440701102c8142d0b81c1d4a0001241400e211032440300c0080c4201d108840448110781c50744204407181c1400c2e44d0140803d98140001010050307a6401541c1081081c2d041390013903a07444900505d0000c041c1c0208101f0380014600132503251354003210a01403c40f00b1005051104001d4102200241600c8080d00c10602d150104007564000c100319584c9140804042c4200c290903501640c0180c112001a40000c264100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 803433516 1250 803432266 803432293
    0x20c010e0a23030a0c02010e01031b0c0516081b010c05030a03022d0316031509060f15021203040309170a031e0207090e0709020c07080709110a05033105 67
    0x710740a41310301d41c98080b40c6a550f5001190060700480b02035044c1981d80400c881e000c100c1950840041c02669180360f000f442902c1c10500b4010b1604820390825200d0005220b541c10108020b01c4001050203000d003c0c1c100040100d60015045401404a010000c6c044408941c180c0080c03949a81003043c038030001060085954914002c0010b0391403600c018004140310310082d54800d14080c0c2d0914001c142c002c407106000b6058400c5502c06c0d21240c0c1d031503e007002891041041c034130040c0003d104110a4220810b006900c0b120703081d880c1d082614000002404060140340c90102400e10130580341c41140c104079019540d000481010f802090f01c2856500c95082d02072005460081160b019042d03c5203802d4003030002e804003a41c2c070242030140c1d000210306580320f44054840040540010001140b600c8459401d0021603000910300340c0c00d00201c901054030450481c1c19044540c54a150380341d490526031455214214401000e9a400c813103000c00c04004801e0305010710380240185c0d41c1d00b41c55120f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 803434766 1250 803433516 803433523
    0xc0706050405010f050c010603151d0703050307150f23060907120b061e0712020f070605030919080a090b040509010909140312010f080619020c010e0a23 67
    0x402c45001402008103400b04a1145028041d070240d5580041281916030f551780ca80341c2c0b20140035280341a80d400000114030060562034078083e0600f4041d00c1c0250441c1c41b05c81d05d0340705814010780740000078401e01d108800e2079801074805901e0b0700c03402c00204200c0c003090001d4403110441c000c404000c8901244e80380ca4900f0302c0c24010007441d03c82c00301d5661280c01c03907005000840e001c44e034410011300181458920100320149240206000703d5900c1c1c629181104045400200d12003c5504c4640c10448943d8000303020016601e003400c00715103d075a005502c40c58514140350885192000104031020018002c0240480102c0c82d140d49400c1070b21140c40c01d4040c080d912401c5d0740202024010451a40b066200542c0d07507000308400e0420404400c240c51071603002da1170241c0c11082c000010410141d543c1c0303c51002d020326401400e43d0b4145500e50400384102e590700f20001c15400030790400540710941c044000c00e140c3e101a1040c0c0c10381d80c14140c480c440c1c044c00300c98085a0030781e440c101c400b4011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 803436016 1250 803434766 803434769
    0x210601091509030321090602090a06080f072d03060e0c0715020f070c080c011409090708092406120f100c0c0b01030b0405010f05092806020a050c07060504 68
    0xd5840030b4890b881c603241141c81c1c49101c103003030298030344580700b403c4201a6400f0b80000755006480150fa50443c0c0f60a1010903a15640702e5801c0010017010300ca072401619440039000085031400b254001400b0964000c1d0024040f01440805c02d5600060401a0103802410071241032420300c400c281e441f0060754005100c0d0400081284103403100012740e620030b03a80179007a5414000b10581c1071441a0744d4901b400c071565041144958014840c80d091583e00c110303100e00050003d000a0300307000f01d40d00441c200c1e481c00303058002400070903000503000c02801c200505241300d00320400d8200f0101800c2c1041500307801c0c0c1c0e406002e00364059204580703441c0025180c420303804490007850081e00f1281007000070800e805240c0300700710391000b496000c0b907807000f1458040c600400d03284020341060b2a00e9421251840c1c000b083c4a4102010004c5e00d80c03000c204006030320305540401e03031080c07841541d0240c170410064004000e548003142c42c071270081d88440130b811040242e42c04c0700c010f180c880b207058a550045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 803437266 1250 803436016 803436059
    0x30c1205090a0305031b0307120e01060b0f0c010e01050c12010e040507180b0a031104141018090c08060f100803090d020f0409030201050a0b0402070f020d0821060109 73
    0xc02c0000000d10440055034041a54480440c081c3d044c00c43c810780d02d0380706aa24100041084940b480c40f20107a1286454100d21003008104841c581002c01115005016206c0610b02d030204e03104140041c03c2d041074890901040082005281410300c500b1f01c0d40010800440130300300c10707001040349442000120301071070300300c002840d41c54a4a00b50a82c0000b840340f500d542c09450742a4058545c0310742c900c240146118402039100c40b4100021f200481c0d02107482d24040c21001d4040c850142c1010319858255416450304400702c4c040d0381f070480c0141011510041200109040000c2c40301000300c0d16500030300320000741c0145a122440340034807240250007030b00340d031345c00400ca00030441c6000d40d440102144058050314000e4080c5d000102203400c084420303400340c0d440b0305c00c005c0d80c2c00f658400c03101742c120308580450a01d91691105622240e640710001d00514101c40c00b64207100119041e01c81c48100c840740c400446200710400c1c140d00406442d001c1c0802c1850001007804407a1800d00d0201031103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 803438516 1250 803437266 803437273
    0x72304060308092106010b03040b220305090114030903090a06021b0118090f0c030b1801031506170f390402040b040f080c032e02090a06030c120509 65
    0x4400300f00302007071540d83c42c0441500d200e4960204d03200b07000d1025a00900c00c840c0c0b03940c3c4924060500103180311000b465001b80c507610800c002ca0b22810504d1500140d40c05207040c03511541c00b940140c030f50700c259284010b403448000c401c00441c4400040142078082080d180035420310750741c00082c3e03a11071083c4e1075010f91140070001c02e03030594030032002c1307074103403580031000c0c812143d51140007000711030150040e403c0e06510b4440c201200c2e60503000e11100144140d640402d000f1410081241e07404045c04002c102c41a01403004d84020b5a40d000403006e00510540c20441e2102c074442507580d03000d0300b241d10082e030240005410a002c076020051030303d22040500504105070050910800031a1400310f158840e601703001c0420210700c40c1c5c3c00391014256980740c060000e13061114040ca0001007198440c4643e0040060710340b800000901800c8020750700440040c080c0035240300c032010340106a1115000340480c0ca00140d0181d05070000c00310514180c507000c050b0343c1d00740748020aa480c22a5500400c0d070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 803439766 1250 803438516 803438527
    0x60b03030306012a02040504050604170901170903190f1b081603020f0709150e091c09090519050906090309060a020723090a020c07210203072304060308 67
    0x1280e0800059041c001c4c0007030f0742004030165000604403401520180d80320392000c002c0000300642c4c400c0d8005104030b0380001c5820005a070000074001c0003524021ba070507030070000110705001c20401c1950020984c4903004040030883c820001e141c130000c1021500041c4000c41a08c244000301c040d13608203940c014002c54035101c441c0e0b03500000c10703000c510210114400c64910650059040c070180d800381054207070109490482c0c402c01c040d00c510300d402001c00e0745000703001c4c4000140c001602e40620490b003144d000031058924002d88008455600c58142c2900340020884940700d45044440c001c0d01d0030008000307c2e02c0c4c2e164610303034854040b50a00b280e0745c0100000c04132868100041d010072485031048554107500c3c8c421003454009091020619180c10f0f00d4400254603281c1d098070b50081c5076010450508481400d01a9201101d100303003c880020300902d0391844410b200080001d640140484034065036a001c1a920a10380070a910b2141c1c542d401c0c1200e152170180100c5007182e400032005420308 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 803441016 1250 803439766 803439797
    0x50307031101051b060601030c030e03030a050c280f0507200a05030307060501030201080924040218191b0c1e020a12050d0f1b050708010f0603060b0303030601 70
    0x155800c0015062003414881c40d004044c0080090701d07903082e05805040c40707040000024003a03a50202d002d8062509014080d0b40d002ea0001c1602c1d8440c0758a400400c40e44c0780c1c080700c0c82d0f1501c500b64403c0d00810300d00c02060000c2240100b0040700d040581c0c0c0b040c82c00c2c0c2d0010001ca9080c0101000105181420110150001040041d950031514010422403080f07a440000030710390707840100100d4883e901c410040040d907800124180d07000f02150007410101281480c3c44010139217400c82c11448040e82d00102e41951a000780052004050441c1d1103542e0038603010408036443c024840d0581d00c4e08044071651414010819007105020035160360503100500d40d66030101050f18a44051200074481005015030f0762070080400900d8042007007402c1c1030450901390b081522502d010300502c403138203994070a41640002c200c03000b1340e44440f85502e0301c2c0b5245401d40c05d1000680c0040d9081d820704190100d039000341e901c41001c8034803c41d01002401c4030340050503100c0c0021103841e80070494116925000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 803442266 1250 803441016 803441033
    0x301080a061d030705071404150b0703020c060304030c02030625030f0207050712030306050405040803010504023f10080c100c050114010e151309110901090903021605030703 76
    0x8000c00301680c070b08450080c1014070316000450b044c0c1d00c0ea400319104001244a816692a5100d0709460900c20450302d0003590a0500451043c4a0905000105c0b0800c0c0b40c030a05c40081d201070000c3c2034540d0b90a01e400e00804001c4d8640f001d92181c080c48001c01ca0529400200085010910250a90080b04050160300410180ba403021200e0b8013086500001401804410701421081e28500c480c2c504504008085800503001030380514a03003014007001c90788800540781101d40454026031390364924030812030040c00c0111640141601d0344d007200901d6906d00c12101c019401821040c105556100031040300303030010b204044a91300030b41604c040d80d060200c41e0f500c072101581030115424009a036154215000503241e80c043c0440e080040c000c0f030103440459600300055201c900c0b00c140e52240001d07144018101101401e59403007128104010300c0c80c50038120701c42c000340f020050b503a40308070000141c588010128018010041d8409100168900c514141c8801030004e011207402c540d541d540303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 803443516 1250 803442266 803442281
    0x204141008010501032a080f0a0b0607080d0b130c0e04060e0402010509010933031406060d06050d05030c190f06020d140403031e0c0c020918062a0301080a06 69
    0x1c40d044c4da803c0e40810306d03206004400c1d00b000c1a6540e1b821440d05140001660001500041c4503505004500d016aa2144265020503030042d184503640c00b01100a01d0003000b0750160319030055a280e2400b8102102603029610040044d03d8035240c0420b190304100840c1d91074051a98034240388030102d03016500c03d01c06000c03c4d03071040c140b00303101c0307912109100580c035640480d1003a406503a00005140807010501800740f034050f81414007100c4203420054500b40c4000749506d000c1d0700c010601100595580e00200d0043c00c010782200020725150519940f07039408070350b8903903880c46090b440030701e9080303101844000130760031040c541041e20482d950780001c0c1d8002440e007a151500c0f450050f2203e1845003515014a01c207860008103210803248000000880005850606103024200c2030b0b4141c001c00b5084940b54121013642283d91340709a2204400d82d0760424018a11134402040564414a040070612080c0c03401d0130342400ba00c403401185c0600c0b09000d00400380c2c10586038a0000342c0560030022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 803444766 1250 803443516 803443541
    0x17010e0402221506050f1603030605061204021e06030705032505030906010911040303050729040b361c09031106041401080c0715020414100801050103 66
    0x6200034891501d481c0d16044030341c0b03403552069030b80c40b074641951007520080c4000c00c4182442c50808400030281c9030140240301801d154485520201030405100c0d40c4500e0151500502d500d032140004c0814880c24102120100e01412a00104020b00400000070611400c0000c01c0249540d80d0ba201c00c8074a0781028285030301640300074100d115126a9000b0703c410714405a55682d4991030499842c5240040c1a4010b2401501d07180211006000d0341040707905030703501414843e03038510641c549000c8024100449280c10030b8224400040d10760003203005400dd501841c07104070251603100100480c511241d02d03d140001c040c02500002d16090058144008500001d8840d0500da21003190310320800d94011200040e1004000d0041001c400e000707e51480d000c1d00c41e5410141020501c1c04405018011507040c003607044001182e005038041251801c0d03a01c009072090151110071114041d402900940400c850500c0780d0b040e640c00c1440c6c80c01000205a525000795910b010015401443c17605440d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 803446016 1250 803444766 803444779
    0xf120c0902030a020309060609091902011101060608011d0f01090905010912051314030c060705030d020d0204090e013b061326031501050d09060905010c17010e0402 72
    0x340040851000d14800c2201c108056a2803a00900b4641401d8004140b1885222260f0620209010024141c1e00c003202400725510110418001600c90700b035904180c611940c20b08102280e003c1d400403906040b074112845003801c003102c803a202401a681150300300040b908038001000210540e8202c1001c03c0c0c000c1c0000149002e0b184c0303d440c041c4d8009101040481d4001032880800c02c4e441100b00000c1c450302004540c223160060000340c03900f1000072240d11910021883c0010311801780102e030640d03001e40b0000c56850000c0304850000c5d402911400384180d1601d03645d680c90420601811031f603505e203405031181007000301619402c4012501006d46801c10040c10a54205d0410018079005212004002d2188000762801403010358101c18100092204040100c100003805016a80c2001c1c103080762001c41207940c0c004071054041c0d403206035001c5080249500038008142c0c08032203000d0084d4024000c1041c0c1040503110b80403455204022060b52500410501d4085101d660300310344001d110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 803447266 1250 803446016 803446019
    0x9010305100305030a0f090801060b07080f042103021501140d26070b06011b0b0a11070f140d0c020d020a121a071d0108040f140718060f120c 62
    0x101032445d042843d181000c5100c6044044250303401100c8000104100d034003e211040c2061002c801900440000520081b0301040ca12501d00207941a90060902c440c0c441c8103d02044c0800140e5240c0c2210a601500600000c1d400d8460030412050503210018070300600740002d90180052480c0e049429a500000085009402c1000386003c03200c1d0207000c0303e1540c690800e41000440c010010307141a0500c01e0300d43c001041c8110041980307e0164011540350350a42d00d20605101a0004050310102c040700000c00760200010029449020750003288602801d802c1d840400350f85003500f40b040d602007031071050b84400500e055261621203510291a9400751640d0361104200d035a1412000c4518051666440c0316403c40b5500d010350004061800c0c02d6400c604c5041020080e2924201d541041802170008007800a40c0d65031590061344030110044411039800740136122a0207010f041a040c2d4810700c43e907801d20450203503030142c4484139041400c0038901103d9060307080a5000c100c0f01c61104080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 803448516 1250 803447266 803447273
    0x905070206040b160309060f090204180b0f09070305071d070206010e1306060f0f03052e020309010905100b041104150f020f010f0b040b190302060a030b030316020a0b0708090103051003 81
    0x14407048c43d00d83c03000499261510310410042d6800140b001c100030904521290110342c01991047d00891003070185466a1900e044950414049400203016031090741d00c0015030401c0650340807070742182d05001c0b0300c0c55154440103d0304c4003400c0c070540381c900c4a0348000c24055290741c0311301c0480a1192100145503540e1b007020400a28455000580c149082c000030410b0140500501b05c88060381603141004024030b201080c80c0170a444d5100c0e203001c5c0d0101c0055001042544511055a082422241540009400f502c054810b80200c00c3c0a94100b901107c0fa00c4021800d0f0740031f51740c442c40312207444021300c482118450410340c0c08004510807103212800051080c460441000462a00819001016418401a101d40c1c185036406105403d15590491200c0008102075035811100180c0d1075400c80021001707800d040c0c002507414080000c03105900040319041d400414802e840005603035548502c01c5203603008480014001260410940d0307125072180e4030070b81e40140315100d4280031a40302d44 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 803449766 1250 803448516 803448521
    0x406050a0f110d0c02060708010308070f02310c080a0c2d0e06040501050a03050702101d01110c1c0918150503030c03040b0f0903060c040905070206040b16030906 71
    0x4854102d00c40340090000302c58410742c00f849881c14003d000500c2e450030030050060403c601440054607a20000c2010400c010b822410840890740083c00c01040e00d000000d64001001c0381d168203107480207084400c141a407024001c0a034120401d888032040b65541c903100d4000f0301030843c00c801c1040910400405000359500454440a00c0b003003503044800c00014010703040342c6d03450a0b00c9207e010306100400c0b081e80d11804075802c00b241481e020800d902c410074240e10304021603505154090404182034203000d00c48104545a15400000780042000150780f4844c030300c02e41202880c550007480c4410314070315500352800c005104a1400600c5140e46002100c0300103e01c0c0128580c1c1c580380c0010300004c1e5580d120010248c0f4040307000d90325100307070b041c20755a50740302e14400d80d0210040881e544000c03440c4502a00c2a414010b001d031002071611481300255580f1038001d00c00f03000d1902c8041392007a03100040180c4156070007061a040b5031035120354540c0f001240c5c1344400070581c0780d500c2a000542c050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 803451016 1250 803449766 803449781
    0xd0b01060507050708010501030b2701020a210603030c0215070f1202010c08010807090e0705281a0403061805010606021e1606051b0a0305031e09060406050a0f 70
    0x81d69019110101450b1032810002268460280c513810500140089181954459013010070209422026685007108948910700c800300007245500c0418141344094221510601c07001d500c1d80d11740940c4511042c02c8003103900d50300010b400074001000751001420540b105007004001c460341d8504260050b602d190401c105203000300c41c00d0a000b440891602d40901038803101840604000000d9030403e980246d850100e40b095100a544905901040307030005d1164001804000d0895a481070915610900b85400400b4200159604174800514282c40c600d14804030312519021524141c550340314038000d82482184426500b030390105501c0040c00900c9600e0080561f0b4000d0005120300c40034100d140c02010000600a4101003458003100a2664844041d07520b9030070503584600805e55624500e155024461105d441051140c006041d007100c0070314401d80c050314039030b0704083d003031a8921a40d0380262020b6804c1c0d4010804540002c12642105500200ca40f100103104902000c1240075100c54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 803452266 1250 803451016 803451029
    0xd020a031718060a082409090304060905060304080f1e031e1807032307030506010509010909080304030c061b1214042006040b04060e010207051c110d0b01 68
    0x2004a400c8189120440c0c00510403a00f00c1d040c500340c0300d006824030300002c0100390390700840c40444030303180d000c40e03907884181101030f09800007458840040e949d6a880f41c0240e0010074516000043c1c10310b002d01c02c0b40d1107140d10000e820b041c60031442c01c040d250740140b9086800e9160074010030b2550044100518414544a018020741864a03864020012000391001e00e814107286901c07606070400140c48021079510019814189c80e00c00c01070a80103584d4084010140190100041400000902075058507802c4900000300c1e680c60940d24111684401c0c010408200ac3c0001804079008002e00c40c8958016000070030900801c56810f05003100907030008001c20302c02c480c400d401e041d0f98400c05c0188402030101d500282029101c02a409120750111036a1807074005403808d2640711350058400a01c0a4860242c0700c0b522828060310f072803684403050307005200d80c600c0001d2074907040076080c0c0c042c217042e46548103841d140d445800801d40002075440e00300680f0090540011440700400d8020110f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 803453516 1250 803452266 803452313
    0xf07122402180613031b0815090d09050a0e07141b07050402090d17130f181b03150e0405070e150f04020307180e100b0c0c0d020a03 58
    0x501070203050a24400805031030103480705005001c2004584c000b4481034a40050a0414050454203000c07066400f41c0c2110485000300c0301c8242e42c000f203202002e07000704421801e668004211080440b0080564420741d94130207049107082100405410660707401c481d10f441c04650702c41c82400682215400201e00e4449560050303104000c50409106910252000b240c00b5450301d038103800041c106d600c1c4400e0240400ca44c070301510035000d041000710b801c2401985404003400e5902c4841302111842c82c407511041c46080b003080c98008005105130035441001c00c07114140e89200e000b04400425240300308002c00740000f00c0c042900c0e0030b0103011600c90f0340301d43c008099180c2015000503200e00050b191618078031910a0207105c035510401c004000c51426240180c49550742d0008035240e03d810144041c0c0c00900010119285407400e05440c41140010107404502d82e071a014550507100e5055196500d80011180c10010f10b001d200680c0d05034001090b14800f503491361a103848012801307145561442c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 803454766 1250 803453516 803453527
    0xc1903020303220c060806030a152003060a031101020a0503120702070501020304080c0f010c0b0a0c0e0109050319210503100909150f0f0c051201080f07122402 70
    0x407440e80c60911031982d0140b43c00d42607001da030351400031115402050140b01e070030340008003107840400039403050940001101c1c0311800c05540410080c1408039000c1c501441001450040203080700c2124000c100c050401c007403c80c03440e200d001d4043d40c8040c00c00e045020f401094004240c0400280c501c11001c942008980c1c100094064a01b0286e9070055041d500248800c108405c408507148144820981d010020100c448004807146950480010010400d101c18440c40e4102030b400320107422815124114100025401540c0c00300b810b00c01e003a410b9004c0350802c25450b9120080a10281c0700d001c00361011004032400200707904105200000082002c01001a00110100f410b0010310242004010054003502d41d18000c3c201124810380242d11094a4071451009074802e1b40d000013510010012649580c0e4010300b1680721700d29400e03001029000105194401103044a1641d80c02801413424500c2c141c1c50403a400c40112094801c095001e0b140000141c1c0c030740085070900e0580c5030040c0ea44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 803456016 1250 803454766 803454781
    0x2d07050717070b0706020d0b0604060309060f1109010e03010b10021b041515020a05160f0918120c30021f0207020609040f020319020a020307080c1903020303 69
    0x400300900740046a900500e001c11446440e030040701c1c600c540200c0050b03070350f43d450a84640582075482aa0350840c0c4001000200b00b5415030107000500d100340d00134003d2092918011050300c0040800701a0050200002d21403036002d91030300700c40003101800100d08581c0c030100141a103660750040d0009a00801c0700048440700740c0150b0a07000500300c0b0104681d044080384c0c0d008810850240c2000032003a083d42c04006802080284085076020003140d1821840c44021580c2c00384602c00c01101101075107021904603058040d08c03090308034079030030350215050a4031258104840c0030100d20500c8482d10546000c15001014541c40d4411400314151051141c001f0615501014040a0464104640811507030000e02000d0740440c41c01000076031241c0c0c4600001d20203124540c416a40030785031007c4000820303c04c0c0c002e90700c501c1e0b40100517030300001d102c0d04041c16889011503040040e0020400080020800809000089644022170b80c183c512030489043c1c0181016054025074008010018030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 803457266 1250 803456016 803456039
    0xc06090105070203162a050f04020c0c01141201030303140c03100510140412020103110403030c02130b1c12020c012319050d202d070507 60
    0x201104100070480352502e444000d449002d514443c0e0b03541200c2c003841d8424403100c8200100d4098840d20504d04282a50345411030050081c0301e8580582c000321070803d50b034a464400c0c3d8440c00607200203051545c0659004440d03900304a0040784141406203c100483c1060a511034040c1d8400c0c3c800203a10781d83c0b030200005c4940010320910510700c08100b0080350304400c110000480b28103446400740390601520035210103005007404031301042c0c0132a000a00300f02c0044502c003028000c0c0c03801c01034071560107440d9095204034000500400c0500fa440401402d192540c441001c6c00d445000175414074807400100c2401c02d1241810100200b03404003003c0c0b00d0500201d5661021500003400c808040751300103403006140341c414807082031041a401c07445120307443c01c403094103440c1c8240c01d242800524003c2d2068010703820040b50240341030b51000c007800030041e00c0d030f00b06501201281d00340050740d0310461007001c0303843c04410804041d1240720b0005501350027404440d031142000c2c020150500f004904c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 803458516 1250 803457266 803457271
    0x30309031b0f060e030f22080d0f08150d05010b01091401091205190b2e0902090d0b0721090b0f1003170301060f020c0a0603020a120f020c06 62
    0x9604500e400c03070010300040030180c030196014034041094a18001c00030b0440c01800000c11a014001504000292a03996131090810059540c5110541c582d00f0300c41d95001d4031078040c0c0100c0c10302c41d0324102a45c02040017a034000204591700c80441410b0000c5005007446090445541e9140e042501f195070f0004070020107002c0d1241001941004000002e11b011080c0c03040000400380302d00034909000e0280f020b01e008492000c204450018246041c080c5030780102c90707541d450301d41c0c401d181c0c2080390520150400a014200c5020360142001e040e100294011824194080801c1c040000044d05480340d503882100c00d52913940402c0b854041e81e03840401840b8404c41228500741d00b03e8000b600c180c80d07080d00485c0d1010703100d00344d0351260154102c002450304040c12804180c11030400800070301004606030b44d002d035280104141c4020040e69a540c810f00140e502084003601806882d01c40ea002c2c0aa0010030306d01182e690040717480000c01c6034101901d41042d25000100600b450400f000300350f8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 803459766 1250 803458516 803458547
    0x614030d030905030a03110d06080606010f021b1c1b061106090a0605060a08010e06070e09060f1002070b030c04030203120a090b130e0f160f05180a0b0703030903 71
    0x42c0d9511640ca684d01c92044001200606950388080c00310500c02d941910942810b000b02007203c0354889100a940b00c3d0103c0d4140d0008171041e200250461020452806104113129400080c0c881981001200f4610050b01507036090402c040c2c00c08034490351800c080c0c9076090031460700518186040204003034072101c4049003c1d4000303400d004050400042c10003d503500528002241c0d124040050741444241d80000341541c240108410740f14404120180210303071035240c90502c540411700b03000c50503d040703444a620a410303000c140d046081482c0000280130161064405154640f02101d00640041d81c035130146070404582401142810000d5038080044c4002c03590810080b4080100345542502401030100f0700410080c14070300041104c0c10103409840380e010001d1503e2000404007a0049490700100c21045448070140f81c0540317201441824103030b40380b174070740b4498103034240a010b0362184858001103254000240b10b0720355406000464883d55000c240000d85040080500d0500120903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 803461016 1250 803459766 803459771
    0x909071805030f1b0102070e040b010e0f0c070f2109051305010b0412030201060b041e14030312041b0b0c0d02071818020a08070f08010b0609091302040614030d03 71
    0x2007030f0b40140020441203495840080b030110348180b000403420710303065900440320920843c3c140070400c404014a1030680b08843e088000316130b5010034842105000b625504480c1c1810461080030511100d4001e409030b0040b036000510000140e8807088004480917005c00244c1c00361414000342c60021b501d01051004c403c2d0500255042c03070340c841068030032031080c40d2110b40c843c491542054000e403c90300060169801d0540c0b25a542c10310700f83d940480961500390048411800305a891003000c04c818020030107002103051101a5400e00c115600c090024cc0c0c4007180d034900c040046480140b407a000e0300c00403510a0f10340304501c035110315080151000c00705641042070306100d05448590500c00c0c000c0f0300b4001180070b18040c00c2004501c41a41c03c003940000440ca000f041c001c4000904070201c44034003000820050781c130003000d8200e840f02210350ba4886810400943c0900c1d1000c0595044420310b4802a040310031a800a1301306c94040c2d0040510144400c020000ca20b410300c8150b0b40c85007036003800d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 803462266 1250 803461016 803461033
    0xf0201090b04060932090403090f06050301080f1b0103090614041109010e0106080604020f130b0405031902150307050d0e01060e070f09030618020a1701050601050408030f0708090907180503 83
    0x100c1417100f901d80c20150041d51100c00080500d4850031200d4028040303e0101c2c0113050305da01005040d640240a015060300c200d0300609042d034000034052141e00e4202e0403204001c40c0070001140580107038001a50710f940c0f0796940100414001c3e2000c2d006921031640c50054098a00a1000d6010164451210161240c00400940c1d0300103804507030200e012a401691900c4061000313105008013090b410703203602d510002050440c00c0c40020b0060398022000c603004020340f00c00c03400c10ba10340c0d4940250400d1031145401c040602000195801c94941d00b402c605118041010000300c0701d8036411000790717a44400c000c2115114000701141c0041084c070380300400401000024158560a10005003100d85e103280400b1803181e0301c1c08421109a0040c44500161303034640074120514040600d41d0020351034240494030542c050021030b012108490b001d10b050098081c00460180c20880303080e00c0305601040010f003e80e4400e514580304202c2c5448a00b0400f6501d010324500b49a180c00039806035001d142e2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 803463516 1250 803462266 803462339
    0x901030c06031805060403020c04050108030418020f0c0610030b07090e060f011412040c06051312020103060302180a0e19170f072105040509040f0201090b040609 71
    0x1085040e0303941c1d81400325101c910146424031124100c200030b0820b001e0003091004065000c2001460300d0011a02480243d0b290304101d92684220311070203406910f20410031800f00c01d80d401600ca4851030440385030a003030714003444a0406004071100c201c2c14078175034410310400c401014681d8000c401480c041403014200007800c00030f58009040700707114a0001111441680c0b003084801c4240d5203c8140c00c0d102e9400400c6110041d40a55044600f020414404034070948240161444900103620306080d02d03140c50901c6002c05610030007641055103607107000c00580c40d01c545030701c1c2101c41610941d0075440c01c3c910a2013190600f54030b11405402c0f0610129010759030f48018442c1c0c54200c900d181801c8041403a080c00c910400d10004034208010a00f030082c030090682521003a9150014200495250501200e142c885c81c00f43c0d59010802d9004500891104a50641c1407441030402c0d40c0c2d215110780b140791498000c0c1c2d21a41c002404403a0a211610100c03960140030f550001503800c07400e20042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 803464766 1250 803463516 803463533
    0x2b0c08151801050c030601050904060506040602010b090a0e030a111002070f0209060a03021e22090c0e040b0703020901020309130501150309020a0b09030a0b040302160608190515040510060905090103 87
    0x40c1821f040000c00b1542d071446903181c0d44007034020640208004d42c4d55941d8140a4041c01d150450144614074220001e00717006003e004422108401d1801b4515040f41b102090710f0396450000d1450940c4914032403e4610040d0b48000d182e00d82c010403e54201078094410003501c4140100303114044c014441080005031200c5403071002400c7c0503483c03080288038640100f02e1110000801520003810420851185466903110300c0003d4001d0480e102526240d0069554203a400d540041000001000048220384a03601400710541c051040d0303440c0c08030000000e20841628006405001c1e521030041020b100082100b9004034124241403003241e800760002894508a4030501c0124500022101d48541d07090220905450b8003032650b00d000e0034507040080da11400c41c9040f8141e044002008030f40720340141291842400c0015000c0b5103824600104409000060201c41e0003000e02c01c0d401e40c1540c1e8601999200d214515402a48546041c000030b01d0314800b035110600900194006001181c0100d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 803466016 1250 803464766 803464771
    0xc1403060c0c1906200f0d0203060d1b0609080708031605160312021506130b031603060f0506060f04030813030f0f0209062b0c08151801050c03 63
    0x182a8030b4451400d600043e09182c00c2c42c100c80c0101000d81e04450400c641d0354000700d83c8184000d070394030502ca10002c0000c0c07603105103041e25201030300610500c820450950000c1d90b00810140451244003041e565901c9803801c0c02c1190925051a44000d0050744d0f4030030641c20003042960024128180b6010b103c989a02c1440d400c1901100381070310b490188001000074003200d41c401007079001c00c0c82c0d9034140100801301c6840f9840060203524450b05208400d4540300f402400c00401c0214040070104151000340104030202c1e41501509401402c03004500c4615001940690000710311540758441a0040710402040c09114800910280912440c9001614290390b402021070395542c1c420094ac8441e0035061344010048031200d030364017003003004d00001c480180340700b590031088a448240c2040440f80301ccd440f81c19148980180e43c694101b02c1101e404401c14040c8040080c5603440e1315803d400e081280e900300301403203008421f1044400e480c141049180180d08000c22850130013103502e80079840007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 803467266 1250 803466016 803466031
    0x160f0b07060e190c1208030c071110020c19081c0201110f0d0c1e050904090c0e01030b090a031e02100905072c04030c0c080a0c030c140306 61
    0x11a2490800c1066070102400082d03150407240440099040d50003d12645402160364003e0349800041102040e0203070400a94080140e605581d10180180400d400191042c0d9130f00e114800c00c0e4241d912486805074808000e94044d000e112122010f02140701900010b061584038410000c01800c80c0100715030001404521080c265090021000ca0140038034980c081c4020380d00154409004000c40c000b00707205000c25034103000000a50000703a40c2c2c000c804440a44201038540206400c1d84104002e1071000001400006e400342075807211413100585070091141503100100600521030001110b030f81c040c4200005002c082415a402481046942d17042c000050303200c1304081c0900d00900003c00943e0301c0380000c100011081c03c02942d101268490103503400c5414005080c04c0c0c681d61a280056140404000c800d6103c99404490003029194250344101c0d00d02e0020074109800c2c8240710700da90180d2041c500850443c00c01301d02040d03055214001100d80c00a124510380c40201d90150321019 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 803468516 1250 803467266 803467289
    0x40c08040b07082e090b030c03150a060f170f192d051c0f0e090a090b0c07020f0427080c12040f0605090a0b0304240509160f 55
    0x2d580213414a000041a802d0200318402070713986019012503840281194007110b03052005c0b88081c2d050540b5030319036054554140e04005130054145030383da12925001145200009080f42e03a038200c640405400e50022031101d030780c0c0000c0c403060200c1003020301c1148290a02034200410380040e00c41c0900c03c408001031031010b00e400d003049081a0503401c2000c1020b60307034182c4001c140718541181c607540362045002d11807151121601216100d8060b6907801200c540703030000100d11480c2008a0b4503c002c060089041d190178009000440c1441c40d9400390116003896605d640407441006040c141c249a002c0c0a145003000c1c4170020f02001141c1140c008007034880c4050f00c8403d003070000c002d1003003254810b600e02c16000c1090305a00c11200170030031221000155a01552a400d00712481d214075110103a018050700d80070300103010300e00b00039a0020722400e0844c051200d00b00c10100d00361540c04543c4003c81c2c0d0f91b02000f802203c14402407480c04070069070242e43c1390804090020758003041c0210b10b140b08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 803469766 1250 803468516 803468521
    0xb0411040e0406021603020a032703140304030c030b010f141c020312181f1e0905030a03030605011701061209060e12031b030606030601031a040f020306040c08040b0708 74
    0x50560480e45600c44100d60403004078517608001c1c0da9140c040c001140061403140c00400003111907070400c1d268110b50219819401c0c60342e00c40310a2080820340e040d03101e001c00c110000000e42d01d1011100118803075015001150301d000d0302c00003400c0642d4405003079486c415035014840d5440700e0fa15034400048411043c1d82c20002e0001c00e240c04c01d225020102e807003001583d500040780301c3e400100c20306400c0b2203d181e5010200c40d540c42111884802c0340114802451502164a40f40710500d150000392402050940d600d0002030308d0a4240e000075408a0b076118800d10195a10403041c40000700301b8982e08290754900803000340800d0080c281000850368503d0490704202d8243c00401c0042c6c00042102c0c41c00b103400080c007025a00036108a01c48c00700103514080420511025648503450080c299801c43d43c807600150f0140400750608000c25130001a1600680e0300c1d44130754031482c03002a0005880345400c00c14081192505680d0005100140e420800024030083d011507101c0001c0c607020300302c1e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 803471016 1250 803469766 803469773
    0x406030e0d08062d0901140301061e030f030512101401020d0f0813051606110601031208070306171e1204050f0d020604060c0606171e1009030c060b0411040e04 70
    0x507180c000304e1035000004070b00006054281810054007003400710020810181d44101e0b01d118042d54801c2c045050606400810100b0641c0a807007007140d029080480c0303007420b04008010a031904984280340800210014414038082c4240c05030300c01401c2c0002c0220000e8581c2c0a0b05100d0039118120800083d280000c0000450201c031022a0364004111001c040d40810a0100350703206014041c002041120010700c403407800a032540c101c2e40c1190040000c140d40080465440500a143c007090580b60301c4000f030504000748050034620242070103091040411556020501c06040040c800390380316020f511003840c24841240c041301e008503a00d81886035a440032502c5180e1070300010798400c801041c002905500400b0783c2000078406d40307041201c20344034181e01c081e03d9038000c5a83c0c5241d00c407500c030510601c000f00301c1c080541c4110080720032030304e85e01011200b5184030040440000d81080040c2c0f0401c0799078081c5490b0840c007180e050000520019503030682340103910070241c54200c0c4001081c00d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 803472266 1250 803471016 803471089
    0x12030a09330e0309030a030201020c06060411070f081308060402010e03030a050a1b060203070c060b030102040e06370609090612121403010b03040b0612120c0c03030406030e0d0806 79
    0xc040c0080c1c26034202c2d1b0828100a8000c9d007020b031011038140920000100c0c903182c2481803d4510240c00b103620301340b05a0703482d01e05000f510a041211064003c0011500f03031104ca00c0280d000f001400300402103031806100041240d0301092503140244d206120200b10b058009003658080106031400410f000000c40c000c0481402074640603080e1032001090081c0154025030070484103005000600181c02c9040030705080303201d07030b114000300c04480d680414014605100403010320551004d000309c8400854110551000e003042c6001d0b2401c1d0706005c10000d840d0048847c900400c0b81e41d004010040c40d100040c00c2d0b1403d0454000c01003050540070100d0b050280c1d1007488002058010390744c40c2e40c2c4460f081219607105031402d0b0780400300540000c41d1860310740c9002c00807045941c040c0c07071440a490351164260f0020059602d460140e030000c103007951000c0020780010111139401094100b4003034101410700710480510410000d42c5010818140c03901e0005c201000c426000600402d400000d40854 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 803473516 1250 803472266 803472277
    0x60a0b0d0609030806010f0207030f02010c060b09010603020c0c04021306052107030f0b040209010c02010e030c0315100e07023007060c03060f0302011d0312030a09330e03 75
    0x220600c2e10740403100345036200c0313003880c40360800303880d04403500360030320b60a0b80c1d9101c9522000348800380101502006501c42d0780d0702c070405441540d0115a90350400009007211009801550000707501041142029000704441c0d00896010344c0e00314a031501101c10700c031098226000e1a014003400082700e0080b07400c4103100c4400000c2003045080300d410a070b40d00034064400400c0103c056030604030a03030203514061089420183d0141c45200100d1840d0340107499801d154401a0b5241c040d03400c400ea66910b00f07010001480300d07808a080d400303182150000c0315410203030708003041a501460030020000e40000b100701c0390405034420358905861a601071010180031110030b6041030804104401080740c19001000002501e840502049071500d8040c42c41c0c072010300c40039001602240e51100c42031584482c80c001801c2c080c0548a012504029a00e0540c3c41643d00c1c0c20056950402c0d802441083e0f540d140749485800441d80e502400c24080101c10841c011620204940e110100200130408000303c6a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 803474766 1250 803473516 803473523
    0x207050703020d0201050c031b07060302032401020c0301020c01090213060b040b031012050307050d0e0105040b0c070504151802040b0906090406031b1e2615180d02010504020102060a0b0d 82
    0xa070703210300c8902d49c04a191600425640c007403089100204015000e1b00070707a882003552212500000350402d02a414004520040c941540103284905210341c074280000c03c010001000080740c17450503441481006404030400800c901d143c1030050140d08054800c4908031803111104507203a860300c0d01c0c1c0395032101c0341c0d500640c20402145a588100074002c40980191030048055a0003080c440c101510010000d458050024104020074885220740b94081c00b9084c05050072900d002ea03d410100e070884400070001c03200451810410007900840c82c50106152020103419801c1c03514003800340c41d0398002c51051901c54400802c0f0708503641c4407540140c004540004d080b923006100c6c0300c0e41aa500c02140103102d6241900e900300d0103141d10482003141298181c0402464030725202c0301142001004940c440014000d99900c014a14601420503006041c00503503c0c1c0800000410b60b460421490001c2c002c1d6410b24041002603a0003151060340300c846039502082840f00400000c2e5801c0c1c2121005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 803476016 1250 803474766 803474773
    0x30f0e0406031a310501060902040f0f09021215030c04060e06010f02070803120903040b0d06053105090304030501020d0605030706090e071d120f100207050703020d0201050c 76
    0x4148100e099410314460340f440303400d4000340c56901c41d4451001e00290303000b903642c074403490591800e801e110280c6541e0f03000300000240c254480554005980c0964801d280c0c0034048402440340502140705140108200f620461400540039403481c0c1000380180020042c809105020140ba103040c4440c01075050001c2041241544903441143ca100003900c4550000d0800d00c2060301d0107000064840c01c1e00c1401e0700071070925040da604404d01e00e00040c801041408180300002d00b2103d0700c0003811950032404d10100300c15003014180708000480d00c03c2a03250720401c10350701c80f0307108030310349104107100a4480214969580d50711140c81c511441e1b100801c6da41c0300203120144154268020f4055410031019070390041c0e81d8010886091040f03001d000c81080c0d4050109224a00070803030144144075000c08003014030700c0b180000352044500c0034200e016400101d4010002042840400c882491460045060003c607803a00d5940b4245800000e008080e080c504800f568040d0701500c01d80c20f210b030203c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 803477266 1250 803476016 803476019
    0x903060f0603110303090607120516050304030218161220130e0c0307030203061504030510050f070516020301020405060304080a09141e010e03010608010c080c1204030f0e0406 77
    0x50400401c0540320549110010440800c154580481150318501000341418200b42083e01c5120071002c2194400b0184042000030490000740300d00c003c0c0a0030f01502c040c41e00c880ca9030051000384419285807a02c0380c1114020003003520040700d4280e80c04030813850200d2103500881820001082640122400c40d01c81e40044c85020460400528840401c20041c41c0e806903030301800c0700448021354104084150900006410fa40300342c2c0655880b210042c40e44884074211840004c0c070b5445038109440b00e800514600c20204040e0042c55001403400080788664505090001d219010380b0105800708498181e0031001c0d580c003501518050480141034540e64282494522140d52180c1c00600103d250708000042044400d07802002040c0301030001c100c46841c00b600060607590030140b8a0502155002c0411161000d02c03c64001e40319500000900c030005000181032500014071042507100b0030802c002c2200700b9407444541103a85401d00d032041c01031510058401203440308a10750040e240000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 803478516 1250 803477266 803477291
    0x60a060c1e0605090a020f19050111100c050a030e07030b010b070501060803031f0801060f0311011e020106080c09090304060315080102130303030b0405040515060114070b160f020d030b01090306 85
    0x10b0044170240300b15001c03124000b07200c0600c8215000e001148a0307080b240d041c10071280d401404000c003844214426203600e4600d903100f020032a01d990000d0400a040480c06421b01b0b41c062061580e024075180080c015103165a5542d00840414000c2c2c40721004046040010030009401a201030504403094988900e01908003e201e500c0b00940440500c4c04035900045140b8180705100596211005030720680c0d0950307c50308444159001000c0c100810100300301002c10062240d0b0041d149203034000301c0d05e90300d00301c03545181a600307080c3d840c41901008288810a0400811641201c1d0342e41004030717001c00c02c004203d0300300c1c0d81a4051030165000107a5039441c0909411200283c0f8480e890800c1111259000c1c4011100201c6004086600018000003840c0500104036804001450207400d503c0b1300c1c3e200301c403894010b110115010045013007800f850340000441040c2251546c03500c6441c644c4c00707610003540c5100c80002c00c01415a50703144030445034030030b40840c00a50342000060007072200d40c9a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 803479766 1250 803478516 803478523
    0x105040f080c150c19090806220615140612040209100506040902031009090f32061e0603101503080307080612240618010806010e060a060c1e060509 65
    0x10709910f15907007400b80c0c190914042e115210071f494000e40140800d0b0344440d500e1303100c000b6240d00562030040054807c0c0004510b40546408095244241c00e040b502e0321284040c2c0d1036480b80c1c4a40701d6070f0140803c044100c01095000d5006404031103c0d017090311100280c2c05440b0903070b00300c56048880081e0225408002c1d80085024001100e2200080d03941d80b0000e20803100b614030028801d24604506d81e0106484101801804800da50703e01043c1000e205071540c0385020501ca09803540010081096101121100360314072180c03a0013865a610300780000036210207803001070349071041d510320300d00c0d40e01401c84000b04055076104940340e6590520380f501601401044568a05c18207030740012081c44a400300e148241c2e07004020301d06000c0c0880401c03650b44090b000704420717004402151401e4804019000950080000101802c010350600c6080e4008040040c0814040c1d008201c04000150380300d800e212444e03411040d05c0d0f03400890060010708412046001034425820700050045000020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 803481016 1250 803479766 803479777
    0x1e0a0914040308090724031104080f120310051504031a040b13081b0c13060302010f0e0a06030f021903052a19050f03010e0411030105040f080c150c 65
    0x362078000e51551504c14165541a0600030380c4044070b04000c9914080701210750b03035550313001035080200f18201071040790f403465006580304418980c0280351911422109001241098446220651451034594900241002e0078030845024260b26011114a00d020310b05440141d64440882840700314002d00d2040c6400042d9001e0f50f5841074540400c6110f010284006c0c5196845031b80c89040220221a00c1c440b0900c49003000070900072299010031540c0c810b955455840100d541c000751540c01c5000040803d00407245a4050000e511004800d0382e4520341c48008603245c9140110f00c4648428400c00680285600519290401c1628204158154112a2081c00180c081001c14244070b0b6521341d40081111042d6010700741002010281002c3e41c00c107200644841c200585080401d400c10081584268099a013520302c120500042086405254068000c2200244210704150302c07450140c0c00301d8000203105440c00544001d0712201400f09079080320340b10910304200d01e4641048030559114 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 803482266 1250 803481016 803481023
    0x1b03071a010806090a0201030f1103180d110a020d0204180b090105070e0d020f01020a0804030b06090a02280e031615050301031a04061104060513080601051e0a091404 73
    0x400032902d0240024010300c20350180004000c80c07503480d001540189210440303901e00648846090720b118240d42c00840c0030300301403180b0002c11014920b4050070055003144400401200c0c24000144820000d410785039540c04940000c06940d9620001d001403189010b11094442c240c07041d00b0601000040d0711b48120f9600703009000c0e5070340e40d900403100a06402006a40821604028005810622001c0c58242d078180119070051045840360380c081d421951040702c41410315002c011042c02d14140392a0445940181942022040041c024140a0004424a500018021030f09a20744130b807031400540c550280558042711101020a0b080e1507150081a1212130720000301d0141d40d00c04c10469040320742040d4062200070006104200042c030190040c0e520b41d440f0320558120211410081c0300402c0223845003a0350700706104000b011013101e544900010f411690040000381c030303165410100c900310809959002c0500c03900050100103a81c20942c0050f142210008c5010041944d09025500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 803483516 1250 803482266 803482313
    0x9030e010f0201061d090f060f0a11041a1c060803090405060a0b0913240e090703030203040515070f032105090c012a05060a0f1a061b0307 61
    0xc070000c0036803d0300e01c244501c0d41811030280d42000c1854411604581224100c0150381e007000400e4801843c12a059900e5464405000c040c4680c0c06454404d604107070792407400e12030800b880c2401d440c014201490102d5036051002030004d250810a07500301c0280502008100700341d0b034644015940d81d40190300568051881d1001040042c0341400d050340c11120b4190002e0f150800b030800f8030a121402000c0514042c2e01c55110f0b202000001100f0852030b211601300c401018030345260000402805046045a600000c00902c0442e90210407034058940c190744403070001c84149811000c0d44240c5001034070b003080e488181010580c3c400c0d21600301d140204046085103148158904c01c8601c00d0720b54040b5548080251001540a0b01c1e0f1780c4000d049013030308103841d1100c20358500c1e8003040508007104c46030000f0341007140210080c494500c1d0090981e60810041c1101e45001b1103000404007198400c080108982010350241141c0c0c441c1030240409994581c041460320f0611140c1124041c0c81800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 803484766 1250 803483516 803483537
    0x102122101260105160e0d0f151d060a151e08010b030304140d08090405130501180b04110415080304030203151303080414071d010812030103120201020d09030e01 71
    0x60b014080d40d806080b0b440000c1d42c02c40316a05040e625400c000449030303040440300440501140c0c5024252280e140511114224421402d44103009c5601c6114288061003500c105104083c07000501c46a024041c81000600440f03002c074289011141e40e4002d1411504400c0605c8950817000c0b1800202d80e01d14000740203141c01c15007095140e000c0c0d40500514030495480309850f0f440e11b044024401405000c84a16055a02001c1401d56004449a5160003003c0c090801044024800d040e401c200c08040c01c011803030a41d4903070700c40380380240c40030313101c0c406290391000966925031100074083c41745030404100c1640c031681d4039140e07001880305a20a0040700e1400c1720410b0030114951241c040b952850b6480219a541580c0b01d1030068419a00180c10503034010800d60100486006009020729512000302c180c08011403428050f002214079030802400410719034582000d59055070361200c2c8441100c0700000049009000c2c0c1450f020480307040640101c14160031281c080303078442007039a4140f0740c0c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 803486016 1250 803484766 803484839
    0x40f020d0c020c1f1e0e130510030201080603011b020703150627110c10050a0b0109030816050615030f0619090f12080105030712020102122101 63
    0x1c00283e22201d8100f034808240c051518004142d02c01d5105a90400032040d00100d00c1c10340302540c0d07111141000c1a1071048609081c94540c201907400800f0000601140ca020343d42500c04001501c0009d041c8082480412141e81d000e40040302e407a07c001c42480700920680600035a1543c86120507101002c444e406080d00c01818007500302524401080e90015200614903a240100e10704007003004a030b6100007814a1190004c020300504180380700504204c6041c0c0c0c40003003241d50181510079410f142903141035260340c0100c482000c89402c1458291201c1000c0e0040001c81c00e03c94008200313020b92801c1041c40262105503410040040e011500303120441c4840701c1c0c2d598810b860411843d2603001a03884006810341001c810a8030444405180d10b16035601c0e410310205550042001c95000350042c00715003010050100240041c0750b00b401149002e1700040c0d05c0718010140300104a10015a207004800300c2d4095040007148003082031a50b6035100c500000f00401e03001d0540b0103c56452905049 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 803487266 1250 803486016 803486023
    0x160b01050a09050c04120311060a0f0c2303040c0e010902031501110717010e0115082506051e0c0a050d14030a05040318081b0108240a05040f020d0c02 66
    0x914013a02018546424160369044548030350a00302d0411000f47c0000c0000740050090a001d06182100030400d070400101000603240d104841c0c1d410099181c040103030015540000c109101c00c901629035880d2030b1424101c6003420141c102c20409100040001400e10341030f8000c611070211103d030545500c40d40c5004451801d081005100194030441050100000201c0100100e41c102400002c500d401e10510707a0a40e6004209410081c03c4640b04005d141020300c48a000100544140302e502c039081c4c810000261250f028100c01c1040108100c0b201b0008284400c2148170403894003074036000701c88842580ca800005080b240c3c0c0c000c424041324030b03a005402505002c500c5521040c1595228204040101001403054081040303010b564a00b0b010b1035480c4070054580c0c400a0b210b440300c10100714111010500926041205003801c1201e100569000d1807480c000009445103100318031000601048000d4002650103803400c56106a01c2c54141e0003880b10b900048410f01111a00640c16070701c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 803488516 1250 803487266 803487271
    0xf020309030306041a0d0c1418130302010231140105070212010b0405010806041b0b0711030f0615030c03150609091c171503030a0f0203160b01050a0905 67
    0x15158002d00220b545031420b038000807806000000c45008201003040040c0c00e00d40c191105580c3c81d000e000e028407440304006044c140c0c010068602e501d00042c2c02c2400d000d441c100401c20350602079400c10540030103200b0b404507031421a012610031050b01c1903040e4040c0e0840d6400032658402148000080d070310590310f100c660784c504c0585030182404201c0e001d0050056422115441035540c504600c015551030b0711415020b06102c0f1700620481c503051401d0750441c1814040010400c085050400607100100e013152000b030790141d50b060b180842c002c00b103480e2200c0f4900501090007044208104070b034a000c91024100d078100c04407089944030009054450742c403d080303200740c201001c00294507418400304203600003209004491610368900c03540d881c414008cc41020008034180b10401030300045001d102d030041c0030754141600154030a00026924030410204509105a00c2000c0c1c01d098000c0c000c0d140448240000f04040e60014a40111000c209021300382c443d0b1030548004c604042d840c0b05451 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 803489766 1250 803488516 803488531
    0x5060d0c050d02040207120203070201021b240c01290f0a06080c0d0507030b18060102060103030f14030901060608010e040b1515210622020d15030b06040f0203 70
    0x440324148001c1c8070062030100c20a03600980c080001200003652040310012039115580a503443c1c4501c3c0c0f00090619031060500500b4100054000381c4039620058034049888848086801950750240780424900505d0781c031100a500e0520300451803000d27110704e0307e1034481c607641800300c12400c001081003083c0312003985500300e50001000d206442c01258425003010300e034076510b400c0203046c0600805580d81100c070040044e4440310b40082902700b0005486c81d03000c41d110a80300038502040003d507180300510028041141d21052a2901405082030703801407498601c16560305d01d45500628080d2240703104220006007400e00004507100801d030b0b15405a54080109040e5840f14400640744068005016501a84000d400e200c6a11210002c0110501510064000840400000c850f0f00002403800d40291011000386510000c159881c06030810211401a10b0705d58012021004000f4010b5900540031529008018048059039240c8184000c540610900318001500d405038042600c991 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 803491016 1250 803489766 803489783
    0x20c0f0a230303041502010903090b07050606130204050415050901090b03120c0c0a091b0206090a03030e0a0210120e0c0f0906011812050c090907120525050405060d 72
    0x103052007000e4411014840034000d0843c0d040c0360310303a0710203035054409004900c01b6030b564125401c10190042d110100806448400c982010141c2d140c083e210500140710900c2000c4d40c0e04c411143c40c9065040d01d000d000d0140c81040031101083c45400c0b101100d020720791080c4002000003d031341c4428060200750f44009001340c10b1590310064031600303d80080009243c0d500888110105030380f41e0780c3c52000149100034000c076260001041c4080850b080c48140350454000d841085110000001d10354006c1d45d0619000a070b44049c03648003400e000324950b000707500c1141155243d0041d0740c00013003003840c910f0108080081d260801140e950b1201884a4580c1100e07030303642c150f900352802d403040d540c2c0681c06042444656211492026100381d0940100507586562440c503014000200050900e030941039402103030505000211039640d010714840d14134220641503400302002000e0184240300410380c00c3c038401440301c507001a608140c1c940195402146408002081d0307282043c0f0b10002150800c460 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 803492266 1250 803491016 803491049
    0x20d0b04061a1308060a020703231c0e01020a180617040611130312030f090b1b070b0f01210c060f0e1302030a0b010804080412060e01020a020c0f0a 65
    0x72030105800c014a00c4481c0c00a808000458203405e02185114215000780141d6400300340c0350180ca10000288a40045200b02000741c01c2040d1800458151074520901c80100c01811203020000c2c0c2031a10340b0150303d50011401c10785c034130342000380301003008201030300150051f44410040fa2400c0a000801d2a894540b03000314000c1241030340450030250b842c910b00c1d85000700e03120940000303c1c0700d5402210703c0008001c030b4541032507052040b11007504c1000340504c02d000440d2640d5201c0d140c00340c80c440d01200d81c0149002c0d098841411610b40300d600c40f161288620745102d40310b020700403d100d810712801003107000d6601900503140060107650701001e00b0344814100402119021070103a01c0d00103101141620340300581e601500017080e1400c1120250307803890902074510545000300c00c41414001d40c2014080000c000e842580c058803000c0d20004441e09050400b43d0280122a161180a510005801050f1940424940d00000065611549031802c1700309000c88007203d4480e40114010680782c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 803493516 1250 803492266 803492309
    0x61509330e032d0c0d11030a0b04080d05100302103207050c0301060303090b130b16061b02030406351605071101181701020d0b0406 58
    0x60301010803000e403901004104003000401d24118030380900c0702c03942851840080f0307a503902c0c0340e0340800b040f0300c0d50150900c45840307070214504414007000105070085035005c0c00480e4908014402403640c2007000d1100c1400d00d810305610703560006c04042207140c204000240c010203045081b0381280d0f0f024010120411070108116015a042442108002c1140924903140c1c0d5480440ca0503403012017001c5c0e555010700c4d14082d4500340b80c0403c014082c0e4185202000401e0304040010101c0c4c1c0240030190b0355041c0c0028403500036849811502c51058049106d0150740c0300c03550000c00c6140306d03e4007045100c103070480ca44080c4001071001001640100003e00ca550312580b2000d815624a8407000307030b4a6290303020894407003080c84410618406030002c100d04440c0304903030041040154140079181110b20744803075981c9011442d426040c05480204032041203642c5680c00d004201d0f098003602c2d0700e100c0044040c043d610a0341c42c18001030400003119040e00d80342c1f0401c02100c0b07a45e48034981c214080e96 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 803494766 1250 803493516 803493599
    0xb03040c0e01140a080d050f0a050c19050d0806150c030c120c060c1612050904060305030301140a050a0e07021c08011a0703080703150801061509 64
    0x10011580418a5240018101010300301e81e4080c14a15041e03500c21007408060010041c2241d001d400158805c501d20341205800108507100c2a0008180303580d01e04166000f903400b480b600301c420401d8441d52001d148844400d02c10201d80504c2801542d64201e4401e0342124030710401d40c0c0c640c0d8828041a003803a58074000200030300240e82c2c200150703400e182e21100c07038504010305034600407001840060b0641044409000d0683d000801d04406800c0c0f0782080e18103070b45581c11500040400560034041da154038000e0301070316485040140280401c81e1246820b40d10f07a0420700c0740302003030075402d08150568071f402c551800c251003010388103102c102c0c6071040410302d42c08060620000e60140c51f003c14988118207026660800d0700ea140c030041c07945045103d070615054950043c0c50780109000150009070f2100715035812101510300450f1a852100102d1145141c0e41d000450642c0707030910000710803c011100ba107040300c01c0d44990b102c00e07969082e140d0064504240303c0480c2000f11503000500b56001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 803496016 1250 803494766 803494771
    0xc150a0e010e1302030c0304120c03050d0902150a2d05120a0212090a02011707051605120c1509070b1e09060a0c1b0602190807080a05030405010c020105100b03 70
    0x2003000e800410034504030f00c1264000d0704e034800242c2c80001013205020030800720006c5074900e0314161440d040c00f9140100207000385541c08410580304c00c046425940d440581807411044144020b50340c100042c00580080d50002c800c2c010702c02c080807046040b585410021a450000d51501c510f0044480b403002c1480000800303007580c0b00c0e4240311980c030320469006024450140b15004000d40705e500c0c000507011286034100d80c0b00f2134040c1c0c0e040000d850fa201080d0b510304054040d41a01e105100e1074900c1c02c01c0b011091f2285002c1d8040381030701880a00141031440916040c003249102d86071005d10903161a4940a0110b03200740c00c00c100305a241c0350f1507d5111000d0780b002210709166844c8002181944422600e00010307010b8030a21050012091006e2003102c03201c104040d80f50302d810030103520350714800021304094801e210800e00340070003082212040d65010002e665107010320500030700141c005440c01d40d4030358600454242a90300500c6a07034002c00c0c003e4289441c207481c0c070003451201d9000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 803497266 1250 803496016 803496019
    0x222051008012d020408010216060b040204121e020310090b0c030f010611120a050405041d0c012007060215070306030c09020f120109020d0b0d021503040f0f03020c150a0e010e 77
    0x17004001503803502807010707080755814410310f400c4a4010781400d00c142c0b400004028403c40c070401080111102000c0002442e66011a82c40e242004140310400354401090020390503000e20315400d41700c100b80b540301440c0113104e04806c00e0203440d008214415404101e8060850f1a18500184121405031130000c0d00c0302d01410071a07801582c508941402030b040070361050049400400d082c00140341902030a246841a07000003000e5110100c2150749c0c40c1101c00320681403015131881c0c2103180f160300c3c20b400d980469410488210f50f65611000b5a64070741030300006440d07075258001c1081140b10f03002d524100d903000310b6060f000c503081c0704483c1300030750008102c0f50000708200403000d01300c0311900190f4020801e54400503141c021004c1844207651100c40220b03c0703061440e001c0c03401a99150385195820141c0c000080d200c2d561440c2000c1082e108010140c030b804202650310080550026800c0514841a2000c03a40d500003108600414081c411858000c94068400c02c5200d5118604002c42c0820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 803498516 1250 803497266 803497271
    0x708011a09030a11220603060b060c0706080a020409230609090a0308060607150c0207061b0b06040b0315010303030b0402030403211b050405030708070e010b070222051008012d 77
    0x14107901008280a011170260350b1507854100402c1409458420400580c909955152804180d203a420380ca41c1c0090040c84140500c503804103403140c4807603059502404040700204004a003040c4a084038560052440c920444404006205410320220341402610100300519480301c0c190380680d00389000910a41d00140c090001d4004600c1c40414030f0318940102c040003c5410392010000e041180c13030717006042445001c0180c41144040383c044003882030b40000340c0f04071a448060002e00640106181668141700341224003840da100c85100d10704807886614108401ea0341c00082c08140e000c11039014001c80d15114204000303135690480360015413410200043d403803544410b0b8111800c1c4642158002550101e01404281800c2000a01808560780180240c519100074008502c034140150441c0940c086080f0741152a04401d16680c018070002d066a2241c12441503402400200c5074055050305541e0300041d02e16040c403078624000c109155683c102d070310310300c84110b42c1041070700300441140d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 803499766 1250 803498516 803498539
    0x160803130b07030b01091403070315110a02031c140a02030a09020306090a14010509030a0f09150c062022050a0f0608070f020703020d020d020301050708011a09030a11 73
    0x241c0c1100315501c42c40c56600c0000d40b0840502c0010a69066500b0594080540440c030344101c3c0c1e00000c810085030351050381c2e0003040e081d06860001400422000da180e1103004100b42400c07540201c040c04410b2001d245822006000c481040d05072075241034402218895000071950345030f0690001c6501804ac440302040c03000c80c6134086480c00d0300c11103c00609400c0000044200012038035000b51920384500240514101016402d40740e104010043d01401803d1400d240198080ca172940002e11041d00c4015503003858610282c50304112280448004c1d00d40340188500000070088003590521000d03c3c14204003401600303c11135580388051288071520795100240547d200300701d081c05091509408006607142450180c00040c001e07126a06120500352500101c503030000700c0302c0c11240c048400c07d403840440d0000c00c410000a40020b03405500346003c0240b6960000c400394100d54506011000c12002403151203211b020b02602281d0582000c4404070129000350460200170f0b500600c6641c010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 803501016 1250 803499766 803499773
    0x20a030f0812040803010810090206030723040603140601050703020c1903020a030c0806100e04020904022e020705040e0c04020c1905010915050f06192c0105010516080313 75
    0xc200c103c2c0c2c00c46400f080040107000514051011000390f814007070741407084c0d0480368000344075400010815410801070f019400c6e4180341122045c04800d4283e004030303658035201e03a4000d000e0010030094125401c0e40e140810710383d51146080700d030602c1c1c048c0e0103130412070300c8542006181c0590007860546c4241c0a4004005030341c403075010304021446002d401c02e0340c900e020f070040d00b0080020411a00128880e90800801180d82a048c0c0d10a82c119545051640d6510000d02031840a00210794000302424000303150504441e00c8285103800c2d078007122440c699680c2004162031038100100c2007500018039540741400c160b006040c000401c0c00c107441c0040f00c8207080c4c0000704e0300480d00703031a940e45642d4800c041c005110030205068484900c01d122a15003640d01c070040301030103048240188440ca00312100788026100b01e00140006007034003c40b0b9680c1d09105080701c94480c00310a4030070800000042e82c1c0d801007044600a603040c0700710340b510f14000c0e20341c0d403015000148002102610f902c8940c001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 803502266 1250 803501016 803501047
    0x3031e0e0102030109061205150712020d051b0f0904020d0905030a0c1703013c0f0501030e061b0c0708071706070806011b14060a05010e0c07020a030f08 67
    0xa4064030001602d03503140030301e0582600c486070301c40c151950010070f0080c003040003c584005201c420407200d500c2c0b625441d60071180c1d040384101a080f01da02c003003020490000e1030f0b040180140030700903021441031200107100c1c1d860300c2403012445d000d0600b0000e248050500350080c10440d000f0100004840501ea140d040c06c540c1300d8140200000c0414616200f040164500b00c2542c03da40b201c0241558100b045228941c8000f0006c50400b801d45100144031083c9245503503000c80090088000040e40ea5240050001546c0a4240428109140900c011400082c0d0a2161000400038001100680c4804000390311000c0e00f403171140200b020119030b0550070490100105400c4403500505504071850600f401805001d00303040080000501c40560381c00ba1075100155003c403000c94080c0c1440c43d03c00141200e80c1c2d40003800d40140e00820424000c10381c40703281202c1c001c48041045581e440c8045105204181e4000e40c800c07100102800030400844810f94898850000c2900d00551212040d48 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 803503516 1250 803502266 803502281
    0x100f02030d020304061b030e030a080a020712050a030c08160e010207030c12030e01020a02090f130b0a02070606050307030b0c181e0301061a07060e070329160c03031e 73
    0x1e0170758441c3d40b82204d8070700900c0980188829403a0400031144c40ba05801e490b1b2203003400d2541080200c0e030102c0d00010180c0d04882e0030a6009810303200000e0484c1000e8a680c200305140307004a40307440825510140280b56641c8a21307031540c1c05010385404800242d903200d20705006c2c541140305408010000401401001d0080c00d045419041013a1705840c00501c405110401c090454001e40511401a16088010b942248440c80300d01c2059407681e01450340400c0e541320140006d00da110a0080c4c0324400c2d4001c00c5007900031181848504c0d10780041c15541e41301d501c80201549a000005020303150b107170004c0c01ca51547c0401300703a46103107100002200b4980c24010f100c03015000c01c41500d0585001d1107178100030920109002c40c82001442c04120314000d413640540842d40341d0400154420381480a0409960310080c0c01d40d030310ba01d000026002c91000c50041010403010b80108560321503000b011000c0002944d20140803141982d41103016180d00d0702010101c401440d06c2c155007203004d008840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 803504766 1250 803503516 803503523
    0xa21140111070c0e011d13020f060a05030f01150c0f15060806090607021b010c05190f120203190c230a15020a2a06051023100f02030d020304 62
    0x901d0383e414610030744808007043c0c0c0040300382250040c1c0880c0703086102c0b01c81607100007407401068007141940041500030000c0c007021640690000b5000001e15000740243d030052030381c02c1307091141d607881d100f07075203000e03000003614401151044c2e103c200040c1e4002c0010450a1040e102c80544840e521040010381d403054000c404e00c2d401447c00c01a80030310410505074081000d00c014510181066541004503000002d003270f04010b15a0050030512108004040307010002a040350407002c41801c0403644001580004c4404200ba4170318581141d01c00410380322016900d42100a16542840c001c0d0b403181a20300707086460740012107199901d5408030306540c4840c5405c5e005408010243d00c0c001a80d03010a40b00180024414010a0080390380706840e21070f040000d080407401006002541c961007000218003d00c003908200420004018014298088a18080600703001ca000011100400b0b90706403002a00480d00c92043d0081512642c82c080f028079241c01030301e1900b15500309802c1640d00403207098 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 803506016 1250 803504766 803504783
    0x120b07030b101e110d030c091401080a1e09050d020708060411240d021c0b09040b060f06030a1a030a17090f060d0b0a2114011107 57
    0x540603058010010410011030b1902c51a0514800140a5080b450042111071414441240d9124007604544890049520456001c003044040c0200500074441d01880002d1100c100080c1c009080b000d180402c0d00f05031170703014450b5100140500104110301e115410100310b1861600354400a10801c240c007401400904100c001040010b440d1040940c030461503540034030b08006c0800d4861200112502c030858000e10760302440d1407001c40828001e02226030b400d03c0002c11140307001096005100030080c11240c94070410960010008465a01745082d030420240c00c0040d00052400c4452503002c10014218503243c0458008284c264000312012140c45968105204800803249540401c03144110001d10001006030384030b00200c401d254165a0b116000b007403506450baa0100b0901c442113010380f00c140c0310b0b80c0082424000d4032811074064080d80c030080000c10324080ba0452001d01340c05c4000f03000c101155a6803036405070035100810850313035580c07401454181409500100250740c011150b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 803507266 1250 803506016 803506021
    0xf300603120f08062709030c070b04090606030e0d0c020312071103010513080f070f020d060515121f0f06030b01030501181104051305010c02030a0305060a030302030f030c04120b 78
    0x20340101d42c0506900d1085da5070240122060203141c00820710407014003110412a12156a402e1440c0220050310b8102c1c01001000720725510b1580140c0100c4082c010140182641c0780c10543c12907036654400c000c01e1304000c103100007182c0540b00c01500184040d0854800c1203400280c01502c8d04813040444a18091040914a51600b4000c0d29001100c0c6141c030130b00380c4090b580f44543e23489080070340104840c0125900c01130181c05803404031202e402030119010100c8910b820002480c040ba5030308000d110038010542c140c142540b0a0142a200c03400622942524040f0361021007001c150811883d03840d10103102078070026005007070055216140148855040d41703082401e4812840100e1716040c1440359030070218081e1510213045c00c40a8500040d2522003954951a01402001c041c0c150340c2801804181594000300410a11081d40c0c0d0420558454000b00703c00c0c070300f0324070000d001a031050008207080150400210b0b04101c00b9110710f803802c0d55419248452000c194000c5c1c0d45c03034052808 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 803508516 1250 803507266 803507297
    0x40b070f140318070b0f0702130b0607060b091e0109091407060c03020f03070f0b040203010905010c32031f080f03181f1409040603120f30060312 64
    0x1540d000380c00d0b03070400d503400d00a1101001b417581c0036a2030301030300c5000e0f00c18061a80e10313266405400e400601900099540f0f019080c03490207404881c000b03a020b00d05a000082e450f05448070b45641c01e8080482e08001640707440c0c1040041c00300007200351003140c070280200c0f4a0701820829400288604d440320300c0e03091001d040203410046089036031180c681040041600141202010340030060340040506655103441c00031030700400d0700740c40c0148a036183c20040c000302600120603124240304618000d080341c1c02c0403a030601181c2e004042d01003c01081c404034110b00f4071b90b00040309a21042c840c03000080c0da6410914a42580c08c0680c54040d000007405101e40c174000512810360150a9800340c1c001003400140c03c4030074a07951494010005210344ca80011340380602155284038000b403007409003584a04114080000301d50350500812180f020481c0482d01583c0240c012010791111906426500b5540c0c89614005403000c0d85460b0707440c00044009001f860822556240300e584000c0800c80011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 803509766 1250 803508516 803508523
    0x105070905010f09170d0201270f06021210090606030605012f030a03050a0b01050a0f0c15020711040b18040f171903050901020f07080f12040b090114040b070f140318 73
    0x1201c2110000c2061075410008504003600e5009510034070416250003182488400de000b0b0b00308070040f134070f03070882441080200c0521060650b0743e4031408000c280c5c0d076800141c4c03c4805510500340480c02490107034050350003ca031480d55a60030f40d45a140d601943c0046141598820400040406e944100b40038581d040c074400d2800840c0c003801c02c94580400b242020b040d02000603d0301e4100600000207200700500c01001520f0181d29090a540351050742c07410005050040000307a000340c0c43c042101b0190b1034842d000b4990440f6800c040b0100c0d842d980c9503800601580c0d041501e00340c2c455028503a5441c4144000c2540b01d803c07840d14034181d190303c0e100070103440c00a043e00c40315a005000c0720118203030450895a00503400000107984101103030141c40300d03000740300b00c11a800a01108110502041d170124030310550034030000700b01004c10000100f42c026010b40e0042c102452000020b204140600b00001820b1250f0034803251241c40b0058a1006030300c11100d49001a01d1384041901545040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 803511016 1250 803509766 803509781
    0x1207030903171b0a0c110907080402210d08220c1403100c030b1008090c060723390f1c060203010302120105070905010f09170d0201 58
    0x249414858030005403001084082204190409110309002160510754a0360f80e81145158040000f500c924040b0400703810a09030f40e40503170710f214080c0030550651412403820391090102c4d03101d00950703484a800b44031038078064042c000d00d00c0711501c1101ca0515001c020321f5100c444d455407262060b140c483c00c81d04580103200f0620b008007940500e1035000420f2041c840c1c050fa000030300024081c01101000a1510b5604d65821400c40c2c5802221980d04d40d01d600040c580903420f40e07044000e05900501162078001c00c071540003040c3c0056420003081e10f850310041c6141030249140c021155201340010b00707110000c0c8010606076001442c0b01d403010004008080d03019140040c640045160044c0c00703180000180c0040e849070441e60380d0b8003c00e580711416004480030145a501054089242a0000754004c0c04140e105600201118020740c0050040b5407103804203a0703a0b802c4892a000040d01c1c5035003014040010f10151000c08102c02d0303041da01d0310b03804114000003408801c00d0f0311406421a043c0f03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 803512266 1250 803511016 803511031
    0x51005030d02060f0601030915050702070602030414060f0d0203160f0c0506181c0302091c030e010f0e060c07051203040e131a180c030601050d0201030504080405060f12 74
    0x640c02104920b03000b080c041c1d40081e503100030f400695603075001213000308003494000b0515001e04680a071408075603405144602400e80864001544901c401e90f0341c0d0049115a03100440c42003500d01090920798080c10101765a08070990401d0009081c01b01a0303041159490624810020782c0002d99500c4110b03a0600d042c1c0e03080c5942c0c1c84401d600c940ea00c86000518090030301d01700a00c03c4034008810040c4903115004881c4c81136460b826007030010b010b035000b220000d22405103807188a041d440002880301e001c40c0d1546600409585050054841c190101d1009084c41004a84c810b0a91202001006c16200795009070805c0d90a0030104585004542c02581240c0d1007884144074908e0842880d6401c440c0c110032081180c5800e02c2c203886112103580f10410b10803860001e001403072034210303000340c1c21000000656000c40045024140d80752400d00c07965074444241d6540d103000d94020b512064010f030040c04528641511280400d069500c82601010000300000d44ac4805802212096800050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 803513516 1250 803512266 803512273
    0x170c0307021e13091112150603030405130b0f13140c030c0313050a050d081e04080d0b1c050718090c05060a11011a0a06050c0304030303151805100503 66
    0x4041c0401c0102000081c40c0f4200380c0d4505411042c090110885080b4010080407880c01075200c2004545800f0003904680e00180c5820200c1c0b4146808421741d8240ca201603c1448200007440c10b1a02820981103406d8001684c0100380c7d1036501c072418180c0fa6140340b081c2c08200c0310300402c80d0f65141030f03004180741c50090050051220030f008603401c40340c000e07010410b41d241010041c2072113407d0102500c00241144207604070030100c00e801464441c0b0419a20928035a040d54828070b02c00b00c40401c6a000703150540421041c3c11652140d40014407205001d00703580c000481c0446000400d034441a810b0b661075106000402c80c0d00c4080744480344030500440248000c00c0c09540e03001c1d1219090081e0340c0711760000300e03159000e10b100301c2c030a103841c45a0000038003603515080464144603a0912420303000b15003514010403914000c00c222040140e83e540150b240c20b140d0744040f4010881c00014420000e130301c24000078800c04071803034040001c1c5140000034860400b01820311280d5103e41c0b040e0300a40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 803514766 1250 803513516 803513569
    0x1611070b0703080c04171501080109150507020304030602070c05030d02070602070e060616060e0d0912020904030302040e090313090b06180a0b0a050315010306081207170c030702 78
    0xc200c082558440ca506051400b4191a060014034142c01113400503a106800c42180e00700038a800909100c0c0c900700405003a9090341c82d81451341c2a02e02a5802501a140c0c00d82c50090150300c0d03030301490340080e2510541e81401d1301c91395039034142e0707008020545180c02407020034003261602340000c0c1401000c50006240d120326015001c1e481752100d10400c003603001410001040d0380c864030115040340800512250084020303140c00380003000d0306443c00d8007c0c407954542d1071103280900b640e68141d41541c4070500803001c07640e0130003803c5c2d04014000c504154003840001210300386407446601480c08040610740b903041640d1030080c00705007035001104e074a06241200b681a25a803013210241210180c405040ea84a0004994000c130184d00c070342d6a0400c0014440d044640c41005540241710708084840d028030342c400110165460b90165074030a4003c401c805804218031002025014400d0100c42c00001041c4000401034001d00e076048802d13080000c0040c11446c205200200b241030b10b181d15000f09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 803516016 1250 803514766 803514779
    0x2160b090108040b0703180f0c0e13081b0d0f170c0a0309050c19091d0c0d06180b01170120180a090b09010e042f09161107 54
    0x1000908044c00c3e98081c0340204981e90710a400030540d550401c9100320702000e85207080002d0f201c5643d42542c050620000c0860749482e6605070500494a0451040304008141c0307582d659540014081c02e542c41c0d5008000c2d00826040c80140d904040980b076040d00040425400352800ca50040340c1008448040c0400140f01140c0d0242e9840d0715240c40c0000e00729010f40307401850007190f2000c440d40003c0b00c41c1ea035980c0c105c0204100c0280c40d4440d00c1400482d4507401c01c1c0ca07800800407080c0203d030704102c400141c94141000b054003003d01a02d00032030005004051492011014001554000714410044c4900071609040c07040b0f0030540c40c02081400d1a480b00f0321a6254000d00860702e100b40014074036880780c64221004810b80d00202411100d58ae01c0d0303100d00c01810004125805a030146000189507504448001d22440d04002850364107400940c502d10249444100e44c040a40860700b90082c0c0e48883c40c41070f10485075000041e14240d1001409004032000c3d8010500e541e210400c10b0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 803517266 1250 803516016 803516027
    0xa030b0708090c0d11010e18010807080c03060c130b0c100b0616030e0a0e0108010515010f09030201350f0a0603020609100e0306190c050702180a180302160b0901 71
    0x20640c01417040c651000e803240c01200d01032800c0381c1c4503501403010311407118845d203a800054101c2c0e004400712110a980c6005003034a414015181c00e07450b400003800a58000413110080140c2d100b030004401210703480d00034040064201c04074024250b8410200304031040e90b91310030800010011610f8900302010400c844143c0100d182c0001c007040044641180701d9110b640e5101b029000090a2841c00d6031540d610a0092004640c0e800ca545000146d0f081154001c02400c180202c0701c0d926600340e00e007543c00650f0100e092880e080070031001c203450000c0c20481001c000640c060500710f06803450400259207180b000c3c01622042015151500400059503401e04481806009842c1070440b003c130b804c41030b10420400307034625400d07004282c104203940034948a000e4407080701075010805590385840885030340c0a401c000035048000741c5440f1a46010007604140d0043c0300c114040350035002e038841c80499071fa00101c100d02517440b298000e120006582d80d148040c0011300c1016045c9124400000d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 803518516 1250 803517266 803517289
    0xc0f0506190f050c0d020a052e1505090103060203180c010e1c050d02070305210304062f070524161403010e0919111e0a030b0708090c 59
    0x240b01c1034401d00b9059901481c15144003250500640795184031510020703440301c00c0071800700d03401d00500c810380710426022542c0c0020b0190b041052494040c0407079403c0e00400030800001c848411034030f400a9140d9440074100d01030340c802d030f4015840381080180310065411000c4200c50b01e4000e03140072010381c0d0b400b6011203c0c0400440d40b0503401c10b444094060034512410010381280248103034904e005d600012440200ca100d002101c0e0000003915071000f1061100a52040403503040010070f002c144650449103541d201850054640000b86460481030f0403401c5800d0303c0d101001c40c00106002c428450307080c203c180040010340c42d240d1080e031a803011400520009482d25081080e000715031007001c07040348405c006082c1c11794950711880402c171003260881e207002c218800d91048044021180502d9001154400c400960084068081018050700039603001d685c6440c0c0c401c4400c060f550b200070400294000c00101c9020708040c1d8004100c0300d0024802491a840141e0070703107507519403480084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 803519766 1250 803518516 803518567
    0xc02210a030b1305040c06020f0f1c0302130f140306041205030c0c06010b07060b0d02030c06030712020d0b090915062e020105180a0f17160c0f0506 65
    0xc1e0301c82c102c0d0005004000700c84445010307145070104000c20480b0300e4015a0036600c06408881155041a501c1541c1d0004801c44042079003000c691190300428461b000034170307140e050a01508001055541c0c090318100c80c0e102c0c0006140c0c0420400074207a81d05010040c0da002034000c0c041e546801c1d11481c7c29100d04208003000c01c81d00000003400179800109440e00c5d5110407090320215603548251090542108ad070564070725241442e40002454116040440140d021b00605003413a0030380100001508001c00a80a20040b08402c41049070300388010450451071600020715100700307400b80040c207080200704000f507034084501e074818201c44600e225030109007203c100e9042015080c4076440f00494403400c041c40f2102061042801d5010341185220300c207a07088003041c1f036820150b840e980d102e008101811145003408203402003901c48240b0540400c001d0540c624061140803400001c4004074400d441c0c9001140c418009104100d6186004160840d280341c18088140c0700c007807a041c4a80c0c2c2c0403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 803521016 1250 803519766 803519771
    0x10c060b27130c1509030203031603080606041809021f021006090b09190b0a030f14371a0a0b0303090a050609030a151e110909090f0607030c02210a03 66
    0x10131040f031180d60004065a4090103880d02c0c1c06031650f00076100341caa460202c0100b50a1000a1101d042580a480849015000c000380704200802e0070350003400d201030706a07000a085541202c101c030305c000382103074917038501d500400715450000718140c01c4864907000b22600714101010780e101c1d95038200035542c001e101e0031031480480e5a8500c110b0300400c0c50321902a04145428400000d22160a8100400714008d0100b4428024200c0c411503c820700c4071515100701000b44158034000c011941d0000b00030072544c065006c614107640703c0810204e440c070b0164000e5422442081071030382c814018502402070076802941041900c1c0c00081c4c21120724050300b4011040400c40c0700c483d070303810044044115000040801c0c000d82d6417101d02d02400028100f03000e190701c035556038000504203104200440505451140c1020420f00802000b0800900304403014810041c440480301d4003803244e80d000e0107541d20001044030701140040d0802d101d030420351004030340d1700c11410303285490402254008400351600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 803522266 1250 803521016 803521049
    0x30f0e0114211e0c0a05040801060e07110d02031e25150b0607080304050c04090303020a030c0e15030606040b30040302060a0c030f0905160b0301080c010c060b27130c 73
    0x8681c18081d648c04450558200040002d031103041c501028040c8089a645d401e00381c04285c88280d03901071100140005a104105450341a5148540143d0031440304484130b107454034428401c204483e504e081e884103101c0c00b980d12410803920039050004149003610034009041050000f61050281800140400500100250420200b440341a0b40310ba80140100300c0c250390b905005001b0340110303540e0400f21b458003491180150281d49003c4080800400c01481400e06c200c0c925165000500290b0300f203407045c0030100303c100b0030701c020380581c2482c09584a03441f600c0d01482143c00c102070318424811070031107043c400400d0740400daaa50010310142c001c02e00014100c0110010106550f031104101e1800e0062004c22001190448078009640040c004054a591081101d88820300c1111001e6003e0500d01605502491075244607500400300000e0740c18020000c280b01000c039460ba0b070106c106102c0101c14655600e03800c41d4010303081c503000040b40c20050f40d441461162038002e00c6072440c3c80911 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 803523516 1250 803522266 803522287
    0x6010c0201030f050403020a1b0f090f1e0b03070509060603040b040314040f09050721051504050103110306011a09090408090301020f0316020a030f0e0114211e0c 71
    0x200480c0c40e4180f20401a914003405e0094803039102e80f008403040c1d80d02d682e45561102d021000401030750032070100c103404907251003030340001440c400080b52407040c0c403800968a552a0600a005080410300001c030710380e82000d04250070901682c000703501c103456107018045544c58600c1541d0f44540e1140c502d141fa0b449070306043d5083c8140308006c02c0b040034001800f04000c0074120b20300702110520300040c801038031505000d40b100040380f219052a41c0f004c602c0391500549507000b1070740002c2007040e00802082d80d80040341c183c5030260016101000b03000c1000d1110306042014034014065041000c0d1000e0241040d00502e00c1780814a03445002c0d1040030a06016504049560b05000240210f645401d0604490002d802c2220741c6490710702000d901441250021406486c030300d5140e40e8050096804403800e0b2070300d030f82040c2410304020807043c40708010f0650100800c1181000c2c0c0c010f560520a0060030364070303800010040b81c004201030308031181801b844200e039904040c080c4c0e8000e440e6540c089 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 803524766 1250 803523516 803523521
    0x12060b030105090d200303062206090e06070305012d051c1e03050f0d0917090a12151808070b010e01050303031611010f050c0a180b0306010c020103 65
    0x1581039140d4a048180070320101e002440201d281895144c06014450703948030700741000101c840c01400e90f003040000540f64600a00032640c982c0c07000b681003c246904ca24a5012604150000381f4260390b104402d00c181c2c00104459640324030f1510341401190306210048020042482c05003d054807081403440001c03800c81e0121003e4000900f41451628120303242130b1001d600140c05681018911203440c9403c40400c45140302c150305901ca05e85410007486409400d031388030724107205500380e4500c44180020b03001140700c43c0706406001001e89440802b010031580c807405034404e003680700d10342100d080003440d170441c10011a08401c00000309401e502d201c80101403003c183c006c06080000a101d400c2118601e07142c4e043e294a4165281507a880e5000e044d0740388002c0d94140d8500220880c3c1c4488240f041c0001d280581020340042280d400c1080c0d008240c80c425150400c190b0320204007040d10b41d5004a00d1080300d03012000e1114500d140441c44002844064400e41c10004141402004d590094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 803526016 1250 803524766 803524781
    0x1203053c0d020c2d061b09121e0c0109081005060102240f0609060d26041403010c03060501092c0a020307110c011d18090a1b0f1206 58
    0x100c040e140484440402c045001d20050f034845408240d46019078400d810005d82548540c01d0004506600081c0000702101e81d004400c049501c41030a6481c9211200c0c140304a0700c1491921040525030481d40c801e0b0b5050000510031a410403015406c1000058070004802088448003513002440341c64100c0101d00b4010300094102e10500d841c413601500c080509280e910440e480003a12100d91a00c004110362448141c0e1101e278010f096066000120385000019031070551890046030695404940e403071a07a8225074881404018460401180390800b03018812003541d0740e1500b000780909000c00a043d515260003512313003942c0c000142d10800d155400041480074a24038000e00d0074544184050047d50003202c1e1440001c081c610106680b4800142914240c20141c581004801d01c0303000b141040844007800a5000c52144010910040084c04590060700b140014144172805424094020307124a17414003504441c00000b0420010201c0b9104140d80d4400d014010448140c1800030242121 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 803527266 1250 803526016 803526037
    0x2030f0c030415020708010501050303090622031b0608011703071203060b04090c121b050c120310050306090a0809010f05090301060e0a0f0605060f07020a1203053c0d02 74
    0x43c08000003a403078000411208a443da040244860303a200c109164690145000c956004071040c08003c0000c80d8041400421042c0004d0310400035a403a02d40d080003440354401c2000c140a42201841482d6100900c2030260801c412400e0464030183e084960301d20401c40042c10301509801035030360051081c0c1181c8010131241c00615143c80c1c49101d140010a410039080d008079400c075000c603c02c50340a0054071030002c4a40083e61100c40328100540e25640034004d400114041c0149030303115a507500000d0740c090030080c02c031074005504140c02e06251580190018006511401d078010004100000701d800f0140203181c240b0480d940380400b40d82600905c0d161580c103500b04100415088610700c0a03d100b1009400103010051020329071004860240c001d040d0441c9080008100056096008110003031000d4000e141040e50350b00800043c01c180a4120000b0b6400a4007c1e00c2030b408482106500102c16030f02c5000c010800711207e00460808149507c0c0711000c40c000c00140e01c02c1c0c1c180c4005128 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 803528516 1250 803527266 803527289
    0x3070b070c1217010e10090b04090605090d020105180705100c0f2f010c0f0317070305070f0e1c0606090e0c0312090105121306020d0b040c020d02030f0c0304 69
    0x2c82d24000d015030b101006401014a000000010401000d905084c010001a0002c040c00350a004030480505200d05070f031500651180805800603401d441920b100343c2d102c001800703402585400090035070f107028190101914400e08418010b0744003242d80303c200d88007200d5140e640d43c0540800c4c3c0e0140803030b180151051f00a40c81c01024005111091031940f914040308110641001800d500000c40300035699000a07164883c010018190820360320046001781020059056540c400546c040d40071a41800020b0302c8a0034801203603040350307440003080c0d0a400c2440400411201040040c2c8218081144000005d1800c20a100c56544000d016021010342030218503005902c45907a01c8180a030580203208a4000042d4111958241d602c013400513503c503442d040d071448070103460341c038003401c2100c900c84002038500c001500b510080c852611a80b602043d50141c9501704011031302c039a00d010040d034000038042d1304059808021110700c00b031410181a19103000340d0041e4954007554102c0e0781d2501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 803529766 1250 803528516 803528543
    0x4171e03030a05100f0314030c0129060f0d05040f050102041d0a0c02070608071215060815031011041d062d010f111615020f03070b070c 60
    0x1100030004512541104005002540ba10746806503c00d545100c2d41540101d142014400115039080e0361103170b24200001c407422316442045450031181d00100708841100c550001c4002e0a614241e001041c800440d400b5040c40000c5482a04501c2200b07001c142d00c55450001034100300200745800e00c0d0a4228000b191100d845501c903d1443d2605d100187c6560840e00c00101c00805500801100d45059800b80160701d10300340c0c094a10146c0076107841c0601103004052000041c1c68820028004040f107a805501450306902800e0810084c1c14800c810a079204004000d40300001d02c1049500e03903120001e5a05810755080d01c2e01d0080340c20a52682121a2103c0102c440c5068400c3c05100100d40321603480e203140c030850390400d02e20002c08141c0d401c40b10303200c0810740c010580d881030070319581045c04181114608403802d1481001c09006140210030b02030107940024044041d0320303041400108983d45204019070b640e0301802d40000c1c21048000000b9035524410500b08241c142d2101041c6181d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 803531016 1250 803529766 803529823
    0x1f020307170409140610030b01120c08071b11090a140a0207050d110a0816141c0504050913050304030b0405060f1302010e1e06070309030507050907050417 68
    0x150720070f11804060a040c844016aa16402000300c2e0261070020704080e00c0c0c5079820030a034090011500c21905100d03213a121003903942c070309014504010b10726642303640d018584800f018044610b0760b91480c5541068540150000754240c004800810303048584100503a41c00d1305940140902c0c2d402030b07410b294401e00340450b100c415000b03040001c2c4150150350400d00302140c112501c0880038603001103640b000c99071201103181c980c014000c065840803901c0042009460b0a0b52000c150001e824195108003c5004c0700c3d0070b80c80440d810580140345c82c5150500e0b000c0000c0c50303920040d040341d681d03d0518450300108041081100e00450f40028406602e140505201d41c450304201c030b080b9000211080007800e44503c400714040e8070381d4141c59041e640c504ea2000d0000c1d82c0e01045080519840a1000d41c40316074481026185541c40380c0c7e5411074240c1146404c90a0030398a07030005020b414a24144a100c68104058801b5580c4080c1c402000100401d00a8541048414082e42190150100c00360a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 803532266 1250 803531016 803531063
    0xc07090209091e0705070303090c030b090606060301062a120825051204260904060807063029010c02100c060605151308010b1f020307 59
    0x40700c904071107054155a0312410528600980280c0719110200c16001841039030103100540f4190b4040d18000900081c9a501c584041007160426200d034071428080040031181080360b2588400143c40702401c41d4940b4802401200d1040e400d244460700d4172401420908142c0300250710180c01141c100c000000200c400f401100c010b82c1e4500020280020307071800030b107401c006001603000680d0703998588018410a1250010041c00441d207540f8110500c804080c00b258203204080c10760760b01e480e903c030303540410001119040e901c100030070f82200c01c0802950b80c120300844246400020010b03c4101c000c41018891800780301060202031a09044404111508032190051340802c3d40c0c1030b03031214400005442c10050014000d42c08000807030045403482c8207004d103641e4184503003404116107854900140304402014403010101c0b0000c03a881802a440c41d020100418610000b005488403140c081108440c000324401041c04501d041800c00c03500c07c004545505402c11054004c01c6403a0700920071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 803533516 1250 803532266 803532277
    0x1113030b01150c020312090613030302100b0f030712030203120a06050a05180103080f090409050109021914041505041b031a0a0e0c0f0708031f05061209030c070902 72
    0x100100121070209802100c1508203144c000f80107000c0003124041180f80383d0f00142c030b040e41100c02405050340d1410b640c60544051403003a00a0f100c20030646070210b040710313890b15003507110381c040a04802e0030b500c0214501042d02c50a80c1032040c0d000f40303810180d145101c0c0d64880c2e09800040020418100c0e810382c01141641c004940d801006540c580400030045180000002c103002c3d88001000028602d0004001c0600c03112000f505050600703000404aa41120f020740e096511040e484085283c01e0482c01c004a84007002c42c071005003091001380a5a01104640b0b018580c1e07100c00316030301000c1c81c0c41b10b8005c00c0c0052080c08044a13000b03403040c113101c00140304004241044110240708451500240c10720340050700303e440b154500003550391250009488041c4a40c0300f004001d840840c0e9000800b1514042c1030143e03902e05200107901540021031a80c10780b0208400300510947d03591408680c0105e103803043c030751099152004404d041d407080d1032100f90240302e8050005580c40c025009001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 803534766 1250 803533516 803533529
    0x90601050112050408120619270203010b040306020f0d06060c03031b0221070b101e050904080c0c030708010e010e0606011e02010b130605031b0609041113030b01 71
    0x41e22002002580001d030f030001d5030000d080c0101070140b80e00c9200303602e2190790f01140041201400300380c8000380c4105200c042d002410382c4141c10f5800038010041c0444000462922031045155602d0720410404070b01403030000400c00ca4000030250480072020094400c2489c070580108000d650742c0340090803101d1812070840110b8200580c0810070003190a0111807100c154020301480d41c0041681c41e40880850800c40e01c1f048140310b010003041c13072182450301c1020240380740401e09003081d49087c1d1210003803c0014031070080c0c1c0c605201d10f403600c0c001d8070b40143c0e202d400d082e150811442e6460800e61000102501403048620000e20b45805400c14800010b41c203000300549812040c0c12500d841c41190a180898030403804c0109400f0303041402c0d80800d00520001611580e42000508480e1010007c800c030151078520500c41441d042c40f0701003030f042113414403031820013088005ca074590080400d0148255560f4405851100120f01210680e150704001c040310f10380c072440c1904207075101f8002c2d603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 803536016 1250 803534766 803534777
    0x4091404050c0d020a05060c070e010b0417160311040b100e1806030d2a060b181302090717041415040506040b0613020c06010302190b1b01090b0906010501 68
    0x2411181050b100d02018150003428030f4603920304120507c40c09600c100070fa083c1622806000181c1c0f1040700258034003901501d41030a544903e803150082d2060b0b0f0307104035655550068903c040000085030055411290f04c0040300d60f11459176000a0b0041420348481d0f508aa84c1703908050380950f000c1a1440090030499103030025a43c4050003294600080760f03030a4140d40510b0321010300034040c280604140c000d003514001480802d2040c4ac80e604504581201c3c655210a00c8404505d400d034814000c401c90070300046410b2514141c12846040b01d804044c0c001d5500d500426051849011401a04920111003100d6800c081c585241c0c40006550582d9150040c005c03224114043c03a10554007840e0030400602440e110303a2180144c06401400c03c1341e100d141c0c50964104804140041c11a0024040140440c1d41c910300600c0540c0811640d5008521055070003440008951015a13480c2c1c11607080c00800c550144194600400c0d05000c0034026070300e01c104008a41000240080c1a9070082e07907030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 803537266 1250 803536016 803536033
    0x41a0f0d15080102070b0408090f0a17070608090a110a080a0c030c0b0a020607030b01031b030c1101020f07151d0a050f1f1e050a060501021603030807140409140405 72
    0x81c2d80c02c0b8012502d0013000740202d14081070118a24501505410200030500b4210b0100c04001a151041c4c0d94000240340d5030f00d4045808605040c000f1400425032400c2c106031601d0030b1034141d03440310803041005140300360031040c50f03031207444003001d00c4c0c041c20b50b5808644525040e4108605950100c0c441102c41e155032500105030083c0d44403d4440d6004aa001840c003511480b40507409050321000c10341c101541c0305510411020101d048403500d0346a601d001424001c8000020300d41034000314a076001d0b80c0100600c2044032044001c5070b00036a00600c80e00b61764514420380c240a429400110030034101c00301d021a0841c40045801c0d803e880c801c2c812252244180328040e0384529030703681c0d044c06d04c400364a1140c404401e20740040180c4508030034110100f1342010000380844006883c00c0c18070968591040c40306503010041c0307191100c01240340508542c50360354001e03c0c1d010b00030103080400940c0310582c80034000010030340303000c0d000c030000c1403204040082c00600800000c46d4140c031544680d866 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 803538516 1250 803537266 803537279
    0x21050106050f3105011401030509120d150509040602120f06060711180f010602070509101e080a030302031009050402030c01110f0106080a0302120c03041a0f0d15 71
    0xb031111600c0c40a800d483e44030700c814460280d18102440c00301d050300300d00f602020701e4001620550703000e4a014000f03102642084070005003202c2004100100940c04803d52280d81c49000081d41c204107191040403074181c1160391031042ea0310f01a40195000609401030000b000402d40240140c03070b42c0700300da848141d40c400001d1801c06200baa40b40360040001c0240d98040350a03560b403000c0707da07400f80410080c285801c0740c4405011003101c6030b000028a820040c80320aa05110a0008080c100c0303005126050086078501102e2030391040d40300c070702d42d8400100039040c0780c030307000400404141043c0d4000020030b00b0040c0296208460105040f500c051001c210030240380305490240d60050014001ca803851001510a0341c03926169420314403440d402207a040009000340c1004e030203080040c1130401da01d464042c0c038040125620401580081c4580c0703134214400020345048450254400542080304080c6043c980300d01c50500d0400000065480e24024070340d0880000c82050407204c248566841c40c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 803539766 1250 803538516 803538529
    0x1403131a0402012d14090616021003090b220b09011418030910180906030c06050f0313021f0302030708100501050a081518040501050c1201030209040c2105010605 71
    0x1301c0c503046451015411000c50b072060000d02400c08011504618004541000a1a43d0032515168020fa0007200c203400071410003011888250485050902082403940d440605035080244203001030f03c180b19820010440403002c42c2c14040e041207505c03800d801e00010301400fa02c840302030329040108803008601801165410f002410408070701860034640c8070747c01c210350285083c0180e000c10034000300074a0078102c40c00405008180b08031f40050001d01c0c61601c5c0e120400c0300e5104105114080c070031740b010120b141e000c803030f40141440c1030503c0a10880c400164000050907204004050200340300d1031482d0194002c501030140e5071550401076503110400c0e104183c60780110703400900305110815181d400340c020181c006940c0050001c8182c40040402c5034011141e002c506822564018041409820300c10540c00106803080c041c54140d4044c510131141030306201c002d003c0e002400000301840a0b43c0c50301405003580c082d6a2030090341804240048080604041e61307194030b421400111480d080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 803541016 1250 803539766 803539817
    0x209190516120e070b0301080109020f0301020a0c080708120a0603050105160522080d05040e0c040320062205030709061805180709050a0b0301020a1403131a040201 72
    0x80e41c0d001036507990b0100c004080c0c81c100c030640c1c0741403040020100b518480d0f040994080c16401000190034420350041160180110500c41d00907417040240c0c0000540c09942000f09940102d44195900d4881c60103070046e2140e040319003000c41c21807003840524402900140f007100e000e40f000340031036201c2d4041c0382012002d0380011400b04004201f0044410482c021010952009860440d143c03640c0714172290408000105000c00200e00181c203208070806516903e402031107901c00c06041508640d180400c01d030f2a80b07200d000c83c021903881c40c0b8041c0e40d10070443d1f02440c54164100e18100301400900418040d030b00505119029010b8085128101d07807240758115404510700e03a4880b00b1000360980241400303003910102d80450102d56000400400c190340c007c2c180d07c5c9000915150184840d001ca88110000c1d0b4440d0b4010030040d4005984011145010814100e1882e40c076191a1800b441000b50f18100403c040d0103100101401c510440a41c0d1145000b80c13540e0207180009540c3d0036601c84030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 803542266 1250 803541016 803541061
    0xf050601020c1e0109031a09070602030f040b1c140a0e1207110a05030a12030609020a0e130e010e060f0a020307021c0c062406020601080705040f020702091905 70
    0x600401c030b5403e42c01241621003e88117040643d219034030b076210b0b20b008206070300303a80d144500604240a6a12400c0000342c0060240c0e1000c2d508150507110003070b003030b0f02c60703071050300f07020341003c248101010203c040c0e8a00c5501c2e4014100305139041c0800422100c00111800103c845c5001512002100c020601a1211a1400c005480d00125545202051850540c601d4200940c1d0b013000c1801c0c0c50420100c02414011a1081d44183c500b83c4002c0c1941c06a030001c40807580140304041009811191144000c101154150361440f81203800500815030078101c40f140c3d60030400060080c0b01c1c04900203001d03a4003081c9100003940c40c10900e9050303100c1039504500681c42404180400e0800904813145d002c00c031300d4104030310804c5071a25030545a440501d01d481e8441224240e00d074030314030072100d8000c111500181185614020a1685661451003120301407500c6402c02d458660f801e134111421a42d00428070049414a85400560215100102000c0c0342c902030108507040300d00c075086c0d502180c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 803543516 1250 803542266 803542279
    0x30d020115050909240a180312020c1f06030309050406050a0636060806010311161e030512010b0c07050609010210090b0604060605042411010204090f050601020c 71
    0x41c2c0b90510a48410043c0052524012203c007035008411400800940350154160b0700014202060b02104441703540f1102c4040105140c0c0030400250060401c1c545030b0723160030f401070715900b8200540d42803200142105282c5240c0c0c5060101c0e00a8a0b480b140543e4000d81d01c201e03c0d0b80c0c03220240b100301e4a03d030051580c4001030090800406100e84100000301a28441008608011b640003074100729804d1031002c5c42132410401404856030003440c0c1a4460b200b4a414010351607000e0034500c0d00d208102800e41c814031000300304010300a4040d00801c05000c440703485020f400b202d082c001e2107a0000070514000e05c003079500004001e5034070020f032131040e0807a00160482c10b2500c0c04000103a070001c485a03040d800b41101a01c205440d510075039218502030035101440c0d01e0318808110442e605a00020b0074404140010300c010124086501039240407440600422540b580342aa2010003040d0f52050543c00090089401031b4260041100007111210038402d9403a140c005a032900c0302d0300e00d4a0341044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 803544766 1250 803543516 803543519
    0x130203071709120702032a090601031e2003040b090124050d030c0f0f020102011821200c03010c090e0a09140a0b04021810060309050316030c02030d020115 68
    0x200c02d04014444d0a200030220b5103003a0707902484582d200d5560012000f1007490291040d02414001d80740d070741c0300e40d00740303000c000300f01000c4941031810304004504140e066840c0140d01501c0200044070300110600071044e6101e1501b4985070407038803400c48807c2d40c103500348041c40348921545248a000c144420450340b90441c105014840b01404c50b8030180c0c100003010500c03401007000d91000652641c0600c141da0303c0106103000190075146050140503509041c0451000030500003030015808201d94a21030f00c65050307903603084401c60004041ca02510303004441380c480548001840758007581041d80203104c000c3c130442c01660044464862218103948100014a00304100d0b8096114544075092400071480c1107170f0b8492030310700461021250000450f05101c113614104200301d1840d424003001484624002d0703140d01a015013441150f0626480302c10703104c00c000040c020744510a4002c0c0000f030b412005801c0062500c80400f01c243d01a000b100303d0b07a11014418004c0098541000303a8110b600c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 803546016 1250 803544766 803544793
    0xd150305060403050a0c0204090303020a02070b09130506040b030d0c0507050406030b0f0a0f110a030b0607050a080f09041505100e09130302010609020406050c1216060902030c130203071709 83
    0x1580104c1c05c1c6000c0040344a400740040c2d80714460350b010503009030750040c1c9921094002a00d01146608a1442c03c20140024000ca48d10700d2206129002c10840c0810b00b9290318000c24068458004981da25005480742014090b030700026121945010701c0c11120441d036640140804c445a5020246c11201d100340021304101c0400c0005410110310400001d050300780c21180ca08940c1418180c01000c034001030317559a80350380b5020343c1c0070201040302c000e03141403103039543c940d036498a49100521551012440c100a800c0c0301c3c081e9055043c01130700510000a84032042c114401d41400f455206980000404210034401e120808185c2c101800b1610640c030b445100c50b0102500420031001c564881c0004540140c09001800040c9860b446d01522040181441818410301ca0150306110009001043c56100b038505d0450b00310f900014001105026070020a090801441000d0b8011a0030400c81d82401c10944c0210b104d0102503680d440903521070f002f0300207050004d03915101c0b1917200168040c1207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 803547266 1250 803546016 803546027
    0x201090b070804063605030c1509090601091707030210020a0f08031f08011d0a0c031704170c0a051905060f090913061a0d0b071110020d150305060403 66
    0x254240107a071300da04040c81e90182c50241c1321240c89040603118940c820884c0e81070410103412322000c12110012002205002c61f1198003998061500c110350b600081988ad0b4010481c44001d08220982943c0300c81c1016810340da11030051004038000e00c419010a440307a440031601e692481c0e403001c00008100d01c0d40c6c4410030107400242011078070302d482d2032004803c0314130301003000c005040000001c10100503119401207924070300a2405030035009400407100240c640d5228000362640856021000d648245880700b040c02a42c00c078000001c0c400080e0ba60113000040c840f103080c802100c030340d50f0464440043c0b014030000381000c1c990725100e1907824480d500e04400641280c5d110224454104845c030400903030f25000603601041440e0300010b40100740440c82c003039503a0100c0d5800e000305441030031a01080305880c070300030050109641e01c070200f0740842c86661390b214110101030071240d0784d90800c440d210003580f003141c0d00702e483c41c078103d18900340c0e0803600521801c4a801802402983d038035510151103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 803548516 1250 803547266 803547287
    0x8030604050a0e03160b0a020f040e0a090f0515100b0d050a0b03190614060f01110f100e070503070528050a030f1e020f100c0605040f0201090b07080406 67
    0x1000c03600d50340d040050300030030400340031100305c0741000490f020b1031030400c07010b06a000740030100c1540c0100181168030480e00304071012902c0c4c80c0c9000119545d0788462400a01c5035440017400b8810101c070741800c2c0100000c0541c0c00c07086601018806848201003d220f20701d03503100c2c1d002100c0c3c05000510b00011598071450b80007a56520108800c40c00314006402c140300c10300c080c41d05030b400c12060b6060000500ca4034550250141e6103580c00d0a001d8000303007100d840e0601960411800003000c60401105100039449088403604842c2e12501030101e21002d010100f07203180c0760b4410042d0020b0103180008003241201d501403d500d0040c1c1e010034105160144a00404007404d101d0380f40003407a500c0f0321160b40003c50161114860107407551a1404540c1072414105400e07d20901c1d03290056074402400070b440280484112906403010301d01556072541c4a480a080c440c5031400304001e006c119807805071414800d9072026501a02c0b50312017000e502440c140540881c106000c02c0c400305005095010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 803549766 1250 803548516 803548531
    0xb01090627030203030307031b0305010644060f2209140307030206060a090507080c030709080102030c25030512180a350d020f1e0403030212070803060405 68
    0x1c010603129008a891507000382c40010009903540141240000380500124185a00385014802c0c0e500d44000289103400c80c543d10340848403a06840341424107400c8040300301160030306418010601405603038400900840f0564010500051001100d1030001920304d01250304240c0e0b04054200000602c0c01441004012150040e4900b1a90001002040a402c074035200f94001e0480d454100c0600111000c07560000d0041c90808041c80303c9280c0000c0313030907030090389044d04a40b2680ca036002151080c046a2050071694400000d1001a070314407002030040c46211015490a82d2211030b0802c440e03030740400e0280000d01d0511142d074110304400e501d141c00c40420a08501d612900c090620300b005480501122038000704101891a160f00070700d00080740010000052440c1d1002902d0101752143d07020014440e940010040180b0f010b00c01580c0d4284105a2a4031083e15030b0100b04009034041c0c04150003500c035400384401c00c034002c2001c860003103500160840c216200d890600c4090a0302501e030340e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 803551016 1250 803549766 803549837
    0x1c2c06070206040e070912030f03090305130e09010c05160f0312062c010b070b091504051f0c12020a0201092915010e0d0f05060a0b040b010906 63
    0x120302581d1101c010308050044200d1200150034803400207025642c0301e91002d1b101401c0c03d4811000710390014002229200705003000300d03085580d0f24044407184240c031044030800e107141c40d021910a807982a1a0311a200da00004c1160228681c005e0b2868003904404565840f00c01615000044400030784000041c4281000202c201d400091042901d986401800304501c82d41c8060086681010185181c1c41a528035003200b5414940e07401c8140c413030104090001e90503880401c00e4120704101c0c402c0c0c4500a04c00440141c101761a0064913422010031002a10040581d017203c0c004041c0300d900c5002002e80c5922291440951074807001c5c3d0441c07081d010655507140c0c944000304406008010011002d0040c034030021038021003458040c5000b800510900740036986890f8240d0300220000d00a1900311443e11203c2c0e5180752840314203841400040c4240241024000d201181e50850041e55a00700e40520180b144240110380500d135a100d51070014019041c0803c440c1107000c0c41c0c010210041e16a03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 803552266 1250 803551016 803551027
    0x10062007182309011d0c010311091507020a0f0f1205010e0a05070501090914130c030807120906020c181902040b0304060507050f0712110d021c2c06 65
    0x1000125000c0442e05103502d80c88004206100c071007031040f150700c5181c1010541c11300b40162a119a00d50b14607103014180340c1d803a07888030400c250385810b6403180d02004007210312941c10b900124590381c10114040740644000100400d8010f10307032120206441c680c092404d034032481c1c0014468190340a82e4203480c0ba540c1e4840001031a24140482c1c81258001c800030a2040d290400041c04424117522a00416141040d20481c0311808071041d80c0202c1f40190000040d03c0b02e04007010030703010307681c4020403010002645204114030700c0440c2d903209800b900d40461182c2c0d180d00c16601c0b5000c481c00e1591000c00083e03031400100c80e0381642c41e0041c0310b00094400088030020360000326413140e040300c1c14498002c02080108210b81c0101503000a45103852410b110078408215031501031800d00800e580c61415501c20114030410348420440f10010403a00380c3c0160710b1003e9150900c01c4810410b104c14402c0ca6180c00d80220315607002480d102190101c140700302c410b01d118001040c003070360b0b074009010400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 803553516 1250 803552266 803552291
    0x6060108070306080a030908061f090b0303041203030509060c0403032708030f070606050609030709110708030a15140a230405070f02010e01141504060305061006200718 74
    0x3242c445c252281d02c403414481d08000c0c1091a0083c01004002160070304440d0744800101103c2550898800c40804070b018001100000d0031030040360822401041100e2558080c10351580109000343e03002425516182ca9584000c080c0b4885c2e4000540403a030544007400d4062a041c695134021041c00300d91007002c2c0d850342c10040c2141d001e0b00400c100443c1c003117200018040e6500c12a00201402c41e034483c680703001c0101180e1605203030b100d8040499601c030038060810850400f04e500d040c2d0300084142d900e14207402c034807000b4068264039003441d03002c101020507410a0841c0c08843c0c040014980030101c1d141c24421310520524480c0d0702108441540c0501580c3c8683c01042c1c01400c8a8550306018a50014000e08607507140140e076a20ba030401901c45450111341080d135030410451a005242c20350017001040c06004a50300091041c4524400c01180600c3d0300041010798906544808440b04024070448840641c528a403c0d550407143c0304011b090302d000d8496800028096020030070001c0180c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 803554766 1250 803553516 803553523
    0x10b010e01180e0903070204050f04032f06070507050c040510090f0b040c030506100f05071707050a080a02150c1204021516022e030506010309080c0a0b13050606010807030608 77
    0x42d0541e0703085d40701007090750452030140070f840d40c0001c040315003600301c5c581620010640c1c00c0b42035051500088007a503101c2c0d00403180f1242802c511140c802c590031800c0802c0001d015500a0209450900610141080c00e00d0a400b1b0b0030301032515000d00d442c80170300f0407071488018224103900c040c1017681e44843c2c3c4010b80310740c000c40305007031002d860009503481d12400707001c000104911508100510414462101030700b20050b56010340e000098004009020862101c1c10300c102c55002d07003948140d403210420089654014400150a0303400c1e1400101e504401180305a000d4a5048540d20203003c207000c204a20202c0c96409400100602e0030691000c6050078994003040405408500b103400300f41c01d60034400324403450340c04031340e81001030308002c002d41111403080041b02d00304064640307011400d2030b0b1098201010958104564503500d03100d50250b5030b83c88001c0101141c00704121400101054801c001d44c5462a8020014022590700e40004540520008220009140e07988202058144041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 803556016 1250 803554766 803554771
    0xf1107050904060f050603030301060804030c060e1009050709060501210b12030a020d0c0210030b0102030c0322050f011205130b0403021518120304020604090213090c02010b010e01180e 81
    0x1010f001441c0d00c007880d01c02017034400060002d8000da1040004110750b0b980032000710b030b2260300751400b81d201000c2c1e403400c40007801461f503100b111449142c64107942603c0b1039014825451288085402003961180280300743d854521460340403840800003101120030040c0c6000e6080300e14600050b85070402c90004070366106100c81803100360710115001c41b407550104503407540e82455081030340113400207a0000e00307a01e080e66110300800d03440e6122103030300364003c1050780c0110800206403600d0301c1000c4640d036510000a80380030001d0410740400a0141460015441c00c0c51040c5d60300c2d41b030a801003840c0d2024120142c00d0a0001d1b80145005003c03400040c010342c0203504ca50f010b05400c81068441e0403800c60080c080c50b80000c500001800e2450700011070a8207100c8411040d500c9940b50f000040c5e42e8011030307109412041c00098000011000c20710b403403080e9056004c0402021503042803ca00700d81340120214085203580c880001c01c0d40c0982e036140106009600001d040641740c81c10070000720020f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 803557266 1250 803556016 803556023
    0xd021b01240f050f0f0102010b13090c0f0803031b09030d080a051b041811040603140906150616020d06020a2c0114120c030f160f1107050904 62
    0x4004007400440d086080020090a801070200542401c0000042410002c01e8103240303d40e0012501c04c000364000c0d0000e5050240040c44000d0b41c0c0c1c612060603010b80a54601243c41c104524004640c1c06020203000090f580c000740118119901e55045803a00d48161140d180b1410341840a0909590304100500154141d41e8a0280908050000c01d00703460000d44031004081218500b0082110400d060324102c2d04050180400420360044440060007180103203451884d00040204e00309030550440f03c8143c0402200e0303022071780c500e004c00c3d40f130b01030a0b1100070450408440b0301d503031480c002015042020f000c00c075451644501d07600250000c100460216030300b03030300419903139282030300010385c186400301030032283c8154081e5000e000e0540e80c00c084a01e0501c41040c60948905001c03100b81d802c0c100700f1204074041c505280c00065500e8008850301d01804004900240800740807107808852020039450b00c805503841d6100a48420b956210401030511441c107002070140e40d500000c9029901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 803558516 1250 803557266 803557301
    0xf07020d03090b071a160f081504060f0617090c0d0206090405090607030e03040b030c0703110f0a02030c101b020321070203010f020301030b01030f1502040b090a090c02030d021b01 79
    0x848800c0c050880c4001c06e0040f44002c445080d550701500714000c0601c0b505180f411401c503581d07d980b440c003010b032050303c1960043c1c54030801241149201c121030050700c40580711341c0c3d07a8941c0007800c0410b9100840b002c4c902608820442c078481d040c401204000e9902c000e02c2e50b420540786a020404440045655450940c003c10a000f0300740e405100303c00400c1c2c002c1d8041c40c9401c0c00d1012100291101800390a40898001816018103109242d80c504030103101040c0e0304165010340c040c0d0303943c4d0f20404040e40700c3d0150b01c07010401450300800e03111500311540c45001e0fa085803014104401001c001d000e91b058051141440c83e031a10f00c0505900e00030000d8402074035030301240141402c4514103480c07480114410401400403402d45400b00b411294020408009219580b40950700030b030b005502c80c06032a0020a021a050340100d02a01111405440030090560340300c29402c1075400d000707041e0b00560010480c5103121111900100108420701c1c4104040c111a00d52640c2140d11072624241c9001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 803559766 1250 803558516 803558543
    0x7170307080603030306030d051b0a05030703081f03030c060e161409040c050d080915220506030c160209010b0a02070602061603020c010902131a060f07020d03090b07 73
    0x54100140716040202980118194607084020903075440720354280805005011890305280c0000c00b10700041401c5030300544071050141d2030001e55079000454218082036a0700009981c0d08a064095071040808103180020189580c0b0140c602d0402e001060707802c1615080c0c2d0000c00b101c00c01110107110030034014034046a00d8000c0407551489040d2025100342008010710002c5125501550141e03a0304950210ba0f883e001d181c11809407195a6406411480311b0000441c0f8440c003001810f500511040040d22829048441055000755400f816a00c118140041000740d903100003d0100c0070404410340b100f20304035070001207040300c09900100d803901000800c1c1c00c40d5941817081d04000c1c040340c0014145814140a02c3c017000c03080b0581030707081642c04910400c1c00f6109411031850182c01070500d50b2800f1200f040315010740a441030030042111624030701d1046080080c119100380c1c0c8402d581c5814070403030b1390030402000103038101601080420440855004540b000409003d40314440a107041c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 803561016 1250 803559766 803559781
    0x2a12010b03072015070c0b090c012a0602090f030f01020c01180b063007050a0b0f2a0f0d0207090608190303020c01090302010209040f0603020a1505071703 68
    0x842004203003264a50100403100105200000d8903132060306100c100089590750000c04a5988650120180c581080705081c00100240820318912205080c0c1c1e032049442603001d05030216101d110902049036440076a001c010422070f501401005500401510703250a0140000e40782003038261038081c031654001554030580c40c0074810703035100c0004014080503040190b00c5100160a004000c42d00904652000c400380300201c031100d002401d03090f6441c0c4003803101f61301529034078040d90103801d000c2d541091010910300302107400d907604240300c02c00b0245401c0103040c48195200c50354168103040016625503003040030040c03064803083c681e582e004203041014549e0003072a05520b41d0215064910340034061003440b9000c00c0e50001d08a01c003000207484030342440c08038024401d044011046511380a038040805a06400901107580100c07020b2003000030441c3c0c4c0c0411242c070341c44000c1d4001e981c180108041801c0d01e0100180c041c4e03070709001d401c0407059200c400161b40341280c81924928008100b15a8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 803562266 1250 803561016 803561027
    0x19090806130203030f03090c09011e0e09030406120204050d0f0c050906090c1804150617130f060608031c050a0903080606091207030311060c032a12010b0307 69
    0x825480d10800c0001a81c0c0200741c42c1d10445c0648041079500000040317100000b040b20503c884ca001e00f00054a603034841118001c082040110049a08100f03c0058001c4004804500840307200000d5031419280c000155240b0301400d5408241680078003001685603901104007407940d0089802c2040d545003403420000c4004240c00c810300c288900000e0003510788400c110140d02c00f80a510300c0c3d82d0750140790301851107401184c8180d50700c00d04051420318101340002d07201c000c403901030b10348d4484100c0003103000b4000348048452041c0a4181614a800b00340c204584034921809030400151954440c8005411684104140b01c1d10001c110208804401c103481407550004030760004006060751640c0041480001400c45842101d02046511803551680080d000100c400b0044a83c403d07035038a80601a107694030b10084840c010000040d181c4c0c0c01d07007402c413841610500303d01c0074580c00c0190541800c84804030001102070051001d41e400d5407010072264040c205c02032a1760784034509064010321 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 803563516 1250 803562266 803562271
    0x10e030a0909020c03030a05041b06020c01031107020d02010522270506030a24050f0a0b0901060537121112180f0a080403121b031419090806 62
    0x1901d0720400013080c3d501000710130340c0c0e00038a1800e808a074980f03803170800e120300502404203d200d440c02c0b444002051500020f504a9000c0284c80600c510107190207c41c4650181e0310010b504866202d401400540c41a0000c050080341205035109210030f00440c14003400d40342d000b0414282c016581e003043e00c9040208000c9100c603201080c0002d28081010030340707400001400912aa6441481c0c0c440281c1d80c00a8040b4854000c40400480c541054103881440068400d008524a8110303d00e801d03041c050354003030507590103413145403800d20800700c4192601800361000120400d003402d1504503620350100025196000d68855480c408480c02a100315805441020407000d0100440f07143d800c0c40041c8258407006501072180b0900101d90500d06040744045c5450050040081c41010000f45901400660340100034260007126591800d4400b81c9222071141e040007280b130b0101c40024442e003410f41900860b03500e42806e103d0309022403002e50305943d800d40c0c0803c005503414400440c04000160b13 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 803564766 1250 803563516 803563529
    0x30c060212030424060b2b0e07060509060d1407110105010f12020f03030f0304121419020a122606010f050a170f180a05061f0305010e030a09 62
    0x185141070650703400015084c03101402c1c00700480200041088a62940601e0081c80c00d003031503e564010400300f25080d510b4002161f041b940e1307102c00f00c2d00c2c0000c0b140f081607002041140140305140c240a420744440d0040c81c840d5138018400c10214000d40514010150f1300c4402d140b0481c030508000c207000c4d00320008031441c541260324241c010000644c81040c42c808036490740b101002125998000b01d074030b00d0f268542a9400d48000606071901c001c1540c003c610803401114030f18012242c00070b007199509210024051900028424100342e8250200e80310340c030385054011940d11203001da84e92000790703d9a480702e60105122450508201c03c40101c1c003041c040d501c504480c21450324070000303031050448455040401901140412070316000e000d0b09a850800c10408800030301d4000401841002c0848500100e04091403080c2c0d09140001100d02c01c840d03115000d03001a075545c02c110940402440d6416900e2000501d001010807000c0c46031140161055016585e211441c0b070010b000c0102c10351280 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 803566016 1250 803564766 803564803
    0xe010603080406080f0f010b0c031b0d02100218040b030c130f0605010908070e070203040e01030f0c051801180228080f0f0c0a030b060a09050a12050a11061201030c0602 74
    0x40502c4040d6913006e41500c0c85c1c4407005440c0c02e06049590b140d805041520582c070000d080f2114451301000440e03403050b400b16400c441c0300001e02d0304004d099003d00d64032a00c1c118ed00a01f41609481c20b50448010464040c08450080c01c1c4200006c1805407a10589030780580e03250130700c0300506090b000300000b5100c207081018000d440d004003541d17204c00a2203031400f03104151001c140118070034421100241102540c22006584904041400004d0310070100c42c5c01d01c10300000180c90528422007141d0036403c903414011a07182000c082c1d08040901107100801e070742040034142440095415010002118421104030603940130082d2091a000c0c1404000e440920704004c03925041d041d203568041003c08203591154034003c01600030300111800158002e0b0041240343c1c1055102c200107040f10801c5495140c60703956414114180000e180707014201d034200884c0100482c0c08801280c000c010701801c1180380410384400c0d990004003e80045407000444442085000d604004504480c6c00510340c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 803567266 1250 803566016 803566021
    0xb040201091703030103120e0306090d09090506031020040e060405010806010b0a0309020d0f050d0905090123190b12060303030c09010806180a0b01230702130e010603080406080f 78
    0x8030750fa80c00148002407001450042905031184149140215018068110b45160401c0e081854517002100405000900e040c040040c04843d140103040c0140b0002e4054102c40a184190b20080c044540d00403164440c806010000700711070303a000708005e0400e030400f41c025003481410001609d0701a030089400740d00010050010380011021144841c4040c1800a02200c09102203202d004203c000507001d135940a032044207110700892949240c0d01e40350745803c0026103c00400075620700130b0180d0342603c16581e0700c0700080090698942a0b0142c020040f00900c0c03040f50071006082d06170341003180c00300c0d00401c0000520f000c3e29280d540011007200514103507d0182407040c0180174020384c41d070410111102040e65500c0e1040801c0000f40c040c24029101d00d0100080c00c0039000f48100e01c2d000404200121044240308042d400e4881030000042d450640c050702000f0306c088040c01035180060303a50300300e0340b900ba209100d80c400441c410300e6140e40b1742c0c0c900f0602900c0388400030110030086140004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 803568516 1250 803567266 803567309
    0x30510090503091c02090106210903090603020c010213030503040608010605040e36011505030601050a0b0f220509060d05060403110a050a140712030905010c030309020d0b04020109 79
    0x1582c4030900140d03400b0135004080c4200703008411402c0c1000c0c0d000300041d0000700d20a170b40041b11180c4400610150008000e00c0386210007282d05015020300002c0525038244500c521a800401403121700a00160034070300603040300003060b21141e1082f00c0c43c0d031001508014050f0000540e50041402d410700f941018a055000b0b40700e004000c11a05403074141a0f01c4400000944580320348224203417000c4941c0c01c0200014900070a62040f00c01034a510508001840d40382c000f4a05061b41c0d030291002654505d81143c0100a40001c0c0c4040c01051b13042c04040c044202da4003681c84000101f00d05100c0386484c0c5420300880e00d101030540d50050360103540040100303500042140e0800e80c50324040c003d14040c0c1200c58140184d00b00014412701030200c218061000440c3c0300711442083c1c0e42900e00041e41c07104040c0521640440040200307411200401440d8040d1141c400c03164042c1c200031610f03c00d50f0340001c0201c007140008070f4034500304402307001c00e40d43d0200c80e00e0041d000800c042c03004c0803071144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 803569766 1250 803568516 803568523
    0x40e030f0901051e070c03050c310e030c0d030b0f0607020f0a090f0f0b010503070c0605061302030f070305100815220c0602010515100e12160305100905 67
    0x501d2a052010014802074409070f8030302d020041da61041e0348130742c0321000c1c1d00d01440301e482c0500c42a5600e1203041d819082618002201c2803100380c0d005505040c000d0542c5412010303290100040c520b0640d00d24803064848010b000411060300000080c001040c0d101c00c005d0100c40c4281ea0f4107018159a40d0302c841c0e01c0d200d090884546540440d404141c0040d40b0b00050b030140c120f41c0160701c50078200f03842d040981095412520a100c0f03010018441c10040c0d90044510380000c851040c0028052036051011801a0740060340201010740000c40410a02010f007040ea070040ea01c50490310b1014041220b6590300d441038a400284075004408030515000c8019560003804041c00210011031000c03521030a80841031400060a248503080003031000c0c24085c5c40e4454511614000d9400e0100160f045408450107405480c4001c001200b004203000040f40c41074900610103070000d01222048002003001c0100185000c01381281c441994203616001d402e0034912400d03c0b540b41c0c1090140c1c0001400030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 803571016 1250 803569766 803569777
    0xb010302060705010608011d0c03010506060316090306090b0604231f0302030f0f060703091a06030307050a06050105010f170619030b1009050c0901020703021210050f0105040e030f 79
    0x110369964a40050f400c11500406213544483c003658605000d00c400800030802101030008000261080750f0302c17050900d403d03a00100c40b11540701000704001a90342200340710307612a805551510b101d01c15200e5451004803459410b00740c4035802550100102450240107282c41c503080a5a003000354407203c9079503c82828060310020044020004015100c030300c505441005540007011181020100281144c449a400c1120100d601608002440d214001c0c02001c80c1950302424070607c0070036092004080b0071016184541c0340c0010081880850000c1000d507001c24018000003a05500d010b00140c035010b0041203003c24801080f8501400001e5203000a03880481503a0b80d207040e81400000f01d10b05441d542005164412007014042540c82d9844900b0640301d0001041040d0b84803e0120381103070040443c0b41d801644404000d00060400003140900e00c40315404484808658000f00004c0e10310440b500020011007078010003052038070f4000d03401040000c2c0095450009003188842a601c50f5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 803572266 1250 803571016 803571019
    0x40b0a09020d23071d06010203040b0f180d14010e0a080409050618010f140a0305030d0b040e07090e0616080103030c05210d0c0519030504060b03030f1b01090b010302 73
    0x180c5500b6240101d5140c40c0700c584800301c0f010fa540c41034482d121426107000e40440440001d141000080495000004480659025186560414a0300780900c03900740d000f03a8000001c0941c1403484a42c075200c0441e041c1806100b0303140c0041c0f40e40e11200040c2101c0000c06c0700111940005500804034900000b1038003529260b00c00421541d6920300800c140c0b0700c0c0110107031406040c0100000e07182c8140200442950f02c08902c031103400c040881002000c6100d400058080d0304100200074a0700350795804100201c5001d80302141c3d80740400303c02e906100f036603030042c1c070000d071580030750101c0250074460203611581220f0310b0b0040d103c034a0401005010305010081c140691030b11a00d042c402c0030090512021799030b03003101c0c0030002c0d4440346160640040d80e021030034a0402140900181c01760342030b03030a46808001800004c07219084110302800001e0403c1e1030f11a07030780c0c4c0c481180380c034148002d14019550b10356459451921041b088802481807846654592500261900044003500e109044a80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 803573516 1250 803572266 803572283
    0x50712090f1205010204030b040b15060301050901090b010c05011d0111041a361011030a0e0d0c03060b0109091a1201020d0e0d020f060f01090c050f0f03040b0a09020d 73
    0x3603510f48640244103640003e820021114108000c20074a6a8410f21420000c01030000c8400c015051091a00080c003c0f107500c07031001070050003407418613071044c04141014901310724004100c1d03e038182185c803030610b1424914150112a2907040c0240540b1140013181e03201c040c5050318001030503140c02c61020b504d81c00303040005010424912034848549a541c41400b00d01d00188500010341006110241c2e094021002000c1002140d030252082c1c0b2800384940000c0c500d0810b000204454900c0000c0384a903020045400308008900b134841680003a40c4507e0002070102c8804c0005441c80403207034000c180c12818942d40114028106204030746809054030400d00e0420001001400f9002e00e00c913909031540b0301005192000c00005001002c8030700e9400f50340750b8072005c440702034540f00111100c0000e2041d96004002a881035804140c000400f0b190850034030094a030f40c071000f41d010b02d43c64024081c0120070301c0709201c0700c0e20701c0981004241404000b00e49031035002c42c41040800030301a20105 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 803574766 1250 803573516 803573549
    0xb09102a0c05031e120a0213050108090f071d130302031909030212060402010f090311190308040608011406091804080c01020d090c080c06040b0a120507050712090f 72
    0x40100181c41d000e03246103111300828003003122214403a41214002c80100e1720030b1030200b81500c0032071003100c0102c110001c5070154a8184001510064009002111a442402084880410240200710150115a54484403140c0c1c040150494180160002e090b000301100d00d400001e03000422611a401c503100d048020f21040041a240f2110a5002035002186100c2c8011030b8180410040c1c4070b28401d0300c403240c20b102860303000c484009150000608203040411007400030b107000e01c5e090420800c41c5860090454a0795161300c03040d00300754003040114a103000180704413810490141c01404003a16203504041034040015000000074040280c0501450045010302500c4002c441e4200c403006c009540d80d002c6050658014942070106507548031844c4008219660003080d4140100c8004000c1402c0ca420b0014001c01130f80410459010700c014000032042c20740781409041d20640880e1540c0d0b40310b44480c01e144254007200b224440410000c410244228814039a00e20269142120340540b0003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 803576016 1250 803574766 803574773
    0xf060d0603050f0d210b040f050703200406030e0a020409030801030c09150506070515090d030e0a082709070f031a1f0203040308070803100f03230a0b09102a0c 70
    0x803d10385d286c80e5002030070446585450f00941d0040d900400c0c280ea010030501c24048490588451203041149560004000c00c20100d40b1a4104d42b040d10180b01c10b4400d8210141d00007411102a4001180400c01210040040c00041c0c60003900401c10440c0038404c5940c801403100c180d9005004843c49240d010501405000c01000810403041c12003a85072034600703101001c81c0e9150341c0c096903100003a04000c8801c100e0071012a00ca9203032340c1d0112106003491f4034031014a0100c1d9820084400400107040541080c2c0ea5503000b1714011195519940c07400400c061005080d90641c40c0380780d20f01c032802c4d14812500c1c0c880b140d6200341c0c440c141840203125203141104900b0351149500c082d149540100b1600c1c00c3c4009040218061440c102e2429410b540c0c504050740b031001b0a101c080c1460f62500300c0c4000056488405e80910180d90701520002c80b07495584c07a086d47d0060342d407901a50f11480c035140743d003071076403003060711005104014960580c135020000b10000c2042603403404204582ca01c00040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 803577266 1250 803576016 803576021
    0x20901120320160603092d0b0403030906050708040b010b13030506100617091221070e240702130b03101e02090f0904020f060d0603050f0d21 62
    0x81c1c880c00a81c1d2649544158525541c64042950f2181805940800020b040d03000344a40302c0700c158441030120324100179520034110118480d19040340071840340c1c14040020311040ca0248a0340c485c0d14006000005403d00c1800c07200e0080c040c1d002d100d008414800815014400c440c1115050000e03981d03220f01d1202500810001684010005d02c01c00e02400401d944d1b2240900c00d9404699440c61041d07940c440411a84000b6207450701d054002544084060f0020002810a02c041092075006490094404006010200c0d801070000b1800d01e0b4500e05460042c54060080c0d51500c0d41441100003010300c4180c1d0b100c0d03014000d101c0c3c0c5036140700803248030454000101803400241610a44d070038000c1d001c0040e080c00200c0c075000c2040c90340b40080100b80e038420369a800d44007910260014500c04c050044001c030240090380d2001414090f004240e40b1400100140010700c0008500e076442c61400c2d40c50000c0c0000398440c2908600ea032002ca04da844407812080c442c00f8101c4003440303101c10218500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 803578516 1250 803577266 803577287
    0x30f0b040212010f050402190b0f0d110d140a05090c0d1b0605131d01030f0c05091008011a0102060c131d160c05030d0209181614070209011203 63
    0x2d2542050070408200c06550700c868442d5009898078044141c0c44558400c0c151aa801520480d090030302c40c00e5034461852001d0b1011700038000c00056140040510341d4a2a04145003003001c044e125810300d06951000c1c03000c950010040701c418003560600206003506d4942a9113482c1c001c55000c0e1103201404000c840c10496440304003600488291601c070b00410980c4900c00d0800c1440c060b010019052000110b00d0f14003000c20074011f610303030f42076a50346849038078600816980700c0704030385010802c1e95400320481c3c0596440e21003011039500d41000c1500f907071000c807003c05080d8115121107504c1d0360041483d9500042d80b5400d03070380d2413100750160081c040c0c80d03401c542480180700034601303c120305070700e5140e0141200006440460b03d40003406c44200001040003411034006004d05805030360310790054142d88c0801009515a204040d82d000c1d07280008a52005864900c6200ca61840303400424203480356041711540c030b15000968000c140900f1041c446c150301038896600072800c0c14812201400d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 803579766 1250 803578516 803578549
    0x530242d0a090216030206070c020a05010e042406020c09060a060c05120a080708090d140a0504080a050d1715091e0a0e0105060d051f020f04060c0b10030f0b0402 71
    0x1512880850040700904c1400d0008030050320039070003c2183c031405105400313040c41d0300a0046103024201001103940000807581a50802d44480d103c0408801008582d0303a1140c0f20780303d082c40d45103041b800034506410044403500800d441c00500041d6229102204207070346c031900344aa1a58803603d00203280005d0490040000340011943c070385801e607c4030340380740104043d0380c43c0d06070740e02d03070342c1c205921608030305403203000300707440302414080d000c070003c00b070100c4000c1c0e402c101e0b040c140e54044032030410441440890b8a500f00700d282050103600300314440000d0f110f0344800c1d000361a05030a00650364440c80101c500c680d002000144400203003c02c4004100c410b41408a0315051a240040142801401404695003010001b0325039050104140b881180c02c04010030070194850781740306208000302e62071a4101d4013007010708842000c41008100402030759a8503d18923503c3e0400300f071610720160480382c0d045500300b410808280304203407129400740c014840da0b041e40c80c1e500c0050300b030718204000c0c01c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 803581016 1250 803579766 803579771
    0x10203130b2107080403140d15030b0a020a020a031103190302031008010b0d02041a090c041a0406090b2a0d021b010530242d0a09 57
    0x4103101c0c18240c06031120b0b10502c0755107900c80c06a02c0c0c0c1c1c00060041250004001000c0c1c4c400940824402d500c034040304207040362114034041304c9818030016140310076480c030b9015662000c2042008001c02481d6449802400d0850611451640094441d091210b02408101784210306011000050040303a000d16040d900d000140f11301100c028029400071500300303d1815040c840017a00035018001c000350418000d14401d0307402c400740e00700300060200c0904081c0003041003201c2c19042d1504104a0300500c042c204054a444c6004a1006441031580d042c0b80007003400e01080001d1600b010444040e166030601144e124540c001c00b07800e00402102090b0300d1120070f00841c04000001065496441c0003a500341e8140d4055108024070206540c00c40a000900400000c1c56260182070300b02c40c0b240110f51030030200c00d00040300304a1050141c480b51020b11b91460800716040c06e8203901815004262020003140d003c04244400010044103c800700a000780c1000100385d689107106805403007109001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 803582266 1250 803581016 803581019
    0x3061e03030225360e030a110114010603050405190f02060d290411040f031101091203020318190905100b0408070501031d030d020a0c12080f1806130201020313 70
    0x1003484c4500943e4003021100f542d80484070822440d40260310070f041510004501e0098400400c48062101200c01080342d541c5520000250702c407503490a00800c400c0c3e43c0454207041504020b070030a0f407021041e0a015007014504c00c0040c0c0342443ca4201950111070241d12040f500030b5002c043c0104000c10800790311280380303c99010400c5a41c07220751071400e0b03600300320680380c0c4400710105101d10700138601e6166005004100280108000004500c0c040c5030461030540d0301c803116064031107545002c902580012400800c0381084070808030005100b102d594030840390101e10345900324440d011f181c2c142c580b540005071300310b258424580005c01d0450241c41d84d07682da400d001a1901200d0160a002a041c0801e00f4403030070325141500c0d6000c000348069840d10030a031056400a40c00f140c2d1681c103001030a0f5803800410701c16801c0c441001c1590b21014036920300350804505200c0000c2800580f401d24a00100c0f024034006401503000610140c2840c005200d400141c0c80d5004429821001e010040030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 803583516 1250 803582266 803582309
    0x70f06021c05182505040902010e220c0c0f020d030e0307120b100f06080402240307030518031b03070212071e0308070b04061b03061e03030225 63
    0xd901641e444140c007030b100c00140600780001404d001503120072128040c0001400181380ca035111030a11881410050f050411201c04505c652105002c249401140309000440c1900d850107955a5040344d850301002c8110b4135079800c88042c026a2020b4002c80c0555403000405000d46241c0d0502000181140e9501d65203000010b800f00600c081180c071908120045200091440b01080656203201040c1c400182084c42c1141d81e507100900c260707400346192a4503100c40707409a071948041c00b0034000e2243d40740f03080b074001340503a9009443e02014082d546c901c0314a03a28048207a030b49030460107071402c00808400c00002d195000b9050065031100d5084c5c441c00468400107250b00031165031040d000c1041e0411040040a00d0307031071101520142080140c01c00150740c20441c254402d10800c1d000840800400c40616030501903140000420307515402805028107003a180d03400d08112611600286040da03500948604e4076084c0005154640c50090f000401003840742c4000d814140c0815a010390000e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 803584766 1250 803583516 803583541
    0x8040f050322140d1202010209090a0209010305070c0206041404060918140706021e010207050f010e010f020f0a030207020315070c0209011d151c06091106070f06021c05 74
    0x40d00145900882940040d10007450207006401a82c01444c52004102907100c5405804400780704c40c0455500308410b01c4140d0b141e661a83c0074200c00e090046c1c40341c00d5400054215071014042d0303414030050141071001a80e85000f1a02035a500810001081b00c105001c14080c291607000740606a04140c91301c0303004c03c00507102d911820b02900c8030165250f81005100d485448034000d417401a00700001c0e604100c2141c0c0007005c018103001d40014504130300340d01d6407030800141040c900c0599444e40300784a10001d00340900240b200c02101d08615188103841d0580c52885016011018903801280c00c1c404d40d07505111403108404400f51190035407408050081441060704012403056440900105400072012080542402e8030603c0198a441d480c43d00f404a1500542e896807207846440702440d281c801c01c0000f81c219201d090081307010381036403034000c190300715906d50240034100030704c030541c0460791461a03d0500c0b0f4020200513076820b4051040c200d01003102c422414803500300000d0002c08403186 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 803586016 1250 803584766 803584807
    0x9030a06021222030c0809011403040c080d09050f120a02280b070b06010804140703080d0507020c0d120c080441091e070906030c0206040209010608040f0503 69
    0x607044141c541d2103242002c5561a00c200380130740000c2e020841140090b810700c00420010b41c0504000810001980d0400c4003503000304d030125402070041c00d0800c441c200800c0f00c051a000a420f11301c084905200101c3c45600b0116411031140880307000580802c0d809202e40480c858011b03040642c0400f1003104160403003180e06003c001d038143d82000194540c1d841c1d0a4a62040e80700d001c4400341d8460f8401102c014001800075600101107041d001594041040003030020351007403103880d4544480c00c5a0004075000105040c0554000500300a0b072550b0316100c0b200d000c1d40c05078405403124030b82c0c10102c0b00c516481100825031540024049078141c50404c00c10043c009a01600d40200c031280c1342007032103032900e4a07402015240d5880024840c9072190344076501401e05104c90000c05940845001403140545100c03003c81d0000400f440269410701075080d400d03600740020f00d0706040c0b650200d207100344144140c50400880101140400c03074200110705c1696041002c5075282c81c0c140f0455590350707003403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 803587266 1250 803586016 803586031
    0x60b0d390801120c05090714180405010f050a0e0a020d02040609052e03390809061005060307020319020c120f0c0f0a080105011410032009030a060212 66
    0x2000700000700f4a200b1036040f00055445518400d00703030310b000284001c1c00d04c0509003205200780c0b64500710302c88400350301810040750741d084148405c001c00360030f000c11114103820104410385256400e01c0f5584581c100e400842d080e4010383c0405594000290000b030050030040504503000003400180d90360f0041210040e00c608861114500c00000ba144d20b44010350300c19040030407200c5460003a01c9019030310081141d80e0503146010b8541c041c0f40050780c1240030306400816102c000c001600b003168000020b039071160440004080605080201003580842d5100b02e6210b00d1000000072038580c800d005441d1003040701d00b170b03007400f00c100070101945806008450070300440f0321000b00c1c00c5003d000038101520201d040d001d0701241c0c0c0b1240900003509128200c030b40c3c00000300c510000780c100091189078002c0540051106000d9016070800125440a40c0d1040c00c1604080707000e60030301c0301041c19035034140d001c0301c9981d40e545001001c242000016400a040c452000c58401002c0e01d5400006126902 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 803588516 1250 803587266 803587277
    0x80309191d0106032a12020702060408070305281b05181909020906190302030f030a0201050601030b0f130e030d050402030c03010608030409020702030a060507020c1201060b0d39 78
    0x91000024024040e0180300c0069003030441144540c0b134001c8411900106ea0800050b16007081900843d595500c41d0340184015400548108240a4140318102548501c1c00c000c604807800085050b10a5040101c00350886600d10508100d4070240c0304890700070200580a4040801481110b50240d00c00b11740381202d001880b000482003244610510f0810703940102250340945500c5c01744802080e0301040248020020a0088096074003040000380030455000156591a0000350080c00d58001910490505041001200c0f0350f07952141840c80020090f60904034410b0301d141c01c640600384112071a801400000341840101181d500a80e21550003502298907403940f1005150894003207101d504041c0e08140001e0140c0403140d0024104a030004040741c52140315030301d580044078002d5680e007000da070101414142741d0a00c4da125000c1303a81080e0013000043c0c64100318030102e100f50403508a0b425940c01c0c020381c0080045804441d20403040381e81c00b0301a000c00048610594016188401099 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 803589766 1250 803588516 803588531
    0x6030c10030e120a0507030e030a06111801180605032509061704051f1e0b13090201020607050d060f060e03061501020d0c050a06290a080309191d010603 67
    0x100c90701111349405480e503803070785407101c5038070b0448220b22040081c950500641048601241d803d0189031052500c1203280c0343c1c0c901814450080400f042d04000e410320008003a014400c03451110060111280b40c101556203985042450080c03000001c0b40d2106405d806900d514019401180c6409807a002d0b01c50000391420300c0c10702300060700100d500170314030f81c00300b412407400c0408140b80070044d0a80c0d410100b640721f21003001000640050202c0400030b552401d22440e54a44001903e101d1440c5403030030426460683c000030345036034000b48260180310f000602034200202a90241c1c0082c001d445860b5200c0d522040010300a1221280c0d46100c0c2c880c1001140700c0c010710160051344128140c000b000040011001520124884c2d8801e80c2c890040c444000041001c900a4580c0e076038014507260481d814100c2107114a412059105004440041c01400301207000812154180130071a03407503101d401c60b407040f846540750f140c02c421041e25a4190312090709802250540c10303201c16071810301056 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 803591016 1250 803589766 803589793
    0xf1e0819050f04060c05070e0108011512030804110d15021b0d0914010306090203090708070b04050d060e0c030f100b040c0f0f0909020403051b0d0b04060506030c10030e 74
    0xa020742d00d01803100d940c0c104400c11440340a883d100c99000d01c150f040d140510380c0d43c0069070100d0030907400b621442e5112103451201c001056280e10203002c4020703640042032404d480040c1840030040c00146003c042d29902c8035956600a10000280e600048107007000e10542c1040d000b80d0410301021b005048861303003004601102244605015600382e0301c03101220700d0161141c5c07428001c0e0304014141030381d13120041400c3c20706000551003902070030000c00707100d80f600c90036610306411940301d083d84007004e00c4180080d64910620745580b0703401034000700707010070000c12042c00d01e0180c800245e41407080c000c884007050070100750000c4106280000700100d03184c030350034481070f00c1007140d01e2800210001e4007402007a003d00015106210b03a450f00241442e00c940f403150499100f5041950795030322000300d9031001c01c403402c44081158030a4405803909120396070f498455040c00740008002c40d845500181d8180c40030445424a010000d00710084e20030501d10250040509140809c2c150041c86d20400c0e01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 803592266 1250 803591016 803591027
    0x32d031b03020721030f05090a020109050102010218010507050f1507120b0d08030901140c130b040b040b0c0f031605060a06030825080a05030115080103020d0f1e0819 73
    0x150750700400140c803020114070440004c9181c1d19103010915580345201c000d440340a12a0610802807880140f501e96070900001d01100055030006045a00411060b01d8201806150100031602820f0082d01c0700d14600d0b00a00b4201c0740003a074820340c03262803001c0b40302030450030490780541516250300002c01290301d040029160a11141c2c0d42001d112008000000d050b0b01c0115800801d5000006000c2d9603852038105052007a2904115008042a00b480e0720b81c42d01c01d1000180034050750b0516107440d201000000303006500c40d00c12102d9002c9030402408209001020707601c4401e001b500d0b500c000ea440b000b034594100c02d00544480c880c20002803040e800034032465040d070717401c1502c4505024034610449142c0b04c81e00e03003903140c074007107480001d0020303c801c0c01401c050b1701d25858054480d81001188151014000c50b01c50800625030b0040015854080f108060180c002c1d0300602c0700c4009040081180c00c42c540c0f1810300903100241d560034080702c03001400f02c0f88a40580050041c4450104449 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 803593516 1250 803592266 803592277
    0x105071206060509010c0317071112090906191701020d0c230c0304080616081f0b130b0d0b030709060506090d0221010204061b080304032d031b0302 65
    0x1c90010410a001503001d261b00c942a1482454406100501542030a07140d5005480e010049960209158003440d004c3c03215445c014008840e1504010021001844503000174180768055440d090070342900c04058940c11003d46030b0003820807103034101000034074000d510032401c90b900a45072072034500d40184900d2450182c02c201289400c01c0030002811031103180e03c180c900f098144010400021488410b1180c2441103841c2c401d2084a2440d050300902612002440b80818000407600a03201c1e0340c1c200b0021060340c4d40e610703a043c0c44070611081c541b01018a600b251410480c08902d003040e011103a00616a1101d0580a494149941c2c1d01c0750b106881460282d96480b5070f00b0309c142c5210781051000e0303028845c00204010103001c2442d4460900319034a1600c16120707500054240103943d040584a001c4600b4100c002e607000710349403140c40081c00301074001002c111301154000d0b140c5812540c00c0300d96034113030510320044c0910079102070010805d0b074130000810028105a070070322602034400e403207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 803594766 1250 803593516 803593529
    0x303150315161107180207110303030906070804060621060c03020306010203070312110a080412020601030f02040c03061502010e010b0603060109051005070b0c030901200a180b0c0105071206 83
    0x2d1881e800c1d00010343d45000c404020504510609400084814059401303e0441e103e0910040e07540205042c006070303264060356902e011f80d004101340049041e0000e01e42d50301c900c65103080025520340b46409c002411256018050f00340f00c050480340e4480e0510644400144106000c1201c00481c0d1404d40030790008a86182c09600700340501740100e400740c05031043d20107582c40c0028209901d040300c0c100ba90012810440050708280c100010442545208031440c0c00e640014031645d89144c0e1070404100c080c0c0300090040d03445100502c009030094000c04040c0c050105c0e50010400f45c420004d0003062410810b41c5590b007490750320441d50921408480c012001170390b81460103030030300c0107001c0e001601501c400200001004090081188160424020500140c1d215030fa410290341c2603003541d0498160140c0030f054003000c0d108040c850300c1124801442420f2540740340d4038040001031b4900300c83d800507040500019448032201410342c0302d80c0c0b00d5243c035220038035218003424024007190014010350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 803596016 1250 803594766 803594791
    0x30f0108010c2f0a0b0c03100e010f12081201090c020d0c0b0c1b0d0903120302091e0d170301030201080714030a020d0b031501090b04020705150a0209030303150315 72
    0x68403c0b2200102060318101d903400c0b00e0b2000800e50740d000d00c17488202c0704031242e00d0003c01031000c0c1d07407504035030140203200e20b401001055040c040c404900d0b0f1314034410b05210185907106002002011810340721b04003000c0c000c2885541c3e441d41000003800301d150350100140100303100d04015500904110b00490342000c485030f2541d4590720041c0440d48415400c4601758451034030400015001c10074050120025552a1150352452400814202918206009040c0140102c019545401d59501c46620500c49013422040900d030100e140e075540180c0c050101114171103800c0031030901c24011412640b0030380c1c1e0b100b1540c1e42ca5100f2140b2000090030104030100c02c0001c604443c105030007500c980c1060200002e042420740000a02c2c200c00004400340701188400100303c00781d218499000d200f0f100fa68298580610f41d90f40d203444000300d140a0500c8100312011030450103540d8182c034901c020140c201e0780d890034507a110101c502202c0303000074400e01c100000006102120001d04e40030b10070041d00c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 803597122 1106 803596016 803596067
    0x307060f080f13120509040c080612030304030516050c06160c1e050126010b0414010c08040e060f1302041a04030b070503041106030f0108010c 63
    0x30b841d0685004108201d00860038400001564811603070f0321400100d02e4295814002c41300b842c1e400c07a01d40608902415001041140144400c84080c0c205102c00c03026981d4030302c400c0b2070081c001202070144280380d44051100091040c494415a40d13445c1807400800d043d500414402c40d4051626040c0d02d00f0b0080032010702e4090043c6560384103a4481244201230380303801900c42c050400041c500ca41c00c151032050a200124a1041c54420180d6510303003110a03542c0282c0074090704081802140005580280083c1207469841344046040a01e4a401500c1d0f080000f0032040c0c01c800204891865a910010303450701c0051b0080c401a25507041900351b9062a90681075107200c14002c02041c8081005c500040780d1004461a00c280e907503850f450140b4040301010307929504414048244070665140244050581d41d07580001c00030281d80c1030048401440d40014540b10003c0d0000 = true := by decide +kernel

theorem cover : BRFrame.Cov 803417266 803597122 := by
  have h0 := BRFrame.cov_init 803417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 803417266 ≤ n) (h2 : n < 803597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
