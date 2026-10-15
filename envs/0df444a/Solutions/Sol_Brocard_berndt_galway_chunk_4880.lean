-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4880
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:02:15.725988+00:00
-- url     : https://prove2.me/submissions/5a5e7ae7-f61b-4062-a141-4272d577b4ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 877517985 ≤ n < 877697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 877519235 1250 877517985 877518013
    0x4080313060c0503030c091908061e010f1202030a06050c13060c02060f0c0703020406090c081f06200a06140703050721090512270303040e07020c030f 66
    0x200c000a2005160460960019458060700ca110140130340511110001d0381e5207060b00c1c6c10280200807400907010b00c00c01030741c1e2030b40c464440406950340010955030011440901e002c0c00e16403410f1b00d2030944888555845c100200f050441e11034000c86c2c0501403102c5a10104280d84a5035100b4001c20882036500e8014158a8a031286550440f01c1404001401c0c807015840c1e90080c0c6440c049084035056a44d421010350740d02d40703c103551000754010300b40a000706206890790050819102030352070b003901940320002952090089043c0c11404540032010800410780b090303400401d840d00c00100300710070b110345081c428108920103409072030032621900302c21f120324001c121260b030145903803404012504121000400d43c00320240c990302107550255200b07a03201d51691100410561000440303220025112503102583c01c0500c01c04003164000b040300390316007851a81000f2644008014614160800e8078601d55940c000d40010114031074018004466101040088164440780c401008103000b8109 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 877520485 1250 877519235 877519267
    0x2b020c01061502070605040504020309010902030607020c0f0d15110c0a082a0604020f01210f060510020c09181005090d0302090102100c050f0f0a02010f09050d0e01020c0303040803 79
    0xa541c0b0456115600030052664440107860903100222130250b541d4440190050240c000001c0c003940c540500d4003170282c4144c00140080e000142030b601e42034400214420030550152880015003005124644851040c849500128000d00d84226050610042500c01454408401c0c01250a03640002d150501c0742400f00701d00c8281aa07165002c0401418a0f140344c0d1101d0740500024000c9140d106122000da0003484203d09a400d1400c0041c082c2d440410311b440070300b40c1910703040306c282c0c136108000c01c03281414056503012904035002401011042400e0043c0326100400070714220030074660244c0c03903038418020714030320410800003c1441d0801c001442e043c10407400241c0f0a02d441007100215a0740c02040110586240050004002c1400c503402c1e204d510601440d14203402000901121f1903c02c180507006070303000d5600030002641319242c00f0040314009a8090304c1035008104a40c2d046101700b1340c0c84082101807066500b0144620007084c5140c00941010074160000b25106143c000120 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 877521735 1250 877520485 877520519
    0x120306060216080c010e0a350d080c090607080403140f0601060c0b04082203050c090106090b1810030903080c0307050a1209020613030302160b2b020c0106 68
    0x1d01200c11081c030382a042a074500d95100724906106d01703a290904550b585000000043c180d1249808901115101c00c1c0384ca0300f001c0520301600454020034403110400010030442d0400360752501029905d481c203044800d82c00000b101d035808030301004400c0014001d80094002507100d0103444003007003010b2601904000c035101c45410b080d0702190041005552110180500036007010b5104540c0d02c1d40c0c100311816104802c8000e001c01380107404101c0c4032118600c4602180e00400c2960640101d12080105200c02880391400140d540402808035207000e6000f131030130024644c048202d054021021072101020a815500030a94480326401032541000360b0316408518001c03c0c51a5280c000c074040e20314058041c000c420040c810202d154103404a90200c0e004a400612454803025404500c110403440d501044005024407108000b4a940005071101900c070051070107030900131207038800e9450369442c03000031202d403055183d00640294140300a0082500c0c1c600007044982c1041081360f0704130402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 877522985 1250 877521735 877521763
    0x21603081b0d0b030705030f0616020313140f03070e0a0e07030b0f040c03080f0711010305040507030b06031e0a060608030f04090c0e090a060e0106020a030509040203070306031203060602 82
    0x1103030009a1503901101150b07242c1c100b501c070002c0e1660503403000c00d180801640089030580700d0000101c610444c0002e2051007038050b8003a90411801c918070032030322070259540020441030108014824060012600c2c03000200203007d00741c5410704940001d2070418664815204500610b0522410311528001d031354664450000a00805145540701000000014403140354a00540301207002c000e42841010b0040d0307004103c05440d00a08142d0b078125502c0550700322203c60701c8204d080360b554000e0203168411a0004054600c83d407841d1038404100308000c7c0076a9041c0110841d0090402c03800300760010300410200240781c210340d40d28042040316030540212060b54424800040800116003c40b1300341c0f916220042040c0080f00400d8504078048550700d940207205008200d40807103583d010804640805031245003c0c0d0340c801e01a80c9841068902400043e8204415280c90a081d0004d6400c007942c1d140005000e540e9841d640440000c0b031b6441d5001a031903003420419036070f04011001c0c1803221 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 877524235 1250 877522985 877523011
    0x908010c03110421050601031b05040504030503040b07030e03041e092c1c080a0c08090d200d0507052e2d0902030709021206090a0f02160308 62
    0x386282503111801103100b241c11903161554100c2c01d4542a135002207040354480d003120350b656121315161120322042a4000700444c01a82e000070350740350600500c0c0c0a21340540313032280b42d600c85403106040b0020040140091589840c11001401800c20003400188240782d540c0c0030401d1035446060f0079140aa100641070380c1000c14482c186108008010000d9100c8400140c244603444001030070f0507559040804242c00d0038412090058205e610070344201c0d940782081103400341ca0035099425030010348402c030413a402400c40780301e1607010321400354074583d22007203103d64501001d40007482d00d800b0040c40c400051001c65240200001040512000d040304003200c410800059240c1c1100c01c0c2880150f1480c580ba25140f1903400004402c0000701e02d05d056400020303000000240004c0c0c0308a6004a001c1c3c4249403000502074842c0c400d49010810301c0c0c0c00200107032155410400740f600060242154035a40300720242100c501d40c80146801c00401440103110302d000d0402a002840081801d049024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 877525485 1250 877524235 877524251
    0x20c011d1005070309030c091d0109170a02010e0a26040302130f09020405150102150f010909020310020a1706011805010f0e09011403010b0319081c0c0908010c03 71
    0x203103405801540c5071107440d12039101e85403070a084908490541c03003d40807040110004c02c40c056160801c40c02c001145400203010402100c18900700d6900d02d9015181003003000c2554210301d100c0b4010248002c00d840042a101441c01410b03050032045d10044442d02540100e86500c0790005940005403200b00e41e5040c14285160003240d4480d03052602f5450490b92226030410094280e0320946490303070007800401c210719000c40300c00f4582c04104801c0c1c3c05031046001501c0d80750318041006118011100b48840390364641300002c800341c0705018003268940180740b00c1e420007400794030244c2001d8a00e40d48100025420003849100e40d0009004e0364108a80303006080d110030040f0705414202c5400307203000b2034603010705d400403610201c0010416030b204201d0000082c2140070742c2e130141c0020008400030003100c4a818101995074206000035501c0d0409487d00d280812203990203828459030a032004034108058200400848644903000404500750350300c240669a42442012101c40490608120b800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 877526735 1250 877525485 877525489
    0x10905030703240e1e010b0f06070206030403030e1203150d020d151d03070501050105010503060a03030813021807080718052419081015030903030e0607020c011d 71
    0x420b6220418642c16190f000c0e008881d10b1503409811400030640990f102e2444580502c1c1d84c1c40c01c1c041e2210401c0d0b080c20f010320b03c54138211840600001008011518003459542030148035040200107805240c0d5501c40040d108405120514850942103095562458444407607462a80d03207041040c01003154802020068641000000300b103600f0a00780318048403044031460103030078031019140d01d07d5800711810408090000c041d00195100304000d0210f60780312001100c06000450b11030354000c200010400101c0d026121703140c1c01840d0504243c186511a4000c101c510700305c03e0700054803022090400860a900c8242c45401003032914200601c0e440580072300925580a01079144201941500d4116003a00c5a00fa6081c100d509410349407101d4910307181000c83c0e4000c41036407020948506c00207001031b0703022840c1e600f502c4802581d088c034028910301c100c4c003d00c1d1264084041c10303a604201d00c82c3d5a030030004144540303c0c0b030f801003041080400005027842016002075146540102280d000c0d9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 877527985 1250 877526735 877526753
    0xc020303040201083d0e01090b0d0b07120212060f0904080421140c0901090204030803040809220204090e0c0a050f0112020a020c0a080606030a0b0613020c0606010905030703 76
    0x72681d8065685a46500029004178601c076031401d031800c1c80b844454203075a80b14a81888001c5843d9403480c048581e9031202e003c0261081071048590100e0f0403448980010650304070305810140f240350042e8036003000c9044204981c0203045601911030b0200411049180c4208640b9803c90269160091030505643e0000180218020900c0d00021003400d04000030244a81000c40d6802c0901b0903043e0b4200101d4039241c04014015600484041c4c00200d0300c24014002c4030f0880c1d901060715490741c0d03940e0301d0300c10301c42d00081c0456a011403902d4009816016203072103481246424030300103039100d00e020718a2044454036551440303181c200c001038000b00e9171003900d90b42c211031090b142d52101d88004e4004076522142c0404290f58640b010171410100c550006658040203c00e4032400c1c0c44903101c03507599a84600844000d80d069202c1034001d4002001c1040560708035a001d4500c200028510410b1001e0b604030850701401ca500c02010820a036901c001117400801050303029000080c10342d1201049 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 877529235 1250 877527985 877527991
    0x19201509011514150706061415040306021804020a030f180804050904020f060406180506070b0a0c020102090301020c10060e2e030210080405010f0203090a02012a0807060c02030304020108 82
    0x1440c1c81c41905000b9521081018070800c81c2c00001c0e141c0c0c5d540103280c07050040489004000c142d50140804030000c0c00e04100c0355038225a101303120384c1803c1c0746568010195001480300580c01c4030465150b0215101c0e40080c048402040e02c020403032003000008034046842228500e00b1800328840c41d8001700d82c02004403002d1301c0094400c0001980c69001246111420065842e017103000050700041866101314144441c4400440000c21b6540d50700030842c00d40540b00014101c4201400803621f8145154070490b03403005035000140c1080b005100082c2242c000203442e001039000303260341464003612803054002509042c2462400e81c00c081c140129100c846a20104a110300070042c1c455000341100c400e401103500070510b22800109520080c85820241c0741111198285100c04d07626580c0da000ba244900c02e06401001124020703001103411800a1041c2d0903020f40c840c8006108240201003014070501900700345da542e00140c94414101c1c1c0d071030120320046400920a01c030041c0c0c3c1c04902990 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 877530485 1250 877529235 877529249
    0x3011090f071d1e04110403050a030e060f03070c0c170706020105010b04080a150207050604060204030b0f010515070309170106061b11040e0c030d0f0f14192015090115 73
    0x124403d50080424010180c2c1040c2e46140348000c680081008030003ea009100d6100756207060752115101c00388499405a20346001d1410810300010706074a10901c1d00c03000d094014040d00e00b2050750b4011104030800707003503907030a141e400a074010b004098090180707900405d50401d20501d0140b070212840d4407a40b032038500404140009210950301030294065614a036001001ea4100d82814503265000f0b50003803200b1039444c0d425500240041c6102c2e40014101c442c09002d104203002500c10464040e480080120240a40103002140e681501e8201841c616041d000015a150410601030030800c00845484103801c1403c01c28000101201c050b100f28403030035100070842410b81d000d080d060181c2c40680c19007502c90607107110041980400f20103071032241521041511882c1a5080b180b01c0b20241546a043c00100049052801c10040280c0500360600e0104045c184510005560001d0350140540662020a080d2850b550803080795030004e0001c8000c0219040300c0d950540d00506520500b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 877531735 1250 877530485 877530529
    0x10f0606051908060a091109010e010c231504050106050901120c060e0114030405060723040e060d05061005040501150824060d02040e013011090f071d 66
    0xc4c4281e11814215400b07031070141024004121318149002054100e40903490014002204403d010350194110038005a0040c1a02d8651070700c0c148840c03480081c0c1300c1004d150b440340001d124241815214040c0c00340340b04000100c2c04500d001c08021020340180c0089501996100d04c0c500010a402012011195281000302c61413100a00680d1106038030880c100c51400000108002c2102c0424414443c110503160229103544080440001d129040a501401c4500300401d2265041d403000841e8400c0004003800c9a5401540e900d5080c000159079409014405a070140500d29141c012140075103a1079482b450700c11603d1000510464014002c032009461100100381203403c1414070440e602400b0b030542d82c0d201c0410724920020b500910070780061201e090004a103040541011a1081d080b4141e1541d0b41c010f000c48640540702d0f000302c111100008003009003241c2d1510403003180700d40a43ca1740a0f81c01d1601c0c0201034a82e17201d82c9142c051294000b5000d83c401d07070b1100500001c45e54944001c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 877532985 1250 877531735 877531741
    0x4020f07110102031b011b03020408031e2206030b01020a0308040b0a060b0a0c142d2802091305101d010501030f020310050f0a050402030a0f05010f0606051908 70
    0x140d044d07126042480c6811103100700c1c04050140150000301907a10010441c0246454091048040f40258000e0841a4100b04101c003a202d84000b038012420202606061500305900155041c2540d89664643c200307001000c03c0142d96094030400743c2607602800500100540fa80d001811070310018001410f0713106041c0403d0741c442c016405031003e05141e100b459950b445901c0003829488031070b40122100300e40c081c036400020001090300d0350f240002c07041c0880301104030700a540401c1c0c0448004880c500c0707800c0e040c8820303607450055030014400c0e001c0082c0004985005110500d00014421805d581480000e240001e0b00022186018040440c0c0000c0800b26101450304112011000c5042c03903080100120a02c600440a2503005100f00c04a40f9600d01a800f00001e89000300c881211042094002030f42c5904241c00c829401032000701030750300d6030030541d60b910942080f41109071801da41d1901070400c0107030144a00005000c4e541082403c1c4240110980407200c1e1038075465003004242c6000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 877534235 1250 877532985 877532987
    0xf07050f04061d0907031a03301309060f080d020601230909150906190f0b0315012c04150603150c0207050402070305090108060a122004020f071101 65
    0x226080300301000780076103640d0074045c0008000c0c1c1420358404801c603441c45206e1809140019840c1c1c1641c00c220348565a40d000c40c0d07002c0c444089090f010054410003003001075000d040890084001e03088010001800f11f003018803d00001e2020741104035aa80700e80c40d512001c03500090010b045a507243d000786072260324251910713002c19034041c000d50407881c44024044c160b070000c0b404000041040c140058181e86020301c240d0b8605040e104110180408507101440c0303001900981441c0c030010700c0104d20246610046494180140000f005519000c001849413501e88007501d071070304119240e540041d401c0c041129601501c06080104142d542c01c941815038581034102e94015504080c19051540841d92500d0243c40c1c840d1044005002d0010007040600d030074401d4848a541659400e42040510001900c10007005022a648000c807981e000500088200040120620460420075a88030001c8034120525103c52503603c187c0c01800b280c0e8500a075103058500203034000b55a10f10490507040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 877535485 1250 877534235 877534277
    0xf090f032f0303040306050603012414191401120c2c040207081b01150b03100f0b04080f070b092209290c0a03020d020c030a080f07050f0406 62
    0xc1882e805010110780001480200d80c01103205070010ba0090000d8204504d12541c400004420440d00844120701407055510030460040c043c00060103d51818800300d1a000c03800300d20b03a100300c80028401024a45550344054150101c6c00301490900c01c4400406000d005600d2181102c07111840c02c500c81c02444804848081c40c004014004641e40c100314100b201c2d441c1d2041e06598118141c14068100b10f44052040c0e01a0020004c860314605040010400d500d03807015010703030b2001a030303184041041c0000003801c0009081d081503c65071140b40480703040c1010942d05840d407564118a00070452095110112085100c3c203c40700b500b40c0da491020391400403100e07518444043c0c5421915030401c5122240100d0f0804401c10342c0c90b2460888010610f0342c002115110300484062000e4050540a5006049070b02c05103103002d0f0812826060962540d0072805914001480d20760500c85001c1e0b80c00300306074100043e40782c22450901da61000308103a10a40c440c42c070402520006e1200d12040c400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 877536735 1250 877535485 877535573
    0x5190501020409090b0423061605070c08030423060a03200a0c0c050f01020c0603131b090b100c150b060c07090501050102030901120c0e030a030f090f03 67
    0xf203803c00025a84e41402a4444400c80c0c00301c4e5545942c501c594004065050140400000c03d0000c00c1c6aa0780d0814440014000f01a02c1080c00024400b9100140244115801a00d2004c0c01151207034a401201144031800f000205e054000d81509000503440d1081151a900c2050030045901c00c5010b03542d01600c0c002c0100710b485604081084017600d07a104004124440c011b40ea00100381e911002007110880c2e5000d181405130340a544042e40da4100380c0061170b4842d9841c82488207800454880343c1c8903010a007018100c009840405109601e090320810a4501003913400a5600c4003217080600a101c02100142c8000c1c0c0e002c201d022030001541040e11044005070425446420007032140d641c504060055407129030a10340041915440041a900456016940c0701c7c03101e0905881c00300240842c013071090070000081c42850b1261001c028040d5618800d554122403540c000c0d40052a504094000c14240054110b08101140364910784440700d11903011205404048101d04200090340c103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 877537985 1250 877536735 877536749
    0x109030b0721061e0e040b04050c03100b0909060c0d1e020c030d0b040b060f0c03070813030b0105030a030c03050903072c01090b0a0b0d020c070e07021009051905010204 74
    0x5010241c03002c510641001040320718440280c02c4c0c45080102160200405002d040c0410740c3c00c41c0068080351600c02c0e526000f5001c1c10581d00400900c0b0082401c2400304600c0803510307500c1e101168007a042454245902ca850100501014240200145c105214050003256030a44542d14403841254032108130180c030305004802c40d590140c40c900261650454094041c00e2440c16101101030f040130b000ba41480e58004000519000084010304c0d05500406881000c520041c000c12000986140003000708a81044002c00da0600d5450301c3d052251050b000503010b5040300c0c000c0c03000640c0200d0f070181034a07414180039480e0460800840c3c0340000a48c0402004521010100360385810070b4001d006240083e00401d07420307030701c8128140680e01005005600403407070400800c81c03008010f014042188401c00090715008045080324500780c0241c100c0071100e000c0700e06101085030100704190103250304040601510059844207a22410740145a0710558124690401009002c0d41198007916132 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 877539235 1250 877537985 877538027
    0x302270906011101151805160503240d2402040e0606031e010e07021902060d05040203070f0308031035070e1006080916091505090711011a0109030b07 66
    0x2e9246040711b0041108140000285070001162186004806c1490b21040d503450355031854480b441045910b0f180f90000005e085140e0964104541e206c0150028043c0540c50003100c03074a401c40300c2c5000e40343e41c6640307810a80c4100f108205c10480782a1542d80076408071401612a55404000e4100e44c00f401000075290000c0000840c81d01603010304c030350042e26030358200da14030006002c1d403d0601c1282100039510070024062082444416000585c0c01480607042e940d08075a1620020302c00d03000c941003190011f1011003001104016a410b00c4001c14a406204403400e0b070410341001c07c4404149800031703401c42d00b20f00001021003004260000c0c141400c1d540300d80c0c0390520810205041d14011075000445140125141e04400034a0811208001c0703102040c2901d008440002002c0d0352075110071441188000141540e5048599840b07490070361642d105000d8181031240c211250005452034112602c0207161060740c0c07218090b42560747c8510000120b44648030240c0301001032010b07014940c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 877540485 1250 877539235 877539239
    0x54212010e0a11040e030405091b0705010903080c0301030b04110109080a03120506090705120601090b040618090509070b03090a1b0602210a030203060a050907030227090601110115 79
    0x440002c1d0388590901442c185201c41a80314100b100303484c020581540c00d54000e03c004e002030719042e15088e8201000040610191950000c2d50502e5000703044255050b0b552081480145500718003556402114002d03050714541c1076a9400c61034510140c409000c80300804440040390b4051075001d0040c0c040e50b001c9840207641c520f002400030440e0442c40c1c820314201000700d03129080014440b030040646890b22130400411900041189100601c40c0e410031001c1f020000c2c082d110a0001c2003d000b0a03650803009049904100000a00070391101d80d21500c4d01c0100305911901144c00002d5517403d82209950340c4030081c2c0c5910b0320003412005403604210070003030719581d0400380b400c8007126020b400781c1b01d00100400b080380c005d1030b1028203201028420001c0c14140c038840e90041d03a01c07910051807050301580742c60104290840440e01c8034017182e400682e8110b441c0360f941d03100c0509005c1810107425803e42c40081004d000d0003911990601c0b0050390b021452580070742100e540a04403203d01c200c180e27 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 877541735 1250 877540485 877540511
    0x12303070f1409060616060b0603160314040809010c05070e01150807030507081b130303020f10020c030d0c0909051311060315010f0302070501020d05421201 69
    0x40c0040c03107101031040e4828040a0b01d0b0900165041c419440106101d0420380c400c1c08000403102d00010840701a55181034080f950750703800020354022060b170075915591400c003001c0601100e060181c001b000170351907000c010000b0b10396011101409001c2c6402000c045040c50210324200c0c0540091903080452030020584200ca00c41002084c4200d07580d40c20b40e9140c6010540890b0801e03907000002810b0440003820466102c1d0040010760308080c00c0c0c0d4508441c070701754100b48404c603400c03c50040e00801c450808c0c5020030030803000da02c0140e07001145001d4174000c025580344602000500000d466005c400c0040380900c5034400200384040341403281d0f00c0c0c000c0c0030b14a00c50307042a04a60060410f031107070003a414080207883c403800c481d403019443c041d86070b0015102540e501e1280b400300b6800f005540300090081c0080c0070720114504c0f0204850400e265103039010811019054103080ea101e1142120340101c0b43d031000803040c50583c0300c9090074040f002c10603480600e407050303520307601b8505a04501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 877542985 1250 877541735 877541759
    0xa050906030414060121081e031003020f0a061218020a06020c1912030c29150303030c04060518120a060516020a0209090102070b04120f08070801230307 67
    0xf040c4502683c501d40c3e02c810030400300440c200c9003554020100501c9074002403c04000b01012004c44071555854042d040e2204a245e0044402c410409080b84040045003024541840f80741c2084071040314040c20100000d1a220a079064a0420381d1124442d051171210381040318001d94028014202698980360701030b40d203007441c200817402141d0411014030356000c01c9000c0e00640b65030000d41c08030100281c07411500c802480c90f054031080b41200020f0f0380c00c2c0c2c00d5003001003100302c01e80d0004800e1411507404180e12900300300e49402038100308200210300c1582411241500d035281042d545401a0b00c14540d41080b000d242140c10407030501035a16008400560b912005118007020700c07007076035500550f90108200e1600d2101581c0001c0d002030040c13038013065090f0300081e400c000500b03058003034488406e990002d650a880341c0d00204111015140d204880500b403c4250407d0030030741c1440700000b0f1000720705200d0301c1c40c1402c071203111b08414030440040031018580101111105500c4d00c5002c021 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 877544235 1250 877542985 877543013
    0x60d09020d020d300c060207020112020324040507270803121906150f050d1b120507020601032315010906080f0303060d080408010903080a0f050603120a0509060304 72
    0x40039040700101c4021040c4c82000d000490a260b494403504000360351154045d402184080b0705102c024400511340341c46a2024610800d0092584902103404402410b122011100d9542c006c50821317042014954004408104996046080120420f02000c500d02d21003000d41110607a4000000c48001c0801c03042c60042c0950480301c43d850b10b8801c500102001caa02d14410707801a24070086003014018011003602c20054030609100d0300d070500c44094541151000c5044048030004943c03188440c1e5484040310865030034402c0c081016080206020f941e40e64140b200520300341205058080025980040e070140001300b8003142c992603d030030340e0707502070102c240142c8818614101002502600006a540f508500c21000d5460760300d5100c00d10134140351040003600c82c080b04000010f0743c81400d20800a4081c06551110010308180c6c4041c0143c03217141c200c0b2880c80d41050305000301e550b00440c008a424221170009a40c520480405494030b00403481d12a9100c4404400c0005000d0b00300d6405c1d403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 877545485 1250 877544235 877544273
    0x180901050601112109030307060e0106080c0a0b0304081e07061407020109210c0b1e0a0504022808071e08280f0c0b190203030105060d09020d020d 64
    0x80701030f032601910b81d5403805110845071881d03074408821908444503004060458029040d28078110003030303d91009445560001000c560b5444008100700d0f01c081c42080d04c00d1100312007403030700e031464004070b041d9a000c040c20203080c81d6400212000054659500e00f0002c1d0903040342142c0b12212400c01c1002040040e07148005140c2503c0002c21192040c4140845954031010100410244004441030003c400d403070b0b8010f01c480d00b28800c3c003080c3c0e02c0000a10400c1210f00e81d0503040b011006446075020080e003000c800a08001c10b00c0016070322111500e41c0d505021416101d0031680c8110640740384580e6104008038000c548000c108050100c1c80c00c1003048441d20000c5400340d55031a8641d0381d2030010440c50b03001010400081d4101c40804041e86d005003d0b05084884082c2c5450307004064905500c40c02c101d240010342000c1072045a00d801c42058640c1c00a50304662412010464a1107600002142599601c0c1200f046665072110742410b1074001d0b000c42518081ca00d409020080324401e900c2d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 877546735 1250 877545485 877545497
    0xe0c0705010507030e1009140f031306090f0e06130c020705030609060f0c070c24110610060e1801031218080717010b150406180320180901050601 64
    0x44215001c1c2c05120b1802c20644010a86c902444100c00002c00d6001404c54900d10300504401c802d0700c0c00c01841c0ca4500b41340700035565683c0210003401c41c4031155071281007400b411481c00c10480011070b40c204104c0e4840700c1c0701c0307209640b4500002d02d844000044900031f03a10300042003044036800038112043da00164100c900c90b840d90744110f80d030390004032040508403242e04005100f156000000c0d01036075102d4502000c4060316021405801d640521500c04184005055004019844160400c0070460706000c1c00e054206582e050000400761301562061010040c0420000e449504500b85604001c218140f0b076075850b0700c2d03d0700508040316420350001d001403100c198100c1080644d002180c00503401400325a01c0c21403210303003c044201422010f07559440d00070b04140c5403044510081d182010602c0d50710360034a10041d1001045103440c2c0c001c00e000400a00c00100803500080d401741d100080f03092452200400107501680359401407940141e10402d100d020401500581c0c01168262188 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 877547985 1250 877546735 877546741
    0x9010e011a10080402030604020f010c060615090608070806040b1210140c2d1204030804050601080f07030f0809030a03090e1b0a0305041b0602100606050a050a0f0302040e0c07050105 80
    0x807030343d8240c2620040e40c99007092020800605c0d2008031881050300c103042540c1000c801c3e0300c882007203413001d50210800041503903944148590060110002d00094180806c41d81000b8100a00b075460050050340115074608940006568140400000166a008032802d1741d8147c81c0c000f018087c400360500b1502c402d030020500f401c80345401e80718030100c01e990030080803c041c103803910b0030b540b40c00d80c1c000601ca0070400e081900260007030203440b4078080d4480c02c2160070a072a05d82d00d000030503401600903401c000500700480354040b03410000c881d0401c08407000002d45040000192003034204113541442400c03000e804143d04010034030700310b940ba24010021a5160341502120001e0200c030707a40c40d030070304001c42860b581c082d034409500702c0d014584401c1c055050360124000102542c0204d800343e48583e40c850004502801030602030310191602c0303400c001030900e020740507010b81c600704c2040c0081c5514403107180d482035061300c0040801a85103501070620380e485840d56070200d4000e440550270a000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 877549235 1250 877547985 877547987
    0x604170609030a02060c030712060b0c1e25270f02041401110c060c1006240c050f010903050a0f082404060909140d080f0f09010e011a10 60
    0x183c80050b00703240c01415013695613041c890a80e07440202003006020300c8902d0500c605882d48502005043d100030855a907441d00e1540c40c0c03038448214800d00d040c901e50030900404860114031441c101003d84403800114a200c405050705000e00d40003240034000b800d1802200c48124809240e1020710408100804405641901c007039203c9c5001d0445088005c0d001503001c2c2d4403c1180b003c00c0c00441040c1c0380054140f00010b0b0060344003240b40c0d03c540d488000719441901c40c41c070a00000340900165600180121004c0003888005100c030182441003410203a0705000c4180204503580344400020000148145800303030154100a06240c0000c1400c8002003580f40642c00c9140120058024a52544107103140d451001c5586c0c2215070300207848410003d440c0c144c500820f01000d100c2c06041aa0b804024180c17860402030404040411143c0c0003401f02c0c440580c41a6a04070f0030026034410103545014110b0b01429034095071002942c600f0b60003075a803042d6400e03180385044003118080c0945500e210 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 877550485 1250 877549235 877549237
    0x90f0601170f0c09010c0b040309061107120602031f080a0303140f04061a060f0904110f0901030f060503030c070303090614180a170105060916050702091005060417060903 75
    0x400354116a0004003049243c002c4101074000c0900526100c0590b071603d0b42c07202e2103510b095408a01086484505001035a040b018440c010b040910042038241e280c001444003200711140c010b0003441d0b000020038490241c1c00c9010442c3c41031403a21010f101c2d542c11402e9039400103002d0540010b8a8102d010400e180480300306405410802c181103010384440c1c940300e005100c8441c07011584082e5102e40e002c5a01d80d24003403da4003140741d902c103450b00303c0038040c8070075200b544618101c0c4070340c100401c5509150035415035041d11004e1900055802c10b4280750b0004100301d81107641d141c8008a158410030500003540d5064911940e9070304285c56440323a094400500215020045400c18440d01c2000d0300901800054030000421601c44030395980301d4124204011041d101003651250b00700512130a082a4081e0010304400107800c4510400d5002031203400342044c0248500102030108110010b80710405014000c002e107001e0790399507150f4480f4400420541c15010501a810000b5420341c0080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 877551735 1250 877550485 877550491
    0xb010e030d121514090727050a06080118020c24070e0a050a06050c0304050a0b120105030a0819030902030607030c02210f0d020c1b03011a0307090209040b090f060117 73
    0x241c0024050200300d0b0402080300d1000f80800700b00107030503891115103018010111150a111840d03c200e188c00e0405100450655030403200c00e03c507000c4010007008910500200352401c06160040c2c03210401c4c0c0c0744c1410444590b1422070100520310880400108041080303000e03c1e0580c407a56001803004040c0004a152440b80d04d50204010304100200e9001e240100600e26522080d00d1a00d0b072a0000a4041e0850f9008020020301c080f0385003003200c0d814032000c1d016101c110000c2c1521748403941da4421780e1080000e42891506511480c1a100c0d00070381120381c0e0954010161480c61401034030050080c050550050014400c110b42c0a8003440403500c11403ca410100300280b403e580e803003404025521076003e011480c0d41c01c00030840201004d100013a244610102d02034025807000e8105425107812124040503102200702054a503074000607490124ac04008000d40c0390340160780000d00501c0b10081060f040f441d42001c100101800b0341c549885503500b47c0710208440200102900300b00021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 877552985 1250 877551735 877551749
    0x4050a2304110112060e0f010509070207120201110a051e1504080a0806010c0c0b3105090a0f0f05010911072a0b1210050f130b010e030d1215 62
    0x40740019544902000d4001d01d04c41c4102048240d03a03a5804840d449007190080200912180144481c0c82c00a120795001000751006111f22804d01394484511800e00304002e0502000040e03142110006100703004500b5040720660b0f01d60391000c941d00403d600e6696011582e402210b48420300b50004205460041d600816054242a00e4010960b079294001c1d002e607040c0520856410005043d8410a80241c001d20814036154056003540c88c456442ca0f90700800c0200802101744c08011800711810304491040b0303890220f80d11845107060051411500c0b080600c1d04003d89010f20780f01c0e5400c05070481e28216010050441d819a240e0414018020b008148a00e0100f8040ba80100c4c0001c40001994a81089072035660350012840b0b1a03008015081c0034813402001c1080d0580b1511500d0020441a00c08a001c200008000381596451215511100d075a81000201d40d901c04d004601c0e0070718019084806018414070098000c404884800500c1c9083c0340f1694685032a0002e924215452 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 877554235 1250 877552985 877553003
    0x6110a061508030a1e110d03090813120209010b16060e03090904050d0807110a030818030406080906060a1d060102010b1003060618060905100e04050a2304 68
    0x815503540001d0001d80000d500c055240d58000710b0180002c1c0b008050400c3c00782c85000b0100301c200f40c1e0110100190b510642031006a540c10403004001254540d0f210700d451400240c100fa0a20b00000c0e0340c05050b860703020883e0f602001064156120240c000503070f0003182e10400b03aa0307031303023441c180c0e50f1090300100304c5841c17411000500001e00380d800c610814158002540d08085803000480e4414401b242c0942d090b07844526805c1c00c1e0340e0800841600b110442c900a4590b80d400c01c07116035101c0c07521400404204160001500080d4212280741c0d07140701c0d4205803681c0e0f0703540d804020050721099510700524001e209c04a2610b15251002000701c46481240c0e0030104402001d801c4544c1000300664107554035044070030800c0c0e50720b4006502141c82ca85000958a0030500002c05040c00240c400c449401701c1901404915004881c00045a40c00c490701c01042900710001c4506a00410b08950401d041c00300340500c03d4503540180d01c21140301d4103540000c01d042c00707801c00e003000c0640d406821040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 877555485 1250 877554235 877554253
    0x60e1902150a0c1e05030f04050f1e0d0303060f06090807060f0210020d09021f0306060305220f0c08062211010f0509030604060c080c070b0f070c08220611 68
    0x2c0781c3c0b0004029a0903004071301c40b12001035140c142c25039120480707003c103200c0b0000307080c0054a00710001411940040d1140402041d10700c4001c14840c04031151305d03100c0c8803034064010401d40300e604008003034008080580d24059071800c015200f8080c90050300f42500031004082081031091080520b41802d5030700a1224045850107032000f50310076007050500984488043d00507884518084802c5009803076044c00c0b1200f00d00f00141100c41940200381007604142c1407151203c400075465a10400401129031905407520302840000030000000300b510038811000190010041234180c071440380340d0307050f410303c0d860000c40390007040108038001d2007040b1004080702d181d40720300d4840e0700c01e02d02801c2540c507000001c000245001c804940031142c01c0c0d1503d1219581ca0707801640d154000e5040c0800c107013010b100d42d5801c502c00200a103100c00d40d03ea80c034000384540c1e01c118128006160009005075071418141a03803a44084040000c4d07010400040001400a00c200c00800c0d41036012805044648 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 877556735 1250 877555485 877555493
    0x4032c0108040305040e0910180b0103140a0f080c1b060d0c11030c0a02030d08060907050d02070c080606150408070b03060303040b0a020330070c060e1902150a0c 71
    0x14030060b10690401c0000e010101b1000358980815004002030310017130013116640c1c0701d00300030b40701804034000e4211522540c480002c0e501d095418150303944a50325480217005103507424034040041101400a481c607003407001c1809800ba008004402070076003940d0791241d03160f40c18100f1500c00484160403101c10441184540044e5024070102d0b00240340000743c002c0d4607400a890740d040300c110841c042d0062240c1302e0442c40c0403c09401c240a581c00c00401e01e252071400035256a40060142050080001e11810542c41710381c11108455031094038404d596403164078a0703944076000c030b03011350040481440011504c0b030b03006c00784e174111380d0f0300300003466298140102046175800c00b0304160740500c000d200c08241503590f94041d100540e0541d00641d161448216003000710f18011030080496844001000c503009680111584c1c80612406c00c09084a030503d405002440782e40e80b04c440c24001c0b18502812038081036500c8001c14000c4640c0408074050600000d030501c0b4215154011441d5881e0004c001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 877557985 1250 877556735 877556747
    0x6190902010e03060a0609050603120a0f0c0b0f092b030c020f011b0216030f0305030c0904060305030309010c170f07020307050d020a150219120b1804032c01 69
    0x28030616149098100b0034000c04c3c0741c064280e401d0a042c6441d10340a2089030340e03500c6100e0b4811000c4004055004251613860403d03c611021081003015071541200060700070f01141a000d5402500300b1842d00d0440b4034100000b8058541020f180940748445000400a0301c1c1000a2100e44c10780030304034400207074282d0040500d000c01c0400d6006922045409110030720500000e0020341c1e09010070481041c1d00241024252000814072400020082c8045801c2c9400380c0304059150606554a8a0381c1c1101d0f0040d0003560b50141d4883e04004020081140c00300203140144206002032040411184084d1008030441c002e102c000c0c914080010035140c1310300b8400f034210380303035006803450400c0c81d45a050070107140800c3c1c000564003400c003031410401c44e0040e0890a0314500811800c01c04218590200c90072286c042200b01f002041c4441c1e045e80c0c81e507000304182d000080c55107501a120054510a01104913001d5020959040c00e0141c090f1001071001071640101010004c801002c0f4015101e0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 877559235 1250 877557985 877558001
    0xa0507320d0c020606090708010e3d06030608120703051b0601060e0402040b090d02010216030f021c12030e03070b010b0c460204090c0906080619 64
    0x400a2524268080c0d068200051180c81e0072258045804030302580068500680945218020505442000380d038913403010510341960008130f051480c0b501d03881490008505040c04c114580e2030b1001c80b041c1800100718038484804801600c65400540e1840240c040302c42610521099030851100146403440e03000c010954a8800e013484d50520302203841e4061045011070600381954803000040c404c25800000d0f120584404035010340c5010709045440c1c01c50b02400c4c42c0d4502507500c1061072021a8020b011070700d584070320540d41004042e07030b9041c003501085d5203072020790041201e0300e000c1c01c10541c2255052051030b00011800000042c0035411001448500c2c0d0b01c0341940810b010100011703501540b00b03402030288103410750311500800031150826600340f041880c080c0c15018480b00501e90801d1040082d6980c0c89609901804c81100060702c0604c060000d51151030009004208242820048180d95100c9820410280c40f42e550075a0f900090314800480500113331800c00300b440c10782142031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 877560485 1250 877559235 877559297
    0x30206032a0d061512180204050705120a0c0504061b0b07050306011b030806130e030c07080709051b03041104050a020d0b0f060a08100f0303030c080a0507 68
    0x103865141681107200e520701c0901102810000101d4200708507030350154001801d2101c51040c50300310469400b402001321004280000c946a615500c62514102d40d41109a40c014100703100e1440d0000c4004c21560004484000c020000304c0441d01910aa1240410b410402d0303d9441c03402e401e000701602c000e14424000100005210850b6002030314802032640034010a450344c50300e9042280014009442001c403044030341107910200c2000c0b80e40f0807081500288140e40d01c284a0510f03a12000c050070310800d900c565407100260148050b500001c500088400450071340e40c0c0a91524036407070984105691680340c20706c078040051490914100115001440358203c0102003e401c80401c06580c411603000c0b0480e039002c1406981540300340501c0308882c902720340c0740540e03942c4040082c6075805800450f40410a4600015070721481840503613001e0400312070385182c410303034a240040181c10a203007100001181c800c0803524999107801001c0c090b9400c0d48130304080008941c61030000307001c8241110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 877561735 1250 877560485 877560511
    0x21207230d0504090c0305040c05060f1b150f0c12070306030b0f0709080f0a08090105120c07021305070c060e03130f15050a08180a0c0b0d0b100903020603 68
    0x1003081080840070a6129488040c1c680d89002442003c071804d01400f02d09050070002004001002a441c040c180c070011544a91100c40c80fa000b08402c0c042c42c0b11001030f079070000c050000124000039402039040c0302410310003010394626096901d880d000f980c000c003000d1020311600d00001e070f40418180c2d00010920340006d20315500d8032801d101400c20344e00c281c00c042e4550144200213500c403800c0000b0304581c0c0005d240071000c00c0c3d1850fa035207501250150400402060303c8015a02c1101296048400e058001540d81002d4002015aa20415089125402c1c0c0840c20300b9421540c01398601c11221503c1e034071656017141d182c00c07000d44203002c02b0000a000400400104030360105820300030b031020381c003c021501cdc00c102d10048801c01a081410511500b030007210261644003403101d500034807a40345155021178201c1f0251406072980f0700107002c020942c00c0894079203c6d00c00541207640c072800301400b041981301c0c1401a0705070a040031100050001c50f0920150030032400843d00000d80646003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 877562985 1250 877561735 877561793
    0x31509051504110a0909022106210f0d03060e06060702180c090f0307030c180207120c020906120c01110c030109060902011107120f140d020106060f021207 68
    0xb4003140c0340c1040c01e160700d100100b644580d0307640c0501c01c0030103400310303440440c0381c2003a40d02d03a200c0700001c0048a8a05088000c001003050700c400320258002800601d2026254541045c090340f290b10781a5660700c2403140c54454804544203005242c00c440f60124002910b48801d02403140507440610182d80100040200d190083c082c01e0f4110b200d4408800002e88590340d410811550400704a1030358440d6100410510100f4186803900c0102d800d5035107a081907001d000c000c0c20181c02a0075000d04000101030010130b850f5000300503100c0710b5208591051880e030301c0b14204506007240c460400d000e98040c2070304070f5140d4098650b5036404c00100c000c03103418258510000e400e40340b2098085404c1034a905181d0110350704010000801401180130b03201403410100300d0b0010303113485580940150440c15400701031100360a040030b490074210041d16001d8114002c0a806812a4880e100010307a01f4a22440240d10101c2c6101c0419151000700385030035056112030b50346010040d09100d9403a101049 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 877564235 1250 877562985 877562989
    0x904060b03100608070518150d050f0606040b06120402100c0204090503090414011206180b0f090d0e0102061515030703050907051e0111100207050114070315090515 72
    0x681074800810280110b0f805081480440c209030503640514042e07c03030f20011602c81d208040c505a03101151240315007000700e4400000328592040300000d08140100400c07064512000b04105105410566060010030b0280080c03000da0b00c904469500181d41c5031002c20014540904941051092450600024006500000c084811800085075103900001d40c07052071f820180190a140c14001c05001c0c0e403503140c14400c0c40b034100310721001000c13543c6e00d81c1c100c0304246c0f19900410038142c004060311094a40f521440403007120135640215035105200d292100d891141c20201c0440d401a80a0b003d40e03210207041060302c2c1460440e02d9440502c00b044400801042c0003d0341c0301d603001da5004102810214082401c0c05826000b00f4050b15141d009540442c100b4140314040c40d0742843c04000c441554908503003000240c3c540c0d41000b90000466500b07101054105c4101401070010251040c2c58410702502110343c0144081200429020208003914007039004a903c41703010400d03011030f0624900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 877565485 1250 877564235 877564243
    0x71b110f120d120f0507020a140a06050f07030b031c0503250c1103240702070b04060909050603010b0a030b15041e0506030a05031903021309020c2503020904060b03 72
    0x201c00400124140d440400030a8a4010000302c0c80d40c6010802a07030806d200000e4032503a801300080c0049401c03507007162104c0380c00c01036903807402e400190030401410068003501c0140d05c10f844000c006820045001114500414030703450084400b00b03600622403a9080c2583c403038000615030102a030401c4440412690756001c0c07000f40c10b159a80711059003140c0d01c1d100c0040c5001180603030084c1d1014200642081803e030301d5454460414500085660f60781c02e040b840c0081c6134202d140003c0c2c010400107a000d420100c1e14041c6c905642c414030507991010249422921380d08100e9038030803e10385040011a1001902942200301e0114040715501c205021605071004800c8a40244409002240408050b0702c00d003604040b048018104e00020360310740315900e01540c03080035032000000c10042412400380d07040b01e4507034000c110580c0e2155942c2032840c009400c81c9501d56800e0040700354103c1d016401c2001644245411000d000e02142150284404001c00078802c4450a0b500e210560f01950200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 877566735 1250 877565485 877565503
    0x30905071d0f010b0a02030901050d1515020106060509152101030b04020a080a0b040b060a1208041d07050d232502010e0c09100f0806071b110f12 64
    0x20580a109003442010b4000c002e6050f440a002c00006000380c1c095542d0120482d030140409280503030319079030403841120080044c03000c0c0d4108046040000a141a42d841500290740200d400070400b080c1d541d0800d0340d8910529620320f60018a8034020f0442c0d41255000d00030920038512000c00300070010b40c50790040307503017a042515407050300c2c0100411858003051190192142102030450000c942ea00d0600c1c040f4003800042c1004002800998213071200304080780108200c7c03001c0004c03201c0604001c5195441030040303080c500a0000388249945502c05c1c03081c0070712003a503125840c1003d501010001082caa214280013000002c48103050301d4144410349019141e00c072940618001014181103140414840030000d5904088038a0039164000c00d180d0910344082e039046074603a64185020380900306540101101002050703010400304c00005601d80303e08056203c00304e481071155020401030704001c10003029100d4461001102c0e00b0300001c1742304440e402070181882d43c0f414461f60385c1001451 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 877567985 1250 877566735 877566779
    0x5091b04060207050a050a0501021504020609060d0b0405091f020706020412060c270902030903090907080a0e0a0209150307091a030601142b06090b0702210a03090507 73
    0x360f8014842c40c40d002090400824080fa04503810728a0000042c3d1a0104407500c031460b040108000380a540b00c10084070041071000741115500c41040125500606403006000d015600c1c003400504070540003d80a0b1b07402070308402c0411a0390318044071401a5000d940f0848040350240400203914202280b07000c48030307206d450013090100004100606007041c10040600e0700681002c0358600440000c2c501042e1288008050313640d0341c0794007600d0300c0c51207009061500504450200810580e0000071980224080300082c42118004030049507510708800000e94044101000308008011600c19100d000f10041c0946100f181e488600d03404440c0855540b12072910400500011490180007190140925220000d5091801c1d408101120302c40c10074040c00c61158242071603010318481c0c02d03071200c030f030700a006000303003e81c0345070082007a881070790421b01600c1841c01c0c0c0c1c0054281c014094101809060846042c500d03031920403405001820020303034450140420104406258a402511200c44 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 877569235 1250 877567985 877567993
    0x61510051210030201080f150d0309030203120310152a1202010c0e01050408031824041715041b030803040605180f030d02090f0405070f02160f05091b040602 69
    0x1d14000075000c40c0001f04601d4100842034100400314003181401c1c3d00b40c0f2820b44248004004900c2c0c143e840094940010707605100d6041c81c0c0c412800040000c520421000901d04003042e511000d00c09040c540034a0000420240440105070f0b0315100c41c1c40d084015240320000708030301c0c41c0e02c035080e00d00040d0f1500300050351500500c90202d070f01f0909190840000780f030410701e80b614180c103454072800360703801c2441184480e00c80d141255440445a0a403c520042d102100410304460f02c0510f07441441402003000210b003079000400c1300410601500540844015000d41d034594a0850011a00094230341e2460001004804600d0380400f07140325134031a40c0001a1070820203000d140307440441b10a01a968040b1125061a03500032040e681c0c50041c84074096141c00580d40090543c2d40c00d0b50807160841e203400e040101007644140423110404058082d60b141a0740c02e8040b503500a0340707010304840702100c1e035410003203030600d42415a0300c08048100b0010070b0070104030b4040301e82d201d54444001a80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 877570485 1250 877569235 877569239
    0xd1803020706090501090b07060e030f120105042f0f0a02070504060e010803181f050a09050105090d0b042a060908011a01051309022a061510051210 65
    0x40c040040d00060302443c03c1440c403452900000034074034070f07050044100554010070500200507041d0014021442c4d09400d81c1d48494190303e100e401c40d00b0220710741700c00d01114030000405040a02c5440309480c200c01d034072140306061540c80d0a00070482124481401d608022205d00140010054025a5207070782c0688a150305c2d2800700410b603480c03a00f0060a00c0c1c0c410004002000c400422503008223060840742c0c049840040000344025100c00b8001014245044003801c0182d10100904500c40d00791500c051703d80e1030786d004481c00c0c05241842504101044050000b0401c00c0c00d02c00c0c0c1c41440764042501c0e0407075115450b401c60b054050040708540107104140b1080b5089580300002c3c0c800c0e40d008102240d02c2003a043c651011081c4007a0500000042d03401c080b0307100781101d2014116060055586103440740300780d1481d48281b000592203001520f408507081c3c40104503a40240c1d00590b00843e810020020440405800c00c60107060000c00c01220704442044a01035104d82840b031444880cc41c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 877571735 1250 877570485 877570487
    0x20d060801142214120403030318020a120f080c0f0712020109030f1e0c051005070506070e01051210061202030402030d1112040f0f05060703050a050f0d1803 69
    0x180c0408840500e5403103207020840c40302d450140d00c52030f10384118035900000400741070400304035000c100b03034401c140241a101d0201107280c00082c02164030a540410070940e2018038040e440300f00c03a400942c0440e07001d1080102d00012080d6440180c0240c10f6007800c0c002c240d80319840c2c0c0d80185402c883c280c00084201c203003030f0820320181004221041d500f09d000d0600b40d00003011424107010040c000503d0019100038403522441860001c0d41c907009400e203501c26400d04108400d040c0c41039a01c1000d0440400c542c00e481a8160344c0650303489001404952a942010ba4107001b000301e440781000f80a01884082d00031026910b4050301000005400003402e240340245011084020f100310540104240310060300e0004094a4013402841c01800702000003e50718241401d24403420356001f800b00340031882c8008848018201c90301011202402d941c1d0394184411801007210140c040344d01403140c03203c0c1e00e000f400108441d48102c10481d20780164010a401140c0302c0d0710703512620406010941d4105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 877572985 1250 877571735 877571741
    0x20c01050f1b0f0d0801030f060f06050607051e03120411041506050409140c0307030c050c0f0c03070905010e0f1306020c15060405010f14030114182802040c020709020d060801 77
    0x2104c0c45141041496043d80c807114000c481344080109074070365540600b902810181c1c0100d0261600510841c3d640b02103040069903800200040380c007940c407102d860b48101c40004101c9039000a500e022001c0c0740d0396a1a440c000d61040c0b4034060300561a80d402025400100d202540900420340360720345c4445c00c0500b1001180c010407020407003c0002424070180c50006000d483d4400b0b000d14000c64080440351003110a80560301c034480c00c034030a140085c2d203810400b213130a8854030f600f981101c0000345d807400d030407040d80e40c00c0c8110104041c12002003002400c0304400d65601404803855080c2004e5507940307900482c0d0143c01a8405a0084488039140c0503011a07002e40180b0200c0c3c4c01c0c840c95040c0707003890b14140f1403840740945024024030440c1c141d44082d04656a90380728054203051900d0007a0500302c1c0706424194100d054010740030b00b920000c0c11021540e41c00d41500701440207081d9290b0901c4024400340c1c1c0d454046d84210b00740055801c0c194001402030641c1e0800218030075150081c01425 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 877574235 1250 877572985 877573003
    0x909030c0c0406030f080d09151e090b1b0c07091b0e030709020d060e01030b0f13054b07080a08031302130905010506010e040507020c01050f1b0f 64
    0x4103900340343c020400b1460a2444089191300051030543d60090445440c0042401400c0280940705c49000903148107407a41c0100f490b100d2841d000d128881d105900b840840d89510b000070003080300400402d5518801c103c01d82880750f505082c55103400c52002d403651038003000750701c091419603c4801c812641c03500d107048001d8800140c141200c082a00d1400070743c81c0d041c240102c1c14040d5012079440d0f08001c5a4100078001d200303404800e40d60f035850781481a041c2c041291341c1e180e0b11a00c01c0c0401d0942c41403100c3c036190b10340c22101410100f00080c4280448501e0700ca22202d00a0000c10200310030ba01d111080e00a41074a00221184005110704d0241400c12030b5125241c0354014103400d07408115a80d0840382e0003002340350090135400c0d207840040e401c040014400c1e50090301d041c9a90041100550001d0301501d82600c800102d007a5400400050310000c664010058201d802c030802c0c1940148050444036810052641c04c10400000c0143c8003900349034942c07802e900c40c0b20a1a1803580c180203030a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 877575485 1250 877574235 877574239
    0xf02031f092904031d1503010303080f01080a020607061407110c220c1b03020c04051015140c121201080106061d0a0f06080a0c0305070f050d0b0909030c0c 68
    0x2d0850358410307105426000800180a121890100c42d500d13400e0710207000c1044130700800300880d003030790a2120403258200740000c81c00304078044081041c0c03000c184a428101c840e58401044038007026424498650001030045981a4603000081418410995414804c0d0b50654803c601041c40740c840c40d00c0e1800c154440c6004811541a1040d1106101150380070000300100109171049550790850318521081174642c03d10849100e41420990f0103c0d05841c14002203d06025035140c40c128030400740814441c1540e025607840343c4008050007040540f0048040b00c0032035040c0318056a4850070710b059000c404110120004141044903002c3c080103000d00114030003003011034204800a02a00c4e040c502c02d00301003401444402035961102401c02c0030700180590100002d586050240800c00295009a60030b418000034440c0355100c1e1041c1c4d48559000c2d6180c145145540360700344d0f40f5610424983d450700e82c841c0f030b064230a40c07504541a8040c000c81c80085946040d5800c06504195000800078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 877576735 1250 877575485 877575533
    0x1051c1a060f0909040507080d020f160b0a030c030f050109020703110c010f0c300e0906060301090b0a0e070f0f0206010b0f0307020102090a1509090b0d0f02031f09 72
    0x1110100b034070058030003140d003c1c1c1d505042d54603a401c1075490800c040e88298501d208000881d03003055400701d01006015089000c96407100780700701c048644221103025110a00b1411700c00180b4051098115400440b85410009200010000c200d030607640709811002a850300001c00508166000001c29244c1c120000036050961280c3e000030958400305568004001809e000c0c6800d004590a243c00c1c00c80510780040307449646119114050307920249058040741844d00482000d0400c282254499000203022034070307507800c3c224014001c24a00081d9a04101c02a03c049840401174482d10b0003000c042d00e480b42510300400e001050028202c0c9140110341000b00104907807000c0304152400f0080b03200c1000d480e640e0f1540228024010b0840c5264800c800a07000900005244851480045583e0754955440c0d01c1c0c240030303400c2d00d60100015412680c1220030801082e0303001c1408906038401000d0f240d02010b40c54070ba640006005800504603666903507a01e003001704090701e4000320080c0c55050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 877577985 1250 877576735 877576747
    0x30d03060e011205030d0e06072006010b0a020f0307060b0f120c04050a0f150e1b0306060a0512010e010e180607080405010b03070b071502040f090b01051c1a06 70
    0x14801c01410311a00c44011403516115040081c24010740b180317000c00c040c01f044a18100044140e9800043e218100840d00c400184200e1001804201d400ca0103503600801e100c0e46840f4000903154000c2d440041107001d010214103000c2c1c1d00b40010404907010300400f03d1100f01110400010b02100000310740b145c00c1c4e00d50b02c0c01141c4004035458120310401c480004140d9900078ac4000640300c4029100c1d6920318110100400c1d0410b050450140d0f5224050742942d55201070706008a400e0403807504204000500015000c1e00d80b1b4801801c60261600e402410050401781809000b002a04094598002280103000383e0742142d000d1948011481d242031007000020404548402c400780001b401c2280100000b414410250008246500083d08070781c80141d07240094845908400c40440324007000c04100d0040010071700035a0141e803450918010404d207002d01050040c1505400581030000600000d410300001e03100a0040c04014078020078031140140001c500c40003441c510901c1a0824070103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 877579235 1250 877577985 877577999
    0x50d03050409052a0d020f04122f0f060f1201090c030b0604180605150a1b11120f0123090109110409260a02070f03031d12070311030d0306 61
    0x45080c1e405000d04d0159980100d80a0788007034480c1c20003403540030200003000a00d624142d0100d4040c036000c1d6544c2c120090210050a4180740c0c000d240c0141d001c000b40d07a490036860061000792034080b00414051801d8100301e885812504000950004100300700c0040048030745a000e00d01c0c58811900d01001074103545800142ca9004500801001d0b20a00000400b00312481d407000028140c010103454100107210411aaa40d1090007440c000410342c0e204000065601c40700f0610180c0d0014003090f14000900074882c490111100002d414804c190408500046c01e100c0c5080100842c220501d40819900c83c00c1160076001d004440d01d83c1c50400e9200200705207031496141508219404202d0001e41e0416014502d10300c5e99001c441d0103421082620f0b10001d10052190140b2a0280c842080d5650700629201c28075100107030104811401e2868a8016081c030013610010081c0602000100c000b002c0d4a4072000350809c803025a000f1301030980034602000b4140981c1c40c545400d101d00c40c20484 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 877580485 1250 877579235 877579291
    0x1051806010b21060f090f0106030f0e0d0f021903020604210c0822180b0105030114040f0615080f01080c0a14060f12040c090908180109050d0305040905 67
    0x1c41d00d0070781440e55000c604103656820405c2000540180398054038203100c680d01c240010300703220b4500440e01d000d1418111400f5401180541140724014007180d4032140401c1d220070301d00790491303c21405003144043c0b500b4526101b161180c0d00945c0103000798030b40fa06d0141d05070304070703811540140683c5205404080c1c2c0d00c0491441901d030b001074150f8550101c1e1030041d4018590014110010022010110b211100c40341d50510560800209009070000e160040d12644800e0250305000c0c500299003542d2030403d900424000420b08100150035651072001e84d21400d910480c540000da8810244240c0d136840400f110701500185c009000170407880c0380041ca4012302d5220b00c22403410308825070714080c1e841c0300998824a15883c00303641d950003001c5111030181e80c00c49044036407a002c400041044111882952100c0e940f0218581c5040e001c4804d0b00000e066a888030703410401034030000705498980d1070101140c240f11b51074031900c880c00c200140c01503550003818000d004200e512000c10b5544006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 877581735 1250 877580485 877580527
    0xa060332040f051f020306130509030d150510080603010b01020c06072616050d0c03081801091704080618030a050a02190b09010c0e060f0a1101051806010b 68
    0x1000c01a02e4411843e000b07090905810700143d00c03800e0210030f80000c48240c0c004600c41d14003142d03482803070018150403008945050b40e580c2c60990050103070740d071a40800e900030001d04c4004596000b1007991400010900c001d032290300800030764581c09002d4281000d00600101070002d0020380174015060021405074020403c0161081c0e102045040308110030103180e20101c0c9050225030380d80d16020a04038070240e0000030440e0180701c0d00c40004076a62050000100e0690b040d6030300449500c40c4c0c4201d080710b1808211003143c0795602c482110000c1d03010314245d241c44a41c200283d071254030f8041e9060500308000c0030b919182108402c02054240b0200407201c25102509010b074440160390412890400b5200904610311400009002841135a52445110386030210003401b501da035030380d4122440301504e100e5580050007444000c80c045144d00c098807404040346002e1440041200748a800c2d1902600d101d140c66100c40e0310005111030601c1700a02400300c403c00e60385040c001c500900360340381c1c2c20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 877582985 1250 877581735 877581743
    0xf27030c130f0b120c01020d080c04060f110a060b21030a08101d180a030c060b01020c060304080a0905030d0e2e0207082107060504110a06033204 64
    0x360b04032070410000c0c0d8410000020013504400d4000f4040d07003915580c513002c51031103000d84030786035505100ca84241e444510a8014408880c2460700e41941a500c00111411036000c0c05180335a5450700401080030480442c007441c4c001c41c800007a42c052103030602400c035202100c5a84d0008548140e0000011200c1640161a00c240160307600c0d5400c1110810b5600105000c202d42d89040801401707030ba00d02c5001e100010580244140f5007110295100d504c0e003030050201d0005040b0001088156000782208201801a03d152090150000340c0c40e5104460455082401095603180140d1000c4a0001340600b03400501c484118148050501135006180c20304c90748161441c0c0c03800d82003100101c0c0107403a051403061034000000c140039480b01064090404c0910a00100c4a0b844a16000c28244480e82c40c102620f060641d0b00c500c005400f000f0070980d0b414200e1201645191100b40d1503034010900c80d0b50000d40c0c08a41300004003444100c25020000808035407102111034416003100307400943c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 877584235 1250 877582985 877582991
    0x801030219180c0215190f15230103020f0313060603021005030901110901141303051c080705040b0a051c060602010e060901020f0a0f03020f27030c13 66
    0xd11009000c1098180d0040040760810160b20007103598aa08861001c4015400780e0b0343d03007180400045204403003200c80a00201d000b51400e000c5608990082d1419800a00c004c18001d80e0301074040268141ca80c4200241c0070001066000405e17440d15440036500c003440d0542c40c0203200700c418507542c00042c0c050810700d0b14458843c41001103942c09400119400342481058682e0400007402c1a00112001c5001d5402d08030700d04001c1400b10115010304405845009040f62a8544903000e50401d40b282c0b040140c0c40a40803020480800140390340c0280c1020720041541801c0d80140b4048000e440d0b1014083c042c03006001038000714060324100082880c040e0746990114021501c40552004206c40d418580000491410b60642081915000302c5007121184c1c0c44a0b48114200d1003110b2058011020901c01032244034455010441d403080c0619003d4101118010806000d5200314686d0a1000d00d8079404900031441425861144808034060000f8a4070240443c000e070351030354014008a65 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 877585485 1250 877584235 877584259
    0x40201051620091608130c03172101060e0d0f020415080f03071203111201330e0105030615030c0432090705070b101806050108010302 59
    0xc00300c0e4510745039802c180300181140c1c85034a80c10b0710009800041e409515500f000400e0219074440552403c400d03036840f595240d8a404e22264850140d01080b40c504c96074400c004045240b65071807104140e11895035558454051060007450412000304070560050301004203d6903800092829141c001902c0700c1c0f83d03540e030502d44a0640c00d0080c100941c003907d000300d1002451000d40000781558500e20803940004c9840d02c0d000c1c4c2d2401501c0009054407100f0440034203042c4650032030820b42218801450600140c10021050071200740c108020000d050381987c06080c1d81e468a150226182641c0504840080d80d00104000502400340f8103210000011440c1341d11401050152031380440c5030140c503403c01081800c8580d01511030308160084c100b01808558407400c80c61151000804144854442924184140740d4001002c01c4103110050040e80003140e0400f050512800b44400c03400182c40c1041d8400115400742203040740c40b00d180c12402d10169800c0004103040d684c048a00540e44070b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 877586735 1250 877585485 877585507
    0x30507090f021c0b03060915011202010306150c030f080105100e120709140711070608040602070c1e08070602101d010e03030121031407030c05070f0306050f060904020105 75
    0x840b6800181c03005004282c884940c0010035404003a41c007034105e00307807140c40d10303059015940c903103124119119160800d001041200e601482c145100c51040c100030401ea80e40c0c5101e1b00c8510210720800000c2400e000340502090f60008056a8501c2c0908000c9029410310700401c81d0307660f607180070105014141381b04070f6003a522010521590305041d8111030069803550258405807844110651940d0b9600c0041440c580c011022000c1c0c0b5138081b130013421258a0580704a40a00d4081d1094425a508011032008112510460009003061a4890b008181c6041d954180200c1d19404001076070072100c428401e007580407071000120700c200314020500300041001104101d03400b00f421445580707403d80c85c182502020010f181214554422070b020082408119a102e4200c2207004000800c82c0c01c080c03100300004d0001d032100c0c5029181800d8910115640c1e42e144c04210b401200e043c40000d1801c00422040e0b000305a0b024900c02d82c103500600740040070072070055020704020305002010800603452 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 877587985 1250 877586735 877586737
    0x3110414131e150b091c1b09060801020304030516031814090f090613140a0308100603110a0813050109032c090c0703020f010615030c0f09030602090d0b1e01080601030507090f02 78
    0x1a4122400310105407c440089000031054441c01c102541404800290682c0620950f4841e41e0151600c07842c0c10694501070300104c040c844210f0502050507100030300d02c2035100c05807010309960341301c0a510340341c00d000304001824002c044904018001d810010f8205010481a0f08180311942c550a081542c2c680143c1030030301e03601d2003803e0b0b1140352541010700d54031141c0d00f8040c0d40e4040540d10302e0f980301e11080b000c0d9150784807002d458842c10442c502586103c1c08183e54000c44d401007003400b001441c0e541a0a44890b0300080d000285500d860f03405020059840000481c440c00040078200c0070740010502c410701c02089000c4a10000c00c0420600d4000e11103107022103c00380007000495150a8004003490f000c1104000203840c015450300b80d80c0c0900000c8000110903110030301e1840c5181d450502a48c845580b10741c0000c10003107000700180c903202d44035000b071120b100e4000d080000d108103294040d0050303001c0f0300249e20810042010840108441080d45c0045e14085040d040d0740c150040070b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 877589235 1250 877587985 877588039
    0xa0204020c06010e0f1b1e0a02100b010302041a0c030c071d0604020f0d051f0b0d1a010c0602090d0b07050a090603110414131e150b09 59
    0x98000a1030680300c59000c100d95059807014a406075254540001151030000f048070701c6008032440510000c5021100c20140145a004118407031120990ba8000001c40d0050720850f40035034407940710001840510b000b0700003044400c0c60b0440c2803502c0c0c048047d032001c2046c0c800d42020100000c0340003e4620038803c5505200a08040342c414995030102c4d001c20041d00702d00b0096032118800420342e2440c06008481c0089980c0051509241e40c00e61544010000a0541140125010a40240550003501110007000c001b6802915240300d040300030309030f40225042500b9400d03607003081403542c0e130000700c00c0c1440c503000307a0b0050311031104401240564814a0703000c0c000442c083c04120405070700000a01c003004071603456082083d9207805c00e034203460300c070282d04060480901082c050422403002a1407003580003003460900020303884844040716440d00c40c0400303645c10200909484d07406806a4061101c0c08140d014020b4901345000da018014032502c18801e016208031a2000540400b040013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 877590485 1250 877589235 877589239
    0x20c0111010b041805070e10140f150a080114090f040602040e0a020901030b1008070f1808010504140d1b0f0c0902090a080c030a031808030c0304141e060901020a02 72
    0x20882104c0300310790f201c401c3d41c10301c110b90a118050000c588840c401034998010300403803070081a110704000300d0400500c108040a0b40001903078038241e0003a81c4104209400703124100000d541c60402c00030080c00b45405130485d071001106025954034a46910750065800304000c0304115480d104d0b850254080d1145074842c2c400f444200c0300740500781305664010708046400743c80170012482e00302c081c06240c0c0d840f0b80304100445c0c05c3c01c001030046c9008007818000ca17a05440e100c0da00c0b0094040305401c00c0c0d00d58000f00305a80d5104200010000c0340024003400c1802c0c48010001c51564400c0202001c0d242008040310300c600e008044104038802c0c1c0242c50544d1b002e4a403950183c3c5803240c210003500290b411501c00c118075000010205404030300c0000001028018000b16603080d1800d0301e41281e415030f000c410319800140012071010500c080c040e265450405141d80ea450850008d00d6035440c548154401c07508445903075040204003903142e120280a941e82e41d02c410704540140e08180e08528065 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 877591735 1250 877590485 877590491
    0x3050109060b0405060f0f0609010c0614060a06230a0905030f0a020910060207050d031713030215190f0609061d13080f03060301180503030403090504020a020c0111010b04 75
    0x1100300011500b011000075001e94041185a076480200f244c605142c0c2c6000d0341210b2040051a09820024000d21541a041c1080310210015540e40c00c200d607480c0ca4001180b4004400f07000491030000716000082001e4034004840d0f584084454100246c1c01e44440e800c0381c400103000103101d0040601c90001d0a0080c2900c0840d10607144464030366043c0142284501d145a0000350404030b555484000e84009a0080109504140034414030414040c0e0503010721000b0040d01601d49094805a4428588000c0801d83d881e4030340b5001e890b140f003100d0080c156594032020031402240200f24590442a1060041080c0ba542d620740002451550011405582000707002f08050300340801188003c80e020b541043c241c0c1c0c40d030600c584101000e610040080074100440c2c2e0343d440040c009182c100340c00900009809101102050360043c1e440401c48103a000842003101b03050308080000c00500d001c1d14103501d82942920025101da0030304007060b050205088203071016100035400708952076400f0b4020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 877592985 1250 877591735 877591751
    0x20f04120215120604050601020d02100b040207060e0a051501050d030e130e0f0f0a050a230a120f020609030f250606031511030118092003070815010b13030501 70
    0x80c00350b0404ca5003036006508040105125510000d02d142c0783c0b04666001c2c20401c41001100c02c064000803522582c820303000e03c044800b0555030310a55420031601c90045c40e0b000141c0c50b201e030602d25410450581e400b00940104250303154500f0240290740c0c540740c05502441e03040c00280c03103010300304408000d0038038100c0010104040041c80c603031441c801d4411181c441d1820b100c1c00c3d0751002004401440303034001140e503030f0006d210109400d02001940b4200d140b511452051985084106d2005442c3c2400304091440303541e0300058403046103080361015040700c0c90f001090b16a00d10400303407042d500c0c00001951858000303040905000101c12614074101c1c03950300d8200000900b00354001610320240d54403125114108610841103000a0b0030340545c2960728104000c00400c17000e0340c00118080c0c40300e854000250600c28035140c1401c10202081c0c2c0341024000b81442c00c009500005041c0d802180013070740010024510904640308000c0f49a900c0c820740c0d00080040700300d83e2008007598203000780 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 877594235 1250 877592985 877593007
    0xb100f120923030f0a03090c0905091014040c0e13020904120f051305060703090b0a090f05040b2107051f0f0c12080a1107060204050f04020f04120215 66
    0x2565500000b5110300600c070301000e000b56501d0344602d10450246400c20400c1072130301c80c0607400c103c3c1824050f20182d044140d58a100000341c6908640c410707101d812183c440841d1256501c543c0c003450038019010040e9141550380c019140356203000d40a00c1c02e03108000200445951026003a050764042c00006290a051074003408411080c004000820004181c50307a10504c00d800b501c0d840c407100000c1e02801490007003405190752211106404000320076a000c154400090000d08102c010780d80c6038625145000009a80b1002c00d8100310301c60741c100748001d00b1a5a07004565001007400c04074902c00ba0b035580c1600d91030005107901c0b0700d8000c1d001c69204a440c03040f010b40c050079039a00752a10f0280d018680e4084542c43d8a81e20014600c00258408020311486510380da030780415030b8600040e40d00d5110301d150480ba08070170401c40b03072290009000d0184e41010600420600d0080d1825070400c01c0c1d80842c4803d0b4010782c001d001200b1003c0241754199a03a964640f00c04485503620755540341d0b01485 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 877595485 1250 877594235 877594253
    0x101a03061f14130e1815070207090f0e06090327010f05071104050109020918060a051e0904060203070315050907050a020a050d0f0906030b100f1209 65
    0x500c0034452940101205010640d401c0c00d4182030045940303140c2d41c005061000140c076000414000f1880010b140045200410700c10814010002e00d100321180c2c6180106092500708503410701d1590050940600941580005114040d50040a004a00c94242e03401c4840201642d1110145510036281404889100400105040040c03d045003010701300c44607800b48071120561415002030042d03c10703a400c0911803c041d2859501c03030000c0305640c0e100840010180c40d0213800c0b091380aa800520400c02c0d00d003410340b22080c403d10f658001450300d010400100284980d00c5124043c440018506600c909050410340140100804203919401c050403c00d0007074104031407401c00300c3c0c54a240c0680c82c60701d80b25605d0440b600100301c00250340d101c903070440d05908a64424025403181201c0040040c1003441000030515072940d8803d07141e19080c500515002d041c2d030109060501d801c04401140d1079122001d810140d1f54181100320b001e00d220200d65400c5180020042240f500c400e030020440f01031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 877596735 1250 877595485 877595491
    0xd1107021c0b1b1b011b021e06101205030d0f150e060d060b01020708030c03031605030709090504020622050907020c0607020f03070b1201050102060709080c010305101a03 75
    0x8508080d907566009000302800d4165242c1e0652502403001c140404c40c1c5000d4805032000113400424a03084607160100c25030310350021903003d600400d40300e00103402801c0c0c1c00920810000001c1502d130520042c3c034413040c441401380c1e60003064100840d00900004004480040741d94110802051008079a020000c0c11007e05070010396448160010b0300c0c0ba405041180540d01c001c0c21038150a03019611140200040c0c000c81d41503000e060000a2803d00900c058468180840d01540d628a00709a02c4241c0c41c41024501c8180304041c001d009400303610520f400141c0d121003000240a0f00c840c00010214080c044a950110b04011400c0c1040c0c5480d035042401c8920644010b03665480321042a40ca400c0308224080c1c00403000c0c49240c026141c03031058654640f201600342c400958403500f031b0400d0b03a4082c507c45141b44814400400213541c0c100201c1c0c0e0310146c50b1400c0a03c05081c00d140c1038460a0000c00c00b810180c0f200302051400c0c409400001c01800031200e01c0d540d40b10300300c07141003440d0011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 877597985 1250 877596735 877596743
    0xd02130b0c07060c050c0909100204092a050313080f0c010c020f01180f150e060708011a03150103155301020c07030f050c01030905030d1107021c 64
    0x405400201c290040c59502086640003002d402e8420206c0309001c0c04800c02400c4030050b1188240c030310158500742c40100f001d4510003c01080005000c04a414551a1035504030920724401d25049001540401500d4102c052401410600007071403c080e6441d00602100200e01c03600000d111121150540c0b0540308808240c080c0d55824156411071422614506040180b541540486400042c1e081d82904500340c40740810300251131003003419504940285500c01000c1d800f540c10f101600d90051100740c0100000c181103414501c03a00d03c2c030900790001034036a108402d41800b030031480d40e01a4000b61901041080880c00303040d9030b90131444101410056030310a0082450018044400100e00d21207042681c036800081c0d243e126655100d13581d03103502d842030035550920003c0c98000092000200443c02248000c038ad010302d41c1000c2d07040c84003041e026414503180090443c0014004029210303460070f5090000780e4481c46400b000242c0c499010003d501612040480c442142d07900134101c0d55a0003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 877599235 1250 877597985 877597993
    0x218191b080907050109140312030c0403020a0806060102030904020927160305010b04030209061302040b04090e0c0a060f0c0609060c0807090308040510030608101e0218060d02130b0c 80
    0x3a105400362102c10f28091a80014a10368007400101500d01c4002c6140c40d000d021210b40082810128545410546a841c840c1c00006030810640c50080710381070282510002419183c184400003039581c1c49083d82c003600898003c6500d00865450500b005a007903034041d0725904085100715140703580c0500b2943d240d204095140b800300f9440c42840740c02d05a407001001c41e450320741035030200420300a0003004294045001420619040c40d1400a880146155010030380c5903410400c910042e545c0c0501d0b0001e82c0d601420300d00341c880d6a02c1c1c20001c11504c072801d0000d00d100300701004a540c4120300d1000741c0000e080082540412403568446000000c0c2540ca240c00c42d01d51640803580031215110150521800f800309001030302d801a60780c0035090070740c20005202a034034040d0a007010200400c5205407640c0e5041c0203200d00054160890290005004515046010650441d601a0301102174090000801c600081410a074111501c00e0100800c841d5401e03902d40086070550300c00200f002c62409 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 877600485 1250 877599235 877599241
    0xc030c0f07120506180f030a091d070e0d0507050607051506060307081b0714060a050f10030f0f0812090d030c12021309050112020405130218191b08 65
    0x2100c108100c0d002d43d0b218002d400709071220304000c050840000c103820f106000e1920b01a40c0c1d01020002001c4040040c1c84007001d0300c0c540940e03d1040580d1803031100c940205142009011a40301c001010307505000c0325154070040e154245503103022025040913400000008501d0284200060040922004c000b941c0f0344540d51310040c020395000c10b84000000c40e4008003c40da20b000d00c03030044c4140c80d04000c0300e90b0405005459040080c0540ba5803203059410040520021203061700400d42d111150001450045c180042002d225110510024184036401035824040051107001c5138600e03600b110010f921031240c0a001403005506480b03004081c400c0307100b100c02c0c1900a0107240c0c0340d248280c640c504040d1812880d20081d42c06446c6040c403120500102091407045841114042d004e0f03a100380c00a03c480d88103000403210040c0102445414101007030005a5810075100304842d24601609000d0321003403000c55145421815200220b41804034401240b142c0080400d2445820380c1c07030080940f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 877601735 1250 877600485 877600499
    0x1d011104091b0806120109020901030f1a04110607030909060e060a080c01020a0f0312050703020d06091107031809140402090a1a0906190f05030f061003170c030c0f07 73
    0x1032444001000842c00081c000350700e030320704503044070911a241800030507c1e0080780c0c005588160242c00417201030f0410401c410900c002400f6942103061601500303017160034181c9030a03c1c0e081310a01030710b10403070000a1000070503100e0b410038002088112003c0c85207544a01c0710312404e0344201c90090042c00f12980005070181c001619203186001a00908074084460b2a0080407a03e920016014000c0000c0b459841c05041d01c074091040c141ca64006844a004c81c0907041581c0b1690700c2030048a0800008140b40d01c42d8a04544601d680350504614800784a4810b10064699900608845107804242c180c642d0302d01c100c0030b100354801c80b102042c81c0d44654201084074440d005000501e40c2030a0000c03280d0600c5016550000320080c08107102c043d8031036003128103180c95001080000701c1586d0400481c02c00b041000b002803805006001d50f031820351010083e4410768800946205070003007101c0901e0084004640c2510041300581c2d80e00c480750340225a8a8a040f00c80091030720070008009049 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 877602985 1250 877601735 877601771
    0xc07060b0d0b06060d060e0a090c06020a030909051017070501020c010c1a15030a0f1a070813020f04050106050901110f071214010c020a0c08010203060d02041d01110409 74
    0xa0355105250310301d035031070b140140b02c240d822651400c24226954000842c0300041c01c0c87c16480392545940121340848031f0f01c0c11001c0561541d1080c1e0555003c82c4107900004e401042900540da1100e4000800b07a5400c01082e082c12116400100074040307030035220700c0f2080d0114400090751020f03022201e80040410044031400045c140c090400503d222141c8640480a98066049180c06d00811303c01541040042c4c00c008199000f207078403000b204103c2e020040031714421105e0021500007401c41c0e00d04807201910340c401c02810014140c0c03080900c08115903903000c040ca03003680060010032071581c44103400f40c8a6840170401d5400f041e428034203e502404e0000301d400e081000b1134050903c0038a8104444c8455080080894198041140640e5199800d1040300302da02c034103070300a04042c0f40506003c0c2d01c0b560507801070301c45640104100960340d11405007420607140d040d02c001810b250114880c003603040388811800750a50038942c02000c5598880007078005d98400100c00c000300010341d680c102035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 877604235 1250 877602985 877603009
    0x150f05040605030406060506031503010b0d031b080c0a110111010c1b020a1a1b0724030f05010605030a06050402070210030528020315092703040e0c07060b 68
    0x184200801d002140c4150055500140f088802241d41d580325400190300d40c00480b03403d880381201500895071403809000d4980d080c201660f0120103140303552070081245801c03003200a0107a481ba00d4510401290304101c0d0740b5240040c0c03c2ea41001030914220703020182444007940007036100b001c0d91800c00e006100c0c01c01e5898054892000d103441c000c04000340c402c00050140da101c210f07050001105008003c01c0c0e0724130301d070144a69680d038a85030b80034501c011822880c5900d50344002c8043c005014541d0010134034034030610682ca4165000c04049000d40a0040d106000908000000030100d40240155001c1c80e50500c043c40310503140c9003400100d001c1c90f60040e40c0006c040100300d034039034001c0e40001d4122050748000380803a5200f014010200358803940c14040320742d000041018804060140d035607800b004413140f411500300b8001c280c103410150440c400000f41ca011031641c004ca4108100d50007081c00391504111072500c0c4645480d29088584252002410016460036924161066a00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 877605485 1250 877604235 877604237
    0x6120309091609081b1c0503030a1e0212250509091e190f06080c010f02100c0909050c0c030412030c08070b150a050d060f0b09040507150f 61
    0x1036550744650018900b1440e0300020310a1040f00d1030041016942030110390854805041400c034040c0d50102840794012140c9111180c1741c42e514550070006030003108403074100224a6001c900100c3d41c1c1608049a0b180380210040a4030000f5002c6120200b501400e106040c0303603200692030041c3d000e00c1d52030802145080340004104001c00252131600c00c0200390880745e54061545d101d054060407081416050b2401d140d141c000b0060107081c0304441c010203948a031051001c3c05424a40307510103541c0e03044020300c070341800340d00810049a0317482000560280c0803043e6080c04000802d0101801c00c0c6160b000b010b819a0400e03001a404407002001ca80c0c1c2894540e00451a01e4035010710001104d2105108808104e080d4841c08081112500944a0240500700920325400e00520489080e041d051045010300c181030f9040040d075842915041e0410f401420110b1442003d03802c010040502551666008031000c00f40010300c80009280f000b170b00c107611104038078480d08000c1500c0c030301964907100c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 877606735 1250 877605485 877605499
    0x90901050903040915270b010302070b011211130209011404030b0f180304091b020105090304052403090a1209050607020103110c010903020d090605072312030901020306120309 77
    0x1600a2584c44001c10b003485c61101000140c40f81e9800003400c00d807800c1080c03035407003510300c000c181140b40c4581c80415809080440c82d1281a0b03440c04001c4005220f1100740458003940041401101f030241018a04001d1404002c0580c81113944003e40214030300c24001105880f1030004c07001d1010880c0c06807500032203c40a140e136000003295403018010880e044103680031018445000381000680081c0c01805404a401c149111010001c0410495a2821a0b06101c1400683d8030040100e40c00c1d03400680f203503200c10310703000720001005400211050204c040082048541d010108080d09194420440c094172030142c11000c4413407a207103015466204008100d9480158001d6004541c17060f6030442d842e003045c41c546182c6084034910a010b6001d600001d14806405900070001c1028010314180f00e410440c9540f00d40c0c89d145150220180300c444001d40010000304e0401100d414284500c5800340ea070310f455442d4034042c0d00151032040c000e540440030401d0b800004004d4070816200503101c070f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 877607985 1250 877606735 877606739
    0x504020f040b0d08040303230339070c050a051806010f03230604060603020412060903020309100504030209161d0f0d050102041409063307060b09090105090304 70
    0x300b61020318198402120005440010890720182000790b0281d20359100c0c900d0f07000c04000304144c0005000410007010000c1110344c5003584c460b40119203501ca0141c0d04203160841c40b105001350000342c44841c6001064020412424070b070290107a0380c082d107501103078503a98024860aa004241d01c40c41c41c0d840c402c00101c07030f0351207004070f0b43c09c1c07d00d1440c0110704094905441c2d558500500c0303d6050078400034023041101d003482c1c020003005041c40e00c4c00714030381440c7c50b480030350610404da40140035075250700c141018980f0030016940d40180050660039420241c10010b0b01c40c0d442032100324050701c41d050014003003450314141c052580c180c0c0e0700c542c0d0080740310f072410080702c0308501d404036446412445080c10030345580c09520780c1c03c1d2245c3c0c001a926410108510081d19149005a101d05404810010705444820584120000e034080c015017294802d0088a16442d007480300d0884801c0c040352290500080b90090f2920303000644030706800e503e076a4849400e8480131910a580c0b54400c002c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 877609235 1250 877607985 877607989
    0x5010507230f10022a0303150406090615030e0d1409040908040b03010305070b0301051008090a0b090d080a090807140708060421082208040b0a0804200904060c0e040e100f0504020f 79
    0xa14086400500010304ac0383c0b04c000701c90071200d4a030080012100c41c0c1984940b529010310820101014040c000e000c03e104c071f000024110511035551143c0d58a010690440e25204d035002018520ba0100e0034039140c5803203e0f03500e0346a0300248826241741c4100304000520f240040d003140d042c0c0300003a1071103450010507a0143c600c11405405504035200c2d2a4003d004101c02300b10003401050850050652100c04140c000d00f40740c0041c044200840c83c2803100c0001999030307011140041d85c000d0704841c040341c103848682c0c2031409543c0701039040c0c0104001c002c100a0081903006800c0303140d060903100607a40d01c1c2c045907030a0044034105c6600b00030360801e03910104611100c040492240c422245401e4848074a100c05070450302d846e0000c280c2c41c00c1403108000c0e086005220329032101e00924104104c08000509104000d08040c04c202c1d07698a1010242d44502c181110b12a0301800c140803512300c510000d595400003184d0459598131f4407400c03014000301d1740a00383c01250003c0651f9080104101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 877610485 1250 877609235 877609261
    0xb0a060f05040e0f0a1b08011107110a1e0312050a020c010e1527032b2723180a06050a030b010e0105010507230f10022a0303 55
    0xc0d180f503103115100d0441c9041c0401c01c03503404100d22072607099403c80d0f600f4101c0d40d84d4010075000307200c2d50707410100c01004141110007030350201070700899a0308400810a0205070000d055400010992218035007c20f003048507000d400c4100d03403048a42e03032140c1001803803ca441e80100001c0e040141c0142400d450b03036612909103010349000c0188403800342da14241c007014696100e00c219008500099841c1c010180b1840c444142a90040e000b501401c040440011040c103440848141c0c2c005401a0340400e0911504140329518002285801c000100c4001e902d0034040501c94046e402a50611b0100c4400d001c0c0741101a405010303104800380d4400400c01c1101c040000d0100c04c06a907580301c0098155a00144440210b008000c100000c0d410b0144180c14a54140c0220341030180c2001180d00007160900d4424003d44410100036403500c05c1d00000c0c1c14841074100c0c0c44100c0c42507041070403d60140b9401490700c500c000c1c5585082c000702908203180024000311180c9150010f2001035442c5413800f0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 877611735 1250 877610485 877610501
    0xe0315040203030d0c0806040f06030f0b0415050a090203010501140d0f170a0f0e06071104091a190b0f06121005040f0902040c0c110103200d090b0a060f0504 69
    0x101500d0820301325168030000c441d4400b56000c0000d215034184000c0741800d00ca100c1c103000c50101c1c00c1c00010301f943c40c3c1c41183c540e2040014036089605000505204008066140d02c00410005001e01d042c15031802c0080e081d0408280d00c29481c00740000b031040c03150381c038a080e00c00c0054080000d00c1d140c0e48900781c154004010681d24440e1015480445092a100030001d440b9203848140d10000c00d00c81c010b000d28582940180108010800c03803021598040c0e10740400c00381140c000c1041c080501e060340310151003645140f0b501c3e902c1d07014017024004095540b005801c038908108001072380a4200480d01800020300c0ea00f003401005403d000c00310401d0495845035003240700001880d540c0002c01c0807942030000849081380d4880e02c0e40110325140c080e6190b02240c51801c0c1c0100e800c192119003010245483e00d83c10b0503a100190151011010031105e141e20014003503980341d44080405034003400d040c5008480908101000900e416503c4c41004165080460382c2c030051030506007480000c0000d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 877612985 1250 877611735 877611739
    0x1802040b3705090c0301080f010606140d140403110f01050112060513050a080d0b013612050c12031809370b04061428080d020d0e03150402 61
    0x404000316443e00c60848507401401c66920041c3d4035803410b03038017034107110240c200b40146034185141001100d52280c20725140901c2c0000300760b03071000c07043c41c1000107040814a245500c03280070104000d00d90046000b5030100010740a5403402c04100c600c181c00c84074240206100078091071290b001140c043e40c0302c5035002c022852000705551003a11805c0c40c2261002084544a038001401c0f152900c0038060118520703000c1c02c16401c14048141240305a030b8054901004007045124010820303072107070a00c0c10040410500d14009984039061103a22508205801d5005200c9001c807181014000800c8418640c643d00381a091030f6404800c22080e030398040c101d1041c490a101090b0b41008a1641c440c6424400301d0007802118035407040c4d0400d8909607900144607030b1400c03000300300c20401c000a402011500310380c0d83d02c2c0e001c00c40c8180184405036040d0320100962001020803402d00006110b002c840483c4c0848800c02c4404404131f0b02e400300c0c3d1020b140c1641041c1d069440484810180715000340c80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 877614235 1250 877612985 877613089
    0xd0203090a030b1302060f0307020c040b060d0e010b120102040905060d0f0f11040e0606180705040b030a15230a0506040b0903010f23090714010804030903061802040b 73
    0x4ca40002d00c0c9038101a006801c0558004244120103804001e40301c1c0c0c0c40d4003650203106518082000880e140149684240c0b82d58464a41c400c90000a40c4985448000240401c816400c1d00711985e0003500503014113040c092905000c0380840c0f074640340e00320742268001610f81031210b49a030b84803184544003008865005d6001702d900c1d05c40c1d603980580c140841600008180034a000810859402480d101c210450070391801880103c80d40b2104403015601c131102840d55940b07416172460002d1602c52a040e52121813010040b40c5c0c10b004c48001c107031110014007002081c0401104000742203003140303e135541c0728008010422100f4021006030000c01802000000c29002c1c00d000c80e801eaa10702e050f50800701d810403050407545071079483c28680181c2074900404507142000e011101200718061302905226a150000301014400c81750f5001643c0e011005000070b080d4408040f8031013040c04400c1f4412803c10720321000d07908264680042c811282c4c030380c0e080030000564070301c20a000e100c01a9150007807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 877615485 1250 877614235 877614271
    0xc090f091f0219050706230a0c09030209040c030b01081b1201020d0615030f05241f0f11010c1d0109080304030f02010810030507060e011e0e01020d0203090a030b 71
    0xc3d451101c040c440d5480d2985995005a481e0a000b01c649251040702d00c0503154551034594a40c0b4a109a4450f21050700010004d90b5140140c1c0c50051a0784000e520440b00d100b0002040420b891030800c9a03c03e8602c062184d80f80d10100d5102d6900c02140701005040c032941504900e0415a81c4401c09203540005142001d040c1403101a11802e0304020101403007401e420380c2080c1d00d4440d000b0b8041071003a0030801800c1c035451580201c0048981c00c10201d00d1140b07225407580d5031900119100780400c400742002d400c01e0201400003a81461003001003402e8070300301e101ca10018003e144001d0000da413183d91405402008104000c2c2130825181006482c00e8045540f0a0070030040024500a00390380b900f032020380c40018924038004241d07034030180d4542000c0000410009200c0c06450300c506001c3c913101007134001203817445042c1e01c0a01d500c0c1361030616000d0705900003035154044c81c003c7c2d0a40d05511300c1c22505036a01d00c2100410394210516000410116110310081c58101c0014885030842039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 877616735 1250 877615485 877615507
    0x1b0708030711030d1a04140604050709050303070501050a15051020011406030d050c10020904180b100e09070b0c070803040315060f0e0402090402041d0c090f091f02 72
    0x7030840044c2024140d590318035040708413030300848402e14a404450034032048008280c01c85110001920381c07801240c5440110300680c3c0201198006400d0181c212500c401450401c1d6020302800e8904030040ca01d80346404240c07207101101342d02a20400340c0702aa1182a81c20308035066203400b401c5103510b01c00c106880c3c0c0c190000703004118005031002e4030101d0710700741501090709040100328034606120080000450403000440d03d81c201c0c100c01000142c540b03004d40c0102e03001e880b10701c0901040f2034180d4031071030400081d103040c940542401d40381c440c509621455080c10740d40090341d4003011075019001c20400030302850010079180c541c074015039038080d40e0744000b1465600507801c11a0708c410180e030002c12107400c0d4070910001b0840041480000c500d4104800070800025102030b0042d2903200c005019034941e42c100c5062617600c0c1c000b0618070244405200d0315820310580651242d008400414500a05260100d004454075005000e950031083e004039501c0007546040c1c000c0d0741e02807188840d45 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 877617985 1250 877616735 877616737
    0x17031005090a0c0201050123010f1809020d1811120c0a03081b0a0803010303050304080c070f08010c03291503070207030213150506032206090203061b070803071103 72
    0x364400c240100790b83c120010041d0a41da8140c100925520030a40903402c0f11602c00000300340c813802801d0003003501e0b6030420111780110030320210451f0821031280004821503158010902903a40342420403c1d21016416500d0b001007840c4081d01e00c8448506c1c2c0583c1d17142034441e403403a00c002c1504890640600e00b011a00a1001c1d40c0140d0742204081013082049880024036200c480840e00580f84485060780c0344085800180001780070072001000081c2001001c4044500000020080390355150703540f14007004014443c0a040415400c0c2135040440c20b000e070051000315442d41001c00ba80c4111030101486c074a560703440c810703441040001904946036607a0011405048140c3c00303084e170603007140107211421807543d10360b0428901d4403050404454070300b800701c815903030100c0780d0958907200d07840401c2e105102c100104001c07020442c196400c00a0301c0d4441040e141c800c1e403d0b940686e40e21808440052001e1003648201d2900700151400070780c07640001c41d403200c0c1606001039208003040c00b0503c1c0d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 877619235 1250 877617985 877617991
    0x60b0d03170c220e01050d0c06030c140c0a0501110c0319031e0b09070503091c03020d020f04050a05040c02150618040506040201081b040513201b0102071703100509 72
    0x1104082031030500c62080440361003030240406591150080d0171f1640c1d101c11241d4a48212002c142d41c52071001c0c14248100c1205c0906840c05c41825281d150900041d626002d211070b08a50035860045504a080c1181d41038490314003101003d142000080c00850102d0600e0301007410800d40e45198408800a2042d8940d01c5000021400039031088004240800060060040420b005050041240d4042c00081d000e40c16580100d89000c01ca4094000b03802902440310860201c81c000b141181580003080042c0044810440705620180d540d1010301c0b0403100100318110058014052022914001c541c0c1c42e0f03000000034006185040d00b83c1c2401c1041c50042c0c4013210990000010300040d0740c2c1c07006005401903510009900340790b6000d495500b0078440c61265a0107018810b0080083c0315050307100c29004a901c0e000703c243e1902e004080d504562108180c0e883c00341c00e040200e0503007401482a54002a032144a91803034000c051040c084580008001601001c5008804162a00c40c1c031407040c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 877620485 1250 877619235 877619287
    0x10f020f0705060106020a0809010e0102070506042310020604021c0602030a140f010501080114040e030c1e0706020a1e0c08160e04051e1203070c060b0d03170c 70
    0x748801d11031500d40d09141042e03020500f190701211030a80071410040482d1010300b801d080c000082c0c0c0c030300e60060341800c51550106511020100e00052160820791b1800041000950320b4540001d0341340800608031900e41c080300c0141d1200340000c1c01410588450040040e0306020386400c50003540d80c00d4166441224070b00c14950300c1d080c1d0090035000d08004650028081c940243d41c82d81420002415514144220542003814180b80798860720b90b94052506958200d050780e503510f040a41c0681d50b00201552040e08503c006602d07203041201080361010b6910aa0141910301100e44486400d07280d52800011184008031840c4001084000040002d0141c6d02c040d05504240d40c1c0c00c2c2c0c2d5000c103070380c1c403c3c0307840c82404040000152010908007041000c0c02c14482402c8100ba01003803801e40070921b12800483d0000a000c80581c000001c0c0c45014402c09051180c2014001072141c0c40989020003400306034111140d0b2000c001105000d580402d02c50302c8141807403601d41207894440400e0082d08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 877621735 1250 877620485 877620487
    0xe04330207030f0306090905151f150e0a1d060f04050703050402010801050a320d030215160e101b06020711012303060a0e0f071107060905040e010f020f 67
    0x400f90300740c000d4034001c0c0090081000a240d56171a00f0340c440e40440700e4020f0b20810354001840c3c1c2c4a002c0c0307400c4c0d04200c2284100c07102c1912108014a006002c0300444003249000c1150066481c020641900380e032640c2c001d40c4401d14074005840c0000030302800060780180c01891001241d2614421a8420b00584e60085140d081600000d803480c00180c00103805280c10400500400341d003140006911320800340c03000030341100351030090004141007060550041e480e41e00e0909141d400181c5450000c240d103c034030695192100708910100d510241030000c15a810802400741c070705080200d0808210381849118071000756034000307200c400441704072031099011480a09220068030020030391107003802d0042c0d841c140e980c040711410020701704420030f100002000075007a4031040184801407050800e00382850400c04a0391020348021511640003400c0701980f99a0000b00045840840324a5145e06d5001030034030341840090204a0840c07031444d03403900c9251043d840319100400125585075805 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 877622985 1250 877621735 877621757
    0x30915110307030e01270f05060c03010314060402100e0117011e0b0724060305060421021506060a09050910051e011202090d02100f090e0433020703 65
    0x140c1100d455000081c1303580c1c580400348214800d050010105598825495080004c0c985403401c81004110402005801003200707000294003554059410b03a071090000d081d00c40a0069640d682c0c140444029512841010352041c0540c002c00d80308500d410107240040c10b80c518112807038803400c000c3c1c4c002107030001c0391100c000e906d0302d2568404000c0d00002d0441c1d4600b00c0540c0783c400401c0503c580c448042d40c000c7c11103400c0c030f84045d440040199402001c1c0c1da4a80350504206094803c080301030000c8014960001040c94404100701402c44400036001c0000d4071303010148900d0b90002a183c2090128818000c541c42c0c0d54074003e640309084400203081c5043c10300c002e014150174a400b40c06cae40034000780485103a90380c001480e01541c412524005890b010320100040343e0705800d00300a508500c111001e62411944103034000090903103a02e504108070382d1031640c099510802c40d40a003100b000d681e0410418811b82c0b50004413444614284000c0c41c3c0410800303803ca0340514000c0700858081905 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 877624235 1250 877622985 877622987
    0xa1b060e0102031801111e03030708060405090604030f1701080604170c060a090303020f180307211101090803030712110403330e0109020a05041b030915110307 70
    0x21100c0a0082840070710b0800d0303000328910300900340342066a0306100c000c1c9540d0701500420425046040910204c041e05203154412040c0c0b2a8000d441c0c110010b84180001092410103000d80d50160082000814851b5690740307080f500e400c6402d0054040000310841030f0b0880c92080d505a01030070b0004081c1c4136a003018501502d00000c0e803100007040b00da00707000c14640c00d24007280e96640242c1801f004244810341d45021402072080c03650618601c0d00204407040706000c201da01030a520415811a41d02c035440e03041e0400004e0004003207200c40461070b004a000039850b140d03010301c44074040c18040802d070345503a13605045400c02c8071034100184101c1081c01d6543d41d41d005400d5078402c6040000d1400c2d0458546082001c00c000d00c44900e014103401084078a10080a105145c01035130100704500d06024040c24040e0454402c01d9100380441840480c41e440c15228400086101881850b06460343c80c0055000d0001c8442c01e40b03403c00ba8500d06100c583c05170203040d80c008481d450302560381c60a500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 877625485 1250 877624235 877624247
    0x318030c050f030a0b070c020307030b130c051e0103091b18060e0412081b03010b0d0f0203150907020309030a0309170601060f0e030a060f052d060d02030a1b06 70
    0xba8041c03090b4020342c14200402c80c2040f1040d0040481e1510146010040c00401d04d0200f6681c002420751002500304040340200d1411103509512a03020a203260355540104000d0a204611340710600c500d1b8842841c866000741d04c542c11692243c0c402071601902c0c0f400300c4040940c030b540a61222405402003941e010300307034803801c00540403c80d160301d180e042540341c564002c03000701524014402581c020079090b8038001c410407034a085200c1c0b0159030350784444084920350081509980c61504102c080b03240b18050b4001e90740704803a10100d4251103000c81007007011880c4064400004e500081003030000c1038406000190200340607880c1e0100c0d86140c0894030400c2c0000a0404e0f11a420400040c0800c40d40140517851815003071a05401c082c0d9440d000900300345880780000c1c6440d24105045000d40c01c960003c81c840d0303030507500884003881d184081e00c6100700100c24441c3c02c25117690000e0340718a8103140d83c07a01140064110303441c03200c1c140e0759140305960010007040c20541e1140100f010701d5210b1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 877626735 1250 877625485 877625509
    0x6190801240902120a020f0c0105010b0a20060c160f0614010605030609040318080304090603050d050c0c300f010501080109050a02090402030313290c0a030c0318030c05 74
    0x2034803c510300600c0180d9010554400b81003881c0ea00c0e000548215541810f600b07903040012614000c000d50350751200200c3d038075800521007001081c058103440b00e4091a280c40c081030040c2820251034a82c0d200c4200d2107441c0c0c80244202c1e2090000d601140202303188008030702e20303d4400d00001450310941c082480c42080142c0c40300042081c100104a0f060300c40003030b100c0c1c003e941070600110611211501e0400d419554000124030302c00401d0011380c02c40660041822240a00140e402c86241042c01712414815804400802e500109078543e1904203010401d407445444c0030295041e01c01140307090301d2011420950321141c1d124902c5880c0c0d8807420b1090500400442000f000300301099a01c203030719011256406803040130342000040540d00e0034001c95a02d00310444404640c0c9450380c01205107064070303200c07a641c0244401e004810040000040395960380607400200007444c00307998225964010110102c00301f046584a49003481c2e210350040c005984a114001002070a000c01c2c40882c10843d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 877627985 1250 877626735 877626749
    0x30e09060d062007030804060606030b0a03080c010f020403030f02160f05061309020f0304110612241003061e0e010314120a0804021201140619080124 66
    0x5001003541c1d40d201100480e40e10007000325a14084240c2843c90394501800104401e400003142ea0030513502840a602c141e11070310042007615101c9004030221920f00620760b4011680200500104801101800c054440c800000c240a21548a40816a00301ea4021004540b03150080145030f5018050750050112010505c141d140c9440e0b001ea2801d90315201d85800782074000b0750050040c403d0f8080401805445034259520301600341c40c2c0349171b03500c1142d003580c200da9a540030b111240751580842e6849041d0300f03803e460716203419100c20350352140010f81c06a03080090800e22825160810030b0903280301e880c0c50009d055403414030b040e280203088002c14803c801030043e042c05644d064840b0a0b041d40d4100c8003020440440c2143c0350720300323096010408502e030000b003243c0750415400300c10710780724620a80b001a0040031104009003a103903070304d0161159a42000005038203080c0010803c030000b03001c070040f4540b02d99440d029401c407403446000822415114544060b001401e00c902c000038244 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 877629235 1250 877627985 877627999
    0x8070c091a031b1e03010213062d02120306042d0c020106030f080a051308011d06090709050c0706021b010615090e0408040b0a030b030c01020d09051c0b0f04030e 71
    0x22600000c4c001d40360301c0c500b0000000c100100b2140c10b403002d40c1510b0011102c1200c4007100313500d8100c090724141035104070710020689800c4505106500e00c2d0803170302a1580b600140b071070700c40d04000c0b0302c0da540004145581090b6107a4010071000d22100c960380c0844e610b03889803400345281c5840102500c885080324029681051010000a02074400c400d40090300a0039040d1924201c01040380c0030310520704608260318000c040451444010361010144840001640b00c10441c0c0070901c41c9c41d6102242d04482941007407404004881c031030781146910011241a091a026055481c0b80898000442d0010701210106110b002d4203401d00c9001c020305482c003696141c6941031040141510518094405c46c1d5421002080410001d003099070054604003901e00c0c1c070b9180c0c0710401001070460548041c0b0a1003003130072401555001040724060713490f1039070301c00d031126080000303008040d000c0d0002994004040c09501c40030806165106020306201d0016030b03254140343c20010300d022008507415100b414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 877630485 1250 877629235 877629283
    0x30a120801061d0910050904120201060f050f0d1115130602060603100b0a0b070614060a05060403061a03030c0615030d0f0c0311030f070308090105100308070c091a03 73
    0x240c0e010402c4283c14101d4542c1001d03030314816000303022a459880250041641802e0008000d031401e030035030800f22541d000b042015034078a81c1c405460460311807141c01011b071907020344c1203052650400144c14002d140e00c2001c4840c03800421070701c00c07589030f442c0d81c40700d40402d05840344a140d0388048000d0010b48014221400c0100000b81c88154070521f03900c42c60342d40e09284030706071909280c40c00201900c00d10365813944403604000d8040d0010840b00380c3c0700a84040091610320b030407100d03641a10005040306080c941180d540708002c0041030a1716887e40300d1107405004607030f0100010072500707030010058641030400000d642000c90381c44103000d101c2d0b00010010307200b5540c0044222217041d102d1400a2145082e8141500d20b40a19a20000c0c140400111514414480b03401860001c0c03295442116503034560303031458200c0764241d070500c0030b0451000c01003001c034184a0281c040a40a00000328030b40e50764444203130031034020320b1441c18040304030b04181c9143c0c0f9083c4281c3c0006041c200e44040703200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 877631735 1250 877630485 877630517
    0x3040302152a0a2c0112021c0c08010603110d180506070203040f050f030613170d0b090606030402010c120c080c030306031c0207030f11030a12080106 66
    0x1100221502200e004084005940e8280000901d82e444412402d200086031401c0304014035948440c030500041001d01c0760b503d40c16803048003040101a814030702220130511a10044456984600c05100031a03000c0c012800603100f800d03100e4950941c0800000b80b05a40c4060141000790140d0240092500d8450803079524140f01080314050081038400140980365202032440e8101d152101404e9442410200004c15400200070400d0700e00103045149019a9001084002c6404002c1903801d600031b840441c0780740400800a14029100e101032540320100f07021402c005412024003050350a8988500040d03e05158400b80e800c0303101500c1d880d10b189482e80000c1c1510b844a40010319001001e03a040481c984282c0400c06074075880300440f41d8484603a154241e4941007595510301ca8050503121050700800685070f80a41c2d80c445d00a804007620b15290f01d0f0404420100035501e400800e10700c9295558103010305a80c551261001840500051100a0500d00305804c81c00520200560000100d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 877632985 1250 877631735 877631743
    0xc03090306130b1504090f0f061512120302040b07030906080c031e060103270c0e0103051203060312030910110c07030605060f12251215060312091a03040302 69
    0x1002904001a4062040020170010201c9400140c1202d880d800e988040110810f03988030803900424041c000240850410001c08040d4807035052401b114031828000140003a0540340111f034142001410180d4400480e460340c0e209801c202c1c0003684900d0203122180c3c000e83c80b80d420000c0f0313414141c21468034240d01c1c5080e00d6410300c410981c03a007440014940384e100350800000304281c01c0400710785141d41031381104120f10103103049548032040f21020134404140c003103282c101c07a001130081403145010b070320611007544044c20700740e050b0090010b10000310340c901c00118001ca10480c000c01d0556040005e40c01100d01124940c4440c0d2420080500056000a41e400959801100010781303a11000c00260301d451803645599001003541908000c80080400c029914000440c1d04c0b5070514200f21110181c101c840c06034030040c0e1004c0d011000401d002841c00303541407500500004e492038603500e62030a0401c0408040000a003284c900388503440034000b0380c00801d07078580815070450406640c041d480d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 877634235 1250 877632985 877632991
    0x315060c02030106051c020a050402070b010e1e0c25031224060206010303180302030a03200f0102030105040c02120d0e12280206070f140904020c03090306130b 70
    0x200034218844209641d402e40c8040004d080003000d001c10038440c400c2d41000300444460580c0324621000d40041c2e1401c2c43e000320341003241d20225400d4160300f0a000c1420800c4003034010381c9610b0300320001082c0d40d8210340c1d409018210500440c1c2d1190380c2c0d000401c5000404103440400c4d8580c64011100107a0004403a8101c0642c0b1070b40400c000c1c1581040e49044082240c040d40403000104c80015442d802060341c0c1e069a000e607850640c0080c09001001c0b000c003407840000c1d050f511043e46600403d11074484a4404011410700c540003803001c0c2c8500d480e280d07000c400e562069500000401040c03410340700b4008004418009800c1d191002004c440c8207000754148106056207440341082d4014050001600b2040003051194840c441c41d05880040c10442545998111040c0040d00351203000288040c4190308540c0d81098504114030110794911903c50a6120315a080c440650305a8440c005004040101401982c946120008041c9440b00140442205034013807a0b8000120f9107041003164 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 877635485 1250 877634235 877634237
    0x9040e0c010801090c1101090b0403020d050c0d030c050702031e1006030312111204030207060e0433150512070305090607050c0a060515040c1d210d081006031506 71
    0x340c04450780305c252440003559220025a500e80400e080c200300c0740c902c500340503602035030071503134600c440c07410a03103451003610b00384a1103600401c00702c43c04074440e801036504201286000382c03d040495000c00e1900038403007031b40f0000c2c0c3c071030200c0c60408034010401d071800c0d10b18101d010302200c0d1a5484c090881e68540009045c00b0303032649840e40742d0410303403002c40d1030300c80e2440d00c213000514103420001d440340c019024040000300d91840c1c00c1c8503494203004902d10301d15110312a42d204802080400c420304020070300c203000e03072003081c400090006404003940d00e041020785890380d44a40401003c040c0b0503000300307800d0a0510342420f01c519240e0005200c0c2d40280310b410900d94030403201800c00c0c909005007600521060130170080180341919004412a980016902407101620051082c1c45070762100004480f0095071490000c0c3e50b241401505000741e0f1198005104c06002c0100ad9040150405555010810b0328007032010005030060984001e12041c54204841c04541100c0d00d00300c401403107024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 877636735 1250 877635485 877635491
    0x30a0c050f04050111150f0708070504030b0708150a080a1103190f030201060b0a030608010f0e030a0c0f0602031e0a0603020607032d1d0a12060c020f0a060209040e0c01080109 77
    0x1702000040080842105030390240c01d10031301e841e121110b80c1500842d280c3c000204400040707100c40d405801614140e943c41103080c41030740c1d1030f00c400f200d42940040003640200f003411007800058503885840805001e140029103d81d5605081810704417482c000418041d030f001d2209481210442d4030340c140d501c0c0d0f0240701c1c2d50303207170b51b2a090481c00343c1600c1e04080000740e40002e003001802d03050342c0448202c48010009100c0444c00d2003090b8100c03005140b0060260308100034400038a40b250107200c00e294803540c05510507400030f440b1841241c0085540e07032482e0101004c40c03005001d40103075030380c2e001c1c858038002e0001c2c03411540440c10900900000030244908801c00f00910314000401d5200803041c1860003c2c1c6090301c0a00a0402c4034440214400d5812b40c10011a1414188100d030280d4510720390303440d144400c9603103540040150b81005011801410341501d01440c00703000c0c400360580a1540541c5070843c10040000b1507101042d4040b0fa42d11000400940366013010000d4115009101c5c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 877637985 1250 877636735 877636757
    0xa030305090a05030315010f08071d0409081c052406070f1e021e060f07030302040f0b07051b221d070e01051c1e1502030a0c050f040501 60
    0x840c42c00100101c01005400301008022450f03070903507042000704109a0b2010021110301c0d90075504000151903c0c000940300d0300c640a1170845010b8082000355000d1f1002980d2070260325224120f40061110012415104181c00040c01c0c0f14040d064100d03d61108550602d4203c441548001c6070040352a801924013080c0300050014680c00f002200d904224510303503c083c111507020007400160012442112a0100005840d00040800c040414050140380c90002614001e220940094004404143d02084049a40c5080c0a9103a000f44560301d48280c40d000146003407030070141c544440c00c00c01401c5010000c0d480d601e0000e50405c0e4030a000162188900c00c20600e405415140c200603520103c4c11015210400c0024143c022500e51500c1040d299890b40c0400c00d00c1c081c82d42c0000c50350601300344070f000171a038107240c04260001e0141126003031644580c1c0f102c0c2030000030301c10700303c1d130310303808070030490352290600922450082c0d0345019171901d2041003a2000602850080c40d04000e122245 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 877639235 1250 877637985 877638001
    0x9061807030303091b1d090102190e03030f1303030f0c0c03030539190302030a2111040302010e04110418140c03061206070507080a1b0302060603070b0403050a030305 73
    0x813580b0301400468601c0168079440702d8030b001a2001c0c00c410480100303c0004075000350609c281e88440520200000c4100e8180404480c1d10100e0502198180010400c2c10b0440022074000d0034003403c421454800b084c86c2d414041c0c041c0036144000014005640301d0140080c4c52141e28000703581c0c0c141045525080a0988549101c40410112000d80c00815103085449640802c01030300b00340b40d9003181c10f6001c810040c0f0400c9010020020003603032003803102180250042003d44482200f20190074041c0b680c00148209035412821606070540d400107051066580c0501d03c18100c81c0241c070140500b448887c42064948210300c01c2940d104841402e01800c1c0040350002d084043c08000486031600b0a1101c040482c1e0096800a120352405814490201000310340c00d07119040a481d0341d07017030006507190416030350b0045802c01c08210000d40c0c5440040b83d0b070aa9001c0803406075004155601d400d2050500d40038998000008064043c403040000450000e54802f503141d1624010031140c482080e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 877640485 1250 877639235 877639253
    0x7020601150c1505150f0f040c020a050105040809121605010e04090203010203040c090606080708041220150901020f1c0603020d150c051603080403180e0906180703030309 75
    0x340240400f194001c00840b420803904600e01a603014080c1007220418001001800b10781c070b0144a0f04000a010840d0b07491515502800501c4080c0c010354100c0b80c4590b8456084403c12201180d1507030010031442400c0c01d0065103511020701c00c000400141018103a0581c000d14144111410060303010300c803252a45440e08081070490307020300295102e060901e08032208510600604088030f10380800003842c107101d9800640500d20300d44130341d9821b440c1c3d40c46035440c14804d00c12000900c125130404206550400d8001701052111401030003100c1039980049101d83c0e40503102c034010340c0c01800b60071880ea450408075031051003004541c12040e54501d5218014200951019520a11410094003480960110780384007621061040140c060031000584241c022400c83c4102c01200c0103c0100090050a07055006802820840140900c40001c480303031500d03540091030400c480405011000008009003038101080380c1a5a0381488050701c00340d81d801251201504050f100ca000700c0c00e0000c032074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 877641735 1250 877640485 877640507
    0x501050d0b040305191e0c0c0b071e0302010c020615060a08150301050106120b0901140f0f0402031501030605030607080c1303020303270405062d0901030c0614030702060115 76
    0x170040805c40e2907a80090902601100746480030413203a0201c0c2c030110f11421498900552008020400d01d041910300d0819400c0b03e072044552042e0006092620304801c0c400d01520b91180d400850f42c9421103100a01f0003c000d4299001400750040441003a41c604080c0c810303041c60751414801c155070701056a8403055135501d085815518000000c2130095000c001e41e201410700000600908040c8070512288902c244102c161400320b15145401030310341607180a40040d801000d186008101c040020102ea10643c1c1c1ea90541040e000c1c50305041d40c150199100078241100540b0b1303289070040019040e483d005020841d41c0000091080320546c11076141340c0a0340d00074007106d80790400c0e441d181d42c85903100b5004c00d15070007a0840345a420318144c000c2520400300549018986145848401d0362560060710030410f01609040e0552603031500b0400900843c005d5a85400b45480e0403409010126181901e100b94841041001419a0005000c0c1d04641e54900d64510030f11a04108441071340c1d5a07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 877642985 1250 877641735 877641757
    0x1061e090b071a0705131d041101031506030f0f091e030903080d021206060c21072108060102030f1204020d0f03020d0e01030207020102060f18030f0c060a0501050d0b040305 76
    0x20b20241300540b98800301401012011401d61385140d604d50f9294112105a90340075001080748800040c0080e28031075801e1010541810085180ea1008000c0f0003c18110341019002a517210761035280c0b2101402004120000c03480e04008500181e02c2c3c01d20301c8240c00e140f070444441c0301c015803010184070300d2200000310f4001c024191901843c040c100003039403102d4080c2c0d4101c0c049030301003266480c000d001c480c0c03205c030008010f01d105460104000d0310010411a140d001302c8092001e94041200c80a0050020034240d02000c0c00700b9004802401d0788101501e82411940140207541c0d1741c206d00c10407508910785000142c2056900da10000700248a9400700031b000c0310310004403904050300007030b90300d02e80c8109449500d24064140c0044049011303a0074064010717408603002c00c810140c00c105031608a03c000409a00c03215400a07000d24690242d11850018803001a000309000b40500406030085950f02040c00154902800142c05401c10f69024042800340c0c8045801c040c00b44049072080503603 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 877644235 1250 877642985 877643033
    0x31060531082217030306210316060b030d030e120a05070627140c090603070b0d0906060602030d0c1707080721060303024b0601030b01061e090b07 64
    0x3d20a0840d04ea8200381d840500404040c140c0c2e6500341d4894412024100b0101c0046061100d001d607000713402c42c0e10310f1054403250303a55051b2960035203007880000604c0c2c0c20358501041151054104034504080682c0820100c4004c0c03094880e203550200444000c2ca8201d440881c011052051119090100d89d035032983c0100b20140c40401c01140100225402d94404191001c07507180c03105025141a040b9021a89500710120a102e20001107019103591102894000303007688003955843c2c100c0c1c0c6030f904011b015070301c0411599034801d00c0303000d02190300e1594034040b22a0320380d0340d6080d00d10b8003000e0103080074008681c3c0001d20161107034500c80740300100303298030b01194600c0d0b640400c01000c2901080e0014001d141c0c0d0841c0214100481d100c41a0858040d4140184030006415a00c1c032100303007031008003012101c2e01c0500301042203418061400741d800581a94075150303001d405580e80709020002d4a06e10b81e41034001c01d4000072640c00b1101c010401c0e40d9100e07102d00c0d0030100b004000d140b4200130f8031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 877645485 1250 877644235 877644269
    0x50f19030501170606100c2d0b15060904180605010e07022b11070e07081801201602031501031a310605310822 49
    0x140c5a08124100c400035080024121081100c1e00d8884908903000341d0000e291210090019103d08500500b042c0a000321030012606402614001109075012409180c0c920720a035003405500c9080c0ca401c01e8090110326900c04004010840314080e8020700380c030450750b4600104c1c0c00000e80c02d4210600350b000d01c04028030341e11050300303250588090720100010721605501700751f0405120100e0707400b07020f107040c0807080c0407440d80210790004c1c0c6580501c40350301842000207030302d581460280b4001d41e030a803134080301da26020710440d2005055954949035681049160313140f100b1801d5121035007401201005950f044204030005002d050901c000b13416100d540b000401010060b0500e6041c0d070f118910211030318010f00040c1304220350a0358901c18500c403003020494400c1080c25508035485020802c0b070203000079501e8a00444408413160340e4101024840303903040541401080c1100921482403070420401034507041c1c40c078080d01030300c5460b807400446c0400c90384101000c1140148640c07614041c00300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 877646735 1250 877645485 877645487
    0x310150c050d0306050105040902090f090a0506041802090a1a031509060609040c0909050c04020a0c050706030e0322031410150303211d030a1e0e01050f19 68
    0x880394a400d0328540903038045586100c0c8a805070302e08845059480341d00b07090800070500b0003544001e0089070b11058901c04404161200c10301c40f481341d1102c0c0c0c00040d96261420900003074541e40f80c00a1709490000b110b241c016920401c510350491a40318000484048c003111400d4000a68048980c2c103100340300e24426a00c1d0a1a4214880e01584090b81d4058444d4001d006410760281c400502c2048030300014805148654403000e0301c81d00130303400c84070f02c60035401c0410100d0307010380d501c14006842151442c0a02208020950041005113010403181852042294980c022400c15160600e000c84080b0b00102c800121040950b400c400514a401d50210003c0c0d2384001070380014040751308003d000d81d0003032405940401101e8140c4c0300d8180c01304441016481c1482c4d01c0d03190a03041c6a8811100d82c100c00c3c05003903502c580d17072000002c6940b41a09100a00309030800d49002140620800b12040b0300c65024230040d07036640d42070030003580707804074084200c8444c06600c4c03810803040400881700840c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 877647985 1250 877646735 877646747
    0x4030905030f0a05011506050a05131d1e0403080105040e030c01021207020d090e0f2e05010e040e07030f050319020c040b090603070315060e0a0b1f020a08031015 71
    0x2130311030303402040761000401307101100b00c05501c14070380810418001c14209500860051202c8101700e003014407459220035030b40d0810031085480c0601c4c02e00110030040031320f400702e2100c820441c050114a8042c5040d9800800f003d005021f02c40c042c40d1201c3c202404000104265403115140100954540c0303031010030290388620882d42d110061040051081c0d0307d80c00341d13456000340c5042c002851403035030f02c0000b44054403030062724010b4031641c21400d03a04401001d6041d502d15076003c00c18151020314050004200441801100d8807540c9860368000a2803400910481201d5021203d00190190750500070300b58000c040b0800d502c803c0901d0b12600066002c14203c80300c5100300c0d01000240315a00500807aa04101c1d00b0301d4050f4851841170020a1054100d0820307080210701c04541d8645444060140d40400c1d6071940516849000800031817500001c0c1040c07200e05540c0309080002c14510082d56200441d502401c0007400201040e00001500e180034090961107086d000180c502c0040203004c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 877649235 1250 877647985 877648003
    0x14150303040513020c07150203031501090902070c0303090f0f12060905060f04020a060807020c01080c130303022d071205010603020a060c03091a09040b0a0e0708040c05010e060a0804030905030f 85
    0x502d015407000890000e101441247c44121039900550640c0d03030300746203400c0400c0c1c25605241440303006000018104090b00003081c2035482880c80f071160f0341c507501e00030306405499000351500159407641070000c900158200c41c00c44007507070384400041c0c155042003030040c5840d020207080d5020340c208010a90001d10030047c05144203403444144a5540c8d42d0846040c001501e036100180c1040040c00307901c0d8400c0c0705254000c49620303101031501100368482c0000c83c2c00c5510440142c0c00c82018a844005240354190070305448130101c1041440010040d51181010300883c0f08040030040c4000c01e1020035407000e000741d603002d081500760903100c0c90080c040070300140701140040d1901e00042610817041d04680601c0980f0801182040e92400411010342007840720140c004003605000904070520040041c010b54031900ca103030190400341001100d45100340c00c500d0511000b0084100c45481d0700003110148540340c43c044d00c0c5920b9610b02120300c1402a4042036141c45401c0540035240e40110f04151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 877650485 1250 877649235 877649257
    0x30f0b0d051c020c0a061d041d0c0a060f08150406060e0f0d0308010620030f130807060807030e0a0c091e0501080a0204110408060c07060509011415030304051302 71
    0x6040d8030780700f02e0361807820f95110358112041801c00c1115a01440504070009828601c0382d50700c006060104048545491280d40b03400400c9034119207540f018041006034040c1564689140340c00c085000c0d080540c0c5130802020446003000007024200c0c01500342c68000700007030003400b6190780d4001c001c2c100d03480d54413540c4c407903030b014951340009107001070818181c01ea040d10750440356840e1142c180c2d4500c80c0c154000c0d80c0200310b805100d9001c6400e1001f4500382050b11402c03621544600c3d007410740b400312900864129030110707030180241c4d81c110480742e80c421240d240118001c4060b29201c1d040c0003d002005056000302e50300402c400306141c100c1d2250100d02d110348601c19070f8404018094600c28421a1002d400c0031440f8009818103406c030700c040c0c404840341d0b1440c0c56900c0314110b2030070303404540d039281c10a000709009041141d00e0145940040d0418001d20010707010440c40842d40c00060441c0304c10500f0303405554200c0c0c900784184c50051100902c1940b980007001c0c032800282d4480c40e4026 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 877651735 1250 877650485 877650523
    0x603050a1e0b0f070507050a05060f011d150d061506120b011e0c02090c040305060a110901030f0b10090302122103061519090807080d030f0b0d05 64
    0x4420001d0464406240d1078101c002c009254840c01c10280310300001a01c000300b040b00400040020031010080452081e10032030050140740b0304403040341140d40d0180c00136040c1281e01185200c00444140700e4903008184901c3c150304804c10280060070300c4815400042003d828049c41007a181400d00e041c80c00c0301c40da84c807860b81c00c10442ca07248040b14031602034940403d0b500d41d1503541d11441c0721600909048107061050715100142c0000e4903034030f81200d07081440d280c0020140704106007404100d401401c1c0c01e000384000d44540102450b42e00440801c1e40c10560703942040d140098043c0c00c070308007081c2c0250001400007080c0710024100d050720b0005a004d4160281e14030b80380000022200d100d41d800008005400d0711560380030130070354409001c103075000c074155040c400b0342249440102444040701c5054114529170003000350903e501a400804980c004076001c001080001c204200012a20318001456000d0350b0031440c01040001d5003e80c01609140b003010030800300042d40d41162200718058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 877652985 1250 877651735 877651763
    0xd27060218060f121005040510090c021c121d0703050c0f06090d080c010507080a0c0801030b0105011404080304080d120b0105071e0b0903031608041a06130603050a 72
    0x20001a1203064600d6002080c1005207101e100307140025107404c021807940c171004071a5240009419180141c0f058401d0b410f5406081110102901c6840c00d4800711303001402e40c047c0c2540158084540494000c07040c04410f65140c0003014180c0e20400c62405000b481e92001200d171000281d50300c2140c041212503106460b03200382c892500800d11202680c0003041c0f2072914032500180716000c0c00050045940c034500384070704800e2101c280030305071050320715030b5402e480d40c17610302498415154120b01c00c000348031f8400014001300d20325080c80da040d03c01c20700b010381d90725440c0494a1114451540303c82c2007804082408140d003000400e8181c0e0310083c5aa800c03d507103044001c01c4044510703040030607010400030400000050501304044c1c6140c58a600c0d0b40ca680e0741103458079041c00c80d00b10380f07140d9a80c200200304801161240018101c0010034604024549070641e2050703030220300d20452a000d4000e140004001e5503980d007000f0929124444240603155413440d10700d83e190191013044541282400740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 877654235 1250 877652985 877652989
    0x3081e0d050403030e0c150d0213030b0906040c12110639060c03091c170a050a0e0705090a020711060403081c090f030804020102101a0906040905030d27060218 70
    0x12007034500802c018140c5004c2c0b006280000032b42c481c400c114000c2120070b600201043e41c030000148142030340c202601e0f0606d402d00e080c0030440c900340c000d018440e2b448203441001c204468504076010109940c40341d41c42502102043c102c1c0c5548109401c090300c4003030b1a1749150000300b0030816141e4410111529910740d8644d030344082c04110340400550384000210704401e256018400f0241c0f1050038442c025140350a60b06044100c2240c2c08001c1c103460784140050300c61070744103064041c504040540350302428040002c4000d0009409408101d402041040038400e01c0120003500e4413000700030a94580c1e491078601034a0304460480103241860111244c80c1221f180181d045450b44061000381c000160b5506a400d0900640164118030655910030003800c0544202e140703002c080f001140a0b607001c0020001503107802071180d8050303400e0001c0d0304c00203034002050f69210b84a14101040b21030681c0204110301d01c0c5d030004a180c150f400c8000f102031008640c000d04208111b4189007a0031041002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 877655485 1250 877654235 877654249
    0xe0303071a0f0622110f0c0d050c0d0305100503011415090705030a1e051e010801140402060a1e050c3d020f0706060806070903081e0d050403030e0c 65
    0xe0b503030382200060301007840081300941c01c280e1003031822200160344868141d519826402500704001105400101d04180040420500c0d800510a01e85945070a0f0a4072519441e550400005820b05480c5c01c045501c2c58802000000508805802001030a201c581181c240850540d00003016000c4000d04500e18207080080a00c251803680301c4074555164295800014044100c0d0b03684130083d1280e8000c5030070b04a00400780120f00d8a18160341f101a0128101c060071010390200c0d0080e031428404a203c6030212003000d901c41c0e011240030342c450b000c00400ba1000c01c00440690485000000e500402a810502030844c60b1089001c9a40340d2410104920760001c40c0e41190f21903a03c1d50352844106200c0e203480810342040ca4a000d4140f24440f0f000700c0480e048900d0441c0c1854a41005006030b44041250070350014403883d1800c0c03010304e192500b2040b441011107994412404440c1400d400c54600e0843d4044218802c0410840c645428010f00901911443c0010380c012031840c0c52161034800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 877656735 1250 877655485 877655491
    0x206011706070903120c06060e01090c0e0d060e03130306020d1d06040210140d06060f020d090303030207020f091f0b0a0917071205030406030609020720010e0303071a0f 74
    0x5200d00701c0060135a02c8100880c81600400001c00c101030341c0500c00242940100002807945036521145541400102c0301610703103440d4100300304111100160304070303a142e410140d840c0307402c520000340c6040718003141030852141442504084103e4080001005041e5009140500840004104989a442e0740c18010104542281f040354481c0d400301d0302501e80b41018cd50510032504104450310704070400302d2426041030345a94280c07940c0e00c07400c00c0550303081560020f003611644060803002c094000301400c505003a02000d030415030b02080000854445656844d14854000c0c0003e0481c50400106246813082c0c0c40008020541c0311030010707a2009480595507556495144c0c0078525080810f2072400c0c50142c0041880d521998400003414144204c400104c2c5006502859455080140107401d94032158000007001c1d10411101c0c000c1469501b003a031a406041c80002521058000121084113454007510f61500000450400704110703c669025407540e80d42100300f0130b0707881d94000d0401c00811 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 877657985 1250 877656735 877656737
    0x30206090f031009031e030c02150703021303060b010e01030c20010204030209041b06081003060c021f0f0531030302210103030210151401020319020601170607 70
    0x6000c14500c914019414854110380982100c00c520070b03946140c4142c40da0940203402003210322400000d01d07114243d80c0c041d192064102407014a0304980000d50340c10381c618500807803900c40703004520040d210b901154202a9900d0520911035202e04203c0001d10203142c10304e001c9013100c242c0600a5010340610a03403100a03460303051400c01803a1300d1030450018003069803c070b55800c1101000683c2c81441c2a80968000c445e4640300303d000c03207405c0608c640c00380c0142050003025010040c1400000c01c1d99400d59034801e9020400960f01d803020784c078100002e0108a502444200d9400303600c15280d01506004150000034040f40d207a13030404615522003000d0460300b898601111169140c16903032500890b511a1400601d8445a6541408002407540d064286c0c01154001041450f604000c500c0c1d420314640350802000c05404150741e1203020b18881c0f903040244640d505506a8000c0c419185401d403c08000d420070403026034020740b510400d0264000915801181d0b2650002c0000c7c10362041c561 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 877659235 1250 877657985 877657987
    0x30b1503013b061807030203030301030303150b03060d020f180a020d0b04020304020609040917040f15030b0f010315080a0602030a0507210902062a010b060a091a0403080c0304080d0504030206 84
    0x1441300301c84401698800b0540988265103000006841c2040150300960103035800044031880c0303040582030b540044d400409002403d0050000c00d644e1804d008441c49da042343c0803004600390304007140d035030b0080b00c8030386044071142401c200707038010590010000c841100c8410010032035064100320481c0015030340030703400c007038117024a501508150740320b40c001070b01420304003410320285003d00009074030940044083c5a85d03a0800c200c0d01403410b0070310642c1e2556040a20483c030800300030415003000320301c41c00d0401d41c0f50010403221f0303082242000c014004c400243e40c0c08010704d081080107980280d4454603228500b400148085102d010209031080b41745800512807a8000750b50406088043d00c141d81c06102001821200703140e40d100000c04041e11040e001490700e400f4a66800c41e0140500d4038001c0000b00030340c4c18101e40c4904504185d44980d0102c00c0100e501072600a898021900020155140021048482140000030740215400f00048555040c5880c1c3d0449290140b440000c1d00448 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 877660485 1250 877659235 877659241
    0xe0718020a02030c1c020105100e0411060d0e0a050f070b03040b2d0f010504110f030a09060c021b1801090b150a2a020109030b1503013b06 61
    0x6a16001041e80300c1e40751040703034184200d44040b6802c00c4040044d2072002d80322000a821400c2c1c0a001720780e070020100c010031441600d00709841010384c1c0b000b800200400207000d40b15146a60700e5003074901a1803c000708225101680b41d0b600d50788c81035884169554030803112051030b28100000d0039003e4580c440340c801e080d074859035100086000d0190a9000802081c41c200149030544244904d8509904a140030300381025249507100b4001030b0000d5010b203080070305070720209580d60103d40c1c500c0c0c0b031042202c3c0d5075a186185203005060b98100102000d007441200a00d440c2e0004642c00c038008510007078011142a18100404803a03a0708190f0280311510004114494255000001c00c0102a1190341250a00304111410742c0c00030000c0c40124600b004d40310003085001c81061114054128160480d100301d03000603100c59054400200801da091001521804c08010340007820361014000380054628401d0940c5d048108103c00b00c5100d00001c40380e20110300d40101f1000d41c110001c0036004d03d817 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 877661735 1250 877660485 877660529
    0x2040320030d120e0d0c0308060405040c063b0a061b0303110712020f0c04090203030d18060f0b01030c050a09050f191206151406160b04060b040e07 65
    0x500c00c3d42c0b00c8540781d6240c0a07041400000e1050210b081650b5072a0082d24802e440c01400404018002900440c501000c000000300854440025202281043d80e11441c0044640d1749200d0308010310540003400040440f80d03001d801e00ca405030710300300319013100300e00b82c07610000c4403c0c182542e441e001c01c401c0400240c0c041781c0258481190380320300300a100c1c80c02044d61640c40e00c080c1c9203009040143d00004842700751820a1100061840e4200c8080c05040c14503000207a0724001c4a049034111a51400000d4048030b00c27285042200c0c3d0710510038014001e002da800c100a01d921408a40803a05010450564521903002c550980f00b050315502c00d00703410081031000d0084403010081c0c010740707074000c403961031740090000c2002003024200320301880615180a00580d003180b03602c54107260210009000d5414042c1c1d04803041d660035906240c441a03036100c0d40da544e082000f0054554940c0c0c00501060007080c0c4c200020209003a40d0034007030645903030741283e6201400d106581c2034200c04840c0c00a40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 877662985 1250 877661735 877661747
    0x51513050d140a0b06030d0f171302030d0509100e031027050c0f01020106060503130609020919051005100503040510181412030c0c0f1002040320030d 66
    0x20390300074804080c0900b803040055141919840c03058030704101d000100300756132070108180c00200005240c80c81540008180150a00401000301075008420000107070b941c0c5a40080100c400e50010100c1e41810102400038200e98080c0030601d024841030a01c0d1100640110300c164546400030f4000c0c031017043d481801071700800034100f48031400703055404240444640c0380707000c000b45405000544480ca031110308221203100301214090641e41440d8041003016000803e0f48d611582144403403150500500c1e10750020105004025441a0b22506010b00981c03010341194400300700850401040d110805600400d020510a0b00d92000b2000d2810854521510145410a115200712003c004902414500b03481c0c1304038440c04070603091101c24042c0200014034403d5070440401401d140100040c0800709844001c04d1403404d000001b5401d400107104012510121409100761841c14014070b8400019500c244020382d907006811008030701d000c543c400c10803c04900100240080c030200b00c41500e070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 877664235 1250 877662985 877663009
    0x1107030f0302070614100801060905060d12020f1002030708070311090d030521040b0a06030308011202032d07082d071d070f0f020a060203100b0c030405151305 70
    0xd066280c1841591790090703542040c0c065401e40e82031201071410300450900312905d5034455440142018140b00998454410f41c0340c1e10340d00400240030300c0860308000d070320300980300d8945070740c47c4568076a0a14030221a8051401849942d440c01440d84413501e085040d50001c07900d1501121040108403201d1910100803100c0620a0901c24200a0300600c2c4424a0f00c41602c0c40d040c0c12141400c100400101d04901940000c42c1c640c100322480c05d589000340441d205020302e03448421500525815940c1c100301d0010a1700582c0c0084249040c0c800701d18580035204d00c03144119100d01a008140c061000c6840075003080040c0e01024403d00c0845801140d142ca02201c0c0490300072810041192140700da00c901c4082500300040341d080c108644001c000100380416081041150000201c000b0703400702e9a4040079401000241c3c9a84030561407070b40c005c2c1e4517440300e40e0b0701a00041440d241a404006002121001c45a440310040103c00d0900342c1d200d0448200500c04180c0800c0c4003e10303040b406814 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 877665485 1250 877664235 877664243
    0x6050a030b0a080a050c12061603020906031e130809040b0402040b0309030406090b0f1b0304120f0507090c12020d06050a0608060907020706020c0108060f03030708030a1107030f030207 81
    0x3000110480440c06006158110f190705400480a800921404200454010030151000c201d01c10010310344980b42c00014062102d2221a20602d21b1614031980540c2c40e003000040020303549080000c0460050201101c0010703501003c02c1c001000c00c54194542440c29030054640ca10380300540d001c01008062008030554015400d2001041344080d1402640c440e0707090600a40da41c07814408007410800c01e40d80300400c03201040244054034a0b80405841121240d0702c1c00d9160741c03040e84122825405030f60481c44040320003480a00a10001900401080e030240341901e40198030382200703100313a60341c40c4010000f08002c154051501550780d402420303074094040c0f00091864a4900051320726103940d03c590000341146040c05004d00d0002c0d59039800072001e000400c80b241c580b0300040e4449182000f01814080b2503000102035480c0c92a1102c0c504500600362542d60f840c614124100e0f40007070314104201480c050b1912103200f080d4040f0303510710350540c0761200d0b601280c0e00110080c1d404035504032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 877666735 1250 877665485 877665491
    0x190204050c0417060a0f0c09061b0b0a0c0810140607031206060305150406050a1a0c0a120207090905060109050a0e0106230301141b0c1903080f04020a06050a03 70
    0x1e6100d5291211543c248107038800382c0f0385030038015107000559868204100000f4a0004212401c40d0041054003c86000e0309200d140b0440410325407a0768040383d08041c1800d40e28a0810480080d143d1080e403011b08a51101308e0540c80c1c02c0d0864a00c0502c03401070303560303080c90000928101d19140700035091440c400e00d002c6603082000905481560340c9680312001107900c5000b886071030040c1b24a111601841914100021807400e40003503c0d0b08081d1113111898800e00108055440050003280c1c88804008102c030651441460891202200904884018004c070200031594140343c1c003a80403a960000003c20b010307420582c02900400002e400c04103200e03624030003c0076080c000c1c0140001048190750341d40b01c03210b641c02d000340403080b154503480c443d916141014409042c0302ca580f941014003012030000062f1400b001c841140700313005000f81144145150065032000a85000328120b2280d95001031a417200180e0060844060b60000d41c004004901800030703500c180090140c12803a46408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 877667985 1250 877666735 877666739
    0xc1b0103060f0b120421030b010f05120c0a1403011508010806010e040b0c09040e10060902280203041d01090f093c0c030501060f05240f0c03030402030c03190204050c04 74
    0x1b50502e424014550000ca51030f80a01640c0e503030001243c00502c90396042607450301580c498800000c100052032101c02c0755000c15005410b52161212221001001a00030740d00c0d6101c01c3d400d00c8241d0755008000c0080d14503000402c08080200b040c81c1207a0b000400490b580d200c0d0350f01c4c3c00b98003800500c1d4840b4100305100001c841d40c1c0c1e03801105100e00500c0c0c09400c22440102c0f84c2400e4848a030400c11001d4010041d42d031302d64030411808501c074428581100c000d103180f408100e0951160b680101c20214440d2444a11607070003502413412078488000c04c2005015541c00507082ea0316101000e4600c42c0f603801d00644500310aa900381038000c2c017200a2a441411a83c01d54440c82c0d200c409a40380800c0780401d00821400340700742c0f0b02801840d1400007100c0d10380030004411400007081ca4011881c0c000140b29091117070800e99003803540184c4041e444005400800d50b0341d8104072800d03071084c4507100f034480d0a82004a041c0d0500a001204015070380095001d02c000382c400504400300c0700c1010040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 877669235 1250 877667985 877668023
    0x60b01030b0915092214010609020a0914031b010c020d0605070e09090a02062a030403060f0f15140a0503030d0608070e09030d050a020c1b0103060f0b1204 68
    0xf4801e040090410040d5a000380c14088456001403902c0c3c0c500003011142880d960000d0034500c0e0603640700d0f000b8130070590004101405008158060b072250303800468581306054220742c6801c2a01d804280c404141d0146030b003003568603812030a080046030380b64207102402c0d51103440404109070002e031480039400b0310b88c0c2e910400c030350088415600048441c1c91980a030b03d00740310b41a41140320308009205000c0b50f44c00080c044d01c03c0c0b080305038218241d10039051054451060040342c00d0340b1601900c1c1c5070740d135034108403018141c00c11041045524206980c03000301d41e688955a5111805005c84440e207091110802111003001c224940c40030074a01d00152581d400c00040031540d10490012880c5440c0c8401c61f0324061140d08001440c085070400c12042d00701c00020381d6605050104082005d4aa904100b4000c3c824050703401c9250180b11400c0300002c40d00c0e02064046842070f82e04201d0740c0e44c2c85064018000e001d000300500b1030403c2203000354041030914015005400b500050300f0b02052480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 877670485 1250 877669235 877669249
    0xa02010e0604111315050d05070e041a010905070c030f18032108040812250f0f050c1f021b010c0e090601050904150b040f08010c03020408030304060b01030b 69
    0x10b4201d550500c2c0d2400c0c1041401d00d0075a95240340c070034180a00ca41c807200c03031903d09445000e005160090a0035060242403220801109000300000031800e000c0c3d01f401c0c2044a080c0400340e11402071700b6030f0701c0000108241d5500c074003880342c2c5261307030349071904899550100c80c5060054507000030441806101c56201500c004102c0046100b1a04590300c0340340c00c0b40c1e041c01c260340341020340103210310b1200300008100e0800c1194500c1a000e0754900007645c41c407004412002000c4d800009101c82824080791581d00300d00c40044082c0140c6418a0a882442c4200c0c2c0d1032181b0b0307030f028101c1d420100c581640c0c8440b04601000da048900d0000d400e0411903800c422420009840700242c82c0e455242140506400007200142100183c0d001041c07403030005d001a1884c070442e586240900d0b950313101140361092851024010b4640940c80540d1169640b00103000d0301020f000d11046035190007458034895003c0d200300c40446280c000614116a40e030f8030780f02e0007010300000503410301d500c035148001c0c1070780c56603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 877671735 1250 877670485 877670491
    0x30613020a0b0a0c050d0e03030f090a12030809070503061612020f030c0d05060306070c0b1302040c020a0b10030b070f02100f0e0c010c15020702060f0a020708120a090504020a02010e06 81
    0x180d07607450070401d9405d0491809003011911300c2400a1504103002940300842200c0061001280441d51803a0a0700458243c42d81540480b040780d0240000e2020941c0c466030090007614210100c0313100d1900d03101050344a1321705481010752118401c08540d0818002c012510041103025401424200c5240490840780d008076070b801e80000c400141603064886a06c2003a800c42e07016002450140f4140601528070301c41c0400107030000d540903001501000b4851005013125902800034080010500c1000e955003101040855200348200001003181e6141d102e40b5084030740182144003252038844050b140405000030319800c60280410301c0b40b00d8007080c001d0054411066400241c1518482d421504080b43c2d07845aa04221042585a000c00c4042e003200500c5000350a005a4a80080c400581c051003006684627030001e001c11020501900884c900040b41e1220b016216003840c20241d80000d0300c10054660040381c0c003c2d00030300c01d606041e400350404400c0c0740000945e0140400d40e8a240c01c07070032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 877672985 1250 877671735 877671737
    0x3091306031a09070b0c0309130e070b09100201021608450102030c0d030c2106060207060c0b07080c07020d0c06121103011404060315060e060f030613020a0b0a 70
    0x241030103c562820400d10005001da070031070311306200b9011103e50f1207206507030710548100c01c94044c482040405520689014100b18100c9007801d6980101001c1600300600c072038410100c00b4070794811140107008540c1c11031944070018540c2d440c01d41c1c0d500c0540d04800000710f19041d4401c002d612542c4c201d500f00941400c445400c840740642c10b844942d4480038940918115041801003400400d400240b5000b50080c60501180c480c06d1014200e50348107120f03c1d49107007103940c1121100f0524413a848a8141c4420b642668030721a250242529146c9120320020140004440040d001c41d102d0000c2e40d8010700c07403541481c80c0c4550b42c1c0000b00301c8805083d050f42d0350040220100902604910f00e03011002d440b8205024180c55280c405059000522948010204a072200070341c958039580200081c40e03212050742e19000d064080306005000500407008421002c002240c0a89400d0011150504008006044595443d00141c0c200c1c0b5801c54100e030023150049000c1100850400070744060082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 877674235 1250 877672985 877673033
    0x1140723010f050105041e0e160b120109050c1813020a0302121501050a030b030c0301060b0d06061b12030e0d020a11040e0304050d0c03060c030b01110c01020309130603 74
    0x60b40c1c682c0d100b00c680681c0318034441d9181c050560300500e06c00d4016039103188040d8001070b800000c0034040b820703c0d5401080c1c80c00c0140725000482d03008050b00c00f130401030345640b4070007605a0300d6429403000c030743c02502c8458900e00180606500089040c40f14214200c0103030000d0ba15400c0200c0c240180c0c0c100d180c1c1e00c2c011030b401081c1e603400540b00103502584601040441e046c454018070002c2c141d845150208030400d84c03900d40746a410740f4200000d00c84008054000c00c035190b518121840103421920f410340409050140c0050841d01c0342002e881d48103850b082c052412643c80e41ca003261002c030400501d00341520307400c20007410b100610440c4901c5816401a099801c16031501c001440c3d0036150982c41180340440d403004050000090710709a0b1390176155014a001d160410692451496200900c19070502101c5407009030705411002c20b508080e210700010b001c42a21b40c0d41c458051207803407401030344140304000300c0c2d240210350030704e010009813000031711152651102c032030145070460750071041f0f01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 877675485 1250 877674235 877674251
    0x904120c1a010e07020a11101803030908120403050312040320030408010e1906090317010603020a08061f08060a120503070506070207030525170a120e0114072301 71
    0x80c001d0f59165000c2124409040d22180590b207900d0a621004030860059400c3d0440340070a60040c40c0302d05503102c0c450500314038103569250041103100303140640c0e007035809821600c00c00060b040c425281034035801400b03181400d507024581284240000c006138204007a0b02c501913400c038100140a0110348801019555841c03c0c0000c0394203680401100101c00c0c1d002c50002c440ea900c80e2288000d803168894000b01e66280749003011103154964011840c89a410b0348000281240c05074014217401035103880300103503582e8802c00c0118031951011548200744602d2050a603007441485020f5200000a10349900340b034540300c001e81900000b200803206a07000081074002d000342009516400b000510041c550913045688143e01d500d03400710f00e07081840d9108050420003004c100014040c106440001014948048000e40d03214941007090350254828041c0c0601f06202d8440c4418241040c2c5403034a00d680180300301c0c0490382c000b0f40c05a034507400641c03a49103004140040d924070100d00703600109a00d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 877676735 1250 877675485 877675499
    0x20c01090c08030703090905090c0618150412030f020708030d0203011d10090c020309040c02011a03030301143607080a021303020d140d0c1a01050904120c1a01 70
    0x1005540200503075a00c18004d40000030b40c0b0001c20401d0704c0d0201d002049545a40d0041440c0050303400015900040c00300300003c0c00e5800e400142103242049806030b020700c1410034905428882c0740a2101c10300c04000116000c02c2c005e07040792030840f4a86c8100c0d21b9042d900c0d0b08950540d040b01c10384d06403072900000108440c0c1551014035442c03980c0c0752202e615900b05101d9841068443d44103030740c11582c4030000f034840c8038028425141c09181c0a80240903144600340000c0c024040004080500410201610301c982000000d03241a5070410300e142c426a400308040090f81d04503e04840540181c0307402d0910004d0306e0050b81120502d91800307046160412100107003000f10010800759081d0301c140a801407420741c807885403003200c0c4c0540b8091107480c03903130501c0f11400b824454001034074402c960080c52203e0b8407100022109010f2042809803c0e880f40d04895940402c0c400e050f4000ea4000c0030501040c0c1500c68199880501e04140d034030560036035140c1601845501e2500740002c200c40040100d6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 877677985 1250 877676735 877676753
    0x120d0f020f011b11030f03040804030209070201090305180d0f031e0f05072a030b0a0b090411120a05150105040e0f1e10020309010b0301060e040503040b1c020c0109 72
    0xc1c424210003880380303241e0316940300020a11030745114104000c00c1c100c003640100a000726030840c034581e400b0b030f030742c9140c035040c040c0f080e41c814403089000c0e010318800290060700c1031003031900f503552550320750780742912907100c202c407100b100a1501d902c08007040c1c2d00000283d400d45201c2015100e40c680a1049107140e03440e42c19280740507104400d0150308151044020350200440e00c2c190307401101e545186200c140d070f130717071407440c0d4441c2c26840f284c8030060200620503d041c102e0700c20101c0d00010301c0804e54400134172125a0742654001c0212107220f80d049141e00c0c0545803403240e9280203049900c001440d45503289024001c45116074506e54030f00c0140820b0400b4003070540748000b00401418600d0741039095a980e00464143c4a58142e40c0d018103001c248801d03c0746c2e26520240b400c00b9500c03420680c0c0954001c01014403461702c2586080d000146030113481c44064451a041000345007842c0c83c140e030800c200e90000d1490014000f010a40c40c160344030030301c09803210303485880c0005601c4219180250031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 877679235 1250 877677985 877678003
    0x605071b061a102a1b0504060b18060c120d060302010206060d1e060e01060303050909130201090e0604020d050f040201082a070503070c0605070b06060313020906120d0f02 75
    0x120010043da06280b42c00031426006a04102c06113003448040281c01c0b459540702d168014070001800110004022145044005581c8119020042e6031f681d021260504d10503403295800c9a14410480460f5241c10405031030040c007640182c0b612100801502c6050340c5c0040008402250740302418015541d0410941e5807201c81941c800c4559405511401c19001290316130615511540080307408100003600302c04201c03031a0308001c0c070080e078481c40c025080d600000c4010b0300540840d00044c0c80c071701ca583da030904e48580603120b080002d81400600034070b900006252a030003e80810480040c11520321480d07101d440140160102da003458800188211005080c02c131803600340c800310705c0e90003210040207081e103289051242c1c3d6585682c64030b03500b580264030002d8504200644000b41203500003005018407485058019581e540d440100911404141c1c1c10480c101d155113501c40c01414281082c0d40c200c0c01c002d041301c403924022040c640c94603454402c09030000b100c421907003903c00e804100c2648 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 877680485 1250 877679235 877679239
    0x408100515060301120212060c0c0c1e060a05090a030308070e0f15161a0105011214070e0409060c0f0315120f030915031b020c0d0605071b061a 63
    0x84a62000006402c0f8007060140b9650364980a85900855071005030b9000740001c11410b4810032300d04180161099084461449640d000d102c21401ca00d02d0201030890348500f0742c85007a01d40d22000d1050042d06d400582c020380501c9400c2042040d0381c2d0398844118019072080d51070205a140c1030790000c292003038540b02e1500034410013851215541c0c542440c20000070201a8035901c0d1840e0ba211140b03800c4422030050403d105184003007007201c03040804681612802e0300ca40c1c0d405180d0400c0300e41143c103184182c11988a000021441c000c1c41615a111094002003000c98003001d551245d03000c41d2000d0000701c000c18800e10001d0103254041c024140f00c19180225007410318a000c6041c8008401507000034a00c20703007048040c0805010318010005018080f40504800502e058040d0017444110420031080a1600708001068400510501c0401c2e000d018a0400360407030780e49001801003d07241c5010b01c1b110100359020312204403501c500c3c9901514020652031424844072000540c6085414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 877681735 1250 877680485 877680511
    0xf04030c18092102030d051303110a0b011a1215040501081522140703020901090c050901030c030b04020a050d1805190201030908030108060a0e1c210204081005 70
    0x540400c2501c1c0301010f698405019410401d944104124194400c40000715078192800b0140049074851301000342020340300791121603848000c40352103940c2e8210322900401c1d20142ca00140310703580b00341c442003942d8901400c0c1181026206007044803020000c036002c0c2400d07200c46280e4180b17450305009031801400790501510780421284a070000840c0700070a080481030895107840e8040d201d1302000c500c115088420726820a0110307001c1c0d91a01407900c800e0381304200000011814101c0703889103415440070f0f170301c85c0f900c0c01124200560261a00500942c10b06035a402c1d840116103441c0020080b410507035581c01c2d5926503482003030b012074200d4801406098840e002c0c400024600060201c40c20407a0214101c2c8858a4401207010703001c490802031850702c02100000e404a4005041f50251852980a20003010900921a59001c1c210610069040b484a12900c414010000076490065200080e6880e40120340c01d0421b136807060340701e0421607108401d000054061881201e4021040711582 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 877682985 1250 877681735 877681751
    0x60712020c0307060b060d021c05330406030503030114031009020d0201050313020301060308070b09010b0a15110607050a0906080f0f0703020d090803061905061803030f04030c18 78
    0x810b549000e20500203000c10f549400c44115680d504054598940000c07006554681e060031860a03030750141d02e0310046940c201004900c032101003d0602c079110381c1580f040d03075811009282d8064640c0700c00f4070503904940c0d02e030004008142e0a00086010b00b20104a2034020084107040c035290490311403450703600518004803080181d0b20a84403032042502403070440d4803912400820a10480e9402c402507040d880c11000108109000c400303459140d01442c0380c50030039911407040f282a1004018641d0740305a030441c0034845050b606881c038a10807071601e0041a0036110f803203500d04d8080141c4483c00410004265492160780c08010381d00a00800d1418007858100b40e9501c1d14000d001608442250469000003007100b40310783c2c19690400d000c0b500500101d41e0500b031034085a802a1441c500540300c40b00078080084004030000100e80010381070503d4160003014014680d001090407640c94042041480034242012000d40040c1d4020040142883e00c0e007001842d054007110301d501108c2c0d06010003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 877684235 1250 877682985 877683007
    0x320040b03060d0c1205160b090d06050703060305060f01080d050a0504060f0c0f0b010312020c0105090603091603081909030f060902030106330c0b130c0b0a0206071202 74
    0x1607a8100344180c81d1441039489520700325040812641002102c050508401000d1010020358011004c508511400c010390700c070300714211729100c0c1702600c9400208542c20781d40040e1090f80480e91190380e46c9070000d1030945944e1814144076003920440c1984422000500c90350109214036a038040c03607814400d16001400401410b60b005074405e8000b480340ba001e0900300c85004400c100708a070342c84010392000d004545084d1540b0b003020702040c5c5034240d1268080048038000034842d100800142c4500781001388c51400c00c00580d000134a941414001d100700411b0581c16040b4810155100e4070005450355100036031010781f4010800c010381001000f000802c04203008140f100051a0445c0c0c0125441c00180086405080d50340d100c9050800000390390030741304103100100d608482950414121082509104585000d4510340241c020514800071514004c030001c01f100d000e911580742070304070940d5041080c0c07040d0030005038040560071000411022540c000c0100300b9020920100f103041081d08a5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 877685485 1250 877684235 877684237
    0x103060b0307150f09181a06030c0405061321030807231305061309050a0c05040b0a020114071e0f20010e0a03091d0f060d0305070609030320040b 64
    0x61a1010700a009100c0e030f060b103200b1202580a080703925070307009901d8181c41e42d2100a01c0f80d04201f051604811640e44a64a00001140d0041001011841c01e00741001d082040700e41c860036031700c6404902c280e00021030b5040e8861103402c68002c0010a00e1b07c8140c0c2c2005003642e81c009080104000c0041000f0088605420a010940040d500981d46920149100307004d40344031600025800b840110302c0440d001a20400c142c10344d40980003c3c4542d440e0422403900b541c1c0900c1c00800032582c240800c0c0000a500e401034000100c00d8400441c1c900c000e0304d00780149500c2591607500280710042c1c041703c0c2d045c010889047e03c010524001210048040d030007031914000303001800a4032143d0310000121402500910682d8020509442004076249405000c2451501c1201003c00041c401e0002d8041043d6056108002c2d81218400b280d560804012084030b4100049040c0582401401c0104010b803040c007940511985000400b00c6648111b894041c804080c1e40c2e0700403200f0171080c028498120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 877686735 1250 877685485 877685519
    0xc150203030f060f040518070f08060c07080d110d050105060c060a0b0301061d0a0501050d0804030f0201030609050f0411030a050a060b1807031505060711010e040e030a080103060b0307 81
    0x2c100541a21860001203074540c02c4080e581d84070381410140400030026100c2540120400d00c2200d10f8030355541ca01c854682803501c106031281e0044800181000f90080003450400d100314402840d202c4500c4408040b00c1803188607000101010a01403524645445828003421080700c0250a10394040030180d50345000400703c540e01a219032026440f40c17403d4121002521154400003108140e070004502c02c03500484221000361f041038000101401c120400c000240d800c544034502d003600f141c030f46001020f14400d08034101699040000b031441c0a0380300b243d0144440d9480d8140a04103410706c041d050100742061440f0b50002411400054000101c0c25a0a54001f00c04184c01c2d1886001409040004011091842c0110104014554558010054441c02600c01c044807911407081c04800d0040200041601410141a184544c024074208076000350007400880d440c020541038506580020201703401054580c0018010094180610f46884070158010304400d0301e0000340410044c910 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 877687985 1250 877686735 877686751
    0x105150402030c16060605040c08240603040803340908010b0d111c03050a090f0302130e0c0a0b0a03060509060303070b0415060e040209131110090e0f01030c15020303 73
    0x70300c0c80c60420511b50020302c001c0400400130000c2d505071310400750541608407480c002c40d000c0d00506512402103a10400c40444000d48054115540ca0340d03449481c0d80040d000b40010540007841406106850501c01c80da01d64104942080300b0004902404010003900f00703440700e906145c1e81020540300d400446000b15004506007011008000100340c2d0b0284903101260b50690001c907400525801c20f0041c0341080f41a0748500040f556043e4454408119000c02540681d0b155000340d89140d142d000b880d0703000c10b103409603281c038039001d400210a144194020028401d011898a410036014422400140307401e0b20600c0b103510b00800040d8a9101c0c0c454006c28401c003070404102884601315a01c1c03040242c40344100405030700d400c02c0411201c000c8400320f20a407145000903020303003403411103510850760010004503450015000c10002d00b072a01030315070070411b6060700024400d4a208420340500040c95000949505604ac4200d00300447c1e04401920b440100802009550020880b60700c0511 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 877689235 1250 877687985 877688017
    0xb03091504141b19080d141326010908160303150f090b04020301030c03020d08070b090312180c1c02130608190b0103150617070e0603070311060a0203040e01080105150402030c 77
    0x5041805800c90103400000082008441c8c0b01191072003090040c56007115403000c51400d01915460003e00b41e0354680343c000c0c411081882800280810350545908040c030909000c14460404550122101c1c1c90358002d020f81800c05400700300103000ca01c42c0d41c03000c84c1e0070346065203950b0440e01c84141c410841d00c00240100600103517482400204420f8806190340b0802945150505a41c82a500d405c00040e14000501d440d01082035203c428400d054009050030182071070204035030810100881200240c1502d0245103128030050350b40c840c0040360300d80922000602c0d80c0c02c05a03140d2801203103c11003403d4404514440303020484c0c2124507411a90b01c840002554030a01c000748000c0c0c81194820344624540300e0748182c905c1c0000c1081800e0700c80d0035107088400c0e038488040540c0c640710b03480080c01c0030545070140d041d41d0401a0040140200500441e444c046c0c0e6007200100c209000d07407082040c2d075559028080d41c5050102c2d01034505404560035410b509280c031141d8458410b8a44400340104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 877690485 1250 877689235 877689257
    0x3030612070810020a030c0c03120e011b020102071709090103060213050604080f060a06050d060f14090a030e1009090903021c03090303060b03091504141b19080d 71
    0x103080001c1e50103080400c0c160340e044416074103039a0280d00a03107112404603040018606000d44502010741c031864050782c030200007250806c02c0f14000c06c14410b240d0328554803000c0c14003c80c2e04034220b1407031050701e5030300069440c450ac0c20003c2c030300040d143c0003019407082000810b1082e9200039440381035a0704004016500c06136134180c54030076821540041c0c3c01c13040224000642c403002203040400852103009079121551042001400c841d45170080c6d0340e0000303044412a010a6495001a2403071001c501c1c0002c010041d46c0040c80480c10032100b180307569200c61903040030152700100031260b03850103a1b000a100d40c217012014240d40e02c14082d040420f40e80c0c01200c0709142c420005550380c102902c070452130401e44010000c0c040d000b840c2d01900881e007019400902c201c04101201d1150441a01401c241403203152000110540944280d0340280c0789030720030410042c2840807800d134840312005200200b4881003400461591100e09556011902c0c900f08182c4001080c81e00403440e1300d1500700c2c03c0c02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 877691735 1250 877690485 877690519
    0x504050c1201091208160c210c081209070e1014010c24110906040e040c1505031b0a0839180321070c05092502010e030306 54
    0x7159000a400060020003001e00e00c3d0300007600c0c40c064541040d43c03145202030f280e407da91703101c00681c002300100c4654107003100070b100142c408071102d02d03107262500c07810480e503d880c841c90300054074862006a03068184041e941c42040030030001c103071613607101c000c506e802c00c02e5610710780e801d00c510040c400a508604416070721600f0074001d500e902520920041c6180380422145282c56086070543c1860300c81d0300e0884504410540d2140c50000f48058602414a02072080351036029100319010070240c0c202084101016035104510b0409584881d01c91070410000c0c5002d110740c0301d05901c00103007001310f82c842681c048d140c603502050350554100c012607140811085d0502181c204000d032445181040740c2120001c000b03110600b014081010440c420b0010161600f4a0183c6094500340005000d818010940c0c06001ca02d40103019041c00f5564034000700341481e00455850034100e901901640e01c904c01c080a5800c0341c00540300802500c1c4480c10016601d12025106600c10802c21100c0c62030070b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 877692985 1250 877691735 877691741
    0xf0c02040906020d02071103060601050c0a0818060d0f06090504021825170615040e090a0b0702210405030703020103020906070210021f0b0d06150b0a11100504050c1201 74
    0x411005000f15a031b21503900781a008140f0700010148a0b01504010400381d40c0320b0400d030b46084e441c1c070000c1c100f20b5580d951070060542c8260b1860080c40700c8d192580720719580e40d0016041d2840100d00100700c041102e0f1850302181d0480d0488003801c3d14040621000d600d81d8103d4400a2031020f10381646515240d9452038914120000c04c03c9801c0311000b80000d541c1d008101e0030500418803418500c03502c40900304006652480103040c0c0840741440100003034541c5038002c50f00b00c0b0241c1c0c1561a462904e4a81107000c034012100880940d1000502c1010340001501c441304200440f42c1c05402c00d820403000070345a40140c840a4105a0003245410842e50340608035405940d008003182515044950701945031524a0b2078902c140202c5102010708070898007914401c2100104800101040e035a10030703008240103c4003007804d03000c1403c0031588845003c0105980b41680d00d420b00542d00b5002464034040a9041d50003015007082c0500000400c00100e107513190200319880da855048030b1000b6801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 877694235 1250 877692985 877692997
    0x15120907170a030e060f37080708100b0306010e220b0111012a1e02100c21050903070c0905190b0a05040236030d0f0c0204090602 57
    0x6a84401c02078203458400020305403905a1203925512080c0d4803e0081058500a086290794030090030054203a400050584c6d41d142800001403552480741e58034414190300079052022804124079905001440b50044a2154004024810188842c3c01e0a400e6020b900001e00b51606105440080d10407070f54030070790100941e0740c001004152010350700141c000540b61814400b40070450f051030440c8240e0060081d0700b1420003c1d070003500b088010500030300c0c000702080e0f81d045c00c00c61035255004041d0908030240d000389800d5170050980c5520703500d0400441e040300b0100390034000c5000140790941c000c04d508100e040b1110300d0002d110f6559128141c00c5103d55400103241c00c00030741002c100b0901e60750140c1c0c06003192002c10700c03035180c051102c282214241c882c0260f1280c2032800800c200c1c50150009c0258007101811100949541915015110300841d03001840250700da8154145041c01c00071440144c40d41e14103001c403910078400240c12344100340c3c0c02034000ca4482d01176005000d425011122 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 877695485 1250 877694235 877694249
    0x10051009091a01050904050607080a0b030d0e0f0d150c02070824150f190503242809080f030106180e1608130b010308030403030b15120907 61
    0x7104440740e262041c54240007124020b55541c1c620000310f01400e11603001d5108030b1f80500144481d480311202581d00c1000180000291903c0b400b031400c0680b001d000b951100311054441c03285215a41c000c018261402e5058280900c51034126080860050210b02c10324a003100740010350104400401c9003001903c1d001420503102d012050286440000707180c411101e02410018019200d84500d4130b00e0a12282c0301079405030941e040e01c0082d10b07060050060382c0106024000c46103644030003190500d1903070f10031010903480c844104c03111140340c9911a9448003040e252411201e01181c852011140f441d085a074085959503403c108100084088549501241141c15240d40e500d09000301071031040c1041300802c82e0b12800c0081e00140c1409028003842c00c08220002d424025807040340d100a004200060f03410001441e4804a440e100d4140d001c0c41c06020019602e14050500ad07065441c0381c1000350085103080e007030040b16031050050310001803d003224110140c54a000c01460000c0e5500181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 877696735 1250 877695485 877695491
    0x170703020f030a06051f0b1c05061201181e03020a0803130c5a0f0824070c080a120c020718050c090d1a04110901080a020310051009 58
    0x110500c22602031098070090380c6c168400c1c10741d031204405661030048000440c00544045181103103040310360045548000c029088140304940345003a10709450443c0102044403080041a80500c400c0d1066411842c03c81640301d144410300d550002e41d920403110000d01b103550040302050b5107610781c4411050860300881c02010043d180e141f212040300040400605144521110f80c0740c00c808480003074142204500200869480c09008040c0288503c8804c01c003160380b6a808501c0c4420190200094460000242026a141d83c11149440044610a800baa160504102d10a90f20220200405a01504594035004910026144522542000d83c21181800907000000f0b50024044003200e00c030b0310758040541c10441c019012035005480e5200103601c2005204c1c040c5c100040101c07180d510811440714800c0640c285008244e100b03460440d12040c0d0200070580e0340c0b600003511805091010301401c2c41801c654002941d0b42090101040101d4880c130000e03030f06064a446034401064100418 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 877697841 1106 877696735 877696741
    0xc11010513180609061a0d0c030f0e10060902040503071205070b0703090f0608011d070e030304260705100e21010e0106170703020f030a0605 62
    0x20600341d4602000020310b0180d0403481541085041c840001d4042c14484034506950040c2c0c40311014040311805214071145070402c6501c40310710b02200280031103075024298082c151400c540400c840c500652003500e1080402c401421041401c03082221548640303c180481c007442c01041d406500000083c0401c0319107801c1c02e05440d0060303044442a40e0740d901d800d50f080d80030800c110000b500e0381d2030030010110340c00309040c003a05141c02c021513a0340c14220000380365011400700d50391001440300840c00f03090040d0000074007200f001d41583d654540f5050000303000e41b071030803030003d420704142048250000085108410b5480c02095a014013002030404c0b2141030f42d0104c0154462183d86a85014003030818a0b1241d1001e03540c000310321402c1464400d0308492656000561841108030511401000400c40314260b82d4100c0702400030f403e6900c0840d240c041d0016005001500d07000034 = true := by decide +kernel

theorem cover : BRFrame.Cov 877517985 877697841 := by
  have h0 := BRFrame.cov_init 877517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 877517985 ≤ n) (h2 : n < 877697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
