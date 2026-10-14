-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:38:18.452464+00:00
-- url     : https://prove2.me/submissions/62ef7604-7887-48a1-a513-7c34274e5491

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 376258992 ≤ n < 376438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 376260242 1250 376258992 376259027
    0x71508040f060e010e070f0b0405010c0b1003150227030303070e13180209010902030709141c03081506090630070206010321020d0f090b160b0105010c050d 68
    0x25001c02d141c0f40c50a41c1c07049841c00001d40c1081c04200001c00c00099494010b1064000041c109468200040c4c940c0d400a034014110041d0072000907004e540c40c00b80301c00910340c0920501d080d82050080c0400039001034050304c0302c074003050328412160b0b03000040d208030420008004500c1c598440c0000c40d545408015550f03004060700701c40c024803a4140c003861301007038802041d260300750390705004103c01e800c41079106180072481002030012059000070881c1c141d0f800306404664107020b0401061541c1d20303a10300081c0186101d207141d42055070250030750380584007803280d0840d248209003c02c4024410301681c0ca52098003041101e110b00100c800080c043e11006074421410703a20554201101c020440305200160041001401000b407190140c09a2118480c462120040005800707941c420761440ba00c1c080c442209684000c0714450b1155070080d2900d400c40a44803407011501c6042401d81210845540c448100040354952003460440d00391034008006101098802030240c5001d901002910355 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 376261492 1250 376260242 376260251
    0x201360b03130809270a06061b02150f030405010b01030b0307050f10030207050d020a05011b020d0c020a090606020c1018030f02031207030210061a0706050a0f051602071508040f06 79
    0x5e034000780341c10503071031683c0b81c01d04c1d1045803900780080c108960706a040343c07051200e4102420392504400c0b010228042c1d0556140f410b003410800102044c1c00360200190086200000b04001c101041d000036026050a0300e0920020300b5030000c15880341c03014044d413034110702d035070900391100d2500b40c80155103800c140c200149000d081d5120241881754400740000964072420500c405c1001c2440b031660050b03101040158140d226400007915400c812080380104084461a5030170340d607a801c1b04c2030051509520400030603999074000307510340054081c030500c9005c1014009135200d00684c2580400c81101c0e45022401c1c1c1941c2c0c4620142d60300400c26030b018814070700d8a03000814030000400b1441d021f50000c141251403000314005445d85500015025601c43c20041140e542940945901991240011406079204444c180040098586105000b802c14007480f40c104a03a00c0324040800c039680c04c1da8980c58a6450304441a550840780c50b000410032030010740401c1182103050151342c0328050204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 376262742 1250 376261492 376261519
    0x1303020303040308211003030302071103030c0d02070b0315100323011e050f01031107050d050702030601080106080d0507030c0b071d0102010908160201360b03130809 73
    0x3480d603007040e0002c070396415000400c28254041203c00c891050028208000307170380b802c3d10180d201050244402018580c0118003c0100079286001e0590390304040e08032500d804c0391302d88080e43ca08007194400050701401c100801d05c418900100c0b072040707113074424000740c64515405000c2204180d0602c50308042e13944001102c580c00e501c1070740c80240c045220701400c95040510194540030028405480230302d1050042015840c0d030480802c55180034200003c4510307613944089804d10401c603008200c3e0141050304c158961b003003030141a00350300a804071041a83c9845400b8201c50141c0501c2c4101d40c418070003180441e00c254018581b032482440c221540e41425600e01c3d0381540f00355964008180341c070007036140c103180901025000210034402846484019100e0381180d00c81d14903c0215091010010b505590050032515070807040c440c0c61000d070030303200b0030110340d54070300d04601c0309203500703600400034480034070000f6039006607260300382e8100c8909555280c100550045078007a4000448a40380c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 376263992 1250 376262742 376262749
    0x2090f0f0112020a030501060f030e0d0e1306030f0b10080703080f0c0d0207090e0c090103081e030f1f03110409170408030733110712051215010f05130302 68
    0x3080c0c4e110a945010500d5410b040000c1c05100340da40d51881014903000400708440e07800100c001c0c0404190403c00b4600b100070001c2031020300400080c41c1e040d400d05000004005519000160b0103005020f5510192512000740c090502540306017800c56200d4035050002c251795a00074000d0120801c0d505141c18040d016450514140c0000c0364054ac101100c1001541000e014010b64024450040c00e108036a10000070890941030002800489002c02c40303810b4805518400354078054002c1c05981c03203140003050040020802c40b040440100d444000e1040180c600701714405807580000f80100c0c1640b2a0107001c000c2c40c071410255620712007070090f0505902d00d18010005048001c0113143c0d940e00c0360501c440c18203c11400012842640e0380001c3d540e45080e8003800e0807460000001c203480071a0301e40c0c502c8900500e08060120881d050110004035002001001c0b03408219000c42010707521507101c240c00c88500000c090228201d0441740d002c440c8210f0081819843e02907648207281d4a03034012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 376265242 1250 376263992 376263997
    0x516051c0c0f02060705030c04170709020412060b061305011116180608030307050301050d061b0305090d0309030e010f2312090309030c150717040906050402090f0f011202 75
    0xd59002c901d00c8414050302c142e06200b826031010041c1407851550401c15a00a1640300b280301c2c00040004020f006440c031a010311404004151021065460301d840311503191411034a0901250981c0c580f10b00d29030705081400555060443c070140603000c0c02d16103001510240d0171000410424003480882c42c0111a4680d0620007600c44240690641080d000c40d000403070704140c114503c130303030f0052080000c250360120459054070301c01e0380c0025584215107030110140c022030211f00c0f050002520111401989070303101600c1f07000303007404542200680a605038111190086c0140015800704040b40360742d40540c295106052041c6041d010194500e1614071200d44d800301019009100040ea0008510f1020801c54008082d907010f5490001490f0001c1c0d5180500c500b418000d5800c1500c400e0410900001e6507074103600890b610280030884412560241e20600554104500c0c2035004580342c1054401c2d6265260f02912540303482d0045020040c1004606480f9810441c082d0040c3c4a014542d002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 376266492 1250 376265242 376265261
    0x204060609170609061308130902071203090203060402012708010c080919030c03050405041b09090b0607080304020307050d050706020c0909151803130f090516051c 72
    0x251504040d0410200c9844000c02d08900d82403039014200b40f0162840c04546550001641d00d0402c0304c1c0e40c102d10782464113010701c802101d5901e2100c6c200180c580d10301e4000b409214030540b0400900311030001e0907411103001c10b00103905a8400c0c1c0000740154060301881d034101010358180003501aa0080340c12121100707400c6440140d441c0c110784c2d98015080b56103590000c01382000351680101801d8400800c02c40008054100001c1c11240c606144c000d00464000d004060024002c080110501c0c2791280350290844000a080c2540012007036024800c506020400030045441e11006031201c03000b030381000e0310030782e80b5000d918000942d5540703204810b6441440703007000c0d14180c3c0c07500348081d040c02c0450304194002c240d07400400001c500007281c9601400004142c0d032035980c4070807840300c0384078a490104852030321000921100640c0a00c121108513030303245002221242c2c503101d030481600c006494251101c11121070140180780204054803080904d0144800504130b01120b44080d505001c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 376267742 1250 376266492 376266497
    0x102060a06030b0a380f030c0105030a0b21060612010509100914010216120503011203030203070e0a091d0a0512071b15110d0816050714060115020d09091802040606 72
    0x3561740300542003100e1104a404401c5000c0c1483c2d40b0320f140068810301c0014050a0040d42d9103a081c001664bd10440d05515808480d4401600360103103030159440c1c00a403101485511009810100713100140905813007482d0303c1000e00043e0700300c0d06621003d0000034074215562072620242c0308400d1000d00c047c2100113540500c000c0c6500403030520100601e45494040c0810a0401c010b11081440507424208240e040c500181d4946c1c1c0d1101c01c540001034072140c07540c8000f404500050400494011485201c040ca0304580e00c998100170300360340c5d040001c80080403900050502c000007140f1402902c5c0b880c0c0074820241d0340c030341001100c004204258002c00498500c0540c44003015900c011841110b0b80051700600d40c0300203040c005000f04030010655100c00380e00c5509140c40600c07410035a1011648494640043d0811454541c0c8801c005d0040308444070301c00480f881c50a00c00140344e002100e40d900c404031702900307142101001d0200c0d000041481c0104d40140e60040e20703244501d00043c00d465 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 376268992 1250 376267742 376267841
    0x90305161706060901052107031b0906080d031d060c0a14070b0604020c03070b040503030109052802130b0703080105030705121e0a050a0b01050102060a06030b0a 71
    0x40030340a04640941116281e5001c0403c002090315407062040c10742c0d43c110f071355515048441c52035454116604000342401d000300c2c8400810006010318014046102a15400303000ba02c84003e1030886010f44034283d981e0340070002c075062080c040d6101c901da604010100d00d80010403c15079900e030090548200c090034a00040001c2c92551041464040d01824040b043c45e001480d00e8055801c407000d41460311507075002800204854040080782c1c1368642c481102d18407850a802d205407213030000d20a641c181410b0800041c4191030151030040780d448400c079203488144184100b800250482c424040243c0000880800c504051a0160580c0c0340b103039441d00300782d60402003450b003014296400103000308002180c1d4500c650340801c0840c0c80049000180621549407603d0034545150b020700900a40944040c05080c0155140954180c1e64281c08640703454594007041c604850507031102600101190000c501040c0158100c00300e034002c5075105115102d080e0503841c6000313114001e040755a000302c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 376270242 1250 376268992 376268999
    0x315060103060603020c030915160308061207120b06010201090c0e150a050319052b031404110108090a0203030a02010f0f02130e0a0f050117010f050115050a09030516 73
    0x18000c82015080914081d0b040401c050046da65a000d005901031050780d90303440c5404004182c506680c1985101c41d40704040050f2030801520f200820394000d4002e0406420042c030500c00001e00c1e00844240e5400a84071b14025141c0030f01e10440603200e94110354a07244442d01190ba080440c00c0a064003200d50030a5090000307143c00c07560f8030034640c40d001303001142c402c21090b070300450041c20380c0801c0c09001041818600c0d00341c0c00c1508480d441510f071140c2d01e06220300a4100c1c1c15074000e03a80c00d901e08000e0040d800d159035891043c1114024415030b81203078160103d5110b455070a030001002400c07158404003a5001a0550b04218442e40050f951b800842d81141c442c0e00844032500e4049104620b840f410242c488500046c1c0d000340c1d0f03203950044000c560400401e50101d86242c40950b0100665611808201e100000b5490b10200c00d40c200f40709114410014440c881c104d44001424107084d0306403a00640faa40c1103400c0381402d12070540000004141e0621044500c0e61000b070300705048908 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 376271492 1250 376270242 376270247
    0xa0c11150a1709030a0c080412060e060106091211130f02031005010e063408070c05042a030f021809370b030d0221090901210203150601 60
    0xa00c03100c00c20310b818540600070000b0021003165a204464648400b420741181070000c410f105507401503440852040e018424031040360b1019546a2022003514041c1e41d841804035000e01d114000d600c04c4003103440c00f04002400405100700c40c80000340402860320303000d895100840b94401d120510942e0004200446000365005444c0a0502400c20440340001803011031a43c0c05900c00c0320030300740580345010300d50308040383d0414069030108400c1a00c410aa2034526125006254215080f07a56118080340e180ba040c00b86c400100340c1c01c0381c41c115139140824010200240e414210041c0b5030350b101e0000c0055001d000801e10f10001c06482042c0c09102014040f0005000f8542031118540e101c0405204050211802c0803007600d40c640a81200700c080310344024407150107865450711898165080c2e083d0081480612001e00b074140c501e006030140d11138045442003101d001e60007255072005102015074141d042040340315581a0070801015503000c2841c001e840ba1001c05103004010411001e982e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 376272742 1250 376271492 376271507
    0x10309020a090222090204060c08070c08061303030506010503220215070804031502031003120e04060801050901050105030f2812050c01050a09121110020d021b030a02030a0c11150a 79
    0x11714410451405140c054000c01d40600b5050003007280c100043d542c42405413501c001405010712800307807aa03506080d120725001c08490641180800d00b800000b804560095003aa48134030050005400100c0f15049005200b400428040741d01040190f00c003100c414a0318044d002e110311810900da921804d500300a910040341558020500e401002004801e5071320070310150490740c3c8141000c1215120030b00c192007040310048020342081c501f5400107441801500f10501030240d810003009540d0f210380034140c40f10b10340c440000140d481040301010115408546191240081e0b03640090b03445647d64080385640905811800a5130104100c0507a40d000e03c00c0a0700800b0105081000c4101c0c2c0d554181462131a0110505000c444044445641c80a0100c002800360703082d01159910750028888009400070640f13807880007800d03405000110700020485104007404c5d0001c5040c220007020444640d4520b69045801c2212506006201d4a81e0028104000d000454094841c141c3c81c00003070200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 376273992 1250 376272742 376272749
    0x50a1b0b0429011401093305070506070e100806060a05130b0408150a05090c060d0209040e01051512030904021c1419051509060103060503060408070c1a0405010309020a090222 77
    0x3051f4540625a41c69003c0da20340408000180ea400004031500415100c501070684094001d014480030803800c0d90f8480482c00443d002103440e0b05900150342c1c400c54940000b181c42d0707030b00042d0802c0746850050003800070309051110089099056601c503200001260440d900c203115a0748543c1001300031a01c503c00e000d0303005244107010040c9160143c0040c1c1d41b403510070007047c081c6000103403403d2107006c0344e01107855415000e0000d110030404d00030301c1402080116035414840e210b81c1c1e050785040c0380000900c007a40ca05000210b040104641c01c0000960000c01d8007003114451080101101c400da004a101c041c22105130000e161800c4451550302c00078400c0601071a03031901c0104031040314594040e0614a00c01d0b5441c40640d6507000050300102015040186c0c54803503401040100000c7c18004d00b222481390500c0c3c5c0080b5035a4403282210102d282803c003949200703100920003544207512411030b03030380000c0521503920f075208020307401c03030780b0005d508a60540d034041084007003480a89030f00d004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 376275242 1250 376273992 376274009
    0x80307030e03070827040504050a050105060102010b03100b030a1401020c0601051c0b0612030f09100905010815030a0b070c121409120a080406050a1b0b042901140109 73
    0x2010343c15500d040440c40350b5401e4000039001d5070107003110407100100044580801400800c01e038201410255500c1400d0182120558203100c005100d1b54030602400b09490f0b0003400070040c904420101001400000052a4140c490a050030001c95103d4446a100c440c0030f100040c0e41d400703840692420004160004c9000c0d0b101e00011000300480e1107441030b007240c2c012000c0c1300d442d152034000a500c0300649415019500c000f290a65036001000300520000f1801c489113030080360a40c40584503026584074050200e1003400016000000602700040c0b5198000d064402d0885a41d03210200028199004800901c1641200e8100800031000706010883e900b0038004104e0340b4100e680c3c0c58426034009901443e4422400410300d40200151243c1c160701035401074071141c84540c0106990400030400000400600d80ba42d05403c0d0310407002c2c0465000103000c102550360340c54107000d20501d01c281d55502c1c01e500c0012019000225a4140648000102c000d403480d044d02c0010030b07107583c0340c0182c1c8a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 376276492 1250 376275242 376275247
    0x60e0118032a0807060b0d080a1101050f0f041e0c140306180c0f040209060a0f1701080709020a05121527010504090201141617270406080307080307030e03 68
    0x454070107010781310303032a40c403e20201b0b1811644000c070700301e445d009070700400d540c0b00810020130068015000307150300c4c070050000304131966640740307003030003a00c0151220461615000003003408696200c540761280320700b1a10240416210395511038001c00c0d594407003284144000e850081518040c0301c1c03540c012000c090812400500e001880344c461149060041c410003804560350416100c68040d02c80001c401800a038541000d607801809014070321601c10300040d105903044441e100020341d441d050b11203a4008104481c245480500294822032410052040501000019503400503070203120340c0a90342c81582c0c040c101020311015035900c10a001d2804a51024402c1e1400540f40c518110389084401082403501800180c448401120301100700d00400550740c079010810340b000340c4004e407140300d103014180489a103040240c001c0c0f0b002a01c010400c0c5007001c1002d020010318804280004100081c115902c42d00103103580c1c050041240c65000100421580d40c3e094130034000e109403143c01551 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 376277742 1250 376276492 376276577
    0x70f150f1b06050c030619080606151603020705100c033203090703110a050f040e0c0303070b041209050a0b0a0201020d050106050d060609060c060e011803 68
    0x10912114000c08a00704405000c48800424105600c40e40a9820541c2041541003100c0416880c1e403040310001c2c0140050300d0a6152083e000303026104684c2520003a00142d150072042088800205040c070854000c1442300c0082a002c00c0b0004410714407940050005d40c1c6041c051010030038481e01d5610901908040e900003081d00b150000f1110200392071100c1110521011003101021000710014110801208208124900041001c00d89015000c40890240040c0810281401502038650424503010040d082410305400450400614409a0b07061900c12400f0915540140d442942c030b0304251000c0c80180002107901e00490000b40c640700030a1818880403601c00c5415205001c00e01000040c8030802070320030340c140e40d402c00307400000740181c0d41c0d1404010b1290b0000d90415241c0b80c600280001c500d0301603602d8504480d42502c4159400486481d0a8000c0c0700c1101c01103200e540780c0d000e03001d201000c600352010b010700c80e80310f43d40c03c04a8810030100c01c11100064949201d1400c6010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 376278992 1250 376277742 376277747
    0x1050402010239040f0e060f09010c0912030e040507030b0f1c020114070b040c060f0f0f11030705070b040e0f040201021005040615030501061a0906070f051509070f15 73
    0x220000c0c00140460f4044120307500820f0042810100100e085458501070750218030000c04d80d60301030b0200d030f040c1e0080c13500d800030080d088660b008001d4000c602090020084a61070700d00944d4854000d046c60685240c0c1032004c0380590b0401c4a0794000269140a2841c0c01c0c6481240045021016109841c00c80f40401a04441d90460100070f410320032040040d1200b15656411214038070750002450300c442c01c192904c070f40c1ba00410700800d0702180402c1180c5111a10a403400394140f980d82d5259291003d1000c019588211075155808860000f0000f29020a000b0454600108074081d02d8130f650b01d14002c981500c1e5030025040d0030310180c0030070178040503030b03400940003085c1d03d4038400000c0c940d00e81e0b14102c0028404a40604001c070f51a50001003132207410b50000382212848102c0e104441e03551a21200d1070301c20303840e055602c003005024543c0491400b40700d5890107403050017210001c404056862042c45d60890700000710754031014050288440e40d4640200030300032601544c443c000f124001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 376280242 1250 376278992 376279063
    0xf0d02011107110604091103010e150a0501080c0c071e0605030f07082205010b03061f0306020c030405090c0703021b0f040c0530070f0c080c0c060408010504020102 72
    0x1d0003000a582d140c18180e55135004890050190740c07010004000e400c625043c241d0402d01c038540f4400c18140004869440c40c3d038501d035031480001c100104c0541441c0041d0b8004034040c0540d03810300c00030700400203001070401190b0040d040b1100d0400d901107601c0740d41c04000c141d941004003040f105000f40700a25140c602c903035411800c0c908184500e07554403c2d241d0801c40590207107424851054400c0024840c1c190700c41284d581e415820b0b05c0c010303035a54824294075503440500c6c1c0a1120816010404150765a000c4c050144551060302d03c2c02c1da0701c100040e8032f820142d8458058000004009041540402c01e03403450014001002078265040c800240d1442400084180280d8a071920b20035101c0c403071012190780388004008011440064184a5400307000115001d450040101c00b060813140110300314400c6045a507185003d0b0485962991030603041f1510380e9800b44a45401801035030303150b0000e0310141c5864400000c0520306400024034203d030480c030036040c00030222624010451100c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 376281492 1250 376280242 376280257
    0x315020f0a05030c0d0203010e0a06080102090f0609040e06010303080702061b1c0b040606110c0f150703020a02060304140d030605011e12050a0c0f050c07170313080f0d020111 77
    0xb0025240d07640c0b8982c1c5084d5201d00f44074982914400400400c040d4803c0c564a8000c0721601d1b000c0003003e444149041c00c03807040149043c0d0024000721003103910701d8154014442c84401410216440c6108040d00b07103410801e81044022680788020021090f0341045481d074480c40700351800d001007050072078a0406120314480382d8010b9504039460590711401c0c0c5c02c405080782d00035100300615960759100070540859844c02500d280562004100103141010390b00c2c026040c01801900f10f10721600207a84281e01003102101540500c00305500560703215070107144107034044c3d4941428480049009030a160a000140041c1b503e40042807140b0b9134040d41046160101010301d010030700c0b141c1300585e5003141280a070303910181444200004100b180e00051180106611031280b08034044030f054405020b0521648500d40c0425000c000500b580710b1134161744902c6d8000e4038502164000d1a103154245a00400c406500250700c00d40200c008001c1c8803c440d4181c402044522000134a5a51602c503905 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 376282742 1250 376281492 376281497
    0x804030f17060d1b170f0102070206040501032f18101e110601090f0506010207060509090a02071b03020102060903130317041d010e48040f0315020f0a 66
    0x5240b10401002d4801866400d444d1400e0044071581c401840f4485c40d0307600c000141a000790101c020b0990414020785255581c001c1450f410141031000440003440c04040c86104c0d45158040075070340c801c075007150a00713881c030f10703e2103950f2841442c6c8a01d2081a00c3c440c1507018040d0035120882060b030005801d4010180c114041008a184850865038400e040300510f00f103001d18000015401d415502c54400030f81c058809015603a02c6400681c0c5440240c8100e101091080007001c502d8130301205c015901001d50f450050510885803250030b180c0d651030601259040c484402482990b07010800d165020a415009501c0e2035181000c0c40d4210003184002011000004041200c1c5e94810b800c0e03801405101100a8540c0340c5403507520342c055000c2c4110035507440d010012405240b22069800942d0f48064200c4010002c06d00c0c000c000c01c41d0340610300070b11940002c03103a040000900d004200504002e20310f001114290305254071059151050a41981e20400c03412240b52041030581e0000d41650 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 376283992 1250 376282742 376282759
    0x51507180824160e191d01060503060a030f0305120a0b0f030316390906050906010512100e19060b1224090f070f020708070515090409030804030f1706 66
    0x801188581701419400d507010300f000403012442ca0503803845c00040082c00c1c0b4034803a550344d0f84c1c082030703a0360710080d1007298000300c064609201054031403600040c82480b924009240c500b007180b800840f900203036054201d054079440d400d4840e150107243d018140718100c002e146804020b80c401440c040d60500001c122003407005071100d40c6000d1040200d01e00941c9000c9201f004080e50300416682200c0c01107800a41c600340000c140c0d4100707080c006100c2c080603180d0500c2c280391443da00001400c010031303548010385207010100f54890501c14407401403030f1381d81e9414000070007501d4a8050350016040303030f442d046003404a00d02e04030f4880c0c1d803183c00205518140306004000342207018900c401040143e0031004400910040c0c0c80403542192140109680e00e8440002c60179040340c40d05060f01c64950300303070b20900041c0858505585888030a43e1a0040c051a0204440c0070900750761070880181c01141d92602008107150308101c0d10100f08440c1c0c9450000744103025203100348580060940d5000314105c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 376285242 1250 376283992 376284017
    0x6030c09060121140901050426070b09160303050c01061e05060306011707180803130b090f040e01020a0f080408040e070c050a0b0103020112020705150718082416 71
    0xc2e0b04c240c400d540c0c140f880007664a0038441c1c1d14080e14041e01c04951700701868810f5224080401c20f1003181c1741c102415140b9005094403214080708000d4000d00a80c01806031089411402e07100c1c00006520a460722a194011036003c2400c40d00d403a0301410340f010752150005003440d400349a0344252107007140c400c2c1e00c81c2c031140c004035841340f410104060f9001c240340a002c0c0c800c0c0c00024982c08248403600b403a42c4680c540c203849071a401080c0c00b481d40107040c4d980c103006103055103025043d03c2030301400000b0b00e200500000303410740d445000103a0041e540040c0604170154440d10a481043d010b0500307041c0360a283d030301c280d003a2044d4441c94404c1c030442000300b009688281c104c403c4403078020003110041a810b00780307403000c01e00070720041340420124454034450728014000c2c0d54000da08207000d4484403c0d01d0620540311480203102504020f0081803007030740490245d8415014020610003443c10709109408420804c221480000d02c500741b20381081101d25080c0d4803c444101146000350702b80d0311 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 376286492 1250 376285242 376285307
    0x9030602130f0603020403111002060402010309290117010c170a0b060705010c090e1e06180108070e0a060e0601030228120f0e060423030d0506030c090601 68
    0x1903000b25805411001d400241c2e5540368004d4000c0c0c9009840b910040d0203960b04000f030f50344841c020f045c00f58100a0015000d0360091b4030082c40c4501584120b00c441c12190891106020022140c441e01c2c0d03d5180184900d004c2c03810310084941d20038000700007083e20700307070302030b1155024a100d80761305140c00e00020a1101590051651a10054003072610f40fa860718115020b0040b40b00e000b0000341078041c00180d0b0f801c600f00154010401a104003103090003022840c01501001042582c02003c10b00900c10902c0d244240c0e140200381030400341100d070703003000b0446040400161000d100d07182010018400b20490302c00301d0b50070210900300181c0c4c41d100100c440b80b115442030b00030f07010388465050180c2d056801041d04203450102510403c0940310080c4000119880900c1202c42e980c41480000d0000c4c1c0003016602c842101d60700320001d030312000e060740c80ca1035000240c0c17280c1c643c3e22401480803904040100d0401740800703d400100c0341c03402c40002410074411030303009917031000020002e030722108 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 376287742 1250 376286492 376286527
    0x230a0b1f1803230a030801090207231507080c0307030f09051209010314150d240c08091c03020d020c0f0a02090c03040c1e05040507110d0e0109030602 66
    0x512201c80301c003403958908100e03030104602800181100140c0c9894812442c000c21200026035254840254503401c0c0701d000002500300e52400c651074008040180c00b2181c482c2004402004a04002c02c4040080050030a8901000d801c900c1409940c0c2c05200d10010940c003500d9101059250015049142c25103000c050101024040e21034041d1001d0003030006660002099008400e03201804070481c00e041800ca0030604580b80160002112130360b55540c9400145162101c0c0a207007a444c014690300e2100260458542c1e044a80e01d48d2114586c09260300700c200d0710303849808040a01549881507029010410b1034005000030186d0014810440000b96419a054074907440300b00c80e0400e10040c0c01507a5592001010b0303110b201140c00040c00300d034400302240d10884d48070080011080c45d0024008086650f4260010404200f40000c01c05896510034544a045e40340d90707240c0c1124003140c056003407501c034a045804002e160348004249907040724280046036031003c0f006a03200e52040c1681c001c103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 376288992 1250 376287742 376287767
    0xa03050717092506090504020c010204050604080106050f010e0d0b180a03210207020114130902180103111e090d12050307020c04020301030c27230a0b1f 67
    0xc2a03207418412140300004400e04580b500c030041e00c00c040e240c4100e000780d800491041c0740004001c214180400d0405402414800c0a080005130400340c807400003c80b16085a000381e0091b070b5607400c00700300d245051540c58407402006c1c00e01c0100c007407114010410908440703c01030900442c0a010038041c460040d2540d42001000d0292040840a49001001e42c0003081048612400000c00c1581004042c404c45034440d030305840700310320940c040c0350414082d00000c1d0145d003804050540010401c550740014840003c0003403040b60101c51180000d001c69000c5900404034500600c50b807185100d014840716460740804003d15204c00f40013000403846100d02c0030082c8950a5480700c1c1c0b01d1690480051401280c140d001d80381c1c20101041804128002440b01615035865464204411030800a5019100d000229080b65030720303030820200250b0f460508480803040d0740142d01c0c080d0900310b00025400c552482402d120078111200051001d03602e1401d80d40310b940c0f1000d5540d00f0540604500b681d07a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 376290242 1250 376288992 376289027
    0x1030f020d08181207050121020c0d030c0318260903010c080711060c12090123060a0803030c030103020f0a0e04050a0b07020102030910020c03070f0c14010908030a030507 75
    0x4070956001c0305800f000e0f240d11054010300811010450b40400440d039402691010b80d00d0f151440c90003040700d10b120b071307160071012000c075803c000c003005140c401c4c0100350300702800742c80100355800441002822111254416070804008a4403030300060b61007000c1481018444070101e01e058082c0b43d0402e0240705405889501d9841e04403284146500810710520031500740d10390051540300040403e450701d0080316a80301202d001c100c2442030746070422101e90011043d600001d0086880104034211483d0301100d0b0101101c91010080d95150a5040d4400350000c040650b0460408828100d0180018040240310b503861030100c00c195244d2200101c02450242181ca2040c02d0a0806640b03030000a20103444d02880003000600050050080703a002e11000002007010961000088009410160340d00c00c45000401c03000c1e000c60f80301440c007102ea078000d40085040c185409818541e40e03030944e08680c107204c03401c401080130580110070b44500c605541030104155961080031030701c0310313150183c040c003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 376291492 1250 376290242 376290247
    0x1611030904020c0c030606090c030f131401050f13020303090d06020705030f04090b04020c0c010c151a03070501020a02150d021b031b070b0403030c0c050a080f0105060603040b01030f020d08 83
    0x202e0f80070000e03984003042c00c04d8040c0c0301c0c580c95040c14401450011289943e813920204041403207000c510b2040340e8841e01440321007188128682d21800b80c3d60611000c0140c036912101848010781224540d5504402441d59074000b01c50f460317000c82c0c0c8a0084241d0f01e03210b9101c03180d00005014198048888150b13100d015a96510100e011000442c3c00501480e091540740010b843c510741000d00c22640c000382060001c000e0b00701341c400115100c550342c28040f41e01003406400740b02e0071445405240c940d030342000e0100341103582c40024107191000c0c03a40b04d581191b10030002507002d43c58000100ea03001a511500c1381d070f10103003a274501c03010b0306c02c5440291142d0300079800340c0819030b000300c007400b8413003040c80520f0012703000c891290340e440d03040380a081c001800400003000068025048107845900c40c7d214402c074207039244001441a03546a20101458114002d02050041e081c803d050748075104a54940c2035062a440e110301c441c405010041035005001e03038031001d65413180b01d071588040e48040391a9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 376292742 1250 376291492 376291507
    0x403080403120e0609061b0a0b10030302330c070f030926061602070306090803100801051b090f0d080c0d0e06030c07031e080411030303161103090402 66
    0x580004040c01a0000101c0c3e942d0500014a4a40d04803082c00300300520241c10220101c060004222941a084201e407090404c1ea2002400c1c0c5940d80348525000c070f00ca030030369174514240070341084903880d0000d50f28400340d04800d0018403504d241b0713600041c00240307400b5240c0e600e0094003080c0c883c4480241c0402c680e08028401c240e400418081271740d0201c0580f0205007418030318805c2c6520000004038407074104000040c283c000d00e00381d0a606004520481e5031035a52a1180000c07141d0381402620345610000c2000089100303403002d01d005000a4008010500c1c0c00e0504c5d000f038171000d0340e01c10045400054494040d1341d6440b000003250100070000c844a4030603203420b010039403041e28045120302503840b400c948180604d2500000c000090403840c59a502c50368444415441990100c061104c0d5044181c43c0b9810700e8118401e50b00356403514002400c0c00d040840c0d42c0101c44120900c01c5e80100200200c5e8580400550100030041c01d24001101141040e01d045018041e46036811510118000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 376293992 1250 376292742 376292753
    0x108061c1a0123011d090c04050a090209010e0307030332120106030b0307300510140124112e0b010207030c030b0403020307020d0803071d030a0809060403080403 71
    0x8841403c0c04000300020b0b00d955030054410520740700704091010303003811407613950742404070440760312540901c00e02c1d2070207845200040854195400c108815580032481c0c0140b540c03c000228003040b41200100b508502c0c5030703002402a860030a5106800c81140b50840380141a5800b003096035540100d41c03510703444d54a514842e465400d02c0b031040041c0c10140150034078180810140244c4014030912031400e1800d00d00030503407004e84d11042d46880d003602440000b243c814040c00da07064800c04000b01d140720b40c080c140840f402d07040e0004103000402c12000301d00004580c510341c913921900d00301442417164001c00c4d6424100c004c100c913491a14818510400580131040c02d044550b0300c02420081c17102200012680c030001030200402c0441d51400510215440d01040c0740c1c0700e4440d02c1120b18040c0c0c298045840030503506800c07296460003109100100d6000840808920403000d01c0e81e00c0741c08100000795903079511075005000b001000600c0806611044104d601858002c3c001319a915030301c1c0b0f0300c0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 376295242 1250 376293992 376294019
    0xa110714061902040f060503040c031a190209010e12010627050115090501051b01060902030103050d02061504090203070b03070f0f050f07020f0310060902090f0108061c1a01 76
    0x2010300d04001001c445124401d94070940c0d058074401a0741701116400d200c0d00303075078940c0050000e94030b180402c000000007400503120b00711201108100c1c80a00c2c00c02250030010f003d001440014941c2c0184910781c0c46907803010b045a004a000c54a0319054a170b6065584c0c010700b40c0307400803500101c00344d00a151103000d24030558003031043d0600c1003020380c0c0d0314a920105a1105819500013500d1400c04208540c4a40701802040201c02382c80f041c1c0080d0f05110a0131514558090202e0325008401001402020701161070300c260b190010b0f05151401450020b1060f0070015000d200f540c0c0d03070042c80c0554038108541d0002c0c03c041424507542c5d044c00480513103002072200b546070015440044040c6030905c01c1e01030781d044000311300709141010070503420058842d4484140d0354043c03080880090207072008bc05510001d00c03a0140041e030720200c40051152030703205044094107216900701401415220044d11a015440d18000e0100c40c00d902e00e051003d4488070802e034500302600100206034501c0b8041c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 376296492 1250 376295242 376295251
    0x110a030509031203040c0302150d05011202010306140306040b09030403050a051b0307030b0127050414010b0103060f030f03091205010b0319030c1401111809010515030a11071406 78
    0xc031a54140f1860000340d26200481e0020440b140c1d1304010401410040152105d182c24035820504087c4076400340012580300f64400429080b05401000c2556003511608010300110705ca02101101140702181d40c5000c00b600003440c440072040010303402c400510580b005503901000361119803103a800c00b41ea0344c1d44240d0380000034610341c2c0b119008030301d400604801140e0384084030f00b007681c0c644002c900d6500282021240d90b11181000001c4103041480340702e21a40c0311320002860f05005c5101d20703007140c0441c04c031541171619203001803000c0c1c02009440403c5a5104103811404000d62500302c40781d400c40e038010500a0202140441007000c19048441c2d004070940c00c5400500100345007280b031500740c181c040d000c074148801d02004100f104001411800c1688004036140940380c0000c07240303501c4100c045482084a1051920520f01000c0c075074010038048072542012079902260120a200141090002d10b070b907803080c400380035140f90030f8420054116540c850107203400e00b9165214001203c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 376297742 1250 376296492 376296499
    0x18011b020106050a0503072103021603031101050106020d02030f0717040b0d0b0108040305220b04060c05010509061605220f0e0603060f01090902010c050102070c05032a060307110a030509 82
    0x154042511b0600084460444410101022504a110005400401500200350210b0150a07000b25404070780c051004025880b90b0386e9564880001c2c91000c0c21908180c000c94219081400f24001c00b039800001da03044900d217650301c01d903580d1041c50070007001074a0080c00c00034240042400500301208034054207580000000134480603080360011a80100f04803030050202d0020b01c040080a030080b40b0703105180b2011030b03590400c99203d80758041d0540144d440f010000d8180351180081081c2805a2504018450024003050510420071842032003090440401c00c0700114400314060340808015039649168807480310803e4407508031035203030305490144d0054102803038041040b40c1000510725105002141545c0c005908003000031024007100130007a81081203101c0c510002c16401c0c4000d000062094006030f4403186080c7c00d25091201c1c0c205100c01004001d2440640d881010071454403411044601c0c076680d564124042d52441030a420359026440307211000000c141c1c00200900071503004a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 376298992 1250 376297742 376297759
    0x10608011a01090906060207140f0a080619060506030115090b04080703030912020d1112010e1b06040b0a030b0111030a0309260417190c050108011d18011b02010605 72
    0x4000c44c106445044c031409005900c0228104070140c0c10100400703107644010200144103510500044c2c9c0505190007000281e0044010b2028904822542440f58000070310184182803910300000d46c03a00051180c000c3d00341243c1d81760f1908520410389403010780002030150b51500e4031a0f04040d40c40c45240000c0300810300c0c0c2007001c1390145800d8031040f401a03009018201d0405640d58901c0b100307842d90300305a00070f04601d4084a1014007030256203104000760300101581341e03084401508001e00c60f001703207004410420007845041c40000c101c0b422480365007004101a42c48400403601c2d1103101000c003403d8000402c2c6010455459000503092030f02404504001604900707800100e1003103400980f00c402002c020411030350741400e07844401c0e51701d2001901d82d200c2c070038240e0850002411030100d502410445051002d580c011074864050501c40c00003204085041040e1002031501412181d1a03c2541c5103540651400b50091040038450040d42e0050340c910001c064040c01c0c080c044c461091004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 376300242 1250 376298992 376298999
    0x60f0b030901050c0325180e090d1704030305151003021b070f090e0a08070b04050f0a020f011d040f0204050f0d0503160305070210050409050702010c020607050c010608011a0109 78
    0x11400d4902440f0306110011030706807006c41c22414906114012400e02019000540b0301c00c02c2d1031103420041030141d403103244525203100300c2802c000f1061140b07814407030107800c0210360040d15610709902c00e074581030000c2d6a45031102d019420318503083c40c042d4008030b424100fa61055150f00503005000d9490f0381406464207058138141c4400590245040b0524200020489540076410561040d850f4109484511000751620f07403442c0d1090b68243e8900c12600288800c01c40c0400c0382540328146d03070015001e0b02000c3d0303000a80340403035400c1c0e407030400561000c0182c0d004101d031070206a042000700100060b44001ca5100040e4200d031240b54410910603446022504001503101000d6500002070762500301090164001010f03040001d804121060107980b005858200d245140515251107454a881c6401103103019258024551400c59043c0300903103204640010b1b02c150002e1036070a240b5140e03506d0901d028010001988408255070074401880d20306196086c07005400340083e80c0d440c0c80b9644 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 376301492 1250 376300242 376300261
    0x32505010e07080d14040f03030504050a060e060403060209060903060403020c010e060913241d13050c09060f0a09051006051c02090103090b0a0c09090b06040308030a060f0b03090105 80
    0x840340300f5080940c018144a2001c140b04502001c110105401658106502c03031520840c40f0b1100e410490205000040500c000d24000b0003050040a1030300c0d218203050780003408100d05006510000780210780110707103415a5941c80c0300f5280110800703401c8688038503060400a50790342a540c0e5035400f0400300540e540d41400d0040c1180e015172000780910801e880440314503030080c103141501e190b0b10800c20b80410110341e11240020700400440c07504480741d04038480c0c943c100b0300c0c0140941c0684144140e00c0740010b18081540135401c04101e030500c80c1e81e52404007080a44291030344050340009038200100f801c41165111034094805409480512900c82205440d00d110f406460103442004114a10502105400030520540189408598801c0c2c035a9540c3d2000019200c4010300c40d203620340701e60f4141e4402d210300000d0100b080103200351315508001c203200d4402c50001500c085000000900c1c2800c0540200d002801007500120160707503501810340d903941068941e0342c103a508000118014a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 376302742 1250 376301492 376301503
    0x5090d0b151207060c0206070c030b04050105070e330409020c01090510020c060a05040f0c030305030f0601030209060d0f060e160f02061501050717030a2408060414032505010e 77
    0xe58170f0300c0d101d030006001e408000003038100c2035045070700164407500800091440320302d49000700d1156001040f10f00b480540602a1203903480d4440c01540d034140700389007040400c0080314840180c42c0000e181d51044076002c480e50f1107503402440500e40005007115170602c05520000c103071070246064032425072068110a00340c0c816540301000690040010500300001c3d5030020342c2051003200304503a008103039603511800d00056481500401c00100400400902d5800c80551284003441d0442c540342120300054424043d01048900c059580c40140448561982c0624040e184182e10021189010f249103001d4982c00020000056501c0c1075003542c56000140c0b4602441030300001da0f05400c6203000449042d040640241c0381003641e0840d10f41902841d10055000e0ba010110120760007103001c41072050880d00c5a00f4203000ea4617101c0c2000320500100e221900f056006042d168440c403800402440e40c014684805040c40407044540044402d00007808c01c1c40f84104003e01c440207041c0d800c00d46a4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 376303992 1250 376302742 376302749
    0xe070f081b15030a0b030a06060303030e070e1506071a010815040b0103021e091614070b0a0b060c06010902030612060907050909010212011217180105090d0b151207 72
    0xb03a0980000700110114202459120208640005440e081640043e1400a001c001611010b03510001841810313854001d40710500f1a00c0d0081260510704240456000b2000303280c070b410035880e070f200701c8031581c0c0314000c0703030030103078100546d040c000d11100880140424280f0401c1c0d994460312501141c004110350a0910440e00880c0c503440f5603203103809000311510016820301d01080070002c003004640e1024002402a92a00f407001c9040100400281c6214910792000c03400b20424050b01000840d8041016400941c2040c0451404540700c02300e0b1460280d450b590200740100c1001144454055000d50305c80e078021120200030030380940c403982c1c480c0825a03080d03403190405581882142003040015400104000005241130030008482c01c003540203800244040d0170b0007000606000b28961002c000c01e681111071490030f0303100520b551251070a007413003d06101c1d011900d803000d9981e203418101010b400040c109580d1820508c60400412008169441503400c800d446042d600005440407d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 376305242 1250 376303992 376303999
    0x7080d0810030b062701030302010506040209030a110105041503020c0706050405060d1508030d091a13030804020d080a030507090929240307021504110d05010e070f081b 74
    0x905045407900c05283c0801000141c0207520142490b00056541c0071014010080e506030361025411464004d095400107031425118030700500a404083e940424419a030941c03050321609058040b00041e107090240360320100d405804040900c1251f50160010309540c614a01983c0c1803c1d103c0c00140c8081c0100e00400c0d800c080f05010910041e01c55500c0803041c01c000e10b10002c5410395501d046441c581c0304200c040e450f951140890010042c420301070074980382d8a82c1001c0081d18240c0791212640e2001500541041082c0000c94103540310b0760784a0f07001c1c58110030195507440c00400301a010b02001d40c0d101000800302d000002d543c00e806e1044003010080c98108422005c180700500c84c40600c0500441c3c1e00110400340d00c4038295040c0d0341080640740040c12141c4a1800c401e010381401040050900540c00c2107041100003240004450313000c080480d05400240400d0a10a0041c00c2a010682040c4215000400c0c0c0414940340c4004a82000c02194091042c000e80c440209007045034840c0c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 376306492 1250 376305242 376305271
    0x70b01060f0c0b09161d1b09090403110d0c03080702010c05030109020a0e03060f191e0207060213170708150c07021801030c030204060506070f120e060c07080d08 71
    0x103c0c00e01c000c5401101c0842211240c0c1500000c1c40d0351040d441d070041161045820064245c0c0040e856800d0b440b0780c01d4034058010a01d60b030450b26845c0708071801684117140550000b03007094000e82e20110030148040407980491b441341c10203401f00303c147c00e00394085484000010900d51050080300361410035035444a041d0f034a8080603001a4000d80c480d0b0052050028031518283c5080050078460058045405201e01b00000c100c40e100c0082400407200d50b042030f10358a9440010204404481c5a007000141d4a07100b50030020020f0080c4070320102d038440c11074000104c3e0b00c842c40349401c60714200e00c15188401d5550311040da841102003095540315251000060240c00380d000038280d02da001400c01e2142680700b060040800c5400d8104850707a0785000e0042c030941c2054032640001d0034054822500d400825140c1c01d5902d4042000148908c1100405942d4988260800700e905103020301001e07180d8012003805034513015140119002803090402d1038040b42e1207000301c2c60048040c64141d44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 376307742 1250 376306492 376306517
    0xb070801141011031b07050a0515040501050f0f0703090305060a090b0f0402010519230715091b0801020304060c0f120509070f03030f0f0815040504050703080a05070b01060f 76
    0x160f040c0c980b00340480481c0400d2100d070300b40c900703808058690468003001418850b800c2000b000384c10040b940019025581220103241c014400718100d070291002400c0c030646942e0607141c4590a8441c0300455400e420700818040c04250300300c07248005880c030507015654103035214021101268410400a0200b161044c0401e10301402202c005070000e0043c9006880c0c202102081600c0c050110801000038081d9864619140c108009010604080c04015407400c2141e45403c140302020115143d07100d99159000d00030040e582002c01c100c002c074031018410a9036504421170003500115001da4a03241029400e102003441110120003901301030702ca20a408d1b00f17500307002d4020140288a0822032045c5040818401c0c054500000118402c0e40c407404980c081c0d540090640c20004c400c0702c28418000306201e1a9540e00035242c03004d00081e28006070b030340e5450402d01d1070400558800b03802c6000c000f500140740c940c0a00241851801030342c40070896661110101c40400c240e407081c0300041c01011043c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 376308992 1250 376307742 376307747
    0x906020c01092307050f0312040807030c080303160f121806141006050a17152e0c06090b040b01170d05030402092a040914060a0614040b070b0708011410 67
    0x2d1b4100801038202c90440303612001c038801580c0140c102e1100d41d40b0503801001001381c00300400c0b002d410b0150195065091480c4401e81280b0001e06110600548240800b40705200b220a8000d1820706101030050400105401d800c0b851510001e80d0781600f448200100c040540e0f903164055002190503019280c0b40c03041c2100c1d960001001082040350303080040d4489602d0303600e468000c003010051801d849000004105032401c074164030100200b07030328030418031024145030000b030700030b119040c41140f8442c1850404010040702c04001c0ca160124024041480740022843c0c0c169460000380858010300e0104071550780744000c03010700c00500108005001070420744941c58115817071030454410b401c48506e140748400420003011503820400b00e000c1000d90250b0181048c10724060f00706c44000d081800205203803040f40d02030a000c0c05100034109583d50348003011280103065038008191541c105241406031120142c030001c0024010b04004900c8005905004185607001001c600c1110b5004a0a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 376310242 1250 376308992 376309009
    0xf020103180c090b10032a090b1305150304050304030f11030f16140d0209041a04030c0204140c120705190c02030609030301030305070b06040906020c0109230705 71
    0x8039410500035040400000d0b2900307446001030212010b0200c3c403c40800c040c402503100c103e60507030400d03080290540f03500900c9445041810600d5a810708641178028080d50300b00074650011490300c00000c0c60304603440e010061070f01941c100b1641d8680001c518103402c551404161030290480d00104020400500d0071810381c0e0225100300c0d140e010340c1c40c154001a08240302d442c54489960001d1303e250400056004807030300a84132030b9640c0046003518001213610342c0071060300240607010b00c1022505014007a4140c96604d10f141e140120186441d1400801d0140c11001c205d00880c102290b61480c4440840c0403031144400613950340c2010100c01c040c60b2148005466032040c8030381013203114948905c800d61800300d401551203450810746940306041c50324100510300340e01ca4006000520000e40c3c807070102c80143d601700e0340b10f140a0303c404000800801080500416161000440301c002007010f400c4140e07400d0103054041c4209440c0040420b00041c0011240400e402c0b4490600c42460b18491 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 376311492 1250 376310242 376310261
    0x3040e0118020c30070b060405090319081806070c0614130303150b04092c060708070915030e1605060d02070c03080c0c030601080a0f060e0f100b01090603090f020103 73
    0x40b801c24102c110301d41d911035030040d2410740d42c00e000300c6c0410100382014001e09800030445401180340c40044841d844041805a4a031410009924013168865420f1280d00404200980c05e517039031030038201c03805420240720850481300c4a040000500b400c10101212511444603914003003400540c0e41c3e01203000381422847e4000b0a9250800030540000840280000c1d011100700014012010114240700440c100c8034403c0400f500c2d4080c070b02e00303a800308440350440000e080ca042240c84641064a200406802494100d04c1d00e40da00009544c1c99003042c00d4068526042d42c1c02c0c94140c07040010310980c1d40c01502d030003003401c0000c50b03644c034103da000f001554083c941e1a0320194070b9944601c200c0d0300074042031401c2e50201061460500d0184002d9004103801740c020310840701d5030354442d000044161406070000f5580c0c3c000300016081030123003030144c001c6001580c8000300c092840500400e00440658001940c548022a60324007a03c104062990405c82c8802075114990044001d00000381 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 376312742 1250 376311492 376311553
    0x30402013605040b0a050d0f050f100f09020f090a021b0d0905190504020d09020619110d1403060409020d0b0405060601050708191103040e0118020c 65
    0x40c8503954645081804803541a10040c07000e10110200030320420701160300464840e5281c0203245005555484141088402c1a40c548203880b1b41400c2c2007030f003c50344550180503400340910300300024401044d5060084041a0100500300e9100c0102c0d04450002d04000e401c403a5842c90592186001d65070701343e110049040151400742001540705000440303280c140764a6100c0365034401d5481e00a01000050007098481c03041e000d90118442c0d030004140d00c1101c0c0115800038081d18400540d802110b0590f40242900380c0c0c890070003400f148015101584000012052100c1c048980700200f12344941c0351155076204807004d0f208848489550014001ca0f50040e9100f101c40b0060b1100020031070700303e000300419541481d0504150b420030b04028100341c10410100581c2001a06100994248101e0a2038203807407480b024200f640e00240b00342010080b403001140c0001c04203445503055068a08428810b00c480d00300d445100242e015815061203e500308052100c01c3c03a04441e0811040301c4c905 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 376313992 1250 376312742 376312757
    0x3020c04150501020322360b0603011503060e070c0209060f0d1514010b0c0607080106090e100e0903130b070206040e0709030b0a0e1e070603200f040e0c03060f0603040201 75
    0x410951304070144c4810010741f00c400108110007401c480c00300207209800040001d224007030003800090700f07d01c0140103c582000c400007049900c00d20039400b0401414205888030350b28109510040d04c2e01180c40c5040303101d21480e0001030802c1c03c000d86001d0241c40e0140c0707504c001c07450903560322034088042d80c014850325617540078480c401880180d810340244a801451a5143e9224001d41d0400a0044c2041c0a204040c8010000243c0c400355003c102d50048107010a1915030310a0103422481591060f01200083c4062101114021005029180c1da6140310025541c0d00d0a4000d694040d184010394418028001040f0300191411043d5210249241a90f40f032500c940d0b400032000002c0e1903800585030b8076245944e00c00c6007000740c3c1080c0c2d4402c0010040d030450b00943c0e2995003906004203002c040c0c03507050150030444c941003c0d60301c0301245550251101d21542c100f1419802512448103104442c0f00407071103a8002000700d81c0150380203460404800003200a01c00c0c6640007a0080341080f900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 376315242 1250 376313992 376313999
    0x2616091d01020a080f09060415110c01060902040609050324070c05060901091703060901150509060705010e070f080601030303051e1510090609120503120403020c04150501020322 78
    0x82c4000e0518041945a40d000743c10012490114141c0042489005a10900500011813070091604007038032900440845c28000e1000c280807240512224901c0c00d40c24900301240044598016100380c0d12546e4584107140e030350b0380c2050b80c0c50200d1502c81a1811001c240304101191103814250721290740e04000c000c0303050310fa50302e91518100711a51003503a5500d000c070604201196440c4001c83c3c40302d034445070441c14803000103064000188920039984c41051000c054880c081d006448034540018480d07a101d83e80303810200c0c0030700b9007100d01c01c0d458007850801085e00c69100c240101074600090082985a00f155030036030003444060315854640c2c1c0d11b0f010f1403080c106401d02e050700c100016000f2a480c4d01c900024020705200c00c00b040c0c424421050f2041c0030749903110a0980c21603081750100721841145e03042540c11840b88040003048440801d0800c03042c90f030005800c8251080c1602c0403c18258444a00c100c001894003131580180c1042000c43e14050050201d00420500c0241c2c200c1450b82c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 376316492 1250 376315242 376315301
    0xc0e060a0503040b1005301603060c0302030108030d09170c030a1101020a0e04051503010923190803040c05030d0903110a12121701261609 61
    0xc49006001590000400c420000ca50080755007140c1741004688a4504000000315045030525010109100d680c0104140e580030070010604503003103209031a0000000c0710001c2a0310b5850205440325420042c8282007a4428801c42381244e01500107582403081501c1c05002502c0142c070146d4082e07100c05803840e0020f8020f00201010090803008640d9200c004d5400b80100003080e862034004c0c0d10520500060a8000b02581d1300d0020407100000c9039a90020322040f03460b01180c1d04c0d5017540c40c000762403040007040e0303100700190b000058040030000070344051b00c1c1d500c03000d121094000201541d104000198400d02441c0c205114120721000c0130b80f9200480e00d000c00c241a900b0001700071040c1002070151034103404124643c01d8030100311b070301d0a01c1c02c412552012071400030b001c007816104c0d030b80096221700c021104080440e19001d015503501c003025448034038150791825101070000c101c4030810307400050442c1a0500e2443e880f800318545610800142000c52124015000203294035a5101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 376317742 1250 376316492 376316497
    0x906030703231518060a0920030111070605040201170112030509040207020d03021b01030614010e0d150c170f010605130503070308120f0702032a0607020a021002120d0c0e06 76
    0x4d0100340121030801340400f02c6481d10b000034002002c0545059400000300340300801d410010400c1c18070044078100c192020074010039001d104141003010100d0001d041200b81c4d084903001d83e000340e03184a01c0704049000214146130a2264184c2044103080e503100003030044010b0314800500600c0182442e9083d00426191410040308800680141c0c94100c906100c88101551206080c03800b0011142060403035450161102085030600030f2100d041002d42e9112400301c956079034410440e004600401810001030050510040040b03503551607981446035551744607030311610000d050350145903e441010781c1d190f8401220f0000d646504007000c00c003a101082010003c40c804c45e0301c550b5a040d00505060040805006012281480c03021300c89816800803d54603280f0080c14900742400489508043c118107540020b68140560003c1140480c5c010401500071402540c030761040841c12002240c540b016940d00450042c0240000d021b02c06181e805100e1200c05c82c201140699858000114941c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 376318992 1250 376317742 376317751
    0x61b0321050103050d030902150d1e150b19030504021c05030405030f0a03090303080a140a0b010806100c231516050313140c10020a0209060307032315 66
    0x80391901c004104010003000b02054401c2140f60400101c825030740044c03400241020136111800c0041514504401180e003c10080e145000181001c01500c0240030040e18841540c60010072042c500015011400c4040b14038105404070340c6581000c00010540080070060026a04141000030154031031480004007400c46015100442c0c447d1300e07200802d40303003255140061210b5001038030b000000070713000691001901da15081c688840e550310304008c0300800c05030385030484102d00d07542032110781c0c00c880d88034140405003a40c65070065a0340c141480312040e40b40d420540001c804400c203c1c0410303038001404000900d1131601080c40c20b038000703405140c03c0c08404d5188880000342c0a100010b00d45003900070319045d450500500b14601441c0c0061000041040a0301c46100c1910902411805010b40306942100a0520b130040625150095440c451010200d01495009000c91094a000510442103d5100342501410100011644c803409044444d01040340314403069000c00952080c48039114 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 376320242 1250 376318992 376319057
    0xa030e03030c0d060b040605030c0d391e0c080913140f0f010605070819080106030b0406210302030d1103040201120212070e060f030406090203010c0207061b03 70
    0x440f00202441e0703084800710742c0310503241a0b00708000c00c00c860700300040d20791080048000c662520b0556070a0383c0601009009400b44d901088800c8010040740c85c00200303048403103940441d07e90181001540e0341400405650b01a07850458102031580c0b14400b042d112074407410031542480c800d4004503581000f90312403c501a070b1602c10b0700351040c190341c9e0850760100d8001080c00280c02c00000822204030103010304410000000b0f4001d0901aa903c1141c0e03c6034030010200c01910803866006005000a0203010f0000b4100702d00307055141b0b4107008035000d48403000080341070146519188410510f000c1e00480a40c00103000d0700c01d034500d00c0e1042c10144103200c00400d0341c030b242a00c00101100a029170101c0014414070001c22030301020b201c0e05920542c0b03820300110a1a030f00b000112039020348000100d1950001041000f08204e540001105901c01e400034003980c0a00442030345c03a103085014403c005001d030300058081082c1030302e240246d140241084032680500d00f503000c800100714140e2102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 376321492 1250 376320242 376320247
    0xb0f010503060702060709050d081b0c03010f0b01021b0d050d030902010e090103030c0b0702010f0606022506120915050103232103091504051501050f09010306020a030e03030c 77
    0x40c0d081c1070003500d41c49079107031010300380c2d918010a002d81007030b016004107800b03480300043d50001c1061710320850302108081c2c0c0c00310300c00030b81c41c81a040e513036000c282e0b01034025400e20071520203802c030300c0c01795003080c1c98160050590801c0f86000803c120455140040e840001c024440001c110284843e080005141d0b0380440c00b04176500003d0314031207461400c01d003c0c0343c40d1801000800e5100c1c9a6240071039216901c65055107800c030089014060040c48001c42c90700e09040021351a030001440d0042c194561500d1400c0000400e84900310755080c0306240224807584400b00b46400150b0040d504240300da0f80031803407500e00d094071900f2600242c208542d2040ba010a40006011f034810000141012100619046260520038405030841d200e0704044500044003041034840c050281480290790419624018982801c09030b40d91003e811002d010803c1c1c900c0086420308002841d04224603003d083e0100592940d40d0703880c025071004c584e001c10144d0302e40c0c0510104406000a60107084080701c000e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 376322742 1250 376321492 376321499
    0x10f0c11070b0f0403060902040e030406091a130b0c030c011505040e01052205010b10081b030112020607140706080a11030f0402060a200d200a02060c0a0b0f01 70
    0x40c5072803080d0300810301000c0c09003c901c21010140c02101c1c143e03640200301040d00421480840c1c0038103240c2c11002540c0c000451b012800982c840d5802e0104c9400c5040340000c542202400111303442840e84000c0b40001e080818004120401d0040c00d41d500218220b91421404690490031150010300c807117840e2440c1c000410070303858180220318001c411080200500d04103112090302c040c8580e0100b54a41050704150400d000302035002e6680e0780c60240a0f03100841440744010284a003ca8056603000103d4500c0d0302c1c60491003042e64103032010686080e0801c2d00980130032013142c000b9401140c0c201e8070950440450001401103000030312440d1a000a942050702510b011707615515100001600207004105080c800d40420540240d010394446540d12070640c42107851031805040801c24602d5900441c09101000483d01d00e0107075166030308030006c44044401c00c4011005c003811410b0760702c05003241c400b625100c0c2c020100f44042c0c1c03045440e485256600c40b4807100381110100040c0a40740f0041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 376323992 1250 376322742 376322777
    0x60f040212030c10051501020c100e03060a02041a0322080f18011b020904110a08060c0304030f0309030c150f0617120403030c170909090f070b2703010f0c 68
    0x19604101e032140800348141b00032000075aa807648000d41407181c6008070750b2a04042c042d01c0380b46409440501a1340030703441c060100401942c03091080c12034545c07002d580c0401d0f000310305017580d0280780c0d00b00a40c2c40030600054002c40195075003805503070710f840801000b401541050014030441401c2c02e000300a021400002405050703400c507000040400d852a18001030b030f920503c0c1c1c0da11560000c0e80046110b2808007040d03503050302c2c2d0000d285031f1142606201012450401961240d442503564160074000b14200f18191450084000c0105104090080c00a050703100300e00840b0301d900c1c03000640e2180c3c003901601542c030140e0048403014208000d0300424001840700d84108100307800303214609451513900505540c41042e02078011440407083c1d60441c84804215108820001c012900a041c00c7c800b013502c1d030503c0c204912892249400004281e0f082c0801d035140609100d00d80c0340c2c07038040c04150903211954441d101d40d155507902203800d040503140c802d21002c40066520350100d0030a03145d07003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 376325242 1250 376323992 376324001
    0x90f0506010801150504020f0412260f0d0b130c170c0a08040305220b1902010605011209170c07080d1409120102130b03070f03020309060f040212030c10 67
    0x701201d6410031100f140d41d94058419401120411343d001a03075080c100300b000a48e0b01658201440030400301500c3c500340b2070a446091601884d0301d0350204655281032152a03144600d140c070001000e018040c6103490078040e44080100c800180200b40500d003540c044504403a55801c001002c201089050814054100041036100000340d0b061460040d072000c010303003140781c001c1c4014208040081d0100405502c4003514000880403224450010340380c4801e41910f4214001100101001c040141a030a205018034002c81e241130311003c402c0c10420080d9800340007003040950344d10b440d01c00040c00c1c0780e5410004050400340c0030040e0507880d0400c2c0700d840c00c0481104103107081040918040b680c0c040903030304070780801c00115207204d0038030103082c1d190780a80142c01c1e4005950302c0010000035a2801e20340150b100302e10594800101d1003280106030200e000a4a00585039440400003520f4000041052074105d0300080c005029032040951142c5503500c5522249410303040484481007a80203800f4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 376326492 1250 376325242 376325249
    0x5090f0102041d0603031207020c040b041e050a02070519020a060809030301120314070f0501050606071703040809100203070506011203021c030b0a03030201020306270c0913090f050601 81
    0x95141a240241c240c143d112446204407a100c480d10206929036010000c6890410f03400c00d40c441c242c64441c102a40343c180d01c1c0101402581051000c4495240034492000480031070006050f00c000302c1c4179080010300d402440a41010b90030405400802c2c0304100c0d0000100c10104212018100d610501000709036940c0110b06000c5034406020040b80b0110650f410345065900d0a140501c1324181160f401c0c681610118222a00040758020b01c03c1d400031103400180244020311403901e42800740040c0e4441c402d0080c0900680402950106022000a40c0c002e030260b01078a090000c40c0b030000744044200300c64800981e100040c0e03202002000e00c521030041c840003007c440c104000780c90194480c10b038865900300d1004009030840a2038040d91081c06440006403508021070348926019001390b1065030018403c03e112110503400380e095200c546854052500d010995440f8032440d04d80795000302100581c0201c0c0421240c0c07a41714070744660300c1e8860090080c1003004083e4101942004010380 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 376327742 1250 376326492 376326523
    0x4060e070f090e150705131502030904060b031311040e01050f1510050901050a0309050601120c090c02030f0d020d0f02030a05061207120813090c020f0718050601120f0509 75
    0xd8121295410201d2550351001c014144250387d0f03a07a4440005403500306801402c0c08030842550ba10b4081d84c0000078180011041e1001c1042e81c1d2182c0d5028241d00003258031a0106840028010001d414080c0c0c203500900040c1012542e010000009401e50350200c2d04400c01d2406481041402c2c03080b0400040d0740311003980e040c1030b0319034400401002c074401c90345070a050144c0016440c400c14032070b82c40b0b001502c0c2c0140a564495841d01c3c03051510440b11034040d624032100140104462160344a0b6141d05100e503002186000508050640d144c1c02000d620164141e00780301e81034410815000d4021803a40c6000d0059603460845844000c072940500020b000b42c60740070000350071503800514282540c410070a00121200149442c14941c805c0d503040e220940c4000e44000b403400004d8101c0051244c0710740942c5d4070004944800c0d40d4542c040c1c07107800c440440c2c0300d590001d0786150341d0000e604907106151940700b04401d824860196200303078544003100703541d171b800f0044503850600080a4008054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 376328992 1250 376327742 376327753
    0xf050d1a03100504030f081504060b0a020d090b030a0c09150e1018030204050a0b210d0c260c0109050c030c04060f030209090307120908060a020301031a04060e070f090e 74
    0x245c600401d4688116162000d200c1000045144008842103038100204011f00c00c0c090240c44d010840a5600480050000752203001d69043d5200d00500e8100251000e50307114a04650b52080c2c5100940000300100c0300340450640d01041e2480c946081180c01d840301d443d110144881841881400051040c0c110308110740f981c5119190700d034aa508101726901240c5c00304203503e03102240c20040580c0b00c1c140e90320180c0361151035018000d1059001e0020070740426038815507003803c0103645014024500030b14241c01d50b0014240d402c0703c5128940d0b00d01e0303190b4031a82041d1010840300d003100d00900c03095409510842d0a80072034981082184007107034060303400f40300c2c1500c0e00c0a03c4a10704d00034003009100f4091a000a0b0303800104005035441e040d04481c00c5049505118000382102c0c4450007580305a00a2400003080e107039403402102d040b65405190485400c10340e419850138903001030822141c05850f0706c82d000003000104220340c0a00103040381c48030803d280411010071900010001540340c2c011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 376330242 1250 376328992 376329001
    0x304150e06030a0b060c2d010902130c0c0b010602010e060612030a03020702030a290906040335190506040903051611040203040606141f0f050d1a031005 67
    0x16001030b00c1c0c204103440404280c0c0f65920000032a80e000d070404c54000b81c070841c401000101d8240036121700c4908443c804101c0343d00007086941c01d0741d11589004c1d401511350712241c070340310000380d000f00c1d0415920319221b525503a8903618282003901c20b0348003800607074641085c812014001d107c0d203904035004840c0942d0390340c2502100c40d124061500c0f080f041c9580401c41400303544003480b001d500c0c81c0e03001003441150046040d01e0058205541910001e1900c030200250040c00c0000d074440c05550143c0780c0c200c014a2440210050003110398840d401c0c49030b0604e0801c0c0d03000741d4240990207001c4898024120305180340403241203890060805100740d0070103030041d010a0300281254800e403904608030318404481e0900c2c0030300401c0c0e041e0003a0080c0c40001008103000c16944054241c8080318201c02600700c50004104218405400010520381d41c5403400f059640034110844601341c450515504040e5200200001c0b6040300c102040d4031000ca174000ea001389402e0041c1024682181d10402c801d090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 376331492 1250 376330242 376330249
    0x180302072c041a0a02090105030c07211e0206040f060b06070f0f03030605010315170c030615030f0601031106030408070501050901090c050d08090f18090304150e 71
    0x8a034407035007105600c2500301c140c0014500568040070300c09203010140301e081910b45120800350701c4149081c407402d0480450840d6026000315001028143c0d1401d0030b6480d0945d1101c02a40410401c48182c1560f01c1c08001508503c3d0300700600040300d49a410140402c072116040d901c0e800e440d2581190040070410001901c100c0403c0c0c050b80d00980000703100c13180d104c041141803140c00c50144c12084840351410030401c0700b66900d1451803007590144849035841c0015801d41c1d400034000064600c3c10341d41030104a082031404205003c200b800c03103008044a50100c0d0800a0079640c289406c0350841c001e00c0c032402e08000c44c6000d840c0c9040203200c20344c5580c44040300010602402d0b0b02c030b000000041414001c03040d09840301c40350040000c1000381840800c1500901c035880c1c04484958502c0c0c000101840e140030385614003504456007514180e06001004101100c0407030036540300307951900c044400802d40a2491145006a000b140d49500304040c0812001c0403680c10410810501c00541031500c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 376332742 1250 376331492 376331503
    0xb060408062202060d0608070905010501050711210a02180f04110a0f1401020105061512040804030611042315130b0d060f14090f040503070803010315180302 69
    0x502c0c5410044120408114582a504528401a5110324003081d44000a402c66004104990301c4804481d00389540b04400d5080c3d880c00d100d081d010601c1400b100001c101e008140e80380c4140d0050604450007000400d808101c000e01040c0085070340014416030840c20560f084018042c40c0304c00d0074400349041d40004c2003016004000030800f0100300800d1644d0b4135000340480103041006004e06070980c03078950340d00c031030010002003c3c019803c20000c5841410f0100034601e40b610000c500b80d1130200c14050000e000740c80940304588080b41044000b01041d054801c038000c00c904a40040d960704e18080300d01604480e1298031004251602440d00c03080d175190f0b021403020b0b80160025035100e101c4a00b641c400d4003820f0788503404290002500540a1490340e0101e01510030810403000c1254035040b2031100803001440d00c50f00091040301289148140c000706550040c403031030441e490b00303a0990310018690000c1e4021109100c89401d04d00c40759285002e81c00417002403052440c0840d4031624001d4ac0d81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 376333992 1250 376332742 376332751
    0x4031104050f041412030a09120903020a090e0c13020c06101511100c0f0f0206090303010b070f05030d1508240601030902181806011202040b010504050d0b0a0b06040806 74
    0x813940030500d89810041440420100d064284460f40c0b24078100d2420341c007500b045403048030755100c40072018203002e0044540b0015260090700554240d414103040c0ea00800080050125500c04c2240740e000681c3d410a191004189801000d03848102204403107260403000347c1504d81c20804100140800d081c01c1c4d80e2035810b40c985242c4440f46101d0200041c1c24408103180803450b103810441420b40c03240e044051010000000c2d640c5030702d802c7c25080100d844d41d00686400001d508200010003403d0707103400241c03003020300404058000c480780e5680c0300c2c5540c0c0720720004203074540c50f10809001220342c4048140203100040260280ca22840442c2d20144076100401d010008203034081007281c2d200e07034000404c0700d0f4050002c00804c025040d05082030f5a003154402c102038030b501d2200103644408105581290031074070301c91400c8002a0b00300000341c0300ca0344620b4100304050100003000d40d2410032801c00d56010328105070190514001302c00542e0b0103402028002e513020041004030070000210b05030301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 376335242 1250 376333992 376334003
    0x10815071b02100903020d0f0b070c02060304060c05040e04060e0111070201210e0709050912070c0b0a12110a1403100902070c0b030c13060201051302130b03030c0304031104050f04 79
    0x240a0103400540d004c40140e080650810318040c0300e007040010030f4080100c0c0500500381d01d4129650560119031a0100050094020b401071020038005a41504101c00038800760400e81d04141c3c41380100d10f0700c03540846090f00c0a81d158520800000d40a2080f0785522494100080c03800310300c0c2d000078000c03d8030741150540c007034a0406c0b50802c4440b19441092420100f40a44507500d91701d094550140c20151410142d5000c2c0d14803036510004076004550a041d401001e6107012840c3c1944c40034903170445d61265041c00369024004404e0f00c0760340305642902418841094503480e05000c000e1001c041d0034402da20780f1008109200c2441e0486910104a4001d00d00150351444640783c01c1c0c114034640c1e0720940c000640481800020701540c0080c0400c20003081100b4000c0ba900d4200302e0980b40150b0b00001c00354034890040703016042004280c02c0d869100b0002085600b41c03000400c0c617603489203032142e003690008941481080018503200510310b2003124180004c1c10418424200040041c100504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 376336492 1250 376335242 376335259
    0x110c060f0d0b03030a0e090c0301053303012315040504020a0e0a1401110610140d230f0f121e040308040504110703080a0f0e0303010815071b02 63
    0x4400d685070b04504070501c805400d59840e070403181009415000030b4004030b44102c0c0e0784030028402d001c508094a04a810040c001c9503d00e0000004416683c2c3e00e00740109a65164001d21f15811300d0100107500a0000552080b90b4000226a41003800000c1840c40e218240c104001d8400d41c18003000e4905030303901141d0069584204001c1510300d184101d2042c0e4200701464000107a03002c00000f441e1002c8001c2c0c0b20008039050031112a62560011101003012060010b0180010301903806100c04010020b4421400c0501036100c080c2c01c00a0a0310890780410b0f02d42480066800902c01000e103e920803000f0040d035004480040d4803110317055a1b4140000010079042e0720318400c0c41c4004091002d1140140c2c1d0b070394813070030100600d60083c010a0700072410406c407601b100c100c0404641c2c2d0250035a45049260b1980f000c90006041c0c081c0006034020303103609080700146800c3c0700840c001d0041d8801403050076021400320302000401440001030002c040c000d00030103400b0b1000310b882254115088113 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 376337742 1250 376336492 376336507
    0x809010212040210022a120d120b06070204050f071b030806192303210d0e0709020d0902041508060c070303020f03090f011103060607111c03050406110c060f 69
    0x3d03d002c0025650300b07808400720060074030241044c1506c054000702038074003001342808042c15a0703591100c2003440c1c0000c1c0c1050000074001005600200340020014a064030b045032903000030307007aa9002d4907441413080480d41406402604442010341d444082e04082c0700c81c2c2c440380c81c05001d00d200208111301503074840e4a80740007490200030b50b10150040600400450703c0e640013154410744201103190007485121207409203400e1b881c0d1312041d02c0c0080c041c034174030301603010b550140501041401a182441102404a0f0580d418000380c02010245400003508091600421081d15400100340d104200d01030000d010b1803101240542d80078000b40a5595654150700d0224000e100702001030747c4041c40802409036040c004030340740f101640500001e210342c2040e0008000f0034401070f99021341c4440c0810000740040c4484170058000349000380304920317085003036540d04108064000101c00140c0001014000d00e900040c2c02003020a0090003488150005000300301517208941043c0840c02c07011a0300c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 376338992 1250 376337742 376337747
    0x201050610030e211b06100503120301171606030f050609040309170c04140603100c08071d0307060309020910080a02090a090f12090e0412110325030809010212040210 73
    0xf0317585d81540035006000e034104040c500d91210400d40d91326178069103500300060a481c0010311555903070100801c6c00d103964030b0040c0e4103d110060742140030090291450b100d000d41030300c01d0705c0801030807107860110303940320300c9107818003120700050090344200c2e0780c1010310020980c040e043c082034401e150162a29120034610051410004a10705035010703041030702503038002e4500c48500740120815800c80318000180e80f080c03000c0c0d500054442001503802000611000e00c00c0450401c0749072000b031000103000540340370a080000ba90000404252282045411422b04030000351303001c140761000d031401e5400c02843e01e840d05055480644a0028032000c144010126402a0a000d0703004201e03041c022182d2509601c544000121500424152400000c001000c02c5880d4400c075441090314070b400d0300c2c1420980b038224450685034840d200921014214001d07110a18000000301047c00400b003407076240091151200419107031a80c0d005006500c100d9200509464000e6411900200b54140350b0408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 376340242 1250 376338992 376338997
    0x60a0525030c020c040e03070206031f0b09120607170a1e05010609050a231518030106050a0b030c070503091005070b0c04060804021e0d03051e0a05030a0b0409120201050610030e21 79
    0x1030015a0cc000e610000f09035401034000c0034507400a4580102d50070001c03c072151a81000c444401c003041d0780001c48410642d842d900c165011100c4900062411144140d250180311000c0c0124040c07580d940050110580055010340144801c031045e00e89a070a2882000b082076001c40c42c40e0807402c1081d00008642c1d40d10b0000c0280707045c003c2250741c44c0c0402246260049a04582040c0203510309800400c840c245098003c05640c003180c0c100e03145484401c101010341e807049606841500041c065100b265490440061030319403607556503525050301d810400f408203000b5100d152101410081003203182d4121025070340c0141c0443e00c8041402144501c0090180f91102940d880b039603051850b410981c01801804041e0070041c184000c003040a01102c2891091202c440040780b001d00014013101d40301e401c260503c40c0058004076404602e682e44618003070703400c800c1d2000750351a441000020b05050110b0030500e04d0510701800f04980403101345803070f04220100b410340d0400001d010454407020004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 376341492 1250 376340242 376340281
    0xc0f12061d0a050a1a1207030f0804031407060c061d07061d03030901051b07030209040606030317150f061c0e0f010e060a0525030c020c040e0307020603 67
    0x181c1e4410100a09180000d140040740c064058502e04004240d20320854070960032403a8031407800140e014441010080036a00040512034103101d40b41010000400e00041a20000d110350748c2151154290303c1c041e804582c02c80005e10302540007480c100040c0364802044401150880e600259426522200110f0b4540c005c000500d503100d0400e001561540c088841040c44480b58131030a400c181d1901015142d22551001a0010300700b444102003d00c030a140d142a000448000c9440095481e07011502d0903d044806440c00c9544035000c006160304020340c26520444800c8846451500c0b4001520390b0700b00c2d1400501030081e04d2889082612044211880529600641c40031044400000390280c6054007c0d080c030b90080110a5000d00d10500946911500f010058082e40ea6101d40304c2c8010702001341090300300702090461240010098554039002d04040c0d0340031412102c0001c1c06450068145480c074041c61400e030100d41d0164011054411090b0704445069a80e00c82800c2c080707a00d020800d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 376342742 1250 376341492 376341509
    0xd0c06090b070818120d02031305120a0801050414010e0c1626030411041a1003060509070509150a031506020f01050106090311040902040e030c0a150c0f1206 69
    0x1d0078404201d80080a10740b00e001302c1c0018110901e1940520780c0c07240009104003100010601c201c0300c007400540c016690203c0e00840d880d400d03050b15110a80b404042201181000390006510321115030701c000002c2c0035050035078007032180043c0d8500704609007105104940051000c4008543e920710300004850031122031003082e4420070340904040c4560901400342c2401d0544501d0442c41c60a5800c007660301c01e03a00300102a22082c402014440580811002009940ca141d40c0791780e0140d0740e28400c850542c60760307031300041c2d200c1c00d01c0f042c04015003024002c2024064240010b08242c0e46210305800b030082c104844646401060800340c0c007803c3c41d00704480d0301a1001e4408038a0560003c2e04201d1310380e10714028801a40d8680f801d44001071240409031203040747c5280c0c1d0b02d1508164200540f042e10140c0005024011300030204d040d41c01103104208590030810a440070701c404041515821075002504110304c007200388000d40303400100a5078605000000e030034841d6450f150303031101006000c00c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 376343992 1250 376342742 376342763
    0x901110423120a172704050106020114040809030c0a06030b0a050a08030a0e0f0a06110712120c0317010f0503010608121e070501021b0f120a140405030109050607021e0d0c0609 77
    0x12117088040d4000581c05c180598581000050f030f5620502404260140d0b048540486403540d803034500c00d9612610400344c252183d401ea140e11a159078403008010100d55178000340080700c0504100092045d075100502c9201d000c1004d000740c980c0803080307840c04440c90805040e82084900800c1c082042441010303170000341303144e0019040d134106542c0211a120001a6902e043d00c034429280352950880d80980311030340684111041500801ea542c14007802414003000b8010030b0301110300319182c02d0f040440f41c0b108148080096060074050200580285e402600000f080000712090b54040c0d96820b0300d12032400805a08040501021214060b800134002c0d5650b8260644a2188110302841a9504d00c0342001003c1c04100200785101d902030342c00440b40c54070071b99480440d40d51280110100442c9001c10001400360b80034400c2d40340c0305100310054006071802180284c100481020780707070100300c41c0d07600210748003e01088100c801d800e14200021410128103000c0b00500f03500303800030040c0149 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 376345242 1250 376343992 376344037
    0xc070c0504060b07050708010e0304061218110f04050f0c13090504080415020609060403030c030f020c060702011410030f0609021008190204030b0c030901110423120a17 74
    0x24080146811405003041704c880e1b07030355200c0c0a800c1710b024400c2c1140a8100348021311915204440c0c2d100e01c042004008504066681c0d030045c3c04a0304140100d401d01c03843c00d07400180d03052450380302c1c2c2d0071040ac0342c041240c2d14010380d62146441006090409180001800c041c102035100304c100040d05201c84108200e241902c0d1007041640706000f00d00d042c080000c0c08214052001404611490a0901030406903d84c0da8091f005011400ea440090549500c40c1c95041a42c1d88041c106540391750004020354141800041d003111006038600e4800402c11040181094402c90f211701140c0e8464051041e05101d170034824028a03026900961000040350004081640400d14600442d950b21843d100c011542075884224130451000601200e8140005018103402402030340e441441680046200c03160500c00e0000c03a07100c0d42150840c0c60201001101c0c14030400c203407007500081030320782c00d407030a0413052420341d42d44849000502e40e681e0325540121101074402501c44c030102c0080803a211009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 376346492 1250 376345242 376345259
    0x30302071e02131a1302041502030a09060f021011090901050f030c04110405030d0518040212010918081305040509190f170a050c0c010201060e0c070c050406 69
    0x480c20090711007041d8031002074a81c180690701d81c058140d0080400c0c5505602c0e046010180c4101d00c019800c40381803012008030350311080850390900c071460764016030741c0f400e00c036511658100a0215804640c01401402003094109400406441290400c1141d01410781400c84c40c007008402100e0700c2506100c0c655100d8070078040a8403c00b4030072a11880c2c02c2c2e8031003003480840122a01255415840416520040c3c03d01c0d90088002c3c40381514080d2070961100003092a1002c0c005003a00045d40011f2030103441080174400e042d03d140110380c01e520701180c035510041d520806008010066685043e400c0050075043c4558035166880070302551606941540750240c040d95109203409141001d000405c0c400c2c000c240001280c0a48000c0c40181e070300390700e8117507204081000440d840c0c0c00240c00031011000d014090400811030f0740d00d05030b80b1170f042005181003005040c4e070366041d0380c1440c40900c544601891101e0f03201455110711b0307480740034504000114001a50046d0b801515040000c038030b101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 376347742 1250 376346492 376346497
    0x402040f09050a05070813030908030703020706110a020102070303050f0c12090109090b0d0308040201050c030c07030c0e150f041508030a1107030308010b0307030207051b0102011b052212030302 85
    0x90700c0050401c1640c1d03070062030105646044501000280442c0001010819105620801c00d406403801d041c0d0f01d626146410f00c0c40e03101600503000b50340031301001c001039031780114050803a4001102400e5404c4050380082c1d605c04d12808001d05010020600c242e4414003c02030350094900d04080700d104908601a00c5005c1e4006440b55000500328800480c184d0340720301a0801008000d000360440d5040c5490465440707201601c12410400704100035045c1c014108003a0242c12a1070001c0c0260916524200c19044181d92044807620b5035041000545501c01c4d40c5142201416240c001e0189030308030000d07004005401da480c001210321200420a0100000600213100143d2100c0d130000c040c4018003a919410340c400207002804110041c0700d60340b102c1000d140c110416040c00741c1020250381c2c43c01d09040852440e8410700a06016900131580d09006003160b041c1582403414400144640050240c03080c41840e040400110701c1c80d80d039640c0311450401c02841c20540da0b490006062800401030f5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 376348992 1250 376347742 376347749
    0x902090f0a05070302041d07093308090c01030c020f0304030809100e131a060d02070201120b0f0f0604080d0810080c09150a0302040c11060907030b0f0a06050402040f 73
    0x581c60003000072600f81c003901c00c440980e0001d219100ca00c400682181c0c42c185401400501040782d0315000183c05040280710780d1089041181a00303080d12980040c0320b00a42d0703000041c0412a400085c041034040100380c401230340c1020318001c1804450a0f0b000d915110700562000a503120000e4000706202d112005062406002c840084903130f01c1c2d1302c9084805c01c9200d44510b50000e00d0203507241d130301d1001c1d070300103040819180c1c0240c0b4044403440005a607500215109254260000340d030300c0444da0300c211488110000044200080c400d414041104501544203d0340541100d108942099403458103540c0204001411100326603131401e0020400141951022a0074401000c042480d401c0440d02817207000c0003070400b0945941d801840d8522610185540c3e0708100000004009615070f4002c2aa00090a0300d51060b000900c1660603d0800c00410f9500190020003041c8006541c0c0b50144e900100b04418082860721034100c008000c05035540050fa00600c00240080e01c0690f1038400c4048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 376350242 1250 376348992 376349011
    0xb0c010c02012307210f020901030c0c050c011d0604080a020109171b0414070f23070b060a15081e0f01031b080a211b08030a0902090f 59
    0x188404102032849074580502d0301443d080d50020b02094420a000280e080c244031000d66002c42c07004940d421980000704044119400185520703595806004501610b561850510650149915416100e5012403440c1e410000300e0120300280100c5a031001c00100e50050035256516a0340349001c0e079a0003641e004a01041c0c80d0000002c00d4a040000e14040f041d14101401a1000c10080e6684800d24180c000d5409035a0b55440713800c000e007074003c503803040400c0e4070f881c042d400742424003519100e01400300401010300741c000c0d00310003151001a0792425500405860351030701c508000540c82c8100c0c0e0402d420101e101d14020701103c0d88124224055424040400041d00341c0c4c09014001c52000c031000300b000088900100005485040180a50b500c05001034200071b0300d9040107414001c403002c2c161014064000280c8507811161900000c008840c12700c0c440030001d0014440d200301e0781b40d40c040c00c00e03103001c07000451040494201c50b00446e07004100d0032441c030b00301500500900b4103903181400d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 376351492 1250 376350242 376350251
    0x80c030d06080f0a1b150906030b0609030307120c0b0f0103021305220302160f05100302070c30050604030e1903140c06030412110313030f0c0b0c010c0201 68
    0x1206900031801c0d41c10b18003c00c0141072001141e441d840b401d1030740031184041c24011180e001455444403040603c400911b80d940d2682249081c0006082c0ea48949442d880381e0380c01c1002c4510b82ea0004210396010760302c8041c0b0800788101840584100c641c0c408090070f58403400040044d2224101c01050507648200e031034514030040c00c000c60f003ca440803141c80c13400724045811515412001040401c4452213841210003074800c507480000c1190343d0b61f0000d201030560b85424000c41c0fa14076800d01d12030644e890214141b042e1a00e0301040c1084601c5468030006c2c00b6241c1c00401419041d290755400c0d80c04854030100c03045864240d64403c0120340079000550f018210782503520700710052650703000e41d980f03035024401d06580361a20090240c0c0d0603280c09206c1c071042c038016516404084d42c8158001c3d45800301a21844401078a1402c48050028003900104030b4005200c0b0710304000019690400404480000d081c50004071800d01c2d5000440701040100b42d814406605400003030010607540d00900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 376352742 1250 376351492 376351499
    0xa02011401051806130c02161505091309061e0b19061101060e0108240712020c030702301504030c020117010609090c02160e13080c030d06 61
    0x214001420300603160300005042c0e0f81512001500000c0e03401110080400383d403103112642880403100b180c21001d000d40c1080f00541c480e91900e403500b4000b40b051500ca140f00b03104d900d03402445440707a0307a5035911890301101c07800c40e0251982e01111001d98070100c200843c101c3c0301c2801c84000141070000210900344040c1405034100500010407035a4016801d030350740c506140c000d0315494036411000011350b585400015071060349604180c000c2065101500d110a4020500d90440c5505d2032040f82c000240818080c0d019402407031000241500b200042e1541c807014480c604602c68044060740c805000d00c3c4084181030903e00031403200040030801d0380000600180291034418810a01d0f01500ca510f000501080c010007024600510503d401d11070450000c4060950320350a8202070001620180148150340142c865000740c800c01c1e00042880c080007041c0050500410700401800081d114089800103400ba441c4404d0b9690259003a610f541420400954980202c11504507940c107021000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 376353992 1250 376352742 376352771
    0x160e06030316120c0c0f03020102010b0d0c050603071e2703020904080d1d0a05010b0a0311010f0917030903061506120c040e0f040b100513110403080f0a0201 69
    0x1148a8860180c5035101c9500d141c56442c2043c3c411880b520900c03041c07440c1040050118001503018100350100540328500303500009085602007403d260144030071a4000f03000c120340b650043c0072681c08480a03550796650f12001c0310032806442c901401e0360102c0e01286545500484100c51120305c02c01190074221100300c0c100300c0348a05110181d041b10002000c64041f885400c02422080808000451080000b0902034585948040300c01011382050418004116080c021007603500811a040586d02c0d0070343d00e80428010002c0e9031603050244060b402035406001e1010b00004005410302d400792416000300300c4d91207034003c50060b03100b80034290004c0c06184e00b2030030b4180b14900203001d00c1c0c01e046e41c0500f1112219405056604031032000c0c0400200a510110002d100702c5010048504600f454503002c0c2c000c00d0060f2005c0c564810844090040340c5a0700304805103407000180100381901d80d0824001d1910850304041c182410018400320705501583c001c000300303100d6038020004001100310a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 376355242 1250 376353992 376353997
    0x2010507020d0201020307050a12181203050c0403080a1d09010f2606011e030506150405151e0f10090e0f010501020c01080a0209120f0d0c0b040f080c160e060303 71
    0x150380407230400d0000c03140480c03044840750400c1018a40000798840300d100341e103080c05038040007243c014805019209210745e2502400d44c001d090340140d541814116542c0c0802805440c80f07150070031108403140140c89208034540b50303561a002d440411256101e928003502400b05d405690a4078144840e2407002d0036449003c01c0c00880c00002800c082c1c0d0070894000c2400101c0282104030010001011003c0340c0c0c240050f6000c0c202c40c0d4001800b1840c0c80041c4810b8550080c10343c052040c003608503503c01c1d110054450b8035602d90044400002c40440002640900c812105070f0300300540c900c000304403540000d80e60059440318203445200fa0340d030252007940c1e10400d00861f030042c0c1041030400314950181030300541003154154054145a425808290f2150343c000100505900c0a031034045055801e000e143c0003031460307203441c058061042e280c0f003562040c02b61000740340d01c4201281000740029042540c02455482041c0c0b80046071002410b4114001401441c01c5192110301040180c50000308 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 376356492 1250 376355242 376355251
    0x5071a0408060103020d0201021e0303010510030504050a0b100306090f05010b090405070306020d0609020a0f0e040b0a1802070b0f010305010b060702010c0303050606041e090f18060c12060602010507020d02010203 93
    0x80960fa8216030a0101d0800868012415889034059507031002800642c0003030212004401103031258907103c02c200f8191040342c0002c00341807400045c03002294010490051080c0c10880016298927100c20001d201612640044e2445260a08007001c10600c43c90210140c0d0044c0700a12210f281c0030201306100500b40c6c1c00a240d17034403200e02040091059000340861400404001514913a00c8519009a9204034052000a40c40c90b824690058000c0f50390541190191020060141410042000c00020380a0120100c000015106025140b90122075a480d40450030140a0601a0103c24080320038002203802d5400e142c4008100e0801409440d113440d0140e445c2214181d0684003900184005800360390032803001c21010034041009039500b250040900384803110503140000c804203c580c0c001d240b04580c2d08108420180303102c182c0c2101c2d10243c00c10000110003072002d600303803114030a560307000320a54103100000906940643c0020f1141c1000d4091b40c1c01024403c00407402c0340b10484 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 376357742 1250 376356492 376356509
    0x40f05030f060406050601120e150f070c030302281115070c020f0a0503060915100602030a050d0605040510050102012004060f05041a1306090308040608040f02090405071a04 76
    0xb0004020134600e0f006160010380605001505151201900c01074070380c00c0501a0751607002ca03c90303010320190940e540d64402c4181521203501c1c100b15130001d202450360344000c1c04068002c1131240400000280c003118510060388034000003651074001500340f080740c000c80aa54060013131042c005401c4041ca00d0700c40c00441d0745070844085c15078200f024800000403102e030000803c400200c1e143d2820481c5070302441800006140e000075030442e60b40d401b040100039403180d5444000c1040b641d600041500e4194440e400c0c59500c400c40081101d0080101d6801264003070300340b03801e0001080f180720705441601d1007070b40240101b00b0500f000c3c083d02c1c9a03000701d100443e07004010401c901c030301c41d0a981c00c0d420301a1900918155507042010900d825100c0100c2010100080310300f10520a102c0a000428090800c0107440d0700d5a1541d540a0045124003800c2c040e60200090400c28610010480c040d80207020043c81c1c100380c1407503175440b02503016210541c00201e07185043d84008805031001ca48448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 376358992 1250 376357742 376357753
    0x50301030c0b0f130b030901060f1805041401051e072f0a05010e151b030708180a030207030209060d020a1205030c0303130219060f030507020313060203040f05030f 72
    0x942e03080e80c070342d00c03e5107002040f650a03c000030240700a440040000c000481009440b414034080107400c40c0c0b10b9900030416064440010409c1a0446007001901450300c20002403d40e15410002c14110741e80c02860203a51030324040040044400b0f042c10f10355204904040615030f82c600007907400a00030590345400220042c56007022003035200001480300146402e854a081c80e50707460b20309503101c8100c070040c01c2c0c002c400300f2600b0113641c02c00c00d984004244244e6150308055035290341e81d84806060001040680c0300000d0b055000b1079a00d15003001c100c000c945140d03441d0309009489a0007170000b240305401000206e1741d140340c0129802c03a45500113010348a02860b0000b800c40d41c2d40d10000c03c40312408240302c00c04c41243c1c140083c61040e540340c0148005844203104000e00d1407400d82c1c2c01d0320a590000c1c0c00b4080503034407523000321042655007000101c43d111103100364910301a054552000340c00e8010007084055002c400341045440390040f04400e070ba00c41040544030b9902c2030341ca4000741e122 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 376360242 1250 376358992 376358999
    0x20606040c3c11100e010e07060503010509060a051c02040603170a0201050a0b0a060804050109020904120908030a1e1806050d060504090b190204090510080c18130c0e090703030f050301030c 83
    0x215170101d0300c8460341c2000068894002d220301c60400100764881c0d00401e201000411030341c1440003070746a004078110388100900341044001462031005481c5604052140d191000c11500c6030346c0124003840c0c02915464001050003c8030341254401010390340194200303408a030501e0114042c008007110010642e031096802c00508850b40c0074002d100b41c4056494044100240c0c071601c100300e010368096804600380b4220f60704007800ca098154441903065004101d14030302c043e8881c84030112200c40401c005a80900d447c81210130b41c43c0c03070820100074903060200040441d0845c0080902000300303401402520b686204000407200070f03a1002d89550240c10014500546844a07003004000f4840014202519001d4030412120101d8051000c142030304402c2c01224001c001c10781403508200c80852329202240540741d00d03004081d04a0700c030000500c201004010740c2c506d5007400b9089071200240c492501804c4180d0720301041c88160040b5410500e1440801d10075000c50381a00d4212030740f840003625 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 376361492 1250 376360242 376360273
    0x10501050f0d060b04030602090a0e1e070c060e0106090e0a02101809060602010c081f0311031912080702030a0512130204090308060a080706020606040c3c11 69
    0x214100c408010b40d540c0e04003146030402c0102800165004510040c0c0320042142485400f1000e90804202102a01c00700f15101d1400702c00e01c14143c0c2d1301014a081740e182d140041c0c4610344c501c13400800250400440e810814415882502111880e08061000001c8104242d44030b0000900c081c1d0800340541c0c1c04030440380201d007240310504045141c3e444151f603c3c6401d4003100c02a802500050751200360a4040310340c040781041d0040030010180c5606000c0c180c04028141e03003031100500c1640421941c40c683c1c1c1e02841011a04000d091001e20300c0c0320725240120040802690341ca0124044c2c2d808a06a140700000b0749640c14082d448051500d1860810305c125400020310289000445544c1040140c6841c0104601c09100740c481c0c0c140c5c1d08000301000f20030083e640100c00d8030b5204c02802c020700e03540003400540010083c0e50008000c542c11070304a915003003d030418410359020020040b501c141c048400c52a10171250407030303004081d21444c1110755000e02084080c0d142d00c5169508400c0d40d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 376362742 1250 376361492 376361497
    0x9060e04020c0c0d0501091a061e0f151902030c0a1403070602070317060103110901140d09030c060b01050405094204062414070204110703020c030105010501050f 71
    0x74402c01120002501000098044101c807402100c10365107803000441003040d00c03060000e1004083c00f03400c0d140c0c9802004101c0221103c00c401a0b511000041501320f81c40d04410900d01000142c40400009904030200c0e465610001c841e003299200c07108c00d100b5036407001c4107641c0f052101034054174000e0070303585880302452202c40c0c0840c10360004006580c002003540c03004081184c402d40380e10040c15a0010900c240d46030050400c0c3c1410304282905907014000d00031241a42000d007014090307a4011440c1320681d000c0c581c484480d00b442c04501d0b40c00c1c1a04440d0b081142ea04c81e602c00c1c03141d00d2900004440324019031103800e4102c64140085802e00051181040141c10302480b02020006258501d074801e443c0c0d0003250b240004842000f040b2403e0a00807500544440e1680311070601081c00400348640b07140050004010036400d2a0000302c144000310b40000b50010410b01101c0e0303074400f0070019076010740e108074058400c40400e4542400c2c1801181c0c101da41c140c542c2400c042070200400000e6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 376363992 1250 376362742 376362757
    0xf060906070c0b0c151608420f0109061e140a0908070b07050d030b030a06051008070803040e0c070c08010c0810080115140402040521010c09081906090818040c09060e0402 75
    0x207041c41108c4000c031541c1070074014045001070b50601500f041090a00030b01030842c40220341001007212040c0000758000c4140741d45200c0c10035005681700320940085444007004d00c900035240c02c0010b5903002d8140e0003000c0da0150781000b4140c0d10315580e245100000e43c490030304000e180d07820415681c1d503814041c0d0300c100500c0501a0948086407510340e901c1044a0701101e645101c860b20f543c0034802200c0400450002c1c0842070001c501d810304045903101010001410100304c490300040030400c02003152148002402e0b500c0081c00309682d0000054860300007203900e10007010480f00300140e0310f60140103194136102c800462180180c285182413841c150790042e820b0300076408010000f6107031903203207039401440c0d445016514510110300c035840c00d40d2100c3da401400c12100c0e0764240084034012540017080b0f0a60055a40800d00926041010b0f120551001d41004008900c645410000310014006040101c1c2d0400804501c4c40b010340d41603209d40100c030002a200000c56946060550040854 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 376365242 1250 376363992 376364041
    0xe0d11011404140f0a050714010c02130603110607020a03141207060c030522030c11030a060608060f0106080f0a0f0e0105100b040812090a050405090312060f060906070c0b0c151608 79
    0xc21066030007003194cc045c0900c44a030020b9030366030200180210000da070124590120744443c503100701ca400140b040c80203404042c1110041d4204035817010703000c0020124580079012540d840340c0035401c0c11001896081c8450010a0801e80001c200000c504000e0000d128001034202c590301c4641c07011a006d118152088503500e07070345401760f945035a080084904851080070080b0381541481c1c0310a040203c0a00b052940c2130024005010094000d40800e41c00208450b40744500e940d03250550f4083c1109000c5001c0703007443d1040c0d000e03920ba0190445803090030200169402550307120180100c40c40759108140e0503410104458400f081c002c0002d107545800100480c1c4419242e50028040703030002c0d28600016030000803407803160100c0c00c801c1030713000804075114415405c60b400442c0c078603c01c114049101d2040000d210701040b219175003400141070046a000e88440c40000c40a585003c0711141800c2d01440a0020710300c81200d0817441c460644c035640701c410390303202c04442200e00044940941d10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 376366492 1250 376365242 376365257
    0x30301030b240a12050c0d12050f070b0a0b09060d050d11150f071b05060103020904050a0506072003041406090a03060c030912030e0d11011404140f0a05071401 70
    0x10300ea5902d0344000c02510413000f65410b420620f00d4030525006000d5803441c05110414002000310f0240401165110003d041155a5a214165000343c0b03114a0800501000ba6001071218a038402d90103401e00102c103035101c0c84070b07403600400c022464003003920090046d032001c0301c08002180300304448188118844126114020560010a10f1031021180001c0801c0d04204004095500000300c0f1401c047d06009241844965110b0740d0b00d4410500020740104034010104040000070800d1220742904181625420308042c080240040c0d12080c045040b0030f42d00540300c3c260a4044222803c82e800f0008260b51049940240f022170b0300301c0c00e455076002517040c50010206505000d0b03412150f0460340d0008041c000751411401d00300d60031514404140c64070002c07980644000550302d010b60300904192403d0003801d54124050100340c1c21091116031540280020040346540541402075a00c06642402244564007562030800d120003400c9640329840801280280c1c03000c18001c400107260005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 376367742 1250 376366492 376366561
    0x901091104030c0902090a06050a02030732010504030e0a24090b0f07021c05031204060e010603141b030304030f0501060b0f0712020313090b06160b0702070503030301030b 75
    0x14403c40c1c5648400c001e1500061000704c1c925001c854003000d40303100d0508504081100340025034a00645100030a408034a5105030307030440041c444040000c1064440c194400031240d10540a41801c0c0d4080b00445c80215102c46c1d01d00d4100c00001c20f884031226446201d03012014081014603602c3c0950b03041c000007080125030030103040010100131800d007600315900d0490f44140314010b08203034008500490f800b514507000450110403610304001500700c2c00c0c0382e038071741c0e0a210009090b4808203507090b41c0307041000020007100500581c0d250500030291034070400707840b05e08008072010401c0300740c0c10342013040700780300242c903001d282c4002900030800003030320b02c1e2110030842c0940d1002c1120503211a0203d8200c00300f10816555a0350602c032440690304103942e98007aa000d21089000f03000740152030b00e03254410b40d203070101526820101c11070b00c0c0401c40813505150000c0c1300c00796000d40040c0254200425241000000c481c1202d074802e4290340d541e80e82600301c8400f520800b040050b01c1401041c5030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 376368992 1250 376367742 376367753
    0x150209090405060117010c0906030b0301110a0c140703020a03021012061725092a08100902040311040c020a0f03050d1808040e0c04170105070807030506090109110403 73
    0x3030303101c0c0b0710410003000c0030b504101160050f0308400785480c640c0d03810001175503240c6d42c2c0b0503000000c03106103040c00b0546111800010f0302500740801d640e454590042400d054055000c1044480785009110240980c040c141145807510107600020b904449121070030001810030f21800c491104251919040c1d031510300c41c0030001c0e80c000c2e6000b41702e9412600d00050042c18103114100000c2c9001c10303601c0c060b0b000e00e05203003808405441003511440d56120076248011032021482078034407102c0c0c054400030705080000b426108059401c1e46102c045100c021481490620031a0150f0340c00100720180f4080420421001d07040c8040742d1011401149160000290300300c0e4a190303042d103e0f440f0320780c8502c050400481107844690b030000320312406130340a5011070300381c0080342c095600300043c00b4036542d07611130b040f00281315541c001040002118a4108050410f40c4058040e40326540d8421043d114070100b00c05645054504a0303100c180140104021211684025580f07407840042c50f00341541ea80700c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 376370242 1250 376368992 376369009
    0xc0f030f12020a0302061602150f04032619020f0c0c010e0103060b07080f041a0a12110306091504020f041d10030809040b1320090d150209 61
    0x11280a9289120941084641c001111880c0030500c028003400e051500c0080d40c905001d09820020100000b0b4840e0301c1c0d10034072140c01a126034400c181003909000d130180d000004100d17010340000b850841d190214000d00024404c20006001054032591a5658401003824041c080d08151503800c0003118645240c060240c881040c1000150506034010000589041c40099a8504251070100280028158602a40c4c801da400c2071160303485071118882c1c0403551160390000c014103110314007201021400c000003801100d072155600110302c28076811090036500c528490f4035901406000180042c180a000d0507070015841c00d62034003203c030010104040b80c0c4001d503403a5203590005024071410402c000440b801c1c0c0b1203060000400e10708010414119a45404018500600002c807107480740c0d00d9420651031030380000d1081802e5160b401000c401405100b040b1070315140c007000740900618018060f40d481400103003000902d80000c3c2d03508801c0c40c022601d000c8840c0e909018440440d11000321 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 376371492 1250 376370242 376370249
    0xa03050105151c0609080405090408040f2909130203100f08060105031507020f060f0103050105060118090e2b09082a010e0409060c0f020a0206070b040c0f 68
    0x8150805212802c11104016031560045191081002c54201d149907500080c40c1c01c148002204100707403030021080d10030b0341d0005500c161a44144414404464028411030f00800c03110040642d65541c04a402d116003030031240000040740c0a29940e200c42c00041240d41001842030103030301051401c00b81241c0042d94090070105004000b0b0001000e00c0c00300720054802d8070300800003585820b001903030380c81400340c85110041c804804686c0d5103000300080d160381030004098485900e09101e030800061404d200541e02c075800d141c0801d4165020383c070010302c0840ca41c034000e05100d0074405060302600100d960043c1900c542458041503c5900c5841090802d600c00130001d4080c806d500100a212a0b400010094014800081c0103040040a081c900f040c0c01851681c0501c0c04001682d00002080c80650402d0903e0322103030807c01e86030301030300e1200b585803240203060801417001c030781e03a209400009401c81000c00c443d00100d2443d0f40034992051140d0740300c03500c240d200d45001041c02441d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 376372742 1250 376371492 376371503
    0x10e01021306080c030a021b0a0501290906101b11030705060310050405071e0807020d21020903010213060f080c280315120b0603010207050303070f020a020a03 70
    0x32041c00c1c51000780d041070010019440c15410505111001d180345220150400020584c00600c801010321590001c040c000015402d40d40e14460b6420014003803c240080b64074440841e02034845820120389494081d0180600308403000d81d116024132041d994158603840c240078401110300d9107a2040000386070540d114100380b08452031480141458035030180c00081c81040140200800441803151410407910300f2600841e031358551900030f48030700e01d0b102c285000043c001420503030410380041405000d2801c0c0d500300c401c1d038190504210340195250321003075664862081040d08680b15a0080c02c03508000500044c50640d40320400f1245130200d40c0001d021030700d041007954001da0040850740c3e20a2420f0b155500d418030035586203a028030140d640c3d241c0030a82440a9241a120b030703000340038410000310710340c07040342d201d40f0400d25242101c10200c6e401114a0000740301800c06009803502e4a902c00700550031070304c80400c20780e103c01070042148114440c40032590050ba0f00d01d07203040000e50290 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 376373992 1250 376372742 376372747
    0x2010f1e02101104120813150e0f04060b09090405010e070e0a05091f0c090509090a11030f0d261e060a03020a06031109060705010b40020705010e0102 66
    0x4041c80d80c1a640f2407001461a58410700c03080120000d0349414000c0740c1e034814182543c03488103172105408211540c0182083c1030315000c00030700b026041280904403503002c070b40b0b1000d2121010108020758040703005110350a402402012424205240c0d0300350440e1080c0c0000c51209108071866207028419813009080c1d03c00041070103100c18241c42034503001000310015010805071100416041065001e01c2c81c0717102d40c0d0304100c2100d14403d46900d0003818004204420030b0404850039690703002c450a0540d1365540f2040440714501c0c000904000324031000000e04510f85040d0f00c1a2942035442000c2c00e5180c003080c03c1d00c1c03a01c1b5141d414080c0300711109c0042400c282111608a43e4000009207075a010f90124041400566242016541140d04526003c58181190b40100c0a01c0c0100441c003600860046a00010040103401220a28406407a8014450040358298580502c0f07000350602420030045003100044002e108000764800c1e5003001347c6008465074416085802406840140b179601 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 376375242 1250 376373992 376374013
    0x1701050f07021507140c0a21020313030b04080f160b010501180b0901020a060e06070f0c120f0509060c070503060109020703091e0b0403060b040609090503030402010f1e02 75
    0x511099810101c1440200410003842c8041c000801014040303005005a441254481c4018242218000100c0c0c0c0c0544040f2045407038248100c07a08800304c03620002d003402028100030b03c00019640c10b0320380c0798112034103070307145031035000b0100b9014000361900c80c400c00c21a40b000e400c0798001c02e0b50b8141c0c2c415100d948106401c11001c0900d06800690400840552000c20703151050582800d448441e040380b0b03601d0b00500010b070300d0104da240b40141320030305000244542420200d0000d108058944440313418080d151011112a17500d2400108603030860a9818452803042030310000030000c07030500c50710300300884000a00c0e5811500b003a00d060707804100107020a04080c444140108111802075003800307040c1d540500641400d0242840c501684591007400906006482c002480281d809959a41d02c80c14490b025001c00d42503c0e003e1424020006400c860520403541c80d60703080340c0070351f00f15110360340111038503407104d103d40c02000900045617807a010100103614415010350001c1800e010b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 376376492 1250 376375242 376375261
    0x8010302030d0e030c040e071203020f100501080a0b100b0414040605190e090c0a0f080d0c020a0e040204061e0e09160e070c060f02030403030f0501030c091104170105 73
    0x1051542d070420440c01d0020007125450018211861440454000c9852001140003072325000707140c0d1148084421503500c00b0103158003c202558804a09030035078041503440901201030310420700c03400701590300c10610400460400e21b400c1e60484034420162010503907520b80d0001d40d8016800c10780500441104100b80b600c0c140c8075030b100a100960f01102c0c00400600a6601c8100700e124101c0f11517000b0b0005400320909000c088001c0ae4002c00000b00592100d9141074002c201d40501f090038401d05c40707584d901500641e04052a01c0d0b00034031400301c090401000c07203010180600200d030031545810001c1581200391060746090a92403980211682c5013040f104000c030006041d00b50725810080382c810303c80b449220841c0a0303d4600440703403140c0e00d0f040411078031250100805084c80e0318041c40103c010f0003540046008070b0081da4240207043d0a07000c490119102031000510303018095804100340c14858016030b8074021076415032800c0c107548121109601c461408446035595640c0708101c00707640c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 376377742 1250 376376492 376376503
    0x90501030e0106030b060f0103060308120618010e160c0f06150603021e0a110f0a020a0b19210603060b090f0103081602040605030d020604050607020c01020a02040905070302030d0801030203 83
    0x1280701c0000d2109902e035840e4000076000203090103000300015203050b83c00341d0190300311000031940100150b40d640300700c5034054022101512064400c0010390070302d904801c0c000c038001e0b040c2d035495294118261101110083c58034040d061441c00e020b061031032038020a4407025140c810034040d010114415030300c00a40a2000d0700303504038a0600d03105000503180440081c810030700002c3c100c008181e03620840d000c1640e9500b422141c28101e80f14403040b10940d10000f0a03d0074503030b4801c0e1288042e05888200008003401100c00b080394240c640e500365840680b08120307001e444506030038101074420a107a420b50656400d43c00a0301c0c0c01f600c4103006007944c00e0046016030301040c44070032031240d541981c0c1d030341042d48100090780c0e0390344a03102207010035955942d20510082500070200c481000103800003a40303900d000c48068445001d040005800540080380c1e4401c0c0f800140e025006501c51130b0b00300310003448102c40c2920340e031003a50313000300043e101082465410000d5486001c00c641c51072040501c0d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 376378992 1250 376377742 376377761
    0x5010e0108070f0308070203031c2f03070815040e1b0414070e0402041203020606090702011a1302040806010b250308040618050709090605010e010308032a030709050103 74
    0x1d5004030400c000c80160f4204240540303900c12007850b9141602d000203440e60041d61080e4002d0740160b0764480c1001d0051703000c418902a034130700960022a0b903161240c010345901d40101000242040040c041d544144441c3d90b0150034100c07104141c0d0b00080224044640c108031100c1e007540180038041120b507030500e0210300741c4000c44080c8400002c8410890524101400110510400c080000520394841d010399002c0c0400d058508041c29403400c00035503a450948000d2702030940d0b0f0380800c508034418052072030b6070b00201c20000d0a419000c4140402d82d40c0104421910a6092002003007143e010300c01540201502c04445455055a000e000c8580301c050100300c5000221075510000079410030032141d80039400030720029a041465080820f408074004000700180191031002c50800c00380d0b403140e1b07034581c0680010850f40e0f8a40009283c0c0000a0002034128041400000c1407400051882d03240e000700d50a56200542594190407000e810035100c44021820802040c03210396414410350001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 376380242 1250 376378992 376379009
    0xc0801021c051f0614040909120f08010503280503180a0b120c03060102011404060507140c100b010210090f200a0b0903010209030304030606050a08152a070605010e01 73
    0xc102440c2044540034030500c20b440c14082c4000c0c13580c00e21a00c0405a0340140b603050002e0090036954600049c6880c04400c5000200d105141c021035920311070024103041e1140a00108481c0000307014035804070303c2102c14444002449002c020000c0d60900180200100e500104000e1001c00d10410a4000080c2c1121100b0882484650a01a00c054413203400294401d042c5a407601d034100101d0241070b00310001540340320210b0902c010420b40f41d2040e481005a039440ca81d8080315024000510300c240521403c0d035030f00c00007034182c4440150b44840000081401220303081060000d08070150b50100d4002c0c3c070064540300341e000078000413409043e1941805460040200491400507805540b54080e0040f1258045483c900c0c5840035411a1406a4011700322074803290b81349003001c0502014050b1074042c8054020005c3d50041c005254a0b07502c20000c000c00300b80e928060140b0846202c03040c0d40c811334651080740745200707601400a02d0071900070400070402d076041110140b217415040c0d204069 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 376381492 1250 376380242 376380271
    0x403061a0420071b12030206061504030c030b2a0702040b0108061f051c060812070317041b030318140d14100203131412090d0c0801021c05 61
    0x1203115200c2c21a000c03036500c07030794002013000358103289005000361703800c144040007188013800c05160300040d40301d104d071030215420135642c0c11755485c460b82030156100041142200c01000d00014142c00346040d0f000c803101c43c0a00d4000c0d210380e40c010303003081c1203002100b072503070005091015414680228801c3d0030007800c010b036442c06c040c00410907844220183c1a1200c0e00c501031031068511920444444140d113407050140010819400d1b4003c0c01c841c403c0d00a030f031140300c40084a40c000042511030064150311600264200c01c0c1149884460082c004c60701c22040c070500022040f104500d02000d14040e9540110594030708407035a411000030b405c40c0440c1d002001c3c5034074256581c0101c01c8031407030380010300c0500045e080039120325083c246e40304020098004000c00c0050024003644c50706440c09242e0310720004820394422500c1d003030b802205200c040d10811094445042144044900a203d140400c0216580e000b407035003280c012800c4590909081500840c00340041d004284d080000b0181c2a0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 376382742 1250 376381492 376381541
    0x13031511070b0708040f06050a0c081003081c020c160e09120a05070f0b07050702090a020306030601050f0f040903051801030e06220c060503011d150f060403061a04 72
    0x81460001c3c942e0703081191340000501000a115861810f4583c4218207003d1800d145014001916600c1d503244009000940040d0b01d071030001d2080e20440343c00101c0340703107058000e0401c1d04041302114100c5c07100640070011081c0582041182648440a01c4980500e40c1d0030400710459101c0040d080514030ba1002c1c020041000403a0b089a0074007100303040030b03680c3d4401481d110302c000d1034003030300034000c41d0810b0100449a0b07084401403441601c00c80750132846a40b03a4542d5412804150703030703298156220320010301c11401c105c1420320305904000d1650505240003070000303045c0e0b8602d03032084000440100d1303c440d072203c0e4000c9500c00c988090030700b4810743c9200307412241d840d00010124100740130340c40c0e184680f000701030045409241e0030400e54071410b074540310090901d9200f0310461800d01c200c1e8608076800080c584815000b04812500101c0c001c107840100881070618000e030640c401d408100010000d0341034441c00c44440305a107030030000814010100300854031000003042c0c1d22580ba6800f003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 376383992 1250 376382742 376382753
    0x70e0d0213020a0309050f030309060f0114010c0804080313080106090204030503180a0b0a030905281202010b1e0301050702031606020703030f02030a141005060a141303151107 77
    0x6505040301c142005031101581c2008901800601d100500035010303801450740ca401c0088019446180c1d800d0484a0070749400d101e039941c0d12400d109400000c0c074681105903c41d1321508240841074090b028013406c7c41d8540001900b560301c0010424503100f03515030700b013024440a001d400001c100c1c6030301c00c41c1400e180d601c60300d131688038a00b009140c030720780c40320748455994400b008100a08030707142c64203450390062600500140740701c0505a9a81c0701c0d0084407000c0c10340840700390600078104659411040b1065840c014801c4024050030159500c850035120340e80c40d0b0584000d041da0798590148042500300d003c0c07500f140c4001d0a9181190000c00ca585642144070002c61101540101300680c3d410250400720020a00305064072001d60000042c4a08500c407600140e00b000e268140140082d207408012446580081c4074490b0060002e101100c0114014110100c542d50b00c0108a450b0420307036010ba40348440d06030401c80d604004410b10f00d800220b80c0c80344011740007a5029842c40c040254848 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 376385242 1250 376383992 376384009
    0xf150611151506070219060203130504021e03062d01180501050415020106092a0e150d0b060703020607020f01020a12090302150f06040b0103050c0304111c0803070e0d02 74
    0x302c034001c44000800008544400c0803021040001c0c05241a0f0903844010080d00d903881800916044a074005010860345810b2084454000c12131443c2c103c0c00648248111aa400041225601906581c00d00604240314000700345400c9000b2008001c0c8482c2c1e800140c800764804804103202c3c2c03000b110620050744c0060407181078800740c0301522250990340706c089000d072460360000d8907028181010500c400004c0d0310280c820003160320130300c80070b440c03900411501c150301074007041da00100ba5121403140c401c10f00d0041000701c8101d0030100340c09544c440070070740c55805403104400590000003044100c940c1441201c1c0103500d040001c3d45007010412000b481c3c000381122a1142940e9900c0c2d0004042c02000251b06507130100b0700c00d13142c5242840c0d40d000785000c1102c58500960910f0032072941c0790710a1040501c105558481941141c40d20740361f2600c003807440404640c1014220440ba41d100b80c4e80c1c035a8040300703403003006003c2d96480c0118000301440040250f85008440c40c0c490400140c1d9441031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 376386492 1250 376385242 376385281
    0x1602010e0606150f0c0106080610060c030806060306030a0b130308010f03030c020136150c0c09180b090303010303021b09150301061a03010e070c02130f15061115 71
    0x80c990b00c400100340c04c1041445405075080d002c0d80303402000518228042800b034800c00380000603c0a941d640c10080c0c4280f0800c00340100080c180c600044c2e82e80c0b800d01c01444d041180941196502d21039582c9081c0b81c59030a45070b210030700964100071020135510040c0203001d4030000380c2c0500f0280c50b681c1d001d07145204071200241400f62404031280c13550703490100c81c0c01003900c4202003409030404280c6130390459654001c0c00b0f43c00802e5441d0000e002e005510024250354010f9a140c12180341c4041c1c0b6000b0011304084e800d4600d40900000f000c1400080346a025404000146540e545540360103880d026454220704599450001080c5a9684202c51a0350081d407109000c083c81040000190051940740c00c140310880c2d00352080c0b2159036644010710705840c54408081c2d01900c0c1c003042901d010108040007503200c10f03a000040340c41009070b00200c600c00030100c0042104050200c480d07450718401d0f042580001c140305401000c1044c200520984021100000300e05030810300340e01c001200da4ac0c407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 376387742 1250 376386492 376386529
    0x3041208181509010306080105070f050c070f1706010801060506030a09050c060c3913090204020d09030201050f0603030a0c110a1d07050c0d1d03061602010e0606 71
    0x4500e015248244030388000d560004003190a9190050b034400b05503008401c0e0035000a20340200482d007860b05202e44c81c0540016164013840d07543c991002c44041e0300820b00d4080324010746d1030001e41003d030b00f403240011309991480c8003c2d01c0d1219540a19040c0140e1140a41d6810b00004002a03140c0b1000c80c0d421000178038001c50044458104035183c0201e405035687c0191000400030595100403500704002031104102c1c0c13109405d5940c41e8070303240c52100001c011082580b55041c0355032401060703034400d20329988004550b610160700020206c1c0c10000100b040980c54580c003400700765080c4075441c0c4c88104c4804a1400d820014040b81d500e000e4010301400b840001d200324000c0c03011403007290391132040040c40d0005003030702c4522080916070000031001010148002048480740901c00f610180c040c0c2000615122030f80380b4003207589445080e035040c420b00609020800b203840600c2040d1140344041d5040401e1aa40c1030000d003107580d00b080c50400d5800c25014440c896490051091b02c446014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 376388992 1250 376387742 376387747
    0x90303081f230301090c0b0703021006031514100e0a0b0310020919120b070903150e06070c0b0604110c0601080706201507230301090e03041208 63
    0x5900d07190400c9400d600101c0618902500080d280540c503602816041d1109101007110200d9050500769103030110000d101c3d08910300c051000140742c80141030101d010348101c4200c5000c2045800850b51207400540303e031100f104c40e4002e0300c00741d40560200c016424100594a103440004106040c0c614050035074151010300109007124425004004600c00041c00c0ea0b603d0948071090000960001d070707400340a5002c001c602d000603480d4940100884111600c0080021807a9841e211700c0000201001d0510001301008404100034101c942510882d0350030002d80350ba2800ca4803840c0c000c8c01000340302042510100c1c2c01c00600b204892541001c000e5402240d0100b403100220500e002d05000c02480d8412035000040b6001d002586c80202c0b040c80d1108141034454500d00f04081142540580b244d90007180341d0341002e034140d071010754403503258502800840314000a1450060039140c40001d640000b00041c441e04825206a80902c3d407000300a51425140100c0005a0040e1940190001c80301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 376390242 1250 376388992 376389001
    0xc010309020609030d03090605090a212a11060307020d080a24061713120905130c020613030e0904150501182405150d060e01150f09030308 61
    0x7070b0390507203a50b080002d0940d1420388800314020000c24522009480c1e06040901103100d0b000c01080c0725101d0f603048160000c1044098160b06044c424400314041000001000301216050201007000003205003841400d0448850800f20a214641320310340b4070400080090240c0a80c0018000b218035450b410988010f07a035514440c00100210000f10142060140c1003503034206400b409503050f01e200380c84482401e03851440113090f0311380495810b2110910480c255005c02c01c071041d049041c10451170b101d0390050702c8002103020892083c0c0c0d0f00c055691100034040c0c80d55014000143e102d481480e8289901d0501e44008014186604185001c0c3d003030000464140280400083c1401000d820240039551352840030b801d10b094040c0400b001c9034901901e035842d49000c0d0070f01c00d0080580d081400090b9003003408028490001035084100007004214040d0007844d02c1c0200002484040340b007480761342c5480c460810542c05019503804010390522959a6150096860010780b5054503100d0042c1d1786 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 376391492 1250 376390242 376390249
    0x1051018080703050a020901080c130b120f01051005030604050a1106070501180c0b09090f0c120907030b06031f0902040f050a0f1a0108040f02030304030f050f0601170c01030902 78
    0x800d8000724014000c0c881c01105101c000203c9074034040c0f00741d0780c61401d0faa8032110b0707940701c1104100c42e50344040c05110b18041034149402c11100d1090040c11900c2c7d00c40e107901c50320303e03022045050407010b0351130b0307010805806c60a5240314000e01d801d0f809410286400d0344c82c075440b03a806100003801003500b4010011140c407103e0960703c003a64410000c1007004400c100d4a80c88880d40c1104407001c1c0c00f103640101c0c4409500c0c0548000103000b4203c05c440b51106400310400c0d9400500644007094203001025468a100c000f86000f481800017800d0882d055003000c4e03600001c000e00050280e4005146142c5a4661020843d221070039220001283c010a10015010b000c0401c40750804c4d03802d083c1480042c0429a02600c51a07110190410402d40542e003d0800400e8000f101c0d40401e00090000e400300381003000280100d88006c1c02c0c0d0303180c15242d44c1d0f00304003617171007510694680e80148089070b1407040821180d03001d480c441c03009420030f0701e01c0300c3d6180e540d1a240060f6410140c85003540401c548 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 376392742 1250 376391492 376391537
    0xa111b0a08030106020f0c01050403020d02042708090f010e010c030c020d14520b0f0a12090209150a03081c0b060408070527010e07020d08010510 64
    0x990140780d203a60781d696064006e5030ba000c0b556188801d0301031030074100c00a602a5040f10126a400340400c1042d030599001c200040001c440f8540c00118051604030110a44da14202561845083c0c411b071142107000a11407012840d0a6250521000080e1013101d41e80200040d410180e041c0f820352048031b600e1001c0740ca0000703d043c0051140d6800340701400d400350041030b00c1c5006103603016a010000318500c06081c2c1803038900b10130b104905401e001c45c80c010110b0901016900384940c043d0341c40d159148019481c50340491201c60304140007190405140707511210009469620354400d101401e040c0e000501c1f0403502401c0da189250311580f4881564840c40e090500464001404946500031140f203811a800360f00119400e0f545000c0882e85a40781500598044c1c80f1800000e100f07450070316041c001a03958018408203200408030300310355a40c0c00d081c80540a01156645d04c0c925083c011400fa02e030420300040d181c02d028665005000548580c80302c038410788090314103482e4008001c840000040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 376393992 1250 376392742 376392763
    0x70e071e050712090302120d05220803040306051e061c02031c09060f090e06010c020105070618020f10080601080601110a210207240905180a050a111b 66
    0x3c80c80c01c4800c102c00d07030804010000c90340261200c1c424420035505003603e41d620940c0b0000826024844003003041ea180088500c40c590810380d15510725120b0359013610b183c100b94411101e02c3d8640003084520400050203283c51040c6103414500f504041c030002e068011174580b00c131820107a028100341950b0301006040c00b031101c1c0c5102e00f8582205668021b00382d050601480c400f190180200c480764510580036542100d0b410207030b07403000b5100e40c801180c10030003114090703042100a00c081c1004c1070041c400d0403400d40e1007440c1500c942095105020a00320082c18040c811100810b903d51074035000756240e039012000340381424591b595480140c0b02c4028640110100340b00704151182040321200b042051a4014036400c2c09685103044101c0e074481507405101c40c018038095036240542c0001100c90210401e508000c0c101c180c07240301041416007008802c5070142c400c6028044000502d10656400400c5e0440a10150515465906071803003586100d041c402a11115407018000c14810203445 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 376395242 1250 376393992 376394003
    0xb0f09041131050d080904090f02060c0303010504051003080307030b0a12051e03040f060c0c0e0702060a0c051305010e0a09020313030210051303050304150e010204030302070e071e0507 81
    0x609511040e58809002924000300c0401c5602e01d010070f10386860015442003c0e071143d221854080d40f00180030141c501d151045a2820489224400603030b10310340540001c1554400940e1651b140c2020130040c0c540280c030f1588072082c031510900206602e0070407a50322140504000c00c18109000114151000b1a0311010118054414440822501050007811032020307101c20001801c00c059055203034031851003590344c03a0640080c00c11001e40143c0304619046c4c0a00c052440c140c0d610010600e11070b00483d41600180c018804000107254903109200142003285030480c20210450035810701c178a07aa0017080e062100611481920765200d04045c2c010b06000c540c25034a074141418007552a4501d0b100c11070250095200074242202c0c0e42c4a000d200d480a96815035030600a514141e41c40e500140003605d00c510300310740901140c0c115015034001c100908000503640d910314200241041513940094a40c0b41d40d0906008007180c0c00290b41c0301c0d43d00004020b50140441c04c10035981403107003107402884d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 376396492 1250 376395242 376395277
    0xe0702071703041811030112060b0d0b010e070c050606130612030504030c0e0705030a090501021b0f01061710180501060303090e0f0f0c09010908070305160b0f090411 73
    0x180301c800880074004461078a0300d074012549240c500c40c001d13a101c1280344505014140010480c04070540780c9000c06901900c4000390f1b500e0200b02083d0003811801c0103440003460440108942d03010314580176804852072030700c41a040800e03034600da100c0f100a004a0310410031004001075190b0b142d800303000100303004030300b840301c9080c00c4c40c2c042c2203504144029152840d10b4903001a8000d10803a22a104030340030b54600389543c0c0d031190208003c1c00c1405050318150341c24851001030105048250456030381400c004c0802c004103012181c01c0d80c202d90490a03410a07104a10fa500b0300c00002c81c040200c425002c045140040c0d64606152402c1c001c002400942c00c0000010a15410003840c10a560000c4502070700781ea00d500c00441194410b0703410b80481502d0800089590848001030040810145082ca2a2a668000d018a0311000f40c00503180b50b00b280404030b18002d04910198000c09181c0d4019080c03004421035104a4080c458480b4016a21400c0d030207007002c000c00880e402d41c00048040311 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 376397742 1250 376396492 376396529
    0xc120717070504050709081002130506030a0603060c02011a10210b0f090423100204060305100f18200705100f1107080d060305010e0f010b0603040c0e070207 69
    0x141d031001544145801245030001151009119142c8101a54040c41c01000101c2c41c007082c074002503100000c07500b41f50601c400007040c10340e504d41c0114000c0c000c071640400c03580c2c1141050411228502c0f505002c1d07a2400000b0148c2c101c801920700900c180840325107040c40501c8400366400207804611a09042180315a510f4540040c1c0c08907043c00015103941a254194500b881070041d802d84016240301080d010195600030160410343c101c00c00082600d4611199428290a0760007035000035000c20340354010058440b006400d090010030711484405d441e40c0ca4000e00016000039121300409264494101c0021a0302000a02140d03c10020031030f42d42e8034440c1081a151101100c20181960600d013451580f000e1900400000b23003207403200c0514000da16a00d0b10056030110b404400c002d51036078000070101c0d80c284158184004a80003921000b88a80c500e07a08452039140c0c40d5101e50018001c2c40301081c0c5208030403080d2140103032070482c203881d0484280d240001c5940700902c900c41000d00c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 376398992 1250 376397742 376397789
    0x4090602122e0e040317090d1803020a061803050d0503070809210a020a0803040b041a1303110a02090712060b030402060d052d0420030c1207 62
    0x41e105101420040da0850841c0030001038020464900c0d8a6925034042c050040b19003003298180c002d4881c1c10049001455520100d180c56004c51300e443c85508950704000c445500200b29101012a144101e06140d0031030740041c0a10032907000d0b0404003d14018280410a482d1500700091a0410308481150710a000003c0080c2d02c02c84106001811010108000700000030711105450000402c443c41c800b01089901a2034100a0003407085100d0024804007240388000154011401180b5421452130036040400312078942c2d8042c480a001c0460802c50807203000c640301d0b800f0315454a4521000344c2c1c07401a50340f0b00100c030440a5802401c00f020f101e01c40d60020203d42400903024402d20100c1e684200e04144e901045402030341021040101c88000c54050344495402900580d65103546c5060700d40755400c80d9110180841a1145901844140b00c1d81c090900c08a1000445403101ca405030804030b41c172900c2c01e295580c011043c4481001501c10107014040240207212440c802ea151038a125 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 376400242 1250 376398992 376399027
    0x70f050f010903030c050a090303050906040f0e09010e0601140409020d061a0f10082d040c05090f042604090f0906061e0b0f04050d2118031104090602 66
    0x203c0c04070b03181c01c044141c0b141c003403010b5036008592610b136510403500d10f4809940c03550084502030340c0002c003080701080d40f051005a0340c01800c03105900c1c4034146042110203013100c1c2c1c2f450189400394001401044003c407500d900351041c0c1d03c15500410100040d06c04110100c2031418024503450910051400c0280b4030210031441c184211a50040c0d04050307002c1c480c000b00c82404c0f01d00041d20f031000081001c028008450f082140800803440203804001c1c8000801d03005640c212440924160100598900f090100750800c10001a24600c0d00b4141d46001c2800000c0c044400b020000c00e001c4030042c1c03100000d60780107000c00003040c0100c0c61140f140500500b007400381203980500c0c149010690349154114030b46080c0c1d1140f00a889142080103000c0d103500030203081115803c041001181c6903d81882105c0c50038464419035030021090380c10b032007484c01c0c00c009035000c00440d084103120300c0c1c00344c041201c02c51741c001c0040040b0101a60100c2c0140034000009011a800060010f0544266901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 376401492 1250 376400242 376400261
    0x203090307020a0e09100e0312040507090e0102030f1501031b210c020307020108100b1911060603030a1103090406033f0f020f0f03030907080c0d0602070f050f01 71
    0x41080320f1546400d4200c030b0550040d11000e42c268402d0f40024265a1503500c440f101c0381585040f6404c040c15100020018141210202c509800600302084410181d0041c600e80c604040000e500790b140c140035405020745c00030002805290002e4050100c1c1c5d000758040080c24103030070860716070701c0002c03000036100d82230080c02a04079040d070000354080b40e4010b1203a14401c001c294040c0d442c0003210f03001104d0941015140711500c0c1c01103030b0b0009034180900010042c0c1c020750702038108050b00d1920082c04200c091204504140c205d501040440c0e0303001f1007100e10183c9141401400d4088080615195004440181d50000c4c60b095020003441020310782c00e4040e00f210005083d20b442c4c0440f00040001c10176000c400540f2200c0a240c600c075002c0c00694500d030341180304a807010484080030070314009450812003100e400001c188198600c05220403406454404005d00303110010340c01242401c00c7c0301802802c0c0d541d0210f8200304101414102030302c0c17150400e0858400240b42c401e094000d00c410117 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 376402742 1250 376401492 376401499
    0xa03050702180f01081006031205071419020a050d17030a0b03070b0c0c010504140913051f050c0c06041101020309030709050f060411030613021b011e020721050d020309030702 77
    0xe03050f1591b03070b85500400c02036aa100c000c081103070340a81c401fa40d10b074001030300443c0c1d81d25101412074007800d8104100b802c48160b4038404860301c013842c014001c0c0c13030101c3d8100314040c5190380101c3d000309800c00200280100540074055a81d5580090b0720010316400d450a5410f0182da040003035000d250001130116000148191118100c2840c0151a14821845032a1901001150326034051802e410f145900c481106001d43c0c0740d00003030740d4081c28880d000d441004004803c1a0352134a80e5402e02c90789500034401d101092900000c110565a2a02d00410041000e080034182d090303035910078001d8851612001e411a0082c1e034603850390b900070702821078545d41a2100311000901c41c0c6002d000e01e209003480b2200b034600c0c40d2140800e20140c98641c0440c1003005408000b0740054840c25801080c02142131400080c04150300310031120705030750300710140a241c1c2c01408003101080c42c954541c64bc804081e281c2c2076200c11049030079030f140d001d4501e0440030940701108202034000040010704d0000e00c00c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 376403992 1250 376402742 376402753
    0x201021c020a051005010f27020a110c1c020409020d020312040312031806091a090a15020a0509121006151e0e06090f060408030702030d08090a03050702180f0108 71
    0x1144090841740c00b4440c501c10741c07a06c100100003d100c849074410000316500008013060100204001c01e0b6400061140e00081d400c80d030782d48030301c030b401d10406004035012501000d012204000b0b440a00000305e4000e482141e44404210855480507142a441980036081c5ea02400054210415980042c40291a04511006642070b054441d00c91114411f10810f4440250310594641c00020401e080d422039140d01d80d682c2e4440d440caa0004054850540d50b4000d00c001800c80c5003000a4110b071003024000b2500500041450329004401d9404048065900c2042e02ca1f04801071460136a0311001310250a24020700070801c85580c031200388004450ba02c80c8400200804600791809407030303040c0000050130b5143c0601c82d626210001786241c0308001d220b0031484036100000380c002e0303106c0d60240388250b2001440340c085080034015540401c40720f0800d040e6030302c5c0041b0526103402d10000d0050401900040e80011981c4404115412001000101c15149441042c501545400303014486a61054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 376405242 1250 376403992 376404013
    0x6040b090106030b01270906060807050405130b0702030f070c050f0111070303030b040e0f060f2505070f06050a09150e12091206071d0a050108040b040201021c020a05 73
    0x5020311000c803130340058080340b16841d02d184402040102900c21040c040c20a515214108080c015055054000d442c0003804a02d441c0c5207a1401c09107601c07450045081100300041d610071000d08131543c607000b40d80c9003560341d210a400c9045100d546e8108124040100c2ca11080c000c0e0700c4040380c103444042d00c4c0400d07413200440040d600c0342c4102d20306ca0070b140d00500003070000900c2900004081d1101500c08074190815080385800e20b24508030394013043d8402d40810581048000b01640c0145d12411510914201240446190720140d0b8101050000000700c045c1000174102e41100c400fa0014000c00c01820301d16441c10151002d1003058445940340f07003e405a142017403040c2c03180d14509070010302e01d0540c12052007541e03401c0800500d80c4a41ca881d01c10f8401c98041c050720388282565501d41c480c4403032002000b9a00204070581601842c080401400541d0f002052160004c0d00300c00e0f00040c940c1c441c40104d1a2032803418411103107203203c40d10b001e80c094000400d1000c85100d030054a44440e0b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 376406492 1250 376405242 376405261
    0x30509010b040513030c23031914070305071509080d050603060613050c090a030804171c0309230f0606090906040305070f1a06040e0a0203060c0f07060e06040b 70
    0x9013507864070b45500368443e10f4000079002e404514080e03485042d031401440d81c900e40720700b8804c144a90828080e00006a440c08491038000d2060145015080405019420008800b068054460020140030380021104280601c2d035603002d01c14407000c0c009014120140c6405001600011441d42d840c0d03081c800414218031740495154414040581391041640c1c6044c0c121000c4c0c036015168503c180c800704940c0d201500d0b8021075001841c090300003280d50364902000e164900b0321048250290303030000040d40d4084018010740c0450380440d03207404568004103052040d54075149030310210079491712902011880001040c444070a072081c000b502c42030f0341c980c0300348040501c045407000c2030b54100c0000100040c1c004c070064039040d0701034201c9891070800c640e070754400040803450300740c0e941c400903041285500c0e042c000d1a00031110840a0000c0320807903400300381d940c840600407052020012a0b9030080780141019074540c0d540060b81809540702d503524117607d44506490070fa038041c0a40000a01c09031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 376407742 1250 376406492 376406501
    0x504150e0319150b010507061103010503071203050a0f02030912100617030a140c010f4b09150501051f120b0d052b030c050f090619030509010b04 64
    0x940000011140c40c3c1c107800400000e05400405030b040c09000d21942c400b266042c8105c442c0d0011100e101592075040c10201480e1202030b600032007000703503003100e80c0c000240d04c6804e07244100c845042c20b10380061130010681c1103014407100990445410035411000038800a1280c460881620341046980e40300d9440e001c014a852265124560007000006051886010356090032941c8203502810b144051a090742520511904d0b400159101c8003140d090351034240d00c244a00c0c0301d140b0350300b03030340030504204212001d4600103d40c1080e80000da036a11036201038000458455100b0021841c22400000150051100f8040d40703014601e804021f0f40b518900c0b003024401d16001d40c469882000c0b801c501d450103400c461b400e041c0c000414252120019000b00107054190b4030b002c21101001030400703074484407040720b04000300c1010304040b59201443d8100301212802010740944955524007000890760741e125490100f01040c030200c000c100ca00e68542d010341d01941c510710003480000081d03404c100c10344 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 376408992 1250 376407742 376407793
    0x6080a051e03041d010e13033002070302060906060109050303031302240a0e030102040f030305030612030c07060e06030402010e010509040603050303010b090f030a030c0f030504150e03 81
    0x9a001120501c201e110207001201502a4081224600380d1260200d014190310300543c80d0b040c40b00100148109802000d100c0c0c0c1c05400040c1da0304485946132001410725025155010f80c411409030b180c42e49440102240c4001640300b402907540302400d1900940d107000450340c1c15a940a910080b454a40c0304012000840d040180150f08588607034070031080300050b25004076130100386000f181c0c2c80701c54034103100810380710040c3e601078641d0380c00d0001401d4500d200c80e22511a9104000c1130006004121040e401c1c6c81d0540381850701e0380d6502001c88e800e4004010025080d100c0850109030710140010f03114107503040b035952204031424200c144172031404181c50090124000341d0601e80e25520940103001181b41c018404140b580c0d4a4645900350761081e0481d240300040020b52031098182281148101002a4024040040107807002402d0003804100100b40d07404144403070b410700d4800c0084c1c5003e0150300d0446c00000a01c00006000102ca03621110300034058a001c22081001088165014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 376410242 1250 376408992 376409003
    0xe030c0102070e0a091203022205031e0a0f210503012105011803270305070302062101060503010f061e23030118060e071b03030608030c1006080a 64
    0x314100503c0352000d0b007004000c8001d850707444c0c50100c041812240004c944200740c1c0ca0040c2c3c3d6800d0401310742000359001031040a002c148020800840d01c0004041d86140032060001d2405402c0140b458141004004080e0080f06182031010501581400e000305105840b8103180d010240501c003520640000d02c11040c10810b500201c0c168001901c1101c5c81c2c0034401d2000141342c00040030360400c0341da9071407026400075060310503040e2642541a03e00200d03400e4003c222800502e50360300c00d0742e40c00b65804024003462000ca40304000c7c0d007000d89800580c4005600f040d03c2980c50b004002e1054200b4410480001030f92100096254069410003003107080120013110451400a01650b05986048418803100100068804950f40c0d20f005940607040b946902074440600200f504c06450b0f480e0072149104a155091040d06904650041644411001c04001c86800760034260018540340e4820340d418000060207020b1100040351244201304980d1302007091589038072606039a1100c48000909 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 376411492 1250 376410242 376410253
    0x1080c0d21090506030f0601030e0c0f150915370c1704090e120f0a03050c1c050f0a110a211b0e010c03090b0a020f120a0e030c0102 58
    0x400c018818601c080003041802c1500d00d49568002103a480d03881101d049007100d8269051040d590380c140909806402040e0017050031810031000100d0700c80000c0c600700c0c80349194240c00d100c81c0007008107540d440d1078002c0499140c41041090071000e1780c4030412015803603003001404286540544a508038051214000011906c2e001405030756203e0b841c1c00c196005804030b0404c44060106100400142021120100f08494100851841d0080103801c1c141030720024402c00c4c0b4005030003400c0e50321007c2c81d850046800e4860790510042c9114611130740042c41c0f4060501c0c44081d480b608001d0048176105408452a07035503c00060481e0003d510310310729040c0800c2300d01c252a1240403a400b030340e0000003a284414890401c41d01c125120040300003c450162001454a370740c102e050340c441c0410a0800030980141c2c0d82d001019032050780900c078a603c0000c01c0d2844400c3c8208180350b00b4845120450b0880021603648144981244205000003007192148004500f404500a01c004006030010301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 376412742 1250 376411492 376411523
    0x913020d0311101401050303040e061309050105011215050108060a09020a051903050607031401030f0812010f05030709140a02030601140d1a030606011d040b0409080301080c0d 77
    0xc0504406401907042181c0100103010041040c054021080012100012203140701c0300080a00c1d68140d000510030341050108000d480c0080346800d61210341140d91460141c00c07040310400078103004002401d29071134440041b40919283d1a0a000e40b405441e0110000c400401c0050950b0800d0080202a030001c90205120f0300a0790440d00c58584010402040fa42e2034001007650b04c0ca03801482d0fa4050700302c01d41001841402d2148940102440c42c0a1200344910401311901801c10f20000304031409140d014420b00c0480c0040d50703080070f1840054046940d5901c1c0080d8041d1181c001c691090213035045c000f80c141140d100c0d03201050310036100c0564640e02c40d100c480c0203400050800d0305204001e1510074003108000014485a4100340f00050980d40054031840429003c040080c02980314109000d510b82e00316003102d40310061088050325460100001c030f0068007072802e100d41c0040c109180042000260300c05135042e11b84a40458407801101c204000a00003600e501078a08203c1c6150b00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 376413992 1250 376412742 376412749
    0xb09031c0c05060a05010302091324021b07050a0f0f030204150b19020114091905010605040606051b01060303080f06010905130e070e0108030a120609060303020f0c091302 75
    0x10250011500348650411416240c1c01c0c1480c604031800d014030f45d9284010305c21450402002e07030308900e800c14501086150703903540c5019901a00c018054520040b0007101c822121a0100c951800020544a0b400081d0303641c0240c0c1d038081400b42c0c51040d44410804200340c60520384010455110f218001102461038090000401105146039900c0e60026004500507103000c0040800308454408400700302e07003080d0000d007110000510350706450007110601c03040304800175400c003001070700d03100c0c9681a02a07440d11600400c410303404140c1140c10800c0014880c0d070414081c01110796290785110b0b07450905c1c0c7d40d241c221021400014042101d200103d60018510520280d04c14010f040000800da203940015045280014100b40100d441d1222800c0000c02480601d00421845c0c82802d1716504042c0b8060312805454008000c01c02c521b40b0048804c0890340002004000c10300080200c00e0b00c81c10029210140c00f803498245200b00d54100f072031418489200761041c3d1702c104400100c0411035080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 376415242 1250 376413992 376414033
    0x406030906020c0d05040603050604090215090a150c0605090304080616030b030105150f0409120507050115060302030f0c0a09090c0c171b0a020609090c0d020301030312060b0903 78
    0x10780d6401d0b828003541e0240c103800c110101080300d00c1d0700c62507200c9260200040c140e81000f4841303070165040c06210390050711107561101324410106a443c4d21030303651078003185100191794000441c0780089508055070607005200d0300400ba016110078442a07440c7c562140d983d100390310400c5025032000300010000402c00104655000c141e10703010400300242d200003825120140c60b10507020b0500d25402e2094502003400c06490182614203010400064a4076840110b01c2c5404209002c1c0005078882042429803029504500314540800d115403155002402500212800b0400c0098800441c1464113210181c40050980b5030340d03500c1c0340b400d02c0f0100000d0031030400b0711001e102188254000088101d0007050010492120141d1111070111423403d03012044242c80441f81c00006026016845241c1101c59582c420f075240e895580701c40f541752165124071800e4154a520210011040681c000320351650300350403600601c111922120324020900c0340303138038480d1b043d030000040e5180a00398004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 376416492 1250 376415242 376415261
    0x140904022803051c0e0913110a0b070b0a151206020706020d1b12060f150c020619081e071101060b0703030b190e040609080918060310050705040603 65
    0x7a103038519580b0741d203a500c0c200c500c1c04051806080228040300c2a40d009030244c4190310200e4400c0518240b4113403a8003000c42a01000d0105240d00703203c00000d44441600400401891141c02d65135007250030040c0c8100e17400d0300d1802025050100360f20207403041280001c05d90300c60660020240d0250b50b00c5000940c071407041120895028085050303500010700c074804154600d00004171040428000c020302014004008603d420303e44a4240008515401e205058400360514860764032100d1800b44e41d008424000251f00c0040040c504440d06030110f00a4841c0c07115485020b410317140c88441800020300d962403017201c95040e030005418031b803040440922050140000080303080e162070388080943c0c0f2206003500802c3d100ca40358441820701c20110051550b08443c4d880407141040c812141452001e40060f00c441d1b00c90342e524041c02144d4003100c6c0c8030b09008210070121405041c075040703022800c0702c045100c1e014100310710041112500034184109803550314103242c01d06201c03007a00102030900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 376417742 1250 376416492 376416559
    0x607050310030f11030d022109060c01020a1106061804020d03030605090a0204030b1012150209180105100f050910170403111c14031312080114090402 66
    0x4400404214800f1543c80d500380120b03540c0340701d0030380e69040c18642040907203200c0c2190310401040b200c0c07000113401c1e50000b0040700a217565816a19000032901c0c002c5040d4015503510010300803003010b801000e00c045020021080d9250f9694007010498407001d4407055890500b211000500186800440c07048498400c0c1400908580c41d0340200f030403800206d650304000c50b80000d05000b80315456070030952200c41c60f45550110360410341d400702c4040c011b4000500c56128040220f80c7c250040d0150b4103a01c0c0003a0040c005a400303001d210042000030b204140c0650480d41740050414403560460502c5c9000e41c030f60368a002d0444091050310368003001020104001302002c03959000d40c2c200e00d0b42c0a14004d54801018104602e5050f0606824001403201503034018824001c46410880025064205a60709a02c0f59100c07034502d00380d44108440200007441141c00d0180c601d030440d68060684095014100c0d4208038071080c840e1440059401a5000e40c0a03505074030103030007042210301ca25a401c0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 376418992 1250 376417742 376417771
    0x30406090b0108061806090c010804240b0109060302091806030c0d06090302280b0a0b19080c0a0f050409021f0306140a03120804050309031002030f0c03040506070503 73
    0xa49031a1841e42080c1c1015915030880002e0000c0744e61102c0005107141c0004024050f03c2c00c20300d800680d90003d40701940d05000c01c200001d41801691821b0103039a000319101461050011808800200003c5459a0201c0d801c14408905940300e8030a681e00903030094480c80f4802e04008040a83c80b078000c149a074144a04c2c030044240751a2495998140b92141c40041000c58480c0740181c18181e0b400500c3c03120a07030400f6036080145800e941034032415000f40e0800001d0b161101e00102602001020079008425801e00d921940b07a410502c204403180c04003643c0c3c150400b8003c001100600c0d20440b01030302c901003018001403030183c0c003114000d0300c02032030a0920f903840200c0d102031410303040810740483e5a0340400c001400e8000c02c0b51140c3c030380403201c059140d819641c0d8540d075401d2216403541000041c90000d82001420000c80e80003103801000c82d4010081541d44401035402120040f650f80a070310041554481d0000549004a600c00c1c06842603941d001401c4607190801001989010782d40c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 376420242 1250 376418992 376419011
    0x3020c0a020d240e0106051f0f181214071802090a0f03050303010608091f1d1c030f0b011b08070812040303050f09121c0204171c090308030406 63
    0x10400c140f0600050740c03400300e4070460640c54075003141e00f182e0103280100d59620012080407000058000a043c003403e1045d114846800100c44100301641804001082c420000c03958003a0300c00c810303220340d20455000d46050009101642c40d48013902c10491801500046654541d007584c000c0d00c503001d0090141c195050707441d0302c00101c48404e50300a940a41002006200e8107078440e0105034000c00c0c1000415081000b80c45200d1118620b42e641c901310b9940300344103204c0c2c03480200d084102480351001c4855035450034100707802032518100007001080c54100790307981d10b51250117140d0290f50161102e500030860354141084000c2e0701c9a00303ca000d1020061140001c142c58040d144031400d01e40b04031034030b20b028540981114406807460520300f01400411040e144001800108400780c5980b598807840c41d20030f01041c07500068401c80c01540081800300300005035250382c0b9001d41c00813045030f0b807908100710044482d0015103861000184d60031000d0001c40d000c100110307000b0788035441c0000c07003600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 376421492 1250 376420242 376420283
    0x1a011d040f0207120c0b0c09030c0405040510060819260d0204050a060c020f2106093009010c0c0801020705060a06150504170109050601080309010f03020c0a020d 71
    0xd100601c0d411240d40842d284040c001e8031400c0ba072600350b050506141c00c40041d11500004403005001010708400080c1141c0340c0d440510119140d510094000d204c035080910b8029103407020b001141420501d0308500042d00340002541154400b5400b112402c4001207441d84803001050021040c42000d5011ba9444440c2d240345c000e08100a2004005807145e003080d0800c035a100d2203900c26010843c00f00641c0000d43d807004e00028a030310086840c0300009042d5804801e02031441c8854450a0060780204026480007084d54558101414148845c064906014400c0000d40703002d1034441800038070024245502480712404040d00500d94054040e580712051800d80e803200c141254143c000c0005d00601c00081d003c0c2c0d00250009100200800b100c0600060180c011445480010303020501d0740c01c1e81c0402980940001c0341c1010584026603182e1004c580d41c0d500c030700301c502e001a440030300c0d44100501c60700c25160303015030681c09030120f040760350200026481c0d62035041c0c0c0c0c00d1003c50680d018109 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 376422742 1250 376421492 376421501
    0x3040210030b0607051501140105161e0b0603060c070f060506031002040b0915090f060d02040801051608070c020a060c021f1d0d08030c0708070f080904050601031a011d04 75
    0x240700704018050a640c480e5101450001a0308c100b24003020001e81a02580c1c1140903240c007148a100582845011410051501c40c03c64980481c1264030f402010f05000360350b0740c020301c907149c01d50032078081c0c0d210440184000c0c484d9403030103807000405247c20703c0000ca00d40c02150300444010308407410301c1d011290030710481e801684031500701d29002560403414107205403c95800101c6e0440380c0c2c101803d100c0402d0404203001e0250f4403075a4009108035405502d641550b001d88200c01c000c1119140100c0b40040900c030315000f15001c10f105c4000123220710f00c522900d015045d8090003d08480c3d1400b8000d480c1c00a15100c00c0f80d008154144098100c1d04030764540c03000120568a444211205014000b100d41d15001c00c24000d03500c0000c01380c0400c5a0904598004010007510360761031310313035052411b16401211002880000500700d5036041c050040d0103043c0889007150100305a03201c20005600b140c244540d01e00d01004899148031441d070048184501861200010b06205070208000a0441c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 376423992 1250 376422742 376422757
    0xf0f05011d221208060301050f0613021b030d05060a092703050702100f0e0307030b070c020d0b0109060509090604230102040f120611030702060a112b0e01060b03040210030b06 77
    0x240b02c1350400906240c240182900321180d610440c4150402c8808070315034207214102440031580020385607101102460440c01514081c0c0d00b030340c3d22420100402c0d40075140a0321001e00c69500000b0218400da45031240e490380300c01e03d00c0d01003800c200e80c50502141400582099040c410240007040c0981c40d04030503c540c0411b00d0769030300f1250005082c007900e411040c03207120340207a10841d018800183c0d04109180c01c60b845041401c90f4141d14800a07601146c9400c2c010305410f5540000900c036080e46d0002402d440048070007040c50350300d82e107009139524403c99003d8800c2c0d07a086030078a4440500301c1c4a00414001900252609032101c621441440b20740e07003d0014480100740003018089580b1071100503c000c0b104091450a010600940d1408050302c003010403583c0c0d41e0a040a07480e0f1004483d07100c10f6181010003500c0c007940d0032156100fa080050307031147d0700f41007500784103290620502040d250489805400c546403502404a020320b41204c66081c1030b40d48021500c10ba4032800605001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 376425242 1250 376423992 376423997
    0x50607150509030c0613210914040c020309090a02210108010c030b1e01021606030c090f0803120408040305150406141003080a09090f0f05011d2212 65
    0x100000352000604492005140c1011900140319000000902180880d00800d0007607400c42107003101e060610b148241607109017904003008100800e03258100c03099100701d819004c030714442c0342d224606110540301074000700703130058004100b800840e01e054102c1d642c01102d8a1b900508018520101d50740380030b1140d8040a0440b1700000410540b6000d0217450405509440c080c03000452086c081713660240c845501a51200300d00342c2800d10350b40308000080540f5550301c4c0d40c0640e0343d9184406001803010058950006120f403101141c10322103403e40c0011030f9180707030040d440c0400690184402400c0940112126a403c000000105100300a002c0c11655540d0201029040515200c2c04440c4e0380202186200c0360201001042d40b070b1001c3c484212504a1800b5070390715510502100c0b200301c240c102030b991515280302ca0b203d94040d83d108005104d590501048180d0300d031a543c0f02c00302440000c4401507502d13400041d0607600003001c480109081c1d03080d00c800802d200d6480000c2254081c008000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 376426492 1250 376425242 376425263
    0x303051b070323070b070b06060f0c1b090601030608060117011d0c01080f16030e0a20011101060b04120305040b0301091b08040f020603070e03100c03050603120702040504020a050607 80
    0x40d44424030902c0014605c882102d03150010075a1036500000004104510030100416412050721303550b8100c03039400e01c2c00342c1611112000400402109140101524029001d290005040e0350003031041d68159681c01004069076032a20300002a0300083d6007050206540b581030060911903440c286482c0080c1080107400c2070f1040f07000041550000422145280010030244040001088000d0503842160701d0f000c51140310f1102014605401010300410900d13040740f40a80c44840c401c40803410385401d82e5105030401d1042992400d941150245030285c00c5c04020030440c00f21901d95560a076442400d08500f0a60360321b4030040140c000740e0100032003944484040900c2001441085082a03050031300c0e2000e41000c2c4c446220741040401e00234058000000454202030080d44c1d0000100c0006046407101e5000b031030b40d071004c0c016803000e0703501007814040424203078603010950b802c0c9031034510006418003101d03408000c098000940203a80002182e040800e40d9142c0c03e00925089015071003c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 376427742 1250 376426492 376426553
    0xa02220507020a0b010303050d0b0904030e0111010902012f1905100203070f03110c010207050a02030f010c021c05040905090d090e06010c020d080c0312010806010f0303051b0703 78
    0x800d68200522640c11500500d0b5940c0000d0210210076065a40514003039444840c2c2e10301142c020548000c007164000c000d082000101a0b200302c100300840390a90300c90b05204400d0320b0391801d0750314215000340422004d4080d030030340d1100390005d00c250500200072143c00182100010b0705041c00d030034043c400008003140110520ac404c01c189081d01c0e8092404620b10319085200030801440704c08007008158079051040700310503520094860301d0342500000c5503111760600d04255154003c49080f40039004021000c04059010310425408800b41d4005e8585d0045c81209210280f504001360030030300c94207100c00b04403420035121325441102e00700014030030109a0000586902e50035882480103200007010848566071015120030400d60644809a00d50345501c3d0a01c81809501440c4525220100e00c54040c600d140404034122001c5206580c0c40d40d2300c80c07601c0d001c103003039078000540071942c1040002c080e1204804450032907040703d01650784c059125903420600c2c0a0302041555816840755450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 376428992 1250 376427742 376427809
    0x30b0405160609090203070e0a06020a020f190605160f032007050312070503040b07060504020a06051204030503130b040507081006031a1b0309100606030c02070e090a02 74
    0x2001c818080e4190321140c518040004041541c24091080c81e00d0f0040f010918817030103045090160080200301d00070054548100958460024900764031a6180300030ba40c40905001415120505294541c64841d038204030303058415501012051641c08550a004800701f00301900c0c01c4400c0b03109980b503aa0300d0302c4060703101190010000c042c000740d41100b1300c100000d5400081d01d4403114408072910307490703503610705205003140181c0d40011040300300001c0c0d920070000d0640c04144503500c00c4900303e55207910b40c4c2c4100d07a0740c003900f140111583c03190800f045c086030150002c0d59014000c84940c03100e008055540300200300060710211010391142505100c003030424450700a07406035800d020070078603217151100140340b290041c1d0f61108000d41b10108581d028105210b00020040c001615640d003000805107907911407520048810a03d03225000c10114400d01640c084155140d0040c000a4103201800007e410040c00e0f220252007110101401a2912418040081c81f0a900003000300c1d082c05c01c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 376430242 1250 376428992 376429003
    0xd0609081903050f0a021326030339070609020d0609050d0e030c06030a02031806070c0204060509061e041e1508121c02160807020102070f1508090a020a030b0405 71
    0x10780d42180140b104548103200035070320800300c80022061120084400c848c0e11500c0032802e07a070356001e0100000700000490889500400001c800d281c000401c08040c1400c9030068030701c510083c00700c40411580f03000c540d030f980110020b10f00040c03402010a003681e0b245011203140035000c6506410600e021103045400c17000c0c4190f5024241c01a0503841c003c100015411b20009005511281d800300210302081c0520070240c0c400c0c1d0100d811589203060107a40545020b1003a98200d02c101d06281d40414075040c91a001c42c040c1c3c034050860101c000518008481c1c40844c86090385d006079030f031401c95005440110401da2600c1d19510700054040d40b00c0e116550003400342e080302507036030b100c0d10450304e0600c41384003250203011881c002c0501110418520001921500c2002c02d0923000340d4010b402884500d500800301d0601c00d030226608550340c1c203541103150703080c0e10070110482030000700045d140380201d81096001042605940b80b0305425030025080f0804c0780c0098400f00c580030100310030450200708 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 376431492 1250 376430242 376430251
    0x80a021306080f0124030e0a0f03110601080d05041202040e01021b0c180609040c0503031c0e0d050901030c030209041104050102100908030621010504060506010e0105090d0609081903050f 82
    0x1500d030b283c0162120740c00c80e01c50425145c404151b0f660201490025051003a1008503a001501c200707105c0c81400d0040250b5112503c074200782c0a4100009100500000c540038141c481e41c890a040500c2c0068000c5039038400340d0142e03006030f260b40f4452903c500070b2008000d0030060b1050441201141005540745c54205414103018040452201c04880c0700d0848455100e101114030f0b000a941c6c0d0320701602d0042a07644485e4040c480420a541d9900000506030040d004d2103904100c005500040d807551020807868002c0441c9003005502c20551103a000440c0414050402610f000c00c1c900c0424115015615440b800640206003030000b580d05200c00c41c1c00d8001e0311014401c10704251515010741c800581100d114070b03000c509148810044405030542c1d05440c2c402044649014203003a005030504541c0035001611229400c100c035802281a14039035000900741c41c6820200343c0c2c0340d030300410300b581d002e580081d82480b1040d521524080380d01d11007081960080740c0783c10a1406100290b10252 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 376432742 1250 376431492 376431509
    0xc150a051807082107060204060c110d0b0f09010e030d02040501030c02070e1311040e07081606080a050a02070f080403061104030224130602060f09070f06080a021306080f01 76
    0x1104001040002800010b5692242011040c86001451070740c4a0305c40c03c0d100070003040c0085800220349400400d200034942c01440b410481c1e4004030b0800a00040d407500042201d546000802c6902d91b5180d40ca660062031480002000030040407014519004144030b017128940000b814002564140643c0301e803000c030b0780000d044040c100010306c441000010002260312030040840d0050080c4501c002460b00d8003d0400c001c40c070040c11410f9103600c0e0a00400d0014410850180050f0400001c1003080b6034140c0d80342006038681c40083c0002d00f41c0a0001d8900036028400400460000c110340c03103c3c0c1d0700c6800c043d076503549945005c105a501e0030183c1d4940c030034240410005611120840d651130210303080914a030301e0080207041d0b640d015240c1c1481e05d141303a250010402c0c03038001039424010b000c501021900c41d6154640543e8038095401400c0d07541d041c9460412401d4011051150400a030301d0b0050b0409205080928000300cac1b50b0b0204002a0f41001440b590f400e01031400f0b405002d80c20b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 376433992 1250 376432742 376432753
    0x70b0c2205190e04120c0b0109050a0506010e220e120406080907030c0e0603210a020c102a12030f0b10081b09060f040305120c0c060c150a0518 63
    0x101c04203881d010007080541100019031200d145d0603c43c2d050340300395a034810045201940c50b1101c401c002c0004136144042e051404021076800e40c020300d078052403860010082c4049112240c4003001d070300000c01c0c62038541519a444c1543c00c0d0300600c0901200c6c61540c0305951218540000100440e90242c0102070039080601d003840490784556412064811000000255031142d802091602034403030700e1964006c0340b001ea001d041d09102030043c18005c40503401c0300c45607000b041c10010303000000346400c03002c0303804505000e02d0140401050490751411641283ca00d07581500c808102440943c0b8040c0040d0344c403c80050303460200d1150310405401a10b050b0303100600f108003c2d1244c0c8000d01610700c010f0010950401100c5030780e0445030b03442d44c040c00c0a03449154081c800c0d8444d40080c00200c5040c000c401245038007100420030b1b10503180800c801442005082c205015a0b5404402c3c040018003480320300710006001d10341d54601501d8425000240381c070384491030350b071003910a606540c52a00700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 376435242 1250 376433992 376433999
    0x5060a050411010302070809030a05030903011112011509151808030307020604110f030a060207030306050d1e0311010504050a03020706140301090e0f0a0c050906060f070b0c220519 79
    0x1c1c1003600ea1940d03020301300141d42e145982052402406107140050303141c82070002880030084040083e051140060380240000343c0c40c00840d14071b50048812021404113900c004003c02240c0340500c4007030a010341003146045458214880c030391401c034841031001c1041641900d0074242d96503030a500030a07001c0e0281d0301f54142400c0094a680b80580f001d48600c00c2d07040800060741c0d40c2101440d4140d40141110005136403450f1400194009800030b030013003441c245000a650901158079512103134451080000c00e10302c6e00f0240d0701b44e200c5010a50410900c86000e04942009101d090302035402600202020b00042c500245000602e41082080105642032404007a05400580e0f040d5005030394045011100d00302c400b442c0c4ac0380c14910080500c40d640819041c0400641c5c3c0e0010b480c802d540001265891205022a501c0350308010803540e074007004aa00172442d090b601c0e0b50042032800086241061007010483c0001512048511624002408124602d020513000b030801000c03180c1003004a14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 376436492 1250 376435242 376435253
    0xb010b0717030121210c3503040f0204090501021c0b1c0212031c0606030212040204021b01150501020c0d0317100902030a0605030c041e0e0f0303010b030405060a0504 73
    0x6019000e032004c00c0900081010802840700702031891105107161484000c40307140040a40001040503100740c4103a143c0d203034030307440702144400d18201030f280d1045500c050700e44103595580c030040054643c500c03181d011b0b0005a84501070311155034010000540c070f4104055884a400615020110a1030720f85078007403c0030f4031071801c80802101c42c800048058040790010500e510310100c203001050100041c04140c90400f800040e10f0f0460f04801008210389a080c240e080b40302c1c0c946034004c6c0c8007038040060018505034005204204100c070907881d080c02140c0100c0d080d5498180980100e203810704017800a96130410403507072009001c40f080412452103460140620003034400c88112042d0390f2001501110207a07031801c0061115220071560703460080510b4004056501a07907111740141c00c0a11420302d8103024020128101c449403180c62080c000ca488010506000038000901840e00203200b804420f102860081410f05182640c2c3c4c9040e1515030300b42a0002c1c000c00b40d103481c020a0101081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 376437742 1250 376436492 376436519
    0x81801031406120c0d081308030c0a060e0a0213060914040209061c0f030306030b0f041106030702010f0609140c0c100f2c0d0e03031c06030b010b07170301 68
    0x806071110702003c21400704032070403c0c00100300380381c00210b820a40c2c000c00c035880c0300509000c40044080c1d40c5203038880450300d40313a101d1103040403899405804160081109a809101c4c41c44900701100c4c590a40380d03010984490384090300e0b54100d42d41c0d000c1045142e490307000e070700340b034800315601000d207031409900250050320050800342c021903820030b2010511a03144000039050f504480d1040e410807076464020003602d59070000322283c01011000c1124a01102d1106000e2135200100c4050720070901d09008281d00002d000f80d0444d900d41441d0031a00083e440341101800c4415008662000c0c14641e40c140031101505090682c02e0401c141c40d41910007040741c1d04c150900000c040b6040483c110440e0141010500560210030760003190442e0004072078041480c14881007e40320000d40e0644196001496010241e8254004111800041070000703a05030300c0003c0c20500180f455241c0c2c8072448100000d8001c895000d5000030141b00348690714101020520552091074695810b00720241c0544 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 376438848 1106 376437742 376437751
    0x4090501061b021e01090b0d060f05010903020303030a0203040f0b09030909070305011232030a09080a0c120606031713090605010f2106030818010314 66
    0x4900b24516141460b400400910520100303084851450600030803c504002030300c080880e404980314050100700d207400e00c2c0011200d05102c180c2c0807400741600300c181400740c1558100300517a0004100d0f51f00142d044405030300c07902c0b5490120611303401079000500c2014440100902910004040c4c614060221110030858403000015402c0b10f00a0086006031003105080a01290f2550142160b0401d0182c401142c200c4041440c0020342481d100401c003908005400c0c5840ca07440000346000d4240a0082d050030050356030f881c510003406110b41908d010124440038180025907000e8001150442e04909038102c440d964074243e58030602500b07128442c008008a01c0980511544043e5141a181c40480386640340041d03030036545011305040741c12507042824001c83c5460003100300842c070940c1042e40f034414600004060a0011410070304240c0380c00000410380da507a110b1242c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 376258992 376438848 := by
  have h0 := BRFrame.cov_init 376258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 376258992 ≤ n) (h2 : n < 376438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
