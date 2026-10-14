-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0992
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:41:55.054231+00:00
-- url     : https://prove2.me/submissions/24cb8146-db3d-4392-ac14-b8efe481f26a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 178237410 ≤ n < 178417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 178238660 1250 178237410 178237447
    0x150d1112070f1a220e0106050f03130311070b03011502031c0c0302041703031005010f020309240c030a09050d08090112091b080c0402030108120d0e06010f2306 70
    0x140780d0003992401102012030044d18150405038144980145020840c403035451410a02400103444d00070b14110441107032440d54000500710114850040c0c04048c10940a6010f00c07020b0a800f1003640c1c401da5a480381510a60024424404010706403041c07582c0303080c800b00840300b10040080c40c00b03000105100d407000c020a03103416401c05060f030030000441d0010705014004000035461006507580e18290141c4200c0040c0c5500c0341d03040c0081004c41008040d0044140c0d800002c05466200a152551001c443e03071f0a80140321004a41c030005034500c030078201100030540c80e04152941602d543e41c0d84240300c0708894020024112090500c42801d066200b1182ca043c0c0e1110500c01046c0c074410741d04e8004101501c40b0001d04035044001007000b01030f500744000000410110740842c02c648c0341905158071000d800d0564540102c001500c50901c003c4d6901c01e1440040100880e405503850b0902c1c40480c01442c042c0e8405010300440d000c4c05440d01c4443d0030020840a4091400c01d210000210030014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 178239910 1250 178238660 178238699
    0x70314010b1f02010c030b060f0d090f050703052e110904060b03010504180b150612010303020105190515090601020c0607110118120803150d1112070f 66
    0x1525118404016a00d03800c03409003102002c0464010300302c4002c1c010f421106100d440703005041c01d054000c1119a00d540c00e503580e502280318102e80e1100480c020350000e24800c02c0c010710a59481c110303401448800110300042d80d11840440303140d030241d0008050001c2200f8096801c56215010a11202e2040d404c05894078035011713805400c004042c00000e0a03940c05c0d0700041004031010004100034a8030b07002c1c402c5820307030310088044409181e80784c0d07403209400181280908000c8425100e01e030b40790001280c0d495085407281400c103503128a4002e001e090181c66454104405254a0001d030340640300e010700551180641100b8440c040051229960001b03002034107500502d280200b454807020020044144601c28140101443c02c001600d112400c880071521441c843c0c0048c00300341c80440d08292107070b8112244545039524000b41c11030301c90604660b5500403807c2461802000500d2000c050401c41c12104c901c0940d0f492a11142da40120f0b05c01d014070f00c1004a001c001c4c1440d42d410001d10039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 178241160 1250 178239910 178239913
    0x31212071112090a030b04050a030e01110c041802060f07020f0108091009050f0102040608010f060e0a0e2d0901050c090f12010204150804060608060709031e02040507050715090302070314 82
    0x20f40e45e03501c854440c4e1800f00c0382a03c0c2031b000410030008050380040100601c1c5000d081c003441154a0060107030f914081016040e0085664410000e51006000303224611aa8003c018603640c84103420382c0ba409800100081b8020381e01200b80c807020b58090b490651007901c00c1001070208000002d10000a400000801e0700e26004140c407c000140c000e000170006484a600c5d000c0107540340c507003500101501584038600f04101d9a903182c8050b038414070000b04030394900901c8a410385810b80e00040c400100c502c03aa601880308219a0070201209075007500c9022b070300c03008010036078880c511910107109266640c0e6100d03141c200c00540030301d0010007c9200d6407104e4001030506442d6014a8070007420b541e0716a001c20b5105d000c0004101c550b000b44005001c0000140805017068080a450032100c0e0000521410350380c0ea40031103000c00c42c242d00100c01c0d001030080c422400c3c881e10103803099001e12002e0340c2407081b00c1c41c40c0205040b1400381481403603056008107011031441c3c64044ca00340003402500d01a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 178242410 1250 178241160 178241179
    0x51e13021302090f0303040b03010b030903090301020414040b01090308090d05010207080d0506090c07030206240405070801090f0207151e05101d0907060e0a030203121207111209 78
    0x1503200c103441c0824009000800603a2241c2040802418044400340540300f540200b105022080c01d40c01501d046400b6107001a4032a04ca080c01e60742980035802034940c00d503201080001d00b07811001030300c1c1025002603908205d0402d8050044400070283c0c0000b4007030328070401c80e001d494101100d000035a03d000b803000508150555403005129480a2440880076445105214040c64041c0c043c2c1e8000c0e0640b000c0b03078a021119640a500c0c1c00d0014280603042007406101c200481d94020b4024003507400400c00c204a2414a401030b000c00d20038083e030201946407004a8040a03d54401ca03940c542c0c20500001c80d40301120005c001078070648059500b028180310300c0e11154003d0b40180b50080d14405550010b40e0704011000d0b81203e02c0f01c0c103804411984000b48202550080303041401d90701b55240c006110300030000802c03404111036000075010321400d02c0c40001006100d028020030a28140010708640b1540412039000c10403c6420449400c0304c842202201b4500004005070304d03000d0201d101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 178243660 1250 178242410 178242413
    0xc09140d020a09050906070804030801050d0c180f0e0106030201171008070b03093903030417010203040203070609080d0c0609020604060e090f102c070f12051e13 71
    0x240701c0c5540c80a41101d0700e40c814042405c00c02c2c404181c3c0310141d441c0c00c2d161480d0588004141c004107108644c000e0040d00c0f01c0304140401c0d808000083c115000c54401512103140a182c010514aa00450020728101c08010622818010541180d80507502c000d4407500420034511003d0014103c030510f84083c2c203000500e4002804054000d0249048654491900d400024105500381803400c0b00c1550710444118000c40248511a00308a00c80c41c95461504610201c2e10354801e41e000b1811481d40d050b40082a00c505400851007644290240c5e040140c3e1944142c812010501a002c42c0d908580090b049903440340d103070a8862801081301251000c1aa004200f165026400250004803441601d003100c2c02e18215141e00320030440d40550b0f5178985542440c00d40b085c0c0b0b01602265010303210f07040c40500361681c0e18581714007a5079205442401c000a010b0035000310082c156001c140748500512800c6c109200345031203840c215861549030b50400040041c0408014084000000c40030400030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 178244910 1250 178243660 178243669
    0x106050301110c06010f0b0403060b151b070504090305041e051302120907080c0607080405041a0a0b03010e070f0215070302040914060f010e010219030f080a0c09140d02 74
    0x5403001c064900031a0343d120120300103030070540305801c02049a1480300e030030002040400101e404994000d500054010f80c01e02c00296028101000a80768220116603a54081c480e21100c4101c8075800c011692a25518000d00064a1011300054081142800108680c4000315600c001c2035104812000c40c06440b90001806940401c0c066002168041281c5101c1c03440151020b0304550120002c0c030100d8940786110b544c804144030007900814001c9036410400c40c5140644004d000020030601010f6a9642c41104010001c42145c1c4513050200001034050080c0d0110b80c140c0700d5210040760340342e807009801d0350f0000f0606614000c507c00d10121480074000300b403040780952295500580e0301c3e03103800540c1c1d040c0c0e540c0e0289826004940005d0151a80e034415082d03420715403c0c20642c010b01c4042c070041c0d046c48041b900c03441d02d0700b035440d40c11410594001881c01041113540c481108079120a42030404440b20040c49001003400280148441101c01c031601e03800a0f001010480c0003405540400d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 178246160 1250 178244910 178244921
    0x102030108061005012102090109050409060203070e0904030807080c07320705010507021201090206030a09030807080702031c0621050609030306060423040908090a06140f03090106050301 82
    0x40351a00300400f44a0089070b0301e41c400b0000e0509207040a01d03050401000617980c681c020b180c490180c3d0001d200c582d242d0150004030f00500c4001d108100d070920a05065002e5031041f40e211000075400b8a03191007030302c1e00ca004039000e66010ba440e1489030341d40400603182d00201428071103c85109001c0701d0001101c0b426209140500d00c226114100c0f03100300c81c1c500d18603910049051035000300d01d007030141d40d9204023506e202540403180d10708603c00500fa92070042c24440300117500300500004000b50408103400a299651103a030b01c004196170703811411940b040c81903804100680041280701d000c121080c0c820f4000c0600324030000b5802e60740f40a040e04400c01c1544d0110300855011148050050034031045910030841406149140741c80c0d4005036180c81140181e0088040f05002400000e07040030001e00201d0b0042c204220b1344210303085c0051542c05c408655072280c01500b030045440c07849140f020400003480003800d030400000801f06134403904000c0c0f1030302066681d040c0004080e542400785 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 178247410 1250 178246160 178246169
    0x3070f05070b1215061b0d322109030a2304050103050603070f1d1806040213021e0909100305030a0309030212070f2a0302010309080909010e070906110a140a0501020301 74
    0x149507c3c9005030000d00612041e891448120b044402c5142120014600300e1881007510380d990381d80c030b6214403000186003141c4004100000050020440c00744000001032110340700079150300c0300c0020120a03c440e41e8080c0066250000000e000800c402c3d40240c00141e0040402001c1c1c5038950307102c4090302810442980803441c14031060300d40307610510700c50381c200d90448038041c440300c1001c03901801103640d5030300604002c0c0606031009101000c040380d903060f6030800301c0071001e2803698981980c494406402019041e88508007180100308251207583c8030700100c95001d000345003030072107000c1c05600900901c4820390030b40c0152162441141e110900815000f0322502411440074007134140380c50b100002d0348050440031200385800e0a4003400b090900110786c1d09217000303c0d020020345001c130507900820035200d0300800d01c03c3c000310f00c03880c801c40b0b5107205000c9030341e0b100180760f5034080868031040500c5854485402c4280d9505c0401e148000c20400d280c41d86040b02e0000c11550b940600f240c0c004da10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 178248660 1250 178247410 178247413
    0x609030207090f0605150309030403120e1807091403150a050f09190f03090504090f0501180f06090201021c0302030103030314040203100b040e03070f05070b1215061b 73
    0x4040c040c142507442405140b0301c14070030400c84e150828000c501c0c040f24001c0e80109840f0f010000078109102081150042c0d6808500c81040d5005908040c00c4040d03400c00c1d29118144e0b10111406565101015a03c200c50a6a420040324501209180401d0316040b5440e018055001808400000400c4d030314007070300f15140d0000309031504c40010325405401902d00a490381051100700358031a5001d441b48203064010344000e8400d43d6500c2c013030383e402500703600c5107800504100d045070912001d6a80e0010b07590160000340030300d008a0013554098000e4550040c448020000391201040c8503511101c201803040c012030300700490010341a0300c03140e0302102c4400000e03000001070003090b80c94000ca0031515202d02c0011143e0800d640000d03180d80a0b00c01e6910950756512101fa05d03642c8a030842d000101c000029280d86030b00c6410140b983ca05404401d80701440307560750000786041010101e0b10801c8406250009a48800c18003030006c0500072002c0c0d0340100244241e001c0c2642007460500054050360 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 178249910 1250 178248660 178248673
    0xf0705030d060801050115050d06090c05030a0c050c100f0204050303040e0114040603150c021203090f01050f06010e06030703200306010f0e0303191103030703140a0c020a03120906090302 82
    0x41000c05540b00e90300402c26a90610b8010000503960a0f04941d1115160419030b03117035560084200014000d617800109518144400510071a810100071406684032400070300601d5481035040e00c580c401e41c8080107440d40580b10782401140750b64011200d1300d101e44005494a561900000e1658006030005568685c400300100a4203c0e5944000c8829a0648060041900d940c6441c0f0300364404068803150743d500d0360708210302c1c180300340200080221804181903c0b801c080203816510840c03018098860f601e001c0c0402e1b10000280021485504165104801c0d000c00c41c00344003003904050940424541c5681c01c04403244944032048081014180c2c50340e03120301d003000005080d503448045540c117000c2c031000300400302e460100482d00c920641c0a40040a082c200900b2100d058260a41c800c942c000030040c00740003030b07046c0c000b050719004024082c00181c076211214805c0f0b90b03a5200caa00903130b012501100009015109080041002040004800e240c41d2602400e4072007a80044005130000d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 178251160 1250 178249910 178249927
    0x1511011109130c0c03080a020d090308150102010501081207080c010f021c02030402010801050f13090f02100207060c0308072a0b0106031505060702030f030a0306050a05041a0103090203030f070503 86
    0x10041da200001ea402c01448900c28000d0003508030a8844405001c002c078200c00107030f12204a80454001030175002c41001003404500f0010214201aa4170310b01c1031541c244251900e40c414042c5a050383e0042c5e0140082c0035004080c0c00482c0e203e500b04403146034090101540d1201d080c8203481e400103851002503510350005806254901c0d15010030344070340e481413041c0310261741d1281040d4191003041d581e03c1c40250079440000d102e484e50780d400e2000e1078107140066081002c603403000307041d81c0d20a0718081103400007400140d803240424003880780020048501c440100e03201e041042d420110900345008428691000d0440101040441c022094903119121040050031841c80f80104002d2500f0041a210003510003601c4e0b032544030f0107105c2d0350b0110b20f40c810741d5024442d101d201c1c0c3c0c480044039a90044a00b015002d001c5902c1420320542c180c20f00000c20341450f0103580558980303042da006035107030207000550003080803203002c1c0d8152005200005400d120240145002c0340540c008645810b40d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 178252410 1250 178251160 178251169
    0x1203010602060708070c020d03030609090c0503100506090a152105120f07080d060e0103050d0306080615042004060908100b0109030201201203070f02070f1511011109 73
    0x1d40f490040045003400c100f20113500024481e1134a42c102c07002c001180c0c01d814100c01500c16904841403003444d01340c0403020450a41812412138009900713482c5180191034001c0c00306e030800c417081e036000032000c0c00051038085180d1018240b0f000b401180c1c1201511340244030007090350100c6402104440102580603c00100260314440140600c201d1908688140030b00c818000c80f04010122400825902010100c0d0307081580504007040e4440e03804c1d030b542e00f03080d0303a150740184000b00880c2c42c06202007541440411041d00c109004000720001c0c00c6010180701c01054050030210b6082c048080510212400c40c0040c0014000d0780d85801c681030501004074100500c02070300d500c8040c03403e16810780c2d59820218281c1281d4090a0420400b04101e41111000d80c2e550103280b0303680240700c28501520384031000b85006000a55800c1070300a01001c043e640c800c03150140580404800d4401c00c010a40000f0b09980c6201518041003142c4081c1031150a5400041e280000380102152000e603e080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 178253660 1250 178252410 178252423
    0xe060609150114120a290d020f030f010c0203131403060a0b0a03080f1323061b010e060702060601080408120414030310050f0d0206040b0c0f1203010602 67
    0x44035418500c0c10034050910180d4480424070341030002003048880144020010384208210348840003945180604201d8000c0000345182d0710690281030280324020a04c05540c01000b41c081c120302d90500c020340800808810348180f50390f0500c11061101c25400081c0540c0c4801d07285034005640341e41c221400415100c1164000c6008409100e02c0a00d4541c0d000a12513000b0a00800018040661802192600d549034201a1160600248100c85d402d40500100750803416035400d0f440e0070b03450341351070003034a00340f0a2041c1200084030314810ac00e1900703a0003080310200113000c000440d9681c1c03d200342943d0205c080181650410003c0026030341e014845141d11100c2460700301d40d14134180d560340c0381a00884030000c400841d5680045c0c201b00d5003880301e12b078403064001200e031a80f42148603204542054042d05015010140c3e0010031410904038208016500070079240c01c1c9820844403040e9038000c40180c42c0c0b85d12660554030702c234a070140718044e80c050402003254be6940c10164080c2c07500b80d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 178254910 1250 178253660 178253671
    0xf020f12010510390b0717060d02220b0a0e100603020705030a030504081201080309040b0a050a05010e060409020406021b01020a030804080307140d0914010608070b1b010501090e06 79
    0xc18071204840b8203e29603010211060079520a201e0040008041c5520710a5000083c4803206080600407415004082c5400051f4040c800008170b9030f405081c0468031150060081d08440020540b03490480c00340c81c94200010306160018a07103558a0000f015031f41c0960100758280f003040b0522610480707800c441006880700b13085c00d625004541c1e0790340350fa0307204100039502010799400108040087c00411541e680c04809045082d6585401900c3e44980c0036070706541c41140381c40803540b49400c00e650b107042118401003408400c2c500d80801904e0700f40c101a251503109900b0000410340d4a25072000e0700280103254000c102810075007080700901540700720002d041d9030100d40c40303e0020b41c0c011809a4010ba008220a40300c0c0c0f030301501641c1d8403803070b207101c0d5610301e00124211002d1001c0c0d0f0f11141c110360040318608090000005010b00b00c1e2400c0c01840f01a400100f0103025094400c1c2c010801c0104002070000240c011600c840c1c2100d10a030028002d00752502003581d02f220b802c00a403078216 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 178256160 1250 178254910 178254917
    0x9010e01050105192106090515061b030c12070308130203030405101704061e11030f06150705012c060105010809010b0405160320040302040f020f12010510 68
    0xa504240010f05280600c4030801000c641c6038400140e410711591004181c034458242150140300c081e00b002d4040e12107070182c850228a8840040c200d0712a200c0e065001420203000d40c5c0c030b031031044401a84a2901190007c0541c40704200801c0d110f0020092126001041400c09845100600c2c9c01800280041d2825080000d4a00350750090ba4001c0203c0f01110800c451844040704164400d07540d4071040c0e000604018011001c00c0140f0041d50041d001d81e80501103607042c2085004015070071141080b100d405a02002e00018140944101c50550800700040034603807800010504000181e10408007100c1594440daa0614204108034a00e41136000d0302c48803202d00e103520101680d9038041489a0340c1004070b0344001c42d11280080d480716000400c00340050283e880e16030360f40d030700700d070301c04940c030400a071900e041001000e0b0300c01f11080d020360850b030049280601d5074007000064100c154203028403e500300f00e40c1c0e020b4061030004104900201c803000d00250325007403c000106402c1da08034000e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 178257410 1250 178256160 178256189
    0x9060103060f1d0f0c120a1e060305071d041202070e01060e01120c021c09080f0a0203060f06010206040b060a0b04080f1b010207050409060e01020a17280c1107140901 73
    0x2180c0360700c000c2da00c1402c0050840c40d403503959081c889014084500230143c1c240e10441000020007025004801034a000308210745060341c4e555101c60b00c0310000440d8605112300d240100780044c0b0403d2050103201e403140304861220340c441552940d180310a900c05804a4104807250302a540c0142c0c04450713240c45507500f000f25072611a070282d1113810b60005036166070020000110031a000e058240c0180503054100c0325104154048182d0b40d4420050aa1103807003840700040d81a4099482c00e403141006a0261081d03498131f41e00d42101c07080140c0800c0c0c0c80400580c020550b503030140080c000904240004020803001c0800345400c02e41c15107407201c1304252800d4442031598000614004941080e17400044450303190920304003e2440c7c54a18036554000036031012110703441020b200d2a15880e1102c030419031190b61008501e241b00741c01590700684a038500c41b1020b00b00c1d031b10000041409040800c0c03e024840c2c109402c1030700a41103e20700070054200c007002801c10140d0b21b4050071010000000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 178258660 1250 178257410 178257421
    0xc120c050a120b03010e030408030d1109030a030f0507050d080103020118030b012102060f1308010513020609030a0b01030302030c010f2906070f061a1e09060103060f1d0f 75
    0x402e20035080a0940030385690078484903031025448004510b0109094030f444581f00d060054070399220f2540c210700c403070900d0807100704030122004544032064010010103408032555801d0f200c7c0d19504200c078051003801e10013003010900174408403034a94419a500c88481d03045100240c208400304901c1220030180715000e1001840b042c4980c1c1c1510090118116019022045022460a035030f2000350004004030304141d01003140c034050280140801615a81d641c0c40300502422210120355206c2c0c103990845d902030240c1408401030550040190680f19a07004640383e21203000360a0707100301d0050384001800d811991080c46415030302e0901110030712007c0302310f55000e04004011442020181c8001d12640ca00740c1e9000200c501c1c1c20340c028003503041c00d070a505220000b021042c0c449500b144040800700120319044040d8203200c120103226a951190f11401d01854401c020700050500d030342c8901c0414440390b4520810001c041040c807030294200030710f5585d9041e12000e8030090a5808070b80074440c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 178259910 1250 178258660 178258667
    0x803071b02010c140f10060e09030f04030f02010314090d020d03180b06041409070801060f0e0f09011509230105060304060228031d060622020d0c120c050a 68
    0x4050130b8110303014a2600541e2450103003805840c200345c52052060014040600140ea04035000311540703441c0000b0f5a45d984140d1a81b284211000005864010001800002c5070f042c0d844001c00d006240003d040c800c4046070001d01c6506443c000c4450307001441860140340d041000d1904e60134a0f00e014001209054098881c2c50795030317800100001c5001e000140e0940b115401001801400070021200b070401724400f81d01c0b80c8950007051865400d0507000310f445401100310314215040007040343c1c10ba9894165000c00c0c1c18000e0a020365a5480b410504011007614003400040c0940138000218010152841c0c001100103c0311902d098985200402940e958081500d50058001c1400b59980304148003a00443c868524907698010707a54000c0d8800c00e0703040d444104100c2503007104c50208011400103950300c0100b183d4a45d8840344030005200600d2401d114070704d901d00461409030600b061940e110080e15803003c190000510040c52103590320003039010f0407480c0743e040d0411b5840c02120b824000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 178261160 1250 178259910 178259927
    0xe0c03100506121512151e3c01051003060e1f05040509060f0405030c240709050303091c0804060305060310020a020c040b0d120305011703130608070c080301030803071b0201 76
    0x13821a07484c1c1d80004110b81d901f050101c0d0306480e0380b20721903510b10b80100a0b2403620322503030100144408866080e100403104480803904904025806103143c1c1ca01810083e50740c1c4048090010142c81c0c0341c002032a0292802d07110302a80f0014501803c1c02c080042245440f4041d51100744214180001c1c4003003420049102a00309100c20196403580d580c0e8105140307180b04400030a2528400d0350280030b2041c0d0554a6191450f05488030704100e0303100c100c8221000c42103401200d91540003003180c00c0a610300040d00c2c080041c842c0080100d8041c042d11050580d8006a205001180d10340341088001c0c9400d0080300e40034800c000c0118103011a00300001d599080480445000b603603910204c0d41e2035618640c0b229074460748000110403114a5000080140c4401e01c51000200070842130102c400c0008825034065400b01400044c0e6249460700485039030402030400f006108ca01d00601c0042007803140158061401610001d580b0306100000405450401200c1240c40b2090000500140e0f802001d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 178262410 1250 178261160 178261183
    0x7120e150721020f190c08040f0504050f090c121e010902040c020a030c0803130f1a0105270a06150e0a0b0301120b0c0415020f160e0c03100506121512 66
    0x104032907408400080c0c030740914906d0050074004001c02c1c000f50350040d03044480c0c1a1001a58140302e2500c8401400e69002000d807003401450b080038000c02003600705a80601c041c041004116806481c00300305404006502421000c0e0a075102c111f60015030400e4091600c105c5803500c01840c41488644008005012750840180055030010114210f0b05507050048192030b00720400d9030320f03041c0314904034801078515115a200d040803140001032030324280a00050080740360840c0301c0b01001601000b008e2880c018100001c1c65a00e85011540c0002c0241b0600c14180c940c40704c008403100c4404024004c2c4141e800108100300c108014000454608060000135a002c0540030060301e034a401505103005942100c8025203048690864040d80010040301d0001840c05a5600849401c40802c0e44c840b01d00400040080c810003082c02c0c03249900045a0058240305811140354a50740004c2980d480b54400300c8501c00080c0c188806061100c4074031041c03003000c41c1c10303a20200d180100c850b15907480224 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 178263660 1250 178262410 178262437
    0x507080c060f040e0c090405070507031106070c15060f120b0a022a0c09130c05030a0803040209071116030b0a050907050f0f0405010f03140607120e150721020f 70
    0x70800311401700068800e21000140144a2450021801000b80d0407104040d8000b4a0800c8000300a03130001ca207882c0202c51716500c80001881c2925407151741440541e070f00700c4030303540c803040002e111610507206401f03407242c05201680011641001014607070b015001c0101103204020309602000d2a40a11101e01b041039194044898a03800040c201054000c0f515000340c161004c00034010204804542c034580b29015606030261034030107150b074540c41044000c2441104201281c054500303001c625502000720301d46500f405140320119420140e4903108440502d15000301482082551514a40c1c000c040210812040c904000358a5441c5001c3c1b0506004100c6451440e88940303807005403814214000d04140551b5070340700d6000741c1c02c01551000342e590300c1c500761860709244408941240070b4001ca940e051940e5080c1c1114030002c0c1000da1503140a445000f4915070f400001d03107032061040140351103142c0400702c00d00010b007a0100f03041e4914880740c810400c18a0600041c000d44050100250 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 178264910 1250 178263660 178263689
    0x602070512150a020301061b080d020f13150801080a020d02130b061c050c040303090302060a0306030506040b010e0c0405060403121b1202010b060f07060908160507080c060f04 77
    0x49040c00c00c00052500415402c0d44420800c1104440d00250304903041e580d81d0000e40c050f50366172a40b1055500340000d020307050070001652026640d401074428099442c410602e00300480b03040d00e03003d04007544201010024400110f00841d0850001c60041801c200a0903500c42980c0c00652050001740e4021300c40c080c0603016000c05125503009030130400001c1e1030300d80c0d541441c1040e1311405a19100b950b2400d4286000511340b41061010b0368210b9034107403038072807406d41584d081094070303040082c007d400c0603074815000011440400c0380b02c0c007403070040f03088105a5040403a4a142030300024202ca5600030100300800217501d40c0012102101c1e0000788842a00350f400402f00c0d00140846040c940c0503001d411380009018820b200c88241000ba40c0003000310950304070510009014a0030200d1401409102810110715590451581240f20b81c840c10700d408843e69602e801105114415141c0d51f020680a1000303490400001e1400c04044a180d8200011180364074110712450247e07803481390050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 178266160 1250 178264910 178264939
    0x5010b130b0423070f0923040e010c05030a0c02010917070c06020715050c0c10090e09060411010806280302040e0a02100c031b06020307030b010c030f1b0c03050601030312050106020705 81
    0x740c503203902070850a144401004182552017102e207d1585010f80f20f1460a020700b100201d0507c02ca52071454503880e1181103540307691071640100703084000d410070b654807500000002140844644103441003502d040342c58004a00303201c00100701d603802502c1990320604040c010361a00c1d4100c0203d5490170301c0c1041e41c410140004a081001c1900b0a64000e940c5c0c66136070142c1908020b400058640144190520f0b58030450510f94600f02540c0191a1502008a402640d449081d096a208001402c039201008031001c4040e100c2519803070001ca041c0d2020000d200b185005e0042c0d0311440f44000040401254503000580d410022951410034440d07603410150826010f45001049883c0c0e4241140464909003008006584125603032030001c0c7c900f48001d070f125030082c000ca081c201d401d0b6851a141d002600c80646660182c0e072480c5840c104c0c0b003204400000c0c0c1444075500071310f11603005041d01d54507501e07002c0c4c02a0741c0882c0100c550f50a050040c000c0543c0011040c0c02c5030811603ca80000106 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 178267410 1250 178266160 178266167
    0x7170f01090c0902160519050d03090c0b07140604050c130614100c0605041a07020f0601090e0106030203190c0609080a020f06090916090b04030c05090405010b130b0423070f 76
    0x175402880c0d40900a40b40e03800445c0d5161540109018006441000481c41d0049080310300c1020020700c0c0071070038141031200c40048405440f00134441d100740402c900315462418079202c01100c003200d1643c012484500c00382000c00020022200142e0280701017070901076025654000c40300d643c2d00511440c0d05d880600341c802d094a1400c140c1144041000d41058100be40841d0701082008100c02002d0010940652001448220f0318002d90040c002607400c0c00c0d03603000541401d16a40c1803543d29200003101594007032040440b46490303105003085042403843c0400e4988040d60041d001e110308110100601b50f0041881d43d0402e1381150651002c500c1c1c0000030704a406415803280d04200390710100a00c131109800319000462941e107131211900d50707540c49200e032417040380801009504e5042080000c0c3c1001075000360424800c10012501568180101b4040419040760031100c91b207610111103d42031600c11f14001a9034140350303d020340c1c1095502c8940c002d01401600410100302c401d00c010521 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 178268660 1250 178267410 178267447
    0x200c040e0a0b0c040e07090303170a060f0e0a0b0102010c0c0308130b04230c0303070605150423100605040311150a0504081207020102280507170f01090c0902 69
    0x20b1148400080781800d0b075060a282c3c10a000c0d4800383c01415001c2031760380b070040742454201c95065035a0b024219404d501c0b408004c10180807040b44c252602d101181c8050b1606010019202540000340340d49481070b0342c80b081d50344100c80740e030659240140e9580c40c2a4030a03807842c0c9181d09420412055180e0004d40c414118407038001070031940b00441403000b000041c50b600201550341c10100740c1030380c003021103090b00d0700c1482480da075050b03108110b03d00010343d0b5074028a922550011603402400200300105094403100000141d0010100c400010844209050190020401c205420380d450902402400c64465400054107100c00840b40781440d55401184061003000c0205007a1281046100070308030390400e00401c0400d0041102900440b0321755030a44800680590091042d04032a642c0e5102d10807168500d4056210f0b0960324202040041100000911504216295840f0030160b42c900b0310207404404001039051031540b8000c039550700d00003000d0b10f041400050796081c449000c00da0050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 178269910 1250 178268660 178268663
    0x1e040c0909031706032d070305061806010e13060203090f0a141213050609120712030806010503161b020a03081b0601060c0f020d1b0501200c040e0a 65
    0x20704050041d410507502407200521040c1c0072094942a484100825031518030480d01c0340580f46c0c0441a4009446002030a546c0442c544c4082d5003a5075125262242400d6042318049444011050b00791882401040564010b001c03e88600e1480d00f04800142d8040c00b001070040c0aa54001c000701e6410750003402007001074a1b0010445181e640c03d403414500d050245445000d0324021050b98005907060034040b074405400140c1c04c015450308000401c046504092401ca412620701201c0f541c400100300040d60180020103059890f8620030b05c0c0081c2400d0008142c5410400c05006209030590400100e01c8818502d00301104021003410440c410344503c2d00700a5440b05200c0d2001080c444120010154040c0b00203c40b2202d2900309219940c84000b8402d20340042d114900210103c8d54184240f10341701d100401c3e68802160301c3d110f2400310300d410909480030720a00c0008001540c2c2004c40341321640c1444050140d0315812000d510f4803841e80145413401a0345404464403080c400b40116031419 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 178271160 1250 178269910 178269929
    0x4020406150c0b0603010b0117040c0f0306090c090b030316080910090801050a1404031202090607110f09010f0b0f070b01170c040510170c060a05070203010506091e040c 74
    0x40212a000621070a42d0540a480d0100014041340090a041c090285180c0041e1202c55542c0820201840c118800900039140342c500143c02044019034854000d0065000b1000400e0b01b52a500713044800201c5a40191961460095140702540300401942d000d000c403100b1100488201b8149091148511410160302240e6800540039040d00032034030700e00b66401a4000c105c05c0d914031641d281190280c04010400e01250300002e40000e110740760f8144404003024000d41011001313404200302c3d410100e42294030f14201c03000c00150307051402e50564003030000c03684410360354503100c642e100014903030190494860b000200c1c0c0c1f074010801000c0700d040c2d81e40721182400640c0d4845600150345410701220b10709015554100d0050700d0a03000c3c031402020f140500140b014501a0a17081486512800409a001d0b10038010142c0e80c4503005854010b5203603c40540c0c507a4540704160071504010103d5112708035041c14000c07080d09011102c074003215807440314540c5403507604120346519110791003200903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 178272410 1250 178271160 178271189
    0x9120c0801110a030e16030b13021503040b0f011802070524040b01080d08071101180b0106110111070b1e10030b0f0f04020103020a0c08040b1e0f0307050304020406 72
    0x7190036030340043c00101040d541c100b20301d0038840722240e1121007805250480010686051011a00f0007041c80c3d0040c0d202c01c1010550b046a5000c01d80d5080c00d400306071440880842000305001145a4a42e8088200400780e075896041c8026060007102c0c04602e00c6100745d01285a50400000b000b03040b80000c880c1d015034204010b56001c21014030002c0390304999595140d030000500b0f60300013560500b44403080e2510481603950803803c0718115034800800000e5900c3e616900d601c0900381c4084a4040c0c002d031801e08066051810207006000c0703c0301001500da16000d441084c2040c0c9a0690790340ba41c4c4201d40b08810b441d00140840341c0d9401080070040300c00400180000110340b142ca000440784034821054060303075000d000d8010070404a0304680d01401a80011740113620035030041500f182c0e941000c0e0990700554503400c03c0c40e0001d03000000050300000340354503009030a1080c0a01e180350741e00700501d440003202c0b0101c55400050100e1051100100c01305007155a10340242c0c01410001c03c0d40301c00f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 178273660 1250 178272410 178272431
    0x102070f0b01050406061103090405101211010216060503010e0604150f030b060f030a020d0525081209030d032c0303060a0501110703032303160306050303070309120c0801 75
    0x3101c6028800c041c8214074100002030b2190185080708803000c56140a54100b84803101407001a020090400c9517402d061070020581445d08000a4980c5019601242145540000182c94800744030f0024008081d107800800c0896408800c803030550300c00c0314450426450340000311300900b05072603840c000030000e2200890780c42100c04030001200c0c05922849215154074040c0306505410700703c50b68250300301d810050094100b8400285400e1704c80c000300c2d030301e074030815010002b800c444201ca40f04180d0244810070003a1001c102c0300d154210404039040ca07116101c00029650300070644000c0c10726440e60840b0070041540030100800251584510b00020601d001c905e449a0085134494490281c125000c1441c0d4495416409442449002400000e080d91400e07a00c25500c1c40c0320450151505400009000b840380185010b9038400803071031700800784a0030107019030b046600054029070007400b000f0302003548010a1800c5900241c41d0103481007050408d14200100780e00015015030a01c665850f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 178274910 1250 178273660 178273673
    0x10b0a060234050d0f020907031a1918110f0403021207050102030d020c160303230328021e09040608010605030a030e0a0e010807060305092d0102070f 66
    0x441c0040802c8140507070a407045844244441200709101000074007800610142c00c281030b586804074010880044075000740d60002d0381c41c07038040341c09030002501c0d20903041d1017104800000c2d000080c101d6400848a1900b00e1912540707446200300c00000043e441422211b146680c803000c00320050b09041030b5951b0300c003d141d512541c05448120300451400701503500d42440420210183c4005234040c5152845010703207070003e90050803012940b806240c84400004841100c4440158400d0300c4d81c0201a051740c032050b201005510340645541d03402c00c200411b10584101c0c403044000e01050740980da203404451040280111100d08021400000d885901c00520402030b04645000b22028411991610802c9003039500e944541ca400d0760080100900080c0a5005444c0d4150301500c1d48a0b070503034564031696400700030380c0002c119400c071100074000d0b55451700400c0e41c80a83e0380000d2030941c1c0c070410300402200360064003499a046081d081c40c001c1c10b081d0100ca1a250300b0403036000715400a0304050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 178276160 1250 178274910 178274923
    0x30109050f01050d12050307090b070b1e13020d03090806090604021203120a05061503010b090112060311040f0e0a06020c060108071802030a0204030218060301140c040314010b0a0602 80
    0x540701c1108000986840c00b03c201e604d40e07941c001c122a507640d100f444262201d4002070045024888060400303d114030306da10140544901a600c210021b0130b101c402c0d082107038200d14440c400f041003081000600303102ca0007000c241d030394103592100800140703080c1141c030740007c0c0e00010702c0c0e03015250034407101110015009008074001c94a6107990140c41c00c046682e482480f090642c00700f0f034180019495a06548640ea010300060180010104102140c41482d4070903000102007281c040358074030555912610703402c00803042d100200102400c41c0c40d00109007840150041c0b0440c0c031129609210b01c4507410150a031002e4000f120341c4403119242c603002a40000326041607501ca1040005602400000c8200840b4821005040c00d841460780c0c40e030280d40018040035085808000000058071052103841c205c10b0345802d070380040d0800c0b200301429a00b802c2c109a02038000a03080c0502e140503038040390103c80d841800e01044080c0341c8c0041d8050810301506070b42c401d00dc1500007030040d0700440c12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 178277410 1250 178276160 178276171
    0x9071b2619170709060c08070501020c07060305130b01050f0307081b010201110f04030312060308130e18062a2206111207060b040905030c1b0904020108071403010905 73
    0x103a044100c1c0c0c858884142c040c0c21660070b0001010340000b041814090b01c52000c81c0c0d402083c816180c0151521a682642e001c15a08000c0b41d0040c001000300986c180310716500024040440c1c03085030789580719080c0400b01130240910a021310f5040c41c409581c10041a40140074080a560490140c1100114262400558580036500300405000b003495041c045403020403100c2d80032030810b401c5480449200310031510448035143e5a4401001040702d44020f4040000c076000c50700001400c0905e030300e500c950040c00305c04a41040041c400400306022073f00d1548082c080702e1410119007a20610386500d11140300f400c83c0324000151103240c030410005003230038075407144c10100d5010b0342d0360404440b6032420b602c0101003504400d65062070803443c0380080100c240688404114510f51400107812141468002c88095000003049800800280000d0650703e0b01044560b40075008080441c10380d80e00100024100141c1200291810f40151100300c003070340c1070400d05034407580c485a052004003c1501c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 178278660 1250 178277410 178277417
    0x50c0705071710023c04080d03060608040b01030308091f0905011409030d05100905070905040c390f0b060f0a060215091f0b09071b2619 60
    0x20f40400030101d402240d144811000b0b00f080c1e1041002d4052042c0b10b180070340500400381c5c040e8045043d03040d07400504043d2052030080e0024000b01c0202a044aa19621181c24800c10404200200b20400c00b85411a60103040c5007049039201d0002d541000000300c80402c540c0448603682c003107129603070300c0700000c640f18500030441e03154034040146411008031607200150703104000d2462400d0306600b00e607810000082e22040990b40f10074150090350000c40d986c000145203044200320900c0e0038014100e081c602c40c208a01c00607070701d14401c1070910402941c640e051100a403a0005d00980360610710b08250411014029a43c10b45800300100c84117460952052005581c01207642c139105402104807000c0e81c0041c001d01c01d10412202200200803ca800345004009200000c1d034540c14203049540b5405038001201c105840c100507044101501013020813101c10207030717004130222110307050005400034140c0048901e0441140b01201f80540000b014110200740c94840c101e03000d86520f4018582d44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 178279910 1250 178278660 178278673
    0x90506120c150702060d0e0f0111090d0206070c03050a150e06010b070b06010c0506011d15061b030403020409080901022b031104030b0c0310090b090703050c07050717 73
    0x9015654500d800a41140c2c000324a01d524080040c041c0b00400505102030100d50520000100c44d038221800140c1d0740070642c0011403c0c040018083c1b05401210320202915800c1c04074400c0403500d031000d2408000d0156200080001c244421889014002c40d800070132542d903880b4030314000c2d0143c0003604a07440c03d40d04065600e26000000304006040ea251a440503041c203c00303840f04c994454020703001505200502d5400c1d00421020700c0a107020300000750048881d0380400c400c1c00342c0b88100a206d42110381c405040c0c0d0100783c0d0758078100c0324107071201168480030001400c18142548520741c40250b20134500380024081241c0348018000200c2c1c01d800f503c0e0034808040707040c04006d034192400e41e1605003d1549690040c0aa807101c409154502d00c028201603d9540702d030000d00e07050700c13030b00c0c1d825201104000d98484072004e07500c064502400c080c031541190401148000c80007810020606890384001120550841c0a0317480454000c4111204240d4030042c1c0140c0600b0350b90500342a004e0380 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 178281160 1250 178279910 178279939
    0x5070f060912030503040818040e061e1510171005040b04150b0307020703140a06050610050423031f0b04090b060d0206120f070f0c030f0c0309050307090506 69
    0x40b00c003000300303a400d6101d141c41c65403540e4031100d180d030155284589241c0351204105450b280d03172080d0304e4460968401468203080c5000048880c40d120f03118132007603002c840b00300b2000c1008a42e00b040d0f15007054448000c80380780c1e00b1040e180c4240d12024811216192000c100f40b010034840d03058203c8505071010803200c1144400e0201303070790340c070f6904042020b20500c04200c00e9400d00d00a651015561040d18a8151a550b50307014803451b032600b8000c25031007000e002050019500c1010340000b000c07203a10f000041964030281090142c0d00c55440ca0094600480c800c11a07580100e400d130510060640300016040b03a15520304001001860710154548404000340b0b040038481e14081907000000716aa6940701020840350b85807096080340c1200d014016000c1075110b0380085801440108100b4141d403406040c0204088009510032040018003031401010a4004507288400c2185240804008909040c02e50341110294031682e0140309030040001c442c20740303030300890250108417900003495244c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 178282410 1250 178281160 178281179
    0x403051210080c10031b05031009091203050714030109020319060803091e0405010b190302160b060f0603010b090319081c060906030c1503060312050903030705070f0609 74
    0x90046103080e6118071030150513440e290302c5000b01000f0303a01d0042403580150f076500c9034a010096560011440210500104469080a110181c4080401088280c80e80d803108009151112a51401d140e40c1c0e0003c544030600c584250b200c2c03000e00034603065032969108117040c000c0d0300c212803084020015500c482500021070040000720383d400303001942000700420400c032680d1503900341c034417044c00e0110040d4643d0b1920300840c0e0007020a055115256102c400c1c10703a580401071001e1038200342c81000070544503030401016000043e0003c0500b19107503140d001007072144100d103002c01d50268000c000000e071400000300030032155406070b042d0b4030403c0e1200761180a82e250010002d090140611025407007180905040c2d00c54500100e000c914150365a854404503483d5810998600f00d409405008102d04215040e080d446285000c001040c6580c07211624034048409201c100480080d22041c4d070f650810960b5a6281c21a00f541c1c0ca1540c0c440091107902e2041c4034150214000020005843c100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 178283660 1250 178282410 178282441
    0x70b09010c020d090b0a03020c1002071407030b010b070f020409110f06041a090109030f060902090123010e01020a02030f1e0a050c0108130605090a020a0b0a0c0b06061204030512 78
    0x1034641307a0481544c284034041141c0d8001c03e100000b007540c00d0210780c41c200c0042207142102c1040520041c0d0b203031594109030007145000740c50300805038440b41c82080040d40c5116030a045400000b90f50782c59100500e40b601401c030800801035407040c00c04401c0e2042c06401807e5603c0d8020488510b01009510002e100c001e001da44903012040f0401c000e1540d8011314030340200144401490301541d05901d99550700e148034880c010070f841d07045d82c03203d1300c00c11801c16800b01800341c0b03021130321030700303040e0b2001941440600030515150422554920680c1141d00030001d0252603680202601c00415038170003510781c0e0b40d50081a5035008064114411400300340810382d040007641140251512454107801503c0c0070f003020700351503820f030120000a0007161b014072426020320b00501c0680500c1d0b483e0300400c410384005810032206e0080c100400810f40d5000074880060035031261150700e80755a20030020b2030324001c6914016641c2028001c000c1059807020040600355080003c0d02071588401299400c42d85 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 178284910 1250 178283660 178283683
    0x105040b030d17101a03040c090207150f150e0a05060907080a15031709030f16120204110313150209010801061b0c090905010e0c0307030305070606080102070b09010c02 74
    0x5030003c4409610000c0010020341c460440b1032200c00c1c0c2e5550707080522410980d203054891104000c001e100030840d0344038403c2c00801c2001170940c00c1c43e400751140c1c5585207000e08109600340d65004411100c080c1d54005013000b0b143d075a005240c0700e035221110b1818130000c0f034801a90301d00d0180016003d1420301e00b0140592650399411246030b940d20004001083d003250768803007000b04403c0000c00104800d03124101d5454003013440e40c480055070301380340c58020801034084160700040d04500340310102e80d8022080f5042e030081268045070600110f8010994060350000c10700000081010030084040308000d560b00c00d0002c024911000c03245c0d40203d0107142c0032540000c00382d400400119200f0340b4210003076402c11100c2100840c3e40c0e50345c58030140031544880941c42e240c440007070a100c001c2c4070300e2039003450b440050401982528002a1203000380d0200805200022960000f40200c0740d200d03074041c1c5407400085507204114241075007107000440300c0040c2c035070078400560903051002c640c000004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 178286160 1250 178284910 178284917
    0x90911030312010b0f07050303070306031b180f09021011150c07080d0e0f0606150301030c06110a05030307232106190308070c0f0e01090911180105040b030d 69
    0x10f03400d103607421354650b001e88203480400109000c110041031003440290f014039041c0e00d00180703035407440c5070240d50404120208110410042e904203c12040385048850885401d800090700301d09019030301d8020301d070004020790000d04000c1003020441d044044001c3c80c4c44407804880c41005442260440c05408403843e030f1884d401480000002801034014007550300010101042c1c000c64214407514149a1810070250382d40260203201c16410101c40b222881c1d8442155a4a15811a220044001d00600c15081008403510030448515130500515403042c1d804000d807a03a90421101c0185003108891011054404d06452145075000c0b243c11902000b15600c0d030079526441c4002030150000c0000c04054100c1c08403042059801014901c002c051842541c01549a551504003895005039a401c502d5403200b0f040c6050110842c0f0b007000718112005510081003032642ea19080720710740720004459402580055440c0c40050b41e007071516041e07410503030781000100384903801c0590320722001e081500071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 178287410 1250 178286160 178286197
    0x408040506030402060d1b0801050312091905030a060c080705090108060405150a0f0806090a0c0e0603010f0f0c0f020d0e010305270a060b0301060e06280909110303 72
    0x6070411501440d4403d00040c589420802000944403d0350b0040034a80003450719080c0040c51941c1002c1b400b400750005600070610080140c1181c807640c41803089042c420a0000a442080d03602c21240b000900800b900b0f4030072107810340c64900060840000c0a40100720020000380740e540c0305105551261105039140740c0c05d0b481c1d00080c00002c00d00a8406000e00078220000c0c1f1440e02c44103d203c00902e018107042a1091038072109609000d005040000306400c003104800108100410342410b60700540e290000300c3d01c13a100080d0041c0304080304001a142456201400781c5100d43c80720f40c20514580b11000e04003c80030049884e090700050403030100780d07000d00026041d40310358081036003d21451a1000510a40303201d03000741070106260a21194401d1124100b0440c0f103010382c0d00c00c0300d41507000b0b025050070410f84070300740d1800510703150044902d00c00401c0300b4030368a1440c004204000e41e03041c41854440724820040e240d4140c040d2015160842275070100d0a0001c21141c40d480c00c0200a0300f03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 178288660 1250 178287410 178287419
    0x11121b0307051c09120c030905060721020a0c03060c0807020105160f050d140403140403050312060d02040e0d090b04050f040c140313060c02060f0a0f1e060e0f040804 73
    0x107100f00f80481c1040c50f60303a82c4400d900090001120104822801d455540110050740380062440f05140c01c4a405031a007446104001740740c1219103103802d08800b5054802001601d4200d143c00c52403000a407080200300000424044a58000780c449401951001078036581d45c541a420307034009885c0390540e01c01d445483d001c1070b8070a48000000c01e109144c420b280c0201d4849403003c0e034040500d0251280080d8007440b0815030441d08287d900d0301c62641d12800c00d841c41d20b59603128042c102002010400e10030004000b80c1c1d641a001008550080c0100b00d030200703070300d1131580d904051b84004010038041c100129910151390700362000c503070300201000c106c40310b01028000a08020100e041c240041c840600390007213900c00145100d048950702e11000105a4103010b030a0780d108a643c03000790b421900610a01146641d5416448001a0300102e60118141a01c000508000050b6600343c80c40b40d400c0c564400c0726400c944203c0b0016035000e0102c0e10341004100c031009091380d0040000801304010070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 178289910 1250 178288660 178288687
    0x30f0601020f0c0f180103050c21030f0f0f07050703021e03120f0708030a09021314060f0307080106031b080c01020303013501020c0709181511121b030705 68
    0x30103030b040580784178010412034a02c030100843c01e0300202c50725000b040703048070300b402c2c0601140c240007007418003914140c5c01c0e4450719480e0b10030380303d460200e003030001108142120f011040f12b8400d5042401281d4584942c1800d070b0300d48806000c02c0b440f13500d00718131201000407444400403e18100402424148a81c0681012f25074403000210404080601409003c200b082d0050741c89a12805404907501d9a0392042010075002c0c0d0340d0500302d00b454042c490301c4024490004039440181a0707007104001c5615000a4504035041d44410100e40c01d00c40d000c020030800b180c1c400391040180c420a150b042e1100c1b042a00d445810312141c0c0140d000307000400180014800003034402c20400500c0039112138600e03001038080200408500e0503900001d110420140c00c000344002840300013010491562201e000740040e210398080540888800340d02d4803810001540a00d0603210b4040160347d03211640d0000c0c40e800003040b10f0f4a0426202031040130414400141100c0c0310744e40580e503040c6001910b241ea00d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 178291160 1250 178289910 178289929
    0x902151c180b0f07020f010c0906030b15220b040302220609051003032019110406060810150804141c0203040f050103180201050a2102030f0601020f0c 66
    0x92a005640074818000301c0d0585004070300030350f01e44074407880350b203802c20780680f900d042841c101171144c0c982280704060341d512440c0241520364900c1c01041159910700025075840c80c4003050b5138051400103040152855403022651001031220000340b5541c0e540302c84001d82d01072440b0182d00722001d10300200b648480c0003140f181c55a914000050f0591700c45203054200c81e000c8620030f5450514060a200340340d0440304600010094542c4031100e854200300e196100d01318031110360210034030000c0040070050980b40c0303401e1011700540100002035440b82e0041c050b24060b2404895100e02d00e1004c10710b42c1100100c980a05144d88840c02c0d56152542c50035400c5c0080e0644621714090380c0c0076a49154600d449000700301140e9401075444605000343ca50b005034440e44180d0505242648100c01e80c0003540a1a8400d41c090034000c0d180c0d1981d801c02d44134914110300e65100d440301d01d0884405024244d001e10300540200d60000c04070b0ba5074000590f83c403481000e1246e401e900070b5022491518100c120f8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 178292410 1250 178291160 178291181
    0x7080924030105150a09052115040309050901060c080f04050301020c0c1918020d020f220e04030c060525030e010c08011d0606130305010902151c 64
    0x4a0314289218015581001001030080140340c0000010841c500e492207003648941c206650700d928001024002400c0705000c0e10405000d4540c1881c07046445e43c5100d00c0750b101448a0064036003801c10004904134140003220210003007548000045070504240d02a03d05864590302c40500500c8503403980c50b40364000784045601600100008103581d00c00380042e140182c0c404d0700400e42030030024100118030700000e00840c04100d40b2242044040000c9400c58001e03e01c2510050b41c4114841c0e1640192103620039504108000048600c603002080d40030404088914181601441c0c0382c50701c0f440c0c8203400383e9018000401d0f64081c00c02050344c50380b11541080340f4140c44611502400905031400040c584c03107401180e900d6070b074400840c80a01507131308100602c1c9840c1200b513040096410302c680274044001c2544100c40d0019281c2c0c0c45500c1202ca041d040c0300c0c40c13880e440ea540d01d0301c1806002111402c0340180e04103416010100d40000580d12171006a9803c04079070701800034801c0090010040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 178293660 1250 178292410 178292419
    0x40e0405071706150306072a0f0b011503020405010e01050901020a120c0b1006080c03041113050a0b01092102040f110a091e1401020f061603180503070809 68
    0x300040c20308441d00180b12100091000fa11442c81d1460a80c042010400206802074101004000c4070030b5004048040b21020b201c00c82d060300c00f580a480201981079030300281101e0410240f5400c1c002a01c074203904a4a4103c00407008201900c021002e0380214401d107130101d403005403d207000350301681c080d105810061040300c282c0c0300c0c2a01c590030305140d6600d60313034003082030300d03816030207000c44009100c0c3c0c40b048005030031003100e1030302000a00100000700f618403444000300c0424100b00c0100302c04081c050000b01040c1c1f441d080e00000c003000308000c5d100d000c4110314100c1201255402840c601040b100042807242d00c1d80c0307015062022480c0768040c00c030780c01a5240d40030045005513214035525000030207080340c0c43d0700b810040030341070700413940080f0594181601c02004910840340310b4015105441405002030300c5607030060b807078200b106402d0146801540304010300c4080d003d6500e0342c14485943e09110880605040c01845107910700050586e070000c00106002c10000c00c02460780040251 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 178294910 1250 178293660 178293673
    0x70c2004021207050a0e12030f0c070803030712050106020a0201090314010f050c072d150e0307030c03020618070e0c0f0a03020c100b060306012703060e0f0a0503040e0405 75
    0x900d420742c00310084603000046a0007040d1000d81a40c032030481c03004030000b500c2a0f09030a40d0400d003c3e0703aa000d0202e003150410b20005e03410301c0485c0207014000040802400701c070f0303da00700700c0800351600c0c5140b1445411107240c1000003607400d01c0041c8109043e40c040e141c40400714155140c41850b92016007080d4210340d219448580f0420355481407611500442c0d164549549951503d0729080ca907403062051a042c803220803400c80e03809102d0300241c082d800681903555040c0d01a20708050205251405181d0001140c414185508a85e000e560144207500707648140e500c0b0491000000e40c0080e041c00140e000100a00c454000a100140c2100211a8035800e10355203040700c6005034040021807000039008682a07007030000410a4008501c05d6510500c2441200000b140040c0002001c00c1d04201da40649002d9046945d0000c541200061030104012900d0b13041c900054a03504a08900c10301c034010b54400b0000c400320300581c9040c6d11a010310302d01403401c5038040c0a45000380c000d0740c4c01d00468 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 178296160 1250 178294910 178294927
    0xf04030804060b03150a050708010810180c120c0e07020c0409060e030f0a08060405060f012303130b01151b1a1008010b010e01020601060c060e0a060b09070c200402 72
    0x82194081e104001940803103a4501058903405451010344508c052200d010014001c0420110300106102c0c0c1c1100700003810720101c200202c00000105001d841800c548202144904034041c1031100c0b1402540c86049041d5140308900222908940010050b0058440000741c2e03e015040402d01d540900400326607c1d804040160540d40013a81803000d91a0004c0c40c141180d400c00540307680414105c50420282c5003500228a03400868000903042041d8a0200c0a40312810800080c1c002c000c04078443e143d01d03241c2e95003019081b05100542d04000c1100002440c1ca069484114880c0382e15a12203000d140141ea51030700e0045080021111700c1e1146c03440d000c000d0b01d0204124810304000c00081c0b1001e140228490844e1895025070303042161510440344070340d0f00020040d044884514000404840e40c2c00d15100074070400c0400036442c0604240c420521a05400070010240100c07041c5215448510041d5a40c80041c3e40c02030104120001c00d0460301d005e06a148452880600301510b4a82d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 178297410 1250 178296160 178296163
    0x1403152e1d06120a050c010809031209010221010302150313060c0c020f0616081b0307050a0201080709030b0601140c0607110d03020f040513090c030503040603050f0f04030804060b03 80
    0x40d4425000c40500000b040b090b0319000d0a54400d030014032000c3c0420700441d40f1410740305c3d00c80c0d440c003905100080000c0340c5d0400d410012103124000b8814408400d06040c0e00250103035101d1040c4850124141070002003000080e00c000d4100e0760700134807580070307144500003044081d000200411442d12003086c0050200700b0501802c80034002581e6010041407451041094007030800c1821030080f0f2081c800d01040880f03001d44040d400390407501c51911801c0b0050300c0011400300104c880074902000c175001003080320002e40c0c946e2680c800d880744100360740c505508070380d68055844094240c00360840424841d5000d04001c0920002c8d2541e0103140200c0840358070b290a0701034690f100000c03003030800300c0c0c480d1320140600c0c0d4502085180652038080d510a070f425144c040d5004031841405c50a601d00180c8001c0c0c0d0084000590200c15500499900d0030701c943c40b40c0140c8980e0010030305240004240300020b01c0060300c40e0040320001001915180c40c00c41da010030041040399015074840210089070380 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 178298660 1250 178297410 178297439
    0x40f09080a0302090418020612090f0d0306030c060825030b0a1403060603060c0403171e03070306141f091707090e07030b04020105071a011403152e 65
    0x401d450150b134500d007000c01d110488010b118615034803044203d01d10300507500c0303d04980144d1402411210f4039141c115440d4108040c5a6a5014074443c000b80c0400309a003540100302140c0c09890b0303580c01103680f49000e45e601001200c80d001c2c5c8520790800a0904001c0c03084003c5008060302d400502030359448003081c40701d00207801a03078583c0d002c1c441109113450204080c1d0740c840f074107070701030311581c00e06000340d603928022400020440d0141180c0150a00b00d02000d03140c141a24861540442c504503d0100981d0700035286280003d0034800d003c0741400002d0180c0c81c900300301130300c503610a00142c130740c003c40c1c401800850810040c2c408800503075903022020205c3c0069070403015049441c9808001800c1301c04e41c1642c1c2c5050307045080c2c1080411400e8801c150b0181c2c081c20324a0352184607142c01c000c3c0810350903104858000d2540085400080b50301c02c003500120a030103c41958540c0a407121441e941220301038805400d4403c0d5000c0181e0030040c21151842c01c005860f0700c40d0b16090600103154 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 178299910 1250 178298660 178298677
    0x150f15080c09060708042d0b07050f01020f07021e090a020d1d0d021605030c0120010921020312071d0324010f0f0501050906040e07020a14150402040f0908 68
    0x4002260502446400d040354105140003c24a086000c00d11340c080047e15070301340b10700c006000c800701c3c1500600c501800102d0001156038000c542d02d4400442080d056003009109a0141002c0c00b0903c503100d0326008014040c8000030070404da69680c0e40140d00196100d42d80001044d5240d4044519003031000744d484a20b404140080c02c0c1402100340000d1504640c07044400c281c03105008100990b40b800b00340b80d002044203103490826034000009021b105000303406003050540ca0189004103105154070036400c40841c10100210002500004030ba482c040c0a000d12960311603040410705072401120b48110410800d5910211659050300090500102691403541c8402d054082848100c5141905000d010510281c03a152820320510341d0800d071150144a05001c400190907420744c2d17410068400420101013000003600d04440c0094031504051021070b402c101e800301d406d921800110740c144c03e4110079080b4403841c6d0b075240c00700406095910a500040c0d40e0b02c106900c0421a288010054403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 178301160 1250 178299910 178299923
    0x30a0608060c090a0506090301270326070c020a0510021b0a0e04061104090612060c020c0d02060d02040b1b0f011506120b06030a150f15080c090607 65
    0x80c0ca469041070030603100920a880b405803c0001030314a079290221441960740940c0e00c0b944440420010a005000d2008941c400200c038040c40400302508400303941c1c0d5a48680c0c0c44180e001031141210601020a41130324903944081d0000030400c0e485030182d0f0080343d0000700130405c12030781d0300085140004084602c4005800500305080729004400100402c1181501d8980302e041c50040010b0420030301810062050342c4038200f07480c122031810150b40c080e000d9020304001d425925a140201c2015544089a04500f00316004149a0000c100c0101c40c0c48054040d80803030f1825800c10925900001c4140580c0d0f03070900c00032960803092800b030001c5140e86919000707a040c907440c2a078544010107681e40d00903030501a920501856034000702e400c5504a040c072001e580070200340c1e60301400041466580242000c0f041042c8148544c000f4202c14090b00c01c0000d00540301c84030f41040850b90300410150001c030090001c8014400c21134a540544035048242c1001100381c00242c0e513500000f0242c0b1076 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 178302410 1250 178301160 178301171
    0x109080d060e0615190c050d03020a1b0c05040207050a050708071e080d080618041b0e040503030f2d0402040e010c0905010509040b041401140105030f0c0a0c08030a 72
    0x1c28850b0034a09400003802c58004a211400b0042d001041c400c054210b03a140d450400c41941213801040c215542d160302a0540d6404506804014000d40000c80c400340014104d10b5551f00840402d100c68809642189004840e5400c180c244000781d400042c4c00c41e041d2140c0441500840c00a010341da018141007005804150b140500c501814450344910310112142c3c0081004004000a03032141c00c4030040c140b030318055039250002070751000f00f6403030a05e0541040d070800082103d40c4445112200d0f0070303200640c000303458008440c524441103600801d190300800201ea2900040b031800b9502c150400030407890100019500440004501c4903401d8100381c0c84e06100441c0303480d00a000c00440040300070480d0745c1a07043e00800301c8038144642c6061003400074142e40300751542e81148031125000f80c000d00102d040c50010380f0380d002c1c0034401e28034290440070840c81c0640c454003c40c0c0c000c00700c4034500388880d00c90780d2001e11182c2c000601c031020312801d05042c50000c0c101501552141d00a000d00080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 178303660 1250 178302410 178302419
    0x91024170c0603090303040b10031b05011112030415060302130903081302010e0f060c010c050c0c030102040b041a040e04050a02034c11040609050303040e06040903020109080d06 78
    0x7030028003080c1c1c00d1103030030140100700c105070000050302d134815040103404006031542c1074901c5d034050060b00058240e0042c80c20880081c8003841404048405c00e9a8400414007241103142e110030b10201030150f07210742007002ca07002c00c0600610b0401d40504150001344e2a0380ca038001083d15181d08042c22540e51105104402d040d00408140d0b404501c640b0075184003640e580c002080141c45007065803043e109654601d1554403a04140c40c41c150b84c0c0d1008115810080502410b240c20110341c08009115402c030182c4681010300940d401ca600500d4800d0429051075060f1084c038420101d00640400d082c080040d40715812035550707010b540580050020030210780103060401194488030b045065001007420013541e03111840d9903000b4020714004048040c00312050700c03182580d89480700e0540c20a48411076140e2400014001c81f4080d4540d80341e1199600c040c16120300551040c14503101a11000401604064118007031031403080c4000070f001c00c25903aa800ca2038104d52886018199500018031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 178304910 1250 178303660 178303663
    0x304060903050c18040321050a0e060604020414360402180411060a2c011706010f1103070f080c120c03030a0c140309030a090e09102417 60
    0x200c0f150035a2108860100c4213000b840041e0054401020001c915503620110f500c1003084101410286000703120908020090310b000d8410303403030f1118950003048040b44403840c0034400c440841d8143c042100704461014100081440b0441c2c030217000741c0c4101c07242c400b001040e00d000011a0151002c0305440d08150040c46001c1c800208c140c0a4443c24009101c08151181e010801c06103046440036a03d001c0114100d40e10548144a8904044036402d45800ca0000d84451010080203907100d40d6000e002d400c0d0030005c02d006440c81c3e80464401d8005002442c8901042560007084404036450501240e80741061400038060980d030160022a001000c0c4c2d6040c090003200107441c0d5005030504917a4050251640b00c040e16640740d117555070015440c0f042c002c0b081c000b03c0c4048001d041d40c80e031611080342504c1ea400703030308240000b450f1071401241d01071a01c3c04280c0621084070040078050706403031341c00008110140e182c03071181901150081404c074100e059100902200c2c03064140c11122505181d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 178306160 1250 178304910 178304923
    0x80705040803030c19021b040b040204030618140d0e01080714031f050d080f0304060b03100f0c08011206240314010c020c0105030c03060105070210362303030406090305 74
    0x20111f40100d1903210b14003881c501e11084800c0c3c00c42e00000c104000c080044d00900c03960388020300d01802d01c07906c8000c2c0b10940d20442012806000102400c2c0440f1054076110103101c001ca50100d100c26440b006507520480c00c080e481096030034803210f45285030403d03644c0d6130012903410481d8070081c88021492903004010000400054400541d485100c2d035918040d4000d00000c0d14403203102000040c140142c0d908940400b02e4003405440b9543d01c01e00b032410150200c0c9401c0300c0d04d14144901070078071510601c113080c101c5400034401e540b101003030369800e805807400001040803040700c0c182500504441020701e00c011440344905006440780494140d0965203440d0601055421601444800340d030007008595000707204040459a0b0354030f4100503152400f41d824040d400031030017165195016000900c00b1150903000b1082105540380c201c02d03800a02900c40c13588106000a00c04000b40104403014001c90f00e4142c86103809004c0b610b01091031500a903000c1d000040d1095004c04c240702052028 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 178307410 1250 178306160 178306207
    0xe010510080d0f03021305040204030b0f100303080105011b02031f1103010f0303050a020f070e09060604060302031f060e13030f020c060a12090c03110a091b080705040803030c 77
    0x81d214407a0b9500010303200303100380001c0c07005041d0001201c50301c0b8281156014040c10008104545458480c00d0641c1c81c00421954186038034141801b00b400c0100300a0054120390703260780c60f1045030703003084011034815090400106501210020400c016641840140b00c00141c03441003145007007880b1002c00955000f4091b5001d03020081006001940f00c0503a000709807601800c0c919915613810cc0124502060402041c1d4107004000c2d022a140b1403401446000f800007404031015a101e140420048540a1100a500d170b40f003c0d601180404801800c01c420034900700780010b41070350b9441c0c1c214030b01900b00c51403c0201d010711180b004154020341c1d0f0f10040e202a20040030940078610208419205140800701403180c08034044009101c036030040074071580c0c00110034003082d81c1c82c905a2040055a0741d400e10440c1c0d42c2d0360200c0d036961a88a0a2a151042c405030651544122810b40d0b0230309019040408000c000c00011600c064100000c50040c140c2c0010555038000d0b0b01c1d510810361004291 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 178308660 1250 178307410 178307413
    0x3010c05130b07051507050702041b020619020705010207050609010e16030b0c04080d0e01080a110409090f05060c03010501031d030a1d10030e06150303030c09130e01051008 76
    0x560041408075403101400d603122400915900c20803418083c0c80c024444101101d510012402c001031594440b01801000d4402d583c2031101e2007500d101000d4440d507000582d00140e000c440080c100c12910101c01075a442c41300781c0140b500c042c41e180c060990b400b100c01550194003003420300011000c01d106446126442801070124040c1003213100d1200d0344188000344c0b4210980b40810360100b00b030340481d002009100308842d00c10740240000b40a4030150403119020031214000925004803e00918810b07600b400c0846140c0740c01d1800302401417606000c141e502c80d129144081c00948200003081c0101c408500c00c2e0344031340c98440014182d42c280c0004412116004000000c3c0d15070010903110089900c1c2042440c18046800d041d80e00185400304540c801d45040e4909040f07900340e4084200b024840068407281d40e26029400030102540310041e400d588104001032469070325034041c2804070b400618002c0d00d10040340109090720140c40003043d09954850a0107428a181c0540314010000e500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 178309910 1250 178308660 178308667
    0x120105060d0602071a041203060803130b070c0f060503040b0702070b1b01091506140603220f020a03120305060316150e1201151d0a180203060403080603010c05 70
    0x20560030707194058018416070300891010200003502002d840200116404d05800d4901030901940c1d6860f40740200c4082460004c2c080340c3d40d580401159013a00e01611039520749881c11400005a42c030074072003501c00350400c0300049440d030546a0a540103122545d2100e49034241818200e03410300c0098030050940d0b02031309040060510340070a030354070a0107a0b21620000c2c008104414050007200c01c000307113224940700489510501a41c0080269442ca0300c3c40e515103100c4005110310361205403440c040761038014070f1400450130a0030200310000d00c01c000c003814044096005c0346004c55150421604407200310030f00228035a240c810141c2c41301c000c81c014602c2600c0380400c0380e48072101e401904c2031102c13282e1815a5050080024080006c0040d00c00c0740580e4808586a000706902001901882ea40302d800142d881514a40c83c4071100028200e2a1243c8500c04c0d07070002440c0610f045c40040b00d101c1049400342e68140203051180e406512002b07400c1c5004410113007160301c090b80c103074244502030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 178311160 1250 178309910 178309921
    0xc0203011d0619060608060603060d06050106050a020f06060607140f0304061e0521060a0e0c0406090b43060b010909150b0d11040825381602120105 65
    0x6d0115407c00c1d01900e040d603a81c1c4030b0380049110498100400303403220b802c0c80000911030768000014580d42e4015070a0b12070068950100c01d80315035013503600c1580600f05000640100d4922890800b00b036440c4400c4500710b600214610342142c005e0b80c02840803a40c030340180030351451943c043c050311400610744140b4052140c07501690041038420190100c648110004080e80c460300c103c0006445040000302d050310301480700802c654030a0040100091140f000017607846d260b40e080d50350200c1031100d40e034903412540c07a00c1014089071049807a0616072007500080c000203010381039641c96014443c0483c5040c1c060002400080150b84110381c0c0078541001d07426403160f1615084d058070020840c40d955013801c0780a2802601082000c1c5032001e000240001e00c00c0340001d00042c1160f625186108042c181280954004803540700315150030081100500e54032404544640018081107041801120720503500342807a004100c80d40031141440c030a000c00c0d4030303044d6101906001218024072062614 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 178312410 1250 178311160 178311167
    0x705030903030a0c0e18090c0103020301031a04060b09010e0403110c18091e030403060f0507050304110a09060602030a08160e190302130603020907020a120c0203011d06190606 77
    0x2c04845095a40700503048501c5d119184460800b14000c1103102d61080800e102030918400340c1d40c1c01110301c202e0703043c030707010b54003c0c001c1d40c0c100c036002415820b03040e10140081c800c01d40d006008036440b135510a4100016910702c00001c0c060001d180c0f10800c14a4503190140140118041114550f07110b01c0b1a0030b643e41c1c0e00703540860222081503501100c3d440389082c2c1ca1918901c1941071080c0c9015800e519414000000a003007240c0c001c200c20311044a0030603c0714100e0b14150b07909000510104005404075195480340341034001c0260801c3c070783c16035a42000301180c0d0280c0013100181c000003060105207500c609450780114159034201840c010030003014102d2a241c8141c0e0b400749403180c000c1102c2a03181503a64004640140c648071801441200140050401d80400c0303106e01442e1000c034818520014420805036030103111a140704c1650201030300c111005090480c1c2c0740d0340f168603854503022544900070b80311400000034501810684442040d0784050b00030340303082d03520340001000395561 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 178313660 1250 178312410 178312417
    0xb18070e010206160f090f03050f060a050411061c09060b210a140a05030f0406030c110c090924091e100b0406050d03171501140336060705030903 64
    0x4d0340d09151040f0300f05420256001800d03a80424000011484c2c0042400b0f00803a104421030016000d5400581d9030369520340840d40c0c140d40c003074145511440700300d146003018002424000c20381b04502c8140768a0b0103c0900b541c1e4800720807100d1a443d072100c0341c09400d040f2040114284840102c0b034480c24811144e950310a0980b001130200040b01203000c422480c148401c824094205064942d030b84144410405207601510600002900d00300c4a105020302c200c4c0e0484400d0000b00241000101d080108020b10700064601091030050506108024410407880340fa5a49000000c1b043d500c0c0601c2c01c2401c00e48100c04042020301883e031050381004007c80c46080d02000003000203000d4024501240c000e2007a50070441d0010241d9503504241504001004000d660102e9007407403550756920140034140307604c07030105d0200b00e0340030f500c1681001c0000603607072203070004020319400741c0106004559500c2e590b4040042502004040300b2001060040325840217560400078903505150290716a24413 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 178314910 1250 178313660 178313701
    0x110a20010f080f150604060503070e010306120212100213050906040e070905040302030702060d02030609070306060507061a06070c06030509241003080406021006050f011704060b18070e010206 84
    0x14501c42c0051419513058003120383c8004050a401d0f112625007501414940c403d03640d02c1c01007161601c0307803007856102c0d014110564101c4251481d92080c140d090045034211220608c1480c0034182110b84101014805080603400c40e0410031081440e000511036401406826240690709040d100600054005001c4084900c01c0c03400040d01d40d43c1d414228114000d00310000d41c0b028002030603841d10542a0003460051200f11600142a100c4a00c1901218024030031040070a5040c440a4007145882c3c1c408071228003030010340d0345e22180a50014646e603012080444980f45510000c0c0302151389840399a17403010f03010000788941c00801c03840151759140744907034003850980035000441c81134030f80c0b00c031000860b80301c0c80c0b80340c03196215030000c0c0d22400c0700c401e0b500c2c04a1500000068034a4084100708250340d060719040c84200085541c1c0411020082065a1a45d1901035200d40d640b2030305105088904400681ca4503414210001812041501089411544040c0074030842a848a01040140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 178316160 1250 178314910 178314931
    0x10c180e0f09070b0d0605030c010f120b0a0521060a0203040503041401020102090904030201050702193c0f0215090a140409020d0b091c020d030c110a20010f08 70
    0x10740c1d6048400d07180c44566000200d04c028040b821022411540d08540107449080f01540d0170a81358a004603045203030b01c0700d202c0014110b51620304001c14280d100708500b02000d480c2005480d201c6c00411080009007014510503040002400d06112091005a8000700d00307080039451810305865403a030324002c60140140340c101240699030647c1c002d60448140f0f61001d0030b0f5100a1030030303080180c000c00c4121612400350103034904110303541200c40d12403803036141d00604040c00918119082c507821003043d101c4150001842c80f03090b04034030241e2016a4103900c1340c8070310b0401a0152060190012482500e92284a03040c014501c031035840d00185010350f8810b1a0010340c1c10349400010f0090a10b85001940148000c4001c0341400410811544034484007022600d11f045801c0e89068000004025400141c000011464419100b07030888100c190040c40c5c240201e03030034843d0f0a810310750301500407a46c0e004e501d41280c0002440c0806003101010900f403c106500e003102001e001000b0040c64420003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 178317410 1250 178316160 178316191
    0x1a101202150702040e010609180302031902070506040b0315060405090a09030302160501091103161401120f0504110603070504091508030304030c030306122f04020c010c180e 76
    0x1450118042d1915640c00070301c203000d080300420780203000300a0390140306856400c0c5192002070854102c2100f200c07a81c180c3c015440c1c00c0c200701070951604015007a038401c600422000103510360700c4c1c2e0041c0000d821001840c0342d8034100440c88078580c0c00d02918582c0a5042030000b0091aa0f915046a42c4000802c1000c1841981480d08500912901e031050480c07a419881c84070502c00c0c150b002c4045a4800c4000e90076003ca00310400d070b5034a0706103410420040703080a00f44100c5c10300781c080360303500b11040c1405040400c218201c00d040d94904250f030b501a5549a08010500062580e040c82c4000140e9491f4654105840002c05600c40c03805030150030380d200c0744402400310b00920100000c02544055940700c0c1054540100444002101540000c1c14140c020445110726408850740c958061804080507106250020340202882c0717040c0d95003031030751a0751103181c0ca403400200b20070480c1c10000258980b030f01c0b00141c03c0290140009101040144050200303160010500388c0012042484566 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 178318660 1250 178317410 178317439
    0x10e0708090703020a060302090415050604052704030c0201081003171b070b0a170105030303040b0a0e0d12140c0307030b060720090c070f0209090c09041a101202 71
    0xb5111160f40025000803011000040007a03042d400741019640c11203080c05070320b807001403105540042d0302613141d0100b0104000c000300e280c460402a60201840d1608a4054102c1c501c104078140464003070f40441c1c00144504110741c2e00a00d5260b1207400100c84540c5142162115109c45840160020b1440000600c0d5034106c01d0001007803540702d0104044585141d111001c504041d04001800808240142040a244031f4104402c41c10b0304c4000d40107608590f103503112180070346006815455215034580d050f0170501420300500007103143c2922107040040401c2110306c1203079554010f0080708a0504e0902c40e402080710100ca070494658900858000c0104000030345a10810000800d01c042c4900599000301c140080c0c80d56552013154075070200d0b0349070340361946c0510500722300a210f00c0f2220b200800500e040319038903410256090423103072042103a030003056281c8019075058805190321f015400003901e000c540706030701c507001440c2c0b500703128a4416003c0c09690b4402009106000d401d55900c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 178319910 1250 178318660 178318663
    0x40f0b06120109050714150d090311160303120b0312070c1d010503070b03131b09140405060612060703240b0c060a020f0405040203150402071202060708010e070809 72
    0x10088507541d8020454980c86103480c40e550300322403042c28840c44680483d01840d1801c040000d180155942c61945408420f80051b0006c201104084051050140700f203407103032204002c62034042140c542031007615415030401138000240c502492260340d0400000500d19240462180600e500c0c0c4511207444100030b2801800c0d0804580083c0c030305000d40102d110140d450026070b03d040700c405a0660b888280c072445040d0492000f12181811580c0c40c3c01c0103400518190f00d4061a0f442c081c0f048a9600e4079542203030309842901c040600846040c00c10302c000e1000c14032107150080d2007102d86003030283e079602c0183c0c2c0383e400c0241034109060783c509801c030101f25100340b0480260b00c601030b0a40032079103030100001c550700017440d800a244240c030001010752085100700c0344042c00881302c0b28101880c1008010207544000c0044007106903010070b4800640340c6001402456200310412140240c041d44001d00d41813008010302c0810140c14010403044d60001b50003900403441d480c003602c1c95a6082c804a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 178321160 1250 178319910 178319929
    0xe0409020303030f10060f0e0618040204060306090f050609010e0a0e010519051b16030201150b0304200d080903010e0d0f030e0a02130b01230301030614040f0b06 71
    0x1070740500000040180c881c029400703c40c4510642c80c1d00c503030070b1a1190011100840001e4491000c9003098483c10000e1404902030300f14128040d0f011040b07034050401207002d0f40c010345e005001003511064140b10704141405260b4480b44d00100c104424901203000070302d07040040c403455403038000000108681d0501e5800480c410307102c1303000034003560034000120600e40b451049418802454407010550511094480103070a18505c4251401c00417640e03221002054100422015590717140542c1c00220440c07481a402441140d2110ba1a850a8140452144034580074290600340c04001011256603d03070207046881d0b000305246481f00c4464000c00c2c0107209829a201040c454548298aa00e5104210000350301c01c40c1c1d018803007900c11000350341c0d8440551030020340c00420094004d1210200b0f83c03041a0007041403522041c9000040c8141010710244020400c04400000050080c04418012903c84200903041d80c1400e140030380702d25a20b51400d00c030080c40d2031000c10100d4010756400004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 178322410 1250 178321160 178321163
    0xf04021306080309090a050709150c0b0a0615050310030f020d210207050d0803040b10230a0f030b160201020c030a020c090c0301060f0f030908040806090622030e0409 73
    0x1007104070348503004140da9400401c107907441000c0f040001040c01c0e4440c0161402140652900030056040c0303880100141030f4451080108000e41d484035010480030000c0d607005080328140000c100c0d00701076076241046840603080052010400900c00d95550558890045a4001e00c00d4540804240700007030700212001030140402034540c074080410300001131207140035001602101c84041e661801c0c44203c8640c0318028043c10b43c148000381c04120700c001c03caa4000c0c482020a5855030304c03040c40c0340746065001c0400381441c180c0c0d1119003181c14541108405450301017010000249142d40701015400000c1c0f918080c42c4490740c04104c0c8074001d40648032000c0c0342c1c0b0141c82d2101180c510081d075610308116098451040d01c0c0106009800820480341655030b1030b541c10210711050181507408400b0f10280c5400c041d5a0302c03141c80802c102d840500060719045002d4000d50801c080080e01d07000015141050b80300003c0d8003c0c8200d0b0580d41c0d04070803d42e040c28601504200100060020480c0010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 178323660 1250 178322410 178322449
    0x6161403040506070306051c2307080703050106082a010c0b1e0a0207030203030610020a02090a020c0c04060f06030e01020d05130c080c0d020409301112030f0402 71
    0x140002c0090104803184504801d503001c0000c0340d42d0b10100008680141480310141606090a00208450000520400b03201036184540e1b03c10125a05250289a910246060300584020700030808280101d00003480f942004000300c004403d0010350f80840d115800d0310425045003d200d503a40200e01d10849030b60000050091072030000710f100da86c2e080c0d0304882407000100d0f00c002803420b0420f00c240c562454055004600b19a038140500c02d41c4c1308060401c1d825803040c40180001a03850122840c03140910100150f103907450310b40540d20302182100f14502c00c60820100744246909035600c90101c0e0000e24000c5030f034038030b440140740c0240308010348c1d56030f60f80c1400d00f04112002000300242d0b0841c8200808000035035690811522101c00b820045c0d40004030180e0b4101524041e006501150700032003040d6000c041c01c400240b81c510b60240507000046a0b0340c0c2084009412418a000031030041c009410b0855400300e4a603010b02c402030401c10f0400020020038259121401c00c0c6618140028 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 178324910 1250 178323660 178323667
    0xc060509010605011202040e06010e0a03080307020309090109090308061005040905100302330d0b040e060703050705070201120203090313090b0f0a030b07030e120406030501080c04090302061614 85
    0x8141c041d2519014050202c0e500d1405c5e18140b40062007140c00f00c40a0320010001034035100011200c0c02c0c2441d21040d4420484d0707c002c400318008100070343c0110300c0b0f0303002980c0d50302845080c040c1e00c204c164000c0160b145071903c0310303010070b400c022031952081040f96a21a40040d911065030140900d07000b8031021840c00c0100541110506150404d0f01d0080b01c6441d243c15404403008003401c62034020581080380c0360316030703044010908043e0010500340c030f00204114402d0350105045504042501c42e01d94014014054159058441c0c250015114644075103089000e40028101e03140030344920b485141d0010024190314000c2c010f0b199050041d981080105a5030022840505080b485c1c091044907160341401841c03400d146400c08880c0d0000e25940d00b96907a4000342c1c01400300c00703a070242ea40908010384641da64094010405000b1a03240066154140250340d07141003c08104180210701d444524004030350000358081e440f1514a503141c1e24007441e00d07002c503240890f011101c0014807021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 178326160 1250 178324910 178324921
    0x6061201021b03040509091c0c0c03170904050601080915060d0c0b07050f0d0f0507020301060302040510080714010e150c0703031d010306030c060e06040509100305160f14010c0605 79
    0x20004008988040740d0138009038032100b50248d124640011903416139003900c0100d0344514000c10106a0f0b29010701660100c0d2036032030302c90b6254885104500039030194001040300003417815214040d00030400f032070500403d1401c1007866544000e0321200700f68016051002034010703a5040d00100c10250720099481c0c1c0340ba03490048052942084800b155540110381050301c40204c0010044401103403a80d03400340c01703142040c080da8150700254040e42c16540f03803132010025882d180101402118a01c40a0048924020990341860641e4121402c140543c401c0d0031a147c7c0e010300c0d5040031880c12076403001d0460208442030311902c04d05148101d20700170390f8000024190001e000700d468801c421025160001d0040045003210110b00000302030b007076440010300180b403003240080403003180544000d190a40702c9000803401d6400722011140e00c21480303411b100f001014013080701c0040f400503031902d007141440a00c90115180d40201506001d1600360b00e01168880c130840c0800d290070070320401481c2040d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 178327410 1250 178326160 178326163
    0x140d05010c021c03090c06030e010f110a120b1f0512070302070227010b0306120a050a030905150304030e06090409110f0102160527070e04180506061201021b 69
    0x102424080d118180f100309001c03180c001d006603610030364400440c090790313824000b040d80200110007090f40e540d942d45032525481042d0b803007480c001300040c074485500e400d000400200700c280000750b40455541054482d4a480d1980810b54076015070000255000c1c180048084440c0c1c00f4402140710a1031290060150068165000304612030081da9611340b00c0c070602c0402c072043c42d140c844541c07070414080c00402c24421b0f890f0155800200052003810a09100d517240c40c0f40c807000e1802a22a9000340509404140d000f0044a004210507620750003c02241c200c1072035240002000902171088858180041d640c8410071103960000042c81040011003900344a050403601c48030150103421038040c10b0156600004801d84810200080c44030000d00381814004039441040b801d0000e101004085080c145a84040c288502059903940400105035010013090f20704180400c80c4003544110f541012036008540d01f503004805507941490846000c240e140288581044c0101c100208c62110864071030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 178328660 1250 178327410 178327423
    0xf09011b200a05030615030111040f0e01170304030b09100207060c0e2211041d0a180305030c031504020307020f100501120f03020f060a020301060f1404140d05010c02 73
    0x1112161075190354006018001640514060241e040d40070500085c007070164288502ca0501000e0000726031600340003d2185141c1094004107901c7c480c942d000e20000000110441c01011242c480d4680ba0000503c0c00d62039100d00d00000c0c101e0382a0030f00040c1c40170820007103200e4a04951804564403046410458000c0c45800300300700001e460202130004c1ca2900c00503c04540b4a040c2502d20100c4050151800a06c0703002c1e480482010203110009404640445202d0003060a031000049403820010788030840d032605512443c0041a9400180420ba100c01581d500c4070301c100359241d484c7c644c8070854034901140b802c4c060f4006d0001080200c510b03030202d100340c07444151808903124680e0301950312080d140f0034000e031002c840904001c04042441041d070300190710b01074010354601440380400142011f100300e0f109040b640d0000010044240c0c0000c921140010a1614807182110341c122296280701e0b510130074007a204411541201e50b958046002d0079164410b00030400c2e08482c4002035241c5c403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 178329910 1250 178328660 178328693
    0xe250510091a04061d0f0402070204090609030c020a0b130e0601120c020705100801080309060f070506090a140d0210020309160801090b01081504020103150e070c0c0603060501050f09011b 82
    0x170080d100403041000c8108114008280090407008004020070910000b034019440907a4015101c4105d000418064810000420300941e214440000640148031703207180641e00c00110b8000800c02610500800900e850550301c004401800a0700c5002c0100e0b12403c3c44003e107a80c8900c1c103c04d401e401500000c680301151000d445009211000a0b42a07070a400700f4415884150002c0000d40340c00d140400c02454501c41d9194143c0c1805e4050720354601c2c0c0788044134950401e511650031030042c042017075008101d06400d1360041c0a20800140000d40741c061717070801d40900070380220100782410018000d010285052100d90000c0603660b59a06001e00310a45040c0e96844040c00042160400860812201110307151080c01e5034a884d40114001c0c4148000030908a0b45410040741045045200b18000e00c125918984201500e0030800042e40440d444582814504041080140d800c20140c8103c1c1d020040c1c41a100c810440051345c60030315108032a00d581c5058140c6e00200001000c007110f400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 178331160 1250 178329910 178329917
    0x1b0a122d060501140910051b0f07050919201305090a09020a030b1003080703020f16051809010e03120712050708060409061e0e250510091a0406 63
    0x35034400044d41c0c1003001c160220b00c5107008110500d540e04141604031084080307446c0291802150060b0749140141c6440c031001190030400414025003000c0120101421040b250220a03041c90b141641c84029210300d2408410744803144040004c3b070800301c0a06000c3c1a02c94142d0b9004104904000122507018080c0700b8101d08000c20390107807882c46000a10759000c0c05554516055171582c204428000b0411014030343e07581004070029421201411815100360028922844d00700d032068108440c0800c1c1c0d9125046508041219942c0c048a40700030380b506111806650f11402c3ca0280034000307000b5104500e02c0000703552030710500100d031000d1140e042d5588485c401e40c94914158141c0d001561030200081820340400c0c5030340740c47d034007405030a84034500000f00c0301c0c10380c607551207540203100822035020f950b200010130942003441080c403074210041480c5403000c10610f41e0200010300e40a011300409458001525042c062208500039020f00891400f5840e503480c2e2140041e80540600e1001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 178332410 1250 178331160 178331171
    0xb09090a270506090604230f1b210705040902030f012409020c030a0509120703080d1107080d1e05040f030f050a12020a0302040e010308030105091b0a122d 68
    0x44c8000800d40500555001c0c880207000c020625030382e00714103545000294a80140c030710f1248068010440c04040c0003007010398440383c403c04400c000c036102d40480007403030080500c1d1108004450201d60602a100101c17800520a400750011034908141c210805900390302c0e101c49850100300703040407000c554507480941c41c1c0c9151103210302c00c143d003e1030070070400590050010303410309805076024221614002c1c00e60756000b0b050700c2146242c40c7c40c9900544030680c000230b0b5103200c2401401405800b4108120aa180c0006a03a800c0c0d90352043d0705503921040d5485a141e4050400c061281c01b01881e0b1a0301403202d400c2034142940c0c0500401421008690000f2502c3e0550f802041034a05405164450318030400626680c01c0c0030b580004a02c1d0b08040d0b08102c00710384101c001354414040d60240099a41b00d40c1428140620540701503d9050f0042c606a128200842c0003021690f20642c01d1600191100c07a404503200584806003940c03500ca5400c1c2d100004c11043c0080c80c4140c2580c0c940180724 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 178333660 1250 178332410 178332421
    0xf09060c02030c07260105071e0e0a03080a0c020306010905010501030b1c0308060127090b0303070b01030602070c12060c0f080105030a031805150d0b06040b09090a270506 75
    0x2664030802002421640052004026101d0045c410804982d01680b909200303140d80d00c145821144110380c04004112851100c0240040380785005064134101d06029000041758400506a9541c903c80100700d0040010f0030b886d404e01c00c8201802a0344d0180880b005543c4680741d4a020341001d000340c80c0043e24100203200c142c9022004507524100e0402c4403003071120180c40c220b41c1c0700d0004002ea4184510031201c04010b501064413506011507140c10300b1f6249007400c1c602070596154103103d80c171a5005000840c007040300b00d54403a044a6020070016a5205070b864040400c0000b94491184551f441c1964414001c0c6a04020301d400d84a81d00c0c410504119030081c0c41d003031028021103415900c084442d0f00040e0007031011101014a2851400c98550b441c40082ca202d16550b80c02018030501240d01200505a03009115840d102240e88608060528a42c84042d015441a0510070310107000410340020045e0301c41441085424030340d4001d01200101c0401d021040d22045074288940000070341c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 178334910 1250 178333660 178333663
    0x110a030c050306090a090f140703021807050f07060608121c050103030e0f010309140a150608030a030c0c0c0303030e0d020601050d0f0215030f0a0b030604020d06020315040f09060c02 80
    0xf0320503074008040e0645034542034404002010320103000c541022040c54840c01248403032030840e074000c52210040040c5404d501c18016440e9201480302d00c400c03858828803144031b4011003035481da03a1507070250b20f88900301c900b03100000c0c2c0034552249400e40524112160110340c0390b0014a0342ea14401030740da8009040c01c0405d03044600904c8090005461070000f000507260405500c2803280d0145000f068528942c0c0b03d001d24000c012818184660112614030f041200700030f0007003c220000c00e000c02201d031a04143c01d4403449100c0f080010565940c6407c0c03007550161408096942d08030240c40c2c1501d031a45000b5000f09541842c1c000c080c82014881100705200049150580d0030141182c180c1d100d00b0347e45d0303080000c0d0039141282e00c041564401a110001c0c1c0000c0c1d4803410ba00c6543c01c14034288642c1010440c0c0200201074003c2d00b001c801c0001585031210f0320303803440d5440580160b80350340b0786502e4401c01c4138050b4a00e0b401307401c101802d911010f864201150340c900480d400c010300c0741c9419059 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 178336160 1250 178334910 178334917
    0x5070f0509090406020a090308300708160903060c02010f18030212070212060403020606090a142404060914010915031101030f022205030c060d020d020904110a030c05 73
    0xc40c0d000102c10700007400100e00d60042c1040301001c2c10000403003926aa501c0700150815240a11100c0d0301107500ca0314004a400c40c158100c80e080303100d5100d8103000ea002055410010301e0508000058200b44403140d2250b0748010007150000001c0180d2001d88400a028003600c04a01c07000030308010040d25104800070540765103d03850f03001040e000c0030441c4100030319013102c2016a0301c80244002062411802c3c09802d11441c8294040c00180c0307029810880403c401501c00c0a14918000e0448486454040701d140c110b10b94507510400c241c080018441141c4940745001d0304182810000100300c5102c0c4c01145001c5d00244400e0150781c0c07144500d20481c0c6000b01400b5040c800d00d5001c201140f02c9021070400307144180340100307481c1004031916007660701440c030103542d90106c209006400305900d10b400307014003002c9018008070540500001e901d4007880c0d4904440c5580051810b1003100d5523411100b04420291050007000455600741250750820f440031000f090400f1a040103003441603049 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 178337410 1250 178336160 178336177
    0xa140307090203240402040305060f01060810030809040b030f16091409120705030c0115091406060d0b030109120207030b0124030c0c0f0b071101020f090d080409020c0105070f05 78
    0x5650a01c0000e0702c0c94040b42e0900381350150410750030400800420700900025114440c5114940120352504900404101d00144081c0c840d0301201c8042c0001009001210851402124081251011b80303000074240070b080d0100024511134040d203001000151131a01080300c004d81d00030000c0307032001c204c0d5030b60200c01100e030040c40381c0107106035840917045d4201038034a860045046a0610542120b10741c00c54040d05411400c0e1403039080b08002044450061400555003038402c00716a04008011440364015805102800c58845141a00c940c9003503001101046e04484484804035040708080d45070b4142d400b040e1405c812410000c40d200c0e50004591488800101c005044c4100e0480c08400030161618000b041090b8000e5400c0851004a14030031030354010381c1c2043c500c0c10054006807002d034513a82c1c00740e07059006000c04031844460009490004a0035a80d041c407800c0b1a14098420b8444d5412035240c140c804503c810104105500c100c0c0300301010b0300c8101084141007c00e45a600400f101c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 178338660 1250 178337410 178337431
    0xd09030c0605070507030803011e05030c10030f0e0303011d01120c1211210c03070302090f0a230403020c220c211e02040f030b04030e0a140307090203 66
    0x1001224400c200074010a40940309445c482d03526a5501c005680c400c2e88a800c0002c12010801c40c85524070f0301c0d12005000c102c0c0208a10f280440100d58030a0302200c10405160740c440e03581c0d003042140d4100c40d0503002480262035403503855112031080082e01802444031921444004204840c4104000c0740f8507407c2428051070600d4984010380d2641c1600003203c0c10481e05166903e01c1d1240b841448200c15003c110125600b15804a5450242905880c0b8800d07030203400200056100c503400c1d6900100d8405a40040c1d0369140c0009000e050603030040141d04022101c041a940911440540140e2096007a1040d00b40340701c040002d146a144400c4118484e40200907501c40c44541c0003a507041c215003484818645405580107800040d144429280f84e102d048508124040c40c454001214000008505190520a1150058089010042130340c003c10000c80c00b450300030440300200f084020035880405427100e0745001481640600ba42c041d12811602088107030041c000da0b0721840340f182 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 178339910 1250 178338660 178338683
    0x209060d02070f0c030312050a021905300f090a3807090e0a0509070512070b0d02040623090d02180103080a121509020304080c0a03080601020d0903 65
    0xa0034030000d510518003241d00154200725800010054a0360000960190b20f41c00d41507642c07043d114050b107200912070f221961040210311448616001030919090485c600140c4440c032a03000c03410026002c0415510340070000d000300400c2001200014450f180100b01085180c4418545e1581c4250580c4010801d00c88580d090100507490903d0f0380e000508034412901d1380300c0d161b440300d6041c8030a650b0100010498030301032084100c201085600a00c0fa24820001442c02c0c8203e0381d00d817034480c0070b07440c8201030035140c00d82100820070401d400b400302c20818a81d40d0442d06080720080d0300c5845540301003800c0248c0305860304449000c9080071140c4403981440d001e00d0b8810003041d0080d081c801c0340c3c810241c0340200b0030400c141c5500d80c007841c401e05070035913956403c68010f021071101400c80700c121800e20803154141164206800e0880f4100c41002d40c5940b281c3c035040e9000d0040810810842c8070b6106890245940880482d0064030281c00342c0f4003648540d1800c9640c42c1207800050f02e4491000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 178341160 1250 178339910 178339927
    0x306010801090b1818010b0d080a0309031404060e0103060b031e06011209080a03060b13030b060411072d0b0c0309030705030403030f021002071a0606090d0605010e0a020906 76
    0x150070058001e0700c000c110b04032414130040d103814103160a4070901c3c1c05949880036602a10424841e01501c946c00322445030032045160380d40324040c400d01150701c0070540c032904810100750140040303401550104d4641c5840360b49401c0c0c004e2030b450000c500703140080e042c088001040360400e82100e0094524448042c0d5051440b46203118a09000d404a41000002a0707406006203440c4a89070b8090b22503101030742c2d2000d03003600050035980306800081075940104048420b803624501d000084035400414000d45a55210000d40100103503401d0b000c1a2030300040b190200401d10308611003000140f04040100000000c66950303100c80075400801d0284040e011900d00c04070b400c0699070000b000400c8038038207011603031821706540181d031044010654a1704421307105038051000a800000000045060540c0d0f41c8038203c02840031803400009001900100d002c0d61981c40445507200c074060140a0116614680000100824030528406032680341c041001c0820394000c9aa000c11f00800d02d90034082c03c1e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 178342410 1250 178341160 178341179
    0x15060315010e0d0b010f09050601050d0903140a12050a05090a0b04051e03121303080414070306020a020f0c03030f09090a0f110903010b010c050721050106091b050306010801 76
    0x40c0c1841040b012541da00d81d151400038007507503c0344095400c1d5514009400417501d6141c0c1210f02240d0901c0b00b00b1800340d03480170644000b0f0301508400308400345181419030b40200701e01c0d0804406040055201515908141e045508111038407041200390348906107042101e00c2540c038a403580d004120f07944007190a8030045d0390040c2c050825a8003641210a01402e015000d05c07d0401980000ca46201801c0000812940c001c0c0ea01c1801130309216a50b40003804d403400208014a00c0114000f032074860f000070080c41c0c015680c00003045582c0c046c8040043d41d945003145074101c2522500400742c0007400c02005603483d00d080503290906007000c5000700000c07450018100385c2c8840d601d2100003085a1540680c0b0603143c071940006a0ba000c441c41818252048101118180315440007284001080050007004459410100041c000e1242c440f21060540c81c0301d0103009036007032100c04514052240d100c444d50085004000003d020035071010b46440c00122401408240c3c850010400103a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 178343660 1250 178342410 178342441
    0xf0105040e030408060435030a11070b040615080c060f0a050d0207060b0109061e050c010e01060806150a030305180a030b090c01110102040b1804150b070506150603 72
    0x801c10741c1e0809488100081c50084116415903281d00000e142c001080d440a000c031940c40c4003428031b6403840c681610074842c41d1001074000c9a296517200c2c0b81103101d01d0800d06480485030710007800c12150070320341030001c0603107025400600c1403465210001615030002038600c00e0342c08083c10480c2071505000004070070707401c80d0050100740441040528518079080c401060303000c1c81900d0000c4d0b81103110300010a04110350b0046800d02141c0d007594002110440800d580240d4203140442da40c644100d620790152116100d420b810390b007080c80204488ca008155244900d801c8481041306640300800c02042c5e03941440068003250b0100400c03210300200700c0d03816a0081000d4229210642d59569401840e81c0403202240c06400030010b0040759a88044600d100341c3c0ca01000303609107400c166000300140b04da901590703e05c0743c0803200d100998549410500320714007205441c1498940c0c0700504034059000607811540b03130017001c000a00c0c3c2d02900d4000740603100060201ea041d0360350f080102141c0003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 178344910 1250 178343660 178343681
    0x503101a0303030106020a030f0e1309170d05160c0201091403190b07030509010c0203090d060b0a060206090d1706100216090b030106081216080d06030b0f09060f010504 74
    0x102090054a03094404000850003403403a54000c00d13000c43d00342401401189010694010030112500302c11482c0d8079140c2c00700c80e0200c5507c002402944525000c05c2d152100c18a032036411402180740000300b001e40d80003502c0341c91000c05140c204e501d04a401c503088004184001e0214056060a10141d2001d00301421041000303022965111041c4400895544034000300700c4a5500110030000302581c54024290041c0e4418000d0000d0001c00c40302940728094117404034064521501c040c0309100342074000c0404030801500300350304151a0030f0004d455203021a0141c0d9a8496000c2c43c8030320718480c151008954a2500c0d0701552502c801c2c041189140305403140d901148125070280d455880c0b40b5801100400e903c20000460a81040070305094a5113544200c64039000464062146108503084886407030091070110703503448142c0340c4510309000e40700701400781e00e140400200401602d01d480030300924404402e1126aa6607103030f61a90754500310345201003c0182c4004000e2410650407401c2c004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 178346160 1250 178344910 178344941
    0x109141911070605090d0903020901090218040c0824060313080d06080d0906140a0e01051303050619020304020307170703051504031404080a111323090304050310 71
    0x440016900c1990380e0882c01e803e8400303940d51400d0211406041000c070303c42ca1918107003410841d213543c0016441a00500ca5110741a800040c001e000c0390300b44501c001e228000900c01c1140c18070390440100801d004861804e00021a81104103d243e02880030541e1120010400e0f80780d07596407284031a50750040f441c11100c0620500c0801101340c5d43e40100c2c00600301d0a070061040004a41008012007850380c00442031110030265108c28030450400c5030240130640c00c0c85444030403403a00482c1c0c544603220049003c1151410048108031010805c68021110321004032465041460000101d00c0142e400035411303441150100594481044000381f0006a80240c445a590f207441e8642010385501310300702d400c10030b50108820950024808800700c00c0d8125454101420040d000d943c9142413200901821442ea111883d55611a4165208146040d40501c28075081098100d4180e4000b8018040d58464070000343c54450b0001c151070858400030020821481ea488015005100d00858520380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 178347410 1250 178346160 178346171
    0xc120602071410050c07081206010207030b010e06042d0504260304050f07060f140f04060e12010e0304050402030408070b0c13050a06051b0115080706030501091419 72
    0x1041c0304441028600c44a8006481c0c00e82910000c1c000712400202170118101e42402890302048110059035800c10080c101c0200c01d1710b9070ba0050340380400c036600c0100584400000403039014580c3c40454060041a1001d01c0302410740311000a103050301c1c8d0b800c2d003452041100c002140d09404c1d0800c40c5c100303000709040d00240070002640d035225216a80d0324449030000205010803c0010801030b00e07500521400340c062581022002042c0321110060f0f80708000702004402d02c1500750b10100d030401c4444015855440350394002c080c0840704401009171103881090a080311003101030243d0aa8070200001a52500303092908100003500068410b0f60004414800c3c03000040c08022241d000b120510902a10340c14000c4e14501c0d40481500b04500404042104001280c0c005083d583c0c5101d1403c1c0030b20218444200060051644006102c2031745009280001d142c800400c1d600e00351502a501401140c3c1c07103003500c005a5804030034802c0c016010340d001403075040041c40b03138000c408501c072000300300c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 178348660 1250 178347410 178347413
    0x50a0e100f2f0312010905010f03081c02030412020c1219030e0d05010b1203090f010509011e090906060e0303070809010504080a0c0f290901030e060906180a0c12060207 74
    0x107040400350b03502100c0d40d01c001190310043c0040b40a4600401040390244901e604000d141460025944002402180081408610440000c200460076116110215100d1500e0b0a0181400310032010f690054010702c043c2c1c02c164101b40c1c603400350900c5010b0080c020250344064007200041048016410440d1007041180c440d46c501044a4615000c0c0001003442d6000c0c20800206503450400314a0650007000743c44c2c8c0a40701c41c02881e0103800242000c5458960300c8005a90501e843ca121040301c0d55180c1c140d2422a80282000c2d043c1d40241008004664481c202505d040340e204503450351607881840310340002090b600c0200b100d4101898054101130399221810b10386500300c01c040321010040a42070281c00e10350036a050040c040c3e04902480310b00c0a6020b0300c9400d69044c0400184480004e000103035074080e4000320030401c0d041044a50516182ca1020780300c0100340e81c020403100703100c108611034083c00110f0a1260f900121028003103803414a008004000700d01c3c080b00c00341d40905c801c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 178349910 1250 178348660 178348727
    0x12060106141b010c201b0d1406191505151308061b03070e150415020c030d0903080d0203090114040501020a080105010f05090d080408010c050a0e100f 66
    0x1c0c1120b89440080340602c00200003400d40b60041c42200418000c1002c005000710380081c0001d154a084000e1200d15000304d40417404000d9081c8010700b14204a0503000700c54600040d4091080885d1070284d10791200400c2d4a40640310301011488144001000030301031440c0c200440d00c4101c001e0301920789001d01d40001c07039511850a03401201290440b6003000850180b131102da41c1c20546082d103441c42c515042e14060008480412081d005c0c660a202c13001150030501e0888000d07004031130780000c14400107480250b48002c0d003d0294080c2c040e041d480f1180d64010200002984d038400e05240c02c2c802e15020540084d00000e000314850742d02c0e0103030f41c44d10302c00340910b65000d1401003001580e58014541c0207002d5a00c1a80058104485c2c44043d45e10740d50b102c0c0680711020350484030601118140c1c108261035014540010a007940ba0440281400d50000020030035400326807201c0804003100d10401c610700b0303c48000034001c54000d0a611201d03a229800d01c1600c0c03400540840042c51001e40c501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 178351160 1250 178349910 178349947
    0xf0b031305070f0f080d08010603020304050109020a0b091305040f030c0807020904030e09090607080106030902040b1c0b0c0702060307030b190806150301050103020a1505120f010f051206010614 85
    0x200c443d51003541c0203216903e0103510007806403009000900000c014110004e04401051054604042d404004502004000c0d00300a0303440340c00503d6403160645422400354254000b0701c80a2003582c0320b83c40310000050b5070060a00c02c03134100c40c5240109443d030300c06941c4140c0e0044225000a0b0401495005aa0f6040940d0140f8020764403c1e42d05005002404046807015002030071a0740072a0400c0b400c20f034403200083c10765445240c003007098400c0e1320215014212010b061540244210600c0d400115101041075186000303002100d69601e4140b5036916503c00c405010b034000900f040002c0e40c0da4042d030450300c01c1c501c0141c58080d244044801d610728850654100b200f06030000310071f00110180c03c8440030110242103000300001d51555001031000340451080040017120003c0310100c45020700203031120b50111000035982c1d071a00320030001170540b090088020a15a074000865181044802c600500c50320000030000c0ba400d040b1309440350003003405030039501e14003000003000d420342d00e5842c1d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 178352410 1250 178351160 178351169
    0x3060d0206070515240d1704171c050403050a0f0804150f020c0307051f171602060c070f0f05030408010207060b090f06060a0503150a0617010b03010f0b03130507 71
    0xca40d01d0742854484042c1241c2e070310030b4181801d51407041c101146c0d030782c080408440c42d602c60312030607a03000c0b00724007904940502c0e4000b00800228840c15120183c01080f1410000e1415035075030403a6804910940382d41c0200c2c00058290b62021b00304000040621050710405409400d00038200ba5542c81c0c6d186103800700043c5030300002c0c0303007207030741203401d90104030b8500e07081e404601a102e00e90401e0007294640340640c01031714840000f4212246058081d942004620583c0e01c2000f01d940362602d6000c000240c82210700e40188128000606028411420f80c6d142070b9000c5824114410707151140c81c0c0c0110b252000760b455001c2000001500c01003480100380161040e280400c604504904120300484024171200190f11060200701150b9107400c00c49140c1d5540f4108940c0300d803107680d06602c0001160740e60b03035004488004046401a0071440860a8017240d0010306007682e01d49078044810701003071040800001881000707024a281e80e8011310390000c403501c840840c1c2d10072611406d01e055402d920 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 178353660 1250 178352410 178352443
    0xe0312040219061206090203091f15030309080610121b050a060309050f010506010206040f030309050304030b042109170102070818130209030604061802120106050f1503060d02060705 80
    0x8441d40d0700c400c42c01003e009150080c4110702350b281c40e40c1d00c1e44d00c1c1c840c40c16494800002001140c1401d8006034001c510045040d10201400d684230324000d4080c0300d40380182c0040d40b0407940000e2210310720b041c080f803e550194090700c4804c000e507500c587e030340040400b00700290446140003240300d44603000c0c0000100196038011a800300d80741002828164070142550059040400700041640c00140c096006039200000002080f91810103d0050200e0f40300184280000900007090000107a003881c01a07010313a00400d10b0350002d010751540202c204124070080349600808012000c0e8030010728841080c001c00252401c801940c4021584d840f20b600504540304807144e400c02420904200010f42c1141c070f0303045140840600c0000e68480c00140300800050b1108803520808600c562a070503e542d0150103a108103800116103406083c0c540182130145410040001141c07a02016254056103d074400710b256442d1041486100c42d4206410798202c0c03420032410b400100200444c1c103503083d1086 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 178354910 1250 178353660 178353677
    0x60f0e090f1b1507020a030212030c010f051008060403080a02030a060f080102070b0f04030e0f01050c0d02070312090b1c060308180907090302130c030f0c0206040203060a0e031204021906 82
    0xc041050301c0101d2084100800804c0c09000016190042c5140c01d8030f804540428812144900952070340c49040d68a00a55003480c10300b01c0c101c0446e4100d580203904c1c1c202d0f010001034544070026239802007160003a00040f58000851881e500940c000c0d90450070a1101042958031b4002e041e041030091b42c8130000c581c3d8002519400c2c0801007c0307181d000741c1510080b01e994203203900c0060070014080e40b121b205070b1903021034580d50b070700980468401841200540749045074a400c040e40301d84951100366070500702d1904004000d88214020300c140c400c0844060704041c212a14001a440007680c4600619a652404004540150003416070b602404041c0c0d42125851410f00c818008043d0000045c07007500f4400740016600c001c8a1188804ac00c40005900200c642c01107001e041032027001031a0914081e06406140e071b01180c1c20388150f0090741100e205480b190b8440007104c4200011030183c4e001404500515940030303c00c0c1d60000c2c00100304d4407079015103c80607016810582d0041002c9240603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 178356160 1250 178354910 178354963
    0xb0409050f09100b060405040606030e060a062d0308031303090918031d06031306060b0c03250203102901020d18120602040503060a060f0e090f 63
    0x502800740d00c00d01c498400341550410030700c00d0380d0703070700c800c0f0b000c1d040040e00d0760b8920085840794000e03a0002c0400820a100d070980c0c50714080d00070710141580040b54040d450009919803018013405d402c6604c6e00000800700061515100022002250822089200d04070008041480c0a015500032418000c0c50300b070f045d095140142030401c0c20350040680906143e107012188581c500044a040c1d01420825084a043c86aa51020040c16a0307164426804400c4c42540313140c2c0314640c0030280c0715038020002c00d034460740030b002c0d81c1c0618410389406a000300101380c0300c0e41e41110b0000b800d08910340d4081445565a0001c0c3c240040705550040319561490b1010040d0b00e142c217008081c1c0d074603044c8003403410740020000751242220b0010600303103c0212108451602c228800500910007549480300744c0c18070345010000380d8401e110f840d110b031203038201048403404984111411500101a0303d6801031824480036071805000f08020003901440c0c0141c00c0f64403040c025402c6090b03003568850303500e1680 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 178357410 1250 178356160 178356179
    0xa05060a0806010602030712031b031b0e06040b0901110105250e010f08090c1807020c1e0906010e0303280c03140c03250c050f03030d0b0103020c01060b04 68
    0x2240e10041c010350000c0d004110040e0040100c07611184c0010300c0d040158403105069000c4c1c0282a109400d80c50440e1807400750550690252040e00c255a4540309410012801240c1c0c48107515030140c0c3c045001c0104002500c0300314002d2059100c1070500c010045280143c0500311031044444c0300e20904103003140c1800800010184c0b20341c19a50600c1d1120404d2540003c00100c11860564140400c0d180441c1400204120408120f50000c0280000003402800041251802e951101c0980f25404070012145400e003400d14442d80c601104030302d02c08904080011100c000b0308080d040c482074000c2c03880c507500c00744000c280d20060756a0428200c11807088590205806510728001c10250002450001c0d07480b2464910789818459215100c0014405460a5120f081d48140f035050a1b40103540071000b00401e03080c00940181c042c0305c4450794460074440c00803982c24038503516400400c5400848046680320383d0f440d540616005040412070058203007140c055400c0380d80d01c0c1b000818100280d040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 178358660 1250 178357410 178357429
    0x1050a05010914040e0f030a0c05150103121b060204081f02090f09040507080715030606090b03060910050a08100f0603020d0b0a0915050405010e0f0d05130306050a0506 74
    0x30286032001c0da007482d0140d031400c0e00c03222040b20344c030864603486003442c405000c1080d9412000070406895450700d1806026055a0018800300ca4038010012488a0202000042d13030499400120703e00c400c4002410880700303880381c448001340c0c14501030455004161203101a1000c1c3ca592001080d40120008101d1014800720040d5800180104030780c40c060744500c0c0254a0001064410028a403510f2030001d0800c81c845c0c1020180c1e00c5901e00c001000031000d10340100103009501d0402003a0b4030b501f02210301d0788c100c0c02445d50701d0a04001007210380c02d00020440e80f1041070b0b40d680c6149611078000038402841c5922002840d0b01202c603404170380005100b400207100400e030707080140c607103503901080d00a8413a034005040c01c501000082e034440040d0b008151595444058196010042e0390b462000b480705450a498641c6007811038240c2d024002089a10109402c005010421380d1500482e02907015122549506190003000400141503005460050f80c1041001ca410703d0300005000c0c00d5070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 178359910 1250 178358660 178358669
    0x1020f04060e090a0606120e15090102040f080a02010518010e0a0603150902070b01050f060c0d02070626010b03180102040902040611121603050903061512031201170f060c0301050a 79
    0xc3c601030f010441b254201c4000c64240d0100700c0c0c041201085511102e04102c6041202600f40c5c805e54100801a80f040d80240b040e42c41c40d540e00307041640c0341d149407950f0f0080c2c03860003404034400b0041820480c111300c449000b828014034065035540700310f0300445c04100d5a0340c04080030a071a4080030003078140150b480d50240046640850420406440d8000d07410350600c1020b001d020507165981440d01c03048101c420f2601e05034215500300450710700007541c4102501c148000940500b40407280c0240e00b0b090b0845000460340c48000990030084480500e50000c1c0c000d0700c0d151517841401032800428009040100500140107072030b5850444058042d43e02c28440d42402e030040ca00708051441c1c1c00302030320540c040d07000d00c140c0f041125107801e544d10300c00e101500740d0511600c0700300b100003822144c0500303c0c08000d90341c1d2542c0141c00009640e503401020304605040829800500051007580321700e00d00d0010b410f0841d006401c031b04030748030f050030307001d07135440c0c80d54400000103201d1414003411450051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 178361160 1250 178359910 178359931
    0x8101203110c0d0c15091e06020c0d0f0b091608030d1505010f03090c0b07060221160804170a3f051b0a050d0605030a050c01080901020f04060e09 64
    0x740f52a64a1a400300b01c54002c6981d04100b88000e0904144602d60354406411100a83c0719003008045140040844034860340740141f28603a21078060323040440c01ea00000e0341c09000e440010006a0314041418801810703205a441000910200881d048001c030000300044c01c09150781d41718500960064940300300030810b450380a907a040280c0d9910070708034182d682035450b000812100e10700d080300d134103080d40c0d0001c200c2d000080341e00b400344002580140704400b0200c001d04941c035400e102040c1c100c1c00c11601d0f01d641c1c8030018034080040b4000d03140740780e00070300c0b540c044000a107415440d24003980100640170001040c60048c040070300d003200100c2ca43d1000c0c240c0c0355000e4488002e542c4030340d00703042c0341a020001e44400100750702d0401152801800554036000e55200c403030182c4000e05c950081e407260300d0414200f0000081605010500041d41070f00440035040003d180300c01507076501e4015006014640d0308128210710703040020f01400c05400941ea5408010b0709000030020503600150640700c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 178362410 1250 178361160 178361179
    0x2010605060c0601060809031c270809040c031404060b010206070503010e1302030a021216050d0b0c030403121401180c0f0e030f010f050603060f041208101203110c 72
    0x4000090840c11175110b85480311581d030307501180c54150b000340c10600d00743c00841411b251000a103500003110310004422103072030324503070103181100034501c03180d01901400082002072600d0900da005030307042c112182000304104011404040c4070b00f104407401d90340c071590b0f91400200d969042c400160014000c0c0b40160171541440461440c0007009054400040524904a0210b440034480c01000307075001081a0785400135070040680340c52010044a0880c01c0d1224003007054034201d24507101d0690001000803007039685600b03201140c2d0001d0000d034284240903804180c41005405003a04104022007080c0d032135490000340300c01e110740440f0b0a00741981440e42c101d00c00fa80c03203400340200c81624a4510390310f4030300c0f80c040b03800c2601040d421080e550030304113402c902c2c14244c0c2102d80038240039800c448503680c8144004c8c090949c190b40041264604cad60104207076070700c42c00c1601d0700b08150340b0305c41000c260360b5540090282d1144104038003103003504044801010b020312400e0f401207003d5401201 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 178363660 1250 178362410 178362427
    0x301110c0309190e0f010602010f0905120304020a0b0d020a031506081302010909060801020301080d020a0302030a031e0504030c02040c031a0d050304050d0f150209150304050c03031305010201060506 87
    0x100c901402d030b2854010100f0842c90041c1c445510040402801c64a11044caa41800d010703c0c014901c4c02d000e49005582410040340640409100d540040c50300039000d810a802c1c0704402e100541d2020b04142c0c0c0c004075040e00890000b00020041c140010600c81c01a511010f002d03003d0180c0d81804207404441c59030090402078903400a00c425800700c210744420521040520041c3c81c0c1b40d1064104c050304a240c0724010500110540c0154141e40001c4120b03120b00f40645000c03a6668088180100182c2041c8080300035a0b00a4001c810b0301d03820041e03044440b4030340c9501201100d9003143c090f00002d00f0a507000056081610404a1000c1a0300d41404050410415807515041e0341480b14041c1040d0100b61060203428820344018020081c4860540d00d083d00348150703001000c01003a02d02c4403804414100b010314601c2141c0f1502006088501e00b01155600031030290401007007a242805803201440d856502400200041e0500d001c5005c0b03250b0800c4002821104a078000e00d0149804000204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 178364910 1250 178363660 178363663
    0x2030a0f0c021003020705100c0207141509060d0609090308040b130309050607020103090605040804081005090c0d0f0507062a05060c09030f07030b070311160b0615040e060301110c 79
    0x701c0f0718805050140e81c1c0c00d00e500c0d00300e1806159241082d803c40c0b908501170785856010440804541740081480483e006d40d104000302c0300300314001100f800c10100110103003410a517002d0318110b078010500242d40c9a6990b211015140ea8240441c00921518200020868092040b0750040a4920305803c0e580c5035580140c8032403024007405116210105030141168030075086030380010343c01a0f00340450306092800c128181c000780105141802000d0310403c03043e00703510a5510a4034403a00401c03800011000f0b20052050b80001500d981c811440d003040882d100f0401c410041041d656481100c1016103d080e500d00c0601c200c100c46109182d40040100b40006a21a040502e842005555207640400a46000071640c4a04100c0c001e6440000500c00c031848020300c1411603840034040c5409000201d2040c0c886c81d0105603140f000b947d0a00c002c540900c520660141d00076204c101e58204040d030783e5400c0d402992110344041c41d600708024140c03c083c041c4412110254194a0801108001c1503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 178366160 1250 178364910 178364929
    0x30c0c010206151c200405070219060510032f0108040b010623120106020d020d0c0204053102180106021c051308011a030105072705040f140c0301080a0314040305070602030a0f0c02 79
    0x5000d540c3c450340031518410a40142070002c6600442e5200c18041c504200010461030f183f0986501d502e14041d103c280d4020b03242288500e508c8003119925a0a01e4400d8501e424400e6280c18200c0d41c80c1c5601514184600050204c0e25039060242c4040d0f1410400074545180120244119004003e50311003132604442420360b55a41281c0104440c0e6031030081d0f0130f80c9281c034581d050303100856008103803d030102e54800040f058003d440c1c1c1010b000c640030003001114400c0c0f1449005903c03401020603900d4650020183d00640391a000307141c010704044002ca022188d41003a120707655104460b0a0741502c880b480304a824095009200d01c1c540008040c100c10041402010f125070010210a4a004401c0b40c0320080c0c6402801004600c3d6000e07101c2006100313140c4680ca885141c807002c02e50b021071100c00daa049a0914004103040c0906543c215060318a609254071800d200380701c00310004005000c0c10001d0880d950003103480d2040c90b8001405400c10462000611160030805809a1143d1184 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 178367410 1250 178366160 178366163
    0x705040c050d1a0301060b0a032316020f01050c041e0e06060d02040f1805070201090206090f010e090f040c12020a0e0603100e030c0c010206151c200405070219 70
    0x26600043c261000d96100c443e1941585540380c482c0110350404074002810b13004c801ca82c2c041121040d07201d00f0800500c0c2182a00300415001d000180307005082c0d040c4042a140c0e2441924910540d9504140c01e42b4801e41c0c1d49580c2c07240c0420140154140c0c0784410050f003040710060010249446900c18010401411040c00b0300310020321070030440403e4046034014546d400100c2d411a60780d504099034000740504202c04141000e000c581100d205000761f07003600340c008000d14075000404c1d00b0484c010740090201810b004212415034200d54a0b900140d03c6800300b02000304007031038203103044001d0340c1542d080f0401024440e07030020090307100c100c0303054199070004a0f0104c1644444001a01d0706d6142c54080104a0820b050b00c0b00c1c0302c0c40031002c5d2054251140454400740704100042e620b40d4401c8031208408071101944c61000c2c0707455034000c41070394a9004030807503d1025450f00d014140d24081849404429100b40c1e60aa007418420035620144601c0500a1b008a48803001001e010381d210 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 178368660 1250 178367410 178367437
    0x111160e04052401090b06030906073f0c110a2d030e1207060c0b0c0c03070309030203070b070515060114040807090f020408030307050d1b0c050705040c05 68
    0x18108002003028411083c03d0f2002c02c0848902d007107421020b83d60900581d40c1c480d007414100640303400d104054070302400c04500600700b07584c0c071880700f00c403002c44100610308082d900940845803244620121099100040c1c403a21100380018189d60555075500b42c40d000b00b100c2c100f80708580303c80c0802c7c0c41d00041e500c00c00c0d4000482d4421020840e00c0349502214150100c034851580c201500044d06198000b020741e44d205094000c05411610388030244550800300e00d214990310300141c800c00e4101c0e80050046946402c000007202881d00d035401c020000c03404665118402c0c010b62600b0030030880140035544020340f42054999446841d280c680380c001e000c080b42100810304580c041c1a03001c1410100d150407644aa50381d00f001951038100303103c1e0380d01503072030618403107144283e071700031501500c09200007149103444074401120950b21600b07045142566034422109141600c001e8804182003c0c4d03100c2200003c035003040b80c20318105d0f5204e14402d505c2c1005008034907412406444002c4041d81 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 178369910 1250 178368660 178368689
    0x6030a0b0607140a0201020106081c050903030f040f090b091b0d09080d02040311060301050d02131103040b010914071d12030301030b01211505150a080705011116 71
    0x10200c0c0a900501034000d0410414002015550f000080c00711031580c000d030300911a4070741d100380b410b8a65000c42e0850724848603074104004081e00542c01890020030190032030707241c1200346079a24a140c00980040030b200004060401c41d0312410301500440e20f6003201e00e4600390030070201e00400d0141040802d1425100800c001c5400d03d1560f001c0c0d2407103604112101c0da40d802540200d002940326000440700d81d03840001142103801c00105580c1a6540503150745400c0b03141303400700150455030a241c0c0640700c0c1c9071081c200005105102944c040e0b403207918015425414071064a0075120240b00103101000c0c84c408006555520080d6070710b000c403022417540007041807000401c1c0e202c4c1402a0007041391000200020421400d07140441c1201c0c1000c140300308000c04d4bc1c1302b908101d0807a12003d445030702e00c0340c42c00703c601829a00c0181c001c040c0ca042c01030350384a0072012405000f0294400e00c00d039040400b080003256040006070380392140d50806011003150505000d1b01942141c001c100085c074a01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 178371160 1250 178369910 178369931
    0xd1103010e0a080309210301050409081603050714010b0a0b0c01090602120402010206010605071205031003020d21110604060e1e1b040509031902120a0302031005060906030a 76
    0x2035108241d40316204058034048486420500003591040e540440c40c4c1c40741c1b038490122100c0d603c400c54280c40f008800c1a00e50307460b0400300700182140807420307a085201040000720046060320a00703029486502d907661541207904204101d003911401c149080e90400e0340d241116901e0f0003500064401c0a940c40e40c8400d04900b05500421080c4c5000b03008920004c0d40f0144585482c0f00036200318400d03401c81e511a80c0300c00c4111070b280211903000341300c1c1d200048a800c2d0180244c01071340d13004126250001c803850307803600003810810610303030160b4049090441c80405102c8111640c1031441250a00102c40064007040960350709000b400a40000d40e01d00c1d004560510610091408014a40d07080c05e050310020181c0741c50705500200d04140f044a0070100130581002d014541c468150034014508098803079070808040d045c1410750314110301070f001d0318080e1400c0400c040e1140c0000346d0390051301c0303191a19842c1c18440341038114512071f4106021000095884078202c0781c0c07003042221701041c402c514 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 178372410 1250 178371160 178371163
    0x919080102070c050301060501090b030a2f030f0a02031303030203040f0204050c0a030507020a08030a0507020a060516110c03030403120306050915090f07082d010b0309070f050d1103 80
    0x15080401954000200c1c2d8082c09003030b9030483c0035943c0840003080481c0c0c0e140f00550f102003003032003444406401840000c2000042d94080c0e4014070000d6140640d2500d0810309500c0e00c0404400c100d4100d0740801441188416088401d40c01111100304601d1800c19501c00c14540203410001420150000b00040c00c00031126080703110240d010b0001d00180c202150509581e4000756030460000b842c000c00522282d00c0083d0300d02107141c200d986507107140c480040b03aa0103450014012000e501c15007400c400020341521691b441507290552215507445401d00080c03410807040c240344150b9112000d0b10801d503030080700303e174112a8059410780d1807645c60031090300a00940c0d800154842142c00420980a14510791801c0034602101c2e903031190754035a0005414128141e883c080040c030380100060710199007035004240c8403003032403540c6128070b42650b21500300e19098001a240103000b0042c4403805070104058809400940d00030710f21142081c002c2039032101c0c440c50160a0f00041ca401d4903d40d01d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 178373660 1250 178372410 178372459
    0x8030610090b03090106030203060a060b1206010302160813050a080318010c0f0f02090a2003070c05010f14010602030a27080604050105060a0b090117060f0d03020c01031401060509 79
    0x40003110b140c0301c0c43c3c6040c03000c0c024040f610080c2c1c02070240b0030000382000c8041c03042c00196480744804c44d041c0501202001c420060052280b814164200030301c0a140d0b0074000050341061040024968850180d07088001004041c0d00243c001c018141c800d0210740070210a030740f1501424a11020140200b0300102c074620030460000d4941040b0b00c6490084c0402e6041c1100a14000d482c920701503102c880c038032401c540e103100160510068014440d94003c06c2c403401180c0200f0036103880705000007141c4581d421a416505680f100d183e55040780c1107800315010303016004220380e00144d4240100301402801600624040c000c600124030b00207803a00010030305e000c0181c1900720464840b458980307040c5000700010303240d051003499110000148243c1c454121201100c1c10307998918030a40c140480b034400c18000c0c2c4210b0740a548030b2031180042e2101c2c2c07800350b4024003036030042401280910015046499444183c0341049090f0010301004e604070f400c0700e40118003034030220840c0501d43d281501c6c03040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 178374910 1250 178373660 178373669
    0xa060f14160b0a0c030c09050d0b0a0f0e0609070801020a020303130206040b0d0e0714010e1309060c021b031b060307090807080d0306050906031e01022b0f090803061009 74
    0x101d4070300502c0f0514445500000000003251410000c08000b41000d07583d0420511800d03a200004c040304c10000352007066a59080410381c07401103041c0c000080c121003540c042010f0b01003107034061401c110450348104a64001044400000c510344140203600035103070f100040a40050994420986046485103001c5034003e1010150071500c2e8194000c03034101500c24681405017030312070000042107410100301500c841d80e105840f4001c3e040100340600c10020510380c0300d0300140d030796036403104080b032218050701c00ca03000740c2d074094509090002e02c601c210f01302c0300881c0c9020b03922000640d4040c8001891001c40344008440ca9a20307982c0f121012030303c0b0a40c0780c005d86504c0c06680c0740015061070002c0e000d5043c6896031000e021064917a03092119916040f145240d042d448030b0040e28410600303002c40091144418005890803000181080035480203119045071904030400c4084548100e21400040c0d840035041844a4ac082c0c0d01d0b0a1307040d000241c07216200b491400d4036881036074024000ca40003071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 178376160 1250 178374910 178374923
    0x609010903020919421e05040f0504030f08010b0f03250806120f070506130b0703021506030114060108070507060e250b071104060b07110a060f1416 65
    0x7501d041c090a900503898004059030507405103171603c190500d20f440510f00206085c41d01003030340c509203881d030700b507207448000b10701560320a400031806ea142c0740268500c00c00b01100226050420b4640104102031600c500f0040054040050041403c8a400c8500916800343e01e161a5207034550410801c601c958160001002c0c0f5040c0400d60780c2d080485030344541e04c00c442c9242100016507249032607111144000c40c064002d207805110070300e0403078043c000c200d52440755928002c0d1515441d50560b445800150003590200400c0c00844d50400e8174140e00c85800e400900c400340d5086000d04600e030b805418541030200c444001801144108265a111034004009000c82d60800e0300483e265020741000030a41c0b000c40429440070210750320741d03d00b1941c0c80100b5a11f080100c0d1240a1445c840c00c06a85e4419141e0100054506400002c0d2403401e0003410b4200752070403110200203082c905a032004050101c920312240803503400c2200703003d109040b144540d94030341380c5020701c4c038074034400d00d0700240f06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 178377410 1250 178376160 178376171
    0x5070c052403091e01090804031e02060d0b030c01050705192619020303010f060c0c0f061d0907020a020d02040f050c0d050f16030903090b040605180609010903020919 73
    0x42d20008544456882440491080e0070504844c030382a5000d1000140c040031040000b040010200b09a0910784000342c4070360080712411b070380015401e9000c440e200c9401511050110035603e002d11581c2c90f40300302420414900308450b611903403145e06140d0642841841005a6024000021010034100c1d054105500309000c1590030b0300c22030303040440e11608200b041404280030728000000c50f0b06031031603001c03d05502860104100c88091614000f2102980d0030700f800604ac1d10b007544254050034550300d8140d5212740c1601d4030301079091940f2081d8801c4444d8002c0c01303442500400e4682010340c0540300400d000842d400070038081d1035403100154000b49002c0411205085a1018261030804440140000d444101d1004c0e6621300a8480520300086110b241e14500d000350710042966102e403d000410075540c0d1001c0186170810387c0312001040c8001140d45401091100c4883c070401d0403540715003030a6810f00001c0051449000081c001c0450101007520319803107418210b20800b262605024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 178378660 1250 178377410 178377421
    0x3120b0a0b04081213290301091d07030803160e0901090207140303010e010b07030e0a181104080601060309031715040c170f0703090f050601140105070c052403 70
    0x85981c4070f4454070b00c4502036040d8891880181d02d00315030307004218448422202d0f0404a401d048801141d080501c520b0a8001368400c22284a001d5402071841c024005109290121040915068041c01e00d034103400400d400d100040c1c401c01500d8004030030b82c5800c01030840090040c0c8540306200f20382a885000c0302c0c000203e445064009001d82d9118402090902c001d901d43d640c1e07680002c0c00351000c64143d8900500c510b450361006440014002e1800e00b200780075083c045480c22450f5040822842d1414404002808a600840d07074080424102c0d6840c243c83c1c0004d850f280c01e41030140000b0180c403544c401c07040c14400c002843d84990b420f18901a213040c10700640e00c294940d00c001c030f4002e5082410700419940685a251040302d50418003154550310881c0d0751108080060040040c140d07161407100201f4605101d814800e481a00146195414000000c82a40508030040c1c100a0104490000100c503921a58215001600c00389100252500c1100380c560020341c00d011600008000c009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 178379910 1250 178378660 178378679
    0x3050615070b07020c0303071a1302040903021b0d020d0f03020313060c12081504050c1e070b10052101060e090a030909020901140c030c0a0b041e0f03120b0a 69
    0xb03000703c03080d070202d40b824500e040515490340030f20390010f40303036003907074050351440d030000c8041a80e100c5e022072807071141d0614982c00038045036080701e003d500680c4441d0408103410a07106a00c40c08020454001c2d540711000d60000702e82c00030507600200b40c18000e8083d1420503008101b90303480c04501c0c0b80d07140c51040d110b4400500d8840003040a48010025202c1c001d8200c4c00b0b80700e100c1c054a2600c90454815825200b888040c0c02c002d0129940700070104440c2c2c082e101240e0121043c5039002d902d032555458603040041c80c003400900303003010300c5520744020491945c80300d503c070340e2001e015140c40e001410780380b1081e40148526801a444007400f8001c100d9480c2d00480c2941805120351514420b59403514030942c124001d52250340d0208075003c07400c0b50a10180307400f4102c00c90030b440c110f9141c0404030880e02d0601582c1c41003256600910002e001c00c1042c103101764492040740420082450510343ca480c0c00f0b820390f442014003400104414800310310100c2e0458000180064a0450100d03078988125 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 178381160 1250 178379910 178379933
    0x803270303270a0303050405061b07060c061103060a060c0812040b04021002060f06060702040905120705060106230a1707020f010b030c0a03060b0a0f0e100e060a060305061507 77
    0x111182d03442004070070154030b4008080c10a8075019580e190600c0d06100a200c915032020203246a408802481b041c0b0741c5c81c01300190300217040b10795200000e10050b4900141500c40ca0991a40026418010400341d070301c40405010840341c941c603102080b902142881d60082c420b0742c002918040c4407031f040005010800010a024510a88070154286854a0200d031111020341d0002d07102c411840c00b04103585081005040561b00060002882002c10b640307561408081c048103444141021500da418441c00380202801000b15003049015000300e118400c034103000c5c250a40c00001400700c1d2404a2078824159440c0341e00c0d011000f4012400d000d00040c4d0703100c2038030520800039800c00804200c0390402190f807a20504005d005009250300b10355854000c2c101d1081d003c0d40120f035030400069140c0c910ba0710180100103840c60340d405400c1c6440100e18101c25074000341e0f40341c0d00d44402c2c04036030744514550f1b4085517402e160000c2d043e2541d000145800c40340c4005010010b201140c45000c1c0710081110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 178382410 1250 178381160 178381207
    0x40b031302130504020d030e060c03030a051506040b0708031312080901050a2a1403070e181e070909090c0504141015140a020a050c0103060803270303 66
    0x500c40c07481d0000840364283c4000300e44c0203401c25070fa080348800080c0101c141007200341005154904003498403422034555001203030b0000c2060b8480703041c0004103051142c0440c205a099a0061800b403c00c40394582511504400809102001000410000c8080b040617403181d40b007810300340301c00c00003070f40102814015907101c2c20f2546000003003040c001140c400c1003180041074140f0920f112401c624100c201b580f19149805210b02e0700c00c154411840784005501c42c10868440a0f2202c1e00407007804184150703820074000341d209a405001580c584041c0900c0d86510218807043c8940e1000d10494402c2c485900c1444c070f6a00b0f00800c04204240005080d003582c070240c404001007542541c840040c044240c8100754020201c3c6418030a45032508200c0540352003a04000c114440d044180200651140100d1030058100810301c9042001c14171809d0600e5500346400d10801d420052910380ba441070039412044905283d01150400e041c40039802504d003402004c0d00e8942549003841d800b0b25155164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 178383660 1250 178382410 178382419
    0xc0a060f030b030c0a12020f0904080309010e03160807020111070b1b03030103030f050705070513020406030e0708030f180909010b030d05160215070609120e0d0b04020114040b031302 80
    0x218000b90700340004d00301030f01c000c0245110700180c60189444078524400e88140c3e00200406403801f900c1d1a09140c180c00360b44141a0907540781343c69000035085650880340b17484030750010000c0070711a00e00e0b5219480c0168001c4021a03a80c00184010b17910304d141c044461b40f0b00e02480310002010400710003e0400071301d03504601240c544415000a0314ac0c0700901008010a0740c01540f03084082c400c80150508501c84e50495100545410004031607000d0702c206210b6550700098107116003545030042da410b92400c01c000346a6079041c8a82c881d268020107515000004020138903045100058001a080c002c01070040034a5042943c00e16001e000c0d5201194024482c00420350b484030710170400c42c0e02c914020b04080345e03241d030b0355800c004a68036040000c1d00140030501c00c6001142c030b240b00300b4080c544103610040d10210901e4014000b00c0c03243c840548211002040c3c54041088903c029900c6a030900c0c018150f000e49061036802801170f41c104000c1c0318404410010f83c94070040d81c0f10420b6000305c0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 178384910 1250 178383660 178383671
    0x601081603080703180305010f050a060509090a0303020c0c090c04030308070504121e080a08012607090509070b180316081e190c14040912050702030c0a060f03 70
    0xc000c844403030461100400005007003001c40c02081c4120358080900d54841c000c0f00b540307562903c925003542c0b10a900043e10a55a82c1882440c040c2c0380300303c100a00d01500d1194441c6030085005880b404c420714041d09042d00090303100c4d040f42041c0043c14040c84014031000c82030420b5004000540c000f800220041030089001c14140c0340039405841c101c0b105041c22401410042d668006100600c034490b8420600070340342100001d11540141012625907500d40b100c44d03141c02800b0a080005c0400b40485070a01455061081e0000c0781100c161034a10401041e03d8071070905480c58425941e01010f4043c0f004110201c022645000c41d4000c114100d0407581c0d00d508200c0301080c0c4180d503114882456221010050040680c1742086644104030010b5400d50030141803030144450700000111060400004103200c40038030901d505032800000e880411a5010564401b0a00358044072003000f40309010401408555040214001e60040a0800000d40c1d80d9494041e10550310314190380301003420031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 178386160 1250 178384910 178384933
    0x3010b040e030921070306020a031e050f180a06051f06110d030c0507060c0212030c090108130b240d060e06060103110405100c05030705060103150c0206070503190e060108 75
    0x900e109041d504c0c4000103070584074038513070b2050025030110442005040c0c40b018400108da010a540c909412035011000c00c46103051032492400100042103400c12021400c02440a80800030b40d09801640c400720004e0715490701c84522411000394007100000195080300030900e181d021302e005803140d5840d004c4810f81e08241400f5016a008003800400040307003030002d00d02203045a08001d4041d03220340180c5010124001418079241c3c0100c07245a2084000912241e01c0e5034095400d903841000701041c800041c2d06940c40c204d113076002610302c401c01040300c82e04120043c003000c074100101500800c511540c0c2040c1ca13004014103101d1002103d14004c540018209502074040c3c003020050003143c0a19081c01c6c5000c1191891b11541e0b45801c0203a8210940000f0314100020680c4c41d000f80c1c010070709507145142c22003503500c801800348109400d11103101d0400d600062415000001800d03c03130349955903003d00700080c00454034490745040c10440551840d000c00301302141610f4407001540c03001c6a86 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 178387410 1250 178386160 178386199
    0x10209060706270807020607080c010c09060f020601050d0803040302190c14010e030706120f090b060a050d08090105091c031707030e03040506180d030906030506040c020c0f03010b040e0309 83
    0x1000d402620200528001847c04c00c00800c2c1d0ba5102d441294101544c544038039007140c031480e0f985000700300c081d48140701d89078001e0421102c100c46440100200c2d810701d030200d186203a142000401c2050040041400c02d4000d000f400300901800c0b54550101c0010700f844040752081d44914000030300c81c0300864080354410007403080301c0c09003d0020308080c1e1410700f04490003210402a81c904540d00d20120700a4466400340c01c000b00d015030180d401505180701000307506030140d40024441d80c0b8100112001500507815120540da007420700c151150703500400b10744000e0142c070f210503070005420007200406412011490f0103a81200000110380d4941d4425003c07200e0034589144d4070390017407204000501e4030070300500f1a00035210036400e0750456a8003142e06001317100001c4011407443d403018040e80b80d26206241d4060000c5500303110400703400e20069103d02c0c1d141841130145084008614907500d00350030812280f03030013a004108017407a15081c5500e0f600030300100d5220707261040c1c00307e182051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 178388660 1250 178387410 178387481
    0x605060c0c0d03110a0302070e0105041e090f170304030909020c032208120a030b030309011e0c050607030b0301050609060306011215110702031e07060e03010209060706 74
    0x1000300c0281501c801010401c140201c10b072808604110300104d40d480755031400c0c0008100b40e8800c3d001030040c241010403041c070001c070580025010710302d0081c0303454001102000d15480319062400002d5420b0035070034500b070311500444000e030905240420404080c40418021840749009940741d400040e00c428030041640310703a40b1042c100d50f10604c0f04180461045031116039009148440110290f84c60031000e0a0400c0300268400d400030104810b11660303054080c40d08400800c41c041c610b0544400d0011300761440140e1000c1c1e0000c0c0d40491458034901404001000541020442e103162414940007030103403207070303880c114029424107001c6019400d184041c2801000e004015002030380c03c0c192030002c040d00c10300058803400084646001441d81512513101d403681c903a802075a41c3c4404d070040c54031b49091800c1c400017112055241c9180356402240c00020f8500c4c5107403a510f80340c50320380040e004e401600790a5a002d800007031100308101035940065100303c03c403042502418825402a00c4115 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 178389910 1250 178388660 178388677
    0x60c030e27070305061e040b1302030403020607090b07030e061308060106121503080306210c0a0e10230603161106040b010513060905070210110a1b0f020d06020d060506 74
    0x819a01107004003006e070301010802044040c0c000642c00b8001c4d00060b00c0003e030810401907540d0300109010a0582c14820103610000509080045a141c1b04016a90f4410204050704000303203250404459507e100840d0006c03008800b0031a08992244e100c203840d800d0030720420f07020858020285d40c40384640d014003083c243c2c603041700c0c518ac1c520711340310003580c6d5100030000c03940424070003080b40c0c101d803010152105032220701c00288a6903040e8414402c0d514540c1d004010503001e24420001c2090b0143e01c001d0650710a192921482e41002c0100042d0044228440b40d114602000304608980c802040c00c02c800800d65a00b60720000f0140100d48a03c2d080d80d0140c02c4411600040c0190b040c241d01c280c145801c04000020501c3e5962080c00c00c40da010f9410100507001500760180c16901c17401102c408100004c2114070b8407040150240c020001d03148a1862114290704003000d21041d141000016038028001c4984518907180c8140250f20070810506242e01c0c0c03d40120340d070708080d8166a4500c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 178391160 1250 178389910 178389919
    0x90e25020106230307050604080a0c061d010c0c05130e010c05161b090504080903120301140112020d05010b0706060801050c0a030b0f03010f021b0f030301060c030e2707030506 77
    0x502d0308004180f4025140c4040f160180b00d000d60004a584800b0700078001080f018019040090301c40c500481a8051540210100b00e030090500c82000304e1100c00300b00049090802a03801c032164513190040c456280d00c120303403050720b0070440038812082d60050098100c2c41c800800c911000312300150740314001c1c1340c03001c0d50142c10f03054401c0c0003c0465046d6244a5804000d4400b60342e503500d0325000340e40080700c084034a500c0c08600f44806040801c040890586e00b40ca0f1141503605015031303102c222254a01d2181080000e07960015104010350440d48080700506050010750f850700c00c0150994401c1c003046400c58900f40000079180410710074180503401500780240362940010040700500020504a1307400300c0c0ca41e5a004450ba000d104080030042c0d1000c016840e8042100c2e855042801c04c00000c600d50091900050840360100489041d03440c40e003840c050301b50050a0407540040846000d5412078040340d0350034000c8904d4181040141a6031006400c26640d18038228250b80050300c605420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 178392410 1250 178391160 178391189
    0x160608010315020412030903020117040b131502120115020106062010060e15030a0f120504090e031209010b0906040b01050d02070c050306060102120307050a090e25020106 75
    0xe040c02580320262000560150500340c030f0384100c4076461140b9500714045047c00b4810021560005202005045076280c1e2421601d400c0d1038005103078100134103005101c0c1280010004000d07002c1c0c202036030307008460402c44d1110343d004014220b8a02c213000e201505e130080c42800c00c407548140038a80030749407950f880441040822a6851001848202c80070320b500655100d80d000c48a288680002032020101244203030a14241030036094580140403402500584804030100f900c0d5030002103280d5001c540c0c400c854050007800c40340b50180750011840c0a007400303140020f0130743c00000b8140190030b00348444140d8444026090880c0d00329144190031100c0d507400659507103081e50014040c10010b0400743c7c5800b110f01d9810040382c2c890b0b10200c60300858030a0900c10390404001d490b0f4821030a0004045202c00b88920341c109010082024003040700c0003941140a0740b04454810040818102e8080300341401004981000d0840781098090f0342c3d08451110800d105000d090308032007510206004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 178393660 1250 178392410 178392413
    0x307051c02011823100201020703020c0609060f031008010515220621110a08100f09060e0a050105160e09041a09030c07080303100b0d1b02010e1606080103 68
    0x208500c035000410f4685803c064002000c642210b690720b07150f083c2ca90310707001d80f80104042000c54940c5041030000c5a02c107100000010b5000912080a0f44045030810340b0703565648009600d511807020702c124a4038012050040040c00e0710103c100780c0b10528003c2c082e6030751b10340703070f80148803101070b00142d00240e003c0c2c10001c01601e88221403140c1101d41e00110300c83d601d44101e8898090005954186408650501e8050100203c60002003000441c1c688994900c4e010701990b0362421480301c03400c00d0b0790703601104014280a51201f5056940300c00c00b80255948030040c16142d00c00d408091703e4550a050015803e80940780c1180c03200400381c1c43d40442980c0103024010344444c020005c89100f031801180c45828002d10342500c0c40340315140c00940d82c07603091916032070a00015500040c3caa0f4001d0041c000c10f0002841d9800540785c003070800340d8071138241c14000400f8244c00600488051140455080800e5040d008419405501c0c811580041d40004501445407a544980310014030050b00500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 178394910 1250 178393660 178393667
    0x6161115161a091509060115120e0a0b0105091b030c0d0f1a03101a01030e030d0906020409060b0c06060402031305060109090c12110f0102120c0c0307051c0201 70
    0x71400350051007100684007000d80000c5001070706440040e100e50240d1002440c040c0c441c11210361204d5520060b0940d54508184000d800302c03120040c505000415284509002d0f03540d003c181c2c40c121080854055861034242010103400a000d440c3c0140c0300d110006140840100343c0f01c001030358500c401c03840c0d65500b5680720007c1c2c00010f100484183c90f181d00c08003a101d07a005025030400f1840218a41c00c411000b014a08200040020304050912010700d1080b11403142900e184007003800c01080d1515012182421485806e8070000010b181c0b660f0503040c030070726178054020344684a8041000c10f032070300401c0c00d05c0c3c0960b0345040e4850b0f00200000d822410990040c5801200035000c00a20841c9543d880b410041c09070001082e0070f03928188601400300b8103510030020b00a400118203603030a641c40780d4500084002c419400b609580c108100b06910803c004101c0c507040b0900c190316100306050b42900c40024540e4180b00788140d171310202d071604d81b559005245c24909074240441c00c05550065 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 178396160 1250 178394910 178394947
    0x6080a02033c0f060709060915091e0503100b060d090f050a050a0b010f05030303040f1104020d0b0a1a16170d090309060e030a060e0c06161115 63
    0x15142d800c0c0015180c46505070328500c400644555000d80010407650001528020300144030f20300700114100100704a07500950100141d0302c0d03104001d0007986003150103030790300041c0d544103100310444900d807141e24a21200403041552000c4040d0781a041243da24039041e00c0d006450740b41c3c8400100084584017000e07600a01c0500d01c52a0042000d03106522101d08140d240442554030347c1050307506008002c01d550805015100b9014080c55030340c100350210390f4074040208001c015145100c48802840001324403407816039402401950b999140003500406009851143d80c029028004041000300442c82104407007c4908400f81c1005020500548171942c8100107492000300c2003a01c107642042070008000e105c100080200b2008120314000301181c5c0360b41c3c0085d080000701c0d0034240e070f10740e804114010b002d90041400324107040700c1c0304c95500340803910417182d40c80745001491300c1003401d83c07035112080107002d407042003540100300090100c09104102042c0b074110003001540780a54501400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 178397410 1250 178396160 178396213
    0x1d1e0d050705040207080304140304060c030810092c0607021911040c09170a02090a0c02070b0301061e0e06040302010c030309021302031005120703020f0d0b0c03060406080a0203 78
    0x21a941c0c10341d5030000c03900300d90010340c06690a190000401c8140400790718103103c40401100114500f500d0148002c00d00341050400904110b0750b9004604c500c1840d1035502c018000c81a41041112400714540d41c1d200b0740e0240c0b880000c9181502d0040300c490101c2c0c1075111b45415005018000802410b545021101c076604480006560a00b840039407260b108255443c0703c5500c0e00850542800322244c80003c410b56622403e0b40484603007401a1a911400d60b000301030540d000c6500611010305a00b0080d45412040308242c01100010340c1c203034402264402092150b18903019159048800c450b03500700b85d030364243c100904202c100015403144030483c20341d60092800007a441519400286610050b201d8402c041c3c0e004402c0c8a00c1421400c1e401c030007020304498103500120074049640c2c0358451403001a214107900c0c1c03002c840d1078482c042d215a034180c0c0030901c59038500e04001a51041e80003500c08074001e618240021075500d40015911040c242c0003001001005083c0e58420032034000b0025 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 178398660 1250 178397410 178397413
    0x1303020703051002090f09040c0e10080307050a030f080c07170f0a020a060507030903122a080f010f030f06050702070504110909100e13050111030103031d1e0d05 71
    0x340000421801c1c03102c45032441d8100009641c400400c0c1c200302c1190b036614801c3d8400c3e607200061100041d1410f40000c02c44401003415031642c1d0703e01c0b2600501c55132903807020042d80170002d03440c01040408101c0307154982c0710761a03400c5c0004001c40221107103041180e21140c040741c02c100ca071001c29075a150a50640c1007045c885031030701c7c03418415410382d81c200401030b4000da4400d00251041110031301400303902000a180400c0181450380f80203040c0800f0701c142d0007441d50ba511403024503c1c1881540072140c400c48041004003003021900828194003181d00d200c804404c8000411404101a883c400b180e4000c1010308080c03009449001c01030801800d040300350311640c1c10002d039580f940c0c0610740020140011071900c2e9900030050068441005217a103c00b1450030b10107102c040c03500d90b182a0032a585d202c5040c02240b4514100e4010300165500744800c240201c000010140c0c4004421140340444400c0f014040f0080c0c280610811020301c410702c2518500591a03050801ca06648070842c043c40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 178399910 1250 178398660 178398673
    0x1e06070606170105070f0903031b05010903120506030102030402010c11040b03060c0406170402010207150c0b0f190e0316050c04020304050c0a06140d0f020909010b0d23130302 77
    0x1a2590101e036502e5000c180b915500d080340d00d030300000a00c11a83d0005150a041a40300301ca0301c0700401c10211400010b0900084100210a0301d01b02185a208981c2c0540200300385401c2d400d0140c1450a14914085000d0510300060018141070080d81d000700c2d810303100e007801e40a242d81c0320451480d0148803990010741d10603000c80700b540c0c03c10490f030044101c419201d581d0b60a024005206003540d80c8280f1060010105110051368000b46900c2152452008140d10072036880b401c0f21800c5100c90050916941842400300c010100380c2d4a90059003845140c07040380b98400f42c078070255002d07460111210303041442003601d401d05c540b00c00c41485200c2c00580e503c40a400d4005400ca800646013074a0320752240c4c000200e5030500c00000c801070862410080400110301c1c41200e5a446042000c200e940e44278003812259520b1a01580c00e0b1080003414070000f0341c1c50b2941c0c040c2542206e618440302c14144090001000c2c06065214004060510205415680c0d14035065102d080c4800885c03c5120f4003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 178401160 1250 178399910 178399913
    0x30203060d02030d030e10060b044506060c0b011e05030f0a03020d11031c0617010b030712020901150c0803090c100f0e0904020112020403060b090a09021e0607 70
    0xc4c0700d2000340e0f4000392000035525011ba030084d894004007200e0140b0451416005001030302181c0c0a84003103825100000c6100841c024000e601408181180c286030074400314100d0190300b003286802c0050b0700c221010044a541e44108072401e03228000f02074003a12000d401800704240f241d6059244204402294000540d650046480c00b41840f41d18103090f01300341404010164140070203149800149407594090000c40032140e168030410b4450030625000d40300300d0700c0c00c507090741103000149400300b0f020704000d4105827128060700f60855954824020580081358210740207800007100d9130090304c0303404261308020482030129a0b842d40740b410310241d4040c0b0000900203000030341c4a020b0702c3c0c0242c000c0129007410b0101d0003039a0032209040c4142014200d140641c0f00300351482050040b252861a5250b5000580b190354801800c80754681c00058048280002c0e50410100343c40180e4002035a6980c001e004001c4074404c1c0030095000d101c0004404882000400029451400038000c900c0d01c02c26 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 178402410 1250 178401160 178401163
    0x931060209060f13060e0612060312030a090303060519030303090606120c0311040b060a030504110303040906082103070c030e04061701050f090c010f090e0c0705071e0501030203060d0203 82
    0xa0048040a00159410004d158821042e00404080c1482c2e1b081c0c03400d5030000b54030f81c0103d5403c4c03801c1010300381c0004c10540e402c000c60315a04034035182090f03907806e00782d0401001e0048550b069011900b0701800145504003400b603c1042b0a40b00c40c480d550780d0a596080340a80826241135601588880e408141405030010207074200d885990a14071070b41c914601044924007041c03196220310724200b10039032203440c1d6904881d90b4240c03d103400503507580d6034580920601c0d58200c401d83c041c0300115011900070f045500c40c2041c0c490400481701c4034002c00c0c00910786070100344000e5441001c2800400c8403d805049000c210f0b0348242000d0441b401018003207000c8800641c491601d6568950303d00026030001e02c2040e42200440780042d00da4130b40059461707030301d900b5009030314100402540c440604078410103020001e05203213401b0322494104030100340042d40140d0015a11400703104000030700d18010130140d80c80c9013220201030302c4083c40c000054002303400003031005402c150700c13120001c01aa170 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 178403660 1250 178402410 178402417
    0x1b020616051c0306030213060f09020f0c0f010f1820010908030a05130e04051b0d0203070311010f05041a03040c0312020d030506030a030e0d03090e0f06093106020906 73
    0x110f660b000400c94918010080c102140c0c12241c412503250210500c0032280d030300c1d0f00c1c2d005d82d00c0101c005030f550412500c01d00c54611822a090300075006480400102030b0341034100345050b042c8124180010005698400300070402c51100030322401007404895030f81136401c1101850b25005040c080001d030303070314461182107610040c002e100080700061080200381c080240c107c003800014600180a20b4556542640c1c0d84001030103402d590200314802449a8414000600b029800b4003541d03500f660340d150a0102d86409240c00d070100300c48403242c0c01c1c83c0b8460000c0e141110142c1c559801c0445441c11300e4070703041d4400fa100341d036801450380b40031010940d600600324203500346900515071404660401001c5540103000d4a00c80d800c5420740700007281e030003140180369003000c407116612602146402c0c0c0b140c40156000c1102003034400c0810940c0d0090300c035420b02ca064155490041c60796800b03070350b1041500b5841d100051f21458040f000740114100254220380d84a0000145041d10080c0084d12941 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 178404910 1250 178403660 178403713
    0x190c0b0a030f060608040302100e030f0d1a0f09041407030f0302031c0e030405060f13030b09010f05131401150906140d030f1107030803010b07031b02061605 69
    0x39100c81078410100043c0c071800005002519100703045082c259130003502c0d452016450f164058803194811490341081c81200e003d40d100c0e14580c5c0d900c10354540340380c0c007408441041c400203da04064540c442c4c00e040c41a102c0070301004114900c030b03686a43e04c0c120444601c008200c214810907401000045003501a04400c40c02900210b4950304902d400e01c4580c14040340302c92501d03040c4071804080140000581c4e044d1042291031984030b2095554243d01401030f050032450071214140c0c0081030010030000c4a0250102c10000e01c03003044c0d11401c2c0010307a10f040c0d40880941c072000011201203001c100c014001c2006d494008940185c1a10840d40108650340142d8410382e42c40e8001c000050030301e100082c0d280d10580e10345151280720307103001d000300511090303d02c00c3c0311900c0441c10840e9002d20414020b076600c60410780d220b584031100301c101e0b504040d10440200c5c160400c902ea1482c190907103001060744c001d00f00c031300c0e112400c98143c44a0001e84011105403040e40f07030b13004c080a0b410740c0c81203091 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 178406160 1250 178404910 178404917
    0xf19050f01030b09151b13121a060607110301020c0d0801050f0109180209010c08040810060503012c0c090103050a170a0207051507020d0b01030b06060c190c0b0a 71
    0x15419403d250107003010140c642203003980414044404442c4940701254800d910010060f00072602d0f603140d00251040c80203901c51030050701c80110324600c07164034000c5024080c00202c44104801030006416080c01c1e078a20354418018804c01c000a84030210180f002003000d4005030801e4044580f00d46004d000c0d0504101240f1590014403d9061624000e040f0300d100340b030048007003450401d40d02c01d02c845041220141c41e4000420103450303400344410709540d9a101c00360540c9c40d55039241c280d0711003c0c000141c04101d42401c40005561405009406801e100b220810b0344140e11864600c4001144a403080058010310100d45074075955030650300d00860181010780041f00c12442c001c3e0380c485d69281030900644040c040d940815500007003042c19144161000707141c0043c40045400c0c14080d910000b98864510002d1034200840000194100c070310424080841d03171200d03401c000130750150740c80e0100d990348803140741f0000a050071701c5024101d000c0c50b10349025039221409000d25038001e24080020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 178407410 1250 178406160 178406191
    0xb070c05030c031902040b180a0f0f020a02061504110706050603010f02040e01060503040606090e0d0f0e01050708090f121f0b011209050f0d0e0301060b040303080f1905 74
    0x6414140107254407402c00b10b02401596000d00c20034403001c1210306021703004581d00c4143c0e03005501c885424800c0c0707041d204842800c2d842d11140305000703050b01c0e040041c4514205052001e40b1016402605e5070400745401415544c0d4401c00048010181c0401c0261310544400c458401c288040c80140a010700901c030105452a1280900d8291110345d00c1d00d200321441040200500a483c0804a0551340d8a1401f01d94030744403414118084c0c0050303005058800d141441006154100060310442030311191103009102e001094103550018040d003003035001c51400c02c0b0020004020000030030301400014600009100080b000c20005101e10810640b2070f4130040859480c0400c9519124410305201e2003032040e684042d000030400d610444000040b143c070f86030082c0030408140040c01501c0d080310304480c40d510200000419003454002080d019501c0c000000c101c0701d00000448041c1c1c5c1c0c050f210b903031290700c801001d00619030000b00040c0c040d103511160700010f0350441c041d0500800c03000309401358 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 178408660 1250 178407410 178407419
    0x60708041e060f060323031b0f06150f010816030f090803010803040509090309010504030204050a0e01110d0f020c07030f0f06050103030512090607140c1509060702120408100b04060b070c 82
    0x10000384440d20385c0191b50a0469600841c3d20010851324181540d0102c01c1d04080803100c1c040c82c0245a0052180c140103140800c40d031580c19040d0024062400c481e65070400d00060010b642c50181034402e100f07802d001329441c02459000e504054088100e0700c400180c84980303034441c40d074075400c2a086800140c00011317041080385403060300c031500080860080c503e0300a540300003078541d11035840001d000d00e440d000003424050301ca074004100282d000000b801200c0040d5680714035a8418144040d05c1e82c40d0852540c158801c03403003618490800171005201c1241152140f2070b142240c110210707111030b60a00400f00150345030041c0d1303000b03500c45e842e612384848955815080312907005156103410b5000c00c0401140603445003050b2000d001015107280e80c0c2400181e01401c060144585c010f08060000a000040000194581c81040c455082c0d545061840101c410036100c3c0d4070a05619038071058030700c00e401c4c180b80d11211030810010310004442e503554282103800c0d00400070654030b031f01d5040340420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 178409910 1250 178408660 178408673
    0x4060306050109080604060506060409050a0b120a0b060609062215050304120806030f011107060509010902031c09260f010b061206030f15040c0602060708041e060f0603 74
    0xc054072007401c010803103c0c280300f9603e90b101030050003d80309130386400100d8065140c1c0c40c2110094600e208051082c0e19060040c0c0c800f5152001000d8003039111000010369410008c640c0300e000c143e00802c0c0c40b18545514040100c40e03042444120f62000041200030805820040d8550804141408a4090038034002c0c0d154646600d040c40081070100c00c004000c005603003409410742c0341c000390601c1546501c0c3c2d0b2000ca4600342002e8006261586031043d001e04001c0000c01400c61148154400d0156a95a1408034240c2d200fa45c0001d4055018464144041e4007542d01380b0120116803800c1401a6981c04061098010241c0b190700007032000100440d90090521850001440d140f0081c0f01070001800130480d035202e0955402400007013800418040e5805214115103240010308440061848032403180f50b001e000e03070b01200c0c40d50315900005042400824420311640741502d82c1d28165a560301c400d0014440701c500d282d00d00400d480c4500025580344a13410102c0b00031100060750600314540071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 178411160 1250 178409910 178409921
    0x30f0216030b01050909011103150f0415061d041a040c17060409020102010612210e01020a020d060912050c07051905150f070807110105181e09040503040603 69
    0x8504a00d00290500c007041d0300c0c2c8082c604480054540ca4825680c142411780140411601c4649462000013803001d00c41590f10f419174241c801300e9a50f03d2181455040008440c6a441098079103491440100711840c00f901041012280c0d030200020901b82c0310001400700c4242d5080001c0885032648034046508287c0300750380c007061180c1007948208885c0c02341c0c0340c0a0b480052800d44075540f02e21202003164401c2d00244028a083e4000724080302d01403803d008440311849810840e07420200303400041c5485101808541c40040c1c026020410546e020310030740c0342c140c0740261011b03504d40d542c12002480340c1e02c000780c984d2100c0e940c0a0300d0311141702c501d608100d06680036a20600203124200804013050101504840d000c607014599614124481001c0d80105000344200f40030110750320f010700840e00002c2031158414800041800c1c030480040d500b9001e081e20310402170781e20780103180550800b000c2070088205401580801c490140300024004401201e00b1201d80d00045420000d058060152 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 178412410 1250 178411160 178411183
    0x50604020705060117070902031008010c0c030e13020f07110108090c01120f0e06070507170301060c0f0201120c02070509060901120314040f0305061902030c04060507110409030f02 79
    0xa41c500115a101c039a511030042c003840d0481d0300d00284800c19600c2c1003019000400c85900203544924284003000d604c92168800d2418650130822800019032042090440301a85511618580c142800521000050032200b2140e615801c200c840c101148282c040d11440344640d88024801c0c40b0348000409000000e0a40c0d14154001c0c080c513001c90b078120301ea0310440c034500c800003d84d808400445502400008070020194000c40741400742c01d50384000107018050081d9002003200000c0c14540d030b604c2c07000744990000240100c11800010310003000543c140350052602e0250388020182c0c100844071400c0107940568010141000f160030500c0034294481d2089502030300e1580760405103071030211042001010000c02c0030800d40ca514410702030340c0c05080c00d0020b0407103c1e81c492429075500c80701500c690b142c1f044100d4050800114500849200c1e011104d0164103103880e0803402e4800c1d40001e02d0403902e10300c191200c01030549561041c043c10a0195940803191501c4940107420103213005803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 178413660 1250 178412410 178412419
    0x902061c020306240a050f041508040303060f0608041407030605240a050d140a0c06090303080f061c03030f0203100e07080402060a080c1b1b04060e13140f0d030506 72
    0x6042c4621104e06941c107440343c2d03040c103658540d91361888281e2446035130042418180040f12440c680c40d8401000c0348038038441d131010000e0a4460004001c3d00390380741f2441000a07a9800064000f07080311051140a000074421540c040e41c9071360750a42035520440d58040c52500445040d12000030b1140300d00a10002603500d15082c074103000c04150410300781680507101064424050088410401801c00c42341c0d00800d00c1c0c5045500d440c8001d08031120f9200580000d00a040460040325030030002a0103030700004e02403c00c0c40407085000300e000103040425020702d42d640354681a003010a000444c0b00e0343e031400000d0a0a0b09021a07400380c244003400e46810012080100401030f103805080301e10004003030130004007958070881140300724032414842c6024102c81d0031051448600c001401c48884080300c2d02c105598102806001c21108680718442d0b2001316800445c2c981c42d101c40442080a00401101c01c0c400f1031040303001c0c644443c0d84490b20056100e179108140d0785615110b070a800400855 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 178414910 1250 178413660 178413709
    0x5070e150d05041b0e0a0e1506040f0f02030a14011a0904050c07200f010516060b030109050d1806050403080304120e18090609010204180902061c020306 67
    0x104490390080c00d5910800550714800b04080c04044218a490220001003285003503858202500c82c4400944030340c03201d10704000d84d200242c100880c0580f010211050070703007265542c1d40200030141003011444a0807170369941c002c1c4041d42c81800210f210b91010803010400010502c006508403105034012819421244111405900c1040c11140e2159040b1000b144c40c1e20384c20340303003095885840d10090180036008010507004102500e00000b40d070044400e01c20b40084280195218864840340280365024507000d800021801e5002c0b81d1000da010b0000117000c107043c0d6a4a00d001d01d03001e000380c081902c03094031024480c0c0b62403101014207000d152090510b031840d82d540c206400040c00041c4150305101e0781c03900d110310070725800707021010040101c00100358482400c1c2420100340e075652010f014035000034207030300e0b01402210200c1d40c0c00c15080e01580c60321243c0c90300400440e03500302d0f4015020028030908071040031010003400c1d05000d0040c0d0b6800c00710100041c60301c8051806905401c0704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 178416160 1250 178414910 178414939
    0x5060906060916020c100e0f040b10030e120f0c0c01020102191d13090201021b0901030321060902030f1302011b0c0b0415120603050703031b050105010905070e 70
    0x10603072141c2102c29562140b210707a000f200c0603400d26080d000e402d40c00407500060f2a1055070700440c00128014150342036200c2000c03150521003a01c541c607203240d81090201804209141c4030382d003c90301d00030692055818900c00e603007140003694040850344009010200f0507442d100800d011900c80341409000840c80c00704460341a0302051120500581404400000e00c3d19880780309000100c4031200034125000f0f940e0452000008224168069005126104043d0016440d048600e03102d06001041c681040c2e18503901120944200c80c0c0f202145100a0003038001a4110301440010b05040030000d07840c3d1410504016050b08004c16084021152131011800360b6005480c0d040080c1c0b60700700d00c82c48481e80e81410003a649541d0300c0070801c0c45c000140040c0c1504800690203d01c10680c2d11003c0107005d5101020a6035140d01001d0800d40101d8410400a805110f06101e02d081c0700e0780d80715401145032141030071220241e2210060320b07100e0707003005017140d8420340540f4084030403146180e41c1342d800e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 178417266 1106 178416160 178416169
    0x50a020607110a0810060807240504150801091407080c0a05040b070c06032306060a0309080307021f0e03031317030739020f0103060f030804030506090606 68
    0x82c4480841e0b43d0f000408d031001200d5800c0c100110903007140e030303117004282c1c0649042d8040c084200800603a8003001100340020700303810b4030b4101c1958900342d40981035035050305400055401040c2006241900403951303682200c0503012858403224950801d480300e229913004040000070118548041103854000307182a110695400d00040d94a52901c00c144148519200001110280007490764148480070340351030310440c500450b814142d0f4550055542c801d03661180141c0104410000b890024040b070190b0260003c1304104044070130000b6a224003000c0c0c19405900404900c0b6000c0c488044041401842e510b40e905039a810f0106c0080c01c8405103502c007060341c504031851090005507111010040c03569080c0d8440c00e800655080166034400900c98605041c0d480801140184540d8198800b661103203a0035640c440c00d41c200145000d000808401140c1d211108000da540c54 = true := by decide +kernel

theorem cover : BRFrame.Cov 178237410 178417266 := by
  have h0 := BRFrame.cov_init 178237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 178237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 178237410 ≤ n) (h2 : n < 178417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
