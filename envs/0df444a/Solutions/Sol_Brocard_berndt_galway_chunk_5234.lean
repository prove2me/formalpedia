-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5234
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:11:41.21475+00:00
-- url     : https://prove2.me/submissions/fc5074aa-2ad8-4c9c-8244-5af6a156362b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 941187050 ≤ n < 941366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 941188300 1250 941187050 941187061
    0x5060a0306061d090c18060409020a03260c42190e0304030f081306031a18070305040c08030c0106050a0608070c080c011112090d021f050c090a0b03 65
    0x1491030b030013040c0300f203581c0c45500400c09680b10402100540003045004209541d590000318010304082d00c0001d402004444002040c000c0514203d1456a26000050024140c00260f00c1c847c0c000e14a20702d001c1d40088070700c0411110070790a803c0044050202da020300e1440c00081c007507900d160000100e01194800d041040000031442c0c060300104441c242080700d102e44c0d8011690724011400020001200da0025105000400081e90f107091001000c440d640c50722600000c01804044410301007030f9801c001503280c240b85c1055003440c5206100582d80c8990758001701140038100150080e03851342d113504004104594240020b151001b00c4200109100d440d103070900c01c44200c0c42d80304c00c082001130405c0c000200d40c0032490622054110100580380c01034400d50a00403c610054043c603010000392000e15000d4848031035100300e00600035190341c4004090140d0300d500d8001c1220030041020174843c04d14107020b500c41a00501d101000e1800d202c0341102040150545800400c4070880203c00c11a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 941189550 1250 941188300 941188349
    0x414090c0907030509030a0e060c160e0f070e060304030c0c2c0603030912011b2006060f01030f0b030a0501060806100303050a0f022505010f02030f070605060a030606 73
    0x60300042e042c0340420941c03074240180d94403801682c00600c100316400000e0380050b51810142d800c0781440c94160f8240c03010381481a000e0214030300c11b0600c2100c0d2400095502c030884c5145c41c4c130445d2181c0380e4a15141c1c031030081000551000b40304409100040302428045507500301d411000d40340416203201c0e000540c1c04007a4036189134048008221007404200f260300e4030040b0a0703880f00c0d0015120030411020301d16181e40909580641e01c068921904000400c041e80056903009600581c01c401d005050952a019110711049600340d41040320707101000c840c0c2d4420b0744140d0b00c01d00442400103e42009800081c1020844001a50755a466003828410003000380859a005114513424405442c9076540c068080c0c0120906030040c82600c078111001c0c50300034001c05900e11410411428942c920f0702c00c1c00305039641406100e000440382000c1c4130030076000104582800d00d8420000d0b06240c400e80d2504c01401c4001c1055800ca1840c1200200080e500d024000141c00203101c5d40101c0f4501501c0b00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 941190800 1250 941189550 941189569
    0x3030503150d0507050607150216030f0302090306011a0d09051015080c04021e07050706031a0f103005150105120c19110c060c120304020414090c 64
    0x3880b40c02060034000004500180e11821981c003520b00c10b03100d01d41800c0498a0500541740003030342c02e00000f841440f403c1001200b90159110340c6036005c504014480c100d0481c0510301406401d6406540180055032548044c1c000c00b0821007201442d0201c160241015902004000c95030340d0b01010b50982d88400500030401c0941c2d03407004448400c0d250401e8147e0f190180c505c030a0049500280040180d03400d58842d0300c5240c203032a44d55946144500d4584c1e980c0c4410301c44c1c040080d1500300003900c13840c50745290346440e0034000d190780100e450f00c80400c40101499070603402840701241c00961903001d590301c2e5200002c1e020082103043c2e1500c0314144140ca0004140082c09105c4010412103aa000026900301055039080315010b82d0303034483c80913003500c01c0c0c00d85d960006078000030318540158800702c9000c00c84402d80903500c05043c1c150a020f16030241c01c40010381c40d044201003100004204000d10b5010380018030100389542075000078000408240d9190a00e6002200300c082c0c82e04181250 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 941192050 1250 941190800 941190841
    0x81207020f03150c0c0715121a0105091302120117010c02030906070602130f080109150e0a020d0c120b040203010b0d0b060d03170702061009060308030403051606050103030503 77
    0xf0b03100000e96081d4081c1603250082100c2003524001c01c40d2001041e08100c070402900568003d048039202003080540741c84203200561007002d041a6110862000c1d1884c41e28103214182c44003818040c3e01c90070020f005101c07a203640551a0700b03004061039514010407080c005e241c0b0000f40b1015000b008046030a50b40c410f42c040b41594010040ca5070a80c0b1170714221148140c10100042c0c6600d0150000b404590b5154400078600543e280041181c14066000e01c0000b4881c40254a41064400d10f46040c2e42d03040c41041034540160600307901504010410030303140b51203951759441090f1107072540300941c40c82440030760ba400c1c42c1a0070002142424821401c1200301200c1c4000c1c0e940c01961803845184001701058015800f401b130080c1014003e00000b481220510070312003040c9400080250741e90070844e00c4040c8071a508800144c0c09200e8480d14003960340107000b0526650396510142c50030f13403000d0342e1801240185c224450208043e4456107000e144682e803215aa814040520b01c107500c0324005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 941193300 1250 941192050 941192053
    0x10815010f050603130b160905012105071b200108101707031a0906010506070503120c27030111040f03060c021c03060806011512090c081207020f03 65
    0x40c0141d01409140008440d4129041580c0780c0d140500042d103000304100c02031800505005005a48a184004000040056442101d01a41c4500440710b1420440183c1e0309c0b00301c181d010381c1600d40305401140d400300c028101700c24120361000e100600c840a0640541700c42e003501340c1d602406000e40c0c180072401042403a100410341071900c440140c0040030b12491006511500d9108640041400b24400844d0007807640c00208000148084100004a9400c292406064004511407818009451405030031000450030200036400580c801d01d0054801d215928040c01508510794404c0081040d000242c07030302c0000c020b4000103040c29909018103040c120b1806000501c0b02d0b81000004108503600400d001c2424031901c0d00690414006682e08100c02020040810900d90103401000031140940c0c21540305a903200c0c80b114407000d000d4405000541080011024280290450448140500c1407203020341c0d03607541c0c880e217021032070722542c00d200c4000303d03440c01035140111101d129100141c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 941194550 1250 941193300 941193343
    0x302070801050a05070f0f0e0406060302121006080a052a1c11120a021b16230d02031e15090102040303140d0905030a2706020c01111002030f0108 64
    0x401402140098101c2c03404c201c7d01801c41a01702c0d1099603170780300101d00504200107554543c00300030042c2d0310600b170510b108021400441c042c251100d00790400c4034842e545d15240c0340c480080481c05440040c1502c198080162014103000c602d04694036a44040081c0701070307854104c0821480e014800070001c514492a160514a0000d00c030740407074200701b0140d031100c0312a5403461040e1009000720511000c50301d900c1d6104e120303c994001040305450441d1030101480c0e6a5455981c9488200800d002c14880c3d4034240c80b142c0303814a40310031070110740700605680c076950743c00c8900f00700c0d9000050f0094965010003400d140706c1c201c480c2c1e103030342125012009602d040c2c01e43d14054600e0750450700d1402180c00014044004854941c003403c40c060703101c01038a0361401d1011000744805081301200c8072003001c0c4010200ca2b500c1d4102e110302101d20740d03000b07410880d038043c0043d140368800c1130811000f0b0040e152200701c050600c2c07004501c5012450a0301e40c0325410403441ca8940704540c07003403064641f03612 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 941195800 1250 941194550 941194561
    0x50702091e0703020a0912030e090a1116080d0c020601090c05070f0803060319050c01121a130e190318031104020d060b0c0a17093006040302070801050a05 68
    0x5040090b4401c00504015a0351991000101c919801702d80c400003601d40980ca5880401d07501c40940f003101c580803960a48240c5400d4051400c40e804140180c3e8004010003d1090314804a06201d003214002c00e4401c0c144003558a01800382c031a601c0a02c00140c0041006000d44003003803003001c8100c1542d2500a04165241da01c144070210905000b8243d02e0002c40020031540e001c12910614141c0c2c02c907110258520740ca086c5a49098028043d030128120510a80c4e14003464820320b04048103c84070a114003034501c0600c100402140c0b600c0e0301e125200c030050020424100201d4210000d8214203800e44800c50500a000c4a0464580d040700c150002c07080000c54111120640880c100b02d40041c0c0d54038010700110018000f0382d100d82005600440d0401d90036002181e1140e40c6805003001114020141101170031034402c01d1145580030700e00e03940100c2e03071405828422009d00750341c813505c03440208040c501501d003000840701100181d0202c80c1c00e11200c002801039035001300003640c0c14405070425 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 941197050 1250 941195800 941195851
    0x801020d061707061209140a0c0927350c0106090b03071a2a0f010e0a080d0605060418180f0807050115180b030d080c0304150c05070209 60
    0x340c045480030f0544031b01200085c4002020a008503081e00c4003207411400540c640010524064450300f80d0603460800200210300c0524000450081c4084244110a0f42079451840142e200303d03500c95031405e450a07070001d140d442c8070f03510324540500f0000d64545003030648550035105030380c0103910142e00300001d004640d207000135410b050383c042400c02c070108a80e0030030421281c0201000342040d410419903c02c180c0240740302815604451509542c11803050070100e900b0780d000d00462280c29840201c000001c1114500500000c3c22180000705034aa43e680c00141550030070f030040c810070f0080042185036600c0504c41c2e82138031600600390a03180c40f410b4640241c400d0881c03034013400c0071100040b200d04000c001e501841d030080d03601003480c0c850354841816a82541c4200240100280740141c0d1042c07501e000120a421a42d1980e076180307c0f941d03503600403440b9800140045036100080c04c42041d0504160040c50845580e907030f21542c503280345004005512a011f00111b04401980b0800310b02d2060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 941198300 1250 941197050 941197067
    0x1912050933040b04060b0d0825050303070f02070321021b0f06031509040b010f051f050a18060512011202030a0818031903080c042d0801020d06170706 66
    0x1c11880b181c00c0c2d03990358140b94000c2c086c542e0f03485034400e05c0c1e02213140c10001ca610161181c0700d0355a0030000c0341d610001d5084621851040098240c2d441480040c602c035115500c0051912414416241029aa03070ba5009440f043c2514504191210048071041998104040142c2d0114203e03110054501070020440e503522601130390340600300000005864210a0080203000c4801414070800392803c2c2c1840114100203010741850000781f100e001441d841c3c1490412880760202e00160b03211011b06009035850b5015030124000d00c0800c035120400075030075001d0170004040c10740340c4035030320900c0c0c40c1d201151540580100000240d0100004c000d41c5000a98100250307002c04541c1d9180c012001440d414102451400ea05210340c43c066810074401d50302c282980741c801d48505a80c0c1d142d50007070381c440340158080ca52001594040341954a82c0c440c0703640422072501d64050300d8140e00c850829007642d01003031039000b0068607030108101200780c0680c14041c1da01c221028000301800c003e4014000c51 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 941199550 1250 941198300 941198303
    0x1180302040203040204021c140c0708090904050c030f0d020c18150105090a0305030712030506100e0d060501060203031005030f0a030e042a02160605191205093304 72
    0x40e40032002400b1910b81f81e0440d800240c0a50308500200c03400d107501405402c0303542d007a805191228010541d5002d1030b0050356606c69026800300e0601c802302c0705001e400c200041083d00d0b00e1152049035002514288031002892041c4000b81c455020b040390060729080c000540b16000d0800309079031144030903004c10b80c9a04011440b29001c1d08402800048881e8001c80390320992102031842e00000b0020004000d0061510424a07040a1b90002d04141c048440807070f00240c01411196101e420503220740c03c3c0e500341c014001c0031003081d0142d50315070008442e400d80000f0056803000091016031410080720000400d030031001086c110040002c00c988940e00c1c0301e002810b101c0c00b0614070106503aa6004500c80c889205006001c00d040c52601816a01c035810160b8050301a074090041c00ea504441000e095898a454440c0f4041e42c0b811000c0650b90040d81c002c0070045803a074140c510181a00400d0701580c0ca9900806400451540501209d0100b02d003018a9402c112403100300481c8110940d90f005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 941200800 1250 941199550 941199559
    0x8190503012412021c0513020a03020d030210050f090c03121902030412050706090b0a020601031211060403080a0f0e060a020903120a20030a021c021f06090b01180302 73
    0xa80324690300f0b4a184220400050f11140081840c585085862541c4100c8440d0240144410307212040107411490803602e001c1d4010700b00920a00240c1859801c680f5402e100e8811681c0300c400d6542058115202515107840342c0136000140064010b007003181c03145521040f4090b0000e00c120030018600b512030180e500c1d10a605040301074007424000d00542e4010112000018041d5010307181c11920780d4480d02900010070170754000400c000148405582c1d04030b107150010120740c0d00f592240c400c07044500c100074040100c030401001c4424002d10900e80110300c41d0320390340900e0034020a0320702900c2e00c000c14144c1c09442d1040305103801c6400038040740c100c80380c4040140e4070120800460305000340c1021036070050a0016000500e29800b03007800c250f49182c0521820051508016251a03204d00d02480005a100d690800000d6407894000d03103125180b40115140d4840502c00d014080007200c640035225503850b8000c01585291740036480542409103040b030070091030360410042100c224000607004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 941202050 1250 941200800 941200859
    0x1e050108060d1403090a060c080a03052d22030903080a021e0c041d1005150a180b010314010612020d0203090f0c011d04020f070f0819050301 62
    0x1984510440803502da8010301c02d03012900c455882240d8a0f405603080c10f00402c0c01910020b5038902ca480c950501c6d607801900245000d000042c110060840074190104080d02201c0043c0f00c0500c060702030404560003082e04010b4030301200044025003040500c49506044d42c1c02c800e0003e81e10108007404d407580311301e1041c4c40310480c0ca412450810000c0c2100d620f00496045414158000111b2680e200300850302401594245200c2e80103c000180c858a01d03984160001c90503030384070b50408c60b440040702901c0302d518022800051981070003540800100c48103029107200312405030040040004082c2814013500c4042081d07000008014812202005035031008849001d90715011a000c41d02c010106644a04010108540b03030443c0b41c0c60001c40c0d1007540c45048503540100c480300f51505580b03503000d07518240c4200f404041d620011211102c075004010880014160b500015291b901902aa545075910945c100f181001105003010030b225003070004110f846120a50b00c050140d1040c1200c59 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 941203300 1250 941202050 941202061
    0x906140d09080903070e0f071722060f0902040608010501061b030201150605040527011e05090c0403171606091a19240506160b130201091e050108 64
    0x41c42c1c007a4124240d0f060080e007000140010b11164514040d05000c0d07c1880e450b1511101500c02c004900700905100401d00c00081e902615114004043c04880800c600700180036500d22048a0100b40082d080710b60741e190720000e500f424030905020702101c80003003205504005020348207074150b0780e410020400c5240c00404040c405e4110b8411a1500d07403200c10842d4852a01501030780143c02114003e000e00b200c050348800307085441c0b0f4940381618450a8140e420248a0980e04145100b40040001040300000e65500d540e059140b2070100d80d002946c072135046d89000b5170003089540300e441111405100100300940351407103410290b1780c8114006048200e5180ca08030100c54001860480842101040021102e51103082e20361a407079a4200659420700080403081d82d12201400a55014030205004906003040100301c60f0609200140d8a400305582c3d03078400c1c03503044411a4030001c80c40310803011540c02c5103040000d400d0032036681c1c445000101c0201e10901ca180300f01410014280007254 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 941204550 1250 941203300 941203313
    0x30c070312020408031b0c010c02060904020f220e0103050601091505060a0804020112090804030f031b060606021204051f0e131a0f0d08180a03060c0906140d09 70
    0x1c82480c00095443c0e079590701030181c40360803603846110805401c040a805410020034000e406180507103c03410f00114503001c0c400b480d0071a1040513040341c1e081011030100e4070268080c06c500d094020304030000b00ca2410803a10800c0c000d52002c440380d2101c00c018000a480410058151407094000240d01d800041588141407081d038000d0f0340050000030301c409241d0b03114607180d04c924000e885204101821075180d00455001040c043c1c071101040c00706000045151501c4041d1b1400b0340b50100300d0070802041c0090990381e8540c111205682c0c1c481c20008550103108030b1100c0c4480c121260300782480c1401203a0000000b043c108980e180d50301c40450070601900c0f8002807000040e181010f2a110107403084000c06580e44007a05011421220304154074103100848100c403000b8017030064a10042c3d9810100f5000002c000041007140d6043d41c1880e21080e0f4450011400340d003002c10140840c1c4c0000c0c5c5000b841e600b021003006040401c410b8181e003540d01b114041716440c84005040d045509006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 941205800 1250 941204550 941204567
    0x307030c0c060903050304020a0f060c020607050709060e04050622060f0e10060503010e07061704110916030c09030c140a170307050d0815040504030e03060c040906140303030c0703 79
    0x40000389004240d8081c1030b030017409184074500c2624600300c102d8513904a000131107010312039440040c4180d0071010040c1401030140403a00e03c80c004035000141c4650034801600c006401000840082c5030820050141c10080b49420101c2c20000380060311990a40c40c52003298410068009901c0e40034840b510841d42e80602c0020201c4015241c03004101603d88000c1d02c801d10400b4070030340c205031400c00c69070408034079802102c01c2c90312402d504104d001801c48031064010000e0b01ca00706217003620286600c030b00314041d02c5403a0b20300c40180642c0b6812405000c4800d0b0301d42810801c22618024400144a1307082c1605507034a001030075001c02001400900d4080803038001d60494401102c4032810600004081c01090b40304001743c8103401110384045814a03804c440d0899041c00d000b01851b07540c1440d62103a50403d0007482d20708000d081c483c000c645001400e030383c02d0038002c10004e010085800c2c64801d00014068441c10501c072424003400107a50303030001a000c01045800000e5410406005080740c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 941207050 1250 941205800 941205803
    0x615290c0628060b030a0f060b0901030b0a0806070804030807020604030905120309032a030d08160e041a011b031709160801062306031317181002120307030c0c 70
    0x1440044d4540b8a1403106420076101c016002d402d0002c0c9884080c00c034000e100584820a01c400d0500306002d00441c060007040c201150080f0500d0000b141c01d0206002c2c541c410360180c3c031405075038105031800402d90003004080d401150040c8090200181c0d10500d46011140121040b46031038641202203415486000c1101e50300d480303805044a4114082c039100098003c00300200300314035040400b81611764090a00240002d940070f00080c6d0301a01c1e802c07034640910418a0043c202c68111008102200c3d91400180b0b01d03a0040043c420043d030740090105a9803501c035090646104ca82e0394003170401050007101040e411910400501e07540d01c00c104502d900c0c0c00146d041d0303842c0c2c5e1f9541c01c4603001f000c0600800c100074582c50305401c1085005158103120070340107006603203140d4070b45c40c0c01c46008460f0102182e002c159801003041400e0754030040e081d142c0303c0743c60010340301c1086230400c6a60407080d002c4101703540207a031403010000c041100b682c1d8402d509003030200348400362000854070000c04000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 941208300 1250 941207050 941207131
    0x804020f0a03150c1b03020601090507170403230409141605180f1804030e0603070c020409110909010605010801210f0318060905040f15060c0615290c06 67
    0x5c0f118141030b40000e0490480d00b107a0b10170800c544a40300c0495a11203c1da4009174840007030b50110b00002d01c65038030100e8a60006194204c0a0b484091500d078a82c0140d1101c03020f540c40d02d107540c0c0c540801040c02500480204c0030110b2000d4824030103082c0303014640708200c084202e5a48983c01d500e07101d03642042c0740030050060f9403840d00c41c48000450901510107600085000450081074181001100d000b14003584410b101300445500704400341c03001d00c0e41258091041051aa0341c0c0e2a10710100e0300030804400013180940c18039000422410050380004140340d24820368100e80580d28900b0f070f248a40007040e124031161030381030030307203802c2d030100341088035080000d500166465000d10040280ca030111b80500403190b004401106849042e03552a030069440e01007000150b015140720402c15100301800b182c0c035801d25030803219962082d13000e980d64601c03204001401821201032118055204907000b4103011242200e95903c1d44020013150b00500e00c00c424100000741c0c4840381490245000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 941209550 1250 941208300 941208347
    0x11030909070309120201090503040b1b010f0e0c03010504021813080706020304170307080f0a0e030d061509080703030c030c02060309150612100b060c0d0804020f0a03150c 75
    0x2004005103140b070420b0741d0707004c401090305640c00c0c03040c007404e4441900500254106401c03e00b034010a64010700341001d9507a01220a41c100f00f5080c000e803103a0381d0000c00300041c101c4024113840d06117000c0300c4425210342d16103420040103030744040f021044010202030120465880310703d0900642001c610152010300c0105c0d00d0803c0041c0c0b0380085105520031254044800200c4403100200d020a540d0710f400720300c19400142c0460700c24446240e10a51609020454420007a200c605650200c020080074949449081c07121203401a05070111015901e400140e041c0341004164980041c0c1c0001070030032209038038000501d07114a58808820750010034450b03a0703007452036006541e00f280c2031038002e200380034070000b82c180d280c8228150450343c81d02020700b540210074134800d03000300b685103031603944860709000c581c074224002c01c040480702a0036199810319080c580100b0000621108a152113200406d40600005010800c10303250031503101d0000c2248012040265070111010029002d0240c03e40d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 941210800 1250 941209550 941209561
    0x4060207021215190c020a141606180602030403020d0f1a0903070303060e1005040e12030709060305060301060b0405010f1e0c031814060f1e0301140103090c0611030909 74
    0x100702650107075145a41507904c0c0110882e0040a9410858040000d0f030011129100800c440507844c410503025441601c0d605030308034000440b0f0200e2504820700081813082c844c02002c49600ca480c0240c020340c0000d50130a03240d5800140907251005004050202c0125180e04005450360344005414000380452141d01d00515910764076040648141c0000b070805c0707c00a5810010004a40900032a60307006260504000a20011344034407103030210701d8031581a10000c2c0301d0b01074016602a850760754030050103d180210090650b04003804007071003649441d00800101003050200da04a81c020300740500c0790240d000b4162840d205000c00c0d0690b540340404505803095004000c00c6000f40b280e02c40341c40424000090307100342421030180350880c2211003068002480c1443c06841e40e11001c51065290646409811410401d9107091004283c004801880000803081c03208000403020b180400c0310300d882e070302c4106225000b44195002cac4040c4042c1c6410030342e000d108841300c0a030081c009510700d0500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 941212050 1250 941210800 941210833
    0x1e0d1b05120f0c0d0f0f210218060a231603120b0d0c0504062414070501060609061101090302070e09190c0302040e1c080a02040e04030c05010f0b010503040602070212 73
    0x103500704000040300c070708481e03840c58003400d05030720011601e44844402c60340a4000e817000354000c1c0c9c0c1248851170581c40c000c004d40c0d6075400402142015079907005803152580b03490705000150b000701007032604d0107002070103c80400390754101c0e2a0350140f8008901c82c010003103004c01400b04999154000d04c40d066031800b405140380c3c58100b124001d5404229843e5a913140da08203000f10303000c032401c0085075090708a184e0300c900220310703800b10302c01442460080c07160340309401c448155200c84017158502004003d00b0742c000c03001700304414842c4028040c009096a000303484070054090900c20504001c04900d40020801404144903400c0b01c0c04032140404d82440f54540956100c200d120711308010981c016000e000c941035249055122012071034085001003950010001064103001035800d1100060300b41c001a28540214000d4441200102c61030416509403241c0f98030110320b150412a54040d980da202c41100d40c020340101006846801a1001071403401c9070910300da6040c401c21984c2102c1000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 941213300 1250 941212050 941212067
    0xc02040b1c03030c020c01020c010929030f04032c12030412051c02010b0102071202040b1320040f0b0c0102130e070201270b091e0d1b05120f0c0d 64
    0x31503000c90303890518986c012a41c2d00204194a8001000e40604000c00a295640d100c9031004108420026881c6d0202d104902c0c0c004176a500d04252003030f0280003e040e000b03048c041d0301b888482044150655210740003035801c072032784240e5405007200050071410003109100f60350181440118584412405040466403800e42140d02902e4a60386e014440031640144101c404003481130300900b01240c50b240c540320680b001d0f440161303081074480ca9403584541da058040003c510a5240c00200a0750141020a000d0605803a80918141c200070512440d022020783e074003101c1d200c1c07000942e2954090240d80c0a802035410107044806141000324062003000c01240c41070200b0f50080100803120fa1a03000da40c6850204100e01d400988030b15808190f99040c1258800c0c0510100c4086000300010442210800711580b0b5080d002001d0b590312056010202901c070700c140140d0650041c050340c494070b0302d078a0b850728100d250010000f0b920500c1c0803000c3c103030b501140c0c03000c0c29544c1b24041411301900404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 941214550 1250 941213300 941213321
    0x320303070306030b15010206161b0b070e040902030606060d090209010609050312040b0412030216081b0d05060c090d0b010803042409031209330903030c02040b1c0303 73
    0x642d07103c0090307105c43c2603400000c1d400704141e00a040035115200007440b840c08100314041049003c3e007819100c20348803d10301c0080380c45856950014600307010010400c0719000340d020301c60390625110f0009a070340020040d812000858049a60300c42e6121184021715907020700039000101c010000445070741000445007190701c00e900b50384c1d1030001ba015001c00e41c4118080c035105100148424468042095050324807a482801100e9184451080c22402c02c0b200790320a403044e912a9205a025035600103482c4100c050560348007004040703d90f2900e80324100240410460400403640e1802913407600b06408803140c100c880420196111030b0015101d134030234025500840144074000d4070706100d0f03440003103000c841640c4881801d4103641e078000ba40c1045091440070480c103031001243e554040501c10900c50700800030b4807014103e403102010040703901c002000900213580340401c04260441d20000c452035045800240d010915070004078965598140c50161002c400000010103815500020081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 941215800 1250 941214550 941214563
    0x10050414011b0207031212050a050603070501021204120f0b07050301031205030103030e0907141201051f1b020a0f06030e0c190501080c0c0a0c0608090a32030307030603 74
    0x10407030710090b000762840303000703001e00181e020b5034041010400e20140f400440349a40352158039114800e000e40e0a940c4146c0e260489503039070b50240072507858100b0114008010a00150000b034106000660b0035001300c1c42544100310f0580e010200700040c3c4d000e001841a44244004901e040030080101150024001100c0000c0318081c0b2000060007a41034a04980e03140e5a1561407546100501c082c40748017415010600940b0302e95401ca405980000d00003c40103006291499854a0100000b024088086038161031850076500384a681c010000c2e0800504080a5446800380d480844c0e090891540054081c80075200c002c1142a4582c01071004203030a2011510b1100e050340c1040001001060194104041c0c641c0401903540a070304400d07804040c86501500b01074041ca4034078100302c2d620500300c520b20441441482615080502144c202c41c10400500c152800be503207003103100300941602c000c2280d680001110120021400c0d1030301e56071400070380340c80f801d1441e0040d020348400d00048444 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 941217050 1250 941215800 941215811
    0x5060f010b070b01030807030c05010606020a1106030709060c0c090c0906031505060301090c030e0d02030a120c0e1c150e24060609150f1b03090d0b091005041401 71
    0x261484007510b00c0c1d560414a00140c691841e912501c550348000310490901c4040041d0f1030201d0400e1150343c3c010040368014000d2100a4a00400000c43c10401d0912500c414014003900c554004a40000c0c0c0320b0718200a0580c00c0d0a0500c140c454455610035a0300b982400c0004c0dc0856221041e4002c5a2894030240401d101c21f180c00880c80209000e6240c000710141f00406c4449000e4011f50149a01c0c0d0800080ca401e21290403428603140c901440e0250f403000039000009039110a014a4000c800901040a0658607000610a5400d481c00c180300360350034560b40801c050006080c00b031195100b0b0901c2c10301c441d8220380a01801042c0140302c03c1f4040c810400307101d0301c0d901c0c00541143c0c000d1544515155603c2701008440e070852503056800481005100504041c20070007080c90110481316a070700c50f071449281c5201d015040c42100c61030380050240c05101d4540e4110b010703020358003102002240e44c0d448101450f0040203c4c0100c0c000741082c040c4814890500c800c0c02c2c404200c807000b0f100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 941218300 1250 941217050 941217059
    0x1204211d040b0d080f040b0403050102070b0f010f0608100b1204050f0a0305071b05060409022206020a2004060605040305070e060a030605071704050114061005070602030603071205060f01 82
    0x21910890b4149800c000c1148040c40000c000070000d10b41007200141d2503007400d4485140c5881a04290801c13501c0360750002c1d0940510950340d1401d5172014501000300203560500c800009045218801c1e5401e010003500401d196074040c0040401402841100702d890b07110f00f0003500c034651001c0e1825112800395480c0a0303604480031034121300e5513825888080ca07080d8555210114880c4209425175850040e90011410b580c852000388011302d6038031409a06c0b0201c0101070081d2024503010a00d5140d07450104000443e004035a1049964020080212500302c60071a0080c04e201c583c1031b40e60040c6001000b1401c40c0d00a400781003900e00070070031a10156140c10358140c1e1400300780c03030407548a00092410000140d85030000c95010307001740f0b045024041d0f903a4a4000845c01504c3c00c480d1a51100d1202a102a22003104c0c1c0c1e01c400c0444402017100102c0d8806400d512441c1000b5098540000008085032001c2002c0001010f1048030360b09182c2035401c0c0180c80e11800e482c650344501a1070000078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 941219550 1250 941218300 941218309
    0x405070807141e030a0b030f0d082802090103060f0f090f110f0703030b0306010e060f010e0f04150509040b010f2405090f131b050c031204211d 63
    0x29000450a01003c1088016081c801803540006085030249500c4401800154809222141c40142e00c4802007d56619108000d48011002420800c00700408445601e8040107102c02d4100c464081d000140d44055010048000c1c0202e41c006422451903207400142960300b204140c403c81e07600c12020455000b130806c8070782c00e8a000b0400d103003003140248860107244000400038540a480303400e0001c0c0021a000c0800e0400809070f00c030740312001000c0e04000450030b1085070205101b82c00d2070f14409401c00c000c0090007180031001914042d995a40241044070035400b0b9840c098007009000d16200d18091800c010b00c04424042c208003071001d0302001600042c0c05064880407101c03000c00714000d1100c49000c4030740d80c004032043c0b5400601a148200592500e060483c520002c4400105005218981200140021000c090100030007000302c6a0113600110580e001c0c01c0700110304a031a6225810b100c61500005a9060420b44c2000c288140c01d40c0c00030740401c0341011000b01a56098030040400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 941220800 1250 941219550 941219557
    0x180506071106160f0903050f010902010921030e033901020d09030b04240b010206090a2102070e0f01050f0d02060a030e030c0a1b05041b030b0609040507080714 70
    0x14104100030003003d14070280507244040c0989000d203002050503a480d1a40d51410310440c1c0c98200c6a55105680b1065507444229030000d80181031034481c20f0a100c6440266075600604060104031101070500065a424420501d0001e40700d4103040c0610203142d00614454040351000c81080e207142c503940f10a5002054020486425841e003000d01c0b80340d51104441c8500042c800c86080f210300740700303280c200403490403120030012041001a03540c000304006483d00c0070141c441102640f282007010001a60142c04117508400078507408602c0240e024207902d480190b0300006004400c81c0108001e24820140300e6040f60022614072408484410034000c040071400310203504035008003ccc2e012540d010740c204661840d02407080b00d280a40c0d400c4054101078800c0340032100c17000ca0034064000f403040450760034040c0030100d0341040310308240c907182841c040910980f00c040c03589172180303a00103640300e00c10303240d2204011b00240f040d45400e290051150500300d402101245458001040340380c8920700f42c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 941222050 1250 941220800 941220811
    0x102040512070e01050d1a04050106030b09031314030c0418020913052b0e030a0209010f0f1a1e0d05010906081510090e03160803160509090f04020103180506071106 72
    0x440d007c50441104204000c10079074041d03413920000400206002102489a449200903644881381c0342426102c1e81c102d40c0c002d0314000102d01549000b40d8010840340c3c4095412200000c1c104074050055554841c030010103988000b9150822424540c01c0c0c11000805202d102900c0fa51600d90a04501200380401c0907a003008188a02d440b0f503e002c0e012400701d0a070f000f0122a04d2800d03690000340400c100f41c0001c85400c00003a02000308440031220400034102641280420662018492409000300030441100901c001049a094100081201c104040409003400300f90707100c02c10000600b289114840c00340c82600540c502e11a44030b003081340201c0d00d2203c4034040614005889024010103088003855002c10080c0a50707030041180c1030701d1400d01c2041c89030f8481c9002003040501d4059054010140b240411440d20903545101c4290347c07009071085160081d45070350004074010030300d0300004428900001b0206040c810001640d0744244103940e0350015039200c141003161200b505481 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 941223300 1250 941222050 941222063
    0x1e07080703050714010504150e0a1e1b03060902120303040f0b1801050a23010b031b0d0e10150302060304060506030a08190e040218120102040512070e01050d 69
    0x40e000080c8201c0092007428015042d411018558103482070840d141514100d8a01382d000703003000035594450042c0c903188042c00c000b5002c8007440d031700d40c18011007102036498800342005061030104401d41e15901581214000e0018095407a441c0000c020482c0840030f03807082e1401d1520541c07d00380041124891940f010080510003443e03a254010b14102414406040c3c00c0414640c24a19007403048512030362007060b000c1004003440e00b4682041240d0480030907100454001070103036520000850340c001d402014100007036200c088124001d400350049805040d0b05048401c2c411840010342031840c0441c890007004100001204040d11044a100083d0801001d00c0050b011905aa01c034581c09603002c2c09850b20407180790703a481c506610041010305400c04803145841c1041e4040c110080c61081a2011440c0100901e181880e54207402801885000108090305619100790103071001410017400010142c9156034080d51140038502500e0032900c206000014503103822280d01854039080311 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 941224550 1250 941223300 941223307
    0x105010e0124120c051c06060512060a0314060a0c0305132004060b192a0f0b0709052b0206130e010b03060f010206040c06200706051e0708 61
    0x346140d552640b00e050000c02895000745200500036000c084019603902599420030a14544894800d400410605841c103003045c851103801100700c0f1801403141400b0451940c8007400940d0014054200030544802d280301c034003c1c11310000e045030003941c580c50140944850810304904813007003103401140b80d80d0381403615008261410b564030100440b00f44c001002c0710114010400b5141ca95120381d07560f400025016044030401b0325040c01c01107040c50410450294181e80240a444d00c0c03580d20381044520255208002400c9416018264000303000d03096450b040c1e101800000551044a0040c862403042c0c5c031801140c4c8030b0042100c000321a0305604001640c00b84002a0000001c8100704540c450002c075001c0782c1a66998020403a0303202056aa14041040c04072804041100505542c400001d00c000501002d135890f00351251031030520a09a030503401d1500c0c038800010015143c0c092003c000c202954000010700b03101844961a000b428a030712007420984c07140c084054a019400d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 941225800 1250 941224550 941224589
    0x14090a0320070e01060c0510151a09030d03051012021e21070302040b041b0f020c0d0b070806010c120806041b031a100c0f021c11030105010e01 63
    0x1045640440c4041c0c404640344540ca8035500c1d5100c1a00382c010304049800750365000c04000e02007121000515000300306001c09500404660241246802140b484090104501c2d5240d805030f0b06603000d18200904079019a425494050024002a2050800910460404580d00d48004641c2c0c904c1c82d406450410108503494860210034044289140c0c01801c84400e905801c41034030300d21903142d400300064140c1514510400040f600000e043d1390165040c02d08810248242850301001141941064100800c00603801c81c200042501e100d0781c4039581c0500d22003404851010148940203940b40d0a0b1710341c5a040041d20200070b0b1040043c0030032042003045494500c501825500840041c0000c01c5c8815a040c296940c01ca9440c00140041d9903141d204000d40030580c190305c080b139030a07100e007550000c65038001411640c01283c080c1a040d01c002d00340c070840d2100c20f1031640d040d80c04408003240c16a01d1500240d0002610505442582402d00204111112005040c1224035200400e014070200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 941227050 1250 941225800 941225837
    0x60f07050a241a09061906020105090c0a0b091003060f0305060105090106020f0601230d051c0f05070204050c09180106112d0106030b0108070302030f1207170d0f14090a03 75
    0xb88581c2d00800c0903452106c0802c9010032140182009400114861410700c120f140303405407180c0b641d446000c241e1030400c050801c0c8401c4941070345c4d0035215080d01030070300001a8040c241a50151415018440c0c0c00002d00c040440d100e410f8030710458585840b6640e131070040341c0d100c4000f03140e0046900a40c0040042d4020381140c903001d52120b091000140910384000b901503408140d05680c0754108080c40b4100c81d40d00700c6141d4400c1c0d244c2c28100000448032034010b08501801400a020380d81e94030228010094003012398680580007040044182d00084981e12400320a00c918030204442c015404401d00c80812107482c0006047c411001940c80189220320410700804421025561180c1c00f0010940320900c3d01c4c041c01c0b1300310041424a16501c18036203010100e240e03500325504969031200a1100802c100c1c0c41c003a400c6264850380300801d5002d00301d81c0c42001b8080c1d004910381000700070301c99800d801c06c1c014a0700e0031403610b00c0da6031103422a0387c03200c0c1041c0004002500814000307071784502 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 941228300 1250 941227050 941227069
    0x14070c0515150d03030b150901020d0903050706120e030f04210f03051b0f010b030709090b01090c022506080a0c0e191e030209160905060f07050a241a 66
    0xa18020035149100c00210309000d003194030040d141d40703000441023515601000010362000051034000c0034a032642e2512602c070034090042000708207404880090500302c5410405c101580d47c1c054076a00c4100d40c541c40d5065000e0711034401070320507000d0100240c40ea0f0055a0340c6184e000f40400c0120166130b60102ca8503070148810009412818454034201e81081000d00c03249006c51000061002c0c00000f011f1800c41c40340d01220a65060224200004114400030390450b008214042546801c204d41681070044404a601048a4880e200c6020480e2002503004070b86c0b1a803a031030003a0b120020401d054a010700c0080d804117135170142884050806140d4503140c02c500300f0b040c441c0781d6143c1c518074210740c115050041e0552542c0c5014810340c42c041607055045460b101c001c0034401c030081005030501406104480c85080007181e5442c00c500d0400031190001c1e8008140d60b0078600c14078105070203114051306c2e00c4402803102d04c5201c00c080340c2d00c500c030781021800030100c07440b8140c001001030405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 941229550 1250 941228300 941228303
    0x3060b060c031204171305040b0d030917031c140c0403031d06221d102706080318030105190207110306071d1c080a020114070c0515150d 60
    0x280a01822100030725200a40091b0118180100030245094200016514403001141c8150031680d20200002d8100004c403041b40c3c01a07001d1402c5410344d6005a007540208010b000030400712685020300c05c0d9480e4440e48264015800d008034070303281c2072883d4a140c000e90000030080f84803010034020b0b45182c9690304400b40c1c4000d00091030414002800d24070700340d12044050410309041400d21643c0c070008a82807910001000f0200c3c00e2a01c004990b000c1d0f8002e1050500030204c83ca02c4035420b10b0750349040d1802d02d425010910469030340e42d60241c0d03aa4440e0700c11105480b01c0d4003c049141c6410b01406000e00b2030480600d1705012a000c00b04000d5010600460702d15400321380c030300c1c0d15880c28402d561040c1075584920b1030087c0c2d4030f07074111020b40d11500c904e8403801e80d07400c05103283c01460180904158011400d1519070402000590050040100301c0901c500c00004001217542d105100e2407205200c0d00540d00d14928802560300c4a210a42d24080c02c080880041b074001d0820580407a50b45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 941230800 1250 941229550 941229563
    0x14150a050603070803041205100e0a080714011d0c09090601090e1606031d0c01021c030b12030c15010f1e090f0501140108070807050c01060e1003060b060c031204 71
    0x1c658480e116403850340551f000003000750441c00a101400014003119000d41c0d400300d400d00107817503e00e1a050b02c4800c051001840d594020405e00188458a03a003e03005440300e800800408110390012100c498a5a400b030340769204140324441c16050100f803e0f03018104100062101d0307401c01c4409800340040c0c000c00034892080c4031034200c11468140f85c1708014085a100000c1101e80d007030752840740c150f8588054130281e0040540c41d1a50343d000a01a0200611070300c1400a02e10b80311040300504581c3c3c0140303a100da81e42d01c001d09c103004080000c0c0000d0080320200c40440e04600204a09030b00e00344640401c0b00100a4200100c100340c0400e0003170000c0015100903482d484a60032000c0391400318080707109560b08d00041c0701501c40300d50086104030003404c00009a107007648006010300340007481d034070400a000ca0b031500449000d421040280000d001c001c00075280c040c3c1104c402841c1d0344420382d083c50811100318150b007000c0741254444840d040207140b82503074088986100400180049808 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 941232050 1250 941230800 941230813
    0x506010203091f02101409060c130b180405190b0d051f0e030406030905120708070213021c09060612030c0f053903010204050f04152114150a050603 65
    0xc2d590b00b032050384250444140c2a07061400d011f105203250100080c6680c81c642420080065505900d280c800211405001900c0e07a940300311181901d80d031800c204203900103081034140500a016580840030500f80d9540401502412404008250803448409000c94005041c01c1d0300b004000644030100500b41e44000c9400c6d207800c01c4252541c0d1296000100180da00c070346150800030103101041c59036501c14030b040d0070140240c440b4030a0f885850002031080e8000d010f04401c021054043e075148200d14000c80304072900f226004009050311200c200c0e03010745030442c0820b4006100c07030011809a01941c440546012036902d0400184031000c05607594072480c03c001c920100c04009480c41441c104100410301041d5100d0044415884a1000e100c0d0340140414000c94595005464181d042100d0101312a48000d15280400e60396070489488400c000100250002416010b0b09510780f0900c88003a50780c40011006450f12400b10046d000040e20f18041210442260080c5070810700041c10780da0b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 941233300 1250 941232050 941232073
    0x80621010e0607211b0c03090503060a0c17040f201f030e010b0f01032d020306090c0702100507021c150e0105010b04090509160807090506010203091f02 67
    0x24106003101e01100040c1a1114060b103104a842030296102da801c0b0103010b405800d803171121310880506006404c0152020a00c420f00d8454503009004110141c10303202c00d03081002c5060080d00b841b014940208040380502d0380b02100843c100c503c03942d08641c0d41c008040441d541d04030512152140c00040321b0306030b40d00c030000350345001c1c5200200d0003044800c9411200c1003c003409442144051030000d0745003054207405a12690002c1c10300c41c00918001890b002c000130301c01c001400031820342e5001c801d0f110b480000d404d05540214083e11080300c0c0450369645d81c004148441c131032404020b4000d034120001c018803601178405400400c0c8020500350b880305182c1c81d241030040e0084003d480d641004091008810071510030501c60030303900c400038041c1d5810228504d04500c01c0f81301e03482d030050b910000542086428440821405007040c0001c0c0d82580d00d404050303984545005503011a45800041405d40d8000812142c01b0f89014080e040359550002d549902c0009868a201c1035000d030304d06095 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 941234550 1250 941233300 941233303
    0xf0f0604060b0d15091502090d0b091f1a030a08070303150b070b04150603020904080a0e13020d0612030804020904021f020f070803130b030c0f040e0a0c080621010e 72
    0x1001c139140716000055844841c1045400700411000f941110f40c8104207019070358507001c1d845e50b44240c12050030f088a480794100340f03262400146480100784035006480714024410b07040020f00c0030504a051007040350f04410151104c2c2e140d8801040c20408009a0300041d000741c201f03030184c0a10480c00069030380d556a400e14607510602003210410f15030390801c010040030f01d4800f400100040020000303641168003049c40d003200580090b040080c0441c2100301288100c0030380485c40340c0581401141c4501c2c50700c43c40603401c1007000310a460300388000441c1101c0c40f00f034001e0105416507903035402032b19142c00740701c0301502c0944142e800913524280400854800a0a442001c440354000c0094041281e0000d0810605030405000703500200b000d5151521681030040a507031800c454a46d50b230300c0c2d8000701c150501c80c16220300303a070180201c1c0c0080e000e44202040c034400d4150b101c003400205d040001c02c840090044850550042900c144ea00c00385022034202c4549601e824000070f001460501c0d800e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 941235800 1250 941234550 941234573
    0x708031e1318060b030903040b180a031406010b091e0a080d09030519050a02060d2a08090c100f020316060b120a030f0c030509210f0f0604060b0d 64
    0x2401c1d0000d80c2d442084140c5209070030040c415506110b08604141180c2c1ea101d21a610814600082c0855519007018092001500c0c8100040c24207407010350b03a190903c0d00400080d54550b00d40201400012142c4403402102d50058009011484d51442d1028699a41c60502c407855001440c96401040e02017081142c060046143c1c1c9410740f03214a50310300036181036580c90b101c010719844030f50540002107000500c2800c20740d0440d400b64540c407090f1862401081ca40400002d03110380c038000364480c5000c010903070232100c1e000d039544003050b55082805a80d400603c5040c581089100113218038552141a4189003000c0920540c0d01e8104d09284840c0f10400c4524107072803095039104030200740c5c03811406881031010380c94050300621440b518060001405001d5071130034041c01c0d54002d020144030300d0845011400042042001504c0d8000e85560070320b1f0080419024819000d2115807400c00161281d54601d08000601650303885a8681d006014090708460300b00080a8944002541a00d40b2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 941237050 1250 941235800 941235809
    0x30827060a0614060414060304151e1a03101e02030c090f01090303140d1113030618021f02070515030601200d21090f0506090708031e13 60
    0x800d225040400705041c03d082c03205824480e280404c0104029512465602102c1c40100e4445440e0358550400702e00080c42c100f402002c0354507140c00e5143d078400c94210410181d0000a0402103581c05a2400a481040020b0f49502d540100300340320100841c1d401000152180d80e01900ca02c4880c1002642a80c00c01e0f12018003881c804144d10440b400c2c0f29401040c003140034600105154034544010b0710120054025600010001440003110038864201c01c580a02c9070009590354903113700f50744424017280c0000c407a42401c00c089100010f45040c2c0d541715150b0018007104050001c0d40c10114400d0315080c4903400d5014450000a9507038940c00014141d07180d00002d51303903c1c9441400101003854141010151800d034003c0031030740020003e1100c90210540c24402e000b120519210520001d0800316031a9240c2000074100400c075040081c0250148a0f0003101c6060b2200000e0544918450003444100e1b40240401e200740c605410302c911294407a0481640340c410b6501c108401e44066800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 941238300 1250 941237050 941237071
    0x1204030e0406030f29011701020403171201090614060c010615020f070905190b040902040e160506181e06120f1303020c100e10020a050f030703082706 66
    0x2140d00501c50001c00c40d0382c820308050b100d0b505c444144200c07000c2d520410300035054050180f0310f1741e440c030840941c1214061030300030720003003010102701100c03a44544c404003210090741d0b8040300009000415016460076031303c1040044043c0140d150a20050707030070060201c5c00c1d664807a6800180424861060000c184456001c1c00c3c840e40707826605403800f801a03000c401424a40000c114025942400446c518007070948085905107841000401410150101940c81481c1c02007007110003000282d180c01c0c04842502c9400420368074010403802e401365071415540005031072081c01052400c1000c00c0414240c0d0020750701500c00100110380e2076080585401030f2400540c0030f01030b14804460b801c0794092480178200222940c030350b400075110f80d20440ac40380290880004152094022a820340e160380c009000c904c220050320f4402540c40f58108c030151100d000c4c20b55840900382e00402110704054242d00c81480071349545082e1a646079200124501d848540d1043d03080604003806418012651717081d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 941239550 1250 941238300 941238323
    0x190504051f150c08070614070216141c020112020f070201081303020717010b0301090602030f011e06050703030b121608070f090f02040308040612201204030e040603 72
    0x150000407a4510341040080d5039061000c0c40000e5846448840256808400c5944a42281c90018007a010014020f0000360b148402c005565500103109400d102642c00c541410075a1050522403001e410380d17101e50405440c562100020608101c0492200d00c1850070107034120020a420040740c100348c58600c045480060290295a03124003920f0300503c40c0300700c070000d800466902030b54500042c81582c10f00c1a804441000f40502940700400d080c101500a1100e00d80d41c0c60110001d500450b081c140c2d400c11040085003648000122800b10b0001c4208081c4a500b0400c081c0d645410285c002c40c101510750303019800703a8a501c580c0b8001848400c00401d00b58003a800d01840c0005a40c210206640c040c8008200c6003410740c0d40501211070510300000c18507a6a00720310041d1185420140c18244001400205140c1c09107051840501e030640400901aa811000c0b14503001c00000c0c214140c0b0505c91502040c0341350300c0c01c40d0824824103060090840c2c050218050700c2183c2c0c0181c65100914 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 941240800 1250 941239550 941239591
    0x5070e010e2b030e0a05014b180f0b040b0705030d06080c01030e060606121306140f06030a0209012105010609090312181e1709030c180619050405 64
    0x6000c024046c141c05d092154a00c1c1c2003d051107c20358001d4403004030003022a8410034840800000c031800d61700c0b0035940c02e000400140c00900001c001d41c007075a035030003c542000240001d07044868000e5650b50044585003915141012890784c00003c820b40302030201308142044985603104030f0005010f004003400f410344000001604440c0511042201500b00d4010440a0b6a403142200c00d614801c2254401c0b581740d091010402c458001d20081505250507408a070100328000c00070710aa9440401c11859942c00c42423548900070241c0094100001c640140a441c0980035800329030000724114045c4600e0584810782510038079800380740025a01c00f41901419841034220b11040c0c0110001d101e500440c0861100000c1c200401520b1a681c5450440c1030025a00880c1c038000c1d042a10031480745001c2028003096406510018824422000b07003a041f0700b00003100301c1c6206005040480c680c1d44140920038030160362800c0c0c4008000f29900450300d03907203611503a400b8400e1400c00b0001c0700011f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 941242050 1250 941240800 941240809
    0x706030f0506180c07080910020a0209090a05060c0309030706110409180c0e0c1b010b12010c090501120e0102070b010905330f0d0b0a05070e010e2b030e 67
    0x1e82094010748183c1001c521071540d4503041034000320b603082c2145e501c43c003904281c20340d400780b4404a81c0c0842ca10000c1c0b00701030340c0000c1c4152814000c84030709405442d6401819581c1401a0004040b0713005503000620008000020710381c0150a03c0c2541d180120300e980d000201c400071802c0481102c1301060502c0040f00920400e440452405c0046021007415103411f584080c403840f034219104e0410000558001d411401d541103c154140c8468804030300c0705015000e04400300906d40200010000c2d00303201401402588500b02d0951102410035050000450307120a1001e0283d40c8a03840d0a40403100031400d200a200c07044c0503200e9114030754104001da0080d00d8024140d081051100300100051402c445006850030012030b9805851900303190214091201141c0d02d00d0380a502078490f4020300603c1d202503403040e40e08040421107651044404d5891002403d80980001d007115568a0141407642d80490500e00a02c022002d01011880c90340c002590030034100d0002c1c034421030701e0009040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 941243300 1250 941242050 941242061
    0xc0603050c0f070b0a180c0303140f030a0c210506030f1501060507030905152113080319150609050109150806041506022413080c01020c0706030f 64
    0x541c0c2003058500401d4101d20403290207003c070301608040101c4003143c0180c43c540d002e0344040c200349010303808078507060030105c410000300c2c80180c000c2120006401e007001c61040480f840102904031132420b640300d800040000340050b80f13000e410f200100c4103005511101040d14a419800c9007004141841d01c0e005142c18003001d08040001503100701c1070307520a0282040c2c01415903516151090f01c0f054641400c4035014041c0c2e200e50740040b0106030805480381914000d02310b07030102c100c01407a209641d4203070000d152001c644003000303095072000c00c0c1c0c0000c82c5440115049403005400d40c82e40e4500c00702d80c500b25105030b80414a55412843d00b0400590010b020134020300c0c003402d010549503d4044d0f103000070010f0b038450030f0800010390009125079459500c504141240c2180212815856101c041e44d6140c05a1b2102d2510b0b034500c41c40320011206100c803030b10944c030214001e03400c0d41140d82c40c0c52080c0c2040b6040d150030354080c40880180e4008000004c0105110746c0d000c58010740c0a40072008442 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 941244550 1250 941243300 941243311
    0x617010b03070e060907050a090911030f1305030d0207170a021f0203070e01050a1b0b0a1401030f0303020a110f0a06060e06150a050d05270303090a0308130209040c060305 75
    0x285904100307185c0d6840c1e0182d5880700450520b241d6400c403500007201c1100c41c942080c0b9010703240400f603000100d000c002451103031501042c40c071469220310909424082c0b5a0701e00400542c4100501d01240d241c030f4010703002b450f10403036480d040b080c608415402a40c10207019030005a05c00608860324040750b035180f00c0d182610200451440c04c06440041c03c051003c000b00c0d040c440006498502c091261440241d10314504405e02a24900b03890000360900c01640c803022880e080450844400301008042c3e412640c1c041c0c808118070161382c0e820340c0690802c114150521140c034116260f144414002040c46120001c0584506481441e1901c00c17039155402881440001078100411502c5d001c56007940184460800303030f182d0080c880100d0303481c4555404105128142403c2c424000301c0044120090740c41080c903caa0004000c00c025602e010403903204040380e00008544021034003468446802004144011440382c2c602d0300440c141d40d8055504460b0301031409403c1102d294584100c60b00071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 941245800 1250 941244550 941244569
    0x21309051c0c030305070509060a03060501020d17010e060a0305060a06150e100e06130602073305030604151e0501110a14010605030601030309090f0c0804080d0617010b0307 76
    0x30021030340081007091010b00040505650314041900741d4000c40a54510301e4002309919992455404024094440d0b0700c64079025104030b1108540d018010381600c405d080d1115035a20031680b078009800038921020b8040c6410403140000840441c005000007485080440400300e840c80c6011008200708030007050709020442c0300c031261916507a8683d000c4080101520300b55042d40340610000d40075200b201c480f6000090a2032001a03101e80100c2e0a2007100d03000c0c0440746c1c0914028041c400005004000100101d660044a035007190260b03014540001010700000340141e42200c2601c2c0100b91500034103007440110f8034440c030280d80002c4c4040503010078a40002002c86590b1600da41e0820040018018148190400f10250095201400524000f0201c904659403824041d020840e5401071024027410105007641d41112401440904095a69186040e94440d111901d10b5003003030242102054444500088a000905121041c0030b41c03c00002900a041c02c10180b624200f43e0010510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 941247050 1250 941245800 941245843
    0x6090d0905090109090203100507260c03010e0403090504050406060e18281b080607020c0a090c020c190f060c05120307110a06090b011710020d0902130905 68
    0x59103070041d15a0440b100318502203070903405c0c0d10009081c00c1c45001442901c6252904010401d41c3c8084d8410506080195201814800c04001c03d5a071404940d070380d209034001c100400500307d0030380013558040d01900d8024881529a000102074a00a44094940d117885820900c40b0880e20305d921608000c1d01d112b074010b5805800f03061a1a401010442042d111039860042071403080340201c201016480201248054014a00d2810f030241c00e000301941ea1044030005040345000080ca03614460004001902041c03a0500442c0980906051001140290311035a840c988420401c8c1c0c16140c82e42c4000c4042710300340440c050360105564880340030084102c040780007080c0c0201d04485100e1480081e5a81d0303545440301034400410032180e0300c07107505c50080c50b50203012856212044482c4111480e01442c2d98404400172009102181c2902980004807040c1c9003105940c01041c0300702d9100380204000d0550f0f00022400003408002c0c4013915250b640c80d204101060101405940c14881c47d4403d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 941248300 1250 941247050 941247059
    0x6050403051206190306020d02040815090105102409031208150114030f15060a0f02160b0a1110110c1c0c1205070602030406091403091e060d060806090d09 68
    0xb0214a01c0080c2c50a40c0c000b601c0c503004c0603650114ad0203803160340c0448003038950f128481e024028045800c0b1850354070b4040451191800c110000c8221100c0500101c644000a000005039191006d4080180411034500100007140481804124021303034903034400c3c6107440b0140b07c0d08080403080403030410006441150340003081c1400e607a04000e41c0e444030303816507a41154401c516134290784240c5e4001000b18030103c0e400c2d401342c03002040004903401e40c3c460300340890800030340410398000e56140316000c5c44403070070b03440c45080f076001210125011544601051540b00c03040f500c80000c17428030100b0025142d1b41e442001c01c034184001d0710140403201d040300c3c1a00001d2242c00200f00040420500a2000115034401d409840e01181c12407002c42d40c1781803525280c0010a40c0321000c441d001c3c00804410950f000100680b20301660107084d50b2030084003162640c468111044085a116005010088102c485849210007400d2102c0060182d0704200007610b00c0c11506081d804100f004401c010720 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 941249550 1250 941248300 941248339
    0x1c090b011712031902070b010f050a0b0417010902040e0c09090312010b0f0c10050405011527150803070c0b0f040501111009060203060f01030504080a0e0d06050403051206 75
    0x103860300c0000d04403c1d103a03160074a070800300701d0341c10100846890012039003d09228107051410304a412440150b4030899445040c491405c00a03c1100d0064000780410030180c50205035030206000c0120002030107007001d0f80041c0807600f940303154614550007a400c648260402d80c2680b6045510900114180510741c0080118040140280c440540c8045107101d298001e04060780c88603110392041c0c860042d010007a0340001c000031901540d256003080c9800e1b4100a0300100705060700c0f05104400102040a40c1c0040708803140c90403c0b16440ea61121316103a071200020110241c010f200140d0765072407941c2442005410705c1d401c40b908000c0e040048410f81030000c1c0448040329828200343c48081004000300e0b0820fa0034086c1c800701d003414203505000b040030950046224410807200520080603101c011000c0300c004590083c00a01c00300204041c95000c1c40364410900d00c001c26401115819607186026035106650480104401150041080401c02e000c603502079001d44007418503200c07441465 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 941250800 1250 941249550 941249563
    0x10f020307020d08090a0308161109060901060e030f0a050a0209061f0c031422150c0b090102070f030f03060501110d0806040f0212190506061903021c090b0117 70
    0x1044a040007461441c90b8071511001401160423483c1140c65013030400c0500074030907070000102c841045034842d1241070724000c0841802680090510f59103a03091100680b1418031904c1ca4a500d88135100e80c00080210410802000c40d2145e0040c0034030390002d1040c40781484010301003900c030b065600c56080380301401d00351080100226142c1030024600b00c2c202650b4203030300780c884100014070001e105643c48040c050521381d56040300c003045074810742d103030000d08000324011804000140c001001801051580c03180640280d0400c00040c5490314940d642041500030007011008508651300c50802d0316098070404008101c28200074070007000d054140c84d1103900010400e0305005510004c15601d0301c1d036600040098078031a10456880d10602d1110345503100440701c0101e02154030100741c40208407401001e0080c032010303080501f05082c0d10172880107054403000040815900b840018000300d580c0d101d1014000c941c00000582c00308c103003400c01550405802905c1010501040740c01c80000002da903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 941252050 1250 941250800 941250803
    0x11e06050108044e090501090603021b06100f0b0301031e03230706061e05061606090b09010f0912031d01090809090a110d050408091e010f020307020d 66
    0x144030804014410309020316881444280c0c04c1c1e800040400c0b600f1040944503400c440b20022080c040c00c01450b08566003941800780c0e070300280562000700001c2c3d00940240110030345186551903201c0076405940c0ca002000c07102c0e00f07a9480560010028900301100c804040d044031524503203198119100c078042c2c0030f02d141d40d80781c808843c1440f140a151080f00191203c014140c00c0304030308581c208810003c3e40100c0c0081d14003600d00040061a6942c0981c00c42401c1c2d010900b80c450320345000d081100a07040303041e5003105007604140317020000e00d0901c104944648104a91022070074041040b5007100c2c007500901805529161320000800c40303055034a03540460074980450100504076455400d019101111441c543c01d14040b0340c1008811000b510003d4000d0300d601c216a62540030b1241030366603038001408402020090b0001d0908a90440c1e41c0c0030b400381241d2880c00741c0d0400407414000b040501e81d1852001009100560341e8481038800c4a40110300c0151308119980c1c00280c00444030190 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 941253300 1250 941252050 941252063
    0x30207060503061f0f0216030b0609091e0d03140f040605060307080307050c01020c01050f0403082505010608010513080301053c0307051e100302041502011e0605010804 74
    0x1600c03940e4821142403080c42d0b030144c8905500c1c0304100640400000c035081c2002d8029034040d0b0031880303600b8a500d0f045a420164412840e01c3c1d0718203015403100c02806e201c50a006170342c800c00202c02c00700c80420246007140700a040c0381d0b1125800500b150034a410411042401c0c9043c02543c04c0340d0b0107100e4009400030740002d001d8640c400064504207042d400050070380008500074080c0540810380001401d000c2c2c00b80c074103400d0181c004592901c10304401a0004005000a0001c039000ca0081d05807019410031100102c001d0811000448418a030100c4940c0e464500c18080020700b8020103800c030b260884110b8104145982d0401c042c00140070f054010154050038280d0400724809074400e10a030f54900451000504207842480701c2140c180c1402485000800134560401940c10060803e4654040a989800c40304008807601a160001d0405d90240030114860381414500c40c01c1990701d4000040c5241030420501900c04c1c0800c041518030b10f0600200b04c00d0b40c0018003542d010354481d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 941254550 1250 941253300 941253307
    0xc120914010e0406080a0f0b0609010501020303071d0603271606030513024b040504020f0a06090501020f010e0a1209031e0501050a0504031b21180b070302070605 71
    0xc0f400a100c02d601c0644103200d015001024441c11510407603501e8041c101c0d45c0300660782d00c410321825840a120306070069000308000b6003100d00c00c0c19103120708000f00052031100c1e10a24000342098105550a205021544c0900511040098030010855a41001a08a0002ba2100845441a14841c00d014141c550000540d515000c14052260542c0140201d60303008901000030341000e0b0025880d2850503003003405102e581600c201394103684d071071048985541c08071070040c0800b509000d44200d8029010410310002d60f0703100c0c46a00081c1015554040c0a9441d090009181080c0c0002d000b8460f458404251010000440c280c2c1100340c00c525608500e040400040326085415440900080840940711040f0342c1940140600c40740144001c1c811900c03030a5080044500945008011030342d0094403410030203a080d04c10300c1c1c990007004200c0b44000212408001c000c1614401e000180c010030701d101d49060b0720000400500141040a4107144441c0c7d8007940d544414040e0206005010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 941255800 1250 941254550 941254577
    0x90703270201050f0a12090309080f07050603060f0315190c051c180c0308120c090a03030e012a0212210904020c1b0f0402340c060c12091401 62
    0xd2000d506000c1ba005030402110178030b420000c0c90f010b0340b40141e841d68001c0b013003101c560f05000580242a030798002c0c282851034542108121045a00110042c1c240c06802c035100c1d5811102031415100703514402020341030743c40300e024102c11980440b050000740081401804400c03001512407605000212500042c804400044401480400b01005120300354040b0040100103c102c080d0400c45c00d1400380108035100c607800d488075800b404220707030340100003404100003007445040384c5c104010b0f044c100a800c4e4110300d4040c0c03084919800818004405018650046080c0404d801d183c02c0802c2001d421003c0c2e91f040941685601090b07001c0e040344012843c58403541e50781d03040b42c0102050740100c074448840d443c41642040007a8040500c40e01c01c0c003031401e00c20b08088c021102e40301d071640c001c40442080c82c000b03403000c0c0180c24580d001030303141c465000300040c180c2da801c2c1010f49541c2d100c0d80b5083e2000c0c03900c0d09030650340307180e070000304a41c1c88820401d00072550040c1041c9003090070302c8424031510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 941257050 1250 941255800 941255807
    0x230a05060312040b12010f06050a030b061b0a050d2d0e040905060901110f0d02130b040308030a05161e2705010e040608070b07060b090703270201050f0a 67
    0xc65502d1080650005001410403c50300091082030140c3d094810180e83c1e803000790040380d25610842011403000c020001845110364840011020000c2115080010085420034509480c050220300c0b03134000302c0002d00344a010040003400d000580351201e0190514100c002c8500070030000c6c40c0e923030020240803505ea079000b02e0910401c0c01014108000e20303580e03410500e13514035040d00d5103030065282c400050101c680100803220f90704038070f40d040c41c6000c0394000c411000b50b11480071100203100d800008246054500010401503000d09c41c00c940b40d0800c0d10081c4d08944010301204181040d02c1c448a078110340204150248012074810340848408401c0240c441d215190b4941005040c90000d219455407180c144d10152882aa02c0040465500d821300080b5065030003200241d074807443c0c0c01c014045c1c40c0d038002c102051103040d0105411050300080341c1d85040966000c0f02194a96a4980c107841100c201d4170400318080240d075007001c100342c0000c1c1c02441000403400c503000b000111810f00c21300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 941258300 1250 941257050 941257063
    0x170306010e130f11030a0e0703051c050c07030c05090c0405030a0201050714010c030606110f1b0109090903050702040f021207050306061209030702100906050a0315030203030706050109230a050603 86
    0x2c080f10203102401d603034011264254411100c6031245440c107580c0c94500c0000060401c162980440108464055410018008407600e51303040c0400004100c1000050030520150000358881c140c1060030a040070204801c800c0c0c0200070018188090008100983d000241080150b4080c2401c5030b440c0824206103071500c0c54007100c03803003940c00c1c483d07041001645503100b10300301d500c66a80c0702512002c401540e032f102c0c402c072451849194041015141070384880f0b509110f950b0814188601400c1c0d80d4540307a01030f1100124180d000c0b8a000c1108030135402c16014a0000b8940e01c0030841c900b00b4803030000e4600050141c001000c1100c00b00c00201e032034a0f4038049400320012190182c62920300900500c2d52640510f0089000d5884900b41000180c0600404030949115454040c102242c10f0307030441c0240012080071500704804a40040903840600003001518046c1e240810550f0611100005503140100b50014601c0c441d02e0020425081c0c5607115041705040f4800b18458030b441000078074008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 941259550 1250 941258300 941258321
    0x121b06090d0b09011a09040611070506010b0910030b032d01090c090b01090e0c070318090c1d010c1b0e070c05070504110d09210c170306010e13 63
    0x1a0703203001c1c8001e00580030501d5108103841002404a080c401c0711515402030a01191500400040003080000d0f8035600003c1d201111b0aa4580c03c050490315868903205080e404030080c2c002c002a0701c0d14500300440c2c40b841050941c142480242403d002096441500010152886680c0012003195400c01c601c00c00c100d05070075009000b046d000b424115084a403602c203254a0030319102468500354000d0203041c0c01c07a4131504c68844155038004c000e20459024041c01c60410801c80d680300302803e078a000312000f60101110000da038441307019005d40007115800d07116601056041070469181c0e030007034071040b801c2c0d03219188608041012405602d182101d400407200e00c201d26081100c80d0342d00040208008d40075104a95a665444041c0300840d0503907420721010040801c03c0001320891758111401c424410300c109900841317201c0340807107405030310348410300080c0594800805004141e4100600000100511071031410204000b81000b148102c00c14002c0341c0104010b803102d80345502406d00003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 941260800 1250 941259550 941259559
    0x8120307082509060314060a0312020c031614011e21051f1d0a02160501060b03090106211103030d0906150e07020a1b0503070e040b06121b0609 63
    0x680b5000d20140c0542124042c1d000040e00d806071017400701c0d148485143c007c01000e000236040030f05640b1046011581d0f90740000c1544503c00b0317550070780d8a04128200000265034507160a641c1040c60680803450445543c504002d42068a4860030800c40b061164000d0507007848180480980d8600e049030401080d030101c15482c1c4020810070601342c0307800201c180d0a200d8000c450350348504001e62501e800380c0e00c443ca040310b0400056000b200c035034010001041c114000c000015240d90311142940e4082c1c114665509000c014008051424020100030b03120400398a00b540e1041e0540240305c100c40f00000d0100656078251021a403024812201280e540c680d051042010750300340000075000e02c1c61040d0130b07054802000034083d481d0050b25402004180e0241034410700546544c08400c501024518a005082d500041c1c1c0e070344d007003101c0c50003406004900d090030710b01414861103001000307103214010804110340a17002000491203443d80e452400e201c00e0b1501c100d5020401900907003103082e401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 941262050 1250 941260800 941260861
    0x1a150604090203101d011e0e070c030e010c05060619031e120801080a030e0301020f042601090c03141e0f0d02010218060c030d05100905010812030708 66
    0x805410340045106801c0015600c107241d90b02e620320500c4021128170321442244c040014810501626a07980c10700c840c0c1c0c09150902510786100c01080001500c500c030200303407284820400c160b00a0303100c2c0f212000908101c0e803400d01030f41341c0540f50710300205000d01c00d140d102d201d04150340801e05110007640d000300b60b01c4c95154641200d415110403003903080d41c40da0414900404100c0c130a580950503240914094880aa050fa9003510305c0240402803541c195005d1003001c1032504154040c00040c882c40018503d059a0303207604140809049224401e00e906200858000c5171298041404980c1d100c0c14070407003044600d184a041210409690210000c4110110007402c00000ca454014103000103032840e20420000c26400c0b4455050844000d000000014a1a00d484800340c081010910103903460a60501050400c49038115451201c81d218420140100285882800e001d8881c0c50000c100c034007511802c042e000d02004080e075080080200c0000c50045410215000901003050003410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 941263300 1250 941262050 941262059
    0xb0409091a2a1216021c0e0f0427031404050102030901080a06030c03110102060907140d0206070c0b03160f020c04090501090506090f1002190c0f0b04050604020a0b071a150604 77
    0x812440700039900300148261006c100c0b980d0040c1da8100c004804036101d04181601d09014088000710202a0743e600c030390395580400c0c00400120040d00d14421181e00c002d00c5013000c5c68090700d07a83c0b2301110b2002c68503050100b8411a41c00004581c980c4000b401c240a540d940c00320010060492038000a1000640240000400540c200d0968403d1402d8003a1040313a82c0b4200003a680301402c3c8a800e40007006c042e0345503014201401d80218050002d8116441c210042c0c84000c480a915800003804000020412044800300d03000c050b1984140d1034401691002040c0c002e598200035032042d84500c0c0e80d1030560703082080c03d41c40145141da010301920100c0c90715203030709a103a06000840403064000c0c0c4100c065420303400c0c400c840d00b80a080703031840a00f850301c1030111001040003004a900980036144080881c146180f41d907c40c520800c0203104502c2c140c410b010005076642d0101c00d4101060140c0000920258000104a021100b0328045580c4010300300c061051074248442d04580300180104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 941264550 1250 941263300 941263321
    0x1203020d0c110d08060102012702010207060c0b04060b0604051e1306050d080703230c010605060301050d060b150a0809060c040f031403040b0409091a2a12 68
    0x114048286500300610300110006940b0000a8a060141a000110145402c03030164001d5a08600184000900c01d101842622000b85c80e20350001410140000c1010840d0703030402216000c1c4c24540707080c3caa0800381d50b8a01001c0b8801400041603103407180486803154031188299001018010035a101c480c88000085800c241c0348100c99018600d8000c1c00790100440f4000c0301d048803c01b5050141084441e1502c07481508544030860402c00c0600d0140242b000c1c04064104403104011202da4030f17040008141d0031507840354081c078001c0f1018801004a640c2e01d054080a69810030804100944100c0000311401884000c4021003440070500d00107042c1d0180f902445600b4402c1140d10a885041500b0b4003801180711b07000301425865000e00006021810402c1003c0c40d030803c4a05242e16008100340e242c1090700100b550b55070341d0f004001404021824584c183c403000760644a01d080040300b0307801200402c5403150046c7c49200c0780007041d00f0500101c41c119680d808002596050100480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 941265800 1250 941264550 941264557
    0x50d0503040f0218150901060507151503050f010f050c0a0c060603081b010b030a11130e3c0319050f0d0507110309060912031e0406030c170402010305040f120302 71
    0x412070000c0841150f141030021045050307644c89c8d11490708101c0c15076516055a20b90303042344400103840b030a9481d0100301e40c1d00c00300051032264007d40015507601c00c44a08603071381c440e510703c8c036141003805000390807803a4800c039608041240745c815008149814501e002d0601c552004051000000b21055850982c405440d05014220300a000e48042c98041661b19620900003404010b5111340c2598075103400d8510682d4046118030200715039201c40a6107040061075039517900601d4500700d04440c041079201401071803078142c00d5590941c21071203a106030741c2d000306041c110451100c10130050415002e80181c8500032426079000f6500c04510b04c4d204013070402900c06401150200200e0352001d4030110a8640001010340090304100020301000f90412000c45d40d09001d0008006000500c440401031060181075894015511440c052000382100c03078031401101042100d00c40c0155802c41c2d00b40d04d54125809107008140380d110f60801701c0c0000c1848000400d6020385a604001154064014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 941267050 1250 941265800 941265811
    0x30201020c10060603061211040e0f1002090405090a0308040b221a1612020f2709011208041a09120a1101031a12011107060b030f010207050d0503040f0218 68
    0xe20140d5600c4440f00c4000f601850000c112103802304080e0707a9420554407886c4441f640c50125001c200d001541107003014142c240801e44590000341c5801241401d01940750401740c0746004150070000da0710000d001003c00740000f003015681c080030544e11000d9803046420002505115140100240382c552a10440e490410b542c406000000030f884681c8102c04040b81046a00c0d4070030300d8984509050020361081920400c0d98506000c07840700d040803545140000001541c1c04201c0040354000c201c09490168440d44c0741c95115041d200c00161444203550440d44100316482d042003030000219500e0040701034486d040341b1115035440e40c00e44001000400d1502071101c400c03d030520a00114199504412a007280e104004250495410645000240580c00500000346c44c3d5454064804a5010302d00c00d69110f61544240c0c07103149010b001c83d600c2d0744a01030003145403e0b5035a84840c0c0f60350309402c4900900030080001030922100e0200c031001c0c1c81d4003e141844012010b9180c09900500b501d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 941268300 1250 941267050 941267057
    0xe0d0203130b0408070b09130f02180405090d120b0603070c0c090504030c081e040b07030801050316030f051203070504080d0c0b011a2206020f150112030201020c100606 74
    0x3000030311a00c00400c079820f450301300b400340c10030908080300c0003590f61200c50910b402c2441d2a14140d0741c0941d51288910180c2084030269540003200c0d03c0089840e04039994074070440c41c02c400c0c00f42c07090340054050761000c0681481c00b000110410700d00001c101400c000394000000000b0042a268400f4041940034410360014065513207440310702007103500407038008000c140c10304505c3c03000c03603860409000f81007001100c0f0b650b10140d0340f44401c1030750026401040c82c4c0340c01280b214200354001d01c100c0d0140c6019401440b107184101c5d664046140c0d144406800280340d0682c410501030309203c0016201120964103659007400d10004210341c1c018401c00503c1c0c090201c0040280e44140403250707640d5002503c048aa900348003143c01900741c6004d045c40408400c2100c010740408100580407250b803103016450906141020103810a60b4044036140c0c036410440c074070407036171040c0031106041d606003180c08261030300245001c2c0e00a100d406101c1003544102c1c807540007140760b9600f20328107480d1240d9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 941269550 1250 941268300 941268337
    0x1406013014060108091606122d0f0908040905071b0c030314090a1e03061d0d080c1602040b0904050c0f01020f060c07110909060406050f0103050a060f0e0d0203 70
    0x1821b4070f62003451011044411000070800c80796104100f0340c201a49202000030790403d260140700034001426001c941d135624401c0c00c2e5044207084e0701c90402442c1c20b14509000401c6907903140000c2d84620f00640c42e4a55075807000c1424148249001d4000a402c440c110a90100c00c0c00d0074a0390207040d200803400100c43d41000540c01e01040c09481c000f600107001c0d4104103040901d0b4102c01544400c0354401150300c04400400b2400034040c1034a60754460141600316000c1d05590b5080401aa66420911010a06100e403444440d002c840c000e4480d4441d29810030054800074000e4084100065400101041800140007010518a08944049900c20b0801c0449001680c80307a40c1d8004100a503040000040d000d410003800a02c43c41c3e2180800700e034152006070004400d00010389903001140d020904001c10040306204047c2c20240460b4100c1c655032540e80e800e540c50048060042c52151250401e42e462181ca404c040000802c51003558048080000025901e0b045806009000c61509 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 941270800 1250 941269550 941269561
    0x140c03190207111003200c0c03060903120622021b0f1b060708070b0a0b030106050d1e0b070c05060a0b150309031207121406013014060108 61
    0x1072080303480d6180d01c40c94809441071000200803100900c1c80d80031051540300c20308040c0340c03604070400e04081441004a242c403818024440c5180c0b0070550320a41c02a44035006000d01a64000103990480142070b1204029503201d40100342c2313101c1c00c0a4903100c038104e10880c0b1a020308240d006403901034072074121030031014180ea14007941c40080c0452840107030415004c40c480c006031900320003101040580058507112960703a40d0b00c11070380205030941d1040c44100502021400a004049104000710000e000305400e200000c1d03040802c0d000001e01590002c40040c0301a019a40a141d107141c00c420460802d2400c03440c040c00404030f0050464040c022140010055143c0c1d1080c2000e21401500511001014858100070f581c806841200544010710a80c03000c64034181070640300e900380c3e640d20000351020003c0b24054912000c08076044114480030060281d1303110814030011548030190441d0704c800030180301d003410300040d1180d000b10300306200c411051000c0d00e50903020700000e80c0c5450882d680c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 941272050 1250 941270800 941270851
    0x40608060d020a14120604030324030210050a0e03010c050c071e031106160c0e06010201200a030204081006030309120c0302010c020a08012c0d081801140c03 69
    0x40340d0000354000420401481840030380024255070010140c07200d8004106149040d180c91402c039011230009465080c0ca06031a40c081001c00110450501001510350540c2d001880c0b03502c000d640320003000070200307541d24550f118085d10380c07208802500070809550303140c07002002a401208407400d24030a0301c00010303905600c00307082e000402206110b40021810342e034441100480450340346601031000c2c0895990340f50241c0799400154455201403002d10700d1314541500c0d00b440142003a055900d0000c080c2007800c010b804c40780804403c042115621038000c5c200380e000307011b240c0190419106600c044e1004001c168000d0301524000c0c1c07030b000c00301640c601d16004079907064400100000d442440030070055000e2000321140d80e100030700c000b50b4203458501503400c5400425a80c3d480d190004010300c050300d005e050394400d503464000078040385480030030090820070300500a88890b4554400c8460442d20a5015004a402610028165003003012805c00c1d150400c3d42c030781c4d00300d10400c0042c00a42c4034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 941273300 1250 941272050 941272069
    0xf05070509150105071a1f0b04051503060402040f140301050714120402150c160b04080a1209050402070303050406241701060305151f030b070c020310020c03120a0b060418020c1204060806 82
    0x41c06070b69005812641c12f9030541010b40f0042d00b103034080c04007048007142d0445080151900c51b02c01001102001d080500b034400192945051000c0c1d2110003101c95a40011518074405403090101591a00d1021642420810460a10b50700020031024520312000c2441e603800c032025001d05040039100c004a0f05207204910400c402948081c0000c2e0003d2429408030008c4261418811201a42c51020a080e40c1c410f01c01140025500d0042008004103841602940030f41c42c5400010100807071105103141d41743d0301440c451801d0720050960b074620250407000141d540001580d072180160042c200040a0507501481d1210307400700b4502e600401000c0c244120303030b08101c4480c002d480d040e000795080c0001c803000b40c0e0140101c41002d611690705000400841184200031551501440300781c2c400820090080705080d030034002480b109540300c0c41a2001d461001c20000380c650074800d9101d0080c4100d88070340d142400303410a50341d445400080500212400c0d91201420380d40c6140400102d0031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 941274550 1250 941273300 941273309
    0x4020a0c330c0e030705012a080703050a0215040209180f010c03051806070e04020c1c08060f0a030203030304060506190608010e0114012102040905040f05070509150105071a1f0b04 79
    0x11f41d100c0701415000c40a200c8147c1001a080c031440314882152589d0b2100d80c001c40083d00810b01c00664200103c3d0b042203041100c000907845000c1c181025400144112000b4248801c4102c420700505096003090044840c2d610303544000300500440d03080042c001c0c1404a0b001c028882840c4030f8401d600001041c1c852040d81541e444200c4101c0400400000750041044c4d80312920030048050000f6038000e990030081d18680d210061540b0b008001c000e00f641003030441074042c1800c0002000140c90000640340c1042e402003001c10302d0365804d400310f604201d09140729221108c1d4507000080680d0060050b1381070700c9a151030641c9580e281e040342c0c1c01400440d20142d001070120014031040a01c40b0101d07030554980c081c4090700c0d1640d141c0e54070090316025a0280c400a001c5298101048002c108850050405842e403107001d240144101c10403d44075001c5c1c6040c0000002c641082000b1010040312070481110038180c542094500444010702c6030003000c03286100008042804401d82d000d503070865 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 941275800 1250 941274550 941274557
    0x11031f1a060d24080a020d02121c12090b0630011509060810050406060b030f0907230402070809220b04020a0c330c0e03070501 56
    0x4014024181005226180014040d561408508000d59840900034198903040701c0011a59100d61001211009141e048494044221030000c0001c00700216820561a8048810003082c407414004528003030702c4005070104030b002d541c04c01d41c190750510355200107007401c40d5955520b5001c401940740490b81950070180c00d030400000003508a02d04500c05050380c20391101c02480040e10014060044201e02c100101641d449241d000039011564042000030825000e082c0080e40c0b038080416200c079030380300341012040e40343c00c009014030940d50030110081c08000b00382562440c00000c00d40302d40790103856a030024061482d001901105200030300311606011480c9820100026082000a50003510202c0703100e5824084840580d858070788048021711424a00b5500148450001040700d910111082c41144180240e000540c1d0103c031800441e5409011440064404c092144400c60401d00f800a003513100b01112070407400310382220440d00e041d0f0312a034030a00071090406446484500445000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 941277050 1250 941275800 941275843
    0x30b033016120c1203060e130303090204060602071a041d0406020c150711011401060f0c1e02010801060318020d0f05070f09060504050105060919030c03081206010f020c090c12040c031103 82
    0x48c2800420341e070036104d10900b00041c840d50907a0110701a42d095600007805a00081030411400c100b00b41507001c284602090300740b4003820107500c1740b0b1082c07185c0194080030180ca4009001c01140f541101c0c203220400741100c402d4582210f01c0310000f141151800c0000310119055100c00c00305004104400403610000c200d940c2c01e00c0421642da0b1081c60010041080200a043c04951051040700d401c8000140400490f14680009041810180d106a08140c682010644c000d000c40c0001d8415550440e04142914401d0504024140013400003900030300071a0000a080761420020f02c0c00c44100050500842d9510f00811084640910400b904240304201c1c01e80d076481c0858a0165006840862441690300c9468514032028aa0401c561042c030004550701c13407040e0070f401180d11001c02d281094000300b800c1c20094590a8030381007070f402294000c01103070007801e500003500c211060078030002da07180c40d150601c90300c0c2d070f000c61206803800b22070001b2100185c00c000c41c80026034502600310307a00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 941278300 1250 941277050 941277061
    0xc020102070302010f120f0b040c09150503040609050f01051b04050603060d230604030e0a081005070e0d08180303030408070b0a0605040903030b033016120c1203060e 73
    0x4049421080c260b0800c0444000701b88680240d10a500341084094400101d440b00343c401d00c01169000034070207050000d181000c0050412040a98003200b00e02c3ca00700782c5a80300c40c9030002c05046010002400c0c0c0c0a140d202d0368501005501061280a060016a4030104000400e80a51046024040c1c005804000250081c1004000700c1500b5119001c007203401d00d4003d5a0241440711090540500d41201c01408241a80400b581448031402c54000e00118503081c9195600d42e40c607000a02c01a44460001d80814003c141c5640288400307404481c6c54040c1e031030000400d912902d16070040074081100300c1202d09002040d02c0c49107910071a01850301c13070345445480000e80010150b401c41c5440e0366010a02d600c49014102c44180709441c0030401c082c03150101814154419041e1030030340d90522820b035420500403100205819800c405c03959a101c2c41014030030003031a01c030018103100c1486c1b1618042d280d01580e42010035000d44000c0c021081c001d40c04800784c603c0d40c8180b201c0b8207a1240400c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 941279550 1250 941278300 941278307
    0xb041a070512070f0b150a03060c0915020d03140708040f0609050a060902030d0314070e0a0f08160f0b07060e03120f0108190c030308100e0a0b0406060c02010207030201 74
    0x14518010000c036624001450320041003948441e1040b130b40242c25603103680410125030700440d00000280b90a00c000c91001020500d000d14900c0042c112507115981000000c0c020034505c0041c0156940c8119007030341031400030350798150300c80080002902d071007010150205e2124507036024512565480c202070302d030707900d50721000a05000140e40c11030381c070846000010320801511070301a10032040840c0f444880d004040c00c2601a842500605041c07a211000c0c41e2030840440f98841200d08044651080300004a030301d10459410155a21070590000b044403c0001110003011a91043c2c2030300068450018205442080c81031002c7e8803c2402080d0000d00290807004500d403441d8101c078105040c0c040780da040c5040680745503500880d100c0040c00700c148184a6208041e40903c25808114403030350b14901010754520005d0708201c3d81801190402000035690001401d0f10b80d41c0184a050605849000380108a07025203d10f01c0c003000010968040c42003c4100b0790140c000d07121441ca0340c8c0054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 941280800 1250 941279550 941279557
    0x20a020312091203030a0506100320030a0e01050c030a06120312020a110619060f0b1b12220f120b1902040e01090f020903030a1b06091208010b041a 65
    0x3030740c42010503c101500000400265101d0b5602c40404103a0b81451028080d10400102200080509140b444000045100503003c014000024496601e54540c0768000090807024004240c1d54200005e10005140070f101030350181c4040042001220780d2004410b503800024040140802c980061480200036a0760180c0282c1d03c0900341f174403840c0740010280b400c00f03a003143c03071030310b0305910301c0c0c0c0941c00c240a03200301e42c090b00040901400d61030611040855a0003800301ca000402880c0c0030355a01d10005001d0301c1401d000c0c8d4103949440c1c00e591440b88d203500c203c00929114144400c040002c5141c03888290360100c444081d0a80e511000f1030b1507149007440300900c113041d0700c0b10b2004a003102813120720007040100750158cd05051541007081c40341c02d880d4204a00d40032180140054101c5540c00b200b01c0d10412014100031200324501c0104180300b201c401c001400803454202c101c400e000402091070308040c11030f41e6480181c5c2e01c54403052104c0c0261f010b10424a410b00140700f00007103504009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 941282050 1250 941280800 941280817
    0xa02010c060e15011d01060e030a1719111b0d140c0a080106060809010606050f030a0b06121e070e1c051608100219050304061805010615020a020312 65
    0x40d0780310220900a84807010b02c0a030b00ca440035035085040c01025511030b217025805003a2a2400680701c50b16040080d681e102c0c0550701030041d5004800030700010000b00200c5559210f000d0b514200c500309544058281d035001d5442d010a0700035501403000c01c9011070000015040000d03c03020070400b290312200e0111000100d030400078031401843d084a0b41e01c80e04a02c008208860011076903506001c2c00a1055401034070b038011503810240203202c40d541000955040c84010812a5102d41e1f07104003a13005000496801c0e9001200000d144070b44000901415224803044100140c1e15507840d800c942c0040c5017268150001081c05c02d12102610b03100888001c02d5400503401c480855054892504110309546503c0c03850040040c10885001c0510100030540704070341045041c00d5001180802c03c60904041d2400c00a0001c0050704000441e1701107604407004180498180d0914135040b80280071a00441c55010311001c1031842ca1880001c4082c030a03a409405010a2a4860020030b001e4000800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 941283300 1250 941282050 941282053
    0x709061412011806060305010b12091f0b010806010c151e0e060403090b03010303120c0c1a0f010b0c030d09050309060a031410080d0e010e0621090a02010c060e 70
    0x1600789450741e01580c58040c2c40710000c0c402c6608880c5050340103c9035540e1004040c5030408004006401c2c0d42819a09121924520360349503507a0700c4842401c103a04c142d20300786904600080d00e22180721070340c883c640b012020303280d20500d0348454005442c1c04229960003480030009004030040001550002c1541ca0311090021039044d04c0400c0c000c1c180c1c1c00700400c08815502c208200000d1581c40843e01004161001c501803455042d914001e00803130702c03d02002480d07034544001d107105074803410480c050650052690002d071140c150014401e10340a03284070b41803a8020001143c0c0400301c00445411499202c019031800c0d86403000f5001900c14020252160300041c045101d01d91542402495030011540d0f000a4007090f0010741d244110015203c40d0040c106d401c018080703101e000419440121240c180403881101c400300483d1210703840c0032403e811003004540c8404824980f441c2560385982154094459503480d04019514042ca0001a000030b80480541d008200242d0256503095007050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 941284550 1250 941283300 941283307
    0xe06041104110d05040b06040c02100c020a0f0305070b01060e030a02130f09210f09030219180c02061b0a08100308030103030e01120c02070b090a0e0c0901020d030507090614 76
    0xb00856070b801c120000c50b050b070f0300e8008120400244c04400c81e800503044804100c10050390300002d49e500c0d9051482c400c0160b98529201002c3d0082195001d104c1c1d00414004120b401c0e032900401d9078200703500840c0e04143c05030002c51a1400380c1c20f0016141400b400500c2c4001c407507000c01400600d800a84142c540e6501c2e90024249400d00400c040346005a41c82c2d04036000c10417030000c9400d1003c00030310030030442040074800c00e5403207001d900440780c044481900400e2102c151000709881030b80a101010407041e412006e02d4003940141d6074030348080c2c00390b40196441d00100740e46407412a010200840b070400a40c0b18460080b1500c0350040072416003840001d84903601c59065900c2a08250003203084104108a19030340409600c4072680000424006101268400796441c42a03002c0e0883d078441c00b003200c112039100d9080f484020204a0340c00601410b05440b04006540052142801400f40c10303800108070740a4024140181d00d90b560b1034030040e24220307085039198404500440c03d1213080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 941285800 1250 941284550 941284571
    0x10621080c25080d050711062101051804120f0207080304030b2e030204050702030706060e010806130b06060714030a03060627050d080c0f0f010f0e06041104 69
    0x82050909518440c40018400c20107503100e408510500d034040c2c451a4044c0c86908041ca500c0816900443d0303000c648080e000c00303000d0000302ca40c000c14810414a000140c94203107030040c084c0380c05040328015609048080301c0000410702120003160b01502c0105240c41c07292546219200c9030300303940140e2040c3c0d0100c5486510710750540e8016071003540c4031a03da40038820301801c0d882c145000403000f8441183c01c1c5a00002d0728500240038800648115035910004150600070300482e150903a10540070031189869610010b03403520b0a0003030003030178490000090810368011800c92822504082d00030b91590300c000420035280d0207198201c0d02c0030000400c440200e40c0401c080d01b00a1401e443c089806400c09000a0000c00c030080381c5c400000c0d880308504482180d025100083da04181c406024540d814200304a151003906050aa00d20a621403200007070800315043c008007003801c000b40301024440c5042406d944d43c90700c402103141c000b100420009043e2921000c0c4009006d0008034a5030640f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 941287050 1250 941285800 941285803
    0x2030711060702370603020a120c031d16050319060e030f03010b0909060a141509090c0406020c0405060f010e12030a21090506060618030303040305180102010621080c 73
    0x44d000802c020f660340d000590058014290040c0207050b01d498110305105d0440310040592241c0c84076100388580c0d030358880d4225032107a040807040510605030b02c8a10002c1f20b94a541d5001142040101007240e124041078034031740450300351001c01c0b140c201c132803209047d034441c5002042070002c04509031008110075280811500c02540c02050918401c81d15800f504040c401941001005030303218020f03004003402001a80304186044860582d20640032002411000011b845070065403980302181204010414800d04018002d444107036081c4c95080752200e00b8401502d500390742c22980011182c0045181354070400f1481d47c08040241041c00000e41c514145047d580110441c3e400580c0201120702c0700c0170158450500e02c0340441d03040080300e56a841d5591034480250003d813064400140103d000740c2d85006c03510f48004000d05581e45c0e401c0914025080781c1c8032004207039404110188041248d03006103d00300460748500f083d244041242c0e0380380550340030340e00e0b0704650141d030038841001c52560 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 941288300 1250 941287050 941287099
    0xd112106040807021002060910020904020f040b040f09060f03020906030a1a060f15191112120112030e010e01020f070b0a0305010b130302060d180f0c0602030711060702 74
    0x8038030b4142e54994030b0040c4031412400960300c100703543c001414880c0d00c15001401c4089a038541d40010784800514000078064852542d0f0320181d0600402e000c6407a100d200010300480382c1c02001000d603c0d9032440d0300c1c029a015446091203440901c0400c0003d8140350706071503800380000b02518005800e80c3e807201e140301c0e203900000d10045041c6040100700e003046006645010b6080b9903c11110441c20403001680c45480c0d0003c10605500800040712400b03908014200d0070103c060703a070320116000c618191504004818019480540d0001980d0b060b100461001c45416580e8400b80701e00031301c01500c2c007031580042d080c114070032481d040817004070921170341c800b03018507400e550b07900c58104000506030340060304040302c0740908002e00804005050200001c50307906445140d05ca8011a92142c0100440200c08100200501d611010410012168042c0358840c860b400e100c0c80e25440e040fa502d0042c080c008101138070f48511080545442c2000d802568030044c1414850050708560007030203039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 941289550 1250 941288300 941288303
    0x150603040f12020111031f030c080105190b03031801121404060507110d12140106020105091204050f04020906090a0b131a03010306020c210703030b0d11210604 70
    0xc1080c046a07040210003090b101a801e00d0740300920401d14107245550692002418100c01c0130001c2200d00440803038001c10300e00940d0041074200000d517131a548103000e080212880ba90b01390040c0405400b083e814402d200b044035024005500740b0104a0380b07110b1070840d004c0d10605000e03c03000c44406904050181c03804c8604000d021405d01d0815290050503540c01800d81c00903c49804000380f2483d0340000c5108140410b464100f801c45078000c0000001e0241100018644034040008640f650301508108d01510851301101d80c01111561440c030030b8056800384a5020003407028030030040c81c040e0080c01c2600b4005003842e10f010a0040001c0c28150540d010036078002010480d000ca074410300c01590024850344040f41101d0054a60751442032005000c020304440e80441d0b58800d2810400c01c070441640000400252619186140340003030b000700a01300c00003403c2042118540c02d0071200c07400913507441010849880802d004115102d0354010381d1002a82c2c0f0a4040340d0041001c101d01c50199 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 941290800 1250 941289550 941289563
    0xa080a080604152c0f040f1a150f180a111b0a0308220201030c030902030a0506060a06030e030409230a020d062103030c09051206181f0515060304 64
    0x2032000200e0b204d501c0300c111035403e11072100c804000404030703416001c5511503800301d80c28494078941e147c00b10740d001d000800c91940407186d004001c8503180d070082517540c0c01021141e00314181c4000d01080011044410000c50040b5080d000c43c0003040c041d00600400320043c91071b01d0a200304109d100307440c0382030002c42c1046d41d40242c60366020f1603085850300b0303042125540310300c02072910012444440240a00002c0c101940d8101580620b4801e5018564180d40182a20080c07090b50810b90781d40c00c002e5440c21300c1703031400d01c400081e518001e116140c0f680e040c103c00755041c94600303083c140c02010000765451542d81d8800c400c2260f01e00204030303640300e102c51700c1c4016156000c55400000311015900709010450740055100c0c0400070007485554800e5040c80c010821804640f021503403486150310203504074501d818032040109021440c03520521142d200001f6010b1440c5a9680d2114150126101d24a124020a011007019041598805111300d4441c0008144c20040382030785d84203e400b500e20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 941292050 1250 941290800 941290829
    0x1090605060f0102030a0903030c0c03050d030605010e191a070c17011d0c040e1906020711010201091502070602040b180a060504052d040207050f07080a080a08060415 73
    0x151a004003030b15007200080c401581084604040980010958003000d020302c0304042d0500304203c03407580c18074055513110701941e8100c1d40d2000046d000c3c150b140140c81c08120300404105d100d00308102c840c41c038582d40c001e21940440c40c10401280404458500003154141040850302040c001c1642400901c0329003100000050840712650844d00c03111005124401c0380389a010200b09d0000e00e29402500850300060085945d09103180782440f244c0c5500300140c040c1010700e0621000b43c0c00340804c20301605002c1d40d80906034004900300c45144000605c1000701d4100030031005220340c00b82184a209550041c40e050300c602000c15981c01c1104007640061041880d4040390404a06000040c091820024205802d000c00140044d40310203001402031141f07102c1c00d240e1a00002d400005000203442150341f421070f418010703210502440280500e228041000031464800540000920b0f001590076080c060303030300001c484200300036124580c0a0b0300c44040d25010000d04103101c00030100601c06084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 941293300 1250 941292050 941292061
    0xd080706150e0f011401080601030603061a011103090a17030c062508090c0114070f0305040f1406190e030f16050f0f0909030f0c06010e01050405070e0f030a020301090605 75
    0x4407254003c19507421000305034010001c02922600c4c407034401100b424203443c50354a03900100d00404207507001a240034100315030503603610134249140c102c03000280d03202c01c50b81c1c007924040c1e41d403441401440da41199280d0307020403011382810142c0d00d103000d14800b603900d01150300b0220340ca0b10000340c4403040c0e144084070111040581e4440810811051070601c0e09007032407c01d8100352900c2140c1c50090502c860a9610400400034508070303880148d12104440c0403401ca03040c01030494000c0c1c000c00c0002d0030300c00d0b0b02003040e140c0d0004041050400400e810f190960343d030381c00e944006c9070904401c188031b4845c90102c1703996414402564248000d000601c0701800800c85401201e03505d500050149040510f0b110180d19034044d41d5012440c141c41c0c010b0140c8031114024174500ca210201100f01d1800301d4120107171500494161f04071450920006861b07603c0313000f044112442540c40c64042000c07207044010500340342c0000c0443c0c2100501390b40241d440f5030080b9013036551014003101c80075611400c001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 941294550 1250 941293300 941293319
    0x607050a08130506010302190323010b0108090604150207140a0201030614061204080f030112050d0503060f0d05010e010f06031b0302130e0a0c06080406060b1303020d08070615 77
    0x5601c11240e02d58019411481d480d1603880e00c1c81800b0190149050100d1146a800502c03540c0e00213680c0444806040e0581184000104d00035204404403542407203c03d4669611402081c1e00a40b0b03100301510590301e0f150740f83c0c0d10309100351030700c042d2640d0240079140214800e11000031300d280b41c54020300929506480010101d80507a00f00280c28480c3c18010101c0d0740384c26040d02c0d5411f0f8000d0300412142c44600f0981000e02410701c824100c03040000020490b4900d45012004c114828800c50b940741c0d9070034000341c8240c082190516042000000b50a00701d2400b881c00c966454020000000d0390300d0502c0090b425154800140e82d8000d0300c40b2810400c2000b2490421040c5a10030380b5480c40c00c1c10750b800104549840340b03000c444503407101c002e80910071062100782c6065034000c003440c01036650f50b41c3c090f000260894059910310b1405100190382c582010460300550341400e922802141198200544c1c2c200005054602c418240150400030392213100701350036202c000003003c3c9100d15152120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 941295800 1250 941294550 941294567
    0x40504060f0f051605132106062103031515090512190b040c0b0706090b07021606030f0f0e01050f07030c0e1e10030b100302070c0e0601110607050a 65
    0x81c0c2095250004002c0030b809144091030304c003200c51405603a21141c0c214a07104030615504203a91200c902044004d260241260001d1000e100d180140009569040341c1802034480120707100e0300b0303c1000c0410001030b110782d018108c50008580d0f40352880e134540c0c4070a8410f400300443c5902080c00658180494900340041c0f0b00e80321030020090290400c00105900d81600d04480200b560740c0103000718040002a51405c03014010304801d80713880301400c0c10404041c100780401a602c10a055001c10490392000c20194051006075201110709483c10340110000d05442003401c0140d55100c440250180707160140c691410141c0c00003003a02d042c244403807100f524020744101c2c18145002c10038801540c210325401c0341c0380c0046501da8048030654041c1c001c207c2c4150800d503882128021080701554059001510004007078502c03102281505609030124480c0303440107082e800000d1810024500080e4215500040c180b40100c05000002007040c0380180c2901c042010807400f0650242a640c4803944 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 941297050 1250 941295800 941295821
    0x2030a02010f12140a0e24041511070b07020f0703150b0603091c050a0c0807060b0634020102070b0306040e0a080301060f0819330f05180c18040504060f 67
    0x140c18207002e403001c01022041f044445400c1118410006800d0040100007000305c4010702c5400e1051001100350710095070702840342181e0103540d210102e400b96200142e5150003180200013410384509507250742c0a00170305001c100c1c0304a40c035000d0844141d00c0700700107940101048002042ea203407000c180d90354035004070340fa01420010103125200d01190300c40008103035581c00401d01075030b414041c00c101e00513015a1403516004440045c09001000e04800380c040500300304051201c0601c9002200022070414042c06401039102c59401d01101401000560300041c00600000720703844070440690809001501c10340d43d0307031004001081003e8002c017620070303d0300340d5240110311840c2415550140000c141c0c0303440c0202e0340d28110084080c8174240c268041c04031000c110404541c0d1080048640f15040c003030149a5010704c9030001e0340341071222000c000394405c008901a0f030350310207642c07038070070b801c40300500c1040c82d04401000074941700d0f40b003894004c50060030003082c0d1402a6008c54240e0300290207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 941298300 1250 941297050 941297053
    0x1c050c040f020306061c0212041b090203010b1222080a020d03020403150216140304080f0a03020c010f0203041508060316060e1507080f040317040302030a02010f12140a0e 75
    0x1000599585c0408440300545070544541c2c1800344000294024010b181911681240d00e44c148014800144004003220b07468000340b000b2251a885840140d020070710039241415030070b008810070101058240d503442408246044c2d1a82c10b241c0c10340c080d6020160003914110000601591f980f0342c144040c00512a0a003425842d0500d590b0381c00e0381d42c0c61904584242544d02180303d80c05840782c18030750701c8516005a103400e100200080000c3c1c0701e45c4240310b48410351040e0100e00c50070f0800401c40d08840c0b03405401038100132505000541d100941e4a642e62700718001004082002d0340310240c1111400c1865640c0394441ca0710300241854012101d00601c400078440380c080000e207610001004954109680c3d40c42d0426902070080341a000d034042c0100703441d90100e42c591b9407034048006881127030300a501242501116180015071403040d070001a415400c019401c1000d07501900d441600505507203032482c031f2110405440c00448190340e0208090701c403c10140148605940500c1401c84610340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 941299550 1250 941298300 941298307
    0x50609010e011505071b03050c01031802330c0303010303081f0b0a18290403050c040207022b050709140a050c0c0d02070612050603060a0b1c050c040f02 67
    0x50034400c0e51122103c0c400300140003440d0030420020320210364400c0e041c0b001400100d5224600b40b07031900d0041040300d00091622079081c0d081c040c00303826000b0407a005803a503910081d10b420700c80a00030b2558003c490b228401c0302c0080201c1d043c00c0091480d4081100503507140e504500e002001620042c080302214003182260b05d1240e00008240401c489051181c00e50364001c01c481074034004041007000704041400100010300492403505c01c0311010510740d081030b044480a52a010340d02603030201800300e50011210b080b0074102980203107005400100b0585245d0324204025200c452035145800b4a4030240c070240d403c1020810011015025500741030055000d80c251003030700d8801c000c0601710b08685031008241304c030f188402100d03842c05610003070700c1941d075a42201a50b5800f0501c241400103030b000003100c120386c025100741401000000c0140c10740f912504444400340aa01e08403a0788080002000152905001360034003020f0b100c0c2c009130500c070745440704002c00c680440300030641c01030040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 941300800 1250 941299550 941299559
    0x1802090604120602030f0c0f03070e03011e09060606140a08190513020406050f0310051306110c06070201020a090e180709060513020c12031306050705070203010b030c0a062a0303050609010e01 84
    0xb80181c079403150ac18540003c403c849100000e0241c400d00000d00e182d071095040c00c00100005420010010b4055201403080507643c4004440342c295180084040c00f00900c02d07600d895115014064200d0305610040074444400211102150f030160b0b00026150203441d44482103007418080c0ca002404201d440603903102050010944a00c0c8880000001583c2c40001410240f440780c042000a60001c604014540703148542c00f406a1040503400120721078030001414403072050003200d4103034020740da504558516040001848002c064800b181d040140c1c44800c005400420104004040028001c21028505011300140942104c003a01946004008003c40340600003034030411f140007482d486d5982da88500483c03184100c0c14500078001e9090000344100c1d03642c000007a01103240220000c115405015003011b039140c0700d0144403900007880042c10484030740034205541c84d004065006100210150201032031080141c2011004a40c2c2e803020300100d4244103000324050000c40f0110103055040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 941302050 1250 941300800 941300827
    0x108090705060409020d090807050f070f0b040b090d0210022d060601050a020a06180b0a090b01050f13050906040c0f08030910030e0f1c091802090604120602030f0c 72
    0x46015130150b2540000d1516040185903001006036504440c2a0b03448506038940704e602c03020003050310b001511400b80080b414100b1040000111010344000c2c0e4903007841c0003241542c580004201c00e0707101e40070003491005600c2d9103514481040c40c1c2d9000d4065100e0340071060400c0d99519120b4842c2400c0001c0400c0c0880380081c40541110007400d0403a103910505030101c0c80c0c40c00c01d80c8010081420030f036403510700c401c1101d10040c2d90ba200e440041d82030340d00e14132044200c0b0482c02011b048203200000400003424503110701e0580c100003810340702840d407082c2c240c2c0c1c040e01c1060b00d0b40e03c140e0740400208020301c5100c0c180c1201500240c44190881483c00b82c0e00b903540e00039240b03d2881184000030a071005400380d400a03200c100000c0c03c2da000e0b5480700065030b4841c4240b100011001c0000795004843c02c0c4901080307401d40c0c15060201001503400301d01d000003900701061540d01304104000101c2d8140c0301d8019928501e200b1500580e882c03a050604084182000e40041100e40c000e00030019030505 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 941303300 1250 941302050 941302057
    0x120201021005061903050607090e0708060d0311010e0304140a1a181003051b041a1c050903210f010b0c010b04050c0a030608070503060601200d0e010809070506 70
    0x200000ca40c0b5101c05000511048080c035001382d0b0700003000000020480701044c1207201c2e566a88030401100e84d503488221401c0c0b0100c030843d00081c07414000446a02e449803140510034040d14210032240c69072240142180c0c0e5480381071500e94004101081079031076100320380103090019110340b07040a00e401d410300e620000032880d002485201103005845841c0d164505070201c5c03c001c089028014117001d010b40100000d5a507040c0b50780100c55026074440d07803801102c0403116546880440610706020340c4045400414260360031040344807085503000050b019150040d9507a13005550788030480b1085030301c500004500907148007090340410441c125071908e403d0440701d420500d5607440b030084030603500400e4885a002c0d805454134082c000c040c602c4001030801c02c4501c1d10304000040c0c4580019548510502c04c855140c1e001600140f101e500c905030048202010708001403425020710512400e009002e40407900180b4145400c4905690008625400960000c05030141c00d0600012910911 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 941304550 1250 941303300 941303323
    0x2060f0730080a0902030a0b16032903011112090610030c090c031e15050321130807032405091c0e0d06050103020a0b0309030313061b0c030912020102 66
    0x6902d0006003200405812070040c0030390040035a135035400503151107149031005560b2403109401c11510400e40501038402c0451000c14403044201c500c6100c0c03000448080018000e9415540310b40100003610440000f500743d074000b4180e64440c61174882440751a000c1c0041280700b4000c1607500810126100300c480000381c4561280c082043c0700d6518043c0c02424242c5001210313880c61032492021a40703183e11003400038a24a00c0e440000d9941d0040503518003407000040303008042070703814040440752000280480b14500300440e015640c0c5000c05401d02d415580248c1d076910310104800164618590100f1001214810030880b60034007880855035520306c1c180c2d0704c142d43d840343d140440c128045d658401000600800c503152030041c5103400009070000b03100490180743c0f07088020a007407400034241c902c5103032610025811640d500c81030340d05007945000306942d00d40d92001e14240c4480e218041c0e549200041c1c480110342c1035a8940140941d039294040620440740514141c0140c0e404981c405200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 941305800 1250 941304550 941304557
    0x110f15030106180b120709080c0315130206030c03011d16080606040b0414030d02060622090210020d080609130f06060b041e0b0a0909020c010902060f0730 68
    0x190800306500381c0320f9090740180280c000c01141c20050484805c3c451845680c41d541ca042c5807960311004256984a0300c050b040e0f05402405103020001c041000382c0e42d1040c80350413107000e28140d40d004580030b640151164003100800200603c20340200318903008004112007480000c901d0095021264504e416007000c0420880394003054a0740d40f424195000382000c0c5214698881d500c0b81c003d46a1441072503c68043d01030401c0048a2034008103a280c8a09409841e06402200300603c54800314260000781480ba503940b0b08070340141e220004000c507a500950000c0c191150040d4015120840c001c0083d032040d280303171040011104901140421140e81f01d8410809040989450006005d082d0400344d2007070b0000c100040d0b88100f0803041d004404c180c41070740c0c0403140c0700c1a90840c544180300070440030800c2c0c0300c001c0080c0381c0305500500c0c1c0381000c0030002070204c0590380000c006901c0b0102101c020400403550000303100002445a2107840d6000071250030392001c0059003a140c0f6030461071800c0c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 941307050 1250 941305800 941305817
    0x20d2705090613180c15090b070606090501030602070b10061d0105160b0103021906050f0919060e030d0206011206050402030a050d03050a0515150c0316110f15030106 73
    0x3644403481e040307034079029900040c041340884030035100741e501c854202641c0c0032500e05800209201300920141803032444c1c0e038030761003070310f050500c24041e582c02207404881d000d55540d4000f8080c110f900c102d41c013940c42080c01681e28102410020420710700036000c803c00b84909501081080d4200035110306405078002410310340345d50800181e41502039002e400d500c0b015421642c104001c0c501c1c06450503640300321290b040585030b0346003140c0c112410380500e01c04107004114207142041c4c0000985082c802c01480d00d00d01e10b08000102c204504207902541c0820440e4511100d145028405a00d01c0346040c8002c1107658500b100c401001c500340c031750141000e030f503c0c03001c80c5c1592420300c003040180780c0020440f085e0704003009004004240484102149a1600002ca12914040c02c42c0440701c010041c1620f8180c1c0a0345200c0104e03034451900321005200070001c2420038082504a0b0340700d2070156107440b42d42c20540c4c0900401c00b5242c00070a200d40300c20303e010100f1400c0003040d241503d8243c074201c4075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 941308300 1250 941307050 941307061
    0x9010f12060306090807051509190f14011a030f0c0423070c12030b0102030d0c050d090c03060f090c0b180409050c031b030a08030a1506020d270509 65
    0x8000310740010b80341505004400080c0099080106007031703841f030f108941d4081016650303101d040b03000b9102c061554010000a500204483e14032140b001d0041c030050008510650341e203807008410400711005651641e12500180301c2031081c1240307142e819805092900d0181e1505500d41d40c40b208080d1086035545016076000f40220080a0302d0710802001c114a8100440301a003860008a0304444400b48100c01d2403109100307000d1000d4000b410380040d41480b501e500c00740e019200c1c01020500704403090005000b441c13080e004e41d1000310701410269201c80d045042078425146442c2840c90f2042c1032481200009131501510801c9034240d840c290f40362600e104048905440203076540e50300030b0804a01e03101703002022419192903207044040722054507420070180b0303242000c20302e165170580103074400ca40403401c2c481c02503500c0400740200048402000805002c6854183c02240069000c0e500420f4010b0300188490031032860740c00c040c4549101c149180c0c0003083d1500600d40030340e49076004141c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 941309550 1250 941308300 941308337
    0x20f0f06092808040e0a0501050a06050301031e061107200f01050a050c01060315050604060e06060d090b010e160518060d090c081605010806031009031707080604060b09010f 76
    0x8800e40c004000f5a44a99076a00c2d980300f10b206032840b0392030501d03007000000c81b4035101c1884400c84030240c6070307075086a10b15294400c0081c502640511210550120980051414882e0068000d52244450344910150800002c41183e0484102e0310500441410000303546401808a864009285c03245da1040c0014080300d1b9405010b8140c02c056003004008801c0158020070710290910000080049036107460420094038114030844102100003400f18550741031000040c010000701e07640c040340085040d562528030760b100f43d2040901620101c00d000640750b050364614418565881c002c4e00700303560b400d09010908030150605100c1c5c1000600c00f08501d0242d0862030380f054200400ca402d89948003c2c0e140ca81a411700c90000284420202040c250f0052000c513000e1000600200558101c1034071600042104400c00c2d0144a100d8031028002c0b410b011100d403203100d05544822160078100c0502c0103840090b04001318140003172080d580c080c1da010420400340030321890a03039291051006100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 941310800 1250 941309550 941309623
    0x5120c0a05120702060403030c1b020108150303190207050915010c0c08060a0603030305070512040b070203070f0f02180402100315051305011d0903030411031507020f0f0609 76
    0x155107160101003040b003c0c1d900450404d00c914081c0c0c40c14014141d54100440301441600c04d80100c0300e1031000000055481504419800209011b98500540d1900c0029103190010508083c00c20707c41203525012075414410f81e00100000e0b20301041c1405c00c0c501c1041c07002c5100c8612810400d1100120040c0202004000003d182e003000796404c3c1c0c01c1141ca44c2002d00000c0c0400d030046801d01f40401c0b000c2d8450405c0303840d0b481180445003440e489039960200c100b4005040c0c0720440c40709200c80343c04103030102ea0a80c1c11610030040a040c40d2120702c107001000031400c1000c21a001500200310142c1c1b200405039440004514000483c100503494920803804550040342d00003000381a02d02c071019650f400305058541003510411205586116038501010880310b20816070810b01c045030024651001d0018003440c0201030b00d609078000d222222076010101c1e41f204c010391080030041d441e1002801418002000c8102070490b6180a0503529520380d8100300e8000002528807020080700100e4085 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 941312050 1250 941310800 941310817
    0x1009030504091a040c0f02071206022215080402010503070507050a080d0606200c0d0303021e0307030f110306011b1703100801090c0605090105071b080d05120c0a05 72
    0xf0411100f001c000c080b001d00001c070f4100c0c010703480d020340300190b940116040c0e801200740780c0c000c2090382c0c00e02c5c040c0e68407242c1415045424a40030300c40c070440d20403103285603030003201c0c61000200c8407458070f1403050120355081014820700c0b42802c107004c0582d034440300300c0350700401c1c90170b04980d43d4a5030300d052890040f00c801c0c05000b070304022850115401664000703408507680c568030704585240c90b0032880d00401044281400316032068000040d00d040000744d0110381030003030070018281504c004940380c1038070441c481030324504000800c00420346c0e0907214100942c58005402c0100e00281041e5613020321000d4903090501481205220b0300c401e03034014dc03030405648030000d50140483e601d40020107401c180c6205030710024081c00420300d0641481a0580305070800c604a07a40c500e07140007030340c2a0388010451410441c0c20400700000c52a60552400c400c2502900703010300a103001e0245050400080b49401044010084009001500b05495811505c4100e005694907a1240c0c283c905205a030790 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 941313300 1250 941312050 941312069
    0x30906160f05011e0e03090103050c040b0408010b1005070b010b030a0917070302060f0f0a3318060b090f0d05151b0406021e0f03070b06040e0607021009030504 70
    0x30728820018190080c1c041c10140b0307801e1620b2030041c0d42d60001583e641d10070903007041c2c0c814010744509601c241c22064100003520760440c50300384c81d111201c4c0345a010340c000c10401d039100c429909480c02c1c1b1001410101c40140340441c01e220455444079602034043c031910484140c0400480e1070502d07282d0200080552100c402c2554071410700700e008854006040560140c090071000828024400c3c0015204000328034214286680d0001c103400242810205800349041c0003032000101585441400720340c2c170f168211035880600e440400d041110034840780021541c00c1c134808100300003584d000d48004203030842d5542006400d9001148003180c64000142151050f8100c00b420460241247e0380102e0010301d10b400e008000610201040c400d07407095a005a01c03242144008494603500a0014185c400540d110291190446450754006030b41c1514185035800902180c5d1826200d40c1080d020840d0240034146043d50029440f00142d21441d4000b80d2200800801c06204c0c1d004c58025105422 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 941314550 1250 941313300 941313323
    0xb07140705040c03140603060105030d0c060b0603510316030b1902030c0a0315270b0f100c11060409050603101a0d15020a181703090616 60
    0x43c40100500349031a50308540c180a1404a0541d0402013402d074141c4030003030010a1900740001e41105e00702c500301e1080e100165180818034141d6510802035000f00041c20146528107151000d0380ca06074240c0700620064a908a41c01780d0040718000000d5006402c103030155042401d0201285c2000b442c81c0c0c481c3c040704006a008001c0050040c103d500807004000608030b0f0424480304035080340300c2030303442c10340c1e040c0103000ea010445e10a400840c01c4098400c0040d07082e60f44e484154110aa20300791130500300d2485101503440c010281304502e412003089403e02c219003909008101c1000001c1c0c0d01d00c1c2000102e1a8103c00e006620178640d1110710060a8940c1e00c5a950b14000014107040da043d41c400e000b0100d07060b00380c000c00d002c2c6101620f0342c1020460310040c88000c20040d480034544c00c07100c0b442d000381117148102c02c0e807006d0161002a911000070b01a0882c04884c80b40145c2d4100c0180c0100c1c3d1f40800403003240c00001d490b0a001c003907070308a6070b640c0c01242011641c840e03800000c141c88130307a8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 941315800 1250 941314550 941314571
    0x703030c050708010207020123070f050d0e15040b0c070816150e03151806011202091803040b0a0c06020309100e0111030a1a091f0b040b0714070504 65
    0x403145403919000304203607140c240d1196042420b0b03100e590006400a68410643c00c03046203108804500c0e490741301f032264985041c9550302c0c281013000900c165000e0300401c41880d0100d41001e61400500412100c440448180d1000400107004034000c802c2c500784c01095034286250100310410140040c001100c00c00e1a141d000c000030b1100600a48280e01c045404010070207009625420078000001c0245c5002c0c02010120303054401d004020b1140d0243c0e510004040741e8051221901909038000c44c0c002500c01030042c0001c03010041c003042c220308418100d82044c09800b10907181501d04001d20035030349810800d41280c0360194070101900d994400400d1090782c010000e840807040c07d2a035410720080070b2001601d800c131040421503a075220710400010300050060350010002c0c4600d45001e40215024001140c2c001030210340c41611000e40c41c00714880b2004000510700100401c5030708902c0c007070601014001c28020310000a1a4201c0007a001c850244244800320203050050020040c00604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 941317050 1250 941315800 941315807
    0xa270c090506040810110406021504020105041706160c05070e10030605070f0f0519201603030e0f010c03080613021617070305030c0310050a090b0910030209190e070303 74
    0x394035807016261b103018500c1c190215000151004c94200d6000b80140c1e003102c040303c0c1048440140101c0c1084002c0201144049000c0641c100c07101c90140144034610b0524540d00b4a400304001090910510440000c00214006616004d4444400100c2d5594494030b0080c0300c050440e41004100e40c0c20001004a60369000440da0070501d0a9600d04050005440381a01d440c400d1040351304510030030310780310310260b80912007401241d030110125001d542c400003407882c04e1800140d90031000007007000080060540c804a04408042c04503540c05a07009180d00203046160f44140c010184080c4800280e12961540841d5800e400040425581d40369a056007908003068003c0031208640e02800c420320060000c1c1c00e5400300d55245e1290f504d1511402208280b83e000140310b41840140c10714082203d03100c209091000b0040a0b0002c80c0f1804c01d102002044800100003000500140c10100050381d01c0c003030303081d801001c00d000c61488058503e003900040c121200c00701e00c552241d403d00004043c2e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 941318300 1250 941317050 941317063
    0x212010e0318091003120f11070f1e0b070b07030b1816050c0304120f0503040e01030b011520210c010507080f01060f030e0d0c020a270c0905060408 65
    0x200c0c1c01d0262075a951000000a400c4c41c04054070220520143e0341c440c5002c0d0b02ca0722030110035420440c1854081d0240c043c41c00d01c6941006007406850354081014260080b113442200254078045041d41d4204104c3c480c4a0182c01c0c00509130400c030f4404030749d04500036030042d201c1e454041c02c103514480c160310320003207000400c0d40c4101c0012010b0300c00d44180c42c81082a030700c21030940f4010314034061070316001c60381c1140b0608040c2d42c0c4100143c10740c2c0001d1000c00003800100301318a2080b04940c0346041c040e1010105a0001c05540704881c1c40104542d0b02c08100c07a000d41c0c945c0c1202c03070812252490a4603090190300050384c03405888070402e400c4020540905241030000380240302d01e0755221001c03140d0b07801c10380350040580301460050015500406000f00490100d00d4001500c00001c0061031070941055560004110a010f00c402941001c981900c003400c0c80540c40c810550b07548000000300c40c50b420503440305d290760303400041c01c880c07050134168010140107084c581c070385d0744400d00980c4408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 941319550 1250 941318300 941318347
    0x81003060e0115211b08061603061403030d0c030608031209010e030703090b030406230402040b0a05060a050f040e0f10080105010308090402071401050903040618120212010e03 77
    0x1151810000365404160071405488028410610600c000c603661385814203030111002c102174080c400c0007080c540810030001d80f040702044070001e42c03003503c8003018003140d2540d00240d9250701c01c1111400740f528000300303c039000c0c003940302d000030503808083c2c04600070310140d00460414040010b1040302d848841500d94002c900e460000c1020183c0c3d010300381c3e517a200340307003008011454100003000819014009158840c0c0145000720b4503131240c0c81c050f2041050b038441032010112080902c4103604280c482e1801800301510000e18039070803c00001e159001d105d00b07000c1003080000d441c0826040f1402a50020907442007a1240ba05010200e070142c0c0e00e040f00c040c0d440f01c1003003000194080050003094120380d00050464a4200d0f0101840041c2d40880400e5401d140500c00700d0f40d50b64400d00c917062050200c50007a584541c10210b0007404440c04a441260307245a0581c02d00036002001074000101d0790444900b5040400480c3d120301405800382c6003146404041654100824144480c80015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 941320800 1250 941319550 941319581
    0x30e0d020a0b060618090406180609030e150414130c26010518041e121101020f031513020d060513051b09010e031009061103090d081003060e01 63
    0x41c1c2c0e444080c00500d0003204000700d40da40d83c0028a2030b4500380307240007d4225014030340214586030b21890500368148240c6d03007152026594106030b82419800740107200c045800702c03480241c011100c2d0200459002d14040c2c445e10442000c4000c0f0540c0c0c507030b404202040b400b12802d000006003140003810010b500e039401c2035500c2002c0061060360700300d0b1a0290580704000c0109000f01c0e0314100c9415618030080c012600700414003010740a40a0702e62100b2525440b1b058032035450303090100024040c540c03088140101d0303801400140c1190b0300180c2541c2d4824100c040040d2402040c000180b58041101c8203501500d03c0010f00c0302030800c084e0884019a1019075440d09404c0906c82003100304e900444040103140210b80302a100d4100c2c00005001110301450500c50a6468030300003402c10001400c80c46c426603a542c084c0301084010700580c2118042d0818440c154509030312500d8803040ca04404200f08494680080d1104250386070035009542c007c42c041081c1d9130280d840070b000b011182d81c064400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 941322050 1250 941320800 941320823
    0x10e03100f05271005070302220302040f0605090c0c010207081303060c080105090403180f08060f0f0705030117011401121124090a0905190b030703031e030e0d020a 72
    0x243c3d02e080c03a0f40c8000c0d103018001130089007a030b0302c4241c00824010b082c51003016000c200900310f0a110007924081180828030b06803000d80355204010881d496080202e44007400c001e41001541d440c050943d45c0854907281443e554003040c080b1900922540300000d008a1020403a01d0403003003950030300400e032031140c102045000c204110a4030006401d2207007030f0f44822110000340009110b602003280c81201c00c44056082d6031180411100000681c00001303a0307510240801003907a03042c0d07850940161841148044606005030014003502c8140500c0d03d410030040e4120302c1b141070961061050201e038a0385182c2035611003111110320880307640181c40307041d100c5200000b40d140030300409007403100c074241803010055800c004a2481c1c01510300e0310b60110320402c3c00100300344980503031031144203040040d102600302c10100c0401c44402402250080e07014a1050002079007001c0711281841082d841402c06070315188080b0090010340d000009580101d0124150060300006e038100140e1098140c0c00e0b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 941323300 1250 941322050 941322091
    0x409050321010e011e15090302044808040c0905010b0c010c090f090b010306050a1707080d080705030a1d0609100e030d0b130e0c01090b07030c02010e03100f05 70
    0x210140345d100aa00591200810441c030301041101414481c503a042c041000b9941350005021681b0314920311008100141c8110000c00c20040700f1000c0c1c01400046900d190b00000d111220040b0080c0d40d0303418401142d01141c241321008461100a0910710700900c001d40c1c442e0035010782608400340c1140d040d82480c0103840c1c061300660f44a41540d0030040c0700c0d5815031410071688003500301550401e0500d07079074582c081510380303031100c0000c00340c4005500c45d0901250068202e00c0c065240e800a20560841642030000c6907000b040107412484914203e52a0741300d8102140c0200841041d0700048151800702004030305000c1800b031301c00e60003c002e941040c0840481c1070300361060504007500c0740d002045031302020403440d17112240c0b5607006000a01e42c480341c0034081d021034a2810000c1113550054410700201d6900003074110241c2101081b45050600c155005003001e031510740024148002c280c030307920698400b0055040c40c02408181842104580c11f0311300700612003568620b005540c0402c4114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 941324550 1250 941323300 941323319
    0x20409080f0a020c36071112090117130201180803070f020916020a02040e0f0d170c071a0405120f04050a050604030203070b030601051c0c0905040e03090409050321010e01 75
    0x641c0c0f40c1740381581103004512944403050301001401d141c18412a44c00c84209120304104007921113400901c606c0e564010b00b80090b0402c8145542d04948507100010001c1019a4040b42c1000303590a0816070398468800200001c0d034a00394010080c2c9120100d074039010703c01c4a0514004050003500c1000040d10f60001c2c40442001c02c0ba510300240e404174a02400600f0035611032a1203074804001d0300c100307541d110131349410000c403504a400003030038419080c50090b403500030385600f20350f101544907d40310f0f03a980d40840c140e9900800c502400d0080700041d043c03000c00d209601e103000070600d5141e507076070441d100c1006030f410034000d860040d00c60601c0420541000b0084a083e80d80090050030f185d483e01c20100400c0e48014409410001c06010b00d0414202d0030710031080c8003051400c08a061402450000c090008550080d403007941003000e0301c4a10140801126024003050303c01244040e4a4104180f031072040c2c260b60544450f40310b00c0e81d00b1000d942c009050583d40600059001a43d1720f12800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 941325800 1250 941324550 941324599
    0x5100803041206090c080d03060602011802010c050a06020d06031103060103082205152d040b0d060b16140604150b010c0204060e0a0b010504030f020409080f0a020c 72
    0x108a26802000188040030180310000d210501c10000413600040030364550240103c1544124500d511400d0740c1400103030540554000f0f0102031008000710300c2e0f044014850103100007400780c18404901c01c0074003407000500503e03c2407500309605541d02e07600444100d00070400d5210942c1ca116042c0801901c038940401c006048a03046500c141c01d000015440407241d141c5a0046580b44200c00c000099548171401c1c110002503502d09801e48441154807400080300c8001400c280c100740044d00d5011001040055900703580076203541030b0304d8040c0081c5080040030703141c0041d400d10001081e9100040251420381136003901c2400101200c81001c22515682c40c0d0503100202400324007000404240b103550300152000c00149000d41041d501d580128048460036086040c00342c000404000e8181c8a500408034002001e00c3c10742d2900b45503440e0101d0880700d04200a1256440d900c00d030003030041031802d940840c1d900d4a0001d50740c4480070000780da01c03800700300c0013402941d038180002c41680e40320300b10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 941327050 1250 941325800 941325809
    0x720060115020714040b031e0309100c020120010e0714041b08010302130b060307171e011a0c1f060b0304081b0102220302130207120311070803090a060510 68
    0x8a100d62501c250403c8042c0403003031b001a8240c46017080d18402d0200b81001d005d21f541004000e03640e243d44403001d1014108400c0030000c02e002c0400b0220340143d91050145a0841074145a000c070042c0f05000203014280010b16014548a20440424406111805400010000c640810542551400d071000111340c04692201040380080100007505000010040000e0103180c00a10b00c3c241000240c201d8100780c621900161201c580d001d90091208080ca8002d907a00c00302e040340c0d844000b07090018841c1400366040d5114070158500718180d100d010364104521940a03104559a4501c19441602003140001146820090300140042d8140222402140c00110540c94003c090030055a031080f44880c0004640d800c1144400ca50818005c10f20758a03600b0203101401450342c0104105500101c9001503842d1040000400058108003000200d1409040114400449100d840c2e44c0740a040000345c140b1100008000310041c0214182100510882041007103441e110044480d11419003c2c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 941328300 1250 941327050 941327069
    0x1103062e0509031009150e031611041506050c010501051c122d02070e0705030f13060903111905030d021305040e0106030b09150f07200601150207 64
    0x25058451040d801003102c024083c04603040001d003140c9840449081500640e0450340c4444c860040c1c46141c000c0002c021402c0001314100a45803d0302a00100d40f201c000b0031209092805100c0368450340c001220b1030396880b4101a159035103641c06403c0341d03c0091840c402e54604400403174981752004000714174060b07000f40302644c170f11b165035400940003000803400d061140710b034540700d111030030b4110300d110055140c10a00580c80440001a1500d00150000205002e111042120703080d032000c150b80e40501c108802042ca520f07404440014401141c002a2007582482d01000c00c0c540c0001c03020765010f449000b158031142c002e122076a501000801c00030643d0f0000c00c0702d061000166000703030a982000400c0768a03520f0b560f600180031100b4048044072165143c000403c180085202143c0d07001c2c00c144060180b021030409440541080140f5103029034803c440410079a5205100b402c540300c42c50a444000241e030b40301001d940e20024421000740301c80101030740380201d102240d04801c8412401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 941329550 1250 941328300 941328379
    0x105160503030106112b030c05280e090f060f130e06162105070921030807051306030203180105100f05060f0d0e190c05010905041a011110110306 64
    0x447c09800a0711201c004c108003806800c0d078a01d48030a03180c0285083c002d8403054000d00c0d000c040c0450100f40c401c41e01c03811781c000070040c100ca0b000c500c10758411000c0307988480241c2c003000011007840d40c041911043c00e1403c82e440d02e50140018046003c1e0444561641e400c1d141c0700300840c0c058200000c0202250203089644203152410340103140c008807182407a400e01f03502c0307402020045c04d4101800843c04040e541403014943c2200b00e0720b421010130b02c1c1c8140350804039262002d10709010701c904010541d0000000780d820061803020580c0070a0760b0024002c900b01032030140081500b0b401341590b03400384824005802d00c0c100701100c1c111800f4884c01c81c1004104e455440042c03080c03000300c01c4107016075541c201c10544e84284075078078640721750440c0c003505042c21b000611010302d9030400d0303004078900f88107101c10144034000c10034644000d280400c0e1510381d611400341400364980e90084040c1c03d108100d0326603401030707015521500043e00d03640b05c00b1058490700034498581c01c81d02d8403a0fa8504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 941330800 1250 941329550 941329633
    0x6090501051e0909240f0a270501090c030b1501050a120506060f07050708070801060b040e1b040b070201030f020a140f0c03030a0222050a05010516050303010611 71
    0xc3e50f440c1c0c4455008281c6415050314503100c2c1e2002c9100c034680080103182001c02c846140405041604101341070070421242500044562003003106c80745c41d01d010008064403000304038094105002440d8000315096445a8900c1e028a44580545054104d1080105242503c0d4450f10070341d0915449940ca046e8482400141e141c02490050001d0b508040d0800c09500c061305403c0081190707610450090480c589030020343d505100303039608104000e0341003000c1000079007008419101560700c8420f042c0919100c040d443d50030080b003002c4410345103c006c500000c00740801c101074100e2078000e072803c0c4034043c3d1141083c0c0880c410084840041100c00030604558580d00c8003810342c1c40003510705107252818100005146d074204541c550081600001c0158410b444100c0d40c203050000c1051203d00d441c14200055400072007030051504001c5c000c90010130040380001d2100e040382c0c019003540d55a5031149801001c018444201c0c00241c07091881806452900941c810249002d503103100980e0780c6117 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 941332050 1250 941330800 941330809
    0xc061b0312020d090f1b060206011d06042a02010c080603070902030414030304110a05090f07030c03060b271f03020a0905030f101a0112021e0d06090501051e 69
    0x30380c00d18800744d6a030500800010004190016451b02440740f4001450324809010100951500b1000c11500208010001045d0306d2168400f501d9081e900034081d6a941d402050040c42030034490701d2501030104010f80302c80c42d155800402030320329a000b84440c4603100000d94034282c0c03d80f040c03500340e405420108810b0b0826806150024820700d0f80380e00742c0c18891a404d10f190020345065502c40c03038100d429181403600d0ba8855008001c1038411400515000480d1a01144014464014161501c07421585648a54480400341c01082c03100d03a1501181d00140400300312006047c0c003000e081350924001460030b00c04550842021070003000c7c211406200c100e010350803a00c488401d100e009080410141d405000c02242842914000c00c0120495005102074030092502100b9241500c4070102d0281d03400140342c0c0805141c102c0140c3c2e50500b0903e0380100d1084644c4140704040081482e00d55200300750060006c84951000c2404030340d03218010000001c00751820414103101c00c0d16800128141b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 941333300 1250 941332050 941332057
    0x11d090403022a03010506090c12060112060f2306071104020912031e0a0c17070b100f05030705090109090c2303160e01120606120c061b031202 63
    0x1c2407040d20052144400540030070038482086050000400300100043c0c2800d20800d076026108a4049100d410903c2800d81e00384150307460f00c0040000c0c0c030000b0301c20b41d0144c2c0916900b130a080308104a41c55940d410702008801c0303030140c01080740054451a240700b04c4001d481c440d03950024070030751828800342d5a16003958044a60590019024020300049907980c0c100c1d04120316482000e981c1d0383c5e22044541040e5072051038041c00901050000c80e56880c0c0c014a90b111041e030000700e010700000d82e01d03090180350140071001490f007440e038010410004080f20700502110f81145c00450065160300806417110840d010389a04070706458010000e980c80b58011300ca20b40d009045800003a40c98a1107444900f84007002414044480602c150a03420100510500500b02d0701520440360304143c40000031120600c00e9a00040703810340c80c0070a102045d44050010601c0310880c440d9406031749024050020144520004030780115210009824000aa00c40465041d41e900d056464800c581400130f40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 941334550 1250 941333300 941333303
    0x306060417011104030b0103031803080f0d110301090e0f070e151201290a0506041203020f0f1c020316080a030f050f090601050d0503070b041e030306090605011d0904 73
    0x10740310f1a04010400385075000307101540c050400512250706504000d050720030159032494204801304420001700302090103585088408201556480445584c920050f1170001c1d908000200300000015814049034081e4815040c000280c40355030740701e80b02c1c4030b03113808031441607103404042070000a00c40004c8450640c000c40c2c0051807450340d40c62114295007110901c5616a50000c14007e0061040502501e8001e00f40d0003121500c040e10b044c000030504c0350103280b080d5261035005411400070540203000303020154851030202e50600c1d600000c01642c078030f80c5280f180c58841b6185c01802009201108030390104207000601000c8a5159480d5030b460b500894022041654070002d044c6910140e01034103005881440c07009940b42805c0c00a02d08083c0c040e401f07184224400805400047c10200a0b102803a404c0055449580d0752400c0c006900c49406c0d8a040c00d440f443c2509070308060b055480201034072002c000c20848652208015100340c410106840003141d0380e00d40041861074890034140c0d115 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 941335800 1250 941334550 941334553
    0xc3308150d0f03030510151b020a050603070f3c03060f0806010504141006031a09040312050f19110f0f0415090b031302030a02030d05070303050c0306060417 69
    0x1d041601c0c1d01d042c01481003400c0780082d40f24030610000018840c19140641030902e00c00e0a0340c44142c0000d415250380000b08040710880103100415561114564402044090300881d80c0b443c000380020240a00d0040a0300800c3c1180e8001145410540e01d50850701c98820111645092058580d950035101c01d050b1010141c5520010805402c0c01c94114010000e000080115505000410082e101c5400e00b008426403481c0400030102e0008030860111041d80c03d00040d4a141a40282210003c4407580d58000e48540f00348001c15504c01103203d0101075000f800c1100d6207402400700c0c010581561200d822030362480081d6401d001c0c1c0d5000098681000d00090b140c02440891894160045e042032104e401010030100109060702c180180c1074591362a20186c214140118034445000280c9420181c5030340301c140da4115201002404006a0000c080700c3d0001a0340c54000c10341c0e40000e0302100024242f82c08944140390b50001c1da0f00898004103002c0c10141031404864103810507400d01d1805 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 941337050 1250 941335800 941335819
    0x150d050c07020a143f0d02190501090c060f03200a0509040608060108061f080304090c0e090a2412020d0c0b070c030611030618090a0c330815 62
    0x1480300d01070741107509a1042418043c0b85c00614440d400044028480062503002070405850042d0b01084604010201103007594186071903042c404c5c0140407601009110305031051012038030726040440c180881c0300c00d5900340554520a00310300701d206207407880b07404151021702030308001d03c2c040d03009401c2c1480b02800008001c1d642d00a8685810800c0e4000b1041d0b420010910450200550307940049503107403400042807500e00005142d8078441c510a0480c1c4565480e80d009110b4814070044640b050020491140c80c2861090140200300130700c1d40b0905c012103442a1107880d10700c168010101c9003c0042d01c960038000390203100c90348070801d50882d01460140000f04d40002e40728003808502d0b00403000b824200e41985429411640c0b44c80103480418018000c2000990301d00c4e00c0064071002980a40e01c00d904e5642000740303030400300c080003000b10404a0000ca10042c184c0204a02c2030340419450b105094000c000f0b044410300d2401207000220781200103100318003621010142440040c00e00b405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 941338300 1250 941337050 941337079
    0x408090d051605190609050f040f020c0c0109080d020307080d0204030c06020a151e1d0106060302070203060703050606030a0b03030f07030302120c2b0b150d050c07020a14 75
    0x108008041d51142d0752840082c28001800d101c0352141440d2100c04c0403141042c1003845c05400c60f03c00388560b620541c58020100d855490300c0e005901015150b050a5480d0942c08000c00e40320640c48004c58005441c0c1140000ca4003000511140458080d401a40c80c1140070b031100e101e071b58070038041d1a501d103408000000015050001000c02404242d0240010a005140892a90407071000e0b003d04542085015108101100e8400710750304481c0c08001600850410551501c20041542c40c4107540ba200c40080d041e034140c0c004000c881c1c40cc5060303a41e19580c01505900300c5400362411604031106000203001d843d026480300034020707001405c9900b041c1e08800045c01c594841c100c2140000d0700440c24050038030300d4488e91074010651180c0a0b040600030784018607103a10100445c28410368241900c00c1d010f5140c4d210040c02d034006828099001b039200403e5003150f021b81c9014000c3c46c5032000041c2c001c06190255214107500810760541d4500e0001030180000c1c51200c0f050313100501c0b040d00007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 941339550 1250 941338300 941338303
    0x4060810081212090105071b140f070501121b05071401090f0b10050609060d1409031213020f010e040212011401020f01090c030f1514100902070b0408090d05 69
    0x4400300c031080e055681e95040c038010b4510fa00d01030080d40e85a030401d000c1c002401d0300801807400d04110030f40c17000c0381e951a0341069000b0044091580f4090b005042c40081080c402041e038070240d400c20780b43c2030300c64289144904215002d0310160990b0907098114118294402d40041c901d0750b004002e0400c0040801c03a0303081c00c442e5000403c07903c0303140c080c0c0c0000800009842d007545c8407202c0da000c4000c4c50304c0c202c04100d80340305002c40c41e0b20031301c400203c0d60244c81c41d41e44000700300c542d40041200145089050190f8950100210030002c40c400400641d81c40c01c85201d9162403680640f000b0004500040155a90b44995441030380c0aa028004a8622450524424002e02550303140c1c1d400503081000181c20405e001403954001c0c0d041208a0022070301111141003141d91100c01c03082d8901e100d0404080300b40140184950b501d0a100b44078612411503400701d40640c03692030082242680d150030342c41c12813050240041852215100245c04100390340040c044803c8080c110440144441d590039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 941340800 1250 941339550 941339563
    0x60201113115051b0d0806090a0e062403070f05010f12020c071a070f020d08040b030c04030201081303020a060f0f110d11070f0f03021005040f02030d02120406081008 73
    0x5001140703c460781c4d515102c101044130001c0307010300100d000b8100d0040200100401860164610102240e03588101d07610000010f116a41611401c1c00c0066129140e40f07100d03c01002d038048000c00e903580300d103008900d00c0200c40b56040390010a0f0703c1c240042d184200c400d0080014024551058900f00c040c50008003002d02c06440030789262800c1c651201d104071142041002c4005080c0105000a04800d040c40101501125620a001da041c0b600000300d10840d080f41d06100740103c14800302d00743c0c89002d0010b40b40300340c90381b03059940c0d161641801b00b83c01c1d060250050b40024068004583c040e40002d12181c1c141c400407644075000e03040007055420f044d00c03284102100042c80b52071448640302e03069215a50070070840c40c000c40e0780c8610401c185040700180806d1814141181018000c001000e607031712000d03409000a00d8a420050540311404100b64002d0107840c0500412601c007261801010343c10400c01da05003402c0c00300c11240084014540c901d000070a03180030075441010402c6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 941342050 1250 941340800 941340839
    0xb04060305092112010f0f0933151b02010c170c0d02010b030f0d0513120804212f03070e011806080a150f0f060602011131 54
    0x6844d92482514107103046507405038041200d078000842c1c203014112041c1f58440865140280100e0f0340441c268031000c0c141d099504c58184101040303016079030000303d20b0a803001c032025800408800300c5905000e40c1d05866403008100905049151080190301900c00e40c1c056902034503060302e0003640d0340503007106070340310f44041c0d0100c2d44441d0780e000082c0e0707090042c2c01714000300b9405810b10344520b500301940d13105030320107550031301c8801303c1c0004101620004050081406802c1ca20341c3e00d0140c00c003404680e000380900761602c0c9105029910181c8051140c2c9001c0fa0b004100889030300b410080004041c00b903810a10160522803060710706503500700035107009080d6150951f5441c4d49011004610710b00f411070b42d000304a0502204024002c00820a48009600082c0064032000127265086c001d0010244150505262004061006025521031030603902150002c21030141002204a02802140288001d24510350002c000b00b142d100c520504054001e41030b0b8900d95110540e00b0700b094001201c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 941343300 1250 941342050 941342113
    0x1090f0f0618060e010b011d06031b0d02070308070e21070b0c1005090f0303071b021003240315020c030903060403030e1608060a0509030c0f0a0b01050405010b0406030509 75
    0x1907113684d0b22000c1c401c2c449546400d00700590420b200b41400740b051520f00011900c941e0b03000c0001200f10681900510844d0410400760f903880d80c400030720500a402400d0203600088103100019031040c0600429060500000c0c003841d0308004214820b00200844000301c901802082c5000968840c40005800800d030498041c003d1900c201007030f0021034000802c3c4003829484000814103045021088030342001080c03500140300603070007a0001d02100d182030025044400400030b00955580751b4010f6192803203041d20281c21441c1108494080034460001a04038102d00b001040f0b0001554010a04810184103880c10311403400002400c1620464040d804071b920780c40c14070a015001c0c80f400004052142c81e121001e0f04080e16141e40c2e9200400b2074a03c55555404101030743d0f0f0400079143d502e0922000ca072801e48078400565203d9170010700c102d86e2642c0280011485140c00c2c001d90b03068a41c41411a410306207064001c42c007414002e000c10119021b04c600703610b10741e0150541c18440313014000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 941344550 1250 941343300 941343311
    0x603050115030209100e0406180c0f1103040b070215040e1b0339040f080c0f03151b070b04020f040b0a330c0302070801090f0f061806 59
    0x10300c07900104401d000e03a0082610400103420a9940c0700d07280341c0d114900345803c588950605011400808140c0c00c4039180314000c0003090040201030b001078240031000d640b001141c54003202d09039060441c0c01e00c0c031303c0e80f90820701044c4952000311010f809c0c0b40d0300003403032000360761b07061149840385a0203504400d507030598010030450300e5600e505842d060707600200c1e01c00d4a103261074442070340e022040701082c0f9550400c200c6109030198075241e0030b4000c4241d44468a0791596034144140040c0414810400c1c18050a030850ba51482c103640c590b10101da003c4c1c040c15402c3e0703010340e002c220138000520281002988012810903078504c50040d1401c5c611170722640c60b2504080c010480802c80c4204460b02c0f4078100103400d5055202c400d5007070300711610690002d0460726491120f24100c9070055919158043c0c0c0035000c0f0807541d1000d082c80b0581d020b50281c400c06a20385291a007a5004008060020b1011045c030000203521840000c09082c010080040c0182494268186000e80041c2c107540c96501c0c0c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 941345800 1250 941344550 941344559
    0x2070507121502070302030d0e030306040b0a1a090a1d040201200c012307050a0209091c050a050d1505010809150c090109080a0507030501061a190e0a06030501 70
    0xc000c030001608100d07444034032004090303071640c05011003241024035842d0041000000c00d8020070594912443ca02d03014005800c01c00101545d075003040320010312071401d01007010010304100402314140c92982c0030700d100d95141d40310948000e80c00103003541c0d000a89844001801e0720344015204203c0310300140d081c03030b9040c00c1c000184001c01e54880c0d00c92183c000540d40010020001d0341d2542120207007440301c29000950312100592403a0821150390038000180e0340104403000c1074040180b0b10171182068035495a2681c1d9070350b440c9008030401e800310f40d0f0744c481c0991760080010782211903091405c2d078503200c061820282a11132100d40003020541d281c000380265a00074802c41d13804040c520007400c0381d4901c00c0340302d180740c079010b4442c0f00c400e0310014900359982d1088d81c05602030092002182e025540ca49080383e80d40d80d03644804d0382c3c1d5520305680854a41c10080d00c401000000300d030840c0c00c10740b85038554921007581c001d00806205403140d0803400e580300d106c010002802c00383c80000c0e096140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 941347050 1250 941345800 941345803
    0x303011d010905010b0a0c0203010b0d05070315020c070e060a090903050a020d03200d0608031209060c0315060d06080105070c030e100f140d0603061a010e030d1101180303020705 78
    0x40e0800400380341403c0042c0031351100101612044156440c181c00039070380c1070020030f00409820658941000c15207410405005d400520b01c3c2c1140c1c0320b20011900383e000422024200d002d10603a92543d82c01c83c3c1810000340090403000745e001180285450307407a81ea141c4480003214492001200801c1020800d034090396014001c280300741280382000e0142030600ba0840401c0e0740c003040d88016061022519041da614194011806080e0041c201d0341e4680c0400103440300c400c01105c1040c0da500c50480001c030b8820090003a607000da12095002c0900d00f1407241004155008290b8041c2c51070748c0d07440000340c408424001c2d64002c44090f02c80c50705c03460145c107004000c803031f409092034024031540748220b00709684a29160001c0685181110a0b801d803810682043c1c4a040d4083c08900d00b0560048103001407030384007481e24005841201001d42941005650344941550080d505400a043e042e02c0103000c0c901009000d950720000060408a90041944243ca01c0d0390550000758007003680800c0050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 941348300 1250 941347050 941347109
    0x260a030b040b010e130e0304030c0303050c07140906060c160306230f0a091401110901090e07022802030a0b0a1d0c101b210c02030303040221030301 65
    0x8003880d1513202034055501080c0d1600d1601140701e030043d42d54402c80d15101303090040d20007655201300c100584c2c641d84d040050080c0c000301d52603a40707030295190008100c0011502140c0c3c525000e081c0703104a564800801c22907030030201190f01c01e0b0180d00c1042d840503182111000143d8030440002507401042003500191400d44c400400e40700042ca800d001007808505004c5034003e224110201d422800c510340038285d460300d41e00031500b56003000321810350f5200c0301024121201d020ba80d4601443c1c3c0d6018600c41d008000e442040158201c29292540d002ea4a100c2802c660b03008480d0001e0980e131680400c0ca0015007407403e4803503620356424040d0915140c040c41c0040e0340302c5035841150540c40746d0a0b54454032038065541c8100902841d10003160300a03501d403800403040c2c100d000b40300c1d001d90a210161003c0c44000400d41c8039109050b4903070a00a0490030482c40e0040c0045041d030b49ca07039090020004802c6d0b001d291800421a00c46100d410400086010f812044a110b1030042a40317064402101c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 941349550 1250 941348300 941348321
    0xa05091920011413080127020f241801050309120a020a0b01090b010e030706020c0909010902090123030703031707180b0405130612260a030b04 63
    0x200080c010400700e400440e1034031030000661040740c08400c8500c0166a54092111001e14800000c00e5030071345004d001c1c1114048840e1000240003403030354030012210b80a42c04858000c0d80d6103403200c12015040c40080c0040c613000280103101a80200d0b8100d101745035079014680d00703c000008142c0001d811207040049440c40a08cc16811403c24003c40b544546842c0b22018081801046156406d4420440a0203454015922640b07650712031501d207000d001605103040c041003071101340e4206400d000809000f202c40a030f0203008020700c9902000701501c0c02520200aa40d2502404005030303a803001e41c00c1c001d01c01444521104072010050b03041e84480305c60618400c0c2c003d0402040401d400012070303e29a589900c0c84540b41d0b55008050f1450b0609050700746042d42d0990000c59841c03062030090080d90f01c01ca8a010000000503164401e0380c00600842d4841441520154009002e00d40c81f0030315030020180300c402402c1040c400400350b403ca9103261001075242d10b0012164140352240b0070060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 941350800 1250 941349550 941349583
    0x18020109050d020306070f120c4e0905010203070819020403050703020904060e061501030e1204060c0503161b060c02031e1213061119080717030a0509 66
    0x3030302e2a07000a911800001c0000040c00b40152800c8001c61107006400124800800c0c10480140b00d0080100303506201d41c00803202d40d1102041c0b07a0b01c280846d94050b1030b95002c40c0b845c0c3c0001c07072103c482c44d0140c00b1882c103011201d0304c0301d5901c4009072013030000e91311480440d03540f030f503580c40c003040c0d640d2840030702c0c0b5280b01c84c1901c1004240007280000c56044140c0307805540c410301a07103031454605c00510001301103c45500481040c0800b000700d0104402d4038000907a010b012004146204c9500c50f0400c1409e1400c030702c2e08200030004980a030844000031400352098034280141503810080c2017002c1c2e001203072950380801c441040f0608060303000014142500d42503541c8281580441d40e52001c00740201d401844840d090404110200100144d92034460040ca0b259115900b0344010308a040c010200413902414164802c5a03001a106900088084809041c0d100c152103554669101200c00c1d103161b07080008540c0711211074030045010340c51218002072146801d0034a2030810002c10004590b2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 941352050 1250 941350800 941350819
    0xf092303160608010510110307030e09060612010e07140f030105030118030512090c0301020c010b030c0d02030604080d18050c040c0201051b0f0c0f060f07020706120c121802010905 79
    0x7a00d520a01e2603056032006c3c0d800341141140884107503062000851016407a100005100003010341c0600c070140005821f030f9078800203841d410204482d60194140e01f0390609002001000205456112135811910f030382072421850030076041030780740caa00c002c0c400044280b0000042020781024803c03007801c01442041d400e20040d00341e600411074816580d1800d010b03a903080c0031a00d41e0609005144c04401d004000315039906d84615080c2c060304111a4061080c000e100c4d50b0b01d80f504009126800c0150300501901b41a80e807680c588020741c00140e0034602d5261758100d0019400d400d0194a594540203500070101240f1420401050b10030040c0b4680440e41000b0600034401003000f90b00340d002070f0300e0401544800a880d4040c401d4040c00e80300204920591082d00c542c03540c045080703401021207404211459441e41700581c1d5070812441740c0703030002c3c50b071100f01101000c030340e40700022010192404040030002911400140d030f5030000b040000b940414420400c543c1c00030b41200007040305139a812035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 941353300 1250 941352050 941352059
    0x70906090b180918030a03061403030a020a02011b0209070801051e0901170a120302040e0c03070e0424080f102c07090e0d0f0318030f09230316 63
    0x10b0360700410945500910b5040040780c0d00342442c2d040050701079090340131a9150740d4001c03002400382c246032003007400d04028a030f0350003440d0138003200322003044155400801300958075900465808100300041c0e600c5c00580f13648200183d4468003040d000f20340039910701885504003010030000c03481da00445940d43c0c000394045111a2200d140c0c0e141103035000000c40c1032007903150125500300001175500411142c0029070302c036466a0142e0142c01560011303d0980d10941d244c1043c01d40320300c03007a50941c0100b6034110b915852858076030485103d2040107009840c00c500105500301c0501a15004042a901b1240444041c00c408004450226480c400c0600c2206055880c0b4224400c4100382805000b010720031045058004000c407200812340744000b00510404020300355103500754406502e0001e4910907104030f800707109002d064101d06650800c0c0220030702c265002d546c036200c1700522008bc007400880004d41d444245210b00f034550714081b603900e0a0131040301007506012921441d5003082241000c02e00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 941354550 1250 941353300 941353327
    0xf0506010305101b0e0f06070803010806011d012102040605040e010e0610050906091b0706020702130b06160303110705011a1f0503100302101115091f0f05070906090b 73
    0x2205103d042d030309046c1e1031458401045140c8034031900034140d01000400003901000010b0004e04075130203044d8001402d902904140114502071252081ca5040300381a10704552a01c0d080545a03440204000f403183da445001c0380a403210b403120b6500c241d40d2401c1c2c40c2c40c600e9081c451186d000041c8141d8034103850501e80020001c2c00f01608041c090540d110005400c0240c0f107021284000c0d40c020141c0d01c414041c13600b178010b5800041c4c228002c1d01541c050081c51b8202d4003c2d407c14260003030540d4201400800318601c0786001103000d07410591103070042c45010234614010180d09006400104290b4041d0300182c410100b02e0818501815206c000c09803e1701044d00f0808524045141c181c3c0d82e61150006803020b44a03680010354010200e010310140d41c0d41040300510040100020b44074441c0c0d10a1120380d5510048600c040d0369048692546c003200d0b82020401d440b41c180c1000046c13269402c1c610342c01140c000712a41801300380c030000140540c0350000d000c440200540140a03203840035086111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 941355800 1250 941354550 941354567
    0x90c03061508072904080a0803090d0207050108071d0406090209040b09150d030e0919140c0f0904140f0405150c0421020d12180f0e040f0506010305101b 67
    0x120b000801d1304141100101420840d0001c0c0841c0049403400001414540078950054840c40c600b071090500c502456400401c038a0104c1d10140c54844c5941c1d10b83c0000d03200404102c000044004400c00a5900d0f030b9640c0c854400605085100141c48280f12001c1c401183e150301c5c81d0301c1c4144908820000008900c088180c0c40d460152600090f03d01140b4055403501d404078400c986c4401d0040800000721a00c1402e618400715800083c0503580c070b60005280e034000b0903182045c2040c0200040b40c042c1607100001c2802d040042c20000d03100012035840b850304013003034030b00302c0813403005500780800d0080c200070000b04040328244030341103800c01e40300c03801d8035103c1e900c40c114405059100c0303040320300c1031541480c00c0244c0180850b006402c952600c50102888000b0b00383c00300c1e00a00d03080c540c10066048000a541e0400d640ca103500781448000e8041700340c014400c40d405086810500001082403100c2802588148004c1c920041c00103117400948440040c05404170081014804031103520007500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 941357050 1250 941355800 941355839
    0x30c0705040b060f030f150f030d031e060305010c140a0c0b07030e10050105190f140a170a052a0d02210a020f0102070b0d0e01090c0306150807 63
    0x40802e21200410b01c28020030b070300200e0000010003000340d00200c00d10700e207115450710300d209070b00c085150003008211a00c0b401c3c1036806070312800c2c1594507280242c1c4803016016101b500c2c4071441c44c030719080c03d09a4150741c00450307869440382a0381401035049680c10007240c0d0110703442400d100e4035240c01088600e0f07500c8050100700312103000c00c2040e4040e03400b44c0001001142079405041540c00b550340a44801e115590240340441424400e00e2480000001603400b042e02c03509201d480e280310503038098113083ca11544044800000200d20707a4000d01c010f420704040740948500091801e100c2d0524190745003041002106101d4540c4c54500018560401c8404543e03070b6041c140f5900206d09144050b508140b010f55031002d25100c0010300003030070400340c0d2089600c07101d03a810040049880c5e100d80c0c4181c1d1900a0b040c400320146031001e400400c0d001050383c0001402490380d46500b00c11010690003070303a45542d01c000c0a800004804140310141a201d4020100249004040080d480100c042e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 941358300 1250 941357050 941357059
    0x3021302190c0c03021518010f020a150e062a070201140a0c0b0a062c0f090c09070929030c07031b03090501080f01060f0c020102010213080705030f030c0705 69
    0xd08a0801c20f04460302c0c0091500035084490882d04100b55074005d90150038070315540e420f500304031001984500c1d01c0311380c000c4041d1f019006100c52035980d08c101c291040c07a0000c07160b0b00d810308044038107410800a40b0850001004559244910581040b0f00840c1014064158810403100002d03036000400c4813550b44100f9030040e65a031005c0750840d26090b80d030b00000d010300c04030070601c14200e1079604074000f230302c01984001540186001c4440c02c204410842680210001400a03004407140340341107500090620039203503480f40540c0029400b00c030444201000c07410710b91041c440b082c02085510344500d5440c040070712400c2c14603544600f5000c000c000880305000000d40c1c2040502c80d20700e1401d028034400b000c4250844500d805421284103014a03400642c0400000d1a86219100900d04844c07090300d800050050550084036003100d00541a4155034081124003509250914000000c28589000c0c0c2078403810700c010181041c01851300d0110562041c03080b01640711001c9000003c80c0e00407038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 941359550 1250 941358300 941358317
    0x10305060f1f03031d06090a033302070c1502120d0f1a030d05030f0a1a03030705060702070911040b0d14040602030604050a090305090d0204060503010c090302130219 73
    0x8990928840004180c042c2c034000c1036800020940c00031040d00450a6030155110100c0007081801168014105240e07401303d6003e02c10000300c0d034940f0b40030201c1045180d510f4180705108a42426581344008122840740c2d000840e0018448241500d00141440b00300e48404d0094000009540310362070a00e000c620040094403c95010550740107003110b01c1c401405021010140748020103601d0503540e00740c080d0080100001c01e86200c0c80c200ca2040b18a2220250251903420642c00100000c404070840c603150010042540d98081016094440c4240014180c40c0391651001b0704010b81030380303c0c4d01543d0602c3c8404e007216038000305440641c3c1854035002d40300e00c1c0e28480e0310085c3c5038402640c62007030620002e00c812300c6926001140b140c1026a802d1000d6101c5510140031100c6445001d00024070a0000e00d000e85000100704141500003400444c401303480e1400a8215007a084602000c580c00b20310801c114201031003000c000c0002c101046080c403003500c00b2601c038581031503000d0040040d0342 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 941360800 1250 941359550 941359561
    0x70e180c100f030b0301060f170f0d0504030605060303070f060213080f030714100e1b010903020907030513060510030201030f09020108041209031205030105130c1202090a080a2108010305060f 84
    0x1d5014200805170002c00d00c502a90710089e1940740149104030484501035501c00d1258003200140e442d84800c642c0e03460500e004e26580f9044001c10002d00416450700007013001030085404c06500600c410300403140142d0f1800e01091101c0440389d00d0340304883d19003000c110303010515404000d507407030b00e40c214900101d0b680c0d00304513050400b80998104424545031106600c0a0500050002e503210b4152914810820717036100152000b103c0d5100003588001854005281385200750401d130382200c481149564103160680d185020340f0002c5890350341031001c01720704005640c1d0500441c1030030b40c40c485080001c9003181d00020070600004001030320690403010a407420510445911008682201004140700344641000380190b100f80304040c425150503052181030f160500c10040b000c01e05840d2000c1441e40e204d0381d0f1010f908040340780e42c0c5c40340c2c4140000440100034001c1c01034543c40fa42485620040e0340105000001d1021094000c0002c0d0390010700000d54000b88850308800c070340c0c44d00507841e641c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 941362050 1250 941360800 941360803
    0x90f06100507380f0106120b100806101d04020a020f010203090105040b071e0e0310060b0406110303040309050f0a0909050f07140a1403070e180c100f030b03 69
    0x90020040255007101d4210354030f00014442d4548042c508440c103d501c4880751404102d1000c00d54031940e410b1031190040000030b0090050100e880d10142c00031548203003000c001341e0304802400f03000c0007146021b000c0280b03600c0d0180018038180554140790520040001c6616030070f4404801f0341e401a43c0c001080c0103018000c104900348112043d000b50b41d64500809a03502030001900d00700e0b080c89091380031a800070300a282c180098400d8202280c1d902d460601c0c00c5403404512101c1541500a0300003c030350300015400303960090701400b43d065940380d1800000504061b980354010405030410b00c1400006540620094200c0e1070485100d0100d03601030b030000d44605d41c1503001c9960306280996410410901007440d0b42e140000109442001d6940c6806c901d080004106e4142e0000702c00a00f4003480e41c81003200040402c0280495546076100c248140141c0300a441032110f0000c0e445090b101090108909010f0355400e448409004840c9800900369400403c1410181500c480c0d107158076440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 941363300 1250 941362050 941362057
    0xa030807060e160902120c090d032f15180601060e010302120f060139080d0507020a0501060f0e06061e0301090e060121080309100524090f061005 64
    0x4100c0380f0404039940d1380645100a6100d020440810f490410000e4601d039041030548241c404044c1000340280e6140d60116a2620f6029403c950042480300382e80c15100380000f0300c2181d0a1241c004c00e4902c0c00c1c2210b541000c1d10051200031f000c0780300031007000030410200300941101da481c2403201550110030700583c064020001d44200144840007004480556020300b180205405c1c1c0342d0701c8170303107680c01c400c45001c100840341c241250b00c000e1840740f42d050000b04400c0340940100b86507030138080203510382d100b51441600c6600042e03002e03082c90801d01c0340a1040303900401300c3c0807009085c0392800c00d04441c004c0c402041d141c071031341001c9081071000c0782c040300400d06070030f4a4010039600d41c0c45404400050101c404080e44d03034890040042030340c0c06400100320340d1000080c900d20301d10321b80d640c903100d00b07034801042c4800d140546031500d103075013043d4000d55009101c40f408a40c0c6003400405002f41249149150600c10980303081402079510210100b0754004900707507101031080700c2080003500c0a10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 941364550 1250 941363300 941363323
    0x3030809120a03020901030f1103070e0409050f010b100315050409020315010308031e010506092b0b0a2a0e03160b03040b16120209210115050a030807060e 68
    0x310002030000d601c540c9135000b0b00d03030000240c9040011074500c1e50200100d480000210030024010070100c1c525900801c40c030704c5007100061000c5099000f03580d0301d40c103204035105c07a009107a45030401b8451a01d00a0a46030440c001441c0810030018103c25109407030096214407030085503140d08080654400707000342084042c03409032180c00c559403407a04024990003250401043e0186c880c11000c0e007550829814100c81e001400d40381800d000004024040b0f1581c0012608440c0008124012601c40141181160702508600c81c51345400c00300201951000d486a00309100b400e503054000c0260310395110454005407910318016100400030a14040380c03202e01415450044600080c0303000c440c80194440c130b100700c201e103075691a0303403464040024200708014041015151450f0610000e036001d0b19080400404c0c214054940c141002c00004a0780207a182c2c594444482c0b1081c0b9600e00c0c00340004010582c2d002004d60315544402c4214040c1c8000140295220400503450020421510b246070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 941365800 1250 941364550 941364583
    0x7030f0c0806041203050c0c1b0607021002010c030c0c1212150e06130504050d0e03070b0c15010509060109091d010c110c0103020702061602030a05060901061a090a03030809 76
    0x508003810300c0412900203010304c2c0c0000742404001100a10b02409480440320070f00000d01410804e80c00c100c0b282800024200e402c20014011900980d848003043c44a41440e0380000a0340340340d903940101690000b09404080c810303c6980000020011550b580c1d018146285c03002d546c04419102c103010b010414808240c9082040f000304600d004400c105014880485646481402c20032501094075000c035405001604400507070820f2501075180d8503030411000b0305880301c194907070140f840581c1100e0001110742e0710201080c10b4003065403089901401045403040003901e003000000b0400500c80c0100010542c0316842e98003500f50885800c01c041c1103241c0240010725000ca40100f030801100c00c1e11999100c1c502d03146030303994028030840d070101da00600030071300d00070070f00d64031403840c4c0000d4100f2a003620410448601041e02806a14050440403002040c51481c1c0501d01c2c02c007614102442480040800c110070866849414401c03c40b0b6040c100b40340346a0321102010304100c00c1c1c1c115110760 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 941366906 1106 941365800 941365813
    0x105010b12040f020901030b04140a050c010c0c03020a080d0f0e090c091c0c08070e0f180f030a03021312050a03031107020411031608070207030f0c08 66
    0xd008241050101c0002c3d13001c1024140d09034402d441c16200d9409204c1001101c42e051940c00722210014820f86880c6d0300c809490b4848004280e0500000c0340da80001c000038031822400440c3c0003012800c2c1a07a41e0600d803503c0360860340c20b88000540750b0000f40c0e8110b00a001a02c10301d2006441800c403a55010041c1442c0d0340598a0320307600655102c2d0f825800b4900031045986035105107401e100c0c0c00e103403c0c3c6441c5002807a4201c6101c0ca04c0758000c021608051001c450b920502030408494446480004030b41002c002122565150000143c004022038050b0001c00710481d5284541d51015a28061803101c2010b00d00c00a100d81c110011290100b4400d42140007100100e45e1a14500701c010380c00a012228002c0203080003602c08000c00800c1d4001c5400d10602e81d10a00b4010003500d40410020746400359070100419000e202491b1a040c00220094031011704100000c5580 = true := by decide +kernel

theorem cover : BRFrame.Cov 941187050 941366906 := by
  have h0 := BRFrame.cov_init 941187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 941187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 941187050 ≤ n) (h2 : n < 941366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
