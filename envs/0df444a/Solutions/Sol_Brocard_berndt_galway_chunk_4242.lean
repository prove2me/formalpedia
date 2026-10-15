-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4242
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:59:02.423781+00:00
-- url     : https://prove2.me/submissions/3de6f979-ac59-475d-9752-0dd606b3abd0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 762769784 ≤ n < 762949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 762771034 1250 762769784 762769793
    0xf0d0c0207050f190512030c06070c030905090f0a020904020424021207111509041a010f090305031b03090d030216050d02090f070908071707060801080604080d0f06060309 75
    0x410f00c4407141103a0200d0340c01e908601140400b0110301445024551046100d20141c10070415154125500c2d000d55040d403818000040100714480b000381d000501c007210004041c00c045513010300bd01b4038100003542d180c2e1400f80c0000a5030100100980080d82040005400c020759075140d00701c103104024011039280d20502c001e01d80781c200c0f078009541403010401d03600001c146007001c3c44a15010340c0d12016017210050041c48034004c04005682003800c00000401041c1000c04401c0c800ea000d8840c1c9940a00d10710b01190440c646002c020840d40c4200040c00352101004200c228420390f440450b0b16115124020843c5960a03410840269000141443ca551900325138040078160030380c1d81d90b070f001e0201e800251804e0030151000f00080d8000c0e01242c1c18074807409015002d80300503070480b400b059403010300c169000620301c400090342c003e0203004101c252003254000c0c12642080c1c006d04054480d51138207070403988124034520140e9070f1581d02e103038100220700496000301500d803030004125200b07040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 762772284 1250 762771034 762771049
    0x18070803040902280c060902060d02120405070614090f1201141501031e0207021810030b1f170109150501080c121009050a1e121407080f0d0c020705 65
    0x12404584c10810803131007103145c2c0c060468003400350032640c003040d4644503001041d0035100e4403140c250b0340d50000030b02c00d101d1000c00f940c042c0a940300b141243c1d03034540c1d104c1c000c4501641d000c1124041440802c040f2500d81360841048480303100007082d8100c0d0101101016084542c01001ca12102030310390100102c0d480282c501c0044010300703003424803410705180c001d0844031074903808000120354041064001d5446a15482c7e140301c4d01c000c01c061740381c209031400400f1460548001c80e03019006800181e0702d0002c1c8540207018000c40303507821940034100101d040c21481c40074112101c3e03643c1e40f510036001c5250083c0030780c201200b04400041070350600c103255050400c02c07512140030301d80c801403160080d000080d100c0581c13824454009103000322480e0090914079078120280111110305021103c4840162070b078541c0382d200e9a421510001d4081080d075401100c110003441204092200b00041062000141a00210011410724007002000050b044811900b4100d005911000050100d414402c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 762773534 1250 762772284 762772327
    0x1e0c0315170307080a020c031f0c05040b09010302090607062a02010e0d0509030c09090d180b030105090703091406160e0312160206030f04050115060818070803040902 73
    0x200c1d0861900c80042206039a8820004000c20039540043c0201499200f4805035404803402815038140e29140002540c4801000220100d0b80780b030076800c900710500a900319012240140109400e1841942c010742c003c1d003100c2c0c1c14a4100381d00700b11401c0003900f1031141c1c00070325000166040061040c01c00c4000307460b4603424505c055a24000b2180c0b0b114000281464032040d040c54184e5840340000040780c2001402e025141d00005e48000784506680040303443c8111f64915a00c5941001d6404038035913011007107200d08800b0700003c100510190401e1081c481c1c1c0403442c2c1c107020036801015680c2e040b901d00c1919000005410004c2842100315040400e810390300201d24000318082a02d10002c0d454110300101100c0300a030000300e40f60744600894444500d103400070a620b07242c2c0f07444905c5040303800080b03034102e615519202c4a19100c0d0031224054040c0c0d443c65640c50141e40d1142d4401d2007001054250903598030444400043c020301c2040203001600100c00d026072a001240c1c4e4034107a01d0b4118 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 762774784 1250 762773534 762773549
    0x6020309010b06090d0f1704080105090105090a0b04030c0602090603190b190b030406150611120412020103020304020a03211d0906010c0c0e0106050a020c0a030b0a1e0c0315 76
    0x200a04c0021750f8524010f10700300c1b604400c0c008503140c5c0f0b518140d000501c01c542483c1b0070300307004140010750b0141940014030940d5004024010b541d600c044d40c644444021000520f01d80110f070108000c00d1080041c8180b841c8101401441c0804540016150b0f42084440030030b01d600c2003d110000d840705001d2070200b0101550341404100c0102d8445061111500941940c2c0342c000c400101400510b8001c1c41c3ca2a902e490040803049c0c0302c4400400d801c0792014190920b10544100c0b01405034030104980403107030464032240c243c104070741c0118013a40c4007401c266400074841d140400440c2140051003c00d40340400e0301c40030000403500c00b618070f03251b207202c460300d61543c805071b50120b40b910a80283d001c0d509292000f511111450003070b03084030711034000c0f41041d0b01d40c400200d607058010005100c0c80d0861b130200c4211134402c00405c40480e40c03a010040036806058041465141540c00c54200010382e0491080345020303603445142280c070344c8000500003a891341c40403240341d00b03010034207000381115 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 762776034 1250 762774784 762774787
    0x903010c0e100e030a021c021504030503090d06090506010b03151806040c110a08040603050f060a031205040b0d0b0f01020609251805090c03030a0e06180d06020309010b06 75
    0x7400103452500038150410500a002d4058561554284060982c1d41d40c01001900301c9401741c154840300064000d0224000e8070b0800c00d42000381850406d8038200c07030384440210f11b89a114402d02400c014412001c6031140e48500148000030801c0c050345004c0c0c624900504d03140c0c070705078076502034110500300b080e4059400c4400a20460740741603441c41e40706000b45c030046000303591008101c0b424942942d0034269400380c41003440c10070940c14000c2040790150380e02485242c495049201107900142e4507184d00601d508002c20004104200c212660744550500905050390b81c0350410040d809200d8004000e0f940d42c040044e01e15150000c1030a001c0288010502d0345890286151344490181c002c6410510911409001000584980025100c054100c000d060300449507140500800c2e01c901c01c0d40e000751071402e00542000800e490011001d9600c20110105102c103204003940541001c107200f07100c0d4020580a42c5880401e08425481840c0060f40c034a010860346013100c1c0d1100115115400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 762777284 1250 762776034 762776057
    0xf0506060408060c130b03010e06030d030c0f0e011206090b0a0e0c040b0706020405100302310303210516020c04050705093f07140102030301290f0903010c 68
    0x400a81180d1040181c00c06a54410802804030301500550b4403042c4070140000009c100390300074a0400c0d004010940440d00c4040d080322054003900c1d10307000c00c440082c1c40c03c64007900070382c0700c0d00003007001c2c4074181050240c0c2c800c03070080d04041d80d1080d0085036207144c80d60021680e030304043c0080c0c0010050f03c101d04030603050424103041603110300d100344955180040351b10001d0000d40c1c0d0440780208402003c03100c0450403900c0140c040d4000c84031381600d40100e000c003030f1511070040075a40c942c0380c09114440da0311404c50b503040c0d825402c0c24100c0c03002420007005114211440d4801da500484901c0003501c2e40d802d0b030300002840c15a070341300c085000c3d900b0082070017043ca400000b030706e41d8900200ca40340c14046075840e0800070580f808044030903e142c90250342190511100040310002014420b8400060300d07103010050700b41001202500683c0100f00402c12450006280d81180144841d0003d084c10400c10142094004d03d00b1101c0d0007000041041c1503103000d10980d40b002c3d025080142e685003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 762778534 1250 762777284 762777299
    0x905030a05070503040503030301030b060910060909020a170133091206090609031809020f09060c0708070b18091918020d0501020d1d03030109091e060f05060604 71
    0x340d10401060100c00324110040010500585011b0100542226205c0d0b9407824040240082990418001d1840320081040d1900c03d03800c54040d5041925090215072402c0400e03c020351211a000c41003012059620703072102d28000009008040760403c00503240708824020130300208081c05055015852140c1610f01604149402c088030300d034513071681c490b400c1070415402400d2202da0040c4894607080403001015006660103c5e142c1ca522100304886484807000300407486415155624800706004498652410900400c658031a03101501c06560f40e8000e064540341c11604442141d900106a042d02c2c44203607000400c0c5804100e9248199040030180c0440c4205200040d9644a4464002580c000d0803811900155036014200c00d0483e1000e0074254000c1d00488050862907040001c80c802150190104500340403920000e90b256901c0d040450006188002c0c0417100c11080c110502201c01420320741040c1079005603408030b90a0b0f0b6541300300088070030007400140705daa802e00c802d10840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 762779784 1250 762778534 762778537
    0x80a08044203020415090906060c0519050a050f01020306010f08070c03030c0e194b05130902090108060c0d0e100216030905040506130c18080f0f01090503 68
    0x1d94607058410480040540880291003142c00401100c440000c51010300c1d5071000c5004100c4416080070428070303440350821100d940003001c0c0541280d1000341001303484200400c480800910503001c5403558901c903568181403509281d200e0125942c08020415296007084100c1558091172414110900e03003031101500401042001404050b503d81d516a0030600800c001c25101d00010440c5072164004c0b00400c604111034050424081070341002070030030251082144030780c0418a080f19000020503a03041501d034282d160400500344100c440000d40d500e031640c500c21080f0055102182031a1280180800300c50b0681c008000c60b80843e04000c00280760400b9074070a04080800407070822112014149042140441c1e40c84032440010340a070b0026020380c100c0740442c8a0345481407266540c0c1e04208c02c03900220380ba1904060003070241d001b442c0786540700185d034488500304181080e982400b407551010984e003140b203c0798403154118080041c200111292800b507207000784601021591010303120b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 762781034 1250 762779784 762779879
    0x5040209040f05070509011401030615020601150c080f07050d090303140901030b1801030b13020d0201080c0706060314070e0402031b1201050a051603290a080a0804 72
    0x381824000107500b0040305204240052034000c25150195846e030000a401092300901907010a19292000a0306990146094110101d94024050f2070386010414031150403001550340801104c0f0b02c0030800180c414002e00b0b981c001a2404c076890710802d10300b85140c800400158030a000e801e00080000039840751500554100c0d9003e03460300c1e111a01e0050700134091602038145d100c81c601c43c0d021a51198083c0e44c070b040b240114503112064071245a0384010515200c006500911450807410240d4001e10320a5001080e003040c0724a440b01a44520048500980003180d5110400c00e503011100010031109028201c0780e0020541400d00ba400282e03205031a010b101020382c11608051015940d10010034040301070300c0c00a10a07454410890001070000301c8601d10310140e01e44481ca140e41c0b29200310590a407030044080d4540c0c402c10700d64800b65042e844000e81c0140c80d079402091b2010180300c003040c1e141c426a10f045e00e035800d040541202031081e0009010422080c03580e03444400181c04c48070036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 762782284 1250 762781034 762781043
    0x190f1806120e07150f08130209070e0303030a140108030421020f10031b0e012316050606041a060a050703020316140c0a1d0c0c16090b03010504020904 66
    0x64031500120700d00900921400300340d042c0100c50001405040046010380004038555442c040700604880541e0460426240c3c0864803002880443c014200101101e40001d02824145007440800c00040c0c55948120f807440c3c10130344c0328984540b02a00c0c0c502e405000d00400030145040a040c00c9500c0c0011204410305800c3d4030100c8461401d42d20f81c2989000012006421041c030030840e4000a0003500d030100000403500b4025014040d030601c98100042055016580c0460041c880c400312083c001081904600c0030340108841c0c0c7ca40b09044020740b00152003000500144e2801000300802c40f50b01c51110300f1302c41c0e510302420380c0300d070345840441c1d44e041d104e424407a44682031420700f249540910b11042c800095200240030a000404511503d10051a022601074007992400c1c0601040c507482117003216100c0d6000720304040c1c4a18000340c2e101c0c0711302d0020b03400e0500c0007103050b150110502041c404143c034004188140c0e401401489006a8154000d2100b0705042d8041443d10b88010030280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 762783534 1250 762782284 762782297
    0x90c01090f0614301b03010e0606030915010f091107030f0f02070b03100504180302030a11150a0203090712120311091503070f2a02060d02190f1806 65
    0x740550140c0001d8000440d0140c1542101a504035044c03e601c0c010f5808083c80c0904081010710090110120707416112540071010003074890030240103071030708007038841e0f0424003440744400c8041500e450460b00822042c21505174051402c0d00e02411511001051221078004100a201182e00480100e00d8800e0f9890010110701100300f00b2803d0519640040c020200000b0900003803600b0804280181e0346c040780c04010146c4800041e10600003045001400b6800a0158100107130051280141f0801004151881420180280c0d0108401112980307025603010061200009003002250058503a50b030740608001c2c00307078451405010200d80742808054648410a4401c68034405440e40c03244082c014602154142d0389148a54100f00d8080300050144404003403014881d0011a411070706c040c0c6030b80c606003e4000000750300042580d060703070000002c10010340380c040e952008090700841000304501c80c041d06034005241140c4401c030b1004001e8000030044030703802c840010200710740443c01d00c4c0c0e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 762784784 1250 762783534 762783547
    0x6091c0611030610110a0b1e0a021803160b0f07020d0605070206070c0c030803100902160b0709140d02060c06070e190605090d0507080109030207090510081f090b090c01090f0614 78
    0x141458000c2509141c410042c0203100409e14550090714420950031403900400c1130110078199103600e5030101442414462030100320b4009594020024003080702d403140e00d451450340103d4600c180650040719990395550401c900c6580c1840103039045a600c0c64001d503681c20a880f6048901103030f000c003410b040400030208410444580021700240091a000d5403501103001c26030300c80c503982440503038403852007030005002c240c4140c6000040d6a400f105000c829060340090121031000c140c01260800c03400c100e00050fa040c200301061282c8455030300c001020a1000c18045030442c94500444158a45802030108680280540e80514025510f4a00702e440c541015881c01100340c2c00030340994a0000d01d0010301d68003185c144140d5035880c0080c400c5440e2908244100a014825001540c002c400c0d000050b0340000a2a09001a82000400e41e058261190680311b0070980351324007140c0c00208040c006580120104006048141c40000154a82070000e00400504401c0c03242000001610 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 762786034 1250 762784784 762784801
    0x5070206070b0a15150905030705030709021e04170c060f030114130515041109011407030e031005040302060906040512090d06020a0c02120c06091c0611030610110a0b 73
    0x2105905442083d043d00d55a001c24000d000f0310043e0040c0002da10040205103408c001400c01d08491025006120041c0f8000078500250048001050100900d140a42c1805c1c007050203000900300d102480c0c13040c00240c03e0042c2c0b601c1e86c00f4950b14062078091020400f03088405040e2811a1b12000c0c0c0c0300300e0300c0616130000c2c810384401c0540c00041780c90801400170480200c0b40d020100d000549040081c200e0141440300103009141200d4000b0f21060800c0310500b1300c1c4809407002ea80b107828405411904000024201285041702444465a810400003410741c1006403030742210f00030000e04040d05240d00d5003615880342c07a540c502d620740300003601d210648600c4102028075404c00e404641ba107100410040022000e03e00070b83c480c0c03813140300c0312148040102c1c1c4100f02c0c03d801040c0501c3d14849005004507106220008012500b0784000113002c00d5150250014075a18484045d41d240307441420800100200d90080c0b08001c400f0b13280010741c03200000d40e001907580040c3c0750f002e40da41d00c1d1003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 762787284 1250 762786034 762786041
    0x3170a0c020d060203060102010b0906090103120c05151b0705210c07080a020907140a180e09060403120b031e0102070203070f0320060a0327030509030d05070206070b0a 74
    0x5000b03411003806050b00d0300303200b810f40c051405803009070700034001c1145030720400544410a0307601590002004004000140031031840c000c02e441581031000110210b51500c03800c2a5a107101c2c030914898900c20844060303e480524a4480b030800c0c000e600346000394070303072680d80e0301d9a00706406044440701c17640c400280464203403568209405c040b100f01c542c5810a0326110400c400080707005100036030100d40c030395005201d8620071811403801582081081c0341d0403a5044841d4201c003556150b2410b021800c15081d0800b80e00c1410030f48001c140f40c1c1014a4010b2001029042001ca01e138035000f00781d850740c1d81c0070500960b41c00340c8031100c100d01d4102c15142402071280d82c400a605108044001a810301c2d005080c904a03409610400c804028508001012000c00344206a01c00010051100d49501076408803800f44102e40c00f68800e440c00300e0306500c0031303540035400768041003001c515404107240c06c1108000341c080c1e916120381403a419902184050040307910007028404814001040403031140c3c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 762788534 1250 762787284 762787307
    0xc0c0b0a051e040f03240207050322090f0c14040501020309090a14070903150c0e12280203161a031b1206030114190c03020d02040b2203170a 62
    0x103d004c01541c0f03143c410b101502004400b800c40c000d0781400800c984c680e00c00d855500d500b00d00554582a120140100b80700c000f2030320200300e80e09400020030030f85550310920002400b100e000046100380800302600d4444203420201d0280010007007800280da012041d140b803518181c6800c2c109888211001000d050100c10070644008080c00300a211540490b0040c02c030390141c204108603501d070f90784d000262101000110049080c00080d0485420b0410119000395249030a81d0f1a5040c902904600c1d0b55071607009011406007004480e040d0316081c86605d003228a07403101103e5051600e0300d0941e11000018941050010200000711203607098219510a00c4032180440e940d0700041c00c682d4041c0c41e0588d000b40c040d41ca0110070aa183c40030b04060f0f40114610b01210148040d4001200003a12800d580d0f10100740d000d018264150450b40040c202409003144116221805d14200080c0c0e000b90040304242514540320400200b41503084c1e030180311000729a9940e03908002802038804d82d42c2d01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 762789784 1250 762788534 762788549
    0x121802060a0203040617060d030804020607021f0906020105011d130f0506011a120a112101091b0c12050f03100e09030a021c1e0c0c0b0a051e04 63
    0x141d80121070350210080080d101310b52206510415001c4d80c004240000b124115001f030316400010011901660307001da4000d100401c0c0c94585022076012496101c10140700c8009424034801c080b12180d041500000507016520003000f5a624040e000071001c1928018185000303040c1020075141108500703244955070304525a44040020307460842c0e6104002d118440d82c58080c514844424031022007210180800303000c80b0406511000c51540c000c1085086600580c4400c000304910030380c0d4100c0c40c07564101030860030701c0301e580340541c0380c401c0d18071011794600c0c5401410a105c1d10150000d50b10f40c5219000000b0014060398260191003a202d0681c1c008141c580100411140001610503041a03d040700045e0040d5192500050b42e41e019680710380d030241e004803861180101104060012000c1945400280d09916403401403002801039800400980342c018100e0602228640207002001c0c8007508a14112404e44001c20300d000c0d50f614000c291801c1420720000f07103483c0e03050385c5c00741100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 762791034 1250 762789784 762789787
    0x1e0e040506010614190e010915020102030f060301090b010b07020d1406070210020c0d080408090904080a0305010f0b0d1e0e0a0b06090f01031203020d020a0f170712180206 75
    0x90030519601c0c00c00740704107000128007014100d0407004001c20340d188180d0146104c0b00780c48070100c081d258100c4038500241000700d0443e0005e001d5480d10517008582d5013036000140d43c0d04015844076400341006115a000f68100011900098295403006045031207c00b2001d072180c40510004203a240320000c00741551500460342504400b000c07030740c5030141b1116000c0b900d828085a159809030f000318080450650401c081510549008a1215601c02c0c4150841c618004c0c4000029071500400d0710309640f464004a150804503405d8400c490140c031043e04140305140c90401d402c4200e1062400c0301c07070b0b491344404040c0c0c0c00c0700d209060789103e503880c0e00061004600c210312095440c0820340007540d4540c0c030740e40030138841d00300a070030113009408695582c02e11360300b15154440c200c3e0781c9a011508040c0c2c03c02000076210200d00c0500b80820407030341c455000c8055084001c0414806641313080030541c0c810280003100d504101c500b07086000e2000045403c2c401ca16082003c0708410a004c0c0d04080e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 762792284 1250 762791034 762791041
    0x6041415090907202a06070507080c0a09050c04060507030c0b0403050c012004060c02031c120b06091f0207080a061407090609030b040206040b0d14010902131e0e 71
    0x4000800348801120761a01c0a003c0b0f6844010540e074061700d880038040a03a100307400b000700708540d84440340f81503005055a17180120703590742d59240807402d6102e822950403101c1d02e1816860031080c0c040080159000c10301c424144182d103110248564032070b000038004001500707400c140c000c03412824030303a410810010140c50941405800ba03401031102ea8481e501e80480d201da41c2004402e0001d000190100e001d04290034042c0c03d03a100e000404060b80c0c18841d076102200000484210f8182c21646580c0715824519900517400944034000c420728070a803000e0100310555264607809400946520300818222403004400341e080007034a4206050710b0080b040002d050100039042440840030b00d00e1415103d075212042100d4884042c022100010740d162800c1001c40c0070030300580e0304640010459440c5c10380c3e500d40525944e000700952a80a038035020800741003075042500714010a0860001e61a1004c429500e17501400c0501130208520381d072002c8041c07650030b10304108010b400202216004c2c0d04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 762793534 1250 762792284 762792287
    0x7032012041202150105090406090813030303061409070804060e19050d082a090907030b030105010819020607060204030512070506130c030b07030b0a09090b0606041415090907 77
    0x810895090302d19160072019011218400a8414480044180e020310300740d00b0101040180c03840548146c800585400c00031000c00c040d04014622800101c01e0254043c0c55071801500384c82480c0d2004d107450350310490f248400d850701b4458070390002d401d140c80c8440c0d0b600c61620900424008045181c14890242c0d14000b0740c0c0340302c0d030b5400d04c1d40c01941121040031072401c0445207090100d440302c0d1102c19509580d001501486901c40d03407410b040e0101ea08000a6502041c9051400c40d9280002074451105c160142400c1c031036075001d0508080500580d03c441c6a80000c06010184000d008020004040040c00f2040e0f06440c0078581c030109071625860f1002040072150402c034810b456600985000c192032800e4175414000581e40b00038807403c10380c599180d202002da00203244000345078495004c240303140d48018982e400b03000036090001d002d40c3c690034500400c10005003090b0260700100700500c02d00115401d102d81c000400c540300d62800040540c078010501a00825540040d81d481c10320906d01d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 762794784 1250 762793534 762793567
    0x37081b040b12010e031c0b030304030308040807060c0801240207231c05240a0b04090c06030f0e1609091a0906060108091903030b0a0302030f01020d05070203070b070320 74
    0x1024001c60a142415100b482e0003241d903140521f907407540c400c01042000901910381036600c1405114a581004a40d440ba601a941d043c09240000b912503c0140400e10074200d035002c960b007009a20390303150900d413000a03589507068000c0311441c4c03c0e00c89900c5d188068004139115545030290626081c642001500302c95050081c0e0100c595008110400b54040c01c0089640c01001c400302d180c03141512400b100300c00030016520000d40050b150003039540418a54070681d0001d01140d80e0000759060907020380c404441041e01641ca040e08040101121881c058910ba000d43c0c012640c00120f0b06c4103848c0c07814017130040c0e61010132618a0141005080302d800702e04a889031030282c0f2480c00b42c1d655006c0c0c3d070703807034002546d2401c481c0c80d8180c0010012074401e40c0301050b00c181c00b4241c003401c40e03203a400084c60140d034203002e0843e507900020240102c14007405007a030000c00c1400114184840b03559600b0303001000405a508240d501c144024402c042070840c520500400c90030b003646c800722200c911301ca0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 762796034 1250 762794784 762794797
    0x714040b060a020a0f020d05011404050106050a06050715020c0f070f121505040c1802031837021005030403030515150937081b040b12010e03 62
    0x840c40e160205030141440c400316100d0020395405090821a15a00c0303001801516101380c0e004028902c904c00050b009200b0300721403620859a40f4128070745480c0450035544035030402d5000c1d08490f2030402c03485030454103403035035242e1101000c1e6030307054100780c0300009000d0301c01d1070a503c0c0300b5241d145506510100d54a0241e80c1c410604404558440f42c1c400a598a27042005001340000c04010550588542c825a08644144101001e0fa582c4d0f1480007d0384001076801141c41e0340c00070520480c8503454568458441039500038007064600d0400c0c1d00d82112a0ba0750900c2c4200391701030b4500b425000c400c001c242c2c1d140c0c010103559540d48681c00003041c68000b241c0c110003107441c06c808205101c01d145502d100c1400010020302d40c4410507010031480703802c07615059070005440c031070040301d00400c9550b454040c8900584822041e184800e00c24002900354045099900304071000010300c2410030152401140a80303001c601c00d40005e02081ca0004400c0100d41d00f0751829000d03030320511020008185 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 762797284 1250 762796034 762796039
    0x8210c0a15201909050607030f0c1209080c10020c101b03050d2901050706020403020d050a150b01050a080601020309090f010513180204050415050103150e06070906080a020c0714 78
    0x10f0003542c18010f4482c08214040d203607104405201700d400103071080311030060400d600d01d401300000c003507aaa1003a141c40940c480394086440b00c80c06000204040000717043c0d0440c1250a140072400c401c06c069156201d150040d40501450081d20001e940520a8060744000d40501c07420860880d05000301550003a0008076525414094000034005411010303804c3c4070100100741525034010001502c481e40f0220040701d1140d0280300002c05030b0f403a03800d0051518040c0001d80b10007082440c003050780c010000e010b260000d241c940000c24590313203c0251624260542007070003880c3c4520b00140c1c50b50081d8165540d010f0381c628104405c21001c81d980c1412240107440c0700541041184400040e102481031078910210110911001b40c50907400c00c1c2c0c0c1080c019042d90304401c95100308030040e07038000d0308107075403281c2281002c4510a02d14400c1e0b990000180000d0701c024149581c0081141d00180320360030801c041000803810742e54980e4111012440e1800442c0e1905580303403021036081003540b00d440e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 762798534 1250 762797284 762797317
    0x3020309010801271a030a0f11180c070804090509010e010e120319060803040b09010905060405060d0504080c19020a0510050307081f08210c0a1520 65
    0x5001c2104c440700002150701845041107a01c502c441580050102d0a024100c1082c00720078007171217403014840740c0d03045406150090314001e814200300b01d411110760007480c0141008490030b0345810340030b81a19003094400401d1380e5030704824102414140100e812002c00700d882c0c441482070204055002603020f0070880001d1120005203200107031284a01c0042401d00e400800c0010078543c14010340b043c0569500d02d0004400340c0342d0b8041031660708583c1100b000d1040001d1250031a68100c008031000b0301e8101c5080e0b141c0303401c0c040070842c6070142c0f5850410a58036200400e0070803000300180c8000d038682d102192102d142c0c81a0112210843c084141d01400040b44040360300c1c2001e80c54642d1031206502c44615581b100c00c0c1c00c5426043c01400b03036004015100c258030611144076103400003001c0300c4004088020742034401100d03031007640d8a07861019000b00041400c0c200d0101d24a0810344d0070500b0368461034412110030000c0c10320722803400d495600c89001c40c01d040c00c88801400108102c0350700c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 762799784 1250 762798534 762798539
    0x40203010c030209030d05130b0a0801140303040f15030f020d0b0109150c0f14120405040b010f020d030b180106021f090302070b091305091e010902090406110f0703020309010801 78
    0x2d07402c03481820145500b541046941039001e83c000c1c0020300a841c0142c0788100c1150b5600d01d0a80a90010482c8100142c0c48500400189401400c00003c40c80f04401440c0703840d14100d800e00740d2000c00e100d04044a52201c0c1e0103802c40d4000ea00242c00301c40c07404415556002d00250120040c624840c025020030f40a100c0400c010304403000356840704442c0c1c0c803541a00101380e2654503840749e07080f030122502c0c001e00c2d00360800c42d10240501300b5010300b0141c00a4445003804100b20a80c1c5444032803078100716140284101107980000c0d0002c910207581070001e19003411a0101d0100003c1c1e0070808260b80700380000040482d80002c448990389483c80320388041b030a002040c0e40a03219031082c043c0042c0d0001c0001c0c0046903642c2c0081081c060002d008619120021200c4400d5070b0080380e001c111500105201040c40110b00c4094004d06e488000030403845610364000f43c101200508003802490780d50740010019500d40c000c50390f81d4104a5030003a160070725450005c2d500c1c3d01c0306c00040d00046500c2c000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 762801034 1250 762799784 762799787
    0x30c0d140d0906022404080c10090503090108070503073617010b06031614070524090a0503160503041206020414060301230f120a050d17040807020f090a05040203010c 73
    0x2007040920985901780581c0c5503902c40c12401c0e00403020795503140c0213615401c000841a48554032940c0e20900c003940c0c6502000d0009010140003c080e003040c40410001c200c4a540c0c090300700c600d400c0c54000b90b04124111400d60085203280e5074503030524045514004509084010000c4d00421042c00003030101464000c203201143c0825030719803546511013550246854060520400c01800d25004541000d40e5500d40f5840d2450b810584035076030f1007450400380c02203ca14000c0c5d50201214000340400092540c03000d40d04e11031060f00d4a401d9030b1407512072042001c180308039001007061458a0704409100c1c18040002d521602c2110640281c44941e00e0079410300e00107890480d02903a5140d900c6010000e00c0486503007286201551210b07140408000e04c2d82c4800e40705015200180060030221910715044d4580101c1c07400d08030030f2194a02c40f041c4840401c4070480d52150388060f1298030717a480c610200c3c00040100001a81c03244428040100000007030b4440c9103e540220024090356158030340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 762802284 1250 762801034 762801073
    0x1802090901240323030a12091a161b1106040e090f070918030c0204150f06030f090b071b08030a020d14072a050304030303051e06030c0d140d090602 65
    0x4544e42d543c0c000f404421417040c081d640c0000361008404000c242c0054070742d0f503610480010309031101d5190301c1a040c01810000c6044041421a2608041c0144003c100114118481c5150010402070703042150701c58075283c01c13040e107004280c41001040e41d41480400c1c5030700c0ba0364504500b9003c0c402d0042c00500c2c00300034081c2c5000141504240c0e644e074440f940303084481c80b0b180201a0b03042500c4460141191a208a42c90000c01104100400320343c00e012000703003030710f40050291010310300302100c180c040b4001000c51500274150381040d0700680b0b04500c003c00e440c070b2958000380c030601000c0204141e81541303400419240b092441c041040101c0052001d084070b0055441100041030002140164035045440340c559002031800d0015204a6580740303880c5a000b6002240060385800500c2112141030040788080900752040d081285880c1b00440d83d2024003200440c443c4612103500402d0003415000c1c1450358032038071f0a890401c5540e810142150300e40384240f10040c81031802c013503180e0300c0088 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 762803534 1250 762802284 762802343
    0x61812030c04030b220c06021515010302031e01090c08250e010c0804141912020607021c03180801020a050d090219030309150318020909012403 63
    0x200e00506250a546903444110002084031100324034110344d40602030f44904802c0e822506c00d0b82400142820000b0090500c05050244551120b001050040c1c1480d2030b99101c2e80e0000a04e0016100c0d940d0092907560408900e0840d5001c0914000100d00e143c2c084e04040e070040241d80320201c1645608000c4101c400c9001940449101c00e005a80e468601c03aa5800080050525060040e0386180d2a8078805920a43c84400b129408004075215410805807201c0200200320743c6000852404110410318001c0709002449031200140600441d0f07644014030a03050001100484685c50381e1034054807489191031b40c0e00220008a10000358800305000721090040c481e514503042c00e4101011102810174894200c3e84100c08515105609041300002001507010b035803280d4545107000c004080301112015a0b0b0105810600c2d800c1d441200e810746020401e0303040e11319810940d600d0451074010310404002040a080c4910f00d0400e0031a59902c8105a901035040047c810b007181c13000107880cac06440c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 762804784 1250 762803534 762803551
    0x201020d080702032b1d010e071a030c0d06080a0303050a06050307060c0c03120f0905030309090f06030106051f09050306090601030305070606050613290d020a03020c06181203 77
    0x1008612400091004840460005c05040070b021241c1e0b445410241c0b82c03588440c0c80e0b02410b56140b100c0e03000090051001c000d440300090940c0a04001c401e010003030f1100d6111600e8880040480c40c05070706841140d0380548515410044945c40e040240e481c2d140e0303140140d0009080030080b41004006128010845000500600c07a0a1401c142601c148114810607a050303080d40000001103441300741d00180e00b880ea5a1454501d040104c3d02504403140341d00405d00a603c180076603c6c680e2102d407402a0000e80702000061142e030b40c1c3d00041d0150003241c1204da040054081e040050340c11045100c1003982e00d50300d907800d20644031414103540301011220700b01c0c0759100f0340c01000401e020f0001050118000d00e8003143d000d8844012901d9680716400c21004900c58170002c002d003c0d61220f00054403910b0030445542c20b0340100c0d5180c81d034000d682e45490090384c009400301c41a4047d07411205404000010f441c0c0d03e15107030071261400ca280c100456424002e44100246d025480741c220b92040d0f01c0e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 762806034 1250 762804784 762804787
    0xb04050d03140604090501020702063702030d0209032a1e03060a050702030d060b030402042301090e07050a140315040803040b040606180e0d0c080910090f0807030201020d08070203 79
    0xc683c04c000140c6500841668155820040803026880d52000ac01101950035001d10401e220307004d00320300e41d282000c04940c16900a43e43c411100c4e90201c12655042c1203c180507813503100080000382850b90300da0303080006442c083c4141c201d000d1042c20240a5003822100003210812010440c110900000301e855495000080043c21601669100783c1e041052441202d00b040c40707200724441200c002d07820011802001204000452401d03020b070140c2c5491044280e074600964045101c41c1141c10f01403103002075242c10741e10070304200800c4068014035005162a0a196441500c51140030464880601038050f200c00309003c0c1c0107200105004680c400d10140c51643e507a1250802040f00ad00111a920b407903c2000a05840212180d0028910f098000801003120a104d620300a05140300d882408840d26521001c47d6070402a5001d41c070b001e0b582d41d469004000022222071025403c8420303401d08400d030205240c1000207412007038a200703800b282c68a08000f20300307441c0c19200702c6100005a00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 762807284 1250 762806034 762806041
    0x606010e01081f0806010306050a0c0c020d03082e18020705070306270305030a0606110c01120213261519060b0f07020f0a06050301151b0b04050d0314 66
    0x1a228120f0305070701a0040d81d090030300e13100c590242c2014004c0e03206441aa03101e27420311401d0074051144c0d86401d001401c0024500d001b66012a5451a44003809024800540000740c4040c600042c03003e000c2030b074400c1c0486c01202e0012905507a805074000e400ba6880d0003051200340803518400ca98103182c01c50002d103900c0e0714550b02c01c0b0140c00040201c1c0d280c0c002d90040608a0a0b241b0155a40203119442d425102e00c1d04488400c100c86842d40301804200300d240d564003003280042514050b000c000e28046100004011012005c2e105091800c114501041d40001d20003003141164a00051100280404c01c014001680e648240ea00c40c000c21840000001c1248010000d11416034005070450209285948942041d8150004c19a4002910300005c01500b10710f031a904080c02c000d01240d00300d08243c01e1100c018502d01050280300700c9800940c00c40ca101034091422780c28126242070040c0d4244980f0302d0f054414000c155411141ca2160741c0510304601d003c2d00880100c1c0480c2c400382519541c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 762808534 1250 762807284 762807301
    0xd20030c0c09070c0516230a0513020c0712030f05090f0105091c060204090f05090a0210091802120a05130303181415010b0304050c0f010e040903110606010e0108 71
    0xb0700181240003400000d441100000d641800101320204100034082030301450003043c0030182d08251851000030203007080040340341e5907240410054400c141c0d10a0520180c0e440448002e2240030511001485807590000c2c00d055641000826148290764080075440281000e561074026840c0070755000c284101055404e5109101407c0c0310310004101c0070a0845901100c2440b9046044c01d480b2103800081c02d200340007090280500c9072624540030041032600f07400711030b2115230a0300c00901c03400f0480319090034a4400c0107c107010303050036500c40d0102e48120901100075030000342840100315460001542c08451480703032911400140c800c090201c10b82c0c2d50110020038002c49100200c540b141600c0d00481c0c5024510101c0d0a80140241460400e00c040d607100400141d001e02c0400000304108030002d030340802c40c10341c0c4801c01d503840c100314503c03080161440d4580000b40e03a04030349400c0510007070681c804034260f0280d01c0320003941c00c140c44410044508103032a0412501280501002c1108071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 762809784 1250 762808534 762808549
    0x1061704020604170a02031204050102030301030209250210050a06030b04060c110304090b0901120f140c090f160f0c03123c0510030809120d20030c0c 66
    0x40d1004002c6454182c440c9210314000c08000c0c070360f2031300b940000036200031070a003081180c0540309a07645940c200b6281200003543d9110500000f03004410f5207000c50740d21040c840e022050500e603860400c02c102c02b100710080d80c031280400c0903500a41810302249095200d4880c41b8240d9400010f200d10300ea6540d22242d002d04a10006081044200c10501d40a21428400750028000514000c641500b0042c2001500f01041e0002050703c8a4081d00e000001c942e010204411540188104101d90b58464002d003403440d210380e00358100400408000b8500c0a00380c0861044102244585407019075903811190002d6400412000c9082f01e4900c00c00320f4010980705000c88003580c004101d0080328030410b1181c4403446100007040050280f011039081c6080b61241051080f000104481d1400070f01404c00c184041c40094048400019550404e8a40240040e400681c3c0d00403520700c0290014010561102c800101003200d0294407200c0503242c000c030840305c81c505400700030450107642a0402984 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 762811034 1250 762809784 762809791
    0x11e0f05160305040c05090c0a09080c0907143009010c080c070f020a0b040303020f03070f03030f0b0a0b0307030e0a02030d0e031005040303020a12180b060a050d0b01081203010617 79
    0x6500c1c8010000466555591f07003244924400d000729900d40c0880c690240c001e00c0030360000c079090b4101d0031004443d501d40026147e8828007510b061075210180c8001c10031584a410b000540c00041c200c003561000742e400c1c1d441081641d9100501007144c1e40e12003070501b211122080400042d414501007499a011000601481c0340905410f07000c92079583e001914880d001da01c8910080f001050400c1496018030582c801c0ba4002030255182ca8210b543e004080c0ca4001c200400f071503910302680c01c0010159200c020b00d4040580b01d00c15090701d03103840d0360044d041142c0c0000000d0410340c0c0003201c41008070319100110780c043c004060000303148600340c440c0c80601c14044d405100c0c01c40718035903603130300e900545020741c2c042c0d00c0061f0b895907890802060400d0528184c084a410718503101030740007107030740c0910b460382e040a40704c0c01d1901c441c400607000d15096885594410000d10040c424880841515030480d04403404803030f1041e0440d42c51b4a1039000901c10000402e482c1c50304001100d00740d480182c0e2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 762812284 1250 762811034 762811043
    0x610080907050a030609030e0a031505070e041e06140f06030a140c0403170a0c03110f150a051b07110f1201380d05010b03011e0f0516030504 62
    0x114035120400300e48043d2070303039001740c0d1819100c5a00c41c3c145074001c01480c540007410740300b0510084c1141c546150040c0201c0780d02019603900c00000e00c405218102c1c80c15030032030082c03040c4441c031204035100421924412840840d0b40c03034590001901040c1c8a20701c0382005c0e02034503403030071a41300e801042a540c0001340000e00c500d8881d062383d00440400441c50303103d02c7c0e946024640f510304509281400b40c0c080e441020b0461800c0141744112070304008081c44055040c030301403034010109107689060402d0940a800c541c414a9080d00b42204006001441003410400402141c3e41d44c2d403401d0000c1401c0000080901e004011580200314895041c0003821000390070502c0050105010940100700021032040e81d035540c00381d900094611a44075200358500d48200380c0240145082a80c1c074a454113000c038401d500390309544082080039000001d12540c020000c0140c0399195040075110800551562411450101c403804079000921030180594540c01a40205601c640c00030fa0081c000600141da = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 762813534 1250 762812284 762812293
    0xf17030706021c06050102150a150f0609060315031e0515010b091f08181203040b070810030308160507020d200103020304050d080705070501060e18030306100809 71
    0x2808107080d0300003403514590541040154105030b50000040f241181c205d18115041202c400346c40c04800110241c104c2c2030183e00250071900d0800403100814194007004d43d104050000089454014055108032805a201032004510700800882d0401441c04020610b40c100e446510100e0003000b1244541481203044a002900340c003818202440f0903407140e03001c06000503050354103043c0300540c0c8141c00c0524410f41440b10009030b01500c0f00700d000f403c00004007480341c1d00017001d0780100001090b145000c041540e9908003803d0007480b5200488069004c80c081e6008117003039400c1008240212a0940e890034002d486d000d040f0002c280c0901340038010080d041c087d04001d40d49000b09881004e03c10404492014051740ac400076080b12038840e14141803050040001140d400320308584900810b180c0460359940d0800b00707a03110300581c1070103041c643c40c2100c040b6038903104951242c0291440c2403062026440f25200a41e60302c000c9800e0b58101000121200d10103000c2c10410b81c112800c0829103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 762814784 1250 762813534 762813547
    0x319151217180a1409011a07150608060903040b040306050601030204051806150702031903030213030f0c0e04032001061e0e0907030b04110409060c051c0203010f1703 73
    0x924894100b00c0741802c406200c105414901d00d0640c5400f07004220841000b0810303081030340000c114020502c80d600f1803000303024038929964403405c11100c2d070702e60141440c646d1900c000c8441e0010601d501407000c0e10301c204800309854020010640d81100d02d0011640c2c80c1c0b0341940d0f6010b002e0040070f05424140741d000d010206140d41c2e0703040e0340540280c404107410070503d401010000304180c11a200159500c040103e2805a103000c545828218903031420a00c0a41061404500174840c000c514035002100704070110421540402e00395020b806841024185503e0f80d6040c40b52007070603140200800d0500d844070143d000510704804200b40c540b400040d01e1a0303282440380d4006c1412502c01c0c00100310313050500ac4000c0e10200c1d65000441e03200100011410750703447c00c2c10002d01401c060700c81a01c518003102d0030384e1a80c2210b0790f1507502c4403080c0065201c0d50400391890f08401c1d0141401c0507400c40011600010f4401d4904894001e0042d680081c076110304540000c3c0d001e80100b48601040059 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 762816034 1250 762814784 762814823
    0x703020a0807060f1a01020a0803100b031905010501030b0a050f0a03120908070b0c030306130216110306060f010212070201110616120b0102030a110313090203191512 73
    0xd04560703409100c010440b00000312101382259110710085002d81103010701c115250b43d0019901981a5006500c1c643c1d940340d0080b990300c54a80c2e6032120a050000108014200c020301403029883c8402120500140e41c0b210015010743c1c02503215160004403403401008549071400d44021f0f0020007400003d8a1500ca45a015514240d10004408a0020b01d02045100c1d420416800102a211843c0d810112895a100e41780d00c030180080b48206400003850382c081400713034101c500d8250314001d0701c842c0c0c5070f0508c0c0006040490151a5100e07014a0001414070304101807400440c0700c0507806841c0001203e2000b02e80ea40000d0000c0c1d040140e02036241c42825800c2110600a420806824584400e07401009007a64040624230700580e050030301c2607200e641c00005513604050341e41407203445051003068031313403031806110040742c1061501c1200182d19801680210b0080c2030280f5600d207040403400003601521603142d074540150300f80c3c040800104044c408030b00d403814450140c00840d00d948941 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 762817284 1250 762816034 762816037
    0x1312031d0c030708070e01060528081603200a0e1207080d02031305130207060c0c02040f020405063405150f2e08030708030109050609010510050703020a08 68
    0xd6080c0c0d207078403090700c01c8428a0100b00c1c140040c8122001008198101080c101c007410b018403400c000c1c0280810100030074010a01600d9000c40c150103000041c04183c07030018102c5206407602c0600c204030189810f8200c0c442d000d011403071046411107481c85041fa03c1414483d500c02c00c441c204021035030707004074040c0c0da603d060140100702d03113401084601e0400d0100c0341494091100300013598000c201001800140e40c1c0c1110807108200c07040442c02a220a070b500103031040b10300080c48146842c140702065034015021104490094800f0001060b07040000f000301c2c80b490040aa20000134001e03c1d01c540d0b880c0481514684044000301c000409980d90102d1080c1100000ca400f0740007091000d0145800500b0503070300854005100145017072075440a05080ba156084004920917040e041c0c0e4840c249525800080050008503a9110007500701041c01e07070800e0059144540c10030012071300b14546854030724103903100102150000c080340f480a881541c810881201075000d442d4a610201e19140f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 762818534 1250 762817284 762817331
    0xf0504180504060509010c0c0308040f06050f18160e040204020702040e1f0c1e1403151806100503040c0b04060c15060303050a0c0510050903090109060503131203 71
    0x4003040342e060500d04102a030320014000c0340140c0c9098001c0070700030341c0400460030b401d4150402800b2a2901d050990300c0814500b40601141e041500b84900f03900110f86c983d01c115420710455480b651500e944540b10541d051035101d01251740402480345489030038038650040d1008200600d49007007540801d0581d007071802030182e190006941c840f10000c0c80100110010081c440802c45d14548950152401c6844010400c5411b0340800150220b8000c01a984500c10050306c0070342c4914014060800070b5007070001d52401600b03001b03180c149449640b410140a200e00818110701e00001400032603203a04006c00070341c1d201e15081d03c0002c100c290700c002400130340110b07503500ea45420742e400c000000a400c1110080001d04c6c000c0100042a40301d000d83e24100b49900d00b404188905040c134034a4180340c03088000c030441c9030500344901058000b00034140e00d902a00d41e40202507a4010544181c0402c8650fa40003031052516440000d82480e007410390b88a1a040001e40b0649400210340400c070301c0c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 762819784 1250 762818534 762818579
    0x302090d021c17120a020a030f060e0711010207080414130c080a0608030702090c09040e011506091a0d02160b07080a150b0d0b0102010e1203070e010804120f0504 71
    0x2e1060400b031199560300b0b01100c6859045a030301d003040011a414116400400541c200c0d41d0208554400a00ca604410210400500e05000c1c2caa12549921600750050705c980000c9120840103061a01040c002c4d11031007600b10080c241030900d0545504c100d80310007444994482c3c08a410758030903d01e240b00b503040360100796550310900c5c90f0000300d040032a0516000050207134000e025070300040c2d0f1107410095000c03c0c2903920b82d445410b130f0300104024000c9105501c9055003041014044840b500c1e84d40d40841da55540c0b80f801d07644c0e641c145030044512400c0307440e104035401c10070000c4181454005040380c80704a200d100307407480d080c0c4071005004801d685540010303180f41d003405800c64150280300c100000c0032040c1c0c81d000386425424030491043e100b02424071900d80001c0307070182e8000c0d4841c0c0b501080d40300546406110307242580140386e00482d07212010801c0400400b80a52081003514460f96200a0b00c072030324941c01205942041100c142e2904000b07040101003210b02c0640001c4240003a003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 762821034 1250 762819784 762819829
    0x60109270c050415080601021603050c040b0112321e0903070c0602010b0a17030417100c0807030c080105060a080a1508030c06011d01030212010e1c0e120d0302090d02 73
    0x80d0002401e01d803244138500c2741075404201c01c1c40802c0380031802e198440d40813940094000c1d8100c0040e5a44c0055241842ca283e1400003038840c400c2e042c1966a403c54000e10301444151840302101000340d10503940e60310011402e07203031202d0319502e601445c0c0d00701e036030390040742c1c20191156208071900712141c01040042c6d448103405000ca050004450002e44500b8054a8010750b4600c40300d50380b4000d900c202d1050b00008041451464400c0c0303d40d1031040517158060000214006c000707482940d0a541d42000070346061700701c00c0440c2c0306080160581e20300500a074a0084280000c0b140b1f020050940350004d81c0d50724580036a10000300840004111000c0a10344812045c4021410300c078050303004920000c1c0f1100c0907004507204201c0641034a45c115488400e942c2039011b55401001641c00110451003004002800c8128407000c880362007496503103c064548540040c0100c10b406c0d42184549540300b03070144100180681c000d02100c0030090300034074401c5090f030006071280d030303e0102c924000f510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 762822284 1250 762821034 762821041
    0x2102003040b331014030601030b042307090e101205030d1505030f01050105151e0313020a08012c0a08130314032b0b09040b060109270c05041508 64
    0x2041071356014400e12a0510480d24108010054064030005001c5030406541d20424003080d07483d980f00b0000101c4180e0151142a0300050306609070000b80e40000c00300794a4100020764030301d446043d501c84d0800c1c0c427801d080d42e4648000302142426a179000c039010302003409503d000e429a8072030544a0004070034000b40c014940401e00d400c00c0550601c980050741400d0044c401c907100e0f0000c3c4240e0342c101074001380c0d40d9503050211440b54948800d880d4107082c0c0000501590190314490030102c0703802150418802540c52611a00301e40480c4511002d00648448000c817250725141305411800c000b60607200104d110b0343c0c81340490303400503600c000301d0a07108405000303002e00810075041c04590070000b14903108170810301c0c41018105100012412250b00d03810280b0f4159030700b14218210b00501203c01c5070400b80781c80b06032444d040380c546002a10418000501d000440b04220300310f01d180a8031112117a813400c442d4043d2034028500014018200310000b0b042c0c0b003500b46072980705240c4e03517420030303c1c00d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 762823534 1250 762822284 762822289
    0xc1b03120c0b040f0609050d080907050607050d1805060d020d06090b0108010b0a18032006040b160c0512030a02190b0718080d02102003040b33 63
    0x40a48001084904007807080000c0c40700010a42141c0c1002202040008500c0e00202412030460020081d00540b2410300704683c1080c0c42c7c90250042c00280c810942d02d030350601c129805290030241190748014410071001d40100c00c0c0075140c1c6a94940c49060315114000f08201e644100528410740f40c0c0000c8111520318944220b90161041c0314007031141210100008103505810300031012080000035158003c2f5020300d0155069040c6c0480f8248100d1f40c0e410055410807000145a05840c07050180c0d068a00d4800111000c1d01e03109502d860070545100d1413141103441e110030440c2d4049145501054994818440f0146c1300d030301c000155501e04803203200905200c035000e22030800e142400701030400a0174600f99246d001c80c4030310f401c4d503550b405030b1441500102c007a8000f907054002c9a10300720300703241d02240c400c080215000301402010400010400c60584a8410f294880010310124002a030460b81c3c03150092a142c41d0300c100364101c03246a1040c201500450104504d03480d08180407070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 762824784 1250 762823534 762823553
    0x3060e1504150305030a08090f0105181b2b05011d150408070b06010201090212030c070b04030809010309080d1a100e18100b0f0901030b150403060209010c1b03 70
    0x903000e0030219541a10f0740e5912903490081115002c00d20044c40300040310345804221546130204484000c0c09941007030841950300c0c1c2a410301c1004280101c030790000d00c0494a140d505000b500152141012100700d079644100180101c502004120350500b00001181c000d018421140c0210b555191010200015892400e443d890b9010b89916040c1c1c20000880d8542062b184100c1c2c0058182421703a5030107004030300400d0070100096200520f191104203c8100101030402079120340c040b9030340d140d11003054240501840c80b00910b084000c100c1a00c4030352003a00f05002040c4620300d114106080c00d6410320a41d685030480f0283c2b10854083c0303010a2620ba801101c2041081c1001c0c088581c4900c04510780c03041e01c030000024020900003041440c1a8003106000900ba01c1158948981c0e200f40c0104440c0e0014001c2400682400030720100e500d00a08078560800740480c01c1c81c03a262039990b40b10080d410030440d02d0306002c1c85801041c049203a0a102858116003245c0c00704105080d4039001444 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 762826034 1250 762824784 762824801
    0x90c1b0c0f0d200609040207120806010e0a12061d0a03030c0c0b181915050105030303010510030510151701062606030c0307170706031a010f03060e1504 67
    0x204103a0340e84402080e505400c00700703031103400c4500703e52902e203020204410740300d00340e0381c240c2040c80042c1c91814047c0c12981c0c210781c58101d40d10381801e500d034840110790718180c4030106540011910810400c511100d107032100341c58030646c00071a081c1e1410200d201000d040d0441490250400b0364000700b099410f1181545551441c01d00304003200311078580d910800780003080c50310164008110803882d030504006050302852082a0b0441c140c17114a8002c50440c0c014aa2407025401c103400807a030751401100341c6c0d06a52015000c0ac3c0c0b07001340054220b000d00409041800f443c09440400710310342e101e84880083c49860f540300d84202072054540181c007190164404402c102e044040d580c80e0192008900c1603000c0011407120541e184c4900003410107030340207103050385403086000c00543c3c0d107031102e080c00d0705020070310545801c1da80e0b468060741501c82940b500c1c40402c0d560b08040d1031540c003c0107601300b503004034940004c180382c80300400e44008100b40c40c82c42c8524a500420710040c541030003550304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 762827284 1250 762826034 762826039
    0x803071119060b0406090606090509060306061f090302030304030c03200109121704080f06010905090c0d1401050108010e100605060d0c1b0f060b030a050705090c1b0c0f 74
    0x40c140c040300c04451407640d0900000704519110748240603295100e80007000501081c50040114554442e00a001c0800034441c1c1030140c0040800209540341c003080d110311942c805802ca09010102c01c01890905800e074056105110f0036150100240e28100040c0024511030b00b081e801441c01c40c2400c0540c2c401c400c1840c00001c0342000960715690f40006c1d078800300c609400300c1e45000c0d8101d00d011161f41c070b00702c140c1c40845d0002040010b00300c0000581440b104280344103881c920f90305d8140c03d1003952000c899035080390f0300c26006a42c1c5410404030f0f40329994001c180d07441c2e81c0e400d0b0b006502d0030344000380d004100c1d5a448208441c048401404500b04051010b002004468546004203c40307001300e440c034000c010741c4c50091042060140410350441c0d2040c01401c030850485140c202d0f816400003078152856840d1446200140c107002030100c00032034014009004d560f1030502041034000000b0003100b0158010b001c1c0350a840c48840d0701d1040f0462803009040060030769801e00840c50080d56083c0e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 762828534 1250 762827284 762827293
    0x9060f06040c0f051c09060b1002030711060310050405040b010801180209150607080d09060b0a051c02041e060503060c040f09050c120403020c090a0606090905040c030204060308030711 81
    0x1000d150818001d0581c10f1180c04d01948552034040d80300c1010103101c00c1e050210341000103e00811042c0d50069241c0c900440301031074486d0890b07070b0890b5a80aa0017006040f00a1086500c1052600344055544040010201c0c031005446002003401d0315015102103580050510060048400030301400340900004444040b04a22540002e2a0076030043c00407004e01780858070310031082d10342c0812202d00c0c03600560b1160f9500b00814090009000ca0b6900b61041890050108514a805120181110b4008103a025281c8860342c070b200410500c0c0d40c040740d00c180d5422a0041c9404c07030340c0b00c282e00d6010380000092214640420305050800c0201b149820410412051000300628000001035414000c800513040c1e50b43c0054540910901e00e0201205500e903041000f019400189540000e10070344400440ba120001280c0aa035058040ca401082c60144140310711102680690361242c058110001165501c2e00450211100c130b0308281c0307007141c1c00070410021540182200031020781e580d0042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 762829784 1250 762828534 762828551
    0x260702120c1c060b12070e0106020d0507020f01171f0509040302030703110f030d0f0f060807060f0e15040501081302150a0c140c01020c18070516080309060f0604 71
    0x70440c482d1920040403044041c0c50007824840e29510484030031358058800405d46110341405640c610003440340e020030040000020902610108050030030381403540b14541006c01540c20400340c034005001141c100b08a0720500124182040c0109010302403004031140181c940d441130184112a40e0081c1d4007610b0108140000070b03600104403290580c140c50003044030304440d007a007424000070301c14070203040c480803400110401d4658001c01403455015000c1000500c100004804e40c4c48501c58001e540c0c0003580308110480c090350034000b0f06440fa00d00049011880800110312004098030940d8031080850180090b58001c1e0031550058150701c50201504240d0b03001844500045048200c010310210301030364482e00600c80400c0b0079510503001240c504072604030503550300c0f508107080c1c010b11440f2819001c034281b0341c030311006030b07400040f0104050351110703820b580c1c9a00c074401003004400f0350b14207030b404a00f095000c1c500852244001c3c2c0fa148c180080c001d0300c421405041c55211724501a8035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 762831034 1250 762829784 762829789
    0x3050103081b0307060e01060501030e0f120c010e070e07170c09012102070b040219061205060105071514010911161e03050c210304060207260702120c 66
    0x2610381952401c00c2c0180c505094010443c151300038800c0050400e070030f06110000341c00040d003202007502e0080e82e04006c0445404002680c846604a02c6595504030a80f81e183c54280034006260700f0303a250340003041e0041e0b050403540c50916035901c00320f500c016060911400541c440483c03146024584035a100d542850302400c50f640c801e010015040c03101c07980b50496856121402804450b041200464403662a81010100000200c1c1c04a2103404070035400c00c03c03003c0c000044011340e07a10f130342c4814444945001d9040208405491070b41806801e20182000490802c082c40a0302c3c4d00c500c000c94080f000d0741c0464000c030b07810303044050f00e24140080b01000354010000e45240340700e80c0030802246001400d00407180d0320140b0000d0440e00640441000303164104000f407000011103000c0341e041c55100c108100300f454280181ca00c01103400c001040209003103030043c0c00d0150241c58007913084050001c801c40c28402c003000d0100c542001050190035460448480188000c3c404054103151600800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 762832284 1250 762831034 762831037
    0x315092f1606090b040f0308061905040b120729090f090612010510030b1806010b07030201020d021204062f0f0c07080c09100e0703050c0c010504080a030c0305010308 73
    0x420a841c1c4150324490382031084540291a100ea0040d2400c00d280c101400c08440c0b4840902090f00480c02e510081105820314045020b85181448242070210f800c200420001e0410203115035809401c5546880b500d050901c5218000d2003590b1a40820f00a040c040300c808040050184101401c14018000540c0b40d84440310020442224078400b01c1c2d90f100700240c07040f1010a00743c500c941c0b0b004100320000700b6050010003600d000e50b810424641d104e440000c01ca18100510b070000381c01c46030040118030041d401401c050b6200c0d00025040c5039550303030300c1c2c0104e800040c040d0305142045014041849000c0c0f00e58000c7e100010750302030443d07800c8031080d06110030200c0c823040c00150001d0100000e0f0900c1d42603581d500c0c42001681c0d2001d944070021540d1700e00300045184104456804200e03007518074501c031002c9414000391100f2680e01c02d081031f0000c20000b0403002851908000388400000c0070710909100301d2051400350b0320381568150060031100c002110005041c500070050021508000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 762833534 1250 762832284 762832297
    0x1203040f060b0607061103073c1e08010e091b100e090126060108120906041706091e06130204060308070807020306100b0702040b010315092f 62
    0x80802c1d036070341c4800419600d00c0740d000080e010900d030a00700103801a80100850080510782d44d00c80d5940c07001230b43c0c1c54218403602c5c2030340a40141e051160504091518102a1a0140d410100704101d0094492018103e00c24013480c00104144018040c100142d000560060000e01c01488911209074403010305000c642d0071244200888050310200920440800c5c070340036009000b288695940b01192412200b0a29000040065400c10036028200019419040b100e00c080140030003143d5080388034941d0b010158040d00003104000201d844000b42d04024a001644801003640b49006910740d405c2910701e0b40c0101e11071034000a101c40c15000040c50941191038a03000d41c602c2c80513440002c0082260307a10040032208082216414007071100e002d011b01900a4007596907564601c00d04580d80110f500a07080d8085050000c4000b5040035848842c01240604000405158030b0b40103203503403001c6601c0040b1840d2540e01c03001048603d009452410800303185c42c040c403131020302e11280c020f02400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 762834784 1250 762833534 762833543
    0x2104031509030f140c150123091302040212090d140901020c09360f21090406050310091a0606220b030103080a23030c070501090203030a030b031203040f 67
    0x18940c19003640349030121507a07900fa420480c6c607992078035910415010024451480d203080c07208500200c80280e0107600c182403c00802e40c024030340e110107150084461b18181aa0013a50030b00680c04002881c240031030041c2d0700ca44c0207028049400c00e00400d0540742941c41101c03040140b0032801241d800041c0f02c408008100d0300c0004580c0d038004030116500764409000c4020040550306a03158042e404100300b006100c41c107849402c5414441d65513203142201001c00d00c156041a00381c0c3c02d248400207030007800c0006002003402035030388c1d002074508151020302d081c400e6a1000c1c100108a40751010381d40c9440d80c214080254a4100300050a42c040c3c03408100314504c00046050141403040c84810141c4a069205601e03540c59083c06821604410b14007004181f0000421041c01d801500c81550100d0325020b041c41e50b80c03468195002504280c200b11001d649454400c80140e905102802508149039000103c1c0b1900104061600b904420b40c1d6420340010024800400d0b0154810500c03260070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 762836034 1250 762834784 762834797
    0x6130507050609060f0a090810150e150d0605070e0d0b0f0c0403060c051b0118021005040906090e0d08070804020f0d122102040501051b2104031509030f 67
    0x1801113a1544148403804541500c001601019182c01200400664940000302c0c3d4600b43c03085040c1c8121000c0181005007907040382d0b01002040030480d8403036070042100740b540380c907030702c0b110041540d03000c80c442c0c1194015183e00421059542c44010304c1114241159402900c0034141c484c52011038010300306415407852580082c02c000401c1040f28000c5602c1401000301001c681401409508452115079019103030440384a91a403050250b600071400c5138040e0b0a06900d40e908200c0c2d00b0f08119034120501070240000910103100784181c2c8001c180104020906c518101507050901c070840b8508003c1c0107165080c00210b55000e5043ea40c4035a0581e00940f40c1212940024541c0325000700007440010410343c020f15807a8841984200c40e000d103000406000301c400b400f01e00340c2c051402898005031052000307502403003c0528803113240e100c2c1015aa609543c1603500500c1c451404000039180400050810030020034819161002d083c0410400c184030590f0380041c07800300d10489000c100580e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 762837284 1250 762836034 762836047
    0x20d23072306010801020304060f05010e1612020a03020c0d170a02070f06051501031401140d11060c0a0b060603010f05131e06060219020901061d21061305070506 71
    0x34181d45952103a041501107030768640c0d582c4a1313240030358000c86040f00c1d081d08002c0080399015544c003665060f14a50410b4120a5803010707120b0358041a0944072400b0080310805440c4a0646440208940071003a580541d0b942401180545000c100c6c0040504110200d090182180c2d24401000d40003035100c1c1000d60b444200c0d04104040541d0300c0c00140140f4904070900501406008004541030401e880c140600c044503180003489500134440d01d18000070b5110501b2442c81d0440b40c4000c2c10344100740c9901c5090002c400700d003080e000922481d00545c44001010140003100303c6c0035510000c2211564035541c103002640381001c00324801d0601841111450b11400c503e650000940d208008501900310001103840a0251602e44605005030042d048500116645040ca403240c8a4000c2c1c46080240d00e07004003100c4035100c01e400607060190600c00004141ea503c80110300000e1400203104d00d10080041860034031340301030303c0390081d41c02100000002031408552034044800456600e40c4841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 762838534 1250 762837284 762837323
    0x61b08191115061206010b042607080c130c1209080d141005060f0306121608030a0e030a051b130e01090c0b070309050904080904020307020d2307 64
    0x404040300103001d401904803540a500301040b08500c644412100c1c454500a002829520b0b90801e0240c602c0c0310304200001c3c405031680301580e4a10000402600c0e85a602c0d00f1076240c1080d519401c0070402d9004400904d200307141ca2084500c15101c84c0d6400c00140800d4400070b00030b100034030090701009448013543d030103100d550001da810450460b036080c442e5400244100e015840102d400d0741110746002e0011820b81004400d0314402d1900c90092861501d40804020740107100480200230f0717110710102241c0381c04142100c01c0080501e00b00564848071a440e001d41500c0b4601c002d14080d900402600000c16070024000800c0d0707001c018580c400128030004074a051840c015a07010090402c05110560681544800621401203030480a401c1d1100c0510701c403031046610140016841d91814816480c2000c501303a00a4802c8100624000d045030101d0203a800440784200542c0243c3c0140403041d811074000c0c5454241c0d0380381d0400301d0010705a0003101c0c2c0030f41500074120810380c0703000d1010079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 762839784 1250 762838534 762838547
    0x703021011060702060106020d03060506040b03100b16020108070f0c12050c030406090914041709010203040e07030c030c050903070311061b03040306111c091b0f061b0819 75
    0x3007450405458051614000203913a400c420710507400144241c04040b04c035140721744105003d032400201307228585490192502003036000a0807040b003091200c0030016811892000500300182c2d201c600510b1050980005059544000c2c91a000d010316540c00d11140b640c0201c5171a003603948a807010030f800d85080422101405502445d41061100041c0452071940000303a0b0802c075942c0c0784051102e0709101e0350410060800307640c003e241d16050b80d00482c03600706d803e0150042e800c040c41100d00701360b130b580c00b07030301c000c40e0300f0707141c2c080800c1d47c415070002c0103035050048100d44611810014504014900401d9660000d48005410700d5070300a1100303440c0c4d480c90704031f070582c0002d2501202c5e09413149031840c0d140e03400781c8400c43c0c1051806006005400140056500d1404881001441140c0c07207001070020700290041216844501c3e00307402c0074400b6849055001d4860f004d400d80c0400d080c120003500030503682802811006509180e10700044c0698121a05040c1d4005141804160002c2c2a10310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 762841034 1250 762839784 762839807
    0xe07030c060203041719021003090b010b0714070602030f0a0e0a030b01180b01050f030c121501030e010207050a06090201170a050f180703170d020f0315011107030210 73
    0x1108005101c0c1e80c000b0141c401d403841090051003c101c02c00707116036500142500c0460010b142c01c16400540742c01551003070420300d2414007249500b001e59404041a609800900e8410400b00d0958144034542140b07050040d0040010030600307080a0002c1e559000761202c0034190140090702d01d03c0346204075100c11106401500403284161245441d080c01c00c024050520081000619501c0d603141c6030040c11051034041e100e162034000070006501e42c0e68001001d82c0704500b81003189991040381c2c135210030f100e00c41c290340300400648000001010390f042400c840902d6030048c0300e00d5012540c045184031106e81c3c0301c04c0c0020081c020b4030044c1d0390412800390100745d01000c1c2c03007000000c05081c0c0085120304182c2500403000c0c1d491141c1030441c0f4858481d2640c03103a0150307005000140790f04e44100568000d03a52030034142001520b2003000e913800b0150580c011a408800d214144180c800981c000c040d007420450591201071005658448c1c140c40082c2c8100d000b1140340c8943d81c001d410b0400c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 762842284 1250 762841034 762841043
    0x6020d0e0909120c0102250309150504050d050a020405090714060901021e072912090313081b0a030f0b060415091a091006081b07050a110406050604090e0703 69
    0x300d808088113024000e4104030051404944c3c114601d4010b96040c04403100c501780c1c15101e0500003410142da203a004d216101c0d4003801c1c000108008603c5a403a04220b018540c0b0420041424041c140706000940e60f01911140a985c0010004d108181c422003000010f0403040e1002a00d9020000040f840c00b04410000501d5a02c080104002c0703a4000c10780e40c00703880e44a040200c550000f12000061418120414420303850244240030213801001c590300d40007911201101d007031103600d08010360b0f41281540f0841507a440840c610b40b16030584103010010200445100d5081031540d01d0306901c1069aa40c000e10b140040f60005403265515030001d08a0507502c0000781d041d507242d01100c001007803000841310812131240c0d9110124a00908501e10850000440c401c2c081d14203441074600b0100540100900c1c20700201b00d4a0a081c0100540042da00810041c00c10300c1c010b041510040501d50380301d0b809503003080307000d10094580030103d50490340c800790000340404403201c41d01e040101d10341000b403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 762843534 1250 762842284 762842287
    0x9020d080a051e04060804061508030d140a06080c09090102122d091902150c010b0a090905030a0e13050708060117040f08030402011202030f040c06020d0e090912 71
    0x4411075008000d030501403054414980c3c01c504481040100d4080d0748215400603060400007000a11990001c003080080000c04c0c20150b6101c071400c0c1c0c1150001864071043c41c0c5c1e503070049131b03c11a07080030b29604201c0120f01042480c0c244920a40c407103125008881c05180f6290100319014401d42c101d8004008810303010805d0300700206140104400c0c49018a02c036010b03903540c0c0d110790403040000350281d41044004e000e40d0300012030380c0051034914003080e139011680428402c4911082801007480b02034110000540844003410400d20010a4001c013a59610b448403100005200004403803c1d8059824586076070000113000490348041c66005000301410503050000e80380d04512a503004ac1000d0f00d418642050031810032541d46011100540307040c00342c0d00d5500220708410015a0480d00605d001040001340d11303a110b040c4d0f407041d01c440c0c6e4020480342c100002c3c03010840794071015040520251481068006000703107039a1000ca24944984400c0010403000c68003002040c80d01411300c48030380d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 762844784 1250 762843534 762843547
    0x11e0305040c0e04111f0c0210050c030c030d0c0f2a1a04060f090f0b060d020d03022407120c09091107150b0904120c020409050303041b140409020d08 66
    0x60207441780081050241e0514081104c0700d440c0308100f03522451040d41d91100740500c0d40c00b0484000144600310052203010400e0864150080c8010402018920001c6694180758071900b000c0350090401038082002d00c06040c9106a44240c81d080c000c0c640e503604072105c011420300b1104801054030b00405a50010155001040a44050600c01c0b4000c0000701302110441e0000803d66203410401480d080c0344822407800561941c0d4039982140010740807002a0a8039808034801200d90001030300944d01031909a003e1412401500c2c046c00e82c86840011a401d02c00005441206a00380c004283c80c0c481070220041d0f8421079214000700030070343d002c2c0041c8810441103031003a809082d058640d0a0210307a190094060750050444001000c1d1500c46141d032a51281c110301e81c042c408400c10031040c1d101450142e961070050a0490b8041d101a564034201403401b6508000340080c130808005d002001040007800e1100401040d96050b24045440002c51000400080464800800b070031000f0989 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 762846034 1250 762844784 762844793
    0x70516080a0b0105240c01110f0322200d02040609020d0b0d0803060915040903030c030f0e07051203041805090f0c091b120106030218011e0305040c0e04 67
    0x100d40995004100107030b41a601d8030b0910017201d06650a0b40e0407128040c010400c10703141d030030003045005600000082c0101207014541c4050340140074401d80500e006c814413150741150f039040e5a5030710341544054210502e0f41e6035411a0700e0103406035000440c595241d41220f89424140c0500301d40d0041080044584488043e0000d4204070349446075185081080e01d4241000f540c000c00700e80e0001001c90841c3da0385020000c000344000c0c200900c4005824a085803521140142405248039403004250205c50b440014104d41c410180240364a041858007544050003040210a0b141d0035903040d801511252407480c42d5100300d40c000f0041c1000c00c0b11380c0744001e8a55102c01e01400b040c100740da141c460355501c0c165407403a03002d05255000a0a5012949501d01d1080c0c0c40c03d1440ca45203042d0900380a0b0428131400c02c0300364403090100740c00103210700000307000d2203410000410908001e1149000034504105491040c1c0800c41130503070380c6000c0340511122076070a600030f0104691901440c07074540352 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 762847284 1250 762846034 762846043
    0x3070e10020f0a051605010c0c1e0801230f0f04060b0607020909010902181b07020a150f03050a0e060c090409050a14010c11030a0e060c0109060506090702010c050a0507051608 77
    0x21010024010740c100411b40c0e601c20409001c0a940140302410224101065407080d15807100d200000a5411600010205020b000382c04240740b90010000d00301001c58110000350000410b402014100c4904102258011440c89500950403110001e043c1c03543c1d4000c02d055204850010b5071024602e0104441410305400c586950341c0309643e03240d6014144280c00900b044150f03604d00038884052142d60107a90000301a2583c24002003060007043d59488003d040700030b010803045c00294a0815188107150140569600121825020400240030400d400c0d203070303600503202c27480f003010001e4034101d196110f401040304950001d01351040e1191a2230441d05040c0300340035004032942000c0000ca001401403241022180001d0061881e10802e103104036a9031000f050b080307030702000a200c01c0058081c00d200b0300013118800c00d0000b07400c0c03d10300304000740950000c0c01d00381107a052094031011180e00209170f600d0300444d030038804d03112021031a11030705000c154144000c1c000182440011000301c0000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 762848534 1250 762847284 762847303
    0x20a1706032505120a050d08090309100e0f01140a120603080406230304031409040e010203011403010605150403020d06410723040e092103070e10020f0a05 68
    0x104c00041c180074060b11261a40c1240c3c801030290b0704031071b1101e0000703405000d02e00e5000035884190391074032207101d0001c0c200c412a03405103800030b404d001c00c0105030300b04080d60341c5c501e49090038100041c540c0c84841c0255441000018000c20007005c1c0c1c0501400c0301074002901071940105901d8446494080081c41c02e4a140641640d801c001004511740c00e28503002c0b00e02407030705580c4507403140300048110300581d40450039030354101e0307940c846452118500703101450180c40103090118820207605d0415096491a4020314071860640d001080004098401c50741180d605031000d00903400c0906140300104200070820040d1354042c50005082c441c1100e10b000c0b1301218040c0a00540610b814001c08600212440404a21107195440101c3c3c0c800001c48440d1b034074226000d18046e1101801c1480030010741b0305a00580c0324410320000300c406004e1611103074807082d1280e421403a08082c000c4c8003605d050b0f03c00740161002106884254820f01c10381c1032400c03c0004079010104c071480d201b6660b0103c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 762849784 1250 762848534 762848539
    0x30b01050903010219021515010806130603120906090f050108040302120d020703081513020d0b19050406061b020105090105120f0108010b0a060c060509010b120a1104020a1706032505 80
    0x1680b629040348899110380c0c020036403014142d40d034890400040d9100ac0c80580380035800200c256101c84045020f0040c840078520880e0202d18091030101c025000d1040394000500f4403910314030500604034032000d1030341110400d10f40203913107071960300b07060341810040b071889000200700045540181c0f0058009100452080da140c17a20340e5600a01c040249031103001881c0e200d103c0c1e501104250049402410315031307001e0b000005200c540d09d0300186445074a110851888892080c080010b8a01846603130010134190030507880100911454100160201500a051040106015400364403940a45401e100c0e152080c03041420800c00305a010b1307009110b03000e003643c2071414601c20380c00c000800c4002c4035440c0d2641c50b0342d8071003903540801510005095020070365a404140c0b1140e81c500404640491101010308244400360a16010000145950034001c2e40100145222a640710340b001d0194a80702508485903112900000d04040e16070003ca001d01003811405140130171141c28a00440d03d04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 762851034 1250 762849784 762849793
    0xc10050430022817043209060d080f0409050106021e010b01090302010c0f0f0b0a050714030c030a060f08010c120c1e02190f0203210a030b0105090301021902 69
    0x4080e021507100714080000039540f64001068400581e00361060f2054451401501d0305180c1c403282d2958904855454185403071100304091011400c1d030020700b06000c1c4080e110760f40300d49012030204507881007100009003a01d9001449100110000040d0380181141d14000c3c480707569a0345c4021b6031000f22520400301400d2201da074000c110b0301442200030a00040e140c00c5407861442d001943c581411100550b07d00ca810301c074072000150500390558050b4880c07006003500b42045000388049078401029034007800b5101c60804070484424055a41c80030b8580300072a525a500914000035154035400303440c10343d07802100481d054806412a8818680d103681d00c07000c01c2009603030780c010303107660580c0400401c00306800c401c904010b049080c0444002801250f042011081480710b402040038030590f80c2101501e24441149001c3c031031140c0b080c0d610603c0705048070111460f8509880303103015a00c2403660b512504103007070b405402500d8681000400031900c4401030030340a00212007202080005004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 762852284 1250 762851034 762851053
    0x7020c01181e03080c01060f080a020a03060c0c020d0302030c1002030f0105010e030f06070302030f0c07051b0103110f1e030106090506310807050301020c1005043002 73
    0x10420007200310010601c84207040615001c00103408904052000442c002070309004404140c4081c001d124400092000040d402d01d000340e400d00260050b0444046a004000920056500d10004205803600058000746c1c0c46502c4000f5a010803002a0003500480c16442000500d9000703c06003400084c000d003902e001c2d00303010400404911003107503410f40002d1210014040755105800300d0002e03000c06401c660192200f98141440e1000844080c000680c0000810081c0041e021a45e5004a00c48005a04012842e42d0301e035110b00c1059084a01c0c00c0c504142049c00742c3c420f40090140030035235030042d680c6080720b040d000c92680c0400850801840e105211188044250085038126000c613038506844a081c80c0407c440ca5202c45480e000c1540e50f80f41e80c107240703c0500f000c05940c444a0100c0c4500030701c1d00000500f02503440c1d0116109900c10300280300d2091000c82c0070354032940107250000307a80c0c0d503914060500c00c00408507400710080785d50401206852680120071640c2d6141c08440035000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 762853534 1250 762852284 762852287
    0x60509090c01080112061e06050a1a160c05100c021c0c15050d020a0203070b06030d0c2607030513050a0b190e0301110d0b0607050a083007020c01 64
    0x12201d0003028009a075036401040074982948908a80d80d20032000810346642000241f50091002c070341c3d0301c4a0950f0b410741088680341c05402a8002c1600c9a901404062401403000c0c070790090118a014a0f800108400100217482c50400041e104c0140070402c0c5040c520001010700080410407801468140384881d100700070000c20400d01503011038480b0000e41400106115452034035170040c288502884114001318003030002c0c20b141203459000f16100c00b03040c181540c0c4000082d0602d8029000100754201d1903a000380c02d40307006500b2402d80c108843d015224400140340585484c18070580205031142010342c00001400c03c508180443c1c0d43c00d507241d104100e0310384031a2203100c9403140100400742c06070480c0c840c449401049810b1082032418000c0210342907599203c8200103c000026003500c00c510a4414000c003003c09580c0c00782007858940d034140d540c2e644900c3c0035145030008518148031112604130072402050000f034003000881c0e55071410503448800d80300d060150246540301c08055 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 762854784 1250 762853534 762853543
    0x117010b09121b121501030f0203010c2a1a0a0914070806160324080f011a010e030a15020904050c07021e030309060c031315080106180302031006050909 67
    0x45103510a000166840e000030030203030145000e82c084c014000c00c070030802e03810300c1a02800e00a501840b96480320400610415003100e188011890a000c05500480c005c0b20618210750101c4800d60092408807415042580118020340307030703440640a043c42000184140e5800440a007072041303460b40c49400703030401180d8036009640101c0c80260322030000512465910384810040041505000509059100440c1c1682d51201860000065084000c022000041000880b000e150200070402c8040088000c00c540c0b0740d540c401c038100241e8000b520303c980d6043c070980001b6a880705275455080c00500e2000040c0d00518040c030303c205c0c40c02001a200d400c010b0100e4003240d43c020b003041240c4000d840c0564260f06c01c042d0041d010320050056510740e48458000703102020000b0004c60300c540b44c00d121081091101c0d040710347c2400c2000b81d4a50f03069004802e040c10340d480350610300728007c181c10305501c225405620195052246c90603600c404000c0303078012416200c00707480c1800c3c1540c41c0d0f810383c1c1d5507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 762856034 1250 762854784 762854803
    0x50c010206090309042007030c020102070f06120e070e0702071806060509040f0e030c03180a081005061c030e19121449080f060117010b0912 62
    0x10350400c1204c20021300d816031080100004000c000004150300031400c42d980e411004089010800411188007550703010000c80000381240d1140c0c0b80040d0800b0780050a1460810300c0136161610781019080445003401080301030641d29180f0b04807860850ba000b0b5a0303002c28422098500a822030045204074075029130000d65412f5203481c0e2418100c0d500380001054802482440203541e0100302c0540ca000344002c001112040005580f103c440a40300b0340912344910030240300d01c031801401c002e49440424000d40d2840480400106c5aa80c4004200f4100c01940586041621213072804100340c0c000fa106400051305841c5000d0000c02230400041c88c84d460300450424071000c11401c0c0001e080c15a18140c00119103040c0c500c01e0f03c461490040c100d00c2c41c104503004c2c2c92030494501d4034849031107965100d0300c0d00c140441c104807440e241c040c02da03600140c0202d2100d10704000003480b6034050441d2440d000c40000031a00290382d0b900c0480d14941102c9001440f440354007244e194500000a026400c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 762857284 1250 762856034 762856051
    0x1205010801060b041e23090c160b1509010b0309060f01210201090b07050304060219120e0d0b090610090221250306031406070807050c030d0612050c010206 68
    0x15181c117058604290700385116500a2201c4401c00214215142c0401d6100030108055000c450002c12420080903040c0108110301c80002030062036000d00d603850180724502d8000b42030a62548a5000762549603000c00342041d0004481e200014500303031010300a41c800c0c03071b140d0300b034032055140c0c001800c001d080f082c41116000c04003042580800703142c81600da66002d04c141410003100e03540b11000c105035004640d050320507400c0401e082014079018015908034110501100742d0038070300c940c0c80c4c56070047c110005070b0420140d032801c0380c21521545140e0800b2600206a44a5841e1001186680b08000c41d280340b003c1d0301076040000c00070428000c1e901c0b444907040e1740c40700039241c03450200c0c024400181040501e40814008100d00c0ea88141e00f41c40c14155580c2c003103030301130071410402d6000e00754180e6100d50340e0000381081031959000d0819038010005142440c2d60f08642c060a81c954050314010b101010b03d04540001e000c05000002ca004034806d00641c1d042580500040e078840404494002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 762858534 1250 762857284 762857287
    0xe060423070506030a02091c0c08060f0f1e091e15180a1a0a0b0603060904020d150c35130203010f020c010f06090b0a03022106071205010801060b 64
    0x442890f04030091039124000c100014182540b4100080840c140341e0400035841c441f18035500300340305d8410710b2030001d8003088001b800c06040c04d084003204050000c120703014005000c40450b0a4404100c103049003020804801d030400e040420001e80c4402034207144912504072001120b0458401080320400391041d00c0440325140c0c3c45046600510103081620155405242850b0000038401d0700348401030f9012803501c003000d20700b034a40c0c0421240c10400c60b600c104410300412019594804446030b12a40c140d429142211007850031049403003a1280d840c8059081c40d40707603000d0a51140705000d402e0710310b10ba00d03844a40d0814850300010344a4035480300c001d0425000130100c04090040d16540d92000c1d00020f01000888202d80c12030b041002180c1c84d81c1d44a014207411804617004441c0601030f070100c1040710f550f600001520380300b564440280507680100700d5404d011080d09101502c0106241a541d441c41c0c1080010490500304c003000001d03516010001c10321080c1403058806460040d414103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 762859784 1250 762858534 762858539
    0x503061809030f0304230d12050c090d051e0a02090a0e071e12081902070501021c030605030a060902031e0d0e031c02100608030c0d0c0507090e06042307 67
    0x3581d01d900003081900d039280114600101b500c07002e00c2c514580c1c102c0101503e0100c02c00d501c000c0825445190b900c0c88a0704060900071900b14040440d03e054000725540c01175240036240c130340c0c2031071070b0005404001c042078003021010050104a41d0902c40c802c43e410849940d44100201c1200c1e0b0213000c24080c1e5111003024020b52006180c0340407200178048070608403d5984044060310f840f0f5400c129058040070841c1510952001d0360301d41d17a00c80c140090710385030341031030b000030f40e034140c4024007034170b1000d10190340c1071402c3c003e41c85070020306405810b894414503907007132a001624106c03404900a00c594403a0080000e51710034202100700b1031030058121019540c208603030600da20580e09501d4061810000200c030181d0b42601aa000150082e02601140100301d20031504154000101600200302042042d040440d41c1c40d2a01e5490501c00400000f40c105186458a03d0300222002840c20301c17034158448002a210f8429842201d003109900103003600903420044822018026038400d000c103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 762861034 1250 762859784 762859807
    0x1d04020405060102030f03070905270c030619150f110318040b090703050f0105040903121a032a120a02040b0310060308030f090607090b0a050d020a050306180903 71
    0x11a03007203a0144126810240e0445084a190781f040d5032201c0880c0c00980100800e080c600381a038500d840780c041580f8400c1c10880c4108801c4001061414007001c00400100c4035920300750fa6546030500b0403001c100c25901c42d1a0010881c068588607004109004080f0062601c9a840b40b0707884545207000c0d5040c040301140340f548142c4590300e80d6602c561070b90104001d0343c0b249480309204040171b0382d01041900744481c0303030031a215040e000913011f07a0601b15a403010981101c03c0302030300d40358403100241e1310242617500460020200c402d50781c140191a004c0c00c00d000c0041121040c129040c0c14180714000380c01c1001100c0c030400b42e0030700081e000300403881e01610b400e034841e1480c89000303415201d0303a02c48030090504507041c030780044800c01c17404001e102c1100071019001d6445070b410001001d2a00b08150080c191403518031540c144c185000a80c100003e21800959088081c005401c1d07490b0190610040c045410464902c1e004040c20210f044294005d03a2026006640f0300e8050b5207054950003a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 762862284 1250 762861034 762861041
    0x4060513030602270f1c02060405030d020303090709061406031305030a020d020606040507080f130c150f0e0121090c24020f060f0a0b0d0302010c03061d040204 70
    0x10200044005000d0000c0420014002000c502c103114812035001140240303003a0a002035125030310b00a01c4e60805915544c0c603481001a00c0c61500c0f0b103c42100812440012000d2060750005901405800076054074281c00002460203409940207583d400340d1290210303011030b400c510640080f2000e80d403c5a145040c881c0046030411524010303031003804102c2d214580340d81c0c4a0f00f200c000503032000d0701c00311096505001c2141c1000045030f040c4041d041541d001007041c40003500789000e912034031021540420b00b43c4103c0c055030b40d00003800042d040d030f0b514900100c1c2e01140410350104020311201c0103041c0c07107007030b019403494016181c2680248100b07607280e81c1080e00b1518020166030310880745002c24010308060006041c0b138118415021142040900140881403a10040d540484500da600d1b00e000710308180d106051082d03d003002da5440f80c1c000040c1c03031a00d50060700080c00d485144181a41904600700c50300c6552800d20096549803128280c004015025110450b201d0000c00c00601c0c042c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 762863534 1250 762862284 762862297
    0x901140307050a05031f0f0807120b010b0306060705070f05100f080c030a0603021503040627080a05070f0b010321050403201503101505030708040204320a060b040605 73
    0x100070245841b288494418900715044410081e00f100c100300140b40c82005800c0c0608500140301680a00d65503039501c40d4601801480c0c0b414001000203007554135008191491070340c03c602190f4896503580524442203d2900445001d0324044120a40c2d42c1d00400711840d0040c0e50342d6034945a0f83e50070500d6181c03604094102c154580c1c5620f000009607441d400030410f09a250724201d80c2d80d0410b441d006084909003440700241c1e5400d900107403c1e00c02080c540c00c26140c0c2100100d69600040c200c120746c40d109100c002440e41210861032014403010030000b80c1641c0c820003c1c00c0040f4650980024880c8250111400081d4200000e00001e15480d080c210f8580403ca5810401e109500010303c0d0144110010b0f5100030021082190700301000d00c440000708030140000d10b240f01906801042444000d11900520610601207411500c2d0360741f04030b080420742090346039400b084400c42da86044681e107212440340c00e203d02007441d251461080c24125103a40c0011880c0c1482c04000361200d41120 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 762864784 1250 762863534 762863551
    0xc090103050601021029040e0703030c0c0b0d0902100e1014040f060228020d0b180102030109090506090c180403121a1216090b0d15020901140307050a0503 68
    0x2005c00702440125030154550404282d81d6034911204501d64172541e84804c100e015204505040304684030450210700070301581e0309407a00c0d050b20036150800c03050941240d0b0085005180018110f010307002d444d84000b00e6248202e0724285000040182140d94162a1100c0e0f070b80045100f560b10170300e03400b0783c0300790741101080d4001b503003410b9842c0c95a45204c40b82d58030031405030b00404601e018a070540040809040d01c210216640a60150045260321001031002041110701384080b552080c104401741020181001c025507403581c613488640050550180f085845100b00000b08c2c000020225104418480180c60b48056100380540c40403007042c082e10680038010404401a41d050080c010284840c420080054500b0042410702c030080040c0808115184c10074000380608606005550040310f44030800820700008820002d484c031121540f008244841c0040009000201500600030b110000d0322010a400300300d00c0034102507c0300701ea1600c00102c04110700301c0540e01a402454110904 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 762866034 1250 762864784 762864793
    0x50607021309060b0909010203010303051207021608160b12040602250c242c0a18050603150a0515090405010f0b0a050312180a090501080c090c09010305060102 70
    0x9490201044600030b02081c2c600a0722403044000d24103081e244a500240200f00861071980345450040103405940c1c00c0030303100b40300140851044d034402c202c08001c02d02898a0045070320b0342d500c0056030745e240380c4650114030303c030351000041d11100010680d450921a014201840d90b51340d03039140001d600a00c10304000e41c604184074911101405030310a24103114007940c9400c242400311607000d0306000e0481d070208088a505000c00d5541c8101a01c505ca9103010201d51080d48400c2c03034060b040007464005412407048240010144102d07203d41d1032490344044108401d44502040c180c0700d50031001807506c0068801c000c120480002d43c4116031101590341c01c00405100ca40015007055030a03542540c40b60b4503090446c1d4038652034401d13010b580300c0803641c845655143c240403a07140c0d140012040c090703400205002d8460090886c031080ca0030f000170078024044d600c1d015820001e1000380a400d8807071140303444140003420321a140a01480340e0274105410007590340011400b03040010900ea045028 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 762867284 1250 762866034 762866059
    0x14010c02040c140f0903060c072a1d06100c0309030f081b010b0108090106060c060f0b04060611010c050901050f0a0c050f01090b220b0a060f0905010e1005030705060702 74
    0x11240c001e82a070307041d072800306070783e49000c10300b00b624040c0041c0290400d02c1e000c000440014040d8030802c480fa06413402b900000d0035107211082d1199007154800b41182d0384407140d031049440c0c1d010415100308011074580035810a040022a0411001d40006002c00d0440005001080040414000040c41042080d01e8a10080030554400e41c0075079101c12242c0d184c3c0d0103400c0c650b810604c01d40c0c1c440312000003000107034507041004000003514007001d00b82c5070361030020f40b642c51b00b181c01c98400c14002600a01049a036400c0090030100442e100799455440c001d0f1850165110340308484461005030340c3e040c00c000502e1038011041c2c4c4049808000d1107505108080010010710281c070090103440b000281000d010304120820400042542c664015903006e0750801030604c611484900c2c0d0130080072022566018000030003044036800c12101c03d6460b05000070800c69a8000702e0589200201c81d00d07032030b1182018a044908a4001c1c40d5054000840500c55030a11101038022a400104000c60740c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 762868534 1250 762867284 762867317
    0x1020a0f053a14191512050a030807030e0318060c0a29060d0f1a01080709140709060f0903080d0203010801050105010f0f08070909021c0614010c02040c 67
    0x40d1140114456508002c40002072a10746108229061040408150084c50108001c04000010b0682d01c4042a80e6800324107004190305d4411000c0d204160441c1900d0070705042456035242c003600220005011000042e40491003406400311000d5000001c500b08094030181d44030440d1034402c0c8a07004003050000040380c0b01d040040d104528012031881003035607000607041400c1e01200303610605d080b01e11402d0210070744590040c140400d80018403984a041680340002011101418a24804920f0b60003c60441e001080c240100e6032220010412203100020701c001d000e408456020100743c880030200000390041d01a8261404545400307810162203690f040720f00e81000f1320304c448e460307070101c0140002c580922880f805440242005602d150760b0100c001d10440510000004000c40345e0042503100d805110050098950001d0641d1a04d80c040460741349112a480380301842070800000240f01c2980c0003540d010314106a40340582c04225400380000b5004a00c0c441c010442d00c1c00c035468891 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 762869784 1250 762868534 762868597
    0x80f07050102031315020414150412080c010f0608191403210606040f1e0b07080307142118030c0604050724030f0b0603100f0801020a0f05 61
    0x40c542d0107611030f13030038400c0d0500003101301c09865000c0203544100011700940c031700003d000ca0300c10403c41d038140e03a080d210810b160440c0990f9200d50a070201c0b040d101700801412002400b121903040c0c0080001040009503103040e58020302c20350803603401c121081464150354100da584024000c032010082e6040c0c2100b09895a80003e42881a8024103d480903007804901d880303540118045900d60304242c10315103030084080452160b010000d4404410354040182c481c10340004150b414130303064449000e030400342e240340c0c8121007140014000003120a9461040703000d58101003002803104552044281103000320000240408841c0b2503800b51205c480d4400700020140b10340e54501409040c2000e00e001841c1055580003d41c032180300c0c4000d003019000c3c40010020b0700e80c4525010034542e5007040d044000b81440240160007040020400036900301d2002480300726007036120b1140101d6a150a55802c034003c202a4900080c5403444103c41588508007422058010205920100b2101d40044e0904e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 762871034 1250 762869784 762869791
    0x10121b060e04050c09010f0c110405070c05011404080a0c2d17030417090105070b011512090c1205070e04060c08152404030f060e0d090e04080f0705010203 68
    0xa10060a0000c50742003500070f0681081500041030700700358400c000617205031102e2101e01d0402003d01c800c28103000006e0301000320454081e2017003000e801c203c0002810bc0031a41001d880300d6090480c10869040b82c26490340c0320b103400004030742c20005001c0c8120358803615220192004881d103458a208005005e030141d1074180329100c01e030b40d04081d0749880e40030200d01c0300305c01c0a452014010440400d41c441c04a5200d519802c0e41541e035110000016207244c000c840003e05848148000420700358070f4000e1400701180e0320380310190314940b888442e2068403000d02000b041a2100a03080003800010180e03242c0c16442034080c3c410329034803005000c82c0410100c1e02507440b50380324214460b4540d04030780d0103600604c101e0800070480c081c000c0442d120310503c00b5840440713481c15030b030003201e07032070300c0c0280c60245d5400445210a4101410401c000d03104402c03200c49a40100e07980300701d08900600803002240d20805501c51941da407502d03040c58a4004a20b1490055005c1006100040d82803004510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 762872284 1250 762871034 762871037
    0x3050306030c0a15030c0206010605030106120e300a09050d030c0503031303142b0e0d0e04060501090e04060f2304030806040e0c0613030807030503011d10121b06 71
    0x3500313501a0b000741030301c080101800554100000601000e903005c4100e905481c5d41c0e05041201d40b0241003132000030203100809104502503d5440d80680341036403006000403010645082e120005800c51280c144100f106144c045840c0e05003c0004d41440461503803032038003a0a00d00e0a00d8500e803a224115071080b02c414015840d040b41031010190814544440300402072801400c0109100001e0585d803070749141000d00085140550a040f0500d07046803103480c580c1c0f0141d5021505104d0064410107140c40b0192003107003800c8012403194490101e0808a42c81e07200d001c012a141c03510b0b60b6004009101c1413042541c0c0b18030703c1600c0350121201d43d001100f100602c00c0010f05c0c080c2002011b5040142c5034030702c6242062080158241c001901c0700304403804451711a650941c0402c5d42c601d61515600060042c0d502081110906403c18081c504a40001151000201c8076032100755420504079542140468100c50a04c06040c2251441c00c13060302c140c8020881c048400d4070440ea01d0b025030700020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 762873534 1250 762872284 762872309
    0x10e01020f0c2a0f0d05033405070509070203070b250311041e050406080610090915110d050103050609240c072105071e050a03050306030c0a 62
    0xa0640104015a00e04043c2c41c200d0308481d220a80c0640720200d4942d054148100d5102010075200d030380d2120a01d000640c8503041381c1d07880242c601025201c0c0d0110440e40b4a0043d000305071810385500d06124260f0030350000241503510b003010100040540302600d020f0841c0300c240721500004081c641c01500454002100111000b200589142c810301d01410f600708050a000d466040c101c0340c1400c0c0d0701615500d94819480e00816429200340004640c003a90f4001e0400320009100710000c04c8490003034404454043d241c1d5103a84280c4180d4007030042c01460000d001c0c1c1c00d8490700200d81d01c0054501184072810703140803441a841426a442a001950b05401000a10440d12003c0001d107000c0b0404020500004040c680c280d00300020081c2003a4810f10b00080c00c1040010410b6050140700030494103c1381d17844005c9c0e0042c50340d00444401c03a820401003805071008100c5802c060042984000203050301017440d03800f2101d540000d4060b94251007103402604241c0d840c8041c01c80a8070f0a0800039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 762874784 1250 762873534 762873547
    0x905100b0d022502010903170d02070c080c180c0a14071208011d01030f05010b060c060106021e0c0f010203040909110906090402280302040507020604030809031911010e01020f 77
    0x500021070f0802da001d101d08010480b07000142d8000030040120b982203441d4078100301100140013014410409226581c1e8400100f0400700402e4004000950f55104229400c00e203400b0244000c60000100180c0540c0e03249000079400d64501c0d004148545480c40e00c0320160300d01800740c03a020707082002d04441c501c00444154920340c1c0d00a48803401412060f5500c0124a040c0b100ca074801681800042c11002c00143d2003800d1007425000241c2c0d17120301400d0b160355000181490394a45c04d00f0f001d440014010001e60010600414141c3d04c0320420407401b501001405500300002c601806802a0641c0001c0c0400900c1e48594030503680c8050003418910010f0740c250b13080000b4110001e0906225142420600c405a1140c0083c0c00c03c081055000c56010043d01d40c120701c2c2e00200342d000940c401e0070201041072190380130540c1805030f80b181e00d40d6080d42e2240003503d80c40e4018a040207160040d400a44c5d1101d03031003200b0440d80c606000b000040c8d562503c03001d013820390f442807030124442e6200141c034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 762876034 1250 762874784 762874807
    0x109141e0316030309020307210c0911030a1a090a021c06030308010e0a0615050a08240f0111120408100b010f120b0d060e0c1203040905100b0d02 64
    0x8005150180c101551408511068841c6000703000703030001e0201980d80e46418110b45007005130340c0190054042c001074071758044140003000c0c036500304221003499001d0000960003a040c001c0c040340b074258808243c1150f945d514017600401703c040c40f02c840c4034084081e000d1151107010031507019810580c0c001da512104000c1c46562054140385030f003e500d00c1c1160800200798030510050540d1b0840306982040e403207a042e100003411440d00094101c1c0030a1641d13a1445401000030300f21300d030894540d411ba0355a130281c50b84920180f40284540b4100740010f681c00d503d0a50100301402c2c205040c40c0c2c1d64441d28004252400003e055001700d00d10000805010640d002c00811042c1074200000784850010b00d000200161402240070041c800c014580400d402007035081030b20b0542001c2c1502c04480001d007403500140c010140440745500490441aa00313041c00500703900c54101e84001546040d25244892000b480300038496100160080004600c121419000b44009102c0160160725250182036 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 762877284 1250 762876034 762876073
    0x609021002010b1203040503060c2b290d080307030905060a0e071505180a15030b041104060e060315270106320f07060e0c180a0509010914 61
    0x600200035402030001f040070b554002a01c60b40642c46051041e1540202e0104540c0c1151580c15555095051981c03400a10719589c00f20440280f0564030001400c92442d071b4141da00409000c090b000595104128085241240150340080711407800241c180d0300341c1c4035642082d9040d03d190030031640341d0030b4101400c2c0f010864031000d0704030240100c0f59041c5940c0c000c1c08510401c104d118090342c49140049040d49c900e0700a000405907102107200c030a0900d00b00600400b080c48030144507a1408502c3c07400401060242e805562040d00c8030400380c01810304112254000400688a283c01c0d03142a040c503480d59618944003131200d20580c80540721088070b40130481d105030081010005004040d590324500c0015040400384c6010551145040c14101c00407075108000f400c0c820707140002009410042a0b920605502c10620180c1d008c00c00a10200449200703600b554011030700b84200400d4168080d5032003503410801c030500000e01b00d40d481e0b442d4100800080001809038110075040d60080034041c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 762878534 1250 762877284 762877309
    0x14060a020306011b030903021005030601020d0207050102191118010305010c020d08060603091e0a05100504080915090a0306090b0604093201050406020a0f08060f09040609021002010b 80
    0x2441035046107400d000007006100384007540e840d01c0000704118000e06000788144000396030090032403020800f8009000e02583d1095862380e006114040144041c035101041030030507100e0513400b51000c104e8a800e107100d5203282c40c0c010354081c101503903001d0340d6665040080300c1c0d101b52281041e401e507145060944c01c40e1400c6581100750b4114102c003445940d8090a5035034061b508650903a102d8880d050340c0c170f14000381c11a0181c031750b54100850000c42e000000361480c610b40310310120b906010360102400700303071074059500604900741030208036500c1c80c0c014001a500c0c90ba850500f0706241848000a401c2c5009500c107440e4aa5903a114000340080032039116413110b004d44040c49001f043c0c0d51b40b066080b82c40000f07100c1c01d07108030000b26225401d04008a60f0742080744020b00540c00d20342021402075015030340c0403011480d8a049402c01c140030700b40041c0704800042402800780e203248188040380398014000c9410642d18944800103a840ca403100303910301000c0e400084d1400c0320505101840001c1c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 762879784 1250 762878534 762878551
    0x80a320927011806050604060f11012a05040e0c0304050a050102070f0201090b161713080d0207081c0c06020409090c0509280b0a24031b0c030309110d1406 68
    0x50410b02c42d5131506c6084a0460301107103040e0359200c00c1d951007100d0f03901c404203c850255081c4070100455007090358000060f401d15443d440c41c0212100f0040d03901d48668072418881041c40c0000a003110b16103805554054010010b880c1c0c075208075580c1d06d007240d0000c0004c036400042e002d407680655a00a400c0c901500040c1089890040e202d164440141805e00000785901015448118002d00540644441807100101080010384465000340c40e07003440c1014000500c01c40030000358100c8005501c1e2440d06000b0240c4021081245003110030892018050701c00c40e408010004043c02644202c0350010b014000c0030300324508190820800e480041c000c081d002c0b035403040000c00c0e400d0455041c038103607086600000d03902602c0c002040c0c000c1510740c05002010701001c20428a0161094410038a00ba10303501082007100c0070403101c0c100500b0022040001e841c4004150000b1301035400405804d0240396a50046840706001071550301c51100c0840b8643e003090b00d1001e820030100712850b0840c402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 762881034 1250 762879784 762879791
    0x30f07030b090f0c040b0408010614030c010c08030c120703020a0210050c1b0712032a080403030f120e0c01030f09020f0d060b060304080a3209270118 66
    0x10303007000800624000c1c15480701490180c0124100402d50011a0002e011400085444655400340d2078000c0c4a18030405030641d192031980c44e4245800b240b0341d641240140c58440345907406440d040c15a4200518840d1000e00400c9074000b1a034465500c07a125004a81c1c2c05640d41d000381000909042d8054001c440c4e00c5d080805010762200f442040d1034440d16141000402e03103659840c0c041c03800546500c9886c078258070b0140c000034190302420f00304010403034882071052883c1c41d0303040748a50030072884060001c4009000c24400244101c128140300c445901d004104c83c0030301e520b01011035000c04c280c40ca06030300150340c101241d6014041c5100c3c1003000701c010000c1403501d8011850b504800002140715a807240542010403607241d00c4114080c0c0e002e010031f92030b482c1618200015034001c2d50007001003100c2502084080400075450702a5030030b44c0d0784e2209001c0d00d04080320801d0304003030501d552043c4000c200400d40c10002c068210750820020503000903515140d000072001000c6000d08084030705 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 762882284 1250 762881034 762881051
    0x40312090c081e060705070314030405010b011b1505130203070e0714030c090409030203040902070b01050a0e060d0620130e060603010b072004020c010621030c0b07090e010b030f0703 80
    0xe020130041d40c018480e040080e40c8010700c1c030301100c82088220404149003400300600051240540c0150700229080c0ca0700c030305041186d05415507102c10311900524142d00e080d15059441040d80020703810a644044080b0302400c01d03070000c0d041104e190041c06070401440204080203a006c1c140c00c02203101c0e0030381c0341c1c41c50074810f900d040d242c8039031240c0304d0181d0303103920185082520800c01c03070b00288010300d021521581240307060400f0440c01c2c81014890a01000080f0701d080b00440114012140200801c0003901d690f594180540700f0309540040d05070807225815005c0080000500c1e48165940c3c1304416079047c620050b0600d040a070100340600421300052000588003002c8a407910b400180741d2919070229040000c10300008010a50002c3c0040341032200c41c00c05411000903644062442500c0c000110b0f200308417400d0840e0082d00203070314070504001044140c01c215405c61180c1c6400c81e141d580350200300c101c1090a0b406440810300000800c285240c8010703009030007113001c1c42c0c00d010208 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 762883534 1250 762882284 762882343
    0xb0f040b13030e0d02060f13050415060203030a09060b0a060806031006060807054602060601050403060e0705190f0e040f11040f0c050a0305061206040308040312090c08 74
    0x35001403103e40600e0706086030710150754441050f100f841c11040d49a6550b06846420580f88815030310030140191b04040200c08062b034080315034001c1d598070354015070541d511a40a00043c0408200a40300c613581c0c0d10307022034103450701c6001e48060035980d22200143e0410406062808900c002000c10091920100b8001c2591101c46183c0085140c40c059860700d003c000c0480d00c05000d10070b6142e81d1590b4140034045070b013a10350f0050900c0b0004154040381c000a820591300d5940441d19580095000c200510000740181d001d04040140442125002c40d03c0361702003800424082c08a80384108903032030401649900506030409001d0b0140820900d080a40e0340306403180c14603100a16006043c1601039250302c8079480164a50609031f014400c000088102410710392103c211440000d0802c4001401d606212122a051007051f100528003550b40780c0301101e1800c40900101d003003040c6110000024060b500840030290b0144124248091803d15a5460100007050400956400c80c40c05039040c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 762884784 1250 762883534 762883547
    0x24060d0b130507050a06080105040f110a1206150305010e0108120906030601020a051023040f0f17030109050a06060e010e0907021f0605041d0a021c0b0f040b1303 71
    0xd181050701101d60501c518055040c0042500803039000140c0c08000a425a0700c08607041c120740c025981004071680007488801510810002076029010400c603070310f40340d031003400000360407504d00600003145074032647d120b80c2190f00d481c0d040d80000e880d43c0041c00000f1805526500410243c0e001300403c0c0400d02d0010498003429840b144646008400181c1e264001c1c00820f501035801070688801c4c50042758100000c0c10040a4040c10001c0940350101e070922120b140e40c01560400c25a400000507940d443c004085d40d50005c4812044140f5039107966482c0781d01450103020703d02000b042c50302d0030801d04001c4131516804001003100310861403000da604408103000c20300c0c0940e01110640d461200580c9480011200342c02c40d2200c84820400e01074440d40103906450044406100c90a1280050044c0302549400d560550308045610001880c1c10000d400200043e032502102e0328800d80c40703140445138210b904000b00035072a800c100400601e0254258040c0010b00961140c1c489600c004080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 762886034 1250 762884784 762884791
    0x604050406020d1803030b0103200a090b0301150f05071e0507080d031b0e180601020c0a030602120f100b0706021b07180516050a030b0324060d0b 64
    0x1469445011409101d4550125481102000300500c01d4104014220041c0e820070a8103600180ca4404d85854561082c01400820b014009521000840d040041d09003980410800c0d42444032540340094140b803450081d5000701a00214a00007d0b110340029103040381815840301000750401c4200001980b4012154040000016003541014a03140c001e03c0c0540c19040120359100d451300e41550349525070800050917018010301c00300c40c0302e5a8000c1c3d5605042d01c007039581c0500e10000e52502c0c3e40540304203980c080d50520407240001510b80225298012940040c1c4040390002203203103140f071500d100306400c4804a02443c1c1c180c43c14400e0b5441c1c8a07201e0280d00d000c2080016098140002d940503203e044840c418000d200f0380d4028490b540e220300c58424201d104611201184809020b44100d41c4110040d41c01c034000503821200454081d03005104d0081807540e61400190741d61402c1001c00c9000503100580025202c105003615010580100781922400b1104a880700040c540111141c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 762887284 1250 762886034 762886039
    0x60212030c04150c06020f09030106080601060c0206030403090b0f03220c09110906040b03040c09090b2716170102070807030311070b0a020a12050906070e06070b0903030901180b06 79
    0x1460300c1050340840e0844c070303a0032018005600210340800ca040c101001005411401c9000b0001f00b59111b1140752203040910608011841d41d10b8840c015003480700045500910a00d041e4488076141c6400800d2034100031440941141d001c01004101503260b20400071910f0300c4e0b195280f40343e07510f603904140020940600340030306844180542c001e07907000c42130710320100000b460719480701c1e194241c04159400440c4c050380c550419250028000e00f5a204001c00b09801541014407544c41c8414200d034032590402040341000081c0e0b41803038442080c4090000030441d0ba042c11051381c54281c0091300c0140d000700c040c119074410894100055050341c1100e8800d80d05003000f144120443d4043c403242c0c00b400a000c1d200303410314003c03ca45050158000c00030041d030340c1c480a02d004207a01040007115805c6465074441e500c00d2020800b041e001309500100c6000090119103404216920f1440d4040150313100061030788080280060381c4000e01030701d030565408521000005915880e507250704074000e00241d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 762888534 1250 762887284 762887309
    0x1090c0612110c0c0301060f030314160204091103060c0901090e090102130f030606060908030723070611072c0402041b05120c1602090901150807060212030c04 70
    0x214103442604001c008070310314042da0762a01c1005516503201c07180191180e21075440d0120114500c24422102815250141d0320b241b0f010034002541070041e8050344000e0500402001c4001c010f9a90b80590103085d4425800b4914510020040c1441c1000182010000d84418410451141d0740441940c045880f40e50b401411520b42103d000d00921070b482c90200032409c0f07480e011600540700c03000300741128850b0b42d003081025035590b0100e494003958082c0c81c82e581c2082003a080850a0b034030781d070f114240240c40f00c2a01c1541d41c4004030315005041d401070002c43d101c041685811901400407000078131002021112003101165800107000e8000104090403410201007425500d50754070248441d41c40c0119044090580140582190001003112080315605000680c0b040104000c0d548105c080c2850b00301c240600c0d908201c19100c008000014565a5200c2c0801e0300e252095002c0007042005c028000fa5401c0c0320000b41043c10300c40b400b0103500400c0040c4003c03d540641154100c440c90a00c51 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 762889784 1250 762888534 762888557
    0x301052b050604050609070519030b1005130617010e031e07080304030816020d02030f0a032004150504080703020906010314090115170c090417040303020c1201090c06 73
    0x9003603024142002074801d100307803420442005000588140a01c4240c0102d0304c0b066600d50400001d08000308510850300c02c2c0200c02c100041c03141d40480d410030b4103030800040c11511140455804001061800103598070391600704501e05500440c40c048205250081c0811703a91000129507911820460410304518405005100590101030f500d105034071182c115628101400d00402456054601d0360800b158603407000c0e081c500001d10b103240c04041e500a107003440c0d0804101800c9400c410304503400d0540300d8040e860215180565070440b4156032600c9031300c8504000c800aa071007959a460320a00104100034003103ca40001c00004490341100d40c4801c0307950340f0004901400d0f03d80402c011089180040c40180760301900602e411100e10b66824010f25a00d480845400084042382c11854102488241c194107046114540c070074029054070048991142010016074811381c030030340041c0c10210b107131003481c501040d141e49644a900001e1000884a4a48a0407841d81c1e110702400e014a01c40603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 762891034 1250 762889784 762889849
    0x80d2403081308160e09030a020d0f020f010f05070e06030c03040210031103040b18240a06030f030c021c05060f04020a08121b010e0706032f1206010302030105 70
    0xb5400b4040d24403d4640319884100a2031030715441e406a4001c1c2c100a40020700a8607000060b122002c02c00c0d03008003604164560140c641c290f03007882c0786046029008000000d00b50034020542445440b850005080c40d049000500700010401c1091017844100140301521a2941c15641c00540443d810b00381081042c8007a0001c2000b100400034184001c000c00c001e104000040520030101001159200c0310f00b0820075443e00c0949444840c640c005414240c504840c41c0d03007956010003002c20011707d20380c89480e241c080c0c6240c61011000034040e000305204500380081c0c1894901001060a0401071050b680c803922201c0040500f6540824400003c041d507840c1005c2100406001091310284030030324070403500701c0d41328820700c05044001303601a50040e94148242500400001c004e402c4c01c60401c101100940705000c840c07d1100e154080d600604001c0480740d07906110551601583d60b250149035800950b0014189414036205000402c81c64a41c603540c1e164008444a071400c504201c40f12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 762892284 1250 762891034 762891067
    0x4120b151c020306160504061809110c010c09030f0b0717090318060a0e0130060602010c0c03020607111c0c0b010807180c021009080d240308 62
    0x940c01d9108a26540c0071030031503252110358103924026000d035040e030394951844045904002ca03201000402c2004100807840c4103980080500594040107850039940f0307000c0809407240d81c0044005400000390342c1c01024000d200c3c10074169021704000364010301e10f0700c4e02c2c6901c222029018249031080f200160803039100303d2208100010300c04490034a030602006040d907a4102018408403180641181e10710703850003c1c15070f0800d410725500c04480d901032070011195421074607007552009420a021019403a81d542001c0c1075421400c030700081491412000030300356461900d500041c842c500304c5003400b180e4046202c95011101d818841001c0e02c6c1c01008130319000d00090f010f108889030111110406078810b14240105000c1c41420b007050340c8886c1840d44484440c8180709841202007210352a0003038540084198000a0050310f038000f918007410740c160ba0b003241c0210f4a80200048280100d1100e101e914143c03208a5900120325460242008421500d80400b5002500100303804417209444074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 762893534 1250 762892284 762892321
    0x61806030e0f2b08090715170f150405090706081003051009020406051909090204020c0610060801060f08150a0b041205011b0c02210307030c0b0601020304120b 70
    0x80b10032588004842c0c1d2888621089400351480c2c0c3c034110001c040d4130890b1440d01595580c4003829000d80750a0394484010083c481001c28401e074901900380c004c00403107215100720150442d40300c0c107150409444091801c1c010f00340d403181c2d10341014409a03010004007031042e00c02504000010b0744500039043d095144941c030003003192040d094018149451504843c40c0c0c113200b6682886010340703070310400c90f40c81c110b005654941d41c103003241000040c525070841c40309140058030041c5020300e481e034802c0c2000002c40303011400683c207040030030845502c85d50302c41c0117181e10710300b1a0b00820481e000030000d6201030240007280d00d0030b4281484030790720341080c0d1008041e140c050036039443d500c52981c2c0365944605015100d075403034603440f1090803a448500100b0402581d40d240342403403055003004611048230402c410303801e10140410081c1d0004000419802e40a91641509400c1900d410110450010705040c115007050008000c180d0040c4c005080080d4010700d8a004c9d03540f00c0d0a052001c0c030540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 762894784 1250 762893534 762893563
    0xa0e06190302130504140a09061e05090d0f022e140702160b12100305060c0d1b0504060f0210051302030105060102060601140f0409020304110a061806030e 68
    0x2444000c405034040c0c1c010000310440600414241d50b4500401048861025080c010b100000000510501c400d501108072588540000940c200d004403a00a500040000d400a400d40e04c0b010301c0602ca004000000c120100340c6441000503d41301c07030080d140c1074820003011849080c03014201941c4d0b00104071070030304518403034200112250811000b60710102500d0440142c05298440c080d80301c2211880d00940b0307202d0350f80c03e141c4030803140c02e01d15120340180007440d40c416203070011001510502c00301c0e01a81500d01803d44401881a992084a8080c6408402c1b001c0004003000040e8110054800320780940c00c7c400b06481020005904000301d52110b001c0d01c03440c1c42e08024042c0544034110031360b14000e41c0200150f54811005903540d542c2038424902042c0007031000480400040d0003415074482200000d03040680d6a120350040e40c0003507034119540c0c9142c02100229090810307a07a0010407007883c1041c039841e06418040d035034080300c4c01402c04240d168480071000e501c04020441041c8440b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 762896034 1250 762894784 762894817
    0x5090c0a14040b1507030207151e0e01020c1f0e0901121b0909051005181b0102070801110904050f0c07020904020a2607080703020a05040c0c0804030c0303020c0907050a0e06 76
    0x10b1400075160861801425008120001d9001027244541002c000b4184e41000d40c4504042c07840064641c03503a103080d07003811486880940f80158989030110b03482c08007014a40106182d600c400079107460b121420041c0100b0220b8010040c6203030070994212050703002103030000412501c800b0104024420303000381d60300c02d0410000710204500013030034403422842180e081040b500c40c6110344581c0c2040c141c840203079038410b0400c4d200b40140801c1500000f00140110341e48030f0707503c14105080d18249600f811108101103914840c9007014091903500030394203004822a480c003c03112803094060408045e0280404d20000740464441c00c082c540548640000301c0529505c0c0350b030940e00c4181c0e101c4a08110b00480400080b401d000060401c03d03264000c094545c510309160501000384031071203200c003c0128540c82d210200b412400180059401201d4510f42c40f811070801900c1c050701c0e009494050881c40c010006070a500206803224682e8031b10307284222001ea00c00068641c014000c80003041c160 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 762897284 1250 762896034 762896047
    0x120601030902061303060c0c240e0d0503150d05100b030106090e01050a0f11070f05010b060304120f0521060109031b0f1703310905090c0a14040b15 65
    0x44c50000d2100700d03885031005002d280c4002c0000c940340608600014007501c0001c002400c44030107031b845150012500b80c00010303a1010303407515a2400004894603070210300300000780f25507681c0d102800c1c0081d060907182e8604090340ca0703403516900d1080b20b007098a4130f59a0304591505603801c1d0007032802031607003100a22001003810307180d070300900c0c05a41a150302c1d8034010300c0154015441c0a69003603601809601400d05040b9140e40c92160040701e0102c40c1ca550b2210701e0100c5075298000b441c0154000e280c9130781c0c0b6095054001c0c2103846810400070500401740042227284464000c2c0070710070700d24a04188a181c40349001030b241c401454000070680350908140b0f0713030369000303980c2c0d0001201c07202011105086e41d9610440030403440c15114000c9070700700300b080b001c0c1c42e050040485903512910041c015071051031084000c1c8003000e42c00c458031241d1103070140440050100480e0385207110440d66003410618000350110b541ca00400da01f4003e035254000c00080c2d42da400030282010308108140c07956502f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 762898534 1250 762897284 762897307
    0xf0a11010603031d0405090c060a1205040b0f010b092b0c03080d0c031a060c2e06211217090705030f030705030d09150c090f150512060103090206 64
    0x113000d0001c0070550071041101841d07203018020b15001e00c0021024200d035070300c0401400001e51065140074244440d03103c00301c050050320300c9820310550180c400f10b41740b03080600040c0500c0340180d016855404082c8801e002694407000d8110080d000604842c540400d0184078401e20304d480c05014080098000e00003080c07000c582d0086c00302c01d210326810400394042250a0f401c840b180b1043c6002201038440095040c2892001030141f07451520480380324804035901102c030f640c030b59901d028440d680c1103100818140c0780e00460000e0400d140858001070603851544115407000307240903081d9030618500e40701ca46d000b42d1140c120350100700000b541e00d05d004c4141d136070b0b47c028038425a03000c1e104241900b0b84201010041d03588140e4050081c40c0b900e500501c2d010042c01d905201914101100d80419400e18001d2007580815101a106c4002003072802480061080050b4000c0714403d800d9601c1d1019954803404883c0723070703d1044103100301c01d03100d0070f004a00520424800a41060b4000388070f03541c45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 762899784 1250 762898534 762898547
    0xb0313060c0c0302070902180d0203012910110c21070803040305070e04020112110f0d0507080702300403020d0b0f060402072f04050115110f030f0a1101060303 70
    0x10b600a40031a0846969020690103d20804000c4803844001581d452000d00e00304500b1140d00d030009001240c51070b200d140e040c204480d81c09946000b06242d001009150514002d05da04440f03160804c4000c08490b100c0d0242c880103c0808070384501e0a0000b4075841c0801640b03040e0f0940062012100307401e480b0b80b0340c6580c83d40940401d807094803881d000025400301c0f26403010300c03a0b681a562105091001e6500300c018050000c0000304d01d0f0020302050004241d004060900f00903100c86c049542c0c2054000901001c070301170056401c6410411074018502000b0342d031400005407946070f4894540428091021070f0083d07400c0254041c8641d01c000c400d02180a9040740198040c0300942010344602c400c220891287c0540145500c600342241008101c050002810702c006405c800045544600c002904540d000d07003103c994801c511415241d81e0f5844010122240711400003043c00b1801140a15940d0058066008180400085008100f071140e81054810320140f0000d0002d41d44914010703068 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 762901034 1250 762899784 762899807
    0x60f1e0909050a02030108031b01110f03340c0302070e070206100803070f0b06041e1e0b06090f0604170c010311120109020f0f040e042a0b0313060c 65
    0x4a50a107004203d501080e842201d04071480100154a000411100360300703207000c44814600995610281010700c0e100000c01000c07070490307413498107640c0e06d094621100c00049140f607102c01030031044604245101c0c211110400900c1c2c60804a90382480e0780ba0883c542040c9030001004c100383c410511500036000100c3c2c0f801112510075981c1440d8540e254076641e406403040261a00034015040408130312500030158103c000030780040b41c146141055107400c99018140704002c155221070445d001440684000055543c030842032107040302e1000082c005000f000d1007244100c0c03202c90500c1c2180d84833800c4800800b184107000d0200c03650050091789800714440354030301090130074020160704d0b681082105d0300c15110640381e41d02c1d44d0a007001c0c00000e4110803458101a0300400c00d02c5002c4042c03030040c00041100080320081841e1030b1421031081c2ca03502004500c0031460110301c10044c01d410303605100f46c0310004080c035102d0f5940c030910301805a0306034001d00020301d00315400c11281e5100d0f0900c0700c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 762902284 1250 762901034 762901049
    0x1918020304140a030206070503071202180a050121020901020a05060a0f0b090402180c09062d030112140109060203070e01020d0f0e0f1305070c030905030604020a060f1e09 75
    0x14608104880c076203d08140d04000d0060b0001c0c0d0029407058000d40242d6049203162800d4040d41581608010803a80b151111560310380e0810224070203494502c03140800781c8020b01c2d040009042d1401000e000c0340140e0040b4001e80d0b0045141102c1e42d208003c03c80c00c13103802c10121045400c0c030740c50000060010f40c40c980721540c102242d02210b41402010b8902880c0d020385031032104210101001c2c07800f80b02400c28a010001045020f074240e4804000c0c10940005900c103084150704000b00e442e4040e1046028079000e00140300412400c80141ea11542485d0800b03003088141c1190100d5a0050001007030040526101006118100c0d83c0001e140c2d014503400c0e0201c0303001c161030300425500c841800c0312001c00513500d41c040354460b0405c4684003c0c00107024208002c00e4500c00e89000613240300701ea03c9000900c1c1e03020280e00345980403060100810058002d804e80c1d040c5031b0082800002540202e1040c06846040005003510401d07840420f00c107540b9a03540c1d40308001c40002c100080341d200b03001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 762903534 1250 762902284 762902303
    0x21009030b070e010f08060301140c0a09080105071b030201061211010305090f0601140f03031b060a11030c1c060303020c030123011a1306020102071505040f021918020304 75
    0x1000c0a003d52015070b92200c050315105100c42d2030780e40440b03100c44010010750701552035212441c41d00440c0d040180c05072002e840c8080d200c05803203400a000030200d030f010740c0c00e0b60304001c1400420f81e00318502400b4a01c4030f00b1050705003c3c5030308003031f409409290721200d21a1300650008052000000702000031003804d0341d05100035110a0300203079607903414040c2a14079800440c0100000800309035003a140340005001001709418101c00a0300b55001014040b0044084003600c0030450014821340303500a100c6002004210800c1c180c400007808020b040200301400001c00086601841c00e0003051310700c0d8072606002c2d1589911b00252208102c4580368069800d02c220b006000c2112810002c849181d4400e42405a203007800e056000c0044140c85031044034208050320f4842482e00020010300829000946d89901514082030b00008001002440d146080107120000da2040308001045404488220040300701d2a020160b01200390b0105c1e44004500f001d0541e1404950003443c480c0340900d40a5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 762904784 1250 762903534 762903541
    0x30a030b041a130e0a0803190b030304061e030608190b01090b031f0b090907030b070c08090f040b040c03091103030306031c0915050c0d05040b1c09021009030b 70
    0x591019078414a4aa103d00c41031118184400141d0000c503242c10300c00100d41549020343c80d807601c294000c5c1c43c0e0f1207505440c0c00b1010356410803030044031054201030f80150303d8245031610060040c990002d042441600a010340740c080c0e0301c240c00802c060218082504d40803100461100d010b50030030340080b107820b04080000960318807a0700c600c0d010280003801409020355060400c40c50311940000316035885560f0f02c901b00c0d41e6200e00c10350300d2048000303d00600d203007800d40c1400588242300500800130820700c4620b1400041514050340c141d80c80940380405000007040000c1d01415090520301c2c2c0045c40c11107900c51503075064002e6565213000d024010404a844d905054481c88101d440d290545d100440251000b1850b80d541030903001145000e0a0a030740b100c000c0840c0d041420702300800540302281c641c200d240140702400c0000101d00784103141c02c2ca030800506540c083c242400c81442800742e400040441580c00c000c0f40d40c0e038018111104101c0340c050150540c10640006c3c2c61030705080707000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 762906034 1250 762904784 762904811
    0x906070f02030d0b041d06070e102a12090608090f190c090f090b070e0a17010e0f0d1706030316050c0a08010209030f0111030606030c0c030a030b04 65
    0x10000640c600d079000c0d500d0140350b040c014000c0c06034030340107980041d034401c0d00317480304e45101050320341514251003d46420304003000300030216408041158421500d113410780ea54160030503d0200d0202200030301c401c2c902d04003602d1070011880c10101400104c7d160884403085980100002c0c140c1d501500e55280e04e4903041083c03561546051180c520a0740860a442c0c002c0e00200c2403c14004c3c400c1c00324038980c03078a4040d000e058070801040f103600c043d102e422140030002c00300d5840e68040301924101e1140c01040e8000b4a40007010720034158000f00313086410072980402c0d00b00c41c0884504804450b000c41d521540145d4030348040e010100042e48040000c0c2e1303100c04d1000800d0089030000c0040d4203200b0396402010062215280440d001d101c0d9690101300754031880c01e40701c0105000c00c0016150b514200c20b00d03043c121100c07850a07417039161855000d6401c0159042d80e0300710700183c0700f170350701c3c1d9680c03401800c020310445502c0202c51002041c190382199041d00940c49030803060300c0038040040324059 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 762907284 1250 762906034 762906047
    0x414040302070521060114060f04030302160b03090604080d02092e11031e0405040e0d18120f05210717090f010c020433060215070c020f090c03090607 66
    0x1a8601d04e5000003004101e4a01020803042c1c4000005102501c0c184c414582a5480d900641c01100503802c9400c003441284540c64260004062aa2210b455468244541625044002c0c4020910100880e90404402c4a5410740302071140c0900f035016440340c0529100341440d0180c4511144060480d01d00c820355100e0284040c034020050001e5081641d00b2002002c107a00d120080c01c072019007480002505c0d980d80c020610750f065440080c0420707000d40080185403e02503140e00c21a40c0000c2d034104001c21b0202c41100d603007a00300812042d508014542541000400ca540f40071108000c02200d00d42c4403403800810b48581300d9943c40c0002c00c2052907601c0b071401880da05561203104200f0740203555010760318900c019840240000f4443c44010501d840319454415500700111b0a01d100500304068100703c032001d012103000803c0400750141c424402d0040051140c2c0420490710f0109046443d41d240d1000d1598009062040031721308041e9082c402c0d001107500c8400c600c111808584480c0c0a0036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 762908534 1250 762907284 762907339
    0x5010611071512020a05030901060b040b2d0304031d040b090412180b07140c090606070f0b0a02030703140f0117100e0106050a0e011d040204140403020705 68
    0x202070700201c0d14018901100680802ca94018001c0c030300102c00f0041c1d5940f0041c14846483d444194990070045819821581c0c1a0003080207071900b0441030040107040300a68800300610b009655a2442030348515000d0740d0805086084c03050080140000c05810103950300ca8103041e003071104800308403d41084103a6078124a40c540100c6c10201150101c0c80c40e9510048168560501040240c0c0b040b1032180b0115403540321190006000c110001001403d48140d9103070364695000b0700040e004030000139200e01e806070140340700c4c1c940024a1000c12101c5000c1745000380c0c201441c1040d82c0303050030594001c1d40c0203d030362034006860003042c900984003901046025034200003040c100c6a00301804014201c900d484c819a80e4850340f50159020041809060758030759000001250b401e1508090083c805c400e0340040d00414480710050095440500e600d044a82c00c864031030f2101e8480f80081740c024000c484028030304552034410401030540004141088076002e4a6030b81d94881c0c558003110f522840721 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 762909784 1250 762908534 762908567
    0x150312050c2506140c1b0f01090b120402130203010b0405310b0321040608071e0f0509030d21090807020f0315010906081603080912071206090501050106 67
    0x44000f48403c5200d40c011100c0741c09521403a1340b038165019680ea103445400c28684031a080c0240303002c129402c04658084001d0707020f091050710141403242c40c130a6400b0f0301c032200304401080740019095545821240e001d042c1090b80866803035071100e104540b543d12500400d80620650008000f40d61000c51005c0352503601c0088101100150145440140000c03012040e41842084641c220b0004980302900142c40e100e5041541c80b8589080900040c0d0010280d03030501580048020401002c1004281c00104a1402174443c100101c0f06075a02e0080180c070b6501407180c40108921541c00892501880010300460304840c2034144110040d507500d840c004005150034449400181015a42c07a00d400c1030040643c0c0c4402c0c64000d02c10301c20ac500741d02410100307031a0842001004000d00c42e0388202400e400c1d104940c54216240c842c05071003588006401000003401041d420720b0107100c540d0103400d0705804840c445aa500340360001c1d296051040c2c45c03552134030000181d6107018007188c0c001070940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 762911034 1250 762909784 762909853
    0xd08090d0c081912080c13090f0b0906010c030c0203030f030f060f0f0a031b08030f0307030506150f0307030609021b01050903030105220209060d1d0d05030a150312050c 74
    0xc030013080703070704100c003400d002d428079400d000e2034207600c03074692100c40a4283c1c01400210210441519000d450318060309a000b203003040184201c17668011000750f4150703010f04102c0140d0501d480032a15610558450b201c9440010043c084402c0f030201e510350048604440095565400704100b00440c0444c0914a90000b00158100700141c01441c10400c111000890901510b40d607110300c9017103600410301c100031960700008220fa000c1e0148a501c0d004401507482e42441d4400382a0b41009118030388900e200300d40c001c80050040d510130f420040150200d18415034071050310540c044003200f031000030aa819420407000440007031000099904a80c8014801e0702040c5c0184040b10808034071096110301741d5020841800151a07010003405550722510000071000c1c0d05aaa500c0c91850091003002c86800c80c0c040345001075800000c2daa007026400c1d41c0094400c20348840c0410f0b039045540010000444084804c600c02c0d00400030b00525081e04095603908410030b900008100e5111038a004940301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 762912284 1250 762911034 762911063
    0x30501140f01090503030a03090b10030302060415090c0806071d10030c0c05010501060c060c0305151207051801140d0818010311031014010e01020304050d08090d0c0819 74
    0xa0140004074901c0341814440505600e03007000c2401c6601c020f034190086919603191b0000c0050347d03041c2c04d070301001f51601d011030a425070340d0007921003901800107802e481000000203402c1a041d0700c000b82e141e501000c9140d0300d0ba510a481910703110201c46000114150140404054100d40000c4220910040241104201801e410740052107c80c2448040102081603040000d03424420b03180a49960f40b1a170b0f8100500d4079194003510010421101007604101c28031045148860f9030310301d0780c4811943d2400101484001c185044941c0d440075901014610700100c2111900700f8041c16a04200b40701c903090101c00d002e01000d8000c807038004003964000c000051840281d140c0250100005150104115400300e406c10010b40080d078030800310480c0c0340c1b000c1003101498540903030700340401e08000c4544e11050300080c1d1207000b2489258042c4405171004010445003034210b0701c228800422204203c0c00500380840d0a1401e4041c080300e51180a90b800ca100800c2d11400116070751010300d920742000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 762913534 1250 762912284 762912289
    0x120309010905062a010906111206010e030c030a0b0f1003030503011a0f210603070b0909190507090608011a07060e01090c140913050a03110c0a0f1503050114 69
    0xa121030848804d4446910324000615000aa503619200381d000000c00e43d281e82e8140718086840c08814600c03004020041d8402c0341204c04070341c944c440c00900f001c802d00445000071a0034038800303403290750b4140101003480c020440c0880c1100e0103002d5038208501141d840341420603038200c83c0c2c080a0003058040c4010000c00b11140d400c02407440c203002c6e0341030a0042101c000740d195044946c00c1e410380300742c080070f800c90b05242e02c040551040040300105000c3d45481080c0c00e40c0c2c411218054041c06810000401a8000404c260b031100300b148000c220302d1800e90703c0104520a6070081000141c20500001070b91a040300754030044a400d4400c417403602e107a66480320020551050703000f2044d52280c0c01d28001c1080320290400401440070980f00b031400344401c002800302c00900645190b10030000300700c045400042c1381d8401e1076050034015200c0c3e2002c014245440f4462541c80e9210460a2002c82d40d45580207821003280c0581c1c04e640c0c1e038480040710940907944240100e08a41040c080c540e1444d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 762914784 1250 762913534 762913537
    0x90408030f040c0e10030209100f0b0d06080601090b102d0c0203060412140f1603021009061b0c050d03050c040e04050303060306010b070b07141c060512030901090506 73
    0x24440d042180649564150041e40300c003089900624a10503007170100150b0030b100c0c1507a5886154142e40c2c07512241460035000b0000c00c00d0050016940c4040360703404070402140e003c0c0c0041e045000440c0d007550794405000000d08a44404e85006400714030303000fa19640900c180829101032624580b000903260103c100c1480c0c1c11088103000c1024100c5c0c20f0026840c18002a401f66009501820000000c140080c040507014034042003c0c041c10850310040302503010030b541107040c180500400c05c01e96800d040b4507042c5080c07003078510103182c40c089000300f0555500c442d140702100d14250000440c211003d442c06000c440700030f003281c0c1041d40b10510701d6210b0fa2245601c2014aa00c8909054691803600244482250211640c1d8400024841685010001d0600500e4882109031900b00c00b9601d000804401502c000300340405400c46d060440300c503000340e82c5807034003c1c0050010313540000e40003c0905185d1141038042d00c2d2074000045500d4011084402800e4181c48481c211850082880801d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 762916034 1250 762914784 762914791
    0x30f0305070f060507030f05150307030f03030b06040b09010e0621191113150210020d27122303040501020c0f06011508240414010b1305090408030f 65
    0x4141c14468800000d0300c3c500c9494090001c5035070001e06c05100021071030441e28050940d40d04030002c001203207503e503000104502500d604c07010383c040a00c2d00b85021b90240c561b100400703622000100b0b010403000e2654000d0000054260303640c2c00c8200221b0188409031181204508501485010300300088206d12082c90b00002c0382d85c0c072041c6032200c4030100000c6952010914003510000034040306403d48070044440580891070300270f210728907643c4010f55100c030701d40d02001c2c0b000d802042c01d0803c6c603079550101d114110380d0300a09081c1c81c035001090140c22002802155541045400c403550340c1e100303005103104100c4400003800070700c3e40c030560a03a190f00024011a440d43d001c02c10900d108000780700340002d00107044d00911580d41000380010001202281250800c6810b00801080d2034980000404042c201d480000c001d003021000308001d8060980d0141e003d1f04440000281d80590f13200400301c0b1a0703d89a03982445403500d08200010509403006404c0301020300c0410304088004011940 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 762917284 1250 762916034 762916043
    0xf0a0812070f080601230307200c10110a17041805154e0a0203060403140904090308092103060f1c0602030114090601170603030c0601170d0801030f030507 68
    0x6c00b00d0703c000d900404c2c2c0c0d00031184800082d00e00a81880890003806603201014882c0014100c1c1c22105004180b60711105070020041296031030484291302401c1c008035480c40e411100b03660042500380c442c440f580c1d11911440c2a0341007040110660400980300d45406802c5040030003c001100ca001c201c02c0030640301c90666034450440b1404941c9a01c440180f540403500340c03800c8000f00100001c610f200e0b40200480b0065048850840300696021a500341d000f41e250404121400404242c0365a40c000c1141c1070b500301d46000252414150401030070742c480d143c01c01c00c5519005100c2119501e070003003031041d2509014140040b130500d18241c11100000007010f410f0203064808103481e01d0511801035000e44035603900100600019101809252010078140d540501905007503000a08044180c000c545c0301c400c1e480d01040540d542170046603107442d41070341100d0f1503503103440300c0880a94029048880e248079500d00b0514841c0030b012018100ca810a07200160300d89281ca05032540d5008540c201e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 762918534 1250 762917284 762917327
    0x609011d1f180606090815060405100305010203070804050f1204030b131502092103030a0b040e0d020f0606030a03200109061103060a08010b060a0509030f0a0812070f080601 76
    0x115050410402c100b040e8510401254144c50128083c05412a9070030485030781d0403c1911100301d142d80c02803036400803410b40d070000781541d48044000c0d980d00181c0004000354000000d100f01160b0100b80716000e5805201a01d880300110003105948404185244802140070300007040455202c1004a0b440f403074a0744080f01c3c00d0100e83c3c401c080743c250102509002139000c1190811428001030420100e040c0f140480c03540e9a030b40c502c02d550f0380401000e40d03411640f5036152030364540300c070340041034141c220303504544030300065001c040d403699010f03a0450a24460303440000ca503407800050b1503130301c0c81c1c040e01d94440c04035580648c25545c00e05940302140d50b64841c0000790000710b0600c24a1303442c2c800e00e6001030f200d0410314104900810968410801d580c18481d0101032a520103003154071030040c03420501d0b40d6000c2c1c9004070341051542d4440d084140120fa07003c0307050245400040c075001081203060070482d0380e000030583d0754801112045000a0614000034841c0d4000c0212120381580d003030b03829 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 762919784 1250 762918534 762918539
    0xc030809011803050c010b04061202090a110f04051f0903020d1a0f0f06030d09051e0a0303050307020d0203130611151f08010b03030703031e060308030609011d1f 71
    0x10b401000620102e0000f20000307510080b1032400c1c4907034503482504603418084c80d881c100004d020600382030006442612403402180c44000150300a6404030158041c264860754104060702031504503105560140c1c24216422019007800300c00d060407503001d83c440301c2086096400380000e115004074100d039040e1880800344070010f4404181846241c807000c0b02645841c0140d480c2000c004064107103406030303001c10146001150010407e00070f0320800da40d03802d0884000e00c007052010503000f100d142c008410035800700c24503612800648c0300300142d400300c9030404141032080381d40348034143c185a854500d42000303110151051103108000c0002e901111440701c001c145408802c5000e035820421384074a4003820209400008a01c40240404002001490058030100b5103d10031080014101680d501c0d100c5001092800340740c001950444040181d1034491030041e1055000b42c41c0d02e8401c80324400005400180c610b107480040040c0200400d03aa01c2c1e400801c405058600c448145188850001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 762921034 1250 762919784 762919811
    0x9010b0403140f030309060103060c05031003060b040207140105010e0f0c09090a1b08070f0203041a0306031903020102120c0c0309221a10020114010b2212140d0c03080901 75
    0x186006d8903c038070150449500d0361910000b20760607803070140705110b42841007200c02e140d800840c00450360014004503041c14a080094000c5c8030b4140014121320000511080b00801544031780c2c1621010320200078103460784160310b146100f080742e0041d507660081041007458100000c9154100d00c140101113031020400414841841c0c0c1c114201c000265250304020145d903220a80c2080c0c0000d07400514903103418106481804821052000c20308040000812001d890030000ca008200786000c004540710320600c0d009010b50b102c0710582c84985102d40126803021092340403a401084404000d5140240241c00d0001100480301d000c1c201e084050201178041c46140103010444100900444a0440b036804004174101c140243c80d045a00d80140040e41481c00018141540c0010016980b41e5126010b584586804e20001030400c003028900020760440d15040c01e0031319880f42c000307401d80d620001e140b50340d42c0d0200d00d05540003c40303811038040070a000d41d81c00c40c4c01400c10ba0003c2482000041c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 762922284 1250 762921034 762921037
    0xd0204030b0a0906060b031501200708030406020706020d0503010618080f010c120b09190603050102040b09120d05030703091106070f050f0114040b07030f0908041409010b0403140f03 80
    0x10b80060356601d071000841000450320400b030103446d003002d10a0441c140340a40d41d03021900981854107024100000024100d680030002c0074065000013100c43c0c05031107822031030701c9030005d00c41d100c003501c00c0d40c40c04640540045074508407450f003a90740f03504503842c02c40704850510703c1031a0340c0f82030900850040f0b4142c40500014501c14030f40400420038054140c001440b4500072182c0050700e1345840f4950342d203a45d9095a50344c10000c7c15841c0c405032465014008002d0026134002403043d840002c0000d08101e2080c0601201c00c4100e44c0600f80c07150a220183e01c1c0c1da070300780505000031000c00000309417074000d5000d42423490062080318180058540030031aa0f0348031100c140d51084d0703c0407a03a030070400100500c911440c140780003841003258807c9610380070003000d4001456000070300300003100c85110358031500208040003411311548100e4103040e009540310740605c0400380494071a210041c20040c0c03c860496440c640c1144ca4145581c4a403030b00e03107452101c00c0d00349000c2c010381d084000c0d20810 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 762923534 1250 762922284 762922291
    0x10906211d0d0207050a06090305070b091305010e15060c0c04110c0307060209040e0a03021f0e01180c1e140a0510180e040209182d0607020619020d0204030b 69
    0x80044c42054241410421015200d40c403200401440d51410b00004c0e03000702d9820b0440b42440c4000d6156402c0c180020210469000390f10000703850480002101070b80c211003903004001d40742c11400038200d044107020075880707060001240381e401140000b05508040d880300c1c07030b04031100508608110f01d0500d42421030b44400d40603100c840d00465403403003a01c0e052207001003503003007080100070311102950040c0d1549050501c2400252070046c05d80d0344408190005403115006e500204500c401c0301521002803488000305848038000700d00e02040401c0c5008866042c0c05c0c0d000c1461130034611348558802e15003005081c0c640c210401c407200190f0380d10f8454011060302c800c1d0301e81044002e26a401d4240c82c0780268460892040c04405010141e22541c0101e44c04c12600c2c078040c80f19005012901d0714115551004407203040c03c400746203101810481e481900a006a029200c031501e0307250302281c1c3c0d0b807015910942d4480c0c04040031a40c07462980d00505150202c0107000d42002d980e516041c45501046 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 762924784 1250 762923534 762923537
    0x7050303120906160c0b0403121107050c0604120b04021302030117010b040207081b07180b13150501050c0f0604060204060305060316050628020c010906211d0d 70
    0x2a007030012461003880002d6126000100103c601e91448100402d280342200000e0014010360004c5008d061003100b110302403a6240d0030a0010004500400881e03034001c0c0400e44160090100100c81031502d50101d40032642c0ca010702c0b00c14580183c980b5140501e000c2d1080303078005031140100d219001c083c00554000c181d440d403000300c600340103c2c0180c03c2d075400249041c8110700c100041d078001030940d801d0324a06104074440c01d1540c030030180382614084003038200d12031050744001e072070030358415641040c10301603006d5904100030b291001b00a0203540c0d10700c40c2240f00508006091000703501c00d03009420844010030441d03280c1070983c50f4890a058042c0c07006c1d0380c503a0300020244a06070300740c00f509820490035001000d1001c400300d043ca0100341c05006803446108009440c01d00d920b0806001d4101860340d03100c9545100025134061b5132501210401d40c0401c02180d40000d810740500e00c50100c407200d020442010000b5232410400034000c0c100316190b044145100700302a60380030041c031049007005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 762926034 1250 762924784 762924817
    0x624110a0f02150a080a020a0507020409110f06120103060b03031b0a0c0b0309100e010e1b0a0f0b030402310c090906081f110d200906090108060307050303 68
    0x180d0040c4003c2c0704201e100024000340130880843e480c0d52220070070354000081080140c50740d188080440c0c00d4030541030041c0d806820003813070009200d0151983c0205640407901d460800c090b0703409010b1a409105000d640140e11040108003041868201c0c209002e002415a4030b001060601070200660240300d8105079845501e103131040184074080ca5000d401c041110a04502e48640c504c2d07503d400d94145403005540715001400004425040000110410380c00d4410902c0311626415200d10180a420301c80c1d0030701d00001a416140300101d00075240103240040c61592a5028010b880442000b48664400c41c10a59026651040d0b221451410f104101040c42d10300403000918000103038221042c894900350041110490000f000c404504642015030f003810800c44d0303a24000c1244880b02c80c454440020b5030550000305a000307d0621004c400d82030140e00051100d150980a00011160000d500f00002c004070341c0109c0c40d603503110800904650394552518007281c119080350980e80c070f001b9003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 762927284 1250 762926034 762926063
    0x411190c0b070504050d1113110c1603030c0809060d05040f0c0e16230a0906030e060c0f091201020d0b01031d1507030603020a0b030105130624110a 65
    0x481c0489900015540ba000e030030581000300241c48078083c0100240a40c41204241040f41c039a41601580964180400c1000380c0c082e950901c9070b9481801c14502c18040c0e42070828241c0080b942e1541680c1e056a80e03038218141555907451a98086546545d02240501c0494480d40c214000c0908c103d1245050700c0486a06250810304843c0f240c100088a03c0604c04018542d62007076949040302409241000480c1d4110141c005010210340120b5401e21001507100c0c031154000c04d8060461740d403581e0800000e02c80d03048160b1501c50644001e214803001300b003481e03500c400d14000b61000ca07a008103506044ca115034941400ca9020140501007280c40380c7c0d000c0903a6815204149000210621a6400801c228161a100c10020b401c040e4220001e80100707003528805e500c9640510b0703001d024100240c1d201c0c41189801e8009103d401c0c418003114030468108059406003608403034000c1120f51040da01c2030180e2007124801c0d0405010000c0c10300c5409941c2004200100c000c0d809240044403900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 762928534 1250 762927284 762927293
    0x301061214090c1e0a03030e0a081b04020901030f050a05150a0806060d1a0702010203180a0c03060b271e0705092101050406060612060302030c0411190c 67
    0x2001842585080807400c410015145004210403240032001c0b00c2c0078000945244402c00d94861201c10503802200f0448044100f54102c0140306109004444c00c542d820390310b845e0f8560354800e400f003110300b0009055034065141480c1d00036005a075014180412840c55801c081d00032200d0032113480407121341307503001d2140c0c15150000c0c0c0006500d040d207004038510f040c030f804d045c0d0b60356002c0c12440c001c007500c1e82c1c01c4040c0518400c20252842c2c885d8110405820400030080c040d4205545d0045440c650040422040e200041c03502c440c01d40c0f2800c0038000625545400c00100076803040c45030402c52542d090705844021618095000c90b0f801d800c69554281290302c2141001002c07000e44400d4030f01010300a02540002c1620704010b8125031505145c2e03020041e50070f928500c0c1480e1101c030340c00c0c2018802040200c2d0400b60985840740d0b240384060140c00604016512030344400b94258021400501003070038160450a00c201007003c0061a0240300c0c1b21081070300c802d00781384a0000b100c4469103030410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 762929784 1250 762928534 762928541
    0x70f050607210b0a0b160b01032916080426070b06010f05160f060507020618061006180314210310091e0515030705091b0a021203010612 60
    0x4400710200011010f0102084080545005450181c81c000c40d11088036030000700c00000840c5c0c05450048156501e20b8103d144a5003143d070802040d403114405840360f0646086680702d4210b451141c101c500001c8400d60ba241400341040c0c0c1c0307203d101c11102e1b0880940d05594841b074241c0d213940e11f55a80b40703400c2071480f224000e440300e810402e92000c070a0605600806aa00342c40e04c1c0c0440b595000850b01d810801e1103051712009046a003020200000c154010550620800d03100d10064a80c20760a03145907140c0f075040b0381540791022101e005111a510800404a00150f0301200c0b80c00b5640300c2e120707020258a510611442071b40400c0107403001b07204011408500d14a0644c0c59030031810000082a40706005004150203995105101e01600074074810b8000c2102815000f080790703003440b0900c2c4101c09078080b440c5000b80306020b8000740e241001f00d00c0d1840380100384911070441015141c0c035501a4081d41482c1c007140309071803246604812132402140281029141d04014202072104035069 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 762931034 1250 762929784 762929837
    0x4050c100f02010e2e060329090a02010f180b070c030327050607051510082e0504020d060e01050a0507110604110a03050601080f0610030512070f050607 67
    0x54115080084051000003084a8010810240d41d40002e903980e170220010001544083c0401160710005042c03039075600e08071000c0081101810400c0d5803103004003a40c2d81e0058000a001075820769104520f644503005100350140c85903c810740b05540e0350701005182c0c100c03030400e450601d18810f0030800c068000358400c50690b0080d4a2140051b4526550b045585c1c0d00c0c13007a24010000003400500300700c01070008111048a03804500458103051800f501c0f1882da600482d1309501c2010b40c1882d40c055600351441500414001d0280b5840040454101614002d00101d0304403040154002c0022001d0107005910740e201c400004444c9801d040c1d400c181e540207002c81d03003401a0151208100080410762075407141d04a01071303a00c5045008007003803000d102d55101130035a000d6000045a0328001140b103524890b80c0c0000c0f0b5007551100e84c4e03031000360081880700611583c00f03c14690600010358010300555400384100031001410342e202c59081c44822200360000403641105203140e50b5100d80c05003078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 762932284 1250 762931034 762931061
    0x60904050c0919120b0a1113030302120f0717070203030d0c0f0503040312051503010c020f010c0e3d0201150905070504050f06041205070303030e0a0b0a0504050c100f0201 75
    0x100b0500e03061020450f684544c901034010b0008500080c020407070b580008082d04441c4e802d0341d560300026140c02c00030030541e000031401409104000d031300803d080b80c01c0d0341c0d01e114803481c102c0c6440707129699030103e000c0c83c0d589400d2050042c020710015a6040c009040c01d0492000e02051801c00540014595500d02c00528244801071003480042a4002e40c00300013420020000149070316041c5004211249001b4410b40c11b6007032003480c05400c0d41c00315a41c0503000c1c1c2d0b18024002c21801e400203980d410a02404941c000600000705103559655240d400030946c4101244200c909202443c880e03500c854003080302c0940c1d16183e18544542c0980001c100801640d4070400c00c5080c040d40080984c03040c0d00c1090700c1035244a0310095295204000c0300e00030104041c41e80c110120510700580c640f9160b22003900403d161240700d2442d510046920040c6681c4540320201307946d100e0380c005000340f001500aa0b891702c2060401c0241e903c42c0c6411100d09605a280c140d00040b40c02d1f0000e0a45101c8200c401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 762933534 1250 762932284 762932329
    0xa0e18060a02070f08071b06020a050c10350f060906090f060114090d0606050a06020a05030702061803010c023306010806011e091706090d0e060904050c09 68
    0x501184020044c0402d060740810400e03901c58490401c3c070800c034601643d0201e05a00c015000544940000308987d18601c5001a030b03107482d1130034040151051348100d42c540420b0081100864448800564008281a50100a1780d01a500c8405100524210f0300203510901100601c290382c42e142c0c04460b482801103400310b0080c42e00d032802800d00340019200c4d83c180007021700403035103481c1140180e0b00d144401400781002c01080341800c00141c103103031286034040c4a9808000c660688046155501c154201000b10300c6c0c003105a0a10680740d10105400314034080b564a10f07a099034003802100490b80031503000b080e480d13444854004180301d41e42020b1040c3c5480c0301c00540303100c0e40c520280e030f40100c1c02d003031506055840c200140d501000217035141031138001518482d00d000341c00050110582c0c549810301a5003413880c80c66107644100542d045040d546c000742400113114410401c10500c9000a001c060400b0302c190041000e03104103a9005c03811400101d824891400c1220076090b4403190070808a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 762934784 1250 762933534 762933547
    0x2714010c051809190c1116030b16092306130911070f12030212040c18051509091f0504021309020603011e12050303070f090f05010e0a0e18060a02 64
    0x10080780035011080000107440381c00e40c41c5a0707800740c2281e4590b0421074047d40c40c41d2243d0301c98005002454002199915040c0c0045600c524106940007214402510781c60011400c000d05005e806031845104011458030070700030403058440002504d02d0406564415184500344107141c004d4602000110000d1a400c1c0680310100d01400c2e21005402d41202d43d1100044008504070302070320880816100190340e00c42400304114a00740c0c81801c9400f030001c0c140e01c0a806001d1102130f5617040c1e40d05c41846070703038404060283c601410720030741011402c1304840a15003490062800540009a10050071362b58204210a40c03c140e40b4002c080804d034582008030192541c00101103010600801d958a1005040c3c1d000c41801c14a2034805801c0d03106131134a41c0b41140c9407090b40ca61044400782c0006161001002486005a1681060710070701c0ea80600c02c24206001141e0b41018180720f5a80143c3c02c800024071000c0412030540a40384000c44880080d404c0c81e0407609c2d203038024008040079841003004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 762936034 1250 762934784 762934801
    0x30c03030403110402091207060305070e0603070305070903051c110312041e020301020310081626010f0e0604050d020613020f03030918060406092714010c051809 71
    0x12202960f5214240c000d4030004840403034000c0c0900c540042d00a8620350040343d003103c00050000444516641c203114994806204590400c504880250003c10034408154818029040550302200714580300010680d0ba80741d00b40391003e07540e140039403418a0f00480c43d0080e1b11030540c40036500700c00c0c01940741c4130300c0c0d2100c00d54213540200081c0c2204d814144803100450507101001029400400039500c9080194511807410394034802c522007031040c54010260b04030281c81110440b1800002030a803104180c6401d00710680c1c0c80311000255685244c40d881103080b622a0344c3e0145103400091800b45003a281440c0345c040d0980c800001e40d03110f2410800d4040e540c0d000c4104155050f644140e5030014180424654022294420b5024000c405480c4990740902c0c1c06a10a60b0210703820300c901582d0b00803203000c946070b4460080540c01140700c007159021003026070301c071150700c034014005803500c1a19119085400703803055000000ca00280000e1f01003246103680d0b10310703041211504a1401c11842 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 762937284 1250 762936034 762936037
    0x6050304050a030f020f0a050d0e18040b0a02090631030510110c0d0206070806040902030a020f0102032b0c030c0203090d05030c03130f06050f0d0b030138030c0303 72
    0x103000f400c0040c0b020a00000d28400d000050201c000003044a105c01114030300107440d45d02a186020010303010001e031404070301d0081d83c01c2e0354107503410307203800d429484503280c2e000b401000500459925400b044081700b1a100d10b4020b029640b0754584032108500803582660002b541e40106800c1c064406000340301041000c1802d078001551366a0001e1403680c20144080316015007010303c0410b000d09080c0308030700350300442d90522402d029698129140e071100304020841c0c095110180d0154000000d102c01420200c45c040459041401240d04100850000d03408100b03800203040030300e083d03406a03003540640601500003510094141404a4003495200954030302411240364421141080b140050010030b0040700c0003c43c0050030350380d07505d81074411080e44452610842c1500da80c03001d00019641d215400741c1e80034100c403403131061801d005041460040c0c08640300c41ca501d5540d0f4002030302120001c40310000d5003000740030304506032560044008441c0000c4110240a40c0003600007901395a070200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 762938534 1250 762937284 762937303
    0xc150118050705090d242c0c0d0803060103060602030c030d05060d0c030804030b0f011a070f061118120d050c03120412020c010c02011418040905010605030607030c0507080c01290103060605030405 86
    0xc0c10b103e41c080301100114541300c1d1660010349c00010410800b001d00040d0002944651170070b8905005d1196114001c90342da210302001d0450320f80051190030402d0541f50040f43d04080c0c010080142c00519445954895805038001c44034107000140402c20813040d06c58480e03104e4910314102500b58541060781c0940b580e6045050380d10540000c2c107404000c11900f42442c0c8540100d0104441e0040c011640304603801542044182400194202e0640ca0080c1d0300142c2510008040c080000d0000b4080d21680c0001d4040f0350f00d4003081c8504800d24040031501485a0301982e100d444088840201a00b441c9440807170a0411140c2c01a4a0150360090450320000d940c0c101100d545403180f244002884034005440755125003049082014054150001402c2d150308030140d0b10303031303403165001a02210410001500450401d00280c4007050340a005420303004450340c000b05a60444c2d954078000300884c030303d80039400b020807030b4015590f507414070900001d440541020351540c10207407076603981e807203052 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 762939784 1250 762938534 762938591
    0x603010e0603031b1b0603091b031f020418150e07020a050f0c010f050a0c0807030306091d010b030102180d020f06030106050c150118050705090d24 65
    0x600c045000782c0c42c1001141c403030b10800c2011160001c103283c0a01e450380a81d10240b05004030400081c00a480d14a045a008207000720040c1a035901000316445118000c481072135050040030890035550942074080c0500c1c500401c0d00690307560500200c115a40d40c00007548614610f00b00392082c10003070061825095034842517484013503507219001249048003030b01e0020b01500603200c155a0b541c0c000150842001da098848000e4111401011039840c0508482d40001840060842c0042444c800040a050780607181c04a102a04c403500071041d03ea62003020b200c0725028035000342d8003803402c0c8070b0340d0780c4150110029807410580c100002e503114101a02140309203030300d50820301150f81d800e0703440502e9040a044107031650703901c120151403074010550384c00d5036009401002d41c5100d000814203043c0ca0100900d803035040340c080821401800024104018000c003007090202c280d49001d07400034410305ca840c001c800e29504641d003084000c600c90b068413119040000010b1801350690404c0320b5120303030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 762941034 1250 762939784 762939809
    0x6010c06021e040801050a18151d0a1401050106050f030a1d030a02070503070e070f030e011113050f280b1303031b0c0b0c012406020706050405060301 66
    0xa814084000d100d210302c0c0750206a902e148122001ea18030015000b00e0ba1100c0c02080659150601031041e2035880201d5803110610540344000503040756611030f8800109080007581d04190302d070b2200b42404108800c2d80036030101c20148100104a8000c44582d05ea0341c0c000e0109500d000c04c058540d02449a041b107160304040005400d01900e80e1058088000d5030114944100d990a1380586940c0001c03000d0005000d140300205150600280304002c9035249144e214041d600c1d05005c60742d01d04240510340c2010784075001104010401d0094100c2c001d00000708030f0350f510001c07400703c0300ca03425070384001d008460402503070810790740e4001c41811005207122010f540032044150851000d01c0ca0300050616080420280b41d500e05100c1118150f92081e1990304c549159110301502400c00040c005282c682d00000901070b02c0c2e0400040d10140c0304101c000708120011482002160299640500c030b8103440c52810800a0740c1000510020041030601070318042c02c050200742180300502511084d44803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 762942284 1250 762941034 762941057
    0x10091505090405010b12150618040f0e03040503100608100c020a120309060e0a1223030112050c0d03020c220f0b0a0501030b0d14160308090a09020901080601 69
    0x180101c8164200051080101e0340c1c403200a050343d5040b210030001501c00c44000608110b103500c02008080c1c5004000c1030400d08038000d001203513282d01c5420b9811549440c90440d1a20050046180b4180c1c000099522282802c3c181407034907526007080326106050107801c03c055200801c1c041d040b014001404150701035284c4c1c0907883c1800900004001d8490b00c1c61103468194954483d0600c540f1951083c80140440b91005544d190f04100c0030302030341d0100900c0e02c07105020306540e400741290b02d4240c0840c24400041507029400980c03001407000707211402402040018043c40a180c00203c42001105a0a480081d600e08011500e5409805505801c43d000000d45030001e0320008035000c140315072107a41d155030002e03000c41c40216010b0001c040001c02c7c06e602a0080d0520210040c24402200d280783e103804880c03958820350482a03000d00154483e4401d5802441805180541812a901c49030380c824488070b040507a00c9801d26071300c14080c036210341c0c0c1d115019540060702440c040b110f900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 762943534 1250 762942284 762942287
    0x40e01060e1f0e07030501031e240e011119110601030f031209140105062218080307080708010605030421140417160311060f36100915 59
    0x380b15040302c0d403041068400c2101099158000c0f0381601d10031105108881c90200811005a00c2d009000740407010350128010481d000c00c04009807407044240200b840750098100d282122400c4a0501005000203111204010041284d221046482c50b003a001d00d444000e4064030351006000083c004029030300e5550905201c4c040810307044541c00c070100b010786d10926040807071b034001240c100031550030a0700103203d5107409009080f2180c0200c0600f5901c0034500307a41d10040200103007620000c1c49035000701003c142d00c8809140304e1300554484403200d061242e405080c41c04142e104e802041020001c100020300095640c1d00041c00341d1001072011400c40205495001445481c1c9801e4000480d00142000d540700809143c0d1568400b07440d0010082440300c6104010f600002d00035000e10b020265807404c3c49002010200c0203001c60b1414640905c440d1040482e0740401c5074407501c40503100c0b0310202d0140d0140103420b00d003107544039803d0b0203000000c0c1c00c0d0412841890080d15452407a00c8019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 762944784 1250 762943534 762943591
    0x6050a05030c0f0127170115180225030512010e0103080702010f11100f111e09010507081306030b0f010e10020c04090b01140604030f0213020903011505040e01060e 72
    0x9040781d858284440b62561003800440d220001311002c0d0b03608042c00040c48d11f0881043c83d040c1d030240c000703000c1440b1409030900082e50023a01087c1400e02040342d0007850403942c80031103411510943e5910f90703444050354800e84c1604180c0041d010300c0360000c0100000344002080340e02503582801e180d4001b01c458035054810400d000700120041c00f1300700305000b0b44412540a09084400c070b01d010401142281c00407012401266044030f0a1480c804210b424211030740098424100c0c140362880c684030b40e90740c0703961b01038001c58141c11680304240b07400e01065070075000f21405402c0c1a10844100d40300040000d0500c9a045003060241243d08500c0031a1031082c81a208413010142c000e1108100d42d103803d0441d0030091081400010f03032070340c1460f1140303800c00445c0e044942041071414000f0141e001c1000114011601c800110741c01c11820b4444d0700c0070f000b03071069252480000c01c002440d0100f8481601e10b8a101201164940b040902000808040150300400210000c054807243e540c00d01540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 762946034 1250 762944784 762944837
    0x509011d060d0c0801080f0c120102161b0e040321021b07050a06020f0703030503131e0317090a03030f0b09101403070f0b21090106050a05030c0f01 65
    0x211002942c032088007015003000e00d03450029610190541ea9400c00b494851915514031170130b45d00070010304040f82c03a240c2000901200020700040c5485c810326038608414844c7c0d1001c441440b600360301160800748074540007000b0a0340c9900d101e0640760aa800034940c0c1540c44090320250890311189070881d0f625415503099050982940130020610204a5601e0000744542881840a004081042c0d48003203020300302508001e00a140140c1555030a41e19034000a1403200926510220b05021690032168001c900c4660030f00c1c080c2003c2942030040020040941020540c80100188120310300006031004080360580780010381500300b5146500501013501c10b071035100003610188201d8800c0041804115444d01c0810150103044c5001d16845401610078007510003c070140402021078004000c0c841d0794512441902060004549082903c0080e0350050705695142d105000c5030406207070b6000980411001040494071070720000307024404804c651810401e0940c20f80e150300e000312a040c1c18 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 762947284 1250 762946034 762946039
    0x4060608011401320105221e05060703021c0e0627010c031209020105120f100812040608090f060a150b25210806090a020304120e06041a0405011e0509011d 68
    0x7d56545d11400900c1900e01c41c0036244113050405c200040c00d00d40074003203412207075240d005018074101610300c5003040c148000c8000c06110320840648401d0b61940000d11003412124280ca01d101c402e5000c082003070b5624128541404845c100c00360200ea0405a01032698000003400301e04061030344012580c038054210302801080a4600380440451203031b4000e0310482d0f0400c080a291982c844807543d68010220485844190800c81400395500c91b400f00c81d0b00c64200c800310317510751440d40c1105150000c100c52240740180e54424480400b1452075503180241082100b540c200410401c4148501c5100350542040d0101c181020f810845401110200e004914a00c808005c0c84e00f00080c1c07084104891031413042d1003400000e03010710300500c20b03603000c0c0da0047c403110b005a100075001e4030018000007400da8001018080020340c032074031018904000760b2982c10340d519a403400001410f21070b0000714420300c078100c2180d2520440d51100503103400f40780910f0010008029502401140410308101a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 762948534 1250 762947284 762947347
    0x309023709022206050313060b130f05130804140d0c03120f0813030e01021222060212031902120106081506040503031204060608011401320105 63
    0x38000d03079142d0181118076480d0140300c03409041901c1c560660640741c041d44020a03010b0020481e84100c000c40c1010187c0728010010350b031810f50300003d07010008182c1c2e8110f41911007100f28000031003800b415800c00208030b0a50401600c030b95070400a80107500519510110707400d40850700d580e41520640c207848d00041c40b601c0d26500e0341000e0040c5950541e1010206a20b003d000010354452040507200c2c548003594141c1c1460035a50032100103a100307401074114841c0b4011591110102001003d09002d40c000c110201c99091601c21500700c01c1c0d510407003e5400c600701c404084144442200ea00001d1000391401007110101070030000d008024042184c00b8070100040340d05a082450907005003021100c0402e03080d1081d0820220344214002c05405400500c1615140c64045020030b81080c030802c404692252030b028840d00b1a0705441200c01030030380310030041203040e50008424504c119000010f07030303401c1e2044071034003200d604410401b0704105000810041ca8240c04142100803400c10b030015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 762949640 1106 762948534 762948539
    0x3240320011b1115040803180306150d0f0506010b04060809070b1603030b040908121f1205030c070b04050411070c0611070e1e060103090237 62
    0x3135000580c180781003112140c1d50014101070640e800c025622030b1501404c0001c9005e0b2060070130f0182d085032081c01050121000c00100c10001591041d0b40d400851410b000502d511800240407801241c002048844840008100300c500325036800146071290741e85241c581c01c0310b108100004030b00308403501030407403a544049a028040d0500081020301100810103440700640100e030f000e000004c19032004003030703800c0082d000b0481b00078145407888d039100f2002803802c080c050304103040e042c945a041041020800c80321149140b6041e02c260a0b51200305000b59000f80c060184603600f08020f184640c02d011098500c81034000140145462a208054901c040780c01c4020390180182c00b004590300313182242a81c0a00400300703689003010880c0c0e500080b0408007408941c10142000321810169441100c000c0b202c030b248040d0345481c000da8014002015411003c0d4001035943d41400 = true := by decide +kernel

theorem cover : BRFrame.Cov 762769784 762949640 := by
  have h0 := BRFrame.cov_init 762769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 762769784 ≤ n) (h2 : n < 762949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
