-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:13:53.984117+00:00
-- url     : https://prove2.me/submissions/97fc5440-270d-4683-9ba9-7ebed4e97887

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 197302158 ≤ n < 197482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 197303408 1250 197302158 197302169
    0xb2e051005043302120403081303201f05070b06060403020d120f080c09360f0f070909020d02190302210118021303050f1515060a050915030c04 63
    0x1e00341030f44801c010798460419403000e0781400810402400490070389401004601002c0c4021200999252100d4282c1e00703940100c1030310343e45000c15480803441c05483c8410b440007110270180000005901c0179105100d8246c1c010101207100340001c4140e91040300f51070055401402c007040f02e01503446e10718a50b000c400c0b01134000c00c2c000030814200d64407842c041d52040c031034580c8080c0303044000002c101e034048610421500208054001c0080d80035071028003400f002c0c6189200c0030500b17000280d03040c5072a008056142e01c1075400b0400100e81ea102250b00b04507601c1c520010307910a02000254080e1140161140c02050005224200c0c29403542c002d001c2c01c4413044015400c0002543c49030b0390f403902807050014410499042c00100241580100225002d61046259140d0380341c0d41d0740d00380007060b14403c4071030704040540e468000f0040011a84240d030000302041c510001d100203070041c01307510400c100b00207001c40c1590390303074680401012a040001c45023640328030700419040000e60003030080b0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 197304658 1250 197303408 197303489
    0x70c090606020d0e04020d0f02041d0c030405060103031112070b0f06040b060f0a0302090a0b0a1b0c060e0111010609020a030f0212060906031501030b2e05100504 71
    0x1503851010607a841c002c003041d41c40305504454134040001170340000b03005401c120741c0c071080c062a80705184001e0000307040e41c1444a5014000d00001e128100c0c0041c03440034004c1c0700f0420400014804504641541e07814240f0218020b54820070741d10b00242e01904002d04000014104140150611500c0c820b26170b070b09140703140750380342e209000603500c0354800650491014809440702c02d56050182280c040da6150050519441200151110325075500041000c01c0010707110641682c0401411100352100041440c0c1051540d80d41c40c80f040680305040800c01d030301c070313445030160300c0b80001c10010b50b0b800e0000d006c207a4030394000c20002e40c0802a1800847c0c50310780303100000c0302a4000d80e8090070101d10200c19030394582d0240310046800800b0550300d40500810111105003400200340654011b1169801d0352414508401820064110032014903070900e80082d01400006200b00644105484c00000450030940691b400d02450b000308084402908801c004001030905010003418142e14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 197305908 1250 197304658 197304671
    0xc0a0209161202030603031309050609060d0f110d020303031e070c0b1602010e0604030306060e060313020f04180f061407020712170403031e02030a020a02091b070c09 73
    0x140104034800e01000c10703119400b07242002980e0b40074540c003000140c1036a14140390760040720540000d94028014843d42c3d80144081424001e011544c4050161390810900742076840d0740000c4000650020200d2100204000c0c0c691100400c00e03900355806400c80e6100d00384141c01c500000481c0c1400010720200e0f000151300d0501c00c141c03400004c2c0c4c000e210340c100c3d602c8940805014040400c52481550b481d26414840c5140400c40303d803185000342c0e8002505801d084c0024440031000c13035002d1007003805200b80860900b4111070b07044150390454140344004441030104001d00700c2622f2210b02e195003c0b002c84107000403034594440540c4160410803110640494070000150140c41740b600590098206004054010308445030180c001c00e000307902d000900380900350780e80c40743c0c00440001c0d4500c94600f002191007000094007500301d0000e1070070482184002540c5050443c4043e11560307902010030000d0000300e0070074600c85491030401d0303503d0149003400c00401c0b02920070300c035500f4135080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 197307158 1250 197305908 197305921
    0x10c020c03370b01030503180102011a01030f0b0909070504050c03091509030c0d0306181b1d120102070b0108010b01020a080711100e0a0506030408030112080705030c0a0209 76
    0xc005001c00003088640504841200010100080803400d910288440710015008601000d41c028005c6100d20015a550000c182d0340740c01c104a0000102c0c196814428600559000602c102e04049400c1c80c1c0056a90031f01c90605024242d42c0c2650380d0070424002c18803104139000314903601900c80650b810b201c15110815051207900c01120340c0f00158205101c4841e83d580c3c1b030395044e500300000c0d8040b282032a09688045060050054080d004655108010040a607041c48042202c4c1000802006911200205104d510151010610400c8003900c12111200142d4910743c40c1c4802c050000c08404010111090003940000410b5696a00303100c000134016405020f40049481e041e030280c40c0004960391000e00c03070b80204600b00c1e410f00038215100000d4844180b805080000d541c1c8499010004a0500c1011403464000d1402110304004001c0811800030850b81100c0100e03161001c40461410413a0780c078050032100910901000560580c0303034400155078244c143c000c444615070b645401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 197308408 1250 197307158 197307163
    0x6030f060501083120091807050f011b0506010323070b1c05040302060a1a06221a0301140117070f0905030a05011409010501180203150a08010c020c03 66
    0x2152052180a1100c0c3c1c0b118102c0c000f840040e00e40905682c035540714101031750300c0032881444039000f000010f255402e081c08514191044035041104815204010708106943c070b42c5520841c094a400f07041c0c040c0c1c610401c0d901c906008600d00c990b0390101552001c452030069190305c7c007807000b030b03541c2c0781151180702413010700b1030603244001e14080c014016545801c1001860f6000003403084441280000542d4203544d031405607078800c40c0709a01418543c40d054007560f046401410940040b00d90000300d0080c1c51302c0b04821200f40102c41c00300c0c0da602c01001d0750f807000120f042ea084010700d110082c4c1c0c030500c014181006941620010f0a13400000543ca400468004100070b000c0b881c085034980128114074024104c46c45035420510300b8010003500d48002c0392414105002c1256507a668047d06168802c01000303664000c83c00300024401940341203d080c1c8150b90007100e601050381d000012480443c0c034404540780e01c4101504104990b80d0300c4450038001c2040d40c2c2818098004d000c40000213141c007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 197309658 1250 197308408 197308411
    0xc12030406020d0804080409050106110105070f02250305030f0a0f0e010e1903050607020d020c090402010c0b07050d15030b0709030209010b070804080307060b010f08010501080106032406030f06050108 88
    0x1d079000744070a0940040c2181d20000251050f031709240c081201150844643c01403d020300700c241c030388407401e4044102040c01c42d00d0090005003005440030034051484d60210300c4034403124a440ea0000d2800c86013107100c20340d00490340000d004d07110000d580390818401c04090038440032203840c2d150f40400016001e40f408480420f0150000c0e10300d6181c2003840c41c0190700c646106c124180801010b5450359192803501d4401c0d128180540d00c05150358894035810403034081014810f44951101e0b04099001802c100c02e0100c1c020402d0744a4800100303550310030815501c40301c80703080741401402d089581c024500300e079074001614940103800004e00030380d014120543c00c0765400341205480313a10301901c5d00d03d150000141142c00000400c0b0008003107808101405009010700000036108101c40c00142400981180d19824401c042c001080241e802c003100d40c0c11a100c900340450a01501580c944060061600d40c00490010b510013140040e4560301c0340090181c82c41c42040310a855000542d4220380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 197310908 1250 197309658 197309669
    0x1020304080d09110d0602030a060801020412122604030807030b090c0903010207080f12010f08060a23190606051e07020316030b0406060614090f120f0c120304 70
    0x1c10001030b000011a81d2141d5806406010000050041c58000800301c0042078015900da41e004420301a008401d880340c1030003014910001c40c641841d02480141150441002902c0e0500c40cbd490250114000d40c95101c20701c00d41c0d184d82400d11004442141440c0f41601d050300020140400240291f01034452490649030040914a03280d03280e0300d4491032075000362440c0760195000c1c8100400900444003428030002440d031241d031103001919005000c1e480581c13040308600d60745081008241404100140c201c11201c1d4049108214540382600d5440f11380440022b40742d0090401055880303a600c040540d416400701071052560350b20b003c4405010344105030b0102100b620102003021038100061010900c0036090380d4010710101420700b1214100d07070064840511460401040140d1481020b01a056500f4200b84d8140501103018984c042e1024040c007441a6020700c01d036507a680950140c50440c40812548085071070030704562500440c4200c24042c1002c0a018198560080151026242e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 197312158 1250 197310908 197310923
    0xc070c080703080c150127060b0d05010821040b070c0b0d0203070305010e0c0901210203040c0305010e030a09050609120f15010b040506030c030c0705030706091133090d2301020304 79
    0x20105910380c900560710514040c7c0300750742c3d200020720090081c2c0a07180c40d070502c150010f02036140891240c140800410b00c8008501c402142050075008001030b24180e42d0b8071290a0348070803c5140030246964250044440707001c1c04104107480041e5074006620400c12690180071990ba200b085002e4040191507a011a00b000d0050740460351040f160b00d203024142c0a10300b043c00000c9402e0b60201d92003503401392000700200d10180305103d000d000d00e10500560700000e46c501000d110000f001581680512407280400256580301030342e071000301c5190080404250f075070315400c02c445a0707951103100c1d5001107041007140c0006a410390740d10580301200c0000e80381d00c0c615503900c0030000780e0341e000404450103036030700b44030755008210100090300c9424883d0310005401c00c40b03800e218a0202480034000e210700412400a1130907884400b0f40b5012130020380d9520b2440711101f9210f06d49001c0d43c032480d9005507540c13582006110051400041c803895800003070300c0e000100185c0301e082c0d1004031009003503030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 197313408 1250 197312158 197312189
    0xa110c030c060a031d160609060801050d0f020405070806031203060904020409290711010203061f12020f18060304030806102c0102060702150c070c080703080c1501 72
    0x1410040300426200c891440c0010300d0316101000a01508912004029642d01801106c0250011240c0c1e10010f886282000c2e030403140f030400000e1a20340c0501469004080700000c1c4010000d104a40003102640200140441d2034800d40003000101304443c071900c61710401c0014050040c41d401228001c40014140e840c50b59101d400f400040c01c1034000485400407041402001d1802c0d012801e4542d105100e5001a5414540c82c018080c0301d40400441c40f0381d2040081c014140d40d185a1031180c40c0e032094510701c0c0c1e80c44ca00c80a5807602c40344424029040c0c00007030416941c040400c018400e156800804500d1a01d410b800e0240c14001210014046080940400c1180c83c241c00038101c0c00c511403400d110300d505960850031036003c41402d0b004031514030130605c42c01c45d82c0521400b50b004109200a02c40c104503400d01546003030003c3e05c1e9880f90040002c801e01408101c04040b406800603004944480756603150071100c603417094041040c18050070310010107110303140c052203040715280c080b055041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 197314658 1250 197313408 197313433
    0xa0506040e011208040f0306090218090d0809010b0406090209031c1d03031b011b0f0914040908040612050a110a110a0203010c090824011502010f020409020a110c03 72
    0x40c140f60a0007903601c12000d00000410900b000d04400c0514420000421070750080d03c140314000c000444650602041d20303042201051001540c0c2003801142c1c501551540c131481c540a0042002c4030005070424246003011400758202e400802c0c1c822429070072600004628010b03400c100e807100d00c1c9a8000740c40d203075106440518444804130b6919000381501d10300394240c400702e03010310000002c1b0030031a51540d03013040c0c6d60b01e0a40c2c0841c000b00c000b400d1440c040d484400d4010958842400707151203011162902414540b543d034040080c041e8000c440a42d1543c440350040c2040c0c490404d40c802e0b0905010000e03d01d07071900e018050038a151580f615040480300c0710281c406c02c503561700d2826640300b00f09c030040c003699003405a1500300c0ea0030744408000605048403582046080031070480e000e01c008220781404444031800b541101c4140a607000d9014504030700324050081004000d00c040d0006c200800c0d1030010750700801c0912510307110501199009540c0c582c64520b0100140ea00d500103166a07000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 197315908 1250 197314658 197314679
    0x109090c051c0b030a1b0f03060603060e0d080703240f15020c15090102010906060b0307030c180302040b0102030c2b0e03070902180402030901060617150d0201140a0804020a0506040e01 81
    0x507003c41546d800c03030507540ca842c0e850031420f601e82d00550318142c03078490401c24080c1d1440341c421001c0644015212440e00b4200151074100c2c081c10b0081015514599200054011000e1003d0b80b114001864807481d540d6045041c0d10425005004002179032480344203402d4000241d020900c0d07405408915000e128800c0c0390841c5e08038200550540d503c0e00728100000b00705104031405440c0c1203150139200c0c02c0400000b811654903050550034010300380403e90f503426855154004413030b41181c002c01d2680e16540101d041d401000b10f46003252048410000800044244090443d036020802c0940d0305400d0718115007200d030006000c0d405400607a000d001c290115002489980034040400044030902404034080b41d00844031200241d41d2000284800c6a01021030310242054106c803219904100f0010081000c46900d440c2c4140035148540d0304690003880a22001026019425100e2a801d0005440d42d4001c4608a03c5000071880206075031400b10180c0d000d843c03105040c04250703800c1c009104d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 197317158 1250 197315908 197315933
    0x1080d0503071407150606050a0c06050705040b031003061107030512180f060f07080f07050d0906060e04030e040203160c0809060a121a0607030e0109090c051c0b030a 73
    0x203040100b0040b212030f885020000502c50b02e8425629004000e402c1a4401c04984207604200c00708101002007644659010151911075500700d4000200390703c0711201a0744900c52a48201946840401049002001502400c0031030b40107400a0229a103000203000c91807080c10703001404150b050150641c0070190000305984031205104c442d003203805103c02d40d0714000c7c3c044022030b03180c2d000a0030011129051190701d0b41040f02c5040996541c00c00344605202110000d04460030020042042000811140c0012400c50303004070b030400ca00b584611103a50700b68000c44056000c10743c2115100d4013828244210780c40f400601e0400d80108031100310444a038403003900150741c000c070701b071001e481c4a80d6010001c0c0031204440c4c0361a05503241c09054130007a40c003200720f10588104a00c0b220710317541d29100c0881d004a5814600302c0600310616005031104240c80e040211002c1c86c0004a2013100c0d00040101816035174180c0000c003440b8804840000d8421911380c1c9501600005420400980e00c080c404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 197318408 1250 197317158 197317171
    0x6050d182012030c010903030e0f0c01110705041104090507020d0503060f060417010506120d0f0305070c050d03060519050a21060c02060114060304050d08060f03070905071701080d0503 81
    0x48028281d61181180345402640c45004c503a591501d0345030415030036100f485c0c0703031588500207490840a48495151030790340f076034241410f000d84007105460300c500c1070017400c01408000703004001d0103010300b40d48511500540600e100e402d02c0c05010130101400080d172480c61144035507505155a80380424840448020b4100e141c00810600004c10314250060300c80c03c100810b0000001d880c509a810010b06000703030101c84c0140d4010900c01003803140d101d003643e26201c02134200130480381c442100440b1420440f0002800740e003c3c406960549641c07580055045500485030804003249003c1c03e808000c02920a169003e201d41c40108605a03210600b8500c1400d0741e034000301480102d40300c8400741c1d584402c9580c01a00140c0041c840b000c11b1055580031000f090b40d501d810740ca026030755260f80c0c1003241d1a003014009520300181007943d49a03448508a10050161141c0c580d0307980c80e08000e0201599540d0120b00070041ca512101a13564400f4100c40c02d1500410700c0415000080c0c41c0340d88068040c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 197319658 1250 197318408 197318419
    0x5070206150f0f12150c1c11090d03020d0e041104090506120601080601030506251202041a1b030a1b030e040501060f030501150c020114090a06050d1820 67
    0x102d16940c07640a65202c4d500d44030050301e80d0b000e0b8441049140c00300208904c108200c203112040e001d010401f900310f000c1c3c08035100000c01d01d003520b128100602401040a034840c905800007000c060380030501000248180c0c40e10300001c03804104000a0b0b60201c00c01180881c0180000c2002d0541900029000440039109940196400d0b40f90b03400c0034400d8100c010320b40d0105004204108040100fa50321074040508400384140228050048072200f41c448820045030325103401400300a0f034100c0e0004c00880000035802016111080381e282c101c600056440c5003200301c0304100700b50100859070720b42d08c0c5650b03250600141034450320711101c0606013681000500d0700c072011030341c85912a4074040c0c81161148044411060f200030280c4205070006806082981540b400080c1c01000441c0c849909092a4546948562400d0014003402d014584d201007a00c00c005800d5070408001d2107500300c083c40902c08007070312000ca0005440900d00c01403961480134800301c95129240e800b0302821100400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 197320908 1250 197319658 197319679
    0x606090621140c0316020105040c0512070512010e06010b091f03090c060815010201090b0720010c09060908010501140103090203100501141c0503031f090203070f0305070206150f 78
    0x202080c2c00300443d0348800d10b0100106000d4061051484400000303a248002d21181c5020780d165903103c1e1030f40c807a0b1409003106030460307100848144441c501900d005007a420610580d0043c40d406001034120b400828007071180081104080d0a04540c0440c4019100090400c109103a4031000b003200300956082656030300f003441c0000c80f0082d02800400b1746035a004030380d04001d114410b50600225006056a240c4221413001425491900c0c1e4042c10600b07158101080c049500886520440c0d060001035191445e4086019000400340055841d555118003070a6298840c2900300c1c1c2c028050150081607440501d04a5031190304500800c52006c0c0c1500c102c1c843c0c01c41e010082c4e60b002c1e0490100c00300c0203103603002541442c02e00c2c803811040b00355150a400f011074554503100d20020700381b0640b40c0301071501c00d4491441e5081c05001010680c8045681e0710f004200181200c080401c5500043e00340b034042030300f00d0b1001442602621001540564451002c010420341c2003c00b4000ca0300241003e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 197322158 1250 197320908 197320931
    0xf06010516060902090a0212010e070c05010609140c0f0d05060d06090c0608060303040e06040b030712080703030c0e100e01180329010b0a032c0f010606090621 70
    0x44078480300314818200824407405030310410003105070007004d12050500c140034001c000c19404131607078112140c03184481c03120307103411204441c04407140c20045c0607982015400281d48030300d540b09402c4c140824901d09019242c91128103854070500c071140001c41001d2014042210b05640f00030b4006c0c0005240705081c1c2c0c4140c0d10b00050f5020f460050316000c1c00660f040104d5230300006000c0d401b060131009145072a05018160080010142c840ba02559907150008043c1e1001c010810140c95003a00103214030726036251903a81c3d07170322903142140000d040240a0304283e0242060b80b008907402445000c00c103142d680304a80c9050030320101ca04005108801c040e1411200c480b8001031070042c49503980e1b003855410564581c0700203c1380441c051002d1001080780c00406015030744100860300d40030449140310201d10854004502d1007000c640322070820701d00c4480000a88007600040c010017031110564504050740d054a051207400c1c04140d075803030010080c005d032805000c0785401420b000281c40e03a228 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 197323408 1250 197322158 197322187
    0x2060414010c061407020615061608040b120121110d0203011415011821050309030d0807031802222406080f04020a050618150901030b0306010503060f060105 69
    0x1c00d05420030b642084c240714045030305010070369101c00c111212104074603c0d00082900d52140c8541185561030406011040107801e400300d400500c4c00420040d01d4041444130245150028031444861030200b1610202882805542c0c010789500301c000c21200703071a00c00030700144090392a4101da26550f6100c4d407621101e9026240340c0100b114102440ca13855190001600034940303440c1e50821605994401c2040135400200c003814201e4100c1160000340351031821914600441c600180d1600170140004030240d80400c900740300300f10b85c1d9014845508400101c107501c00c40349402a410100311441d5200058010f4512581c1c060800320014a000300091031041d5032071001241c0000c0381500703000300710300ca51002000d41c0010b96030a0f08040c0f41401d0303000501d4615588140e41c0501e001084902c81c015001c0d01000303000780041c0c41070300341c00060425a4030316800009140c0c0400e162003079818003400d00150140c1600c9000e0000d0140da10b500c02d048000710740050040e8100b104c1040051000b42c40c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 197324658 1250 197323408 197323421
    0x1e010b0307080106081009050d0e03070e0c0d0513020108010e18070b280503150a050303030f0910020a0503130609120507050d0507110d0203010b041a09070201020702060414010c06 79
    0x1000000a003007030170982418108801010307600055803c1403040c0c00420390100750001b100840381002000d40564034007007070402c0b50079401001c00382080b0b420000603e0961009014114106404006581d101d40303040140e100c0c1242e001c0c0c00a40c2080040c0408040d9901c0c0300c3d0444110307890080c4140d0040c420900e400310702d8105445c90040802c05400089000007200d13031984c00390003a007001d8440b004000f00580001009a4100d810142c4400c4c020384a17140da40d000b426002d003d03607982e45800c1c081c1c0c2d4900001a641e14210b03100b2000480d0480c192442aa24000d060b88d03900351458485019081e0300c041e41c06400d480003a5074142020000e8440d00c143c08200400da03d555440d40c60b64103185003000d140303000d544140241042004006058000311641e4000102c8908174030440c41c0c000b190040280d03c83d02900540350800541425043c04804010b01004072022102c541e0345840c100e00780d010b240c90003908440148030130300100b1403008003c04001410701d08940e03601c0c840d84840b13064960 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 197325908 1250 197324658 197324669
    0xb070309080d020a02030d0807031401060e0315011401050f0408010207050a0c060206010f0501210606030603050c240705010f050a02030603160303050a140412030e090a050103051e010b0307 83
    0x441210070440103006004484002000e80040c109039203081e0082500c0e184008840350400461800007104075000e90301c46406542c00000d0762a0380d41e1910340c00f8006100584085100f80f050300e1802c0c104030101c03442181130300c01c80e9064203002c1d009140156215044001d043c202c0c114240f0003c40c0528091000c7c0415600900040110190704d0074280422005600020110b4209000600140c1d0004908008851080ca030a139402100703401c0d03095200c0c68603030340412a50b04010000420590503048002524080d02c15544141e1130f0504010320f4190170903c0d90303101003840c60903052610f0000007405031280228008070340002d28107140c0c001c0320811030305444101c1d0301000f402034500301003120b004150b5818505010712811502d0240003405911800005c02c600325000c01030f090304c4482500d000f4003801a0405030728001c1e150182c40c1036040382c2c509016000c00000241001040d000340360489801002801081c0c0c5e00c4403110038142c0340b07590605a60341d2608001c446544041021000411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 197327158 1250 197325908 197325917
    0x210810270902030f0102030711060108030a050c010b0901060f09060e0d060e030c1f0f200c0a140a12080c16062301030201020f010b09060d1a01030305090319081603090b0703 76
    0xd0001c10240c1301500c1074161427010381c4900e00600c01008000111070310000c0c142411174503454140c1a042c050452040b01d544c00900d03407400000d030310f6080344411041d40101e48a103541e15407240350889205589101c419803207807505003800040b8105902c40c401c40208241035034500407200309503c3ca0620076641d13030168202600006040701c0c2140c800d0340e40841d056002032068002c1c1030705802500100c8401582000d0300054800d1420300108416121140d0107070b003510b260b421603065240c951045582c284c404102818640707042c40e10461041e48a803090955580c1002c0712010001e00302804904115031507a550b030482c042c01d101404000c0070154034010200d900c1e41c11440024241108181002220303811b22001032119560b421032140c0c0716205544c0d40340383d002e0a044c548800f0012001c28406c0d040c1c400b0021052550001c000c24142c0d0080e0125120300d0305a08a0501d415000303030740034100315401d1141d070b0500c0c1c1011080c207100c0c0b406894149842d940312940f8407155444420100c000c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 197328408 1250 197327158 197327161
    0xb030c03040309060905030312090304080106030843060b0a180f1a060304020a05040c0c03020f030703140a0309170901180f0e04050a210810270902030f010203 70
    0x15501c08190000342c4045d181c0340d00020710307080100740c1d02c0c000d80106502c0e40c4070103800512440d07810000e0f5001010900000e01c02b05541c1e04081541c1c0d03004842c3c01d4000925401104107414000c1c8280b24030102602ca4414100030004a5031800488101d044400315200d9006851030b41d180080c00c006084400c1c800103116403076080c90f0046503030b07520302458030508089603001c0c43c14441488208000d800c0e20501d90f20340d6944001904040c917a004903901c80c0c98424454500707a4040464044144660220b400103903120200a5070b070301451b40010001489601c003d80c40701205400384c5500d4999090101d00303128107507200c0c4590031401c000b815000101081c0d4001c60b60b40304920300d02000400b0202403040d030410340d010211b0181b40c06502e000741e40d000301040401608200840b00c03a81c02c282e914921a110524454075101a22304800001d0380900104040d0142c8001100c100c54a03800c5814400275520314149800300350300b08491003a65900040f00260f1424800500860000b80006949 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 197329658 1250 197328408 197328413
    0x30603020306071e0306080c01120e060103290103051e0f0703050609010b0604150e15070c090605011107030215040e0f060301050c040e0f0c0403020d110f0102010b0a05060a02070b030c0304 83
    0x2c440704c50480704041c00c0220030880024081180c04000100307181040282042d150001c018003010400240daa00c503907400001030000703070030f034010341002c0042d07038200010048412025001028080500141c002040a40110781c907010960343c0451407100303590000505080c00341c2404140c1d8029a0150401e90402585600a20505502e0082258400c2c200703070a01d500400040e00f0051764400303000882e180340500381d41e03110a54551072910082c090b582c1480e440c19455171300e181c2c42050109805c03e0004910b170360040d44400c4422081c40028001349146400700b04280038100c5443d200010304000110300b884011821501c207a013004109111030030b111050508481d0024480f4010704824401407140711400801c01da00306081c20051011604e60416080c5541700756031000750302603d00c500c06000c000c4040c00c56000341c00e0403104581e256200c82c005900342c9840d04105030740070380611000d020502c2c2900107000d241e41648100c2d1000d41d104c2e042c002c0c460748251403c00600a011041004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 197330908 1250 197329658 197329697
    0xd060b0603160305160503060d03020f032b021810140f0309160503070905060f04020a110d141b0a0605012403021215031c0c02041103100e0703060302030607 69
    0x10040c0503500001c5c5030082c000340c020220300010744240e11500340d0060302e406161003000070101a1021a040d280c0d500c68140174003250a60300301c4903c03000780510810882d17007141403080c7c0e805400501c05000000054100304144282c10f00400c1080c071460710101c2c42030005440207000f19400c1c1c40305060752400d00030801031a000c4284440560140500814442518080f8010049900995000c613860300c030203002400c40920b01143d0b940040c4049120382c2c800b903201520746494018074080e14000066840c0c201c60070005c1245c3d03032800b07200c20007a00c920b9000c40d04100c1c140c103802500381d4456412581d5110107440c000c4e4001903614621102c11101700011607642c24002c02c42d82000c500d04050011410341e036480003094030340b40600c40340909e1f000e92000e101d44102d010710100c1e00b10b8900c859480103000600c90000503070140d4504003508032041c01e0202164000c50010005101081c50003038100f0003504010710751410583ca460000005131006c0098502031031654845002e0425480c90250 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 197332158 1250 197330908 197330911
    0x41d010504021602061b060a09030e01020d090b0d0227030d0507051905030d060806070f0c081801110601030303020703080c03040314030711030310030c060503040c050d060b0603160305 81
    0xa105070b01c1001040e04610110030f050380c8655040e1081900c440a80d00d82c00046d021200c0101c01d80d00540040150f000c20b540d21205500d0300c251142502e040c8020012071b680c0446a1510004c101035400600000c1003203006401c0c0b01507403103c01b500d07010042118180d14211001c100e10050034544101640d86424030000c08490a50300e0903d00380786140c0c403841e540720800642ea100260718240020148071040c0103da24503200b040c3c0070300c03203142e82e07001d0181c0e04c28003110107030000740e4403425400c031040c8110499800541c10607042c03402d0114400c3c15403030310040010340a051044091040300d0021007844005c0c000e50090301c006071a10b88170b00740a092001e000702034145c0c0050030010040000e80000070003481c07621b031840c401e4680c0c4d6951010b442d042c10b80380e1000c8461102008001030000700d6550341b801c1d01d00c03560704400501d5580c60141c9150106440c0102030300c1d500c040c04c1c800c90070f203002003c2d07580e8003a810114441d4402408691254003e0314004c81e61180c0c0d40d11004280e40602949 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 197333408 1250 197332158 197332169
    0x25180903020105060d150507050909070905010225090e1e010207030e012a14010e06100801110301090b0303270901081603030309050c041d100507141608041d01 70
    0x519041e00719520403c0d4a042c0f0038940702d211f5502e001258406100c4c2e41a0f5240c1d0320094040201e50800d04005440080d40b0300ca401d006103e00c1150419007a0207a00900c2c0c1c502880c00d01110345ca041080c1240034010350300044085201c0c0242000c183c52440000c001401c601d82e0005a451000307003401050b00045480c002d051100d4500d042e03e4001410354601c00604003001c1195034003403e4a444064010400c0c05580c4542c28050003007100c5070041a410300030114040b084c0c1e072140c3d40f042c60314240c4426070140e95203c2002d100411803160070b0341200100c44401000e980c50320303014001c1c00c43c03d182140044071501c48112075020050a01e024018003612098004000b51364844c1c444507074085040c0402010180ca46c1c402200b0481d040007141079100005000b03004224014421308041c0c403169a0714481c9104a4485050149241c401c2034090320b1107540700320002e41440c007401d1040e40403060900d84261002028004110f040019201030b0020003152040020880a940744040068000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 197334658 1250 197333408 197333419
    0x605030102030606040b070f020910140301110a08040305040513021b0a050d03020a031e091703090a02121f15080f0a0b060a090c0e01080906092518090302010506 71
    0xa100303969803a4401d49003103c1408080540d0340c8003600d06079190f00e2144230001d401c20314032810b0100314082642180c0c2603e80100c00034841d030301c84c18205400d861460f010070400c008100260750180344070341c0303c1c1648540242401c52809699038042055811743d07030484440982d01140401c3c04544441c408111404035a00810043c440d503141c07940c031012001c203071800703042e800504468858000c3d00009100c0f034a284034425068007108a80c0050a13a103c0d04803407150640c2d4100385003d20040a41e401120100010020702d41c00f90300f888252001045052180c0c440c08900c41484072146410441d008003114010541c480c110b80303a1401c418050300000d00d42d0b0071114000049282c002034500d25940c00000440c010f440f200301203495041950014510b140c06c012210001d15004120078035086030a0340c4100c03040e9914803102d51148070139960444990007a106002a4901440080d41c200200884003885c01d50748400514a41c45100e1410b00542e4864003200c0900d84c0a214240d482401a102c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 197335908 1250 197334658 197334661
    0x1f09061812030b040902040e010608061b07030f050f031008060105040c051608090d06051e0115030506011b030806210a0311010b13140601050c0c27010612060503010203 74
    0x15450304040c030014041e07041640c1d90f806012140d643e90005143d10750060010842d04d110910080c0c0078010a0003504981d108800c082007010302c0040321511794123a48402c05080000c030f0ba174211042640f803505002044014420100009000001140205114900310f04250310f0805c045c0d042c40c8050784403a104514010400540d260490100c60889036402d414031200c0da4103150503d502e000d50f105084d04820459414000c11250703034822801540742004002407a0340c0c010004104210900481d540d00342146040d100d0380d800b0b070700819000b001c141040081c4080e942c044080382a640b900590010b03400009118582c2880c054200c4658000d03444015046034450045950310101600101002424005014000340a40c441a11242c2c000d01d0011040d29440301c1002400b0004075007054010240c2c041804c0d50f000f0811240d0f4490f941010b00b00b5007a6030b10400110074400c01c0e0501c02e0000c0300024042a10b65201202c0c064502510b403003590410048058049881039004503000361310420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 197337158 1250 197335908 197335913
    0xb0721020304060323162d36090b10021504030201150b030105120c0a090b030307020306040614010807030b0103080c16080d0e0303040e0103020607051f090618 70
    0x407035064944904000c100004011074440d0f42d15205c0c5110701201d81010240300440020350300148140f101c1da80c410f4110803a12565807840100d003102c038280c0c00403189040104901808504103080d0b440866900e40581e80344803070407041c0c516414810518185141803016201c140b00d101812481038558880d400030500f070284d540c1c110075002400010810000901701807007500081c0c241880c0c01c0151140e103035144801c0b100b9800a011300392040021551140a1080000741e21003a200d0080007620f8180c07400ca600300080c81180130854150008001d01d0015850410116003e00e10810740001da2502100d0001021300303040e04001c0558001000410204039010861815070360010703103041d0340301c01d403142151074110002b034208040ca165000010b6152004039460b00032890070b4407140801c804410400d5280d01c258050007000d1441140180094200038018080b06032142d03044640041072140c503560300d03c0001904400140c0c640410310200f103240d00482d00e0160100d10040061400d90707 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 197338408 1250 197337158 197337163
    0x715200c01021506030c090c130618090e060c0f040906030507031a010806071407020405040c030b1b1903020c030301091b0305090c09060307050d14060615070305031e010b072102 78
    0x900b07119100e00142d401107030756034623110300300d49441003401e0341c150b042c9541c0c01000d05a00c5000319015040025800c000446a28a02510490042003c06000c659482844c0c0700f00a4112054801400b0000c3c000499802c41911490b805980150b000308441d500c1c61514003950f00c90426140c080c0c2c2024801004044000160b0681001c980e040106809528000c910208d000c3c0a10103076120b0304007130500041c043d03d442e0344005c0d01c0c002c41003070b4082d80c2e5060301c0a0107102040440b4030f076400b0400040c0e0009254046801c00300c01145809881c200c08005540e10b036800c2a00100e0b2850740c1d86a000d641e1a82020351030100d0b44003410b043c401d618081c1103103074950380e9603e00c050041c00402d00007141540c0c1840b9020151000800c038581100a80c2054002c3d21000800321609100e00008525145040010b120750480b0403a0018680300706076030103c8940d08040d014170b250040076804c04848401d111680c1d806880190b40c000e8960019013490311501d01c451a400b00740c0712028400702c581c40d601 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 197339658 1250 197338408 197338423
    0x40608011107060203040f0b0a0e010c090501020d1809050106050a0f030b0105030604180506090a11040b0f060f040506040306021801090e01091e0203040317070e030715200c0102150603 81
    0x105005860b071b90346007401c08100c0e29043c00102506c0d920004c00400c01c9040d44141054807000000b00410b8444070410341d038a00785406260b000d40e00104140d04440e104103419040c0d1401e0b1645500c6150356001203400b82e880a0704044040341d40450042c011560204900505060500d001e03c0b5100c51040003a0482c4001b40800d0301803034031403200224201007101c4403032403194000e0072501d0618000c51459101c451007a402c0b9a04070412034809443e107428000c000b01080d0041101c45880a000200002540101c070400b14240081c4000540d03596040050402580103503400741c2c0d911082d1114005140400d4240303410f00c41011000d000d032020280c40e0905640c03641600090702e00c40c8010700c510311700540580319201e41c000000c010030140e10440b6440c05003800c2803603802c0da071100482039510840150425806a00411040042410320781041000180c6130500e980c500f07900c50f03400000613a6400502d046540f05c01c01403209035a04119529042064031000c113600c0c148580001e0329000e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 197340908 1250 197339658 197339663
    0x1c0c0b0609070c0b0c040f140a1e120c060f0512010603020c07030c090207110604060c060515030f060403080603210a02030906040e071706090a09080d020703020309040608011107 78
    0x42010001e11910b0044070018080f5400040c11103003490310b08140f100c664024010500d00c20b4641c0030004405041c2400f0307801c900380003480e0542d0340e0f04050560080c7d20071584c10224200044000061f041003c0000b001c40c0c501941030f0081e620f0500c60083c1c0300c050402c182c0c0c41001000c010649080c0c144100c16410742c1c0d00d501d0003507038483c000d40c1d2a40c41d150343d40e0000f61000c0110311b80000c004405500428915228081e448401e101403020408180103c0c8228404074081c00c00d044000750040d0b01190b41b1000115190756420070309404a4038100e20700c0603a0301c031035000c4410320062540010f001c1c0d0340950214000c0507000d420b17541e240002000348016440d01000880d090101600074419581d0081c0041c140a4546980c0c8020301c5010600b60781034004514541485410030031706419951007a00c000d0004030140d100c4442400060410708010b5414403020301c45003103a00800d00003002241e0103a030013076407915a01c00c2000110703440c0d0317849039201ea0300d85014034a901a41c034041c1c034a030705d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 197342158 1250 197340908 197340919
    0x103020306130312020a0203190801030321020d05131401060503030d0f14070c14210318030d0c0e030703020108041401200307030b0a140d030c0807051c0c0b06 70
    0x30b0b090b00c2d040d42d07420040c0d00810002400480c0303480d80384e80d0020162981042031071003c038103041003105c15142c0e14420301000d0001500c28500c080082c0000094144d0f00b880c4680062801c4404840907045540545008810400c02c11180046c040380c0d4a5a840e880103000c0200320f001c1c900400031b903991007454084048962282d0104c2002c6915a0040c1d49000c00c87e4080d035007e00e8180002441820701d144212200541112030461400b00084c00d00704405000681020b03d0039404010001c035003005102910201d080c042210080a042c000f034030002c0707800c581c08181c02203642070227803680184070041c0b8041e601102c002c00140c1c0c0e014030740703039003060304009041407840400c1150f41c00f4001440070180e4215103816141264410b181c000c40c41078030159001c1014511110030404851a180f0681c1c109170140340c0310b00046d2503d40c4400f40d5080c40f80c10b1200310002c0f80d90b50750102c0d80200c20203580030707007180c20445009000c0b00c00015012200b0b1405503c032a55581d114805154007400050103503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 197343408 1250 197342158 197342191
    0x504050d020102160b0a110d0c0206180406030b06030d030902030606040e070b0705030d11070317090a140c0111060c0d050403090b12090c01111506150a02010e01140103020306 77
    0x1a40248201c100b40072292074000aa13940320b000340c00300f03540100003860020f250f14120307103074038200413407445100b519a03681c66580f20200c0c6c00b0490300f500040343c600d03500011071030f14281d9591a4403c0c500214032801e50001f071403415204150808110b40660001d0500341040a0016a0041415944144200d078000340c010455000c261500020741c0040d4466000056a0710500000001070b04442404e043c051140051a500104042c003400380e0050216000d004000741101a040b81c981e40b00001d10100c42001080b030703c850110501840b05c0c0411034103c4c00002581c2d59201a20f91107000c9200000e1801d424040270ba55000c2c4140c0007420340c1255035401050806120b6002203000301801c2c6412503d414000c100e904280c00c05662020700b51040214801c090f500800030b049050301c218024049910400051100085005081c1c179030108050350051503211002000d07100e421266400010b80c81c600c0106942180c440203c80d88001c21041c00401c0117a800040c02640020103070840d0030b15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 197344658 1250 197343408 197343413
    0x20a020a060e01110f09090a091112160303090801050106051309020901140307030f05060312040b130f1205060703021e0703030e010203010923070219030c020301090809130c0504050d 80
    0x40ca015081c1d071319440e500107003081c0500300b040c02038071a11000315040d80a9490340e41d0290111160381400410060f115080700c0c41902e000c1615810507640c0c0c400350f51418440c80c0908032400000d800460200c0c8a0400c04d1000d42c6007403048602410040c00e14504d0301d47c018031024904101882500d03c62a0001a01a626445a00e05a9101203070804490b242e00b000d90b0083e020b080301c007610b480207a00e400e001130550b00e0001000000c81446102c803518007820040d1182059100701c0c0b900a108501c203200141025803507030404014580310030f104191003601d1614030309000002d042d0004150040c132074504c0114044003140520040c1400084c1c3e121a10704c1c081d0040d000c280b0929a0552003c800041c4112a035002100e100000c0220b04440c042905480c011007901a02c1110060b071114071200d004000030900224051f019007001242c40e5030660010b401e6906089007101c2011001c0344903041e500f001c030003145c40040c4012050080da1384c641030080c21806203206191281c0d800c503009205 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 197345908 1250 197344658 197344661
    0xa081303120f0506040c09050105190c05030c01140f09150402010c02090c04080727150e010315110c0c2101050a14070f020c06090411032701020a020a060e01 69
    0x145180518018842142c20103000d000810003140d0b0903000d02c0c1880d0801105601c2007114100780c2320144c50b6a410a031404c0305100c4d0400b0198000000d100c00040f05801044041005e0000800443c002081710b0400050316910be00000c0c003152040a0840e0600480000204e6a43d2080f0719801511a060b600c0b0300040301d800c9510b02019400a500c00300f0711904004803402802581c00780800c8031041a602c40641c40c00284c2c80140742c0b0741e809516501855592940c100c000f000003c000d686148548a40051440d200e00ba841100c040c4600d00014a8200c558000c04001c5807040c54041d0034110020009611071100e01050703446030940805a4041035000b80c80d101c841c4004c4c01c002c109503d44006407100a00c01c2c002c5081c003139440000041c10007841190a03400d036240543c06032060044074024400940c001c00280f540c4140c45400c1c01a0038492180994400c100700c14001d0110030103000036100310111902c0940f550390042001c0c40c00540c0000d400d81480e6803010000404000c041030450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 197347158 1250 197345908 197345927
    0x1d010e07030f15030309050a0b0412060914010902010906051207080c0c0d090302040b060301030206040b0d1b0c021302130b0c031201080d08010e041109060a050a0621020a081303 78
    0x1158503d803070754406000003c40b942c002620b209490780760030b032500c075070412110714200d114080401e182008140310900200b4000e486041c444e09006c07841c041180e803109410069030f0301d200211f0f035484611000755070f8800c5400b0014225410701c940341000482d64400b2059004041a09101c01d01e8081082d80c104e01003160b401e20501c0c0e044c0c543d40c24803d10010700f4540c20f44000c1e1310031828003110700958a44141280d040700c2c0c1c020702092034146005403880d05500040d00c80d20034079a03240340a440010b14040c01c00703241c070902c3d03640b10302200300c9104100a80d001e01030920300281c03041c010032500030325100043c2c4c1550981a80070341c60780f050052103442e500c10905030000b08088035000190742c250015900130801c8550300d40d060f10f6038a66000f500b0600c02204c0c050304400c2c48040016913070414809032600040090548000581c460010032800f00107984513200142a5030070341c03001141c000283e0030703038000f4002c400c0d403401825100042048501900e002441c402c0e10441c401018022901c4c003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 197348408 1250 197347158 197347181
    0x40e031c05010b19110f031306080603060c1b120304080a02010513150b0609150406090614070b0406021207020c01140c06012706230607170c030408060406020c071d010e0703 76
    0x22070340d4458808c51100001840e202c0d090100700440c0c0030507824034020504502c9807084036050303800c044030b00e100071001801d2003a0440c4540120644444601180f5008601c186d00900004d80d591000c1c00000303003110001840b503840c004417403500c42e00290310100c600c000c8110180c804105402080c0c009081445024406580f12201d64000c0100d80001c070081c200f00c4a040e1103918103a0369582003907a2282a010103004001d0040081c0c2c13001489050300550403502072000181055201c8501d036001e80d0065513441c0150f880010034000640e40114a00384400c2c0444900d401d001c54101c00c43c0d6101c42c18041c44a9203040e01d04001c0a102256001e21250b003090174080c8540766903080700a14150000717584035041904500d060106041210031901616400441c014007010500011070254203c60510844c50008100000311004100039840c060350040d000165a034038a030b0780e414a010f02fa07a0108008484160780d084d003414855801c5030444040c4088031560741e45540c42200203021080c0d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 197349658 1250 197348408 197348413
    0x15100509030a05071409040f0b1305010926070804030206071707120905010f0509041a0607110f04050618091e030c010c0e0618040e031c05010b19110f 66
    0x40003c1c40400110320b8210b6000c445440c00d210640d506000c0401c03c01ca402510950408500500103962018660350201c01c0c00310b0b030101c002503655141d00f0366541c0c0b14199403005040c94461090030850480407203158454510030b1030021781d0341e1415800d0040b40f2010b03220b0742010130588140b080005089001d050624106c680c0c511152401c00488a503007480180011050f08c00401c580d4015440104800031984486003002614010000901801d1510b42c0128100043c0c0c61880c1d1205400341941230701c592540304598001100f8480a5040c400044d40300e18142814896691907016010080c640c3e03d001d40c1c021540d401010518040365625a103000c003100014002d1420808005440c0754180d10b4001d00c2030801140040711150114802c00e0b91050013000301501c030101d00d4144682c404005000403031f0750104214101d042d0780140100c20080c0e5100d4440c68482e04c058441d050250000064090500c4003a6000550a450102d006020b00c5076000081d103625004000348200e45002804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 197350908 1250 197349658 197349673
    0x19021c08040303080705070f12110709020405040b04021e030705040302030d080a050a0501030b0106270f0815090d0302030a021204120306091406010807110708150f1510050903 77
    0xc050805602500c41540050a404c02040040b0b2043c1d08a03024180c2180c101c290104098032054010782640c06c0440600c50b8071500c100002d84140500c000822201200503110b88c030f850300b400103aa2100d4112445140b0401c0f005000c0e16514000084480011506131707281e59940e00281c865102e0742d08080c0d414070892185000c8203601030381c0e5034420b00c03542800340699291a4030b40300581e9400c0c040284000650f00050061504ca4008042d140041500e0900c132401c0d08000c4100f00280d64012244032030f05d04a080c00070301c10800c0f0300448001d0380c004c01241803403e0a0026203401002040604140e0004007090074941c1c188c041d1010b1a2a9070703a030340b006040070b2814043c8001100300c10b0740840d080c0340001401054920854850300200d02140c13401d50707981300044454543c01000901480500c0c0c1c2401c00a0f44100070880c09031801000070700340d00b1928000c40904200090030300c1c003c504030004002001460010074049024186d580104144c2c00c52340135a100d0084280c2240c151207400da = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 197352158 1250 197350908 197350913
    0xe07180810020a031d0a170d0e0105010608010510080a0f0e1006030204180f020d03050c1209040f06152a110a060203120408030627070210060819021c 66
    0x900a100c004541e40301041200280d04290760b05c0d190609030900b00d03400140008020540e080b04501040c802441118507052030041018111180310510f540940e41d204014040da6400100c0740d805884201c40ca203103a10309800c001801014010055012140c13500100421000c8176040380800300c8252098480d85141c00b40204001c1003e0311050344502c0c140040001c0c2590f20302802000c06411030004075000d0b84030b800707001109090380780480811030200043e402002c001c2c49a1480c200c8a0984503946005203020882604c810220b0180000e2400310100000461444080d503200881d080c1107a0cc03002300980e041801020760903010b11044005c2110041021500001100082c01ca4042e12150f440e000b04a0352030066003140c480d285090004100418100809542e1100008000c603440c1c003003030b09003031442454200300103412408120520280039010301000411881000003000b5a915100e44141c0d40c60711101030041c00d8240b0340900b002d640721a1550b4005070620400a10711403c0340c0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 197353408 1250 197352158 197352161
    0x15032901050403150213050f060403030c0206130608090d05130e060301110a0e15091c150c08041e05031903021b0c100302041d0a0e011506090608010e07180810 70
    0x480d000c0da920300194408a41f030700d007641d4203025210001e041182414211342e0269045510098280e03400725050040024008003030320814007400407659080c44506281c59298940350101e42c0307070004e2004c03d000000c400c101441801e03048606e076802098158032030328042401002d16081c2241070020001301e00311a540c0006074000c25140580d0504144016201169410700540c41060303400340c01028100c1550100c01181c00c0203c2c082c00b07241c41d0035107061403000b04640d00401201c0118100108000c144446481d075125007044c00100d010100e4500e03502c5036242d04c40c006c0d00c070007001140002c4100c168400d5042d03a0100e280500f022540c1d01c002c0304081d60ba802d9064465109409910b00045031724400e000b038400b1210300e040f0065804007100c41141c210880140a4108a5516030f820f0603541400d000e00c501d41400c003205140c210b07040400080240d09283c10010500ca408001040f20f80240c1041a5010b100c500d080f4040c150402c0c00d0f00f0203484150710081f400e108808010140211a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 197354658 1250 197353408 197353417
    0xc050613020d15051005010201050108070b070c08150a0501080a05120c010b031605091b090609040219030e0c04060b09101110022205060d0e07090f06150329010504031502 75
    0xb011445140301d40e00c6e001207003a502c00f40503805d00c0741c1117080100040b800b40c1e009008240c2c403030718409251503203500c12540b5021400c10118080e0b10f4040900c050400140b059901612030103004e885403081580700d007603460003140b41c1d40001c3d01d400035841e21440360070351050103404001810340e4822144601e00004144a5001d450f04c148109404503150b240b00003102d1006607501c4450030304241c4c0c1c1c4010000642c10140401d60403d800b040100c084244005901c0040112501c00103885164504410720740941c0e0910302e4012890b1500500042c105481a5100c0d04011282c0e01c40d20014071104540c1c0c0e243c1a1140401072040c2c1f204418502c0031307a00178004841700706100c003070a48880c11040154101a1040c10307004081000080181039103074208000b4102c8001c1210603140da5042d100c3c0c215042181b8121000390b0300d140034031440701c4425105850030943c0c50280080c01c8644060100724502c1c060f5408582506030a4600c0d59000d10305440042d40c1040319158044440707d80030002c2e501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 197355908 1250 197354658 197354671
    0x21020a090905070302070f1502130e07090603150b0904060503031603020607030b0f010f1e0309050c0303071e0303060b0d1b0206010806181f09020a060c050613020d1505 74
    0x5200000302200c3c13280c0300784c985954000036911580f90307441d256012400444503046074a181c080001c0c10000c44045503000003071829144910040c07411040052280e01c0a80024040605001c0c0900c400b20325540884207984000e5a00d039a00c0030b480001400a0002da44017070f03018040890f000b414041e4460004402500a400341c81080d51200d0040b0216400341c07200d26400140c0c5208602254414025031440b0500f508200514513200c400c410440180822400c00103a102d0031000c080010602407c000010198029410982d0303035902c5400304044c101c000903c40981c0300901d170615110750080d500034002102c1903651307004001100c0f0050030a800034010480c1440d80d4280d00030307100040c0c0354121010540a000152207028106401051030b0408d80300b1840f0b81441c040d03040041c0c8541881a8a42c048006020800f44c414002074800550050050012480d50000800d82c00704220751302c071414a80c9031000c9062031000413401001103070098000c90b000140901c00300c200c2e9210500030036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 197357158 1250 197355908 197355911
    0x20714030a09090209010f0503270c0102240c0a05070618110627210f0d08100324020d0e071401020307060b0f03031314060a0f21020a0909 61
    0x742c41e14140804c2c2d04c03507041240e00003410a03a558200920520265420411040c01e40c0f8810241040a1030300c5910355580d015250054440d8986a680401c040f03c40d0104079801c64090030400c44911084400040c0641403004000480c2040540b00b4800ca40c00e007640044104440c0e910f00114500102c184c1e0300454182a19410040103894140190f8a00301c520b00c00c1d1081070414440c002c20800501d943d0181c02040d40c09111241c95440100204a60f040400418240c8905000c036460325001c40c0c0b43c842030051000503c074800029080c07020580303421105001050050381801444d611001c922422050300c00f01d003407801c4409a0304010100c0550b00112200140c071040d15890074100c40c0303010743c05607004001c004001010798000d2145514014040c080c2c2200003404603003583e000da41110003080c0306400510a181c1002d510860246d0140d4146044c00c541c200c000c1d05500c0c429020034248030000c03000c20315403420403400d5010311040d01030540d102c4086000c050003040160090b5502d49 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 197358408 1250 197357158 197357177
    0x3140c130509030d0b0a08030d02070c0906030221030d09030c060b0108070c020d1e0302071e1a0c070906080d0e150307050c0f060103030c14070e0105060c01020714030a 74
    0x11403038081c450050081202852400300c08000368001404035035803040d009000000d0004a100040c0007030a00030940e204c0242c0d4078040c41c6001c1c00000041d81045400070b04d010300c01c0c005031301e0346054064940c0c41c4140b1006030428480c41e40d882e5000f040c5000c0d1515041000301400c1507030006203001c100744603000c18004030381e0314801501d200342e0481c1c0410000701140d000c0405031900803111443c1d00d0144a9040800050200d011040d1414950641c09030340150810802c0c82000c2130b40300030303075000c03040a050002e080843c2d02d564084c1402c031002c0840008511324103110f4040c0011001890309103010040b81da81c49105070385503003c810391600801e4841d5440106414400040c403010000c4075403992456803400419142600040f801040c248034040303001d1694141000300354080c50090b107869416820620704030b40e00c040c00b40c41e800e100c1d8010040401c10030000d15038890640e10200c840c0c41e00e4440d05011180280642500504440a245a40c050360240840100b40501681d610a10321 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 197359658 1250 197358408 197358439
    0x3070302060f0a02091e01111c0f0306030209040c0f0603020a0e091e01151d0d08210108011b051c0e100f020405032107030c0f060c03141e010e0702010603140c 70
    0xd40b450800c05122484c00302c1c0c0b90204461144282c00c4542c07044c2d0030003340c1242c5940200e01c420b401184c003224040b201030001c0c8940e81c06121881c0c0108620b00c0c055160011800700200080d1001101c00d0084040c1030104600429103403250558410020342c0ca00d00750b035102ca024145054047c03000f4041008004940d160a10320304082000d407101a040025003a00c640e40c968840c0d02200284c1e0f100da02d0110000c989020500c0a9802404484004191000c00141c05026401800e107103106000c001c000144810040e950f180380403440b2030400107004401c601c1f0040c00e2944e918a03441c3e01c940b0b4000c1d58010307000c0650240054034001d404456948013400c0c04000d154498409000c100c1c80c040c0203d50010748a4900e074544944500f42c100684901c5a481e6015640041c0500020a4850420002c0001405500c030f5001809110040180400301c10a030ba01c0d0b0fa060146028a04040c0002950907000f50800c00046a02048041030280000e40301e5445101c040c2503203201d40700003d0345015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 197360908 1250 197359658 197359663
    0x20a1e0f060f1506140c030f0a020a0506070f0e0f040f1103090705012619021809070e0d0605091e0607020f0d0e010e040618020d0e03070302060f0a02091e0111 70
    0x340c401c2c6441d45c1c0340c00c0c1103981120559801003404c0040f18401003203490514540c460143c03881a03011b400603c44540c192611904205005256404001e00002d41084560780030000720981130058480041c20381c101d03804135028003848144d45100c176042030480d903100c10a03200114410188102582e417400d444500442d207605402c41c1900c21b030005594021841d000d02c40030a6040103512041d41042c2a48141c0d0701e060380c21645492401c2c1014190021150501da844264403100c00d18028403040302480c00900c140c2e44c2c2a1024020390303075410000c0c0f9001400c2010090307122442500c484000b401c2c0b1a0550345040841c3c03143d006000c2c1107034500b031040c00002c602e80305034050b1322180c0e605040c3d0001151040c030020600366109444200020380e809410b9402d6a0420a4a1015a8920442c1d10351400d0300c1400515400c25802001030750042503000c21000e801184400080308e0b503884010258000e4001c240c0d82c00d5104815034008014100c903060301c40402d840c2a200c22844603941ca99094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 197362158 1250 197360908 197360951
    0x105010503160306030f0f05010f090c12030c020604170d020102090a05010e030c0a0314010e070807030303020304080f030a1d03070c0506090411161110020a1e0f060f 73
    0x602003803003031001c55200661486030502c84109480c000541d02e80e241c45190100820300c000ba00c25805000e40d107010300600303001d09034070905141c0c1c05204c0e4040a6403555002131041c481c1302c00040301003180004241c41039a40195880c0c004212503202e0b611554111146180034100d1281845a070380c540c2d94150044c000e80c0c9140a00078800203802d40b03400700556007415041c1c4125850f02650101e203030039585610031140594080d40700e9420f0100000f20107401c49082d1446070300a580104010490814002441c5056951500c1c0250b00c81d1628585076a035405000b44c001850740001c4100110912070740d000303c0719244c9030312001c070750b10180b078500030303200e104500000d8015404401c05000a041c51030017003000e094058070009409101701c01d42c0d85a500a9000240c0c1d540c0c41d00210b10511894120080102d1002c40348416140410b440c060750314209403c00401c11903034821000070048029241840c21500040407041e02407a03032814000274031000030284c00640ca0054603001c26404c40d000031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 197363408 1250 197362158 197362169
    0x60c0c10020a0b0c03130609030c060c0c0206190507200f01050705030912031c15060201063b01082103010605070b0c0918010303020105010803030f0402040b0f09070504090506030601 80
    0x843c0140c0340d210042c20f10354402041d03001a11408060310001a2042c07140d580c482d070007a51903c111203800e240c01c5c402d80d010203400c1c4040100c0703006150050b0380e90307800300c440341c1c0020f0f031200410301000c3c80162001e018464015146840210125a0b9140148800200c010b42104d00c0f542441c00400195080c1c041d410002d8440c2d4800d05c2044032504201e4106a00c00b6651011281082c41c1031140070f10703440c0c802c0c0c0031240c2c440c0c99040154a000c2400000c0707002c0c003564002400078608100425420b4400440780805030203001201c0d51982c0c1e142906640d00d6011040e002c011580c540f0403990b691411114045024a427590309400811449020b903816280704d643c07402d1038080c17203488007400d0b42c0000c0e03c0c04948030820080780031280d4541c1e50001c00e0340881445460b43e5851750038040c0c2120416480000c080e0010820090301c4002c00421a5225604071000a028030710704002c2102800c5240100d90007000100a002e01e854008000d00116020398000740318503583c0c1d0050544412007807040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 197364658 1250 197363408 197363423
    0x206010f06090504020c0727050a02071e1a0106090501020607140409021c020d14180d0c050f07170c01030b0616080c07140103050a09120815060c0c10020a 68
    0x74815444d02c1d030001d1044101c4001290134040c0c94010781500703a030b0031105600c591003d010242018445a000301d56105074183c1c811800c101c03c0f41c440032501844010f6a100720001d0a407000100160b03004202d28201d00d44110078815a1030780400f400141e058012640580328010000355602e110b084580c18202c0c48004440c1400e14000151740a50000c0100c0307555800d213102a449081110300c050710412074204000710711040707072a51510704100e018280807644100e0b088a0302c41400005a41031a4600c80d10b41080c007400b0390300700382d0b0500b031805070341060600031114001490f01000900240c014a41c100381da105051150040d001c43e00f02c102c030a034020b01e00303101134041280343e003400c1c0c42494015101c45240050020195040c02c08a07004408943e1016508000d40d59041c8a2180c0c8810104e03000c2080c1c034a2502c85040e6001c1d06078109003085061030000320480c030190b8942070042d02c06000603484414a4907803a40750101844031a010715888c1c008040c1e201d2001900d441d405420295 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 197365908 1250 197364658 197364677
    0x303041205030903040b1804060f0b07030806040e100501170a26120709060e100c0209070306050a06090503370f08030f0915060f04020309010608070e04030206010f06 73
    0x5080e01c45400041501002d80028807001820301c0640000b032151644002055012034200000c02c000c0744d00d1a005800082c41d030394004c0c410f0400440446901c40d030582485a51603560070000350180400380d400416034054a940c410f60100540c000074162080c551481025103803071100640d1b240c1482101030020300220840245e0403000509002c05002000001803512600b03011000501d502a2102c1c070001d5170400082000c0f070783c0700c10f2080400d40200c80c080340007400d0080003400c803604100064414107020000c522028000e90180d030007404051b001d410115514400640214000e1090324024003c00c4c4002c001c050300e81d003c0720440c00400f01c030a461042c1003016510100a81e00c0c0c111244007100705568081007425020310310590b901c500c00207039441d000c00260f041c0586010350429403c0c0560a01c491035651001c0107184c441d0588005880390b54003402d040c00b60800303a2107003c150088840110b51a003040c0314061180740a07401310781d5540d9a9501d000364800443c0f01d02c4c00090007110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 197367158 1250 197365908 197365943
    0x30c0909090c03060c1209150a0b13050106120e030a080f0c0c19020f030a0809061602090406140f0105060d240602160e040818060f0a0201060905010503030304 70
    0x5040d908031040d4000c8070250038908020a240102c00d5410a282c41c170003044428184014601e525030000321000500003480d51000c03440c1e6840d90141c0880043da0301c484100076191150414100001c4049405001c0e95a582e00c01038105043c1441c0d4010041c18001c00e0540240000200c450305202942c6030389260340c5040d04c00a0300301c00600707069184407041049440c1e5201c10810219440d80710300060b42c4140c4d003841002076907105140b2050191b000f40c0301000104040c48140c03200280140c8415540b0364500705c60303c103e001000d400950042c204070a1006006059101d000460024800007140f42c540250b40c41c2d04c01024861103600440c00c210581c01d444143e001000e201820016140c4280140020001e16000342d811400050b40507044540c0b4107e11002d0020003048035050711151030800391120039a500c00c3d50103403d4040c52000e502c501c1ca444190071244504181c80d2000d840d07010040009019014600c20401d103d4200400032a10b880c002c022203008030351220070f0000110104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 197368408 1250 197367158 197367169
    0x190614060318010227041b0806010203090d0b06090603061003170405090f060307090c1d190308040f0e060d0201030506030118050304031509031b061503210302030c09 73
    0x805021014212000d0b80340d550809001404c5650803c1c9524200251101c003034054034800101c3c2c4038821303800c4c1710074120311020144461a1002052810b50720b6070342c4610050745075208000810340c00c08044242c0ba020b00c07252802890013054120344c080010b072100e20401d6a950420340d034040c0719004442c010000910b9000744a03000d44404c01c0c00e42c0c00e003592040001c85650b4104c89000100c3c02e0001040203074030381440309101428900fa4200300003803000000030500c5c81420fa98081410244000740490340d40c0d01d51207242e05040480140b041622071401425540052203540030000b00d540c40401c004200d076044503c40c52018000828042e02600110041c0c1400380040e074146d5a02e003014201910100079601d80b880c042c000465580d4030314a040d6290402c0190507948003031904c80f5581c00654000b201000303c034103c2000101c1c0740c542d1b0421900a0500c1200c41e80c424a01c02400000c2020f80601c400c0749421001c000d028413902c102c3c0580c142e1004480d05091500204007c140b646043c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 197369658 1250 197368408 197368411
    0x90f05060d0206190309020d030e0405180d14040905011203030e1c0e0d0212010c112d011b120f050121030201060b0a0e100507050a06051306141906140603 68
    0x11740b40200e202c00c2280c0100b1484580d90b8030031340000e10400b11084403400c0078001d4682002d0810340c1b2011400c61010341d02d807103950a4245904000c0071000e09094490740806035405456003400404c400d595900359613021109404048011904001003107200c580c020807654001184000030000700200010200c41c0d003280100c440303501020349140c0d040944c88050488000e01c9810700009050100e00b44040d0808a00300c400c2d070b515500528040743c440098400351802001c0b00c5251034115030030323860640c0c0500070181051410060002d07a10401e1980002c03030068217207a485040080c2002e0a50044c04e03601d0034022865460b0740c0d00588200768070045e12462006010f440002149078079003c2689041d8004c2000030b0014001659103025843c04990ba01281040c50414515099165035a16101c1d003411101410b1150382c2c1e030015040c80c60300d41080007590350000040210b00c0e070b400c2c01c694100c0c0b02a140e041049581c0d61107210304c00301d80d218100503034400002c1c0d00018801c40d010090654030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 197370908 1250 197369658 197369707
    0xf0a0203040221010f0f091e050f0f06040c09050f0615040e0c0304060e070e0c070311160f050411090402090613080601060e062802070f090f05060d0206 67
    0x100345002400f1404410461010003003260011420010803985d48041c3d440003401c2c1c1904525100f10200001d1740760900382e030381c1c0501c50280100402075040047c200b580c517040c0c6010500888000f0408203c0200308140300310721850241c0641d03030315840040200d400403655610b500c0c4107403012070420b14014000c1d908040b2848615440e10740c64a0342601c89800075207030303ca074a0030040f060101301301e00c80c050421001e44600040c5051032a141201c07010482c0604001074911000400ad018548070790200c200318580340c4100c1d000d405091a070030b4a954941c4c0700310301030340e413200a0125441c0380500601355440070403a4468100fa0410003048025400420400e501c9001046244203400c0d800c6443d100410030240681001d600d09031014294400000b06644161801c00a215040e91080022030620682840740c41d8412456803040e482d0001e03641142d4803110026000007000180303500141d80816078507105000546620060104a03000c448000b5400308040c0980003a484109139a2040c030308 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 197372158 1250 197370908 197370919
    0x308040213020a030b03070506030412110c0d0b0906180d030203150306040807170304021c02040f0e0c0a1403031c0603060c1710030804170a05010c020c03150f0a02030402 75
    0x20812619207049074014003071400441d440700c040d01c00d14981803000200a160541c0c2641c5189426034616444506034902c40d42400605c41402e41030707a1381009a215003801c0a4014240044241440c2c4400700040b54481c44034481c4c0c83c000740846500e030415000603250940104000300c2152000e602030b400007031203c00300f003606054a584a58003001040c0c061030158101c00d565004034140740c1d500480f140048804c41004105000c0141c40350540383c292010000034645100c5072500c0001d019002c501720030a020b904144200ca03241c8800f040e0040c0c002000c684c05800d159441c40402100c05082000c03540c15003052201390380103807400c0f0142402c1061f061002800c142c99503269011a4104500d00d00003e0031320707260403808841c2d500140c1d08001d198040544051450355034109500c50703801000403107001c4c5194504050800c100318000c0c1c1d0f80c0103009000c440d1902d00025034641317100c18094824420690180d00c0b40100c408118003420401c051030400d5550144188003942c4058422a04803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 197373408 1250 197372158 197372179
    0x30a090305070c0e01080706050301060801090902010e0301050f1005151206150c0a1112070b0901021e0a050727050c09040207060606030e010623011e080406150302090403080402 78
    0x24601c0c0f02d804007030001c85004545039414007040034542041c0350020000d0102c204014020140c002658604440c1c449101003144070745880100c409024030800b0703039095030801d024800d01044100c1014410214078203003600c02580c0c0e000300102c20700c20009010b114a02040101a001068041035620000c054515001804400c81580c0b4a0384008402030782d940204d00030307100300031010107040d8090600701c80d0307041e0044003001a5511840b00340304030054040c00140240441c1d00901c0712000709100b8070a50030001000d01c201940712031042d0001c490310302840b000070903000308100e003070b01500c20f440d40b0003941800f02c00e100c0f000601020700724425442080c0070075031080d40c07980002c00f00382e03105240104005141000240a8824110303046403140d0400000780000315000d00c000030584540c1d8080740d51a20540011380c0c0da61280207107000b00307154640d421000f098011100ad4050761140d041000018000340401114030040d00009512240e56400b20b07020a101c0c101450304580000c100c00004c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 197374658 1250 197373408 197373413
    0x302040f09080c2b020309040f0b03070b040e0109060b0f130e09010209030c0a1d13060903050717130e04171602030f0706051e090409150b0312030a09030507 69
    0x41c3d402410502410358483ca2000142000300c40001d405010114107a06036034450000194aa02990a005000b01d135a00400480404580c0103907240d0103024080c0c4070380c0c503110f180f802849e6000d805441900c00c0c3e40400040c3d070784c405104803021142c5081c00303941021580050b41c0c4041d07000c110144480d404541001caa400709010b071b042c0c01200d918000580e10048401454108540c00091502c203200c825400c1150343c4555030364010300c034050b60310310700c0d42e80e0b4100007110210100302d0f000d0302c5546003000403810103400000400140b401400045005240302210031082d100d80d0368102040d10394803c1c2004038a40080c00250407601c0360750149401d01c0900a0241c042d045100303940400b02c660138900095090030310000d00140070a40c040c1800504100020785a4404c038440780490610403248071301080c01450554040300b4008205220381e00982c20305150503885908603103075030703440d0115a5410340342c00114044d200001d8140c041c103541c1c2d4100c0e2040240405401601800001c2210400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 197375908 1250 197374658 197374673
    0x12020415050301080607020604030e010c020103150803130905070e06090f0d060204050114070b010e040302030d0504110906010302130303210603050601080d020f0606060d020c2a0409020a0302040f09 87
    0x1024805581c07655180c0d80b52a4981785001005803900041d9080f600500001c0b03544540c2c4511a210b00703003041c072215800d503c0124000d0041761801215402c21760004510200048010185240410f20080d0040d446e6240d103411101c050311880042090304540030000d003426400751003210f400620807041c0180c0301011400442c0542400c450311617001409102560300b04c0c405000c01d0000207a100d05040441d510044603250601490110411510000302014402c00031034010781d105500034051410b05151040c2001034505440384103102920025246500c60f100b614404031181190745000761031602d080d6a0414610b040f03400381e080d2611480c00d412668052100103504c5040100115850a908a42003286011444045400c0220050b408100c0042c4454000108540c101d560f0500f5100e084000e208a10400711217004840a403480380d840010b100c0c94002c0c0340c2107a100f00003003007c1004219a070208000754041c075070600910250820361701944800c460035100281c0c22607107855005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 197377158 1250 197375908 197375939
    0x317010e0406090c170d0f090e0103020607050c06120f010b0c030a080705220302040b040e070311060d09110f220f2d1a06040918021504090e060c070201120204 70
    0x421b980130750700006040b03a00000801040ca0149054403c0380c1c2000c600c0c04141c80103210280c42040042904014000c0c14000520f4061005001d1992086100c548659000e41220455444402d0000000e07012140200b00c626101b0a08060344c94011248070541304042d01804080400206004494215004044046141c00c0302052440107e00c0c500c1000706540d070200036103028a06000f50035a64600005500741500d40c45800d041d02e0843c8100800c107680540b1400c0313440c19007428000e100340144e485100b90320030001e8840c0c20b0005804001e011500d000000030030010201c1c40140e021707029140d40300d002c1400740c58002141042680c03803990764654201e54001080003400034010003c0c0d4651040340c89200900340c80b8070750111030500083e424005d40c490704000b1074484d00c80100804005001c110266170081001c3e04ca00490600b588054000e40290485989032540340803c505000610034414603400c980c65242c4401d4ac0d00440768040c03910800d44140e9024040401c00102020528 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 197378408 1250 197377158 197377199
    0x306061710030b1807140604031212110309060609040206030726010902030106110f07050108040213090605060f0105090307030215070b07030c030b0607170310090501120317010e0406090c 82
    0x281001c02c543c642c9a400c202480d40300707001c40700c610368004241d507c592003a07038110782e040703448100640700d00701041e190702c0d540c20f43c280e1a1602e48890704500d0000c100144d8015048041111000d54821040c00803010043d80e0180d407001d4144009050984a00c2c3d6860aa8604644d40300740e4240030102074440d80ca003030b0010840503401000500086a225007a81c0320200c00303600414000001c11442501e414083c0903040c1080000c00008003951642504156510100c03038007044244813074200780340103040a4903681c2c410003508202c030074107621a41c1980c1444400901a00341d03a4510382c05c009524885050240c01204140641c001003a40001c6a034401c226684010540c41080380001b812141201c0c1041d10a14090180170b001c10058103d44034091407020600b0340da070326010600c1c980da1016910808100d81854000300b00184508601d1096500c43c0d01c4074072121840079205480c02209008050182d4010300002c1d01085083d000068203900505c582003401e42c4408035550800020a0b89 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 197379658 1250 197378408 197378431
    0x31801050c07061103040c0306020901111903080709050307120609150e1203040308150103060f090204030b010e010312030b0d20011119021315060c0c060306061710030b 74
    0x82c002444800c3c0a900c00d0880d8906501c0d00e14074150f600e1081c81c030f43e00e000140405601003050fa00e140d000e0683c51103500c0301541110b85910009420315082801c4c08030840014645d100031a1841c3d00910300c0303005072030005016000e654248038070318440700c8903500c0030707a6415110780c24000854801c00c4034a602c010100004141d08888000581c649030380c81451040c1c15100b0804c110100303a2006249820514200c2218003035040b80d8012005050550002d11030035084600004403085154018411a03121341d00c08421a0390780d609103240740000744000790111600385102c14031a031080d8007030448014010100c919880715600c0e0f4442550f030603003000400003130900b0005032541e0060405415401c07488010001d030540054545048451410028010400d00d01d00f54141000b81d001f01c50811800c142c04115540e580c00001e11503800f200054544483c14400410f10b07034864010070060750081c0d29881c600c42c00c071601031881614001c000c2d40d01d181880201100242071a40320303500400e0365019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 197380908 1250 197379658 197379667
    0xb0706180b01151b030f0c05160603060801060f05060a030905010c0f110f0d20030f0304020a090504021008090a020907050a090e060a03080703020f03030a2304020a0b031801050c 78
    0x425039282051042c4003824410401084e1000702d41081c444150355600d407900c2c40da90085003405031400124200004c10768050050070381528007074240d42d48121041650144070b141d80c0c5032020f500702d4010780621000510300a60078020760034481c00925881069107000a1401241d031112401c4070451080030000413041c0400d004095402944560365010540c040c00703902000c10760840d940d401040d07100b02800103070510100c11803690307102c0030084854401500da07510101c1d0601045584111002c03881b5001100c40070915503110300c40d15104a50140088005d040c01220a46044d80c00502202051090314646401601c1d9030bc10389028031165120540c8072089074101610f8030f03102c0e170800350944042c602008029911303504040200c80c0c10116090741e90000e8203049040c500310030303d0b0305010b11002007440315401c41d50b80311030054003040710290404d10500c280c0b800d5a07203041d00e0103035226a101805001c1d13201140c00441c0c0040c0b036038881480d2099103c0ca024250354040341d40f410390010125 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 197382158 1250 197380908 197380919
    0x602061501030b130b03150f0106110a0317060619030624020307080d02091207050910050603150103150321210b0d0b0108060703060e0108070b0706180b01 68
    0xa50110000090809103c1400d00c200441d201c420103001034203030503460b502c02c0d14454509120000d038079100c01101040d146050031078058020b9080c490b0703200140c640c1a036412009000b1400d0b03d200b07a8565a0070b0292401d20480c0c00e503594015103a264000c208010103180710050909114000340180c9001c03c4d02460036800820704c05202890740240d480803040340600c0c6034080110340401e54010012178440d503010b03a441e0000d000d5169015005100c3c44038001c01c06c6000607c6a044031030440d01a10300d5a50500011020003162050760b8100c5800c1c40030400b418003206914400480626000030982c80381e601500701544207034019030b114180d40f040390703541e16051030189a0b03008550920001d600300d58101407003202c1d0001c204005243d650300c0c0a031020740c1d400c1e9403014169008014903416584561754540c03120820707585a00828030301030000034000d0380341108038100c444550142011074648a4003405a0380545000c8450079910100d07425000c40015010542d14003c200303603086903040a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 197383408 1250 197382158 197382181
    0x31202010c020c030c040f02090d031e03091e0203010e0607030902031605010c290118050a0603020a12030e030a120f03180f030c050d020606031e030a0e0316060206 72
    0x384140ca00b1900400400c0c51540c030300003407613518040d0070f850018024610b402240002d001b03408405a201c203980c0b48540515912440c2d407406503540c400060030540c00c040054044801c0144010080070003c814000b1070100150080d08150028002194201443d072400c0c0c20004111100000b0a60303403503020341035082c200500000d001d1400c4960185608100011349000803d841c01132a6a000f1841405910701c0c0b03154405100c60308070100e003410b50711049851401140f0444082140e8030b04400070f5840302e49400b40004803500074183c0060f00307050095a011290400500398103024408122490b503440400050190502401c4201d404640c062001010000d03030fa02800101410006245160710000b0245442c055009200b00108491464284c07251880c5040150150189182d019049600441e0191003141e04900f43c45106c1281c0c80d041a00c91280d14000c0200d51040c410044458066005440c81d41001000c84104074619980a0640346085e000500140c01403824882100c0a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 197384658 1250 197383408 197383421
    0xf12031302040b0d050627010e030301050d0516060f0e0609010e13140f040303050f0702060c1605100e060903040b030a0f0e0f010e0114091f0b060d091505160806010e060403120201 79
    0x2e1f600030b0129803c400d40541d0b4a0106020f0300307205103101d00340300c0200a0b040151f03242c00312001c1c200c00080c035514903002d001c04074644050300104030001d410071610302c1c00074122070707a8001c1610ba45294010300420701c484000d0340c0d596002d00c01d03540e08070760250891060000c2d208210400340184186031074503004040c1c0b0005420b0300c0c040c038400c0040c40a41a00880c40a40c0b15031407278130254403240710100d000c488903490100940980540741000c49040503d0300103a84018000048603401e0300c0d030f40b51450b0b5a00c035a106103114000f0500c085050920181c00c80840d111860b0700200e801c03070221900c40d0501c5001a40c00c80d803607640d1380c0f1420489400380900308540c50358800c0b0840c14640540d515884000c80c02c28840520105203a0f118082a1035015031007240c0050402601c50401d820301000604a0f40b8040d9441c40c8650100000740e1071901816205140c031a00900100c0c1c0070301c006651540028010906001c2e01c04002c1e00c0d542c1b0f43c00090401140120f8002c1ca00030b10501e0007900711100f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 197385908 1250 197384658 197384731
    0xe06061002070602120c010617030705010b0f010203120a0204080f0a0b0603060c030a021b0d030609060e0c0702150705010507030219020601230301060312020f12031302040b0d0506 79
    0x240104166500400c420a84580d10040d01d41d440482c00355140c010308c203d400c03445407010300602500d80c19000002420313589110380b00801c11655000e04000d0850409407403280160b00c104401c1804504509441d42c11035400c00340507041988038662141000c0f14a1026821a40030181080501004001c404e4210000381c0203000103040080700c2400506c4004d0501e0401c58001584500c0b002e10605c1907051800600d0540c1c0b03058041e818000c1c00350580344600d11641e818004046030320406400c000307020b0034001d03034940c1c5440242d500303012900d85286803030500c012041c40729401061080c064944a68030f9032f40c0042c2c0d40c51001200000c048010030880e0119400800188031400510140c220074404c100042920703500e220300000d001d000310b0707007005001d42c403001540a81c0980010f00d0000c146118010b03503a8841260303540c0255804101d41c49909035144101c0302d000743c1025400704014420141800c3e070b405081d5103a96107030000c00d07682c4032400c0078a1481d83c60306051200310110240c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 197387158 1250 197385908 197385913
    0xc08100e0d271e140112180506100f09020f09010c050f01111b06190e010b0303040f0609060206090d030f09020904110406050316050f30070501031e09150e06061002 72
    0x4c100d000001c20881c0358006510220756901c106e51440d10000343d084e0125507001d000c840062804c8000c04020480074421048600b403039420110304000b0728003ea4080302d00070b400150500c206030004403007100c0301c8074050b180390040500d2146001c3e020302820103500c08041d03407241e89016481101450483c034603200042504001d05110096100451017420743c0200f2340041307800c0303402c6207101707006283c0d001c0034582c144400100058103296424080e001c8800c643c40f0a12000c0e42c5090603038a8040c00c4500a0f0300e50000c0000b00305403402944503072030100071003000003241800745c0d012641c1c80314203031000d9440017810400d0041501e41405061b02030101a03025101c280e0b0502e03615500e0b00310300d005452180074038400403d102e40745c171607a5500ca400001c400941400e2004c40594203540c0c45006040390303004910010030154001e01801c0d45d54910510f2841030540c2000d045001060228012901c0301042c960071060000c0500806120a401d80d005d442d05003005002c203c0d03030312402d200340303000c0d074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 197388408 1250 197387158 197387189
    0xc0f100b030c0f04020c1902040f050613150e010305100506040c0e043603030b060a080705090a09020d240509060d030e0306040c08100e0d271e 63
    0x546020a5456a1042c2501c104100d54090000900039004401946100c0d210b62454882d503030090305220b14070580240c1d01007200140e08000d020940d0701c11146103403c60f1160000b400364140170f500c039a19a001c0400401c40450700d4040c081c1001c1800c0e4800d03034071584100080801541684a8075401203c101c0c1e040189601495010700191403030301c0114072031592200f101402c43c404131030040104041c0140c1c0705c0c031600d040040c1e005c10722602c4801e900003407802d200c6101b80c1c1880c1040711072080e0580c50300c00c0c40e943c804a08444a034071059846410402c0c03c000090a201c46001600b0803050074040800d85504070101004181b114900c580f8117136138801001c1010341c581c81a1150003c5003981c04201050007801c007650811000d45910b6054030580302080240300b469090031090721303000015200720300c0c4c0c20350880c0306941c0030103114599a00810302107010700c0d000e401c480c01402c0740d101500c40310008520f0341c80e990416640c080310110f240d08840c40d000b10092440000600400519990710 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 197389658 1250 197388408 197388431
    0x209070206250207030c06030501081b06070605040f0f0302071e120201080c1b0606120d021005070903050322050d08070b250f0305070f021c03060b0c0f10 68
    0x41122403501282c080b042603480600107071080c0581e03401741d9000425009800d90b1494014000c000901c03405209010b8400640ba555595814400340700000401711820115103880b050010107000c0d03c12100c0f0b1102c2122840051401d00c1d00c4c3d0403690294001e4642c10345807a028a58683c60b0a0b01c0d0310b40d06050040500101d2603440a10036010f030280303030450003580c5502100d0881e00c07903800d141110310204c031041051108001500d600c990701c1540d18800c0a0100518030b81e0fa52049802000560007080140f50010703241d60045900c200d00c0d1034403600456072903d5550540c0e03c0354240541c80d50100c12102c03d41840424001d0040c0400c0d01c0c0142d030203485480310074050040c40c40050051a1980c0450300140034505030510403d0040090218500b0182c0042c00303900000900b18082420030000611b0680140d005a040d98030a4010b0950003101420f540140041e11200c10241a981c0380081442100b00b4003404428045500030b007044580010040d10300500c13182c1441d201802c01e00030790032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 197390908 1250 197389658 197389681
    0x7020d02070b0409091109090a061407080a0e0c130b090702060403020604062409090317010807030605040614090609072c040f060513020109090615050c0a020a030309030209070206 79
    0x310345406100045d080140e1804103041c01c107002c003869000c940a0244101e542c0d0208250107400d00c0b86904100138170b409086203003410400c42c4c40201081c500c500140d10b11043e9040402d4208411050b83c1e8501400030005101c2245c074101e8074012555543c0b01010703410000030160b00151140020040d510b0160b030005e40d00c60340103000401e40e5032203c01004ac141d10002a8107501c1c2c01201840042d5a204c0306040010311240c2002d80000f1080c0a4064002807900c900506954018001c2c0c101181180c5821000d03000180040303c000d40c4d07809075021241d2403204600d00902d6250050141d600300b85200c62304d003107120782000c0000030031302920110310300711307081c08032401d480c0c50364421007130f0b5113904140b0080d040c064405000e02d820501040320b208074081000c0c1c0083c0c400d0b00c4c0d480c03809881d11014000c4038a107018605005240214881c1500e020308040c003201c0c0c00e0201212400d00d0b042c0c0c0840c00305015940110040b0311282c0b411300071403400042c0b281e070003806880280300610303060100e881d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 197392158 1250 197390908 197390917
    0x60b0d0605130605090c13050a1502210409090c0e040803070207060f0e010305130f05030306011103071208130c0e04030f02032a15131a0408030105040b041d010507020d02070b 77
    0x140c0d0300381b0000785400c11000c0c400952009080040c4034402c40b599400803401c0700c040381900040140a2111100c0c4010442101c1515600103031901c0d0b41401d09120031f1000801400c90107480c100707120b000c002802030a41e190b2511403803080c1d044944070305011501a01d0940540c000809010412035884181c60307004458441e82c0500b4079000c0340d145c0310b442c2400098004060301400e00c440100030f480502c01d001000314043c15081c0e030307800010030310f03500c3d1940c0300c1c040d00f14001c02e81c0c20400080c095043c402c40680c0c0c2c11001e85994074900202a913079040138400598421a201030312903041109060f00442c041c4c9052030103001071840e1000d0000c41e0100b58100006800403070a95000440c081581085400303080800114844814148501032603072141d00a001100c0607100c554810504588200740c0500a03030340a040f0504503404c200410010b018130804081e04a6030700c03200c03094100b44401d49500f0040c00e0398000a00d605000600900b0014454450420765000c05010001b80010a0803107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 197393408 1250 197392158 197392171
    0x609021f050f1e0706061509060210020f090a030c03060c030b03030702091909031d0d05060a02090310182112050604150305061006030528060b0d060513060509 70
    0x1580c0d4681c998030307400504403c410b4040440348007240b40d00c00c108042d0301c050107850203040b001c1050725650b041206c0e01000d5014103001600607011401540882e900506400f5010043c0142000c0160300400c0803005103a0050720703802c584035010010311659100d01803980d11149400d102090804010942d02d00c100c1c50000e0081424000050501040540c4040d810707644000c148100a43c50400401c18100382006c102c07100c604d4029050503147c04070018009552100240c041d40e1b4800f4603402c020341142c0d004582500840700c030050644842d02c50500105c14840c1441c00011071410305580b6010010222a5022001c2d40d82c0d1042c0c40e040038100b4111074048001003419619000400c002d091825006120b10300040c0780031040200104115110b004111000110b541d52610202c4c1034031810f9811340f207031220a10340c0c50382d0450b80726218510000412000b160481d034034500188503921404c419088150744030010b0095217045c0710418070303001e4040014020b090410f0002031010402a091 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 197394658 1250 197393408 197393437
    0x11030a110f011709010b12031305090c0c030f0408010f0b060d090303090206040e090f0d1b030531080106080309060306120a030305060a080d021203180a0609021f05 72
    0x1041c1c19a01c2080704084504512400c41d203d400c10040e030902a06403051514403540075540d00d020b284070000f00b81c42d0000266150b030140a031600c4244420308901400c81c40d1800340130401c00580e42c5e030800080440111140e04030f50758501d46500213003141c41b5100310b6442542400180307407455681b80e080d52010043d01d0000a00d800491505600410718080700030f422007000300d0005000500508001d1046480c0380985808030243d2012a4550b4004026040843d903c0aa070380113145480c08504403282c443d085c40ca00d02054181c0f070645c0300034070003170f2070f40e41440d018210021098020a09401020004001e0111608002d0950340724056000b41500503600800041e1550b91040e251302001c41800301910492501402d00138041d0404270f441501454104e42c0010b541800000c8044120265501400009010030203c15071648060018070900803a0340a115030500b0034004007520707511603503001a0702070380da105004504800c080c030b29008801c00707060b00802c260030030115070b04010701c5000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 197395908 1250 197394658 197394679
    0x906071223060306180303040b060d060207240204030803160912050303070e1f0309141504050d0f140c07030605010b220b070f0212160311030a11 64
    0x2911001426410400082459a045150100e80090381d000703018410a4059074440c0e940e04180f142000b0a0744410b8200d90700c10400200400e040080d0b950300a40020442184002e1640f038820991300080c01c1942d502c040c030410388403501c440b0002000001550601075060902e140c41e001038500006020099007840214120300c01c0c3d1003582020301078800ea60081e1210a001d00f0500c0e0b42c1c3d00304491000104442c1e000d4850a807900b900072900c81b011400522507038400d510001c4000c0c0900788002c0b14509007100c1703645080304080c0a0941d4070b0010400d42c4a00d4940382c00c129240910001c038003010300c804180548401035106081191702c0c0003000000342c0e40c000e00501c02d45428413940c8003a11992070000081010940100100700411041640c003544240c220010390707520301c07180305584035000d04010a5000903219002143c0e018001802c10301214450210142000d01d40b254544050b03501c05018400c22a19070982e40030504241d000f000b540d5050754401e072034070002600a512503490800c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 197397158 1250 197395908 197395937
    0xe13030e0d02120609010b0a050d06020d0e01180201021e060402060c070f0611010b040c081b1e03070914010206070809032a0c0118090506060705010e03030402041103090607 76
    0x14922502c0c0d010b010104500c1d8030440c41615018140c1e0b0b0605079501781038010580c0c0c81c0a0791581d0507200014468406100b032a07482400940c00244088200c43d1a1248103455070300a01c960a20755102a20740150540607100080c01c05070a04286420702e4030741c00d01c1108060300001c1065000703505840440d1354580081c0024540602607102c05641da51065000c80c43d10751050340f041301e903001d85009019454103034040100703440e0900f001000040c0420300040090f03000301400034821501052861800c0c2814103440700001141d00072038840c010000c1030201003548404880010f0142583e881b01c003c8400000075103901020301181c00704500070000c0344810006100b190b441d50003080001074540d5004491001035000c01d001000b05004030000b809155001f086020103524403000c0c6503081c82e08080b1303c4401800090912900710405000000000c2c909104480d0b9120078000150f840b85071520401c010340c0c4446106e80d40c03025081c400d10640d0b10300014166004000c5042c86503401d507600c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 197398408 1250 197397158 197397169
    0xa1202070c0317070b0a140a05042109030203030d090311060f0c030a0f050709050a0906060504120302120d06050901170d080a110a031b08060102070b300f010e13030e 73
    0x4c03e0142c03030f41d048801884070702001ca602c001e1044000c0100c1c07481c00c1d0f40740c030ba1070700489400703d034080e012084400c811000c0458400300ea04540b040d500b0150016030310f03034011900d1600f03c42c41400b003070740d502c03008a0189900804540da0110710800248000d180c4280c6c0f40c020614040c081c800141f10100129404c90701d15000906001d0004c003040000d0703e0031200040002a03a07102d841d0003004c09081c003148480850103102d06a546548a21b403405280c071540181e5651600e80070780441c0030b0b203003040c0c616504440c018940140c2c4070b07502180d02c03810482003044049060340252004150070010b010050000300c1c6a0004280900304402c0c02c3c1c0d42d0103540c1010b000317087d400c0280ca000010782d008007503030503602080342182c10b00100d40c0706901c4031000ba45d41d09400d03200c840c00369200320010001101e041c1c008080040c079242802c562a054076100d003001002d10351400f41d004010008000700720b4a440a40c600405117048401d05c40e040c42c4101107001c024a400103003c0162407403062001d034460 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 197399658 1250 197398408 197398417
    0x370e0105040504050c19050c251a22030b0f0402030106030b070215010905040b0402061308060a020a020f0604081c09021c03140304050d0e0301090203120a1202070c0317 74
    0x1401c02d2010785400b141c5d0400c950301281c003400c280c00c0300c50120300c4032034481ca0642e64446010700c0100118081c416644252100840c0180c07641c000c10840814001c0c0040030610b070140c0e04076041170f01c60394141300001004810200d42041021a03440800c0410075420249401000007800040c60f0344480c0003081c05000660070203052400180140000c050340021300c00189412600e214000c4d0f601c45094200741c2d14159030140c908462000401e02601e0b028005000301c05034120703000d500d0f541d201607241c20418211000b085856012505c1da5451b5014440603110b948070b1400b0780706074a080c1e0344180040c010081e2444900413402041140c50314298004990a47c00419a00842c2d000d841c0300d1486100d2510200d000900e80c030011041030052a0559001700c6e030080c080d160020842d142181d0103503840007100e07410340d02e070f20b260f00250b181440500c1c0261441e0300300f10f54071000740c0800707048201c0c8140c60807140c030310400c0780c0004948100303002002e41b90b01081d460740251200600c665203004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 197400908 1250 197399658 197399669
    0x609091214180112110406031d0615061306050d0e0c0a03060f06050d08030a0b0303070f0f03210504030f0224040c030c0906050406050f0f0114040801060b370e010504 73
    0x21701580e800407814a44082e00844150707a8060007400c403004048444058403c2c0800020b0f801200480c02c00c0107100c1c2000c04501c009002e40d820028014024400300b00c4950100001c5000020f240121a0f1940200040042d02c0300050014950041c0841d0300501a0310028004c40e07580c80802d848550316400060040100600500d02c20040f810404170961041c0e070300344002d601d86581c04040d0706012096808840d0000c070243e60403296034640c0c0a0911703545030210304000111603440480d500b00b030320800d0031012000d800a6985040d00c2d014244070680700414007075500407410001c0401300c4000e118030016801007403078106e444526014412003e603800003040c40ca4200300100d42c6001075072040003110000c48042c448181d654013441151080f22a0003600071a44901045482d4091070b05080e4012082c00304600d000e036162045400c440c4290056a140c600c001034a1510004010240e90280780050001106100808183c0d0094111628080900c10210708160b8207038011000d4400070032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 197402158 1250 197400908 197400911
    0x4020918010e1606021227120f060106030516120b1203120106081005040203070c0501020a12050c03090a0b0a0b0a0e071d0303030c0c010f0609091214180112 69
    0x1810b58a03900c82c2d0303215544000403030f0207000002e1003610015003503541130031b04620140340000301e076110014000241300340240517016126000482d202e00800781b000c0c803110f1000d0f0031510f11000c4100d00303110069000c2420142803400307120455000d5841c400c20786e5060b041000f07802440358000d2015045000710305078040c11075640842e41e404048010714500030340700b4448205a032660000c0e074070840d0568800d901d400c40803500b4007240c101365004542102c84e80c01d00d101c5c041400e41d00d050030ba03808292404000b070150410b045100c4942d014190b0041e640c0c8500b2401c40c50030b01c4030203644400510026120360000408680d501156038441070703403e0000b620040c0d400351240d050581501702034602e100000c49645a542c008444440b14032405100200a1880c6803102540030025821500d00000d1075540c070103040001c0041440358500a0940380030104072003c550900d080c010382060049010321409407035522006989a0440d001082c0d0319204003070b034a8200e40100e400450000d0300c0031300c0d503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 197403408 1250 197402158 197402171
    0x10030c2c01080c10110303060607080c01052404060e060f011404031b09020310030212070f140102070b0c0304290703020705040605030a0203030d0f0e0607091a120402091801 76
    0x350040f8601c1102401511018006400740900321240450104894410341041c00461400e1a000004181c0300d400741d00114200344212003403074219203054450901020705501454508082e504048080340c808580c10020b551074407003400e41400307004003443c2c41000d03102c0000003143c0c01a20707580342c40c0d4942d000442c0c8461312460550b48104003003101041003d119400041c18603524021207215880c468904100705156a0900c440e108003808401014015103030041006220140d214000749030305454540c00c40101d20000e03081581d20342001c1c414180401003001c070b4010020450302103402c4072920310068003500d65064040c4510728200d140f00000062481c040c942e00051180c262101120304001a03951681015035440e02c0700c0009405810500c07030943c0074201907020004000c841c5074081540c114445140d424080c2c00c40d046d1002c42d0040c0010f11583d07584500038640a041044007600d0711700c0e010400a110040148003c1c403d480001c0050301401c00700e035040e0b40381300b550402405070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 197404658 1250 197403408 197403419
    0x80703080a150605120405101a090c04060818010b130203042d0602030c0d020406090602240402060715060f0513020304080306010507061b030b010810030c2c01 70
    0x108042620002201410010500c1400400b503000340c1c11905079440d29498281041c54002c4801e0b170060094070180143c04000800d280c0741c0c0500400c0d00d00401c0c0100d00501e006041192080c009404004401030501c014409a9004a46c164001c0c170310b224580395108840c4140c0e40034061404400b600819004002030b40034003107401440c02548103078544603403688144c1c49801040b4071600c815043e02008250360002c20710560055801050b1031249a01e81890b0014035402e81e4007a50019001602c400302c00c0041741d41c140800c01e00303201e50b00110903000034407581c105003482018001910071a000500a800c214000500c4449a41007500500000f0f030b844011031031074000c03881214010500c001c01d071000c0b90b4140c03088030f101310b83c0103410301d041d5110400115090b8000890803101c442d51401c2c240c589006141945441111564000c103030500a04001010560064079410f281c1170024420300010744207041c02008d807080000e80c44428000e60610807420001100c0038561041100f001044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 197405908 1250 197404658 197404667
    0x7060911040506030625030e0601030503030f010e07141804050928020a03030f0221030a0b060c060a0209010302040b0c0709110a1403060a08060a0603150e0a0b040609080703 76
    0x200900304840400c8559640c9051544840044403a140580b81e0070040d29180541d024082010701c102d0310300000c007011074268280c90400c081c0c00543d106e50011040080e800490510b07030f400750140303074200001814084405008181c0da185643c40320140030800d0340110500804d1b009103540018010301450425248940c1c464184d1540c0b4602031400203a50129014001c10b10003070b00d50b024040024261464404403020800c4900c100f045016071a0b42a240f2080007000b20346024846940300d99030305182c040c0c3c80860b10001d8220740903a0040c441c5082219010555580c4003444d8100075a035a5481e400480080c0320ba0f030443c040d00240481c0d02c43c00300100003120780650700600300c10001e020448011030712501a07240c0100020314035000802c8030b009010081c54010f8001f802094400d82c50301d21007810710701e0446070030aa403981d40c2c20403c14032a08603061030700c00c26905002c200c0701041a000589032040c20801520941d00c0c0f0001c034042089590040702c2d1250880300d11500e520051070b0040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 197407158 1250 197405908 197405933
    0xd0c0e01030507020115090c051e030702070e0f0411120a140d090f03030f02011401030321020a0f0c140a050a06060f0509160905090115030e010b031e0102070609 71
    0x40c0080d2030100001c02013401482000c0c1c202102d2002d210700309140500102c040e241d0148608200801400120703407105c51007105540508403142c90a0f16881c092070020300d04481c0b580040455070300d02c000c0c0b0441100708024603400c103030020501440380c00c0480c00b0410340c04041c202d009151007044102c00c24003141c580b42030246460761041c0c450b10f02007041d0071514100e0a001e011580d0b03600c6003041001030700071030940d85004094000400c4102d101005c030312840b10240c3c019804160700c0440c0301c0c1c210003020940120303038010038411400e051154034000c04400c0003041e02400e020f150b103c00e01c01e215440a998000407404021107420b00001c3c603090381c803606048c600301c41c400d0410001064040018480f0002e850000d0b2a0240b07a5844001c09048800c01035250703820701000f10b40208403604c2d01d40f4024080c184254011403207190132800141120304a06814006915241c4106035540d000300c0c01d002c1c0005080d40c1e108a43e05000102c900a110b440001040a481c240080c81008112110030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 197408408 1250 197407158 197407187
    0x60207060e06091c050c060706060303030b01030c02030a0f051306030b090115140901051c0c0e040203040c0303231303031e0e01031518020705010c0f0203040e04080d0c 74
    0x1079800041c40c07051003a180912500141e203c003a1001c00300d13031054101c415082080c085e0044603c84056200450050344c002802074403e6902c50720107000703168050103500004082803030100580310760034800a40f64001d600380c1c81c0400112505038403981e4031401c252140010085c881c540240c0e0385000140060946030602402152200000280ea040d403e55040e4079900a0f100c0003422240180b4075006640300c0003102341800010302035107c1110540150860282181d0390004800026000180c01075008d05030300ba2145004004000004010b425010201e03645414441000400403500301c180740c0b080340c03406030a90004100803000001350352040302100d0007074449a103d090030101c2c08810308010054840410a8401c0043d815442a80315582044000100c0d0840e103441d91480300c160145944035000c1183c021400400b841001e106800c101421410130480c19504d070200a0340701d024501c92280c0003c800000036003440144011107010045491040155100f4907c01400c01145500079 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 197409658 1250 197408408 197408417
    0x130e011d15071e030e01090c030b060a140f0102340e0405031b031902030403060605030102040f06030b04090b19050106050f0706020d0e0712061109060d1505060406020706 75
    0x8040c24516141e41d16000d240d081d6a00045850030340b1045080d0140031020904266403840c00c3e05179400c007031140d101e00b03e100d11a8a40d03654030b1402d102e49000005402c6600c00e400d020010003410b4400c01400c0445a0306440e603046003281038005074101400c0c4200540f00060b000e01d040c094030454400d2140a0711036010700452962034040810a40f041160002c0280d841048007811200d8209594810010510100e924007614000346440d0400740b1810b0340056800494180704001042c041c5030043c1c4420b80003181400d1514440707a144650348e209030300a040d80c52803444203540359504406200c2c1c1c2c1002c605600c505003013541d01c0881941d2040301e401d041c0b0b08000850380324442c2d401c9911680441200710708124164442c038000b50300c14010601550750b900c2c1c2224a604090205600a120090310481019a1814031005507080580402c100103001c2040103980d0b07680303c0603074203082000100010303007412401b92881020066000f0941c00440442c00140c0d15a001420b101500d102d50345 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 197410908 1250 197409658 197409673
    0x903040e0903091305090c040c02070e01090c170c130b070b06191502070305070801020915040312030e0c180709060201090b07050307021e0d0824130e011d 68
    0x1d5140c49005a90303140b075106022401e0000720520301e40100c0e8100000d40305031040d000e401800101100d500d00c0c03004001d03801090b0108542c408060b800c90040c03407111000e00420700e00c981c0040201c402d0640c100300e07640503840841e1038501c012081d54103420541541d000c1d150344600310070f01c03241c10501c0e0440b05450310b440011001e09101c5e40b0803880c01c0782819003210090803c240c00b1000190703e0119811071091882c000301080003000303c0002042c0440c00141c0e039111010a00620046104005a02c0b8030101700030000100c5414561300300d0102c1d450b00185c11500011441e042c44920b03d201540548440701010016804480b00fa000c2d6459465000b81155200c809030300341d40151501400301c080210020b05042e01581c019544510688187d401c0c040c3e14202c840c616052000c8104116400540751544540d001190f0580001d840310483c5258500304c00d41541c504080711200340580d1b0a10540001040182c0200c0600407084000f40031b0740150340980885c2040c52402926035124000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 197412158 1250 197410908 197410921
    0x7050309330c190305150901030b06010e0306040b0c1e2a010b03190204020c060411030706050316030e030d02040b0909130b0c091f020109030f030c050d150e0903040e 73
    0x7085800303e00d50107403191103e20420000350014030700146440742c000ca8100384c0700312a5440640d414041c5100e404008410700701400010200d81c20b28038060f0003640402c09000200d50a92302266102d0b103c1c01802d6904e1581030060ba50904402c0340c1e09420b05000300d070034039882003c0c0e24075201c50040802855042d5030a106010300780d031560150181c0507042580d800084000d030010741010680058005450855443c0409103485421030b015503a4032000b0a142440346014040750008242500d0080d0450a080da843e00e070340305018200d03030289642da020307401c0300139414401d0b107192540304501191074569441400034039034050f02c903003842200803000003203075094810913201c01d054100700d110a00d5941d203008421107521411380d00b5440080241504140e1540800c12010b2142650002c10050054030b4060700c2c5100158640c0141802e25070303189091544002500c0d41448030020100c0c084940f887c050042d80e0091f00005070080e00b4108011052a0001c02001100c03041d2180e41d03801c0d42d030b00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 197413408 1250 197412158 197412181
    0x409140d030606090504020f07080307020a031e081303020a060203010b0d0b030d080606070f060216110405150d0c080102160b07020a0f020d05010e0d03050115170705030933 76
    0x1800f030100800d640c014148028189a40501000c40407030109a142c03940341c1e1a0170710b084c1c004076080c400503482030711020200740d407000309102c5c580440140f00c1025246107001422002c0001c10240c804c0c016000d6801c1450b10803c0030641940e0415411541c84d42c4a40140c0703101d0740200031800d102410f003075100e0010304001603c4052034420341e5132200d039602d5074400c028140d40055015221042008112000301d01148001c020a403030210443c1662415481d06c0342c01d18060021191240b454a02044646081030241c40220348088825000303411051905440b5003801d5040f800d0030750301c0071036505c1e003850f02a441101080d0090200c41d559695801c8101d80da079144440c001c085202299491005007848010041c86074400e10001c03d55030504130144c0c0c60407140806210000c1d071284d00400c12a520034246e0355100107d85442050308290454450030107001418010030804000f000441d40c81e0248008414014085500490030f00c0000040d0107185402201c04d8803003154001050520600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 197414658 1250 197413408 197413421
    0x19020115081c0e01020f010510091a15030903070b09210c120f040e101e030b160201180b010306051014151605030c06090102071a070903020409140d03 66
    0x10807403811025440212070f10710301c540d4201e0641c468440c1c82c00e0282e00a0140611030509410402010781c0350000300b00680340306855011704243c80da0501200c0d503c5884c102e004c070f0010b100c00c007a079a45400404c1440c621030710001428114140c810301c0900d60001c9190240312002048665003441d441640110078841e02d14160b07920750104013541e0381c11a1a1000d80041484031551a08003075860f01401ca402808641c268540040c01006108008040449040b01080544425070082c116501d825031214003800b400405042c4040c0480140c1c804d4101c526909903001842a0511031450a250820307828042242c0312030a04000500d088401a0314500b00d40306c0412016401416006106204202c0b5000214848081081100e8511100d4070108510722600085980e04e154260726410180040c01881450340104420400300c0d002c00388407000900d01c500302c00001d03215804281c9100c0b006900003500103007031840100030f210301ca116955849014106031400712105070011411200c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 197415908 1250 197414658 197414683
    0x190605090103030c030311040b1b031e070206040f1214060403140706110412020f040b0a0b1804110702040e1501140303090d0503030103030210050411040906021902011508 75
    0x5500c010404203208201d683c1c603007802810001004121402118425403241d0080481c01100207030780141440f404111007800000a0061400c007401e030b14030306070044000784000c0300411001c00d0600641d0349550403200207006007107980e1501c03a0f03140c0c03400c0c911b5910110290348444100d4100a00d1040100d485442954542d40d9020751150b0742c148102d01b9040184155080c0e55111140349503018502d0080c800742a1040c03482d05444107034410089034415504c6d440e8016420641f28001e1074448151100644540c519059119500003049002e48800641301a40c0705042030010500041510007c0c000180203071024000e00301c40d11400f40d52a402e086c00c010820840304010405070403441c0303800c0040c107801000d0768905072541c000103d00c0c6031800c0e01a01d240d000003004008044c3c041140186241c1200811f0013249460380310040c400175040c103468000c46c0c0795100d00c0108181da90449a170044201180d12401c0e0080c14000d00800740903405051402c880200840c43d200e00051080c260350 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 197417158 1250 197415908 197415919
    0x50f1003020a032d050c030f03040b03041e0f0309090c030c020c10020f0a050609161d06010302211008032d04050a0605130b0f030735190605 62
    0x62442d41c65a070300380c03d900d0180340c0264450141402c0c2c201200c138018095400791004200a0020310209410001c1400b5203d0003580100420414009201c06a84c0c3c410f80001b84030380f803140e40502504c00c1e1420b5090041c860b02c4400d10410815802c001d040d0260b8200032400c103c0c140751001c0c2502151240d0200101592043c0340401a074541000d0b0781c20301042c1403054414280c0e40f4110145040c184210486054000e01708100920b10104200308048d0340c201590031070145041c04015941c50782072001d101c41c01c3c5110004076180d0007601103074010702c0000903901e0010164002100c1089094401150341c600462000a0984000003a900000c005d2030494105d450040703111008000e8504101e141c2031400d03c000503d07507803a90f181c040104a541c035503655490380011560300703103c82d64202040c880c2091100a08030000c150070340e42d0085880c1400384814690049013030100c8491025000c09a41c8940d8031458903040d21103103400741484505030101e06070350800c260103035410390043d1130300709 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 197418408 1250 197417158 197417179
    0x509070e0409050106270506041103010b031e250906121a04110406020c1005040b09030f03181305130201050a0e0306040f0219060806210709050f100302 67
    0x7403a0542c00380100910410000440951310030011001804407a10160f080400c86082d01d050449030180a500c64012038041082c1100c0e44000ea489000c1805405180c040c007100060301240900c03507482d840310103a10031041d540f0b00080a01024414107608081c4d00055007000d0303002c03d0164503404282d481c01c0d00c80b03403d01d4030131483c1203000b003020b4110078152496501c4c2c040f6517600c4621074060030304940b4000d99925424040c001e40740558460010b80500580c92a4440307503903004040c0c6050b50512104031342e507011744500181c074240140c60300c00703458040011301d13101d00d01c40034100f003541c1601a04c901c0d410090f03415000c03044031803c07215800703000803116501005610940081001c22201e007170030610000d221011074505002241c0480b0700c0c06400700c10f034065150059100440200b100c111580107824494020a010b0014105500034404840d01c801e904060600040b11401e0003001c0315100761740e034040c0b80080c000030349051651403a00170200d20b46c0100c0007244001e60b500908a000c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 197419658 1250 197418408 197418437
    0x230906040f02040302060703031517060a050702010b03100608010c020111040b030606040e01090c0806030105040c050906011b0b1f080d0503150d150e0d0c02090c1b0115050907 77
    0x70707084144400606607030800011006a48060290003134a00a035030021700c0e03002c1c0c15085550740c44c00d90480c80b41d50817111045400008000707112a84004c0034100030031180c0741c00206a0140852100041e454058451448201802540004e0841c0c161000034051030000500503400c03184004103040d603440d410401449441040710003160000ea000c1d040901d8607030b80e40c450100da00000e0300100d03000c580382d000e00350a0f1035010702d11035000281207000b04054286543c51840c0c00d141c138468640203005220000d42aa8000c1c403014682c001c1da440200a80005403605d0044480202c9403420143d51705c010402501c0d1400001506944100c1e008050601e82c9903001d54468000807ca10560700e04074020202d00d1326050401c41000d40702e10151138880351f550750140c040e104042800600b07a806060500082c030344c081d401c903400c01c0d01640c0c4000280c498104901c0148150340a1a0000c0080d5011041c10303101540604111080c0c44884000552034508112251006072098400140d01c40400e100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 197420908 1250 197419658 197419661
    0x30d0905030c101403090718020a0503041b23041409061f09020d0203070e060c0c01030207050c030312010f06030606081807030605090115050306090307142523090604 73
    0x3110f040c01183c1e03002c0000c4d182095842144e6072610f64100d41820062002c01c41950344849210260035410030407800001002c5010040018041401d18502c2c0300071540780d140071201a1184500c2d4403c9c101400c9901c0c940f1480061119004034034100754015008407801c0310710f01412400c1c2c05060f8946500340d1140000014210040301950440e200040035482c0e0b1000b00f05020349414007607264076280d80f01a2030820080d0001d4007a4004101c000e00200010400ca02800e5013400c0c0143c407107100342032540ca00703407201019075003500c80040c40420b144024004681290b007406940c200c501d40720f00c000c9081e11058400e81001c90381c000e011610030006008248843c10303110703089524207075698940d041964010b88840d11617964440340f00c500050000c06e50320181109400620080c181200c48a649108641c00034081c640c070981c4400c1030039018420110b205400c14203540300e036082a50703510380307886441c8140500100000f00c901c5210b0b507084000115150020180e803c0c0b95540d1040c0300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 197422158 1250 197420908 197420929
    0x1005030c030f0a020d061e0f0b090403050a0c0611070503070506070516021c0203011e0b010203211315050a050702010b0a030305090d0602030108160e040506011a160f02030d0905030c 80
    0x5402541f500940140d02c0075501c114041e100c0d5030100864031b904950220011240040d800c140121109000c01000c0380d00030088890721042483c0c228441c09007070034140002c10500034140348464001900c6802e001000024001040c098800e0740e02d181c6601105035018803429003094000d4403548980c2000d40740c800102088160b050b401c120301e100007940001d08460420038682102c60208031744600e00c203928440c2d000801d2083c0011440c1c00c0d2144121403c52101e440c803503110074115000510304c4481c407e0950300d80e070380c03061550f240b600f50214032402805080302c540342c002c0d20740000940400c0c0705000b0b41c8980c480182ca902c2c0c41c981142c070125903551004804c1604060244641000920140700030350090900c0c034040c080e0300100f00794000a9040546c00391038030646800501010400202d5050b0444464100d0700701d61242000020026006034a1003148481c400fa41c03450501c0f01c1c940550400d03c0c03084040c3c81c0b54800041050760501c03c1c5000302c0d034040d0301040d81d0010508091038041e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 197423408 1250 197422158 197422163
    0x3130e041502070314030a0903180f1401030902030d0201020304020102060a060506030a050402040b0d0606080d050f160f0206160b0f0705040e0a0b190303030c0f0f030903090e1005030c030f0a020d 86
    0x101d80c010350174002c003e481c2e071040d107907030b0300141d81c0f03418a0052543c024440d082000c100c0c2c01d200c2c0940c2c40c00c03c80d41e003680e080e0700400600c40c0441c03450154581c040c0d84044010365011742580c00700441440064002e40044400743c0c00342c0142c0e400030b5001001e5110303040c19608010203c0b420f5841c0d05252a006080051080707822550340c01104040d42d56111801d001c052164001050711401c0168003410600e050a401090100c14424005414101340070340c0c1080181d04d40748100b18015092440340d4007020708029401c02ea000803c0e0b49525405d212040c0924018540d04046444000400c4891901116030000003041403009215074044a6030712a00408900004184c4000d5000003035800c03540b030b40c128140c0b0039860004108064160184016400403410200d010f11035404025140c3c4000c00080c000301551a070a540405000311251006415640c4181140b0b140c117206001015805004041c0300784607405642065280009000f0060300d4694090113104070309500380100841c4c040c01c00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 197424658 1250 197423408 197423417
    0x62a04060309151113050405040c03021207050d030e0405090c100c1115030402130209011b080c1209041109150c030c030a02060f0f06032a060301030503130e0415020703 74
    0x1c560400400c1c061240c144c0c100e005855641c25038062090718070700c400e601c881d0286d820041044081468000503500702c980554a440e41c5058014480d403e008803900102c1e0302491481e4000d0a26030700c0401c010b10950180c0741045240c55a040711075550321346d0740100e9804254142c01006040c440c80c40c0039065441060341e01e0342d04e40d4180c0003408207040150f807406180d1000c1700700410751800c2c85079102c3d03a4900c29001c51400d850100000c009281048400409030010b919030be0420000c0700031110103003911401d03182006100031442c65194405d05460340f20324140510f0050422603401103480e071600082400c44040d0794030803400c819030001c071450109404240080e00c0c503040c00f4802041101aaa4058200786c0380402040d400300340090324841ea404440320400c03070a510002480b05404031103a2844010302030040d5071100000b00214a43c2d007000002c80001708100300080a80105034080340d2220000d51244c60040c0701c040c0c01c550280901140b072010b41581840740c1d00030f10f0a02d01900d00b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 197425908 1250 197424658 197424683
    0xa12051317010506010305070810060e010c0803180f070b09040b010c02180f22020f0f0307060503091507080a1503120c0606050f060a0503060a1502062a04060309 71
    0x200c9844804214481d60325903510381c01001403940c0c1c141f2645901c00581d007000051414a4551813158500c580640340500a01c0300882c0d500b0380c001c07082d01107604d902c41d500d10b58908e4603e490f402290019819145c6034460911038003c203100c0810f0b141c056402e103c002d60309060040f4200300261418140c55410720030010410400341c0c98900722940c02ca00030050548ac98102007010102180008204034240a440072a05148101400e84070740c05940403250ba401182e01100011013a0041189283e03251040900020b05550860040c42c0704080807002d45080205000442141440858a170000030784802c0004051580560001c1460b06c4080c60b00e0055030b840e030b617402c103541c22014048000f2031042d078101810026180030300e0f009881c0c151110510066020b0201d0000d01881084c0d0091213404000904142c840c40e8024000b40082051074101f0300300481e02035101e2409548001440d030700d40074041030118040511400310500b40d410070b45042e1030107100328018040800304545008041a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 197427158 1250 197425908 197425919
    0xf050c151905010816060906080c0901030609061205060603010b030a03080a060b0310151d0103090807050102070809120715050d0b030604060606020106051c1101090b0315120a120513 80
    0x100e0b00e400303013401e030b40104118010a0b0100300300350ba190b4004c20402c07000140902100340d110711465001144c5404494a841040006034080d0010b41c00c401c1645e49000340004078040c00c00e80c01442240610b0580d205a03c82c0400c1c1400e8501401200b038040d841103104030006071250600707592200c400800006c0d181c0d22420410003580c0103441d6a526462040d005000c05d454082c40228480c03114109000d0088038030710b40c013084040211b150b5041c03541c1d030744200003441002c60480d180a94054021940c0d01514905020650409503c440c01010300010702a65480000340385410b440c040310140711041c4072460b00b00e03802e42c002440710070030544607002109036807410840300c0d0040780b0440380456418240380c0b0003405c445d1154006803041c1d0103921004561490074694841d03558010082c00b40100c090130040e150b1419a034001d03802c0340b00020400000003000014203407801d904440410401c800018103503038610414001074180c10000401d02011401640100220754202c461091041e41d0355 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 197428408 1250 197427158 197427161
    0x60921030b061e0d09240903080c09040f020f1e04121209050915041a010504031101030b0a0605301f17071d0403051e120c0a0f050c1519 60
    0x1000200d80552190241104003a142c00e06020180385a440411200c001510010480314010f412b02c03008000010300c81800c0c0e2610340000b540f04294100540d174440054000241a40c000c0c8013070110040100042660307400c4040c1210211784400c0b000c2810111140c1311451110440003607002849240100000c068903941d0030207200d042c00414041c103412240c414007003900d0002120400c412560004010030307a0b000740c1503d041d030b0781200800c50101038000058000b01038424100ba800032010400165165200b401824000d10301c6c6000050306011140200f014220030032046d40c2928410001030342442c3c081310f4503d9500140c06201c242d44d6543c250900d158204244500094105480038481640d403a43c041d030f81c050f0010f05080d11864181c6000701140030b904110b00340c440c02e03c3c11420015074900162031200180c5000c07684c5c1070600728a40802980030401c210042194450101c0215004c1d60036100a50307807020280c40b203c01394110b441c9034018010400a110500703e010300000032a00e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 197429658 1250 197428408 197428421
    0x6050d0609050c0d0b01092912011203020c0603130305031f180b0a0510300f0b03011a040c0207080618120702150d09060921030b061e0d 60
    0xf00548165610b803091904416540011a46814886c89a00410070340105039940c900700d007540c07580b003a4910304504c404240d520442840301051080800045070001140c0ca0002d0703880c2c0301c6d800700d440c003c034003100340702240c00201e80130380c0d0f0040081b00345001309010340020741d803219048a20a81030a0801d00b230151030040f07500001182c07c0d0302207204001c19120702c2000048042103400c0200c5515050002d036404802c503070a14100b060002101c10500d00e00c1840001e140b00928030418031416454912005006102005070100d083ca00707a903a003070030188540c2c0310070101a480426031361408020310011301100d0750410704500c80c03400c0000306903406000907802004095494242c0c046540c1955282200300b050316003100404025060060340d480f0b0410410700048981544c981d00c2140981004102110010703220720f00b0403403c2c034200034200c035544d81100100d420a4505007843c500840490b85c01291403074100a08202c0c81c0341680b5030480f0340d00040d100380b00310ba103060400070b094400c0c3c580 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 197430908 1250 197429658 197429671
    0x90c0f0507080d090506060f090402030a06090212010513120e030a0204181e0b070207062f1005070315030221011d0309032404063803060606070302060106050d060905 73
    0x10801c03d0107180d1230860300c01a000682103400c0b45160500e500001d0326960105002013074250348900d404219101c808130b2244070181a4000c02142ca08080b00040c02c11040030100d034201d05c0d841c004803156000c2e01c0c0b22102140098020000b004c07096080c80001c018048442400030034400c0c1080000381c3d418103007030207200c01d441c0e50071041d00c891825004442c0302070846820354100e41c40501080b036003d488030603140815010420000e00c804071036030304504038289000742c03401114843d03c80300c0300d283c0109000b181240d908101440c454030040c3e9844000d400003d5024058045e080030249ca01c02d8802507481821000040100c14050200b4a0719522102c603040c0e5040451070149610b400d0140130744090b00308800d1083c003a2072030700c0c603048080300400040c4110399800f444001814074509048480c81010440d40c50380c1120700301803100590300b9804900c24172454000031140e0070007200f42d503902507041c0c00510060f400e0413010b68054100240c401102640d035080011000640d00a0707500810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 197432158 1250 197430908 197430913
    0x50d1107090c09080106050a05030a2d03030c081503030702120f0f15061503040b0403030906020a1709190803070e030312060316050901090908130303020d09090c0f0507080d0905 78
    0x40c58990490301b521b4140c0e00c00e40c8940c00100f0100201e4501194100106d03510028070605181810000126407505500110000ca05c020100c001c05406500101340804280c0310142141c0d03481c000180c1c1c03040e64000301c0380c142e00207020000040c200014034656401c0c0c4036003039500c002a182c01480c5400c00410090840340e00040821608801900103590060380903980d07a10080034050654045100240001b0580d50154000405242c4a035103d100d5483c1c2c007002c15542c40307000882c0103040045240503e01c2101d00c580204030404000907030985071655082e204429032419072161031803900020111800c0c09805d80102d0b02a40e010304c020106030000c07500210441c1031a8060625120f18544103580135150f50302e080c03002c1d40d0b6600680d81150700f0800d011030065030a242c40041030050207928016a400c005c0c02004258000c2800c5140103003550320590f00b00d580741000401e8405c104820004104102c01d102c010a00c40d0700103000b0305000d00c00c141e140203103c0e424203089610006081d10280c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 197433408 1250 197432158 197432177
    0xe10020a1203020306010801061b0f0311010b061905030711060a051e13060c0329030c090708130201050403050f100c03060305060a0b0d020a0e0604050a0504050d1107090c 75
    0x70001d80c001d00d40019251608600394070301400080e110720010b000e0300081c0715038002e8224010104014844d4080e91000c0076810b401c2c0d03d4070300034105900c44000d9440b00d5007082482180350912905071780200d45641148004254004401d6032aa03102400070820403c1100014503012010400180121001100041e00d4585401c00d025281103824240c00411000c209002c80d43c2803c4800c0d410540e0068000500d001d40c220b004d9000f004480c80d1094a03540440500e001080b005030b40d400ca880301501130b101d20078441d00410101203811240d8002046111340451500401068072540312031041c10460b2030300f51643c540b02d00e40344441400707440030f40c0000c2403540c05407064021100c1c47c047d542418842c10f410360366800d0300c03400000c1140c84169905e00440e440343e0703123064058603003640107011481340d42d44641524022a07401c80340e05014506102c08180141e8035449024441c1d9000130192000e240c042c01c0c1100c0078094800c4021461013602070120340018544110410300c40da0351200c030350301c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 197434658 1250 197433408 197433413
    0xa080a150f05070e040f0b0a0308090f0406030f0609030c02120615030616030e1612030801060e06090d020103090b07230c030f030a020c03031005040b040605060414010e10020a 77
    0xa41c1c0c20681e5042034a4102002d000c074654200510150b03440c01190003141c10041800190010002c443e1000d502c800c2e0b08100105110b40304c00100303000e40e015980c0504990310007080c031080d00c0c494803000b0458681c0b41c60560115146074040c031034107442440c1c00c807500f1142d500007444030001e0b841d04604640022060102032901c80e02c4103050900d041c1e001d82058500a80c020314007110f09141c1c3d005140d16030011120104040c0104010008442102e103103560303c43c01001d103a91407814003100403e426000200b162402844480c0e42214010102807900300004284680540d540c0000c03810f042d01c1d0f26070300d0005029900104d00c07404243c3c1e16409803c030810030341d4101c440c103521041010303001009016491080030045a08080b0080760f00caa032034031404224402440307690000c24080c00044140990b41ca150f00751201190800c507018096480c410307040100b120007d10805900900400c02005200d00541c0b91540d100703814100b5031012840302e80825510083c110b40c4100581001001808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 197435908 1250 197434658 197434661
    0x30706050c010e07060e06090a050909070f0605130302060913060b250c0302040c110f01150501030209010f080709051f021207030804020f0406031202160b09010504090504020a080a15 80
    0x228507180e20001c01000d4a801d070045d140c40100c07056a07004900000f41e00800c0e482d427100c0c2400900c0c0207403030300d81203207805281b564950440d400b40c0d1078010082c0000280f000c3c4034005441d24201500080038000385581d08000e800d5004a90303540e00b01c1c0d481340e4480d0048d90f42e0b1081000805040103180d5440f1600001c0441441c412918000341d002d204c4d02e60781c04100c0004800040d65030513500000c41c104070030341c16075075841406815143ca11895074200c42c038035410741207072550030113280c0182da00e1900c07540194240c1c0142002d4900141c588204082c05130310030740800ea0849814100f2003c201d03203940210799607000c802401035a0000301d14031a118a5410010485e29964070782000b810445156401011410040c0c0064480c60182840c00c0d041e070f03281c4d07100324011503002080d000c0c00718002e41c000c1d481d51040e04046140c40388000c1e001400070301250844c0c4480105945141c503144c103115038600140b90140c02030f42c21820002021a07050410004a4001c9008034101e50b100a907900a010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 197437158 1250 197435908 197435921
    0x106030c0b120c0d060503030c0a050c01110a03030c09050d03170a0e030a03090204021b0d080105010f020c130b1002030d0b06130512010f1109090a02160f11030706050c01 75
    0x2003010780100950000c08214403203440d049803458003440e981c0d0181050850117000c4680104c2d43c0f6010008500c0042600003c50944051180c400e0380c000340c03040001501c04914a000500c1d00f90049001ea800281c0b1030381c807050320030850b070500115058513607001c42c140d401c005000f01d000c1207812290700d807594105107900340e00103820001400183c1810700e01544900400c801c0800740b503250401e09046648640503120700030200c004204c810300c114400c15a48168001000d070103e01d2030703000415694840c90b40603000d00f5898008040d0907101400307200e05074680c041b11300141c4d41d40c0c01d10006155a82c004815034050340d54021500e6018084801e4101c1c1c1281030a42d202c2c0100700105010030244180013011100210361030340801000c61412800350291128603000d9078584181603c81480540280007140401c0e15130341c8040d5204007010b03040b403041c800c808001d808028103030341c001070b00c4928621040d48601a81d01e035110821001c070340f41c032490f40c00c440080b420108245001446c00d11800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 197438408 1250 197437158 197437169
    0x316061803090e0c040e0f041406040b130812070f0f0903030c080d0f050901051807030c0b09012109060b1009030b100305030d05150d0c15120207050106030c 69
    0x42481079802418001c0284036030f0018826500020b544940d05405680040640e074014580926200340412014a800c960031a990461580324411402d00081c0c078500c00d60344a45902d03850340350304c480c8141e1640f0050f4116003810741005030401c2584d51141c41c0f8003403140d0b80c41c0c10070b055902c0b02005e88078400c050281c00800c41c0011042010943c405841104075070030100f82c41ea00c1c0e00310022003000c0c0c0412410035131018141014840c40100541c4618882c00380d901001c1e4400a1494100352100403a1001510500c1441424041840303132100410b11903805052846902821880c40007001c035140d0080700310181d03070391508000e101c480d009a00301c500f0202d603071180d440024080540728510030f00002e00206561380008030801c00b070011660146800c801261384550440168001a2a0850300b48070000c224031107407000d9042001c41864a994030185070b038001414100e5003070000e511b082c42c480030007a41e21340340f5064198510040c05400e000f50000301d0350382c0c11030800226603411f56208 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 197439658 1250 197438408 197438441
    0x3060103051b1e070f0c0e070c0f02060c0c18040b060604080d0e1201061e05040902060a03020903012309060c130501050d0608010c050c0d0905090609040f05031606 72
    0x42c0450081c802101d0342418000c20400c100600441c07000381d40c0c0141c81e0014415803424440f4014800318068860440364040072600e100c0c1ea0b07407401100e480c107030300e40300914420303840e600705006140080c040d16401000c082100c0d1084446000103110a0145aa5041300b004000600040c06048001d059002c00140d0ba410f00d01803070088825a01e841c007890100410000100311719a41d40d807041101c080c2c82800000340406912540d00c88600c40240107208c94108000c503001072542454040d0003c0650003c04090078141454401d6010f5446031751400ea043d50303100e0a1400322083c1c60342d414400142042c020b4010714082224601c0e003200506088000b40043c802c85443e2031801c00039405440081ca450398580e50a90302500150125811440b81c5501701050315206645c0000605101445242161084017507004141c880d44441d014058001803090b000960a00b45100d50b1a00a44142c602d0b1011101c25150203003580c01078034045018540b50358034002030003042c4c000d0401702c1128442 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 197440908 1250 197439658 197439691
    0xc060e0312070b04020f04020f0a02070906060801030b07030204150903060f05062407200a090c020c0405090f06040b060a0608090d0f12020708041d100b0903120d020306010305 77
    0x40000034052040c00400c58840f00d0005070854a85411000206801400030b5403508815030407211150006c0d2002e00c01440b940c0b60003ea0f0031558020042150f0860b00d0f000314503402c49d02c402406da0002003c190505400300310000b4400364001d181d415030001e0307687c3c10610340e0843c6001c9003522345800e15440100c1c245020322440380d455180d402c25424507040c421030202003101c0101898050000003403d18009094100710b81101c100c40c000014008803813211445491325440e00072901c0829000c40140d210b08180720141c200b55015039080203400046984540844400341e1400000b250308460400c0e0b80c0c3e0a00000f400c04c036410344040c0807142048059843c0190282d03640e2403840c0c20001c20003140d48071020341c107409807503000c45c3ca2414040542d0748484030f091a08a0341e100c0d128142400d50002100e10340c900000560310301a01000443c00d144510f4140048441d801403005d255050042800340b0082c5e0006000402d01c29201d5580540c403403821400150403074000601c040c0d9511046103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 197442158 1250 197440908 197440933
    0x18080a05031b03100b0a0c050601080105041101091a070609020418020f0d17030709120812010e0106020a150e01021309050601020604020108071d090708090f03090a061103070209040c060e03 83
    0x48071041e030302c2c545c090703c4d15400381345d80c1111218500d0202801da40509800444c450030306400440c0700382e001d41081c90340343e80310303000445d4074081c20b104aa00b15050023a8082d20030700001c0080011a0141e200130849202940014007103503088800e0041901403450040118202003401e640d2081c4121599540c003031a0b600c9a152661002110a00031000000006d05a900807102d150140101c0c840c801d01200c5186400c10180e4040950b020000500900020b11014003a400701c1c103a810320b50191000031280d54412005006078810700031256160700072800c1481c404d01c080e1030003003075441e042221360345480540c07021200041c0c4007a045422000801000d40d800c580216040f0038185003441c1c00040410301c415410b00007900c01c69004514205200455602000550040394203400341e5950300b480301181580d07846841d01c000e800050b108820081580100d0b01e0110a00780041902d2031300e50141e00003000c51400700c404698a801d0410300344030340341d4000641d88107020258018100c80780c805 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 197443408 1250 197442158 197442181
    0x1d010b0105040506090a080a08030106030f1a010e130c0341040501090b0114010f0c0302060a110415030c121a13021905040527010918080a05031b03 65
    0x140507884c044c041c0000c00c942a915070204000081910710709407403413420180707444049540288905000242840f00e903182c00304051041144900d1195020220349501100644e991049060407075400a0401010168200c45000324031056120344c4d0005400789461801c0c02c00c800b201950f540e0f40500f0761888110861125440c4619441e501540e48203540c0c0301d1070050301400b0035150040c41d01420000025880c100c02c0b0802c1024038013620f0716821144141d2084404240c205005401603000e4030125400b030000d07601421366030b44980407092901c0d883d06040810440b4840c111b5000955541d80b5072078440d888006056181090355082c88280e001e824012608100e044400d0301c140169031820042d022940c1c12107c1081c45003082100ca2040020f0140068009200e105e0013242400400c0c11480d00c12401c0c42840c0d4414010a10aa400d10445400904488444040307040800141d00040f0302e810300640b1201c002552196900e01d01621038103114000d2901c401403001d000d00c14010240d411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 197444658 1250 197443408 197443417
    0xd020709050907170709020c06190504050705090a06051e0307060816031104030f0605060916051206030a051002130f03020105090d062310120203101a0a06031d010b0105 74
    0x412040421304d0a40c504003604011055010340400c600c001180003040318003050301d40c840c140e507d203540320600301d4451003015547c044600401e1601f111400340110f01d41015030540200c8a28000240340d51030b10045540700075000220709110f000c088003442e00f031408102c1c50014144900d842016410038030030f0390300400ca581803501c06058841196421580c01901a00d004603080003240d5040c4286041c148000e200585002d0b0044a4200c0010b00c2d464204403c01c00c011642c1e502c0620702808941c101c1250400504040d41c180203244807080483e1080181000901ba401001655400e41d4921031701080410b5108881c00703070500d0000c01c050b070b0f006020f44103024016559014002403e107460030040844c0314000c0e84440b00001504500030540c0c0d1803511030124115100303000c0b85c030f4201301d0600005066000303500d98007214003410300490320340000b00c3c424844684c000341d007a500c20011351818825040f07a0000b0b50b07694400f801d074000b4140015214030307a130002044102003440001f00303544074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 197445908 1250 197444658 197444669
    0x90f0e060f04050109080a030b01021501080d120e0609100b010905010509040507110d03060303030f05060f0607080903010c05070b1302100e03120415171003030f020a060e0d020709050907 82
    0x90a00050b0a01c0343c01c0d000101002c2d8070a410554449540c0005402841444100380c014420b140f480d140a4034005201d03810303101f41e81c0007401d9290012a0848003204038450070382600c0d032102808a0341800800c05107010f50512000b0341046a010b040032812141c0d003c003c90304010b0125001c2000d030360050b0844500c0c0c0c0c0150b40104203031303489035415155510141076541e445d1040da4801c41030140e01d640044240d034483d5500740401c5880c461410309590b003da402030b82c0114100c0040c20703e0710704000181225485036082900b0803000310002421541744095100c00f00d400002c5a41c1004260440940e001c652614240112000e03600402c1905400495810500c004d51807003000302e54081010003000d05030312078032079a1251650f5904400b070240c00c220700003040040000074910311043c0c0c011403003102c226850315481c0d4074544045034025601c0907000150300802c14004046016130250303403048c0c1c0690000705081148050300134a00451035016180107890002448074000000c60440304481 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 197447158 1250 197445908 197445931
    0x108011d0a0218180a05160f0f090905070902070b04022e0305100f0312030b01050f1611060c0109030f14040302042004060e01300906020c01020f0301090f0e06 70
    0x2600c4285400407a1612900070000e4410740c1c5d184020400c00103515154002e01c0b00c01d8003c034680e64030031000000ea07103004101000c0e260810600007440385511251000b40034000300c840c0503a5a840682c01c0764042207080d00d45015140c00c0200b5070401c4170213243c9615610031921010180715041d1030003040420002810140c482000c20b80703410382c9518620160010340441c0b1000d07a607d2600c0808081e200b0b0b000c0b00400c0c144070b042c41046d0700a07001c1c0d490071007000d043c40e442c03c0c001442c808483c0d180c00500b204d003203040340712040d680d80780c0070040e11a10340900c3c0006210a024200900342103601c150400401c14080d02000103030902c0802d80d011a50306480224050042c9840b1004810440e02c3c0c085e65058041000030b46d141c3c4c0000e49e0410f80100780c0b140305020081c0d80700014040d0035000014049a400004a0040420380e841031110902500005003402444000d99080e64028080c214171b2a0000c0014800d0602070300c200c02e21b5040c1c00c0020003140720940200d54035914001c00341ca1504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 197448408 1250 197447158 197447161
    0x306010e1e060d02120708060901060c0302070b07110405090c0d06020f19090306050105060f0315010e0a2309040210080c0c01020412050607030e0c040b0301020c0102030108011d0a0218 81
    0x22801c00003542012800038542030b2030f0610680e4203002034201012401d0001854808611028010485540501d0300a0080300c00f42e820007030113541d0414032040071401c520540200140200481e00640149841041d0242c0306401210400c004d4500c0030b0041440b40c0c00c504180202555030a44100002e0f60140c030140e00e80908442440150196180244841100c108960704159120440b0f0741503902c911803c101903600c03001480101c0c0260080e040d0034100410200b020b0400f440e144618502052404010118803000860800302582d807100a80c0f10203446017814a00d10328481c3e02c0440d0050703845000c40e03c0d043e00050703410a254211a028480c403840424842d10202044484050007100203543d55aa501813a20940c040c601c41074a150007143d010403040c134480d0042000078580b0700f00422802c01e0103030410006104078080a0f0b072566003044540c0c03d624003030000d5802407007640c00019452028000e6034200e0b86541c03030180e00b15000741f2403180041e502d2703070700480c04c004510900c251503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 197449658 1250 197448408 197448439
    0xc0201050d020d06081002030915090f07030501061701110712140c030a030e0a0c030b0c04080f03032a0a050310030803042006040303021902040204031a060f060306010e 74
    0x194403402050251003800042c96007400840d54120400300c1e5003000c200d4106c550180c400320100e0009845110700ca07000703403080b0303811241540b003aa03030040e84201c01d40f0301a6803149802440c0243d103a000701e5880e51582001c205a80c0604000c06039000007900a00041a1803107028485110f032840082c410303c8441c0c84661010303c40c0000c1d441d00e80c51b160b4413580d2556007801c0c180e80c2e0b030081b13000840000c3c10300c010456004000b044810200e03502210b020383e40d90865481f90491400108a10f00507032082c0400a2280300030011444140800380155940e42000c20050012203954110f8210401d14640010f0b20b0714611011540c23014994604907480e5214418590840c20700ca81c8007070300504020051005020340d0448805101d11822648000c2107440801d015040c01640301c003034050380014540314401d490b004400400c3c1031004100610f80790f240e5542c1006014100400b01c04c00d22200d0400040e410005050450036070120b59682c250319103080000c08a40d01d600e807690180c075a200620a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 197450908 1250 197449658 197449667
    0xc0e1212030705071b05090f0c09040216060e03090a1413061409010905011206022a0d180e07120b0603011203030515030303040206130e010b030105031614010c0201 72
    0x8020001004060340c030b00b05520300070710350380200c0c10607a032a00440d051241e205c0004204102107032405001c0745942c3d80c0b56150513040300e000030920311400000700942442d83e5103520081c0200220300c400c41c60b40031402c1c180074049440944000603503910400c14241d169a4086003e001c4a291850788034280f0440320220b04640381c000c800041c038500b40800801c048210343c182ca00f1900c003d55060007107a81e13815515003966000c0c4608180c10140c0c11140011a10540082c0425000c408411001035411345900100d03149080c07040e101f980181126964442e4007015550384042480b05209070f0b60b05040c0203903814200684014184a40c2c00c0180441140d150000200120001c4c130007502c9603910a2180c007040310101301100000d10b0b0100044540c0c940000a00012001034001c5003141da80f94280545075003e50f40ca410b106440c2280003c031207080900d4180640031031400242c40354503010905d442d00038000004001d8a16500c400c0c000034101540c4100c010b9000d01c0c001210800c02e000586 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 197452158 1250 197450908 197450923
    0x510020a1b140d020d140a17040e09010c140705030403170406021207030912020102190804170a0f02060708070c090c030509060906040b10030c0807050a2903040c05310c0e12 76
    0xc08c50141d1860315900004000054004c4880810313030790301c0558031200d10074202e038810003047d0301048c0741e01c6400980d11514000f8044080c8900200d038941916a141c140074521801e001c88200c0f140001c00380301c1c950341842891402018603c049042015540e800b4124401c80c2c090341e290a00d0120007203003503a00c20480c0d06042c50718a00b4003480740806081502880d4031a00962002c50300000601e01525400216041400e422402c2080789022a5080003900d0344a09400d45501e04140f203420b005c10000502d0320300a041c05400041c910203494000713815900010176220481e000141084600c841c0416516440369000991004036a90104040445043c83d00050800d0354240408600c41400141000035a0000c6070400c40e800c0c0d503140d44044c10f040c00f40100340d049400d66014071208881c14043c58000788102c01403010705440700c0110300054007880e040c5149041c040720034031414a10501103580c0c003410500c184000e0320050f0300500300d40c0e5042ca1a07402819000303e043c080741001d20121 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 197453408 1250 197452158 197452163
    0x1030609020a020a110102150406110705030a090e010b07080a0806060d3201060f0c05011d0c040605100509191703030a0c0302040509010510020a1b140d020d140a 71
    0x440d2a0390102c00c0080d9102c2d288201143d1940744021004410b600014500c0030213000c107280b038400d0307656a40d41c03a8040c1013180440d145110043c81130000140341800540340b1a00f2590b10f58905070320f1301100c4c0f40c1203001a0310072859004100500404920004100c40c3e188003107040841c00d5403140400b045651089180c1e00000307034030340f100320f140541400c00460090030059100710800d080364110210280340078443c5a0100304141c090303940640c081d131a032280ca81e020308000225404d40504100c4013078034910180a540d040241402c040d40380511a081c040d2509803010341d042d2241d05030181c140c2c4603510000384111541c5c12100c2c40544000100000391100c1300355107488608452400d5920381060312180d1030503082801e400c41592080c03003901c04840c8010300152059107840103008522048010400c00c500aa5203164003280200c0b50090409058403038a601a500d4000020034040801035518401c4021809403405640c0b50406c50040e0360700310041000481c010022185449001c0000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 197454658 1250 197453408 197453411
    0x70c0302040f0608010b0906030d080c0f0d3201060522030507051c0c0302010c15110306040b01090b09090603030714030d0b04050702061810020c0a02041104060c02060901030609 78
    0xe101206005801043c211410358000b448440d104400308080d0311400c885041d019844000c0d00301e100c0703110b0814550484c1c0b2054440b4a0900000b11036040c960100d5416001e564a400901c1040d22201040a040702c2c0c9800010700c2e42c05424284440000e0103203e400208900440c44800b144000046a540d4203550f4100c11a0706070b072481c08603102d000030300c02d00d0302c50080c11003014280c0d0700c4614010985940700c44044d1103142181d00544907107021003020340311555119606c02ca2608244a000d071040840c545c000d450f494100c01b0482620320758001d960400010303010402246003c001550011241110036214030b0b901c032000b01e49180500a1702070b2603000c07220b21501014030084024070f00c0c0300c00f403801413020490f59010310041c2c620a56000005a100c040020148440814004c810466610944104420707190b41141a078200c0d29464100c0c3d0004070306c1100b1031501d4881c80d6148200d9104850a01e0700e4902c001d4058660340304064001c04002034071214687c42540944007070f101c2040c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 197455908 1250 197454658 197454671
    0x307050310080c3001091b0f0308030a021c091a0105010f0806060d021c050423030a0c050309180921041a1204060b03010b0306060d110f0d1b0902070305040b070c030204 74
    0x2c2c4071355100f10500140b203287c180c028002c105e0035040300b042404c0c0c5e60403c403400c4c0395031104040c0030002c5d44094401c400c41410182030f10780c03540d5031b4001c0180160042000107280384030400340c18034420040e84403906100720f00e400242e00c00e03084044d443c0d0100c0300325036441d250b0140d11030907406031041d02c07940821556400c0c0d44c0341c0c0c0040103138000c5005600425451034189400c202c48001c0100083e000c0b10280c0c0240b100c4207043d0f2080d208083c50b544213105590400b00a140440c06c0c40024882e009170003c20f08041020001c0100b103036501000e2503e1180c1c8091601c0c1040d10300c10301c118000d004c070030007800482006209140c011140320101e0034110700c00380d1801d8185040103003c4888068444d5007083d000380018500010181d020303400040000d242c80c45165901c0f4800da5040c0c00450700640031191540d030700c0da01e0720405002107005882494440d0f0104a084000541d5500008003c507c1800f011001c241d12200759000d035214010380c603940333040c142404d1040c58466800203520504122 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 197457158 1250 197455908 197455913
    0x203030109060f051503130b09010b03101401180e031605010b040501080318040f0c080702070608130f060f09080903120301140f0a0b0307050310080c300109 69
    0x401941240c1e450441080581d49610807407280000ca4404c0a43c0f210340d041e003560500c10104011604000c10811580403501c0c580d48480214130704035043c00c501d0f5543d080e0604141800c1c01402100401c80e80d040080c410081d11320701d07001e00c0602401c510507035500c41c0107403655502d6002c0040e4030340600803030b500c0e1342c84001e5664114074508002c85880d400c00e402c5800381c0c100390159505842d03180303000d0750401c921400f422101c1008464115449a180c0701402c0001030707140306008045e1001d41d01c40049261203440603240100070b5000e80104040181040f14801e840c1c40d0301c80b1010b50041810701d4446242c14030354080c200000c1d044280c00c1c506120281003000d150300610400109034107a030000c80002e546080070317000900c5021601401c10070064114505910030704900e00c1e0044c01500c19a8440403810415042103e10070b01241001061088881c829225240100110340c010a1410404000300704100900940c130803018071207003009140d02c1440c030711200b5030303040a6000300b00780c4100c0e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 197458408 1250 197457158 197457163
    0x20f0604050c01090e100b160f08030a0e0a05030403020f01050405222d020903010207121812110904111017160c030516060608100e0613140a060c02 65
    0x1c401a03404a200d4801c00221844403400d0f4500c1005c903000c00e40c11b07031842c1c07520655083d4480d450784d51501070300c9182000006c025180c0515228000c0030b40c01d0b20b0740b4111804504858450303080040c0d0b5031110001c00c0015000000712811b581d030540301402810344000050781d00e802260442503000040e258000a0900c600008901205480d541440401240c01d40d0803000146010280b2084c084002c000e25020b4181e0000d005402c1c0141c0010300d803580d07c2d141d110380c29000c02d018000280da2915a400c04442c0021001e029228204160303102c0d08490f40c958400108c2c01458900407500e080004050001c005c130000d1206c08040c1855950b03118001c1c00400007000f1024646040c81d0f2400460070344103907070034035405140b240d85590fa10208242c80c140c805821030310010280007985406880001e1950141c0c07001032220900800400382c40c11800e00544040000c0c20400758001c400b003018103103038481c40d105056084046003042c40c8108211604050b02440c02506075030419151034400c6500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 197459658 1250 197458408 197458423
    0x31f1502010b0f0103203106020f0606010509010e030a0203030309011d010902010906120204050301061203031a061e19020606011119060216060e010c0905040e06070f020f060405 78
    0xc645070100b50001c10015001c45d0031b90030a1300340ca02689035141c80006505d2000304520101030090006101d2002169021403020781c481030030700c02502000b0007220360104200004511400041c003013600e01100020098040d5204540c1003200c4580140e915803010700180c0344d041d4025003034990344d1074103c04440c0a04079000c0c212030450b03600214180c142e071040c414a070a066050350b94502a5240000031581400703401c80d4018055420840040d181c1d40074031541c001042c4905a10749149094100502100c002080d801a41c208104000f07541f9038038181161480954205010400403000740421181d00030369213032060500106c4d0754020390540020301e0a01c00d0200b40e807100841d080c2202c12075100c0c2140c01c104161518a80c80c01d000081a070713000f03400041a0380602a440c500700780c40b04000d40342001545829a55034000324010994040241e1010b40000d540c10b000482c45060650f5480074010840300420a60480c001800b51003441300706055540c01c8110303401410207080050b01c6105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 197460908 1250 197459658 197459681
    0x230601050f06030903030c031021022d010f030212010f03021219080a030b1011060610120b0d0b0c0406021504080316020f0d180f0803031f150201 64
    0x141d5060006003841e0900803a4032072107245010b035085031500707520030302d0a0300f028008540c1c101808602140e4000f41d010b0540d6021a45402c6902e450440e00500400015a004540e051041000f80d4100116071900000c80402c0a10302041c0c1c0e21009a0100c0007401078522400c03004942d000005610b81c4182c210324143c90007220705010b04020380c62600c1c0e4890700c1c825480000c0410f9040c400104081101800c200000390502145004400000031440c2000001080101c0c41c040d044050303d6100f00544c6074441c0c0203558200845e03805100180601d03030101c901803000d5454000c2c05103141c691030402c0888a5100d00212500c0c10300682d89403554116024003c0180f040c00760801a00c07029100880c007641e0800002451600d880c16081034505121645009602c80e148403500107000801c4503401e00110340e40c6000c40207110851840d04110f03180c0c4844480d86038050140110200070003103e4100e000c03040030722038400e0301c0e846260100f4055480010080320068030000c100c2d8064004506289 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 197462158 1250 197460908 197460919
    0x41e050a060c032d0225051e150603150109051509150d170304030c0501050705040308070b1803030709081509150711030403030c110d11060901110a0c0e0f012123060105 74
    0x8c405144483e078007580f80d072a888030340d88803a009082c00900b02401f00d400000183c1650744069421a2920201c0c0e0b00380c2c4460581a500d400300b2400514045d907921740400200c910030b84505002c003200404803041c5892521a00c51414004100407681d00e020100f030700c84000050300c0745050b04010b000c141c21040162059402c0900048007944a1307008c40f41502c5c4e2001040d42401c1160f11080e0020b0b000509070340d8800b1802007080510f820400240d4815840750b42c80c0b9840d18100900c881c01c0c80c0d502c1c07024488038001102840008031002c101440c03d1700c01a0100c08a540e102c00003180c42401403948003125010001e000f000f4503074895001c4107003c0c050600300d0f01e107078054014445201c80340710b000f2b4400703007d64584101d0386c0ba01c44014100d0443c1490800b2206800341c04050500800c400200e41e0300160540400a02004c0352005511003180d000794074a42d8948a4907102c40b1030364956040070b00141c0d0070810100101d20300c098032029a2200038000700c0034080da0a5964907400e000c4c02d80300c1c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 197463408 1250 197462158 197462173
    0x8011b12060803030a090305090a0e0108010c02030c060a02130e070804171c0b010504090608010b1809060403182c13020f09041e050a060c032d022505 66
    0x59025028110495090b100254035641e103503400710008002d4001c045003003100400814025503034180000340900511400d07020b82e54948903070a821111254458420340d041449000342610000c00c846a003341c00f540007580d40d01260351000030720141c0e40c002d41084d012110521107042c0d4815001c511651088104a43c5990201c0300404a40112480d00017035400f000241d1f4252222034010f1080d0802c18101941010b4542801c0c8056418503006034416039941e201303114051a0204028a00c08803551020b015420b00c21103094440e40d004101800f4409403100391071020000000c3c60300186902e0392803031044007204407500d10030020f140c0703c00c9002006401260340903601035400c0b0450f030780c0280701c1e490007441072040c01201d0000602c00c0d5402010101c0840058205005010b48180701e200504403041c550b02d00601103030200c02d0060100b500e880e03400d41c400b0408014041c88030b0320480b540c00041d201040a00c0281c03081c0030b0300d024000403181c4c00e104030710080844212224130a60541d03810 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 197464658 1250 197463408 197463437
    0x20d020315090706090e04020d260c150103030831080d050702030406091a070501240603061503050402130c0201090c0504050403021f02040905040b01061b0305031f08011b 75
    0x1710814040ca003c94410500890014a00107aa540501e4813800f4480c0d00c4000078a05d080e00c168a0140c4020388180000e4060340fa03031014030041d050207140902d02100c95040da14002c028040082c0b50ac03014804a45255214680301c224140075030004051200d11a441d520300400c90790065812a04418149001b0500a500201c15107065540941d10610703010302c5c1001c03202650300381d40d008206850081003d0350108400780504041d080d1082c00480422004241c2010388221940c010700c10985009418020031402100d18041e001c10740c0780c0071a05445500004002c2c2000748101c44807140b8003c41c03400591340640110400314001c015040d8883d544109000c16104100c0d001001078201804100c01d030542150040f88000c0e5048005050684500f2408200c40d41941c0644000003403d00400180b60300c0b1034000b04006a952581c40401d14598001e0014000039181c65a0140d640d015040b41d011102440b0005104050092204450300e41044856000e01c500000001d01c00010117840c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 197465908 1250 197464658 197464667
    0xc110d0c12050a0e09010b120f011d090114040501050a0b04021908130b01030b0f0a0b0a0302150c01020f07140f0c22021201080715090e04020d020315090706 69
    0x68080e001080240020300d008400c4602e079010070f4054091202c14050803200d52208102107019010b10001e2555801603240c421040000007001d09088003800d400602c00a450070011243ca5516180c0b001a140c5441805034017604240a49802c01441c01c2d00300300520038150840c9001d0840700504011034ad000006000980c810b03209642505407001d060041c6051142145552100154100c450b9266560740e0301d0000060a03802a1507000401090220702243c01101c581c00c542400e404222502103c0d003c502e28800c14030021380b0a600c00c260714001013810b8011a90160170900003190340341e01448081c10b03560000e100a9503170708450b0b8030754180c48600180b111004605030000f00b203840d0104080000d80c070201d5268003001c4c880c41c540031513054014000b600a900e02c1e0034a5039003940c14040024a440c0942d8408054072008060794140340740c201081d00155050f00001e0000c0e0307611800030413071000f440c15000b50144294108451407002000392140104051819580718550301c000496 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 197467158 1250 197465908 197465927
    0x50307031d1f110415030e0d030507030c053901020c06010f0608091e030d02030106020d120507050d09050109020306010b0406030605031b0d230d021005010806040212030d0c110d 78
    0x1e483c6408010502604614042559000b0528540450180c0c84503e00c2d50418500c194000080f9403610140402d440c1c140c0034171413403d940b514189007000340c4030607030589846035042841400152022098404001c50850b940200301c414001e41d510800d108480d0f640345424420703048103120040c004a42c251003400900e002d64180b4000f00b03000c03c003010f0100c014001005002c2c2d6544410414044501514000355008150b5600900502ca040700c40c094180c0c403042c61100e0a8900d0902008070040d003001c160745080f42c10440005035815035207407290041a0b00746c006941031080b600002650380210001303206032500340c0c1d0140803141d80d0302c0c01e16540d0a2294102c0003908007443c52008541050300e0262445030103116000c0d401c038400511141e415a01d02050500d94100e40302441025070100705041c03410728030b40010842da40c5003100f0b0030b840e020040c2000788500403801d202d00e000d00701001610707448120100e041010220082c0c001d8450507650414aa40f4003c40308842001030194102a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 197468408 1250 197467158 197467181
    0x80c03030a0905060c0a1a07081e160903020a03060506030f010b0a270501090e01180507050609031e0309100e0f13060b0301030b041b06090501050307031d1f 69
    0x40750b07014107020400c81c994002c543c036090f00f4410401c3c1c03078010462000385c0300c002c4000c02508000908040f20300420982d4001c040c00007407801c0041400d59030b2265220b03141e00c213452404d492091080c2400407903081c0101d501c003a5012001c10008000c1c849640c1c0264000c0100f1021204190400c2e0082400d03180a846429805110303200204031854101c40700303000d00015104048010005045000c00b200d000380c000400040d13407260701402a1400b4840c0068080c42d104807aa0003030950f580301a5507c02c01d00805010380702c0450f00c44c3d210380b020803c1c0500d400441c0301e00c0c034000121b040c180365680c000d4002d02d0b200d0910910303031407080c034040c20484a00a0b405042044000011800e00003200038090347d91a070b941e958000014607070102405940658410041c0c8081d0781030604048440200090501d10041c2c9101410024181c1095414080f254282440c43d280c0e80c500b9019170040c6400440b5848160480c80ba40c02942c1e0081b41c2c250324810201e288140710600c64507030300229103989600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 197469658 1250 197468408 197468417
    0x9090d0e1519110a0506060405060604050604090b1903061a04020a0f081b0c07030c080303060d0b0a0b0409030807090602120a0507020a150503010923040b07020f060907080c03030a 79
    0x14041d442e00c9040c54520640701402c00d0f0741c1403140c0c403625900d0710103002c805848540249050106514150007619040342089500c241810304003400500c592145100d44150710b50307500000641525880228452003919241803074059589007048005485501c140100031103811891040d00d01c2d051003a14118549079907121540a903152003a9280c0d107001d000c07181018041080c500c880e8980c07200402c2e12852030310141c0403640c518076120300428060340011030203030014400c101c0d260320380c5004800110707005102010581c440390400001440148252900a41042c0704da00070b1541015403540a00321030b64170007140580d01d50303040741c503a8450283e4a20001040100d11802c901c580080c0540d140003d05c0c00d000c2d00c2d81c3e80440c0c501d03a01c0303901564002c10300200c01000b003454076214011400b40c485001302d01d894601401c600c0d04080040000701030504520104280c180b08010b10052100644100c80e268200712480a1707036010b40d84201d0072184140305508845040100c1520b40805a6484 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 197470908 1250 197469658 197469667
    0x106050a050406030c02070810060501110c01050307051804020d02071112060118020c06071806050a0906052101060e030705010201110307080405030d060b070309062c0f09090d0e15 79
    0xf0450141c12071807a4082148505d170070120b002c100500400d9200b4100c07078000500e5a1401002400007202190807101c00c0e001000c0c8501d2a1f41c00c10b048039449480c4c4d1600130307034690b046506a424402d05032105a045031002c11181240c80041c1c2c010305500e0300424a40c18184441c000704410072410303020244c0950051001000000811410390042c01c284003005400c000d00d8005082c5454022500c00c1c00050b01c40990b8407c90b2161000400a0080c5191a030b00d0a00c031200c000e00544940c0c4100740c02c0290016248443c189503604204104841040341c090950f500d0304003c1c075100784d2680300d902c64050181c00047c0c81d03005100d01380c510501d01c00d150342503541e00f0400342d400b8540100155002c0c04100101d4144480e03a02c21300000e44034510100f502c0f20480d0900902d05203050300310409014592655052001049801e060b08208940c44194890013001c00714021102d140b600a4200303502d0700600c0321880001c9007184804100b41c2d035074050300002c01c00b041003d0a6600301181d07494410407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 197472158 1250 197470908 197470919
    0x17150307090c05091c03140a0503010b091c110a050d1104020702060c06010608040b0a0e03030a09240504050609010903082d010815090c030c0108100f0e09060106050a0504 75
    0x1007018070074501c28100241001070401c04218818400c860000d00061030104c213200309600f07d40c03420201380354014410304280130f1700d2002e481c510060042e03504402c3d0114500d00d1642e211401c400800581e0034030f075408102c0c6441d2030661060181107161044240c00e10124840c20001c08007202d280d0442902500c0324011001d000003980b1081069030000340c02c1140111501c81041558004c05842d6103101180c0b0741402e100084400c00b800303054009060903a02c00101c0e00c0003098981280134480001050b910314609404e20305d08a0038054040c07900740000f0304044000707a1215118500178829600295504440c050803140c1100d030017004a00000c01144064001d4003c0c64a1208100c0200c038500481c554499440d9200742d1120f60a5800320404061840d41c01100da074101d00c0c0c100052810342850400030b0b44482225042c1c4d070400040c6e400103400b49074041c0490004040001e100341c46640c031102d82e090b01a000710303100c1a192103502c000281c020320450442e60111615643c940c140303824071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 197473408 1250 197472158 197472161
    0xc130b0a21060204271b110f06090102041e05060322021302071a07090b1809100f140d060c020a120503010602010b01081e0702030c030a1715030709 65
    0x441c1004000d11030049900c0000c0c0c0c840c030040024258282100e0508052010540540c0b0303400c052204015082a0a2074242c0f020700342c0300880340103241040000030514010240c60130031030140100030351085e00706010103950194010001e40b280002d0601c03603c40e003445410300c5c5006a11070190850700030000600d5149103660a01d03500e4880030140d10900d49030340c00041b11000010702140d8003a600040c14002c00c81c84080c0c8004104211040c0720082c541030b9000b9202c844207106a1480040003c1c2954400c4400d0080c494104001041c0c44403034140345524180c0b00c0031901031081d08400000c004107170000c0110161503d100c0c0280911180c030203682c0c50784060000e400300b10307056102d280b240000140380800001d0f011903240d40c03101c2d03c035071401c44d00a096880604030319041c041088180000e0440c1c80741001508507401c2980c5c100754032a450201c2c614407860716070b20424000422615901c951103980b0070804106049030f0b40c00f60722190940304404068951590340359005070720402c1050302c213 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 197474658 1250 197473408 197473439
    0x3060b0a110703050105010303090504050a05090705090a0b0a0b0d0e032b23061903050a0206031b03070306031101030605010203120a020f1303020a090e0307030806130207050c130b0a 80
    0x4000695106690fa5650380303082d14403c0e04210049207403813909100500b403910070151700442009003448242441c2865513260f40d118003960f4081c45004001400711500d0f60803004a9180c060451300b90b069507060303c840c0d81d41003134506014140c1403010311401b000700001a10324642041e4140c1c00d004418502084409a010080341015500c6060007022518890210072841c10740c090f0030406450000100305054034140c07940171401a000d801400030800002e81070107042c0c0c0c150f41d610340e03030f40700d8890540d079035107145400249042d400420440b05030391640002c03044074419502403c4501780c02d00150192041340c0103450060340f040c070811000c800f00140a42e00412020801464003005800c1e83c04294040d0500780c07048010020100210f00748000703d0402015280d408100d4600381403c030750b8813881f4200010342084000e401054155030791707440569a41c44130100465035101c040c40c18a0b101c40c80643e62503c01d00582d41e00d03558800c0c1034020320b0041790009265419443c1400f0038071a14004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 197475908 1250 197474658 197474687
    0xf08040507090606030906110a020a0f060b04050126010902090705220b0a091a19050d1505031c080c0c10060303320301051302071b080c0103060b0a 65
    0xa40c030700001d42c00c0c560b100d01000390820f9500031075150301034200707081510384071000c01c8410201040301003a01e0381c0c0495100c40d03555101c0d1307200d000c40c1c00604140f006000c050104962046c50310b400051840340b81e0400b40e490904080c0c5206500b412820014200d4880c41d074040c2d0000c0c001d50000702501e100d28000c028070b00900d90b03014210000b44000c825280c010b074001602d81007000403c00843c80c0c00418120040503603030001d06035800b40f2a0040d402d402512a2100ca9004180740d510b1214007230f0041d01d1035030007000d10401c544600101032182118440c410755009008902e4000107101c40321266080518064035203c5154aa20142910507408620882214040d98820f405c00203c1d60145200a600a542c2d030320b80008107214540c1c001e040b02c0f9848600098842001c44030740c0840d02582d0440d502120301030742c5180c03c6d10303441010b44601e01c0e0042074803010001c103424100c2c03141002d50a0b07032414000c603901c2d00882d030b00560407a070960003004110001401286640e0340b02d08940d55101c41c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 197477158 1250 197475908 197475913
    0x3050d09020301200d110309070603020a0c05030a090f060201050708150f130603030801060c0c030206130b03190605031207140a02060a020706030c1b02010c0206090a030812090d0f080405 82
    0x10000804150070a16141944c20380c9000207a0180d00000310f00504144040c940200c52450511035009075540e2072600ca4031043c1a004521000114000e4421400441d00401540d6441c210a18000c0c040d040350300401030800204040412030b2441403084c0740c4140c0350783d00d079020745449036220140c41242e040d401e075520400741c841400147e1281a80c8104c0c40f003283c000801c0c240c3c114a0080c0c0301100580013072080200207032004000c1741210305544120703501982e50ba80e4451292070300100c02c0d07600b034010290344c180010030701049603865599990000c000a90401902e6141c000309600c41d280a69400050002804080082600010000c025481c0e400031103050302180d81c045540c94106103119002341c6c1108200300f003078603051b0140c694a007903185803503250300004a40815a00900e000064100402d940c40c000c03c40d203805c0d00700c500b0400300801c80e070b1f203282e980d00d090b0b00c06500c01c030b07421020300d81c0040200c3c224280016038541d610180741c513020b1410a0405080b01d014030020300568962 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 197478408 1250 197477158 197477171
    0x90b012d230c03072321041703120703022106060910090e1501050307050c071a07060f060e1308130905060f090103030e040c0509040e070e0c040303050d09020301 71
    0x7902070401040781a150602958840b981070501e800c0c0e101203000c902144c80d0328200c2054051401064110a1401c01540f60b0280b10b201c0f804421a40038580016071104800c203140ca15403000080642485c0780031084904150b03a03640412400c1c2c0c011207040302c003481c0400d0901220440c0f82007216500400152045042c4652000099078480c05280030700082504102e0500c41d482c008401c4c42e510100d0170009011603841384000134401d00c4000c00000070800c0101d5403000c01c7c01d060154000034403010340c10217500444100b980c0b00301d5110603c101c5d10030b0b240c88085101c00c02940159001c6030039171a03200d021a6503200d1441d640f010104021101c02c0420410a94041c01941c01d00000e4900e000e80010585400070038001c0707d5200700c1c00684691860301c01000044d50020124900c41c01c143d4002c50810365045040d100d60081039010b17070303209040102c1031009000000c3c640d0125904021580c0e41c40c1c40d4041c81a07414400da000150001e07004001000341000303590400c540407071010b00001100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 197479658 1250 197478408 197478467
    0x20d0209090705031b03070c060506041509151202180402010c1b03060609290f180601030513120c021201050a06080d172a0301090b012d 60
    0x980740440b5600c01040c40441070003030050150350801c048920024001d03155040910000c1c00c5c0b40201c4500401031030f240c1000034481e4843e604407151804030045042ca5554031f4204a40181607444004490084030201c00121881005d821000c069005800e106020503400b580d1124160000c000303038140400e800e25400001e510f43e26000c150403500321010101e90940c50004191210b581c003103a101420802010707008003041400c220103044a400c00501440c2020228484100e0303c1c44c0030f03a2244100b558a840c102d4100c046d688a10000d90741001550340c2c0030b1504554508682002d40050446001c44141d50301501d14201e003e400144104c9400840c01c10742800d481c000c480140c800d60300d510f410401d424003000000c81c540721508004109614100010403c1c41c1d0081c03400070300b00d169903001626500c045075401d90144006000950303070344e126507070000070b0040e103445c00d03000881c1100c06500b0966040000400302e10050f42d0482c1d014144002203951741c1d214040c90f40d00035174240e450402c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 197480908 1250 197479658 197479669
    0xc050a0807030507050103140a050a200304021005040f030318170a060f0209181302041d06070302070b0a0e10050a0b0a15050f0a110d09080105090d0f03020d0209 71
    0x40032028024000c440c11490864207106041d44454103242c180b40400c1205040b9424840d84400c10704800035056440611b10782c0a0a581c42d081c107008001c01080d1680d0403120b00046102e14004c0e43c1503a80d5a01009040361a88514400c4110a522103903080c0006031182ea03001c1c103a4004514102d003515180d0255000001203d28140d40f00c0c3d0140c00c03100b0820256010f29556504001e00850510101201080103c0d800d44a0800303c00c0203140054003003000c0c83c00c4107044e0380d0060b004110010035502104450a048155001507104010020308000c2c402d000f150038503907110444916640710802c0d003d010f8480030040e201c950144107920807182c60188550b078400c111700310b00442c54500761000e210680740e8940212083c624000c0340d085003590010110340040062113001551888640340444018108144160f0076004410000c41c91562000502080c0d0f84220000c10694490309100c82c0d5802c00c1c60640fa002c64004110540140d010754040e00c142c01c6510ba0241c50f00b01c90070700280 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 197482014 1106 197480908 197480929
    0x1090206191205010801050601120b010219020d060c08101712130b04030b0a0c020a05070506030a060305031b010c230f07060c030509010b03070303080c070c05 70
    0x104602d201d280180110070104108214650311240c6442c041c0106865960001d04150440900340045100d07403014103d051b0014000f44100c480030300f003080085401a41d00080301111600800c1d100d00480c070910086958011140c9046c41c185006902c16030040d001c07041c514104031901200010340d07256000804031650362a000ca18a0461604019810210200b0340104d0b00008000b051640c0d14001c2c00c1700c5a080c043d8481201c403ca82c1c95502c03460142403503011590400060904400030350304983d5140e000b0480715100c1e03c0e8bca1035980541006011060140410321480100388141000804145403010b60780040012130352400300c2441f01c540d040311000030f808910b01c0c52502200e500b5980100f00f441010a600e001034014102150380e03415550806100c8012440c010039082c09903036043e2130b22612a103403000204c84940006004480e00542c04d40049484d90b41c00300d030704 = true := by decide +kernel

theorem cover : BRFrame.Cov 197302158 197482014 := by
  have h0 := BRFrame.cov_init 197302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 197302158 ≤ n) (h2 : n < 197482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
