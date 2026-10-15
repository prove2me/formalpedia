-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:34:17.940386+00:00
-- url     : https://prove2.me/submissions/1219e6e3-0560-4fb2-a245-1f19f7914867

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 907553956 ≤ n < 907733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 907555206 1250 907553956 907554023
    0x11a040207020f0909030301060206010f080a1103011d01020a09060206060a140d05030301062d0207180b0d0636020f010903080a110f0706020a0803060a12080c100603 73
    0x10010900f480000d030404c0300aa070307428401e5001100500c551b07501080200d001d01151010400078516040609030341d80001d6000615098940100d080305440c00d40000000240c0c4181625005040d0482c00b4001d400081802001a06c88180002e40600124505028601c0036202d82c00107401c0c00c0b008080c0c1c0c1328414001d030300701001000000100f84107002560180509a03600e25400c54441102a8000390403521007411118480c4d94400c019000611803044400054061a40c0580900c605008264068800c0e0300b020501c600d0780c00300811540309189940c407050056618482444501d800840840c1d0312305107590107219000050b1802c100070080846051402c850116141d40e90341c0110f8004c00400d82c08282442c09c00004458180f000402031002d041c001c151051400e40001e54030348080d03402030300a2000201261060301d9100c071070400307054500004600d40c03000d803620940e41d9100700640700c0103004a107801c0d10440d05070301480044a81003948036840380180212600035510414111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 907556456 1250 907555206 907555219
    0x60302041823040606030507050f01050a031d0304030303050406050a0204030804093b0c030609150606070f08040608010806010506030a02092808100212070507110301060b0c0f011a04020702 83
    0x11058050b028280e43c80759226500c04600c1602e11704e0024502011a00418860410451207a00e2039902c00d00340ca041c5502454045164051320420b176152609403480d40401e800005000300c18181c050700002c2c06284551790400840d500c443c0140200e02031800010034425081004000e13284a17030300300d00546030704104400342510030780038406080c10960303801c1c0c030741501d50700150030724110300f0300c4900d041321400d40c09408145041c0d00c0da0758580b1182c0a0301d10a03100701402080840d29000243c442150b80500c0190945403607041036400d41d00706105000024420800220b201040452080d040341e0f000f90a082c216100c030748450b006500a0b402e82c0e60454054802e829624010800d5001c04000c0300f900000740904081d6500e04186401c00310107102401048001c20a404620340c3d50ba100341e0514025464403550b1511111008658020903070541c05c18070003103415a803032801032410f00c291000300d440c4030a15128040c03d036810b046c041440710300da41740001500c1c242900100111071006008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 907557706 1250 907556456 907556501
    0x80a1106150f1003140f2203022a0607050f06090c10050711031002030105010e0103060e06120a1202010221070f1209050a050d080f0c04031203110703020f070603020418 74
    0x8691440c0702280e4440c4071852500a21280f00030a1886000c400c015030a424101030860710003960300c140d048080c1c9030034900f01c000344d00ca140d0b0080c6403c0ac1e101c8001c141d591f85003020b060441c0d0380c107110750030b0620358042c1d4070214151860021b64884c001402420f01c0014502c0c204050701e4941120100340c0313604100c0000040c0f10b0787c0038480980003103044080181c80e941000001800360803040140d1341418034214043c0224901c2c0044940e0082003200c0b81550041004112410b120140c84018140c0b0303810a8402005078064014000708410703141401c0c04042c0d80c400341000c10030300780e030082e01240c1240c1c01c00f040c5620a10650000032011038000c0340f1183c069403107901d0800307500c005542c650002846a500250b0100300b41c0d420445184408050f8200512020801c0c03280340300050024115214507413038035001e50040111030390700801e005c1d1140075070b0401070345a000b003e0105006004400c80840d040303000b0b100f42c8060302c0703642440041c1816482c0d5100c0013403201c0d02882e160180642c0c80c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 907558956 1250 907557706 907557731
    0x902030c0412211110050a021b1c090e1603110c0606122406010c02040e0a0209100602030702040209040f050c0c070e040b04020616080a1106150f1003 66
    0x280340030003038030410032200181d50903440040400f0001e00c1080070404054811980c481c03001400c080404170006001602d80c6130003201d500203215038100015824684021614200000300f010440c402201c03042400c0340c04032000440380812240036002558960801080030320714a56203100b107101c40c2d4100091000030010189455812a00b102c0ad400c0c0c1c420400c12609041c400220400b20805d04003d091401400310003490784032907181e0300343d070104040e00080e000d41e114515540046401034030070040903220750a001e40301c010b07000c0d050b4011040310b00070441e442c00c501080012265680c0c0a0340c1806801d80c01c0101940c05046d01d198415110f010020400c2100d01c2038a00901081e0b6886645844c01c0d1801030030103801c0d5000b460140d00c902d0400010601d0ba011090307000b6411601d8030baa0701d03244104141c81d40403402c00902003c2c4007081542003940c2005444070400b40750750448119540d184101c0704036103080f0b0062500000082c08941c101d0420322a090441425402d020030101142132 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 907560206 1250 907558956 907558979
    0x2401140105161103070902030c04050a050a080d0c0606051008180c0907050a03020c120306190312110f0604050607030b0a050307050d05150405011401140906090702030706021303020307061106010902030c04 90
    0x5802c0c274045c5800103000c105030701d0500d80c400000c2c641038851411a9143c1405d007525280b61038104400c0c0715003041c000c801c111150707009070040d00300200300821a0403c3c05009010741382c21180302c0705103014456070600e86000041c4640305e070b0900901c0d50b4403a40c0c0b080c100b21015081003003644203143d002e010900305548107020030080d00c40c00b0000036440740750510820140342c0c40c094034045000c802e90000e101169001c180c2d0b07030311a5090700380100c0120b400002140b501910801c007004074001c071000d0001304103003c034455005025550b030a00034520180c0400c00f40031000e01c03d00360b05d40c0c807150082203d41420344040300d000340141c0c16105070000c4102140301e802400c071002c594607592550f0302a482c0801000b00c9000d031a00c1040d1041050040d80442d16910001c1c1143c0e21070307510000000c0d4191b10810484040540c0504255103d00e1a080d00602c20001c0f40000c03482030184481c0416220700c510340801040000320300034451a440c1c6840c10000354006843c642c0c41e440108400700c0d80d080300c0d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 907561456 1250 907560206 907560211
    0x6040809041e200403081602010c0b0f010501120605010e0d0c1205030910030c0e043c0c021f090501090c15020106050910031103240114010516110307090203 69
    0x5903000f00c0c3c214061803002c80341c0f6a03505400b182120301880103102003058541903ea03c1c004a441d2a0f0140c40a400144d600e80c00d10000100164665070401240c04018280d0504842081c0c07602000400e10101c92810b43e461405101e0004546912511040c6003085031444c29500491007030301040d444003280360038007103512010740b995440092014810304141d015551400010b14081240800405005102d0350740d00409610460f01c0e4402540207080100c490201c03c110340320750210214900d41d60f034050241411410051030f1503c00c51b03018050002c5004c0302c0c00014401c0c10a4031000030382d2a84001e188544041d00c0a641e108450310000b0450000c10002d808155402002e290030040002d085d1017071900b280c1d00681c0e2003003d03c940401c054100c541920343c07103004c1014603c40714001c0781c5003d06407036000000152212620348004480641c1d181654001e412000030300b00500c2c01510144074500190b40122454038a1310040380030250b010352603240050a9a8502e5515556002642c005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 907562706 1250 907561456 907561511
    0x2041d060105100c30051809010311011107210302120306090403230301061713120f030f0906020405030f01140c2b1b09081c020a150605010f030e0604080904 69
    0x6e01445c20384807181440400c5e0301c013181c6500649d81540d5900e45003125000000e41403240a241e00c804201091100102400109a050895161449425003840d606900c142c000d40030b400f4000820381c0d1103500312882018084c0c10b182003504c40d40e0f41260340100c2418241f0150f600d16400e800b2010072040114006d04944c1c3e41c04081c000104540c10351080d018251100d150354121009000a400b110034503240ca1040c101000da0010790b100c194040c091751424011114a408504c0040207029030103002682d0302507040310840d28441d0306990880d000303c015a502442c90a0005041244280083c6500203600c0340b4419204031a0001061122814041c0d103100340e2202c0001d801c1910000c60400c5a0030384e407800b240321034a008070ba80c0e200c2c040c021250900300d44030352071514039a00811601249a5000d66056825260590f41d48020446030007424005408080c4030160644203001c1c64150080da6805400d8589503540c410140754001111940c0190303c0b501d40074070786001004a14441343c0e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 907563956 1250 907562706 907562717
    0xb04081c1b050c091e0411010509030f0a05060702032d090915030609240a0b0a090c020d0302030402011205060f060f04030c3f02041d060105100c30 65
    0x4000041040d40034005007198054500d81c5104914880b80c0c0c00c0d071710b0704a9007000f040c0c207000c440d000040356103105000d03006825101e0b0308031141c5221000600400c0c150f014806540e003d44170402d040f40c0300d1094603c0c0000c90054460720900b100a03440314001a080c0502c81c29191145240224004900171960031140941000b50000035060130312000382c2c0110480040c1c8005941280703807030380007880c0c1c0214900d101c4103400001c04c4481240d100f0030f1000401002000610343d107005c40c001130b0401425140042c042c41c40a42905400381c002c4c0e900481e4140c507003c10416416110324020140100007540c01480082900070580301c003001060501c0c1e040304080c0d81c0318110f09000c00c082e0ba007a0301052358403800f50100303440a03854045601e2a44150350703010b40d03124126845200d000c0d00180b0080c0d0b2040c41c0144a011000c050602d81150010000640d111680c1e00c504000081034080440f0001c20010880f0000041088002c00c0001e1441f41e4070000f541095040d0440103224081c00e20007085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 907565206 1250 907563956 907563973
    0x5090708030a020d1809050f0403030f06050a0504151e06170c0906030a0b04021b0c0f011d04091a0f100f090b0d050f06010f0b04081c1b05 61
    0x54051004001509038200150729000704004001d507502ca00e050742c2d8040000f88664404000c0956401714010a4406c40c00d020500708000608000d1005907005c5011030b180c80900d502050f487d0190b802160b00c02032a000415140c14140009044d820381641c1c00034174090004a4240610031003030340c40003d441a03103040c003030802c50040d11100d01c054651441c0d010440c00c10034002d80c1c00c42111807400084c3e804903100d480301c02d144400b400340c0443c0c29601500200c2d14002030348a000401a60304102402c5076110400c240c10300600e5400401618001031009590320070743c0f42003076901e150701e95000d40000356440c11a05d4062269039040c08604014101400b88038503541005000c540156855100c140079618091030304030350b210203106540c9025102c144c1100c11340d0354010b20f07001e42504a0265018003100d6441c0e6600d8076424010074005007440040030403016008010399013a240baa5005000d01c18400c00c07440e040c0300c141840c0108001300840002d4101141062010140b4860b070300500049 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 907566456 1250 907565206 907565221
    0x90f040f080708270310020405090408070311150613140606220b03010312090f0302010e150309010f0e0c01051e13080714040903080a0c0e0303040303050c0c06090a060f05120a05 78
    0xb03c1b10102c100c154900503c420321443d680d00401035002944822541d503078900178541506e49174081000a001409507110110365442c51820b05480f8000c1120000503119080b05400c1c129428400800308481072640040c02d80c0c00c020f00101401c0d5140888400324010710644001302c40341540040584c214040010010884c000140a01c00c1d80c50381031110f091414203405d1880316140d84400313410010801e032401441e4a50b880b20f46025500340140c0307552446c0c0014014040c04084001c000c60382d00d80844004000d50207d051454420140d4801d4582040b12415440030888261043d840420800c0f80c8100c21216600c4070b802403414501a05101e841d0011024060b50340b0040940501e040110a1000035403085100368844132240d000504018501070881d0071114a001c00d81d09131100007404410f01d40c1080103450440040e00c2100e00014900c2c040c081c0f00d0007111000c982240c2205024422180150303840ea46500746490f11900f01a01d20380328440300101a00c180c008030790f036070701840340a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 907567706 1250 907566456 907566463
    0x1902030c0f010c020604031d040e0c0f0f1c0203010e06130303050f060619020f03130509180c01050d0f02070c0e0f01230114070302060105090f040f0807082703 70
    0x100381004003c12100400d50800b03504c2e20750040009003004580c80c6080c1c01126000d00c22411840040c100700324008010416954480090024034800c06115010740450b2905014141c01110050040024100c0511511584800480080360305540f11000124084020008030748681e4071690340102504585c00c02034200c5001600e0103403001c00d01420041f160700c0b290200c5100e00540318002d140c10b240c4000417810040380c5180f01d889400000b504107120b022112084055801c200c0301d00e2901c2c1c4540c1c900015000c5541304404540d042a007100c500341d0b0040c0050300c94025060808900b0380075144030310b01240c0c03282d4022114421081c100307010318014080c41940c0304280003481c82c980d50412040245800000b020001850110080b00b42c450340b15161004c072540b49540081e0300c500c4907240c0a501c0e0a02400b445014410103c00075101c00d006007a001d00a0303420403038100c0280384645500c486035200c5c1d202a98941002c21000040c031011141000071384003c0c021201000c101103041504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 907568956 1250 907567706 907567723
    0x2070c0503061329040b0a1b0810060c0519030c15020310050108070801210b0c03061c1e170a0914040204230a0e0a0605150304030e0f061902030c 64
    0x41c41c144c07103d009401000c12004181c4c2007600440c801006644036074500c806810755114190398202054003440103030f6001221f450003240f091800b040da00d511560100c8071090350420103006684003080801c10043e4004000c85424064600004100d03100d403141a0400d054416011404e680042000b40d001e00110b49400544000d10b0045124100350000824108042c003600c030389019403029550010071100e07042c401540e030000701e52042c0e150030380c05400150012150a40101160f00350f40500314801e0048442d0035500001507010391a1400c09105404592078040b50102442d1005070f0070300e04203d016110600031540c0b11404213042030b801d0b4aa01003a10341e0300e07002c1da0050000340409400391181d52000007192401c800040391b0704000410000d4582d00040e005000d61003401480e03482c9801c454140c910595040e5040240740d20410040d20040303c1c0600000c1001002e4611460400c12442020030f00030003150805042031407201c03e8041045559000d03030303c000340490314044140407018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 907570206 1250 907568956 907568993
    0x33c0c010c1b120203090d1401050f0f011a04090e030702040c0504081b0f301c0318060204060203041403191407081222051302070c05030613 62
    0x34800d40900c851002c011000106102010110003603242d108105446408030000c0000c1c2d168012420105121142082c00800550805d000640034000400d0120300862220781c1c1c40010760b1038011303504c070070039025140d0ba00c215100308070018503440b80740a1100060b26450143d607441c04144100011610224050010700005002c04c005906020500380803840030515050220701015001410f0740c018009115071101c164100361700400122885540c80da2210341c1030880b00b140b0610003607524040c42c00c0124262126420641b25507103c0c0e00241c1c4841c41a40503403c0011455a60307070284d07000380d085000141d2010904100491a14251030089003094000d40580c1c01c294441500c14a00d2a0380a090302c858851020740101003003000c1802401c03044181c0c0c0000e00c24103a074000c16813204510742900c10207884d00840b039160070000c680c11110020032160303554940c40790f0030300a900112020350b03140d881c8001c00940e907142400400d10480d07025810b00b401c01e0341844e000d00710600445409 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 907571456 1250 907570206 907570217
    0x3010e0718120503040906080a051902060a0f020f060705091003020c0304061815020705090c27150d05070f0804050a0305030c07080a120501090905033c0c010c 70
    0x200301c81d940030403001d8107a92094200010b82c400d1400e2152852090342d00846030540345c4171001900050201e194104544204141d88601c3c0001341311016050355180041d600400400c0344078011806014440440f85143c0140ca45024444020509121045840d10007140b8000342001d802c0c0f90401c01450846100c0c1030841c2021420381201c1d80d03900550107200c040c040d0099521100f2902c1c1e4003400d0040c240001d1905490029400094a803017140c03044900412695022401a80b02d8806403820300215500c00306146007914049030210086c0065540c00c000c03e040d000610b0300b40c14004001c41c07030803100040750714280034500401024014502c403040042d45028440003d01c04034001c02841e816140040c0c1f203840d81040e00c45035218101c0010160480004d8400b40c590304800c10b900ca109003800108126a030741c0040005581140c00000c000ba00100108801510111b50901d002d81e4480303000e108480002030500007000c03030401034040b00040450340e10041d0350709004401304900c461404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 907572706 1250 907571456 907571477
    0x35071e0f081504020c0d2304081504030318030806090f0106050a0503150a120b01080c0a181b2c09060d1713030510020702031c2303010e07 61
    0xe05000000e014078240355440e00c5101c0c1283e440790152000c07020352000381d481e49415200050f10014801607403500c00d42c14440d4440c529011081603808940d540c0c0c014041001041d05482280e04008104070245a0703600301e50010100d849106280543c0b194940100504260307040194469000f486c4034200c035003440050000c81d034080d06440c048021428001d4176074960309072003c15219140119500f00080d00e0000501c44000c0b45880c0f640740c050129440d042e600c6000e000e44880384040b8a03a000304103c40708000b006448900307240680030b0031400003072007069940040082c0205d422110002480c609048210180028940d020820355139890303009511401c002c00c4001d14024801071003a20501400018800c2c08103d090300345241c2407a2030303a2500e070005885180380050009035502d10a4014040d02004948201e50b00b845d0000c001b091840f030080c121624402002d010801000a00b500c001c0501484c40c20048494908003141520380d07040000003403640300003c011074100310308901c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 907573956 1250 907572706 907572737
    0xc083a0e0a08090d0819030501050405061212180406060f08161403060324101a070f1b0b030414010c0e130b090a020406020c0d0335071e 60
    0x2128200c04095801c00c0c110082d40c2172032085e40c0600020304a940280002c1c208070168564810f41c140d030b8040380c0c2000a88c446005018115042401c09550383c0d00900c011030340842504041c01d21142040b01c2100080c0c80700010500356155644440d0210302030703011003004542c100e00c8442d0703c03210a4164001d556001000200928016000c0e003200120000120f002604d0030b21483c1c0d00c11924180809885000303402001081c48122160002100c41600c04650b066100c80c4c1400858414104681040400c0d01c400b080310030b4200307003160895031298002440e101402881002040c05d00065500c034602424201d100231800d203240e2682e40d00d0035078481c55094001c4402c0024907010703221088211140d000071002014024045039200e00144100681842160010001d0b9604da600fa1000c0900043c00c2c03021808448400074046906500040c82c600d140c440929440000300c0c0942030343c00e440004c3d802038003100f51003d82c0080c1d1480603c3c415a400c207080f050b941d419919088041548559 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 907575206 1250 907573956 907573973
    0x30a23060d0201030e010e07030201090501020a03020303010b0c281106030108101a1804021002150408130b040b12070504180b03070816240c083a0e0a 66
    0x144594481c4280800c030380c095920a0b4401301d007406400c0000c0150300e450070407803640c0302c1c0a48400c9001031a4002c01188a51022a0001e0440d80c140c00460a590915441528039003020303075003404174402c0d403503e503981e112202a01c1650390400400d1622040d00c03801c19240300880d5119080c0904001c02c010890340000049410500301188400241035100d4041c80f0507491340c0d4490958011141039010b0710714003e02000303500442c402c1b1602c00801400d91026601d501d030f0b4164800300b4003014030014000c9030341d42008042c0b0500200c07903d6000398888502c0101d58000d030b0040784440d60046480301c03086c00318148041c1c02404a0804a0505181100064192802d10b07450310310b1917110320041e49142c07030130420308000d00300000588400b001c010b034010314912154842e001c05808848080d03031400c00d010710150810030080d911243c0100b105c6d00c984910740e1040c0c0440600d500b030140c030082c0c40fa4070903c9641446207207001520b81e80d151540b040f003d50707003003101d105526045000250300051411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 907576456 1250 907575206 907575211
    0x303090510030e0105010f0e060301090302060c0c0a080d09061a09010506130806070e0307060c02010504151803050f0709020f0d050c04180230180c15030a23 69
    0x4403490410701034003500c01c0303002e800300c8003482c403c560800380045240703150402818240c1d2011040c1e1081c65030340c4000c0600380da0101c2d1001e401b680003078010401070420074008103400d40c1007400702c038841d210640c1c941a0b04d50012283e8058250f50b0810700041150600560411040c2c500e203188001c5660030004011101c103124851140f0400130303002c1400841015228020a04d03801510441d251110340a40354030304070004507110340559007000c11054050030070061010b4042c1c1d900e41c10715003891050703048003104007048414044800059089030210380c00d02405503114401170030a8000004136189403100c00d402071542c80f4014009444403118910640742c030006e142e41d000c2019210f68003038000911680e0060132802c0402d10340b008034401950010300101d42400c03107907402c040301519910004d607000d064240d00c03503d070000462400c44c41d800809030040d407640306482c00f10031418000703201c81c94184000c1440240200411258600501c20180c0200880030440414045041d0b4072a03403d100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 907577706 1250 907576456 907576459
    0x609010909030f3504170712031a03061f06050c0a060c051905130e010509060103090501110a0903060b01030606120207030207170c03013b0a06020f0408011503030905 73
    0x1813450410080b81031142079aa514508003a074075020051103000580100c11201901c01c81d8240441502007004441190507041d00031090b4414004072003000c4000d4801d8500d6505801e28107038210455070780904c072050140400080c516030302c0000c96440c1148101d01c0e4803800921009000304004680086a03a00d101c5500c030030001002014035206903501e000c2c180300c103070540003854036680c0107603000001802c01681284280f0b00041e5580160000c00c00309020300c0390001c0c40a4042500ca501039003020380554826400440c40366035843c2000501d40080c03044900250460303104009012440c481d044881c942072a05107c002d00341003002d006503c0c031600850f001640020b210061501c2400400040c00703a881890480c0e0f08501e08166076020b40410b190300c25440d1207145100b80c800d0780d540900b441c0490402c1d20f0754a1144c0d923100c940c01c440b1396902c0b100d801151482e80c0000c10600c01403400c04074113840180c071541494001030071190441e00d80141c0ea25031980500c0403e030003083c3e0004981d030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 907578956 1250 907577706 907577717
    0xd0501231e09100b1603021005070c0609050c09090307060e0a0c03300c03020105151c030314070302040e01060e0328020a030507060f030203130b040201021f050609010909030f 77
    0x1501c4248030282082d40c0d0142a40074000700b0b032514805d0828140200700b500a13800c45201e9030000750300c50100c0307105031603100108044003950703c00030342c01d40c101104540c02070301a94090200d60002c64000007040b2a04080d980000402d03404001042c40340d00400c41041d00200b41240040d5036010071004a03000290407a0452640f8074035651a00101c03054400b601d100c3c00c16440312044019108055400e012800355003000b000a140035801600003504480052990300c185100d03d03480a445503041c08143d080540342c0d44120000d400c1c446100340201882c0e50010303030f01c0f894405250360386c00f8180c00460400080560300140d5030340010b044208280c42181495160000d8800e01b21151803880e402500320103d00c0000092000104000041b40ca0700d84594441007181039003203080b403104949c1030781b14141001c00b00c0049640165820b9002d0300c10b00480d100c41110308c4c40d40383c18540c10740340c80038480c2d2204200042c50504e5860540109108d16081c400300c5035641c0c0180040c2c02c5240300380100030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 907580206 1250 907578956 907578961
    0x6050117060a0e100f030305030a0e030c1b0a0b180f09090d030f0b0d21030b03070308160f12120b01200c0a030302061f03030507080d020d0501231e09 66
    0x10715003060040145a440c1c01c1c6030340146c3c2c920307000c0d00c40d07002207070389140311442c0820704090010080201c0d44d00c2207400028141114180281484c00c00301c60740f115400c50315510011413641c546800401003198035440a88140105004011403a8111080d01d40501c130940309110210000003284c894180301c5050104a6031f00c5108001c0003070a0482d201da5100c5c1e0207a44250074040800d501044841c140d06680c4801d040c4400180c0946100180c50b40d05a4400724081010070601000303003556142d120389114440506032500910501d0112003940c0f0b6880000c40e0458480d045a2a00201120b0b41414401c85400b000040d128041001e15030700a0845824a02082c1c0001e021003540e90100500d607034101902d900f8000d660301411500194080201a10701181e4200da0603501d084a03072684d60035240956903510440c90390001c0a218583c1d40d0240300e080b52101080c05014082c000c0e98001c800741360300309988461014218002c41d405840c40342c0d8440144c811481c29103040071825240c0713480f5038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 907581456 1250 907580206 907580221
    0x2070e130f03081e06010207060302130807260c010516020f060a030b030615300723041424040e011b0f0e040903020c03070906050117060a0e 62
    0x50000a001800c0006a07010001050b80101c4180c0c01004900702c03011500c020390b03d2600c0a642e007902d803940580d0010f0410022203120fa0018504a0710034a00d2803181940c03410a80c1c0307804013542003070140c03282c144885556450058011043c0450320801041641188000a0400d104645556203c1001420302105544416011444868011302900d075030b010701d080010000c05d00340300e409101e030050070045141c03a20a880001d040c410014002c03100300031410b5000c1a40c004244001304041c0174461040d207000410b00c0000005d05000b0b207201040704111001e00905403043e84100c1c0310324034214010040460001800d90312032803022100802130b42c40180780203904101809542d002e4280320581000d118190884404480c1d22003a00110520303000c0c1c25a81d07a079041030f150f0006a01c10494102074605500194a454080e005441d020341040c404a03041411030f40020a0960721800100001d513032042d5501d055558a240b040c00302d06041d80010301004952180807445008000854a035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 907582706 1250 907581456 907581481
    0x912030a091208070b010905010f06080130080a18062105191a0a173309010507020c0402070b0103020904082a011104080a15020c01060f0503010c0306050102070e 71
    0x90075041341e45117800c0e60b5920045400352030240544e1a0441031301c0f40003e003079405001e40a06889680448014103500c00380c43c100c02050800c0380c02d2214021803001008501620020a1403e210340d880d500c60100301e11540518500f558050420403400f6242e0494041d414140b01d480ba404045010845c1c0d181c5840303401710202d0075000407241614220340590204048500d6124802c02503919400c200c0e03880c640c1001080f9604d41c21142c0e82c002030048003c0001c042900c0031107039000d6010240c1002c07001382502030100126031000c242d81d0b45105004080f5010850034240e10030803a4190700d4108240d60303244140c0c206100c024090407444000c1010010400d09031010b81d451004007800a00c1c089a41c2921400411140b40701540381c92034903440324000d00122800d492010008040401e020354502c104540400c508040c5aa800c1c01072034180c0b142070051100805d070320020860354604100800d400c55088810760414185041c0c000c001030790300422004126825403404690503590311420000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 907583956 1250 907582706 907582717
    0x30f0f0921041503020904050903121f231203090a06030f0908070b040b01140906010e041b26010e070c0c0306061511070605040519050d05030912030a091208 69
    0x4020f0050112a4038070381c59030207080c0c11041180c0c1809291109040c158491103148451562811003500240c1880822203002c1d820302c051920380d031400c0e60744000302d0720030b10040c2000003158610481125440e103014810a40c01403580e40283d0310f403658220005031a0006c9100b044140340e01c0b4100310702140041d0f485040324540152060b0740d00e0703016141c140d114003c1100c044414110010001c601c009000c005110b440d50301030402c210786e4a03548015600302640e400410350054030b50390100701d034141d080904000e0301c8990b11284c0b05100000748410020345200c412604455a0300010401400c41d0144a500301030181803075603030385690341845210004180c10144c4240c0c20001c001411100541b0b041d0b840384420350f94203080a4085445945400b954401c2c8000960203100c14080c2e840e1106505001c0a0400d951501040d51140410422444d40c01c003a1083d410104280000c2e0505005c00c030140c03684035028500c0c00d844824060901c5c07416010f00346848080600540c208072504003101c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 907585206 1250 907583956 907583969
    0x718080703030203130b031b070221010b010e06070506040f0312050c0316030213090f020405031c0314310515010612021c0b0321030f0f092104 63
    0x100e040c0d403a0304003c4d40e070313500038050300c1040c115000740041d207030a0441c140c0b4001c5440701c600752111301c601864070540b50410502640d001080b0303030a803080103020003600144c0015a100100719a0425400904002c01c0c3c0c0f01c0b61401001c08100c1d0800081d03002c280680d0141e400b000b02d90401d181e504044803501814178440000c2c0d403500f010b00c02c008c82100c3c0030394407415a10300c003803100c001c42c10c00440c240e0241c2481d1400c2051424030910403580581c10100c3d008408500040c00c09640e0340002c0c0c07409100c050400c10a107503800410b044280c0c58040c1842840340c004e041e150070b0a00100d902c082c20600d442c1040c613807007010220008000e10391a01900c16030031800b1144605030540d80c52004c840d0030f1050002140103030000342170611850090710b03408074903001c6d001c0c080d410009054025100d0210a154180a020204c010307042c4680e040141c5040008500d50b00c92802004040401901810250010300d0301d008105114000060368485014a10f000641071100d010842d51540110b07005079 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 907586456 1250 907585206 907585213
    0x3090b07170d0e0601060e030303280c0504031a06060d0e0102070b091501091109060903010e060408030f0a0501360c0c05010f06060c0210021507090e07020c09071808 73
    0x1840c6403600750404250811044140c40c45a46e81e07900a542e61105521020b41640050000130a41003030b9070303030841140eaa2000300000c080203031102d990840300001c81103004500003050900a021060b1041030103104583d01c09889420302d0381c0020954003400f020450015201c40150316842400c0d0160ba00c1c00343c0c01500300d040341c241180504d803a05201c100c0c052845c11903000019a480c3c6e6801030b04c070180928020f841c900f80e207001c144440f0f54843c1035a00e41542d04c5000034404201e04102071441a80591025034a07810b04498203003034035001904005a0901f0300c401403042468008030031000d804400c00e1500e8000510290048250000040740007a5207030051140ca501d4100c400c005103a48103100800041215040000449000b40079040019018228100040c108107046052104090040350786500100506501e00e01040300c945000801c1c04c1020400c44203c0074800d81c002191340040c103104644880821100c1d5001441c41e010890b1080d0540742c0c000304107030110301805880055 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 907587706 1250 907586456 907586467
    0x2712060915050601110a0803070c0c08060a05190c050d0203191409013206010207030b0108010204050112050405060f0c1317070e0108103c110703090b0717 68
    0x107841c018002140e50501040705081c265a00760400f090040041ea8048000d0b030035926204001c44a14980c5d18007140e801e10300d590017040041c0104003107481b45000c15408940d130325201c10300c94a009200c0040d503192030309000b4030b602c100b070b0068103032004c98a840c00010784a6032048aa4110f4200614151030700c2454414020140c000c1d2100c02881000000001d02c18402c00c0d107104503c0368000300103500340159104e094101d45035445a201e030800c01c148100c2d07540640b00d454184080d542a400402140c0d80024100415600844030b40c080740c8060604001a140c55280d080e140d5100416440c031802500340000d07242c1c0d9100341a95012511f82c0c2d0805a625140c41400703138181540002c00c07410b44101040000e0030a01160414160b130000700140034120900c5100c0e50141004a2200c0c0304500740a210450000b40344d20980b0000c20180d80021146000d40c0a11045407020300c40150703600010004030001c213401480c000c049038254002e40381d44440508000c014a043c0d1240c45103480c00000d903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 907588956 1250 907587706 907587743
    0x9020d0507020106050f0603060f0102030c190209060103020c030d091b0602070911070f0f05280201030507020d0507031d030607090f050907080c0711060a0c0327120609 74
    0x30040c4549030980081000e1034880c010840e52001c080c8500d40e218030f0810004065040c0340346490001c1206004036418080c0c6051810b040c40c500240004101d001b540d0440158030380a0285608902c003801c0452510304841c0500e5202e210b042410001151a040b803241080381154608081d21506854080240d440d41c2009440345014841c5070106801e080f6540c1c86101d82000301c036200d81c0c0c8a054080010816a6400720844071032a00b50b400340540d03594049090900c085501c1224020603070140107040343d03c0003404490020300214110f42c00350a4401c032840d000401c8078a01501410f1800e1481c00460b5091503c800300c003d5140c05028030303014000d41a40100c1a041500d4504400c2d001154966051191101c0c04032185070000c0d41d03500c082500106644001c2178400d0107584100145a01e40f030101d107540d808118188000350029162405042c2d0060035016080d03003800604050b4071442e4114250002e540c00f42c042404a4003914400300300040d40010f0042c1e0b8800c0000005129844 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 907590206 1250 907588956 907588961
    0xd0813061206141009090f050708090d02190804090614130b010e061605010504230a08070821010906090e0c010917010e031c14011d1009020d 62
    0x326000c08a44a68000d11001e0703214090401034519507008900c0841c2407801308036100380c0400070b020901c1061800403c540596000315500340c10b90f1038000c101801c109900401302c51000708003090320380200080f0301500d503020a0b4618100c49140480f040e801143c181274415120300d50014460030b1501100048507400d80d00e4641e0100005c968082d203104914440788140c52984100300c1c00200004503460b168500300f0041e21540f043e1803c240c00003429942e0340b07401c4680c142c5096804c1050131481540e05101610300386841b40000e03010304040d0105a075114514000e6120007008004003117100c1d1050707a549c041c8640c0c0d54210100034a21941e40b02c45c0381000705240c4c0600c1c02038909044074088550800290000841c0040e9103210856142c00240038040c20903040c005880d5403135030008650340c04200064800527900d039680d20408481940e0f910100c0b02c000c401002040740d440d00400003130340801c10319080c030300303200c840c0300002e42c0d8460344107244007a81d80181000f948040352186c5c4e40a00c0e039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 907591456 1250 907590206 907590209
    0x314010305010b0f1509060304080c010e01150f030812070e090f09060f0f04170d0609140907035606010e0d0303110405280e1509060d0813 61
    0x103a035410340b9074810a081c0301c1c2d0080c0b00b20a900d1601c4040000c06e1050401c0c0c070003980d10600545038503041000340300130182514415102418669110365848000c03110a40c01030005200d000b4001070700524566500c2d815000c2e14400000c1d00c008000003a5140b4010041d501c5e0f180310040c001151894548030b000e92003401900e84140601c111400100c4044460b00c0e500d00982403807901841d2541d40f03035030388079820803441c00407121a0360902c0302c207a1003811401a540680000c075004100c441c0903034180c0414100051040000380d11600d002c101051050100740700300f0400b10642511545800c030300e0003008047d0311101d9100b00c00c0b2220113030184010a24102031040c03c0140d0500741d241c40307004556113400e403500c0da54020b01c0352a03240002806980302001626060300028180f5a440e00003404c01c0f06c9004030f1135915080c842082000e2440800d40300c0103007950a001f5aa24280100c020a00814604015009641c0007002ca9590341d108c24004d03021560081c035640e6200360543c015404a65103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 907592706 1250 907591456 907591459
    0x21e0d14090f010b030703110f041119030b090115230703050711041e0207050f0a060b09011d0412110a06020c012a052a1612050d0f0314010305010b 65
    0xc1c80d01c0300304c1c10716010030b451003100e4100e1240315010100700e041103401c401c0800160391003680d0350703101d800d0714030040b02400921440094414150050520160648402c03420542c82508001d0051140b005503e201814587e16403420448041d00407681555904540c40e96000c0ca4402040c0101059442001440340034402c04032a40c4c5d000700d030800e01c0280c41c01038113000c241e007048940c00e80030500164046c1c101c540c0a8400c440c02440110b180c04d040c804040320981d0419107402c0070034424203104131154014584060751010802d1401c21f002c9215002030070040034501448503200d02c09200b107200344e030f16500400c00e482c0e40c075581c0d2405000940c041d40541c4d0443d400d000d25000b07103080c200c0e21a580c0760194030a184150801c900102e405034050112001200e080c5411602c201c1401c040c8017410042c208000c140c0401d03000180306441403268003541c4041d109a0302d0500045011480701c10713811290501800b4071060700015800b03002c507020710880c40c021410000061080540001800303500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 907593956 1250 907592706 907592711
    0xf0304080409060b130b0c07030c170d090b091e0301050711010c030204080c100c0b0406050a060f1d04060605040e0303060f0301330b07081309021e0d14090f01 70
    0x80d10310189656014005007441c00c0300c0071441c10850701b0002c2008040c000d4801c03060f60a495265507805403c010540c00082c400340701040c0b001c5410324100f004034000304190070440704181c9440b0143c5c0c800d00c07410004034040d6101011a142d46519a1000c07413402c0001030007030103207283c075040040a400c0d03000d03c007203019030900c110342510602a2080b60309880780d070005044174040c0300302484541418038003280104905018080041402c0e05e400da0701a80c81844003007241d0802e9075500702960700a4210100f116000c0204101d41003012100a590a00040d813061250750f0ba0f0408400600701c9900064101d4100b51041c05001d030b0110081d8460306007150140c03a81210202490700701d650300101c001e00741003180b070096807201a030f0345412200c00302581d881380c00d40d4403000e1251868221582c03c8408031008517400441c07986040b87e082c081c05205030f0840c284410383e850306264901c0109100050040043c0101c00d19a00360041c41e000c002030100c0c40706500b44180c2071307580d032000f0480040e501e51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 907595206 1250 907593956 907593959
    0x50901061e260111030f06030c090402190801060b0c010612031b05032106040506100203030a0e010213120308070c0203070506090d05010614011b080f0703050f030408040906 76
    0x600c0105050305803010700450445810030080d0360341052241614081499102c5a00200034004d0142038042c0001c040c0d255100d051406000c080b030140509a18400c4c0c2000c40c03018a43d449030414598801e4044076600241d4800008650000c256500a100740d5401c0aa001c90048021401066008130800c001c00031275030760300c89144518850000040004182403601420641c40b85c4102c0841c50040054900c0c1200196a10203030010303200c2d441c00e41901c000c040080350701e02032140d80c0e84a0826243c040480f615420000c0d00d83c40020040d004999a40014403003c034000d6054804942000d540034810a480328401c4902448860084000941d40800680b10500c114030f041d440680c00b50007022460b06100c108001508014040798110719607401000120720700340a0000140103000d0b5084121110800040079101038458414102d242c2c0540100010001d004a40141d4000e001d5140c0319011460120380782c2c4541c0c04590280340000c02072100b840981c070024401c554041c1d03c200f00b020b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 907596456 1250 907595206 907595219
    0x9091109091317070f48141201060e011502063105030f030a050c0c0a020d030528080601020102090d120c0803150102190201080a05040312060e061002012903031c05090106 75
    0x7420040c3c100e84031b064030160402040031203504054a698004090842d02a100d00010f400c58020740e104482d002d00010041084400c003469554a00407a4800341c003030b5151080d4400b0f54010700c0c0c1444001d102078421030505103007200c0c0500e0401070b030002c180c2c1d641c1d942a0003a4000380e0020744058070510700d0000400c03620740c80d890448090b007460b40c0207040405484c1e000c01800d400507103416000e008041009014800d00c840280b130440051005a0308005000f010003072041c60700510b55819a0300c1000300340c1d91a5100030786071508a60002d000b00d0140c086400403558480c552600074048080401405044610300381724805074402039080310b45600c2c100740060100c0143d01000780c0458105400b140d550141900556401400780c24101d9050608000e180210ba07583c0d80f0544800b045401440011310780b540030851782103054402030010920490344004050440c01d082100a90b4900804049807400e01c00d68031306164811060301c0b041200320540c0060041100e828099504e00440070449 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 907597706 1250 907596456 907596563
    0x120f12020f0a08030703020405060a02100f02030613050901090b1006021903140327030706140c0301052403040c030213090512070309091109091317070f 67
    0x12100301c00140140d0b03860303440b0001c01d9400a8180001c2507001c01c400f0600c0e80701d1034020421150b5a60091050070211101002120700103682c0c03025450040061004541e2200059a001c41013114001156100c2461190040c080f080b0002e04402d0300408010383e1904810308407046517095000d907000340c0d944490640058401203802000320340341810640d0010210405540d200c14036074400b039004403c9000004440c0601e6550b64416400010070600304a42d0b0f005a00821000c03c903a0007082c00c04604045850005014490103091408034216074a840c0600303807100c030030f402049580c0e60304090809003035542ca10700080c1d000b027a0000b0550190485445030340207554001d00500068034110708000b0a6a01800042d03081115428010400106600c03130682d802e00140304069030b8a81c00c0090007000800180380e0441c2e44404070071b18000c65100b042c44052031100f0464907640e0441c6250002801c0398002c8050091603402a10080c1c0071980701d00307030b017003d03d00700000c840c525079a030702c40550f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 907598956 1250 907597706 907597723
    0x12030d0f0e0f190b15131a06040f030b13080d0b010e0d020108040b070e13060501030612050a02060a0507120f0e10020c09040c15031b030603030203180307120f1202 72
    0x1400c0c0e2281d000b0f40104000221590700300c00d511440640b80104c0000054002100740b07160b24403140d0300c0350f0a8560100c108002c80c29500d09540340e070301b0130b403400008005010b094030001e0100010580010964a03007400b503d030b1550f50001c6020b07150100804484010001401c0040c041410a4003424451070b180d00c500500d03070350503541c40700159941d036180d003e0700340040c2c0000c040c483c0d480300d890350756541c007143d0380c1900c40084000101e00e441c0c080010300f99103040e40540c1041d076503039000501107070300403450340704a90301035031303401d40d55040c5e00c0c4101e425100b00c00c4003810382c0584d42481c5a20542c0486400950340c4243d4910a1680c40c2000300700c0c4440303100d8000b0340941d01c001e00d1080213041c24122150b100d8080c4c1c0c3c0864100769114148662034a1411100c0002680c8010b02a8000c001140c0174040c501070345007c1101c581180d802942e00d01c5503160b405001d203020b000c1040c2c0d59038108407080140038650740b0303e021a495460140c01d03c4028040843d00c02000410112855100141401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 907600206 1250 907598956 907598983
    0x2a0618020607060b120f060406062106020901120e01020a0f3b040e0d1202040b040b07050a060e0a14030c030f030703060f060f02060703150512030d0f0e0f 68
    0x24030781902507903a00018a13414103560b0704900030802800000030300380503c040d400540360141c8568038003440d290080340c1c4290000b84080038818940d040a01040c52400c0c002a4813420040e40c2d10002c00050705c84160048610864070f0506024130300d044410340290245440c140c8079009034920101007580d28128840022441c045a009203400d02c2400f03003261440b011510400850017048407000c542540c8a504004030f441d4800318141070f690740e02c524401164075501c0c9046007400c0c10803e55050358800d0740b14a00e1010401300325041401014060640e000e40c0c0903508001750f2898408003600c40040740c0c0191140845002c400745e692401000311001812018003851614401002c2c818864001529040425607110030108003140c1c40070780ea070b0241000382c41e601d001c125141c2c0001d260000081c550402c060500301c440345040c40c4402032406942040310010380e40c0240710501403550007040c450206403810a480c2e44100d41c025401615641140d4080d2040d070408680d20965628540103040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 907601456 1250 907600206 907600219
    0x1020705060f0a140d06170607050702010c020111010606030b0301150b040303050304140a08030f24060c0f1510080d05030f0411040e010b032a04020a2a061802 70
    0x41d0901121100108400c503503905056922034222103e0b0344841d0400d0001e20b07100c5c2d9403000d05118100c2d0701c960341c10030581d00000405052500340f50040c494003c0440c001d043c03001c100d001d10216800f80030141241c002c0400200405559044024060480301c4102030184d403078032036600d032150502c4800005840b10084c107980341514603581250f4541c07000b001a81c000004140c0960705034018008114414000c840c0c2d0307507c1c0e050005042c041d01501400d101c0c00000f088084200304907907000c0f64000500200c54203130b21004503201142c04c03c40c194580103400d018400f1000081580c3c2600303d401441c0c1c01200301d8081d40c5a0249603a1200700403403a131b003c03442c2400040c80c1180f0f441a5a0b030f02921030060300c802e0040d140d02241c203540f140c090b2410140d450381103e407181e040400c035800e0b402003070800298100d4204440c1082848203416581c0c007650f0000340b0100b50310b020750f5000d001c0300c034405d01080e12501603021030384012200c90012074400c2d0410000e01d0222561000280300d403034008024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 907602706 1250 907601456 907601467
    0x605041713240815031c23040510032705060108062a03060d02100512060f010c02010c060219020d110102040b0306010c0f05010510261509150106120b0102070506 71
    0xc900c130091480300c941e82c1886a0f804030b100900e1240e608140004041e101d8600180e5040340ca6a0400c07070094030410700035418001000160b0302d415034007500030072608000508902c01e503e1640b010400c2c4d0f40c140d03020702d82080b100c41080740c006090b604035110780003074514580702c40c0840c4240b008804020104103007030600e020b038042d1545008640107500100b00f00000013040c0c3c0403550700c5410764114000b0a5002c03800d03031030100140389400d42c4448101d58080c007900302c040020303208003e00036001c2d04001c042072306c503030400842e54100c65000382d031220218441c1c0e034400f800079075403405181084001010014200c40038032050003a94190341103045e10310f00b1580c5407001103c002900100a940a203100d9038a080072401c00e11402d402840d842036160b0449041030304890440c00c8020300c0300021b03921b2101c01c6504d450b021502d000c44109003802c0c0c0310340d602c0d0700d00030526202100c00080c540d002c00c040000b40142e000303488d0412815600e4414800079203520700580e181c0b02d0b50300c107054210004100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 907603956 1250 907602706 907602721
    0x60102032b06030c090e2b0c051204150203070b0103140a1416080f0606040b060c0607030221100603021c0509211606050417132408 58
    0x114021440c680c1888080070346406403040d01660041e0740144e9041c4c190003010b001d5412107001e0101503144500c02800704415012407040c81b414a5480700c000c2d0f00c645414a0b1009208072120724440b5002401c0302c00d000e600694040c4103502510580707640d250100081040c05001000b9510780795002010322155a203182c1b00c00e941c1100103a4003408e503002e0042141d002821a168010840103070000401081002800003480c0d58a141c20003962640310065a04015000040d081d61200e0f046d9004902a400078020031481d00440700b4115003402114200300c103180d0300d6406814a0104c51081d2088080e100455101d04c50381900d0010203a40140401d00c41580660020040c19000c8118018103a452960311800c0795030544200301e040c2c01c20080c1e010209066254007003aa41894011351815208081a110304c6910b0000202271988442c0081c00380104080407601c841c42401c410790fa2841202d08180104000740a41030f800040414245007004141d528404138018036240c80c3c040762103099 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 907605206 1250 907603956 907603987
    0x9040b010e0a090206070b0403020d0908032a0a030c020108060a230105041203050d051803040911090a030602360d140a0f060509030306060403200a08030406140306010203 75
    0x802d8281d84685405940b0010784a0f10020030f04280107604140071801c062070700078180b0700c49448400800a1800007403018082c04800c0303402c101c0c00f0450b000c0c010b0301c01c1280e00d20f100c0050038070442180181c0c681441410340001400e40b80d0740c400d03a2120141c1d83c82204114440c50203010f20304400004030032a06444001e102c0c03000080340c05040c80307030400343d0f10a90044512a0044210001080494040d020a00c90b002da280c0000e039030407810000590701c20285c0ea4a01135880784410f00c6842c1e00c44502c003008a601200c00800014044000c02c0b610390405001a50283c000e44079084a4030b000c40780c640b103840c10a031000500ca2840035107100309030820001600340090054880c0403d08181c0002c3d4013080041020171441891084602c0070541040d0701210001030020303003160420805c2000315903805c01141c007500e9001241c0072401528800b00794105030030005458202d1a0610b010a4520001004c0c0007204d4840d5030301d010800305411201041c3c04242c0703045000da4014003c0011442800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 907606456 1250 907605206 907605211
    0x15060c0b0a15080106050103050c160b040c030b0a0203041428020a0b03041101091508040b0925080708070f0311010c080706090303050601050309120a0e040f0f0b09040b010e 76
    0x500000c40c101c801019240d0602c2d0070783d0b2205046a645682c01c21181d41c16000b0554051040c404031410401c4201c1880d202804540000f0b0119041e100040d0410502c140341001450300b00040f04081c3c0340a011400003584103813415076502d12012240d07802614000f5040c1948064840002c06a041d26859055040301e0008101c4c2e00001502e80401d0066450014600c07035405820900d0740300100c60009414003016420881500d840035543c0c0c1c0c4c9580d0003405071500300ba400401d4500b15507444d008141051021103031a000c1e007264000c440310451000072030100703841003141030b2085541d4502c2040c1c3d80c1d0711640304507858400362103003c0021a0020388011880c00043c100802580305607902c130b04056000142c04c031481c59580c00d04c0400c2c0340d85445106da04c203a0a00305035265092800340b041e960350000d02042020200000c4c007000540c0714820031010000701401c01c0c046410182040703005403000c4100f20740c449103054045c541c589014801075000c2c541040521819908011440b075018000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 907607706 1250 907606456 907606471
    0x1406090c0f040f090c1a0a081f03051b010908011a0607060b09011e050d151505060c0304080c0109061d180a090209010509060f010309110a1815060c0b 66
    0x102c2c1030f0031602011034054601e203d44034810941161303051128910900360821032844942070144803608141e9040a1501c1d0403006401c41c070050040485503980c0418415080244035004102045000003030500000da8160000d072160040207841c2e0f13600c01ccc200d9010300c90010100a0441441c94139040440003041b4940c0101d4021603140403000102e648502d080e4013181418400d440846000381560680c90040e1074100d824550f071150039203450000501040000000a0350389101c100c002d10040c0c4650001d21001d80001e0310b803480c1d02805903c039000791288071102d00842448150b198450b14101c41a01c10b640c8620130b14a4112185402c0b01502c2c0c520950230818890215210104040e41030b44240c4000601003540000e134418030200784010380c0994010440301090040e00d0760340c80b036401b0b80c540003803a000070103030b2a0b8108200450f01082c0800e800c010711000105400e591040b18148007a01c80fa020301120b400e03150b00c5807090003680f08440028001014103000a0744140140303070000301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 907608956 1250 907607706 907607711
    0x270705092e03120504050603010902090d0c060c0605010504060e28060b09012c150403080f07020306010f181119081b03160507140a0b041406090c0f04 66
    0x140020003450310307407040d071407524507480a0104004100031040048103041c0c1c40e1800354142880c00002c50380b14001800b5801681d50041181e6160381c40384111ba0740d00d036030029010714a0750782d03910b00907109104413041610151b003402d002240b507003010b010b02421503002c05507410785681d940282c40112546107842603090102d044030251618003501510000e0100051140d80e1498000000f41a0024046030008498400b8164009090181101d460f40e40c109986041c3d00c00415140d100080c030580e0402420040040380803014412240041c1c002c071340c820b40c00c41d1140e07620303004688042c080314070400d200703c0410316644048010f940c200000403115030785180c1c10607c0450600303112004e003184080000c2d00341810801400e14203042401c0032890310022038954181200d64072044200440e11506000e0000b40ca10204030b100c2d2850080414802c065032160103107482c041c0d100100c02d0701d09640710710081214502e948d1010038000d0190342c02c48020103141499005000b4816a85d01060398802d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 907610206 1250 907608956 907608991
    0x803181906021515100509010306050901090e19080f0a110d030f0501171e070e0f090c1206070f02101409060c0906030112060b060c0627070509 63
    0x246503041440140046401900480000401ca103543c460000c141d8480b20410540c12503003622900324901c003c50032032030f1050f0740ea80d81d440140c020b008140d10498000400400001309405950b01c01943c0750200400d4800003541902404400c0414800140101740c1c100031041492134114024074484002e428440d001e99010000d56003088a44a4900c000ca9162459801040c040303100e013a02600310034018144215242d880e4903a680340c0c01740e8102103c005010301d0000984100803240c004c00700b280701c020452800800d00c2c5131080c400c0d10b1180c00340c8a100488107061422041900005440b480244800c2d640c2100403240d140d039881340002980600103401c4440300d01e03405a0b0803910003201001d80726041c842e0501e85455002806040641d8003440b80004035990039045904403859100e150100d40b143c0e051400c002d007940c00f501580114005004400c045002c50810310414242031400600340d2030f85604543c00344c90a180362115009580305100c1440d102c0f542c2a00580b4036286407440340c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 907611456 1250 907610206 907610239
    0x4050a0b0c190201061802070c0905040302030a020712080306090403030f020f280203030f09031309061d04320102121b0711120a0b0c0d060906080318 66
    0xa040c25a0703050140c0030001000d0844030020520002d6045042c0700800865107020010b0282240301904420341d590005694001d2140401d41e0101400014004001600302490040d40d2540100801030150141c03050000d841140800d00f2040344d6003014140b403840d40c80c60100540c1400c010011000e0580d40c81440e11004101e02c043c0070611948841e4543e1074410100c5c102e000d900704481d84e000d040342070302c10400d02a80407065a42046010f1b80c80001e41e1220300d0540d0440c010240c1c90440002c040e28005160412500003400304c6401c7d8486111022010010003c061801c035006401c03004140c0440c5010f00f01403c50720031402040c05000008601c2c3c00b44c190136a48400b0000035000b170000280801d8120f21000c121a031408128140d2030300e25207a54450072000e0343e2020300d104429000e01580c2d1050148604462541d10048403071003403800c00e02011103500a4403410711440c0c540000441d0302e0348a031140d0b00541e01582300071070500194400450041145484141e0066824142d100f0304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 907612706 1250 907611456 907611473
    0x4050d0f0f0f0c05032107020f01020a1208180105040314130f03081b15150105070503030406060e010503070503100c03021209010603050c010503040b1302190905091b100804050a 78
    0xc2c103115403800740c60b107443d242c1010f1801080c0004610040d5558103500a1220010100c9a420394103440008000300d8000046c2d0078010403090141031803190350000c0015030746c0300156511502401030040d60b10282c001c01e040c01c0350422034000340030072500b6413910361500180c2d0143c803d0101d41c101c50040141c40d00840384152040d503000701c1b442c000c0032038052112500c044810016411050080c00881607501014245080c0a041181c0780140060440d40c140d00c502c0856507ca0342110440b030342d030f05041c44d1420003000b040c450001555519000440d40340b42c08195102111801070080403e08101c881c420010101c00d400780050641c2045186250103036050b28601c00c0082900001c0d0f4140b66080c2a03007407421122860341001010810007000816122100d070b04283d4120320710703c44000d54030104407012000084030511030030001c000501010039400c514401d180e05815035400c00c85100d8400c0c0020003c00001d50310542c4103030200b01041c400e0050640c000e010340100e640f0464a070b100d10a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 907613956 1250 907612706 907612733
    0x50907120809330f09210c01080603070b0f16030f14120a0218030709060303180b160501060902030106030b0f09010614071a0f010305060c04050d0f0f 66
    0x40103000400c1409007803800b00070070380a144000c1810f080300c0c480304402c101a011640c0141000100c00705142c13038102c0c0d980003603607101003001d0034880001c2040c2592a091110000c2e014015109103072000c0e8075540f003412194000c040280080502c0c0341051503410341a000854503224001d01401030300420303c60b04140c0d038880350080e02d51091910101d1001028100306228017102c0c81801c1184500c000c03148544180d2005400400580354401500c0d18200200402c0c0d40907850f10545201084000865202d00300702e07442600c1d00b25480940e1120400482a6482040882c0d541400704c02d0bc00c0b05100c1e24182003522403000000c980303850307285070000c81c1c0007a08100d000035503509201c2d545003000c0050b0708180000b140d03d07025640c5490002850081d4880100d0390030140810356a04201043c0d0300c100000106500c01412403400c0030010184002c00d02c01035520b0b214401c003060100101608442c166203015040c0380030700519171a07887c50200c0b400707801c4449420606010001c281106003462 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 907615206 1250 907613956 907613963
    0x5032e0905090709050106090b0a0e0a03051c03090f0b061801290c061b0d090f1e120c0812150f01050c030301090e01020405100302030712110d05090712 67
    0x14041c14948102d0b4034002c02e5802c4003076a180307000c0c01170100681101d20001280c5000c08499920303807107a03104440c80059801c02e5038014143e0782c130100070441c0c04510710394000240456415040100c400440030307a9040340f0054103c0d0032050303040340894080d01c070940d0f00400241c81051120100810710701218002d9000710b0403182c002a1182140e0004009440300010b41c1c02c182d401c00d2880034000e038480201400841445900100324141201040140d4030001c01500d4100080b240c0c50802503040c0c60600000c90741c0d074501c401d040800303284400c071805070260001c2e03010b00d20511000c029121581c0d4914191109101070144500c0c540300310f800d4622603904210504034045d21382d0184050760311810103c0d0306104060242003101c60300082580e0440e40341c5007000c5114111000b00a0080c86207400c007603000006141504940d0b60144c0085000c2c0f1100d50301c00034903504202408040310a20300340c04209040070005160340c85201c2d00306541009a400503183c1055880c0507241242c4443c68044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 907616456 1250 907615206 907615211
    0x5090a0e030c0106050103381f0903110a0f0b03270c01020c040e12071110020a1707030c03120635060c03221514060f0105032e09 57
    0x61005503414052603a4a8400141b41940c070219a001d80c81848d45060201100405255003500980d0300d400b07404044230040e42100c1200325103c0f0008148219901040e1401405880300d024503041040c208001c0364242c4620f1101e96081c00d0003030101e60f00150908414030206403444150b05941e481a400c034a021400403c001542c0748001790800203054503c51045103052040342c81c803c40030850104568403980fa903aa05c0d116403400254080080b81d500b0340181106440c110303c1038001810280c0e8a0080030544142000500300d546c462040c9140100060000302c0c0d514002780c0503030b0b15199180e081e020046086500d464121880b412a106000f03451b099401c0d05816151101908402022220010b4480e0740303003442c2c0741e290350704c8003803c0300c5004124108034a40c010840b0a0340d40d5001d902420410a842c9021031400c05403d0b58060f22600050040104d4028a040610340c5003034035060b11f64504594031418a08840da41c280b440c102e000352031148035150070305251a00300c094000c400c1e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 907617706 1250 907616456 907616459
    0xa060612060506010305090d0e012f160f030201030c1b0312110301080a0b13210e03030c0c04150306110310060801030314031b0a0f02011a090105090a0e030c0106 71
    0x30800d41d0000f524281c14107241030140300c8400000300e08245144400d0500000d40401580100d0f842c25624901d1034426030104c0380030306075018030711407010b12103408000c0f51f886042c1103140c04603a400c3c5204142e4080e9884c001040194025000200c4d0b121050915155000c0f140d41c182d800c010004004800081000c1c018040c444c00c144a41c081e00e0741d8180c0681c2c115030402c1129580e0301c44400c00901070b56113010020300d0394100040a100d03282ea201c0d000b0042524808620405a49001c0900d800724814024907507080c02c000040c0d48817403040c98020218018028203100050030021000c40071000c0c048804230109145004000442c00304116030f130740c1c0b0f04d00740c0810102e041054000108101d076613030040001c02d44c001400c090404d010028a0390380c0d102d01112031088000c3c1c0038144c49080300420122540b40d0003070056211154250000d009030031540c0307400807410721322442150340000701d000180482d003031101442ea8004255003002070401c0c84400201d2954100d40d0035203c003030391203420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 907618956 1250 907617706 907617713
    0xf100806090106110307021e062b050c09010f022109090a0204060206012d1202040e030c10090501090b0124030b0904080d060b030a1d0303010303020c10020a060612 72
    0x9106005108030300d003140844d0103264030326480344140f480180c42856840c1c56854001400916000f001c44d000b080c030342c1c0e184914062505484411440c3c0f200780900a509240302c0c03075150084603c140340c407941d6070f4542910400150784a504580f240c03811403198180c00e00345030405000b010000500844240e8446940f0001c10001c02d10003130461250a00501c02044541e0300005c0060550300e203040c010b081c515001c03601080c819000c2e03a501001d02c200820002e001000e41c2c2c8450281402650180450b10b588400d01396240304a000d00c0d0380ca58410342450051042c668081c200d070038410000030420088039182d40c1018403081c1c0145100f88034002c01c070703144030b07541211422840318141800e002102c0f280c8005032040b0001000a069a94009120b420728161903004d0009031072041840c9440c2e040201d40070005052051804158420340c49000d08200070000a4a04032075043d8014140725030340f0030070701440b220085031440952044094540001c3c00d02c3c091200508007952103405e060680c0d06 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 907620206 1250 907618956 907618969
    0xf0d12023316080f040807050303040606230a060f021c030c200a030302030c090a06050c0f010b0d03111006080a020a060f080f0705041a090906180a0b0f100806 70
    0xb018840512014010611507582044959138000644000b8074030f181d845082000d207522030b10318001d10a0000004000410801e079102c4c0e4103446c41f040b940320802e2060500e805404a4512910740d0000b0b0180b01081810b11a03182400070108610540b007486040d0f10792012400c1a0358a280d01080d182d032555000c9990001c003036010020081944044520100340d181e0721601c40500240402d500000060548180710007115040c10010b04200f42c241d41da118010101d411962007850640241b0b10000010030b0305014808411030010724000c0545160b0341c040d83c516485e100d80100a000c0c4412010340150140702e110010218040600301907603075841000051102c1d90071480500c9017403003640d210180e00070b07015644101e5030b0a64100d40e454204041c0c40d41d00440e44041200341c5982b1440c0d0000452501816003540c1c25540a10103403564420060580c1401694254050105001444550054100c1300c0c11101c00350400c10404000c40c00704004604003103044011404030001d206140c01d042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 907621456 1250 907620206 907620211
    0xb04090c03260306042c061807050306130606080d050703230304021003060909060f0605060a0503040803060a151701140607060209062a0c0f0d120233 66
    0x20001000250030441d40ba03005020180a8900550342d50100a0a0048034004182c144440980c9030150b0201100d01540e03441007240d403200014204d905103444402c00044100c2610f100502804807940c580c444481030307018610044c0c031600d898200c0021180018003000c80c607030702c141d40c4040e44d50269050103400d20000555121394100c010300c5c28071800340101c00b0390790401e6040f11a10b03205500d20104030050403003038000c40c600e203140c05001001c0000c158852072f05426060300078041d10b9542c1003040000e000301a500c00102c0c004100080000e128035004590003440103203000f000c0e80e229062034084c55081e10403100400c007020305038075603040506801801440066002d001e0313600f01c44041529030003100402800d140d008603408210f640e82105440c20205540340340c101c002d41140c106074850241c000400b07a01d0040307182c0e4568508102165400e10b44015210200e80c00003a42c44014000400c1c100c84114001c040d40308640c180c520f08040e0540902c5408135045040750789060340c040901 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 907622706 1250 907621456 907621493
    0x6020306101d060313170a0e010c111309080301080705180108030a080a09081206011b02030706053609090c0603040b04030c020d06020d1d0d050f0c0706090e0601050711040f0b04090c03 81
    0x1218032b06001411320100c4810148081d034503041c501d0f615007002c0014145100c801040800040000315444034009071010403144226203802c200c86140c0300f11400d1030028003030710003030703400420201e032540d40102001900700c4074907240007929000740d885a81d001d4102c8195000d0240d1700d8ae05112896038848a0100303031243d02200203000c0201d070303800240e5402c2544110810b000300455686c07103540e07802d0000910081c941c4100074a20b4505070b41405035000328105684110b05c5803012903c4003c0c001581c000c1d00001900780c500d181c517951a0310b2441100100304408000c0b82c8090100140c403441c203002c0344c076482440c000d80c5905d80482880181e5a5103100c00d500d5107101c1500c05905800000c481d84080a142800c03643c036000807029900038400c0e640001c441d44211103002600076400000b0f101100c102103158000754442d1001101d45125002014002c0210382501d400c59160503400551141d00141000a415103800003040646181050a940e40c039890780e010810711402e40f440c1c4001c2c110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 907623956 1250 907622706 907622717
    0x403080304030309060b060c0a030e040e010612211d060904090c180b0d02090a09170703030606030e0d2a080903010b04020f1e0f030406020306101d060313170a0e01 72
    0x4841c08d40a9695401c04800f0b410808a0b002d4000305485507444080c40510000c0207004503900d40b401e041403200b40100071540840040ba04044903030010340c1092840304180d071030b226060708100c500680c854058172910b81c086400c1080c880035603210b20920103603c0c45000d0864002c0e1070503d40c0c41c9072005806000c48402d08050b000c0409076551040e4030b01a581c1110901d02c5901d405507070000420b1143c600404401c540c03e408209450010040d0003414425a400d01032141c4804049050703446c2c6030680c500941c0700320805030109001d4624907800020a545056041e09140b160b816100d240e003000355a07140c80042d203008182000c2c000c0f0000402c055505614046034249003190300c0c030600344022020030300741001002c2d094030002210a511941d202c0203481c0d00745400d1000082d4015600184141280e4000049190041c03114403000ca0000d80307071800b8116054180002540000c103111040c0e60070703004020000c1e10741e078644500d091a520b0080d880f10050400034161070070446080e0305001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 907625206 1250 907623956 907623967
    0x80c070528054804021c0b01090501080606180616050c06030c030f040f2405130c1e030804030305040f0b0c0d0c0816060e0c010c080f07080403080304030309060b06 72
    0x100380342d44603c4081c00d140c42445882c11880c030f048241c22054990b80c0d403007800040c03029441c070071194905814029240e4100280c2c40f5480064981751014403a45011035210b02c009906c03850601d025224880c18101092483c11040000a0075a402035007921014a0443c10303140a002c002c2000041c00c0e5016911146181000d0040560741c3c00002e000700740c0301c1040b20001d0304008184038103c0003560700140030205041650002c900311807513031900070200ca140500280075000b40107416164640c1200e102c040482c103281d00f181c0c00868420b00340020310301d8402c0c00400540f900c001417000318040c1d0340c0c0139144d5042900c90044020994080c0c1c11450061115086001021400f0051025103080c480750003015881c04c0c110038052822070b04000018005848240700264200025001d030703010940701b40c003c609005541c181c1c546000500098810300c2684c05076200310f001848003d004082943c10f00396295150f49595204640c21800a0386800b00740707041118a01a0456260007210a80c0c1000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 907626456 1250 907625206 907625263
    0x809092e0506030612030f040902041d160807031508060a06170d1214040606050a230d0201020a0c082802030c090712090c050f0303070201080c07052805 67
    0x10301020340b2580c820100e40054046900b800c01c210303030601f80c0c1c0343c50140e10f070f59070303415a840250801d114180380c403e21030a034084500c0609000a100f01400c282020364401c0500d002c803006400101600e061640d501c0a0041019103050200020901c1500400b280d1404864100c143c0780f490707000ca010290f01e2010b03d0780f11000805c940e0302d0b00e16140340840450301065100ba001c2c0229155508a07030503020305100130b00c80d40b50071130416a0010b44c7c0718030411b940c844c0704170b0036140419002200c0314200e41e00600c070b5260099201108600510407240fa00c0b5a030703103031502c4c0604240c2c041d5516130700040664040c600e80300b1205d005c6000c50340d00502c5801c01034001c69210703241010751910a90042c00064403460081c40b608030710f60300303201c000c000000031480c105010388078900600b4850700844e130711191207150003c216000f941e41039403260b007a515186401000e5804c0780c1c4007143c0b540540c4905d103030b00d01a55400c907215661f500750710a041102c1403d05c40d09007800c0c0595100303c088404d0011103203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 907627706 1250 907626456 907626469
    0x501030c0503011503270c06021204050607050708012405010c030906030b01020a05011a03061b040e070c0602190e0a06142802240402030a030c0809092e05 68
    0x1190113108031160595003034502140240769062005501c4240385005070204200741003103854941c40368410194a64079072609a9680000384034105c22024104018025070808001078080c0c18410011174558545940c81b0b81d00752040001c00202d0b485201d041c402d6000266000c10004203800c0c00e0018425a541c6c50003004501180685400d254594000116a134420050710442d0354001b40200001105a4600d920318070b185142ca9129205950102d00ca00c82801000e00000b41c0c4c4410391460580f4182c101c41102d80010040c0702400300c15070b42d01d4041b030701500040c448100201c81c001c00e5104c1202c80500541d13078942115005816120040c01000c1e003000b6000c0c0c0600031800c1e102c0e12a512600401031905030f0b10f10020113101100804070f4502c0d00040c00c07a01c40607403030300312800408013034421420400c400c0307a02940c194050684040484d000d44142808a4001c0c50000e240100000109440c08000d43d02005009503400004c1c03800440d851174081c010320b83d0000389007142d1030700000508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 907628956 1250 907627706 907627709
    0x61011060a02070519080d0b0108010828061401150509010e1c0c090c0f020f19060603020603040308060907030608060c0c1e030406140f0d0b03070b041206060501030c050301 76
    0x407560020b0700409024003000a41c3e00395074444000b000030881454030000c21341142c3d004061050900b4001c40e000d40c018005181a45ca6420042102c841400515805042d104075a0400307001c64101348004160140120707507034801200441506545001d11910120109100030740c104141840a944c4caaa4006078007100c0071070440d400d500b0404440e0700c0d11030030318a000c0020160303455050009200700d104d0300008442001500e9020240700b12200c11307a1204c80e403072200d00c0035400c4600000c01030401c8143c11070125002d040000307455a1071f9400304505500940302503004c100084104885032400304923080d0300c00150329040c0082c0e8a0038030ba040d5910b2019005042c04103003c25403801c0c5017001c1201031010b03d03000402801e0700300104486512a841401510002510003004803581401c0004448801d41401e4030140f0b80741900c510320008254103c1710365071601698a000403a02c0d8458058805440900102202292145040070890b08642d0000d81858207040b21441c520381c11100752070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 907630206 1250 907628956 907628971
    0x40302060711041d0f1903050304030f2f060703201c090f11150904051503100f05150a030f1406070804030f020c1309060603020907030506101106 64
    0xa642c2400d000060150805012040d01691030480551400344006143e130298200c0350140ca9481e0f40714907115488111558020300458810400b00300020b1007281213889a40036460704a209040751610080c458034541920f0f00060f0034512110300d02c00085c003205412500505041003241c801502d0440d04a00c0c060b405144030b10045075400c59140220310002c030040e411801000048803a02c3c120704440c64a0005403901e040d08102c400940c20088032104400f040d103103902c1d0500d4401c00030040580b50041a5048654803000c400c0300a8404100c0c8410001c0350050104043d065810310104845004001000640403d100089141c4035403080c1d0094035080004a480000582040404a10342d840349d424148140403c1001072035006403c00e025501c40d80d1100741c904803c41040703a03100c0700d54a600f98030010b5200301d001c0b81e01a9074000b01105209900c0418890b40c1d03900020168141110045c1c0880d0322502003181601e410801641d9110b0039050000754240c14108055940304001c0000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 907631456 1250 907630206 907630223
    0xf020c0a09020d15090501080607030c02280209070e040c0c1a18030c010605010e030d0206010506090d14010b03010e03070809041a100c03080108071d0403090f090605090a020403020607 81
    0xc00601819006840000800e510039820720703170b4500410000340400d1190658501400c404508110b10038001d15801c058242e0050040d44420b00c201903c2c100758403000107141c0703e1016510016142c00c601a8030944041c0c0341c41c18060542410f1105403000050000308001c0c40000728000180007444420762541603c03038081103039640d20103101100e90f0200e0300c86403920004c039450384504415003140040da1401e071b0341c2403400c80038001456900c2e4113400f4920050f0b00a8801400705013402030207000340d40300041103034400a031a601c2d1540300e207492018445240c0d445540ca000075041c240150504801600021460640c1da616101e030a40180444a441a51503581c085040380002c181c40f09010802040c1082132405450301400c1015020344c22004240700c000001200d401c041049022903807220940c08543e07101c4038210510b840c0c020030480a02455080c0410008000b0b45010090003c40074002002400e080400141880040c00d445840d8010402400180c4482d019180540d5100d40328 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 907632706 1250 907631456 907631467
    0x20c010f14030c0c0f0d09060e180901180b010e06012606060906040923011217130f0e010b09010909090512210901090f020d11100f0f020c0a0902 64
    0x440c0582d12621401e00000d05c188600d000301d601000c542444148001c1e100c42d036006035a000150380700b840724040654801211025070104241d10000c0d95807100514000283c8440110200102d4155010040e00c114680100522240d54858011a0410002d0a016491a03540703044491024002c45945016031700e2400400c07000e403580400e5800c02c1d00c000700100d0312143c45a00c4100100b2041c19103c600750000d0301240e900b4001e200946068038011f96040031030300140e40780c242c03003e01104900030702800204448440c0320003140d207050141c00b02480d428880740c42c00c0e000f1542240180c128117110300041040c65007517a049001e80084a682403030200f91901c00703050150501c5404c514400f0003003c0050b40c0403107220031542024106030a144042119141d09803c0307400c950b80c0326401003017800300401d0304015140003500e0b0310703845100745401c4961242d00c001283c00e4600c0f184845012420396142c00c0212500049002042021880140700e40300031240010038591240c40f0301007041d98000740 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 907633956 1250 907632706 907632721
    0x90a05032b09080a030c090b16020a030c030501050108061807140105120114030f07081905120f1207080402012012190215010b0f09010c051507020c010f1403 69
    0x40d03189109100901c10040003502c0c0c101400f6a0f402000700c280003a01c0d00c00001400d500940018040e100104419401c1c0342000c1c9422040340864030742680e001100c10000030008038490312610203035109600110341ba514142c441840d0100c080c0807000306500134001403c060301e00013903010032180165420204050700c2d5005035014460307024240300d5030031150000f10340c2c070314601d0044680b00d405070112003040c4590540c183e00c4a0290044030042e07001950020b003400e80482d0141c05040c043e409542c1d80d051200c501c90300641c0000760f81c042d4540041807807106002c40c103181940c44100c42c18410075510f4a0360008084405000761130000402d8402c103290036540030044015606550520350740c0d03070400c07090095510015219408010720410f4030406a500f850385540d4122080511200c2c00e1092440810100da0000c10546040090a030484004140100402807600c0c2003810707502d03042d040c8050000d00700101e088200e4140728a6006510011342c2c4044c00f0000303002d80d005215129140c110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 907635206 1250 907633956 907634017
    0x14010309060e011b021006060909020f09030303010f0f050913021306080d051c27060b060f071b082a0d12030b030a0c050103330e090a0503 61
    0xa80c6030b85640ca40b11201034442d07101a2113600c2840c0396000c885030111342860300c4081da01c0302d02492002500c00e10082002030219005021000889a12682840040070100385907400903404402c0c135a01480d0100903070340601400d0009800c0c1515015881c0c5004420170f403d10600c00c200a0080044214800c400c614030751144010700700340300c2a04e8058815042c002c0c0142c008a0b80504445145042051140d490344201080140030014441800a280009801c418000c1c0c009440d00c50f218020720b1070965900c0d009005174855500c040780c0b1001c060070180d140650714280819020140d91061203900c2000036120045c0c003c2103000c1120086141d000c541100c04511941e03048408540da92003045000c050701c00401d01142d401f0801183d44108241d510400d954001d130451070004802d1240d03500c0703900444021010303000b60302d40480103007403800c0d04c288010455000256440d80e0600106071205609a00080e010b8001e01181043d0f413a040d0f181d00c50030308178400a400250001d1440341030b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 907636456 1250 907635206 907635221
    0x2121317040603020d18050703080708070803250f081f05120c1e060f0a17040c0609080a0c051c0501020a02010507030e06070c0b090307050f0d0201151401030906 71
    0x3160820345481d503811001e00a900600c850310480742c1045540d07581c00c0250001400120b030440c00601010b4655200c07600207600c6490f0559030181c00300103071400300d4900f40c003c40c0561545d0604d4820000c0040640030900e181c445040100444100102c1c1c800d0341c8130007600c0d0404d41c0d0030742c1d00454800001203913120360303c50f500982d00204c1c05e154401e0f120501048403030244800383c960000148c40c540311040300e0405031514586c0030300140140001c803007000c409408160090300700541c40b03126010200f0a80d0400f240c089030030070000c84041c0040d950240c1550000c040700001001d107444240c3d00e0030aa024180186401a01d035010b081d851070342d0301c20301c03158a5500a0000c564501d000d400085c0a05030803204000803c0c01c2440061f0090000500244030f000280c3e900000200203941e0340c180d100000e0803410703080c401841004007103901403114403104280b40c1c00034058400c100c0c1000e030940b640c40b00c00c040401882c2004200054036030380d41d02441c0809190000c1c0265581c50310b0720040448 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 907637706 1250 907636456 907636493
    0x114060613030f05010504110d1a0709092c0d0e0d0f0b0106032a020303041401240f0e0105130504020102010f050906040b01150509010806060d02120f0a021213 70
    0x41c00040404d1200640c41a802a4042c4071103800b06030011302880726651b501a0010142103070201c1000c0300005e011100781d04030800d86001c0181613940c802481c04d84030308400082401c00c04034184120b4804103881e0340d04501e501d4001e0114080c0f5440c0107416070507080820390154109680000801c54201400f802513503006504038843e58503040001d000f0142c602400d024562070341d41224074942d440c0542c018545a541c021440c5540d140da42c55400e07002142040300c9507480c1d409903d6080b0640100c840c2c030300a1407444644052074075049440c039100aa2082c28010349410051042e900c80005105030305820103400300300780e141e82c80100d0050002030f03002220607203090b052007100307440840c5442c041c03400341d0201c40c1c05907210701d4031040024a002d0310b0340100e1010003070011103500500c4001d0f80074400400f0785040c00581017108041c6e03880392a401e04090901401c100b2990b250002440d08040d8a40c806c504000448480300c180d43c03030150403010145224407140007009113111010094816 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 907638956 1250 907637706 907637723
    0x22a0406082a0a0506090618030609010f0b090105090103030c1106180f03011e09030201140a050414030903070b0d0e010c03020406020705010e090c09061326011406061303 75
    0x8003001002400c0b002c0150310454010107080d900b8900708440354140c42d0020540c9240402d01c108009190f44a46588075101d005840b40365815507060000074800c9155800109000240c14200c3c0c040300d80200300ba0344100350314401440349449100c2183e065079810b08203030302e1a0394642025040000340c11202c41e0b0080300015010710083c1d05281d4042c0340342c820f40d406445c0c0300c03060042601780c0d44251659030703080240800981c0c0b15081074000e40740041c040c0c000000c0e01e203400c5044141c58007045890011040d10f40085c003040020507030300b046032000403801546c1000d58040000361502e9591154006e00304c4041206213181655078010100c14800500801c07030344404a40180c0650414400c080c054000d048000519501403811150b038000000d000340d00d1039480302428004c40e002284607580114003030040380f0500250450100c013900c40c140300d00710b88055102c80c80c1c0d03079400441c84d0103000342d050404404035010100c001540050301183c6054980c03002195012814410780d001400112 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 907640206 1250 907638956 907638973
    0x507050103020c161401090806070206041b03020a0b0702091305060c070212030c061005030102070201120908040f18050c070f170c030f040f09060e0114040209120d0f022a040608 78
    0x212444080c036024801c1e07c40e595001d039101401615454100c9480025802031800100002c0c00d5611030440301c1c0d800803144d49026129000304600b07041a0700b201501090008014007540760018038241d2040c514011803c81e041a5a9410349403000034140e1010b8450100d040e01c115600c2d500e0810044200341c0841e074646c14404121030707460380240e0f4107d1401405070000300c1c0c039003410f0084601240d01a1240032418006824040045c06102410b0307848207030602c40800c10003020f40e103680c003c0c07405040c0d420640840c0000f00c0111100079000f0904a2000c004480c001034082c0200c141076600100e511100c400c4084403e0303968814180102120302001580b0030300b451119000c0c105440c0c1444a446c2001d8035210098101c80302c0c0c0c010500c00402c1400104260a0032841114840358090005400d11042c1c00220b1103010340729124a1a9070001c0305010301ca00d5209440b00800702d1301d0320042100400c80c07424098280c1e40109803001d0034a600c0c401c80155141d5811280080091004584009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 907641456 1250 907640206 907640219
    0x22506050a05090c060703080a0e072c1905090a0b4b0a2004050112141603090c030b161409060a0e22060e01030507050103020c16 57
    0x4020841e035582100d45084082080400c0010781128440f2014043c580703010b415860a40300110b00030440150036446c0e0348801c0101405000703c000401c600c3c25603108441c01c8012012411440e6510904d00101741c0701007140e0200c0d107610703140202030075040004035910394100690502c660a030b80030340601d540b0401d000400c000c2015100c50f081c0e42281017600162032036200102d06210813a008141c40c00c0564a503a07200151141c5900b00d590020009004030320300380e01c8660300098800ca9103a019011500b0001941c201403082c2a91000d001c0030005003061008124010b540a00301817242c881107988000c20701e000e50b0042111a8004031980042990307490f04040301c0700116070400301090944803100e411401000d01107690f80000203514204500341091003010f07001420060200020f100010451352581441c001e010a51080102c0c0c0703550082412100b6246a9440403481fa681c01d0010808210041624811348009180140c0e46600321307010140703450403142e02c904d818500030500142a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 907642706 1250 907641456 907641461
    0x20a061101060503060c030a0e2e050c090d080f0724060509090303010909030e0907020105070207061b0b040c1e050906060301030f030f1101060f081915022506 70
    0x30011050000e101083d00c81043c1a104d240980321030504c0701c824804560131841581155080e40040811101c000007081482c0021442002000f001788940c03c0241540a60700d00a159120591040d0a4078090189001c281e2103914103c014048101c0480c0344d074561814101210740190300a0050f003c0c4100902c041c08000c00400d003421103061500d44005110300f08118117030f11a400d4580950b003540e18103d002001341880c41011810445407400c02019661b4076603240b070240c80781b94000a810b10741441c01914141994004034184601200804050240c180050043e9035000c05004529110b514004c607007502c2c245c05c0032040f0000b100c440780e20540891203e800b200d10854449415031128403e10100d0f00c400c1c0000740410489d92145d102103405900214415101850100a450a140b403a135003140c10b180c110300c00f81c80851310708100c4000100f180d0f04c0315884040c40502c0700c922684e81e400c074111600d040d40080580200b003845c1044c0c1c9000c50031194071400c5520006c06402803500400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 907643956 1250 907642706 907642727
    0x51603110a03110610030305031f0510051b060603033910050a05011a030417180a05030304140d1a070509120606010509010c050705181b09010f03090807020a06 70
    0x2152003031071300140d11030042e030b10030a04494260711414035540720000100c05282400010400568507484000b83d5500d84400781c1e243c042d103540d503140d2104207000c4410382c143c101c5116405c440e880342c000d11505070f40c00b01c201c0311000005034800000401c5072040071056090304958034045c00c580e40040080342d02c045030303a01c40302000c00b50400c00e035a03540d04500c04482e0203006820084803c0761140d074244109400464000d4065100740c80c041d071424440e0540760f44130424401c091404420015030030300344506c102c0c0c0901012400b85d0b003042d040c07000d07500319024614040e078031483c20800010148503903603810500121885204a14034505400054155842040d08601620b1a074020310015200480c10a0181c18143e4642d40382c180b03143d00440d001e4803149000e0740c103070060a02c00601559110f03c50722003c46c800382d41017203600d000d142010540c0300555200381201010000c44125aa00600640714081d19040000d0750441c181030000c000d000f00000250090074015010400e25013022202a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 907645206 1250 907643956 907643987
    0x913150314060906070e06030a0f0f0218041406010315031209180e06010302010e01170414060c0406140d020d020c07051306030f02040509120a0c020a05040c051603110a03 75
    0x2012620f0355040c050f90340c80c04841090028400300b201c88007901d0144010768010106920129503500c014103503104546070703200d4069045a000804c02410160926540b000f52004ca400300200802410324000320440100510b0405a44503100c0450800c2d13010000f019540050242d2030188070218054a02c0206001d000da048600080441c00c00358076000d540450700191002d07156591039a8015140c503903088000c5030601c0042e843d0b44180320b00260003688618000c807406000f210610a95071704000c405004114650300411043c8425500403410900d00d4810000320350b84d41e0806910000240242d10000d6035046c0005040801008009290300c00d481e4102d8030402c1c0c0f40589020241241c0b0544001804100c40d1092400540350035808594014403060554250480c602100e94a0781d012100281c0800d05021125056080280326100500000c0e58104103680c442c0320080c0241c0520710004500065000c084400c00d031060031b903c2e280c40540011106800e00f035160182c8005050400348 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 907646456 1250 907645206 907645213
    0xa060c0f0f050a08030a1409030d0c0306081002070c0f0f1205030706050f040516150509030a0206040f090506090708010b090a03050601060207030213021603050c070b070f0b0a0509030913150314 85
    0x140c7c7c10741d888800c858000c40541d0021807414aa8042c904086c05142110405241d660740002070744034400c0c0580e03000662904401641c0e03121390f162024205049070448280e00b24500002d010140261400c03609603144108070307000300985e0b8a04140765100d00d0350001c0246081a00707101128520f4400705000d0f9105105032220355882110b0300498610a1182c0303038040b682041442040b6007d4001020ba91030007070306862080700d1540100d911984181e01044090a03141c1e82001000440d1103403030380001d81120002e299090403240100000018024540c1003040007900034501d0743e440c035400e40259400030546100d90794070301c0c0203525059203110a81c06980d281c0d01e035400e41040d81c0308950640000c840c0504600a19031821101d80c0c1002e0030503040c038030510780d010840c030094002828042c0e02c1401240100304181c607004610420241289500c14100001d0284126000c010b07501c41c100241c0f020701d54a01e460310b02c2ca028002404c4140f9a001c601c903004418043e00003003409540c5010403c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 907647706 1250 907646456 907646471
    0x102041206021c1401061d03010218100c030c0221010f020913020408192d120302091302030a0216080a0e15040504050a0623030c0a060c0f0f050a08030a 67
    0x100050701c0c000700c402c4404c00000c00062228a0099400101c01c20b0300c4195407204034480c5c008242280c1c428024081c2c1c0000b54400f807803040c6000196440e0014680c685684064490f0380c000e840e00c081900024454a00d050f060301c0c0d800d440ca4000e003022602c60700207020041007950148002c0d8800c3d14058003c401d011052840d02030540225021942c45030028525000c0c00c0e1a04004d03000001011102001361510048003081041d1144610110380900c6510350b841e940351242d9004001c1070343c68285401400082170a0b40c070203c1c008400d140403000940d499492005c1c602c002e125400c0c00c0381104805c09040021b0000c402c1c064030b90503807da2602d011202081003001070242c4012490748100d502040248080e00b419000140c0000d248500440c4190326441101c003540454002d00c5101401d0004001c041c1c07400b0485120800815101120f46500f04403008014098990003d8031038010890b80e042045128908004080c1e000004c0c0c1c0d40340702051400c048654019643ca15041d0300b445035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 907648956 1250 907647706 907647757
    0x301091a100c052104050906120d08071e020d080403110d09170a0b0a020a020709090b1902131a07121e0305061c1703010906080105131211010204120602 67
    0x4100d10040184d408500b41454030041048985008001307d8000c00d00c1c0d0313004c0a8041c0204104115421075803110025403a0150005042a800c2080d841200b0300c0e04285502d01500455040e4200d44039150148441d6181c0c02d0655820304401d511084a10501c412405059481406c00c4181e941003d00312128955000d407480e41c454408034060a080b03202070108580c04e00c558001c0c00114550700503178200980d03584a900485211701000d6a07561900002c100c0202e03035400c2c000504480d003003000c606150b40c01940041000c80b074003900045483d41c400b20311007a00704c001030b1f0320601d9000d00804104c03610640c006000603c1c0b11608120f00640d001c0510409009018461003070002030300070740014070f078001d15814508010105a13500103102c0c0002801070081c81c001c5010303007178007100031070441c0ca000b0f156801c440009041c44060301c1107401550018040d54242e03420019680f414116810000c41600d00a1007640d0000c0e50420304408180c0400155030040c2c5510b14141e020f1401207019441e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 907650206 1250 907648956 907648993
    0x412030903170115120207080f0706090c120b070305090606010e15040915080703080304021516050303060f010305011d0709080d03060302010f0509010909050a0b0909150610050301091a100c05 84
    0x8000b090108103203c940c42025274007003d003d140c1e01a150101ea1008252281005400590083d112150507103100c1800d1203480c0c0c0241c0d400940a1508111070710f044078040341c0716540509180c0c100000800b12445690740c1c1402c0f280c0d2040180320440d0347c0e80d40e40c03600c04001c01c10242650f01200e203c1707200007490200440c007401160b03003100d003140c07455841d5402c110703611b0000c80aa0180880a00109010729440110f940900c2e12500003181d890a1040803c10342a24901000b4101343c1401c006102642c0b4410040c000c4407030701502e400b055120004c0c141e9828040390006081b80c032070110444840d076456007000c0c0c1180d000ba00c8448a481c0d11807022640c034480c007000c3e9804100142000c228500050707000d994011180440081e02c11040d600181941005582c0702d13a0ba540308002041d1480c4058035010b8021604442c81e521250500502034a240014030071038942c180c0e00d80d000323110b21202d0480000f942c40e009080c0c107900c4c00c0100d40070b00f0050042d201600d052240c40860f81ca40000d10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 907651456 1250 907650206 907650217
    0x402010801170c01081008060406050411030f0304150e0d08030f0a060608190b0406092c0d12110f0a120c0516020402091804061404120309031701151202 67
    0xb5405030071a052040019288000040c02c0198143c603101310020b80360805010141c09079104080c0402c107410141001010020341d0011584249c1100b051490742800c0002103a0864000c9521450407010200c3c0c10b81d101404c05003115044180030b1004010418010300651084a25413652240c2d600d0f0307603003240200e070000c0c094040480d6040c008039110304009040c1d00e186008030031004c584c101c0b1000110301500c3c140c2c2d100b119519161801d180b0080740d03146010000e03c01d0301c44842c0c1215084c800386a030300d166030008a8140207025105100548094100645800881314050781d500c000380b00c2c01c02e407a8040b0b8035501c0060109850700c8031034046406501204203842d92007a041039855902240240031020040382c1c002d070b0070003920b0b95980b640c4e4400c0515181c00105034106141606240e41030301d02800190140c121002c007000002101d20307003400394040f02c03458005164512894103030391101842202141443c1040c1c000240e12203523022003442c410003642c0c0c00c1485040310b0403c5050b4003e8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 907652706 1250 907651456 907651499
    0x405010c0f0f0507050a120c1a0c090d0507080304060e1c0b0106120b042c0303010e0a0b1315080705061204080a05040f030b0109050c030603060a05130204020c060402010801 76
    0x41100710040300e11400203418464042c4082d034041041e242d940b0b031f2202c902902082c000ca094207248805009811501311601c5041a00c08820b92030600881c45503803003501c2c0a030b841500b60120030003d00608100c4139000c0d001e560b0807a5070741e0351610800303401100160740451089408802d075408404a0301c07569400c2580c410301400284c0d09103141900c11070030508500f03034402c2d03541c150a505580d0700e0046402e00070403110401c09401c00000442c02d44500c1044400c03c5030b00410040100c2007291400541c0701c1c08e00800010000342840c0040c2c8680040700c507980a0908040c0c0c0742038141d04640d000c0040703481442c1241c0003655a130003401040d0180c000b0341c5190019090000740810382c4c1c4d80003040f104c180da1510a150607292460444414a190400d81d64850940d0040c81090100e11603103400850f040080340c214a400400241d64800c0240174030b0600c0d1b1140040384070010b12182480348558018015500c42c14607072a080d50b658401c44050f40061486400000d001c405051041c044420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 907653956 1250 907652706 907652717
    0x12060906031e2409060501030f0201030606050a020c0d060906050f0a06140f0f01020a02090a1433030c18090c0603061806060712030b04110c0723030d080405010c0f 72
    0x590707500074603110b100b50f4140d012040d00ea012540026049201e0700d0f000c0c40c4611489113044456000050440e1401c7d0404000d0140400108841035000143e00241c1c076130845180c0c80540703062130050302078000100010070f11406c10003070000d04240d105c521485031040c81c03020024144e854021041604100c001145c000130401c800e00280c4c10480006114040180111080c0103000ea001c2003154800302c0302e40d51042e40c2ca401c03e00c0001140c0b404941c02141c60ba2110094250146140e0020a503403c0705800c01803441518460645041c8000c80c1d030f40d407009000b100480071069018401c80402c6585000314000c03140c03c0f00032881c0203016280581c0000d050b03132441e580012240c04400c030f00078242580c0301500340040c40010303d42c5403c1408030784a55a012483c06544814401540c201181409d0043e0003448100d81003a00000c420b4200c5040361000408107030003401fa441d0000c80d91640e280c041c002c0c015500541c5811240070f44c0130340e114100800014000f064211610040845c0c8400000c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 907655206 1250 907653956 907653983
    0x40f09050408070b0f0703060501091a0d0f020d0c170f180f060c090f010c031e20070f0b0f0405360610020303012412060906031e 57
    0x4a601441d407181c818240b4518200c4161220001403d0856581a4030080541000350b013035814000c14004150a0810750b8140e81018440794042c2e04244101079030050204040600781a150001400159095030031560394900b0140b6501818151007510082010b958210103c5101b01c503105109140102c0c0104054840f103003030710540c00103000d81040c10b11801d0f801c80303031455040c41894041d202950101d6500c5e07058006200c0304601c4a00d9160502000340b00b46004260001445448124044080503c00c1c1010700d086c7d4088540055949403e0b03005e54050100700d0b80000c001d01503410105580501641c0c600c41e0305c2c40740c0f09410044c00c0c10b54082c08200114140301c00c4001900904008100c09904a0002003402c070240030f129620826002040c05881e01700445031110075031043c8091440d660400300400314003541252012816800d44000020080c4902441548a0716264042c070240344e1303c0245c1710140003640070070765041c1c0c000145118412071500203010103580c040548168503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 907656456 1250 907655206 907655219
    0xc0603060e0606311e0603020304020d0204050a090804120311030a0c0605060f13090212161401020f0d03020d06051f080a0e07060203071e0302060f06030a0c080a17040f 74
    0x66440412800c00b0084d13444000d110402407000ca030b00038002c5001814202919082d901120f0813140d4052424140b0401c107200250320703645c441c90070741c0d074050720b001c07910391184c03804040201401e00c409040c0c1100440d011440021101d400c50300c075030203070356001d049005440c00d01e0340328841c400c0c40102080044a101c00055155040b503503220700014044603541d400c3e0000700d04041204140d0856072039036000c4070002c61401150768220084524020f191078030001b00d0100400c880c0d4050441e000445018580301e6038400c0201010380c50f0038605548039101a84800b0300a5004a0241e400b03450402c00089424207000360146800c00c0c3c65454240880310080c01591010000b90000480d00c0d00d803c0c0064820000700712400c01030845600a560b184414286104482e40c02c186440707082501c50440c0703021a600003042c5400c240702510700019a10340c0c400080c500880520000d0480c05032070000907200d140030402e20780070350207917914119689039a121682c80303118501403420660307060703003061007003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 907657706 1250 907656456 907656487
    0xd0207120809220f1a120316050f0105090d051209010e0304230612040305280306031a22150f0603020a12080405010305040f0b040c0603060e0606 64
    0x21203001d8442546024903100102d6400403401140c800404103110340854914024400d80490809000041050864803108565000d900074402e41c411501ca07182400e400a0a0041760029031608100351200c817590714009071500380039145000706502c0e040000700d201e000071807810160351140d503800e0714001c19002142d0581902070301140240d9070780d24001c88490000c00061003c4c0c040005100850505d17034000382c0208003050316a03401290244a000c101404045015811a905080040c0c4400111201400310711101c44440e102200421074515180e41607403009003903d001b09607442018102c10343c130f00030340c410640718804103815800301d4100d4a060200650b426030711407903240c10381503070901c0c0c003400b03440211440c41800799940e0010000c5103003200300e41005120401d0f84842225081d144d2010034020342c800c050616440f1000241000003030034408682aa200300c10242a0a040c10300d06407081c51402024086403400d100451402c805055803423140e600180510715100020840110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 907658956 1250 907657706 907657739
    0x421210807110a020a0806092b03020c030f070804090c0c02031005061c05060619120f0c080a0302010506090a060807140d08030702010209010215330d0308090705030d0207 75
    0x82e401a04054001a074074039034907900903d14000140510700302040036600b481d0300e0f100301b0000c0700d400e00c0c5020107101032403125080500c0c603410016114500521071a045d07128100e42e615007804001070303603401c00038110054415503803024410010707040c400d103080d0b801c1034000c81e000e5410382c0054000c0e100023420307030401079200e00058514000d07500600d400b0800c40141b240102c46a4020100700941c6062040c140403610008043d85100e5914040d80c0790441d0000040207800000100204c20a00504004e140000c3c201c500031030b81c450085080c02070080909450082c424000c20010441c418410b0046406035980040900340b050728201d600801042a450001d8000b04042003507004546484003a41c4602e401c0e800159841503200002814a42046803440c003c9542200344000913041c01015490742c105246101021103892458250341c0002e10400c40d0302c940501d5640c41010740c422002c50044d60050222000300da1154105921100b041c4054001a03019070b50402824441c04100031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 907660206 1250 907658956 907658987
    0x1d0601050426060c03011514042301080c0337141009021804050411030709150b0412030c03050c151f0501050f0f0421210807 55
    0x1881c007035881042d06008030140114006440310181141c0740340c1000d001d007036400104a41c4103071071036060680406851181000580c00c0180410303911590b0349200c0708840180408001d5981b0504004c80c107071151103e1014050b001640c80808105400c21110949020310764a1100c0c0058550840d142009000c004445070300c2d0524900080326030b644c6920583c1d001c101020300060300c0740303411600c14075021204d911501c05544100a005c81d443d012181d02504540308844c04103aa85075420080c8041c5a00d0070700b5a8903002d001000504103e107a803149581030082c8040306001d03591900b481815020754460b50000810070f003a1a0006841003000516451007800c01038104884a9000c510b0304c400a6555402d40e50160705004801303800c0c40011705504400f0705001841414100002c1c0749014040c50090ac400022521990303100c0c1240980340545650036828000c0c18000c40039011444a00c00c4c2a40d60284e007103010000000711100c1c840c4182015241c48880b43c481d0342040f601481c0c1400f425 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 907661456 1250 907660206 907660217
    0x71e030b0a15020f0d0509040c18150207081f090305120f01090e010209150c121201051504380c0604120306030b0a090809031e060a061d0601 62
    0x41820340d54020725201810000d071000b030031a12800d901924000103e40c607110343d6813000104003200c1d030340101106c10780a0241c401045040018034195840d5107503140700c000481e03588902059820303050b0b5420160280c2c41c3c0c220340707c00742d460300c00030749a0341552444001550184000381841c081504548880d52191400910342181c10007264510361041d2000488410000010020340010380209806610940001c519100116000560b90780c2800d009980c0b00c1c03408902c0440f102010b02029074407802041c00b440d55a46158855030001d03c0900901d80300b03a0400c1d001c04185101881510140c07800300d180c2000c0086110310840c410200c0380b49156001400908501e0b0f03806082028100d14000900100f07001d08280c80d01aa801c4042a034034000c141c43d2800800114864001c1c840d04841c0070803001400c0e00c2d6078200710245120b110340700c07905440745404070001840d14030140c040c1500f01d00c00740e030595140c50003903000391f0b03d880c456140e400f201e1503203200c0d4213120366143e5508110141402e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 907662706 1250 907661456 907661471
    0x60d0c09020f31061d010e0f12150c030103120309060b0d050607120b0604031b210506010e01060509040b0310060b0d0615050a05030403170a1d06071e03 67
    0x20980c6110000e4410f4426150a4418031051502c43c1520380150016050a80362400c401008001502e40c20b0180ca0412003e482d030140b40e9101d00c1d00500b90f025016015031884c140c400003544c0e4070080c2d05d0310003d00340c42400010342e40b04000b4081d00c1c10303a40c0c03190100e890440c5040301100507105045054880c00e03a03910084490303a4558080e2102948200060481c6190041002e8070110707848104501d00e504105159040ea51480100c1d81940c0d40103820b40140c107001945000d000c01c039600710700d501510b07866900f840502c11f03400291130503110b0f10403144542c2e00d03001d0b04060518284182c03004a40d090008000a1600f0307004805005000b13001c6403e4036485140a400340c42c1f1550004094840c0013901321031140d51405090040c100e2440305061000380c0401c02402c0f07100f00d00d8050b00304600030022500f05032150080d40380e00f0030100081c01050401403651001003001030b80790241e21600c0907143d011590080b43c00d9100e82410345982e401001c50740304c6421010880c135030400030156102c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 907663956 1250 907662706 907662727
    0x2030616090e07031d0a12180906240e0a0b0d0e0d030c030c05030c03010311030a0b150109150f051b0601150e010203041404090609050303070314060d0c09020f 70
    0x2c5115403c0c503540070a01920701a1604000040d280e09454107404c5034000d017000c600c49154003800c00407a441c0405040c0c6903064100b6001405812801152b414554001405003980942d01c940320320083c00803100c1540200241e0310317074004c004000d80250742d02d0000c100100030000503244051500c030010841800d001006424502800c60420100b680c0c0d0003100c4040340e040c03080b070640780aa410102d203903080000702c100060205220081a90726081c02c0b1802c00d4405010160103180c0c0841e08209608001120300d141442088510b800a50800400140b201c540706000712050307099240d0400000c060041101c07a940103c100c40049024415640d0204008020300c2d4001c00d88003003101d032101110f400090411500711700c070034110350041c04140403500051001d12680c240407680050320f840f8a16245015101880014190340000700c00c02c04021703095000107049804451600c5001e5682000b003040d00d10b0008009080c4a48500c414031500c01c45034010301c1c3d00c0400981c82803e01e0340010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 907665206 1250 907663956 907663979
    0xa08090d0506040309081c050313030306030b010308030402010311090f040525020c030709051b0a02012003040b06030601180b0301090203120a12021801030c170c040602070b070203061609 82
    0x3d074100c001500310442000b000c102401403145244100042c2404411f80c0b840040c51400090800ea550441051017941003502951000c0001d59021300c0e01002580c0d02d04003a03816800485003030b40440d08050b41102c442d2058002c0b101300940080140799400900700500008080050070800110002c0600c0955406280e60040700d00640d0750080c900c1c11105028581400300320307480b02c01e104d800c150038096449004d1084103419022140b20316214100e24008a002d0074881c28031454001c141c401008100b046c2d08025031041d401400e040d20b564480d8010306907181d0b42482100b4000754041201c000a00440d04482401100100082400720803078002034202410583c0c5001e1000e400990506c01039000301c1915404071030460f0841c10725940e140b003858030101c41d10f01d0b14101542e030103034112400d0113054280603282c00d442909445142a400ea00c6171035209014440140c40f403004005405030b07401701110052503016001d00206e07124414030465038400000948240207071580013141400662 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 907666456 1250 907665206 907665211
    0x50102040f03030e0a03020a0519030c121209030816080706052e03030206060405280b01032004140112020310031101020a121b0c09051f080a08090d0506 67
    0x1c48214403203a1442c6809842c01c00b4101c481402640a042d040025956105083c41140c8042c2c0781140076440030140300b005250580c0004109000038040481e40080303000019031128415405108903200000040da80d154081c4001007200c1c008214196002c00041c5511091920a120a43c2066041d584076410703036000704c42400ca0f24038540316050114a20005480d614580300300c0360580746042d51802501d68000805640c045c5440701c010071090840100914075070301d0305603100303a54400020606406004100388803400a801c01c0c2c42c00c400f070350b141101500c040781c5035448540303060b10f41074807280c548001d1141d07079040c400c00a000c0e00c20401203000440c070800001701030790b103201d003940350640144c040c01001c24115070025003207100017003100500d1000700089092911110110340c0ea080140d44120074010f059a4004100103001e05c0903401c800e025031411203c0311461031385e86e01d041d050f1b0300c010702c5130303041640c050700c02c04000c2081d00c402807584a00181500e80780b480742e604e4040c0b400005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 907667706 1250 907666456 907666469
    0xe0a0b030703061d07030507050903010e0706140f03010306090309050a0b070c0f1809060b03070e0f01151707021504140705060306060a03050603070e09030a02010b030c100305040f05010204 83
    0x8001d0010b9052196801511107039052941016030b249034482048001000b0790145641d450124003044e0260041e5070517203000030000e00c8290303842d648450b20b8192622441d00403030628902c4071407440207207003564802d803940014103046038a10f0316070502078210f442040d41440700000000c81e0799100e102886001c0c101c1c1d2a041680d40c00c00d4542100003a0295100308584042e52606000c00403040c000812160261400440e140e2900d051200c01400c1a807084ada051041000008031001d800c0802446201242c1440849070ba0f100a039140c0c5042c0e0041800008144407500d0056585013080d0517080032441c4101c2d060548500f44081e000182507400b80c400c450303250001d006210080019001801c4203440241c19814604042410381c007903041e20781c0515480b00300103540c54400b002484005c0c245010f42d070042e8185940500e0b22036000300703480401075007040004c0700c8600b0700040e22240107401402c480c00d114010b80e07084001707103c05170040b120304243d11060b00200300240094070180c143c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 907668956 1250 907667706 907667729
    0x6060a06023417070510050d0e011e0f1410170106080102070f0501051509060402070609151b020705011707120912020d170a020702210106031406040c05100e0a 70
    0x2099000f052404240b0343c0305074400c100701140c60a5856200d401e0314405440d60501044444013140d540e0301401d001170121000407400d8849404280464000c03900740e40e40705004106024080d1400c5013620030881c0c2103041000a10340c20007011032100fa12044103582c1900000381071b900d852882d42a80c2c80341030190340200108034000103105d02840b6480e00002054610040c420079030b030108140c00c0d00248003a200c1c0f81d02089560500c5800d0300100d503416030105c2011001903818024000401004525800c02d4070100742d10000280001741d10026034005031245c010684c400108032039900700082125042180c800d48081c42c0007034078014170400038810040440d400301c6002c030080c43c001455046000f0080c0703506640c07010b142a000d0168004444403005039607a0f83d41d00202c0c203441d0000c0d064a0340750b0f80943c131401c105501980010140c074400c41d050004610034039603007991108182e501418400355103208002901d40310903031400d42c0000742000d2078100820b8000660840099001100341c64 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 907670206 1250 907668956 907668989
    0x1032a0f060c06240302010518090c0c010e0a03081906320d0804121b09020d050c03060609040e1f060e0a090302030a051309050106050c06060a060234 66
    0x5000d000380744c070a4203100c1c0301031a440c60b400030030000c040d807500c00603040c0440011075886000d01621420f9050001403e03040040c20001d0307000c01254000313406191554079001d4411b2440780049094482c05400d9982d01d00715490303041e441d0343c03e2900d08003401402c1d40c1d00c450006869001000354100d0242c0070000c2c60b00107034070f0301388004c03184000d4409a110ba1400800f20002444890586003a034815418205031082c480c54448543c03480300d8495404a41c0b050000564072407547c00a0a40d131690b2802071013030340c65041c8440f800c0e01040d14459070089040c400d0b42d086040c2a40035084e0340c3c0c1e030b00f0200c1d0351581485640300030080c00d50158940700b9403144010700c500c1c0d510001080c1c021001c0da004100010303441d20020749030701416a400f0100b0200141c00440c03580110025070141030f58141c10003565a440c50050030951200d601c0210341d001e41c000054139840d14403421401c5921903000782280803800b48501600d000c0c101d4030f400d0700e003141c0036284031810522014130024084200d040c400d0301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 907671456 1250 907670206 907670213
    0x3041b030b01260f0316060212090f0708070b0315040f0e2832241f0603090203030f07031709010507091703160602041d01032a0f060c 59
    0x2d10101901030002c0d401824001300540d03000084038404510700c0701080d4048160328212003e03100d080c010742074041d0a02d080c440d175280b012400201e04180c50342218803461790b0742e1000340c07907032287d102d40406800140f0001d051036010328041c40c02910700810004903088282002001c43d02d601d4192440c55220080d0351840d00c1d012003c01d09030250084032420303c004ca9580300d2000c49000411482c0c280385a003410300b502000c0c1482d980744001c188094170314a01c1c0301c5103032070306d800194142903c540042402096010035035046a10721000e0300366000d0080c1e81020000c0d0042d2849c50000c80e0503200402c42c40304480c50010180c01c0151295031110310384410081049102d41001d0460816a494001401400c40d082031412003101d010000c02c1c80d51402141d10541103008600605024243c1c4500ca00c0401c032280e402801a40d49030f41060125001d085c104d1051402c09010040032203551030b42428001000c3e041d0201600024105050340580303a21201c1c903410281c0e401400821002214601003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 907672706 1250 907671456 907671509
    0x503071b06090c1806030f12170108101a010c080306010c0c09021317070e040f06050a0507080705070b010b2a010902210d0c05010e070b04090c0503040803041b030b01 73
    0x101c001804107002d061b0640d03d91100310706000400400d501038900b0040310081c0191201140c00a0b2a00c002c98550383d240142d40c1c40e03501d40c81928201d03515080149004640310404481d0340c0741e040e9542c402044c019074440c012944068070442c1800b449810f010001000410354001800d020540540c59551039030080f0600180b42d00041c2d15404081c0b801514500001010350803100419101000ca460f80d04146d12401c2d01e440011702a1410002048841e031002c0d00b026008440030b649800156540030303011141409102ea00402100b07c54004110040c0440090318260040d5950822101d4100180400ca0300b2281020521a515180c2d04000c1d40342030b10101c0070039801c00400000102811000c1602c8441169401c0184881038040c0d00c148a42580040313219600e9008950b03500b0340302d080d0001103401c90b100b660351407424102c4107200b1500c54000d5070f000b41d501040603411601e50307030f440d1842030500414140e8000c40c02c61000000c18480842a4001c208003140c410310300b0600c600911030f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 907673956 1250 907672706 907672739
    0xc090a0f1802100c1e0c17030702090f16141317070b071a1807060e1c030801050603040f05100c030b0307050604120c0f0608250503071b06090c 63
    0xb40600c1307080c81d0000c82d5807070074070b09110388000000b50104412440c200c0e000c0801c5070041c000c6255500c0d030603080703810f0000c01051003078001c4800c0d849903075917128886428041115840b8075074002800c00300d00d29004404001110003245825030801592244038510012140d2044040f0032512886490030340c400e120031009845a684001d20388000b90f2111842034429100d8180f8020f41100020b070000c0300b10700042d8420720140250f400041d604e1800800e05060040301c40e12074120b05e4440f04640040c0d841c041203555040e11124216072070030b010003c0541000700141c1e00c62840001c4c035000940144404c03c0c2d01078800314009205403214074010100c2c0c00c0071035118040d0f400440240455a00c01c2c05950881c3c803c050144202e48079450054007000c0c0c2a8058501920b80800200380160801a02880384005030303821414900d41500c2c818a00310ba480148010800400105080718829450707000060301200443d05845103541d00c940c11105030304015242c9074402d04040c000c0f01c801580058 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 907675206 1250 907673956 907673989
    0xf03190e09041b08070b0909070c0b0103060b1003051302042309072c061306120501060306050907031a07110f0c010f230d18060e010b01110c090a0f1802 67
    0x91719400c1804841d0383d403103000245c901c501d020701c000812041c0319a84e041807440d031000640c02156540c0c50004090004603407168480d460440003204503612070b200c0d03a44500581c044200c1c0b482c95039024400101076851418494025104a4100b030252200096005802c5003004260b101d00d40a0342c0d50301d402400b40c0c2d840c01d4000e1340c90700244845103401126081141243c03240c0200308007922040007400a0762020052881280010042c8001907100720100e034002c81080c031141d540c8510454842c201d900008019540c1c1c07169480865a641e80c425501a030340b82403240114800d403003590304d01b8050303829070065640712002091095078010307100403c0c0700203810401400094071001d40811000443d20b0a244d40f80030502510303910f22500448110450903020a1980c0c8040c10000003800385070308410303999030070b0031040d0781e455105440307194440144c10007410850400030200300589002074a020030664440c060202094000d02c107111100301c900d590b500a03264588148060400c0001040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 907676456 1250 907675206 907675213
    0x120503160804033e040e0a06020405090a270f020a03060b0a060302031b030402030a0b0702160b03010e070c020415080a060f0e1f0e0a0b01170f03190e09041b08 70
    0x601c400d030800441c41d0f5503881c80541350089440400c0407074000c00c44002001014455400000e0621100d5401002030340c409840001450307031a43c41400a0f1200410054032807104822149001c20749203010a1803e846407084c8a807084103a000121480b060f078001356901641c4d01d03400701c52803803c0c504030b00c02030060781010760452520410344509000c480301e444441c1c0d00000300241c219a010300480407031942c49000380c0060304003044000c1da114407400030700c03904044042011980e5900c4409030ba0483e9101400315006941e01482180e0b501c00400049801680340d10070a2240790400c030454000e01030400040020803030a08040081d10160724454005a140c401030000802c00420b10210011903ca0021100320030300c10480000c1030580700000042c02044114410001c0107402d0b94101d4a450914078a40340c5080d900035100e9200844991869104009960240e103600002441d08402c42c206440034040000c080384240d80b08a9040360b03507000c150400701e1464416051300b00a040b061005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 907677706 1250 907676456 907676513
    0x806030a030818030904050403030b090106140d0b1804060506270601050a050c030a0207230109172e0e0601150c141c1d010912050316080403 62
    0x9000b005014007000c0c449011411903d040460400840d41c501c14003410400842c0b4250800800410004a40d144280c0300c900c000110303d4400d8941940000164131000d1403e60402c1101c4010910031202035086020b101f80d48403000181c0c81030310b202d540540c00118203450f007807042144020003000703c0d08440c1c0020403049142e18201c004039601103802c2c20302a6444400d0101a1418001d1085420903803100156403260142d0220300070007103505900c103112000c07200b003840e00c5841c0f134440700050002c1c1980c001041030103249a001d2859024000036500c0c0028550b450180c0713520b80510380d480c46510f54100100003032051050103e01000313200507080701d5050003110311101502c0c004c4601005030302e80100c41804000d040150b081d042070300450b00340035003889400015031340d803000500105138080c11920740043c10041c3c03a801c03074805940d90007500d401d000a01d4980141404152114401400f50103180b00d041038580000034001d40e032080c0c4992541c07400283c08040c1006400b0301c1c582200c01d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 907678956 1250 907677706 907677713
    0x5071206031e050322080705040203010308180a051e090108070302060a0c05100507080f0702061303030e030403080703090f0906030f0308070e060d090302010f0b0303070b04052a010806030a 83
    0x420701c1440c1030070ba142c21500c00c094184680b65015480040e07800481c02020412001190646081228444020303500708560310401c000032404240b00c0504180700402090b006540d002c60081d828003401406d0480302a00c410104080b40503119014901c088150040482807400240305030041080703c000301040c90966002c5034840c050440190148020000403808210050010681b049505082013002d441e01c03840040c907000054448558910568000c9961184086540380c0300d02d01c86c81882002c02042d40c2c0442c002c08400300129294002880048006100b0000a091690207582e030351181a0034101017130302c4000c490303005034007040c58400104001400440c80c440b1482c0c1600f0071403956614928265412026042c41a5000d40c0005446c1120800c2390f00107400740d0b01941c000c00032091502402000c80d41407402180e030540c001c0c840c4600044032040210750080c80388080d03e04050356483c8820918450301d400c00e0700141408902c018550340420883c0d8440c00850050001e10070a84 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 907680206 1250 907678956 907678973
    0xa110705010905011b020d08040510021528020307080403021005040201020c280602030c0c040b06120c0409050a022107080606030703061a09040e0f07092c010507120603 74
    0x2055606001116440c041c96040d9840031081c001c0e0047e003d030300c650800340740c030140c994000e0040c03500c0341c400e4501710104507200213070a4500401c1002520070705e0711750400704140042454112209034241410b0410301401c1030021758000c05054980542c98182440c4c080d0800708400d0403080c013946404100310145c0c4c1e0000740c5901d1540161070480c11058940340c54601c0411482c040703032070050b00b401c00140084c0c0c00401040241511070030340318000d66210030013043c1ea0040742c5095005400b840740c10608219100100e40100074250302c2d62070180e81c0c1c1c0e281400d5880459081107130070382c0440d0345213010180f07085250110700d040302c584a5a2900d21809411060081c0c031030b900800c000f0001824840c000d600c407001914910192055a1030300c8107403202c2a521851910340100c0c01d10401d0351002200090288041301d118000c0c00f84541086210401080521a11002017a112039420340c0324002075044214030641c0000851325150612014003024400c5015260b003500d803000030000b01d10f08c0c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 907681456 1250 907680206 907680209
    0xd09120f12050c040503060f1504020c03030a0f020405030601030c150e010c1709031504050111040501020604060209010e090a021e091005030a020f0f07050f0102030709030f0302160b0a1107050109 86
    0xa81c1c00140540b143c07400d880c0c00780030700e03000f081d018460031042c001c4078001c2801c2c00e4811400350046030486241d00d030a203c00d074054440443d0040e407050000c5042c18645400a9480412840d03005080650300c2d80064a411000e0740203644141600740180301080b03001c1c0203540442501d0034102c0d0030092143c0020070030410800c001c3c0110048a0002c3c0802c91b2040c12103d105200800b1149c900c2e9002541082201b8140c40c102d6103586420210181c076880d02041c0c0c0c08448058020303040070758aa46819010b0740c0080403e030f040100b00b00c00c41c0e280741d54140920340140b842d80c40c0142c82c2d010310303030398011340528080c0444c81d01c03081030040c840d2aa46400c648011085140341a945030303110f050703414010340501c0300c4c0000c1d01c1c04003240a4922000c0640540031b158002c07403c03580305085081106080b80b01c00c2e5410000160701c801e0034030100308115000d0814034440c4c81155108007454254a414080310740001954501c00103040b50410303800800d101c01a074102010300032041c07411002800a4965 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 907682706 1250 907681456 907681487
    0x12080615070204090512090a080105010b0901140d0c0804060c1707180e041a150f1023040f0501080105131107080f120711062a0d09120f 60
    0x10070760119115500104406a40300b4101d030002c00030030000c401da030740040f080207000d0101a8000619070b8414020181203500c4000e030b40d0f10381001e4034011a0340001d00780c207070503901c4e00c10004030b0141d108610520411415030313030f12a442c500b0249042030513074001105010411006210a09080c1c54001580360002d4840c104004102700013a000c40003818298440414015260200b00510140e101c1c0c6a0004c00d00070115807455a4001c4d141d58900304065105400c0350410f8421140742c00c101d800042c0c0d0001030b007440c603449544002002420202ca66103800e2604d00414100410700b20300c1c007100003505090a14240390740c1084049200303150071031080803e20703448487c2202050f107060b0455142c0303034200c89510b0340e4191030304070541d199100740a442c528008850028803814032403000e0b80e000201481c00b900540e195182c075900c1403012a40307030a407482c025002d00288100140010325807080208008034000d1100d04105d1a5590341c01820001d10002e10380c0491020350004a81020b0b144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 907683956 1250 907682706 907682749
    0x3080c070b0c090d0b16020f06070206060f060405040203040c0e06010e01140a1403040b01030302150114090402040204180605090c252402090307060e0a030803060d0803070c120806 79
    0x3d441c00003a0010100850144c60004080d080c070440403104000002d2003e419000c58000d220440141580d4000031280c140050b0480c2c1c021845074601010419040b040091040d42000d44031400101203074003d840843c0c032420f2458040000340403c02409501403003d08140c0094000400080c0c03211400b0151884041c0c1c0c00100400c4c6c0d0360080341012088801c0030083c0780c0380c0c0390034a0031440107036081c0002d602501c1801c52000240c401c080515051300c2032400843c410303401400c2400000c40f00540203d81c0b040e0248000b0400748140b8007040303190003c6440100c0c0080c6814180310007084054160781001c9410409104540102c00408005070191282d805c410881801c00c0c06400e203c0340307540d040d42841c040000360b191040d41c028104c007150440543d05a943c0d40d55050700d51107036001c6140e40010310307244c040000c54581400385520910240c0500c80030700075035aa22450f41d000315440408103560005d02014001c8210346680e098070b442c00c09030000c0c01c1c02c0c00010442c2da082080284403c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 907685206 1250 907683956 907683967
    0x403060207150204031209050906010f03090317090c04061409010e040c0519050f090105210715050406090b03061305040602070c03120e1f03020a051306030903080c070b0c 75
    0x2549419107082d03102082046444540f41e2420882d5080001081800200d0001c030220b5146002200d90b0300503070b41619000b090503042c000c1940542248201a0288019804880540240c60401d2480f507006c100290401c00c0543c0e0802084503850380054699001c1e40889a506407078010011b81036980301c0178007056590f554070b0600d25036085500650780000c0c510307060500400e040e4109c0e01c140c1e842110034440c22659042449610301d000d00c01c0c2d9512011007028924649001d9012103020060003064500c12a19489400c2e03640c0c814032654000640f00003803c00c0312980c0000c004001e4581c10750041c0ca1400e1800029003884081140040380565500c003180c1080456412290f065030f1103401d0601790355880c24140c01d46180300603040c01003074400308054418034040700101d140c0403800e030ba151020510200d084000b500300f0001041803020030040030385e42401d11000c0000408183d5008503d0303040510300104a000043d01c00b441e03a00c0144184000030f15545034141d4000340c00400c85482c0d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 907686456 1250 907685206 907685213
    0xc030301120f050d030504110d050c04051317180a080d12091b03022724151309091e0201030209100512060d031d06040b0d091106030c0403060207 64
    0x31261410042280c4640710009a4541d09074006c140b165001c0c0386010306280460040c0322a00f40010801005600480d600e2103007460070360302c41c42e04010303802c0914094011030782e03c5100d40c0700c2401c1d01030b40342040071440d807160003075001507007039122400e55464814910b4201c074144c0e207040020070740b0b0920000c0e0718607074010a6140d21101111ba004902a500c0030902040440b44103d140002e900403691540b50800c80713480e040032621480030903103020380507a80d402c2c2c4a11350382100307402c403805010346c18420039100d54507040e41c0068507041e000303603565441c2061600211580d15a024008080c1482400c801280e401080108445200308452043d01d105100480091040740c00c815400289507125000c11584000684041181da00459130540c440c00308218242c88a510001c00041040e260000c100d07088c5d00325220441170141009007000e882d686c407030107030b500985508000701e40c0c0c606125003030191180800341079220569402c1d01d5802c0030041c00140b8804c03800701030045c5d6000a0f80c6801c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 907687706 1250 907686456 907686473
    0x51b030f041413020f0702040203060a091b0206130209010905060d080d0608100213061214010e0402010f0c030905100905060703080f0a020406020d0e031006290c03030112 75
    0x1410031002056549460b0321030850000070b2071a00343e0181ca1206610441080345200701c50619041031401d0b41441a0f5500b08000b940c00208083c0d049804682e00280c20308160158220803842d00301c80008940c6c0d03412000380740c408001c06440500c41c40178880b001588526001a054410300b0a022955aa480020402c1d207442502c0041c000d10000403124280c048641c0414181c2d459031041ea2020000d16083d80b05900503c034031504801d595440c1080340300c0c050b100c0a6000c02098a02041070b0002581c030364007100f001d900011495001c4410041151783c044402182151581001c2c1c450b5121a20300034501c40c1c1da8001c590050300c0f10b211400d00e003401400840010326000341019524452803400426200302a294640003c902201003201a96180281c2e000d40e521940288050514824100c2c0c1e060300e441c50458240c021544003d140c0c4103107000f80b101804000203c42148246a09030703108a02150180001207041441405440040441264110344d5070007c00421800181468a803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 907688956 1250 907687706 907687717
    0x7050108060904030c0b0c041401080907092f0703090e0f1605040803030103140106050312182808060603072303070e07120c0801030231020a0201020325051b03 70
    0x40c00321100800c021407c943d00104243c49544000c414403452400040d50110401e40741c010203a00141024001c0020b00d90002d8a000381c0b404813140341c0c00d03041400044040c1062901d001c4c0c0c8100042040c10325400100040091001e02d006520900d00b2015500c5130700c8024080310030a28007441040e8009224401792405084090103136580c0f940d40740381400e8411202c00190345a9424501c0c005154a80440d007880603051260106140c4441d501a4140c0004400341c407903441241e00c066024038071146c1012003840301c40100c9081c0303800e003081041341c5824070041015100b80e1180900744101c049141488961060510a00b010048044c0001e070400480380c110318582202d0804020940c0e83c003c030b080e1580c01c040c080c1004068101d100844030000309010194106500b40b1742008a14200700803d400e669165145a800031224001c28043e0703070003552003d0042c0e4021080c003201070007070410040864040310302001008081075025019000e1300741c2d0507001c0c00d00b220031800a03003400d000311003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 907690206 1250 907688956 907688963
    0x61d13060c2001020c0d02030c0312060118060c0b2202040911041521030e22060602031e0901021c05070f42090201030207050607050c060907050108060904030c 70
    0x124450b034074a0000e4003c1d040005104090700c00c0c140d0500c4580d002004a038860805c51015518040101d0f07850202032102410302810801c0803140450182c40951007200641129a01c130a1181d0349070905401500000c2c02c2007202c0c3c1d40b10000d9400ca1101c0e2801c0140c800e505a4021a01e82c1c080d040000d06005075000446c0c0060408080010000300c00c0c056200b0f80e02d010f183d04040300743c08515110100f016150080200300046c3c00300001d072401030741c540508180f034600c200c07402c1d00341c04801040d19031580c80382c0050388c004111f500d03c2d80051585408240d80200c3c0603414a10720300d000030741d102400c0381d052500041000964258900c9101118106a01301010406001c450b02d002034031303062040d0340c60fa08401036854440e4407803400c0c041c0841c00341d030349030781804802c0040e0304c04401403d0a00040b41859802c02450780011000d110032031080180e52103680d100c0c844101c1c043d040210041c40380300160080b84013030000d40e0300290802d0f0401130070b4a5043c6269200c0c0303030941d054100801c001c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 907691456 1250 907690206 907690247
    0x16080f160c15022215120b030c0307090501050307081c08062403070f1e080a021308010501030507080a05070e0613020c010c1d0901031401110706061d13060c 69
    0xd05031081c084c44104101c10f4130303090350b0070391941c803c440740850b1550301c01080002d032507100d07061220200b600051180c400081c00d603514100710b00c00103450b0000c1c40e40b01640503515240100050315081c000e850041280b03e001c0d046c40180201500030309032a5154035000d120904021401a8035800000380560340c070b03644844441740307014200c40c032070360002c5171440b00060003280c0c4038a00c2c6209100310300341c0465050481c0311000b964031060b01c0024000308503484c265801d004030100ca050820222000340040e400001c0c044d4107504205041c02501d402c80b240c1c50f1b202211000000d80c0000701030342201d11038128511142c0301d820004040040d406402040d031400859043c4024806500c98003070312900b503c4036402180026030347c403040b00d110601e5603400251000100042103c6480d100c81c10038080000040e0030300341c8031800030321380c00c08001615a0b5665040901442d4071910b507000b09030b81c01c40d9511920f13140803c56081800c00c4448020402921900c0003100c07076004114807200c0303080d04141c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 907692706 1250 907691456 907691467
    0x114060f0d1815020324060306010f110a0c0e070c08030c160c081605030708070b0d060e010e19110a1d0a0603090209010e06150a09050916080f160c1502 67
    0x780f0010307401c240c401c1c2c0d0102c6850180302e035003400205000b2203401c4028001e50b04541d00c201c01556400c02c10308000b002d00545150000c06c1c7d00c01031110270f540c1d902c81c0405600150501e5136007492101d00804031818080c500f00c031200400c1300704040c5d80d8403a0142e8995a5241661a0255031800344204010301c00400340c20003041c0303c0300124190403101002c1080042c801c0d41c5004140d90340e00300380310342488c036042035105120640d0000010418000003080114016503a02c581c8117991800742e204144102c16a0144450f0b0888500c0c1c107001031010403800e00c00c529074060380c000103200c0e026a60041c00510f6143e14004000c001a888524900030150b607180382d0740c0c02c40500503201d541c03000c900c80d14403200045802e2504469803030207040080c0910a803000f1075901c40c10164001200c1c0030921000c840c0c00650760ba18440002d01c03e800c3c420394046000040c40b4082c0404401601901d840e030409020004003000c9070842080c07491aa02c1c1c608101e64160800400c80003c148501c404e0f140005903 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 907693956 1250 907692706 907692743
    0x240c01021b060a06060509040c090e040c15080702060606030a0e010f020c070b0304080909100f03050a0210020a0b0f150603090a0c1203050304110f04140114060f0d18 73
    0x100101218215042c0d4540b80c1c0c1e0001d540c000c0f03820310b0241d40c01051041c440d18400381030170752001401002e241895003400741c07a21704c18584114101c50442d1200a27207402400b40c8040c0d1078181d84200498201030a26083c6840083c2d1103082c010045800303070101000046140d01c0350303000088900c907048002c104906a20740446e010754808c01011a092141d400001000380c402e03030489200b0f41d0070146e030906021245041004000000c3c00e4a5151104144041180d1504100c060300a52003403000b0a1b0206291040c00709102c00000d0300c205640002012801007619800503590000c1c2c9080c80c441599582c50010008007010601107130800303004801c02411b6400010105c0840740650174580c29141c0e0384003403228050720040014000341c02440410001007003010301030f2484000038a0305180b011802c003c81c0844100c43c03800805855400010040b1100404141a1010041c1e44c03461410306641080c48291240d100c4803c0601da07240b4480070300040c07a001d19141780344d128001c181d68024011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 907695206 1250 907693956 907693987
    0x51e0304032c030d090e0f0403020f060f0f010918020d1401060611070902040b041403030d0f0902101d0d1e030c0b07030b1320132102240c0102 63
    0x10340740c004e200d20780058810764015404132081350b240ca80c0301c120665626030203085200c4050030460540c454100340c149942400e01030303d44030300e48030080000c8501d01005252160003040c3e10000c180c2d454840c0014054407900c0c102e1040b250160f49207541000c903890300703580d1345220b40110015546404000b2441543c40b10340c01032244031b21011140100c0c4c542e80000202d00c1a0b104251b20910200020003110200755001c3e1311b000001400d4038200034001d030660096030744103840088440c2d03980c03156100710300d40002c945000807060f00d0445442c1d00c56200d45a094031181c132a40d03200e65070703881c4407900700124000307500560305406069807103503059440d015200d0042500100d40590305c0400103200340d40b192003501c8151000900e00c007102d60444131000001c0c1034981b018400c07014000d02d200303c094078040081c0300000008203140c0425182140004000c000f0394240442e02d020030760031001503a80e50f407400d07000c01c0403449035042030005410410b03814454460948600d5002044074000a414507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 907696456 1250 907695206 907695287
    0xb030c0d0f181b23090603010c0903170712080a1a0a1403010f11090a090b030a03030207080c06040309061d060706020c031c0912020610030602031b040e04060c051e030403 75
    0x5c0d074410107a51a0481090300703842190381e070003001507607a1400300080b13941c1421807460514180510362505c0e00e60340325805003e059042e031070040341d030110038040c2c5200c10340703d017070402c807036401864030020078040010701d0a540610880380034500d80f08507d19156130130b61000c0064110003108000c200901c0c0003a40c0c01d0740003150040d100782c0100c100003030001c08074003400240c004e00401411001c0250307074044d8001d400ca040103030b42d00da0041c06030041d504d908012142c042e60203071b202c1414040ca8020b00901c0203519150301c24440310034900444054480e4000e85005952041c00561503014440700c991950040c0c1414001d24072400400165516140e8403002000d40184c0006080b804616003d90340c0c0d0304280da04803014482540200b0200350313140d020f950011075100442c0c1001820440c3c2c0300791900650813400181d00c1900501003006083d109100c2ca4905504100703041c0000d6801c508a81c40c010000c0205030900000040c0c2011312440e120b59000d03100d00c9082000038080c04c903003030102406 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 907697706 1250 907696456 907696459
    0x12070905040506151c03051b0a0309050a0f060504090209120607080a0f050103050615010e10050c0c0111071202010e120a03090b031005190b030c0d0f181b23 69
    0x2203503013480d0075080c0000a801c081e0b1080c980032440300d03145d5404a410342e03ca00780021251782a10410340785290203001c0c0380101030090740e521142d0303400c081c2003046898550b441620401c440081c100304150b040000c1d9822208040c03070058440060f900400d10210083e0448116401444100710000c5d401c044140e0041008040422034066500b0020381192001e0101520035840ba80c00100c07000700c403407203544803480c0616007003202d1107804e0701048018480c64568400b00f0000314010325032100c204000c10030791400340703004000401c2d40e04034a62582c10500840d600c40322413800103c29a4090088400d50a6000d0030240c1e0540035201d12a44070141d00000b01e0008001d003e00250b420710040589000e50b42e10f10240010601d800c0402a00d00c0300310082e001e201c040c10780002510b000201c0918840c03207003a04210f5440340503500032411a03481000428501e4035003c01c2c1070312002000240d89920741c0c003c010b06103007030a14040c105011941c3e480341044609817081da60200101c90101d0020703400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 907698956 1250 907697706 907697731
    0x1b2006071d0a0302060d0510080f010b011706090402010809010b100e120a0c05040e011d01020702090f070f0305131407090f050f0402040b0d0b090a020a061d12070905040506 76
    0x4841040100b00b02103480040c1d0f0041080c00001d4841d0f416034003417908a440e220018071100c1c0e9400c40a4180b01b000002c0300c20a0b50744501030a2196040003142d6000200ca044020705440c02c47c0001e114000701500c040e04020820b40010803500c1e003548112245080100941205242811700805100c00003407128020300c04408210401e2500060f001c00141d84034042011890510040c4001490207605d400780542d00c0c0d40d032189005003c240c0320141c124415001580d075440b02c0c0140520008080c6c1003a14081c8038008000015910038035003070040c28a40703008229034403103468000e004020701e040680380f040e0001c00c80400c0c0c1d4001602c442101c1c4150000c2c03200c00000d2441c0d00444030119405801342c10503030700090052400c5e41c0a807034080350080000c03081c078030151506042c4000440301c0400aa1002e60f009055180004602e03006003454503100203601d0200b00c1410803000c050521038050074840c0c03160350a10f0805e105d601c001d0400d24200b0082c03031a00c1e041059039080169070201032102c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 907700206 1250 907698956 907699007
    0xa051801060305072606060111010b04020f041d01030b070318080c0105040501050a0218040b041e0204030c1205150c0c0a08040509010f05060307080402011b12080a1b200607 76
    0x103071701a50092407141d28202800c9103607030300c2e00190380111a0311070a000955952444860b183c1e0b544c4040d00707006213032514080d01c56080003011400315044034410044802e01c0c50040000400c1d80c54100d50149043c94049114030062000445041208900038034036100410680f440a00540c0703c0c5110303a00820090040352180d8407120300300d1040580c00700c010780644d0b048800c542800d070000003041c0006403000590881d101c00340024442d241590084e0b042e0005000c009102401d400b020142c141243c0c01c01103102d0aa032403d6580c0c403601822036282000400143c085414401920000390400060710704203101441c1441c80780c4d00a02659109044280c0049001c60501781c1070402d50307001511b4645941c446900691344c80302c00400c202e041050700c10500e031010200b44085003015100c2d01c40d11220158001000d0407040000b44100041440d00c55000f010000614081011001c142405070f078a40c02100061080c500d030342c222180621491050111060303119200e1105040384680c10540038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 907701456 1250 907700206 907700249
    0x7050c1c0206030c0c2a040b09010e1003120201200c03030f1302040207030f031410060507050132010603090302100c110a1119030b0a05180106030507 66
    0x882000c240a502054900c001400605014008540000c0b585a4440c101002c4003489071915011071144016900001704080c28425206100a40b01c034088405000210f0040c01007650664148501034803c44924089026910b1014804000d1a00306414140e801500e2101901924502d500f220500b0040c89107610f4400e50709040e00c0812040c480a146161101c0d02c241d0a04040034200c2d15400501c02250401079990313100608215104e500d882694102680000d030482e01c0b10380801c0d0080164800700848c00891009540640350399081c402d0311105c05041c03c500400c0030000007030207c5070040a0000038410a42080d10910b000d8070078807060b0b80c0f0351b2002c909444a02c5801030244e8040c0d04108100e40080d0080380000407186484184680514055850300340c1d00032040d01c5103a810100580603082a5181c00c00c0b92048107440e1140320b280d80e41700e2211070002018112000e59900c01b0591030740e114440e000d21416010024850981c407414890b403941c2d494883d21410380c80407080081403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 907702706 1250 907701456 907701469
    0x4150e0f2d060f070b090f03031006031d07091112040f020a080307050a0320060a0e060a0209060304061508070e1501111504020a090e060615040807061803060606030207050c 76
    0x4841803500e0442c103090b1160b5801003145c174040c02040050007019030300401064104099445a601d04000300e48540c9011f40240486125003581e5050041b40340c9075454204002586904a504070440024091102d042240003401004481d507021840002848140030942801d01c041f14001c4984a4840c0e07a100620b42d40c904c1220740061a58000302c0d00c500110f4003841040030302001100c484d03d001184410f41c542885012901d4025440d80e03040d038075024500402c4045d0340916002c0d02145010011360000b0040c0c00020001003429444042d9042c124040503002d030020140c1030125800c164641c0080c01041004130340c5150707603d250360744507030042d8030411402000040e040c0140c00030032000c1d0000d4606800040042e03030015180f200001d028041489040d050302c0c0510003410366820100d040003d8501801200138601d14103200030f00c00014085000400c4644074140380103a10484421000d461003c0e0b40007130b110600c0c0400000b02d054154004101740c5120340291000c610303428040004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 907703956 1250 907702706 907702717
    0x8040801060e07081803190f020705030c0607170904060e041106071e0f0212162310262e0504091506270204150e0f2d06 53
    0x140d00b04003180c40c2d80390b0100c1e442d050b22a4041903c1c17602c2c41ea000c03034031004e201c7c0e429048001104800c01c98403a40d410b12000c1c010300000c4029040c4812902d0025145009002c0c000d07002c8441e820742901c000300b0000c1160080301000d4424445241d1318011201520021035068840031000201c09a0a260500440e44441d500c6202d0380c2038101c02c1840040b1015a010084800168003201000565944514140300246020050080300e00707001a80c00791020070f600041c1800c6020010034010750b8405000c01c0c1c1c4000548000d013031842c15181c100d500381c01000e00310104c1c10b000198620030307640c1090210303c1008030a07030380d00d0228080903002c1d1400c11001402e0010307a04c840000d00051400d5040803644030b010307003816a011418130b445c13001101c05d0f6a00c0504a901010000c160132142224811240500c111085003054a020148107082c0300e100c51400402c41a40a01405036070b80ca031861740d541c0001ba001e114400918160030012542060900c0780002444210800c10724000040302c0c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 907705206 1250 907703956 907703971
    0x604120801060504060e18161b02061b07031218140a030312060506031515030103111908061f12030c11041e02030a060608040f0210180308040801060e 66
    0x4e19152402c00201c0d0160706031600d01e580032410342501c65442c0349400d491801100500d078a02c5030020100d0b006003086203044090404407008040f40c0c0b001d43d0b943e5003030750580c04c55245a0201d082286c540ca03824111107800042003130241281c42000079911110480d52801001d10b03c042da1521501c07800c0c0c0c540f203500b80382c4e40e00000c021001e2001900c20f1f80c02c1d40180044e408081a425121000550b47c0c3d0401c94029191075032074603610000307142851144074040000c0d580345166505603100e100001424a40382400703818103203c0514240c45c03148461006061036000e03a01d10b403c00503801e0307940b041858a0410300380184132001c0303003101c12070540818203945515004080d159641e01c003803503202201440b0b50f1003551041a90081d20342e120441500c0012440010f9680c034000d2840000c82d11541c01240800201404010010b02c1000796050029011290380b111506056021940c803002c1c1d4003290b0084041e560004100701b03180001c3c2c815280304c10002c1c4802903d400c0541c200c441c0031038607103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 907706456 1250 907705206 907705217
    0x3171c0b090f090a12030b03030a0224090604060e0309060d090308090106080706030e010b0a0f09060e0115031a042c060c1603020a0c03030c14071401050901020a050f060412080106 79
    0x100000c0c01000380c00102480d541404200901d0385e000190840c0c2101c2b40034400340e00418100031050f16150000d10f01c9200035400c0300300a042800801d80d48140003400180851f0780c03501120071800d000c100ba180f0030f04004040903510421740c0754079005404050f100b1400709004401040a00d40103015540549a240c1c004100851800100710701410001e040f100c100c0d580d0321010b5684d45c984400a02c003400c24060524007061510b000c50007140e905600c00d80c01c42440500521100d007036072190340e10303c440b28600810201a1100450402000084600d42c40f51609002036962046c0e031507110481d400090100443d40c45800c4215183c4008490340040e0328020480000c0814080c4041c214540c02441111240003040d540c880c60703044030f5003095020803a00303a40681000341909036120302000d070300040c0c01b403140b400c081890306034011030400303060180c0450320364400e034820010100c1081e00101217602102143c1001601c50303400350b83c180c035690945a4400fa0f03480c010940c0a0490780580d840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 907707706 1250 907706456 907706473
    0x1120c05030a0b0f09010e01080d0c0323190225080a0206070f1a01050a05040209030619020d0609090b061509010305041103010203040c080d030b060403171c0b090f09 73
    0x820042403c600901d40c0001c10ba02e29006540302e0540c01400380900c0c035200309065040c001154580650000b890301042003401000c00041ea110309500b5915081c24100d0030407440036100350441c1c0c0204918030903401241c000803404151f000401d00b00c00030704075449400c20518410000c2c021403003400380c650903501c621081c0c2e006040500c000d050036402914801812003065403000032800d00d010548040800140050003640743ca000020000d010482e0114a024411400310b40c944100030f045a24201c05260360303090601042d0101c90141400c80f1040201e5611910f60100400074940c05031400d055404c001225400c01000c0640d40100c07025005040006240044014050040c4100d0303903246614110312050f01d090000d14010741c4941201028103003031964040c540005040c14504260401d60009c0d0b150f11080115400d40f034210344141c030101c402004441c01f0380302d8201c0010b902c80302c4403808150128039911610b001d010448120314030761100345030821284429240c10305180c001444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 907708956 1250 907707706 907707721
    0x714040b09270106031b03140f040c09090501060e10030b0a020d021b0616090b040b070804030218150612060d05070506040f090e03070804152a0201120c0503 69
    0xc4500c000e9503054030b04901400d040700e50011142003130744501c02090301d0304030f080300800201e507091043c95800c0c9170030440100d12819212500340e02030004400b4400010202d03080c400c0c01140300c405081c1c0354070300744000d4034189001c90003401d0310310601d1425010000403a44604000443e8400c0720341103200800305864140440000390701c00b6400c0c00c0d00c141c0c01c10201290158880344100d2848017507001e01420b240c0015051488081c861090082203a00002480031b8104e00c000e8406480548600540710780007864500142d00c910b400103540b0424266410802c5540c0ea00340620440540452051008001051100d90700903222151002c1600070005180f505080359182030300c03801031003102d94455440000c03900c1a030094101e6003110720800c409100d40c10ba2130007140314480b0090001d524181054444003004d0140b40034019464112a054090280c0b1a81e14500d4103104a403d00350b48081420300841c1310720707400d4001c030b0200e10310385112139182c0340d00e1080c200440150388506145a03141c44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 907710206 1250 907708956 907708969
    0x80c090105060f0909010306230f070c020117010806070909110306010e0d0609060b0307120f0b04080c010c022113033e030c190303080615070b0714040b09 68
    0x280c0ca1107042052113071841c60307524200c00500031030062a000a03054651186002d0790050a14502030301c0741c420b42400b11698040c5011036100b4044d28119001040a00c01221111000c58400484560301000820000000f20742580105059242c0100d155621031032a01510601c1c10410b030421307001d00010307080c1d5010349402c0c2860030004001c4075007885139585200845482c83e8003030321881c0e80c415148815080410558015040ba031155a0030318030580c0c0c481c1040e4101050040c01c94680002250030410910107840040500100034011070003408002036440554904004440a0118007070500b0700f040811180140d174400701c2c0b050910301b9034031154034410ba031206140b80c01603a6841040404000c0407464805400f45401c2103442900400305460049031000980c07082d0304084420040e8990340790254101c941c5801c04240a54802000611030110f0b140e401e640d540e00050485c0810183c002054420015034441e820381c2040d1010140c803900032801102c0740040100200031240c82c040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 907711456 1250 907710206 907710217
    0x50306010c140a0b01090605060d0b01090e040f051c2f0a0809040b0f0d030309020109050603090307030908061506070507030c0b041401030203070c06050712050718080c09010506 78
    0x41c10440d512040d00c0c0c0e610302442c8480541c008180d00404000010820b1442c009401814491310901070a8100f9001440178030954112100103903403075805042c03c1e40900d01000040c54101e01142c1c96282608002c0e0442050045c21103843c02802c0140201c0340204050300f203e0003140d510310211100b45598994615101c007a900b07540d0a00c03090110000b441005000328080c410050340b17850303281e58010710003501c03085852140302c0c002d10031001c405512106400580c0b00d4140c83d01041c80c50700f03400103807100c0265800c401d4201d00004200440c9240001c01850403911907990b0715034580d911400103464440699000080e4490b032000f10f4a145007003809800b1060045040e10049170b541e07614071500322120392080c10307144c10201303080091500010001d504124203090562039032030402001400124a01c0e070040009a0715000702e42d803a0320400b8840d403440300044c0c0404c0750f0300b031101e00907040828000c10f40d8600f041d00345010803035850115103001d0007040074140e5049a400c1a0030081c2d00d8000e13 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 907712706 1250 907711456 907711459
    0x30d110313080c0f1603060b041a15070605070c0326010b070512040609170102121b070b07050c1902060a0305060d05011a0a0506070f0204240e09150c0a050306 70
    0x24201c2c81141c81c5014403400500d60711030121784900360b10313614041080c0c80480c0030b1148600c0c0340081000c50805041524844004101c1e51000d240c0501d4a07a0402801140c5010b402035140c0804c109645812034031442030b5900a480c2c1081218410a9070500e8210402120340b00d0608331004020300c0c00780d00c015003850340c8100280d552810000100d107116030800c1d803000b40064884070302046200d0711030319591b4180c00814001e51030500f5048640c48000030241a401d180d8012040102c54241c06c9000d8070b80a41d44120240075600702210024082d40090060341d0385401070090204c448018005030010455000c0c02250a00c802d4032006d40080070000d001680204041d004d00c0d0020303c00b880749241414a003081400190000401e00400e45100e0b00142c3c00b0300000c0010001040942c2e564408441d411100810a81d140040c00742d141e03044c0f00240c07200c501c04c94001081c40c0340e0b4520400e1240c132b4100111480820b03824100c6d50741440a031044562072001304401c16580e4031400045510500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 907713956 1250 907712706 907712713
    0x7031209050c3703021002060114060a210603061d0a0b1005060703090e06010309020d1b0b0d0501090e010c0f08150607060e010b061e0d110705030d110313080c 70
    0x405240140c803106200f0351804000f0070005040c0114641510709113000602c52004200d42c0d81814015400b800100b11042c3c41444045900e4880c903204040d680f03000d9030440200303c400340340d8004070005040303240012150182000c45642040000c920194032141700c0d0b20082c19900c400e9280c141c1041005000e825601203641e00214203070312988000d2407858403d03074545002d80c5ca400324100110001400d407a042500301350b070003400340e070302c10211500c8250000413801c054404244c5030002c07003803d0f038002c2800d03a1022a80100900142d84080d04840300004140b100d0380c0050b1450f4220b036540c022800c04a9084440713000031a12801489512043c40700641c100b081007140000c0e600d4201240458210b40c5070b04052203032404c20300506d20084c10541e46d5500348030182c62644c0d00c4c076600c1160000700c5180800d041c280c10805800c510120840261220f86d100c041d420b180351260300104002c88010700b0160302194940c801c40c110f07031250080c840102c1a200382d0740d44040075076220307810b011550310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 907715206 1250 907713956 907714009
    0x170f041e0801142203080f0702100e030706050603060421090302030a0c080f060702030a11030712020c0901121e03110106080c0a08060f071b12030207031209050c 71
    0x70801d1003a000075001c0420070441c0c51410083c04482c40404140c04440000d100070b001e40007a80110807036410206044034000c00c0d41c0da018080b8540701c40c1c22049400c01c4d00300140e81d40a0703800030004040503809241d041c41540e4843e0107040c2e80e120b050390024105440459854080500b02c254a02c1041d001e2800a280760b9507900000d24040c00032009407206840c6030010401c01108010a00316485c4180162196203071004000c4e489014001031401806004078140410082c1031080b00c003d0f5a101142810140c042c48001b541c44005400341401448904008100000109410210181e022420042840100b2200314401d044040118180100350800494000080c090340002d880358000404001c014002002181c1420f42e00501d01c0b60001000e101e50903041c00c202641c07089860400010240102051440f00c45210b54060b00c003211070540001c1311603258000f0b10440d4001d644850740c1d1000000b07440210349868400504a81c0212101c41c09406c0c0700c080b40007001c6a0b40601c68406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 907716456 1250 907715206 907715219
    0x160501050f180a0b041509080c1c02032809320103020a023003010b0d05060a0806161e03020301210b1b0d020a0c170f041e 54
    0x64205071000001c090208042010b000c07224030380458410b2810b030080040315a142c41d10440c01e40081c0002c0c03d1103120610a01c01d40c10240c102d81407941d440707003005640d041a10b40c0c0030389849089110f820034400000800b4074484c40001a24040500c00340713800c550503103512038024019280070751001400241d5400241d04002d000340d00f40e0311a003031068640464404601c8201140400154a050510500024000c2940020a400c0080d03000030907403850078112031111180c0c000c001e0443c80350f41c0000008038500c080c0002400c511540b03158140000d84070304003000900b490328041d04070140e102d800095201c04000880286203c61030503c1c0c02500310114600400102ca842d241011031380000042003109200004200c03012405d80e0000c0c0d28002c0340c4e4901461401c013400b5850010350901d00f0464180e00d00c0111034038120304c0031085694810304200501603043da440d0544424000e60301c6806880324180440c0c1d54494840d400b10302e044d0918550403007284c0740a4041254480c000008101c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 907717706 1250 907716456 907716461
    0x31801060515130f060e0f030a050609030c010e19110f0303160201020c04111911030403030903050d02150606070c0b040306061a0405010509040b37170a030302160501 73
    0x55400150b03140c032018018035498080c4c1c1d22001c1c40c0115071004102d0943c0c006d85040507240211030309007003004132400282ca41000960302a010f4003c0d1014040034080c00001840c40c0000040213000240c0030881c0d0640318421034410b007030f820f0140744041c000113244003503500446500a180d00c117901e043d0408286190002030401c000d4601c0f8002103015503804000d0300392186000c81e024001104050007501403409880107064a42404188001d1307001d00030002082ca540c84030088a8403295607042c02170a01d2240d105c252054010780300a400300030f201151491044600440039030441c2c83d040c0510845600070036090b601210001c4002c01c020b81410300500045004d004040b5032f0500f4800b0158002080c100c2c1c07460951400c0108001c9640c1100c151020f004080703c0015880c02c6910200d6010751650345035051810141c080e1140f000d640b516008140541c801801541e40d8544402d025170103484240040c0c658400400301e0000782c401c3d0010a101c800b40c900c00b100c0d40e507483d03441509 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 907718956 1250 907717706 907717729
    0xe0402310b030a1208100506090f040c0c08030c03010e010806270c0301090809040c0912020f0f03010e011a030703030918060e09030d0b01030902060a121d150106140318010605 77
    0x100c0007420b100e20706d14120b0440000c1e0100300c401a243c0107000700099464007140c40001c1c0541d40704c44094102c01c0c0506400310000c4c1d0824510350b501e01d0890000c4001d0380c024042c007140746e05140c001140d000b5001441e02e21a00809281901c80788038618941d0012000614846143c41582a0622151402e004440580d03100750700302c80d01c0708c2082c0704100540b24041e04038010051244c40401030741c3d2180d50f500148980513203001e803403440c0c1500032070110701c0c0080303202c1d426600f8a0410420b4440541c40319940820001d81c042581ca83c3e1001c254498819100c0030780020492001484441840c804845c049900d03403500081a9170788080c1807821701720803a121801a00040790030140221517000f540026882482e041104a01c50344c0001c0c094094001c4c40810400380340d031580412009075025a080c9a0620381e0a00f030701d0305010b02315595002d101c8401000300441c4000042c85402082d001030410007001c040307411a950082026084043c103404005150740344c020018003030316500381c3d814 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 907720206 1250 907718956 907718993
    0x2809140d0e03060c0307021f0207060c080a0b0a0f03062c0f060903130611070504060902071118130813030804090c09050a0b0f130e0402310b030a 64
    0x45620401400b05420214000c148070940b01e4104100101994041a150354614542024004520746060310740c0c02400354100040c02285003110351012981c00c2540207220790100340d01885610f01d0401401202a00383c0300700c6008103102502400096243d40060300810501c40070b4034080d42503c50703510390420550080040c3d6410403040b6880c0010300380000c5078010050f4008520b081915814013840001c81c1c810001003241062a0781034035a404e10510740284001071040c4102a100c0840070021b50000f40304445061403156132301c01c0307401d01d074140808107084490075003a690b41d40100781041da010814100d60350803040200445115105040b40090f6014044058603141807256260860340c01d40b04d0503062200d000c0781084141d44040885040d156550001c540764640e03086881000d005481c112505200000c0d004181c560b410108107100c0d6000312404010120503203e0002200f0890004a240380d40320000c082203042150001315011801908030b4250a00c2c1d070306c41180c04c004581c5141d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 907721456 1250 907720206 907720217
    0x102160825020604051c0c0e09010b0a03020906010c151404300f1103030c0c0d1e03051305030d0905011d0303010e040602040e16082809140d 62
    0x680030501da209141200025522160449000e640004505010303e02c60548a42c2c0e85249151b586181092aa1201c981c009440d81c40a078560502d400300540c211030b10f001c41e40c41e040407402d42c2e241032070030441140e401405c0c4100980316200112000d080e0030400b039a1020b101400f500c990000d5200c0d5034444a01001244c0090078285003042814441100d2a201102200740d02210500380e0345445c1c1406070b40341072a000c0c181e0b244078203480010220401c440c460201008200050306030300011300031014020103540b0240d012540c1680c520400e1442c2404e9440074030394041449000381e01080c0c1041ca011a00c601410300342d40d407149158020181c40503a5a20f408404e02080800d000300c5000000d43c40661074104c5400100981e280014802c903094403220130003180a0043e16411039000d07214200381d40e22189044040241c008033072810550000d02c0d401c0010700c40313200b41d0002d09080242e80010f650031111b980710840240a001030142d50710310b09001024005903040200445208841d01d03078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 907722706 1250 907721456 907721467
    0xd0e0307031e170f040512040915051005040e040f120203090103060905070e090a14091f021602061b0d030b03010b090f160216030819020a200301021608 67
    0x820801046807040c481484404012a09203c10242d050350780300b1200c0e54400c03059569810a50315200304130b004402c0b1140f000034003240d111545c0c0c2001c41030030826039050000582e16014003c81c0350902d0590f0340028014032050022007050895503400c18002c45240340080c0c81c0c0c3e181c11410021005c481030243e400041d0961031940c16000b080700030b107002081084180f8181c800501004e08180b84248201e40035400540740b40b80a601242040c0d9506520f5034161400c80102030380c500015540b900b000c02100c281c0301203143c0c140205d0325410141884440c800c10103509010482e001031201c0349038050300e00c408250f0b00200704614440c034035240e540030031324502640501d801c4500e03409916010307005d503c1c1004111400c019129801c0b06000001c0d40041611410880c148440786402080c0c83c48403c900205200b0400080d080c45004503020401400d84801d080c1c0c5e0300c2c8200040180202c00300608902da10042c1c120903003c03a82d0280001d8a0a0443c50680b0000400c020046400e600c001c0345 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 907723956 1250 907722706 907722737
    0xd030c0c030b010f1701090c1a0c030406030504030219031e12050c0d060e0f060d0c080715121418030d0f021e1e0304020d15050601020c0d0b010b0d0e030703 69
    0x890304217011017035000704004d402070b480b11114100c06018040100200036449130070241c4a01c115201030b42e0041c1a44c0d1115147d540c01006080700b500c090b40140708804664004684c0c0c880d071000501d41c90340f180ba91501103112003009915070070546000380408d41e020040b01140502a1a1142c2001340c80240d56010030a03070442112402c0d0010403e81640504001500c90f600c5160794000e0000c445a101d12031591504503039480701c0e504105030a0090f202c0004a66201c00f800c002d8160042d218004a034112005460407968000542c0900000c402d002c00c3d0f80442003030340e44c041954003000f500d00d80540782c012003007540c0151038664061a8000b0350f110500c8810703582c0d040d82c800d001c4d20b401d00c1c0c0b840d045400242c4c0e5403031080c426024500000440d04646e1180545014a0743c0040f21603c8200203245d40001407000701d840f20b0160080b00c04101580c98084c0d4040030080c0c0c007400407002642818101003a5400140810301529610300303400c01107040805c00340c0300c8035100360340300c60090302c0d220b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 907725206 1250 907723956 907723979
    0xb0405012a0f12050f090906150d151a031501090503010608060912090a0312030f091a060913030302030402180c13060801120816080d0b0a050306060d030c0c030b010f 73
    0x4003800100b20013400945c03c000c0348041180e00070390044841c408551254000155180b07829008c0c0030000a000500c002818031a402024014241d101c100c662950b89138014011240c0c20305107541ea401041000944800800308042003190046c0341008000b40c844000c80d003110b11540010780c075684032208101c200d5604120300c0680d541180b101e58107110b080004604890840e00000301030071001380c4039114a03031090b802150820035501c42400a090b0702c0c1080004c95004188a141d00781c900030000f49182010000c1c00d01509042c500c4d01c01e2200e19440c2240290400340049134009459581d2103900010007000780d0081035070300c07036281d03440000100c1c2c4a030440b160b80c011000d0010550040007000d08100104034069040600315580e1805880005040174501c0b00c010034401e004100101c0c4079501758400044600169100c002003622001017598940c1c0413a0401d9001d03e001305080006485201c1c44421180300c2e040348004c064881c1e03900070b4141c809802120540200c007104015894000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 907726456 1250 907725206 907725233
    0x70606051e0310230c0c1002180114041a04030b091f0509030f0a030e06090d11070317280201020702280b090f03070315060608010b0405012a0f 63
    0x48010002203d400030f03082c11080001d0040c51881c50307180001141004a5401c0300d0500070079505a0340c180401f05c03007006c0207412202e00303401601d8283d0360801c2c140d401100c87e04024900011024141490591020303805034a402185507550707014400080000c142041c0e50740900045000381c00c142d00081e8814650b204100086040107080205121035041c021044460003030480000e0350380c40c0e5203070714242c019085034200012148628005c00c440710401040844107440c0d99034401d0011b40b40b0304001c0341c0d50001400098280180c52041100c200c10380c000828a031b1061088180d00c803400120f0152039800740780c100a0250350000740c40380441c80d10403030300500f84d5a202806c40c6004280c80c10900c000c6098010701200703a00001d80d4460790b81d0b86140304800008002c0072201459103038904145507468110208801d1410308401160350b5000e0b10010b4181c0d00342904080c181031901d4011030307244030a101038074503000760445e001d800062045a4601d40700e004014250340c100081c80c1800d921440d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 907727706 1250 907726456 907726483
    0x60906150304061505030616020f0d020319030b0307060324030506060f041e090b0a061a16021c03080106030218090603070f080d0f0c020d0305070606051e03 69
    0x80411810500c0444015241c01c90340003074000070743e0311185a80920640c0c19805c0b2070341c940b14800421003500000d6034654003c615030b42c01c0e5107601440c411410307500c90308012840d0140c1c005002d503015141c1c041c504058031121514010800d0030550340401c0c1400882d80000000070b4030b5905854a242c6000040d0000c070b10409500b03518513156448a03915408013908491150701c04800038641c0780c0d11504a0508408e01415000c2400d5104a11400401c18150100c0b00c06072000d000131036103c10383c80b606045420540101c150f0203a40380b5031880a501100d500c0c0302c0582c4403117030003016844410000203059100c035800171f00701e0300509019081c480140c1c030000030180100405a200c0304500c489006011050f20003e00d140c0b01c1900190030107901d9044941d50f401000c0740011140c000244901003804140c03920110746604c0d40b0200c40030701c0703000c02c065001110200f0210000384142c00074616103020b1f107400070704992528001440c00c021003550030300e50946c051541c6a146014089191102217 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 907728956 1250 907727706 907727719
    0x5060301030c09093e420d02070b0a0c0509130f15061409010504030b0910090b010f170c0103093915081609030206040e060906 56
    0x51075032450b4082006004446a03243c880301d11000700251641408074100505400d001c444454000c03400100d0308494654a2182e858840340c011420960348941c008070440068070415040941c0c80b64541d0020401d940010030010000080d0310302020240500f200480320140c0d5070001c2e414000060030000d00081f501d140b81c50b1001440d260072030211822003800f680c80e04500c982c1c400e0084000c0001c003e020103454282203e011106075481d40003030558846480301544c95030740e80340e01415409288022404036038100414400300761348140c00e55000200b10201c6130710702d081c09241d00a45020230411625400a40018046070340d00c40a040302400000841ca03541480001c035440d501c08a00300030f141070598030010b007403e01c10b91701400c01c5105a0b40e1062070324070741c84015542c40b08412040c039140c10f5600c500d01146e01307e60100740200c1040f25a0343c0d540141c58800459150000b035045200074007407505000401601d641020304001c001000100300c89181180600c0032842d0014103207480b500303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 907730206 1250 907728956 907728959
    0x40e030306010e1225090c1b0b0640091a07050f03010803030115050a0507120905030706020102041a0412081305040207211107050906041506020303090705060301 71
    0x903800500f520b419442126101c2035260300322200e078105046810a9020310000801ca04a80700304001c900040b00d950710000c100300300020348112060400340700d15240100d60310580c3c0b40030510151400da001540201241e000f4039040d03103007101a1020804594000048102e054402c425401c8040886100e060061044104542e0b410500b80440800c40c48901416000714001c2c52040e07058030348050707501418580d80d503161004207590750404d1240d9100805509050101c40d0b2150b01a154160010b4503113504040c12070352102c10454542a15030108410303218002013550303040011600802d515000180d403542040301889819000e601d00e0070a0304400c220400182454501c24040150040b10440d1622140100312944032200d5004980c400c0c00070400c4818812500a44000484941c0500f2444905201d00fa40c42e49000441c0c000190000d40c0d042015003401c1108079403103140100000b902010140c0c0020150080d0341040e40180d10110800c00441c104000550290108403611801c56 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 907731456 1250 907730206 907730209
    0xc050f01020a03050d060e010609080f0a1106030a11160b150102031c020d0c0e01020d1809110d020a090501021203040c090216050a080a090504230c0d0c0e040e030306 73
    0x42c141c4200040410600081000c0d522815521450150044a05404945d41c0d80c40d0f00420340350050286054601036442e94088020000844070105544200905840824001040701c070350030081884c0d48141d102c003466140400018010241c0c01e6185c407500c03c60003030608011080c0000108882c20000c2d00c0c0340185620b81e000400e8982001d806d125a102d009102c0b00043c010b406801304107245c95050000c42050190800748481e2090400c2c3e0880715001000d242c100c5000380d160b0015038a0804030307141440b004145809c000c01251211801d1880e04030498034a03022640400b40150001e0480c10b8180810f40e8184203520a14200b00c50642c04c60134240c0f29806100c0390b0340304118146e0740c00910324412000803042007801c1a0090180d8082c48281e0404c0d1903d94000340d00c00f000110034490100b642e00d054412009005c0300500907120041240d0500543c8800242003400481010b201207518840035004120b04080c19540c0c410445c160401440300380c035020149008a41c005001f0401107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 907732706 1250 907731456 907731463
    0x30a060e12040825080604050604120806011e090f0f050315071706010c080d05070e0130020415030e010b100f210f1a030a02090103082104030c0c050f0102 68
    0x70a07104400130036080401c0320026901030032552000b1024000c400c1000140710f00400c00030300c16070240800b1480d04400d10000c0360900c2044a8550100b1022060541c5044601d41040412111070501c4004e441c3c070f40d8aa140c0210040e8003580410080c4c100500079820240101c0d02c9800424011034180e0500b15805004445041c91a80b40e8001c0140021740f2603219584804031b043e00080f01d0382d502e441142c3e411002e800c00301e4640c00440c0000490030b000794440d15100e2241d080c00000f6241c40104002c100922102c255102031205030244070204d145500d00350700049030701403501d00187c250356a030a02800e4450301d441182c8a41e0f03078030011240d83e03a0061004c59100440f464003030a6500e41c0c8801c0b41c100340da0840c0b00000c6074984240c408451540b58030003100040c0008455105810044c02c045d43c0f41008031340250080d04070401000010070f50406460560303a1040d070882038109041141d41039000c07c079030680000d501d09181209000241d82040081d207400c0d9100812907004800103543d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 907733812 1106 907732706 907732723
    0x9061c0509010c08010b070b0c0403061d100207170a020f0f01061701060605190311072f101409040908030f15010212090f030a060e120408 61
    0x30018010150181200c0d1b5510185280c00a5561031070940030020703004041d1410180700100c00154070f40100700146031350080d00c01d282c0d840c0800d02880e110000c03d811041920400c11080850f14078110b0100d01e10a000d26141d0714200308000b00c1c503003a060b495421240c0a080706102d41c020701900800c0890780c030303031403009031920709203041c43e08a4040344603080c003241d01002142c1d0200800d84074100c000d10f26080006600e03c0c0418180d51302c0d84031000440f44440940c1d14203041d611641c81c80d403080f642c551130080b50072288002081021891220300070a0001c0070100b0b40d0302c51003100846404c1000604103201200640c5002480340c1c00c00c0e40d0055545521500140c5070540104642c1e0112030140d0042c04101038240b030450440c2e10100600b0380007035100c584040e0a45040080401386482100005040b4103051252810001c00d07040740011440204400c1041200000e034014 = true := by decide +kernel

theorem cover : BRFrame.Cov 907553956 907733812 := by
  have h0 := BRFrame.cov_init 907553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 907553956 ≤ n) (h2 : n < 907733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
