-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5178
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:00:19.662468+00:00
-- url     : https://prove2.me/submissions/4e5934bb-4d1b-49d2-998a-40752be9929a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 931115107 ≤ n < 931294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 931116357 1250 931115107 931115113
    0x7051201050906120a12181a0306060f04030c06091a030f190c090f0b0703120b030109021503180705130e070e0f0702070e01270e120706050a0501080a02090702 70
    0x300c4107128a10b4110405d2082d120001c00d020494031050f03020408007054450400c040c1c94281c03170400380c1503e525401c64444400c10010020894590703a01080b1881e911165880c151125104c0c14414040b242610a501c08644111070005500f0b1400c1d81030740441c80707e010000d00f950360742404903030408001058500e1098008000f898000030312301c01d00008006a5031410041c6090144a0402c4ac5040c1c100e1110b00d041440000002079000709043e201000c54034002c81c0d11007072000420301611041d84002d500809031844c0b0300154407104007a51045449640c500700c3d1043c1c8004840e03c4514601503a41c05c4550b002c50b480700c49002e82c00508042d1400402c55540c01d0362041c0d8000861004d95034044c00b41101402d001402d80c0c104001c0d00940496000341c5400d5140000c02c01422600f20580d20008090a1600a0314603480d8040421860810240c60507110310340c5800d1495400346c0b10440d02c852501d0301203100080f883c40b44a050300e540d8001024540700300e03004c00c03486c1c11004200f00d04601c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 931117607 1250 931116357 931116379
    0xd1d0f1e0a2313020c0c1c050703120e040b0102031e070b090705090c04060c14010e0706080621060105010818010c02013603050a0e060309030d0507051201050906 71
    0x82c1103040701a40031010300400c040c40e840c60200304041802004002000310340140204081d5400220306001a4070007102c00d4000b05800c01845035294078541006480e074040e0007000002d01588901160505000380d96209020704408100070850b580000380c24016401070145414036505e18009440f4039000c0103a0a04040c940d6a40945004040341c640310540c10503101045142840d10311150070100900c6480d0a00d0300b402d50041040500040c007821440c1501105d080e03281c0d0030340c0100c05101000065481c1503844180151803040180c4402d07001781d0518600450094007000641c000810f41000ba00340c1d03910b441c0046400c03034405805021407006606c500400d20409210383c0c100d401c0180c00204021150000303149901101a0413803000c00443c0c03038541029050800d261404650504099032a0022880c08555850080a140390030040000610200b4880000a00043c5000c210184800e5507200003c446500070a02c00c0d00d004044200140024544900000e030301c0130002c1e040b64041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 931118857 1250 931117607 931117619
    0x1f080a1404050601031b1a04030506070c05031e0909070e0108070f0512060109080d0810050f0d061a0406060e102a02011e0c05060f01050f04021b0d1d0f1e0a 69
    0x10b04036114113441a1f0800642041040b0041c000684d00000304d0412040d240a2529015128480c00c0042c0403e500d1010201100040080540f4034441001c5d02c2070380e503450100c1000c1c0c0b549501032011408030303c03140d0005004a1243c5c41101d88044203980d0740c1c3c2800506004071948200180606043c050b4420780030400c1d0310200b00c02400c4480c6070380d452180b0708000320004c1042c072403904461301481e4400000f02440d100c00e00402d003003d0b481413001862070f208003c00f0400818003442607030b1250802000082071640508002100841281c5030380003205041e83c2030303c07600300c8600e4120a40240c0408400c15004170fa0441087e54010b040c00d900280a50381920100305001c40348501180c0c0d00d0f450407041c0001044151350007010713201d103201c90794100400a8003408120300124807498000405070750f041c03543c3c591b6642081000088440004041c4009000328621401034035002c1c0101381c1d80c00551030b010310031450b00301004d4035441c0d546605844071030000710000a40c540100a0150010310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 931120107 1250 931118857 931118879
    0x40506150f0a0801080102040303050703051815090f030106080727021303140105040503030a020c07050d0b18120304060207051e0c01030f1a06091f080a1404050601031b 74
    0x24410390304034442ea14002c280020b00b4030300e8180c0004030071340c0c4140410300c0000d4201c1d084510703098040c02e00310b4a846a02c4144829892002d032100d0708403910707201e400c100301400b001500c24424215a095090741c1500705041c02c0380c1e4540b09a240c2a8007446041221a400d050070511070005211200205549488050140c0c0d009810540d140072404008005000c9280000702045103030400a1000341041d46802c0d0fa0381c04050645040560b00181007010307040100154001000c0103443c041d150809030800c4004601c003250548076401d5140411042ea64010500d8114882a14041801c50310355841d10310007500240c0c0102d44500c207003900608000f01d0240c0388440700034620010203108401307100060680e40b940084004140c2482000c8030300700c504180a902d80c0324156003454403020100005403440044103803401e1186c81c14a40082c540d0740c0140d0b09842842410024011000d4070039102c012148202c801500c55040320380107100241884e40c0305241e10590140c50a480798681c401c1c002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 931121357 1250 931120107 931120117
    0x1d040b0429070909141506090d050a0311030f04150504050409052a01020a0f0c0f03110a0f0503100b03160806040c050102120d020306011205010b180f0f04050615 71
    0x20401c100c0002c01100590001942d0054032284c0300600100c2c1504a64400c19840900150884001c90301030001036203400b025100c0c5d140004044922200032030600e5a10303610b0f004001e50018414140d008442d10b00001102d401026403522a03140078988141a4031035241c4020480401c032041000140540d51801002074613405000548558960300140c40307814031307410401c41200710031420060180d070b0300440d0300c0c0c0d00c0c0c40e040482e0b2041082c4925245210600c0b980144c5c0c2202d903c1100030060000c6208840e500b03460684260804a03100d0059188200051007001d034198440ba0641942102039000400c0107800030302103480c1030506201000342d80b140368000320501d80c070110400080c0310900001c04000d14080c0048c01d0700d00e06540f040d80c1c0d9171107408890a031443d000404110329074800c901080c038860050200b00255615100132008507480017001c801410a040201d410a2078007020500c08103400400c0304181c0748101d828800500401050540e010421036440000c0c1c126082c0100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 931122607 1250 931121357 931121423
    0xb04060906090e0d021618020c120a030b010513060c050c0405070c03090e010e04080307270503013b010603050a1103120309031c0e0d0201151d040b04 66
    0xc0340300f01c984407045141041840349802103610071aa481100d05400380114180d41c680050100b001c00820303080d01c080d1140440c070329003034801c420307000440a2a00300582040001c550b01841420804001151140196040303004141c221080800c00b0340c0c00341402220181c4500e0036601c4030603d62000500b1220125680d202203036940440340200340c2e1100d500301c040c100348107605940354140b544070b00006900030001400304c0c0700000410000c1d4011320124560482d40205038000001c1c1c6541c0c0c4011000501c07899000390b090070b1582c401c0000d454001e4a10182c030791038003110701c000b600d8001c000b40e1070341481c480b4039561108044045813090140007010b40c01480c1c110714500c450b0341030500e890103a171400e0000030010b009010b05180c0c00b000703c400c01010500c81c40c0e07108a00b4075082000f400e0031550b00559208150000141d90303019040600307135010300c4030003080e00790340e4000008104801d041495190004a800a400070303407847e868540290103024030071021140242210f4500a49806003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 931123857 1250 931122607 931122611
    0x11806020d0b1f0c1401060303200d0c030f140f070b0702150c1e031906080a0203030906030a020f070f0605070c03020316080c161406070210030b0406090609 69
    0x210608034400d0203450303150b0700e080e14208560354a04030116441180c02a20404004031200010309009807000c1d8000d08444100082102d1741d84d030320f8042c00020101e8071110900c0c00d40441c240450780b0208049181061540b03403010071440658081301e039251441030607424829486d20980c0d0520b6103101034094078107401c1c00d550b5900e481e0f0178000300c1804001d141c602154001050a07046010300d01d25103800c40c0c42700800079102d02c2021203035501c81800c681070041800c0003008010480500ca0818030392820504400c00a050711421929142d580b4407001941540c402c0150110a0030000c3c01990311a000d0540141440c04d880c0d40100554402c40c3d09840f1079a40c03904880522815110303685c0c01800d50304005400c16aa9500030f5101c0c02a44030001507012200071030024056688100c0c6d20711011442550b5000c000a440941408064001d4082c0da4500b0010340d80b050404800b11400c0c2c0c0e03001444000e186100300c1080340074104600500f50842c1d11400001540c0d4841e00510700513203205000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 931125107 1250 931123857 931123867
    0x40204110301080703140312070c14010b0a0b0336070602070e01030605060f0418061a2b020d060203150a050a05040b010c050604060507081006020c04020c01180602 72
    0x410094031160a508102000d08000401542600140303820440ba0304c0407020800d40c00d0501e540d405c601031107080d000b051030400704014607241e100b0a80d2005034407403015000200b10f80510300f400c9801c3d500100ba084400c00c0b9080c0030212100c2c0107144e00950010b41554203c84403104891095190344105150080101ca041c10506003844044040d148030b1008010300c0b450094808450305041c8405004d80b0341c0d98022861903152109806500e11014000340814420350b44a0380c00c00c1c103410001e41c0c005141440b1241040002c15568000800c01080d00e15a0b00174800100c3d400c17889060b0121840c1000e00d101001030721610041030205014190041c0c49103403000404905501800c0d025115045181048c000355580c0c10044050700c909503400581940d802c4010b075207204040170060000e101e810100000c22065800040c41030f022581c0b04100c90301c07042c11251212883d40542300268103c2c0042840074202030303000d003d03010007010002c0340c09400207403c00030200a000045d40e010347c000807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 931126357 1250 931125107 931125109
    0x70b0a0e040f060f06140c06010510120c050d0b0a0e04060506031e0115060305040c0b030606071b1a030903043b0601020d0c030c11040e0d09062d11031902060402 71
    0x5240a403201b205000d40d00e000072011031140c07a04014010340d41705480c900070480c00e05201b03019621650311444802c002403400c0310704c098015000225408c0740386081000c4854142001c2c81d110300cc490a03220002c0082d200c950701c81c00070b410010911505441403a441c00ca00d4151100d450040c055451700004400c2c54020004603500c2241d08200c2c1451b003024184400110180c14410869070300c44040c0f07489444860001c0c1041c410703000043c10562030381d91642e903001880344a050031500c0d00e40800300c021030700c0ca404903640d0000b15001d00f210703002441304112052200001c3d04d11200760811a44540301c2c520103200140d020707080c3e1030130001c030420100201c5503010031517102c05074024140040340c000b032998000c00a4424040040c401d084ca80320300300c1552a1034003c0c413203c1c030f84002a01e000342520817000704074021520031100010540001e5984241c5203402d405158103080c8001a094102e42200381c9848100c001359041c10b04c02004103818045030a8502a041542c9501401440c14240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 931127607 1250 931126357 931126367
    0x70602030708060f21190c05191a07061d0c0a1a1b0a0c0612050c0f1219020406020f15010b04061d091314070b0a0e040f060f06 56
    0xd00f40e500400805075000010f0f5503845a21800303040202040390b00450b524442c50501540c00f4403414880404602c1d01e04204152815005540b03054660388103203e030841713074080345a074944646c030040012820f481012012070b00013021442e014043c00304a0b01c072602c00003108107004408c444130356040103507108590b01d0522a401d00828036900704003c88001841841041d2080244400203070441012040c2e5180c800e0081c1e024a40c1c00050501d00903696500190140c00188020a5441c0c5880000740e00c0803007250903070b966150100303038003800c100000c010a10f08010140181403141c0f03c90b10500712045580c0003d1025026aa010300903504000c00202d2405042d02e03103007084413800e140140813509032a82610122550b80c0f910015543d0040c440c0b10690001c580c072560465074001c02c001843c03012190b0414241e11510ba07902c0301d4400c03003a50540325203041c00359801d080c80402114103403500c241c1b41d00d0302100c0002d00c001520219070091808840c01e40d4440f20b201416000d041240031307000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 931128857 1250 931127607 931127611
    0x302090405131106131a0406022803080603010b1e030705180601031e0608010515013e0703230604050c09102105010606030905030d050901020c03070602030708 70
    0x15014050032409a0391442c083d00b410304210300420011400c441343c02081c44102d40101344482c03200c4c08002041c020414150f1141c044d50000d88542903105040780000010b80e01300d01d8400440d103044075001c0d901222044030150402d6803541d00c80f42c450206a80d511200d0b8513040b070441030f0082d00e501040500d130a00c03900341d100b03a203c2c90900519400b0182e101c1401c0764460b1092900094110740e060400d90740482020300c81e800c16140c05404030f14100f0552085000b1650200514800384525004440180b20710420810b1101c051038080100c10a003146034020300010303a01001d2a10507a5426031030500345a2003940d0078104a01c5105240e620340144522046150024000c81c2ca02034030b56941d1170b1150762000b4040c1d04541c2c0080c0e90b5803044520a400f50101d590440301d28540031080000c2c01d41070340001e40d103039480e01c9000a1424041c0c8900c0780805da004003d14102a4803214410050000500e045000d5400304a808440b17001800142642072140030016100e0410210042c143c80c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 931130107 1250 931128857 931128871
    0x501030b10081501140705060106170105060a030e121215060903150c16120807020f0d0e040b06040f0f0f05130b1906020a140102190f090b03070302090405 68
    0x71401031000080e4040c0391a6800001810154040007042004a0b10b0043c486155012400045610010400040707107080c101c445540d00c000003100a00034200c681c084c20b2180e1a4004400c00540c44114080d4001032801d08548043e140e603a2045100c0e200160700142035a40c80c64090410802c002104003100382d25010240c9845052000c441d01081d6646103600d00c030350403100e8080003d040340300040308407807001c0f4902d0000d4125005a2409108030702c0c480c40000089410000001d000c030f440042c818030b201401c0801000f041c2022700b801d54942100c48200e6401540b140b4500c45683c503000b004200501e2529140c041151401d01c913540c651000350070040b103071071303140c0e804100c540da40184ca001c0c4804400000140038103c80c0c0020240c11000c01d0803401c0424ac1d42000440680108500000f54000c01081d42c00c0c0f603c202c4003500301c3c0315000454a904001e102030b6070050744506012982c0101908103002a5a1103001407160341e0000c41c0e55000194001440000384d040c41e00030f42d600141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 931131357 1250 931130107 931130119
    0xa02161509150621020f1302040323060702010c05180a0f0b030603070f0305070605210405012903070e0907090f09120318081c0608011a010c050309190e100501030b 72
    0x40c0c0380d0002d4071004460381424407c20200c0701d0303107150060540c11a0001c56100918804000c0741c83ca841080b00210b520569150040d800001e20307040c01805210300c1d08034190348003850310240c0000200b007101d407071180c141c0040903148082107000c3c0f0107501718054510b00c07914948904d80303a4105481c1402c95000400705590f9588200300050001681e1815580c42c1d041072925071031100714012107050704203030450821101600340424080194003500500d03c07658205038800030003843e004540700c2c000e110300d80c041c0c4c042c100c10401c450801402c4d41d00201d0740016264003a5551600005864020b0f070480301c250340d5580c1c00400c10003501507400c40a07020741010702508010b20f40c010b00c20443c0c00c4d0060000000050300400e000340c01103101c080c0b0482045c0c00c103e6551140ca01e20f000344141880468520070103001c184856001d40c50480710310354082c000310b00d802d40c1001449242131441070038020f8804d0406000c254020600004d9100300360164440b00703d50725280004080d2411412142c2c0294 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 931132607 1250 931131357 931131419
    0x206280507080d0507210f1518020c031c1a010903031b02190807031e0b0106050d02091c060f020a050403110f0307030b0a050a021615091506 62
    0x921000296070480c400110001a03a42c5c404900342c0c0c0310a03242040090803003c500380030310301401c03a034000c1b410440345d04820403000c0798124014810b0811400380c9071180c4184840b0001003c4650010080c0c2d40300740050ba030500a000c4613284141e606801c80c1e80c151501c580680901041e0700541c4811174200b40b9000c40c1c198030f10388018004a21b801e51103201582d881c580c43d02991034045103442800001d00d11400440d6951412548501e40c500007110240040044060203451001020340566000060303200d180c0d19150064607035034007032210041043d40a01200c0004d5440b4503100400308440e000c41c032070902d000d15107a41214800c012415150b0310600410313505550010503582506c0d885402200d0031401c01d00018030703a05640c00300075071510400070040200030704103100f80d00071409184240041e0b11103541c03440030307800f074003084c001c3d80c2040260400c08507a00c903004491250401c031001904004e192682d207041169480401200350f2150380030044002c0740c103070f4034120082e00300b0100450 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 931133857 1250 931132607 931132613
    0x201e0a1205060421051b120a09081002340203070f05090a1a060d020f0a0c03090905040203031204021c0302010506210c01111c0f110c011e05070206280507 68
    0x1406100946206031810a9510308031072007c0041105580060441c0b80d01c0d0540801c1c000c020300d4550084096a005020340c0000403210703402070b0781c1c602d0142031400f40c420008414140082c0d5003c64000400c1405030441005070302c040c8003c0024001385204038209a0504041c440c068201030034419085107843c0f9444114002400981c0601c4000c8516a55035034009080070080d000742d00c0b8160301c1103070005101804940111004100500c00c1d200c101d119a0360f4003091003202c40446002e509900208111490101c04010050b0700900c01406902d05000d826607420694000510480140c0e54131000e10249160003014204a641801d108a05040d501c07404291100034a940300ca0601202e83d10403440d8040030b01880780b0741d2441d50410a84480800320081c000d018641c000c2d0042440c108004540410118540306c0180c0f0607152000300407503034038030700810650000c0c0e00c0c0c1c00c0040900002d4016900e5000909401c5003026010131000100f8002c01103c3c0e11452800060100400c003100c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 931135107 1250 931133857 931133867
    0x490c0329011b0206041203020613110630010e0105030f12180d2604060804020111070f0b220302091504090b0106020109201e0a1205060421 61
    0x40c2842c144012490400e1a840409000b0b14000d50080c400702e8007064500001a403100f000e4080d50031039005464800809007031010146000e4888031500d1014616410072000500000e03082080d00c4a2031820300100010030f6480c210441000e05100c00100604440d04d480240036000c1200035100d0805032400c40303580d46ca0a2460102110300c00301303249040010b41c8011240c8018040c00950700b603086890725058901c0256003907030300040200f40c0c018082c5000b000359402c2d81c0c0d40d901c5080140d00c1d02c0c1c0054505040c0e06000e00501e00c11010040340f8040100c0d010700c0204003100c5807c1c0c80b90401003248020030359052a80004900b4140300700b0144c0d546030f402c5c3c1d8100001d44040008964000081000f42c0001131005d48060307980000040d44550561059001900641d41a500340524078030705418206000110b55200c4000b20b512000c142920007537a0ba1030000030a000c55403039581d200fa060060700c070041541d450304103104220030301c6100c1300c10080d03000028403200800891414041c0c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 931136357 1250 931135107 931135181
    0xa12120e0109150318050a150507030917030406090512090f03010e030708030a151205013b01021e090a090c080a0c051c0506011103490c03 61
    0x81503101c40c17030307440300da40418000c84120340c0000c1590000f94031414114400d12041003903007800d500e44030009050700d1213842190b40003a401240c011903003e040348042402e42000c0c0080c2c0d20380f5590050140003a10410000380006840001c1c1d50b141c0300c00e24104114000014042c50299040640314248800080200c8040303a610581a0f0f80380e8070b54400150040842000c000d640d44070b0740c00049aa40755400000801522900c021301104510503500e15295407400a4040d0f8041c1d040c20520ba00c03107818880c1142101c0030f1000600b800724a80f40691000302608050215000004208105007460b121104c042e1041407400e020824144000820f20600100b0300e04284c0c0d40c0d146c1c03460300513120784205c0b00c442e10700018203c00c000c1c500281000401c1d0543d0f0300d034007151800306420300076500402a40c030045040782026609910582c403406850101c07001c3c0da8500d4480d580c8008a14050302c1e2210208070240000041c8401e8546c0c000d41151005000a000c608441d088480d44a01c0541030381 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 931137607 1250 931136357 931136399
    0x60111150619090903031d2b020c0405011203020708030f0307180302181f031707060b030316030905040b100f050d0e0f060a020c0d08060a12120e0109 66
    0xd8003565500d003940c020b168107403c21101142003900d07500500da030641010300b01807114170010800ca2002504607594080c3c0c0001103030403e00c0139218911402d070281c0740d00110011030040e101c02400a0000400300c8100360007003000d40c2d1008031406d09141d410040c1174003078080178004500c2c241080d500d03c55540001403403034080210380012701c080e40c0d50184d07155008641c040d050416404400e520803400c424202c0380d0034040c185408401c2c02c00140c00d548101101c0c0c004c607000e1407001501448690030392181005460240e100c03405022940c40c10002050030052060300c44940d4411840d0003000300c5a1075014510840c01c042d0451080d6071420850703029800f140c01c0c18048410540c0050359223000d10505041d2181c27030407000c0001140f020a107084800075031010350342555070707004050049000b925907024180e40543d442c101c14a0141015540081008102191040da54010601c0c05100104100d8040518050343c5900680204207111100c500742040070380c460400d59007203101403110140d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 931138857 1250 931137607 931137619
    0x1b021b0108100b0c1606052d0403020603360c031b040f110a110f0a171b0105070e040c0e0105030a0f0912050306090a050402030d08060415030b0601111506 68
    0x80800e11300c0401c83c500482e601d0100440d201c941c0c441c40074200da003040b100310000501c02c0300c40c1490400c03184205070f000340148079508d040c5411034080c000c01342c0004000b000002c04984960b40e8401808210054014050b02001c02c00003c107007606003082401d01825001e9449414002a8030f0701203a010303640040c1c00e6074001022503528107035002418624541d007541003000100304c1240c680c40a048042540103900302c540200c440c00722aa0b4400019a0180c003002e0142944000c08408000800403083d0101108443c540100c850fa0300316107043d603400780420004001d00310740b402c1a0080c40480403841c284540304012140010f01140b00081400040581d210520000c0b900d1951003001455000810800070640f07811015000fa841500e0030380c80382d02000000354100c0103038041c491207a503018010b0410301c1080d50040e03034003402c003a010550103034940c200c00803040f541030a868011801044484510b00b032180004d0078000340b622110807160881a41d40c4980140a40403e421030020703514 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 931140107 1250 931138857 931138867
    0x10302030a090b01082a030604230303010909020901050409020d02010f03090b0115090b1e0717070f02010831230f0601140f01121b021b0108100b 64
    0x92200030010b80300020410851a00003080c03c003800a01c01c0010503c007000c4401d10b020500781c10700302000c401030b5564140c0c0017100080010707420a240b42c100348042d10f0b482c41c1600c1443c0301e01d03043d504240c020100b0b880c0d641900d1015860071a21a500620090350100443c0700103401050f031901e0107040c06818440c1206051040034882c0c2d200c55040c0f41c10001041c440d503191003985501440540d00c040018a036003901280c03208019080310030480040d001c00d00c801d004c0b40301c865115003000700182c071442c160a0000301c0d0488004024011075121303100058000704588009000300c60042c21011807142001030841e401d00e002282034a01c0309a0700e22044550240b45081c0f01ca4088000d692080102091404940150001481504403507131805988603a070721045005044240b041040f07a0000702411042e010b540640385008450b483e110b80480d0b42001c00c1440e2103000c410303410104c01030b0b0080300181c02401010781c42091a540901e00104241800e610800401c0c1842c00303120101d20001507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 931141357 1250 931140107 931140121
    0x806100e0d0b0411032b0e010207230604060201020a120c050d021e0a09170607120216080c0307020a09050103230c0307090618060303050d0b030316050a1b120201030203 74
    0x8042513452071300404a07042000c0107070306e031000c082182017044010340d0343d4840c00b003c50703005020003440008103a008051091800c07000c0c04000d100038a4220390254000385007202a22510001c00c060440c9030001340e80c0e40580c0340011724202c40300410b510400c0c50800380a80b00d6900100f01c0d865019072074400750311010000c1101d20041d0702c10310f4902c1c10840000d8040580c5801080310011140a5105412011003016000307131a0f50017114040700090011260103a0700c0034583c00b42001d542031141100400c06d0a0f61280d42d05c3c0d1210030326a030302d0ba1010035110114a811015200500651041032220303503d55a155074072101d030340140e01b81403000003041c0c22503da4100240000300703100504a4000c40da881040b58000c020500a0389180901507034a0420742003a0300440301126816031742c0928100d12012005c00410200601c40e5250104003c00c2308a9500203040400080c050005821550b16030324201e4404651213454441850205004114401c1c80d00744080c03020790207003005a52a80d5400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 931142607 1250 931141357 931141373
    0x1e10030c0e060409061505040803030403050a0c12050d0b0a180519050c070c0605120103030f021509010e1c050d05071202210a0902150c0307080a0806100e0d0b04 71
    0x1c00c1500001c0104000500000540020303040b01c1d400020908074882c00741c0300302c8143c0702d24000d03002c0544c03080010070002846200200116a880c0c5042d404c000410760305c07855030b90010f486000000d000440e581a40103254864400d42c40d000f00c0f41c10180070714021407412602c20b0300016050301c070b5071100020b00da1000022100ba910388502000c1085140081e802421500010010364906201c0240490b000b0302800460b90044a4814100540c0c1e207190380031298080201000411030080703554669004101c80c0c6c04a0140301a00000b01d007100200f003649151804d030402000300b000030300317003002261030f00082112800c5428100c0440c40340d40303006055926a01400d02c060701c0e0ba1001401403400f81a8071030204020384025024035490701e44550700b00544060000195100f103000c0d00c60030300050b969005164180b400c4050741e09010407919044a590004400640030406200401500c0e241504e03060304501d54600b00101d00454800c041102691b00d0f0030000d0200d444000030800344401c00b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 931143857 1250 931142607 931142627
    0x503030f0f0a231b190f050315040b0301021605010603060c0e0937151a0906161a090625030f1e1a09041e0305090411091e10030c 57
    0x40010071350355501c2c00310390505c4e04242d200000300250815052101c2070348100202c0380074035002003031103249848040800004020481545515650030843c1d2440c0500c840300d4145182e0042000007080c3d481d504200080e00e840340101c0c2d04015060882d20482d640e0100e0303043d040132000301107840f0560313451100e1401a01500c0d03c801074455170003142000c0c0c1c000e60800080090940c88600d2500c2e910f0f18100580c0026400001003802d007885000706a043c10701c061b002c2c1c403086188020100307940352100703010084400c860100c12443c420411100100030422240c11121480342d9030b141161441562500c1507a8a180500305070701e0b801c2d8001448444d42281c040e258240d02065110300e08110205c0040444580100e8080008071800e101d5290902c0044e116135040310003040e840002031480015009400021801c0c4001400306803c2c0e80c496200c1c102046d20038003066a0b40d10030080420240030005601c518420019201c072102ca62103201007908201e055080c041018a42128162803070101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 931145107 1250 931143857 931143901
    0x60515012007050a090c0315050a14150c031216090302091906080d0311070206030a020703050c0f030d110703140f0409050c09100504060504050d020d0503030f0f0a23 73
    0x111304042030844d120b0380500883d69403074408000031010440d040a403500030b4460584c1c08011000d0401003802026101580b852005000701142d04040c0b5a80c0c035150030104e0010740540c4082400121224407039140d941001c10540c01002c4003001d1900140840454003000b40141d4605002c0383e0848009500354102c440d01c02d00900c0b00e40d0f107980440380ea40381c052807002c00103810315003010303881020041201c000540190815186950702207007070010350300c890001c80c01c2060030130100382e1980090241100810418014681c0c604a1082c40000d031a040c0c102c0304c8042e80200700d1103000981108042c89910048007140b5103071111501d5200e071501031540101c020314213000802c11a11046402002080e00859082c10311202004080703506000381c0c003442c00811010801440303145040007900103c984000c182d00c0ca1400e035955110700719007041d1000785411a000081c4412045c0c84190b20b0361007901d68508000003007041540410b0000b085140310060003049000c0b03100560b21044203040402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 931146357 1250 931145107 931145119
    0x1202040f02090d0605091c050d020306010c0f2105160b061c03080108060a052226030a0501080d0903020910121b150801090b190f0306051501200705 65
    0x81d00c0e081520103041e00321000340703180c0924481403400c2c1409290315147e5a81560310242024106424000254005481941404044848840042d140d00c5041d003001d80b10309884090b000100f01000d00c0001c13103d00007030622a0502c40c052940c0028100012100e800c03a03e42582030310340c0d1003c65180c01c0740f14003007000703004104503010500d41c0196240d030403200340344100e8203a0340d5052a15801c4038800d8441c420804451811600941816850a0b00c894000c006203010080180c000850700340000d280941c080c44044204800c00925104442c018041d20001e00300701e0000f680c0c000c1c0b030800706000080c4070322880c0c00440c403101140c60303416020b0240d401081401060f5410981c1c09064000c209001030000c0800100b240c0954074507021506550740c03980d51450342010400340150801c00103082d007143c1890200c4114407101d850340030041ca200543e0b08100da045040a5054500007483d50440a41110307400c685c0d40d0380b1040c80300403c1040900c1c081b0042d40301c0c180d1030408020f60b000300e52040d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 931147607 1250 931146357 931146379
    0x2010c02010c151a03060c0a1d100306090c03090c0b071103010203010803040314190f240608070801180b06030708030a0e100e0f0907121d0606030303011202040f0209 73
    0x3100340c1c0300301011961108001c18035541300042550343d81c02103a2aa00d141c2d4240089602d5500034120781d94101070170000c04440c03001a81c00700d004580b10b800031100113a1500c80c20031900c540c81c8101800741c480341c0b03801c0c850710b082a00d50064814452107842c0c29202d001641c4800d11010300901c000e400d4008000703640d01d50307559010641da50810700083d98800000d14400f14a0f40000808058030288035403c03030001d10312a10740340b034000702e01d5500351044031072000010b680741d20101c801d403031165009000290f19403c244117545406441c1e0840c2c00641c2c50040c0b40c000c0c1c01030060300f1800030f580c020728003000d0b5030721a800300b800d0070016031003c0c01038800811161081904403400486005e0142c40e81c42d0003884840381251900c850040594000c840c1484181507401c0c004200381d0b000715141009030703900c1d0419030300404407155002480586105c0007124102030b1800d01c081504000124029404d550400d052552201c840b000024840c4d59181d1411241c4641501542d250000040c0303030362040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 931148857 1250 931147607 931147643
    0x8010b090102012c0c010c0b01030b0402060702100906201e1501090207060f06060806100302130b07060c1e0c051005070e1002070803090108150a080318030d0c02010c02010c 76
    0x9a040e0314007031002c078040d000d01001ca1b54410f40003050f13060381010301d02d80241d1035a00c800880c00400352050b80c204504102c03180142e29455040f00700062960b84110030300c0c1c90020002c000150a062240712281c10000b8a1800a8002950b40d11150101170301e402d130307069607141d00c1d15248502c0707054401280040000980e121a940c05855500e000d0982441b8600781c2c0d56546040b035405004013008100600003050036818021503401d907020701414014980000040b05640d440032690000040e1440080c620041080a0164802800da9401c008003d4040f82e10708038251250003201c0c500300881d030398010b420701004104402c00c4001c4007200b0041e0b4207100350002c041d80c091000041c000c05852003019141d61000400130211800350b80618144000a001150180405400034440f81120300b8509499a0742d954104002c004900003103030b0700c00003034180d06e6007100345e401c1785403003900002c00b049a4603401980d0000071540c24a03007603a0300d048a100688030b000011401500d002c1d003130180683c00d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 931150107 1250 931148857 931148921
    0x21010c0206010602010e0d1205190e010b1c03090308030c070618290105060c0304092c01090507060c080d0c051b12070602250f1a0708010b09010201 65
    0x1030b6a0f60394000d00c0b800d041d45c02aa5500c441035141d88001480140c1e6181024030716a001603002114074a500e07240e440c0003a55442507070601022401e10b80d45d2880040f100c0d29015607964140b400ba0440010780e5110f40e1030103840090340f4800649808000170000c0c203607403490003c0303418580e4005004c00c45840249501209850421400c95101c03404819000014200c80e0340c0c000181240c0f5021320090382084140449030b04484c500c1c940a120a0201248111b4140904c00f110150020154201e040228041280400e4018804407a034980f0007250081a0702013898002d0700c44904000d20302401c0d07850302c0561485842019215145000d101c0001170394804002c2004040b032240c1e0140032513142d2001d81c0ca481c1181c4000001010030000840058595000740480c200350008400a10035102c12801f800c0130151011501f9181e0741c0002c1c0c041002e4081d1141d800404d400c1c0e900704514200a02034428407040c002d884004901061080c02030380300350491b603c9401d08546607007203c4805e170100c0c45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 931151357 1250 931150107 931150109
    0x309080c03040815090109050c01051b060a0c0e0d03020a0f1e03080115020328030b10111204150e040b0a30081b0102070b1306050105011b0221010c020601 68
    0x40704c5001e100225160940501446220503009806045800071040041d00d0540c090350302a403240f12251505140d41c481480540d1040d8440c3d0380c0403c17888001302d0001c003070242400c2d901384140c040442000101c2e5000500c0c00001e039000400905a06513818548440d601d403a81115000035070071114030030158003c800a0482d503500a403100c4401840c8030aa84a0040136061030b1a002c142102c44044000b00842c1804c081d0681000100c214000b0041030b00594000000808034a1100025429203002c0103d00080c08a2500f81e90509080402907050150200b0402c17041003038207030f48a5025581ca50104040e800010301c8c120406960303107184901105e80c85013a0351040d04001031320603440e94880e1301d0846243d110810310700c0e0001010110b903444111322481e040641d400d210a50002d94031003034a5005411180e50407100b1180342c9015001da0348140c009a0411901c1c01c0040241d00d140640d25008690440d0000d6404210f00443d0107808110a003c16441d03081424070700d40c0715000304000e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 931152607 1250 931151357 931151383
    0x5061309050f0d02060610081003081b0c0402120c1324110111190905030316110409080306040b060c010504080703090b0f040e0916080321040f02010309080c030408 72
    0x14070700f207003612410307604c882d000c84007250001246a14109403e100b1401e160748442080c07806405c2680301d865412507600071003014604181e80c848103003402d100810079030724140c10450b0f0941c0b4188600c12102814000501b4a111640c03010407850450711511518a0140803000414030000b4128004200280d0581e051a404680052003d6202241c103000b9001c40010301d940c0702d4503201600d60368000f41107036003144034108100443c010405a0702800102001d09006001c94644400e50500344007040e00340b12101c0c41140b4001c00c2d000080c08900c01d8962018085400044020702c0001084151084407840d0005510b00001c00080180f00341c0500702c82030181c0d484200180c8c840d05550700c1d031320910390100324002e01804104801c03d40c05440302c0d407008904054400541e88580b81d4146d96170241c0007980550004151494950a940044840d601203c0c081070303020f04045d181c80d0f030000c02106002e41016200c0640b81c0a000c1400300f203442032a180000c4955841c3c4c0c1c0c42c686a1600c18a48443d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 931153857 1250 931152607 931152613
    0x90915031203010f0e0408122703071709090117160b0409063f020d03200a1e02060702130203041a06131e09050c03061b07030305061309050f 62
    0x3060341d07000f41c5c200ca845194854125440d02076001c2c4919403803500181b41c0034848180c007000d5400c0c5052924410012020350004645403c02e928240001c001c482003140100f0348141b2804445a41381d488407811520100304800c01d812000514030709154400148102e0404074070000203c0301d502c1c200070320480da0004070410160f03440d8516010f444484a0300103d03480e4840c420b118a031450038650f248140d600d6407016502e10850740c0404c00070b1b02c40d00f6007a00812a412a03144100c040c5083c0354072400500c10240030009120f031b4401c20251481c00d80700c3c0300c480c1c140c0403401c00c64a802c8110780b03c098009022030942001c01c00c502000c0d500c1281d00312070200aa40b145030078a25002030f25405020010407001c002180d540c1e2000013041344881740340d40c48503258012104003005102d0003d20324000c10150100603c2d240030701d0700d016005404010000c501e42d03035116000c0d0455080d62400f99162030082403648440b4002030940f1070400e00804413901d086001c0c004c11030001750a9008034a440c082d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 931155107 1250 931153857 931153859
    0x1110309070602010915020918042001111e0c030f030c0c01020c0d061e020a090305190c17030c0d09031101180b0d090506010305012f090915031203010f 67
    0x30407800d985e2403050080c440340409900348100c0e0380b25000740c20b0407a070240c084410404540c40c514000b4900f61815207140c000c1601420312042a0b00038031952030380030b0a00003401610369180365075428010541a840713a80c6040307001f00381a01480001a8410700070104c070049180b48026a40300d9000085a00c0c462103074402160301d5500215003500591030007092903001c82c4503915650040d00c40c194207219081c507011120085e585441c80913058500e12070359525040c50451a00f01d28065141d1142891080d0207040354000401261142c3c0035149001d03840b00b80485107288482c0f66018126468081c3e0003600141a020b940c4450310300c01301c038082d400075404000714000643e4640d589800050000c950f8103018030908c1c003110300409141403044400200e19030b164850504050302a00212400d17515030900e03010861001c040c48184a80f404c0c40d42c048201c072000813421910814003014014502480026038580e403158490a1a81c00a825501c0100c43d003180c1d04406d80c024000d03a16841442c0f50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 931156357 1250 931155107 931155119
    0xb09150106020d0503063f07050901120602090312040b1c02070c050f0604030f05010b1f09061d060d0b10050f070f1b090b0f01030207120f03020c0111030907 69
    0x40d40d103c003da913074407039500e1903c654061044601f9404c0101d03155011060707030101c4444904400c0d603091041c65000d004960103c04040d8108030b59a0301c42c0f446803210f0001400020001888200383c240e10140059480d203c0401107030a1100001050300418008a400502021228010300d00391805454041702d030250060100c080340600b9501802100f50441c0c10311442c200459003c1815030f00404403403c0c40ea50741c3d40c5201041350007a0480d1941d4440064001d581010400402c5c82c04103180c1c403085001c4907002c000c0c2030505510484003003040d9032252410181ca01c50148a0481010b0070190350b8100c01c0400710044c090a09030503014000342c01c8510b94140c07080e01034940c0c082006a2301460100c6d80e40399040c01418001c400d54080c40003050750201100c0850413040146921240407402240e120704014041407081c44e45d0b4145401081a10005440007444009205443c10842c0c0d034903c3c001c0d0f00b10001c0c092020007918940c85c1080c18510031218102031441583c030482210202610b0383c2c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 931157607 1250 931156357 931156363
    0xb1e070b04050601120302030909040312060f1d01030f0b0a0b0414070206060a3606030f0b060604030f0f11100e090105120706050315130903080f0106020c0d0c030b0915010602 77
    0x105d40540182c1040c848180f991401c0c00718281c005000c0c4c81c0000c1c42c2400c00318600b00300e4500b9840185d0700130650710100b0901802c00e940c2100d10000d010b0452541d03245480b03405015500c840010480c00341c940018114182540c020110198040c1081001c034100b081c0040c00c6550698044000d031080800145151500415101c1a144034a9032034148400e81e4460000000c103030030b015101041401c03c24010840684114402140940a032441941e5582400743d0000340180030103000c0d4400b0002800840d24040c11426900da1212a0074000c0c101801c24003e03805802d807078158000d4003551503030800e59010300d6484082c1d01c1168440e48590361801048480342135100c1d000800d4200c07000800c6903c1c080c0c03010f1640074404000f03405035a4401000075a0310521174aa4880b89590b03222518141742d48030030300d83d41c448a9042c11001950510078003070b6031108c05543d514840d0b100c61103103500b000513030b403000c00080d41d002001c183c5505100d407030240c40c1d81001070052650300c244800081c0041c400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 931158857 1250 931157607 931157639
    0x20f040606140703030603080a0804150516260f0114030102070f060902030f0102030a060e1305060115050c19121e0c06110d06062303010b1e070b04050601 68
    0x10ba101d044002c100c003070510b00c00c0d0304442d0060b000d141d520500000803c0c4918018900f020095443c68145d2901d460404d0019054040a000b0b261424081122282c1e00400e030340201156410904070001145d608158100410700054222001c48824020905040d151290503140c4800000c01000540010315080b400303081c1c0050581c064a40e45d150120350503501c00d00d0801d00281c251004400789100107803ea9209032040030701107540310f50030000d031048c80800c0c580115180c0c0101800070055111a640c4010601850313880d00460b0700d50b110f0481c000c0040b90340d000a00301c2610450303a4010040080d01350004c0c1c05591000010084841070742c8543c5521050301c648081140d800a02d040b03003103030004140d00c0200c410740d0b0f80b100b450710280c8084000c0e00070f014101d10045012410401e000b02181c0c881109a00601120004000400e168000340c03411755030040c0e05640c90321541c507503800b8404c12017000c1189407440025064140098014518480d030b0084084912a0343d03950425030000a003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 931160107 1250 931158857 931158869
    0x61a010e130e07030b0f071e0f12021e07120905060307030f02070b010e1605040b090d1109010f06091a1803070f06020c12010b0d0210260103020f0406 66
    0x10762450100d40105611a080d02c144040880d58450b89a0b511454054801d03121000b006801d9030400030742c581c1c40301042c10b86441d020186c500c9440500c101504445000000301d082c80a140c0056840805c9030303055540060400349505541940117500030360b00d501c440425109220401e019041c10f0f1302545103401207130344c054031461442d03668001c200c0041034100408400c2c1d13a001c1260f540031504683c5420701910b0540e41c44401820800004802c955403441d030b610600205000030824441e00d0f4099034844807007a5842c05500090703161988960010340440796100c0580000400e10144404588080e03d1141d11a9040c40b9107400800712002800e42800c8940e83e41000007511520070a44420b805407005002c85640310b8442c610440141440c0d041707140142e2142d02140c8041c42c02c03d8410350032a500000801040c964240460300340c1d12410006809810012400001c3c40d00c140364080101c07046c41c81c030341f1142c103403d840c0c2100c00c04284030070391160741d580c0c8121585107040d101c0d0f0011208 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 931161357 1250 931160107 931160119
    0xf21091d1e0705040513062313090c031a0711160302010e190603050a0c0810030b0711030406030b0a140a0515130b0c06071106070311090409061a010e 66
    0x7916148901040c18000c0041042000911000030280c84031051290310000000000c100316041c2102d4001500104290469026074042c0340c0f8500c2c1c80e06540c0316020352500303502003140030340c9041180040d10320750310040c0342003904100e895401c00310000c0c0d42d000f034502d50f40d80400c04102c028080e9a440e4000c0780c00310a500b402070100010360044076011a11a809442c4050202070880340c0740b9001c01c19441580480d4031401000b41b8a030051081d07a44000e441d0504801c5801c0090400f8000702041c0070003880d210b11000803074442d40c0907000042040c1800000c4a81c0c80c0e842e000020044c02c064484107006646402d400308400340ad07081204282c071000352128140514100c100481044040c00c441c018400420544551301408401c5001810128500c907a48440c11713500710f480c1c110020408003c10094403018682c651010a44c150401040c1c078011a540700e441c8085081d920900300c07240d40c8035103040c800d90200300d0f07190091211080f6241041c00780300c0810005441d0f0345d0111180e664031607 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 931162607 1250 931161357 931161391
    0xa08160b0901031b02010c0201180507090f09020909070618030302031204150e03040513050c0403110f090f0702070b09130905010216030c0b070203040e040f21091d 72
    0x2280410103801103141c14503011030441a012001c01030703030049101031801070b510345144c4801c8940900402c03910242c07100240202e02e2540d01e4080e292030310341c002d03030a140c0d4032150100466807041d0030002031507400920059050602c15002c507a04c02180c0701c1c040101d940c40040000d11403600540382d0460307415402031803a02c55041509a140d03000100b003240d410f80248100410080e182c480c030050b403000d4000035940c1301d0905c41000a40310000e0040402a0706000c00c0140302d0f0105d0003510708481c0c2c40303180c83d90981c1c0e4480016000c81d400d1a0740580200f150340400c1050b075901c4100c03600840c0325809840c000b58942c42d803008107104203240c50317403c42c4202c41040200c002d0366002a2145008000060404510000504400d0304540c015000903855503c400140300b80d0000341d5801090600045151a10300031140c030166000400103030076000c6100c95041805050400b24810b034a04046556114000d9007001d000a40030703002d513203035666400c02080e080e543c800070040e00510002c0d05030040c1c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 931163857 1250 931162607 931162619
    0x63305070803012c0c09040e01020406020a020d061b0c0201030c0201062714072006040f0809060c0607031506030612020603071e050d050c0310031101030b0306090a020a0816 76
    0x2141c0112444101a039420341c070941d0222980c04d2180940e0210800300e80e110800310401058403640041d140080c0d204202c1044807a8001541c07003002a4161203a41c000160303804d0000040c0b48145030840101e07458a40d08503c1ca03070001c5042603051003601c041003c0358084004900701c9105000e032010404a245e01404c9003804008040b01001c92600c0c00314420030010322620050030140d489401080c00035660030b07819032203802410700802c2c20750010282d9190686031540c001041c1e41010b4504070000454403401d4441004603100600c10030b044502d941084100140206508410701a04841840c8046112486400f5040840e102d107401030503c02d441da000c000d1903620140600b800c0c8800f58a030800201c1100c6140704980d5219142d054482e190014170390142c83c0c00500c8a2200c074810002c01040c000302014802c19a50003816881c00d80c120180142c00a260003000c1683c50f00c030301000c022895000103061f8924502c2070b900004501d9950034040c3d82c0700c04400e036a903508401c2c1c1d4400d20203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 931165107 1250 931163857 931163879
    0x30a03081b040f0303170c0d0f110a0f0e0402070c0b0906040806011716081f0e1f11070302100504030c1a04110a05011b0606330507080301 61
    0x11420141c0d8006001ea0840180300c95225503c800001c20545000b0030070b041e00103030349400c03150801d040b03400d07245041000c45c500381c410503500350701c542d41c5c03003040317204221907640034070ba41c548420600d903a2401c1e43d50000e42890401c82c1120001032900d070042d40e00342054000e0700c00040e80801e622500d00d08100750020103400500700f00b40c021505020000c1c9030b0034100300050081184c0803060480c080d02c1c0c8800d80c2400c0302c0a005100940e02981c04005c568400518424140030074800d8100407090040000050180075016604a00c03607220100701e1240303640c4071415800300f14181001080700c010390001d042d0050b98005005070704a460030000e10215908881d40c07013072180c0b17400e075a0840380f81da425540500038000006048281d108000c104181005100549181201c241c01d546241c800024045800040040740719601040710008125403030304000050030060069107400307006541c500f540d40c80c0000c40042c094210988036010719004000b02c0381001e42080317100d0315682c03c020318030b02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 931166357 1250 931165107 931165111
    0x3160b09090411060f07050c031b0d0f06050c0a030608060702030a1209080a050d0506120d050c16080319050702060f0903100e010518060f0406181505010315050402030a0308 76
    0x80c4103024800816003543d50f50006010310b900e01c803017a80d200c1800d4180381d481d050700031450300d00940c00f42d10040d041542c0540c2d1865501000c460785480120f00b40b034a9000800b5400000303005a046c81c05000800d01c1600c042c20032244641c0e42084003654075080160743c0c1e41e0030341e00c02c0050b81080103501c54140c4101101e04001c50000c00108821505c0d0740c8941c0d841d402081c42c0c40c001280412a0800140540213072a00901e003107850b050744a00c10500103071201205051170050010016540303481f0003040c0a80001200040505400c0039601c1206903100d43c026607181c0c5a03a0b010020030703001240943c059030100c03a005083c080c1051006141108036a00c0300f05195458811982241c0c40c030300741c60003400308000ca80300021031705040c108103101080c0c007486001c40940d040b0700b0401003070120300005191310503045100481c0301d11030021120031400c0e0b4110081c02c0c003c40072080c08950103403900400e040300e1113080c005140c8112681b0324811031f01c00b650b00a505400c142c0810001c41c2c40343d1034090f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 931167607 1250 931166357 931166363
    0x509091e01061701110a0f0219031206050d050c09100806041109070908030d0b040902130b0301050117030d051b0a11060610020a1212140f0a150e07020307080d0b03160b090904 77
    0x36278102c4048070310b44c001d0443c0c102c114002003042c90340701c1010055009500040c0000c0d5841f0342c25026076907580362104044290700780200303041c00020300100c006000b1000249031090a6900c1d908042c01c0c1280b460341c12400c800c0c051510070f004180d62512039201e50742280d00f40c2000e98180000c24042d40090000e4405080e440f9840c0c150b10005652900345d200d0003400c0110002405a410074141425100c059000c41d9092102d101c4400711a03101100300c034203451040b000010103643d841044500f0014410491000020118501d414990414009404070004004441086c0d403a201040305124010744007000503007081c0040400942403000300f20b412883c80c10140d031300c41ca0190a090440340c4004032110300d01c800805110342e60000d1101943c2060108105204036080078410441484040c41001e030f40700c0c231050009481a04c20300c1555001684138019030b81e030b44800081c8001800b92018064030902a05000f1a00100440e60000485698503811800c1a40e240b0800c01c08020040007a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 931168857 1250 931167607 931167613
    0x9070c02010201200d060501180605030408070c120311010b100810051201090209090312130303020c120d0b03210a02030408010e1c17010509091e01061701110a0f02 72
    0x141c041c4403564070384500c0b41284101c4c055141c1801100c08016101941c0c0070314107201c44410300d80c0c00c190400c08a0011342d905070038265903a44035403814031018890385d000900341c4d6035256070216485101000401d091030290351020035481c0c040d0a00c6088968002c1402d038441200303801c0c000d5090060400301e500c40310341c2140180c219a1000400c0748184240ca222806075581c00c8004210724140000c140c21401071b0000b18200703190701803c0c2c003e0000161207071700000c10000803001018030903012664000308070025911120310501a1107070340e802540c10700701100d051090407400b82c103000803020070700320a00e5020380100c1d41156680055900641e91070045000400000c50056001d001d5030600d29880801000c000e04642c41c1002e15110704d040708810000803021800d68105c00075915410b44030101d68086c0b070b50716400401e52520080002d400841c40c0150138624401e001980301c40b0441d003440242c91f03451450311072201d00301c2d80206c41c66602c0382d40c00d00844022034416a9644c0d00283d443c011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 931170107 1250 931168857 931168871
    0x30601080702160803030601020d02010203010b07140f0d0503041208070c0b0a060314060702150c0405060a0c060e0c0f010c1e02011115011401050703121109040609060e06090609070c02010201 84
    0x140c59841d43c02a041054254000000c1c4a0075503810414105200c0d090f04c0210308650400303450444601c07407044c000e42000100c1c0c0714494a028140101d00c803c00300002211024001010060440e800468090f01d1107018070700894030341070013980068815000c5a544002ca26401d85c0d42310030030384002e014488230503034610010000a5940b01a00040189000100303107901c0e0251009141541c0601c1c1c00880c0410b69051100010148050b00d060381c070b0031203080e030b1250034580040320340303001e110005011681081c0c6980d00701038001c40c036012010004c1c2c0318201001c0390040152200035001d00004e000b500000a6140003251070000150300340d105240c91080749015404003407400000c1607901c0f00151030107004214a050440c0501100d0704c003802c100c0e0400070191009071850205107036040055440301d85803140481c0d040e049804107030005000300080b40d11261890010f01c4d07680075415aa00c24000030030200c3c9841101c551180100610565031075841c200b00321424000c518049041d5900e441ea = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 931171357 1250 931170107 931170133
    0x102090607110405130b0f0a2d061a1821071401020d0906050309011b05040e010f08030a200312190e25120c0f0e0c030601080702 57
    0x1041a5400b80e1403407001c440d201010081120806030940490b0950540d403d00000c6050f00c0f2540d0198004526500b01da072030f0041ca201428989014101451450b845004200001058950142c0e001c08080102a481f4944008001c448030006070100c03105026240141020741c11b860b48103400a4100f0114401181c00b20702d0150b0501402d0700c1c150051b030740c10310a83c2c07002c107001c000b1a10248000d0414405031117014000040b00d000303500421500000041c1c0c0c1344070035041010301100801c05c0340c0c0d02504100008090303801c54081c1c82c0740300240c20000a1804001d400110035908d400000c0d52418802c00c0c0107031164003101c0f1901c0e50b403110203018156860030a0026003100100c8201e820000d2903c5402226904101111f602519242007050011140001401d0030560080341c0c0003580159854203c1200b4116980001200300c00c0d420300c0c004000a4000010884a6200c1d9100c0f4103900ca042101d4070203401c4682003000181400002c04941c450341c0c0054010721680190f030440a4008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 931172607 1250 931171357 931171369
    0x9060a0207030909060b03010305150f0601030b18040c0611071a0702030a0c0b0a0f0f12051308040f0f0b0a0f030b041b0c030e01030605031b013c0f1b05010209 70
    0x1500800c0701c86c00100c01081807103018441c0c80401212501c4410305443c210340000717013080c40509050304056403044103100300d4480514049183e0703c0742c080310035030b403802d8506030071610380d54000c1d41c0000310650f405074401e40b000100390084d20f103501c200e03220100035400c0004032a000a482130768144100c080c00e20126400c0e0300140d000e0000d00542555070b0081041c040c1c410b0005400c007108000b4410f01d40401c10f9070020030040c003544808008603842d1076658071349240502490020300503040026000860f04070800d0310354112005450301145035a91818182c2243c0280d80c0d113036010544900c1e0800c0d48500c00e900042051600901c005402c80004030414000ca00d0b0203a0349001c182c0681102043c1031700000c5280c0720302c60074038003408000d0800d80403035140c1c40c0c001c0c0741ea12021421026003959a000708a031583c403075940f4a524101e6030400e5001c2034403000c00800031285140314110506034500c603034050700c0f0100031504c948c0c2a0b090f4205102025511068094840755405d01001289503111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 931173857 1250 931172607 931172609
    0x10902070507050d050c1507030512090304090c120c020c06040b03270d02120903150402060f0307360b0a0c0206030903040302041a0d030c051603121709060a020703090906 75
    0x40c3e00200b00841b04117003800140c80e048180800c3c0d044081c802d403400298000d04482840c05040c0e0b01c0117054541400741c42ca14011504580301160410844113019503001044032a10301701c2903000d1290310003030079081e6111045000b9854110340d08200078003101440344015a0002884424050b0a924000c19135909900c140c0040c0304540002148031440da5041080380d0360b42c455440d0303051500e0941000242c2d03c4040c022425030001039040003d003507645100940d03113200c1d401154030b030352803801d614010185503040b0651400c52605c0d0801d0300104a940800040001440414001c01800d1040711007440d08111546c0d030800640d042d1500043c0c4030500618060300310729000715200e6045104120a465a41581c002d0041e01204905a41d554039010755200d1500350418641c244030741d05083c7c0c2030040c04558a042030000140010400828038281a52020035503101000b030b40c41d001e03001c0040802030f15424895440407000c1270050405034010161540300781403050b4965982d0000b80159105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 931175107 1250 931173857 931173863
    0x206070c0e0f01030302010b0f030c01030e0c0a031103070801140420030d09090c1110050c040f0e04060b040b1e0a030b0933011404060806131b050108010902070507050d 74
    0x704004101701a0240945243da11040350100884e80020000c00d41d5500721401c2681090b846518140008909019184491002402502100b6140d0504044003900c40304228064421000002510b401c10301c130362048031100e0010b42c1d809807501d0b211000d80c03550440e0301015100a2800d0340c08160f808000c2007046a415031200e100c40c41c60710141100b1a246804000180105040c3d030300c21503000070500e0102480010b1000a81c0c0c0c480f0304040000d03000d5034000800021a040e8046854100e614400344182c0c810700d014007220904405100c1694810400790b41c0000000c00b80c2402c00440000b604281903001d045188440c1c0d0320307124000c281c0c0f8242d69000761070300a07241510b0b248105000350662042040c4071100c90724403040305400400014469640c002c0c0744130103c1c0120355640c0e00120000c142d280110307502030800410800035419a80412102c101c0500a0038100700c04680d8a80100c07401611107001e43c0e842d0050040107513100c00c2c2d045685000d2010089684e540782c3c403200c2c0e10540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 931176357 1250 931175107 931175131
    0x53a0b090106020a0309150c02032410030b040f0312020a08040b0f1b070512040306150503010b010f0e0f0a06020703060e160506070302010605030601170601050a030f0206070c0e 78
    0x10505210320500c041e00300104642159151401080d0040724403003c403600a1002c40650400f01011180b16a24100095050042104034071200d50314805103651045080190301c0310740c844100381001040d80d40320040400721000001004601c0801c0e5004615000e42010441701f003085054408907404440d901001c9a650400c0c00300384411002c1040e4881444c810b4000d01e82010400c81d01c8003440c00e0f80d2800c16400005503001001000d0082d007104c82c0e11181040c3e103941d268580314015003500b04a84407088160350001600745814020140d1070101a120f00d65094802c0d8001c4402403600c0b0010b540196011801c40400d4070740c400a03000600d02c680c080d0200500390702c1c1c41070556403101010161588215400e0304404880d4015404a46080301d0b040c2d540c2c069450103034007401155008a07031500840c2e000040c1d80c81c1082001504185010075940300d41c5c2c9402c01c06c150079405010144c106008261110010b040510007008841c1c0241c00c7e11226603a1020b400c0d140280841c2c000082d03403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 931177607 1250 931176357 931176371
    0x160302150c122b0c0903170405060409021c09020108070509060c060708190902100c0201110f0f0c0405040f02150c011b090806060f22090c0302180403053a 68
    0x180000c0491809a040403c1440756001ca00c0c0020166580c500028020030307001134203014000d070f82c0d0303084400800d40035280d951590303664031783d1000079000407151a0700642c0d04905240020b080b440703451596a816100d140068860150485a81d00044c90180d0024020841144108002c2110b07900c15444c45c0d48840443c50521003010f0400d1644044509040c01c1c05050001aa202400c0010b0760909241c64440901c85000481d500f6003280c0201d000b9000e00c801142c00b20310049805a0311201c51011501150403102c00d00c411260112000303004c28808846020042c80d001ca0b0496400000421440c1070015840909d07086030003402842c010401e0000c44000050307003206000000302800409490985070250100f4215034000c0c3e0742d14820300050304000031404110316070f840740008180d001c11031680903240041c8170791a1400181e01c241403081240c108104402d14442c842c5030304dea81e40742003140c984180314040424403000c100600383d06419240d2844110400385040c40a14004a460 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 931178857 1250 931177607 931177657
    0x90519050315010f050d0812040515010618050906010c02060315041104030807030c0c1203090305071e0311010504181b03020a02150a110307050c160302150c12 70
    0x1140c841c60040750b415410000401245548072800e1049910030740f0006451185460400f441d4032554984c40d0007840700e08248000d10400090f801c1c20852411f8807140a40d0720382500b540c504507801e4845e203980100031030074086410490b0718540c02c010103040c4202e000c6150341c00103500e5003045400201d29000744802e49082d15142c0981810360a403004424505811a10380780001d1095040140c03d1002c0340305548104802907041c90004c003150040540081c905190003400356240744400e9036588926900800d80f88000e484030500c1e80525101c0b0301c1500c1c610356514808000701d01102e414040284400298800305c141c402150030320641000445008200101e401c000c407506140c0304051041c083d566031140c0005242c4200c08504041c050569030744400c9001401000108074100342012082c4100c8580100c094030107418050184c1e00d1141902e460688012080c0c0700c00789d07001e0f001c00348220302c0c1803103080100320416840382520740d00303900000100c105610042d01506000300d560400120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 931180107 1250 931178857 931178863
    0x31207080709050a2d03020402030a0605010806060316120f020d1d0c10110a020312031e040b0c07050115060e01090603060506071712070e01030b100206160905190503 73
    0x143c00201c400f01d2400d4140b1841441d90500c07121650341000c0e130208113040c10311107400860002c503401002075545e07150035610030000d00140c1c070991b400f1901100100d0502d2030b10f1020341c3c1c0300e200342505c0040b0f420003c1c0c00c1203c4c00c0d6500c5468143d5555207503040c030100d0081d070004003a03100d03900e8000300d82500900801e0000890110500704280c00c16428000d840d5036084107080105001d1030030340c9800d20301211060074442d10000007940b41c401c05942071081103c1801540c4203c0114050282002c07a80f0b1051039080003c6070020141e050100c001b8003e00b03852005802e00754091800003540c0e50701440240e8010f901c03034010101080b8031045440d403640e800418003000d0140c27890140700d241d2421001c20010300880c0c000400d8074203100001c0c00c0c8ac5d20306030141c81706940404181c40f110b003400c09002e800301c0c1c030710469140007e00f0100d101c5480d04000c0b0900000700800e03801042c10f41e072002940d801c1725070b40807120010850903500000c0d0a54904031046d90303111942800f24844be10b000c0425107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 931181357 1250 931180107 931180109
    0xa0627061e1e050714270d1518121701090209060d090809090426070809210304061709070302030703061509050a0e100218010c05031207080709 63
    0x81e001d070420028070640700225902c190340c650040004680c640311213009445000310240c240741d41c0030300803460450a2040d9010f031003110214854a240700c403609424040009910fa0024001c40391000d0004019019544102090b2961034030031040d012981d07a43d00d81180b00c03880001c0000c0d4280d041da07030645814812290040c0700b420800c601e41180e500106106024420001e40003503a030b00300c03440a20510b0000c07501d0211008141e90481e18051800380000300244031200c04034040001c0709148513400c5011120750b44d070810400d13410308034818108107008050740e0709040040f50701c484030448200104081d001414582e00e900305840d40c036040e50000c22100030407071030305e44d4024a010005a1000b003001400d807500040f0106848090941d06200007020b58880348886240c18101301354032070140e02c8501e84820300c00c1039603140d4510400c80c8007680150f44800e50801ca0200307070b031159903000701201c07003400344a031b002d0b00d04000d2415114481080125500000329240703074100480540d10103040d034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 931182607 1250 931181357 931181411
    0x60301060e03060f1e100b121f030f0204090c05061b150112030c030302090604030609060e01051017010b0d0b0108070e09120a0c060603050c030d0503090a062706 71
    0x20494580000c60410042520460802824217070004c242c0441983c0f4071000517200c0032070ba5513aa220f0320094008140d1044a06410721101441c06503800c82d40b10000c0300031260810ac0700c600d0310b55941c007003000401c0007140442e03205401c4e090004440d12844043d100701c0c000403500d110b003001b00f0b02c070360303810700040780c00240c2240000e40040c030007040301c80140c8a880f03425203403049860442d41303002e0f8003c0c4581407012754400e802080000401080307412001160f071140005016405c183c0382e800382030355020340d20541000454401800300c02c03481407071100405111800851031000c1385d000f00f00303081100b00040d2880c00680d0014090800100896401015605442c440034a07040c40b2035501c0c1c062016208071075010004220316864807a620304400603070010000c0180650303a1501e40e90b03c51032074007014081d0007080101103203c0c3c004e10540b0312911760340c0c01608480d18190307035110042851226428101501d02c46409941021903c02d03040c01e8803078900040c00c1c0321440c842c01c600001c2c1461031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 931183857 1250 931182607 931182631
    0xe030604080301090e190c060906030e0a020f0301020d0204090603060507020706021c0e03060711060105040e071202010302070b0c030103030801090902030a12020c060f0919080a081305060301060e0306 88
    0x8400026905821a41100d40034000045c109445180c5e0600744001050006c0710266103041000074040401a803408650742500c03082000356035404181e00f40d84401c5051480754114000513405410107072040410751100800052516142c00c00c1c1c0012600160004600303540d8800c0f041c0200085807017410f0f004003c41c0001e080147c54034100079a070369020b8001c00303080c00f226003007620414002d0b0b0641d920000f0003410b031200340c600488020400403c030140020300b03100e444000070f4542014400c030f69500c2c549001400c0850b080011540422920320800c034100b507800c00038400400c0041c0d10940c041d40c405004c6e0381d40c0c1e514500b4000d00340001a0410f00c49940f40103281d0b40165000604032034039540c400400c0900d507182020507810a43c4c50301d889500f2481c00100e1410b85d51466004041c4040229068001d001d10030414900b5407900d40180361440d80701001890104008002410015126a031a20010f6464101003499500283d00c2000070a8401e601d0082e2442c040c06000d40c888041c0502c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 931185107 1250 931183857 931183861
    0x23130504020603070c1113090c090b030a081c020307022b0e0907030608010f020d05100602370b01081911060a0c0c1203080a090c0902030c09100207060e0306 69
    0x10b00d00e440054805030a100c02e485102c010020039522011400d00010482c139426000041d9010242a100900300c0f00340343c1c0d00102042010161103075510b1800b0140017040d040340266100001640140e00d62680c1040320040100c03a1081d07800190311880c0aa4040d1a04450605650350082c15881840058803002da90b104a1581e000c09150f010b040700f1030b8500c08580320b0400c25002402c41c0e4003c00100d50810785e02c6040b1500b00d4000b4005e040500c11704002c19070b02c60f1088071440c2c1c018028500180c10181c0c0c2110000e000d820071400750245100031120440c0210460184039242000c100e0783c0b090185d004008501c001d02000b0072120070b2124245900403507646076640400d8002e03482d40b04580210300b1410082c49180311031451a4852009410b140d240c10100804014905e02100029140300009025030380c940100308040d540040b103c04805d0070680014040c0d00000c086e8041014180646070842d0b031196009296100f8039005000343c01c1c00c0a4004121100303070386585e4060361003641 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 931186357 1250 931185107 931185109
    0x1a030f01021620030a061a03061b0c12030a091101081e0712020c0f0d05120402041d0d08070801140a09110403021e090604332313050402 60
    0x80400499102c035111181000b8071400d203c058000840b02c0f40c0501c1962824010001d06074000c074084080c403401c5904244940040540d156022112500c1d00c203d92aa008004d42c401005440002040c80030b480b00188144800542d607002154520f1419494039104e4040c401e8082d4400c60310102840c0c04071180c50704056010f00c0140c0084041c0c100e0007103c0000d61258411441c440700519000c0c0e0035591840c446aa5035903a42081c840101103000e84e1100018650084c0f007241c800c0325031451204919500d82d000c2000030508040080383c0726103000304841000600307000c041095486030300d802d0002e04010400a2041c58143c003d45000c4107007250004480e960a4610401c41d00304800100d440c180000150046009542c40207401000c10704c0101c0b00128404da0103188800c0681d0200050794030001084103440c0c60181818815031030821006541c691ba0002c0811100140d0b042c102c2940e6501840740c15042c003000300080c208210f03042600b13910784015a80ca542640ca1020b11083c14160 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 931187607 1250 931186357 931186387
    0x330105090d060b0307080309130c120c0c0b0708160203211803280816030e1e010e2506081504020d0f0b03060108100b060408011a030f0102 61
    0x3006148244a02101c5404100141c0c00503041d460f400b4064542c200c1d0b5514000c2d6480e00544200c0e489009a404c0018007030085104101c0c5a109554070300d01045200d00c1c58000920030040440100150500d42001080c4681c00e12406000c0302d64482006240c0300f3303205141e00d00340402c0c10086410801c00c40505132480a03c030700303841c00e0700d0403e86c0f0941c5404600460720300c0d4083c4507000500010881403041d40b032140c10720a00803003518a12400303450461046030074130400c031614000070540c06411540c1c98446d074080c40d40b40040004840a60140c00a00102154000100142c9a44980440032407420500c0112101e00503090b2a004920601c01c05482d841c0c264052901080110000221000c0056003a0b188602014004540e1120b465a03500081c00e1a10485030489040506034030b41c0f0f05000807598100c50940b0003070a10010400709400c01792030f0104111340d10034414440412900c0080c0301d000110000c3d030120b1040840da000600d420443c03c0101d003002f5034810310003182060316003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 931188857 1250 931187607 931187617
    0x60103080a0e0a120f031b0804031104090c0905220c09050903041a040e150a0e15040609050603010b010c0b0606030403050403082a01060f030213060e330105 69
    0xc2c0c2041c9501c09110004241943c602d42c1c400840008609803007028890070080d02043c880c080c1c1d4884041d100101040000040c1007140284011410031081020514081c04149603a00092002c51480141c5e200c980300c13060560010081c0650301c1c2c051003030100490003010201201141c200c0a17107140c903183c2d140002e62911800d9045511500000c3c044481030086030b000e0980461400c450441a180703120154001e40296001d0900401c00704105000280940105400090101c0c10507070030403034602074404020b0481c80051240d070b140761416030380d1401004082d00d00000000342910b00350f0f0806013035640d20b44c002418081c01450f40408500b003020382c1c50303101d5410b4404590320b8803076107400c503a0340c8541e80c005044990301040c400c0514204d0492058000c01d0301e80014102200c0d1003055080303c01520400b20304001c0a5010030050501800e0340c47c4942c10789100261312991040b84c40c4203040120744000c02640425100d1940520122064901c2400209202c48445201001030854820 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 931190107 1250 931188857 931188877
    0x801120c0504050603011e021809090d030c0e100c0b06010503040f0611160308060102060127240315060b090d083106030f0b060324060418050906010308 67
    0xf41c20029000e51000d401003505525881150003110711040000b900075000580c5030300000b400f00f80741d140180381400f001405103c00101800460100280035801401c00031560402d0160451034810b40c2e0b075403c841c14107042140d40360b03880c0601080c40e1155203928002c0069060080a10a102c081090f045001c80c015511a00014184501c01e0490751180568040c0321201600b95201d1000c0551004c0203070300940c0d081e002c0b1601c1c1d90300c0d0341d00083d4608080b081551040140400c02020b81e4240c0c0102501d803188901c0c9030700030f140c00110054404419001640c002107034841c0040d14028034801d4100900d05190001d04018140c2c1c0080c800340d01c690006803940d1030101c1c0250b40610860150312041f04850340c000842d49400b01d4105402d2040d100381c81c040f034509106c030380d180005802424142c4000078a03452440c0d03140480030b8892000710040343c0c48038501c0806c43c1d0326510744d80018405484540241041c500a809118080e206c0040c00341415820010041000404003001d0312007440c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 931191357 1250 931190107 931190111
    0xf070c05030406050d153f060e0c221d030409020301050a06170c0d0213080f0d09120b10080709050a0b030d0e01050c0c040216060b03340519060801120c0504 69
    0x50303440c00030b101d84c1d0207410031087e002c0c80b01c0d4a01d408001080e07200f02c203541100710503980040311f05020403800d0100701e01c8076014024074a441401c1a01d00381e2007501a10b10140131610054054240b0390300d1500709401081d00c0a03030001c018041440d14448101c0244000c1c5400161425424851515140081d14680942e00d003c02c041c4064440f46d01654a040801ca4dc00546240d90350101b551f0b40702c1c3c12030080400d01072542114400d034800d00030a4251291128000c030000041d5031881c0401c2401844643c1c00442001c0210302c0340818804640148203204000c266414140701910460b162140e0143c880c0c0d00204102c26402e03040400324094040900f80203407034880a200c05400c200c0c80d060144c0d4084c0c4009600c0b142c106400c1222003810340550010888a9142001d15036920360f00112044401d00d00a840848420f41a170540c04044694203051000da5440e0080b403400c600c901c0c0101110314042e039040c00389a50104d800c07801080d0713048001745a0800754840802000c007a00695000303035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 931192607 1250 931191357 931191419
    0x120f08030c0403080c010b102309031e0708100e100e01021c051527060d0b07050703110105100302061608030c04150302040b030f070c05030406050d15 66
    0x11040310700365002503400080240d61501e0302c000b464000c2034840303000c07032060166029080f1001e2240018402801c268401507a103451500807443c4503800450441e07a05115054a0744103080c055103003512140c042d60010075055080064443c100608488100300d12494181024040d8400250100d0700f41c049010000e1000510030301d040c06071103280816050840001528090041c6561299108001c055602188002d200041084400c0040307030303810072001c00b01c0308400d41e8640c4402990f08204000e0028114100603503c00d440b0800440301140402c40110f038150a0540049441c2c44602c443e1000f044280350120480c0e035800d065000c081d01900c000316144103540b10301400c0302c11081d000943c094503441d100700e000c0b0443d4800e0080340950a1480000d8900c03074081d00039a41520251a445421a0f558a06041242c080286000d0401604d40d203010081a0144000d0003c1c01e0f0b5035031a259141d0740600c80509030780140c1088000346100b80010898100314402800c0a01d4260300c00443d45 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 931193857 1250 931192607 931192621
    0x50705011805040e1c1805060c03070326040309030b1e011203020f07141002060610030b0f040c05090406140d0b100f140f2409060c01050405010204090501120f0803 72
    0x40384617500000d0702240c2c00085003007581003007100118091104009106545880c180300250040700c0780318446500c148501f10009011700281220085120b1001e150101c1c90301e80507207089415102940070030140d140610a00c50420f54582d07201d02c84168808050030000700c4100e9118051141c409031001d90034294007014405c4c4001c1c4448002d1404940a81d81c440e1402c1101d04441049035105c1d882c000ca0500206001103202c0703114a0004043c20031020414406034058007074440320b0b5a001c0402140502c0d81e0f95180b00f801800012a581c51713488107002418001126003a41103e0500320134120792122030342d00c102c2410880d6900103080d01464075069004520a200c50300548025600c510010030030701c1c0c0d541d21052280d042280ea000c1300300904414403241c03000c11200032603183c183e220680c86c2d00e40e14100a010500c00503180c54900603030043d0755800c41c0e0059070304940d90703500060b080040c00c0450140074090400d100c4251980d590556400c071410a640d18020810782020001500b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 931195107 1250 931193857 931193863
    0x6150901110708011b080403050f031510020607140403052112010b090a0609051011070b0424020319030c1404030f12180303030b0402130803030103050705011805040e 73
    0x581e052920842e040203480d19040c5019200d004584030402040b0000380c0001e0384250301460081303416459642c0b07086504880081694001000218804032850b600a40741e01d49a070315030515415940a003006080c4010002c0150002c01000d460310301051009102080d07003c02c482403600c0200f03405035200311800e0a0384c42e00e4002c940000c024100241d0002944032481c0c0002c1084180850301e8904898881c074094801e052603000c0d03d80c010603102500d40b000e0b0f00817103a0030160880c000c100d492842e600c85e000305172948542c00c51680318420000c3c1c0a40742200304205118501d140c005181030082058441d03c11314a44480c07801095118803040140c070b40180d0090702c85003141181650740c9c6403241410030034207910030011103461400c0050180c01c83d204083d0750021f503a0400e000003245155840031000780c1018032806c3e45c016802c02c001404da0000c0c48010000344582c0300515100d41c5103051490034a09103501081c1401803551003061103070610300c4c1c254107523001113a0000707071501c01c1c0852070701d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 931196357 1250 931195107 931195127
    0x91606090501050304020d0f080703080603031201140a03051f0f09111e03060106030203090d0f080601030f0b06070c050909031602042c03041e0b040e0c0f0d0609050c0306150901 78
    0x104e16000e441c441c88c00e0080203801028400e009864046040d204c0105141d528441c890014000d8400d2170f0042c064400c078010300340c2c81e802004044560050301c985585080c01065014451000c079100303180311070340c44140140c900c0a0101c0d4410025900c0744d0b103030541501c0007825000c0c42058041d0011000d0780000e408410101000f60880340c5568413a00702030001d52050f80e20202902c246442010411721410f5851490f0030607a9408025403203490064010f44030002003952041d80f5041901d615458080113030100034014080c0d00c185503c1d00c018032032401c0c00980760045076001000402d216044c03080144441d103505170350008a600034048601c40c100b15141480518115006056092450000181c800c1c1c4203070184410400c1c0002aa05c2e050070396510902010000903c410000da4201c140020b84c80704e501d034602c1e46070505140c2c4844180d400305140b002c203a9581d0364113001030429485803a5110407038881d2185503082c4080006c050480c4042c04624445000601010991207003400f50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 931197607 1250 931196357 931196363
    0x30e070b0307020610050303070309031524060807050c0c010c0c0905040606031209050108160212030103030906080a0c05090409151505030f030a05121017010203091606090501050304020d 82
    0x9440b42000c801c000e40300e41090f50401c1c01c44c0c10707407640400c05280110441d04825410388030403440503c0c55441c4041010b40c3e051015005558440060124900400c0d8034000640c1d900349a00daa42401c00103440c134070025103a101042030500004d045c0c04800100e50800001c00d00308004a50b05a10b07010170443d420341c1041d02c040b8140420310041100c560003100940c2e100e0440c44d0000780c1c1001d411602c3c0034952048a00082c9142c000c42c13298090300d0800807240340c0e02c0c4140c881c0558000305c070100740d50080e8001ca002035a03100042042ca43d0081c0e100da042000ae21050088140c540710091850107011101c3d4825540c0341000004c0248220002c51140e54017482440502015036104d410390005120b800c0c001d005241c200c034114080072044941e407a149440d05814150548205403e1081c000c122554441c240080450070300c001860304510120150000743e56407500425075401c20b03809001c0103079660384104040c0b0151390000f110405594084c0380841d200d548a00004007074002c1c035140030f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 931198857 1250 931197607 931197629
    0x30f0c020a1a07020f12031b01020706050c031e0c040b3402010e03121e12161704080a050d150e040201140c060402060d0f15290406030e07 61
    0x65000b11011000340182600842d1201c100710032031750070b0050951000c40304010a0b0020440c0e00c030502010600b0502c1c00300400c0c00181440910f0b9180310840da400d85560b4950031010041001d64841c003880902014074059145195061105100c88180514081c40c002c3c504040340042c4000110481e042c2e4400c0f000c80540b418a580e0368054101e550b41c20016070000b118810219940d00f400215100710420820007145410764030b034040403a001d51114544c070300110070041082c2240340107248600030035000d4031003070105079a6100a054506200c0c1c5031050000503c0070403000c02c100b8800e4811545503803c2c565681c0002d40d0300b4100030310b059601e000d010041240e021039040c7d41010714601c102d10030b880799030003000902c03c2c00d03506004003002402c0a5018a0010340103081050140000844180c00030401c222100ca0f5841540c1034a924102d11291002c000c00410484407a8078850855a01542030b5038a0281600c03407141c4030b01c1c001e001c1032580f5000001031101040010000070503451031b02c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 931200107 1250 931198857 931198889
    0x5060c0f0a030e030d021b0402070311070e15091302090a0e120c06010e0919020d061a04051506070605090a0b0403030609062c071107080105011e03030f0c020a 70
    0x10242900d40c942d50f403240644984802d045a0500024044a03031000d03a10201050905080422020350b1003104102c040001c0c12149054100c03042100c0b1001e40032441c2414920b241a5180b203680c0c06101c1c200c40c1c410303075030754050001d010480e5510a20568054460040c2503071808618005059420080d0f00c1d0342c45141f103070a2036482d0301009051000700c0d49040e05c41c03907682c5035135000c0000016100002d10790030400307507824aa907010b02c2c1200c0207480034000c002c00d0140d0b621901d080f550b4240e101c03806030980c035103003240e603260500c42e61b58001c0c81c0d4521101e4904260300450494080c040700203081640d1640401c200401c10000c0001c1194042d030195031a2406180040c00307420680321300084e40d8101200401c038089031070540c00707462505070010700341c0c2083c00103451078105001d803240c1d0601c00d00c2d11a4078070340c120a01c10440600310703440010034154507180110440895a8008034080043d28000b840069070081207107181468600e0f05140c3e07035000340001121007502d54000c0a01c204a119 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 931201357 1250 931200107 931200113
    0x12060506071b0515030a0f0501180c23120106081909020315090a0506010e131b0b0a05120a022104110303070b011815051002071a1b03090a05060c0f0a 66
    0x4c01075204880100040c0700700000107800209031030302030148900403004051002041201d950051310036940e145014001c000c18000f160207480c581e032312551602800051000388146a48100c00d0051580380780c96180d605d07009104032600165400c0341402d5689540c2504250740d8100511803030a13810440018280c01e007540350b0307a071320320401c58116a43d01803d000040d90107221071003103200b1401c5554191000e0f865985081d142c0c008440c4201540c01940400301d01166980301820034600c464a80310703941c0000d60000070f03020780000c2401300080d00401c0303490a032107a003070b103821000d04144020015070388451130071803207030107001c1c003915014840400c80790103001038070082c107042302e2000588151100744c00d840c3c00c6c1510300032402c0841d46d070918a0208a281030074403c41848554910586080c6611035503070180000d03c0030130b8030381000408183c0101455900c040f00c80e14803401d1000790310303020005000c924865185c1c0304241c0710b1940443c0b0a403e0700320500424452101300030030307220507a507286 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 931202607 1250 931201357 931201399
    0x6050c040509010f03050a060c020f06040b24030307020f030a0b0f0709080309091503070b1c06051c021c050102030a0608010b240708041d060112060506071b05 70
    0x101c126803140c25202d00004818401101c840c050b0380c0c0007000b1f0170742051a503c03084083c11a14646c0011407190160300381540ba01882540c7c0198403c0c0a0200e984c02e14000700c1d00c40e0100c404101100310b42c2103101600e655000001c44121581c1a11484000c41a41c00000d04000441e0310140903580048108890007440700100341c0b08100e582c8550b01e1198640852599a0041070f1440c0c0d00003503a1008940c3c3e210160380b9154400000034100c1da0b105403036003840138598203d8075800144142002980b8029030680c014000600019074128803815415500283c0104284001034090b50441102100d0a5030207008040f00300c1e0024029560303802c0c9101e00e080182480e100700241755203003101802440c90100007958124082a10400c0044002005e0a0707a0b035020440403110501c0420000422a0014504580c1c0d800400078810b07891030501e0005d0038250324000c0000e07066240c50803d220350f6807a08280e40540750071a0b81d4079440034407030044007081d14841d00308a51110748259012401d000170 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 931203857 1250 931202607 931202609
    0x3140a200d1e0203070522050301020d090215070c0e150a120c0e0c0f032e031b0b1602030a060f0b040f051e04060204030614070f020d1d0a0306050c04 66
    0x800e04182020540e148020204d01040d50b00c0d81c00203104000c02c880e00c001850300c1c2e10038a98202c1090410f1642c8400280c01c99116680c400d00568440501105521b020000411218034500459143c1012f070350300e07000c200a030740c01628082c0d24a280070030309404188044508481002c1c0c1110301031a180c000907562043e00720710448464600c3c100103d1002660700d401805605981000c900303207986070019011a400c02004081c5501c3c115042000841041803030401a04940c00840d00d01400c5040c0204995480d0061204400700042d041020703151481c121005204042c502000e090368510000e0300b00800320320003402460030301000c0322018416512a03042c2003800c5a0801032003036a5102c0205031402200e0425a40340806400f0036115805025541d1241c8100c0005240c61345980e030341c10031200d021901910340c00c4201c04110b1600d8000385400100c400c80d000410b021211502e00410940152165440d414040c0400085586800400801a6038000007d000d18035110541e0a620781003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 931205107 1250 931203857 931203881
    0x81303110d0c061d2a0a09050711031317030909181e0307020103051305060a0b10020109020a061b0803181c023c060403030c03140a200d 60
    0x58800000d2450764581a100580c070300d400701402c525520707000c40d45c00c00d4009101c5012191952011010181e40ea12046000751a40c400300244c1800c100100501001d903015401010b9030040100511348851030f43c61200300c8160b45001c14104000889903400d50003684411908481d00105009038140c0040c001c003040c4115404aa51814012070950380d1400c0c1131103101210b030000c1250034055442500300691040039441c520b1001401a902d076494401d08441c0d0011075651202400781503d00f0a0b0301850f103985501c0207220741c2d01540c000600d09816445500f06008401d036440300f00b04000081583c0c02604801415144e24200ea50352800807803500542c20140510319000001130b80984403042c1201c01da83c0140140c54a404450a04800e60094100701704038000058400c00000c80d08004c4840c00300c8003808a40c28145800b8080d91001c802400c240760625030812020440e0000c1e246d800010074501040d00c0150001c90f074482003810000d210b528a00040c92a501d100d00d800c50450360741 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 931206357 1250 931205107 931205111
    0x907030807080f1b0f1c080f0709030507060203070c06090e0f090c03031611010816181512060918030c150c08090f061306240f080c060307081303110d0c06 68
    0x6e1035800401840c2080c040400407039460ba0201345490101c451440e0b00c038040e41030a1203200e440e0f81310035182686a030b11020040e440002c908042180c88080c1100928483c2480807070700707040c011001701c9004014601200400000005400c407802000714a1700c0d0040541541e41c0c445105040c86000d5201c84410784100704c030800480e58951080340840d1260f04100e00c00111354956040072105209a0181072005016100d000724510800c00c54014000c03106403140078080200b0402ca2081d5149036000c650281d2030301c80032030041c0d40410b901c00c4402c0d40c50310f80380c00b26048910f8040700c2e08082082e400c00b1186001e0544000940201005008084400448440d42d03462620310356540c5046850700c072074401118602c030000387c00740c106454514803040910804040c3c244241c1c008262644159024100050204100718041c884001510313400d0354058910314008101a22030203000c1c00d290225004090901c0a252094101c640c81030b031040c007038481c1007a042c03d00600010154105540c400c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 931207607 1250 931206357 931206373
    0x331e08010b0609030706110c03101b020c0102100f0615090305060c19080c07060c050409060f0510080408160b181c05180312040e0907030807080f1b0f 66
    0x11424809031a07502800130010f00c02281040c04c1110348100b1408511080d10480c144280d20740e50078054071000f40111040040c400d280d100c24101c50b54100075100056400040700300141e641d010400c20b00c1c3d07100100000c0344080c003003244070005080350b0b0700c414140100301d5100004294440c80b444100c030301460468900340c940380082d03941c03072283c14480c06055901d00c0c005562203020f0b00d0110360110341c101d1540c0c18141103403603040a0b1081d150400001580029090103498018481c480161481e1031048054074206004107207041d160781d0f0200c052003204d42c0090308001c0c00b841203c5020b41c80310b410740b500008503e04442050402e4900c074042e02005800b04d01c40404c006148000e54031a4840310001a070340e803c0c10b45442c1e01c006c400b0101104000c085c400710361420000d0a150120980303495a0702d501d4064003c403c4a40500190540e400072002000031900b00c0b002d035845c03560810906642d94070b00304d0190600c0d01c108440e00e0700c140911004261071000200e405610740080c107095820304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 931208857 1250 931207607 931207609
    0x5070201110c101a0d110a23090c04030c080312010b0702030303060d05070f080601091d07060f0c061107020f0301022704060302030f0d0909331e08010b 67
    0x50300802c81882503da1092450810f125403d400010301190007843c100481c500d5900800c046030b22122003540d521045028105950070002c800b4001040208000c040003c014541c810024412020091066a904000c90310826030308044034015035100d1400c541e280c2e9120b0009031640c20107005e070040c002080000040f10014082202c0c00c00754000c1c0618907668502c0100011603907801e03404d070755922602c0e402043e0001d5500c41d01c0041c055220060011b50b250031511b00c19903441d148221200b09160303c1a1140500c00113800055410754201183c00a100340d030704403031740d4103001c0024058900700745400741c04914030001002094000d841e01000d034981d480130706080c0d208140c0d925850a02c00d41001b40c41c2c0000003890704500300001c0011840c150b0782c3d00000e107000c006050b2508a50003106042d0001604185204020700d0105402c0c0b007288800711403000c035019030345150b900900b070404880c801d43c1740c0c80001602800800c0229410074038030300c610301003021050040e1f960541c6031400d00401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 931210107 1250 931208857 931208891
    0x206010e060d02061c150603061a0c1e10110a02160302060a030f0e060708160c052e06030c0611010203060a210f0609020a0509060a0e130c0905070201 66
    0xc1903802800d10340c03601a03000b400107590384401e600c1c5d800382e0b69079904420309400d034200700c03100604050390040b65141c20301540c1000f041d8100c40c842a60074081241d94100040802c6c03c00d805c14424171004e0150f0b540008090400c1c1e81d640307280d103d0600c0d1002c600070026000e0058850080070342e0071560ba462441e0405103c00f4101e002c081c0d4402c20038411050454841d030001c0d02900400e040205d1514282c030449482c00d40d05a61400c0814150000c001d039110b50304c007105400060300e140040540c003554a078140c9804004036201c402c0c400480d140c1c5100c0315481e880f00401c1c8240c880401031961340b070802207050700e19805424001104100d000c1c51682e414000c0c1d0307006000c0104840b01240c5813003100d20300e01c1c51405100014002c0d02c5014008208501c07801051540103000201d8a0783d05881041403890f0303550005071044040030f040c4501350300c85120800c142c400140c02040340340c0b5107440c102c4200c90031160040c0014803a000105036608103800090040440350002c1c400010840c80f5044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 931211357 1250 931210107 931210129
    0x3030a080a0e010b0a090c1103030c0906070303061e06030614060f0c120f040e0135011107050304091431083c041403070f060206010e06 60
    0x202004040751003803031154046540814084000a02400d6a00200d08060119400051384603035078004071401c150400d80880580c420701c0c01841c51441d07c03400c20500c80c002e403a40e1070b015100100780b10003010300030f40c0650042c2941d0700c00940a00d00d20704010030b9280050007640700107410090005615080d4000700003105000030705180c10302c1100c85c00480150400490b031490382c4144e070000c0f00d140c41c4c0040101881c510803018166110306040300e2a401c4901a4088440c00f10450101410a40d103036144401d241c0300c001a5032803000c44420040d01400c20002e00e80f0484100103820410424000020b0003200e0f2403050a20a10b20080300350400d4000c103d0303400c90b80c484039a1070310303c410034042c0900c0041503004541c0c0a00c40c280c3d455542c00b603008041e400c5e240c544000140754a03448001c51900081501030211010b07048540f007001c000340220722880913851000c2c0080601542c09008074400341840b030071003144140d618072001355a003c2c01c0c0301e00c0070540c9218011920609107071071408 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 931212607 1250 931211357 931211377
    0x1111801090e191407090509100e0702030301031e030909090c0f0b2203020105030601210939090905030d02030708010312081311030c040c020f0c0402030f130203030d061d060303 78
    0x100511f01014028581d800501c10349041c0c000100214499203582400b9001c4c4495600461b220f40c11071902404001c00c1032000d10441d40f0502003400041d5002c2202c1d01034508a81d00402c1c0d036140c034034041c141840d41c0c1d0011240840543c001091840e450b101601002c2640d0341145134400ca0903402644400140c04040c1c00508204005415940505403080036944800d10b400200d085030b2500790100c0301c1c1d16000321142c501c90703c048201e07513101d220065607003090365448448010b421034510b210f440040c13084491058690f101181401f00500556041a03441d0b44190360f2440c206100a000003401d010444000054840300c04859104900301403042038110001030001d03041303896002249481900c25585489400c090415030385442c0144000360101e1b4000b000264042c06807942410342515405005520500c00c100e405501030320b8807504908250b8020070401454000709080d407280a0f00ea01d001c2f42000c200290a0190414100380b0a00c240710645a5403a0301c41059100d100d100401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 931213857 1250 931212607 931212617
    0x7030f02041421010e03030402040f0c02210409020f221406130b120f090a110603041707110405010506070f1209081002091201111801090e191407 64
    0x11022401d180320810b002c000320096030706080c411294624217440c540d00a901c01e43d08003009020460510b07008001c9105400d58090080c001800402980c81121002903141e8081f003030034441c18044403100311400760041d80410b544d112842a69001d071584000131450020014107115a480034000d4000025240840f582c10f403620401c0d42009100d800480521035482203da03c0001d9410a11004002e0300c07075002e0380c2041030320300249204825138008016100c990880c140d41d4000600380c1c00244410f000840e03d842c3c4a0b2074904080352842c0804a40d966030000005100003030088800c0341001e040e008850502071aa01e42040c0502070140400040092030a40c941600091440c00e182034100171740d10b4440b5000369603181007490b0400c05108a1701d2141d00003840005400d100c5482c1014406102c002d006005001820031114803d0b00c00c0c890350f41c1c0e41c2c61800d103441c1e8400e40440005125503003480e18541481c0078204050280d101001e08054a0060740100e02031240c131a0600c144469110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 931215107 1250 931213857 931213889
    0x80910050f010e0c12070c0311070b070f0602090a0f030b0703090b0103020603091c05090405090604030f1103160b0109050f0105210a0605010306092604050d0203011506050307030f0204 81
    0x281d042e04003c00b03010f40300c000c8810711032000d032250601c0e10648224070594507807800110354140a04551501d2641102d2034200c3c05040c0080c0c1d400e54102d6210700da01240d82a0490f0046c03c10f6802806840f480c541d109208100c00205550781c800c90000356401007040c90301c0307600e0b480e0084d000c560100e8402403042103c0b20040015180c11009168446411420b682c030640034404143c0926030071581e400003041c2d0100b10240c0606062180070703400400c0c4401058182081c1e00c0241541708000300341810000c603042c031000c14880c1482a00d100d2182c9443e00000e5804501d06203041c0c500901800d01c0592030400021040103403000700a0496101500702a03002c02c000b81c20341c0c40e00038804030780c111602c203204102001516a02c1840e0095009410010701d80420f403604c0110040c0681d4900384083c000c030840c4004506d020200d404540048076969285605440401c0c00360100c040e1030036007500c48100018080790000c000f0340c0b0034080ca80d0b00700054015100010120701850240c5a510032903000707 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 931216357 1250 931215107 931215119
    0x1b0206070201030b090103150f0902152101030f060c05030610030f1107050a0c06110607030b0d3c03090302240f0a080c03010e34080910050f01 63
    0x8228550040c58041031a029100114900d0ba00c00e900448000c0f41003c407910900b8409e00ca904450b0301000c0040c8441d030b400e1340004061341000240c16800b4040014140d00d000b4400f110350001da1180d1484030800c0da581c2c14842c0856040b500305036425401c18484038001845076003140d11404000300352009098151400b2001040b0444c1103205043da140c2c1d100c0c442c10007450107001c0840c882c1005028910f1070703140551801140e503104600348002182c03100a6814045903150303000d403041c580000d80002c00400603402071241b0b040a032810600c10005980b0744015200e01803c1e0b141d024140c401e00c412601441c141f010305c20005000034000350018401494000003d50441c000c803446403a82450021003e181a408a40c40070726219002618203002c5412858035540440641d111074159807520300c20794006ca000405007458008001c400c010381e4184900c149095030318002c0b044640003452080500300c0801690300c8100c44c8103101d00703444540500d004803441410581c0d02036060780d103000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 931217607 1250 931216357 931216369
    0x5040b130311120d15060507171c020d0b030c03070b18061309060506132904080708060f0403091205010f050703050103021f020705010c2307080d1b02 66
    0xe007102004404965812085030800121680e24400c1c940b140da54620701c0c800300202c8000c64484004002021010000540c21600391281c0e160031004040761200030390000d260318413400b80c0390700c46440950b074480001c01e5280c2c05800040c03a03203407081180040c00e104259440c094104103075030640c410b02b024803155030341801600000c4522801c141c55034504100040e0203401c0b200f041d1908030103201042081d100b5a0060720004e10003a074029280000c0080039055100071030095900c10300602c0381e441d15502d0007882c0410041032110301291501c0d15500043e40310300c032a101d0740ea040e205800101e00c61041c0b80c4480e9014036031544624405520708003007404a00f582071025140c0d55030340c00020200c1506401814490a580c2c0d80015847d0704502c1045041c03062003000105404075401001c2805400058401c10f940302402d040301c102c2d6131450030030140703214900e00b55514482c2003c2c0d104240e40005107581564102d000303403403a0350740d5068101c801c030702e5004c03031200100e4043d8000c074050309001d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 931218857 1250 931217607 931217641
    0xd0c02070302090a0c1407111005130b091e030d0807090b0706050610020a0201080c2b050906090d020a020d080f1209010e160905090109021305070e0405040b 69
    0x160056814040c0e80c0c0e0006510300d80102c0f020840a501c507170780444110f030300007070001c41010810754150600545480700300100741d036081020b0140e580b0142d481800c44c080e83c26102c0180340c807842000a1500d461501016403c25000e0078000c51341d20268000391142c0751382a0b5151580640200400d048814080314107890103840d803000e0145a043c040b5101d011140101001ca015a0005c00c241c1003900a0124800e0000002c40c11504629011070043c1e038040d0400303030071026410001c0d8640c1007450308a000040301e50b88200030030700b80c1d4916000d40d80c540c0d0000351240a000e421385503255101d0805a848200e45c20512006030800218000103191000e080f004045c040c0c17402c5401d107543d0314141e00060b4842c05075044105846420401c01e05801d0048006480040303000d0080004d1955043c64140205d01406460365290f0b0001042c0b1030b03003540300a046980003411348047d01401050380c4002d09058462030009940c40c841c0c2d01440c03d09010703860040b688440013800c555200300c00c0170101c2080c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 931220107 1250 931218857 931218881
    0x901080c0a20060603150402102102070b0907060801180908070605070c12020706090e090c0a03030503010f0b04120b0a14091e1902190e0a1a0103110d 66
    0x241c8403440c0b0061100c1c4100b221800c41c860040020342481400c00d454441155001c0c84404220700030000142c60342d03e40c103d05030699051034400840103009850100c1000041c00c00d04510115500c8140301409007018056800b440696040c16103817402211610b10034051034071450301281c401c480d07032901c0350700c40705c1c655001e1000242484841e43c2d680c01038510554a4a002403021214030040c4030220a000d07007102614001003801915180c40070703000310b009118910b144102c010000e0300003a002d00c900c159044005002c1c1101c40d449140241241c2c0080c024581b030904031260108041c0c5c044421107042d50010f442401f00e00c81544e69403c6030710001841c0006403074958120036010005160f030a40035540005c0035260382c000003066024410b4202c003510f03500da4840d130710540d100e01030f07030301c40028264060b91000c03040300101042400801d5103a215202c2c902e80d130802c0001c01040c4d0790100b42440664203001c091215058011000e81d2190130000d801e03544200701c503035100c0712194071449440c21 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 931221357 1250 931220107 931220117
    0x1e030103211202070b01081c08150609060d1e0213030602090d02090705030603010f05010e0103020d050321070e0301090b062103071a0f1005010c172106060901080c0a 73
    0x20300440e042c00380d030010f203011281c802c002070050100c5081801810701d0300c0c08460f044180f8100c880002401c0100c080c025015030460030170014210780714101144c03504200580001d64505044e1802801040c502010303211410078501d0103d0b500304213000b1030b07601007020049104c1c140e0458496000070340c404064176500042989000d40140c40f003900d01c5101d401c0d81c0e2610344d240d00d420010705007920149840403001618200040c050042c02d200e61905690701610b1f6101c42d41035030f00d800c2d8030b10320030600c2041c4207034901580c00d0003640303025080f54411364540d51900e0340084084d0a0600307035121480003c020041200002d50359050000391500601840c000c0f513250110510010380c02c50340111002d0b075103410301c0b89200a5003400140507580244c0040e07400e00b40c51912802c0324040b40064000c0b141005650f10317183c000d001c41c80811207101ca80d801c0ca800c4d610418070603031130f496030341e00b034880300c0102c41040020782036161001c182e48101f00103071244001681c2c3c4074490361281d4401c042c0301042c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 931222607 1250 931221357 931221377
    0x1c020f0a2006160c1e12050708190507080c0d020c0a03110904060b040923030a09060518123703031e0221010b04050d020d0c1a1e03010321 61
    0x141d8550505001d150032440604901505041c00c1e5100c1b024070b914881400000c1000d5800204c821048981020844c5008400300710001c808444030711a060340540000c2002c00c100c1030040c0085080514030403550215a20411580e00703100908034684000780003100700c040c068002c0c3c00d200055584c1710703124210004100c5a00e40004044810200c020381e110b0380707045a00441d843e20b0810850f010341c04040150705004208d807000301410014024a01040701c003141c440c90a2081c059040c0102c0302c000c00e80910f8000070b00b10f00d6551001000c0384050400c80c9844910951748800b1070b901c90030403840502007407079069103083e00584200512034003c02c940b0010714404142901c081c0019050019580b5060564007415207580081a040060804020401006199240092411403a40c142d410b4143c0c50075605101c030302c02c81c45920441c081c3c000b4624040c030820414004003940c1c01110596404c41d550864844801e01090000801050b4509c20815440d00120a216000000c91404520070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 931223857 1250 931222607 931222613
    0x31302030c090c09030705040b0d080d0e0604120201050a09051e0f0601080c0a060906050322020a0303020d030e120d02130801060b1305030d141c020f0a2006160c 71
    0x100c048a03c16034020021822840916081c8103030310082600300c4043c030030f081000000401c1a08940c1d402088d002d07001550005101d01078000342160781c140800c3e00c9440c546418000d0405401c1c01c402c5005520700300005410780c000e0300c248031615811200805c12001030380710342c0014051100042c503843c403921510300c92440d0708000d502c0c060100b11016000300e0010b081441008082600b041c42805900d8030b007844907551200c10323243d2007048000340c1e071403120b141b11207162214841d10019400914501000c4107140e00015030507110162660204402c240423841c5e0b0740c0303440c4651070b03800346680100700446040305e042c0c029000d00840b042980012681d40c00300d10382141c0060b48030801c0e581d030106500418102a07440d141c002c01c0300758091b2192002214008041a2482814030102e89010070b0303802a60035800710b040c0340c283c0d034803008640d90120510746107003a40050110100091580032689141d09080c4100715060421200402040d00d90450386513000140c20310f8002003060a041c1e42000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 931225107 1250 931223857 931223869
    0x31501030e0c0a03060b0a0501260403050c010e06041509031b060b031605010906031103161806090302030f01020f1204050a02060403080714030c030a1b0c0b03180111031302030c 78
    0x540c8036017000244078004000340810022a54042030510065400d0a070050303400c804240700e01c103070300b200c1041d1075074039440d09031028000c035176124019620341482d00c00c9404d00060418022030044e1010f844003c0c51442000c142c41d881c0d0303801000204000c0072908103070352010051201e544961008141302040002003850030403e0200f103140000f20280030001341d40c101e08a0805002945000d010b15004a0803800091101070552001065105014001a441070b100140c4c030225a1900b40321407a600d01c401070140e41c09000a074441d019840b481e42c0d125105208581a003240700141e241800d46490b1100c05411008006444e5401020603031801a510100204065071090200316118a40d505100521041041c09211140d00401043d005000000143c170603400b00c0d03103400e00500c021030b01c0c0041c0b2003400c2e9034006d0141c0d9a0081c040b0b10400d179030000d07512411020540c16100c0c0c802884250a850a5a1416240340d03405c1020030610b04c00c0c003107101083c43c00a4203e4841403154408500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 931226357 1250 931225107 931225109
    0x30f032d07030506010215070507060e1009050c0a031e0606080105070809150c0921010e0a0b16080103150e0d020d090b0f1b070306020409021e031501030e0c0a 70
    0x910815000c200700700d038252142d80d4105400b84010102c0c1002d111b02c1c540407400103443d800900c480032680f0002c100c0141c000d40440c072a4601036030600e450300c64586024000001d8219082c1c010756980c200c80b0300b0100303034a0080340d40104803840c000c200c3e040c813903415585409055842c10b0b00d0b0303440030030380794001d003d218068501c0d075844480c8d03450148030460500c500355000c4600c4007251002e001d8030120500031303104440e0080b1070141c024110322600e003c0005102181d44ccc529420500c4010009101241c141c02c01400b0702022107003913445950303400c4000500081e000c08030b1a69001800811240d00c01e40060708508103000500c41810400b0724a011803141036100140c0c42108540c4031580e001c47e80500400b038044c0d007039040c6017030b00c0744924450182d0f109815144140c00301c0303c0510242080180c0003150030510465840351036505442c080d60107030702034982a0032410029038601c807804003141d00ca80310b55907800c403104004000440151003880e4940801b4401d0301c50404940c0e84d5086400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 931227607 1250 931226357 931226431
    0x3060c09061b0506060906010302160b0a110a090317041d01051c050a0210030605060318060105011b0b0703021c05010302042a18090203150a0506040503030f03 70
    0x280005107824002002160311840036221451080d00000028100180301a00030100310303000505a0303100070048000340100e058540e02c454081a0101c01d00401425440c00340c2c030000c600344000301c1c0c00c0d88050300600c00e002000000442c4400c041010440200040b87c0c48000c001c6614a010b54520261103070348425041200c0c104041001008689045941c00460810080c1041020207050300ea5a4580c07034001000b034003030000c1500780b190003442940210042e2400603c0a91a81840a8199041526040069080c0c4a25000410750758041e004110b0741e80e44c1c0484480c0201000d588401a140c030103804d51007030603001d00101c0c4003215242d2030700848400e00000000c05600d1030040000b41c806107030071000428120b07107002c03805008940154280d44850305102e9001c03100585003006d1b400c0a075105d120b4441c80070003403122144034604194031038032084442c0d4002c1a116010007140d41b14a214007030749a8020441480e00321201e002565100315101003190041c09182d80b8004e81821215281c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 931228857 1250 931227607 931227617
    0x6070509010528031a031905010b09011701050105010c2f0603070c0203060f042604031502030601020f0d09230d06050f0a1503060504051c0917030f1b0703060c 70
    0x103501c0d404c2d4144140399071226000d03000c200c901002008a511401d43d080300b1101a4030b45018401806800d40002120400140880c0c00c40d40e0740c0d10071803850b449a00580040c039424030000103081d61040c0d02c01140180c208407140040c8a0050246682600b00d900f859800c1c208210b048e4220356540b00594414041c40c1c940b40d4038008176204150410200500a4212000341800d02c404584040d40201c003003059140050345507000024030000c540119130006044102c0903403112021001900914041ca40a800720381440e0b041454003515840d00c0103525000512d0781800704180900200d1490b40307101d4089031900c51900d1803001c40c0801002c0c2c0d2007504d0042e2503000b842100a4020034442e40007203003107000c02c008800015070084915040c40090540c5840f500420103215061110380328250202001c50764a01a0580103012000c6d207104074034540084060120031844040129140b0f2803e60180d10f1800041c01c507030403201070b08581005441d01c1125000710019040f846410450400c40e160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 931230107 1250 931228857 931228927
    0x1210e0708100c110606010c020a08120d0606030b0306040210030b030303090102070b1308070b040204060909050c0a06051804090807080a0203041a190f1e0905040f0e060705090105 79
    0x2060703098510210100c004c2200c044c2144400040c08122650824001d281030f0501015a00008094208a030064915802001200300d0041c07171100c01816446922107007400455039400040d81202c20044250f5019040000040d00601d4a000354804c1c1c1a6a4100010000b16100101c2c0c6182c0007240c55aa41c0d0b135001071030704e082c4110114603540c0304891140559012102e43c1c0e4a1180b030203160b40080c00c151488001c101155aa50410000340ca00020700b0049030615080031980e0b842640310050250340c43d1200800d0040c1b15000f00c80350175984040105561911a0a10004184444060321020750500182002455280c004d12080000e6401192154182000110040034451500c0c150711010054544041e0100d0038641641e00581400300b08000e151400352503040125920038202e0f0040c9140c4803003981c0003c808420356406032420814140c1d482c0003501219031005002c0b10301d601900c0000c410b240308030300422000c881894414285212081102c92410000459502c034a1001d24 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 931231357 1250 931230107 931230133
    0x111207060f390915030b09010603061d060d050f0624010c030809010b040f150e10260706031b0246062004030201210e0708 54
    0x440c90103800c140700944494240001c00700401c400001c0040100350110810310586001c1c1e80b60b03e008040e24280480c0c86903180c14020f00400201045510800d0403000100d0714511911940c1c0c00d8800d07090781c42440f9103880502c4242e4010040102e0b40c001040300c1000700150702804000f00e100420f1008180604100310900f001e181d2142101c0f14038007421100718400da030311001c1c1c10358a6806041400c415190400000c0c05003001c01d40e401d41007402c042d5860618011070340482e056080c19162508841e40700c10440201c44800c0d240408100c1992100b40300440103500d650682c0c9456008552421440c9400d6508181c4140e001070007003590744070b80c040202280e1b1080011140303640f0103840ca02550505030420342c0aa0381110407078024802800580c00c104013a2200e1001d00d131000c81c540700b8214541840906064070034483c5a002842d084043c0c0c082d401d082d03900b980d905031124032403424207482010002c40d064494910140d1545041c4000c1002800440003030460311014007800e0303001076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 931232607 1250 931231357 931231361
    0x30a0305040203060117030a0c03030e1509010e060603031e2b0b010c0b0a0b01051b0f1903080c0306040603021c2904020909031b0f0d0c030807111207060f 68
    0x11b4080c0300001030603200b0711308048000c81115410802030410008801240c1003c07402000026082e030080d01c21110030041c0700c1030038083e1a00c00c0c0c60a5000740900c1039111030445d1070b40c1d420f4502c0340d015801480000003070b021080841c0313601d40b40c00b41701c2ca05000f140c06c2e0442c10100c0380010030810761120b206605400d4510700908400e40d0302801c050583c11a1591a1440c6010003011294010f644051400245e031103002140d11961041c503030081520a07524945484060340b541260f05485503910345500400803180080c420350f01510b402209030398003483e541c0307161310081c15580d100b59070b600701000503590350314011002440a07460613100f00c030358a08034608040ca424400307010700540e075a000003094412080c0e94020760540b000502030301d4050101d49180143c0141e82c02c45440344060900406001900b50380d00700485048a0a04214140664500680c0c0308040c0014040d640050100f82c0030710500d02e400f14110085840314a200341000c0000e0f00186030031540551248000c1c4080100c078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 931233857 1250 931232607 931232609
    0x606020c04020909180709021b0d08010503060a0f060b0408030304030e09060f040b040e1c0e0103022722141e2d010f06080a050105100309020a08030a03050402030601 73
    0x107540c1140342540610016500b1079000341020790000782407030080f0310001c052002000524841d102552984809242140c12040c580200c0066125032502c0000e620302c00c3d24a6412200040c000c2c0032140c0310005018041c142058203085c843e6190b010002d86540c00d40d008000402c40e00015584030b0919240040407005040c0701203106000f00700030700140c0d954404100303004031421100000c08415030800302c0c014207140041038515004206480310181c4007803054041c818001d86d0356408828026005604902502c0c0d00c542c00303414046002c02503e01c4446100c1d1541d40300500704400c03120785208260001e5038220070400a143c0b6084c82d50f0741141240380d042d80280c460042d480600c81009c52480340140010603020349081d03950700440440b0b950a0a000c183d05404415040325038549480c01c0d9920b4861140c400056070713007000a2030b0080c2c644201810780e0001031a40c0c0d13808000000450240070780a0061740c0c071804030040081d500200b0401400e44203041c0d207000c507071440e00b4010982800d0301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 931235107 1250 931233857 931233859
    0x6030204080c010804050d0e030a02041508100e031e120106020c0a060c08070807080d0203040f11061306050c01020409050a0b03120414061c020a171008030f210a0606020c 75
    0x13400c418031000501c003091045034036800f490040e01001d50400040d1804480e001e0187d04039240c50080f0301c46a054103460016648843c1c22600740c003034001d011004035a01012442441d8001f8800702c0d4000047c2c1c2c52510500809140682c108034401441b000311190a9014501680c08192015410701340021003100605007802c18500f81c1c00c41d9212200036210385c41c0010000f94000070410100300c65032064419215409008545038501481d02e2001400d03c52010740e00710005440c421841e142140441e6050000300a0880103503250034000c1d42c282d0031810102034955002c2c800420303400198410b031841200d4038280800e003002000c05050030082c0744160728441500070030040c080744a18160840401c2c0d0240c03201c5541c2c4191008040740c0040e0118120b605034000140d030710710340e039012401000005080a040c5015112030540d004d5101d8140714200682e00140b180600e00245840a0483c203031112040301071520080ca450592034000b04c2d440c2c50740f256148000e101c000d82c104103999400328 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 931236357 1250 931235107 931235117
    0xc0108010f060c1b0b1314150d0903021f1d0115150315030602070209060604080a020904060905060702070e0a0506090a0f0e01060f0302150301030f140c0a06030204080c01 75
    0x10800340c00500d40c400c0c20a001d410700403021480000089841104c0300103008a40030982c82c0c0081108031040c0300c40038440c24049254a10b41c140d0145446c0c107544c681d141e4019000c1e4a0140171494140103400e10900503402d6010300d41d800c0b2514485000e01e2600e241186070000350400b039540004103120648042102261324101140d07510750b43c0001d00c50305841e0a815078402c0d10a0500d011400b80c1542e03413a081303800e010b129001082040c184c02030720364144208c03542c8460769030310f200f80304c0c06018500c61800960b1000710340c00007508222000a41050040001040012483d15041d140c400103444400041e03020420410800c1000b842c459002514480c080c015414028005411610083d040a0340c00c0d03600c602020600300181d10509169028400034030070241d443c4840b40046d02640b0040c0e024400340c401c48484940403400702da040e241d0004003001ca842858a801402c02c01400c11080b8a12554509980359513541e6086001401e80e640e02503596802c00c00e541d42422080035201e41804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 931237607 1250 931236357 931236359
    0x11e0b010516080d110901020c0d020102190804031b06020f0a2301141f06020102040e011a0d0212180115061101060504020705010609050906240f09090c0108010f 71
    0x1a0344102164001c142c0301c0080c2111450a08005140b031003000c0d49082d0f07161524420851481100c00078101701c4200b42c0070307600c5071040304080c000300724803442d002070068200c82907401c60f0700406078130f03c038449000310810380c14191a5640d1548a1035480c0c2c250343c00c1546d66500304130741c65041088640854162015020b860400d60303031009a8101a903040074110a00b40d180c0f61145425170150b500401c01500003c524280804403800590a0074180d078a28205204040b440c0c41c014001c480031561843e20250880e880c105814480c00840b00080e05410820001d043c25500a4000b4081510203400c04803030f181080c2c4000304070b40c0251a0220b0050f4106000c00d500c5c0e8006006070002c49000781059900d941c0402d8040b1f00510f0f2036044a81e03c0384c4086030190030300c074055129a0950701800c0d001c101710380350002100e0b603602e0200e810a83d64022030318082c20364850103150902406001e8850076403650b100e00000c49519085030f20071401d81c449180d01c4101c1d81d2200c0c00714014244044107007040303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 931238857 1250 931237607 931237609
    0xf030b04030509060d1a0f010f02060f0604020405090a15050f061e2205180f1b09090f040c140f06070507030209180d031a091e09011e0b 60
    0x16150040014042c01000b1030b828000e515044112855402a01810015880b00c0f2949a8090fa440424113025082d02c41a81c810365010701400c030150040d076001803c07160303251400c10425820007085160419000d000014840d00d0f80d42c1a00c0c0036402c0000003103488501600c07400d00d2894154000c1d4400d0241003003d22050700d400d0100c907800000106034140d00100115039498500c201c510322048078070301c180c002c0b41c030354010000301e000e550089450340700300540f00084085004d01a00c014028600c00f03070100d490747d02e00b4000080241204145c0608240302000021700b90101210803010095400c02004100680f41c401d140103445440404800300c1e5095000c034011a020183d0140500030000700e5000b448420003100c4025903000302a03038804c2c81c2c8100e0050319800580f00000d4544220b1040000041c006d000700d003001c25207503030391800807400c2408001c1c081501a1100c0c03510b41240702c2c490b000e2001c4c901e00c2407083c3c9048001142560f045c101800c00f1089a040104181e8603001250b10f107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 931240107 1250 931238857 931238873
    0x3041505060d08040e061f02010c020105090105270a0816150908041802040b07060b010809070b1c0e06042102060103110409050f030d0501060306290a030e07080a020a0f03 75
    0xd0300c580c0c1d40e20700e8195861b9400705100d07a0520820309960684c1007241440d81d03905400c1260003450980c02408a9120426041d007a0f580659821090302880d00313503607010342040d9440d40c900c082070b90b04072060030380c00d9290702800e0383c0095880e8200100d540147c0c0240500761345a44202800c0c290200321007001d541b200b46c030394001c6024a820040705007000c0030b11004a601542d0203041c1103400e107a500d10203880c0040090245428039408103445800046500c8030102d081c00480d2400c0c0341d118a041c1200c03c041c4d0784410400c114881d21603842806100c00791040000c244614030454400d11403c0c001441c01811030341d00345d0000b00715032201c0010700029030000d141600344201a1000f0600101e180307000d5040c852850061601d40c8400724521681e0103450f0419412943c0c162002c012194aa44100816580e46000c80d82c1120700f0b04d0300d070404c1e0003150006140d4158a0b1800096204403500c15030b00b811460b0b40580340382c0d8805640c41c0c09619008940d900140f0000b80c40f910440e24566a03810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 931241357 1250 931240107 931240109
    0x3120310141c12140c2e14102310090306090c0513020406091a072a0905060d03120b15030f0705090a0303031a0612090609010507021911030303041505060d0804 70
    0x2e0600b4141d22103101074001d16000240c41c5d494900c007804101c414182400d40c600007101c64000c000c0e05044006000300c1c80d40c17480c4040c90309d4581001a11a95601800061501656000d040103000d180000103d045c5104070801c0380d00c256800c0350306034a0042006800418246500503507841040700f0446c041c3c01950143c02c6521540e100201c0da022040400b065000308803024000b03001c0d100240ca00803030000052a034850702103058415942e212a000d00441d542251015000b5294082113400f09003d01515118014070140c04508110b082c80803c14802071869014894039011013400202c050541165520908501d010f600b0101c040c40040c40c074610318400542456a00d00901c2041c10018111070004013025000a94442e011210448190011668030500b4007902012a50001c0180602c90207140c1c142e005107078020000e51030300b8a08104090480d1800c048607070a00440c0c409002443c411341c0141815402d440b660102d1206541c0c00903c800d120b005a8000c990000d0500006c1e10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 931242607 1250 931241357 931241383
    0x60a0f0302191e08070b0a050f0333040b040c0818121c0c09035d020708280203010e010b03120310141c12140c 49
    0x4a10703880d004502c4031001009410200c2ca8410002500f45843c50481c2560b00326010b007011600c1d120b5846000d05801d0058204900c00120100705403c6120000400340d90040640814441030802c4c00a035403806001441c200c0b0724400c0082044c070b12614003403003100d0b2803450690b010f21019424140c000d01c8198010310400d80c0003d407111980d40510200648807030788a01c040580d036a11000010000145185110340d05038904019013213050511440b090303c102ca500c020083d08255580b030503030200c1100e0f0401713003002c0000803620784500759003400921107050403051841c140d907203100e8000841080126810065503c107000400801c800010352010240d09aa80070340e2a55400075038207401102c0041c007039455800d20b50f89a401440650001802c00b004400f10742808010b030cd407001c0310380001c88409250b06030001e41048035a00c0c2290030441c4d0400200105980281714501c183c141d541008250340f2101006110745195030021400c8204600c003000541c00c1007800c81c10355075142980402a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 931243857 1250 931242607 931242619
    0x140f0901030c0903060504080318150403050d0f06030804080105011d0403120b0303030708010e0105010e010504051203040b04031b0603020309250512060f160c0308130f050c09060a0f0302 82
    0x60361072281c503c10303004d580d212009201e01e04260802000c0c1e500291886100c1060708403106405030000503d04401e0b5004840500c4565907c0e2020345842d00860604000a911024030040740002e6204a0703000d58491080107880b18285000942102c0051b080b0b1607440e118280c1000b41c04400c0d40000e035116900d441e000203201141c0100c50080d040e510082601444044244001d00b50001040c90603100d515583c1e190030303070303960300110b440c00f00324283c05021038403c000502140c1042800c46070006801c004030b914055488101282c0d0b6071042d441600c814107015081c503a07100035500380c0d900a00361480c080d070550400444540d250806107503c0f1301c140103091075400300001d56080d01c0c402088010000b030300010b024070a0390b4031801d04035209101c0e85c0c440c00004001c6005a00741700d1290360300ba95180038a1425603010f5844040c050003a4000d0880000c00f01d0008a5003a0860f0501d441007015010286110090080c16980900841c2c0305003580d140510254a00c4000c0c102280d8040310340e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 931245107 1250 931243857 931243871
    0xe060a0504050c0604060302030a0e0d1b2303070b06030d0e060702010905040c02010c11460807150917090117040506040b100e060d021f0f140f090103 66
    0x2c1850700744a040d0141e0030940100d000103005030542d0182d440741038641001e000d840011100d4948503060290840045103480f180c000d419088200f00e17451070380c82026252503e5181d105101c0e001d4003801074800446d4800144d003020419a00c0c159034002c10143c009007610040c5010141c10000c2c1041402d0199030301055080c190784c800c5001c50018040070f4000c212118521000034080d006074250500419005000b2044100c0001140340d14086001d00080b01c1d2010344010010007504042c8a020116000c544c00ca09a445070080004451041070195030b41c2e4014030348100c01032810340700c01c84143d142c900b02d600415200c600064911a0500420b96600d4007800140e4a0310880034214003680b512004103c108400000c8246c05540a078408850a03500c0503100840180c04e8003410183d02c001401280260814044e424021807005142c601c160310102440c0c48080d00c140c0d41b0a00140030600c0c890a00d9400c11506510320450204240c94020540076000040c4100d280081c1055502c100f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 931246357 1250 931245107 931245113
    0x130b071218060e03100c030b03190f080703140d020d14041106090303072f150d180b0a060609051e0907200d020c100c0209041b08060a0c030e060a0504 66
    0x459500c44011017010880281d10344002001440c84828081c0644613807a008111800c18512001003241d000703040124010752540e4203582900143d100710184594981910324202c0000e0144c02501e0005d000161960b200006070810390352405806600810100300303000102c2d000310310384c2c91045820354000d9074a841480c0403920714403c07c4009064900002c81895407012104580c0c0f440440c6004060740034540007081140519076131a070100403410030001030203c003402da004003d3319414008050f8914441e40c81e804504902202d031101841d50b641c0081c08066000030501020305401d80c2c3c107040130200000c48440b1030b550051200e20440c0e6802c0041d0303a4078411070810443c0302039502d41c0072140c01000922a80c454103042000054041c0004070365050418070500b008900440e981e01d81c0c800380b03e03001d10466a10241041e56560035401802c0008003504e114080103104880041555181c40c2074240d08030707070820103404105824140c10802100f80010307000d41203a480000065561128a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 931247607 1250 931246357 931246363
    0x1f0507021e0a0f0306050901141308070204090b0f0c09030304090f022203050c0415030b07140c0c010806100e1909150611010509120708130b071218060e03 68
    0x100e40c1d0b102007040d001040c14412901441d007203911075142030055884032500982603d10445c00c2e01801903445000a282c1d480000748500214040c0282e607160000c19001302d030a403079903c002507030102c14a005000003618240c081a600840903a000f07810044034400082d180d12462090680c1552103801d00308454225904440741040d21025042c2d10100000142070400c599100c2a44ca502659010f0700c01403c041c02601c20021001512100c024155600c0c5084a0400ba051904010b82c0705200c8900c06504001442420007070710080401c0810a00010843c0c0c80003041c0d54003c0741600305244e005034020081294800e4116000111065010300801001d04c03540d02ca40c0b03881c1d00704500640d01140240700201620804d5032054100d05d580000582a95010303200314141d40d100000300d00c01c0d0310720640a04141841120124a40a80381c02c0142c181308050300721942d514000650841080403041e43c0f550350800500b49080d090300780165001250502c1c0c0b04039018014610043c00b0165002c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 931248857 1250 931247607 931247659
    0x406050415140307052206081e010602070b0703021011040f060c0209271203060a1220040209040f0507020f0a240e010c02100c0212030414011e020304021f050702 71
    0x401d1081d60702951f2058014100e50040ea0001e880c0b00017003d80544c001d21b0100c040d8103941194000f0900c0b64985500d01617541d104c403c040d01140181300302c0842004080c041c520141410052180c4c0f84d500b0a0f14080924189501c10406d2024080a1900503160704400ca903101c4112500e5000303405001c4c908204074110150200700307e000e0705089041841a1001541c0100b4080d202c410b031998039411030f08600d2500c8480944800030140b82da0320481c4140030b0820030780b1005800581828084004030f0240d0307003458000354078103460754104104603504000d1100884212001000701480c0ca440301120310300007000c0542030810103904806455001e8000040d07100c0850000c12210700c4545000b03407202002031809000380d05280403480c5840c40051a0419401007000007032a548a90780e404540106c2c00343c01c030001d552a4501502d2100705000e05070008c0110750310140e5640340510400100c180380e41c1d244200301070001a20408950f1043c141c0319020380c145e40341000c3c180390030010750b00f00380c030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 931250107 1250 931248857 931248907
    0x7020c030a03020615012c040e100605030c0906060d0207060b120a110a1d090f19170a051b160f05030f0d020c150c03040605041514030705 61
    0x9040c07910301c1050350008985100e6083c202e104d14408a500c001100c1d5892298034a441158080034a0025134800342a01481c2000c02000000e06213840402c8a040c580c100d8840d0703903400d540d00410800c904040c072050030000b2007200d1104991400000194443c0a01d48030140301d0780d40402c214007000b05583c0418605040100060b0300c00c501410800d550705e0341032800301c0d00c0402001e41e2401906180b40300d071017507131180c100703202c608040c0700e82c0c4038400239004100720791714499209500c49072107081c0610100c610070742d040801303138000508241c56010459440216102400c100f92180583e105c01580c454008002c2d988840341401d05405203004000070303d800101311807117000075000284c0300d202d0f82120b1003030342600c0d8060510b000154132903410306800009a007024110286a18110804142500700381c5840e07410882004982495038020b42c1000007c40d500180903c078500320341441048168203444c100303120034a0b10340340da05240009416542400340c04594440ea800e8010700b80e190b1565 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 931251357 1250 931250107 931250113
    0x406020f03040c06110a0c05010f090f060513060e1c021f020106060210050103170309070f090b010e0907142a0606040b09131203020d090c0305100c1707020c03 70
    0x20903050280f141d000e0362243c200401c44454100080b18008030b00b002c0c0194000000c21507840c070f070100541e20340f80b0300028003040103492400420000c3c41c204841c0054400c6903250b6449050340e40d400f8074540c0c0190084014006c4146080b041661074100343c80b0301c00404000d80001140c02d1003c035080c3c1c0c2441d02081c1b606004040300484096056000c2402c0300c01c1d40d030842c0c1c41d201c25002003404494080c00040d01456042c040c3c4150451900700558224018004881410380e072985c140310914025085080c00684410a1f0b403840e60b0f0280c000d04802104a6a15149092508000d421210305c0c404142101102049a241550000b40c0c05d0301c585500c01207685007243d07200c65003900c0b0001111554401c42c5440301400c5e20703060107400248503559010750b00f1004c4009489210361070081415200400d5000c0009580000040c05502c0d000c074482d080f580c6009040d0b04e0070500340700f41700c0c1403040480e1910340000046603016100030019000729445800310780350800300700d0602082241c0950144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 931252607 1250 931251357 931251361
    0x4180804063b01020d0c05100504030c020306010e040c0902180405060310140a06240c051c051c0b011d040e15100f15030f14090307060e06010503150406020f03 70
    0x10b40701c00d14924055030980c2503898840341d508040c1c91001300000d002d812035002c4c1008a00c5c065560b80050b421034000d00304400d0002d03e90f80020b251404c00d030851440381e1040800e004c100510082c0d804050300c42030740c080d03050031010741805890092500c0020b1269464601144568505206450340039084440a01030000d4005a8051104090741c48591941c980701c00007481c104120603200d0300042e041e4a40007440d14150b01107807403560400c01543c0c80d02880382c0ba4000d449020300303540d1300c0e0782951300d5281d2240b991042c191020503060814000043c01d0407051400b42c3c1e44020002450181030401c081400c440d4400300b002449081c03880c504500c00c85181168000e00000c1da90320034482480d04510740d6032a482d6000314803c00340702d5200c09000504820719801e0098000248804c10310400280350355110301c03030150101007540c8020041d000064031500f400004d00078185000d45040040c4203070351400c008a640d1350303881850072544642200c086000c20905404983c4c00c0303029161072079128 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 931253857 1250 931252607 931252697
    0x30106091a03120a0503180a1505100e011a07050111090307120308010e04052a040c1b0f03050c06100501080a05060d1704090207050106050418080406 66
    0x2851040c8100c041e1000c10705181c040c602d000194203400384010004241800002c0500780d07004d410203003510101e82c1c0500c400c180344440c2001a00c0311140502c1c280411022840c00307110460b04e0190400c011403101d140d081c0441d14a0510440c1103411070081d81801a0183c64035030098040c44000400070350a060130598680d10180141441c688101c090f9887d403981d880440240340d000140c014007085504004000c20214407080703070b80c898040c0003130384d00007000ca40030390b10f62880c2d1030b100e00d6201c41866865075550400707101d10b50010300c05040820a0490305000514161401c0c20014000341d200b5810400705481a015914000300c0001140c50750f0900d0014640c000d183c5009090014004c540041e11070741041c00b4041c00b07194046e00040a242035612a000e4401004004940c051810400000d4005140c03000b40203581c0a41c0000541d0f50510341004152408034465401340c81090000401040411007250111402801c22354800d0308400c0c0d81900f5500750100c0007001d10000d003010400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 931255107 1250 931253857 931253861
    0x8180303090f0c030721082221051902270a14070e0d02120d0c02040509010e121809091c051e030c0702090118050705030408090d03090503010609 64
    0x4158069400e403200c0d801c0072800c1c544c1c1c450081c810100b41b41420802d40c242c004241550302052030041d8495032902d4804a07900446150118448150700b0b008602040081d4071002c448551142c0018505200c40e8245c890035030300c01d0000000c0928150290192003107554035264a200e03100000d070326600000c40041c0c0302241c007204035441d07800a420f1400c0380c9003800a600c002c0344070300f102da119444034006030402e10500d201a9039040742c00420170680042c0888040000782101d1006949602c0310f0041807050000f501d03009004111681e050068504001002090341201e07603010008058441d0907604800980c1c581140c0100d070004068001d100003c000842c1c01c2c4030f0458541080c0139400300b42d070021201482520104040140001c030b8440b00924100021504030354020403581c1032460503000104807c4003a071000040044140c048024000d45010340c9170b10111905003103040d898142c480c1c0c4910b100701d08205204140240d201d0301018000c4085c980034042c0540200002500d503950080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 931256357 1250 931255107 931255123
    0xf03090305011802010801141302030108011a032113030f0305071b06360605092407020925020c0a050306060a2105030c070527070818030309 62
    0x203525420008421500407140100f0900640e041e540c59107183e182110904800b500b511101380e000d14940d141015a038142c2c0013541c080c141090000460400f00c8064032070101a0301c40d8240a46c11003100d181a401e40d5000300b030107144007000070680e100520b480340c040741e45868000a001403078129015080c141c1c4a40606061480303202c11a140808200b590000d0f200300d403144400207a88840e40c0e0b040d900008244042d222085248001100007080c200000c05030766400c4035000a02c0070843d01e0440ca00311510281c40310b1480e10034060107900650b5034549101e2648080e000d8881c690102c0c801c0540c5003400b000d0308075861803080b1588190100251203a841c40c003218070410614002107030741d14001c04c10302e000b09001444c0309981c9240900ca88074034541640306220440303000c01110040340b4107000605440140b1070203003903254100310800850903520380d80140944e000b4030003080601003513000203070481e0750350601c024190f40343e030340b04c0100c400c00c03003020035170b030301020050100003000002c10b50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 931257607 1250 931256357 931256363
    0x304050a0b0a050405070302060a2a06140702030d022b05060a140d020f03010e0703080309070b1911030412080403050708010c050406180f0e070e01020d090306180f030903 75
    0x104041c0c48808030302094a4061303802624036000500100014900f050040c140200b0398148100e524011222f03070102644100707648150171440442817130400c4814426080c000d40d102c510b0483ea4103201000940c0d9000d0301d80c8a80c10704e6400150001c00307403c4c10600408192040c03041300400040c03880310101900d0195125030081c002d00d840891505456050404800d1000e468000007600341c2d000c200e030710594030881c10f8041d540c52100e410305c094244074900156004411403696410002042440d1085940c031900d000b51050151204245030040f10142180c03c5244c107001b50324280c0280c3d4214030036980b1403007121400c420440c0400070682d010b481182e000d0010345840c6540c99420314243c0e06403068200000350100010f01c010780c041c1c440f02e60000085120117008a45a101000340741220b500005519034483d420000c14030f510444842010200384007800d031030312590030050f15a00c1036000c0104507a48914192203000703960700d40c0e940e0440e08000c2031820100103040290030891140416 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 931258857 1250 931257607 931257623
    0x60f1003060e03271003090602040914040317070f05030403120509100b04060303050702130209102c01090603110903120a0206130b0c0c0a0c170f1f0209010903080304050a 75
    0x3c614035020a00b141300314078002e06a0700c0b020600315000c9005100582048130340da5824400070403020024812010034400e1801e9900306400c0904010f40001074a550001040d42880200041940d002130b04250001c6241401d80e00d030348461800b540c000180109246810b481c010400c000400006a813451452070490f0402c220001c01c802e00082d07070b100d0b000107130104008101c01801401e00130169242101148401801d10103140005050440482e02d100002058041e4071030f8100600c00101550f244030324090740e441ca803458000380c2683e086100300c909066842c44409a41c1031524116076030004018196055589044103440710b0307403c8074452400503c140c4000642d2a84c0d0320100798401031b04841c00c40c01641c7c0302910b101095201e8060256a80505400c00f000207943c4036000c0d0190400c0b0840c02c030740c1c40d00c0b146150328291143c0c84080c4107901c44550101d80003250515a484858050800b607500d00400006a404042c0d0340d10080100f01d000040205002c0c002c2412000c95100d1001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 931260107 1250 931258857 931258897
    0x20307020316230901052e081501030b1003020a03140f0906010509010609122301270f0f02180f010620030a0c0627050606010c05060f1003060e03 64
    0x40345802041c03c10007540c214600350014822850710b00007201c541451a00c0f41c0c1805040400440d40d403129024481c80411506014000c0c86108403454080c14042881c0411508441038001080540c40c5111070050540c00500084210303ca5041110f05125101e01c94a00d070030040d00845120108030364204103402904000301c0c03140303842104135040352259611910201c0c03c0042c42101c0c0d480e40c68080340e91701100e89400c40c11030075034403000612031442c200000e6036a20a03100714180141c041e960301800e08140240f84002001000800600c1c0d4011079010403840861010907440e00160340c1c402101c09450080000b43d09001c5400c0c1c0c1a504160341c0c681304c0b00040260b502c0500b00820648019400130320100e05014418158641c00a01072140810049280001c3e4101c113010040c00201c4056680080d0702800010441a608680f00380b8202e1642c070455110941c844001811180c081c04282c03020610300e1003000c02400156400030b0080042c822004885a03681c0c0c0054071588600101c180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 931261357 1250 931260107 931260149
    0xe010e030705060f090a060509010612060c0306050907170c0f12010305070614041401021002040b0a09210f060b06120609091204060c1524080604050a02040507020307020316 76
    0xc0103018010440041911b50303c144d0b12400600070050070303000b140d035131a4000250944024140c485035030180c3c500207031540350200001c06491090f00a035020780310701020701c1034041c1c3c4080501d03019203040c80790094070307140c901ca502e08921410f984400503072000b16120b0810f0b440c580c40e0504a91058080f60b0600d07641d1038056400494509a06201d0300c806c1c0001c201580807401100030441051060b1416181c80348000012a0426001003811500100300007041e42e0b00841e00300003401844020300e00d401c82c0f0401402501b400e12000511018086070120204109600640380346100104405c0c0c448414070004208a60202e41943c440c02c25140400e820132404201c0e10000314181e050f40740781c036040000680d00b126202204490005200c1100d03070040129200b02b030030b51000080e004003000003041003400481e00c0d5410405180d0003040500000800c00118100d49540c1568042199910b039042603045014a00003c0c2d090301030326003090f100c0342906444105440400e1080410310051302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 931262607 1250 931261357 931261381
    0xb030408091008041a041a0c0d0b0a0302030c1203120f15010318110310051006092102010f12051602011109010903020d02040912020a1104051302090a0e010e03070506 73
    0x910040c003044038032000c0c45070780d45d01080300340c0c0d01500406030f4000c001080040454060002c480259450502142c80c01c2408854010100c4505040350805202c85c1036400090b1100040c05580d44104410038010b207a1a00c24403e27a0400c0e40402d01002d824505080c070300c1001c11049a5107040d03050220b00041041d8060b10500d10311b00c0894401403e081210f40e01e20f00c41c0c810562019a0611036400c0540c034410060181d54442d002010034050354078942900a09400840d4000c1584000c102000102280fa00030a00103495024a029049041c59035030a40f1650304810007c1c02d032303505180801400c05403881a00503914580e031700800c00b04104114021590003901081c070700040c01d5003c1040903241101a0040c1c2c4c0d40010800140411f50740c0d12134200c01c1f01c210460000d0313000840705201b0300282000e1a2100b14082d81e082c0010300c5c101001c00c1c0007005613a002842940c550b8041107071410198090a0711814440003001407000c0020604d541c1d811418007221107104000000784185196 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 931263857 1250 931262607 931262611
    0x2071b14010e061c05060105091c05060f070f0509130204030303022208071418090d0905040923010e070803120a02120105060a110d0e18060907180b030408091008 71
    0xc0b208918561413082202c007130600030700340741d040190038010005140c0d18107040102100211016034880140340c0742c05401c0480040c02d00d04c00341101d00c10818001d401248094400f800c0d80b03081c40d550b00486c000107080d60414400381840700cac4045004402c15406500600349800000c81c000340c0c08a5480b6210001c0945004064954001010030450070448480d00d2020410051980301c400c9100b4809480c40d41c412200143e140d071180d83e01c15001e80d080000710300609016a02407020320340a840e0f06140342d400180700312291001e020382040001d020343c8902c020180641c10b80b65015030350b92103d42da94102c43c61f070480c4918100d0124154490a10031280c403482c442900c4c8019a00c2c2c9802c0000e10b41003821103e00f4020010540840034805001c42c0d0002c49050300d9000c041d250f036000703000514020362110820001200d05101ca82d55030031140c90361200091500780c182c02c6205010b01041e115036402555201c0002c000d11040011040c0508030700c4400f903451510707400342450200e030345584c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 931265107 1250 931263857 931263877
    0x6070213060338042001210c0908030c1e03070b070f09120b0601050a090e0112030e03010b0a15110601090501090c052d07020603160806030106031502071b14010e06 72
    0x180c00c00b4984113101015030762801005040c5041c3e111b06040da48048100303d1079002054a239102480500d15400007040c1019000e248000c506002480032499510742d01c040f0f03916a8582c01c0036414080700c0c810421620b001e03902801c0c2c501c0038180040003900d00070590b0000e40100d0443c0002040980b024240426003540200c071178003ca031034000056909070b000000110820611402c0030885048090051b0f008100800c140b00d4040c5603414000c0c902408481c000c1e10036414440b2420b01c1c0d0395611804d205491400c1842105007a03550400d0300c40c0c5081103120820b5019038000000d04a00c00e50085040f501400400c0c080c10440c000200c840e0301c98100d5036510190b100341d43d43c000c0325465030901c06c0c40c3e0016128900c0c204040d000620303240c00c1282d0712601102003002140003035a0210039590440e070300360000c0c0076031811030740c0f032585c4020100110540558046550b805100399443c1c0320740c0e00c00d113041e125401e5075220645d9030302c55140c0c00c80b09070100345805880245400c2820032107540c462 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 931266357 1250 931265107 931265123
    0xf0106020a0812150607050d03050f042402160c030c0b0406080112080409090b0406060911120901240e101802090109081204080c030601050607021306033804 69
    0x280781a00283e424080d001100300850f9000f1454192210b00003815128000c00041c4131103010440b004040d20801001031406900b00c605202c002000c4c1d25280700c00c1e5281d089490f4400324009004c10080c00340c4550704144450143c0d0500902c2000503145050300c1c0038909450b010380e00c030351402c00780c0e00c12481075400060401d80100b01a1003500c0b41c8001040c49841c081c5d2405594802c0b40040e01e24094082e0780c84c9120398184001c00c0342911801000788280003007400074a491003002c0c102401000001072034081d5000014002d00008c1d400213240320a501510910000f02030110700d2155601c1c000d580b41d0050700d401241c2c480b0901440c4000301c83c000741b01e004507000c1c03203030350b220294010040940c107014201f6008121003105000340f20303403400081015034543d850903440903c0c003c0b50b0b00f9107034081c0d0022001800720340c07102c6040f503203042d40580f040b2000741d0301e40c0751004c000c2c082544094001c81c1010690a00b11700050b4003010400c0513100b042120100076000c1c0c081805055030000c080324 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 931267607 1250 931266357 931266367
    0x302131104170f07030c06080703110a1d0d1208090a02030a02060f070c0b220e0606160606061d01020c1f021e01020c011506050702060f090402120f0106020a08 70
    0x15180402c0004480c40c0c4060340c92080d0f0200d02c0515200f5180c10458000c1035804080c0121503002440c90340c0103810745401d0000400c2111001010308c10b05007a00300b00103c07800880c102001c0d80882c00b1402d80043d000581c1d00543d81412076598040d840030400140c501c90103d621241d0001d44407a2898000b0054610781030f0a90030001c9552001280a4203d0b1080c81208085581c210298006100c0b40341529607510304015100c54003805110700740840000044140814020085816030014040c4d9641d80d40d0081083d444102a00080000f80300c03a0501c0c80100b8003c1d480341d549085810081c022450808403000103a850b9090480d900d0f80180542501c40041c1080b800c800124044900603075051074151a4100b002e41c0c410414010542c0d00015000c01c048030901c43c080e80d00b00b44140601407035042100081c41c0384200b0101a2280c90b02203160614801041c0031108442c600400031540c840740d1840d8101604e0080303440050b014408000001d4080c0042060403042da80074210510b0300c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 931268857 1250 931267607 931267619
    0x1d120705071208190c02091501020712170a020106120f021e180703180308010e07140a0e150304140705010f1b060612050f0d020a020a0905041502040f0302131104 71
    0x20302099004d22040049a000313490150300e0f840d0309140189031524031482000907400c00645005d5482e0300150ad5003002150b072a01041c3c0d01808091102840542103698910034401240504450f400101101c1c02e9410301000b0080b201400340c100c5c600c00e4a80c00d244903009245095150800154683c1268860501d031409000c440714140c0d100c0307064240040c1880c0d0b6100f03062401400f8500031804240c4c140c0060207550301e880140c1d64001c4e01407400040e15100e40108404030701030001940c00b07000403842080e21583e143c048808480112000c00c030b840e40f400c0c0c03d01a06614102e40c92100d2030107894408100d5510031000d140210301c860301d42c034070701030075050070008007911a100a40f4007569842011804000f000c8440c1a02c43c000c200034104016900496810911448091829036000507504001a102c46205108032243c002000856a07210f0a10402801a0a200d0b00b140b82c40043c01043c02601003641d1403d03240241d40c19410070040040b0301e400c640021004c080b10341e905000c10001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 931270107 1250 931268857 931268887
    0x1f060905040b12010c050a02062d0406060e2502060105030c0609040f090602030610030b01020d110f0d180503030403020d0803040507351f1d120705071208 68
    0x10041c121002d81d0445103d07031800c460008442e54000351000450448560381001441c1d080360f40381a0b444040912041e400c10444030352071080da42d004101c8000b4040c0441c0e940580c000300022841d0112624050700218108041c1c400050041800040041401480040d03080e059480c00780c01400354007444810421b540c2c00c0322414950054449015007480b07007040c001c020515100780030242c4c50b4100a402c000401c0048041c2c14101464450103468683e400248100c4a60641c1011b40c030b103200ca040018140000a40480d28510032141205801640107003040303900610039480c400510740310b804042c2c5a20651101039031060703600846201090b942d000941c0c0007440f510488030101e55591214411074070800300f04a0703501382c0080015062490319403800c0a040500080d06e42c103040c910810510700340d901600b41c19650b07520b83c5608142107503c03400e600c0b881c0c1e00048802c000003198a0300e80e56401603c0454250051040c0000e8400f042c039007144c9031540c0151403a0401d00c0c0d0256420f9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 931271357 1250 931270107 931270121
    0xc06020a150f1107060902010e090f07080a0b120f0105070201151e230f0d030c031d061c0c0c08042705180d080c07060b0d1a1f06090504 60
    0x450f030340d40341a00808001d01c001440320501c03489012520500340c1c0009040e02c035170030800d0790041e4100b4080009003013805040e160700c903840c1d040c10000760701da0300d40800040c69810010741d00410140c00d600304812000800d06806000d0070028000d50b92841e5089080e500c580e03071040c100140a840034090b81c4c10a402c0342b68840e03012007299052503070302e400d844082208950300441c401d6a40c0302280c094100400f06030100380c803d5400e6040c2d0b003515075004009144140000c2c041048000081044d00b26004031503001001c020b0000b501c1e00742c04180a481184900c25604855140080c50844940140f2103c0300c0950003200b91401c00e4a0240304981014040202088180300c00c0644004110284540341c064400c3c07400307070a0050394240c011490402556130b0002408107d2007000468000c1034203e5139410b07404080854410030403008117241e013200d41c034000c00384a206020380d0340c0e00d030b2030100c080d2003078450312b98000401c1c925070a041080c50650107440d0000b08440c0090207581010b4001d08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 931272607 1250 931271357 931271381
    0x70609050607060e03030106050409060905040209040609110306180f0703111011010504110301051506030a1d1c140702090a0203150a030b01060906050c03040314030d05090a0c06020a15 81
    0x8100542c0110134142558000d81141010450101d0305002800e2144110070141001e4203003040300707080c0361f000100d00080c001c000070049030700c1d00c0c0d040c0200200310100c0c054180001d42220340c6803c010030b0016200400014020303e03440b4600c0c03400c1c1031440005210b0200d81e041100c8446400ba4a000e002680069511500c280403000781260b4040500b4402c00d4800e0340222581040031020408040c00e507100900203801500d100304003000d032950342c4c0d8201c1e0307080318005500092684540e55a9100c03140184c64084580c0203264031800034510b5002c103487c191f0429650400d0100d01c2e200380f03da4a0080c0c072000b0790000600000a201c0c51025030045801480400c030042591403900001410005c05070801c9a030298030740700400400303800080c0e0501500d09814400d080c4481d280845e903403400b8902c8050b000ca07142c680101020041801100c01c3c01200100510883c5490b400150f03403005548801c840c81d2021140c0012440d1001c546801c046522010001124a04181540107000d09000c09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 931273857 1250 931272607 931272611
    0xd110f0a031703010f15090510301d0307112b0b010801060605180d20011716030e0708030a080a05010803120f041506080102031807060905060706 64
    0x100200e2010b203414080d9000c0c1016070341e075075030600c01a401620301039400b64011032006040d004d4100d410880141c00d403103064401c00c40880ea400c800322405503c2c444070001d03c880800da8020f84802e030b004c01ca8403101116100380519008907645d00c002c0c1180e8060381240b504188040c000113021032041c0108048018201c00070044811000d1108030031180c84006110b103612031103420407a86005c96070050180b1402044a145031100250591140381800d032141e040403900c50040d07a5907144481c09054100d10b082d8007084014480c00e100118108141e0302080d000c580e420701940400740340030302ca81c0060601071020581e0300306c140e0181504107413208641c0210400032440f401d003000580002007542e900c114107400d0101c04902101d07030680200100b50810003e4001030348030aa01d240d0030031414041c4080035601c80c18004031500c0504458034845017468400106004150007a500410280060301524100e5070407442d900c000d148500d0000c00c18600e410441c601d418400303070110038098800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 931275107 1250 931273857 931273859
    0x901020909070e0a30140f07171b0603070306150504030204150b041e15050c060708091f090c03050d020f070605090603070c0c091a0d110f0a 62
    0x12584401154068005960881d840c0701d58030304110400c004000d4170011404400304541042d411400101100605845a01c8030a08008054960008080d030340001d031907005d50300c29101030b11034946100b68200b5080c2d00300041038494010031014140300000d02c602c0682282202031144c030340c200170700140034541e80b220001000b2040420000282885617543c035a140e080d84100300844000c104206016500401c0c240700c1582d8080032101074681c090b42403800c51090301d104180300700840d0085918035030441e4803100e0594112024000341d2480340241c80055403003400032070b200c0c101210000c019074409101e6204004c0b00c0380316400c0720320315102e020980c00243d0310b5440c0400c00c0d070303402114264071500101c0c6c036580e8180a04100700010034043c040803840e1000040c0309002c0c071210381d4481d00707000010074511806484244210b50b03121a121a0881c0d03241c403200003d029209000b031102007540c089a2452602c010303052003044d4415904460b082d078a07003c0c04408900c140c0e60907000003050030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 931276357 1250 931275107 931275109
    0x5150c0a172710050c0a02120a0c0801060312020c1014090405090604060b010c0c0302041d010c02150108010e100203061903050c041a09040b0c13060e0a050d050706030509010209 78
    0x103110030896014000c0d020807003a00d0000d104128000d44464401c002c410305c1000481180403a03091200d903012603041d16240d0100c2101c90078000c188200801401140c00c0c00988250107400803801c03240a0f40513201620700d0400180c1c2c446c00344549255220b02400b003482100c074040c2030203401d64003500d00d51030f003025445c07008a011250181e03030200981d84440304100070001c490003003080040082ca000003565001e50340d64060f4500e103000c020700c0303281c64044111404990140036501c140d00c5100a20134000381c207a0194652080d410504007100f1280700109403100305000b142e010b03c1e911001004c00e02907030030108000f500050681035000d404840c0c0600740440480c2218051405180030b00408a40d4008001c00c0317400c5601c0e06110207109602540300b0745d81c0c84030680c0d40b144d000700c4031111503910700120f40402d20552031103109445105401168840d401058070b4007100007991105001911281000000c0c961000c3c0102035921120007444954800e401841d040144039002509040d000c030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 931277607 1250 931276357 931276387
    0xa1805070914100f110d02030c0c010f120b010314071805010833060a020d080709030b060904050c1f1202030103080f16020a0e04110a0608070c11030105040c05150c0a17 74
    0x6002e040050381b01194041e90709102b03204003101b18109003040d00c40443c244c0000b52052010a0008400e180e4580d2004c601d40d0094100f030445001003440150b651600c50005468051102e9242c1d14000c085440030841e94040c1e07039030358052614004807007000d4000f190007002c0c040d1151018401d01c64059203108058881c40301502c030075000c0703401419a600c800d07a001050300341d001301b2103410820201000c20104842030081c9400c9441654521440d42c0c0d14100361349400180690b040d0803452545034188552004c003004a240303c49583c0ba0034242c894140808140e0000b804054858001003003903903c400b441d0002071034141ca11003a50002041b0710303000240400084da0000c03988030481010001017181030f9480a040c401c0444030440d080b03040c00d000400c905c800070420800e01240e110141c05002001c3c00c1e42940c0b40c00200240b180303142130700d03010031030344240d200307441c02032600c5016420020ba0a1095a4911405a00802404100741c48454800c418144041c000d590300300100c1342400021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 931278857 1250 931277607 931277623
    0x603040b0123031c021f061707120b09010213140102010b2d120703060f06050613031e020a240503040b04081b011415030c15090a1805070914100f11 65
    0x62880050030920301b400d00500440003804032230442c0c0241070140081d00044040b000c0c2180c01c1091041c3c2d41e601c80301240d00a109403100084080450040040c5c1d500e8440e460161002003a0b009008541e03013102485004181d0300c85503a1801446d16004d01c06411407101e80c204410018121550b0308001c030b0403642004000d400030f441007516501000f414107201c0c090b007001001c0a4483c030307103007001070f0880000c4090300d4040200303c00003541c00c00c002c01c81303c2c40c01d44006580007480c2c0d00d000d076940c4005401c8480314548200e03608082440311000d960041040e07a11035a042002c58078140d58580c1d8401842d4403010a0a40d013107800c10700b44041d1882445000b4021000d001000c0340340c186201d140310001c3c50250154403981c070010803614661203d00d00b400c00c80d12841300031038441030700000258004074640c00c241c42c2c51a6030524190107404582000f40036002c151188403260b5241e60450f070714580d0030144160030070002c001c41d160b41403013443d41702001e2010340740c40c01c04441c1c0c601001c3c2c142030748 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 931280107 1250 931278857 931278913
    0x4051f0c050d0e070519060e1f0806040f0e0c09130f031b3305070e010c150903050d0b040504020d14100e030a1206150c050c0603040b0123031c02 64
    0x2410038000c0941100120f00c01c10000c60300202c00e454082740c034601c00603039030546900700550b0300d01058064a07540c2017501c585181032418001c0d0440129069a641018041c00c0d1007103220300045800300c95020b928100c11a000814012400d20316103082c3d0300030302e1590403090100c5203045442d0200f4007844601501e4408518489040740c1c4800b0702070104416040f060070228504824040310981040c0f0b45150b5240030709104880140314104907a0350922003030490036940c1800041410560321030001d002c003d600f84010004101a0828001203d5040300c0081d0000070311048440030038107a490008e20f55045801300d1b10810420603802041d12007584080605902c0401c640800c260404c80311401d0703034603107071041010341c1c07034111031640c00700c0e80b807500509106518460b0401d000e41449480700c0c03040301504c2241d03281401d1401c01504542481480801c4800b018500c4542080a860401030040100140018400342101e052a119407000d40300c150710607005d01421a007007002c55900c411078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 931281357 1250 931280107 931280149
    0x9080f010935030408071a150f0625230709140c1c1d0c090906070f020f0303010b03100e280e07080313050d03090b0a1704051f0c050d0e0705 62
    0x1d0803070079420030070501c504481c0702d40c44020100c009911039406840c0310345000c90420000302840e02054126900c2f540c0064201007400414821130000d02000c60081d40040c0d04031074000f90b503041520221900780101c420b6001150003c43c40410b03201c070113414441070902d215800d00d02c650107103078202c85400007d071541e00314004008496a205000d946d02c40d040a903402003441c0b4018080746c0d26080001c140c0c10a010141c0010b0010a2081054040f02e1514030120307550795844645640060700704072400402000b0007000415441c0149004138055051104020783d2100c885082005060308404003030a015610604055a40010045500207140b0000507542d6403040264013145d0040c3c1e83c001d2400307450760494100021b80c0c02070181040302c1010904c0d9848401110b4200c403ca5912024150014000750610080c0310000c00c6015034020120b100d428404489240f10b07060b10041c40103140070807400d00140c20307140c2d01034100041210003038081e03501041d259070000d800c800716400c50340c00e014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 931282607 1250 931281357 931281361
    0x21c09120b0f1e0117030702090a050402130207031232010e100f03060906020d0c050c15060a0302010c06020708070305030405010b0a0b03070f09080f010935030408071a 74
    0x21a00b000000d4105000c00c0015000c9808075034044101c00c0188240340500c1070290a4034443c880a20031b58140950080201f035070713400e0182d100c1002d410306a5080e88264101811a0f0280e4000e108a8a015078181c5809016000301a007800c02440c10700d068155400a405405510801940c3e00e02030315110141480c1055040100030380d80c0304001441c026006c61050400d2055074200400701003100c1c1c3c00840070032304502c1e62034400003030300135100041c4c043c0d401e100502d04d14070b03004405408175840e802c040b40d402030280061900b182000b41d6000c0d0b0007001040c0240090f501c901e194000b0315001d44005407400e12140e0311030400350b0142e4070640c0001c2002c000d000c200502801040c40c0003000304e4414056500b0320b200b803c103511002d4402000c1c0003030500f010140310700940b83e00c1d004240e240c080c0c5e9a00666040d02d28082c00401500b202d160f0380c072150148001c8000b445000c00c03102d2405031004040381803495890103500140041d55000c0c003c1c00401e00144210304103174403200352000d5014480c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 931283857 1250 931282607 931282621
    0x180f101a0d0b0639031801020d02011a0f0406030803150a060207140f04140c03070905120601030f05030c0a050a03030e15060f010c0206030a020c1c021c09120b 70
    0x989052404511405082041d0949441400940c00008101c0314004e4801c55040900a01103044144080f030305000100b090007400140e036410715040c0100380c080d40c176804180d4101b00c1c2296090103c00c2c038620580640741d40313141804210441d643d04080c00003d282510780d04d40708a07079002103500408081d12205500e88906026100c1d0f002412180000d003a210b041070401e44000b0454007039a8040c00c0d1490140c07185948a41041c0180b466100300c4088900300001e03607a2159004982100102d9000b42c00041c030f03810030704d02c00080c080a03600609226401c56440304040c100b90942a22284002e10044201907070a1090b110494400c800034620310f00103140c00743c10754076259009845500182c4a204502d10300c4181c8030381c8000300b1076542c10320000107001600da26080f0440603400c810040304020311100036500030403aa0700420120303138581d44031280d01e190003104908564010303000400300e07146041051400d031400300002c1c01c00030541038079040700c0a1010382000081e50508030707280610500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 931285107 1250 931283857 931283861
    0x15010e0a091b0804171e0d060f0f0b040e09070f0e07020610060f0e061603032708300705030a0c1103070b0a061d090606180f101a0d 58
    0x4034410a0501c3e0a01d8607240e202e4810f044100c801c01d407051000040c0a41040011a002035806903681e02c165850b0702e1a0203000700140141d009a030000709603a400411910f60080c41c0000301c40860501c54138107414501c1e81c081c210000340030b2101c0c5124414010070481d80201c5041c02401550644503050701d00004003e02d07101c0d02610b6003000140700c103414403405e03a000b50b04003404101802c202051955040120300548155441035044903100c0401004260340340c1c2202140d80e80b01c4010030342c0e40801d0700c051010440c072824000c1c224041004025016a450000c0030407890284020040c1440f07808000c00b5080001c1300d211002039400020030a2420061180b1b11803025585040802c1700e545c0207409580c0c0c4140701e0b002c0c01003500c10380040e0540803a60030000182c40304401e203070b62038412140da0041c43c080036202c2c8a003600074240040c031607050048038140c0501204a44600c5600c071140720005003240584560541030425101081404117030a5400100c0d480072401661480c20050300c00c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 931286357 1250 931285107 931285151
    0x71e050607020f1c0f081003081813021615091502030f0f0115140f130305070e060109030204090201022b02011112040602091c0b06041d0615010e0a09 66
    0x144281055104130545079001424034102111400d0070301060701e880c03d08001044a40d403000302951f10001d83c407003590814a07001d110220050345d1801c0e065140d0464030007a8014407031044070303141805100d000400d40500c440700c601404041c00248c8800147c91b2601040f00c98420b09000c5034002041c401c04003003101500364000043d800f4880c00354104028141075180b0034803501c0802c03200015031210407882000b25508000d030b40317094580d694140a030042c21241948401c1d6400d01500800003102ca00425901d4410f05050703652110b001d04550804c8001d00f81060160f04511610413009a03801900100d103a00707502c0b071842d1060640355140020b003980c081700a54145414207000164582000030155900107034003200142c1c40e0045071010441000c840820901c00c840001e000340244402c0b16103181c0a80400e5400b4090b009a510140307042041000d40035445600c0000005d0886c241d0b0034240c120010140f500d200b1040225000521644443c2c000300c8216545403201c950104810175868 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 931287607 1250 931286357 931286383
    0xb13090b06061612051804050601021002090a080105010f0303030e1c2d08010f150507140a0f0602041503060510030b0105090a0b03100909030503040f08070204290303040b071e050607020f 82
    0x11050b407070027a00007500e47d1141c100c018916a00071880b0802640e403000c400300a01048402040f0755139564000c4001c0000c01d10003a00442d01e414011510344002140480b80c802540d401c0458041004500712500300510891110469441c594050200c0400881b55661000c66817000104e5040000b2079582c2825a4400c3d031000f400c20028440503074104041c2c42e942900b00c1d0f0f441d008005103c0c0542e040c14200e140080026074001404001c20805034050015500b0b14803000240b00d10484080d400c80e01c1501945e5400b58040d034010781e00034440e810204281c03006240c128108504500860119003081d004103403010b8010003040155408900c3e040c004080c0b0841c18042000b0b1030700c01070460f00c00500061302140e00142c01e50280b0004c032040b252010f42c0a441040700001c100008584ca9452036103044103681400b290303c00c14a00082603034203071b5a5400040d46441c000ba500c80782522180710030640c482645010325030104d5400d001c01403043c03042d0740140081241d007542580c00e121100c020b00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 931288857 1250 931287607 931287611
    0xc030204120f05030d06030503071b032f0901230609010522030f0b01030210020c01121a1201200723010f0905010b13090b06061612051804 61
    0x4000e075803601c4100105840d00800710300200601400c1050440c411404002221810010b00200b0490004000c0498a0040050102181c0700c20400112803a8502c0040e103c3e070702c0d00204a40742c1003007210b841c02d85000d80206002d0384144002046051000343d00078a02d803614600c190f10b52102504281d0a200b2080f0340803440c246041c400a0994000c2442c0c500d1048040280500035901c03026100001d90b4000e0400d64000302d95286ca80210740090008034014003480c2900030700c19000141c0c42e40c1201c8140c64900381100b81c446960300605500009240d0500e00303522090054491040c010300312100d2a0001c05d0706144550b00500310441a520040e000408110ba140407400e0501c500e42d078490010170500c024a521042240903181c9100c40c40c2d061480d00d50844100700b4150f009040d00e4400342d80f0916180007001012089501c0d805003c0e041380941c0001440514009005082075000624003000a00c0c413911590700114203803e0134404510001a00034a01c0c002400c040e4900da021941 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 931290107 1250 931288857 931288859
    0x6090f06010f090c0c053307080a05131a180d050409020702010e04050a061406090102070e040201021615022806050a1107080315030105061c0507210203010c030204 72
    0x100e9481c40c9200380c03a039113541c4500e00f0490f10310a10009040e950440100d494403c0359038049042075080d658000f00d41020040032038907950500701d10382d1080e00249c80d0159a0b9030f0308041040503041c02824400c002c1103a08c1140c0006542108038014030440d03540e2003c8030f151124803106d01d140805003e0b0810b51164103860741c001d40c00000c0701c055403d8800056190610303880180c0710b50300002152540181441c00f080303806180e90f80020308031085c2c2001030406048d608103021140c81604c100d03600581001e2018403100700030501440d0000e00c1803046450181000d00c0202091072180c00c040d9210032414a84c0b096a603042002100d120704c81403800b14441c1003c6510240405d01c140010901521100000d68034241684040d04010554110315903422803803610b41c0c05a441103813030b00e080d08650204c0e0030b401c0c1070510032280305a002601e1745203143c0c2441ca038510100604241102e01d84108030b0b02080c1c00c0080d08480d044085000e00d1181200840d00c101070070340310050410000c141c41840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 931291357 1250 931290107 931290119
    0x3060312111f0b180112020402071103060c070611130e07140a05090901090b030a0201080405030f0d0b130c090b0a02070512071d060a0e19090506090f0601 68
    0x4112820160604080411805a01640341000d03900450110b85072588601107203040c442d0303085260b443d1001c40e40c118004054200600c000c201c00c3c01a044028841b500c80f0005042c40d43c0140ba201d8020001d0311800c80b041e0001078030b07080044a10207003a080c045071039020810707180a448413aa003218901420715507904510b00c44011584a00d05c524a401c40105140c1c6008551151001440b170080e039a49800406001c2d240d40d0020a60300c1c0a440c038000001140401031180380d1241e000140940011032180d0011102070402820580d2a07010030082954485203810007005104602c00021941c51150010403c81c10f400d0503026071010700300101c16103003561010004080d50b4500c103000361125103c0c1c0b8124a0100c86406c2142c03c116107035540042c0302070024012044034070140412510700c00c1e80340d001503100000d45025420440d2088281b05038038401c03480c507501440410341c90001041c10038081064400c015010750ba150800c0f01802104e0000780101c0300e21100402c02001035501d046 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 931292607 1250 931291357 931291373
    0x609030909070f030b0a09020a0e12030703140d0e07030308090a0323090603041109010503030423060c0105040614220b09070b030a0509071205190c0906170607030603 73
    0x140b240041109100d020601c050196002450203c0301901c2c0401035501e64401500a62000d08081c3c080b071558407060301e1764505681c1030b54403107080c400514102186690140d40307040141c41582c014071418007240e420483d65100312500c0c480508001d000542ca1030801406040c03024225200a8000e203a08a01007500807405002c124000551820079054200c1d00000e00c1c061215410781c821000420301003032040b015031511807483c00f00e4040440766652410196684964030a01c110400b03003008103a0040c0c0c103a4000210072101070f1007549044400000d9900b1104100c1d400ca8110355142c0b10000d03a0841ca540c000e900003410060503140c001c03640144505200c10f440001c0a244681c80050684002800507500918002e018a622030410001e018081c03c803c640f0490148214100091201403141c4001078150b00719002d0b001d541d981040700d6405e200404001d54040001c040300103481c50f85403281c0c00003400254200c0302020010f002050030100b000d0301010816080c0141840449c00d90 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 931293857 1250 931292607 931292611
    0x30a1e0f0c0b0402031e03030103020406060845151b121e040b01030510110414040b0a0603020d050603030403020f060a090f03031101050f160e0609040f0e0609030909 73
    0x200c45409642c1e118400a1b14058060600c03c20020b0310800d03111303044078000061816240300300c9051051940f60801100d07a01c4080b5041403074401c1505001446124100240141c20700d51b140791201d26002030008030204080b0140c2c001c4030390050f0200000310f8621400c041e040b061000400c0c05144105d4000345282c080c400940c1c04618100c03020030701c1402100f480129440a900d0100428546410b02c4013184409100990740360103486d9608480d95a103202d030590301e805900c4414141410541000034001400450a070002c0d070790400180655207401030513005140a580c0560740d5020102900e094484c0078113698026441400240010b9648580c98520190103803800758540d0b000c601c0889451915074405003100348080c00c003009044c0d002003035043e4220b0440c0240100c2e1998007440310001400c07207608004031070ee0030b180ba01691107101007035541c0030000c100505100d4080009000c0b25606000b1050480d40c8006280200c4411710049130b000e03003100041c1d410400c0000c08104800b00c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 931294964 1107 931293857 931293863
    0xb0c030f012c0403021608030903010b03010b0d080a170109020d0b0105070b0105090702030d1802100207061413170a0204051005060d0f0b03030a1e0f0c 67
    0xc4480b8022614265000d0100d8250342c002c41441560800b80088085014065008010b1071b41e03041d520016100f40005555114800001c060840b40c01c43c5146000741d050403910007803035031107841c80c0050303030740041c1d1141d5500440b08044401c10b0340c1d21140c0320b24920311000414801a60307405060303100c025010030800f501ca07500c010741d4135010b4000e00401211403400140b01c81e0501c04901d5800140a004580c14126581150003d0381c021018954100300400b214005624003a0a03007980c0c0d0003280044c04d8107a040203802400f21004030400e145403100000e001da5640744c0500a440108030804018007000c140341001381d201c0135199410f034811410500424600124070f4041000c0342d0700100018600400110540081c09454919002050381c822603800315803811320080c2905000390303580700b41c0e030b20030822050907846540f00c030b80701082130032024480e103a6000b01c0b030551300d0340e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 931115107 931294964 := by
  have h0 := BRFrame.cov_init 931115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 931115107 ≤ n) (h2 : n < 931294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
