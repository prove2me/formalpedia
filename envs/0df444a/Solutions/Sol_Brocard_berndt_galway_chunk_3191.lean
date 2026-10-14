-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3191
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:27.670425+00:00
-- url     : https://prove2.me/submissions/050e50fd-f693-4543-a675-c283da99ec66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 573741007 ≤ n < 573920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 573742257 1250 573741007 573741013
    0x30212070611010b090601030c0c060501060203070c1505091003020d0f3e0d0b0d050102220617090a0c03080310080f0307020f010909060e070e180f0c0705120c 70
    0x41c410b00e401c188501c041d182c5018202c0b14180d556480110010080c202003801404815825003022034407030b100d000d010703281c103030000c60b0703146c03005e0a0045071030065521840e591001400000d2940360f0240564050356000c1d210720645135407010054029010340e071900044c55251140b4031004c81703660b82280c81203c4020646454010792060700007032002c003044545ca0312020708450a410007250030000e1034036010442002400e1480e06c0c001a044445001d016145130f074012030500740b111401e01c0a14404d10b844903014240f0b41c50070002809989904510b444905d1b511000074030348850a1201d038901540c03150b081c035080c0b92a0300d0004103d800c00d44010547e400000c41c0030841c090001403003220f00450314001c5040072401c0e403c2012020300c10300c01904001c0a000b000400403c0d6004160291958180e81d450514150000a00250242d00c40324402c12140d41c060140103a0781d0305003900030650007880c01d9144c0c0c0703155501600384a1114014003074418604030480306002c400140ca0345d11030348800c0d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 573743507 1250 573742257 573742277
    0xf16090f09050601050111010e060a02092d04111b100501051815151603030b0d02100305070302130305101d030a0806030a0b040f12051c05060a0302120706 68
    0x56481181d00101005207582c0c0040010b2040e58001c0c4040c0c201d1a006000100b02d50011941c21801c0440586008a036a42c01050f80c4d0340c20b1411240481004084405626039040c03203051600c80c24040c00d0300c160081c2d554841c42c2d242803018604880401320032400518940c0401c514490341c40c113043c410034101510340ba002007010714082204500d07403403001c0c0c4501c12540b9803041c00328010400300d0048d9400b8041d03c2a040c40741b0000f0000c0c051024551415454095081c10041e06881000b103106224102c013028100040e502c0d69a4a60180410701e40000c181c2e036807035016802489070303004141504050040000c100301c0c000501d80111400d01400307000200100020b952580070884644005801c144132001c203051180380095070004005049409a003501e445188030b40e20f06980644118074008601170900554084500c04000135150080c038000807030041d413840800c00a1001d0390326480c4c134003041181ea540c0401d08080d5400a00030030703946002e1108107a94501e03e108410100c0c1010003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 573744757 1250 573743507 573743531
    0x170712050918010b0a111504031808010203070c0803040212060a15080c2101020d050109090b070e0f0103152301110a0b01050906041b020706140310060804050f1609 72
    0x2480d20f040b0b4009500300e81c01c3c056a582c0584420072050203d40e05803091412425440c45615112409940240c454403800320b10011580009001c64000c01c010344c0c010070600075a2540055510382d09a000003d80d034807a1240d01c00552040d80c0681444810301c55001408118044ca50124400481c10246a0f00c1b2903512540580c40302007942000d80d020612a140ea0b030300005211240e0402d0044c0c10005240c03040705a03036101180e60a8000021050340c90b01e0107410008202101d503001140e5040100c070001c42000081c89c095024000c0301d04040c0c503841400c40d4000101d0149000d4036040308113a0040700c0141181007101a2011454002041400170386060440854205e2005802151215250782004280441080081e0905810540c2c1310384416001818488140160401e54064160305141500003880c220028101e4400c882041042c001049900d210ac0b00458030a07007003c1a081c2d4880c01e00314140400303c0c00307080d92400344181d09010307600c0b80c1010b541a96401c17a410060740340404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 573746007 1250 573744757 573744799
    0x110a241401031109100e10230a0b09010c050a1a011203141c0e070806060a0506090d03030b0d03080108060f0f070e0a090204260c010c1707120509 64
    0xc40302070310000d0340f900742d8602414031000140c0d010541110045850b82c0d507281d00c07a020036040301e107040c281c0800c080611034410300880054400848007036125800741a8800540310311198400e14a02500c0001c0c04076840e4010480000c0030364101e810794032900c1c1142000ca1410602c221003403440c1c6a44800400c00001401e151070fa041d42690350b0080e4507a81c1254604e06a0205188001d4500c070360312405a01c8015020f8860a0b4268802602803189803510903440c022001e03001c10b12030424407001384880d0f103460050b00c0c14030038116150410701c182c50078260010520b00700c0e4030780c0103601104050280750700034407464100c5205030101d03141ca50303400e12052a00179050318500c01c06070044000c07601240c818121034028460092800c50015955a52030b401c80e0b1042d4480f100c20070500045d0b148140300d80d200490380c40050409881e5181c0c18400080c80c0d1420a030008250f03441007100326040e640b00c8029504515408203200c00da0303a007220805800ca4110500091155030340b07015a03107440721b041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 573747257 1250 573746007 573746009
    0xc1b0303031505060a0c03031808160b062b0606050414010311010206061e0f100906030e0f060705070311060f0103050f012d0e03120919050607110a241401 68
    0x1b65a0140300410550702140a8580031116200b011801c5c40c0074808074038100f004003544400e5894509181106184c10068141e00505a600c40c81c1504061880805c00c45e091608140d16428401001d42080c43d0460090005400280e00145040804e1000785246010103050ba030140c01403255903040f5100480c0d58100495819410080c1807540c00f08840d00d0018104448100501c00e451005c6040007285104405d80401c1e400240a0042008066014860604000c0565000c2d258540c1300801c5140c0d03504000e412032040000c00502c00d014103205106210f41402c9040544505081c0210a081c01642c00c0c00140c03400c0c05007116050f0700303100500c170703201c4607084c201684148203000c2000110494485401142400d0f1207100e040c052200500003044100c12078080800241080c41e81e0078640984544c00750071140c1400e03151400b003000007a900b07174040d4039071500b05490140c0d80d5126040091080300204038003040300300381080c5403401428862000c0072400c10001030703001c005880400102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 573748507 1250 573747257 573747277
    0x8011b0915050f030c19020d030c090305071518030c06090b0711062101030614010e010e0112080d051003150c0c020d0f050f03040501090b18010c1b030303150506 71
    0x800c442d02c0d01240d5000655403001400801e070381032104122000ca080c010400d20500148c0011043c40c000c50381600c2681a0403030301e803a14040482c1540e075546c2e52a99140100058002600024a0510300c9002b00401900003100b200c1c032160703540c1c60070750b408410314050300b8049102e0450116040c00f080059a81d1103401101d5001d07000003c005000700d6038003480d02410004e0f1407000c440458074018801c14000c511a00b00007c62903100007428442c800182c204901c1014440010000580300321462419540184e441c800c0a444c246400c00442c45882c608440403800c2c0400c00290180a07480b24048078010880385103000761640400d8210740c80d203c9254085961079070014090305107800d0300221548907080c64090000c441e02d49500d024610140000030b80e0002074184001d50740002c000004204c01c1d00481c0c24010014200401c01ca07140407e58100b01d01c0c0180c01d0140034407040501c9801c0c00c128078810361316880e030400801800368100d09039800715000200203080d007041002c558003030321 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 573749757 1250 573748507 573748517
    0x1106040f141c032a08030a05060f0102030417070e010e0a051f0b0d06031403180102190f020409170705070f03080313080702030114091c02030a1808011b0915 69
    0x70b07075582901e034685030081d0941c43c000507840d004103110180388100c900da4003440b980ba4803454415810702c140c1380001e0a840c019012080200c65a98000084d1000d5a820106080c401028103802c50300d0401142e00000f403442042000091544c050b080c018015100004144215541d8482c0760f070207941e040700c01d07820a2440400401540400320041c202050305018086641596610303091500c0d80d6005556000d41c0001607488039203940c0700728044895000b80080e04005002403508480ca010160010b480e000e101038104085690381e03402640002c0c2c2c030640194141c450000c80354500d070044441260203206d060008240c480c59004c1c0002180d6108411a182d83d03200c1c41c540800307036040310003121058014007208005030f8080c0102a903d0031030350705020351850580026854802e407041580154031a500c0301c018207940c007104892580300d441c1480001caa0949040150400140d88403c510b5464a40c444040780702120051207040696503a02c1080e607140c0101661031089150202c000c62 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 573751007 1250 573749757 573749809
    0x7111002130305010218010f08130f0816031e02012a1806051c020310140109050904050c01021509070302100c0605190e1b0402071106040f14 62
    0x1440e001003906030221040018080d40da66245420b9030090161000d001122003c1d08000d540d03c50ba00520300f6415241800d0740d401c1400c02d140c11051048001b819000580c00ba94040c0a1400c0c100c540c6414075021150b458405420000c0c40240c9440140c2080c03488080b4500d250742c414003070407540140c0349142240d50500000005085444004200d080c005840040d5007040101c001d0080140700d29212503a881038400362000c0807080025186c80600e106105029030702080c1c40021090302d445580c5040440011300051710320b60710980c055548a49100100802c112003c40c0b40e203d091020b03003c950b02d20810000c00d000c41e03002100c1e00040c1d50f000c00b40c204090702e40301c1c4a0400002032402c0545020f01d0a0b11034006507141140c5542e40201450b608041c0000e00b8411080380c0400300010300f5031407103103284803202800c3c1488440d01c00c5802040c0310050088800c01e415444000402441d51160742e80400d4800480921075006440d00c100e10a04280c2802c80d1030401c071a152800c2034a00d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 573752257 1250 573751007 573751033
    0x509030f1b0a080c0c0118061209020a12061b030209010f2d0c15060b070b0c040506192705130b1003020706060f05010e1002010b0603040602070204050711 68
    0x82104a40c030440c180c45050159004260104000c00440c0b64002c06484202c03605000501f40074480701c400e54015442c0e603000c01c10a5404202c0110b6142000e0000c00c9040340760000600e01c16090308841300b100c000b070702103d00b000260340c805080444005004121000e6803002602207003e00700155010a0b030852b110555644140d510042900c2c0324498038017504404183c1e108000d04001d03440c804511000015001d0010f0382c0000b01c2070110401080c0f08075410445003810700d001d00000244031403140700c049069004114180c9000d4000a0005900c461441804202c44040c1404480c0030580c80c005c8044507810512840a070040b000821214032441c00084c40955680703500501088ca036600030101082d5141c03902148039000da1303500540c545169040000c00c0f105c29503c60301e0035081da82c40c2040300d80d070404140322041d46c1c22140159525002c4c24164050310090000325842a400410002008503681c00f0745115802030f0f508111565030700034152000c01d000f6a25400940c401039001c181 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 573753507 1250 573752257 573752287
    0x5060702180a090f0c0503061b1b0307020d0b0f09010606021b03031342050c0a05010c0315170627100203010e13120e0103020f1b010509030f 62
    0x440305002c0006840e03a041e840d10024400e410b8401c440780386030a00108802e290030400d00340c02c280319083c0c0c0b15010f00303040c40400300b500c9070042d000c001e0465940c1d102003440091064800250700581218a2a101490030b100e0032902100c0d2a03040005890200b803550205106200981d465078008110344552902e001c440e1032600d44541e5450700c0200001c00f000082d188075000200310b0540307980418100d003c04540f084000100760440650300c02e001003000b091100210070b240c54181040b0740c1d0703040d0452050703043c405c0101000e0000d40c2842030107504c80b541580b00383c0c12400381d00202d928180d182c0042d0f50a090955140741ca140d4050700114a00780c965248076094103001c110b241c03200d03154840724241000007480040b9840d40d800310041143c2e03480d42215507802911400740c02d2407a8000d0b0781e0000f0504001e60590308000800d00c0403505030b40250b040303401c507608400c103e64544581c81010491070702d0380ca111007402d50a0501040148030000b044e41c2c2e944040413881401c011146413880303c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 573754757 1250 573753507 573753511
    0x12060b0a050d0c15260405030f03010f030c050405060607030806120a030206190b0907080406060506030406150f05010507060902060d050f0702151e090c13150506070218 74
    0x103400880c50800080302d40e1a07031142503045100b1a03e0f2a549413425980311143d4031a8000d401c10300890a04028607544014040182d48100d10440500c64469090151a50256070742d08091007a0020011645c9114400d00d038040381d1156003075000701e603116024070060312025240c2a41001c014805440040d0003280540d41c00700c1c0142202c2441d45c0108102c9241a0f8004001c0d40560000c0040c0154044003000c3c5074454a0b50800601041040d10301103180200d00804100803c52924049820001c1c40d030820402400f0041500c1c0e1242000e090131001050600c0c0c0c02c0840300c880d40000508980340302c2c00d401c219030058403828200801d0f622810060043c0e00f40c01c0b41d0042c000c101505030081d007841004c5c010b4582c4030050301545006400a80360401e40120754420005503010002c844004070030300c800400704903400240703641312889001d2074500c4070300030303694806200406180175100b00d6008183c892854041c10314142c0c0d0310000e10505101c3e4510181d006001030700c2d0502e0340c80400baa815 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 573756007 1250 573754757 573754759
    0x3120e0d0b010b0d050a02030c040e0a060905010312020f06010503281509120507020f01120b0d120e040501180507090b04080c0f011b031404051908070f12060b 70
    0x351810455481841d415001d800038008042c02140611910a20b4450b240e0b010504072000c51460070220403c0006020303911030f10f083c0c4400e0a000500a07642500000c00a04000b08280030a50b1645003030041d64520003030043c0184900b81d41004401c80008107036040350b5018000c1c21560820f103105103000080b4407034260783c0051100c400400564440061307030345a01809400102e00030a8030b0700d09542d80e00f4110030001c2240600800c0e025903111004e241048509007031081d40d034465040e01402401290210070ba000c0c0d007107540c0310107104003140d003603503126070039542c00401c01c0104040100b03d0303a003030007800d00d4805180405075002c1c045a220a070070400a042403000c05583e40d400c002103038450b400020264101c0c1c0c4a203081820b1003500c29280780c409080c4008090000055000c078084644d4010701001408040c3c0c03103988038500100c60142402a050b01d034100851a030300001041c3d01d1044c0d110a00c00c3d01d0b00000c0480f8820189001d0310482d03001d01c001c0c02000c0e03c405000c0c200c030702c0b141c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 573757257 1250 573756007 573756019
    0x304111c050312060a0b0403110108040c03080a0f02060601030608030409091b030c14040515150f0d05010302090601050901050d0c054f03150e01021b0d0903120e 71
    0x14a01150003000909961103021501e85004d142c040b05106814090340d0064010100620092000031244001c101d0000c1f02880c04031541e680320705040c01e143d8200e0340090480e502c0042c9601865601c0800d40ca11100103400302c0300c013500c03280011000c4502e28440c6000c0303504280000c1c001c40c80c1d5600b04148090094148003600c851066004e04021400d40c400c980c520900c01d410060403103100e546034951003044908205c14a820321205029000789011a44035201007842075a480c0d0f25181a10102140702030010303212080345480c800140001e0200780c0c4280140c10000d0001c1d03202d82c00f240e0043c036040e92000d04040348600641c0182920b8858141400303c280011502190358421121404560504004400c1e0020140381084a03100c0c1140c00095144546409621041095003045a92124030a00f20b034030308103250002020326440d01c000550000030710410105046600b881d82d40000000e441e1041019481036032a074803648070090180b8140c1c04d034002e846004d120075025030080600b40e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 573758507 1250 573757257 573757309
    0x7060b0a121502122d010b0406120e160509060303070f0311120304030528051b1e210a0207140310380303070f14030c061b030411 57
    0x840d13510810200d5040700406501c5082c0ca08480301404400d100301c006a102c84e40e55414149210041d124034000d0405106509402000c07280445c0d0116038070311001c5041c0d4041c7c8410016503104407006104207881317130f5100000f265032450080304642003507078098004044d0110550341951004d444407041d42c0301380142c3c501841c0a8132a40c00440c495846036644551307403046a60390796143c149580c1c034142c05805c240c910000c3d0f0380c1c208040761400384681d01c000000e07500c071200316490700320220180810140c0300345000d05c0742c3c040000c08003c0071203110208030502583d00c95102050040b042090010f0348001e004110a0015500d4285001406010340b00030144400841041e281607a14440d60b00040d001e250102002d001c0203a00010007090840b0b1480130000002030780e0f4041c1e080041c00303100c600301c02541009001540550907142a4090301e0725290318030b5400b0b0300c400040310052030740a0b0840c6402d0310300030740e5070803244110b9001400c1f51000c10260300f409812181120505400d10400c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 573759757 1250 573758507 573758527
    0xf020d0807030309021c0b04060e010e0307110a0602060c27030609060a060f0303021c03021309020c0d1716030f0216020f10120b0a030b0a0207060b0a121502 69
    0x1001c42600a80b000b01d540d03021881480180031003041010200c42c050603403000021800e07410756030040d4210700d000c41c1a4541c880807500500311944000c1c0644400203840c4108805110342103440c6c7c4088500c51b0f140e036035544041ea181c1030115011000b040c0c0c2000f00c5d0b0400c040b03003c514502600d03000300211020400b80003181c0707090415a0702c540d043c0d01100070460305200900800b40030340245c4803612111403566502070760302d65044d07005c440390540301103c072000c8a00c287d0545e100410105c0300c81080a80d5111460700070741c0720200007015401000184000c1c207005d50f0740c4001054146450b090a0b0781c0e4800d00340303020290700c0709503410541c8414005500d0300090014041701c9038092100300d10140648104a05001020300e0207001f00300c6c00e01805566500080c994554080704000811400d03100e900040456800343c00c0200320a442c40240300f201c40b0540d01609480e4420102044141d080b401007113003001052082a10203201c03120241e00003103084011b046a829100d8000d400e20746440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 573761007 1250 573759757 573759773
    0x19050f04050a120c0807060c0624030b0403030b040203070c030e01022b0201140c030f0c0c0703080a1d130236031204050a0509061914030c0405010e040f020d 69
    0x251040f501c0b10005511601400084024100204003000083c20301d180340c084003414864051f100540501e5446c1d80d11400c14442c2001e000e0400390003030318241050340340e01d411403802d14162415000240703026080c2d0340d0340c246072084038011041500c800541e04d116680480c3c000e0958002581140036180c0710311981d401140b485211458040200c80d074040d0300c0381c4000d003100c80d411644841d402d500014080c840c2c0c1c82d001101d41009802c40040d0540d074076098503100d1441f940d00100d03418440c0040003c1449048409002080c0340c42d640e0001681c0d8818110801d00283c01290364800c1c0c0380c2003480a1291282d0040c541c5c0e240c0c6030001c40d945e180c990b40704100f219494402e10b68840c160310785198145001d01c0004494881e020703902d4142420480071403100c1000340601c6008038000e00109442da503411f201e0304c0c0ca2600104051140320340302c4400d400c00946184081c0e01078402e503400710341c1c41c0c5000c0c01201d0507a0201c6c0c140880c2903407a5145d04d84800c14064060760001d0300c500d009000300c1c40203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 573762257 1250 573761007 573761009
    0x303040b102601021b1b0a050a03020609010c0b0f070e01082e090e06070f1d06180402030a1b050c060a02070c08060106021f020901021009020301060801060303090509010b19050f04050a 81
    0x164001c0c0580c6c00b41c007440341c4c014149018070701d449407469a00912075941e03000014820790790190340d525100e03480100142c1d00c3c1c0134101006401d21040a04220411500340071341482001190303614000c404000c3c0040d200c15100784e86036103c000e0b80c40303022040c001d0320b18000d0400d041d812148180241d070364402c1a0842e03448070714600c80d03504101c00704030350a508501c192070000e041c0d10308078001d00c000040c51400404004400c5101e44030008410a40641100444e6070b054001081155a414550004030003040c103027180c401d40080b0101034082c01401031003554002880c480181515a690502c00002580a92000c0311507004070301012070201010030009019012540080c0300210800c2e21824540b04000203004c0514010050b602d03059070302140142c0e081c180c070000401e94441038030009014045540120443d07601e8288000305059011500108994040d2903024450b625841d050205200e1004541200c2c02c84150900d0600c1c841c5000b058400d5070700903160708190710342000030426205 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 573763507 1250 573762257 573762307
    0x1061205030c21040e0a0b0603151e01050702190e010305030301181512030c05060a02071103011406090c2101060f09060f1805090106020303040b10260102 68
    0x1080c0c1c1d60242c4402c2254003280c4010110420708251188041c0e5010321460003410b4080c0e25080c0880c40c004100d820200f50004000c004a88070b20700300302010550300113440e120b0308c121007506641141c849203801c0b401e03030104107035200c07440d0404903002e01400e1120402c02c141e4200c2581000242a005031031403501940c8a00c001d143e4035490140340d040000904074120515510f0112171b9051102081c0003101142c070f800c49001400c140301d040544014001d4000a00a405070400304040600b959005183c4203210303100f01c0380070305c0d40c441c241401c880302c42c3d03c8041980c2d034040100c3c10502e840c811142d4004147d084040c03a1040381080e20040b44410040c403080c071280c0320300522190381c0100004e0760106007481c04070310302482e20a00a154800c644119401d12448a04603c510b2102e11041c4e0040c00024001c0002d40d40e6848000b5500d83c01120b050f5903c5240c0b0b404100305c0702001c0c2c0007000315500560340760b01c59050201c08903050304100b13001c108903640c20003442d644405054800c4030010702c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 573764757 1250 573763507 573763513
    0x40306150608090708070311040e0d080901140907030b180a11090c0a081603020403061b03110a020303010e060a090c0c03080a060e1302060f161e1a0901061205 70
    0x310789000a40948009461050950030904040c03020120001d0340030104da408c0001a0640712a4401160050121030100c108070b000e40030110500c4e40d004038102c1d0154071210020010b4030301000d40c0c203409190944040b03429411040040020410726802d5035000000d8045d13061040408611aa04c1e05100c003900315054480c24a5130354403460401c04480e0b10070b0340c0d05005440d014031a10001c091350001403141d900c00d4112810b09030510305ca98103440103036501c580200804804d00c1c0e14100551003200321040081d0421131000c40c185110300aa031407038a0550019807d607402c4c01c0022490003c0100040e400013071780c0000060060071070041c0340d42c00701c268481c81c1c3c45401d603050007000c924004150741c04460420508120414890210316803200d40200800d156a00520014405104040b4042c3c1e400c4004036200c0900e0301010946031003070b4418550400c00100313401d40c00c00382817402030001c0c2403000702d03844982075030044811569114016a00010707580751148408030012400600c1520154 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 573766007 1250 573764757 573764759
    0x120305040e0420010c03050a110c03010f0605040b1c11010c0210080403020607090609030201080c0d1e0b032107020a0306020d0b04050a0e060106050a11060a1e0c140a0504030615 78
    0x1c1c00d604150401d200f00b0318045081442030389018009120b82c40320340d4108504003c510303142c0c05040c4070b801d4001100034021f0224240d00d0f821a0041e003081d003ea40e2160b40b8102042c40c55292121201903552065031406a04440d651107000c3c00360303c0922034a0500c0707600d5915000503940c4c40018200190303291a50801810729060003450580d00501100c00c2c003200035030511443d13801c0080101165424a8205005e5a44025240160068200008946007020790300641103c5860300b552402102000404c42000100700705541c44801c1492004180442040c02d8101c3c0056030080010720300290001d40d005a032a65008201d900c918034030720010760344200524951601c2d0007056042a030001e018498402c4030301e0041e40b91803040c030071801440b000140c0c0001e024001c81882c1018401d600940b1954542080013001501e40b007100340d9010740750814083c0e00300f195840350780719003038040d0b8403000c8071085102c11039541d134004180358080c400f05000000020f401802034001281d80c00e60085401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 573767257 1250 573766007 573766043
    0x2001180c090b01110c060c0f0307060e10050c03010509070c0203070905014209030c0f0e01060f02072705040f020f06030411040b010c020310050403020d0e0a120305040e04 75
    0x88103100310b1281044100700c09000203c000055032144540103c2d8103541d186040702c0b0360361400c000010321002900001c072340d100c20300500e03a01c040002c2180c5001e032000c1d140d2165001007200c0040b00c0741444000d041c40144001e040201456901803c0d0341405500e40c03990790002841c0552a5010240090b01e41d40180300b1110500e41503103403c03c401038000d556020001c0c19003869464943c5e155028250102180c4080707100d0103182008541100f030281e1b0644d10381003118140c1c1614000d40c1c2c031344d8014000008805102e000d03807200c601307a260b01030032030700d4204481c15121a040990801d00d1101500c80c1d000946000d00c0b070140640d1288036610f110003040d2060060711800c000609215080500070040400e03404c0440c130045140440300042d8500340c900050301c0c0350905c1c10029405d0310901c10510400d8a0311383c0b203103000c0c50003074080f00c10007400703240c04036040e403103a0758060341115500300100301180441c070407074142c14801c1c1403c03401c09485400010480b0011a400d940b096003095103e80c01c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 573768507 1250 573767257 573767261
    0x703300b03010c141206190b0301091503020d020d02061c0902100c030813150501090507020f062e090903020a11090f15130e0a030305060a0302012001180c09 69
    0x1072801a01300304e41d207071020301040740c3d07a8007030b2481000820420000083d515a11200b880c2c65582e0411003400d2295258441c2c808160024084c07a0003140c68200040010700042c0039030b10890f94010052401001264240039414003485802c03a0004410300c03201c104e008004120681308540440c0008240d003e078010001c0c50700840c0c8001003800045100c03c1c000ca640b204106900098241c0303201c2d0501024038001032031070546a428000c480c5490000704100c42e0310341010340641c040f0360850711a54600d168007034607030304103542c030394084d0f411484001070510a420340032200e13111108181c40129612000a01a0303241e08a00700c0041c1c1250180d00b04104034818005410700e01540d0341038051400c1780b4420010030b0003420740e95040c2c0261000820f1507846070114004031400c40c0303040c060010400050369813403413000c4c81180420305150020340107042c10040a0222a0141e407154501c14465038181c0700202c106429160079500da210740c01c7c1031a1049500840684640c0c09642071504c1c3c41640d0003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 573769757 1250 573768507 573768521
    0x901170c0618010503090c1906030b0a06080601030b0a080703050309120705030a201908011109030a060c0c0b0f0106030b1909020f07140102040e06150703300b0301 72
    0x84a0041800b519059a007000c0d004000d031902070030480d5407a286e82000907d480152087ca61f842501070b40e0200324480700200401c11152207450503c110040d00c010000c524080c2c2c0a40710015500000180d5258400d40002c0340015000d031000700d1141e200e070740a50411016800546141e800010f1001c03041c1095000320b002c0f002c1c3d15010381109402e00000a80f0b941072500c02510b494030800c8680d0b800c2507151781e100d0b0003800080100d14000d000c0c45038031000b070039507100301d51b4654a440900308110381010300f1215407080050242540300507540d42c0a00900c0140e28071010007010490b030f01e0014000498050007125001ca8402c00d942c90020010151021524114010650080b9280503441d5003944d51044e16001d04000d80c4540d804901d2000f04c1c068004094462000701c40176941e8604107500a0068800c1207001202595918082c00303aa50691011103009c450108400000b09100700348060b03640307440800344e8064401c0e4601d80c604107421840346130402d035502d1030f122035186400d2103900f07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 573771007 1250 573769757 573769759
    0xf0c010c0c03022707020f011a0105030a23010303020609060112030203030f090309060a09050f060a05070b0702100c030c020f16060806040608010e060f33010e0901170c 74
    0x4104022035035074003007080214400240195880c94108007050621542004100140b01c541ea907249485000250348001e0960241000e528203051036440145002d40d086540d101a11a1071854442c0c3c44030200070b00a0b03601c0b40340007804600c41c1c1d540100c41c0b038500074000c40c040d07401015907050a030041c1e810004107911107506010380c02403140000341c0100540b580806e83c1f0180012a546218000d070440c0300300c2c40c03100c0c2c0c44000041d0b00c0c46202c2d0048442e50540c0d0041c1e5600600e08070303400900ca8144110100e60000c26004d010707860000e24203846083e0303c00031920603144500c80200e41c0506880c1c01b45551004603481c2c1c4001c0904503810032000718800400402400c22aa80c000d0300c21080c1c0450040a040203d0360001460383c3d191070f00807100a1180200810811400d602c0d03050300c40c0c0e42640c40350807141d0080c0101c0c0a84980340800c0c151100030540303002900944000c48c45401502d0004070f810300c109007048030460360300c014030136000300700c04010440070142d404d860350300301905032800c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 573772257 1250 573771007 573771017
    0x5041b0315061e0e0a120507080f0303010b0d060503070b0c0606013011131508040c0b07020d0c03200603040c03110607060c050a080a0c080604111b0f0c01 68
    0x10407030b03140c0c8003141043da82107038140e5607003944030710030215408181c820382d154000702011360015525503404540b18000f8040c4c42134a180079103c0403031a48403c680d480c01082070380280014080b060204008014504814200042d401d560398042801d2548a80c00710500900220718051aa0010f00000d41d00c59400d19012000c01d0104c035114649120900f0704282e40840703c0c19104101600784d000050342040003440350303200e20030802c0c042100c0005000b01186013010700941b6119601695000f80034560100c00d00800030b0070807120060360f0304407000a82e886003016214401052041071818083d46c05140b0300785648001c402122440705c0d0790101701d40030705005c108200100c0c1c0d60804c940180d0b60310580c078072078090819002440364052035002800c05883e1800030103105802000a04001420340c54511a590340d28503468200c985034544400132486040004500380352590000c174007480c3c44be07503050a00c5c5a810081c1c400c14060800c4d070105910048154150350340421040070100001d10b01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 573773507 1250 573772257 573772259
    0x60c070201030605191e0e0c0d150806010902030a06120c0e060102070303120b0d0203030d0f1508030307180801020f04080105010b030412030906110c060f010509240a05041b0315 78
    0x1da0410350200c2d109800341c006c691400000260700149011008080c10369100c035090804015204845e40991081c1180b41d14103001e14a5507440004c0345811201d0020243c41c1680ca400000c0c0e010350300043c4040080c0755950030104113040d9102e84412428018001038060b503080002940446030041c0c00c0364155480480d0410010764072160000301c18000f031201255000039000442e01d17010400c00025410700002c1101c0180c0425030b40914840c40c11b81c40700f403101041440001d0f40c80d021034082d200061304100002800d56020360000e4071803500e021100904580c3d1030f1442401c9030071030f032442d80b544200058100000c040034000e080c00351209001e01451410a0f56411219081c40f052005c140b58840e0b4a0106000c80c0e50701c614140c0410107241595507054601143c1c84000c1200d41404140c2020000b08403810a00c80141c41048000c001c0000c4410100024201e10030b40c00700719a00000e0984089074544a9000c1c05090640040307040250410000340641506c8140c0c2c035410304c0260707030700b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 573774757 1250 573773507 573773539
    0x305070201051618030f030815094606180b0a0e1b13061209120c08190203040e28020703030209090c04081506030a1e05060c070201030605 61
    0xe04800850141e081141408134850385903404c1e01459030003d0a580420b0100400f4560080301c0184070341e00103078503041e030000300000300b20340790b103003600c0300d24415240c10001c0100d06007011a40c83c600300f5481d2010740e0040c100c5200404840708030064208292115003c000c1d00200000b40343c0c414140440502000908c203012540b0a1a5442101030450282d008501030001e9096090142c6403540542c0b641d0b04007100c0c0d9405c80041c40d10a400010705d910014002c085036910a030400c5550195040c0340d01503030524101c0b0121000b01c1c054411920800002040000781c50b9803c08a061076001b66489529041c5403884603d03001341480340c0c0041340f5580000301040d0900141610528000040e100c1100d030904074002d01845c03140c2d0350072898030410702c403422074480d0140044420807004c0341c1a82205045140401c10103440c03260305903004208071800101206500340003984209040003000019469807884c04030151140041614000f4040c8250f5030315004801c0985001c0d200141000c01c109 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 573776007 1250 573774757 573774781
    0x30f150606030c0415020102070210020105060904080a0311030f011403030c0709020f0910030e070504020c0712061401030c0f06170a0504051903030506040b030a0c030f03120c02030a030507020105 86
    0x104001d01c1480d0010018003060500820388000c4d05416418001c50b07180c0000c044d0013940501010b80c85200c003101c05c48403071881405038911840000d46110742503103481c3d9862903c0d40040f1210f0341419110115142071104070300c06188284440b8804100340d524100420401030341a560490003a017003045926100b1030001118021240da04200603550710712101e000145004c0c2400c506e0780500d4000b903003000c00e40d054000c520b11410b080b003690126a640c508000891203204030a403800c1e000f51a08000000c480345010800501811020541002c100140790b05d09078260011110316908841c2409200240d2011601800c0a41402e001d03452030000f0200346402c0052041c0005038071a00000d040160605c010410b5112200e220981c0480300d19015014107400c036106809185400018501481c00150f03407500c0310b40104850940505680340c401582c04405015400c1c80380c01c803004d100840716803085035507081c401d90245403908c0300b110b03005080e10300180002c2c1c02c40e130501c82440780780343c036076 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 573777257 1250 573776007 573776011
    0x111030105120a0803150d0f080a030c030e150a060509040b040c12021309150507021e0c0d1704180507110606031902012d0f0504080a0213090f060b030f15 68
    0x21b906043c41e62000d00010b4246081d604005020101000407101009048000b400300032919803400c0c003a004003c032045049a0b0030144203581a4400398050f10101001c03543e06400000d00314001c1051516200031a00540d0140da0450310030082c1d00420061000341c513100e4003e40f003811100320030009a42c00280c0180400b802c0104401ea0f01c0d1058010014012818808c1031440002400240307003c0c02c02030346a000d004981c003642c1009140444a140c80030947c0c9001c46401040040318030995102c3d01318003100000c0f030190700d020400000c030307203110cd5910091203400d40040c0810b451030241001042000c2415503101280d01050a211142c0c0d0080380407210141c101185001c0c0000600049880d216401d21600c00300030403d200c90781964080458645102041c0c03959080030200c06400c4a151085110700c0d4102d401c40e20a0200616114280c80603130100e0001c08560b41485440e0811074451060040b14111380e01e440006c0c07981424807000d08200c4405018000d00b10000c08800490040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 573778507 1250 573777257 573777271
    0x60c2112010302120a05010e070807060513090b1201090606060f05160b0a18051b100905010305060a080303070e12070806060904050a0f0507030c09020a0c030c140111030105120a0803 80
    0x6011035513100781c202004a10102e82c1c0003c020f010541880b0200d03526480c8034010000180030314032020583c1800f48080f5417000c00060b15414620b4600300c8400001c10958071100c1e40214070081403003403d0800d00407948202e0280c400061003501c0e149001d0401450780300004d050000c180030408003807040c513404075800e940050341c0d1183c9a036141050002132200181d00350341a018900b10505000001880d0450500b80465401507618a00708000070310000a030002c1c00503010b40f5040c00b031944203411458100758054104c0304100d4890707210a0940d04215081000500030800b00601c9141680e0b0142c42001010050840c03c1c0c00c100f10302d91030310002042e803401170083c2c1c004070b070402108001d02c640c000d800010f0707a000c0747c2d0540781c003a40b80c040c0ea02c0290355525001c00003140709042403084a2a1030407585540072800440d079015241000d60f0303413050b20b80d02001005c0080310f5100380502100e0f00380c881e5403d5034070740c100b50800c41c24010200d8454400c0d030007504a4400680c801080740c3d04080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 573779757 1250 573778507 573778519
    0x9040206071403041206020304050d0302030610030e0a0f030513050105091c08070b041a0601020105100e07031104120515010305120708130b03040209070f02061303030b060c2112010302 81
    0x514941d060f1840c410303640f0048100d220b50501d81c00340030055000c0c0d401540304805884c0d0680c00c06030100c090340001e030b507619401000000000030b0349019511038a0b6641134941600c07400182c580300c1c0d0800e10010002640031802c005090f00480000c041904003401c4242401030a0111110109a4a04c500705e8001440c60080c0d85000c2440010025220034582c02160300070743c0c1c582450b00b811041c8003814602a043c1c0d001010070207940c01030103401d22881949001c045854500301809440b030202074050010305540e81091458040d0b00382c001c101400c1107c100341002b406901d080e51600032000000c8400c6041100180300103840400c490301010200e040c1591900c40d14185903003a442401d14031159840030343c40c0068031150800107144158000c5800c0d003400c4e038802e074041d0f90805d41c1c40000381c0117800075400280b640d00c180303540b03110f80d901914001851030104004208103074040d01c5001c6003680201340c1d07400c101e4184151030010314051054281812041c0700111000441070000901c501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 573781007 1250 573779757 573779783
    0x209090f01030c3c05150405101d0909060714041404090309090911310c05040f0e010f0b0c101109130f0501170c040c0309150f05060904020607 63
    0x643c081004d4144820201807220020050507621143c4460300e10409008003011800030785180c0605098038110358020b441005004004802102d520601040c15000341d40e00f00300c0381d05103481d41f0100380c7c0720b4143d80c0000c108500380110050b12107001d61110a280100801052003009038001021300a42d0b010307034000c58804202d1405442903241a00071851280c50002d4074401c0c0a42c801d400c010744007056030f4035610b42d400c00b210500610603903e000e9410420b502d4030413032840c0e107030741c0103015912586c94000c0c20300c0d4440f1800c403141a095440007181401c0c010040c084804e14900d444020700c2c0345642c440c80c00400003045030321317101ca203172601d081c0507510140c1c0710f032604182c0f007201c2e00e003035005000201c0321000c5400d000c014228499500001072400001043c02e042e56813a19440c03204800c014591001408104400351507a12034050426880e41c29090010f42c011207140241c0650702004980c0070000c8554000300e41000b403c07103100300401020700c00582c490780c0480b00c060b600807008d0fa40032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 573782257 1250 573781007 573781049
    0x209061206070305060112021611061309060801050903041a0f0706052509140f041103040b04050606010e090109021317030408070e01050928020d0209090f01030c 71
    0x9540226008521409000304001c2c0c01589a0b00580c42600c00362208194040d84c4030501c000c80c01140c886036602049100d240021841403100004080c0004000501c0e04110106403650080c40d82d00c2590304a0b00c851050000c0602170180d07651001403200210700717082c6005154420142d0301925106c10080000c1c0c1062028044011901c0d659001070f410b201508281c40c851103080c0340c55403a59014208903591804d40da108000c04000c80c0c151001b100414003410041000d01c888120a1584c020340c1e4494a160b0b9161401c060f5110f14002c0403025090320380b90810a0500760300818460400407030103652091540c83c1581c00e8155002c5410041e2100d89005d15582e074a2000c0e00050351004510140402d02c2d880000140103840c0904280c0e4140780c1c2e2900d0080c3c42c00300c05e0060a03800849400042d0f518100044204420309607400d5144401d40300b5134041c0203d0b803112829100050300054040c1690900050b03454221400c200074201a41c55502c42c0c0e600c2d41c00c0d5000b12610404141000d03010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 573783507 1250 573782257 573782269
    0x302060705030f0307092d0918140c090f010b0a03020a021603150f050603031e27040e0c010818120f0a0305010608071e0504120f0606050f01020a020906 67
    0x40483d0318001e441e500d0500f16400b03020500184182020034401030f068000f070700300345045821a02c0502ca140c064290524010b100545103000c101000b0845c4480c03440d0110b100302121241c052a00006420842c02d00030910903650310080900650880c503800401c0b61003190002c9808c0c40f0b803640741c016110711645c1c0d030403810f00c00c404a40702503040039000b000c000c1c8440c200818020440000c0100050403148510b01c05507001100c045505030410f1040d0340300a4800341c1007400d428050b5010307070b140c1001c4040b9180712129100c00d064403075240c40c40740e020030b0420340b0521070f19004240c007d214481e08400000c0030490024001c8100402020710f401c1c28503020009506405207040d400d5844d801d41c04c2042505401c42c000c0392000030306020000034014003500b541400380e2215916601d0807611208000000c4610400102c00c10004000000e038175401482c03c0401c042c402d001c02c241e0710b101410104181d40c55070700001c2c41001d00710640075207a038001030303490012a419241d00c0007a56a034000506 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 573784757 1250 573783507 573783517
    0xe0d11060406091a0f060f0a0f0b0c011401091e090506400b0109050402030703170409060305010b010e0a051c0f020d08031b07030c06181709150310030206070503 71
    0x3403001c032504d0134441444a440b050340e10500080e80c048091035000310800448860511400052041154003880b81041c0c403401400950911400807031a25102021342c04e02e135070245d10803403005a884054200041d50a070800f400042141001d02085107141c8441e0b4071000701800d01d0600810400007003280283e026a040200d8041c2000d0f0317130040391484c0947c01c4000300e101c01220040b40034000480c180c44c0d64425503003e50340207802000a141960342d100f2442c00300d004219600003040c800041d005003207000f404040c6100320008202c0c0d402660024041d03156202e4801d08c074140d40385091080341c455400c0902030320700f02464080d0780b40ca43c0c140350314020b078043e00103504500c1c3c074083c400c2400907410095010342102c00030024640c0c54a50440c056006c1d079440100010301c0c2c0f11240340411429048002c0003520002c007500700c6034aa0381c2c2c2200b160600c9402d1030380705002058440e058504031420625a00c825000c552662610710409460340480b030000910440011840d0b500380302c41003040c0c035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 573786007 1250 573784757 573784793
    0x50306040b0603010b040905060d0b06010c03121d010e010b100302341502040e06060702030f0a12030c05090d172101170d020c1002030c010f0e0d1106040609 69
    0x141c1e070b940c541c00a0402c1b41e001e4050b00f5903042c1010f0201c1c1050400ca62103000381500010b0381c06c019120752004544c10165a0380c1507082003040881401030310054490400e0a0004031031016400c1300c108040f030300399400e0b41e50b9605182d2520001da00c0c20780303599001000c07081d40d81c58016a1a130400310310030844494041003802c07415888204281d5003d40c0114408220b024000c0c00300301d010340e0865681a442540954103003008100d000c80d480b41030401c094a0b00c01d2000301500d41201c01c8100c420f260880c1d03840242c400c15000b8100000c00d54051042454012007841c0051034008441c0100e0700c00c50340148010429000506030b104601280c00545520280010400034410150303205103241090a01408494601085038401054400030704501640184d030090102410b4500400c40d20302c0c1480302c0e000950104003c0303806404400e116440961a0b440d0300021540017080456103004080b5000d04240403e081c80c0d480a480d0020381668416400f4102040d213400c246065200107200050074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 573787257 1250 573786007 573786019
    0x2030c0102030a0911063103150c03240e040c18020702030c040b1c05100c02030d230412020307020d0b0a1a060405090903090a0303110f0a1101050306040b 68
    0x11000300d0f05150080358409014404c5151021804d40411841e8420000907408184d0701900c0d02c0700c204114101d00e10710301c0802c042100d6031692600c8040c40f540020366080082e5076100c0d0612002500761240101485082075641881030410030300c035021880c3c5005480c4003400d1640003404000340c1012000c050004c070b50040b115a01841d920201a400c80300c03049100e40582600760043d414030f03100c0d2611401c00200202100024030004031264600c8600a0310b041c0240710040d000c0b1072050103000c2c500e004550007190f445018100c40030403516141a040c0e110b0303d508010b40e02803001070711490f030003030f80201d0505061440b801060703185115880000350481140001d01c014045e10344100d81c42102005d1003803250314102c800c107004201c00030040d1540540140300500c41030600c416280c0c0d102c03420800301c81c030703048005000901c051030326403040b00080c01c00070307400924003028000c00d01e002014100414844401d0f940c0c184140e0380c1c400c9942e04011001c0009036071507440f500400301d0040c1c05400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 573788507 1250 573787257 573787261
    0x5061b0109050307030207060e06030604020a090509010f1a0309030708030a060e0a0f0c11030a0f0e1507050d020303070c062415020708030705060a02070c090501060c200108041202030c010203 84
    0xb08544030f8000050a4004d17000e106000945a230090031030a4003210010203540c07465958904003c02500b00350301c075104014488030082402c0c0c840c0e55400d406001c0d550b4a01c0f003918948001b0f00a2440c65060a045504040c428080c420340000295450550b000c0b0354182c996070b88000c0c4100500c07017684182c040d29140014413180c02034a034043c03026182c0c008420300402500d40001c0e1140d140c0e1106000880e84104080d081c1d241c03141d0300c80901d8880c0b919122040422080001e81c90000728104c1e801d11410001e4020100300081101c200c0d1415180013442c194078006501a20504d050f5001030403040d1107100c0070480010280c0c44803580345002031705110164880c11450012840070140001500c1210808192a90300006444105620200614050f0345050580010750040e65088442c0250450042100305550080c0e42c00307040d10741d560400648940c140000080740c080261182c80c52400200034081e43d003c5444c0d0f03401500500302441201074160101d1844c8540c03030000801c4d51001c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 573789757 1250 573788507 573788513
    0xc07060606080402280e0a0b0613051c1106030a0e010507180b0f040306020a0c0507150e0a0e040609030e0307120b0903040e01140f04050103300905061b0109 69
    0xa01c2d64041d900956145000c0505050540325044903043d041c6025803401c102046012010540c1c1a4040004c01010036170780c600b600410300d250881c42c4070591181d080c420902447c200404040000b242d64210380000001c9a01c441003079251090510340140d0001000904c50180d54004100301ca1a91000300070b10319082e1001490391800f44030504070307440c0403013000078400c080805680d103001d91030448500c2c0610b0f598440c1d0082d4840d00c6200184104010810045181444031714018003107c48650812138a54400502c00c02c010710b9124492400000103105d904400682d056029a00c030345c0001d204003c03401c0564240d214a030304181d151050000100b800505290140123052240190030b02948503e41203a840c0d014900a00700d074444982c004000450103564a000b28100160450302c844160001043c240c50090300309070303044042110503155484041c0e8500303400021142440d0a01141240d0043c40541c2034403419116840c0410381c1e07494449200b46544404401c00300800c156200ca00e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 573791007 1250 573789757 573789767
    0x106030804032001021b01031d031201060806010804030518030a0204020d06080106212607060506030d02010608071412070f05180906010e13121805060909060105030c07060606 77
    0x4542c0e1510f0492403941203243d50001490b82100903400b251011522031032001103008144047c03901c54000e40403040001d01320f20610051221503071a003840380e03c03503040203005441d100c0c001e84200d041040440420012070b1380301041d03c8602007075521441c10000c01c4070000b86840001807001c1d51181c0b00154081c00101c16a1000086507080c2c8001e00c0219619005a800090307011150b00c0c83e00700d00d4006d50002018400300ca002c03240c4207180c0d11b500a0501d0040a640e0300311210864030b80c0e81d00c005000213803404020510355140d0900c020f014407805d054805846a28511803203d580000c0c260b004c3c5240c0d61032440c0a082800302080b07070011540d43c4650200303a400c0d445014010f0080d40070120107030f5000801c840c8110745400c0108616481c0c1440e491010800822008401c40208500d00000e0001c800c0120381c180f2540d0340419a013806545040f9900762a40294460502042000100d480d08600c0a80c000e00908107151650b0318100c0d040b4240c455001d0040c0f14034640b541c04194a9000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 573792257 1250 573791007 573791033
    0x207060b0411091504030206041e1703070c080d300e030d0b0d1a04020607021206060901150230072004050408030402090a18030818031c0905010603080403 68
    0x12254007184c505440c0c000324940c07103580000303034000000304410300010924215949460741014003c5900f990346503001e540304410046100300d16007002641a091005000c20714000e002d00038003909004840322001340000080724840402c010600d0280c4980c84041079060700c01c5000500d050100c4030910860780c2c0ca9030b0084590704a1585032250704a12802c0618401078036030b502180420098641085903002500010412a07002404018410058503070001d0384249152300801000e150030300c0350420607d140c050b0031108074130a007001707040031881e400904440d00e0303045944000c0110858046480030105400c1c210360341e5000009204081000500488450b562004250010161440e08000070b440080d540500040004c3c40490003510f001042d01c0e41140707c00340c00050000380b141c0241c00c440b18100054000c5032103c0104a036107030750304010b071615802510107140740540346549050510000d03003a4084056071092050200102584084003544d0003003411900c81c1e81d04d2410032040016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 573793507 1250 573792257 573792259
    0x307050115150210050603073b090c09090708031207110c10030b0d0615050102010b0a03020a063e1c0f11160801020a08090d0804060207060b041109 65
    0xc100380c00a00b624807440725141192040d405030651101c501c0c130070f1016100103801294140030b80c44c000503003507401810101c11501e43c800075a009101031000301a040c000c440320a401c1c442c01c039080041e450350100c1d42c2401001d044807580010f07101c080c020b514002080c2c200500718400010003403000401d1a40c1c40f885100e5594607810000c1440501c1500c4482040300329401403146880d2074880e40c041e070840499800050008500d1074a01d40301c08066448a6424144440e502c2405101c156428001c03681060010f941c00c0d40b425203036602149148039980f00741c0d41080304070304500a100b1400922521251100c0c03400d002c62000005960211500d502035150013446620400c6407501004503645e62180c072551a8450a21942e0344c00395883c035507000c03d542c035034042e43c1c9500100d102c00c802c2000152143c1d030001610340151800107000c070f0b01d0241044e0b0207988510b007101481544042c04c42c2c0d00c594403c00240e181c0301c81c3e02d005400340100b004866405070405400d0740013200704e04068122504 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 573794757 1250 573793507 573793541
    0x6091d0d14030a05071211030619031a09150906150103051501050a050403021c0303140103080409150806070f090f0e040602090a0b0a110d09060507120e0303070501 72
    0x5080002503564450704036500d601c1180500005403601c0e6582e200c95413018045c100300441c012002c109000303c410001d9081807103c1301105100076802c7c40a40380546140200421182c1ba0a43d2950613440d0180401c1d9101c40c4e0084c40010101081800100d41c185010b034a040c0503810003020094a5220848426a448031074420400f425842406a2402840301604408800c01d40400440e140d0b8425910300781881410000000161071b5200f002d0707121440003d40008603403003407800409848401c0d4070342460b0f44d12440180301040c0e05800321000c5407502000001c680ca54011886007a82042d441141c480c050030301000032907130308003458002440d5070359075600105403100700c43c00400200f4056144804900700020f03000644a500505820000406041c007256480104650035072088401a000075000783c841c2c80401e40412134022103500c142001038200b414032000a069005289002d13086107400c400016510703008211b007c0d14003d020b002e582d9a00c0841c00d00d2341c040e00903074042490b022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 573796007 1250 573794757 573794773
    0x2031c020c2415010507020f04051017100c14031f0e0a05040b180c0d330c050301051e041b05090a080a030e010c0c0b0d09020103051e01120606091d 65
    0x140c1700e601290b8966500030144c03a5541e07840000c0c0b000a0500500741046c21468150114250304010414502c0c050000010100c0400c0406074000355032841c6103001c18005a0710444090201038000c0d80d074403c100420003e500c0c040c0d10907405460501d1303030001c14158070000a2011205880d0032071440b60380560300c444490303202d42403000707414048041000c07225044581503543c0380c80d02c0100f03282058026034001a03c28000c0502c1e5083c100014504610000141c001c1c01e081130b128001c0c180b4480180c24420305548c540030104042c01c2520000c490928210030703507551199202d81c080c3e102201c0100c01080c024501500103020b59100044081c07056501300030005005100003401042c059059465200c000d90900040d182107036503d03070840d03040c0300d0204080741003288c1c00c002d03142d480710741d001c08920f8640b54000901210b401034021302d20710403481c154400000200b110903045a184031480d02562a460070032070028a40d07a0002031b5038a0500c050a5000032000300b441c44000700f01001d0322034072 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 573797257 1250 573796007 573796009
    0x1906150806090928020a0807050108070201020712030507120f020307120207150b0a170a0215120105120c06030f0a051612020a03060305030c0f0d02031c020c2415 71
    0x60b000485500f03025602214001420409500304481c0c441c6148149121080c410b0b80042c81c0048242c204d108954401d44040020303613800250b031504483c1c0b0740000c6180c0805500c460441d038400b101e130704091585031000b00320070901ca00d41c0703c590b911903a00300b044280144401c54000e0b41c41500c1f617400166200c0c0ca0140b0116180c4221110943e200b11400d02100204601402824503400d041d60f116104100000303940c0d1500e41100075015000018110811403441005460001c16a01450741d50003800000e010315035072203071030b410748000315065202100d03141801441d20354115141c9402075008000d00c00140c001c0c964150092241220500c00e5540c0c1020b103440c002c88044a80c40000e058205803412510250300522003141240790124a681d125200c06145a004108800459001c2159200303154020701c6258030143c803c1c40614074012050419500019100e044000300d644d00140865940d00e04000025078414494255907800d000008044205141103a004400c80003040f001905 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 573798507 1250 573797257 573797269
    0x50c0109050105040b160206070c08010509010c03050601200123090d030203040b040311070f030f03030c0e0d03050c010f110403060b0105040e0a0504021206090a05070f1d1906150806 80
    0x42d00c80300d481c0317035003001740302c605104010034191801c0e6000384040114001203041071524501401c1e0550001c0355030b090000c41c00342141c4e40301d040384040521300010300c00b1582c0e010041712101c4844000da0032464845604080c010030b4100e03422000d40230701c010741c041e041240c131203080d101e07440a00c1505d84003141040305809a10003158001c28242d50b280010b40001d00507003490081814100840b54841d88400c003408031810381d50020f40e0000d40b0107070003c04041e4980108103084080d4a020218500103401044443c0d590718002018854049000c03040b15600354010362014141d060140a140c861180007120756006020544189041050501955000340101d034200c6491000a030fa986ea103034031100005100c0075104a03407080008404100302c2c4020842a80140b8586014107003400840c64030620f084010382c0101041a069a030401c00403a0045c849402410120303151001a07071076104020385c8107800707010041c140d4602100130030244641c00800c60340e81010b403501c40701900e41c1410040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 573799757 1250 573798507 573798509
    0x20f100b030c0a06051b0c04110301140a08030a211104030201090f080703242a020712060e160f150e0d030f0c080c010b100f020606100e0d050c010905010504 69
    0x800300d00300300500340c21442031b888402c034102210010388140700e41d51b40000e0107039400914800c01031100800140700b65054486c1c2001d02c0076040300e03454410b0b494000e8a070f4a0f402000d40c9a801d1080115400e44200c00c081007030080400310202c1002146405400064950054081030b0700040c0c505038085100c00c0f481c941d110949030403500400c5454510395606207074a0000c940740300819481e0f6621000400e4038001c1800c55045503402482e9003291070307a40442c20398004c0c141b50455001c40000c2021b210012104407000307420410104002009000003450404041030f41d80714801684000100000111a100c0998260250403030364102c00100c11106003401160440d0701901c64006c4000003401803500d012030803080d003814161103143e610744100c03079000385412011503511800030b00002e162200480030181100d01b4036a5208600f610001d5407800000c1c5400c0c0101400302003003041d0390141c01130f4075507100d0042c605c8141c42d40500c1c000741c540400380340090129045002c00300c0c0a40c0510284c0b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 573801007 1250 573799757 573799769
    0x6010305060c03060a08160501030c091d040f050a05060a1d10151e0510020115120804170307061419200403080a0801091407080403020f100b030c0a 65
    0x101a86074140c031107200f5070014101d02e41c0700203841d800045550040c0859a4207001c254440e041c0207141c403001400342c1c0c0101e4441ea04200e40d16038140300b11000824811502e4440001a54680e515440c018070307048440314000c0c01601c0f5640001c0704008002451512800c440c02d411302c0f0143c580f0440d1400c07110014003a0505070042e80340070301d036194640c6c03100d945050707110070400100e070b030701e000040008011044410805d003d200061100782005d030300da050107501d0761000f0408540410300c5859000618001c04945c42c2c4071180803400d0140c09029140602426925140d9000d09055071942d0f039400b25004445c0181000007020501401581d498428181c512a121601102c0319501004080c03c080c2da00e40600f41020000c1c1c50a80388010340003a601c40c0201542c1c55611100281075034070140c0c0407504c2c0a05041c1804030b005c51000e805030300300c4514104411140c13181c0c50241d007402c580341d41805051150540c040c0303040e03299800c90340e400d2000380e0640c0c0d44e04c28208288407055a40340240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 573802257 1250 573801007 573801013
    0x402060a051602041805060c04050303190903080a120b01081902210f0403140a02030901030905010f1b170f1611010c050a03050a0e0601030b07090504021c05060306010305 75
    0x254041501950090035401079001d60042c0021542c0e0008088500007000004108030002d0300204009041103050340160300101501d00b05498900000c0d640e01c10125450207d01344c84000e12092070003036008030090b550100805454031302c4804020207a84074401241134090808004402a500039110a4000c1c0d2507045182440e21400c50709a011b58803c40d9045a00700015a9011810340c001d07000500940144d10018042e041a0030020f106020f12486c00c0384804041217003e241980004c12a2400300082c01c02242d88081405c0260040c01148181b03d04241042c0c1c182c80340c03451114040d05c0340482525600c408000001d40035460708400c46140c01c03001484000f01340304107140c5100b805a003480c0d01d41954160305c4008840d007941d100107800c0010680100d480c0c0c414039054050503034444510401081003140c14449195034003018070000d801591980c01040c1c11502c121620340207807002500030356460114210981c40206910400500646000d001c20013900d00450054101c0c0c1d000700003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 573803507 1250 573802257 573802267
    0x917031003170706091b061b170c06070f0f0f05030a0e0307020d110123073c050d030605060f09030c040c02150a060f06081003080f0409060e040206 65
    0xb4102d900c0c40d0b640080318041c0d00611003000043c4090041c580014428400315000704071209104903025142d030004401d00041e4001c64418040c0c145000001541101c490303c81d4512440026845201b8400c600d2000d0003140d040003200c0743c101d0400d0007800d1017980c0e4401800c54101044502422400c015000035200304040350b080c66054201c0414103074420141c03450300781c0aa00040302ca0381e40345422503203414272000d60f80c484e68001002c4410b206000c2c0c0c840c2840340000300c40140c1c9108000d80100109100d94882c04030b91510b145118003c0e540060340f10b0801d0b1101001030781e1041d00c0034200d84e544192104007100724400c1c003500c011114040c0040f402c08041c0c101031060f64116000d0070381c052203030750803110490b500c500541c1007103011a0007400d03000d80c504030b0380002c800340280200c0e681070614404101052401401c501201d5203440e011044e034039400031407200316000340d00c0600032460108018010f442840010802c80700000001c101d51690752002e039010031422103010b540607a007444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 573804757 1250 573803507 573803513
    0xc1b0a0f270e030a0e0f03061f050607020d03120e07060c1110050418230601030c02011b030903110a06051006110c0d02061306050d0b06090904020d020d0804090917031003 75
    0x7410718a204c80040c0f00703844140811007c0380c50200c0c221403116000d485203070b00d90f02042e0014011800b910041e5a9146031201907004680140307a0b1601c0101040b151200d6013011031480e03803003d0008500031042d101880c0d40c411008064112040041d1078103d150700806200c1c0c504240d010111b02004d44030b06040515042c4244035460603288001d07161611840d103003a86c1c0042100407542405180203060090030048001400c8400450101040da0b142920619525406d545036050103080c52801142c0310200c1d1804651490041108040d50b100d120000c000b00803080e0407140c031480140c254112156a80d05d81100c6520300b1114000d482e4101011038480d50605101050704280040d181c3c6250455003c8070904601c01544800001100440c0304441220f02d80240c00895504035145400d00f243c01000a54190b40500000e128a4482d8411021911600c0c0c44054254010301e0303281e10303550340c0c101001c050002850100d40d0302540d0000d1011231000041903034041c00701602090a07030382c1540c0e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 573806007 1250 573804757 573804767
    0x1050f090d0e03100213080d021011120412030b120d0f0206071403060a1805061c080415110a0507060206010b0307120506131e110c1b0a0f270e030a 65
    0x70601b070f070380c2d02014001044040b410031810f903800f941903000700354901d03142089804580ca4a0581a01240b00300320304010340c00340184140d0401d8012101c160303840403403070054004204256207e50812241c40001c041c084c0046084141c1c00825140c00d004a07601d0710003240c442c1c1c4200d85134400310f8110640b59a00c102c10708040c40e4001000b42c00c3c0b0110a03141c00d000c2e5188240043d040c15015290f10401c03690b410080c1c0e031982c282107142071383d01050b481c170f41d00c170601740c000e900807409a500f4010100341036031f00c60340c5415030a0100b4403d41e0300200c40c0d810309a40381c55140c0540d802501c5100000604c0030403000841e48243c0403560346500e00c200044040010f0400900043d0344484100d082038840d91711803180740c0b1052040c80709442010010340d514800c0d954034104604240c0350901041000a030003045141d4214004c0700b03250b140c100140c000441940c8160080c40c048444e80c0408600c5008090395003145030407109102d040d0120884a4030300755008003010001540051008501c490300038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 573807257 1250 573806007 573806017
    0x405010206040b0a110c0a0309091b030f06170304090c05030c0d05100314010c0e0a15080c0d061205010f0c0e100207030b0f01150206130312020c01050f090d0e031002 73
    0xd96003c2842207107460005920b400c03071b844045042c0c101c5010503003003540081c12000100070303020080c814a082c00400d4003040740a06412030034140c565200c5200340c0c5580d4080d80c090300002c7c06003599400c11007640c0783d980d041400b5020420740341112076105c4a0081c001c0d244120326180302c0130710f480d200c0b1a17440050300c0301412801e8842c400800100014100800d031001c850070400001440071401d0400a050780300c003d02d03a501820410005000701a41c204a00311024103d0610501030f03207400c1800405403060084843e0003501d01100401d20208510100001600820080c0130304950044a041280d90a5000b2000304045c05000700650505d140313001400c2d080350045c0c0700010b50f251902d20b0b0301603044801c00a114001c0700103010303003240c09034281e103103008910042030b40c0d10342100c0f040c02101c0105409420b00126500d1044960002c1d012102880d1440e0000e0000d41030240200780c0c19102960005641e001d80e030808020103105030129400071340d0040007400303441408035038071000b0740c82 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 573808507 1250 573807257 573807271
    0x12904020c15092806200d05062805010809010207020303071b08160618080d0315050301021806071407030f02030601060504050105070213020d1503060e030405010206040b 75
    0x81c4900e0040035028065003410320040e100348109450103210b03aa0412440402e00c08150a4051021400301000c001c8812801d900540008980e0302c404600000c070084861201a42c403000211030b0000304003600b1650107040c00303403a840b03c0c456041022018800e000b071041c0c54030b540000e10410007076211383c2441c0e810010344000140f40800740c1d00401c1c1103900c841f04c255070718503051a001c030044030412510743c020406076010705414207210a00900b4501c552045600300861000f050a81081314030080e4000c007250001c6411001e03c464014010b00440911840c032488080d80c002481c0c207060003190320304101020703100320700d1031900104155500161420f442e0b0744824811a01060401c000490240d03014076007942102000b44101490214160007450070040203100030090ba9030042d041e0b8034021b504a4010310030124101e184002402008610319240d410701c1c4ca04580507140c00e1591090f01d005801c28004150b0300740a480d40c80c07003036224081c0168001400a00480e0100309480e8111030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 573809757 1250 573808507 573808511
    0x910030f060b0304050717072c09060a061a0f0706060b1c0c0201360c0f06121a0d060608030315011d01080703020f16050307030809012904 61
    0x5403003154002200c0854002405048001060000b44202001020000c02154041c100c2100144180d40d0300e0300240c0c0b250a180031128000e5031481075913105c51012021108a00c42290b141804285a50307000544940104c0741c907021000c109507040607500074441e90419030207403520f0050303a46485203901680c01500c0141c0d50700c2c00810100800c0c00144061282c071800c20b85249002da5004003151524010360040da85007c00d24420514201c40c2b4a100d00e80054803082084c404a038088042c0300c504800404400c1c0f00c2001040007031442d41081d050346d03101c0c0d1b039a06448280d040300c0d900301c60b80d00405070510701404007120f90a10380b00c484240560301c90403020035160f5581080a01c4d47e002510006425138502c40d41d4103880d40d10003c10300780d01c5117000100ca402c00d540000a454140080c2a41c0704142e00050040850400c803800c940c68107148100c15960034955080c490780f03c1e08171240480c009030b034403004621844414040d404000840041b50740d1505290803014130181541031009030031079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 573811007 1250 573809757 573809771
    0x201020d050f0c0d020106030302071d010509090a020901090501060e0904080306120304120809040b0306150114160c080d1e030b13050703050117011a0f030a0b01080a030206010e04020303091003 85
    0xf02092040d502a414035800116556040d8500030b420140c07a03400c64210415007201303101c0c88020b00c2d01401d0441e0b03c00c0c6c4000a6640b6400c0c0a141400c80d0308402a402c881650000910402251b01c024101d0b01142e41e81141190994200111020262409001d05038140040f8025140201d00403203500c3c1600e080341d207440d40d036059054860210000a40d00f40c480803071840c281342011b01a1004010044028242a00d080c4004005910b00c42e0b100c6410401c600310410f00d4000c40801711100300303403103150a0240d01d42034504100c0c6482d00d405402c615004851076280300c00e0044400b040c1d112160070000c100a203021300124000c0c40100203c0742d02440a40b080e03062442d69100300c0d070064110380e501103250f41c14080303022b1200c0040008440141c0c906800301400d000d01640c072708480d031001c07240e11004034403400019281c038a007100302418203205a000040d8101000800060701c03442a0240e40e0540c1c1e980501042c66102100d002e0341603001088000311624040081804402890070001802 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 573812257 1250 573811007 573811027
    0x606090d0b151207231e010e12060a0f0204150c0c090c0206180601120201030b061213050d02061902031806100305070b16120c121d0306040201020d050f 67
    0x565103d90404100d0340080005100b15203010b4920f540419050490350868107014001c200866030b2505100c40049a030044507000760f10038280301640c441c0040492031107406001c040768654101351001340d0520310f03050b00130a40c68102d0080d82c046444034441021140e01c4960245e6001c1d104160441342d0303031308600300805c0180242c4111440c0b50101d80c0103050030718203089030090544840500114580c4410010001b5500b00c48001090719828a40400c99040680c003168040c095288102390fa40d9819041024901203651402411802441214500b40910801b41d86900c001c0c2e8032140c1407100c5141c241d66000d00c54004541003d02c040c0500c04010109480c20f007840b8040e86c1d0214000b10041041080c00f80030064003000c3d1174050429403078110403210400e05101c9001d0001d007002274600c0000682402244034800a6400c000c030b44448a040c02c00080c018607010102030700125044800c070b425400c0004119114660603001850b40100e07030340c819a03040c3c2003498400b00c0c504c0300708204100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 573813507 1250 573812257 573812269
    0x705010f1e0801030506070c0b010b1303080705150109020f030f1f06050408010e0105160e1201090303051602060405151b040906030302010b030d0f05070c050603040c0303080606090d0b15 82
    0x108074642d46080d459410b604d480b80c00c0100c0039003990300300f0441c0c00011000c140540911411200e22208581c0d850481c0c100034000c211f00380d8400783c00c100d80400d4502c2030100100d800c55804840541c10303181c6a803502d00e07490890051a0840750610001e000040720207401a6440f0b800c010350110050101c812144c0216071100942c2203600021b01c080780400807400300740100c2c02a810f9420083c0803528100003032925086548088c4000c001c04a4688161600c41ca100703900c1070030404c4000e0010b0003541c10050040c0c241500d1744403a44940b0845007010510100e0007074000c40d4404090914080d18084401102c08003400007404900001c0180f00c1c9081c140c2c00500c000d01460402050f454a18103029084855096a56002e5000b2103900301c2025404154001c5851171428040d0312a105400c01403207c1c0b00a8009503000003001041c0810300c0407035080e10080324440e507228100f0b56241c4080c070440d0701981e160180c01100805941000811480c1050790002031007425103103e0300b11300c0004003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 573814757 1250 573813507 573813557
    0x120c1903050c0624030129041e0902032a011d0406030302100e0c1f02030d06061d061e0306060904050c0423090109050604090606090b03011d0705010f 66
    0x203d9135005121203108950811800741c0d0b0302c031046000300304c91414900003018001024400380d110302140030503040555640d038004542100100440042418504241030040c4071200302603109108400d118070742c840c3c00c0d0711041252080a034550030009907040054a01c03222501d003040c4409801c107010308403501c41d407040d48025402039008080d0100c0309003940084030030111072900c00e500f02014103100740d15a58034840401151068030b28030421019012410340c0581885862400d081c84000580030b41e016010101c604000d00c144220a40d01c2010001035105400b8641b440142c4104402450300146016552081d8007820030f610301a1480c0024044944c111005844010041411320404485c5200c071044003074004070b6102d160f80320074001788580b10b0520a22090075140d0340081c085450b5030b0052011194000c0c01445015260340640f005400340141c0c2038025840c0032040c0e01e80300007242110185054400c064204e48c2d090000440749000196090300a1162020041105100703402c41c081c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 573816007 1250 573814757 573814771
    0xa0c05011104030b15010206060108041104090b07030c02010c0906180b0406051c0603050a0b06030a0210030e0f070b1b1203040606051008060108180f03040314120c1903050c06 77
    0x141c2d16821807030708501c0340e44042d0441040a4444240c0c40c0143d0300000d03a250841e03000d09200c01c4642d9113141c0061082c100c0060a40c0190411b0408810440c0300744400340211441c0c1c5090204155030340c1c04078202e07044111402c0021391701d6002085201c0c090030a440f1101180005007103003d44030040e41c40d143c2d0055103c100010340000b01310b880d40041108000b00e44148800501a2a26540751b003a51650316150203440c1c80c1070b45010895030356040180001055003d4408050144a014007038001d00c8194107450a90080c001c024174108004075541003550601308120303061010007550003200b100c1490403008a0b10544042030300713188440c0040e603c0b5512910000c99120300700420b100342020a031a5150030700000c1401d004090782c1186086034482400300b55050081d000580842c609416403054180030300001401109004541c044003130012140400c9a22030820901303880120b12454000034415007000c01d0030700d00f460070741802410035030180c0b0f84282403c1000e008030742410401c3d5101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 573817257 1250 573816007 573816041
    0xa27030f09060c0b06040207200307051813031112040f0608010518060303220509090a03050a0e040b0a060e0a0b0c03040b09060d020a0810090c140a0c0501 68
    0x4201a03000d03100e91002806850503041d880d1030020082c2c814420315800401c0c524100c00010829211541510101500440c1c0000b03105491181c4080b0b0b000070140301b6004e801440808103881c20a100d81c0240b400da140c0c21403241e540d0f80682181d05070b010742803c90802a08001c8180d00000401404102c40a03058140ea031352450407409100355002d80c0d000310140718203100100402c0d690100b180140d85174140da241006c0e0703140c0d00041c0c00d40c4036904000d505003030a010001e000c0006140c404040d140d0070790340805140c0b82c4805c6260b1700c40d9480002000900c0130440110b0a034400e12803e004c0040240c80400c0d000c10b08070000310200f2091b00007200064944084109901c1d00c4136030b07100103102e2900c0b00e03850003040c0007030552607108038001c1c000c540c035001031352100035244c140413500d51711840700045403100b0110000600d20241a5401c0100480d5a9004070341704a003403141c100c40d485152a018590f482d4040b4403c0260800d0324283c082c4451643c00c00081030003800f60b02d25080f110664 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 573818507 1250 573817257 573817331
    0x160806031c110f060c0405010f0c1509020306010b0403020d080a0201110a030f0b0109060f050c03120408041d070503131b0b040f09231312020304051e090705030a 71
    0x159524010000a0f00c1007950700a01c14800a848040c04580940b0801c3ca44140034144805055900c540c0794680149004481c010a5840b0321569000c3c2440c1403088040d02e1569076035484c08492070040303000c0654880425082400051021801403002c0000d0b80004a0003205004070004213802c02c1c0c80d0800801c0e200c041c4843c40c020188120061001c003400c0c2140400e041440003803501042c115603106005001030404c0e0360fa42c08200f43da01c55207a0f1404400a481d140c5440102034110f40300e1174100500d00e00d0041503400c00780360214070890043c0d40b16410342e51001480c410040803541c0540e03403600c0700400820307070b403640452480c050440710740601c2d683c500e0305034071140405555010311810b03413500c0d030742403482084288941003a00c004011200740d0f44900100c000e0504401c42c00602c04c607865881e150340d10340c003c80923100300c03002100c3e01801e2100250032066209188520141d02190b0f1000159001e40031750059a08030003001d100254606100741000e039210004000400e1691140708 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 573819757 1250 573818507 573818537
    0x50a030f03061e06030c09080601080f0601060801120209061216050f0d0803161e0f080604052203030e0f0601031104090c140d0b01090c080f160806031c 67
    0x2d01c00040101e09060252081c030360040c002c61501c18080e04041684a02e400218640b0a03141704000e00901c100f0b450341541e58440183e13035245106e0300c20b6100e0140c02e000140050103052114120343d05078134418002c400c254204588c060001b0203580d407088000d100790048034401c010b401007030008100000c043e142004104240d000c00714185030301c14059030042d90f00242d40c81c0250f9030440609140c0a80b0103d02420a4600d0800324640b07000e218601d645181801d03520240910403011191150100d0b40c5500090105a4a040719564443d20303020142a040044e046c3c0d0b05103d0a01900d0001800715145c04030364280030211044401d9a0321860040c030070700c045903840300d43e0500c0846007005020071540c1c4036200c007211440b40200c568146643d003000381c1c82c0c40b180031003004d80c0195144015a10ba45c0b4140c02011103404000c000b030002000146030080c01c58201d80a0144080310000b50142040308440c2514001c1013260180500201104680c0d4070308103180c611105a2180c5a01c66160170f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 573821007 1250 573819757 573819761
    0x7020d090306180c03140609060603121e19030c090b040326040902180904030c12021015091d030d0b061c020306090703050f0103031101090506010902031609081018050a030f03 77
    0x29085180c8c58019038240101070760000740109082004520307242d01c031404030315480c64501c6012022505107000040c185040001120b588241c030071561010451000b802c4411500300240d0300440c0b070142410002070012800c0301c3c0d100744441d8002c0d495540d0682ca40d4001c12500d07001030340144089a00410f05010f01112058900d02e001000c0d60300000d81d14003518010079482c5140005080c4404007002040c0c014030911020011080c103074421b100000d06c60441198a4080e07204800703140d071901d408417a0b4002d90240d190340654086000b5410041c0307032200301c40184032200280398000402c10000105035841014406034880d404e200603100e1a015007030108288008140208052801c41000101c26030750320582c0c10349402d4a00134003407241d141d1000e4014106900e018055203d682300000700340c401d42e0015071180401e40440c542e4a61400410341c0d00c101640110203240d00300030f005112a500030313440070140040c07000d807141e10000d91b901d07001d04001d0394503c00e5000603142212051826014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 573822257 1250 573821007 573821011
    0x706030605120313141c0f11180406150906031a06090103051f0b041d3c010b120102030a05310501060f06090302030607020d090306180c031406 63
    0xd103003c0c510b0a960510f01266400c01401160002002d02540002c16210a010300b1142e40d24941c0800c036141490a040c40c40d031481003401c58440d480a25506458284298880040d020402c07409105403550342d500743c00340041190350340a840101200140d85240c40c041c10740150b014000f812a5102001442e802020000304628000c8038030b900100b0014000148280f10340c3c03c00d00e0118056080549802c0290030540710303455000b0b0610072080c00d074600c44000842d002c640401141c415240c815149607800d04280301d01c03940c116401c0c0c0903140b451244042e04001c0b11000d000010000740020000707601c04c1c0d4000044030642e5010040180c81c003a43d2080d1600501c001071141d040042105003034141c3d900f0982d5510315084581e56540030004250440740242c20000d2800f6402502c94400904400903072000340d20074032a48003c90a218004942196144426076031030440a0964854030094031000c081c20840c00a410f166801081d400c0384000065032140b9a0340c0c1c4406891052645440c0740 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 573823507 1250 573822257 573822289
    0x140f030408030f09210c01020d020d021513050604080a110106051302071b0902090f0402030103050c060f0c070b0307110d020c0f040f05070216080604050601260706030605 75
    0x8104400e000c03500d00001510803202c003100499996000d0140801c0000d14032006003000035407804c012034500800440e41c2c0c25030769401e908954441c4030f0340d28200e0391013600840500150300305889201110641d41c440f107600030040701e040459808142d071268034043c0200c4080e0b88203070012940b106070310b901c4114508509200c0c4001d1000c1401d02001031404da0403100c111a650340c2c00a40c41040113070300c880c5050b0014081c4451110f4644d40d0410070041d43c01115900d11030840000c15036900d14040c0b003600d040c1c0c1d070050001c28055540c1c03c144400ca1788043c0041444490a00c03503c41d01c29801c21550014007201e07007001341c983c01d0a20380585040401c240f865803c1e000743c10a90700d03043d0b00060b10303000c80000303d030004414880880810014803805000700041410503007044440341d0001083c081d0600c142056203450b84d81c41c034826848100644d00102590001d000410480400b094480c1ca4010070f25400c0625124030031485140c003900e42c0c45170000c04e031201e50030010780c0340800780481d0a1071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 573824757 1250 573823507 573823513
    0x30506010f0608011401120911010201230c0c10020403050c0a0501031a1017041101230a0c060e0a1103010c03140a0213051e04150302010516060e0307140f 68
    0x70400303074081c0040d4014001c001700c1080702e48889840d03a10402c0c10400302d07000380c18100041c1c3c070a400c01503102c1c101c44d02000e026609106042c004411102131724182c903201c1070b00025482d00c88010040c02c641c410101c1e04102c0c4a2200b00700015155071000380011031091000f411783d8001c0c0da080c400c035030460303501c118140b510308015141031030181c8004210740d50b0222030200d04e040c22105c00769052015010014003800c281000c0004026003841e031f4206900090300c8480c42c3d1840c44d01c101043e50f00a6a0320a0075000034814032031070760701420403681a03900c01e00d40429030a0384030004d03529090b102070060791800c400e002002102c0c1400c3c401c280c41c401d454078040c407900340315490300c1c0c418000107402c01944550004021b080320451820b0f03807014100003481c1444094038100101d803440c04840c120b0f485503192690070b04c0903a007503500c2c0004482d410b86a007030400754900085844110006429112144c03903220500c01034100784010840148a00c1104280040643d1279503e44111045100d9039a4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 573826007 1250 573824757 573824759
    0x717101d060607030311130602010614060a02120f121311030c0a0506070204060e1618031a2703180f0307050907030b100e011107050a170102091009030506010f 70
    0x2d181e160031107050a4042c18003203500c1407080500c0f01030340700c0e100424141e55014600400c03115419086042110302c10703400402c01da580b8008000040c0310ba8601c10001d6130201e5000c01c0d0009840025101076812951400e0030b0524228075607040c1c11f0115552405001c0b07080c070400810080181590104100f5401840d0100004001ca031941045004041c03242101046403800c544d82c9411000203003841d5500a509800e1400e0701140c0a00d14084520110340601c5080200b180f00c0c04158007203039044541c03017a10f010008501c1941c1140604950300c540042c1ca00750040e50840c0c14500080d2000c20011680c6413a00d03024502c44040c0ca410032842080c080380d80c01c1d40b41e60006051810760703004803401155612140c1c8180d0080c2038240c1c065800030a80b0b40d46e14900b40d000994400e1440303003070300c4001e81820702e404080d84601c0540640b5500001500007403012100039071032208550011310005103810602d8000406501d440c00d00e9000290b651081441008003d11a0900601144145040003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 573827257 1250 573826007 573826009
    0x70903080414040e07140909160b03041a07020c0f04060e0f09160e1e06100f030f24170a03050702041b090806131a0717101d06 56
    0x26104520a5040e021101c1e0b030b5003400c03550389501c0100111180d808a480d0701c0e41d41ca0981c65210b0700d402c4610311488028002428080c00481d210b0040042c0d555003008403410302c44440c044d80c1002d442a81d01c1c01c0e640441100f1041605540382c0129a01c0e0018450102148100180c0c40300410b211401036041c500f080101400c0b0b20038480c0c0107184003448071a15a43d000c6800c0c601505114803607100c8030b00c48000280780040315405401a2401138451102d00160380360084c49901c169001030300800a040c07980f131068419034902c1e10302c1c02c01d40340104940c011400158203841e018110300c0c100c0d00c01a031400040c003040d0a070b250300802062800c0c601012919000940740d440a2001506000c400156482156642c2e840940110040803030815003c40a0300d0082101209002c1c05400744039080124440d030390202201d00f1451343c0301141100b01e4549440031403c0c10b4024003003506024031140d05084200584110310310401c01102903003031103440e101e95454447c90001c0d412409240c440144521 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 573828507 1250 573827257 573827273
    0x11b0503041211030f04080c0607050c01270e0a0f0e03030a0203090a080c03070606050415170f06070c050c0406120b18010203130b06090702250f03060c08070903 71
    0x402600110a40c0075142d0110007501d6000c180c2c1520311480c08009444001c1d80c103104084c005680f2584200c40682080e401401960320903800c0144c055480040c5069441d841075940c02030300300c58480090310060300042c10301c100c000150401d0820b981601d0800146804502c619030340840050700078001c08181900782c60b02c03840060210b4041540000005503141c0b41008140d0b885503016022980d5a00d055050a443c0e4000d428111035040c100b0100103814541401a03500c2e11803d0603450411a14000d50f01c442030192030030b00030b8107016500c0b80c1c0e00300007010f210941c4120300d2078451f4160250249001802c00c1c1048500500c16868420140282034450504540e41a44003206002680b240c207001104d4101c2d0a100200e150b00000402201c2002c20b83c214035451710807800b0400e541c03281e000304101e90741d01321006401603110700201210034441da840000910a100d0130760f03a049440e5000400c4904158000344d40150b00d920702070b07029a5100c00d00d1588084585050b90700c0c1c90540e5076080c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 573829757 1250 573828507 573828511
    0x3080301050d17030703020a0e030609121605060c192309060c0604150e01090b04110a0b0706020a2a0b0a0b0d06050901060602030a0909090305071202010b03011b0503 73
    0x101515040300800c04020072074248148202c1c40340f00650322031401c0200117001c3e52102004000240c001580302040f8100000c0950003202400045d0200100d9a2906a41e54100c03044200500d4252000034002ca8024006039004015045480b80c1c0e9880d249200c41c162010011800c08100c00b04034200154005071804030b03145041983c1c495603c00d0340d0340c0024850302030300300340315424000e9406000412468041281c0d0785521440305101200e058140142224603981016000c0c021f181d0020380042c078031808440c40410f008203040b145607142c041031282500306c1300e0100c40c2c041e80052241c5c225900300121a08019103450b60384010780125440d01090b1800c01c00007442c0f5013211010a142e940c1541044020000c0a03042a004420504100c80586003ea802480755482c04401062651002c01201c140d5091600d91050707443c81e00078120000c0071303c86001d5040000c103024480004e0181420024030030314943c00460f16603100c000f05400c42c0c0c507042051070590003501041034031036044000d681e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 573831007 1250 573829757 573829759
    0x4090c050309070308070804080d020105100b0c1b0301090c06020d02100e0a0b1b0a05090406121e05030d020c06090d0e010f08062b0b060105030613090312020429040308030105 77
    0x2516500f162907c005503004642001700b05005050848003d20b905601162103040104228501c1540d80c03030f4050120303c17404642c14010303040070244080c10441042c68964080000d4000940f10741c0c1c1341c44500c2d10080c25004440140c215030a546075480c0e041104059841200300c0401c14811500e960320307510700780da0400900314214200010f0707000c820b004203150707542e040d00386050f45c1d26035914004106600030f5038118421450a400490030f00a6000b8130145603030310510720b03000c02d042511800300354028241c04940c10310041001440115090010300056a20400140240c0c10000966801c141000030302404000440c800a9005da034000c0805965601c03e00b03141da503944a24000c06c40394216030814682c00140102d821554041e155403003014280100c5e09a2002e4a40300011601448107503540d40d80114074407204101d0000780d40c450300307040e4803c1c01c02c00f440e04120142c441c180e80090b800404403040150b110030321401454007030011008a40c842618103800d40e643e010320307800103029103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 573832257 1250 573831007 573831023
    0x50d0621030c03030e0714090108030301050105032a04140f040c0516030e10021c0f14250b10080111031803072a1d0f1e0c04090c0503090703 62
    0x4800e150217640310342078000074a02030f5404251580e0350406c066003069022802103001c3d01c00092600c1010003030300e040c1d0340c0580d105480c680b41c103403901d00411203854001c4124801041c132120b0b1080300300d00500c000c10301020044240010581080555002a141140910300b010100b10303109a10000f1641c4050302140c0080c0050a5800c04503601e413102c00c486a0040240790001e0302650300080c10251800300e948403518410041c0108450840e041d0350403501040703000034489042c124036406004d13200d00058000d40c20400503011101e4408642c1e07400d0b182881a03200740300b01282d88075084006059460000c1c4904900c0207040d42c2d15200082203503116403614a0600e01d204020b2003200c600c550006403100c80301030303401050803d0140c11030459030038010b8260000340c0007054102c4890306448014525049581d490035048800784020078501880c03256420003040340c070800da0351700d0240c408030030b5841d285d40c1408500401c4804102408040c45810700820040c0000010b10340107a035804410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 573833507 1250 573832257 573832277
    0x100311121f09021302181005030604050c0c0102031303020d0905060712201005070e030d1d061209010501060507150e1207030f090f0f050f0a08030703050d062103 71
    0x1c090700501c007640c0002c1d070102d0350380e0403c0f0110085030090254003030722016240c030009240c82048043c1440d422600e0100d0020b1001034050301e450391059900040b80c0900601d0000888450360032a8421243d5000100c41c0e80c0c0780406042c0d04000c03c40d11b6030b0b800d0601e030a0590800000031715030300912400402d0030000e4640019454440d014002e2000307800c159801041d529850038586400b0407078041000c0d00d00d0075000504c61803081089100214015010b404d00e1f0341c1d1104121805c185c800e00c030740382c00c0900b601d8201e400c0e21510010240000c0a107030b81141030070300c8200b02e420b454045e4000401c0001c103001b41c501140c25000e0790b642000a8480c000703089120041814200040102458542030b00820504d041c1508900f110000712010365407a41c1d0075450f014040000c002c54001c009103c03102901c01d01907030900e1801c81c4501c0c0d40040c031040000d41e4890006203103500c5448202c0010318081045180303160240907010103055080c403c441210200313030703c1e20b0600c0c8101d000542040540d03e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 573834757 1250 573833507 573833563
    0x1e09050a12080f040b03040b1b0306010302090102070e09030a0201050c0a02071809060203011d060d08091e0907030e120703020303070f03090605070906110303010302100e0303040e10031112 83
    0x4a4000f6207600c180580c13560358400081c103054004440640d03400f000385002a004200602034402501100c0a80c1400c41c0c0714500110000e4100620150640c400ca4001180e040c002e42d0200d4417591601009687e0b9070001d420081c25590b026000c48030443e0140501000141c0109121040e584400c201174481941d13600c106016100400c405089507100000228607400d01402804420202d20081c246503200c150601019440e01080074002c00c04c00e01810305a4500585001d05d910400c0c60b01003502400d1100203681060f0079186200801e55031041d5241c200c109005c81c66040d840500c030b4909006941d100692603100c01070000c02080040d8800c2d60b40d45020754410f82c040c0380c1080003007100e0702c1e1488019101000502078140480c811054850300d461001046a050f254040c1c2250404880010142e07040b01601c00080d615020901c00030403400c03500c040c05071045441c60700d0001520301d50304164906e00e0211380180e00880c65a410300701265000503818924100002d000e03500034004034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 573836007 1250 573834757 573834773
    0xf180b0a0203270f06070b010b0f0d240b030708011412031908060402070f30020705011b03170a1107080304110f0109030615030b04031e09050a12 64
    0x30715a000f030242211640d000221031282c800070303c0410ba80d801c0301c00c1001e10030002c0c0346c0944030008200740d4440c001404110000c4001d0402d25003600041400c0180c085441e02c260b4250001c00c0918440c01c120f0421270110381d030312490040050f40c416a246044c00400100424014003990702c0c410000c6040c1c1c00c194444200d500401c0c0c843e070b0706603a05c54442401511918135298030190024205001291031880e241c42142c0d0311a0b44011003c481d0b85041e541c951030300b10a4010380c03000c003090011200d101c0c0c101200c120000c84142e0b020340302c0f01c0e080500140403103819a915201850342d4401c40d00009400005030a010300b5a5451400c0c05d0703403960311040c060302500f40482400400030030090200841000510701440c03141704d03101c060202a400f44180d00c40c050700a940010b411507000c0001c070300564440d5226000303088008044a40741d03102c070b00c00f1034402e86084000039061302203103a141c9208035501c051900240f519902e098079120010b18207103154018012400200d40c9103c041100c14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 573837257 1250 573836007 573836017
    0x30f06010219240b010e1e0a1d01060305040c03110310230105031516090305011a18060108070521071806020102091e0f030615010f180b0a0203 63
    0x32014401c00025140000024450083c040c1d0030310724008485581030824010aa907915061351004201e4031130100b08144454030a5000d008000343e0410300303c02d501d65041740c0c0041e00941c003943c501071503001010307451004c0503401001010314000034000052141c1e210101101d8002c2010a070700340514002070b0030300444d00f0507034040314940f00403040c00c0181005083d200003041c491429450380d85405064540442e54052010460308200050003115105d0369a0144403c603d00b400d0155181c4d40c84608483c0740115a00c902e60344200140c40034540481101a40d080901c2d0300f400701d0602000290880d1405000c2c1703c00d0100200f41d28041c030100c013440d0042c01c2c0301c6407080c0d040d608001c000a00240002c00302001e50541c803e0001c54902e005008071550f03140003810412109a4000074254050400001c05900140303010901c03034540d400f00060390107129203461a030f6a0347c14043c00584485039890644041c05550794115044030102140c2d1800c40c0d014880c0b003551580c11a108034151701c65 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 573838507 1250 573837257 573837283
    0x6020d051206012f160b03041b090e01092a06030c03090203100c0f051206130e0d020d1e05040506030a020c07030503031906261c0503100e010803030f060102 69
    0x1d00c260365100b1131408640700820301103000560b1094050000d0602c114001c034069050680400c00124002950700480c0040080f05085007402844d202c1803184142d908112805245a441d601d2860a000c01900031400791000d05070070b070b030b4985402100340810401620031030007415641c0401d461018000c1d000000b02542c01019952802c2d459680003005200c2d0100810019a80d11a00380200c0c3c09101261804507820302c82d103540d0b41d15181088400404001c00c4d01303515480b00200c1c0388a00c4100146090030034075402601148001210003490a00303244620f204203c100720890b035009800008503019200c0a40340b5940d40e61b0ba6802040180c45a01d50310441c0f44034444002040c4400480035502890200340c2d80c40d0b040f40000c1510040d140c1d140070300c1c001c01c40044801110200446007000b80301801606944a600e4252407841507005088200400328800100700000320b003a0347c0c2d400d00540f100c0031500000d541081d402907a6400020890340c101c03d090300100d0050381c0200300c81c580c0880 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 573839757 1250 573838507 573838547
    0x30b0103181505060306041a06010207090f0b09070e012c060412030810060f080415020a020a0201090801050103050622020a06121d06070302071704060509030706020d05120601 77
    0x11079140c140d41003140500080310301460040441c26030310340417411078003494000001803071404050005011180000e000941540b06c0c281000403003a0142c0203c80140c450b450780054801c4522080c42040c82c1c00401a130f042101e000c0e0301100c1030381c108966402c4602091000321200c51058801c40501744404903c591100000c140012a880036224402201c2c2c445e035106c01690b15034103c8540780020500404000c030b144607880ca000140701e1900940d1180c0900c2c0040400c0300540600412a84454170090042c0c0065240b10306558000e2146030003050000000c00a56240d1b4480585802000d00b496104201141265250800c4a0b5030f07079400f01e40003002507040650345c06d0040c008000e001d0700412082d003894203044880046504200543e698880680480d55481c2002ca00070741c4103000481d220418400048500d0103140090f102401203900e0b41640da90704032041528000311a0321401c1103500c17805000000f203600a051361101e00b030400b03880f1850b4484d40016902c583c6032a800c10341004d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 573841007 1250 573839757 573839801
    0xc13080304030c050a0906030209060f040f1a011b2307080303010f0e090c1e03031608031e0c0a120b060715110c0a1103010b0901080601060806060910030b0103 70
    0xc10030001144c8085910b2042c0c03e54480d101e8050b1001840701075400204c03180001d42c2c0d414405c443c4500800000c000044100c0b0b407508400403510710040701861402a1300740b1040a50300844207003040040390500c01c61800d01b035a95400c2148100c0c0c0a500010700312001920b0301542000040b018010342070680381c0b6503850310380706c0d0b40920051040503546042100826140400400d48808404020700005001c031400d50140072030f0701c107402d581d075058030041000b102080000c5a07568621b40c40383c00c0003030352030409501c6400b0549030030700e40ca250210000d06001d41e00c030000048805400040c1008101401462040c2c0000c041c80e1031740a40120700062000c0400901d40f025034481035000300d0170803900040000f103800c43d004c0c05100c0030055111210080c08160039071810000000000c0011803c1c15014003c03c140950aa00c15203080e48600e0041c070540d600071302c1140d40514196045420000d03a07200148900194120a80a042c2c0d03441c00c50355264440d0300f00c1e452075404046100210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 573842257 1250 573841007 573841013
    0xd0c0c170a0b150306071412190906050619051c020604030b0a0f060e0c0403140c0a03140d0201112b0e1b191a041e03060c0f080c1308030403 62
    0x503540d10550390321a0140000241020740203c044415a0100111f4507040651100c2034030500703d006425280d08a903403500c3d01600003120700034112001d01c2100e0200b0f10307090500a0080c100d04082d880b2000001c1400148138580b98801103031001c6c4440c4140c0c403e0010a8008604c42d0301c5540c201505044400e4100305030442150404000500a1941000b200b40da0380c4110703040e14026114034004000402013080420380340520100740742c0550080d0749902000e240000c00002095000b121604070782c101d40714000c071040c041d4400f9004940020f000c2ea5060142900b040d1003400c4926101c6020519140b0020020381300080003483c16403010001000340d200c103207a0b99200401100c214150018101c401420f00050030403410b40c510541080b1681851115417440c551141715001802c0148000202900030004905040941141551009080d82002000e40d280281daa0007031007554181c0360044c47d4401d18443e402050704004a4031044090f901c405a071310980c0c40400d15200208010042c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 573843507 1250 573842257 573842281
    0x80c0307030906110f100b0307081b1801080a0308071101052e050f0d03050f0f13050301090210080901060f090501080106080a0f12052a0d0c0c170a0b 66
    0x1900e02507120540768030b43c8240800c2d0780d0390550781c03051700c960040c3c0740d0820200c4040c0c01031004500014140c513256603c0b03012103444e10100d034200342d00354281000c1852150500c503c5d0a103802416502c0301c0c91075810b0504607591001d003180c0003030420072403100186045105540c00d45641032030900911180c1082040345040e41c203aa9000c2c10015103408060308800c0c1914840812558082c090542004801013003101c0c0c209010015030520408001a080f1840c001008003000c01c40395024603201c03024104590039000d80707504079500982c5404003000142e5944110b00d020613925203000006691980007190140003190f020703007002c0e0b01103003011550155a0300080d06840290b4004c1120a44d1107071083d43c2c13080c00d0840589902d8021101002043c1091002800075001e42012880c058070048400440b15552000c0b840e10022150b0560300000c081c802e190128106207824195844a034503440812000da11800d030f06a0785201408a0207038091042c0c42c00c0ca40c00824070301031031600c407001d508 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 573844757 1250 573843507 573843509
    0x20d060501110304052803050613052e0b040b12062d0103030f0e1c0308010b0a050d18020306040b01061427130e010903030510051804080c03070309 65
    0x4041440c406031042c03039240000540f02184d0700102601c001d0302c0003c10300e20310103510700e20081c8007040000c13000c004503000304003150080d0031107200000403503201d080031420b100060701002c003013450900070b203010311000400e2010704410001c40080c0940d48500001c001b8409040a43d401140307403035000004050214019100d01a1002d41d91203102082503501c0b00c40d6060068503001030070100040c00072074481e52512191401905102c130b892144800021880041c1e01c092916840e1b00740200b608040e0f001400301e004006041b0f0150a0502d010700240080c004c00680c00304250780ca00760300480a40010003181c1180d00502a14181c3c00c06041c041300404090081002144000c070080800c51030200485070803920348213244d40a4155050f01d5918015290169030b803024082c40c00e162034607018441e0550229520b000002c0581680c0b90140603564010080c0c03101201040040107161210078040840c41701018202d2803965840c60700c24114040c4110b01912071102240c1d5404164208007044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 573846007 1250 573844757 573844759
    0xb01110d1205100e19020d110403061506050301090e070308070b06270f090f060c04080d0c02031005040320030d14150f0a050d06052707050d15020d0605 67
    0x44080c0d6110003c108031401076200e58210311000000007541d080c40910080001400168058900058068040c06aa0400d1000301c41c140000400f002044090312600c1e0405001c10002e002491a000026145000501c95515160b4607600b4000d01c41005202c03030405194031804582c0c55688070709005442c00000c41c0e0b507078000e104a14140c0518944001022210014032024044035640c08406201c0110003404a41c0f43e4440c007d08000e030703c0303c103100d01441003c042c40740c192924540b0380c2e41c3d403411a03440703100c01c00e0007040160703480561000b069801110540e40c1001c40c21b51941d00c3c0444400616480a4400030305001d1800340c0004080300411058100c41d40c24066031101d40d000b11540c01c0141c2d464110418802d0300414541080c03101005803600c001c110280040d52200810500a0f800108460b1140d83c0e00411618605100030610460801050074241503484040d0554508040c000c15210fa40035401010800400782c100d1180f02c0700b401c1040d502d504175030b090a409814907010341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 573847257 1250 573846007 573846011
    0x20703090f0806150d020303120a1a030c1207080601090603050d052505120a050309060114090a050a02091c0c30020607020d03021b010906050405040b01110d12 70
    0x703120300194034540262201c1101502c1d0030780301d40c10644598010074001d540c005080400010142e0380600c054038115003100c0c0941d06500e0030501800440315000a005161489007590029603180000c02101c21030060b102c51100b445070300b000c0341c50101d00703910a00c810700c41c043c000b00c2e20704001d0300b054086902c0b42c0d0071503c03455500c0e14113440318081c02014880080030300290400c048001b011205405001c0d00540750852450180d060301644802c84c448081140002030001d01d000c104440f90041c4092014000304a00c83e40c0000c1c43c4c4400038021400003501c92000ca10410750035412034507a0400241581600f80c4994005c1c81c0a00703944c41d059038064250a000200c4000165960302050442d441c00c0c0b8107448600c0c901c01c211000e403002a038009100740801001a1540d4080c0c0c1c1d8580c1c0603030000c1002c2c4c4100e0148245020103040320504000003564200141500441a9401c1d50700440707002c2100700c10000100c8004a0b100c0800b0740c039125180310358180702c1d00710043d450000c3c132140d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 573848507 1250 573847257 573847259
    0x906080a08090f04112212060b0f040f0e07091112040c0f030c08010c020109081605010f05010f181a120c21010e01090c0501140717030f071106010b09030703140102070309 75
    0x11b0030405d1a054417070750140360200003080d40003407215400300c02c1825000b4180d456215601e8082000c0b00c2008540c511015940d004440c402c520070080000288081c40d0140701e550354000003e4518021f03c403920903821090804101004110b02d030400140009484030000700c3c0c0d07a0304142e407141d505482220002e500e4408460461032060142c1e480181c5c008110b1454550481c10182d0403010042c2c0c1501ea42d56a80c0301c01c1c0105805014143c000c040b0420030a01d03082c18442540d500a9002d0b072003160f0a490000c2c0d5241c1070203d03103a0444010800c6807851428020b28080c14107008603445000d522004403100e100c41101180d15840215110350000c004005203411441c0c200c1ea01084050282e080709641001650701c200700c0701e131610071125002c0e030501c5020703030351114040f80940380814079100200030051151841200190706c8140c5240c4680000c410220080d150700041c00f95182c5800002107020650b101044020001d42d4800c7d020f42040500303c1c92107000b500080000c50009881d108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 573849757 1250 573848507 573848557
    0x50a0b07111914071a04050f09071b0c0b07050a060b060c0a1502300f040f0f03140d050924070f09030f12090906080a08090f0411 57
    0xa11000d208618407801014001c06443e528182c0c081d0540f441003c1c403a910340450b1282c5440c07000d101a00c0c2c154056911035003003200300b0400058400c003035801140f0200c100081142d004403102c00d140c022403030422680700315051107420ba4589030403078000c5d81000540a005c00c140000c90061142c05102c040104d01d9030714041160038070428014000e550b00c801c20440105030140c0700c1c500c40b0f004804005242c00002c0c190f40303024200e03618540c822900c01ca40d41c5506045109244c1ea882000083c141d1081d01d0726a0340c1002d010110f00c40a4203107180150400201030150b03aa11003140000c5901c01d0702d51140c1a8140041c04007250402e50600403049071104450303242c2c14a0341c40c1c0c0c64441d442c0b881d541d2855812075880340803400307400800c000c07100008003184580c43c10aa415000b02c009078500d0010134030242191210358001c0320200c0c030340001040750450100e03c080c0f2a076801084a03641d0308085000424030442d803240a81c1c4189090340343c40d19591400010180c0519942c0402c0c6c00c10002d903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 573851007 1250 573849757 573849763
    0x30f020f0717093d020a060b0307051c03090e0a0b03010e190308090c04020a08010801051605040b0d0f06060507021815060904020712020106140607020607020402030c0403050a0b0711 80
    0x3843e40c64001681c801400e65a600c001d803a8241c200100002c00d82c951400c41881c2020900e403003d000268104100d040140421802004189081074009010b000e141101040b541c42034229000140841c9140042c20180f00d44e4440008009140001c891401e102c0610002801c00c40700c810711a40c41e020119680700300119400c440c868501c1120101c102c0c01e80c07015191444014104011805200380312090380d541c0b480a09680070300c0313a480841942c106600d05007100d1000e49801c081ca000c2101d010348160380032040350150b505e0040340e03540b40e00c400310105002e80b10010300400014181400401e1b01e83d440005402014001c0700c9103001c41c051041c50b1440d101007614454400388940080c00d6160602800900081c01c000d40014500401c0303841d49840d480c054072803c0c00607515481c2c100303e141d44101060302c030110304840440c6070407000d42c002045485407000090241b0b4011002610415214081d40e00540d0407905442c42144c0c549172610320303120b0485200c008074801c04010b800c519000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 573852257 1250 573851007 573851017
    0x50c042c0606090103080313060509030909092109060409110a0212121b0c06130212010c120908040305100b0117010e0403030b190f0e010b0309030712030f020f0717 72
    0x30b0844000b503400c50b261b010789544004c1490383d070707544041088000115648100340c03180d42c4c0b42c0050764a80c1480c000b042450000a05000d41503484000a400c018406081c2d00f201c7c40d46c0b5030f850568441059000c01c09a001e40d500104181c0c0c43d10000038001e000340002000c0b4101c0c26425121101c0307143c1c402c8520340c042c24242800340c14000c0001003801d014085400312800320600c2080c02c141c4800800d91601130115880d8a4000108050400310b04050303600074001d40e0780740b0003071111110010004100c1e02100010303d503429202c0800e4002c3c442402c0403180a140c0120a0b16a80c04103120000701400c90045c55a00080000020386040daa50b501f98a06950a1030518000c943b5280c5040b00540140030340070368004c0002402c00f030a400a5480c2c5002007079824921844285494104c03084048160301c100c030701d00010010420b82d43c0010003103a08007a444200c1c040c0141907945d04400801d20060a6881c00c0e01c0020034003491000d160107000503610a841400019407203c41d00800350045d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 573853507 1250 573852257 573852259
    0xa110106080d0f050304030903021f080105041109010c080712081503031c0506040b1002010b01030f09030c080a02071a09131e110705070626010803030a09050c042c0606 74
    0x110030703060f40102e880f0304025070f046030207845c10b101d40640b20780003d0440315104d060401072000c520b05040c0307000d4200b00810b0041c1401c480c1006000000350b0500da9500c40c2c00d40340c1d810400e800003c1810441c9401c10340320700d40c2c1c00080440c4803192002c4003070007d070350540300040d0200d440501048241760000c01c90300800e403110140c5407614a0740c410400502806041d29600c140c4402404034943c41d00d5014009036040b503030010429018000014084078048a21480018104013000b40842d801c8820380c22a29030100c542c2d0303980d07003030854102d040001a40129650700104841a0070748190780000e041400000c491002110200802c81d40c1250044840348400f8030710340d00c2c45120001c159000102c0b84c0a21111107150010b566074050501a1030740001c2d0102c2e00803401070382c0000b03003865204104c0401c81e4603215503504280307542c0d5030f9010080100d6140380e01c5c1e0f0000010070409000c11003000380090024064480c002801908101e00c02e14000182d620300319030b1983e002c500040f03050142c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 573854757 1250 573853507 573853517
    0x5060f010f170109061103070e0f030307120c0b0114010908010c02120c0a0c030f0b0603030a14032d0103050124031407050604030303060306050c09030c010c170a110106080d 76
    0x1280001e5440300191503502c05100307550391a809000701c1d06a0080000404021680d40d40e00e143c17902c00034050f0b81c00f040340b0900610280142010b1034030000704403512550000301c0b40454008a0394100c403e41c030079480c002e201107091000014064070011822200d0402601d9000c1c990f512900042d00f21000c480c00d00005900440b01d1182500f080c10003816031b1a10b900680310411503075120988526002d92080340c17040403040241c0706001400f485540c20035000c4000d507262000200d0b004000c41000796800004400010100300340342200240c05d0060603400510b041c80d00c3c0c0b1104003402d494030922098400b9400c1020003a0503162000c4120301e10307100302070329241081c00c0d604c640040361300c59095500d59100324040400c0d203a8404010307000851007642c020425504624100096034000782c94004200c03c18450303451541d6002c100c00215520031700e06000e40740c40d10700b00030301030790140c6540c26a41031000801c0310506c1e603c1409a0121980c90000748041ca940c0d40b60a0340d104448100000050307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 573856007 1250 573854757 573854759
    0x426040305010f0e1510050303040807180c080f101d070216050d080904020f0c06010f0902030403090504020310031415010f06020309090717130201121505060c031b01050405060f010f 80
    0x80c400021064011a01800f06c04210381c44001080c6590312039000f98905502107030382044a13401c801e000003814043c142c018400c01080d0f081c0509001c00c05800414540e00ca80006100701500340c45d9400180b41d4080000809032001b81010070309641540c940c00180180081459920000001c0300c080b00e40c09003100b011050281c903004680c3c3c00604056521603002c0148030706007480722000c1c2c554407900c0c5d07002c1d098551400078a001d00010360350000c524a4018820000400d0700000400c0840782c0a41c0c0c0941c0d01d0b42c2d011943c030100120ba410040000d04942c9100c0d402ea40001810b001d118a00025030a01c2e0342c803140c6202a140007813003100010f034820082c2c2031007414800c1c880340d001003e03400d00c803402814a0320203041c0408201d440d081c000c400c6c48643c1c000d5685c44000c000079045251001c010415069050108e035032098002d0500030742001034801c1300c4a80c1001200d0352401401c0c00c03114120030048079903000c0c00301600c007030301d1621840000ca050f000f0442e1515048030101007242c2c0d025 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 573857257 1250 573856007 573856033
    0x40213090b0d2001110a121101091505060f040c022d0a110604080a0f15020a080a0b0d02090c04030512182b0c0e070e13050426040305010f0e 62
    0xf203400d00035601d04100e03021201802400e803c20010070303100c1c03040020600c41000e020300201140d0517121400d0321740e070401125038041200039441001c114480c3d107000c0390994418012400400361400131980103841c2a400008880d030100b1617002c081e1203440302e4100e240310365000380034002900c22411000d410240801d800103202e0903a560f00c122000c1c01c181e0074540c3e280c410a007011034000342900c0e041400208401040000d03555040003200c5140d00318140b4004c150001c088038401450b40c1440d613540c00030341400d41d43c0d034a1002c9510350b0040480c1100c2c940024a2840da4000d80b008940510484802d80c1c1c3c4060020152001b40900340128141e05000b241048501ba403980c50190f4003d26241d0200c6100d02c90000e802103541c0110070144040749040124086814014507860030410801d000d03041d166501200c0190300540054007207015151800c180800304141000714154445540c0118180c119120150080b02d024000800c02c00c484c50a0744402c0e250921240725890304100c1c0c1e0701c252 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 573858507 1250 573857257 573857303
    0x90303051606060b0c06090c09040f020918010e01060801060501031b03021309060311030c0415030311150103050a0506010803130b07050c0303130302120d020a030518040213090b0d 79
    0x20781c5008150100b03509560b241c1100556001d034440c0c0e201c54010a00b048030b0b006003001041c0604005584030790360f515040d112105100200040203100c4d007840307000700750204825011a0080e001c40c500030082424488040ca00803d91442400d083d5428048005110343c0a8420628081a00c0842e0035090821303501c00c034000d602c004600c1c0081800c104c40421064094818080914070070b01d16140c00c0d030403000400d0310b001c071601e40d0540b040e4105851082c10001c800c400c601203c0e814108203018599802d04d1038144143d14155101c4054890000010300400043c1811a43d002c0c400b5a102039881c0c06425403688608056003c00c8071114508010194281c402042c2c0d40b030180c02a2225203101400103408c50f0b10201000f0710f4185025011320962400141002942c0482c40040481c11001500030751108514407004e0184a800f0400040480c1045d2011b00010b02c000d00071036a41c07900d40c980c848c58011601a501581c0d181003c5d44003181008284074404540002c808050f0002c0d0340c064801d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 573859757 1250 573858507 573858547
    0x24030b0a20070f0f0b1f050a06030b0d20011805060403030e030f0604031107050303030105090f0637050f01021f0207080f03071407120c020d080c06070e0109030305 72
    0x7010859940c590300400c00009004510b40d201304c1c5c0300d001d01e0410b020012405140f07506000c11860f03090700304004698a104242044510070300300070460440742e000203800c0000e10807001d0400160241d54203485a403c81010260b088243c80b2809944250b1144400c129860700500f50002400c010a00c04a40a484113624455008045503c41c0b007001c1c03040c03810217000782c030101c01203480e564080800d42d0043c01018060803044d401103007150315000001c0d40c3e92002900e00201748500c0c0c000300b14540c54040040c0341c0e440031060016680b4100c054400c0100c06005070f070300443e010605000c113061401e40c08400b40700005900405145616500c14440300080221240006608100c0c001c0024041c4000e0084106200140780d01d078901380d00d02500c070300e403825801c2e4072041d810400d000c0005e150a207020a6426107280098540c0f403103101140b80300c880144060005800890784c0c1d58510340c00101c840c80744415940c0d014410103098010742c0c145841e07000003804202e05010008030051039610b543d07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 573861007 1250 573859757 573859763
    0xb070f1112130816060207080c0306010909110901030812013c170c130507090b07050304051302030601030c0f0c060b1311042c010b090424030b0a2007 66
    0x7400c595200220f5140c5224880110f400e903401000130440309406100e0480145080005051481d8090002a40703815050040c0d00b0002e59072100b42080c0074548a0a417802c49010707000955550f102d040101c0c40d07400200e1820364588200c000410107002d1a10401d008120500c00d00210030440880c4104110340c081d503400752190720050003da9070604624900c100c0c030008010b010007151803401d00c0100031105801190301da0a00d0b0a02902c40d0f40581c00c40121601c0b0442162100e00c249040390440c407035a440a544400c040c85881041d00f0f5550081d4007900c000d807403c010000c411001038031448080305e4004c02043c0b92280410124232a5004000ba0340f000901c11203601c100b00d040d40c0203c40b0b42d0b1b4001100c03070308040750038011f132642030b03001c04216000004103803818a8855030320800c80405000c1e0440d41e80b8040ba4021b00b82d02d45070806020180c8245803011410000b60225094081d0740c8030580700180540301040101019100300c3c1004803003807151002d0203c80f101a1400c07644081011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 573862257 1250 573861007 573861037
    0x121704031a18070b0d2a1b2f0901080d030c090e0406020408121e07050118081c1104030f050a050307031206050f030705010e0d06090b070f1112 63
    0x2c1c1207002007071000310301a203801c2c0d90181d1104003c42009045902da0003120051000240d407894440b8520420070050825928141c641a0346525940b645000700a50040040c4180c01c1019200341e6001400d2a01498030714007a10750708198030810040480c288254a078903003001c20710401c10761003900184900202400d140c034040d9512a000582e0303840464055034419408a414401000244540b51100c0d800d000c00c54104000e4044405841e0510b03280c2c4001004001844000c120b029000540078690507804032200d508507050241d084e034812020f5a10f50800100000c80c10300301882010364000c0c001a1060800d421039a03080e660710120f00054820384290307070010340002c208100400803140b0030381d1036500314409491900c0a0700ca903030700320034032070b908610594500f910000792840440b017003441c200503419001e1012590f540e0110360040c5c0506d003450021403c0c86038112801d070090289985a07031003180c8100c1d089800060740d008405151700700c05003000399440c0c1c9001501c5414200081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 573863507 1250 573862257 573862291
    0x1150b03090708150405060610080105010c060b0d060e010507031503060b0d0807050706140f03041b15030203040b01060503040c0b0922230705090405040f020406121704031a 76
    0x6a444d082e110b00000301002100020001005014441c140d000307001501c0d03000c6010b075011405460703c84140117040c1000b4a10103c1d0342400001d400a10103004040c1c20b0a01150071070800310003400715030302d01109540c20712002ca922603200e4880d0441144a10168186442c1146d507400068034901240d01da02c02c148494107000b00300f480f401401d000b846540117201d0240b401c280903051030801c41143c1c04101042c08a0f103d482d500c0c50480e6031243e403003010b054600b2030384010344104c03541c01d80141004c203050280c1c01c2140d54140d4002c41c0a01e015a1003130f1080c0e0790b682400c490b01d1004840040c0605006030f03003081046080ca01a1606d982c0c000c2641201c1080300d945040f1401c60051807021036900d461401c00c014a00b03050007800b0302400d0131081d609260081014010384280c0c5030490083c0c0e0365800150911540300310b4591401c0e0b0081081c4601c50f42c5a40604000300ea18a00744c03941c40c0491368402c90380c2504d00448084990102c8070101110b0b001c02c042c0307043c0c0d2004003015080c54240d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 573864757 1250 573863507 573863519
    0x150e012c0d05160b03011508060d0b0402030708030f0408010506102118060911040b06161412031b13050f0111151b071a10090608060a0c0201150b030907 67
    0xa000150142d50304d05a2298503004045000c45000c42a103c10711055005001da151118058a80095041301100300542c44910100e4a0086258001416400041a50402030006100500c100d56000000f03201c1500c4034010041d10309412001d5002003401c4414200100301c0c059140200e03005521400180540c3c10303110300125031042072003180e801c0d85d5406104100080d100300030b074103a00c007a60108074140c103103c08142c1e14459601e10384400c1c0130107000401008207000082c21740c1c00162050b140c00905039000c034800c6e078100b90754031100d814400c00380820b4180d05c18107550075803140482d0319055a01d028188504031240f81541410003800f0000c0040703640701000300f40b00440d550326900c0158500030161100d96501c0241c4131605400401c012400b0611205148044c840c06c0c1040c00710359103400b40540b280b0100740e88140345141c200307000025483e03004214503218a5400e6000d1020741c0184504a08a65410068202c1c4400c418814094218ce03200a513038450282c0b011600010344a034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 573866007 1250 573864757 573864793
    0x507050d06120b160e120106120f03030507080705040605090406150f1238100c02091b0d0b010207090204030c050f040e100207020a150e012c0d05 64
    0x1800c1003100984000c102030401880504107a03001611813040c140407001e103c002040c1da8009240036209103184103400c084103034203502c050010b008040d003604d444456883c040c40308922084082d4040791510b8001140740780600700d40c500c00d030000e0780d52038030303140c00d0903000d45958002d107014640007075540401080c0e074081e441480e0300d5425540c950341b40200c00000000c01900d8508600e00343c150a03d08a540d091407036025148008079800e420000c1d841c0405201d90500038000010740c0d01c0307115500340302d0290307070050740e114000c900940354620a41d9403501a05041c118403258915480030420061a90120f1640614001e00052042c2e035030569440034810f09a03001500191a10360030038408100ca458044841c0700304800654003800340380200042152110414440c1c800c00a8001602200f1542d951072420003030600165054840c5000a100500c0325011100c941c2c0803d403841e0b40c10542c0744150030100c4070300b0005a560044400c0310000c0c8003001e100c214040b1100d110b1058010790091000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 573867257 1250 573866007 573866009
    0xe0705071e05030d05010b04050d0303180b040c1706060913170414031603081207170a050906151f09090219020d14030f06060d0c18050f060d0507050d06 67
    0x1800045854007413030703c50708088403010ba000c05601a030400003041107403540000d40415036003604002990440040b0300100381c52102000411064960041004100d02c1450b00750540b2070004031b8841106600312640e43d981c1c0b0660785a588081a280050802c0e00680740900c9500c0c0325080810f0802c0802e985403003a0341040d0060038000d142c0f40c8010703009046c10441007152044041380b06104cc1d1440e12002c0c2e691040d1081c01010307154000c0020a07440c043d0342c2910380700e0441d0410b001c203482c00c03460100050005545408240c01108045002016480c0c1c004d01a820024000a20050f0404030310320401c29401c521428064208000568940c00c1e00c09000b501c00c4016054610240400c07000b428110848859004e2101d4009940400c0c1c4140007502d034040008050740805454010001e500d0707004030710f000d60003d824480008500c81c4d0142d51105c0f61540608a4680213807500b0421801990316400540c001c03e00703000244800c1200d070069600102103003007040c9081080000c8000b5107041d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 573868507 1250 573867257 573867263
    0x30216050a172e0b03030f0f0919030b07140306031005060f0303120f0c04060926032205150909060f105c1b0906030102040e0705071e 59
    0x1e401c2d18415450076030003001c0800d13000f00d0255103490b50300b466042840c000c4001901c0e00e200d0205103c3d0b0700361a03000314000b450440300d880052a80d6640703065400c0881c00c41e182e600140d56100711119032581441964040c80004000d04030f0014603e403240c00626000b480c0551080480ca005004c5480600041c110600051820340c0c1c54500352080c8200110041e058021024007084100105540800c41d0030030350781c851201507143d146030109a11092070b015006809404005030072444607291102c00c12001d2064200d00e8615943d0301d0400801d42c0f4080001246030600300402c000c1440c0080b1140e501420050107c00900040d1002ca410181d04184a4011480302c0c0114012813980080320f00d601c5030350911078200c5600907000c9240c2021601d44903540702c49040350441001c2c0c4202d1071802c07840443d00480d4400346c04054401260000d011040b40290448000f184d0a404d040c003c94040e920000e06080607922001004c0307401d50300034401600c0c00040201c00d0070b0b880490342031440a02d80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 573869757 1250 573868507 573868573
    0x50609090601140f1308030a02030406140d020a110f0c061c200a0305150d021c0b070207090b030f060f1005040c1101050f0907061412010b07030216050a17 68
    0x12050240400e44150040c46c0f4a0340300340302098107e03a00008480070b803021440c1030001d03803036680b81012060040c9060455804c0c0003060306004103a0007083e081c6003948a00c01c549584007100602c0b030700c0e44810300c0f1154002c5030070442150003031005d062041e5032905150380020540c241c41d011400240c1840500b0311003010000c0c41184080d40340c010160003c4142034501410f014210000307020640300c00000f03000b58a4008407684443e00c6445040102c3c1c1c22440c581d9480c6480700f00207483d89128000c160b226441e0040c03004090030001030a400070707040c00c80280080e44842a01c0701c10220300034098680800100d8000c11942c849010b0200c01c180640c454940d030740e28908107a4290784005150f102600d001d1802c000a0840000741c0004440050030105144141000a84107502c6940428090440710100000d4040c0115008010b8540203500f6200501d07031084100c04014410b20420743e00004685040c45100c01019078149048121022501c280007181400c00030754010100442e0b1904c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 573871007 1250 573869757 573869767
    0x90a080705130612030305090a0b04050607270620030f1c050f0604151a0310170307020114091003060f061103071b030507150f050301050609090601140f 67
    0x800c10b00c5208001c0d1000080c284590303410038100400190b4440300c054201502d890101c1c0000c41c00340405029070f9088040e0254034a02400e0282c0e03100c8068841800154103403507500701002203000d0708d515152400c102464450301d0032400312071650910b2072036111410074a82e00904400208000c0c052001c06980c82612083c4002240d46010321403406500c200f07062108000d01542003208243d0302c0841150b0000c7e0740e0302192002c11010712140c009a0141140005506002c00b202002d180300340d00e551200500c0e240c43d02007400300b20b1390b02c1500f03400c694810300c190310056020380b00401350140540340081c24020914000f680000d01e924919021966501040c4960718209500002401c1e0a0034070302c0300c03102c9d580c12680c3d9078482d840011305204480c0b11030001d80107d102c1d01c0340045030080c00311620551222070380c1c1c008000c1520f0250109642060280340e240c010026030f81240c5004100505201165050040460004140c0c5042103488041010031241041c0a0408800880150b40d01c079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 573872257 1250 573871007 573871009
    0x2c0c0405010501030c120906060506131a07050a26030112020301240e06060c0d050a0e0a05010804150e0f0a030905040203150d0c180906050708250203090a080705 71
    0xc45068101c0c41c10942000300c1c0004440c1c10034020000c070300c02e883c4009403800403424101d004000581005a001000142c0f5900aa003c4072000083c0d44000790640c00c90340d0642c1c0c21050300c0c402c07a40300802d103400c22161503002c04c140c1c41b01c40c148040062200d20f0880000e03c8000d1550780240c004078a184103412179281541400d01c1002006040c803580301000c40450041488802c0541c071a0a0034200c0c490005940d41d2590723030569100c031000d83c0440300700030080840523000303030820040c5600151646c0a414406e15003a124601201c0b810f0b124801c05e80c90300c3e142c1104078240900740c08000c6440d84403006465201300b01400810742210090300041c04a80740040580216a226074030880c010b000b486a0344601641000714030204a415100f0f50301a4600281181469441000107050444c1100311a04854100010b914170880b004c0210356221001541c1c0080143c0d6007001d06442e002507041c400307440d914000001f44950040341c1c18104418005406000150818041030700401401c02403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 573873507 1250 573872257 573872261
    0x4230d0f020d030c08060d0606030b130213020711100c120203090307082d0f10050a0b03030c061909050601150305070813030c0f150e060112152c0c04 66
    0x4125420f280610100000703100040028801400c407912851900501104101040e0b200d83d004550021460440385091402c05070a140194402d9001d04100a00c020901d003542c4200c3d180c090f4004264110320741d2800c02d000503004081e410509224a2202c3c9d100801d0090380ba80b501015070340d0003569900440341c107040c24a216640b25002a510005040000071140401c210a0003a0b050050302800605000540f0345004a9442d041c0c0d0b0081d81c044001500503508200c0c41034030039140504c8080100c4040c19960703c940440c2030225000000410091038001c2c901d00800f084001c00410351465a40f182c908124083c2d2005480040c821603003840d07207030140142a07018101d03003041007441c03924070a41c1c8462000c0c11401400c002016480c4402c00a45810094005030000f100000d03015508465800402c0c43c1042c03599203102c1c440c0001a900c1d94601403002c0254803546150030301101103280d10191110240d1504d01d180312000014a0700c5a501e0808460b8100d0300c01821840b110700203000c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 573874757 1250 573873507 573873523
    0x2003030c0606010f0912111f0f0e09010b03070c020604171b030109030207150302160305090f0306061509061b15070905150c0703022101060f0e04230d0f02 68
    0xc02d10028000400c0808001446c0c40c01094002c082c0810800000e00001c011481494546580910200c44010b54582c801d108003a20112a12000035044201e02005030b201c40074400e0701d2007050108002000103215100b00c1c5403940c4050845806d007a00d42200304035458031003012a419170722030030203200c0c1284c0646944400c240f058000300002092510000d40700c6c046030244010844181400615443c883d0b070485d06910300007409a1403061031803400418a500240700240324400c0c1101403101850085010750080700f00521890101103204d28100c01904814045c9910007414080b040d482604001c405200c02034150181ca640c6400180084a04002414160800080f40300c1070106c0d4503400c49105134840c5003000583c803004980e8410f840c6c0300301504002d401900c00b409200700a0103c109440e404900e28000f48007240d02c58001590540092203501d6181d80c0391008070f8003003a20620b4480748501d095000328458004c4108803450804154250300004060300311000c441a814402e0310303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 573876007 1250 573874757 573874787
    0x7020109031b0f08030c040e040f140d0518010306081504020a2103031d0703210219260403080702040501150f0305091f05060a0503192003030c060601 66
    0x1c6442007191220301c415807035450024131070300c00000840c03401000c0000352402008142185c95103854a440e0404c110902c1c24800c82d26403621101c400b21805020400d00740c500416900c99041816401021011500a40c0e59605150341d400e40890a014203200780e10b409083c1e034070071000c5810706d4414801301079000e52004501501c4111400003070240038040c0300c4000d40602d400b090140c130080c5001c95080a050f081c1c5282d01c18208000104003005000e044500d8017000e01d51110305004c00281c0c0c54005003040c0e00420104c802c401c100041c445c0c0c05480c401c840d41030400c3c000b601c1c144d1102c074169000d500f00703070b071840300108506046117450700540b400340403403201e2007680c00300462007d01503046006110b030505072540001560f082042000b083c181030b86107074a00e50322400b008004d00070001510300c2401a06ca0f028081054200003500744040300c2c0c00e0711301d1002240300780c407150101000140c0f0703000c000c0110300a20003142c1d410005000e501403410301522607421b100c400900000c040d22021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 573877257 1250 573876007 573876047
    0x120f020c0d050f03010302010c06110a120e0c010206270a0528152016050606060c120306150c010506131b050d020906030108060f06030303250311030702010903 70
    0x9904801c260f43c1680c0c11039a0a0070802d001e40e903d40f911601402c440e41c2c110309082004980c0c2c2040c140e00c44040c1c9148d410400d020800c01341e00c035040d903480301003a14055000d07070320500119101c142c1c041c0c0755810209100c0038221004d840015440c0c00d00b4585003003a162a8080d10159280c0d64006003d0b024401e1401d0025003400115903c00754031011038072805000556407035030240800d6140003c00e6080e001a01e0032230741d1305600c1a0301c00b0981d44880382540d0703034450034000408504040d0300310790034865480f0040c24284001255140c031a030008081c0c40d08a04c0b151140314090410b9000303001c0c0d01d1032600001c074003444d1100078442400c0d0f00c0381c9022070160500e03540d0004891040c0c01900fa40b126443c100341d032510610308080103842060001c542055000000040011001c0303021405051080f80d11a001d403104c40403d40d480c00b098411008500c440c007503084009542d210711185034416401c020603140d080480e15910343e0070480303caa0160b51600880b034101680014140c000b554102c043c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 573878507 1250 573877257 573877267
    0xc0a18060e011208070201140f1b01021204080a090302030a06091401060506040504020d020403080d05070f030b03100b011709061f0806060603061306080318100f0e01120f020c0d05 79
    0x201034181c0c030200f00640711100c005250f205691081c01540c004450349034507556a20103c030340311041940244150408028440042e0111140600031101320103154882007803a83c586444000f140c0d0b000056041c01d101040c003001005850900c8015810750042e100000c1d903000501f4501d01006441c4400c84c090b03450300d001441159183c809680540c2c074251001030b203445110b10300c000244600c1c0c1000d808083c020402c0c44180c4c60a03000326208a03d5503551480b40000d002c0b0550030f446941490307680c103401c40b00709064110029401b03060008414500000e15051440e0080a0b06030291501480c542080b420050840810100514440030603041510518640310b551912120302516440c4600c40000c040340065032280070344403a030910315108004031540d47d00081e03502c3e07110318424414040700300b5a01e02d05281160746034405002c181c039444581c4030f14100071111a0300010b001e03410311003107903201c07050f44800d0b126940700c000b4101c400680c0c51000601151a00d605161190300b04901040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 573879757 1250 573878507 573878519
    0x912020a0201080118060806160f080c120a0207060228090509010b16151505120a0201030b03030c07230d050d03050411090a09020901080313170c0a18060e01 69
    0x7019044841c0142c40700e05c800401181e420162045600020301c0340300d104e09200402d040140003480c600c0071b507100c0081003100100190f80030a02100c4003000c001051008403403020703032220066481f00002000505c1e105c49507985a04036004480440c401520400061425403c100320001468002e8201b120034503241400013050901d0500804640b1503001c00c103440080b8a202c11041aa98040d40c0b45640c5032802c140c4900600c0c0c0b41d00124402c0c09052400901400c20034010300c7d902008da000b40c10040ba0603001034001e00880c3e042d10303416100c20003a0180d036a40038070040004d00030400b11003040c032085c00000d03041e000d081c1c0030b05c0e40b0800b40401f60074001000007c0460803840c0c00e0501043c07503681c1d42841046444e0709013800d07030000d111000700b0407030002651062640a20841e82111076980700c02c14250b490003074015060198030350400c24440c00c10b54000350320b8650342c1d0704c04031107845502c1004562043c040d50701508241840003440c420b00d907218040c1c00042c141c3c81c02860210340c5460 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 573881007 1250 573879757 573879767
    0x60e070e0901062c150418111611130f14060f06070f030903050604140f152811030f09010b09040b04020d1b1e03020f01030e0a150912020a0201 63
    0x2180d50315000030300c0713812001c10303841c0d00c50442191000381017407a840396aa001d405501e159110079140813280307005214084c010b803c0080d40c80040b002100c60031841001c0d80d5401410301c482d004203600041640202405c1c41071801840945202c1c40408101060410180c915030400074003414816a4136620000081c1c4a041c1030f02c803aa90042c1c039107060744000342010703070b40c6584a0b0809002030207088104030a00022800310741901d043c580465078021300c480000740d262a007908800451001c000049036454549000000d4503004802c0101d2581402e00c0718481100c1406035641d11380303400441000340031045004829400a041c800030f000005078000092071201006000030038401c407030b1000c502551200c010302d0421a138808850306030950b085200c200315000a03c1089240340158680805c070440d0fa403515001c0725070141400c2d402c400102c005502500321602c042c20383e40f01e0b03050280d02043c112041c035141c1911400b00003541c8103150078940300f8016120a11425580158000750050f40d0113 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 573882257 1250 573881007 573881057
    0x80709060617040f150e0a0c0b03070903030302030601050c030c060105040507080c030a0c110a0311160305150406151206060f05030a020405090106230901151b0303060e070e090106 79
    0x1a40c09102c1031483c0045e070b956000e0360079070704641c40c1070600d06c3d04410002d5110710340341c0134a494100060f640c550300b1401e440212680c0c00002c00d07110301080040e0090b00950b8101e50f05050840c20f040c1441803451440c4c00c1114540b070103501c00001000b060809200c0c1d141c10440030314080070780f85012036407003202e44401ba1000b80810341d920f00d41c00607140f1800d440c060f210081c000b503412091160a00802c55140c0b8078040300e4038083c0c2c1e6400d500b09070081d0f007150704030703030703100001e40b11b042040385c0101e1a4603401081581c0b1030340c030f89100d802103903417440e2004054001d24030409804900c07824040708540080d0440c114101550b030f401d00032950001101244180d04440226540d078504034024013610b501e52105064055410003031802d82c9580e86160400c0c582500c5144a6031313130390800f0b101c1d403052010326900840c2e500300c00b000800c0e425170482c000250181c140480d8042d590308904070540d808840c10700005080b041040c0c800e1600340007e50050400d031410f134178030180e80760300b140c0d01c0301003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 573883507 1250 573882257 573882263
    0x60406051c021603020606030c0a060e0a12050d020c0103090f06052a0703030b100c080309014104050705010e0f03030406030213060c080a030e011508070906061704 72
    0xc141da41c072685001c02007a001c0c1000400a6444454110514024842000084000d405000001802402d000814109281004100d4040d146ca031902c16a81c20065140464129250b4200441c0040040554015051060005001400c042c10000342407104070107600b4109402d10300c0c08001b10b0801914440c480b0b420103800078450b160034409118410324040b00c03200c10340901d80c0c0070a0002188010f8034800b0302a48041c4a1000364804004488006020314008200400c0d110404641150301950740b0509900000a40424400e564040d0f1041c031a4411080c50282c19064081d20740203100140c5548084074140080c20310790348583d20f070780e840d004450400581111300c0d20641e43e0390303030130200503840074003034030782e103584071030006010754010150f10055075840c0c140062000d118030601c03c11990020000e07420500e0182084002d007031802d1541c3c0d015900d5004400780c441020341c004004003642001005003602c2d084001d4180c6441d0b511400c14050001740e0f01c03445000d04d00f0303800e1344254 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 573884757 1250 573883507 573883517
    0xf07050a03061a180a0b01030b06030c070503071b382b090b0f070c08030402041b0801060306090605060912190b040c0506211018021201060203030402060406 69
    0x10880c20040448546001007503003d1010402c1c8500080701840c21030041c000c0440906c141654040150300b6580100c202581209003000080c1856a640740030f407075060301c01c03810b0781d10b044126100c16081c0407103060f210180c01054401007002d030401c014441040244148040c80c0c0b104242012408180c4141d40000c0d03506001174681040c0b40381c2807e282e4500107e00e90030a6144280c0004001400d030841c007240d00c00d800f80041481d6044108a42e8854034240d0b0300c0242d4451280d440800607040604100d030844e4440d1030f40441440c00603462000c40c03007640d0715140c0079858440d00070281c441c6540301c500070074502141030015884050464501180a071210052011030a4419140c500340300700400c6103402c0010804104400e48890718016406a1094001e0300e440707904000031032151594a4606042201e842c10365403190061060340078480032050a0780035a107100302600c403010001012100ca42c0090110030ba2810b5130a0300e03015000500c002c40c01d5146c203030b000c201c1d01e10480c0503802c1404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 573886007 1250 573884757 573884771
    0x24090809040b06043206070b070f0e04050f04030201050f060a0e090a140303010815010b0301030b04050705030d0c150603030906110715050c060901090b0a0c031d0607020f07050a0306 80
    0x207103e000450300240210b00724180403840240044208411440d41c95070807a1204e02c074a40a4504441501c903c190030035000246500c4443c015214042540080170900c0362800450390b450307440e031158500c1081e83c40c481c03040f280340500d0000e084440050000003e8102035050000c0d0391034540f24141a18005420380e80b007510780b40c881a1a00907000390080040d01d04c4009100700b400d010025504a4040307104552103541e0460080700020424040c851900c107050004201013109100e40c01d070400e0103041580c40f0181c60b0320110341040145200d84021520b024071940c204100201d0300003011b80000c604004d00c42c1180d9000b049a0810321580c020001d036072140b954001400d11003d801800300104a01c01300c26401c0e409051500944c09590395070040000140680c8018001c0782c82040d40300c0c0100040740e60f9040f914000349044440c0c00300301503896139460b400034a41b0040502c0d00e0503000040c50705260400000b80f038501e042c20340b105035400c6010104496129068000207480d80901d01081d08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 573887257 1250 573886007 573886009
    0x90411010e040b0d0c050907110c04090f021002061801050112030305070203120907030201030e010b0a060f0201021e040801060626220320010e0703151824090809040b 73
    0x207452004981a4403251086850302000300811581701160800d03625250f0340d43d1a404141c0b2158400b80e0095015008050007410a150943c050107801d885400d007090703100219008524001000900311015a11050030300810304680740307640c03884602c0b81000744040e40c1403000b070031010b9003440c0000341030507220408180494000d0080e01d0480011845c42075a600d000b40060f5520412844180d0100303241800142900344103015040d4103100180016101c140b138260200d85c0700b004104d151045540c04e20249024819566241011035034054065031600d00b40808103003102d8060b4016414082100311001403000c554000f0316004100318031a03203032580e0b008610801d59012001c9200c0c200f08544100d030070950001c81a0101090300a040038039584c2c0ba0071428200da046038801c1c489a07010030030402c0000d4071f10500c2c5000022032000810300c10703140a4000503810720180c0484048950703503904034040e80b154810400411078400d062144416035124041248142a810750169803113500c081c100d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 573888507 1250 573887257 573887261
    0x30708030c070b1303200d11031306020313060e0d0803130204020705010c110d141b06010b0a02010509030f0d09020f150a1d06040e071101090b0103030806090411010e04 74
    0x3182d0b4202c6040c01403481c000c00090310070700135014224040f40c820000c00c1c40d1765407a041030002103907548004181c07500401c0ca041d9043c60040d07a12001c0f070b200400c02c5102c2e03c0040300340b280080c21950011925513a070382000c0e45240c8020b407c1041004021990000c440d80c035001e01d0840366401031403c550360345038000d0031800c0c035448003c040d4125000203100020400154800a070702d181a5440340ca01402019510382c85071188004400041d012481c071401c030786182401030802e202514150b14481d0030328800310303007000b00903441901004000b00d0440c08543e0203000b090b9010039040090352825104624483e5180108508e00c68036035a1904054115260f82d408000c50020050420b01c1e068010b42c088011a44800750f4500000c021243d49144095030591200564500070106420242081c02501c800c4000605c1d54042111028a100c5041800e10805654074059200d024184d030460130701034802e031340150003140120290410040410790300030014007510000d01c0c103402c90741c00110020300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 573889757 1250 573888507 573888517
    0x60a020304050628090618030804140f040504030c02031203331815091504090c030c08030a030605091509070c0c0f080d0507110f0604030f03120506030a020102030708030c 75
    0x1209804c50b503107840b40700b80c01c0301a10080300c4981d13441410840444180000254981c8002060f400003403005100c14152a030342c80c105070758040e18110441c1445800101074407000c1c0c0d002c0d8041f035500010b134000c2d8141401f0350f10484ea100e00b8950f145040164079290740031a00b1040c000030040302600280805a280030140d184000284210b0340024421000300b0b03000c0003602c1d03194a1000d085413152490400700200b034450620004165100000b14003800b025259240007110b503203681d00c0c4003100140780c05881201908038a030046071500032102e406001c136042d40d004203218140000c02c01200c100d205003a0700d0a4402615076282c81d0300ca00d0801d0f070301172100010003445078030300c14400310b14001c51020718012500c0c0b4800b111603c3c58024800c0e90503104900740a41080c8800965a034682400c403040c01455a0141680745403641c1c940b11745c884000806011000034031b1250f4140003951050044980000c0e0403006440110742c5640080d56a201d401c0004111840110000300480241d40607030b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 573891007 1250 573889757 573889807
    0x1e0907050d0c12060609030b1f03050a0f0c050f06072301020a0507200d06051302090c070b0601091d130203071805070305190e0c031911060a0203040506 67
    0x101006034481c0300500078050754441183c84070701d00031001503200e21075055a0100ea8000030112150746549003141203000d845110070b401000030740d400000041b020002104154010102515240360500d044400d419050348402c0c801c0c40000c003a05415529a0125200b16901c0b25501180000740070120442c49254014103c40703500c045040c0680c1c98120000f400310511455100d03944052034030401d0089007071980307480d402c0710b1b00054a200140320b40c0d00140c0c200b00d4141c41034050140b1940011407102081310300055042c40410010304001c04241d8803904090242000781e030303050505070005c81c20000019000b50101911002c1040b1000c0c0718044400c4c603401070b00b80c85445480b030382008420300480b032107404110302c1d0200044686102e03108003070298000d8000326050308241c0d10150050311529070100e9641c081c1c0004500c499404110140c000c07403104201030003020b01410081300702042c2c07000c000c2c054401042854040307580031086600356001180d000d61280f84a400800514007090501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 573892257 1250 573891007 573891011
    0x20604180f1b0908030a0804231207140105040b060409110306040b0f0c0405030c010c0213140702070b0708071202070f08010b0a060c0213050615030103080d0b1e0907050d 75
    0xb078a858015480c0d066a840d2182c07100300c2c0e42a501d02c80302c0e980307110f010752001c00100308402142c00030b01504080d400500400308000f1401040f100c0d218107005204030031000860000034448208180750001303008030000c2c82c2c0200300a1500d81c90790034542e54028105881190b4030200801001407c402d1381b10b07400300241c2100d85914141c908021111015101c604c041d0b00d5400001d00203c0000045030f085c3c850103070240c6040079030600103441c2c4584402041f070340807030255051002d00303184d4401d10700758805c1015482400d040c5550080c0c06c0c202e90743c2250941c1901009400c0104904a00315020680d103c0d0000c4600e20303843e00b00b24100085c2d50426400180c18810020313400d03005400c4803c42540448400408a5a60409685039100b0103c000c0d0081c0c1c070610902590031240c0d11460f40f02001030185844c4a11050250b002c0350720980040300e02036004079581c00081c05500c140c0d89114001d60350b03ca1f400c050203902d02c00114210b03112600c11810040040d550034811425180803210710750003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 573893507 1250 573892257 573892271
    0x110a0803010905060a150e090403090905040c0e010f060504031412031e01050904020102100c120207050f010f1401090b300c03060c1210050306131401020403020604180f 74
    0xa03202c081d00054548a200e000d0000d800f1800b0344182c2e0005140001a45901d80c20003d807105114804c88020310580031301000038800110400640216803007144100c60b4960040e050a11100f074620060704014065074039400180034a503000002c8906503608503d6424100f80640352907031410080c40c4043d001e01d0804424440510f200c41007140108004030001c4016a88032003d002c22101c3c1107a02a0040c0d01154195151115551020403400c046151003402d2008101d088e1080e603011020490b400e0b40890050355050302e00b84941004c9104914007070054034481c0c401031141000602401080c0d5a035209485100c0c1e95440100f2050700d20303c10165800c000444038000c41118525900d9071501465000b08030314500450068070034500240a1400c5c61114907030a4030b120002056498141400a40030903da9410005107100f010303145070030102080c0618040c07250f52814418003540d41e00520090005070741f500700395011380c0c0c1c0003916126001d684607000c03030251400b9000c0e02c02e40d42c0b034054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 573894757 1250 573893507 573893519
    0x304052103040308130e16050a1e1106090d0e010f0302090a03060b13050f13020105070b0a022205030304090c03141620061305070f0803072d03110a080301 68
    0x2c1c0105d160008442204903964642151040e0f204a5134000361213112580c107001103028101901d000e140c01c0c034203200002d281c1c081b4102c90b129516241c4001c01e00300110781c901051708104803035103e010080540040c40700008003401482d800c035156412f215410040c81260f901ca42c1c10398607020344c0104036200e0181d8a05000b0700900c40381030f0340c3e405013000c020010000c03221b500a450180658644000c1c3c0eaa42e4803100c0e0f0002102d815089040060400c060b10108406808940c05a0109100140e4842425207004103105004440c9080580768100c100801d42c1d02006941c1107640c0494007081035607084800301c0081695032034000c044100c400600c86001d292900750f1740c40f075009488091800141034100305442c100c0c50101c2000d640200e00280072549518110340b8181e125000b1141c021381c4034035a00052413040e401000300d541c070224405007401445414422100343c045c5e001550192041c40d01d200c0f075045641c000d414001855004404218100140c1e009280c11a214a8483d61629 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 573896007 1250 573894757 573894773
    0x3040816030c170702090411040212090102030906070c0305030a050a0f09120e010c020f0609060c0f010e0606091e0417040b090a0e01060903030c060f060303050304060e03090303040521030403 84
    0x40403c0d104a1040300c0344440340402081164000ba80091540c015580d4a80c1d0307051b500095100460780058090060008110300ca0350154040c44e261030000da12850031b0701c44149450b074001c040c42d0402c00c0ba2908800481d40050880790010442080424103559402ca10400b41c89841a9000b002e0300e030420400510800b00078520f0b245143daa1800201607051004403074040401c14065404000401540304a00d0010018181840007402c002e05206501041038102499070038450b041d65190060034811160911400758041421295044541065524850102e540c40042c40041050002080600c02e05165140001c0340d40201c15546e55140c071303007014891b008284042e00506000c2e2010468910b4440110b05031030456a0b800c40d02d9186440031075600b040c14805540007640c4480c0d41c22003c00500a44000d180252211562402c192616208440a040c0c0c4030300300f6002800101003030364000c8111821680b003180e460300e8000715001d08032140c054031410055684030015001042202031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 573897257 1250 573896007 573896027
    0x403020a030f0504050a060318080c06010305060901020f04050409020a031203020405030705040612330507020d020c1f02030d1b023d0209040606110d1803080304081603 74
    0x1a60350350100194102d42514140154080c4a42c0104099424003441d4805c0d8805a19803480b44405900c443c06502d99002552152600b10710540001c00144107004c2c042110903001550b4200851504440741c0c04044280958000c0c40d1091741c0f1030300441e095503140581d010285810629000d0b0180601d01d01070000d6215206643c060302688100046600d0544940821600844a041e42c1d0005aa840d58004e003241c1c150118600c00c03120070700e80c105024103da42078200c0316407000903040c00c200c58040e141040700e416910456001c2e10900441e40c943c0d01a000b500c0803003c0c80d14030041d0b121441030b03041d03010b05100c80c0c49242c60510f6007418004807804025010f50b654007558540f43c050011000d5003100942d001d0808013242030054452030180701141011044070200604000940c0c00140076182281d11150000d0f003d07500360244100207019202522103907003002e544000e11081e203030340c1200062001074039102002c400907092098500484000c1c00360809074083e81990313403a011388100c0348 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 573898507 1250 573897257 573897263
    0x9030901020705090c0315150f03270d0813080c0a0c06020601060f0509010c0b0a09140c0109051e0a0807060f09080604230d0809010b04060e0a090204140403020a 71
    0x44400020359420400d904c45c0c001d2207200300d440d24590312000b001c0d03444d841c00e0007020b4100c04c0c0760450141058103103016110003461400f0582d62810200300f0760311030f000391000405217040a4103c0110a08000402c0d54180c100d504020707282d595524071040521a102601400d0300c040003070701c810b4045e00484c841700c0c40c40c42402421401c0b41c40d82000c03662448240150360128500751003149000f4091070107403000000501d408510800982c1d141840c02500303840011a041d200c14130b041c10054120b00d884503140c8080700414403c04140002001011144969030049035000e5411600c03000c82840344130340c1c1d070014100d01d544e141c0d182d45c007a0341e800403480f0300400942041040c0314464800d00b240070403030310f40350010091503c03291518000903005094010704403c0801c4c11151a000510190181200d6500c480c001c3d894658101c0c2d00755091131005901c40c0340741a9040c44110410809150441111540068280c0c154408035000348842c8411000300b180d40380401040560020301e100750f981c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 573899757 1250 573898507 573898513
    0x5030304060c0f0801120c0f0e0a0506012109020604151e0f0c0206030901060e0108030a091706130510020f1c0b09070525110a06090509041e05060903090102 69
    0xb114800c0365400d0a00f240e52001506000c01008081828007082d000a4050881c02010981d10f192203a40407000703501c03040d0303036035001000c20514881c03034441d0307607400202820140d4800136a24140f496541c0c5c40204145411f960307041410554503640180c5001d818000300c2c01c500d11000100180c620810306400e500c036041f244036821030540c800e600b2041c40e0801500d80d0703c0407050590802450303402c0140a00f100759039608000988400359a42076008118100c0039503610044128020061142a004003151350541980ca0510020018100b0360000000103074000d8414031341b505d90f050003c4502c2e003e80c0c1c14008900042c546010000524840c0c0100c9481000c10380034004070000e44202c1410745030700c0014480000c074824000c4c0010007200c0358025040c150020240201d4601d0784440b04252a40980e898407001ca504103000c1d00e80140610707040001030b00b40f0741070010b40c1301100180001c0805000300e43d038250014a1483d607100003580041540c28500d01001040d07580c0e0000100f00340188 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 573901007 1250 573899757 573899771
    0xf1e0324080d050f0d1802030709061a03190207080708131706040c090b06070507030c06140f0717040801091103010c053c0304060f0f050c0a1101180503030406 70
    0xd0180003290b01813840f400c42e007400d058030340100100a044503100410100056136108005960601c0440041c007061600000d0b50350810583e070f1500b80301079280c025003840410901c44400c2e42d81c000c0c010032500d20706003da511012468096154061010b00401080c40410f480d886800240c0340386051b070310700c0e02000e030504c1e0401121581d5030006540103030046210070024000300310aa0840440380ca4007420441c50580290398103450f2001c683c2c17094400c034810940c04d100c03499004a41c1c0500c0d000c4458864205448081030010b01d10600d20300030401c200d1104040d019210903c159802040c0c81402000b66080c6804c04803a8202c03a200158825468803d14000760342c024010780d00d8405050440410b800d9034090001030403101802c84210400e01d0003041c18480704d1407401148107134425000441d110b07210380031080a0361203180c02c07603004904240400007a1952801a03d40d00c180515041e16940c103c504058010050244100818942d0100340d00502100000031400b80784079100c04c110034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 573902257 1250 573901007 573901033
    0x209040c080d031b0804142406030c15160c0e0612010509030405010309060204260606090c16060e030c1609062130020c010f1e032408 59
    0x140c000e11101c801e840201c0d0030b5088150300c17a100c0c0d01e41c428032910420303e4a100400351246048003410740000e2155041f46142c48000b070410700d580c1c0040007500104006100b03600007441035422481f0b401e50302440072031000c2c050644800d2800201d80c12080165009840703a5000c1404281100c120b030150044c0c0041c800404c00c14401e032803144010f400698145418807004401034880e00105954841d024400400c042541c03407243c02c0750100034000c00ea006160042c030f560500c0b0b401030005101c1d00c0d10b4030070800900069022101d2032201c00303100320010784040c9450001042a65001040d510012503004000100022006000c41e5541180c103209980c492140e001d4070350314042c005002c812090650f8180249080b02a00170b4441c2d80342c1403254424001d640407040e140522400c802c0b4141070b5139980550180910f130340484e000e1030110700107088000003a005014410b91070190881c12030091860b2446948405543c03060300012904200042030840308400290040d51414098200d1121300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 573903507 1250 573902257 573902261
    0x5010320030d0806041e0606020102070c0f0303021207151a04111303030e060712091802070302060f07031d01060312020712030e04090b0f010e0a0c050909130209040c080d03 76
    0xb080116611500250380340b6040c04050040c46140c4581441c1001844c19800010b00400001e030800e6800141c9504182c18000c4000005601c41780d0800700500341400844d50205441444c18040c2c201255038407803e14080d4501d034041204e54500300e15080310f444a201c1c0c0e0040f182c110322402c41d818030081e50f003a01c2e1220340d48504070a0041a070020002000041c0c0211000c443c04240113050078240004d68903848040b81c0454401e100140000303009002c40440c2a50700040c003d01410114101a015034002e99200c0d00070700800c03500351158000031904e610a4114024000211103103942ca505081c00b513601030581070000300d446014207840398180d103100041d288201d03107046803c15519400e944081e41d000c0141c405850f00305454424080100d003040031682e02541810020310075541c5485800c40b0700202c080d0240034014103140c4200c41031548101501c0c0d441c10100c86510036615094090841c540c1000802504401d0305400c02007800b003408045002c54440c0415950360300030340d0500300c3c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 573904757 1250 573903507 573903523
    0x14090d0504052b0b070305040618051510050307090b09091207121707021b030d091e0e040b0907060e28091b02010b270a09060501032003 60
    0x40c00000f1560000103594440c9010907492100324050381000300c2684490807100c0080320b9079008a52a40d0a100420520303205804a14039100e842c2040400145d4403103881c2c00e040b40a21095061030408116060090305e0300e4001404c0040c111058a07941d06000340190401c0002c1c3c1d0310601103000000d02d08200441c521001c02d4800c1c2c0c241d4a003ca0a41c1d480052000c48004001000380d0000d50905008607046894002c103002e8000b03105100010302d03186015403100458034043d821070f880880355680c112080300203494901410b80409a01c42c105458280f5041c0e200d42d08450340d0400f403105000750114018010354050042d6030f006525003d064485141c003011898110568001c1d40c555083e041c03010800d10041c120352804001c0d5101d14503000c3c0c80d00c184040001a2454144220b5a40c092252011300032040e01c2403045041a401090050800d1038800c01800642e02c00281fa4984250f000131080c69000000700b1040d6100d00340180c0320500314001c1c101543c2d038000c60b084a441d000401d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 573906007 1250 573904757 573904759
    0x70f0e040c0b0a0203160308160e0a060e0d0605040f05160302061206010c0b011e0905101203090902031e1e1b0c0a0515010617011e03050114090d050405 67
    0x1e210501e402800d07401035001025010460200b480000714507940104002480c0703002c0d540d00078103424980700092100b0012000e03001400f40c200d91364511034641010340700850746681000b010716041c81000ca014508a108010b20f4580b8101c104402c02c0a14561403464500071012a0706038000207000313104521080c00040e40c0a1018850301140b220444180d9510000600d03040c50038000991301c501084100303030003050300307032a400140540410100728840014480300c441846030341400c0385400c0310481d05024003510540501d4020060500440c854170040002e0107045590340340c500344e9080040cbd1498903070000380003c0d5002c55004410a80d0210803c0d800c00800315840e107500a641c110510740380b440c10100b120502c10100000c8051100d40e40450080d00a40000c0d003503c010f0f0221188160003040c14811040d00b04034003080445a164190f403207404040448100062030800d440c0c01c03d84c0018050760901c260a0841c18101400602514454044410310083c80d036054900d80220b0042c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 573907257 1250 573906007 573906023
    0x204170a17160204020d0e0f0a060f06030308010e0903090a1503060614030a05090c1903020f0307030f031409040f0b01020d091203270e01060809160b030423070f0e04 73
    0x81c0d4003502e041d034024103580c0c8544c44000b4501000c0447d0340d080c042c030f55400c3c0c0c3c1160010100501480030300c0c000d024000c0c7c00c00740d0810119046580180ca030100600414182d01c10402c00183c4456041085441c10100203000400c1240d0380c4034100d100304200c80c608000a42085c60016075240101401382490100325480390840e91100304070001484000d29100c06482106071a000b540ca800da1603910f4148452400d03c446801c5005018030890701d031305800c1c000da201800400202e281006500485030785443c00516800101254000c40e006548000b640686011420301046035160710000400314280c00755968020102400c0d21104000d10400320310318006013007540024030403118001441c0e80c1350b60007020520030020400c1ca0725060b8100401140042006010140c1c020301002d03480f800500042060011b0484044025032180c42010540c50000c00030808020f0500000304980c20040304000c4910002010030b41c0e1140701d403282c6d0803088510342c004100e02610f1444540f00e40d400400c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 573908507 1250 573907257 573907297
    0xf140406030b030c040606030f050f0402030303060d05120f1206041104062609071805060619020c0315070f05090f010c02011803060506010f020303040c060f02010204170a17 76
    0x410303000b070261112402d83c14083c00f042c603146075031544a200081d01c031a83c1d0009600388110288400c8441c05441d030300862600004100060f0b500204403a0302100941da000440c1e140d61038010700d000c403402c200012b00b08003c907011030011070b15006000744058000c0c40144503100c50f0140b00489030902110481c1136003c200c14801c035070140e004074206030310071500c00031907003611021068001c1c0c042d00d2111254014440400c0f96112503803460481410b441000c00c55810054001669407280c0c186602200b00c1c0c0e420784201c0180207220742c0d030441c1c80140642c0e00c00c442800c2400d03107003e81261034802180707502c000840d081d80310b0010340d280098080c01c01c928000700d15005461039403400c90300700e0402c5100c200305001403800c103001000035032003414003003410703b03049002618000c5c0d140004401c5501c24020400071a049800c0c10048449901340b4030682802031200300e000e03120b241c00120000134807049600e08048005036000c00603018502c07039007242c2c4140a00c001c03940305846011500f1580411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 573909757 1250 573908507 573908519
    0x22805070608101703133c090203040b061002070b071104060b0c0a02031216061d0106030f0210030c02062206091a060603010501021005090325030f1404 67
    0x1d0854103c4104200848001c1e500c02020b14a400c698210800301d8101040304070803800700c0030754035010b883e0b83e04000c124a40144450006171405400c0e0320f1441910b028024015201150b240d40074241a0405540d24a024209901103d00503244203003c1c0342030044010150f4030200c3c040d400c0c0c0324664050307407400c0380c04c4d169260f00e404800c10035640160b0307030f0600140c500d001c88024225a0211000f41001005500406050404120903c00e020804010806801c048031514074481c90707000d0b00c00109411140a443d018a0615481c0e03026903183c0381f00413040c089941d0210864903c00c85101b6121100382c8021401e0b1f0320400410b001517070211010499508029600e4080e480400100c507981e075001c3c3d2902e2061f50040101980e407402048580007250803100c0d8002d5101e0380a4034820300e50751403c00001d6450070b15140245019940f040480c0040341c0501c00c8920140000c04c0111407400c5080d00100d9601101c001240030555440c00c01c2c030ba19000c1c10402c1032040c0c0c40b80801d41080d1400d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 573911007 1250 573909757 573909767
    0x15060f0f030e010b0a030f0b0c0306010e011b0c1805130b18240105040b010906051e040504050a05160305070206040209250206060406090605150c100c0228050706 71
    0x505403507215500d130422005140c4410700c0f080d00a5000341b520741c540d0002030400c105000c0014141ca03c03180400c00421406981284040d44085801c1c82d0100c070794440c100404140110105000b0520b1041c1c0c0c1000803003070880e411840e00c1810001d070030002515041141171043c0c1040d20000d0520308542c0002c1d6100c46c0f82e45420000c80002d100740e850000c08001d00c495104c00180b280304440c442e500052003d401e01c1d01c50300f11011020300b0a81211760400c0b1000e042c40c0501002e00005aa051103200c81c10302c0c4640a44008000103041400903040501d1000058401201c52100e0343c444901403005c118428020175000300c00035009810a0380342c41d001d00c58031401c014500844014108140c00440c030400d044540c8402044c0e020b40b080e818550100019035800782c0c0600a81c5052800c2402955191401950305401544d4500d44d241c9080807094244a10100189030b207616128809000303030380126195214000c140311107420540d40c001e0507242602c140d20040c0041d84000300501030a8098 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 573912257 1250 573911007 573911021
    0x18040207031101110304030306080c01140a030b0a09020c01151503180503030f01060206090307050c040203070912030c0b060924030f071710140c0d09080a0315060f0f03 74
    0xd1034100d0850a40c18100d500f520540e5000101307000c4000200010315506100d40c2e0060402100500140400e090009001c0e00c011101c54800070340c0058040580ca00a0b440b001d1b4145025000c0c0d1000780d601c0c11100001d410841041c000c5500717100a038140801540303402c005072940300d0400e45503030920140490090524402c110090344d900c0724100e000c203400300080c521030001e07006001c001d507051940080c01e000c005411141194424402400050307004118040d03500c4041c2ca0040c3c403a51540d0040ba00c0c0050341d40075032501400c4904013814154030801c0e489140e40103284078211501c07603c0500c01c081504640c600c035211303035800c0c003054004140305080c00c10010040488242400c1100000d0804a882c0c0c0045030060500d019419140b0007807101c0494610031260401c0aa107083c3e182aa803490000c080c4030780800300044180307041032558000c4152981203000140ca85c0400c02d40034008142000b00c1c07280c8402403e2001402e207100310607c0181c8a007a0307441241e90450140c09030090098 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 573913507 1250 573912257 573912263
    0x60a0f12020714060702250501031e0c0207150c030c021c060501080705030f0109050a0f0f05032a0601050307121a040f0c0e0115050a051215040e0318040207 69
    0x1c100b00c2e0049180120401070200750340020346028140510040c0c03074124141c940380700709088182440001400070220004440d402e090218444180d0105112603005208403031000b40c3c9044a40c0a01310f60010304a800e440c00e03407082440d5603400d04415101c401c0d880000400040750482c0540040c2040743c80d200c0c9a00810541094502c0306580744011744400740c100768920b0380301a008018520301044050081c1120500801a4107299150305407903d03003004e0090f041f0044445040b0800149442800350240c21000f81e80c0c41e80150244c0d148000304004a841c64a000a1240394058002040d114100c130001001400c800e49001d0710300480e0208600f040c3d402d40707880b000f4044030286000d10144240d01c18000310704690f800b89451501207050350824101c0d11454001803248814807100810170001500700a40c40d0319512900329014414812000f155401d14001d101c406c0c1030365908104403c400311014001710b00742209103696800ba40d0407550280841c030590340d159042c190300404500740 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 573914757 1250 573913507 573913511
    0x14130c0c050d030b1801180b01200601030308070206150f0303070b01080303012d140d06090b0118150b090607020d0b09010513030c1103190b0f0105060a0f12 69
    0xc403901c80ca82400c10188880010948400103e040ca180c0114680890343d581e44071803070719504028000c0000300c118944400e0300c0750f40304502440c1d030f801080a600050004004904181036501072552506420b110880100310194003080c0c0107030001c94220300c104c0162030110141e06141d404c00a5041501c2040c0f41c0601003001028041483cbe0003001d4003910360380000355540c2d4546850014581f1048004c00c03ca16400040b0307411614090b40884201c0d4000101943c511080c000001d40b00e07000c4d01d800070281c0349401541781c10010a80700c500d049911b101c2030750340b000000954210699507958240d441918040c1814080010a200500510140540a0380c10480395901141411513241410303a81045d565003001160300c400d00405502803520840740281c8419a90003522440f0b05040041c0b01c107616130002041a01e0400c04038449182c4400001d0201841b81450f907007800d416030348608280c09620000c5081d081490840d8100f498594a900c010320041c4401c0320000400b51107034040c1a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 573916007 1250 573914757 573914777
    0x1503130c0510020c1306050d150b060301090504020120070614072a060311090913061109090906101a0412030302040603050601210905120304060c0914130c 68
    0xb489128200728940030310b0b0010595222501c0400c0510004081c804034060700f082c10511454031134401c2d038400b544d401550b100f07803040c000301100302070458204a15005200480000b82008070b0b40c0205008038002c0c2c88414003c141103e00309040800c8035424901d41d40445020045948905001d10051441200306e508052540e695640c00c94040c2102c400304441d0303a40306a00c007102c04000100181210300f0100301143c10030526a80500841c0d81d0244038040000029410b5403000d440d0034a400e40c41a000c0018880340e4030202210f0b003040346054050000000020a1300301d000030842d0007944078103440c0781150301d0f00e40548507882c510703e00d01c00646011312000508480500304090308030310946016071142d003401c00080071070b0f00080c60700e81080f070b1001ca404190003164a1000a47c1e8600380042091780b40c50030061300d80805103070040d020420000070001482120b0b800036015420716a540c00c5841c0e528440007071249032055a441d8040c40c0005001e40d07144255100b00c60b40080d42c18216410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 573917257 1250 573916007 573916009
    0x150b2b05090a0c06030e0c01050c01141006110601051807050c0d02060105150a080c0d11030114120307030518010c0f031805040c02031602041e0c030b1503130c05 71
    0x5503009880c04442030340030203074100420042100800c060b0203245000c01070b600f40c01309502d690303000e860780c80da0600c0000940000345e0322080d0440318105c050003460255504161034a00144811842600002080700328068102200494490304a40000300303a040754620350402000802e40103404c03e014400304010a04078020240440220085a41c0140c0040d43c034003818001c03558000c0c03107807003c540801c202010a07240c02485503900001001d155030384030304c01c48a2000c000c20030200409200600407000280002e403034042c2100291003683c2e1656050031581c8425520701403000300401085060040d103448007400004005850780525100c1080945612092080424410305400045000d6003400c51032900c20800001080251420001403803017110080d00c1c0d0113591000b6003034020340e481c030300290b5840e5040505c1c4804002d40c1500114864005440107004130203882c004a030038460301c040c0510740005402c0311aa0010131203403455468a082e400c0100c141741080b40d00030205500071a003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 573918507 1250 573917257 573917261
    0x32a01090e0907210209190621050c0a0b040608060418080909010e01080a2402031905100303140714120c070e040807030f0207080d05040603150b2b 65
    0x2407415401600703e0340d0a1400304446030444d03020080c80d198545141c3e9005032203802c2c482d41d111105000102c5c00748000800c22018040660118441c00800301c15403203e0402031508030501440b64003103640641801040c07003070840942c40340200d03c00c03003404100a41c2c0d02804071640c0c040001080000d4041c5502c50519880404034800e580a107030200b14003010742810b00c0010b016103018202c90182d989890340329691000c140c000206041420f00103c0802c09001e10034007411902118195284c2c5030000b42d4000002c024640003281500784008510b06408016025054a40503914079007074008013040c0c00034950021100321940c10031941c0200580c0414071240195505a9206690f52041076400d81c0c9054442c0e0071074054001e001c0103100001e02140121400103078142030002403c40705100503810502076510895a5005040c140001103038014010b01c15501076880800800b0300851114402034a03a014034655100304012228014540c6080c02e08003104000c5c3d81207a5184583c15841 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 573919757 1250 573918507 573918511
    0x606071b090209041d0c01030903020309090f090601062109050f07090213061d1c0503030702100e06040f020112090204021903060501020f0606040c11030a020c0a05032a01090e 77
    0x2030041e60108032031032507240030b01405054082c0d602c000781c1c0c91001d00050315100c03a01b004295040c90b566070100000c140c024010356641140081003690240b61007665001c40034400c4074100201c0c000d080000c54200c0c081d40310b41c00c1c00b0052120540c08a1031103010300000305590305040e1064804c00c8035120f8042c608001c84405001c09500c09a00d915041c0c000c002d41c92266040f48007402041f0f806640000c1030015480580030302150041c0c90301c00741c054001507450346010050601d000020400910030380005407800c0d494038800042009240c9103c240380c40e00780a84004202510090b0b40030301641c410740034840c2501c0000c400142c81c1c2055800142242d010030340d240c03120070340501080c0f8403075094401d45000300720038000303003481d0301400e1182a264100140180c0c480c41d03803180c905189602c40c1001c0c0103e01ea00d4000c9950300c02c00301d50041d6494010541c4140f01c3c90f4a050080703864200840c01d460740300c25040419160708941c03003900e001d400c1c00008032070401c504000005000310300320100f64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 573920863 1106 573919757 573919769
    0x70810091e0803070e1c02130213031b05040606080a230712051810021b070b1c050f0f36070e040b0606071b 48
    0x203121501c00c42000c030804415149401c01411400840c05500140c540c0003211849030f0400010711818070303100000c000d010604a0060405400388540c00d00f0340d98026040495007010342c849403190f54000d8801c1c1e546440101d00e0120000503110241005603402d001460800c440a0041e0b10041c01412503a607035103d00c10440b5012a000c1c070203081e00300032104443d00701140c008010b0103101000313541441c98140416140c2c034140d12503a011007880009002c1c0c000c0b0540d05e800007904440300344139050241000c0c58006003030074041100a40341c0d83c0c05460321003584d45411031038400b21000b0002124034000500c40c2070b41013900301e19400340d101461250a990744003080f51820008961103850401a0328680c208004410600700000c1c00e1601111040740c1d50b0001a101b00c0b00958002c0e1200106001160850801034028124035000e0980000210682d03a407611001d1210740c014 = true := by decide +kernel

theorem cover : BRFrame.Cov 573741007 573920863 := by
  have h0 := BRFrame.cov_init 573741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 573741007 ≤ n) (h2 : n < 573920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
