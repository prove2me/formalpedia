-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4907
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:07:27.170954+00:00
-- url     : https://prove2.me/submissions/294b46f0-32fc-4184-bf75-b98256854fea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 882374100 ≤ n < 882553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 882375350 1250 882374100 882374131
    0xb0117121c110408030a080f010f03020a290406030e19021e0a080f01020702040c020a03090920070b060a05150a0c02030102070204180309060221210717060307050d0209 74
    0x40b203840c6900102580d400603000f20104411402c8d9017000d14050070707202001c4001c140c5181c00188602000703000d00d03d10000011007c0c1c401010111881000a0420b0360503030b110703a6030b85005401450950b200250a00031120361080700c0c54082442c4021070f0703004003420b50068540359180421412181d4294101400031800f00d40e40d5800c00c04071015911032000541c0e43c90b000e00c1400309072030300f86c00c052007554040142c1c000040d420000010680e01c0010b000a035180c0e13655141105808484841c0d522035000254600601401d13010720f5201c2d1805a80c040c500c1c90b500c000784901d0701c600515088012406100c1041094415550b020f40140000e0000d82007400e9a000a0201c5080c1000c0d2420100a04021020160850142402888680064031451820401e40710821800540c0c00b800c018000540050b011000b0704d4440790f00001048001d4240350000b8040d04110401c01401e51580b91347e000116580f400151480130b0300c102500441d0340e0071180c2e003403148004014040170b48000e28030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 882376600 1250 882375350 882375359
    0x14150a0f0f0f1a0a060e1201060f06200f0d0c23010501082517150903030727050f1f020c130c020705010e010203070b0117121c1104 58
    0xb07000710070407000c888070005580d0842c0c0718812284800126124003038006444104030b800c0c4c00c44080c030a101015603d400d072420198241500600d040d8200c112502031500f4003041c0140e001e01c4200204100540d1801402909804941c1ea48031175005115240d0084074400c100c94820b00c09440400d200d010310b09401e05040c05940b10b140f414001e407005680d07648004112084007000340010640c2d00f0810404050680000b0824051580c00381680001048481401d084410000c00300c0040008100c0307145401c0501340152245d0094038010005020f840f0980e80101714020407e25056001d14811030403883d04040c0401107280c807401c0340c0c0c0660200900c8518031211700d02c1e0400c982d00303940603005010501d8200000085190001802c0328a00000a04070315000a8070308142d910909005180c15803441c0101e14501c1080c0c001090081050000114401c10703030800540c0c2a010015a590418603c00c245114043c10f0611030310440c0380c41c412100d80c1c40740e070301884040e0303805184289400d858 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 882377850 1250 882376600 882376631
    0x20907031e0227010c080405091509040609051209060711030c06041d070827030f04030c081504030813020102010902091306110a090501030b0316030b0414150a0f 71
    0x394460000c550394400310700b0110802c103c00005151000d080407200340015454004246c0034030702403540502c02c0c0c0e4003c81c1c0c0d8040704240760301080900400599040c80c252074980003410a11008403014460b460000c25071094603026210f032000058007441c20000c04c0c1e2200c00920182c226083d8041c0281e00c4c80c84040e803a440000e002070080250075001e2904e20044100350060700605450130480300c5002c1c06a414505a0740c0e11000d0f09501030101250751003a5190300794402c002c00c01c0000080040c00100f0000010202030131030342c03114140c80d01011492521340d00401c003107030010700003604107001642d107003c540b011072401ca006200000c1d2901056000c158400f01c143c0d070710700c64800b000c02c8013030403c1494040d140d1640c2c01035000d182000d00d200c001070245291030281c9414140c54801c11807072510101300000c100c11034124004644c980d24206004c950f072041d101070b00c40c407003180d604803000000021040040080c80380750b540540e40c2d450141d0014608050751241040e1250107607400f1148 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 882379100 1250 882377850 882377857
    0x3030b0f060703110c01081005090a1518061a12090a0803040b0906100605180f03101b0c020114070303090b01081605010305090a0b040c080a050c1804020907031e02 72
    0x460307201d1318841c5601c00415460815011011030421140004114103040307144c20380c00403190151000d0382c1c03903111040820060140c2c070413200b08103a0b000f100028640e036400d20b80c018081c9442802c00807140c82d41810304481c0300c15011241600c0c0e08022980d0450740d180c1c031240d480150103068441c00c110075a00d078101c0d50310a03202600c81041d44e07414000b01c5c050500c20140c0001c89982205519450304502603e00c0c0500980b030a203550503070122100355224803203956441d88009013503035040351602d80e00c02c0c003c0c800c86400c1821210312010394500a40070302d1042441e50f80503114030090010006000ba01d560088030300b20b01301034a5180c4a000141d610707203200e01174403000e40070b46040030b00846c05401d11407107588910f0406041800f07001c224200403904031281e03500210824419502c50509402041c42a809000203105504850040c8400450f0f04410002d045030780c0b00701d00803101520f071455401030320007a40c8859101c0103d0300b224000c0d8401e011401144640c4040110007202c030038120780 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 882380350 1250 882379100 882379103
    0xf01020a02030a0e0315161b05011a06041d2706010303081303080f06010903170307080a060617040c090c050306090907061d0604030b04060207050609010c050703030b0f0607 76
    0xa10104503c802150000000a40000c1c140c0050640c00c50103c2c80703000201c409009134170103182200c046501d1174400da0b103241c44071803007490080000850f403078001c0c000c2c085603a00412040e188010560280342c810125030440d07142800504c00720f001080d003c0341414000d006a2506070ba8842500b4400301070005846040712010007070881580f442c10041c02032030000b04002d0301814010082400260810f1706030741c2180d13008602c10410b81c2c6600040e1620769183d000034249441060700803003a00e20040056108a80c0303555070000c203450b428070640a4411502542c800b00700d50349150251340401081081d446401611101c80f85980ea0382c0ca03004a84520104000048002003044401c0c00c0c4200e010f5001500d03030000b08005840c000c03000740428403405800c0f21810138814030303803181d5035070b007069401540d000f482031005401c2c240b814100035409480c040320b160184000007000c5003018400c0440400311900c0761880d0015a503002ca00070500341c2d044541c051170131007202c07104e5103502020b0060036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 882381600 1250 882380350 882380353
    0x70b190201021c020d0c1e0c1b0f0f1d13060617030c060c041401051b3406091406040b042c041106030c12070306090c091a0c0f01020a02 60
    0x1c004483c0405e06464548680388280512140018401440c80819040c4000a072601c00502142d6140103c0d5418150214469100490402140f10014054440111007101ca25060300944e14090174080b802420100c0340c111043d040000d46001e1000d1045003407600c11407000440c01c0d150600400c02001044c47c0004d00d50002c1003100c6424400c00035190000c5c0000a118141890243c4a07100e0510704603085041100c085682c0710004034040044041d54a0300d0b003511442d600d628245c1e8620410204001507014100700d010650300c1f200a16501544d050ba51004035080c02d01c0e541400c0c0700107100c104d64010341c0400c00041d0480000000d0000340501c0740b20030621040e50b02c070b0104da03418003032460305040e41000d0500c800200b80d01c011222100041e61a103032650341300581d014081c000d002000800c1e12203c810420002e900d54020350680317451403010042d092507004101c40001c5980543c80078458594491024240303d0720280c0684e015203c00c840b01c0506031a0944d013603800c85194400035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 882382850 1250 882381600 882381607
    0x50a020c1e151512030d020c0c3115030b0c280801030f03110d0e1011190602090604060e0307060305060102062a040308120702070b190201021c02 64
    0x2084014044000d0a180d8120350351903c1c240038011140c503035409201c07030340304410710040c200000340d040c802c0c0e40b010400036000315260034100507025100c41c06038251600c076405861007641c8074012a650341411481210315640c1003101e00c0c111a00601d0404480c0c40030021111001001801040038a03100301c945408007a1600340d02a0004504d85074501d0300b030040110700c80c15400d103d5029407841c3c110b0381c1104113a0703070504030390409171110700383c902190040d0301038040c4111403150008003000c0d0854044d40c0c40c0700084400d510407034008511404200300d5404c0800511a4044540701d0751500b640244401480d150716000060301c1a031140c3d1000c40070407480780b01e03800c2d1440c050044200034513403401c05001a14010300003d450310001062030303414502100c40160070038003010000c1c000c18444030380d00d545c40c2d480e81000d2005820410070011103001e148000f5102502c0441c0d140101c0b41182c0388281170100c485e44044c0d103481d4903c400c004641d424054034003d0001006040c03005098141c00681d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 882384100 1250 882382850 882382903
    0x90305130b09031b040212010608091b0a05060d020c03040608190501030b041401060801110d051e01030b07020c0307060e01081e0105040b031f05090d0c020d06050a020c 74
    0x1448080c0d80d00c58a8640400e200002d010b4074040380d50290441d182510070004500d08001a00078041c04080b01c4c004c5034058004507107960041d0100e400f81000104445a039000f29000080c055041c581403500309000d5001000507060050290511548181c00076080c803402c881b10500c1c44d002944408000703002001480082508003201204904640c038090020350f045840e46004440041c00050580f4411900c2c1802c1e03090a40c0854080c00e5610024000c0140006091440f1f0308000c240c0c2c000c1515010118803030300d40d61490100d020000c4c21049407183c2c41d60300e820058003801030004055010360b0199002568060091740c0290003503848480064401c0c0000619409000f00140c2181c440c4098641401c01d54480d03442c1118421500844e0001c0c0c1500440c2c20003138031072225084410032003404035800e4941c2c0c12851180207038104940c2400740fa00f8046030044598030004c0d402180301d4140402095841d00305583c401b007002c44c098a4500d03104a46850141d02424090040d23124054242 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 882385350 1250 882384100 882384127
    0x50a06020a0e100f0f0c11150405040e0105220237080606210307060906062112051b031b060105010e0a0b092d040b06030910150801090305 61
    0x41010000d440c0004c00403602c0c0901400b000701411070302092186030b91624080003d400c1e00d4040646014100e150340207540403038022030740c0050040d688a04c2c200000300e00015414460a4400c1e038081c14241d4202c851001009040d07102d44200342d0b04040c0085000d04034008501b5081d0450540984146ca003201842010a070710201350022540740c3c0014061118907550f02a040e0216080840c0c0d45031020500300d13103c0e1031072181e400d0040c88981410440320602195600840490348030100703441e01c4032005610340000c44541c940060500103003107060b0721180c1c4580080c103000c0305e1a10180c03408400304507a051a58016070080c2c031406113584104034032104248480c0b07004240c00e080050200d43d1301c50004034500080d004040c1c1d0040301140d0540c03a45e4900704500341c0d105415070000010034400d2200d1041b803d500c20441c0c0a10300301140c3d050142809412240b04640a101a081346640006110702030075940051080d00e809118011078103500038458034041622075114140c0d550406690381 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 882386600 1250 882385350 882385369
    0x131512050c04020c0c1207180b0f03070e011403010f09080c070501030605010207180b0d080d0608060121051002180411070c031b080a080d0b04050c090409050a06020a0e 74
    0x24001da0042c00503500d501c00c0024002005802201d404180c1b210840c4140d2610029601c1220503902c0241c600c14400a203038404020f000007521608241c2100d24181583d80140744035202c0c0038006800100040e1703c840c0498001218001c00108100c4207200c261000d842e0002e030140c446010004041c60113040400c90300004040c20308091000e20303d4400040e4a9500e5441001d198030000d459440d100101a84400082603000305171802d003a00504042e113054004e0011000442c4c5030002c0072540d000005116412560310354100c04814060b00c20010116891040450b03080c85104100070301d40030540050030440805000300245102c0080c1000b0035245002940e0306641010030424000c038000d00c1100007507030b4001ca211360440108010382e05449169034008400c80c007500128a08204034000101141c2410440912000303841100300310072600155910320b1119410883c0011074141608400b10340d0b03000e0001e1b60034038030740c64131071788240e074029880c3c43d00254034840400d050303240003a900b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 882387850 1250 882386600 882386623
    0x302070b10060e030d1d131a10050c0d120e0d1107170a060b01180f090f0c090320060721020a030903170705010c0e030d0309020d0213151205 62
    0x2c0c148403c0d2005d01410100501c180c2d8a0044880c2e02c1c24000341e290f0000019403218401002c000c039240521442207403000b0110143d108007207074890303451410f20841c00e50b540400400c001e0f10302c0c039010318001d858010218040341996a194007000300e20880a00c103c1005600076211201541005e181950a02100f40c200015010080090044400d80050002c0c86d855000d44002009241c0c2d10060b1020364400d00300d01d8190b201002e000c650307071203254a210708803a6190390502690541e10b0b415400d8411400848001951040d4100007040444800d1082640200a15840e90882c2000301c3c14640c4030183c00c0d10404400f540c600301524145003144044c3c40c00f80b000d000a03010700d1394014820b03020ba20001d080101110401e84048251108940c01c0c42c1c0d101c00204895250914003034440500784101d0340c42801204a20540c2500070302032182500d5000b08080101c40d0950f08004004040701d1300c0149071a034540740d44d4101055101d18030058050084501001c2e4030b42d14000c0d28104c0041070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 882389100 1250 882387850 882387853
    0x81306270201110d02030906130e01081606031b1d060c010603140a03090311030721031e090612091410060501051806160206030a2c15070302070b10060e03 68
    0x44e2010344036070200641e000548125035056403030091800e40f00e44190307241c11064071081e80800009030707050001802903045240903e280c25807580e40000390129160100c40740411381c9404201c1c00010321985140384140f10b244903806280b4840d1010480a0308a615503400c0c60395244e50605c00e101052545044103082d11004140f214070715903000300565940c1c80001c0803098482e881c3c0625070303000c1c0300060203002c00c030300714103148080c0500044a6095048080e0b020908c020000d1840342e11407000303c074913803403580c4a411950749040c00848148038a0340c04d40103a00e580c2d41507540041c142203151901c80c0c020074010301c00038040410646c1201c1a5a02140c14050708001c1c00901c2143c06030f41e0310600404913a61a281c02802042a41442d0100710007580700400004000700c112407903000c00610074921030840c10a81190b00e01c0d95a40b0800c8846050716880a0301e044400a1580c6c020f07a4018254a0050b00744a070b182d071005130560b41500c101c4c030358581d8402c041c02525805121941c40c114100e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 882390350 1250 882389100 882389113
    0x50702131137050d020f03070c210509212508060106020a110102030706092d0b04021009180203160c020f1e090a02090906090708130627020111 63
    0x41c004514144100d10342801400b10b03409450380e4285c0d054170558601d14801e0f590780e00d0b001800401d60409a802202c61202c3c1580c2000c1c210190515914018650344503d4a495000d1080110405425400f0381f0544008403070540786902c2840664194000824921080c6c01003000c001c40d0720000c0d40100002d40c7c481801006a0350b400505d10110b59007000b10028030292000040f419482000701c0500740300e0402c820304c0104030020040078a0b0322050700c1034040401400021079544510440050503031a240d201140240c03420903040101559541400300e1065030700d9888a0401c1050b102c4800b0680c1c0c044100410407180740310800c0d840c611440c00141a1905500141c1079100d44003425000340f0714220112070383c403495001d00b42c8080c001400e0000d9440c008070203e020b94081070103a8051400000455104c4c2406500329009020540344c1ca10160340d4403c515901a440140c00c1d00c0a60b00d03405288c07030348404140c998038600715100b1040e086c0c0324680005040303c411800024032a92101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 882391600 1250 882390350 882390427
    0x120509030c150c120c1c120c050c03030403090509130206040e090304030516080c0a0510030c140c0303061507050706050f0d020406081f0b0d050a200703121b0507021311 74
    0xb0302c056a1f961440c10000aa070800508202c80ca401401c100f1b440e40d110010a100605811104503400c451044035040b5183d0340780114a04c802564a10080d00005c040c4018840b52981209850340103000204480c14641d8a4860f9460040400c00341e400c46040c44038140400541444007200c2d58409507940d4203940d00d82400729080c08148031641c000c25a071100c5545e4594820a0500b04040096000c03d403240750b840c039200e8880e401a640140310780f48405043c1c1c042c409800a681c2516003100c0030781141d81ca0684182c1e03095215243c03d40f8500c0c41000102c0f0302001d9071001c2e0000d01050b42d83c41985280c40c840c008800300b58003040b0400000104001c00172106280e0455a41c941511004585910350342d0040e00580203041d20b0242809070b07052014580e00901000d404528080e50320032013200e0b500c407804000c44032460002428100301e052405601806100201501c5102402040c83d207101141d410007103800c81506040440b0300020206290f18201c2014810706d00c0a4071050450b6200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 882392850 1250 882391600 882391607
    0x50c16060c15061a18060d1a0d0c051002010f11030a1406090604180803091f060503121803121c14010e04080c030307050403120509030c150c120c1c 65
    0x70b900540c5080384c130000300c000f04043c020000b152800b202070001070303c600d003020f0154081c0030301007e00400b47c85082086040c601e010541c030a0041d03000a0030040e00c80c10b120500040c0d0308004013002c155034850b45001d816083c948102022014070480e00c41e1641030000d44030f400d850084c510001d48024070403d02169030b688072211500003600300d40001d2612400c245055500e80142c6015109101c0070042001c40c1001080c1c01c01d0004e180c013440407980d4494a0b00ba402c40340c1c0380c010646c041d0320000d00c91111004281c000c26111041400e0030800c140500c00223890326000c1c15607508242000f0072250000b00069401c03a540340140c1da0305000b070b00f00242030210040014032070003c0d59001c0300e0200f014452010115074800349940140d03030b602d01d0704510107081c59009204c100c4581184080c4a54540e21450071340b0790310705008001c0c00c0b4100c000f40802030341c010442c07620030008004104e03003c1080401c02c03179009c03135540003164075403903904c001c0707400e0700740f01400c410f040e1440381075005520300326031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 882394100 1250 882392850 882392879
    0xb090909060403093507140105030c0328090c03060c0c021f111e060f010305250b040609090b0405160f03020904090311100c0906050c16060c1506 64
    0x40412000d0300c07001406417081541e803200154040c00303481c5c0000d22240c0c0f2001068000580d040c11444000301c01d90080111000c1c8000c039400001041c003030001c03075110030107144510f000c14100c4010102020070240007004803101100216022186032004004100300341c000c4049040c00341c1032081c203e280e030b9004580484081003c1c9221060414805043c4500030401c0b043d0881881d01100c034400604910180c0140300a00d81c1d070128825000090396072801d00403d98140da0b400800742501420700247c052a007942c4c0b80400460f0f07a0a10301c01f24140c4c4041000d031008101e10b6031007854035807402c10000304071100080c0580c0a06d081208004000980ca045600401120314000711980c03c4010110001d0103090503c03a482410407901d48145a804130f07010504c072059005030380500d5051000b8904540d50400810049510302c0010021507000302c01604120040005450444039040028980385142d0f070010b002180c02c02c91900c0a001c014075142c0c051b0221403804121403800e08500c1c460740d61 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 882395350 1250 882394100 882394109
    0x22d06060910121a04050a0c24110f1c03061403070b0304080d09061d012a02150f0412090e0c070503120c0c0f0109150e12040b09090906040309 63
    0xc0f005242000700300030740781c00c070b95000c1065a841c69241403614240b61150002901a590b0580c0b03d440420000c0c00991345000000d00146a2030006a0309002603039500c0340c0c201e0300890b40c003e1008842d0142418003250464400001e030107488141c01e036801500304c59140c1c0108441320481072802030f1039140040e02509944814608a803a940da52411141c5446045a544101400d040011041000b2078200034a016960072400440042c1c40521a003210511240140140502404000840c042c00046004a0720501c180e03908104a5441c002d400300f01640d0700e0848d4045102044140f1200c914903583c01e07045403030000d402a1a08207000861030300034120034802c040004281080020408c100c8002c2000d00000c07088a1500d00500400d9801c6003a082d0030b48d000e0704907404031801043c0300b0b007000c4542c41200200d85c8900c405124000b401001382c072240da44034200000b00c18044070b0001d00000c004501d072117079843c1c2c000814071160340070141088410703612a105100000342c02082d460140e070b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 882396600 1250 882395350 882395369
    0x21c0e12070b041b080d0309030e0603090a0204050604020702061909050603090c13060302041e050c27060403051c09060512060d0602040f170606010509090708040201022d06060910 79
    0x1ea0f2482940c0d00c084c0d002d0744281150b2040d204003032255500360300070302d0319240203465159a0402410900c00b8230310041390078001e16003021070700d0300040c90b21b68030036034103c0c0000d44014102041c07640407400e1944111180200721140b0116400420f0340030a010000c6d01c41620143e046041203400f4958548000311164421403880160340e101d080039901c914001c40e001802440031840c4000c1c1525204034081e5091851030520001440e122600c3d001c85030100c0400703000b84603500e800804a864099090314450b4080400c10001011030020020003103a40c0c114007070000c4142005038082c2c0154001d07030000301404030501185c1c1c04c00c0c4804840a510080035940c50811354500e2a000000b481517070804480c40c411068085050070712220003841064080d0101c40d015107078100107541d540070f400e40c0c0c140d210103481c000845a0340300b0701d8240c0e00f007403041c0100d42c1200c83c07548250103861039903501c480c0483c40c0d1840e01d4901407000c01103e074120710107441c60680e82c2000d001c01d2611210600856070032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 882397850 1250 882396600 882396623
    0x11b08011202131a0a080d0e041d0f0708010f0b0a0b07021504150e0a08060402150403080703171f060c14010501080c030d050301050f090703021c0e12070b04 69
    0x41d501c48180c001c0046103d00030402100c1d030041c0c0950801000e25001a0107003a000c2004181e01000043d58800108070f40c0300c00c4c04000d5008200f00c090003441d03841c0c00e031040070b89043c0211140200070031480740744004041c0c0007003403c1ca00d4245c2111550302c49a100c2e60304000c8081e40c10b84900000720140c1d03101c41c6400303a45825a002084050604081000c10240000340c00185d50301b2801c0301200ca10a6551584000c4103080204584820030340610720325a002000401d00501c0c1c614201602c8540300f0a146080582e280c0340d001d5140c00088041c2c010450791200840100d201b10301d0b043c1e2166941012180807051350804c80603c5075240101002e200303010401c03406000074440b8104121021400a205a6840e4600344d900c07841c00c826118060322a001c03d0070041030040c41560f058a40180101041080c1902007040020001d4042018180d007009a9000e00400c4c90760940c140b00300c81008a69505d03e90700041c9001490b46415842c102c0034046074001650800300b5a81003600820203020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 882399100 1250 882397850 882397853
    0xb0603071d09100f0515040506090d0813050a09021224120f0f031222200306010501090302012c0d030305010303020615010c170d060f08011b080112 65
    0x1c1c024034009001e5800001281004004804a1003220585500e882d03601d50840e070360000d00212540303c400c419440c6900380814000ea0034041c1c050261610002c0005241c4000760700d81003020351082400f00040c444650090150741007022460000f00300801c0c0840c5004016040c6200240d0701a2216124403410040e020002200f901b04c1d421210b80203240100301212010080d6a80c204c4003101150303401130451101000d00044290741c480e0405000e401031503928040d0748481c0c07044001c0c1c0098817100108450000c924002025001075401a40d40c4245454039001c044c40d04805034801030410607200304c00e02c0181d13030040c125070174040200008030201c2c281400032420030620040150300306040410001c20f1581c141c20141c101e81c069025101151901c1c5501c1b2120034003241c00d540422503448a500005090301c40f41182c11100c1280e5030304200780c64008000352191a41328804a040c01c14040c05000700070b2040d41c1060250f422000c6404454060290222105104181542000301c40020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 882400350 1250 882399100 882399137
    0x60f070605040c09110c160f030b070c060e0c0a1a1227060411030a0b1612020a0e0112020405090c070302010e030304060606110c0310020a09030819120b060307 70
    0xc0213080500c41c01d0201c242036100034011508404178007002d0388105240341c441c25040c200c81354291b071040350b5120030340c0b41140c4821010f000007070f090508002070070b1107080224001e0303c41c80c0455107424026118035200c0004000c102031860300140d00c0d0b07001807106a413078410140203e4401d010850f00310541c56a460403a170106c1c4000a408400102d1641c0070101d0012012840e14412840703158136a01da241d0b954107050380c5102c1800010103034100c0102285900003540c0c5800c5009405150680040c200500c1c1c01c0d00b0f0381c12030080c841c0031669843d043c10081d03801490042e08a0240d1500714105860840024a200d0014251840b09440041c20000b41403007904020460200c030780071640c0e2414a440c0000061240340309200004109411105001101107524a15824018018586801c0344074405c0020f44c021440d107400d002868000000080050018000281c440402800c2041d4040b1019000072455800c80302a20b00c0c0c050f00d0160b0343c0e207000030342e608050303503103450400b0a40403013522 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 882401600 1250 882400350 882400373
    0x32a0f030c051303051e1b040504080903010e061e090a060b19030c05040507020f060402010509210106081c02030403110a09020c0f0c12100c020718050a050105060f07060504 76
    0xc10200703c0041001c802d004002480b220f145c0314202e104611020140496031320352410b4259040796007100700d2001040c0c5003c1c1c102c240c00c02e010301101480d0810380c40c0002d0865001c4070325500349822102c00c0080300c0003405004800020522420708191030728100b815290b15018000402c0182d079403088555684901084160b14440d41c000000303200d40301d05000702198558401d044c0b117682003100041349148041102000e0440140040c001503d45074019200c80d040040070b82c0d040103041c8242c00340c82100c440c0c5017030140000e07800054070301d081840b281d040c4000c00310b003070071180e141c8481d0340c40030740d400012501102d030041d80c007201c850815000921281c110b030380442c184030b0005c100600340a20101c5d58102e94120701d0b049551462083c01441829082c0c22654042a0031a00c60800f02d400c0640040e0400c1d1147c3c41500e5080e600e503d050340703071460742003259000f0705d030f9600420001d09841c2c45600c0c0513041c11519075051010301030941c51240302e0414010401911400807030304004034003c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 882402850 1250 882401600 882401617
    0x3050408030309010504061b020303281119031407030e10061806060f120f060519150e0901170f03160312050105030a0f051c032a0f030c05 61
    0x68942d070b81400c8400f1400781c00283e03010b4805501c1d2000101d000c2c10400950300178200540c0203941542e668920b40c0f01c40242d8070308040d10005210407034003100f96940c070685012000b1846225114004e80d600e0b4190351030005404c40c2458030301401800c4120000115641c40030750346c03802190b212209421941071004441d02c1c568068100040454440401010350a00030605071040064540e584c40171500316480a0b500c4001c5040408140d0a58509800422400c6c0e0304050200d0b603d65074101060352a40c298a10840400552100384620040d104003800b50504030318242000015140010b240e0703413418821300c03140155042c841c85640c0c0040c00101004da11f0b85042d81c3d212144418500304032a0264400c0b40041c00c02040000141020311420303043e41d5024008007070240b1b8550783c1000e80f00310000c003035403144103500c0d08a030286100d1f032206000c1c10041c0d5001c920120380303485883d804c11084400c2451045200c11000346da41d8800c61040b015445842c01045141d9810002d5895102c2c60380c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 882404100 1250 882402850 882402853
    0x21b09010503062701092906221404110a08010b0319030e0d03020d0f21050c0d1104090b030a120311040506030c0417030c03070f2a03030e04020a140703050408 70
    0x4400007808242403026503484000e294400c7d6046031444442c0009a00b20389980d4041402d444014034002030400100102800c8640040c1901032840c03284042981150700325030741c07010101ca070b055908000c0600c0006040c0c0310f00a1213014980c00c0000d40b0ba885a00101107000d0f1410810014540318034000804070710083d0507a07041c9070040c14000d4907038040901f5000882c4900c08888002486040c40000f0b80503e05503071038024650000080141c03901030f114280c0c0100502502840500500c01c050402160701100b550b518540002d00050f0b03400c19491030300c281c00802481c004a81340b0424003c7c600428500010301e140e40665084860056400c112341000c00403080048c0d4844030001403041e0340000d04c2c01b00c40040d0100025980c1e10035101c0c002e403140c10a201c5a400108014a102c0d2564800c0e9040c60810404500c84801d01d8140c03d507030400320781a00f80400900d5040384020b40d01a01c191420b510781428294090004856200030480d504c0c80017440c0f0080c9441003003900c01800c003e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 882405350 1250 882404100 882404111
    0x904020a080402010201060503070302010c0b070e100c050601050604060e09220501150b031021060c0804020411040f0605030402041401032102030703120b041407021b09010503062701 80
    0x1e004803002c540480c09903280900c003049510b000500c100c100c3c0c0d4141c0d60014030965903514101c0941d07010b071214040c0141126090310a0f6902071100400c0d44079640c0c0c0c1c2101070881d007003551604806034441070245408000a103c0035a1280c1940c3c8000c80c1598010701c81d49803c02405614408103d80440b46111020018200316040d00440320841d0340d1801c02c241c4584901a03400244410707510283c00203520b0004005c0101d80310400c041554450082d40101c0f031003900c402098501c82702003440090491001c110841c0350038441c5221b406a4120708600305814203038695800d0303030075000b0801400350101c0000c0465079031750010f0900803803007200f03940e0b156564a00980e800d03100c81c503501e6020310f0355040c214030300e440003045d00c250382d8140e034030300030380750f850810180040815160868016890745080100780c846949483d014141c0da5004000a0302c070540311000103541c1c281a6440b5440c814010840e69400160070f6401c051600420341c40034289414040d101c0429260000d225400c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 882406600 1250 882405350 882405367
    0x20603011d01150203090d1b090e0d031a042d0912080c070201140d09050f0c0402040b04210f03020105070818250803030109021306020f0c0d08090402 66
    0x1003411031070a41401802940c0d03200e030008010344201440c0d220069100f440240300a00d841001602d00314051040116501d002900c5001c900b030107034001c0c0c8a80c5460391b40304040124100869180c0e00d070f243c6070420400b218000815046140003120510868640c2c2000480058006c041c21048108442d06000b04844503608800762008a5085e18040c485107070007203940c0d0180c0c070f040b0302c58a000211146082e03c203a0040d0707030700e400c150f074200d11364402402069105142d501c40c04009500031710081131a145c10003542450058801c5500e40200e0041c00b0410090350340c00141c17001c0d0746078280c400107191180c10410f0042800c00d04080d005242c00c000400074160194086030040c0ca4582e01d10185580d0f40c0074001c5000070b0245043e80303560140d111204000e06010524010241341d1860a80403507a442681e469900280c200340242c0303a00040c00b40054110058a01c01004240013808904049840b040c0c2c1f0b4074051041d0502030383e0040324850812450104035108248000c00464448005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 882407850 1250 882406600 882406619
    0x40905040f140601180f090203014104080309240703150b030f150a030b15031f020904060510030c091403030d1505151225030b0d02060301 61
    0x7038180c403000203003180040c92810114516060b1007080b032a0000c8822203140c0314004202c01c11252651541c2c900c400c034010780d000e00640e8003485030342091440744a0f030740502e0000e82441400c080d0b04d80360040b024400d401c10008116510541020305142c030383e0f680381c821506090241c9281028041c10b0808001a001c0c001f0341c02d400340e00300c0ea50401000d8801440462080540d008096500d5010301c006030302d641d074118035140d010015041b03544804686c00c010800072501c6030001ca920f500d002c3c0801c001d510403e40c040c406240700320010306400700d00a524090b0800c1c0d82625190301a00007030300d4200c41c0c6070740d0001c400800005d040e10b40e540e020003000400918211401e100000c00c4030380006221807032610400405c1200501843c6009803509101009081810050750006030745080004d03d40e840b041d4103110041906c404954441044001400200b0b004060b40b0180c1048042c418900030543c215450200460900096294140000a880d0000488002e510500c00800070802d6101c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 882409100 1250 882407850 882407873
    0x3100b0a05030a0b09010303050412060b040213080f0c0a170c0306150f100e041a06160317010303080606161209080c060405030c0f27100501230a020304090504 70
    0x310750f01c0811040000c04200701c1308040038807010300040c000b80014080040001d003074091080c41b03210001110044440410141e811400410b9140842c50b4400c0152541c1481405000c001c14005403000c4210000040e5201000d07016000e504200002c01d1010700408100340511140c0042c00c54005103005a40b21118905102d645401402c01c6100c095141c141660303c0c1195060540301e888507038495009200c0140700795803401503807a100000c840ca042e11940c0081480c000103042c03180380250941005880c0c10358010f0081c4448810f030004101299200010b0754101000702e96240d07036040d64451070219000c2d8101301030128a0203042b5880c00e83e80000503441292040010703030741c2c1040d103031080003982c1c0a148074441d0183c200c0e00e00301d5074a150840ea4402100c00c000c040d0001340c109807a2141d40502c2040b00144010452414000035544e400c042d4070061100b4038043c1007031080a003105407400c1c1d00a0601044100100d0b00224150003441a5000761041c00002c008525203420802c00481 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 882410350 1250 882409100 882409111
    0x100305011a0a15080f0702070f1401091e260303070903171810030e03030c0a1b08070210110a03020a140606150915030a0b0a060e10030203100b0a0503 66
    0x14185000481c81d506210000b1802880e07240c0c0d542c00c3d9160522200285c400814000071801504401301d0b5580d14030318840e000e4501d48100c182e2174582c03500050200f0584d6000f01d01040d614080321050001e11140e03120966002080d20740e0f001032048440c50040c8140b14044006000c04400c01907182e48c05840383d411a40164945401110769100c8007026108040d02d0325030092110a2050361350920309028500311004d882c1c009600141c051981307065400544042c04800000162100300070340c0043d203850078504480f0022000e0105650710320640c82410402405080d585402403070701c0c0d004e05003001d0002e1903002030350f03000ca400340381c02034a4182258085904180c001952003000d0b80c000341a505c074410141c510000205043c8201c14590041541c3c550702034080c18030710000e20700620145005411500c0b0125a00180408026240000d5080f001c10494910081401e55036480345142400c611401e0051b629280c48a0514580100360041400210002828400e05601000441c4107a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 882411600 1250 882410350 882410359
    0x80a02060c130303030b06070605040305180f01080f06010908060a0b152506150b0405040c03050f0105270c0c0607030b06070b0c0c0703061d0703080f03100305011a 72
    0x90741c034841103840c0c41c003440c0c0c0e118606200481080c8000307400799005034100e184c01480c15007080c0031a5103010544800302c60880001c0d4002c940d0b41001e104000b4910141b100460720b2100d1000500c1c0001d096090084c25100c0303600840c0045400da074047c104600142100a065030b405141650040c006895504902e5020b0b003909082480d2110558041e2030307000740e10100c1c819100301e42e040700712441f41095000740c076001d6a40b00702d500f90018a181340ea004044802c407558466141404000031928070381c0449050608000802c200400c888411b01d05480c812240904140c440c2c0c60305003240c000a41c554000b50300d0b92814800c0a0107a40c000c0c00206070007004407a03c1d07564101e001c8095070b1240c0030150f00301c401030000740c0c0040e20242400350b11104100c1302e14100400c074039215140c0b09860b070040c0c68241e9211403a000c160b0381900d003049c02245900091030010300d541c1d00d000c21403040140d41252050044046076080d2003460144008640040c001c0c0078419103001c2c0c0c0c001c003464601105101c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 882412850 1250 882411600 882411613
    0xf0c0f03021b0607050c090c0d0903174501050a150f030b0105040513020d0f0c0b0406120e1f0221010602060a09021c0b0109140603030d0911040207080a02 68
    0x643c90700c0003c41d10056800b43c05040f800c503240060145190f4003500e900100b072400d000c0e0011800c414480d998000340070340c4d550b901002e203c2103124241000509480c01c0c8960340c85a14141100d2141c03c4618000d5044038410b0b5800040e0340c0107844028249118521b50030071301848078949c5c1d55005040c1c1042040045070b200d80e90342c00c4440741e0035240c5c800241054031550040009181c40d0b801107034403480310780c2070203850000390b030008100d00381d1500300b250b5039036512400b6414001c00c03190000c060141142d520385028104440030b4078480800e051842c640781c64000403248801c007405054103203142c00b0310003501c10b600746c01c80202039000030365900ea0748035098000c03070045c0c00000b805504840f4180c0141820751903500c4070401401d0803890a0760812190107408640c3c400030721000e82e900d4001c0100d00d40f1035043c00d080c0c0d02607a41200c0c6042c1c0080b01107043c0001654080102d41c2c01c40e213101303000a41c1058a152014a055802e038143e40e115201082600902003070340010304242c1c0181d4281c420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 882414100 1250 882412850 882412903
    0xd0503090f03070312050a0b10020d02011b1704050a06050c1902010203070f120b0a120b09070f0e040c05030d050d050a09080d020f0403060c050703020601170a030f0c0f0302 76
    0x140c0b40243c1c02c0142c00604c1400c4030401d042040e83c001038215000c1440460044048800f091855804502c0d041c01a8807142000551a07428450703610380940303115080041d844404801090003400d44000800e04c40700401040811000b000080c0d203165201005105506d841702518000f604070710310110b441c1c1541070714841404d02c18401c5074802c524139110402d0b032060400c000c59090602403009030103540d962020040540e10440c40c200204040440185841418038114000b41800303020801a5444103005000803003075100c6400030383e0240c0303050038619a200d00b85105242d4a0b940010b816010701410b13402c00035408001000041d516030024401500c80300480320407945050f2001c0e0480006001c9000c0c200d01c150001c19000040e4084941000d03200e455000c129940c2003c17490110390f002440004040d010f002d0f03540180003140c10038007000c400280c85500c4981d030902c01410030000d407007000607003401001c0c80101160415445c006890080c0b8000c0e550321900e078034400c179032984050100e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 882415350 1250 882414100 882414103
    0x1525050316050c0a0b0405010f110c0c060a0207231008060d0809040e03040b040816080a080d060b21011203050906161406070e010302120f060604080d0503090f 70
    0x280207420040c0080300e00315441400322803075003121550501d14010901058041141d03443c180340124020400090b820504010710012150445a68054440140b0540581040111344012490b1041e202c06682e086083c5081303090490035046445045e030942000403404000040d04025090255902c42d004004d646040d41c20f08812555213521000840c0c00c1030004003400090320222a0181c00402c0602030700c504141184c01c5904003501c800c8002c1070400c1034502c108200301c01002c0c0448001780d01810300390455101e0007030800103400c401000441d0184510386622010061008030645034880200b01c20220080d8000881c545001104000121f40c0b4034000041002c40c66141d11020f1500104e0303014400c60f9001a01d4004807401110500400f0405402400f000c00e518240a403d6a00e003c90740540540d6000f03204604240c0b040c0881140c040e0071881c50b07900722240e9080d6680707036680c24000a406101d1030b00052018001e1250007544150400301950203000108140e4000015260303895 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 882416600 1250 882415350 882415357
    0x1020c121b0102030c1912080903072004050a0c02010c02060c1605210d1104210f12020703020f190b031b1c0507091412152505 56
    0x140d40c9801154441d0844000301e0091400d00d807060054034140801805481d003411011a1442c1001c00c120748140208802406902c1e64045241881c04030303828019249a41d9004d0030000920078008144403150000180c10450301c065401001840359140151010000d08400c6610340090340c20034000e48c4045002082c89407054602e40c0c001410502070580c1c04a00092440c0261018080d0242003900c201841086074040b91411501e107070ba40b80000f081200b02e03091100b40841414060009108800741c104012140b00018042224044c0c001e081600280b09100d40083c4031070480e600e240c444c00d4004c18441c2c1128000c80f0042101d0700b01130284410000381811581041a5042c82400582c00703c102840c0c00001421051681c815034140302000389c2d000306415010303083c48101c6000001b03441c1c007886902c07280394175006462528001c11920b602d140002102d204104014900d0000c8108200e20149030b0092044040103042055008401d0012190039008a000722005012990b009108a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 882417850 1250 882416600 882416629
    0xf120f01060219030509040e03030106090602070b030a0906290f0405040b04020108040c030b0a050f07020d021b0310020d0204030c05030604081e09121006050d02061801090b0a020c01020c 82
    0x64103d02c242c1d5a69100e58000b032103011028804203004202041d02c1c0c51103401c40c0390502e01d0003580d5035414054090800910781d400b010855220794800e100048450003030b01c1d00030000041c0030a0b10149803800070050202c80d04030308050b020200741450718802c4c803544c100458070159601308901d00303184144420380703100700d402820310b400c070390b000c5001544034141072a030090191801e0350410751250f554940310352054856090040e01d6000380f000001032451001d4001d11680000c1c541d100d400140a0340b94a610351510144071507111540300161000c2c4061021510341190441d60b800c1615400c0700290050300042d1000c0c2c0540b070000c98a820005021801603811000960400c0030b5074103000840304481995040d0740400f40003090b815140c504c012161800c910000e00050b0301400407200441d8095803040380b04130900812803001d41c5881c01112001e088101d801c402030700c40040140e0704110180d2014069130030005403907a9013031303001c43d00500d421026425504123345c07031130030005d000400304407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 882419100 1250 882417850 882417853
    0xc09060f0b07051e06150f0f041e02041e09020a080f091203130b061012020903010207052506030911060705010e0708012c0304060c14030f120f010602 66
    0x5000c03000e1090090403802d8402c03c2103a81c0500b00003010207030000400020409a4881000d00500e0103900c403903540c2c3c1701001e850400c00c4d124680c0004840c202d01210041c0100c0d83d07200211000300e9020402d90f12080620b82c15507031160f6605142c45029005d502d100034030286c5102c0410540703814000c4034200249640c515885840300b43c02e548801c074001d80160218441c800e594003d00080784040e500c101841d072040313000030280c0d0074010705800005000c0d501c00c3c03040d04102c07a5220740210b149580140d42e810010b8490085030b01180c0203215035030340035080340301e01d050081c44d40d0003d00340490031a481c401d1503a800d541e5030b02c064ac00d8810b02030700100748120041140b040b07810711300b002c0e0800380d00a40010a00c184042c00140c100340580d00000c030345075111301d921101070480c050000c0d041c80d404032100b0441559200096168062402200100191480303002c0c1800311401101920709501d005403070b6610b000b8440d0358625442201e161404800640009000c005e0b089002e80c100d546580 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 882420350 1250 882419100 882419129
    0x1409150903030c1b01020d06090b040e0601051e21010516030c02100f020706110c0c03190210020f0709060905010618050906041415040b0a03210c140a0c0906 69
    0x1004000c0c0c581302815202c107907500b0701070506050901e0184d100205001540051a01402e4003400255485503915a60f00e902040c010049a00c4503030140700c0407900000c000301041c1d1030600241100e50799081c0c41c07000d00ca1000c042d10f4100c2065000340c0c024500c1202168040300c456000390305071140e01a480340940c01170354441c201e14000381c003c1e164030410302400600c0c00c1190368459003200c407070280150045c2e40104001000c8c02d01007143e01c1ca012000c81c020170782c004d003811000112954005c0d00070300503035481400002940c0200120380042c2d1043c801e442c442c6484d1a8440d00030042446040c4c0c0040c1030400005020b809400f143c10080a5224801c100307038201002c0c0702c4080b80c00303031881c0d0300613175200403043c079041d20b4500b820300a020390010203004403100002c100c2540e848900003481148210001c20010398501301281901d105030805004940a1301d0b025500a607544001a0011350040746440c00c00c0c102003070546149200d00a80b000550f110080c0c07038200e90b60740c01a00001075504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 882421600 1250 882420350 882420367
    0x1060f050a030b06180909070e01140a03020907030b011e0f1805060a08010824150f310614190503010606081b03160c020102011409150903030c 63
    0xd100402400c0c909040c08100a2458008500c0c0355002c600d0701c02140d0701000701c01c0082c0ca0501a01904404110010001181080c0d0000f80002e410711401701c180b00a40d00001c416180d80000303d00660b00200810b1007823420400240140080d544001e000803524014020204c01c0d0003240310709201141e0b03501600803041d52058a1202c911265142200310411000545035a020000c11007103180741c0e5103c40c1c40d4901a90305140040312215000f5a4054203c191003807032160480703507400310001c12a0ba00308e242c8140411a906035104665400500300340070200d00543c81c9008004440c3d8440001900310040c0680e035045458a000e1f0448030f066169101e0100d280c80c0c260070500d409045c024034503040c1e9820000c0e084403010b500c8000030031801001c001c0040c0d40c8010750720740c46503101078951543c5460700030181d5180d0782400001c10b21020200810a5900c00d60088010003c00b003c0b03c400f07810501e081c155030350300c070288040350203a22600081c01c101011080d2405203a28040c00382c00d04041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 882422850 1250 882421600 882421607
    0x70308070c020307080f070906080a02060304031206030c0509090d0f0c0c0e041212150315020d0606091502010b1813080a03231302040509030f070b070f0801060f 71
    0x502004104008500001e0140e9418051a0001e0043c80002d00444680402c80d0342410000c1d4030003407100b480c0807020409100f003c81c03501c40b4203904035909680c1c1d81c1d0360f00c3e080e100d1440c0100d244101030301e00580401084841002c0000795a404c071551609135440000c00356a1303511004040c40001c040034003c1d8107007802528910b148030b10403418007006545610311258207d20482d0181c903454235101009042581001c004030150705004000e004404002000034024010380c880103007558468007010340d00c0041075056901040c900e8800303202140e503401c8020710066150044a800306c46548010029500501c100d0790032000181103229440400303405000d410000400d8407565000301c00b41000040c40f01802080c016515440014811907032111307505c002c0003644440ba075100084014842c0524100d0041c18034158101c90110311940c40802140c154054403543c0101c45c1000305400082001400d00603216030401d0392840c821410310030003100c60100a200740404071302031080004c0450b10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 882424100 1250 882422850 882422867
    0x13060507030605040207110117040503030103080306040603060c0e270115020118031110090515041704060c0611030618040c0e04050606091807090f0b06030403320703 73
    0x107418006045652440810103036800514112107400211100704055170300034210b026041c2030a1004441842d22340d42d400c0d600e00c010700000d4480c40000c400034629940d19007224014541c840d9041c800c02d0140e07000070b417148098041803403180000148100441c40c2400c0040484055122144d010b41d20302010484810100c41c0d040e000c55403200d111b80b5609101110301460715102c2d41c0d4040c1c2e91003a0f0035480f4101080f40342940703505414800801d01082000030704c03e83c0c001e860f506042c03242e11285004a08004195a140071803200824005006a0020070b650243d50182900340b05506040d40240c8040c4011038226900c4903103074503a000c0070200c007840710f035002c0d203e06840600c0d1500d520260012130301c00c45080f14035502400c01c0181d00d041661722503130044100714142000400e610503058640c48207000f58141a550b0305c28400d020701c2240c2007141078400241c20b040d40e0381090b00700144041056150b114100180e90a600800091034050b00c064840106d40c140c10410300e503604440210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 882425350 1250 882424100 882424111
    0x6040902030a09140f150609150a090f020a020c0a03171605030304082214061c02040f150908060f041a0a0f0c0905090414070906151106130605 63
    0x50f40d5048060016050004031005100301c0c500031300c82260302070b040030b03e060312050350049031440c05d605200564079503075822a003001c40e420032201c2d004281004140344403110340c40b00c0c0c0d20b82e04103031f000c0d10b40d022300341d0080c10080d12035801d0ba610b8199181c00d110f0b00740d00300c0c80028914651101144500da02c03d070050b002c520000c0d1302d40040c109030351b1501495504255002d417420400060310720305011149410100c800328800080c42960324100300030300c0b4880380c800300a0082200103002103810346c6903400c09070b044410032411511241c4400e1a10f004440758042c2d12040d250450040f801c2a001742224012640c1c1c2c42c2c0100441c0d55902c02c40c004116014008540b170404110800401e032105a07001c0344a84c0754450001420b2192800c0e800036030f1000c880072820700c00c0d070b01002d00c0300c1e803500d980c45541709811064070301ca5241400c001c10b140100d1903100c640314a2800d074020070784516108088800c00e0403940d69002105112a6507511481c0c15201a0068804402110009445500310342d5006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 882426600 1250 882425350 882425371
    0x1e0903170a0c1a070e0d0b0f09011509051e0f0606090105071202010b011803050c0d02030703140319050f0a0f1116030209010f060c1b0b0a0c05070e060604090203 71
    0x107a607100703c100009418044001c914800c10045640e078001444008800111040803070000300361a032200e1410701400260021641d05c4c0000e040d80001d4204403503040e2403980e507103d07060b6102100c20042c40d054a030400100000d138051143c803981000c0c094010031a100000e440354464030204405648100c503042d0501000b4820b01c404070b9507c0e502849817060f103400100e201d0100e20001070090200e20121681041220300520218800003680421403805480d22852002c9500000b8038040442d03200410910481c64147ca0304c400100107000a07840d00b14100010b604062815180c6028004009200b244c1c20310680070310512404000c4421540f03030030880052a82540c00354205111100d40c03901a0403100d20402c214204801a6401001c20f283c0d4030500700d0515030001e00d140024000070340406081e19a5490b032071450f02d168030051041d80910b90b55a42040b41c09080c24008010030341c2c05025480c00000c07250340390900a13100307000c018070304d030700e8242041c0b0030704000d42000c0e0060091 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 882427850 1250 882426600 882426617
    0x30601020706030b0307030c0e0f06100509090a020408030c03041a073503010b07052b18080a0f060b0d08030a150503060403030603200d0b071b031e0903170a 69
    0x3c56407486030700d0062700050154005510304418011642d010161800d805202012900c0b50865448400e4990700300044950603043d48581c403c00b40070340510f0b005a140ca020004540b242500e000000b0301c102c0741c01e2499940100c5141d9100980742c00f031105c0180c00d803507442e03507c540100d03526425103054041150710005400361031660807401c0c0d0000d800c400118600081c200090000c100a0341c00c01961000050000345001981074007845040c000007418080719883c140f0346005050b40050140c000f14007180d040c0e0b02039040107005d07802052004c0e17400a103840030080ca941424040c40b00c3c3c0b039030444002461512296807001c02440d80c00c41d55441000f8541c000b00d05a90140041c2c0d000358001e5402081f118110309217038003140c007043c940b07007460701500310400c18607210503020a40c00f40e04040c81041980e92600142c41c2c95450b0801e03296904c100b003000008140d041613414000481c80d4803020800181c8010a07110010680000303800081c090340c0541403005014014513140e019450180354 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 882429100 1250 882427850 882427853
    0x1205040b0417270a0b04030515041a09010f0f09030c080307031503120f0503010609090903120f1a01050f0d02030a0603140304090b0a1412011d07051005030601020706030b030703 78
    0x11920510514000e050b0f54549284220701d01114044013404100302e03c44d1810b0301d581d441c0c0745e40c6d000108000100100e101c00280070704c00041c400302920004014440b0451500da0781150007014150100301040e864000480e1a005080c030840f0b000f1581b5458801a1002ea900c2e500d01a0700000c111004150700e03200c0c2c5122030100c000c17800000b1803050080100d50110320001a0044d04048921010400140010802594866000380c100c070800b0310000340a0a81c0e0a04035642d030300e250429001581021f410384207000c2203900192000c0c001d1102e112444200500440d00e40c4a0034551055000082c44040c480c0c8000754000c50304059240b00000341260f403540c1d00401580d4a0994100e2900082403c2000c007456009403100e08108951400c2c2c013506240084400ca00c0d0724400e1409050840c40b1303603120040951204102c0040d841d0f50004a0344051600d80d1b540a0034061140264409030b0600c9400e4011020799010b0301c4140c001d070445a0610b40103c0041080410703641e41803141a90010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 882430350 1250 882429100 882429127
    0x19030e09041e05030d05090d09030809180106050c101b0837050a090b0106032f091203030114130b060d060e07022d120c0601061205040b0417 62
    0x19070061080f005162694520404902180e4000341030402030f8000005507841c2960001e00c0406a82c0d0040c08243c40f4008140414001d0b11071400c40a03082c0b51240c0017051316600b180140c00f80851b81022903c40c001c0c01c000400030381d0808892080e0400b4404001b41110b4050150075038403540107841444104588490100e103601c2080e0050940301d5124001c503020485401484d03808410500c003802560001d69503600016014441c40c4201540c80c070600d504003208401c0c81c1c00c1001101080c0451041d0354545140c1584170141c842e2054150203148030032140d000c4185d0b4100d540b181071114030310000c135060200368400003185010081ea40c5c411802a40d840502800349a800c903100014024106003c0310460400034002c20203540c02800c00d2003446501602404072110784102c001580d5500d030201925140300c60340c041441d440d010030241c84000c0c00184842c1200e620fa503030700e2103a002200d00181203400642c3c014001150100002d80410307610503c00c824120007540c6180303445245600c61 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 882431600 1250 882430350 882430403
    0x9030b0c07030e0301090b071403040c030f05010209040c081e0c030720010c170c0c1b03071a0d0605100207032909010605130c051204030c051e19030e0904 68
    0x440d01c0d1080d607c2448652030f8014109807400c3e1a0105407491800d168550703158001d002e10008008810518411040100a406803408400050014090501c030b411000d00b50040031141c0812801800300031004054928001500907803419948514503220520102c4491a0200702c6084034403c1c050300c0340c103c01017441060100416070382ca102c0903280c15030640c4012907014140c0c041c451014030042211040120b003031001c215002c0c100e0483c1d200001d01007130030320085034000c51059100200846450780d144000b006820810403040004648071020411161002101391005a014017418000501c0038881143c0a0013058080582d041c0340c0040030f55424000c40301c6903180d944407401003080381000020001c080310300c41020310251140d010010700381d0260b601204403000a02e0041018580213100740d5410a80000c161505006507402c205038090166228180a1065112005404180c200d08025441d895a034030380c2590540720070000080d201400c1078600552840400e4011080c07280755 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 882432850 1250 882431600 882431603
    0x4240201020f030906060316030201050a03150b0d091506060507150b0409080c070f05010507020607020f060a08090c010f052d1b070b090906090a020708041403060709030b0c07030e030109 82
    0x40101b03251013801d040c01c00321310324a101d4402d0700019080c00180e03080820740d20f110b0402e2034005141040c0200c0c0500c000708550214101c64000901459030014540145505070b0050312044003010713035100d07240304840302d522651001403028456000003419160401d11080620304005c100300e207201d000074040703900d4104201d504160000358880c40040c00c1c03003c40010649102200515071801c00084d0031032051101c028800d00b4000343c410119610700110410549019100ca600c44405090113800c00c50281e61441092094032884a2198400c850103c1c4080c00c65441d1382c100a402c45440e4019060032240000802c40344074441c441415050140a0710312030b04d18011840c0c0c030310714269810142d09070001180004100a240400e40710f640842c0d070450002e840c884030a42c1d80b502c07403800900030440020a9a00002000241800c142401c8404000308070181c0e1000e46641c801622907a403d4400103000c040381c6070000d02c4542040c40035002c0180603081034071030181c4401c0000e00715112030341d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 882434100 1250 882432850 882432853
    0x703170c040303020d0906020705150c030a090819020d06050402180403090914040807020d050313090501051c0c060e031e0d0305090f100216120903061104240201020f0309 75
    0x4003001410f904100c2c04117106081c0c201800d1943c00d00b40f0080d00d80358503000f110b000d50007603d00482074100b10b4040301d282d000c100040c3c9440342c1800100600c50001480f0710012072041c4e0440d20303100c11818640505c2e80f54014804080c040d856070303d020147c1070081c800c0e1703800b20311f890300c84551100b4800c5d07040c0300b60310130741d545500503003808030a03800c40f0301c0552541000c000b81010040040d01c2c1c21f08844e00c10307404840f101810388071840d20074994071880c107600d1142c02112400151421031500003074141c3d2070841e01c956804680c15204569441124000762009100c000c0820103075005513040440381101030180d40402500c1e80454004c688075503c0b804242c1d025006601c003040e810b228043c0c0181892015040c000403044d1910b40d9040c40e003454a40c8181d0004003041c0e83c844490140740c0c0154001101c3c1c1228481880103080d41b0700030321042d590941404081850640000111800e03140340141c2a44a030302c04403849003041891600041c1959400c0001d141c0501c481000365108504200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 882435350 1250 882434100 882434107
    0x5131107030c03021b090c070c0b07060b011202090f040c0207091e241a090409050f010501060e0d08070512071b08071d07031d010b0406150f050703170c 67
    0x90000d1810703404404103090344c0e11100b9505c4641da507060060341c003d100408050b07101d8220741000fa0f007403042030b8004581c1c07480028080d4200105a008141002002d0b00c071061054050019001a440340c140f005a0180ce94900ca02c1289040e5004e91a01c075024411200d015440740950030454005108840020804000340146c0040700e004142403686015aa1910b80b02d808030140400103d6000d001c0340e64840c0c0c2026800c0c11041c00a81e215054018400e02c803107403c3e424000d813200c12003034071341581354200b40c0003140423801a00075941030341002e4020000c01d0666120b00c21181c1056100304ea083c0540d8200c0c00c3e2801c0140d028100160145844d100d51124170041c1c0da8031003407584d1140921b600810020040b0810300f8030308440310015025100490350790803400710018841d4120001d03c94400c0013900300544015072041000b000107482c02c0221548031100c01d0701240d80240c1e00b00c0011b4500c884070044510400140051500ca42008800c14008000208018030100d072010407448021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 882436600 1250 882435350 882435353
    0x3031404090c1e080c040512120a030603110a0602030f031f060507030e01020a05071404021201092a1704021c140d0507050615120a030c120309020306011e090e07050f0a0f05131107030c 81
    0x309108040c01410fd42b15071341a45820b101035168080d6410002c40c4000120009102d0015030510140d40b40c804450211595111030380500a50403c200035000280e42d440b8a07401940001b40000c4099040002040da807841e00314a90760003d070f040d0b00c4a4029070207100050500e45584041400780c240c41c48041030108503c10200015448800d1007409800c209001000306500915050b00303940180100e00710942e55400828100c080c440c58996003000700b00160340510001e0305503548031104400585048907031b192030440701070155810141494100708082401d80000104034000200c01605010807000380d10324660520500341d4054003c684c51841003070400c0001c80030a46c86000c142002c0140804030f4010a0f520740c814051600d9032050b0080b4551014880b5100d44010010400144044200c500040707459140038819680641c102800480c003610705810284150b030040e44c21455100e150a0410900c0011031440b03045550761201e2a103182d00f40d1600403e0385500944842140385441e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 882437850 1250 882436600 882436613
    0xf0a0e0309030a3905090a180b0f07020d1202031f030b010e01050d0f0b060102010f020d060e06150d05040303020d061e17030403031404090c1e080c040512120a030603 73
    0x4030303100040c0c00c0c070f10400d038001c800e01a035800100b40d40c170580307855141e03a0b600c0f036541e401491900d6071048040c07002002c060410881030803161040780103240c2c0511544421300306076a5107a403040408045a10030a9a42201c402076001d540d220003519a00012401c080e0668804c21000da00103a035000075400052041a84000c4000c0c01010180c030200d0102c0340544034900c0d440300f000300080c855080c0c0340104c0c0d65a80b00750080f40e804400c101c41103555111010b0400014240c0340704d00300c0145000070000303400749404501c0302c1100565660781c0340b620924042e00702c001c10300100103d0a00d9420300c4070117141c00341d501c60b030009007801300d1010480c542c46201c0915206160b0744140d0255560340649003424002105480489030f160030321040c1c0220345444118640101d41002d0b010707600d45164522041d500210350103004c0d02511a111601d406600101c9070300c03a0484070204000410001001142804410525400d55481c00c0e00c0c52404c0400305040c4d254003610340703c2c0001b501c0d0a0b050050003207 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 882439100 1250 882437850 882437903
    0x3030e0901031203020c010b040510080705060c03030f0c0c1204092009060f0405152503020606010e031f1a030102040311190b0a260f0a0e0309030a 65
    0xc4500006940c95aa51462003000400c020320426802241728040c0410035004042654002402172049141c994905101e11825115100d40d501c04c101001541c0e042804c1118008101807014610350799030324040300401c1d240a018062203c404102c0100d0103441404121020842c1020465495140108030415121190000c0030f8a541407084500056080c1e81110744c2a142035518030b450303980800e600c01250146500c4244c0100c1a811066000d5200328000c1c80380d40c20301c00711906510813035400c140c0003048440c001000f503445100881c009601449000800700340c01011210300b004100c00305a64040100345030406141c541440030010141212540c403100340690007181424610703101d140c254040300000c80d01031014444200c8050002400800141808042190755008181400ad200c44c055010fa08001040a40522955184910703210302503800b45d03141320100e0b151000f29000920f0f0001c00842c040c401008045000e440138048540080e0080320381244840d01086080c007900c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 882440350 1250 882439100 882439127
    0xa0b01060806030c10030e0c04061502250b091c060e061305060c0304020613030807150902090f0a200d1401050a0b1e0f180f0d111f0206010303 63
    0xc02502c0b901c940b5841c0c24aa20082412506e000f0420f6a40d80482505040c01074650300c2d0040d08080000c210204081e183d000c081849508580c91140c03441800412145012440001745042c02000c00c00c03916a44050001f07000c006142c0d5601e0040f022020848034215442244c50b181c071004d1203036111405000c555889804a00d0084101180d5500d06444c0d98008000352a0440e0110206066423030703a4003542c400345007111f03c00c0c4010340c503414030b44500d81020108440000c00c4102c070b160602110302034480000d0303010b020f8841a860704000300440c50700003014100d026655100e081d080031030f130b2842e000e040401110b600d07948403007106100066903031030481600e001c1800d2004028545556403080c0c201c0301444942600d41140f8807180300b43c10f84682ea144008100800c4c84d240100358440180b0802900c1200c1310721400310038042c898034a00d014110b55100c0880c4c02c8200200d40168100c0388910401065803c1c000d03040c2c0241c09003400751140250050344060010300406402c0014419802d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 882441600 1250 882440350 882440353
    0xc16111509010c0b0c040506030f0a06061407200604180f0902102715031b0206071101090b010e18193e030c0a0f05040c02030c0a0b0106080603 63
    0x212101c8000b0740041140e01d80240300303400103800a421520460140d90190800400c0f0b103035282413503100c114080304180c0e4041d9025160100005003c2c0c094048084501211030040b8140641c07034a6100e00340b54204512030070310200c0c0e000170b0300b0383c3e13a000e000b00040c00c100c440300b03118812403031a11000c40d035801d04456100fa140c00d540d400565200a03e0032031207461032400a4411040f0074083c5000b0900e00ba00380fa40c09902d070000301d540c3c02c0b00c284400c0f542c05c3d66613003049049806044221048640d900040240e000b4801107401c060ac500319149502440800218411100e5035032401c2645090703026140e41e540d59401d1000d040030f0841d400d00100c107042e00a00c0a9604c0d0306440c20b14107450000200030020710f1003207514483c201d034541d004c441e955850020380d090b000100e0640c0444039035140c07846401100b80302030080ca0003045074807d441e4410b202d028424100741c20320004259611701682544800d11803030301203034001c01165101a200b0200814a54500034000d440d09101800c0c05200707 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 882442850 1250 882441600 882441607
    0x1b16180f1d100b0306010e040201050c03130303141c020c0a170403030e030703051506011106040f020114120a0b01020a050729030f0402010c060b130603170c030706050c161115 77
    0x41342d03400640c10b4107544884400c140c0380d0301c9038401030310a8070680031070070030600010900340f00f0801540c6050b002ca0b402503c178041e070701081300d124500c58410001c40409030650708201aa8801641e40500510004001142c1c0700b5506911080344a801c141180c100c4100002001e10070503a00c29601403011800f500140b030b403982140d4034151900341c6031389c041030072551040010b11a03a00c9480c80803861018070055400504042c144000c4a200070401a40442c0d101040c9164580d03200301290384c0c8403449038010405031215105000501500c07041c150451250b6804000422018400c4100800020750000c2400e45c7c030301403460032603008107000b0f54943e2081c0104086c913071402c010141d21590900e4104000f807078514101d0010101048801c0d00901d50b0341481142c4c034041d50000303059038010b030358a44003901c07442e510144a10074100354401075002803080d42c00240e6103400a503044601c040300c017400c140f4682580202086650016110501803859280d000c2c185541c00c1402d142d0f1a0a00e640f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 882444100 1250 882442850 882442871
    0x3061005040f090b182a18060304080f03010e0a060504060b040b0d0f06091409010c0c080c0c03010c170601090b160f05010c051b16180f1d10 62
    0x6151500c1c4030343c001daaa281c4a1800c0d090b0380d501d03c0600d6030345281640d10b45e41e0420303134007590540d24000e000010750a0400300c18102c2c624a081a12291640c9104101c0350012120510100e500003400031150710109102d0040031125901c0a507000e04004001400f1920f40f440e510b50079113800e98000740c00380d03242180511000c80460f045030192422680a19a41c2d44807511381070080c00c9138041042c1c46468070002040d000380d01e400c1a0403c0045841500307950726202d04e118200ca40c0c04000c0e07004203010710042c00c0000c0e69840540151203800d42034400381d018030f402103800d40394135500700c400044a50520812084c501d11700070fa0403000a00e0440406030030b084c0c0510262060121030b00350400c11040c001e00300700d402c40d14018201d80c818000d01455217055005019071300321201c8042ca1030351007021a00218000a03402c9040356148180e00e405174500001600790800500b500048903071101202c8929104601851a684960503007031303402c40c1d103c070520303d00300b028440711f01c15040d060048042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 882445350 1250 882444100 882444119
    0x3030902030d1409100e03070f0617130b040206120403092d0303230d06030b010e04050a0b150607051b0f0f04230c04060914060703031109060f0306100504 68
    0xa518010582c5d8071014548415401d42d050803108210700ea062040c048089032000001218508441d4140c54022000303003141800075041004460400c0c04807440c04510000c5449040040d81150000e0034003440c145c44000000d03035140c0119000d0780480d1158004010066480d0b2038510078542c0c040f4812007844142da030707812140c442407101a04201d00e0b060803444609800e840e07201180080d02d0016902c00c1e188040a010b0800c83c8000d441400404000013400d05544400314441c540c48000780c00c074078004c0d9450500c11751015044d1007040b00b1030300c4803080c183c450b00001d1100d94040c00040c02504402402e4289094100c040507000e031104555101b4a43c444090f581660081110301299801c1640c0b22131403a08800ca82d100004048441440902c52000005000759042c03540c036001003d4403240c480400c90164000c907a004141000114080b9200c1c3e8440c1c0c0300e1031a00e0403c04e1a140704003000030f086402900141c07811240000502c140d91501c1005060003c1d62030030440e0401e480c06421380c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 882446600 1250 882445350 882445357
    0x1906090e06161b1a0f07020606120f10050412050a05040b030406060e01060203070219140d1716030905010c15050405010b0312040501170c0a210204060c1101140901030e0309090403030902030d14 85
    0xc90040d4019602b5100c914014000c1d006900b400e14211441400e025804c840500416101921182004060040760911480484590b02c0050311098a402e05c0c140000c0e80c00d51004009498913540c1e000c001c038110300b401c02800e001700707000c2c0e005580f0b451260040001c0c0500c84510826804c5080c1c3c0100002c69800030701400094045a000d0b080140c0e0f07083c40d450100c084c04007982e4850700061440c1505040740c000c00c1c1100d0280d41e40c041e807180c480005403804c0398940006001d01812070b0680e03030110507642080768854070400c0049220480800480d01d80300c15000c55440011000c9028000c0d942d202d8905040b8003054440a074aa0400040010040c421110301004011804007000141205072001020341740e0f42a108540e1341d560340200070041c9640150407a4106034104100c20380e0b40c89203522031b40120000c0202850106004011740c010003d029141180380070a10a840540c0d0b40c8801c00c9100ba4040d403408141c2c1141417042609140c11582e41c2c00c103006e03001d120b5103074031341214054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 882447850 1250 882446600 882446611
    0xb0409030f111006030b010602120c0a021c020d140c01031a040510030c03030302030a1b0909051314010207030206090a080328051906090e06161b1a0f070206 69
    0x115054803a081c03020f800c00004402540d40c1a0401800104001c1011111412200c56600740c99140e091f00c40484024494100e450b0310f5980000629000b524042c0e8a4102e0701081355a1100c0c860242c3e40817401c801000d1f038055030340680420490424003018005502030701d509180400c6040c2c9031020044142c6c8920403014001ca030307141c0001d80d4a91004048001858110650072219680c0c2d18000340a03600450b480e00306c1c0350500c5281900c3d0b94940c1c140948180494a85150305420310208400a00c8001e08540741c2d40c195055601c0424019401d402280c41010000369640019041c041c0c603102010f02504001c2e80300749840303004215103105803600b1400c0158060711104800f280e140d802d05850103001070705454402405032a504c0d125071504406142d0b10140003440c2d90711039950481d05682c03d14499a0031060004a0701415003003119a0f00c0c1481c1401078a03a10340411000703441c80c800000700d516000e0044003039034a100b85483e256202515501d03c00881c80d05900003521902e02501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 882449100 1250 882447850 882447857
    0x703030516080912060402130501080d0807200109020306070e010507060b0604030b090a02040506030c0109030b180d080a141306020a111006051f08010b03070309060213090b0409030f 80
    0x1e00d40801040e4411180d200b0720040268044410440b15543c5442d400d94003244244200ea202011042190088504a848800c0580703032144c00c003d41a5002c84008040000300548468601101d0140045c0a01c01100340800041c0403c514818035140035400b0381880140b0085070f0417500240c1e40401100d52455202c6c00c00304001200c0c0010502902454000401464000e010044444000a00080400d000300c1c0c051000c1d403681c100303054403041240c01d13050010703402c4007061001c520f582d00204e4110f8924810a00494802e0480c0350038034030b4901da88000502c508060100b409060301030741c1c03c003081c18016170405040c0b01c640050003913101440102026004211003041c14010030820003854035080c10303113551444500c0c1040042005006c0c4a101d104507000c3c0181d803c6c4180304d0f0409103502e0fa00d8411559081807001c05480d00f00034200420152100d0b0254000348440c009800241e03200705070036040c6800c00f4209429030700c2100e04a4001c6240204a4002c241d010b0802c0b8000030035400e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 882450350 1250 882449100 882449137
    0x507090e0601150c060609020c100b060a0e0307030c03230c0a09090816060b1002060c0301060804170c03120601031b03020d0b030703111504080d12020d1509060807030305 75
    0x210640f600132411801404c40341c646500000c0403030241e0000c20100a00703400782c4641120085030070048502d040c1c03096030011828012120b030b8500803c0e489415520040031511056a6541c4040c454403554008403103051481860480411002c414a082c00b1280009450107560b0040400c104400521030300070707400d44a1040d4030500121208483d580c0c89101007410701090345080c24000385c8001489a40118422020074440c2480490010300034410b100c112071959203041011900d120f0301070801c0c1c0340400b1184502e0006444031004000c410300f0301e400b43d600c0d503c0d00318540340d000d0402001c90341407504240c07000114038240551309070009580d050060300c81d10000e54a0008211000705d90741c240c1b25000c1e001c000e208000003c5984200102c030006040b160041c411a441d029910034031109a0150741d2201d0140e0041c50001503414540b034006050046111084081d184d5a000d0003c407903e03a0582031041c07048900540002d06100d01c01404194559a0028101d05c01c403014102c1c06015103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 882451600 1250 882450350 882450389
    0xc0616110f2e090c080f03070213020c1911100c05060a0c0207091a090c0408030f07240c110f0c090c0d0603080307120504030509010305100e010f030507090e0601 71
    0x103022001180090b04400c11603180540380c10b0b540302449019600300f511403003a0b03004180c000001101c1c0070543c003611200754403001c194282c000e9005104040014040d842003042d120100c00b003080c000c6800b900d04108104101c1d4203210696408402c0c0004002d08440b040c070210701c000924a8000690030740c00242c0004840040741041c0090300b200b401c0390300b060510381340074882c0011545c011104a07000039441c0c468450a105034840c0342f14040c0e03207420074041d0000340e680c0030014080c41e60060703216400f4900c0384040c0780007240840145403d0103a603001401c0d035990f8803c100880c2540840f00030096a800708098076905c40c0080c0109104040010000b020402039205a84055658440500000e510d924100310250000c0351485c001071807d881c8112a14424022140205d030151901450002040f0045025084c014042d0030081449040094100e0350303596560f00070028802044c88103421071822a0400304c081d800f014a190a01000c07941d60840401c0d05030448010040c03410890401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 882452850 1250 882451600 882451663
    0x70b07080a020a0804090f050a020301030c180906050a0c0305181c0210060602011407021c0e06130e0a0f05090601060c0201140f09010e010f0c15020c0616110f 70
    0x91000a04e00000441c0000b1409000c1c2c1144403a40c2e0425400d1201d030703a414042a0403400240f2026004181b10901080440c0e02c403e2105a44240440081034004035511501d05442c0300b03076040000709a0b617401a44020340d143c0704682e00a000284055811a829122a0f41c5c41d0802200710b45500740d003c0710f440c0c030a40200720466400000e1001407014569424001e40248238600704001410445800551050310105119101600d0307190503485071480240e04031520405000c080d60058020019507104005c00c6000030000d2024203070880003860700b840b0704010703070303003032044010303915003060203001c000d213004a28603056800920340041070242900048500c20f600010000038110b0020716420760885c1c80d402080203400c02c1e00c0d00049080d01c00c0044079013640003514000001c45061803040001e240c5642c01040d450411401350400c030720503800383c2c1400001c0d01c4c480113203154603035091807c1c0d80100074a0307003641d001005840448022505161141d07012118070412b045801c0c1c07106440c000c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 882454100 1250 882452850 882452863
    0x206090a0513020304212304030203011b02010f02090d02091e01090c0f0c0b0a0c03061502010504060b0406050303030a020a020703060501060e0406080f0c0402180414100503070b07080a02 82
    0x30300418441c80c00b440504401d000390b0003500c094420b034060114030b40b415150b1104010711140260749800900d6200c50016400120011510142c40c104200000c0540c3d82405056909c410b4400790411421850b14041c0c2180e1081c98090289401400320b0400b03a9206c1050b2005d59406541078400c6648001446014410821601000c001400000b20701001c0b60f0380014800846130300d8907034105885203030503a01080c83c101c0c010002c0c403001c0d000911008407604803803100012410085441d03601c9610340e12010520209840060b1740d9138040009110550040e100c407175200380d404003c5a030611012039101e10008182c22000354000821000c0b0510821003500115088001000603503100c120090607041d16070b02c0e0b04d124504110000c9503000001c02c00780c56095035000180682c8030080c040c080650442c410102880d1035140c8101d855440c1e9009168a030540f52413001600c0c0b406501611111400340c00090295026000030b0010300341070230031281502e400040702e640310b044040d012440c055 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 882455350 1250 882454100 882454109
    0x15050909152d090d020316110f0907030b0f0a050916050c07030c08010e0d1e0504170a031803030806130209041e0b040e060f0712050c130e130206090a 66
    0x100418442d1102c0306210034000d5020409070b80c481c18103a00e00300d0b07890081c2c40214680c80e090f000740342d00282c1118440c1801e1103000d80010b0b0303094000c400203070308680122051008030752a912140790902d003208403050f1145003150101440d500b00f0000c2580707600000c0080c0f40c02400c0503180210180103074140c5945400310011a2411a140d1601000034803052194079030a43c21328030022074043c0e01181074200c1240956a020500340411603001050509160b004280f00341003101055050100d4100c01e00280c040d8014001c00791140303802403905240014246400c6035081d001c1c00029030186003a6000b030070031924004001070800c640c00080c414815000e0b4441e2070256070341c3c80c5407803c105880e13072221001410001c10f00c126090005440b0151580007442e04903000040001c0c818001c484d400055614095007404540341d20041220000d40c0c2c50280208041505d10a01e02c044004102905001419a16a0500d0008415088140000203109400105103a00161144000c890003031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 882456600 1250 882455350 882455401
    0x2070b04080a0b22020411130f030309081f090c0b07050a060609150506130e100905070e01020d030e011b0903021302090d080d090c091505090915 64
    0x45a0700c405465680c0c814200c229403440880c8001101503030301e64103480140f10001507400da00c0c0c2c100c1d0b081100403c04c01000340c514181c18800034102d02414010310002d8003c05003c218180d003581009071030803d47d6402805140c0c880f40b81140050549480b10095100780240880e6110084c41c2143c01000d1503003020500c0100420444203000000805030b03050ba014550402c84079440d544220b0036203844203070b00040150f51020401590910f4030007040452455401101450b484011000f1141c40c00e4030f5101014424410600c0044904c0c85400d130801403905080c0320848100c40080d460703510303418030750041c950341d0f0b140d0750454482900f0003492881e079480500d00d1000501c0010f2b051003a2400268001c00100609400220940c0f080300e811040003400814940c0c042c1e6500910760b48080311825400d521801c100e000214840112009060110320100ea02c0d80c0d080c10f14250300d210750344424031036002d4100f40000070802143c070f4546c140c25907030740d0b03051503550600e0091030700001c42d0400d440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 882457850 1250 882456600 882456607
    0xb060d1a101802092e0c11060705060a1811121c0f0212040e18010e010203070f180e1311060d150605030f160e10090f0503061b0a02070b 60
    0x2c0e00c40e034010101e81108035010002c4c3c0101281c1a4807101020401c2040c0502c404503c2050074024108844000c0c032030030030000c07241d010002186054120f860200d69681c40b10301070001840c914002d0100d0b50b280207911070310102c600d4440e1a00880c201e4200780c0241132441102d0310840c41400200c00882d900700c2d461003822103e8000608a6103000b25080060003134140ca140002c03242012030b03040320b078800748005c0141c41e0003664040616095401c1b5000c1c0d0b6070b0b1349500020b4a4280051881080079441d00900d5030144400600090132051540b2044450384a01f4402120003014851700801001c002c1140c41c8843d14020060294100e40d01ba40803130003082c400040600340e0840a40c03800a00351096080d50b6814056403580020340d5a071540808040020b030340e140101010820042c42ca00d000d6000c2c20071440401c0522074001c0c900700c00145007110521800c01c0d0000ca010080c40180c1c0181041c0c50103280300a0342d0006201010020300000a02000c10742c4200200390117081448545541e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 882459100 1250 882457850 882457889
    0x5130b0703050d0c080114060c03340b06040b1801270e07060224010506070602090414180a081909150201020711010801120209060604120f0b060d1a10 66
    0x45203000341f2031601c01d07011581094080c1d042c514150f0b442c00c0c00b143c0c019410110210b01c203825a10400300c003882c016100c40300034110303540c2e40c0d043c080d2868050401041e15040c0f00d4240000d4602040f03c00d806901150070303141c10362070039440d0981143d040038684d50101c4c1c3c8180980030015110b04643c074280c3c2c180359500406e00c1c0080741c10011078100350215025082c00c0c61618094440e040a0701143d54810070040250382450001001002e1240c40b00603e03000b035800009040f01d41440c13100c41c84210420400a041d01401440e107601c00e141c01c01007040c5806552203418902c9680303191070161280c7cac01d801040038080c1c2040c10103030003e01c08071016032a404c10024000d40003020103560703103080b052861082d54068410075050383e04080508000b0140e580a00000d200c01604558206504000c0040c550002c4184071300d249100b0f402d14404042c0608203146122006071800b440791180c00003200c0040c01c2900c1c02851001e018440c07540d2655109001c42d6100401e5000391300000c10f0204a86 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 882460350 1250 882459100 882459107
    0x150906110a1e020715050901090b03090a1b080709090f0b1f0e040803010e091203130b01080304050f130b130e010e150c0d150303180605130b0703050d0c 67
    0x8010886401c1d1440d0410030358400300d91350002480368a10080c00810b41804440c131503002015040018101000d0359590b0b4081184203a00440350700c041038114003241d000700b241400b1495520601004150700203410300d00d850b51113407668456007403102c0d9503040860401c18ac48442c00121904401444080d240070300a000080c07100340c880100000380f00901142c1041c0401c140c5000d250000e45142c00c40c0e003040e51040f14240081e00505c0d40384520000000e00308a4000118460740d080d040720240d035000361800d5109540103030441c000c560010300c024002601d402c004c5020841040302c90350748400c0509224402041d000c1c142c55040b260740f0b2008016601281c002420381420705000300321088070103071129140c56409076124041c00c0110301003459149204050201d18442c0c0000068910840b080d001036040c441e401200481e60284034405003050b403068030401010701782482032424015040c00340c440001400303141121070011454070f06142c420029203c69080d1080304201c00c104031180039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 882461600 1250 882460350 882460367
    0xd06020301030f032c1201020705060103030e030d0908030307050a050409060e011401030b2d19061b050a1209090f050f070f0e0f06090d240603150906110a 68
    0x960115560344120145d1381e4402e040701400c0b41a444842e20042c0000041008850300340c141089259001c2c0b1a6078086441800082e00a40c425100c80c0c8a01d00224103150400c00e00d01c840b1800d01070007110230400320502000f180d42c096014500304e603640c0e8640105440a02481d000401140c1c40d0032004074280b0742544149040e10403220051680c842d000700110151918806203a4002d019190501244100c0c900303211002c4e0140d4120301c0c4810900c03004228410008204001a0b008070a0200500e6404c40b07120a0780d560f81204454200c061070721804d0f543e000c1c120780140407858040307417021814404e40c140c1c4050015000213101c844002c2da01500a000203843c15845100c2d80ca021581c0700b4003030b05e40b2030484241a110440c0421070700341040701001000700100e410101c2000b0412403595090200c1311014411203c15070075240110115160460410709036081034034100c011f0021501402d03130b074107069144050102d00348115190032400340200c40c0c000022000041040380c445500300446 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 882462850 1250 882461600 882461603
    0x15140c0c03010f110d0510080a06090b01080105010506120c0906030411010908030a090e0c0d1e1a13020306012001020408060c03040b0c2b140703090506150d06020301030f 75
    0x34440e11019050700ca0413140383c2c0d10040c4c1414000c11070700040c2160364004547c414101000c008030150744880036400e00c4455001114400d0703654a00c80304020300e0111403809065888001c000640c140300201c0d03214030444004030150802a00042c01d10b40304802201c40d40503002e040e007512410a0f19192801401004880c0e000c41c66a04d008925840f000081c1c2c0c0a504031070390f805040b2490a00741829405000e400b24604290801000b644d103240d0380039030300035003411610b2520300c5911001c885003191030a49038920b0700c1e04010001e0070741d652400f801240284600c4c3d001070b038176100d5100582e244150400c812140020526441425142c194013070400c45540000366286642d928a10443e40d1004a074014112402d42011a40f8128450091308410402d5130084061134010400c03040c8050121680d0066140c6402801c8540803880c082103070405c2d2642001e00c0858400d694007030702c64000415201c0e44014030f01081400e50f50384c00322041040d40044045540c0d507140c0c104082004502c120 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 882464100 1250 882462850 882462853
    0x70201030c080c04091a060f040305070f0503030a110f0f0618061b1e0c0d03060b09010c0308060102070b030c04050907090b0a1d04051303110c030715140c0c03 70
    0xd03205545026015091043e04070008242ca414201540c16005000190304482e103010701440495517501c608004003194105004090f03202c925508d41189020b805400145100070318450422050303e002054491507031940c1042c803807400b41585181e180001400841c000c40c0b0910142d0454041d010801c0f6000714803032051035500e0841d100182d60f0f90380c0203039172040099104803001b01101c080721000d4042040503da60840c2040c00450355122a0040c2c11405c1c400d41112100c070322541c2d018410170000345100394115040104650001c1c142004042001e41409906000a03030660b1091000e440581003001e403440c0c89003041881f0f400560401d00805002d21500710200d030049002d06607040032280c4000b0a46d142480b00c50044444840b6413100c052a8001304000125035629401818410801c074040c4c050701c1b041d0360800401d8602000c03a4200c058000603404800f41d20003007131a80c00e0f0748000402403140506400c04641c2890691200c41ca245400f040a4080d03101c046000c0c08902401c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 882465350 1250 882464100 882464111
    0x412030e071202091005061c0b0d02060d0e072d053001060f0602030706050106110a020603091006150810061d030c1c140a030206040b0a0e0703030507020103 69
    0x45a078400950050b108040c210340d841c1c000501d0908029903214184014502d0312940e0b4001080c01600a000058004c002e281c0303200e180c000e450700c110100c1c43c0b003c8400014803041a00030400c00d20401c0a140201e075103640b0b00c3c074001c030000c015400082c002c2c604d120002e804c0f001201c0d00e4103d540e00020041602030b400008080c0741c861000700c4160555503a580c892035856100300940007100310351a11654031030700002400410440e07400020240c3c2d070050b65030b840440c5010790803590140c01550910012403a03115a071200010030040040d03058071600c1e03483e110300c008145040c0200401035411814030030041008030100f04055080713841c98940d034405440d01d40c0203d5018040340071b6800000e40040b060101d0021804010031075a2018003500c441c0700f40c0d44007044004c6180c80c0c081c41d80342c5030000d0a40410900c3c2c4581c0c40b408005401801013003480760790081d15440302400180c00440c0d00d4000c42c09460280d40b090150780c0c2407004481645669140290958020501c00c3e80804d10f0032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 882466600 1250 882465350 882465371
    0x6080601080c03190302150f01090b220e2805120708270a1509050604080a030e130f090b1f0303121d061005030a1505041406041203 58
    0x1401042c2050020042e0006841c0103c41446000c2c200c90194110312420100c030140554484a0301d0244404da450144039604068045065405001020f80101d10340c500c0d02030b604103503a82e01d4000d0b1004103c007040c030f031400080807132422121040746480035210040c000503c0308243c22601c88188a070042e11030001d5401c1440359640900100030b81001c404120395044240e03c00c0c18000780e812980103c500780d030301080118555244540028222840700c482c5104502c0d0003501840061008841c40c0d403806040020040d118104440c005090040d44035080c4580c0d681e450f440907820342c0f8110100940e45d0901c150340301901a42405a40510300c190110b03060120b0002c16605102406682ea5503c5145a900720350301c14051400301c102903925144100148188000301d110605180700030111818070711121001200316600c10f6100c7d510281c01c40c0300140201d8a04030510130307441c0c0001180d43e03036820820002c42034114942024010320081200b00714200b1264544034046640401541521 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 882467850 1250 882466600 882466603
    0xc12030b060c0a1b0e060907120e0703030e060708042303030c07050406060912030c030e06041e060f02061303050f0301063f0e1015062c061b060a0608060108 69
    0x5405090703440e030300d22000650181032240c8880c3d0230a4562504d4401e605d8888450002c450f805100710032160019402003045c10b03402003e0340f440440c110307400d615020256854800910840c443e510350307181d0107404600c24000c1c0c03002d003c61012014040c0c80d980c00f106000e4649070211401424810f51030054041107940c49002d00100740e442c0548030740a00c071003c0c0c405035103580d1142022010440c0414104905883e40c0025000400e1f40d00307102a8005540d401d100c5100030a81c003d401040041540340880d80d50005440c0d801990b4500d1048141d05d071410b0031100d034458200c0d40d04101c80008000a540f50f0711400314001658510f8aaa070840e469080200000d65030b40b4060b801c4503903403c90304c1400c1e140d80d40100344907040c9100f220300721707207191030444142c64a0981e5900018040b40003001141e0f080042c02c00314400101e00300c03c000320a40002c448030710301c490310741380505d02c081000385505c18030740740d03001c003145010044800d1444c143c221000544054081e03280f00e405007200000740101d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 882469100 1250 882467850 882467903
    0x1501031b12020402031306060803090301180f03140706020301030b22031d061603030506030f060106090e070302070b09010203091e0a060b190605090109060f0c12030b060c0a 76
    0x241c424000910a140d502040040d4001030020101d106060b50703030702d0000b0764a11408000f030034000007031601d0364000c87c101801c5074040401010554012080400001c0c003c0c05c1034900b03a030349401e0941c02221101070b01e0303ca03800340c40b40052000b4400000407051200540c403891080010a866000d84284100d100a030010301c000000c020480c2920212160480b8112460880c00b01406c1c260070300000c0c14031980940da107100c4c180c020075a03401c148026810140207800c00780e4011801004103502d02040103200480900c24107044202c0840410310f00791298046804581d00180241c0c3d160a01800da14001e600c282d800041c03501c84c071034015889140046c104201400380e90082c1501c254252590005026003000c00d07980214840c000c488401000100e000141006596031912003801e14009413200b40e4540003082441500359a01c40c81641c0308200d4400c160b4003400300d4030f191602410550107482d881011b00e41c090000305040080d1034001400f81c1c1c503d4080c1d882225554003401c02c11824a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 882470350 1250 882469100 882469109
    0xd0804121127010b030c0903071d1b0d0207171b0d1d0609060708030c09040b0906030a1104020c0109150c21020a0507080703050702040f020f0d09050106081501031b 72
    0x400010130204803603c000c0c580c400b84c0071a84501d03150080c00041e0903c2e450350800300102204011241d0003170700d04400c0c00e0b44054484803600300c4c040e000d5032400260090501114100d03800040180420002c0002e00310400350712611651950040ca89444202c02d00720005c004900c03d00803107800e40c503c100b00065034801d01401441c07403d8001020301c481d60340694000c0b50005070800440001030113160040d88181c01d2048110b13140c22801d820042a500c0404690b485920504240f2640d0f80e0080f98582e00e03254402226410306c00b036607001c24007070301450b503c80265520780f50540c001c0c443c0d00031215482c04074104007049010310045056858103859104045e440305203c0520ba51801d0f10360081c450343c0c819040c114104401a955003034642d01403c02100016400f04840c0c0860500c1d001c1d01c1c008100641c0154240b4191070341407c0107008000e55540d281e0346440200003409400e40c40076018103545000c0c6c8501420101040c04401000c0c80111003505141e0180c03089034028098900541c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 882471600 1250 882470350 882470419
    0x309090703051012110604030b07030b061e0307031506050414040203070801170f010501140f04090b06060f0d05010914070f02030a0f031e1b1d0d08041211 68
    0x104d0502c0c804604829550300c013203d0b040d0f41401d2100c03070b80c1d072040040d0004511500c8203c1003031074401c00007000d842c03805202c0ba018031130501400c0f000c0441d00c00e281c41d007c1905000319032241d41d405000c9028200d514000381c00c040103903101181030307035125008100355280f085495682c2c01c000d0051104a01c021203103040040c05402c01800003170b002c0c0c070780f400c210a604403c8030702d006248007a1070700b10ac800780c2c0111a1940325071803603006410013070400c001c0400c00f111f08000b80d540d90f03213030b0b102e651400900d050312500f40010050a504074031800c1c0c9200341180c4904010350341e1038410820042428900551300d0320000c0740000c8078103220700810b0024074020f502942c10140400000d4910600c0440090203041d2145c0340e41e505610a40000c0303080554014020030626641c1c084d074450018142054010010400c4100c00c3c07801e01036807418046102911081e000e0000380c1003503c240c1c040e94112640702e40c80c442d2038400b4403c0421403001094001c80e40c900840c03803400104070204599208416a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 882472850 1250 882471600 882471631
    0x207120b01060f1110140c0703021b2206050f0d03020a031407060c080703060f0608041103010608070e061e031902031c0215100308070b070c080705030909070305 71
    0x1d05219882c580004201414103888030104c41081c107051903049907480c1515a600da030b5080d0101589001d01d03801ca42c9880c0f80510340307115514000c0d1680700840503402000007440882c1903a4564004030000700701030301200c4203030b078000d950244060641c500c2003601c41c914a09803c078852404480071100749505030010480541c19503810b0b58807504510400003e02c801b4030030a8045021800380a082014659500714603140c0074101808a8180d50000070440728146414030028dd002800d803500560002030354083d4a515000003400b4000a0300503480c51702844400180030340103641118040c02044451a1411031070b041080c0c0e02103182d001e9154994030039481d64641c00c108581440c10940060705a5224440c2d4a0418540e02c81e2083d42400603849891703003200d0508000c12094000104210b1620b01d54559160341c1c20034011080007410900700a008103000301d024449a4109540c800240303501c0301e40300e04200d901c031380083d05114001d1440340000b9851074460f00c9414860442c1c0743c0900750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 882474100 1250 882472850 882472859
    0xb01051b0312151018090912020d0809070e0a09140d020f031c0e0109080c0a15050f011e1a0c0c0406030c12020102010b060d022107170601030f09030206070207120b01 73
    0x5045030682a6a140880345c902c02041008440c014040c2c0207015501c40c456104603050024602a102d200070b004214020042c040b50100c0410410103d80c0ca07040e41d03c01039204d80c61b00b100280101c4000030f001e0205001036070131200000c82c0c90b441314810764003950f48040701194259203a125046040344241e00c0700082818600f8107610007040425400000203c000442c0d603a003445600064110405500040c8064100181505840d030960584802130180f818100d180d1110070070306018507141034084445100311150089240c0c0021301c00205042d46a0911034441c400640c40b50140b054035004581070035555040070700a079400ca903031164407410000c0c60041e90505102040c00103d045540b241c43d072019650b0394501604018841810040c0e440381c007148402d16a05002038000222141c81c0100500b41350005150421214202c181003040c0e6030f001d004a001f001e2119200e80e201e131030001d101e018564001509882807400341c007202e003101d0f01c074104d00c0c402040e01100144418130120041c013 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 882475350 1250 882474100 882474107
    0x12020c0f0d110d1413180f09050a1101120c0c0201090b09030c040b0105040f140a0e220f080c0616030612110307030b0109091203020910030b01051b03121510 69
    0x820034840c13020543c104485401a810a510181e01c1034040c44200040405580554031551800d1010151f041000100e00d950302138803048d4414019140310107820b2200816405061002c481440ca202c0030061030105080140c403e500d04682640000c60f40380011407812540300840f500018010010180031018000300070151900c029014104603080c800002c50a4400040c030014140304289940e050103100c052282d03000d141d5112038510a044014821171448400c0e600b00c10382024415030003824654240708805015940000f0f21826000550011503c4040fa2803402002d00e00c0c140d03588224400c0d000c6082d190940141e02681494952180016030410040e034000d61003d410303215065600d8540c070581041c01d9112042160f12401103004001d01407110160300006030a04506116086010031103241054120b0070905a555281c1080c581c00b0b6030985503503821860b20f180c00e01040d10120754036a0400f16080701e03c00501e4001c1107080d00001110114140c0150180300702ca03260f000201c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 882476600 1250 882475350 882475367
    0x60c0408063304111201051e0607172b050106180b28020a11030105100905130602130501030b0f030a170409020708091804050c0d0312020c0f0d110d 65
    0x11603105544140c0070f0301301c21842e0040c10315013030030120079400f662510090240c0c07444d440c00d0000c000021074080440c26590403040e142c07500d40054034420b4500c080441e4545900c581060140e04200054100440455620082c5569160240c050102c0e90742c8000640d09104400b0480d0f141c0001c0c2d04050012810f5080a4130414140d4070300090381140303c0314400500a1521b00d11401038001c0b041180070f116500000c8004500160000c20152400741c4130780010000900030311168130b8640c1302144e6a4821b2001c13100d00c298016000715602c0848802d070982125040c1b20305c90101c0d06203011315081d03140001045999107000f40103001004010765510b46d4166a034070110a20320800c0c440072804222520103419021b200380d50075030340d80c14858104280140040040f4507400490401c1000290b0046040b050881c0d00ba22451840d0140707180580e42d0200070f80301a040b0610220380c4525148001481d000217492803403d842a00120f0078048428030416481142c1591040d07480078802807240548 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 882477850 1250 882476600 882476701
    0x302150c0304090507020f1513020f010e040c080a110c0309042309070311030f2505180709080d020307020d02010507150501050310290a08060c040806 66
    0x2074030b14068544180e4800c4500982e00e01006912002003540e9140c0100003240c0c2d0503000c0d401f101c640386000303403400000d01c0464000a00603c07004010403c00e9008044040c0d20550081040c89204503040c001022002d04070f6003070107000d0418a0310040011408202d03224402d4020246141012007400c1c400640543c03164110403000700c071194000300249035081c900401040d000782043d1403460411000034980444a244030740c1061110b14288400001c0c40d42021044440b100d0f0704003d40746030000b10041d140d2000e6000707203c40300b0003070006140c40c8456110b04000c2e190010b4050320b81d01816506c4000e0301c042070169004000c40c03005481c100320b105910601c14900b40e49011140e5460044805c0101401c04040c0e031200c00500c0241b6041c80044018841c110040180655403000e07110380c0082444180c0076010940e003401801d40701d842000d00034040e1002240c0460801d60400180c40d4060f10441260307019000210300311540180040e82c4c00d1010700407500e03145512403442146002e481c01c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 882479100 1250 882477850 882477853
    0xe0c07050c220b2e090b040305010b0307120206030c0d0623030708120403110f06070804030302010b0109050a061b050706020f0c03061b03040314040306050403180302150c 75
    0x10388100d50b40e500c0c2c891019080e1003080030091080c0c80749040040d02e00446a4500c5004030201c580308400c03603400f1310b0340f411298043c0410000c942080603503449007240c1040c25680d10004010091140c15001074003580d00c16411608034540d00c0c842c60505201055000b94000d008001003000004803601800ca9031104001c00501c0f160b5070201c1c4100105520048040c142000c4200000e51506000707070401000040c0251421b000f03624011842803046000080604211030301640550301c9540000300c4404000d080d070341d03803280e69003003429035500700b031100f20019820401301400795403240304490202c4001801654400c0e0400a05865295110b4001003803048900c0144003c40e0081000000034003c80e00a8003100909002070780c100300300060350740d000360b004000340b0102c00745201d20000342900c40c92025449441d50b180445401c403c1c40b6845682e10300124010080c0706460b400a409648030340ca425003541e1040700215106c0c100c1e48000381d4410f290b90050900080c540c402460312819900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 882480350 1250 882479100 882479113
    0x90614040e0a0912170a18020a03050a05100b0f0906031009060b040c0c0b0a0e071505030a0e0d14090607242702010e01172e0e0c0705 59
    0x207070981116400c03a4042d80c0c090700c99044000344088030034580c9a000c03d910b0300700101d8905418184481d07074090700d60320856643e0105030340707001c83e502c03a9202e0b079540c01003c0390400c80c0d40b030401aa90300b0014000366a6030048410b07c44103076a261007400c1c0130b00310280114510034420300c1080040315000700141d4060151070446082000184204010148245000603c2803503100c1131008948480350303000144000e07005180041800804207660000e206130021030b94800072605d007802c003a9240e001c8070106003582d020307036007158003d405580714070a00041080441d91140c060b9a44018403104000070803401482610f50f045240024040c40d14003904580c0b800e00035a82ea07440c20041d01311001ca54940380c2c0480c1c510303119240909032811800c8240f0749400324446008050405003a24001c2c188041404400800e90060405000c60f405801030f55100d490151309018403d00940100016090180380f403200311030010081006407044400c40d51079668541200c44943e50000030305540364070030384 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 882481600 1250 882480350 882480359
    0x7050c0105040c030b0106182102060a030c0f090308031504020c030a020105060f04061d1b0d090b060a0b0a0c0c030206040609180209060f090a0306051018060609061404 74
    0x900407240501c3c41100f0340e0003810718504042ca00303494180c021408100c004c06e0058121102c005894050301d541200584808180381c4100040c0e1400c550000c0d0403000105d40b190100340c25620509c0141c007d521508821110000100c1d19001070740002464044240302103813003442a03a80281c1000405040145072244c2c690102c0c1c51038100188010041c1e45900070400302d4105082c0340c1001d154103407002d00c0320314103084101da1415618580a0042e102004c0011110b20301040506083c1103c0c640c07155076a1102d01c8088003501d0329071415511040624080350040c100034000b002250020050309061948411b402c403901c1801076000e0321062200480400540d0720381e40100006d0601d40c65050f05c59203416135100850031802c2d0000c0c51548140001d4445450302c10031224090b41101700341d542c903010000040c6100382c182c1c0002c0c11191800c820042180004003c880030340f10030340102c03003628111000d41000c2c0c54250240d4400980e2442c002c20002e8010300011105a6003000440d05150b200c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 882482850 1250 882481600 882481603
    0x321110f0919090e0c0f03030a051602040504060b100e0325030b1e01060e060f07060917031e0618100914040317041112070b040308070309062607050c 66
    0x11030b007020b541182e48008491403607a080150100800c01030352240883c1013200c00223030702ea0041e0140081449070006101c4d14040b4411400c0146542c0180308002c00e042c64208000209141c40c0498044d16007200801300b15401201500380c02ca400800421131010340c681d500700d41c0600da015107450308080304004070000b00c0c03510340140f003448841c0c06014450b0098030600c08004040e40a007050000b0580e10040d15129a422145654010765a040c3d440d0118074110004040240d00500603106903459000c207002e002e0019806003d0741c500c0141103150005034100801d0741529155403001d20540800f1160041c0c100c1e103584800710b2007000070040c0e507501c486415200e0000e414074000807540104002c1681000000d01e81601e0a0408506494566240280000924103840c8074001d030344c2e6040e1501e001000110054080054602d82f920fa82c1c0c50301c0304494000e00d40c114085501c43c003021074414442d501204d50000109a8040a0880c4aa12400241000d0202c0040010802070130303190400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 882484100 1250 882482850 882482899
    0x160510051c05040c0b031b0319090308060102060c27150301080607023702060c01140105210d0e0a0f06050307020f010501080a060e030d06030321110f09 67
    0x30107002040c585818500a41089210b8001c0b182080c014018091145142d1070b00d0444058603011050352a190a01c200c10910b0608140140d1103081a021404041c0d110032018007a110a808944042c0c1705c54007864014003e00b50200e443e401d0080d50700c2c00344409009070085040f03000e1700703960303d25200d2802154254400d80183c4402c2c1e1058007444405a410011007190100340c203401c13204140e8501c889588003088012006001d00c1d03045040f4195030351542103408070b0b46004c00070010b20751245600c002004091140318842c071210705213900340c40040b015420031f84003480c0240144460401e010381d070150503c4802134212090120100c3d00000e0750075918007030901c6480e01c0ba00c4e443c103000b00914010380416883c205904200040004e00360005442075050342c40380d0003042e00b019158500c1d1860042900042015041c036000005068101c205008036a0482c880780300c202884000010a17100711129500b5000c07420094004180c2d11400230b8000000010130b901c100700c00d44001d4514030368 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 882485350 1250 882484100 882484147
    0x20f03010b0a02060108010b09150f120d090906050312181908010b0409031b03020f10020301150305061e0616060c02010c0206091002031e070306090b0316051005 71
    0xe01c0080ca040010b501044070a0041000100030320202c400380002c10400e81b0064001202114000c1c8440200d40e50300d4109108140090003001c45d5507080038800b55920310710810400455100c48020400741c1c068000c00e029104050002d000d80a01d000041440390300c20040c0c444440b40c59150745ca07a5982d0100480c810714a20042c1c480400c1c2000313129421207804103a0a0700c038a1034441002c0010b50032a4603198000d42190349484a400141420f80c00e001e01c0c442d00c100507000c3c91502c048401d440b07070b0140d4140d0300b0310030115650358044034095048501c05d440039030b40580324400907110300c0c0920442c400e50b002d015000d40d043c40382d502101400080307007410448519072184030400e4255824031421180203007500c010030503828030703100c261303142c1e030f0f03052071041030309400100041407aa40d52009800b102d032000540c58036032410400c0280200203a000d10034207e4200103075215149170015003d40306c2c2c0203a800a101d05c078680307030030803000005041040782444030038840448085240c03a481011071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 882486600 1250 882485350 882485369
    0x41a130c08030d0501140a060f110f0a23070909020a090903030f180201120b010c050f060126030a0c11040c0c06110307020a2a180b090c0a12020f0301 66
    0x210703d021607140c02d65005030040105141c0c071202480c00f0703642d400c00c901c0854410f4202172401144208040b00c0c018200500c41ca070034881c6188040b0410380014600038660301995001d00c800da0301c41d0b05003048403198482e040d00c5038001c11043c40109550381c4407440852000b05a104095580d207201c005941f4042d80036400309030f50750703541e000c220498004c010b44803940c21010300518071036600182868400d444440002590740c03024a6003a4095240e001906810000701c90071003c0c007000d42030769140c0034050203448020421760b4504210880c40300c4c1d6180311070040514100102800200d03640a0340f00740507200c0003014640340003151180c0c841d03018030700400e9a03107886014080c00c1260940d81c80b10205400c4503420410401003d41c0498400142d607131100c600700080c0c2c5010341d40d060b5030702400140103950b480c481d00004d80d002c002c030300b81241c0c4408071390074040d0600c1c41741080b011600880e1202d100410800c00310040900c22080403042481e0900010309000803007002c081150400d81040810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 882487850 1250 882486600 882486607
    0x103032a151d0709021b1f11160b0405013b032d0705010c0c050c0d02090a0903020f10140a050c1b030d0e07170303041a130c0803 57
    0x841c014090080148140880000e422141a41080c1d07a1041403142d80744c00f170f40c04103a050b8540381d9940f454851183c205e084400d031064001c500c1e444110210b10742e282c0c040c0360420501c0200019029541c00440b090783c5440c103186c41e6150310070504c5008004403015503170388820300d10942d01221440e141740d45c2c210503841d01807601d074440301501c15044412002c6500901c040c00c1c0444d8015041076147c0b04100b10b14460080381045080075010305140101254202002400c5240d8000c2c2d80d045482e000f242100c02c000c00301c005120300b0402044d80690070400950004807512050b0304030380d0f400c82c82071045807000d010102c0240d00f8140640c20603c14a500c0d402c847c40741c00758198406401010f9003100300203d08001031402072511490704807020148100105862030441801550b400034074040041c007000ca04010302c19100d00d03290049200300340e200301d02000000000070559108540c0410b564a100e544a001014010401800800d42080240c400400100440600307401044441d0040d40c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 882489100 1250 882487850 882487883
    0xf08071206020c2a1f110a0b010303020a11061801140409140a06060906050715060312080a1a090609090a210201110c030901080402062203050c030d080103032a 70
    0x3529000b2020a01c20201e9207508407500985c51620100409581000302240700a20241410582224001ba0030001090000003e1503000318460710454454280c0c955003400b501c04000040c0140c02002e07076441a11105030195500403a03100008140d0304001c681425510030f10381041da21800380580004075500144507102c40b01d401228050090350030038040d0b060501800509a00825074094502208161000414030703096000758013843d08880c08050090985d03001030300800d8166005013140e468401524243d03100402d051032032000040540100d902e0300800c111041c240a484c3e201d150140030070500004214164407840130034451040601c2d150030380006030031101480140d006407201008450041800401280c60744138007400d010209844600201d072031405484e115140c401001c500096000e6903486402e000c9a11500480d00d1a1408c40141500c07038401500701c0002c103040c0801800020302905015142c2600d4480c00058000300701c681442084100b0019500304048405684 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 882490350 1250 882489100 882489163
    0x50703050606060405031513120201020a020c06090d020103021b24010603050c0a050d0605030106060302180a14090a090501020315100e210703080703030b03070f08071206020c 77
    0x107038810022035195003403901e005d0109450301d240448031075040300300c0000200d03c40c903001145542c054001126007801007084801a000f90b0042441001600c1031442c260200d1405000b01c8646001c0544070200181a941c0154042d40040c1c1442908002024051000c92800c00141c450300518100080103040d05d0003c03150a0f100c1a0020004c140c100020041510f09140480744444200d1410680daa4a1080e4000c000c3c071241d00240d43c0365007803400001c1c0e03080e8180c000d81001c4842c620441003007440b0310104070a0403018400e100c43d000d48038100b00031310b10300219a1a408032542c000070a018001ea030350030342241e0040360341c082001d00c1c050700f1a80d60b080c0200c0c0c0003441c82050811008540a010003d40c03283c0f810100d40c01c10407207420b000038543c04203011074801554006005500c6002c80c1c0703005000381c1448608940640704250000038848920a0b02070112074030355016081850038000e40202102d01c000d8260303111a001c1140b4400d0080802114030004c608804544c2184207450402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 882491600 1250 882490350 882490363
    0x30f0a05090a0806010605071203290a061713030c170d060501021f0b1503090f120a0c0609061d07081c0504090504021c03051c0207050a062705070305 66
    0x3c0e04154400001408201c0e0007000710355030503421029140703507405044800c80281c0010b81440b40004003203000b01902c1c6c1c40e2039030b60031480704040b04d848810a480d401b04840c171000052040c400402c0d00b00c081402c0d01c8940001c0103149000e46460b0144032240e449400c1c8286951100c0740c07900400040302c40c200301c01881180c01070942403000e4643c145020941e501e03080081030080502075500d00c640301d166940e4260070fa4500301c40d074451640b00d250090f0420b8a411081480800c1360180c11031145041882104a131504192a00c4a00c13646d45251140001402040b0048072599641c50540d03502c2c40c1110251a03047d0b060705d00802415007409902d03400c0c441c0f111840c2081d0b060f0034244250781e035004003c1d20300f030340e2040c40005107031341c0c0e00e00002c3c1e030f44801e8209072040d4680b061256410700da0f000000308440003c44044103a540c03040e842440484c4100800913049402c8801c2140009010350172101208c03010b40b81031101c0348691108030000c000c2c403810032a0f4070360060004200b0094188200c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 882492850 1250 882491600 882491609
    0x40b09070e130c0605070803040219050a03050309120609070e07020c0a030f05010f0203270c0d150608120a0f12061715090303130f080d0e060f0c0a05070203030f0a05090a 75
    0x9040c03246d2070350351040c40d000241000f80306a191003000c070100310700348a00000a2100801040d0a00d68900b4456240da001c008146e002d1001c101040054800c0000d00c02d0280e0400c45c02842c46a18100100042e40c0016041c4070850080303c0180d00c00d0341d00c100481000e103025429981c40d003280362410500319040a2000c84200d40148100000070710400b59034040d0407207051421a0410581d1261800c2811103203481f5031200310810050103018076280c1440c481c0100803000c0007110b03217407004140d841800001d5040c0c2c0a42c10080000650f02c80d840c2c1c861003031000d003440c0012100c500e0118003510324a810407a5036012507040c13107580f04810020210a01c044134141c903503030300340a81820b440b440014102d1701441c1c6104000400c00c0900c0100201464200e0035941d1500c41000048006c1c100d00031321900c1c40d10400c00400c0342d0b0180d070042140a01c00c0f09407000d19010031b00320191040d40241d00c040c0d03458082484442030740810840240502c0080da5940d640d20200c0c01c04000400125401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 882494100 1250 882492850 882492857
    0xa110105070509060a12060306050412030501080a020d020f0a0b1c0908090f0310020309060114040c02250b040f081e0303040204020d110a0807110d08040b09070e130c06 74
    0xd0000c0160000d00b00d07038103e501075601e29135659540c0c80c03c2d40c1c00201c804062001901c0c0003800030610245a000724000ca1050712180c44503c03e0b85000c4065603000c0c0143c01050304541d406400504e02480700d405802d10140c016201c1001c1800003882d144102d0b40004860f0000003002460640e0484c0781000c00000e4410070000b03410181c0b00d610960184148031070143c56500b03035885042d6010001100288100b583c20340d52880c0c05207a40d61143c60a1041104a9030610701039400e1746000d004000140d10640d00038900100c0c4d41440341c4071400b5100740d400c5038010300400450307103000180042014007001c0b2203402d512480e041d4a140382450240200704100f1900410703800342c3c1303004000c4070340282d0102d5000d600ca40f4614901d100a1210741e000042e28840000c10142c0990001d5140b8403c21041d203c105080d01500c451649031802c12125400180520380020000340a001416030082603050440d6201d03900e407040c880c1d003070009841150103600c4000f1040c0400c9020004280600745614 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 882495350 1250 882494100 882494111
    0x71b05030a0b0c2d090a09020a05030f064b0303041707050d11040609152d08071a040e010501121415011407031b0f0c03080a1101 57
    0x8a8280103600060303c1540410300005050707104c461442d48002c09800c807010110340d204814120032000b84d1184401e0703402803c81c40c200003010f0b40e0303a1007510740c0403500b42c071030740d1a595800107400032882008089070f0f0300c110ba01040040340502546180c4002d8400d4410340c518160b0141d803024100102a510244440916088885034070301100fa501152403602c505440d14500403031581c10720803290030480e0071105108160081c1701c211a043c049048060300c08004072a1182c4111040c3c0310740c4489098078048001d020032002c0d4543e00710020002440f804100b00c104088040e001e17151445d44440125804484280500b14221455040c2a00500d9006240514140080c8040e100511071103050152240c0c010300010a990814112005217040009892400724050424005440c406500250080c074840100b0395011046a26258140d102d040301402c203035582440b900030001c1c0c221460720040403000001210b4817030b040055486404503d440300305100005002d6100c07441f605071141e0509 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 882496600 1250 882495350 882495353
    0x21c14060f060a03090209040b15010c0c0b0d0605060301030506040302070b03100e1305060415060609082509110d05070c0c03140a050f030403030306080f06011202120102071b05030a 80
    0x403014400c0800c1c098400c42c1d25044026010740c010681c2190107504503075180308000c10400007010062040d0384003064a69401d01d00340c01110300700540c040c0107002440018060040344000005800181104000070032000d440d400401e81c02e0b0401e9100311072951040c400e00040680521210004c0e02c0700702445800d5140c9032000045020480c0304604644240c480418010b150680b00100c0c413640050403104d25090501e01220800c0a01080c061454601080400c8642c810340060f01103900c001d000b007081445569400340000780310000940082c0c1c580b180002c0741d00441c001c010244191101315600e40c208010103005817040202040e00b040a1600e4000000b605426110103607034010b00130420710701000c25214504040d43c2000341c02d030302c64881d200c00200000001001980d100e039406100c265521601141e43d00c0040001d01150703040000140b120010010003412068001028207500480c1510030a0882e40401c0d800d49040042540070640f5910742c04200000b4403054008081c07400380d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 882497850 1250 882496600 882496609
    0x90b0c0307080a0203040c0302120a0c050d150507110f0a02041107050a1416091e0e030a030c0512011e170a080c150702030c060705030708060f011101021c1406 70
    0xf80341d280da456012010a0501c80041206000b955010b03042a880706c0b8042c03d00f0340d0700d0071609411245000b0f0003d0102c0c0f10b0421481c01c001056002d404140c000c0264a60321000d080000e0071581002001070700076005030790802c08210444007000c081c1c1030b1074040e4010701c81030b500c80d0020080540800c0117000b000440c0003d00f54849500700301040d2401da445c0240d10b080c00040c448020040c2001c44010402c0485a8000e40c080c00d40914660784041900c0108070903a80300b40302200194105200e403421490080d04200345080b0a40f510314a400c0c04290350007540e02080c0c20081510b90460702450420280f06203000140c1104000702508818103400c5a507a07201a00000700141da010540403514036040000361090000e406407022549040da0b0001d42e03a4100e101450701e0391050101040c2c41038081c108a03400b9090725500ca0030700c1d540d480300b0b020b018100300d1402c604200788072000c0c074040340c070a00c0548030242208004007000091054840c042d80c4030740c041c4255001810042c0100d035943e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 882499100 1250 882497850 882497867
    0x7080c071208070e1201140121021e0402030c040501081503030307030207140d0f12020901080105221a030705040605060a0c260316080402010807080a020c070306090b0c0307 76
    0x346442d080c0702542d20b902d0200d03120102d100d41c0540042800599426140064200c1540c0c0d01862203883c005aaa40e132030903002100c19629025440c421041a10250070034010240142280d196450b1800150707002040803a40100d400d610342e080b010900340603c0d03a102440341d8200d44074851801040d0b400c003000035181d201c050500400d059002034100b003001760320725801c09140004e10079681c0aa00c090800740c0500c070b110090700d001036060031000e10b0407401e40c0300b034a401d40c1e4184d480c90a96800c04042c0b009000303a410407800444500107070080c0d14002801001c01459800300364800454141041c98604030705134110034851800c0520501c056281c000540d01008403a1500701e10310411414500c10103195400d4034070828440c03190550181a100b0011401060030042c4c0c0f41541880140445180e030003501c0090014084c40d020801a92191980a4122600080c010719041440d034807507245c03511962007109c031036488030800310901a00303c070400c2d8000e102d41d000f40d10303518022200400155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 882500350 1250 882499100 882499133
    0xa02071508072109050102040b1e0c03090d021c14070501031a0405130f0506070e0d11093c0c03060d170d0915050106050c0a0809030a0b010e07080c07 66
    0xc1c821042044980070340c002419164110b0000c6660319150349c0d810302c0030380c80701046003060040048814043d400e04411510858804005075080964200401800791105801a81c1c0b01c031921011688040c0c001f400140010b1240d0310141c2c1c51003d89030040d00304400c070340c4080d0506160600f8514003c206039503a4002201c100c03000102039550140040c0050f9448c0c0300a4126100d4454100030480006a01c1d4040c600307a4070f40314858840308081000880d09440000c060030b20014040c41a8288440c51640000000e0343c4121190000442c20000c10f441387d05201c1e00e110380302c2400052512001d102c40d041240640c28a25500d04803000c01c0c0d210000a00c005d120001d0150344480c9030030340500f074803005132000740280403904850501c50407101110300342c141001e187c000001441402102102d250000d2134019100f10040c1c0e0b01c442c030140d00104d20b11a0140100b090340d038001455100114080c20001100940605000d080181041e2004100b082e85100402501c0c02140d8200300000001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 882501600 1250 882500350 882500387
    0x20f0f0d1a1c060915090c0e010f06090315061e050f0319140a0c06030606121a01050f04050406080105070f020a05060f220c050f0f0d1e05030a0207150807 68
    0x1011399181601c001d00c11079102210081c82c00c2c01e80420011000d41c0d000844500f0240c1c00560390300c03494450003416442c4a100081055000300f00000742d0400300004024080e080e00049042d0f442c10101e011000e072007074655020741c000205200750300d00280c150a0400c3c00350700400320241c541406408004c2c1c41c203005008502c82d01075151824004000410304140e00c90199103145503680130140c00381c04640030302004540b480c09402800506480f032080c0100c0350301064a14400b00000648080d409a005810301c840c0400010690303807103a014460041c05640000035451501d142d00400d1040118015030440d04206241408070314005510758002030103490f00380b6503480321013413040800041c441020b10308100000b04414003061031000c3c03084500c00e03119450390030b0a001c20406900e0402048980c4100024201c8012448104500039071034003008059200c0c1c10b6039290b281c550f800c4170b015100141d0258800740a4900780c50516000600ea900307081105060012000d405403180c0080c40811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 882502850 1250 882501600 882501611
    0x605060307210e010504150e1b12250e10060807030f0e0c010908071809050703150b041a090604090c0b0d0e0c030f030d020f0f0d1a1c06 60
    0x2003a101e1090b00c010340180d80d42c100461110307008401c1c0039080c100c509a54000c1c0104180342c0c0b540450044000040090002d4030610001c01d401e003e96415500d5010b800c6428803080c1d8182800070490710101d49178250100c1c41c1400704841e5804104a1504002c4403004140180a0b40746041c60140042e10394034140480c4956030302904034000c01881110a480ca401e001110070320610103d00d019138030000703a0303030001782701d48411995a803030400b07204404203000300e08035a1514103059441000c903d880351081e10002607aa4803101d080d8100c3c22804880e00740e0320714841d2028940342c46846001920106000410408007002500c400c1c0300400d034074021a00d60503a1410130919512490280001041190701c2d141c2c0800c0540092411502c0002c047c8551881241c41c1d180000722664880c1c2803100551400d00504580307400b94009076091006904103202e2018001950070191514400d4440001091011101c000d9030640c0c024601500840c0600c1c000c02c82200a03040308025185c0000012070f6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 882504100 1250 882502850 882502877
    0x30e0105090a06050c0114070e010c0510020a050307121104062d020a050609060c04032d03030209030c09070e100909090b1b04080307030f0516080d0f0605060307 71
    0x180303445030030a001e61203584240003040d40c2c0e4010018001c0240440000c0009031552000c1d07440c0c004003640c00300d02048421422005a40c8544a070f100c0c071a22500031740d0344d6801614800c40036604102c0d042d00108034044200a62507038030030020340c0c011181c064180419174014450020320300c00d5000e00810046a4062001c20280d906c2600343c2043c0c100c081c511503c1c200c0080291a0004002c00300c4031401280045101e0803400a0075038000c21000c0101841c19256940300070142c503d840440c1e50061521200000846060f25071b41c040c41e019450141c0d0790919142010308050160070740070321600c0524203004005034040100010500c2c203603020072074452079200544070408a0341c001311805d414000c0450803c9000d0304002e004140c1c51905205821650742401c800d40503038081c0301010751061241c040401e106400340140c4601ca81000c52504901217107011081d4000c0e5001d0b1181d590000b03480f00c220b83c051003644c0d20039800100400455042800003416072001030704803000c01202c1c414401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 882505350 1250 882504100 882504107
    0x312050a1107031203060e040c0501031e06120b010e0f06060c160306021b07080a020d030915031a0604030503072006070b010e0705121f0801020a0203040f060e010903030e01 76
    0x1a6081ca25802c81c1c4a55503203151015a42007900c52420000341442030000d290300541082074001c80d80301415041607030520004600070040281084240b120f04500200e0000da00e00c2120040d04401e00000f020a849041c880111881070348130618000d13402c010441d1204d0a9820310f90420700c112510ba83e1900070030203140c80c2c0396144000c400c404101c110b002007042210f500600c801e01c12840c1491060303180307900c0301f034440200e48110b0003540c00c69030580740141382844c01007280340d1183c1445008030f51907550b60015080207044003004290303a0b00c0c1c59245901c1d8801505e07084001107078039900e4103055a5425880340280305004042554080c1e046640d211f0910b541e82c00403402030b08084e00c404450070324540a01c002c1c42001c190003450404594000d105504a504005910298504686a07081c40070180c4607950000f1544003030303950001c160310030f0038001421454420740c011a2a28280300d00d00c0100c40c1c850f4801802c2c000d400805004990300a1602c0c81180d40505113401105020f40c01079 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 882506600 1250 882505350 882505367
    0xa050a03050f13150e07090213060206062202040b030c0d0e0c06040612060e04080a0e030106210224280801030b0c04030510140f04082502030604120809070312050a 72
    0x24840c0c2d0003216000f08003003040c0c0c0d0250402009c0751000c080600e82c0c03240b00baa02d54105a420a400c0f000c1d8000d40c5002141100d00c0e0f1240e520a2200145015913842141840b0b40007596850742a0100084440c50644103004407800300341e00c0000340c402d21b1785520008245100714070a45080c0550710101c10040300132940504010002035000d80c815103050724001419900036990000400c0c00d1582100e001d040500c510300c03d17254081c0c2c400c003041c900c200c1e4144a450423040c04030b90011a07128080c48074888540c0ca0940c8000304070001e5155040b07800c1e0000702aa01c01c040d554031200c60519846070b1036102c1103140c116030300100030980c0c9465111651441d4801d03600007a2961050198a400358031855010420781e0a5900b0100c07480d4903803059821140b9402c2c0c40c050f2020005004401d41c800071942902404640748076000c81000f81540400d00305801102c05640b4652842c14008507140c201003015441000c1034050329031b29045540e06071050300e8205113141007100220303040200c20b0281901 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 882507850 1250 882506600 882506621
    0x41a07060f0b132f0c1606020d05160501090803060312030615090127090c0221030702010b041407140307051e07060e0c01030b0f011209060605060a050a03050f1315 72
    0x313014881074a145070f035100c1d40441d418071114420610076031003120540401c5001c1d608039038041c00f405003803408100c4017030304440855078154a002066200140d0700b44140c6840b94420440c0c640c0300c0c5002c004140c14411800440e82103248200100000d9985042c000e031010076100d18095150f201c6500121080d0300b1602240520400c0c52819244c85c105c5009a0402c813039030408240880448504101d8071130884400100484040840381d048d03032242d40001d107074042400d04c00002c040e40b64800060030b42c2c4200801d201001175420078041d00c0c9038414214505602c022007018070b503041c0004000d1662080c00d110b4010558403130480c140881c810411298060340040003440100888080d42c0d440d03644002c80d42e800b0070701d4945500150b0610200314000c0c120142c66051410030741508803c00f81044400496440355500e001180956a040c05448007030515503926465041003c2c014003154806003255821040060030001c413a5030001a51510541c03001c0101403070720300913100c440a00002c3c002c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 882509100 1250 882507850 882507911
    0x604050705030a0c0329180706090302010203120405011b09030c0b0a090b091305181b10081f0602060a11160227012c07090b0f041a07060f0b13 63
    0x10704c144811902a47c51000200c00700ba43c0b01c0507940c00e0305542e009405d200c0240540c00501009011058011078507910501600020810039404911034400c564840150404591450028000e114801040d0340103070184c1c554680c6840205c1c40083c107087c0207807203460703070321800000e0702d00d15a03c414807100d15081c0e4101041c062810042c102031642451500c00701500d10031310382c14141d00c00ba843e00d21140c0d202c0c003030082074942e14130100840f030700301c801842c0340b00c0348021400c00f0409031011034a80000301003541c0540030304c1c00c1c0403287d1000c0d13032146100300f24141c9082c04600381607800c0c195005001c944c1100e004001e5107240e00002d04000e8042e038100305001079600005080142038981d8003210300a510103140040c0390b8410101e4080040d54003800040b5851410310020400600070300100e880085200c2c02c1039074554081c2c00c0082c030519841a40c0c040401e0080400c8824042c07103605044009060102e405c136a4081810502c1d035501c000847c43c0c881d102c8c460303504840c1c45031040e82c055001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 882510350 1250 882509100 882509183
    0x21e010b031207061b0e100e090108060f0a0501060905010309020d14060106120509031206210706110a1511090904080a18120f170c0604050705030a0c03 67
    0x801011603600024000d88541d4200f0590f04030300c170600c0204c0c0f0850a444c1e21901c00b005520414020354182e1003e08809001c22605030170003aa035070244003802099250010002d51500d40c2840d54145000740031452800d0801c401404029081000f01c001c0c2c681c00e1800045142090002580740f03040540f01600700541c0c041080749028010840341d040e5106515100c00f180c0c8060801011650200d03141001d5030018000d2419a80880710742a0300b040005103d1a2481040b1a0300034070500c103615243c04a5101c480104115900034501402303454182c0045d0007984019200c400000803100d1500c92030507510904182034001e84000c2e58082040a00100b4841c0352501e800043d5920201c441c01c041050404000c100507907203032084007610b5488600c0d61000002d0f503510000c1441c09141180e108284803000c0c1c58007121013015040010414004154504141c10000e0520f00e0642060340a500440040c07800b1407112019101100d500022030020303602c0c0c01c5000322107916000c048811400106 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 882511600 1250 882510350 882510373
    0x302090c0d091505060303070305030a0209031c050a021615030507020f01141b03060d030e060904020706050624161403030115110109020d02061c110d110901021e010b03 74
    0x1018520002030750f88600b001183c0702d5004040e0740f03002c2d0320382c0200050010400a00144050f4000c2d1800c4040601182e151014804e510188545000c0e0340308002140440c0c004805039041101034010150006800d2089041a0b000300c41001c0c02c80280c0189501c03070300400c11480c1700b01b0002c240f000100300200f187c103035802c2011110b80c0055036a10411141200030842001440e41106e010b080c0041440880c2201c41c1c0d81075481c0705a90b418954013060500c01c2c00901c3e141d6000401a030340c861307000020580750400c01c2210b11800800780d0020010642141a03944494400722070003416070020314070b020151885c25a43d1031184500c00000c5000c00700c000244c1840911840e020020b461b00e0380b8000b0015818031900b20303000444081d41c040310340b50000026041c104001d03d90080e407000c031116408042c0c4010810b40e09101e5944096410024040000001e0391051044692a51b05501d10385200c4000007961a00f03011000070540f0150104546c501c01c095110703800140024007598072070300e001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 882512850 1250 882511600 882511613
    0x1214061f0c02091006030609050c040335040905150f01140912150705070c06050a0c02151b0a02100e0111010c091401110a0b060d0b0406051e100302090c0d09 69
    0x291207505c001c00d003040c0c0003240e0381e00e150169511428807110b4030760400c0d1964a410f40051004125004a0400307000c02c1a003299039803600141148100080300d59079450500c52408651000301003450003201008401d2250750341000401e080c031408d180028041e4100340d1003420504c03421001c1784d40000124120038540001160106110440d200344d0b0380f041d52052001d40d907600c15110000d0003100c05910910610380100701a10030307075415242c0301420441603804100c1d005d2107104810700060001c00c200828282c001a400310910884007c1c1c0901ca4882d070203d00440890f14801c4140020010441081d0344038480b5003458081c600000d00100b01004405403002242e400b94154254800c2200d071400c1d40107e00c0552a058407000408150006865681c2510b40180600350301c244442200e4000c1016051682e002e00d005010000c1e242c00d144840300083e43d101201003485842d0401000300c449062000704045035015030b503465003980c0c4ea00c1c848001e44175040c83c14000501d030180d43d2044c80381 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 882514100 1250 882512850 882512881
    0x1b1809020d330f4e1e080f0705030705030711100f02030d0c030f06090f0506030609060a0e21070201020607052d0405060a1214061f0c0209 61
    0x1c1c907000c1c0c007150a450b10301c3e001c0c80200c1d6010315007030030310104050041c00d082c490816003e81c00710798880c00f4040301401c596811140c0d200246180d0320050701c1100078002400c0032039201d1410740c0d85034080c68aa42d0b0780d91855014420b03500700402000b16154092103401d004a030b0750581e0010580b41e82c0c50b618a400507246542a0405000351841c03003026081502070791020b0404035454009600388012207074660042c4c031011030580708050b100d01c0b201c1030380b00050003044003911045601084a1815010040840b0b4006054a01c40e6004105001560700f01103415504010003510104440c90030710000c45c50b00e40a841d04182d07502d0310142c001c8501c0002d03000b806046100340e09030350407902d410383c0c101c60b5805508042512a0f4110b0704080c00c50680440000541c41080c0381642003940c0c400000b0410740008485e04045446419002481101c5100b035464120440c80401c4903130415a004c0754860011440e002c1d084071121901c0e180c518080c02d088148198010301141d030300e140c090a450500c94 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 882515350 1250 882514100 882514181
    0x13170d0908030a0f02090a090b0a031b0501020609030a0503010b0322030302040302130504020f0d05010e030301120210030e03040e0a02120106111506032508010e011b1809020d 77
    0xc0c68011091035500c8075001b2550f580000030700d801451414045214018240c02d000685c3c00b5042000000c0043d000c070b6406090f1103070889980842c4e51921002a00b8041c000b0045556504100001d9602c2c40d00314003a0b03415252611941138490341d44c03055000d10341024620541494446c1e00d9140d042590580080054a00c02c0e2186c02081c403c1110710303002d5400540b0000e50003d100c0c25a22200e003413580d001c1c42c0440c0600000301c0c4080c40340d2a00ca00f076070320a030003060342c030343c400014a025410f0032010904940310368a030820112040144a6480b400340f0300038040010114030114408103210b4050318032010380340c0800310a55a40340c0c0050042820810100228001d130000720121450b9004250720403003000c0d0141103200080c00d151440c1194041082403070600e200b0b00824154402d1240000d408511070000450311a410b04200c0c0848880700003104018040600346184491164480100c84200201613100c20848841d50040c0510381241d043e546c062002d0144203000e080141031090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 882516600 1250 882515350 882515371
    0x140a060f090627030503070e0603010312020d02031206010806010c0209130615060e1306081c140a1d010e03011802152a011b0810050913170d090803 65
    0x3e0312159085031a164122020078040c0c1580425200441c0c004d034015540824103286c10040b2a40e603000007060b9400a81007580c3c100c54000d018215141c0400002d02044ca90340002d509000c0c14000007601944002d00076410095698042110341c1d001c0c00d000030400350300800c020650314141d00b010501c400c4001065865034246900c41d0840b00d4092510001c1e5003481e42d441d00c85020036000c1c0000d4460b040212884680e03240c400040d000801d00040c2c21060070841202c141030304150b0b000348042040b8041c9a034002c0100311005016030080d2000c482564140b100710140300d00d00340146c0d108403040c62490b8055092155021011204d203810300c2c415807007118801d540403102003d50866028401c001c80c1c2c2d40304080c2d8801114030f40304005005080f031032000458031207481c003840308808080551000c0070234071400900074a0758115034074401414080c0c0d1035001c03038945080c01c0b585003407481c0d80141903245805080042840904101c84869140820510000c0020328205031164012200ca9580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 882517850 1250 882516600 882516611
    0x121a04081903060f090b0f040615020c0f092806060507021e06120c04050a09020a110615010f03061a0408070f030f0b0a0b210c01050313140a060f0906 66
    0x450003441030f64241c0303580251040c50320781000c01903402050980c05c12540094407400d40e0441c1e950310f0050401130003d4155400c03141c0c003020030107440e24210f0b20b03480b0b04c956941c003000c42c04c5460b50550140e00402d07410068110035040c1c0b03160402c40018140701c9024604080c0042401d80c0c10070002d0401e10302c243e849106504a20340b80032011860b0284496100b6810841d640c100f054030720026070044921446140341540d11030001705a80c0d032960010108980200e030500b0000d401a5031034006041d0303071001d801c0c50300d404600141e00041d40c80b08941800040c3c603002c02018429400340d0050107070700004004d0003903070860446681d082031280c2061440b400b0008901420406604002c81360b22101d18140d04405648a00200c4070040c00c03c0070080c0e03900c4840180e0754400440720424229204029031910b0420b41307942c00d25000b070301002c0c18000100140b0040d4109204c1c007001e401d412088424080c1c01c04021107081001c1d40ba00604000e040030b441c08138280441e03010780019032080c9403c224 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 882519100 1250 882517850 882517897
    0xa03061b030608060c09030f0d03060317090306040215130b03060a06050a0207090b1c060522020609040f090203060a060915081b010e0a0816140901121a0408 69
    0x907030380a0701038035070507130041c0c00441c0003145080040c0c0300f0800001c040c0d881c000700c04400d0318605014500c010000949805040091096a200310b01d9240440c10302503103800d0400021076554800030348001d01680c07080100f1540c1c134411038181c40c0c00004c800710404a0310b603500c0e00c11038160000e450b0b41e403044511880006030b0502400881e841039190380c004c0c0ac1e41504d0000c01400400c9200341081d0000c039400300d040c030000c00079590740d4462072044030b00040c24101a0903d24402040c44820117205444405040240c0d844d04151001c51a04070b80c041146e10071801c100d80948502c910080d0548035020500100d03000513003001050fa001134138200070a491a555164a00300f42c0d02c2041e1168001100403c483c410304a1107665482c0181002e484c44450400440c0c00c0140c42d920400c556005400c481550500699080c0010482061503072100c0005400041d050541841034194100b590f8101c1d004008004421800c059944100000c107840d00341800c6606500c003104003200c200c010040f0300d070f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 882520350 1250 882519100 882519107
    0x391e21060509011203140c030a23040b0c0a081204050d2109050c15120a02030c0f2508120610140a0201020c03040902120a0603150203040f020a03061b 66
    0x80c00c0740c4004000045a9103409441c04410084a5080d03041040c50040d5180102c4070300300800044c0c11101c01180e899002c100c000b880748a244140b5075001d114160313000303940b0320b082c4103483c20b40d4003614500e655449201c00c1180b1348070070b00300024114a030118883d44d0010781d00f10603510540c014801d40e900c40078910002c5904070f0104500800500700c8a00503100f2480c2d5034030000b40c2038400d81c01c0390403258003a4005203502c000565a0701308a0800110040308078a5248195002001c582081d41541481c214504007801111003910703a40d60080340d43c00c8c81c88001d0306144d10300b03554028450006e01d11818196819800240251180b00320400030030700601700384031304d250f03030311201d40d20f00c1c145940c1c41e0f600d88001e03030080d081c200c01c40d0340a0000008903041400200001c0514100069807039100402c6c0d048035000007040c19524a01e4024100080b640400d4501610204483c0050340c0e550741d49402d844a42901c032019401102109000c000c2103403651040044900c011022078924144c40e0044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 882521600 1250 882520350 882520361
    0x408010501090c120b1c0f06060305100f060e040f1a04151d0c041821110703051b01030204030819030513030203190203070b0c0d391e21 60
    0x2030f600001c0b6800c8000741b0744006901e060301c940c82400b041608056a40300c180c141d0700d03583c00556094214515012403860140304010075200141c400b0b1041c20b00c0c1c580c08113481d5400030b1001d07014100101e030200130480134004148091801000040f000d00340341c100800d06517541e00c501100640340201c0c1d044182d0701e021007503180710008401040c15469240901002d0140010700d614020343c80b451060000f207020000a040c409401540d03a501070f1400002442c0d1408004030140b19001041c0a10200346e01041c07004c0055100311800d0010301e034031401280207101d00d40c0054800440407079030413910400e484140d1951f60361a58144403a4407402c4454175940d1352641c00034056802082155001d02c001d2022000c040d200340107582c102005071b25030b0074801c00c1c100d0302c112031103200082c0d860081c000d40c491032100c9601401e80081f07025655404c0148800320400c1c0000100c3d240b44215105c500c00c5010034030039620003070010702500b1642c0e070180032615030001070440c0e0a0008180c180041d00381c0700d003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 882522850 1250 882521600 882521621
    0x23010c1101180924030f0609150c030509011b05040605130510050c0f071805040804051203071217010e091c030e060a0515090c070803010611150c090103020d020408010501090c12 78
    0x607005c0c00c00c55581c7c0ca5000307003800c0104681c00c80107010500c01c0c3c04080d00c1940c0d481c4803151000b007035a00c0c050040c107086aa00c40347c01c00342d82c1c1c16a9020070417903500006642c1600c80e5410490f9940d2144501070002c1212580a0350340203c4c40c0a080a1003a4010050304045030242c08881641342c0d50200380d42c50f103420f03025120000194420003e28405a0340045400c2802615441d10701621800810964103194008032904d0380300240c03001c2003006000c103c0f810a0302624000d41901c0340604150001d84040c8074803500724000b040810034103a0240031aa98070842c0701d0490058100002014001d4880f0803134000c41c1e40200070020350059124050b00b48161000e0081203003074150402000300c20712001d0020703c2d030010144403600004001c58000d5000e0141900d580c0c6000c080708580328542084282020308540100701413100c080305580c1564040c041c01d00300940c0718929207105200030b010719400301d882582004000206111181d0080e0802100d540e1011700c20382ca6011a101a01c2042c9403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 882524100 1250 882522850 882522863
    0x9100f021b012304081203011e1a18091f0f0b0f13030b040f20090609070c020402040306060e091603031d1923010c110118092403 57
    0x900300f0000c203610310308a020081c2801050304040d00c0c3d034401464a0340552120a60000020062040d5081504044081c0340c030359400d041c0845c1007c0300004030750190003400001c00c80124090b06030b0400501210b41c1c600c000340940c4418a001010901210040740912800048600000c82d0341503102c0c42610a0310640440545002d10982e0350101c568086512070202e10200e200110004042d480414003c0703000309162200814907041550040341484140d540b001407120f141a81602d039880c902c0e600c08011a181400e90351000303000e440140c4010030080d445440040c010040000341e61290064401c028000c105a80d07401c60bca907500c0c8ca0750f800c0301406040301402000000d1054440c46150410541300c000700e0b140010114460050381400303103415140d2410306002407002d03005011480005907245000034840540003812142003c18040c2400f003030741d4021005640604201030481034451403600c1c0242e500c445480040c820601c43d82040c06109501d54402c820f142441c0301030725000300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 882525350 1250 882524100 882524117
    0xc2805070b071103030a09050102070e0609130309171b1c06050c0f0703081b180108090a0516140618040e070b0c010c08090106080c060705010209100f021b01 69
    0x224907400ba081a24100d90720303648220f00280d0f6440c10b0001d4100040503449144041c1e06040001e800d005680d088101100c80c15403c10056941354815250083d00d080d000c050710061a00b411540c60285801000d018100c0c0707140564a100001035818440d01e0610580302c0403807811041104c40c000c801c407016040c5075130b00d04000c0441c8641d805036810141c0e11150916210126054002542244c43d054021501d45010002c10f03401ca030200c040380c1c0c440c1c044040e14110207070050342c0120890581c40f80c1005081346c0040d0162804001c0c41418603040b0048441c124803501d440004c85015008018107810301840a241505100d42a40c0004100001c00b1401985103000d100c02400c110850440a03c544c441c00034030503001000506025404d00000b08828021580c098501d04015100705190b03131400c2d40c1000760f040d0108100d04600740031030300c0c076586441c0c40c103100d0701a0141c7c40701d0759400b90b004400d50458940000801045400079000d44509840c280401c0300900035480c0c4490200d5004d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 882526600 1250 882525350 882525359
    0x4020f010807030b0d060e060a06060504090b06090616030f02010c09060c080702040f050601030c090b030c130b03010b030f0901023103140109020a150e21030c280507 73
    0x141d00d4036500010342c3c900020214600b00002d0301c0e07200e4103c030603510301e540c0f90842c00320088140140c036440080c0e1482400074030320344440240144200c0c03050120281e9594204622030b0b640d00112226400014255510343d108080f168104d51090801280402c2188141c103801c0c42c0103000f0b0340940101911901c100d280f41200685d4601c001d050111200070003044444010303503440c418004520360213400020f2610308680058215240015403105201c40401c0400c25102000200c80d8040c4000d00c0007a00c40b410660300d07044145094000600c200404000480c070014148041c5215161100c0c81140d0380d12100704881c203e100b01401901d001086d80b00030385040318600304900d0040880182056420350702d883c0c00d40d6a11030307402004181d0b5115081c0900390318099844c0b0300903240416011120b404103002c05451400c25a82450150280903001580c03a104240e0410f001c28090044e01e964801000520b0b423109965582da48100300303104801480c07a4454210f5682d2194028028010b1ba82807 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 882527850 1250 882526600 882526607
    0x6080d120902040912030f0c0c02091906080d02030a030b060304020303030426070303150b0301210201050f03040318080c03070306020c0f011b030501080115030210180b130b0304020f01 81
    0x70110680c1c00c192980300000000b0000d4910400e007580980c0c0c0042c000010300080c2007a01c4400b802001001500c52944c0d002d40e036824903840d005070a0080901c800c0100d00f600e400541480c3d441400c2c18010080e48405007a0044020000e00000c0e5070200302e0001c61900300941e80c001074a004e034256000b0300004000078408140b0a004521501c98040003040400f403102050b4000e42040340083d4840f00a40484640c011140e40a0080c8040e104d00351f60510304046030044514249000c9d4801c050b051405590103a0100d131b041030420300c442e59403884c250502410a020440c000c184441034104005404900420b0784091940c00602900300180b85880380c0019400c002a4111a40500018410506024421042c040640d41120b55110207007041c041c00721a41688520201e03414680000540009040c15005403a4100e8070a1800c0c500705070102c42150002000e4580c00315001c40110b031071009540545034a4500c405c001442540301d4079840308502081c1c41c000d40203a1610802d644c150700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 882529100 1250 882527850 882527861
    0xa1d0303011d1603020703090b0f180d02030c0d0305090a1401110706080606130806090114220b0c07051b030c0102031801140f0319050105180f0703111c06080d12 71
    0x82c81c0c04511236450301c010b05070f00d5012149038100842c00060411905181004524000c14100c6100000306030a40200707032603088840000b44502c403040c40d0b8004060090b0184c558054015204804444d2501d0b51250308013031004006000c1054405c8105c400c2100150607400c0d40c0f25a624002d40751036203418000c2c1031300446101c3c1260740d007010020400e64810404a480346010b480085030f140031540350050300400c041c5c03a0701138142d2401803292084024000b0500c0c441e1b840800742c0a5551000c40c943d0850007508801411409511030b4410600346480b00c0d40c4449500320103841003082c0c1c8000699403881410302251400701303510307104000766008100084141d140302c00b185150000b2612042700c0c550040308c101c2d51400b04a0705400102400c2e00c10f06002d440c0a4070070800038403000050b0744081030001c00e00712402d03039203c000a51852107a000303014a200b0450a4948502100c0360030f541c544001c40c2040401850990b001a0140b030001d508500c503501034a50350200124020703004040c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 882530350 1250 882529100 882529103
    0x60509031905060103061d12030601210c14072001030207020a0803033c0414010606020a14010203060a060311090907031b1e0302030a1d0303011d16030207 68
    0x48040c201182000601852103251140c0c028010f21340c11864071200315104c4082d00c46c0000754407800e1040d1403600103055641008501440c039100e50302e00d401212a071b21104180c415001300c09211015003e00394101401d5800c658031084005000d0700c00d40c2030303d809141c0d00607051aa0792001052082e2803080c106c0310040c010300d0050315080c03407030b00441d44160280d4803446941e440081040b9644c030301c880725070143c07600c0824071016112020086685d1202184021040200030902040c10000b501401c0c0c130b6040c600b00b00902099a44e01c0c400394860708a07101c15610704141400001d0205018030850703114600040c842e84909043c100c08034014040580d00000c15101007201d03005942d142c0d40702e54400e4015541c0810511241c43c0380010b860300d03114070482400500c146d040070038400e60144496202c0a03240042e16542c800f880d520103021002d80c40008840c1480e203880640034080002c6059070750102c8005140701c0c086501d4002c2c9907045861090b641c07600309100282621a80003031011070b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 882531600 1250 882530350 882530353
    0x109111204171c200403060c030b040f02042c0708090304080610090c02071a09060d020f07020108010e010602060a1d0706180501170a1d0102070606030308090a030906050903 76
    0x42110300528880d903404416070350504000941c60040e00d00c06406003d0084100746007101d4140a8070391310040c14090b902008206644800900800522903401801c20250041060100d408000c4c45280294490301404042107440c1690b2542c4e9103403440d08a44814110b4012101507541000440b12001302414407040d9000c208000a200d0004000c514058040c074141010316614045500c03040314444415402550030200c0304022207520048228400e8040c0740c0c80541c0c9c0d07006400080d00b284941100002d00601c0445c2030300300000c0c0803000e0b0402c01c0c800c1c2c0740d0b4103240e43c88441070680e52800b407041000581c0000d00042e000ca07680d820000ca00d49500116020410501d80c5250a0001603003100c800a01c4008820030040b5020f604000144005c2c00c15000c41d4028010040444600900c02007099446040700d102d100d4803c1340401407200749100131510307080b0a142603c085d0050384029000074881c100498128a00841c4000382544d05444950800d85050001d4400b034000c4400c0b107030305 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 882532850 1250 882531600 882531623
    0xa1a1207020322051002150c030907120b2a0f0f040305060f0a0f0204060503400c06090e0a0c0e0612010306202b090b0f0109111204 58
    0x10740340001c2c044100d03401070440c406141d0500d424010a60000140082154040446407d9019000741141d8100011108050303581d03840c84151490710803035911419403900400c0121090081c0348100da4040c2d2a0360310105500c0e2410b10083d40d80309144400345012070810011710051010601c02040080c2c441c50030142425a00c1e00e8460a00c0002c403079441002d00e0880c100f080d82400c6114200c030b44600d1400840c203250400c04010203900000b4200c082d0f00300100000e01032001030444003d42d54410308040f0360061003043e94542c2e00e9241180031680d000705403002060181c003450303034001581c400c20400c42c1d050f515061a5400b0306000745c0394000740a083c04046400da1121802080d001030940c0000b080c5525510303024084034034144200580302c2a5141c130002c2e191140c2c08440740d008041216480110074401408000f911607a51024030518020150040080390040c0c00e03c00c080241c0e010201c1e0781d0b0f4940b03100a8924a01101600b5481080b1b40441c000303096440c0c981250084000144 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 882534100 1250 882532850 882532867
    0x806060f2205061c210504060e0f03010e010e0d090501020601060e012001290a15140d02191209080409090c15050301210803151f0306050a1a12070203 66
    0x104201c0141040d10305090035049101c805c0c100c040c05c001c00d490245040c030715003850184000c15954001e0000c5115811240360121190703000d4010b108215801c41c001c000c05c291182407e5640e40919011201040711070750700056070f40c0041541d0f8121000c80c0c4030b80003814080c4004403404c0364074100801e0910b154510202050b0001d02c0368889002c0007000030080c1d19240e09100d50402c0200617513500c6401d11500901880c620f1207400c1998a4490900328001090710045450038080d12122810b12480840c40404021080501900c050010f8545242003e032680c88181501c0340801d0103019031100308420062628075070f100204142c090f801c0d4045007902ca401003c041c001c012075040028001000500c01e543c0c07aa80d10b118031056540c80000c2148585c1c1e550020790000a000f15101c10307102c12111000c0d120300c071a000b200d000814089040008900015004182a014590181c00640c02c003089140410100c40140d90000c500e20341045c0d26400b01c2d0f070750b0401c000e02c11401c43c002440101c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 882535350 1250 882534100 882534139
    0x409021b010905061009050103050c0d3807080f04140f0106090203400c0b0c0d03050702030f0f0708040e010305211c050603030408070806060f220506 66
    0xc82c4544100c020b0705140c01e02100c42d0031161084c0d040314120f1458035004000103240010103408078101515030305210500d0f806c02160045488100c54800c070849102d010071250041c04951a03505000060007060b110100201c0724003008650010340445814081008103450340e010f0b200030b2080e442100c22804c01620b101d82540c030503600003001541c000c0300f400380300041300303110810281c0c425640c40c0010304030840505600d074901d01c0d0000e84c0440c480d031070410301c4040c81240024000d0030500c20740d038848102c1c0e2280d0390002d94070110006031900d8041481e9600c040b08451641d086c5003c0c1c0c900703003001a10b04003015444000c1c1200e6086c000c002c0041c0014401511900030340c01480600b840380c6007140e841748514400d06800e4800c410400424910604207032070820081c6669100050554401c004079186224640003203c15115117040010341200026615102e0882510b40c1e08102c0203400500c0035a507440c0046403010400c2100c0c0450101a96011607440240205030090024501c181c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 882536600 1250 882535350 882535361
    0x1218111306060302190e1005091c1a10080a022106011206051608160306030b09010608070803160311010b1c0501050601080f061314100303140f0409021b01 68
    0x40e011a8000c03500c40d40c50b03c050030b4000720312040342c02e2045038103140d000040c80031f40303a80007020280000416840900c1e1940c6148003c61034650224161b0007000d801c202040d12a2000c490101e5440030000074035500b007504401c0300300c403040c10040c044403c06e03508024425001d840d015001c041d1240c6000e404420422046000b04100f031204240300009051003015607000405c10b941d4081c098542061040e03101c0240c40d23001c50380c00d801c070400107514071003140074007940d80c00900a84410002e00c8203c0034103511800880c3c0c0d0240803541180c1c0e60b20381d00354076030203225418121182101b50b0803006c03034040c2c1c0c0e9021043d840c100c0005010540e010004003110b40807060039448440e2101c0400170840c003445101e420036005d0801e01c02501d001019402d10104c02801c4e05c0c09000f40c040c00c104079040c903804c154034003030401c1403040e40c41c80c044480f064504a24402980004c0030050020704100069080303414102031007004614140c00d12b5124000ba500840316107040d2141e000d9a0390305504203121300c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 882537850 1250 882536600 882536609
    0xa0302070f03110717030d09060f0f0b031e0d0807021603080d180c09181a0703110304080304061a0415050a3218010e01061218111306 59
    0x201c2030140e240e058018980710135504200f140c5c605440040390300100000a884e01604010008a0441c410740380003000703407030b041d583d41b11510705000d0f1040b100c0200740c00c0080040402d8040b60740c002000c40d590034030b142c4416175070704103500306100200321030b80b0980980e0740c0942580100c4102c07015401d0040c444d0b548680c4185c0d20b1038808181c00d1400e480e1401080c0c4100329510010031058120344480642c6131992181030001640c842c021079007203040218138040181c00102e001028240d207501d20403002422070783d25001900c4d040000c070070182d4a4065074003842e0010106800d641e1aa40d40320001c2034a05602c3e204c1660340c4c0316151080e6928051104126456072403c0300240ca84020302030140d84503001000315040c04055405110402800d04902c9a0012200001d1451003404250941105032125a6449007040045030481d80350f41042e048070681c0d41c40380480400b5110500854100b07040c44d0b42d00d6407440d1400c00218404034004d42c0c10a070000d10382080b1458400c010b800b103c030306910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 882539100 1250 882537850 882537857
    0x90c030a0b031c1d030d0f021e160e25020c0607060213053a0c0e04050d0309020a0302043321230319171b0f0a0302070f03 54
    0x80c00c01d40c180c3c00111181d542d0025035913942041804000280c440f070191800300e04008403640000d0205108101040e4643d554800300c0d041c041c40d0100d05e6443d882c0023a0b103039071804480d000000d46c00c81110103081c070640e4040c0040d20454818103003d055090300c0c0080d001144a41c0703403034149540d205802003d405105407070040c1e03200400003040040400d83d034003640c8182e004813240312003103e901168401c880880203601c1c0d0f40015009509240c03010b0240003514080209002203000c650740c0b112180514000d000301c514401150701c00710190f07200c1020080d00a449640b04000608154104d282e501d8440c0c0e54441c00b20449400404132121100d2018250849890f4100300c0461145101e541010203141060307400150703615000004000420702960341c43e84a612451540014400c0d03078006040358900b00d015003801d601c000c044e44580141c44030320100c8503010400c3c141c82c4410440711000d100088c13178200200c810b42103504c1d4000529410506400300882000203001c50400044c075071007601c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 882540350 1250 882539100 882539143
    0x6112107140f010c030e012a030902030a0b010902040602160617070c140c10020609030403020f0a0905090331090c051201031203050c030f06060d091a060102010b0f090c030a0b03 78
    0x51070328255429150040c3d10f411146607001030043c00e01c60b10004103091410040380d00110bd101103442e0420469020f0b00a806103000840c03000042d4000300201e4440340d00700d45d01c40780ba8415030004103ca920601e800300f50b81d40019aa0720844403403d81e03002640b414410700b040b5a03911002c501180301d01c07512105422a2030a04800d14001c03142110000c4280b0062400703282c002d40307095982c40783e0700001c4d01c24807425040703002c83c0c3d44941203c1c003d0721811005200c17a04241514956a400000340340c41862121000c1050500b8041218540da03034900d00b03600311161a0003c000000d101050565081080401070408580d1158030024021449100003004404c03648800500b15000a000c0b40d564000c10014402c8800b5140c0101c0c2d000902280c4956581940300308a00c010501104000c0042540468860070442d1100c0074a01c1984281c000b440400480c1042010410101c2541c0340d10501c030102244c01209680c01031940540100b000003816450f290009103007803401c51000780002c4a50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 882541600 1250 882540350 882540371
    0x1b02130e030705070519051c05010b0607050a020103180f14120f07060c080402030a080325020610150f270f030c05150a120f0606112107140f010c03 65
    0x4611315a0786d00414032004031070782400e002034880040080100492070503e100744061103020752200d104031074001d1030700d66680401d00d48207840b81184c22040e40442d181c101d003085d5040f04040e0004100e5400720006a41072420717681c54a02c6185000c002c0e0a81c03280100c400908410003000b0041e03040c3c5900e000c1d07142e98841c5401026036019080c40002c0001102c184001078800180058582d036001c000540c480e41c1d55030010300001110035030440c80044620b1550307103054000c1a0b480c080c1c3c1004001c8000151501c0d18410b003242c034401d460b80050241d82c0103151080c402e4400800ca070030b02c02c01c81541c2c25504081c50300100c2c826080000880003040381001042a1903204100515003a616981541000d000c050400d014100c3c503a010300c0780031074107800c01c1c101582c4007807401e007000700003007016030340320140200424500d8055500d1449199207002c0c03100030801c0f6a1a110120300c43d21032400020f95a461052a40c0c4900109603208035241010b9a610a01801202c050706980004a21864 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 882542850 1250 882541600 882541609
    0x51005070f021002030c2503081c050a062301022509060e0709090606022802030610090b0103090c1a190c061404021e03030f0309010203060a061b02130e0307050705 72
    0x7c107055000b1480022442d40040d41e40038800b0302201c1d0440e0b0300540381d10303500034040b0380c000b4104010300102c0c3c903100c1001201c548076441401a42d5800349000e00704094807009095021000380414096482200b20a054501090040c2954440c41198547c815618900b090980b402a08000141d100e05000c020001d940304140c20020080c144080c49014a810310203503d070818031400c0000131509184c0c1814150350005100c0360158040c0c1150030628025890303501c080307901e0107554080d6040600c41c0d12150f110703008c1d50210942258031030000d103140030010300ba080346014085050707003001d01441540c10100000004004c0458640300900d4016240820488402e4461041c004a0034018040542c4900504012154000c82e9500ca01c044d0b1000103803a5003d03814510701e40c040000200008004103402075130040209071107440c2025100c042c1511201510b8100c516890519980040540f0b00440882d004004d00700d40008c41300c0ca400720943c20359009010035601a806240304020a091 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 882544100 1250 882542850 882542863
    0x50403021203010f0e060a080a1110111207020d1b0510050c030d05180d18051008150105090d0308060a24120b030106030b09010c0306051005070f021002030c 69
    0x4040701c400b461036040103003102c108015030103403200d8040c482c0009103c40c0c803000c10010250420508a910703a00b41c0b45400a14010071411541c0079441c0c150f03186035064090141d010031514a40060200407001d44140d0500e0381002c0d070280c0e80107a217541c2c0700012074004000ca90b4043c0c00d032170728440c2c401d0a1400b4000c4d10382242001504100e07042202120084e800320958121030300312400400c05031940d4190391050000c104a41147e40030b101100c82e4840c7d081000c110b00c0300c1800352100c0090356038030204600120659080c1020032030820010796140c400781034a403050101418440c2c104000302c030100b01e60907481c50089001c1019141485124504800310400601e0406c07180d00200c811040d1040e294104080d5032000e204e104c10311b155206041d9007224140e010080c0003007060740e6480c280105d03489402d40303035109031394600b404810800744031303000c2e43c2c0541c0c20141c42c00000c100016400c50302c550054509441101e40e02c1000001603540e82008910b0911a60055444c2c4101303901480c107022 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 882545350 1250 882544100 882544123
    0x5060a122d14121b070803030106110717061308040308041215200d0915090c1a0f0c01020d0501080f012a03051f03030c0b0c0a0c080a0504030f0605040302 68
    0x50140310341040380500c000c115000c908058803404135507040c1c0d1aa40303103000e41680000015001c00b20012501691005d000284041c0d40300071940c1c0d4035070700d035010b44c6403a03400c029034801c03a04610700103103400510810101c0002d11500142d480e0654a4680101540080d002540d64443c411141010300030907212003d02920075000801051002254000b004102000c1c82d140380180801e150402c0c4041c2c0e48002542c0d0307007000c008401856260030351070041040d02021140d012041c04082902500e044001b0324050600b51014034004051482d1a0306e50401d00382600199020031180d0300100e16802460700074035410000b800b03903400103800a405c1d28424816249021243e15901c54060181d640c414020803040c00e0014031a2189405080303400902e100911401c4030210002040503481b40000320391034000c01e00e485260b198048503035918031a1000d001c00241032000705001180400c2d00900d0300f480d440c01d01d5441c1036035035034034040700e00105041501c88550b18410401850b8042c00140001d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 882546600 1250 882545350 882545353
    0x2010203010e01170d08070c0c090507090b0a090e0411030f1b06090603010509090c030a11010306090605012304080106120b060303030103031220040b0a0f0305060a122d14 75
    0x50103041c01d1030f40d610045d100e4541040151030100b080300c2c1c00749050b0549131b40c0000f8090401a141c0411101410044e1421000100041800101d5895000546000207440d5442400072868508007010303503a03000c1c00544452400046041e01c6540c00c02800381c44004480152a0300200c09042040c0000112071950094000300300d4441c480d0740758001c4a0641d0300488a0403100d0b02d400300c810385880781da601c00c9030f0140b1030301074082c05020040c85802c5038010b00b640c0521920307446d00e859001b95003d030311400d070100b0a40c810041c0c00041005185a65011003180942002d540c2d5414500791401a030021483c040c5204140301031108082c0450341c048020740c010b40c61549141e5004003540c00c0c02c09842c10381e90b640d8203070820a488440b40124040c0303407210801e0321640c40b6444200300b9803107d600803000c5070380c50180c0c130121800380c01098400c0000800c140305140ca030220340071fa02d40f40c00204030390907401c040e5286d0181010300c00c4a402c1303030f14444504001061515101403890380d9490b8800f02d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 882547850 1250 882546600 882546629
    0x13051503010b0f1e0301090c2c01060c020d0b100519030b01050607080d0207060f05131106130911090a080c06070609050a050607050d1406030703171902010203010e01 73
    0xb1a207844080720f0400106032600c58081c550151825482120061a1640341d4209143c050510a61801282c00e80c7c04801c1d900625440352404100d5042c01d03400704038401c510b80401007054900442e0000c3e152030001c0c0018880c00d000f0383da00e0f44d4009044a4501012f981604244582d0030440d2189980d000032054003c005421074840143e074450500c43c091080348000b0b441d00800c00c0280c156038424561200941d12041c0c01d103040c2c0003911401c500d40404616020005102c545022203d210381900440d45075813040100c2c061040a40c0601c0103404005240180054840034500c10800703410041c0d0030540d00c440300c0c801040b0751142d465100348a96172180f0201e8402d40e441c81c04036110030364425030020381510f00b450300c2c0e8201410742078041c000d03014030000c0000094010b0000c15051480f043d04205010755507290340138a440a0320311607010b41c002c40301400042d1016401e19071008440240d00d040c04d1000404014a10003180a400140d402000410440c181c8100d1580507082d03440742e18a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 882549100 1250 882547850 882547871
    0x301090506061009030b0901020414041b1115150a08030324040e0a0b060f0411070b071b030309030e04020a3006080604110d03080f090c1305150301 65
    0x151074002500d014858003a40c1190664580039110610003594440359040c0586003d8004c58002c1d0802d04c03841032401c020140c1c1511600d4944580c031802c401e215405003803424205030846a0350321007820702c00f10b84288518140800e40c100035552082e040001c030b600150242d4001e0101c6441c480d1b2010485910a01c240202e41828101c0600c2c812400d58103108908d82c808002005454040c4080d0311501903070f02000144104042018868481a07a0810060840c1c03400e100c115801d0780e0000b0501042485140c0001d04e40c4207440c1c0c1c000e11b031490008a4514801d400104520040e1022804a581d81600800f01500b26540006018040710110300705234030034102801d80820f80c2d001640c06c80190100c0200c0c21000c52240304040102c1c441004000e84402c0d280e40d85003003eaa050b01c0c42142803c41c004545404030f20101442c0d40756881c0d0038a42c81322516900c5e54100900310003400d016400108503141c59201100c00143c1301004081500d05101d9081400030800c0101c41c4e002e80d05004a8a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 882550350 1250 882549100 882549103
    0x1e0c0e010c080304050703060f1d0d05120619150207050906010c0221060106020f0f1b0616050604030903120c02030d0f020a02060d02030601080f16050c010e0f010501060e03010905 79
    0xc1003580102c003850f035a0791640303820b50800d001c40d04010b024030700d050384502d0180ca003a03202d070001c0e03a400261032003914a80c0500e540c0e03c1c903c4090100015404002100c003281c0c201c0041508540094064030385100310082c001342e04941600480702020f040e04161050130350400041d00100000c2d61a81010b0414500003030442c040864040d008001405000740312580d041c0d58869410151016100c99503140e0b100251a200c9644034041540310b2130340180300d038807008150700707144502d60411300f004001604240700140e045034004100c54180c65003c0000714905100300da102c0d92003561508181421898104203203d07910b8198000c020580d1202c2006840c00601e1003031003076990400032074100b101070040346041d402d42e900940006000c100c0c80c04159440e00514010f11098803003a600ea03950300d040112001044a810220300740d664080c00300d50380540f000300565a005000442c1d0200c05a41042c5030a40102111026a54500040200f50f500000d0001482000c4000740716484ad503440c6c0b01d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 882551600 1250 882550350 882550367
    0x702030604080a051209030c0f070b0315030304031203060905010b21100f0f0312050f22050603041401060b07030917070e0405060f07030903020303070f0e041e0c0e01 73
    0x14210440000c0400e990b5014006841006082c904405586e14203050740319140e40203291406460700c1226145c403125940270031100c0c00c4c2d0b0002031840c1d08540d00c017140c0d00100300c40000d0003509400304000100c042691200c6030203203460701c0d4402040c46481d2103504c80407900140d01084405a00740100c83c580c403219491005241e10035040d20702240c8071084402c0003000346500200105c0d03071030719000803072580d820300d43c001301c900601120450a0000c80152118400c04549840a01080064055415a0b0151000c1a281d0021030382195902c60380428031650040d9001d130340040d10202208000d881c00d018007006030180d084614280045558007a102c4401c80c081e05110074030070455442100c004101003401804c441c651030001d41054244252901001c0c0d590102e4140002c000079400c500030b0144c07842d1554036500862456503000c031304651101c19404a00b042003c50844500e1030ba07141e0113030000100f241000e07480d01841d800000c204a441158090040c0240d0000010084c0c1c0c100e103e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 882552850 1250 882551600 882551603
    0xf05030a020f22050f0702010c0203040e0907051309060c031109060d020f13090506090601140d0905160e0105150406080705090301050a091b0b0a0309060b0d03180b0702030604 77
    0xd0420a45010000f80032050380601820056040d0400f2401c40b841a40010380642c3c00120440c481d912a808103c2c00d9410f600b8025025900401081181e40441c03c41207a001c5c01c80c0b41500c420176150b01c001103c12084580d603501190311618820107220140c0700301c0c40700d002c450038104403802d1701940790a0103019001001e4031840d800710b41105030103c1078048078130018070341440c1662542c0d0b89081c4c40e00c00419000740b000040c07030400090001e0a04106480c0100c805855150b00d00e0100c00002d0724076440301071040c041ea9260008080003400c00c220008805032644540032505e414002c0192059405a0095203e07006450180510706402c2c400c0ba42500d070203141c90380c4607580703400082e0350b035120702d041c2c4a40641ca000c1c2000740ca54115800312036450310490780f005800850546090b501006030180e00401042000324044540c001d134041030f4620310800000c12800942d6002030f01c01c0084040990104d0000300e826500711a8000c43d16010b820800450fa0411407030760003080e07840d03078010030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 882553956 1106 882552850 882552859
    0x109030503040c060518120a12020322050d0809190b07020a09020715240806060f030a0c060c03031b020f060a14060f0103061d01050a0f05030a02 64
    0xc072004007091289086c0040141c008104d0092241c2c007480519115801c841000074290700da8000034505c8640185803920b121120480103a2084008031a48504034041070080d60b0b43e10240001103500800c50390b45680060380814100d44148041c5a0030204841d00061748100003c01843c2251090355481d0142d5a141d40081c01d03801007010040103000b0b4101213282030314807940100c044243c01c0c0107180c4000d4194012010850040d000131816412440c2088058209840141000c40302a0018103072200151207010f100c01d59401094204903404000c00b09041c4641c00a5880c0d60f452100000c2c110b048030000382d0b130340d444c48400e210b850288100180403541d06108456222030074828580c65a5100300400500300743d07119015040c9a66140e000c00c01c1c0b110035078001c400c031800c0e0324600d0055051000b003003110500c1d81d02c04440200b2510050050751404654854095070546 = true := by decide +kernel

theorem cover : BRFrame.Cov 882374100 882553956 := by
  have h0 := BRFrame.cov_init 882374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 882374100 ≤ n) (h2 : n < 882553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
