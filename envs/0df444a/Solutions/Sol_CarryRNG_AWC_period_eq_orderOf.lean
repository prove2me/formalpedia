-- Prove2me | solution 1 for CarryRNG.AWC.period_eq_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T19:58:15.765781+00:00
-- url     : https://prove2.me/submissions/bffe7a90-7b96-408c-82d2-6ce84fbb23b3

import Mathlib
import Definitions.Def_CarryRNG_AWC_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed
import Definitions.Def_CarryRNG_AWC_modulus

set_option autoImplicit false

namespace CarryRNG.AWC.P959

open CarryRNG.AWC

/-- digit `i` as a natural number, zero outside the range -/
def dig {b r : ℕ} (w : State b r) (i : ℕ) : ℕ :=
  if h : i < r then ((w.x ⟨i, h⟩ : Fin b) : ℕ) else 0

def X {b r : ℕ} (w : State b r) : ℕ := ∑ i ∈ Finset.range r, dig w i * b ^ i

def H {b r : ℕ} (s : ℕ) (w : State b r) : ℕ :=
  ∑ j ∈ Finset.range s, dig w (r - s + j) * b ^ j

def V {b r : ℕ} (s : ℕ) (w : State b r) : ℕ := X w + H s w + (w.c : ℕ)

lemma dig_lt {b r : ℕ} (hb : 0 < b) (w : State b r) (i : ℕ) : dig w i < b := by
  unfold dig; split_ifs
  · exact (w.x _).isLt
  · exact hb

lemma dig_ge {b r : ℕ} (w : State b r) (i : ℕ) (hi : r ≤ i) : dig w i = 0 := by
  unfold dig; rw [dif_neg (by omega)]

lemma step_dig (b : ℕ) (L : Lags) (z : State b L.r) (i : ℕ) (h : i + 1 < L.r) :
    dig (step b L z) i = dig z (i + 1) := by
  have hi : i < L.r := by omega
  simp only [dig, dif_pos hi, dif_pos h]
  simp [step, h]

lemma step_carry (b : ℕ) (L : Lags) (z : State b L.r) :
    dig (step b L z) (L.r - 1) + b * ((step b L z).c : ℕ) =
      dig z (L.r - L.s) + dig z 0 + (z.c : ℕ) := by
  have hs := L.hs
  have hsr := L.hsr
  have h1 : L.r - 1 < L.r := by omega
  have h2 : ¬ (L.r - 1 + 1 < L.r) := by omega
  have h3 : L.r - L.s < L.r := by omega
  have h4 : 0 < L.r := by omega
  have hc := z.c.isLt
  have hx1 := (z.x ⟨0, h4⟩).isLt
  have hx2 := (z.x ⟨L.r - L.s, h3⟩).isLt
  simp only [dig, dif_pos h1, dif_pos h3, dif_pos h4]
  simp only [step, h2, dif_neg, not_false_eq_true]
  split_ifs with ht <;> simp; omega

lemma step_key (b : ℕ) (L : Lags) (z : State b L.r) :
    b * V L.s (step b L z) + dig (step b L z) (L.r - 1) =
      V L.s z + dig (step b L z) (L.r - 1) * (b ^ L.r + b ^ L.s) := by
  have hs := L.hs
  have hsr := L.hsr
  have hr : 1 ≤ L.r := by omega
  have hs1 : 1 ≤ L.s := by omega
  set d := dig (step b L z) (L.r - 1) with hd
  have hX1 : X (step b L z) =
      (∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ i) + d * b ^ (L.r - 1) := by
    unfold X
    have e := Finset.sum_range_succ (fun i => dig (step b L z) i * b ^ i) (L.r - 1)
    rw [Nat.sub_add_cancel hr] at e
    rw [e]; congr 1
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    rw [step_dig b L z i (by omega)]
  have hX2 : X z = (∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ (i + 1)) + dig z 0 := by
    unfold X
    have e := Finset.sum_range_succ' (fun i => dig z i * b ^ i) (L.r - 1)
    rw [Nat.sub_add_cancel hr] at e
    rw [e]; simp
  have hH1 : H L.s (step b L z) =
      (∑ j ∈ Finset.range (L.s - 1), dig z (L.r - L.s + j + 1) * b ^ j) + d * b ^ (L.s - 1) := by
    unfold H
    have e := Finset.sum_range_succ (fun j => dig (step b L z) (L.r - L.s + j) * b ^ j) (L.s - 1)
    rw [Nat.sub_add_cancel hs1] at e
    rw [e]; congr 1
    · apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
      rw [step_dig b L z _ (by omega)]
    · rw [show L.r - L.s + (L.s - 1) = L.r - 1 by omega]
  have hH2 : H L.s z =
      (∑ j ∈ Finset.range (L.s - 1), dig z (L.r - L.s + j + 1) * b ^ (j + 1)) + dig z (L.r - L.s) := by
    unfold H
    have e := Finset.sum_range_succ' (fun j => dig z (L.r - L.s + j) * b ^ j) (L.s - 1)
    rw [Nat.sub_add_cancel hs1] at e
    rw [e]; simp only [add_zero, pow_zero, mul_one]; rfl
  have hXb : b * X (step b L z) + dig z 0 = X z + d * b ^ L.r := by
    rw [hX1, hX2, mul_add, Finset.mul_sum]
    have hp : b ^ L.r = b ^ (L.r - 1) * b := by rw [← pow_succ, Nat.sub_add_cancel hr]
    rw [hp]
    have hsum : ∑ i ∈ Finset.range (L.r - 1), b * (dig z (i + 1) * b ^ i) =
        ∑ i ∈ Finset.range (L.r - 1), dig z (i + 1) * b ^ (i + 1) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]; ring
  have hHb : b * H L.s (step b L z) + dig z (L.r - L.s) = H L.s z + d * b ^ L.s := by
    rw [hH1, hH2, mul_add, Finset.mul_sum]
    have hp : b ^ L.s = b ^ (L.s - 1) * b := by rw [← pow_succ, Nat.sub_add_cancel hs1]
    rw [hp]
    have hsum : ∑ j ∈ Finset.range (L.s - 1), b * (dig z (L.r - L.s + j + 1) * b ^ j) =
        ∑ j ∈ Finset.range (L.s - 1), dig z (L.r - L.s + j + 1) * b ^ (j + 1) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum]; ring
  have hc := step_carry b L z
  rw [← hd] at hc
  unfold V
  rw [mul_add, mul_add, mul_add]
  linarith

/-- digit sums are bounded, with equality only for all-top digits -/
lemma digsum_le (c n : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i ≤ c) :
    ∑ i ∈ Finset.range n, f i * (c + 1) ^ i + 1 ≤ (c + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := Nat.mul_le_mul_right ((c + 1) ^ n) (hf n)
    nlinarith

lemma digsum_eq (c n : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i ≤ c)
    (he : ∑ i ∈ Finset.range n, f i * (c + 1) ^ i + 1 = (c + 1) ^ n) :
    ∀ i < n, f i = c := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ] at he
    have h1 := digsum_le c n f hf
    have h2 := Nat.mul_le_mul_right ((c + 1) ^ n) (hf n)
    have hP : 0 < (c + 1) ^ n := by positivity
    have e1 : ∑ i ∈ Finset.range n, f i * (c + 1) ^ i + 1 = (c + 1) ^ n := by nlinarith
    have e2 : f n * (c + 1) ^ n = c * (c + 1) ^ n := by nlinarith
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact ih e1 i h
    · subst h; exact Nat.eq_of_mul_eq_mul_right hP e2

lemma digsum_zero (b n : ℕ) (hb : 0 < b) (f : ℕ → ℕ)
    (he : ∑ i ∈ Finset.range n, f i * b ^ i = 0) : ∀ i < n, f i = 0 := by
  intro i hi
  rw [Finset.sum_eq_zero_iff] at he
  have := he i (Finset.mem_range.mpr hi)
  rcases Nat.mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h (pow_ne_zero _ (by omega))

lemma X_le {b r : ℕ} (hb : 0 < b) (w : State b r) : X w + 1 ≤ b ^ r := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact digsum_le c r (dig w) (fun i => by have := dig_lt hb w i; omega)

lemma H_le {b r : ℕ} (hb : 0 < b) (s : ℕ) (w : State b r) : H s w + 1 ≤ b ^ s := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact digsum_le c s (fun j => dig w (r - s + j)) (fun i => by have := dig_lt hb w (r - s + i); omega)

lemma V_le {b r : ℕ} (hb : 0 < b) (s : ℕ) (w : State b r) : V s w + 1 ≤ b ^ r + b ^ s := by
  have h1 := X_le hb w
  have h2 := H_le hb s w
  have h3 := w.c.isLt
  unfold V; omega

lemma state_ext {b r : ℕ} (w w' : State b r) (hd : ∀ i, dig w i = dig w' i)
    (hc : (w.c : ℕ) = w'.c) : w = w' := by
  cases w with
  | mk x c =>
    cases w' with
    | mk x' c' =>
      simp only [State.mk.injEq]
      refine ⟨?_, Fin.ext hc⟩
      funext i
      apply Fin.ext
      have := hd i.val
      simpa [dig, i.isLt] using this

lemma V_zero {b r : ℕ} (hb : 2 ≤ b) (s : ℕ) (w : State b r) (h : V s w = 0) :
    w = zeroSeed b r hb := by
  unfold V at h
  have hX : X w = 0 := by omega
  have hc : (w.c : ℕ) = 0 := by omega
  have hd := digsum_zero b r (by omega) (dig w) hX
  apply state_ext
  · intro i
    by_cases hi : i < r
    · rw [hd i hi]; simp [dig, zeroSeed, hi]
    · rw [dig_ge _ _ (by omega), dig_ge _ _ (by omega)]
  · rw [hc]; simp [zeroSeed]

lemma V_top {b r : ℕ} (hb : 2 ≤ b) (s : ℕ) (w : State b r)
    (h : V s w + 1 = b ^ r + b ^ s) : w = topSeed b r hb := by
  have h1 := X_le (by omega : 0 < b) w
  have h2 := H_le (by omega : 0 < b) s w
  have h3 := w.c.isLt
  unfold V at h
  have hX : X w + 1 = b ^ r := by omega
  have hc : (w.c : ℕ) = 1 := by omega
  obtain ⟨c, hcb⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hd : ∀ i < r, dig w i = c := by
    apply digsum_eq c r (dig w) (fun i => by have := dig_lt (by omega : 0 < b) w i; omega)
    rw [← hcb]; exact hX
  apply state_ext
  · intro i
    by_cases hi : i < r
    · rw [hd i hi]; simp [dig, topSeed, hi]; omega
    · rw [dig_ge _ _ (by omega), dig_ge _ _ (by omega)]
  · rw [hc]; simp [topSeed]

/-- the potential in `ZMod m` -/
lemma cast_key (b : ℕ) (L : Lags) (z : State b L.r) (hb : 0 < b) :
    ((b : ZMod (modulus b L)) * (V L.s (step b L z) : ZMod (modulus b L))) =
      (V L.s z : ZMod (modulus b L)) := by
  have hk := step_key b L z
  have hpos : 1 ≤ b ^ L.r := Nat.one_le_pow _ _ hb
  have hm : b ^ L.r + b ^ L.s = modulus b L + 1 := by unfold modulus; omega
  rw [hm] at hk
  have hk' : b * V L.s (step b L z) = V L.s z + dig (step b L z) (L.r - 1) * modulus b L := by
    rw [mul_add, mul_one] at hk; omega
  have := congrArg (fun n : ℕ => (n : ZMod (modulus b L))) hk'
  simpa [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self] using this

lemma iter_key (b : ℕ) (L : Lags) (hb : 0 < b) (k : ℕ) (z : State b L.r) :
    ((b : ZMod (modulus b L)) ^ k * (V L.s ((step b L)^[k] z) : ZMod (modulus b L))) =
      (V L.s z : ZMod (modulus b L)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_assoc, cast_key b L _ hb, ih]

lemma iter_dig (b : ℕ) (L : Lags) (w : State b L.r) (j : ℕ) :
    ∀ n i, i + n < L.r → dig ((step b L)^[j + n] w) i = dig ((step b L)^[j] w) (i + n) := by
  intro n
  induction n with
  | zero => intro i _; simp
  | succ n ih =>
    intro i hi
    rw [← Nat.add_assoc, Function.iterate_succ_apply', step_dig b L _ i (by omega),
      ih (i + 1) (by omega)]
    congr 1; omega

/-- backward uniqueness: a potential strictly between `0` and `m` determines its predecessor -/
lemma back (b : ℕ) (L : Lags) (hb : 0 < b) (w w' : State b L.r)
    (hw : 0 < V L.s w ∧ V L.s w < modulus b L) (hw' : 0 < V L.s w' ∧ V L.s w' < modulus b L)
    (he : V L.s (step b L w) = V L.s (step b L w')) :
    V L.s w = V L.s w' ∧ dig (step b L w) (L.r - 1) = dig (step b L w') (L.r - 1) := by
  have hpos : 1 ≤ b ^ L.r := Nat.one_le_pow _ _ hb
  have hm : b ^ L.r + b ^ L.s = modulus b L + 1 := by unfold modulus; omega
  have k1 := step_key b L w
  have k2 := step_key b L w'
  rw [hm, mul_add, mul_one] at k1 k2
  set m := modulus b L
  set d := dig (step b L w) (L.r - 1)
  set d' := dig (step b L w') (L.r - 1)
  have e1 : b * V L.s (step b L w) = V L.s w + m * d := by rw [mul_comm m d]; omega
  have e2 : b * V L.s (step b L w') = V L.s w' + m * d' := by rw [mul_comm m d']; omega
  rw [he] at e1
  have hmpos : 0 < m := by omega
  have em : V L.s w = V L.s w' := by
    have a1 : (V L.s w + m * d) % m = V L.s w := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw.2]
    have a2 : (V L.s w' + m * d') % m = V L.s w' := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw'.2]
    rw [← a1, ← a2, ← e1, ← e2]
  refine ⟨em, ?_⟩
  have a1 : (V L.s w + m * d) / m = d := by
    rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hw.2, zero_add]
  have a2 : (V L.s w' + m * d') / m = d' := by
    rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hw'.2, zero_add]
  rw [← a1, ← a2, ← e1, ← e2]

end CarryRNG.AWC.P959

open CarryRNG.AWC in
theorem solution (b : ℕ) (L : Lags) (hb : 2 ≤ b) (hm : (modulus b L).Prime)
    (z : State b L.r) (h0 : z ≠ zeroSeed b L.r hb) (h1 : z ≠ topSeed b L.r hb) :
    Function.minimalPeriod (step b L) ((step b L)^[L.r] z) =
      orderOf (b : ZMod (modulus b L)) := by
  have hb0 : 0 < b := by omega
  have hs := L.hs
  have hsr := L.hsr
  have : Fact (modulus b L).Prime := ⟨hm⟩
  have hpos : 1 ≤ b ^ L.r := Nat.one_le_pow _ _ hb0
  have hm1 : b ^ L.r + b ^ L.s = modulus b L + 1 := by unfold modulus; omega
  have hbm : b < modulus b L := by
    have e1 : b ^ 2 ≤ b ^ L.r := Nat.pow_le_pow_right hb0 (by omega)
    have e2 : b ^ 1 ≤ b ^ L.s := Nat.pow_le_pow_right hb0 hs
    rw [pow_one] at e2
    nlinarith
  have hbz : (b : ZMod (modulus b L)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hb0 h) (by omega)
  have range_of : ∀ w : State b L.r, (P959.V L.s w : ZMod (modulus b L)) ≠ 0 →
      0 < P959.V L.s w ∧ P959.V L.s w < modulus b L := by
    intro w hw
    have hle := P959.V_le hb0 L.s w
    refine ⟨Nat.pos_of_ne_zero (fun h => hw (by rw [h]; simp)), ?_⟩
    rcases lt_or_eq_of_le (show P959.V L.s w ≤ modulus b L by omega) with h | h
    · exact h
    · exact absurd (by rw [h]; exact ZMod.natCast_self _) hw
  have hz : (P959.V L.s z : ZMod (modulus b L)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hle := P959.V_le hb0 L.s z
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · have hk0 : k = 0 := by omega
      subst hk0
      exact h0 (P959.V_zero hb L.s z (by simpa using hk))
    · have hk2 : k = 1 := by
        by_contra hne
        have : modulus b L * 2 ≤ modulus b L * k := Nat.mul_le_mul_left _ (by omega)
        omega
      subst hk2
      exact h1 (P959.V_top hb L.s z (by omega))
  have hiter : ∀ w : State b L.r, (P959.V L.s w : ZMod (modulus b L)) ≠ 0 →
      ∀ j, (P959.V L.s ((step b L)^[j] w) : ZMod (modulus b L)) ≠ 0 := by
    intro w hw j h
    have := P959.iter_key b L hb0 j w
    rw [h, mul_zero] at this
    exact hw this.symm
  have chain : ∀ u u' : State b L.r, (P959.V L.s u : ZMod (modulus b L)) ≠ 0 →
      (P959.V L.s u' : ZMod (modulus b L)) ≠ 0 →
      P959.V L.s ((step b L)^[L.r] u) = P959.V L.s ((step b L)^[L.r] u') →
      (step b L)^[L.r] u = (step b L)^[L.r] u' := by
    intro u u' hu hu' he
    have hV : ∀ i ≤ L.r, P959.V L.s ((step b L)^[L.r - i] u) = P959.V L.s ((step b L)^[L.r - i] u') := by
      intro i
      induction i with
      | zero => intro _; simpa using he
      | succ i ih =>
        intro hi
        have e := ih (by omega)
        have hk : L.r - i = (L.r - (i + 1)) + 1 := by omega
        rw [hk, Function.iterate_succ_apply', Function.iterate_succ_apply'] at e
        exact (P959.back b L hb0 _ _ (range_of _ (hiter u hu _)) (range_of _ (hiter u' hu' _)) e).1
    have hV' : ∀ j ≤ L.r, P959.V L.s ((step b L)^[j] u) = P959.V L.s ((step b L)^[j] u') := by
      intro j hj
      have := hV (L.r - j) (by omega)
      rwa [Nat.sub_sub_self hj] at this
    have hD : ∀ j < L.r, P959.dig ((step b L)^[j + 1] u) (L.r - 1) =
        P959.dig ((step b L)^[j + 1] u') (L.r - 1) := by
      intro j hj
      have e := hV' (j + 1) (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at e ⊢
      exact (P959.back b L hb0 _ _ (range_of _ (hiter u hu _)) (range_of _ (hiter u' hu' _)) e).2
    have hdig : ∀ i, P959.dig ((step b L)^[L.r] u) i = P959.dig ((step b L)^[L.r] u') i := by
      intro i
      by_cases hi : i < L.r
      · have a := P959.iter_dig b L u (i + 1) (L.r - 1 - i) i (by omega)
        have a' := P959.iter_dig b L u' (i + 1) (L.r - 1 - i) i (by omega)
        rw [show i + 1 + (L.r - 1 - i) = L.r by omega,
          show i + (L.r - 1 - i) = L.r - 1 by omega] at a a'
        rw [a, a', hD i hi]
      · rw [P959.dig_ge _ _ (by omega), P959.dig_ge _ _ (by omega)]
    apply P959.state_ext _ _ hdig
    have hXe : P959.X ((step b L)^[L.r] u) = P959.X ((step b L)^[L.r] u') := by
      unfold P959.X; exact Finset.sum_congr rfl (fun i _ => by rw [hdig i])
    have hHe : P959.H L.s ((step b L)^[L.r] u) = P959.H L.s ((step b L)^[L.r] u') := by
      unfold P959.H; exact Finset.sum_congr rfl (fun i _ => by rw [hdig])
    have := hV' L.r le_rfl
    unfold P959.V at this
    omega
  have hpow1 : (b : ZMod (modulus b L)) ^ (modulus b L - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hbz
  have hfin : IsOfFinOrder (b : ZMod (modulus b L)) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨modulus b L - 1, by omega, hpow1⟩
  have hn : 0 < orderOf (b : ZMod (modulus b L)) := hfin.orderOf_pos
  have hper : Function.IsPeriodicPt (step b L) (orderOf (b : ZMod (modulus b L)))
      ((step b L)^[L.r] z) := by
    show (step b L)^[orderOf (b : ZMod (modulus b L))] ((step b L)^[L.r] z) = (step b L)^[L.r] z
    have hcomm : (step b L)^[orderOf (b : ZMod (modulus b L))] ((step b L)^[L.r] z) =
        (step b L)^[L.r] ((step b L)^[orderOf (b : ZMod (modulus b L))] z) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]
    have hz' := hiter z hz (orderOf (b : ZMod (modulus b L)))
    have k := P959.iter_key b L hb0 (orderOf (b : ZMod (modulus b L))) ((step b L)^[L.r] z)
    rw [pow_orderOf_eq_one, one_mul, hcomm] at k
    have r1 := range_of _ (hiter _ hz' L.r)
    have r2 := range_of _ (hiter z hz L.r)
    have hVeq := (ZMod.natCast_eq_natCast_iff' _ _ _).mp k
    rw [Nat.mod_eq_of_lt r1.2, Nat.mod_eq_of_lt r2.2] at hVeq
    rw [hcomm]
    exact chain _ _ hz' hz hVeq
  have hdvd1 := hper.minimalPeriod_dvd
  have hpp := Function.isPeriodicPt_minimalPeriod (step b L) ((step b L)^[L.r] z)
  have hdvd2 : orderOf (b : ZMod (modulus b L)) ∣
      Function.minimalPeriod (step b L) ((step b L)^[L.r] z) := by
    apply orderOf_dvd_of_pow_eq_one
    have k := P959.iter_key b L hb0 (Function.minimalPeriod (step b L) ((step b L)^[L.r] z))
      ((step b L)^[L.r] z)
    rw [hpp.eq] at k
    have hy0 := hiter z hz L.r
    have hmul : ((b : ZMod (modulus b L)) ^ Function.minimalPeriod (step b L)
        ((step b L)^[L.r] z) - 1) * (P959.V L.s ((step b L)^[L.r] z) : ZMod (modulus b L)) = 0 := by
      rw [sub_mul, k, one_mul, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hy0
  exact Nat.dvd_antisymm hdvd1 hdvd2
