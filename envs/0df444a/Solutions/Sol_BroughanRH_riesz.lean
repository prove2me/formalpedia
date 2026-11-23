-- Prove2me | solution 1 for BroughanRH.riesz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:51:14.47832+00:00
-- url     : https://prove2.me/submissions/03ae5a52-d0fe-46b0-a0d0-06ee21c5d884
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib

open Finset Filter MeasureTheory

namespace IntegralsAux

/-- `e^{-y} ≤ K y^{-α}` -/
lemma exp_neg_le_rpow (α : ℝ) (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∀ y : ℝ, 0 < y → Real.exp (-y) ≤ K * y ^ (-α) := by
  set m := ⌈α⌉₊
  refine ⟨1 + (m.factorial : ℝ), by positivity, fun y hy => ?_⟩
  have h1 : y ^ α ≤ 1 + y ^ m := by
    rcases le_or_gt y 1 with h | h
    · have : y ^ α ≤ 1 := Real.rpow_le_one hy.le h hα
      linarith [pow_nonneg hy.le m]
    · have : y ^ α ≤ y ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (Nat.le_ceil α)
      rw [Real.rpow_natCast] at this
      linarith
  have h2 : y ^ m ≤ m.factorial * Real.exp y := by
    have := Real.pow_div_factorial_le_exp (x := y) hy.le m
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h3 : y ^ α ≤ (1 + m.factorial) * Real.exp y := by
    have : (1 : ℝ) ≤ Real.exp y := Real.one_le_exp hy.le
    nlinarith
  rw [Real.rpow_neg hy.le, Real.exp_neg]
  have hpos : 0 < y ^ α := Real.rpow_pos_of_pos hy α
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc (Real.exp y)⁻¹ * y ^ α ≤ (Real.exp y)⁻¹ * ((1 + m.factorial) * Real.exp y) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by field_simp

/-- kernel bound: `e^{-x/t^2} (t^{θ-3} + x t^{θ-5}) ≤ K x^{-α} t^{θ-3+2α}` -/
lemma kernel_bound (α : ℝ) (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ x t : ℝ, 0 < x → 0 < t →
      Real.exp (-(x / t ^ 2)) * (t ^ (θ - 3) + x * t ^ (θ - 5)) ≤
        K * (x ^ (-α) * t ^ (θ - 3 + 2 * α)) := by
  obtain ⟨K1, hK1, h1⟩ := exp_neg_le_rpow α hα
  obtain ⟨K2, hK2, h2⟩ := exp_neg_le_rpow (α + 1) (by linarith)
  refine ⟨K1 + K2, by positivity, fun θ x t hx ht => ?_⟩
  have hu : 0 < x / t ^ 2 := by positivity
  have e1 := h1 _ hu
  have e2 := h2 _ hu
  have ht2 : (t ^ 2 : ℝ) = t ^ (2 : ℝ) := by rw [Real.rpow_two]
  have hpow : ∀ β : ℝ, (x / t ^ 2) ^ (-β) = x ^ (-β) * t ^ (2 * β) := by
    intro β
    rw [Real.div_rpow hx.le (by positivity), ht2, ← Real.rpow_mul ht.le, Real.rpow_neg hx.le,
      div_eq_mul_inv, ← Real.rpow_neg ht.le]
    ring_nf
  rw [hpow] at e1 e2
  have a1 : t ^ (θ - 3) * (x ^ (-α) * t ^ (2 * α)) = x ^ (-α) * t ^ (θ - 3 + 2 * α) := by
    rw [Real.rpow_add ht]; ring
  have a2 : x * t ^ (θ - 5) * (x ^ (-(α + 1)) * t ^ (2 * (α + 1))) =
      x ^ (-α) * t ^ (θ - 3 + 2 * α) := by
    have : x ^ (-(α + 1)) = x ^ (-α) * x⁻¹ := by
      rw [neg_add, Real.rpow_add hx, Real.rpow_neg_one]
    rw [this]
    have : t ^ (θ - 5) * t ^ (2 * (α + 1)) = t ^ (θ - 3 + 2 * α) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    calc x * t ^ (θ - 5) * (x ^ (-α) * x⁻¹ * t ^ (2 * (α + 1)))
        = x ^ (-α) * (t ^ (θ - 5) * t ^ (2 * (α + 1))) * (x * x⁻¹) := by ring
      _ = _ := by rw [this, mul_inv_cancel₀ hx.ne']; ring
  have p1 : 0 ≤ t ^ (θ - 3) := by positivity
  have p2 : 0 ≤ x * t ^ (θ - 5) := by positivity
  calc Real.exp (-(x / t ^ 2)) * (t ^ (θ - 3) + x * t ^ (θ - 5))
      = t ^ (θ - 3) * Real.exp (-(x / t ^ 2)) + x * t ^ (θ - 5) * Real.exp (-(x / t ^ 2)) := by
        ring
    _ ≤ t ^ (θ - 3) * (K1 * (x ^ (-α) * t ^ (2 * α))) +
        x * t ^ (θ - 5) * (K2 * (x ^ (-(α + 1)) * t ^ (2 * (α + 1)))) := by
        gcongr
    _ = K1 * (t ^ (θ - 3) * (x ^ (-α) * t ^ (2 * α))) +
        K2 * (x * t ^ (θ - 5) * (x ^ (-(α + 1)) * t ^ (2 * (α + 1)))) := by ring
    _ = (K1 + K2) * (x ^ (-α) * t ^ (θ - 3 + 2 * α)) := by
        rw [a1, a2]; ring

/-- The Mertens function bound in the form needed for Abel summation. -/
lemma mertens_bound (θ : ℝ) (hθ : 1 / 2 < θ)
    (hM : ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * t ^ θ := by
  obtain ⟨C, hC⟩ := (hM (θ - 1/2) (by linarith)).bound
  rw [eventually_atTop] at hC
  obtain ⟨N0, hN0⟩ := hC
  refine ⟨max C 0 + N0 + 1, by positivity, fun t ht => ?_⟩
  set N := ⌊t⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr ht
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum : ∑ k ∈ Icc 0 N, (ArithmeticFunction.moebius k : ℝ) =
      ∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
    simp
  have hpowN : (N : ℝ) ^ θ ≤ t ^ θ := Real.rpow_le_rpow hNpos.le hNt (by linarith)
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
  rw [hsum]
  rcases le_or_gt N0 N with h | h
  · have hb := hN0 N h
    have e : ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)‖ =
        |∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ)| := by
      have : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)) =
          ((∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have eθ : (1:ℝ)/2 + (θ - 1/2) = θ := by ring
    rw [e, eθ, Real.norm_of_nonneg (by positivity)] at hb
    calc _ ≤ C * (N : ℝ) ^ θ := hb
      _ ≤ max C 0 * (N : ℝ) ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ (max C 0 + N0 + 1) * t ^ θ := by
        apply mul_le_mul (by linarith) hpowN (by positivity) (by positivity)
  · have hb : |∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k : ℝ)| ≤ N := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Icc 1 N, |(ArithmeticFunction.moebius k : ℝ)| ≤ ∑ k ∈ Icc 1 N, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro k _
            have := ArithmeticFunction.abs_moebius_le_one (n := k)
            exact_mod_cast this
        _ = N := by simp
    have : (N : ℝ) ≤ N0 := by exact_mod_cast h.le
    calc _ ≤ (N0 : ℝ) := hb.trans this
      _ ≤ (max C 0 + N0 + 1) * 1 := by nlinarith [le_max_right C 0]
      _ ≤ (max C 0 + N0 + 1) * t ^ θ := by
        apply mul_le_mul_of_nonneg_left (h1.trans hpowN) (by positivity)


lemma integral_rpow_neg_le (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 1 ≤ N) :
    ∫ t in Set.Ioc (1 : ℝ) N, t ^ (-p) ≤ 1 / (p - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hN']
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le hN']; intro h; exact absurd h.1 (by norm_num)⟩)]
  have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (-p + 1) := by positivity
  rw [Real.one_rpow]
  have : -p + 1 < 0 := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have e : ((N : ℝ) ^ (-p + 1) - 1) / (-p + 1) = (1 - (N : ℝ) ^ (-p + 1)) / (p - 1) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hp1.le
  
lemma abel_bound (θ C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 1 ≤ t → |∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * t ^ θ)
    (f f' : ℝ → ℝ) (hf : ∀ t : ℝ, 1 ≤ t → HasDerivAt f (f' t) t)
    (hf'c : ContinuousOn f' (Set.Ici 1))
    (B p : ℝ) (hp : 1 < p) (hB : ∀ t : ℝ, 1 ≤ t → t ^ θ * |f' t| ≤ B * t ^ (-p))
    (N : ℕ) (hN : 1 ≤ N) :
    |∑ k ∈ Icc 0 N, f k * (ArithmeticFunction.moebius k : ℝ)| ≤
      C * (N : ℝ) ^ θ * |f N| + C * B / (p - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) N, deriv f t = f' t := fun t ht => (hf t ht.1).deriv
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t :=
    fun t ht => (hf t ht.1).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) N) := by
    have : IntegrableOn f' (Set.Icc (1 : ℝ) N) :=
      (hf'c.mono (Set.Icc_subset_Ici_self)).integrableOn_Icc
    exact this.congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  rw [sum_mul_eq_sub_integral_mul₀' (c := fun k => (ArithmeticFunction.moebius k : ℝ))
    (by simp) N hdiff hint]
  have hB0 : 0 ≤ B := by
    have := hB 1 le_rfl
    simp at this
    linarith [abs_nonneg (f' 1)]
  have h1 : |f N * ∑ k ∈ Icc 0 N, (ArithmeticFunction.moebius k : ℝ)| ≤ C * (N : ℝ) ^ θ * |f N| := by
    rw [abs_mul]
    have := hC N hN'
    rw [Nat.floor_natCast] at this
    nlinarith [abs_nonneg (f N)]
  have h2 : |∫ t in Set.Ioc (1 : ℝ) N, deriv f t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| ≤ C * B / (p - 1) := by
    have hg : IntegrableOn (fun t : ℝ => C * B * t ^ (-p)) (Set.Ioc (1 : ℝ) N) := by
      refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact continuousOn_const.mul (continuousOn_id.rpow_const fun t ht =>
        Or.inl (ne_of_gt (lt_of_lt_of_le one_pos ht.1)))
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) N)), ‖deriv f t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)‖ ≤ C * B * t ^ (-p) := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht1 : 1 ≤ t := ht.1.le
      rw [hderiv t ⟨ht1, ht.2⟩, Real.norm_eq_abs, abs_mul]
      have a := hC t ht1
      have b := hB t ht1
      calc |f' t| * |∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)|
          ≤ |f' t| * (C * t ^ θ) := mul_le_mul_of_nonneg_left a (abs_nonneg _)
        _ = C * (t ^ θ * |f' t|) := by ring
        _ ≤ C * (B * t ^ (-p)) := mul_le_mul_of_nonneg_left b hC0
        _ = C * B * t ^ (-p) := by ring
    have := norm_integral_le_of_norm_le hg hae
    rw [← Real.norm_eq_abs]
    refine this.trans ?_
    rw [integral_const_mul]
    have := integral_rpow_neg_le p hp N hN
    calc C * B * ∫ t in Set.Ioc (1 : ℝ) N, t ^ (-p) ≤ C * B * (1 / (p - 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  calc _ ≤ |f N * ∑ k ∈ Icc 0 N, (ArithmeticFunction.moebius k : ℝ)| +
        |∫ t in Set.Ioc (1 : ℝ) N, deriv f t *
          ∑ k ∈ Icc 0 ⌊t⌋₊, (ArithmeticFunction.moebius k : ℝ)| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

end IntegralsAux

namespace IntegralsAux

open ArithmeticFunction

/-- `1/ζ(m)` as a real Möbius series, for natural `m ≥ 2`. -/
lemma inv_zeta_nat (m : ℕ) (hm : 2 ≤ m) :
    Summable (fun n : ℕ => (moebius n : ℝ) / (n : ℝ) ^ m) ∧
    1 / (riemannZeta (m : ℂ)).re = ∑' n : ℕ, (moebius n : ℝ) / (n : ℝ) ^ m := by
  have hs : 1 < (m : ℂ).re := by simp; exact_mod_cast hm
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (moebius n : ℂ)) (m : ℂ) n =
      (((moebius n : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      rw [Complex.cpow_natCast]
  have hsumC : LSeriesSummable (fun n => (moebius n : ℂ)) (m : ℂ) :=
    LSeriesSummable_moebius_iff.mpr hs
  have hsumR : Summable (fun n : ℕ => (moebius n : ℝ) / (n : ℝ) ^ m) := by
    have : Summable (fun n : ℕ => (((moebius n : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ)) := by
      have h2 : LSeries.term (fun n => (moebius n : ℂ)) (m : ℂ) =
          fun n : ℕ => (((moebius n : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ) := funext hterm
      rw [LSeriesSummable, h2] at hsumC
      exact hsumC
    exact Complex.summable_ofReal.mp this
  refine ⟨hsumR, ?_⟩
  have hL : LSeries (fun n => (moebius n : ℂ)) (m : ℂ) =
      ((∑' n : ℕ, (moebius n : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have h1 := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, hL] at h1
  set r := ∑' n : ℕ, (moebius n : ℝ) / (n : ℝ) ^ m
  have hr : r ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hz : riemannZeta (m : ℂ) = ((1 / r : ℝ) : ℂ) := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    rw [eq_div_iff hr']
    exact h1
  rw [hz, Complex.ofReal_re]
  field_simp

lemma range_succ_eq_Icc (N : ℕ) : Finset.range (N + 1) = Finset.Icc 0 N := by
  ext k; simp

/-- If all partial sums over `Icc 0 N` (`N ≥ 1`) are bounded by `B` and the series has sum `S`,
then `|S| ≤ B`. -/
lemma abs_le_of_hasSum_partial {g : ℕ → ℝ} {S B : ℝ} (h : HasSum g S)
    (hb : ∀ N : ℕ, 1 ≤ N → |∑ k ∈ Finset.Icc 0 N, g k| ≤ B) : |S| ≤ B := by
  have ht := h.tendsto_sum_nat
  have ht2 : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 0 (N + 1), g k) atTop (nhds S) := by
    have := ht.comp (tendsto_add_atTop_nat 2)
    refine this.congr fun N => ?_
    simp only [Function.comp]
    rw [show N + 2 = (N + 1) + 1 by ring, range_succ_eq_Icc]
  exact le_of_tendsto' (continuous_abs.tendsto _ |>.comp ht2) fun N => hb (N + 1) (by omega)


lemma riesz_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => (x * Real.exp (-(x / (n : ℝ) ^ 2)) / (n : ℝ) ^ 2) * (moebius n : ℝ))
      (∑' k : ℕ, ((-1 : ℝ)^k * x^(k+1)) / ((k.factorial : ℝ) * (riemannZeta (2 * (k+1 : ℂ))).re)) := by
  set a : ℕ → ℕ → ℝ := fun k n =>
    ((-1 : ℝ)^k * x^(k+1) / (k.factorial : ℝ)) * ((moebius n : ℝ) / (n : ℝ) ^ (2 * k + 2)) with ha
  have hterm : ∀ k : ℕ, ((-1 : ℝ)^k * x^(k+1)) / ((k.factorial : ℝ) * (riemannZeta (2 * (k+1 : ℂ))).re)
      = ∑' n : ℕ, a k n := by
    intro k
    have hz : (2 * ((k : ℂ) + 1)) = ((2 * k + 2 : ℕ) : ℂ) := by push_cast; ring
    obtain ⟨_, h2⟩ := inv_zeta_nat (2 * k + 2) (by omega)
    rw [hz, ha, tsum_mul_left, ← h2]
    field_simp
  -- summability of the double series
  have hbound : ∀ p : ℕ × ℕ, ‖Function.uncurry a p‖ ≤
      (x ^ (p.1 + 1) / (p.1.factorial : ℝ)) * (1 / (p.2 : ℝ) ^ 2) := by
    rintro ⟨k, n⟩
    simp only [Function.uncurry, ha, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg,
      abs_one, one_pow, one_mul]
    rw [abs_of_pos hx, abs_of_pos (by positivity : (0 : ℝ) < k.factorial)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hmu : |(moebius n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have hpow : (n : ℝ) ^ 2 ≤ |(n : ℝ)| ^ (2 * k + 2) := by
        rw [abs_of_pos (by positivity)]
        exact pow_le_pow_right₀ hn1 (by omega)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [abs_nonneg (moebius n : ℝ)]
  have hsum2 : Summable (fun p : ℕ × ℕ => (x ^ (p.1 + 1) / (p.1.factorial : ℝ)) * (1 / (p.2 : ℝ) ^ 2)) := by
    refine Summable.mul_of_nonneg (f := fun k : ℕ => x ^ (k + 1) / (k.factorial : ℝ))
      (g := fun n : ℕ => 1 / (n : ℝ) ^ 2) ?_ ?_ ?_ ?_
    · have := (Real.summable_pow_div_factorial x).mul_left x
      refine this.congr fun k => ?_
      ring
    · exact Real.summable_one_div_nat_pow.mpr (by norm_num)
    · intro k; positivity
    · intro n; positivity
  have hsum : Summable (Function.uncurry a) := Summable.of_norm_bounded hsum2 hbound
  have hcomm := hsum.tsum_comm
  have hinner : ∀ n : ℕ, ∑' k : ℕ, a k n =
      (x * Real.exp (-(x / (n : ℝ) ^ 2)) / (n : ℝ) ^ 2) * (moebius n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha]
    · have hn0 : (n : ℝ) ≠ 0 := by positivity
      have e : ∀ k : ℕ, a k n = ((x / (n : ℝ) ^ 2) * (moebius n : ℝ)) *
          ((-(x / (n : ℝ) ^ 2)) ^ k / (k.factorial : ℝ)) := by
        intro k
        simp only [ha]
        rw [show (-(x / (n:ℝ)^2))^k = (-1)^k * x^k / ((n:ℝ)^2)^k by
          rw [neg_eq_neg_one_mul, mul_pow, div_pow]; ring]
        rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul, pow_succ ((n:ℝ)^2) k, pow_succ x k]
        field_simp
      simp_rw [e]
      have hexp : HasSum (fun k : ℕ => (-(x / (n : ℝ) ^ 2)) ^ k / (k.factorial : ℝ))
          (Real.exp (-(x / (n : ℝ) ^ 2))) := by
        rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
      rw [tsum_mul_left, hexp.tsum_eq]
      ring
  have hcol : Summable (fun n : ℕ => ∑' k : ℕ, a k n) := hsum.prod_symm.prod
  have : (∑' k : ℕ, ((-1 : ℝ)^k * x^(k+1)) / ((k.factorial : ℝ) * (riemannZeta (2 * (k+1 : ℂ))).re))
      = ∑' n : ℕ, ∑' k : ℕ, a k n := by
    rw [tsum_congr hterm]; exact hcomm.symm
  rw [this]
  simp_rw [← hinner]
  exact hcol.hasSum


lemma rpow_sub_nat' {t : ℝ} (ht : 0 < t) (θ : ℝ) (k : ℕ) : t ^ θ / t ^ k = t ^ (θ - k) := by
  rw [Real.rpow_sub ht, Real.rpow_natCast]

/-- Main estimate for the Riesz function. -/
lemma riesz_bound (θ α C K : ℝ) (hC0 : 0 ≤ C) (hK0 : 0 < K)
    (hC : ∀ t : ℝ, 1 ≤ t → |∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (moebius k : ℝ)| ≤ C * t ^ θ)
    (hK : ∀ θ x t : ℝ, 0 < x → 0 < t →
      Real.exp (-(x / t ^ 2)) * (t ^ (θ - 3) + x * t ^ (θ - 5)) ≤ K * (x ^ (-α) * t ^ (θ - 3 + 2 * α)))
    (hp : 1 < -(θ - 3 + 2 * α)) (x : ℝ) (hx : 1 ≤ x) :
    |∑' k : ℕ, ((-1 : ℝ)^k * x^(k+1)) / ((k.factorial : ℝ) * (riemannZeta (2 * (k+1 : ℂ))).re)| ≤
      (C * K + C * (2 * K) / (-(θ - 3 + 2 * α) - 1)) * x ^ (1 - α) := by
  have hx0 : 0 < x := by linarith
  set p := -(θ - 3 + 2 * α) with hpdef
  set f : ℝ → ℝ := fun t => x * Real.exp (-(x / t ^ 2)) / t ^ 2 with hf
  set f' : ℝ → ℝ := fun t => x * Real.exp (-(x / t ^ 2)) * (2 * x / t ^ 5 - 2 / t ^ 3) with hf'
  have hderiv : ∀ t : ℝ, 1 ≤ t → HasDerivAt f (f' t) t := by
    intro t ht
    have ht0 : t ≠ 0 := by positivity
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun t : ℝ => x / t ^ 2) ((0 * t ^ 2 - x * (2 * t)) / (t ^ 2) ^ 2) t :=
      (hasDerivAt_const t x).div h1 (by positivity)
    have h2n : HasDerivAt (fun t : ℝ => -(x / t ^ 2)) (-((0 * t ^ 2 - x * (2 * t)) / (t ^ 2) ^ 2)) t :=
      h2.neg
    have h2e := h2n.exp
    have h3 := h2e.const_mul x
    have h4 := h3.div h1 (by positivity)
    have e : f' t = (x * (Real.exp (-(x / t ^ 2)) * -((0 * t ^ 2 - x * (2 * t)) / (t ^ 2) ^ 2)) * t ^ 2 -
        x * Real.exp (-(x / t ^ 2)) * (2 * t)) / (t ^ 2) ^ 2 := by
      simp only [hf']
      field_simp
      ring
    rw [e]
    exact h4
  have hcont : ContinuousOn f' (Set.Ici 1) := by
    have : ∀ t ∈ Set.Ici (1 : ℝ), t ≠ 0 := fun t ht => by
      have : (1 : ℝ) ≤ t := ht; positivity
    simp only [hf']
    fun_prop (disch := first | exact fun t ht => pow_ne_zero _ (this t ht) | intro t ht; exact pow_ne_zero _ (this t ht))
  have hB : ∀ t : ℝ, 1 ≤ t → t ^ θ * |f' t| ≤ (2 * K * x ^ (1 - α)) * t ^ (-p) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have habs : |f' t| ≤ 2 * x * (Real.exp (-(x / t ^ 2)) * (1 / t ^ 3 + x * (1 / t ^ 5))) := by
      simp only [hf']
      rw [abs_mul, abs_of_pos (by positivity : 0 < x * Real.exp (-(x / t ^ 2)))]
      have : |2 * x / t ^ 5 - 2 / t ^ 3| ≤ 2 * x / t ^ 5 + 2 / t ^ 3 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      calc _ ≤ x * Real.exp (-(x / t ^ 2)) * (2 * x / t ^ 5 + 2 / t ^ 3) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hk := hK θ x t hx0 ht0
    have e1 : t ^ θ * (1 / t ^ 3) = t ^ (θ - 3) := by
      rw [show (θ - 3) = θ - ((3:ℕ):ℝ) by norm_num, ← rpow_sub_nat' ht0]; ring
    have e2 : t ^ θ * (1 / t ^ 5) = t ^ (θ - 5) := by
      rw [show (θ - 5) = θ - ((5:ℕ):ℝ) by norm_num, ← rpow_sub_nat' ht0]; ring
    have e3 : x * x ^ (-α) = x ^ (1 - α) := by
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    calc t ^ θ * |f' t| ≤ t ^ θ * (2 * x * (Real.exp (-(x / t ^ 2)) * (1 / t ^ 3 + x * (1 / t ^ 5)))) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = 2 * x * (Real.exp (-(x / t ^ 2)) * (t ^ θ * (1 / t ^ 3) + x * (t ^ θ * (1 / t ^ 5)))) := by
          ring
      _ = 2 * x * (Real.exp (-(x / t ^ 2)) * (t ^ (θ - 3) + x * t ^ (θ - 5))) := by rw [e1, e2]
      _ ≤ 2 * x * (K * (x ^ (-α) * t ^ (θ - 3 + 2 * α))) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = 2 * K * (x * x ^ (-α)) * t ^ (θ - 3 + 2 * α) := by ring
      _ = _ := by rw [e3, hpdef, neg_neg]
  have hbd : ∀ N : ℕ, 1 ≤ N → C * (N : ℝ) ^ θ * |f N| ≤ C * (K * x ^ (1 - α)) := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hC0
    have hk := hK (θ + 1) x N hx0 hN0
    have e1 : (N : ℝ) ^ θ * |f N| = x * (Real.exp (-(x / (N:ℝ) ^ 2)) * (N : ℝ) ^ (θ + 1 - 3)) := by
      simp only [hf]
      rw [abs_of_pos (by positivity), show θ + 1 - 3 = θ - (2 : ℕ) by push_cast; ring,
        ← rpow_sub_nat' hN0]
      ring
    have hle : (N : ℝ) ^ (θ + 1 - 3 + 2 * α) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    have e3 : x * x ^ (-α) = x ^ (1 - α) := by
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    rw [e1]
    calc x * (Real.exp (-(x / (N:ℝ) ^ 2)) * (N : ℝ) ^ (θ + 1 - 3))
        ≤ x * (Real.exp (-(x / (N:ℝ) ^ 2)) * ((N : ℝ) ^ (θ + 1 - 3) + x * (N : ℝ) ^ (θ + 1 - 5))) := by
          gcongr; nlinarith [Real.rpow_pos_of_pos hN0 (θ + 1 - 5)]
      _ ≤ x * (K * (x ^ (-α) * (N : ℝ) ^ (θ + 1 - 3 + 2 * α))) := by gcongr
      _ ≤ x * (K * (x ^ (-α) * 1)) := by gcongr
      _ = K * (x * x ^ (-α)) := by ring
      _ = K * x ^ (1 - α) := by rw [e3]
  have hS := riesz_hasSum x hx0
  refine abs_le_of_hasSum_partial hS fun N hN => ?_
  have := abel_bound θ C hC0 hC f f' hderiv hcont _ p hp hB N hN
  refine this.trans ?_
  have := hbd N hN
  have hp1 : 0 < p - 1 := by linarith
  calc _ ≤ C * (K * x ^ (1 - α)) + C * (2 * K * x ^ (1 - α)) / (p - 1) := by linarith
    _ = _ := by ring

end IntegralsAux



open IntegralsAux ArithmeticFunction

theorem solution :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun x : ℝ => ∑' k : ℕ, ((-1 : ℝ)^k * x^(k+1)) / ((k.factorial : ℝ) * (riemannZeta (2 * (k+1 : ℂ))).re)) (fun x : ℝ => (x : ℝ) ^ (1 / 4 + ε)) := by
  intro ε hε
  set e := min ε 1 with he
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  set θ := 1 / 2 + e / 4 with hθ
  set α := 3 / 4 - e / 4 with hα
  obtain ⟨C, hC0, hC⟩ := mertens_bound θ (by rw [hθ]; linarith)
    (moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis)
  obtain ⟨K, hK0, hK⟩ := kernel_bound α (by rw [hα]; linarith)
  have hp : 1 < -(θ - 3 + 2 * α) := by rw [hθ, hα]; linarith
  refine Asymptotics.IsBigO.of_bound (C * K + C * (2 * K) / (-(θ - 3 + 2 * α) - 1)) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_pos_of_pos hx0 _).le]
  refine (riesz_bound θ α C K hC0.le hK0 hC hK hp x hx).trans ?_
  have hpos : 0 ≤ C * K + C * (2 * K) / (-(θ - 3 + 2 * α) - 1) := by
    have : 0 < -(θ - 3 + 2 * α) - 1 := by linarith
    positivity
  apply mul_le_mul_of_nonneg_left _ hpos
  exact Real.rpow_le_rpow_of_exponent_le hx (by rw [hα]; linarith)
