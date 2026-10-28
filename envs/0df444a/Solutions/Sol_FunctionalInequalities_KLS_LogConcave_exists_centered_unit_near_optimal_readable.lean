-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_centered_unit_near_optimal_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:38.678073+00:00
-- url     : https://prove2.me/submissions/9098fa13-8118-4e25-a998-383c5b658b4a

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_ApproximateEigenfunction
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_center_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_literatureConstant_le_of_gap_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
/-- The mean preserves real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.mean_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (c • f) = c * mean μ f := by
  rw [mean, inner_smul_left]
  rfl
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
end
end
end

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- If `C_P(ν) = C > 0`, then for every `ε > 0` some centered unit `y ∈ D(T̄)` has
`‖T̄ y‖² ≤ C⁻¹ (1 + ε)`: otherwise `Var(u) ≤ C / (1 + ε) · ‖T̄ u‖²` on `D(T̄)` and
`C_P(ν) ≤ C / (1 + ε) < C`. -/
 theorem solution {C : NNReal} (hC : 0 < C)
    (hCP : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      FunctionalInequalities.L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(y : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi y‖ ^ 2 ≤
        (C : ℝ)⁻¹ * (1 + ε) := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  by_contra hcon
  push Not at hcon
  set C' : NNReal := Real.toNNReal ((C : ℝ) / (1 + ε)) with hC'
  have hC'r : ((C' : NNReal) : ℝ) = (C : ℝ) / (1 + ε) :=
    Real.coe_toNNReal _ (by positivity)
  have hgap : ∀ u : T.domain,
      ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ (C' : ℝ) * ‖T u‖ ^ 2 := by
    intro u
    set c : T.domain := ⟨FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
      FunctionalInequalities.KLS.LogConcave.center_mem_closedWeightedOperator_domain m hν hi u⟩ with hc
    have hTc : T c = T u := FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_center_readable m hν hi u
    change ‖(c : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ (C' : ℝ) * ‖T u‖ ^ 2
    rcases eq_or_lt_of_le (norm_nonneg (c : Lp ℝ 2 (ν : Measure V))) with h0 | hpos
    · rw [← h0, sq, zero_mul]
      exact mul_nonneg C'.2 (sq_nonneg _)
    · set a := ‖(c : Lp ℝ 2 (ν : Measure V))‖ with ha
      have hy := hcon (a⁻¹ • c) (by
        change FunctionalInequalities.L2.mean ν (a⁻¹ • (c : Lp ℝ 2 (ν : Measure V))) = 0
        rw [FunctionalInequalities.L2.mean_smul]
        change a⁻¹ * FunctionalInequalities.L2.mean ν (FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))) = 0
        rw [FunctionalInequalities.L2.mean_center, mul_zero]) (by
        change ‖a⁻¹ • (c : Lp ℝ 2 (ν : Measure V))‖ = 1
        rw [norm_smul, norm_inv, norm_norm, ← ha, inv_mul_cancel₀ hpos.ne'])
      rw [LinearPMap.map_smul, hTc, norm_smul, norm_inv, norm_norm, ← ha, mul_pow,
        inv_pow] at hy
      rw [hC'r]
      have ha2 : 0 < a ^ 2 := by positivity
      have h1 : (C : ℝ)⁻¹ * (1 + ε) * a ^ 2 < ‖T u‖ ^ 2 := by
        have h := mul_lt_mul_of_pos_right hy ha2
        have hcancel : (a ^ 2)⁻¹ * ‖T u‖ ^ 2 * a ^ 2 = ‖T u‖ ^ 2 := by
          field_simp
        rwa [hcancel] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      have h2 := mul_lt_mul_of_pos_left h1 hCr
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hCr.ne', one_mul] at h2
      linarith
  have hle := FunctionalInequalities.KLS.LogConcave.literatureConstant_le_of_gap_readable m hν hi C' hgap
  rw [hCP] at hle
  have hle' : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hle
  rw [hC'r] at hle'
  have hlt : (C : ℝ) / (1 + ε) < C := div_lt_self hCr (by linarith)
  linarith
