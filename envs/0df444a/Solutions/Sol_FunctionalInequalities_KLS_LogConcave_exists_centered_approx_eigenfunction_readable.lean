-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_centered_approx_eigenfunction_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:26:22.580073+00:00
-- url     : https://prove2.me/submissions/64a317e9-b175-4064-a891-b5d1c508e6c0

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_ApproximateEigenfunction
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_approx_eigenvector_of_gap_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_id_gap_of_literature_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_orthogonal_ker_iff_mean_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_centered_unit_near_optimal_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The zero constant is the zero element of `L²`. -/
@[simp]
theorem FunctionalInequalities.L2.const_zero (μ : ProbabilityMeasure α) : const μ 0 = 0 :=
  map_zero (Lp.const 2 (μ : Measure α))
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
variable {U : V → ℝ} (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- **Approximate first eigenfunctions in the heat model.** If `C_P(ν) = C` with `0 < C < ∞`,
then for every `η > 0` some centered `f ∈ D(A)`, `A = T̄†T̄`, has `‖f‖ = 1` and
`‖A f - C⁻¹ f‖ ≤ C⁻¹ η`. -/
theorem solution {C : NNReal} (hC : 0 < C)
    (hCP : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal)) {η : ℝ} (hη : 0 < η) :
    ∃ f : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      FunctionalInequalities.L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
      ‖FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) f -
          (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤ (C : ℝ)⁻¹ * η := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  have hT : T.IsClosed := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  have hd : Dense (T.domain : Set (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  set lam : ℝ := (C : ℝ)⁻¹ with hlamdef
  have hlam : 0 < lam := inv_pos.mpr hCr
  have horth_iff := FunctionalInequalities.KLS.LogConcave.orthogonal_ker_iff_mean_eq_zero_readable m hν hi hνU hU
  -- the gap `λ ‖y‖² ≤ ‖T̄ y‖²` on `(ker T̄)ᗮ`
  have hgap : ∀ y : T.domain,
      (∀ k : T.domain, T k = 0 → ⟪(y : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0)
        → lam * ‖(y : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤ ‖T y‖ ^ 2 := by
    intro y hy
    have hmy : FunctionalInequalities.L2.mean ν (y : Lp ℝ 2 (ν : Measure V)) = 0 := (horth_iff _).mp hy
    have h := hν.closedWeightedOperator_id_gap_of_literature_le_readable m hi C hCP.le y
    simp only [FunctionalInequalities.L2.center, hmy, FunctionalInequalities.L2.const_zero, sub_zero] at h
    have h2 := mul_le_mul_of_nonneg_left h hlam.le
    rwa [← mul_assoc, hlamdef, inv_mul_cancel₀ hCr.ne', one_mul] at h2
  -- the perturbation size
  set η' : ℝ := min 1 (η ^ 2 / 2) with hη'def
  have hη'pos : 0 < η' := lt_min one_pos (by positivity)
  have hη'1 : η' ≤ 1 := min_le_left _ _
  have hη'2 : η' ≤ η ^ 2 / 2 := min_le_right _ _
  obtain ⟨y, hym, hy1, hTy⟩ :=
    FunctionalInequalities.KLS.LogConcave.exists_centered_unit_near_optimal_readable m hν hi hC hCP hη'pos
  obtain ⟨z, hz, hyz, hAz⟩ := FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap_readable T hT hd hlam hgap y
    ((horth_iff _).mpr hym) hy1 hTy
  -- `‖z‖ ≥ 1 / 2`
  set δ := Real.sqrt (η' / 8) with hδ
  set σ := Real.sqrt (η' / 2) with hσ
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hδ2 : δ ^ 2 = η' / 8 := Real.sq_sqrt (by positivity)
  have hσ2 : σ ^ 2 = η' / 2 := Real.sq_sqrt (by positivity)
  have hδhalf : δ ≤ 1 / 2 := by nlinarith
  have hση : 2 * σ ≤ η := by nlinarith
  have hznorm : 1 / 2 ≤ ‖(z : Lp ℝ 2 (ν : Measure V))‖ := by
    have := norm_sub_norm_le (y : Lp ℝ 2 (ν : Measure V)) (z : Lp ℝ 2 (ν : Measure V))
    rw [hy1] at this
    linarith
  set a := ‖(z : Lp ℝ 2 (ν : Measure V))‖ with ha
  have hapos : 0 < a := by linarith
  refine ⟨a⁻¹ • z, ?_, ?_, ?_⟩
  · apply (horth_iff _).mp
    intro k hk
    change ⟪a⁻¹ • (z : Lp ℝ 2 (ν : Measure V)), (k : Lp ℝ 2 (ν : Measure V))⟫ = 0
    rw [real_inner_smul_left, hz k hk, mul_zero]
  · change ‖a⁻¹ • (z : Lp ℝ 2 (ν : Measure V))‖ = 1
    rw [norm_smul, norm_inv, norm_norm, ← ha, inv_mul_cancel₀ hapos.ne']
  · change ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T (a⁻¹ • z) - lam • a⁻¹ • (z : Lp ℝ 2 (ν : Measure V))‖ ≤ lam * η
    rw [LinearPMap.map_smul, smul_comm lam a⁻¹, ← smul_sub, norm_smul, norm_inv, norm_norm,
      ← ha, inv_mul_le_iff₀ hapos]
    have h1 : lam * σ ≤ lam * (η / 2) := mul_le_mul_of_nonneg_left (by linarith) hlam.le
    have h2 : lam * η * (1 / 2) ≤ lam * η * a :=
      mul_le_mul_of_nonneg_left hznorm (by positivity)
    nlinarith [hAz, h1, h2]
