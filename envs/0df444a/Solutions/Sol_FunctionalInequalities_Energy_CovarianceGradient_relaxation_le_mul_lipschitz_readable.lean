-- Prove2me | solution 1 for FunctionalInequalities.Energy.CovarianceGradient.relaxation_le_mul_lipschitz_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:20.330713+00:00
-- url     : https://prove2.me/submissions/1c47ce60-0b2d-4c82-b063-c9f75240000a

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Factorization
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_eq_ofLinearPMap_readable
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_comp_le_mul_readable
import Theorems.Thm_FunctionalInequalities_exists_norm_sq_eq_inner_of_isSymmetric_readable

section
noncomputable section
open MeasureTheory
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end

section
noncomputable section
open InnerProductSpace
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
section
variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
/-- The covariance operator of any Borel measure has a norm factor `B` satisfying
`⟪Σ v, v⟫ = ‖B v‖²`, including the zero operator of laws without second moment and the
zero-dimensional space. -/
theorem FunctionalInequalities.Covariance.exists_inner_eq_norm_sq (μ : MeasureTheory.Measure V) :
    ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (operator μ v) v = ‖B v‖ ^ 2 := by
  refine exists_norm_sq_eq_inner_of_isSymmetric_readable (operator μ) ?_ ?_
  · intro x y
    calc inner ℝ (operator μ x) y = ProbabilityTheory.covarianceBilin μ x y := operator_inner μ x y
      _ = ProbabilityTheory.covarianceBilin μ y x := ProbabilityTheory.covarianceBilin_comm x y
      _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
      _ = inner ℝ x (operator μ y) := real_inner_comm _ _
  · intro v
    rw [operator_inner]
    exact ProbabilityTheory.covarianceBilin_self_nonneg v
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
section Bridge
/-- The covariance relaxation is at most the operator norm of the covariance times the Lipschitz
gradient relaxation, at every point of finite Lipschitz relaxation. -/
theorem solution (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) (f : Lp ℝ 2 (ν : Measure V))
    (hf : FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac f ≠ ⊤) :
    FunctionalInequalities.Energy.CovarianceGradient.relaxation ν f ≤
      (‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖₊ : ENNReal) * FunctionalInequalities.Energy.LipschitzGradient.relaxation ν m hac f := by
  obtain ⟨B, hB⟩ := FunctionalInequalities.Covariance.exists_inner_eq_norm_sq (ν : Measure V)
  rw [FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap_readable ν B hac hfr hB]
  refine FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul_readable
    (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν (ContinuousLinearMap.id ℝ V) hac) :
      FunctionalInequalities.Energy.PreEnergy (Lp ℝ 2 (ν : Measure V)))
    (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.WeightedGradient.operator ν B hac) : FunctionalInequalities.Energy.PreEnergy (Lp ℝ 2 (ν : Measure V))) id
    continuous_id ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖₊ ?_ f hf
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (FunctionalInequalities.Energy.WeightedGradient.mem_domain_operator_iff ν _ hac x).mp hx
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [FunctionalInequalities.Energy.WeightedGradient.apply_id] using hg.memLp_apply
  have hgB : FunctionalInequalities.Energy.WeightedGradient.IsTest ν B g := ⟨hg.1, hg.memLp, B.comp_memLp' hgrad⟩
  refine ⟨⟨_, FunctionalInequalities.Energy.WeightedGradient.toLp_mem_domain_operator ν B hac hgB⟩, rfl, ?_⟩
  rw [FunctionalInequalities.Energy.PreEnergy.ofLinearPMap_energy, FunctionalInequalities.Energy.PreEnergy.ofLinearPMap_energy,
    FunctionalInequalities.Energy.WeightedGradient.operator_apply ν B hac hfr hgB _ rfl,
    FunctionalInequalities.Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr hg hx rfl, ← ENNReal.coe_mul]
  apply ENNReal.coe_le_coe.mpr
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [FunctionalInequalities.L2.norm_toLp_sq, FunctionalInequalities.L2.norm_toLp_sq, FunctionalInequalities.Energy.WeightedGradient.apply_id, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _)
    (((memLp_two_iff_integrable_sq_norm hgrad.1).mp hgrad).const_mul _) (ae_of_all _ fun x ↦ ?_)
  change ‖B (gradient g x)‖ ^ 2 ≤ ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2
  rw [← hB]
  calc inner ℝ (FunctionalInequalities.Covariance.operator (ν : Measure V) (gradient g x)) (gradient g x)
      ≤ ‖FunctionalInequalities.Covariance.operator (ν : Measure V) (gradient g x)‖ * ‖gradient g x‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ * ‖gradient g x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖FunctionalInequalities.Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2 := by ring
