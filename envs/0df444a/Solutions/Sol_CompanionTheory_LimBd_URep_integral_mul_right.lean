-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.integral_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:16.50834+00:00
-- url     : https://prove2.me/submissions/5d36a990-970d-443a-a895-6ec33e356317

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace CompanionTheory.LimBd.URep
theorem _root_.solution (f : G → ℂ) (h : G) :
    ∫ g, f (g * h) ∂μ = (Measure.modularCharacterFun h : ℝ) * ∫ g, f g ∂μ := by
  have e : Measure.map (· * h) μ = Measure.modularCharacterFun h • μ := by
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ h]
    exact Measure.isMulLeftInvariant_eq_smul _ μ
  have := (measurableEmbedding_mulRight h).integral_map (μ := μ) f
  rw [← this, e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
end CompanionTheory.LimBd.URep
