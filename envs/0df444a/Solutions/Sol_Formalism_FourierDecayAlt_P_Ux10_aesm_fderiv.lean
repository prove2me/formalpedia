-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.aesm_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:14:25.260818+00:00
-- url     : https://prove2.me/submissions/33ca2ef6-e8f2-4f0c-a45c-942e8df16392

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_aesm_deriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {F : α → X → E} {x : X} (hd : ∀ ξ, DifferentiableAt ℝ (F ξ) x)
    (hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fun ξ => F ξ y) μ) :
    AEStronglyMeasurable (fun ξ => fderiv ℝ (F ξ) x) μ := by
  classical
  set b := Module.finBasis ℝ X with hb
  have e : (fun ξ => fderiv ℝ (F ξ) x) = fun ξ =>
      ∑ j, (LinearMap.toContinuousLinearMap (b.coord j)).smulRight (fderiv ℝ (F ξ) x (b j)) := by
    funext ξ
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap']
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Module.Basis.coord_apply]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  have hl : HasDerivAt (fun t : ℝ => x + t • b j) (b j) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (b j)).const_add x
    simpa using h
  have hj : AEStronglyMeasurable (fun ξ => fderiv ℝ (F ξ) x (b j)) μ := by
    refine aesm_deriv (G := fun ξ t => F ξ (x + t • b j)) (fun ξ => ?_) ?_
    · exact (hd ξ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    · have ht : Tendsto (fun t : ℝ => x + t • b j) (𝓝 0) (𝓝 x) := by
        have := hl.continuousAt.tendsto
        simpa using this
      exact ht.eventually hm
  have hc : Continuous fun e : E => (LinearMap.toContinuousLinearMap (b.coord j)).smulRight e :=
    (ContinuousLinearMap.smulRightL ℝ X E (LinearMap.toContinuousLinearMap (b.coord j))).continuous
  exact hc.comp_aestronglyMeasurable hj
end Formalism.FourierDecayAlt.P.Ux10
