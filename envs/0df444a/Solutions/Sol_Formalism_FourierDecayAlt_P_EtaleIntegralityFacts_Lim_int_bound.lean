-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.int_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:30.259351+00:00
-- url     : https://prove2.me/submissions/cb3677ae-6dee-4d99-822a-830f28a46e81

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f g : α → V) (maj : α → ℝ) (S : Set α) (hS : MeasurableSet S)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (hmaj : Integrable maj μ)
    (hmaj0 : ∀ y, 0 ≤ maj y) {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hfb : ∀ y, ‖f y‖ ≤ B * maj y)
    (hgb : ∀ y, ‖g y‖ ≤ B * maj y) (hin : ∀ y, y ∉ S → ‖f y - g y‖ ≤ B * τ * maj y) :
    ‖∫ y, f y ∂μ - ∫ y, g y ∂μ‖ ≤ B * τ * ∫ y, maj y ∂μ + 2 * B * ∫ y in S, maj y ∂μ := by
  have hfi : Integrable f μ := (hmaj.const_mul B).mono' hf (Eventually.of_forall hfb)
  have hgi : Integrable g μ := (hmaj.const_mul B).mono' hg (Eventually.of_forall hgb)
  have hind : Integrable (S.indicator maj) μ := hmaj.indicator hS
  rw [← integral_sub hfi hgi]
  have hb : Integrable (fun y => B * τ * maj y + 2 * B * S.indicator maj y) μ :=
    (hmaj.const_mul _).add (hind.const_mul _)
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
  · by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
      have h1 := norm_sub_le (f y) (g y)
      have h2 := hfb y
      have h3 := hgb y
      have h4 : 0 ≤ B * τ * maj y := mul_nonneg (mul_nonneg hB hτ) (hmaj0 y)
      linarith
    · rw [Set.indicator_of_notMem hy]
      have := hin y hy
      linarith
  · rw [integral_add (hmaj.const_mul _) (hind.const_mul _), integral_const_mul, integral_const_mul,
      integral_indicator hS]
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
