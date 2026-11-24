-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.cont_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:13.080118+00:00
-- url     : https://prove2.me/submissions/7adcf0b6-286f-459c-8544-21addb682023

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_chart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_chart_diff

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
open Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {H : Mat k r → E}
    (hH : CkOn ((0 : ℕ) : ℕ∞) (GV k r) H) : ContinuousOn (fun Y => H (chart g0 Y)) (Dom k r) := by
  intro Y hY
  apply ContinuousAt.continuousWithinAt
  obtain ⟨U, h', hU, hcU, hcd, hff⟩ := hH _ (chart_mem hg0 hY)
  have hchc : ContinuousAt (chart g0) Y := (chart_diff g0 hY).continuousAt
  have h1 : ContinuousAt (fun Y' => h' (chart g0 Y')) Y :=
    ContinuousAt.comp (g := h') (hcd.continuousOn.continuousAt (hU.mem_nhds hcU)) hchc
  refine h1.congr ?_
  filter_upwards [hchc.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY] with Y' h1 h2
  exact (hff _ h1 (chart_mem hg0 h2)).symm
end Formalism.FourierDecayAlt.P.Ux10
