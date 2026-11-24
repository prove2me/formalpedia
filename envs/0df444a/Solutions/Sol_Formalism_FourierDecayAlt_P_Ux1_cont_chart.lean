-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.cont_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:24:34.548658+00:00
-- url     : https://prove2.me/submissions/b2c06df4-4b88-43a0-a394-240cb973d1f2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_diff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
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
end Formalism.FourierDecayAlt.P.Ux1
