-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliUnderIntegral.integrable_map_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:45.441918+00:00
-- url     : https://prove2.me/submissions/805dfbd8-9f95-485d-abc9-38961ed6a508

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliUnderIntegral
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CapelliUnderIntegral
theorem _root_.solution {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    Integrable (fun x => (L.map (fun i => φ i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))
end Formalism.FourierDecayAlt.P.CapelliUnderIntegral
