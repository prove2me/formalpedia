-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliUnderIntegral.integral_map_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:36:36.0315+00:00
-- url     : https://prove2.me/submissions/f4e314bd-849c-4ef7-92a1-cb737eae460a

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliUnderIntegral_integrable_map_sum

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
    ∫ x, (L.map (fun i => φ i x)).sum ∂μ = (L.map (fun i => ∫ x, φ i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := h i (by simp)
    have hL : ∀ j ∈ L, Integrable (φ j) μ := fun j hj => h j (by simp [hj])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add hi (integrable_map_sum L φ hL), ih hL]
end Formalism.FourierDecayAlt.P.CapelliUnderIntegral
