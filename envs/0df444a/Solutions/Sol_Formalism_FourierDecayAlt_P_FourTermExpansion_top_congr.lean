-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.top_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:00:45.739261+00:00
-- url     : https://prove2.me/submissions/94b55d41-c95a-45b5-9acd-653d5c439cdc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_congr
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {Φ₁ Φ₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U)
    (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    ∀ x ∈ U, x ∈ GV k r → Top (LT M) v a b Φ₁ x = Top (LT M) v a b Φ₂ x := by
  intro x hx hxG
  rw [top_apply'' M, top_apply'' M, he x hx hxG, EZ_congr hU hx hxG he]
end Formalism.FourierDecayAlt.P.FourTermExpansion
