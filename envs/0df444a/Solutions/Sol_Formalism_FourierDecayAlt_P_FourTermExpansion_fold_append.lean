-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.fold_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:05.787248+00:00
-- url     : https://prove2.me/submissions/16aa699d-e64c-43b8-bc7a-109260b71010

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion

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
theorem _root_.solution (ts ts' : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (Φ : Mat k r → E) :
    fold M (ts ++ ts') Φ = fold M ts (fold M ts' Φ) := by
  simp only [fold, List.map_append, List.foldr_append]
end Formalism.FourierDecayAlt.P.FourTermExpansion
