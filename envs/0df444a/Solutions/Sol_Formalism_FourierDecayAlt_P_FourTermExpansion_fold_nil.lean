-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.fold_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:38.900638+00:00
-- url     : https://prove2.me/submissions/5ddee863-16ff-4da7-8157-dc079b11113f

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
theorem _root_.solution (Φ : Mat k r → E) : fold M [] Φ = Φ := rfl
end Formalism.FourierDecayAlt.P.FourTermExpansion
