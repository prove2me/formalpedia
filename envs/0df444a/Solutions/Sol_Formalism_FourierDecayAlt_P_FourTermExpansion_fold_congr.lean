-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.fold_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:23:19.224924+00:00
-- url     : https://prove2.me/submissions/a2425407-fa1b-4d4a-898c-1d55e451e44b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_congr

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
theorem _root_.solution (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) {Φ₁ Φ₂ : Mat k r → E}
    {U : Set (Mat k r)} (hU : IsOpen U) (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) :
    ∀ x ∈ U, x ∈ GV k r → fold M ts Φ₁ x = fold M ts Φ₂ x := by
  induction ts with
  | nil => exact he
  | cons t ts ih =>
    intro x hx hxG
    rw [fold_cons, fold_cons]
    exact top_congr M hU ih t.1 t.2.1 t.2.2 x hx hxG
end Formalism.FourierDecayAlt.P.FourTermExpansion
