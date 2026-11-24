-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:21:25.141872+00:00
-- url     : https://prove2.me/submissions/96b196f0-4526-4595-a870-20cb9a581cc0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_hasDerivAt
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
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ₁ Φ₂ : Mat k r → E} {g X : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g)
    (hgG : g ∈ GV k r) (hX : inLie k r X) (c : ℂ) :
    RdV X (fun x => Φ₁ x + c • Φ₂ x) g = RdV X Φ₁ g + c • RdV X Φ₂ g :=
  (((loc_hasDerivAt le_rfl h₁ hgG hX).add ((loc_hasDerivAt le_rfl h₂ hgG hX).const_smul c))).deriv
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
