-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.herm_wb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:59:57.201176+00:00
-- url     : https://prove2.me/submissions/e169b248-d415-4145-a48f-a8f30c5bf3c7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_EmT_Em
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Em_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_Em
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Em_EmT_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) z z = star ((Em k r)ᵀ *ᵥ z) ⬝ᵥ (Hb k *ᵥ ((Em k r)ᵀ *ᵥ z)) := by
  have key : ∀ w : Fin (k + 1) → ℂ, herm (Hpk k r) (Em k r *ᵥ w) (Em k r *ᵥ w) = star w ⬝ᵥ (Hb k *ᵥ w) := by
    intro w
    unfold herm
    rw [Matrix.mulVec_mulVec, Hpk_Em, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Em_conjT, EmT_Em, Matrix.one_mulVec]
  rw [← key, Em_EmT_mulVec z hz]
end Formalism.FourierDecayAlt.P.B2x3
