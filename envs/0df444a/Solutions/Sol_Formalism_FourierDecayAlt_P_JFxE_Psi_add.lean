-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Psi_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:57:16.747247+00:00
-- url     : https://prove2.me/submissions/add97e27-7b9b-4853-a0ee-7baa7ac30d1e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_hpart1_add__61ce7b77e173
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_hpart2_add__c0f72fda320f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z + W) = Psi D g Z + Psi D g W := by
  simp only [Psi, hpart1_add', hpart2_add', Matrix.mul_add, map_add, smul_add]
  abel
end Formalism.FourierDecayAlt.P.JFxE
