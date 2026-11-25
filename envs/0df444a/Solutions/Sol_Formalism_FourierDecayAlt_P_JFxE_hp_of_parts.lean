-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.hp_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:23:45.884702+00:00
-- url     : https://prove2.me/submissions/98af5ec6-61d2-4517-a840-e79e44650d95

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hermPart_eq_self_of_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hpart2_eq_zero_of_inLie
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_hpart1_add__61ce7b77e173
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_hpart2_add__c0f72fda320f
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hpart1_I_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hpart2_I_smul

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
theorem _root_.solution {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) :
    hpart1 (Hpk k r) (X + Complex.I • Y) = X ∧ hpart2 (Hpk k r) (X + Complex.I • Y) = Y := by
  refine ⟨?_, ?_⟩
  · rw [hpart1_add', hpart1_I_smul, hermPart_eq_self_of_mem_lie hX, hpart2_eq_zero_of_inLie hY, neg_zero, add_zero]
  · rw [hpart2_add', hpart2_I_smul, hpart2_eq_zero_of_inLie hX, hermPart_eq_self_of_mem_lie hY, zero_add]
end Formalism.FourierDecayAlt.P.JFxE
