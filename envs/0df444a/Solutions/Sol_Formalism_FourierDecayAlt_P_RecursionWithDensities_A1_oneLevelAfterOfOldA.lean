-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.oneLevelAfterOfOldA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:18.031845+00:00
-- url     : https://prove2.me/submissions/0b71c253-a127-4da9-a39b-44ed829bff4a

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_lsup_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axK__dd0248578f9d
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_axA2__0d56062f0ae4
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_thetaDomination_d_of_axK_of_domMinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution : TC.OneLevelAfterOfOldA := by
  intro hO E _ _ H _ _ W _ len Kl D Sg Φ tr Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 ep a i hNZ hi1 hi hep ha
    hK hA2 hTh hE hLE hLS
  obtain ⟨Th, hD⟩ := hTh
  have h := hO E H W len Kl (D' D Sg Th) Sg Φ tr Pat1 Pat3 pat1 pat3 c1 c3 ep1 ep3 bd4 ep a i hNZ hi1 hi
    hep ha (axK' D Sg Th hNZ hK) (axA2' D Sg Th hA2) (thetaDomination_d_of_axK_of_domMinA D Sg Th hNZ hK hD) hE hLE hLS
  simp only [lsup_eq] at h
  exact h
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
