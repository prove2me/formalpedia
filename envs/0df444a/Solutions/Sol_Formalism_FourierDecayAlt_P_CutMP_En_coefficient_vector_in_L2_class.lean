-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:47.006583+00:00
-- url     : https://prove2.me/submissions/54ecc62a-92fe-4952-a104-a948e794ffc8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCVInCC
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_inCC_wordSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_CCle_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_word_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
namespace Formalism.FourierDecayAlt.P.CutMP.En
theorem _root_.solution : CVInCC := by
  intro k r E _ _ A m F Y s hF
  obtain ⟨L, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  have hck : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F := by
    obtain ⟨c, hc⟩ := hF
    exact Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast Nat.le_add_left _ _) hc.1
  obtain ⟨c, hc⟩ := inCC_wordSum hF L hLw
  refine ⟨_, Formalism.FourierDecayAlt.P.Qx8.CCle_congr (f := fun g => s • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) ?_
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s hc)⟩
  intro g hg
  rw [Pi.smul_apply, hCV E (B.GV k r) F hck g hg hg]
end Formalism.FourierDecayAlt.P.CutMP.En
