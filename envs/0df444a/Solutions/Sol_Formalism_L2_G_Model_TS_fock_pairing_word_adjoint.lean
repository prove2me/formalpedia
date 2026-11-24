-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fock_pairing_word_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:52:30.891773+00:00
-- url     : https://prove2.me/submissions/dcb2b8fc-c4a3-46ab-a51a-ca84e0189ac4

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
import Theorems.Thm_Formalism_L2_G_Model_TS_fock_pairing_divided_adjoint
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_applyWord_cons
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_applyWord_append
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_transposeWord_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model.TS
theorem _root_.solution : FockRWordAdj := by
  intro R _ r n w
  induction w with
  | nil =>
    intro F G
    rfl
  | cons x w ih =>
    intro F G
    rw [adj_applyWord_cons, fock_pairing_divided_adjoint R r n x.1 x.2.1 x.2.2, ih, adj_transposeWord_cons,
      adj_applyWord_append]
    rfl
end Formalism.L2.G.Model.TS
