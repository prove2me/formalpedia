-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.adj_fockR_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:35.502462+00:00
-- url     : https://prove2.me/submissions/be88056e-3c6c-4053-b9a0-b4c25a9d97de

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_smul_left
import Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_symm

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
theorem _root_.solution {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by
  rw [adj_fockR_symm, adj_fockR_smul_left, adj_fockR_symm]
end Formalism.L2.G.Model.TS
