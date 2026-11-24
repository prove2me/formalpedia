-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fock_pairing_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:21.17196+00:00
-- url     : https://prove2.me/submissions/93e17171-25af-4452-ab6b-647d76497687

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_symm
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_add_left
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_smul_left

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
theorem _root_.solution : FockRBilin := fun _ _ _ f f' g a =>
  ⟨fockR_add_left f f' g, fockR_smul_left a f g, fockR_symm f g⟩
end Formalism.L2.G.Model.TS
