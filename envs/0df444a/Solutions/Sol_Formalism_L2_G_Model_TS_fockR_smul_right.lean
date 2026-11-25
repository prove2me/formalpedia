-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:12:17.36594+00:00
-- url     : https://prove2.me/submissions/f1aac5e0-22fd-42e8-b68c-d7f338a798ce

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_symm
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
variable {σ R : Type*} [CommRing R]
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (c : R) (f g : MvPolynomial σ R) :
    fockR f (c • g) = c * fockR f g := by
  rw [fockR_symm, fockR_smul_left, fockR_symm g]
end Formalism.L2.G.Model.TS
