-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:05.548953+00:00
-- url     : https://prove2.me/submissions/41916175-b11d-4819-adeb-f04159d3b6f0

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_symm
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_sum_left

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
theorem _root_.solution {ι : Type*} (t : Finset ι) (f : MvPolynomial σ R) (g : ι → MvPolynomial σ R) :
    fockR f (∑ i ∈ t, g i) = ∑ i ∈ t, fockR f (g i) := by
  rw [fockR_symm, fockR_sum_left]
  exact Finset.sum_congr rfl fun i _ => fockR_symm _ _
end Formalism.L2.G.Model.TS
