-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:05.679069+00:00
-- url     : https://prove2.me/submissions/5dd36a63-c15c-4dc0-8f71-9b5a19b47e98

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_eq_sum

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
theorem _root_.solution (f g : MvPolynomial σ R) : fockR f g = fockR g f := by
  classical
  rw [fockR_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    fockR_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring
end Formalism.L2.G.Model.TS
