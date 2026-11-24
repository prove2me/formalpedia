-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:39:02.58048+00:00
-- url     : https://prove2.me/submissions/0a3dd8ee-534e-4c7f-a700-c191910856ad

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_sum_left
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_sum_right

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
variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution {τ : Type*} (f g : MvPolynomial τ K) :
    fockR f g = ∑ m ∈ f.support, ∑ m' ∈ g.support,
      fockR (monomial m (coeff m f)) (monomial m' (coeff m' g)) := by
  conv_lhs => rw [f.as_sum, g.as_sum]
  rw [fockR_sum_left]
  exact Finset.sum_congr rfl fun m _ => fockR_sum_right _ _ _
end Formalism.L2.G.Model.TS
