-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:03.011768+00:00
-- url     : https://prove2.me/submissions/ce09a1a4-ea0d-418f-a944-20ab8ecea35c

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_eq_sum
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {σ R : Type*} [CommRing R]
namespace Formalism.L2.G.Model.TS
theorem _root_.solution {S : Type*} [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by
  rw [fockR_eq_sum _ _ f.support (support_map_subset φ f), fockR, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_map, map_mul, map_natCast]
end Formalism.L2.G.Model.TS
