-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.tsact_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:03.440245+00:00
-- url     : https://prove2.me/submissions/1d25131f-4808-4a8e-844e-334757235d01

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
import Theorems.Thm_Formalism_L2_G_Model_TS_tsact_eq_sum

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
theorem _root_.solution (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g := by
  classical
  rw [tsact_eq_sum (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    tsact_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    tsact_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring
end Formalism.L2.G.Model.TS
