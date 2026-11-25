-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.tensor_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:09.796265+00:00
-- url     : https://prove2.me/submissions/a8691b03-7b07-4166-84aa-8eb7cd82371b

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_latIncl_iff_int_incl
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_least_exponent_over_ring
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_pow_sum_smul_mem_delta_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : TensorReal := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hν y
  have he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (exZ (r i) (n i) (hn i) (ν i) l) := fun i =>
    (latIncl_iff_int_incl O l hl hlO (r i) (n i) (hn i) (ν i) _).1
      ((least_exponent_over_ring O l hl hlO (r i) (n i) (hn i) (ν i) (hν i) _).2 le_rfl)
  have h := pow_sum_smul_mem_delta_tensor O l hl hlO ι r n hn ν (fun i => exZ (r i) (n i) (hn i) (ν i) l) he y
  unfold exSum
  exact h
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
