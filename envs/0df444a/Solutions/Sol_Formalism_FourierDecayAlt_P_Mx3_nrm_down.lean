-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.nrm_down
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:27.292822+00:00
-- url     : https://prove2.me/submissions/e77f603c-d052-4da0-b8d2-4e19f673c52e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rhoUp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    NrmDown P l π' = Nrm P l π := by
  have hr := rhoUp P l π π' hU
  have hrl := hr l hl
  rw [if_pos rfl] at hrl
  unfold NrmDown Nrm
  rw [hrl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π' j - (rho P π l + 1) + 1) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hr j (Finset.mem_of_mem_erase hj), if_neg (Finset.ne_of_mem_erase hj)]; ring
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π' j - (rho P π l + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hr j (Finset.mem_of_mem_erase hj), if_neg (Finset.ne_of_mem_erase hj)]; ring
  rw [e1, e2]
  congr 3
  ring
end Formalism.FourierDecayAlt.P.Mx3
