-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.aC_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:21.986515+00:00
-- url     : https://prove2.me/submissions/0b75bfd7-5db2-4801-963f-42eb17f57fb2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_rhoUp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    aC P π' = aC P π - 1 := by
  unfold aC
  have : ∑ i ∈ Icc 1 (P.k - 1), rho P π' i = ∑ i ∈ Icc 1 (P.k - 1), rho P π i + 1 := by
    rw [Finset.sum_congr rfl (rhoUp P l π π' hU), Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hl]
  rw [this]; ring
end Formalism.FourierDecayAlt.P.Mx4
