-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.rho_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:40.293011+00:00
-- url     : https://prove2.me/submissions/111a9ff6-479b-45d6-97ff-697e86dc5d93

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_tyInterlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_ord

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
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) (i j : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hij : i < j) : rho P π j < rho P π i := by
  have hI := tyInterlaces P hP π
  have o := (ord P.k P.u P.u' (rho P π) hI i hi).2.2.2 j hj hij
  have b := hI i hi
  linarith [o.1, b.2.2.1]
end Formalism.FourierDecayAlt.P.Mx3
