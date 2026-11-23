-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.wt_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:54.251727+00:00
-- url     : https://prove2.me/submissions/e2b2bd9c-35ff-4318-afe4-d5248fa4cd53

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_fac_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_fac_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Herglotz
theorem _root_.solution (N : ℕ) (τ : Fin d → ℤ) : wt N τ ≤ 1 :=
  Finset.prod_le_one (fun j _ => fac_nonneg N (τ j)) (fun j _ => fac_le_one N (τ j))
end Formalism.FourierDecayAlt.P.Herglotz
