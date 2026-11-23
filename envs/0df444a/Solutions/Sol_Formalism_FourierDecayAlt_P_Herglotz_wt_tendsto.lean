-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.wt_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:14.09631+00:00
-- url     : https://prove2.me/submissions/99e6a551-fa01-48e4-95e6-cff9cffccc3b

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_fac_tendsto

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
theorem _root_.solution (τ : Fin d → ℤ) : Tendsto (fun N : ℕ => wt N τ) atTop (𝓝 1) := by
  unfold wt
  simpa using tendsto_finset_prod Finset.univ (fun j _ => fac_tendsto (τ j))
end Formalism.FourierDecayAlt.P.Herglotz
