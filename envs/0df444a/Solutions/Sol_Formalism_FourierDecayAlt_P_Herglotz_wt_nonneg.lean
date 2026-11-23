-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:01.178802+00:00
-- url     : https://prove2.me/submissions/0fb670af-9570-42ef-8a88-e93bb1bdd7f1

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_fac_nonneg

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
theorem _root_.solution (N : ℕ) (τ : Fin d → ℤ) : 0 ≤ wt N τ :=
  Finset.prod_nonneg fun j _ => fac_nonneg N (τ j)
end Formalism.FourierDecayAlt.P.Herglotz
