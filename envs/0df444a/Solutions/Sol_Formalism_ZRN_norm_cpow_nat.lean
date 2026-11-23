-- Prove2me | solution 1 for Formalism.ZRN.norm_cpow_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:05.346311+00:00
-- url     : https://prove2.me/submissions/0fb54623-96e9-443c-a154-d5d76c2384f3

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (n : ℕ) (k : ℝ) (hk : 0 < (n : ℝ) + k) (w : ℂ) :
    ‖((n : ℂ) + (k : ℂ)) ^ w‖ = ((n : ℝ) + k) ^ w.re := by
  have := norm_cpow_eq_rpow_re_of_pos hk w
  push_cast at this; exact this
end Formalism.ZRN
