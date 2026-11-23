-- Prove2me | solution 1 for Formalism.ELL.RootExponentBounds.addle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:49.520474+00:00
-- url     : https://prove2.me/submissions/918e9cbd-e9e3-4a20-8788-c0a1f7ca357c

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
open Formalism Formalism.ELL Formalism.ELL.RootExponentBounds
universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.RootExponentBounds
theorem _root_.solution {x y : K} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
end Formalism.ELL.RootExponentBounds
