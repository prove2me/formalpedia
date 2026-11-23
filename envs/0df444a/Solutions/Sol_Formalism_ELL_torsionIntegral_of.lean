-- Prove2me | solution 1 for Formalism.ELL.torsionIntegral_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:55.300588+00:00
-- url     : https://prove2.me/submissions/3a5a231e-dd51-4580-bb6b-13b94a11824d

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt
import Theorems.Thm_Formalism_ELL_TorsionIntegralEllipticTorsion_y_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL
open WeierstrassCurve
namespace Formalism.ELL
theorem _root_.solution (h : Formalism.ELL.FormalGroupPointsTorsionFree.{u}) : Formalism.ELL.TorsionIntegral.{u} := by
  intro K _ _ W hW hΔ n hn x y hxy hnP
  have hx : ‖x‖ ≤ 1 := by
    by_contra hx
    push Not at hx
    exact Affine.Point.some_ne_zero hxy (h K W hW hΔ n hn _ hx hnP)
  exact ⟨hx, TorsionIntegralEllipticTorsion.y_int W hW hxy.1 hx⟩
end Formalism.ELL
