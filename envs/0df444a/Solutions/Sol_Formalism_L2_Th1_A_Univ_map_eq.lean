-- Prove2me | solution 1 for Formalism.L2.Th1.A.Univ.map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:13.999778+00:00
-- url     : https://prove2.me/submissions/2dfc2902-7dab-40b0-af73-28b21c9a8bf1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Univ
namespace Formalism.L2.Th1.A.Univ
theorem _root_.solution {R : Type u} [CommRing R] (W : WeierstrassCurve R) : W₀.map (φ_of W) = W := by
  cases W
  simp [Univ.W₀, Univ.φ_of, WeierstrassCurve.map]
end Formalism.L2.Th1.A.Univ
