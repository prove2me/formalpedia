-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.some_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:51.555806+00:00
-- url     : https://prove2.me/submissions/d9ece272-1927-4a0a-a902-f42033ff15a0

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassCoordinateSubstitution
theorem _root_.solution {L : Type u} [Field L] {W' : WeierstrassCurve.Affine L} {x y x' y' : L}
    {h : W'.Nonsingular x y} (hx : x = x') (hy : y = y') :
    ∃ h' : W'.Nonsingular x' y', WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx
  subst hy
  exact ⟨h, rfl⟩
end Formalism.ELL.WeierstrassCoordinateSubstitution
