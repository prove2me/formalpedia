-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.chord_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:31.604811+00:00
-- url     : https://prove2.me/submissions/0ee4b701-6437-40d0-92f0-0fce925cc38e

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_some_congr

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
theorem _root_.solution {W : WeierstrassCurve K} {w : PowerSeries K} {σ : Type}
    [DecidableEq (FractionRing (MvPowerSeries σ K))] (s t r : MvPowerSeries σ K)
    (hs : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w s) (yOf w s))
    (ht : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w t) (yOf w t))
    (hne : xOf w s ≠ xOf w t) (hch : ChordAt W w s t r) :
    ∃ h : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w r) (yOf w r),
      WeierstrassCurve.Affine.Point.some _ _ hs + WeierstrassCurve.Affine.Point.some _ _ ht =
        WeierstrassCurve.Affine.Point.some _ _ h := by
  obtain ⟨hx, hy⟩ := hch
  rw [WeierstrassCurve.Affine.Point.add_some (fun h => hne h.1)]
  refine some_congr ?_ ?_
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
    exact hx.symm
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
    exact hy.symm
end Formalism.ELL.WeierstrassCoordinateSubstitution
