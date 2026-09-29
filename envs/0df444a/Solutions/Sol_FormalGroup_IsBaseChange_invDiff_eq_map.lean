-- Prove2me | solution 1 for FormalGroup.IsBaseChange.invDiff_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/83e0fb02-dff2-50d5-a70f-9600afccf649

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsBaseChange_invDiff_eq_map

set_option autoImplicit false

open FormalGroup

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S)
    (hG : F.IsBaseChange f G) :
    G.invDiff = PowerSeries.map f F.invDiff := by
  classical
  have hGs : G.toPowerSeries = MvPowerSeries.map f F.toPowerSeries := hG

  have hpX : G.partialX = MvPowerSeries.map f F.partialX := by
    unfold FormalGroup.partialX
    ext d
    rw [MvPowerSeries.kw_coeff_pderiv, MvPowerSeries.coeff_map, MvPowerSeries.kw_coeff_pderiv, hGs,
      MvPowerSeries.coeff_map, map_nsmul]

  have hden : G.invDiffDenom = PowerSeries.map f F.invDiffDenom := by
    unfold FormalGroup.invDiffDenom
    rw [hpX, show PowerSeries.map f (MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] F.partialX) =
      MvPowerSeries.map f (MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] F.partialX) from rfl,
      MvPowerSeries.map_subst (FormalGroup.hasSubst_invDiff (R := R))]
    congr 1
    funext i; fin_cases i
    · show (0 : PowerSeries S) = MvPowerSeries.map f 0; rw [map_zero]
    · show (PowerSeries.X : PowerSeries S) = MvPowerSeries.map f PowerSeries.X
      exact (PowerSeries.map_X f).symm

  have h1 : G.invDiffDenom * PowerSeries.map f F.invDiff = 1 := by
    rw [hden, ← map_mul, FormalGroup.invDiffDenom_mul_invDiff, map_one]
  have h2 := G.invDiffDenom_mul_invDiff
  calc G.invDiff = G.invDiff * (G.invDiffDenom * PowerSeries.map f F.invDiff) := by rw [h1, mul_one]
    _ = (G.invDiffDenom * G.invDiff) * PowerSeries.map f F.invDiff := by ring
    _ = PowerSeries.map f F.invDiff := by rw [h2, one_mul]

end S_FormalGroup_IsBaseChange_invDiff_eq_map
end P2MW
export P2MW.S_FormalGroup_IsBaseChange_invDiff_eq_map (solution)
