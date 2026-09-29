-- Prove2me | solution 1 for FormalGroup.IsBaseChange.nthSeries_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3c2aec37-113f-5959-8214-dfb2155642bd

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsBaseChange_nthSeries_eq_map

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S)
    (h : F.IsBaseChange f G) (n : ℕ) :
    G.nthSeries n = PowerSeries.map f (F.nthSeries n) := by
  induction n with
  | zero => simp [FormalGroup.nthSeries_zero]
  | succ n ih =>
    rw [FormalGroup.nthSeries_succ, FormalGroup.nthSeries_succ, ih]
    unfold FormalGroup.IsBaseChange at h
    rw [h]
    have e1 : ∀ p : PowerSeries R, PowerSeries.map f p = MvPowerSeries.map f p := fun p => rfl
    have hv : (fun i => MvPowerSeries.map f
        ((![F.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R) i)) =
        ![MvPowerSeries.map f (F.nthSeries n), PowerSeries.X] := by
      funext i
      fin_cases i
      · rfl
      · show MvPowerSeries.map f PowerSeries.X = PowerSeries.X
        exact PowerSeries.map_X f
    simp only [e1]
    rw [MvPowerSeries.map_subst (F.hasSubst_nthSeries n), hv]

end S_FormalGroup_IsBaseChange_nthSeries_eq_map
end P2MW
export P2MW.S_FormalGroup_IsBaseChange_nthSeries_eq_map (solution)
