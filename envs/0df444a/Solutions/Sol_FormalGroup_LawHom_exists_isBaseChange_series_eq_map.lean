-- Prove2me | solution 1 for FormalGroup.LawHom.exists_isBaseChange_series_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e8652d3e-cb87-53f9-80ea-5dfc03bc68da

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_LawHom_exists_isBaseChange_series_eq_map

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem solution
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {F G : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (F' G' : FormalGroup S)
    (hF : F.IsBaseChange f F') (hG : G.IsBaseChange f G') :
    ∃ θ' : FormalGroup.LawHom F' G', θ'.series = PowerSeries.map f θ.series := by
  have hθF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hcX : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      ((![FormalGroup.LawHom.substX 0 θ.series, FormalGroup.LawHom.substX 1 θ.series] :
        Fin 2 → MvPowerSeries (Fin 2) R) i) = 0 := by
    intro i
    fin_cases i <;>
      exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ θ.constantCoeff_series
  have hX : MvPowerSeries.HasSubst
      (![FormalGroup.LawHom.substX 0 θ.series, FormalGroup.LawHom.substX 1 θ.series] :
        Fin 2 → MvPowerSeries (Fin 2) R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcX
  refine ⟨⟨PowerSeries.map f θ.series, ?_, ?_⟩, rfl⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, θ.constantCoeff_series, map_zero]
  · unfold FormalGroup.IsBaseChange at hF hG
    rw [hF, hG, ← PowerSeries.map_subst hθF, θ.comm, MvPowerSeries.map_subst hX]
    congr 1
    funext i
    fin_cases i <;>
      simp [FormalGroup.LawHom.substX, PowerSeries.map_subst (PowerSeries.HasSubst.X _), MvPowerSeries.map_X]

end S_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
end P2MW
export P2MW.S_FormalGroup_LawHom_exists_isBaseChange_series_eq_map (solution)
