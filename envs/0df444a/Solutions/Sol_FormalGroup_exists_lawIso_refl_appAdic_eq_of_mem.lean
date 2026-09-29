-- Prove2me | solution 1 for FormalGroup.exists_lawIso_refl_appAdic_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7da462d1-f210-5a0a-9f79-560f604c08c8

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_lawIso_refl_appAdic_eq_of_mem

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R) :
    ∃ ψ : FormalGroup.LawIso F F, ψ.series = PowerSeries.X ∧ ∀ y ∈ I, ψ.toLawHom.appAdic I y = y := by
  classical
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hXi : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hsx : ∀ i : Fin 2, FormalGroup.LawHom.substX i (PowerSeries.X : PowerSeries R) = MvPowerSeries.X i := by
    intro i
    unfold FormalGroup.LawHom.substX
    exact PowerSeries.subst_X (hXi i)
  have hvec : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) =
      MvPowerSeries.X := by
    funext i; fin_cases i <;> rfl
  let ψ : FormalGroup.LawIso F F :=
    { series := PowerSeries.X
      constantCoeff_series := PowerSeries.constantCoeff_X
      comm := by
        rw [PowerSeries.subst_X hF, hsx, hsx, hvec, MvPowerSeries.subst_self, id]
      isUnit_coeff_one := by
        rw [PowerSeries.coeff_one_X]; exact isUnit_one }
  refine ⟨ψ, rfl, fun y _ => ?_⟩
  letI : WithIdeal R := ⟨I⟩
  show FormalGroup.evalSeries (PowerSeries.X : PowerSeries R) y = y
  unfold FormalGroup.evalSeries
  exact @PowerSeries.eval₂_X R _ R _ (algebraMap R R) y ⊥ _

end S_FormalGroup_exists_lawIso_refl_appAdic_eq_of_mem
end P2MW
export P2MW.S_FormalGroup_exists_lawIso_refl_appAdic_eq_of_mem (solution)
