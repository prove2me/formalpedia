-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.cob_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.999945+00:00
-- url     : https://prove2.me/submissions/1c82a8b2-85a8-461a-84eb-78ab2a1038c8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (f g l : PowerSeries K) (a b : K) :
    cob F (f - PowerSeries.C a * g - PowerSeries.C b * l) =
      cob F f - MvPowerSeries.C a * cob F g - MvPowerSeries.C b * cob F l := by
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hx : ∀ x : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) :=
    fun x => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold cob at1
  simp only [PowerSeries.subst_sub hs, PowerSeries.subst_mul hs, PowerSeries.subst_sub (hx _),
    PowerSeries.subst_mul (hx _), PowerSeries.subst_C]
  ring
end Formalism.InvariantFactorPaths.G7.LemOne
