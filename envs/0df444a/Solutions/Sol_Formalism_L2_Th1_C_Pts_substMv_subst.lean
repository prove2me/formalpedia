-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.substMv_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:20.287152+00:00
-- url     : https://prove2.me/submissions/ff769085-c881-45d5-88b5-5adb692d56b4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_hasSubst

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution {τ : Type} [Finite σ] {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) =
      PowerSeries.subst (MvPowerSeries.subst a g) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def]
  exact MvPowerSeries.subst_comp_subst_apply (hasSubst hg).const
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f
end Formalism.L2.Th1.C.Pts
