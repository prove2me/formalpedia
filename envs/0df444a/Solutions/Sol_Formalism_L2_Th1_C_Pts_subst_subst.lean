-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.subst_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:05.33178+00:00
-- url     : https://prove2.me/submissions/d657c778-9efb-4056-aeb2-0f8366760f91

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
theorem _root_.solution {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0)
    {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) (f : PowerSeries K) :
    PowerSeries.subst x (PowerSeries.subst g f) = PowerSeries.subst (PowerSeries.subst x g) f :=
  PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
    (hasSubst hx) f
end Formalism.L2.Th1.C.Pts
