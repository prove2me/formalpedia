-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.constantCoeff_fmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:31.222111+00:00
-- url     : https://prove2.me/submissions/7b2365e9-64af-4768-a0af-38ff49f1fb09

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst_linv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_C_mul_l

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
theorem _root_.solution (h : IsLogPair l linv) (a : K) {x : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (fmul l linv a x) = 0 :=
  constantCoeff_subst_linv h (constantCoeff_C_mul_l h a hx)
end Formalism.L2.Th1.C.Pts
