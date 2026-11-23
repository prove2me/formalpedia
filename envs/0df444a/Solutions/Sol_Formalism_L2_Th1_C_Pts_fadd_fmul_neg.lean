-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.fadd_fmul_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:32.129451+00:00
-- url     : https://prove2.me/submissions/ae48f67c-b774-40dd-bea7-c107a5ee68f3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_zero_left
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_add

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
    fadd l linv (fmul l linv a x) (fmul l linv (-a) x) = 0 := by
  rw [← fmul_add h a (-a) hx, add_neg_cancel, fmul_zero_left h]
end Formalism.L2.Th1.C.Pts
