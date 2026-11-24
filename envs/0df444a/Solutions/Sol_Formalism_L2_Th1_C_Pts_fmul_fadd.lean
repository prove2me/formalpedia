-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.fmul_fadd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:45.456935+00:00
-- url     : https://prove2.me/submissions/e8c314dd-1d0c-4d82-800c-f1a17ac3f22a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_l_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_l_fmul

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
theorem _root_.solution (h : IsLogPair l linv) (a : K) {x y : MvPowerSeries σ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    fmul l linv a (fadd l linv x y) = fadd l linv (fmul l linv a x) (fmul l linv a y) := by
  rw [fmul, l_fadd h hx hy, fadd, l_fmul h a hx, l_fmul h a hy, mul_add]
end Formalism.L2.Th1.C.Pts
