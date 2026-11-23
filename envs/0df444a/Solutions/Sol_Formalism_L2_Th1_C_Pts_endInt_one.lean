-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.endInt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:31.279569+00:00
-- url     : https://prove2.me/submissions/556b6b96-f377-4760-bca2-c86861da3d79

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_one
import Theorems.Thm_Formalism_L2_Th1_C_Pts_mulBy_eq_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_intMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_X

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
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution (h : IsLogPair l linv) : EndInt R l linv 1 := by
  unfold EndInt
  rw [mulBy_eq_fmul, fmul_one h PowerSeries.constantCoeff_X]
  exact intPS_of_intMv isPt_X.2
end Formalism.L2.Th1.C.Pts
