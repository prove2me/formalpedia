-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.endInt_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:00.82856+00:00
-- url     : https://prove2.me/submissions/c44d5a32-770c-4709-bd05-871b6d782145

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_one
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_Pts_mulBy_eq_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_fmul_neg
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_eq_substMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_law_of_zero
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_law_eq_zero

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
theorem _root_.solution (h : IsLogPair l linv) (hF : FGInt R l linv) : EndInt R l linv (-1) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  refine intPS_of_law_eq_zero hF (coeff_law_of_zero h) (constantCoeff_mulBy h (-1)) ?_
  rw [← fadd_eq_substMv h hX (constantCoeff_mulBy h (-1)), mulBy_eq_fmul]
  have := fadd_fmul_neg h 1 hX
  rwa [fmul_one h hX] at this
end Formalism.L2.Th1.C.Pts
