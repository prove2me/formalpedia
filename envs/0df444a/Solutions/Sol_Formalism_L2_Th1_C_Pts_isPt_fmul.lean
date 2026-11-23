-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.isPt_fmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:30.928904+00:00
-- url     : https://prove2.me/submissions/e542bf96-e4b1-42fd-bfb7-321aea9326ba

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_eq_subst_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_subst


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
theorem _root_.solution (h : IsLogPair l linv) {a : K} (ha : EndInt R l linv a) {x : MvPowerSeries σ K}
    (hx : IsPt R x) : IsPt R (fmul l linv a x) := by
  refine ⟨constantCoeff_fmul h a hx.1, ?_⟩
  rw [fmul_eq_subst_mulBy h a hx.1]
  exact intMv_subst ha hx
end Formalism.L2.Th1.C.Pts
