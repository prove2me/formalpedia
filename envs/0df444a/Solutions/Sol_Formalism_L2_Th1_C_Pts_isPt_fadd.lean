-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.isPt_fadd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:30.974863+00:00
-- url     : https://prove2.me/submissions/61424097-1cb0-498a-93e0-47fdab6c7c10

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_eq_substMv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_substMv


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
theorem _root_.solution (h : IsLogPair l linv) (hF : FGInt R l linv) {x y : MvPowerSeries σ K}
    (hx : IsPt R x) (hy : IsPt R y) : IsPt R (fadd l linv x y) := by
  refine ⟨constantCoeff_fadd h hx.1 hy.1, ?_⟩
  rw [fadd_eq_substMv h hx.1 hy.1]
  refine intMv_substMv hF fun s => ?_
  fin_cases s
  · exact hx
  · exact hy
end Formalism.L2.Th1.C.Pts
