-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.constantCoeff_sum_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:21.295612+00:00
-- url     : https://prove2.me/submissions/bdb6efb1-951c-4fe6-b082-73696c1b82df

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
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
theorem _root_.solution (h : IsLogPair l linv) {n : Type} [Fintype n] (c : n → K)
    {u : n → MvPowerSeries σ K} (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => constantCoeff_C_mul_l h (c j) (hu j)
end Formalism.L2.Th1.C.Pts
