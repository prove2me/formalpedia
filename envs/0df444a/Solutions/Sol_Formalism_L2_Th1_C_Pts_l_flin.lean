-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.l_flin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:32.870634+00:00
-- url     : https://prove2.me/submissions/32cc76a3-c975-4f74-8c49-f7b809bc6337

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_l_linv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_sum_l

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
    PowerSeries.subst (flin l linv c u) l =
      ∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l :=
  subst_l_linv h (constantCoeff_sum_l h c hu)
end Formalism.L2.Th1.C.Pts
