-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.fmul_eq_subst_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:09.250235+00:00
-- url     : https://prove2.me/submissions/ca9dc617-5fee-478d-a970-9bb103c3124a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_hasSubst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_subst

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
    fmul l linv a x = PowerSeries.subst x (mulBy l linv a) := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C a * l) = 0 := by rw [map_mul, h.1, mul_zero]
  rw [mulBy, subst_subst h0 hx, PowerSeries.subst_mul (hasSubst hx), PowerSeries.subst_C, fmul]
end Formalism.L2.Th1.C.Pts
