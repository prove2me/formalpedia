-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.cc_fmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:52.303253+00:00
-- url     : https://prove2.me/submissions/e3ebc073-f966-48cd-b475-0935a46d2252

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_C_mul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {σ : Type}
variable [TopologicalSpace K] [IsTopologicalRing K] {T : Type} [TopologicalSpace T]
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution {l linv : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hli : PowerSeries.constantCoeff linv = 0) (a : K) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (fmul l linv a y) = 0 :=
  Pts.constantCoeff_subst (cc_C_mul (Pts.constantCoeff_subst hy hl) a) hli
end Formalism.L2.Th1.C.Clo
