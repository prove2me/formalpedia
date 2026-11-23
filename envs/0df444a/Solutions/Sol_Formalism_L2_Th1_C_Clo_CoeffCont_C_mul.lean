-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.CoeffCont.C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:33.835365+00:00
-- url     : https://prove2.me/submissions/c1e670f7-02d1-4cbd-9eec-082e14a2094a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_mul

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
namespace CoeffCont
theorem _root_.solution {c : T → K} (hc : Continuous c) {f : T → MvPowerSeries σ K}
    (hf : CoeffCont f) : CoeffCont fun t => MvPowerSeries.C (c t) * f t := fun n => by
  simp only [MvPowerSeries.coeff_C_mul]
  exact hc.mul (hf n)
end CoeffCont
end Formalism.L2.Th1.C.Clo
