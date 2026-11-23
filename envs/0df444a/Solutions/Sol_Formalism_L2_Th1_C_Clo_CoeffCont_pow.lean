-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.CoeffCont.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:34.56211+00:00
-- url     : https://prove2.me/submissions/24f189b2-bcbf-4a3f-aeee-53c78078a827

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_const
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
theorem _root_.solution {f : T → MvPowerSeries σ K} (hf : CoeffCont f) (k : ℕ) :
    CoeffCont fun t => f t ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using CoeffCont.const (T := T) (1 : MvPowerSeries σ K)
  | succ k ih => simpa only [pow_succ] using ih.mul hf
end CoeffCont
end Formalism.L2.Th1.C.Clo
