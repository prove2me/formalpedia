-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.CoeffCont.subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:48:48.3918+00:00
-- url     : https://prove2.me/submissions/44378419-0280-450e-8554-74ac945f29cd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_coeff_subst_range
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_mul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_pow

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
theorem _root_.solution {f : T → MvPowerSeries σ K} (hf : CoeffCont f)
    (h0 : ∀ t, MvPowerSeries.constantCoeff (f t) = 0) (g : PowerSeries K) :
    CoeffCont fun t => PowerSeries.subst (f t) g := fun n => by
  simp only [coeff_subst_range (h0 _)]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hf.pow k n)
end CoeffCont
end Formalism.L2.Th1.C.Clo
