-- Prove2me | solution 1 for Formalism.L2.Th1.C.rescale_pExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:12.419643+00:00
-- url     : https://prove2.me/submissions/5e91d8d3-3d2c-456e-adbd-b33cce3e16e6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp

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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.C
theorem _root_.solution (a : K) (f : PowerSeries K) (hf : constantCoeff f = 0) :
    rescale a (pExp f) = pExp (rescale a f) := by
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  have hX : PowerSeries.HasSubst (a • PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  show rescale a (PowerSeries.subst f (PowerSeries.exp K)) =
    PowerSeries.subst (rescale a f) (PowerSeries.exp K)
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hs hX, ← PowerSeries.rescale_eq_subst]
end Formalism.L2.Th1.C
