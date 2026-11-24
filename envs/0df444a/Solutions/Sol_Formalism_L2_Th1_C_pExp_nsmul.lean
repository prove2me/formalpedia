-- Prove2me | solution 1 for Formalism.L2.Th1.C.pExp_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:08.234532+00:00
-- url     : https://prove2.me/submissions/b8408c51-949c-4aac-95df-1840eb116db0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
import Theorems.Thm_Formalism_L2_Th1_C_pExp_zero
import Theorems.Thm_Formalism_L2_Th1_C_pExp_add

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
theorem _root_.solution (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) (k : ℕ) :
    pExp (k • f) = pExp f ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, pExp_zero hE]
  | succ k ih =>
    have hk : constantCoeff (k • f) = 0 := by rw [map_nsmul, hf, smul_zero]
    rw [succ_nsmul, pExp_add hE _ _ hk hf, ih, pow_succ]
end Formalism.L2.Th1.C
