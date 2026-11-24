-- Prove2me | solution 1 for Formalism.L2.Th1.C.isogenyIffBar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:47.169487+00:00
-- url     : https://prove2.me/submissions/4d224c22-91b4-4cbb-8c25-6300d6f56f98

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
import Theorems.Thm_Formalism_L2_Th1_C_isogenyIff_of

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
namespace Formalism.L2.Th1.C
theorem _root_.solution (hE : MvExpLaws) : IsogenyIffBar := by
  intro K _ _ e s2 ι _ neg xP c0 w al albar hal hbar hendo
  rw [isogenyIff_of hE K e s2 ι neg (fun P => xP P + c0) w al hal hendo, ← hbar]
  constructor <;> intro h <;> linear_combination h
end Formalism.L2.Th1.C
