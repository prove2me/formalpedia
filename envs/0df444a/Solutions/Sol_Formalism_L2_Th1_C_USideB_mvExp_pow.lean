-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideB.mvExp_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:07.066796+00:00
-- url     : https://prove2.me/submissions/380fd489-282b-49d3-9c03-6ef1515888ec

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB

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
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.C.USideB
theorem _root_.solution (hE : MvExpLaws) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0)
    (m : ℕ) : (mvExp f : PowerSeries K) ^ m = mvExp ((m : K) • f) := by
  obtain ⟨L0, -, L2, -⟩ := hE K Unit
  induction m with
  | zero => simp [L0]
  | succ m ih =>
    have hc : PowerSeries.constantCoeff ((m : K) • f) = 0 := by simp [hf]
    rw [pow_succ, ih, ← L2 _ _ hc hf]
    congr 1
    push_cast
    rw [add_smul, one_smul]
end Formalism.L2.Th1.C.USideB
