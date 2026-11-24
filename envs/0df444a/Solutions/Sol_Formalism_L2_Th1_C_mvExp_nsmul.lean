-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvExp_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:17.171465+00:00
-- url     : https://prove2.me/submissions/b9fc927e-7cdd-43e1-a93e-358c3ad52c44

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_zero
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_add

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
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (n : ℕ) :
    mvExp (n • f) = mvExp f ^ n := by
  induction n with
  | zero => simp [mvExp_zero]
  | succ n ih => rw [succ_nsmul, mvExp_add (by simp [hf]) hf, ih, pow_succ]
end Formalism.L2.Th1.C
