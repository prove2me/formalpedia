-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvExp_smul_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:30.320804+00:00
-- url     : https://prove2.me/submissions/4e247709-816f-415a-a61b-e3ad164e3503

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_nsmul

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
    mvExp ((n : K) • f) = mvExp f ^ n := by
  rw [Nat.cast_smul_eq_nsmul]
  exact mvExp_nsmul hf n
end Formalism.L2.Th1.C
