-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvExp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:18.068244+00:00
-- url     : https://prove2.me/submissions/21d47554-5f5c-4953-a70b-6e696322d57e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
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
theorem _root_.solution {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f - g) = mvExp f * mvExp (-g) := by
  rw [sub_eq_add_neg]
  exact mvExp_add hf (by simp [hg])
end Formalism.L2.Th1.C
