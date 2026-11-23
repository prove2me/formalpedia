-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:32.996088+00:00
-- url     : https://prove2.me/submissions/6ecacb94-b9f5-4dc8-9ca8-0e61dcbadc26

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_coeff_mvExp

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
theorem _root_.solution : mvExp (0 : MvPowerSeries σ K) = 1 := by
  classical
  ext n
  rw [coeff_mvExp (map_zero _) (Nat.lt_succ_self n.degree), Finset.sum_range_succ']
  simp
end Formalism.L2.Th1.C
