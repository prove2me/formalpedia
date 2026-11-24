-- Prove2me | solution 1 for Formalism.L2.Th1.C.CompactOperatorsAlt.below_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:22:05.101875+00:00
-- url     : https://prove2.me/submissions/8c37146f-6d4f-4495-86b5-4b69a81bbb61

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum

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
open Formalism.L2.Th1.C.CompactOperatorsAlt
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.CompactOperatorsAlt
theorem _root_.solution {n : ℕ} {g : PowerSeries K} {al : K} (hal : al ∈ R)
    (hg : ∀ m < n, coeff m g ∈ R) : ∀ m < n + 1, coeff m (C al * X * g) ∈ R := by
  intro m hm
  have h : C al * X * g = X * (C al * g) := by ring
  rw [h]
  cases m with
  | zero => rw [coeff_zero_X_mul]; exact R.zero_mem
  | succ m => rw [coeff_succ_X_mul, coeff_C_mul]; exact R.mul_mem hal (hg m (by omega))
end Formalism.L2.Th1.C.CompactOperatorsAlt
