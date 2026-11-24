-- Prove2me | solution 1 for Formalism.L2.Th1.C.CompactOperatorsAlt.below_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:22:03.668799+00:00
-- url     : https://prove2.me/submissions/ea48b12f-9a80-467a-8767-3f9de3b4aff2

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
theorem _root_.solution {n : ℕ} {f h : PowerSeries K} (hf : ∀ m < n, coeff m f ∈ R)
    (hh : ∀ m < n, coeff m h ∈ R) : ∀ m < n, coeff m (f * h) ∈ R := by
  intro m hm
  rw [PowerSeries.coeff_mul]
  refine Subring.sum_mem _ fun p hp => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact R.mul_mem (hf _ (by omega)) (hh _ (by omega))
end Formalism.L2.Th1.C.CompactOperatorsAlt
