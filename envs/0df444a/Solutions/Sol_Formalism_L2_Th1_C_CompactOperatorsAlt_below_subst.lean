-- Prove2me | solution 1 for Formalism.L2.Th1.C.CompactOperatorsAlt.below_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:22:06.19671+00:00
-- url     : https://prove2.me/submissions/536c7dea-38f6-4abe-b083-1985e8d4bcf3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_pow_mem


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
theorem _root_.solution {n : ℕ} {A a : PowerSeries K} (hA : IntPS R A)
    (ha0 : constantCoeff a = 0) (ha : ∀ m < n, coeff m a ∈ R) :
    ∀ m < n, coeff m (A.subst a) ∈ R := by
  intro m hm
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' ha0)]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun k => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hA k) (Pts.coeff_pow_mem ha k m hm)
end Formalism.L2.Th1.C.CompactOperatorsAlt
