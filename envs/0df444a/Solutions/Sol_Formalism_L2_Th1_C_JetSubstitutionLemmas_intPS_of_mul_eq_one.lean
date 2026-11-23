-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.intPS_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:28.430585+00:00
-- url     : https://prove2.me/submissions/1839a627-eacd-421c-a1f8-b426824b0c13

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG

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
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K]
variable {R : Subring K}
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {U V : PowerSeries K} (hU : IntPS R U)
    (hU0 : PowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntPS R V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1 := congrArg (PowerSeries.coeff n) hUV
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ'] at h1
    simp only [Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, one_mul] at h1
    have hrest : ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) V ∈ R :=
      sum_mem fun k hk => mul_mem (hU _) (ih _ (by have := Finset.mem_range.mp hk; omega))
    have h1' : PowerSeries.coeff n V = PowerSeries.coeff n (1 : PowerSeries K) -
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) V := by
      rw [← h1]
      ring
    rw [h1']
    refine sub_mem ?_ hrest
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact one_mem R
    · exact zero_mem R
end Formalism.L2.Th1.C.JetSubstitutionLemmas
