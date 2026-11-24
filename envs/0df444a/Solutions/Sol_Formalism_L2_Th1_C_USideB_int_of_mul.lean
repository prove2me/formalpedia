-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideB.int_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:04.518467+00:00
-- url     : https://prove2.me/submissions/7eb61b15-921a-4807-a8d5-71cedcd9d635

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
open USideB
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.USideB
theorem _root_.solution {R : Subring K} {U V W : PowerSeries K} (hU : IsOneUnit R U) (hW : IntPS R W)
    (h : V * U = W) : IntPS R V := by
  have h0 : PowerSeries.coeff 0 U = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hU.1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Nat.sub_self, h0, mul_one] at hc

    have hn : PowerSeries.coeff n V = PowerSeries.coeff n W -
        ∑ k ∈ Finset.range n, PowerSeries.coeff k V * PowerSeries.coeff (n - k) U := by
      rw [← hc]
      ring
    rw [hn]
    exact R.sub_mem (hW n)
      (R.sum_mem fun k hk => R.mul_mem (ih k (Finset.mem_range.1 hk)) (hU.2 _))
end Formalism.L2.Th1.C.USideB
