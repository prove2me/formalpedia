-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvExp_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:41.249782+00:00
-- url     : https://prove2.me/submissions/3b6e2078-1f6a-45ac-ba21-790db46ca0ce

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ K)
    (hf : ∀ a ∈ s, MvPowerSeries.constantCoeff (f a) = 0) :
    mvExp (∑ a ∈ s, f a) = ∏ a ∈ s, mvExp (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero]
  | insert x s hx ih =>
    have hs : MvPowerSeries.constantCoeff (∑ a ∈ s, f a) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun b hb => hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.sum_insert hx, Finset.prod_insert hx,
      mvExp_add (hf x (Finset.mem_insert_self x s)) hs,
      ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]
end Formalism.L2.Th1.C
