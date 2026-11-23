-- Prove2me | solution 1 for Formalism.DivisionValues.projection_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:40.120494+00:00
-- url     : https://prove2.me/submissions/c10979ea-b526-43b7-a076-c4990bf397e4

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : ProjIntegral := by
  intro K _ _ _ n G0 _ r c G hc B hB x hx
  choose a ha using hc
  have hs : ∀ s (w : Fin n → K), a s • w = ((a s : K)) • w := fun s w => (algebraMap_smul K (a s) w).symm
  have hsum : (∑ s, c s • r s).mulVec x = ∑ s, c s • (r s).mulVec x := by
    have h := map_sum (Matrix.mulVec.addMonoidHomLeft x) (fun s => c s • r s) Finset.univ
    change (∑ s, c s • r s).mulVec x = ∑ s, (c s • r s).mulVec x at h
    rw [h]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Nat.cast_smul_eq_nsmul, hsum, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← ha s, ← hs]
  exact B.smul_mem (a s) (hB s x hx)
end Formalism.DivisionValues
