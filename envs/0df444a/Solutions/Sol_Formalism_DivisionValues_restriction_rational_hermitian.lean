-- Prove2me | solution 1 for Formalism.DivisionValues.restriction_rational_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:03.951867+00:00
-- url     : https://prove2.me/submissions/310cc496-5c16-4f94-8a9f-e7f06baf8a2e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_map_gramMat
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_exists_restrict
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_majAt_restrict
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_hform_restrict

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
open RationalHermitianForm
open ConjugateWeightGram
namespace Formalism.DivisionValues
theorem _root_.solution : RestrictRatHerm := by
  intro K _ _ _ K0 hcm hstar n H X hH d z hzli hz
  obtain ⟨XT, hXT⟩ := exists_restrict hH z hzli
  refine ⟨XT, ⟨?_, fun v => ⟨(hXT v).1, ?_⟩⟩, fun v x y => majAt_restrict hH z XT v (hXT v).2 x y,
    hform_restrict H z⟩
  · intro a b
    simp only [gramMat, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hstar _ (hz a i))
      (Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (hH.1 i j) (hz b j))
  · rw [(hXT v).2, map_gramMat H z v.embedding fun a i => hcm _ _ (hz a i)]
end Formalism.DivisionValues
