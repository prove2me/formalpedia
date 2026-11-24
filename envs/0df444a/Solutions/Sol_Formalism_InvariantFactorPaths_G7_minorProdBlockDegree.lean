-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.minorProdBlockDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:46:35.952994+00:00
-- url     : https://prove2.me/submissions/f02ba94c-d7e2-4de5-a031-a6a8f0239127

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_weight_posWt
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_minorAt_posWt

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : MinorProdDegree := by
  intro K σ _ _ r0 r1 C l sf T I n hn s
  have hH := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun c => minorAt (sf c) (T c) (I c)) (fun c => if sf c = s then l c else 0)
    (w := posWt r0 r1 s) (fun c _ => minorAt_posWt s (sf c) (T c) (I c))
  have h := hH (MvPolynomial.mem_support_iff.mp hn)
  rw [weight_posWt] at h
  rw [h, Finset.sum_filter]
end Formalism.InvariantFactorPaths.G7
