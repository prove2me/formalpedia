-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:50.281721+00:00
-- url     : https://prove2.me/submissions/5922b3c3-53ee-450f-8730-af47814f78c8

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (A B : ℕ) (f : PolXY K k) : harProj K k A B f =
    ∑ l ∈ range (min A B + 1), cP K (A + B + k - 2) l • (hXY K k ^ l * (ctrF K k ^ l) f) := by
  unfold harProj
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, hDiv, ctrDiv, LinearMap.mulLeft_apply,
    mul_smul_comm, smul_smul, cP]
  all_goals (congr 1; ring)
end Formalism.CountingSumsFrames.Har2
