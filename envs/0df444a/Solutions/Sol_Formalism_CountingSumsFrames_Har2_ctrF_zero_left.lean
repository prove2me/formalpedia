-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctrF_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:01.780535+00:00
-- url     : https://prove2.me/submissions/de543ad5-e20f-46fe-8f22-7f21f0d23599

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inr_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inl_zero
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_apply

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
theorem _root_.solution {B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k 0 B) : ctrF K k f = 0 := by
  rw [ctrF_apply]
  exact Finset.sum_eq_zero fun i _ => pderiv_inl_zero i (pderiv_inr_mem i hf)
end Formalism.CountingSumsFrames.Har2
