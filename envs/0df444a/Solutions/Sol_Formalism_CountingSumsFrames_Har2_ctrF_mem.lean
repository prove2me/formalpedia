-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctrF_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:00.918326+00:00
-- url     : https://prove2.me/submissions/fac36a6f-8ba7-4013-a8b4-1d035bc3edc2

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inl_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_pderiv_inr_mem
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
theorem _root_.solution {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrF K k f ∈ PolAB K k (A - 1) (B - 1) := by
  rw [ctrF_apply]
  exact Submodule.sum_mem _ fun i _ => pderiv_inl_mem i (pderiv_inr_mem i hf)
end Formalism.CountingSumsFrames.Har2
