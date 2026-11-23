-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctrDiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:33.610808+00:00
-- url     : https://prove2.me/submissions/0ec49663-aa51-483b-b9b9-f9af0dd33d5a

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_pow_mem

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
theorem _root_.solution {A B : ℕ} (j : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrDiv K k j f ∈ PolAB K k (A - j) (B - j) := by
  simp only [ctrDiv, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (ctrF_pow_mem j hf)
end Formalism.CountingSumsFrames.Har2
