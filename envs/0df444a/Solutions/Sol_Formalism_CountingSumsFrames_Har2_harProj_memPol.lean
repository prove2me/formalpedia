-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harProj_memPol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:33.991802+00:00
-- url     : https://prove2.me/submissions/1dc8529b-46bb-4f19-93e1-624bd30a6b18

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_pow_mul_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_pow_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_apply

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
    harProj K k A B f ∈ PolAB K k A B := by
  rw [harProj_apply]
  refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
  have hl' := Finset.mem_range.1 hl
  have h1 := min_le_left A B
  have h2 := min_le_right A B
  have := h_pow_mul_mem l (ctrF_pow_mem l hf)
  rwa [Nat.sub_add_cancel (by omega : l ≤ A), Nat.sub_add_cancel (by omega : l ≤ B)] at this
end Formalism.CountingSumsFrames.Har2
