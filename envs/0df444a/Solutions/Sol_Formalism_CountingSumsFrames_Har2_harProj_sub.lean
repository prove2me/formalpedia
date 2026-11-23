-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harProj_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:44.133271+00:00
-- url     : https://prove2.me/submissions/96fec5fa-e0c6-4810-b14c-96fb78e726b9

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_pow_mul_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_pow_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_cPoint_zero
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
    ∃ g ∈ PolAB K k (A - 1) (B - 1), f - harProj K k A B f = hXY K k * g := by
  have h1 := min_le_left A B
  have h2 := min_le_right A B
  refine ⟨-∑ l ∈ range (min A B), cP K (A + B + k - 2) (l + 1) • (hXY K k ^ l * (ctrF K k ^ (l + 1)) f),
    ?_, ?_⟩
  · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_)
    have hl' := Finset.mem_range.1 hl
    have := h_pow_mul_mem l (ctrF_pow_mem (l + 1) hf)
    rwa [show A - (l + 1) + l = A - 1 by omega, show B - (l + 1) + l = B - 1 by omega] at this
  · rw [harProj_apply, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Module.End.one_apply, cPoint_zero, one_smul, mul_neg, Finset.mul_sum,
      mul_smul_comm, ← mul_assoc, ← pow_succ']
    abel
end Formalism.CountingSumsFrames.Har2
