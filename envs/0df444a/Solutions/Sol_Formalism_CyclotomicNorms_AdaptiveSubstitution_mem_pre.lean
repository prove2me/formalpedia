-- Prove2me | solution 1 for Formalism.CyclotomicNorms.AdaptiveSubstitution.mem_pre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:25.533806+00:00
-- url     : https://prove2.me/submissions/448a8a5c-9b8c-4218-b955-cb16c8aec7bc

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound
import Theorems.Thm_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.AdaptiveSubstitution
namespace Formalism.CyclotomicNorms.AdaptiveSubstitution
theorem _root_.solution (ℓ A : ℕ) (B : List ℕ → ℕ) {i n : ℕ} (h : i < n) :
    step ℓ A B (pre ℓ A B i) ∈ pre ℓ A B n := by
  rw [pre_eq ℓ A B n, List.mem_ofFn]
  exact ⟨⟨i, h⟩, rfl⟩
end Formalism.CyclotomicNorms.AdaptiveSubstitution
