-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_inf_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:24.478181+00:00
-- url     : https://prove2.me/submissions/e6d8c047-7633-4601-b348-ba0b01ec1c54

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_exists_smul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength
variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
namespace Formalism.LatticeIndexTer.LatticeIndexLength
theorem _root_.solution (P Q₁ Q₂ Q₃ : Submodule O X) (hP : P.FG)
    (h₁ : Submodule.span K (Q₁ : Set X) = ⊤) (h₂ : Submodule.span K (Q₂ : Set X) = ⊤)
    (h₃ : Submodule.span K (Q₃ : Set X) = ⊤) :
    ∃ d : O, d ≠ 0 ∧ ∀ p ∈ P, d • p ∈ Q₁ ⊓ Q₂ ⊓ Q₃ := by
  obtain ⟨d₁, hd₁, e₁⟩ := exists_smul_le P Q₁ hP h₁
  obtain ⟨d₂, hd₂, e₂⟩ := exists_smul_le P Q₂ hP h₂
  obtain ⟨d₃, hd₃, e₃⟩ := exists_smul_le P Q₃ hP h₃
  refine ⟨d₁ * d₂ * d₃, mul_ne_zero (mul_ne_zero hd₁ hd₂) hd₃, fun p hp => ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show d₁ * d₂ * d₃ = (d₂ * d₃) * d₁ by ring, mul_smul]; exact Q₁.smul_mem _ (e₁ p hp)
  · rw [show d₁ * d₂ * d₃ = (d₁ * d₃) * d₂ by ring, mul_smul]; exact Q₂.smul_mem _ (e₂ p hp)
  · rw [mul_smul]; exact Q₃.smul_mem _ (e₃ p hp)
end Formalism.LatticeIndexTer.LatticeIndexLength
