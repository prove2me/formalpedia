-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.finrank_T_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:20:17.113334+00:00
-- url     : https://prove2.me/submissions/c4be1258-0667-45dd-a357-365197b80647

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_WeightCompositions_coordWt_to_coordKWt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
universe u
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.WeightCompositions
variable {N n : ℕ}
variable {K : Type u} [Field K] (ν : Fin N → ℕ)
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution (k : Fin n) (i : ℕ) (w : Fin n → ℕ) :
    Module.finrank K ↥((H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) ⊓
        weightedHomogeneousSubmodule K (coordWt N n) w) =
      if w k = i then Dw K ν w else 0 := by
  split_ifs with h
  · have heq : (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) ⊓
        weightedHomogeneousSubmodule K (coordWt N n) w =
        H K ν ⊓ weightedHomogeneousSubmodule K (coordWt N n) w := by
      apply le_antisymm
      · exact inf_le_inf_right _ inf_le_left
      · intro F hF
        rw [Submodule.mem_inf] at hF
        rw [Submodule.mem_inf, Submodule.mem_inf]
        exact ⟨⟨hF.1, h ▸ coordWt_to_coordKWt k hF.2⟩, hF.2⟩
    rw [heq]
    rfl
  · have heq : (H K ν ⊓ weightedHomogeneousSubmodule K (coordKWt N n k) i) ⊓
        weightedHomogeneousSubmodule K (coordWt N n) w = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro F hF
      by_contra hne
      rw [Submodule.mem_inf, Submodule.mem_inf] at hF
      apply h
      exact IsWeightedHomogeneous.inj_right hne (coordWt_to_coordKWt k hF.2) hF.1.2
    rw [heq]
    simp
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
