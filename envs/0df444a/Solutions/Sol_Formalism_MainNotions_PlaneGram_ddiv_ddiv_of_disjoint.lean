-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_ddiv_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:30.541914+00:00
-- url     : https://prove2.me/submissions/f15532d0-7e57-4385-94fd-a128bf557d7c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {σ : Type} [Fintype σ]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (M₁ M₂ : σ →₀ ℕ) (h : ∀ x, M₁ x = 0 ∨ M₂ x = 0)
    (F : MvPolynomial σ K) : ddiv M₁ (ddiv M₂ F) = ddiv (M₁ + M₂) F := by
  refine MvPolynomial.induction_on' F (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · have hb : (bin M₂ α : K) * bin M₁ (α - M₂) = bin (M₁ + M₂) α := by
      unfold bin
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ => ?_
      rcases h x with h1 | h2
      · simp [h1]
      · simp [h2]
    simp only [ddiv_monomial']
    rw [tsub_tsub, add_comm M₂ M₁, mul_assoc, hb]
  · simp only [ddiv_add, h₁, h₂]
end Formalism.MainNotions.PlaneGram
