-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_eq_sum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:21.559298+00:00
-- url     : https://prove2.me/submissions/b2031900-a7a0-490d-ab99-83647aacad7c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight

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
variable {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : ∀ α, F.coeff α ≠ 0 → G.coeff α ≠ 0 → α ∈ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by
  classical
  unfold fock
  have h1 : ∑ α ∈ F.support, F.coeff α * G.coeff α * (fact α : K) =
      ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro α _ hα
    rw [notMem_support_iff.mp hα]; simp
  have h2 : ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) =
      ∑ α ∈ F.support ∪ s, F.coeff α * G.coeff α * (fact α : K) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro α _ hα
    by_cases hF : F.coeff α = 0
    · rw [hF]; simp
    · by_cases hG : G.coeff α = 0
      · rw [hG]; simp
      · exact absurd (h α hF hG) hα
  rw [h1, h2]
end Formalism.MainNotions.PlaneGram
