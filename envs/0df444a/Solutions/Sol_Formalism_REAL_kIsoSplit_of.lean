-- Prove2me | solution 1 for Formalism.REAL.kIsoSplit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:06.676647+00:00
-- url     : https://prove2.me/submissions/5eb81ea2-7fbf-4d9d-863d-ff7c887fe4d9

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Theorems.Thm_Formalism_REAL_compactSpan_le_isotypicPart
import Theorems.Thm_Formalism_REAL_isotypicPart_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hd : KDecomp) (ho : KOrth) : KIsoSplit := by
  intro V _ _ n ε F S T hfin hr hu hS
  constructor
  · have h : isoPart ε F T S ⟂ isoPart ε F Tᶜ S := by
      unfold isoPart
      rw [Submodule.isOrtho_iSup_left]; intro y
      rw [Submodule.isOrtho_iSup_left]; rintro ⟨_, μ, hμT, hyμ⟩
      rw [Submodule.isOrtho_iSup_right]; intro z
      rw [Submodule.isOrtho_iSup_right]; rintro ⟨_, ν, hνT, hzν⟩
      rw [Submodule.isOrtho_iff_inner_eq]
      exact ho V n ε F μ ν y z hr hu hyμ hzν (fun h => hνT (h ▸ hμT))
    exact Submodule.isOrtho_iff_inner_eq.1 h
  · obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
    apply le_antisymm
    · exact sup_le (isotypicPart_le ε F T S hS) (isotypicPart_le ε F Tᶜ S hS)
    · conv_lhs => rw [← h3]
      refine iSup_le fun i => ?_
      by_cases hi : μ i ∈ T
      · exact le_sup_of_le_left (compactSpan_le_isotypicPart ε F T S (h1 i).1 hi (h1 i).2.2)
      · exact le_sup_of_le_right (compactSpan_le_isotypicPart ε F Tᶜ S (h1 i).1 hi (h1 i).2.2)
end Formalism.REAL
