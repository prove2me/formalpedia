-- Prove2me | solution 1 for GaussValuationUniqueness.ratio_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:28.108794+00:00
-- url     : https://prove2.me/submissions/7b6b089d-055c-4045-9d5d-7a44f793af0c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
namespace GaussValuationUniqueness
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  unfold ratio
  have hex : ∃ a : Ω, f = a • g := ⟨a, h⟩
  rw [dif_pos hex]
  have h2 := hex.choose_spec
  exact smul_left_injective Ω hg (h.symm.trans h2).symm
end GaussValuationUniqueness
