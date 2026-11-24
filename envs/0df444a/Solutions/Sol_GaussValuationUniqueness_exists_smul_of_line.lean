-- Prove2me | solution 1 for GaussValuationUniqueness.exists_smul_of_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:19.186209+00:00
-- url     : https://prove2.me/submissions/29e4d02d-4cf4-4dab-9c24-4e3f453d6476

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
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {l : Submodule Ω V} (h1 : Module.finrank Ω l = 1) {f g : V} (hf : f ∈ l) (hg : g ∈ l)
    (hg0 : g ≠ 0) : ∃ a : Ω, f = a • g := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hg⟩ : l) (by simpa using hg0)).mp h1 ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have h2 := congrArg Subtype.val hc
  simpa using h2.symm
end GaussValuationUniqueness
