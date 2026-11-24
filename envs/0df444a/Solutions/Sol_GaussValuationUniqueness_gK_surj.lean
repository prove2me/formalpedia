-- Prove2me | solution 1 for GaussValuationUniqueness.gK_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:20.709803+00:00
-- url     : https://prove2.me/submissions/0ba83b44-fc1f-40e2-8090-79548d51d28d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_NotInjOfTrdeg

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
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))
namespace GaussValuationUniqueness
theorem _root_.solution (hv : IsTrivOn K v) : Function.Surjective (gK v hv) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨x.1, rfl⟩
end GaussValuationUniqueness
