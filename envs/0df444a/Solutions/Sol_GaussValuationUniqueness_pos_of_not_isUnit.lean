-- Prove2me | solution 1 for GaussValuationUniqueness.pos_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:26.922072+00:00
-- url     : https://prove2.me/submissions/25a45f02-bf4d-490a-8af6-17f516ff7bca

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
theorem _root_.solution {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ))
    (x : vRing v) (hx : ¬ IsUnit x) : 0 < v (x : Ω) := by
  have h0 : 0 ≤ v (x : Ω) := x.2
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hx0 : (x : Ω) ≠ 0 := by
      intro h'
      rw [h', AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h.symm
    have hinv : (x : Ω)⁻¹ ∈ vRing v := by
      show 0 ≤ v ((x : Ω)⁻¹)
      rw [AddValuation.map_inv, ← h, neg_zero]
    exact ⟨⟨x, ⟨(x : Ω)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩
end GaussValuationUniqueness
