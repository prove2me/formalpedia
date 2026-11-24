-- Prove2me | solution 1 for Formalism.ValuationGridEstimates.lemma_u_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:08.859823+00:00
-- url     : https://prove2.me/submissions/e29f7c2b-2a1d-46a7-b49c-f13cb7e00637

import Definitions.Def_Formalism_TowerValuationBounds_HermitianSumValuationBound
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Theorems.Thm_Formalism_ValuationGridEstimates_additive_map_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ValuationGridEstimates
open Finset
namespace Formalism.ValuationGridEstimates
theorem _root_.solution : UnitQuotientValuationBound := by
  intro G _ v hv S S0 ζ Ga Ga' Gb Gb' qv c hζ ha hb
  have e1 : v (ζ * ∏ s ∈ S0, Ga s / Gb s) = ∑ s ∈ S0, (v (Ga s) - v (Gb s)) := by
    rw [hv, hζ, additive_map_prod hv, zero_add]
    exact sum_congr rfl (fun s _ => additive_map_div hv _ _)
  have key : ∀ s ∈ S0, |v (Ga s) - v (Gb s)| ≤ (c s : ℝ) * v (qv s) := by
    intro s hs
    obtain ⟨a1, a2, a3⟩ := ha s hs
    obtain ⟨b1, b2, b3⟩ := hb s hs
    have ea : v (Ga s) + v (Ga' s) = c s * v (qv s) := by rw [← hv, a3, additive_map_pow hv]
    have eb : v (Gb s) + v (Gb' s) = c s * v (qv s) := by rw [← hv, b3, additive_map_pow hv]
    rw [abs_le]; constructor <;> linarith
  have m1 : |v (ζ * ∏ s ∈ S0, Ga s / Gb s)| ≤ ∑ s ∈ S0, (c s : ℝ) * v (qv s) := by
    rw [e1]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum key)
  refine ⟨m1, m1.trans (sum_le_sum ?_)⟩
  intro s hs
  have := (abs_nonneg _).trans (key s hs)
  linarith
end Formalism.ValuationGridEstimates
