-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.ga_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:13.580816+00:00
-- url     : https://prove2.me/submissions/84d2dc16-a126-4eec-b424-f487935d5d87

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
theorem _root_.solution {ι κ : Type*} (W : Finset ι) (below : ι → ℕ) (l : ι → ℝ) (Ps : Finset ℕ)
    (J : Finset κ) (gainW : κ → ι → ℝ) (tauW : ι → ℝ) (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ)
    (h : UnitRule W below l Ps J gainW tauW gain tau) :
    GaW W J l gainW tauW = ∑ p ∈ Ps, 2 * Real.log p * ((∑ j ∈ J, gain j p) - tau p) := by
  unfold GaW
  rw [← Finset.sum_filter_add_sum_filter_not W (fun w => below w ∈ Ps)]
  have hoff : ∑ w ∈ W.filter (fun w => ¬ below w ∈ Ps), l w * ((∑ j ∈ J, gainW j w) - tauW w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hg, ht⟩ := h.offPs w hw.1 hw.2
    rw [Finset.sum_eq_zero hg, ht]; ring
  have hon : ∑ w ∈ W.filter (fun w => below w ∈ Ps), l w * ((∑ j ∈ J, gainW j w) - tauW w)
      = ∑ w ∈ W.filter (fun w => below w ∈ Ps),
          l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hg, ht⟩ := h.onPs w hw.1 hw.2
    rw [Finset.sum_congr rfl hg, ht]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := W.filter (fun w => below w ∈ Ps)) (t := Ps)
      (g := below) (fun w hw => (Finset.mem_filter.1 hw).2)
      (fun w => l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)))
  rw [hoff, add_zero, hon, ← hfib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hset : (W.filter (fun w => below w ∈ Ps)).filter (fun w => below w = p) =
      W.filter (fun w => below w = p) := by
    ext w; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨hw, _⟩, he⟩; exact ⟨hw, he⟩
    · rintro ⟨hw, he⟩; exact ⟨⟨hw, he ▸ hp⟩, he⟩
  rw [hset]
  have hc : ∑ w ∈ W.filter (fun w => below w = p),
      l w * ((∑ j ∈ J, gain j (below w)) - tau (below w)) =
      ∑ w ∈ W.filter (fun w => below w = p), l w * ((∑ j ∈ J, gain j p) - tau p) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [(Finset.mem_filter.1 hw).2]
  rw [hc, ← Finset.sum_mul, h.unit p hp]; ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
