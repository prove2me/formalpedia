-- Prove2me | solution 1 for Formalism.G0.TopsChoiceProbabilityLemmas.partB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:15:24.126264+00:00
-- url     : https://prove2.me/submissions/beb6d3ed-123f-4ff3-8b44-e67f0c3764f4

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_P_nonneg
import Theorems.Thm_Formalism_G0_TopsChoiceProbabilityLemmas_tiles_bound
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_P_mono
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityWindows_prob_exists_le_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows
namespace Formalism.G0.TopsChoiceProbabilityLemmas
theorem _root_.solution {n : ℕ} {δ : ℝ} {r u M₀ i₀ : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondTiles n (insert i₀ t) r u M₀) ≤
      n * (1 - markedBound δ r u) ^ M₀ := by
  classical
  have hℓpos : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) (by omega)
  have hM : M₀ + 1 ≤ n / ((6 * r + 1) * u) := (Nat.le_div_iff_mul_le hℓpos).2 hn
  have hX : ∀ s₀ ∈ range (n / ((6 * r + 1) * u)), P ((range n).erase i₀) δ (fun t => ∀ j ≤ M₀,
      ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))) ≤
      (1 - markedBound δ r u) ^ M₀ :=
    fun s₀ hs => tiles_bound h0 h1 hu hn s₀ (mem_range.1 hs)
  have hX0 : 0 ≤ (1 - markedBound δ r u) ^ M₀ :=
    le_trans (P_nonneg h0 h1 _) (hX 0 (mem_range.2 (by omega)))
  calc _ ≤ ∑ s₀ ∈ range (n / ((6 * r + 1) * u)), P ((range n).erase i₀) δ (fun t => ∀ j ≤ M₀,
        ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))) := by
        refine le_trans (P_mono h0 h1 ?_) (prob_exists_le_sum h0 h1 (range (n / ((6 * r + 1) * u)))
          (fun s₀ t => ∀ j ≤ M₀, ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))))
        intro t _ h
        unfold CondTiles at h
        push Not at h
        obtain ⟨s₀, hs, h⟩ := h
        exact ⟨s₀, mem_range.2 hs, h⟩
    _ ≤ ∑ s₀ ∈ range (n / ((6 * r + 1) * u)), (1 - markedBound δ r u) ^ M₀ := sum_le_sum hX
    _ = ((n / ((6 * r + 1) * u) : ℕ) : ℝ) * (1 - markedBound δ r u) ^ M₀ := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ n * (1 - markedBound δ r u) ^ M₀ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self n _) hX0
end Formalism.G0.TopsChoiceProbabilityLemmas
