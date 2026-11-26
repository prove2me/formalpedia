-- Prove2me | solution 1 for FriedCrossing.Regularity.bound_on_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:48:52.230692+00:00
-- url     : https://prove2.me/submissions/a1981ef7-38bc-45de-8002-3f7695d1e285

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {g : ℝ → ℝ → ℝ} (hg : Continuous fun q : ℝ × ℝ => g q.1 q.2) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ τ : ℝ, |θ| < 1 → |τ| < 1 → |g θ τ| ≤ K := by
  have hK : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun θ τ hθ hτ => ?_⟩
  have hmem : ((θ, τ) : ℝ × ℝ) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    rw [abs_lt] at hθ hτ
    exact ⟨⟨hθ.1.le, hθ.2.le⟩, ⟨hτ.1.le, hτ.2.le⟩⟩
  have := hC (θ, τ) hmem
  rw [Real.norm_eq_abs] at this
  exact le_trans this (le_max_left _ _)
end FriedCrossing.Regularity
