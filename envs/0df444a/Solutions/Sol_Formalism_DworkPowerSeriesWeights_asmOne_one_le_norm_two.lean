-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmOne_one_le_norm_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:12.394243+00:00
-- url     : https://prove2.me/submissions/8975c276-f96e-4011-94c6-0f08e7601587

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hodd : Odd l) (hpi : ‖(l : K)‖ < 1) : 1 ≤ ‖(2 : K)‖ := by
  by_contra h
  push_neg at h
  obtain ⟨m, rfl⟩ := hodd
  have hnat : ∀ k : ℕ, ‖(k : K)‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have h1 : (1 : K) = ((2 * m + 1 : ℕ) : K) - 2 * (m : K) := by
    push_cast
    ring
  have h2 : ‖(2 : K) * (m : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h
  have h3 : ‖(1 : K)‖ < 1 := by
    rw [h1, sub_eq_add_neg]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hpi (by rwa [norm_neg]))
  simp at h3
end Formalism.DworkPowerSeriesWeights
