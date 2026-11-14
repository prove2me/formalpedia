-- Prove2me | solution 1 for ConsistentSubmodular.Minimax.saddlePoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:46.986638+00:00
-- url     : https://prove2.me/submissions/5ea20aa1-cc50-4f95-96d0-8b679fdb438e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax
import Theorems.Thm_ConsistentSubmodular_Minimax_exists_dominating

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Minimax

variable {m : ℕ}

theorem guarantee_le (w : Fin (m + 1) → Fin (m + 1) → ℝ) (a : Point m) (j : Fin (m + 1)) :
    guarantee w a ≤ ∑ i, a i * w i j :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem continuous_guarantee (w : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Continuous (guarantee w) := by
  unfold guarantee
  exact Continuous.finset_inf'_apply _ fun j _ => by fun_prop

end ConsistentSubmodular.Minimax

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Minimax
variable {m : ℕ}

theorem solution (w : Fin (m + 1) → Fin (m + 1) → ℝ) : ∃ v : ℝ,
    (∃ a : Point m, IsSimplex a ∧ ∀ j, v ≤ ∑ i, a i * w i j) ∧
    (∃ b : Point m, IsSimplex b ∧ ∀ i, ∑ j, b j * w i j ≤ v) := by
  obtain ⟨a, ha, hmax⟩ := (isCompact_stdSimplex ℝ (Fin (m + 1))).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ 0⟩ (continuous_guarantee w).continuousOn
  refine ⟨guarantee w a, ⟨a, ha, guarantee_le w a⟩, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨a', ha', hbeat⟩ := exists_dominating w (guarantee w a) hno
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    fun j => ∑ i, a' i * w i j
  have hlt : guarantee w a < guarantee w a' := by
    unfold guarantee at hbeat ⊢
    rw [hj]
    exact hbeat j
  exact absurd (isMaxOn_iff.mp hmax a' ha') (not_le.mpr hlt)

end
