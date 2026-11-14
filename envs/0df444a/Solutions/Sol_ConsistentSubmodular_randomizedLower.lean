-- Prove2me | solution 1 for ConsistentSubmodular.randomizedLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:47:25.017373+00:00
-- url     : https://prove2.me/submissions/a209d226-d511-4dba-a03e-d9f1be830b28

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_psiRoot
import Theorems.Thm_ConsistentSubmodular_additionRobustReduction
import Theorems.Thm_ConsistentSubmodular_intervalSelectionReduction
import Theorems.Thm_ConsistentSubmodular_consecutiveIntervalReduction
import Theorems.Thm_ConsistentSubmodular_consecutiveIntervalGap

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ} {α : ℝ}

/-- **Theorem 2** (Appendix A.7), from Lemma 1 and a `ξ⋆`-addition-robust
routine: apply Lemma 1 with `γ = min{ε/3, 1/16}`. The approximation is at least
`ξ⋆ - ε`, and since `1/γ ≤ 16/ε` the consistency is at most `256 K ε⁻²`. -/
theorem randomizedLower_of (hred : AdditionRobustReductionGoal) (hξ0 : 0 ≤ xiStar)
    (hξ1 : xiStar ≤ 1) (hrobust : AdmitsAdditionRobust xiStar) : RandomizedLowerGoal := by
  obtain ⟨K, hK⟩ := hred
  refine ⟨256 * max K 0, fun ε hε hε1 => ?_⟩
  set γ := min (ε / 3) (1 / 16) with hγ_def
  have hγ : 0 < γ := lt_min (by positivity) (by norm_num)
  have hγ8 : γ < 1 / 8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hγε : 3 * γ ≤ ε := by
    have := min_le_left (ε / 3) (1 / 16)
    linarith
  obtain ⟨C, hC, hG⟩ := hK γ hγ hγ8
  refine ⟨C, ?_, fun n k f => ?_⟩
  · have hinv : 1 / γ ≤ 16 / ε := by
      rw [div_le_div_iff₀ hγ hε]
      rcases min_choice (ε / 3) (1 / 16) with h | h
      · rw [← hγ_def] at h
        rw [h]
        linarith
      · rw [← hγ_def] at h
        rw [h]
        linarith
    have hsq : (1 / γ) ^ 2 ≤ 256 * (1 / ε) ^ 2 := by
      have h0 : 0 ≤ 1 / γ := by positivity
      have : (16 / ε) ^ 2 = 256 * (1 / ε) ^ 2 := by ring
      nlinarith
    have hK0 : K ≤ max K 0 := le_max_left K 0
    have hm : 0 ≤ max K 0 := le_max_right K 0
    calc (C : ℝ) ≤ K * (1 / γ) ^ 2 := hC
      _ ≤ max K 0 * (1 / γ) ^ 2 := mul_le_mul_of_nonneg_right hK0 (by positivity)
      _ ≤ max K 0 * (256 * (1 / ε) ^ 2) := mul_le_mul_of_nonneg_left hsq hm
      _ = 256 * max K 0 * (1 / ε) ^ 2 := by ring
  · obtain ⟨μ, hμ, hval⟩ := hG xiStar hξ0 hξ1 hrobust n k f
    refine ⟨μ, hμ, fun t A hA hAk => ?_⟩
    have h := hval t A hA hAk
    have hfA := f.nonnegative A
    nlinarith

end ConsistentSubmodular.Checkpoints

end

end

section

open ConsistentSubmodular

theorem solution : RandomizedLowerGoal := by
  obtain ⟨hξ, hξ1, -⟩ := psiRoot
  have hgap : ∀ (N : ℕ) (I : IntervalInstance N), xiStar ≤ I.adaptivityGap :=
    consecutiveIntervalReduction xiStar (by linarith) hξ1.le consecutiveIntervalGap.1
  exact Checkpoints.randomizedLower_of additionRobustReduction (by linarith) hξ1.le
    (fun n W _ => intervalSelectionReduction xiStar (by linarith) hξ1.le hgap n W)

end
