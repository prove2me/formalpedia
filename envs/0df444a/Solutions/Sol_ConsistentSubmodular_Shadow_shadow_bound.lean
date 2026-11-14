-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.shadow_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:27.874026+00:00
-- url     : https://prove2.me/submissions/3c518677-4558-430b-821f-9ac0e05473f6

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowIntervals
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_core_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Shadow

/-- Inequality (6) for one interval `[a, b]` and one left endpoint `c`: with
`d = |[a, b] ∩ [c, ∞)|`, the shadow interval `[c, c + d]` satisfies
`|[c, c + d] ∩ [x, ∞)| ≤ |[a, b] ∩ [x, ∞)|` for every `x`. -/
theorem shadow_le (a b c x : ℝ) :
    max 0 (c + max 0 (b - max a c) - max c x) ≤ max 0 (b - max a x) := by
  simp only [max_def]
  split_ifs <;> linarith

variable {N : ℕ} (I : IntervalInstance N)

theorem left_le_hindsight (j : Fin (N + 1)) : I.left j ≤ hindsight I j :=
  (le_add_of_nonneg_right (le_max_left _ _)).trans
    (Finset.le_sup' (fun i => I.value i j) (Finset.mem_univ j))

/-- Inequality (6): some original interval dominates the shadow interval `Î_j` against every
left endpoint. -/
theorem exists_dominating (j : Fin (N + 1)) : ∃ i, ∀ x,
    max 0 (hindsight I j - max (I.left j) x) ≤ max 0 (I.right i - max (I.left i) x) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => I.value i j
  refine ⟨i, fun x => ?_⟩
  rw [hindsight, hi, IntervalInstance.value]
  exact shadow_le _ _ _ _

end ConsistentSubmodular.Shadow

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Shadow
variable {N : ℕ} (I : IntervalInstance N)

theorem solution {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α) :
    α * I.adaptiveValue ≤ I.fixedValue := by
  have hlow : 0 ≤ (leftLaw I).low :=
    Finset.le_inf' (support_nonempty I) I.left fun j _ => I.left_nonneg j
  have hcore := (leftLaw I).core_le hα0 hα1 hchain hlow (hindsight I)
    (fun j _ => left_le_hindsight I j) (M := I.fixedValue - (leftLaw I).mean) fun i _ => by
      obtain ⟨i', hi'⟩ := exists_dominating I i
      calc ∑ j, I.prob j * max 0 (hindsight I i - max (I.left i) (I.left j))
          ≤ ∑ j, I.prob j * max 0 (I.right i' - max (I.left i') (I.left j)) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi' _) (I.prob_nonneg j)
        _ = ∑ j, I.prob j * I.value i' j - (leftLaw I).mean := by
            simp only [IntervalInstance.value, mul_add, Finset.sum_add_distrib, LeftLaw.mean,
              leftLaw]
            ring
        _ ≤ I.fixedValue - (leftLaw I).mean :=
            sub_le_sub_right (Finset.le_sup' (fun i => ∑ j, I.prob j * I.value i j)
              (Finset.mem_univ i')) _
  have hada : I.adaptiveValue =
      (leftLaw I).mean + ∑ j, (leftLaw I).prob j * (hindsight I j - (leftLaw I).left j) := by
    simp only [IntervalInstance.adaptiveValue, LeftLaw.mean, leftLaw, hindsight, mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [hada]
  linarith

end
