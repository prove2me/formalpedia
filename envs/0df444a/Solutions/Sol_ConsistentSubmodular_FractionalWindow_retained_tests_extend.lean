-- Prove2me | solution 1 for ConsistentSubmodular.FractionalWindow.retained_tests_extend
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:43.120493+00:00
-- url     : https://prove2.me/submissions/c1cdf00d-cc26-4863-9268-426810aa0151

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FractionalWindow

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.FractionalWindow
variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem solution (hN : 0 < N) (A : Finset (Fin n)) (loss : ℝ) (hloss : 0 ≤ loss)
    (htests : ∀ i, α * f.bufferedOptimum old (Q (W.retained i)) κ - loss ≤
      f.value (Q (W.retained i) ∪ A)) :
    ∀ t, t ≤ T → α * f.bufferedOptimum old (Q t) κ - loss-
      α * (f.bufferedOptimum old ∅ κ / N) ≤ f.value (Q t ∪ A) := by
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hwidth : 0 ≤ f.bufferedOptimum old ∅ κ / N :=
    div_nonneg (f.bufferedOptimum_nonnegative _ _ _) hNr
  have hα0 := W.level_nonneg
  have hα := W.level_le
  intro t ht
  rcases W.retained_covers t ht with hhigh | ⟨i, hit, hbin⟩
  · have hu := f.bufferedOptimum_le old (Q t) κ
    have hm := f.monotone (Q t) (Q t ∪ A) Finset.subset_union_left
    have h0 := f.nonnegative ∅
    have hv : f.bufferedOptimum old (Q t) κ ≤ f.value (Q t) + f.bufferedOptimum old ∅ κ := by
      linarith only [hu, h0]
    have h1 := mul_le_mul_of_nonneg_left hv hα0
    have h2 := mul_le_mul_of_nonneg_right hα (show 0 ≤ f.value (Q t) + f.bufferedOptimum old ∅ κ by
      linarith only [f.nonnegative (Q t), f.bufferedOptimum_nonnegative old ∅ κ])
    nlinarith only [h1, h2, hm, hhigh, hloss, mul_nonneg hα0 hwidth]
  · have hg := f.bufferedOptimum_growth (N := old) (k := κ) (hQ hit)
    have hm := f.monotone (Q (W.retained i) ∪ A) (Q t ∪ A) (Finset.union_subset_union_left (hQ hit))
    have hs := (htests i).trans hm
    have hd : f.bufferedOptimum old (Q t) κ ≤
        f.bufferedOptimum old (Q (W.retained i)) κ + f.bufferedOptimum old ∅ κ / N := by
      linarith only [hg, hbin]
    have h1 := mul_le_mul_of_nonneg_left hd hα0
    linarith only [h1, hs]

end
