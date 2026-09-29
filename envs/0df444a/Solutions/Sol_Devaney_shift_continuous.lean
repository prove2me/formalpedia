-- Prove2me | solution 1 for Devaney.shift_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T21:08:04.702836+00:00
-- url     : https://prove2.me/submissions/f054920a-333d-4a26-8cff-764f1cc89c3d

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DevFix

open Devaney Devaney.Sigma2

theorem dist_eq (s t : Sigma2) : dist s t = ∑' i, distTerm s t i := rfl

/-- Proposition 6.5: the shift is Lipschitz with constant `2`, hence continuous. -/
theorem shift_lipschitz : LipschitzWith 2 (shift : Sigma2 → Sigma2) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  have hterm : ∀ i : ℕ, distTerm (shift s) (shift t) i = 2 * distTerm s t (i + 1) := by
    intro i
    show |(shift s).entry i - (shift t).entry i| / 2 ^ i
        = 2 * (|s.entry (i + 1) - t.entry (i + 1)| / 2 ^ (i + 1))
    have he : ∀ u : Sigma2, (shift u).entry i = u.entry (i + 1) := fun u => rfl
    rw [he, he, pow_succ]
    field_simp
  have hshift : Summable (fun i => distTerm s t (i + 1)) :=
    (summable_distTerm s t).comp_injective (add_left_injective 1)
  have h1 : dist (shift s) (shift t) = 2 * ∑' i, distTerm s t (i + 1) := by
    rw [dist_eq, tsum_congr hterm, tsum_mul_left]
  have h2 := (summable_distTerm s t).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h2
  have h3 : ∑' i, distTerm s t (i + 1) ≤ dist s t := by
    rw [dist_eq, ← h2]
    linarith [distTerm_nonneg s t 0]
  have h4 : (0 : ℝ) ≤ ∑' i, distTerm s t (i + 1) :=
    tsum_nonneg fun i => distTerm_nonneg s t _
  rw [h1]
  have : ((2 : NNReal) : ℝ) = 2 := by norm_num
  rw [this]
  linarith

theorem shift_continuous : Continuous (shift : Sigma2 → Sigma2) :=
  shift_lipschitz.continuous

end DevFix

open Devaney Devaney.Sigma2 in
theorem solution : Continuous (shift : Sigma2 → Sigma2) :=
  DevFix.shift_continuous
