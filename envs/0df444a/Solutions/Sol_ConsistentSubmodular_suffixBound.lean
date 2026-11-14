-- Prove2me | solution 1 for ConsistentSubmodular.suffixBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:45.197771+00:00
-- url     : https://prove2.me/submissions/34805708-0430-4d16-be86-0890371c56a7

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

/-- Lemma B.6 (suffix bound), the inequality (30) with `M` any upper bound of
`u` and `z` in place of `max(u, z)`. -/
theorem suffix_bound {lam g u z M γ : ℝ} (hz : 0 ≤ z) (hMu : u ≤ M) (hMz : z ≤ M)
    (hγ0 : 0 ≤ γ) (hγ2 : γ ≤ 2) (h : 2 * g - u ≤ γ * (lam + z)) :
    2 * (lam + g) ≤ (2 + γ) * (lam + (u + z + M) / 4) := by
  rcases le_total u z with huz | hzu
  · nlinarith [mul_nonneg (show 0 ≤ 2 + γ by linarith) (sub_nonneg.mpr hMz),
      mul_nonneg (sub_nonneg.mpr hγ2) (show 0 ≤ 2 * z - u by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ 2 + γ by linarith) (sub_nonneg.mpr hMu),
      mul_nonneg hγ0 (sub_nonneg.mpr hzu), mul_nonneg (sub_nonneg.mpr hγ2) hz]

namespace Certificates

/-- Lemma B.6 (suffix bound). -/
theorem suffixBound : SuffixBoundGoal := by
  intro lam g u z γ _ _ _ hz hγ0 hγ2 h
  have hs := suffix_bound (M := max u z) hz (le_max_left u z) (le_max_right u z) hγ0 hγ2 h
  have hminmax : lam + (u + z) / 2 - min u z / 4 = lam + (u + z + max u z) / 4 := by
    rcases le_total u z with huz | hzu
    · rw [min_eq_left huz, max_eq_right huz]; ring
    · rw [min_eq_right hzu, max_eq_left hzu]; ring
  rw [hminmax, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  linarith [mul_comm (2 + γ) (lam + (u + z + max u z) / 4)]

end Certificates

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : SuffixBoundGoal :=
  Certificates.suffixBound

end
