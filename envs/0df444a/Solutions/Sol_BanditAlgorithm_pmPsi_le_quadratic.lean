-- Prove2me | solution 1 for BanditAlgorithm.pmPsi_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:41:39.358878+00:00
-- url     : https://prove2.me/submissions/6bd3774e-8e6c-4963-abc7-b16b79d11084

import Definitions.Def_PartialMonitoringAlgorithm26
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {k : ℕ} (q z : Fin k → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin k)) (hz : ∀ b, -1 ≤ z b) :
    pmPsi q z ≤ ∑ b : Fin k, q b * (z b) ^ 2 := by
  unfold pmPsi
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_left _ (hq.1 b)
  by_cases h : z b ≤ 1
  · have habs : |-(z b)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hz b]
    have he := Real.abs_exp_sub_one_sub_id_le habs
    have hle : Real.exp (-(z b)) - 1 - (-(z b)) ≤
        |Real.exp (-(z b)) - 1 - (-(z b))| := le_abs_self _
    nlinarith
  · have hz1 : 1 ≤ z b := le_of_not_ge h
    have he : Real.exp (-(z b)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    nlinarith [sq_nonneg (z b - 1)]

end BanditAlgorithm
