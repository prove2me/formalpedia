-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:39.964317+00:00
-- url     : https://prove2.me/submissions/f8ba8f3f-9855-450d-8bef-a4aec46689dd

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.IsColumnStochastic.mulVec_isProbabilityVector
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsColumnStochastic M)
    {v : Fin 2 → ℝ} (hv : IsProbabilityVector v) :
    IsProbabilityVector (M.mulVec v) := by

  obtain ⟨hnn, hcol⟩ := hM
  obtain ⟨hvnn, hvsum⟩ := hv
  refine ⟨?_, ?_⟩
  · intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hnn i j) (hvnn j))
  · have hc0 := hcol 0
    have hc1 := hcol 1
    simp only [Fin.sum_univ_two] at hc0 hc1
    have hv2 : v 0 + v 1 = 1 := by simpa [Fin.sum_univ_two] using hvsum
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination v 0 * hc0 + v 1 * hc1 + hv2
