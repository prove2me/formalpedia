-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.isColumnStochastic_eq_Mab
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:06:03.337155+00:00
-- url     : https://prove2.me/submissions/40b72e5c-6def-45a5-b7b9-8e191b604922

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.isColumnStochastic_eq_Mab
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator
private theorem exists_cos_sq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∃ a : ℝ, Real.cos a ^ 2 = p := by
  refine ⟨Real.arccos (Real.sqrt p), ?_⟩
  rw [Real.cos_arccos (by linarith [Real.sqrt_nonneg p]) (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1)]
  rw [Real.sq_sqrt h0]

set_option maxHeartbeats 1000000 in
theorem solution {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : IsColumnStochastic M) : ∃ a b, M = Mab a b := by

  obtain ⟨hnn, hcol⟩ := hM
  have hc0 := hcol 0
  have hc1 := hcol 1
  simp only [Fin.sum_univ_two] at hc0 hc1
  obtain ⟨a, ha⟩ := exists_cos_sq (hnn 0 0) (by linarith [hnn 1 0])
  obtain ⟨b, hb⟩ := exists_cos_sq (hnn 0 1) (by linarith [hnn 1 1])
  refine ⟨a, b, ?_⟩
  have hsa : Real.sin a ^ 2 = M 1 0 := by
    have := Real.cos_sq_add_sin_sq a; nlinarith [this, ha, hc0]
  have hsb : Real.sin b ^ 2 = M 1 1 := by
    have := Real.cos_sq_add_sin_sq b; nlinarith [this, hb, hc1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mab, ha, hb, hsa, hsb]
