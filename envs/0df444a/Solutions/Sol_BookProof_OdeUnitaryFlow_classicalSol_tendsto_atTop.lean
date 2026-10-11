-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.classicalSol_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:58:00.263392+00:00
-- url     : https://prove2.me/submissions/ea0028c0-9831-4f9c-a89d-cadb564d2af0

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.classicalSol_tendsto_atTop
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_classicalSol_singular_time
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (x₀ : ℝ) (hx₀ : 0 < x₀) :
    Tendsto (classicalSol x₀) (𝓝[<] (1 / x₀)) atTop := by

  have hcont : Tendsto (fun t : ℝ => 1 - t * x₀) (𝓝 (1 / x₀)) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => 1 - t * x₀) (𝓝 (1 / x₀)) (𝓝 (1 - (1 / x₀) * x₀)) :=
      (tendsto_id.mul_const x₀).const_sub 1
    rwa [classicalSol_singular_time x₀ (ne_of_gt hx₀)] at h
  have hden : Tendsto (fun t : ℝ => 1 - t * x₀) (𝓝[<] (1 / x₀)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t < 1 / x₀ := ht
    have h1 : t * x₀ < 1 := by
      have := (lt_div_iff₀ hx₀).mp ht'
      linarith
    simp only [mem_Ioi]
    linarith
  have hinv : Tendsto (fun t : ℝ => (1 - t * x₀)⁻¹) (𝓝[<] (1 / x₀)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  have h := hinv.const_mul_atTop hx₀
  simp only [classicalSol, div_eq_mul_inv] at ⊢
  exact h
