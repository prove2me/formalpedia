-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.volume_sum_sq_level
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:08:14.962615+00:00
-- url     : https://prove2.me/submissions/1dccdff8-29e6-4601-ae32-780c9542385f

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.volume_sum_sq_level
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_volume_sum_level
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (volume : Measure (Fin n → ℝ)) {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a} = 0 := by

  rcases lt_or_ge a 0 with ha | ha
  · have hempty : {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun ξ hξ => ?_
      have hsq : (0 : ℝ) ≤ (∑ i, ξ i) ^ 2 := sq_nonneg _
      rw [Set.mem_setOf_eq] at hξ
      linarith [hξ ▸ hsq]
    rw [hempty, measure_empty]
  · have hc : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have hsub : {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a}
        ⊆ {ξ : Fin n → ℝ | ∑ i, ξ i = Real.sqrt a}
          ∪ {ξ : Fin n → ℝ | ∑ i, ξ i = -Real.sqrt a} := by
      intro ξ hξ
      rw [Set.mem_setOf_eq] at hξ
      have hprod : (∑ i, ξ i - Real.sqrt a) * (∑ i, ξ i + Real.sqrt a) = 0 := by nlinarith
      rcases mul_eq_zero.1 hprod with h1 | h1
      · exact Or.inl (by simp only [Set.mem_setOf_eq]; linarith)
      · exact Or.inr (by simp only [Set.mem_setOf_eq]; linarith)
    refine le_antisymm ?_ zero_le
    calc (volume : Measure (Fin n → ℝ)) {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a}
        ≤ volume ({ξ : Fin n → ℝ | ∑ i, ξ i = Real.sqrt a}
            ∪ {ξ : Fin n → ℝ | ∑ i, ξ i = -Real.sqrt a}) := measure_mono hsub
      _ ≤ volume {ξ : Fin n → ℝ | ∑ i, ξ i = Real.sqrt a}
            + volume {ξ : Fin n → ℝ | ∑ i, ξ i = -Real.sqrt a} := measure_union_le _ _
      _ = 0 := by rw [volume_sum_level n hn, volume_sum_level n hn, add_zero]
