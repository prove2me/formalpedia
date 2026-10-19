-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:06:41.399974+00:00
-- url     : https://prove2.me/submissions/2dee376d-f162-4591-b046-a0715b515c06

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.tailState_not_mem_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_tailState_coeFn
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_tailStep_subset
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_fockMeasure_tailStep_pos
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution : tailState ∉ momFock.core := by

  rintro ⟨n, hn⟩
  have hzero : ∀ᵐ x ∂fockR, x ∉ tailStep (n + 1) := by
    filter_upwards [hn, tailState_coeFn] with x hx hcoe hmem
    obtain ⟨ξ, hξ, rfl⟩ := hmem
    have h0 : ξ 0 ∈ Set.Icc ((n : ℝ) + 1) ((n + 1 : ℕ) + (1 / 2) ^ (n + 1)) := by
      have := hξ 0 (Set.mem_univ 0)
      simpa using this
    have hnn : (0 : ℝ) ≤ ξ 0 := le_trans (by positivity) h0.1
    have hs : |momFock.scale (parcelMk 1 ξ)| = 3 * ξ 0 := by
      rw [momFock_scale]
      show abs (3 * abs (∑ k : Fin 1, ξ k)) = 3 * ξ 0
      rw [Fin.sum_univ_one, abs_of_nonneg hnn, abs_of_nonneg (by positivity)]
    have hbig : ¬ (|momFock.scale (parcelMk 1 ξ)| ≤ (n : ℝ)) := by
      rw [hs]
      have hge : (n : ℝ) + 1 ≤ ξ 0 := h0.1
      push_neg
      linarith
    have h1 := hx hbig
    rw [hcoe, Set.indicator_of_mem (tailStep_subset (n + 1) ⟨ξ, hξ, rfl⟩)] at h1
    exact one_ne_zero h1
  rw [← measure_eq_zero_iff_ae_notMem] at hzero
  exact absurd hzero (ne_of_gt (fockMeasure_tailStep_pos (n + 1)))
