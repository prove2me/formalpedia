-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.vacState_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T20:37:42.634182+00:00
-- url     : https://prove2.me/submissions/c9f458e3-d745-48dd-830c-18e089ac5495

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.vacState_mem_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_vacState_coeFn
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution : vacState ∈ momFock.core := by

  refine ⟨0, ?_⟩
  filter_upwards [vacState_coeFn] with x hx hbig
  rw [hx]
  by_cases hmem : x ∈ vacSet
  · exfalso
    apply hbig
    obtain ⟨ξ, -, rfl⟩ := hmem
    rw [momFock_scale]
    show abs (3 * abs (∑ k : Fin 0, ξ k)) ≤ (↑(0:ℕ) : ℝ)
    simp
  · exact Set.indicator_of_notMem hmem _
