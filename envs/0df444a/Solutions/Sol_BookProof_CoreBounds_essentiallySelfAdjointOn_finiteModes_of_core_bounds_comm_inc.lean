-- Prove2me | solution 1 for BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:44:11.382379+00:00
-- url     : https://prove2.me/submissions/bfc973ef-9564-4b57-af7f-d843a7737072

-- Generated from ChapterCoreBoundsEsa.lean — solution of BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm_inc
import Mathlib
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.CoreBounds




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.OperatorSeries
open Filter Topology
open BookProof.NavierStokesFlow.IkebeKato

noncomputable section

variable {ι : Type*} {c : ι → ℝ}

variable {ι : Type*} {c : ι → ℝ}
variable (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v))
    (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im = 0) :
    EssentiallySelfAdjointOn (lpFiniteModes ι) H₀ := by

  refine essentiallySelfAdjointOn_finiteModes_of_core_bounds c hc H₀ A 0 le_rfl hsym hA ?_
  intro u
  rw [hcomm u]
  simp
