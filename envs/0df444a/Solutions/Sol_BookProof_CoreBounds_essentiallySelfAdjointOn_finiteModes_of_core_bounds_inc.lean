-- Prove2me | solution 1 for BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:44:00.220822+00:00
-- url     : https://prove2.me/submissions/90cef147-b29f-4778-a23c-091a174ca06c

-- Generated from ChapterCoreBoundsEsa.lean — solution of BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_inc
import Mathlib
import Definitions.Def_ChapterCoreBoundsEsa
import Theorems.Thm_BookProof_OperatorSeries_essentiallySelfAdjointOn_finiteModes_of_bounds
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
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A B : ℝ) (hB : 0 ≤ B)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v))
    (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      |(-2 : ℝ) * (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im|
        ≤ B * (inner ℂ ((u : L2I ι)) ((diagMax c (inclC c u) : L2I ι)) : ℂ).re) :
    EssentiallySelfAdjointOn (lpFiniteModes ι) H₀ := by

  classical
  have hkey := essentiallySelfAdjointOn_finiteModes_of_bounds c hc (coreExt hA) A B hB
    (coreExt_symmetricOn hA hsym) (norm_coreExt_le hA) (coreExt_commForm_le hA hcomm)
  have hres : (coreExt hA).comp (Submodule.inclusion (finiteModes_le_maxDom c)) = H₀ :=
    LinearMap.ext fun u => coreExt_core hA u
  rwa [hres] at hkey
