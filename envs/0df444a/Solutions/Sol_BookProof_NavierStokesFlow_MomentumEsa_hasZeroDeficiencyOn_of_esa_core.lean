-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.hasZeroDeficiencyOn_of_esa_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:25:34.174626+00:00
-- url     : https://prove2.me/submissions/eec9eac4-e489-44f4-b316-3e862e6d4916

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.hasZeroDeficiencyOn_of_esa_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {c : ι → ℝ} (H : maxDom c →ₗ[ℂ] L2I ι)
    (Hc : lpFiniteModes ι →ₗ[ℂ] lpFiniteModes ι)
    (hHc : ∀ x : lpFiniteModes ι, ((Hc x : lpFiniteModes ι) : L2I ι)
      = H (Submodule.inclusion (finiteModes_le_maxDom c) x))
    (hesa : EssentiallySelfAdjointOn (lpFiniteModes ι)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom c)))) :
    HasZeroDeficiencyOn (lpFiniteModes ι) Hc := by

  refine (essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn (lpFiniteModes ι) Hc).1 ?_
  have hEq : (lpFiniteModes ι).subtype.comp Hc
      = H.comp (Submodule.inclusion (finiteModes_le_maxDom c)) :=
    LinearMap.ext fun x => hHc x
  rw [hEq]
  exact hesa
