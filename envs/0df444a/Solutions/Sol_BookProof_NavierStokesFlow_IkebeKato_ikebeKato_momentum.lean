-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:47:55.143074+00:00
-- url     : https://prove2.me/submissions/464a057f-cd3d-426b-9ebd-18456b2d13a7

import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}
theorem h43_diag_esa {ι : Type*} (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) :=
  IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds c hc (diagMax c) 1 0 0
    (IkebeKato.diagMax_symmetricOn c) le_rfl (fun x => by simp) (fun x => by simp [commForm])

theorem solution (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by
  exact h43_diag_esa c hc

