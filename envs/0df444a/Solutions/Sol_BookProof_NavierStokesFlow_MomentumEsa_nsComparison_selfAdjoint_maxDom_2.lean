-- Prove2me | solution 2 for BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:53:21.270666+00:00
-- url     : https://prove2.me/submissions/94a93786-cd6f-469a-8baf-3c318e43f1c0

import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}
theorem h43_diag_esa {ι : Type*} (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) :=
  IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds c hc (diagMax c) 1 0 0
    (IkebeKato.diagMax_symmetricOn c) le_rfl (fun x => by simp) (fun x => by simp [commForm])

theorem h43_esa_mono {ι : Type*} (c : ι → ℝ)
    (h : EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c)))) :
    EssentiallySelfAdjointOn (maxDom c) (diagMax c) :=
  ⟨fun w hw => h.1 w (fun v => hw _), fun w hw => h.2 w (fun v => hw _)⟩

theorem h43_ns_nonneg (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 0 ≤ BookProof.NavierStokesFlow.MomentumEsa.nsSymbol d p q k := by
  unfold BookProof.NavierStokesFlow.MomentumEsa.nsSymbol; positivity

theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (maxDom (nsSymbol d p q)) (diagMax (nsSymbol d p q)) := by
  exact h43_esa_mono _ (h43_diag_esa _ (h43_ns_nonneg d p q))

