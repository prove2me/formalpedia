-- Prove2me | solution 2 for BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:53:06.685755+00:00
-- url     : https://prove2.me/submissions/6ef7aba9-a48e-4e9d-9eaf-4923ec4778cb

import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
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

theorem h43_fock_nonneg (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (a : Config) : 0 ≤ fockSymbol n a := by
  unfold fockSymbol
  have : 0 ≤ a.sum fun k m => (m : ℝ) * n k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hn k))
  linarith

theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      ((diagMax (fockSymbol n)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)))) := by
  exact h43_diag_esa _ (h43_fock_nonneg n hn)

