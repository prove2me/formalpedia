-- Prove2me | solution 2 for BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:53:13.94369+00:00
-- url     : https://prove2.me/submissions/76d28d2a-4651-4fb7-afe5-e5040ac2fd1e

import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato
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

theorem h43_fock_nonneg (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (a : Config) : 0 ≤ fockSymbol n a := by
  unfold fockSymbol
  have : 0 ≤ a.sum fun k m => (m : ℝ) * n k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hn k))
  linarith

theorem h43_ns_nonneg (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 0 ≤ BookProof.NavierStokesFlow.MomentumEsa.nsSymbol d p q k := by
  unfold BookProof.NavierStokesFlow.MomentumEsa.nsSymbol; positivity

theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      ((diagMax (nsFockSymbol d p q)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (nsFockSymbol d p q)))) := by
  exact h43_diag_esa _ (h43_fock_nonneg _ (h43_ns_nonneg d p q))

