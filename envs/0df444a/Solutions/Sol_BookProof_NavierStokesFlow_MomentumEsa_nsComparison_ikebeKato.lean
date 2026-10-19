-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:45.248977+00:00
-- url     : https://prove2.me/submissions/b60161aa-8b40-4a15-be78-cfa49dd07839

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsComparison_restrict_eq
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_ikebeKato_momentum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
open BookProof.NavierStokesGaugeY

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((lpFiniteModes ℕ).subtype.comp (diagComparisonData d p q).comparison) := by

  have h := nsComparison_restrict_eq d p q
  have h2 := ikebeKato_momentum _ (nsSymbol_nonneg d p q)
  rw [h] at h2
  exact h2
