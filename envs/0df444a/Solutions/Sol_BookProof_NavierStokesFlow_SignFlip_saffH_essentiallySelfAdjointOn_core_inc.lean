-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.saffH_essentiallySelfAdjointOn_core_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T08:19:44.968085+00:00
-- url     : https://prove2.me/submissions/618ca00e-9013-407b-9a6a-9bd12313bf64

-- Generated from ChapterNavierStokesSignFlip.lean — solution of BookProof.NavierStokesFlow.SignFlip.saffH_essentiallySelfAdjointOn_core_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber
open BookProof.NavierStokesFlow.AffineFiber.PairShift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((saffH hκ c).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ |c|))))) := by

  rcases lt_or_ge c 0 with hc | hc
  · refine essentiallySelfAdjointOn_of_intertwine (flipU (fun n : ℕ => n))
      ((affH hκ (abs_nonneg c)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ |c|))))) _
      (fun v => flipU_mem_finiteModes _ v.2) (fun v => ?_)
      (affH_essentiallySelfAdjointOn_core hκ (abs_nonneg c))
    exact saffH_conj_flip hκ hc _
  · rw [saffH_eq_affH hκ hc]
    exact affH_essentiallySelfAdjointOn_core hκ (abs_nonneg c)
