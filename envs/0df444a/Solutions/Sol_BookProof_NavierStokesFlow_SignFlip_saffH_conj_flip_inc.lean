-- Prove2me | solution 1 for BookProof.NavierStokesFlow.SignFlip.saffH_conj_flip_inc
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:58:00.332753+00:00
-- url     : https://prove2.me/submissions/f0a3c535-6e1a-48b2-8df5-3471e8b6a66d

import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem solution {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : c < 0)
    (x : maxDom (oscSymbol (affMu κ |c|))) :
    (flipU (fun n : ℕ => n) (affH hκ (abs_nonneg c) x) : L2I ℕ)
      = (saffH hκ c ⟨flipU (fun n : ℕ => n) (x : L2I ℕ),
          flipU_mem_maxDom _ (oscSymbol (affMu κ |c|)) x.2⟩ : L2I ℕ) := by
  apply BookProof.NavierStokesFlow.SignFlip.saffH_conj_flip <;> assumption

