-- Prove2me | solution 1 for BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:23:54.323035+00:00
-- url     : https://prove2.me/submissions/0ba486f7-b84c-4cc1-b48c-f3e2d8e966ae

-- Generated from ChapterNavierStokesBilinearEsa.lean — solution of BookProof.NavierStokesFlow.BilinearEsa.blockVec_mem_maxDom
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

variable {J : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (κ : J → ℝ) (v : lpFiniteModes (ℕ × J)) (j : J) :
    (blockVec ((v : L2I (ℕ × J))) j) ∈ maxDom (oscSymbol (κ j)) := by

  refine finiteModes_le_maxDom _ (mem_lpFiniteModes.mpr ?_)
  have hv := mem_lpFiniteModes.mp v.2
  have hinj : Function.Injective fun n : ℕ => (n, j) := by
    intro a b hab
    simpa using hab
  have hsub : Function.support
        (fun n : ℕ => (((blockVec ((v : L2I (ℕ × J))) j) : L2I ℕ) : ℕ → ℂ) n)
      ⊆ (fun n : ℕ => (n, j)) ⁻¹' Function.support (((v : L2I (ℕ × J))) : ℕ × J → ℂ) :=
    fun n hn => hn
  exact Set.Finite.subset (Set.Finite.preimage hinj.injOn hv) hsub
