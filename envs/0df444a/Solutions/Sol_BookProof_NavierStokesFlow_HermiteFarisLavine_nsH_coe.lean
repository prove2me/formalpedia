-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T19:45:38.562201+00:00
-- url     : https://prove2.me/submissions/b84620bb-f701-4edc-b6f5-9149e061ed64

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open BookProof.NavierStokesFlow.HermiteFarisLavine BookProof.NavierStokesFlow.IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (m : ℕ) :
    ((nsH κ hκ x : L2I ℕ) : ℕ → ℂ) m = hFun κ ((x : L2I ℕ) : ℕ → ℂ) m := rfl
