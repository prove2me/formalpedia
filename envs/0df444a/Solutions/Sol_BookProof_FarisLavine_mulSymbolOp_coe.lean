-- Prove2me | solution 1 for BookProof.FarisLavine.mulSymbolOp_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:50:14.994576+00:00
-- url     : https://prove2.me/submissions/d1de869b-9cac-4a14-b766-ea133d585f4f

-- Generated from ChapterFarisLavine.lean — solution of BookProof.FarisLavine.mulSymbolOp_coe
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FarisLavine





variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (lam s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ |lam n|)
    (f : mulSymbolDomain lam) :
    ((mulSymbolOp lam s hs f : L2Nat) : ℕ → ℂ) = mulSymbolFun s ((f : L2Nat) : ℕ → ℂ) := rfl
