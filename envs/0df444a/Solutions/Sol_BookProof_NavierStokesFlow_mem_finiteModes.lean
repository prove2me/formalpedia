-- Prove2me | solution 1 for BookProof.NavierStokesFlow.mem_finiteModes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T00:25:33.646305+00:00
-- url     : https://prove2.me/submissions/4268feca-bfb9-4658-99fc-e74d2f41ffd0

-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow









open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

set_option maxHeartbeats 1000000 in
theorem solution {f : L2Z} :
    f ∈ finiteModes ↔ (Function.support ((f : ℤ → ℂ))).Finite := Iff.rfl
