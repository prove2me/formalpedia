-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.rangeClosure_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:26:04.321699+00:00
-- url     : https://prove2.me/submissions/b9db2985-bee3-44a3-b11a-d9851699fcfd

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.rangeClosure_le_ker
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {F G : V →L[ℂ] V} (h : G * F = 0) :
    rangeClosure F ≤ LinearMap.ker (G : V →ₗ[ℂ] V) := by

  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    have := congrArg (fun T : V →L[ℂ] V => T x) h
    simpa [ContinuousLinearMap.mul_apply] using this
  · exact (ContinuousLinearMap.isClosed_ker G).preimage continuous_id
