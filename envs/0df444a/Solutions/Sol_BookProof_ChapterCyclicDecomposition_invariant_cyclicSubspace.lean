-- Prove2me | solution 1 for BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:51:25.700684+00:00
-- url     : https://prove2.me/submissions/9b37dc62-f853-4061-b008-79996a57e39c

-- Generated from ChapterCyclicDecomposition.lean — solution of BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_isClosed_cyclicSubspace
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_cfcHom_apply_mem_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

set_option maxHeartbeats 1000000 in
theorem solution (xi : H) : Invariant T hT (cyclicSubspace T hT xi) := by

  intro g v hv
  have hle : Submodule.span ℂ (Set.range fun f : C(spectrum ℂ T, ℂ) => cfcHom hT f xi)
      ≤ (cyclicSubspace T hT xi).comap (cfcHom hT g).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    have hgf : cfcHom hT g (cfcHom hT f xi) = cfcHom hT (g * f) xi := by
      rw [map_mul]
      rfl
    simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, hgf]
    exact cfcHom_apply_mem_cyclicSubspace T hT xi (g * f)
  have hclosed : IsClosed
      ((cyclicSubspace T hT xi).comap (cfcHom hT g).toLinearMap : Set H) :=
    (isClosed_cyclicSubspace T hT xi).preimage (cfcHom hT g).continuous
  exact Submodule.topologicalClosure_minimal _ hle hclosed hv
