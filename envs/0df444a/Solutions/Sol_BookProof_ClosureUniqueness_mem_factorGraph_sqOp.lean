-- Prove2me | solution 1 for BookProof.ClosureUniqueness.mem_factorGraph_sqOp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:26:28.330979+00:00
-- url     : https://prove2.me/submissions/d6537f17-9d27-4403-9e18-8d8286cba427

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.mem_factorGraph_sqOp
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}


theorem solution (A : D →ₗ[ℂ] F) (hsym : SymmetricOn D A)
    (hstab : ∀ v : D, (A v : F) ∈ D) (v : D) :
    ((v : F), sqOp A hstab v) ∈ factorGraph A := by
  refine ⟨(A v : F), mem_clGraph_of_mem_opGraph (mem_opGraph A v), ?_⟩
  intro q hq
  obtain ⟨w, rfl⟩ := hq
  exact hsym w ⟨A v, hstab v⟩

