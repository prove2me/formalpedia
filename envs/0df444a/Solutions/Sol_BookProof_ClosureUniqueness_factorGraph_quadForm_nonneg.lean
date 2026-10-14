-- Prove2me | solution 1 for BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:55:51.693507+00:00
-- url     : https://prove2.me/submissions/6350443d-e025-4295-a63a-7e6f212028ca

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_quadForm
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorGraph A) :
    0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0 := by

  obtain ⟨y, -, hval⟩ := factorGraph_quadForm hp
  rw [hval]
  exact ⟨by rw [Complex.ofReal_re]; positivity, Complex.ofReal_im _⟩
