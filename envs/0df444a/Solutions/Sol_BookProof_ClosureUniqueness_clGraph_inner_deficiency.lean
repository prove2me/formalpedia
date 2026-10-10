-- Prove2me | solution 1 for BookProof.ClosureUniqueness.clGraph_inner_deficiency
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:16:23.512593+00:00
-- url     : https://prove2.me/submissions/c93b7db7-447d-4758-b8a8-60db127ed2ec

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.clGraph_inner_deficiency
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {T : D →ₗ[ℂ] F} {w : F}
    (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = Complex.I * inner ℂ (v : F) w) {p : F × F}
    (hp : p ∈ clGraph T) : (inner ℂ p.2 w : ℂ) = Complex.I * inner ℂ p.1 w := by

  have hclosed : IsClosed {q : F × F | (inner ℂ q.2 w : ℂ) = Complex.I * inner ℂ q.1 w} :=
    isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_const.mul (continuous_fst.inner continuous_const))
  exact clGraph_subset_of_isClosed hclosed (fun v => hw v) hp
