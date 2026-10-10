-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_approx_projection
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:56:03.752572+00:00
-- url     : https://prove2.me/submissions/e9888187-aba0-4a9d-af14-4494cd1e74cb

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_approx_projection
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH8_adjoint_comp_nested
import Theorems.Thm_BookProof_ChapterH8_adjoint_compress
import Theorems.Thm_BookProof_ChapterH8_adjoint_pow
import Theorems.Thm_BookProof_ChapterH8_compress_pow_comp_intertwine
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH8



open ContinuousLinearMap

noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH4

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y)
    (k : ℕ) (v : E) :
    Vn ((adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v))))
      = Vn (((compress Vn X) ^ k) ((adjoint Vn) v)) := by

  -- the `X∗`-intertwining, transposed to `J∗ ∘ Bₙ₊₁ᵏ = Bₙᵏ ∘ J∗`
  have hstar := compress_pow_comp_intertwine Vn Vm J (adjoint X) hJ hVm hJJ hinvadj k
  have hadj := congrArg ContinuousLinearMap.adjoint hstar
  rw [adjoint_comp, adjoint_comp, adjoint_pow, adjoint_pow, adjoint_compress, adjoint_compress,
    adjoint_adjoint] at hadj
  -- `V∗ₙ Vₙ₊₁ = J∗`
  have hproj : (adjoint Vn).comp Vm = adjoint J := adjoint_comp_nested Vn Vm J hJ hVm
  have h1 : (adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v)))
      = (adjoint J) (((compress Vm X) ^ k) ((adjoint Vm) v)) :=
    congrArg (fun f : G →L[ℂ] F => f (((compress Vm X) ^ k) ((adjoint Vm) v))) hproj
  have h2 : (adjoint J) (((compress Vm X) ^ k) ((adjoint Vm) v))
      = ((compress Vn X) ^ k) ((adjoint J) ((adjoint Vm) v)) :=
    congrArg (fun f : G →L[ℂ] F => f ((adjoint Vm) v)) hadj
  have h3 : (adjoint J) ((adjoint Vm) v) = (adjoint Vn) v := by
    have : (adjoint Vn) = (adjoint J).comp (adjoint Vm) := by
      rw [hJ, adjoint_comp]
    rw [this]
    rfl
  rw [h1, h2, h3]
