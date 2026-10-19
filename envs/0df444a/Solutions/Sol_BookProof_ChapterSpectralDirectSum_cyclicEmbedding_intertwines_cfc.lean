-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:57:06.157587+00:00
-- url     : https://prove2.me/submissions/1d51d1c8-d115-4291-985c-c6c00608e3af

-- Generated from ChapterSpectralDirectSum.lean — solution of BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterSpectralDirectSum



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

set_option maxHeartbeats 1000000 in
theorem solution (g : C(spectrum ℂ T, ℂ))
    (u : Lp ℂ 2 (spectralMeasure T hT xi)) :
    cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) g u)
      = cfcHom hT g (cyclicEmbedding T hT xi u) := by

  have hdense : DenseRange
      ((ContinuousMap.toLp 2 (spectralMeasure T hT xi) ℂ).toLinearMap :
        C(spectrum ℂ T, ℂ) → Lp ℂ 2 (spectralMeasure T hT xi)) :=
    ContinuousMap.toLp_denseRange ℂ _ (μ := spectralMeasure T hT xi) (by simp)
  have hcont₁ : Continuous fun v : Lp ℂ 2 (spectralMeasure T hT xi) =>
      cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) g v) :=
    (cyclicEmbedding T hT xi).continuous.comp
      (mulRep (spectralMeasure T hT xi) g).continuous
  have hcont₂ : Continuous fun v : Lp ℂ 2 (spectralMeasure T hT xi) =>
      cfcHom hT g (cyclicEmbedding T hT xi v) :=
    (cfcHom hT g).continuous.comp (cyclicEmbedding T hT xi).continuous
  have hfun : (fun v : Lp ℂ 2 (spectralMeasure T hT xi) =>
        cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) g v))
      = fun v : Lp ℂ 2 (spectralMeasure T hT xi) =>
        cfcHom hT g (cyclicEmbedding T hT xi v) := by
    refine hdense.equalizer hcont₁ hcont₂ (funext fun f => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe]
    rw [mulRep_toLp T hT xi g f, cyclicEmbedding_toLp, cyclicEmbedding_toLp, map_mul]
    rfl
  exact congrFun hfun u
