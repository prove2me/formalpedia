-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:42:53.385615+00:00
-- url     : https://prove2.me/submissions/15c3b403-b22b-4ff8-b0b6-d60cef4cff8f

import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_momentumOp_apply
-- Generated from ChapterNsFieldMomentumInverse.lean — theorem BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp
open BookProof.FarisLavine
open BookProof.FourierMultiplierEsa
open BookProof.NsSpatialMultiplier
open BookProof.StrichartzWave
open BookProof.NsFieldMomentumInverse



open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]


theorem solution (m : W) (f : 𝓢(W, ℂ)) :
    IsMomInverse m (l2Fourier W (opL2 (momentumOp m) (schwartzEquiv W f)))
      (l2Fourier W (f.toLp 2 (volume : Measure W))) := by
  have h1 : l2Fourier W (f.toLp 2 (volume : Measure W)) = (𝓕 f : 𝓢(W, ℂ)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq f
  have h2 : opL2 (momentumOp m) (schwartzEquiv W f) = (momentumOp m f).toLp 2 (volume : Measure W) := by
    unfold opL2
    simp
  rw [h1, h2]
  have h3 : l2Fourier W ((momentumOp m f).toLp 2 (volume : Measure W))
      = (𝓕 (momentumOp m f) : 𝓢(W, ℂ)).toLp 2 :=
    SchwartzMap.toLp_fourier_eq _
  rw [h3]
  unfold IsMomInverse
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 f : 𝓢(W, ℂ)) 2 (volume : Measure W),
    SchwartzMap.coeFn_toLp (𝓕 (momentumOp m f) : 𝓢(W, ℂ)) 2 (volume : Measure W)] with ξ hA hB
  rw [hA, hB, BookProof.FourierMultiplierEsa.fourier_momentumOp_apply]
  rfl

