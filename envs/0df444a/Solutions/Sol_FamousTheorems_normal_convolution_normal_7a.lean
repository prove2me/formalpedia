-- Prove2me | solution 1 for FamousTheorems.normal_convolution_normal_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:47:43.654831+00:00
-- url     : https://prove2.me/submissions/529b729c-d615-45af-a5fe-8d2c62d3a3c7

import Mathlib

theorem solution (m₁ m₂ : ℝ) (v₁ v₂ : NNReal) :
    (ProbabilityTheory.gaussianReal m₁ v₁).conv (ProbabilityTheory.gaussianReal m₂ v₂) =
      ProbabilityTheory.gaussianReal (m₁ + m₂) (v₁ + v₂) :=
  ProbabilityTheory.gaussianReal_conv_gaussianReal
