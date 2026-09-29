-- Prove2me | solution 1 for FamousTheorems.poisson_convolution_poisson_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:47:53.029863+00:00
-- url     : https://prove2.me/submissions/d89343d5-cb94-4c75-8be3-e54d34f81f60

import Mathlib

theorem solution (r₁ r₂ : NNReal) :
    (ProbabilityTheory.poissonMeasure r₁).conv (ProbabilityTheory.poissonMeasure r₂) =
      ProbabilityTheory.poissonMeasure (r₁ + r₂) :=
  ProbabilityTheory.poissonMeasure_conv_poissonMeasure r₁ r₂
