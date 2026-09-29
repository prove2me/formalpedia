-- Prove2me | solution 1 for FamousTheorems.kl_divergence_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:12:04.868337+00:00
-- url     : https://prove2.me/submissions/0205dc33-bc55-4dd0-9871-7de2bb534201

import Mathlib

open MeasureTheory

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ ν : Measure α)
    (κ η : ProbabilityTheory.Kernel α β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [ProbabilityTheory.IsMarkovKernel κ] [ProbabilityTheory.IsMarkovKernel η] :
    InformationTheory.klDiv (μ.compProd κ) (ν.compProd η) =
      InformationTheory.klDiv μ ν + InformationTheory.klDiv (μ.compProd κ) (μ.compProd η) :=
  InformationTheory.klDiv_compProd_eq_add μ ν κ η
