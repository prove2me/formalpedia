-- Prove2me | solution 1 for FBMSP.corollary2_superseded_copy
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:25:10.409206+00:00
-- url     : https://prove2.me/submissions/725ad24f-c81b-4090-9432-3c38476461f6

import Theorems.Thm_FBMSP_corollary2_moment_bound

import Definitions.Def_FBMSP_Model
open FBMSP
open MeasureTheory


theorem solution (ν η : Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η)
    (hV : NonnegativeValuations ν η)
    (hMoment : Integrable (fun x : ℝ => x ^ 2) ν)
    (σ : ℝ) (hσ : 0 ≤ σ) (hVar : predictionVariance ν = σ ^ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    segmentationLoss ν η k ≤
      2 * Real.sqrt (2 * σ * (predictionMean ν + σ) / (k : ℝ)) :=
  FBMSP.corollary2_moment_bound ν η hν hη hV hMoment σ hσ hVar k hk