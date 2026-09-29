-- Prove2me | solution 1 for FamousTheorems.gelfand_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:21:05.271448+00:00
-- url     : https://prove2.me/submissions/2f42dc02-d419-4aff-947d-cbb52fcd8100

import Mathlib

theorem solution {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ)))) Filter.atTop
      (nhds (spectralRadius ℂ a)) :=
  spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
