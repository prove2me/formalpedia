-- Prove2me | solution 1 for FamousTheorems.cartan_formula_nevanlinna_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:29:36.530733+00:00
-- url     : https://prove2.me/submissions/d0b80e77-8533-4586-8afa-de9c8f64755a

import Mathlib

theorem solution {f : ℂ → ℂ} {R : ℝ} (hf : Meromorphic f) (hR : R ≠ 0) :
    ValueDistribution.characteristic f ⊤ R =
      Real.circleAverage (fun a : ℂ => ValueDistribution.logCounting f (a : WithTop ℂ) R) 0 1 +
        Real.circleAverage (fun a : ℂ => Real.log ‖meromorphicTrailingCoeffAt (fun x => f x - a) 0‖) 0 1 :=
  ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage hf hR
