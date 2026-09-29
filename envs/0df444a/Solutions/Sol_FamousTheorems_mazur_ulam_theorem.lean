-- Prove2me | solution 1 for FamousTheorems.mazur_ulam_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:50:33.701656+00:00
-- url     : https://prove2.me/submissions/9acf3bcb-db77-49f0-880c-62b6d0fd1c81

import Mathlib

theorem solution {E PE F PF : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace PE] [NormedAddTorsor E PE]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace PF] [NormedAddTorsor F PF] (f : PE ≃ᵢ PF) :
    ∃ g : PE ≃ᵃⁱ[ℝ] PF, ⇑g = ⇑f :=
  ⟨f.toRealAffineIsometryEquiv, f.coeFn_toRealAffineIsometryEquiv⟩
