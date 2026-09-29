-- Prove2me | solution 1 for FamousTheorems.euler_mascheroni_constant_exists
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:37:23.508198+00:00
-- url     : https://prove2.me/submissions/10d8c0d3-ab19-4ded-a9b9-424e00a72e73

import Mathlib

theorem solution : ∃ γ : ℝ, Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) Filter.atTop (nhds γ) :=
  ⟨_, Real.tendsto_harmonic_sub_log⟩
